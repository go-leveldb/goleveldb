// Copyright (c) 2012, Suryandaru Triandana <syndtr@gmail.com>
// All rights reserved.
//
// Use of this source code is governed by a BSD-style license that can be
// found in the LICENSE file.

package leveldb

import (
	"bytes"
	"fmt"
	"sort"
	"sync"

	"github.com/go-leveldb/goleveldb/leveldb/cache"
	"github.com/go-leveldb/goleveldb/leveldb/errors"
	"github.com/go-leveldb/goleveldb/leveldb/iterator"
	"github.com/go-leveldb/goleveldb/leveldb/memdb"
	"github.com/go-leveldb/goleveldb/leveldb/opt"
	"github.com/go-leveldb/goleveldb/leveldb/table"
	"github.com/go-leveldb/goleveldb/leveldb/util"
)

const (
	undefinedCompaction = iota
	level0Compaction
	nonLevel0Compaction
	seekCompaction
)

func (s *session) pickMemdbLevel(umin, umax []byte, maxLevel int) int {
	v := s.version()
	defer v.release()
	return v.pickMemdbLevel(umin, umax, maxLevel)
}

func (s *session) flushMemdb(rec *sessionRecord, mdb *memdb.DB, maxLevel int) (int, error) {
	// Create sorted table.
	iter := mdb.NewIterator(nil)
	defer iter.Release()
	t, n, err := s.tops.createFrom(iter)
	if err != nil {
		return 0, err
	}

	// Pick level other than zero can cause compaction issue with large
	// bulk insert and delete on strictly incrementing key-space. The
	// problem is that the small deletion markers trapped at lower level,
	// while key/value entries keep growing at higher level. Since the
	// key-space is strictly incrementing it will not overlaps with
	// higher level, thus maximum possible level is always picked, while
	// overlapping deletion marker pushed into lower level.
	// See: https://github.com/go-leveldb/goleveldb/issues/127.
	flushLevel := s.pickMemdbLevel(t.imin.ukey(), t.imax.ukey(), maxLevel)
	rec.addTableFile(flushLevel, t)

	s.logf("memdb@flush created L%d@%d N·%d S·%s %q:%q", flushLevel, t.fd.Num, n, shortenb(int(t.size)), t.imin, t.imax)
	return flushLevel, nil
}

// pickFirst picks the seed file for compaction if there is no ongoing compaction
// in this level. The pick algorithm is very simple: select the first file with the
// max key greater than compPtr as the seed file. If the compPtr is nil, than pick
// the first one.
func (s *session) pickFirst(level int, v *version, ctx *compactionContext) *compaction {
	var (
		cptr   = s.getCompPtr(level)
		tables = v.levels[level]
	)
	typ := level0Compaction
	if level != 0 {
		typ = nonLevel0Compaction
	}
	// If it's level0 compaction(file overlapped) or the cptr is nil,
	// iterate from the beginning.
	if level == 0 || cptr == nil {
		for _, t := range tables {
			c := newCompaction(s, v, level, tFiles{t}, typ, ctx)
			if c != nil {
				return c
			}
		}
		return nil
	}
	// Binary search the proper start position
	start := sort.Search(len(tables), func(i int) bool {
		return s.icmp.Compare(tables[i].imax, cptr) > 0
	})
	for i := start; i < len(tables); i++ {
		c := newCompaction(s, v, level, tFiles{tables[i]}, typ, ctx)
		if c != nil {
			return c
		}
	}
	for i := 0; i < start; i++ {
		c := newCompaction(s, v, level, tFiles{tables[i]}, typ, ctx)
		if c != nil {
			return c
		}
	}
	return nil
}

// pickMore picks the seed file for compaction if there are ongoing compactions
// in this level.
func (s *session) pickMore(level int, v *version, ctx *compactionContext) *compaction {
	var (
		reverse      bool
		start, limit internalKey
	)
	typ := level0Compaction
	if level != 0 {
		typ = nonLevel0Compaction
	}
	cs := ctx.get(level)
	if len(cs) == 0 {
		return nil // Should never happen
	}

	limit = cs[len(cs)-1].imax
	start = cs[0].imax
	if s.icmp.Compare(start, limit) > 0 {
		reverse = true
		start, limit = limit, start
	}

	tables := v.levels[level]
	if !reverse {
		p := sort.Search(len(tables), func(i int) bool {
			return s.icmp.Compare(tables[i].imax, limit) > 0
		})
		for i := p; i < len(tables); i++ {
			c := newCompaction(s, v, level, tFiles{tables[i]}, typ, ctx)
			if c != nil {
				return c
			}
		}
		for _, t := range tables {
			if s.icmp.Compare(t.imax, start) >= 0 {
				break
			}
			c := newCompaction(s, v, level, tFiles{t}, typ, ctx)
			if c != nil {
				return c
			}
		}
		return nil
	} else {
		p := sort.Search(len(tables), func(i int) bool {
			return s.icmp.Compare(tables[i].imax, start) > 0
		})
		for i := p; i < len(tables); i++ {
			if s.icmp.Compare(tables[i].imax, limit) >= 0 {
				break
			}
			c := newCompaction(s, v, level, tFiles{tables[i]}, typ, ctx)
			if c != nil {
				return c
			}
		}
		return nil
	}
}

func (s *session) pickCompactionByLevel(level int, ctx *compactionContext) (comp *compaction) {
	v := s.version()
	defer func() {
		if comp == nil {
			v.release()
		}
	}()
	if len(ctx.get(level)) == 0 {
		return s.pickFirst(level, v, ctx)
	}
	return s.pickMore(level, v, ctx)
}

func (s *session) pickCompactionByTable(level int, table *tFile, ctx *compactionContext) (comp *compaction) {
	v := s.version()
	defer func() {
		if comp == nil {
			v.release()
		}
	}()
	return newCompaction(s, v, level, []*tFile{table}, seekCompaction, ctx)
}

func (s *session) getFirstRange(v *version, ctx *compactionContext, sourceLevel int, umin, umax []byte, typ int, limit int64) (comp *compaction) {
	t0 := v.levels[sourceLevel].getOverlaps(nil, s.icmp, umin, umax, sourceLevel == 0)
	if len(t0) == 0 {
		return nil
	}
	// Avoid compacting too much in one shot in case the range is large.
	// But we cannot do this for level-0 since level-0 files can overlap
	// and we must not pick one file and drop another older file if the
	// two files overlap.
	if sourceLevel != 0 {
		total := int64(0)
		for i, t := range t0 {
			total += t.size
			if total >= limit {
				s.logf("table@compaction limiting F·%d -> F·%d", len(t0), i+1)
				t0 = t0[:i+1]
				break
			}
		}
	}
	return newCompaction(s, v, sourceLevel, t0, typ, ctx)
}

func (s *session) getMoreRange(v *version, ctx *compactionContext, sourceLevel int, umin, umax []byte, typ int, sourceLimit int64) (comp *compaction) {
	// Determine the search space for next potential range compaction
	cs := ctx.get(sourceLevel)
	if len(cs) == 0 {
		return nil // Should never happen
	}
	limit := cs[len(cs)-1].imax
	start := cs[0].imax

	var reverse bool
	if s.icmp.Compare(start, limit) > 0 {
		reverse = true
		start, limit = limit, start
	}

	t0 := v.levels[sourceLevel].getOverlaps(nil, s.icmp, umin, umax, sourceLevel == 0)
	if len(t0) == 0 {
		return nil
	}

	if !reverse {
		p := sort.Search(len(t0), func(i int) bool {
			return s.icmp.Compare(t0[i].imax, limit) > 0
		})
		for i := p; i < len(t0); i++ {
			c := newCompaction(s, v, sourceLevel, tFiles{t0[i]}, typ, ctx)
			if c != nil {
				return c
			}
		}
		for _, t := range t0 {
			if s.icmp.Compare(t.imax, start) >= 0 {
				break
			}
			c := newCompaction(s, v, sourceLevel, tFiles{t}, typ, ctx)
			if c != nil {
				return c
			}
		}
		return nil
	} else {
		p := sort.Search(len(t0), func(i int) bool {
			return s.icmp.Compare(t0[i].imax, start) > 0
		})
		for i := p; i < len(t0); i++ {
			if s.icmp.Compare(t0[i].imax, limit) >= 0 {
				break
			}
			c := newCompaction(s, v, sourceLevel, tFiles{t0[i]}, typ, ctx)
			if c != nil {
				return c
			}
		}
		return nil
	}
}

// Create compaction from given level and range; need external synchronization.
func (s *session) getCompactionRange(ctx *compactionContext, sourceLevel int, umin, umax []byte) (comp *compaction) {
	v := s.version()
	defer func() {
		if comp == nil {
			v.release()
		}
	}()
	if sourceLevel >= len(v.levels) {
		return nil
	}
	typ := level0Compaction
	if sourceLevel != 0 {
		typ = nonLevel0Compaction
	}
	limit := int64(v.s.o.GetCompactionSourceLimit(sourceLevel))
	if ctx.count() == 0 {
		return s.getFirstRange(v, ctx, sourceLevel, umin, umax, typ, limit)
	}
	if sourceLevel == 0 {
		return nil
	}
	return s.getMoreRange(v, ctx, sourceLevel, umin, umax, typ, limit)
}

func newCompaction(s *session, v *version, sourceLevel int, t0 tFiles, typ int, ctx *compactionContext) *compaction {
	c := &compaction{
		s:             s,
		v:             v,
		typ:           typ,
		sourceLevel:   sourceLevel,
		levels:        [2]tFiles{t0, nil},
		maxGPOverlaps: int64(s.o.GetCompactionGPOverlaps(sourceLevel)),
	}
	if !c.expand(ctx) {
		return nil
	}
	return c
}

type compactionDynamicContext struct {
	gpi               int
	seenKey           bool
	gpOverlappedBytes int64
	tPtrs             []int

	snapGPI               int
	snapSeenKey           bool
	snapGPOverlappedBytes int64
	snapTPtrs             []int
}

func newDynamicContext(levels []tFiles) *compactionDynamicContext {
	return &compactionDynamicContext{
		tPtrs:     make([]int, len(levels)),
		snapTPtrs: make([]int, len(levels)),
	}
}

func (ctx *compactionDynamicContext) save() {
	ctx.snapGPI = ctx.gpi
	ctx.snapSeenKey = ctx.seenKey
	ctx.snapGPOverlappedBytes = ctx.gpOverlappedBytes
	ctx.snapTPtrs = append(ctx.snapTPtrs[:0], ctx.tPtrs...)
}

func (ctx *compactionDynamicContext) restore() {
	ctx.gpi = ctx.snapGPI
	ctx.seenKey = ctx.snapSeenKey
	ctx.gpOverlappedBytes = ctx.snapGPOverlappedBytes
	ctx.tPtrs = append(ctx.tPtrs[:0], ctx.snapTPtrs...)
}

// baseLevelForKey reports whether the given user-key is already in the
// bottom-most level. Also this function will update the internal state
// for speeding up the overall performance.
// The assumption is held here the given user-keys are monotonic increasing.
func (ctx *compactionDynamicContext) baseLevelForKey(sourceLevel int, levels []tFiles, icmp *iComparer, ukey []byte) bool {
	for level := sourceLevel + 2; level < len(levels); level++ {
		tables := levels[level]
		for ctx.tPtrs[level] < len(tables) {
			t := tables[ctx.tPtrs[level]]
			if icmp.uCompare(ukey, t.imax.ukey()) <= 0 {
				// We've advanced far enough.
				if icmp.uCompare(ukey, t.imin.ukey()) >= 0 {
					// Key falls in this file's range, so definitely not base level.
					return false
				}
				break
			}
			ctx.tPtrs[level]++
		}
	}
	return true
}

// shouldStopBefore reports whether the overlap between the current table
// with the parent level is large enough. If so the table rotation is expected.
// Also this function will update the internal state for speeding up the
// overal performance.
func (ctx *compactionDynamicContext) shouldStopBefore(gp tFiles, icmp *iComparer, maxGPOverlaps int64, ikey internalKey) bool {
	for ; ctx.gpi < len(gp); ctx.gpi++ {
		gp := gp[ctx.gpi]
		if icmp.Compare(ikey, gp.imax) <= 0 {
			break
		}
		if ctx.seenKey {
			ctx.gpOverlappedBytes += gp.size
		}
	}
	ctx.seenKey = true

	if ctx.gpOverlappedBytes > maxGPOverlaps {
		// Too much overlap for current output; start new output.
		ctx.gpOverlappedBytes = 0
		return true
	}
	return false
}

// compaction represent a compaction state. It's immutable(except
// the released field), so it's totally safe to share it with multiple
// sub-compaction threads.
type compaction struct {
	s             *session
	v             *version
	id            int64
	typ           int
	sourceLevel   int
	levels        [2]tFiles
	maxGPOverlaps int64
	gp            tFiles
	imin, imax    internalKey
	released      bool
	weight        int
}

func (c *compaction) release() {
	if !c.released {
		c.released = true
		c.v.release()
	}
}

// Expand compacted tables; need external synchronization.
func (c *compaction) expand(ctx *compactionContext) bool {
	limit := int64(c.s.o.GetCompactionExpandLimit(c.sourceLevel))
	vt0 := c.v.levels[c.sourceLevel]
	vt1 := tFiles{}
	if level := c.sourceLevel + 1; level < len(c.v.levels) {
		vt1 = c.v.levels[level]
	}

	t0, t1 := c.levels[0], c.levels[1]
	imin, imax := t0.getRange(c.s.icmp, c.sourceLevel == 0)

	// For non-zero levels, the ukey can't hop across tables at all.
	if c.sourceLevel == 0 {
		// We expand t0 here just incase ukey hop across tables.
		t0 = vt0.getOverlaps(t0, c.s.icmp, imin.ukey(), imax.ukey(), true)
		if len(t0) != len(c.levels[0]) {
			imin, imax = t0.getRange(c.s.icmp, true)
		}
	}
	if c.sourceLevel != 0 && ctx != nil {
		// Ensure the source level files are not the input of other compactions.
		if ctx.removing(c.sourceLevel).hasFiles(t0) {
			return false
		}
		if ctx.recreating(c.sourceLevel).hasFiles(t0) {
			return false
		}
	}
	t1 = vt1.getOverlaps(t1, c.s.icmp, imin.ukey(), imax.ukey(), false)

	// If the overlapped tables in level n+1 are not available, abort the expansion
	if ctx != nil {
		if ctx.recreating(c.sourceLevel + 1).hasFiles(t1) {
			return false
		}
		if ctx.removing(c.sourceLevel + 1).hasFiles(t1) {
			return false
		}
	}
	// Get entire range covered by compaction.
	amin, amax := append(t0, t1...).getRange(c.s.icmp, true)

	// See if we can grow the number of inputs in "sourceLevel" without
	// changing the number of "sourceLevel+1" files we pick up.
	if len(t1) > 0 {
		exp0 := vt0.getOverlaps(nil, c.s.icmp, amin.ukey(), amax.ukey(), c.sourceLevel == 0)
		if len(exp0) > len(t0) && t1.size()+exp0.size() < limit {
			var skip bool
			if ctx != nil {
				skip = ctx.removing(c.sourceLevel).hasFiles(exp0) || ctx.recreating(c.sourceLevel).hasFiles(exp0)
			}
			if !skip {
				xmin, xmax := exp0.getRange(c.s.icmp, c.sourceLevel == 0)
				exp1 := vt1.getOverlaps(nil, c.s.icmp, xmin.ukey(), xmax.ukey(), false)
				if len(exp1) == len(t1) {
					c.s.logf("table@compaction expanding L%d+L%d (F·%d S·%s)+(F·%d S·%s) -> (F·%d S·%s)+(F·%d S·%s)",
						c.sourceLevel, c.sourceLevel+1, len(t0), shortenb(int(t0.size())), len(t1), shortenb(int(t1.size())),
						len(exp0), shortenb(int(exp0.size())), len(exp1), shortenb(int(exp1.size())))
					imin, imax = xmin, xmax
					t0, t1 = exp0, exp1
					amin, amax = append(t0, t1...).getRange(c.s.icmp, c.sourceLevel == 0)
				}
			}
		}
	}

	// Compute the set of grandparent files that overlap this compaction
	// (parent == sourceLevel+1; grandparent == sourceLevel+2)
	//
	// Note the tables overlapped in the grandparent level may are removing.
	// We don't care about it seems the only downside is we split in tables
	// in the parent level but actually we don't need.
	if level := c.sourceLevel + 2; level < len(c.v.levels) {
		c.gp = c.v.levels[level].getOverlaps(c.gp, c.s.icmp, amin.ukey(), amax.ukey(), false)
	}

	c.levels[0], c.levels[1] = t0, t1
	c.imin, c.imax = imin, imax

	return true
}

// Check whether compaction is trivial.
func (c *compaction) trivial() bool {
	return len(c.levels[0]) == 1 && len(c.levels[1]) == 0 && c.gp.size() <= c.maxGPOverlaps
}

// getWeight returns the weight of compaction. It's used in the concurrent compaction limiter.
// The weight of non-level0 compaction is 1 by default seems they won't be divided into
// smaller sub-compaction. The weight of level0 compaction is determined by the compaction
// size.
func (c *compaction) getWeight(maxConcurrency int, minLevel0SubCompactionSize int64) int {
	if c.weight != 0 {
		return c.weight
	}
	if c.sourceLevel != 0 {
		c.weight = 1
	} else {
		// The level0 compaction weight doesn't have to be
		// very accurate, seems the concurrency may be changed
		// in the real run. But it's fine.
		c.weight = c.calculateConcurrency(maxConcurrency, minLevel0SubCompactionSize)
	}
	return c.weight
}

// calculateConcurrency calculates the suitable concurrency for level0 compaction.
// The concurrency is determined by the concurrency upper limit and the minimal
// sub-compaction size required.
// The result is not very accurate. It's just the approximate value based on the
// approximate table size(the actual key-value size is smaller).
func (c *compaction) calculateConcurrency(maxConcurrency int, minLevel0SubSize int64) int {
	var total int64
	for _, tables := range c.levels {
		for _, t := range tables {
			total += t.size
		}
	}
	if total <= minLevel0SubSize {
		return 1
	}
	groupSize := minLevel0SubSize
	if int64(maxConcurrency)*minLevel0SubSize < total {
		groupSize = (total-1)/int64(maxConcurrency) + 1
	}
	concurrency := (total-1)/groupSize + 1
	return int(concurrency)
}

// calculateRanges splits the entire key range into several small ones for
// concurrent compaction. Note this function is only meaningful for level0
// compaction.
//
// The function has two main goals:
// - Select a suitable concurrency for the compaction
// - Ensure the workload is distributed evenly in each sub compaction
func (c *compaction) calculateRanges(maxConcurrency int, minLevel0SubSize int64) (ranges []*util.Range, err error) {
	// Short circuit if it's non-level0 compaction
	if c.sourceLevel != 0 {
		return nil, nil
	}
	// Short circuit if the level1 is empty. It can happen
	// if leveldb tries to recover itself from losing manifest
	// or the first level0 compaction. todo should be fixed
	if len(c.levels[1]) == 0 {
		return nil, nil
	}
	// Short circuit if the compaction source size is too small
	concurrency := c.calculateConcurrency(maxConcurrency, minLevel0SubSize)
	if concurrency == 1 {
		return []*util.Range{{}}, nil
	}
	var (
		handlers = [2][]*cache.Handle{}
		offsets  = make([]int64, len(c.levels[0]))
		sizes    = make([]int64, len(c.levels[1]))
	)
	// Preopen all the source level files
	for level, tables := range c.levels {
		for _, table := range tables {
			ch, err := c.s.tops.open(table)
			if err != nil {
				return nil, err
			}
			handlers[level] = append(handlers[level], ch)
		}
	}
	// Release all opened files in the end of the function
	defer func() {
		for _, hs := range handlers {
			for _, h := range hs {
				h.Release()
			}
		}
	}()
	// Calculate the source size falls in the key range of each parent level file.
	// - if it's the first file in the parent level, the key range stops before the
	//   first entry in the next file(the first entry is excluded)
	// - if it's the last file in the parent level, the key range starts from the first
	//   entry in the last file (the first entry is included)
	// - otherwise
	// 	 - the start is the separator of the last entry in the last file and
	// 	   the first entry in the current file, start is included by default.
	//   - the limit is the separator of the last entry in the current file and
	//     the first entry in the next file, limit is excluded by default.
	for i := 0; i < len(c.levels[1]); i++ {
		var (
			wg     sync.WaitGroup
			isLast = i == len(c.levels[1])-1
			subs   = make([]int64, len(c.levels[0]))
			errs   = make([]error, len(c.levels[0]))
		)
		for child := 0; child < len(c.levels[0]); child++ {
			wg.Add(1)
			go func(index int) {
				defer wg.Done()
				if isLast {
					offset, err := handlers[0][index].Value().(*table.Reader).LastOffset()
					if err != nil {
						errs[index] = err
						return
					}
					subs[index] = offset - offsets[index]
					if subs[index] < 0 {
						panic(fmt.Sprintf("negative size %v", subs[index]))
					}
					offsets[index] = offset
				} else {
					limit := c.levels[1][i+1].imin
					offset, err := handlers[0][index].Value().(*table.Reader).OffsetOf(limit)
					if err != nil {
						errs[index] = err
						return
					}
					subs[index] = offset - offsets[index]
					if subs[index] < 0 {
						panic(fmt.Sprintf("negative size %v", subs[index]))
					}
					offsets[index] = offset
				}
			}(child)
		}
		wg.Wait()

		for child := 0; child < len(c.levels[0]); child++ {
			if errs[child] != nil {
				return nil, errs[child]
			}
			sizes[i] += subs[child]
		}
	}
	// Split the parent level files into several groups. The size splitting is
	// not accurate here, just for the rough partition.
	// The extreme imbalance can happen if there is a big key-space gap. Still
	// needs to figure a better way for partition.
	var (
		group     int64
		groupSize int64
		totalSize int64
		lastKey   []byte
	)
	for _, size := range sizes {
		totalSize += size
	}
	groupSize = (totalSize-1)/int64(concurrency) + 1

	for i, size := range sizes {
		if group+size <= groupSize {
			group += size
			continue
		}
		var divided int64
		for {
			key, err := handlers[1][i].Value().(*table.Reader).KeyInOffset(float64(groupSize-group+divided) / float64(size))
			if err != nil {
				return nil, err
			}
			if len(key) == 0 {
				return nil, errors.New("empty key")
			}
			if c.s.icmp.Compare(key, c.levels[1][i].imax) > 0 {
				panic(fmt.Sprintf("key %v max %v", []byte(key), []byte(c.levels[1][i].imax)))
			}
			if lastKey != nil && bytes.Equal(lastKey, key) {
				fmt.Printf("SAME KEY last %v current %v min %v max %v, size %v, fsize %v, divided %v, group %v, groupsize %v percent %f\n",
					lastKey, key, []byte(c.levels[1][i].imin), []byte(c.levels[1][i].imax), size, c.levels[1][i].size, divided, group, groupSize, float64(groupSize-group+divided)/float64(size))
				divided += groupSize - group
				group = 0
				if size-divided < groupSize {
					group = size - divided
					break
				}
				continue
			}

			r := &util.Range{}
			if lastKey != nil {
				r.Start = append([]byte{}, lastKey...)
			}
			r.Limit = append([]byte{}, key...)
			ranges = append(ranges, r)

			if lastKey != nil && c.s.icmp.Compare(lastKey, key) >= 0 {
				panic(fmt.Sprintf("i %d last %v key %v min %v max %v, size %v, fsize %v, divided %v, group %v, groupsize %v percent %f",
					i, lastKey, key, []byte(c.levels[1][i].imin), []byte(c.levels[1][i].imax), size, c.levels[1][i].size, divided, group, groupSize, float64(groupSize-group+divided)/float64(size)))
			}
			lastKey = r.Limit

			divided += groupSize - group
			group = 0
			if size-divided < groupSize {
				group = size - divided
				break
			}
		}
	}
	// If the last group is too small, merge it
	if group < groupSize/2 && len(ranges) > 0 {
		ranges[len(ranges)-1].Limit = nil
	} else {
		ranges = append(ranges, &util.Range{
			Start: lastKey,
			Limit: nil,
		})
	}
	return ranges, nil
}

// Creates an iterator.
func (c *compaction) newIterator(start, limit []byte) iterator.Iterator {
	// Creates iterator slice.
	icap := len(c.levels)
	if c.sourceLevel == 0 {
		// Special case for level-0.
		icap = len(c.levels[0]) + 1
	}
	its := make([]iterator.Iterator, 0, icap)

	// Options.

	// TODO the index block can't be shared by sub-compactors
	ro := &opt.ReadOptions{
		DontFillCache: true,
		Strict:        opt.StrictOverride,
	}
	strict := c.s.o.GetStrict(opt.StrictCompaction)
	if strict {
		ro.Strict |= opt.StrictReader
	}

	for i, tables := range c.levels {
		if len(tables) == 0 {
			continue
		}

		// Level-0 is not sorted and may overlaps each other.
		if c.sourceLevel+i == 0 {
			for _, t := range tables {
				its = append(its, c.s.tops.newIterator(t, &util.Range{
					Start: start,
					Limit: limit,
				}, ro))
			}
		} else {
			it := iterator.NewIndexedIterator(tables.newIndexIterator(c.s.tops, c.s.icmp, &util.Range{
				Start: start,
				Limit: limit,
			}, ro), strict)
			its = append(its, it)
		}
	}

	return iterator.NewMergedIterator(its, c.s.icmp, strict)
}
