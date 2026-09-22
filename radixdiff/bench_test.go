// Copyright (c) 2026 Ville Vesilehto
// SPDX-License-Identifier: MPL-2.0

package radixdiff

// The benchmarks behind docs/benchmarks.md: go-juuri against both releases of
// hashicorp/go-immutable-radix on the operations a go-memdb-style database
// makes of its tree, in one process, over the same keys.
//
// Every side stores the same pointer value (nothing is boxed), looks keys up
// through copies that share no memory with the stored keys (go-immutable-radix
// keeps the caller's key slices alive inside the tree), visits them in a fixed
// random order (looking keys up in insertion order walks the allocator's
// layout, not the tree), and does its writes untracked, which is both
// libraries' default. Run with GOGC=400: at the default a one-second window
// allocates a large share of the collector's headroom, and whether a cycle
// starts inside it is decided by the pacer's phase rather than by the code.

import (
	"bytes"
	"encoding/binary"
	"fmt"
	"math/rand/v2"
	"runtime"
	"testing"
	"time"

	iradix "github.com/hashicorp/go-immutable-radix"
	iradix2 "github.com/hashicorp/go-immutable-radix/v2"

	"github.com/thevilledev/go-juuri"
)

const benchKeys = 100_000

type row struct{ id uint64 }

var (
	sinkRow  *row
	sinkAny  any
	sinkN    int
	sinkSum  uint64
	sinkTree juuri.Tree
	sinkV1   *iradix.Tree
	sinkV2   *iradix2.Tree[*row]
)

// keys returns n distinct random UUID strings (36 bytes, fan-out 16) and
// extra keys of the same shape that are guaranteed absent, each its own
// allocation. Deterministic: the same keys on every run and machine.
func keys(n, extra int) (stored, absent [][]byte) {
	r := rand.New(rand.NewPCG(20260922, 1))
	seen := make(map[string]struct{}, n+extra)
	var all [][]byte
	for len(all) < n+extra {
		var u [16]byte
		binary.LittleEndian.PutUint64(u[0:8], r.Uint64())
		binary.LittleEndian.PutUint64(u[8:16], r.Uint64())
		k := []byte(fmt.Sprintf("%08x-%04x-%04x-%04x-%012x", u[0:4], u[4:6], u[6:8], u[8:10], u[10:16]))
		if _, dup := seen[string(k)]; dup {
			continue
		}
		seen[string(k)] = struct{}{}
		all = append(all, k)
	}
	return all[:n:n], all[n:]
}

// probes returns fresh copies of ks in a fixed random order.
func probes(ks [][]byte, seed uint64) [][]byte {
	r := rand.New(rand.NewPCG(seed, 2))
	out := make([][]byte, len(ks))
	for i, p := range r.Perm(len(ks)) {
		out[i] = bytes.Clone(ks[p])
	}
	return out
}

type fixture struct {
	stored, absent [][]byte
	rows           []row
	juuri          juuri.Tree
	v1             *iradix.Tree
	v2             *iradix2.Tree[*row]
}

var fix *fixture

func setup(b *testing.B) *fixture {
	b.Helper()
	if fix != nil {
		return fix
	}
	f := &fixture{}
	f.stored, f.absent = keys(benchKeys, 1024)
	f.rows = make([]row, len(f.stored)+len(f.absent))
	for i := range f.rows {
		f.rows[i].id = uint64(i)
	}
	tj := juuri.New().Txn(nil)
	t1 := iradix.New().Txn()
	t2 := iradix2.New[*row]().Txn()
	for i, k := range f.stored {
		tj.Insert(k, &f.rows[i])
		t1.Insert(k, &f.rows[i])
		t2.Insert(k, &f.rows[i])
	}
	f.juuri, f.v1, f.v2 = tj.Commit(), t1.Commit(), t2.Commit()
	fix = f
	return f
}

// measure opens a timed section from a collected heap, so that every sample
// sees the same collector state whichever side it measures.
func measure(b *testing.B) {
	b.Helper()
	runtime.GC()
	b.ReportAllocs()
}

func BenchmarkGet(b *testing.B) {
	f := setup(b)
	ps := probes(f.stored, 1)
	b.Run("impl=juuri", func(b *testing.B) {
		t, j, hits := f.juuri, 0, 0
		measure(b)
		for b.Loop() {
			v, ok := t.Get(ps[j])
			j++
			if j == len(ps) {
				j = 0
			}
			if ok {
				hits++
			}
			sinkAny = v
		}
		if hits != b.N {
			b.Fatal("miss")
		}
	})
	b.Run("impl=iradix-v1", func(b *testing.B) {
		t, j, hits := f.v1, 0, 0
		measure(b)
		for b.Loop() {
			v, ok := t.Get(ps[j])
			j++
			if j == len(ps) {
				j = 0
			}
			if ok {
				hits++
			}
			sinkAny = v
		}
		if hits != b.N {
			b.Fatal("miss")
		}
	})
	b.Run("impl=iradix-v2", func(b *testing.B) {
		t, j, hits := f.v2, 0, 0
		measure(b)
		for b.Loop() {
			v, ok := t.Get(ps[j])
			j++
			if j == len(ps) {
				j = 0
			}
			if ok {
				hits++
			}
			sinkRow = v
		}
		if hits != b.N {
			b.Fatal("miss")
		}
	})
}

// BenchmarkLongestPrefix probes with stored keys extended by a suffix, so that
// the answer is the stored key itself, at the bottom of the tree.
func BenchmarkLongestPrefix(b *testing.B) {
	f := setup(b)
	ps := probes(f.stored, 3)
	for i := range ps {
		ps[i] = append(ps[i], "/x"...)
	}
	b.Run("impl=juuri", func(b *testing.B) {
		t, j, hits := f.juuri, 0, 0
		measure(b)
		for b.Loop() {
			v, ok := t.LongestPrefix(ps[j])
			j++
			if j == len(ps) {
				j = 0
			}
			if ok {
				hits++
			}
			sinkAny = v
		}
		if hits != b.N {
			b.Fatal("miss")
		}
	})
	b.Run("impl=iradix-v1", func(b *testing.B) {
		root, j, hits := f.v1.Root(), 0, 0
		measure(b)
		for b.Loop() {
			_, v, ok := root.LongestPrefix(ps[j])
			j++
			if j == len(ps) {
				j = 0
			}
			if ok {
				hits++
			}
			sinkAny = v
		}
		if hits != b.N {
			b.Fatal("miss")
		}
	})
	b.Run("impl=iradix-v2", func(b *testing.B) {
		root, j, hits := f.v2.Root(), 0, 0
		measure(b)
		for b.Loop() {
			_, v, ok := root.LongestPrefix(ps[j])
			j++
			if j == len(ps) {
				j = 0
			}
			if ok {
				hits++
			}
			sinkRow = v
		}
		if hits != b.N {
			b.Fatal("miss")
		}
	})
}

// BenchmarkInsertDelete is what a persistent tree charges for a write: an
// absent key inserted and committed, then deleted and committed, each commit
// copying the path from the root. The tree ends every iteration as it began.
func BenchmarkInsertDelete(b *testing.B) {
	f := setup(b)
	b.Run("impl=juuri", func(b *testing.B) {
		t, j := f.juuri, 0
		measure(b)
		for b.Loop() {
			txn := t.Txn(nil)
			txn.Insert(f.absent[j], &f.rows[benchKeys+j])
			t = txn.Commit()
			txn = t.Txn(nil)
			txn.Delete(f.absent[j])
			t = txn.Commit()
			j++
			if j == len(f.absent) {
				j = 0
			}
		}
		sinkTree = t
	})
	b.Run("impl=iradix-v1", func(b *testing.B) {
		t, j := f.v1, 0
		measure(b)
		for b.Loop() {
			t, _, _ = t.Insert(f.absent[j], &f.rows[benchKeys+j])
			t, _, _ = t.Delete(f.absent[j])
			j++
			if j == len(f.absent) {
				j = 0
			}
		}
		sinkV1 = t
	})
	b.Run("impl=iradix-v2", func(b *testing.B) {
		t, j := f.v2, 0
		measure(b)
		for b.Loop() {
			t, _, _ = t.Insert(f.absent[j], &f.rows[benchKeys+j])
			t, _, _ = t.Delete(f.absent[j])
			j++
			if j == len(f.absent) {
				j = 0
			}
		}
		sinkV2 = t
	})
}

// BenchmarkIterate visits every value in key order and adds up the ids, so
// the value is loaded, not just counted.
func BenchmarkIterate(b *testing.B) {
	f := setup(b)
	var want uint64
	for i := range f.stored {
		want += uint64(i)
	}
	b.Run("impl=juuri", func(b *testing.B) {
		t := f.juuri
		measure(b)
		for b.Loop() {
			var it juuri.Iterator
			it.SeekPrefixWatch(t, nil)
			n, sum := 0, uint64(0)
			for v, ok := it.Next(); ok; v, ok = it.Next() {
				sum += v.(*row).id
				n++
			}
			sinkN, sinkSum = n, sum
		}
		if sinkN != benchKeys || sinkSum != want {
			b.Fatal("iteration")
		}
	})
	b.Run("impl=iradix-v1", func(b *testing.B) {
		t := f.v1
		measure(b)
		for b.Loop() {
			it := t.Root().Iterator()
			n, sum := 0, uint64(0)
			for _, v, ok := it.Next(); ok; _, v, ok = it.Next() {
				sum += v.(*row).id
				n++
			}
			sinkN, sinkSum = n, sum
		}
		if sinkN != benchKeys || sinkSum != want {
			b.Fatal("iteration")
		}
	})
	b.Run("impl=iradix-v2", func(b *testing.B) {
		t := f.v2
		measure(b)
		for b.Loop() {
			it := t.Root().Iterator()
			n, sum := 0, uint64(0)
			for _, v, ok := it.Next(); ok; _, v, ok = it.Next() {
				sum += v.id
				n++
			}
			sinkN, sinkSum = n, sum
		}
		if sinkN != benchKeys || sinkSum != want {
			b.Fatal("iteration")
		}
	})
}

// BenchmarkWatch is the reactive round trip watches exist for: look a key up
// with its watch channel, commit a tracked update of that key, see the
// channel fire. Every iteration watches a key nobody has watched before. The
// history stays linear across passes -- each pass continues from the tree
// the previous one left -- because go-immutable-radix closes the channel of
// every node it replaces, and two tracked commits on one snapshot close the
// shared ones twice.
func BenchmarkWatch(b *testing.B) {
	f := setup(b)
	order := probes(f.stored, 4)
	b.Run("impl=juuri", func(b *testing.B) {
		var nf juuri.Notifier
		t, j, fired := f.juuri, 0, 0
		measure(b)
		for b.Loop() {
			w, _, _ := t.GetWatch(order[j])
			ch := w.Chan()
			txn := t.Txn(&nf)
			txn.Insert(order[j], &f.rows[0])
			t = txn.Commit()
			nf.Notify()
			select {
			case <-ch:
				fired++
			default:
			}
			j++
			if j == len(order) {
				j = 0
			}
		}
		sinkTree, f.juuri = t, t
		if fired != b.N {
			b.Fatal("a watch did not fire")
		}
	})
	b.Run("impl=iradix-v1", func(b *testing.B) {
		t, j, fired := f.v1, 0, 0
		measure(b)
		for b.Loop() {
			ch, _, _ := t.Root().GetWatch(order[j])
			txn := t.Txn()
			txn.TrackMutate(true)
			txn.Insert(order[j], &f.rows[0])
			t = txn.Commit()
			select {
			case <-ch:
				fired++
			default:
			}
			j++
			if j == len(order) {
				j = 0
			}
		}
		sinkV1, f.v1 = t, t
		if fired != b.N {
			b.Fatal("a watch did not fire")
		}
	})
	b.Run("impl=iradix-v2", func(b *testing.B) {
		t, j, fired := f.v2, 0, 0
		measure(b)
		for b.Loop() {
			ch, _, _ := t.Root().GetWatch(order[j])
			txn := t.Txn()
			txn.TrackMutate(true)
			txn.Insert(order[j], &f.rows[0])
			t = txn.Commit()
			select {
			case <-ch:
				fired++
			default:
			}
			j++
			if j == len(order) {
				j = 0
			}
		}
		sinkV2, f.v2 = t, t
		if fired != b.N {
			b.Fatal("a watch did not fire")
		}
	})
}

// BenchmarkMemory reports what a loaded tree costs the heap and the collector:
// bytes and objects per key, and one full collection with that tree, and
// nothing else of note, live -- the trees of the other benchmarks are dropped
// first, and each side's tree before the next side builds its own. The keys
// are made inside the measured window and then forgotten, so a library that
// keeps the caller's key slices alive pays for them, as its users do. The
// timed loop only makes this a benchmark.
func BenchmarkMemory(b *testing.B) {
	fix = nil
	sinkTree, sinkV1, sinkV2 = juuri.Tree{}, nil, nil
	stored, _ := keys(benchKeys, 0)
	rows := make([]row, len(stored))
	for i := range rows {
		rows[i].id = uint64(i)
	}
	report := func(b *testing.B, before, after *runtime.MemStats, gc time.Duration) {
		b.Helper()
		b.ReportMetric(float64(int64(after.HeapAlloc)-int64(before.HeapAlloc))/benchKeys, "heapB/key")
		b.ReportMetric(float64(int64(after.HeapObjects)-int64(before.HeapObjects))/benchKeys, "heapobjs/key")
		b.ReportMetric(float64(gc.Microseconds())/1000, "gc-ms")
	}
	fresh := func() [][]byte {
		out := make([][]byte, len(stored))
		for i, k := range stored {
			out[i] = bytes.Clone(k)
		}
		return out
	}
	b.Run("impl=juuri", func(b *testing.B) {
		runtime.GC()
		var before, after runtime.MemStats
		runtime.ReadMemStats(&before)
		ks := fresh()
		txn := juuri.New().Txn(nil)
		for i, k := range ks {
			txn.Insert(k, &rows[i])
		}
		t := txn.Commit()
		ks = nil //nolint:ineffassign,wastedassign // drop the keys before the tree's heap is measured
		runtime.GC()
		runtime.ReadMemStats(&after)
		start := time.Now()
		runtime.GC()
		gc := time.Since(start)
		for b.Loop() {
			sinkTree = t
		}
		sinkTree = juuri.Tree{}
		report(b, &before, &after, gc)
	})
	b.Run("impl=iradix-v1", func(b *testing.B) {
		runtime.GC()
		var before, after runtime.MemStats
		runtime.ReadMemStats(&before)
		ks := fresh()
		txn := iradix.New().Txn()
		for i, k := range ks {
			txn.Insert(k, &rows[i])
		}
		t := txn.Commit()
		ks = nil //nolint:ineffassign,wastedassign // drop the keys before the tree's heap is measured
		runtime.GC()
		runtime.ReadMemStats(&after)
		start := time.Now()
		runtime.GC()
		gc := time.Since(start)
		for b.Loop() {
			sinkV1 = t
		}
		sinkV1 = nil
		report(b, &before, &after, gc)
	})
	b.Run("impl=iradix-v2", func(b *testing.B) {
		runtime.GC()
		var before, after runtime.MemStats
		runtime.ReadMemStats(&before)
		ks := fresh()
		txn := iradix2.New[*row]().Txn()
		for i, k := range ks {
			txn.Insert(k, &rows[i])
		}
		t := txn.Commit()
		ks = nil //nolint:ineffassign,wastedassign // drop the keys before the tree's heap is measured
		runtime.GC()
		runtime.ReadMemStats(&after)
		start := time.Now()
		runtime.GC()
		gc := time.Since(start)
		for b.Loop() {
			sinkV2 = t
		}
		sinkV2 = nil
		report(b, &before, &after, gc)
	})
	runtime.KeepAlive(stored) // live at both readings
	runtime.KeepAlive(rows)
}
