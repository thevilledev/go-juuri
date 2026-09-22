// Copyright (c) 2026 Ville Vesilehto
// SPDX-License-Identifier: MPL-2.0

package juuri_test

import (
	"testing"

	"github.com/thevilledev/go-juuri"
)

// The tree itself is tested in internal/radix. What can still go wrong here is
// the wiring: a method of this package forwarding to the wrong one, dropping a
// result, or losing the watch handle on the way out. Every exported method is
// called once, and each is checked for something only it can produce.

func keys(t *testing.T, tr juuri.Tree, prefix string) []any {
	t.Helper()
	var it juuri.Iterator
	it.SeekPrefixWatch(tr, []byte(prefix))
	var out []any
	for v, ok := it.Next(); ok; v, ok = it.Next() {
		out = append(out, v)
	}
	return out
}

func TestAPI(t *testing.T) {
	var nf juuri.Notifier
	tr := juuri.New()

	var zero juuri.Txn
	if zero.Started() {
		t.Fatal("the zero Txn reports as started")
	}
	txn := tr.Txn(&nf)
	if !txn.Started() {
		t.Fatal("Tree.Txn returned an unstarted Txn")
	}
	for _, k := range []string{"a", "ab", "abc", "b"} {
		if old, existed := txn.Insert([]byte(k), k); existed {
			t.Fatalf("Insert(%q) reported a previous value %v", k, old)
		}
	}
	txn.Freeze()
	if n := txn.Tree().Len(); n != 4 {
		t.Fatalf("Txn.Tree().Len() = %d, want 4", n)
	}
	tr = txn.Commit()

	if v, ok := tr.Get([]byte("ab")); !ok || v != "ab" {
		t.Fatalf(`Get("ab") = %v,%v`, v, ok)
	}
	if v, ok := tr.LongestPrefix([]byte("abcd")); !ok || v != "abc" {
		t.Fatalf(`LongestPrefix("abcd") = %v,%v`, v, ok)
	}
	if _, v, ok := tr.FirstPrefix([]byte("a")); !ok || v != "a" {
		t.Fatalf(`FirstPrefix("a") = %v,%v`, v, ok)
	}
	if _, v, ok := tr.LastPrefix([]byte("a")); !ok || v != "abc" {
		t.Fatalf(`LastPrefix("a") = %v,%v`, v, ok)
	}
	if got := keys(t, tr, "a"); len(got) != 3 || got[0] != "a" || got[2] != "abc" {
		t.Fatalf("forward iteration over %q: %v", "a", got)
	}

	var rit juuri.ReverseIterator
	rit.SeekPrefixWatch(tr, []byte("a"))
	if v, ok := rit.Previous(); !ok || v != "abc" {
		t.Fatalf("ReverseIterator.Previous() = %v,%v", v, ok)
	}
	rit.SeekReverseLowerBound(tr, []byte("aa"))
	if v, ok := rit.Previous(); !ok || v != "a" {
		t.Fatalf(`SeekReverseLowerBound("aa") = %v,%v`, v, ok)
	}

	var it juuri.Iterator
	it.SeekLowerBound(tr, []byte("ab"))
	if v, ok := it.Next(); !ok || v != "ab" {
		t.Fatalf(`SeekLowerBound("ab") = %v,%v`, v, ok)
	}

	// The zero Watch blocks forever; a real one fires when its key changes.
	var unset juuri.Watch
	if unset.Chan() != nil {
		t.Fatal("the zero Watch has a channel")
	}
	w, _, ok := tr.GetWatch([]byte("ab"))
	if !ok {
		t.Fatal(`GetWatch("ab") missed`)
	}
	changed := w.Chan()

	txn = tr.Txn(&nf)
	if old, existed := txn.Delete([]byte("ab")); !existed || old != "ab" {
		t.Fatalf(`Delete("ab") = %v,%v`, old, existed)
	}
	if !txn.DeletePrefix([]byte("b")) {
		t.Fatal(`DeletePrefix("b") found nothing`)
	}
	tr = txn.Commit()
	nf.Notify()

	select {
	case <-changed:
	default:
		t.Fatal("the watch on a deleted key did not fire")
	}
	if n := tr.Len(); n != 2 {
		t.Fatalf("Len() = %d, want 2", n)
	}

	// An aborted transaction notifies nobody: the tree it was started from
	// is simply not published.
	w, _, _ = tr.GetWatch([]byte("a"))
	changed = w.Chan()
	txn = tr.Txn(&nf)
	txn.Insert([]byte("a"), "other")
	nf.Reset()
	select {
	case <-changed:
		t.Fatal("Notifier.Reset() notified watchers")
	default:
	}
}
