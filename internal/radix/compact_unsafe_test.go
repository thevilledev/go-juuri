// Copyright (c) 2026 Ville Vesilehto
// SPDX-License-Identifier: MPL-2.0

//go:build !juuri_safe && !memdb_safe && !purego

package radix

import (
	"strings"
	"testing"
	"unsafe"
)

// TestCompactLeaves checks the storage class of childless nodes in the default
// build: segments up to segMax bytes live in the node's bitmap area (the node
// is a bare header, 96 bytes on 64-bit targets, and recognised as compact),
// longer ones trail the header, and everything a leaf goes through -- a split
// that trims its segment, a copy, a merge that lengthens it, an update --
// keeps it in the right class.
func TestCompactLeaves(t *testing.T) {
	header := uintptr(96)
	if unsafe.Sizeof(uintptr(0)) == 4 {
		header = 72 // two strings and three pointers shrink by four bytes each
	}
	if unsafe.Sizeof(node{}) != header || segMax != 34 {
		t.Fatalf("node is %d bytes with a %d-byte segment area", unsafe.Sizeof(node{}), segMax)
	}
	leafOf := func(tr Tree, key string) *node {
		n := tr.root
		search := []byte(key)
		for len(search) > 0 {
			idx, ok := n.rank(search[0])
			if !ok {
				t.Fatalf("%q: no child for %q", key, search)
			}
			n = n.kid(idx)
			if !n.hasPrefix(search) {
				t.Fatalf("%q: prefix %q does not match %q", key, n.prefix, search)
			}
			search = search[len(n.prefix):]
		}
		return n
	}
	for _, size := range []int{1, 2, 33, 34, 35, 48, 49, 64, 65, 200} {
		key := strings.Repeat("k", size)
		txn := New().Txn(nil)
		txn.Insert([]byte(key), size)
		tr := txn.Commit()
		n := leafOf(tr, key)
		if got, want := n.compact(), size <= 34; got != want {
			t.Fatalf("segment of %d bytes: compact = %v, want %v", size, got, want)
		}
		if n.compact() && n.kidCount()+n.kidCap() != 0 {
			t.Fatalf("segment of %d bytes: compact leaf reports children", size)
		}

		if size == 1 {
			continue // nothing to split
		}

		// Split: a second key diverges after the first byte, so the leaf
		// keeps size-1 bytes of segment and moves under a new branch node.
		txn = tr.Txn(nil)
		txn.Insert([]byte("k"+strings.Repeat("x", size)), -size)
		tr = txn.Commit()
		n = leafOf(tr, key)
		if n.prefix != key[1:] {
			t.Fatalf("after the split the leaf's segment is %q", n.prefix)
		}
		// The trim happens in place: a leaf stays in the class it was born in.
		if got, want := n.compact(), size <= 34; got != want {
			t.Fatalf("segment of %d bytes after the split: compact = %v, want %v", size-1, got, want)
		}
		if v, ok := tr.Get([]byte(key)); !ok || v != size {
			t.Fatalf("after the split Get(%q) = %v, %v", key, v, ok)
		}

		// Merge: deleting the other key absorbs the branch node's byte back.
		txn = tr.Txn(nil)
		txn.Delete([]byte("k" + strings.Repeat("x", size)))
		tr = txn.Commit()
		n = leafOf(tr, key)
		if n.prefix != key {
			t.Fatalf("after the merge the leaf's segment is %q", n.prefix)
		}
		if got, want := n.compact(), size <= 34; got != want {
			t.Fatalf("segment of %d bytes after the merge: compact = %v, want %v", size, got, want)
		}
		if tr.Len() != 1 {
			t.Fatalf("after the merge the tree holds %d keys", tr.Len())
		}
		checkShape(t, tr)
	}
}
