// Copyright (c) 2026 Ville Vesilehto
// SPDX-License-Identifier: MPL-2.0

//go:build !juuri_safe && !memdb_safe && !purego

package radix

import "unsafe"

// Childless nodes -- the great majority: one per stored key -- keep their path
// segment inside their own allocation. That saves an allocation per inserted
// key and, more importantly, a cache miss per lookup: the bytes that finish the
// key comparison sit right next to the node that was just fetched.
//
// A segment of up to segMax bytes goes where a node with children keeps its
// bitmap and child counters, making a compact leaf (node_unsafe.go): 96
// bytes, the size of a bare header, with the segment in the first cache line.
// Longer segments trail the header in a class of their own, and the longest
// are heap strings. The only unsafe operation is building a string over the
// node's own bytes. They are written once, before the string exists, and
// never again except by trimPrefix, which shortens the segment in place while
// the node is owned by one transaction and visible to nobody else; being an
// interior pointer into the node, the string keeps nothing alive but the node
// itself.
//
// The rule that keeps this from pinning dead nodes in memory: an inline segment
// is never shared with another node. Whoever copies a childless node, or takes
// a substring of its segment for a different node, copies the bytes (copyNode,
// the split in Insert, mergeChild).

type (
	leaf48 struct {
		node
		seg [48]byte
	}
	leaf64 struct {
		node
		seg [64]byte
	}
)

// newLeafNode returns a childless node with the path segment a+b.
func newLeafNode(a, b string) *node {
	n := len(a) + len(b)
	switch {
	case n == 0:
		return &node{}
	case n <= int(segMax):
		x := &node{}
		seg := x.segment()
		copy(seg[copy(seg, a):], b)
		x.prefix = unsafe.String(&seg[0], n)
		return x
	case n <= 48:
		x := &leaf48{}
		copy(x.seg[copy(x.seg[:], a):], b)
		x.prefix = unsafe.String(&x.seg[0], n)
		return &x.node
	case n <= 64:
		x := &leaf64{}
		copy(x.seg[copy(x.seg[:], a):], b)
		x.prefix = unsafe.String(&x.seg[0], n)
		return &x.node
	}
	// Too long to inline. The result must not alias a: the caller may have
	// passed a view of a scratch buffer (bytesToString), and a + "" would
	// hand that very string back without copying it.
	buf := make([]byte, 0, n)
	buf = append(append(buf, a...), b...)
	return &node{prefix: unsafe.String(unsafe.SliceData(buf), n)}
}

// trimPrefix drops the first k bytes of the segment of n, which must be owned
// by the caller and keep at least one byte. A compact leaf's segment is moved
// down within its area, so that the node stays recognisable as compact.
func (n *node) trimPrefix(k int) {
	if n.compact() {
		seg := n.segment()
		l := len(n.prefix) - k
		copy(seg, seg[k:k+l])
		n.prefix = unsafe.String(&seg[0], l)
		return
	}
	n.prefix = n.prefix[k:]
}

// bytesToString views b as a string for the duration of a call that copies it.
func bytesToString(b []byte) string {
	return unsafe.String(unsafe.SliceData(b), len(b))
}
