// Copyright (c) 2026 Ville Vesilehto
// SPDX-License-Identifier: MPL-2.0

//go:build !juuri_safe && !memdb_safe && !purego

package radix

import (
	"sync/atomic"
	"unsafe"

	"github.com/thevilledev/go-juuri/internal/watch"
)

// node is a radix tree node. Everything except the watch slot and the lazily
// created leaf is immutable once the node is visible to anyone but the
// transaction that owns it.
//
// A node is allocated together with room for its children (see newNode): the
// child array directly follows the header. This declaration has no slice for
// it -- the array's address is the node's plus a constant, its length is a
// 16-bit field -- which makes the header 16 bytes smaller than the pure-safe
// build's (node_safe.go) and, more importantly, lets everything a lookup or an
// iteration step reads fit the header's first cache line: the path segment,
// the label bitmap that locates the next child, and the value.
//
// The 34 bytes after the value are a union. In a node that can have children
// they hold the label bitmap and the child count. In a COMPACT LEAF -- a
// childless node whose segment is at most segMax bytes, which is the great
// majority of nodes: one per stored key -- they hold the path segment itself,
// and the node has neither bitmap nor count. A compact leaf is recognised by
// its prefix string pointing exactly there (see compact), or by its zero child
// capacity; every accessor of the bitmap or the child array checks one of the
// two first. This is how a leaf costs 96 bytes rather than 96 plus a trailing
// segment, at no cost to lookups: the segment shares the first cache line
// with the value, and the bitmap of a leaf is never consulted on a successful
// lookup anyway.
type node struct {
	// prefix is the compressed path segment leading to this node, including
	// the label byte its parent indexes it by. Empty only for the root.
	prefix string
	// val is the value of the key that ends exactly at this node; it is
	// meaningful iff the epoch carries valueBit.
	val any
	// bitmap has one bit per present label; the child for label is the
	// rank(label)-th element of the child array. A node is childless iff the
	// bitmap is zero. In a compact leaf these bytes are the segment.
	bitmap [4]uint64
	// nkids and ckids are the length and the capacity of the child array.
	// In a compact leaf nkids is the segment's tail and ckids stays zero, as
	// in every node without a child array: ckids == 0 is the second way to
	// tell a node without children, in the cache line that holds the count
	// (compact, from the first line, is the other; each accessor uses the
	// one in the line it reads anyway).
	nkids, ckids uint16
	_            [4]byte

	// leaf is the identity of the value, created lazily (see leafOf): a
	// node may hold a value and no leaf yet, but a leaf only with a value.
	// Watchers and copies may create it on a published node, hence atomic.
	leaf  atomic.Pointer[leaf]
	watch watch.Slot
	// epoch is the ownership stamp (plus valueBit and leafOwnedBit).
	epoch uint64
}

// kidsOffset is where the child array of a size-classed node starts: right
// after the header, which is pointer-aligned.
const kidsOffset = unsafe.Sizeof(node{})

// segOffset and segMax delimit the segment area of a compact leaf: the bitmap
// and nkids, up to ckids. No pointer lives in it (the garbage collector never
// looks at these bytes), so it may hold anything.
const (
	segOffset = unsafe.Offsetof(node{}.bitmap)
	segMax    = unsafe.Offsetof(node{}.ckids) - segOffset
)

// The accessors below are the only code that turns a *node into the address
// of a child slot. They rely on two facts that newNode establishes and nothing
// changes: a node with ckids > 0 is the first field of a size-classed struct
// whose array has ckids elements, so slots 0..ckids-1 lie inside the node's own
// allocation (and are typed as pointers, so the garbage collector sees them);
// and nkids <= ckids.

// compact reports whether n is a compact leaf: its segment occupies the
// bitmap and counter bytes. Nothing else ever makes a prefix point to that
// address: the prefixes of other nodes are heap strings, entries of the
// one-byte table, or trailing arrays (segment_unsafe.go) further into the node.
func (n *node) compact() bool {
	return unsafe.Pointer(unsafe.StringData(n.prefix)) == unsafe.Add(unsafe.Pointer(n), segOffset)
}

// segment returns the segment area of n, whatever it holds.
func (n *node) segment() []byte {
	return unsafe.Slice((*byte)(unsafe.Add(unsafe.Pointer(n), segOffset)), segMax)
}

// kidCount reads only the line that holds the counters: nkids never exceeds
// ckids, and ckids is zero wherever nkids is not a count.
func (n *node) kidCount() int { return int(min(n.nkids, n.ckids)) }
func (n *node) kidCap() int   { return int(n.ckids) }

// frameKids is kidCount for a node known to have children -- one an iterator
// holds a frame for.
func (n *node) frameKids() int { return int(n.nkids) }

// childless reads only the first line, which a lookup or an iteration step
// has in hand.
func (n *node) childless() bool {
	return n.compact() || n.bitmap[0]|n.bitmap[1]|n.bitmap[2]|n.bitmap[3] == 0
}

// kid returns child i, which the caller knows to exist: from rank, or because
// i < kidCount().
func (n *node) kid(i int) *node {
	return *(**node)(unsafe.Add(unsafe.Pointer(n), kidsOffset+uintptr(i)*unsafe.Sizeof(n)))
}

func (n *node) setKid(i int, c *node) {
	*(**node)(unsafe.Add(unsafe.Pointer(n), kidsOffset+uintptr(i)*unsafe.Sizeof(n))) = c
}

// kidList returns the children as a slice of the node's own storage.
func (n *node) kidList() []*node {
	if n.ckids == 0 {
		return nil
	}
	return unsafe.Slice((**node)(unsafe.Add(unsafe.Pointer(n), kidsOffset)), n.ckids)[:n.nkids]
}

// setKidCount changes the number of children, within the node's capacity.
// The node must not be a compact leaf.
func (n *node) setKidCount(count int) {
	if count > int(n.ckids) {
		panic("juuri: child array overflow")
	}
	n.nkids = uint16(count) //nolint:gosec // checked against ckids, itself at most 256, just above
}

// Size-classed nodes: a node header followed by the child array. A *node
// obtained from one of these points at the start of the allocation, so the
// garbage collector keeps the array alive, and scans it, without anything
// ever needing to know which class a node came from.
//
// The header is 96 bytes, so the classes are 128, 160, 224, 352 ... bytes. There
// is deliberately no class for two children: it would be 112 bytes, and 112-byte
// objects do not start on cache line boundaries -- the header's hot first line
// would straddle two. 128-byte objects do, and four children in 128 bytes is
// still no more than two children cost with a slice header.
type (
	node4 struct {
		node
		arr [4]*node
	}
	node8 struct {
		node
		arr [8]*node
	}
	node16 struct {
		node
		arr [16]*node
	}
	node32 struct {
		node
		arr [32]*node
	}
	node64 struct {
		node
		arr [64]*node
	}
	node128 struct {
		node
		arr [128]*node
	}
	node256 struct {
		node
		arr [256]*node
	}
)

// The accessors assume that the array starts where the header ends, and the
// compact leaf that its segment area is 34 contiguous bytes.
var (
	_ = [1]struct{}{}[unsafe.Offsetof(node4{}.arr)-kidsOffset]
	_ = [1]struct{}{}[segMax-34]
)

// newNode returns a node with room for capacity children.
func newNode(capacity int) *node {
	switch {
	case capacity <= 0:
		return &node{}
	case capacity <= 4:
		x := &node4{}
		x.ckids = 4
		return &x.node
	case capacity <= 8:
		x := &node8{}
		x.ckids = 8
		return &x.node
	case capacity <= 16:
		x := &node16{}
		x.ckids = 16
		return &x.node
	case capacity <= 32:
		x := &node32{}
		x.ckids = 32
		return &x.node
	case capacity <= 64:
		x := &node64{}
		x.ckids = 64
		return &x.node
	case capacity <= 128:
		x := &node128{}
		x.ckids = 128
		return &x.node
	default:
		x := &node256{}
		x.ckids = 256
		return &x.node
	}
}
