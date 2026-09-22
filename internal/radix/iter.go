// Copyright (c) 2026 Ville Vesilehto
// SPDX-License-Identifier: MPL-2.0

package radix

import "github.com/thevilledev/go-juuri/internal/watch"

// frame is one level of an in-progress traversal: a node and the position of
// the next child to visit. The meaning of i differs per direction, see below.
// A node has at most 256 children, so the position fits 16 bits -- which keeps
// an iterator, the one object every Get allocates, in a smaller size class.
type frame struct {
	n *node
	i int16
}

// inlineFrames is the traversal depth an iterator handles without allocating.
// A frame is only needed per branching level, so this covers typical indexes;
// deeper paths spill to the heap.
const inlineFrames = 8

// stack is an explicit traversal stack with inline storage. It is addressed by
// depth rather than by a slice into itself, so the enclosing iterator stays a
// plain value that can be embedded and moved before first use. The inline
// frames are kept as two arrays: side by side, the padding after each 16-bit
// position would cost as much as the node pointers.
type stack struct {
	depth int
	nodes [inlineFrames]*node
	pos   [inlineFrames]int16
	spill []frame
}

func (s *stack) push(n *node, i int) {
	// A position is a child index of at most 256, or one of the small
	// negative markers; it always fits int16.
	if s.depth < inlineFrames {
		s.nodes[s.depth], s.pos[s.depth] = n, int16(i) //nolint:gosec // bounded by 256 children
	} else {
		s.spill = append(s.spill[:s.depth-inlineFrames], frame{n, int16(i)}) //nolint:gosec // bounded by 256 children
	}
	s.depth++
}

// top returns the node of the top frame and a pointer to its position.
func (s *stack) top() (*node, *int16) {
	if s.depth <= inlineFrames {
		return s.nodes[s.depth-1], &s.pos[s.depth-1]
	}
	f := &s.spill[s.depth-1-inlineFrames]
	return f.n, &f.i
}

func (s *stack) reset() {
	s.depth = 0
	s.spill = s.spill[:0]
}

// Iterator walks a tree in ascending key order. The zero value is an exhausted
// iterator; position it with one of the Seek methods.
//
// Forward frames: i < 0 means the node's own leaf has not been emitted yet
// (a key sorts before every key it is a prefix of); otherwise i is the index
// of the next child to descend into. A frame with i >= 0 is always a node
// with children, which is what lets Next read its child count without the
// compact-leaf check: a childless node is pushed as leafOnly, and emitted and
// popped in one step.
type Iterator struct {
	s stack
}

// leafOnly marks a forward frame whose node has no children: its value is
// emitted and the frame dropped without ever looking at a child count.
const leafOnly = -2

// pushSubtree pushes a frame for n and everything below it. A childless node
// without a value -- only an empty root -- has nothing to emit.
func (it *Iterator) pushSubtree(n *node) {
	switch {
	case !n.childless():
		it.s.push(n, -1)
	case n.hasValue():
		it.s.push(n, leafOnly)
	}
}

// SeekPrefixWatch positions the iterator on the keys of t that start with
// prefix and returns the finest-grained watch covering that prefix.
func (it *Iterator) SeekPrefixWatch(t Tree, prefix []byte) *watch.Slot {
	it.s.reset()
	n, w := t.seekPrefix(prefix)
	if n != nil {
		it.pushSubtree(n)
	}
	return w
}

// SeekLowerBound positions the iterator on the smallest key >= key; iteration
// then continues to the end of the tree.
func (it *Iterator) SeekLowerBound(t Tree, key []byte) {
	it.s.reset()
	n := t.root
	search := key
	for {
		common := commonPrefixLen(search, n.prefix)
		if common < len(n.prefix) {
			// The key leaves this node's path segment. If it ends here, or
			// continues with a smaller byte, the whole subtree is greater
			// than the key; otherwise the whole subtree is smaller.
			if common == len(search) || n.prefix[common] > search[common] {
				it.pushSubtree(n)
			}
			return
		}
		search = search[common:]
		if len(search) == 0 {
			// The key ends exactly here: this node and everything below.
			it.pushSubtree(n)
			return
		}
		idx, ok := n.rank(search[0])
		if !ok {
			// No child for the next byte: continue with the first child
			// that has a greater label, if there is one. This node's own
			// key is smaller.
			if idx < n.kidCount() {
				it.s.push(n, idx)
			}
			return
		}
		// Resume with the next sibling once the exact child is done.
		it.s.push(n, idx+1)
		n = n.kid(idx)
	}
}

// Next returns the next value in ascending key order.
func (it *Iterator) Next() (any, bool) {
	s := &it.s
	for s.depth > 0 {
		n, i := s.top()
		if *i < 0 {
			if *i == leafOnly {
				s.depth--
				return n.val, true
			}
			*i = 0
			if n.hasValue() {
				return n.val, true
			}
		}
		if int(*i) >= n.frameKids() {
			s.depth--
			continue
		}
		c := n.kid(int(*i))
		*i++
		if c.childless() {
			// A childless node always carries a value; skip the frame.
			return c.val, true
		}
		s.push(c, -1)
	}
	return nil, false
}

// ReverseIterator walks a tree in descending key order.
//
// Reverse frames: i >= 0 is the index of the next child to descend into,
// counting down; i < 0 means only the node's own leaf is left, which is
// emitted last.
type ReverseIterator struct {
	s stack
}

// SeekPrefixWatch positions the iterator on the keys of t that start with
// prefix, to be visited in descending order.
func (it *ReverseIterator) SeekPrefixWatch(t Tree, prefix []byte) *watch.Slot {
	it.s.reset()
	n, w := t.seekPrefix(prefix)
	if n != nil {
		it.s.push(n, n.kidCount()-1)
	}
	return w
}

// SeekReverseLowerBound positions the iterator on the greatest key <= key;
// iteration then continues down to the start of the tree.
func (it *ReverseIterator) SeekReverseLowerBound(t Tree, key []byte) {
	it.s.reset()
	n := t.root
	search := key
	for {
		common := commonPrefixLen(search, n.prefix)
		if common < len(n.prefix) {
			// Mirror image of SeekLowerBound: the subtree qualifies as a
			// whole only if it is entirely smaller than the key.
			if common < len(search) && n.prefix[common] < search[common] {
				it.s.push(n, n.kidCount()-1)
			}
			return
		}
		search = search[common:]
		if len(search) == 0 {
			// The key ends exactly here. Children extend the key, so they
			// are greater; only this node's own leaf qualifies.
			it.s.push(n, -1)
			return
		}
		idx, ok := n.rank(search[0])
		// Children left of idx are smaller than the key, as is this node's
		// own leaf: they follow once the exact child (if any) is done.
		it.s.push(n, idx-1)
		if !ok {
			return
		}
		n = n.kid(idx)
	}
}

// Previous returns the next value in descending key order.
func (it *ReverseIterator) Previous() (any, bool) {
	s := &it.s
	for s.depth > 0 {
		n, i := s.top()
		if *i < 0 {
			s.depth--
			if n.hasValue() {
				return n.val, true
			}
			continue
		}
		c := n.kid(int(*i))
		*i--
		if c.childless() {
			return c.val, true
		}
		s.push(c, c.frameKids()-1)
	}
	return nil, false
}
