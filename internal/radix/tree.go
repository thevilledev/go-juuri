// Copyright (c) 2026 Ville Vesilehto
// SPDX-License-Identifier: MPL-2.0

package radix

import "github.com/thevilledev/go-juuri/internal/watch"

// Tree is an immutable radix tree. It is a one-pointer value: copy it freely.
// A Tree obtained from a committed transaction never changes, so any number of
// goroutines may read it without coordination.
type Tree struct {
	root *node
}

// New returns an empty tree. Every tree gets its own root node: a watch on
// "the whole tree" is a watch on that node, so two trees must never share it.
func New() Tree {
	return Tree{root: &node{}}
}

// Get returns the value stored under k.
func (t Tree) Get(k []byte) (any, bool) {
	// (The loops below spell out child: rank and kid are inlined here, child
	// as a whole is over the inlining budget and would cost a call per level.)
	n := t.root
	search := k
	for len(search) > 0 {
		idx, ok := n.rank(search[0])
		if !ok {
			return nil, false
		}
		n = n.kid(idx)
		if !n.hasPrefix(search) {
			return nil, false
		}
		search = search[len(n.prefix):]
	}
	if !n.hasValue() {
		return nil, false
	}
	return n.val, true
}

// GetWatch is Get plus a watch. On a hit the watch covers exactly that key.
// On a miss it covers the deepest node on the search path -- including a child
// whose prefix diverges from the key -- which is the node an insert of k would
// have to replace, so the watch fires when k is created.
func (t Tree) GetWatch(k []byte) (*watch.Slot, any, bool) {
	n := t.root
	w := &n.watch
	search := k
	for len(search) > 0 {
		idx, ok := n.rank(search[0])
		if !ok {
			return w, nil, false
		}
		n = n.kid(idx)
		w = &n.watch
		if !n.hasPrefix(search) {
			return w, nil, false
		}
		search = search[len(n.prefix):]
	}
	if !n.hasValue() {
		return w, nil, false
	}
	return &n.leafOf().watch, n.val, true
}

// LongestPrefix returns the value of the longest stored key that is a prefix
// of k.
func (t Tree) LongestPrefix(k []byte) (any, bool) {
	var last *node
	n := t.root
	search := k
	for {
		if n.hasValue() {
			last = n
		}
		if len(search) == 0 {
			break
		}
		idx, ok := n.rank(search[0])
		if !ok {
			break
		}
		n = n.kid(idx)
		if !n.hasPrefix(search) {
			break
		}
		search = search[len(n.prefix):]
	}
	if last == nil {
		return nil, false
	}
	return last.val, true
}

// seekPrefix finds the node whose subtree holds exactly the keys starting with
// prefix (nil if there are none) and the finest-grained watch slot for that
// prefix: the deepest node reached, whether or not the prefix was found.
func (t Tree) seekPrefix(prefix []byte) (*node, *watch.Slot) {
	n := t.root
	w := &n.watch
	search := prefix
	for len(search) > 0 {
		idx, ok := n.rank(search[0])
		if !ok {
			return nil, w
		}
		n = n.kid(idx)
		w = &n.watch
		if n.hasPrefix(search) {
			search = search[len(n.prefix):]
			continue
		}
		if len(search) < len(n.prefix) && n.prefix[:len(search)] == string(search) {
			// The prefix ends inside this node's path segment.
			return n, w
		}
		return nil, w
	}
	return n, w
}

// FirstPrefix returns the value of the smallest key starting with prefix,
// without allocating an iterator.
func (t Tree) FirstPrefix(prefix []byte) (*watch.Slot, any, bool) {
	n, w := t.seekPrefix(prefix)
	if n == nil {
		return w, nil, false
	}
	m := n.minNode()
	if m == nil {
		return w, nil, false
	}
	return w, m.val, true
}

// LastPrefix returns the value of the greatest key starting with prefix.
func (t Tree) LastPrefix(prefix []byte) (*watch.Slot, any, bool) {
	n, w := t.seekPrefix(prefix)
	if n == nil {
		return w, nil, false
	}
	m := n.maxNode()
	if m == nil {
		return w, nil, false
	}
	return w, m.val, true
}

// Len counts the keys in the tree. It walks the whole tree; it exists for
// tests and diagnostics, not for hot paths.
func (t Tree) Len() int {
	return countLeaves(t.root)
}

func countLeaves(n *node) int {
	c := 0
	if n.hasValue() {
		c = 1
	}
	for _, k := range n.kidList() {
		c += countLeaves(k)
	}
	return c
}
