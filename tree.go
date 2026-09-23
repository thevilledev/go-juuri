// Copyright (c) 2026 Ville Vesilehto
// SPDX-License-Identifier: MPL-2.0

package juuri

import "github.com/thevilledev/go-juuri/internal/radix"

// Tree is an immutable radix tree. It is a one-pointer value: copy it freely.
// A Tree obtained from a committed transaction never changes, so any number of
// goroutines may read it without coordination.
type Tree struct {
	tree radix.Tree
}

// New returns an empty tree. Every tree gets its own root node: a watch on
// "the whole tree" is a watch on that node, so two trees must never share it.
func New() Tree {
	return Tree{tree: radix.New()}
}

// Watch identifies a point in the tree that can be watched. Its channel is
// materialised on the first call to Chan, so a Watch that is never consulted
// costs nothing. The zero Watch has a nil channel, which blocks forever.
type Watch struct {
	w radix.Watch
}

// Chan returns the channel that is closed when a committed transaction
// replaces the watched object: for a key, when it is updated or deleted; for a
// node, when anything in its subtree changes.
func (w Watch) Chan() <-chan struct{} {
	return w.w.Chan()
}

// Get returns the value stored under k.
func (t Tree) Get(k []byte) (any, bool) {
	return t.tree.Get(k)
}

// GetWatch is Get plus a watch. On a hit the watch covers exactly that key.
// On a miss it covers the deepest node on the search path -- including a child
// whose prefix diverges from the key -- which is the node an insert of k would
// have to replace, so the watch fires when k is created.
func (t Tree) GetWatch(k []byte) (Watch, any, bool) {
	w, v, ok := t.tree.GetWatch(k)
	return Watch{w: w}, v, ok
}

// LongestPrefix returns the value of the longest stored key that is a prefix
// of k.
func (t Tree) LongestPrefix(k []byte) (any, bool) {
	return t.tree.LongestPrefix(k)
}

// FirstPrefix returns the value of the smallest key starting with prefix,
// without allocating an iterator, plus a watch covering that prefix.
func (t Tree) FirstPrefix(prefix []byte) (Watch, any, bool) {
	w, v, ok := t.tree.FirstPrefix(prefix)
	return Watch{w: w}, v, ok
}

// LastPrefix returns the value of the greatest key starting with prefix, plus
// a watch covering that prefix.
func (t Tree) LastPrefix(prefix []byte) (Watch, any, bool) {
	w, v, ok := t.tree.LastPrefix(prefix)
	return Watch{w: w}, v, ok
}

// Len counts the keys in the tree. It walks the whole tree; it exists for
// tests and diagnostics, not for hot paths.
func (t Tree) Len() int {
	return t.tree.Len()
}
