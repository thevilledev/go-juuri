// Copyright (c) 2026 Ville Vesilehto
// SPDX-License-Identifier: MPL-2.0

package juuri

import "github.com/thevilledev/go-juuri/internal/radix"

// Iterator walks a tree in ascending key order. The zero value is an exhausted
// iterator; position it with one of the Seek methods.
type Iterator struct {
	iter radix.Iterator
}

// SeekPrefixWatch positions the iterator on the keys of t that start with
// prefix and returns the finest-grained watch covering that prefix.
func (it *Iterator) SeekPrefixWatch(t Tree, prefix []byte) Watch {
	return Watch{w: it.iter.SeekPrefixWatch(t.tree, prefix)}
}

// SeekLowerBound positions the iterator on the smallest key >= key; iteration
// then continues to the end of the tree.
func (it *Iterator) SeekLowerBound(t Tree, key []byte) {
	it.iter.SeekLowerBound(t.tree, key)
}

// Next returns the next value in ascending key order.
func (it *Iterator) Next() (any, bool) {
	return it.iter.Next()
}

// ReverseIterator walks a tree in descending key order. The zero value is an
// exhausted iterator; position it with one of the Seek methods.
type ReverseIterator struct {
	iter radix.ReverseIterator
}

// SeekPrefixWatch positions the iterator on the keys of t that start with
// prefix, to be visited in descending order, and returns the finest-grained
// watch covering that prefix.
func (it *ReverseIterator) SeekPrefixWatch(t Tree, prefix []byte) Watch {
	return Watch{w: it.iter.SeekPrefixWatch(t.tree, prefix)}
}

// SeekReverseLowerBound positions the iterator on the greatest key <= key;
// iteration then continues down to the start of the tree.
func (it *ReverseIterator) SeekReverseLowerBound(t Tree, key []byte) {
	it.iter.SeekReverseLowerBound(t.tree, key)
}

// Previous returns the next value in descending key order.
func (it *ReverseIterator) Previous() (any, bool) {
	return it.iter.Previous()
}
