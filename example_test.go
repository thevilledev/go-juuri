// Copyright (c) 2026 Ville Vesilehto
// SPDX-License-Identifier: MPL-2.0

package juuri_test

import (
	"fmt"

	"github.com/thevilledev/go-juuri"
)

// Reads and writes: a transaction applies changes, Commit returns the tree
// they produced, and the tree handed to Txn stays valid.
func Example() {
	tree := juuri.New()
	txn := tree.Txn(nil)
	txn.Insert([]byte("foo"), 1)
	txn.Insert([]byte("foobar"), 2)
	tree = txn.Commit()

	fmt.Println(tree.Get([]byte("foo")))
	fmt.Println(tree.LongestPrefix([]byte("foobaz")))

	var it juuri.Iterator
	it.SeekPrefixWatch(tree, []byte("foo"))
	for value, ok := it.Next(); ok; value, ok = it.Next() {
		fmt.Println(value)
	}

	// Output:
	// 1 true
	// 1 true
	// 1
	// 2
}

// Watching a key: commit, publish the new tree, then notify.
func Example_watch() {
	tree := juuri.New()
	txn := tree.Txn(nil)
	txn.Insert([]byte("foo"), 1)
	tree = txn.Commit()

	watch, value, ok := tree.GetWatch([]byte("foo"))
	fmt.Println(value, ok)
	changed := watch.Chan()

	var notifier juuri.Notifier
	txn = tree.Txn(&notifier)
	txn.Insert([]byte("foo"), 2)
	tree = txn.Commit()
	notifier.Notify()

	<-changed
	fmt.Println(tree.Get([]byte("foo")))

	// Output:
	// 1 true
	// 2 true
}
