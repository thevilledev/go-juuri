// Copyright (c) 2026 Ville Vesilehto
// SPDX-License-Identifier: MPL-2.0

package juuri

import "github.com/thevilledev/go-juuri/internal/radix"

// Notifier collects the objects that write transactions replace, so that their
// watchers can be notified once the transaction is committed and visible.
// One Notifier may be shared by all the transactions that commit together.
// It is not safe for concurrent use.
type Notifier struct {
	n radix.Notifier
}

// Notify seals every recorded object: watch channels that were handed out are
// closed, and watchers that arrive late (readers still holding an older tree)
// are notified immediately. Call it after the new tree has been published so
// that woken watchers observe the new state. The Notifier is reset for reuse.
func (nf *Notifier) Notify() {
	nf.n.Notify()
}

// Reset forgets everything recorded without notifying anyone (abort).
func (nf *Notifier) Reset() {
	nf.n.Reset()
}

// Txn is a write transaction on a tree. It is a small value meant to be
// embedded; it must not be copied once used and is not safe for concurrent
// use.
type Txn struct {
	txn radix.Txn
}

// Txn starts a write transaction. If nf is non-nil, replaced objects are
// recorded in it; pass nil for trees whose watchers must never be notified.
func (t Tree) Txn(nf *Notifier) Txn {
	var n *radix.Notifier
	if nf != nil {
		n = &nf.n
	}
	return Txn{txn: t.tree.Txn(n)}
}

// Started reports whether t was created by Tree.Txn, as opposed to being a
// zero Txn. It lets callers keep transactions in preallocated arrays.
func (t *Txn) Started() bool {
	return t.txn.Started()
}

// Tree returns the transaction's current state. If the result (or anything
// derived from it: an iterator, a watch channel) outlives the next write,
// call Freeze first.
func (t *Txn) Tree() Tree {
	return Tree{tree: t.txn.Tree()}
}

// Freeze makes every node created so far immutable, in O(1). It must be called
// before an iterator or a watch channel is handed out over a tree with
// uncommitted writes, and before such a tree is shared with another goroutine.
func (t *Txn) Freeze() {
	t.txn.Freeze()
}

// Commit returns the resulting tree. Notification is separate (see Notifier)
// so the caller can publish the tree first.
func (t *Txn) Commit() Tree {
	return Tree{tree: t.txn.Commit()}
}

// Insert stores v under k and returns the previous value, if any. The tree
// keeps no reference to k.
func (t *Txn) Insert(k []byte, v any) (any, bool) {
	return t.txn.Insert(k, v)
}

// Delete removes k and returns its value. Deleting a missing key leaves the
// tree -- and every watcher -- untouched.
func (t *Txn) Delete(k []byte) (any, bool) {
	return t.txn.Delete(k)
}

// DeletePrefix removes every key starting with prefix in one subtree cut and
// reports whether a matching subtree existed.
func (t *Txn) DeletePrefix(prefix []byte) bool {
	return t.txn.DeletePrefix(prefix)
}
