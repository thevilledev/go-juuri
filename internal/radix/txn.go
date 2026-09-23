// Copyright (c) 2026 Ville Vesilehto
// SPDX-License-Identifier: MPL-2.0

package radix

import "sync/atomic"

// epochCounter hands out ownership epochs. It is global on purpose: trees of
// a database and of its snapshots share nodes while having independent
// writers, so an epoch must never be issued twice, to anyone.
var epochCounter atomic.Uint64

// Notifier collects the objects that write transactions replace, so that their
// watchers can be notified once the transaction is committed and visible.
// One Notifier may be shared by all the transactions that commit together.
// It is not safe for concurrent use.
type Notifier struct {
	nodes  []*node
	leaves []*leaf
	// values are nodes that left the tree with their value, which may
	// never have needed a leaf: see sealValue.
	values   []*node
	subtrees []*node
}

// Notify seals every recorded object: watch channels that were handed out are
// closed, and watchers that arrive late (readers still holding an older tree)
// are notified immediately. Call it after the new tree has been published so
// that woken watchers observe the new state. The Notifier is reset for reuse.
func (nf *Notifier) Notify() {
	for i, n := range nf.nodes {
		n.watch.Seal()
		nf.nodes[i] = nil
	}
	for i, l := range nf.leaves {
		l.watch.Seal()
		nf.leaves[i] = nil
	}
	for i, n := range nf.values {
		sealValue(n)
		nf.values[i] = nil
	}
	for i, n := range nf.subtrees {
		sealSubtree(n)
		nf.subtrees[i] = nil
	}
	nf.nodes, nf.leaves, nf.values, nf.subtrees = nf.nodes[:0], nf.leaves[:0], nf.values[:0], nf.subtrees[:0]
}

// Reset forgets everything recorded without notifying anyone (abort).
func (nf *Notifier) Reset() {
	clear(nf.nodes)
	clear(nf.leaves)
	clear(nf.values)
	clear(nf.subtrees)
	nf.nodes, nf.leaves, nf.values, nf.subtrees = nf.nodes[:0], nf.leaves[:0], nf.values[:0], nf.subtrees[:0]
}

// pending reports how many objects are recorded. Used by tests.
func (nf *Notifier) pending() int {
	return len(nf.nodes) + len(nf.leaves) + len(nf.values) + len(nf.subtrees)
}

func sealSubtree(n *node) {
	n.watch.Seal()
	if n.hasValue() {
		sealValue(n)
	}
	for _, k := range n.kidList() {
		sealSubtree(k)
	}
}

// Txn is a write transaction on a tree. It is a small value meant to be
// embedded; it must not be copied once used and is not safe for concurrent
// use.
//
// Ownership rule: a node whose epoch equals the transaction's current epoch
// was created by this transaction since its last Freeze, has never been
// visible to anyone else, and is mutated in place. Every other node is copied
// before it is changed and the original is recorded for notification.
type Txn struct {
	root  *node
	epoch uint64 // 0: no epoch drawn since the last Freeze
	nf    *Notifier
}

// Txn starts a write transaction. If nf is non-nil, replaced objects are
// recorded in it; pass nil for trees whose watchers must never be notified.
func (t Tree) Txn(nf *Notifier) Txn {
	return Txn{root: t.root, nf: nf}
}

// Started reports whether t was created by Tree.Txn, as opposed to being a
// zero Txn. It lets callers keep transactions in preallocated arrays.
func (t *Txn) Started() bool {
	return t.root != nil
}

// Tree returns the transaction's current state. If the result (or anything
// derived from it: an iterator, a watch channel) outlives the next write,
// call Freeze first.
func (t *Txn) Tree() Tree {
	return Tree{root: t.root}
}

// Freeze makes every node created so far immutable, in O(1): the transaction
// simply abandons its epoch and draws a fresh one on its next write. It must
// be called before an iterator or a watch channel is handed out over a tree
// with uncommitted writes, and before such a tree is shared with another
// goroutine. This upholds the invariant the lazy watch protocol rests on: a
// node with a materialised watch slot is never mutated again.
func (t *Txn) Freeze() {
	t.epoch = 0
}

// Commit returns the resulting tree. Notification is separate (see Notifier)
// so the caller can publish the tree first.
func (t *Txn) Commit() Tree {
	t.epoch = 0
	return Tree{root: t.root}
}

func (t *Txn) begin() {
	if t.epoch == 0 {
		t.epoch = epochCounter.Add(1)
	}
}

func (t *Txn) owns(n *node) bool {
	return n.epoch&epochMask == t.epoch
}

func (t *Txn) dropNode(n *node) {
	if t.nf != nil {
		t.nf.nodes = append(t.nf.nodes, n)
	}
}

// dropLeaf records the leaf of a value that an owned node gives up. Such a
// value came from a published node, whose leaf was created when the node was
// copied (see shareLeaf).
func (t *Txn) dropLeaf(l *leaf) {
	if t.nf != nil {
		t.nf.leaves = append(t.nf.leaves, l)
	}
}

// dropValue records the value of n, a published node that leaves the tree
// with it. Its leaf may not exist; Notify then seals it with sealedLeaf.
func (t *Txn) dropValue(n *node) {
	if t.nf != nil {
		t.nf.values = append(t.nf.values, n)
	}
}

// shareLeaf returns the leaf a copy of n, which must hold a value, is to carry.
// A published node's copy must share the leaf with it, so that a watcher of
// either one is notified when the value changes; an owned node's copy replaces
// the node outright, and takes whatever it has.
func (t *Txn) shareLeaf(n *node) *leaf {
	if t.owns(n) {
		return n.leaf.Load()
	}
	return n.leafOf()
}

func (t *Txn) dropSubtree(n *node) {
	if t.nf != nil {
		t.nf.subtrees = append(t.nf.subtrees, n)
	}
}

// copyNode returns an owned copy of n with room for extra more children. The
// child slice is always a fresh array: an owned node grows its slice in place,
// which must never be visible through the original.
func (t *Txn) copyNode(n *node, extra int) *node {
	c := t.copyShape(n, extra)
	if n.hasValue() {
		c.val = n.val
		c.epoch |= valueBit
		if l := t.shareLeaf(n); l != nil {
			c.leaf.Store(l)
		}
	}
	return c
}

// copyShape is copyNode without the value: the copy has n's path segment and
// children only.
func (t *Txn) copyShape(n *node, extra int) *node {
	count := n.kidCount()
	var c *node
	switch {
	case count+extra == 0:
		// Childless stays childless: the copy gets its own inline segment.
		c = newLeafNode(n.prefix, "")
	case n.kidCap() == 0:
		// n may hold its segment inline -- in the very bytes of the bitmap,
		// if it is a compact leaf; sharing it would keep n alive. It has no
		// children, and its bitmap is zero or not a bitmap at all; c's is
		// already zero.
		c = newNode(extra)
		c.prefix = cloneSegment(n.prefix)
	default:
		c = newNode(count + extra)
		c.prefix, c.bitmap = n.prefix, n.bitmap
		c.setKidCount(count)
		copy(c.kidList(), n.kidList())
	}
	c.epoch = t.epoch
	return c
}

// leafNode returns a new owned node holding only a value.
func (t *Txn) leafNode(prefix []byte, v any) *node {
	n := newLeafNode(bytesToString(prefix), "")
	n.epoch, n.val = t.epoch|valueBit|leafOwnedBit, v
	return n
}

// own returns a node the transaction may mutate in place: n itself if it is
// already owned, otherwise a copy that replaces n under parent (or as root).
// parent must be owned.
func (t *Txn) own(parent *node, pidx int, n *node, extra int) *node {
	var c *node
	if t.owns(n) {
		if n.kidCount()+extra <= n.kidCap() {
			return n
		}
		// An owned node that has outgrown its inline child array moves to
		// a bigger size class (with headroom, so bulk loads amortise). It
		// was never visible to anyone, so nothing needs to be recorded.
		c = t.copyNode(n, n.kidCount()+extra)
		c.epoch = n.epoch
	} else {
		c = t.copyNode(n, extra)
		t.dropNode(n)
	}
	t.link(parent, pidx, c)
	return c
}

// link puts the owned node c at parent.kids[pidx], or makes it the root.
func (t *Txn) link(parent *node, pidx int, c *node) {
	if parent == nil {
		t.root = c
	} else {
		parent.setKid(pidx, c) // same label as before: bitmap unchanged
	}
}

// releaseValue records that the value of n leaves the tree: n is about to be
// removed, or replaced by a node without it.
func (t *Txn) releaseValue(n *node) {
	switch {
	case !t.owns(n):
		t.dropValue(n)
	case n.epoch&leafOwnedBit == 0:
		// Stored before this epoch: the value of a published node, whose
		// leaf the copy made in this epoch created (see shareLeaf).
		t.dropLeaf(n.leaf.Load())
	}
}

// ownValueless is own for a node about to lose its value: it returns an owned
// node with n's path segment and children but no value. A published n is not
// copied with the value only to drop it again: its copy never shares the
// leaf, and n itself is recorded as leaving the tree with the value.
func (t *Txn) ownValueless(parent *node, pidx int, n *node) *node {
	if n.hasValue() {
		t.releaseValue(n)
	}
	if t.owns(n) {
		if n.leaf.Load() != nil {
			n.leaf.Store(nil)
		}
		n.val = nil
		n.epoch &^= valueBit | leafOwnedBit
		return n
	}
	c := t.copyShape(n, 0)
	t.dropNode(n)
	t.link(parent, pidx, c)
	return c
}

// setValue stores v in n, which sits at parent.kids[pidx] (or is the root),
// and returns the value it replaces. parent must be owned.
func (t *Txn) setValue(parent *node, pidx int, n *node, v any) (any, bool) {
	old, existed := n.val, n.hasValue()
	if existed && t.owns(n) && n.epoch&leafOwnedBit != 0 {
		// The old value was stored by this transaction in this epoch:
		// nobody can have seen or watched it, so it needs no notification.
		n.val = v
		return old, true
	}
	n = t.ownValueless(parent, pidx, n)
	n.val = v
	n.epoch |= valueBit | leafOwnedBit
	return old, existed
}

// Insert stores v under k and returns the previous value, if any. The tree
// keeps no reference to k.
func (t *Txn) Insert(k []byte, v any) (any, bool) {
	t.begin()

	var parent *node
	pidx := 0
	n := t.root
	search := k
	for {
		if len(search) == 0 {
			// The key ends at n.
			return t.setValue(parent, pidx, n, v)
		}

		idx, ok := n.rank(search[0])
		if !ok {
			// No edge for the next byte: hang a new leaf node below n.
			n = t.own(parent, pidx, n, 1)
			n.addKid(idx, t.leafNode(search, v))
			return nil, false
		}

		child := n.kid(idx)
		common := commonPrefixLen(search, child.prefix)
		n = t.own(parent, pidx, n, 0)
		if common == len(child.prefix) {
			parent, pidx = n, idx
			n = child
			search = search[common:]
			continue
		}

		// The key diverges inside child's path segment: split it. The
		// child keeps its leaf object (and that leaf's watchers); only
		// its prefix is trimmed.
		trimmed := child
		if !t.owns(child) {
			trimmed = t.copyNode(child, 0)
			t.dropNode(child)
		}
		split := newNode(2)
		split.epoch, split.prefix = t.epoch, child.prefix[:common]
		if child.kidCap() == 0 {
			// The child may hold its segment inline: do not share it,
			// and take the copy before the trim below moves the bytes.
			split.prefix = cloneSegment(split.prefix)
		}
		trimmed.trimPrefix(common)
		n.setKid(idx, split) // same label as before: bitmap unchanged

		rest := search[common:]
		if len(rest) == 0 {
			split.val = v
			split.epoch |= valueBit | leafOwnedBit
			split.setKidCount(1)
			split.setKid(0, trimmed)
		} else {
			added := t.leafNode(rest, v)
			split.setKidCount(2)
			if added.prefix[0] < trimmed.prefix[0] {
				split.setKid(0, added)
				split.setKid(1, trimmed)
			} else {
				split.setKid(0, trimmed)
				split.setKid(1, added)
			}
			split.bitmap[added.prefix[0]>>6] |= uint64(1) << (added.prefix[0] & 63)
		}
		split.bitmap[trimmed.prefix[0]>>6] |= uint64(1) << (trimmed.prefix[0] & 63)
		return nil, false
	}
}

type pathEntry struct {
	n   *node
	idx int // position, in n, of the next node on the path
}

// ownPath makes every node of a root-to-parent path owned, in place: on
// return path[i].n is the owned node of level i.
func (t *Txn) ownPath(path []pathEntry) {
	var parent *node
	pidx := 0
	for i := range path {
		parent = t.own(parent, pidx, path[i].n, 0)
		path[i].n, pidx = parent, path[i].idx
	}
}

// unlink removes the child at the end of a root-to-parent path from its
// parent, making the path owned, and restores the tree's shape: a parent left
// with no value and a single child is merged with that child -- directly, not
// copied first only to be replaced. The root is exempt.
func (t *Txn) unlink(path []pathEntry) {
	last := len(path) - 1
	parent, idx := path[last].n, path[last].idx
	if last > 0 && !parent.hasValue() && parent.kidCount() == 2 {
		t.ownPath(path[:last])
		if !t.owns(parent) {
			t.dropNode(parent)
		}
		t.mergeChild(path[last-1].n, path[last-1].idx, parent, parent.kid(1-idx))
		return
	}
	t.ownPath(path)
	path[last].n.delKid(idx)
}

// Delete removes k and returns its value. Deleting a missing key leaves the
// tree -- and every watcher -- untouched.
func (t *Txn) Delete(k []byte) (any, bool) {
	// Read-only descent first, so that a miss copies nothing.
	var buf [24]pathEntry
	path := buf[:0]
	n := t.root
	search := k
	for len(search) > 0 {
		idx, ok := n.rank(search[0])
		if !ok {
			return nil, false
		}
		c := n.kid(idx)
		if !c.hasPrefix(search) {
			return nil, false
		}
		path = append(path, pathEntry{n, idx})
		search = search[len(c.prefix):]
		n = c
	}
	if !n.hasValue() {
		return nil, false
	}
	old := n.val

	t.begin()
	switch {
	case len(path) == 0:
		// The root is never removed or merged.
		t.ownValueless(nil, 0, n)
	case n.childless():
		// The node disappears altogether.
		t.dropWithLeaf(n)
		t.unlink(path)
	case n.kidCount() == 1:
		// Left with no value and a single child: merged with the child,
		// without being copied first.
		t.ownPath(path)
		t.dropWithLeaf(n)
		t.mergeChild(path[len(path)-1].n, path[len(path)-1].idx, n, n.kid(0))
	default:
		t.ownPath(path)
		t.ownValueless(path[len(path)-1].n, path[len(path)-1].idx, n)
	}
	return old, true
}

// dropWithLeaf records n and its value as leaving the tree, as far as anybody
// else can have seen them.
func (t *Txn) dropWithLeaf(n *node) {
	t.releaseValue(n)
	if !t.owns(n) {
		t.dropNode(n)
	}
}

// mergeChild replaces n -- which sits at parent.kids[pidx], has no value (or
// is giving it up), and is left with the single child c -- with that child,
// whose path segment absorbs n's. n itself must already be accounted for. The
// child keeps its leaf, so the watchers of that key are not disturbed; the
// child node itself is replaced (and its watchers notified) unless this
// transaction owns it. parent must be owned.
func (t *Txn) mergeChild(parent *node, pidx int, n, c *node) {
	var m *node
	switch {
	case c.childless():
		// A childless result gets the joined segment inline.
		m = newLeafNode(n.prefix, c.prefix)
		m.val = c.val
		if l := t.shareLeaf(c); l != nil {
			m.leaf.Store(l)
		}
		m.epoch = t.epoch | valueBit
		if t.owns(c) {
			m.epoch |= c.epoch & leafOwnedBit
		}
	case t.owns(c):
		m = c
		m.prefix = n.prefix + c.prefix
	default:
		m = t.copyNode(c, 0)
		m.prefix = n.prefix + c.prefix
	}
	if !t.owns(c) {
		t.dropNode(c)
	}
	parent.setKid(pidx, m) // same label as n: the parent's bitmap is unchanged
}

// DeletePrefix removes every key starting with prefix in one subtree cut and
// reports whether a matching subtree existed.
func (t *Txn) DeletePrefix(prefix []byte) bool {
	var buf [24]pathEntry
	path := buf[:0]
	n := t.root
	search := prefix
	for len(search) > 0 {
		idx, ok := n.rank(search[0])
		if !ok {
			return false
		}
		c := n.kid(idx)
		switch {
		case c.hasPrefix(search):
			search = search[len(c.prefix):]
		case len(search) < len(c.prefix) && c.prefix[:len(search)] == string(search):
			search = nil
		default:
			return false
		}
		path = append(path, pathEntry{n, idx})
		n = c
	}

	t.begin()
	// Everything at and below n goes away; its watchers are found by
	// walking the subtree when (and only if) the transaction commits.
	t.dropSubtree(n)
	if len(path) == 0 {
		t.root = &node{epoch: t.epoch}
		return true
	}
	t.unlink(path)
	return true
}
