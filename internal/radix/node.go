// Copyright (c) 2026 Ville Vesilehto
// SPDX-License-Identifier: MPL-2.0

// Package radix implements the radix tree behind the juuri package: node
// layout, lookups, iteration, and copy-on-write transactions.
//
// Three decisions shape the code:
//
//   - Ownership epochs. A transaction may mutate a node in place iff the node
//     carries the transaction's current epoch; every other node is copied on
//     first write. There is no per-transaction cache to consult or overflow.
//   - Lazy watch channels. A node or leaf has an atomic watch slot (see
//     internal/watch) that stays nil until somebody actually watches it.
//     Writers never allocate channels; they record the objects they replace
//     and seal them after commit.
//   - Rank-indexed children. A node keeps a 256-bit label bitmap and a dense,
//     label-ordered child array; a child's position is the population count of
//     the bitmap below its label (the rank trick of Roaring bitmaps and HAMTs).
//     Copies are exactly sized: 8 bytes per child.
//
// The node itself is declared twice, in node_unsafe.go and node_safe.go, with
// the same fields in a different arrangement; everything else reaches a node's
// children through the accessors the two files define. The build tag
// juuri_safe (memdb_safe and purego are honoured as well) selects the
// declaration that uses no package unsafe.
package radix

import (
	"math/bits"
	"strings"

	"github.com/thevilledev/go-juuri/internal/watch"
)

// leaf is the identity of one version of one key's value: the thing a watcher
// of that key watches. It is a separate object, shared by every copy of the
// node that holds the key, so that its watch slot survives node copies:
// splitting or merging a node must not notify watchers of an unchanged key --
// and a reader that arrives late, through an older copy of the node, must
// still be notified when the key finally does change.
//
// The value itself lives in the node (node.val), next to everything else a
// lookup or an iteration step needs: reads never touch the leaf object unless
// they ask for a watch.
//
// Most values are never watched, and most are never copied to another node
// either, so the leaf is created lazily (see leafOf): only when a watcher asks
// for it, or when a copy of the node must share it with the original. Until
// then the value's identity is simply the one node that holds it. A node whose
// value leaves the tree without ever having had a leaf gets sealedLeaf on
// notification, so that a late watcher still finds it stale.
type leaf struct {
	watch watch.Slot
}

// sealedLeaf stands for every value that left a committed tree before anybody
// needed its leaf.
var sealedLeaf = func() *leaf {
	l := &leaf{}
	l.watch.Seal()
	return l
}()

// Two bits are stolen from node.epoch. valueBit records that a key ends at the
// node: node.val is meaningful. leafOwnedBit records that the value was stored
// in the node's own epoch, so it has never been visible to anyone else -- its
// leaf does not exist -- and need not be tracked for notification when replaced
// again.
const (
	leafOwnedBit = uint64(1) << 63
	valueBit     = uint64(1) << 62
	epochMask    = valueBit - 1
)

// hasValue reports whether a key ends at n.
func (n *node) hasValue() bool {
	return n.epoch&valueBit != 0
}

// leafOf returns the leaf of n's value, creating it if nobody has needed it
// yet. n must hold a value. It may be called on a published node, concurrently
// with readers doing the same: the first leaf installed wins.
func (n *node) leafOf() *leaf {
	if l := n.leaf.Load(); l != nil {
		return l
	}
	l := &leaf{}
	if n.leaf.CompareAndSwap(nil, l) {
		return l
	}
	return n.leaf.Load()
}

// sealValue seals the leaf of the value of n, a node that has left the tree:
// the leaf's watchers are notified, and a leaf that was never created becomes
// sealedLeaf, so that a watcher arriving through an old tree is notified too.
func sealValue(n *node) {
	l := n.leaf.Load()
	if l == nil {
		if n.leaf.CompareAndSwap(nil, sealedLeaf) {
			return
		}
		l = n.leaf.Load() // a watcher got there first
	}
	l.watch.Seal()
}

// oneByte holds every one-byte string, so that the (very common) one-byte
// path segments need no allocation.
var oneByte = func() (t [256]string) {
	for i := range t {
		t[i] = string([]byte{byte(i)})
	}
	return t
}()

// cloneSegment returns a copy of s that shares no memory with it.
func cloneSegment(s string) string {
	if len(s) == 1 {
		return oneByte[s[0]]
	}
	return strings.Clone(s)
}

// rank returns the position of label among the node's children and whether a
// child with that label exists. When it does not, the position is where such
// a child would be inserted, i.e. the index of the first child with a greater
// label.
//
// The shape of the function is dictated by the inliner's budget: it is called
// once per level of every lookup and must stay inlinable, with the compact
// check included. Within that budget it avoids branching on the label, whose
// word index is as unpredictable as the key: the label's own word is shifted
// so that its bit lands on top, which answers both results at once, and the
// first word is added without a branch -- shifted out of existence when the
// label is in it, as Go defines a shift by 64 to give zero. Only labels of 128
// and above loop over the words between.
func (n *node) rank(label byte) (int, bool) {
	if n.compact() {
		return 0, false
	}
	w := label >> 6
	x := n.bitmap[w] << (^label & 63)
	idx := bits.OnesCount64(x<<1) + bits.OnesCount64(n.bitmap[0]<<((w-1)&64))
	for w > 1 {
		w--
		idx += bits.OnesCount64(n.bitmap[w])
	}
	return idx, x>>63 != 0
}

// addKid inserts c at position idx. The node must be owned by the caller and
// have room for one more child (see Txn.own).
func (n *node) addKid(idx int, c *node) {
	label := c.prefix[0]
	count := n.kidCount()
	n.setKidCount(count + 1)
	kids := n.kidList()
	copy(kids[idx+1:], kids[idx:count])
	kids[idx] = c
	n.bitmap[label>>6] |= uint64(1) << (label & 63)
}

// delKid removes the child at position idx. The node must be owned.
func (n *node) delKid(idx int) {
	kids := n.kidList()
	label := kids[idx].prefix[0]
	last := len(kids) - 1
	copy(kids[idx:], kids[idx+1:])
	kids[last] = nil
	n.setKidCount(last)
	n.bitmap[label>>6] &^= uint64(1) << (label & 63)
}

// hasPrefix reports whether search starts with the node's prefix. It must only
// be called on a child found under search[0]: the first byte is then known to
// match, and a one-byte segment need not be read from memory at all. The
// string conversion in the comparison does not allocate.
func (n *node) hasPrefix(search []byte) bool {
	l := len(n.prefix)
	if l == 1 {
		return true
	}
	if l == 2 {
		// A key's last byte followed by a terminator is the commonest
		// multi-byte segment; compared here rather than through the
		// runtime's memequal, whose call costs more than the byte. The
		// one-byte case above stays first: a deep trie meets it at every
		// level, and an extra compare there costs more than this saves.
		return len(search) >= 2 && search[1] == n.prefix[1]
	}
	return len(search) >= l && string(search[1:l]) == n.prefix[1:]
}

// commonPrefixLen returns the length of the longest common prefix.
func commonPrefixLen(a []byte, b string) int {
	limit := min(len(a), len(b))
	i := 0
	for i < limit && a[i] == b[i] {
		i++
	}
	return i
}

// minNode returns the node holding the smallest key at or below n, or nil. A
// node's own key sorts before the keys of its children.
func (n *node) minNode() *node {
	for {
		if n.hasValue() {
			return n
		}
		if n.kidCount() == 0 {
			return nil // only an empty root
		}
		n = n.kid(0)
	}
}

// maxNode returns the node holding the greatest key at or below n, or nil.
func (n *node) maxNode() *node {
	for count := n.kidCount(); count > 0; count = n.kidCount() {
		n = n.kid(count - 1)
	}
	if !n.hasValue() {
		return nil // only an empty root
	}
	return n
}
