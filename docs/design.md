# Design

[Project overview and examples](../README.md)

go-juuri is a persistent, path-compressed radix tree. Writes copy the changed
path and share untouched subtrees with earlier versions. Its shape also defines
its watch semantics: a prefix watch observes the node whose subtree covers
that prefix. The [differential tests](../radixdiff/radixdiff_test.go) compare read
results and watch notifications with go-immutable-radix for the same history.

The engine originated in go-maemmidb, but transactions, snapshots, and
notifications are controlled directly by the caller of this library.

The root package is the API and nothing else: it wraps the tree, transactions,
iterators, and watch handles that [`internal/radix`](../internal/radix/)
implements, whose watch channels in turn come from
[`internal/watch`](../internal/watch/). Everything described below is internal,
and the split keeps that clear at a glance.

## Nodes

The default node header has the following layout on 64-bit systems. This is an
internal type sketch; the complete declaration is in
[`node_unsafe.go`](../internal/radix/node_unsafe.go).

```go
type node struct {
	prefix string    // Compressed path segment, including the label byte.
	val    any       // Value of the key ending here; valid when epoch says so.
	bitmap [4]uint64 // One bit per child label; inline segment in compact leaves.
	nkids  uint16    // Child count; inline segment tail in compact leaves.
	ckids  uint16    // Child capacity; zero when there is no child array.
	_      [4]byte
	leaf   *leaf  // Identity of this version of the value, created lazily.
	watch  slot   // Lazily created watch channel.
	epoch  uint64 // Ownership stamp, plus the value and leaf-ownership bits.
}

type leaf struct{ watch slot }
```

### Children

A 256-bit bitmap records which byte labels have children. The child for a label
is at `popcount(bitmap below label)` in a dense array. Lookup needs no linear
search, iteration follows the array in label order, and lower-bound seeks find
the next label with bit operations.

Size classes from `node4` to `node256` embed the child array immediately after
the header. Copying a node and its child storage takes one allocation, with
eight bytes per child slot on 64-bit systems. The default layout uses a 16-bit
count and capacity instead of a slice header, saving 16 bytes per header. The
path string, value, and bitmap occupy its first 64 bytes.

The smallest class with children has a 96-byte header and four child slots,
for 128 bytes. Omitting a two-child class avoids 112-byte allocations, whose
first 64 bytes can straddle cache lines.

### Path segments

Segments are immutable strings. One-byte segments can use a static table, and
lookup need not compare their byte again because the bitmap already matched it.
Heap-backed segments can share substrings when split.

Childless nodes keep short segments inside their own allocation, avoiding a
separate string allocation and keeping the final comparison near the value:

| Segment length | Storage in the default build |
| --- | --- |
| 1–34 bytes | The bitmap and child-count bytes in a compact leaf |
| 35–48 bytes | A 48-byte array after the header |
| 49–64 bytes | A 64-byte array after the header |
| More than 64 bytes | A separate heap string |

A compact leaf needs neither a bitmap nor a child count. Its `prefix` points
into those 34 bytes, and its child capacity stays zero. Accessors check the
prefix address or capacity before interpreting the storage as child metadata.
The node itself occupies only the 96-byte header.

An inline segment must never be shared with another node: a copy, split, or
merge copies the bytes when necessary. This prevents a substring from retaining
a dead node. Splitting an owned compact leaf moves the remaining segment to the
start of its storage so the leaf stays recognisable.

### Values and watches

A node holds the value, while a separate `leaf` holds the watch slot for that
version of the key. Copies of a node share the leaf until the value changes.
This preserves watches through splits and merges, including watches obtained
later through an older tree. Ordinary reads and iteration do not need to
dereference the leaf; a bit in `epoch` records whether the node holds a value.

The leaf is created only when something needs it: a watcher of the key, or a
copy of the node that keeps the value and so must share its identity. Until
then the value's identity is the one node that holds it, and most values,
never watched and never copied, need no leaf at all. A value that leaves a
committed tree without one gets a shared, already sealed leaf on notification,
so that a watcher arriving later through an older tree is still notified. The
leaf pointer is atomic because readers may create it on a published node.

The tree stores path segments rather than retaining the caller's key slices.
Iterators return values only. Values are not deep-copied, so a mutable value
remains shared across snapshots. There is no size counter; `Tree.Len()` walks
the tree in O(n).

### Safe build

The default build confines `unsafe` to
[`node_unsafe.go`](../internal/radix/node_unsafe.go) and
[`segment_unsafe.go`](../internal/radix/segment_unsafe.go). The `juuri_safe`,
`memdb_safe`, and `purego` tags select
[`node_safe.go`](../internal/radix/node_safe.go) and
[`segment_safe.go`](../internal/radix/segment_safe.go), which use ordinary
slices and strings. The transaction, lookup, iteration, and watch logic is
shared between builds.

## Ownership and snapshots

Every node carries the epoch of the transaction that created it; epochs come
from one process-wide atomic counter (trees of a database and of its snapshots
share nodes and have independent writers, so an epoch must never be issued
twice). A write transaction may mutate a node in place only when its ownership
epoch matches the transaction's, after masking out the value and
leaf-ownership bits; any other node is copied first.

`Txn.Freeze()` makes everything written so far immutable in O(1): the
transaction forgets its epoch and draws a new one on its next write.
`Txn.Commit()` also freezes and returns the resulting tree. Earlier committed
trees remain valid snapshots.

`Txn.Tree()` returns the current state without freezing. The caller must call
`Freeze()` before retaining that state across another write, creating an
iterator or watch over uncommitted writes, or sharing the tree with another
goroutine. Plain reads such as `Get` and `LongestPrefix` can use `Txn.Tree()`
without freezing when no tree state escapes.

Committed trees can be read concurrently. Callers must synchronise publication
of a new tree, and must not use a transaction or notifier concurrently or copy
a transaction after use.

## Lazy watch channels

A watch slot is an atomic pointer. It moves from `nil` to a channel and then to
a sealed state, or directly from `nil` to sealed if nobody watched it.

- A **reader** materialises a channel with `CompareAndSwap(nil, ch)`.
- A **writer** with a non-nil `Notifier` records the nodes and values it
  replaces. After committing and publishing the new tree, the caller runs
  `Notify()` to seal their slots and close any existing channels. The sealed
  state holds a permanently closed channel.

For a replaced object, either the reader installs a channel first and the
writer closes it, or sealing happens first and the reader receives the closed
channel. This also notifies readers that arrive through an older tree after
publication. Freezing before exposing uncommitted state ensures that a node
with a materialised watch slot is never mutated in place.

The watch rules preserve go-immutable-radix's notification granularity:

- A hit watches that version of the key's value. A miss watches the deepest
  node reached, including a child whose prefix diverges from the key. Such a
  watch can fire for nearby changes as well as insertion of the missing key.
- A prefix watch covers the deepest node reached by the prefix search. The
  subtree can cover more keys than the requested prefix when that prefix is
  absent or diverges within a segment.
- A failed key delete copies and notifies nothing. Splits and merges record
  replaced nodes without replacing the leaves of unchanged keys.
- The root is never merged, and every new tree starts with its own root.
- `DeletePrefix` records the removed subtree's root and walks that subtree
  during `Notify()`, so an aborted transaction avoids the walk.
- A bit in `epoch` marks a value stored in the current ownership epoch.
  Nobody can have watched it, so repeated updates within that epoch need no
  tracking, which keeps tracking bounded.

Passing `nil` to `Tree.Txn` disables notification tracking. To abort tracked
writes, discard the transaction and call `Notifier.Reset()` before reusing the
notifier. One notifier may collect several transactions that commit together;
resetting it discards all pending notifications. `Notify()` resets it after
closing channels.

The [model tests](../internal/radix/model_test.go) check that a tracked commit
followed by notification seals exactly the nodes and leaves reachable from the
old root that are no longer reachable from the new root.

## Compatibility

The differential suite compares against go-immutable-radix v1.3.1. It allows
one known difference: if `DeletePrefix` removes a subtree whose root was already
modified in the same transaction, upstream can miss notifications for watches
inside that subtree. go-juuri notifies those watchers. The test records this
exception explicitly; other observed differences fail the comparison.
