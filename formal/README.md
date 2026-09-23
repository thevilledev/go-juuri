# Formal verification

[Project overview](../README.md) · [Design](../docs/design.md)

This directory holds machine-checked models of the radix tree in
[`internal/radix`](../internal/radix/) and its watch channels in
[`internal/watch`](../internal/watch/):

- [`lean/`](lean/): Lean 4 proofs of the functional core. Every read and
  write operation is transcribed from the Go code and proved against a
  map-and-order specification, for all trees and all keys.
- [`tla/`](tla/): TLA+ models of what Lean does not cover: ownership epochs,
  copy-on-write against in-place mutation, the Notifier, and the lock-free
  protocol behind lazy watch channels. TLC checks them exhaustively within
  bounded scopes.
- [`conformance/`](conformance/): a test that runs the Lean model as an
  executable next to the Go library on random scripts and requires identical
  answers. This ties the proofs to the code that ships.

The checks found no defect in the implementation within the scope described
below. [Observations](#observations) lists behaviour that is correct by
design but easy to misread.

## What is proved in Lean

`lake build` checks every proof and prints the axioms each headline result
depends on. They are at most Lean's standard three (`propext`,
`Classical.choice`, `Quot.sound`): no `sorry`, no `native_decide`, no added
axioms. [`Statements.lean`](lean/JuuriFormal/Statements.lean) restates every
headline theorem in full, so a proof file cannot quietly weaken one.

| Go code | Lean | Result |
| --- | --- | --- |
| `node.rank` | [`Rank.lean`](lean/JuuriFormal/Rank.lean) | `goRank_correct`: the branch-free bit trick, transcribed with Go's shift semantics, returns the number of labels below the label and whether it is present, for every bitmap and label |
| `addKid`, `delKid` | `Rank.lean` | `addKid_consistent`, `delKid_consistent`: the bitmap and the ascending child array stay in agreement |
| `rank` against the model | [`Bridge.lean`](lean/JuuriFormal/Bridge.lean) | `rankOf_eq_goRank`: on a consistent node, `rank` finds the child the model's child list does |
| `node.hasPrefix` | [`Lookup.lean`](lean/JuuriFormal/Lookup.lean) | `lookup_goHasPrefix_eq`: the one- and two-byte fast paths agree with a plain prefix test on a child found by its label |
| tree shape | [`Order.lean`](lean/JuuriFormal/Order.lean) | `entries_sorted`: a well-formed tree lists its entries in strictly ascending key order |
| `Tree.Get` | `Lookup.lean` | `get_correct`: `Get` is lookup in the tree's entries |
| `Tree.LongestPrefix` | `Lookup.lean` | `longestPrefix_correct`: the value of the longest stored key that is a prefix of the search key |
| `Tree.FirstPrefix`, `LastPrefix` | `Lookup.lean` | `firstPrefix_correct`, `lastPrefix_correct`: the smallest and greatest key with the prefix |
| `Txn.Insert` | [`Insert.lean`](lean/JuuriFormal/Insert.lean) | `insert_wf`, `insert_lookup`, `insert_old`: the result is well formed, maps the key to the new value and everything else as before, and the returned value is the old one |
| `Txn.Delete` | [`Delete.lean`](lean/JuuriFormal/Delete.lean) | `delete_miss`, `delete_hit`: a miss changes nothing; a hit returns the value, and the result is well formed and holds exactly the other entries, in order |
| `Txn.DeletePrefix` | `Delete.lean` | `deletePrefix_miss`, `deletePrefix_hit`: the result holds exactly the entries without the prefix; it reports a match iff a key has the prefix, or the prefix is empty |
| `Iterator` (`SeekLowerBound`, `SeekPrefixWatch`, `Next`) | [`Iter.lean`](lean/JuuriFormal/Iter.lean) | `iter_lowerBound`, `iter_prefix`: exactly the values of the keys at or above the bound, or with the prefix, in ascending order. The iterator terminates within `4·size+4` steps and never reads a child count of a childless node |
| `ReverseIterator` (`SeekReverseLowerBound`, `SeekPrefixWatch`, `Previous`) | [`IterRev.lean`](lean/JuuriFormal/IterRev.lean) | `iter_reverseLowerBound`, `iter_prefix_rev`: the same in descending order, never indexing a child out of range |
| the iterators' `stack` | [`Stack.lean`](lean/JuuriFormal/Stack.lean) | `toList_push`, `toList_top`, `toList_setTop`, `toList_pop`: eight inline frames plus a spill slice behave as a list |

[`Tree.lean`](lean/JuuriFormal/Tree.lean) is the model, with one definition
per Go function, named after it. The theorems are about the model, so the
model must be the code. The [conformance test](#conformance) checks this:
across 300 random scripts of 200 commands each, the model and the Go library
answer every write, lookup and iteration identically, in both the default
and the `juuri_safe` build.

Modelling choices:

- Bytes are natural numbers; the code only ever compares them.
- A node's children are a list in label order. The Go node finds a child
  through its bitmap and `rank`; `Rank.lean` and `Bridge.lean` prove that
  equivalent.
- The compact-leaf layout (segments stored inside the node, `unsafe`) is not
  modelled. The conformance test exercises it, with keys long enough to reach
  every storage class.
- Ownership and watches do not affect what a tree holds, only which objects
  hold it. They are left to the TLA+ models.

## What is model-checked in TLA+

The models transcribe the Go code operation by operation. Run them with TLC
(`tla2tools.jar`, Java 11 or later); `make formal-tla` runs the exhaustive
configurations.

### LazyWatch: the lock-free watch protocol

[`LazyWatch.tla`](tla/LazyWatch.tla) models one key's value through a
series of transactions, with every Go atomic operation as a separate step:
`valueChan` (a reader creating the value's leaf), `leafOf` (a writer copying
a published node), `sealValue` (Notify giving a leafless value the shared
sealed leaf), and `Slot.Chan`, `Slot.Live` and `Slot.Seal` (the swap and the
close as two steps). The tracked writer copies, updates, deletes, inserts and
freezes, then commits and notifies, or aborts. Transactions may start from an
older tree (a rollback that keeps notifying). An untracked writer forks from
any published tree. Readers take key watches on any reachable node and race
all of them.

| Property | Meaning |
| --- | --- |
| `NoDoubleClose` | No channel is closed twice (a panic in Go), including when a leaf is sealed again after a rollback |
| `DropLeafNonNil` | Notify never dereferences a nil leaf |
| `VisibleNotOwned` | A node anyone can reach is never owned by the transaction in progress, so it is never mutated |
| `LeafShared` | Every reachable copy of a value shares one leaf, whoever created it |
| `NoLostWakeup` | Once a value's retirement is notified, every channel handed out for it is closed, including one asked for later through an old tree |
| `RetiredSealed` | Every reachable node holding a retired value leads to a sealed leaf |
| `NoSpuriousWakeup` | A key watch fires only for a value retired by a committed, tracked transaction; aborts and untracked forks never fire one |
| `ReadersGetChannel` (liveness) | `valueChan` is wait-free: every reader gets a channel |
| `NotifiedWakes` (liveness) | A reader waiting on a notified value wakes |

| Configuration | Scope | Result |
| --- | --- | --- |
| `LazyWatch.cfg` | one reader, two tracked transactions of up to two operations each, rollback, an untracked fork | exhaustive: 17,439,719 distinct states; all nine properties hold |
| `LazyWatchSafety.cfg` | the same with two readers | simulation (`-simulate -depth 100`): 208 million states, no violation of the seven safety properties |

### JuuriTxn: ownership, copy-on-write and notification

[`JuuriTxn.tla`](tla/JuuriTxn.tla) models the heap: nodes with segment,
value, children, capacity, leaf, epoch and `leafOwnedBit`. It transcribes
`own`, `copyNode`, `copyShape`, `shareLeaf`, `releaseValue`, `ownValueless`,
`setValue`, the `Insert` loop and split, `ownPath`, `unlink`, `mergeChild`,
`Delete`, `DeletePrefix`, `Notify` (including the `sealSubtree` walk),
`Freeze`, `Commit` and `Reset`. Each operation is one step, because a
transaction belongs to one goroutine. The model covers tracked transactions,
untracked forks from any published tree, and readers asking for key-watch
channels.

| Property | Meaning |
| --- | --- |
| `NoMutation`, `Persistence` | No node of a committed or frozen tree is ever mutated (only its leaf created, once), and every published tree keeps its content |
| `OwnedUnpublished` | Nothing the transaction owns was ever published |
| `TxnContent` | Every operation, with its in-place mutations, yields the content the map semantics prescribes |
| `Shape` | `checkShape` holds for every tree |
| `LeafOnCopies`, `NotifyNoNil` | An owned copy of a published value carries the leaf that `dropLeaf` records |
| `RecordsPublished`, `NoDuplicateRecords` | The Notifier records only published objects, each at most once, so its lists stay bounded |
| `LiveNotSealed` | Nothing in the latest committed tree is sealed |
| `LeftSealed` | Everything that left the lineage is sealed; a value that left without a leaf got the sealed leaf (`checkSeals` in the Go tests) |
| `SealedFromLineage` | Aborted and untracked transactions seal nothing |
| `KeyWatch` | A key watch on any tree of the lineage fires iff the key's value changed since; splits and merges around the key do not fire it |
| `MissWatch` | A watch on a missing key fires once the key exists |
| `PrefixWatch` | A prefix watch fires when any key under the prefix changed |
| `NoSpuriousKeyWatch` | A key watch on any published tree, forks and aborted branches included, fires only if the lineage changed that key |

All three configurations use five keys over a two-letter alphabet, enough
for root values, keys with children, branch nodes, splits inside a two-byte
segment and merges, and start from three shapes (empty, a branch node, a
root value with nested keys):

| Configuration | Scope | Result |
| --- | --- | --- |
| `MCJuuriTxn.cfg` | two tracked transactions of up to two operations each (`Freeze` included), two watches | exhaustive: 4,085,504 distinct states, no violation |
| `MCJuuriTxnFork.cfg` | one tracked transaction of up to three operations, one untracked fork, two watches | exhaustive: 5,483,385 distinct states, no violation |
| `MCJuuriTxnDeep.cfg` | three tracked transactions of up to four operations each, two forks, three watches | simulation (`-simulate -depth 60`): 3.6 million states in 14 minutes, no violation |

Readers' leaf creation and forks act on published nodes only by creating
leaves, which is monotone and matters only before the tracked transaction
first touches a node. The model therefore runs them while that transaction
holds no epoch: between transactions, or after a `Freeze` and before the
next write.

### The models catch seeded bugs

A model that passes should also fail when the code is wrong. Each of these
changes was made to a copy of a model and checked in a configuration smaller
than those above; TLC rejected every one:

| Seeded bug | Caught by |
| --- | --- |
| `own` does not record the published node it copies | `LeftSealed` |
| a copy gets a fresh leaf instead of sharing the published one | `LeftSealed` |
| `setValue` updates in place whenever the node is owned, ignoring `leafOwnedBit` | `KeyWatch` |
| `releaseValue` forgets `dropLeaf` for a copied value | `LeftSealed` |
| a merged childless node always claims `leafOwnedBit` | `KeyWatch` |
| `Freeze` keeps the epoch | `OwnedUnpublished` |
| `unlink` merges the root | out-of-range path index (a panic) |
| `DeletePrefix` does not record the removed subtree | `LeftSealed` |
| `sealValue` stores the sealed leaf without a CAS | `LeafShared` |
| `valueChan` stores its leaf without a CAS | `LeafShared` |
| `leafOf` stores its leaf without a CAS | `LeafShared` |
| `Slot.Chan` stores its cell without a CAS | `NoLostWakeup` |
| `Slot.Seal` closes a slot that was already sealed | `NoDoubleClose` |
| a released published value is not recorded | `RetiredSealed` |

## Conformance

```sh
make formal-conformance
```

This builds the Lean model as an executable
([`lean/Conformance.lean`](lean/Conformance.lean)) and runs
[`conformance/`](conformance/), a nested module like `radixdiff`. Random
scripts over a four-byte alphabet go through both the model and the Go
library's public API. Writes are grouped into transactions of random length,
so nodes written earlier in a transaction are changed in place, and reads
see the transaction's own state. One key in eight is 30 to 75 bytes long, to
cover every segment storage class. The test skips itself if the executable
has not been built.

Seeded into the Go code, each of these bugs makes the test fail:

| Seeded bug | Where |
| --- | --- |
| `rank` counts the label's own bit | `node.go` |
| `hasPrefix` takes the two-byte fast path at the wrong length | `node.go` |
| `SeekLowerBound` resumes at the child it descended into | `iter.go` |
| `own` trusts one child slot too many | `txn.go` |
| the `setValue` fast path loses the old value | `txn.go` |
| `mergeChild` drops the parent's segment when it owns the child | `txn.go` |
| `trimPrefix` misplaces a compact leaf's segment | `segment_unsafe.go` |

## Running

Lean 4.34 (install with [elan](https://github.com/leanprover/elan); the
toolchain is pinned in `lean/lean-toolchain`) and no other dependency:

```sh
make formal-lean          # all proofs; prints the axioms of each result
make formal-conformance   # Lean model against the Go code
make formal-tla           # TLC on LazyWatch.cfg and the two exhaustive JuuriTxn configurations
```

`make formal-tla` expects `tla2tools.jar` at
`~/.local/share/tlaplus/tla2tools.jar` and `java` on the path; set
`TLA2TOOLS` and `JAVA` to use others. On a busy ten-core laptop the JuuriTxn
configurations take 15 to 20 minutes each, and `LazyWatch.cfg`, with its
liveness properties, just under an hour. `make formal` runs all three
targets. The simulation configurations run by hand, for example:

```sh
cd formal/tla
java -cp tla2tools.jar tlc2.TLC -simulate num=2000000 -depth 100 -config LazyWatchSafety.cfg LazyWatch.tla
java -cp tla2tools.jar tlc2.TLC -simulate num=20000 -depth 60 -config MCJuuriTxnDeep.cfg MCJuuriTxn.tla
```

## Observations

None of these is a defect. Each is behaviour that follows from the design,
checked by the models:

- **An empty prefix always matches.** `DeletePrefix` with an empty prefix
  replaces the root and returns `true`, even on an empty tree, and so fires
  a watch on the whole tree. go-immutable-radix does the same, and a test
  records it. For any other prefix, the result is `true` exactly when some
  key has the prefix (`deletePrefix_miss`).
- **Forks share leaves.** A transaction started on an older tree, such as a
  snapshot, copies nodes that share their value leaves with the lineage that
  retired them. A key watch taken through the fork therefore fires when the
  primary lineage changes the key, not the fork. go-immutable-radix shares
  its leaf objects the same way. `NoSpuriousKeyWatch` checks that nothing
  else fires. Rollbacks that keep notifying may seal a leaf twice; `Seal`
  tolerates that (`NoDoubleClose`).
- **An aborted Freeze stays silent.** A watch taken on a frozen tree whose
  transaction is aborted never fires for the aborted changes. Only objects
  it shares with the committed lineage can fire it.
- **One extra pop step.** `SeekLowerBound` pushes a frame one past a found
  child even when that child is the last. `Next` pops it one step later,
  harmlessly; the fuel bound in `iter_lowerBound` accounts for it.

## Limits

- TLC checks bounded scopes: small key sets and short transaction
  sequences. The bugs such models catch typically show up within a few
  operations, but the check is not a proof for every tree.
- JuuriTxn makes each Insert, Delete and DeletePrefix one atomic step and
  lets readers create a leaf in one step. The interleavings inside those
  operations that matter, the atomic races on leaves and watch slots, are
  what LazyWatch models step by step.
- Not modelled: the memory layout and its `unsafe` accessors (the tests,
  the race detector and the conformance test cover them), garbage retention,
  32-bit specifics, and compatibility with go-immutable-radix (see
  [`radixdiff`](../radixdiff/)).
- The Lean model and the TLA+ models are separate transcriptions of the same
  code, each reviewed against it. The conformance test checks the Lean model
  mechanically; the TLA+ models are checked by the seeded bugs above and by
  `TxnContent`, which compares each transaction with the map semantics.
