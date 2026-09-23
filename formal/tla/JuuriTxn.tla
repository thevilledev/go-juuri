----------------------------- MODULE JuuriTxn -----------------------------
(***************************************************************************)
(* The transaction layer of internal/radix (txn.go) at the level of the   *)
(* heap: ownership epochs, copy-on-write versus in-place mutation, the    *)
(* lazily created value leaves, the Notifier, Freeze, Commit and abort.   *)
(*                                                                         *)
(* Each Go function is transcribed as an operator from a writer state S   *)
(* (the heap and the transaction) to a new S; a whole Insert, Delete or   *)
(* DeletePrefix is one step, as the transaction is used by one goroutine. *)
(* The lock-free races between readers, writers and Notify are the       *)
(* subject of LazyWatch.tla; here a reader's watch materialises a leaf    *)
(* atomically.                                                            *)
(*                                                                         *)
(* Nodes: seg (the path segment, a sequence of bytes), val (NoVal or a    *)
(* value id: every write stores a fresh id), kids (ids in label order),  *)
(* cap (0 for a node without a child array, else room to spare -- the    *)
(* model's alphabet is small), leaf (NIL or a leaf id), epoch and lob     *)
(* (leafOwnedBit). The child bitmap is the kids sequence (Rank.lean      *)
(* proves the two agree).                                                 *)
(*                                                                         *)
(* Checked: published trees never change (no node reachable from a       *)
(* committed or frozen tree is mutated); every transaction yields the    *)
(* right content; and after each tracked commit and Notify, the watch     *)
(* channels in the state they would be in are exactly right: a key watch *)
(* fires iff the key's value changed, a miss watch fires when the key is *)
(* created, a prefix watch fires when anything under it changed, nothing  *)
(* live is sealed and everything that left is.                            *)
(***************************************************************************)
EXTENDS Naturals, Sequences, FiniteSets, TLC

CONSTANTS
    Keys,          \* keys the operations use (sequences of byte values)
    Probes,        \* keys and prefixes whose watches are checked
    InitContents,  \* possible initial contents: sets of keys
    MaxTxns,       \* tracked transactions
    MaxOps,        \* operations per transaction
    Forks,         \* untracked single-operation transactions on old trees
    MaxWatches,    \* key watches whose channel a reader asks for
    NIL, NoVal

VARIABLES
    heap,        \* node id -> node
    nodeCtr,     \* last node id allocated
    leafCtr,     \* last leaf id allocated (leaf 0 is sealedLeaf)
    valCtr,      \* last value id stored
    epochCtr,    \* the global epoch counter
    sealedN,     \* node ids whose watch slot is sealed
    sealedL,     \* leaf ids whose watch slot is sealed
    committed,   \* root of the latest committed tree of the tracked lineage
    tx,          \* the tracked transaction: [on, root, epoch, nf, ops, expected, frozen]
    hist,        \* published trees: [root, content, status]
    pub,         \* node id -> immutable fields, for every node ever published
    txns,        \* tracked transactions started
    forks,       \* untracked transactions run
    watches      \* key watch channels asked for

vars == <<heap, nodeCtr, leafCtr, valCtr, epochCtr, sealedN, sealedL, committed, tx, hist, pub, txns, forks, watches>>

SealedLeaf == 0
EmptyNf == [nodes |-> <<>>, leaves |-> <<>>, values |-> <<>>, subtrees |-> <<>>]

(***************************************************************************)
(* Sequences                                                              *)
(***************************************************************************)
Drop(s, k) == SubSeq(s, k + 1, Len(s))
IsPrefix(p, s) == Len(p) <= Len(s) /\ SubSeq(s, 1, Len(p)) = p
InsertAt(s, i, x) == SubSeq(s, 1, i - 1) \o <<x>> \o SubSeq(s, i, Len(s))
RemoveAt(s, i) == SubSeq(s, 1, i - 1) \o SubSeq(s, i + 1, Len(s))
RECURSIVE LcpRec(_, _, _)
LcpRec(a, b, i) == IF i <= Len(a) /\ i <= Len(b) /\ a[i] = b[i] THEN LcpRec(a, b, i + 1) ELSE i - 1
Lcp(a, b) == LcpRec(a, b, 1)

(***************************************************************************)
(* The writer state S = [heap, nodeCtr, leafCtr, root, epoch, tracked, nf] *)
(***************************************************************************)
Kids(S, n) == S.heap[n].kids
Label(S, n) == Head(S.heap[n].seg)
HasValue(S, n) == S.heap[n].val /= NoVal
Owns(S, n) == S.heap[n].epoch = S.epoch

\* rank: the 0-based index of the first child with a label >= b, and whether
\* a child has label b.
Rank(S, n, b) ==
    [idx |-> Cardinality({i \in 1..Len(Kids(S, n)) : Label(S, Kids(S, n)[i]) < b}),
     ok  |-> \E i \in 1..Len(Kids(S, n)) : Label(S, Kids(S, n)[i]) = b]
Kid(S, n, idx) == Kids(S, n)[idx + 1]

Alloc(S, rec) ==
    [s |-> [S EXCEPT !.heap = (S.nodeCtr + 1 :> rec) @@ S.heap, !.nodeCtr = @ + 1],
     id |-> S.nodeCtr + 1]

Node(seg, val, kids, cap, leaf, epoch, lob) ==
    [seg |-> seg, val |-> val, kids |-> kids, cap |-> cap, leaf |-> leaf, epoch |-> epoch, lob |-> lob]

\* newNode(capacity): no child array for 0, else a size class (>= 4).
Cap(capacity) == IF capacity <= 0 THEN 0 ELSE 4

\* Txn.begin
Begin(S) == IF S.epoch = 0 THEN [S EXCEPT !.epoch = S.nextEpoch, !.nextEpoch = @ + 1] ELSE S

DropNode(S, n)    == IF S.tracked THEN [S EXCEPT !.nf.nodes = Append(@, n)] ELSE S
DropLeaf(S, l)    == IF S.tracked THEN [S EXCEPT !.nf.leaves = Append(@, l)] ELSE S
DropValue(S, n)   == IF S.tracked THEN [S EXCEPT !.nf.values = Append(@, n)] ELSE S
DropSubtree(S, n) == IF S.tracked THEN [S EXCEPT !.nf.subtrees = Append(@, n)] ELSE S

\* node.leafOf: the published node's leaf, created if nobody needed it yet.
LeafOf(S, n) ==
    IF S.heap[n].leaf /= NIL THEN [s |-> S, l |-> S.heap[n].leaf]
    ELSE [s |-> [S EXCEPT !.heap[n].leaf = S.leafCtr + 1, !.leafCtr = @ + 1], l |-> S.leafCtr + 1]

\* Txn.shareLeaf
ShareLeaf(S, n) == IF Owns(S, n) THEN [s |-> S, l |-> S.heap[n].leaf] ELSE LeafOf(S, n)

\* Txn.copyShape
CopyShape(S, n, extra) ==
    Alloc(S, Node(S.heap[n].seg, NoVal, Kids(S, n), Cap(Len(Kids(S, n)) + extra), NIL, S.epoch, FALSE))

\* Txn.copyNode
CopyNode(S, n, extra) ==
    LET a == CopyShape(S, n, extra) IN
    IF ~HasValue(S, n) THEN a
    ELSE LET sl == ShareLeaf(a.s, n) IN
         [s |-> [sl.s EXCEPT !.heap[a.id].val = S.heap[n].val, !.heap[a.id].leaf = sl.l], id |-> a.id]

\* Txn.leafNode
LeafNode(S, seg, v) == Alloc(S, Node(seg, v, <<>>, 0, NIL, S.epoch, TRUE))

\* Txn.link
Link(S, parent, pidx, c) ==
    IF parent = 0 THEN [S EXCEPT !.root = c] ELSE [S EXCEPT !.heap[parent].kids[pidx + 1] = c]

\* Txn.own
Own(S, parent, pidx, n, extra) ==
    IF Owns(S, n)
    THEN IF Len(Kids(S, n)) + extra <= S.heap[n].cap THEN [s |-> S, id |-> n]
         ELSE LET c == CopyNode(S, n, Len(Kids(S, n)) + extra)
                  s1 == [c.s EXCEPT !.heap[c.id].epoch = S.heap[n].epoch, !.heap[c.id].lob = S.heap[n].lob]
              IN [s |-> Link(s1, parent, pidx, c.id), id |-> c.id]
    ELSE LET c == CopyNode(S, n, extra) IN
         [s |-> Link(DropNode(c.s, n), parent, pidx, c.id), id |-> c.id]

\* Txn.releaseValue
ReleaseValue(S, n) ==
    IF ~Owns(S, n) THEN DropValue(S, n)
    ELSE IF ~S.heap[n].lob THEN DropLeaf(S, S.heap[n].leaf)
    ELSE S

\* Txn.ownValueless
OwnValueless(S, parent, pidx, n) ==
    LET S1 == IF HasValue(S, n) THEN ReleaseValue(S, n) ELSE S IN
    IF Owns(S1, n)
    THEN [s |-> [S1 EXCEPT !.heap[n].leaf = NIL, !.heap[n].val = NoVal, !.heap[n].lob = FALSE], id |-> n]
    ELSE LET c == CopyShape(S1, n, 0) IN
         [s |-> Link(DropNode(c.s, n), parent, pidx, c.id), id |-> c.id]

\* Txn.setValue
SetValue(S, parent, pidx, n, v) ==
    IF HasValue(S, n) /\ Owns(S, n) /\ S.heap[n].lob
    THEN [S EXCEPT !.heap[n].val = v]
    ELSE LET o == OwnValueless(S, parent, pidx, n) IN
         [o.s EXCEPT !.heap[o.id].val = v, !.heap[o.id].lob = TRUE]

\* node.addKid
AddKid(S, n, idx, c) == [S EXCEPT !.heap[n].kids = InsertAt(@, idx + 1, c)]
\* node.delKid
DelKid(S, n, idx) == [S EXCEPT !.heap[n].kids = RemoveAt(@, idx + 1)]

\* The split in Txn.Insert: the key diverges inside child's segment.
Split(S, n, idx, child, search, common, v) ==
    LET t0 == IF ~Owns(S, child)
              THEN LET c == CopyNode(S, child, 0) IN [s |-> DropNode(c.s, child), id |-> c.id]
              ELSE [s |-> S, id |-> child]
        cseg == S.heap[child].seg
        sp == Alloc(t0.s, Node(SubSeq(cseg, 1, common), NoVal, <<>>, Cap(2), NIL, S.epoch, FALSE))
        s1 == [sp.s EXCEPT !.heap[t0.id].seg = Drop(cseg, common), !.heap[n].kids[idx + 1] = sp.id]
        rest == Drop(search, common)
    IN IF rest = <<>>
       THEN [s1 EXCEPT !.heap[sp.id].val = v, !.heap[sp.id].lob = TRUE, !.heap[sp.id].kids = <<t0.id>>]
       ELSE LET a == LeafNode(s1, rest, v)
                ks == IF Head(rest) < Head(Drop(cseg, common)) THEN <<a.id, t0.id>> ELSE <<t0.id, a.id>>
            IN [a.s EXCEPT !.heap[sp.id].kids = ks]

\* The loop of Txn.Insert.
RECURSIVE InsertLoop(_, _, _, _, _, _)
InsertLoop(S, parent, pidx, n, search, v) ==
    IF search = <<>> THEN SetValue(S, parent, pidx, n, v)
    ELSE LET r == Rank(S, n, Head(search)) IN
         IF ~r.ok
         THEN LET o == Own(S, parent, pidx, n, 1)
                  lf == LeafNode(o.s, search, v)
              IN AddKid(lf.s, o.id, r.idx, lf.id)
         ELSE LET child == Kid(S, n, r.idx)
                  common == Lcp(search, S.heap[child].seg)
                  o == Own(S, parent, pidx, n, 0)
              IN IF common = Len(S.heap[child].seg)
                 THEN InsertLoop(o.s, o.id, r.idx, child, Drop(search, common), v)
                 ELSE Split(o.s, o.id, r.idx, child, search, common, v)

Insert(S, k, v) == LET S0 == Begin(S) IN InsertLoop(S0, 0, 0, S0.root, k, v)

\* Txn.ownPath
RECURSIVE OwnPathRec(_, _, _, _, _)
OwnPathRec(S, path, i, parent, pidx) ==
    IF i > Len(path) THEN [s |-> S, path |-> path]
    ELSE LET o == Own(S, parent, pidx, path[i].n, 0) IN
         OwnPathRec(o.s, [path EXCEPT ![i].n = o.id], i + 1, o.id, path[i].idx)
OwnPath(S, path) == OwnPathRec(S, path, 1, 0, 0)

\* Txn.mergeChild
MergeChild(S, parent, pidx, n, c) ==
    LET joined == S.heap[n].seg \o S.heap[c].seg
        m == IF Kids(S, c) = <<>>
             THEN LET a == Alloc(S, Node(joined, S.heap[c].val, <<>>, 0, NIL, S.epoch, FALSE))
                      sl == ShareLeaf(a.s, c)
                  IN [s |-> [sl.s EXCEPT !.heap[a.id].leaf = sl.l,
                                         !.heap[a.id].lob = Owns(S, c) /\ S.heap[c].lob],
                      id |-> a.id]
             ELSE IF Owns(S, c) THEN [s |-> [S EXCEPT !.heap[c].seg = joined], id |-> c]
             ELSE LET cp == CopyNode(S, c, 0) IN
                  [s |-> [cp.s EXCEPT !.heap[cp.id].seg = joined], id |-> cp.id]
        s2 == IF ~Owns(S, c) THEN DropNode(m.s, c) ELSE m.s
    IN [s2 EXCEPT !.heap[parent].kids[pidx + 1] = m.id]

\* Txn.unlink
Unlink(S, path) ==
    LET last == Len(path) parent == path[last].n idx == path[last].idx IN
    IF last > 1 /\ ~HasValue(S, parent) /\ Len(Kids(S, parent)) = 2
    THEN LET op == OwnPath(S, SubSeq(path, 1, last - 1))
             s1 == IF ~Owns(op.s, parent) THEN DropNode(op.s, parent) ELSE op.s
         IN MergeChild(s1, op.path[last - 1].n, op.path[last - 1].idx, parent, Kid(s1, parent, 1 - idx))
    ELSE LET op == OwnPath(S, path) IN DelKid(op.s, op.path[last].n, idx)

\* Txn.dropWithLeaf
DropWithLeaf(S, n) == LET s1 == ReleaseValue(S, n) IN IF ~Owns(S, n) THEN DropNode(s1, n) ELSE s1

\* The read-only descent of Txn.Delete.
RECURSIVE Descend(_, _, _, _)
Descend(S, n, search, path) ==
    IF search = <<>> THEN [found |-> HasValue(S, n), path |-> path, n |-> n]
    ELSE LET r == Rank(S, n, Head(search)) IN
         IF ~r.ok THEN [found |-> FALSE, path |-> path, n |-> n]
         ELSE LET c == Kid(S, n, r.idx) IN
              IF ~IsPrefix(S.heap[c].seg, search) THEN [found |-> FALSE, path |-> path, n |-> n]
              ELSE Descend(S, c, Drop(search, Len(S.heap[c].seg)), Append(path, [n |-> n, idx |-> r.idx]))

\* Txn.Delete
Delete(S, k) ==
    LET d == Descend(S, S.root, k, <<>>) IN
    IF ~d.found THEN S
    ELSE LET S0 == Begin(S) n == d.n path == d.path IN
         IF path = <<>> THEN OwnValueless(S0, 0, 0, n).s
         ELSE IF Kids(S0, n) = <<>> THEN Unlink(DropWithLeaf(S0, n), path)
         ELSE IF Len(Kids(S0, n)) = 1
              THEN LET op == OwnPath(S0, path)
                       s1 == DropWithLeaf(op.s, n)
                   IN MergeChild(s1, op.path[Len(path)].n, op.path[Len(path)].idx, n, Kids(s1, n)[1])
              ELSE LET op == OwnPath(S0, path) IN
                   OwnValueless(op.s, op.path[Len(path)].n, op.path[Len(path)].idx, n).s

\* The descent of Txn.DeletePrefix.
RECURSIVE DescendP(_, _, _, _)
DescendP(S, n, search, path) ==
    IF search = <<>> THEN [found |-> TRUE, path |-> path, n |-> n]
    ELSE LET r == Rank(S, n, Head(search)) IN
         IF ~r.ok THEN [found |-> FALSE, path |-> path, n |-> n]
         ELSE LET c == Kid(S, n, r.idx) cs == S.heap[c].seg p2 == Append(path, [n |-> n, idx |-> r.idx]) IN
              IF IsPrefix(cs, search) THEN DescendP(S, c, Drop(search, Len(cs)), p2)
              ELSE IF Len(search) < Len(cs) /\ IsPrefix(search, cs) THEN DescendP(S, c, <<>>, p2)
              ELSE [found |-> FALSE, path |-> path, n |-> n]

\* Txn.DeletePrefix
DeletePrefix(S, p) ==
    LET d == DescendP(S, S.root, p, <<>>) IN
    IF ~d.found THEN S
    ELSE LET S0 == DropSubtree(Begin(S), d.n) IN
         IF d.path = <<>>
         THEN LET a == Alloc(S0, Node(<<>>, NoVal, <<>>, 0, NIL, S0.epoch, FALSE)) IN
              [a.s EXCEPT !.root = a.id]
         ELSE Unlink(S0, d.path)

(***************************************************************************)
(* Notify                                                                 *)
(***************************************************************************)
\* sealValue: the value's leaf, or sealedLeaf if it never had one.
SealValue(h, sl, n) ==
    IF h[n].leaf = NIL THEN [h |-> [h EXCEPT ![n].leaf = SealedLeaf], sl |-> sl]
    ELSE [h |-> h, sl |-> sl \cup {h[n].leaf}]

RECURSIVE Subtree(_, _)
Subtree(h, n) == {n} \cup UNION {Subtree(h, h[n].kids[i]) : i \in 1..Len(h[n].kids)}

RECURSIVE SealValues(_, _, _)
SealValues(h, sl, ns) ==
    IF ns = {} THEN [h |-> h, sl |-> sl]
    ELSE LET n == CHOOSE x \in ns : TRUE
             r == IF h[n].val /= NoVal THEN SealValue(h, sl, n) ELSE [h |-> h, sl |-> sl]
         IN SealValues(r.h, r.sl, ns \ {n})

ValuesOf(sq) == {sq[i] : i \in 1..Len(sq)}

\* Notifier.Notify over the heap: nodes, leaves, values, subtrees.
Notify(h, sn, sl, nf) ==
    LET subNodes == UNION {Subtree(h, n) : n \in ValuesOf(nf.subtrees)}
        vals == ValuesOf(nf.values) \cup {n \in subNodes : h[n].val /= NoVal}
        r == SealValues(h, sl \cup ValuesOf(nf.leaves), vals)
    IN [h |-> r.h, sn |-> sn \cup ValuesOf(nf.nodes) \cup subNodes, sl |-> r.sl]

(***************************************************************************)
(* Reading a tree                                                         *)
(***************************************************************************)
RECURSIVE ContentRec(_, _, _)
ContentRec(h, n, path) ==
    LET p == path \o h[n].seg
        own == IF h[n].val /= NoVal THEN {<<p, h[n].val>>} ELSE {}
    IN own \cup UNION {ContentRec(h, h[n].kids[i], p) : i \in 1..Len(h[n].kids)}
\* The content of a tree as a function key -> value id.
Content(h, root) ==
    LET pairs == ContentRec(h, root, <<>>) IN
    [k \in {pr[1] : pr \in pairs} |-> (CHOOSE pr \in pairs : pr[1] = k)[2]]

Reach(h, root) == Subtree(h, root)

\* Tree.GetWatch: the node holding k (hit), or the deepest node reached (miss).
RECURSIVE Seek(_, _, _)
Seek(h, n, search) ==
    IF search = <<>> THEN [hit |-> h[n].val /= NoVal, n |-> n]
    ELSE LET ks == h[n].kids
             is == {i \in 1..Len(ks) : Head(h[ks[i]].seg) = Head(search)}
         IN IF is = {} THEN [hit |-> FALSE, n |-> n]
            ELSE LET c == ks[CHOOSE i \in is : TRUE] IN
                 IF ~IsPrefix(h[c].seg, search) THEN [hit |-> FALSE, n |-> c]
                 ELSE Seek(h, c, Drop(search, Len(h[c].seg)))

\* Tree.seekPrefix: the node whose watch covers a prefix.
RECURSIVE SeekPrefixWatch(_, _, _)
SeekPrefixWatch(h, n, search) ==
    IF search = <<>> THEN n
    ELSE LET ks == h[n].kids
             is == {i \in 1..Len(ks) : Head(h[ks[i]].seg) = Head(search)}
         IN IF is = {} THEN n
            ELSE LET c == ks[CHOOSE i \in is : TRUE] IN
                 IF IsPrefix(h[c].seg, search) THEN SeekPrefixWatch(h, c, Drop(search, Len(h[c].seg)))
                 ELSE c

\* The shape invariant (checkShape).
RECURSIVE ShapeOK(_, _, _)
ShapeOK(h, n, isRoot) ==
    /\ isRoot => h[n].seg = <<>>
    /\ ~isRoot => (h[n].seg /= <<>> /\ (h[n].val = NoVal => Len(h[n].kids) >= 2))
    /\ \A i \in 1..(Len(h[n].kids) - 1) : Head(h[h[n].kids[i]].seg) < Head(h[h[n].kids[i + 1]].seg)
    /\ h[n].val = NoVal => h[n].leaf = NIL
    /\ \A i \in 1..Len(h[n].kids) : ShapeOK(h, h[n].kids[i], FALSE)

Immutable(rec) == [seg |-> rec.seg, val |-> rec.val, kids |-> rec.kids, epoch |-> rec.epoch, lob |-> rec.lob]

\* Record every node of a newly published tree as published.
Publish(h, p, root) == [n \in DOMAIN p \cup Reach(h, root) |-> IF n \in DOMAIN p THEN p[n] ELSE Immutable(h[n])]

(***************************************************************************)
(* Actions                                                                *)
(***************************************************************************)
\* The initial tree: one of InitContents, built by an untracked transaction
\* and committed.
Init ==
    \E ks \in InitContents :
        LET RECURSIVE Build(_, _, _)
            Build(S, rest, v) ==
                IF rest = {} THEN [s |-> S, v |-> v]
                ELSE LET k == CHOOSE x \in rest : TRUE IN Build(Insert(S, k, v), rest \ {k}, v + 1)
            b == Build([heap |-> (1 :> Node(<<>>, NoVal, <<>>, 0, NIL, 0, FALSE)), nodeCtr |-> 1,
                        leafCtr |-> 0, root |-> 1, epoch |-> 0, nextEpoch |-> 1, tracked |-> FALSE,
                        nf |-> EmptyNf], ks, 1)
        IN /\ heap = b.s.heap
           /\ nodeCtr = b.s.nodeCtr
           /\ leafCtr = 0
           /\ valCtr = b.v - 1
           /\ epochCtr = b.s.nextEpoch - 1
           /\ sealedN = {}
           /\ sealedL = {SealedLeaf}
           /\ committed = b.s.root
           /\ tx = [on |-> FALSE, root |-> b.s.root, epoch |-> 0, nf |-> EmptyNf, ops |-> 0,
                    expected |-> Content(b.s.heap, b.s.root), frozen |-> <<>>]
           /\ hist = <<[root |-> b.s.root, content |-> Content(b.s.heap, b.s.root), status |-> "lineage"]>>
           /\ pub = Publish(b.s.heap, <<>>, b.s.root)
           /\ txns = 0
           /\ forks = 0
           /\ watches = 0

\* The writer state of the tracked transaction.
TxState == [heap |-> heap, nodeCtr |-> nodeCtr, leafCtr |-> leafCtr, root |-> tx.root,
            epoch |-> tx.epoch, nextEpoch |-> epochCtr + 1, tracked |-> TRUE, nf |-> tx.nf]

TxSet(S, op, expected) ==
    /\ heap' = S.heap /\ nodeCtr' = S.nodeCtr /\ leafCtr' = S.leafCtr
    /\ epochCtr' = S.nextEpoch - 1
    /\ tx' = [tx EXCEPT !.root = S.root, !.epoch = S.epoch, !.nf = S.nf, !.ops = @ + 1,
                        !.expected = expected]

StartTxn ==
    /\ ~tx.on /\ txns < MaxTxns
    /\ tx' = [on |-> TRUE, root |-> committed, epoch |-> 0, nf |-> EmptyNf, ops |-> 0,
              expected |-> Content(heap, committed), frozen |-> <<>>]
    /\ txns' = txns + 1
    /\ UNCHANGED <<heap, nodeCtr, leafCtr, valCtr, epochCtr, sealedN, sealedL, committed, hist, pub, forks, watches>>

\* Expected contents.
Upd(m, k, v) == [x \in DOMAIN m \cup {k} |-> IF x = k THEN v ELSE m[x]]
Del(m, k) == [x \in DOMAIN m \ {k} |-> m[x]]
DelP(m, p) == [x \in {y \in DOMAIN m : ~IsPrefix(p, y)} |-> m[x]]

DoInsert(k) ==
    /\ tx.on /\ tx.ops < MaxOps
    /\ valCtr' = valCtr + 1
    /\ TxSet(Insert(TxState, k, valCtr + 1), "insert", Upd(tx.expected, k, valCtr + 1))
    /\ UNCHANGED <<sealedN, sealedL, committed, hist, pub, txns, forks, watches>>

DoDelete(k) ==
    /\ tx.on /\ tx.ops < MaxOps
    /\ TxSet(Delete(TxState, k), "delete", Del(tx.expected, k))
    /\ UNCHANGED <<valCtr, sealedN, sealedL, committed, hist, pub, txns, forks, watches>>

DoDeletePrefix(p) ==
    /\ tx.on /\ tx.ops < MaxOps
    /\ TxSet(DeletePrefix(TxState, p), "deleteprefix", DelP(tx.expected, p))
    /\ UNCHANGED <<valCtr, sealedN, sealedL, committed, hist, pub, txns, forks, watches>>

\* Txn.Freeze, then the frozen tree is shared: it may be watched and read.
DoFreeze ==
    /\ tx.on /\ tx.ops < MaxOps
    /\ tx' = [tx EXCEPT !.epoch = 0, !.ops = @ + 1, !.frozen = Append(@, Len(hist) + 1)]
    /\ hist' = Append(hist, [root |-> tx.root, content |-> tx.expected, status |-> "pending"])
    /\ pub' = Publish(heap, pub, tx.root)
    /\ UNCHANGED <<heap, nodeCtr, leafCtr, valCtr, epochCtr, sealedN, sealedL, committed, txns, forks, watches>>

\* Txn.Commit, publish, Notifier.Notify.
DoCommit ==
    /\ tx.on
    /\ LET r == Notify(heap, sealedN, sealedL, tx.nf)
           fz == ValuesOf(tx.frozen)
       IN /\ heap' = r.h /\ sealedN' = r.sn /\ sealedL' = r.sl
          /\ hist' = Append([i \in DOMAIN hist |-> IF i \in fz THEN [hist[i] EXCEPT !.status = "lineage"] ELSE hist[i]],
                            [root |-> tx.root, content |-> tx.expected, status |-> "lineage"])
    /\ committed' = tx.root
    /\ pub' = Publish(heap, pub, tx.root)
    /\ tx' = [tx EXCEPT !.on = FALSE, !.epoch = 0, !.nf = EmptyNf]
    /\ UNCHANGED <<nodeCtr, leafCtr, valCtr, epochCtr, txns, forks, watches>>

\* Abort: Notifier.Reset. Trees frozen in the transaction stay readable.
DoAbort ==
    /\ tx.on
    /\ LET fz == ValuesOf(tx.frozen) IN
       hist' = [i \in DOMAIN hist |-> IF i \in fz THEN [hist[i] EXCEPT !.status = "dead"] ELSE hist[i]]
    /\ tx' = [tx EXCEPT !.on = FALSE, !.epoch = 0, !.nf = EmptyNf]
    /\ UNCHANGED <<heap, nodeCtr, leafCtr, valCtr, epochCtr, sealedN, sealedL, committed, pub, txns, forks, watches>>

\* Readers and untracked writers act on published nodes only by creating
\* their leaves, which is monotone (nil -> leaf) and matters only before the
\* tracked transaction first touches the node. It is therefore enough to let
\* them run while that transaction holds no epoch: between transactions, or
\* after a Freeze and before the next write.
Quiet == tx.epoch = 0

\* A reader asks for the channel of a key watch on a published tree:
\* valueChan creates the leaf (atomically here) if nobody has.
Materialize(i, k) ==
    /\ Quiet /\ watches < MaxWatches
    /\ watches' = watches + 1
    /\ LET s == Seek(heap, hist[i].root, k) IN
       /\ s.hit /\ heap[s.n].leaf = NIL
       /\ heap' = [heap EXCEPT ![s.n].leaf = leafCtr + 1]
       /\ leafCtr' = leafCtr + 1
    /\ UNCHANGED <<nodeCtr, valCtr, epochCtr, sealedN, sealedL, committed, tx, hist, pub, txns, forks>>

\* An untracked transaction (a snapshot: Tree.Txn(nil)) on any published
\* tree: one operation, committed; it records and notifies nothing.
Fork(i, op, k) ==
    /\ forks < Forks /\ Quiet
    /\ LET S0 == [heap |-> heap, nodeCtr |-> nodeCtr, leafCtr |-> leafCtr, root |-> hist[i].root,
                  epoch |-> 0, nextEpoch |-> epochCtr + 1, tracked |-> FALSE, nf |-> EmptyNf]
           S == CASE op = "insert" -> Insert(S0, k, valCtr + 1)
                  [] op = "delete" -> Delete(S0, k)
                  [] op = "deleteprefix" -> DeletePrefix(S0, k)
           m == hist[i].content
           exp == CASE op = "insert" -> Upd(m, k, valCtr + 1)
                    [] op = "delete" -> Del(m, k)
                    [] op = "deleteprefix" -> DelP(m, k)
       IN /\ Assert(S.nf = EmptyNf, "untracked transaction recorded something")
          /\ heap' = S.heap /\ nodeCtr' = S.nodeCtr /\ leafCtr' = S.leafCtr
          /\ epochCtr' = S.nextEpoch - 1
          /\ hist' = Append(hist, [root |-> S.root, content |-> exp, status |-> "fork"])
          /\ pub' = Publish(S.heap, pub, S.root)
    /\ valCtr' = valCtr + 1
    /\ forks' = forks + 1
    /\ UNCHANGED <<sealedN, sealedL, committed, tx, txns, watches>>

Next ==
    \/ StartTxn
    \/ \E k \in Keys : DoInsert(k) \/ DoDelete(k) \/ DoDeletePrefix(k)
    \/ DoFreeze \/ DoCommit \/ DoAbort
    \/ \E i \in DOMAIN hist, k \in Keys : Materialize(i, k)
    \/ \E i \in DOMAIN hist, op \in {"insert", "delete", "deleteprefix"}, k \in Keys : Fork(i, op, k)

Spec == Init /\ [][Next]_vars

(***************************************************************************)
(* Properties                                                              *)
(***************************************************************************)
Now == Content(heap, committed)
Lineage == {i \in DOMAIN hist : hist[i].status = "lineage"}

\* Persistence: no node of a published tree is ever mutated (its leaf may be
\* created, once), and every published tree still holds what it held.
NoMutation == \A n \in DOMAIN pub : Immutable(heap[n]) = pub[n]
Persistence == \A i \in DOMAIN hist : Content(heap, hist[i].root) = hist[i].content

\* A node owned by the transaction in progress was never published.
OwnedUnpublished == tx.epoch /= 0 => \A n \in DOMAIN pub : heap[n].epoch /= tx.epoch

\* Every operation yields the content the map semantics prescribes.
TxnContent == tx.on => Content(heap, tx.root) = tx.expected

\* checkShape on every tree.
Shape == /\ ShapeOK(heap, tx.root, TRUE)
         /\ \A i \in DOMAIN hist : ShapeOK(heap, hist[i].root, TRUE)

\* An owned node whose value was copied from a published node has the leaf
\* dropLeaf will record (Notify would dereference nil otherwise).
LeafOnCopies ==
    tx.epoch /= 0 =>
        \A n \in Reach(heap, tx.root) :
            (heap[n].epoch = tx.epoch /\ heap[n].val /= NoVal /\ ~heap[n].lob) => heap[n].leaf /= NIL
NotifyNoNil == \A i \in 1..Len(tx.nf.leaves) : tx.nf.leaves[i] /= NIL

\* The Notifier records only published objects (a subtree root excepted:
\* sealSubtree may also meet nodes that never were), each at most once, so
\* that its lists stay bounded by what the transaction actually replaced.
Recorded(sq) == {sq[i] : i \in 1..Len(sq)}
RecordsPublished ==
    /\ Recorded(tx.nf.nodes) \subseteq DOMAIN pub
    /\ Recorded(tx.nf.values) \subseteq DOMAIN pub
NoDuplicateRecords ==
    \A f \in {"nodes", "leaves", "values", "subtrees"} :
        Cardinality(Recorded(tx.nf[f])) = Len(tx.nf[f])

\* Nothing live is sealed.
LiveNotSealed ==
    \A n \in Reach(heap, committed) :
        /\ n \notin sealedN
        /\ heap[n].leaf /= NIL => heap[n].leaf \notin sealedL

\* Everything that left the tracked lineage is sealed (checkSeals): nodes,
\* and leaves no live node shares. A value that left without a leaf was
\* given sealedLeaf (a value moved into a copy shares its leaf instead).
LeavesOf(S) == {heap[n].leaf : n \in {m \in S : heap[m].leaf /= NIL}}
LeftSealed ==
    \A i \in Lineage :
        LET gone == Reach(heap, hist[i].root) \ Reach(heap, committed) IN
        /\ gone \subseteq sealedN
        /\ \A n \in gone : heap[n].val /= NoVal => heap[n].leaf /= NIL
        /\ LeavesOf(Reach(heap, hist[i].root)) \ LeavesOf(Reach(heap, committed)) \subseteq sealedL

\* Only objects of the tracked lineage (or never published) are sealed:
\* aborted and untracked transactions notify nobody.
SealedFromLineage ==
    \A n \in sealedN : n \notin DOMAIN pub \/ \E i \in Lineage : n \in Reach(heap, hist[i].root)

ValueFired(n) == heap[n].leaf /= NIL /\ heap[n].leaf \in sealedL
Val(m, k) == IF k \in DOMAIN m THEN m[k] ELSE NoVal

\* A key watch on any tree of the lineage fires iff the key's value changed
\* since (splits and merges around it must not fire it).
KeyWatch ==
    \A i \in Lineage : \A k \in Probes :
        LET s == Seek(heap, hist[i].root, k) IN
        s.hit => (ValueFired(s.n) <=> Val(hist[i].content, k) /= Val(Now, k))

\* A watch on a missing key fires once the key exists.
MissWatch ==
    \A i \in Lineage : \A k \in Probes :
        LET s == Seek(heap, hist[i].root, k) IN
        (~s.hit /\ k \in DOMAIN Now) => s.n \in sealedN

\* A prefix watch fires when any key under the prefix changed.
PrefixWatch ==
    \A i \in Lineage : \A p \in Probes :
        (\E k \in DOMAIN hist[i].content \cup DOMAIN Now :
            IsPrefix(p, k) /\ Val(hist[i].content, k) /= Val(Now, k))
        => SeekPrefixWatch(heap, hist[i].root, p) \in sealedN

\* Unchanged keys of any published tree never fire (also on forks and dead
\* branches): a sealed value is a value that changed in the lineage.
\* (A fork shares the leaves of the nodes it copies, as go-immutable-radix
\* shares leaf objects, so a key watch on a fork fires when the lineage
\* changes the key.)
NoSpuriousKeyWatch ==
    \A i \in DOMAIN hist : \A k \in Probes :
        LET s == Seek(heap, hist[i].root, k) IN
        (s.hit /\ ValueFired(s.n)) =>
            \E j \in Lineage :
                LET s2 == Seek(heap, hist[j].root, k) IN
                /\ s2.hit /\ heap[s2.n].leaf = heap[s.n].leaf
                /\ Val(hist[j].content, k) /= Val(Now, k)
=============================================================================
