---------------------------- MODULE LazyWatch ----------------------------
(***************************************************************************)
(* The lock-free protocol behind key watches in internal/radix (node.go,  *)
(* txn.go) and internal/watch (watch.go), at the granularity of Go's      *)
(* atomic operations.                                                     *)
(*                                                                         *)
(* One key is followed through a series of write transactions. Each      *)
(* version of its value lives in one node at a time, but a node is copied *)
(* whenever the tree around the key changes shape, and every copy must    *)
(* share the value's identity, its LEAF, which holds the watch slot. The  *)
(* leaf is created lazily:                                                *)
(*                                                                         *)
(*   - by a reader, valueChan: Load(n.leaf); if nil, allocate a leaf      *)
(*     whose slot is already live (Slot.Live) and CAS it in; on failure   *)
(*     Load the winner and ask its slot for a channel (Slot.Chan);        *)
(*   - by a writer copying a published node, leafOf: Load; if nil,        *)
(*     allocate and CAS; on failure Load;                                 *)
(*   - by Notify, sealValue: Load; if nil, CAS in the shared, already     *)
(*     sealed leaf; on failure Load and Seal the winner.                  *)
(*                                                                         *)
(* A slot moves nil -> live -> sealed or nil -> sealed (Slot.Chan: Load;  *)
(* if nil allocate a cell and CAS; on failure Load. Slot.Seal: Swap in    *)
(* the sealed cell, then close the old channel if it was live).           *)
(*                                                                         *)
(* The writer of the tracked lineage runs transactions made of the        *)
(* operations that matter to a value's identity -- copy the node holding  *)
(* it (split, merge, growth, a child added), update it, delete it,        *)
(* insert it, Freeze -- and then commits and notifies, or aborts.         *)
(* Ownership follows txn.go: a node carries the epoch of the transaction  *)
(* that created it and leafOwnedBit (lob) when its value was stored in    *)
(* that epoch. Optionally a second, untracked writer (a snapshot, Tree.Txn *)
(* with a nil Notifier) forks from a committed tree and copies and        *)
(* updates the same key without ever notifying.                           *)
(*                                                                         *)
(* Readers take a key watch on any node a reader can reach -- the holder  *)
(* in any committed tree, or in a frozen uncommitted one -- and run       *)
(* valueChan step by step, racing the writers and Notify, then wait.      *)
(***************************************************************************)
EXTENDS Naturals, Sequences, FiniteSets, TLC

CONSTANTS
    Readers,      \* reader processes
    MaxTxns,      \* transactions of the tracked writer
    MaxOps,       \* operations per transaction
    Fork,         \* whether an untracked writer forks from a committed tree
    Rollback,     \* whether a tracked transaction may start from an older tree
    NIL, SEALED   \* nil pointer; the sealed cell (a permanently closed channel)

ASSUME Fork \in BOOLEAN /\ Rollback \in BOOLEAN

VARIABLES
    node,       \* node id -> [ver, leaf, epoch, lob, vis]
    leafSlot,   \* leaf id -> NIL | SEALED | cell id    (leaf 1 is sealedLeaf)
    cellOpen,   \* cell id -> BOOLEAN                   (open channel)
    epochCtr,   \* the global epoch counter
    verCtr,     \* versions handed out
    w,          \* the tracked writer
    f,          \* the untracked (fork) writer
    pubHolder,  \* node holding the key in the latest committed tree (0: absent)
    retired,    \* versions retired by committed tracked transactions
    notified,   \* versions whose retirement has been notified
    rd,         \* reader states
    err         \* a violated assertion (double close)

vars == <<node, leafSlot, cellOpen, epochCtr, verCtr, w, f, pubHolder, retired, notified, rd, err>>

SealedLeaf == 1

NodeIds == DOMAIN node
LeafIds == DOMAIN leafSlot
CellIds == DOMAIN cellOpen

\* Allocation appends to a sequence: the new object's id is the new length.
Append1(sq, x) == Append(sq, x)

NewNode(ver, leaf, epoch, lob) == [ver |-> ver, leaf |-> leaf, epoch |-> epoch, lob |-> lob, vis |-> FALSE]

(***************************************************************************)
(* Initial state: the key holds version 1 in node 1, committed, no leaf.  *)
(***************************************************************************)
Init ==
    /\ node = <<[ver |-> 1, leaf |-> NIL, epoch |-> 0, lob |-> FALSE, vis |-> TRUE]>>
    /\ leafSlot = <<SEALED>>
    /\ cellOpen = <<>>
    /\ epochCtr = 0
    /\ verCtr = 1
    /\ w = [pc |-> "idle", txns |-> 0, ops |-> 0, epoch |-> 0, holder |-> 1,
            vals |-> <<>>, leaves |-> <<>>, gone |-> {}, l |-> NIL, nl |-> NIL, q |-> 0]
    /\ f = [pc |-> IF Fork THEN "start" ELSE "done", epoch |-> 0, holder |-> 0, ops |-> 0,
            l |-> NIL, nl |-> NIL]
    /\ pubHolder = 1
    /\ retired = {}
    /\ notified = {}
    /\ rd = [r \in Readers |-> [pc |-> "idle", n |-> 0, ver |-> 0, l |-> NIL, wl |-> NIL,
                                c |-> NIL, ch |-> NIL]]
    /\ err = FALSE

Owns(ep, n) == ep /= 0 /\ node[n].epoch = ep

(***************************************************************************)
(* The tracked writer.                                                    *)
(***************************************************************************)

\* Tree.Txn: a transaction on the latest committed tree -- or, with
\* Rollback, on any older published tree (an undo that keeps notifying):
\* its values may have been retired already, so their leaves may be sealed
\* a second time. No epoch yet.
WBegin ==
    /\ w.pc = "idle" /\ w.txns < MaxTxns
    /\ \E h \in {pubHolder} \cup (IF Rollback THEN {n \in NodeIds : node[n].vis} ELSE {}) :
        w' = [w EXCEPT !.pc = "txn", !.txns = @ + 1, !.ops = 0, !.epoch = 0,
                       !.holder = h, !.gone = {}]
    /\ UNCHANGED <<node, leafSlot, cellOpen, epochCtr, verCtr, f, pubHolder, retired, notified, rd, err>>

\* Txn.begin: draw an epoch on the first write since Freeze/Commit.
Begin(ep) == IF ep = 0 THEN epochCtr + 1 ELSE ep
BeginCtr(ep) == IF ep = 0 THEN epochCtr + 1 ELSE epochCtr

\* copyNode of the holder when it is owned: an owned node that outgrows its
\* child array (own), or a merge into an owned childless child: the copy
\* takes the node's leaf, epoch and lob as they are.
WCopyOwned ==
    /\ w.pc = "txn" /\ w.ops < MaxOps /\ w.holder /= 0
    /\ LET ep == Begin(w.epoch) h == w.holder IN
       /\ Owns(ep, h)
       /\ node' = Append1(node, NewNode(node[h].ver, node[h].leaf, node[h].epoch, node[h].lob))
       /\ w' = [w EXCEPT !.ops = @ + 1, !.epoch = ep, !.holder = Len(node) + 1]
       /\ epochCtr' = BeginCtr(w.epoch)
    /\ UNCHANGED <<leafSlot, cellOpen, verCtr, f, pubHolder, retired, notified, rd, err>>

\* copyNode of a published holder: shareLeaf -> leafOf, then the copy.
WCopyStart ==
    /\ w.pc = "txn" /\ w.ops < MaxOps /\ w.holder /= 0
    /\ LET ep == Begin(w.epoch) IN
       /\ ~Owns(ep, w.holder)
       /\ w' = [w EXCEPT !.ops = @ + 1, !.epoch = ep, !.pc = "leafOf1"]
       /\ epochCtr' = BeginCtr(w.epoch)
    /\ UNCHANGED <<node, leafSlot, cellOpen, verCtr, f, pubHolder, retired, notified, rd, err>>

\* leafOf: l := n.leaf.Load(); if l != nil return l; l = &leaf{}
WLeafOf1 ==
    /\ w.pc = "leafOf1"
    /\ IF node[w.holder].leaf /= NIL
       THEN /\ w' = [w EXCEPT !.l = node[w.holder].leaf, !.pc = "copy"]
            /\ UNCHANGED leafSlot
       ELSE /\ leafSlot' = Append1(leafSlot, NIL)
            /\ w' = [w EXCEPT !.nl = Len(leafSlot) + 1, !.pc = "leafOf2"]
    /\ UNCHANGED <<node, cellOpen, epochCtr, verCtr, f, pubHolder, retired, notified, rd, err>>

\* if n.leaf.CompareAndSwap(nil, l) return l; return n.leaf.Load()
WLeafOf2 ==
    /\ w.pc = "leafOf2"
    /\ IF node[w.holder].leaf = NIL
       THEN /\ node' = [node EXCEPT ![w.holder].leaf = w.nl]
            /\ w' = [w EXCEPT !.l = w.nl, !.pc = "copy"]
       ELSE /\ w' = [w EXCEPT !.pc = "leafOf3"]
            /\ UNCHANGED node
    /\ UNCHANGED <<leafSlot, cellOpen, epochCtr, verCtr, f, pubHolder, retired, notified, rd, err>>

WLeafOf3 ==
    /\ w.pc = "leafOf3"
    /\ w' = [w EXCEPT !.l = node[w.holder].leaf, !.pc = "copy"]
    /\ UNCHANGED <<node, leafSlot, cellOpen, epochCtr, verCtr, f, pubHolder, retired, notified, rd, err>>

\* c := copyShape(n); c.val, c.epoch = n.val, t.epoch|valueBit; c.leaf.Store(l)
WCopyEnd ==
    /\ w.pc = "copy"
    /\ node' = Append1(node, NewNode(node[w.holder].ver, w.l, w.epoch, FALSE))
    /\ w' = [w EXCEPT !.holder = Len(node) + 1, !.pc = "txn"]
    /\ UNCHANGED <<leafSlot, cellOpen, epochCtr, verCtr, f, pubHolder, retired, notified, rd, err>>

\* releaseValue(n): the value of n leaves the tree. Returns the new records.
Release(ep, n) ==
    IF ~Owns(ep, n) THEN [vals |-> Append(w.vals, n), leaves |-> w.leaves]      \* dropValue
    ELSE IF ~node[n].lob THEN [vals |-> w.vals, leaves |-> Append(w.leaves, node[n].leaf)] \* dropLeaf
    ELSE [vals |-> w.vals, leaves |-> w.leaves]

\* setValue: in place if the old value was stored in this epoch; otherwise
\* ownValueless (release, then the owned node or a copy without the value)
\* and the new value, stored with lob.
WUpdate ==
    /\ w.pc = "txn" /\ w.ops < MaxOps /\ w.holder /= 0
    /\ LET ep == Begin(w.epoch) h == w.holder v == verCtr + 1 IN
       /\ verCtr' = v
       /\ epochCtr' = BeginCtr(w.epoch)
       /\ IF Owns(ep, h) /\ node[h].lob
          THEN /\ node' = [node EXCEPT ![h].ver = v]
               /\ w' = [w EXCEPT !.ops = @ + 1, !.epoch = ep, !.gone = @ \cup {node[h].ver}]
          ELSE LET r == Release(ep, h) IN
               IF Owns(ep, h)
               THEN /\ node' = [node EXCEPT ![h].leaf = NIL, ![h].ver = v, ![h].lob = TRUE]
                    /\ w' = [w EXCEPT !.ops = @ + 1, !.epoch = ep, !.vals = r.vals,
                                      !.leaves = r.leaves, !.gone = @ \cup {node[h].ver}]
               ELSE /\ node' = Append1(node, NewNode(v, NIL, ep, TRUE))
                    /\ w' = [w EXCEPT !.ops = @ + 1, !.epoch = ep, !.vals = r.vals,
                                      !.leaves = r.leaves, !.holder = Len(node) + 1,
                                      !.gone = @ \cup {node[h].ver}]
    /\ UNCHANGED <<leafSlot, cellOpen, f, pubHolder, retired, notified, rd, err>>

\* Delete: dropWithLeaf / ownValueless -- the value is released.
WDelete ==
    /\ w.pc = "txn" /\ w.ops < MaxOps /\ w.holder /= 0
    /\ LET ep == Begin(w.epoch) r == Release(ep, w.holder) IN
       /\ w' = [w EXCEPT !.ops = @ + 1, !.epoch = ep, !.vals = r.vals, !.leaves = r.leaves,
                         !.holder = 0, !.gone = @ \cup {node[w.holder].ver}]
       /\ epochCtr' = BeginCtr(w.epoch)
    /\ UNCHANGED <<node, leafSlot, cellOpen, verCtr, f, pubHolder, retired, notified, rd, err>>

\* Insert of an absent key: leafNode (or a split node) with lob.
WInsert ==
    /\ w.pc = "txn" /\ w.ops < MaxOps /\ w.holder = 0
    /\ LET ep == Begin(w.epoch) IN
       /\ node' = Append1(node, NewNode(verCtr + 1, NIL, ep, TRUE))
       /\ w' = [w EXCEPT !.ops = @ + 1, !.epoch = ep, !.holder = Len(node) + 1]
       /\ epochCtr' = BeginCtr(w.epoch)
    /\ verCtr' = verCtr + 1
    /\ UNCHANGED <<leafSlot, cellOpen, f, pubHolder, retired, notified, rd, err>>

\* Freeze: the transaction abandons its epoch; its tree may now be watched.
WFreeze ==
    /\ w.pc = "txn" /\ w.ops < MaxOps
    /\ w' = [w EXCEPT !.ops = @ + 1, !.epoch = 0]
    /\ node' = IF w.holder /= 0 THEN [node EXCEPT ![w.holder].vis = TRUE] ELSE node
    /\ UNCHANGED <<leafSlot, cellOpen, epochCtr, verCtr, f, pubHolder, retired, notified, rd, err>>

\* Commit and publish; Notify follows.
WCommit ==
    /\ w.pc = "txn"
    /\ w' = [w EXCEPT !.epoch = 0, !.pc = "notify", !.q = 1]
    /\ node' = IF w.holder /= 0 THEN [node EXCEPT ![w.holder].vis = TRUE] ELSE node
    /\ pubHolder' = w.holder
    /\ retired' = retired \cup w.gone
    /\ UNCHANGED <<leafSlot, cellOpen, epochCtr, verCtr, f, notified, rd, err>>

\* Abort: Notifier.Reset.
WAbort ==
    /\ w.pc = "txn"
    /\ w' = [w EXCEPT !.epoch = 0, !.pc = "idle", !.vals = <<>>, !.leaves = <<>>, !.gone = {}]
    /\ UNCHANGED <<node, leafSlot, cellOpen, epochCtr, verCtr, f, pubHolder, retired, notified, rd, err>>

(***************************************************************************)
(* Notify: the recorded leaves (Seal), then the recorded value nodes      *)
(* (sealValue). w.q walks the leaves, then the values.                    *)
(***************************************************************************)
NLeaves == Len(w.leaves)
NItems == NLeaves + Len(w.vals)

\* The loop of Notifier.Notify: the next recorded leaf or value, or done.
WNotifyNext ==
    /\ w.pc = "notify"
    /\ IF w.q > NItems
       THEN /\ w' = [w EXCEPT !.pc = "idle", !.vals = <<>>, !.leaves = <<>>, !.gone = {}]
            /\ notified' = notified \cup w.gone
       ELSE /\ w' = [w EXCEPT !.pc = IF w.q <= NLeaves THEN "seal" ELSE "sv1",
                              !.l = IF w.q <= NLeaves THEN w.leaves[w.q] ELSE NIL]
            /\ UNCHANGED notified
    /\ UNCHANGED <<node, leafSlot, cellOpen, epochCtr, verCtr, f, pubHolder, retired, rd, err>>

\* sealValue(n): l := n.leaf.Load(); if l == nil { CAS(nil, sealedLeaf) ... }
WSealValue1 ==
    /\ w.pc = "sv1"
    /\ LET n == w.vals[w.q - NLeaves] IN
       IF node[n].leaf /= NIL
       THEN w' = [w EXCEPT !.l = node[n].leaf, !.pc = "seal"]
       ELSE w' = [w EXCEPT !.pc = "sv2"]
    /\ UNCHANGED <<node, leafSlot, cellOpen, epochCtr, verCtr, f, pubHolder, retired, notified, rd, err>>

WSealValue2 ==
    /\ w.pc = "sv2"
    /\ LET n == w.vals[w.q - NLeaves] IN
       IF node[n].leaf = NIL
       THEN /\ node' = [node EXCEPT ![n].leaf = SealedLeaf]
            /\ w' = [w EXCEPT !.q = @ + 1, !.pc = "notify"]
       ELSE /\ w' = [w EXCEPT !.l = node[n].leaf, !.pc = "seal"]   \* a watcher got there first
            /\ UNCHANGED node
    /\ UNCHANGED <<leafSlot, cellOpen, epochCtr, verCtr, f, pubHolder, retired, notified, rd, err>>

\* Slot.Seal, step 1: the Swap.
WSeal ==
    /\ w.pc = "seal"
    /\ LET old == leafSlot[w.l] IN
       /\ leafSlot' = [leafSlot EXCEPT ![w.l] = SEALED]
       /\ w' = [w EXCEPT !.pc = IF old \notin {NIL, SEALED} THEN "close" ELSE "notify",
                         !.nl = old, !.q = IF old \notin {NIL, SEALED} THEN @ ELSE @ + 1]
    /\ UNCHANGED <<node, cellOpen, epochCtr, verCtr, f, pubHolder, retired, notified, rd, err>>

\* Slot.Seal, step 2: close(old.ch). Closing a closed channel panics.
WClose ==
    /\ w.pc = "close"
    /\ err' = (err \/ w.nl = SEALED \/ ~cellOpen[w.nl])
    /\ cellOpen' = IF w.nl = SEALED THEN cellOpen ELSE [cellOpen EXCEPT ![w.nl] = FALSE]
    /\ w' = [w EXCEPT !.pc = "notify", !.q = @ + 1]
    /\ UNCHANGED <<node, leafSlot, epochCtr, verCtr, f, pubHolder, retired, notified, rd>>

Writer ==
    \/ WBegin \/ WCopyOwned \/ WCopyStart \/ WLeafOf1 \/ WLeafOf2 \/ WLeafOf3 \/ WCopyEnd
    \/ WUpdate \/ WDelete \/ WInsert \/ WFreeze \/ WCommit \/ WAbort
    \/ WNotifyNext \/ WSealValue1 \/ WSealValue2 \/ WSeal \/ WClose

(***************************************************************************)
(* The untracked fork: one transaction on a committed tree that copies   *)
(* the holder (leafOf on a published node) and may update it; it records *)
(* nothing and never notifies.                                            *)
(***************************************************************************)
FStart ==
    /\ f.pc = "start"
    /\ \E n \in NodeIds :        \* the holder in any committed or frozen tree
        /\ node[n].vis
        /\ f' = [f EXCEPT !.pc = "leafOf1", !.holder = n, !.epoch = epochCtr + 1]
    /\ epochCtr' = epochCtr + 1
    /\ UNCHANGED <<node, leafSlot, cellOpen, verCtr, w, pubHolder, retired, notified, rd, err>>

FLeafOf1 ==
    /\ f.pc = "leafOf1"
    /\ IF node[f.holder].leaf /= NIL
       THEN /\ f' = [f EXCEPT !.l = node[f.holder].leaf, !.pc = "copy"]
            /\ UNCHANGED leafSlot
       ELSE /\ leafSlot' = Append1(leafSlot, NIL)
            /\ f' = [f EXCEPT !.nl = Len(leafSlot) + 1, !.pc = "leafOf2"]
    /\ UNCHANGED <<node, cellOpen, epochCtr, verCtr, w, pubHolder, retired, notified, rd, err>>

FLeafOf2 ==
    /\ f.pc = "leafOf2"
    /\ IF node[f.holder].leaf = NIL
       THEN /\ node' = [node EXCEPT ![f.holder].leaf = f.nl]
            /\ f' = [f EXCEPT !.l = f.nl, !.pc = "copy"]
       ELSE /\ f' = [f EXCEPT !.pc = "leafOf3"]
            /\ UNCHANGED node
    /\ UNCHANGED <<leafSlot, cellOpen, epochCtr, verCtr, w, pubHolder, retired, notified, rd, err>>

FLeafOf3 ==
    /\ f.pc = "leafOf3"
    /\ f' = [f EXCEPT !.l = node[f.holder].leaf, !.pc = "copy"]
    /\ UNCHANGED <<node, leafSlot, cellOpen, epochCtr, verCtr, w, pubHolder, retired, notified, rd, err>>

\* The copy, committed at once: the fork's tree is visible to its readers.
FCopyEnd ==
    /\ f.pc = "copy"
    /\ node' = Append1(node, [NewNode(node[f.holder].ver, f.l, f.epoch, FALSE) EXCEPT !.vis = TRUE])
    /\ f' = [f EXCEPT !.holder = Len(node) + 1, !.pc = "end"]
    /\ UNCHANGED <<leafSlot, cellOpen, epochCtr, verCtr, w, pubHolder, retired, notified, rd, err>>

\* An untracked update of the copy: records nothing (nf == nil).
FUpdate ==
    /\ f.pc = "end"
    /\ node' = Append1(node, [NewNode(verCtr + 1, NIL, f.epoch, TRUE) EXCEPT !.vis = TRUE])
    /\ verCtr' = verCtr + 1
    /\ f' = [f EXCEPT !.holder = Len(node) + 1, !.pc = "done"]
    /\ UNCHANGED <<leafSlot, cellOpen, epochCtr, w, pubHolder, retired, notified, rd, err>>

FStop ==
    /\ f.pc = "end"
    /\ f' = [f EXCEPT !.pc = "done"]
    /\ UNCHANGED <<node, leafSlot, cellOpen, epochCtr, verCtr, w, pubHolder, retired, notified, rd, err>>

ForkWriter == FStart \/ FLeafOf1 \/ FLeafOf2 \/ FLeafOf3 \/ FCopyEnd \/ FUpdate \/ FStop

(***************************************************************************)
(* Readers: GetWatch on a hit returns Watch{value: n}; Chan() then runs   *)
(* valueChan(n), and the reader waits for the channel to close.           *)
(***************************************************************************)
RSet(r, rec) == rd' = [rd EXCEPT ![r] = rec]

\* Any node a reader can reach: visible, i.e. in a committed or frozen tree.
RWatch(r) ==
    /\ rd[r].pc = "idle"
    /\ \E n \in NodeIds :
        /\ node[n].vis
        /\ RSet(r, [rd[r] EXCEPT !.pc = "vc1", !.n = n, !.ver = node[n].ver])
    /\ UNCHANGED <<node, leafSlot, cellOpen, epochCtr, verCtr, w, f, pubHolder, retired, notified, err>>

\* valueChan: if l := n.leaf.Load(); l != nil { return l.watch.Chan() }
RVC1(r) ==
    /\ rd[r].pc = "vc1"
    /\ LET l == node[rd[r].n].leaf IN
       IF l /= NIL THEN RSet(r, [rd[r] EXCEPT !.l = l, !.pc = "ch1"])
       ELSE RSet(r, [rd[r] EXCEPT !.pc = "vc2"])
    /\ UNCHANGED <<node, leafSlot, cellOpen, epochCtr, verCtr, w, f, pubHolder, retired, notified, err>>

\* wl := &watchedLeaf{}; ch := wl.watch.Live(&wl.cell)
RVC2(r) ==
    /\ rd[r].pc = "vc2"
    /\ cellOpen' = Append1(cellOpen, TRUE)
    /\ leafSlot' = Append1(leafSlot, Len(cellOpen) + 1)
    /\ RSet(r, [rd[r] EXCEPT !.wl = Len(leafSlot) + 1, !.c = Len(cellOpen) + 1, !.pc = "vc3"])
    /\ UNCHANGED <<node, epochCtr, verCtr, w, f, pubHolder, retired, notified, err>>

\* if n.leaf.CompareAndSwap(nil, &wl.leaf) { return ch }
RVC3(r) ==
    /\ rd[r].pc = "vc3"
    /\ IF node[rd[r].n].leaf = NIL
       THEN /\ node' = [node EXCEPT ![rd[r].n].leaf = rd[r].wl]
            /\ RSet(r, [rd[r] EXCEPT !.ch = rd[r].c, !.pc = "wait"])
       ELSE /\ RSet(r, [rd[r] EXCEPT !.pc = "vc4"])
            /\ UNCHANGED node
    /\ UNCHANGED <<leafSlot, cellOpen, epochCtr, verCtr, w, f, pubHolder, retired, notified, err>>

\* return n.leaf.Load().watch.Chan()
RVC4(r) ==
    /\ rd[r].pc = "vc4"
    /\ RSet(r, [rd[r] EXCEPT !.l = node[rd[r].n].leaf, !.pc = "ch1"])
    /\ UNCHANGED <<node, leafSlot, cellOpen, epochCtr, verCtr, w, f, pubHolder, retired, notified, err>>

\* Slot.Chan: if c := s.p.Load(); c != nil { return c.ch }; c = new cell
RCh1(r) ==
    /\ rd[r].pc = "ch1"
    /\ LET c == leafSlot[rd[r].l] IN
       IF c /= NIL
       THEN /\ RSet(r, [rd[r] EXCEPT !.ch = c, !.pc = "wait"])
            /\ UNCHANGED cellOpen
       ELSE /\ cellOpen' = Append1(cellOpen, TRUE)
            /\ RSet(r, [rd[r] EXCEPT !.c = Len(cellOpen) + 1, !.pc = "ch2"])
    /\ UNCHANGED <<node, leafSlot, epochCtr, verCtr, w, f, pubHolder, retired, notified, err>>

\* if s.p.CompareAndSwap(nil, c) { return c.ch }; return s.p.Load().ch
RCh2(r) ==
    /\ rd[r].pc = "ch2"
    /\ IF leafSlot[rd[r].l] = NIL
       THEN /\ leafSlot' = [leafSlot EXCEPT ![rd[r].l] = rd[r].c]
            /\ RSet(r, [rd[r] EXCEPT !.ch = rd[r].c, !.pc = "wait"])
       ELSE /\ RSet(r, [rd[r] EXCEPT !.pc = "ch3"])
            /\ UNCHANGED leafSlot
    /\ UNCHANGED <<node, cellOpen, epochCtr, verCtr, w, f, pubHolder, retired, notified, err>>

RCh3(r) ==
    /\ rd[r].pc = "ch3"
    /\ RSet(r, [rd[r] EXCEPT !.ch = leafSlot[rd[r].l], !.pc = "wait"])
    /\ UNCHANGED <<node, leafSlot, cellOpen, epochCtr, verCtr, w, f, pubHolder, retired, notified, err>>

Closed(ch) == ch = SEALED \/ (ch \in CellIds /\ ~cellOpen[ch])

\* <-ch returns.
RWake(r) ==
    /\ rd[r].pc = "wait" /\ Closed(rd[r].ch)
    /\ RSet(r, [rd[r] EXCEPT !.pc = "done"])
    /\ UNCHANGED <<node, leafSlot, cellOpen, epochCtr, verCtr, w, f, pubHolder, retired, notified, err>>

Reader(r) == RWatch(r) \/ RVC1(r) \/ RVC2(r) \/ RVC3(r) \/ RVC4(r) \/ RCh1(r) \/ RCh2(r) \/ RCh3(r) \/ RWake(r)

Next == Writer \/ ForkWriter \/ \E r \in Readers : Reader(r)

Spec == Init /\ [][Next]_vars
    /\ WF_vars(Writer) /\ WF_vars(ForkWriter)
    /\ \A r \in Readers : WF_vars(RVC1(r) \/ RVC2(r) \/ RVC3(r) \/ RVC4(r) \/ RCh1(r) \/ RCh2(r) \/ RCh3(r) \/ RWake(r))

(***************************************************************************)
(* Properties                                                              *)
(***************************************************************************)

\* No channel is closed twice (Go would panic).
NoDoubleClose == ~err

\* Notify never meets a nil leaf (Go would dereference nil): dropLeaf only
\* records the leaf of an owned node whose value came from a published node.
DropLeafNonNil == \A i \in 1..Len(w.leaves) : w.leaves[i] /= NIL

\* A node anyone can reach is never mutated in place: it is never owned by
\* the transaction in progress.
VisibleNotOwned == \A n \in NodeIds : node[n].vis => ~Owns(w.epoch, n)

\* Every reachable copy of a value version shares one leaf.
LeafShared ==
    \A n1, n2 \in NodeIds :
        (n1 /= n2 /\ node[n1].vis /\ node[n2].vis /\ node[n1].ver = node[n2].ver)
            => (node[n1].leaf = node[n2].leaf /\ node[n1].leaf /= NIL)

\* No lost wakeup: once the retirement of a version has been notified, every
\* channel handed out for it is closed -- including one handed out later,
\* through an old tree.
NoLostWakeup ==
    \A r \in Readers : (rd[r].pc = "wait" /\ rd[r].ver \in notified) => Closed(rd[r].ch)

\* ... and every reachable node holding it now leads to a sealed leaf.
RetiredSealed ==
    \A n \in NodeIds :
        (node[n].vis /\ node[n].ver \in notified)
            => node[n].leaf /= NIL /\ leafSlot[node[n].leaf] = SEALED

\* No spurious wakeup: a key watch fires only for a version that a committed
\* tracked transaction retired (never for an aborted or untracked one).
NoSpuriousWakeup ==
    \A r \in Readers : (rd[r].pc \in {"wait", "done"} /\ Closed(rd[r].ch)) => rd[r].ver \in retired

\* valueChan is wait-free: every reader that starts gets a channel.
ReadersGetChannel == \A r \in Readers : (rd[r].pc = "vc1") ~> (rd[r].pc \in {"wait", "done"})

\* A notified reader wakes.
NotifiedWakes == \A r \in Readers : (rd[r].pc = "wait" /\ rd[r].ver \in notified) ~> (rd[r].pc = "done")

=============================================================================
