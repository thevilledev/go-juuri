/-
Copyright (c) 2026 Ville Vesilehto
SPDX-License-Identifier: MPL-2.0

The functional core of internal/radix: the tree shape and every read and
write operation, transcribed from the Go code.

What is modelled and what is not:

* A node is its path segment (`prefix`, including the label byte), its
  optional value, and its children in ascending label order. The Go node
  finds a child through a 256-bit bitmap and `rank`; `Rank.lean` proves that
  on a node whose bitmap agrees with its child array (`Rank.Consistent`),
  `rank` returns exactly `rankOf` below, and that `addKid` / `delKid` keep the
  agreement. Here the child list is the representation.
* Bytes are natural numbers: the code only ever compares them.
* Ownership epochs, in-place mutation and copying do not change what a tree
  holds, only which objects hold it; they are the subject of the TLA+ model
  (formal/tla), as are watch channels. A write here returns the new tree.
* The compact-leaf layout (segments stored inside the node) is a storage
  detail of node_unsafe.go / segment_unsafe.go and is not modelled.

Each definition names the Go function it transcribes. Where the Go code
relies on an invariant for memory safety (reading a child count, indexing
the child array), the model takes the corresponding branch explicitly and
reports a fault; the iterator theorems prove that no fault occurs.
-/

namespace JuuriFormal

/-- A key, or a path segment: a byte string. -/
abbrev Key := List Nat

/-- A radix tree node. -/
inductive Node (α : Type) where
  | mk (seg : Key) (val : Option α) (kids : List (Node α))

namespace Node

variable {α : Type}

/-- Recursion into a child: the child is smaller than its parent. -/
macro "kid_decreasing" : tactic =>
  `(tactic| (have := List.sizeOf_lt_of_mem ‹_ ∈ _›; simp; omega))

def seg : Node α → Key
  | mk s _ _ => s

def val : Node α → Option α
  | mk _ v _ => v

def kids : Node α → List (Node α)
  | mk _ _ k => k

@[simp] theorem seg_mk (s : Key) (v : Option α) (k : List (Node α)) : (mk s v k).seg = s := rfl
@[simp] theorem val_mk (s : Key) (v : Option α) (k : List (Node α)) : (mk s v k).val = v := rfl
@[simp] theorem kids_mk (s : Key) (v : Option α) (k : List (Node α)) : (mk s v k).kids = k := rfl

/-- The label a parent indexes the node by: the first byte of its segment. -/
def lbl (n : Node α) : Nat := n.seg.headD 0

/-- Number of nodes. -/
def size : Node α → Nat
  | mk _ _ kids => 1 + (kids.map size).sum

/-! ### The abstract content -/

/-- The key/value pairs stored at and below `n`, keys relative to the end of
`n`'s own segment, in tree order (own value first, then children in label
order). -/
def entries : Node α → List (Key × α)
  | mk _ v kids =>
    (v.map (fun x => ([], x))).toList ++
      kids.flatMap (fun c => (entries c).map (fun e => (c.seg ++ e.1, e.2)))

/-- Lexicographic byte order on keys, as Go compares strings. -/
def keyLt : Key → Key → Bool
  | [], [] => false
  | [], _ :: _ => true
  | _ :: _, [] => false
  | a :: as, b :: bs => decide (a < b) || (decide (a = b) && keyLt as bs)

/-- The shape invariant (checkShape in model_test.go). The root has an empty
segment; every other node a non-empty one, and a value or at least two
children; children are in strictly ascending label order. -/
inductive WF : Bool → Node α → Prop
  | mk {isRoot : Bool} {s : Key} {v : Option α} {kids : List (Node α)} :
      (isRoot = true → s = []) →
      (isRoot = false → s ≠ [] ∧ (v = none → 2 ≤ kids.length)) →
      (kids.map lbl).Pairwise (· < ·) →
      (∀ c ∈ kids, WF false c) →
      WF isRoot (mk s v kids)

/-! ### Helpers shared with the Go code -/

/-- `rank` (see Rank.lean): the number of children with a smaller label, and
whether a child has this label. -/
def rankOf (kids : List (Node α)) (b : Nat) : Nat × Bool :=
  (kids.countP (fun c => decide (c.lbl < b)), kids.any (fun c => decide (c.lbl = b)))

/-- `n.kid(i)`, with the membership needed for termination. -/
def getKid (kids : List (Node α)) (i : Nat) : Option {c : Node α // c ∈ kids} :=
  match h : kids[i]? with
  | none => none
  | some c => some ⟨c, List.mem_of_getElem? h⟩

/-- `commonPrefixLen`. -/
def lcp : Key → Key → Nat
  | a :: as, b :: bs => if a = b then lcp as bs + 1 else 0
  | _, _ => 0

/-- `node.hasPrefix`, with its one- and two-byte fast paths. It is only called
on a child found under `search[0]`, so the first byte is known to match. -/
def goHasPrefix (seg search : Key) : Bool :=
  if seg.length = 1 then true
  else if seg.length = 2 then decide (2 ≤ search.length) && decide (search[1]? = seg[1]?)
  else decide (seg.length ≤ search.length) && decide (search.take seg.length = seg)

/-! ### Lookups (tree.go) -/

/-- `Tree.Get`, from a node, with `search` relative to the end of its segment. -/
def get : Node α → Key → Option α
  | mk _ v _, [] => v
  | mk _ _ kids, b :: rest =>
    if (rankOf kids b).2 then
      match getKid kids (rankOf kids b).1 with
      | none => none
      | some ⟨c, _⟩ =>
        if c.seg.isPrefixOf (b :: rest) then get c ((b :: rest).drop c.seg.length) else none
    else none
termination_by n => sizeOf n
decreasing_by kid_decreasing

/-- `Tree.LongestPrefix`: `best` is the value of the deepest node with a value
passed so far. -/
def longestPrefix : Node α → Key → Option α → Option α
  | mk _ v kids, search, best =>
    let best := if v.isSome then v else best
    match search with
    | [] => best
    | b :: rest =>
      if (rankOf kids b).2 then
        match getKid kids (rankOf kids b).1 with
        | none => best
        | some ⟨c, _⟩ =>
          if c.seg.isPrefixOf (b :: rest) then
            longestPrefix c ((b :: rest).drop c.seg.length) best
          else best
      else best
termination_by n => sizeOf n
decreasing_by kid_decreasing

/-- `Tree.seekPrefix` (without the watch): the node whose subtree holds
exactly the keys that start with the prefix. -/
def seekPrefix : Node α → Key → Option (Node α)
  | n, [] => some n
  | mk _ _ kids, b :: rest =>
    if (rankOf kids b).2 then
      match getKid kids (rankOf kids b).1 with
      | none => none
      | some ⟨c, _⟩ =>
        if c.seg.isPrefixOf (b :: rest) then seekPrefix c ((b :: rest).drop c.seg.length)
        else if (b :: rest).length < c.seg.length ∧ (b :: rest).isPrefixOf c.seg then some c
        else none
    else none
termination_by n => sizeOf n
decreasing_by kid_decreasing

/-- `node.minNode`. -/
def minNode : Node α → Option (Node α)
  | mk s v kids =>
    if v.isSome then some (mk s v kids)
    else
      match getKid kids 0 with
      | none => none
      | some ⟨c, _⟩ => minNode c
termination_by n => sizeOf n
decreasing_by kid_decreasing

/-- `node.maxNode`. -/
def maxNode : Node α → Option (Node α)
  | mk s v kids =>
    match getKid kids (kids.length - 1) with
    | none => if v.isSome then some (mk s v kids) else none
    | some ⟨c, _⟩ => maxNode c
termination_by n => sizeOf n
decreasing_by kid_decreasing

/-- `Tree.FirstPrefix` (value only). -/
def firstPrefix (t : Node α) (p : Key) : Option α :=
  match seekPrefix t p with
  | none => none
  | some n => (minNode n).bind val

/-- `Tree.LastPrefix` (value only). -/
def lastPrefix (t : Node α) (p : Key) : Option α :=
  match seekPrefix t p with
  | none => none
  | some n => (maxNode n).bind val

/-! ### Writes (txn.go) -/

/-- `Txn.Insert`, from a node, with `search` relative to the end of its
segment: the new node and the value replaced. Ownership only decides whether
a node on the path is copied or changed in place; either way the result is
the node below. -/
def insert : Node α → Key → α → Node α × Option α
  | mk s v kids, [], x => (mk s (some x) kids, v)   -- setValue
  | mk s v kids, b :: rest, x =>
    if (rankOf kids b).2 then
      match getKid kids (rankOf kids b).1 with
      | none => (mk s v kids, none)
      | some ⟨c, _⟩ =>
        let search := b :: rest
        let common := lcp search c.seg
        if common = c.seg.length then
          let r := insert c (search.drop common) x
          (mk s v (kids.set (rankOf kids b).1 r.1), r.2)
        else
          -- The key diverges inside the child's segment: split it.
          let trimmed := mk (c.seg.drop common) c.val c.kids
          let split :=
            match search.drop common with
            | [] => mk (c.seg.take common) (some x) [trimmed]
            | restS =>
              let added : Node α := mk restS (some x) []
              mk (c.seg.take common) none
                (if added.lbl < trimmed.lbl then [added, trimmed] else [trimmed, added])
          (mk s v (kids.set (rankOf kids b).1 split), none)
    else
      -- No edge for the next byte: hang a new leaf (addKid at the rank index).
      (mk s v (kids.insertIdx (rankOf kids b).1 (mk (b :: rest) (some x) [])), none)
termination_by n => sizeOf n
decreasing_by kid_decreasing

/-- `mergeChild`: `n`, left without a value and with the single child `c`, is
replaced by `c` with the two segments joined. -/
def mergeNode (n c : Node α) : Node α := mk (n.seg ++ c.seg) c.val c.kids

/-- `Txn.unlink`, at the parent `n` of the child at `idx` that is removed: a
parent other than the root left without a value and with a single child is
merged with that child (`parent.kid(1-idx)`). -/
def unlink (isRoot : Bool) (n : Node α) (idx : Nat) : Node α :=
  match n with
  | mk s v kids =>
    if !isRoot && v.isNone && kids.length == 2 then
      match kids[1 - idx]? with
      | some sib => mergeNode n sib
      | none => mk s v (kids.eraseIdx idx)
    else mk s v (kids.eraseIdx idx)

/-- `Txn.Delete`, from a node, with `search` relative to the end of its
segment. `none`: the key is absent and nothing changes. Otherwise the value
removed and what replaces `n`: `none` when `n` itself goes away (the parent
then unlinks it). -/
def delete : Bool → Node α → Key → Option (Option (Node α) × α)
  | isRoot, mk s v kids, [] =>
    match v with
    | none => none
    | some x =>
      if isRoot then some (some (mk s none kids), x)            -- the root: ownValueless
      else if kids.length = 0 then some (none, x)                -- childless: unlink
      else match kids with
        | [c] => some (some (mergeNode (mk s v kids) c), x)      -- one child: mergeChild
        | _ => some (some (mk s none kids), x)                   -- ownValueless
  | isRoot, mk s v kids, b :: rest =>
    if (rankOf kids b).2 then
      match getKid kids (rankOf kids b).1 with
      | none => none
      | some ⟨c, _⟩ =>
        if c.seg.isPrefixOf (b :: rest) then
          match delete false c ((b :: rest).drop c.seg.length) with
          | none => none
          | some (none, x) => some (some (unlink isRoot (mk s v kids) (rankOf kids b).1), x)
          | some (some c', x) => some (some (mk s v (kids.set (rankOf kids b).1 c')), x)
        else none
    else none
termination_by _ n => sizeOf n
decreasing_by kid_decreasing

/-- `Txn.DeletePrefix`, from a node, with `search` relative to the end of its
segment. `none`: no key starts with the prefix. Otherwise what replaces `n`
(`none`: `n` goes away). The empty prefix at the root replaces the root with
an empty one. -/
def deletePrefix : Bool → Node α → Key → Option (Option (Node α))
  | isRoot, _, [] => if isRoot then some (some (mk [] none [])) else some none
  | isRoot, mk s v kids, b :: rest =>
    if (rankOf kids b).2 then
      match getKid kids (rankOf kids b).1 with
      | none => none
      | some ⟨c, _⟩ =>
        let search := b :: rest
        let sub :=
          if c.seg.isPrefixOf search then some (search.drop c.seg.length)
          else if search.length < c.seg.length ∧ search.isPrefixOf c.seg then some []
          else none
        match sub with
        | none => none
        | some sub =>
          match deletePrefix false c sub with
          | none => none
          | some none => some (some (unlink isRoot (mk s v kids) (rankOf kids b).1))
          | some (some c') => some (some (mk s v (kids.set (rankOf kids b).1 c')))
    else none
termination_by _ n => sizeOf n
decreasing_by kid_decreasing

/-! ### Iteration (iter.go)

A stack is a list of frames, top first. A frame is a node and a position,
with the meaning of iter.go: forward, `-1` means the node's own value is
still due, `-2` (`leafOnly`) a childless node whose value is due, and `i ≥ 0`
the next child to visit; in reverse, `i ≥ 0` is the next child, counting
down, and `i < 0` means only the node's own value is left. -/

abbrev Stack (α : Type) := List (Node α × Int)

def leafOnly : Int := -2

/-- What one iteration of the loop in `Next` / `Previous` does. `fault` is an
access the Go code only gets away with by an invariant: a child count read
from a node without children (garbage in a compact leaf), or a child index
out of range. -/
inductive Step (α : Type) where
  | done
  | emit (v : Option α) (s : Stack α)
  | cont (s : Stack α)
  | fault

/-- `Iterator.pushSubtree`. -/
def pushSubtree (n : Node α) (s : Stack α) : Stack α :=
  if !n.kids.isEmpty then (n, -1) :: s
  else if n.val.isSome then (n, leafOnly) :: s
  else s

/-- One iteration of the loop in `Iterator.Next`. -/
def nextStep : Stack α → Step α
  | [] => .done
  | (n, i) :: s =>
    if i = leafOnly then .emit n.val s
    else if i < 0 ∧ n.val.isSome then .emit n.val ((n, 0) :: s)
    else
      let j : Int := if i < 0 then 0 else i
      -- frameKids: only valid on a node with children
      if n.kids.isEmpty then .fault
      else
        match n.kids[j.toNat]? with
        | none => .cont s
        | some c =>
          if c.kids.isEmpty then .emit c.val ((n, j + 1) :: s)
          else .cont ((c, -1) :: (n, j + 1) :: s)

/-- One iteration of the loop in `ReverseIterator.Previous`. -/
def prevStep : Stack α → Step α
  | [] => .done
  | (n, i) :: s =>
    if i < 0 then (if n.val.isSome then .emit n.val s else .cont s)
    else
      match n.kids[i.toNat]? with
      | none => .fault
      | some c =>
        if c.kids.isEmpty then .emit c.val ((n, i - 1) :: s)
        else .cont ((c, (c.kids.length : Int) - 1) :: (n, i - 1) :: s)

/-- Draining an iterator: what `for v, ok := it.Next(); ok; v, ok = it.Next()`
collects, given enough fuel. A fault shows up as a `none` in the output. -/
def run (step : Stack α → Step α) : Nat → Stack α → List (Option α)
  | 0, _ => []
  | fuel + 1, s =>
    match step s with
    | .done => []
    | .emit v s' => v :: run step fuel s'
    | .cont s' => run step fuel s'
    | .fault => [none]

/-- `Iterator.SeekLowerBound`, from node `n` with the remaining `search`,
pushing onto `s`. -/
def seekLowerBound : Node α → Key → Stack α → Stack α
  | mk seg v kids, search, s =>
    let n : Node α := mk seg v kids
    let common := lcp search seg
    if common < seg.length then
      if common = search.length ∨ seg.getD common 0 > search.getD common 0 then pushSubtree n s
      else s
    else
      match search.drop common with
      | [] => pushSubtree n s
      | b :: rest =>
        if (rankOf kids b).2 then
          match getKid kids (rankOf kids b).1 with
          | none => s
          | some ⟨c, _⟩ => seekLowerBound c (b :: rest) ((n, ((rankOf kids b).1 : Int) + 1) :: s)
        else if (rankOf kids b).1 < kids.length then (n, ((rankOf kids b).1 : Int)) :: s
        else s
termination_by n => sizeOf n
decreasing_by kid_decreasing

/-- `ReverseIterator.SeekReverseLowerBound`. -/
def seekReverseLowerBound : Node α → Key → Stack α → Stack α
  | mk seg v kids, search, s =>
    let n : Node α := mk seg v kids
    let common := lcp search seg
    if common < seg.length then
      if common < search.length ∧ seg.getD common 0 < search.getD common 0 then
        (n, (kids.length : Int) - 1) :: s
      else s
    else
      match search.drop common with
      | [] => (n, -1) :: s
      | b :: rest =>
        let s' := (n, ((rankOf kids b).1 : Int) - 1) :: s
        if (rankOf kids b).2 then
          match getKid kids (rankOf kids b).1 with
          | none => s'
          | some ⟨c, _⟩ => seekReverseLowerBound c (b :: rest) s'
        else s'
termination_by n => sizeOf n
decreasing_by kid_decreasing

/-- `Iterator.SeekPrefixWatch` (without the watch). -/
def seekPrefixFwd (t : Node α) (p : Key) : Stack α :=
  match seekPrefix t p with
  | none => []
  | some n => pushSubtree n []

/-- `ReverseIterator.SeekPrefixWatch` (without the watch). -/
def seekPrefixRev (t : Node α) (p : Key) : Stack α :=
  match seekPrefix t p with
  | none => []
  | some n => [(n, (n.kids.length : Int) - 1)]

end Node

end JuuriFormal
