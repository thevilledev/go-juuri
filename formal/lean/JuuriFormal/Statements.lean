/-
Copyright (c) 2026 Ville Vesilehto
SPDX-License-Identifier: MPL-2.0

Every headline result, restated in full. Each `example` must typecheck against
the theorem it names, so this file pins the exact statement that was proved:
a proof file cannot quietly weaken one. `lake build` also prints the axioms
each depends on; the expected set is the standard [propext, Classical.choice,
Quot.sound].
-/
import JuuriFormal.Bridge
import JuuriFormal.Lookup
import JuuriFormal.Insert
import JuuriFormal.Delete
import JuuriFormal.Iter
import JuuriFormal.IterRev
import JuuriFormal.Stack

namespace JuuriFormal
namespace Node

variable {α : Type}

/-! ### rank (node.go) -/

example (bm : Rank.Bitmap) (label : UInt8) :
    Rank.goRank bm label = (Rank.rankSpec bm label.toNat, bm.test label.toNat) :=
  Rank.goRank_correct bm label

example {bm : Rank.Bitmap} {labels : List Nat} (h : Rank.Consistent bm labels) (l : UInt8)
    (hf : (Rank.goRank bm l).2 = false) :
    Rank.Consistent (bm.set l) (labels.insertIdx (Rank.goRank bm l).1 l.toNat) :=
  Rank.addKid_consistent h l hf

example {bm : Rank.Bitmap} {labels : List Nat} (h : Rank.Consistent bm labels)
    (idx : Nat) (hidx : idx < labels.length) (l : UInt8) (hl : labels[idx] = l.toNat) :
    Rank.Consistent (bm.clear l) (labels.eraseIdx idx) :=
  Rank.delKid_consistent h idx hidx l hl

example (kids : List (Node α)) (bm : Rank.Bitmap) (h : Rank.Consistent bm (kids.map lbl))
    (b : UInt8) : Rank.goRank bm b = rankOf kids b.toNat :=
  rankOf_eq_goRank kids bm h b

/-- `hasPrefix`'s fast paths agree with a plain prefix test on a child found
by its label. -/
example {seg rest : Key} {b : Nat} (h : seg.head? = some b) :
    goHasPrefix seg (b :: rest) = seg.isPrefixOf (b :: rest) :=
  lookup_goHasPrefix_eq h

/-! ### Shape and order -/

example {r : Bool} {n : Node α} (h : WF r n) : Sorted (entries n) := entries_sorted h

/-! ### Lookups (tree.go) -/

example {r : Bool} {n : Node α} (h : WF r n) (k : Key) :
    get n k = (entries n).lookup k :=
  get_correct h k

example {t : Node α} (h : WF true t) (k : Key) :
    longestPrefix t k none = ((entries t).filter (fun e => e.1.isPrefixOf k)).getLast?.map (·.2) :=
  longestPrefix_correct h k

example {t : Node α} (h : WF true t) (p : Key) :
    firstPrefix t p = ((entries t).filter (fun e => p.isPrefixOf e.1)).head?.map (·.2) :=
  firstPrefix_correct h p

example {t : Node α} (h : WF true t) (p : Key) :
    lastPrefix t p = ((entries t).filter (fun e => p.isPrefixOf e.1)).getLast?.map (·.2) :=
  lastPrefix_correct h p

/-! ### Writes (txn.go) -/

example {t : Node α} (h : WF true t) (k : Key) (x : α) : WF true (insert t k x).1 :=
  insert_wf h k x

example {t : Node α} (h : WF true t) (k : Key) (x : α) (k' : Key) :
    (entries (insert t k x).1).lookup k' = if k' = k then some x else (entries t).lookup k' :=
  insert_lookup h k x k'

example {t : Node α} (h : WF true t) (k : Key) (x : α) :
    (insert t k x).2 = (entries t).lookup k :=
  insert_old h k x

example {t : Node α} (h : WF true t) (k : Key) :
    delete true t k = none ↔ (entries t).lookup k = none :=
  delete_miss h k

example {t : Node α} (h : WF true t) (k : Key) (res : Option (Node α)) (x : α)
    (hd : delete true t k = some (res, x)) :
    (entries t).lookup k = some x ∧
      ∃ t', res = some t' ∧ WF true t' ∧ entries t' = (entries t).filter (fun e => e.1 != k) :=
  delete_hit h k res x hd

example {t : Node α} (h : WF true t) (p : Key) :
    deletePrefix true t p = none ↔ (p ≠ [] ∧ ∀ e ∈ entries t, p.isPrefixOf e.1 = false) :=
  deletePrefix_miss h p

example {t : Node α} (h : WF true t) (p : Key) (res : Option (Node α))
    (hd : deletePrefix true t p = some res) :
    ∃ t', res = some t' ∧ WF true t' ∧ entries t' = (entries t).filter (fun e => !p.isPrefixOf e.1) :=
  deletePrefix_hit h p res hd

/-! ### Iteration (iter.go) -/

example {t : Node α} (h : WF true t) (k : Key) (fuel : Nat) (hf : 4 * size t + 4 ≤ fuel) :
    run nextStep fuel (seekLowerBound t k []) =
      ((entries t).filter (fun e => !keyLt e.1 k)).map (fun e => some e.2) :=
  iter_lowerBound h k fuel hf

example {t : Node α} (h : WF true t) (p : Key) (fuel : Nat) (hf : 4 * size t + 4 ≤ fuel) :
    run nextStep fuel (seekPrefixFwd t p) =
      ((entries t).filter (fun e => p.isPrefixOf e.1)).map (fun e => some e.2) :=
  iter_prefix h p fuel hf

example {t : Node α} (h : WF true t) (k : Key) (fuel : Nat) (hf : 4 * size t + 4 ≤ fuel) :
    run prevStep fuel (seekReverseLowerBound t k []) =
      (((entries t).filter (fun e => !keyLt k e.1)).map (fun e => some e.2)).reverse :=
  iter_reverseLowerBound h k fuel hf

example {t : Node α} (h : WF true t) (p : Key) (fuel : Nat) (hf : 4 * size t + 4 ≤ fuel) :
    run prevStep fuel (seekPrefixRev t p) =
      (((entries t).filter (fun e => p.isPrefixOf e.1)).map (fun e => some e.2)).reverse :=
  iter_prefix_rev h p fuel hf

end Node

/-! ### The iterator's stack (iter.go): inline frames and a spill slice
behave as the list the iterator model uses, top first. -/

namespace Stack
variable {β : Type}

example {s : GoStack β} (hv : s.Valid) (f : β) : (s.push f).toList = f :: s.toList ∧ (s.push f).Valid :=
  ⟨toList_push hv f, push_valid hv f⟩
example {s : GoStack β} (hv : s.Valid) (hd : 0 < s.depth) : s.top = s.toList.head? :=
  toList_top hv hd
example {s : GoStack β} (hv : s.Valid) (hd : 0 < s.depth) (f : β) :
    (s.setTop f).toList = f :: s.toList.tail ∧ (s.setTop f).Valid :=
  ⟨toList_setTop hv hd f, setTop_valid hv f⟩
example {s : GoStack β} (hv : s.Valid) : s.pop.toList = s.toList.tail ∧ s.pop.Valid :=
  ⟨toList_pop hv, pop_valid hv⟩
example (s : GoStack β) : s.reset.toList = [] ∧ s.reset.Valid := ⟨toList_reset s, reset_valid s⟩

end Stack
end JuuriFormal

#print axioms JuuriFormal.Rank.goRank_correct
#print axioms JuuriFormal.Rank.addKid_consistent
#print axioms JuuriFormal.Rank.delKid_consistent
#print axioms JuuriFormal.Node.rankOf_eq_goRank
#print axioms JuuriFormal.Node.lookup_goHasPrefix_eq
#print axioms JuuriFormal.Node.entries_sorted
#print axioms JuuriFormal.Node.get_correct
#print axioms JuuriFormal.Node.longestPrefix_correct
#print axioms JuuriFormal.Node.firstPrefix_correct
#print axioms JuuriFormal.Node.lastPrefix_correct
#print axioms JuuriFormal.Node.insert_wf
#print axioms JuuriFormal.Node.insert_lookup
#print axioms JuuriFormal.Node.insert_old
#print axioms JuuriFormal.Node.delete_miss
#print axioms JuuriFormal.Node.delete_hit
#print axioms JuuriFormal.Node.deletePrefix_miss
#print axioms JuuriFormal.Node.deletePrefix_hit
#print axioms JuuriFormal.Node.iter_lowerBound
#print axioms JuuriFormal.Node.iter_prefix
#print axioms JuuriFormal.Node.iter_reverseLowerBound
#print axioms JuuriFormal.Node.iter_prefix_rev
#print axioms JuuriFormal.Stack.toList_push
#print axioms JuuriFormal.Stack.toList_top
#print axioms JuuriFormal.Stack.toList_setTop
#print axioms JuuriFormal.Stack.toList_pop
