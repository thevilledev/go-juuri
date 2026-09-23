/-
Copyright (c) 2026 Ville Vesilehto
SPDX-License-Identifier: MPL-2.0

The key order, and the first property of the tree: a well-formed tree lists
its entries in strictly ascending key order. That makes `entries` a finite
map (no key twice) and the order every iterator must follow.
-/
import JuuriFormal.Tree

namespace JuuriFormal
namespace Node

variable {α : Type}

/-! ### The key order -/

@[simp] theorem keyLt_nil_nil : keyLt [] [] = false := rfl
@[simp] theorem keyLt_nil_cons (b : Nat) (bs : Key) : keyLt [] (b :: bs) = true := rfl
@[simp] theorem keyLt_cons_nil (a : Nat) (as : Key) : keyLt (a :: as) [] = false := rfl
theorem keyLt_cons_cons (a b : Nat) (as bs : Key) :
    keyLt (a :: as) (b :: bs) = (decide (a < b) || (decide (a = b) && keyLt as bs)) := rfl

@[simp] theorem keyLt_irrefl (a : Key) : keyLt a a = false := by
  induction a with
  | nil => rfl
  | cons x xs ih => simp [keyLt_cons_cons, ih]

theorem keyLt_trans {a b c : Key} (h1 : keyLt a b = true) (h2 : keyLt b c = true) :
    keyLt a c = true := by
  induction a generalizing b c with
  | nil =>
    cases b with
    | nil => simp at h1
    | cons y ys => cases c with
      | nil => simp at h2
      | cons z zs => rfl
  | cons x xs ih =>
    cases b with
    | nil => simp at h1
    | cons y ys =>
      cases c with
      | nil => simp at h2
      | cons z zs =>
        simp only [keyLt_cons_cons, Bool.or_eq_true, decide_eq_true_eq, Bool.and_eq_true] at *
        rcases h1 with h1 | ⟨rfl, h1⟩ <;> rcases h2 with h2 | ⟨rfl, h2⟩
        · left; omega
        · left; omega
        · left; omega
        · right; exact ⟨rfl, ih h1 h2⟩

theorem keyLt_asymm {a b : Key} (h : keyLt a b = true) : keyLt b a = false := by
  cases h' : keyLt b a
  · rfl
  · have := keyLt_trans h h'; simp at this

theorem keyLt_total {a b : Key} (h : a ≠ b) : keyLt a b = true ∨ keyLt b a = true := by
  induction a generalizing b with
  | nil => cases b with
    | nil => exact absurd rfl h
    | cons y ys => left; rfl
  | cons x xs ih => cases b with
    | nil => right; rfl
    | cons y ys =>
      simp only [keyLt_cons_cons, Bool.or_eq_true, decide_eq_true_eq, Bool.and_eq_true]
      by_cases hxy : x = y
      · subst hxy
        have : xs ≠ ys := fun e => h (e ▸ rfl)
        rcases ih this with h' | h'
        · left; right; exact ⟨rfl, h'⟩
        · right; right; exact ⟨rfl, h'⟩
      · rcases Nat.lt_or_gt_of_ne hxy with h' | h'
        · left; left; exact h'
        · right; left; exact h'

/-- Neither below the other: equal. -/
theorem keyLt_eq_of_not {a b : Key} (h1 : keyLt a b = false) (h2 : keyLt b a = false) : a = b := by
  by_cases h : a = b
  · exact h
  · rcases keyLt_total h with h' | h' <;> simp_all

@[simp] theorem keyLt_append_left (p a b : Key) : keyLt (p ++ a) (p ++ b) = keyLt a b := by
  induction p with
  | nil => rfl
  | cons x xs ih => simp [keyLt_cons_cons, ih]

theorem keyLt_prefix (p x : Key) (hx : x ≠ []) : keyLt p (p ++ x) = true := by
  have := keyLt_append_left p [] x
  rw [List.append_nil] at this
  rw [this]
  cases x with
  | nil => exact absurd rfl hx
  | cons _ _ => rfl

theorem keyLt_of_head_lt {a b : Nat} {x y : Key} (h : a < b) : keyLt (a :: x) (b :: y) = true := by
  simp [keyLt_cons_cons, h]

/-! ### Children -/

/-- The entries of `n` as its parent sees them: prefixed with `n`'s segment. -/
def fullEntries (n : Node α) : List (Key × α) := (entries n).map (fun e => (n.seg ++ e.1, e.2))

theorem entries_mk (s : Key) (v : Option α) (kids : List (Node α)) :
    entries (mk s v kids) = (v.map (fun x => ([], x))).toList ++ kids.flatMap fullEntries := by
  rw [entries]; rfl

theorem WF.seg_ne_nil {n : Node α} (h : WF false n) : n.seg ≠ [] := by
  cases h with
  | mk _ h2 _ _ => exact (h2 rfl).1

theorem WF.kids_wf {r : Bool} {n : Node α} (h : WF r n) : ∀ c ∈ n.kids, WF false c := by
  cases h with
  | mk _ _ _ h4 => exact h4

theorem WF.kids_sorted {r : Bool} {n : Node α} (h : WF r n) : (n.kids.map lbl).Pairwise (· < ·) := by
  cases h with
  | mk _ _ h3 _ => exact h3

theorem WF.root_seg {n : Node α} (h : WF true n) : n.seg = [] := by
  cases h with
  | mk h1 _ _ _ => exact h1 rfl

theorem lbl_of_seg {n : Node α} {b : Nat} {bs : Key} (h : n.seg = b :: bs) : n.lbl = b := by
  simp [lbl, h]

/-- Every key a child contributes starts with the child's label. -/
theorem fullEntries_head {c : Node α} (hc : c.seg ≠ []) :
    ∀ e ∈ fullEntries c, ∃ rest, e.1 = c.lbl :: rest := by
  intro e he
  simp only [fullEntries, List.mem_map] at he
  obtain ⟨e', _, rfl⟩ := he
  cases h : c.seg with
  | nil => exact absurd h hc
  | cons b bs => exact ⟨bs ++ e'.1, by simp [lbl, h]⟩

/-! ### Entries are sorted -/

/-- The keys of a list of entries, strictly ascending. -/
def Sorted (l : List (Key × α)) : Prop := l.Pairwise (fun a b => keyLt a.1 b.1 = true)

theorem sorted_fullEntries {c : Node α} (h : Sorted (entries c)) : Sorted (fullEntries c) := by
  unfold Sorted fullEntries at *
  rw [List.pairwise_map]
  refine h.imp ?_
  intro a b hab
  simpa using hab

/-- **The entries of a well-formed tree are strictly ascending.** -/
theorem entries_sorted {r : Bool} {n : Node α} (h : WF r n) : Sorted (entries n) := by
  induction h with
  | @mk isRoot s v kids _ _ hsorted hkids ih =>
    unfold Sorted
    rw [entries_mk, List.pairwise_append]
    refine ⟨?_, ?_, ?_⟩
    · cases v <;> simp
    · rw [List.pairwise_flatMap]
      refine ⟨fun c hc => sorted_fullEntries (ih c hc), ?_⟩
      rw [List.pairwise_map] at hsorted
      refine List.Pairwise.imp_of_mem ?_ hsorted
      intro c1 c2 hc1 hc2 hlt x hx y hy
      obtain ⟨r1, hr1⟩ := fullEntries_head (hkids c1 hc1).seg_ne_nil x hx
      obtain ⟨r2, hr2⟩ := fullEntries_head (hkids c2 hc2).seg_ne_nil y hy
      rw [hr1, hr2]
      exact keyLt_of_head_lt hlt
    · intro a ha b hb
      cases v with
      | none => simp at ha
      | some x =>
        simp at ha
        subst ha
        obtain ⟨c, hc, hbc⟩ := List.mem_flatMap.mp hb
        obtain ⟨r2, hr2⟩ := fullEntries_head (hkids c hc).seg_ne_nil b hbc
        simp [hr2]

/-- A sorted list has each key at most once. -/
theorem Sorted.nodup_keys {l : List (Key × α)} (h : Sorted l) : (l.map (·.1)).Nodup := by
  unfold Sorted at h
  rw [List.Nodup, List.pairwise_map]
  refine h.imp ?_
  intro a b hab heq
  rw [heq] at hab
  simp at hab

end Node
end JuuriFormal
