/-
Copyright (c) 2026 Ville Vesilehto
SPDX-License-Identifier: MPL-2.0

The branch-free `rank` of internal/radix/node.go, against its specification.

A node with children keeps a 256-bit label bitmap in four 64-bit words and a
dense, label-ordered child array. `rank label` must return the number of
labels present below `label` (the child's index, or where it would be
inserted) and whether `label` itself is present. The Go code does this
without a label-dependent branch, with shift tricks that rely on Go's
definition of an over-wide shift:

```go
w := label >> 6
x := n.bitmap[w] << (^label & 63)
idx := bits.OnesCount64(x<<1) + bits.OnesCount64(n.bitmap[0]<<((w-1)&64))
for w > 1 {
	w--
	idx += bits.OnesCount64(n.bitmap[w])
}
return idx, x>>63 != 0
```

`goRank` below is that code, transcribed operation by operation: `label`,
`w` and the shift counts are `UInt8`s as in Go, and a `BitVec 64` shifted by
64 or more is zero, which is exactly Go's rule for unsigned shifts. The
theorem `goRank_correct` proves it equal to the specification for every
bitmap and every label.

The second half connects the bitmap to the child array: when the bitmap
holds exactly the labels of a strictly ascending child list, `rank` is the
position of the label in that list (or its insertion point), and `addKid` /
`delKid` keep the two in agreement.
-/

namespace JuuriFormal.Rank

abbrev Word := BitVec 64

/-- The label bitmap: word `i` holds labels `64*i .. 64*i+63`. -/
structure Bitmap where
  w : Fin 4 → Word

/-- `n.bitmap[i]`. The Go code only ever indexes words 0..3. -/
def Bitmap.word (bm : Bitmap) (i : Nat) : Word :=
  if h : i < 4 then bm.w ⟨i, h⟩ else 0

/-- `bits.OnesCount64`. -/
def popcount (x : Word) : Nat := (List.range 64).countP x.getLsbD

/-- Whether label `l` is present. -/
def Bitmap.test (bm : Bitmap) (l : Nat) : Bool := (bm.word (l / 64)).getLsbD (l % 64)

/-- The specification: the number of present labels below `label`. -/
def rankSpec (bm : Bitmap) (label : Nat) : Nat := (List.range label).countP bm.test

/-- `for w > 1 { w--; idx += bits.OnesCount64(n.bitmap[w]) }` -/
def loop (bm : Bitmap) : Nat → Nat → Nat
  | w + 2, idx => loop bm (w + 1) (idx + popcount (bm.word (w + 1)))
  | _, idx => idx

/-- Go's `rank` for a node that is not a compact leaf, transcribed. -/
def goRank (bm : Bitmap) (label : UInt8) : Nat × Bool :=
  let w : UInt8 := label >>> 6
  let x : Word := bm.word w.toNat <<< ((~~~label) &&& 63).toNat
  let idx := popcount (x <<< 1) + popcount (bm.word 0 <<< ((w - 1) &&& 64).toNat)
  (loop bm w.toNat idx, x >>> 63 != 0)

/-! ### Popcount of a shifted word -/

theorem popcount_shiftLeft (y : Word) (k : Nat) (hk : k ≤ 64) :
    popcount (y <<< k) = (List.range (64 - k)).countP y.getLsbD := by
  unfold popcount
  have hr : List.range 64 = List.range (k + (64 - k)) := by congr 1; omega
  rw [hr, List.range_add, List.countP_append, List.countP_map]
  have h0 : (List.range k).countP (y <<< k).getLsbD = 0 := by
    rw [List.countP_eq_zero]
    intro a ha
    simp [List.mem_range] at ha
    simp [BitVec.getLsbD_shiftLeft, ha]
  rw [h0, Nat.zero_add]
  apply List.countP_congr
  intro j hj
  simp [List.mem_range] at hj
  simp [BitVec.getLsbD_shiftLeft]
  intro _; omega

theorem popcount_zero : popcount 0#64 = 0 := by
  unfold popcount
  rw [List.countP_eq_zero]
  intro a _
  simp

theorem popcount_eq_countP (y : Word) : popcount y = (List.range 64).countP y.getLsbD := rfl

/-! ### The specification, word by word -/

theorem rankSpec_add (bm : Bitmap) (n m : Nat) :
    rankSpec bm (n + m) = rankSpec bm n + (List.range m).countP (fun i => bm.test (n + i)) := by
  unfold rankSpec
  rw [List.range_add, List.countP_append, List.countP_map]
  rfl

theorem test_word (bm : Bitmap) (j i : Nat) (hi : i < 64) :
    bm.test (64 * j + i) = (bm.word j).getLsbD i := by
  unfold Bitmap.test
  have h1 : (64 * j + i) / 64 = j := by omega
  have h2 : (64 * j + i) % 64 = i := by omega
  rw [h1, h2]

theorem rankSpec_word (bm : Bitmap) (j b : Nat) (hb : b ≤ 64) :
    rankSpec bm (64 * j + b) = rankSpec bm (64 * j) + (List.range b).countP (bm.word j).getLsbD := by
  rw [rankSpec_add]
  congr 1
  apply List.countP_congr
  intro i hi
  simp [List.mem_range] at hi
  rw [test_word bm j i (by omega)]

theorem rankSpec_succ_word (bm : Bitmap) (j : Nat) :
    rankSpec bm (64 * (j + 1)) = rankSpec bm (64 * j) + popcount (bm.word j) := by
  have := rankSpec_word bm j 64 (by omega)
  rw [show 64 * (j + 1) = 64 * j + 64 by omega, this]
  rfl

theorem rankSpec_zero (bm : Bitmap) : rankSpec bm 0 = 0 := rfl

/-! ### The Go arithmetic on the label -/

theorem label_word (label : UInt8) : (label >>> 6).toNat = label.toNat / 64 := by
  rw [UInt8.toNat_shiftRight]
  have : (6 : UInt8).toNat % 8 = 6 := by decide
  rw [this, Nat.shiftRight_eq_div_pow]

theorem label_shift (label : UInt8) : ((~~~label) &&& 63).toNat = 63 - label.toNat % 64 := by
  rw [UInt8.toNat_and, UInt8.toNat_not]
  have hl := label.toNat_lt
  have h63 : (63 : UInt8).toNat = 2 ^ 6 - 1 := by decide
  rw [h63, Nat.and_two_pow_sub_one_eq_mod]
  simp [UInt8.size] at *
  omega

/-- `(w-1)&64` in byte arithmetic: 64 when `w` is 0, else 0. -/
theorem first_shift (label : UInt8) :
    ((label >>> 6 - 1) &&& 64).toNat = if label.toNat / 64 = 0 then 64 else 0 := by
  have hw := label_word label
  have hl := label.toNat_lt
  have hcases : label.toNat / 64 = 0 ∨ label.toNat / 64 = 1 ∨ label.toNat / 64 = 2 ∨
      label.toNat / 64 = 3 := by omega
  rcases hcases with h | h | h | h <;>
  · have : label >>> 6 = UInt8.ofNat (label.toNat / 64) := by
      apply UInt8.toNat_inj.mp; rw [hw]; simp; omega
    rw [this, h]; decide

theorem top_bit (x : Word) : (x >>> 63 != 0) = x.getLsbD 63 := by
  have hx := x.isLt
  have h1 : (x >>> 63 != 0) = decide (x.toNat >>> 63 ≠ 0) := by
    cases h : (x >>> 63 != 0) <;> simp_all [BitVec.toNat_eq, BitVec.toNat_ushiftRight]
  rw [h1, BitVec.getLsbD, Nat.testBit]
  have : x.toNat >>> 63 < 2 := by
    rw [Nat.shiftRight_eq_div_pow]; simp at hx ⊢; omega
  have h2 : 1 &&& x.toNat >>> 63 = x.toNat >>> 63 := by
    rw [Nat.and_comm, Nat.and_one_is_mod]; omega
  rw [h2]
  cases h : (x.toNat >>> 63 != 0) <;> simp_all

/-! ### Correctness -/

theorem goRank_found (bm : Bitmap) (label : UInt8) :
    (goRank bm label).2 = bm.test label.toNat := by
  simp only [goRank]
  rw [top_bit, BitVec.getLsbD_shiftLeft, label_shift, label_word]
  unfold Bitmap.test
  have hb : label.toNat % 64 < 64 := Nat.mod_lt _ (by decide)
  have : 63 - (63 - label.toNat % 64) = label.toNat % 64 := by omega
  simp [this]

theorem goRank_index (bm : Bitmap) (label : UInt8) :
    (goRank bm label).1 = rankSpec bm label.toNat := by
  simp only [goRank]
  rw [label_word, label_shift, first_shift, ← BitVec.shiftLeft_add]
  have hl := label.toNat_lt
  have hb : label.toNat % 64 < 64 := Nat.mod_lt _ (by decide)
  have hsplit : label.toNat = 64 * (label.toNat / 64) + label.toNat % 64 := by omega
  rw [popcount_shiftLeft _ _ (by omega)]
  rw [show 64 - (63 - label.toNat % 64 + 1) = label.toNat % 64 by omega]
  conv => rhs; rw [hsplit]
  rw [rankSpec_word _ _ _ (by omega)]
  have hcases : label.toNat / 64 = 0 ∨ label.toNat / 64 = 1 ∨ label.toNat / 64 = 2 ∨
      label.toNat / 64 = 3 := by omega
  rcases hcases with h | h | h | h <;> rw [h] <;> simp only [loop]
  · simp [rankSpec_zero, popcount_zero]
  · have := rankSpec_succ_word bm 0
    simp at this ⊢
    rw [this, rankSpec_zero]; omega
  · have h1 := rankSpec_succ_word bm 0
    have h2 := rankSpec_succ_word bm 1
    simp at h1 h2 ⊢
    rw [h2, h1, rankSpec_zero]; omega
  · have h1 := rankSpec_succ_word bm 0
    have h2 := rankSpec_succ_word bm 1
    have h3 := rankSpec_succ_word bm 2
    simp at h1 h2 h3 ⊢
    rw [h3, h2, h1, rankSpec_zero]; omega

/-- **`rank` is correct**: for every bitmap and every label, the index is the
number of present labels below the label and the flag is the label's bit. -/
theorem goRank_correct (bm : Bitmap) (label : UInt8) :
    goRank bm label = (rankSpec bm label.toNat, bm.test label.toNat) := by
  rw [← goRank_index, ← goRank_found]

/-! ### The bitmap and the child array

A node's child array holds its children in ascending label order; the
bitmap has a bit for exactly those labels. -/

/-- The bitmap agrees with the (ascending) labels of the child array. -/
structure Consistent (bm : Bitmap) (labels : List Nat) : Prop where
  sorted : labels.Pairwise (· < ·)
  bound : ∀ l ∈ labels, l < 256
  bits : ∀ l, l < 256 → (bm.test l = true ↔ l ∈ labels)

theorem countP_or_disjoint {α : Type} (l : List α) (p q : α → Bool)
    (h : ∀ x ∈ l, ¬(p x = true ∧ q x = true)) :
    l.countP (fun x => p x || q x) = l.countP p + l.countP q := by
  induction l with
  | nil => rfl
  | cons a t ih =>
    simp only [List.countP_cons]
    rw [ih (fun x hx => h x (List.mem_cons_of_mem _ hx))]
    have ha := h a List.mem_cons_self
    cases hp : p a <;> cases hq : q a <;> simp_all <;> omega

/-- Counting the members of an ascending list below `n` two ways. -/
theorem countP_lt_eq (ls : List Nat) (hs : ls.Pairwise (· < ·)) (n : Nat) :
    ls.countP (fun x => decide (x < n)) = (List.range n).countP (fun x => decide (x ∈ ls)) := by
  induction ls with
  | nil => simp
  | cons a t ih =>
    rw [List.pairwise_cons] at hs
    rw [List.countP_cons, ih hs.2]
    have hsplit : (List.range n).countP (fun x => decide (x ∈ a :: t)) =
        (List.range n).countP (fun x => decide (x ∈ t) || decide (x = a)) := by
      apply List.countP_congr; intro x _; simp [or_comm]
    rw [hsplit, countP_or_disjoint]
    · congr 1
      have : (List.range n).countP (fun x => decide (x = a)) = (List.range n).count a := by
        rw [List.count_eq_countP]; apply List.countP_congr; intro x _; simp
      rw [this, List.count_range]
      by_cases han : a < n <;> simp [han]
    · intro x _ hx
      simp at hx
      have := hs.1 x hx.1
      omega

/-- With a consistent bitmap, the specification counts the children below. -/
theorem rankSpec_eq_countP {bm : Bitmap} {labels : List Nat} (h : Consistent bm labels)
    (n : Nat) (hn : n ≤ 256) : rankSpec bm n = labels.countP (fun x => decide (x < n)) := by
  rw [countP_lt_eq labels h.sorted n]
  apply List.countP_congr
  intro x hx
  simp [List.mem_range] at hx
  have := h.bits x (by omega)
  simp [this]

/-- In an ascending list, a member's index is the number of members below it. -/
theorem getElem_countP_lt (ls : List Nat) (hs : ls.Pairwise (· < ·)) (l : Nat) (hl : l ∈ ls) :
    ls[ls.countP (fun x => decide (x < l))]? = some l := by
  induction ls with
  | nil => simp at hl
  | cons a t ih =>
    rw [List.pairwise_cons] at hs
    rcases List.mem_cons.mp hl with rfl | ht
    · have : t.countP (fun x => decide (x < l)) = 0 := by
        rw [List.countP_eq_zero]; intro x hx; have := hs.1 x hx; simp; omega
      simp [this]
    · have hal : a < l := hs.1 l ht
      rw [List.countP_cons]
      simp [hal, ih hs.2 ht]

/-- **Lookup**: when `rank` finds the label, the child at the index it returns
carries that label. -/
theorem rank_hit {bm : Bitmap} {labels : List Nat} (h : Consistent bm labels) (l : UInt8)
    (hf : (goRank bm l).2 = true) : labels[(goRank bm l).1]? = some l.toNat := by
  rw [goRank_correct] at hf ⊢
  have hl := l.toNat_lt
  have hmem : l.toNat ∈ labels := (h.bits l.toNat (by simpa using hl)).mp hf
  rw [rankSpec_eq_countP h _ (by simp at hl; omega)]
  exact getElem_countP_lt labels h.sorted _ hmem

/-- **Miss**: when `rank` does not find the label, no child carries it, and
the index is the number of children with a smaller label. -/
theorem rank_miss {bm : Bitmap} {labels : List Nat} (h : Consistent bm labels) (l : UInt8)
    (hf : (goRank bm l).2 = false) :
    l.toNat ∉ labels ∧ (goRank bm l).1 = labels.countP (fun x => decide (x < l.toNat)) := by
  rw [goRank_correct] at hf ⊢
  have hl := l.toNat_lt
  constructor
  · intro hmem
    have := (h.bits l.toNat (by simpa using hl)).mpr hmem
    simp_all
  · exact rankSpec_eq_countP h _ (by simp at hl; omega)

/-! ### addKid and delKid -/

/-- `n.bitmap[label>>6] |= uint64(1) << (label & 63)` -/
def Bitmap.set (bm : Bitmap) (l : UInt8) : Bitmap :=
  ⟨fun i => if i.val = (l >>> 6).toNat then bm.w i ||| (1#64 <<< (l &&& 63).toNat) else bm.w i⟩

/-- `n.bitmap[label>>6] &^= uint64(1) << (label & 63)` -/
def Bitmap.clear (bm : Bitmap) (l : UInt8) : Bitmap :=
  ⟨fun i => if i.val = (l >>> 6).toNat then bm.w i &&& ~~~(1#64 <<< (l &&& 63).toNat) else bm.w i⟩

theorem label_bit (l : UInt8) : (l &&& 63).toNat = l.toNat % 64 := by
  rw [UInt8.toNat_and]
  have h63 : (63 : UInt8).toNat = 2 ^ 6 - 1 := by decide
  rw [h63, Nat.and_two_pow_sub_one_eq_mod]

theorem test_set (bm : Bitmap) (l : UInt8) (x : Nat) (hx : x < 256) :
    (bm.set l).test x = (bm.test x || decide (x = l.toNat)) := by
  have hl := l.toNat_lt
  simp only [Bitmap.test, Bitmap.word, Bitmap.set, label_word, label_bit]
  have hx4 : x / 64 < 4 := by omega
  simp only [hx4, dite_true]
  by_cases hw : x / 64 = l.toNat / 64
  · simp only [hw, ite_true, BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_one]
    have : x = l.toNat ↔ x % 64 = l.toNat % 64 := by omega
    by_cases hb : x % 64 = l.toNat % 64 <;> simp [hb, this] <;> omega
  · simp only [hw, ite_false]
    have : x ≠ l.toNat := by intro h; exact hw (by rw [h])
    simp [this]

theorem test_clear (bm : Bitmap) (l : UInt8) (x : Nat) (hx : x < 256) :
    (bm.clear l).test x = (bm.test x && !decide (x = l.toNat)) := by
  have hl := l.toNat_lt
  simp only [Bitmap.test, Bitmap.word, Bitmap.clear, label_word, label_bit]
  have hx4 : x / 64 < 4 := by omega
  simp only [hx4, dite_true]
  by_cases hw : x / 64 = l.toNat / 64
  · simp only [hw, ite_true, BitVec.getLsbD_and, BitVec.getLsbD_not, BitVec.getLsbD_shiftLeft,
      BitVec.getLsbD_one]
    have : x = l.toNat ↔ x % 64 = l.toNat % 64 := by omega
    by_cases hb : x % 64 = l.toNat % 64 <;> simp [hb, this] <;> omega
  · simp only [hw, ite_false]
    have : x ≠ l.toNat := by intro h; exact hw (by rw [h])
    simp [this]

theorem insertIdx_sorted (ls : List Nat) (hs : ls.Pairwise (· < ·)) (l : Nat) (hl : l ∉ ls) :
    (ls.insertIdx (ls.countP (fun x => decide (x < l))) l).Pairwise (· < ·) := by
  induction ls with
  | nil => simp
  | cons a t ih =>
    rw [List.pairwise_cons] at hs
    have hne : l ≠ a := fun h => hl (h ▸ List.mem_cons_self)
    have hlt : l ∉ t := fun h => hl (List.mem_cons_of_mem _ h)
    rw [List.countP_cons]
    by_cases hal : a < l
    · simp only [hal, decide_true, ite_true]
      rw [List.insertIdx_succ_cons, List.pairwise_cons]
      refine ⟨?_, ih hs.2 hlt⟩
      intro x hx
      have hle : t.countP (fun x => decide (x < l)) ≤ t.length := List.countP_le_length
      rcases (List.mem_insertIdx hle).mp hx with rfl | hx
      · exact hal
      · exact hs.1 x hx
    · have hla : l < a := by omega
      have : t.countP (fun x => decide (x < l)) = 0 := by
        rw [List.countP_eq_zero]; intro x hx; have := hs.1 x hx; simp; omega
      simp only [hal, decide_false, this, Bool.false_eq_true, ite_false, Nat.add_zero,
        List.insertIdx_zero]
      rw [List.pairwise_cons, List.pairwise_cons]
      refine ⟨?_, hs.1, hs.2⟩
      intro x hx
      rcases List.mem_cons.mp hx with rfl | hx
      · exact hla
      · exact Nat.lt_trans hla (hs.1 x hx)

/-- **addKid**: inserting a child with a new label at the position `rank`
returned, and setting its bit, keeps the bitmap and the child array in
agreement. -/
theorem addKid_consistent {bm : Bitmap} {labels : List Nat} (h : Consistent bm labels)
    (l : UInt8) (hf : (goRank bm l).2 = false) :
    Consistent (bm.set l) (labels.insertIdx (goRank bm l).1 l.toNat) := by
  obtain ⟨hnot, hidx⟩ := rank_miss h l hf
  rw [hidx]
  have hl := l.toNat_lt
  have hle : labels.countP (fun x => decide (x < l.toNat)) ≤ labels.length := List.countP_le_length
  refine ⟨insertIdx_sorted labels h.sorted _ hnot, ?_, ?_⟩
  · intro x hx
    rcases (List.mem_insertIdx hle).mp hx with rfl | hx
    · simpa using hl
    · exact h.bound x hx
  · intro x hx
    rw [test_set bm l x hx, List.mem_insertIdx hle]
    have := h.bits x hx
    cases hb : bm.test x <;> simp_all [or_comm]

/-- **delKid**: removing the child at an index and clearing its bit keeps the
bitmap and the child array in agreement. -/
theorem delKid_consistent {bm : Bitmap} {labels : List Nat} (h : Consistent bm labels)
    (idx : Nat) (hidx : idx < labels.length) (l : UInt8) (hl : labels[idx] = l.toNat) :
    Consistent (bm.clear l) (labels.eraseIdx idx) := by
  have hsub := List.eraseIdx_sublist labels idx
  refine ⟨h.sorted.sublist hsub, fun x hx => h.bound x (hsub.subset hx), ?_⟩
  intro x hx
  rw [test_clear bm l x hx, List.mem_eraseIdx_iff_getElem]
  have hb := h.bits x hx
  have hnd : labels.Nodup := h.sorted.imp (fun h => Nat.ne_of_lt h)
  constructor
  · intro ht
    simp at ht
    obtain ⟨hmem, hne⟩ := ht
    obtain ⟨i, hi, hix⟩ := List.getElem_of_mem (hb.mp hmem)
    refine ⟨i, hi, ?_, hix⟩
    intro hieq
    subst hieq
    exact hne (hix ▸ hl)
  · rintro ⟨i, hi, hne, hix⟩
    have hmem : x ∈ labels := hix ▸ List.getElem_mem hi
    simp [hb.mpr hmem]
    intro hxl
    apply hne
    rw [← hl] at hxl
    rw [← hix] at hxl
    exact (List.Nodup.getElem_inj hnd).mp hxl

end JuuriFormal.Rank
