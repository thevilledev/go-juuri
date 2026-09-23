/-
Copyright (c) 2026 Ville Vesilehto
SPDX-License-Identifier: MPL-2.0

The forward iterator (iter.go: `Iterator.Next`, `SeekLowerBound`,
`SeekPrefixWatch`, `pushSubtree`): drained after a seek, it emits exactly the
values of the keys at or above the bound (or with the prefix), in ascending
key order, never faults, and stops within `4 * size t + 4` steps.

The proof assigns every stack the output it still owes (`iter_stackOut`):
a frame `(n, -1)` or `(n, leafOnly)` owes everything at and below `n`, a
frame `(n, i)` with `i ≥ 0` owes the children from `i` on, top frame first.
One step of `Next` on a reachable stack (`iter_good`) either emits the head of
that output or rearranges the stack without changing it, and lowers a weight
(`iter_mu`) that a seek starts at no more than `3 * size t`.
-/
import JuuriFormal.Order

namespace JuuriFormal
namespace Node

variable {α : Type}

/-! ### What a stack still owes -/

/-- The values of a list of entries, as the iterator reports them. -/
private def iter_outOf (l : List (Key × α)) : List (Option α) := l.map (fun e => some e.2)

/-- The values stored at and below `n`, in key order. -/
private def iter_vals (n : Node α) : List (Option α) := iter_outOf (entries n)

/-- What one forward frame still owes. -/
private def iter_frameOut (f : Node α × Int) : List (Option α) :=
  if f.2 < 0 then iter_vals f.1 else (f.1.kids.drop f.2.toNat).flatMap iter_vals

/-- What a forward stack still owes, top frame first. -/
private def iter_stackOut (s : Stack α) : List (Option α) := s.flatMap iter_frameOut

/-- A frame the forward iterator can meet: its node is well formed (the root
or below it); a `leafOnly` frame is a childless node with a value, any other
frame is `-1` or a child index, on a node with children. -/
private def iter_goodFrame (f : Node α × Int) : Prop :=
  (∃ r, WF r f.1) ∧
    ((f.2 = leafOnly ∧ f.1.kids = [] ∧ f.1.val.isSome = true) ∨ (-1 ≤ f.2 ∧ f.1.kids ≠ []))

private def iter_good (s : Stack α) : Prop := ∀ f ∈ s, iter_goodFrame f

/-- The weight of a frame: an upper bound on the steps it still takes. -/
private def iter_fw (f : Node α × Int) : Nat :=
  if f.2 < 0 then 2 + 3 * (f.1.kids.map size).sum
  else 1 + 3 * ((f.1.kids.drop f.2.toNat).map size).sum

private def iter_mu (s : Stack α) : Nat := (s.map iter_fw).sum

/-! ### Basic facts -/

private theorem iter_outOf_append (a b : List (Key × α)) :
    iter_outOf (a ++ b) = iter_outOf a ++ iter_outOf b := by
  simp [iter_outOf]

private theorem iter_outOf_map_key (f : Key → Key) (l : List (Key × α)) :
    iter_outOf (l.map (fun e => (f e.1, e.2))) = iter_outOf l := by
  simp [iter_outOf, Function.comp_def]

private theorem iter_outOf_fullEntries (c : Node α) : iter_outOf (fullEntries c) = iter_vals c := by
  simp [fullEntries, iter_vals, iter_outOf_map_key]

private theorem iter_vals_mk (s : Key) (v : Option α) (kids : List (Node α)) :
    iter_vals (mk s v kids) = v.toList.map some ++ kids.flatMap iter_vals := by
  rw [iter_vals, entries_mk, iter_outOf_append]
  congr 1
  · cases v <;> rfl
  · simp only [iter_outOf, List.map_flatMap]
    congr 1
    funext c
    exact iter_outOf_fullEntries c

private theorem iter_stackOut_nil : iter_stackOut ([] : Stack α) = [] := rfl

private theorem iter_stackOut_cons (f : Node α × Int) (s : Stack α) :
    iter_stackOut (f :: s) = iter_frameOut f ++ iter_stackOut s := by
  simp [iter_stackOut]

private theorem iter_mu_cons (f : Node α × Int) (s : Stack α) :
    iter_mu (f :: s) = iter_fw f + iter_mu s := by
  simp [iter_mu]

private theorem iter_fw_pos (f : Node α × Int) : 1 ≤ iter_fw f := by
  unfold iter_fw; split <;> omega

private theorem iter_good_cons {f : Node α × Int} {s : Stack α} :
    iter_good (f :: s) ↔ iter_goodFrame f ∧ iter_good s := by
  simp [iter_good]

private theorem iter_size_mk (s : Key) (v : Option α) (kids : List (Node α)) :
    size (mk s v kids) = 1 + (kids.map size).sum := by
  rw [size]

private theorem iter_size_pos (n : Node α) : 1 ≤ size n := by
  cases n; rw [iter_size_mk]; omega

private theorem iter_sum_split (l : List (Node α)) (k : Nat) :
    (l.map size).sum = ((l.take k).map size).sum + ((l.drop k).map size).sum := by
  rw [← List.sum_append, ← List.map_append, List.take_append_drop]

private theorem iter_sum_drop_le (l : List (Node α)) (k : Nat) :
    ((l.drop k).map size).sum ≤ (l.map size).sum := by
  have := iter_sum_split l k
  omega

private theorem iter_le_sum_of_mem {l : List Nat} {x : Nat} (h : x ∈ l) : x ≤ l.sum := by
  induction l with
  | nil => simp at h
  | cons y ys ih =>
    rw [List.sum_cons]
    rcases List.mem_cons.mp h with rfl | h
    · omega
    · have := ih h; omega

private theorem iter_size_lt_of_mem {c : Node α} {s : Key} {v : Option α} {kids : List (Node α)}
    (h : c ∈ kids) : size c < size (mk s v kids) := by
  rw [iter_size_mk]
  have : size c ≤ (kids.map size).sum := iter_le_sum_of_mem (List.mem_map_of_mem h)
  omega

/-- The value of a childless well-formed node below the root. -/
private theorem iter_childless_val {c : Node α} (h : WF false c) (hk : c.kids = []) :
    ∃ y, c.val = some y := by
  cases h with
  | @mk _ s v kids _ h2 _ _ =>
    simp at hk
    cases v with
    | none => have := (h2 rfl).2 rfl; simp [hk] at this
    | some y => exact ⟨y, rfl⟩

private theorem iter_getKid_some {kids : List (Node α)} {i : Nat} {c : Node α} {h : c ∈ kids}
    (hk : getKid kids i = some ⟨c, h⟩) : kids[i]? = some c := by
  unfold getKid at hk
  split at hk
  · simp at hk
  · rename_i c' hc'
    simp at hk
    rw [hc', hk]

private theorem iter_getKid_none {kids : List (Node α)} {i : Nat}
    (hk : getKid kids i = none) : kids[i]? = none := by
  unfold getKid at hk
  split at hk
  · assumption
  · simp at hk

/-! ### Pushing a subtree -/

private theorem iter_pushSubtree_out (n : Node α) (s : Stack α) :
    iter_stackOut (pushSubtree n s) = iter_vals n ++ iter_stackOut s := by
  obtain ⟨seg, v, kids⟩ := n
  unfold pushSubtree
  cases kids with
  | nil =>
    cases v with
    | none => simp [iter_vals_mk]
    | some x => simp [iter_stackOut_cons, iter_frameOut, leafOnly]
  | cons k ks => simp [iter_stackOut_cons, iter_frameOut]

private theorem iter_pushSubtree_good {r : Bool} {n : Node α} (h : WF r n) {s : Stack α}
    (hs : iter_good s) : iter_good (pushSubtree n s) := by
  unfold pushSubtree
  split
  · rename_i hk
    refine iter_good_cons.mpr ⟨⟨⟨r, h⟩, Or.inr ⟨Int.le_refl _, ?_⟩⟩, hs⟩
    simpa using hk
  · split
    · rename_i hk hv
      refine iter_good_cons.mpr ⟨⟨⟨r, h⟩, Or.inl ⟨rfl, ?_, hv⟩⟩, hs⟩
      simpa using hk
    · exact hs

private theorem iter_pushSubtree_mu (n : Node α) (s : Stack α) :
    iter_mu (pushSubtree n s) ≤ 3 * size n + iter_mu s := by
  obtain ⟨seg, v, kids⟩ := n
  unfold pushSubtree
  rw [iter_size_mk]
  split
  · simp [iter_mu_cons, iter_fw]; omega
  · split
    · simp [iter_mu_cons, iter_fw, leafOnly]; omega
    · omega

/-! ### One step of `Next` -/

/-- The scanning branch of `nextStep`: past the own value, at child `k`. -/
private theorem iter_nextStep_scan (n : Node α) (i : Int) (s : Stack α) (k : Nat)
    (h1 : i ≠ leafOnly) (h2 : ¬ (i < 0 ∧ n.val.isSome = true)) (h3 : n.kids ≠ [])
    (hk : (if i < 0 then 0 else i) = (k : Int)) :
    nextStep ((n, i) :: s) =
      match n.kids[k]? with
      | none => .cont s
      | some c =>
        if c.kids.isEmpty then .emit c.val ((n, (k : Int) + 1) :: s)
        else .cont ((c, -1) :: (n, (k : Int) + 1) :: s) := by
  have h3' : n.kids.isEmpty = false := by simpa using h3
  simp only [nextStep, h1, h2, h3', ite_false, Bool.false_eq_true]
  rw [hk]
  rfl

private theorem iter_step (n : Node α) (i : Int) (s : Stack α) (hg : iter_good ((n, i) :: s)) :
    (∃ v s', nextStep ((n, i) :: s) = .emit (some v) s' ∧ iter_good s' ∧
      iter_stackOut ((n, i) :: s) = some v :: iter_stackOut s' ∧
      iter_mu s' < iter_mu ((n, i) :: s)) ∨
    (∃ s', nextStep ((n, i) :: s) = .cont s' ∧ iter_good s' ∧
      iter_stackOut s' = iter_stackOut ((n, i) :: s) ∧
      iter_mu s' < iter_mu ((n, i) :: s)) := by
  obtain ⟨⟨⟨r, hwf⟩, hf⟩, hs⟩ := iter_good_cons.mp hg
  obtain ⟨seg, v, kids⟩ := n
  simp only at hf hwf
  rcases hf with ⟨hi, hk, hv⟩ | ⟨hi, hk⟩
  · -- leafOnly: emit the value and drop the frame
    subst hi hk
    obtain ⟨x, rfl⟩ := Option.isSome_iff_exists.mp hv
    left
    refine ⟨x, s, ?_, hs, ?_, ?_⟩
    · simp [nextStep]
    · simp [iter_stackOut_cons, iter_frameOut, leafOnly, iter_vals_mk]
    · rw [iter_mu_cons]; have := iter_fw_pos ((mk seg (some x) [], leafOnly) : Node α × Int); omega
  · have hne : i ≠ leafOnly := by unfold leafOnly; omega
    by_cases hown : i < 0 ∧ (mk seg v kids).val.isSome = true
    · -- the own value
      obtain ⟨hneg, hv⟩ := hown
      simp only [val_mk] at hv
      obtain ⟨x, rfl⟩ := Option.isSome_iff_exists.mp hv
      left
      refine ⟨x, (mk seg (some x) kids, 0) :: s, ?_, ?_, ?_, ?_⟩
      · simp [nextStep, hne, hneg]
      · exact iter_good_cons.mpr ⟨⟨⟨r, hwf⟩, Or.inr ⟨by omega, hk⟩⟩, hs⟩
      · simp [iter_stackOut_cons, iter_frameOut, hneg, iter_vals_mk]
      · simp [iter_mu_cons, iter_fw, hneg]
    · -- scanning the children from position k
      obtain ⟨k, hkk⟩ : ∃ k : Nat, (if i < 0 then 0 else i) = (k : Int) := by
        split
        · exact ⟨0, rfl⟩
        · exact ⟨i.toNat, by omega⟩
      have hout : iter_frameOut (mk seg v kids, i) = (kids.drop k).flatMap iter_vals := by
        unfold iter_frameOut
        simp only
        split
        · rename_i hneg
          have hv : v = none := by
            cases v with
            | none => rfl
            | some _ => exact absurd ⟨hneg, rfl⟩ hown
          have : k = 0 := by simp [hneg] at hkk; omega
          subst hv this
          simp [iter_vals_mk]
        · rename_i hneg
          have : i.toNat = k := by simp [hneg] at hkk; omega
          simp [this]
      have hw : 1 + 3 * ((kids.drop k).map size).sum ≤ iter_fw (mk seg v kids, i) := by
        unfold iter_fw
        simp only
        simp only [kids_mk]
        split
        · rename_i hneg
          have := iter_sum_drop_le kids k
          omega
        · rename_i hneg
          have : i.toNat = k := by simp [hneg] at hkk; omega
          simp [this]
      have hstep := iter_nextStep_scan (mk seg v kids) i s k hne hown hk hkk
      simp only [kids_mk] at hstep
      cases hc : kids[k]? with
      | none =>
        rw [hc] at hstep
        right
        refine ⟨s, hstep, hs, ?_, ?_⟩
        · have : kids.drop k = [] := List.drop_eq_nil_of_le (List.getElem?_eq_none_iff.mp hc)
          rw [iter_stackOut_cons, hout, this]; simp
        · rw [iter_mu_cons]; omega
      | some c =>
        rw [hc] at hstep
        have hlt : k < kids.length := by
          rcases List.getElem?_eq_some_iff.mp hc with ⟨h, _⟩; exact h
        have hdrop : kids.drop k = c :: kids.drop (k + 1) := by
          rw [List.drop_eq_getElem_cons hlt]
          rcases List.getElem?_eq_some_iff.mp hc with ⟨_, h⟩
          rw [h]
        have hmem : c ∈ kids := List.mem_of_getElem? hc
        have hcwf : WF false c := hwf.kids_wf c hmem
        have hk1 : ((k : Int) + 1).toNat = k + 1 := by omega
        have hw' : iter_fw ((mk seg v kids, (k : Int) + 1) : Node α × Int) =
            1 + 3 * ((kids.drop (k + 1)).map size).sum := by
          simp [iter_fw, hk1]
          omega
        have hframe : iter_frameOut ((mk seg v kids, (k : Int) + 1) : Node α × Int) =
            (kids.drop (k + 1)).flatMap iter_vals := by
          simp [iter_frameOut, hk1]
          omega
        have hsz : ((kids.drop k).map size).sum = size c + ((kids.drop (k + 1)).map size).sum := by
          rw [hdrop]; simp
        have hgood1 : iter_goodFrame ((mk seg v kids, (k : Int) + 1) : Node α × Int) :=
          ⟨⟨r, hwf⟩, Or.inr ⟨by omega, hk⟩⟩
        by_cases hck : c.kids = []
        · obtain ⟨y, hy⟩ := iter_childless_val hcwf hck
          have hce : c.kids.isEmpty = true := by simp [hck]
          simp only [hce, ite_true, hy] at hstep
          left
          refine ⟨y, _, hstep, iter_good_cons.mpr ⟨hgood1, hs⟩, ?_, ?_⟩
          · obtain ⟨cs, cv, ck⟩ := c
            simp only [val_mk, kids_mk] at hy hck
            subst hy hck
            rw [iter_stackOut_cons, iter_stackOut_cons, hout, hframe, hdrop]
            simp [iter_vals_mk]
          · rw [iter_mu_cons, iter_mu_cons, hw']
            have := iter_size_pos c
            omega
        · have hce : c.kids.isEmpty = false := by simpa using hck
          simp only [hce, Bool.false_eq_true, ite_false] at hstep
          right
          refine ⟨_, hstep, ?_, ?_, ?_⟩
          · refine iter_good_cons.mpr ⟨⟨⟨false, hcwf⟩, Or.inr ⟨by omega, hck⟩⟩,
              iter_good_cons.mpr ⟨hgood1, hs⟩⟩
          · rw [iter_stackOut_cons, iter_stackOut_cons, iter_stackOut_cons, hout, hframe, hdrop]
            simp [iter_frameOut]
          · rw [iter_mu_cons, iter_mu_cons, iter_mu_cons, hw']
            obtain ⟨cs, cv, ck⟩ := c
            rw [iter_size_mk] at hsz
            have hc1 : iter_fw ((mk cs cv ck, -1) : Node α × Int) = 2 + 3 * (ck.map size).sum := by
              simp [iter_fw]
            rw [hc1]
            omega

/-- **Draining a reachable stack**: with enough fuel, the iterator emits exactly
what the stack owes, and never faults. -/
private theorem iter_run (fuel : Nat) : ∀ s : Stack α, iter_good s → iter_mu s ≤ fuel →
    run nextStep fuel s = iter_stackOut s := by
  induction fuel with
  | zero =>
    intro s _ hmu
    cases s with
    | nil => rfl
    | cons f s =>
      rw [iter_mu_cons] at hmu
      have := iter_fw_pos f
      omega
  | succ fuel ih =>
    intro s hs hmu
    cases s with
    | nil => simp [run, nextStep, iter_stackOut_nil]
    | cons f s =>
      obtain ⟨n, i⟩ := f
      rcases iter_step n i s hs with ⟨v, s', hst, hg', hout, hlt⟩ | ⟨s', hst, hg', hout, hlt⟩
      · simp only [run, hst]
        rw [hout, ih s' hg' (by omega)]
      · simp only [run, hst]
        rw [← hout, ih s' hg' (by omega)]

/-! ### `rank` on sorted children -/

/-- The children before the rank index have smaller labels, the rest at
least the byte. -/
private theorem iter_rank_split (l : List (Node α)) (b : Nat) (hs : (l.map lbl).Pairwise (· < ·)) :
    (∀ d ∈ l.take (rankOf l b).1, d.lbl < b) ∧ (∀ d ∈ l.drop (rankOf l b).1, b ≤ d.lbl) := by
  simp only [rankOf]
  induction l with
  | nil => simp
  | cons x xs ih =>
    rw [List.map_cons, List.pairwise_cons] at hs
    obtain ⟨hx, hxs⟩ := hs
    by_cases hxb : x.lbl < b
    · rw [List.countP_cons_of_pos (by simpa using hxb)]
      obtain ⟨ih1, ih2⟩ := ih hxs
      refine ⟨?_, ?_⟩
      · intro d hd
        rw [List.take_succ_cons] at hd
        rcases List.mem_cons.mp hd with rfl | hd
        · exact hxb
        · exact ih1 d hd
      · intro d hd
        rw [List.drop_succ_cons] at hd
        exact ih2 d hd
    · have h0 : xs.countP (fun c => decide (c.lbl < b)) = 0 := by
        rw [List.countP_eq_zero]
        intro d hd
        have := hx d.lbl (List.mem_map_of_mem hd)
        simp; omega
      rw [List.countP_cons_of_neg (by simpa using hxb), h0]
      refine ⟨by simp, ?_⟩
      intro d hd
      simp only [List.drop_zero] at hd
      rcases List.mem_cons.mp hd with rfl | hd
      · omega
      · have := hx d.lbl (List.mem_map_of_mem hd); omega

/-- A found byte: the child at the rank index has it as its label, and every
later child a greater one. -/
private theorem iter_rank_found (l : List (Node α)) (b : Nat) (hs : (l.map lbl).Pairwise (· < ·))
    (hf : (rankOf l b).2 = true) :
    ∃ c, l[(rankOf l b).1]? = some c ∧ c.lbl = b ∧
      l.drop (rankOf l b).1 = c :: l.drop ((rankOf l b).1 + 1) ∧
      (∀ d ∈ l.drop ((rankOf l b).1 + 1), b < d.lbl) := by
  obtain ⟨h1, h2⟩ := iter_rank_split l b hs
  have hf' : ∃ c0 ∈ l, c0.lbl = b := by simpa [rankOf] using hf
  generalize (rankOf l b).1 = r at h1 h2 ⊢
  obtain ⟨c0, hc0, hc0b⟩ := hf'
  have hc0d : c0 ∈ l.drop r := by
    rw [← List.take_append_drop r l] at hc0
    rcases List.mem_append.mp hc0 with h | h
    · have := h1 c0 h; omega
    · exact h
  have hsd : ((l.drop r).map lbl).Pairwise (· < ·) := by rw [List.map_drop]; exact hs.drop
  cases hd : l.drop r with
  | nil => rw [hd] at hc0d; simp at hc0d
  | cons c rest =>
    have hget : l[r]? = some c := by rw [← List.head?_drop, hd]; rfl
    have hrest : l.drop (r + 1) = rest := by rw [← List.tail_drop, hd]; rfl
    rw [hd, List.map_cons, List.pairwise_cons] at hsd
    have hcb : b ≤ c.lbl := h2 c (by rw [hd]; simp)
    have hcl : c.lbl = b := by
      rw [hd] at hc0d
      rcases List.mem_cons.mp hc0d with rfl | h
      · exact hc0b
      · have := hsd.1 c0.lbl (List.mem_map_of_mem h); omega
    refine ⟨c, hget, hcl, by rw [hrest], ?_⟩
    rw [hrest]
    intro d hd'
    have := hsd.1 d.lbl (List.mem_map_of_mem hd'); omega

/-- A missing byte: every child from the rank index on has a greater label. -/
private theorem iter_rank_notfound (l : List (Node α)) (b : Nat) (hs : (l.map lbl).Pairwise (· < ·))
    (hf : ¬ (rankOf l b).2 = true) : ∀ d ∈ l.drop (rankOf l b).1, b < d.lbl := by
  intro d hd
  have := (iter_rank_split l b hs).2 d hd
  have hne : d.lbl ≠ b := by
    intro h; apply hf; simp only [rankOf, List.any_eq_true, decide_eq_true_eq]
    exact ⟨d, List.mem_of_mem_drop hd, h⟩
  omega

/-! ### Keys -/

private theorem iter_keys_lt {c : Node α} (hc : c.seg ≠ []) {b : Nat} (rest : Key)
    (h : c.lbl < b) : ∀ e ∈ fullEntries c, keyLt e.1 (b :: rest) = true := by
  intro e he
  obtain ⟨r, hr⟩ := fullEntries_head hc e he
  rw [hr]; exact keyLt_of_head_lt h

private theorem iter_keys_gt {c : Node α} (hc : c.seg ≠ []) {b : Nat} (rest : Key)
    (h : b < c.lbl) : ∀ e ∈ fullEntries c, keyLt e.1 (b :: rest) = false := by
  intro e he
  obtain ⟨r, hr⟩ := fullEntries_head hc e he
  rw [hr]; exact keyLt_asymm (keyLt_of_head_lt h)

private theorem iter_keys_noprefix {c : Node α} (hc : c.seg ≠ []) {b : Nat} (rest : Key)
    (h : c.lbl ≠ b) : ∀ e ∈ fullEntries c, (b :: rest).isPrefixOf e.1 = false := by
  intro e he
  obtain ⟨r, hr⟩ := fullEntries_head hc e he
  rw [hr]
  simp [List.isPrefixOf]
  intro h'; exact absurd h'.symm h

private theorem iter_lcp_nil_right (a : Key) : lcp a [] = 0 := by
  cases a <;> rfl

private theorem iter_lcp_le (a b : Key) : lcp a b ≤ b.length := by
  induction b generalizing a with
  | nil => rw [iter_lcp_nil_right]; simp
  | cons y ys ih =>
    cases a with
    | nil => exact Nat.zero_le _
    | cons x xs =>
      simp only [lcp]
      split
      · have := ih xs; simp; omega
      · exact Nat.zero_le _

/-- The search runs through the whole segment. -/
private theorem iter_lcp_eq (search seg : Key) (h : ¬ lcp search seg < seg.length) :
    search = seg ++ search.drop (lcp search seg) := by
  induction seg generalizing search with
  | nil => rw [iter_lcp_nil_right]; simp
  | cons y ys ih =>
    cases search with
    | nil => exact absurd (by show 0 < ys.length + 1; omega) h
    | cons x xs =>
      by_cases hxy : x = y
      · subst hxy
        simp only [lcp, ite_true, List.length_cons] at h ⊢
        have := ih xs (by omega)
        simp only [List.drop_succ_cons, List.cons_append]
        rw [← this]
      · simp only [lcp, hxy, ite_false, List.length_cons] at h
        omega

/-- The search leaves the segment at `lcp`: the subtree is entirely below the
key or entirely at or above it, decided by the diverging byte. -/
private theorem iter_keyLt_diverge (seg search x : Key) (hlt : lcp search seg < seg.length) :
    keyLt (seg ++ x) search = true ↔
      ¬ (lcp search seg = search.length ∨
          seg.getD (lcp search seg) 0 > search.getD (lcp search seg) 0) := by
  induction seg generalizing search with
  | nil => rw [iter_lcp_nil_right] at hlt; simp at hlt
  | cons y ys ih =>
    cases search with
    | nil => simp [lcp]
    | cons a as =>
      by_cases hay : a = y
      · subst hay
        simp only [lcp, ite_true, List.length_cons] at hlt ⊢
        simp only [List.cons_append, keyLt_cons_cons, Nat.lt_irrefl, decide_false, decide_true,
          Bool.true_and, Bool.false_or, List.getD_cons_succ]
        rw [ih as (by omega)]
        omega
      · simp only [lcp, hay, ite_false, List.length_cons, List.cons_append, keyLt_cons_cons,
          List.getD_cons_zero]
        have : y ≠ a := fun h => hay h.symm
        simp [this]
        omega

private theorem iter_keyLt_append_self (p x : Key) : keyLt (p ++ x) p = false := by
  have := keyLt_append_left p x []
  rw [List.append_nil] at this
  rw [this]
  cases x <;> rfl

private theorem iter_flatMap_congr {β γ : Type} {l : List β} {f g : β → List γ}
    (h : ∀ x ∈ l, f x = g x) : l.flatMap f = l.flatMap g := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
    rw [List.flatMap_cons, List.flatMap_cons, h x (by simp), ih (fun y hy => h y (by simp [hy]))]

/-! ### `SeekLowerBound` -/

/-- The values of the entries of a child at or above `b :: rest`. -/
private abbrev iter_lbOut (b : Nat) (rest : Key) (c : Node α) : List (Option α) :=
  iter_outOf ((fullEntries c).filter (fun e => !keyLt e.1 (b :: rest)))

private theorem iter_lb_kid_lt {d : Node α} (hd : WF false d) {b : Nat} (rest : Key)
    (h : d.lbl < b) : iter_lbOut b rest d = [] := by
  unfold iter_lbOut
  rw [List.filter_eq_nil_iff.mpr]
  · rfl
  · intro e he
    simp [iter_keys_lt hd.seg_ne_nil rest h e he]

private theorem iter_lb_kid_gt {d : Node α} (hd : WF false d) {b : Nat} (rest : Key)
    (h : b < d.lbl) : iter_lbOut b rest d = iter_vals d := by
  unfold iter_lbOut
  rw [List.filter_eq_self.mpr, iter_outOf_fullEntries]
  intro e he
  simp [iter_keys_gt hd.seg_ne_nil rest h e he]

private theorem iter_fullEntries_filter_lb (seg : Key) (v : Option α) (kids : List (Node α))
    (q : Key) :
    iter_outOf ((fullEntries (mk seg v kids)).filter (fun e => !keyLt e.1 (seg ++ q))) =
      iter_outOf ((entries (mk seg v kids)).filter (fun e => !keyLt e.1 q)) := by
  simp only [fullEntries, seg_mk, List.filter_map]
  rw [iter_outOf_map_key (fun k => seg ++ k)]
  congr 2
  funext e
  simp

private theorem iter_entries_filter_lb (seg : Key) (v : Option α) (kids : List (Node α))
    (b : Nat) (rest : Key) :
    iter_outOf ((entries (mk seg v kids)).filter (fun e => !keyLt e.1 (b :: rest))) =
      kids.flatMap (iter_lbOut b rest) := by
  rw [entries_mk, List.filter_append, List.filter_flatMap, iter_outOf_append]
  have : (List.filter (fun e => !keyLt e.1 (b :: rest)) (v.map (fun x => ([], x))).toList) = [] := by
    cases v <;> simp
  rw [this]
  simp only [iter_outOf, List.map_flatMap, List.map_nil, List.nil_append]
  rfl

private theorem iter_seekLB_out (n : Node α) (search : Key) (s : Stack α) : ∀ r, WF r n →
    iter_stackOut (seekLowerBound n search s) =
      iter_outOf ((fullEntries n).filter (fun e => !keyLt e.1 search)) ++ iter_stackOut s := by
  induction n, search, s using seekLowerBound.induct with
  | case1 seg v kids search s common hlt hc =>
    intro r hwf
    replace hlt : lcp search seg < seg.length := hlt
    replace hc : lcp search seg = search.length ∨
        seg.getD (lcp search seg) 0 > search.getD (lcp search seg) 0 := hc
    rw [seekLowerBound.eq_1, ite_eq_left hlt, ite_eq_left hc, iter_pushSubtree_out]
    congr 1
    rw [List.filter_eq_self.mpr, iter_outOf_fullEntries]
    intro e he
    simp only [fullEntries, List.mem_map, seg_mk] at he
    obtain ⟨e', _, rfl⟩ := he
    cases h : keyLt (seg ++ e'.1) search
    · rfl
    · exact absurd hc ((iter_keyLt_diverge seg search e'.1 hlt).mp h)
  | case2 seg v kids search s common hlt hc =>
    intro r hwf
    replace hlt : lcp search seg < seg.length := hlt
    replace hc : ¬ (lcp search seg = search.length ∨
        seg.getD (lcp search seg) 0 > search.getD (lcp search seg) 0) := hc
    rw [seekLowerBound.eq_1, ite_eq_left hlt, ite_eq_right hc]
    rw [List.filter_eq_nil_iff.mpr]
    · rfl
    · intro e he
      simp only [fullEntries, List.mem_map, seg_mk] at he
      obtain ⟨e', _, rfl⟩ := he
      simp [(iter_keyLt_diverge seg search e'.1 hlt).mpr hc]
  | case3 seg v kids search s common hlt hd =>
    intro r hwf
    replace hlt : ¬ lcp search seg < seg.length := hlt
    replace hd : search.drop (lcp search seg) = [] := hd
    have hse : search = seg := by
      have := iter_lcp_eq search seg hlt
      rw [hd, List.append_nil] at this
      exact this
    rw [seekLowerBound.eq_1, ite_eq_right hlt]
    simp only [hd]
    rw [iter_pushSubtree_out]
    congr 1
    rw [List.filter_eq_self.mpr, iter_outOf_fullEntries]
    intro e he
    simp only [fullEntries, List.mem_map, seg_mk] at he
    obtain ⟨e', _, rfl⟩ := he
    simp [hse, iter_keyLt_append_self]
  | case4 seg v kids search s common hlt b rest hd hf hgk =>
    intro r hwf
    obtain ⟨c, hc, -⟩ := iter_rank_found kids b hwf.kids_sorted hf
    rw [iter_getKid_none hgk] at hc
    cases hc
  | case5 seg v kids search s n common hlt b rest hd hf c hmem hgk ih =>
    intro r hwf
    replace hlt : ¬ lcp search seg < seg.length := hlt
    replace hd : search.drop (lcp search seg) = b :: rest := hd
    have hse : search = seg ++ b :: rest := by
      have := iter_lcp_eq search seg hlt
      rw [hd] at this
      exact this
    rw [seekLowerBound.eq_1, ite_eq_right hlt]
    simp only [hd, hf, hgk, ite_true]
    rw [ih false (hwf.kids_wf c hmem), iter_stackOut_cons]
    obtain ⟨c', hc', hlbl, hdrop, hgt⟩ := iter_rank_found kids b hwf.kids_sorted hf
    rw [iter_getKid_some hgk] at hc'
    cases hc'
    rw [hse, iter_fullEntries_filter_lb, iter_entries_filter_lb]
    have htake := (iter_rank_split kids b hwf.kids_sorted).1
    generalize (rankOf kids b).1 = k at hdrop hgt htake ⊢
    have hfr : iter_frameOut ((n, (k : Int) + 1) : Node α × Int) =
        (kids.drop (k + 1)).flatMap iter_vals := by
      show (if ((k : Int) + 1) < 0 then iter_vals (mk seg v kids)
        else ((mk seg v kids).kids.drop ((k : Int) + 1).toNat).flatMap iter_vals) = _
      rw [ite_eq_right (by omega)]
      simp only [kids_mk]
      congr 2
    have hsplit : kids.flatMap (iter_lbOut b rest) =
        (kids.take k).flatMap (iter_lbOut b rest) ++ (kids.drop k).flatMap (iter_lbOut b rest) := by
      rw [← List.flatMap_append, List.take_append_drop]
    have h1 : (kids.take k).flatMap (iter_lbOut b rest) = [] :=
      List.flatMap_eq_nil_iff.mpr (fun d hd => iter_lb_kid_lt
        (hwf.kids_wf d (List.mem_of_mem_take hd)) rest (htake d hd))
    have h2 : (kids.drop (k + 1)).flatMap (iter_lbOut b rest) =
        (kids.drop (k + 1)).flatMap iter_vals :=
      iter_flatMap_congr (fun d hd => iter_lb_kid_gt
        (hwf.kids_wf d (List.mem_of_mem_drop hd)) rest (hgt d hd))
    rw [hfr, hsplit, h1, hdrop, List.flatMap_cons, h2]
    simp
  | case6 seg v kids search s common hlt b rest hd hf hlen =>
    intro r hwf
    replace hlt : ¬ lcp search seg < seg.length := hlt
    replace hd : search.drop (lcp search seg) = b :: rest := hd
    have hse : search = seg ++ b :: rest := by
      have := iter_lcp_eq search seg hlt
      rw [hd] at this
      exact this
    rw [seekLowerBound.eq_1, ite_eq_right hlt]
    simp only [hd, hf, hlen, ite_true, Bool.false_eq_true, ite_false]
    rw [iter_stackOut_cons]
    rw [hse, iter_fullEntries_filter_lb, iter_entries_filter_lb]
    have htake := (iter_rank_split kids b hwf.kids_sorted).1
    have hgt := iter_rank_notfound kids b hwf.kids_sorted hf
    generalize (rankOf kids b).1 = k at hgt htake ⊢
    have hfr : iter_frameOut ((mk seg v kids, (k : Int)) : Node α × Int) =
        (kids.drop k).flatMap iter_vals := by
      simp only [iter_frameOut]
      rw [ite_eq_right (by omega)]
      simp
    have hsplit : kids.flatMap (iter_lbOut b rest) =
        (kids.take k).flatMap (iter_lbOut b rest) ++ (kids.drop k).flatMap (iter_lbOut b rest) := by
      rw [← List.flatMap_append, List.take_append_drop]
    have h1 : (kids.take k).flatMap (iter_lbOut b rest) = [] :=
      List.flatMap_eq_nil_iff.mpr (fun d hd => iter_lb_kid_lt
        (hwf.kids_wf d (List.mem_of_mem_take hd)) rest (htake d hd))
    have h2 : (kids.drop k).flatMap (iter_lbOut b rest) = (kids.drop k).flatMap iter_vals :=
      iter_flatMap_congr (fun d hd => iter_lb_kid_gt
        (hwf.kids_wf d (List.mem_of_mem_drop hd)) rest (hgt d hd))
    rw [hfr, hsplit, h1, h2]
    simp
  | case7 seg v kids search s common hlt b rest hd hf hlen =>
    intro r hwf
    replace hlt : ¬ lcp search seg < seg.length := hlt
    replace hd : search.drop (lcp search seg) = b :: rest := hd
    have hse : search = seg ++ b :: rest := by
      have := iter_lcp_eq search seg hlt
      rw [hd] at this
      exact this
    rw [seekLowerBound.eq_1, ite_eq_right hlt]
    simp only [hd, hf, hlen, Bool.false_eq_true, ite_false]
    rw [hse, iter_fullEntries_filter_lb, iter_entries_filter_lb]
    have htake := (iter_rank_split kids b hwf.kids_sorted).1
    rw [List.take_of_length_le (by omega)] at htake
    have h1 : kids.flatMap (iter_lbOut b rest) = [] :=
      List.flatMap_eq_nil_iff.mpr (fun d hd => iter_lb_kid_lt (hwf.kids_wf d hd) rest (htake d hd))
    rw [h1]
    simp

/-- The stack a lower-bound seek builds is reachable, and weighs at most three
per node of the tree on top of what it started from. -/
private theorem iter_seekLB_good (n : Node α) (search : Key) (s : Stack α) : ∀ r, WF r n →
    iter_good s →
    iter_good (seekLowerBound n search s) ∧ iter_mu (seekLowerBound n search s) ≤ 3 * size n + iter_mu s := by
  induction n, search, s using seekLowerBound.induct with
  | case1 seg v kids search s common hlt hc =>
    intro r hwf hs
    replace hlt : lcp search seg < seg.length := hlt
    replace hc : lcp search seg = search.length ∨
        seg.getD (lcp search seg) 0 > search.getD (lcp search seg) 0 := hc
    rw [seekLowerBound.eq_1, ite_eq_left hlt, ite_eq_left hc]
    exact ⟨iter_pushSubtree_good hwf hs, iter_pushSubtree_mu _ _⟩
  | case2 seg v kids search s common hlt hc =>
    intro r hwf hs
    replace hlt : lcp search seg < seg.length := hlt
    replace hc : ¬ (lcp search seg = search.length ∨
        seg.getD (lcp search seg) 0 > search.getD (lcp search seg) 0) := hc
    rw [seekLowerBound.eq_1, ite_eq_left hlt, ite_eq_right hc]
    exact ⟨hs, by omega⟩
  | case3 seg v kids search s common hlt hd =>
    intro r hwf hs
    replace hlt : ¬ lcp search seg < seg.length := hlt
    replace hd : search.drop (lcp search seg) = [] := hd
    rw [seekLowerBound.eq_1, ite_eq_right hlt]
    simp only [hd]
    exact ⟨iter_pushSubtree_good hwf hs, iter_pushSubtree_mu _ _⟩
  | case4 seg v kids search s common hlt b rest hd hf hgk =>
    intro r hwf
    obtain ⟨c, hc, -⟩ := iter_rank_found kids b hwf.kids_sorted hf
    rw [iter_getKid_none hgk] at hc
    cases hc
  | case5 seg v kids search s n common hlt b rest hd hf c hmem hgk ih =>
    intro r hwf hs
    replace hlt : ¬ lcp search seg < seg.length := hlt
    replace hd : search.drop (lcp search seg) = b :: rest := hd
    rw [seekLowerBound.eq_1, ite_eq_right hlt]
    simp only [hd, hf, hgk, ite_true]
    obtain ⟨c', hc', -, hdrop, -⟩ := iter_rank_found kids b hwf.kids_sorted hf
    rw [iter_getKid_some hgk] at hc'
    cases hc'
    have hne : kids ≠ [] := List.ne_nil_of_mem hmem
    have hsum := iter_sum_split kids (rankOf kids b).1
    have ⟨ihg, ihm⟩ := ih false (hwf.kids_wf c hmem)
      (iter_good_cons.mpr ⟨⟨⟨r, hwf⟩, Or.inr ⟨by omega, hne⟩⟩, hs⟩)
    generalize (rankOf kids b).1 = k at hdrop hsum ihg ihm ⊢
    refine ⟨ihg, ?_⟩
    have hfw : iter_fw ((n, (k : Int) + 1) : Node α × Int) =
        1 + 3 * ((kids.drop (k + 1)).map size).sum := by
      show (if ((k : Int) + 1) < 0 then 2 + 3 * ((mk seg v kids).kids.map size).sum
        else 1 + 3 * (((mk seg v kids).kids.drop ((k : Int) + 1).toNat).map size).sum) = _
      rw [ite_eq_right (by omega)]
      simp only [kids_mk]
      congr 4
    rw [iter_mu_cons, hfw] at ihm
    rw [hdrop] at hsum
    simp only [List.map_cons, List.sum_cons] at hsum
    change iter_mu (seekLowerBound c (b :: rest) ((n, (k : Int) + 1) :: s)) ≤
      3 * size (mk seg v kids) + iter_mu s
    rw [iter_size_mk]
    omega
  | case6 seg v kids search s common hlt b rest hd hf hlen =>
    intro r hwf hs
    replace hlt : ¬ lcp search seg < seg.length := hlt
    replace hd : search.drop (lcp search seg) = b :: rest := hd
    rw [seekLowerBound.eq_1, ite_eq_right hlt]
    simp only [hd, hf, hlen, Bool.false_eq_true, ite_true, ite_false]
    have hne : kids ≠ [] := by intro h; simp [h] at hlen
    refine ⟨iter_good_cons.mpr ⟨⟨⟨r, hwf⟩, Or.inr ⟨by omega, hne⟩⟩, hs⟩, ?_⟩
    have := iter_sum_drop_le kids (rankOf kids b).1
    rw [iter_mu_cons, iter_size_mk]
    simp only [iter_fw, kids_mk]
    rw [ite_eq_right (by omega)]
    simp only [Int.toNat_natCast]
    omega
  | case7 seg v kids search s common hlt b rest hd hf hlen =>
    intro r hwf hs
    replace hlt : ¬ lcp search seg < seg.length := hlt
    replace hd : search.drop (lcp search seg) = b :: rest := hd
    rw [seekLowerBound.eq_1, ite_eq_right hlt]
    simp only [hd, hf, hlen, Bool.false_eq_true, ite_false]
    exact ⟨hs, by omega⟩

/-- **The lower-bound iterator**: after `SeekLowerBound t k`, draining the
iterator yields the values of exactly the keys `≥ k`, in ascending key order,
without a fault, within `4 * size t + 4` steps. -/
theorem iter_lowerBound {t : Node α} (h : WF true t) (k : Key) (fuel : Nat) (hf : 4 * size t + 4 ≤ fuel) :
    run nextStep fuel (seekLowerBound t k []) =
      ((entries t).filter (fun e => !keyLt e.1 k)).map (fun e => some e.2) := by
  obtain ⟨hg, hmu⟩ := iter_seekLB_good t k [] true h (by simp [iter_good])
  have hmu0 : iter_mu ([] : Stack α) = 0 := rfl
  rw [iter_run fuel _ hg (by omega), iter_seekLB_out t k [] true h, iter_stackOut_nil,
    List.append_nil]
  have hfe : fullEntries t = entries t := by simp [fullEntries, h.root_seg]
  rw [hfe]
  rfl

/-! ### `SeekPrefixWatch` -/

private theorem iter_isPrefixOf_append (l a b : Key) :
    (l ++ a).isPrefixOf (l ++ b) = a.isPrefixOf b := by
  induction l with
  | nil => rfl
  | cons x xs ih => simp [ih]

private theorem iter_isPrefixOf_eq (s p : Key) (h : s.isPrefixOf p = true) :
    p = s ++ p.drop s.length := by
  induction s generalizing p with
  | nil => simp
  | cons x xs ih =>
    cases p with
    | nil => simp [List.isPrefixOf] at h
    | cons y ys =>
      simp only [List.isPrefixOf, Bool.and_eq_true, beq_iff_eq] at h
      obtain ⟨rfl, h⟩ := h
      simp only [List.length_cons, List.drop_succ_cons, List.cons_append]
      rw [← ih ys h]

private theorem iter_isPrefixOf_append_right (p s x : Key) (h : p.isPrefixOf s = true) :
    p.isPrefixOf (s ++ x) = true := by
  induction p generalizing s with
  | nil => rfl
  | cons a as ih =>
    cases s with
    | nil => simp [List.isPrefixOf] at h
    | cons y ys =>
      simp only [List.isPrefixOf, Bool.and_eq_true, beq_iff_eq] at h
      obtain ⟨rfl, h⟩ := h
      simp [ih ys h]

/-- A prefix of `s ++ x` either extends `s` or is a proper prefix of `s`. -/
private theorem iter_isPrefixOf_append_cases (p s x : Key) (h : p.isPrefixOf (s ++ x) = true) :
    s.isPrefixOf p = true ∨ (p.length < s.length ∧ p.isPrefixOf s = true) := by
  induction p generalizing s with
  | nil =>
    cases s with
    | nil => left; rfl
    | cons y ys => right; exact ⟨by simp, rfl⟩
  | cons a as ih =>
    cases s with
    | nil => left; rfl
    | cons y ys =>
      simp only [List.cons_append, List.isPrefixOf, Bool.and_eq_true, beq_iff_eq] at h
      obtain ⟨rfl, h⟩ := h
      rcases ih ys h with h' | ⟨hl, h'⟩
      · left; simp [List.isPrefixOf, h']
      · right; exact ⟨by simp; omega, by simp [List.isPrefixOf, h']⟩

private theorem iter_fullEntries_filter_prefix (c : Node α) (p' : Key) :
    (fullEntries c).filter (fun e => (c.seg ++ p').isPrefixOf e.1) =
      ((entries c).filter (fun e => p'.isPrefixOf e.1)).map (fun e => (c.seg ++ e.1, e.2)) := by
  simp only [fullEntries, List.filter_map]
  congr 2
  funext e
  simp [iter_isPrefixOf_append]

private theorem iter_prefix_kid_ne {d : Node α} (hd : WF false d) {b : Nat} (rest : Key)
    (h : d.lbl ≠ b) : (fullEntries d).filter (fun e => (b :: rest).isPrefixOf e.1) = [] := by
  rw [List.filter_eq_nil_iff]
  intro e he
  simp [iter_keys_noprefix hd.seg_ne_nil rest h e he]

private theorem iter_own_filter_prefix (v : Option α) (b : Nat) (rest : Key) :
    (v.map (fun x => (([] : Key), x))).toList.filter (fun e => (b :: rest).isPrefixOf e.1) = [] := by
  cases v <;> simp [List.isPrefixOf]

private theorem iter_entries_filter_prefix_found {r : Bool} {seg : Key} {v : Option α}
    {kids : List (Node α)} (hwf : WF r (mk seg v kids)) {b : Nat} {rest : Key}
    (hf : (rankOf kids b).2 = true) {c : Node α} (hc : kids[(rankOf kids b).1]? = some c) :
    (entries (mk seg v kids)).filter (fun e => (b :: rest).isPrefixOf e.1) =
      (fullEntries c).filter (fun e => (b :: rest).isPrefixOf e.1) := by
  rw [entries_mk, List.filter_append, List.filter_flatMap, iter_own_filter_prefix, List.nil_append]
  obtain ⟨c', hc', -, hdrop, hgt⟩ := iter_rank_found kids b hwf.kids_sorted hf
  rw [hc] at hc'
  cases hc'
  have htake := (iter_rank_split kids b hwf.kids_sorted).1
  generalize (rankOf kids b).1 = k at hdrop hgt htake
  have hsplit : kids.flatMap (fun d => (fullEntries d).filter (fun e => (b :: rest).isPrefixOf e.1)) =
      (kids.take k).flatMap (fun d => (fullEntries d).filter (fun e => (b :: rest).isPrefixOf e.1)) ++
      (kids.drop k).flatMap (fun d => (fullEntries d).filter (fun e => (b :: rest).isPrefixOf e.1)) := by
    rw [← List.flatMap_append, List.take_append_drop]
  have h1 : (kids.take k).flatMap
      (fun d => (fullEntries d).filter (fun e => (b :: rest).isPrefixOf e.1)) = [] :=
    List.flatMap_eq_nil_iff.mpr (fun d hd => iter_prefix_kid_ne
      (hwf.kids_wf d (List.mem_of_mem_take hd)) rest (by have := htake d hd; omega))
  have h2 : (kids.drop (k + 1)).flatMap
      (fun d => (fullEntries d).filter (fun e => (b :: rest).isPrefixOf e.1)) = [] :=
    List.flatMap_eq_nil_iff.mpr (fun d hd => iter_prefix_kid_ne
      (hwf.kids_wf d (List.mem_of_mem_drop hd)) rest (by have := hgt d hd; omega))
  rw [hsplit, h1, hdrop, List.flatMap_cons, h2]
  simp

private theorem iter_entries_filter_prefix_notfound {r : Bool} {seg : Key} {v : Option α}
    {kids : List (Node α)} (hwf : WF r (mk seg v kids)) {b : Nat} {rest : Key}
    (hf : ¬ (rankOf kids b).2 = true) :
    (entries (mk seg v kids)).filter (fun e => (b :: rest).isPrefixOf e.1) = [] := by
  rw [entries_mk, List.filter_append, List.filter_flatMap, iter_own_filter_prefix, List.nil_append]
  refine List.flatMap_eq_nil_iff.mpr (fun d hd => iter_prefix_kid_ne (hwf.kids_wf d hd) rest ?_)
  intro h
  apply hf
  simp only [rankOf, List.any_eq_true, decide_eq_true_eq]
  exact ⟨d, hd, h⟩

/-- `seekPrefix` finds the node whose subtree holds exactly the keys with the
prefix, or reports that there are none. -/
private theorem iter_seekPrefix_spec (n : Node α) (p : Key) : ∀ r, WF r n →
    (seekPrefix n p = none → (entries n).filter (fun e => p.isPrefixOf e.1) = []) ∧
    (∀ m, seekPrefix n p = some m → (∃ r', WF r' m) ∧ size m ≤ size n ∧
      iter_outOf ((entries n).filter (fun e => p.isPrefixOf e.1)) = iter_vals m) := by
  induction n, p using seekPrefix.induct with
  | case1 n =>
    intro r hwf
    rw [seekPrefix.eq_1]
    refine ⟨fun h => (by cases h), fun m hm => ?_⟩
    cases hm
    refine ⟨⟨r, hwf⟩, Nat.le_refl _, ?_⟩
    simp only [iter_vals, List.isPrefixOf]
    rw [List.filter_eq_self.mpr (fun _ _ => rfl)]
  | case2 seg val kids b rest hf hgk =>
    intro r hwf
    obtain ⟨c, hc, -⟩ := iter_rank_found kids b hwf.kids_sorted hf
    rw [iter_getKid_none hgk] at hc
    cases hc
  | case3 seg val kids b rest hf c hmem hgk hpre ih =>
    intro r hwf
    have hcwf : WF false c := hwf.kids_wf c hmem
    have hc : kids[(rankOf kids b).1]? = some c := iter_getKid_some hgk
    have hsp : seekPrefix (mk seg val kids) (b :: rest) =
        seekPrefix c (List.drop c.seg.length (b :: rest)) := by
      rw [seekPrefix.eq_2]
      simp only [hf, hgk, hpre, ite_true]
    have heq := iter_isPrefixOf_eq _ _ hpre
    have hfilt : (entries (mk seg val kids)).filter (fun e => (b :: rest).isPrefixOf e.1) =
        ((entries c).filter (fun e => (List.drop c.seg.length (b :: rest)).isPrefixOf e.1)).map
          (fun e => (c.seg ++ e.1, e.2)) := by
      rw [iter_entries_filter_prefix_found hwf hf hc]
      conv => lhs; rw [heq]
      exact iter_fullEntries_filter_prefix c _
    obtain ⟨ih1, ih2⟩ := ih false hcwf
    refine ⟨fun h => ?_, fun m hm => ?_⟩
    · rw [hsp] at h
      rw [hfilt, ih1 h]
      rfl
    · rw [hsp] at hm
      obtain ⟨hw, hsz, hout⟩ := ih2 m hm
      refine ⟨hw, ?_, ?_⟩
      · have := iter_size_lt_of_mem (s := seg) (v := val) hmem
        omega
      · rw [hfilt, iter_outOf_map_key (fun k => c.seg ++ k)]
        exact hout
  | case4 seg val kids b rest hf c hmem hgk hnpre hcond =>
    intro r hwf
    have hcwf : WF false c := hwf.kids_wf c hmem
    have hc : kids[(rankOf kids b).1]? = some c := iter_getKid_some hgk
    have hsp : seekPrefix (mk seg val kids) (b :: rest) = some c := by
      rw [seekPrefix.eq_2]
      simp only [hf, hgk, hnpre, hcond, ite_true, Bool.false_eq_true, ite_false, and_self]
    rw [hsp]
    refine ⟨fun h => (by cases h), fun m hm => ?_⟩
    cases hm
    refine ⟨⟨false, hcwf⟩, Nat.le_of_lt (iter_size_lt_of_mem hmem), ?_⟩
    rw [iter_entries_filter_prefix_found hwf hf hc, List.filter_eq_self.mpr, iter_outOf_fullEntries]
    intro e he
    simp only [fullEntries, List.mem_map] at he
    obtain ⟨e', _, rfl⟩ := he
    exact iter_isPrefixOf_append_right _ _ _ hcond.2
  | case5 seg val kids b rest hf c hmem hgk hnpre hcond =>
    intro r hwf
    have hc : kids[(rankOf kids b).1]? = some c := iter_getKid_some hgk
    have hsp : seekPrefix (mk seg val kids) (b :: rest) = none := by
      rw [seekPrefix.eq_2]
      simp only [hf, hgk, hnpre, hcond, ite_true, Bool.false_eq_true, ite_false]
    rw [hsp]
    refine ⟨fun _ => ?_, fun m hm => by cases hm⟩
    rw [iter_entries_filter_prefix_found hwf hf hc, List.filter_eq_nil_iff]
    intro e he
    simp only [fullEntries, List.mem_map] at he
    obtain ⟨e', _, rfl⟩ := he
    intro h
    rcases iter_isPrefixOf_append_cases _ _ _ h with h' | h'
    · exact hnpre h'
    · exact hcond h'
  | case6 seg val kids b rest hf =>
    intro r hwf
    have hsp : seekPrefix (mk seg val kids) (b :: rest) = none := by
      rw [seekPrefix.eq_2]
      simp only [hf, Bool.false_eq_true, ite_false]
    rw [hsp]
    exact ⟨fun _ => iter_entries_filter_prefix_notfound hwf hf, fun m hm => by cases hm⟩

/-- **The prefix iterator**: after `SeekPrefixWatch t p`, draining the
iterator yields the values of exactly the keys that start with `p`, in
ascending key order, without a fault, within `4 * size t + 4` steps. -/
theorem iter_prefix {t : Node α} (h : WF true t) (p : Key) (fuel : Nat) (hf : 4 * size t + 4 ≤ fuel) :
    run nextStep fuel (seekPrefixFwd t p) =
      ((entries t).filter (fun e => p.isPrefixOf e.1)).map (fun e => some e.2) := by
  obtain ⟨hnone, hsome⟩ := iter_seekPrefix_spec t p true h
  unfold seekPrefixFwd
  cases hsp : seekPrefix t p with
  | none =>
    simp only
    rw [hnone hsp]
    cases fuel <;> simp [run, nextStep]
  | some m =>
    obtain ⟨⟨r', hw⟩, hsz, hout⟩ := hsome m hsp
    simp only
    have hg := iter_pushSubtree_good hw (s := []) (by simp [iter_good])
    have hmu := iter_pushSubtree_mu m ([] : Stack α)
    have hmu0 : iter_mu ([] : Stack α) = 0 := rfl
    rw [iter_run fuel _ hg (by omega), iter_pushSubtree_out, iter_stackOut_nil, List.append_nil,
      ← hout]
    rfl

end Node
end JuuriFormal
