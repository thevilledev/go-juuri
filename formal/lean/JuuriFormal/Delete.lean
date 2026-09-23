/-
Copyright (c) 2026 Ville Vesilehto
SPDX-License-Identifier: MPL-2.0

`Txn.Delete` and `Txn.DeletePrefix` are correct: on a well-formed tree they
report a miss exactly when there is nothing to remove, and otherwise return a
well-formed tree holding exactly the entries that were not removed.
-/
import JuuriFormal.Order

namespace JuuriFormal
namespace Node

variable {α : Type}

/-! ### Lists of entries -/

private theorem lookup_eq_none_iff' {k : Key} {l : List (Key × α)} :
    l.lookup k = none ↔ ∀ e ∈ l, e.1 ≠ k := by
  induction l with
  | nil => simp
  | cons e l ih =>
    obtain ⟨k', y⟩ := e
    by_cases hk : k = k'
    · subst hk; simp
    · have : (k == k') = false := by simpa using hk
      simp only [List.lookup_cons, this, ih, List.mem_cons, forall_eq_or_imp]
      exact ⟨fun h => ⟨fun h' => hk h'.symm, h⟩, fun h => h.2⟩

private theorem lookup_of_mem' {k : Key} {x : α} {l : List (Key × α)}
    (hn : (l.map (·.1)).Nodup) (hm : (k, x) ∈ l) : l.lookup k = some x := by
  induction l with
  | nil => simp at hm
  | cons e l ih =>
    obtain ⟨k', y⟩ := e
    rw [List.map_cons, List.nodup_cons] at hn
    rcases List.mem_cons.mp hm with h | h
    · cases h; simp
    · have hk : k ≠ k' := by
        rintro rfl; exact hn.1 (List.mem_map.mpr ⟨_, h, rfl⟩)
      have : (k == k') = false := by simpa using hk
      simp only [List.lookup_cons, this]
      exact ih hn.2 h

private theorem filter_ne_map (p k : Key) (l : List (Key × α)) :
    (l.map (fun e => (p ++ e.1, e.2))).filter (fun e => e.1 != p ++ k) =
      (l.filter (fun e => e.1 != k)).map (fun e => (p ++ e.1, e.2)) := by
  rw [List.filter_map]
  congr 1
  apply List.filter_congr
  intro e _
  by_cases h : e.1 = k
  · simp [h]
  · have h1 : (p ++ e.1 != p ++ k) = true :=
      bne_iff_ne.mpr (fun h' => h (List.append_cancel_left h'))
    have h2 : (e.1 != k) = true := bne_iff_ne.mpr h
    simp only [Function.comp_apply]
    rw [h1, h2]

private theorem isPrefixOf_append_append (p a b : Key) :
    (p ++ a).isPrefixOf (p ++ b) = a.isPrefixOf b := by
  induction p with
  | nil => rfl
  | cons x xs ih => simp [ih]

private theorem eq_append_drop {a p : Key} (h : a.isPrefixOf p = true) :
    p = a ++ p.drop a.length := by
  obtain ⟨t, rfl⟩ := List.isPrefixOf_iff_prefix.mp h
  simp

/-- How a prefix search continues below a child, as `deletePrefix` computes it. -/
private theorem prefix_sub {seg p sub : Key}
    (h : (seg.isPrefixOf p = true ∧ sub = p.drop seg.length) ∨
      (p.isPrefixOf seg = true ∧ sub = [])) :
    ∀ e : Key, p.isPrefixOf (seg ++ e) = sub.isPrefixOf e := by
  intro e
  rcases h with ⟨h, rfl⟩ | ⟨h, rfl⟩
  · conv => lhs; rw [eq_append_drop h]
    exact isPrefixOf_append_append _ _ _
  · simp only [List.isPrefixOf_nil_left]
    exact List.isPrefixOf_iff_prefix.mpr
      ((List.isPrefixOf_iff_prefix.mp h).trans (List.prefix_append _ _))

/-- The prefix search stops at a child: no key below it starts with `p`. -/
private theorem prefix_none {seg p : Key} (h1 : ¬ seg.isPrefixOf p = true)
    (h2 : ¬ (p.length < seg.length ∧ p.isPrefixOf seg = true)) :
    ∀ e : Key, p.isPrefixOf (seg ++ e) = false := by
  intro e
  cases hp : p.isPrefixOf (seg ++ e) with
  | false => rfl
  | true =>
    exfalso
    have hp' := List.isPrefixOf_iff_prefix.mp hp
    rcases List.prefix_or_prefix_of_prefix hp' (List.prefix_append seg e) with h | h
    · by_cases hl : p.length < seg.length
      · exact h2 ⟨hl, List.isPrefixOf_iff_prefix.mpr h⟩
      · have := h.eq_of_length (Nat.le_antisymm h.length_le (Nat.not_lt.mp hl))
        subst this
        exact h1 (List.isPrefixOf_iff_prefix.mpr (List.prefix_refl _))
    · exact h1 (List.isPrefixOf_iff_prefix.mpr h)

private theorem filter_prefix_map (p sub seg : Key) (l : List (Key × α))
    (h : ∀ e : Key, p.isPrefixOf (seg ++ e) = sub.isPrefixOf e) :
    (l.map (fun e => (seg ++ e.1, e.2))).filter (fun e => !p.isPrefixOf e.1) =
      (l.filter (fun e => !sub.isPrefixOf e.1)).map (fun e => (seg ++ e.1, e.2)) := by
  rw [List.filter_map]
  congr 1
  apply List.filter_congr
  intro e _
  simp [h]

/-! ### Nodes -/

private theorem wf_inv {r : Bool} {s : Key} {v : Option α} {kids : List (Node α)}
    (h : WF r (mk s v kids)) :
    (r = true → s = []) ∧ (r = false → s ≠ [] ∧ (v = none → 2 ≤ kids.length)) ∧
      (kids.map lbl).Pairwise (· < ·) ∧ (∀ c ∈ kids, WF false c) := by
  cases h with
  | mk h1 h2 h3 h4 => exact ⟨h1, h2, h3, h4⟩

/-- A non-root well-formed node holds at least one entry. -/
private theorem entries_nonempty {r : Bool} {n : Node α} (h : WF r n) :
    r = false → ∃ e, e ∈ entries n := by
  induction h with
  | @mk isRoot s v kids h1 h2 h3 h4 ih =>
    intro hr
    rw [entries_mk]
    cases v with
    | some x => exact ⟨([], x), by simp⟩
    | none =>
      have hlen := (h2 hr).2 rfl
      match kids, hlen, ih with
      | c :: _, _, ih =>
        obtain ⟨e, he⟩ := ih c (by simp) rfl
        refine ⟨(c.seg ++ e.1, e.2), ?_⟩
        simp only [Option.map_none, Option.toList_none, List.nil_append, List.flatMap_cons,
          List.mem_append]
        left
        exact List.mem_map.mpr ⟨e, he, rfl⟩

private theorem kids_key_ne_nil {kids : List (Node α)} (hk : ∀ c ∈ kids, WF false c) :
    ∀ e ∈ kids.flatMap fullEntries, e.1 ≠ [] := by
  intro e he
  obtain ⟨d, hd, he⟩ := List.mem_flatMap.mp he
  obtain ⟨r, hr⟩ := fullEntries_head (hk d hd).seg_ne_nil e he
  rw [hr]; exact List.cons_ne_nil _ _

/-- The child a search for byte `b` descends into, and its neighbours. -/
private theorem rank_found {kids : List (Node α)} (hs : (kids.map lbl).Pairwise (· < ·))
    {b : Nat} (hf : (rankOf kids b).2 = true) :
    ∃ A c B, kids = A ++ c :: B ∧ (rankOf kids b).1 = A.length ∧ c.lbl = b ∧
      (∀ d ∈ A, d.lbl < b) ∧ (∀ d ∈ B, b < d.lbl) := by
  simp only [rankOf, List.any_eq_true, decide_eq_true_eq] at hf
  obtain ⟨c, hc, rfl⟩ := hf
  obtain ⟨A, B, rfl⟩ := List.append_of_mem hc
  rw [List.map_append, List.map_cons, List.pairwise_append, List.pairwise_cons] at hs
  obtain ⟨_, ⟨hcB, _⟩, hAc⟩ := hs
  have hA : ∀ d ∈ A, d.lbl < c.lbl := fun d hd =>
    hAc _ (List.mem_map_of_mem hd) _ (List.mem_cons_self ..)
  have hB : ∀ d ∈ B, c.lbl < d.lbl := fun d hd => hcB _ (List.mem_map_of_mem hd)
  refine ⟨A, c, B, rfl, ?_, rfl, hA, hB⟩
  simp only [rankOf, List.countP_append, List.countP_cons]
  rw [List.countP_eq_length.mpr (by simpa using hA),
    List.countP_eq_zero.mpr (by intro d hd; simpa using Nat.le_of_lt (hB d hd))]
  simp

private theorem rank_missing {kids : List (Node α)} {b : Nat}
    (hf : ¬ (rankOf kids b).2 = true) : ∀ d ∈ kids, d.lbl ≠ b := by
  intro d hd h
  apply hf
  simp only [rankOf, List.any_eq_true, decide_eq_true_eq]
  exact ⟨d, hd, h⟩

private theorem getKid_some {kids : List (Node α)} {i : Nat} {c : Node α} {h : c ∈ kids}
    (hg : getKid kids i = some ⟨c, h⟩) : kids[i]? = some c := by
  unfold getKid at hg
  split at hg
  · simp at hg
  · rename_i c' hc'
    simp only [Option.some.injEq, Subtype.mk.injEq] at hg
    subst hg; exact hc'

private theorem getKid_none {kids : List (Node α)} {i : Nat}
    (hg : getKid kids i = none) : kids[i]? = none := by
  unfold getKid at hg
  split at hg
  · assumption
  · simp at hg

/-- Every key under a child other than the one labelled `b` avoids `b`. -/
private theorem other_key {d : Node α} {b : Nat} (hd : WF false d) (hl : d.lbl ≠ b) :
    ∀ e ∈ fullEntries d, ∀ r, e.1 ≠ b :: r := by
  intro e he r h
  obtain ⟨r', hr'⟩ := fullEntries_head hd.seg_ne_nil e he
  rw [hr'] at h
  exact hl (List.cons.inj h).1

private theorem not_prefix_of_ne {b : Nat} {rest k : Key} (h : ∀ r, k ≠ b :: r) :
    (b :: rest).isPrefixOf k = false := by
  cases k with
  | nil => rfl
  | cons y ys =>
    have hby : (b == y) = false := by
      simp only [beq_eq_false_iff_ne]
      intro hb; exact h ys (by rw [hb])
    simp [List.isPrefixOf, hby]

/-- A property of all entries of a node, split around the child labelled `b`. -/
private theorem forall_entries_split (P : Key × α → Prop) {s : Key} {v : Option α}
    {A B : List (Node α)} {c : Node α} {b : Nat}
    (hk : ∀ d ∈ A ++ c :: B, WF false d)
    (hA : ∀ d ∈ A, d.lbl < b) (hB : ∀ d ∈ B, b < d.lbl)
    (hP : ∀ e : Key × α, (∀ r, e.1 ≠ b :: r) → P e)
    (hc : ∀ e ∈ fullEntries c, P e) :
    ∀ e ∈ entries (mk s v (A ++ c :: B)), P e := by
  intro e he
  rw [entries_mk] at he
  rcases List.mem_append.mp he with he | he
  · apply hP
    cases v with
    | none => simp at he
    | some x =>
      simp at he; subst he; intro r h; cases h
  · obtain ⟨d, hd, hed⟩ := List.mem_flatMap.mp he
    rcases List.mem_append.mp hd with hd | hd
    · exact hP e (other_key (hk d (by simp [hd])) (Nat.ne_of_lt (hA d hd)) e hed)
    · rcases List.mem_cons.mp hd with hd | hd
      · rw [hd] at hed; exact hc e hed
      · exact hP e (other_key (hk d (by simp [hd])) (Nat.ne_of_gt (hB d hd)) e hed)

/-- A property of all entries of a node none of whose children is labelled `b`. -/
private theorem forall_entries_miss (P : Key × α → Prop) {s : Key} {v : Option α}
    {kids : List (Node α)} {b : Nat}
    (hk : ∀ d ∈ kids, WF false d) (hl : ∀ d ∈ kids, d.lbl ≠ b)
    (hP : ∀ e : Key × α, (∀ r, e.1 ≠ b :: r) → P e) :
    ∀ e ∈ entries (mk s v kids), P e := by
  intro e he
  rw [entries_mk] at he
  rcases List.mem_append.mp he with he | he
  · apply hP
    cases v with
    | none => simp at he
    | some x =>
      simp at he; subst he; intro r h; cases h
  · obtain ⟨d, hd, he⟩ := List.mem_flatMap.mp he
    exact hP e (other_key (hk d hd) (hl d hd) e he)

/-- Filtering the entries of a node, where only the child labelled `b` is affected. -/
private theorem filter_split (Q : Key × α → Bool) {s : Key} {v : Option α}
    {A B : List (Node α)} {c : Node α} {b : Nat}
    (hk : ∀ d ∈ A ++ c :: B, WF false d)
    (hA : ∀ d ∈ A, d.lbl < b) (hB : ∀ d ∈ B, b < d.lbl)
    (hQ : ∀ e : Key × α, (∀ r, e.1 ≠ b :: r) → Q e = true) :
    (entries (mk s v (A ++ c :: B))).filter Q =
      (v.map (fun x => ([], x))).toList ++
        (A.flatMap fullEntries ++ ((fullEntries c).filter Q ++ B.flatMap fullEntries)) := by
  rw [entries_mk, List.filter_append, List.flatMap_append, List.flatMap_cons,
    List.filter_append, List.filter_append]
  have hAk : ∀ d ∈ A, WF false d := fun d hd => hk d (by simp [hd])
  have hBk : ∀ d ∈ B, WF false d := fun d hd => hk d (by simp [hd])
  congr 1
  · rw [List.filter_eq_self]
    intro e he
    apply hQ
    cases v with
    | none => simp at he
    | some x =>
      simp at he; subst he; intro r h; cases h
  · congr 1
    · rw [List.filter_eq_self]
      intro e he
      obtain ⟨d, hd, he⟩ := List.mem_flatMap.mp he
      exact hQ e (other_key (hAk d hd) (Nat.ne_of_lt (hA d hd)) e he)
    · congr 1
      rw [List.filter_eq_self]
      intro e he
      obtain ⟨d, hd, he⟩ := List.mem_flatMap.mp he
      exact hQ e (other_key (hBk d hd) (Nat.ne_of_gt (hB d hd)) e he)

/-- `mergeChild`: the merged node stands where `n` stood and holds what `c` held. -/
private theorem merge_spec {n c : Node α} (hn : n.seg ≠ []) (hc : WF false c) :
    WF false (mergeNode n c) ∧ (mergeNode n c).lbl = n.lbl ∧
      fullEntries (mergeNode n c) = (fullEntries c).map (fun e => (n.seg ++ e.1, e.2)) := by
  obtain ⟨cs, cv, ck⟩ := c
  obtain ⟨_, h2, h3, h4⟩ := wf_inv hc
  refine ⟨?_, ?_, ?_⟩
  · refine WF.mk (fun h => by cases h) (fun _ => ⟨?_, (h2 rfl).2⟩) h3 h4
    simp [hn]
  · cases hs : n.seg with
    | nil => exact absurd hs hn
    | cons y ys => simp [mergeNode, lbl, hs]
  · simp [mergeNode, fullEntries, entries_mk, List.map_map, Function.comp_def,
      List.append_assoc]

/-- `unlink`: the parent without the child at `A.length`. -/
private theorem unlink_spec {r : Bool} {s : Key} {v : Option α} {A B : List (Node α)}
    {c : Node α} (h : WF r (mk s v (A ++ c :: B))) :
    WF r (unlink r (mk s v (A ++ c :: B)) A.length) ∧
      (unlink r (mk s v (A ++ c :: B)) A.length).lbl = (mk s v (A ++ c :: B)).lbl ∧
      fullEntries (unlink r (mk s v (A ++ c :: B)) A.length) =
        ((v.map (fun x => ([], x))).toList ++
          (A.flatMap fullEntries ++ B.flatMap fullEntries)).map
          (fun e : Key × α => (s ++ e.1, e.2)) := by
  obtain ⟨h1, h2, h3, h4⟩ := wf_inv h
  have herase : (A ++ c :: B).eraseIdx A.length = A ++ B := by
    rw [List.eraseIdx_append_of_length_le (Nat.le_refl _)]; simp
  simp only [unlink]
  split
  · rename_i hm
    simp only [Bool.and_eq_true, Bool.not_eq_true', Option.isNone_iff_eq_none,
      beq_iff_eq] at hm
    obtain ⟨⟨hr, hv⟩, hlen⟩ := hm
    subst hr hv
    have hs : s ≠ [] := (h2 rfl).1
    rcases A with _ | ⟨a, _ | ⟨a2, A⟩⟩
    · rcases B with _ | ⟨sib, _ | ⟨b2, B⟩⟩
      · simp at hlen
      · obtain ⟨hw, hl, hf⟩ := merge_spec (n := mk s none [c, sib]) hs (h4 sib (by simp))
        simp only [List.length_nil, List.nil_append, Nat.sub_zero, List.getElem?_cons_succ,
          List.getElem?_cons_zero]
        refine ⟨hw, hl, ?_⟩
        rw [hf]; simp [fullEntries]
      · simp at hlen
    · rcases B with _ | ⟨b1, B⟩
      · obtain ⟨hw, hl, hf⟩ := merge_spec (n := mk s none [a, c]) hs (h4 a (by simp))
        simp only [List.length_cons, List.length_nil, Nat.zero_add, Nat.sub_self,
          List.cons_append, List.nil_append, List.getElem?_cons_zero]
        refine ⟨hw, hl, ?_⟩
        rw [hf]; simp [fullEntries]
      · simp at hlen
    · simp at hlen <;> omega
  · rename_i hm
    rw [herase]
    refine ⟨WF.mk h1 ?_ ?_ ?_, rfl, ?_⟩
    · intro hr
      obtain ⟨hs, hv⟩ := h2 hr
      refine ⟨hs, fun hn => ?_⟩
      have h2l := hv hn
      subst hr hn
      simp only [Bool.not_false, Option.isNone_none, Bool.and_self, Bool.true_and,
        beq_iff_eq] at hm
      simp only [List.length_append, List.length_cons] at h2l hm ⊢
      omega
    · rw [List.map_append]
      rw [List.map_append, List.map_cons] at h3
      exact h3.sublist (List.Sublist.append_left (List.sublist_cons_self _ _) _)
    · intro d hd
      apply h4 d
      simp only [List.mem_append, List.mem_cons] at hd ⊢
      rcases hd with hd | hd
      · exact Or.inl hd
      · exact Or.inr (Or.inr hd)
    · simp [fullEntries, entries_mk]

/-- Replacing the child at `A.length` by one with the same label. -/
private theorem set_spec {r : Bool} {s : Key} {v : Option α} {A B : List (Node α)}
    {c c' : Node α} (h : WF r (mk s v (A ++ c :: B))) (hc' : WF false c')
    (hl : c'.lbl = c.lbl) :
    WF r (mk s v ((A ++ c :: B).set A.length c')) ∧
      (mk s v ((A ++ c :: B).set A.length c')).lbl = (mk s v (A ++ c :: B)).lbl ∧
      entries (mk s v ((A ++ c :: B).set A.length c')) =
        (v.map (fun x => ([], x))).toList ++
          (A.flatMap fullEntries ++ (fullEntries c' ++ B.flatMap fullEntries)) := by
  have hset : (A ++ c :: B).set A.length c' = A ++ c' :: B := by simp
  rw [hset]
  obtain ⟨h1, h2, h3, h4⟩ := wf_inv h
  refine ⟨WF.mk h1 ?_ ?_ ?_, rfl, ?_⟩
  · intro hr
    obtain ⟨hs, hv⟩ := h2 hr
    exact ⟨hs, fun hn => by simpa using hv hn⟩
  · simpa [hl] using h3
  · intro d hd
    simp only [List.mem_append, List.mem_cons] at hd
    rcases hd with hd | rfl | hd
    · exact h4 d (by simp [hd])
    · exact hc'
    · exact h4 d (by simp [hd])
  · simp [entries_mk]

/-- Dropping the value of a node that keeps its children. -/
private theorem drop_value {r : Bool} {s : Key} {x : α} {kids : List (Node α)}
    (h : WF r (mk s (some x) kids)) (hl : r = false → 2 ≤ kids.length) :
    WF r (mk s none kids) ∧
      fullEntries (mk s none kids) =
        ((entries (mk s (some x) kids)).filter (fun e => e.1 != [])).map
          (fun e => (s ++ e.1, e.2)) := by
  obtain ⟨h1, h2, h3, h4⟩ := wf_inv h
  refine ⟨WF.mk h1 (fun hr => ⟨(h2 hr).1, fun _ => hl hr⟩) h3 h4, ?_⟩
  have hk := kids_key_ne_nil h4
  simp only [fullEntries, entries_mk, seg_mk, Option.map_none, Option.toList_none,
    List.nil_append, Option.map_some, Option.toList_some, List.cons_append]
  rw [List.filter_cons_of_neg (by simp), List.filter_eq_self.mpr]
  intro e he
  simpa using hk e he

/-! ### Delete -/

/-- What `delete` returns from a node, relative to its entries. -/
private def DSpec (r : Bool) (n : Node α) (k : Key) : Option (Option (Node α) × α) → Prop
  | none => ∀ e ∈ entries n, e.1 ≠ k
  | some (none, x) =>
    (k, x) ∈ entries n ∧ r = false ∧ (entries n).filter (fun e => e.1 != k) = []
  | some (some n', x) =>
    (k, x) ∈ entries n ∧ WF r n' ∧ n'.lbl = n.lbl ∧
      fullEntries n' = ((entries n).filter (fun e => e.1 != k)).map (fun e => (n.seg ++ e.1, e.2))

/-- The parent sees the key found below the child. -/
private theorem mem_parent {s : Key} {v : Option α} {kids : List (Node α)} {c : Node α}
    (hc : c ∈ kids) {k : Key} {x : α} (hk : (k, x) ∈ entries c) :
    (c.seg ++ k, x) ∈ entries (mk s v kids) := by
  rw [entries_mk]
  refine List.mem_append_right _ (List.mem_flatMap.mpr ⟨c, hc, ?_⟩)
  exact List.mem_map.mpr ⟨(k, x), hk, rfl⟩

private theorem delete_core (r : Bool) (n : Node α) (k : Key) :
    WF r n → DSpec r n k (delete r n k) := by
  fun_induction delete r n k with
  | case1 isRoot s kids =>
    intro h
    obtain ⟨_, _, _, h4⟩ := wf_inv h
    intro e he
    rw [entries_mk] at he
    simp only [Option.map_none, Option.toList_none, List.nil_append] at he
    exact kids_key_ne_nil h4 e he
  | case2 s kids x =>
    intro h
    obtain ⟨hw, hf⟩ := drop_value h (fun h => by cases h)
    exact ⟨by simp [entries_mk], hw, rfl, hf⟩
  | case3 isRoot s kids x hr hl =>
    intro h
    have hr : isRoot = false := by simpa using hr
    have : kids = [] := List.eq_nil_of_length_eq_zero hl
    subst this
    refine ⟨by simp [entries_mk], hr, ?_⟩
    simp [entries_mk]
  | case4 isRoot s x hr c _ =>
    intro h
    have hr : isRoot = false := by simpa using hr
    subst hr
    obtain ⟨_, h2, _, h4⟩ := wf_inv h
    obtain ⟨hw, hl, hf⟩ := merge_spec (n := mk s (some x) [c]) (h2 rfl).1 (h4 c (by simp))
    refine ⟨by simp [entries_mk], hw, hl, ?_⟩
    rw [hf]
    have hk := kids_key_ne_nil (kids := [c]) h4
    simp only [entries_mk, Option.map_some, Option.toList_some, List.cons_append, seg_mk]
    rw [List.filter_cons_of_neg (by simp), List.filter_eq_self.mpr]
    · simp
    · intro e he; simpa using hk e he
  | case5 isRoot s kids x hr hl hne =>
    intro h
    have hr : isRoot = false := by simpa using hr
    have hlen : 2 ≤ kids.length := by
      match kids, hl, hne with
      | [], hl, _ => simp at hl
      | [c], _, hne => exact absurd rfl (hne c)
      | _ :: _ :: _, _, _ => simp
    obtain ⟨hw, hf⟩ := drop_value h (fun _ => hlen)
    exact ⟨by simp [entries_mk], hw, rfl, hf⟩
  | case6 isRoot s v kids b rest hf hg =>
    intro h
    obtain ⟨_, _, h3, _⟩ := wf_inv h
    obtain ⟨A, c, B, rfl, hi, _, _, _⟩ := rank_found h3 hf
    have := getKid_none hg
    rw [hi] at this
    simp at this
  | case7 isRoot s v kids b rest hf c hc hg hpre hd ih =>
    intro h
    obtain ⟨_, _, h3, h4⟩ := wf_inv h
    have ih := ih (h4 c hc)
    rw [hd] at ih
    obtain ⟨A, c0, B, rfl, hi, hlbl, hA, hB⟩ := rank_found h3 hf
    have hcc : c = c0 := by
      have := getKid_some hg
      rw [hi] at this
      simpa using this.symm
    subst hcc
    apply forall_entries_split (fun e => e.1 ≠ b :: rest) h4 hA hB
    · intro e he; exact fun h => he rest h
    · intro e he heq
      simp only [fullEntries, List.mem_map] at he
      obtain ⟨e', he', rfl⟩ := he
      apply ih e' he'
      simp only at heq
      rw [← heq, List.drop_left]
  | case8 isRoot s v kids b rest hf c hc hg hpre x hd ih =>
    intro h
    obtain ⟨_, _, h3, h4⟩ := wf_inv h
    have ih := ih (h4 c hc)
    rw [hd] at ih
    obtain ⟨hmem, _, hfil⟩ := ih
    obtain ⟨A, c0, B, rfl, hi, hlbl, hA, hB⟩ := rank_found h3 hf
    have hcc : c = c0 := by
      have := getKid_some hg
      rw [hi] at this
      simpa using this.symm
    subst hcc
    have hp := eq_append_drop hpre
    refine ⟨?_, ?_⟩
    · have := mem_parent (s := s) (v := v) hc hmem
      rwa [← hp] at this
    rw [hi]
    obtain ⟨hw, hl, hfe⟩ := unlink_spec h
    refine ⟨hw, hl, ?_⟩
    rw [hfe, filter_split (fun e => e.1 != b :: rest) h4 hA hB]
    · have hcpart : (fullEntries c).filter (fun e => e.1 != b :: rest) = [] := by
        unfold fullEntries
        rw [hp, filter_ne_map, hfil]
        rfl
      rw [hcpart, List.nil_append]
      rfl
    · intro e he
      simpa using he rest
  | case9 isRoot s v kids b rest hf c hc hg hpre c' x hd ih =>
    intro h
    obtain ⟨_, _, h3, h4⟩ := wf_inv h
    have ih := ih (h4 c hc)
    rw [hd] at ih
    obtain ⟨hmem, hw', hl', hfe'⟩ := ih
    obtain ⟨A, c0, B, rfl, hi, hlbl, hA, hB⟩ := rank_found h3 hf
    have hcc : c = c0 := by
      have := getKid_some hg
      rw [hi] at this
      simpa using this.symm
    subst hcc
    have hp := eq_append_drop hpre
    refine ⟨?_, ?_⟩
    · have := mem_parent (s := s) (v := v) hc hmem
      rwa [← hp] at this
    rw [hi]
    obtain ⟨hw, hl, hfe⟩ := set_spec h hw' hl'
    refine ⟨hw, hl, ?_⟩
    rw [fullEntries, hfe, filter_split (fun e => e.1 != b :: rest) h4 hA hB]
    · have hcpart : (fullEntries c).filter (fun e => e.1 != b :: rest) = fullEntries c' := by
        rw [hfe']
        unfold fullEntries
        generalize List.drop (List.length c.seg) (b :: rest) = r' at hp
        rw [hp, filter_ne_map]
      rw [hcpart]
      rfl
    · intro e he
      simpa using he rest
  | case10 isRoot s v kids b rest hf c hc hg hpre =>
    intro h
    obtain ⟨_, _, h3, h4⟩ := wf_inv h
    obtain ⟨A, c0, B, rfl, hi, hlbl, hA, hB⟩ := rank_found h3 hf
    have hcc : c = c0 := by
      have := getKid_some hg
      rw [hi] at this
      simpa using this.symm
    subst hcc
    apply forall_entries_split (fun e => e.1 ≠ b :: rest) h4 hA hB
    · intro e he; exact fun h => he rest h
    · intro e he heq
      simp only [fullEntries, List.mem_map] at he
      obtain ⟨e', _, rfl⟩ := he
      apply hpre
      simp only at heq
      rw [← heq]
      exact List.isPrefixOf_iff_prefix.mpr (List.prefix_append _ _)
  | case11 isRoot s v kids b rest hf =>
    intro h
    obtain ⟨_, _, _, h4⟩ := wf_inv h
    exact forall_entries_miss (fun e => e.1 ≠ b :: rest) h4 (rank_missing hf)
      (fun e he => fun h => he rest h)

theorem delete_miss {t : Node α} (h : WF true t) (k : Key) :
    delete true t k = none ↔ (entries t).lookup k = none := by
  have hc := delete_core true t k h
  rw [lookup_eq_none_iff']
  constructor
  · intro hd
    rw [hd] at hc
    exact hc
  · intro hl
    cases hd : delete true t k with
    | none => rfl
    | some p =>
      obtain ⟨res, x⟩ := p
      rw [hd] at hc
      exfalso
      have hmem : (k, x) ∈ entries t := by
        cases res with
        | none => exact hc.1
        | some n' => exact hc.1
      exact hl _ hmem rfl

theorem delete_hit {t : Node α} (h : WF true t) (k : Key) (res : Option (Node α)) (x : α)
    (hd : delete true t k = some (res, x)) :
    (entries t).lookup k = some x ∧
      ∃ t', res = some t' ∧ WF true t' ∧ entries t' = (entries t).filter (fun e => e.1 != k) := by
  have hc := delete_core true t k h
  rw [hd] at hc
  cases res with
  | none => exact absurd hc.2.1 (by simp)
  | some t' =>
    obtain ⟨hmem, hw, _, hfe⟩ := hc
    refine ⟨lookup_of_mem' (entries_sorted h).nodup_keys hmem, t', rfl, hw, ?_⟩
    have hs := h.root_seg
    have hs' := hw.root_seg
    simp only [fullEntries, hs, hs', List.nil_append] at hfe
    simpa using hfe

/-! ### DeletePrefix -/

/-- What `deletePrefix` returns from a node, relative to its entries. -/
private def PSpec (r : Bool) (n : Node α) (p : Key) : Option (Option (Node α)) → Prop
  | none => p ≠ [] ∧ ∀ e ∈ entries n, p.isPrefixOf e.1 = false
  | some none =>
    r = false ∧ (entries n).filter (fun e => !p.isPrefixOf e.1) = [] ∧
      (p ≠ [] → ∃ e ∈ entries n, p.isPrefixOf e.1 = true)
  | some (some n') =>
    WF r n' ∧ n'.lbl = n.lbl ∧
      fullEntries n' =
        ((entries n).filter (fun e => !p.isPrefixOf e.1)).map (fun e => (n.seg ++ e.1, e.2)) ∧
      (p ≠ [] → ∃ e ∈ entries n, p.isPrefixOf e.1 = true)

/-- Where a prefix search continues below the child `c`. -/
private theorem sub_cases {c : Node α} {p sub : Key}
    (h : (if _h : c.seg.isPrefixOf p = true then some (p.drop c.seg.length)
      else if _h : p.length < c.seg.length ∧ p.isPrefixOf c.seg = true then some [] else none) =
        some sub) :
    (c.seg.isPrefixOf p = true ∧ sub = p.drop c.seg.length) ∨
      (p.isPrefixOf c.seg = true ∧ sub = []) := by
  split at h
  · rename_i h1; exact Or.inl ⟨h1, (Option.some.inj h).symm⟩
  · split at h
    · rename_i h2; exact Or.inr ⟨h2.2, (Option.some.inj h).symm⟩
    · simp at h

/-- The parent finds an entry with the prefix once the child does. -/
private theorem prefix_exists_parent {s : Key} {v : Option α} {kids : List (Node α)}
    {c : Node α} (hc : c ∈ kids) (hcw : WF false c) {p sub : Key}
    (hsub : ∀ e : Key, p.isPrefixOf (c.seg ++ e) = sub.isPrefixOf e)
    (hex : sub ≠ [] → ∃ e ∈ entries c, sub.isPrefixOf e.1 = true) :
    ∃ e ∈ entries (mk s v kids), p.isPrefixOf e.1 = true := by
  have : ∃ e ∈ entries c, sub.isPrefixOf e.1 = true := by
    by_cases hs : sub = []
    · subst hs
      obtain ⟨e, he⟩ := entries_nonempty hcw rfl
      exact ⟨e, he, List.isPrefixOf_nil_left⟩
    · exact hex hs
  obtain ⟨e, he, hpe⟩ := this
  exact ⟨(c.seg ++ e.1, e.2), mem_parent hc he, by rw [hsub]; exact hpe⟩

private theorem deletePrefix_core (r : Bool) (n : Node α) (p : Key) :
    WF r n → PSpec r n p (deletePrefix r n p) := by
  fun_induction deletePrefix r n p with
  | case1 n =>
    intro h
    refine ⟨WF.mk (fun _ => rfl) (fun h => by cases h) List.Pairwise.nil (by simp), ?_, ?_, ?_⟩
    · have := h.root_seg
      simp [lbl, this]
    · simp [fullEntries, entries_mk]
    · intro h; exact absurd rfl h
  | case2 isRoot n hr =>
    intro h
    have hr : isRoot = false := by simpa using hr
    refine ⟨hr, ?_, ?_⟩
    · simp
    · intro h; exact absurd rfl h
  | case3 isRoot s v kids b rest hf hg =>
    intro h
    obtain ⟨_, _, h3, _⟩ := wf_inv h
    obtain ⟨A, c, B, rfl, hi, _, _, _⟩ := rank_found h3 hf
    have := getKid_none hg
    rw [hi] at this
    simp at this
  | case4 isRoot s v kids b rest hf c hc hg search sub hsub =>
    intro h
    obtain ⟨_, _, h3, h4⟩ := wf_inv h
    obtain ⟨A, c0, B, rfl, hi, hlbl, hA, hB⟩ := rank_found h3 hf
    have hcc : c = c0 := by
      have := getKid_some hg
      rw [hi] at this
      simpa using this.symm
    subst hcc
    have hnone : ∀ e : Key, (b :: rest).isPrefixOf (c.seg ++ e) = false := by
      simp only [sub, search] at hsub
      split at hsub
      · simp at hsub
      · rename_i h1
        split at hsub
        · simp at hsub
        · rename_i h2
          exact prefix_none h1 h2
    refine ⟨List.cons_ne_nil _ _, ?_⟩
    apply forall_entries_split (fun e => (b :: rest).isPrefixOf e.1 = false) h4 hA hB
    · intro e he
      exact not_prefix_of_ne he
    · intro e he
      simp only [fullEntries, List.mem_map] at he
      obtain ⟨e', _, rfl⟩ := he
      exact hnone e'.1
  | case5 isRoot s v kids b rest hf c hc hg search sub sub' hsub hd ih =>
    intro h
    obtain ⟨_, _, h3, h4⟩ := wf_inv h
    have ih := ih (h4 c hc)
    rw [hd] at ih
    obtain ⟨hne, hall⟩ := ih
    obtain ⟨A, c0, B, rfl, hi, hlbl, hA, hB⟩ := rank_found h3 hf
    have hcc : c = c0 := by
      have := getKid_some hg
      rw [hi] at this
      simpa using this.symm
    subst hcc
    have hsc := sub_cases hsub
    have hs := prefix_sub hsc
    refine ⟨List.cons_ne_nil _ _, ?_⟩
    apply forall_entries_split (fun e => (b :: rest).isPrefixOf e.1 = false) h4 hA hB
    · intro e he
      exact not_prefix_of_ne he
    · intro e he
      simp only [fullEntries, List.mem_map] at he
      obtain ⟨e', he', rfl⟩ := he
      simp only
      rw [hs]
      exact hall e' he'
  | case6 isRoot s v kids b rest hf c hc hg search sub sub' hsub hd ih =>
    intro h
    obtain ⟨_, _, h3, h4⟩ := wf_inv h
    have ih := ih (h4 c hc)
    rw [hd] at ih
    obtain ⟨_, hfil, hex⟩ := ih
    obtain ⟨A, c0, B, rfl, hi, hlbl, hA, hB⟩ := rank_found h3 hf
    have hcc : c = c0 := by
      have := getKid_some hg
      rw [hi] at this
      simpa using this.symm
    subst hcc
    have hsc := sub_cases hsub
    have hs := prefix_sub hsc
    rw [hi]
    obtain ⟨hw, hl, hfe⟩ := unlink_spec h
    refine ⟨hw, hl, ?_, fun _ => prefix_exists_parent hc (h4 c hc) hs hex⟩
    rw [hfe, filter_split (fun e => !(b :: rest).isPrefixOf e.1) h4 hA hB]
    · have hcpart : (fullEntries c).filter (fun e => !(b :: rest).isPrefixOf e.1) = [] := by
        unfold fullEntries
        rw [filter_prefix_map _ _ _ _ hs, hfil]
        rfl
      rw [hcpart, List.nil_append]
      rfl
    · intro e he
      rw [not_prefix_of_ne he]; rfl
  | case7 isRoot s v kids b rest hf c hc hg search sub sub' hsub c' hd ih =>
    intro h
    obtain ⟨_, _, h3, h4⟩ := wf_inv h
    have ih := ih (h4 c hc)
    rw [hd] at ih
    obtain ⟨hw', hl', hfe', hex⟩ := ih
    obtain ⟨A, c0, B, rfl, hi, hlbl, hA, hB⟩ := rank_found h3 hf
    have hcc : c = c0 := by
      have := getKid_some hg
      rw [hi] at this
      simpa using this.symm
    subst hcc
    have hsc := sub_cases hsub
    have hs := prefix_sub hsc
    rw [hi]
    obtain ⟨hw, hl, hfe⟩ := set_spec h hw' hl'
    refine ⟨hw, hl, ?_, fun _ => prefix_exists_parent hc (h4 c hc) hs hex⟩
    rw [fullEntries, hfe, filter_split (fun e => !(b :: rest).isPrefixOf e.1) h4 hA hB]
    · have hcpart :
          (fullEntries c).filter (fun e => !(b :: rest).isPrefixOf e.1) = fullEntries c' := by
        rw [hfe']
        unfold fullEntries
        rw [filter_prefix_map _ _ _ _ hs]
      rw [hcpart]
      rfl
    · intro e he
      rw [not_prefix_of_ne he]; rfl
  | case8 isRoot s v kids b rest hf =>
    intro h
    obtain ⟨_, _, _, h4⟩ := wf_inv h
    refine ⟨List.cons_ne_nil _ _, ?_⟩
    apply forall_entries_miss (fun e => (b :: rest).isPrefixOf e.1 = false) h4 (rank_missing hf)
    intro e he
    exact not_prefix_of_ne he

theorem deletePrefix_miss {t : Node α} (h : WF true t) (p : Key) :
    deletePrefix true t p = none ↔ (p ≠ [] ∧ ∀ e ∈ entries t, p.isPrefixOf e.1 = false) := by
  have hc := deletePrefix_core true t p h
  constructor
  · intro hd
    rw [hd] at hc
    exact hc
  · rintro ⟨hne, hall⟩
    cases hd : deletePrefix true t p with
    | none => rfl
    | some res =>
      rw [hd] at hc
      exfalso
      have hex : ∃ e ∈ entries t, p.isPrefixOf e.1 = true := by
        cases res with
        | none => exact hc.2.2 hne
        | some n' => exact hc.2.2.2 hne
      obtain ⟨e, he, hpe⟩ := hex
      rw [hall e he] at hpe
      cases hpe

theorem deletePrefix_hit {t : Node α} (h : WF true t) (p : Key) (res : Option (Node α))
    (hd : deletePrefix true t p = some res) :
    ∃ t', res = some t' ∧ WF true t' ∧ entries t' = (entries t).filter (fun e => !p.isPrefixOf e.1) := by
  have hc := deletePrefix_core true t p h
  rw [hd] at hc
  cases res with
  | none => exact absurd hc.1 (by simp)
  | some t' =>
    obtain ⟨hw, _, hfe, _⟩ := hc
    refine ⟨t', rfl, hw, ?_⟩
    have hs := h.root_seg
    have hs' := hw.root_seg
    simp only [fullEntries, hs, hs', List.nil_append] at hfe
    simpa using hfe

end Node
end JuuriFormal
