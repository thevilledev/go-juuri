/-
Copyright (c) 2026 Ville Vesilehto
SPDX-License-Identifier: MPL-2.0

`Txn.Insert` (txn.go) is correct: on a well-formed tree it returns a
well-formed tree, binds the key to the new value and leaves every other key
as it was, and reports the value it replaced.

The proof is by induction along `insert` from any node, with keys relative to
the end of the node's segment. At each node the result keeps its segment (so
the parent still indexes it by the same label), and its entries are the old
entries updated at the key (`Upd`). The four ways of going on from a node --
descending into the child `rank` found, splitting that child's segment where
the key leaves it, hanging a new leaf under a label no child has, and setting
the node's own value -- each preserve the shape invariant; the branch where
`rank` reports a hit but the child index is out of range cannot occur.
-/
import JuuriFormal.Order

namespace JuuriFormal
namespace Node

variable {α : Type}

/-! ### Association-list lookups -/

private theorem insert_lookup_cons (k k' : Key) (y : α) (l : List (Key × α)) :
    ((k, y) :: l).lookup k' = if k' = k then some y else l.lookup k' := by
  rw [List.lookup_cons]
  by_cases h : k' = k
  · subst h; simp
  · have : (k' == k) = false := by simpa using h
    simp [this, h]

private theorem insert_lookup_none {l : List (Key × α)} {k : Key} (h : ∀ e ∈ l, e.1 ≠ k) :
    l.lookup k = none := by
  induction l with
  | nil => rfl
  | cons e t ih =>
    obtain ⟨k0, y⟩ := e
    rw [insert_lookup_cons]
    have h0 : k ≠ k0 := fun h' => h (k0, y) List.mem_cons_self h'.symm
    simp only [h0, ite_false]
    exact ih (fun e he => h e (List.mem_cons_of_mem _ he))

private theorem insert_lookup_append (k : Key) (l₁ l₂ : List (Key × α)) :
    (l₁ ++ l₂).lookup k = (l₁.lookup k).or (l₂.lookup k) := List.lookup_append

private theorem insert_lookup_prepend (p q : Key) (l : List (Key × α)) :
    (l.map (fun e => (p ++ e.1, e.2))).lookup (p ++ q) = l.lookup q := by
  induction l with
  | nil => rfl
  | cons e t ih =>
    obtain ⟨k0, y⟩ := e
    simp only [List.map_cons]
    rw [insert_lookup_cons, insert_lookup_cons, ih]
    simp [List.append_cancel_left_eq]

private theorem insert_lookup_prepend_none (p k : Key) (l : List (Key × α)) (h : ∀ q, k ≠ p ++ q) :
    (l.map (fun e => (p ++ e.1, e.2))).lookup k = none := by
  apply insert_lookup_none
  intro e he
  simp only [List.mem_map] at he
  obtain ⟨e', _, rfl⟩ := he
  exact fun h' => h e'.1 h'.symm

/-- `l'` is `l` with the key `k` bound to `x`. -/
private def Upd (l' l : List (Key × α)) (k : Key) (x : α) : Prop :=
  ∀ k', l'.lookup k' = if k' = k then some x else l.lookup k'

private theorem Upd.cons (l : List (Key × α)) (k : Key) (x : α) : Upd ((k, x) :: l) l k x :=
  fun k' => insert_lookup_cons k k' x l

private theorem Upd.snoc {l : List (Key × α)} {k : Key} (x : α) (h : ∀ e ∈ l, e.1 ≠ k) :
    Upd (l ++ [(k, x)]) l k x := by
  intro k'
  rw [insert_lookup_append, insert_lookup_cons]
  by_cases hk : k' = k
  · subst hk; simp [insert_lookup_none h]
  · simp [hk]

private theorem Upd.append_left {l₁' l₁ : List (Key × α)} {k : Key} {x : α} (h : Upd l₁' l₁ k x)
    (l₂ : List (Key × α)) : Upd (l₁' ++ l₂) (l₁ ++ l₂) k x := by
  intro k'
  rw [insert_lookup_append, insert_lookup_append, h k']
  by_cases hk : k' = k <;> simp [hk]

private theorem Upd.append_right {l₂' l₂ : List (Key × α)} {k : Key} {x : α} (h : Upd l₂' l₂ k x)
    (l₁ : List (Key × α)) (hk : ∀ e ∈ l₁, e.1 ≠ k) : Upd (l₁ ++ l₂') (l₁ ++ l₂) k x := by
  intro k'
  rw [insert_lookup_append, insert_lookup_append, h k']
  by_cases hk' : k' = k
  · subst hk'; simp [insert_lookup_none hk]
  · simp [hk']

private theorem Upd.prepend {l' l : List (Key × α)} {q : Key} {x : α} (h : Upd l' l q x) (p : Key) :
    Upd (l'.map (fun e => (p ++ e.1, e.2))) (l.map (fun e => (p ++ e.1, e.2))) (p ++ q) x := by
  intro k'
  by_cases hp : ∃ r, k' = p ++ r
  · obtain ⟨r, rfl⟩ := hp
    rw [insert_lookup_prepend, insert_lookup_prepend, h r]
    simp [List.append_cancel_left_eq]
  · have hp' : ∀ r, k' ≠ p ++ r := fun r hr => hp ⟨r, hr⟩
    rw [insert_lookup_prepend_none _ _ _ hp', insert_lookup_prepend_none _ _ _ hp']
    have : k' ≠ p ++ q := hp' q
    simp [this]

/-! ### `lcp` -/

private theorem insert_lcp_append_self (p q : Key) : lcp (p ++ q) p = p.length := by
  induction p with
  | nil => cases q <;> rfl
  | cons a t ih => simp [lcp, ih]

private theorem insert_lcp_le_left (a b : Key) : lcp a b ≤ a.length := by
  induction a generalizing b with
  | nil => cases b <;> simp [lcp]
  | cons x xs ih =>
    cases b with
    | nil => simp [lcp]
    | cons y ys =>
      simp only [lcp]
      have := ih ys
      split <;> simp <;> omega

private theorem insert_lcp_le_right (a b : Key) : lcp a b ≤ b.length := by
  induction a generalizing b with
  | nil => cases b <;> simp [lcp]
  | cons x xs ih =>
    cases b with
    | nil => simp [lcp]
    | cons y ys =>
      simp only [lcp]
      have := ih ys
      split <;> simp <;> omega

private theorem insert_lcp_take (a b : Key) : a.take (lcp a b) = b.take (lcp a b) := by
  induction a generalizing b with
  | nil => cases b <;> simp [lcp]
  | cons x xs ih =>
    cases b with
    | nil => simp [lcp]
    | cons y ys =>
      simp only [lcp]
      split
      · rename_i h; subst h; simp [ih ys]
      · simp

private theorem insert_lcp_drop_ne (a b : Key) (ha : lcp a b < a.length) (hb : lcp a b < b.length) :
    (a.drop (lcp a b)).headD 0 ≠ (b.drop (lcp a b)).headD 0 := by
  induction a generalizing b with
  | nil => simp at ha
  | cons x xs ih =>
    cases b with
    | nil => simp at hb
    | cons y ys =>
      simp only [lcp] at *
      split
      · rename_i h
        simp only [h, ite_true, List.length_cons] at ha hb
        simp only [List.drop_succ_cons]
        exact ih ys (by omega) (by omega)
      · rename_i h
        simpa using h

private theorem insert_lcp_eq_len {a b : Key} (h : lcp a b = b.length) : a = b ++ a.drop b.length := by
  have ht := insert_lcp_take a b
  rw [h, List.take_length] at ht
  calc a = a.take b.length ++ a.drop b.length := (List.take_append_drop _ _).symm
    _ = b ++ a.drop b.length := by rw [ht]

/-! ### Nodes and children -/

private theorem insert_wf_iff {r : Bool} {s : Key} {v : Option α} {kids : List (Node α)} :
    WF r (mk s v kids) ↔ (r = true → s = []) ∧ (r = false → s ≠ [] ∧ (v = none → 2 ≤ kids.length)) ∧
      kids.Pairwise (fun a b => a.lbl < b.lbl) ∧ (∀ c ∈ kids, WF false c) := by
  constructor
  · intro h
    cases h with
    | mk h1 h2 h3 h4 => exact ⟨h1, h2, List.pairwise_map.mp h3, h4⟩
  · rintro ⟨h1, h2, h3, h4⟩
    exact WF.mk h1 h2 (List.pairwise_map.mpr h3) h4

private theorem insert_fullEntries_mk (s : Key) (v : Option α) (kids : List (Node α)) :
    fullEntries (mk s v kids) = (entries (mk s v kids)).map (fun e => (s ++ e.1, e.2)) := rfl

/-- Every key below a list of well-formed children starts with a child's label. -/
private theorem insert_flat_key {kids : List (Node α)} (hw : ∀ c ∈ kids, WF false c)
    {e : Key × α} (he : e ∈ kids.flatMap fullEntries) : ∃ c ∈ kids, ∃ rest, e.1 = c.lbl :: rest := by
  obtain ⟨c, hc, hce⟩ := List.mem_flatMap.mp he
  exact ⟨c, hc, fullEntries_head (hw c hc).seg_ne_nil e hce⟩

private theorem insert_flat_ne_nil {kids : List (Node α)} (hw : ∀ c ∈ kids, WF false c) :
    ∀ e ∈ kids.flatMap fullEntries, e.1 ≠ [] := by
  intro e he
  obtain ⟨c, _, rest, h⟩ := insert_flat_key hw he
  rw [h]; simp

private theorem insert_flat_ne {kids : List (Node α)} (hw : ∀ c ∈ kids, WF false c) {b : Nat}
    (hb : ∀ c ∈ kids, c.lbl ≠ b) (rest : Key) : ∀ e ∈ kids.flatMap fullEntries, e.1 ≠ b :: rest := by
  intro e he
  obtain ⟨c, hc, rest', h⟩ := insert_flat_key hw he
  rw [h]
  intro h'
  exact hb c hc (List.cons.inj h').1

private theorem insert_vpart_ne (v : Option α) (b : Nat) (rest : Key) :
    ∀ e ∈ (v.map (fun x => (([] : Key), x))).toList, e.1 ≠ b :: rest := by
  intro e he
  cases v with
  | none => simp at he
  | some y =>
    simp at he
    subst he
    simp

/-- Sorted children split at a label: those below it, and those at or above. -/
private theorem insert_split_kids {kids : List (Node α)} (hs : kids.Pairwise (fun a b => a.lbl < b.lbl))
    (b : Nat) : ∃ A C, kids = A ++ C ∧ A.length = (rankOf kids b).1 ∧ (∀ a ∈ A, a.lbl < b) ∧
      (∀ d ∈ C, b ≤ d.lbl) := by
  induction kids with
  | nil => exact ⟨[], [], rfl, rfl, by simp, by simp⟩
  | cons a t ih =>
    rw [List.pairwise_cons] at hs
    obtain ⟨A, C, rfl, hA, hlt, hge⟩ := ih hs.2
    by_cases hab : a.lbl < b
    · refine ⟨a :: A, C, rfl, ?_, ?_, hge⟩
      · simp only [rankOf, List.countP_cons] at hA ⊢
        simp [hab, hA]
      · intro y hy
        rcases List.mem_cons.mp hy with rfl | hy
        · exact hab
        · exact hlt y hy
    · refine ⟨[], a :: (A ++ C), rfl, ?_, by simp, ?_⟩
      · simp only [rankOf, List.countP_cons, hab, decide_false]
        have : (A ++ C).countP (fun c => decide (c.lbl < b)) = 0 := by
          rw [List.countP_eq_zero]
          intro y hy
          have := hs.1 y hy
          simp; omega
        simp [this]
      · intro y hy
        rcases List.mem_cons.mp hy with rfl | hy
        · omega
        · have := hs.1 y hy; omega

private theorem insert_getKid_some {kids : List (Node α)} {i : Nat} {c : Node α} {hc : c ∈ kids}
    (h : getKid kids i = some ⟨c, hc⟩) : kids[i]? = some c := by
  unfold getKid at h
  split at h
  · simp at h
  · rename_i c' heq
    simp at h
    rw [heq, h]

private theorem insert_getKid_none {kids : List (Node α)} {i : Nat} (h : getKid kids i = none) :
    kids.length ≤ i := by
  unfold getKid at h
  split at h
  · rename_i heq
    exact List.getElem?_eq_none_iff.mp heq
  · simp at h

private theorem insert_rank_lt {kids : List (Node α)} {b : Nat} (hf : (rankOf kids b).2 = true) :
    (rankOf kids b).1 < kids.length := by
  simp only [rankOf, List.any_eq_true, decide_eq_true_eq] at hf ⊢
  obtain ⟨c, hc, hcb⟩ := hf
  have hle : kids.countP (fun c => decide (c.lbl < b)) ≤ kids.length := List.countP_le_length
  have hne : kids.countP (fun c => decide (c.lbl < b)) ≠ kids.length := by
    intro heq
    have := List.countP_eq_length.mp heq c hc
    simp at this; omega
  omega

/-- The child `rank` finds, and the children on either side of it. -/
private theorem insert_found {kids : List (Node α)} (hs : kids.Pairwise (fun a b => a.lbl < b.lbl))
    {b : Nat} {c : Node α} (hf : (rankOf kids b).2 = true) (hc : kids[(rankOf kids b).1]? = some c) :
    ∃ A C, kids = A ++ c :: C ∧ A.length = (rankOf kids b).1 ∧ c.lbl = b ∧ (∀ a ∈ A, a.lbl < b) ∧
      (∀ d ∈ C, b < d.lbl) := by
  obtain ⟨A, C, hk, hA, hlt, hge⟩ := insert_split_kids hs b
  have hs' := hs
  rw [hk] at hs'
  rw [← hA, hk, List.getElem?_append_right (Nat.le_refl _), Nat.sub_self] at hc
  cases C with
  | nil => simp at hc
  | cons c0 C =>
    simp at hc
    subst hc
    rw [List.pairwise_append, List.pairwise_cons] at hs'
    have hcb : c0.lbl = b := by
      simp only [rankOf, List.any_eq_true, decide_eq_true_eq] at hf
      obtain ⟨d, hd, hdb⟩ := hf
      rw [hk] at hd
      rcases List.mem_append.mp hd with hd | hd
      · have := hlt d hd; omega
      · rcases List.mem_cons.mp hd with rfl | hd
        · exact hdb
        · have h1 := hs'.2.1.1 d hd
          have h2 := hge c0 List.mem_cons_self
          omega
    refine ⟨A, C, hk, hA, hcb, hlt, ?_⟩
    intro d hd
    have := hs'.2.1.1 d hd
    omega

/-- No child has the label: the children below it and those above. -/
private theorem insert_notfound {kids : List (Node α)} (hs : kids.Pairwise (fun a b => a.lbl < b.lbl))
    {b : Nat} (hf : ¬(rankOf kids b).2 = true) :
    ∃ A C, kids = A ++ C ∧ A.length = (rankOf kids b).1 ∧ (∀ a ∈ A, a.lbl < b) ∧
      (∀ d ∈ C, b < d.lbl) := by
  obtain ⟨A, C, hk, hA, hlt, hge⟩ := insert_split_kids hs b
  refine ⟨A, C, hk, hA, hlt, ?_⟩
  intro d hd
  have h1 := hge d hd
  have h2 : d.lbl ≠ b := by
    intro h
    apply hf
    simp only [rankOf, List.any_eq_true, decide_eq_true_eq]
    exact ⟨d, by rw [hk]; exact List.mem_append_right _ hd, h⟩
  omega

private theorem insert_sorted_mid {A C : List (Node α)} {m : Node α}
    (hA : A.Pairwise (fun a b => a.lbl < b.lbl)) (hC : C.Pairwise (fun a b => a.lbl < b.lbl))
    (hAm : ∀ a ∈ A, a.lbl < m.lbl) (hmC : ∀ d ∈ C, m.lbl < d.lbl) :
    (A ++ m :: C).Pairwise (fun a b => a.lbl < b.lbl) := by
  rw [List.pairwise_append, List.pairwise_cons]
  refine ⟨hA, ⟨hmC, hC⟩, ?_⟩
  intro a ha d hd
  rcases List.mem_cons.mp hd with rfl | hd
  · exact hAm a ha
  · exact Nat.lt_trans (hAm a ha) (hmC d hd)

/-- Replacing the child found under `b` by one with the same label. -/
private theorem insert_replace {r : Bool} {s : Key} {v : Option α} {A C : List (Node α)}
    {c c' : Node α} {b : Nat} {rest : Key} {x : α}
    (h : WF r (mk s v (A ++ c :: C))) (hcb : c.lbl = b) (hA : ∀ a ∈ A, a.lbl < b)
    (hC : ∀ d ∈ C, b < d.lbl) (hw : WF false c') (hl : c'.lbl = c.lbl)
    (hu : Upd (fullEntries c') (fullEntries c) (b :: rest) x) :
    WF r (mk s v (A ++ c' :: C)) ∧
      Upd (entries (mk s v (A ++ c' :: C))) (entries (mk s v (A ++ c :: C))) (b :: rest) x ∧
      (entries (mk s v (A ++ c :: C))).lookup (b :: rest) = (fullEntries c).lookup (b :: rest) := by
  obtain ⟨h1, h2, h3, h4⟩ := insert_wf_iff.mp h
  rw [List.pairwise_append, List.pairwise_cons] at h3
  have hwA : ∀ a ∈ A, WF false a := fun a ha => h4 a (List.mem_append_left _ ha)
  have hwC : ∀ d ∈ C, WF false d := fun d hd => h4 d (List.mem_append_right _ (List.mem_cons_of_mem _ hd))
  have hkA : ∀ e ∈ A.flatMap fullEntries, e.1 ≠ b :: rest :=
    insert_flat_ne hwA (fun a ha => Nat.ne_of_lt (hA a ha)) rest
  have hkC : ∀ e ∈ C.flatMap fullEntries, e.1 ≠ b :: rest :=
    insert_flat_ne hwC (fun d hd => Nat.ne_of_gt (hC d hd)) rest
  refine ⟨?_, ?_, ?_⟩
  · refine insert_wf_iff.mpr ⟨h1, fun hr => ⟨(h2 hr).1, fun hv => by simpa using (h2 hr).2 hv⟩, ?_, ?_⟩
    · refine insert_sorted_mid h3.1 h3.2.1.2 ?_ ?_
      · intro a ha; rw [hl, hcb]; exact hA a ha
      · intro d hd; rw [hl, hcb]; exact hC d hd
    · intro d hd
      rcases List.mem_append.mp hd with hd | hd
      · exact hwA d hd
      · rcases List.mem_cons.mp hd with rfl | hd
        · exact hw
        · exact hwC d hd
  · rw [entries_mk, entries_mk, List.flatMap_append, List.flatMap_append, List.flatMap_cons,
      List.flatMap_cons]
    refine Upd.append_right ?_ _ (insert_vpart_ne v b rest)
    refine Upd.append_right ?_ _ hkA
    exact Upd.append_left hu _
  · rw [entries_mk, List.flatMap_append, List.flatMap_cons, insert_lookup_append,
      insert_lookup_append, insert_lookup_append, insert_lookup_none (insert_vpart_ne v b rest),
      insert_lookup_none hkA, insert_lookup_none hkC]
    simp

/-- Hanging a new leaf under a label no child has. -/
private theorem insert_add {r : Bool} {s : Key} {v : Option α} {A C : List (Node α)}
    {b : Nat} {rest : Key} {x : α}
    (h : WF r (mk s v (A ++ C))) (hA : ∀ a ∈ A, a.lbl < b) (hC : ∀ d ∈ C, b < d.lbl) :
    WF r (mk s v (A ++ mk (b :: rest) (some x) [] :: C)) ∧
      Upd (entries (mk s v (A ++ mk (b :: rest) (some x) [] :: C))) (entries (mk s v (A ++ C)))
        (b :: rest) x ∧
      (entries (mk s v (A ++ C))).lookup (b :: rest) = none := by
  obtain ⟨h1, h2, h3, h4⟩ := insert_wf_iff.mp h
  rw [List.pairwise_append] at h3
  have hwA : ∀ a ∈ A, WF false a := fun a ha => h4 a (List.mem_append_left _ ha)
  have hwC : ∀ d ∈ C, WF false d := fun d hd => h4 d (List.mem_append_right _ hd)
  have hkA : ∀ e ∈ A.flatMap fullEntries, e.1 ≠ b :: rest :=
    insert_flat_ne hwA (fun a ha => Nat.ne_of_lt (hA a ha)) rest
  have hkC : ∀ e ∈ C.flatMap fullEntries, e.1 ≠ b :: rest :=
    insert_flat_ne hwC (fun d hd => Nat.ne_of_gt (hC d hd)) rest
  have hleaf : (mk (b :: rest) (some x) [] : Node α).lbl = b := rfl
  refine ⟨?_, ?_, ?_⟩
  · refine insert_wf_iff.mpr ⟨h1, fun hr => ⟨(h2 hr).1, fun hv => ?_⟩, ?_, ?_⟩
    · have := (h2 hr).2 hv
      simp at this ⊢; omega
    · refine insert_sorted_mid h3.1 h3.2.1 ?_ ?_
      · intro a ha; rw [hleaf]; exact hA a ha
      · intro d hd; rw [hleaf]; exact hC d hd
    · intro d hd
      rcases List.mem_append.mp hd with hd | hd
      · exact hwA d hd
      · rcases List.mem_cons.mp hd with rfl | hd
        · exact insert_wf_iff.mpr ⟨by simp, fun _ => ⟨by simp, by simp⟩, by simp, by simp⟩
        · exact hwC d hd
  · rw [entries_mk, entries_mk, List.flatMap_append, List.flatMap_append, List.flatMap_cons]
    refine Upd.append_right ?_ _ (insert_vpart_ne v b rest)
    refine Upd.append_right ?_ _ hkA
    have : fullEntries (mk (b :: rest) (some x) [] : Node α) = [(b :: rest, x)] := by
      rw [insert_fullEntries_mk, entries_mk]; simp
    rw [this]
    exact Upd.cons _ _ _
  · rw [entries_mk, List.flatMap_append, insert_lookup_append, insert_lookup_append,
      insert_lookup_none (insert_vpart_ne v b rest), insert_lookup_none hkA, insert_lookup_none hkC]
    rfl

private theorem insert_fullEntries_key {p : Key} {cv : Option α} {ckids : List (Node α)}
    {e : Key × α} (he : e ∈ fullEntries (mk p cv ckids)) : ∃ q, e.1 = p ++ q := by
  rw [insert_fullEntries_mk, List.mem_map] at he
  obtain ⟨e', _, rfl⟩ := he
  exact ⟨e'.1, rfl⟩

/-- The split: the key leaves the child's segment after `j` bytes. -/
private theorem insert_split_spec {p : Key} {cv : Option α} {ckids : List (Node α)} {b : Nat}
    {rest : Key} {x : α} (hw : WF false (mk p cv ckids)) (hcb : (mk p cv ckids : Node α).lbl = b)
    (hne : ¬lcp (b :: rest) p = p.length) (sp : Node α)
    (hsp : sp = match (b :: rest).drop (lcp (b :: rest) p) with
      | [] => mk (p.take (lcp (b :: rest) p)) (some x) [mk (p.drop (lcp (b :: rest) p)) cv ckids]
      | restS => mk (p.take (lcp (b :: rest) p)) none
          (if (mk restS (some x) [] : Node α).lbl < (mk (p.drop (lcp (b :: rest) p)) cv ckids : Node α).lbl
           then [mk restS (some x) [], mk (p.drop (lcp (b :: rest) p)) cv ckids]
           else [mk (p.drop (lcp (b :: rest) p)) cv ckids, mk restS (some x) []])) :
    WF false sp ∧ sp.lbl = b ∧ Upd (fullEntries sp) (fullEntries (mk p cv ckids)) (b :: rest) x ∧
      (fullEntries (mk p cv ckids)).lookup (b :: rest) = none := by
  obtain ⟨_, hw2, hw3, hw4⟩ := insert_wf_iff.mp hw
  obtain ⟨hp, hcv⟩ := hw2 rfl
  have hle := insert_lcp_le_right (b :: rest) p
  have hles := insert_lcp_le_left (b :: rest) p
  have htake := insert_lcp_take (b :: rest) p
  have hdiff := insert_lcp_drop_ne (b :: rest) p
  have hnotin : ∀ e ∈ fullEntries (mk p cv ckids), e.1 ≠ b :: rest := by
    intro e he heq
    obtain ⟨q, hq⟩ := insert_fullEntries_key he
    rw [heq] at hq
    rw [hq, insert_lcp_append_self] at hne
    exact hne rfl
  have hpos : 1 ≤ lcp (b :: rest) p := by
    cases p with
    | nil => exact absurd rfl hp
    | cons b' ps =>
      simp [lbl] at hcb
      subst hcb
      simp [lcp]
  have hlblp : p.headD 0 = b := hcb
  generalize hj : lcp (b :: rest) p = j at *
  have hjp : j < p.length := by omega
  have htr : WF false (mk (p.drop j) cv ckids : Node α) := by
    refine insert_wf_iff.mpr ⟨by simp, fun _ => ⟨?_, hcv⟩, hw3, hw4⟩
    intro h0
    have := List.drop_eq_nil_iff.mp h0
    omega
  have htake_ne : p.take j ≠ [] := by
    intro h0
    rcases List.take_eq_nil_iff.mp h0 with h0 | h0
    · omega
    · exact hp h0
  have hlbl : ∀ (sv : Option α) (skids : List (Node α)), (mk (p.take j) sv skids : Node α).lbl = b := by
    intro sv skids
    rw [← hlblp]
    cases p with
    | nil => exact absurd rfl hp
    | cons b' ps =>
      obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
      simp [lbl]
  have hfe_tr : (fullEntries (mk (p.drop j) cv ckids : Node α)).map (fun e => (p.take j ++ e.1, e.2)) =
      fullEntries (mk p cv ckids) := by
    rw [insert_fullEntries_mk, insert_fullEntries_mk, List.map_map]
    have : entries (mk (p.drop j) cv ckids : Node α) = entries (mk p cv ckids) := by
      rw [entries_mk, entries_mk]
    rw [this]
    apply List.map_congr_left
    intro e _
    simp only [Function.comp, ← List.append_assoc, List.take_append_drop]
  cases hd : List.drop j (b :: rest) with
  | nil =>
    rw [hd] at hsp
    simp only at hsp
    subst hsp
    have hsearch : b :: rest = p.take j := by
      rw [← htake, ← List.take_append_drop j (b :: rest), hd, List.append_nil, List.take_take,
        Nat.min_self]
    refine ⟨?_, hlbl _ _, ?_, insert_lookup_none hnotin⟩
    · refine insert_wf_iff.mpr ⟨by simp, fun _ => ⟨htake_ne, by simp⟩, by simp, ?_⟩
      intro d hd
      simp at hd
      subst hd
      exact htr
    · have : fullEntries (mk (p.take j) (some x) [mk (p.drop j) cv ckids] : Node α) =
          (b :: rest, x) :: fullEntries (mk p cv ckids) := by
        rw [insert_fullEntries_mk, entries_mk, ← hfe_tr, hsearch]
        simp
      rw [this]
      exact Upd.cons _ _ _
  | cons r0 rs =>
    rw [hd] at hsp
    simp only at hsp
    subst hsp
    have hsearch : b :: rest = p.take j ++ r0 :: rs := by
      rw [← htake, ← hd, List.take_append_drop]
    have hjs : j < (b :: rest).length := by
      have := congrArg List.length hd
      simp at this ⊢
      omega
    have hne' : (mk (r0 :: rs) (some x) [] : Node α).lbl ≠ (mk (p.drop j) cv ckids : Node α).lbl := by
      have := hdiff (by omega) (by omega)
      rw [hd] at this
      exact this
    have hadd : WF false (mk (r0 :: rs) (some x) [] : Node α) :=
      insert_wf_iff.mpr ⟨by simp, fun _ => ⟨by simp, by simp⟩, by simp, by simp⟩
    have hfa : fullEntries (mk (r0 :: rs) (some x) [] : Node α) = [(r0 :: rs, x)] := by
      rw [insert_fullEntries_mk, entries_mk]; simp
    refine ⟨?_, hlbl _ _, ?_, insert_lookup_none hnotin⟩
    · refine insert_wf_iff.mpr ⟨by simp, fun _ => ⟨htake_ne, ?_⟩, ?_, ?_⟩
      · intro _; split <;> simp
      · split
        · rename_i hlt
          simpa using hlt
        · rename_i hlt
          simp only [List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false, forall_eq]
          exact ⟨by omega, fun _ h => h.elim, List.Pairwise.nil⟩
      · intro d hd'
        split at hd' <;> simp at hd' <;> rcases hd' with rfl | rfl <;> assumption
    · split
      · have : fullEntries (mk (p.take j) none [mk (r0 :: rs) (some x) [], mk (p.drop j) cv ckids] : Node α) =
            (b :: rest, x) :: fullEntries (mk p cv ckids) := by
          rw [insert_fullEntries_mk, entries_mk, ← hfe_tr, hsearch]
          simp [hfa]
        rw [this]
        exact Upd.cons _ _ _
      · have : fullEntries (mk (p.take j) none [mk (p.drop j) cv ckids, mk (r0 :: rs) (some x) []] : Node α) =
            fullEntries (mk p cv ckids) ++ [(b :: rest, x)] := by
          rw [insert_fullEntries_mk, entries_mk, ← hfe_tr, hsearch]
          simp [hfa]
        rw [this]
        exact Upd.snoc _ hnotin

private theorem insert_set_mid (A C : List (Node α)) (c c' : Node α) :
    (A ++ c :: C).set A.length c' = A ++ c' :: C := by
  rw [List.set_append_right _ _ (Nat.le_refl _), Nat.sub_self, List.set_cons_zero]

private theorem insert_insertIdx_mid (A C : List (Node α)) (c : Node α) :
    (A ++ C).insertIdx A.length c = A ++ c :: C := by
  induction A with
  | nil => simp
  | cons a t ih => simp [List.insertIdx_succ_cons, ih]

/-- The whole specification of `insert` from any node, keys relative to the
end of its segment. -/
private theorem insert_spec (n : Node α) (k : Key) (x : α) :
    ∀ r, WF r n → WF r (insert n k x).1 ∧ (insert n k x).1.seg = n.seg ∧
      Upd (entries (insert n k x).1) (entries n) k x ∧ (insert n k x).2 = (entries n).lookup k := by
  fun_induction insert n k x with
  | case1 s v kids x =>
    intro r0 h
    obtain ⟨h1, h2, h3, h4⟩ := insert_wf_iff.mp h
    refine ⟨insert_wf_iff.mpr ⟨h1, fun hr => ⟨(h2 hr).1, by simp⟩, h3, h4⟩, rfl, ?_, ?_⟩
    · intro k'
      dsimp only
      rw [entries_mk, entries_mk]
      simp only [Option.map_some, Option.toList_some, List.singleton_append]
      rw [insert_lookup_cons]
      by_cases hk : k' = []
      · simp [hk]
      · simp only [hk, ite_false]
        cases v with
        | none => simp
        | some y => simp [insert_lookup_cons, hk]
    · dsimp only
      rw [entries_mk]
      cases v with
      | none =>
        simp only [Option.map_none, Option.toList_none, List.nil_append]
        exact (insert_lookup_none (insert_flat_ne_nil h4)).symm
      | some y => simp
  | case2 s v kids b rest x hf hg =>
    intro r0 _
    exfalso
    have := insert_rank_lt hf
    have := insert_getKid_none hg
    omega
  | case3 s v kids b rest x hf c hc hg search common hcommon res ih =>
    intro r0 h
    have hres : res = c.insert (List.drop common search) x := rfl
    have hsearch : search = b :: rest := rfl
    have hcom : common = lcp search c.seg := rfl
    clear_value res common search
    subst hres hsearch hcom
    obtain ⟨h1, h2, h3, h4⟩ := insert_wf_iff.mp h
    obtain ⟨ihw, ihs, ihu, iho⟩ := ih false (h4 c hc)
    obtain ⟨A, C, hk, hA, hcb, hlt, hgt⟩ := insert_found h3 hf (insert_getKid_some hg)
    have hsplit : b :: rest = c.seg ++ List.drop (lcp (b :: rest) c.seg) (b :: rest) := by
      rw [hcommon]; exact insert_lcp_eq_len hcommon
    generalize List.drop (lcp (b :: rest) c.seg) (b :: rest) = q at hsplit ihw ihs ihu iho
    generalize c.insert q x = c' at ihw ihs ihu iho
    have hu : Upd (fullEntries c'.1) (fullEntries c) (b :: rest) x := by
      unfold fullEntries
      rw [ihs, hsplit]
      exact Upd.prepend ihu c.seg
    have hl : c'.1.lbl = c.lbl := by unfold lbl; rw [ihs]
    subst hk
    dsimp only
    rw [← hA, insert_set_mid]
    obtain ⟨hw', hu', ho'⟩ := insert_replace h hcb hlt hgt ihw hl hu
    refine ⟨hw', rfl, hu', ?_⟩
    rw [ho', iho]
    unfold fullEntries
    rw [hsplit, insert_lookup_prepend]
  | case4 s v kids b rest x hf c hc hg search common hcommon trimmed split =>
    intro r0 h
    have hsearch : search = b :: rest := rfl
    have hcom : common = lcp search c.seg := rfl
    have hsp : split = match List.drop (lcp (b :: rest) c.seg) (b :: rest) with
      | [] => mk (List.take (lcp (b :: rest) c.seg) c.seg) (some x)
          [mk (List.drop (lcp (b :: rest) c.seg) c.seg) c.val c.kids]
      | restS => mk (List.take (lcp (b :: rest) c.seg) c.seg) none
          (if (mk restS (some x) [] : Node α).lbl <
              (mk (List.drop (lcp (b :: rest) c.seg) c.seg) c.val c.kids : Node α).lbl
           then [mk restS (some x) [], mk (List.drop (lcp (b :: rest) c.seg) c.seg) c.val c.kids]
           else [mk (List.drop (lcp (b :: rest) c.seg) c.seg) c.val c.kids, mk restS (some x) []]) := by
      rfl
    clear_value split trimmed common search
    subst hsearch hcom
    obtain ⟨h1, h2, h3, h4⟩ := insert_wf_iff.mp h
    obtain ⟨A, C, hk, hA, hcb, hlt, hgt⟩ := insert_found h3 hf (insert_getKid_some hg)
    have hwc := h4 c hc
    subst hk
    dsimp only
    rw [← hA, insert_set_mid]
    clear hg hc
    cases c with
    | mk p cv ckids =>
      simp only [seg_mk, val_mk, kids_mk] at hsp hcommon
      obtain ⟨hsw, hsl, hsu, hsn⟩ := insert_split_spec hwc hcb hcommon split hsp
      obtain ⟨hw', hu', ho'⟩ := insert_replace h hcb hlt hgt hsw (hsl.trans hcb.symm) hsu
      exact ⟨hw', rfl, hu', by rw [ho', hsn]⟩
  | case5 s v kids b rest x hf =>
    intro r0 h
    obtain ⟨h1, h2, h3, h4⟩ := insert_wf_iff.mp h
    obtain ⟨A, C, hk, hA, hlt, hgt⟩ := insert_notfound h3 hf
    subst hk
    dsimp only
    rw [← hA, insert_insertIdx_mid]
    obtain ⟨hw', hu', ho'⟩ := insert_add h hlt hgt
    exact ⟨hw', rfl, hu', ho'.symm⟩

theorem insert_wf {t : Node α} (h : WF true t) (k : Key) (x : α) : WF true (insert t k x).1 :=
  (insert_spec t k x true h).1

theorem insert_lookup {t : Node α} (h : WF true t) (k : Key) (x : α) (k' : Key) :
    (entries (insert t k x).1).lookup k' = if k' = k then some x else (entries t).lookup k' :=
  (insert_spec t k x true h).2.2.1 k'

theorem insert_old {t : Node α} (h : WF true t) (k : Key) (x : α) :
    (insert t k x).2 = (entries t).lookup k :=
  (insert_spec t k x true h).2.2.2

end Node
end JuuriFormal
