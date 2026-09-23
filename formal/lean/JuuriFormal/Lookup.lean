/-
Copyright (c) 2026 Ville Vesilehto
SPDX-License-Identifier: MPL-2.0

The lookups of tree.go against the abstract content: `Get` finds exactly
the value `entries` maps the key to, `LongestPrefix` the value of the
longest stored key that is a prefix of the search key, and
`FirstPrefix` / `LastPrefix` the first and last value (in key order) among
the keys that start with the prefix.

All four walk one path down the tree. The common step is
`lookup_kids_filter_some`: of a node's children, only the one found under
the next search byte by `rank` can hold keys that start with that byte.
-/
import JuuriFormal.Order

namespace JuuriFormal
namespace Node

variable {α : Type}

/-! ### Finding the child under a byte -/

theorem lookup_getKid_eq {kids : List (Node α)} {i : Nat} {c : Node α} (h : kids[i]? = some c) :
    ∃ hc, getKid kids i = some ⟨c, hc⟩ := by
  refine ⟨List.mem_of_getElem? h, ?_⟩
  unfold getKid
  split
  · simp_all
  · rename_i c' h'
    rw [h] at h'
    cases h'
    rfl

/-- With ascending labels, `rank` finds the one child labelled `b`, and splits
the children around it. -/
theorem lookup_rank_found {kids : List (Node α)} {b : Nat}
    (hs : (kids.map lbl).Pairwise (· < ·)) (hr : (rankOf kids b).2 = true) :
    ∃ l1 c l2, kids = l1 ++ c :: l2 ∧ (rankOf kids b).1 = l1.length ∧ c.lbl = b ∧
      (∀ c' ∈ l1, c'.lbl < b) ∧ (∀ c' ∈ l2, b < c'.lbl) := by
  simp only [rankOf, List.any_eq_true, decide_eq_true_eq] at hr
  obtain ⟨c, hc, hcb⟩ := hr
  obtain ⟨l1, l2, rfl⟩ := List.append_of_mem hc
  rw [List.map_append, List.map_cons, List.pairwise_append, List.pairwise_cons] at hs
  obtain ⟨_, ⟨h2, _⟩, h3⟩ := hs
  have hl1 : ∀ c' ∈ l1, c'.lbl < b := fun c' hc' =>
    hcb ▸ h3 _ (List.mem_map_of_mem hc') _ List.mem_cons_self
  have hl2 : ∀ c' ∈ l2, b < c'.lbl := fun c' hc' => hcb ▸ h2 _ (List.mem_map_of_mem hc')
  refine ⟨l1, c, l2, rfl, ?_, hcb, hl1, hl2⟩
  simp only [rankOf, List.countP_append, List.countP_cons]
  rw [List.countP_eq_length.mpr, List.countP_eq_zero.mpr]
  · simp [hcb]
  · intro a ha
    have := hl2 a ha
    simp
    omega
  · intro a ha
    simpa using hl1 a ha

/-- A child whose label is not `b` holds no key accepted by a filter that only
accepts keys starting with `b`. -/
theorem lookup_fullEntries_other {c : Node α} {Q : Key × α → Bool} {b : Nat}
    (hne : c.seg ≠ []) (hQ : ∀ x r a, Q (x :: r, a) = true → x = b) (hcb : c.lbl ≠ b) :
    (fullEntries c).filter Q = [] := by
  rw [List.filter_eq_nil_iff]
  intro e he hQe
  obtain ⟨r, hr⟩ := fullEntries_head hne e he
  obtain ⟨k, a⟩ := e
  simp only at hr
  subst hr
  exact hcb (hQ _ _ _ hQe)

theorem lookup_kids_filter_none {kids : List (Node α)} {Q : Key × α → Bool} {b : Nat}
    (hne : ∀ c ∈ kids, c.seg ≠ []) (hQ : ∀ x r a, Q (x :: r, a) = true → x = b)
    (hr : (rankOf kids b).2 = false) :
    (kids.flatMap fullEntries).filter Q = [] := by
  rw [List.filter_flatMap, List.flatMap_eq_nil_iff]
  intro c hc
  simp only [rankOf, List.any_eq_false, decide_eq_true_eq] at hr
  exact lookup_fullEntries_other (hne c hc) hQ (hr c hc)

theorem lookup_kids_filter_some {kids : List (Node α)} {Q : Key × α → Bool} {b : Nat}
    (hs : (kids.map lbl).Pairwise (· < ·))
    (hne : ∀ c ∈ kids, c.seg ≠ []) (hQ : ∀ x r a, Q (x :: r, a) = true → x = b)
    (hr : (rankOf kids b).2 = true) :
    ∃ c hc, getKid kids (rankOf kids b).1 = some ⟨c, hc⟩ ∧
      (kids.flatMap fullEntries).filter Q = (fullEntries c).filter Q := by
  obtain ⟨l1, c, l2, hk, hi, hcb, hl1, hl2⟩ := lookup_rank_found hs hr
  have hget : kids[(rankOf kids b).1]? = some c := by
    rw [hi, hk, List.getElem?_append_right (Nat.le_refl _)]
    simp
  obtain ⟨hc, hg⟩ := lookup_getKid_eq hget
  refine ⟨c, hc, hg, ?_⟩
  rw [List.filter_flatMap, hk, List.flatMap_append, List.flatMap_cons]
  have e1 : l1.flatMap (fun c => (fullEntries c).filter Q) = [] := by
    rw [List.flatMap_eq_nil_iff]
    intro c' hc'
    have := hl1 c' hc'
    exact lookup_fullEntries_other (hne c' (by rw [hk]; simp [hc'])) hQ (by omega)
  have e2 : l2.flatMap (fun c => (fullEntries c).filter Q) = [] := by
    rw [List.flatMap_eq_nil_iff]
    intro c' hc'
    have := hl2 c' hc'
    exact lookup_fullEntries_other (hne c' (by rw [hk]; simp [hc'])) hQ (by omega)
  rw [e1, e2]
  simp

theorem lookup_fullEntries_filter (c : Node α) (Q : Key × α → Bool) :
    (fullEntries c).filter Q =
      ((entries c).filter (fun e => Q (c.seg ++ e.1, e.2))).map (fun e => (c.seg ++ e.1, e.2)) := by
  unfold fullEntries
  rw [List.filter_map]
  rfl

theorem lookup_kids_seg_filter_nil {kids : List (Node α)} {Q : Key × α → Bool}
    (hne : ∀ c ∈ kids, c.seg ≠ []) (hQ : ∀ x r a, Q (x :: r, a) = false) :
    (kids.flatMap fullEntries).filter Q = [] := by
  rw [List.filter_flatMap, List.flatMap_eq_nil_iff]
  intro c hc
  rw [List.filter_eq_nil_iff]
  intro e he hQe
  obtain ⟨r, hr⟩ := fullEntries_head (hne c hc) e he
  obtain ⟨k, a⟩ := e
  simp only at hr
  subst hr
  simp [hQ] at hQe

/-! ### Get -/

theorem lookup_eq_filter (l : List (Key × α)) (k : Key) :
    l.lookup k = (l.filter (fun e => decide (e.1 = k))).head?.map (·.2) := by
  induction l with
  | nil => rfl
  | cons e l ih =>
    obtain ⟨k', x⟩ := e
    by_cases h : k' = k
    · subst h
      simp
    · have h' : (k == k') = false := by
        simp only [beq_eq_false_iff_ne]
        exact fun e => h e.symm
      simp [List.lookup_cons, h', h, ih]

theorem lookup_get_filter {r : Bool} {n : Node α} (h : WF r n) :
    ∀ k, get n k = ((entries n).filter (fun e => decide (e.1 = k))).head?.map (·.2) := by
  induction h with
  | @mk isRoot s v kids h1 h2 hsorted hkids ih =>
    intro k
    have hne : ∀ c ∈ kids, c.seg ≠ [] := fun c hc => (hkids c hc).seg_ne_nil
    rw [entries_mk, List.filter_append]
    cases k with
    | nil =>
      rw [get]
      rw [lookup_kids_seg_filter_nil hne (by intro x r a; simp)]
      cases v <;> simp
    | cons b rest =>
      have hv : (v.map (fun x => (([] : Key), x))).toList.filter
          (fun e => decide (e.1 = b :: rest)) = [] := by cases v <;> simp
      rw [hv, List.nil_append]
      have hQ : ∀ x r a, (fun e : Key × α => decide (e.1 = b :: rest)) (x :: r, a) = true → x = b := by
        intro x r a h
        simp at h
        exact h.1
      cases hr : (rankOf kids b).2 with
      | false =>
        rw [get, lookup_kids_filter_none hne hQ hr]
        simp [hr]
      | true =>
        obtain ⟨c, hc, hg, hf⟩ :=
          lookup_kids_filter_some (Q := fun e => decide (e.1 = b :: rest)) hsorted hne hQ hr
        rw [get, hf, lookup_fullEntries_filter]
        simp only [hr, ↓reduceIte, hg]
        split
        · rename_i hpre
          obtain ⟨d, hd⟩ := (List.isPrefixOf_iff_prefix).mp hpre
          rw [← hd, List.drop_left, ih c hc d]
          simp [List.head?_map, Option.map_map, Function.comp_def]
        · rename_i hpre
          have : (entries c).filter (fun e => decide (c.seg ++ e.1 = b :: rest)) = [] := by
            rw [List.filter_eq_nil_iff]
            intro e _ he
            simp only [decide_eq_true_eq] at he
            exact hpre ((List.isPrefixOf_iff_prefix).mpr ⟨e.1, he⟩)
          simp [this]

/-! ### Longest prefix -/

theorem lookup_isPrefixOf_append (l a b : Key) :
    (l ++ a).isPrefixOf (l ++ b) = a.isPrefixOf b := by
  rw [Bool.eq_iff_iff, List.isPrefixOf_iff_prefix, List.isPrefixOf_iff_prefix,
    List.prefix_append_right_inj]

theorem lookup_longestPrefix_aux {r : Bool} {n : Node α} (h : WF r n) :
    ∀ k best, longestPrefix n k best =
      (((entries n).filter (fun e => e.1.isPrefixOf k)).getLast?.map (·.2)).or best := by
  induction h with
  | @mk isRoot s v kids h1 h2 hsorted hkids ih =>
    intro k best
    have hne : ∀ c ∈ kids, c.seg ≠ [] := fun c hc => (hkids c hc).seg_ne_nil
    have hbest : (if v.isSome then v else best) = v.or best := by cases v <;> rfl
    rw [entries_mk, List.filter_append]
    cases k with
    | nil =>
      rw [longestPrefix]
      rw [lookup_kids_seg_filter_nil hne (by intro x r a; simp), hbest]
      cases v <;> simp
    | cons b rest =>
      have hv : (v.map (fun x => (([] : Key), x))).toList.filter
          (fun e => e.1.isPrefixOf (b :: rest)) = (v.map (fun x => (([] : Key), x))).toList := by
        cases v <;> simp
      have hvl : ((v.map (fun x => (([] : Key), x))).toList.getLast?.map (·.2)) = v := by
        cases v <;> simp
      rw [hv, List.getLast?_append, Option.map_or, hvl]
      have hQ : ∀ x r a, (fun e : Key × α => e.1.isPrefixOf (b :: rest)) (x :: r, a) = true →
          x = b := by
        intro x r a h
        simp [List.isPrefixOf_cons_cons] at h
        exact h.1
      rw [longestPrefix, hbest]
      cases hr : (rankOf kids b).2 with
      | false =>
        rw [lookup_kids_filter_none hne hQ hr]
        simp
      | true =>
        obtain ⟨c, hc, hg, hf⟩ :=
          lookup_kids_filter_some (Q := fun e => e.1.isPrefixOf (b :: rest)) hsorted hne hQ hr
        rw [hf, lookup_fullEntries_filter]
        simp only [↓reduceIte, hg]
        split
        · rename_i hpre
          obtain ⟨d, hd⟩ := (List.isPrefixOf_iff_prefix).mp hpre
          rw [← hd, List.drop_left, ih c hc d]
          simp only [lookup_isPrefixOf_append, List.getLast?_map, Option.map_map]
          rw [Option.or_assoc]
          rfl
        · rename_i hpre
          have : (entries c).filter (fun e => (c.seg ++ e.1).isPrefixOf (b :: rest)) = [] := by
            rw [List.filter_eq_nil_iff]
            intro e _ he
            rw [List.isPrefixOf_iff_prefix] at he
            exact hpre ((List.isPrefixOf_iff_prefix).mpr
              ((List.prefix_append c.seg e.1).trans he))
          simp [this]

/-! ### Seeking a prefix -/

/-- `seekPrefix` finds the node whose entries are, up to a common key prefix,
exactly the entries whose keys start with `p`; and it finds none only when
no key starts with `p`. -/
theorem lookup_seekPrefix_aux {r : Bool} {n : Node α} (h : WF r n) :
    ∀ p, (seekPrefix n p = none → (entries n).filter (fun e => p.isPrefixOf e.1) = []) ∧
      (∀ m, seekPrefix n p = some m → (∃ r', WF r' m) ∧
        ∃ P : Key, (entries n).filter (fun e => p.isPrefixOf e.1) =
          (entries m).map (fun e => (P ++ e.1, e.2))) := by
  induction h with
  | @mk isRoot s v kids h1 h2 hsorted hkids ih =>
    intro p
    have hne : ∀ c ∈ kids, c.seg ≠ [] := fun c hc => (hkids c hc).seg_ne_nil
    cases p with
    | nil =>
      rw [seekPrefix]
      refine ⟨fun h => by simp at h, fun m hm => ?_⟩
      simp only [Option.some.injEq] at hm
      subst hm
      refine ⟨⟨isRoot, WF.mk h1 h2 hsorted hkids⟩, [], ?_⟩
      simp
    | cons b rest =>
      rw [entries_mk, List.filter_append]
      have hv : (v.map (fun x => (([] : Key), x))).toList.filter
          (fun e => (b :: rest).isPrefixOf e.1) = [] := by
        cases v <;> simp
      rw [hv, List.nil_append]
      have hQ : ∀ x r a, (fun e : Key × α => (b :: rest).isPrefixOf e.1) (x :: r, a) = true →
          x = b := by
        intro x r a h
        simp [List.isPrefixOf_cons_cons] at h
        exact h.1.symm
      rw [seekPrefix]
      cases hr : (rankOf kids b).2 with
      | false =>
        rw [lookup_kids_filter_none hne hQ hr]
        simp
      | true =>
        obtain ⟨c, hc, hg, hf⟩ :=
          lookup_kids_filter_some (Q := fun e => (b :: rest).isPrefixOf e.1) hsorted hne hQ hr
        rw [hf, lookup_fullEntries_filter]
        simp only [↓reduceIte, hg]
        split
        · rename_i hpre
          obtain ⟨d, hd⟩ := (List.isPrefixOf_iff_prefix).mp hpre
          rw [← hd, List.drop_left]
          simp only [lookup_isPrefixOf_append]
          obtain ⟨ihn, ihs⟩ := ih c hc d
          refine ⟨fun hs => by rw [ihn hs]; rfl, fun m hm => ?_⟩
          obtain ⟨hwf, P, hP⟩ := ihs m hm
          refine ⟨hwf, c.seg ++ P, ?_⟩
          rw [hP, List.map_map]
          simp [Function.comp_def]
        · rename_i hpre
          split
          · rename_i hlt
            obtain ⟨_, hlt2⟩ := hlt
            have hall : (entries c).filter (fun e => (b :: rest).isPrefixOf (c.seg ++ e.1)) =
                entries c := by
              rw [List.filter_eq_self]
              intro e _
              rw [List.isPrefixOf_iff_prefix] at hlt2 ⊢
              exact hlt2.trans (List.prefix_append c.seg e.1)
            refine ⟨fun h => by simp at h, fun m hm => ?_⟩
            simp only [Option.some.injEq] at hm
            subst hm
            refine ⟨⟨false, hkids c hc⟩, c.seg, ?_⟩
            rw [hall]
          · rename_i hnot
            refine ⟨fun _ => ?_, fun m hm => by simp at hm⟩
            rw [List.map_eq_nil_iff, List.filter_eq_nil_iff]
            intro e _ he
            rw [List.isPrefixOf_iff_prefix] at he
            rcases List.prefix_or_prefix_of_prefix he (List.prefix_append c.seg e.1) with h' | h'
            · have hle := h'.length_le
              by_cases hl : (b :: rest).length < c.seg.length
              · exact hnot ⟨hl, (List.isPrefixOf_iff_prefix).mpr h'⟩
              · have heq := h'.eq_of_length (by omega)
                exact hpre ((List.isPrefixOf_iff_prefix).mpr (heq ▸ List.prefix_refl _))
            · exact hpre ((List.isPrefixOf_iff_prefix).mpr h')

/-! ### First and last entries -/

theorem lookup_entries_ne_nil {r : Bool} {n : Node α} (h : WF r n) : r = false → entries n ≠ [] := by
  induction h with
  | @mk isRoot s v kids h1 h2 hsorted hkids ih =>
    intro hr
    obtain ⟨_, h2⟩ := h2 hr
    rw [entries_mk]
    cases v with
    | some x => simp
    | none =>
      have hlen := h2 rfl
      obtain ⟨c, cs, rfl⟩ : ∃ c cs, kids = c :: cs := by
        cases kids with
        | nil => simp at hlen
        | cons c cs => exact ⟨c, cs, rfl⟩
      have := ih c List.mem_cons_self rfl
      simp [List.flatMap_cons, fullEntries, this]

theorem lookup_minNode {r : Bool} {n : Node α} (h : WF r n) :
    (minNode n).bind val = (entries n).head?.map (·.2) := by
  induction h with
  | @mk isRoot s v kids h1 h2 hsorted hkids ih =>
    rw [minNode, entries_mk]
    cases v with
    | some x => simp
    | none =>
      cases kids with
      | nil => simp [getKid]
      | cons c cs =>
        obtain ⟨hc, hg⟩ := lookup_getKid_eq (kids := c :: cs) (i := 0) (c := c) rfl
        simp only [Option.isSome_none, Bool.false_eq_true, ↓reduceIte, hg]
        rw [ih c List.mem_cons_self]
        have hne := lookup_entries_ne_nil (hkids c List.mem_cons_self) rfl
        obtain ⟨e, es, he⟩ : ∃ e es, entries c = e :: es := by
          cases h : entries c with
          | nil => exact absurd h hne
          | cons e es => exact ⟨e, es, rfl⟩
        simp [List.flatMap_cons, fullEntries, he]

theorem lookup_maxNode {r : Bool} {n : Node α} (h : WF r n) :
    (maxNode n).bind val = (entries n).getLast?.map (·.2) := by
  induction h with
  | @mk isRoot s v kids h1 h2 hsorted hkids ih =>
    rw [maxNode, entries_mk]
    rcases List.eq_nil_or_concat kids with hk | ⟨init, c, hk⟩
    · subst hk
      cases v <;> simp [getKid]
    · subst hk
      have hmem : c ∈ init.concat c := by simp
      have hget : (init.concat c)[(init.concat c).length - 1]? = some c := by simp
      obtain ⟨hc, hg⟩ := lookup_getKid_eq hget
      simp only [hg]
      rw [ih c hmem]
      have hne := lookup_entries_ne_nil (hkids c hmem) rfl
      obtain ⟨x, hx⟩ : ∃ x, (entries c).getLast? = some x := by
        cases h : (entries c).getLast? with
        | none => exact absurd (List.getLast?_eq_none_iff.mp h) hne
        | some x => exact ⟨x, rfl⟩
      simp [List.flatMap_append, fullEntries, List.getLast?_append, List.getLast?_map, hx]

/-! ### The four lookups -/

/-- **`Get` returns the value the tree maps the key to.** -/
theorem get_correct {r : Bool} {n : Node α} (h : WF r n) (k : Key) :
    get n k = (entries n).lookup k := by
  rw [lookup_eq_filter]
  exact lookup_get_filter h k

/-- **`LongestPrefix` returns the value of the last (so the longest) stored key
that is a prefix of the search key.** -/
theorem longestPrefix_correct {t : Node α} (h : WF true t) (k : Key) :
    longestPrefix t k none = ((entries t).filter (fun e => e.1.isPrefixOf k)).getLast?.map (·.2) := by
  rw [lookup_longestPrefix_aux h k none, Option.or_none]

/-- **`FirstPrefix` returns the value of the first key starting with the
prefix.** -/
theorem firstPrefix_correct {t : Node α} (h : WF true t) (p : Key) :
    firstPrefix t p = ((entries t).filter (fun e => p.isPrefixOf e.1)).head?.map (·.2) := by
  obtain ⟨hn, hs⟩ := lookup_seekPrefix_aux h p
  unfold firstPrefix
  cases hm : seekPrefix t p with
  | none => simp [hn hm]
  | some m =>
    obtain ⟨⟨r', hwf⟩, P, hP⟩ := hs m hm
    simp only
    rw [hP, lookup_minNode hwf, List.head?_map, Option.map_map]
    rfl

/-- **`LastPrefix` returns the value of the last key starting with the
prefix.** -/
theorem lastPrefix_correct {t : Node α} (h : WF true t) (p : Key) :
    lastPrefix t p = ((entries t).filter (fun e => p.isPrefixOf e.1)).getLast?.map (·.2) := by
  obtain ⟨hn, hs⟩ := lookup_seekPrefix_aux h p
  unfold lastPrefix
  cases hm : seekPrefix t p with
  | none => simp [hn hm]
  | some m =>
    obtain ⟨⟨r', hwf⟩, P, hP⟩ := hs m hm
    simp only
    rw [hP, lookup_maxNode hwf, List.getLast?_map, Option.map_map]
    rfl

/-! ### The `hasPrefix` fast path

The lookups above are modelled with `isPrefixOf`; the Go code calls
`node.hasPrefix` (`goHasPrefix`), which skips the first byte and has one- and
two-byte fast paths. On a child found under the search's first byte the two
agree, so modelling the test with `isPrefixOf` loses nothing. -/

theorem lookup_goHasPrefix_eq {seg rest : Key} {b : Nat} (h : seg.head? = some b) :
    goHasPrefix seg (b :: rest) = seg.isPrefixOf (b :: rest) := by
  unfold goHasPrefix
  split
  · rename_i h1
    obtain ⟨x, rfl⟩ := List.length_eq_one_iff.mp h1
    simp at h
    subst h
    simp
  · split
    · rename_i _ h2
      match seg, h2 with
      | [x, y], _ =>
        simp at h
        subst h
        cases rest <;> simp [List.isPrefixOf_cons_cons, eq_comm, Bool.beq_eq_decide_eq]
    · rw [Bool.eq_iff_iff, List.isPrefixOf_iff_prefix, List.prefix_iff_eq_take]
      simp only [Bool.and_eq_true, decide_eq_true_eq]
      constructor
      · rintro ⟨_, h3⟩; exact h3.symm
      · intro h3
        refine ⟨?_, h3.symm⟩
        rw [h3]; simp; omega

end Node
end JuuriFormal
