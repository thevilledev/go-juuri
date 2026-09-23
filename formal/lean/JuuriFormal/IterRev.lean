/-
Copyright (c) 2026 Ville Vesilehto
SPDX-License-Identifier: MPL-2.0

The reverse iterator (`ReverseIterator.Previous`, `SeekReverseLowerBound`,
`SeekPrefixWatch`): it emits exactly the values of the selected keys, in
descending key order, never faults and terminates within the fuel.
-/
import JuuriFormal.Order

namespace JuuriFormal
namespace Node

variable {α : Type}

/-! ### The abstract remaining output of a reverse stack -/

/-- The values of a subtree, in ascending key order. -/
def rev_vals (n : Node α) : List (Option α) := (entries n).map (fun e => some e.2)

/-- The own value of a node, as output. -/
def rev_own (n : Node α) : List (Option α) := n.val.toList.map some

/-- What a reverse frame still has to emit: children `i, i-1, …, 0` in
descending order, then the node's own value. -/
def rev_frameOut (p : Node α × Int) : List (Option α) :=
  ((p.1.kids.take (p.2 + 1).toNat).flatMap rev_vals).reverse ++ rev_own p.1

/-- What a reverse stack still has to emit, top frame first. -/
def rev_out (s : Stack α) : List (Option α) := s.flatMap rev_frameOut

/-- An upper bound on the number of steps a frame still takes. -/
def rev_frameMeas (p : Node α × Int) : Nat :=
  2 * ((p.1.kids.take (p.2 + 1).toNat).map size).sum + 1

def rev_meas (s : Stack α) : Nat := (s.map rev_frameMeas).sum

/-- The invariant of reachable reverse stacks. -/
def rev_Good (s : Stack α) : Prop :=
  ∀ p ∈ s, p.2 < (p.1.kids.length : Int) ∧ ∀ c ∈ p.1.kids, WF false c

theorem rev_vals_mk (s : Key) (v : Option α) (kids : List (Node α)) :
    rev_vals (mk s v kids) = v.toList.map some ++ kids.flatMap rev_vals := by
  unfold rev_vals
  rw [entries_mk, List.map_append, List.map_flatMap]
  congr 1
  · cases v <;> simp
  · congr 1
    funext c
    simp [fullEntries]

theorem rev_vals_eq (n : Node α) : rev_vals n = rev_own n ++ n.kids.flatMap rev_vals := by
  cases n with
  | mk s v kids => rw [rev_vals_mk]; rfl

theorem rev_own_reverse (n : Node α) : (rev_own n).reverse = rev_own n := by
  cases n with
  | mk s v kids => cases v <;> simp [rev_own]

theorem rev_frameOut_full (n : Node α) :
    rev_frameOut (n, (n.kids.length : Int) - 1) = (rev_vals n).reverse := by
  have : ((n.kids.length : Int) - 1 + 1).toNat = n.kids.length := by omega
  simp only [rev_frameOut, this, List.take_length]
  rw [rev_vals_eq n, List.reverse_append, rev_own_reverse]

theorem rev_size_pos (n : Node α) : 1 ≤ size n := by
  cases n with
  | mk s v kids => simp [size]

theorem rev_size_mk (s : Key) (v : Option α) (kids : List (Node α)) :
    size (mk s v kids) = 1 + (kids.map size).sum := by
  simp [size]

theorem rev_size_eq (n : Node α) : size n = 1 + (n.kids.map size).sum := by
  cases n with
  | mk s v kids => simp [size]

theorem rev_sum_take_le (l : List (Node α)) (k : Nat) :
    ((l.take k).map size).sum ≤ (l.map size).sum := by
  conv => rhs; rw [← List.take_append_drop k l]
  rw [List.map_append, List.sum_append]
  omega

theorem rev_size_le_of_mem {c : Node α} {l : List (Node α)} (h : c ∈ l) :
    size c ≤ (l.map size).sum := by
  induction l with
  | nil => simp at h
  | cons x xs ih =>
    simp only [List.mem_cons] at h
    simp only [List.map_cons, List.sum_cons]
    rcases h with rfl | h
    · omega
    · have := ih h; omega

theorem rev_meas_nil : rev_meas ([] : Stack α) = 0 := rfl

theorem rev_meas_cons (p : Node α × Int) (s : Stack α) :
    rev_meas (p :: s) = rev_frameMeas p + rev_meas s := by
  simp [rev_meas]

theorem rev_out_cons (p : Node α × Int) (s : Stack α) :
    rev_out (p :: s) = rev_frameOut p ++ rev_out s := by
  simp [rev_out]

theorem rev_Good_cons {p : Node α × Int} {s : Stack α} :
    rev_Good (p :: s) ↔ (p.2 < (p.1.kids.length : Int) ∧ ∀ c ∈ p.1.kids, WF false c) ∧ rev_Good s := by
  simp [rev_Good]

/-! ### One step of `Previous` -/

theorem rev_run_eq (fuel : Nat) (s : Stack α) (hg : rev_Good s) (hm : rev_meas s ≤ fuel) :
    run prevStep fuel s = rev_out s := by
  induction fuel generalizing s with
  | zero =>
    cases s with
    | nil => rfl
    | cons p s =>
      rw [rev_meas_cons] at hm
      simp [rev_frameMeas] at hm
  | succ fuel ih =>
    cases s with
    | nil => rfl
    | cons p s =>
      obtain ⟨n, i⟩ := p
      rw [rev_Good_cons] at hg
      obtain ⟨⟨hlt, hkids⟩, hg⟩ := hg
      simp only at hlt hkids
      rw [rev_meas_cons] at hm
      rw [rev_out_cons]
      by_cases hi : i < 0
      · have h0 : (i + 1).toNat = 0 := by omega
        have hm' : rev_meas s ≤ fuel := by
          simp only [rev_frameMeas, h0] at hm; simp at hm; omega
        have hout : rev_frameOut (n, i) = rev_own n := by
          simp [rev_frameOut, h0]
        rw [hout]
        cases hv : n.val with
        | none =>
          simp only [run, prevStep, hi, ↓reduceIte, hv, Option.isSome_none, Bool.false_eq_true, ↓reduceIte]
          rw [ih s hg hm']
          simp [rev_own, hv]
        | some x =>
          simp only [run, prevStep, hi, ↓reduceIte, hv, Option.isSome_some]
          rw [ih s hg hm']
          simp [rev_own, hv]
      · have hi0 : 0 ≤ i := by omega
        have hlt' : i.toNat < n.kids.length := by omega
        have hget : n.kids[i.toNat]? = some (n.kids[i.toNat]'hlt') := List.getElem?_eq_getElem hlt'
        generalize hc : n.kids[i.toNat]'hlt' = c at hget
        have hcmem : c ∈ n.kids := List.mem_of_getElem? hget
        have hcwf := hkids c hcmem
        have htake : n.kids.take (i + 1).toNat = n.kids.take (i - 1 + 1).toNat ++ [c] := by
          have e1 : (i + 1).toNat = i.toNat + 1 := by omega
          have e2 : (i - 1 + 1).toNat = i.toNat := by omega
          rw [e1, e2, List.take_add_one, hget]; rfl
        have hsz := rev_size_pos c
        have hframe : rev_frameMeas (n, i) = rev_frameMeas (n, i - 1) + 2 * size c := by
          simp only [rev_frameMeas, htake, List.map_append, List.sum_append]
          simp
          omega
        have hframeOut : rev_frameOut (n, i) = (rev_vals c).reverse ++ rev_frameOut (n, i - 1) := by
          simp only [rev_frameOut, htake, List.flatMap_append, List.reverse_append]
          simp
        have hg' : rev_Good ((n, i - 1) :: s) := by
          rw [rev_Good_cons]
          exact ⟨⟨by simp only; omega, hkids⟩, hg⟩
        by_cases hce : c.kids.isEmpty
        · -- a childless child: it carries a value
          have hck : c.kids = [] := List.isEmpty_iff.mp hce
          obtain ⟨cs, cv, ckids⟩ := c
          simp only [kids_mk] at hck
          subst hck
          have hcv : ∃ x, cv = some x := by
            cases hcwf with
            | mk _ h2 _ _ =>
              cases cv with
              | none => have := (h2 rfl).2 rfl; simp at this
              | some x => exact ⟨x, rfl⟩
          obtain ⟨x, rfl⟩ := hcv
          have hvals : rev_vals (mk cs (some x) ([] : List (Node α))) = [some x] := by
            simp [rev_vals, entries_mk]
          simp only [run, prevStep, hi, ↓reduceIte, hget, hce, ↓reduceIte]
          rw [ih _ hg' (by rw [rev_meas_cons]; omega)]
          rw [hframeOut, hvals, rev_out_cons]
          simp
        · simp only [run, prevStep, hi, ↓reduceIte, hget, hce, Bool.false_eq_true]
          have hg'' : rev_Good ((c, (c.kids.length : Int) - 1) :: (n, i - 1) :: s) := by
            rw [rev_Good_cons]
            exact ⟨⟨by simp only; omega, WF.kids_wf hcwf⟩, hg'⟩
          have hmc : rev_frameMeas (c, (c.kids.length : Int) - 1) + 1 = 2 * size c := by
            have : ((c.kids.length : Int) - 1 + 1).toNat = c.kids.length := by omega
            simp only [rev_frameMeas, this, List.take_length]
            rw [rev_size_eq c]
            omega
          rw [ih _ hg'' (by rw [rev_meas_cons, rev_meas_cons] at *; omega)]
          rw [rev_out_cons, rev_out_cons, rev_frameOut_full, hframeOut, List.append_assoc]

/-! ### Key order facts for the descent -/

theorem rev_lcp_le_right (a b : Key) : lcp a b ≤ b.length := by
  induction a generalizing b with
  | nil => simp [lcp]
  | cons x xs ih =>
    cases b with
    | nil => simp [lcp]
    | cons y ys =>
      simp only [lcp]
      split
      · have := ih ys; simp; omega
      · omega

/-- The segment diverges below the key: everything under it is smaller. -/
theorem rev_lcp_lt (a b x : Key) (hb : lcp a b < b.length) (ha : lcp a b < a.length)
    (hlt : b.getD (lcp a b) 0 < a.getD (lcp a b) 0) : keyLt (b ++ x) a = true := by
  induction a generalizing b with
  | nil => simp at ha
  | cons y ys ih =>
    cases b with
    | nil => simp at hb
    | cons z zs =>
      simp only [lcp] at hb ha hlt
      by_cases hyz : y = z
      · subst hyz
        simp only [↓reduceIte, List.length_cons, List.getD_cons_succ] at hb ha hlt
        simp only [List.cons_append, keyLt_cons_cons, Nat.lt_irrefl, decide_false,
          decide_true, Bool.true_and, Bool.false_or]
        exact ih zs (by omega) (by omega) hlt
      · simp only [hyz, ↓reduceIte, List.getD_cons_zero] at hlt
        exact keyLt_of_head_lt hlt

/-- The segment diverges above the key, or the key ends inside it:
everything under it is greater. -/
theorem rev_lcp_gt (a b x : Key) (hb : lcp a b < b.length)
    (hn : ¬ (lcp a b < a.length ∧ b.getD (lcp a b) 0 < a.getD (lcp a b) 0)) :
    keyLt a (b ++ x) = true := by
  induction a generalizing b with
  | nil =>
    cases b with
    | nil => simp [lcp] at hb
    | cons z zs => rfl
  | cons y ys ih =>
    cases b with
    | nil => simp [lcp] at hb
    | cons z zs =>
      simp only [lcp] at hb hn
      by_cases hyz : y = z
      · subst hyz
        simp only [↓reduceIte, List.length_cons, List.getD_cons_succ] at hb hn
        simp only [List.cons_append, keyLt_cons_cons, Nat.lt_irrefl, decide_false,
          decide_true, Bool.true_and, Bool.false_or]
        exact ih zs (by omega) (by intro h; exact hn ⟨by omega, h.2⟩)
      · simp only [hyz, ↓reduceIte, List.getD_cons_zero, List.length_cons] at hn
        have : y < z := by omega
        exact keyLt_of_head_lt this

/-- The segment is a prefix of the key. -/
theorem rev_lcp_eq (a b : Key) (h : ¬ lcp a b < b.length) : a = b ++ a.drop (lcp a b) := by
  induction a generalizing b with
  | nil =>
    cases b with
    | nil => rfl
    | cons z zs => simp [lcp] at h
  | cons y ys ih =>
    cases b with
    | nil => simp [lcp]
    | cons z zs =>
      simp only [lcp] at h ⊢
      by_cases hyz : y = z
      · subst hyz
        simp only [↓reduceIte, List.length_cons] at h ⊢
        simp only [List.drop_succ_cons, List.cons_append, List.cons.injEq, true_and]
        exact ih zs (by omega)
      · simp [hyz] at h

/-! ### `rankOf` on sorted children -/

theorem rev_rank_split {kids : List (Node α)} (hs : (kids.map lbl).Pairwise (· < ·)) (b : Nat) :
    (∀ c ∈ kids.take (rankOf kids b).1, c.lbl < b) ∧ (∀ c ∈ kids.drop (rankOf kids b).1, b ≤ c.lbl) := by
  induction kids with
  | nil => simp
  | cons k ks ih =>
    simp only [List.map_cons, List.pairwise_cons, List.mem_map] at hs
    obtain ⟨hk, hs⟩ := hs
    have ih := ih hs
    simp only [rankOf, List.countP_cons] at ih ⊢
    by_cases hkb : k.lbl < b
    · simp only [hkb, decide_true, ↓reduceIte]
      rw [List.take_succ_cons, List.drop_succ_cons]
      refine ⟨?_, ih.2⟩
      intro c hc
      simp only [List.mem_cons] at hc
      rcases hc with rfl | hc
      · exact hkb
      · exact ih.1 c hc
    · have h0 : List.countP (fun c => decide (c.lbl < b)) ks = 0 := by
        rw [List.countP_eq_zero]
        intro c hc
        have := hk c.lbl ⟨c, hc, rfl⟩
        simp; omega
      simp only [hkb, decide_false, Bool.false_eq_true, ↓reduceIte, h0, Nat.add_zero,
        List.take_zero, List.drop_zero, List.not_mem_nil, false_implies, implies_true, true_and]
      intro c hc
      simp only [List.mem_cons] at hc
      rcases hc with rfl | hc
      · omega
      · have := hk c.lbl ⟨c, hc, rfl⟩; omega

theorem rev_rank_found {kids : List (Node α)} (hs : (kids.map lbl).Pairwise (· < ·)) (b : Nat)
    (hf : (rankOf kids b).2 = true) :
    ∃ c B, kids.drop (rankOf kids b).1 = c :: B ∧ c.lbl = b ∧ ∀ d ∈ B, b < d.lbl := by
  obtain ⟨h1, h2⟩ := rev_rank_split hs b
  simp only [rankOf, List.any_eq_true, decide_eq_true_eq] at hf
  obtain ⟨d, hd, hdb⟩ := hf
  have hdrop : d ∈ kids.drop (rankOf kids b).1 := by
    rw [← List.take_append_drop (rankOf kids b).1 kids, List.mem_append] at hd
    rcases hd with hd | hd
    · have := h1 d hd; omega
    · exact hd
  have hsd : ((kids.drop (rankOf kids b).1).map lbl).Pairwise (· < ·) := by
    rw [List.map_drop]; exact hs.sublist (List.drop_sublist _ _)
  cases hk : kids.drop (rankOf kids b).1 with
  | nil => rw [hk] at hdrop; simp at hdrop
  | cons c B =>
    rw [hk] at hdrop hsd h2
    simp only [List.map_cons, List.pairwise_cons, List.mem_map] at hsd
    have hcb : b ≤ c.lbl := h2 c (by simp)
    simp only [List.mem_cons] at hdrop
    rcases hdrop with rfl | hdB
    · refine ⟨d, B, rfl, hdb, ?_⟩
      intro e he
      have := hsd.1 e.lbl ⟨e, he, rfl⟩
      omega
    · have := hsd.1 d.lbl ⟨d, hdB, rfl⟩
      omega

theorem rev_getKid_some {kids : List (Node α)} {i : Nat} {c : Node α} {h : c ∈ kids}
    (hg : getKid kids i = some ⟨c, h⟩) : kids[i]? = some c := by
  unfold getKid at hg
  split at hg
  · simp at hg
  · rename_i c' hc'
    simp only [Option.some.injEq, Subtype.mk.injEq] at hg
    subst hg; exact hc'

theorem rev_getKid_none {kids : List (Node α)} {i : Nat} (hg : getKid kids i = none) :
    kids[i]? = none := by
  unfold getKid at hg
  split at hg
  · assumption
  · simp at hg

theorem rev_rank_lt {kids : List (Node α)} {b : Nat} (hf : (rankOf kids b).2 = true) :
    (rankOf kids b).1 < kids.length := by
  simp only [rankOf, List.any_eq_true, decide_eq_true_eq] at hf ⊢
  obtain ⟨d, hd, hdb⟩ := hf
  have h1 := List.countP_le_length (p := fun c => decide (c.lbl < b)) (l := kids)
  have h2 : List.countP (fun c => decide (c.lbl < b)) kids ≠ kids.length := by
    intro h
    have := List.countP_eq_length.mp h d hd
    simp at this; omega
  omega

theorem rev_rank_le {kids : List (Node α)} {b : Nat} : (rankOf kids b).1 ≤ kids.length :=
  List.countP_le_length


/-! ### Selecting the keys `≤ k` -/

/-- The values of the entries whose key is `≤ d`, in ascending order. -/
def rev_sel (d : Key) (l : List (Key × α)) : List (Option α) :=
  (l.filter (fun e => !keyLt d e.1)).map (fun e => some e.2)

theorem rev_sel_append (d : Key) (l₁ l₂ : List (Key × α)) :
    rev_sel d (l₁ ++ l₂) = rev_sel d l₁ ++ rev_sel d l₂ := by
  simp [rev_sel, List.filter_append]

theorem rev_sel_flatMap (d : Key) (L : List (Node α)) (f : Node α → List (Key × α)) :
    rev_sel d (L.flatMap f) = L.flatMap (fun c => rev_sel d (f c)) := by
  simp [rev_sel, List.filter_flatMap, List.map_flatMap]

theorem rev_sel_all {d : Key} {l : List (Key × α)} (h : ∀ e ∈ l, keyLt d e.1 = false) :
    rev_sel d l = l.map (fun e => some e.2) := by
  unfold rev_sel
  rw [List.filter_eq_self.mpr]
  intro e he; simp [h e he]

theorem rev_sel_none {d : Key} {l : List (Key × α)} (h : ∀ e ∈ l, keyLt d e.1 = true) :
    rev_sel d l = [] := by
  unfold rev_sel
  rw [List.filter_eq_nil_iff.mpr]
  · rfl
  intro e he; simp [h e he]

theorem rev_sel_prefix (p d : Key) (l : List (Key × α)) :
    rev_sel (p ++ d) (l.map (fun e => (p ++ e.1, e.2))) = rev_sel d l := by
  simp [rev_sel, List.filter_map, Function.comp_def, keyLt_append_left]

theorem rev_fullEntries_vals (c : Node α) :
    (fullEntries c).map (fun e => some e.2) = rev_vals c := by
  simp [fullEntries, rev_vals]

theorem rev_sel_kids_lt {b : Nat} {rest : Key} {L : List (Node α)} (hwf : ∀ c ∈ L, WF false c)
    (hlt : ∀ c ∈ L, c.lbl < b) :
    rev_sel (b :: rest) (L.flatMap fullEntries) = L.flatMap rev_vals := by
  rw [rev_sel_flatMap]
  induction L with
  | nil => rfl
  | cons c L ih =>
    rw [List.flatMap_cons, List.flatMap_cons,
      ih (fun d hd => hwf d (by simp [hd])) (fun d hd => hlt d (by simp [hd]))]
    congr 1
    rw [rev_sel_all, rev_fullEntries_vals]
    intro e he
    obtain ⟨r, hr⟩ := fullEntries_head (hwf c (by simp)).seg_ne_nil e he
    rw [hr]
    exact keyLt_asymm (keyLt_of_head_lt (hlt c (by simp)))

theorem rev_sel_kids_gt {b : Nat} {rest : Key} {L : List (Node α)} (hwf : ∀ c ∈ L, WF false c)
    (hgt : ∀ c ∈ L, b < c.lbl) :
    rev_sel (b :: rest) (L.flatMap fullEntries) = [] := by
  rw [rev_sel_flatMap]
  apply List.flatMap_eq_nil_iff.mpr
  intro c hc
  apply rev_sel_none
  intro e he
  obtain ⟨r, hr⟩ := fullEntries_head (hwf c hc).seg_ne_nil e he
  rw [hr]
  exact keyLt_of_head_lt (hgt c hc)

theorem rev_frameOut_mk_full (seg : Key) (v : Option α) (kids : List (Node α)) :
    rev_frameOut (mk seg v kids, (kids.length : Int) - 1) = (rev_vals (mk seg v kids)).reverse :=
  rev_frameOut_full (mk seg v kids)

/-! ### `SeekReverseLowerBound` -/

theorem rev_seek {r : Bool} {n : Node α} (hn : WF r n) (search : Key) (s : Stack α)
    (hs : rev_Good s) :
    rev_Good (seekReverseLowerBound n search s) ∧
    rev_out (seekReverseLowerBound n search s) =
      (rev_sel search (fullEntries n)).reverse ++ rev_out s ∧
    rev_meas (seekReverseLowerBound n search s) ≤ rev_meas s + 2 * size n := by
  induction hn generalizing search s with
  | @mk isRoot seg v kids _ _ hsorted hkids ih =>
    have hsize := rev_size_mk seg v kids
    have hfull : fullEntries (mk seg v kids) = (entries (mk seg v kids)).map (fun e => (seg ++ e.1, e.2)) := rfl
    rw [seekReverseLowerBound.eq_1]
    by_cases h1 : lcp search seg < seg.length
    · rw [ite_eq_left h1]
      by_cases h2 : lcp search seg < search.length ∧ seg.getD (lcp search seg) 0 < search.getD (lcp search seg) 0
      · rw [ite_eq_left h2]
        have hsel : rev_sel search (fullEntries (mk seg v kids)) = rev_vals (mk seg v kids) := by
          rw [rev_sel_all, rev_fullEntries_vals]
          intro e he
          rw [hfull, List.mem_map] at he
          obtain ⟨e', _, rfl⟩ := he
          exact keyLt_asymm (rev_lcp_lt search seg e'.1 h1 h2.1 h2.2)
        refine ⟨?_, ?_, ?_⟩
        · rw [rev_Good_cons]; exact ⟨⟨by simp only [kids_mk]; omega, hkids⟩, hs⟩
        · rw [rev_out_cons, rev_frameOut_mk_full, hsel]
        · rw [rev_meas_cons]
          have : ((kids.length : Int) - 1 + 1).toNat = kids.length := by omega
          simp only [rev_frameMeas, kids_mk, this, List.take_length]
          omega
      · rw [ite_eq_right h2]
        have hsel : rev_sel search (fullEntries (mk seg v kids)) = [] := by
          apply rev_sel_none
          intro e he
          rw [hfull, List.mem_map] at he
          obtain ⟨e', _, rfl⟩ := he
          exact rev_lcp_gt search seg e'.1 h1 h2
        refine ⟨hs, by rw [hsel]; rfl, by omega⟩
    · rw [ite_eq_right h1]
      have hse := rev_lcp_eq search seg h1
      generalize List.drop (lcp search seg) search = d at hse ⊢
      subst hse
      have hsel0 : rev_sel (seg ++ d) (fullEntries (mk seg v kids)) =
          rev_sel d ((v.map (fun x => ([], x))).toList) ++ rev_sel d (kids.flatMap fullEntries) := by
        rw [hfull, rev_sel_prefix, entries_mk, rev_sel_append]
      cases d with
      | nil =>
        have hsel : rev_sel (seg ++ []) (fullEntries (mk seg v kids)) = rev_own (mk seg v kids) := by
          rw [hsel0, rev_sel_flatMap, List.flatMap_eq_nil_iff.mpr]
          · cases v <;> simp [rev_sel, rev_own]
          intro c hc
          apply rev_sel_none
          intro e he
          obtain ⟨r, hr⟩ := fullEntries_head (hkids c hc).seg_ne_nil e he
          rw [hr]; rfl
        simp only
        refine ⟨?_, ?_, ?_⟩
        · rw [rev_Good_cons]; exact ⟨⟨by simp only [kids_mk]; omega, hkids⟩, hs⟩
        · rw [rev_out_cons, hsel, rev_own_reverse]
          simp [rev_frameOut]
        · rw [rev_meas_cons]
          simp [rev_frameMeas]
          omega
      | cons b rest =>
        simp only
        have hown : rev_sel (b :: rest) ((v.map (fun x => ([], x))).toList) = rev_own (mk seg v kids) := by
          cases v <;> simp [rev_sel, rev_own]
        obtain ⟨hlo, hhi⟩ := rev_rank_split hsorted b
        have htd := List.take_append_drop (rankOf kids b).1 kids
        have hsplit : kids.flatMap fullEntries =
            (kids.take (rankOf kids b).1).flatMap fullEntries ++
              (kids.drop (rankOf kids b).1).flatMap fullEntries := by
          rw [← List.flatMap_append, htd]
        have hgood' : rev_Good ((mk seg v kids, ((rankOf kids b).1 : Int) - 1) :: s) := by
          rw [rev_Good_cons]
          have := rev_rank_le (kids := kids) (b := b)
          exact ⟨⟨by simp only [kids_mk]; omega, hkids⟩, hs⟩
        have htake : (((rankOf kids b).1 : Int) - 1 + 1).toNat = (rankOf kids b).1 := by omega
        have hfr : rev_frameOut (mk seg v kids, ((rankOf kids b).1 : Int) - 1) =
            (((kids.take (rankOf kids b).1).flatMap rev_vals).reverse ++ rev_own (mk seg v kids)) := by
          simp only [rev_frameOut, kids_mk, htake]
        have hfm : rev_frameMeas (mk seg v kids, ((rankOf kids b).1 : Int) - 1) =
            2 * ((kids.take (rankOf kids b).1).map size).sum + 1 := by
          simp only [rev_frameMeas, kids_mk, htake]
        have hwfT : ∀ c ∈ kids.take (rankOf kids b).1, WF false c :=
          fun c hc => hkids c (List.mem_of_mem_take hc)
        have hwfD : ∀ c ∈ kids.drop (rankOf kids b).1, WF false c :=
          fun c hc => hkids c (List.mem_of_mem_drop hc)
        by_cases hf : (rankOf kids b).2 = true
        · rw [ite_eq_left hf]
          obtain ⟨c, B, hdrop, hcl, hB⟩ := rev_rank_found hsorted b hf
          have hcget : kids[(rankOf kids b).1]? = some c := by
            have := List.getElem?_drop (xs := kids) (i := (rankOf kids b).1) (j := 0)
            rw [hdrop] at this; simpa using this.symm
          have hcmem : c ∈ kids := List.mem_of_getElem? hcget
          have hwfB : ∀ d ∈ B, WF false d := fun d hd => hwfD d (by rw [hdrop]; simp [hd])
          have hsel : rev_sel (seg ++ b :: rest) (fullEntries (mk seg v kids)) =
              rev_own (mk seg v kids) ++ (kids.take (rankOf kids b).1).flatMap rev_vals ++
                rev_sel (b :: rest) (fullEntries c) := by
            rw [hsel0, hown, hsplit, rev_sel_append,
              rev_sel_kids_lt hwfT hlo, hdrop, List.flatMap_cons, rev_sel_append,
              rev_sel_kids_gt hwfB hB]
            simp
          have hsum : (kids.map size).sum =
              ((kids.take (rankOf kids b).1).map size).sum + size c + (B.map size).sum := by
            conv => lhs; rw [← htd, hdrop]
            simp; omega
          split
          · rename_i hg
            have := rev_getKid_none hg
            rw [hcget] at this; simp at this
          · rename_i c' hc' hg
            have := rev_getKid_some hg
            rw [hcget] at this
            simp only [Option.some.injEq] at this
            subst this
            obtain ⟨g, o, m⟩ := ih c hcmem (b :: rest) _ hgood'
            refine ⟨g, ?_, ?_⟩
            · rw [o, rev_out_cons, hfr, hsel]
              simp [rev_own_reverse]
            · rw [rev_meas_cons, hfm] at m
              omega
        · rw [ite_eq_right hf]
          have hB : ∀ d ∈ kids.drop (rankOf kids b).1, b < d.lbl := by
            intro d hd
            have h1 := hhi d hd
            have h2 : d.lbl ≠ b := by
              intro h
              apply hf
              simp only [rankOf, List.any_eq_true, decide_eq_true_eq]
              exact ⟨d, List.mem_of_mem_drop hd, h⟩
            omega
          have hsel : rev_sel (seg ++ b :: rest) (fullEntries (mk seg v kids)) =
              rev_own (mk seg v kids) ++ (kids.take (rankOf kids b).1).flatMap rev_vals := by
            rw [hsel0, hown, hsplit, rev_sel_append,
              rev_sel_kids_lt hwfT hlo, rev_sel_kids_gt hwfD hB]
            simp
          refine ⟨hgood', ?_, ?_⟩
          · rw [rev_out_cons, hfr, hsel]
            simp [rev_own_reverse]
          · rw [rev_meas_cons, hfm]
            have := rev_sum_take_le kids (rankOf kids b).1
            omega

/-! ### `seekPrefix` -/

theorem rev_isPrefixOf_append (l a b : Key) :
    (l ++ a).isPrefixOf (l ++ b) = a.isPrefixOf b := by
  apply Bool.eq_iff_iff.mpr
  rw [List.isPrefixOf_iff_prefix, List.isPrefixOf_iff_prefix]
  exact List.prefix_append_right_inj l

theorem rev_pf_kids_ne {b : Nat} {rest : Key} {L : List (Node α)} (hwf : ∀ d ∈ L, WF false d)
    (hne : ∀ d ∈ L, d.lbl ≠ b) :
    (L.flatMap fullEntries).filter (fun e => (b :: rest).isPrefixOf e.1) = [] := by
  rw [List.filter_flatMap, List.flatMap_eq_nil_iff]
  intro d hd
  rw [List.filter_eq_nil_iff]
  intro e he
  obtain ⟨r, hr⟩ := fullEntries_head (hwf d hd).seg_ne_nil e he
  rw [hr, List.isPrefixOf_cons_cons]
  have := hne d hd
  simp only [Bool.and_eq_true, beq_iff_eq, not_and]
  intro h; exact absurd h.symm this

theorem rev_pf_own (b : Nat) (rest : Key) (v : Option α) :
    ((v.map (fun x => (([] : Key), x))).toList).filter (fun e => (b :: rest).isPrefixOf e.1) = [] := by
  cases v <;> simp [List.isPrefixOf]

theorem rev_seekPrefix {r : Bool} {n : Node α} (hn : WF r n) (p : Key) :
    (seekPrefix n p = none → (entries n).filter (fun e => p.isPrefixOf e.1) = []) ∧
    (∀ m, seekPrefix n p = some m →
      (∃ r', WF r' m) ∧ size m ≤ size n ∧
      ((entries n).filter (fun e => p.isPrefixOf e.1)).map (fun e => some e.2) = rev_vals m) := by
  induction hn generalizing p with
  | @mk isRoot seg v kids h1 h2 hsorted hkids ih =>
    cases p with
    | nil =>
      rw [seekPrefix.eq_1]
      refine ⟨fun h => by simp at h, ?_⟩
      intro m hm
      simp only [Option.some.injEq] at hm
      subst hm
      refine ⟨⟨isRoot, WF.mk h1 h2 hsorted hkids⟩, Nat.le_refl _, ?_⟩
      simp only [List.isPrefixOf]
      rw [List.filter_eq_self.mpr (fun _ _ => rfl)]
      rfl
    | cons b rest =>
      rw [seekPrefix.eq_2]
      have hsize := rev_size_mk seg v kids
      by_cases hf : (rankOf kids b).2 = true
      · rw [ite_eq_left hf]
        obtain ⟨c, B, hdrop, hcl, hB⟩ := rev_rank_found hsorted b hf
        obtain ⟨hlo, hhi⟩ := rev_rank_split hsorted b
        have htd := List.take_append_drop (rankOf kids b).1 kids
        have hcget : kids[(rankOf kids b).1]? = some c := by
          have := List.getElem?_drop (xs := kids) (i := (rankOf kids b).1) (j := 0)
          rw [hdrop] at this; simpa using this.symm
        have hcmem : c ∈ kids := List.mem_of_getElem? hcget
        have hcwf := hkids c hcmem
        have hcsz : size c ≤ size (mk seg v kids) := by
          have := rev_size_le_of_mem hcmem; omega
        -- only `c` can hold keys starting with `b`
        have hfilt : (entries (mk seg v kids)).filter (fun e => (b :: rest).isPrefixOf e.1) =
            (fullEntries c).filter (fun e => (b :: rest).isPrefixOf e.1) := by
          have hsplit : kids.flatMap fullEntries =
              (kids.take (rankOf kids b).1).flatMap fullEntries ++
                (fullEntries c ++ B.flatMap fullEntries) := by
            rw [← List.flatMap_cons, ← hdrop, ← List.flatMap_append, htd]
          rw [entries_mk, List.filter_append, rev_pf_own, hsplit, List.filter_append,
            List.filter_append,
            rev_pf_kids_ne (fun d hd => hkids d (List.mem_of_mem_take hd))
              (fun d hd => by have := hlo d hd; omega),
            rev_pf_kids_ne (fun d hd => hkids d (List.mem_of_mem_drop (by rw [hdrop]; simp [hd])))
              (fun d hd => by have := hB d hd; omega)]
          simp
        split
        · rename_i hg
          have := rev_getKid_none hg
          rw [hcget] at this; simp at this
        · rename_i c' hc' hg
          have := rev_getKid_some hg
          rw [hcget] at this
          simp only [Option.some.injEq] at this
          subst this
          by_cases hp : c.seg.isPrefixOf (b :: rest) = true
          · rw [ite_eq_left hp]
            have hpre := List.isPrefixOf_iff_prefix.mp hp
            obtain ⟨p', hp'⟩ := hpre
            have hdropeq : (b :: rest).drop c.seg.length = p' := by
              rw [← hp']; simp
            rw [hdropeq]
            have hfc : (fullEntries c).filter (fun e => (b :: rest).isPrefixOf e.1) =
                ((entries c).filter (fun e => p'.isPrefixOf e.1)).map
                  (fun e => (c.seg ++ e.1, e.2)) := by
              rw [← hp', fullEntries, List.filter_map]
              congr 1
              apply List.filter_congr
              intro e _
              simp [rev_isPrefixOf_append]
            obtain ⟨ihn, ihs⟩ := ih c hcmem p'
            refine ⟨?_, ?_⟩
            · intro hnone
              rw [hfilt, hfc, ihn hnone]; rfl
            · intro m hm
              obtain ⟨hw, hsz, hv⟩ := ihs m hm
              refine ⟨hw, by omega, ?_⟩
              rw [hfilt, hfc, List.map_map, ← hv]
              rfl
          · rw [ite_eq_right hp]
            by_cases hq : (b :: rest).length < c.seg.length ∧ (b :: rest).isPrefixOf c.seg = true
            · rw [ite_eq_left hq]
              refine ⟨fun h => by simp at h, ?_⟩
              intro m hm
              simp only [Option.some.injEq] at hm
              subst hm
              refine ⟨⟨false, hcwf⟩, hcsz, ?_⟩
              rw [hfilt, List.filter_eq_self.mpr, rev_fullEntries_vals]
              intro e he
              simp only [fullEntries, List.mem_map] at he
              obtain ⟨e', _, rfl⟩ := he
              apply List.isPrefixOf_iff_prefix.mpr
              exact (List.isPrefixOf_iff_prefix.mp hq.2).trans (List.prefix_append _ _)
            · rw [ite_eq_right hq]
              refine ⟨?_, fun m hm => by simp at hm⟩
              intro _
              rw [hfilt, List.filter_eq_nil_iff]
              intro e he
              simp only [fullEntries, List.mem_map] at he
              obtain ⟨e', _, rfl⟩ := he
              intro hpe
              have hpe := List.isPrefixOf_iff_prefix.mp hpe
              have hp2 : ¬ c.seg <+: (b :: rest) := fun h => hp (List.isPrefixOf_iff_prefix.mpr h)
              rcases List.prefix_or_prefix_of_prefix hpe (List.prefix_append c.seg e'.1) with h | h
              · have hlen := h.length_le
                by_cases hl : (b :: rest).length = c.seg.length
                · exact hp2 (List.IsPrefix.eq_of_length h hl ▸ List.prefix_refl _)
                · exact hq ⟨by omega, List.isPrefixOf_iff_prefix.mpr h⟩
              · exact hp2 h
      · rw [ite_eq_right hf]
        refine ⟨?_, fun m hm => by simp at hm⟩
        intro _
        rw [entries_mk, List.filter_append, rev_pf_own, rev_pf_kids_ne hkids]
        · rfl
        intro d hd hdb
        apply hf
        simp only [rankOf, List.any_eq_true, decide_eq_true_eq]
        exact ⟨d, hd, hdb⟩

/-! ### The theorems -/

/-- **`SeekReverseLowerBound` then `Previous`**: the values of the keys `≤ k`,
in descending key order, without a fault, within the fuel. -/
theorem iter_reverseLowerBound {t : Node α} (h : WF true t) (k : Key) (fuel : Nat) (hf : 4 * size t + 4 ≤ fuel) :
    run prevStep fuel (seekReverseLowerBound t k []) =
      (((entries t).filter (fun e => !keyLt k e.1)).map (fun e => some e.2)).reverse := by
  obtain ⟨hg, ho, hm⟩ := rev_seek h k [] (by simp [rev_Good])
  rw [rev_run_eq fuel _ hg (by rw [rev_meas_nil] at hm; omega), ho]
  have hfe : fullEntries t = entries t := by
    simp [fullEntries, h.root_seg]
  rw [hfe]
  simp [rev_out, rev_sel]

/-- **Reverse `SeekPrefixWatch` then `Previous`**: the values of the keys that
start with `p`, in descending key order, without a fault, within the fuel. -/
theorem iter_prefix_rev {t : Node α} (h : WF true t) (p : Key) (fuel : Nat) (hf : 4 * size t + 4 ≤ fuel) :
    run prevStep fuel (seekPrefixRev t p) =
      (((entries t).filter (fun e => p.isPrefixOf e.1)).map (fun e => some e.2)).reverse := by
  obtain ⟨hnone, hsome⟩ := rev_seekPrefix h p
  unfold seekPrefixRev
  split
  · rename_i hs
    rw [hnone hs]
    rw [rev_run_eq fuel [] (by simp [rev_Good]) (by rw [rev_meas_nil]; omega)]
    rfl
  · rename_i m hs
    obtain ⟨⟨r', hw⟩, hsz, hv⟩ := hsome m hs
    have hg : rev_Good [(m, (m.kids.length : Int) - 1)] := by
      rw [rev_Good_cons]
      exact ⟨⟨by simp only; omega, WF.kids_wf hw⟩, by simp [rev_Good]⟩
    have hmeas : rev_meas [(m, (m.kids.length : Int) - 1)] ≤ fuel := by
      have : ((m.kids.length : Int) - 1 + 1).toNat = m.kids.length := by omega
      rw [rev_meas_cons, rev_meas_nil]
      simp only [rev_frameMeas, this, List.take_length]
      have := rev_size_eq m
      omega
    rw [rev_run_eq fuel _ hg hmeas, hv, rev_out_cons, rev_frameOut_full]
    simp [rev_out]

end Node
end JuuriFormal
