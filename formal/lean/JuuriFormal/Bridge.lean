/-
Copyright (c) 2026 Ville Vesilehto
SPDX-License-Identifier: MPL-2.0

The model finds a child with `rankOf` over the child list; the Go node finds
it with `rank` over its bitmap. On a node whose bitmap agrees with its child
array -- which `Rank.addKid_consistent` and `Rank.delKid_consistent` show the
Go code maintains -- the two give the same answer for every label.
-/
import JuuriFormal.Rank
import JuuriFormal.Tree

namespace JuuriFormal
namespace Node

open Rank

theorem rankOf_eq_goRank {α : Type} (kids : List (Node α)) (bm : Bitmap)
    (h : Consistent bm (kids.map lbl)) (b : UInt8) :
    goRank bm b = rankOf kids b.toNat := by
  have hb := b.toNat_lt
  rw [goRank_correct, rankSpec_eq_countP h _ (by simp at hb; omega)]
  simp only [rankOf, List.countP_map]
  congr 1
  have hbit := h.bits b.toNat (by simp at hb; omega)
  cases ht : bm.test b.toNat
  · have : b.toNat ∉ kids.map lbl := fun hm => by simp [hbit.mpr hm] at ht
    simp only [List.mem_map, not_exists, not_and] at this
    symm
    simpa [List.any_eq_false] using fun c hc heq => this c hc heq
  · obtain ⟨c, hc, hcl⟩ := List.mem_map.mp (hbit.mp ht)
    symm
    exact List.any_eq_true.mpr ⟨c, hc, by simp [hcl]⟩

end Node
end JuuriFormal
