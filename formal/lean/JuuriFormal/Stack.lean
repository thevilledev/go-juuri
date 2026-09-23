/-
Copyright (c) 2026 Ville Vesilehto
SPDX-License-Identifier: MPL-2.0

The iterator's traversal stack (iter.go), against a plain list.

The Go stack keeps its first `inlineFrames` = 8 frames in two inline arrays
and spills deeper ones into a slice, addressed by depth:

```go
func (s *stack) push(n *node, i int) {
	if s.depth < inlineFrames {
		s.nodes[s.depth], s.pos[s.depth] = n, int16(i)
	} else {
		s.spill = append(s.spill[:s.depth-inlineFrames], frame{n, int16(i)})
	}
	s.depth++
}

func (s *stack) top() (*node, *int16) {
	if s.depth <= inlineFrames {
		return s.nodes[s.depth-1], &s.pos[s.depth-1]
	}
	f := &s.spill[s.depth-1-inlineFrames]
	return f.n, &f.i
}
```

It pops with `s.depth--`, updates the top frame's position through the
pointer `top` returns, and resets with `depth = 0; spill = spill[:0]`. The
model in Tree.lean treats the stack as a list, top first; this file proves
that the Go representation behaves as that list. A frame is any type `β`
(the node and position pair); the inline arrays are one function, as the
two arrays are always written together.
-/

namespace JuuriFormal
namespace Stack

variable {β : Type}

/-- The Go stack: the depth, the `inlineFrames` = 8 inline frames and the
spill slice. Slots at or above the depth hold whatever was there, as in Go. -/
structure GoStack (β : Type) where
  depth : Nat
  inl : Nat → β
  spill : List β

/-- The frame at height `i` (0 is the bottom), where the Go code reads it. -/
def GoStack.frame (s : GoStack β) (i : Nat) : Option β :=
  if i < 8 then some (s.inl i) else s.spill[i - 8]?

/-- The frames the stack holds, bottom first. -/
def GoStack.content (s : GoStack β) : List β := (List.range s.depth).filterMap s.frame

/-- The stack as the model in Tree.lean sees it: top first. -/
def GoStack.toList (s : GoStack β) : List β := s.content.reverse

/-- The spill slice covers every frame above the inline ones. -/
def GoStack.Valid (s : GoStack β) : Prop := s.depth - 8 ≤ s.spill.length

def GoStack.push (s : GoStack β) (f : β) : GoStack β :=
  if s.depth < 8 then
    { s with inl := fun j => if j = s.depth then f else s.inl j, depth := s.depth + 1 }
  else
    { s with spill := s.spill.take (s.depth - 8) ++ [f], depth := s.depth + 1 }

def GoStack.top (s : GoStack β) : Option β :=
  if s.depth ≤ 8 then some (s.inl (s.depth - 1)) else s.spill[s.depth - 1 - 8]?

/-- A write through the pointer `top` returns (`*i = ...`). -/
def GoStack.setTop (s : GoStack β) (f : β) : GoStack β :=
  if s.depth ≤ 8 then { s with inl := fun j => if j = s.depth - 1 then f else s.inl j }
  else { s with spill := s.spill.set (s.depth - 1 - 8) f }

def GoStack.pop (s : GoStack β) : GoStack β := { s with depth := s.depth - 1 }

def GoStack.reset (s : GoStack β) : GoStack β := { s with depth := 0, spill := [] }

/-! ### Frames -/

theorem frame_some {s : GoStack β} (hv : s.Valid) {i : Nat} (hi : i < s.depth) :
    ∃ x, s.frame i = some x := by
  unfold GoStack.frame
  by_cases h : i < 8
  · simp [h]
  · unfold GoStack.Valid at hv
    simp only [h, ite_false]
    exact ⟨_, List.getElem?_eq_getElem (by omega)⟩

theorem filterMap_congr' {α γ : Type} (f g : α → Option γ) :
    ∀ l : List α, (∀ x ∈ l, f x = g x) → l.filterMap f = l.filterMap g
  | [], _ => rfl
  | a :: l, h => by
    simp only [List.filterMap_cons]
    rw [h a List.mem_cons_self, filterMap_congr' f g l (fun x hx => h x (List.mem_cons_of_mem _ hx))]

theorem content_congr {s t : GoStack β} (d : Nat) (h : ∀ i < d, s.frame i = t.frame i) :
    (List.range d).filterMap s.frame = (List.range d).filterMap t.frame :=
  filterMap_congr' _ _ _ (fun i hi => h i (List.mem_range.mp hi))

/-- The content up to a height below the depth, plus the frame there. -/
theorem content_succ (s : GoStack β) (d : Nat) (x : β) (hx : s.frame d = some x) :
    (List.range (d + 1)).filterMap s.frame = (List.range d).filterMap s.frame ++ [x] := by
  rw [List.range_succ, List.filterMap_append]
  simp [hx]

/-! ### push -/

theorem push_depth (s : GoStack β) (f : β) : (s.push f).depth = s.depth + 1 := by
  unfold GoStack.push; split <;> rfl

theorem push_valid {s : GoStack β} (hv : s.Valid) (f : β) : (s.push f).Valid := by
  unfold GoStack.Valid at *
  rw [push_depth]
  unfold GoStack.push
  by_cases h : s.depth < 8
  · simp only [h, ite_true]; omega
  · simp only [h, ite_false, List.length_append, List.length_take, List.length_singleton]
    omega

theorem push_frame_lt {s : GoStack β} (hv : s.Valid) (f : β) (i : Nat) (hi : i < s.depth) :
    (s.push f).frame i = s.frame i := by
  unfold GoStack.push GoStack.frame
  by_cases h : s.depth < 8
  · have hne : i ≠ s.depth := by omega
    by_cases h8 : i < 8 <;> simp [h, hne, h8]
  · unfold GoStack.Valid at hv
    by_cases h8 : i < 8
    · simp [h, h8]
    · simp only [h, h8, ite_false]
      rw [List.getElem?_append_left (by simp; omega), List.getElem?_take]
      simp only [show i - 8 < s.depth - 8 by omega, ite_true]

theorem push_frame_top {s : GoStack β} (hv : s.Valid) (f : β) :
    (s.push f).frame s.depth = some f := by
  unfold GoStack.push GoStack.frame
  by_cases h : s.depth < 8
  · simp [h]
  · unfold GoStack.Valid at hv
    have hlen : (List.take (s.depth - 8) s.spill).length = s.depth - 8 := by simp; omega
    simp only [h, ite_false]
    rw [List.getElem?_append_right (by omega), hlen]
    simp

/-- **push** puts a frame on top. -/
theorem push_content {s : GoStack β} (hv : s.Valid) (f : β) :
    (s.push f).content = s.content ++ [f] := by
  unfold GoStack.content
  rw [push_depth, content_succ _ _ _ (push_frame_top hv f), content_congr _ (push_frame_lt hv f)]

/-! ### top, setTop, pop, reset -/

/-- **top** reads the frame on top. -/
theorem top_eq {s : GoStack β} (hd : 0 < s.depth) : s.top = s.frame (s.depth - 1) := by
  unfold GoStack.top GoStack.frame
  by_cases h : s.depth ≤ 8
  · simp [h, show s.depth - 1 < 8 by omega]
  · simp only [h, ite_false, show ¬ s.depth - 1 < 8 by omega]

theorem content_last {s : GoStack β} (hv : s.Valid) (hd : 0 < s.depth) :
    ∃ x, s.frame (s.depth - 1) = some x ∧
      s.content = (List.range (s.depth - 1)).filterMap s.frame ++ [x] := by
  obtain ⟨x, hx⟩ := frame_some hv (i := s.depth - 1) (by omega)
  refine ⟨x, hx, ?_⟩
  unfold GoStack.content
  rw [← content_succ _ _ _ hx, show s.depth - 1 + 1 = s.depth by omega]

theorem top_content {s : GoStack β} (hv : s.Valid) (hd : 0 < s.depth) :
    s.top = s.content.getLast? := by
  obtain ⟨x, hx, hc⟩ := content_last hv hd
  rw [top_eq hd, hx, hc]
  simp

theorem setTop_depth (s : GoStack β) (f : β) : (s.setTop f).depth = s.depth := by
  unfold GoStack.setTop; split <;> rfl

theorem setTop_valid {s : GoStack β} (hv : s.Valid) (f : β) : (s.setTop f).Valid := by
  unfold GoStack.Valid at *
  rw [setTop_depth]
  unfold GoStack.setTop
  split <;> simp_all

theorem setTop_frame_lt (s : GoStack β) (f : β) (i : Nat) (hi : i + 1 < s.depth) :
    (s.setTop f).frame i = s.frame i := by
  unfold GoStack.setTop GoStack.frame
  have hne : i ≠ s.depth - 1 := by omega
  by_cases h : s.depth ≤ 8
  · by_cases h8 : i < 8 <;> simp [h, h8, hne]
  · by_cases h8 : i < 8
    · simp [h, h8]
    · simp only [h, h8, ite_false]
      rw [List.getElem?_set_ne (by omega)]

theorem setTop_frame_top {s : GoStack β} (hv : s.Valid) (hd : 0 < s.depth) (f : β) :
    (s.setTop f).frame (s.depth - 1) = some f := by
  unfold GoStack.setTop GoStack.frame
  by_cases h : s.depth ≤ 8
  · simp [h, show s.depth - 1 < 8 by omega]
  · unfold GoStack.Valid at hv
    simp only [h, ite_false, show ¬ s.depth - 1 < 8 by omega]
    rw [show s.depth - 1 - 8 = s.depth - 1 - 8 from rfl, List.getElem?_set_self (by omega)]

/-- **setTop** replaces the frame on top. -/
theorem setTop_content {s : GoStack β} (hv : s.Valid) (hd : 0 < s.depth) (f : β) :
    (s.setTop f).content = s.content.dropLast ++ [f] := by
  obtain ⟨x, _, hc⟩ := content_last hv hd
  rw [hc, List.dropLast_concat]
  obtain ⟨d, hdd⟩ : ∃ d, s.depth = d + 1 := ⟨s.depth - 1, by omega⟩
  have htop := setTop_frame_top hv hd f
  rw [hdd, Nat.add_sub_cancel] at htop
  unfold GoStack.content
  rw [setTop_depth, hdd, content_succ _ _ _ htop,
    content_congr d (fun i hi => setTop_frame_lt s f i (by omega)), Nat.add_sub_cancel]

theorem pop_valid {s : GoStack β} (hv : s.Valid) : s.pop.Valid := by
  unfold GoStack.pop GoStack.Valid at *; simp; omega

/-- **pop** removes the frame on top. -/
theorem pop_content {s : GoStack β} (hv : s.Valid) : s.pop.content = s.content.dropLast := by
  by_cases hd : s.depth = 0
  · simp [GoStack.pop, GoStack.content, hd]
  · obtain ⟨x, _, hc⟩ := content_last hv (by omega)
    rw [hc, List.dropLast_concat]
    rfl

theorem reset_content (s : GoStack β) : s.reset.content = [] := rfl

theorem reset_valid (s : GoStack β) : s.reset.Valid := by
  unfold GoStack.reset GoStack.Valid; simp

/-! ### The list the model uses: top first -/

theorem toList_push {s : GoStack β} (hv : s.Valid) (f : β) :
    (s.push f).toList = f :: s.toList := by
  simp [GoStack.toList, push_content hv]

theorem toList_top {s : GoStack β} (hv : s.Valid) (hd : 0 < s.depth) :
    s.top = s.toList.head? := by
  simp [GoStack.toList, top_content hv hd]

theorem toList_setTop {s : GoStack β} (hv : s.Valid) (hd : 0 < s.depth) (f : β) :
    (s.setTop f).toList = f :: s.toList.tail := by
  simp [GoStack.toList, setTop_content hv hd, List.tail_reverse]

theorem toList_pop {s : GoStack β} (hv : s.Valid) : s.pop.toList = s.toList.tail := by
  simp [GoStack.toList, pop_content hv, List.tail_reverse]

theorem toList_reset (s : GoStack β) : s.reset.toList = [] := rfl

end Stack
end JuuriFormal
