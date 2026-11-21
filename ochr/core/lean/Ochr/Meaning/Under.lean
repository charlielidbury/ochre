import Ochr.Meaning.LocalityRun

/-!
# A state under a fresh bottom frame (`SState.under`, docs/31 D126)

A closure's body runs in its creation state under a fresh bottom frame, `self` and the parameters on
the top frame (the checker's `checkFix` frames). `under` renames every position one frame up
(`Pos.up`) and adds an empty frame 0: it changes no meaning, no holder and no label, so the
invariant `run_congr` carries (`RInv`) holds under it.
-/

namespace Ochr.Meaning

namespace SState

variable {L : Nat → Prop}

@[simp] theorem down?_up (p : Pos) : p.up.down? = some p := by cases p <;> rfl

/-- A position of `s.under` is one of `s`'s, moved up, or in the new frame 0. -/
theorem pos_under_cases (p : Pos) : (∃ q : Pos, p = q.up) ∨ p.down? = none := by
  cases p with
  | bind f i => cases f with
    | zero => exact .inr rfl
    | succ f => exact .inl ⟨.bind f i, rfl⟩
  | temp f i => cases f with
    | zero => exact .inr rfl
    | succ f => exact .inl ⟨.temp f i, rfl⟩

@[simp] theorem under_env (s : SState) : s.under.env = {} :: s.env := rfl
@[simp] theorem under_nextLoan (s : SState) : s.under.nextLoan = s.nextLoan := rfl
@[simp] theorem under_heldTy (s : SState) : s.under.heldTy = s.heldTy := rfl
@[simp] theorem under_heldMem (s : SState) : s.under.heldMem = s.heldMem := rfl

theorem under_shape_up (s : SState) (p : Pos) : s.under.shape p.up = s.shape p := by
  show p.up.down?.bind s.shape = s.shape p
  rw [down?_up]; rfl

theorem under_shape_none (s : SState) {p : Pos} (h : p.down? = none) : s.under.shape p = none := by
  show p.down?.bind s.shape = none
  rw [h]; rfl

theorem lookup_under_up (s : SState) (p : Pos) : s.under.lookup p.up = s.lookup p := by
  cases p <;> rfl

theorem lookup_under_none (s : SState) {p : Pos} (h : p.down? = none) : s.under.lookup p = none := by
  cases p with
  | bind f i => cases f with
    | zero => simp [lookup, under]
    | succ f => cases h
  | temp f i => cases f with
    | zero => simp [lookup, under]
    | succ f => cases h

theorem valAt_under_up (s : SState) (p : Pos) : s.under.valAt p.up = s.valAt p := by
  rw [valAt_eq, valAt_eq, lookup_under_up]

theorem valAt_under_none (s : SState) {p : Pos} (h : p.down? = none) : s.under.valAt p = fun _ => .err := by
  rw [valAt_eq, lookup_under_none s h]; rfl

theorem mem_positions_under_up (s : SState) (p : Pos) : p.up ∈ s.under.positions ↔ p ∈ s.positions := by
  rw [mem_positions, mem_positions, lookup_under_up]

theorem not_mem_positions_under (s : SState) {p : Pos} (h : p.down? = none) : p ∉ s.under.positions := by
  rw [mem_positions, lookup_under_none s h]; simp

theorem live_under (s : SState) (y : Nat) : s.under.Live y ↔ s.Live y := by
  rw [live_iff, live_iff]
  constructor
  · rintro ⟨p, hp, hs⟩
    rcases pos_under_cases p with ⟨q, rfl⟩ | h
    · exact ⟨q, (mem_positions_under_up s q).mp hp, by rw [← under_shape_up]; exact hs⟩
    · exact absurd hp (not_mem_positions_under s h)
  · rintro ⟨q, hq, hs⟩
    exact ⟨q.up, (mem_positions_under_up s q).mpr hq, by rw [under_shape_up]; exact hs⟩

/-- `under` keeps the invariant `run_congr` carries. -/
theorem rinv_under {s : SState} (h : RInv L s) : RInv L s.under := by
  obtain ⟨h1, h2, hsa⟩ := h
  have hl := live_under s
  refine ⟨fun p => ?_, fun r x hr hs => ?_, fun p x hp => ?_⟩
  · rcases pos_under_cases p with ⟨q, rfl⟩ | e
    · rw [valAt_under_up]; exact (h1 q).mono fun y hy => hy.imp_right (hl y).mpr
    · rw [valAt_under_none s e]; exact FT.const _ _
  · rcases pos_under_cases r with ⟨q, rfl⟩ | e
    · rw [under_shape_up] at hs
      rw [valAt_under_up]
      exact (h2 q x ((mem_positions_under_up s q).mp hr) hs).mono fun y hy => by
        rcases hy with ⟨hL, hn⟩ | ⟨hy, hxy⟩
        · exact .inl ⟨hL, fun h' => hn ((hl y).mp h')⟩
        · exact .inr ⟨(hl y).mpr hy, hxy⟩
    · exact absurd hr (not_mem_positions_under s e)
  · rcases pos_under_cases p with ⟨q, rfl⟩ | e
    · rw [under_shape_up] at hp
      exact ⟨(mem_positions_under_up s q).mpr (hsa q x hp).1, (hsa q x hp).2⟩
    · rw [under_shape_none s e] at hp; cases hp

end SState

end Ochr.Meaning
