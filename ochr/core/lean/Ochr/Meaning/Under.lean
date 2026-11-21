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

@[simp] theorem under_env (s : SState) : s.under.env = {} :: (if s.env.isEmpty then [{}] else s.env) := rfl

theorem under_env_ne (s : SState) (h : s.env ≠ []) : s.under.env = {} :: s.env := by
  show {} :: (if s.env.isEmpty then [{}] else s.env) = _
  rw [if_neg (by cases e : s.env with | nil => exact absurd e h | cons => simp)]

/-- The closure's frame is above frame 0. -/
theorem under_topIdx_pos (s : SState) : 0 < s.under.topIdx := by
  show 0 < (({} : SFrame) :: (if s.env.isEmpty then [{}] else s.env)).length - 1
  split <;> simp_all [List.length_pos_iff]
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
  by_cases h : s.env.isEmpty
  · have he : s.env = [] := List.isEmpty_iff.mp h
    cases p with
    | bind f i => cases f <;> simp [lookup, under, h, he, Pos.up]
    | temp f i => cases f <;> simp [lookup, under, h, he, Pos.up]
  · cases p <;> simp [lookup, under, h, Pos.up]

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

/-! ## A cell pushed on frame 0 -/

theorem lookup_pushCell_old (s : SState) (b : SBinding) (q : Pos) (h : (s.lookup q).isSome) :
    (s.pushCell b).lookup q = s.lookup q := by
  cases q with
  | temp f i =>
    simp only [lookup, pushCell, List.getElem?_modify]
    split <;> cases s.env[f]? <;> simp
  | bind f i =>
    simp only [lookup, pushCell, List.getElem?_modify] at h ⊢
    split
    · cases e : s.env[f]? with
      | none => simp
      | some fr =>
        rw [e] at h
        simp only [Option.bind_some, Option.isSome_map] at h
        have hi : i < fr.binds.length := by
          cases ei : fr.binds[i]? with
          | none => rw [ei] at h; cases h
          | some _ => exact (List.getElem?_eq_some_iff.mp ei).1
        simp [List.getElem?_append_left hi]
    · cases s.env[f]? <;> simp

theorem mem_positions_pushCell (s : SState) (b : SBinding) {q : Pos} (h : q ∈ s.positions) :
    q ∈ (s.pushCell b).positions := by
  rw [mem_positions] at h ⊢
  rw [lookup_pushCell_old s b q h]; exact h

theorem valAt_pushCell_old (s : SState) (b : SBinding) {q : Pos} (hq : q ∈ s.positions) :
    (s.pushCell b).valAt q = s.valAt q := by
  rw [valAt_eq, valAt_eq, lookup_pushCell_old s b q ((mem_positions s q).mp hq)]

theorem lookup_pushCell_new (s : SState) (b : SBinding) (q : Pos) (hq : (s.lookup q).isSome = false)
    {w : SVal} (e : (s.pushCell b).lookup q = some w) : w = b.val := by
  cases q with
  | temp f i =>
    exfalso
    simp only [lookup, pushCell, List.getElem?_modify] at e hq
    split at e
    · cases h : s.env[f]? with
      | none => rw [h] at e; simp at e
      | some fr =>
        rw [h] at e hq
        simp only [Functor.map, Option.map_some, Option.bind_some] at e hq
        rw [e] at hq; simp at hq
    · have e' : ((fun a => a) <$> s.env[f]?) = s.env[f]? := by cases s.env[f]? <;> rfl
      rw [e'] at e; rw [e] at hq; simp at hq
  | bind f i =>
    simp only [lookup, pushCell, List.getElem?_modify] at e hq
    split at e
    · cases h : s.env[f]? with
      | none => rw [h] at e; simp at e
      | some fr =>
        rw [h] at e hq
        simp only [Option.bind_some, Option.isSome_map, Option.isSome_eq_false_iff, Option.isNone_iff_eq_none] at hq
        have hi : ¬ i < fr.binds.length := fun hi => by
          rw [List.getElem?_eq_getElem hi] at hq; cases hq
        simp only [Functor.map, Option.map_some, Option.bind_some, Option.map_eq_some_iff] at e
        obtain ⟨b', hb', rfl⟩ := e
        rw [List.getElem?_append_right (by omega)] at hb'
        cases hk : i - fr.binds.length with
        | zero => rw [hk] at hb'; simp at hb'; rw [hb']
        | succ k => rw [hk] at hb'; simp at hb'
    · have e' : ((fun a => a) <$> s.env[f]?) = s.env[f]? := by cases s.env[f]? <;> rfl
      rw [e'] at e; rw [e] at hq; simp at hq

theorem valAt_pushCell (s : SState) (b : SBinding) (q : Pos) :
    (s.pushCell b).valAt q = s.valAt q ∨ (s.pushCell b).valAt q = b.val := by
  by_cases hq : q ∈ s.positions
  · left; exact valAt_pushCell_old s b hq
  · have hq' : (s.lookup q).isSome = false := by
      rw [mem_positions] at hq; cases h : (s.lookup q).isSome <;> simp_all
    rw [valAt_eq]
    cases e : (s.pushCell b).lookup q with
    | none => left; rw [valAt_of_not_mem s q hq]; rfl
    | some w => right; exact lookup_pushCell_new s b q hq' e

theorem live_pushCell {s : SState} (hsa : ShapeAt s) (b : SBinding) (y : Nat) :
    (s.pushCell b).Live y ↔ s.Live y := by
  rw [live_iff, live_iff]
  constructor
  · rintro ⟨q, _, hs⟩; exact ⟨q, (hsa q y hs).1, hs⟩
  · rintro ⟨q, hq, hs⟩; exact ⟨q, mem_positions_pushCell s b hq, hs⟩

@[simp] theorem pushCell_topIdx (s : SState) (b : SBinding) : (s.pushCell b).topIdx = s.topIdx := by
  simp [pushCell, topIdx]

@[simp] theorem pushCell_nextLoan (s : SState) (b : SBinding) : (s.pushCell b).nextLoan = s.nextLoan := rfl
@[simp] theorem pushCell_shape (s : SState) (b : SBinding) : (s.pushCell b).shape = s.shape := rfl

/-- A cell pushed, reading `l`: the invariant holds with `l` added to `L`. -/
theorem rinv_pushCell_read {s : SState} (hi : RInv L s) (b : SBinding) (l : Nat) (hb : b.val = fun ψ => ψ l) :
    RInv (fun y => L y ∨ y = l) (s.pushCell b) := by
  obtain ⟨h1, h2, hsa⟩ := hi
  have hlive := live_pushCell hsa b
  refine ⟨fun q => ?_, fun r x _ hs => ?_, fun q x hq => ?_⟩
  · rcases valAt_pushCell s b q with e | e
    · rw [e]; exact (h1 q).mono fun y hy => hy.elim (fun h => .inl (.inl h)) (fun h => .inr ((hlive y).mpr h))
    · rw [e, hb]; intro ψ ψ' hψ; exact hψ l (.inl (.inr rfl))
  · have hs' : s.shape r = some x := hs
    have hr' := (hsa r x hs').1
    rw [valAt_pushCell_old s b hr']
    exact (h2 r x hr' hs').mono fun y hy => by
      rcases hy with ⟨hL, hn⟩ | ⟨hy, hxy⟩
      · exact .inl ⟨.inl hL, fun h => hn ((hlive y).mp h)⟩
      · exact .inr ⟨(hlive y).mpr hy, hxy⟩
  · have hq' : s.shape q = some x := hq
    exact ⟨mem_positions_pushCell s b (hsa q x hq').1, (hsa q x hq').2⟩

/-- The cell just pushed: its position, a member of the state, holding the binding's value. -/
theorem pushCell_last (s : SState) (b : SBinding) (fr0 : SFrame) (h0 : s.env[0]? = some fr0) :
    Pos.bind 0 fr0.binds.length ∈ (s.pushCell b).positions ∧
    (s.pushCell b).valAt (.bind 0 fr0.binds.length) = b.val := by
  constructor
  · rw [mem_positions]; simp [lookup, pushCell, List.getElem?_modify, h0]
  · simp [valAt, pushCell, List.getElem?_modify, h0]

end SState

end Ochr.Meaning
