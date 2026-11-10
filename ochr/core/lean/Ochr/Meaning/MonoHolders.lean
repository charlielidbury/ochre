import Ochr.Meaning.Mono

/-!
# D14's holder invariant, and the missing half of (WF6)

* `DropHolderCounterexample`: D14's "every live label has exactly one holder, from creation to
  its end" is not kept by `run`'s `.letIn` clause. Its [Drop] ends `T.label`, the label of the
  bound *type*; when the body re-pointed the binding (`x := &b` at a root makes `x` the holder of
  `b`'s label, D13), the label `x` holds at the drop is a different one, which is not ended, and
  `dropLast` removes the position without clearing its shape entry. The label then has no live
  holder although nothing fixed its final content, and the next `pushBind` at that position
  resurrects it as a holder of a borrow it never made.
* `WF6Borrow`, `shapeBelow_sstate`: the clause (WF6) lacks, every borrow's own label below the
  counter, and `ShapeBelow` of the checker's state from it.
* `callOf_readsBelow`: a call reads no label at or above the counter (the item `Mono.lean` left
  open): taking the arguments' holders only forgets, `updList` adds no dependence
  (`updList_indep`), and a returned borrow reads only its own fresh label besides.
-/

namespace Ochr.Meaning

open Classical

namespace DropHolderCounterexample

/-- The state just before `let x = &a; x := &b; ()` drops `x`: `x` (position `bind 0 0`) holds
`b`'s label `1`; the bound type's label is `a`'s label `0`, already ended by the assignment. -/
def s₀ : SState :=
  { env := [{ binds := [{ ty := .plain .err, val := fun _ => .el0 Nat 5 }] }],
    shape := fun p => if p = .bind 0 0 then some 1 else none, nextLoan := 2 }

theorem positions_s₀ : s₀.positions = [.bind 0 0] := by
  simp [SState.positions, s₀, Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size]

/-- The `.letIn` drop: end the type's label `0`, then `dropLast`. -/
noncomputable def dropped : SState := (s₀.endLabel 0).dropLast

theorem endLabel_s₀ : s₀.endLabel 0 = s₀ :=
  SState.endLabel_of_find_none s₀ 0 (by rw [positions_s₀]; rfl)

theorem positions_dropped : dropped.positions = [] := by
  rw [dropped, endLabel_s₀]
  simp [SState.dropLast, SState.positions, s₀, SState.topIdx,
    Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size]

/-- **Label `1` leaves the live set without being ended** (nothing fixed `b`'s final content),
and **a fresh binding at the same position resurrects it**: the new binding holds `1`, a borrow it
never made. So "every live label has exactly one holder, from creation to its end" fails across
`.letIn`. Fix: end the label the position holds at the drop (`s.shape pos`), not `T.label`, and
clear the shape entry of every position `dropLast`/`popFrame` removes. -/
theorem dropped_resurrects (b : SBinding) :
    1 ∉ dropped.liveLabels ∧ 1 ∈ (dropped.pushBind b).liveLabels := by
  refine ⟨fun h => ?_, ?_⟩
  · obtain ⟨p, hp, _⟩ := (SState.mem_liveLabels _ _).mp h
    rw [positions_dropped] at hp
    cases hp
  · refine (SState.mem_liveLabels _ _).mpr ⟨.bind 0 0, ?_, by rw [dropped, endLabel_s₀]; rfl⟩
    have : (dropped.pushBind b).positions = [.bind 0 0] := by
      rw [dropped, endLabel_s₀]
      simp [SState.dropLast, SState.pushBind, SState.positions, s₀,
        SState.topIdx, Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size]
    rw [this]; simp

end DropHolderCounterexample

/-- The half of (WF6) it lacks: every borrow's own label is below the label counter. (WF6 bounds
`Value.loans`, and `Value.loans (.borrow _ w) = w.loans` omits the borrow's label.) Stated at every
position; at a non-position `valAt` reads the default value, which is not a borrow. -/
def WF6Borrow (st : MState) : Prop := ∀ p l w, valAt st.env p = .borrow l w → l < st.nextLoan

/-- With the missing clause, the checker's state read as a semantic state has every held label
below its counter (milestone 3: the base case of `ShapeBelow` for the step lemmas, from `Good`). -/
theorem shapeBelow_sstate (dm : DataModel) (C : CodeMeaning) (Γ : List IndDecl) (ρ : Assignment)
    (st : MState) (h : WF6Borrow st) : (st.sstate dm C Γ ρ).ShapeBelow := by
  intro p l hp
  change Env.shape st.env p = some l at hp
  show l < st.nextLoan
  unfold Env.shape at hp
  split at hp
  · rename_i l' w hv
    cases hp; exact h p _ w hv
  · cases hp

/-! ## `ReadsBelow` for a call -/

/-- Updating the future at a list of labels does not make a meaning depend on a label it did not. -/
theorem updList_indep {v : SVal} {l : Nat} (hv : ¬ v.DependsOn l) :
    ∀ (L : List (Nat × Sem)) (φ : Future) (x : Sem), v ((φ.upd l x).updList L) = v (φ.updList L)
  | [], φ, x => SVal.not_dependsOn hv φ x
  | (l', e) :: rest, φ, x => by
    simp only [Future.updList]
    by_cases h : l = l'
    · subst h; rw [Future.upd_upd_same]
    · rw [Future.upd_comm φ h]; exact updList_indep hv rest _ x

namespace SState

theorem readsBelow_takeLabel {s : SState} (hs : s.ReadsBelow) (l : Nat) : (s.takeLabel l).ReadsBelow := by
  unfold takeLabel
  split
  · next r _ =>
    have h := readsBelow_setAt hs r (fun _ => .moved) fun _ ⟨_, _, hne⟩ => absurd rfl hne
    intro p k hd
    exact h p k hd
  · exact hs

theorem readsBelow_foldl_takeLabel {s : SState} (hs : s.ReadsBelow) :
    ∀ ls : List Nat, (ls.foldl takeLabel s).ReadsBelow := by
  intro ls
  induction ls generalizing s with
  | nil => exact hs
  | cons l ls ih => exact ih (readsBelow_takeLabel hs l)

/-- Rewriting each meaning as itself at an updated future keeps the invariant. -/
theorem readsBelow_mapVals_updList {s : SState} (hs : s.ReadsBelow) (L : List (Nat × Sem)) :
    (s.mapVals fun _ v φ' => v (φ'.updList L)).ReadsBelow := by
  intro p l ⟨φ, x, hne⟩
  refine Classical.byContradiction fun hl => hne ?_
  have hlt : ¬ (s.valAt p).DependsOn l := fun hd => hl (hs p l hd)
  show (s.mapVals _).valAt p φ = (s.mapVals _).valAt p (φ.upd l x)
  rw [valAt_mapVals]
  split
  · exact (updList_indep hlt L φ x).symm
  · rfl

end SState

/-- **A call reads no label not yet handed out**: taking the arguments' holders only forgets; a
borrow-free result fixes the arguments' labels; a borrow result reads its own fresh label `k`
and otherwise what each meaning read before. Milestone 3: `Steps/Call.lean`'s `closeCall_step`
(with `callOf_fresh`). -/
theorem callOfL_readsBelow.{u} (L : Lvl.{u}) (ps : List PiParam) (out : PiOut) (fv : Sem)
    (args : List Res) (s : SState) (hs : s.ReadsBelow) {r : Sem} {T : TyS} {s' : SState}
    (h : callOfL L ps out fv args s = some ((r, T), s')) : s'.ReadsBelow := by
  unfold callOfL at h
  try dsimp only at h
  have hs₀ := SState.readsBelow_foldl_takeLabel hs (args.filterMap (·.2.label))
  split at h
  · simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨_, rfl⟩ := h
    exact SState.readsBelow_mapVals_updList hs₀ _
  · simp only [SState.freshLoan, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨_, rfl⟩ := h
    generalize (args.filterMap fun a : Res => a.2.label).foldl SState.takeLabel s = s₀ at hs₀ ⊢
    refine SState.readsBelow_pushTempShaped ?_ _ _ fun _ ⟨_, _, hne⟩ => absurd rfl hne
    intro p l ⟨φ, x, hne⟩
    show l < s₀.nextLoan + 1
    by_cases hlk : l = s₀.nextLoan
    · omega
    · refine Nat.lt_succ_of_lt (Classical.byContradiction fun hl => hne ?_)
      have hlt : ¬ (s₀.valAt p).DependsOn l := fun hd => hl (hs₀ p l hd)
      show (SState.mapVals _ _).valAt p φ = (SState.mapVals _ _).valAt p (φ.upd l x)
      rw [SState.valAt_mapVals]
      split
      · dsimp only
        rw [Future.upd_other φ x (Ne.symm hlk)]
        cases hd : L.dec _ (φ s₀.nextLoan) with
        | none => rfl
        | some y => exact (updList_indep hlt _ φ x).symm
      · rfl
  · cases h

theorem callOf_readsBelow (fv : Res) (args : List Res) (s : SState) (hs : s.ReadsBelow)
    {r : Sem} {T : TyS} {s' : SState} (h : callOf fv args s = some ((r, T), s')) : s'.ReadsBelow := by
  unfold callOf at h
  split at h
  · split at h
    · exact callOfL_readsBelow _ _ _ _ _ _ hs h
    · exact callOfL_readsBelow _ _ _ _ _ _ hs h
    · exact callOfL_readsBelow _ _ _ _ _ _ hs h
    · cases h
  · cases h

end Ochr.Meaning
