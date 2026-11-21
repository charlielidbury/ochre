import Ochr.Meaning.Steps.ColumnLet
import Ochr.Meaning.DecisionsFF
import Ochr.Meaning.Regress.GenNeutralContent

/-!
# The column's program at its start: every hypothesis of a step, instantiated (lead7)

`def C : Nat := let x = S(Z); x`. `checkDef`'s constant branch evaluates the body from a state with
one empty frame (`modify fun s => { s with env := #[{}], … }`), with the goal `Nat` as the hint. The
kernel of that state (`Kern`) is `stC`'s: one empty frame, no globals, no declarations, no unknowns,
no labels, no goal. Here every bundle of hypotheses a step takes is instantiated at `stC` and the
run context `KC dm D`, and each is a theorem (kernel-checked):

* the checker's side: `Mode`, `Pre` (`CtxS`, `Inv`, `Asg`);
* the reference's: the checker's state read as a reference state (`SM'`), related (`Rel`, by
  `Rel.start`) and good (`SGood`);
* the context: `FundCtx`;
* the term: `valsOk`, `absBelow`, `hasHolePrim`;
* the decisions, wherever the column reads them, at any table aligned with the checker at `stC`
  (`DecTab D stC`): by the checker's own decision procedures, run at the scope states (kernel
  evaluation, `decide +kernel`, as `Regress/OpenFalse.lean` does).

The checker's run of the body itself is not kernel-evaluable (the variable read goes through code
the kernel does not unfold); it is `#guard`ed in `Steps/ColumnC.lean`, where the column is applied.
-/

namespace Ochr.Meaning.Steps.Form.ColumnC

open Ochr Ochr.Meaning Ochr.Meaning.Steps Ochr.Meaning.Steps.Form

/-- The body of `def C : Nat := let x = S(Z); x`. -/
def bodyC : Term := .letIn ⟨"x"⟩ (.succ .zero) (.place (.var 0))

/-- The kernel of the state `checkDef` evaluates a constant's body from: one empty frame. -/
def stC : MState := { env := #[{}] }

/-- No globals are read; each means `0 : Nat`. -/
def CC : CodeMeaning :=
  { global := fun _ => (.el0 Nat 0, .plain TyM.nat), sealed := fun _ _ _ _ => .err, clo := fun _ _ _ _ _ => .err,
    pi := fun _ _ _ _ _ => TyM.err, paramTy := fun _ _ _ _ => .plain TyM.err }

/-- The run's context: no declarations, the decisions `D`. -/
def KC (dm : DataModel) (D : Decisions) : RunCtx := { dm := dm, Γ := [], C := CC, D := D }

/-- The reading of `S(Z)`, which `x` is bound at (the checker's: `other`). -/
def duC : DeclInfo := .other

variable (dm : DataModel) (D : Decisions) (ρ : Assignment) (φ : Future)

/-! ## The checker's side -/

theorem mode_stC : Mode stC := by
  sorry

theorem topReadings_stC : DecideScope.topReadings stC = [] := by
  sorry

theorem pre_stC : Pre (KC dm D) ρ stC := by
  sorry

/-! ## The reference's side -/

theorem rel_stC : Rel (KC dm D) ρ φ id stC (SM' (KC dm D) ρ stC) := by
  sorry

theorem sgood_stC : Strict.SGood dm [] φ (SM' (KC dm D) ρ stC) := by
  sorry

/-! ## The context and the term -/

theorem fundCtx_KC : Strict.FundCtx (KC dm D) := by
  sorry

theorem valsOk_bodyC (K : RunCtx) : bodyC.valsOk (Strict.ValsP K ρ φ) := by
  sorry

theorem absBelow_bodyC (m : Nat) : bodyC.absBelow m := by
  sorry

theorem hasHolePrim_bodyC : bodyC.hasHolePrim = false := by
  sorry

/-! ## The decisions the column reads, at a table aligned with the checker at `stC` -/

section
variable {D} (hd : DecTab D stC)
include hd

theorem flags_bodyC : D.flags [] bodyC = (false, false) := by
  sorry

theorem flags_SZ : D.flags [] (.succ .zero) = (false, false) := by
  sorry

theorem flags_Z : D.flags [] .zero = (false, false) := by
  sorry

theorem declOf_SZ : D.declOf [] (.succ .zero) = duC := by
  sorry

theorem flags_x : D.flags [duC] (.place (.var 0)) = (false, false) := by
  sorry

end

end Ochr.Meaning.Steps.Form.ColumnC
