import Ochr.Meaning.Steps.ColumnI
import Ochr.Meaning.Strict.WitnessFix

/-!
# The column `I`: the `.fix` clause's reading of `I`, and its body frame (lead14)

The reference's `.fix` clause forms `I`'s closure (for a global, in `stateOf 0 []`) and runs its body,
at each argument, in one frame (`RunCongr.fixBodyAt`): `self` (the stage-0 closure at the weakened type),
then the parameter. Here: the clause's reading of `Π(n : Nat). Nat` (`runDoms = psI`, `codOf = outI`),
the body's run reading neither the assignment, the tail flag nor the hint (`runT_bodyI`), `EndsOk []`,
and the body frame `frI` both sides hold. Still to prove (next lead): the checker's start state read as
a reference state is `[{}, frI]` (`SM'`'s bindings: `Binding.refTy_marked`/`_unmarked`, `Aux.valAt_SM_eq`;
the structure-instance `show` needs each binding on one line), `fixBodyAt`'s state is `[frI]`, and the
bridge between the two, `FrameDrop0` (docs/31 D126).
-/

namespace Ochr.Meaning.Steps.Form.ColumnI

open Ochr Ochr.Meaning Ochr.Meaning.Steps Ochr.Meaning.Steps.Form Ochr.Meaning.Strict.Witness

section
variable (K : RunCtx) (ρ : Assignment) (φ : Future)
theorem runT_nat (tl : Bool) (h : TyS) (s : SState) :
    runT K ρ φ tl h .nat s = some ((.ty TyM.nat, .plain (TyM.univ 1)), s) := by
  rw [runT]; rfl
theorem bindsOf_nat (s : SState) (hd : K.D.paramDecls (scopeOf s) [.nat] = [.other]) :
    bindsOf K ρ φ s [.nat] = [(fun _ => .plain TyM.nat, .other)] := by
  unfold bindsOf; rw [hd]
  simp only [runBinds, mkBind, runT_nat]
  rfl
theorem codOf_nat (s : SState) (bs : List PBind) : codOf K ρ φ s bs .nat = outI := by
  unfold codOf; simp only [runT_nat]; rfl
theorem runDoms_nat (s : SState) (hd : K.D.paramDecls (scopeOf s) [.nat] = [.other]) :
    runDoms K ρ φ s [.nat] = psI := by
  unfold runDoms; rw [bindsOf_nat K ρ φ s hd]; rfl
theorem runT_place0 (ρ ρ' : Assignment) (tl tl' : Bool) (h h' : TyS) :
    runT K ρ φ tl h (.place (.var 0)) = runT K ρ' φ tl' h' (.place (.var 0)) := by
  funext s; rw [runT, runT]
theorem runT_bodyI (ρ ρ' : Assignment) (tl tl' : Bool) (h h' : TyS) (s : SState) :
    runT K ρ φ tl h bodyI s = runT K ρ' φ tl' h' bodyI s := by
  unfold bodyI
  conv => lhs; rw [runT]
  conv => rhs; rw [runT]
  rw [runT_place0 K φ ρ ρ' false false]
theorem endsOk_nil (s : SState) : EndsOk K φ [] s := by
  unfold EndsOk; exact trivial

end

/-- The body's frame, on both sides: `self` the stage-0 closure at the weakened type, `n` the number `a`. -/
noncomputable def frI (R : DataRead) (φ : Future) (a : Nat) : SFrame :=
  { binds := [{ ty := .plain (selfTy R), val := fun _ => selfSem R φ, decl := .pi .other },
      { ty := .plain TyM.nat, val := fun _ => .el0 Nat a, decl := .other }] }

end Ochr.Meaning.Steps.Form.ColumnI
