import Ochr.Meaning.Steps.Machine.ConstRunJ
import Ochr.Meaning.Steps.Machine.CallJBody

/-!
# Column `J` with `ConstRunJ` discharged (machine8; toward `column_J_free`)

`column_J_def` with the checker fact `ConstRunJ` proved (`constRunJ`). It still ASSUMES 4 facts about
the checker: `FixRunI`, `CallJInv`, `VarNumAInv`, `InvNumA` (all read and judged true; `CallJInv`'s
proof is half-built: `CallJEval.lean`, `NoStuck.lean`, `CallJBody.lean`, plan in `HANDOFF.md`). Root-imported so the
default build checks the proved parts.
-/

namespace Ochr.Meaning.Steps.Form.ColumnJ

open Ochr Ochr.Meaning Ochr.Meaning.Steps

/-- **The column `J` from the checker's acceptance of `I` and of `J`, `ConstRunJ` discharged.** Assumes 4
facts about the checker: `FixRunI`, `CallJInv`, `VarNumAInv`, `InvNumA`. -/
theorem column_J_def4 (hFI : ColumnI.FixRunI) (hC : CallJInv) (hV : VarNumAInv) (hN : InvNumA)
    (dm : DataModel) (ρ : Assignment) (φ : Future) {fuelI fuelJ : Nat} {st₁ st₂ : MState}
    (haccI : Runs (checkDef ParGuards.defI) {} fuelI () st₁)
    (haccJ : Runs (checkDef CallGuards.defJ) { globals := [ColumnI.gI] } fuelJ () st₂) :
    ∃ (sI' st' : MState) (v : Value) (r : Res) (s' : SState),
      runT (KJ dm (checkerDecisionsFF st') (fI dm (checkerDecisionsFF sI') ρ φ)) ρ φ false
        (hintM (KJ dm (checkerDecisionsFF st') (fI dm (checkerDecisionsFF sI') ρ φ)) ρ (some .tNat)) CallGuards.bodyJ
        (SM' (KJ dm (checkerDecisionsFF st') (fI dm (checkerDecisionsFF sI') ρ φ)) ρ CallGuards.stJ) = some (r, s') ∧
      r.1 = .el0 Nat 1 ∧ r.1 ∈ₛ[dm.read] TyM.nat ∧ r.2.m = TyM.nat ∧ v = .succ .zero ∧
      meanV (KJ dm (checkerDecisionsFF st') (fI dm (checkerDecisionsFF sI') ρ φ)) ρ φ (.plain TyM.nat) v = r.1 :=
  column_J_def hFI Machine.constRunJ hC hV hN dm ρ φ haccI haccJ

end Ochr.Meaning.Steps.Form.ColumnJ
