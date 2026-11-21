import Ochr.Meaning.Steps.ColumnC
import Ochr.Meaning.Steps.Machine.DecideFuelFF
import Ochr.Meaning.Steps.Machine.FormFacts

/-!
# `def C : Nat := let x = S(Z); x`, with the machine lane's theorems (lead8)

`ColumnC.column_C` assumes facts about the checker alone; here those the machine lane has proved are
discharged: `EvalInv` (`Machine.evalInvR`), `ZeroInv` (`Machine.zeroInv`), `DropNoopInv`
(`Machine.dropNoopInv`), `DecBack` (`Machine.decBack`), the growth of the tables (`grows_eval`, from
`machineGrows`) and the agreement of decisions across fuels (`Machine.decide_fuel_agree'`). In a
file of its own because the machine lane's files import `ColumnC`.
-/

namespace Ochr.Meaning.Steps.Form.ColumnC

open Ochr Ochr.Meaning Ochr.Meaning.Steps Ochr.Meaning.Steps.Form

/-- **The column applied to `C`, at the fuel-free table of the end state**: assumes four unreviewed
facts about the checker alone, `SuccInv`, `VarNumInv`, `LetInv`, `InvCore`. -/
theorem column_C_ff (hS : SuccInv) (hV : VarNumInv) (hL : LetInv) (hIC : InvCore) {g : Nat} (dm : DataModel)
    (ρ : Assignment) (φ : Future) {st st' : MState} {bh : Nat} {v : Value} {T? : Option Value} (hk : Kern stC st)
    (hm : Mode st) (htd : st.tailDecl = none)
    (h : Runs (Ochr.eval (g + 9) true bodyC (some .tNat)) st bh (v, T?) st') :
    ∃ r s', runT (KC dm (checkerDecisionsFF st')) ρ φ st.tailNext (hintM (KC dm (checkerDecisionsFF st')) ρ (some .tNat))
        bodyC (SM' (KC dm (checkerDecisionsFF st')) ρ stC) = some (r, s') ∧
      r.1 = .el0 Nat 1 ∧ r.1 ∈ₛ[dm.read] TyM.nat ∧ r.2.m = TyM.nat :=
  column_C Machine.evalInvR Machine.zeroInv hS hV hL Machine.dropNoopInv hIC Machine.decBack (grows_eval _ _ _ _) dm _
    ρ φ hk hm htd (decTab_ff st' _ (fun _ => Machine.decide_fuel_agree' _) (Machine.decide_fuel_agree' st')) h

end Ochr.Meaning.Steps.Form.ColumnC
