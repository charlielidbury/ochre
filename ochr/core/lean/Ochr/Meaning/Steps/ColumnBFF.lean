import Ochr.Meaning.Steps.ColumnBSim
import Ochr.Meaning.Steps.ColumnCFF
import Ochr.Meaning.Steps.Machine.InvShape

/-!
# `def B : Nat := (let x = S(Z); let y = &x; *y := Z; x)`, with the machine lane's theorems (lead9)

`ColumnB.column_B` at the fuel-free table of the end state, the facts the machine lane has proved
discharged: `EvalInv` (`Machine.evalInvR`), `ZeroInv` (`Machine.zeroInv`), `SuccInv`
(`Machine.succInvR`), `BorrowNumInv` (`Machine.borrowNumInv`), `LetInv` (`Machine.letInvR`),
`DropNoopInv` (`Machine.dropNoopInv`), `DecBack` (`Machine.decBack`), the tables' growth and the
agreement of decisions across fuels. D112's invalidation is empty in the fuel-free table by
definition. In a file of its own because the machine lane's files import `ColumnC`.
-/

namespace Ochr.Meaning.Steps.Form.ColumnB

open Ochr Ochr.Meaning Ochr.Meaning.Steps Ochr.Meaning.Steps.Form
open ColumnC

/-- **The borrow column applied to `B`, at the fuel-free table of the end state.** Assumes three
facts about the checker's runs not yet proved (`AssignDerefInv`, `SeqInv`, `VarEndInv`), the
state-level lemmas `InvSteps`, and that the fuel-free table is local in its places (`PlaceLocal`;
the machine lane's `placeLocal_ff`, in progress): every run of the checker's `eval` on `B`'s body
from the constant-body start state makes the strict run of the body succeed with `0`, a member of
`Nat`, at type `Nat`. -/
theorem column_B_ff (hA : AssignDerefInv) (hVE : VarEndInv) (hSq : SeqInv) (hI : InvSteps) {g : Nat}
    (dm : DataModel) (ρ : Assignment) (φ : Future) {st st' : MState} {bh : Nat} {v : Value} {T? : Option Value}
    (hk : Kern stC st) (hm : Mode st) (htd : st.tailDecl = none)
    (h : Runs (Ochr.eval (g + 15) true bodyB (some .tNat)) st bh (v, T?) st')
    (hPL : PlaceLocal (checkerDecisionsFF st')) :
    ∃ r s', runT (KC dm (checkerDecisionsFF st')) ρ φ st.tailNext (hintM (KC dm (checkerDecisionsFF st')) ρ (some .tNat))
        bodyB (SM' (KC dm (checkerDecisionsFF st')) ρ stC) = some (r, s') ∧
      r.1 = .el0 Nat 0 ∧ r.1 ∈ₛ[dm.read] TyM.nat ∧ r.2.m = TyM.nat :=
  column_B Machine.evalInvR Machine.zeroInv succInv Machine.borrowNumInv hA hVE hSq letInv Machine.dropNoopInv hI
    Machine.decBack (grows_eval _ _ _ _) dm _ hPL (fun _ _ => rfl) ρ φ hk hm htd
    (decTab_ff st' _ (fun _ => Machine.decide_fuel_agree' _) (Machine.decide_fuel_agree' st')) h

end Ochr.Meaning.Steps.Form.ColumnB
