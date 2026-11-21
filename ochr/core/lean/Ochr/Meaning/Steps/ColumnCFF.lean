import Ochr.Meaning.Steps.ColumnC
import Ochr.Meaning.Steps.Machine.DecideFuelFF
import Ochr.Meaning.Steps.Machine.FormFacts

/-!
# `def C : Nat := let x = S(Z); x`, with the machine lane's theorems (lead8)

`ColumnC.column_C` assumes facts about the checker alone; here those the machine lane has proved are
discharged: `EvalInv` (`Machine.evalInvR`), `ZeroInv` (`Machine.zeroInv`), `SuccInv` (`Machine.succInvR`),
`LetInv` (`Machine.letInvR`), `DropNoopInv`
(`Machine.dropNoopInv`), `DecBack` (`Machine.decBack`), the growth of the tables (`grows_eval`, from
`machineGrows`) and the agreement of decisions across fuels (`Machine.decide_fuel_agree'`). In a
file of its own because the machine lane's files import `ColumnC`.
-/

namespace Ochr.Meaning.Steps.Form

open Ochr Ochr.Meaning Ochr.Meaning.Steps

/-- The machine lane's `ModeEq` is the column's. -/
theorem ModeEq.ofMachine {a b : MState} (h : Machine.ModeEq a b) : ModeEq a b :=
  ⟨h.headEval, h.copying, h.inPlace, h.erased⟩

/-- **`SuccInv`, proved**: the machine lane's `Machine.succInvR`. -/
theorem succInv : SuccInv := by
  intro n typed u hint st st' bh v T? hm htn htd h
  obtain ⟨st₀, st₁, v₀, T₀, bh₁, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩ :=
    Machine.succInvR n typed u hint st st' bh v T? hm htn htd h
  exact ⟨st₀, st₁, v₀, T₀, bh₁, h1, h2, h3, h4, h5, h6, h7, h8, .ofMachine h9, h10, h11⟩

/-- **`LetInv`, proved**: the machine lane's `Machine.letInvR`. -/
theorem letInv : LetInv := by
  intro n x u w hint st st' bh v T? D hm htn htd hD h
  obtain ⟨du, st₀, st₁, stB, st₂, st₃, v₀, r, T₀, p, bh₁, bh₂, bh₃, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11,
    h12, h13, h14, h15, h16⟩ := Machine.letInvR n x u w hint st st' bh v T? D hm htn htd hD h
  exact ⟨du, st₀, st₁, stB, st₂, st₃, v₀, r, T₀, p, bh₁, bh₂, bh₃, h1, h2, h3, h4, h5, h6, h7, h8, .ofMachine h9, h10,
    h11, h12, h13, .ofMachine h14, h15, h16⟩

end Ochr.Meaning.Steps.Form

namespace Ochr.Meaning.Steps.Form.ColumnC

open Ochr Ochr.Meaning Ochr.Meaning.Steps Ochr.Meaning.Steps.Form

/-- **The column applied to `C`, at the fuel-free table of the end state**: assumes two unreviewed
facts about the checker alone: `VarNumInvK` (the machine lane's proved `VarNumInv` with `KeepsInv`
beside its `Quiet.refl` stretch) and the state-level lemmas `InvSteps` (lead9). -/
theorem column_C_ff (hVK : VarNumInvK) (hI : InvSteps) {g : Nat} (dm : DataModel)
    (ρ : Assignment) (φ : Future) {st st' : MState} {bh : Nat} {v : Value} {T? : Option Value} (hk : Kern stC st)
    (hm : Mode st) (htd : st.tailDecl = none)
    (h : Runs (Ochr.eval (g + 9) true bodyC (some .tNat)) st bh (v, T?) st') :
    ∃ r s', runT (KC dm (checkerDecisionsFF st')) ρ φ st.tailNext (hintM (KC dm (checkerDecisionsFF st')) ρ (some .tNat))
        bodyC (SM' (KC dm (checkerDecisionsFF st')) ρ stC) = some (r, s') ∧
      r.1 = .el0 Nat 1 ∧ r.1 ∈ₛ[dm.read] TyM.nat ∧ r.2.m = TyM.nat :=
  column_C Machine.evalInvR Machine.zeroInv succInv Machine.varNumInv hVK letInv Machine.dropNoopInv hI Machine.decBack
    (grows_eval _ _ _ _) dm _ ρ φ hk hm htd
    (decTab_ff st' _ (fun _ => Machine.decide_fuel_agree' _) (Machine.decide_fuel_agree' st')) h

end Ochr.Meaning.Steps.Form.ColumnC
