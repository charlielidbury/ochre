import Ochr.Meaning.Steps.ColumnW
import Ochr.Meaning.Steps.BorrowParStepK

/-!
# The column `K` (lead20, 2026-11-22; docs/31 D145)

`def K (r : &Nat) : &Nat := r`, the first function returning a borrow. At the function level: the reference's `.fix`
clause forms `K`'s closure from the empty state, a member of `Π(r : &Nat). &Nat`, at the checker's own table
(`column_K_ff`), with NO assumed fact (D141's restated `OutGood` is what makes the closure lemma at a returned borrow
apply, `closure_mem_K`). The body's step is `BorrowParStepK.body_simK`.
-/

namespace Ochr.Meaning.Steps.Form.ColumnW

open Ochr Ochr.Meaning Ochr.Meaning.Steps Ochr.Meaning.Steps.Form
open Ochr.Meaning.Strict.Witness
open Ochr.Meaning.Regress.GenNeutralContent (runs_out)

section
variable {dm : DataModel} {D : Decisions} {φ : Future}

/-- **`K`'s closure, as the reference's `.fix` clause forms it from the empty state**: the run succeeds at
`Π(r : &Nat). &Nat` (`piTyAt _ 1 psW outK`), leaves the state as it was, and the closure is a member of that type. At
every table aligned with the checker at `stK`, every assignment, future, tail flag and hint. No assumed fact. -/
theorem column_K_run (ρ : Assignment) (hDK : DecTab D stK) (tl : Bool) (hint' : TyS) :
    ∃ f, runT (KB "K" outK dm D φ) ρ φ tl hint' fixK (emptyState 0)
        = some ((f, .plain (piTyAt dm.read 1 psW outK)), emptyState 0) ∧ f ∈ₛ[dm.read] piTyAt dm.read 1 psW outK := by
  obtain ⟨hd1, hd2, hps, hfl, hflb, hcp⟩ := fixDecK hDK
  have hpd : (KB "K" outK dm D φ).D.paramDecls (scopeOf (emptyState 0)) [.ref .nat] = [.ref .other] := by
    show D.paramDecls [] [.ref .nat] = [.ref .other]
    simp [Decisions.paramDecls, Decisions.teleDecls, hd1]
  have hsort : fixSort (KB "K" outK dm D φ) (emptyState 0) [⟨"r"⟩] [.ref .nat] (.ref .nat) = 1 := hps
  have h1 := bindsOf_ref (KB "K" outK dm D φ) ρ φ _ hpd
  have h2 : (KB "K" outK dm D φ).D.typeDecl ((KB "K" outK dm D φ).D.teleDecls (scopeOf (emptyState 0)) [.ref .nat])
      (.ref .nat) = .ref .other := by
    show D.typeDecl (D.teleDecls [] [.ref .nat]) (.ref .nat) = .ref .other
    simp [Decisions.teleDecls, hd1, hd2]
  have hty : fixTy (KB "K" outK dm D φ) ρ φ (emptyState 0) [⟨"r"⟩] [.ref .nat] (.ref .nat) = piTyAt dm.read 1 psW outK := by
    unfold fixTy; rw [hsort, runDoms_ref _ ρ φ _ hpd, codOf_refK]; rfl
  have hmem : fixClo (KB "K" outK dm D φ) ρ φ (emptyState 0) [⟨"r"⟩] [.ref .nat] (.ref .nat) none bodyK
      ∈ₛ[dm.read] piTyAt dm.read 1 psW outK := by
    unfold fixClo
    rw [hty, hsort, runDoms_ref _ ρ φ _ hpd, codOf_refK]
    exact closure_mem_K (K := KB "K" outK dm D φ) _ h1 (by simp [h2]) _ (flagsU_K hDK).1 (flagsU_K hDK).2
  refine ⟨_, ?_, hmem⟩
  unfold fixK
  rw [run_fix_of_mem tl hint' ⟨"K"⟩ [⟨"r"⟩] [.ref .nat] (.ref .nat) none bodyK (emptyState 0) hfl
    (by rw [← fixK, capOrder_fixK]; trivial) (by rw [hty]; exact hmem), hty]
  rfl

end

/-- **The column `K` at the checker's own decisions**: for every successful typed run of the checker's `eval` on `K`'s
body from a state with `stK`'s kernel (`checkFix`'s body state), under the fuel-free table at the run's end, the
reference's `.fix` clause forms `K`'s closure from the empty state, a member of `Π(r : &Nat). &Nat`; for every data
model, assignment, future, tail flag and hint. Assumes NO fact about the checker or the model. -/
theorem column_K_ff (dm : DataModel) (ρ : Assignment) (φ : Future)
    {n : Nat} {hc : Option Value} {st st' : MState} {bh : Nat} {v : Value} {T? : Option Value}
    (hk : Kern stK st) (h : Runs (Ochr.eval n true bodyK hc) st bh (v, T?) st') (tl : Bool) (hint : TyS) :
    ∃ f, runT (KB "K" outK dm (checkerDecisionsFF st') φ) ρ φ tl hint fixK (emptyState 0)
        = some ((f, .plain (piTyAt dm.read 1 psW outK)), emptyState 0) ∧ f ∈ₛ[dm.read] piTyAt dm.read 1 psW outK := by
  have hD : DecTab (checkerDecisionsFF st') st' :=
    decTab_ff st' _ (fun _ => Machine.decide_fuel_agree' _) (Machine.decide_fuel_agree' st')
  have hDK : DecTab (checkerDecisionsFF st') stK :=
    DecTab.of_kern hk.symm (Machine.decBack _ st st' hD (grows_eval _ _ _ _ st bh _ st' h))
  exact column_K_run ρ hDK tl hint

end Ochr.Meaning.Steps.Form.ColumnW
