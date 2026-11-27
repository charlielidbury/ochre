import Ochr.Meaning.Steps.BorrowParStep
import Ochr.Meaning.Steps.ColumnIRun

/-!
# The columns `W` and `K` at the checker's decisions (lead19, 2026-11-21; docs/31 D142)

The decisions the reference's `.fix` clause and the bodies read, at every table aligned with the checker at `stW`
(`stK`), by kernel evaluation of the checker's decision procedures (`fixDecW`, `fixDecK`). With them:

* `column_W_run`: the reference's `.fix` run of `W` from the empty state succeeds at `Π(r : &Nat). Nat` and the
  closure is a member of it. No assumed fact of either kind: the body's run is computed (`BorrowParRun`).
* `column_W_ff`: the same at the checker's fuel-free table at the end of any successful typed run of `W`'s body from
  `stW`'s kernel. No assumed fact (`DecBack` and the tables' growth are the machine lane's proofs).
-/

namespace Ochr.Meaning.Steps.Form.ColumnW

open Ochr Ochr.Meaning Ochr.Meaning.Steps Ochr.Meaning.Steps.Form Ochr.Meaning.Strict.Witness

namespace Aux

open Ochr.Meaning.Regress.GenNeutralContent (isOk outVal)

abbrev flagsRun (t : Term) : M (Bool × Bool) := Ochr.Meaning.Steps.Form.ColumnC.Aux.flagsRun t
abbrev typeDeclRun (T : Term) : M DeclInfo := withLive true (Ochr.typeDecl 100 false [] [] T)
abbrev piSortRun (t : Term) : M Nat := withLive true (Ochr.sortOf 100 (.tPi [] t []))
abbrev pdR : M DeclInfo := withLive true (Ochr.placeDecl 100 [] (.var 0))
abbrev cpRun : M Bool := Ochr.declCopy 100 (.ref .other)

def isRefOther : DeclInfo → Bool
  | .ref .other => true
  | _ => false

theorem isRefOther_eq {d : DeclInfo} (h : isRefOther d = true) : d = .ref .other := by
  cases d <;> simp [isRefOther] at h ⊢
  rename_i A
  cases A <;> simp [isRefOther] at h ⊢

/-- `W`'s and `K`'s top-frame readings in the body: `self` (`.pi cod`), then `r` (`.ref .other`), innermost first. -/
def RW : List DeclInfo := [.ref .other, .pi .other]
def RK : List DeclInfo := [.ref .other, .pi (.ref .other)]

theorem ok_fl_bodyW : isOk (flagsRun bodyW) (scopeState stW RW) 1000 = true := by decide +kernel
theorem val_fl_bodyW : outVal (flagsRun bodyW) (scopeState stW RW) 1000 = (false, false) := by decide +kernel
theorem ok_td_ref : isOk (typeDeclRun (.ref .nat)) (scopeState stW []) 1000 = true := by decide +kernel
theorem val_td_ref : isRefOther (outVal (typeDeclRun (.ref .nat)) (scopeState stW []) 1000) = true := by decide +kernel
theorem ok_td_nat : isOk (typeDeclRun .nat) (scopeState stW [.ref .other]) 1000 = true := by decide +kernel
theorem val_td_nat : ColumnC.Aux.isOther (outVal (typeDeclRun .nat) (scopeState stW [.ref .other]) 1000) = true := by
  decide +kernel
theorem ok_ps_W : isOk (piSortRun (.pi [⟨"r"⟩] [.ref .nat] .nat)) (scopeState stW []) 1000 = true := by decide +kernel
theorem val_ps_W : outVal (piSortRun (.pi [⟨"r"⟩] [.ref .nat] .nat)) (scopeState stW []) 1000 = 1 := by decide +kernel
theorem ok_fl_fixW : isOk (flagsRun fixW) (scopeState stW []) 1000 = true := by decide +kernel
theorem val_fl_fixW : outVal (flagsRun fixW) (scopeState stW []) 1000 = (false, false) := by decide +kernel

theorem ok_fl_bodyK : isOk (flagsRun bodyK) (scopeState stK RK) 1000 = true := by decide +kernel
theorem val_fl_bodyK : outVal (flagsRun bodyK) (scopeState stK RK) 1000 = (false, false) := by decide +kernel
theorem ok_pd_K : isOk pdR (scopeState stK RK) 1000 = true := by decide +kernel
theorem val_pd_K : isRefOther (outVal pdR (scopeState stK RK) 1000) = true := by decide +kernel
theorem ok_cp_K : isOk cpRun stK 1000 = true := by decide +kernel
theorem val_cp_K : outVal cpRun stK 1000 = false := by decide +kernel
theorem ok_tdK_ref : isOk (typeDeclRun (.ref .nat)) (scopeState stK []) 1000 = true := by decide +kernel
theorem val_tdK_ref : isRefOther (outVal (typeDeclRun (.ref .nat)) (scopeState stK []) 1000) = true := by decide +kernel
theorem ok_tdK_cod : isOk (typeDeclRun (.ref .nat)) (scopeState stK [.ref .other]) 1000 = true := by decide +kernel
theorem val_tdK_cod : isRefOther (outVal (typeDeclRun (.ref .nat)) (scopeState stK [.ref .other]) 1000) = true := by
  decide +kernel
theorem ok_ps_K : isOk (piSortRun (.pi [⟨"r"⟩] [.ref .nat] (.ref .nat))) (scopeState stK []) 1000 = true := by
  decide +kernel
theorem val_ps_K : outVal (piSortRun (.pi [⟨"r"⟩] [.ref .nat] (.ref .nat))) (scopeState stK []) 1000 = 1 := by
  decide +kernel
theorem ok_fl_fixK : isOk (flagsRun fixK) (scopeState stK []) 1000 = true := by decide +kernel
theorem val_fl_fixK : outVal (flagsRun fixK) (scopeState stK []) 1000 = (false, false) := by decide +kernel

end Aux

open Ochr.Meaning.Regress.GenNeutralContent (runs_out)

/-- **The decisions `W`'s `.fix` clause and body read**, at every table aligned with the checker at `stW`: the parameter
reads `.ref .other`, the codomain `.other` (after the parameter), the Π-type has sort `1`, and neither the `fix` nor the
body is a statement or a proof. -/
theorem fixDecW {D : Decisions} (hd : DecTab D stW) :
    D.typeDecl [] (.ref .nat) = .ref .other ∧ D.typeDecl [.ref .other] .nat = .other ∧
      D.piSort [] (.pi [⟨"r"⟩] [.ref .nat] .nat) = 1 ∧ D.flags [] fixW = (false, false) ∧
      D.flags Aux.RW bodyW = (false, false) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact (hd.typeDecl 100 [] _ _ 1000 _ (runs_out (Aux.typeDeclRun (.ref .nat)) _ 1000 Aux.ok_td_ref)).trans
      (Aux.isRefOther_eq Aux.val_td_ref)
  · exact (hd.typeDecl 100 [.ref .other] _ _ 1000 _ (runs_out (Aux.typeDeclRun .nat) _ 1000 Aux.ok_td_nat)).trans
      (ColumnC.Aux.isOther_eq Aux.val_td_nat)
  · rw [hd.piSort 100 [] _ _ 1000 _ (runs_out (Aux.piSortRun _) _ 1000 Aux.ok_ps_W), Aux.val_ps_W]
  · rw [hd.flags 100 [] fixW _ 1000 _ (runs_out (Aux.flagsRun fixW) _ 1000 Aux.ok_fl_fixW), Aux.val_fl_fixW]
  · rw [hd.flags 100 Aux.RW bodyW _ 1000 _ (runs_out (Aux.flagsRun bodyW) _ 1000 Aux.ok_fl_bodyW), Aux.val_fl_bodyW]

/-- **The decisions `K`'s `.fix` clause and body read**, at every table aligned with the checker at `stK`: as `W`'s,
the codomain `&Nat` read `.ref .other`, and `r` (read `.ref .other`) is not copied. -/
theorem fixDecK {D : Decisions} (hd : DecTab D stK) :
    D.typeDecl [] (.ref .nat) = .ref .other ∧ D.typeDecl [.ref .other] (.ref .nat) = .ref .other ∧
      D.piSort [] (.pi [⟨"r"⟩] [.ref .nat] (.ref .nat)) = 1 ∧ D.flags [] fixK = (false, false) ∧
      D.flags Aux.RK bodyK = (false, false) ∧ D.copy (D.placeDecl Aux.RK (.var 0)) = false := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact (hd.typeDecl 100 [] _ _ 1000 _ (runs_out (Aux.typeDeclRun (.ref .nat)) _ 1000 Aux.ok_tdK_ref)).trans
      (Aux.isRefOther_eq Aux.val_tdK_ref)
  · exact (hd.typeDecl 100 [.ref .other] _ _ 1000 _ (runs_out (Aux.typeDeclRun (.ref .nat)) _ 1000 Aux.ok_tdK_cod)).trans
      (Aux.isRefOther_eq Aux.val_tdK_cod)
  · rw [hd.piSort 100 [] _ _ 1000 _ (runs_out (Aux.piSortRun _) _ 1000 Aux.ok_ps_K), Aux.val_ps_K]
  · rw [hd.flags 100 [] fixK _ 1000 _ (runs_out (Aux.flagsRun fixK) _ 1000 Aux.ok_fl_fixK), Aux.val_fl_fixK]
  · rw [hd.flags 100 Aux.RK bodyK _ 1000 _ (runs_out (Aux.flagsRun bodyK) _ 1000 Aux.ok_fl_bodyK), Aux.val_fl_bodyK]
  · rw [(hd.placeDecl 100 Aux.RK (.var 0) _ 1000 _ (runs_out Aux.pdR _ 1000 Aux.ok_pd_K)).trans
      (Aux.isRefOther_eq Aux.val_pd_K)]
    rw [hd.copy 100 (.ref .other) _ 1000 _ (runs_out Aux.cpRun _ 1000 Aux.ok_cp_K), Aux.val_cp_K]

/-! ## `W`'s closure, formed by the reference's `.fix` clause -/

section
variable (K : RunCtx) (ρ : Assignment) (φ : Future)

theorem bindsOf_ref (s : SState) (hd : K.D.paramDecls (scopeOf s) [.ref .nat] = [.ref .other]) :
    bindsOf K ρ φ s [.ref .nat] = [(fun _ => .plain TyM.nat, .ref .other)] := by
  unfold bindsOf; rw [hd]
  simp only [runBinds, mkBind, ColumnI.runT_nat]
  rfl

theorem runDoms_ref (s : SState) (hd : K.D.paramDecls (scopeOf s) [.ref .nat] = [.ref .other]) :
    runDoms K ρ φ s [.ref .nat] = psW := by
  unfold runDoms; rw [bindsOf_ref K ρ φ s hd]; rfl

theorem codOf_natW (s : SState) (bs : List PBind) (rs : List Bool) : codOf K ρ φ s bs rs .nat = outW := by
  unfold codOf; simp only [ColumnI.runT_nat]; rfl

theorem codOf_refK (s : SState) (bs : List PBind) (rs : List Bool) : codOf K ρ φ s bs rs (.ref .nat) = outK := by
  unfold codOf; simp only [ColumnI.runT_nat]; rfl

end

theorem capOrder_fixW : capOrder fixW = [] := rfl
theorem capOrder_fixK : capOrder fixK = [] := rfl

section
variable {dm : DataModel} {D : Decisions} {φ : Future}

/-- **`W`'s closure, as the reference's `.fix` clause forms it from the empty state**: the run succeeds at
`Π(r : &Nat). Nat` (`piTyAt _ 1 psW outW`), leaves the state as it was, and the closure is a member of that type. At
every table aligned with the checker at `stW`, every assignment, future, tail flag and hint. No assumed fact. -/
theorem column_W_run (ρ : Assignment) (hDW : DecTab D stW) (tl : Bool) (hint' : TyS) :
    ∃ f, runT (KB "W" outW dm D φ) ρ φ tl hint' fixW (emptyState 0)
        = some ((f, .plain (piTyAt dm.read 1 psW outW)), emptyState 0) ∧ f ∈ₛ[dm.read] piTyAt dm.read 1 psW outW := by
  obtain ⟨hd1, hd2, hps, hfl, hflb⟩ := fixDecW hDW
  have hpd : (KB "W" outW dm D φ).D.paramDecls (scopeOf (emptyState 0)) [.ref .nat] = [.ref .other] := by
    show D.paramDecls [] [.ref .nat] = [.ref .other]
    simp [Decisions.paramDecls, Decisions.teleDecls, hd1]
  have hsort : fixSort (KB "W" outW dm D φ) (emptyState 0) [⟨"r"⟩] [.ref .nat] .nat = 1 := hps
  have h1 := bindsOf_ref (KB "W" outW dm D φ) ρ φ _ hpd
  have h2 : (KB "W" outW dm D φ).D.typeDecl ((KB "W" outW dm D φ).D.teleDecls (scopeOf (emptyState 0)) [.ref .nat]) .nat
      = .other := by
    show D.typeDecl (D.teleDecls [] [.ref .nat]) .nat = .other
    simp [Decisions.teleDecls, hd1, hd2]
  have hty : fixTy (KB "W" outW dm D φ) ρ φ (emptyState 0) [⟨"r"⟩] [.ref .nat] .nat = piTyAt dm.read 1 psW outW := by
    unfold fixTy; rw [hsort, runDoms_ref _ ρ φ _ hpd, codOf_natW]; rfl
  have hmem : fixClo (KB "W" outW dm D φ) ρ φ (emptyState 0) [⟨"r"⟩] [.ref .nat] .nat none bodyW
      ∈ₛ[dm.read] piTyAt dm.read 1 psW outW := by
    unfold fixClo
    rw [hty, hsort, runDoms_ref _ ρ φ _ hpd, codOf_natW]
    exact closure_mem_W (K := KB "W" outW dm D φ) _ h1 _ (by rw [h2]; exact hflb)
  refine ⟨_, ?_, hmem⟩
  unfold fixW
  rw [run_fix_of_mem tl hint' ⟨"W"⟩ [⟨"r"⟩] [.ref .nat] .nat none bodyW (emptyState 0) hfl
    (by rw [← fixW, capOrder_fixW]; trivial) (by rw [hty]; exact hmem), hty]
  rfl

end

/-- **The column `W` at the checker's own decisions**: for every successful typed run of the checker's `eval` on `W`'s
body from a state with `stW`'s kernel (`checkFix`'s body state), under the fuel-free table at the run's end, the
reference's `.fix` clause forms `W`'s closure from the empty state, a member of `Π(r : &Nat). Nat`; for every data
model, assignment, future, tail flag and hint. Assumes NO fact about the checker or the model (`DecBack` and the
tables' growth are the machine lane's proofs). -/
theorem column_W_ff (dm : DataModel) (ρ : Assignment) (φ : Future)
    {n : Nat} {hc : Option Value} {st st' : MState} {bh : Nat} {v : Value} {T? : Option Value}
    (hk : Kern stW st) (h : Runs (Ochr.eval n true bodyW hc) st bh (v, T?) st') (tl : Bool) (hint : TyS) :
    ∃ f, runT (KB "W" outW dm (checkerDecisionsFF st') φ) ρ φ tl hint fixW (emptyState 0)
        = some ((f, .plain (piTyAt dm.read 1 psW outW)), emptyState 0) ∧ f ∈ₛ[dm.read] piTyAt dm.read 1 psW outW := by
  have hD : DecTab (checkerDecisionsFF st') st' :=
    decTab_ff st' _ (fun _ => Machine.decide_fuel_agree' _) (Machine.decide_fuel_agree' st')
  have hDW : DecTab (checkerDecisionsFF st') stW :=
    DecTab.of_kern hk.symm (Machine.decBack _ st st' hD (grows_eval _ _ _ _ st bh _ st' h))
  exact column_W_run ρ hDW tl hint

end Ochr.Meaning.Steps.Form.ColumnW
