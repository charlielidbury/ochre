import Ochr.Meaning.Steps.CallJ2Fn

/-!
# `J2`'s call `I(x)`: the reference's run, and the value agreement in both branches of the call's inversion (lead18, 2026-11-21; docs/31 D139)

At `J2`'s one table (aligned with the checker at `J2`'s start, `stJ2`), in `J2`'s context (`ColumnJ.KJ` with `I` meaning
`J2`'s own closure `GlobalsLocal.fJ`):
- `runT_callJ2_J2`: from every reference state related to the caller `stX1` (`x ↦ S(Z)`), the strict run of `I(x)`
  returns `2 : Nat` and leaves `x` moved (`moveX`); no assumed fact.
- `mean_callJ2`: the checker's value `v` of the call means `2` in either branch of `CallJ2Inv` (restated by the ruling
  for lead18 as a disjunction): the body's untyped value is the numeral `S(S(Z))` (`BodyLazyInv`, at the read's copy
  decision `copyDec_calleeJ2`), or the call closed off to `⌈I(S(Z))⌉`, which means `callOf` of the context's `I` at `1`
  (`mean_sealJ2`), `2` again by `callOf_fJ_J2`. Assumes `CallJ2Inv`, `BodyLazyInv` (checker); no model fact.
What is left of the step in the form (`Out`): `Pre` and `Rel` at `stX`'s kernel with the value in flight, in each branch.
-/

namespace Ochr.Meaning.Steps.Form.CallJ2

open Ochr Ochr.Meaning Ochr.Meaning.Steps Ochr.Meaning.Steps.Form Ochr.Meaning.Strict.Witness
open Ochr.Meaning.Steps.Form.ColumnI (piNat gI psI outI fixI selfTy selfSem)
open Ochr.Meaning.Steps.Form.ColumnJ (KJ)

namespace Aux
open Ochr.Meaning.Regress.GenNeutralContent (isOk outVal)

abbrev sealTJ2 : Term := .call (.val (.gfn "I")) [.val (.succ .zero)] true
abbrev pdX : M DeclInfo := withLive true (Ochr.placeDecl 100 [] (.var 0))

theorem ok_fl_seal : isOk (flagsRun sealTJ2) (scopeState FrameJ2.Guards.stJ2 []) 1000 = true := by decide +kernel
theorem val_fl_seal : outVal (flagsRun sealTJ2) (scopeState FrameJ2.Guards.stJ2 []) 1000 = (false, false) := by decide +kernel
theorem ok_fl_call : isOk (flagsRun callJ2) (scopeState FrameJ2.Guards.stJ2 [.other]) 1000 = true := by decide +kernel
theorem val_fl_call : outVal (flagsRun callJ2) (scopeState FrameJ2.Guards.stJ2 [.other]) 1000 = (false, false) := by decide +kernel
theorem ok_fl_x1 : isOk (flagsRun (.place (.var 0))) (scopeState FrameJ2.Guards.stJ2 [.other]) 1000 = true := by decide +kernel
theorem val_fl_x1 : outVal (flagsRun (.place (.var 0))) (scopeState FrameJ2.Guards.stJ2 [.other]) 1000 = (false, false) := by
  decide +kernel
theorem ok_pd_x1 : isOk pdX (scopeState FrameJ2.Guards.stJ2 [.other]) 1000 = true := by decide +kernel
theorem val_pd_x1 : isOther (outVal pdX (scopeState FrameJ2.Guards.stJ2 [.other]) 1000) = true := by decide +kernel

end Aux

section
variable {dm : DataModel} {D : Decisions}

/-- **The decisions the caller's run of `I(x)` and the sealed call read, at `J2`'s table.** -/
theorem callDecJ2 (hd : DecTab D FrameJ2.Guards.stJ2) :
    D.flags [.other] callJ2 = (false, false) ∧ D.flags [.other] (.place (.var 0)) = (false, false) ∧
      D.copy (D.placeDecl [.other] (.var 0)) = false ∧ D.flags [] Aux.sealTJ2 = (false, false) := by
  open Ochr.Meaning.Regress.GenNeutralContent in
  have hcp : D.copy .other = false := by
    rw [hd.copy 100 .other _ 1000 _ (runs_out (Ochr.declCopy 100 .other) _ 1000 Aux.ok_cp), Aux.val_cp]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hd.flags 100 _ _ _ 1000 _ (runs_out (Aux.flagsRun callJ2) _ 1000 Aux.ok_fl_call), Aux.val_fl_call]
  · rw [hd.flags 100 _ _ _ 1000 _ (runs_out (Aux.flagsRun (.place (.var 0))) _ 1000 Aux.ok_fl_x1), Aux.val_fl_x1]
  · rw [(hd.placeDecl 100 [.other] (.var 0) _ 1000 _ (runs_out Aux.pdX _ 1000 Aux.ok_pd_x1)).trans
      (ColumnC.Aux.isOther_eq Aux.val_pd_x1)]
    exact hcp
  · rw [hd.flags 100 _ _ _ 1000 _ (runs_out (Aux.flagsRun Aux.sealTJ2) _ 1000 Aux.ok_fl_seal), Aux.val_fl_seal]

/-- **The reference's run of `J2`'s call**, from every reference state related to the caller `stX1`: `2 : Nat`, `x`
moved. No assumed fact. -/
theorem runT_callJ2_J2 (hd : DecTab D FrameJ2.Guards.stJ2) {ρ : Assignment} {φ : Future} {π : Nat → Nat} {s : SState}
    (hr : Rel (KJ dm D (GlobalsLocal.fJ dm D)) ρ φ π stX1 s) (tl : Bool) (h : TyS) :
    runT (KJ dm D (GlobalsLocal.fJ dm D)) ρ φ tl h callJ2 s =
      some ((.el0 Nat 2, .plain TyM.nat), moveX (KJ dm D (GlobalsLocal.fJ dm D)) s) := by
  obtain ⟨hlive, hsh, hsc, hres, hval, hty, -⟩ := caller_of_rel hr
  obtain ⟨hfl, hfa, hcp, -⟩ := callDecJ2 hd
  rw [runT_callJ2 tl h hlive hsh hsc hres hval hty hfl hfa hcp]
  exact callOf_fJ_J2 hd 1 _

/-- **What the sealed call `⌈I(S(Z))⌉` means in `J2`'s context**: `callOf` of `J2`'s closure of `I` at `1`, `2`. -/
theorem mean_sealJ2 (hd : DecTab D FrameJ2.Guards.stJ2) (ρ : Assignment) (φ : Future) (Δ : Nat → TyS) (hint : TyS) :
    meanV { KJ dm D (GlobalsLocal.fJ dm D) with Δ := Δ } ρ φ hint sealJ2 = .el0 Nat 2 := by
  have hfl := (callDecJ2 (D := D) hd).2.2.2
  have h1 : runT { KJ dm D (GlobalsLocal.fJ dm D) with Δ := Δ } ρ φ false (TyS.plain TyM.err) (Term.val (.gfn "I"))
      (emptyState 0) = some ((GlobalsLocal.fJ dm D, .plain (piTyAt dm.read 1 psI outI)), emptyState 0) := by
    rw [runT]; rfl
  have h2 : ∀ T, runArgs { KJ dm D (GlobalsLocal.fJ dm D) with Δ := Δ } ρ φ false T [] [Term.val (.succ .zero)]
      (emptyState 0) = some ([((Sem.el0 Nat 0).succ, .plain TyM.nat)], emptyState 0) := by
    intro T
    rw [runArgs]
    simp only [Bool.false_and, SM.stmtIf, Bool.false_eq_true, if_false, Bind.bind]
    rw [runT]; rfl
  show (match runT _ ρ φ false hint Aux.sealTJ2 (emptyState 0) with
    | some ((v, _), _) => v
    | none => .err) = _
  have hr : runT { KJ dm D (GlobalsLocal.fJ dm D) with Δ := Δ } ρ φ false hint Aux.sealTJ2 (emptyState 0) =
      some ((.el0 Nat 2, .plain TyM.nat), emptyState 0) := by
    rw [runT]
    simp only [show (KJ dm D (GlobalsLocal.fJ dm D)).D.flags (scopeOf (emptyState 0))
      (.call (.val (.gfn "I")) [.val (.succ .zero)] true) = (false, false) from hfl]
    simp only [SM.erasedIf, SM.stmtIf, Bool.false_eq_true, if_false]
    simp only [SM.headOf, Bind.bind, h1]
    rw [h2]
    dsimp only
    rw [if_pos (ColumnJ.borrowArgsTyped_unlabelled _ _ _ _ (fun a ha => by simp at ha; subst ha; rfl)), Sem.succ_el0]
    exact callOf_fJ_J2 (dm := dm) hd 1 _
  rw [hr]

/-- **The checker's value of `J2`'s call means `2`**, in either branch of `CallJ2Inv`, at every assignment, future and
`Δ` of `J2`'s context: the reference's result (`runT_callJ2_J2`). Assumes `CallJ2Inv`, `BodyLazyInv` (checker). -/
theorem mean_callJ2 (hC : CallJ2Inv) (hB : CallBody.BodyLazyInv) (hd : DecTab D FrameJ2.Guards.stJ2) {n : Nat} {hint : Option Value}
    {st st' : MState} {bh : Nat} {v : Value} {T? : Option Value} (hk : Kern stX1 st) (hm : Mode st)
    (htn : st.tailNext = false) (htd : st.tailDecl = none) (hpd : st.privateDepth = 0)
    (h : Runs (Ochr.eval n true callJ2 hint) st bh (v, T?) st') :
    T? = some .tNat ∧ Kern stX st' ∧ ∀ (ρ : Assignment) (φ : Future) (Δ : Nat → TyS) (h' : TyS),
      meanV { KJ dm D (GlobalsLocal.fJ dm D) with Δ := Δ } ρ φ h' v = .el0 Nat 2 := by
  obtain ⟨hT, hkx, hbr⟩ := hC n hint st st' bh v T? hk hm htn htd hpd h
  refine ⟨hT, hkx, fun ρ φ Δ h' => ?_⟩
  rcases hbr with ⟨m, stc, stc', bh', T₀, hkc, hmc, htdc, hrun⟩ | rfl
  · have hpos : ckVarPos stc.env 0 = some (.bind 1 1) := by
      rw [← ckVarPos_erase, ← hkc.env, ckVarPos_erase]; rfl
    obtain ⟨fr, hfr, hb⟩ : ∃ fr : Frame, stc.env[1]? = some fr ∧ fr.binds[1]? = some (nLazy (.succ .zero)) := by
      have e := congrArg (fun E : Env => E[1]?) hkc.env
      simp only [Env.erase, Array.getElem?_map] at e
      rcases hsa : stc.env[1]? with _ | fr
      · rw [hsa] at e; simp [stCJ2] at e
      · rw [hsa] at e
        have e' : Frame.erase { binds := #[selfU, nLazy (.succ .zero)] } = fr.erase := Option.some.inj e
        have eb := congrArg (fun F : Frame => F.binds[1]?) e'
        simp only [Frame.erase] at eb
        exact ⟨fr, rfl, by rw [← eb]; rfl⟩
    have hb' : stc.env[1]?.bind (fun fr : Frame => fr.binds[1]?) = some (nLazy (.succ .zero)) := by rw [hfr]; exact hb
    obtain ⟨rfl, -⟩ := hB m none stc stc' bh' v T₀ 1 1 _ D hmc htdc hpos hb' (.succ .zero) rfl
      (copyDec_calleeJ2 hd hkc) hrun
    show ((Sem.el0 Nat 0).succ).succ = Sem.el0 Nat 2
    rw [Sem.succ_el0, Sem.succ_el0]
  · exact mean_sealJ2 hd ρ φ Δ h'

end

end Ochr.Meaning.Steps.Form.CallJ2
