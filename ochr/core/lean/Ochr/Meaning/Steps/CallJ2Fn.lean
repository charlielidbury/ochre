import Ochr.Meaning.Steps.CallJ2
import Ochr.Meaning.Steps.ColumnRSplit
import Ochr.Meaning.Steps.GlobalsLocal

/-!
# `J2`'s own closure of `I`, at `J2`'s one table (lead17, 2026-11-21; docs/31 D136)

Items (4) and (5) of the sixteenth lead's list for `J2` (docs/31 D132): `I`'s meaning in `J2`'s context is the closure
the `.fix` clause forms under `J2`'s context and table (`GlobalsOk.fn`, `GlobalsLocal.fJ`), and at `J2`'s table, aligned
with the checker at `J2`'s start, its body's run is computed at every number with NO fact assumed: the decisions it reads
are `parDecJ2`, `flags_bodyI_J2`, `copyDec_calleeJ2`'s (kernel evaluation at `stJ2`). Hence `fJ` is a member of
`Π(n : Nat). Nat` at `J2`'s table (`fJ_mem_J2`; D130's `fJ_mem` was at `I`'s table, with column `I`'s checker facts), and
called at `a` it gives `a + 1` (`callOf_fJ_J2`). The closure's body runs from `closureJ2 a`, the state `closureRun_J2`
relates to the checker's untyped run (`fixBodyAt_J2`).
-/

namespace Ochr.Meaning.Steps.Form.CallJ2

open Ochr Ochr.Meaning Ochr.Meaning.Steps Ochr.Meaning.Steps.Form Ochr.Meaning.Strict.Witness
open Ochr.Meaning.Steps.Form.ColumnI (piNat gI psI outI fixI selfTy selfSem)
open Ochr.Meaning.Steps.Form.ColumnP (RefJ RefP dropN)
open Ochr.Meaning.Steps.Form.FrameJ2 (closureJ2 nBind closureJ2_env closureJ2_shape closureJ2_lent)

section
variable {K : RunCtx} {ρ ρ₀ : Assignment} {φ : Future} {g : Sem} {s : SState}

/-- **`I`'s body `S(#0)` from a state reading like `I`'s frame** (`ColumnP.RefP`: `n` at `(1, 1)` holding the number
`a`), at a table deciding the body and the read as neither a statement nor a proof and `n` moved: `a + 1` at `Nat`, `n`
moved. -/
theorem runT_bodyI_ref (hfl : K.D.flags [.other, .pi .other] bodyI = (false, false))
    (hfx : K.D.flags [.other, .pi .other] (.place (.var 0)) = (false, false))
    (hcp : K.D.copy (K.D.placeDecl [.other, .pi .other] (.var 0)) = false) (h : RefP ρ₀ φ g s) {a : Nat}
    (h0 : ρ₀ 0 = .el0 Nat a) (tl : Bool) (hint : TyS) :
    runT K ρ φ tl hint bodyI s = some ((.el0 Nat (a + 1), .plain TyM.nat), dropN K s) := by
  have hfl' : K.D.flags (scopeOf s) (.succ (.place (.var 0))) = (false, false) := by rw [h.scope]; exact hfl
  have hfx' : K.D.flags (scopeOf s) (.place (.var 0)) = (false, false) := by rw [h.scope]; exact hfx
  have hcp' : K.D.copy (K.D.placeDecl (scopeOf s) (.var 0)) = false := by rw [h.scope]; exact hcp
  have hco : contentOf K φ (.var 0) s = some ((.el0 Nat a, s.tyAt (.bind 1 1), .bind 1 1, []), s) := by
    unfold contentOf; rw [h.resolve0]; dsimp only
    rw [h.access, h.typedFuture, h.valN, h0]; simp [Sem.follow]
  have hset : setContent K φ (.bind 1 1) [] .moved s = some (⟨⟩, dropN K s) := by
    unfold setContent; rw [if_pos (fun _ _ => by rw [Sem.updAt.eq_def]; rfl)]; rfl
  have hwhole : (Sem.el0 Nat a).whole := by simp [Sem.whole]
  have hrg : ReadGood K.dm.read (s.tyAt (.bind 1 1)).m (.el0 Nat a) := .inl (by rw [h.tyN]; exact ⟨a, rfl⟩)
  have hrd : runT K ρ φ false (.plain TyM.err) (.place (.var 0)) s =
      some ((.el0 Nat a, { s.tyAt (.bind 1 1) with label := none }), dropN K s) := by
    rw [runT]
    show SM.erasedIf (K.D.flags (scopeOf s) (.place (.var 0)))
      (SM.guarded (ContentOk K φ (.var 0)) (readPlace K φ (.var 0) (K.D.copy (K.D.placeDecl (scopeOf s) (.var 0))))) s = _
    rw [hfx', hcp']
    simp only [SM.erasedIf, SM.stmtIf, Bool.false_eq_true, if_false]
    rw [SM.guarded_of (by unfold ContentOk; rw [h.resolve0]; exact h.accessOk K φ _ _)]
    unfold readPlace; rw [hco]
    simp only [bind, Option.bind, hwhole, hrg, not_true_eq_false, if_false, Bool.false_eq_true, List.isEmpty_nil,
      h.shape, hset]
    rfl
  unfold bodyI
  rw [runT_succ _ _ _ s hfl']
  unfold SM.strictS
  have hb : (runT K ρ φ false (.plain TyM.err) (.place (.var 0)) >>= fun x : Res => match x with
      | (v, _) => (pure (v.succ, TyS.plain TyM.nat) : SM Res)) s = some (((Sem.el0 Nat a).succ, .plain TyM.nat), dropN K s) := by
    simp only [Bind.bind]; rw [hrd]; rfl
  rw [hb]
  have hsu : (Sem.el0 Nat a).succ = .el0 Nat (a + 1) := by rw [Sem.succ, Sem.asNat_el0]
  have hc : (Sem.el0 Nat a).succ ∈ₛ[K.dm.read] (TyS.plain TyM.nat).m := by rw [hsu]; exact ⟨a + 1, rfl⟩
  dsimp only; rw [if_pos hc, hsu]

end

/-- **The closure's state reads like `I`'s frame** (`ColumnP.RefP` at `σ0 ↦ a`). -/
theorem refP_closureJ2 (R : DataRead) (φ : Future) (a : Nat) :
    RefP (fun _ => .el0 Nat a) φ (selfSem R φ) (closureJ2 R φ a) := by
  have he := closureJ2_env R φ a
  have hlive : (closureJ2 R φ a).liveLabels = [] := by
    unfold SState.liveLabels
    rw [List.filterMap_eq_nil_iff.mpr (fun p _ => closureJ2_shape R φ a p), List.mergeSort_nil]
  refine ⟨⟨hlive, closureJ2_shape R φ a, ?_, ?_⟩, ⟨_, by rw [he]; rfl, rfl⟩, ?_, ?_, ?_, ?_⟩
  · unfold scopeOf; rw [he]; rfl
  · unfold resolve; simp [SState.varPos, he, SState.topIdx, Place.steps]
  · unfold SState.topIdx; rw [he]; rfl
  · simp [SState.valAt, he, nBind]
  · simp [SState.valAt, he]
  · simp [SState.tyAt, he, nBind]; rfl

section
variable {dm : DataModel} {D : Decisions} {ρ : Assignment} {φ : Future}

/-- **`I`'s body inside `J2`'s closure of `I`, at every number**: `fixBodyAt` (stage 1, `self` the stage-0 closure)
starts from `closureJ2 a` and returns `a + 1` and no final, at a table aligned with the checker at `J2`'s start. No
fact assumed. -/
theorem fixBodyAt_J2 (hd : DecTab D FrameJ2.Guards.stJ2) (K : RunCtx) (hKD : K.D = D) (fb : List PBind × PBind)
    (h1 : fb.1 = [(fun _ => .plain TyM.nat, .other)]) (h2 : fb.2.2 = .other) (a : Nat) :
    fixBodyAt K ρ φ fb (emptyState 0) psI outI (selfTy K.dm.read) 0 bodyI (selfSem K.dm.read φ) [.el0 Nat a]
      = some ⟨.el0 Nat (a + 1), [], none⟩ := by
  have hpd := parDecJ2 hd
  have hfl := flags_bodyI_J2 hd
  have hcp : D.copy (D.placeDecl [.other, .pi .other] (.var 0)) = false := by
    have e2 : D.placeDecl Aux.RI (.var 0) = .other := by
      rw [hd.placeDecl 100 Aux.RI (.var 0) _ 1000 _ (Regress.GenNeutralContent.runs_out Aux.pdRun _ 1000 Aux.ok_pd)]
      exact ColumnC.Aux.isOther_eq Aux.val_pd
    have e3 : D.copy .other = false := by
      rw [hd.copy 100 .other _ 1000 _ (Regress.GenNeutralContent.runs_out (Ochr.declCopy 100 .other) _ 1000 Aux.ok_cp),
        Aux.val_cp]
    show D.copy (D.placeDecl Aux.RI (.var 0)) = false
    rw [e2, e3]
  have hst : ([Sem.el0 Nat a].zip psI).foldl (fixStep fb)
      ((emptyState 0).under.pushBind { ty := .plain (selfTy K.dm.read), val := fun _ => selfSem K.dm.read φ, decl := .pi fb.2.2 }, [], []) = (closureJ2 K.dm.read φ a, [.el0 Nat a], []) := by
    simp only [psI, List.zip_cons_cons, List.zip_nil_right, List.foldl_cons, List.foldl_nil, fixStep, h1, h2,
      Bool.false_eq_true, if_false, List.length_nil, List.getElem?_cons_zero, List.nil_append]
    rfl
  have hrun := runT_bodyI_ref (K := K) (ρ := ρ) (hKD ▸ hfl) (hKD ▸ hpd.1) (hKD ▸ hcp) (refP_closureJ2 K.dm.read φ a)
    rfl true (fb.2.1 [.el0 Nat a])
  have hl : (dropN K (closureJ2 K.dm.read φ a)).liveLabels = [] := by
    unfold dropN; rw [Strict.liveLabels_setAt]; unfold SState.liveLabels
    rw [List.filterMap_eq_nil_iff.mpr (fun p _ => closureJ2_shape _ φ a p), List.mergeSort_nil]
  unfold fixBodyAt
  dsimp only
  rw [hst]
  dsimp only
  rw [hrun]
  dsimp only
  rw [hl]
  simp [ColumnI.endsOk_nil]
  rfl

end

/-! ## `J2`'s closure of `I`: its function, its membership, its call -/

section
variable {dm : DataModel} {D : Decisions}

open Ochr.Meaning.Steps.Form.ColumnJ (KJ)

/-- The binders and codomain the `.fix` clause reads `I`'s signature at, from the empty state, in `J2`'s context. -/
noncomputable def fbJ2 (dm : DataModel) (D : Decisions) (f : Sem) (ρ : Assignment) (φ : Future) : List PBind × PBind :=
  (bindsOf (KJ dm D f) ρ φ (emptyState 0) [.nat],
    fixCod (KJ dm D f) ρ φ (emptyState 0) (bindsOf (KJ dm D f) ρ φ (emptyState 0) [.nat]) .nat,
    (KJ dm D f).D.typeDecl ((KJ dm D f).D.teleDecls (scopeOf (emptyState 0)) [.nat]) .nat)

/-- **`I`'s function in `J2`'s context** (stage 1 at rank 0: `I` does not recurse). -/
noncomputable def gJ2 (dm : DataModel) (D : Decisions) (f : Sem) (ρ : Assignment) (φ : Future) :
    List Sem → Option BodyOut :=
  fixG (KJ dm D f) ρ φ (fbJ2 dm D f ρ φ) 1 (emptyState 0) psI outI (piTyAt dm.read 1 psI outI) 0 none bodyI

namespace Aux
open Ochr.Meaning.Regress.GenNeutralContent (isOk outVal)
theorem ok_td_nat1 : isOk (ColumnI.Aux.typeDeclRun .nat) (scopeState FrameJ2.Guards.stJ2 [.other]) 1000 = true := by
  decide +kernel
theorem val_td_nat1 : isOther (outVal (ColumnI.Aux.typeDeclRun .nat) (scopeState FrameJ2.Guards.stJ2 [.other]) 1000) = true := by
  decide +kernel
end Aux

theorem fixDecJ2 (hd : DecTab D FrameJ2.Guards.stJ2) :
    D.flags [] fixI = (false, false) ∧ D.piSort [] (.pi [⟨"n"⟩] [.nat] .nat) = 1 ∧ D.paramDecls [] [.nat] = [.other] ∧
      D.typeDecl [] .nat = .other ∧ D.typeDecl [.other] .nat = .other := by
  have hd' : DecTab D Ochr.Meaning.Steps.Form.CallGuards.stJ := hd
  obtain ⟨-, hps, hpd⟩ := GlobalsLocal.fixDecJ hd'
  refine ⟨?_, hps, hpd, ?_, ?_⟩
  · rw [hd'.flags 100 [] fixI _ 1000 _ (Regress.GenNeutralContent.runs_out (Ochr.Meaning.Steps.Form.ColumnC.Aux.flagsRun fixI)
      _ 1000 GlobalsLocal.Aux.ok_flags_fixJ), GlobalsLocal.Aux.val_flags_fixJ]
  · rw [hd'.typeDecl 100 [] .nat _ 1000 _ (Regress.GenNeutralContent.runs_out (ColumnI.Aux.typeDeclRun .nat) _ 1000
      GlobalsLocal.Aux.ok_td_natJ)]
    exact Ochr.Meaning.Steps.Form.ColumnC.Aux.isOther_eq GlobalsLocal.Aux.val_td_natJ
  · rw [hd.typeDecl 100 [.other] .nat _ 1000 _ (Regress.GenNeutralContent.runs_out (ColumnI.Aux.typeDeclRun .nat) _ 1000
      Aux.ok_td_nat1)]
    exact Ochr.Meaning.Steps.Form.ColumnC.Aux.isOther_eq Aux.val_td_nat1

/-- **`I`'s function in `J2`'s context at every number**: `a + 1`, no final. No fact assumed. -/
theorem gJ2_run (hd : DecTab D FrameJ2.Guards.stJ2) (f : Sem) (ρ : Assignment) (φ : Future) (a : Nat) :
    gJ2 dm D f ρ φ [.el0 Nat a] = some ⟨.el0 Nat (a + 1), [], none⟩ := by
  obtain ⟨-, -, hpd, htd, htd1⟩ := fixDecJ2 hd
  have h1 : (fbJ2 dm D f ρ φ).1 = [(fun _ => .plain TyM.nat, .other)] :=
    ColumnI.bindsOf_nat _ ρ φ _ (by show D.paramDecls [] [.nat] = [.other]; exact hpd)
  have h2 : (fbJ2 dm D f ρ φ).2.2 = .other := by
    show D.typeDecl (D.teleDecls [] [.nat]) .nat = .other
    simp [Decisions.teleDecls, htd, htd1]
  exact fixBodyAt_J2 (ρ := ρ) (φ := φ) hd (KJ dm D f) rfl _ h1 h2 a

theorem gJ2_tot (hd : DecTab D FrameJ2.Guards.stJ2) (f : Sem) (ρ : Assignment) (φ : Future) :
    ∀ args, DomMembers dm.read psI args →
      ∃ o, gJ2 dm D f ρ φ args = some o ∧ OutGood dm.read psI outI args o ∧ o.finals.length = (psI.filter (·.isRef)).length := by
  intro args ha
  obtain ⟨m, rfl⟩ := ColumnR.domMembers_one ha
  refine ⟨_, gJ2_run hd f ρ φ m, ⟨⟨m + 1, rfl⟩, fun i d hi hd' => ?_⟩, rfl⟩
  rcases i with _ | i
  · simp [psI] at hi; subst hi; cases hd'
  · simp [psI] at hi

/-- `J2`'s closure of `I` is a member of `Π(n : Nat). Nat`. -/
theorem gJ2_mem (hd : DecTab D FrameJ2.Guards.stJ2) (f : Sem) (ρ : Assignment) (φ : Future) :
    closureAt dm.read 1 φ psI outI (gJ2 dm D f ρ φ) ∈ₛ[dm.read] piTyAt dm.read 1 psI outI :=
  closure_mem_of_total' dm.read 1 φ psI outI _ ⟨Nat.le_refl 1, by omega⟩ rfl (fun _ _ => Nat.le_refl 1)
    (gJ2_tot hd f ρ φ)

/-- **`I`'s meaning in `J2`'s context is that closure** (`GlobalsLocal.fJ`, the meaning of the closure value
`.clo [] fixI []`: the `.fix` clause's run, whose strict test is the membership). -/
theorem fJ_eq_J2 (hd : DecTab D FrameJ2.Guards.stJ2) :
    GlobalsLocal.fJ dm D = closureAt dm.read 1 noFuture psI outI (gJ2 dm D .err (fun _ => .err) noFuture) := by
  obtain ⟨hfl, hps, hpd, -, -⟩ := fixDecJ2 hd
  have hpd' : (KJ dm D .err).D.paramDecls (scopeOf (emptyState 0)) [.nat] = [.other] := hpd
  have hsort : fixSort (KJ dm D .err) (emptyState 0) [⟨"n"⟩] [.nat] .nat = 1 := hps
  have hty : fixTy (KJ dm D .err) (fun _ => .err) noFuture (emptyState 0) [⟨"n"⟩] [.nat] .nat = piTyAt dm.read 1 psI outI := by
    unfold fixTy; rw [hsort, ColumnI.runDoms_nat _ _ _ _ hpd', ColumnI.codOf_nat]; rfl
  have hclo : fixClo (KJ dm D .err) (fun _ => .err) noFuture (emptyState 0) [⟨"n"⟩] [.nat] .nat none bodyI =
      closureAt dm.read 1 noFuture psI outI (gJ2 dm D .err (fun _ => .err) noFuture) := by
    unfold fixClo
    rw [hty, hsort, ColumnI.runDoms_nat _ _ _ _ hpd', ColumnI.codOf_nat]
    rfl
  have hrun := run_fix_of_mem (K := KJ dm D .err) (ρ := fun _ => .err) (φ := noFuture) false (.plain .err) ⟨"I"⟩
    [⟨"n"⟩] [.nat] .nat none bodyI (emptyState 0) hfl (by rw [show capOrder (.fix ⟨"I"⟩ [⟨"n"⟩] [.nat] .nat none bodyI) = [] from rfl]; trivial)
    (by rw [hty, hclo]; exact gJ2_mem hd _ _ _)
  show meanV (KJ dm D .err) (fun _ => .err) noFuture (.plain .err) (.clo [] fixI []) = _
  rw [meanV, if_pos (by exact trivial)]
  have hs0 : stateOf 0 (capsState (capsVals (KJ dm D .err) (fun _ => .err) noFuture [])
      (capsTys (KJ dm D .err) (fun _ => .err) noFuture [])) = emptyState 0 := rfl
  rw [hs0, show fixI = .fix ⟨"I"⟩ [⟨"n"⟩] [.nat] .nat none bodyI from rfl, hrun, hclo]

/-- **`J2`'s closure of `I` is a member of `Π(n : Nat). Nat`, at `J2`'s table** (`GlobalsOk.mem`'s content for `I` in
`J2`'s context; D130's `fJ_mem` was at `I`'s table under column `I`'s checker facts). No fact assumed. -/
theorem fJ_mem_J2 (hd : DecTab D FrameJ2.Guards.stJ2) : GlobalsLocal.fJ dm D ∈ₛ[dm.read] piTyAt dm.read 1 psI outI := by
  rw [fJ_eq_J2 hd]; exact gJ2_mem hd _ _ _

/-- **The call of `J2`'s `I` at any number `a`**: `a + 1` at `Nat`, the state as it was. No fact assumed. -/
theorem callOf_fJ_J2 (hd : DecTab D FrameJ2.Guards.stJ2) (a : Nat) (s : SState) :
    callOf dm.read (GlobalsLocal.fJ dm D, .plain (piTyAt dm.read 1 psI outI)) [(.el0 Nat a, .plain TyM.nat)] s =
      some ((.el0 Nat (a + 1), .plain TyM.nat), s) := by
  rw [fJ_eq_J2 hd]
  obtain ⟨s', hs'⟩ := closure_apply' dm.read 1 noFuture psI outI (gJ2 dm D .err (fun _ => .err) noFuture)
    ⟨Nat.le_refl 1, by omega⟩ rfl (fun _ _ => Nat.le_refl 1) (gJ2_tot hd _ _ _) [(.el0 Nat a, .plain TyM.nat)] s
    ⟨.el0 Nat (a + 1), [], none⟩ (ColumnR.domMembers_nat dm.read a)
    (fun i d hd' => by rcases i with _ | i <;> simp [psI] at hd'; subst hd'; exact Nat.le_refl 1)
    trivial (gJ2_run hd _ _ _ a)
  have hss : s' = s := ColumnJ.callOf_unlabelled_state _ _ _ _ _ _ hs' (fun a ha => by simp at ha; subst ha; rfl) rfl
  subst hss
  exact hs'

end

end Ochr.Meaning.Steps.Form.CallJ2
