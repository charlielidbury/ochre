import Ochr.Meaning.Regress.FrameCheck

/-!
# `Id1(&y)` in place under main's D99, against `callOf` (kernel-checked)

The call in place (`CallRef.runCallRef`) reserves the result's label `1` before the body runs and lends
it, as a fill, where the argument `&y` lent (`y`); the body `&*x` makes the reborrow `2`; the pop ends
`x`'s label `0`, handing `y` to the reborrow; then the reborrow is renamed into `1` (`endInto`). Against
`callOf` (`SC1`, `Regress/CallInPlace.lean`): the same result (`2` at the label `1`), the same positions,
holders and lending of `1`, and, at every future that gives `1` a number, the same meaning at every
position (`y` reads `1`'s final content raw in place, decoded by `callOf`).
-/

namespace Ochr.Meaning.Regress.CallInPlace
open Ochr Ochr.Meaning Ochr.Meaning.Regress.FrameCheck

variable (dm : DataModel) (ρ : Assignment) (φ : Future) {r : Sem}

/-- The caller's state after the reservation: the counter at `2`, `1` lent at `y` as a fill. -/
def S₂r : SState := ((Attack.S₂ yB 0 (.el0 Nat 2)).freshLoan).2.setLent 1 [⟨.bind 0 0, [], true⟩]

section
variable (selfB : SBinding) (d : DeclInfo)

/-- The callee's frame pushed on `S₂r`. -/
def SPr (c r : Sem) : SState :=
  { env := [yFrame, SFrame.mk [selfB, xB c d] []],
    shape := fun p => if p = .bind 1 1 then some 0 else none, nextLoan := 2,
    lent := fun m => if m = 0 then [⟨.bind 0 0, [], false⟩] else if m = 1 then [⟨.bind 0 0, [], true⟩] else [],
    heldTy := fun m => if m = 0 then yB.ty.m else TyM.err,
    heldMem := fun m => if m = 0 then r else .err }

/-- After `&*x`: the reborrow `2` parked in the callee's frame, lent at `*x`. -/
def SPr2 (T : TyM) (c r : Sem) : SState :=
  { env := [yFrame, SFrame.mk [selfB, { xB c d with val := fun φ' => φ' 2 }] [fun _ => c]],
    shape := fun p => if p = .temp 1 0 then some 2 else if p = .bind 1 1 then some 0 else none, nextLoan := 3,
    lent := fun m => if m = 2 then [⟨.bind 1 1, [.deref], false⟩] else if m = 0 then [⟨.bind 0 0, [], false⟩]
      else if m = 1 then [⟨.bind 0 0, [], true⟩] else [],
    heldTy := fun m => if m = 2 then T else if m = 0 then yB.ty.m else TyM.err,
    heldMem := fun m => if m = 2 then c else if m = 0 then r else .err }

theorem positions_SPr (c : Sem) : (SPr selfB d c r).positions = [.bind 0 0, .temp 0 0, .bind 1 0, .bind 1 1] := by
  simp [SPr, yFrame, SState.positions, List.range']

theorem liveLabels_SPr (c : Sem) : (SPr selfB d c r).liveLabels = [0] := by
  unfold SState.liveLabels; rw [positions_SPr]; simp [SPr]

theorem reached_SPr (c : Sem) (hit : List Step → Bool) (l : Nat) : (SPr selfB d c r).reached (.bind 1 1) hit l = false := by
  unfold SState.reached
  by_cases h0 : l = 0
  · subst h0; simp [SPr]
  · by_cases h1 : l = 1
    · subst h1; simp [SPr]
    · simp [SPr, h0, h1]

theorem access_SPr (c : Sem) (hit : List Step → Bool) : (SPr selfB d c r).access (.bind 1 1) hit = SPr selfB d c r := by
  unfold SState.access
  have h : ∀ n : Nat, (List.range n).foldl (fun s _ => (s.liveLabels.filter (s.reached (.bind 1 1) hit)).foldl SState.endLabel s)
      (SPr selfB d c r) = SPr selfB d c r := by
    intro n; induction n with
    | zero => rfl
    | succ n ih => rw [List.range_succ, List.foldl_append, ih]; simp [liveLabels_SPr, reached_SPr]
  exact h _

theorem typedFuture_SPr (c : Sem) (ψ : Future) : (SPr selfB d c r).typedFuture ψ = ψ.upd 0 r := by
  funext l; unfold SState.typedFuture; rw [liveLabels_SPr]
  by_cases hl : l = 0 <;> simp [hl, SPr, Future.upd]

theorem contentOf_SPr (c : Sem) :
    contentOf (Kc dm) φ (.deref (.var 0)) (SPr selfB d c r) = some ((c, T₀, .bind 1 1, [.deref]), SPr selfB d c r) := by
  unfold contentOf
  rw [show resolve (SPr selfB d c r) (.deref (.var 0)) = some (.bind 1 1, [.deref]) by
    simp [resolve, SState.varPos, SState.topIdx, Place.steps, SPr]]
  dsimp only
  rw [access_SPr, typedFuture_SPr]
  simp [Sem.follow, Sem.step, SState.valAt, SState.tyAt, SPr, xB, T₀]

/-- `&*x` in place, after the reservation: the reborrow is `2`. -/
theorem run_id1_r (a : Nat) (hint : TyS) (tl : Bool) :
    runT (Kc dm) ρ φ tl hint id1Body (SPr selfB d (.el0 Nat a) r)
      = some ((.el0 Nat a, { T₀ with label := some 2 }), SPr2 selfB d T₀.m (.el0 Nat a) r) := by
  simp only [id1Body, runT, SM.erasedIf, flags_Kc, Bool.false_eq_true, if_false, SM.stmtIf]
  unfold borrowPlace
  simp only [contentOf_SPr, bind, Option.bind]
  simp [Sem.whole, SState.freshLoan, SState.tyAt, SState.valAt, SState.setAt,
    Attack.updAt_deref, Attack.updAt_nil, SState.pushTempShaped, SState.pushTemp, SState.topIdx, SState.setLent,
    SState.setHeldTy, SState.setHeldMem, SPr, SPr2, xB]

end

section
variable (selfB : SBinding) (d : DeclInfo)

theorem positions_SPr2 (T : TyM) (c : Sem) :
    (SPr2 selfB d T c r).positions = [.bind 0 0, .temp 0 0, .bind 1 0, .bind 1 1, .temp 1 0] := by
  simp [SPr2, yFrame, SState.positions, List.range']

theorem liveLabels_SPr2 (T : TyM) (c : Sem) : (SPr2 selfB d T c r).liveLabels = [0, 2] := by
  unfold SState.liveLabels; rw [positions_SPr2]; simp [SPr2]
  first | rfl | decide | simp [List.mergeSort]

theorem holderOf_SPr2 (T : TyM) (c : Sem) : (SPr2 selfB d T c r).holderOf 0 = some (.bind 1 1) := by
  unfold SState.holderOf; rw [positions_SPr2]; simp [SPr2]

theorem find_SPr2 (T : TyM) (c : Sem) :
    ((SPr2 selfB d T c r).positions.find? fun p => decide ((SPr2 selfB d T c r).shape p = some 0)) = some (.bind 1 1) := by
  rw [positions_SPr2]; simp [SPr2]

theorem endLabel_SPr2 (T : TyM) (c : Sem) : (SPr2 selfB d T c r).endLabel 0 =
    (let m := (SPr2 selfB d T c r).toMean.semEnd (.bind 1 1) 0
     ({ SPr2 selfB d T c r with shape := m.shape, lent := (SPr2 selfB d T c r).relend 0 (.bind 1 1) }).mapVals
       fun p _ => (m.val · p)) := by
  unfold SState.endLabel; rw [find_SPr2]

theorem holderOf_end_SPr2 (T : TyM) (c : Sem) : ((SPr2 selfB d T c r).endLabel 0).holderOf 2 = some (.temp 1 0) := by
  rw [endLabel_SPr2]
  unfold SState.holderOf
  simp [SState.positions, SState.mapVals, SPr2, yFrame, List.range', Mean.semEnd, SState.toMean]

end

theorem callFrame_id1r (cd : DeclInfo) (bs : List PBind) (hb : bs = bindsOf (Kc dm) ρ φ S₂r.pushFrame [.ref .nat]) :
    callFrame (Kc dm) ρ φ [] [] (fresId1 dm ρ φ) cd bs [(.el0 Nat 2, { yB.ty with label := some 0 })] S₂r
      = SPr (selfId1P dm ρ φ cd) ((bs.getD 0 (fun _ => .plain TyM.err, .other)).2) (.el0 Nat 2) (.el0 Nat 2) := by
  subst hb
  simp [callFrame, capsState, capsVals, capsTys, SState.pushFrame, SState.pushBind, SState.topIdx, pushBindShaped,
    SState.takeLabel, SState.holderOf, SState.positions, List.range', S₂r, Attack.S₂, SState.freshLoan, SState.setLent,
    SState.setAt, SPr, yFrame, selfId1P, xB, bindsOf, runBinds, mkBind]
  refine ⟨rfl, ?_, ?_⟩
  · funext p
    by_cases h1 : p = Pos.bind 1 1 <;> by_cases h2 : p = Pos.temp 0 0 <;> simp [h1, h2]
  · funext m
    by_cases h0 : m = 0 <;> by_cases h1 : m = 1 <;> simp [h0, h1]

/-- **`Id1(&y)` in place under D99, against `callOf`, at typed futures**: the same result (`2` at the
reserved label `1`, the reborrow `2` renamed into it), the same positions, holders and lending of `1`,
and at every future that gives `1` a number the same meaning at every position. -/
theorem id1_inPlace_typed :
    ∃ T s', runCallRef (Kc dm) ρ φ (fresId1 dm ρ φ) [] id1T [] [(.el0 Nat 2, { yB.ty with label := some 0 })]
        (Attack.S₂ yB 0 (.el0 Nat 2)) = some ((.el0 Nat 2, T), s') ∧ T.label = some 1 ∧
      s'.positions = (SC1 dm).positions ∧ s'.shape = (SC1 dm).shape ∧ s'.lent 1 = (SC1 dm).lent 1 ∧
      ∀ (p : Pos) (ψ : Future) (n : Nat), ψ 1 = .el0 Nat n → s'.valAt p ψ = (SC1 dm).valAt p ψ := by
  have hs₀ : (capsState (capsVals (Kc dm) ρ φ []) (capsTys (Kc dm) ρ φ [])).foldl SState.pushBind
      S₂r.pushFrame = S₂r.pushFrame := by
    simp [capsState, capsVals, capsTys]
  have hres : ((Attack.S₂ yB 0 (.el0 Nat 2)).freshLoan).2.setLent ((Attack.S₂ yB 0 (.el0 Nat 2)).freshLoan).1
      ((([(.el0 Nat 2, { yB.ty with label := some 0 })] : List Res).filterMap (·.2.label)).flatMap
        (Attack.S₂ yB 0 (.el0 Nat 2)).lent |>.map fun x : Site => { x with fill := true }) = S₂r := by
    simp [S₂r, Attack.S₂, SState.freshLoan]
  let cd := (Kc dm).D.typeDecl ((Kc dm).D.teleDecls (scopeOf S₂r.pushFrame) [.ref .nat]) (.ref .nat)
  let d := ((bindsOf (Kc dm) ρ φ S₂r.pushFrame [.ref .nat]).getD 0 (fun _ => .plain TyM.err, .other)).2
  have hpop := popCallFrame_two 2 (SPr2 (selfId1P dm ρ φ cd) d T₀.m (.el0 Nat 2) (.el0 Nat 2)) 0 2 1 1 (.temp 1 0)
    (liveLabels_SPr2 _ _ _ _) (holderOf_SPr2 _ _ _ _) rfl (by decide) (holderOf_end_SPr2 _ _ _ _)
  have hrun : runCallRef (Kc dm) ρ φ (fresId1 dm ρ φ) [] id1T [] [(.el0 Nat 2, { yB.ty with label := some 0 })]
      (Attack.S₂ yB 0 (.el0 Nat 2)) = some ((.el0 Nat 2, { T₀ with label := some 1 }),
        (popCallFrame 2 (some 2) (SPr2 (selfId1P dm ρ φ cd) d T₀.m (.el0 Nat 2) (.el0 Nat 2))).endInto 2 1) := by
    unfold runCallRef
    simp only [id1T]
    rw [hres]
    unfold runBodyRef
    simp only [hs₀]
    rw [callFrame_id1r dm ρ φ _ _ rfl, run_id1_r]
    simp [outId1, codOf_id1, S₂r, Attack.S₂, SState.freshLoan, SState.setLent]
    rfl
  refine ⟨_, _, hrun, rfl, ?_, ?_, ?_, ?_⟩
  · rw [hpop, endLabel_SPr2]
    simp [SState.endInto, SState.positions, SState.pushTempShaped, SState.pushTemp, SState.mapVals, SState.topIdx, SPr2,
      yFrame, SC1, Attack.takeLabel_S₂, SState.freshLoan, List.range']
  · rw [hpop, endLabel_SPr2]
    funext p
    rcases p with ⟨f, i⟩ | ⟨f, i⟩ <;> rcases f with _ | _ | f <;> rcases i with _ | _ | i <;>
      simp [SState.endInto, SState.pushTempShaped, SState.pushTemp, SState.mapVals, SState.topIdx, SPr2, yFrame, SC1,
        Attack.takeLabel_S₂, SState.freshLoan, Mean.semEnd, SState.toMean]
  · rw [hpop, endLabel_SPr2]
    simp [SState.endInto, SState.pushTempShaped, SState.pushTemp, SState.mapVals, SState.topIdx, SPr2, yFrame, SC1,
      Attack.takeLabel_S₂, SState.freshLoan, SState.setLent, SState.relend]
  · intro p ψ n hψ
    have hd : Code0.dec dm.read TyM.nat.code0.snd (.el0 Nat n) = some (show TyM.nat.code0.fst from n) :=
      Attack.dec_nat_el0 dm.read n
    rw [hpop, endLabel_SPr2]
    rcases p with ⟨f, i⟩ | ⟨f, i⟩ <;> rcases f with _ | _ | f <;> rcases i with _ | _ | i <;>
      simp [SState.endInto, SState.valAt, SState.pushTempShaped, SState.pushTemp, SState.mapVals, SState.topIdx, SPr2,
        yFrame, SC1, Attack.takeLabel_S₂, SState.freshLoan, Mean.semEnd, SState.toMean, hψ, hd, xB, Future.upd] <;>
      rfl

end Ochr.Meaning.Regress.CallInPlace
