import Ochr.Meaning.Regress.CodeRuns
import Ochr.Meaning.CallRef
import Ochr.Meaning.BotWrite

/-!
# A call with a borrow parameter, by the callee's meaning and in place (docs/31 D62; in progress)

The reference's own runs of the checker's probes (`Regress/ShapeProbes.lean`: `UseInc`, `UseId1`),
kernel-checked: `Inc (x : &Nat) : Unit := *x := S(*x)` and `let y = 2; Inc(&y); y`, with `Inc`'s
closure as the call's head.
- By `callOf` (the closure's meaning applied): `Inc`'s closure means the closure of its body run
  (`meanV_incClo`, through `RunCongr.run_fix_def`); the body run at `a` gives `()` and `x`'s final
  content `a + 1` (`gInc_eval`: the frame, the read of `*x`, the write, the pop's end of `x`'s label
  through its cell); the closure is built (`mkTel_inc`); applying it (`Apply1.applyFnL_closureL`)
  consumes the borrow's holder and fixes its label's final content to `3` (`callOf_inc`); `y` then
  reads `3` (`useInc_callOf`), the checker's answer.
-/

namespace Ochr.Meaning.Regress.CallInPlace
open Ochr Ochr.Meaning Ochr.Meaning.Regress.CodeRuns

/-- `Inc (x : &Nat) : Unit := *x := S(*x)`'s body, `x` its innermost binding. -/
def incBody : Term := .assign (.deref (.var 0)) (.succ (.place (.deref (.var 0))))
/-- `Inc`'s term, and its closure (no captures). -/
def incT : Term := .fix ⟨"Inc"⟩ [⟨"x"⟩] [.ref .nat] .unit none incBody
def incClo : Value := .clo [] incT []

/-- The context: no inductive, no global, the probes' decisions. -/
def Kc (dm : DataModel) : RunCtx := Kp dm [] (fun _ => (.err, .plain TyM.err))

variable (dm : DataModel) (ρ : Assignment) (φ : Future)

/-- `Inc`'s parameter and codomain as the clause reads them: a borrow of `Nat`, `Unit`. -/
def psInc : List PiDom := [⟨true, fun _ => TyM.nat⟩]
def outInc : PiCod := ⟨false, fun _ => TyM.unit⟩

theorem psOf_inc (s : SState) (dcs : List DeclInfo) :
    psOf (runBinds (Kc dm) ρ φ s dcs [] [.ref .nat]) [.ref .nat] = psInc := rfl

theorem codOf_inc (s : SState) (bs : List PBind) : codOf (Kc dm) ρ φ s bs .unit = outInc := rfl

/-- `Inc`'s closure's frame data, as the `.fix` clause reads it in the empty frame. -/
noncomputable def fbInc : List PBind × (List Sem → TyS) × DeclInfo :=
  (bindsOf (Kc dm) ρ φ (stateOf 0 []) [.ref .nat],
    fixCod (Kc dm) ρ φ (stateOf 0 []) (bindsOf (Kc dm) ρ φ (stateOf 0 []) [.ref .nat]) .unit,
    (Kc dm).D.typeDecl ((Kc dm).D.teleDecls [] [.ref .nat]) .unit)

/-- `Inc`'s type: `Π(x : &Nat). Unit`'s code. -/
noncomputable def piInc : TyM := piTyAt dm.read 1 psInc outInc

/-- `Inc`'s body run (`Run.lean`'s `bodyAt`, named in `RunCongr`), `self` read as `err`. -/
noncomputable def gInc : List Sem → Option BodyOut :=
  fixBodyAt (Kc dm) ρ φ (fbInc dm ρ φ) (stateOf 0 []) psInc outInc (piInc dm) 0 incBody .err

/-- **`Inc`'s closure means the closure of its body run**, at its code. -/
theorem meanV_incClo (hint : TyS) :
    meanV (Kc dm) ρ φ hint incClo = closureAt dm.read 1 φ psInc outInc (gInc dm ρ φ) := by
  show (match runT (Kc dm) ρ φ false (.plain .err) incT (stateOf 0 (capsState [] [])) with
    | some ((v, _), _) => v | none => .err) = _
  rw [incT, run_fix_def]
  rfl

/-! ## `Inc`'s body run in its own frame -/

/-- `self`'s binding in `Inc`'s frame (read as `err`: `Inc` does not recurse). -/
noncomputable def selfInc : SBinding := { ty := .plain (piInc dm), val := fun _ => .err, decl := .pi (fbInc dm ρ φ).2.2 }

/-- The parameter's declared reading, as the clause reads it. -/
noncomputable def dInc : DeclInfo := ((Kc dm).D.paramDecls [] [.ref .nat]).getD 0 .other

/-- `x`'s binding: the borrowed content `c`, holder of the fresh label `0`. -/
def xB (c : Sem) (d : DeclInfo) : SBinding := { ty := { (TyS.plain TyM.nat) with label := some 0 }, val := fun _ => c, decl := d }

/-- `Inc`'s frame: `self`, `x` holding `c` at label `0`, and `x`'s cell reading `0`'s final content. -/
noncomputable def SB (c : Sem) : SState :=
  { env := [{ binds := [selfInc dm ρ φ, xB c (dInc dm)], temps := [fun ψ => ψ 0] }],
    shape := fun p => if p = .bind 0 1 then some 0 else none, nextLoan := 1 }

theorem frame_inc (c : Sem) :
    ([c].zip psInc).foldl (fixStep (fbInc dm ρ φ)) ((stateOf 0 []).pushBind (selfInc dm ρ φ), [], [])
      = (SB dm ρ φ c, [c], [.temp 0 0]) := by
  simp [fixStep, psInc, stateOf, SState.freshLoan, SState.pushTemp, SState.pushBind, SState.topIdx, pushBindShaped,
    SState.takeLabel, SState.holderOf, SState.positions, SB, xB, dInc, fbInc, bindsOf, runBinds, mkBind]
  exact ⟨rfl, rfl⟩

theorem positions_SB (c : Sem) : (SB dm ρ φ c).positions = [.bind 0 0, .bind 0 1, .temp 0 0] := by
  simp [SB, SState.positions, List.range']

theorem liveLabels_SB (c : Sem) : (SB dm ρ φ c).liveLabels = [0] := by
  unfold SState.liveLabels; rw [positions_SB]; simp [SB]

theorem holderOf_SB (c : Sem) : (SB dm ρ φ c).holderOf 0 = some (.bind 0 1) := by
  unfold SState.holderOf; rw [positions_SB]; simp [SB]

theorem reached_SB (c : Sem) (p : Pos) (hit : List Step → Bool) (l : Nat) : (SB dm ρ φ c).reached p hit l = false := by
  simp [SState.reached, SB]

theorem access_SB (c : Sem) (p : Pos) (hit : List Step → Bool) : (SB dm ρ φ c).access p hit = SB dm ρ φ c := by
  unfold SState.access
  have h : ∀ n : Nat, (List.range n).foldl (fun s _ => (s.liveLabels.filter (s.reached p hit)).foldl SState.endLabel s)
      (SB dm ρ φ c) = SB dm ρ φ c := by
    intro n; induction n with
    | zero => rfl
    | succ n ih => rw [List.range_succ, List.foldl_append, ih]; simp [liveLabels_SB, reached_SB]
  exact h _

theorem closedFuture_SB (c : Sem) (ψ : Future) : (SB dm ρ φ c).closedFuture ψ = ψ.upd 0 c := by
  unfold SState.closedFuture; rw [liveLabels_SB]
  simp only [List.length_singleton, List.range_one, List.foldl_cons, List.foldl_nil, holderOf_SB]
  rfl

theorem resolve_SB (c : Sem) : resolve (SB dm ρ φ c) (.deref (.var 0)) = some (.bind 0 1, [.deref]) := by
  simp [resolve, SState.varPos, SState.topIdx, Place.steps, SB]

/-- `*x` in `Inc`'s frame: `x`'s content, at `x`'s position through `*`; the state unchanged. -/
theorem contentOf_SB (c : Sem) :
    ∃ T, contentOf (Kc dm) φ (.deref (.var 0)) (SB dm ρ φ c) = some ((c, T, .bind 0 1, [.deref]), SB dm ρ φ c) := by
  unfold contentOf
  rw [resolve_SB]
  dsimp only
  rw [access_SB, closedFuture_SB]
  simp [Sem.follow, Sem.step, SState.valAt, SState.tyAt, SB, xB]

theorem flags_Kc (sc : List DeclInfo) (t : Term) : (Kc dm).D.flags sc t = (false, false) := rfl
theorem copy_Kc (r : DeclInfo) : (Kc dm).D.copy r = true := rfl

theorem readPlace_SB (a : Nat) :
    ∃ T, readPlace (Kc dm) φ (.deref (.var 0)) true (SB dm ρ φ (.el0 Nat a))
      = some ((.el0 Nat a, T), SB dm ρ φ (.el0 Nat a)) := by
  obtain ⟨T, hT⟩ := contentOf_SB dm ρ φ (.el0 Nat a)
  refine ⟨{ T with label := none }, ?_⟩
  simp [readPlace, hT, bind, Option.bind, Sem.whole]

theorem setContent_SB (a b : Nat) :
    setContent (Kc dm) φ (.bind 0 1) [.deref] (.el0 Nat b) (SB dm ρ φ (.el0 Nat a)) = some (⟨⟩, SB dm ρ φ (.el0 Nat b)) := by
  simp [setContent, Attack.updAt_deref, Attack.updAt_nil, SState.setAt, SB, xB, SState.valAt]

/-- `*x := S(*x)` in `Inc`'s frame: `x` holds `a + 1`. -/
theorem runBody_inc (a : Nat) (hint : TyS) (tl : Bool) :
    runT (Kc dm) ρ φ tl hint incBody (SB dm ρ φ (.el0 Nat a)) = some ((.el0 Unit (), .plain TyM.unit), SB dm ρ φ (.el0 Nat (a + 1))) := by
  obtain ⟨T, hT⟩ := contentOf_SB dm ρ φ (.el0 Nat a)
  obtain ⟨T', hT'⟩ := readPlace_SB dm ρ φ a
  simp only [incBody, runT, SM.erasedIf, SM.erasedAt, SM.stmtIf, flags_Kc, copy_Kc, hT, hT', Bool.false_eq_true, if_false,
    bind, Option.bind, pure]
  have hs : (Sem.el0 Nat a).succ = .el0 Nat (a + 1) := Sem.succ_el0 a
  have hl : (TyS.plain TyM.nat).label = none := rfl
  rw [hs, hl]
  simp only [assignAt, resolve_SB, List.isEmpty_cons, Bool.false_and, Bool.false_eq_true, if_false, access_SB,
    setContent_SB]

/-- Ending `x`'s label at the pop: the cell reads the content. -/
theorem endLabel_SB_cell (c : Sem) (ψ : Future) : ((SB dm ρ φ c).endLabel 0).valAt (.temp 0 0) ψ = c := by
  unfold SState.endLabel
  rw [positions_SB]
  simp [SB, SState.mapVals, SState.valAt, Mean.semEnd, SState.toMean, Future.upd]
  rfl

/-- **`Inc`'s body run at `a`**: `()`, and `x`'s final content `a + 1`. -/
theorem gInc_eval (a : Nat) :
    gInc dm ρ φ [.el0 Nat a] = some ⟨.el0 Unit (), [fun _ => .el0 Nat (a + 1)], none⟩ := by
  unfold gInc fixBodyAt
  rw [show ({ ty := .plain (piInc dm), val := fun _ => .err, decl := .pi (fbInc dm ρ φ).2.2 } : SBinding)
      = selfInc dm ρ φ from rfl]
  dsimp only
  rw [frame_inc]
  dsimp only
  rw [runBody_inc]
  dsimp only
  rw [liveLabels_SB]
  simp only [outInc, Bool.false_eq_true, if_false, List.filter_cons, List.filter_nil, ge_iff_le, Nat.zero_le,
    ne_eq, reduceCtorEq, not_false_eq_true, and_self, decide_true, if_true, List.foldl_cons, List.foldl_nil,
    List.map_cons, List.map_nil]
  congr
  funext ψ
  exact endLabel_SB_cell dm ρ φ _ ψ

/-! ## `Inc(&y)` by `callOf`: the closure applied -/

theorem dec_unit_el0 (R : DataRead) : Code0.unit.dec R (.el0 Unit ()) = some () := Code0.dec_enc R .unit ()

/-- The closure is built (its body runs at every number). -/
theorem mkTel_inc :
    (mkTelL (lvl0 dm.read) φ (telL (lvl0 dm.read) psInc [] PUnit outInc).2 [] (fun fs => some (PUnit.unit, fs))
      (gInc dm ρ φ)).isSome := by
  simp only [telL, psInc, outInc, mkTelL]
  have h : ∀ x : Nat, ((gInc dm ρ φ ([] ++ [Code0.enc dm.read Code0.nat x])).bind
      (mkLeafDataL (lvl0 dm.read) φ (extFin true PUnit Nat)
        (extMkL true PUnit Nat (fun fs => some (PUnit.unit, fs)) (Code0.dec dm.read Code0.nat)) Code0.unit)).isSome := by
    intro x
    rw [show Code0.enc dm.read Code0.nat x = .el0 Nat x from rfl, List.nil_append, gInc_eval]
    simp [mkLeafDataL, extMkL, Lvl.dec, lvl0, Attack.dec_nat_el0, dec_unit_el0]
  have h' : ∀ (x : TyM.nat.code0.fst), ((gInc dm ρ φ [Code0.enc dm.read TyM.nat.code0.snd x]).bind
      (mkLeafDataL (lvl0 dm.read) φ (extFin true PUnit TyM.nat.code0.fst)
        (extMkL true PUnit TyM.nat.code0.fst (fun fs => some (PUnit.unit, fs)) (Code0.dec dm.read TyM.nat.code0.snd))
        TyM.unit.code0.snd)).isSome := fun x => by have := h x; rw [List.nil_append] at this; exact this
  simp [h']

/-- **`callOf` on `Inc`'s closure at `2` with the borrow's label `lab`**: `()`, the borrow's holder
consumed, and the label's final content fixed to `3`. -/
theorem callOf_inc (s : SState) (T : TyS) (lab : Nat) :
    ∃ TU : TyS, TU.label = none ∧ callOf dm.read (closureAt dm.read 1 φ psInc outInc (gInc dm ρ φ), .plain (piInc dm))
        [(.el0 Nat 2, { T with label := some lab })] s
      = some ((.el0 Unit (), TU), (s.takeLabel lab).mapVals fun _ v φ' => v (φ'.updList [(lab, .el0 Nat 3)])) := by
  obtain ⟨o, r, hg, hap, hm⟩ := applyFnL_closureL (lvl0 dm.read) (lvl0_lawful dm.read) φ
    (telL (lvl0 dm.read) psInc [] PUnit outInc).2 (gInc dm ρ φ) [.el0 Nat 2] (mkTel_inc dm ρ φ)
    ⟨(2 : Nat), Attack.dec_nat_el0 dm.read 2, trivial⟩
  rw [gInc_eval] at hg
  cases hg
  rcases r with ⟨res, TT, fins⟩ | ⟨U, c, fwd, back⟩
  · obtain ⟨rfl, rfl⟩ := hm
    refine ⟨.plain TT, rfl, ?_⟩
    show callOfL (lvl0 dm.read) (telL (lvl0 dm.read) psInc [] PUnit outInc).2
      (closureL (lvl0 dm.read) φ (telL (lvl0 dm.read) psInc [] PUnit outInc).2 (gInc dm ρ φ)) _ s = _
    unfold callOfL
    dsimp only
    rw [show List.map (fun x : Res => x.fst) [(Sem.el0 Nat 2, { T with label := some lab })] = [Sem.el0 Nat 2] from rfl, hap]
    simp [telRefsL, telL, psInc, outInc]
    rw [show Code0.dec dm.read TyM.nat.code0.snd (Sem.el0 Nat 2) = some (2 : Nat) from Attack.dec_nat_el0 dm.read 2]
    rfl
  · obtain ⟨k, hk, -⟩ := hm
    cases hk

/-! ## `UseInc` by `callOf`: `let y = 2; Inc(&y); y` is `3` -/

/-- `Inc`'s closure as a call's head: its meaning, at its code. -/
theorem run_incClo (hint : TyS) (s : SState) :
    run (Kc dm) ρ φ hint (.val incClo) s = some ((closureAt dm.read 1 φ psInc outInc (gInc dm ρ φ), .plain (piInc dm)), s) := by
  rw [run_val_def, meanV_incClo]
  congr

/-- `y`'s binding: `2`, at the hint `let` gives a value (`err`). -/
def yB : SBinding := { ty := { (TyS.plain TyM.err) with label := none }, val := fun _ => .el0 Nat 2, decl := .other }

/-- `Inc(&y)`'s argument: `&y` at label `0`, `y` lent there, the content parked. -/
theorem runArgs_borrowY (fT : TyM) :
    runArgs (Kc dm) ρ φ false fT [] [.borrow (.var 0)] ((emptyState 0).pushBind yB)
      = some ([(.el0 Nat 2, { yB.ty with label := some 0 })], Attack.S₂ yB 0 (.el0 Nat 2)) := by
  rw [Attack.pushBind_emptyState]
  simp only [runArgs, Bool.false_and, SM.stmtIf, Bool.false_eq_true, if_false]
  have hb : runT (Kc dm) ρ φ false (.plain (TyM.domAfter (Kc dm).dm.read fT [])) (.borrow (.var 0))
      { env := [{ binds := [yB] }], shape := fun _ => none, nextLoan := 0 }
      = some ((.el0 Nat 2, { yB.ty with label := some 0 }), Attack.S₂ yB 0 (.el0 Nat 2)) := by
    rw [runT]
    simp only [SM.erasedIf, flags_Kc, Bool.false_eq_true, if_false, SM.stmtIf]
    rw [Attack.borrowPlace_var0_one _ _ _ _ (by simp [yB, Sem.whole])]
    rfl
  simp only [bind, Option.bind, SM.stmtIf, Bool.false_eq_true, if_false, hb, pure]

/-- `let y = 2; Inc(&y); y`, with `Inc`'s closure as the head. -/
def useIncT : Term := .letIn ⟨"y"⟩ (num 2) (.seq (.call (.val incClo) [.borrow (.var 0)] false) (.place (.var 0)))

/-- The state after the call: the parked borrow consumed, `y` reading label `0`'s final content,
fixed to `3`. -/
noncomputable def SI : SState :=
  ((Attack.S₂ yB 0 (.el0 Nat 2)).takeLabel 0).mapVals fun _ v φ' => v (φ'.updList [(0, .el0 Nat 3)])

theorem SI_shape : SI.shape = fun _ => none := by
  simp only [SI, SState.mapVals, Attack.takeLabel_S₂]

/-- Reading `y` after the call: `3`. -/
theorem readY_SI : ∃ T, readPlace (Kc dm) φ (.var 0) true SI = some ((.el0 Nat 3, T), SI) := by
  have h0 : ∀ l : List Pos, List.filterMap (fun _ : Pos => (none : Option Nat)) l = [] := by
    intro l; induction l <;> simp_all
  have hl : SI.liveLabels = [] := by
    unfold SState.liveLabels; rw [SI_shape, h0]; simp
  have hcf : SI.closedFuture φ = φ := by simp [SState.closedFuture, hl]
  have hr : resolve SI (.var 0) = some (.bind 0 0, []) := by
    simp [resolve, SState.varPos, SState.topIdx, Place.steps, SI, SState.mapVals, Attack.takeLabel_S₂]
  have hv : SI.valAt (.bind 0 0) φ = .el0 Nat 3 := by
    simp [SI, SState.mapVals, Attack.takeLabel_S₂, SState.valAt, Future.updList, Future.upd]
  refine ⟨{ SI.tyAt (.bind 0 0) with label := none }, ?_⟩
  simp only [readPlace, contentOf, hr, Attack.access_noShape SI SI_shape, hcf, Sem.follow, hv, bind, Option.bind]
  simp [Sem.whole]

/-- **`UseInc` by `callOf`: `let y = 2; Inc(&y); y` runs to `3`**, the checker's answer
(`Regress/ShapeProbes.lean`: `UseIncIs3` accepted, `UseIncIs2` rejected). -/
theorem useInc_callOf (hint : TyS) :
    ∃ T s', run (Kc dm) ρ φ hint useIncT (emptyState 0) = some ((.el0 Nat 3, T), s') := by
  obtain ⟨TU, hTU, hc⟩ := callOf_inc dm ρ φ (Attack.S₂ yB 0 (.el0 Nat 2)) yB.ty 0
  obtain ⟨Ty, hy⟩ := readY_SI dm φ
  have hcall : run (Kc dm) ρ φ (.plain .err) (.call (.val incClo) [.borrow (.var 0)] false) ((emptyState 0).pushBind yB)
      = some ((.el0 Unit (), TU), SI) := by
    rw [show Kc dm = Kp dm [] (fun _ => (.err, .plain TyM.err)) from rfl, run_call]
    rw [show Kp dm [] (fun _ => (.err, .plain TyM.err)) = Kc dm from rfl]
    simp only [SM.headOf, run_incClo, bind, Option.bind, runArgs_borrowY]
    exact hc
  have hd : discardEnd TU SI = SI := by simp [discardEnd, hTU]
  have hseq : run (Kc dm) ρ φ hint (.seq (.call (.val incClo) [.borrow (.var 0)] false) (.place (.var 0)))
      ((emptyState 0).pushBind yB) = some ((.el0 Nat 3, Ty), SI) := by
    show runT (Kc dm) ρ φ false hint _ _ = _
    rw [runT]
    simp only [SM.erasedIf, flags_Kc, Bool.false_eq_true, if_false, SM.stmtIf]
    show (do let r ← run (Kc dm) ρ φ (.plain .err) _; SM.modify (discardEnd r.2); runT (Kc dm) ρ φ false hint (.place (.var 0))) _ = _
    simp only [bind, Option.bind, hcall, SM.modify, hd]
    rw [runT]
    simp only [SM.erasedAt, flags_Kc, copy_Kc, Bool.false_eq_true, if_false, SM.stmtIf]
    exact hy
  refine ⟨Ty, ?_⟩
  rw [useIncT, show Kc dm = Kp dm [] (fun _ => (.err, .plain TyM.err)) from rfl, run_letIn, run_num]
  rw [show Kp dm [] (fun _ => (.err, .plain TyM.err)) = Kc dm from rfl]
  simp only [bind, Option.bind]
  rw [Attack.pushBindShaped_noLabel _ _ rfl]
  rw [show ({ ty := { (TyS.plain TyM.err) with label := none }, val := fun _ => .el0 Nat 2, decl := .other } : SBinding)
    = yB from rfl, hseq]
  exact ⟨_, rfl⟩

/-! ## `Inc(&y)` in place (`CallRef.runCallRef`): the body run on the caller's state -/

/-- `Inc`'s reading as a call's head (`run_incClo`). -/
noncomputable def fresInc : Res := (closureAt dm.read 1 φ psInc outInc (gInc dm ρ φ), .plain (piInc dm))

/-- `self`'s binding in the callee's frame pushed in place. -/
noncomputable def selfP (cd : DeclInfo) : SBinding :=
  { ty := { (fresInc dm ρ φ).2 with label := none }, val := fun _ => (fresInc dm ρ φ).1, decl := .pi cd }

/-- The caller's frame after `&y` and the borrow's holder moved into the callee's parameter. -/
def yFrame : SFrame := { binds := [{ yB with val := fun φ' => φ' 0 }], temps := [fun _ => .moved] }

/-- The caller's state with `Inc`'s frame pushed in place: `x` holds `c` at `y`'s own label `0`. -/
noncomputable def SP (cd d : DeclInfo) (c : Sem) : SState :=
  { env := [yFrame, { binds := [selfP dm ρ φ cd, xB c d] }],
    shape := fun p => if p = .bind 1 1 then some 0 else none, nextLoan := 1,
    lent := fun m => if m = 0 then [⟨.bind 0 0, [], false⟩] else [] }

theorem callFrame_inc (cd : DeclInfo) (bs : List PBind) (hb : bs = bindsOf (Kc dm) ρ φ (Attack.S₂ yB 0 (.el0 Nat 2)).pushFrame [.ref .nat]) :
    callFrame (Kc dm) ρ φ [] [] (fresInc dm ρ φ) cd bs [(.el0 Nat 2, { yB.ty with label := some 0 })] (Attack.S₂ yB 0 (.el0 Nat 2))
      = SP dm ρ φ cd ((bs.getD 0 (fun _ => .plain TyM.err, .other)).2) (.el0 Nat 2) := by
  subst hb
  simp [callFrame, capsState, capsVals, capsTys, SState.pushFrame, SState.pushBind, SState.topIdx, pushBindShaped,
    SState.takeLabel, SState.holderOf, SState.positions, List.range', Attack.S₂, SState.setAt, SP, yFrame, selfP, xB,
    bindsOf, runBinds, mkBind]
  refine ⟨rfl, ?_⟩
  funext p
  by_cases h1 : p = Pos.bind 1 1 <;> by_cases h2 : p = Pos.temp 0 0 <;> simp [h1, h2]

section InPlace
variable (cd d : DeclInfo)

theorem positions_SP (c : Sem) : (SP dm ρ φ cd d c).positions = [.bind 0 0, .temp 0 0, .bind 1 0, .bind 1 1] := by
  simp [SP, yFrame, SState.positions, List.range']

theorem liveLabels_SP (c : Sem) : (SP dm ρ φ cd d c).liveLabels = [0] := by
  unfold SState.liveLabels; rw [positions_SP]; simp [SP]

theorem holderOf_SP (c : Sem) : (SP dm ρ φ cd d c).holderOf 0 = some (.bind 1 1) := by
  unfold SState.holderOf; rw [positions_SP]; simp [SP]

theorem reached_SP (c : Sem) (hit : List Step → Bool) (l : Nat) : (SP dm ρ φ cd d c).reached (.bind 1 1) hit l = false := by
  simp [SState.reached, SP]

theorem access_SP (c : Sem) (hit : List Step → Bool) : (SP dm ρ φ cd d c).access (.bind 1 1) hit = SP dm ρ φ cd d c := by
  unfold SState.access
  have h : ∀ n : Nat, (List.range n).foldl (fun s _ => (s.liveLabels.filter (s.reached (.bind 1 1) hit)).foldl SState.endLabel s)
      (SP dm ρ φ cd d c) = SP dm ρ φ cd d c := by
    intro n; induction n with
    | zero => rfl
    | succ n ih => rw [List.range_succ, List.foldl_append, ih]; simp [liveLabels_SP, reached_SP]
  exact h _

theorem closedFuture_SP (c : Sem) (ψ : Future) : (SP dm ρ φ cd d c).closedFuture ψ = ψ.upd 0 c := by
  unfold SState.closedFuture; rw [liveLabels_SP]
  simp only [List.length_singleton, List.range_one, List.foldl_cons, List.foldl_nil, holderOf_SP]
  rfl

theorem resolve_SP (c : Sem) : resolve (SP dm ρ φ cd d c) (.deref (.var 0)) = some (.bind 1 1, [.deref]) := by
  simp [resolve, SState.varPos, SState.topIdx, Place.steps, SP]

theorem contentOf_SP (c : Sem) :
    ∃ T, contentOf (Kc dm) φ (.deref (.var 0)) (SP dm ρ φ cd d c) = some ((c, T, .bind 1 1, [.deref]), SP dm ρ φ cd d c) := by
  unfold contentOf
  rw [resolve_SP]
  dsimp only
  rw [access_SP, closedFuture_SP]
  simp [Sem.follow, Sem.step, SState.valAt, SState.tyAt, SP, xB]

theorem readPlace_SP (a : Nat) :
    ∃ T, readPlace (Kc dm) φ (.deref (.var 0)) true (SP dm ρ φ cd d (.el0 Nat a))
      = some ((.el0 Nat a, T), SP dm ρ φ cd d (.el0 Nat a)) := by
  obtain ⟨T, hT⟩ := contentOf_SP dm ρ φ cd d (.el0 Nat a)
  refine ⟨{ T with label := none }, ?_⟩
  simp [readPlace, hT, bind, Option.bind, Sem.whole]

theorem setContent_SP (a b : Nat) :
    setContent (Kc dm) φ (.bind 1 1) [.deref] (.el0 Nat b) (SP dm ρ φ cd d (.el0 Nat a)) = some (⟨⟩, SP dm ρ φ cd d (.el0 Nat b)) := by
  simp [setContent, Attack.updAt_deref, Attack.updAt_nil, SState.setAt, SP, xB, SState.valAt]

/-- `*x := S(*x)` run in place, `x` holding `y`'s label: `x` holds `a + 1`. -/
theorem runBody_incP (a : Nat) (hint : TyS) (tl : Bool) :
    runT (Kc dm) ρ φ tl hint incBody (SP dm ρ φ cd d (.el0 Nat a))
      = some ((.el0 Unit (), .plain TyM.unit), SP dm ρ φ cd d (.el0 Nat (a + 1))) := by
  obtain ⟨T, hT⟩ := contentOf_SP dm ρ φ cd d (.el0 Nat a)
  obtain ⟨T', hT'⟩ := readPlace_SP dm ρ φ cd d a
  simp only [incBody, runT, SM.erasedIf, SM.erasedAt, SM.stmtIf, flags_Kc, copy_Kc, hT, hT', Bool.false_eq_true, if_false,
    bind, Option.bind, pure]
  rw [Sem.succ_el0, show (TyS.plain TyM.nat).label = none from rfl]
  simp only [assignAt, resolve_SP, List.isEmpty_cons, Bool.false_and, Bool.false_eq_true, if_false, access_SP,
    setContent_SP]

theorem find_SP (c : Sem) :
    ((SP dm ρ φ cd d c).positions.find? fun p => decide ((SP dm ρ φ cd d c).shape p = some 0)) = some (.bind 1 1) := by
  rw [positions_SP]; simp [SP]

/-- Ending `x`'s label: every position reads as before at the future that fixes `0` to `x`'s content,
`x` itself `moved`. -/
theorem endLabel_SP_valAt (c : Sem) (p : Pos) (ψ : Future) :
    ((SP dm ρ φ cd d c).endLabel 0).valAt p ψ = if p = .bind 1 1 then .moved else (SP dm ρ φ cd d c).valAt p (ψ.upd 0 c) := by
  unfold SState.endLabel
  rw [find_SP]
  dsimp only
  have hx : (SP dm ρ φ cd d c).toMean.val ψ (.bind 1 1) = c := rfl
  rcases p with ⟨f, i⟩ | ⟨f, i⟩
  · rcases f with _ | _ | f <;> rcases i with _ | _ | i <;>
      simp [SState.valAt, SState.mapVals, Mean.semEnd, SState.toMean, SP, yFrame, hx, xB, selfP]
  · rcases f with _ | _ | f <;> rcases i with _ | i <;>
      simp [SState.valAt, SState.mapVals, Mean.semEnd, SState.toMean, SP, yFrame, hx, xB, selfP]

/-- The pop where the only live label is held in the callee's frame and nothing is returned: it ends,
and the frame goes. -/
theorem popCallFrame_one (start : Nat) (s : SState) (l f i : Nat) (hl : s.liveLabels = [l])
    (hh : s.holderOf l = some (.bind f i)) (hf : f = s.topIdx) :
    popCallFrame start none s =
      SState.mk (s.endLabel l).env.dropLast
        (fun p => match p with
          | .bind g _ | .temp g _ => if g = s.topIdx then none else (s.endLabel l).shape p)
        (s.endLabel l).nextLoan (s.endLabel l).lent := by
  unfold popCallFrame
  simp only [hl, List.filter_cons, List.filter_nil, hh, hf, beq_self_eq_true, Bool.or_true, ne_eq, reduceCtorEq,
    not_false_eq_true, decide_true, Bool.and_self, if_true, List.foldl_cons, List.foldl_nil, Option.bind_none]
  congr 1

attribute [local irreducible] SP in
/-- The pop after the body: `x`'s label `0` ends (its holder is in the callee's frame), `y` reads
its final content, the frame goes. -/
theorem popCallFrame_SP (c : Sem) :
    let s' := popCallFrame 1 none (SP dm ρ φ cd d c)
    s'.positions = [.bind 0 0, .temp 0 0] ∧ (∀ ψ, s'.valAt (.bind 0 0) ψ = c) ∧
      (∀ ψ, s'.valAt (.temp 0 0) ψ = .moved) ∧ s'.shape = fun _ => none := by
  have ht : (SP dm ρ φ cd d c).topIdx = 1 := by simp [SState.topIdx, SP]
  have hE : (SP dm ρ φ cd d c).endLabel 0 = (let m := (SP dm ρ φ cd d c).toMean.semEnd (.bind 1 1) 0
      ({ SP dm ρ φ cd d c with shape := m.shape, lent := (SP dm ρ φ cd d c).relend 0 (.bind 1 1) }).mapVals
        fun p _ => (m.val · p)) := by
    unfold SState.endLabel; rw [find_SP]
  dsimp only
  rw [popCallFrame_one 1 _ 0 1 1 (liveLabels_SP dm ρ φ cd d c) (holderOf_SP dm ρ φ cd d c) ht.symm, hE]
  have hx : (SP dm ρ φ cd d c).toMean.val = fun ψ p => (SP dm ρ φ cd d c).valAt p ψ := rfl
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp [SState.positions, SState.mapVals, SP, yFrame, List.range']
  · intro ψ; simp [SState.valAt, SState.mapVals, Mean.semEnd, SState.toMean, SP, yFrame, xB, Future.upd]
  · intro ψ; simp [SState.valAt, SState.mapVals, Mean.semEnd, SState.toMean, SP, yFrame]
  · funext p
    rcases p with ⟨f, i⟩ | ⟨f, i⟩ <;> rcases f with _ | _ | f <;> simp [Mean.semEnd, SState.toMean, SP, SState.mapVals]

end InPlace

/-- **`Inc(&y)` in place** (`CallRef.runCallRef`): `()`, and the state after reads as `callOf`'s
(`SI`): the same positions, `y` reading `3`, the parked borrow consumed, no label held. -/
theorem inc_inPlace :
    ∃ T s', runCallRef (Kc dm) ρ φ (fresInc dm ρ φ) [] incT [] [(.el0 Nat 2, { yB.ty with label := some 0 })]
        (Attack.S₂ yB 0 (.el0 Nat 2)) = some ((.el0 Unit (), T), s') ∧
      s'.positions = [.bind 0 0, .temp 0 0] ∧ (∀ ψ, s'.valAt (.bind 0 0) ψ = .el0 Nat 3) ∧
      (∀ ψ, s'.valAt (.temp 0 0) ψ = .moved) ∧ s'.shape = fun _ => none := by
  have hs₀ : (capsState (capsVals (Kc dm) ρ φ []) (capsTys (Kc dm) ρ φ [])).foldl SState.pushBind
      (Attack.S₂ yB 0 (.el0 Nat 2)).pushFrame = (Attack.S₂ yB 0 (.el0 Nat 2)).pushFrame := by
    simp [capsState, capsVals, capsTys]
  let cd := (Kc dm).D.typeDecl ((Kc dm).D.teleDecls (scopeOf (Attack.S₂ yB 0 (.el0 Nat 2)).pushFrame) [.ref .nat]) .unit
  let d := ((bindsOf (Kc dm) ρ φ (Attack.S₂ yB 0 (.el0 Nat 2)).pushFrame [.ref .nat]).getD 0 (fun _ => .plain TyM.err, .other)).2
  obtain ⟨hp, hv, ht, hsh⟩ := popCallFrame_SP dm ρ φ cd d (.el0 Nat 3)
  refine ⟨{ (TyS.plain TyM.unit) with label := none }, popCallFrame 1 none (SP dm ρ φ cd d (.el0 Nat 3)), ?_,
    hp, hv, ht, hsh⟩
  unfold runCallRef runBodyRef
  simp only [incT, hs₀, codOf_inc]
  rw [callFrame_inc dm ρ φ _ _ rfl, runBody_incP]
  rfl

/-- **`Inc(&y)`: the call by `callOf` and the call in place agree** (`callOf_inPlace` on a borrow
parameter): both give `()`, and the states after have the same positions, the same meaning at each
(`y` reads `3`, the parked borrow `moved`) and no label held. -/
theorem inc_agree :
    ∃ TU T s', callOf dm.read (fresInc dm ρ φ) [(.el0 Nat 2, { yB.ty with label := some 0 })] (Attack.S₂ yB 0 (.el0 Nat 2))
        = some ((.el0 Unit (), TU), SI) ∧
      runCallRef (Kc dm) ρ φ (fresInc dm ρ φ) [] incT [] [(.el0 Nat 2, { yB.ty with label := some 0 })]
        (Attack.S₂ yB 0 (.el0 Nat 2)) = some ((.el0 Unit (), T), s') ∧
      s'.positions = SI.positions ∧ (∀ p ψ, p ∈ SI.positions → s'.valAt p ψ = SI.valAt p ψ) ∧ s'.shape = SI.shape := by
  obtain ⟨TU, -, hc⟩ := callOf_inc dm ρ φ (Attack.S₂ yB 0 (.el0 Nat 2)) yB.ty 0
  obtain ⟨T, s', hr, hp, hv, ht, hsh⟩ := inc_inPlace dm ρ φ
  have hpSI : SI.positions = [.bind 0 0, .temp 0 0] := by
    simp [SI, SState.mapVals, Attack.takeLabel_S₂, SState.positions, List.range']
  refine ⟨TU, T, s', hc, hr, by rw [hp, hpSI], fun p ψ hp' => ?_, by rw [hsh, SI_shape]⟩
  rw [hpSI] at hp'
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp'
  rcases hp' with rfl | rfl
  · rw [hv]; simp [SI, SState.mapVals, Attack.takeLabel_S₂, SState.valAt, Future.updList, Future.upd]
  · rw [ht]; simp [SI, SState.mapVals, Attack.takeLabel_S₂, SState.valAt]

end Ochr.Meaning.Regress.CallInPlace
