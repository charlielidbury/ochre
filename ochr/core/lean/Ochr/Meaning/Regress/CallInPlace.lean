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
open Classical

/-- `Inc (x : &Nat) : Unit := *x := S(*x)`'s body, `x` its innermost binding. -/
def incBody : Term := .assign (.deref (.var 0)) (.succ (.place (.deref (.var 0))))
/-- `Inc`'s term, and its closure (no captures). -/
def incT : Term := .fix ⟨"Inc"⟩ [⟨"x"⟩] [.ref .nat] .unit none incBody
def incClo : Value := .clo [] incT []

/-- The context: no inductive, no global, the probes' decisions. -/
def Kc (dm : DataModel) : RunCtx := Kp dm [] (fun _ => (.err, .plain TyM.err))

variable (dm : DataModel) (ρ : Assignment) (φ : Future) {r : Sem}

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

/-- `Inc`'s function (`Run.lean`'s `.fix` clause, named in `RunCongr`): no decreasing parameter, so
stage `1` at rank `0`, `self` the weakened stage `0` (docs/31 D113). -/
noncomputable def gInc : List Sem → Option BodyOut :=
  fixG (Kc dm) ρ φ (fbInc dm ρ φ) 1 (stateOf 0 []) psInc outInc (piInc dm) 0 none incBody

/-- `self`'s type and meaning in `Inc`'s frame: stage `0` at the weakened function type (never read). -/
noncomputable def selfIncT : TyM := piTyAt dm.read 1 psInc (weakCod 1 (fixRank none) 0 outInc)
noncomputable def selfIncM : Sem := closureAt dm.read 1 φ psInc (weakCod 1 (fixRank none) 0 outInc)
  (stageFn 1 psInc (fixRank none) 0 (fixStage (Kc dm) ρ φ (fbInc dm ρ φ) 1 (stateOf 0 []) psInc outInc none 0 incBody 0))

/-! ## `Inc`'s body run in its own frame -/

/-- `self`'s binding in `Inc`'s frame (`Inc` does not recurse: stage `0`, never read). -/
noncomputable def selfInc : SBinding := { ty := .plain (selfIncT dm), val := fun _ => selfIncM dm ρ φ, decl := .pi (fbInc dm ρ φ).2.2 }

/-- The parameter's declared reading, as the clause reads it. -/
noncomputable def dInc : DeclInfo := ((Kc dm).D.paramDecls [] [.ref .nat]).getD 0 .other

/-- `x`'s binding: the borrowed content `c`, holder of the fresh label `0`. -/
def xB (c : Sem) (d : DeclInfo) : SBinding := { ty := { (TyS.plain TyM.nat) with label := some 0 }, val := fun _ => c, decl := d }

/-- `Inc`'s frame: `self`, `x` holding `c` at label `0`, and `x`'s cell reading `0`'s final content. -/
noncomputable def SB (c r : Sem) : SState :=
  { env := [{ binds := [selfInc dm ρ φ, xB c (dInc dm)], temps := [fun ψ => ψ 0] }],
    shape := fun p => if p = .bind 0 1 then some 0 else none, nextLoan := 1,
    heldTy := fun m => if m = 0 then TyM.nat else TyM.err,
    heldMem := fun m => if m = 0 then r else .err }

theorem frame_inc (c : Sem) :
    ([c].zip psInc).foldl (fixStep (fbInc dm ρ φ)) ((stateOf 0 []).pushBind (selfInc dm ρ φ), [], [])
      = (SB dm ρ φ c c, [c], [.temp 0 0]) := by
  simp [fixStep, psInc, stateOf, SState.freshLoan, SState.pushTemp, SState.pushBind, SState.topIdx, pushBindShaped,
    SState.takeLabel, SState.holderOf, SState.positions, SB, xB, dInc, fbInc, bindsOf, runBinds, mkBind, SState.setHeldMem,
    SState.setHeldTy]
  exact ⟨⟨rfl, rfl⟩, rfl⟩

theorem positions_SB (c : Sem) : (SB dm ρ φ c r).positions = [.bind 0 0, .bind 0 1, .temp 0 0] := by
  simp [SB, SState.positions, List.range']

theorem liveLabels_SB (c : Sem) : (SB dm ρ φ c r).liveLabels = [0] := by
  unfold SState.liveLabels; rw [positions_SB]; simp [SB]

theorem holderOf_SB (c : Sem) : (SB dm ρ φ c r).holderOf 0 = some (.bind 0 1) := by
  unfold SState.holderOf; rw [positions_SB]; simp [SB]

theorem reached_SB (c : Sem) (p : Pos) (hit : List Step → Bool) (l : Nat) : (SB dm ρ φ c r).reached p hit l = false := by
  simp [SState.reached, SB]

theorem access_SB (c : Sem) (p : Pos) (hit : List Step → Bool) : (SB dm ρ φ c r).access p hit = SB dm ρ φ c r := by
  unfold SState.access
  have h : ∀ n : Nat, (List.range n).foldl (fun s _ => (s.liveLabels.filter (s.reached p hit)).foldl SState.endLabel s)
      (SB dm ρ φ c r) = SB dm ρ φ c r := by
    intro n; induction n with
    | zero => rfl
    | succ n ih => rw [List.range_succ, List.foldl_append, ih]; simp [liveLabels_SB, reached_SB]
  exact h _

theorem typedFuture_SB (c : Sem) (ψ : Future) : (SB dm ρ φ c r).typedFuture ψ = ψ.upd 0 r := by
  funext l; unfold SState.typedFuture; rw [liveLabels_SB]
  by_cases hl : l = 0 <;> simp [hl, SB, Future.upd]

theorem resolve_SB (c : Sem) : resolve (SB dm ρ φ c r) (.deref (.var 0)) = some (.bind 0 1, [.deref]) := by
  simp [resolve, SState.varPos, SState.topIdx, Place.steps, SB]

/-- `*x` in `Inc`'s frame: `x`'s content, at `x`'s position through `*`; the state unchanged. -/
theorem contentOf_SB (c : Sem) :
    ∃ T, contentOf (Kc dm) φ (.deref (.var 0)) (SB dm ρ φ c r) = some ((c, T, .bind 0 1, [.deref]), SB dm ρ φ c r) := by
  unfold contentOf
  rw [resolve_SB]
  dsimp only
  rw [access_SB, typedFuture_SB]
  simp [Sem.follow, Sem.step, SState.valAt, SState.tyAt, SB, xB]

/-- `*x`'s type in `Inc`'s frame is `Nat`. -/
theorem contentOf_SB_nat (c : Sem) :
    ∃ T : TyS, T.m = TyM.nat ∧
      contentOf (Kc dm) φ (.deref (.var 0)) (SB dm ρ φ c r) = some ((c, T, .bind 0 1, [.deref]), SB dm ρ φ c r) := by
  unfold contentOf
  rw [resolve_SB]
  dsimp only
  rw [access_SB, typedFuture_SB]
  simp [Sem.follow, Sem.step, SState.valAt, SState.tyAt, SB, xB, TyS.plain]

theorem flags_Kc (sc : List DeclInfo) (t : Term) : (Kc dm).D.flags sc t = (false, false) := rfl
theorem copy_Kc (r : DeclInfo) : (Kc dm).D.copy r = true := rfl

theorem readPlace_SB (a : Nat) :
    ∃ T, readPlace (Kc dm) φ (.deref (.var 0)) true (SB dm ρ φ (.el0 Nat a) r)
      = some ((.el0 Nat a, T), SB dm ρ φ (.el0 Nat a) r) := by
  obtain ⟨T, hTm, hT⟩ := contentOf_SB_nat (r := r) dm ρ φ (.el0 Nat a)
  have hg : ReadGood (Kc dm).dm.read T.m (.el0 Nat a) := Or.inl (by rw [hTm]; exact ⟨a, rfl⟩)
  refine ⟨{ T with label := none }, ?_⟩
  simp [readPlace, hT, hg, bind, Option.bind, Sem.whole]

theorem setContent_SB (a b : Nat) :
    setContent (Kc dm) φ (.bind 0 1) [.deref] (.el0 Nat b) (SB dm ρ φ (.el0 Nat a) r) = some (⟨⟩, SB dm ρ φ (.el0 Nat b) r) := by
  simp [setContent, Attack.updAt_deref, Attack.updAt_nil, SState.setAt, SB, xB, SState.valAt]

theorem lentOk_SB (c : Sem) : lentOk (Kc dm) φ (.deref (.var 0)) (SB dm ρ φ c r) := by
  unfold lentOk; rw [resolve_SB]; exact .inr (.inl rfl)

theorem contentOk_SB (c : Sem) : ContentOk (Kc dm) φ (.deref (.var 0)) (SB dm ρ φ c r) := by
  unfold ContentOk; rw [resolve_SB]
  exact Attack.accessOk_unreached _ φ fun l => reached_SB dm ρ φ c _ _ l

theorem assignOk_SB (c : Sem) : AssignOk (Kc dm) φ (.deref (.var 0)) (SB dm ρ φ c r) := by
  unfold AssignOk; rw [resolve_SB]
  exact ⟨fun _ => Attack.accessOk_unreached _ φ fun l => reached_SB dm ρ φ c _ _ l, fun h => by simp at h⟩

theorem holderOf_SB' (c : Sem) : (SB dm ρ φ c r).holderOf 0 = some (.bind 0 1) := holderOf_SB dm ρ φ c

/-- Ending `x`'s label at the pop is strict: `x` holds the number `c`. -/
theorem endsOk_SB (c : Sem) (hc : c ∈ₛ[(Kc dm).dm.read] TyM.nat) : EndsOk (Kc dm) φ [0] (SB dm ρ φ c r) := by
  refine ⟨?_, trivial⟩
  intro q hq ψ _
  rw [holderOf_SB] at hq
  cases hq
  exact hc

/-- `*x := S(*x)` in `Inc`'s frame: `x` holds `a + 1`. -/
theorem runBody_inc (a : Nat) (hint : TyS) (tl : Bool) :
    runT (Kc dm) ρ φ tl hint incBody (SB dm ρ φ (.el0 Nat a) r) = some ((.el0 Unit (), .plain TyM.unit), SB dm ρ φ (.el0 Nat (a + 1)) r) := by
  obtain ⟨T, hTm, hT⟩ := contentOf_SB_nat (r := r) dm ρ φ (.el0 Nat a)
  obtain ⟨T', hT'⟩ := readPlace_SB (r := r) dm ρ φ a
  have hs : (Sem.el0 Nat a).succ = .el0 Nat (a + 1) := Sem.succ_el0 a
  simp only [incBody, runT, SM.erasedIf, SM.stmtIf, flags_Kc, copy_Kc, hT, SM.guarded_of (contentOk_SB dm ρ φ (r := r) (.el0 Nat a)), hT', Bool.false_eq_true, if_false,
    bind, Option.bind, pure, SM.strictS, hs]
  -- the strict `S` and the strict write: `a + 1` is a `Nat`, `*x`'s type
  have hm : Sem.el0 Nat (a + 1) ∈ₛ[(Kc dm).dm.read] TyM.nat := ⟨a + 1, rfl⟩
  simp only [hm, if_true, placeTy, hT, hTm, labTyOk, TyS.plain, reduceCtorEq, false_implies, implies_true,
    and_true]
  simp only [SM.guarded_of (assignOk_SB dm ρ φ (r := r) (.el0 Nat a)), assignAt, resolve_SB, List.isEmpty_cons, Bool.false_and, Bool.false_eq_true, if_false, access_SB,
    setContent_SB]
  simp only [Attack.invalidate_noInv (Kc dm) φ (fun _ _ => rfl), Attack.invalidateOk_noInv (Kc dm) φ (fun _ _ => rfl), lentOk_SB, and_self, if_true]
  rfl

/-- Ending `x`'s label at the pop: the cell reads the content. -/
theorem endLabel_SB_cell (c : Sem) (ψ : Future) : ((SB dm ρ φ c r).endLabel 0).valAt (.temp 0 0) ψ = c := by
  unfold SState.endLabel
  rw [positions_SB]
  simp [SB, SState.mapVals, SState.valAt, Mean.semEnd, SState.toMean, Future.upd]
  rfl

/-- **`Inc`'s body run at `a`**: `()`, and `x`'s final content `a + 1`. -/
theorem gInc_eval (a : Nat) :
    gInc dm ρ φ [.el0 Nat a] = some ⟨.el0 Unit (), [fun _ => .el0 Nat (a + 1)], none⟩ := by
  show fixBodyAt (Kc dm) ρ φ (fbInc dm ρ φ) (stateOf 0 []) psInc outInc (selfIncT dm) 0 incBody (selfIncM dm ρ φ)
    [.el0 Nat a] = _
  unfold fixBodyAt
  rw [show ({ ty := .plain (selfIncT dm), val := fun _ => selfIncM dm ρ φ, decl := .pi (fbInc dm ρ φ).2.2 } : SBinding)
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
  rw [if_pos (endsOk_SB dm ρ φ (Sem.el0 Nat (a + 1)) ⟨a + 1, rfl⟩)]
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

/-- A level-0 closure whose telescope is built is not `err`. -/
theorem closureL0_ne_err {C : Type} (t : Tel Code0 PUnit C) (g : List Sem → Option BodyOut)
    (h : (mkTelL (lvl0 dm.read) φ t [] (fun fs => some (PUnit.unit, fs)) g).isSome) :
    closureL (lvl0 dm.read) φ t g ≠ .err := by
  unfold closureL
  obtain ⟨F, hF⟩ := Option.isSome_iff_exists.mp h
  rw [hF]
  intro h; cases h

/-- **`Inc`'s term runs to the closure of its body run**, at its code: the strict `.fix` clause's
test passes, the closure being built (`mkTel_inc`), so a member of its type (`closureL_mem`). -/
theorem run_incT : ∃ s', runT (Kc dm) ρ φ false (.plain .err) incT (stateOf 0 (capsState [] []))
    = some ((closureAt dm.read 1 φ psInc outInc (gInc dm ρ φ), .plain (piInc dm)), s') := by
  have hmem : closureAt dm.read 1 φ psInc outInc (gInc dm ρ φ) ∈ₛ[dm.read] piTyAt dm.read 1 psInc outInc :=
    (closureL_mem (lvl0 dm.read) (lvl0_lawful dm.read) φ _ _).resolve_right (closureL0_ne_err dm φ _ _ (mkTel_inc dm ρ φ))
  refine ⟨fixMoves (Kc dm) incT (stateOf 0 (capsState [] [])), ?_⟩
  rw [incT, run_fix_def]
  simp only [SM.erasedIf, SM.stmtIf, flags_Kc, Bool.false_eq_true, if_false, SM.strictS]
  have hco : capOrder incT = [] := by decide
  have hc : FoldOk (capStep (Kc dm)) (CapOk (Kc dm) φ) (capOrder incT) (stateOf 0 (capsState [] [])) := by
    rw [hco]; trivial
  erw [if_pos hc]
  rw [if_pos (by exact hmem)]
  rfl

open Classical in
/-- **`Inc`'s closure means the closure of its body run**, at its code. -/
theorem meanV_incClo (hint : TyS) :
    meanV (Kc dm) ρ φ hint incClo = closureAt dm.read 1 φ psInc outInc (gInc dm ρ φ) := by
  obtain ⟨s', h⟩ := run_incT dm ρ φ
  -- the strict closure: no captures, so `CapsOk` holds
  show (if CapsOk (Kc dm).dm.read [] [] then (match runT (Kc dm) ρ φ false (.plain .err) incT (stateOf 0 (capsState [] [])) with
    | some ((v, _), _) => v | none => .err) else .err) = _
  rw [if_pos (show CapsOk (Kc dm).dm.read [] [] from trivial), h]

/-- `Inc`'s closure is typed at its code. -/
theorem valT_incClo (hint : TyS) : valT (Kc dm) ρ φ hint incClo = .plain (piInc dm) := by
  obtain ⟨s', h⟩ := run_incT dm ρ φ
  show (match runT (Kc dm) ρ φ false (.plain TyM.err) incT (stateOf 0 (capsState [] [])) with
    | some ((_, R), _) => R | none => hint) = _
  rw [h]

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

/-- The strict call's test for `Inc(&y)`: the borrow passed at `Inc`'s borrow parameter is live and
holds `Nat`, the parameter's content type. -/
theorem borrowArgs_psInc (out : PiCod) (F : Sem) (b : SBinding) (hb : b.ty.m = TyM.nat) :
    BorrowArgsTyped dm.read (F, .plain (piTyAt dm.read 1 psInc out))
      [(.el0 Nat 2, { b.ty with label := some 0 })] (Attack.S₂ b 0 (.el0 Nat 2)) := by
  have hd : Code0.dec dm.read TyM.nat.code0.snd (Sem.el0 Nat 2) = some (2 : Nat) := Attack.dec_nat_el0 dm.read 2
  have hr : telRefsL (lvl0 dm.read) (telL (lvl0 dm.read) psInc [] PUnit out).2 [Sem.el0 Nat 2] = [true] := by
    simp [telRefsL, telL, psInc, hd]
    split <;> rfl
  intro i l h
  simp only [refLabelsOf, refsOf, piTyAt, piTyL, TyS.plain, List.map_cons, List.map_nil] at h
  cases i with
  | succ i => simp [hr] at h
  | zero =>
    simp [hr] at h
    subst h
    refine ⟨?_, ?_⟩
    · simp only [SState.liveLabels, List.mem_mergeSort, List.mem_filterMap]
      exact ⟨.temp 0 0, by rw [Attack.positions_S₂]; simp, by simp [Attack.S₂]⟩
    · simp [refTysOf, piTyAt, piTyL, telRefTysL, telL, psInc, TyS.plain, hd, Attack.S₂, hb]
      rfl

/-- `Inc`'s closure as a call's head: its meaning, at its code. -/
theorem run_incClo (hint : TyS) (s : SState) :
    run (Kc dm) ρ φ hint (.val incClo) s = some ((closureAt dm.read 1 φ psInc outInc (gInc dm ρ φ), .plain (piInc dm)), s) := by
  rw [run_val_def, meanV_incClo, valT_incClo]
  -- the strict `.val`: the closure is built, so not `err`
  simp only [incClo, strictVal]
  rw [if_neg (show closureAt dm.read 1 φ psInc outInc (gInc dm ρ φ) ≠ .err from
    closureL0_ne_err dm φ _ _ (mkTel_inc dm ρ φ))]
  congr

/-- `y`'s binding: `2`, at `Nat` (the run types an embedded number at `Nat`). -/
def yB : SBinding := { ty := TyS.plain TyM.nat, val := fun _ => .el0 Nat 2, decl := .other }

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
    simp only [SM.erasedIf, flags_Kc, Bool.false_eq_true, if_false, SM.stmtIf, SM.strictS]
    erw [SM.guarded_of (Attack.contentOk_one _ _ _ _)]
    rw [Attack.borrowPlace_var0_one _ _ _ _ (by simp [yB, Sem.whole])]
    dsimp only
    rw [if_pos (by exact ⟨(2 : Nat), rfl⟩)]
    dsimp only
    erw [Attack.invalidate_noInv (Kc dm) φ (fun _ _ => rfl)]
    erw [if_pos ⟨Attack.invalidateOk_noInv (Kc dm) φ (fun _ _ => rfl) _ _, Attack.lentOk_root (Kc dm) φ (pos := .bind 0 0) rfl⟩]
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
  have hcf : SI.typedFuture φ = φ := by funext l; simp [SState.typedFuture, hl]
  have hr : resolve SI (.var 0) = some (.bind 0 0, []) := by
    simp [resolve, SState.varPos, SState.topIdx, Place.steps, SI, SState.mapVals, Attack.takeLabel_S₂]
  have hv : SI.valAt (.bind 0 0) φ = .el0 Nat 3 := by
    simp [SI, SState.mapVals, Attack.takeLabel_S₂, SState.valAt, Future.updList, Future.upd]
  have hg : ReadGood (Kc dm).dm.read (SI.tyAt (.bind 0 0)).m (Sem.el0 Nat 3) := Or.inl (by
    have ht : (SI.tyAt (.bind 0 0)).m = TyM.nat := by
      simp only [SI, Attack.takeLabel_S₂]
      simp [SState.mapVals, SState.tyAt, Attack.S₂, yB, TyS.plain]
    rw [ht]; exact ⟨(3 : Nat), rfl⟩)
  obtain ⟨T, hT⟩ : ∃ T, SI.tyAt (.bind 0 0) = T := ⟨_, rfl⟩
  rw [hT] at hg
  refine ⟨{ T with label := none }, ?_⟩
  simp only [readPlace, contentOf, hr, Attack.access_noShape SI SI_shape, hcf, Sem.follow, hv, hT, bind, Option.bind]
  simp [Sem.whole, hg]

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
    rw [if_pos (by exact borrowArgs_psInc dm outInc _ yB rfl)]
    exact hc
  have hd : discardEnd TU SI = SI := by simp [discardEnd, hTU]
  have hdo : SM.guardMod (DiscardOk (Kc dm) φ TU) (discardEnd TU) SI = some (⟨⟩, SI) := by
    have : DiscardOk (Kc dm) φ TU SI := by unfold DiscardOk; rw [hTU]; trivial
    unfold SM.guardMod; rw [if_pos this, hd]
  have hcok : ContentOk (Kc dm) φ (.var 0) SI := by
    unfold ContentOk; split
    · exact Attack.accessOk_noLive _ φ (Attack.liveLabels_of_noShape SI SI_shape) _ _
    · trivial
  have hseq : run (Kc dm) ρ φ hint (.seq (.call (.val incClo) [.borrow (.var 0)] false) (.place (.var 0)))
      ((emptyState 0).pushBind yB) = some ((.el0 Nat 3, Ty), SI) := by
    show runT (Kc dm) ρ φ false hint _ _ = _
    rw [runT]
    simp only [SM.erasedIf, flags_Kc, Bool.false_eq_true, if_false, SM.stmtIf]
    show (do let r ← run (Kc dm) ρ φ (.plain .err) _; SM.guardMod (DiscardOk (Kc dm) φ r.2) (discardEnd r.2); runT (Kc dm) ρ φ false hint (.place (.var 0))) _ = _
    simp only [bind, Option.bind, hcall, hdo]
    rw [runT]
    simp only [SM.erasedIf, flags_Kc, copy_Kc, Bool.false_eq_true, if_false, SM.stmtIf, SM.guarded_of hcok]
    exact hy
  refine ⟨Ty, ?_⟩
  rw [useIncT, show Kc dm = Kp dm [] (fun _ => (.err, .plain TyM.err)) from rfl, run_letIn, run_num]
  rw [show Kp dm [] (fun _ => (.err, .plain TyM.err)) = Kc dm from rfl]
  simp only [bind, Option.bind]
  rw [Attack.pushBindShaped_noLabel _ _ rfl]
  rw [show ({ ty := TyS.plain TyM.nat, val := fun _ => .el0 Nat 2, decl := .other } : SBinding)
    = yB from rfl, hseq]
  simp only [Option.bind_some]
  erw [if_pos (Attack.letGuard_noShape (Kc dm) φ SI SI_shape)]
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
noncomputable def SP (cd d : DeclInfo) (c r : Sem) : SState :=
  { env := [yFrame, { binds := [selfP dm ρ φ cd, xB c d] }],
    shape := fun p => if p = .bind 1 1 then some 0 else none, nextLoan := 1,
    lent := fun m => if m = 0 then [⟨.bind 0 0, [], false⟩] else [],
    heldTy := fun m => if m = 0 then yB.ty.m else TyM.err,
    heldMem := fun m => if m = 0 then r else .err }

theorem callFrame_inc (cd : DeclInfo) (bs : List PBind) (hb : bs = bindsOf (Kc dm) ρ φ (Attack.S₂ yB 0 (.el0 Nat 2)).pushFrame [.ref .nat]) :
    callFrame (Kc dm) ρ φ [] [] (fresInc dm ρ φ) cd bs [(.el0 Nat 2, { yB.ty with label := some 0 })] (Attack.S₂ yB 0 (.el0 Nat 2))
      = SP dm ρ φ cd ((bs.getD 0 (fun _ => .plain TyM.err, .other)).2) (.el0 Nat 2) (.el0 Nat 2) := by
  subst hb
  simp [callFrame, capsState, capsVals, capsTys, SState.pushFrame, SState.pushBind, SState.topIdx, pushBindShaped,
    SState.takeLabel, SState.holderOf, SState.positions, List.range', Attack.S₂, SState.setAt, SP, yFrame, selfP, xB,
    bindsOf, runBinds, mkBind]
  refine ⟨rfl, ?_⟩
  funext p
  by_cases h1 : p = Pos.bind 1 1 <;> by_cases h2 : p = Pos.temp 0 0 <;> simp [h1, h2]

section InPlace
variable (cd d : DeclInfo)

theorem positions_SP (c : Sem) : (SP dm ρ φ cd d c r).positions = [.bind 0 0, .temp 0 0, .bind 1 0, .bind 1 1] := by
  simp [SP, yFrame, SState.positions, List.range']

theorem liveLabels_SP (c : Sem) : (SP dm ρ φ cd d c r).liveLabels = [0] := by
  unfold SState.liveLabels; rw [positions_SP]; simp [SP]

theorem holderOf_SP (c : Sem) : (SP dm ρ φ cd d c r).holderOf 0 = some (.bind 1 1) := by
  unfold SState.holderOf; rw [positions_SP]; simp [SP]

theorem reached_SP (c : Sem) (hit : List Step → Bool) (l : Nat) : (SP dm ρ φ cd d c r).reached (.bind 1 1) hit l = false := by
  simp [SState.reached, SP]

theorem access_SP (c : Sem) (hit : List Step → Bool) : (SP dm ρ φ cd d c r).access (.bind 1 1) hit = SP dm ρ φ cd d c r := by
  unfold SState.access
  have h : ∀ n : Nat, (List.range n).foldl (fun s _ => (s.liveLabels.filter (s.reached (.bind 1 1) hit)).foldl SState.endLabel s)
      (SP dm ρ φ cd d c r) = SP dm ρ φ cd d c r := by
    intro n; induction n with
    | zero => rfl
    | succ n ih => rw [List.range_succ, List.foldl_append, ih]; simp [liveLabels_SP, reached_SP]
  exact h _

theorem typedFuture_SP (c : Sem) (ψ : Future) : (SP dm ρ φ cd d c r).typedFuture ψ = ψ.upd 0 r := by
  funext l; unfold SState.typedFuture; rw [liveLabels_SP]
  by_cases hl : l = 0 <;> simp [hl, SP, Future.upd]

theorem resolve_SP (c : Sem) : resolve (SP dm ρ φ cd d c r) (.deref (.var 0)) = some (.bind 1 1, [.deref]) := by
  simp [resolve, SState.varPos, SState.topIdx, Place.steps, SP]

theorem contentOf_SP (c : Sem) :
    ∃ T, contentOf (Kc dm) φ (.deref (.var 0)) (SP dm ρ φ cd d c r) = some ((c, T, .bind 1 1, [.deref]), SP dm ρ φ cd d c r) := by
  unfold contentOf
  rw [resolve_SP]
  dsimp only
  rw [access_SP, typedFuture_SP]
  simp [Sem.follow, Sem.step, SState.valAt, SState.tyAt, SP, xB]

theorem contentOf_SP_nat (c : Sem) :
    ∃ T : TyS, T.m = TyM.nat ∧
      contentOf (Kc dm) φ (.deref (.var 0)) (SP dm ρ φ cd d c r) = some ((c, T, .bind 1 1, [.deref]), SP dm ρ φ cd d c r) := by
  unfold contentOf
  rw [resolve_SP]
  dsimp only
  rw [access_SP, typedFuture_SP]
  simp [Sem.follow, Sem.step, SState.valAt, SState.tyAt, SP, xB, TyS.plain]

theorem readPlace_SP (a : Nat) :
    ∃ T, readPlace (Kc dm) φ (.deref (.var 0)) true (SP dm ρ φ cd d (.el0 Nat a) r)
      = some ((.el0 Nat a, T), SP dm ρ φ cd d (.el0 Nat a) r) := by
  obtain ⟨T, hTm, hT⟩ := contentOf_SP_nat (r := r) dm ρ φ cd d (.el0 Nat a)
  have hg : ReadGood (Kc dm).dm.read T.m (.el0 Nat a) := Or.inl (by rw [hTm]; exact ⟨a, rfl⟩)
  refine ⟨{ T with label := none }, ?_⟩
  simp [readPlace, hT, hg, bind, Option.bind, Sem.whole]

theorem setContent_SP (a b : Nat) :
    setContent (Kc dm) φ (.bind 1 1) [.deref] (.el0 Nat b) (SP dm ρ φ cd d (.el0 Nat a) r) = some (⟨⟩, SP dm ρ φ cd d (.el0 Nat b) r) := by
  simp [setContent, Attack.updAt_deref, Attack.updAt_nil, SState.setAt, SP, xB, SState.valAt]

theorem lentOk_SP (c : Sem) : lentOk (Kc dm) φ (.deref (.var 0)) (SP dm ρ φ cd d c r) := by
  unfold lentOk; rw [resolve_SP]; exact .inr (.inl rfl)

theorem contentOk_SP (c : Sem) : ContentOk (Kc dm) φ (.deref (.var 0)) (SP dm ρ φ cd d c r) := by
  unfold ContentOk; rw [resolve_SP]
  exact Attack.accessOk_unreached _ φ fun l => reached_SP dm ρ φ cd d c _ l

theorem assignOk_SP (c : Sem) : AssignOk (Kc dm) φ (.deref (.var 0)) (SP dm ρ φ cd d c r) := by
  unfold AssignOk; rw [resolve_SP]
  exact ⟨fun _ => Attack.accessOk_unreached _ φ fun l => reached_SP dm ρ φ cd d c _ l, fun h => by simp at h⟩

/-- `*x := S(*x)` run in place, `x` holding `y`'s label: `x` holds `a + 1`. -/
theorem runBody_incP (a : Nat) (hint : TyS) (tl : Bool) :
    runT (Kc dm) ρ φ tl hint incBody (SP dm ρ φ cd d (.el0 Nat a) r)
      = some ((.el0 Unit (), .plain TyM.unit), SP dm ρ φ cd d (.el0 Nat (a + 1)) r) := by
  obtain ⟨T, hTm, hT⟩ := contentOf_SP_nat (r := r) dm ρ φ cd d (.el0 Nat a)
  obtain ⟨T', hT'⟩ := readPlace_SP (r := r) dm ρ φ cd d a
  have hs : (Sem.el0 Nat a).succ = .el0 Nat (a + 1) := Sem.succ_el0 a
  simp only [incBody, runT, SM.erasedIf, SM.stmtIf, flags_Kc, copy_Kc, SM.guarded_of (contentOk_SP dm ρ φ cd d (r := r) (.el0 Nat a)), hT', Bool.false_eq_true, if_false,
    bind, Option.bind, pure, SM.strictS, hs]
  -- the strict `S` and the strict write: `a + 1` is a `Nat`, `*x`'s type
  have hm : Sem.el0 Nat (a + 1) ∈ₛ[(Kc dm).dm.read] TyM.nat := ⟨a + 1, rfl⟩
  simp only [hm, if_true, placeTy, hT, hTm, labTyOk, TyS.plain, reduceCtorEq, false_implies, implies_true,
    and_true]
  simp only [SM.guarded_of (assignOk_SP dm ρ φ cd d (r := r) (.el0 Nat a)), assignAt, resolve_SP, List.isEmpty_cons, Bool.false_and, Bool.false_eq_true, if_false, access_SP,
    setContent_SP]
  simp only [Attack.invalidate_noInv (Kc dm) φ (fun _ _ => rfl), Attack.invalidateOk_noInv (Kc dm) φ (fun _ _ => rfl), lentOk_SP, and_self, if_true]
  rfl

theorem find_SP (c : Sem) :
    ((SP dm ρ φ cd d c r).positions.find? fun p => decide ((SP dm ρ φ cd d c r).shape p = some 0)) = some (.bind 1 1) := by
  rw [positions_SP]; simp [SP]

/-- Ending `x`'s label: every position reads as before at the future that fixes `0` to `x`'s content,
`x` itself `moved`. -/
theorem endLabel_SP_valAt (c : Sem) (p : Pos) (ψ : Future) :
    ((SP dm ρ φ cd d c r).endLabel 0).valAt p ψ = if p = .bind 1 1 then .moved else (SP dm ρ φ cd d c r).valAt p (ψ.upd 0 c) := by
  unfold SState.endLabel
  rw [find_SP]
  dsimp only
  have hx : (SP dm ρ φ cd d c r).toMean.val ψ (.bind 1 1) = c := rfl
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
        (s.endLabel l).nextLoan (s.endLabel l).lent (s.endLabel l).heldTy (s.endLabel l).heldMem := by
  unfold popCallFrame popEnds
  simp only [hl, List.filter_cons, List.filter_nil, hh, hf, beq_self_eq_true, Bool.or_true, ne_eq, reduceCtorEq,
    not_false_eq_true, decide_true, Bool.and_self, if_true, List.foldl_cons, List.foldl_nil, Option.bind_none]
  congr 1

/-- The pop's ends where the only live label is held in the callee's frame and nothing is returned. -/
theorem popEnds_one (start : Nat) (s : SState) (l f i : Nat) (hl : s.liveLabels = [l])
    (hh : s.holderOf l = some (.bind f i)) (hf : f = s.topIdx) : popEnds start none s = [l] := by
  unfold popEnds
  simp [hl, hh, hf]

/-- The pop's ends where two labels are live: `l`, held in the callee's frame, and `k`, returned. -/
theorem popEnds_two (start : Nat) (s : SState) (l k f i : Nat) (hl : s.liveLabels = [l, k])
    (hh : s.holderOf l = some (.bind f i)) (hf : f = s.topIdx) (hlk : l ≠ k) : popEnds start (some k) s = [l] := by
  unfold popEnds
  have hne : (some l ≠ some k) := fun h => hlk (Option.some.inj h)
  simp only [hl, List.filter_cons, List.filter_nil, hh, hf, beq_self_eq_true, Bool.or_true, ne_eq, hne,
    not_false_eq_true, decide_true, Bool.and_self, if_true, not_true_eq_false, decide_false, Bool.and_false,
    Bool.false_eq_true, if_false]

/-- The pop's end of `x`'s label is strict: `x` holds the number `c`. -/
theorem endsOk_SP (cd d : DeclInfo) (c : Sem) (hc : c ∈ₛ[(Kc dm).dm.read] TyM.nat) :
    EndsOk (Kc dm) φ [0] (SP dm ρ φ cd d c r) := by
  refine ⟨?_, trivial⟩
  intro q hq ψ _
  rw [holderOf_SP] at hq
  cases hq
  exact hc

attribute [local irreducible] SP in
/-- The pop after the body: `x`'s label `0` ends (its holder is in the callee's frame), `y` reads
its final content, the frame goes. -/
theorem popCallFrame_SP (c : Sem) :
    let s' := popCallFrame 1 none (SP dm ρ φ cd d c r)
    s'.positions = [.bind 0 0, .temp 0 0] ∧ (∀ ψ, s'.valAt (.bind 0 0) ψ = c) ∧
      (∀ ψ, s'.valAt (.temp 0 0) ψ = .moved) ∧ s'.shape = fun _ => none := by
  have ht : (SP dm ρ φ cd d c r).topIdx = 1 := by simp [SState.topIdx, SP]
  have hE : (SP dm ρ φ cd d c r).endLabel 0 = (let m := (SP dm ρ φ cd d c r).toMean.semEnd (.bind 1 1) 0
      ({ SP dm ρ φ cd d c r with shape := m.shape, lent := (SP dm ρ φ cd d c r).relend 0 (.bind 1 1) }).mapVals
        fun p _ => (m.val · p)) := by
    unfold SState.endLabel; rw [find_SP]
  dsimp only
  rw [popCallFrame_one 1 _ 0 1 1 (liveLabels_SP dm ρ φ cd d c) (holderOf_SP dm ρ φ cd d c) ht.symm, hE]
  have hx : (SP dm ρ φ cd d c r).toMean.val = fun ψ p => (SP dm ρ φ cd d c r).valAt p ψ := rfl
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
  obtain ⟨hp, hv, ht, hsh⟩ := popCallFrame_SP (r := .el0 Nat 2) dm ρ φ cd d (.el0 Nat 3)
  refine ⟨{ (TyS.plain TyM.unit) with label := none }, popCallFrame 1 none (SP dm ρ φ cd d (.el0 Nat 3) (.el0 Nat 2)), ?_,
    hp, hv, ht, hsh⟩
  unfold runCallRef runBodyRef
  simp only [incT, hs₀, codOf_inc]
  rw [callFrame_inc dm ρ φ _ _ rfl, runBody_incP]
  dsimp only
  have hk : (if outInc.isRef = true then (TyS.plain TyM.unit).label else none) = none := rfl
  rw [hk, popEnds_one _ _ 0 1 1 (liveLabels_SP dm ρ φ _ _ _) (holderOf_SP dm ρ φ _ _ _) rfl,
    if_pos (endsOk_SP dm ρ φ _ _ (Sem.el0 Nat (2 + 1)) ⟨2 + 1, rfl⟩)]
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

/-! ## `Id1 (x : &Nat) : &Nat := &*x`: a returned reborrow, by `callOf` -/

def id1Body : Term := .borrow (.deref (.var 0))
def id1T : Term := .fix ⟨"Id1"⟩ [⟨"x"⟩] [.ref .nat] (.ref .nat) none id1Body
def id1Clo : Value := .clo [] id1T []

/-- `Id1`'s codomain: a returned borrow of `Nat`. -/
def outId1 : PiCod := ⟨true, fun _ => TyM.nat⟩

theorem codOf_id1 (s : SState) (bs : List PBind) : codOf (Kc dm) ρ φ s bs (.ref .nat) = outId1 := rfl

noncomputable def fbId1 : List PBind × (List Sem → TyS) × DeclInfo :=
  (bindsOf (Kc dm) ρ φ (stateOf 0 []) [.ref .nat],
    fixCod (Kc dm) ρ φ (stateOf 0 []) (bindsOf (Kc dm) ρ φ (stateOf 0 []) [.ref .nat]) (.ref .nat),
    (Kc dm).D.typeDecl ((Kc dm).D.teleDecls [] [.ref .nat]) (.ref .nat))

noncomputable def piId1 : TyM := piTyAt dm.read 1 psInc outId1

noncomputable def gId1 : List Sem → Option BodyOut :=
  fixG (Kc dm) ρ φ (fbId1 dm ρ φ) 1 (stateOf 0 []) psInc outId1 (piId1 dm) 0 none id1Body

noncomputable def selfId1T : TyM := piTyAt dm.read 1 psInc (weakCod 1 (fixRank none) 0 outId1)
noncomputable def selfId1M : Sem := closureAt dm.read 1 φ psInc (weakCod 1 (fixRank none) 0 outId1)
  (stageFn 1 psInc (fixRank none) 0 (fixStage (Kc dm) ρ φ (fbId1 dm ρ φ) 1 (stateOf 0 []) psInc outId1 none 0 id1Body 0))

/-- A frame `self`, `x` holding `c` at label `0`, `x`'s cell (as `SB`, any `self`). -/
def SBs (selfB : SBinding) (d : DeclInfo) (c r : Sem) : SState :=
  { env := [{ binds := [selfB, xB c d], temps := [fun ψ => ψ 0] }],
    shape := fun p => if p = .bind 0 1 then some 0 else none, nextLoan := 1,
    heldTy := fun m => if m = 0 then TyM.nat else TyM.err,
    heldMem := fun m => if m = 0 then r else .err }

theorem positions_SBs (selfB : SBinding) (d : DeclInfo) (c : Sem) :
    (SBs selfB d c r).positions = [.bind 0 0, .bind 0 1, .temp 0 0] := by
  simp [SBs, SState.positions, List.range']

theorem liveLabels_SBs (selfB : SBinding) (d : DeclInfo) (c : Sem) : (SBs selfB d c r).liveLabels = [0] := by
  unfold SState.liveLabels; rw [positions_SBs]; simp [SBs]

theorem holderOf_SBs (selfB : SBinding) (d : DeclInfo) (c : Sem) : (SBs selfB d c r).holderOf 0 = some (.bind 0 1) := by
  unfold SState.holderOf; rw [positions_SBs]; simp [SBs]

theorem reached_SBs (selfB : SBinding) (d : DeclInfo) (c : Sem) (p : Pos) (hit : List Step → Bool) (l : Nat) :
    (SBs selfB d c r).reached p hit l = false := by
  simp [SState.reached, SBs]

theorem access_SBs (selfB : SBinding) (d : DeclInfo) (c : Sem) (p : Pos) (hit : List Step → Bool) :
    (SBs selfB d c r).access p hit = SBs selfB d c r := by
  unfold SState.access
  have h : ∀ n : Nat, (List.range n).foldl (fun s _ => (s.liveLabels.filter (s.reached p hit)).foldl SState.endLabel s)
      (SBs selfB d c r) = SBs selfB d c r := by
    intro n; induction n with
    | zero => rfl
    | succ n ih => rw [List.range_succ, List.foldl_append, ih]; simp [liveLabels_SBs, reached_SBs]
  exact h _

theorem typedFuture_SBs (selfB : SBinding) (d : DeclInfo) (c : Sem) (ψ : Future) :
    (SBs selfB d c r).typedFuture ψ = ψ.upd 0 r := by
  funext l; unfold SState.typedFuture; rw [liveLabels_SBs]
  by_cases hl : l = 0 <;> simp [hl, SBs, Future.upd]

theorem resolve_SBs (selfB : SBinding) (d : DeclInfo) (c : Sem) :
    resolve (SBs selfB d c r) (.deref (.var 0)) = some (.bind 0 1, [.deref]) := by
  simp [resolve, SState.varPos, SState.topIdx, Place.steps, SBs]

theorem contentOf_SBs (selfB : SBinding) (d : DeclInfo) (c : Sem) :
    ∃ T, contentOf (Kc dm) φ (.deref (.var 0)) (SBs selfB d c r) = some ((c, T, .bind 0 1, [.deref]), SBs selfB d c r) := by
  unfold contentOf
  rw [resolve_SBs]
  dsimp only
  rw [access_SBs, typedFuture_SBs]
  simp [Sem.follow, Sem.step, SState.valAt, SState.tyAt, SBs, xB]

theorem contentOf_SBs_nat (selfB : SBinding) (d : DeclInfo) (c : Sem) :
    ∃ T : TyS, T.m = TyM.nat ∧
      contentOf (Kc dm) φ (.deref (.var 0)) (SBs selfB d c r) = some ((c, T, .bind 0 1, [.deref]), SBs selfB d c r) := by
  unfold contentOf
  rw [resolve_SBs]
  dsimp only
  rw [access_SBs, typedFuture_SBs]
  simp [Sem.follow, Sem.step, SState.valAt, SState.tyAt, SBs, xB, TyS.plain]

/-- After `&*x` in the frame: `x` reads the reborrow `1`'s final content, the reborrow's content `c`
parked in a temporary holding `1`, lent at `*x`. -/
def SB2 (selfB : SBinding) (d : DeclInfo) (T : TyM) (c r : Sem) : SState :=
  { env := [{ binds := [selfB, { xB c d with val := fun φ' => φ' 1 }], temps := [fun ψ => ψ 0, fun _ => c] }],
    shape := fun p => if p = .temp 0 1 then some 1 else if p = .bind 0 1 then some 0 else none, nextLoan := 2,
    lent := fun m => if m = 1 then [⟨.bind 0 1, [.deref], false⟩] else [],
    heldTy := fun m => if m = 1 then T else if m = 0 then TyM.nat else TyM.err,
    heldMem := fun m => if m = 1 then c else if m = 0 then r else .err }

theorem contentOk_SBs (selfB : SBinding) (d : DeclInfo) (c : Sem) :
    ContentOk (Kc dm) φ (.deref (.var 0)) (SBs selfB d c r) := by
  unfold ContentOk; rw [resolve_SBs]
  exact Attack.accessOk_unreached _ φ fun l => reached_SBs (r := r) selfB d c _ _ l

theorem assignOk_SBs (selfB : SBinding) (d : DeclInfo) (c : Sem) :
    AssignOk (Kc dm) φ (.deref (.var 0)) (SBs selfB d c r) := by
  unfold AssignOk; rw [resolve_SBs]
  exact ⟨fun _ => Attack.accessOk_unreached _ φ fun l => reached_SBs (r := r) selfB d c _ _ l, fun h => by simp at h⟩

theorem runBody_id1 (selfB : SBinding) (d : DeclInfo) (a : Nat) (hint : TyS) (tl : Bool) :
    ∃ T, runT (Kc dm) ρ φ tl hint id1Body (SBs selfB d (.el0 Nat a) r) = some ((.el0 Nat a, T), SB2 selfB d T.m (.el0 Nat a) r) ∧
      T.label = some 1 ∧ T.m = TyM.nat := by
  obtain ⟨T, hTm, hT⟩ := contentOf_SBs_nat (r := r) dm φ selfB d (.el0 Nat a)
  refine ⟨{ T with label := some 1 }, ?_, rfl, hTm⟩
  simp only [id1Body, runT, SM.erasedIf, flags_Kc, Bool.false_eq_true, if_false, SM.stmtIf, SM.strictS,
    SM.guarded_of (contentOk_SBs (r := r) dm φ selfB d (.el0 Nat a))]
  unfold borrowPlace
  simp only [hT, bind, Option.bind]
  simp [Sem.whole, SState.freshLoan, SState.tyAt, SState.valAt, SState.setAt,
    Attack.updAt_deref, Attack.updAt_nil, SState.pushTempShaped, SState.pushTemp, SState.topIdx, SState.setLent, SState.setHeldTy, SState.setHeldMem, SBs, SB2, xB]
  simp only [hTm]
  rw [if_pos ⟨a, rfl⟩]
  dsimp only
  simp only [Attack.invalidate_noInv (Kc dm) φ (fun _ _ => rfl)]
  rw [if_pos]
  exact ⟨Attack.invalidateOk_noInv (Kc dm) φ (fun _ _ => rfl) _ _, Attack.lentOk_deref (Kc dm) φ (pos := .bind 0 1) (by simp [resolve, SState.varPos, SState.topIdx, Ochr.Place.steps])⟩

noncomputable def selfId1 : SBinding := { ty := .plain (selfId1T dm), val := fun _ => selfId1M dm ρ φ, decl := .pi (fbId1 dm ρ φ).2.2 }

theorem frame_id1 (c : Sem) :
    ([c].zip psInc).foldl (fixStep (fbId1 dm ρ φ)) ((stateOf 0 []).pushBind (selfId1 dm ρ φ), [], [])
      = (SBs (selfId1 dm ρ φ) (dInc dm) c c, [c], [.temp 0 0]) := by
  simp [fixStep, psInc, stateOf, SState.freshLoan, SState.pushTemp, SState.pushBind, SState.topIdx, pushBindShaped,
    SState.takeLabel, SState.holderOf, SState.positions, SBs, xB, dInc, fbId1, bindsOf, runBinds, mkBind, SState.setHeldMem,
    SState.setHeldTy]
  exact ⟨⟨rfl, rfl⟩, rfl⟩

theorem positions_SB2 (selfB : SBinding) (d : DeclInfo) (T : TyM) (c : Sem) :
    (SB2 selfB d T c r).positions = [.bind 0 0, .bind 0 1, .temp 0 0, .temp 0 1] := by
  simp [SB2, SState.positions, List.range']

theorem liveLabels_SB2 (selfB : SBinding) (d : DeclInfo) (T : TyM) (c : Sem) : (SB2 selfB d T c r).liveLabels = [0, 1] := by
  unfold SState.liveLabels; rw [positions_SB2]; simp [SB2]
  first | rfl | decide | simp [List.mergeSort]

theorem find_SB2 (selfB : SBinding) (d : DeclInfo) (T : TyM) (c : Sem) :
    ((SB2 selfB d T c r).positions.find? fun p => decide ((SB2 selfB d T c r).shape p = some 0)) = some (.bind 0 1) := by
  rw [positions_SB2]; simp [SB2]

/-- Ending `x`'s label at the pop is strict: `x` reads the reborrow's final content, a `Nat` at the
futures typed at label `1` (the reborrow's type is `Nat`). -/
theorem endsOk_SB2 (selfB : SBinding) (d : DeclInfo) (c : Sem) :
    EndsOk (Kc dm) φ [0] (SB2 selfB d TyM.nat c r) := by
  refine ⟨?_, trivial⟩
  intro q hq ψ hψ
  have hh : (SB2 selfB d TyM.nat c r).holderOf 0 = some (.bind 0 1) := by
    unfold SState.holderOf; rw [positions_SB2]; simp [SB2]
  rw [hh] at hq
  cases hq
  have h1 : ψ 1 ∈ₛ[(Kc dm).dm.read] TyM.nat := by
    have := hψ.2 1 (by rw [liveLabels_SB2]; simp)
    simpa [SB2] using this
  show ψ 1 ∈ₛ[(Kc dm).dm.read] (if 0 = 0 then TyM.nat else TyM.err)
  rw [if_pos rfl]; exact h1

/-- Ending `x`'s label at the pop: the cell reads the reborrow's final content. -/
theorem endLabel_SB2_cell (selfB : SBinding) (d : DeclInfo) (T : TyM) (c : Sem) (ψ : Future) :
    ((SB2 selfB d T c r).endLabel 0).valAt (.temp 0 0) ψ = ψ 1 := by
  unfold SState.endLabel
  rw [find_SB2]
  simp [SB2, SState.mapVals, SState.valAt, Mean.semEnd, SState.toMean, Future.upd, xB]

theorem gId1_eval (a : Nat) :
    gId1 dm ρ φ [.el0 Nat a] = some ⟨.el0 Nat a, [fun ψ => ψ 1], some 1⟩ := by
  show fixBodyAt (Kc dm) ρ φ (fbId1 dm ρ φ) (stateOf 0 []) psInc outId1 (selfId1T dm) 0 id1Body (selfId1M dm ρ φ)
    [.el0 Nat a] = _
  unfold fixBodyAt
  rw [show ({ ty := .plain (selfId1T dm), val := fun _ => selfId1M dm ρ φ, decl := .pi (fbId1 dm ρ φ).2.2 } : SBinding)
      = selfId1 dm ρ φ from rfl]
  dsimp only
  rw [frame_id1]
  dsimp only
  obtain ⟨T, hT, hl, hTm⟩ := runBody_id1 dm ρ φ (selfId1 dm ρ φ) (dInc dm) a ((fbId1 dm ρ φ).2.1 [.el0 Nat a]) true
  rw [hT]
  dsimp only
  rw [liveLabels_SB2]
  simp only [outId1, if_true, hl, List.filter_cons, List.filter_nil, ge_iff_le, Nat.zero_le, ne_eq, reduceCtorEq,
    not_false_eq_true, and_self, decide_true, if_true, Option.some.injEq, Nat.one_ne_zero, not_true_eq_false,
    and_false, decide_false, Bool.false_eq_true, List.foldl_cons, List.foldl_nil, List.map_cons, List.map_nil, ↓reduceIte]
  rw [hTm] at *
  rw [if_pos (endsOk_SB2 dm φ (selfId1 dm ρ φ) (dInc dm) _)]
  congr
  funext ψ
  exact endLabel_SB2_cell _ _ _ _ ψ

theorem enc_nat (R : DataRead) (x : Nat) : Code0.enc R Code0.nat x = .el0 Nat x := rfl

/-- `Id1`'s leaf at `x`: the forward value `x`, the backward function `v ↦ v` (injective). -/
theorem leaf_id1 (x : Nat) :
    ((gId1 dm ρ φ [Code0.enc dm.read Code0.nat x]).bind
      (mkLeafRefL (lvl0 dm.read) φ (extFin true PUnit Nat)
        (extMkL true PUnit Nat (fun fs => some (PUnit.unit, fs)) (Code0.dec dm.read Code0.nat)) Code0.nat)).isSome := by
  rw [enc_nat, gId1_eval]
  simp only [Option.bind_some, mkLeafRefL]
  have hd : Code0.dec dm.read Code0.nat (.el0 Nat x) = some x := Attack.dec_nat_el0 dm.read x
  have hb : ∀ v : Nat, mkBackAtL (lvl0 dm.read) φ (extFin true PUnit Nat)
      (extMkL true PUnit Nat (fun fs => some (PUnit.unit, fs)) (Code0.dec dm.read Code0.nat)) Code0.nat
      ⟨.el0 Nat x, [fun ψ => ψ 1], some 1⟩ 1 v = some (PUnit.unit, v) := by
    intro v
    simp [mkBackAtL, extMkL, Future.upd, Lvl.enc, lvl0, enc_nat, Attack.dec_nat_el0]
  rw [hd]
  simp [hb]
  rfl

theorem mkTel_id1 :
    (mkTelL (lvl0 dm.read) φ (telL (lvl0 dm.read) psInc [] PUnit outId1).2 [] (fun fs => some (PUnit.unit, fs))
      (gId1 dm ρ φ)).isSome := by
  simp only [telL, psInc, outId1, mkTelL]
  have h' : ∀ (x : TyM.nat.code0.fst), ((gId1 dm ρ φ [Code0.enc dm.read TyM.nat.code0.snd x]).bind
      (mkLeafRefL (lvl0 dm.read) φ (extFin true PUnit TyM.nat.code0.fst)
        (extMkL true PUnit TyM.nat.code0.fst (fun fs => some (PUnit.unit, fs)) (Code0.dec dm.read TyM.nat.code0.snd))
        TyM.nat.code0.snd)).isSome := fun x => leaf_id1 dm ρ φ x
  simp [h']

/-- `Id1`'s term runs to its closure, at its code (the strict `.fix`: the closure is built). -/
theorem run_id1T : ∃ s', runT (Kc dm) ρ φ false (.plain .err) id1T (stateOf 0 (capsState [] []))
    = some ((closureAt dm.read 1 φ psInc outId1 (gId1 dm ρ φ), .plain (piId1 dm)), s') := by
  have hmem : closureAt dm.read 1 φ psInc outId1 (gId1 dm ρ φ) ∈ₛ[dm.read] piTyAt dm.read 1 psInc outId1 :=
    (closureL_mem (lvl0 dm.read) (lvl0_lawful dm.read) φ _ _).resolve_right (closureL0_ne_err dm φ _ _ (mkTel_id1 dm ρ φ))
  refine ⟨fixMoves (Kc dm) id1T (stateOf 0 (capsState [] [])), ?_⟩
  rw [id1T, run_fix_def]
  simp only [SM.erasedIf, SM.stmtIf, flags_Kc, Bool.false_eq_true, if_false, SM.strictS]
  have hco : capOrder id1T = [] := by decide
  have hc : FoldOk (capStep (Kc dm)) (CapOk (Kc dm) φ) (capOrder id1T) (stateOf 0 (capsState [] [])) := by
    rw [hco]; trivial
  erw [if_pos hc]
  rw [if_pos (by exact hmem)]
  rfl

open Classical in
theorem meanV_id1Clo (hint : TyS) :
    meanV (Kc dm) ρ φ hint id1Clo = closureAt dm.read 1 φ psInc outId1 (gId1 dm ρ φ) := by
  obtain ⟨s', h⟩ := run_id1T dm ρ φ
  -- the strict closure: no captures, so `CapsOk` holds
  show (if CapsOk (Kc dm).dm.read [] [] then (match runT (Kc dm) ρ φ false (.plain .err) id1T (stateOf 0 (capsState [] [])) with
    | some ((v, _), _) => v | none => .err) else .err) = _
  rw [if_pos (show CapsOk (Kc dm).dm.read [] [] from trivial), h]

theorem valT_id1Clo (hint : TyS) : valT (Kc dm) ρ φ hint id1Clo = .plain (piId1 dm) := by
  obtain ⟨s', h⟩ := run_id1T dm ρ φ
  show (match runT (Kc dm) ρ φ false (.plain TyM.err) id1T (stateOf 0 (capsState [] [])) with
    | some ((_, R), _) => R | none => hint) = _
  rw [h]

/-- `Id1`'s reading as a call's head. -/
noncomputable def fresId1 : Res := (closureAt dm.read 1 φ psInc outId1 (gId1 dm ρ φ), .plain (piId1 dm))

/-- **`callOf` on `Id1`'s closure at `2` with the borrow's label `lab`**: the reborrow, at the fresh
label `k` (the counter), holding `2`; the argument's holder consumed; a place that read `lab`'s final
content now reads `k`'s, through the backward function `v ↦ v`; `k` lent, as fills, where `lab` was. -/
theorem callOf_id1 (s : SState) (T : TyS) (lab : Nat) :
    ∃ TU : TyS, TU.m = TyM.nat ∧ TU.label = some (s.takeLabel lab).freshLoan.1 ∧
      callOf dm.read (fresId1 dm ρ φ) [(.el0 Nat 2, { T with label := some lab })] s
      = some ((.el0 Nat 2, TU),
          (((((s.takeLabel lab).freshLoan.2.mapVals fun _ v φ' =>
              match Code0.dec dm.read TyM.nat.code0.snd (φ' (s.takeLabel lab).freshLoan.1) with
              | some x => v (φ'.upd lab (Code0.enc dm.read TyM.nat.code0.snd x))
              | none => v (φ'.upd lab .moved)).pushTempShaped (fun _ => .el0 Nat 2) (s.takeLabel lab).freshLoan.1).setLent
            (s.takeLabel lab).freshLoan.1 (((s.takeLabel lab).freshLoan.2.lent lab).map fun x => { x with fill := true })).setHeldTy
            (s.takeLabel lab).freshLoan.1 ((lvl0 dm.read).toTy TyM.nat.code0.snd)).setHeldMem
            (s.takeLabel lab).freshLoan.1 (.el0 Nat 2)) := by
  obtain ⟨o, r, hg, hap, hm⟩ := applyFnL_closureL (lvl0 dm.read) (lvl0_lawful dm.read) φ
    (telL (lvl0 dm.read) psInc [] PUnit outId1).2 (gId1 dm ρ φ) [.el0 Nat 2] (mkTel_id1 dm ρ φ)
    ⟨(2 : Nat), Attack.dec_nat_el0 dm.read 2, trivial⟩
  rw [gId1_eval] at hg
  cases hg
  rcases r with ⟨res, TT, fins⟩ | ⟨U, c, fwd, back⟩
  · exfalso
    have hd2 : Code0.dec dm.read TyM.nat.code0.snd (Sem.el0 Nat 2) = some (2 : Nat) := Attack.dec_nat_el0 dm.read 2
    simp [applyFnL, telL, psInc, outId1, applyTelL, hd2] at hap
    obtain ⟨F, -, hF⟩ := Option.bind_eq_some_iff.mp hap
    cases hF
  · have hd2 : Code0.dec dm.read TyM.nat.code0.snd (Sem.el0 Nat 2) = some (2 : Nat) := Attack.dec_nat_el0 dm.read 2
    have hap' := hap
    simp [applyFnL, telL, psInc, outId1, applyTelL, hd2] at hap'
    obtain ⟨F, -, hF⟩ := Option.bind_eq_some_iff.mp hap'
    cases hF
    obtain ⟨k, hk, hfwd, hback⟩ := hm
    cases hk
    refine ⟨⟨(lvl0 dm.read).toTy Code0.nat, some (s.takeLabel lab).freshLoan.1⟩, rfl, rfl, ?_⟩
    show callOfL (lvl0 dm.read) (telL (lvl0 dm.read) psInc [] PUnit outId1).2
      (closureL (lvl0 dm.read) φ (telL (lvl0 dm.read) psInc [] PUnit outId1).2 (gId1 dm ρ φ)) _ s = _
    unfold callOfL
    dsimp only
    rw [show List.map (fun x : Res => x.fst) [(Sem.el0 Nat 2, { T with label := some lab })] = [Sem.el0 Nat 2] from rfl, hap]
    have hd3 : Code0.dec dm.read TyM.nat.code0.snd (Sem.el0 Nat 2) = some (show TyM.nat.code0.fst from (2 : Nat)) := hd2
    simp only [telRefsL, telL, psInc, outId1]
    simp only [hd3]
    simp [hfwd, hback, Future.upd, Future.updList]
    have hf : Code0.enc dm.read TyM.nat.code0.snd (F (show TyM.nat.code0.fst from (2 : Nat))).val.fst = Sem.el0 Nat 2 := hfwd
    refine ⟨⟨?_, rfl, HEq.rfl⟩, ?_⟩
    · exact hf
    · rw [hf]
      congr 5
      funext p v φ'
      split <;> rename_i h <;> rw [h]

/-! ## `UseId1` by `callOf`: `let y = 2; let r = Id1(&y); *r := 5; y` is `5` -/

theorem run_id1Clo (hint : TyS) (s : SState) :
    run (Kc dm) ρ φ hint (.val id1Clo) s = some (fresId1 dm ρ φ, s) := by
  rw [run_val_def, meanV_id1Clo, valT_id1Clo]
  simp only [id1Clo, strictVal]
  rw [if_neg (show closureAt dm.read 1 φ psInc outId1 (gId1 dm ρ φ) ≠ .err from
    closureL0_ne_err dm φ _ _ (mkTel_id1 dm ρ φ))]
  rfl

/-- `y`'s meaning after the call: the final content of the reborrow `1`, read back. -/
noncomputable def yR1 : SVal := fun φ' =>
  match Code0.dec dm.read TyM.nat.code0.snd (φ' 1) with
  | some x => (φ'.upd 0 (Code0.enc dm.read TyM.nat.code0.snd x)) 0
  | none => (φ'.upd 0 .moved) 0

/-- The frame `y`, `r` with two temporaries, `r` holding the reborrow `1`, lent at `y` as a fill (and
the dead `0` at `y`'s old loan site). -/
def SR (rT : TyS) (yv rv t0 t1 : SVal) : SState :=
  { env := [SFrame.mk [{ yB with val := yv }, { ty := rT, val := rv, decl := .other }] [t0, t1]],
    shape := fun p => if p = .bind 0 1 then some 1 else none, nextLoan := 2,
    lent := fun m => if m = 1 then [⟨.bind 0 0, [], true⟩] else if m = 0 then [⟨.bind 0 0, [], false⟩] else [],
    heldTy := fun m => if m = 1 then TyM.t0 TyM.nat.code0.fst TyM.nat.code0.snd else if m = 0 then yB.ty.m else TyM.err,
    heldMem := fun m => if m = 1 then .el0 Nat 2 else if m = 0 then .el0 Nat 2 else .err }

/-- The parked temporary `0` after the call's fixing: `moved` where the reborrow's final content decodes. -/
noncomputable def mv1 : SVal := fun φ' =>
  match Code0.dec dm.read TyM.nat.code0.snd (φ' 1) with
  | some _ => .moved
  | none => .moved

/-- The state after the call `Id1(&y)` by `callOf` (`callOf_id1` at `S₂`, label `0`). -/
noncomputable def SC1 : SState :=
  ((((((Attack.S₂ yB 0 (.el0 Nat 2)).takeLabel 0).freshLoan.2.mapVals fun _ v φ' =>
      match Code0.dec dm.read TyM.nat.code0.snd (φ' ((Attack.S₂ yB 0 (.el0 Nat 2)).takeLabel 0).freshLoan.1) with
      | some x => v (φ'.upd 0 (Code0.enc dm.read TyM.nat.code0.snd x))
      | none => v (φ'.upd 0 .moved)).pushTempShaped (fun _ => .el0 Nat 2) ((Attack.S₂ yB 0 (.el0 Nat 2)).takeLabel 0).freshLoan.1).setLent
    ((Attack.S₂ yB 0 (.el0 Nat 2)).takeLabel 0).freshLoan.1
    ((((Attack.S₂ yB 0 (.el0 Nat 2)).takeLabel 0).freshLoan.2.lent 0).map fun x => { x with fill := true })).setHeldTy
    ((Attack.S₂ yB 0 (.el0 Nat 2)).takeLabel 0).freshLoan.1 ((lvl0 dm.read).toTy TyM.nat.code0.snd)).setHeldMem
    ((Attack.S₂ yB 0 (.el0 Nat 2)).takeLabel 0).freshLoan.1 (.el0 Nat 2)

/-- The call `Id1(&y)` after `let y = 2`: `2` at the reborrow `1`. -/
theorem run_callId1 :
    ∃ TU : TyS, TU.m = TyM.nat ∧ TU.label = some 1 ∧
      run (Kc dm) ρ φ (.plain .err) (.call (.val id1Clo) [.borrow (.var 0)] false) ((emptyState 0).pushBind yB)
        = some ((.el0 Nat 2, TU), SC1 dm) := by
  obtain ⟨TU, hTm, hTU, hc⟩ := callOf_id1 dm ρ φ (Attack.S₂ yB 0 (.el0 Nat 2)) yB.ty 0
  refine ⟨TU, hTm, by rw [hTU, Attack.takeLabel_S₂]; rfl, ?_⟩
  rw [show Kc dm = Kp dm [] (fun _ => (.err, .plain TyM.err)) from rfl, run_call]
  rw [show Kp dm [] (fun _ => (.err, .plain TyM.err)) = Kc dm from rfl]
  simp only [SM.headOf, run_id1Clo, bind, Option.bind, fresId1, runArgs_borrowY]
  rw [if_pos (by exact borrowArgs_psInc dm outId1 _ yB rfl)]
  exact hc

/-- Binding `r` to the call's result: `r` holds the reborrow, its parked temporary consumed. -/
theorem bindR (TU : TyS) (hTU : TU.label = some 1) :
    pushBindShaped (SC1 dm)
        { ty := TU, val := fun _ => .el0 Nat 2, decl := .other }
      = SR TU (yR1 dm) (fun _ => .el0 Nat 2) (mv1 dm) (fun _ => .moved) := by
  simp only [SC1, Attack.takeLabel_S₂]
  simp [pushBindShaped, hTU, SState.freshLoan, SState.mapVals, SState.pushTempShaped, SState.pushTemp, SState.setLent,
    SState.setHeldTy, SState.setHeldMem, SState.topIdx, SState.takeLabel, SState.holderOf, SState.positions, List.range', SState.setAt,
    SState.pushBind, SR, yR1, mv1]
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · funext φ'; unfold yR1; split <;> rename_i h <;> first | rfl | rw [h]
  · funext φ'; unfold mv1; split <;> rename_i h <;> first | rfl | rw [h]
  · funext p; by_cases h1 : p = Pos.bind 0 1 <;> by_cases h2 : p = Pos.temp 0 1 <;> simp [h1, h2]

section SRLemmas
variable (rT : TyS) (yv rv t0 t1 : SVal)

theorem positions_SR : (SR rT yv rv t0 t1).positions = [.bind 0 0, .bind 0 1, .temp 0 0, .temp 0 1] := by
  simp [SR, SState.positions, List.range']

theorem liveLabels_SR : (SR rT yv rv t0 t1).liveLabels = [1] := by
  unfold SState.liveLabels; rw [positions_SR]; simp [SR]

theorem find_SR : ((SR rT yv rv t0 t1).positions.find? fun p => decide ((SR rT yv rv t0 t1).shape p = some 1))
    = some (.bind 0 1) := by
  rw [positions_SR]; simp [SR]

theorem access_SR_r (hit : List Step → Bool) : (SR rT yv rv t0 t1).access (.bind 0 1) hit = SR rT yv rv t0 t1 := by
  unfold SState.access
  have h : ∀ n : Nat, (List.range n).foldl (fun s _ => (s.liveLabels.filter (s.reached (.bind 0 1) hit)).foldl SState.endLabel s)
      (SR rT yv rv t0 t1) = SR rT yv rv t0 t1 := by
    intro n; induction n with
    | zero => rfl
    | succ n ih =>
      rw [List.range_succ, List.foldl_append, ih]
      simp [liveLabels_SR, SState.reached, show (SR rT yv rv t0 t1).lent 1 = [⟨.bind 0 0, [], true⟩] from rfl]
  exact h _

theorem resolve_SR_r : resolve (SR rT yv rv t0 t1) (.deref (.var 0)) = some (.bind 0 1, [.deref]) := by
  simp [resolve, SState.varPos, SState.topIdx, Place.steps, SR]

theorem resolve_SR_y : resolve (SR rT yv rv t0 t1) (.var 1) = some (.bind 0 0, []) := by
  simp [resolve, SState.varPos, SState.topIdx, Place.steps, SR]

theorem setContent_SR (v : Sem) :
    setContent (Kc dm) φ (.bind 0 1) [.deref] v (SR rT yv rv t0 t1) = some (⟨⟩, SR rT yv (fun _ => v) t0 t1) := by
  simp [setContent, Attack.updAt_deref, Attack.updAt_nil, SState.setAt, SR, SState.valAt]

/-- Ending the reborrow `1` (its holder `r`): `y` reads the future that fixes `1` to `r`'s content. -/
theorem endLabel_SR_valAt (p : Pos) (ψ : Future) :
    ((SR rT yv rv t0 t1).endLabel 1).valAt p ψ =
      if p = .bind 0 1 then .moved else (SR rT yv rv t0 t1).valAt p (ψ.upd 1 (rv ψ)) := by
  unfold SState.endLabel
  rw [find_SR]
  dsimp only
  rcases p with ⟨f, i⟩ | ⟨f, i⟩
  · rcases f with _ | f <;> rcases i with _ | _ | i <;> simp [SState.valAt, SState.mapVals, Mean.semEnd, SState.toMean, SR]
  · rcases f with _ | f <;> rcases i with _ | _ | i <;> simp [SState.valAt, SState.mapVals, Mean.semEnd, SState.toMean, SR]

theorem endLabel_SR_shape : ((SR rT yv rv t0 t1).endLabel 1).shape = fun _ => none := by
  unfold SState.endLabel
  rw [find_SR]
  funext p; by_cases h : p = .bind 0 1 <;> simp [Mean.semEnd, SState.toMean, SState.mapVals, SR, h]

/-- `*r`'s type in `SR`: `r`'s content type. -/
theorem placeTy_SR_r : (placeTy (Kc dm) φ (.deref (.var 0)) (SR rT yv rv t0 t1)).m = rT.m := by
  unfold placeTy contentOf
  rw [resolve_SR_r]
  dsimp only
  rw [access_SR_r]
  simp [Sem.follow, Sem.step, SState.tyAt, SState.valAt, SR, TyS.plain]

theorem reached_SR_r (hit : List Step → Bool) (l : Nat) : (SR rT yv rv t0 t1).reached (.bind 0 1) hit l = false := by
  unfold SState.reached
  by_cases h1 : l = 1
  · subst h1; simp [SR]
  · by_cases h0 : l = 0
    · subst h0; simp [SR]
    · simp [SR, h1, h0]

theorem assignOk_SR : AssignOk (Kc dm) φ (.deref (.var 0)) (SR rT yv rv t0 t1) := by
  unfold AssignOk; rw [resolve_SR_r]
  exact ⟨fun _ => Attack.accessOk_unreached _ φ fun l => reached_SR_r rT yv rv t0 t1 _ l, fun h => by simp at h⟩

/-- `*r := 5`: `r`'s content is `5`; no borrow ends (the reborrow is lent at `y`, not at `r`). -/
theorem runAssign_SR (hint : TyS) (hrT : rT.m = TyM.nat) :
    run (Kc dm) ρ φ hint (.assign (.deref (.var 0)) (num 5)) (SR rT yv rv t0 t1)
      = some ((.el0 Unit (), .plain TyM.unit), SR rT yv (fun _ => .el0 Nat 5) t0 t1) := by
  show runT (Kc dm) ρ φ false hint _ _ = _
  rw [runT]
  simp only [SM.erasedIf, flags_Kc, Bool.false_eq_true, if_false, SM.stmtIf]
  show (do
    let ((v, R), s) ← runT (Kc dm) ρ φ false _ (num 5) (SR rT yv rv t0 t1)
    (if v ∈ₛ[(Kc dm).dm.read] (placeTy (Kc dm) φ (.deref (.var 0)) s).m ∧
        labTyOk s R.label (placeTy (Kc dm) φ (.deref (.var 0)) s).m then
      match SM.guarded (AssignOk (Kc dm) φ (.deref (.var 0))) (assignAt (Kc dm) φ (.deref (.var 0)) v R.label) s with
      | some (r, s₁) =>
        let s₂ := invalidate (Kc dm) φ (.deref (.var 0)) s₁
        if InvalidateOk (Kc dm) φ (.deref (.var 0)) s₁ ∧ lentOk (Kc dm) φ (.deref (.var 0)) s₂ then some (r, s₂) else none
      | none => none else none)) = _
  simp only [bind, Option.bind]
  rw [show runT (Kc dm) ρ φ false _ (num 5) (SR rT yv rv t0 t1) = _ from run_num dm [] _ ρ φ 5 _ _]
  dsimp only
  -- the strict write: `5` is a `Nat`, `*r`'s type
  rw [if_pos ⟨by rw [placeTy_SR_r, hrT]; exact ⟨5, rfl⟩, fun l h => by cases h⟩]
  simp only [SM.guarded_of (assignOk_SR dm φ rT yv rv t0 t1), assignAt, resolve_SR_r, List.isEmpty_cons, Bool.false_and, Bool.false_eq_true, if_false, access_SR_r,
    setContent_SR]
  simp only [Attack.invalidate_noInv (Kc dm) φ (fun _ _ => rfl)]
  rw [if_pos]
  all_goals first | rfl | exact ⟨Attack.invalidateOk_noInv (Kc dm) φ (fun _ _ => rfl) _ _, Attack.lentOk_deref (Kc dm) φ (pos := .bind 0 1) (resolve_SR_r _ _ _ _ _)⟩

theorem endOk_SR5 : EndOk (Kc dm) φ (SR rT yv (fun _ => .el0 Nat 5) t0 t1) 1 := by
  intro q hq ψ _
  have hh : (SR rT yv (fun _ => .el0 Nat 5) t0 t1).holderOf 1 = some (.bind 0 1) := find_SR rT yv _ t0 t1
  rw [hh] at hq
  cases hq
  exact ⟨(5 : Nat), rfl⟩

/-- Reading `y` after `*r := 5` ends the reborrow `1` over `r`'s content `5`, strictly. -/
theorem contentOk_SR5 : ContentOk (Kc dm) φ (.var 1) (SR rT yv (fun _ => .el0 Nat 5) t0 t1) := by
  unfold ContentOk; rw [resolve_SR_y]
  intro j hj
  rw [liveLabels_SR] at hj
  have hj0 : j = 0 := by simpa using hj
  subst hj0
  have hd : (SR rT yv (fun _ => .el0 Nat 5) t0 t1).reached (.bind 0 0) (dataHit []) 1 = true := by
    simp [SState.reached, SR, dataHit]
  simp only [List.range_zero, List.foldl_nil, liveLabels_SR, List.filter_cons, List.filter_nil, hd, if_true]
  exact ⟨endOk_SR5 dm φ rT yv t0 t1, trivial⟩

/-- Reading `y` after `*r := 5`: the read of `y` ends the reborrow `1` (lent at `y`), whose final
content `5` `y` then reads. -/
theorem readY_SR (yv' : SVal) (hy : ∀ ψ, yv (ψ.upd 1 (.el0 Nat 5)) = yv' ψ) (hw : ∀ ψ, (yv' ψ).whole)
    (hg : ∀ ψ, ReadGood (Kc dm).dm.read TyM.nat (yv' ψ)) :
    ∃ T, readPlace (Kc dm) φ (.var 1) true (SR rT yv (fun _ => .el0 Nat 5) t0 t1)
      = some ((yv' φ, T), (SR rT yv (fun _ => .el0 Nat 5) t0 t1).endLabel 1) := by
  have ha : (SR rT yv (fun _ => .el0 Nat 5) t0 t1).access (.bind 0 0) (dataHit []) = (SR rT yv (fun _ => .el0 Nat 5) t0 t1).endLabel 1 := by
    unfold SState.access
    rw [liveLabels_SR]
    simp [SState.reached, dataHit, show (SR rT yv (fun _ => .el0 Nat 5) t0 t1).lent 1 = [⟨.bind 0 0, [], true⟩] from rfl,
      liveLabels_SR]
  have h0 : ∀ l : List Pos, List.filterMap (fun _ : Pos => (none : Option Nat)) l = [] := by
    intro l; induction l <;> simp_all
  have hl : ((SR rT yv (fun _ => .el0 Nat 5) t0 t1).endLabel 1).liveLabels = [] := by
    unfold SState.liveLabels; rw [endLabel_SR_shape, h0]; simp
  have hcf : ((SR rT yv (fun _ => .el0 Nat 5) t0 t1).endLabel 1).typedFuture φ = φ := by
    funext l; simp [SState.typedFuture, hl]
  have hv : ((SR rT yv (fun _ => .el0 Nat 5) t0 t1).endLabel 1).valAt (.bind 0 0) φ = yv' φ := by
    rw [endLabel_SR_valAt]; simp [SR, SState.valAt, hy]
  refine ⟨{ (SR rT yv (fun _ => .el0 Nat 5) t0 t1).tyAt (.bind 0 0) with label := none }, ?_⟩
  simp only [readPlace, contentOf, resolve_SR_y, ha, hcf, Sem.follow, hv, bind, Option.bind]
  have hg' : ReadGood (Kc dm).dm.read yB.ty.m (yv' φ) := hg φ
  simp [hw, hg']
  have ht : (((SR rT yv (fun _ => .el0 Nat 5) t0 t1).endLabel 1).tyAt (.bind 0 0)).m
      = ((SR rT yv (fun _ => .el0 Nat 5) t0 t1).tyAt (.bind 0 0)).m := by
    unfold SState.endLabel; rw [find_SR]; simp [SState.tyAt, SState.mapVals, SR]
  exact ⟨by rw [ht]; exact hg', ht⟩

end SRLemmas

/-- `let y = 2; let r = Id1(&y); *r := 5; y`, with `Id1`'s closure as the head. -/
def useId1T : Term :=
  .letIn ⟨"y"⟩ (num 2) (.letIn ⟨"r"⟩ (.call (.val id1Clo) [.borrow (.var 0)] false)
    (.seq (.assign (.deref (.var 0)) (num 5)) (.place (.var 1))))

theorem yR1_five (ψ : Future) : yR1 dm (ψ.upd 1 (.el0 Nat 5)) = .el0 Nat 5 := by
  have hd : Code0.dec dm.read TyM.nat.code0.snd (.el0 Nat 5) = some (show TyM.nat.code0.fst from (5 : Nat)) :=
    Attack.dec_nat_el0 dm.read 5
  simp only [yR1, Future.upd, if_true, if_pos rfl]
  rw [hd]
  rfl

/-- **`UseId1` by `callOf`: `let y = 2; let r = Id1(&y); *r := 5; y` runs to `5`**, the checker's
answer (`Regress/ShapeProbes.lean`: `UseId1Is5` accepted, `UseId1Is2` rejected): the call returns the
reborrow, `y` reads its final content through the backward function, the write through `r` is that
content, and reading `y` ends the reborrow. -/
theorem useId1_callOf (hint : TyS) :
    ∃ T s', run (Kc dm) ρ φ hint useId1T (emptyState 0) = some ((.el0 Nat 5, T), s') := by
  obtain ⟨TU, hTm, hTU, hc⟩ := run_callId1 dm ρ φ
  have hb := bindR dm TU hTU
  obtain ⟨Ty, hy⟩ := readY_SR dm φ TU (yR1 dm) (mv1 dm) (fun _ => .moved) (fun _ => .el0 Nat 5)
    (yR1_five dm) (fun _ => by simp [Sem.whole]) (fun _ => Or.inl ⟨(5 : Nat), rfl⟩)
  have hseq : run (Kc dm) ρ φ hint (.seq (.assign (.deref (.var 0)) (num 5)) (.place (.var 1)))
      (SR TU (yR1 dm) (fun _ => .el0 Nat 2) (mv1 dm) (fun _ => .moved))
      = some ((.el0 Nat 5, Ty), (SR TU (yR1 dm) (fun _ => .el0 Nat 5) (mv1 dm) (fun _ => .moved)).endLabel 1) := by
    show runT (Kc dm) ρ φ false hint _ _ = _
    rw [runT]
    simp only [SM.erasedIf, flags_Kc, Bool.false_eq_true, if_false, SM.stmtIf]
    show (do let r ← run (Kc dm) ρ φ (.plain .err) _; SM.guardMod (DiscardOk (Kc dm) φ r.2) (discardEnd r.2); runT (Kc dm) ρ φ false hint (.place (.var 1))) _ = _
    simp only [bind, Option.bind, runAssign_SR (hrT := hTm)]
    erw [Attack.guardMod_discard_plain (Kc dm) φ TyM.unit]
    rw [runT]
    simp only [SM.erasedIf, flags_Kc, copy_Kc, Bool.false_eq_true, if_false, SM.stmtIf, SM.guarded_of (contentOk_SR5 dm φ TU (yR1 dm) (mv1 dm) (fun _ => .moved))]
    exact hy
  refine ⟨Ty, ?_⟩
  rw [useId1T, show Kc dm = Kp dm [] (fun _ => (.err, .plain TyM.err)) from rfl, run_letIn, run_num]
  rw [show Kp dm [] (fun _ => (.err, .plain TyM.err)) = Kc dm from rfl]
  simp only [bind, Option.bind]
  rw [Attack.pushBindShaped_noLabel _ _ rfl]
  rw [show ({ ty := TyS.plain TyM.nat, val := fun _ => .el0 Nat 2, decl := .other } : SBinding)
    = yB from rfl]
  rw [show Kc dm = Kp dm [] (fun _ => (.err, .plain TyM.err)) from rfl, run_letIn]
  rw [show Kp dm [] (fun _ => (.err, .plain TyM.err)) = Kc dm from rfl, hc]
  simp only [bind, Option.bind]
  rw [show ({ ty := TU, val := fun _ => .el0 Nat 2 } : SBinding) = { ty := TU, val := fun _ => .el0 Nat 2, decl := .other }
    from rfl, hb, hseq]
  have hsh := endLabel_SR_shape TU (yR1 dm) (fun _ => .el0 Nat 5) (mv1 dm) (fun _ => .moved)
  dsimp only
  erw [if_pos (Attack.letGuard_noShape (Kc dm) φ _ hsh)]
  simp only [held_noShape' _ hsh]
  erw [if_pos (Attack.letGuard_noShape (Kc dm) φ _ (Attack.shape_letLenders_dropLast _ hsh))]
  exact ⟨_, rfl⟩

/-! ## `Id1(&y)` in place (`CallRef.runCallRef`) -/

/-- The caller's state with a callee's frame pushed in place (any `self`): `x` holds `c` at `y`'s
own label `0`. -/
def SPg (selfB : SBinding) (d : DeclInfo) (c r : Sem) : SState :=
  { env := [yFrame, SFrame.mk [selfB, xB c d] []],
    shape := fun p => if p = .bind 1 1 then some 0 else none, nextLoan := 1,
    lent := fun m => if m = 0 then [⟨.bind 0 0, [], false⟩] else [],
    heldTy := fun m => if m = 0 then yB.ty.m else TyM.err,
    heldMem := fun m => if m = 0 then r else .err }

section SPgLemmas
variable (selfB : SBinding) (d : DeclInfo)

theorem positions_SPg (c : Sem) : (SPg selfB d c r).positions = [.bind 0 0, .temp 0 0, .bind 1 0, .bind 1 1] := by
  simp [SPg, yFrame, SState.positions, List.range']

theorem liveLabels_SPg (c : Sem) : (SPg selfB d c r).liveLabels = [0] := by
  unfold SState.liveLabels; rw [positions_SPg]; simp [SPg]

theorem holderOf_SPg (c : Sem) : (SPg selfB d c r).holderOf 0 = some (.bind 1 1) := by
  unfold SState.holderOf; rw [positions_SPg]; simp [SPg]

theorem reached_SPg (c : Sem) (hit : List Step → Bool) (l : Nat) : (SPg selfB d c r).reached (.bind 1 1) hit l = false := by
  simp [SState.reached, SPg]

theorem access_SPg (c : Sem) (hit : List Step → Bool) : (SPg selfB d c r).access (.bind 1 1) hit = SPg selfB d c r := by
  unfold SState.access
  have h : ∀ n : Nat, (List.range n).foldl (fun s _ => (s.liveLabels.filter (s.reached (.bind 1 1) hit)).foldl SState.endLabel s)
      (SPg selfB d c r) = SPg selfB d c r := by
    intro n; induction n with
    | zero => rfl
    | succ n ih => rw [List.range_succ, List.foldl_append, ih]; simp [liveLabels_SPg, reached_SPg]
  exact h _

theorem typedFuture_SPg (c : Sem) (ψ : Future) : (SPg selfB d c r).typedFuture ψ = ψ.upd 0 r := by
  funext l; unfold SState.typedFuture; rw [liveLabels_SPg]
  by_cases hl : l = 0 <;> simp [hl, SPg, Future.upd]

theorem resolve_SPg (c : Sem) : resolve (SPg selfB d c r) (.deref (.var 0)) = some (.bind 1 1, [.deref]) := by
  simp [resolve, SState.varPos, SState.topIdx, Place.steps, SPg]

theorem contentOf_SPg (c : Sem) :
    ∃ T, contentOf (Kc dm) φ (.deref (.var 0)) (SPg selfB d c r) = some ((c, T, .bind 1 1, [.deref]), SPg selfB d c r) := by
  unfold contentOf
  rw [resolve_SPg]
  dsimp only
  rw [access_SPg, typedFuture_SPg]
  simp [Sem.follow, Sem.step, SState.valAt, SState.tyAt, SPg, xB]

theorem contentOf_SPg_nat (c : Sem) :
    ∃ T : TyS, T.m = TyM.nat ∧
      contentOf (Kc dm) φ (.deref (.var 0)) (SPg selfB d c r) = some ((c, T, .bind 1 1, [.deref]), SPg selfB d c r) := by
  unfold contentOf
  rw [resolve_SPg]
  dsimp only
  rw [access_SPg, typedFuture_SPg]
  simp [Sem.follow, Sem.step, SState.valAt, SState.tyAt, SPg, xB, TyS.plain]

/-- After `&*x` in place: `x` reads the reborrow `1`'s final content, the reborrow (content `c`) parked
in the callee's frame, lent at `*x`. -/
def SPg2 (T : TyM) (c r : Sem) : SState :=
  { env := [yFrame, SFrame.mk [selfB, { xB c d with val := fun φ' => φ' 1 }] [fun _ => c]],
    shape := fun p => if p = .temp 1 0 then some 1 else if p = .bind 1 1 then some 0 else none, nextLoan := 2,
    lent := fun m => if m = 1 then [⟨.bind 1 1, [.deref], false⟩] else if m = 0 then [⟨.bind 0 0, [], false⟩] else [],
    heldTy := fun m => if m = 1 then T else if m = 0 then yB.ty.m else TyM.err,
    heldMem := fun m => if m = 1 then c else if m = 0 then r else .err }

theorem contentOk_SPg (c : Sem) : ContentOk (Kc dm) φ (.deref (.var 0)) (SPg selfB d c r) := by
  unfold ContentOk; rw [resolve_SPg]
  exact Attack.accessOk_unreached _ φ fun l => reached_SPg (r := r) selfB d c _ l

theorem runBody_id1P (a : Nat) :
    ∃ T : TyS, T.label = some 1 ∧ ∀ (hint : TyS) (tl : Bool),
      runT (Kc dm) ρ φ tl hint id1Body (SPg selfB d (.el0 Nat a) r) = some ((.el0 Nat a, T), SPg2 selfB d T.m (.el0 Nat a) r) := by
  obtain ⟨T, hTm, hT⟩ := contentOf_SPg_nat (r := r) dm φ selfB d (.el0 Nat a)
  refine ⟨{ T with label := some 1 }, rfl, fun hint tl => ?_⟩
  simp only [id1Body, runT, SM.erasedIf, flags_Kc, Bool.false_eq_true, if_false, SM.stmtIf, SM.strictS,
    SM.guarded_of (contentOk_SPg (r := r) dm φ selfB d (.el0 Nat a))]
  unfold borrowPlace
  simp only [hT, bind, Option.bind]
  simp [Sem.whole, SState.freshLoan, SState.tyAt, SState.valAt, SState.setAt,
    Attack.updAt_deref, Attack.updAt_nil, SState.pushTempShaped, SState.pushTemp, SState.topIdx, SState.setLent, SState.setHeldTy, SState.setHeldMem, SPg, SPg2, xB]
  simp only [hTm]
  rw [if_pos ⟨a, rfl⟩]
  dsimp only
  simp only [Attack.invalidate_noInv (Kc dm) φ (fun _ _ => rfl)]
  rw [if_pos]
  exact ⟨Attack.invalidateOk_noInv (Kc dm) φ (fun _ _ => rfl) _ _, Attack.lentOk_deref (Kc dm) φ (pos := .bind 1 1) (by simp [resolve, SState.varPos, SState.topIdx, Ochr.Place.steps])⟩

/-- The pop where two labels are live: `l`, held in the callee's frame, ends; `k`, returned, is kept
and its holder moves to the caller's frame. -/
theorem popCallFrame_two (start : Nat) (s : SState) (l k f i : Nat) (r : Pos) (hl : s.liveLabels = [l, k])
    (hh : s.holderOf l = some (.bind f i)) (hf : f = s.topIdx) (hlk : l ≠ k) (hk : (s.endLabel l).holderOf k = some r) :
    popCallFrame start (some k) s =
      (SState.mk (s.endLabel l).env.dropLast
        (fun p => match p with
          | .bind g _ | .temp g _ => if g = s.topIdx then none else (s.endLabel l).shape p)
        (s.endLabel l).nextLoan (s.endLabel l).lent (s.endLabel l).heldTy (s.endLabel l).heldMem).pushTempShaped ((s.endLabel l).valAt r) k := by
  unfold popCallFrame popEnds
  have hne : (some l ≠ some k) := fun h => hlk (Option.some.inj h)
  simp only [hl, List.filter_cons, List.filter_nil, hh, hf, beq_self_eq_true, Bool.or_true, ne_eq, hne,
    not_false_eq_true, decide_true, Bool.and_self, if_true, not_true_eq_false, decide_false, Bool.and_false,
    Bool.false_eq_true, if_false, List.foldl_cons, List.foldl_nil, Option.bind_some, hk, Option.map_some]
  congr 1

theorem positions_SPg2 (T : TyM) (c : Sem) :
    (SPg2 selfB d T c r).positions = [.bind 0 0, .temp 0 0, .bind 1 0, .bind 1 1, .temp 1 0] := by
  simp [SPg2, yFrame, SState.positions, List.range']

theorem liveLabels_SPg2 (T : TyM) (c : Sem) : (SPg2 selfB d T c r).liveLabels = [0, 1] := by
  unfold SState.liveLabels; rw [positions_SPg2]; simp [SPg2]
  first | rfl | decide | simp [List.mergeSort]

theorem holderOf_SPg2 (T : TyM) (c : Sem) : (SPg2 selfB d T c r).holderOf 0 = some (.bind 1 1) := by
  unfold SState.holderOf; rw [positions_SPg2]; simp [SPg2]

theorem find_SPg2 (T : TyM) (c : Sem) :
    ((SPg2 selfB d T c r).positions.find? fun p => decide ((SPg2 selfB d T c r).shape p = some 0)) = some (.bind 1 1) := by
  rw [positions_SPg2]; simp [SPg2]

/-- Ending `x`'s label `0` at the pop, as `endLabel` computes it. -/
theorem endLabel_SPg2 (T : TyM) (c : Sem) : (SPg2 selfB d T c r).endLabel 0 =
    (let m := (SPg2 selfB d T c r).toMean.semEnd (.bind 1 1) 0
     ({ SPg2 selfB d T c r with shape := m.shape, lent := (SPg2 selfB d T c r).relend 0 (.bind 1 1) }).mapVals
       fun p _ => (m.val · p)) := by
  unfold SState.endLabel; rw [find_SPg2]

theorem holderOf_end_SPg2 (T : TyM) (c : Sem) : ((SPg2 selfB d T c r).endLabel 0).holderOf 1 = some (.temp 1 0) := by
  rw [endLabel_SPg2]
  unfold SState.holderOf
  simp [SState.positions, SState.mapVals, SPg2, yFrame, List.range', Mean.semEnd, SState.toMean]

end SPgLemmas

/-- `Id1`'s `self` in the callee's frame pushed in place. -/
noncomputable def selfId1P (cd : DeclInfo) : SBinding :=
  { ty := { (fresId1 dm ρ φ).2 with label := none }, val := fun _ => (fresId1 dm ρ φ).1, decl := .pi cd }

theorem callFrame_id1 (cd : DeclInfo) (bs : List PBind) (hb : bs = bindsOf (Kc dm) ρ φ (Attack.S₂ yB 0 (.el0 Nat 2)).pushFrame [.ref .nat]) :
    callFrame (Kc dm) ρ φ [] [] (fresId1 dm ρ φ) cd bs [(.el0 Nat 2, { yB.ty with label := some 0 })] (Attack.S₂ yB 0 (.el0 Nat 2))
      = SPg (selfId1P dm ρ φ cd) ((bs.getD 0 (fun _ => .plain TyM.err, .other)).2) (.el0 Nat 2) (.el0 Nat 2) := by
  subst hb
  simp [callFrame, capsState, capsVals, capsTys, SState.pushFrame, SState.pushBind, SState.topIdx, pushBindShaped,
    SState.takeLabel, SState.holderOf, SState.positions, List.range', Attack.S₂, SState.setAt, SPg, yFrame, selfId1P, xB,
    bindsOf, runBinds, mkBind]
  refine ⟨rfl, ?_⟩
  funext p
  by_cases h1 : p = Pos.bind 1 1 <;> by_cases h2 : p = Pos.temp 0 0 <;> simp [h1, h2]

-- `Id1(&y)` in place against `callOf` is `Regress/CallInPlaceD99.lean` (`id1_inPlace_typed`): since
-- D99 the call in place reserves the result's label before the body runs and renames the body's
-- returned borrow into it.

end Ochr.Meaning.Regress.CallInPlace

namespace Ochr.Meaning.Regress.CallInPlace

/-- **After (i') the failure of D67 is gone** at the position that showed it: in the reference's
state after `let y = 2; let r = Id1(&y)` the argument's consumed holder reads `moved` at every
future, so it no longer depends on the reborrow, which has no site there. (Before (i'), `callOf`'s
undecodable branch made it `err` where the reborrow's final content did not decode: docs/31 D67.) -/
theorem consumed_holder_constant (dm : DataModel) (TU : TyS) (ψ : Future) :
    (SR TU (yR1 dm) (fun _ => .el0 Nat 2) (mv1 dm) (fun _ => .moved)).valAt (.temp 0 0) ψ = .moved := by
  simp only [SR, SState.valAt]
  show (match Code0.dec dm.read TyM.nat.code0.snd (ψ 1) with | some _ => Sem.moved | none => Sem.moved) = _
  cases Code0.dec dm.read TyM.nat.code0.snd (ψ 1) <;> rfl

end Ochr.Meaning.Regress.CallInPlace
