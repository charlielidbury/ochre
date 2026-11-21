import Ochr.Meaning.Attack.RunEqs
import Ochr.Meaning.Lemmas
import Ochr.Meaning.Mono
import Ochr.Meaning.Locality

/-!
# CE4, flipped: a positive check for the proposed `callOfL` (built)

`CE4_5dc7710b.lean` (unbuilt) records the leak: `callOfL` took the holder of every labelled
argument but fixed only `labels.zip finals`, so a borrow passed at a non-borrow parameter was
never ended. With the proposed `callOfL` (only the arguments at borrow parameters are consumed
and fixed), `let y = Z; (f(&y); y)`, `f` the identity `Π(x : Nat). Nat`, reads `Z` at every future
(`tF_reads_zero`): the borrow stays parked and the read of `y` ends it (`access_a4`). Axioms:
propext, Classical.choice, Quot.sound.
-/

namespace Ochr.Meaning.Regress.CE4flip
open Ochr.Meaning
open Classical

theorem filterMap_none {α β} (l : List α) : List.filterMap (fun _ => (none : Option β)) l = [] := by
  induction l <;> simp_all [List.filterMap]

theorem liveLabels_noshape (s : SState) (h : s.shape = fun _ => none) : s.liveLabels = [] := by
  simp only [SState.liveLabels, h, filterMap_none, List.mergeSort_nil]

theorem access_noshape (s : SState) (p : Pos) (h : s.shape = fun _ => none) (hit : List Step → Bool := fun _ => true) :
    s.access p hit = s := by
  simp [SState.access, liveLabels_noshape s h]

theorem SM.bind_apply {α β : Type 3} (x : SM α) (f : α → SM β) (s : SState) :
    (x >>= f) s = match x s with | some (a, s') => f a s' | none => none := rfl

/-- `f : Π(x : Nat). Nat`, the identity, as a global at its type's code. -/
abbrev FCar : Type := (n : Nat) → Nat × PUnit
def telF : Tel Code0 PUnit FCar := .param PUnit false Nat .nat (fun _ => Nat × PUnit) fun _ => .dat PUnit Nat .nat
def Fid : FCar := fun a => (a, ⟨⟩)

noncomputable def KF : RunCtx :=
  { JoinDropCounterexample.K with
    C := { JoinDropCounterexample.K.C with
      global := fun _ => (.el0 FCar Fid, .plain (.t0 FCar (.pi FCar telF))) } }

/-- `let y = Z; (f(&y); y)`: the borrow goes to a non-borrow parameter. -/
def tF : Term := .letIn ⟨"y"⟩ .zero (.seq (.call (.const "f") [.borrow (.var 0)] false) (.place (.var 0)))

section
variable (ρ : Assignment) (φ : Future)

theorem applyFn_F (R : DataRead) : applyFnL (lvl0 R) telF (.el0 FCar Fid) [.el0 Nat 0]
    = some (.data (.el0 Nat 0) ((lvl0 R).toTy Code0.nat) []) := by
  have hu : Sem.as FCar (.el0 FCar Fid) = some Fid := by simp [Sem.as]
  have h2 : Code0.nat.dec R (.el0 Nat 0) = some (0 : Nat) := Code0.dec_enc R .nat 0
  simp only [applyFnL, lvl0, hu, Option.bind_some, telF, applyTelL, h2]
  rfl

variable (K : RunCtx)

/-- The decisions classify no term as a statement, so `SM.stmtIf` is the run itself (D19: every
clause that can change the state runs under `Decisions.flags`). True of `KF` by `rfl`. -/
def NoStmt (K : RunCtx) : Prop := ∀ sc t, K.D.flags sc t = (false, false)

theorem stmtIf_noStmt (hfl : NoStmt K) (t : Term) (x : SM Res) (s : SState) :
    SM.erasedIf (K.D.flags (scopeOf s) t) x s = x s := by
  rw [hfl]; rfl

theorem run_letIn (hfl : NoStmt K) (h : Hint) (u w : Term) (hint : TyS) (s : SState) :
    run K ρ φ hint (.letIn h u w) s = (run K ρ φ (.plain .err) u s).bind (fun x =>
      (run K ρ φ hint w (pushBindShaped x.2 { ty := x.1.2, val := fun _ => x.1.1, decl := K.D.declOf (scopeOf s) u })).bind
        fun y => if (match (match y.2.env.getLast? with
            | some fr => y.2.shape (.bind y.2.topIdx (fr.binds.length - 1))
            | none => none) with
          | some l => EndOk K φ y.2 l | none => LetLendersOk K φ y.2) then
          some (y.1, (match (match y.2.env.getLast? with
            | some fr => y.2.shape (.bind y.2.topIdx (fr.binds.length - 1))
            | none => none) with
          | some l => y.2.endLabel l | none => letLenders y.2).dropLast) else none) := by
  rw [run, runT]; exact stmtIf_noStmt K hfl _ _ s

/-- The [Drop] of a discarded value that holds no borrow does nothing. -/
theorem seq_discard_plain (T : TyM) (k : SM Res) (s : SState) :
    (SM.guardMod (DiscardOk K φ (TyS.plain T)) (discardEnd (TyS.plain T)) >>= fun _ => k) s = k s := by
  have h : DiscardOk K φ (TyS.plain T) s := trivial
  have e : SM.guardMod (DiscardOk K φ (TyS.plain T)) (discardEnd (TyS.plain T)) s = some (⟨⟩, s) := by
    unfold SM.guardMod; rw [if_pos h]; rfl
  rw [SM.bind_apply, e]

theorem run_seq (hfl : NoStmt K) (u w : Term) (hint : TyS) (s : SState) :
    run K ρ φ hint (.seq u w) s =
      (run K ρ φ (.plain .err) u >>= fun r => SM.guardMod (DiscardOk K φ r.2) (discardEnd r.2) >>= fun _ => run K ρ φ hint w) s := by
  rw [run, runT]; exact stmtIf_noStmt K hfl _ _ s

theorem run_place (hfl : NoStmt K) (p : Place) (hint : TyS) (s : SState) :
    run K ρ φ hint (.place p) s = SM.guarded (ContentOk K φ p) (readPlace K φ p (K.D.copy (K.D.placeDecl (scopeOf s) p))) s := by
  rw [run, runT]; exact stmtIf_noStmt K hfl _ _ s

theorem run_borrow (hfl : NoStmt K) (p : Place) (hint : TyS) (s : SState) :
    run K ρ φ hint (.borrow p) s = (match SM.strictS K.dm.read (SM.guarded (ContentOk K φ p) (borrowPlace K φ p)) s with
      | some (r, s₁) =>
        let s₂ := invalidate K φ p s₁
        if InvalidateOk K φ p s₁ ∧ lentOk K φ p s₂ then some (r, s₂) else none
      | none => none) := by
  rw [run, runT]; exact stmtIf_noStmt K hfl _ _ s

theorem readPlace_of (p : Place) (b : Bool) (s : SState) (v : Sem) (T : TyS) (pos : Pos) (st : List Step)
    (s' : SState) (h : contentOf K φ p s = some ((v, T, pos, st), s')) :
    readPlace K φ p b s = ((if ¬ v.whole then none else
      if ¬ ReadGood K.dm.read T.m v then none else
      if b then some ((v, { T with label := none }), s') else do
        let lab := if st.isEmpty then s'.shape pos else none
        let (⟨⟩, s) ← setContent K φ pos st .moved s'
        let s := match lab with
          | some l => (s.takeLabel l).pushTempShaped (fun _ => v) l
          | none => s
        some ((v, { T with label := lab }), s)) : Option (Res × SState)) := by
  show (contentOf K φ p s >>= _) = _
  rw [h]
  rfl

/-- The empty state at counter `n` with `y = Z` bound. -/
noncomputable def a1 (n : Nat) : SState :=
  pushBindShaped (emptyState n) { ty := .plain TyM.nat, val := fun _ => .el0 Nat 0, decl := K.D.declOf (scopeOf (emptyState n)) .zero }

theorem content_a1 (n : Nat) : contentOf K φ (.var 0) (a1 K n) = some ((.el0 Nat 0, .plain TyM.nat, .bind 0 0, []), a1 K n) := by
  have hr : resolve (a1 K n) (.var 0) = some (.bind 0 0, []) := rfl
  simp only [contentOf, hr, access_noshape _ _ (rfl : (a1 K n).shape = _) _]
  rfl

/-- After `&y` at counter `n`: `y` reads label `n`, and the borrow is parked in temporary `0`. -/
noncomputable def a2 (n : Nat) : SState :=
  { env := [{ binds := [{ ty := .plain TyM.nat,
                          val := fun φ' => (Sem.updAt K.dm K.Γ (.plain TyM.nat) (fun _ => φ' n) [] (Sem.el0 Nat 0)).getD .err,
                          decl := K.D.declOf (scopeOf (emptyState n)) .zero }],
              temps := [fun _ => .el0 Nat 0] }],
    shape := fun p => if p = .temp 0 0 then some n else none,
    nextLoan := n + 1,
    lent := fun m => if m = n then [⟨.bind 0 0, [], false⟩] else [],
    heldTy := fun m => if m = n then TyM.nat else TyM.err,
    heldMem := fun m => if m = n then .el0 Nat 0 else .err }

theorem live_a1 (n : Nat) : (a1 K n).liveLabels = [] := by
  unfold a1; exact liveLabels_noshape _ rfl

theorem contentOk_a1 (n : Nat) : ContentOk K φ (.var 0) (a1 K n) :=
  by
    unfold ContentOk; split
    · exact Ochr.Meaning.Attack.accessOk_noLive K φ (live_a1 K n) _ _
    · trivial

theorem borrow_a1 (n : Nat) : borrowPlace K φ (.var 0) (a1 K n) = some ((.el0 Nat 0, { TyS.plain TyM.nat with label := some n }), a2 K n) := by
  show (match contentOf K φ (.var 0) (a1 K n) with
      | some ((v, T, pos, steps), s) =>
        if ¬ v.whole then none else
        let (l, s) := s.freshLoan
        let T0 := s.tyAt pos
        let old := s.valAt pos
        let s := s.setAt pos fun φ' => (Sem.updAt K.dm K.Γ T0 (fun _ => φ' l) steps (old φ')).getD .err
        let s := s.pushTempShaped (fun _ => v) l
        some ((v, { T with label := some l }), ((s.setLent l [⟨pos, steps, false⟩]).setHeldTy l T.m).setHeldMem l v)
      | none => none) = _
  rw [content_a1]
  simp only [Sem.whole, not_true_eq_false, ite_false]
  rfl

/-- The strict borrow of `y`: `Z` is a `Nat`. -/
theorem strictBorrow_a1 (n : Nat) : SM.strictS K.dm.read (borrowPlace K φ (.var 0)) (a1 K n)
    = some ((.el0 Nat 0, { TyS.plain TyM.nat with label := some n }), a2 K n) := by
  simp only [SM.strictS]
  rw [borrow_a1]
  dsimp only
  rw [if_pos ⟨(0 : Nat), rfl⟩]

theorem strictBorrow_a1g (n : Nat) :
    SM.strictS K.dm.read (SM.guarded (ContentOk K φ (.var 0)) (borrowPlace K φ (.var 0))) (a1 K n)
    = some ((.el0 Nat 0, { TyS.plain TyM.nat with label := some n }), a2 K n) := by
  simp only [SM.strictS, SM.guarded_of (contentOk_a1 φ K n)]
  exact strictBorrow_a1 φ K n ▸ (by simp only [SM.strictS])

theorem positions_a2 (n : Nat) : (a2 K n).positions = [.bind 0 0, .temp 0 0] := by
  simp [SState.positions, a2]

theorem holder_a2 (n : Nat) : (a2 K n).holderOf n = some (.temp 0 0) := by
  unfold SState.holderOf
  rw [positions_a2]
  simp [a2]


theorem noStmt_KF : NoStmt KF := fun _ _ => rfl

theorem run_call_KF (f : Term) (args : List Term) (hd : Bool) (hint : TyS) (s : SState) :
    run KF ρ φ hint (.call f args hd) s
      = (SM.headOf f (fun p => SM.guarded (ContentOk KF φ p) (readPlace KF φ p true)) (run KF ρ φ (.plain .err) f) >>= fun fv =>
          runArgs KF ρ φ false fv.2.m [] args >>= fun as =>
            fun s => if BorrowArgsTyped KF.dm.read fv as s then callOf KF.dm.read fv as s else none) s := rfl

theorem runArgs_borrow (n : Nat) :
    runArgs KF ρ φ false (.t0 FCar (.pi FCar telF)) [] [.borrow (.var 0)] (a1 KF n)
      = some ([(.el0 Nat 0, { TyS.plain TyM.nat with label := some n })], a2 KF n) := by
  show (run KF ρ φ (.plain ((TyM.t0 FCar (.pi FCar telF)).domAfter KF.dm.read [])) (.borrow (.var 0)) >>= fun r =>
      runArgs KF ρ φ false (.t0 FCar (.pi FCar telF)) ([] ++ [r.1]) [] >>= fun rest => pure (r :: rest)) (a1 KF n) = _
  rw [SM.bind_apply, run_borrow ρ φ KF noStmt_KF, strictBorrow_a1g]
  have hi : invalidate KF φ (.var 0) (a2 KF n) = a2 KF n := rfl
  have hl : lentOk KF φ (.var 0) (a2 KF n) := by
    have hr : resolve (a2 KF n) (.var 0) = some (.bind 0 0, []) := rfl
    simp [lentOk, hr]
  have hv := Ochr.Meaning.Attack.invalidateOk_noInv KF φ (fun _ _ => rfl) (.var 0) (a2 KF n)
  simp only [hi, if_pos (And.intro hv hl)]
  rfl

/-- After the call (proposed `callOfL`): the borrow at the non-borrow parameter stays parked. -/
noncomputable def a4 (n : Nat) : SState := (a2 KF n).mapVals fun _ v φ' => v (φ'.updList [])

theorem call_a1 (n : Nat) :
    run KF ρ φ (.plain .err) (.call (.const "f") [.borrow (.var 0)] false) (a1 KF n)
      = some ((.el0 Nat 0, .plain TyM.nat), a4 n) := by
  rw [run_call_KF, SM.bind_apply]
  show (runArgs KF ρ φ false (.t0 FCar (.pi FCar telF)) [] [.borrow (.var 0)] >>= fun as =>
    fun s => if BorrowArgsTyped KF.dm.read _ as s then callOf KF.dm.read _ as s else none) (a1 KF n) = _
  rw [SM.bind_apply, runArgs_borrow]
  have hr0 : telRefsL (lvl0 KF.dm.read) telF [Sem.el0 Nat 0] = [false] := by
    simp [telRefsL, telF, show Code0.nat.dec KF.dm.read (.el0 Nat 0) = some (0 : Nat) from Code0.dec_enc _ .nat 0]
  -- the borrow is at a non-borrow parameter: no label to test
  have hb : BorrowArgsTyped KF.dm.read (.el0 FCar Fid, .plain (.t0 FCar (.pi FCar telF)))
      [(.el0 Nat 0, { TyS.plain TyM.nat with label := some n })] (a2 KF n) := by
    intro i l h
    simp [refLabelsOf, refsOf, TyS.plain, hr0] at h
  rw [show KF.C.global "f" = (.el0 FCar Fid, .plain (.t0 FCar (.pi FCar telF))) from rfl]
  dsimp only
  rw [if_pos hb]
  show callOfL (lvl0 KF.dm.read) telF (.el0 FCar Fid)
    [(.el0 Nat 0, { TyS.plain TyM.nat with label := some n })] (a2 KF n) = _
  have hr : telRefsL (lvl0 KF.dm.read) telF [Sem.el0 Nat 0] = [false] := by
    simp [telRefsL, telF, show Code0.nat.dec KF.dm.read (.el0 Nat 0) = some (0 : Nat) from Code0.dec_enc _ .nat 0]
  unfold callOfL
  simp only [List.map_cons, List.map_nil, applyFn_F, hr]
  rfl

theorem positions_a4 (n : Nat) : (a4 n).positions = [.bind 0 0, .temp 0 0] := by
  unfold a4; rw [SState.positions_mapVals, positions_a2]

theorem liveLabels_a4 (n : Nat) : (a4 n).liveLabels = [n] := by
  unfold SState.liveLabels; rw [positions_a4]
  simp [a4, SState.mapVals, a2]

theorem holder_a4 (n : Nat) : (a4 n).holderOf n = some (.temp 0 0) := by
  unfold SState.holderOf; rw [positions_a4]; simp [a4, SState.mapVals, a2]

theorem a4_y (n : Nat) (ψ : Future) : (a4 n).valAt (.bind 0 0) ψ = ψ n := rfl
theorem a4_t (n : Nat) (ψ : Future) : (a4 n).valAt (.temp 0 0) ψ = .el0 Nat 0 := rfl

theorem access_a4 (n : Nat) (hit : List Step → Bool) (ho : hit [] = true) :
    (a4 n).access (.bind 0 0) hit = (a4 n).endAt n (.temp 0 0) := by
  have hd : (a4 n).reached (.bind 0 0) hit n = true := by
    simp [SState.reached, a4, SState.mapVals, a2, ho]
  rw [SState.access_eq, liveLabels_a4]
  show SState.accStep (.bind 0 0) hit (a4 n) = _
  unfold SState.accStep
  rw [liveLabels_a4]
  simp only [List.filter_cons, List.filter_nil, hd, if_true, List.foldl_cons, List.foldl_nil]
  exact SState.endLabel_eq (holder_a4 n)

theorem endOk_a4 (n : Nat) : EndOk KF φ (a4 n) n := by
  intro r hr ψ _
  rw [holder_a4] at hr
  cases hr
  rw [a4_t]
  show Sem.el0 Nat 0 ∈ₛ[KF.dm.read] (if n = n then TyM.nat else TyM.err)
  rw [if_pos rfl]; exact ⟨(0 : Nat), rfl⟩

theorem contentOk_a4 (n : Nat) : ContentOk KF φ (.var 0) (a4 n) := by
  have hr : resolve (a4 n) (.var 0) = some (.bind 0 0, []) := rfl
  have hd : (a4 n).reached (.bind 0 0) (dataHit []) n = true := by
    simp [SState.reached, a4, SState.mapVals, a2, dataHit]
  unfold ContentOk; rw [hr]
  intro k hk
  rw [liveLabels_a4] at hk
  have hk0 : k = 0 := by simpa using hk
  subst hk0
  simp only [List.range_zero, List.foldl_nil, liveLabels_a4, List.filter_cons, List.filter_nil, hd, if_true]
  exact ⟨endOk_a4 φ n, trivial⟩

theorem content_a4 (n : Nat) : contentOf KF φ (.var 0) (a4 n)
    = some ((.el0 Nat 0, .plain TyM.nat, .bind 0 0, []), (a4 n).endAt n (.temp 0 0)) := by
  have hr : resolve (a4 n) (.var 0) = some (.bind 0 0, []) := rfl
  simp only [contentOf, hr, access_a4 n (dataHit []) rfl]
  rw [SState.endAt_valAt _ _ _ _ (by rw [positions_a4]; simp)]
  simp only [show (Pos.bind 0 0 = Pos.temp 0 0) = False from by simp, if_false, a4_t, a4_y, Future.upd, if_true]
  rfl

/-- A state with no shape has no live label, so the `let`'s end passes its test. -/
theorem guard_noShape (s : SState) (h : s.shape = fun _ => none) :
    (match (match s.env.getLast? with
      | some fr => s.shape (.bind s.topIdx (fr.binds.length - 1))
      | none => none) with
    | some l => EndOk KF φ s l | none => LetLendersOk KF φ s) := by
  have hl := liveLabels_noshape s h
  cases hg : s.env.getLast? with
  | none => show LetLendersOk KF φ s; unfold LetLendersOk; rw [hg]; trivial
  | some fr =>
    simp only [h]
    show LetLendersOk KF φ s
    unfold LetLendersOk; rw [hg]
    exact Ochr.Meaning.Attack.accessOk_noLive KF φ hl _ _

theorem shape_E (n : Nat) : ((a4 n).endAt n (.temp 0 0)).shape = fun _ => none := by
  rw [SState.endAt_shape]
  funext p
  by_cases hp : p = .temp 0 0
  · simp [hp]
  · simp [hp, a4, SState.mapVals, a2]

/-- With the proposed `callOfL`, `let y = Z; (f(&y); y)` reads `Z` at every future: the borrow at
the non-borrow parameter stays parked, and the read of `y` ends it (CE4, flipped). -/
theorem tF_reads_zero (n : Nat) (hint : TyS) : ∃ T s', run KF ρ φ hint tF (emptyState n) = some ((.el0 Nat 0, T), s') := by
  rw [tF, run_letIn ρ φ KF noStmt_KF]
  have h0 : run KF ρ φ (.plain .err) .zero (emptyState n) = some ((.el0 Nat 0, .plain TyM.nat), emptyState n) := rfl
  rw [h0]
  simp only [Option.bind]
  rw [show pushBindShaped (emptyState n) _ = a1 KF n from rfl, run_seq ρ φ KF noStmt_KF, SM.bind_apply, call_a1]
  simp only
  rw [seq_discard_plain]
  rw [run_place ρ φ KF noStmt_KF]
  have hc := content_a4 φ n
  rw [SM.guarded_of (contentOk_a4 φ n), readPlace_of φ KF _ _ _ _ _ _ _ _ hc]
  have hm : ReadGood KF.dm.read (TyS.plain TyM.nat).m (Sem.el0 Nat 0) := Or.inl ⟨(0 : Nat), rfl⟩
  simp only [Sem.whole, not_true_eq_false, ite_false, hm, not_true_eq_false]
  generalize KF.D.copy _ = b
  cases b
  · simp only [Bool.false_eq_true, ite_false, List.isEmpty_nil, ite_true, SState.endAt_shape,
      show (Pos.bind 0 0 = Pos.temp 0 0) = False from by simp]
    rw [setContent_root KF φ _ _ _ (Or.inl rfl)]
    have hsn : (a4 n).shape (.bind 0 0) = none := rfl
    simp only [bind, Option.bind, hsn]
    rw [if_pos (guard_noShape φ _ (by simpa [SState.setAt] using shape_E n))]
    exact ⟨_, _, rfl⟩
  · simp only [bind, Option.bind, if_true, ite_true]
    rw [if_pos (guard_noShape φ _ (shape_E n))]
    exact ⟨_, _, rfl⟩
end

end Ochr.Meaning.Regress.CE4flip
