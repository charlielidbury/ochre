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

theorem access_noshape (s : SState) (p : Pos) (h : s.shape = fun _ => none) (o : Sem → Sem := id) : s.access p o = s := by
  simp [SState.access, liveLabels_noshape s h]

theorem SM.bind_apply {α β : Type 3} (x : SM α) (f : α → SM β) (s : SState) :
    (x >>= f) s = match x s with | some (a, s') => f a s' | none => none := rfl

/-- `f : Π(x : Nat). Nat`, the identity, as a global with its shape. -/
abbrev psF : List PiParam := [⟨false, fun _ => .ty0 Nat, fun _ => none⟩]
abbrev outF : PiOut := .data fun _ => .ty0 Nat
def Fid : piCarL lvl0 psF [] PUnit outF := fun a => (a, ⟨⟩)

noncomputable def KF : RunCtx :=
  { JoinDropCounterexample.K with
    C := { JoinDropCounterexample.K.C with
      global := fun _ => (.el0 (piCarL lvl0 psF [] PUnit outF) Fid, ⟨.err, some (psF, outF), none, none⟩) } }

/-- `let y = Z; (f(&y); y)`: the borrow goes to a non-borrow parameter. -/
def tF : Term := .letIn ⟨"y"⟩ .zero (.seq (.call (.const "f") [.borrow (.var 0)] false) (.place (.var 0)))

section
variable (ρ : Assignment) (φ : Future)

theorem applyFn_F : applyFnL lvl0 psF outF (.el0 (piCarL lvl0 psF [] PUnit outF) Fid) [.el0 Nat 0]
    = some (.data (.el0 Nat 0) []) := by
  simp only [applyFnL]
  have h1 : lvl0.unpack (piCarL lvl0 psF [] PUnit outF) (.el0 (piCarL lvl0 psF [] PUnit outF) Fid) = some Fid := by
    exact lvl0_unpack_pack _ Fid
  rw [h1]
  show applyTeleL lvl0 psF [] PUnit (fun _ => []) outF Fid [.el0 Nat 0] = _
  have h2 : lvl0.dec (TyM.ty0 Nat) (.el0 Nat 0) = some (0 : Nat) := TyM.dec0_enc0 (.ty0 Nat) (0 : Nat)
  rw [applyTeleL]
  simp only [h2]
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
      (run K ρ φ hint w (pushBindShaped x.2 { ty := x.1.2, val := fun _ => x.1.1, decl := K.D.declOf (scopeOf x.2) u })).bind
        fun y => some (y.1, (match (match y.2.env.getLast? with
            | some fr => y.2.shape (.bind y.2.topIdx (fr.binds.length - 1))
            | none => none) with
          | some l => y.2.endLabel l | none => y.2).dropLast)) := by
  rw [run]; exact stmtIf_noStmt K hfl _ _ s

theorem run_seq (hfl : NoStmt K) (u w : Term) (hint : TyS) (s : SState) :
    run K ρ φ hint (.seq u w) s = (run K ρ φ (.plain .err) u >>= fun _ => run K ρ φ hint w) s := by
  rw [run]; exact stmtIf_noStmt K hfl _ _ s

theorem run_place (hfl : NoStmt K) (p : Place) (hint : TyS) (s : SState) :
    run K ρ φ hint (.place p) s = readPlace K φ p (K.D.copy (K.D.placeDecl (scopeOf s) p)) s := by
  rw [run]; exact stmtIf_noStmt K hfl _ _ s

theorem run_borrow (hfl : NoStmt K) (p : Place) (hint : TyS) (s : SState) :
    run K ρ φ hint (.borrow p) s = borrowPlace K φ p s := by
  rw [run]; exact stmtIf_noStmt K hfl _ _ s

theorem readPlace_of (p : Place) (b : Bool) (s : SState) (v : Sem) (T : TyS) (pos : Pos) (st : List Step)
    (s' : SState) (h : contentOf K φ p s = some ((v, T, pos, st), s')) :
    readPlace K φ p b s = ((if ¬ v.whole then none else
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
  pushBindShaped (emptyState n) { ty := .plain (.ty0 Nat), val := fun _ => .el0 Nat 0, decl := K.D.declOf (scopeOf (emptyState n)) .zero }

theorem content_a1 (n : Nat) : contentOf K φ (.var 0) (a1 K n) = some ((.el0 Nat 0, .plain (.ty0 Nat), .bind 0 0, []), a1 K n) := by
  have hr : resolve (a1 K n) (.var 0) = some (.bind 0 0, []) := rfl
  simp only [contentOf, hr, access_noshape _ _ (rfl : (a1 K n).shape = _) _]
  rfl

/-- After `&y` at counter `n`: `y` reads label `n`, and the borrow is parked in temporary `0`. -/
noncomputable def a2 (n : Nat) : SState :=
  { env := [{ binds := [{ ty := .plain (.ty0 Nat),
                          val := fun φ' => (Sem.updAt K.dm K.Γ (.ty0 Nat) (fun _ => φ' n) [] (Sem.el0 Nat 0)).getD .err,
                          decl := K.D.declOf (scopeOf (emptyState n)) .zero }],
              temps := [fun _ => .el0 Nat 0] }],
    shape := fun p => if p = .temp 0 0 then some n else none,
    nextLoan := n + 1 }

theorem borrow_a1 (n : Nat) : borrowPlace K φ (.var 0) (a1 K n) = some ((.el0 Nat 0, { TyS.plain (.ty0 Nat) with label := some n }), a2 K n) := by
  show (match contentOf K φ (.var 0) (a1 K n) with
      | some ((v, T, pos, steps), s) =>
        if ¬ v.whole then none else
        let (l, s) := s.freshLoan
        let T0 := (s.tyAt pos).m
        let old := s.valAt pos
        let s := s.setAt pos fun φ' => (Sem.updAt K.dm K.Γ T0 (fun _ => φ' l) steps (old φ')).getD .err
        let s := s.pushTempShaped (fun _ => v) l
        some ((v, { T with label := some l }), s)
      | none => none) = _
  rw [content_a1]
  simp only [Sem.whole, not_true_eq_false, ite_false]
  rfl

theorem positions_a2 (n : Nat) : (a2 K n).positions = [.bind 0 0, .temp 0 0] := by
  simp [SState.positions, a2]

theorem holder_a2 (n : Nat) : (a2 K n).holderOf n = some (.temp 0 0) := by
  unfold SState.holderOf
  rw [positions_a2]
  simp [a2]


theorem noStmt_KF : NoStmt KF := fun _ _ => rfl

theorem run_call_KF (f : Term) (args : List Term) (hd : Bool) (hint : TyS) (s : SState) :
    run KF ρ φ hint (.call f args hd) s
      = (SM.headOf f (fun p => readPlace KF φ p true) (run KF ρ φ (.plain .err) f) >>= fun fv =>
          runArgs KF ρ φ false fv.2.shape 0 [] args >>= fun as => callOf fv as) s := rfl

theorem runArgs_borrow (n : Nat) :
    runArgs KF ρ φ false (some (psF, outF)) 0 [] [.borrow (.var 0)] (a1 KF n)
      = some ([(.el0 Nat 0, { TyS.plain (.ty0 Nat) with label := some n })], a2 KF n) := by
  show (run KF ρ φ (.plain (TyM.ty0 Nat)) (.borrow (.var 0)) >>= fun r =>
      runArgs KF ρ φ false (some (psF, outF)) 1 ([] ++ [r.1]) [] >>= fun rest => pure (r :: rest)) (a1 KF n) = _
  rw [SM.bind_apply, run_borrow ρ φ KF noStmt_KF, borrow_a1]
  rfl

/-- After the call (proposed `callOfL`): the borrow at the non-borrow parameter stays parked. -/
noncomputable def a4 (n : Nat) : SState := (a2 KF n).mapVals fun _ v φ' => v (φ'.updList [])

theorem call_a1 (n : Nat) :
    run KF ρ φ (.plain .err) (.call (.const "f") [.borrow (.var 0)] false) (a1 KF n)
      = some ((.el0 Nat 0, .plain (.ty0 Nat)), a4 n) := by
  rw [run_call_KF, SM.bind_apply]
  show (runArgs KF ρ φ false (some (psF, outF)) 0 [] [.borrow (.var 0)] >>= fun as => callOf _ as) (a1 KF n) = _
  rw [SM.bind_apply, runArgs_borrow]
  show callOfL lvl0 psF outF (.el0 (piCarL lvl0 psF [] PUnit outF) Fid)
    [(.el0 Nat 0, { TyS.plain (.ty0 Nat) with label := some n })] (a2 KF n) = _
  unfold callOfL
  simp only [List.map_cons, List.map_nil, applyFn_F]
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

/-- The whole-content observation of a root tells `Z` from `err`. -/
theorem wholeOb_root_ne (K : RunCtx) (T : TyM) : obsAt K T [] wholeOb (.el0 Nat 0) ≠ obsAt K T [] wholeOb .err := by
  simp [obsAt, Sem.follow, wholeOb]

theorem access_a4 (n : Nat) (o : Sem → Sem) (ho : o (.el0 Nat 0) ≠ o .err) :
    (a4 n).access (.bind 0 0) o = (a4 n).endAt n (.temp 0 0) := by
  have hd : (a4 n).obsDep (.bind 0 0) o n := by
    rw [SState.obsDep_iff]
    intro hi
    have := hi (fun _ => .el0 Nat 0) .err
    simp only [a4_y] at this
    simp [Future.upd] at this
    exact ho this.symm
  rw [SState.access_eq, liveLabels_a4]
  show SState.accStep (.bind 0 0) o (a4 n) = _
  unfold SState.accStep
  rw [liveLabels_a4]
  simp only [List.filter_cons, List.filter_nil, decide_eq_true hd, if_true, List.foldl_cons, List.foldl_nil]
  exact SState.endLabel_eq (holder_a4 n)

theorem content_a4 (n : Nat) : ∃ T, contentOf KF φ (.var 0) (a4 n)
    = some ((.el0 Nat 0, T, .bind 0 0, []), (a4 n).endAt n (.temp 0 0)) := by
  have hr : resolve (a4 n) (.var 0) = some (.bind 0 0, []) := rfl
  simp only [contentOf, hr, access_a4 n _ (wholeOb_root_ne KF _)]
  rw [SState.endAt_valAt _ _ _ _ (by rw [positions_a4]; simp)]
  simp only [show (Pos.bind 0 0 = Pos.temp 0 0) = False from by simp, if_false, a4_t, a4_y, Future.upd, if_true]
  exact ⟨_, rfl⟩

/-- With the proposed `callOfL`, `let y = Z; (f(&y); y)` reads `Z` at every future: the borrow at
the non-borrow parameter stays parked, and the read of `y` ends it (CE4, flipped). -/
theorem tF_reads_zero (n : Nat) (hint : TyS) : ∃ T s', run KF ρ φ hint tF (emptyState n) = some ((.el0 Nat 0, T), s') := by
  rw [tF, run_letIn ρ φ KF noStmt_KF]
  have h0 : run KF ρ φ (.plain .err) .zero (emptyState n) = some ((.el0 Nat 0, .plain (.ty0 Nat)), emptyState n) := rfl
  rw [h0]
  simp only [Option.bind]
  rw [show pushBindShaped (emptyState n) _ = a1 KF n from rfl, run_seq ρ φ KF noStmt_KF, SM.bind_apply, call_a1]
  simp only
  rw [run_place ρ φ KF noStmt_KF]
  obtain ⟨T, hc⟩ := content_a4 φ n
  rw [readPlace_of φ KF _ _ _ _ _ _ _ _ hc]
  simp only [Sem.whole, not_true_eq_false, ite_false]
  generalize KF.D.copy _ = b
  cases b
  · simp only [Bool.false_eq_true, ite_false, List.isEmpty_nil, ite_true, SState.endAt_shape,
      show (Pos.bind 0 0 = Pos.temp 0 0) = False from by simp]
    exact ⟨_, _, rfl⟩
  · exact ⟨_, _, rfl⟩
end

end Ochr.Meaning.Regress.CE4flip
