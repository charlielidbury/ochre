import Ochr.Meaning.Lemmas
import Ochr.Meaning.Mono

/-
  Ochr.Meaning.Regress.CE4_5dc7710b: m2-proofs' Lean-checked counterexample (round 4), valid against
  `spine` 1d886ace, 3b089b08 and 5dc7710b. NOT built (not imported by `Ochr/Meaning.lean`): it
  refutes the current statements and is to flip into a positive check once `callOfL` is fixed. To
  re-check it: `lake env lean` on it from `ochr/core/lean` at 5dc7710b. Axioms: propext,
  Classical.choice, Quot.sound.

  `callOfL` takes the holder of *every* labelled argument (`labels.foldl takeLabel`) but fixes only
  `labels.zip finals`, one final per borrow parameter: a borrow passed at a non-borrow parameter
  loses its holder and is never ended. With `KF` (Mono's JoinDropCounterexample.K with the global
  `f` the identity `Π(x : Nat). Nat`), `tF = let y = Z; (f(&y); y)` reads `φ n` at the run's own
  label `n` (`run_tF`). Refutes `run_congr` (`run_congr_false`) and `meanV_congr`
  (`meanV_congr_false`). Proposed fix: pair arguments with parameters and take and fix only the
  labels of arguments at borrow parameters (`(pairs.zip finals)` over the borrow-parameter pairs).
-/

/-! Round 4 (spine 1d886ace, D14/D15): a borrow passed at a non-borrow parameter. -/

namespace Ochr.Meaning.Regress.CE4
open Ochr.Meaning
open Classical

theorem filterMap_none {α β} (l : List α) : List.filterMap (fun _ => (none : Option β)) l = [] := by
  induction l <;> simp_all [List.filterMap]

theorem liveLabels_noshape (s : SState) (h : s.shape = fun _ => none) : s.liveLabels = [] := by
  simp only [SState.liveLabels, h, filterMap_none, List.mergeSort_nil]

theorem access_noshape (s : SState) (p : Pos) (h : s.shape = fun _ => none) : s.access p = s := by
  simp [SState.access, liveLabels_noshape s h]

theorem SM.bind_apply {α β : Type 3} (x : SM α) (f : α → SM β) (s : SState) :
    (x >>= f) s = match x s with | some (a, s') => f a s' | none => none := rfl

/-- `f : Π(x : Nat). Nat`, the identity, as a global with its shape. -/
abbrev psF : List PiParam := [⟨false, fun _ => .ty0 Nat⟩]
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

theorem run_letIn (h : Hint) (u w : Term) (hint : TyS) (s : SState) :
    run K ρ φ hint (.letIn h u w) s = (run K ρ φ (.plain .err) u s).bind (fun x =>
      (run K ρ φ hint w (pushBindShaped x.2 { ty := x.1.2, val := fun _ => x.1.1, decl := K.D.declOf (scopeOf x.2) u })).bind
        fun y => some (y.1, (match x.1.2.label with | some l => y.2.endLabel l | none => y.2).dropLast)) := rfl

theorem run_seq (u w : Term) (hint : TyS) (s : SState) :
    run K ρ φ hint (.seq u w) s = (run K ρ φ (.plain .err) u >>= fun _ => run K ρ φ hint w) s := rfl

theorem run_place (p : Place) (hint : TyS) (s : SState) :
    run K ρ φ hint (.place p) s = readPlace K φ p (K.D.copy (K.D.placeDecl (scopeOf s) p)) s := rfl

theorem run_borrow (p : Place) (hint : TyS) (s : SState) : run K ρ φ hint (.borrow p) s = borrowPlace K φ p s := rfl

theorem readPlace_of (p : Place) (b : Bool) (s : SState) (v : Sem) (T : TyS) (pos : Pos) (st : List Step)
    (s' : SState) (h : contentOf K φ p s = some ((v, T, pos, st), s')) :
    readPlace K φ p b s = (if ¬ v.whole then none else
      if b then some ((v, T), s') else do
        let lab := if st.isEmpty then s'.shape pos else none
        let (⟨⟩, s) ← setContent K φ pos st .moved s'
        let s := match lab with
          | some l => (s.takeLabel l).pushTempShaped (fun _ => v) l
          | none => s
        some ((v, { T with label := lab }), s)) := by
  show (contentOf K φ p s >>= _) = _
  rw [h]
  rfl

/-- The empty state at counter `n` with `y = Z` bound. -/
noncomputable def a1 (n : Nat) : SState :=
  pushBindShaped (emptyState n) { ty := .plain (.ty0 Nat), val := fun _ => .el0 Nat 0, decl := K.D.declOf (scopeOf (emptyState n)) .zero }

theorem content_a1 (n : Nat) : contentOf K φ (.var 0) (a1 K n) = some ((.el0 Nat 0, .plain (.ty0 Nat), .bind 0 0, []), a1 K n) := by
  have hr : resolve (a1 K n) (.var 0) = some (.bind 0 0, []) := rfl
  simp only [contentOf, hr, access_noshape _ _ (rfl : (a1 K n).shape = _)]
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

/-- After the call took the holder: the temporary is moved and no label is live. -/
noncomputable def a3 (n : Nat) : SState :=
  { ((a2 K n).setAt (.temp 0 0) fun _ => .moved) with
    shape := fun p => if p = .temp 0 0 then none else (a2 K n).shape p }

theorem take_a2 (n : Nat) : (a2 K n).takeLabel n = a3 K n := by
  simp only [SState.takeLabel, holder_a2]
  rfl

theorem shape_a3 (n : Nat) : (a3 K n).shape = fun _ => none := by
  funext p
  show (if p = .temp 0 0 then none else if p = .temp 0 0 then some n else none) = none
  split <;> rfl

theorem run_call_KF (f : Term) (args : List Term) (hd : Bool) (hint : TyS) (s : SState) :
    run KF ρ φ hint (.call f args hd) s
      = (run KF ρ φ (.plain .err) f >>= fun fv => runArgs KF ρ φ fv.2.shape 0 [] args >>= fun as => callOf fv as) s := rfl

theorem runArgs_borrow (n : Nat) :
    runArgs KF ρ φ (some (psF, outF)) 0 [] [.borrow (.var 0)] (a1 KF n)
      = some ([(.el0 Nat 0, { TyS.plain (.ty0 Nat) with label := some n })], a2 KF n) := by
  show (run KF ρ φ (.plain (TyM.ty0 Nat)) (.borrow (.var 0)) >>= fun r =>
      runArgs KF ρ φ (some (psF, outF)) 1 ([] ++ [r.1]) [] >>= fun rest => pure (r :: rest)) (a1 KF n) = _
  rw [SM.bind_apply, run_borrow, borrow_a1]
  rfl

/-- After the call: the parked temporary was taken and nothing fixed label `n`. -/
noncomputable def a4 (n : Nat) : SState :=
  (a3 KF n).mapVals fun _ v φ' => v (φ'.updList ([n].zip []))

theorem call_a1 (n : Nat) :
    run KF ρ φ (.plain .err) (.call (.const "f") [.borrow (.var 0)] false) (a1 KF n)
      = some ((.el0 Nat 0, .plain (.ty0 Nat)), a4 n) := by
  rw [run_call_KF, SM.bind_apply]
  show (runArgs KF ρ φ (some (psF, outF)) 0 [] [.borrow (.var 0)] >>= fun as => callOf _ as) (a1 KF n) = _
  rw [SM.bind_apply, runArgs_borrow]
  show callOfL lvl0 psF outF (.el0 (piCarL lvl0 psF [] PUnit outF) Fid)
    [(.el0 Nat 0, { TyS.plain (.ty0 Nat) with label := some n })] (a2 KF n) = _
  unfold callOfL
  simp only [List.filterMap, List.map, List.foldl, take_a2, applyFn_F]
  rfl

theorem content_a4 (n : Nat) : contentOf KF φ (.var 0) (a4 n) = some ((φ n, .plain (.ty0 Nat), .bind 0 0, []), a4 n) := by
  have hr : resolve (a4 n) (.var 0) = some (.bind 0 0, []) := rfl
  have hs : (a4 n).shape = fun _ => none := shape_a3 KF n
  simp only [contentOf, hr, access_noshape _ _ hs]
  rfl

/-- The run of `tF` reads `φ n`: label `n` is the run's own, its holder was taken by the call and
nothing fixed or ended it. -/
theorem run_tF (n : Nat) (hint : TyS) (hw : (φ n).whole) :
    ∃ T s', run KF ρ φ hint tF (emptyState n) = some ((φ n, T), s') := by
  rw [tF, run_letIn]
  have h0 : run KF ρ φ (.plain .err) .zero (emptyState n) = some ((.el0 Nat 0, .plain (.ty0 Nat)), emptyState n) := rfl
  rw [h0]
  simp only [Option.bind]
  rw [show pushBindShaped (emptyState n) _ = a1 KF n from rfl, run_seq, SM.bind_apply, call_a1]
  simp only
  rw [run_place, readPlace_of φ KF _ _ _ _ _ _ _ _ (content_a4 φ n)]
  simp only [hw, not_true_eq_false, ite_false]
  generalize KF.D.copy _ = b
  cases b
  · simp only [Bool.false_eq_true, ite_false, List.isEmpty_nil, ite_true, shape_a3]
    exact ⟨_, _, rfl⟩
  · exact ⟨_, _, rfl⟩

theorem run_tF_none (n : Nat) (hint : TyS) (he : φ n = .err) : run KF ρ φ hint tF (emptyState n) = none := by
  rw [tF, run_letIn]
  have h0 : run KF ρ φ (.plain .err) .zero (emptyState n) = some ((.el0 Nat 0, .plain (.ty0 Nat)), emptyState n) := rfl
  rw [h0]
  simp only [Option.bind]
  rw [show pushBindShaped (emptyState n) _ = a1 KF n from rfl, run_seq, SM.bind_apply, call_a1]
  simp only
  rw [run_place, readPlace_of φ KF _ _ _ _ _ _ _ _ (content_a4 φ n), he]
  simp [Sem.whole]
end

/-- `run_congr` is false: `tF` holds no loan and `emptyState 0` no position, yet the runs at two
futures differing only at the run's own label `0` differ. -/
theorem run_congr_false : ¬ ∀ (φ φ' : Future) (hint : TyS) (t : Term) (s : SState) (L : Nat → Prop),
    (∀ l, L l → φ l = φ' l) → (∀ l, t.anyAtom (· == .loan l) → L l) →
    (∀ p ψ ψ', (∀ l, L l → ψ l = ψ' l) → s.valAt p ψ = s.valAt p ψ') →
    run KF ρ φ hint t s = run KF ρ φ' hint t s := by
  intro H
  have := H (fun _ => .el0 Nat 0) (fun _ => .err) (.plain .err) tF (emptyState 0) (fun _ => False)
    (fun _ h => h.elim) (fun l h => by rw [show tF.anyAtom (· == .loan l) = false from rfl] at h; cases h)
    (fun p ψ ψ' _ => by cases p with
      | bind f i => cases f <;> cases i <;> rfl
      | temp f i => cases f <;> cases i <;> rfl)
  obtain ⟨T, s', h1⟩ := run_tF ρ (fun _ => .el0 Nat 0) 0 (.plain .err) (by simp [Sem.whole])
  rw [h1, run_tF_none ρ (fun _ => .err) 0 (.plain .err) rfl] at this
  cases this

/-- `meanV_congr` is false: `⌈tF⌉` holds no loan, yet means `φ 1`. -/
theorem meanV_congr_false : ¬ ∀ (φ φ' : Future) (hint : TyS) (v : Value),
    (∀ l, v.hasLoan l → φ l = φ' l) → meanV KF ρ φ hint v = meanV KF ρ φ' hint v := by
  intro H
  have := H (fun _ => .el0 Nat 0) (fun _ => .err) (.plain .err) (.sealed tF)
    (fun l h => by rw [show (Value.sealed tF).hasLoan l = false from rfl] at h; cases h)
  obtain ⟨T, s', h1⟩ := run_tF ρ (fun _ => .el0 Nat 0) 1 (.plain .err) (by simp [Sem.whole])
  have h2 := run_tF_none ρ (fun _ => .err) 1 (.plain .err) rfl
  have e1 : meanV KF ρ (fun _ => .el0 Nat 0) (.plain .err) (.sealed tF) = .el0 Nat 0 := by
    show (match run KF ρ _ _ tF (emptyState (tF.loans.foldl max 0 + 1)) with
      | some ((v, _), _) => v | none => .err) = _
    rw [show tF.loans.foldl max 0 + 1 = 1 from rfl, h1]
  have e2 : meanV KF ρ (fun _ => .err) (.plain .err) (.sealed tF) = .err := by
    show (match run KF ρ _ _ tF (emptyState (tF.loans.foldl max 0 + 1)) with
      | some ((v, _), _) => v | none => .err) = _
    rw [show tF.loans.foldl max 0 + 1 = 1 from rfl, h2]
  rw [e1, e2] at this
  cases this

end Ochr.Meaning.Regress.CE4
