import Ochr.Meaning.Lemmas
import Ochr.Meaning.Mono
import Ochr.Meaning.Locality

/-
  Ochr.Meaning.Regress.CE5_5dc7710b: m2-proofs' Lean-checked counterexample (round 4b), valid against
  `spine` 3b089b08 and 5dc7710b, for every `K`. NOT built: it refutes the current statements and is
  to flip into a positive check once `.letIn`'s drop is fixed. To re-check it: `lake env lean` on
  it from `ochr/core/lean` at 5dc7710b. Axioms: propext, Classical.choice, Quot.sound.

  A root `.assign` of a borrow makes the place its holder; `.letIn`'s drop ends only the label the
  binding's *type* carried when it was bound, so `dropLast` removes the holder and leaves its shape
  entry dangling. `tA = let y = Z; (let x = Z; x := &y); y` reads `φ n` at the run's own label `n`
  (`run_tA_some`). Refutes `run_congr` and `meanV_congr` for every `K` (`run_congr_false`,
  `meanV_congr_false`), and `meanV_substLoan` and `run_substLoan` with all their hypotheses, through
  `.clo [] tA []`, whose code runs from counter 0 so the leaked label is the filled one
  (`meanV_substLoan_false`, `run_substLoan_false`; non-vacuous by `decInv_concrete`). Proposed fix:
  the drop ends what the binding holds now (`s.shape` at its position), which also clears the entry.
-/

/-! Round 4b (spine 3b089b08): a borrow acquired by assignment is dropped with its binding. -/

namespace Ochr.Meaning.Regress.CE5
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


section
variable (K : RunCtx) (ρ : Assignment) (φ : Future)

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

/-- `let y = Z; (let x = Z; x := &y); y`: `x` becomes the holder of `y`'s borrow by the
assignment, and its `let` drops it without ending it (the drop ends only the label `x`'s *type*
carried when it was bound). -/
def tA : Term :=
  .letIn ⟨"y"⟩ .zero (.seq (.letIn ⟨"x"⟩ .zero (.assign (.var 0) (.borrow (.var 1)))) (.place (.var 0)))

def yB (K : RunCtx) (n : Nat) : SBinding :=
  { ty := .plain (.ty0 Nat), val := fun _ => .el0 Nat 0, decl := K.D.declOf (scopeOf (emptyState n)) .zero }

noncomputable def xB (K : RunCtx) (n : Nat) : SBinding :=
  { ty := .plain (.ty0 Nat), val := fun _ => .el0 Nat 0,
    decl := K.D.declOf (scopeOf ((emptyState n).pushBind (yB K n))) .zero }

/-- `y` and `x` bound. -/
noncomputable def b1 (n : Nat) : SState := ((emptyState n).pushBind (yB K n)).pushBind (xB K n)

theorem content_b1_y (n : Nat) : contentOf K φ (.var 1) (b1 K n) = some ((.el0 Nat 0, .plain (.ty0 Nat), .bind 0 0, []), b1 K n) := by
  have hr : resolve (b1 K n) (.var 1) = some (.bind 0 0, []) := rfl
  simp only [contentOf, hr, access_noshape _ _ (rfl : (b1 K n).shape = _)]
  rfl

theorem content_b1_x (n : Nat) : contentOf K φ (.var 0) (b1 K n) = some ((.el0 Nat 0, .plain (.ty0 Nat), .bind 0 1, []), b1 K n) := by
  have hr : resolve (b1 K n) (.var 0) = some (.bind 0 1, []) := rfl
  simp only [contentOf, hr, access_noshape _ _ (rfl : (b1 K n).shape = _)]
  rfl

theorem run_assign (p : Place) (u : Term) (hint : TyS) (s : SState) :
    run K ρ φ hint (.assign p u) s = (do
      let ((_, T, pos, steps), s) ← contentOf K φ p s
      let ((v, R), s) ← run K ρ φ T u s
      let s := if steps.isEmpty then (match s.shape pos with | some l => s.endLabel l | none => s) else s
      let (⟨⟩, s) ← setContent K φ pos steps v s
      let s := match R.label, steps with
        | some l, [] => let s := s.takeLabel l; { s with shape := fun q => if q = pos then some l else s.shape q }
        | _, _ => s
      some ((.el0 Unit (), .plain (.ty0 Unit)), s)) := rfl

/-- After `&y`: `y` reads label `n`, the borrow parked in temporary `0`. -/
noncomputable def b2 (n : Nat) : SState :=
  { env := [{ binds := [{ yB K n with val := fun φ' => (Sem.updAt K.dm K.Γ (.ty0 Nat) (fun _ => φ' n) [] (Sem.el0 Nat 0)).getD .err },
                        xB K n],
              temps := [fun _ => .el0 Nat 0] }],
    shape := fun p => if p = .temp 0 0 then some n else none,
    nextLoan := n + 1 }

theorem borrow_b1 (n : Nat) : borrowPlace K φ (.var 1) (b1 K n) = some ((.el0 Nat 0, { TyS.plain (.ty0 Nat) with label := some n }), b2 K n) := by
  show (match contentOf K φ (.var 1) (b1 K n) with
      | some ((v, T, pos, steps), s) =>
        if ¬ v.whole then none else
        let (l, s) := s.freshLoan
        let T0 := (s.tyAt pos).m
        let old := s.valAt pos
        let s := s.setAt pos fun φ' => (Sem.updAt K.dm K.Γ T0 (fun _ => φ' l) steps (old φ')).getD .err
        let s := s.pushTempShaped (fun _ => v) l
        some ((v, { T with label := some l }), s)
      | none => none) = _
  rw [content_b1_y]
  simp only [Sem.whole, not_true_eq_false, ite_false]
  rfl

theorem positions_b2 (n : Nat) : (b2 K n).positions = [.bind 0 0, .bind 0 1, .temp 0 0] := by
  simp [SState.positions, b2]
  rfl

theorem holder_b2 (n : Nat) : (b2 K n).holderOf n = some (.temp 0 0) := by
  unfold SState.holderOf
  rw [positions_b2]
  simp [b2]

noncomputable def b3 (n : Nat) : SState :=
  (b2 K n).setAt (.bind 0 1) fun φ' =>
    (Sem.updAt K.dm K.Γ ((b2 K n).tyAt (.bind 0 1)).m (fun _ => .el0 Nat 0) [] ((b2 K n).valAt (.bind 0 1) φ')).getD .err

theorem setContent_b2 (n : Nat) : setContent K φ (.bind 0 1) [] (.el0 Nat 0) (b2 K n) = some (⟨⟩, b3 K n) := rfl

/-- After the assignment: `x` holds `y`'s borrow. -/
noncomputable def b5 (n : Nat) : SState :=
  let b4 := (b3 K n).takeLabel n
  { b4 with shape := fun q => if q = .bind 0 1 then some n else b4.shape q }

theorem assign_b1 (n : Nat) (hint : TyS) :
    run K ρ φ hint (.assign (.var 0) (.borrow (.var 1))) (b1 K n) = some ((.el0 Unit (), .plain (.ty0 Unit)), b5 K n) := by
  rw [run_assign]
  show (contentOf K φ (.var 0) (b1 K n) >>= _) = _
  rw [content_b1_x]
  show (run K ρ φ (.plain (.ty0 Nat)) (.borrow (.var 1)) (b1 K n) >>= _) = _
  rw [run_borrow, borrow_b1]
  rfl

theorem positions_b3 (n : Nat) : (b3 K n).positions = [.bind 0 0, .bind 0 1, .temp 0 0] := by
  simp [SState.positions, b3, b2, SState.setAt]
  rfl

theorem holder_b3 (n : Nat) : (b3 K n).holderOf n = some (.temp 0 0) := by
  unfold SState.holderOf
  rw [positions_b3]
  simp [b3, b2, SState.setAt]

/-- After the `let x` is dropped. -/
noncomputable def b6 (n : Nat) : SState := (b5 K n).dropLast

noncomputable def yB' (n : Nat) : SBinding :=
  { yB K n with val := fun φ' => (Sem.updAt K.dm K.Γ (.ty0 Nat) (fun _ => φ' n) [] (Sem.el0 Nat 0)).getD .err }

theorem take_b3 (n : Nat) : (b3 K n).takeLabel n =
    { ((b3 K n).setAt (.temp 0 0) fun _ => .moved) with
      shape := fun p => if p = .temp 0 0 then none else (b3 K n).shape p } := by
  unfold SState.takeLabel; rw [holder_b3]

theorem env_b6 (n : Nat) : (b6 K n).env = [{ binds := [yB' K n], temps := [fun _ => .moved] }] := by
  unfold b6 b5
  simp only [take_b3]
  rfl

theorem shape_b6 (n : Nat) (p : Pos) (hp : p ≠ .bind 0 1) : (b6 K n).shape p = none := by
  unfold b6 b5
  simp only [take_b3]
  show (if p = .bind 0 1 then some n else if p = .temp 0 0 then none else if p = .temp 0 0 then some n else none) = none
  simp [hp]

theorem positions_b6 (n : Nat) : (b6 K n).positions = [.bind 0 0, .temp 0 0] := by
  rw [SState.positions_eq, env_b6]
  simp [framePos]

theorem liveLabels_b6 (n : Nat) : (b6 K n).liveLabels = [] := by
  unfold SState.liveLabels
  rw [positions_b6]
  simp [shape_b6 K n (.bind 0 0) (by simp), shape_b6 K n (.temp 0 0) (by simp)]

theorem content_b6 (n : Nat) : contentOf K φ (.var 0) (b6 K n) = some ((φ n, (yB K n).ty, .bind 0 0, []), b6 K n) := by
  have hr : resolve (b6 K n) (.var 0) = some (.bind 0 0, []) := by
    simp [resolve, Place.steps, SState.varPos, env_b6, SState.topIdx]
  have ha : (b6 K n).access (.bind 0 0) = b6 K n := by
    simp [SState.access, liveLabels_b6]
  simp only [contentOf, hr, ha]
  have hv : (b6 K n).valAt (.bind 0 0) = (yB' K n).val := by simp [SState.valAt, env_b6]
  have ht : (b6 K n).tyAt (.bind 0 0) = (yB K n).ty := by simp [SState.tyAt, env_b6, yB']
  rw [hv, ht]
  rfl

theorem run_tA_head (n : Nat) (hint : TyS) :
    run K ρ φ hint tA (emptyState n) =
      (readPlace K φ (.var 0) (K.D.copy (K.D.placeDecl (scopeOf (b6 K n)) (.var 0))) (b6 K n)).bind
        fun y => some (y.1, y.2.dropLast) := by
  rw [tA, run_letIn]
  have h0 : run K ρ φ (.plain .err) .zero (emptyState n) = some ((.el0 Nat 0, .plain (.ty0 Nat)), emptyState n) := rfl
  rw [h0]
  simp only [Option.bind]
  rw [show pushBindShaped (emptyState n) _ = (emptyState n).pushBind (yB K n) from rfl, run_seq, SM.bind_apply,
    run_letIn]
  have h1 : run K ρ φ (.plain .err) .zero ((emptyState n).pushBind (yB K n))
      = some ((.el0 Nat 0, .plain (.ty0 Nat)), (emptyState n).pushBind (yB K n)) := rfl
  rw [h1]
  simp only [Option.bind]
  rw [show pushBindShaped ((emptyState n).pushBind (yB K n)) _ = b1 K n from rfl, assign_b1]
  rfl

theorem run_tA_some (n : Nat) (hint : TyS) (hw : (φ n).whole) :
    ∃ T s', run K ρ φ hint tA (emptyState n) = some ((φ n, T), s') := by
  rw [run_tA_head, readPlace_of K φ _ _ _ _ _ _ _ _ (content_b6 K φ n)]
  simp only [hw, not_true_eq_false, ite_false]
  generalize K.D.copy _ = b
  cases b
  · simp only [Bool.false_eq_true, ite_false, List.isEmpty_nil, ite_true, shape_b6 K n (.bind 0 0) (by simp)]
    exact ⟨_, _, rfl⟩
  · exact ⟨_, _, rfl⟩

theorem run_tA_none (n : Nat) (hint : TyS) (he : φ n = .err) : run K ρ φ hint tA (emptyState n) = none := by
  rw [run_tA_head, readPlace_of K φ _ _ _ _ _ _ _ _ (content_b6 K φ n), he]
  simp [Sem.whole]
end

/-- `run_congr` is false: `tA` holds no loan and `emptyState 0` no position. -/
theorem run_congr_false (K : RunCtx) (ρ : Assignment) : ¬ ∀ (φ φ' : Future) (hint : TyS) (t : Term) (s : SState) (L : Nat → Prop),
    (∀ l, L l → φ l = φ' l) → (∀ l, t.anyAtom (· == .loan l) → L l) →
    (∀ p ψ ψ', (∀ l, L l → ψ l = ψ' l) → s.valAt p ψ = s.valAt p ψ') →
    run K ρ φ hint t s = run K ρ φ' hint t s := by
  intro H
  have := H (fun _ => .el0 Nat 0) (fun _ => .err) (.plain .err) tA (emptyState 0) (fun _ => False)
    (fun _ h => h.elim) (fun l h => by rw [show tA.anyAtom (· == .loan l) = false from rfl] at h; cases h)
    (fun p ψ ψ' _ => by cases p with
      | bind f i => cases f <;> cases i <;> rfl
      | temp f i => cases f <;> cases i <;> rfl)
  obtain ⟨T, s', h1⟩ := run_tA_some K ρ (fun _ => .el0 Nat 0) 0 (.plain .err) (by simp [Sem.whole])
  rw [h1, run_tA_none K ρ (fun _ => .err) 0 (.plain .err) rfl] at this
  cases this

/-- `meanV_congr` is false: `⌈tA⌉` holds no loan, yet means `φ 1`. -/
theorem meanV_congr_false (K : RunCtx) (ρ : Assignment) : ¬ ∀ (φ φ' : Future) (hint : TyS) (v : Value),
    (∀ l, v.hasLoan l → φ l = φ' l) → meanV K ρ φ hint v = meanV K ρ φ' hint v := by
  intro H
  have := H (fun _ => .el0 Nat 0) (fun _ => .err) (.plain .err) (.sealed tA)
    (fun l h => by rw [show (Value.sealed tA).hasLoan l = false from rfl] at h; cases h)
  obtain ⟨T, s', h1⟩ := run_tA_some K ρ (fun _ => .el0 Nat 0) 1 (.plain .err) (by simp [Sem.whole])
  have h2 := run_tA_none K ρ (fun _ => .err) 1 (.plain .err) rfl
  have e1 : meanV K ρ (fun _ => .el0 Nat 0) (.plain .err) (.sealed tA) = .el0 Nat 0 := by
    show (match run K ρ _ _ tA (emptyState (tA.loans.foldl max 0 + 1)) with
      | some ((v, _), _) => v | none => .err) = _
    rw [show tA.loans.foldl max 0 + 1 = 1 from rfl, h1]
  have e2 : meanV K ρ (fun _ => .err) (.plain .err) (.sealed tA) = .err := by
    show (match run K ρ _ _ tA (emptyState (tA.loans.foldl max 0 + 1)) with
      | some ((v, _), _) => v | none => .err) = _
    rw [show tA.loans.foldl max 0 + 1 = 1 from rfl, h2]
  rw [e1, e2] at this
  cases this

theorem subst_tA (l : Nat) (w : Value) : Term.substLoan l w tA = tA := by
  simp [tA, Term.substLoan]

theorem meanV_clo_tA (K : RunCtx) (ρ : Assignment) (φ : Future) (hint : TyS) (hw : (φ 0).whole) :
    meanV K ρ φ hint (.clo [] tA []) = φ 0 := by
  obtain ⟨T, s', h⟩ := run_tA_some K ρ φ 0 (.plain .err) hw
  show (match run K ρ φ (.plain .err) tA (stateOf 0 (capsState (capsVals K ρ φ []) (capsTys K ρ φ []))) with
    | some ((v, _), _) => v | none => .err) = _
  rw [show stateOf 0 (capsState (capsVals K ρ φ []) (capsTys K ρ φ [])) = emptyState 0 from rfl, h]

/-- `meanV_substLoan`, with every hypothesis met, is false: the closure's code runs from counter 0,
so the leaked label is 0, the label being filled. -/
theorem meanV_substLoan_false (K : RunCtx) (ρ : Assignment) (hD : DecInvariant K.D 0 .zero) :
    ¬ ∀ (φ : Future) (hint : TyS) (l : Nat) (w v : Value),
    ¬ w.hasLoan l → HintFree K ρ φ w → DecInvariant K.D l w → NotCode w →
    meanV K ρ φ hint (Value.substLoan l w v) = meanV K ρ (φ.upd l (meanV K ρ φ (.plain .err) w)) hint v := by
  intro H
  have := H (fun _ => .el0 Nat 5) (.plain .err) 0 .zero (.clo [] tA []) (by decide) (fun _ _ => rfl) hD trivial
  rw [show Value.substLoan 0 .zero (.clo [] tA []) = .clo [] tA [] by
    simp [Value.substLoan, Value.substLoanList, Value.substLoanRd, subst_tA]] at this
  have hu : (Future.upd (fun _ => Sem.el0 Nat 5) 0 (meanV K ρ (fun _ => .el0 Nat 5) (.plain .err) .zero)) 0 = .el0 Nat 0 := rfl
  rw [meanV_clo_tA K ρ _ _ (by simp [Sem.whole]), meanV_clo_tA K ρ _ _ (by rw [hu]; simp [Sem.whole]), hu] at this
  have : (5 : Nat) = 0 := by injection this
  cases this

/-- `run_substLoan`, with every hypothesis met (B included), is false, by the same closure. -/
theorem run_substLoan_false (K : RunCtx) (ρ : Assignment) (hD : DecInvariant K.D 0 .zero) :
    ¬ ∀ (φ : Future) (hint : TyS) (l : Nat) (w : Value) (t : Term) (s : SState),
    ¬ w.hasLoan l → HintFree K ρ φ w → DecInvariant K.D l w → NotCode w → StateFreeOf s l →
    run K ρ φ hint (Term.substLoan l w t) s = run K ρ (φ.upd l (meanV K ρ φ (.plain .err) w)) hint t s := by
  intro H
  have hs : StateFreeOf (emptyState 1) 0 := by
    refine ⟨fun p ψ x => ?_, by decide⟩
    cases p with
    | bind f i => cases f <;> cases i <;> rfl
    | temp f i => cases f <;> cases i <;> rfl
  have := H (fun _ => .el0 Nat 5) (.plain .err) 0 .zero (.val (.clo [] tA [])) (emptyState 1) (by decide)
    (fun _ _ => rfl) hD trivial hs
  rw [show Term.substLoan 0 .zero (.val (.clo [] tA [])) = .val (.clo [] tA []) by
    simp [Term.substLoan, Value.substLoan, Value.substLoanList, Value.substLoanRd, subst_tA]] at this
  have hm := congrArg (Option.map (·.1.1)) this
  have hu : (Future.upd (fun _ => Sem.el0 Nat 5) 0 (meanV K ρ (fun _ => .el0 Nat 5) (.plain .err) .zero)) 0 = .el0 Nat 0 := rfl
  have l1 : (run K ρ (fun _ => .el0 Nat 5) (.plain .err) (.val (.clo [] tA [])) (emptyState 1)).map (·.1.1)
      = some (meanV K ρ (fun _ => .el0 Nat 5) (.plain .err) (.clo [] tA [])) := rfl
  have l2 : (run K ρ (Future.upd (fun _ => Sem.el0 Nat 5) 0 (meanV K ρ (fun _ => .el0 Nat 5) (.plain .err) .zero))
      (.plain .err) (.val (.clo [] tA [])) (emptyState 1)).map (·.1.1)
      = some (meanV K ρ (Future.upd (fun _ => Sem.el0 Nat 5) 0 (meanV K ρ (fun _ => .el0 Nat 5) (.plain .err) .zero))
          (.plain .err) (.clo [] tA [])) := rfl
  rw [l1, l2, meanV_clo_tA K ρ _ _ (by simp [Sem.whole]), meanV_clo_tA K ρ _ _ (by rw [hu]; simp [Sem.whole]), hu] at hm
  have : (5 : Nat) = 0 := by injection hm with h; injection h
  cases this

/-- The hypothesis `DecInvariant K.D 0 Z` is met by a concrete context, so the refutation is not vacuous. -/
theorem decInv_concrete : DecInvariant JoinDropCounterexample.K.D 0 .zero :=
  ⟨fun _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl, fun _ _ _ => rfl⟩

end Ochr.Meaning.Regress.CE5
