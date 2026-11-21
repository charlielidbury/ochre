/-
  Ochr.Meaning.Regress.CE2_3c323dcc: m2-proofs' Lean-checked counterexamples (2026-11-09, round 2)
  to the restated `meanV_congr`, `run_substLoan` and `meanV_substLoan` (Lemmas.lean), against the
  definitions of `spine` at 059d7906 and still valid at 3c323dcc (the per-future run, D10, before
  D13). Kept verbatim as the record of what refuted them; NOT built (not imported by
  `Ochr/Meaning.lean`), since D13 changed the run. To re-check it, check out 3c323dcc and run
  `lake env lean` on it from `ochr/core/lean`. Every theorem uses only propext, Classical.choice
  and Quot.sound, and holds for every `K` and `ρ` unless stated.

  * A, `meanV_congr_false2`: a dropped temporary borrow never ends its label. `let y = Z; (&y; y)`
    (`tTemp`) has no loans, yet the read of `y` sees `φ 1` (the run's own label, never in `shape`):
    `el0 Nat 0` at φ ≡ `el0 Nat 0`, a failed run (`err`) at φ ≡ `err`. Fixed by D13 (`.seq` ends a
    discarded labelled result).
  * B, `run_substLoan_false2`: a starting state lent at `l` (a binding `fun ψ => ψ 0`) reads `l`
    from the future on one side only. Hypothesis B (`StateFreeOf s l`).
  * C, `run_substLoan_false3`, `meanV_substLoan_false2`: the decisions read the substituted syntax.
    For every `K` whose readings are the checker's (`declOf (.val ⋆)` copies, `declOf (.val loan)`
    moves), `let x = loan_0; x; x` (`tDec`) moves `x` and fails on the second read while the
    filled `let x = ⋆; x; x` copies it. Hypothesis C (`DecInvariant`).
  * E, `run_substLoan_false4`: a loan filled by a Π-type value: the `.val` clause gives the
    filled value a shape in its `TyS`, the loan only the hint. Hypothesis E (`NotCode w`).
  * D (not a separate theorem; code reading, through A): a sealed program's two runs start at
    different label counters before and after the substitution. Lemma D (`run_counter_indep`).
-/
import Ochr.Meaning.Lemmas

/-! Counterexamples to the round-2 statements (spine 059d7906). -/

namespace Ochr.Meaning
open Classical

theorem filterMap_none' {α β} (l : List α) : List.filterMap (fun _ => (none : Option β)) l = [] := by
  induction l <;> simp_all [List.filterMap]

theorem liveLabels_noshape (s : SState) (h : s.shape = fun _ => none) : s.liveLabels = [] := by
  simp only [SState.liveLabels, h, filterMap_none', List.mergeSort_nil]

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

theorem run_place (p : Place) (hint : TyS) (s : SState) :
    run K ρ φ hint (.place p) s = readPlace K φ p (K.D.copy (K.D.placeDecl (scopeOf s) p)) s := rfl

theorem run_seq (u w : Term) (hint : TyS) (s : SState) :
    run K ρ φ hint (.seq u w) s = (run K ρ φ (.plain .err) u >>= fun _ => run K ρ φ hint w) s := rfl

theorem run_borrow (p : Place) (hint : TyS) (s : SState) : run K ρ φ hint (.borrow p) s = borrowPlace K φ p s := rfl

theorem readPlace_eq (p : Place) (b : Bool) (s : SState) (v : Sem) (T : TyS) (pos : Pos) (st : List Step) (s' : SState)
    (h : contentOf K φ p s = some ((v, T, pos, st), s')) :
    readPlace K φ p b s = (if ¬ v.whole then (SM.fail : SM Res) else
          if b then pure (v, T) else do
            setContent K φ pos st .moved
            pure (v, T)) s' := by
  show (contentOf K φ p >>= _) s = _
  rw [SM.bind_apply, h]

/-! ### A. meanV_congr: a dropped temporary borrow never ends its label -/
def tTemp : Term := .letIn ⟨"y"⟩ .zero (.seq (.borrow (.var 0)) (.place (.var 0)))

theorem tTemp_noLoan (l : Nat) : (Value.sealed tTemp).hasLoan l = false := rfl

noncomputable def a1 : SState :=
  pushBindShaped (emptyState 1) { ty := .plain (.ty0 Nat), val := fun _ => .el0 Nat 0, decl := K.D.declOf (scopeOf (emptyState 1)) .zero }

theorem content_a1 : contentOf K φ (.var 0) (a1 K) = some ((.el0 Nat 0, .plain (.ty0 Nat), .bind 0 0, []), a1 K) := by
  have hr : resolve (a1 K) (.var 0) = some (.bind 0 0, []) := rfl
  simp only [contentOf, hr, access_noshape _ _ (rfl : (a1 K).shape = _)]
  rfl

noncomputable def a2 : SState :=
  (a1 K).freshLoan.2.setAt (.bind 0 0) (fun φ' => (Sem.updAt K.dm K.Γ (.ty0 Nat) (fun _ => φ' 1) [] (Sem.el0 Nat 0)).getD .err)

theorem borrow_a1 : borrowPlace K φ (.var 0) (a1 K) = some ((.el0 Nat 0, { TyS.plain (.ty0 Nat) with label := some 1 }), a2 K) := by
  show (match contentOf K φ (.var 0) (a1 K) with
      | some ((v, T, pos, steps), s) =>
        if ¬ v.whole then none else
        let (l, s) := s.freshLoan
        let T0 := (s.tyAt pos).m
        let old := s.valAt pos
        let s := s.setAt pos fun φ' => (Sem.updAt K.dm K.Γ T0 (fun _ => φ' l) steps (old φ')).getD .err
        some ((v, { T with label := some l }), s)
      | none => none) = _
  rw [content_a1]
  simp only [Sem.whole, not_true_eq_false, ite_false]
  rfl

theorem content_a2 : contentOf K φ (.var 0) (a2 K) = some ((φ 1, .plain (.ty0 Nat), .bind 0 0, []), a2 K) := by
  have hr : resolve (a2 K) (.var 0) = some (.bind 0 0, []) := rfl
  simp only [contentOf, hr, access_noshape _ _ (rfl : (a2 K).shape = _)]
  rfl

theorem run_tTemp (hint : TyS) (hw : (φ 1).whole) :
    ∃ T s', run K ρ φ hint tTemp (emptyState 1) = some ((φ 1, T), s') := by
  rw [tTemp, run_letIn]
  have h0 : run K ρ φ (.plain .err) .zero (emptyState 1) = some ((.el0 Nat 0, .plain (.ty0 Nat)), emptyState 1) := rfl
  rw [h0]
  simp only [Option.bind]
  rw [run_seq, SM.bind_apply, show pushBindShaped (emptyState 1) _ = a1 K from rfl, run_borrow, borrow_a1]
  simp only
  rw [run_place, readPlace_eq K φ _ _ _ _ _ _ _ _ (content_a2 K φ)]
  simp only [hw, not_true_eq_false, ite_false]
  generalize K.D.copy _ = b
  cases b
  · exact ⟨_, _, rfl⟩
  · exact ⟨_, _, rfl⟩

theorem run_tTemp_err (hint : TyS) (he : φ 1 = .err) : run K ρ φ hint tTemp (emptyState 1) = none := by
  rw [tTemp, run_letIn]
  have h0 : run K ρ φ (.plain .err) .zero (emptyState 1) = some ((.el0 Nat 0, .plain (.ty0 Nat)), emptyState 1) := rfl
  rw [h0]
  simp only [Option.bind]
  rw [run_seq, SM.bind_apply, show pushBindShaped (emptyState 1) _ = a1 K from rfl, run_borrow, borrow_a1]
  simp only
  rw [run_place, readPlace_eq K φ _ _ _ _ _ _ _ _ (content_a2 K φ), he]
  simp [Sem.whole, SM.fail]

theorem meanV_congr_false2 : ¬ ∀ (φ φ' : Future) (hint : TyS) (v : Value),
    (∀ l, v.hasLoan l → φ l = φ' l) → meanV K ρ φ hint v = meanV K ρ φ' hint v := by
  intro H
  have := H (fun _ => .el0 Nat 0) (fun _ => .err) (.plain .err) (.sealed tTemp)
    (fun l h => by rw [tTemp_noLoan] at h; cases h)
  obtain ⟨T, s', h1⟩ := run_tTemp K ρ (fun _ => .el0 Nat 0) (.plain .err) (by simp [Sem.whole])
  have h2 := run_tTemp_err K ρ (fun _ => .err) (.plain .err) rfl
  have e1 : meanV K ρ (fun _ => .el0 Nat 0) (.plain .err) (.sealed tTemp) = .el0 Nat 0 := by
    show (match run K ρ _ _ tTemp (emptyState (tTemp.loans.foldl max 0 + 1)) with
      | some ((v, _), _) => v | none => .err) = _
    rw [show tTemp.loans.foldl max 0 + 1 = 1 from rfl, h1]
  have e2 : meanV K ρ (fun _ => .err) (.plain .err) (.sealed tTemp) = .err := by
    show (match run K ρ _ _ tTemp (emptyState (tTemp.loans.foldl max 0 + 1)) with
      | some ((v, _), _) => v | none => .err) = _
    rw [show tTemp.loans.foldl max 0 + 1 = 1 from rfl, h2]
  rw [e1, e2] at this
  cases this

/-! ### B. run_substLoan: a state lent at `l` reads `l` from the future on one side only -/
def sB (f : SVal) : SState := stateOf 0 [{ ty := .plain (.ty0 Nat), val := f }]

theorem run_sB (f : SVal) (ψ : Future) (hint : TyS) (hw : (f ψ).whole) :
    ∃ T s', run K ρ ψ hint (.place (.var 0)) (sB f) = some ((f ψ, T), s') := by
  have hc : contentOf K ψ (.var 0) (sB f) = some ((f ψ, .plain (.ty0 Nat), .bind 0 0, []), sB f) := by
    have hr : resolve (sB f) (.var 0) = some (.bind 0 0, []) := rfl
    simp only [contentOf, hr, access_noshape _ _ (rfl : (sB f).shape = _)]
    rfl
  rw [run_place, readPlace_eq K ψ _ _ _ _ _ _ _ _ hc]
  simp only [hw, not_true_eq_false, ite_false]
  generalize K.D.copy _ = b
  cases b
  · exact ⟨_, _, rfl⟩
  · exact ⟨_, _, rfl⟩

theorem run_substLoan_false2 : ¬ ∀ (φ : Future) (hint : TyS) (l : Nat) (w : Value) (t : Term) (s : SState),
    ¬ w.hasLoan l → HintFree K ρ φ w →
    run K ρ φ hint (Term.substLoan l w t) s = run K ρ (φ.upd l (meanV K ρ φ (.plain .err) w)) hint t s := by
  intro H
  have := H (fun _ => .el0 Nat 5) (.plain .err) 0 .zero (.place (.var 0)) (sB fun ψ => ψ 0) (by decide) (fun _ _ => rfl)
  rw [show Term.substLoan 0 .zero (.place (.var 0)) = .place (.var 0) from rfl] at this
  obtain ⟨T, s', h1⟩ := run_sB K ρ (fun ψ => ψ 0) (fun _ => .el0 Nat 5) (.plain .err) (by simp [Sem.whole])
  have h3 : (Future.upd (fun _ => Sem.el0 Nat 5) 0 (meanV K ρ (fun _ => .el0 Nat 5) (.plain .err) .zero)) 0 = .el0 Nat 0 := rfl
  obtain ⟨T', s'', h2⟩ := run_sB K ρ (fun ψ => ψ 0) (Future.upd (fun _ => Sem.el0 Nat 5) 0 (meanV K ρ (fun _ => .el0 Nat 5) (.plain .err) .zero))
    (.plain .err) (by show Sem.whole (Future.upd _ 0 _ 0); rw [h3]; simp [Sem.whole])
  rw [h1, h2] at this
  simp only [h3, Option.some.injEq, Prod.mk.injEq] at this
  cases this.1.1

/-! ### C. run_substLoan: the decisions read the substituted syntax. With the checker's own
readings (`Decide.valueDecl`: a loan reads `.other`, `⋆` reads `.prop`; `declCopy .prop = true`,
`declCopy .other = false`; `placeDecl sc (.var 0) = sc[0]`), `let x = loan_0; x; x` moves `x`
and fails on the second read, while `let x = ⋆; x; x` copies it. -/
def tDec (v : Value) : Term := .letIn ⟨"x"⟩ (.val v) (.seq (.place (.var 0)) (.place (.var 0)))

noncomputable def c1 (ψ : Future) (v : Value) : SState :=
  pushBindShaped (emptyState 1)
    { ty := .plain .err, val := (fun _ => meanV K ρ ψ (.plain .err) v), decl := K.D.declOf (scopeOf (emptyState 1)) (.val v) }

theorem content_c1 (ψ : Future) (v : Value) :
    contentOf K ψ (.var 0) (c1 K ρ ψ v) = some ((meanV K ρ ψ (.plain .err) v, .plain .err, .bind 0 0, []), c1 K ρ ψ v) := by
  have hr : resolve (c1 K ρ ψ v) (.var 0) = some (.bind 0 0, []) := rfl
  simp only [contentOf, hr, access_noshape _ _ (rfl : (c1 K ρ ψ v).shape = _)]
  rfl

theorem run_tDec_head (ψ : Future) (hint : TyS) (v : Value) (hv : v = .proof ∨ v = .loan 0) :
    run K ρ ψ hint (tDec v) (emptyState 1) = (run K ρ ψ hint (.seq (.place (.var 0)) (.place (.var 0))) (c1 K ρ ψ v)).bind
      fun y => some (y.1, y.2.dropLast) := by
  rw [tDec, run_letIn]
  have h0 : run K ρ ψ (.plain .err) (.val v) (emptyState 1) = some ((meanV K ρ ψ (.plain .err) v, .plain .err), emptyState 1) := by
    rcases hv with rfl | rfl <;> rfl
  rw [h0]
  rfl

noncomputable def c2 (ψ : Future) (v : Value) : SState :=
  (c1 K ρ ψ v).setAt (.bind 0 0) fun φ'' =>
    (Sem.updAt K.dm K.Γ TyM.err (fun _ => Sem.moved) [] ((c1 K ρ ψ v).valAt (.bind 0 0) φ'')).getD .err

theorem setContent_c1 (ψ : Future) (v : Value) :
    setContent K ψ (.bind 0 0) [] .moved (c1 K ρ ψ v) = some (⟨⟩, c2 K ρ ψ v) := rfl

theorem content_c2 (ψ : Future) (v : Value) :
    contentOf K ψ (.var 0) (c2 K ρ ψ v) = some ((.moved, .plain .err, .bind 0 0, []), c2 K ρ ψ v) := by
  have hr : resolve (c2 K ρ ψ v) (.var 0) = some (.bind 0 0, []) := rfl
  simp only [contentOf, hr, access_noshape _ _ (rfl : (c2 K ρ ψ v).shape = _)]
  rfl

theorem run_tDec_proof (hint : TyS)
    (hc1 : K.D.copy (K.D.placeDecl [K.D.declOf [] (.val .proof)] (.var 0)) = true) :
    ∃ T s', run K ρ noFuture hint (tDec .proof) (emptyState 1) = some ((.proof, T), s') := by
  rw [run_tDec_head K ρ _ _ _ (.inl rfl), run_seq, SM.bind_apply, run_place,
    readPlace_eq K _ _ _ _ _ _ _ _ _ (content_c1 K ρ _ _)]
  rw [show scopeOf (c1 K ρ noFuture .proof) = [K.D.declOf [] (.val .proof)] from rfl, hc1]
  simp only [show meanV K ρ noFuture (.plain .err) .proof = .proof from rfl, Sem.whole, not_true_eq_false,
    ite_false, if_true]
  show ∃ T s', (run K ρ noFuture hint (.place (.var 0)) (c1 K ρ noFuture .proof)).bind _ = _
  rw [run_place, readPlace_eq K _ _ _ _ _ _ _ _ _ (content_c1 K ρ _ _)]
  rw [show scopeOf (c1 K ρ noFuture .proof) = [K.D.declOf [] (.val .proof)] from rfl, hc1]
  simp only [show meanV K ρ noFuture (.plain .err) .proof = .proof from rfl, Sem.whole, not_true_eq_false,
    ite_false, if_true]
  exact ⟨_, _, rfl⟩

theorem run_tDec_loan (hint : TyS)
    (hc2 : K.D.copy (K.D.placeDecl [K.D.declOf [] (.val (.loan 0))] (.var 0)) = false) :
    run K ρ (noFuture.upd 0 .proof) hint (tDec (.loan 0)) (emptyState 1) = none := by
  rw [run_tDec_head K ρ _ _ _ (.inr rfl), run_seq, SM.bind_apply, run_place,
    readPlace_eq K _ _ _ _ _ _ _ _ _ (content_c1 K ρ _ _)]
  rw [show scopeOf (c1 K ρ (noFuture.upd 0 .proof) (.loan 0)) = [K.D.declOf [] (.val (.loan 0))] from rfl, hc2]
  have hm : meanV K ρ (noFuture.upd 0 .proof) (.plain .err) (.loan 0) = .proof := rfl
  simp only [hm, Sem.whole, not_true_eq_false, ite_false, Bool.false_eq_true]
  rw [SM.bind_apply, setContent_c1]
  show (run K ρ _ hint (.place (.var 0)) (c2 K ρ _ (.loan 0))).bind _ = none
  rw [run_place, readPlace_eq K _ _ _ _ _ _ _ _ _ (content_c2 K ρ _ _)]
  simp [Sem.whole, SM.fail]

theorem run_substLoan_false3
    (hc1 : K.D.copy (K.D.placeDecl [K.D.declOf [] (.val .proof)] (.var 0)) = true)
    (hc2 : K.D.copy (K.D.placeDecl [K.D.declOf [] (.val (.loan 0))] (.var 0)) = false) :
    ¬ ∀ (φ : Future) (hint : TyS) (l : Nat) (w : Value) (t : Term) (s : SState),
    ¬ w.hasLoan l → HintFree K ρ φ w →
    run K ρ φ hint (Term.substLoan l w t) s = run K ρ (φ.upd l (meanV K ρ φ (.plain .err) w)) hint t s := by
  intro H
  have := H noFuture (.plain .err) 0 .proof (tDec (.loan 0)) (emptyState 1) (by decide) (fun _ _ => rfl)
  rw [show Term.substLoan 0 .proof (tDec (.loan 0)) = tDec .proof by simp [tDec, Term.substLoan, Value.substLoan]] at this
  rw [show meanV K ρ noFuture (.plain .err) .proof = .proof from rfl, run_tDec_loan K ρ _ hc2] at this
  obtain ⟨T, s', h⟩ := run_tDec_proof K ρ (.plain .err) hc1
  rw [h] at this
  cases this

/-- C at a sealed program: meanV_substLoan fails under the checker's readings. -/
theorem meanV_substLoan_false2
    (hc1 : K.D.copy (K.D.placeDecl [K.D.declOf [] (.val .proof)] (.var 0)) = true)
    (hc2 : K.D.copy (K.D.placeDecl [K.D.declOf [] (.val (.loan 0))] (.var 0)) = false) :
    ¬ ∀ (φ : Future) (hint : TyS) (l : Nat) (w v : Value),
    ¬ w.hasLoan l → HintFree K ρ φ w →
    meanV K ρ φ hint (Value.substLoan l w v) = meanV K ρ (φ.upd l (meanV K ρ φ (.plain .err) w)) hint v := by
  intro H
  have := H noFuture (.plain .err) 0 .proof (.sealed (tDec (.loan 0))) (by decide) (fun _ _ => rfl)
  rw [show Value.substLoan 0 .proof (.sealed (tDec (.loan 0))) = .sealed (tDec .proof) by
    simp [tDec, Term.substLoan, Value.substLoan]] at this
  obtain ⟨T, s', hL⟩ := run_tDec_proof K ρ (.plain .err) hc1
  have hR := run_tDec_loan K ρ (.plain .err) hc2
  revert this
  show (match run K ρ noFuture (.plain .err) (tDec .proof) (emptyState ((tDec .proof).loans.foldl max 0 + 1)) with
      | some ((v, _), _) => v | none => .err)
    = (match run K ρ (noFuture.upd 0 (meanV K ρ noFuture (.plain .err) .proof)) (.plain .err) (tDec (.loan 0))
        (emptyState ((tDec (.loan 0)).loans.foldl max 0 + 1)) with
      | some ((v, _), _) => v | none => .err) → False
  rw [show (tDec .proof).loans.foldl max 0 + 1 = 1 from rfl, show (tDec (.loan 0)).loans.foldl max 0 + 1 = 1 from rfl,
    show meanV K ρ noFuture (.plain .err) .proof = .proof from rfl, hR, hL]
  intro h
  cases h
end

end Ochr.Meaning
namespace Ochr.Meaning
section
variable (K : RunCtx) (ρ : Assignment)

/-! ### E. run_substLoan: a loan filled by a Π-type (or closure, or global) value. The `.val`
clause gives an embedded function or Π value its shape in the result's `TyS`, an embedded loan
only the hint, so the two runs' result types differ. -/
def wPi : Value := .tPi [] (.pi [] [] .nat) []

theorem run_substLoan_false4 : ¬ ∀ (φ : Future) (hint : TyS) (l : Nat) (w : Value) (t : Term) (s : SState),
    ¬ w.hasLoan l → HintFree K ρ φ w →
    run K ρ φ hint (Term.substLoan l w t) s = run K ρ (φ.upd l (meanV K ρ φ (.plain .err) w)) hint t s := by
  intro H
  have := H noFuture (.plain .err) 0 wPi (.val (.loan 0)) (emptyState 0) (by decide) (fun _ _ => rfl)
  rw [show Term.substLoan 0 wPi (.val (.loan 0)) = .val wPi by simp [Term.substLoan, Value.substLoan]] at this
  have h1 : (run K ρ noFuture (.plain .err) (.val wPi) (emptyState 0)).map (·.1.2.shape.isSome) = some true := rfl
  have h2 : (run K ρ (noFuture.upd 0 (meanV K ρ noFuture (.plain .err) wPi)) (.plain .err) (.val (.loan 0))
      (emptyState 0)).map (·.1.2.shape.isSome) = some false := rfl
  rw [this, h2] at h1
  cases h1
end
end Ochr.Meaning

#print axioms Ochr.Meaning.meanV_congr_false2
#print axioms Ochr.Meaning.run_substLoan_false2
#print axioms Ochr.Meaning.run_substLoan_false3
#print axioms Ochr.Meaning.meanV_substLoan_false2
#print axioms Ochr.Meaning.run_substLoan_false4
