import Ochr.Meaning.Lemmas
import Ochr.Meaning.Mono

/-
  Ochr.Meaning.Regress.CE3_9c4e6cd4: m2-proofs' Lean-checked regression checks and
  counterexamples (2026-11-09, round 3) against `spine` 9c4e6cd4 (D13, per-site label ends). Kept
  as the record of what refuted D13's statements; NOT built (not imported by `Ochr/Meaning.lean`),
  since D14 (a3c17705) changed the run. To re-check it, check out 9c4e6cd4, add the import, and
  build. Every theorem used only propext, Classical.choice and Quot.sound.

  * A, positive at 9c4e6cd4: `let y = Z; (&y; y)` read `Z` at every future (`tTemp_reads_zero`).
  * B, C, E: `noB`, `noC_run`, `noC_meanV`, `noE`, counterexamples to the unhypothesised
    substitution lemmas (B: a state lent at the filled label; C: the decisions read the
    substituted syntax, under the checker's readings, witnessed by `Kchk`; E: a Π-type fill).
  * Round 3, what refuted D13: `S(&y)` consumes the borrow before `.seq` sees it, so
    `let y = Z; (S(&y); y)` (`tSucc`) read `φ n` at the run's own label `n` (`run_tSucc_some`).
    It refuted `meanV_congr` (`open_congr`), `meanV_substLoan` and `run_substLoan` with all their
    hypotheses, through a closure whose code runs from counter 0 so its leaked label is the filled
    one (`open_substV`, `open_substRun`, non-vacuous by `decInv_concrete`), and `run_counter_indep`
    (`open_counter`: a returned borrow's label is the counter; `open_counter'`: the leak, on
    meanings). Led to D14 (a label always has a holder; reads without access at the closed future).
-/

namespace Ochr.Meaning.Regress.CE3_9c4e6cd4

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

/-! ## Clause unfoldings (`rfl`: `run`'s equation lemmas time out) -/

theorem run_letIn (h : Hint) (u w : Term) (hint : TyS) (s : SState) :
    run K ρ φ hint (.letIn h u w) s = (run K ρ φ (.plain .err) u s).bind (fun x =>
      (run K ρ φ hint w (pushBindShaped x.2 { ty := x.1.2, val := fun _ => x.1.1, decl := K.D.declOf (scopeOf x.2) u })).bind
        fun y => some (y.1, (match x.1.2.label with | some l => y.2.endLabel l | none => y.2).dropLast)) := rfl

theorem run_seq (u w : Term) (hint : TyS) (s : SState) :
    run K ρ φ hint (.seq u w) s = (run K ρ φ (.plain .err) u s).bind fun x =>
      run K ρ φ hint w (match x.1.2.label with
        | some l => x.2.mapVals fun _ v ψ => v (ψ.upd l x.1.1)
        | none => x.2) := rfl

theorem run_succ (u : Term) (hint : TyS) (s : SState) :
    run K ρ φ hint (.succ u) s = (do
      let (v, _) ← run K ρ φ (.plain (.ty0 Nat)) u
      pure (v.succ, TyS.plain (.ty0 Nat)) : SM Res) s := rfl

theorem run_place (p : Place) (hint : TyS) (s : SState) :
    run K ρ φ hint (.place p) s = readPlace K φ p (K.D.copy (K.D.placeDecl (scopeOf s) p)) s := rfl

theorem run_borrow (p : Place) (hint : TyS) (s : SState) : run K ρ φ hint (.borrow p) s = borrowPlace K φ p s := rfl

/-! ## One binding `y = Z`, then `&y` -/

/-- The empty state at counter `n` with `y = Z` bound. -/
noncomputable def a1 (n : Nat) : SState :=
  pushBindShaped (emptyState n) { ty := .plain (.ty0 Nat), val := fun _ => .el0 Nat 0, decl := K.D.declOf (scopeOf (emptyState n)) .zero }

theorem content_a1 (n : Nat) : contentOf K φ (.var 0) (a1 K n) = some ((.el0 Nat 0, .plain (.ty0 Nat), .bind 0 0, []), a1 K n) := by
  have hr : resolve (a1 K n) (.var 0) = some (.bind 0 0, []) := rfl
  simp only [contentOf, hr, access_noshape _ _ (rfl : (a1 K n).shape = _)]
  rfl

/-- After `&y` at counter `n`: `y` reads label `n`'s final content; no holder is recorded. -/
noncomputable def a2 (n : Nat) : SState :=
  (a1 K n).freshLoan.2.setAt (.bind 0 0) (fun φ' => (Sem.updAt K.dm K.Γ (.ty0 Nat) (fun _ => φ' n) [] (Sem.el0 Nat 0)).getD .err)

theorem borrow_a1 (n : Nat) : borrowPlace K φ (.var 0) (a1 K n) = some ((.el0 Nat 0, { TyS.plain (.ty0 Nat) with label := some n }), a2 K n) := by
  show (match contentOf K φ (.var 0) (a1 K n) with
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

theorem readPlace_of (p : Place) (b : Bool) (s : SState) (v : Sem) (T : TyS) (pos : Pos) (st : List Step)
    (s' : SState) (h : contentOf K φ p s = some ((v, T, pos, st), s')) :
    readPlace K φ p b s = (if ¬ v.whole then none else
      if b then some ((v, T), s') else do
        let lab := if st.isEmpty then s'.shape pos else none
        let s := match lab with
          | some _ => { s' with shape := fun q => if q = pos then none else s'.shape q }
          | none => s'
        let (⟨⟩, s) ← setContent K φ pos st .moved s
        some ((v, { T with label := lab }), s)) := by
  show (contentOf K φ p s >>= _) = _
  rw [h]
  rfl

/-- A read of `y` at a state where it holds `v` (whole, no holder recorded) gives `v`, by copy
or by move. -/
theorem read_y (s : SState) (v : Sem) (hv : v.whole) (hshape : s.shape = fun _ => none) (b : Bool)
    (hc : contentOf K φ (.var 0) s = some ((v, .plain (.ty0 Nat), .bind 0 0, []), s)) :
    ∃ T s', readPlace K φ (.var 0) b s = some ((v, T), s') := by
  rw [readPlace_of K φ _ _ _ _ _ _ _ _ hc]
  simp only [hv, not_true_eq_false, ite_false]
  cases b
  · simp only [Bool.false_eq_true, ite_false, List.isEmpty_nil, ite_true, hshape]
    exact ⟨_, _, rfl⟩
  · exact ⟨_, _, rfl⟩

/-! ## A, flipped: a discarded borrow is ended at its content -/

/-- `let y = Z; (&y; y)`. -/
def tTemp : Term := .letIn ⟨"y"⟩ .zero (.seq (.borrow (.var 0)) (.place (.var 0)))

/-- After `&y; ` : label 1 is fixed to the borrow's content `Z` everywhere. -/
noncomputable def a3 : SState := (a2 K 1).mapVals fun _ v ψ => v (ψ.upd 1 (.el0 Nat 0))

theorem content_a3 : contentOf K φ (.var 0) (a3 K) = some ((.el0 Nat 0, .plain (.ty0 Nat), .bind 0 0, []), a3 K) := by
  have hr : resolve (a3 K) (.var 0) = some (.bind 0 0, []) := rfl
  simp only [contentOf, hr, access_noshape _ _ (rfl : (a3 K).shape = _)]
  rfl

/-- At every future, `let y = Z; (&y; y)` reads `Z` (round 2's A: it read `φ 1`). -/
theorem tTemp_reads_zero (hint : TyS) :
    ∃ T s', run K ρ φ hint tTemp (emptyState 1) = some ((.el0 Nat 0, T), s') := by
  rw [tTemp, run_letIn]
  have h0 : run K ρ φ (.plain .err) .zero (emptyState 1) = some ((.el0 Nat 0, .plain (.ty0 Nat)), emptyState 1) := rfl
  rw [h0]
  simp only [Option.bind]
  rw [run_seq, show pushBindShaped (emptyState 1) _ = a1 K 1 from rfl, run_borrow, borrow_a1]
  simp only [Option.bind]
  rw [run_place, show (a2 K 1).mapVals (fun _ v ψ => v (ψ.upd 1 (.el0 Nat 0))) = a3 K from rfl]
  obtain ⟨T, s', h⟩ := read_y K φ (a3 K) (.el0 Nat 0) (by simp [Sem.whole]) rfl _ (content_a3 K φ)
  rw [h]
  exact ⟨_, _, rfl⟩

/-! ## B, C, E: the hypotheses of the substitution lemmas are needed -/

/-- The empty state is free of label `0` at counter `1`. -/
theorem stateFree_empty : StateFreeOf (emptyState 1) 0 := by
  refine ⟨fun p ψ x => ?_, by decide⟩
  cases p with
  | bind f i => cases f <;> cases i <;> rfl
  | temp f i => cases f <;> cases i <;> rfl

/-- A state with one binding `x : Nat` holding `f`. -/
def sB (f : SVal) : SState := stateOf 0 [{ ty := .plain (.ty0 Nat), val := f }]

theorem content_sB (f : SVal) : contentOf K φ (.var 0) (sB f) = some ((f φ, .plain (.ty0 Nat), .bind 0 0, []), sB f) := by
  have hr : resolve (sB f) (.var 0) = some (.bind 0 0, []) := rfl
  simp only [contentOf, hr, access_noshape _ _ (rfl : (sB f).shape = _)]
  rfl

/-- B: `run_substLoan` without `StateFreeOf`: a state lent at `0` (`x` reads `ψ 0`) reads the
future on one side and the fill on the other. -/
theorem noB (hD : DecInvariant K.D 0 .zero) : ¬ ∀ (φ : Future) (hint : TyS) (l : Nat) (w : Value) (t : Term) (s : SState),
    ¬ w.hasLoan l → HintFree K ρ φ w → DecInvariant K.D l w → NotCode w →
    run K ρ φ hint (Term.substLoan l w t) s = run K ρ (φ.upd l (meanV K ρ φ (.plain .err) w)) hint t s := by
  intro H
  have := H (fun _ => .el0 Nat 5) (.plain .err) 0 .zero (.place (.var 0)) (sB fun ψ => ψ 0) (by decide) (fun _ _ => rfl) hD trivial
  rw [show Term.substLoan 0 .zero (.place (.var 0)) = .place (.var 0) from rfl, run_place, run_place] at this
  have hu : (Future.upd (fun _ => Sem.el0 Nat 5) 0 (meanV K ρ (fun _ => .el0 Nat 5) (.plain .err) .zero)) 0 = .el0 Nat 0 := rfl
  obtain ⟨T, s', h1⟩ := read_y K (fun _ => .el0 Nat 5) (sB fun ψ => ψ 0) (.el0 Nat 5) (by simp [Sem.whole]) rfl
    (K.D.copy (K.D.placeDecl (scopeOf (sB fun ψ => ψ 0)) (.var 0))) (content_sB K _ _)
  obtain ⟨T', s'', h2⟩ := read_y K (Future.upd (fun _ => Sem.el0 Nat 5) 0 (meanV K ρ (fun _ => .el0 Nat 5) (.plain .err) .zero))
    (sB fun ψ => ψ 0) (.el0 Nat 0) (by simp [Sem.whole]) rfl
    (K.D.copy (K.D.placeDecl (scopeOf (sB fun ψ => ψ 0)) (.var 0))) (by rw [← hu]; exact content_sB K _ _)
  rw [h1, h2] at this
  simp only [Option.some.injEq, Prod.mk.injEq] at this
  have : (5 : Nat) = 0 := by injection this.1.1
  cases this

/-- C's program: `let x = v; x; x`. -/
def tDec (v : Value) : Term := .letIn ⟨"x"⟩ (.val v) (.seq (.place (.var 0)) (.place (.var 0)))

noncomputable def c1 (ψ : Future) (v : Value) : SState :=
  pushBindShaped (emptyState 1)
    { ty := .plain .err, val := (fun _ => meanV K ρ ψ (.plain .err) v), decl := K.D.declOf (scopeOf (emptyState 1)) (.val v) }

theorem content_c1 (ψ : Future) (v : Value) :
    contentOf K ψ (.var 0) (c1 K ρ ψ v) = some ((meanV K ρ ψ (.plain .err) v, .plain .err, .bind 0 0, []), c1 K ρ ψ v) := by
  have hr : resolve (c1 K ρ ψ v) (.var 0) = some (.bind 0 0, []) := rfl
  simp only [contentOf, hr, access_noshape _ _ (rfl : (c1 K ρ ψ v).shape = _)]
  rfl

/-- `x` after a move. -/
noncomputable def c2 (ψ : Future) (v : Value) : SState :=
  (c1 K ρ ψ v).setAt (.bind 0 0) fun φ'' =>
    (Sem.updAt K.dm K.Γ TyM.err (fun _ => Sem.moved) [] ((c1 K ρ ψ v).valAt (.bind 0 0) φ'')).getD .err

theorem content_c2 (ψ : Future) (v : Value) :
    contentOf K ψ (.var 0) (c2 K ρ ψ v) = some ((.moved, .plain .err, .bind 0 0, []), c2 K ρ ψ v) := by
  have hr : resolve (c2 K ρ ψ v) (.var 0) = some (.bind 0 0, []) := rfl
  simp only [contentOf, hr, access_noshape _ _ (rfl : (c2 K ρ ψ v).shape = _)]
  rfl

theorem run_tDec_head (ψ : Future) (hint : TyS) (v : Value) (hv : v = .proof ∨ v = .loan 0) :
    run K ρ ψ hint (tDec v) (emptyState 1) = (run K ρ ψ hint (.seq (.place (.var 0)) (.place (.var 0))) (c1 K ρ ψ v)).bind
      fun y => some (y.1, y.2.dropLast) := by
  rw [tDec, run_letIn]
  have h0 : run K ρ ψ (.plain .err) (.val v) (emptyState 1) = some ((meanV K ρ ψ (.plain .err) v, .plain .err), emptyState 1) := by
    rcases hv with rfl | rfl <;> rfl
  rw [h0]
  rfl

/-- The filled program `let x = ⋆; x; x` copies `x` (the checker's reading of `⋆` is `.prop`). -/
theorem run_tDec_proof (hint : TyS)
    (hc1 : K.D.copy (K.D.placeDecl [K.D.declOf [] (.val .proof)] (.var 0)) = true) :
    ∃ T s', run K ρ noFuture hint (tDec .proof) (emptyState 1) = some ((.proof, T), s') := by
  rw [run_tDec_head K ρ _ _ _ (.inl rfl), run_seq, run_place, readPlace_of K _ _ _ _ _ _ _ _ _ (content_c1 K ρ _ _)]
  rw [show scopeOf (c1 K ρ noFuture .proof) = [K.D.declOf [] (.val .proof)] from rfl, hc1]
  simp only [show meanV K ρ noFuture (.plain .err) .proof = .proof from rfl, Sem.whole, not_true_eq_false,
    ite_false, if_true]
  show ∃ T s', (run K ρ noFuture hint (.place (.var 0)) (c1 K ρ noFuture .proof)).bind _ = _
  rw [run_place, readPlace_of K _ _ _ _ _ _ _ _ _ (content_c1 K ρ _ _)]
  rw [show scopeOf (c1 K ρ noFuture .proof) = [K.D.declOf [] (.val .proof)] from rfl, hc1]
  simp only [show meanV K ρ noFuture (.plain .err) .proof = .proof from rfl, Sem.whole, not_true_eq_false,
    ite_false, if_true]
  exact ⟨_, _, rfl⟩

/-- The unfilled program `let x = loan_0; x; x` moves `x` (a loan reads `.other`) and fails on
the second read. -/
theorem run_tDec_loan (hint : TyS)
    (hc2 : K.D.copy (K.D.placeDecl [K.D.declOf [] (.val (.loan 0))] (.var 0)) = false) :
    run K ρ (noFuture.upd 0 .proof) hint (tDec (.loan 0)) (emptyState 1) = none := by
  rw [run_tDec_head K ρ _ _ _ (.inr rfl), run_seq, run_place, readPlace_of K _ _ _ _ _ _ _ _ _ (content_c1 K ρ _ _)]
  rw [show scopeOf (c1 K ρ (noFuture.upd 0 .proof) (.loan 0)) = [K.D.declOf [] (.val (.loan 0))] from rfl, hc2]
  have hm : meanV K ρ (noFuture.upd 0 .proof) (.plain .err) (.loan 0) = .proof := rfl
  simp only [hm, Sem.whole, not_true_eq_false, ite_false, Bool.false_eq_true, List.isEmpty_nil, ite_true,
    show (c1 K ρ (noFuture.upd 0 .proof) (.loan 0)).shape (.bind 0 0) = none from rfl]
  show (run K ρ _ hint (.place (.var 0)) (c2 K ρ _ (.loan 0))).bind _ = none
  rw [run_place, readPlace_of K _ _ _ _ _ _ _ _ _ (content_c2 K ρ _ _)]
  simp [Sem.whole]

/-- C: `run_substLoan` without `DecInvariant`, under the checker's readings (`Decide.valueDecl`: a
loan reads `.other`, `⋆` reads `.prop`; `declCopy .prop`, not `declCopy .other`;
`placeDecl sc (.var 0) = sc[0]`). -/
theorem noC_run
    (hc1 : K.D.copy (K.D.placeDecl [K.D.declOf [] (.val .proof)] (.var 0)) = true)
    (hc2 : K.D.copy (K.D.placeDecl [K.D.declOf [] (.val (.loan 0))] (.var 0)) = false) :
    ¬ ∀ (φ : Future) (hint : TyS) (l : Nat) (w : Value) (t : Term) (s : SState),
    ¬ w.hasLoan l → HintFree K ρ φ w → NotCode w → StateFreeOf s l →
    run K ρ φ hint (Term.substLoan l w t) s = run K ρ (φ.upd l (meanV K ρ φ (.plain .err) w)) hint t s := by
  intro H
  have := H noFuture (.plain .err) 0 .proof (tDec (.loan 0)) (emptyState 1) (by decide) (fun _ _ => rfl) trivial
    stateFree_empty
  rw [show Term.substLoan 0 .proof (tDec (.loan 0)) = tDec .proof by simp [tDec, Term.substLoan, Value.substLoan]] at this
  rw [show meanV K ρ noFuture (.plain .err) .proof = .proof from rfl, run_tDec_loan K ρ _ hc2] at this
  obtain ⟨T, s', h⟩ := run_tDec_proof K ρ (.plain .err) hc1
  rw [h] at this
  cases this

/-- C at a sealed program: `meanV_substLoan` without `DecInvariant`. -/
theorem noC_meanV
    (hc1 : K.D.copy (K.D.placeDecl [K.D.declOf [] (.val .proof)] (.var 0)) = true)
    (hc2 : K.D.copy (K.D.placeDecl [K.D.declOf [] (.val (.loan 0))] (.var 0)) = false) :
    ¬ ∀ (φ : Future) (hint : TyS) (l : Nat) (w v : Value),
    ¬ w.hasLoan l → HintFree K ρ φ w → NotCode w →
    meanV K ρ φ hint (Value.substLoan l w v) = meanV K ρ (φ.upd l (meanV K ρ φ (.plain .err) w)) hint v := by
  intro H
  have := H noFuture (.plain .err) 0 .proof (.sealed (tDec (.loan 0))) (by decide) (fun _ _ => rfl) trivial
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

/-- E's fill: a Π-type value. -/
def wPi : Value := .tPi [] (.pi [] [] .nat) []

/-- E: `run_substLoan` without `NotCode`: the `.val` clause gives the filled Π-type value a shape
in its `TyS`, the loan only the hint. -/
theorem noE (hD : DecInvariant K.D 0 wPi) : ¬ ∀ (φ : Future) (hint : TyS) (l : Nat) (w : Value) (t : Term) (s : SState),
    ¬ w.hasLoan l → HintFree K ρ φ w → DecInvariant K.D l w → StateFreeOf s l →
    run K ρ φ hint (Term.substLoan l w t) s = run K ρ (φ.upd l (meanV K ρ φ (.plain .err) w)) hint t s := by
  intro H
  have := H noFuture (.plain .err) 0 wPi (.val (.loan 0)) (emptyState 1) (by decide) (fun _ _ => rfl) hD stateFree_empty
  rw [show Term.substLoan 0 wPi (.val (.loan 0)) = .val wPi by simp [Term.substLoan, Value.substLoan]] at this
  have h1 : (run K ρ noFuture (.plain .err) (.val wPi) (emptyState 1)).map (·.1.2.shape.isSome) = some true := rfl
  have h2 : (run K ρ (noFuture.upd 0 (meanV K ρ noFuture (.plain .err) wPi)) (.plain .err) (.val (.loan 0))
      (emptyState 1)).map (·.1.2.shape.isSome) = some false := rfl
  rw [this, h2] at h1
  cases h1

/-! ## Round 3, open: a borrow consumed by `S` loses its label (flip when fixed) -/

/-- `let y = Z; (S(&y); y)`. -/
def tSucc : Term := .letIn ⟨"y"⟩ .zero (.seq (.succ (.borrow (.var 0))) (.place (.var 0)))

theorem content_a2 (n : Nat) : contentOf K φ (.var 0) (a2 K n) = some ((φ n, .plain (.ty0 Nat), .bind 0 0, []), a2 K n) := by
  have hr : resolve (a2 K n) (.var 0) = some (.bind 0 0, []) := rfl
  simp only [contentOf, hr, access_noshape _ _ (rfl : (a2 K n).shape = _)]
  rfl

theorem run_tSucc (n : Nat) (hint : TyS) :
    run K ρ φ hint tSucc (emptyState n) =
      (readPlace K φ (.var 0) (K.D.copy (K.D.placeDecl (scopeOf (a2 K n)) (.var 0))) (a2 K n)).bind
        fun y => some (y.1, y.2.dropLast) := by
  rw [tSucc, run_letIn]
  have h0 : run K ρ φ (.plain .err) .zero (emptyState n) = some ((.el0 Nat 0, .plain (.ty0 Nat)), emptyState n) := rfl
  rw [h0]
  simp only [Option.bind]
  rw [run_seq, show pushBindShaped (emptyState n) _ = a1 K n from rfl, run_succ, SM.bind_apply, run_borrow, borrow_a1]
  rfl

/-- The read of `y` sees `φ n`, the future at the run's own label `n` (the start counter). -/
theorem run_tSucc_some (n : Nat) (hint : TyS) (hw : (φ n).whole) :
    ∃ T s', run K ρ φ hint tSucc (emptyState n) = some ((φ n, T), s') := by
  rw [run_tSucc]
  obtain ⟨T, s', h⟩ := read_y K φ (a2 K n) (φ n) hw rfl _ (content_a2 K φ n)
  rw [h]
  exact ⟨_, _, rfl⟩

theorem run_tSucc_none (n : Nat) (hint : TyS) (he : φ n = .err) :
    run K ρ φ hint tSucc (emptyState n) = none := by
  rw [run_tSucc, readPlace_of K φ _ _ _ _ _ _ _ _ (content_a2 K φ n), he]
  simp [Sem.whole]

theorem subst_tSucc (l : Nat) (w : Value) : Term.substLoan l w tSucc = tSucc := by
  simp [tSucc, Term.substLoan]

theorem meanV_clo_tSucc (hint : TyS) (hw : (φ 0).whole) : meanV K ρ φ hint (.clo [] tSucc []) = φ 0 := by
  obtain ⟨T, s', h⟩ := run_tSucc_some K ρ φ 0 (.plain .err) hw
  show (match run K ρ φ (.plain .err) tSucc (stateOf 0 (capsState (capsVals K ρ φ []) (capsTys K ρ φ []))) with
    | some ((v, _), _) => v | none => .err) = _
  rw [show stateOf 0 (capsState (capsVals K ρ φ []) (capsTys K ρ φ [])) = emptyState 0 from rfl, h]

/-- `meanV_congr` (its `hasLoan` form) is false: `⌈tSucc⌉` holds no loan, yet means `φ 1`. -/
theorem open_congr : ¬ ∀ (φ φ' : Future) (hint : TyS) (v : Value),
    (∀ l, v.hasLoan l → φ l = φ' l) → meanV K ρ φ hint v = meanV K ρ φ' hint v := by
  intro H
  have := H (fun _ => .el0 Nat 0) (fun _ => .err) (.plain .err) (.sealed tSucc)
    (fun l h => by rw [show (Value.sealed tSucc).hasLoan l = false from rfl] at h; cases h)
  obtain ⟨T, s', h1⟩ := run_tSucc_some K ρ (fun _ => .el0 Nat 0) 1 (.plain .err) (by simp [Sem.whole])
  have h2 := run_tSucc_none K ρ (fun _ => .err) 1 (.plain .err) rfl
  have e1 : meanV K ρ (fun _ => .el0 Nat 0) (.plain .err) (.sealed tSucc) = .el0 Nat 0 := by
    show (match run K ρ _ _ tSucc (emptyState (tSucc.loans.foldl max 0 + 1)) with
      | some ((v, _), _) => v | none => .err) = _
    rw [show tSucc.loans.foldl max 0 + 1 = 1 from rfl, h1]
  have e2 : meanV K ρ (fun _ => .err) (.plain .err) (.sealed tSucc) = .err := by
    show (match run K ρ _ _ tSucc (emptyState (tSucc.loans.foldl max 0 + 1)) with
      | some ((v, _), _) => v | none => .err) = _
    rw [show tSucc.loans.foldl max 0 + 1 = 1 from rfl, h2]
  rw [e1, e2] at this
  cases this

/-- `meanV_substLoan` with every hypothesis is false: a closure's code runs from counter `0`, so
its leaked label is `0`, the label being filled. -/
theorem open_substV (hD : DecInvariant K.D 0 .zero) : ¬ ∀ (φ : Future) (hint : TyS) (l : Nat) (w v : Value),
    ¬ w.hasLoan l → HintFree K ρ φ w → DecInvariant K.D l w → NotCode w →
    meanV K ρ φ hint (Value.substLoan l w v) = meanV K ρ (φ.upd l (meanV K ρ φ (.plain .err) w)) hint v := by
  intro H
  have := H (fun _ => .el0 Nat 5) (.plain .err) 0 .zero (.clo [] tSucc []) (by decide) (fun _ _ => rfl) hD trivial
  rw [show Value.substLoan 0 .zero (.clo [] tSucc []) = .clo [] tSucc [] by
    simp [Value.substLoan, Value.substLoanList, Value.substLoanRd, subst_tSucc]] at this
  have hu : (Future.upd (fun _ => Sem.el0 Nat 5) 0 (meanV K ρ (fun _ => .el0 Nat 5) (.plain .err) .zero)) 0 = .el0 Nat 0 := rfl
  rw [meanV_clo_tSucc K ρ _ _ (by simp [Sem.whole]), meanV_clo_tSucc K ρ _ _ (by rw [hu]; simp [Sem.whole]), hu] at this
  have : (5 : Nat) = 0 := by injection this
  cases this

/-- `run_substLoan` with every hypothesis (B included) is false, by the same closure. -/
theorem open_substRun (hD : DecInvariant K.D 0 .zero) : ¬ ∀ (φ : Future) (hint : TyS) (l : Nat) (w : Value) (t : Term) (s : SState),
    ¬ w.hasLoan l → HintFree K ρ φ w → DecInvariant K.D l w → NotCode w → StateFreeOf s l →
    run K ρ φ hint (Term.substLoan l w t) s = run K ρ (φ.upd l (meanV K ρ φ (.plain .err) w)) hint t s := by
  intro H
  have := H (fun _ => .el0 Nat 5) (.plain .err) 0 .zero (.val (.clo [] tSucc [])) (emptyState 1) (by decide) (fun _ _ => rfl)
    hD trivial stateFree_empty
  rw [show Term.substLoan 0 .zero (.val (.clo [] tSucc [])) = .val (.clo [] tSucc []) by
    simp [Term.substLoan, Value.substLoan, Value.substLoanList, Value.substLoanRd, subst_tSucc]] at this
  have hm := congrArg (Option.map (·.1.1)) this
  have hu : (Future.upd (fun _ => Sem.el0 Nat 5) 0 (meanV K ρ (fun _ => .el0 Nat 5) (.plain .err) .zero)) 0 = .el0 Nat 0 := rfl
  have l1 : (run K ρ (fun _ => .el0 Nat 5) (.plain .err) (.val (.clo [] tSucc [])) (emptyState 1)).map (·.1.1)
      = some (meanV K ρ (fun _ => .el0 Nat 5) (.plain .err) (.clo [] tSucc [])) := rfl
  have l2 : (run K ρ (Future.upd (fun _ => Sem.el0 Nat 5) 0 (meanV K ρ (fun _ => .el0 Nat 5) (.plain .err) .zero))
      (.plain .err) (.val (.clo [] tSucc [])) (emptyState 1)).map (·.1.1)
      = some (meanV K ρ (Future.upd (fun _ => Sem.el0 Nat 5) 0 (meanV K ρ (fun _ => .el0 Nat 5) (.plain .err) .zero))
          (.plain .err) (.clo [] tSucc [])) := rfl
  rw [l1, l2, meanV_clo_tSucc K ρ _ _ (by simp [Sem.whole]), meanV_clo_tSucc K ρ _ _ (by rw [hu]; simp [Sem.whole]), hu] at hm
  have : (5 : Nat) = 0 := by injection hm with h; injection h
  cases this

/-- `run_counter_indep` is false as stated (i): the statement compares the whole `Res`, and a
returned borrow's label is the counter (`&y` at counters 1 and 2). -/
theorem open_counter (hint : TyS) : ¬ ∀ (φ : Future) (hint : TyS) (t : Term) (s : SState) (n n' : Nat),
    (∀ l ∈ t.loans, l < n) → (∀ l ∈ t.loans, l < n') → (∀ l ∈ s.positions.filterMap s.shape, l < min n n') →
    (run K ρ φ hint t { s with nextLoan := n }).map (·.1) = (run K ρ φ hint t { s with nextLoan := n' }).map (·.1) := by
  intro H
  have := H noFuture hint (.borrow (.var 0)) (a1 K 0) 1 2 (by simp [Term.loans]) (by simp [Term.loans])
    (by simp [show (a1 K 0).shape = fun _ => none from rfl, filterMap_none])
  rw [run_borrow, run_borrow, show { a1 K 0 with nextLoan := 1 } = a1 K 1 from rfl,
    show { a1 K 0 with nextLoan := 2 } = a1 K 2 from rfl, borrow_a1, borrow_a1] at this
  simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq, TyS.mk.injEq] at this
  cases this.2.2.2.1

/-- (ii) Comparing meanings only, the leak makes the result the future at the counter: `tSucc`
at counters 1 and 2 under `φ k = k`. -/
theorem open_counter' : ¬ ∀ (φ : Future) (hint : TyS) (t : Term) (s : SState) (n n' : Nat),
    (∀ l ∈ t.loans, l < n) → (∀ l ∈ t.loans, l < n') → (∀ l ∈ s.positions.filterMap s.shape, l < min n n') →
    (run K ρ φ hint t { s with nextLoan := n }).map (·.1.1) = (run K ρ φ hint t { s with nextLoan := n' }).map (·.1.1) := by
  intro H
  have := H (fun k => .el0 Nat k) (.plain .err) tSucc (emptyState 0) 1 2 (by simp [tSucc, Term.loans])
    (by simp [tSucc, Term.loans]) (by simp [show (emptyState 0).shape = fun _ => none from rfl, filterMap_none])
  obtain ⟨T, s', h1⟩ := run_tSucc_some K ρ (fun k => .el0 Nat k) 1 (.plain .err) (by simp [Sem.whole])
  obtain ⟨T', s'', h2⟩ := run_tSucc_some K ρ (fun k => .el0 Nat k) 2 (.plain .err) (by simp [Sem.whole])
  rw [show { emptyState 0 with nextLoan := 1 } = emptyState 1 from rfl,
    show { emptyState 0 with nextLoan := 2 } = emptyState 2 from rfl, h1, h2] at this
  simp only [Option.map_some, Option.some.injEq] at this
  have : (1 : Nat) = 2 := by injection this
  cases this

end

/-- `DecInvariant K.D 0 w` is met by a concrete context (constant decisions), so `noB`, `noE`,
`open_substV` and `open_substRun` are not vacuous. -/
theorem decInv_concrete (w : Value) : DecInvariant JoinDropCounterexample.K.D 0 w :=
  ⟨fun _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl, fun _ _ _ => rfl⟩

/-- Decisions with the checker's readings on C's program: `⋆` reads `.prop`, everything else
`.other`; a place reads its scope's entry; `.prop` copies. -/
def Dchk : Decisions where
  flags _ _ := (false, false)
  placeDecl sc p := match p with | .var i => sc.getD i .other | _ => .other
  declOf _ t := match t with | .val .proof => .prop | _ => .other
  copy d := match d with | .prop => true | _ => false
  piSort _ _ := 1
  joinMoves _ _ _ := []

noncomputable def Kchk : RunCtx := { JoinDropCounterexample.K with D := Dchk }

/-- `noC_run` and `noC_meanV`'s hypotheses are met by `Kchk`, so they are not vacuous. -/
theorem noC_concrete :
    Kchk.D.copy (Kchk.D.placeDecl [Kchk.D.declOf [] (.val .proof)] (.var 0)) = true ∧
    Kchk.D.copy (Kchk.D.placeDecl [Kchk.D.declOf [] (.val (.loan 0))] (.var 0)) = false := ⟨rfl, rfl⟩

end Ochr.Meaning.Regress.CE3_9c4e6cd4
