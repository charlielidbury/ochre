/-
  Ochr.Meaning.Regress.CE_82394c1a: m2-proofs' Lean-checked counterexamples (2026-11-09) to the first
  statements of the knot and the substitution lemmas, against the definitions of `spine` at
  82394c1a (before D10, the per-future run, and D8 revised). Kept verbatim as the record of what
  refuted them; NOT built (not imported by `Ochr/Meaning.lean`), since the definitions it refers
  to have changed. Each example is to become a positive regression check against the current run
  (`run_tBor` now succeeds; `.tPi` means a type; `rd` is read; a hole reads the future). To
  re-check it, check out 82394c1a and run `lake env lean` on it from `ochr/core/lean`.
-/
import Ochr.Meaning.Lemmas

namespace Ochr.Meaning
open Classical

section
variable (K : RunCtx) (ρ : Assignment)

/-! ### 1. meanV_eq_mean at `.tPi [] .zero []` -/
example (φ : Future) (hint : TyM) :
    Value.mean K.dm (codeMeaning K ρ) K.Γ ρ φ hint (.tPi [] .zero []) ≠ meanV K ρ φ hint (.tPi [] .zero []) := by
  have h1 : meanV K ρ φ hint (.tPi [] .zero []) = .el0 Nat 0 := rfl
  have h2 : meanV K ρ φ .err (.tPi [] .zero []) = .el0 Nat 0 := rfl
  have h3 : Value.mean K.dm (codeMeaning K ρ) K.Γ ρ φ hint (.tPi [] .zero [])
      = .ty (meanV K ρ φ .err (.tPi [] .zero [])).asTy := rfl
  rw [h1, h3, h2]; simp [Sem.asTy]

/-! ### 3. meanV_substLoan at a sealed program reading a hole through a binding -/
def tHole (l : Nat) : Term := .letIn ⟨"x"⟩ (.val (.loan l)) (.place (.var 0))


noncomputable def s1 (l : Nat) : SState :=
  emptyState.pushBind { ty := .err, val := fun φ => meanV K ρ φ .err (.loan l), decl := K.D.declOf (scopeOf emptyState) (.val (.loan l)) }

theorem filterMap_none' {α β} (l : List α) : List.filterMap (fun _ => (none : Option β)) l = [] := by
  induction l <;> simp_all [List.filterMap]

theorem liveLabels_noshape (s : SState) (h : s.shape = fun _ => none) : s.liveLabels = [] := by
  simp only [SState.liveLabels, h, filterMap_none', List.mergeSort_nil]

theorem access_noshape (s : SState) (p : Pos) (h : s.shape = fun _ => none) : s.access p = s := by
  simp [SState.access, liveLabels_noshape s h]

theorem s1_live (l : Nat) : (s1 K ρ l).liveLabels = [] := liveLabels_noshape _ rfl

theorem content_s1 (l : Nat) : contentOf K (.var 0) (s1 K ρ l) = some ((.err, .err, .bind 0 0, []), s1 K ρ l) := by
  have hr : resolve (s1 K ρ l) (.var 0) = some (.bind 0 0, []) := rfl
  simp only [contentOf, hr, access_noshape _ _ (rfl : (s1 K ρ l).shape = _)]
  rfl

theorem run_letIn (h : Hint) (u w : Term) (hint : TyM) (s : SState) :
    run K ρ hint (.letIn h u w) s = (run K ρ .err u s).bind (fun x =>
      (run K ρ hint w (x.2.pushBind { ty := x.1.2.m, val := x.1.1, decl := K.D.declOf (scopeOf x.2) u })).bind
        fun y => some (y.1, y.2.dropLast)) := by
  rfl

theorem run_place (p : Place) (hint : TyM) (s : SState) :
    run K ρ hint (.place p) s = readPlace K p (K.D.copy (K.D.placeDecl (scopeOf s) p)) s := rfl

theorem readPlace_s1 (l : Nat) (b : Bool) : readPlace K (.var 0) b (s1 K ρ l) = none := by
  have : readPlace K (.var 0) b (s1 K ρ l) = (match contentOf K (.var 0) (s1 K ρ l) with
      | some (a, s') => (if ¬ a.1.whole then (SM.fail : SM Res) else
          if b then pure (fun _ => a.1, ⟨a.2.1, none, none⟩) else do
            setContent K a.2.2.1 a.2.2.2 .moved
            pure (fun _ => a.1, ⟨a.2.1, none, none⟩)) s'
      | none => none) := rfl
  rw [this, content_s1]
  simp [Sem.whole, SM.fail]

theorem run_tHole (l : Nat) (hint : TyM) :
    run K ρ hint (tHole l) emptyState = none := by
  rw [tHole, run_letIn]
  have h0 : run K ρ .err (.val (.loan l)) emptyState
      = some ((fun φ => meanV K ρ φ .err (.loan l), ⟨.err, none, none⟩), emptyState) := rfl
  rw [h0]
  simp only [Option.bind]
  rw [run_place]
  exact (congrArg (fun x => Option.bind x _) (readPlace_s1 K ρ l _)).trans rfl

theorem subst_tHole (l : Nat) : Term.substLoan l .zero (tHole l) = .letIn ⟨"x"⟩ (.val .zero) (.place (.var 0)) := by
  simp [tHole, Term.substLoan, Value.substLoan]

noncomputable def s1' : SState :=
  emptyState.pushBind { ty := .err, val := fun φ => meanV K ρ φ .err .zero, decl := K.D.declOf (scopeOf emptyState) (.val .zero) }

theorem content_s1' : contentOf K (.var 0) (s1' K ρ) = some ((.el0 Nat 0, .err, .bind 0 0, []), s1' K ρ) := by
  have hr : resolve (s1' K ρ) (.var 0) = some (.bind 0 0, []) := rfl
  simp only [contentOf, hr, access_noshape _ _ (rfl : (s1' K ρ).shape = _)]
  rfl

theorem readPlace_s1' (b : Bool) : ∃ s', readPlace K (.var 0) b (s1' K ρ) = some ((fun _ => .el0 Nat 0, ⟨.err, none, none⟩), s') := by
  have : readPlace K (.var 0) b (s1' K ρ) = (match contentOf K (.var 0) (s1' K ρ) with
      | some (a, s') => (if ¬ a.1.whole then (SM.fail : SM Res) else
          if b then pure (fun _ => a.1, ⟨a.2.1, none, none⟩) else do
            setContent K a.2.2.1 a.2.2.2 .moved
            pure (fun _ => a.1, ⟨a.2.1, none, none⟩)) s'
      | none => none) := rfl
  rw [this, content_s1']
  simp only [Sem.whole, not_true_eq_false, ite_false]
  cases b
  · exact ⟨_, rfl⟩
  · exact ⟨_, rfl⟩

theorem run_tHole_subst (l : Nat) (hint : TyM) :
    ∃ s', run K ρ hint (Term.substLoan l .zero (tHole l)) emptyState = some ((fun _ => .el0 Nat 0, ⟨.err, none, none⟩), s') := by
  rw [subst_tHole, run_letIn]
  have h0 : run K ρ .err (.val .zero) emptyState
      = some ((fun φ => meanV K ρ φ .err .zero, ⟨.err, none, none⟩), emptyState) := rfl
  rw [h0]
  simp only [Option.bind]
  rw [run_place]
  obtain ⟨s', h⟩ := readPlace_s1' K ρ (K.D.copy (K.D.placeDecl (scopeOf (s1' K ρ)) (.var 0)))
  exact ⟨_, (congrArg (fun x => Option.bind x _) h).trans rfl⟩

/-! ### 4. run_substLoan fails: the substituted run succeeds, the original fails -/
theorem run_substLoan_false : ¬ ∀ (φ : Future) (hint : TyM) (l : Nat) (w : Value) (t : Term) (s : SState),
    ¬ w.hasLoan l → HintFree K ρ φ w →
    (run K ρ hint (Term.substLoan l w t) s).map (fun (r, s') => (r.1 φ, s'.toMean.val φ))
      = (run K ρ hint t s).map (fun (r, s') =>
          (r.1 (φ.upd l (meanV K ρ φ .err w)), s'.toMean.val (φ.upd l (meanV K ρ φ .err w)))) := by
  intro H
  have := H (fun _ => .err) .err 0 .zero (tHole 0) emptyState (by decide) (fun _ _ => rfl)
  obtain ⟨s', h⟩ := run_tHole_subst K ρ 0 .err
  rw [h, run_tHole] at this
  cases this

/-! ### 3. meanV_substLoan fails at a sealed program reading the hole through a binding -/
theorem meanV_substLoan_false : ¬ ∀ (φ : Future) (hint : TyM) (l : Nat) (w v : Value),
    ¬ w.hasLoan l → HintFree K ρ φ w →
    meanV K ρ φ hint (Value.substLoan l w v) = meanV K ρ (φ.upd l (meanV K ρ φ .err w)) hint v := by
  intro H
  have := H (fun _ => .err) .err 0 .zero (.sealed (tHole 0)) (by decide) (fun _ _ => rfl)
  have e1 : Value.substLoan 0 .zero (.sealed (tHole 0)) = .sealed (Term.substLoan 0 .zero (tHole 0)) := by
    simp [Value.substLoan]
  rw [e1] at this
  obtain ⟨s', h⟩ := run_tHole_subst K ρ 0 .err
  have hl : meanV K ρ (fun _ => .err) .err (.sealed (Term.substLoan 0 .zero (tHole 0))) = .el0 Nat 0 := by
    show (match run K ρ .err _ emptyState with | some ((v, _), _) => v _ | none => .err) = _
    rw [h]
  have hr : meanV K ρ (Future.upd (fun _ => Sem.err) 0 (meanV K ρ (fun _ => .err) .err .zero)) .err (.sealed (tHole 0)) = .err := by
    show (match run K ρ .err _ emptyState with | some ((v, _), _) => v _ | none => .err) = _
    rw [run_tHole]
  rw [hl, hr] at this
  cases this

/-! ### 3'. and at a closure whose code reads the hole -/
example (φ : Future) (hint : TyM) (l : Nat) :
    meanV K ρ φ hint (Value.substLoan l .zero (.clo [] (.val (.loan l)) [])) = .el0 Nat 0 ∧
    meanV K ρ (φ.upd l (meanV K ρ φ .err .zero)) hint (.clo [] (.val (.loan l)) []) = .err := by
  have e1 : Value.substLoan l .zero (.clo [] (.val (.loan l)) []) = .clo [] (.val .zero) [] := by
    simp [Value.substLoan, Value.substLoanList, Value.substLoanRd, Term.substLoan]
  rw [e1]
  exact ⟨rfl, rfl⟩

/-! ### 2. meanV_congr fails: a closure's recorded capture types `rd` are read under the future,
but `Value.loans` does not list their loans -/
def vRd : Value := .clo [.succ .zero] (.place (.proj 0 (.var 0))) [(.other, .loan 7)]

theorem vRd_loans : vRd.loans = [] := rfl

noncomputable def sRd (T : TyM) : SState :=
  stateOf (capsState [Sem.succ (.el0 Nat 0)] [(.other, T)])

theorem meanV_vRd (φ : Future) (hint : TyM) : meanV K ρ φ hint vRd =
    (match run K ρ .err (.place (.proj 0 (.var 0))) (sRd (φ 7).asTy) with
      | some ((v, _), _) => v noFuture
      | none => .err) := rfl

theorem SM.bind_apply {α β : Type 3} (x : SM α) (f : α → SM β) (s : SState) :
    (x >>= f) s = match x s with | some (a, s') => f a s' | none => none := rfl

theorem succ_zero : Sem.succ (.el0 Nat 0) = .el0 Nat 1 := by
  simp [Sem.succ, Sem.asNat, Sem.as]

theorem content_Nat : contentOf K (.proj 0 (.var 0)) (sRd (.ty0 Nat)) =
    some ((.el0 Nat 0, .ty0 Nat, .bind 0 0, [.proj 0]), sRd (.ty0 Nat)) := by
  have hr : resolve (sRd (.ty0 Nat)) (.proj 0 (.var 0)) = some (.bind 0 0, [.proj 0]) := rfl
  simp only [contentOf, hr, access_noshape _ _ (rfl : (sRd (.ty0 Nat)).shape = _)]
  have hv : (sRd (.ty0 Nat)).valAt (.bind 0 0) noFuture = .el0 Nat 1 := by
    show Sem.succ (.el0 Nat 0) = _; exact succ_zero
  have ht : (sRd (.ty0 Nat)).tyAt (.bind 0 0) = .ty0 Nat := rfl
  rw [hv, ht]
  simp [Sem.follow, Sem.step, Sem.asNat, Sem.as]

theorem content_err : contentOf K (.proj 0 (.var 0)) (sRd .err) = none := by
  have hr : resolve (sRd .err) (.proj 0 (.var 0)) = some (.bind 0 0, [.proj 0]) := rfl
  simp only [contentOf, hr, access_noshape _ _ (rfl : (sRd .err).shape = _)]
  have ht : (sRd .err).tyAt (.bind 0 0) = .err := rfl
  rw [ht]
  have hd : TyM.dataOf K.dm K.Γ .err = none := by
    simp [TyM.dataOf, DataModel.paramsOf]
  have hv : (sRd .err).valAt (.bind 0 0) noFuture = .el0 Nat 1 := by
    show Sem.succ (.el0 Nat 0) = _; exact succ_zero
  simp [Sem.follow, Sem.step, Sem.stepField, hd, hv]

theorem updAt_Nat1 (dm : DataModel) (Γ : List IndDecl) (f : Sem → Sem) :
    Sem.updAt dm Γ (.ty0 Nat) f [.proj 0] (.el0 Nat 1) = some (f (.el0 Nat 0)).succ := by
  show (if (TyM.ty0 Nat) = .ty0 Nat then (match Step.proj 0, (Sem.el0 Nat 1).asNat with
      | .proj 0, some (n + 1) => (Sem.updAt dm Γ (.ty0 Nat) f [] (.el0 Nat n)).map Sem.succ
      | _, _ => none) else _) = _
  rw [if_pos rfl]
  have : (Sem.el0 Nat 1).asNat = some 1 := by simp [Sem.asNat, Sem.as]
  rw [this]
  rfl

theorem setContent_Nat : ∃ s', setContent K (.bind 0 0) [.proj 0] .moved (sRd (.ty0 Nat)) = some (⟨⟩, s') := by
  have hv : (sRd (.ty0 Nat)).valAt (.bind 0 0) noFuture = .el0 Nat 1 := by
    show Sem.succ (.el0 Nat 0) = _; exact succ_zero
  have ht : (sRd (.ty0 Nat)).tyAt (.bind 0 0) = .ty0 Nat := rfl
  simp only [setContent, hv, ht, updAt_Nat1]
  exact ⟨_, rfl⟩

theorem meanV_congr_false : ¬ ∀ (φ φ' : Future) (hint : TyM) (v : Value),
    (∀ l ∈ v.loans, φ l = φ' l) → meanV K ρ φ hint v = meanV K ρ φ' hint v := by
  intro H
  have := H (fun _ => .ty (.ty0 Nat)) (fun _ => .err) .err vRd (by simp [vRd_loans])
  rw [meanV_vRd, meanV_vRd] at this
  have a1 : Sem.asTy (.ty (.ty0 Nat)) = .ty0 Nat := rfl
  have a2 : Sem.asTy .err = .err := rfl
  rw [a1, a2, run_place, run_place] at this
  unfold readPlace at this
  rw [SM.bind_apply, SM.bind_apply, content_Nat, content_err] at this
  simp only [Sem.whole, not_true_eq_false, ite_false] at this
  obtain ⟨s', hs⟩ := setContent_Nat K
  by_cases hc : K.D.copy (K.D.placeDecl (scopeOf (sRd (TyM.ty0 Nat))) (Place.proj 0 (Place.var 0))) = true
  · rw [if_pos hc] at this
    cases this
  · rw [if_neg hc, SM.bind_apply, hs] at this
    cases this
end

end Ochr.Meaning
namespace Ochr.Meaning
open Classical
section
variable (K : RunCtx) (ρ : Assignment)

/-! ### (ii) a borrow the run makes is never ended: `let y = Z; let r = &y; y` fails -/
def tBor : Term := .letIn ⟨"y"⟩ .zero (.letIn ⟨"r"⟩ (.borrow (.var 0)) (.place (.var 1)))

theorem run_borrow (p : Place) (hint : TyM) (s : SState) : run K ρ hint (.borrow p) s = borrowPlace K p s := rfl

noncomputable def b1 : SState :=
  emptyState.pushBind { ty := .ty0 Nat, val := fun _ => .el0 Nat 0, decl := K.D.declOf (scopeOf emptyState) .zero }

theorem content_b1 : contentOf K (.var 0) (b1 K) = some ((.el0 Nat 0, .ty0 Nat, .bind 0 0, []), b1 K) := by
  have hr : resolve (b1 K) (.var 0) = some (.bind 0 0, []) := rfl
  simp only [contentOf, hr, access_noshape _ _ (rfl : (b1 K).shape = _)]
  rfl

noncomputable def b2 : SState :=
  (b1 K).freshLoan.2.setAt (.bind 0 0) (fun φ => (Sem.updAt K.dm K.Γ (.ty0 Nat) (fun _ => φ 0) [] (Sem.el0 Nat 0)).getD .err)

theorem borrow_b1 : borrowPlace K (.var 0) (b1 K) = some ((fun _ => .el0 Nat 0, ⟨.ty0 Nat, none, some 0⟩), b2 K) := by
  have : borrowPlace K (.var 0) (b1 K) = (match contentOf K (.var 0) (b1 K) with
      | some ((v, T, pos, steps), s) =>
        if ¬ v.whole then none else
        let (l, s) := s.freshLoan
        let T0 := s.tyAt pos
        let old := s.valAt pos
        let s := s.setAt pos fun φ => (Sem.updAt K.dm K.Γ T0 (fun _ => φ l) steps (old φ)).getD .err
        some (((fun _ => v), ⟨T, none, some l⟩), s)
      | none => none) := rfl
  rw [this, content_b1]
  simp only [Sem.whole, not_true_eq_false, ite_false]
  rfl

noncomputable def b3 : SState :=
  (b2 K).pushBind { ty := TyM.ty0 Nat, val := fun _ => Sem.el0 Nat 0, decl := K.D.declOf (scopeOf (b2 K)) (.borrow (.var 0)) }

theorem content_b3 : contentOf K (.var 1) (b3 K) = some ((.err, .ty0 Nat, .bind 0 0, []), b3 K) := by
  have hr : resolve (b3 K) (.var 1) = some (.bind 0 0, []) := rfl
  simp only [contentOf, hr, access_noshape _ _ (rfl : (b3 K).shape = _)]
  rfl

theorem readPlace_b3 (b : Bool) : readPlace K (.var 1) b (b3 K) = none := by
  have : readPlace K (.var 1) b (b3 K) = (match contentOf K (.var 1) (b3 K) with
      | some (a, s') => (if ¬ a.1.whole then (SM.fail : SM Res) else
          if b then pure (fun _ => a.1, ⟨a.2.1, none, none⟩) else do
            setContent K a.2.2.1 a.2.2.2 .moved
            pure (fun _ => a.1, ⟨a.2.1, none, none⟩)) s'
      | none => none) := rfl
  rw [this, content_b3]
  simp [Sem.whole, SM.fail]

theorem run_tBor (hint : TyM) : run K ρ hint tBor emptyState = none := by
  rw [tBor, run_letIn]
  have h0 : run K ρ .err .zero emptyState = some ((fun _ => .el0 Nat 0, ⟨.ty0 Nat, none, none⟩), emptyState) := rfl
  rw [h0]
  simp only [Option.bind]
  rw [run_letIn, run_borrow]
  rw [show emptyState.pushBind _ = b1 K from rfl, borrow_b1]
  simp only [Option.bind]
  rw [run_place, show (b2 K).pushBind _ = b3 K from rfl, readPlace_b3]
end
end Ochr.Meaning
#print axioms Ochr.Meaning.run_substLoan_false
#print axioms Ochr.Meaning.meanV_substLoan_false
#print axioms Ochr.Meaning.meanV_congr_false
#print axioms Ochr.Meaning.run_tBor
