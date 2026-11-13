import Ochr.Meaning.Run
import Ochr.Meaning.Subst
import Ochr.Meaning.Locality
import Ochr.Meaning.LocalityRun
import Ochr.Meaning.SubstDefs
import Ochr.Meaning.RunSubst

/-!
# The two lemmas that close milestone 2 (statements; docs/27 Lemma 3, docs/31 §Milestone 2)

* The **sealed-substitution lemma**: filling a loan is fixing the future. For `w` not mentioning
  `ℓ`, `⟦v[loan ℓ := w]⟧_{ρ,φ} = ⟦v⟧_{ρ, φ[ℓ ↦ ⟦w⟧_{ρ,φ}]}`, and the same for a term's run: the
  run at `φ` of the substituted term is the run at `φ[ℓ ↦ ⟦w⟧]` of the term (D10: the run is
  per-future, and a free label is read from the future). It is what makes the checker's [End]
  (a substitution plus re-normalisation) equal to `Mean.semEnd`, and a fill's re-run equal to
  the fill read at the fixed future (docs/27 §7, N3). Re-normalisation keeping the meaning is
  the run's own `.sealed` clause.
* **Dependence**: a meaning reads the future only at the loans of the value, where "loans"
  includes those inside a closure's recorded capture types (`Value.hasLoan`, which looks inside
  `rd`, where `Value.loans` does not: m2-proofs' counterexample).

Both are proved by induction on the value or term, through the mutual block of `Run.lean`. The
counterexamples that refuted the earlier statements are in the scratchpad file `CE.lean` of the
session that found them (m2-proofs, 2026-11-09); they should become regression checks once the
run is decidable on them.
-/

namespace Ochr.Meaning

section
variable (K : RunCtx) (ρ : Assignment)

/-- A value's meaning depends on the future only at the loans it holds anywhere, its closures'
recorded capture types included. (With D13's fixes every borrow the run makes is ended before
it is read or when it is discarded, so no fresh label leaks into a meaning.) -/
theorem meanV_congr (φ φ' : Future) (hint : TyS) (v : Value)
    -- PROPOSAL (m2-proofs, statement): a global carries no borrow label (part (P) of the locality
    -- induction, `run_rinv`'s `.const` clause: a labelled global bound by a `let` would make the
    -- binding hold a label the state never issued)
    (hK : ∀ n, (K.C.global n).2.label = none)
    (h : ∀ l, v.hasLoan l → φ l = φ' l) : meanV K ρ φ hint v = meanV K ρ φ' hint v :=
  meanV_congrE K ρ φ φ' hK v hint h

/-- Future-locality of the run (m2-proofs' form): if the future changes only at labels outside
`L`, where `L` holds of every loan of the term and the state factors through `L` (each position's
meaning depends only on the future restricted to `L`), the run is unchanged. "Factors through"
rather than pointwise `dependsOn`: a value can change when infinitely many labels change together
while depending on no single one. No live-label clause is needed, since `access` fixes the
future only at live labels; it holds because every borrow the run makes is ended before it is
read or when it is discarded (D13). -/
theorem run_congr (φ φ' : Future) (hint : TyS) (t : Term) (s : SState) (L : Nat → Prop)
    (hφ : ∀ l, L l → φ l = φ' l) (ht : ∀ l, t.anyAtom (· == .loan l) → L l)
    (hs : ∀ p ψ ψ', (∀ l, L l → ψ l = ψ' l) → s.valAt p ψ = s.valAt p ψ')
    -- PROPOSAL (m2-proofs): the starting state's holders are acyclic and label-ordered (I2 of
    -- `Locality.lean`), so ending a label removes every dependence on it and the closed future
    -- converges; and every shape entry is a real position with a label below the counter, so
    -- fresh labels never collide with the state's and a pushed position never inherits an entry
    (hord : ∀ r x, r ∈ s.positions → s.shape r = some x →
      FT (fun y => (L y ∧ ¬ s.Live y) ∨ (s.Live y ∧ x < y)) (s.valAt r))
    (hsh : ∀ p x, s.shape p = some x → p ∈ s.positions ∧ x < s.nextLoan)
    -- PROPOSAL (m2-proofs, statement): a global carries no borrow label (as `meanV_congr`)
    (hK : ∀ n, (K.C.global n).2.label = none) :
    run K ρ φ hint t s = run K ρ φ' hint t s :=
  run_congrE K ρ φ φ' hK t hint s L hφ ht ⟨fun p => FT.mono (fun _ hy => .inl hy) (hs p), hord, hsh⟩

/-- The run's result does not depend on the starting label counter (m2-proofs' D): fresh labels
are names. As first stated (any state whose shape labels are below both counters) this is false,
finding 7: a position may read a label at or above a counter, which one run issues and the other
does not. Restated for the empty state, and compared on the result's meaning and shape. Not used:
with a sealed program run from the counter 0 (PROPOSAL 8) the substitution lemmas need no counter
lemma; kept as the statement of the renaming lemma, should a counter-dependent run return. -/
theorem run_counter_indep (φ : Future) (hint : TyS) (t : Term) (n n' : Nat)
    (hn : ∀ l ∈ t.loans, l < n) (hn' : ∀ l ∈ t.loans, l < n') :
    (run K ρ φ hint t (emptyState n)).map (fun r => (r.1.1, r.1.2.shape))
      = (run K ρ φ hint t (emptyState n')).map (fun r => (r.1.1, r.1.2.shape)) := by
  sorry

/-- The filler, at the fixed future `φ[ℓ ↦ ⟦w⟧]`, means the loan and has its type. -/
theorem fillOK_upd (φ : Future) (l : Nat) (w : Value) (hK : ∀ n, (K.C.global n).2.label = none)
    (hw : ¬ w.hasLoan l) (hf : HintFree K ρ φ w) (hD : DecInvariant K.D l w) (hc : FillShape K ρ φ l w) :
    FillOK K ρ (φ.upd l (meanV K ρ φ (.plain .err) w)) l w := by
  have hw' : ∀ y, w.anyAtom (· == .loan y) = true → y ≠ l := fun y hy e => hw (by subst e; exact hy)
  have hagree : ∀ y, y ≠ l → (φ.upd l (meanV K ρ φ (.plain .err) w)) y = φ y :=
    fun y hy => Future.upd_other _ _ hy
  refine ⟨fun hint => ?_, fun hint s => ?_, hD⟩
  · rw [meanV_congr K ρ _ φ hint w hK (fun y hy => hagree y (hw' y hy)), hf hint (.plain .err), Future.upd_same]
  · have h0 := hc hint (emptyState 0)
    have hr := run_congrE K ρ φ (φ.upd l (meanV K ρ φ (.plain .err) w)) hK (.val w) hint (emptyState 0)
      (fun y => y ≠ l) (fun y hy => (hagree y hy).symm) (fun y hy => hw' y hy) (rinv_emptyState _)
    rw [run_val_def, run_val_def] at h0 hr ⊢
    simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h0 hr ⊢
    rw [← hr.1.2]
    exact h0

/-- Filling a loan is fixing the future, for values. The hypotheses are m2-proofs' C and (P1) the
filler's declared shape. -/
theorem meanV_substLoan (φ : Future) (hint : TyS) (l : Nat) (w v : Value)
    (hw : ¬ w.hasLoan l) (hf : HintFree K ρ φ w) (hD : DecInvariant K.D l w) (hc : FillShape K ρ φ l w)
    -- PROPOSAL (m2-proofs, statement): a global carries no borrow label (as `meanV_congr`)
    (hK : ∀ n, (K.C.global n).2.label = none) :
    meanV K ρ φ hint (Value.substLoan l w v) = meanV K ρ (φ.upd l (meanV K ρ φ (.plain .err) w)) hint v := by
  have hw0 : w.anyAtom (· == .loan l) = false := by
    cases h : w.anyAtom (· == .loan l)
    · rfl
    · exact absurd h hw
  rw [meanV_congr K ρ φ (φ.upd l (meanV K ρ φ (.plain .err) w)) hint _ hK (fun y hy => by
      have hyl : y ≠ l := fun e => by subst e; simp [Value.hasLoan, noLoan_substLoanV y w hw0 v] at hy
      exact (Future.upd_other _ _ hyl).symm)]
  exact meanV_substSame K ρ _ l w (fillOK_upd K ρ φ l w hK hw hf hD hc) v hint

/-- Filling a loan is fixing the future, for a term's run: the run at `φ` of the substituted term
from a state is the run at the fixed future of the term from the same state (hypotheses B, C and
(P1) the filler's declared shape). -/
theorem run_substLoan (φ : Future) (hint : TyS) (l : Nat) (w : Value) (t : Term) (s : SState)
    (hw : ¬ w.hasLoan l) (hf : HintFree K ρ φ w) (hD : DecInvariant K.D l w) (hc : FillShape K ρ φ l w)
    (hs : StateFreeOf s l)
    -- PROPOSAL (m2-proofs, statement): `run_congr`'s state hypotheses, at `L = (· ≠ ℓ)`: the
    -- holders are label-ordered and every shape entry is a real position below the counter; and a
    -- global carries no borrow label
    (hord : ∀ r x, r ∈ s.positions → s.shape r = some x →
      FT (fun y => (y ≠ l ∧ ¬ s.Live y) ∨ (s.Live y ∧ x < y)) (s.valAt r))
    (hsh : ∀ p x, s.shape p = some x → p ∈ s.positions ∧ x < s.nextLoan)
    (hK : ∀ n, (K.C.global n).2.label = none) :
    run K ρ φ hint (Term.substLoan l w t) s
      = run K ρ (φ.upd l (meanV K ρ φ (.plain .err) w)) hint t s := by
  have hw0 : w.anyAtom (· == .loan l) = false := by
    cases h : w.anyAtom (· == .loan l)
    · rfl
    · exact absurd h hw
  have hfree : ∀ p ψ₁ ψ₂, (∀ y, y ≠ l → ψ₁ y = ψ₂ y) → s.valAt p ψ₁ = s.valAt p ψ₂ := by
    intro p ψ₁ ψ₂ h
    rw [← hs.1 p ψ₁ (ψ₂ l)]
    congr 1
    funext y
    by_cases e : y = l
    · subst e; exact Future.upd_same _ _ _
    · rw [Future.upd_other _ _ e]; exact h y e
  rw [run_congr K ρ φ (φ.upd l (meanV K ρ φ (.plain .err) w)) hint _ s (fun y => y ≠ l)
      (fun y hy => (Future.upd_other _ _ hy).symm)
      (fun y hy e => by subst e; simp [noLoan_substLoanT y w hw0 t] at hy) hfree hord hsh hK]
  exact congrFun (run_substSame K ρ _ l w (fillOK_upd K ρ φ l w hK hw hf hD hc) t hint) s

end

end Ochr.Meaning
