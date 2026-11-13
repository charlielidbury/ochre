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

/-- Filling a loan is fixing the future, for values. The hypotheses are m2-proofs' C and (P1) the
filler's declared shape. -/
theorem meanV_substLoan (φ : Future) (hint : TyS) (l : Nat) (w v : Value)
    (hw : ¬ w.hasLoan l) (hf : HintFree K ρ φ w) (hD : DecInvariant K.D l w) (hc : FillShape K ρ φ l w) :
    meanV K ρ φ hint (Value.substLoan l w v) = meanV K ρ (φ.upd l (meanV K ρ φ (.plain .err) w)) hint v := by
  sorry

/-- Filling a loan is fixing the future, for a term's run: the run at `φ` of the substituted term
from a state is the run at the fixed future of the term from the same state (hypotheses B, C and
(P1) the filler's declared shape). -/
theorem run_substLoan (φ : Future) (hint : TyS) (l : Nat) (w : Value) (t : Term) (s : SState)
    (hw : ¬ w.hasLoan l) (hf : HintFree K ρ φ w) (hD : DecInvariant K.D l w) (hc : FillShape K ρ φ l w)
    (hs : StateFreeOf s l) :
    run K ρ φ hint (Term.substLoan l w t) s
      = run K ρ (φ.upd l (meanV K ρ φ (.plain .err) w)) hint t s := by
  sorry

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

/-- The run's result does not depend on the starting label counter, as long as it is above every
loan of the term and of the state (m2-proofs' D): fresh labels are names. Needed because a
sealed program's counter, `emptyState (t.loans.foldl max 0 + 1)`, changes under substitution. Only the
result's meaning is compared: a returned borrow's label and the state's labels are the counter. -/
theorem run_counter_indep (φ : Future) (hint : TyS) (t : Term) (s : SState) (n n' : Nat)
    (hn : ∀ l ∈ t.loans, l < n) (hn' : ∀ l ∈ t.loans, l < n') (hs : ∀ l ∈ s.positions.filterMap s.shape, l < min n n') :
    (run K ρ φ hint t { s with nextLoan := n }).map (·.1.1)
      = (run K ρ φ hint t { s with nextLoan := n' }).map (·.1.1) := by
  sorry

end

end Ochr.Meaning
