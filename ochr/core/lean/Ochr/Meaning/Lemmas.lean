import Ochr.Meaning.Run
import Ochr.Meaning.Subst

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

/-- `w`'s meaning does not depend on the type it is read at (a value that records its
parameters, or holds none). -/
def HintFree (φ : Future) (w : Value) : Prop := ∀ h h', meanV K ρ φ h w = meanV K ρ φ h' w

/-- Filling a loan is fixing the future, for values. -/
theorem meanV_substLoan (φ : Future) (hint : TyS) (l : Nat) (w v : Value)
    (hw : ¬ w.hasLoan l) (hf : HintFree K ρ φ w) :
    meanV K ρ φ hint (Value.substLoan l w v) = meanV K ρ (φ.upd l (meanV K ρ φ (.plain .err) w)) hint v := by
  sorry

/-- Filling a loan is fixing the future, for a term's run: the run at `φ` of the substituted term
from a state is the run at the fixed future of the term from the same state. -/
theorem run_substLoan (φ : Future) (hint : TyS) (l : Nat) (w : Value) (t : Term) (s : SState)
    (hw : ¬ w.hasLoan l) (hf : HintFree K ρ φ w) :
    run K ρ φ hint (Term.substLoan l w t) s
      = run K ρ (φ.upd l (meanV K ρ φ (.plain .err) w)) hint t s := by
  sorry

/-- A value's meaning depends on the future only at the loans it holds anywhere, its closures'
recorded capture types included. -/
theorem meanV_congr (φ φ' : Future) (hint : TyS) (v : Value)
    (h : ∀ l, v.hasLoan l → φ l = φ' l) : meanV K ρ φ hint v = meanV K ρ φ' hint v := by
  sorry

end

end Ochr.Meaning
