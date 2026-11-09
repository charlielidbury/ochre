import Ochr.Meaning.Run
import Ochr.Meaning.Subst

/-!
# The two lemmas that close milestone 2 (statements; docs/27 Lemma 3, docs/31 §Milestone 2)

* The **sealed-substitution lemma**: filling a loan is fixing the future. For `w` not mentioning
  `ℓ`, `⟦v[loan ℓ := w]⟧_{ρ,φ} = ⟦v⟧_{ρ, φ[ℓ ↦ ⟦w⟧_{ρ,φ}]}`, and the same for a term's run from a
  state. It is what makes the checker's [End] (a substitution plus re-normalisation) equal to
  `Mean.semEnd`, and a fill's re-run equal to the fill read at the fixed future (docs/27 §7, N3).
  The checker's substitution re-normalises sealed programs; a sealed program means its run, so
  re-normalisation is covered by the run's own clause and needs no separate statement here.
* **Dependence**: a meaning reads the future only at the loans of the value (docs/27 Lemma 3,
  second half; `State2.ev_congr`).

Both are proved by induction on the value or term, through the mutual block of `Run.lean`.
-/

namespace Ochr.Meaning

section
variable (K : RunCtx) (ρ : Assignment)

/-- `w`'s meaning does not depend on the type it is read at (a value that records its
parameters, or holds none). -/
def HintFree (φ : Future) (w : Value) : Prop := ∀ h h', meanV K ρ φ h w = meanV K ρ φ h' w

/-- Filling a loan is fixing the future, for values. -/
theorem meanV_substLoan (φ : Future) (hint : TyM) (l : Nat) (w v : Value)
    (hw : ¬ w.hasLoan l) (hf : HintFree K ρ φ w) :
    meanV K ρ φ hint (Value.substLoan l w v) = meanV K ρ (φ.upd l (meanV K ρ φ .err w)) hint v := by
  sorry

/-- Filling a loan is fixing the future, for a term's run: the run of the substituted term from
a state is the run of the term from the state read under the fixed future. -/
theorem run_substLoan (φ : Future) (hint : TyM) (l : Nat) (w : Value) (t : Term) (s : SState)
    (hw : ¬ w.hasLoan l) (hf : HintFree K ρ φ w) :
    (run K ρ hint (Term.substLoan l w t) s).map (fun (r, s') => (r.1 φ, s'.toMean.val φ))
      = (run K ρ hint t s).map (fun (r, s') =>
          (r.1 (φ.upd l (meanV K ρ φ .err w)), s'.toMean.val (φ.upd l (meanV K ρ φ .err w)))) := by
  sorry

/-- A value's meaning depends on the future only at its loans. -/
theorem meanV_congr (φ φ' : Future) (hint : TyM) (v : Value)
    (h : ∀ l ∈ v.loans, φ l = φ' l) : meanV K ρ φ hint v = meanV K ρ φ' hint v := by
  sorry

end

end Ochr.Meaning
