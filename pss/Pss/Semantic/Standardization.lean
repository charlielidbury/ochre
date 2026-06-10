import Pss.Semantic.WeakHead
import Pss.Semantic.ParRed

/-!
# Shape standardization and convergence transfer

§2 of `pss/docs/03-revised-proof.md`, Lemma 2.2 and Corollary 2.3 — the
heaviest imported fact about plain β (doc §9: prove the three shape cases
directly via parallel-reduction head-step bookkeeping rather than full
standardization if that is lighter; the proof strategy and all internal
machinery belong to this file's implementer).

This file is doc-level API **only**: the five statements below are
exactly what the model files (doc Lemmas 4.4/4.5 and Theorem 7.1)
consume.

Spine convention (cf. `Pss.Semantic.SpineArgs`): argument lists are
outermost-first on both sides of `Forall2`, so the componentwise clause
of the spine case matches the doc's `eᵢ ⟶* dᵢ` positionally, and equal
length is forced by `Forall2` itself.
-/

namespace Pss.Semantic

/-! ## Implementation route (internal machinery)

Kashima-style inductive standard reduction (R. Kashima, *A proof of the
standardization theorem in λ-calculus*, 2000), specialized to the three
target shapes. `Standardization.St t u` packages "a standard reduction
from `t` to `u`": a weak-head prefix `t ↦* ·` followed by standard
reductions of the components of `u`'s top constructor. The engine is
`St.par_absorb : St t p → Par p n → St t n`, a *structural* induction on
the `Par` derivation (no step-count fuel, no lexicographic measure): its
`Par.beta` case composes the two inverted weak-head prefixes with one
`WHStep.beta` and closes by the `St` substitution lemma, recursing only
on `Par` subderivations. Folding along `steps_iff_star_par` from
`St.refl` gives `Steps t u → St t u`; inverting `St` at each target
shape reads off Lemma 2.2.

The direct `Par` head lemma (doc §9's sketch) was rejected: its
`Par.beta` case must recurse on `Par (b[s]) (b'[s'])` at the *same*
convergence index `j` with a non-smaller derivation, so the suggested
lex `(j, Par-derivation)` measure fails unless the statement is
substitution-generalized — at which point it carries strictly more
bookkeeping (exact step arithmetic, `Match` composition along the
`Star Par` fold) than `St` does. -/

namespace Standardization

end Standardization

/-! ## Lemma 2.2 (shape standardization) -/

/-- **Lemma 2.2, λ case** (doc §2): if `t ⟶* λx≤p.q` then
`t ⇓ λx≤p′.q′` with `p′ ⟶* p` and `q′ ⟶* q`. -/
theorem steps_lam_standard {t p q : Term} (h : Steps t (.lam p q)) :
    ∃ j p' q', Converges j t (.lam p' q') ∧ Steps p' p ∧ Steps q' q := by
  sorry

/-- **Lemma 2.2, `Top` case** (doc §2): if `t ⟶* Top` then `t ⇓ Top`. -/
theorem steps_top_standard {t : Term} (h : Steps t .top) :
    ∃ j, Converges j t .top := by
  sorry

/-- **Lemma 2.2, spine case** (doc §2): if `t ⟶* Top(d₁)…(dₙ)` then
`t ⇓ Top(e₁)…(eₙ)` — a spine of the same length — with `eᵢ ⟶* dᵢ`
componentwise. -/
theorem steps_spine_standard {t s : Term} {ds : List Term}
    (h : Steps t s) (hs : SpineArgs s ds) :
    ∃ j u es, Converges j t u ∧ SpineArgs u es ∧ Forall2 Steps es ds := by
  sorry

/-! ## Corollary 2.3 (convergence transfer)

Stated per value constructor, which is the form the model's conversion
lemmas (doc 4.4/4.5) consume: the λ case needs the bound and body
`=β`-related componentwise.
-/

/-- **Corollary 2.3, λ case** (doc §2): if `t =β λx≤a.b` then
`t ⇓ λx≤a′.b′` with `a′ =β a` and `b′ =β b`. -/
theorem beta_lam_converges {t a b : Term} (h : Beta t (.lam a b)) :
    ∃ j a' b', Converges j t (.lam a' b') ∧ Beta a' a ∧ Beta b' b := by
  sorry

/-- **Corollary 2.3, `Top` case** (doc §2): if `t =β Top` then
`t ⇓ Top`. -/
theorem beta_top_converges {t : Term} (h : Beta t .top) :
    ∃ j, Converges j t .top := by
  sorry

end Pss.Semantic
