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

/-! ### Weak-head steps are stable under substitution and renaming -/

/-- A weak-head step is stable under simultaneous substitution (the head
redex stays the head redex). -/
theorem whStep_subst (σ : Nat → Term) {t t' : Term} (h : WHStep t t') :
    WHStep (t.subst σ) (t'.subst σ) := by
  induction h with
  | @beta a b s =>
    rw [Term.subst_subst1]
    exact WHStep.beta
  | head u _ ih => exact WHStep.head (u.subst σ) ih

/-- A weak-head step is stable under renaming. -/
theorem whStep_rename (ρ : Nat → Nat) {t t' : Term} (h : WHStep t t') :
    WHStep (t.rename ρ) (t'.rename ρ) := by
  rw [Term.rename_eq_subst, Term.rename_eq_subst]
  exact whStep_subst _ h

/-- Weak-head prefixes lift through application on the left
(`Star`-closure of `WHStep.head`). -/
theorem starWH_appL (u : Term) {t t' : Term} (h : Star WHStep t t') :
    Star WHStep (.app t u) (.app t' u) :=
  h.map (fun x => Term.app x u) (fun hs => WHStep.head u hs)

/-- `↦* ⊆ ⟶*`. -/
theorem starWH_toSteps {t u : Term} (h : Star WHStep t u) : Steps t u :=
  h.mono (fun hs => hs.toStep)

/-- A weak-head prefix is an exact-step evaluation of some length. -/
theorem starWH_evals {t u : Term} (h : Star WHStep t u) :
    ∃ j, Evals j t u := by
  induction h with
  | refl => exact ⟨0, .refl⟩
  | head hs _ ih => obtain ⟨j, hj⟩ := ih; exact ⟨j + 1, .step hs hj⟩

/-! ### Standard reduction, inductively (Kashima 2000) -/

/-- `St t u`: a *standard* reduction from `t` to `u` — a weak-head prefix
`t ↦* ·`, then standard reductions of the components under `u`'s top
constructor. One constructor per target shape. -/
inductive St : Term → Term → Prop where
  | var {t : Term} {x : Nat} :
      Star WHStep t (.var x) → St t (.var x)
  | top {t : Term} :
      Star WHStep t .top → St t .top
  | lam {t a b a' b' : Term} :
      Star WHStep t (.lam a b) → St a a' → St b b' → St t (.lam a' b')
  | app {t t₁ t₂ u₁ u₂ : Term} :
      Star WHStep t (.app t₁ t₂) → St t₁ u₁ → St t₂ u₂ → St t (.app u₁ u₂)

/-- Standard reduction is reflexive. -/
theorem St.refl : (t : Term) → St t t
  | .var _ => .var .refl
  | .top => .top .refl
  | .lam a b => .lam .refl (St.refl a) (St.refl b)
  | .app t u => .app .refl (St.refl t) (St.refl u)

/-- Standard reduction absorbs a weak-head prefix on the left. -/
theorem St.hap_prepend {t t' u : Term} (hap : Star WHStep t t')
    (h : St t' u) : St t u := by
  cases h with
  | var h' => exact .var (hap.trans h')
  | top h' => exact .top (hap.trans h')
  | lam h' ha hb => exact .lam (hap.trans h') ha hb
  | app h' h₁ h₂ => exact .app (hap.trans h') h₁ h₂

/-- Standard reduction is stable under renaming. -/
theorem St.rename {t u : Term} (h : St t u) :
    ∀ ρ : Nat → Nat, St (t.rename ρ) (u.rename ρ) := by
  induction h with
  | var hap =>
    exact fun ρ => .var (hap.map (Term.rename ρ) (whStep_rename ρ))
  | top hap =>
    exact fun ρ => .top (hap.map (Term.rename ρ) (whStep_rename ρ))
  | lam hap _ _ iha ihb =>
    exact fun ρ => .lam (hap.map (Term.rename ρ) (whStep_rename ρ))
      (iha ρ) (ihb (Term.liftRen ρ))
  | app hap _ _ ih₁ ih₂ =>
    exact fun ρ => .app (hap.map (Term.rename ρ) (whStep_rename ρ))
      (ih₁ ρ) (ih₂ ρ)

/-- **Substitution lemma** for standard reduction (Kashima's Lemma 3),
σ-calculus form: reduce the term and the substitution simultaneously. -/
theorem St.subst {t u : Term} (h : St t u) :
    ∀ {σ τ : Nat → Term}, (∀ x, St (σ x) (τ x)) →
      St (t.subst σ) (u.subst τ) := by
  induction h with
  | @var t x hap =>
    intro σ τ hστ
    exact St.hap_prepend (hap.map (Term.subst σ) (whStep_subst σ)) (hστ x)
  | top hap =>
    intro σ τ _
    exact .top (hap.map (Term.subst σ) (whStep_subst σ))
  | lam hap _ _ iha ihb =>
    intro σ τ hστ
    refine .lam (hap.map (Term.subst σ) (whStep_subst σ)) (iha hστ) (ihb ?_)
    intro n
    cases n with
    | zero => exact St.refl _
    | succ n => exact St.rename (hστ n) (· + 1)
  | app hap _ _ ih₁ ih₂ =>
    intro σ τ hστ
    exact .app (hap.map (Term.subst σ) (whStep_subst σ)) (ih₁ hστ) (ih₂ hστ)

/-- Substitution lemma, `subst1` form (the β-case combinator of
`St.par_absorb`). -/
theorem St.subst1 {b b' s s' : Term} (hb : St b b') (hs : St s s') :
    St (b.subst1 s) (b'.subst1 s') :=
  St.subst hb fun x => by
    cases x with
    | zero => exact hs
    | succ n => exact St.refl _

/-- **The engine** (Kashima's Lemma 4): standard reduction absorbs a
parallel step on the right. Structural induction on the `Par`
derivation only — the `beta` case inverts the two weak-head prefixes,
appends one `WHStep.beta`, and closes by the substitution lemma. -/
theorem St.par_absorb {p n : Term} (hpar : Par p n) :
    ∀ {t : Term}, St t p → St t n := by
  induction hpar with
  | var => exact fun hst => hst
  | top => exact fun hst => hst
  | lam _ _ iha ihb =>
    intro t hst
    cases hst with
    | lam hap h₁ h₂ => exact .lam hap (iha h₁) (ihb h₂)
  | app _ _ ihf ihu =>
    intro t hst
    cases hst with
    | app hap h₁ h₂ => exact .app hap (ihf h₁) (ihu h₂)
  | beta _ _ ihb ihs =>
    intro t hst
    cases hst with
    | app hap h₁ h₂ =>
      cases h₁ with
      | lam hap₁ _ hd =>
        exact St.hap_prepend
          (hap.trans ((starWH_appL _ hap₁).tail WHStep.beta))
          (St.subst1 (ihb hd) (ihs h₂))

/-- Standard reduction absorbs a `Par`-sequence on the right. -/
theorem St.starPar_absorb {p n : Term} (h : Star Par p n) :
    ∀ {t : Term}, St t p → St t n := by
  induction h with
  | refl => exact fun hst => hst
  | head hpq _ ih => exact fun hst => ih (St.par_absorb hpq hst)

/-- **Every reduction has a standard counterpart**: `⟶* ⊆ St`
(Kashima's standardization theorem, via `steps_iff_star_par`). -/
theorem st_of_steps {t u : Term} (h : Steps t u) : St t u :=
  St.starPar_absorb (steps_iff_star_par.mp h) (St.refl t)

/-- Standard reduction sequentializes: `St ⊆ ⟶*`. -/
theorem St.toSteps {t u : Term} (h : St t u) : Steps t u := by
  induction h with
  | var hap => exact starWH_toSteps hap
  | top hap => exact starWH_toSteps hap
  | lam hap _ _ iha ihb =>
    exact (starWH_toSteps hap).trans (Steps.lam iha ihb)
  | app hap _ _ ih₁ ih₂ =>
    exact (starWH_toSteps hap).trans (Steps.app ih₁ ih₂)

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
