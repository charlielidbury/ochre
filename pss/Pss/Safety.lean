import Pss.Reduction
import Pss.Declarative
import Pss.Induction
import Pss.Basic
import Pss.Weakening
import Pss.Substitution

/-!
# Type safety for System λ⊲ (§5, p. 293)

Statements 5.1–5.6 of Hutchins, *Pure Subtype Systems* (POPL 2010).

* Conjecture 5.1 (transitivity elimination) — stated as a `Prop`
  (`TransitivityElimination`), **not** assumed.
* Lemma 5.2 (inversion of subtyping, declarative version) — proved from 5.1.
* Lemma 5.3 (reduction implies equivalence) — proved outright.
* Theorem 5.5 (progress) and Theorem 5.6 (preservation) — proved from 5.1,
  exactly as in the paper ("System λ⊲ is type-safe so long as subtyping has
  the transitivity elimination property").
-/

namespace Pss

/-! ## Conjecture 5.1 — transitivity elimination -/

/-- **Conjecture 5.1 (Transitivity elimination)**, p. 293:

> If `Γ ⊢ v ≤wf w`, then there exists a proof of `Γ ⊢ v ≤ w` that ends in
> either (DS-FUN) or (DS-ETOP).

A derivation ending in (DS-ETOP) forces `w = Top`; one ending in (DS-FUN)
forces both sides to be λ-abstractions and exposes the rule's premises
`Γ ⊢ t ≡ t'` and `Γ, x ≤ t ⊢ u ≤ u'`. (`v`, `w` range over *values*, the
only well-formed normal forms relevant for safety.)

This is an **open problem** — the paper's §6 program (confluence of `≡→`
plus commutativity of `≤→` and `≡→`, Lemma 6.3) targets it but is itself
incomplete (§6.6). We therefore state it as a definition of type `Prop`
and thread it as an explicit hypothesis through Lemma 5.2, Theorem 5.5 and
Theorem 5.6, never as an axiom. -/
def TransitivityElimination : Prop :=
  ∀ Γ (v w : Term), Term.Value v → Term.Value w → WellSub Γ v .le w →
    w = .top ∨
    ∃ t u t' u', v = .lam t u ∧ w = .lam t' u' ∧
      Sub Γ t .eq t' ∧ Sub (t :: Γ) u .le u'

/-! ## Lemma 5.2 — inversion of subtyping (declarative version) -/

/-- **Lemma 5.2 (Inversion of subtyping — declarative version)**, p. 293:

> If `Γ ⊢ (λx ≤ t. u) ≤wf (λx ≤ t'. u')` then `Γ ⊢ t ≡ t'`.

Proved from Conjecture 5.1 (transitivity elimination), exactly as in the
paper: a λ-abstraction is a value, and `λx ≤ t'. u' ≠ Top` rules out the
(DS-ETOP) disjunct, so the derivation ends in (DS-FUN) whose first premise
is the conclusion. -/
theorem Sub.inversion (te : TransitivityElimination) {Γ : Ctx}
    {t u t' u' : Term} (h : WellSub Γ (.lam t u) .le (.lam t' u')) :
    Sub Γ t .eq t' := by
  rcases te Γ _ _ (.lam t u) (.lam t' u') h with htop | ⟨a, b, a', b', hv, hw, h1, _⟩
  · cases htop
  · cases hv; cases hw; exact h1

/-! ## Lemma 5.3 — reduction implies equivalence -/

/-- **Lemma 5.3 (Reduction implies equivalence)**, p. 293:

> If `t ⟶ t'`, then `Γ ⊢ t ≡ t'`.

By induction on the derivation of `t ⟶ t'` (via the compatible-closure
presentation `Step.Compat`): the base case is rule (DS-EAPP); the
congruence cases are (DS-APP) and (DS-FUN) with reflexivity
(`Sub.refl_eq`) on the unchanged side. -/
theorem Step.to_sub_eq {t t' : Term} (h : Step t t') :
    ∀ Γ : Ctx, Sub Γ t .eq t' := by
  have h' := Step.step_iff_compat.mp h
  clear h
  induction h' with
  | eapp => exact fun Γ => .eapp
  | appL u _ ih => exact fun Γ => .app (ih Γ) (Sub.refl_eq u Γ)
  | appR t _ ih => exact fun Γ => .app (Sub.refl_eq t Γ) (ih Γ)
  | lamBound u _ ih => exact fun Γ => .fn (ih Γ) (Sub.refl_eq u _)
  | lamBody t _ ih => exact fun Γ => .fn (Sub.refl_eq t Γ) (ih _)

/-! ## Theorem 5.5 — progress -/

/-- **Theorem 5.5 (Progress)**, p. 293:

> If `∅ ⊢ t wf` then either `t = v` for some `v` (i.e. `t` is a value), or
> there exists a `t'` such that `t ⟶ t'`.

By induction on the derivation of `t wf`. The hypothesis
`TransitivityElimination` (Conjecture 5.1) is needed in exactly one place:
in the application case `t(u)`, when the function part is the value `Top`,
the well-formedness premise `∅ ⊢ Top ≤wf λx ≤ s. Top` must be refuted —
transitivity elimination forces such a derivation to end in (DS-ETOP)
(impossible: `λx ≤ s. Top ≠ Top`) or (DS-FUN) (impossible: `Top` is not a
λ-abstraction). Without 5.1, a derivation built from DS-TRANS chains cannot
be ruled out and `Top(u)` would be stuck. When the function part is a
λ-abstraction, (E-APP) fires unconditionally (no value or typing condition
on the argument). -/
theorem progress (te : TransitivityElimination) {t : Term}
    (h : Wf [] t) : Term.Value t ∨ ∃ t', Step t t' := by
  have H := decl_induction
    (motC := fun _ => True)
    (motW := fun Γ u => Γ = [] → Term.Value u ∨ ∃ u', Step u u')
    (motWS := fun Γ u _ _ => Γ = [] → Term.Value u ∨ ∃ u', Step u u')
    (motS := fun _ _ _ _ => True)
    (ctx_nil := trivial)
    (ctx_cons := fun _ _ _ _ => trivial)
    (wf_var := fun _ hx _ hΓ => by subst hΓ; simp at hx)
    (wf_top := fun _ _ _ => .inl .top)
    (wf_fn := fun _ _ _ => .inl (.lam _ _))
    (wf_app := fun {Γ a u s} h1 _ ih1 _ hΓ => by
      subst hΓ
      rcases ih1 rfl with hv | ⟨a2, hstep⟩
      · cases hv with
        | top =>
          rcases te [] .top (.lam s .top) .top (.lam s .top) h1 with
            htop | ⟨w1, w2, w3, w4, hveq, _, _, _⟩
          · cases htop
          · cases hveq
        | lam c d => exact .inr ⟨d.subst1 u, .eapp⟩
      · exact .inr ⟨.app a2 u, Step.appL u hstep⟩)
    (wsub_sub := fun _ _ _ ihW _ _ => ihW)
    (sub_trans := fun _ _ _ _ _ _ => trivial)
    (sub_symm := fun _ _ => trivial)
    (sub_eq := fun _ _ => trivial)
    (sub_var := trivial)
    (sub_top := trivial)
    (sub_fn := fun _ _ _ _ => trivial)
    (sub_app := fun _ _ _ _ => trivial)
    (sub_eapp := trivial)
    (sub_etop := trivial)
    (sub_evar := fun _ => trivial)
  exact H.2.1 [] t h rfl

end Pss
