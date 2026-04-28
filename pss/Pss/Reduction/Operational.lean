import Pss.Syntax.LocallyNameless
import Mathlib.Logic.Relation

/-! # `Pss.Reduction.Operational` — small-step operational reduction

The operational small-step reduction `t ↦ t'` is defined identically in both
papers — plain β plus context closure (Hutchins 2010 Fig. 1 E-Cong + E-App;
Pasquale & García-Pérez 2024 Fig. on operational semantics Os-Bet + Os-Con).

This file provides:

* `Step` — single-step reduction with cofinite quantification under binders.
* `Step.lc_left`, `Step.lc_right` — local-closure preservation.
* `Step.app_inv` — inversion lemma for `Step (.app t u) e'`.
* `Step.Star` — reflexive-transitive closure.
* `EvalCtx` — evaluation contexts (optional helper).

See `PLAN.md` §3 (`Pss.Reduction.Operational` module spec).
-/

namespace Pss

/-- Small-step operational reduction.

Hutchins 2010 Fig. 1 (E-Cong, E-App) and Pasquale & García-Pérez 2024
operational-semantics figure (Os-Con, Os-Bet) define the same relation:
plain β-reduction plus full context closure. The `abs` cases use cofinite
quantification because we can only step under a binder if every
fresh-name instantiation steps (Aydemir-style locally-nameless idiom). -/
inductive Step : Term → Term → Prop
  | beta {bound body arg : Term} :
      Term.LC (.abs bound body) →
      Term.LC arg →
      Step (.app (.abs bound body) arg) (Term.opening arg body)
  | appL {t t' u : Term} :
      Step t t' →
      Term.LC u →
      Step (.app t u) (.app t' u)
  | appR {t u u' : Term} :
      Term.LC t →
      Step u u' →
      Step (.app t u) (.app t u')
  | absBound {bound bound' body : Term} (L : Finset String) :
      Step bound bound' →
      (∀ x, x ∉ L → Term.LC (Term.opening (.fvar x) body)) →
      Step (.abs bound body) (.abs bound' body)
  | absBody {bound body body' : Term} (L : Finset String) :
      Term.LC bound →
      (∀ x, x ∉ L → Step (Term.opening (.fvar x) body) (Term.opening (.fvar x) body')) →
      Step (.abs bound body) (.abs bound body')

@[inherit_doc] infix:50 " ↦ " => Step

namespace Step

/-! ## Local-closure preservation -/

/-- Every reducible term is locally closed. -/
theorem lc_left {t t' : Term} (h : t ↦ t') : Term.LC t := by
  induction h with
  | beta hAbs hArg => exact Term.LC.app hAbs hArg
  | appL _ huLC iht => exact Term.LC.app iht huLC
  | appR htLC _ ihu => exact Term.LC.app htLC ihu
  | @absBound bound bound' body L _ hbody iht =>
      exact Term.LC.abs L iht hbody
  | @absBody bound body body' L hbound _ ihbody =>
      -- ihbody : ∀ x, x ∉ L → Term.LC (body^[x])
      exact Term.LC.abs L hbound ihbody

/-- Reduction preserves local closure. -/
theorem lc_right {t t' : Term} (h : t ↦ t') : Term.LC t' := by
  induction h with
  | @beta bound body arg hAbs hArg =>
      -- We need LC (Term.opening arg body). Use subst_intro + subst_lc.
      -- From hAbs : LC (abs bound body), we have a cofinite-quantified body.
      cases hAbs with
      | abs L _ hbodyLC =>
          classical
          obtain ⟨x, hx⟩ := Term.exists_fresh (L ∪ Term.fv body)
          have hxL : x ∉ L := by
            intro h'
            exact hx (Finset.mem_union.mpr (Or.inl h'))
          have hxFv : x ∉ Term.fv body := by
            intro h'
            exact hx (Finset.mem_union.mpr (Or.inr h'))
          -- LC (body^[x])
          have hopen : Term.LC (Term.opening (.fvar x) body) := hbodyLC x hxL
          -- opening arg body = subst x arg (body^[x])
          rw [Term.subst_intro hxFv hArg]
          exact Term.subst_lc hArg hopen
  | appL _ huLC iht => exact Term.LC.app iht huLC
  | appR htLC _ ihu => exact Term.LC.app htLC ihu
  | @absBound bound bound' body L _ hbody iht =>
      exact Term.LC.abs L iht hbody
  | @absBody bound body body' L hbound _ ihbody =>
      -- ihbody : ∀ x, x ∉ L → Term.LC (body'^[x])
      exact Term.LC.abs L hbound ihbody

/-! ## Inversion -/

/-- Inversion for `Step (.app t u) e'`: either β fired at the top, or one of
the two arguments stepped. Used by Wave 7 type-safety. -/
theorem app_inv {t u e' : Term} (h : Step (.app t u) e') :
    (∃ bound body, t = .abs bound body ∧ e' = Term.opening u body) ∨
    (∃ t', e' = .app t' u ∧ Step t t') ∨
    (∃ u', e' = .app t u' ∧ Step u u') := by
  cases h with
  | beta hAbs _ =>
      exact Or.inl ⟨_, _, rfl, rfl⟩
  | appL hstep _ =>
      exact Or.inr (Or.inl ⟨_, rfl, hstep⟩)
  | appR _ hstep =>
      exact Or.inr (Or.inr ⟨_, rfl, hstep⟩)

end Step

/-! ## Reflexive-transitive closure -/

/-- Many-step reduction. -/
abbrev Step.Star : Term → Term → Prop := Relation.ReflTransGen Step

@[inherit_doc] infix:50 " ↦* " => Step.Star

namespace Step.Star

/-- For multi-step: either the source is locally closed, or the relation
is the reflexive empty step (in which case `t = t'`). -/
theorem lc_left {t t' : Term} (h : t ↦* t') : Term.LC t ∨ t = t' := by
  induction h with
  | refl => exact Or.inr rfl
  | tail _ hstep ih =>
      -- Whatever ih says, hstep : _ ↦ _, so its source is LC. But ih's claim
      -- is about the original t. We need LC t.
      rcases ih with hLC | heq
      · exact Or.inl hLC
      · -- ih says t = (intermediate). hstep : intermediate ↦ t'. So intermediate
        -- is LC, and t = intermediate, so t is LC.
        exact Or.inl (heq ▸ Step.lc_left hstep)

/-- For multi-step: if the source is LC, so is the target. -/
theorem lc_right {t t' : Term} (h : t ↦* t') (htLC : Term.LC t) : Term.LC t' := by
  induction h with
  | refl => exact htLC
  | tail _ hstep ih => exact Step.lc_right hstep

end Step.Star

/-! ## Evaluation contexts (optional helper)

Standard `EvalCtx` for application. We do *not* include `abs` contexts because
those would need cofinite quantification (a context is not a term). The
`Step.context` lemma below shows that filling commutes with stepping for the
simple application contexts. -/

/-- Evaluation contexts: hole, `app □ u`, `app t □`. -/
inductive EvalCtx where
  | hole : EvalCtx
  | appL : EvalCtx → Term → EvalCtx
  | appR : Term → EvalCtx → EvalCtx
  deriving Repr

/-- Plug a term into the hole. -/
def EvalCtx.fill : EvalCtx → Term → Term
  | .hole, t      => t
  | .appL E u, t  => .app (E.fill t) u
  | .appR u E, t  => .app u (E.fill t)

/-- Local-closure side condition on a context: every term mentioned in
context positions is LC. Required to lift `Step` through context filling. -/
def EvalCtx.LC : EvalCtx → Prop
  | .hole       => True
  | .appL E u   => E.LC ∧ Term.LC u
  | .appR u E   => Term.LC u ∧ E.LC

/-- Stepping commutes with filling, given the context's side terms are LC. -/
theorem Step.context {t t' : Term} {E : EvalCtx}
    (hE : E.LC) (h : Step t t') :
    Step (E.fill t) (E.fill t') := by
  induction E with
  | hole => simpa [EvalCtx.fill] using h
  | appL E u ih =>
      obtain ⟨hELC, huLC⟩ := hE
      simp [EvalCtx.fill]
      exact Step.appL (ih hELC) huLC
  | appR u E ih =>
      obtain ⟨huLC, hELC⟩ := hE
      simp [EvalCtx.fill]
      exact Step.appR huLC (ih hELC)

end Pss
