import Pss.Semantic.Model
import Pss.Semantic.ModelLemmas
import Pss.Semantic.Conversion

/-!
# Per-rule soundness: the binder rules

§6 of `pss/docs/03-revised-proof.md`, W-FUN and DS-FUN. Hypotheses match
the `Instrumented` constructors under the fundamental theorem's motives
(see `RulesEasy.lean`'s header for the motive table).

The tier bookkeeping (doc §6 W-FUN case): for `c ∈ ⟨γa⟩ⱼ`, the extended
substitution `γ[x↦c]` is `Term.scons c γ`, `SemCtx.cons` (proven,
`Model.lean`) closes the context extension, and the γ-kit equation
`subst_liftSubst_subst1` aligns `(b.subst (liftSubst γ)).subst1 c` —
the body of the substituted λ instantiated at `c` — with
`b.subst (scons c γ)` — the IH's instance. Antitonicity (`mem_antitone`,
`semCtx_antitone`) supplies premise instances at tier indices `j < k`.
-/

namespace Pss.Semantic

/-- **W-FUN** (doc §6): `Λ ⇓⁰ Λ`; at tier `j < k` with `c ∈ ⟨γt⟩ⱼ`, the
extended substitution is in `⟦Γ, x≤t⟧ⱼ` ("the new entry is literally the
tier's domain condition"), so the body's `SemWf` instance at `j` gives
(t1), and (t2) is reflexivity. Matches `WfI.fn`. -/
theorem sound_wfun {Γ : Ctx} {t u : Term} (hu : SemWf (t :: Γ) u) :
    SemWf Γ (.lam t u) := by
  sorry

/-- **DS-FUN, ≤-form** (doc §6): bound clause by `α =β γt =β γt′`; tiers
for the supertype at `j′ < k − j` take `c ∈ ⟨γt′⟩ⱼ′ = ⟨γt⟩ⱼ′`
(`good_beta_bound`), the body premise's inclusion at `j′` composes with
the member's own tier — everything at the fixed index `j′`, no
∀-escalation. Membership half via Lemma 3.3 from the left λ's wf.
Matches `SubI.fn` at `r = .le`. -/
theorem sound_fn_le {Γ : Ctx} {t t' u u' : Term}
    (h₁ : SemEq Γ t t') (h₂ : SemLe (t :: Γ) u u')
    (hw₁ : SemWf Γ (.lam t u)) (hw₂ : SemWf Γ (.lam t' u')) :
    SemLe Γ (.lam t u) (.lam t' u') := by
  sorry

/-- **DS-FUN, ≡-form** (doc §6): needs only the conversion components
and the instrumented wf of both λs. Matches `SubI.fn` at `r = .eq`. -/
theorem sound_fn_eq {Γ : Ctx} {t t' u u' : Term}
    (h₁ : SemEq Γ t t') (h₂ : SemEq (t :: Γ) u u')
    (hw₁ : SemWf Γ (.lam t u)) (hw₂ : SemWf Γ (.lam t' u')) :
    SemEq Γ (.lam t u) (.lam t' u') :=
  ⟨Beta.lam h₁.1 h₂.1, hw₁, hw₂⟩

end Pss.Semantic
