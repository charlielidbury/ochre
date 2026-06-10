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
  intro k γ hγ
  -- `(.lam t u).subst γ = .lam (γt) (u[⇑γ])` definitionally.
  show Mem k (.lam (t.subst γ) (u.subst (Term.liftSubst γ)))
      (.lam (t.subst γ) (u.subst (Term.liftSubst γ)))
  rw [Mem_unfold]
  intro j v hj hconv
  -- `Λ` is a value, hence whnf: the only convergence is `Λ ⇓⁰ Λ`.
  have hval : Term.Value (Term.lam (t.subst γ) (u.subst (Term.liftSubst γ))) :=
    .lam _ _
  have hself : Converges 0 (.lam (t.subst γ) (u.subst (Term.liftSubst γ)))
      (.lam (t.subst γ) (u.subst (Term.liftSubst γ))) :=
    ⟨.refl, whNormal_of_value hval⟩
  obtain ⟨hjeq, hveq⟩ := Converges.deterministic hconv hself
  subst hjeq hveq
  refine ⟨hval, _, ⟨0, hself⟩, hval, ?_⟩
  -- (m3) `Match (k − 0) Λ Λ`, lam disjunct; bound clause is `Beta.refl`.
  rw [Match_unfold]
  refine .inr ⟨t.subst γ, u.subst (Term.liftSubst γ), t.subst γ,
    u.subst (Term.liftSubst γ), rfl, rfl, Beta.refl _, ?_⟩
  intro j' c hj' hgood
  have hj'k : j' < k := by omega
  -- `γ[x↦c] ∈ ⟦Γ, x≤t⟧ⱼ′`: ambient components by antitonicity, the new
  -- entry is literally the tier's domain condition (doc §6 W-FUN).
  have hctx : SemCtx j' (t :: Γ) (Term.scons c γ) :=
    SemCtx.cons (semCtx_antitone (Nat.le_of_lt hj'k) hγ) hgood
  -- (t1) is the body's `SemWf` at `(j', γ[x↦c])` modulo the γ-kit
  -- equation `(u[⇑γ])[x↦c] = u[γ[x↦c]]`; (t2) is reflexivity.
  have hmem := hu j' (Term.scons c γ) hctx
  rw [← subst_liftSubst_subst1] at hmem
  exact ⟨hmem, fun _ hs => hs⟩

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
  -- Lemma 3.3: the membership half follows from the inclusion half.
  refine semLe_of_inclusion hw₁ ?_
  intro k γ hγ s hs
  -- The bound conversion under γ, used for both the bound clause and
  -- the goodness transport: `γt =β γt′` from `h₁`'s `t =β t′`.
  have hβt : Beta (t.subst γ) (t'.subst γ) := Beta.subst γ h₁.1
  have hs' : Mem k s (.lam (t.subst γ) (u.subst (Term.liftSubst γ))) := hs
  show Mem k s (.lam (t'.subst γ) (u'.subst (Term.liftSubst γ)))
  rw [Mem_unfold] at hs' ⊢
  intro j v hj hconv
  obtain ⟨hv, w, hw, _, hmatch⟩ := hs' j v hj hconv
  -- `Λ` is a value, so the member's (m2) witness is `Λ` itself.
  have hΛval : Term.Value (Term.lam (t.subst γ) (u.subst (Term.liftSubst γ))) :=
    .lam _ _
  obtain ⟨jw, hjw⟩ := hw
  obtain ⟨-, hweq⟩ := Converges.deterministic hjw
    ⟨.refl, whNormal_of_value hΛval⟩
  subst hweq
  -- (m2) for `Λ′`: a value, `Λ′ ⇓⁰ Λ′`.
  have hΛ'val : Term.Value (Term.lam (t'.subst γ) (u'.subst (Term.liftSubst γ))) :=
    .lam _ _
  refine ⟨hv, _, ⟨0, .refl, whNormal_of_value hΛ'val⟩, hΛ'val, ?_⟩
  -- (m3): transport the member's match across the rule's conversions.
  rw [Match_unfold] at hmatch ⊢
  rcases hmatch with htop | ⟨a, b, α, β, hΛeq, hveq, hbound, htier⟩
  · exact Term.noConfusion htop
  injection hΛeq with ha hb
  subst ha hb
  -- Bound clause: `α =β γt =β γt′`.
  refine .inr ⟨t'.subst γ, u'.subst (Term.liftSubst γ), α, β, rfl, hveq,
    Beta.trans hbound hβt, ?_⟩
  intro j' c hj' hgood'
  -- Goodness transports back across the bound conversion (Lemma 4.4):
  -- `⟨γt′⟩ⱼ′ = ⟨γt⟩ⱼ′`.
  have hgood : Good j' (t.subst γ) c := (good_beta_bound hβt).mpr hgood'
  obtain ⟨ht1, ht2⟩ := htier j' c hj' hgood
  -- The body premise's inclusion at the fixed index `j′` (note the
  -- context extension uses the unprimed bound `t`).
  have hj'k : j' < k := by omega
  have hctx : SemCtx j' (t :: Γ) (Term.scons c γ) :=
    SemCtx.cons (semCtx_antitone (Nat.le_of_lt hj'k) hγ) hgood
  have hincl := (h₂ j' (Term.scons c γ) hctx).2
  -- Align `(·[⇑γ])[x↦c]` with `·[γ[x↦c]]` and compose the member's
  -- tier through the inclusion — everything at `j′`, no ∀-escalation.
  rw [subst_liftSubst_subst1] at ht1 ht2 ⊢
  exact ⟨hincl _ ht1, fun s'' hs'' => hincl _ (ht2 s'' hs'')⟩

/-- **DS-FUN, ≡-form** (doc §6): needs only the conversion components
and the instrumented wf of both λs. Matches `SubI.fn` at `r = .eq`. -/
theorem sound_fn_eq {Γ : Ctx} {t t' u u' : Term}
    (h₁ : SemEq Γ t t') (h₂ : SemEq (t :: Γ) u u')
    (hw₁ : SemWf Γ (.lam t u)) (hw₂ : SemWf Γ (.lam t' u')) :
    SemEq Γ (.lam t u) (.lam t' u') :=
  ⟨Beta.lam h₁.1 h₂.1, hw₁, hw₂⟩

end Pss.Semantic
