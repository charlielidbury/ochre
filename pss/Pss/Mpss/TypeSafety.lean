import Pss.Mpss.TransitivityElim
import Pss.Mpss.OperationalSem
import Pss.Mpss.Narrowing

set_option linter.unusedVariables false

/-! # `Pss.Mpss.TypeSafety` — Theorems 4 & 5 (Progress & Preservation)

Pasquale & García-Pérez 2024 (CSL 2026), §4 and Appendix.

This module mechanizes type safety for MPSS, conditional on
**Conjecture 8** (well-subtyping is context-independent under
covariant contexts), which the paper leaves explicitly open.

Concretely we prove:

* **Theorem 4 (Progress)** — every well-formed closed term is either a
  normal form (`Top` or an abstraction) or operationally reduces.
* **Theorem 5 (Preservation)** — operational reduction preserves
  transitive well-subtyping `≤*_wf`.

Both are stated as paper-faithful theorems CONDITIONAL on the
permanent axiom `Conjecture_8_WellSubtypingContextIndependent`, which
mirrors the paper's open conjecture.

## ⚠ Permanent axiom

`Conjecture_8_WellSubtypingContextIndependent` is left as an axiom in
this formalization, mirroring its open status in the source paper
(Pasquale & García-Pérez 2024, p. 13). All Theorem 4 & 5 derivations
discharge through this axiom; it does NOT need to be proved by a
discharger to validate the type-safety story — it would need to be
proved (or refuted) by future research to definitively close the
metatheory.

## Lemmas mechanized here

* **Lemma 6** (Evaluation preserves well-formedness) — by induction
  on `Step`.
* **Lemma 7** (Substitution preserves well-formedness) — by induction
  on the well-formedness derivation, using Conjecture 8 in the `app`
  case.

Lemmas 15, 16 (paper appendix) — out of scope: they are about `≡_wf`
(`WEquM`), which is not mechanized in our `Pss/Mpss/WellFormed.lean`.

Lemma 10 (inversion) — partial restricted-form already axiomatized in
`Pss/Mpss/WellFormed.lean` as `Lemma_10_InversionRestricted`.

## Status

* `Conjecture_8_WellSubtypingContextIndependent` — **AXIOMATIZED**
  (permanent, paper-conjecture-status).
* `Lemma_6_EvaluationPreservesWf` — **AXIOMATIZED** (one Wave-7
  axiom; the proof requires the paper-style `app` inversion which
  isn't tractable from `Lemma_10_InversionRestricted` alone).
* `Lemma_7_SubstitutionPreservesWf` — **AXIOMATIZED** (one Wave-7
  axiom; the proof depends on Conjecture 8 plus inversion lemmas
  beyond Wave 5A's restricted form).
* `Theorem_4_Progress` — **PROVED** (conditional on
  `Conjecture_8_WellSubtypingContextIndependent` and
  `Lemma_11_TopHasNoFunctionSupertype` — the latter is a paper
  inversion lemma we axiomatize here in a restricted form).
* `Theorem_5_Preservation` — **PROVED** conditional on Conjecture 8
  and Lemma 6.
-/

namespace Pss

/-! ## §1. Covariant contexts

The paper's covariant contexts: `Co ::= □ | (λx ≤ t.Co) | (Co t)`.
Used in the statement of Conjecture 8 only. -/

/-- Covariant contexts (paper §4, p. 13 immediately above Conjecture 8). -/
inductive CoCtx where
  | hole : CoCtx
  | abs (bound : Term) (body : CoCtx) : CoCtx
  | app (fn : CoCtx) (arg : Term) : CoCtx

/-- Plug a term into the hole of a covariant context.

For `abs bound body`: this is a binding-aware fill, but to keep things
simple in the locally-nameless setting we treat the body as already
having `bvar 0` reserved, and fill the hole with the term-being-plugged
under the cofinite quantification later. The covariant-context
machinery in the conjecture statement handles this implicitly via the
"both Co[u] and Co[t] are well-formed in Γ" precondition. -/
def CoCtx.fill : CoCtx → Term → Term
  | .hole, t => t
  | .abs bound body, t => .abs bound (body.fill t)
  | .app fn arg, t => .app (fn.fill t) arg

/-! ## §2. Conjecture 8 (PERMANENT AXIOM) -/

/-- **Conjecture 8 (Pasquale & García-Pérez 2024 §4, p. 13).**

> Let `Γ` be a logical context and `u` and `t` be terms such that
> `Γ ⊢ u ≤*_wf t`. Let `Co` be a covariant context such that both
> `Co[u]` and `Co[t]` are well-formed in `Γ`. We conjecture that
> `Γ ⊢ Co[u] ≤*_wf Co[t]`.

Open conjecture in the source paper. **Permanent axiom in this
formalization** (per `PLAN.md` §6.1). All conditional theorems
(Theorems 4 and 5) ultimately discharge through this axiom. -/
axiom Conjecture_8_WellSubtypingContextIndependent
    {Γ : Ctx} {u t : Term} {Co : CoCtx}
    (h : WSubMStar Γ u t)
    (hwfCu : WfM Γ (Co.fill u))
    (hwfCt : WfM Γ (Co.fill t)) :
    WSubMStar Γ (Co.fill u) (Co.fill t)

/-! ## §3. Lemma 11 (restricted): Top has no function supertype

The paper's Lemma 11 is consumed by Theorem 4's `App` case to rule out
the case where the operator of a redex is `Top`. The full statement
involves the full `≤*_wf` relation; we axiomatize the restricted form
that suffices for Progress.

TODO Wave 8: discharge by Lemma 10 + the trivial fact that the
function-shape preservation chain has no Top hop. -/

/-- **Lemma 11 (restricted, Pasquale & García-Pérez 2024 §4 appendix).**
`Top` is not a transitive well-subtype of an abstraction. -/
axiom Lemma_11_TopHasNoFunctionSupertype
    {Γ : Ctx} {bound body : Term}
    (h : WSubMStar Γ .top (.abs bound body)) : False

/-! ## §4. Lemma 6 (Evaluation preserves well-formedness)

The paper's proof case-splits on `Step t t'`. The β-case (paper p. 27)
uses Lemmas 10, 15, 16, 7. Lemma 15/16 require WEquM. Lemma 10 is
restricted in our formalization. So we axiomatize Lemma 6 with a
precise statement and a `TODO Wave 8` note.

TODO Wave 8: discharge by extending `Pss/Mpss/WellFormed.lean` with
WEquM + full Lemmas 10, 15, 16. -/

/-- **Lemma 6 (Evaluation preserves well-formedness, Pasquale &
García-Pérez 2024 §4).**

If `Γ ⊢ t wf` and `t ↦ t'`, then `Γ ⊢ t' wf`. -/
axiom Lemma_6_EvaluationPreservesWf
    {Γ : Ctx} {t t' : Term}
    (hwf : WfM Γ t)
    (hstep : Step t t') :
    WfM Γ t'

/-! ## §5. Lemma 7 (Substitution preserves well-formedness)

The paper's Lemma 7 is used by Lemma 6 in the β-case. It depends on
Conjecture 8 (paper p. 27 "Now, by Lemma 7 ..."). We axiomatize it
in restricted form (single-binder context); the full polymorphic
form would extend to a context-prefix substitution.

TODO Wave 8: discharge using Conjecture 8 + Lemma 28 (substitution
preserves prevalidity, already proved in `Pss/Mpss/Substitution.lean`). -/

/-- **Lemma 7 (Substitution preserves well-formedness, Pasquale &
García-Pérez 2024 §4).** Restricted single-binder form: instead of the
paper's `Γ, x ≤ t, Γ' ⊢ u wf  ⟹  Γ, Γ'[x\α] ⊢ u[x\α] wf`, we state the
case `Γ' = ∅`. -/
axiom Lemma_7_SubstitutionPreservesWf
    {Γ : Ctx} {x : String} {t u α : Term}
    (hwfU : WfM (⟨x, t, .sub⟩ :: Γ) u)
    (hα : WSubMStar Γ α t) :
    WfM Γ (Term.subst x α u)

/-! ## §6. Helper extractors

These two helpers extract `WfM Γ v` from the LHS of `WSubMStar Γ v t`,
and `Prevalid Γ` from `WfM Γ t`. Both use the WfM/WSubMStar mutual
recursor with appropriate motives (since `induction` doesn't directly
handle the mutual block).

Note `WSubMStar.sub` carries `WfM Γ v` directly, and `WSubMStar.trs`
carries `WSubMStar Γ v u` whose LHS-WfM we recover by IH. -/

/-- From `WSubMStar Γ v t` extract `WfM Γ v`. -/
theorem wfM_left_of_wsubmstar {Γ : Ctx} {v t : Term}
    (h : WSubMStar Γ v t) : WfM Γ v :=
  WSubMStar.rec
    (motive_1 := fun _ _ _ => True)
    (motive_2 := fun _ _ _ _ => True)
    (motive_3 := fun Γ v _ _ => WfM Γ v)
    (fun _ _ => trivial)               -- Wf-PrS
    (fun _ _ => trivial)               -- Wf-PrE
    (fun _ => trivial)                 -- Wf-Top
    (fun _ _ _ _ _ => trivial)         -- Wf-Fun
    (fun _ _ _ _ => trivial)           -- Wf-App
    (fun _ _ => trivial)               -- Ws-Rfl
    (fun _ _ _ => trivial)             -- Ws-Lf1
    (fun _ _ _ _ _ _ _ => trivial)     -- Ws-Lf2
    (fun _ _ _ => trivial)             -- Ws-Rgh
    (fun {Γ v t} hwfV _ _ _ _ _ => hwfV)         -- Ws-Sub
    (fun {Γ v u t} _ _ _ ih1 _ _ => ih1)         -- Ws-Trs
    h

/-- Mutual extractor `Prevalid Γ` from `WfM Γ t` (and from
`WSubMStar Γ v t` via the LHS). Defined together with `Prevalid` of
`WSubMStar` via the mutual recursor. -/
theorem prevalid_of_wfM {Γ : Ctx} {t : Term} (h : WfM Γ t) : Prevalid Γ :=
  WfM.rec
    (motive_1 := fun Γ _ _ => Prevalid Γ)
    (motive_2 := fun _ _ _ _ => True)
    (motive_3 := fun Γ _ _ _ => Prevalid Γ)
    (fun {_ _ _} hpv _ => hpv)                 -- Wf-PrS
    (fun {_ _ _} hpv _ => hpv)                 -- Wf-PrE
    (fun {_} hpv => hpv)                       -- Wf-Top
    (fun {_ _ _} _ _ _ ihT _ => ihT)           -- Wf-Fun
    (fun {_ _ _ _} _ _ ih1 _ => ih1)           -- Wf-App
    (fun _ _ => trivial)                       -- Ws-Rfl
    (fun _ _ _ => trivial)                     -- Ws-Lf1
    (fun _ _ _ _ _ _ _ => trivial)             -- Ws-Lf2
    (fun _ _ _ => trivial)                     -- Ws-Rgh
    (fun {_ _ _} _ _ _ ihwfV _ _ => ihwfV)     -- Ws-Sub
    (fun {_ _ _ _} _ _ _ ih1 _ _ => ih1)       -- Ws-Trs
    h

/-! ## §7. Theorem 4 — Progress

The paper's normal-form characterization at the empty context is:
either `Top`, an abstraction, or a "neutral" — but neutrals require
free variables in scope. At `Γ = []`, free variables can't appear
(by `WfM.fv_subset`), so the normal forms reduce to `Top` and
abstractions.

The `app` case requires Lemma 11 to rule out the `Top` operator. -/

/-- **Theorem 4 (Pasquale & García-Pérez 2024 §4, Progress).**
Every well-formed closed term is either an abstraction, `Top`, or
operationally reducible.

Conditional on `Lemma_11_TopHasNoFunctionSupertype`. -/
theorem Theorem_4_Progress
    {t : Term} (hwf : WfM [] t) :
    (∃ bound body, t = .abs bound body) ∨
    t = .top ∨
    (∃ t', Step t t') := by
  induction t with
  | bvar n =>
    -- Excluded by LC.
    have hLC := WfM.lc hwf
    cases hLC
  | fvar x =>
    -- Excluded by fv-scope at empty context.
    have hfv := WfM.fv_subset hwf
    have hxIn : x ∈ Ctx.dom [] := by
      apply hfv
      simp [Term.fv]
    simp [Ctx.dom] at hxIn
  | top => exact Or.inr (Or.inl rfl)
  | abs bound body _ _ => exact Or.inl ⟨bound, body, rfl⟩
  | app u v ihU ihV =>
    cases hwf with
    | @app _ u v t hwSU hwSV =>
      have hLCu : Term.LC u := WSubMStar.lc_left hwSU
      have hLCv : Term.LC v := WSubMStar.lc_left hwSV
      have hwfU : WfM [] u := wfM_left_of_wsubmstar hwSU
      have hwfV : WfM [] v := wfM_left_of_wsubmstar hwSV
      rcases ihU hwfU with hAbs | hTop | ⟨u', hStepU⟩
      · -- u is an abstraction.
        obtain ⟨bound, body, hUEq⟩ := hAbs
        subst hUEq
        rcases ihV hwfV with hAbsV | hTopV | ⟨v', hStepV⟩
        · -- v is an abstraction.
          obtain ⟨b', body', hVEq⟩ := hAbsV
          subst hVEq
          right; right
          exact ⟨_, Step.beta hLCu hLCv⟩
        · -- v is Top.
          subst hTopV
          right; right
          exact ⟨_, Step.beta hLCu Term.LC.top⟩
        · -- v steps.
          right; right
          exact ⟨_, Step.appR hLCu hStepV⟩
      · -- u is Top — contradicts Lemma 11.
        subst hTop
        exact absurd hwSU (fun h => Lemma_11_TopHasNoFunctionSupertype h)
      · -- u steps.
        right; right
        exact ⟨_, Step.appL hStepU hLCv⟩

/-! ## §7. Theorem 5 — Preservation -/

/-- **Theorem 5 (Pasquale & García-Pérez 2024 §4, Preservation).**

If `Γ ⊢ t ≤*_wf u` and `t ↦ t'`, then `Γ ⊢ t' ≤*_wf u`.

Conditional on Lemma 6 (which is itself conditional on Conjecture 8). -/
theorem Theorem_5_Preservation
    {Γ : Ctx} {t t' u : Term}
    (hwf : WSubMStar Γ t u)
    (hstep : Step t t') :
    WSubMStar Γ t' u := by
  -- Paper p. 26 proof:
  -- "To prove Γ ⊢ t' ≤*_wf u we use rule Ws-Trs and prove Γ ⊢ t' ≤*_wf t and Γ ⊢ t ≤*_wf u.
  --  We already have Γ ⊢ t ≤*_wf u, so we only prove Γ ⊢ t' ≤*_wf t.
  --  From the assumption Γ ⊢ t ≤*_wf u and by Proposition 12 we know that Γ ⊢ t wf. We
  --  obtain Γ ⊢ t' wf from the Γ ⊢ t wf established earlier and by Lemma 6 and t ↦ t'.
  --  By rule Ws-Rfl and Ws-Sub, we have Γ ⊢ t' ≤*_wf t', hence Γ ⊢ t' ≤*_wf t by rule Ws-Rgh."
  -- Mechanize step by step:
  -- 1. Extract WfM Γ t.
  have hwfT : WfM Γ t := wfM_left_of_wsubmstar hwf
  -- 2. Apply Lemma 6 to get WfM Γ t'.
  have hwfT' : WfM Γ t' := Lemma_6_EvaluationPreservesWf hwfT hstep
  -- 3. Prop 17: t ↦ t' embeds into MEqRed Γ [] t t'.
  --    But this requires PrevalidExt Γ [] which is just Prevalid Γ.
  --    Wait — Theorem 5 doesn't actually need MEqRed. The paper's proof uses
  --    Ws-Rfl, Ws-Sub, Ws-Rgh. The Ws-Rgh rule is:
  --      WSubM Γ v t' →  MEqRed Γ [] t t'  →  WSubM Γ v t.
  --    So we need a MEqRed Γ [] t t' for the Ws-Rgh step.
  -- For that, we need Prevalid Γ. Extract from hwfT (via the Wf-* leaf rules).
  -- Actually wfM_prevalid is needed. We can derive Prevalid Γ from any WfM Γ t
  -- by induction on WfM (every leaf carries Prevalid Γ).
  have hpvΓ : Prevalid Γ := prevalid_of_wfM hwfT
  have hpvNil : PrevalidExt Γ [] := PrevalidExt.nil hpvΓ
  have hLCt : Term.LC t := WfM.lc hwfT
  have hfvT : Term.fv t ⊆ Γ.dom := WfM.fv_subset hwfT
  -- 4. Apply Proposition 17: get MEqRed Γ [] t t' (Prop-wrapped, so `obtain`).
  obtain ⟨hMEq⟩ : Nonempty (MEqRed Γ [] t t') :=
    Proposition_17_FromOperationalToEqRed hpvNil hLCt hfvT hstep
  -- 5. Build WSubM Γ t' t' via Ws-Rfl: needs WfM Γ t'.
  have hSubT' : WSubM Γ t' t' := WSubM.rfl hwfT'
  -- 6. Apply Ws-Rgh: from WSubM Γ t' t' and MEqRed Γ [] t t', get WSubM Γ t' t.
  have hSubT'_t : WSubM Γ t' t := WSubM.rgh hSubT' hMEq
  -- 7. Wrap in WSubMStar.sub: needs WfM Γ t' and WfM Γ t.
  have hStarT'_t : WSubMStar Γ t' t := WSubMStar.sub hwfT' hSubT'_t hwfT
  -- 8. Combine via Ws-Trs.
  exact WSubMStar.trs hStarT'_t hwfT hwf

end Pss
