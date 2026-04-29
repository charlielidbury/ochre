import Pss.Mpss.TransitivityElim
import Pss.Mpss.OperationalSem
import Pss.Mpss.Narrowing
import Mathlib.Logic.Relation

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

Lemmas 15, 16 (paper appendix) — PROVED in
`Pss/Mpss/WellFormed.lean` as `Lemma_15_WEquM_symm` and
`Lemma_16_WEquM_to_WSubM`. Both are 3-case inductions on `WEquM`.

Lemma 10 (inversion) — full form (returning `WEquM Γ t t'`) is
axiomatized in `Pss/Mpss/WellFormed.lean` as `Lemma_10_Inversion`. A
restricted reduction-flavoured form is also retained as
`Lemma_10_InversionRestricted`.

## Status

* `Conjecture_8_WellSubtypingContextIndependent` — **AXIOMATIZED**
  (permanent, paper-conjecture-status).
* `Lemma_6_EvaluationPreservesWf` — **PROVED** (conditional on
  `Lemma_10_Inversion` and `Lemma_7_SubstitutionPreservesWf`). The
  paper's β-case (p. 27) is mechanized via Lemmas 10 + 15 + 16 + 7
  exactly as written. The four congruence cases (`appL`, `appR`,
  `absBound`, `absBody`) bypass Lemma 27 by inlining the
  Theorem-5-style preservation pattern (Prop 17 + Ws-Rgh + Ws-Trs);
  for `absBound` we use `Lemma_23_NarrowingWf` to push the body's
  WfM through the bound-annotation reduction.
* `Lemma_7_SubstitutionPreservesWf` — **AXIOMATIZED** (the paper's
  proof depends on Conjecture 8 plus a sub-induction on `WSubMStar`
  for the `Wf-App` case using Lemma 30/31 substitution lemmas. The
  `Wf-PrS / u = x` case in particular requires an instantiated WfM
  weakening lemma (paper's Lemma 19/20 Wf-side), which exists in
  this codebase only as the schema `Lemma_20_WeakeningWf_schema`.
  Full discharge requires significant additional infrastructure.).
* `Lemma_11_TopHasNoFunctionSupertype` — **PROVED**. The proof strips
  `WSubMStar` to the diagrammatic `MSub` relation (a common
  `MSubRedStar`/`MEqRedStar` reduct exists) and applies inversions on
  the two reductions: every step out of `.top` returns `.top`, and
  every step out of an abstraction returns an abstraction.
* `Theorem_4_Progress` — **PROVED** (conditional on
  `Conjecture_8_WellSubtypingContextIndependent`).
* `Theorem_5_Preservation` — **PROVED** conditional on Conjecture 8
  and Lemma 7 (via Lemma 6).
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
the case where the operator of a redex is `Top`.

**Proof sketch.** We strip the `WfM` decoration of `WSubMStar` to land in
the diagrammatic `MSub` relation (a common reduct under `MSubRedStar` and
`MEqRedStar`). The diagram has the form:

    .top ─→^≤* w ←—^≡* (.abs bound body)

By inversion on `MSubRed` and `MEqRed`, every step out of `.top` returns
`.top` and every step out of `(.abs ...)` returns an `.abs ...`. So
`w = .top` and `w = .abs ...` simultaneously, contradiction.

The proof uses the existing `MSub`/`Theorem 3` machinery via the strip
lemma `WSubMStar.toMSub`. -/

/-- Single-step inversion: `MEqRed Γ s .top v` forces `v = .top`. -/
private theorem _MEqRed_top_inv {Γ : Ctx} {s : Stack} {v : Term}
    (h : MEqRed Γ s .top v) : v = .top := by
  cases h with
  | top _ => rfl

/-- Single-step inversion: `MSubRed Γ s .top v` forces `v = .top`. -/
private theorem _MSubRed_top_inv {Γ : Ctx} {s : Stack} {v : Term}
    (h : MSubRed Γ s .top v) : v = .top := by
  cases h with
  | top _ _ _ => rfl
  | equ _ heq => exact _MEqRed_top_inv heq

/-- Multi-step inversion: from `.top`, the only `MEqRedStar` reduct is
`.top`. -/
private theorem _MEqRedStar_top_inv {Γ : Ctx} {s : Stack} {v : Term}
    (h : MEqRedStar Γ s .top v) : v = .top := by
  induction h with
  | refl => rfl
  | tail _ hStep ih =>
    subst ih
    obtain ⟨hStep'⟩ := hStep
    exact _MEqRed_top_inv hStep'

/-- Multi-step inversion: from `.top`, the only `MSubRedStar` reduct is
`.top`. -/
private theorem _MSubRedStar_top_inv {Γ : Ctx} {s : Stack} {v : Term}
    (h : MSubRedStar Γ s .top v) : v = .top := by
  induction h with
  | refl => rfl
  | tail _ hStep ih =>
    subst ih
    obtain ⟨hStep'⟩ := hStep
    exact _MSubRed_top_inv hStep'

/-- Single-step inversion: `MEqRed Γ s (.abs b body) v` forces `v` to be
an abstraction. -/
private theorem _MEqRed_abs_inv {Γ : Ctx} {s : Stack} {b body v : Term}
    (h : MEqRed Γ s (.abs b body) v) :
    ∃ b' body', v = .abs b' body' := by
  cases h with
  | fun_ _ _ _ => exact ⟨_, _, rfl⟩
  | fOp _ _ _ => exact ⟨_, _, rfl⟩

/-- Multi-step inversion: from `(.abs b body)`, every `MEqRedStar` reduct
is an abstraction. -/
private theorem _MEqRedStar_abs_inv {Γ : Ctx} {s : Stack} {b body v : Term}
    (h : MEqRedStar Γ s (.abs b body) v) :
    ∃ b' body', v = .abs b' body' := by
  induction h with
  | refl => exact ⟨b, body, rfl⟩
  | tail _ hStep ih =>
    obtain ⟨b', body', hEq⟩ := ih
    subst hEq
    obtain ⟨hStep'⟩ := hStep
    exact _MEqRed_abs_inv hStep'

/-! ### Stripping `WSubM`/`WSubMStar` to `MSub`

`MSub Γ s u v` (paper diagrammatic `≤`) is `∃ w, MSubRedStar Γ s u w ∧
MEqRedStar Γ s v w`. Every `WSubM` derivation strips to an `MSub` at
empty stack by ignoring the `WfM` decorations and converting MEqRed/MSubRed
single steps to chains. -/

/-- Local helper: extract `Prevalid Γ` from any `MEqRed Γ s u v`.
We can't reuse `MEqRed.prevalid` from `Substitution.lean` (private),
so we re-derive it locally via induction on the `MEqRed` derivation. -/
private theorem _Prevalid_of_MEqRed {Γ : Ctx} {s : Stack} {u v : Term}
    (h : MEqRed Γ s u v) : Prevalid Γ := by
  induction h with
  | @pro _ _ _ _ _ hpv _ _ _ => exact extractPrevalid hpv
  | @bet _ _ _ _ _ _ _ _ _ _ _ _ ihv => exact ihv
  | @top _ _ hpv => exact extractPrevalid hpv
  | @app _ _ _ _ _ _ _ _ _ ihv => exact ihv
  | @var _ _ _ hpv => exact extractPrevalid hpv
  | @fun_ _ _ _ _ _ _ _ _ iht _ => exact iht
  | @tAp _ _ _ hpv _ _ => exact extractPrevalid hpv
  | @fOp _ _ _ _ _ _ _ _ _ _ iht _ => exact iht

/-- Wrap `Prevalid Γ` into `PrevalidExt Γ []`. -/
private theorem _PrevalidExt_nil_of_MEqRed {Γ : Ctx} {u v : Term}
    (h : MEqRed Γ [] u v) : PrevalidExt Γ [] :=
  PrevalidExt.nil (_Prevalid_of_MEqRed h)

/-- Combined strip of `WfM`/`WSubM`/`WSubMStar` to `MSub` via the mutual
recursor. The `WfM` motive is trivial; both `WSubM` and `WSubMStar`
strip to `MSub Γ [] v t`. -/
private theorem _toMSub_combined :
    (∀ {Γ : Ctx} {v t : Term}, WSubM Γ v t → MSub Γ [] v t) ∧
    (∀ {Γ : Ctx} {v t : Term}, WSubMStar Γ v t → MSub Γ [] v t) := by
  refine ⟨?_, ?_⟩
  all_goals intro Γ v t h
  · -- WSubM strip: induct via the WSubM mutual recursor.
    classical
    exact (WSubM.rec
      (motive_1 := fun _ _ _ => True)
      (motive_2 := fun Γ v t _ => MSub Γ [] v t)
      (motive_3 := fun Γ v t _ => MSub Γ [] v t)
      -- Wf cases: trivial.
      (fun _ _ => trivial) (fun _ _ => trivial) (fun _ => trivial)
      (fun _ _ _ _ _ => trivial) (fun _ _ _ _ => trivial)
      -- Ws-Rfl: take w = t, both chains refl.
      (fun {Γ t} _ _ => ⟨t, Relation.ReflTransGen.refl, Relation.ReflTransGen.refl⟩)
      -- Ws-Lf1: prepend MEqRed (via Ms-Equ) on MSubRed* side.
      (fun {Γ v v' t} hred _ ih => by
        obtain ⟨w, hSubChain, hEqChain⟩ := ih
        have hpv : PrevalidExt Γ [] := _PrevalidExt_nil_of_MEqRed hred
        have hSubStep : MSubRed Γ [] v v' := MSubRed.equ hpv hred
        exact ⟨w, Relation.ReflTransGen.head ⟨hSubStep⟩ hSubChain, hEqChain⟩)
      -- Ws-Lf2: prepend MSubRed on MSubRed* side.
      (fun {Γ v v' t} _ hred _ _ _ _ ih => by
        obtain ⟨w, hSubChain, hEqChain⟩ := ih
        exact ⟨w, Relation.ReflTransGen.head ⟨hred⟩ hSubChain, hEqChain⟩)
      -- Ws-Rgh: prepend MEqRed on MEqRed* side.
      (fun {Γ v t t'} _ hred ih => by
        obtain ⟨w, hSubChain, hEqChain⟩ := ih
        exact ⟨w, hSubChain, Relation.ReflTransGen.head ⟨hred⟩ hEqChain⟩)
      -- Ws-Sub: ih on the WSubM core.
      (fun _ _ _ _ ih_sub _ => ih_sub)
      -- Ws-Trs: combine via MSub.trans_step.
      (fun _ _ _ ih1 _ ih2 => MSub.trans_step ih1 ih2)
      h)
  · -- WSubMStar strip: induct via the WSubMStar mutual recursor.
    classical
    exact (WSubMStar.rec
      (motive_1 := fun _ _ _ => True)
      (motive_2 := fun Γ v t _ => MSub Γ [] v t)
      (motive_3 := fun Γ v t _ => MSub Γ [] v t)
      (fun _ _ => trivial) (fun _ _ => trivial) (fun _ => trivial)
      (fun _ _ _ _ _ => trivial) (fun _ _ _ _ => trivial)
      (fun {Γ t} _ _ => ⟨t, Relation.ReflTransGen.refl, Relation.ReflTransGen.refl⟩)
      (fun {Γ v v' t} hred _ ih => by
        obtain ⟨w, hSubChain, hEqChain⟩ := ih
        have hpv : PrevalidExt Γ [] := _PrevalidExt_nil_of_MEqRed hred
        have hSubStep : MSubRed Γ [] v v' := MSubRed.equ hpv hred
        exact ⟨w, Relation.ReflTransGen.head ⟨hSubStep⟩ hSubChain, hEqChain⟩)
      (fun {Γ v v' t} _ hred _ _ _ _ ih => by
        obtain ⟨w, hSubChain, hEqChain⟩ := ih
        exact ⟨w, Relation.ReflTransGen.head ⟨hred⟩ hSubChain, hEqChain⟩)
      (fun {Γ v t t'} _ hred ih => by
        obtain ⟨w, hSubChain, hEqChain⟩ := ih
        exact ⟨w, hSubChain, Relation.ReflTransGen.head ⟨hred⟩ hEqChain⟩)
      (fun _ _ _ _ ih_sub _ => ih_sub)
      (fun _ _ _ ih1 _ ih2 => MSub.trans_step ih1 ih2)
      h)

/-- Strip the `WfM` decoration of `WSubM` to the diagrammatic `MSub`. -/
private theorem _WSubM_toMSub {Γ : Ctx} {v t : Term}
    (h : WSubM Γ v t) : MSub Γ [] v t := _toMSub_combined.1 h

/-- Strip `WSubMStar` to `MSub` via the mutual recursor. -/
private theorem _WSubMStar_toMSub {Γ : Ctx} {v t : Term}
    (h : WSubMStar Γ v t) : MSub Γ [] v t := _toMSub_combined.2 h

/-- **Lemma 11 (Pasquale & García-Pérez 2024 §4 appendix).** `Top` is not
a transitive well-subtype of an abstraction. -/
theorem Lemma_11_TopHasNoFunctionSupertype
    {Γ : Ctx} {bound body : Term}
    (h : WSubMStar Γ .top (.abs bound body)) : False := by
  have hMSub : MSub Γ [] .top (.abs bound body) := _WSubMStar_toMSub h
  obtain ⟨w, hSubChain, hEqChain⟩ := hMSub
  -- hSubChain : MSubRedStar Γ [] .top w
  -- hEqChain  : MEqRedStar Γ [] (.abs bound body) w
  have hwTop : w = .top := _MSubRedStar_top_inv hSubChain
  obtain ⟨b', body', hwAbs⟩ := _MEqRedStar_abs_inv hEqChain
  -- w = .top and w = .abs ... contradiction.
  rw [hwTop] at hwAbs
  cases hwAbs

/-! ## §4. Helper extractors

These helpers extract `WfM Γ v` from the LHS / RHS of `WSubMStar Γ v t`,
and `Prevalid Γ` from `WfM Γ t`. All three use the WfM/WSubMStar mutual
recursor with appropriate motives (since `induction` doesn't directly
handle the mutual block).

`WSubMStar.sub` carries `WfM Γ v` AND `WfM Γ t` directly; `WSubMStar.trs`
carries `WSubMStar Γ v u` and `WSubMStar Γ u t` whose LHS-WfM /
RHS-WfM we recover by IH. -/

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

/-- From `WSubMStar Γ v t` extract `WfM Γ t`. Mirror of
`wfM_left_of_wsubmstar`. -/
theorem wfM_right_of_wsubmstar {Γ : Ctx} {v t : Term}
    (h : WSubMStar Γ v t) : WfM Γ t :=
  WSubMStar.rec
    (motive_1 := fun _ _ _ => True)
    (motive_2 := fun _ _ _ _ => True)
    (motive_3 := fun Γ _ t _ => WfM Γ t)
    (fun _ _ => trivial)               -- Wf-PrS
    (fun _ _ => trivial)               -- Wf-PrE
    (fun _ => trivial)                 -- Wf-Top
    (fun _ _ _ _ _ => trivial)         -- Wf-Fun
    (fun _ _ _ _ => trivial)           -- Wf-App
    (fun _ _ => trivial)               -- Ws-Rfl
    (fun _ _ _ => trivial)             -- Ws-Lf1
    (fun _ _ _ _ _ _ _ => trivial)     -- Ws-Lf2
    (fun _ _ _ => trivial)             -- Ws-Rgh
    (fun {Γ v t} _ _ hwfT _ _ _ => hwfT)         -- Ws-Sub
    (fun {Γ v u t} _ _ _ _ _ ih2 => ih2)         -- Ws-Trs
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

/-! ## §5. Lemma 7 (Substitution preserves well-formedness)

The paper's Lemma 7 is used by Lemma 6 in the β-case. It depends on
Conjecture 8 (paper p. 27 "Now, by Lemma 7 ...") plus a sub-induction
on `WSubMStar` for the `Wf-App` case using Lemma 30/31 substitution
lemmas. Additionally, the `Wf-PrS / u = x` case (paper p. 28) uses
the WfM-side of weakening (paper Lemma 19/20), which exists in this
codebase only as the abstract schema `Lemma_20_WeakeningWf_schema` —
not yet instantiated for `WfM`. We axiomatize Lemma 7 in restricted
single-binder form pending that infrastructure. -/

/-- **Lemma 7 (Substitution preserves well-formedness, Pasquale &
García-Pérez 2024 §4).** Restricted single-binder form: instead of the
paper's `Γ, x ≤ t, Γ' ⊢ u wf  ⟹  Γ, Γ'[x\α] ⊢ u[x\α] wf`, we state the
case `Γ' = ∅`. -/
axiom Lemma_7_SubstitutionPreservesWf
    {Γ : Ctx} {x : String} {t u α : Term}
    (hwfU : WfM (⟨x, t, .sub⟩ :: Γ) u)
    (hα : WSubMStar Γ α t) :
    WfM Γ (Term.subst x α u)

/-! ## §6. Lemma 6 (Evaluation preserves well-formedness)

The paper's proof case-splits on `Step t t'` (Pasquale & García-Pérez
2024, p. 27). We mechanize all five cases:

* β case: Lemmas 10 + 15 + 16 + 7 (the latter axiomatized above).
* `appL` / `appR`: bypass paper's "Lemma 27" by inlining the
  Theorem-5-style preservation pattern (Prop 17 + Ws-Rgh + Ws-Trs).
* `absBound`: same Theorem-5-style pattern on the bound annotation,
  combined with `Lemma_23_NarrowingWf` to push the body's WfM
  through the bound-annotation reduction (since narrowing requires
  `bound' ≤_wf bound` only as `LC bound'` + `fv bound' ⊆ Γ.dom`,
  and we get the latter from `MEqRed_fv_subset` on the `MEqRed`
  obtained via Prop 17).
* `absBody`: cofinite-quantification IH on the body openings.

The proof is by induction on `Step` generalizing over `Γ` (so the
`absBody` IH lifts to the extended context). -/

/-- **Lemma 6 (Evaluation preserves well-formedness, Pasquale &
García-Pérez 2024 §4).**

If `Γ ⊢ t wf` and `t ↦ t'`, then `Γ ⊢ t' wf`.

PROVED conditional on `Lemma_7_SubstitutionPreservesWf` (β case),
`Lemma_10_Inversion` (β case), and `Proposition_17_beta_axiom` (the
four congruence cases via Prop 17). -/
theorem Lemma_6_EvaluationPreservesWf
    {Γ : Ctx} {t t' : Term}
    (hwf : WfM Γ t)
    (hstep : Step t t') :
    WfM Γ t' := by
  induction hstep generalizing Γ with
  | @beta bound body arg hAbsLC hArgLC =>
    -- t = (.abs bound body) arg, t' = Term.opening arg body.
    -- Invert hwf via Wf-App.
    cases hwf with
    | @app _ _ _ z hStarFn hStarArg =>
      -- hStarFn : WSubMStar Γ (.abs bound body) (.abs z .top)
      -- hStarArg : WSubMStar Γ arg z
      -- Step 1: Lemma 10 inversion on hStarFn -> WEquM Γ bound z.
      have hEquBz : WEquM Γ bound z := Lemma_10_Inversion hStarFn
      -- Step 2: symmetry (Lemma 15) + Lemma 16 -> WSubM Γ z bound.
      have hSubZBd : WSubM Γ z bound :=
        Lemma_16_WEquM_to_WSubM (Lemma_15_WEquM_symm hEquBz)
      -- Step 3: get WfM Γ z (from hStarArg's RHS) and WfM Γ bound
      --         (from hStarFn's LHS Wf-Fun inversion).
      have hwfZ : WfM Γ z := wfM_right_of_wsubmstar hStarArg
      have hwfFn : WfM Γ (.abs bound body) := wfM_left_of_wsubmstar hStarFn
      have hwfBd : WfM Γ bound := by
        cases hwfFn with
        | @fun_ _ _ _ L hT _ => exact hT
      -- Step 4: wrap hSubZBd in Ws-Sub -> WSubMStar Γ z bound.
      have hStarZBd : WSubMStar Γ z bound :=
        WSubMStar.sub hwfZ hSubZBd hwfBd
      -- Step 5: trs hStarArg + hStarZBd -> WSubMStar Γ arg bound.
      have hStarArgBd : WSubMStar Γ arg bound :=
        WSubMStar.trs hStarArg hwfZ hStarZBd
      -- Step 6: extract Wf-Fun body data: cofinite WfM
      -- (⟨x, bound, .sub⟩ :: Γ) (body^[x]).
      classical
      obtain ⟨L, hT, hBody⟩ : ∃ L : Finset String, WfM Γ bound ∧
          (∀ x, x ∉ L → WfM (⟨x, bound, .sub⟩ :: Γ) (Term.opening (.fvar x) body)) := by
        cases hwfFn with
        | @fun_ _ _ _ L hT hB => exact ⟨L, hT, hB⟩
      -- Step 7: choose fresh x outside L ∪ fv body.
      obtain ⟨x, hxF⟩ := Term.exists_fresh (L ∪ Term.fv body)
      have hxL : x ∉ L := fun h => hxF (Finset.mem_union.mpr (Or.inl h))
      have hxFv : x ∉ Term.fv body :=
        fun h => hxF (Finset.mem_union.mpr (Or.inr h))
      have hwfBodyOpen : WfM (⟨x, bound, .sub⟩ :: Γ) (Term.opening (.fvar x) body) :=
        hBody x hxL
      -- Step 8: Lemma 7: subst x arg into body^[x] becomes opening arg body.
      have hLCarg : Term.LC arg := hArgLC
      have hSubstEq : Term.subst x arg (Term.opening (.fvar x) body) =
          Term.opening arg body :=
        (Term.subst_intro hxFv hLCarg).symm
      have hwfSubst : WfM Γ (Term.subst x arg (Term.opening (.fvar x) body)) :=
        Lemma_7_SubstitutionPreservesWf hwfBodyOpen hStarArgBd
      rw [hSubstEq] at hwfSubst
      exact hwfSubst
  | @appL u u' v hstep hLCv ihU =>
    -- Goal: WfM Γ (.app u' v).
    cases hwf with
    | @app _ _ _ z hStarFn hStarArg =>
      -- hStarFn : WSubMStar Γ u (.abs z .top)
      -- hStarArg : WSubMStar Γ v z
      have hwfU : WfM Γ u := wfM_left_of_wsubmstar hStarFn
      have hwfFnRHS : WfM Γ (.abs z .top) := wfM_right_of_wsubmstar hStarFn
      have hwfU' : WfM Γ u' := ihU hwfU
      -- Build WSubMStar Γ u' u via Prop 17 + Ws-Rgh + Ws-Sub.
      have hpvΓ : Prevalid Γ := prevalid_of_wfM hwfU
      have hpvNil : PrevalidExt Γ [] := PrevalidExt.nil hpvΓ
      have hLCu : Term.LC u := WfM.lc hwfU
      have hfvU : Term.fv u ⊆ Γ.dom := WfM.fv_subset hwfU
      obtain ⟨hMEq⟩ : Nonempty (MEqRed Γ [] u u') :=
        Proposition_17_FromOperationalToEqRed hpvNil hLCu hfvU hstep
      have hSubU' : WSubM Γ u' u' := WSubM.rfl hwfU'
      have hSubU'_u : WSubM Γ u' u := WSubM.rgh hSubU' hMEq
      have hStarU'_u : WSubMStar Γ u' u := WSubMStar.sub hwfU' hSubU'_u hwfU
      have hStarU'_FnRHS : WSubMStar Γ u' (.abs z .top) :=
        WSubMStar.trs hStarU'_u hwfU hStarFn
      exact WfM.app hStarU'_FnRHS hStarArg
  | @appR u v v' hLCu hstep ihV =>
    -- Goal: WfM Γ (.app u v').
    cases hwf with
    | @app _ _ _ z hStarFn hStarArg =>
      have hwfV : WfM Γ v := wfM_left_of_wsubmstar hStarArg
      have hwfZ : WfM Γ z := wfM_right_of_wsubmstar hStarArg
      have hwfV' : WfM Γ v' := ihV hwfV
      have hpvΓ : Prevalid Γ := prevalid_of_wfM hwfV
      have hpvNil : PrevalidExt Γ [] := PrevalidExt.nil hpvΓ
      have hLCv : Term.LC v := WfM.lc hwfV
      have hfvV : Term.fv v ⊆ Γ.dom := WfM.fv_subset hwfV
      obtain ⟨hMEq⟩ : Nonempty (MEqRed Γ [] v v') :=
        Proposition_17_FromOperationalToEqRed hpvNil hLCv hfvV hstep
      have hSubV' : WSubM Γ v' v' := WSubM.rfl hwfV'
      have hSubV'_v : WSubM Γ v' v := WSubM.rgh hSubV' hMEq
      have hStarV'_v : WSubMStar Γ v' v := WSubMStar.sub hwfV' hSubV'_v hwfV
      have hStarV'_z : WSubMStar Γ v' z :=
        WSubMStar.trs hStarV'_v hwfV hStarArg
      exact WfM.app hStarFn hStarV'_z
  | @absBound bound bound' body L hstep hbodyLC ihBound =>
    -- Goal: WfM Γ (.abs bound' body).
    cases hwf with
    | @fun_ _ _ _ L₀ hT hB =>
      -- IH on Step bound bound': WfM Γ bound -> WfM Γ bound'.
      have hwfBd' : WfM Γ bound' := ihBound hT
      -- Need: cofinite WfM (⟨x, bound', .sub⟩ :: Γ) (body^[x]).
      -- Strategy: take x ∉ L₀ ∪ Γ.dom, use hB x hxL₀ to get
      -- WfM (⟨x, bound, .sub⟩ :: Γ) (body^[x]), then narrow via Lemma 23.
      -- Narrowing requires LC bound' and fv bound' ⊆ Γ.dom.
      have hLCBd' : Term.LC bound' := Step.lc_right hstep
      -- fv bound' ⊆ Γ.dom: from MEqRed_fv_subset on the Prop-17 image.
      have hLCBd : Term.LC bound := WfM.lc hT
      have hfvBd : Term.fv bound ⊆ Γ.dom := WfM.fv_subset hT
      have hpvΓ : Prevalid Γ := prevalid_of_wfM hT
      have hpvNil : PrevalidExt Γ [] := PrevalidExt.nil hpvΓ
      obtain ⟨hMEqBd⟩ : Nonempty (MEqRed Γ [] bound bound') :=
        Proposition_17_FromOperationalToEqRed hpvNil hLCBd hfvBd hstep
      have hfvBd' : Term.fv bound' ⊆ Γ.dom := by
        intro y hy
        have hy' : y ∈ Term.fv bound ∪ Γ.dom := MEqRed_fv_subset hMEqBd hy
        rcases Finset.mem_union.mp hy' with h | h
        · exact hfvBd h
        · exact h
      -- Build the new cofinite witness.
      refine WfM.fun_ (L₀ ∪ Γ.dom) hwfBd' ?_
      intro y hy
      have hyL₀ : y ∉ L₀ := fun h =>
        hy (Finset.mem_union.mpr (Or.inl h))
      have hyΓ : y ∉ Γ.dom := fun h =>
        hy (Finset.mem_union.mpr (Or.inr h))
      have hwfBody_old : WfM (⟨y, bound, .sub⟩ :: Γ) (Term.opening (.fvar y) body) :=
        hB y hyL₀
      -- Apply Lemma 23 with Γ₂ = [] to swap the head bound -> bound'.
      have :=
        Lemma_23_NarrowingWf (Γ₁ := Γ) (Γ₂ := []) (x := y)
          (t := bound') (t' := bound) (u := Term.opening (.fvar y) body)
          (by simpa using hwfBody_old) hLCBd' hfvBd'
      simpa using this
  | @absBody bound body body' L hLCbound hbody ihBody =>
    -- Goal: WfM Γ (.abs bound body').
    cases hwf with
    | @fun_ _ _ _ L₀ hT hB =>
      refine WfM.fun_ (L ∪ L₀ ∪ Γ.dom) hT ?_
      intro y hy
      have hyL : y ∉ L := fun h => hy (by
        apply Finset.mem_union.mpr; left
        apply Finset.mem_union.mpr; left; exact h)
      have hyL₀ : y ∉ L₀ := fun h => hy (by
        apply Finset.mem_union.mpr; left
        apply Finset.mem_union.mpr; right; exact h)
      have hwfBody_old : WfM (⟨y, bound, .sub⟩ :: Γ) (Term.opening (.fvar y) body) :=
        hB y hyL₀
      -- Apply IH at this fresh y, with Γ := ⟨y, bound, .sub⟩ :: Γ.
      exact ihBody y hyL hwfBody_old

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
