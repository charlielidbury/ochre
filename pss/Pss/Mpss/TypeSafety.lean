import Pss.Mpss.TransitivityElim
import Pss.Mpss.OperationalSem
import Pss.Mpss.Narrowing
import Mathlib.Logic.Relation

set_option linter.unusedVariables false

/-! # `Pss.Mpss.TypeSafety` — Theorems 4 & 5 (Progress & Preservation)

Pasquale & García-Pérez 2024 (CSL 2026), §4 and Appendix.

This module mechanizes type safety for MPSS. The paper states
**Conjecture 8** (well-subtyping is context-independent under
covariant contexts) as an open question, expected to be needed for
the Lemma 7 (substitution preserves well-formedness) Wf-App case.

In this formalization, Lemma 7 is discharged via the WfM/WSubM/
WSubMStar mutual recursor, with the Wf-App case handled by direct IH
on the WSubMStar premises and the WSubM-level substitution via
Lemmas 30 and 31. As a result Conjecture 8 is **not** required for
either Theorem 4 (Progress) or Theorem 5 (Preservation) — it is
retained as a paper-faithful axiom for reference but is unused in the
proof closure.

Concretely we prove:

* **Theorem 4 (Progress)** — every well-formed closed term is either a
  normal form (`Top` or an abstraction) or operationally reduces.
* **Theorem 5 (Preservation)** — operational reduction preserves
  transitive well-subtyping `≤*_wf`.

## ⚠ Retained paper axiom

`Conjecture_8_WellSubtypingContextIndependent` is retained as an
axiom in this formalization to mirror its open status in the source
paper (Pasquale & García-Pérez 2024, p. 13). It is currently unused
in the discharge of Theorems 4 and 5 here.

## Lemmas mechanized here

* **Lemma 6** (Evaluation preserves well-formedness) — by induction
  on `Step`.
* **Lemma 7** (Substitution preserves well-formedness) — by induction
  on the well-formedness derivation. Discharge does not require
  Conjecture 8: the `Wf-App` case is handled by direct IH on the
  `WSubMStar` premises, with the WSubM substitution sub-lemma using
  `Lemma 30` / `Lemma 31` from `Pss.Mpss.Substitution`.

Lemmas 15, 16 (paper appendix) — PROVED in
`Pss/Mpss/WellFormed.lean` as `Lemma_15_WEquM_symm` and
`Lemma_16_WEquM_to_WSubM`. Both are 3-case inductions on `WEquM`.

Lemma 10 (inversion) — full form (returning `WEquM Γ t t'`) is
axiomatized in `Pss/Mpss/WellFormed.lean` as `Lemma_10_Inversion`. A
restricted reduction-flavoured form is also retained as
`Lemma_10_InversionRestricted`.

## Status

* `Conjecture_8_WellSubtypingContextIndependent` — **AXIOMATIZED**
  (paper-conjecture-status). Currently UNUSED in the discharge
  closure of Theorems 4 and 5: the Lemma 7 proof here avoids it.
* `WfM.weaken_append` — **PROVED**. WF-side of paper Lemma 19/20:
  inserting a Δ-block at the top of the context preserves
  well-formedness (provided the result is prevalid). Discharged via
  the WfM/WSubM/WSubMStar mutual recursor with motive carrying
  `fv ⊆ Γ.dom` preconditions on the WSubM/WSubMStar legs (used to
  invoke MEqRed/MSubRed weakening from `Pss.Mpss.Weakening`).
* `Lemma_6_EvaluationPreservesWf` — **PROVED** (conditional on
  `Lemma_10_Inversion` and `Lemma_7_SubstitutionPreservesWf`). The
  paper's β-case (p. 27) is mechanized via Lemmas 10 + 15 + 16 + 7
  exactly as written. The four congruence cases (`appL`, `appR`,
  `absBound`, `absBody`) bypass Lemma 27 by inlining the
  Theorem-5-style preservation pattern (Prop 17 + Ws-Rgh + Ws-Trs);
  for `absBound` we use `Lemma_23_NarrowingWf` to push the body's
  WfM through the bound-annotation reduction.
* `Lemma_7_SubstitutionPreservesWf` — **PROVED**. Generalized form
  `Lemma_7_SubstitutionPreservesWf_general` discharges via the
  WfM/WSubM/WSubMStar mutual recursor: Wf-App by direct IH on the
  WSubMStar premises (sidestepping the paper's appeal to Conjecture 8
  in this case); Wf-PrS / u = x by an internal `WfM.weaken_append`
  (paper's Lemma 19/20 Wf-side, also discharged here via the mutual
  recursor); WSubM / WSubMStar cases by Lemmas 30 and 31 from
  `Pss.Mpss.Substitution`. The restricted single-binder form is
  recovered as a corollary at `Γ' = ∅`.
* `Lemma_11_TopHasNoFunctionSupertype` — **PROVED**. The proof strips
  `WSubMStar` to the diagrammatic `MSub` relation (a common
  `MSubRedStar`/`MEqRedStar` reduct exists) and applies inversions on
  the two reductions: every step out of `.top` returns `.top`, and
  every step out of an abstraction returns an abstraction.
* `Theorem_4_Progress` — **PROVED** (conditional on
  `Conjecture_8_WellSubtypingContextIndependent`).
* `Theorem_5_Preservation` — **PROVED**. With Lemma 7 now discharged
  (without using Conjecture 8), Theorem 5's axiom dependencies reduce
  to the standard Lean kernel axioms plus paper-level axioms
  `Lemma_10_Inversion`, `Proposition_17_beta_axiom`,
  `Lemma_24_NarrowingMSubRed`, and `Lemma_30_msPro_x_axiom`.
  Conjecture 8 is no longer in the dependency closure of either
  Theorem 4 or Theorem 5; we retain it as a paper-faithful axiom for
  reference but type-safety as mechanized here does not consume it.
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

The paper's Lemma 7 is used by Lemma 6 in the β-case. We discharge it
via the standard mutual-recursor pattern over `WfM` / `WSubM` /
`WSubMStar`, threading an arbitrary context prefix `Γ₂` (paper's `Γ'`)
in the partition `Γ₂ ++ ⟨x, t, .sub⟩ :: Γ₁`.

* The `Wf-App` case is handled by direct IH on the WSubMStar premises;
  the WSubM substitution sub-lemma uses Lemmas 30 and 31 (rather than
  the paper's auxiliary diagram via Conjecture 8).
* The `Wf-PrS / u = x` case uses an internal `WfM` weakening lemma
  (`WfM.weaken_append`) proved here via the WfM mutual recursor —
  this is the WF-side of paper Lemmas 19/20.
* The `WSubM` / `WSubMStar` cases use Lemmas 30 and 31 from
  `Pss.Mpss.Substitution` for the MEqRed/MSubRed reduction premises. -/

/-! ### §5.1. WfM weakening (append-on-left)

The paper's Lemma 19/20 Wf-side, instantiated for `WfM` / `WSubM` /
`WSubMStar`. We use the partitioned form so the `Wf-Fun` cofinite IH
naturally extends `Γ₁` (the inner partition) at the head.

The motives carry `fv v, fv u ⊆ (Γ₁ ++ Γ₂).dom` as preconditions for
the `WSubM` / `WSubMStar` motives. This is needed for MEqRed/MSubRed
weakening (Lemmas 22/21) which require source scope to construct the
scoped wrapper. -/

namespace Lemma7

/-- Combined weakening motive for `WfM`: a Δ-block can be inserted in
the middle of any partitioned context, provided the result is
prevalid. -/
private def _W_motive_wf : (Γ : Ctx) → (u : Term) → WfM Γ u → Prop :=
  fun Γ u _ => ∀ Γ₁ Δ Γ₂ : Ctx, Γ = Γ₁ ++ Γ₂ →
    Prevalid (Γ₁ ++ Δ ++ Γ₂) → WfM (Γ₁ ++ Δ ++ Γ₂) u

private def _W_motive_sub : (Γ : Ctx) → (v u : Term) → WSubM Γ v u → Prop :=
  fun Γ v u _ => ∀ Γ₁ Δ Γ₂ : Ctx, Γ = Γ₁ ++ Γ₂ →
    Prevalid (Γ₁ ++ Δ ++ Γ₂) →
    Term.fv v ⊆ (Γ₁ ++ Γ₂).dom →
    Term.fv u ⊆ (Γ₁ ++ Γ₂).dom →
    WSubM (Γ₁ ++ Δ ++ Γ₂) v u

private def _W_motive_star : (Γ : Ctx) → (v u : Term) → WSubMStar Γ v u → Prop :=
  fun Γ v u _ => ∀ Γ₁ Δ Γ₂ : Ctx, Γ = Γ₁ ++ Γ₂ →
    Prevalid (Γ₁ ++ Δ ++ Γ₂) →
    Term.fv v ⊆ (Γ₁ ++ Γ₂).dom →
    Term.fv u ⊆ (Γ₁ ++ Γ₂).dom →
    WSubMStar (Γ₁ ++ Δ ++ Γ₂) v u

private theorem _fv_lift_through_delta {Γ₁ Δ Γ₂ : Ctx} {u : Term}
    (h : Term.fv u ⊆ (Γ₁ ++ Γ₂).dom) :
    Term.fv u ⊆ (Γ₁ ++ Δ ++ Γ₂).dom := by
  intro z hz
  have := h hz
  simp [Ctx.dom_append] at *; tauto

private theorem _W_varSub :
    ∀ {Γ : Ctx} {y : String} {u : Term}
      (hpv : Prevalid Γ) (hb : Γ.subBinds y u),
      _W_motive_wf Γ (.fvar y) (WfM.varSub hpv hb) := by
  intro Γ y u hpv hb Γ₁ Δ Γ₂ hΓ hpv'
  subst hΓ
  exact WfM.varSub hpv' (Ctx.subBinds_insert_middle hpv' hb)

private theorem _W_varEqu :
    ∀ {Γ : Ctx} {y : String} {α : Term}
      (hpv : Prevalid Γ) (hb : Γ.equBinds y α),
      _W_motive_wf Γ (.fvar y) (WfM.varEqu hpv hb) := by
  intro Γ y α hpv hb Γ₁ Δ Γ₂ hΓ hpv'
  subst hΓ
  exact WfM.varEqu hpv' (Ctx.equBinds_insert_middle hpv' hb)

private theorem _W_top :
    ∀ {Γ : Ctx} (hpv : Prevalid Γ),
      _W_motive_wf Γ .top (WfM.top hpv) := by
  intro Γ hpv Γ₁ Δ Γ₂ hΓ hpv'
  subst hΓ
  exact WfM.top hpv'

private theorem _W_fun :
    ∀ {Γ : Ctx} {t₀ u : Term} (L : Finset String)
      (hT : WfM Γ t₀)
      (hB : ∀ y, y ∉ L → WfM (⟨y, t₀, .sub⟩ :: Γ) (Term.opening (.fvar y) u))
      (ihT : _W_motive_wf Γ t₀ hT)
      (ihB : ∀ y (hy : y ∉ L),
        _W_motive_wf (⟨y, t₀, .sub⟩ :: Γ)
          (Term.opening (.fvar y) u) (hB y hy)),
      _W_motive_wf Γ (.abs t₀ u) (WfM.fun_ L hT hB) := by
  intro Γ t₀ u L hT hB ihT ihB Γ₁ Δ Γ₂ hΓ hpv'
  subst hΓ
  have hfvT : Term.fv t₀ ⊆ (Γ₁ ++ Γ₂).dom := WfM.fv_subset hT
  have hLCT : Term.LC t₀ := WfM.lc hT
  have hfvT' : Term.fv t₀ ⊆ (Γ₁ ++ Δ ++ Γ₂).dom := _fv_lift_through_delta hfvT
  refine WfM.fun_ (L ∪ (Γ₁ ++ Δ ++ Γ₂).dom) (ihT Γ₁ Δ Γ₂ rfl hpv') ?_
  intro y hy
  have hyL : y ∉ L := fun h => hy (Finset.mem_union.mpr (Or.inl h))
  have hyD : y ∉ (Γ₁ ++ Δ ++ Γ₂).dom :=
    fun h => hy (Finset.mem_union.mpr (Or.inr h))
  have hpv_y : Prevalid (⟨y, t₀, .sub⟩ :: (Γ₁ ++ Δ ++ Γ₂)) :=
    Prevalid.sub hpv' hyD hfvT' hLCT
  have hpv_y' : Prevalid ((⟨y, t₀, .sub⟩ :: Γ₁) ++ Δ ++ Γ₂) := by
    simpa [List.cons_append] using hpv_y
  exact ihB y hyL (⟨y, t₀, .sub⟩ :: Γ₁) Δ Γ₂ (by simp) hpv_y'

private theorem _W_app :
    ∀ {Γ : Ctx} {u v t₀ : Term}
      (hStarU : WSubMStar Γ u (.abs t₀ .top))
      (hStarV : WSubMStar Γ v t₀)
      (ihU : _W_motive_star Γ u (.abs t₀ .top) hStarU)
      (ihV : _W_motive_star Γ v t₀ hStarV),
      _W_motive_wf Γ (.app u v) (WfM.app hStarU hStarV) := by
  intro Γ u v t₀ hSU hSV ihU ihV Γ₁ Δ Γ₂ hΓ hpv'
  subst hΓ
  have hfvU : Term.fv u ⊆ (Γ₁ ++ Γ₂).dom :=
    WSubMStar.fv_left_subset hSU
  have hfvAbs : Term.fv (.abs t₀ .top) ⊆ (Γ₁ ++ Γ₂).dom :=
    WSubMStar.fv_right_subset hSU
  have hfvV : Term.fv v ⊆ (Γ₁ ++ Γ₂).dom :=
    WSubMStar.fv_left_subset hSV
  have hfvT0 : Term.fv t₀ ⊆ (Γ₁ ++ Γ₂).dom :=
    WSubMStar.fv_right_subset hSV
  exact WfM.app (ihU Γ₁ Δ Γ₂ rfl hpv' hfvU hfvAbs)
                (ihV Γ₁ Δ Γ₂ rfl hpv' hfvV hfvT0)

private theorem _W_rfl :
    ∀ {Γ : Ctx} {u : Term} (hwf : WfM Γ u)
      (ihwf : _W_motive_wf Γ u hwf),
      _W_motive_sub Γ u u (WSubM.rfl hwf) := by
  intro Γ u hwf ihwf Γ₁ Δ Γ₂ hΓ hpv' _ _
  subst hΓ
  exact WSubM.rfl (ihwf Γ₁ Δ Γ₂ rfl hpv')

private theorem _W_lf1 :
    ∀ {Γ : Ctx} {v v' u : Term}
      (hred : MEqRed Γ [] v v')
      (hsub : WSubM Γ v' u)
      (ih : _W_motive_sub Γ v' u hsub),
      _W_motive_sub Γ v u (WSubM.lf1 hred hsub) := by
  intro Γ v v' u hred hsub ih Γ₁ Δ Γ₂ hΓ hpv' hfvV hfvU
  subst hΓ
  have hΓPv : Prevalid (Γ₁ ++ Γ₂) := _Prevalid_of_MEqRed hred
  have hred' : MEqRed (Γ₁ ++ Δ ++ Γ₂) [] v v' :=
    Lemma_22_WeakeningMEqRed hΓPv hfvV hpv' hred
  have hfvV' : Term.fv v' ⊆ (Γ₁ ++ Γ₂).dom := MEqRed_fv_preserve hred hfvV
  exact WSubM.lf1 hred' (ih Γ₁ Δ Γ₂ rfl hpv' hfvV' hfvU)

private theorem _W_lf2 :
    ∀ {Γ : Ctx} {v v' u : Term}
      (hwfV : WfM Γ v) (hred : MSubRed Γ [] v v')
      (hwfV' : WfM Γ v') (hsub : WSubM Γ v' u)
      (ihwfV : _W_motive_wf Γ v hwfV)
      (ihwfV' : _W_motive_wf Γ v' hwfV')
      (ih : _W_motive_sub Γ v' u hsub),
      _W_motive_sub Γ v u (WSubM.lf2 hwfV hred hwfV' hsub) := by
  intro Γ v v' u hwfV hred hwfV' hsub ihwfV ihwfV' ih Γ₁ Δ Γ₂ hΓ hpv' hfvV hfvU
  subst hΓ
  have hΓPv : Prevalid (Γ₁ ++ Γ₂) := prevalid_of_wfM hwfV
  have hred' : MSubRed (Γ₁ ++ Δ ++ Γ₂) [] v v' :=
    Lemma_21_WeakeningMSubRed hΓPv hfvV hpv' hred
  have hfvV' : Term.fv v' ⊆ (Γ₁ ++ Γ₂).dom := WfM.fv_subset hwfV'
  exact WSubM.lf2 (ihwfV Γ₁ Δ Γ₂ rfl hpv') hred'
                   (ihwfV' Γ₁ Δ Γ₂ rfl hpv')
                   (ih Γ₁ Δ Γ₂ rfl hpv' hfvV' hfvU)

private theorem _W_rgh :
    ∀ {Γ : Ctx} {v u u' : Term}
      (hsub : WSubM Γ v u') (hred : MEqRed Γ [] u u')
      (ih : _W_motive_sub Γ v u' hsub),
      _W_motive_sub Γ v u (WSubM.rgh hsub hred) := by
  intro Γ v u u' hsub hred ih Γ₁ Δ Γ₂ hΓ hpv' hfvV hfvU
  subst hΓ
  have hΓPv : Prevalid (Γ₁ ++ Γ₂) := _Prevalid_of_MEqRed hred
  have hred' : MEqRed (Γ₁ ++ Δ ++ Γ₂) [] u u' :=
    Lemma_22_WeakeningMEqRed hΓPv hfvU hpv' hred
  have hfvU' : Term.fv u' ⊆ (Γ₁ ++ Γ₂).dom := MEqRed_fv_preserve hred hfvU
  exact WSubM.rgh (ih Γ₁ Δ Γ₂ rfl hpv' hfvV hfvU') hred'

private theorem _W_sub_star :
    ∀ {Γ : Ctx} {v u : Term}
      (hwfV : WfM Γ v) (hsub : WSubM Γ v u) (hwfT : WfM Γ u)
      (ihwfV : _W_motive_wf Γ v hwfV)
      (ihsub : _W_motive_sub Γ v u hsub)
      (ihwfT : _W_motive_wf Γ u hwfT),
      _W_motive_star Γ v u
        (WSubMStar.sub hwfV hsub hwfT) := by
  intro Γ v u hwfV hsub hwfT ihwfV ihsub ihwfT Γ₁ Δ Γ₂ hΓ hpv' hfvV hfvU
  subst hΓ
  exact WSubMStar.sub (ihwfV Γ₁ Δ Γ₂ rfl hpv')
                       (ihsub Γ₁ Δ Γ₂ rfl hpv' hfvV hfvU)
                       (ihwfT Γ₁ Δ Γ₂ rfl hpv')

private theorem _W_trs_star :
    ∀ {Γ : Ctx} {v u w : Term}
      (hStar1 : WSubMStar Γ v u) (hwfU : WfM Γ u) (hStar2 : WSubMStar Γ u w)
      (ih1 : _W_motive_star Γ v u hStar1)
      (ihwfU : _W_motive_wf Γ u hwfU)
      (ih2 : _W_motive_star Γ u w hStar2),
      _W_motive_star Γ v w
        (WSubMStar.trs hStar1 hwfU hStar2) := by
  intro Γ v u w hStar1 hwfU hStar2 ih1 ihwfU ih2 Γ₁ Δ Γ₂ hΓ hpv' hfvV hfvW
  subst hΓ
  have hfvU : Term.fv u ⊆ (Γ₁ ++ Γ₂).dom := WfM.fv_subset hwfU
  exact WSubMStar.trs (ih1 Γ₁ Δ Γ₂ rfl hpv' hfvV hfvU)
                       (ihwfU Γ₁ Δ Γ₂ rfl hpv')
                       (ih2 Γ₁ Δ Γ₂ rfl hpv' hfvU hfvW)

end Lemma7

/-- WfM weakening (append-on-top form): inserting a Δ-block at the top
preserves well-formedness, provided the result is prevalid. This is the
WF-side of paper Lemma 19/20. -/
theorem WfM.weaken_append {Γ Δ : Ctx} {u : Term}
    (hwf : WfM Γ u)
    (hpv' : Prevalid (Δ ++ Γ)) :
    WfM (Δ ++ Γ) u := by
  have := WfM.rec
    (motive_1 := Lemma7._W_motive_wf)
    (motive_2 := Lemma7._W_motive_sub)
    (motive_3 := Lemma7._W_motive_star)
    @Lemma7._W_varSub @Lemma7._W_varEqu @Lemma7._W_top
    @Lemma7._W_fun @Lemma7._W_app
    @Lemma7._W_rfl @Lemma7._W_lf1 @Lemma7._W_lf2 @Lemma7._W_rgh
    @Lemma7._W_sub_star @Lemma7._W_trs_star
    hwf
  exact this [] Δ Γ rfl (by simpa using hpv')

/-! ### §5.2. Lemma 7 main statement (generalized) -/

namespace Lemma7

/-! ### Substitution motives

Combined motives for the substitution preservation lemma:
`Γ = Γ₂ ++ ⟨x, t, .sub⟩ :: Γ₁` is partitioned and `α` is supplied
once, with `WSubMStar Γ₁ α t` (giving us `WfM Γ₁ α`,
`SubstOk Γ₁ α`, etc.). -/

section
variable (Γ₁out : Ctx) (xout : String) (tout αout : Term)

private def _S_motive_wf : (Γ : Ctx) → (u : Term) → WfM Γ u → Prop :=
  fun Γ u _ => ∀ Γ₂ : Ctx,
    Γ = Γ₂ ++ ⟨xout, tout, .sub⟩ :: Γ₁out →
    WSubMStar Γ₁out αout tout →
    WfM (Ctx.subst xout αout Γ₂ ++ Γ₁out) (Term.subst xout αout u)

private def _S_motive_sub : (Γ : Ctx) → (v u : Term) → WSubM Γ v u → Prop :=
  fun Γ v u _ => ∀ Γ₂ : Ctx,
    Γ = Γ₂ ++ ⟨xout, tout, .sub⟩ :: Γ₁out →
    WSubMStar Γ₁out αout tout →
    WSubM (Ctx.subst xout αout Γ₂ ++ Γ₁out)
      (Term.subst xout αout v) (Term.subst xout αout u)

private def _S_motive_star : (Γ : Ctx) → (v u : Term) → WSubMStar Γ v u → Prop :=
  fun Γ v u _ => ∀ Γ₂ : Ctx,
    Γ = Γ₂ ++ ⟨xout, tout, .sub⟩ :: Γ₁out →
    WSubMStar Γ₁out αout tout →
    WSubMStar (Ctx.subst xout αout Γ₂ ++ Γ₁out)
      (Term.subst xout αout v) (Term.subst xout αout u)

/-- Helper: extract `SubstOk Γ₁ α` from `WSubMStar Γ₁ α t`. -/
private theorem _SubstOk_of_WSubMStar {Γ₁ : Ctx} {α t : Term}
    (hα : WSubMStar Γ₁ α t) : SubstOk Γ₁ α :=
  ⟨WSubMStar.lc_left hα, WSubMStar.fv_left_subset hα⟩

/-- Helper: derive `Prevalid (Ctx.subst x α Γ₂ ++ Γ₁)` from the
prevalidity of the original context and `WSubMStar Γ₁ α t`. -/
private theorem _Prevalid_subst_of_WSubMStar
    {Γ₁ Γ₂ : Ctx} {x : String} {t α : Term}
    (hpv : Prevalid (Γ₂ ++ ⟨x, t, .sub⟩ :: Γ₁))
    (hα : WSubMStar Γ₁ α t) :
    Prevalid (Ctx.subst x α Γ₂ ++ Γ₁) :=
  Lemma_28a_SubstPreservesPrevalid_kind hpv (_SubstOk_of_WSubMStar hα)

/-! ### §5.3. Per-case discharge -/

private theorem _S_varSub :
    ∀ {Γ : Ctx} {y : String} {u : Term}
      (hpv : Prevalid Γ) (hb : Γ.subBinds y u),
      _S_motive_wf Γ₁out xout tout αout Γ (.fvar y)
        (WfM.varSub hpv hb) := by
  intro Γ y u hpv hb Γ₂ hΓ hα
  subst hΓ
  have hpvN : Prevalid (Ctx.subst xout αout Γ₂ ++ Γ₁out) :=
    _Prevalid_subst_of_WSubMStar hpv hα
  by_cases hyx : y = xout
  · subst hyx
    rw [Term.subst_fvar_eq]
    have hwfα : WfM Γ₁out αout := wfM_left_of_wsubmstar hα
    exact WfM.weaken_append hwfα hpvN
  · rw [Term.subst_fvar_ne hyx]
    have hb' :
        (Ctx.subst xout αout Γ₂ ++ Γ₁out).subBinds y (Term.subst xout αout u) :=
      subBinds_split_neq (s := αout) hyx hpv hb
    exact WfM.varSub hpvN hb'

private theorem _S_varEqu :
    ∀ {Γ : Ctx} {y : String} {α : Term}
      (hpv : Prevalid Γ) (hb : Γ.equBinds y α),
      _S_motive_wf Γ₁out xout tout αout Γ (.fvar y)
        (WfM.varEqu hpv hb) := by
  intro Γ y α hpv hb Γ₂ hΓ hα
  subst hΓ
  have hpvN : Prevalid (Ctx.subst xout αout Γ₂ ++ Γ₁out) :=
    _Prevalid_subst_of_WSubMStar hpv hα
  have hyx : y ≠ xout := equBinds_ne_x_at_sub_head hpv hb
  rw [Term.subst_fvar_ne hyx]
  have hb' :
      (Ctx.subst xout αout Γ₂ ++ Γ₁out).equBinds y (Term.subst xout αout α) :=
    equBinds_split (s := αout) hyx hpv hb
  exact WfM.varEqu hpvN hb'

private theorem _S_top :
    ∀ {Γ : Ctx} (hpv : Prevalid Γ),
      _S_motive_wf Γ₁out xout tout αout Γ .top (WfM.top hpv) := by
  intro Γ hpv Γ₂ hΓ hα
  subst hΓ
  have hpvN : Prevalid (Ctx.subst xout αout Γ₂ ++ Γ₁out) :=
    _Prevalid_subst_of_WSubMStar hpv hα
  show WfM _ (Term.subst xout αout .top)
  simp [Term.subst]
  exact WfM.top hpvN

private theorem _S_fun :
    ∀ {Γ : Ctx} {t₀ u : Term} (L : Finset String)
      (hT : WfM Γ t₀)
      (hB : ∀ y, y ∉ L → WfM (⟨y, t₀, .sub⟩ :: Γ) (Term.opening (.fvar y) u))
      (ihT : _S_motive_wf Γ₁out xout tout αout Γ t₀ hT)
      (ihB : ∀ y (hy : y ∉ L),
        _S_motive_wf Γ₁out xout tout αout (⟨y, t₀, .sub⟩ :: Γ)
          (Term.opening (.fvar y) u) (hB y hy)),
      _S_motive_wf Γ₁out xout tout αout Γ (.abs t₀ u)
        (WfM.fun_ L hT hB) := by
  intro Γ t₀ u L hT hB ihT ihB Γ₂ hΓ hα
  subst hΓ
  show WfM _ (Term.subst xout αout (.abs t₀ u))
  simp only [Term.subst]
  refine WfM.fun_ (L ∪ {xout}) (ihT Γ₂ rfl hα) ?_
  intro y hy
  simp [Finset.mem_union, Finset.mem_singleton] at hy
  have hyL : y ∉ L := hy.1
  have hyx : y ≠ xout := hy.2
  have ih_body := ihB y hyL (⟨y, t₀, .sub⟩ :: Γ₂) (by simp) hα
  have hLCα : Term.LC αout := WSubMStar.lc_left hα
  rw [Term.subst_open_var (Ne.symm hyx) hLCα u] at ih_body
  simpa [Ctx.subst, List.cons_append] using ih_body

private theorem _S_app :
    ∀ {Γ : Ctx} {u v t₀ : Term}
      (hStarU : WSubMStar Γ u (.abs t₀ .top))
      (hStarV : WSubMStar Γ v t₀)
      (ihU : _S_motive_star Γ₁out xout tout αout Γ u (.abs t₀ .top) hStarU)
      (ihV : _S_motive_star Γ₁out xout tout αout Γ v t₀ hStarV),
      _S_motive_wf Γ₁out xout tout αout Γ (.app u v)
        (WfM.app hStarU hStarV) := by
  intro Γ u v t₀ hSU hSV ihU ihV Γ₂ hΓ hα
  subst hΓ
  show WfM _ (Term.subst xout αout (.app u v))
  simp only [Term.subst]
  have ihU' := ihU Γ₂ rfl hα
  have ihV' := ihV Γ₂ rfl hα
  simp only [Term.subst] at ihU'
  exact WfM.app ihU' ihV'

private theorem _S_rfl :
    ∀ {Γ : Ctx} {u : Term} (hwf : WfM Γ u)
      (ihwf : _S_motive_wf Γ₁out xout tout αout Γ u hwf),
      _S_motive_sub Γ₁out xout tout αout Γ u u (WSubM.rfl hwf) := by
  intro Γ u hwf ihwf Γ₂ hΓ hα
  subst hΓ
  exact WSubM.rfl (ihwf Γ₂ rfl hα)

private theorem _S_lf1 :
    ∀ {Γ : Ctx} {v v' u : Term}
      (hred : MEqRed Γ [] v v')
      (hsub : WSubM Γ v' u)
      (ih : _S_motive_sub Γ₁out xout tout αout Γ v' u hsub),
      _S_motive_sub Γ₁out xout tout αout Γ v u
        (WSubM.lf1 hred hsub) := by
  intro Γ v v' u hred hsub ih Γ₂ hΓ hα
  subst hΓ
  have hok := _SubstOk_of_WSubMStar hα
  have hred' : MEqRed (Ctx.subst xout αout Γ₂ ++ Γ₁out)
                      (Stack.subst xout αout [])
                      (Term.subst xout αout v) (Term.subst xout αout v') :=
    Lemma_31_ReductionUnderSubst_Eq hred hok
  have hred'' : MEqRed (Ctx.subst xout αout Γ₂ ++ Γ₁out) []
                       (Term.subst xout αout v) (Term.subst xout αout v') := by
    simpa using hred'
  exact WSubM.lf1 hred'' (ih Γ₂ rfl hα)

private theorem _S_lf2 :
    ∀ {Γ : Ctx} {v v' u : Term}
      (hwfV : WfM Γ v) (hred : MSubRed Γ [] v v')
      (hwfV' : WfM Γ v') (hsub : WSubM Γ v' u)
      (ihwfV : _S_motive_wf Γ₁out xout tout αout Γ v hwfV)
      (ihwfV' : _S_motive_wf Γ₁out xout tout αout Γ v' hwfV')
      (ih : _S_motive_sub Γ₁out xout tout αout Γ v' u hsub),
      _S_motive_sub Γ₁out xout tout αout Γ v u
        (WSubM.lf2 hwfV hred hwfV' hsub) := by
  intro Γ v v' u hwfV hred hwfV' hsub ihwfV ihwfV' ih Γ₂ hΓ hα
  subst hΓ
  have hok := _SubstOk_of_WSubMStar hα
  have hred' : MSubRed (Ctx.subst xout αout Γ₂ ++ Γ₁out)
                       (Stack.subst xout αout [])
                       (Term.subst xout αout v) (Term.subst xout αout v') :=
    Lemma_30_ReductionUnderSubst_Sub hred hok
  have hred'' : MSubRed (Ctx.subst xout αout Γ₂ ++ Γ₁out) []
                        (Term.subst xout αout v) (Term.subst xout αout v') := by
    simpa using hred'
  exact WSubM.lf2 (ihwfV Γ₂ rfl hα) hred''
                   (ihwfV' Γ₂ rfl hα)
                   (ih Γ₂ rfl hα)

private theorem _S_rgh :
    ∀ {Γ : Ctx} {v u u' : Term}
      (hsub : WSubM Γ v u') (hred : MEqRed Γ [] u u')
      (ih : _S_motive_sub Γ₁out xout tout αout Γ v u' hsub),
      _S_motive_sub Γ₁out xout tout αout Γ v u
        (WSubM.rgh hsub hred) := by
  intro Γ v u u' hsub hred ih Γ₂ hΓ hα
  subst hΓ
  have hok := _SubstOk_of_WSubMStar hα
  have hred' : MEqRed (Ctx.subst xout αout Γ₂ ++ Γ₁out)
                      (Stack.subst xout αout [])
                      (Term.subst xout αout u) (Term.subst xout αout u') :=
    Lemma_31_ReductionUnderSubst_Eq hred hok
  have hred'' : MEqRed (Ctx.subst xout αout Γ₂ ++ Γ₁out) []
                       (Term.subst xout αout u) (Term.subst xout αout u') := by
    simpa using hred'
  exact WSubM.rgh (ih Γ₂ rfl hα) hred''

private theorem _S_sub_star :
    ∀ {Γ : Ctx} {v u : Term}
      (hwfV : WfM Γ v) (hsub : WSubM Γ v u) (hwfT : WfM Γ u)
      (ihwfV : _S_motive_wf Γ₁out xout tout αout Γ v hwfV)
      (ihsub : _S_motive_sub Γ₁out xout tout αout Γ v u hsub)
      (ihwfT : _S_motive_wf Γ₁out xout tout αout Γ u hwfT),
      _S_motive_star Γ₁out xout tout αout Γ v u
        (WSubMStar.sub hwfV hsub hwfT) := by
  intro Γ v u hwfV hsub hwfT ihwfV ihsub ihwfT Γ₂ hΓ hα
  subst hΓ
  exact WSubMStar.sub (ihwfV Γ₂ rfl hα) (ihsub Γ₂ rfl hα)
                       (ihwfT Γ₂ rfl hα)

private theorem _S_trs_star :
    ∀ {Γ : Ctx} {v u w : Term}
      (hStar1 : WSubMStar Γ v u) (hwfU : WfM Γ u) (hStar2 : WSubMStar Γ u w)
      (ih1 : _S_motive_star Γ₁out xout tout αout Γ v u hStar1)
      (ihwfU : _S_motive_wf Γ₁out xout tout αout Γ u hwfU)
      (ih2 : _S_motive_star Γ₁out xout tout αout Γ u w hStar2),
      _S_motive_star Γ₁out xout tout αout Γ v w
        (WSubMStar.trs hStar1 hwfU hStar2) := by
  intro Γ v u w hStar1 hwfU hStar2 ih1 ihwfU ih2 Γ₂ hΓ hα
  subst hΓ
  exact WSubMStar.trs (ih1 Γ₂ rfl hα) (ihwfU Γ₂ rfl hα)
                       (ih2 Γ₂ rfl hα)

end -- section

end Lemma7

/-- **Lemma 7 (Substitution preserves well-formedness, Pasquale &
García-Pérez 2024 §4).** Generalized form: arbitrary context prefix
`Γ₂` between `Γ₁` and the head substitution binding `⟨x, t, .sub⟩`.
Mirrors the paper's `Γ, x ≤ t, Γ' ⊢ u wf  ⟹  Γ, Γ'[x\α] ⊢ u[x\α] wf`. -/
theorem Lemma_7_SubstitutionPreservesWf_general
    {Γ₁ Γ₂ : Ctx} {x : String} {t α u : Term}
    (hwfU : WfM (Γ₂ ++ ⟨x, t, .sub⟩ :: Γ₁) u)
    (hα : WSubMStar Γ₁ α t) :
    WfM (Ctx.subst x α Γ₂ ++ Γ₁) (Term.subst x α u) := by
  have := WfM.rec
    (motive_1 := Lemma7._S_motive_wf Γ₁ x t α)
    (motive_2 := Lemma7._S_motive_sub Γ₁ x t α)
    (motive_3 := Lemma7._S_motive_star Γ₁ x t α)
    (@Lemma7._S_varSub Γ₁ x t α)
    (@Lemma7._S_varEqu Γ₁ x t α)
    (@Lemma7._S_top Γ₁ x t α)
    (@Lemma7._S_fun Γ₁ x t α)
    (@Lemma7._S_app Γ₁ x t α)
    (@Lemma7._S_rfl Γ₁ x t α)
    (@Lemma7._S_lf1 Γ₁ x t α)
    (@Lemma7._S_lf2 Γ₁ x t α)
    (@Lemma7._S_rgh Γ₁ x t α)
    (@Lemma7._S_sub_star Γ₁ x t α)
    (@Lemma7._S_trs_star Γ₁ x t α)
    hwfU
  exact this Γ₂ rfl hα

/-- **Lemma 7 (Substitution preserves well-formedness).**
Restricted single-binder form: `Γ₂ = ∅` corollary of
`Lemma_7_SubstitutionPreservesWf_general`. -/
theorem Lemma_7_SubstitutionPreservesWf
    {Γ : Ctx} {x : String} {t u α : Term}
    (hwfU : WfM (⟨x, t, .sub⟩ :: Γ) u)
    (hα : WSubMStar Γ α t) :
    WfM Γ (Term.subst x α u) := by
  have := Lemma_7_SubstitutionPreservesWf_general (Γ₂ := []) (Γ₁ := Γ)
    (by simpa using hwfU) hα
  simpa [Ctx.subst] using this

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
