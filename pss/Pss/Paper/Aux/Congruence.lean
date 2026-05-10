import Pss.Mpss.DeBruijnTransitivityElim

/-! # `Pss.Paper.Aux.Congruence` — paper Lemmas 33, 34, 35

Mechanizes the "Congruence" lemma group from Pasquale & García-Pérez 2024
(paper p. 9:45–46):

* **Lemma 33** (Congruence of `≤`, p. 9:45) — six congruence relations
  for the diagrammatic subtyping relation `≤` and its transitive
  closure `≤*`.
* **Lemma 34** (Congruence of `↦ˢᵘᵇ`, p. 9:45–46) — three congruence
  relations for the multi-step subtype reduction `↦ˢᵘᵇ`
  (= `MSubRedStar`).
* **Lemma 35** (Congruence of `↦ᵉᵠᵘ`, p. 9:46) — three congruence
  relations for the multi-step equivalence reduction `↦ᵉᵠᵘ`
  (= `MEqRedStar`).

The paper's structure (p. 9:45) is that Lemma 33 is the "headline"
diagrammatic congruence, and its proof "lifts" Lemmas 34 and 35: each
diagrammatic step `Γ; v::s ⊢ u ≤ u'` unfolds to a common reduct via a
`MSubRedStar` chain on the left and a `MEqRedStar` chain on the right;
applying Lemma 34 to the left chain and Lemma 35 to the right chain
yields the lifted diagrammatic step at the contracted stack.

## De Bruijn translation

The paper writes the named-binder context `Γ, x ≤ t` and `Γ, x ≡ α`. In
de Bruijn there are no names; these become

* `Γ, x ≤ t` → `{ bound := t, kind := .sub } :: Γ`
* `Γ, x ≡ α` → `{ bound := α, kind := .equ } :: Γ`

The paper writes the body sub-derivation under the named extended
context. In de Bruijn the body sub-derivation must shift its stack
through the new index, hence the `Stack.shift 0 s` appearing in the
`Me-FOp`/`Ms-FOp` body premises.

The paper's `Γ, x ≤ t; nil ⊢ u ≤ u'` premise produces a binder
`λx ≤ t.u` with the **same** bound `t` on both sides. In de Bruijn this
specialises to the "fixed-bound" case (the `Ms-Fun` rule with a
reflexive bound step `MEqRed Γ [] t t`). The paper's general
`Ms-Fun` allows a non-reflexive bound step; the congruence lemma uses
the reflexive specialisation, since both sides of the conclusion show
the same `t`.

## Existing codebase counterparts (reused, not re-proved)

The single-step `MSubRedStar` lifters are already in
`Pss/Mpss/DeBruijnReductions.lean`:

* `MSubRedStar.app_fixed_arg` — Lemma 34 case 1.
* `MSubRedStar.fun_body_fixed` — Lemma 34 case 2.
* `MSubRedStar.fOp_body_fixed` — Lemma 34 case 3.

The corresponding `MEqRedStar` lifters do **not** yet exist in the
working development; the three Lemma 35 conjuncts are proved here as
new chain inductions.

The Lemma 33 conjuncts are proved by lifting the chain decomposition
of `MSub` / `MSubStar` through Lemmas 34 and 35, exactly mirroring the
paper's first-case proof on p. 9:45.
-/

namespace Pss
namespace DeBruijn
namespace Paper

namespace Congruence

/-! ## Lemma 35 chain lifters (`↦ᵉᵠᵘ` congruence)

These are the three multi-step equivalence-reduction congruence
lemmas the paper states (p. 9:46) and proves "similar to Lemma 34":
induct on the chain, applying `Me-App` / `Me-Fun` / `Me-FOp` at each
step. The single-step `MSubRedStar` analogues (`app_fixed_arg`,
`fun_body_fixed`, `fOp_body_fixed`) live in
`Pss/Mpss/DeBruijnReductions.lean`; the equivalence variants below are
the missing siblings on the `MEqRed` side.
-/

/-- Lift an operator equivalence-reduction chain under a fixed
application argument. This is the equivalence analogue of
`MSubRedStar.app_fixed_arg`.

Each `MEqRed Γ (arg :: s) u u'` step is composed with a reflexive
argument step `MEqRed Γ [] arg arg` via `Me-App`; the reflexive step is
constructed from `Term.Scoped Γ.depth arg` and `Prevalid Γ` (extracted
from the chain step). -/
theorem MEqRedStar.app_fixed_arg {Γ : Ctx} {s : Stack}
    {arg u u' : Term} (hArgScoped : Term.Scoped Γ.depth arg)
    (h : MEqRedStar Γ (arg :: s) u u') :
    MEqRedStar Γ s (.app u arg) (.app u' arg) := by
  induction h with
  | refl =>
      exact Relation.ReflTransGen.refl
  | tail hChain hStep ih =>
      have hStepWit : MEqRed Γ (arg :: s) _ _ := hStep.some
      have hpvΓ : Prevalid Γ := hStepWit.prevalid
      have hpvNil : PrevalidExt Γ [] := PrevalidExt.nil hpvΓ
      have hArgRefl : MEqRed Γ [] arg arg := MEqRed.refl hpvNil hArgScoped
      exact Relation.ReflTransGen.trans ih
        (MEqRedStar.single (MEqRed.app hStepWit hArgRefl))

/-- Lift a body equivalence-reduction chain through `Me-Fun` with the
same bound on both sides. This is the equivalence analogue of
`MSubRedStar.fun_body_fixed`.

The paper's "If `Γ, x ≤ t; nil ⊢ u ↦ᵉᵠᵘ u'` then
`Γ; nil ⊢ λx ≤ t.u ↦ᵉᵠᵘ λx ≤ t.u'`" specialises in de Bruijn to a
fixed-bound `Me-Fun` step with reflexive bound `MEqRed Γ [] t t`. -/
theorem MEqRedStar.fun_body_fixed {Γ : Ctx} {t body body' : Term}
    (_ht : Term.Scoped Γ.depth t)
    (hEqT : MEqRed Γ [] t t)
    (h : MEqRedStar ({ bound := t, kind := .sub } :: Γ) [] body body') :
    MEqRedStar Γ [] (.abs t body) (.abs t body') := by
  induction h with
  | refl =>
      exact Relation.ReflTransGen.refl
  | tail hChain hStep ih =>
      exact Relation.ReflTransGen.trans ih
        (MEqRedStar.single (MEqRed.fun_ hEqT hStep.some))

/-- Lift a body equivalence-reduction chain through `Me-FOp` with fixed
bound and fixed operand. This is the equivalence analogue of
`MSubRedStar.fOp_body_fixed`.

The paper's "If `Γ, x ≡ α; s ⊢ u ↦ᵉᵠᵘ u'` then
`Γ; α :: s ⊢ λx ≤ t.u ↦ᵉᵠᵘ λx ≤ t.u'`" specialises in de Bruijn to a
fixed-bound `Me-FOp` step with reflexive bound `MEqRed Γ [] t t`. -/
theorem MEqRedStar.fOp_body_fixed {Γ : Ctx} {s : Stack}
    {t α body body' : Term}
    (_ht : Term.Scoped Γ.depth t)
    (hα : Term.Scoped Γ.depth α)
    (hEqT : MEqRed Γ [] t t)
    (h : MEqRedStar ({ bound := α, kind := .equ } :: Γ)
      (Stack.shift 0 s) body body') :
    MEqRedStar Γ (α :: s) (.abs t body) (.abs t body') := by
  induction h with
  | refl =>
      exact Relation.ReflTransGen.refl
  | tail hChain hStep ih =>
      exact Relation.ReflTransGen.trans ih
        (MEqRedStar.single (MEqRed.fOp hEqT hα hStep.some))

end Congruence

/-! ## Paper-faithful named entry points -/

/-- **Lemma 34 (Congruence of `↦ˢᵘᵇ`), paper p. 9:45–46.**

> *Statement.* Let `Γ; s` be an extended context, and let `u`, `u'`,
> `v` and `t` be terms. We have these congruence relations:
> 1. If `Γ; v :: s ⊢ u ↦ˢᵘᵇ u'` then `Γ; s ⊢ u v ↦ˢᵘᵇ u' v`.
> 2. If `Γ, x ≤ t; nil ⊢ u ↦ˢᵘᵇ u'` then
>    `Γ; nil ⊢ λx ≤ t.u ↦ˢᵘᵇ λx ≤ t.u'`.
> 3. If `Γ, x ≡ α; s ⊢ u ↦ˢᵘᵇ u'` then
>    `Γ; α :: s ⊢ λx ≤ t.u ↦ˢᵘᵇ λx ≤ t.u'`.
>
> *Proof.* For the first case, take a `↦ˢᵘᵇ` chain
> `Γ; v :: s ⊢ u ↦ˢᵘᵇ u'`. On each `Γ; v :: s ⊢ a →ˢᵘᵇ b`
> subderivation we apply rule `Ms-App` to obtain
> `Γ; s ⊢ a v →ˢᵘᵇ b v`. By doing so on each subderivation we finally
> obtain the derivation `Γ; s ⊢ u v ↦ˢᵘᵇ u' v`, which is the desired
> result. The other cases are similar, with the use of rules `Ms-Fun`
> and `Ms-FOp` instead.

Bundled as a structure with one field per paper conjunct. The
de Bruijn translation specialises the `Ms-Fun` body cases to fixed
bound (the paper's `λx ≤ t.u ↦ˢᵘᵇ λx ≤ t.u'` shape preserves `t`),
which requires a reflexive bound step `MEqRed Γ [] t t` (constructible
from `Term.Scoped Γ.depth t` and `Prevalid Γ` via `MEqRed.refl`). -/
structure Lemma_34_Congruence_MSubRedStar
    (Γ : Ctx) (s : Stack) (t v : Term) where
  /-- Conjunct 1: argument-pop application congruence. Mechanized via
  `MSubRedStar.app_fixed_arg` from `Pss/Mpss/DeBruijnReductions.lean`. -/
  app : ∀ {u u' : Term},
    Term.Scoped Γ.depth v →
    MSubRedStar Γ (v :: s) u u' →
    MSubRedStar Γ s (.app u v) (.app u' v)
  /-- Conjunct 2: empty-stack abstraction body congruence (fixed bound).
  Mechanized via `MSubRedStar.fun_body_fixed`. -/
  fun_ : ∀ {u u' : Term},
    Term.Scoped Γ.depth t →
    MEqRed Γ [] t t →
    MSubRedStar ({ bound := t, kind := .sub } :: Γ) [] u u' →
    MSubRedStar Γ [] (.abs t u) (.abs t u')
  /-- Conjunct 3: equivalence-pop abstraction body congruence (fixed
  bound and operand). Mechanized via `MSubRedStar.fOp_body_fixed`. The
  `α` operand is the head of the `α :: s` stack at the conclusion. -/
  fOp : ∀ {u u' α : Term},
    Term.Scoped Γ.depth t →
    Term.Scoped Γ.depth α →
    MSubRedStar ({ bound := α, kind := .equ } :: Γ)
      (Stack.shift 0 s) u u' →
    MSubRedStar Γ (α :: s) (.abs t u) (.abs t u')

/-- The proved Lemma 34: each conjunct dispatches to the matching
single-step congruence lemma in `Pss/Mpss/DeBruijnReductions.lean`. -/
theorem Lemma_34_Congruence_MSubRedStar.proved (Γ : Ctx) (s : Stack)
    (t v : Term) : Lemma_34_Congruence_MSubRedStar Γ s t v where
  app hv h := MSubRedStar.app_fixed_arg hv h
  fun_ ht hEqT h := MSubRedStar.fun_body_fixed ht hEqT h
  fOp ht hα h := MSubRedStar.fOp_body_fixed ht hα h

/-- **Lemma 35 (Congruence of `↦ᵉᵠᵘ`), paper p. 9:46.**

> *Statement.* Let `Γ; s` be an extended context, and let `u`, `u'`,
> `v` and `t` be terms. We have these congruence relations:
> 1. If `Γ; v :: s ⊢ u ↦ᵉᵠᵘ u'` then `Γ; s ⊢ u v ↦ᵉᵠᵘ u' v`.
> 2. If `Γ, x ≤ t; nil ⊢ u ↦ᵉᵠᵘ u'` then
>    `Γ; nil ⊢ λx ≤ t.u ↦ᵉᵠᵘ λx ≤ t.u'`.
> 3. If `Γ, x ≡ α; s ⊢ u ↦ᵉᵠᵘ u'` then
>    `Γ; α :: s ⊢ λx ≤ t.u ↦ᵉᵠᵘ λx ≤ t.u'`.
>
> *Proof.* Similar proof as Lemma 34. -- Mechanized as: induct on the
> chain, applying `Me-App` / `Me-Fun` / `Me-FOp` at each step, mirroring
> Lemma 34's `Ms-App` / `Ms-Fun` / `Ms-FOp` dispatches.

Bundled as a structure with one field per paper conjunct. -/
structure Lemma_35_Congruence_MEqRedStar
    (Γ : Ctx) (s : Stack) (t v : Term) where
  /-- Conjunct 1: argument-pop application congruence on the equivalence
  side. Mechanized via `Congruence.MEqRedStar.app_fixed_arg`. -/
  app : ∀ {u u' : Term},
    Term.Scoped Γ.depth v →
    MEqRedStar Γ (v :: s) u u' →
    MEqRedStar Γ s (.app u v) (.app u' v)
  /-- Conjunct 2: empty-stack abstraction body congruence (fixed bound).
  Mechanized via `Congruence.MEqRedStar.fun_body_fixed`. -/
  fun_ : ∀ {u u' : Term},
    Term.Scoped Γ.depth t →
    MEqRed Γ [] t t →
    MEqRedStar ({ bound := t, kind := .sub } :: Γ) [] u u' →
    MEqRedStar Γ [] (.abs t u) (.abs t u')
  /-- Conjunct 3: equivalence-pop abstraction body congruence (fixed
  bound and operand). Mechanized via
  `Congruence.MEqRedStar.fOp_body_fixed`. -/
  fOp : ∀ {u u' α : Term},
    Term.Scoped Γ.depth t →
    Term.Scoped Γ.depth α →
    MEqRed Γ [] t t →
    MEqRedStar ({ bound := α, kind := .equ } :: Γ)
      (Stack.shift 0 s) u u' →
    MEqRedStar Γ (α :: s) (.abs t u) (.abs t u')

/-- The proved Lemma 35: each conjunct dispatches to the matching
chain-induction lemma in the `Congruence` namespace above. -/
theorem Lemma_35_Congruence_MEqRedStar.proved (Γ : Ctx) (s : Stack)
    (t v : Term) : Lemma_35_Congruence_MEqRedStar Γ s t v where
  app hv h := Congruence.MEqRedStar.app_fixed_arg hv h
  fun_ ht hEqT h := Congruence.MEqRedStar.fun_body_fixed ht hEqT h
  fOp ht hα hEqT h := Congruence.MEqRedStar.fOp_body_fixed ht hα hEqT h

/-! ## Lemma 33 — diagrammatic congruence

The paper's Lemma 33 is built by lifting Lemmas 34 and 35 through the
chain decomposition of the diagrammatic relation
`Γ; s ⊢ u ≤ v ↔ ∃ w, Γ; s ⊢ u ↦ˢᵘᵇ w ∧ Γ; s ⊢ v ↦ᵉᵠᵘ w`.

Each conjunct: from `Γ; v :: s ⊢ u ≤ u'` (or its star closure /
extended-binder analogue) extract the common reduct `w`, lift the
`MSubRedStar` chain through Lemma 34 and the `MEqRedStar` chain through
Lemma 35, then close at the lifted reduct.
-/

namespace Congruence

/-- One-step diagrammatic congruence under application with fixed
argument. The single-step variant of Lemma 33's first conjunct: open
the `MSub` witness, transport both chains through `MSubRedStar`/
`MEqRedStar` `app_fixed_arg`, and close at the lifted common reduct. -/
theorem MSub.app_fixed_arg {Γ : Ctx} {s : Stack}
    {arg u u' : Term} (hArgScoped : Term.Scoped Γ.depth arg)
    (h : MSub Γ (arg :: s) u u') :
    MSub Γ s (.app u arg) (.app u' arg) := by
  obtain ⟨w, hSub, hEqu⟩ := h
  refine ⟨.app w arg, ?_, ?_⟩
  · exact MSubRedStar.app_fixed_arg hArgScoped hSub
  · exact MEqRedStar.app_fixed_arg hArgScoped hEqu

/-- Star-closure version of `MSub.app_fixed_arg`: a transitive
diagrammatic chain on the operator at extended stack lifts to a
transitive diagrammatic chain on the application at the contracted
stack. -/
theorem MSubStar.app_fixed_arg {Γ : Ctx} {s : Stack}
    {arg u u' : Term} (hArgScoped : Term.Scoped Γ.depth arg)
    (h : MSubStar Γ (arg :: s) u u') :
    MSubStar Γ s (.app u arg) (.app u' arg) := by
  induction h with
  | refl =>
      exact Relation.ReflTransGen.refl
  | tail hChain hStep ih =>
      exact Relation.ReflTransGen.trans ih
        (Relation.ReflTransGen.single
          (MSub.app_fixed_arg hArgScoped hStep))

/-- One-step diagrammatic congruence under abstraction with fixed
bound, on an empty stack. The single-step variant of Lemma 33's third
conjunct (paper `Γ, x ≤ t; nil ⊢ u ≤ u'` ⇒ `Γ; nil ⊢ λx ≤ t.u ≤ λx ≤ t.u'`). -/
theorem MSub.fun_body_fixed {Γ : Ctx} {t u u' : Term}
    (ht : Term.Scoped Γ.depth t)
    (hEqT : MEqRed Γ [] t t)
    (h : MSub ({ bound := t, kind := .sub } :: Γ) [] u u') :
    MSub Γ [] (.abs t u) (.abs t u') := by
  obtain ⟨w, hSub, hEqu⟩ := h
  refine ⟨.abs t w, ?_, ?_⟩
  · exact MSubRedStar.fun_body_fixed ht hEqT hSub
  · exact MEqRedStar.fun_body_fixed ht hEqT hEqu

/-- Star-closure version of `MSub.fun_body_fixed`. -/
theorem MSubStar.fun_body_fixed {Γ : Ctx} {t u u' : Term}
    (ht : Term.Scoped Γ.depth t)
    (hEqT : MEqRed Γ [] t t)
    (h : MSubStar ({ bound := t, kind := .sub } :: Γ) [] u u') :
    MSubStar Γ [] (.abs t u) (.abs t u') := by
  induction h with
  | refl =>
      exact Relation.ReflTransGen.refl
  | tail hChain hStep ih =>
      exact Relation.ReflTransGen.trans ih
        (Relation.ReflTransGen.single
          (MSub.fun_body_fixed ht hEqT hStep))

/-- One-step diagrammatic congruence under abstraction with fixed bound
and operand-popped equivalence binding. The single-step variant of
Lemma 33's fifth conjunct (paper
`Γ, x ≡ α; s ⊢ u ≤ u'` ⇒ `Γ; α :: s ⊢ λx ≤ t.u ≤ λx ≤ t.u'`). -/
theorem MSub.fOp_body_fixed {Γ : Ctx} {s : Stack}
    {t α u u' : Term}
    (ht : Term.Scoped Γ.depth t)
    (hα : Term.Scoped Γ.depth α)
    (hEqT : MEqRed Γ [] t t)
    (h : MSub ({ bound := α, kind := .equ } :: Γ)
      (Stack.shift 0 s) u u') :
    MSub Γ (α :: s) (.abs t u) (.abs t u') := by
  obtain ⟨w, hSub, hEqu⟩ := h
  refine ⟨.abs t w, ?_, ?_⟩
  · exact MSubRedStar.fOp_body_fixed ht hα hSub
  · exact MEqRedStar.fOp_body_fixed ht hα hEqT hEqu

/-- Star-closure version of `MSub.fOp_body_fixed`. -/
theorem MSubStar.fOp_body_fixed {Γ : Ctx} {s : Stack}
    {t α u u' : Term}
    (ht : Term.Scoped Γ.depth t)
    (hα : Term.Scoped Γ.depth α)
    (hEqT : MEqRed Γ [] t t)
    (h : MSubStar ({ bound := α, kind := .equ } :: Γ)
      (Stack.shift 0 s) u u') :
    MSubStar Γ (α :: s) (.abs t u) (.abs t u') := by
  induction h with
  | refl =>
      exact Relation.ReflTransGen.refl
  | tail hChain hStep ih =>
      exact Relation.ReflTransGen.trans ih
        (Relation.ReflTransGen.single
          (MSub.fOp_body_fixed ht hα hEqT hStep))

end Congruence

/-- **Lemma 33 (Congruence of `≤`), paper p. 9:45.**

> *Statement.* Let `Γ; s` be an extended context, and let `u`, `u'`,
> `v`, `t` and `α` be terms. We have these six congruence relations:
> 1. If `Γ; v :: s ⊢ u ≤ u'` then `Γ; s ⊢ u v ≤ u' v`.
> 2. If `Γ; v :: s ⊢ u ≤* u'` then `Γ; s ⊢ u v ≤* u' v`.
> 3. If `Γ, x ≤ t; nil ⊢ u ≤ u'` then `Γ; nil ⊢ λx ≤ t.u ≤ λx ≤ t.u'`.
> 4. If `Γ, x ≤ t; nil ⊢ u ≤* u'` then `Γ; nil ⊢ λx ≤ t.u ≤* λx ≤ t.u'`.
> 5. If `Γ, x ≡ α; s ⊢ u ≤ u'` then `Γ; α :: s ⊢ λx ≤ t.u ≤ λx ≤ t.u'`.
> 6. If `Γ, x ≡ α; s ⊢ u ≤* u'` then `Γ; α :: s ⊢ λx ≤ t.u ≤* λx ≤ t.u'`.
>
> *Proof.* We do the first case. Every other case is similar: it lifts
> Lemmas 34 and 35.
>
> Suppose we have `Γ; v :: s ⊢ u ≤ u'`. By definition of the subtype
> relation, we have a term `t` such that `Γ; v :: s ⊢ u ↦ˢᵘᵇ t` and
> `Γ; v :: s ⊢ u' ↦ᵉᵠᵘ t`. By Lemma 35, we have `Γ; s ⊢ u' v ↦ᵉᵠᵘ t v`
> from `Γ; v :: s ⊢ u' ↦ᵉᵠᵘ t`. By Lemma 34, we have
> `Γ; s ⊢ u v ↦ˢᵘᵇ t v` from `Γ; v :: s ⊢ u ↦ˢᵘᵇ t`. We then conclude
> by definition of the subtype relation with the intermediate term
> `t v`.

Bundled as a structure with one field per paper conjunct. The
single-step conjuncts (1, 3, 5) and the star conjuncts (2, 4, 6)
share their core via the helpers in the `Congruence` namespace. -/
structure Lemma_33_Congruence_MSub
    (Γ : Ctx) (s : Stack) (t v : Term) where
  /-- Conjunct 1: `Γ; v :: s ⊢ u ≤ u' → Γ; s ⊢ u v ≤ u' v`. Mechanized
  via `Congruence.MSub.app_fixed_arg`. -/
  app : ∀ {u u' : Term},
    Term.Scoped Γ.depth v →
    MSub Γ (v :: s) u u' →
    MSub Γ s (.app u v) (.app u' v)
  /-- Conjunct 2: chain version of conjunct 1. Mechanized via
  `Congruence.MSubStar.app_fixed_arg`. -/
  app_star : ∀ {u u' : Term},
    Term.Scoped Γ.depth v →
    MSubStar Γ (v :: s) u u' →
    MSubStar Γ s (.app u v) (.app u' v)
  /-- Conjunct 3: `Γ, x ≤ t; nil ⊢ u ≤ u' → Γ; nil ⊢ λx ≤ t.u ≤ λx ≤ t.u'`.
  Mechanized via `Congruence.MSub.fun_body_fixed`. -/
  fun_ : ∀ {u u' : Term},
    Term.Scoped Γ.depth t →
    MEqRed Γ [] t t →
    MSub ({ bound := t, kind := .sub } :: Γ) [] u u' →
    MSub Γ [] (.abs t u) (.abs t u')
  /-- Conjunct 4: chain version of conjunct 3. Mechanized via
  `Congruence.MSubStar.fun_body_fixed`. -/
  fun_star : ∀ {u u' : Term},
    Term.Scoped Γ.depth t →
    MEqRed Γ [] t t →
    MSubStar ({ bound := t, kind := .sub } :: Γ) [] u u' →
    MSubStar Γ [] (.abs t u) (.abs t u')
  /-- Conjunct 5:
  `Γ, x ≡ α; s ⊢ u ≤ u' → Γ; α :: s ⊢ λx ≤ t.u ≤ λx ≤ t.u'`.
  Mechanized via `Congruence.MSub.fOp_body_fixed`. -/
  fOp : ∀ {u u' α : Term},
    Term.Scoped Γ.depth t →
    Term.Scoped Γ.depth α →
    MEqRed Γ [] t t →
    MSub ({ bound := α, kind := .equ } :: Γ)
      (Stack.shift 0 s) u u' →
    MSub Γ (α :: s) (.abs t u) (.abs t u')
  /-- Conjunct 6: chain version of conjunct 5. Mechanized via
  `Congruence.MSubStar.fOp_body_fixed`. -/
  fOp_star : ∀ {u u' α : Term},
    Term.Scoped Γ.depth t →
    Term.Scoped Γ.depth α →
    MEqRed Γ [] t t →
    MSubStar ({ bound := α, kind := .equ } :: Γ)
      (Stack.shift 0 s) u u' →
    MSubStar Γ (α :: s) (.abs t u) (.abs t u')

/-- The proved Lemma 33: each conjunct dispatches to the matching
diagrammatic congruence helper in the `Congruence` namespace, which in
turn lifts Lemmas 34 and 35 per the paper's first-case proof. -/
theorem Lemma_33_Congruence_MSub.proved (Γ : Ctx) (s : Stack)
    (t v : Term) : Lemma_33_Congruence_MSub Γ s t v where
  app hv h := Congruence.MSub.app_fixed_arg hv h
  app_star hv h := Congruence.MSubStar.app_fixed_arg hv h
  fun_ ht hEqT h := Congruence.MSub.fun_body_fixed ht hEqT h
  fun_star ht hEqT h := Congruence.MSubStar.fun_body_fixed ht hEqT h
  fOp ht hα hEqT h := Congruence.MSub.fOp_body_fixed ht hα hEqT h
  fOp_star ht hα hEqT h := Congruence.MSubStar.fOp_body_fixed ht hα hEqT h

end Paper
end DeBruijn
end Pss
