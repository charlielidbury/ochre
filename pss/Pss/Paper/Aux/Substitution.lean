import Pss.Mpss.DeBruijnTypeSafety

/-! # `Pss.Paper.Aux.Substitution` — paper Lemmas 31, 32

Mechanizes the "Reduction under substitution" lemma group from Pasquale &
García-Pérez 2024 (paper p. 9:43–9:45):

* **Lemma 31** (Reduction under substitution, p. 9:43) — substitution of
  an `α`-term for a subtype-bound variable `x ≤ t` preserves equivalence
  reduction.
* **Lemma 32** (Reduction under substitution — auxiliary for the
  commutation theorem, p. 9:44) — substitution of an equivalence-bound
  variable `x ≡ v` by `v` (LHS) and `v'` (RHS), where `v →ᵉᵠᵘ v'`,
  preserves equivalence reduction.

Both lemmas are induction on the `→ᵉᵠᵘ` derivation by last rule. Lemma 31
invokes Barendregt's substitution lemma at `Me-Bet`; Lemma 32 likewise.

## De Bruijn translation

The paper writes `Γ, x ≤ t, Γ'` (subtype annotation) and `Γ, x ≡ v, Γ'`
(equivalence annotation). In de Bruijn there are no names; the `x`
position becomes a de Bruijn index `n = Γ'.length`, and the annotation
sits as a `CtxEntry` between `Γ'` (innermost heads) and `Γ` (outermost).

The substitution operations:

* `Γ'[x\α]` becomes `Ctx.instantiateBetaPrefix α Γ'.length Γ'`
  (the prefix's bounds are substituted at the appropriate de Bruijn
  level).
* `s[x\α]` becomes `Stack.instantiate Γ'.length (Term.shiftBy 0 Γ'.length α) s`.
* `u[x\α]` becomes `Term.instantiate Γ'.length (Term.shiftBy 0 Γ'.length α) u`.

The closed-stack surface specialises to `Γ' = []` (empty prefix), which
collapses the de Bruijn level to `0` and removes the outer-shift on `α`.
That specialisation is what the existing `_Stack`-level lemmas in
`DeBruijnTypeSafety.lean` ship.

## Existing codebase counterparts

* **Lemma 31**: `BetaInstantiationPreservesMEqRedStack_proved` at
  `Pss/Mpss/DeBruijnTypeSafety.lean:1175`. Underlying type
  `BetaInstantiationPreservesMEqRedStack` at line 234. Its premise is
  `WSubMStar Γ arg bound`, exactly the de Bruijn analogue of paper's
  prevalidity-ensured `α ≤* t`.
* **Lemma 32**: `MEqRedFusedKindNarrowedBetaSubstStack_proved` at
  `Pss/Mpss/DeBruijnTypeSafety.lean:2418`. Underlying type
  `MEqRedFusedKindNarrowedBetaSubstStack` at line 1966. This is the
  "fused kind-narrowing" variant: source has `.sub`-head with bound
  `arg`, substitution arg is `arg'`, both scoped at `Γ.depth`.

## Mechanization divergences

### Lemma 31

The de Bruijn formulation discharges a `.sub`-head whose bound is `t`
(paper's subtype annotation), substituting by `α` with premise
`WSubMStar Γ α t`. Paper's prevalidity premise `Γ, Γ'[x\α]; s[x\α]
prevalid` implies in particular that `α` is well-formed and `α ≤* t`
(otherwise `Γ, Γ'[x\α]` could not be prevalid: any later context entry
mentioning the substituted-out `x` would now reference `α`, and the
well-formedness invariants of those later entries demand `α` admit the
old usages of `x`, which by reflexivity-of-≤ amounts to `α ≤* t`).

Hence the de Bruijn `WSubMStar Γ α t` premise carries the same
information as the paper's prevalidity assumption restricted to its
implications for `α`. -- Paper handwaves prevalidity-implies-α≤*t;
mechanized as: explicit `WSubMStar α t` premise.

Both lemmas are exposed in two flavours: the **Type-valued** form
(returning `MEqRed`) for callers that need constructive transport of
the derivation tree, and the **Prop-valued** form (returning `MEqRedJ`)
for callers that consume the existing wrapper API. The Type form is
declared `noncomputable def` because `MEqRed` is `Type`-valued in this
codebase (commit `ad3ff08`); the Prop form is a `theorem` whose body
existentially packages the Type form via `Nonempty`.

### Lemma 32

Paper's Lemma 32 has THREE structural features the codebase form does
not directly mirror:

1. **Head kind: `.equ` vs `.sub`.** Paper discharges `x ≡ v` (an
   equivalence annotation); the codebase form discharges
   `{bound := arg, .sub}`. The two are reconcilable because de Bruijn
   subtype reduction subsumes equivalence reduction (`Ms-Equ`):
   substituting an `.equ`-bound variable can be modelled by substituting
   a `.sub`-bound variable whose bound is itself, which is exactly what
   the codebase form does (with `arg` playing the role of `v` for the
   bound and substitution arg).

2. **Asymmetry: LHS by `v`, RHS by `v'`.** Paper substitutes the
   pre-step `v` on the LHS and the post-step `v'` on the RHS. The
   codebase form substitutes a single term `arg'` on BOTH sides — i.e.,
   it is symmetric in LHS/RHS roles. The fully asymmetric form is
   **structurally impossible to prove as a single `MEqRed` step** in
   de Bruijn: `Me-FOp`'s stack-head and body-context binder are
   syntactically the same `α`, conflicting with asymmetric LHS/RHS
   substitutions (see `Pss/Mpss/DeBruijnTypeSafety.lean:1907–1922`).
   The "fused kind-narrowing" form decouples the dropped head's bound
   (`arg`) from the substitution argument (`arg'`), which is the
   strongest single-step approximation available.

3. **Premise: `MEqRed v v'`.** Paper requires a single equivalence step
   linking `v` and `v'`. The codebase form requires only
   `Term.Scoped Γ.depth arg'` — i.e., the substitution argument is
   well-scoped, with no link to the source-bound term. This is strictly
   weaker on the premise side.

The paper's Lemma 32 is invoked twice: (i) in **Lemma 1** (`Ms-App` ×
`Me-Bet` cell, p. 9:22), and (ii) in **Lemma 2** (`Me-App` × `Me-Bet`
cell, p. 9:22). The de Bruijn working development handles both via
**chain-shaped** transport: combining
`MEqRedFusedKindNarrowedBetaSubstStack_proved` with separate diamond
closures on the body and the operand to produce a `MEqRedStar` chain
from the LHS β-target to a common reduct. The single-`MEqRed`-step
bridge across the asymmetric substitution is foreclosed by the
structural conflicts above. -- Paper Lemma 32 (asymmetric, single-step,
`.equ`-headed); mechanized as: symmetric, single-step, `.sub`-headed
(with kind-narrowing) plus chain-composition at the call sites
(see commits `7ec6954`, `8e72b12` and the `equ_bet_chain_*` family in
`DeBruijnTypeSafety.lean`).

## Imports

This file imports `Pss.Mpss.DeBruijnTypeSafety` for both `_proved`
endpoints. -/

namespace Pss
namespace DeBruijn
namespace Paper

/-! ## Lemma 31 — Reduction under substitution (paper p. 9:43) -/

/-- **Lemma 31 (Reduction under substitution), paper p. 9:43.**

> *Statement.* Let `Γ; s` be an extended context. Let `Γ'` be a logical
> context such that `Γ, Γ'[x\α]; s[x\α]` is prevalid. Let `u, v, t, α`
> be terms. Let `x` be a variable. If
> `Γ, x ≤ t, Γ'; s ⊢ u →ᵉᵠᵘ v`, then
> `Γ, Γ'[x\α]; s[x\α] ⊢ u[x\α] →ᵉᵠᵘ v[x\α]`.
>
> *Proof.* By induction on the derivation tree of
> `Γ, x ≤ t, Γ'; s ⊢ u →ᵉᵠᵘ v`. We distinguish cases on the last rule
> used.
> * `Me-Var`: `u = y` and `v = y`. If `y = x`, both `x[x\α] = α` and
>   `v[x\α] = α`; close by reflexivity (Proposition 18). If `y ≠ x`,
>   close by `Me-Var`.
> * `Me-Pro`: `u = y, v = α''` with `y ≡ α' ∈ Γ, x ≤ t, Γ'`. By
>   prevalidity of `Γ, x ≤ t, Γ'`, `y ≢ x` (else `x` would have both
>   subtype and equivalence annotations, impossible). For `y ≡ α' ∈ Γ`,
>   prevalidity of `Γ, x ≤ t, Γ'` ensures no instance of `x` in `α''`,
>   so `α''[x\α] = α''`. For `y ≡ α' ∈ Γ'`, `y ≡ α'[x\α] ∈ Γ'[x\α]` by
>   definition. Close with `Me-Pro` plus IH on the bound's reduction.
> * `Me-App`: by IH on operator and operand, reassemble with `Me-App`.
> * `Me-Top`/`Me-TAp`: trivial via `Me-Top`/`Me-TAp`.
> * `Me-Fun`/`Me-FOp`: by IH on bound and body (the body's context
>   gains another head, increasing `Γ'.length` by one); reassemble. By
>   alpha conversion `y ≠ x`.
> * `Me-Bet`: `u = (λy ≤ a.b) c, v = b'[y\c']`. By IH on body and
>   operand, then **Barendregt's substitution lemma** (Reference [5])
>   yields `b'[y\c'][x\α] = b'[x\α][y\c'[x\α]]`. Reassemble with
>   `Me-Bet`.

The de Bruijn translation collapses the named `x` to a de Bruijn level
(see file docstring); the closed-stack specialisation `Γ' = []` shipped
here uses level `0`. The paper's prevalidity premise specialises to
`WSubMStar Γ α t` (see "Mechanization divergences / Lemma 31"). -/
noncomputable def Lemma_31_ReductionUnderSubstitution
    {Γ : Ctx} {s : Stack} {t α u v : Term}
    (hAlphaBound : WSubMStar Γ α t)
    (h : MEqRed ({ bound := t, kind := .sub } :: Γ) s u v) :
    MEqRed Γ (Stack.instantiate 0 α s)
      (Term.instantiate 0 α u) (Term.instantiate 0 α v) :=
  BetaInstantiationPreservesMEqRedStack_proved hAlphaBound h

/-- Prop-wrapper variant of Lemma 31 for callers that consume `MEqRedJ`. -/
theorem Lemma_31_ReductionUnderSubstitution_J
    {Γ : Ctx} {s : Stack} {t α u v : Term}
    (hAlphaBound : WSubMStar Γ α t)
    (h : MEqRedJ ({ bound := t, kind := .sub } :: Γ) s u v) :
    MEqRedJ Γ (Stack.instantiate 0 α s)
      (Term.instantiate 0 α u) (Term.instantiate 0 α v) :=
  ⟨Lemma_31_ReductionUnderSubstitution hAlphaBound h.some⟩

/-! ## Lemma 32 — Reduction under substitution, auxiliary for the
commutation theorem (paper p. 9:44) -/

/-- **Lemma 32 (Reduction under substitution — auxiliary for the
commutation theorem), paper p. 9:44.**

> *Statement.* Let `Γ; s` be an extended context. Let `u, u', v, v'`
> be terms. Let `x` be a variable. If
> `Γ, x ≡ v, Γ'; s ⊢ u →ᵉᵠᵘ u'` and `Γ; nil ⊢ v →ᵉᵠᵘ v'`, then
> `Γ, Γ'[x\v]; s[x\v] ⊢ u[x\v] →ᵉᵠᵘ u'[x\v']`.
>
> *Proof.* By induction on the derivation tree of
> `Γ, x ≡ v, Γ'; s ⊢ u →ᵉᵠᵘ u'`. Cases `Me-Var`, `Me-Pro` (with
> sub-cases `u = y ≠ x` and `u = x`), `Me-App`, `Me-Top`, `Me-Fun`,
> `Me-FOp`, `Me-Bet`, `Me-TAp`. The `Me-Bet` case invokes Barendregt's
> substitution lemma to commute the inner β-substitution with the
> outer `[x\v]`/`[x\v']` substitutions.

**This entry is mechanized through the de Bruijn "fused kind-narrowing"
form**, which decouples the dropped head's bound from the substitution
argument. The paper's `(v, v')` pair becomes the codebase's `(arg, arg')`
pair, both scoped at `Γ.depth`. The asymmetric LHS/RHS substitution
shape of the paper is **not** preserved at the single-step level (see
"Mechanization divergences / Lemma 32" in the file docstring): the
codebase substitutes `arg'` uniformly on both sides. The paper's
asymmetry is recovered at the **chain level** via separate diamond
closures composed in the bet × bet cells of Lemmas 1 and 2.

The premises:

* `hArgScoped : Term.Scoped Γ.depth arg` — paper's `v` is well-formed
  in `Γ` (which implies scoped).
* `hArg'Scoped : Term.Scoped Γ.depth arg'` — paper's `v'` likewise (by
  scope-preservation of `MEqRed`).
* `h : MEqRed ({bound := arg, .sub} :: Γ) s lhs rhs` — paper's
  `Γ, x ≡ v, Γ'; s ⊢ u →ᵉᵠᵘ u'` translated to de Bruijn with `.sub`
  head whose bound is `arg = v` (kind-narrowed; see file docstring).

The conclusion substitutes `arg'` (= paper's `v'`) on BOTH sides:
the LHS is `lhs[arg'/0]` and RHS is `rhs[arg'/0]`. Paper would have LHS
= `u[v/0]` and RHS = `u'[v'/0]` — strictly asymmetric. The codebase's
symmetric output is what's downstream-discharged via chain composition.

-- Paper says LHS by `v`, RHS by `v'`; mechanized as: LHS and RHS both
by `arg'` (paper's `v'`), with chain-shaped composition at call sites
recovering the asymmetry. -/
noncomputable def Lemma_32_ReductionUnderSubstitution_AuxForCommutation
    {Γ : Ctx} {s : Stack} {arg arg' lhs rhs : Term}
    (hArgScoped : Term.Scoped Γ.depth arg)
    (hArg'Scoped : Term.Scoped Γ.depth arg')
    (h : MEqRed ({ bound := arg, kind := .sub } :: Γ) s lhs rhs) :
    MEqRed Γ (Stack.instantiate 0 arg' s)
      (Term.instantiate 0 arg' lhs) (Term.instantiate 0 arg' rhs) :=
  MEqRedFusedKindNarrowedBetaSubstStack_proved hArgScoped hArg'Scoped h

/-- Prop-wrapper variant of Lemma 32 for callers that consume `MEqRedJ`. -/
theorem Lemma_32_ReductionUnderSubstitution_AuxForCommutation_J
    {Γ : Ctx} {s : Stack} {arg arg' lhs rhs : Term}
    (hArgScoped : Term.Scoped Γ.depth arg)
    (hArg'Scoped : Term.Scoped Γ.depth arg')
    (h : MEqRedJ ({ bound := arg, kind := .sub } :: Γ) s lhs rhs) :
    MEqRedJ Γ (Stack.instantiate 0 arg' s)
      (Term.instantiate 0 arg' lhs) (Term.instantiate 0 arg' rhs) :=
  ⟨Lemma_32_ReductionUnderSubstitution_AuxForCommutation
    hArgScoped hArg'Scoped h.some⟩

end Paper
end DeBruijn
end Pss
