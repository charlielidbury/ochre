# PSS Type Safety — Design Document

## Status

We attempted to prove type safety for Hutchins' PSS (POPL 2010) in Lean.
Here is what we found.

## What's proved (zero sorry)

- **Canonical forms** (`CanonicalForms.lean`): `Top ≤ λs.t → False` and `Top ≤ bvar k → False`
  with the wf-guarded transitivity rule. Height-based strong induction with a helper
  for the `.app` middle-term case.

- **step_sub** (`Soundness.lean`): Small-step reduction implies bidirectional subtyping.
  Doesn't use trans at all.

- **concEval_closedAt** (`Soundness.lean`): Big-step evaluation preserves closedness.

## What's blocked

The **inversion lemma** (Lemma 5.2): if `(λa.b) ≤ (λs.t)` then `a ≡ s`.

The `trans` case with `.app` middle term can't be closed by height-based induction:
composing derivations via `trans` doesn't decrease any simple measure. This is the
exact obstacle identified by Hutchins (2010, §6.6.3) and confirmed by Pasquale &
Garcia-Perez (2024).

## The fundamental issue

Hutchins' algorithmic system allows "premature promotion": a variable `x` can be
promoted to its bound `t` BEFORE the enclosing lambda receives its argument. This
breaks the commutativity diagram:

```
(λx ≤ t.x) v  ──≡→──  v
      ≤↑                ?↓
(λx ≤ t.t) v  ──≡→──  v
```

The bottom-left reduces AND promotes, but the top-right edge can't be completed in
a single step.

## The MPSS solution (Pasquale & Garcia-Perez, CSL 2026)

Machine-Based PSS (MPSS) reformulates the algorithmic system with a **continuation
stack** (à la Krivine Abstract Machine). Instead of reducing `(λx≤t.u) v` directly,
MPSS pushes `v` onto the stack and processes the lambda body. Variable promotion
uses the stack operand instead of the context bound, preventing premature promotion.

MPSS proves:
- **Lemma 1**: `≤→` and `≡→` strongly commute (by structural induction on terms)
- **Lemma 2**: `≡→` has the diamond property
- **Theorem 3**: Transitivity is admissible

But full type safety (Theorems 4 & 5) depends on **Conjecture 8**: well-subtyping
is context-independent. This remains open.

## Paths forward

### Path A: Mechanise MPSS commutativity
Mechanise MPSS in Lean and prove Lemma 1 (commutativity). This would be the first
formal verification of this result. The proof is by structural induction on terms
and is fully detailed in the paper's appendix.

### Path B: Prove Conjecture 8
Close the remaining gap in MPSS type safety. Would complete the full result.

### Path C: Logical relations for PSS
Define a step-indexed semantic model and prove the fundamental theorem directly,
bypassing transitivity elimination entirely. In a semantic model, transitivity is
free (set inclusion is transitive). The challenge: defining V_k(τ) when τ is an
arbitrary (potentially non-terminating) term.

### Path D: Direct proof for PSS via different induction
Find a measure that DOES decrease when composing through `.app` middle terms. The
MPSS paper suggests this is impossible for Hutchins' system, but a creative encoding
(e.g., multi-dimensional induction, ordinals) might work.

## Key insight from the counterexample

We proved that removing the wf guard from `trans` makes the relation unsound:
`Top ≤ Top→Top` is derivable (see `Counterexample.lean`). The derivation chains
through an ill-formed β-redex `(λf:(Top→Top). f)(Top)` where `Top` is not a subtype
of `Top→Top`. The wf guard blocks this because the ill-formed app can't be well-formed
without first proving `Top ≤ Top→Top` — the very thing being derived.

## File index

- `PSS/Syntax.lean` — Expr, shift, subst, Ctx
- `PSS/Sub.lean` — Mutual Sub/Wf in Type (with wf-guarded trans)
- `PSS/Reduction.lean` — Small-step reduction
- `PSS/Eval.lean` — Big-step evaluator (errors on non-lambda application)
- `PSS/SyntaxLemmas.lean` — shift/subst closedness lemmas
- `PSS/CanonicalForms.lean` — top_not_sub_lam, top_not_sub_bvar (proved)
- `PSS/Soundness.lean` — step_sub (proved), 5 sorry'd theorems
- `Counterexample.lean` — Top ≤ Top→Top derivable without wf guard
