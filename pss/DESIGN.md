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

## MPSS mechanisation status

`PSS/MPSS.lean` contains the MPSS calculus from Pasquale & Garcia-Perez (CSL 2026).

### What's built
- MPSS syntax (terms, annotations, stacks, extended contexts)
- Equivalence reduction `MEquivRed` (8 rules)
- Subtyping reduction `MSubRed` (7 rules)  
- Context reduction `CtxRed`
- `equivRed_refl`, `ctxRed_refl` (proved)
- `ctxRed_nil_stack`, `ctxRed_nil_of_ctxRed` (proved)

### Commutativity (Lemma 1): 5/7 cases structurally complete
- MS-TOP, MS-APP+ME-APP, MS-APP+ME-TAP, MS-FUN+ME-FUN: closed
- MS-EQU, MS-PRO+ME-VAR, MS-APP+ME-BET, MS-FOP+ME-FOP: structure set up, blocked on helpers

### Diamond property (Lemma 2): 9/10 case pairs closed  
- All pairs except ME-PRO+ME-PRO closed (modulo helpers)
- ME-PRO+ME-PRO needs mutual diamond for MSubRed

### Helper lemmas: 16 sorrys total
Main blockers:
- `weakening_equivRed_ctx` — stability of ≡→ under context reduction
- `substitution_equivRed/subRed` — substitution commutes with reduction
- `equivRed_change_ann` — annotation insensitivity

### Key finding: de Bruijn friction
The paper uses named variables with freshness. Several lemma statements
are INCORRECT for de Bruijn and need reformulation:
- `weakening_equivRed` needs the annotation to be REDUCED (Γ' has t', not t)
- `equivRed_change_ann` (equiv→sub) fails when ME-PRO fires on bvar 0
- Substitution lemmas need shift/subst commutation infrastructure

This is a mechanisation challenge, not a mathematical one. The proofs are
correct on paper. Switching to locally nameless would reduce this friction.

## File index

- `PSS/Syntax.lean` — Expr, shift, subst, Ctx
- `PSS/Sub.lean` — Mutual Sub/Wf in Type (with wf-guarded trans)
- `PSS/Reduction.lean` — Small-step reduction
- `PSS/Eval.lean` — Big-step evaluator (errors on non-lambda application)
- `PSS/SyntaxLemmas.lean` — shift/subst closedness lemmas
- `PSS/CanonicalForms.lean` — top_not_sub_lam, top_not_sub_bvar (proved)
- `PSS/Soundness.lean` — step_sub (proved), 5 sorry'd theorems
- `Counterexample.lean` — Top ≤ Top→Top derivable without wf guard
- `PSS/MPSS.lean` — MPSS calculus with commutativity/diamond (16 sorrys)
