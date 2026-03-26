# Och₀ Proof Progress

Current state of the soundness and monotonicity proofs for Och₀.
Last updated: 2026-03-26.

## Theorems

**Soundness:** If `Γ ⊢ M ⇒ A` and `M ⟶ V`, then `Γ ⊢ V ⊑ A`.

**Monotonicity:** If `Γ ⊢ M ⇒ A` and `Γ' ⊑ Γ` (pointwise), then
there exists `Γ' ⊢ M ⇒ A'` with `Γ' ⊢ A' ⊑ A`.

## Status: Both Theorems Complete

All cases of both soundness and monotonicity have been proved. The
ascription sub-gap was resolved by adding S-Asc (structural congruence
for ascription). See lemma-erase-sub.md for the complete proof.

## Soundness: Case Status

| Case | Status | File | Notes |
|------|--------|------|-------|
| T-Top | Done | soundness-t-top.md | V = ⊤ = A, S-Refl |
| T-Var | Done | soundness-t-var.md | Vacuous: variables don't evaluate |
| T-Fun | Done | soundness-t-app.md | S-Fun + S-Top + Erase-Sub |
| T-Asc | Done | soundness-t-asc.md | V ⊑ M' ⊑ A' chain |
| T-App | Done | soundness-t-app.md | Abstract + concrete erasure align both sides |

## Monotonicity: Case Status

| Case | Status | File | Notes |
|------|--------|------|-------|
| T-Top | Done | monotonicity-easy.md | ⊤ ⇒ ⊤ under any env |
| T-Var | Done | monotonicity-easy.md | Γ'(x) ⊑ Γ(x) directly |
| T-Fun | Done | monotonicity-easy.md | T-Fun is env-independent |
| T-Asc | Done | monotonicity-easy.md | Raw target stable under narrowing |
| T-App | Done | monotonicity-t-app.md | HN-Mono + abstract erasure + covariant subst |

## Key Insight: Abstract Domain Erasure

The breakthrough was recognizing that T-App must erase domains in the
body before substitution — the same erasure that E-Fun does at runtime.

**The problem:** T-App substitutes the argument type N' into the raw body
B. If B contains the parameter x in domain (contravariant) positions
(e.g., `B = (y: x) → y`), a more-precise N' produces a LESS precise
result (due to contravariance). This was a concrete counterexample to
monotonicity (sharp edge #16):

```
Γ  = { a: (w: ⊤) → ⊤ }    →  R  = (y: (w: ⊤) → ⊤) → y
Γ' = { a: (w: ⊤) → w }    →  R' = (y: (w: ⊤) → w) → y
R' ⊑ R fails (domain comparison goes wrong direction)
```

**The fix:** T-App uses `erase(B)[x ≔ N']` instead of `B[x ≔ N']`.
After erasure, x only appears in covariant positions, so the ⊑ direction
is preserved. This mirrors E-Fun's deep erasure and aligns abstract
and concrete evaluation.

**Precision loss:** Domain annotations in function bodies that depend on
the parameter are lost. But this information was always erased at runtime
(E-Fun deep erasure), so the abstract side was over-promising.

## Supporting Lemmas

| Lemma | Status | File |
|-------|--------|------|
| Weakening | Done | lemma-weakening.md |
| Equal Substitution | Done | lemma-equal-substitution.md |
| Narrowing Preserves Subtyping | Done | lemma-narrowing-subtyping.md |
| S-Eval (axiom) | Done | lemma-s-eval.md |
| Values Have Erased Domains | Done | lemma-values-erased.md |
| Domain Erasure Subtyping (Erase-Sub) | Done | lemma-erase-sub.md |
| HN-Mono | Done | lemma-hn-mono.md |
| ⇓-Sub | Done | Inside lemma-hn-mono.md |
| ⇓-preserves-⊑ | Done | Inside lemma-hn-mono.md |
| Monotone Covariant Substitution | Done | Inside monotonicity-t-app.md |
| Context Well-Formedness | Done | lemma-context-wf.md |
| Substitution Preserves Scoping | Done | Inside lemma-context-wf.md |
| Erasure Preserves Scoping | Done | Inside lemma-context-wf.md |
| ⇓ Preserves Scoping | Done | Inside lemma-context-wf.md |
| Typing Output Scoping | Done | Inside lemma-context-wf.md |

## Rule Changes Made During Proof

| # | Change | Motivation | Sharp Edge |
|---|--------|------------|------------|
| 1 | S-Eval added as axiom | Can't be derived; needed for T-App soundness | -- |
| 2 | T-Asc checks raw target | Evaluated target breaks monotonicity | #10 |
| 3 | E-App evaluates body | Concrete soundness counterexample | #11 |
| 4 | T-App-Top added then removed | Was added for monotonicity fallback, removed when proofs didn't need it | #12 |
| 5 | T-App uses head normalization (⇓) | Variable types from narrowing | #12, #13 |
| 6 | Well-founded environments | ⇓ termination requires acyclic bindings | -- |
| 7 | E-Fun deep domain erasure | Inner domains break soundness | #14 |
| 8 | S-App congruence | Needed for Erase-Sub on applications | #14 |
| 9 | HN-Eval added to ⇓ | App/asc terms in narrowed envs | #15 |
| 10 | T-App abstract domain erasure | Domains in body break monotonicity | #16 |

## Visual Summary

```
Soundness:
  T-Top       ████████████ Done
  T-Var       ████████████ Done (vacuous)
  T-Fun       ████████████ Done
  T-Asc       ████████████ Done
  T-App       ████████████ Done

Monotonicity:
  T-Top       ████████████ Done
  T-Var       ████████████ Done
  T-Fun       ████████████ Done
  T-Asc       ████████████ Done
  T-App       ████████████ Done

Overall: Complete.
```

## Files Overview

| File | Content | Current? |
|------|---------|----------|
| `och.md` | Calculus definition | Yes |
| `och-examples.md` | Test suite (43 tests) | Yes |
| `och-sharp-edges.md` | Design invariants (#1-#16) | Yes |
| `proofs/soundness-t-top.md` | T-Top soundness | Yes |
| `proofs/soundness-t-var.md` | T-Var soundness | Yes |
| `proofs/soundness-t-app.md` | T-App + T-Fun soundness | Yes |
| `proofs/soundness-t-asc.md` | T-Asc soundness | Yes |
| `proofs/monotonicity-easy.md` | Easy monotonicity cases | Yes |
| `proofs/monotonicity-t-app.md` | T-App monotonicity | Yes |
| `proofs/lemma-weakening.md` | Weakening | Yes |
| `proofs/lemma-equal-substitution.md` | Equal substitution | Yes |
| `proofs/lemma-s-eval.md` | S-Eval axiom | Yes |
| `proofs/lemma-erase-sub.md` | erase(M) ⊑ M | Yes |
| `proofs/lemma-values-erased.md` | Values have ⊤ domains | Yes |
| `proofs/lemma-narrowing-subtyping.md` | Narrowing preserves subtyping | Yes |
| `proofs/lemma-hn-mono.md` | HN-Mono with sub-lemmas | Yes |
| `proofs/lemma-context-wf.md` | Context well-formedness + scoping lemmas | Yes |

## Status: Complete

All lemmas formalized. No remaining gaps or sub-gaps.

The only structural dependency to note is the mutual induction between
typing monotonicity and narrowing-preserves-subtyping (through S-Eval),
documented in lemma-narrowing-subtyping.md.
