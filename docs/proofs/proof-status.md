# Och₀ Proof Status

Status of the soundness and monotonicity proofs as of the current rules
in `docs/och.md`.

## Theorem Statements

**Soundness:** If `Γ ⊢ M ⇒ A` and `M ⟶ V`, then `Γ ⊢ V ⊑ A`.

**Monotonicity:** If `Γ ⊢ M ⇒ A` and `Γ' ⊑ Γ` (pointwise), then
there exists a derivation `Γ' ⊢ M ⇒ A'` with `Γ' ⊢ A' ⊑ A`.

(With unconditional T-App-Top, the typing judgment is non-deterministic.
Soundness holds for every derivation. Monotonicity says: for every
derivation under Γ, there exists a derivation under Γ' with a
more-precise-or-equal result.)

## Case-by-Case Status

### Soundness

| Case | Status | File | Notes |
|------|--------|------|-------|
| T-Top | ✓ Complete | soundness-t-top.md | V = ⊤, A = ⊤, S-Refl |
| T-Var | ✓ Complete | soundness-t-var.md | Vacuous (variables don't evaluate) |
| T-Fun | ✓ Complete | soundness-t-fun.md | E-Fun erases domain; S-Fun + S-Top |
| T-App-Top | ✓ Complete | (trivial) | V ⊑ ⊤ by S-Top |
| T-Asc | ✓ Complete | soundness-t-asc.md | V ⊑ M' ⊑ A ⊑ A' chain |
| T-App | **GAP** | soundness-t-app.md | See Gap 1 below |

### Monotonicity

| Case | Status | File | Notes |
|------|--------|------|-------|
| T-Top | ✓ Complete | monotonicity-easy.md | ⊤ ⇒ ⊤ in both; S-Refl |
| T-Var | ✓ Complete | monotonicity-easy.md | Γ'(x) ⊑ Γ(x) directly |
| T-Fun | ✓ Complete | monotonicity-easy.md | T-Fun is environment-independent |
| T-App-Top | ✓ Complete | (trivial) | Use T-App-Top under Γ'; ⊤ ⊑ ⊤ |
| T-Asc | ✓ Complete | monotonicity-easy.md | Raw target stable; IH on sub-derivations |
| T-App | **GAP** | monotonicity-t-app.md | See Gaps 1 and 2 below |

## Remaining Gaps

### Gap 1: Monotone Substitution (affects both soundness and monotonicity)

**Location:** T-App, function-literal case of the body B.

**The problem:** When B = `(y: P) → Q` (function literal in the body),
the soundness proof needs:

```
V = (y: ⊤) → Q[x ≔ N_v]     (concrete: E-Fun erases domain)
R = (y: P[x ≔ N']) → Q[x ≔ N']   (abstract: T-Fun preserves domain)

V ⊑ R by S-Fun requires:
  1. P[x ≔ N'] ⊑ ⊤              — trivial (S-Top) ✓
  2. y: P[x ≔ N'] ⊢ Q[x ≔ N_v] ⊑ Q[x ≔ N']   — GAP (★)
```

Premise (2) is "monotone substitution": substituting a more-precise
value (N_v ⊑ N') into Q yields a more-precise result. This fails when
Q contains x in a **contravariant position** (as a domain annotation
of an inner function).

Example: Q = `(z: x) → z`. Then:
- Q[x ≔ N_v] = `(z: N_v) → z`
- Q[x ≔ N'] = `(z: N') → z`
- S-Fun requires N' ⊑ N_v (contra) — **wrong direction**

The same gap appears in the monotonicity proof as obligation (★):
`R₀[x ≔ N''] ⊑ R₀[x ≔ N']` where N'' ⊑ N'.

**Root cause:** T-Fun preserves domain annotations while E-Fun erases
them. Abstract evaluation maintains precise domains for type-checking,
but this creates a mismatch with concrete evaluation where domains
are always ⊤.

**Why no counterexample exists:** The gap only arises inside unevaluated
function bodies. Any attempt to OBSERVE the value (by applying it)
triggers further evaluation, which erases the inner domains via E-Fun.
The mismatch is syntactic — it never manifests as a semantic unsoundness.

**Proposed resolutions:**

1. **Logical relations / realizability.** Instead of proving `V ⊑ R`
   syntactically, define soundness via a logical relation that interprets
   types as sets of values. Function types are interpreted as "maps
   A-values to B[x≔v]-values" — domain annotations are irrelevant for
   value semantics. This sidesteps syntactic contravariance entirely.
   **This is the recommended path.**

2. **Polarity-aware substitution.** Define a polarity analysis for terms
   and prove monotone substitution only for terms where x appears
   covariantly. Then show that the gap case (x in a domain) is
   semantically harmless. Complex but stays within the syntactic proof.

3. **Accept the gap.** Document it as a known proof-technique limitation
   and argue informally that it cannot produce a counterexample. The
   gap is in the same category as "the map is not the territory" —
   syntactic subtyping is too coarse to express the actual invariant.

### Gap 2: Variable-Type Gap — RESOLVED by head normalization

**Location:** T-App, when M₁'s type under Γ' is a variable.

**The problem (now fixed):** Under Γ, `M₁ ⇒ (x: A) → B` (a function
type), so T-App fires. Under Γ' ⊑ Γ, `M₁ ⇒ g` (a variable alias
for a function type). Old T-App required a syntactic function type,
so it didn't fire.

**The fix:** T-App now uses head normalization (⇓). The premise
`Γ ⊢ F ⇓ (x: A) → B` unfolds variable aliases: if F = g and
Γ(g) = (x: ⊤) → x, then g ⇓ (x: ⊤) → x and T-App fires.

**Rejected alternative: T-Var normalization.** Changing T-Var to
evaluate environment entries (`x ⇒ eval(Γ(x))`) breaks test 28
(`x: T ⊢ (x : T) ⇒ ⊤`) because T-Asc's raw target check needs
`eval(x) ⊑ T`, and `⊤ ⊑ T` is not derivable. See sharp edge #13.

**Remaining proof obligation:** The head normalization monotonicity
lemma (HN-Mono): if `F' ⊑ F` and `F ⇓ (x: A) → B`, then
`F' ⇓ (x: C) → D` with `(x: C) → D ⊑ (x: A) → B`. This should
be provable by induction on the ⇓ chain length under well-founded
environments. Requires: environments must be acyclic in variable
bindings.

## Completed Lemmas

| Lemma | File | Status |
|-------|------|--------|
| Weakening | lemma-weakening.md | ✓ |
| Equal Substitution | lemma-equal-substitution.md | ✓ |
| S-Eval (axiom) | lemma-s-eval.md | ✓ (added as axiom) |
| Narrowing Preserves Subtyping | full-proof-attempt.md | ✓ |

## Rule Changes Made During Proof

| Change | Motivation | Sharp Edge |
|--------|-----------|------------|
| S-Eval added as axiom | Can't be derived; needed for T-App soundness | — |
| T-Asc checks raw target | Evaluated target breaks monotonicity | #10 |
| E-App evaluates body | Concrete counterexample to soundness | #11 |
| T-App-Top unconditional | Typeability + variable-type gaps break monotonicity | #12 |
| T-App uses head normalization (⇓) | Variable types from narrowing break T-App | #12, #13 |
| Well-founded environments | ⇓ requires acyclic variable bindings | — |

## Recommended Next Steps

1. **Prove HN-Mono lemma** (head normalization monotonicity). If
   `F' ⊑ F` and `F ⇓ (x: A) → B` under well-founded Γ, then
   `F' ⇓ (x: C) → D` with `(x: C) → D ⊑ (x: A) → B`. This should
   close Gap 2 in the proof.

2. **Decide on Gap 1 (monotone substitution).** Choose between:
   - Logical relations proof — the "right" approach but significant work
   - Accept the gap with informal argument — pragmatic
   - Investigate polarity analysis — intermediate complexity

3. **If logical relations:** Redesign the proof from scratch using a
   step-indexed logical relation. Soundness becomes "well-typed terms
   are in the logical relation" and the contravariance issue dissolves
   because the relation is defined by observation.
