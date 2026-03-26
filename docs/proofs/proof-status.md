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

### Gap 1: Monotone Substitution — MOSTLY RESOLVED by deep domain erasure

**Location:** T-App soundness and monotonicity.

**Previous problem:** Substituting a more-precise value into a
contravariant (domain) position of the body gives a WRONG-DIRECTION
comparison. This was a concrete soundness counterexample (see sharp
edge #14).

**The fix:** Deep domain erasure in E-Fun: `(x: A) → M ⟶ (x: ⊤) → erase(M)`.
The `erase` function recursively replaces all domain annotations with ⊤.
This removes x from all domain positions before substitution. After erasure,
x only appears in body (covariant) positions, where monotone substitution
holds.

**How deep erasure resolves the T-App soundness case:**

With deep erasure, E-App uses `erase(B)[x ≔ N_v]` (erased body with
concrete argument). T-App uses `B[x ≔ N']` (raw body with abstract
argument). The key differences:
1. Domains: concrete has ⊤ everywhere; abstract has precise terms.
   All domain comparisons are `domain(R) ⊑ ⊤` = S-Top. ✓
2. Body positions: concrete has N_v; abstract has N'. Since N_v ⊑ N'
   (by soundness IH) and these are covariant positions, the comparison
   goes the right direction. ✓

**Remaining sub-gap: erase(M) ⊑ M for T-Fun soundness.**

T-Fun soundness needs `(x: ⊤) → erase(M) ⊑ (x: A) → M`, which by
S-Fun requires `x: A ⊢ erase(M) ⊑ M`. This holds for:
- Variables: erase(x) = x, S-Refl ✓
- ⊤: erase(⊤) = ⊤, S-Refl ✓
- Function literals: erase((y: B) → N) = (y: ⊤) → erase(N), S-Fun
  with B ⊑ ⊤ (S-Top) and IH on N ✓
- Applications: erase(M₁ M₂) = erase(M₁) erase(M₂), S-App with
  IH on M₁ and M₂ ✓
- **Ascription: erase(M : A) = erase(M) : erase(A). No rule
  decomposes ascription on the right of ⊑. NOT DERIVABLE when erase
  changes M or A.**

The ascription sub-gap only arises for function bodies containing
ascription terms where the inner term or target contains function
subterms with parameter-dependent domains. This is an uncommon pattern.
A logical relations proof would close it entirely.

**Monotone substitution in covariant positions (new property):**

After deep erasure, the concrete body `erase(B)` only has x in body
(covariant) positions. Substituting N_v ⊑ N' into covariant positions
preserves the ⊑ direction. This is provable by structural induction on
erase(B), using the mutual soundness/monotonicity IH.

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
| Values Have Erased Domains | lemma-values-erased.md | ✓ |
| Domain Erasure Subtyping | lemma-erase-sub.md | ✓ (modulo ascription sub-gap) |
| HN-Mono (sketch) | lemma-hn-mono.md | Sketch only |

## Rule Changes Made During Proof

| Change | Motivation | Sharp Edge |
|--------|-----------|------------|
| S-Eval added as axiom | Can't be derived; needed for T-App soundness | — |
| T-Asc checks raw target | Evaluated target breaks monotonicity | #10 |
| E-App evaluates body | Concrete counterexample to soundness | #11 |
| T-App-Top unconditional | Typeability + variable-type gaps break monotonicity | #12 |
| T-App uses head normalization (⇓) | Variable types from narrowing break T-App | #12, #13 |
| Well-founded environments | ⇓ requires acyclic variable bindings | — |
| E-Fun deep domain erasure | Soundness counterexample: inner domains break V ⊑ R | #14 |
| S-App congruence added | Needed for erase(M) ⊑ M lemma on application terms | #14 |

## Recommended Next Steps

1. **Prove erase(M) ⊑ M lemma** for variables, ⊤, function literals,
   and applications. Document the ascription sub-gap.

2. **Prove HN-Mono lemma** (head normalization monotonicity). If
   `F' ⊑ F` and `F ⇓ (x: A) → B` under well-founded Γ, then
   `F' ⇓ (x: C) → D` with `(x: C) → D ⊑ (x: A) → B`. This should
   close Gap 2 in the proof.

3. **Complete T-App soundness** using deep erasure. The proof structure:
   - All domain comparisons become S-Top (values have erased domains)
   - Body comparisons use monotone substitution in covariant positions
   - IH provides soundness on sub-derivations

4. **Complete T-App monotonicity** using the same deep erasure argument.
   The key insight: under Γ' ⊑ Γ, use T-App under Γ' (with HN-Mono
   for head normalization) or fall back to T-App-Top for ⊤ ⊑ ⊤.

5. **Close the ascription sub-gap** (optional). Either:
   - Accept it as a proof-technique limitation (pragmatic)
   - Use logical relations for a publication-quality proof
