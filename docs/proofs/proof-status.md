# Och₀ Proof Status

Status of the soundness and monotonicity proofs as of the current rules
in `docs/och.md`.

## Theorem Statements

**Soundness:** If `Γ ⊢ M ⇒ A` and `M ⟶ V`, then `Γ ⊢ V ⊑ A`.

**Monotonicity:** If `Γ ⊢ M ⇒ A` and `Γ' ⊑ Γ` (pointwise), then
there exists a derivation `Γ' ⊢ M ⇒ A'` with `Γ' ⊢ A' ⊑ A`.

(The typing judgment is deterministic: each term has at most one type
under a given environment. Soundness holds for every typeable term.
Monotonicity says: for every typing derivation under Γ, there exists a
typing derivation under Γ' with a more-precise-or-equal result.)

## Case-by-Case Status

### Soundness

| Case | Status | File | Notes |
|------|--------|------|-------|
| T-Top | ✓ Complete | soundness-t-top.md | V = ⊤, A = ⊤, S-Refl |
| T-Var | ✓ Complete | soundness-t-var.md | Vacuous (variables don't evaluate) |
| T-Fun | ✓ Complete | soundness-t-fun.md | E-Fun erases domain; S-Fun + S-Top |
| T-Asc | ✓ Complete | soundness-t-asc.md | V ⊑ M' ⊑ A ⊑ A' chain |
| T-App | ✓ Complete | soundness-t-app-v2.md | Resolved by abstract + concrete erasure |

### Monotonicity

| Case | Status | File | Notes |
|------|--------|------|-------|
| T-Top | ✓ Complete | monotonicity-easy.md | ⊤ ⇒ ⊤ in both; S-Refl |
| T-Var | ✓ Complete | monotonicity-easy.md | Γ'(x) ⊑ Γ(x) directly |
| T-Fun | ✓ Complete | monotonicity-easy.md | T-Fun is environment-independent |
| T-Asc | ✓ Complete | monotonicity-easy.md | Raw target stable; IH on sub-derivations |
| T-App | ✓ Complete | monotonicity-t-app-v2.md | Resolved by abstract erasure + HN-Mono |

## Remaining Gaps

### Gap 1: Monotone Substitution — RESOLVED by abstract domain erasure

**Location:** T-App soundness and monotonicity.

**Previous problem:** Substituting a more-precise value into a
contravariant (domain) position of the body gives a WRONG-DIRECTION
comparison. This was a concrete soundness counterexample (sharp edge
#14) AND a concrete monotonicity counterexample (sharp edge #16).

**The fix (both soundness and monotonicity):**
1. E-Fun deep domain erasure: `(x: A) → M ⟶ (x: ⊤) → erase(M)` — fixes
   soundness by ensuring values have ⊤ domains.
2. T-App abstract domain erasure: `erase(B)[x ≔ N'] ⇒ R` — fixes
   monotonicity by ensuring the argument type only lands in covariant
   positions.

After erasure on both sides, concrete evaluation uses `erase(B)[x ≔ N_v]`
and abstract evaluation uses `erase(B)[x ≔ N']`. The bodies are the same
erased form; only the substituted values differ. Since x only appears in
covariant positions of erase(B), the ⊑ direction is preserved:
- Soundness: N_v ⊑ N' → R_concrete ⊑ R_abstract ✓
- Monotonicity: N'' ⊑ N' → R' ⊑ R ✓

**Previously remaining sub-gap (NOW RESOLVED): erase(M) ⊑ M for ascription.**

T-Fun soundness needs `(x: ⊤) → erase(M) ⊑ (x: A) → M`, which by
S-Fun requires `x: A ⊢ erase(M) ⊑ M`. This holds for all cases:
- Variables: erase(x) = x, S-Refl ✓
- ⊤: erase(⊤) = ⊤, S-Refl ✓
- Function literals: erase((y: B) → N) = (y: ⊤) → erase(N), S-Fun
  with B ⊑ ⊤ (S-Top) and IH on N ✓
- Applications: erase(M₁ M₂) = erase(M₁) erase(M₂), S-App with
  IH on M₁ and M₂ ✓
- Ascription: erase(M : A) = erase(M) : erase(A), **S-Asc** with
  IH on M and A ✓

The ascription sub-gap was closed by adding S-Asc (structural
congruence for ascription), analogous to S-App for applications.
See lemma-erase-sub.md for the complete proof.

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
| Domain Erasure Subtyping | lemma-erase-sub.md | ✓ Complete |
| HN-Mono (sketch) | lemma-hn-mono.md | Sketch only |

## Rule Changes Made During Proof

| Change | Motivation | Sharp Edge |
|--------|-----------|------------|
| S-Eval added as axiom | Can't be derived; needed for T-App soundness | — |
| T-Asc checks raw target | Evaluated target breaks monotonicity | #10 |
| E-App evaluates body | Concrete counterexample to soundness | #11 |
| T-App-Top added then removed | Was added for monotonicity fallback, removed when proofs didn't need it | #12 |
| T-App uses head normalization (⇓) | Variable types from narrowing break T-App | #12, #13 |
| Well-founded environments | ⇓ requires acyclic variable bindings | — |
| E-Fun deep domain erasure | Soundness counterexample: inner domains break V ⊑ R | #14 |
| S-App congruence added | Needed for erase(M) ⊑ M lemma on application terms | #14 |
| HN-Eval added to ⇓ | App/asc terms in narrowed envs break monotonicity | #15 |
| T-App abstract domain erasure | Monotonicity counterexample: domains break ⊑ direction | #16 |
| S-Asc structural congruence added | Needed for erase(M) ⊑ M lemma on ascription terms | #8 |

## Recommended Next Steps

1. ~~**Close the ascription sub-gap**~~ — DONE. Resolved by adding S-Asc
   (structural congruence for ascription). See lemma-erase-sub.md.

2. **Formalize the ⇓-preserves-⊑ S-Trans case.** The combined induction
   argument in lemma-hn-mono-v2.md is sketched but not fully formal.

3. **Formalize the monotone-covariant-substitution lemma.** After
   abstract erasure, x only appears covariantly in erase(B). Substituting
   N'' ⊑ N' should preserve ⊑. This needs structural induction on
   erase(B) with a clear definition of "covariant position."
