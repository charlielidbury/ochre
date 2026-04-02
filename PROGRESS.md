# Och — current state

## What Och is

Och is a minimal pure calculus isolating the core semantic idea of Ochre
(a systems theorem prover, roughly Rust + Dependent Types). Terms and types
share a single syntax. Types are "approximate programs." The ONLY difference
between compile-time and runtime is the ascription case: `(e : τ)` takes `e`
concretely and `τ` abstractly.

See `docs/what-is-och.md` for details and `docs/ideas/merge-fix-iota.md` for
the mu design.

## Build status

`lake build` passes. **3 sorrys** in Soundness.lean:

- `VCompat.adequacy` — VCompat through subCheckNF (line ~228)
- `soundness_gen` app case — needs application congruence (line ~329)
- `soundness` — needs concEval→concEvalE bridge (line ~362)

**PROVEN this session (agent ochre-lean-20260402-214913):**
- `soundness_gen` asc case — was sorry'd, now proven using adequacy
- Key architectural change: decoupled VCompat step index from eval fuel

**Previously proven (still proven):**
- `VCompat.mono` (downward closure)
- `soundness_gen` bvar, type, lam, mu cases

**All milestone tests pass** (M1-M4 including abstract appendVec).
**11 WellTyped witness tests pass.**

## File structure

- `Syntax.lean` — Expr type (de Bruijn indices), substitution, shifting
- `Eval.lean` — absEval, concEval, concEvalE, fuel monotonicity lemmas
- `Subtyping.lean` — subCheckNF (algorithmic), SubtypeCore/Subtype' (declarative)
- `Soundness.lean` — WellTyped, VCompat definition, soundness theorems
- `Tests.lean` — sacred acceptance tests (DO NOT WEAKEN)

## Key design decisions this session

### Decoupled VCompat step index from evaluation fuel

**THE MOST IMPORTANT CHANGE THIS SESSION.**

Previous: `soundness_gen` concluded `VCompat fuel v τ` where the VCompat
step index was the same as the evaluation fuel. This caused a step-index
mismatch in the asc case:

- The IH at fuel k gives VCompat k (step index = fuel).
- The asc case needs VCompat (k+1) (the outer fuel).
- Adequacy preserves the step level: VCompat k → VCompat k. Can't bridge.

The structural cases (lam/mu) didn't have this problem because their
VCompat disjunct at step k+1 uses VCompat k for bodies — the step
decrease is "consumed" by the structural decomposition. But the asc case
has no structural decomposition; it changes σ to τ via subCheckNF.

**Fix:** Make `n` (VCompat step index) a separate parameter from `fuel`:

```lean
theorem soundness_gen
    (fuel : Nat) (env : Env) (e : Expr) (v τ : Expr) (n : Nat)
    (...) : VCompat n v τ
```

By induction on fuel with n universally quantified. The IH gives
VCompat at ANY step level n. For the asc case: pick n = m+1 (same as
goal), apply adequacy at the same level. For lam/mu cases: pick n = m
(one less, consumed by structural case).

### VCompat: relaxed domain/annotation matching

Structural lam case no longer requires the same domain; structural mu
case no longer requires the same annotation. This is needed for adequacy
to be provable: when subCheckNF (lam dA bodyA) (lam dB bodyB) changes
the domain from dA to dB, the resulting VCompat must accommodate dB ≠ dA.

The soundness lam/mu cases still work because both evaluators produce
the same domain/annotation from the same source expression.

## What the next agent should do

### 1. Prove VCompat.adequacy (Soundness.lean:~225)

`VCompat n v σ → subCheckNF fuel ctx [] σ τ = true → VCompat n v τ`

This is the CRITICAL next step. The asc case of soundness_gen depends on it.

**Proof strategy:** By induction on n.
- n = 0: VCompat 0 = True, trivially true.
- n + 1: Case split on VCompat (n+1) v σ, then on how subCheckNF returns true:
  - σ = .type: subCheckNF .type τ implies τ = .type, VCompat via top. ✓
  - v = σ: subCheckNF v τ, use subCheckNF fallback of VCompat. ✓
  - structural lam: v = lam dV bV, σ = lam dS bS, VCompat n bV bS.
    subCheckNF (lam dS bS) τ with τ = lam dT bT gives subCheckNF bS bT.
    IH on bodies: VCompat n bV bS → subCheckNF bS bT → VCompat n bV bT.
    Then VCompat (n+1) (lam dV bV) (lam dT bT) via structural lam. ✓
  - structural mu: similar.
  - mu unfold right/left: harder, interacts with subCheckNF's `seen` list.
  - subCheckNF fallback: compose two subCheckNFs (needs transitivity).

**Hard part:** The mu-unfolding cases interact with subCheckNF's coinductive
`seen` list. When subCheckNF uses self-intro (τ = mu ann body →
check σ ⊑ body.subst 0 (mu ann body) with extended seen), the recursive
adequacy call has non-empty seen. May need a generalized version.

**Consider proving for non-mu cases first** and sorry'ing the mu cases.

### 2. App case: "application congruence" (Soundness.lean:~329)

The hardest remaining step. See SUGGESTIONS.md for detailed analysis.

### 3. concEval→concEvalE bridge (Soundness.lean:~362)

For the top-level soundness theorem. Separate concern from the main proof.

## What's been tried (and failed)

Previous agents spent significant effort on a **structural** soundness proof
using SoundRel (a relation requiring matching top-level constructors). This
approach is **fundamentally broken**: ascription `(e : τ)` produces results
with different constructors (e.g., a lam value vs a mu type), so no
structural relation can bridge them.

The step-index coupling (VCompat fuel = fuel) was also a dead end for the
asc case. The fix (decoupled step index) is documented above.

**Do not attempt structural relations for soundness.** Use VCompat as described
above.
