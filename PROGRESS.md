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

`lake build` passes. **3 sorry'd declarations** in Soundness.lean:

- `VCompat.adequacy` — partially proven (5 sub-sorrys, see below)
- `soundness_gen` app case — needs application congruence (line ~349)
- `soundness` — needs concEval→concEvalE bridge (line ~449)

**PROVEN this session (agent ochre-lean-20260402-221900):**
- VCompat.adequacy PARTIAL — 9 of 14 case combinations proven
  - σ = τ: direct ✓
  - τ = .type: top ✓
  - n = 0: trivial ✓
  - v = σ (refl): subCheckNF fallback ✓
  - σ = .type, τ ∉ {.type, .mu}: contradiction (inferType .type = none) ✓
  - Structural lam, τ = lam: IH on bodies via subCheckNF_lam_lam_body ✓
  - Structural lam, τ ∉ {.type, .lam, .mu}: contradiction (inferType lam = none) ✓
  - Structural mu, τ = mu: IH on bodies via subCheckNF_mu_mu_body ✓
  - Mu left: IH with original subCheckNF ✓

**SORRY'D sub-cases in adequacy (all involve mu/seen interaction):**
1. σ = .type, τ = mu — self-intro with seen list
2. Structural lam, τ = mu — self-intro with seen list
3. Structural mu, τ ∉ {.type, .mu} — self-elim with seen list
4. Mu right (σ = mu, unfold right) — all subcases
5. subCheckNF fallback — needs subCheckNF transitivity

**Helper lemmas added to Subtyping.lean:**
- `subCheckNF_lam_lam_body`: extracts body subCheckNF from lam⊑lam
- `subCheckNF_mu_mu_body`: extracts body subCheckNF from mu⊑mu
- `subCheckNF_lam_impossible`: contradiction for lam vs non-{type,lam,mu}
- `inferType_lam`: inferType returns none for lambdas
- Made `inferType` and `normalizeDomain` non-private (needed for proofs)

**Previously proven (still proven):**
- `VCompat.mono` (downward closure)
- `soundness_gen` bvar, type, lam, mu, asc cases
- Decoupled VCompat step index from fuel

**All milestone tests pass** (M1-M4 including abstract appendVec).
**11 WellTyped witness tests pass.**

## File structure

- `Syntax.lean` — Expr type (de Bruijn indices), substitution, shifting
- `Eval.lean` — absEval, concEval, concEvalE, fuel monotonicity lemmas
- `Subtyping.lean` — subCheckNF (algorithmic), SubtypeCore/Subtype' (declarative),
  helper extraction lemmas for adequacy
- `Soundness.lean` — WellTyped, VCompat definition, soundness theorems
- `Tests.lean` — sacred acceptance tests (DO NOT WEAKEN)

## Key design insights this session

### Adequacy proof structure

VCompat.adequacy is proved by **induction on n** (VCompat step index), with
two upfront `by_cases` (σ = τ, τ = .type) that handle easy cases uniformly.

The IH at step m is universal over fuel and ctx:
```
ih : ∀ {v σ τ fuel ctx}, VCompat m v σ → subCheckNF fuel ctx [] σ τ → VCompat m v τ
```

For structural cases (lam→lam, mu→mu): extract body subCheckNF from the
lam/lam or mu/mu case of subCheckNF, then apply IH on bodies. The body
extraction requires the helper lemmas in Subtyping.lean.

For mu-left: the IH applies directly with the ORIGINAL subCheckNF (no
extraction needed). This is the cleanest case.

### Why the sorry'd cases are hard

All remaining sorrys involve subCheckNF's `seen` list for coinductive
termination. When subCheckNF does self-intro (σ ⊑ mu ann body), it adds
(σ, mu ann body) to `seen` and recurses. The IH needs empty `seen`.

**The fundamental tension:** subCheckNF uses COINDUCTION (seen list) for
mu types, while VCompat uses INDUCTION (step index). Bridging them requires
showing that n steps of VCompat unfolding suffice to cover what the seen
list achieves coinductively.

**Possible approaches for future agents:**
1. **Well-founded induction on (n, fuel):** The combined measure n + fuel
   decreases at each recursive call. For self-intro: decrease n (use
   mu-right unfolding), for structural cases: decrease fuel.
   The hseen invariant would quantify over m < n.

2. **Generalized adequacy with seen:** Prove adequacy_gen with an hseen
   invariant: `∀ p ∈ seen, ∀ m < n, VCompat m v p.1 → VCompat m v p.2`.
   The self-intro case provides hseen by appealing to adequacy at lower n
   (via strong induction). The seen check case uses hseen at m < n, which
   gives VCompat m (not VCompat n). This is weaker but might suffice
   combined with mu-right unfolding.

3. **subCheckNF transitivity:** Would solve the fallback case. Proving
   transitivity of the algorithmic checker is non-trivial due to
   coinductive termination, but it's a well-defined mathematical property.

## What the next agent should do

### Priority 1: Prove more adequacy sub-cases

The most impactful next step is tackling the mu/seen cases in adequacy.
Start with approach 2 (generalized adequacy with hseen at m < n). The
self-intro case at step n+1 would:
1. Use mu-right unfolding: need VCompat n v (body.subst 0 (mu ann body))
2. Apply adequacy_gen at step n with the inner subCheckNF (fuel-1)
3. Provide hseen for (σ, mu ann body) by strong induction on n

Key question: when the inner subCheckNF hits the seen entry, hseen gives
VCompat m (m < n), not VCompat n. The fuel IH at step n can't directly
use this. This is the crux of the difficulty.

### Priority 2: App case (Soundness.lean:~349)

The app case needs "application congruence." The standard approach is to
reformulate soundness_gen with **related environments** (EnvCompat), where
env_v and env_τ are pointwise VCompat. This is a significant refactor but
follows the textbook LR approach. See SUGGESTIONS.md for details.

### Priority 3: concEval→concEvalE bridge (Soundness.lean:~449)

For the top-level soundness theorem. Separate concern from the main proof.

## What's been tried (and failed)

Previous agents spent significant effort on a **structural** soundness proof
using SoundRel (a relation requiring matching top-level constructors). This
approach is **fundamentally broken**: ascription `(e : τ)` produces results
with different constructors (e.g., a lam value vs a mu type), so no
structural relation can bridge them.

The step-index coupling (VCompat fuel = fuel) was also a dead end for the
asc case. The fix (decoupled step index) is documented in commit 7afd7fc.

**Do not attempt structural relations for soundness.** Use VCompat as described
above.
