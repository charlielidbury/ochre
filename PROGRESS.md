# Progress

## Current state: mu experiment (branch claude/mu-experiment)

We have replaced `fix` (recursion) and `iota` (self types) with a single
unified primitive `mu` (self-reference). See `docs/ideas/merge-fix-iota.md`
for the full design rationale, and **SUGGESTIONS.md** for the current
roadmap and strategy.

### Build status

`lake build` passes with **3 sorrys** and all tests (including WellTyped witnesses).

- **Subtyping.lean: SORRY-FREE** (includes `SubtypeCore.shift_preserve`)
- **Monotonicity.lean: 1 sorry** (`absEval_mono` — blocked on SubtypeCore weakness)
- **Soundness.lean: 1 sorry** (`soundness_gen` — fundamental SubtypeCore weakness)
- **ValSub.lean: 1 sorry** (`bridge` — see analysis below)

**Total: 3 sorrys.** All tests pass including WellTyped witnesses.

### Recent changes (2026-04-02, agent ochre-lean-20260402-141112)

**Phase 4 Step 1: ValSub definition + SubtypeCore embedding + analysis.**

Created `Och/ValSub.lean` with:
- **ValSub definition:** Step-indexed value subtyping, `ValSub n v τ : Prop`.
  Defined as a disjunction by recursion on n. At n=0, trivially true (no
  budget). At n+1, seven disjuncts: top, refl, lam_sub (contra domain +
  co body), mu_body, app_cong, mu_r (self-intro), mu_l (self-elim).
- **Intro lemmas:** Named constructors for each disjunct (top, refl, refl',
  lam_sub, lam_body, mu_body, app_cong, mu_r, mu_l).
- **SubtypeCore embedding:** `of_subtypeCore : SubtypeCore v τ → ∀n, ValSub n v τ`.
  Proved by induction on SubtypeCore. Each case maps to the corresponding
  ValSub disjunct. This ensures the existing soundness proof cases (which
  produce SubtypeCore) still work when the output changes to ValSub.
- **Bridge lemma (sorry'd):** The critical missing piece for the asc case.
- **subst_congr counterexample (IMPORTANT):** Proved via native_decide that
  substitution congruence is FALSE for ValSub. See below.

### KEY FINDING: subst_congr is false

`ValSub n a b → ValSub n (e.subst j a) (e.subst j b)` is **FALSE** for the
syntactic ValSub with contra-domain lam_sub.

**Counterexample (verified by native_decide):**
- e = `lam (bvar 0) (bvar 1)` — lambda whose domain IS the substituted variable
- a = zero', b = Nat'
- zero' ⊑ Nat' holds (zero is a nat)
- e.subst 0 zero' = `lam zero' (bvar 0)`
- e.subst 0 Nat' = `lam Nat' (bvar 0)`
- lam zero' body ⊑ lam Nat' body requires Nat' ⊑ zero' (contra domain) — FALSE

**Consequence:** The GENERALIZED soundness approach (ValSub/SubtypeCore on
inputs + substitution congruence) is fundamentally blocked. This is the same
issue SubtypeCore had — contra-domain makes substitution non-monotone.

### Analysis of the bridge lemma

The bridge `ValSub n v σ → subCheckNF σ τ = true → ValSub n v τ` is needed
for the asc case of soundness. Analysis of each case:

- **σ = τ (refl):** Trivial ✓
- **τ = Type (top):** ValSub.top ✓
- **Bodies (covariant):** Recursive bridge call. ✓
- **Domains (contravariant):** BLOCKED. Need ValSub domτ domv from
  ValSub domσ domv + subCheckNF domτ domσ. This requires either:
  (a) ValSub transitivity (hard — step accounting doesn't align)
  (b) subCheckNF_sound into ValSub + ValSub transitivity
  (c) A reverse bridge: subCheckNF(a,b) + ValSub(b,c) → ValSub(a,c)
- **Mu cases:** Should work (fuel consumption aligns with step index).
- **inferType cases:** Needs context awareness (subCheckNF uses ctx, ValSub doesn't).

### Important insight: shared lambda domains

In the soundness proof, v (from concEval) and σ (from absEval) always share
lambda domains because both evaluators preserve the syntactic domain:
```
| .lam dom body => ... some (.lam dom body')  -- dom unchanged!
```
This means the domain composition problem may not arise at the TOP level
(where v and σ are direct eval outputs). It DOES arise for nested comparisons.

### Recommended next step: semantic ValSub (logical relation)

The syntactic ValSub has clear limitations for the bridge. The recommended
alternative is a **semantic (logical relation) ValSub** where the lam case
quantifies over all argument evaluations:

```
ValSub n (lam domv bodyv) (lam domτ bodyτ) :=
  ∀ m ≤ n, ∀ av aτ, ValSub m av domτ →
    ∀ rv, concEval m [] (bodyv.subst 0 av) = some rv →
    ∀ rτ, absEval m [] (bodyτ.subst 0 aτ) = some rτ →
    ValSub m rv rτ
```

This approach:
- Makes the app case of soundness trivial (instantiate the quantifier)
- Avoids subst_congr entirely
- Makes the bridge's lam case tractable (domain subsumption follows from
  the quantifier's domain condition)
- Couples the relation to the evaluator (acceptable trade-off)
- Is the standard approach in the step-indexed logical relations literature

See `docs/research/amin-rompf-deep-dive.md` for the Amin-Rompf precedent.

### Previous changes (2026-04-02, agent ochre-lean-20260402-135537)

**Phase 3.5: Env extend lemmas — COMPLETE (4 sorrys eliminated).**

Proved all env extend infrastructure for de Bruijn:
- `SubtypeCore.shift_preserve` (Subtyping.lean) — SubtypeCore preserved under shifting
- `envSubCore_extend` + `envSubCore_extend_sub` (Monotonicity.lean)
- `envConsistent_extend` + `envConsistent_extend_sub` (Soundness.lean)

**absEval_mono NOT reproved — blocked on substitution lemma.** The de Bruijn
migration changed beta-reduction from env extension to substitution. The old
proof used `envSubCore_extend_sub` to thread the argument into the env; the
new proof needs `SubtypeCore (body₂.subst 0 aVal₂) (body₁.subst 0 aVal₁)`
given `SubtypeCore body₂ body₁` and `SubtypeCore aVal₂ aVal₁`. This doesn't
hold because `lam_body` requires equal domains — substituting different values
into a nested lambda's domain breaks this. Fixing it requires adding
`lam_cong`/`mu_cong` (allowing different domains/anns) to SubtypeCore, but
Phase 4 replaces SubtypeCore entirely, making that work redundant.

### Previous changes (2026-04-02, agent ochre-lean-20260402-123003)

**Phase 3: De Bruijn indices — COMPLETE.**

Migrated the entire codebase from named variables to de Bruijn indices.
This is the biggest mechanical change in the project's history.

**What changed:**

1. **Syntax.lean:** `Expr` now uses `bvar : Nat` (de Bruijn index) instead of
   `var : Name`. `lam` and `mu` no longer carry binder names. Added `shift`
   (increment free vars) and `subst` (substitute + shift down). Added `Named`
   type + `toExpr` converter so test terms can be written readably.

2. **Eval.lean:** `Env = List Expr` (positional, env[k] = value for bvar k).
   `Env.extend` shifts existing entries when entering a binder. Beta-reduction
   uses **substitution** (not env extension) — subst argument into body, then
   re-evaluate. This is a semantic change from the old env-based beta.

3. **Subtyping.lean:** `subCheckNF` uses `Env.extend` for ctx management (with
   shifting). Domains are normalized on BOTH sides before comparison (needed
   because subst-produced domains contain unreduced applications). `inferType`
   uses positional lookup (ctx.get? k). No variable renaming needed anywhere.

4. **Monotonicity.lean:** Sorry'd (was sorry-free). Needs reproving with new
   env extension patterns.

5. **Soundness.lean:** Sorry'd (was 3 sorrys). Needs reproving with new env
   and subst-based beta. WellTyped updated to use Env.extend and subst.

6. **Tests.lean:** All definitions use Named syntax + `n` converter. All tests
   pass. One behavioral change: `concEval toZero one'` now terminates (= zero')
   because subst-based beta reuses normalized mu bodies instead of re-evaluating.

7. **CounterexampleTest.lean:** Deleted (named-variable-specific concepts like
   freeVars/evalFreeVars; preserved in git history).

**Key design decisions:**

- **Hybrid evaluation:** Env-based for normalization under binders (lam, mu body),
  substitution-based for beta-reduction (app-lam, app-mu). This avoids the closure
  problem (env-based de Bruijn beta would need closures to track definition-site envs).

- **Env.extend shifts all entries:** When entering a binder, existing env/ctx entries
  are shifted up by 1 so their bvar indices stay correct at the new depth. New entries
  (neutrals for lam, mu values for mu) are NOT shifted because they're already at the
  correct depth. BUT domain types added to subCheckNF's ctx ARE shifted (they're from
  the outer scope).

- **Domain normalization on both sides:** With subst-based evaluation, domains can
  contain unreduced applications (e.g., `zero' Type Unit' (λacc. ...)` instead of
  `Unit'`). Both sides are normalized before comparison.

- **concEval behavioral change:** `concEval` for recursive mu + Church branching now
  terminates (was divergent). The subst-based beta reuses the already-normalized mu
  body, so the recursive call's result is embedded in the term rather than re-computed.
  The test was updated to reflect this.

**What's next (for the next agent):**

See SUGGESTIONS.md Phase 4. The ValSub definition is in place. The critical
next step is either:
1. **Prove the bridge lemma** (hard — requires solving domain composition)
2. **Replace syntactic ValSub with semantic ValSub** (logical relation approach)
3. **Rewrite soundness to output ValSub** (straightforward once bridge works)

### Previous changes

See git log for full history. Key milestones:
- Phase 1 (milestone tests): All M1-M4 pass including abstract appendVec
- Phase 2 (non-vacuous WellTyped): Bool-valued with subCheckNF, 11 witnesses
- Phase 3 (de Bruijn): Complete migration
- Phase 3.5 (env extend lemmas): 4 sorrys eliminated
