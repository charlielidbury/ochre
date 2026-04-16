# Research Graveyard

Dead-end worktrees and what they discovered. All branches still on remote
in case we want to revisit.

## Architectural research

### research-self-types (was: ochre-research-A)
**Question:** Can Sub.mu (annotation-based, LHS only) handle dtrue ⊑ dBool?
**Finding:** NO. The contravariant domain check creates an inherent circularity.
Need either Mu-R or coinductive Sub.

### research-norm-trans (was: ochre-research-B)
**Question:** Can muR transitivity be proved via normalization-based approach?
**Finding:** Added muR + muUnfoldL. 5 transitivity sorrys remain. No counterexample
found despite extensive search. Substitution covariance fails for contravariant positions.

### research-cbv (was: ochre-research-C)
**Question:** Can CBV soundness be proved?
**Finding:** Fundamental gap. `Sub [] (eval a) a` is FALSE for ascriptions.
Counterexample: `(var 42 : var 99)` evaluates to `var 42`, not Sub-related.
**Decision:** Keep CBN. CBV would need eval-subst commutation lemma which is also false.

### research-step-indexed (was: ochre-research-step-idx)
**Question:** Does step-indexed Sub close muR transitivity?
**Finding:** NO. Same substitution covariance problem at every step. Literature
confirms (Fu-Stump 2014, Ahmed step-indexing). Need erasure to System Fω, Iris,
or coinductive types.

### research-algorithm (was: ochre-research-D)
**Question:** Can the algorithmic checker be proved sound?
**Finding:** Yes via composition with inductive Sub. Algorithm with seen set
handles cycles computationally but soundness for cycle-break needs coinductive
reasoning. 11 sorrys → 1 (cycle detection only).

### research-simplify
**Question:** Can the proof files be simplified?
**Finding:** 175 lines removed. `termination_by` confirmed incompatible with
transitivity proof (narrow calls trans at same complexity with larger sizes).

### research-tests
**Question:** Build comprehensive test suite with aspirational tests.
**Finding:** 80 passing, 23 aspirational across 5 categories. Merged to main.

### research-bidirectional
**Question:** Build a bidirectional checker on the inductive Sub with muR.
**Finding:** SubN scaffolding for step-indexed transitivity. 2 fundamental sorrys
remain (downward, trans). Same wall as research-norm-trans.

### research-check-primary
**Question:** Make the constructive checker the primary system.
**Finding:** Substitution lemma for check needs ~400-600 lines + transitivity helper.
Phase 2 partial. Stalled.

### research-check-no-mu
**Question:** Build constructive checker for the no-μ system, then extend with μ.
**Finding:** No-μ version proven (commit b5fcfa0). Adding AppR turned out to be
**unsound** (machine-verified counterexample). Mining the b5fcfa0 snapshot for
the proven baseline.

### option3-recovery
**Question:** Recover option 3 (Trans as constructor) work after auto-cleanup.
**Finding:** Recovered. Trans-as-constructor blocks lambda inversion, can't handle
self-types via that route either.

### mu-soundness
**Question:** Add μ to the proven base.
**Finding:** Successfully merged μ to main. The μ-not-a-value design (always unfold)
aligns eval with Sub.mu, making soundness work.

### research-iota-elim
**Question:** Can we crack the IotaElim circularity for self-types?
**Finding:** Added head-iota equi-recursive rules (iotaIntro, iotaR, iotaL).
Mechanically derives `dtrue3 ⊑ dBool3` (Church-dependent Bool) via structural
rules. **BUT soundness/transitivity NOT verified.**

### research-iota-trans
**Question:** Can transitivity be proved for the iota rules?
**Finding:** NO for contravariant self-references. Identified exactly 3 obstructed
trans cases (iotaIntro × iotaL, iotaIntro × iotaIntro, iotaR × iotaIntro).
Tried fusion (iotaIntroD) — moves the problem doesn't solve it. The fundamental
obstacle is substitution monotonicity for contravariant positions.

### research-betar
**Question:** Can BetaR (literal lambdas only) be added with proven transitivity?
**Finding:** Almost. The rule itself is sound (counterexample rejected), but
trans(betaR_lhs, app) breaks the cut-formula measure. body[arg] can be larger
than the original cut when var 0 appears multiple times in body. Lambda inversion
proved, but doesn't help — same fundamental issue.

### research-canonical-app
**Question:** Replace [App]'s existential (D,R) with canonical principal synthesis?
**Finding:** **FUNDAMENTALLY DOES NOT WORK.** Three independent obstructions:
1. Soundness gap on ascriptions (trust or reject — both bad)
2. Narrowing breaks (principal differs across contexts)
3. **Eval preservation breaks** (most severe) — needs Sub sub-derivation for f
   which principal cannot provide

**This is the definitive answer**: the principal type obstruction is not syntactic.
Solving BetaR/μ/AppR/IotaR requires SEMANTIC methods (logical relations, step-indexed
Kripke models) rather than canonical-form rules. The existing Sub rule set (7 rules,
existential [App]) is the maximum provable with current syntactic technique.

### research-iota-fix-split
**Question:** Does splitting bundled μ into separate ι (self-type) and fix
(recursive binder) unlock the whiteboard `dtrue ⊑ Bool` theorem?
**Finding:** Split is a clean design — iotaIntro with fixed-self substitution
proves trans/narrow/subst (from research-iota-impl). fixAnn + unfoldFixL adds
only 1 sorry (`fixAnn × unfoldFixL` trans: no bridge between annotation-only
LHS and equi-recursive RHS).

**BUT the target theorem is NOT closable**, and the obstruction is orthogonal
to ι/fix. It's a structural [App] obstruction: decomposing `dtrue ⊑ Bool`
via [Iota-Intro] + [Lam] reaches `app P cTrue ⊑ cBool→⊤` (at the
contravariant domain position of the second Lam, under `P:cBool→⊤` in
context). Via [App] + [Var] + [Refl], this reduces to `⊤ ⊑ cBool→⊤` —
false (⊤ is top, not bottom).

This is a MISSING BETA / DefEq obstruction in the baseline 7 rules, not
a self-type problem. Splitting ι from fix doesn't help. See
`docs/research/iota-fix-split.md` for full writeup.

**Recommendation**: DO NOT merge to main. Complexity increase without
payoff. Keep branch for reference. Investigate [BetaL] / [DefEq]
independently before revisiting ι/fix split.

## Architecturally validated findings

1. **Inductive Sub has a fundamental "principal type" issue** with the existential
   D, R in [App]. Currently safe because LHS substitution doesn't compose with
   the cut formula. Adding ANY rule that puts function application on the RHS
   (BetaR, Mu-R, AppR with existential) creates an unsoundness.

2. **The fix is to remove the existential** — use canonical synthesis instead.
   For literal lambdas this is trivial: the lambda IS its own canonical type.
   For variable-headed applications it's harder.

3. **Self-types (dtrue ⊑ dBool) are inherently circular** — need cycle detection
   in the algorithm OR coinductive Sub OR step-indexed LR. Multiple approaches
   tried, all hit walls.

4. **Call-by-value is unsound** for this calculus. Stick with CBN.

5. **μ-not-a-value** (always unfold in eval) is the right design. Aligns with Sub.mu
   so soundness works.
