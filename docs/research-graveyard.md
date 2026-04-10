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
