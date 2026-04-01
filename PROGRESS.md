# Progress

## Current state: mu experiment (branch claude/mu-experiment)

We have replaced `fix` (recursion) and `iota` (self types) with a single
unified primitive `mu` (self-reference). See `docs/ideas/merge-fix-iota.md`
for the full design rationale, and **SUGGESTIONS.md** for the current
roadmap and strategy.

### Build status

`lake build` passes with **5 sorry warnings**:
- Monotonicity.lean: 4 (absEval_mono [2 app-mu subcases], absEval_mono_trans,
  absEval_succeeds_envsub, absEval_evalFreeVars_general [mu app subcase])
- Soundness.lean: 1 (soundness_gen)

### Recent changes (2026-04-01, agent ochre-lean-20260401-185842)

**Annotation-based mu-elim in absEval: 3 milestones flipped (M1d, M4b, M4c)**

The core insight: when absEval encounters `app (mu x ann body) aVal`, the
previous behavior of unfolding the body (substituting the mu back in) causes
**infinite recursion** for fix-like mus. The body contains recursive calls
to `self`, and unfolding re-introduces the mu term, which gets unfolded
again on the next application. With abstract arguments, there's no base
case to terminate the recursion.

**The fix**: use the mu's annotation to determine the return type.

```lean
| some (.mu x ann body), some aVal =>
    match absEval fuel Γ ann with
    | some (.lam y _dom retBody) =>
        -- Annotation is a function type: beta-reduce with the argument.
        absEval fuel ((y, aVal) :: Γ) retBody
    | _ =>
        -- Annotation uninformative (e.g., Type). Fall back to body unfolding
        -- for self-type elimination (iota-like mus).
        let unfolded := body.subst x (.mu x ann body)
        ...
```

For **fix-like mus** (recursion, annotation = function type): the annotation
gives the return type directly, avoiding divergence. This is semantically
correct because the annotation declares the mu's type.

For **iota-like mus** (self-types, annotation = Type): falls back to body
unfolding, preserving the existing self-type elimination behavior.

**This makes the annotation field on mu LOAD-BEARING.** Previously it was
dead code (SUGGESTIONS.md risk #1). Now it determines whether absEval uses
annotation-based or body-based mu-elim. A correct annotation is essential
for recursive functions to type-check with abstract arguments.

### Test milestone status (Tests.lean §11)

| Test | Description | Status |
|------|-------------|--------|
| M1a | `addRec ⊑ SelfNat→SelfNat→Nat` | PASS |
| M1b | `addRec 0 3 = 3` (concrete) | PASS |
| M1c | `addRec 2 1` is a Nat (concrete) | PASS |
| **M1d** | **`addRec (abstract) (abstract) ⊑ Nat`** | **PASS ← NEW** |
| M2a | `mapArray` base case (concrete) | PASS |
| M3a | `appendArrays` base case (concrete) | PASS |
| M4a | `appendVec ⊑ T→Vec T→Vec T→Vec T` | FAIL (see below) |
| **M4b** | **`appendVec (abstract) (abstract) ⊑ Vec Nat`** | **PASS ← NEW** |
| **M4c** | **`appendVec` concrete ⊑ Vec Nat** | **PASS ← NEW** |

### M4a analysis

M4a (`appendVec ⊑ T→Vec T→Vec T→Vec T`) is the last remaining milestone.
It tests whether appendVec, as a RAW expression (not applied to any args),
has the right function type. This requires the subtype checker to handle
appendVec's body abstractly under binders, comparing it against the expected
return type.

M4b and M4c pass because the arguments are provided (either abstract or
concrete), so the annotation-based mu-elim can determine return types.
M4a fails because appendVec is compared as a function definition, which
goes through subCheckNF's lam-lam case, eventually reaching the body where
recursive calls need to type-check without applied arguments.

Possible approaches for M4a:
- The subtype checker's self-elim may need to use annotations similarly
- Or the mu-mu comparison rule needs enhancement
- Or appendVec's body evaluation under binders needs different handling

### What was completed in the mu migration

- [x] Replace fix+iota with mu in Syntax.lean
- [x] Update Eval.lean (concEval, absEval, concEvalS)
- [x] Update Subtyping.lean (mu_body, self-intro, self-elim, inferType)
- [x] Update Tests.lean (all fix→mu, all iota→mu)
- [x] Sorry Soundness.lean and Monotonicity.lean
- [x] Gut Closure.lean, delete SoundnessS.lean
- [x] Add abstract add tests (§9: Church-style, §10: Variant B)
- [x] Add milestone ladder (§11: M1-M4 toward appendVec)
- [x] **Annotation-based mu-elim in absEval (M1d, M4b, M4c passing)**

### Key findings

1. **The annotation field on mu is now load-bearing.** absEval uses it
   to determine return types for recursive mus, preventing divergence.
   For fix-like mus (annotation = function type), the annotation is used.
   For iota-like mus (annotation = Type), body unfolding is used instead.

2. **The subtype checker compensates for the evaluator.** absEval does NOT
   do type-directed evaluation. When it hits `app (var "n") arg` where n is
   abstract, it returns a stuck application. The subtype checker's
   `inferType` function does mu-elim to recover type information.

3. **Variant A (SelfNat = mu n Type Nat') works because the self variable
   is unused.** The mu is a trivial wrapper around Church Nat. mu-elim
   strips it off. This is enough for non-recursive abstract add.

4. **Variant B (MuNat, truly self-referential) still fails subtyping.**
   Self-intro substitution produces structurally different but semantically
   equal terms. This likely needs equi-recursive subtyping.

### What needs to happen next

- **M4a** is the last expected-fail milestone. See analysis above.
- Then: fill sorrys (5 total), stabilize definitions, prove soundness.
- See SUGGESTIONS.md for the full roadmap.

### Key files

| File | Status | Sorry count |
|------|--------|-------------|
| Syntax.lean | Done | 0 |
| Eval.lean | Done (annotation-based mu-elim) | 0 |
| Subtyping.lean | Done | 0 |
| Tests.lean | 126 tests (4 expected-fail milestones, 3 passed this session) | 0 |
| Soundness.lean | Sorry'd | 1 |
| Monotonicity.lean | Sorry'd | 4 |
| Closure.lean | Gutted | 0 |
| CounterexampleTest.lean | Done | 0 |
