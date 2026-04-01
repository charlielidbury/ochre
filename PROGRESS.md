# Progress

## Current state: mu experiment (branch claude/mu-experiment)

We have replaced `fix` (recursion) and `iota` (self types) with a single
unified primitive `mu` (self-reference). See `docs/ideas/merge-fix-iota.md`
for the full design rationale, and **SUGGESTIONS.md** for the current
roadmap and strategy.

### Build status

`lake build` passes with **4 sorry warnings**:
- Monotonicity.lean: 3 (absEval_mono [2 app-mu subcases], absEval_mono_trans,
  absEval_succeeds_envsub)
- Soundness.lean: 1 (soundness_gen)

### Recent changes (2026-04-01, agent ochre-lean-20260401-181503)

1. **Annotation non-normalization:** absEval no longer normalizes mu
   annotations, just like lambda domains are not normalized. This is
   needed for monotonicity: mu_body requires same annotation, and
   normalizing in different envs would produce different annotations.

2. **absEval_mono partially proved:** All cases handled except the app-mu
   subcase (mu-elim). The blocker: substitution-based mu-elim creates
   different expressions in each env (`body₁.subst x (mu x ann body₁)` vs
   `body₂.subst x (mu x ann body₂)`), requiring a substitution lemma for
   Subtype' that doesn't hold because lam_body/mu_body require identical
   domains/annotations. Env extension was tried but breaks tests (recursive
   mu needs re-evaluation, not just lookup).

126 tests in Tests.lean, all compile. 7 are expected-fail milestones
(marked `= false`) that will flip as the system improves.

### Test milestone status (Tests.lean §11)

| Test | Description | Status |
|------|-------------|--------|
| M1a | `addRec ⊑ SelfNat→SelfNat→Nat` | PASS |
| M1b | `addRec 0 3 = 3` (concrete) | PASS |
| M1c | `addRec 2 1` is a Nat (concrete) | PASS |
| **M1d** | **`addRec (abstract) (abstract) ⊑ Nat`** | **FAIL — next target** |
| M2a | `mapArray` base case (concrete) | PASS |
| M3a | `appendArrays` base case (concrete) | PASS |
| M4a | `appendVec ⊑ T→Vec T→Vec T→Vec T` | FAIL |
| M4b | `appendVec (abstract) (abstract) ⊑ Vec Nat` | FAIL |
| M4c | `appendVec` concrete ⊑ Vec Nat | FAIL |

### What was completed in the mu migration

- [x] Replace fix+iota with mu in Syntax.lean
- [x] Update Eval.lean (concEval, absEval, concEvalS)
- [x] Update Subtyping.lean (mu_body, self-intro, self-elim, inferType)
- [x] Update Tests.lean (all fix→mu, all iota→mu)
- [x] Sorry Soundness.lean and Monotonicity.lean
- [x] Gut Closure.lean, delete SoundnessS.lean
- [x] Add abstract add tests (§9: Church-style, §10: Variant B)
- [x] Add milestone ladder (§11: M1-M4 toward appendVec)

### Key findings from analysis (2026-04-01)

1. **The annotation field on mu is dead code.** Never inspected by absEval,
   never compared by subCheckNF (even mu-mu — both annotations are bound to
   underscore-prefixed variables), not checked by WellTyped. This needs to
   be resolved but is not blocking Phase 1.

2. **The subtype checker compensates for the evaluator.** absEval does NOT
   do type-directed evaluation. When it hits `app (var "n") arg` where n is
   abstract, it returns a stuck application. The subtype checker's
   `inferType` function does mu-elim to recover type information. This is
   how `addSelfNat ⊑ SelfNat→SelfNat→Nat` passes — inferType looks up n's
   type (SelfNat = mu), unfolds it to Nat', and infers the return type.

3. **Variant A (SelfNat = mu n Type Nat') works because the self variable
   is unused.** The mu is a trivial wrapper around Church Nat. mu-elim
   strips it off. This is enough for non-recursive abstract add.

4. **Variant B (MuNat, truly self-referential) fails subtyping.** Self-intro
   substitution produces structurally different but semantically equal terms.
   This likely needs equi-recursive subtyping or annotation comparison.

### What needs to happen next

See SUGGESTIONS.md for the full roadmap. The immediate target is **M1d**:
getting recursive add with abstract arguments to work.

### Key files

| File | Status | Sorry count |
|------|--------|-------------|
| Syntax.lean | Done | 0 |
| Eval.lean | Done | 0 |
| Subtyping.lean | Done | 0 |
| Tests.lean | 126 tests (7 expected-fail milestones) | 0 |
| Soundness.lean | Sorry'd | 1 |
| Monotonicity.lean | Sorry'd | 3 |
| Closure.lean | Gutted | 0 |
| CounterexampleTest.lean | Done | 0 |
