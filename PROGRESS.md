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

### Recent changes (2026-04-01, agent ochre-lean-20260401-192428)

**Domain normalization in subCheckNF: M4a flipped (appendVec north star!)**

The root cause of M4a's failure: absEval deliberately does NOT normalize
lambda domains (to preserve monotonicity). This means domains like
`Vec' (var "T")` remain as beta-redexes `app (lam "T" ...) (var "T")`
rather than being reduced to `lam "X" .type (lam "k" ... X)`.

When subCheckNF compares appendVec's body against `Vec T`, it encounters
stuck applications like `(v1 (Vec T)) (lam n1. ...)`. The `inferType`
function tries to determine the type of this application by looking up
v1's domain from the context. But the domain is an unreduced beta-redex
(an `.app`, not a `.lam`), so inferType's pattern match on `.lam` fails.

**The fix** (Subtyping.lean): added `normalizeDomain`, a helper that
normalizes domain expressions using absEval with context variables as
neutrals. In the lam-lam case of subCheckNF, domains are now normalized
before being added to the inferType context:

```lean
private def normalizeDomain (fuel : Nat) (ctx : List (Name × Expr)) (dom : Expr) : Expr :=
  let env : Env := ctx.map fun (n, _) => (n, .var n)
  match absEval fuel env dom with
  | some d => d
  | none => dom
```

This is safe because:
1. It only affects subCheckNF's internal type inference, not absEval's behavior
2. The monotonicity concern (why absEval doesn't normalize domains) doesn't
   apply to the subtype checker's context
3. The normalization uses context variables as neutrals, matching how
   subCheckNF already treats bound variables

### ALL M1-M4 milestones now PASSING

| Test | Description | Status |
|------|-------------|--------|
| M1a | `addRec ⊑ SelfNat→SelfNat→Nat` | PASS |
| M1b | `addRec 0 3 = 3` (concrete) | PASS |
| M1c | `addRec 2 1` is a Nat (concrete) | PASS |
| M1d | `addRec (abstract) (abstract) ⊑ Nat` | PASS |
| M2a | `mapArray` base case (concrete) | PASS |
| M3a | `appendArrays` base case (concrete) | PASS |
| **M4a** | **`appendVec ⊑ T→Vec T→Vec T→Vec T`** | **PASS ← NEW** |
| M4b | `appendVec (abstract) (abstract) ⊑ Vec Nat` | PASS |
| M4c | `appendVec` concrete ⊑ Vec Nat | PASS |

### Remaining expected-fail tests

- **Variant B (§10):** `zero_mu ⊑ MuNat` and `add_mu ⊑ MuNat→MuNat→MuNat`.
  These are truly self-referential Nat (Cedille-style) which need
  equi-recursive subtyping. Not blocking the current milestone.

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
- [x] **Domain normalization in subCheckNF (M4a passing)**

### Key findings

1. **The annotation field on mu is load-bearing.** absEval uses it
   to determine return types for recursive mus, preventing divergence.
   For fix-like mus (annotation = function type), the annotation is used.
   For iota-like mus (annotation = Type), body unfolding is used instead.

2. **The subtype checker compensates for the evaluator.** absEval does NOT
   do type-directed evaluation. When it hits `app (var "n") arg` where n is
   abstract, it returns a stuck application. The subtype checker's
   `inferType` function does mu-elim to recover type information.

3. **Domains need normalization in the subtype checker.** absEval does not
   normalize lambda domains (to preserve monotonicity). But subCheckNF's
   inferType needs domains in normal form to pattern-match on them. The
   `normalizeDomain` helper resolves this by normalizing domains before
   adding them to the inferType context.

4. **Variant A (SelfNat = mu n Type Nat') works because the self variable
   is unused.** The mu is a trivial wrapper around Church Nat. mu-elim
   strips it off. This is enough for non-recursive abstract add.

5. **Variant B (MuNat, truly self-referential) still fails subtyping.**
   Self-intro substitution produces structurally different but semantically
   equal terms. This likely needs equi-recursive subtyping.

### What needs to happen next

**Phase 1 is COMPLETE.** All M1-M4 milestones pass. The definitions are
expressive enough for abstract appendVec with the mu primitive.

**Next priorities (Phase 2-3):**
- Decide evaluator vs subtype checker architecture (risk #2 in SUGGESTIONS.md)
- Fill the 5 sorrys (4 Monotonicity, 1 Soundness)
- Consider whether `normalizeDomain` needs to be reflected in the proof
  (it changes subCheckNF's behavior, so monotonicity/soundness proofs
  must account for domain normalization)
- Get Variant B working if needed for Scott encoding (Phase 4)

### Key files

| File | Status | Sorry count |
|------|--------|-------------|
| Syntax.lean | Done | 0 |
| Eval.lean | Done (annotation-based mu-elim) | 0 |
| Subtyping.lean | Done (domain normalization) | 0 |
| Tests.lean | All milestones passing, Variant B expected-fail | 0 |
| Soundness.lean | Sorry'd | 1 |
| Monotonicity.lean | Sorry'd | 4 |
| Closure.lean | Gutted | 0 |
| CounterexampleTest.lean | Done | 0 |
