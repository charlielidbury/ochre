# The mu experiment

## Background: what happened and why we're here

Och previously had two separate self-reference primitives:
- `fix` — general recursion (recursive functions)
- `iota` — self types (dependent elimination)

We discovered these are the same thing. In Och's "terms and types are the
same thing" framework, both express self-reference. The only difference is
how *determined* the self-reference is — and that's already handled by the
concrete/abstract evaluation split. See `docs/ideas/merge-fix-iota.md` for
the full analysis (READ THIS FIRST — it is the design document for this
experiment).

The unified primitive is `mu`:

```lean
| mu : Name → (ann : Expr) → (body : Expr) → Expr
```

`mu (x : T). body` means "the thing being defined can refer to itself as x,
and its annotation is T."

- **Concrete eval:** unroll — `body[x := mu x T body]` (like fix)
- **Abstract eval:** normalize body under binder, return `mu x T' body'` (like iota)
- **Subtyping:** mu-mu compares bodies covariant; self-intro/elim unfold one level

## North Star: abstract appendVec

The goal is getting `appendVec` working end-to-end with **abstract** arguments
(`n : Nat, m : Nat`). Och is useless without this — a type system that can
only verify concrete computations adds nothing over an evaluator.

## Strategy: tests first, proofs last

Proofs are expensive and fragile — they break whenever definitions change.
The definitions are NOT yet stable (annotation semantics are unresolved,
the env type may need to change, subtyping rules may evolve). So the strategy
is:

1. **Get appendVec working as native_decide tests** — validate that the
   definitions are expressive enough by writing executable tests, not proofs.
   Every milestone below is a test that either passes or doesn't.
2. **Only then prove soundness/monotonicity** — once the tests pass and the
   definitions have stabilised, the proofs confirm what we already believe.

This brings risk forward: if the definitions can't express appendVec, we find
out in days (a failing test), not weeks (a stuck proof).

**Do not prioritise filling sorrys over getting tests to pass.** A system
with 10 sorrys and a passing appendVec test is in a far better position than
a system with 0 sorrys that can't express dependent elimination.

## Current state (as of 2026-04-02)

`lake build` passes with **ZERO warnings** (no sorrys, no unused variables).
**All M1-M4 milestone tests pass.** Phases 1, 3, and Variant B are complete.
**No expected-fail tests remain.**

### What's working

- mu replaces fix+iota throughout the codebase
- Concrete eval unrolls mu (like fix)
- Abstract eval normalizes body under binder (like iota)
- **Annotation-based mu-elim in absEval** — when a recursive mu is applied,
  absEval uses the annotation (if it's a lambda) to determine the return
  type, preventing divergence. Falls back to body unfolding for self-types.
- **Domain normalization in subCheckNF** — domains are normalized before
  adding to inferType's context, so `Vec' T` is recognized as a lambda.
- **Equi-recursive self-intro in subCheckNF** — self-intro substitutes the
  mu type itself (not the value), enabling Variant B (truly self-referential
  Nat). Coinductive `seen` set prevents divergence on circular unfolding.
- Self-intro and self-elim work in subCheckNF
- `inferType` in the subtype checker does mu-elim on stuck applications
- **All milestone tests pass:** M1a-d, M2a, M3a, M4a-c
- **Abstract `add` (non-recursive, Church-style) with SelfNat passes** (§9)
- **Recursive add (mu-as-fix) with both concrete and abstract args passes** (M1a-d)
- **appendVec as raw function AND applied to abstract args passes** (M4a-c)
- **Variant B passes:** `zero_mu ⊑ MuNat` and `add_mu ⊑ MuNat→MuNat→MuNat` (§10)

## RESOLVED: WellTyped is now non-vacuous (Phase 5, Step 1 complete)

WellTyped was previously Prop-valued with SubtypeCore in the asc case.
SubtypeCore lacks self_intro, making WellTyped unsatisfiable for any
program with `(e : mu_type)` ascriptions — the soundness theorem was
vacuously true.

**Now fixed:** WellTyped is Bool-valued with `subCheckNF` in the asc case.
11 witness tests prove WellTyped is satisfiable for milestone programs.
soundness_gen is sorry'd (needs "checker soundness" lemma — see Phase 4).

**Architecture:** The intended user-facing type checker is
`WellTyped fuel [] e && subCheck fuel e τ`. `WellTyped` recursively checks
that all ascriptions are sound (e.g., rejects `(b : not b)` inside a
lambda). `subCheck` checks that the overall expression has the declared
type. Both are decidable (Bool-valued). Once Phase 4 proves soundness_gen,
the full guarantee is: if both return true, then `concEval(e) ⊑ absEval(τ)`.

**Key finding:** `(.asc unit' SelfNat)` is NOT a valid test — unit' (Church
unit) is not in SelfNat (Church Nat). Use `(.asc zero' SelfNat)` instead.
The ascription witness must actually inhabit the declared type.

## Known risks and open questions

These are observations, not certainties. Investigate before acting on them.

1. **The annotation field on mu is now load-bearing (RESOLVED).**
   absEval uses the annotation to determine return types for recursive mus:
   when `app (mu x ann body) aVal` and ann is a lambda, it beta-reduces
   ann with aVal instead of unfolding the body (which would diverge).
   For iota-like mus (ann = Type), it falls back to body unfolding.
   This resolved M1d, M4b, and M4c. The annotation is still NOT compared
   by subCheckNF's mu-mu rule or checked by WellTyped — these may need
   updating when proofs resume.

2. **The subtype checker compensates for the evaluator.** absEval does NOT
   do type-directed evaluation — stuck applications stay stuck. The subtype
   checker's `inferType` does mu-elim to recover type information, and
   `normalizeDomain` resolves beta-redexes in domains. This architecture
   works for all milestones through appendVec. Whether it scales to Phase 4
   (Scott encoding) is an open question.

3. **Variant B now works (RESOLVED).** Equi-recursive self-intro
   (substituting the mu type, not the value) resolved `zero_mu ⊑ MuNat`
   and `add_mu ⊑ MuNat→MuNat→MuNat`. The coinductive `seen` set prevents
   divergence. Phase 4 (Scott encoding) is now unblocked.

## Roadmap

Phases are in priority + dependency order. Do the first incomplete phase.

### Phase 1: Milestone tests ✓ COMPLETE

All M1-M4 milestones pass. Variant B passes. See git history for details.

### Phase 2: Non-vacuous WellTyped ✓ STEP 1 COMPLETE

WellTyped is now Bool-valued with `subCheckNF` (was Prop with SubtypeCore).
11 witness tests prove satisfiability. soundness_gen is sorry'd.

**Architecture:** The intended user-facing type checker is
`WellTyped fuel [] e && subCheck fuel e τ`. `WellTyped` recursively checks
that all ascriptions are sound (e.g., rejects `(b : not b)` inside a
lambda). `subCheck` checks that the overall expression has the declared
type. Both are decidable (Bool-valued). Once Phase 4 proves soundness_gen,
the full guarantee is: if both return true, then `concEval(e) ⊑ absEval(τ)`.

### Phase 3: De Bruijn indices ← START HERE

**Why this is next:** Everything downstream needs substitution to be correct
and to have provable properties. The current `subst` in Syntax.lean is
explicitly not capture-avoiding ("WARNING: This naive implementation does
not handle capture"). This means:
- `subCheckNF` can give wrong answers on programs with shadowed variables
- Substitution lemmas (needed for checker soundness) are unprovable or false
- `concEvalS` soundness requires `SubtypeCore a b → SubtypeCore (e[x:=a]) (e[x:=b])`
  which needs correct substitution

De Bruijn indices fix all of these by construction:
- Substitution is correct (no variable names to capture)
- Alpha-equivalence is syntactic equality (no binder name issues)
- Substitution lemmas become provable
- The WellTyped binder name matching issue (y_ann == y_body) disappears

**Scope:** This is a mechanical refactor. Every file changes but the
semantics don't. Existing `native_decide` tests verify nothing breaks.

**Prep:** Delete dead code first (see `docs/ideas/simplification.md`) —
less code to refactor. Specifically: SubtypeTrans (~200 lines), EnvSub,
unused lemmas (lam_lhs_cases, lam_inv, mu_inv), Closure.lean stub.

**Steps:**
1. Change `Expr` to use de Bruijn indices (indices instead of `Name` for
   bound variables; free variables can stay as names or also become indices)
2. Update `subst`, `Env.lookup`, `absEval`, `concEval`, `concEvalS`
3. Update `subCheckNF`, `inferType`, `normalizeDomain`
4. Update `Subtype'`, `SubtypeCore` and all lemmas
5. Rewrite Tests.lean (hardest part — all the test terms need rebuilding)
6. Verify `lake build` passes and all tests (including witness tests) pass

**Estimated effort:** 2-3 agent sessions. The first session should do
Syntax.lean + Eval.lean + Tests.lean (get it compiling). Later sessions
fix proofs.

### Phase 4: Eliminate the 3 remaining sorrys in soundness_gen

**Current state:** soundness_gen has ~300 lines of proof with 3 targeted
sorrys (asc case + mu-app annotation path ×2). All other cases proved.

**THE FUNDAMENTAL BLOCKER: SubtypeCore is too weak as the output relation.**

The proposed "checker transitivity" lemma
`subCheckNF σ τ' = true → SubtypeCore v σ → SubtypeCore v τ'` is **FALSE**:
- SubtypeCore has no self_intro (can't relate lam to mu)
- SubtypeCore has no contra-domain lam_sub (lam_body needs same domain)
- Subtype' is also too weak (self_intro without substitution, adding lam_sub
  breaks Subtype'.trans, adding equi-recursive rules breaks structural induction)

**Recommended approach: change the output relation.** Options:

(a) **subCheckNF-based output** (most direct): State soundness as
    `subCheckNF fuel Γ [] v τ = true`. Requires "checker transitivity":
    `subCheckNF v σ = true → subCheckNF σ τ' = true → subCheckNF v τ' = true`.
    Hard but natural for subCheckNF. The non-asc cases need reproving but
    are straightforward (subCheckNF's `a == b` check handles reflexivity).

(b) **Coinductive subtyping relation** with lam_sub + equi-recursive mu
    rules. Lean 4 supports coinductives. Transitivity is also coinductive.
    Prove subCheckNF implies the coinductive relation. Then the asc case
    composes via coinductive transitivity.

(c) **Step-indexed logical relations** (standard PL approach). Replace
    SubtypeCore with semantic V(fuel, τ). Major infrastructure change but
    the most principled solution.

**Also needed (mu-app annotation path):** Re-add annotation consistency
to WellTyped using subCheckNF (no binder name matching needed). The proof
then chains through consistency. Still needs the output relation fix.

**Important:** The witness tests are the canary. Never weaken WellTyped
without checking these tests still pass.

### Phase 5: Drop concEval, prove soundness for concEvalS

**Depends on:** Phase 3 (substitution lemma), Phase 4 (soundness structure).

`concEval` (environment-based, normalizes under binders) exists only to be
structurally parallel to `absEval` for the soundness induction. It is NOT
the intended runtime — it eagerly evaluates lambda bodies, breaking
Church-encoded branching with recursion. `concEvalS` (substitution-based
CBV, lambdas are values) is the real runtime.

With de Bruijn indices, the substitution lemma becomes provable:
```
SubtypeCore a b → SubtypeCore (e[i:=a]) (e[i:=b])
```

This enables either:
- Proving `concEvalS` results refine `concEval` results (then soundness
  transfers)
- Proving soundness directly for `concEvalS` (simpler codebase, one
  evaluator instead of two)

### Phase 6: Scott encoding and recursive types

**Independent of Phases 3-5** (just tests, no proofs). Can be done any time.

- [ ] Type-level mu for recursive types
- [ ] Scott-encoded Nat (nested mus)
- [ ] Full induction via mu-as-fix
- [ ] Dependent elimination tests with abstract arguments

### Completed phases (for reference)

**Phase 1 (milestone tests):** All M1-M4 pass. Variant B passes.
Key techniques: annotation-based mu-elim, domain normalization,
equi-recursive self-intro + seen set.

**Phase 2 (non-vacuous WellTyped):** WellTyped is Bool-valued with
subCheckNF. 11 witness tests. soundness_gen sorry'd.

**Previous Phase 3 (proofs):** absEval_mono and soundness_gen were
sorry-free, but soundness was vacuously true for mu programs (WellTyped
used SubtypeCore which is unsatisfiable for mu ascriptions). The sorry-free
proofs are preserved in git (commit f7c40a1) for reference but should not
be treated as "done" — the theorem statement was wrong.

## Design principles

- **Tests before proofs.** A failing test is more informative than a stuck
  proof. If you're choosing between "fill a sorry" and "write a test for the
  next milestone," write the test.

- **Definitions before proofs.** Getting the definitions right is more
  valuable than proving things about wrong definitions. If a proof isn't
  going through, consider whether the definition needs to change.

- **Never weaken preconditions without a witness test.** If you change
  WellTyped (or any theorem precondition) to make a proof go through,
  you MUST also add or maintain a `native_decide` test that the
  precondition is satisfiable for a real program. A sorry-free proof
  with an unsatisfiable precondition is worthless — it's vacuously true.
  This is how Phase 3 produced a "proven" soundness theorem that says
  nothing about mu programs. **Do not repeat this mistake.**

- **One primitive for self-reference.** If you find yourself wanting a second
  self-reference mechanism, stop and think about whether mu can do it.

- **Tests are sacred.** Existing tests pin expressiveness. Don't weaken them.
  Adding new tests is encouraged.

- **Sorry freely, compile always.** `lake build` must pass.

- **Read merge-fix-iota.md.** It is the design document. The worked example
  at the bottom shows what the typing rules need to look like.
