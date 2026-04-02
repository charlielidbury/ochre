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
soundness_gen is sorry'd (needs "checker soundness" lemma — see Phase 5).

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

### Phase 1: Get the milestone tests passing (no proofs) ✓ COMPLETE

All M1-M4 milestones now pass. Key changes that made this work:
1. **Annotation-based mu-elim** (absEval): for fix-like mus, use the
   annotation to determine return types instead of unfolding the body
   (which diverges). Flipped M1d, M4b, M4c.
2. **Domain normalization** (subCheckNF): absEval doesn't normalize domains,
   so `Vec' T` stays as a beta-redex. `normalizeDomain` reduces it before
   adding to inferType's context. Flipped M4a.

### Phase 2: Stabilise definitions

Once milestone tests pass (or you understand exactly why they can't):

- [x] Resolve the annotation question → load-bearing (used by absEval)
- [ ] Decide evaluator vs subtype checker architecture
- [x] Get Variant B working → equi-recursive self-intro + seen set

### Phase 3: Proofs ✓ COMPLETE (but see Phase 5 — soundness is vacuous)

- [x] Prove absEval_mono — SORRY-FREE
- [x] Prove soundness_gen — SORRY-FREE (all 4 body-unfold sorrys eliminated)
- [ ] Rebuild Closure.lean if needed

**WARNING:** Phase 3 achieved zero sorrys, but the soundness theorem is
vacuously true for mu programs. See "CRITICAL" section above. Phase 5
addresses this.

### Phase 4: Recursive types and Scott encoding

- [ ] Type-level mu for recursive types
- [ ] Scott-encoded Nat (nested mus)
- [ ] Full induction via mu-as-fix

### Phase 5: Non-vacuous soundness

**Step 1 ✓ COMPLETE:** WellTyped is now Bool-valued with subCheckNF.
11 witness tests prove satisfiability. soundness_gen is sorry'd.

**Step 2 (THE PRIORITY): Prove soundness_gen with Bool-valued WellTyped.**

The sorry in soundness_gen is in the asc case. The proof needs:

```
subCheckNF fuel Γ [] σ τ' = true →
  SubtypeCore v σ → SubtypeCore v τ'
```

This is "checker transitivity": if subCheckNF says σ ⊑ τ', and the IH
gives SubtypeCore v σ, then SubtypeCore v τ'.

**Approaches (increasing difficulty):**

(a) **Specific shape lemmas** about subCheckNF:
    - If subCheckNF says a ⊑ lam x d b, then a is a lam (shape)
    - Checker transitivity: subCheckNF a b = true → SubtypeCore v a → SubtypeCore v b
    These might suffice for the asc case without full checker soundness.

(b) **Full checker soundness:**
    ```
    subCheckNF fuel ctx a b = true →
      ∀ γ, EnvConsistent γ ctx →
        ∀ v, concEval fuel γ a = some v →
          ∃ τ, absEval fuel ctx b = some τ ∧ SubtypeCore v τ
    ```
    Requires relating subCheckNF's equi-recursive unfolding to SubtypeCore.

(c) **Richer semantic relation:** Replace SubtypeCore in soundness_gen's
    output with a relation that supports equi-recursive unfolding.
    Then the asc case composes directly. Requires re-proving all other cases.

(d) **Step-indexed logical relations:** The standard PL approach. Replace
    syntactic SubtypeCore with semantic V(fuel, τ). Major infrastructure change.

**Also needed (mu-app annotation consistency):** WellTyped's mu-app case
was simplified to only check WellTyped of the sub-term that absEval
evaluates. The previous version had annotation consistency (body result ⊑
annotation result) but required matching binder names. When proving
soundness_gen, the mu-app annotation path needs this consistency — it may
need to be re-added to WellTyped (with subCheckNF, no binder name matching).

**Important:** The witness tests are the canary. Never weaken WellTyped
without checking these tests still pass. A sorry'd proof with satisfiable
WellTyped is worth more than a sorry-free proof with vacuous WellTyped.

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
