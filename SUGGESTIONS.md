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

## CRITICAL: The soundness theorem is vacuously true for mu programs

**This is the most important issue in the project right now.**

The soundness theorem (`soundness_gen` in Soundness.lean) is sorry-free,
but its `WellTyped` precondition is **unsatisfiable** for any program that
uses ascriptions with mu types. For example, `(unit' : SelfNat)` requires
`SubtypeCore (absEval unit') (absEval SelfNat)`, but `absEval unit'` is a
lambda and `absEval SelfNat` is a mu — no `SubtypeCore` constructor can
relate them (SubtypeCore has no `self_intro`).

This means the theorem holds vacuously: `False → anything`. It says nothing
useful about programs that use self-types, which is most of what Och exists
to verify.

**Root cause:** Previous agents switched WellTyped from `Subtype'` (which
has `self_intro`) to `SubtypeCore` (which doesn't) to eliminate a hard
sorry. Each trade-off was locally reasonable, but the accumulation made
WellTyped unsatisfiable. Nobody tested whether WellTyped could be
satisfied for concrete programs — only `subCheck` (the decidable checker)
was tested.

**The fix (Phase 5 below):** Replace `SubtypeCore` in WellTyped with
`subCheckNF` (the decidable checker). This makes WellTyped:
1. **Decidable** — testable via `native_decide`
2. **Satisfiable** — `subCheckNF` already accepts the milestone programs
3. **Testable** — add witness tests that construct WellTyped for real programs

The hard part: the soundness proof currently uses `SubtypeCore` properties
(lam_rhs_shape, transitivity). With `subCheckNF = true`, the proof needs
lemmas about what `subCheckNF` guarantees. This is "checker soundness" —
proving that when the checker accepts, the evaluators are safe.

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

### Phase 5: Non-vacuous soundness (THE PRIORITY)

**This is more important than Phase 4.** A proven-sound system that covers
real programs is the whole point of Och. Scott encoding without soundness
is just an interpreter.

The goal: the soundness theorem should be non-vacuously true for the
milestone programs (M1-M4, Variant B). Concretely, we need witness tests:

```lean
-- These must compile (not just subCheck — actual WellTyped witnesses):
example : WellTyped testFuel [] (app addRec (asc unit' SelfNat)) := by native_decide
example : WellTyped testFuel [] (app (app addRec (asc unit' SelfNat)) (asc unit' SelfNat)) := by native_decide
```

**Approach:**

1. **Replace SubtypeCore in WellTyped's asc case with `subCheckNF`.**
   Instead of `SubtypeCore σ τ'` (unprovable for mu), use
   `subCheckNF fuel ctx σ τ' = true` (decidable, already works for mu).
   This makes WellTyped decidable and testable via `native_decide`.

2. **Add witness tests.** For each milestone test (M1-M4), add a
   corresponding `WellTyped` witness. If WellTyped becomes unsatisfiable
   again, a witness test breaks. This is the canary.

3. **Prove soundness with the new WellTyped.** The soundness proof
   currently uses SubtypeCore properties extracted from WellTyped:
   - `SubtypeCore.lam_rhs_shape` (lambda inversion)
   - `SubtypeCore.trans` (transitivity)
   - Direct case analysis on SubtypeCore constructors

   With `subCheckNF = true` instead, the proof needs "checker soundness"
   lemmas. The key lemma is roughly:
   ```
   subCheckNF fuel ctx a b = true →
     ∀ γ, EnvConsistent γ ctx →
       ∀ v, concEval fuel γ a = some v →
         ∃ τ, absEval fuel ctx b = some τ ∧ SubtypeCore v τ
   ```
   This is the semantic content: if the checker says a ⊑ b, then
   concrete evaluation of a produces values that subtype abstract
   evaluation of b. This may require a richer relation than SubtypeCore
   (possibly with equi-recursive unfolding).

   **This is the hardest part.** It may require restructuring SubtypeCore
   or introducing a new semantic relation. Sorry freely — getting the
   statement right matters more than filling proofs.

4. **Alternative (simpler but weaker):** Instead of full checker soundness,
   prove specific lemmas about subCheckNF that the soundness proof needs:
   - If `subCheckNF` says `a ⊑ lam x d b`, then `a` is a lam (shape lemma)
   - If `subCheckNF` says `a ⊑ b` and `b ⊑ c`, then `a ⊑ c` (transitivity)
   These are weaker than full checker soundness but might suffice for the
   soundness proof.

**Do not skip the witness tests.** Even if the proof has sorrys, the
witness tests ensure WellTyped is satisfiable. A sorry'd proof with
satisfiable WellTyped is worth more than a sorry-free proof with vacuous
WellTyped.

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
