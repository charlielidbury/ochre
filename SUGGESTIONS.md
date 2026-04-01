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

## Current state (as of 2026-04-01)

`lake build` passes with **5 sorry warnings** (4 in Monotonicity.lean, 1 in
Soundness.lean). All tests pass (126 tests, including 4 expected-fail
milestones).

### What's working

- mu replaces fix+iota throughout the codebase
- Concrete eval unrolls mu (like fix)
- Abstract eval normalizes body under binder (like iota)
- **Annotation-based mu-elim in absEval** — when a recursive mu is applied,
  absEval uses the annotation (if it's a lambda) to determine the return
  type, preventing divergence. Falls back to body unfolding for self-types.
- Self-intro and self-elim work in subCheckNF
- `inferType` in the subtype checker does mu-elim on stuck applications
- **Abstract `add` (non-recursive, Church-style) with SelfNat passes** (§9)
- **Recursive add (mu-as-fix) with both concrete and abstract args passes** (M1a-d in §11)
- **mapArray and appendArrays base cases pass concretely** (M2a, M3a in §11)
- **appendVec with concrete and abstract args passes** (M4b, M4c in §11)

### What's NOT working (expected-fail tests in Tests.lean §10-§11)

- **M4a: `appendVec ⊑ T→Vec T→Vec T→Vec T`** — the raw function type check.
  M4b-c pass (with applied args) but M4a fails because subCheckNF compares
  the body under binders where annotation-based mu-elim doesn't help.

- **Variant B (§10): `zero_mu ⊑ MuNat`** — truly self-referential Nat
  (Cedille-style). Self-intro substitution produces structurally different
  terms that are semantically equal. Needs equi-recursive subtyping.

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
   checker's `inferType` does mu-elim to recover type information. This
   works for current passing tests but may not scale. The alternative
   (making absEval type-directed by changing Env to carry types) is a bigger
   change. It's not obvious which approach is better — let the failing tests
   guide the decision.

3. **Do we need Variant B (truly self-referential Nat)?** Variant A (trivial
   self-type wrapper, §9) may be expressive enough for everything through
   appendVec. Variant B matters for Scott encoding (Phase 4). Don't assume
   it's blocking — try the next milestone with Variant A first.

## Roadmap

### Phase 1: Get the milestone tests passing (no proofs)

Tests.lean §11 contains a ladder of milestone tests (M1-M4). Each is a
`native_decide` test marked `= false` (expected fail). The goal is to make
definition changes that flip these to `= true`. When `lake build` breaks
because an expected-fail started passing, that's SUCCESS — flip it.

Existing tests (§1-§9) must continue to pass. They pin expressiveness.
Changing definitions is expected and encouraged — that's the whole point
of this phase.

**M1d, M4b, M4c are now PASSING** thanks to annotation-based mu-elim
(see PROGRESS.md for details).

**M4a** is the remaining target: `appendVec ⊑ T→Vec T→Vec T→Vec T`.
This tests whether the raw appendVec expression (not applied to args)
has the right function type. It fails because subCheckNF compares the
function body under binders, where recursive calls in appendArrays'
need to type-check without the annotation-based shortcut (which only
fires in absEval's app case, not in subCheckNF's body comparison).

Possible approaches for M4a:
- Enhance subCheckNF's self-elim to use annotations for recursive mus
- Enhance the mu-mu comparison rule to consider annotations
- Add type-directed evaluation specifically for subCheckNF's context

**After M4a**, the remaining milestones are:
- M2b-c: mapArray recursive case (not yet written)
- M3b-c: appendArrays recursive case (not yet written)

### Phase 2: Stabilise definitions

Once milestone tests pass (or you understand exactly why they can't):

- [x] Resolve the annotation question → load-bearing (used by absEval)
- [ ] Decide evaluator vs subtype checker architecture
- [ ] Get Variant B working if needed for later phases

### Phase 3: Proofs

Only after definitions are stable and tests pass.

- [ ] Prove absEval_mono, soundness_gen, and related lemmas
- [ ] Rebuild Closure.lean if needed

### Phase 4: Recursive types and Scott encoding

- [ ] Type-level mu for recursive types
- [ ] Scott-encoded Nat (nested mus)
- [ ] Full induction via mu-as-fix

## Design principles

- **Tests before proofs.** A failing test is more informative than a stuck
  proof. If you're choosing between "fill a sorry" and "write a test for the
  next milestone," write the test.

- **Definitions before proofs.** Getting the definitions right is more
  valuable than proving things about wrong definitions. If a proof isn't
  going through, consider whether the definition needs to change.

- **Change definitions freely in Phase 1.** The whole point is to find the
  right definitions. Existing tests catch regressions.

- **One primitive for self-reference.** If you find yourself wanting a second
  self-reference mechanism, stop and think about whether mu can do it.

- **Tests are sacred.** Existing tests pin expressiveness. Don't weaken them.
  Adding new tests is encouraged.

- **Sorry freely, compile always.** `lake build` must pass.

- **Read merge-fix-iota.md.** It is the design document. The worked example
  at the bottom shows what the typing rules need to look like.
