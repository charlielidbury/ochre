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

`lake build` passes with **4 sorry warnings** (3 in Monotonicity.lean, 1 in
Soundness.lean). All tests pass (126 tests, including 7 expected-fail
milestones that will flip to passing as the system improves).

### What's working

- mu replaces fix+iota throughout the codebase
- Concrete eval unrolls mu (like fix)
- Abstract eval normalizes body under binder (like iota)
- Self-intro and self-elim work in subCheckNF
- `inferType` in the subtype checker does mu-elim on stuck applications
- **Abstract `add` (non-recursive, Church-style) with SelfNat passes** (§9)
- **Recursive add (mu-as-fix) with concrete args passes** (M1a-c in §11)
- **mapArray and appendArrays base cases pass concretely** (M2a, M3a in §11)

### What's NOT working (expected-fail tests in Tests.lean §10-§11)

- **M1d: `addRec (abstract) (abstract) ⊑ Nat`** — recursive add with
  abstract args. The body uses isZero for branching on an abstract nat,
  which produces a stuck application that doesn't reduce.

- **M4a-c: appendVec** — the north star. Fails for both abstract and
  concrete args. Depends on appendArrays recursion working.

- **Variant B (§10): `zero_mu ⊑ MuNat`** — truly self-referential Nat
  (Cedille-style). Self-intro substitution produces structurally different
  terms that are semantically equal. Needs equi-recursive subtyping.

## Known risks and open questions

These are observations, not certainties. Investigate before acting on them.

1. **The annotation field on mu is currently dead code.** It is never
   inspected by absEval, never compared by subCheckNF (even mu-mu!), and
   not checked by WellTyped. For fix-like mus the intended meaning seems
   to be "the type of this expression." For iota-like mus it's always
   `.type` (carrying no information). It's unclear whether a single
   invariant covers both uses. Making annotations load-bearing may be
   needed for recursive types (Victor's trick prevents divergent unfolding),
   but it's not yet clear what invariant they should satisfy.

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

**Milestone M1d** is the immediate next target: `addRec` (recursive add via
mu) with abstract SelfNat arguments should produce something ⊑ Nat. This
currently fails because the body's isZero branching produces a stuck
application on abstract input. Possible approaches (investigate, don't
assume any will work):

- Type-directed evaluation: change Env to carry types alongside values, so
  absEval can do mu-elim on stuck variables in the app case
- Smarter `inferType` in the subtype checker to handle deeper stuck chains
- Partitioning: when absEval encounters a Church-encoded branch on an
  abstract value, split into cases (zero vs succ). This is mentioned in
  och-spec.md §4.2.5 but not yet implemented.
- Something else entirely — the right fix may not be obvious until you
  understand exactly where the stuck application occurs

**After M1d**, the path is:
- M2: mapArray with recursive case (not just base case)
- M3: appendArrays with recursive case
- M4a-c: appendVec — the north star

### Phase 2: Stabilise definitions

Once milestone tests pass (or you understand exactly why they can't):

- [ ] Resolve the annotation question (load-bearing or remove it)
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
