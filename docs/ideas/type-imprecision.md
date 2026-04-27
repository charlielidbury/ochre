# Type imprecision in Och: sound but vague

**Status**: design analysis, 2026-04-27. No code changes; this
documents a property of Och's current typing relation, surfaced
during the engine-collapse refactor.

## Summary

Och's typing relation `⊑` is **technically sound** (well-typed
programs don't get stuck; types are preserved under reduction)
but **operationally imprecise** (a program can have type τ
without behaving like an inhabitant of τ in the intuitive sense).

This is not a violation of classical type soundness. It is a
weakness in how much the type system constrains program behavior.

## The distinction

Standard type soundness has two parts:

1. **Progress** — well-typed programs don't reach stuck states
   during evaluation; `eval(e)` returns a value or runs out of
   fuel, never `.error "stuck"`.
2. **Preservation** — if `e : τ`, then `eval(e) : τ`.

Och satisfies both. We have not found counter-examples to either.

What Och **does not** satisfy is the *practical* expectation that
a typed program behaves the way its type suggests. Specifically:

| Property | Status in Och |
|---|---|
| Progress | ✓ holds |
| Preservation | ✓ holds |
| `e : τ` constrains `e`'s observable behavior | ✗ very weak |

## Concrete witness

In `Std/Pair.lean`:

```
Pair  = λA:Type. λB:Type. λX:Type. λk:(A→B→X). X     -- the type
pair_ = λA. λB. λa. λb. λX. λk. k a b                 -- the value constructor
```

Both `pair_ Nat_ Nat_ one_ two_` and `Pair one_ two_` type-check
at `Pair Nat_ Nat_`. But operationally they diverge:

```
fst_ (pair_ Nat_ Nat_ one_ two_)  =>  one_   -- correct: extracts head
fst_ (Pair one_ two_)             =>  Type   -- "garbage": returns the universe
```

This is verifiable empirically (see `lean/Och/Std/Pair.lean`'s
strict-equality pins, and the discussion in
`docs/ideas/appendvec-investigation.md`). The type-checker accepts
both values at `Pair Nat_ Nat_`; concEval gives different runtime
results.

The system isn't lying about types — `Type ⊑ Pair Nat_ Nat_` does
not hold. What's happening is that `Pair one_ two_`, evaluated to
its WHNF `λX. λk:(one_ → two_ → X). X`, structurally matches the
shape of a Pair-typed lambda by the X-mediated covariance trick.
That makes it accepted via subCheckSubst, even though its body
is `X` rather than `k a b`.

## Why this happens — three contributing factors

### Refl is too permissive

`e ⊑ e` for every term. Combined with `Type : Type` (top), every
term is "well-typed at itself". Type expressions like `Nat_` and
`Pair Nat_ Nat_` thus serve as both **types** and **values of
themselves**. There's no syntactic distinction between "X is a
type" and "X is a value of some type".

### Structural subtype is shape-based, not behavior-based

The algorithm (`subCheckSubst`) compares two values by walking
their syntactic structure under fuel. It does not check that two
values *behave the same way* (operational equivalence). Two
lambdas with the same domain shape but different bodies (`λX. X`
vs `λX. k`) can satisfy `⊑` in cases where the body comparison
isn't strict enough to distinguish them.

### Type:Type erases the level distinction

In stratified DTT, the *type constructor* `Pair : Type → Type →
Type` and a *value of `Pair A B`* live at different universes.
You can't pass a `Nat` value where Pair expects a `Type`. In
Och, `Type:Type` flattens this — every value is also (trivially)
a Type via `S-Top`, so type-position arguments accept value-shaped
inputs.

## What this means in practice

A type annotation in Och is **descriptive**, not **prescriptive**.
It says "the structural subtype check accepts this", not "this
program will behave like an inhabitant of τ when run".

For programs whose constructors and projections line up
correctly (the standard `pair_` + `fst_`/`snd_` pattern), the
correspondence between types and behavior is clean.

For programs that exploit the structural-subtype permissiveness
(deliberately or accidentally) — like substituting `Pair` for
`pair_` and getting type-checked code that returns garbage — the
type system doesn't catch it.

## Where this came from

The discrepancy was hidden by:

- The previous `subCheckT = typeCheck || subCheck` wrapper, which
  used `typeCheck`'s bidirectional walk to catch some
  misuses early.
- Test pins phrased as `(concEval ...).isOk`, which only verified
  termination, not the actual computed values.
- Commented-out strict-equality tests (e.g.
  `Std/Array.lean:156-158`) that *would* have caught the
  divergence, disabled "for performance".

The engine-collapse refactor (2026-04-27) removed the `||`
wrapper and the test-strengthening pass uncommented the strict
pins, surfacing this property.

## How other systems avoid it

### Stratified universes (Coq classic, Lean classic)
`Type 0 : Type 1 : Type 2 ...`. Type constructors live at one
level; their inhabitants at the level below. No accidental
confusion between "type" and "value of that type". Cost: kills
`Type:Type`, which Och deliberately keeps.

### Built-in inductive datatypes (all mainstream DTT)
Pair / Nat / etc. are kernel primitives, not Church/Scott
encodings. The kernel knows the constructors and eliminators and
enforces the boundary. Cost: kernel becomes much larger; Och's
"pure λ-calculus + subtyping" pitch becomes "λ-calculus + 
inductive types + subtyping".

### Operational-equivalence subtype
Subtype includes definitional equality up to βιη-conversion, not
just structural shape match. Two values are subtype-related only
when their reduction behaviors agree. Cost: more complex
algorithmic implementation; some equivalences become undecidable
(though the standard βιη fragment is decidable).

### Refinement of Refl
Restrict `e ⊑ e` to "value-shaped" terms (lambdas with declared
domains, applied constructors, etc.). Type expressions used as
values would no longer auto-typecheck. This is essentially
syntactic stratification — distinguishes types from values without
adding universe levels. Cost: loses some flexibility (e.g., higher-
order polymorphism becomes harder to encode).

## Where Och's design currently sits

Och chose:

- Decidable structural subtype (algorithmic completeness)
- `Type : Type` (no universe stratification)
- Pure λ-calculus encoding (no kernel inductives)

The cost of these choices is the type imprecision documented
here. Operational soundness in the strong sense (typed programs
behave like their types) is sacrificed to keep these design
points.

## Mitigations short of redesign

These don't fix the underlying property but raise the cost of
hitting it:

1. **Strict equality tests over `.isOk` smoke tests.** Already
   done in the test-strengthening pass — `concEval e = concEval
   expected` instead of `(concEval e).isOk`. Catches divergence
   between intended and actual behavior at test time.

2. **Stuck-on-top/bot in concEval.** If `Type` or `Bot` ends up
   in a value position at runtime, concEval errors instead of
   returning silently. Catches the dramatic literal-leak cases
   (e.g. `fst_ (Pair one_ two_)`'s `Type` result).

3. **Documenting the encoding patterns that work.** The
   `pair_` + `fst_`/`snd_` pattern is operationally correct.
   Encodings that bypass it (substituting `Pair` for `pair_`
   directly) are the source of confusion. This is `Std/Pair.lean`'s
   docstring already, but the consequences could be more
   prominent.

4. **Restricting where type expressions can be used as values.**
   E.g., making `S-Top` (`v ⊑ Type`) one-directional — `Type`
   isn't a subtype of anything except itself. Already true; this
   is just emphasizing that the issue is upstream of `S-Top`,
   in `S-Refl`.

These mitigations are tactical. The deeper fix requires choosing
one of the four redesign directions above.

## Recommendation

For Och as a research vehicle for studying decidable subtyping
in dependent settings: **document and accept**. Type imprecision
is the price of decidability + Type:Type. Future research
directions (operational-equivalence subtype, kernel inductives)
remain open.

For Och as a practical programming language where types are
load-bearing specifications: **the four redesign directions are
the menu**. Decidable structural subtype alone is too weak.

The current Och codebase's audit, with strict equality tests,
guards against the dramatic failure modes during development.
The structural property remains.

## Pointers

- `lean/Och/Std/Pair.lean` — the docstring already discusses
  `fst_ p : Type, not : A`. Extend or cross-reference here.
- `docs/ideas/appendvec-investigation.md` — the empirical
  finding that triggered this analysis.
- `docs/ideas/engine-collapse.md` — the broader refactor that
  surfaced the issue.
- `lean/Och/Subtyping.lean` — the declarative `Subtype'`
  relation. The `S-Refl` and `S-Top` rules are where the
  permissiveness lives.
