# Make mu a proper self-type (iota)

## Status: Implemented (with known issues)

## Summary

Och's `mu` is intended to be a self-type (ι in the literature, as in
Cedille). Currently it is implemented as a standard equi-recursive type:
the self-reference is substituted with the mu expression (the type) rather
than with the value being checked. This document describes the bug, the
fix, and the expected consequences.

---

## Background: what is a self-type?

A self-type `ι x:A. B` is a type whose body `B` can refer to the value
`x` that inhabits it. The key rules (from Cedille):

- **Introduction:** `t : ι x:A. B`  iff  `t : B[x := t]`
- **Elimination:** from `t : ι x:A. B`, conclude `t : B[x := t]`

In both cases, the self-reference `x` is replaced by the **value** `t`,
not the type `ι x:A. B`.

This is what makes dependent elimination possible for Scott-encoded data.
For example, with dependent naturals:

```
dNat = μ dNat:Type.
  λP:(dNat → Type). λz:(P dzero). λs:(λpred:dNat. P (dsucc pred)). P dNat
```

When checking `dzero ⊑ dNat`, self-type intro should unfold to:

```
body[0 := dzero] = λP:(dNat→Type). λz:(P dzero). λs:(...). P dzero
                                                              ^^^^^
                                          return type is P of the VALUE
```

This means eliminating `dzero` with motive `P` gives return type `P dzero`
— the type depends on the specific value.

---

## The current bug

### In `subCheckNF` (Eval.lean, around line 252)

**Self-intro** (mu on the right):

```lean
| _, .mu _ann body =>
  let seen' := (a, b) :: seen
  let u := body.subst 0 b          -- ← BUG: substitutes b (the mu/type)
  ...                               --   should substitute a (the value)
```

`b` here is the mu expression (the type). It should be `a` (the value
being checked).

**Self-elim** (mu on the left, around line 260):

```lean
| .mu ann body, _ =>
  ...
  let u := body.subst 0 (.mu ann body)   -- ← same issue: substitutes the type
  ...                                     --   for self-type, should substitute
                                          --   the value (.mu ann body is already
                                          --   the value here, so this case may
                                          --   actually be correct — see notes)
```

For self-elim, the mu expression IS the value (since we're asking "does
this mu value subtype b?"), so substituting `.mu ann body` might already be
correct. But verify this carefully — the intent should be "substitute the
value that inhabits the type".

### In `Subtype'` (Subtyping.lean, around line 31)

```lean
| self_intro {a : Expr} {ann body : Expr} :
    Subtype' a body → Subtype' a (.mu ann body)
```

This says `a ⊑ body → a ⊑ μ ann body`. But self-type intro should be:
`a ⊑ body[0 := a] → a ⊑ μ ann body`. The current rule treats body as
already having no self-reference, which is incorrect for self-types.

---

## The fix

### 1. `subCheckNF` self-intro (Eval.lean ~line 256)

Change:
```lean
let u := body.subst 0 b
```
To:
```lean
let u := body.subst 0 a
```

### 2. `Subtype'` self_intro (Subtyping.lean ~line 31)

The structural rule needs to account for substitution. The correct
self-type intro rule would be something like:

```lean
| self_intro {a : Expr} {ann body : Expr} :
    Subtype' a (body.subst 0 a) → Subtype' a (.mu ann body)
```

Or it may need to be expressed differently depending on how the
soundness proof is structured. The key requirement: the body must
have the value substituted for its self-reference before comparing.

### 3. Verify self-elim

Check whether the self-elim case (mu on the left) needs analogous
changes. Since the mu expression is itself the value in that position,
it may already be correct.

### 4. Verify concEval

`concEval` substitutes `mu ann body` for the self-reference when
applying a mu:

```lean
| some (.mu ann body), some aVal =>
  concEval fuel (.app (body.subst 0 (.mu ann body)) aVal)
```

This is correct — at runtime the value IS the mu expression.

### 5. Verify absEval mu application

`absEval`'s mu application cases substitute the mu expression for
self-reference. Same reasoning as concEval — when applying a mu value,
the value IS the mu expression. Should be fine.

---

## Why this matters

### Dependent elimination actually works

With the fix, eliminating an abstract `n : dNat` with motive
`P : dNat → Type` gives return type `P n` (P of the specific value),
not `P dNat` (P of the type). This is the entire point of dependent
pattern matching on Scott-encoded data.

### May reduce or eliminate the need for `lenient` mode

The `lenient` flag in absEval exists because Church-encoded
type-level computations get stuck on abstract arguments. Example:
`Array_ n T = n Type Unit_ (λacc. Pair T acc)` is stuck when `n` is
abstract, so `fst_ arr` fails its domain check.

With proper self-types + dependent elimination, arrays could be defined
over `dNat` instead of Church nats. Eliminating abstract `n : dNat` with
an appropriate motive P would give return type `P n`, which absEval can
work with (P is a concrete lambda, so `P n` normalizes). This could
make the domain check succeed without lenient mode.

This is speculative — it depends on whether `P n` with abstract `n`
actually provides enough information for downstream checks. But it's
a plausible path toward removing the lenient workaround.

### Does NOT fix the `dzero ⊑ done_` bug

`DNat.lean` line 120 has a known bug where `dzero ⊑ done_` returns true
(should be false). This is **not** caused by the self-type issue. It's
caused by absEval normalizing `done_ = dsucc dzero` to `dNat` via the
annotation path (line ~192): since dsucc's annotation is `dNat → dNat`,
absEval returns `dNat` as the result type, losing the information that
it's specifically `dsucc dzero`. Then `dzero ⊑ dNat` is correctly true.
That's an absEval precision issue, orthogonal to this change.

---

## Testing strategy

**Empirically, the self-intro change alone does not produce any
observable difference in subCheckNF output.** Extensive testing with
various type constructions (self-referential types, covariant self-ref,
contravariant self-ref, dNat variants) showed identical results for
`body.subst 0 a` vs `body.subst 0 b`. The reasons:

- The seen-set cycle detection (line ~234) returns `true` when `(a,b)`
  is re-encountered, which masks differences that would otherwise
  appear after unfolding.
- Self-elim's annotation path often short-circuits before self-intro
  is reached.
- When self-intro IS reached, absEval normalizes the unfolded body,
  and the results are often structurally similar enough that subCheckNF
  gives the same answer.

**The real payoff requires combining this change with absEval changes.**
The main motivation — dependent elimination giving return type `P n`
instead of `P dNat` for abstract `n` — requires absEval to infer return
types from the type context when it encounters stuck applications of
abstract variables. The self-intro fix is a prerequisite (so the type
context records value-specific information), but it is not sufficient
alone.

The agent implementing this should:
1. Make the self-intro substitution change (`b` → `a`)
2. Extend absEval to use `inferType` (or similar) to determine return
   types for stuck applications of abstract variables, using the
   value-specific types now available from self-type unfolding
3. Write tests for dependent elimination on abstract dNat values —
   e.g., a function that eliminates an abstract `n : dNat` with a
   motive and checks that the result type is `P n` (specific to the
   value), enabling downstream domain checks to succeed without
   lenient mode

---

## Risks and things to watch

1. **Soundness proofs.** The existing Lean proofs in Eval.lean and
   Soundness.lean assume equi-recursive unfolding. Changing to self-type
   substitution will break them. The proofs may need significant
   rework — self-type intro with value substitution creates more
   complex recursive proof obligations.

2. **Termination of subCheckNF.** With equi-recursive unfolding, the
   `seen` set tracks `(a, b)` pairs to break cycles. With self-type
   substitution, the unfolded term `body[0 := a]` may be structurally
   larger than before (since `a` could be a large expression). Verify
   that the seen-set cycle detection still works.

3. **Interaction with absEval mu body check.** The mu body check
   (line ~172) evaluates the body with self bound to the mu expression
   in context. This is an absEval concern (not subCheckNF), so it may
   be unaffected, but verify.

4. **Existing tests.** Run the full test suite after the change. Some
   tests may have been written assuming equi-recursive semantics. The
   `dNat` tests in particular should be checked carefully — they may
   start behaving differently (hopefully better).

---

## References

- `lean/Och/Eval.lean` — absEval, subCheckNF, concEval
- `lean/Och/Subtyping.lean` — Subtype' inductive, self_intro rule
- `lean/Och/Std/DNat.lean` — dependent naturals (primary test case)
- `lean/Och/Std/Array.lean` — arrays over Church nats (motivation for lenient)
- `docs/ideas/merge-fix-iota.md` — earlier exploration of fix/iota unification
- Peng Fu & Aaron Stump, "Self Types for Dependently Typed Lambda Encodings" —
  the paper that introduces self-types (ι). Cedille is the language built on
  this work by the same group.
