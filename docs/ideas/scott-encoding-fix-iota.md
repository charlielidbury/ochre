# Scott Encoding with fix + iota

This note explores how self types (`iota`) interact with Scott-encoded
(rather than Church-encoded) recursive datatypes, and why the combination
of `fix` and `iota` gives a clean decomposition of concerns for dependent
elimination in Och.

---

## Background: Scott vs Church encoding

Church encoding bakes recursion into data. A Church numeral *is* its own fold:

```
3 = lam s. lam z. s (s (s z))
```

Applying a Church numeral to `s` and `z` iterates `s` three times. The type
is non-recursive:

```
cNat = forall X : Type. X -> (X -> X) -> X
```

Scott encoding only does one level of pattern matching. Each constructor
exposes its immediate fields without recursing:

```
zero   = lam z. lam s. z
succ n = lam z. lam s. s n
```

To iterate over Scott-encoded data you need an external fixpoint combinator.
The type is inherently recursive -- `SNat` appears in its own definition:

```
SNat = forall X : Type. X -> (SNat -> X) -> X
```

## Self types + Scott encoding = dependent case analysis

Adding `iota` to a Scott-encoded Nat gives dependent *case analysis* (one
level of dependent pattern matching), but not full induction:

```
SNat = iota n. (P : SNat -> Type) ->
       P zero ->
       ((k : SNat) -> P (succ k)) ->
       P n
```

The step case is `(k : SNat) -> P (succ k)` -- you get the predecessor `k`
but *no inductive hypothesis* `P k`. This is exactly one-level dependent
pattern matching. The built-in eliminator is just application:

```
caseNat : (n : SNat) -> (P : SNat -> Type) -> P zero -> ((k : SNat) -> P (succ k)) -> P n
caseNat = lam n. n   -- after self-elimination
```

Compare with Church encoding + self types, where the step case includes the
inductive hypothesis `(k : Nat) -> P k -> P (succ k)` and the eliminator
gives full induction directly. With Scott encoding, induction must come from
somewhere else.

## Full induction via fix + iota

Induction is recovered by combining `fix` (for recursion) with the
dependent case analysis from `iota`:

```
indNat : (n : SNat) -> (P : SNat -> Type) ->
         P zero ->
         ((k : SNat) -> P k -> P (succ k)) ->
         P n
indNat = fix (lam ind. lam n : SNat. lam P. lam z. lam s.
  n P
    z                              -- zero: return z : P zero
    (lam k. s k (ind k P z s))    -- succ: recurse via fix to get P k,
                                   --       then apply s to get P (succ k)
)
```

Why this typechecks:

1. `n : SNat`, so by self-elimination,
   `n P z f : P n` for any `f : (k : SNat) -> P (succ k)`.
2. `ind k P z s : P k` by the recursive call through `fix`.
3. `s k (ind k P z s) : P (succ k)` by the type of `s`.
4. So `lam k. s k (ind k P z s)` has type `(k : SNat) -> P (succ k)`,
   which is the step argument that `n` expects.
5. The whole expression has type `P n`.

## Separation of concerns

Each piece of the system has a single, clear role:

| Concern                        | Provided by    |
|--------------------------------|----------------|
| Pattern matching (one level)   | Scott encoding |
| Recursion (iteration)          | `fix`          |
| Return type depends on input   | `iota`         |
| Full induction                 | All three      |

With Church encoding, recursion is baked into the data representation, which
is redundant when the language already has `fix`. Scott encoding lets `fix`
own recursion and keeps data simple.

## Tying the recursive knot

Scott encoding requires recursive types. `SNat` refers to itself. In Och,
the natural way to express this is `fix` at the type level:

```
SNat = fix (lam SNat : Type.
  iota n. (P : SNat -> Type) ->
          P zero ->
          ((k : SNat) -> P (succ k)) ->
          P n
)
```

Here `fix` and `iota` serve complementary roles in the same definition:

- **`fix`** -- "this *type* refers to itself" (recursive type)
- **`iota`** -- "this type refers to its *inhabitant*" (self-referential typing)

These are two distinct forms of self-reference that cannot be collapsed into
one construct without losing expressiveness.

## Open question: does fix work at the type level in Och?

For this approach to work, `fix` applied to a type-level function must
produce a usable recursive type. Currently:

- **Concrete eval:** `fix (lam T. F(T))` unfolds forever.
- **Abstract eval:** `fix (lam T : Type. F(T))` returns `Type`.

So `SNat : Type` is fine abstractly, but the evaluator cannot unfold `SNat`
to inspect its structure. For subtype checking and abstract evaluation to
work with Scott-encoded data, Och would need to lazily unfold `fix`-defined
types -- unrolling one level when the structure is needed, rather than
reducing to a fixpoint eagerly.

This is a standard problem in type theory (equi-recursive vs iso-recursive
types). Och would need to decide:

- **Equi-recursive:** The evaluator treats `SNat` and its one-step unfolding
  as definitionally equal. Subtype checking unfolds as needed. Simpler for
  the user but harder to implement (risk of infinite unfolding loops).
- **Iso-recursive:** Explicit fold/unfold operations mediate between `SNat`
  and its unfolding. Adds syntax but keeps evaluation predictable.

The equi-recursive approach aligns better with Och's minimalism (no extra
syntax), but requires care in the subtype checker to avoid divergence --
the same kind of care already needed for self types (see Section 1.7 of
the self-types survey, re: Kind2's similarity checking).

## Comparison with Church encoding approach

| | Church + iota | Scott + fix + iota |
|---|---|---|
| Data representation | Fold (complex) | Case split (simple) |
| Recursive types needed? | No | Yes |
| Induction from | Self type alone | fix + self type |
| `fix` redundancy | Partially redundant | Fully utilized |
| New syntax needed | `iota` only | `iota` + recursive type support |
| Pattern matching cost | O(n) fold | O(1) case split |

Church encoding is simpler to adopt first (no recursive type machinery needed),
which is why it comes first in the incremental plan. Scott encoding is the
target end state.
Scott encoding is a cleaner decomposition but requires solving the
recursive-types-via-`fix` problem first.

## Implications for the fix/iota merge question

This analysis shows that `fix` and `iota` are complementary rather than
redundant. In the Scott encoding of `SNat`, both appear in the *same
definition* serving different purposes. Merging them into a single construct
would require that construct to simultaneously express type-level recursion
and term-level self-reference -- two distinct operations that happen to
share the word "self-referential."

---

## Verdict: Church + iota first, Scott + fix + iota is the end state

Recursive types and Scott encoding are **requirements** for Och's end state —
not optional extras. Church encoding with self types is the right *first step*
because it avoids solving recursive types as a prerequisite to getting
dependent elimination working at all. But Church encoding is a stepping stone,
not the destination.

### The killer argument: recursive types

Scott encoding *requires* recursive types. `SNat` refers to itself in its
own definition. To express this in Och, you'd write:

```
SNat = fix (lam SNat : Type.
  iota n. (P : SNat -> Type) -> P zero -> ((k : SNat) -> P (succ k)) -> P n
)
```

But Och's `fix` at the type level doesn't work for this. `absEval` of
`fix (lam T : Type. F(T))` returns `Type` -- it cannot unfold `SNat` to
inspect its structure. The subtype checker would see `SNat` as an opaque
stuck term, unable to compare it with anything useful.

To make Scott encoding work, Och would need to solve equi-recursive vs
iso-recursive types, lazy unfolding in the subtype checker, and divergence
prevention during unfolding. That is an entire separate research problem
with no existing infrastructure in the codebase.

Church encoding sidesteps this entirely.
`cNat = lam X : Type. lam z : X. lam s : (X -> X). X` is non-recursive.
Adding `iota` on top doesn't change that -- the resulting
`Nat = iota n. ...` refers to `Nat` only in motive positions where it is a
parameter, not a recursive definition.

### fix isn't redundant with Church encoding in Och

The Scott argument assumes `fix` is wasted on Church data because "Church
bakes in recursion." But in practice, `fix` serves a different role in Och
-- it handles recursive *functions* that Church folds can't express. The
`mapArray` example uses `fix` + `isZero` partitioning to recurse over
arrays. Church encoding handles data traversal; `fix` handles control flow.
They are already complementary.

### Proof effort

Adding `iota` to Och's Lean mechanization means one new case per theorem,
following the `lam` pattern. The proofs in Monotonicity.lean and
Soundness.lean already establish the template.

Adding recursive type support would be far more invasive. The subtype
checker (`subCheckNF`), the evaluator, and every inversion lemma would need
fundamentally new reasoning about unfolding -- not just a new case in an
existing pattern.

### The stuck application problem is the same either way

Both approaches face the "stuck self-typed application" problem: when
`absEval` encounters `app f a` with abstract `f : iota x. T`, it needs
type-directed evaluation to infer the result type. Scott encoding doesn't
help here; it makes it worse by also requiring recursive type unfolding
during that same inference.

### Scott encoding is the end state

Scott encoding is where Och needs to end up: O(1) pattern matching, simpler
data representation, cleaner separation of concerns. These are requirements,
not nice-to-haves. The incremental path is:

1. Add `iota` (one new `Expr` constructor).
2. Get dependent elimination working with Church encoding.
3. Prove soundness and monotonicity for the extended system.
4. Add recursive type support (type-level `fix` with lazy unfolding).
5. Move standard library to Scott encoding.

Church encoding is step 2, not the destination. Design decisions throughout
should avoid painting into a corner that makes steps 4-5 harder.
