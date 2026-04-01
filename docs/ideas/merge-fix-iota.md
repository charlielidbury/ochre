# Could fix and iota be the same thing?

This document explores whether `fix` (general recursion) and `iota` (self
types) are two faces of the same primitive, viewed through Och's "terms and
types are the same thing" lens. This is open research — not a proposal to
change anything yet.

---

## The observation

Both `fix` and `iota` express self-reference:

- `fix (lam f. body)` — the value `f` refers to itself
- `iota x. T` — the type `T` refers to its inhabitant

In a system that separates terms from types, these are clearly different
operations on different syntactic categories. But Och dissolves that
distinction. A type is just an approximate program. So what are `fix` and
`iota` really doing?

## What "self" means

Both primitives bind a name that refers back to the thing being defined.
The apparent difference is how *determined* that self-reference is:

**fix:** self is **determined** — `f` is bound to the specific expression
`fix (lam f : T. body)`. The concrete evaluator unrolls: substitute the
whole fix expression for `f`, keep going.

**iota:** self is **undetermined** — `x` is neutral, standing for
"whatever ends up here." There is no unrolling. The body is a
specification that holds for any `t` satisfying `t : T[x := t]`.

But "determined vs undetermined" is just the concrete/abstract distinction.
Concretely, everything is determined — you have the actual value.
Abstractly, bound things are undetermined — you have a neutral variable.
This is not a property of the primitive. It is a property of the
evaluation mode.

So both fix and iota say: **"the thing being defined can refer to itself."**
The only difference is how much is known about that "self" at evaluation
time — and that is already handled by Och's two evaluation modes.

## The concrete/abstract split already provides both meanings

Consider a hypothetical unified primitive `mu x. body`, and ask what
Och's two evaluation modes would do with it:

**Concrete evaluation** (runtime): `x` is determined — bound to the
mu expression itself.

```
concEval (mu x. body) = concEval (body[x := mu x. body])
```

This IS fix. Unroll the self-reference, keep computing. A recursive
function `mu f. lam n. ... f (pred n) ...` unfolds as expected.

**Abstract evaluation** (compile-time): `x` is undetermined — neutral.

```
absEval (mu x. body) = mu x. absEval(body)    -- normalize body, return as value
```

This IS iota. The body is normalized under the binder (with `x` as
neutral), and the result is a value that approximates all expressions
satisfying the self-referential property. Self-introduction and
self-elimination fall out of the existing subtyping machinery.

No new distinction is needed. The evaluation mode already determines
how "self" behaves — determined (concrete) or undetermined (abstract).
One primitive, two modes, same as every other Och expression.

## How existing patterns translate

### Recursive functions (currently fix)

Currently:
```
fix (lam f : Nat -> Nat. lam n : Nat. ... f (pred n) ...)
```

Abstract eval shortcuts: `fix (lam f : T. body)` returns `T`, avoiding
divergence.

With mu:
```
mu (f : Nat -> Nat). lam n : Nat. ... f (pred n) ...
```

The annotation `Nat -> Nat` is on the mu itself — abstract eval returns
it directly, same as fix returns the domain type today. The lambda wrapper
that fix required is gone; mu carries its own binder name and annotation.

The translation is mechanical: `fix (lam f : T. body)` becomes
`mu (f : T). body`.

### Self types (currently iota)

Currently:
```
Nat = iota n. (P : Nat -> Type) -> P zero -> ... -> P n
```

With mu:
```
Nat = mu (n : Nat). (P : Nat -> Type) -> P zero -> ... -> P n
```

The annotation `Nat` is the self type itself — the type of the inhabitant.
Abstract eval normalizes the body under the binder, returns `mu n Nat.
body'` as a type value. Self-introduction (`t : mu x T. body` iff
`t : body[x := t]`) and self-elimination (from `t : mu x T. body` derive
`t : body[x := t]`) work as before.

The annotation enables Victor's trick: comparing `mu (n : Nat). ...` with
`mu (m : Nat). ...` checks `Nat == Nat` instead of unfolding the bodies.

### Recursive types (currently unsupported — needs fix at the type level)

Currently broken:
```
SNat = fix (lam SNat : Type. ...)   -- absEval returns Type, structure lost
```

With mu:
```
SNat = mu (SNat : Type). mu (n : SNat). (P : SNat -> Type) -> P zero -> ((k : SNat) -> P (succ k)) -> P n
```

Two nested mus, both doing the same thing at different levels:
- Outer mu (ann = `Type`): SNat refers to itself
- Inner mu (ann = `SNat`): n refers to itself

Both are just self-reference. The outer mu's self-reference happens to be
used in type positions (defining a recursive type). The inner mu's
self-reference happens to be used to relate a value to its own properties.
But there is no fundamental distinction — both are `mu`, both bind a name
that refers to the thing being defined. They compose naturally because
self-reference composes.

The annotations also compose: the outer mu's annotation is `Type`, the
inner mu's annotation is `SNat`. The subtype checker can compare outer mus
by their `Type` annotations, and inner mus by their `SNat` annotations,
without unfolding either.

This is cleaner than having two separate primitives that need different
evaluation strategies for what is structurally the same operation.

## Where the analogy is imperfect

### Divergence

Fix can diverge. Iota cannot. If mu unifies them, when does mu diverge?

Concrete eval of `mu x. body` unrolls — this can diverge, same as fix.
That is fine; concrete eval of recursive functions should be able to loop.

Abstract eval of `mu x. body` normalizes body with x as neutral — this
does NOT unroll, so it terminates. That is also fine; iota never diverges.

The divergence difference between fix and iota is not a property of the
primitives themselves. It is a property of the evaluation mode. Concrete
mode unrolls (can diverge). Abstract mode normalizes under the binder
(terminates). The unified mu inherits this naturally.

The only risk: abstract eval of the body itself might diverge if the body
contains another mu that triggers unrolling. But abstract eval would NOT
unroll a nested mu — it would normalize its body under the binder, same
as the outer one. So nested mus are safe in abstract mode. (This is
exactly how nested lambdas work today.)

### One value vs a set of values

In traditional type theory, fix produces one value while iota describes a
set of values. This seems like a fundamental mismatch. But Och does not
have this distinction. A type is not a set — it is a value, one that
approximates other values. `Nat` is not "the set of all naturals"; it is
a single expression that is less precise than `3` but more precise than
`Type`. The one-vs-many framing is a holdover from set-theoretic thinking
about types that does not apply here.

### The domain annotation / ascription gap (RESOLVED)

The earlier version of this document asked: if mu drops fix's domain
annotation and relies on ascription for typing, what happens when a mu
expression appears without an enclosing ascription?

Victor Maia's work on Kind2 resolves this independently. He discovered
that self types NEED an annotation on the binder — not for abstract eval,
but for terminating equality/subtype checking. The annotation prevents
divergent unfolding of recursive self-types.

So mu should carry an annotation: `mu (x : T). body`. This is not
redundant with ascription — it serves a different purpose:

- **Ascription** (`(e : T)`) tells the evaluator "treat this term as
  having type T." It is external to the expression.
- **The mu annotation** (`mu (x : T). body`) tells the subtype checker
  "you can compare me by looking at T instead of unfolding body." It is
  internal to the expression.

Both are needed. The annotation resolves the gap: mu can be typed
standalone (absEval returns the annotation, like fix returns the domain),
AND the subtype checker can compare mus without diverging (compare
annotations, like Victor's similarity check).

### Subtyping asymmetry

The subtyping rules for mu have an asymmetry:

```
a  <=  mu x. T    iff    a <= T[x := a]         -- self-intro: substitute the LHS
mu x. T  <=  b    iff    T[x := mu x. T] <= b   -- self-elim: substitute the mu itself
```

Self-intro substitutes `a` (the LHS). Self-elim substitutes the mu
expression itself. These look like different operations, but they are
doing the same thing: resolving the self-reference `x` with the most
specific information available.

On the left of `<=`, the mu IS a specific expression — we know exactly
what it is, so we substitute it for `x`. On the right of `<=`, the mu is
being checked against — we don't yet know what will inhabit it, but we do
know what `a` is, so we substitute `a` for `x`.

The asymmetry is just: substitute whichever side is more determined. This
is not two different notions of self-reference. It is one notion of
self-reference resolved with the best available information, which depends
on context.

## The annotation argument

Victor Maia (Kind2) independently discovered that self types need an
annotation on the binder. The problem: checking equality of self-encoded
types like `List #U60 == List Char` diverges, because unfolding the self
type exposes `List` in the body, which gets checked for equality again —
infinite loop.

His solution: annotate the self binder with its type.

```
-- Before (unannotated, diverges):
$self. ∀(P: ∀(xs: (List T)) *) ... (P self)

-- After (annotated, terminates):
$(self: (List T)). ∀(P: ∀(xs: (List T)) *) ... (P self)
```

Then the similarity checker compares annotations instead of unfolding
bodies:

```
($(x:X) A) ~~ ($(y:Y) B)  ::=  X ~~ Y    -- compare annotations, don't unfold
```

This terminates because it never enters the body. False negatives are
possible (structurally different annotations that are definitionally equal
won't unify) but no false positives. Victor notes this gives "free newtype
functionality" — two types with identical structure but different names
won't unify.

See: https://gist.github.com/VictorTaelin/3f748a46e95071e29462b1ac93c294c5

### The annotation is the missing piece for unification

Look at the shapes with and without the annotation:

```
fix (lam f : T. body)    -- self-reference WITH annotation T
iota x. body             -- self-reference WITHOUT annotation
```

Fix already has the annotation. It's what lets absEval return `T` without
entering the body (avoiding divergence on recursive functions). Victor
discovered that iota needs the same thing, for the same reason — without
it, equality checking diverges on recursive self-types.

Add the annotation to iota:

```
iota (x : T). body       -- self-reference WITH annotation T
```

Now fix and iota are structurally identical:

| | fix | annotated iota |
|---|---|---|
| Shape | `name : T . body` | `name : T . body` |
| Why T exists | absEval returns T (avoids divergent unrolling) | equality compares T (avoids divergent unfolding) |
| Self-reference | determined (concrete use) | undetermined (abstract use) |

The annotation serves the same function in both: it is a **finite summary**
that lets you reason about the self-referential thing without entering its
potentially-infinite body. For fix, the summary is used by abstract eval.
For iota, the summary is used by the subtype/equality checker. For the
unified mu, it would be used by both.

## What mu would look like in Och

### Syntax

Replace both `fix` and `iota` with one constructor:

```lean
inductive Expr where
  | var    : Name -> Expr
  | lam    : Name -> (dom : Expr) -> (body : Expr) -> Expr
  | app    : Expr -> Expr -> Expr
  | asc    : (term : Expr) -> (ty : Expr) -> Expr
  | type   : Expr
  | mu     : Name -> (ann : Expr) -> (body : Expr) -> Expr    -- self-reference
```

Six constructors instead of seven. (Or five plus mu, vs the original five
plus fix plus iota.)

Note: mu carries an **annotation** (`ann`), following Victor's insight.
This is not optional decoration — it is load-bearing for termination of
both abstract evaluation and subtype checking.

The annotation `ann` in `mu x : ann. body` is the type of the self-
referential thing. It serves as a finite summary that can be inspected
without unfolding the body. This mirrors how `lam x : dom. body` carries
a domain annotation.

### Evaluation

```
concEval (mu x ann. body) = concEval (body[x := mu x ann. body])   -- unroll

absEval (mu x ann. body) =
  match absEval env ann with
  | some ann' =>
    match absEval ((x, var x) :: env) body with
    | some body' => some (mu x ann'. body')                         -- normalize under binder
    | none => none
  | none => none
```

Concrete mode is fix. Abstract mode is iota. One primitive, two behaviors,
distinguished by the evaluation mode that Och already has.

### Subtyping

```
-- mu-mu: compare annotations (Victor's trick), avoid unfolding bodies
subCheck (mu x X. A) (mu y Y. B) = subCheck X Y

-- self-intro: a <= mu x ann. T  iff  a <= T[x := a]
subCheck a (mu x ann. T) = subCheck a (T[x := a])

-- self-elim: mu x ann. T <= b  iff  T[x := mu x ann. T] <= b
subCheck (mu x ann. T) b = subCheck (T[x := mu x ann. T]) b
```

The mu-mu case is the key innovation from Victor: compare annotations
rather than unfolding. This prevents divergence on recursive types like
`mu SNat. mu n. ...` where unfolding would loop. The self-intro and
self-elim cases do unfold, but only one level — the annotation is
available as a fallback if the unfolded form is itself a mu.

### Abstract eval shortcut via annotation

For recursive functions, abstract eval can optionally use the annotation
as a shortcut, exactly as fix currently uses the domain type:

```
absEval (mu x ann. body) = absEval ann    -- shortcut: return the annotation
```

This is sound when the annotation correctly summarizes the body's type
(which is what the annotation means). It avoids entering the body at all,
which prevents divergence for recursive computations.

Whether to normalize the body or return the annotation is a design choice.
Normalizing the body gives more precise types (iota behavior). Returning
the annotation gives guaranteed termination (fix behavior). The right
answer might depend on context — if the mu is in a term position (being
ascribed), return the annotation; if it is in a type position (being used
as a type), normalize the body.

## What this would mean for the roadmap

If mu is the right primitive, then:

1. **Church + mu** works exactly like Church + iota does now. Nothing changes
   for the current stepping-stone plan.

2. **Recursive types via mu** come for free — `mu T. body` at the type level
   is just a mu whose body is a type expression. The abstract evaluator
   normalizes the body (it does NOT unroll it), so it returns a type value
   that the subtype checker can inspect. The equi-recursive unfolding
   problem is solved by the self-elim rule: `mu T. body <= something` checks
   `body[T := mu T. body] <= something`, which is a one-step unfolding. The
   subtype checker already does this for iota.

3. **Scott + mu** composes the two uses: `mu SNat. mu n. (P : SNat -> Type)
   -> ...` uses the outer mu for type recursion and the inner mu for self
   typing. No new machinery needed.

4. **Recursive functions** are `(mu f. lam n. body : T)` instead of
   `fix (lam f : T. body)`. Same expressive power, one fewer primitive.

The interesting question is whether this simplification is real or whether
it hides complexity that would resurface in the proofs. The self-elim
unfolding rule applied to recursive types is essentially equi-recursive
unfolding — and equi-recursive types have known issues with divergent
subtype checking. But mu does not make this problem worse than it already
is; iota's self-elim rule already does the same unfolding. The only
difference is that with mu, type-level self-reference is a first-class
use case rather than an accidental one.

## Open questions

1. **Does the proof go through?** The soundness proof relates concrete and
   abstract evaluation. For fix, the proof uses the domain annotation to
   relate `concEval(fix body)` to `absEval(fix body) = T`. With mu, the
   annotation is on the mu itself: `concEval(mu x T. body)` unrolls,
   `absEval(mu x T. body)` returns (something derived from) T. The
   annotation plays the same structural role as fix's domain type, so the
   proof shape should be similar. But this needs verification.

2. **Nested mu and fuel.** Concrete eval of `mu x T. body` unrolls,
   consuming fuel. If body contains another mu, that also unrolls. Is the
   fuel accounting the same as for nested fix? It should be, since the
   recursive structure is identical.

3. **Is the subtyping asymmetry correct?** The self-intro rule substitutes
   the term being checked; self-elim substitutes the mu expression. This
   feels right but needs formal verification. In particular: does
   transitivity hold? If `a <= mu x T. body` and `mu x T. body <= b`, can
   we derive `a <= b`?

4. **Is this actually novel?** The observation that fixed points and self
   types are related is not new (both involve self-reference). But the
   specific claim that they are the SAME primitive distinguished only by
   evaluation mode — in a system that already has two evaluation modes for
   exactly this purpose — might be. Literature search needed.

5. **Recursive types for free?** The most exciting implication is that
   mu might solve the recursive types problem (roadmap item 5) as a
   side effect of unifying fix and iota, rather than requiring separate
   machinery. Self-elim on `mu T ann. body` gives one-step unfolding.
   The mu-mu subtyping case compares annotations (Victor's trick),
   preventing divergent unfolding loops. This is exactly the equi-recursive
   machinery that was previously identified as a separate research problem —
   but it falls out of the unified primitive's subtyping rules for free.

6. **What should the annotation contain?** For recursive functions the
   annotation is the function type (`Nat -> Nat`). For self types the
   annotation is the self type itself (`Nat`). For recursive types the
   annotation is... `Type`? The right answer might vary. Does the
   annotation need to be the *exact* type, or just a sufficient
   approximation for the subtype checker to use as a termination anchor?

7. **False negatives from annotation comparison.** Victor's trick of
   comparing annotations instead of unfolding bodies introduces false
   negatives: two mu types with definitionally equal but syntactically
   different annotations won't unify. Victor considers this acceptable
   (and even useful — "free newtypes"). Is this acceptable for Och? It
   means alpha-equivalent self types with different annotations are
   distinct. This is a design choice, not a bug.

8. **When to normalize vs return the annotation.** Abstract eval of
   `mu x ann. body` could either normalize the body (precise, iota-like)
   or return the annotation (safe, fix-like). If both are needed in
   different contexts, the evaluator needs a way to decide. One option:
   always normalize the body, but use the annotation as a fallback
   when normalization would diverge (e.g., when the body contains a
   self-reference to x in a non-type position). Another: let the
   context decide (ascription returns annotation, bare mu normalizes).

---

## Worked example: typing `zero`, `succ`, and `add`

This section works through typing derivations using mu. The goal is to
discover what typing rules are needed by seeing what the derivation
demands, not to assume rules and verify them.

Notation: `Π(x:A).B` and `A → B` are used in type positions for
readability. In Och's actual syntax these are `λ(x:A).B` — terms and
types are the same thing. We use the indented natural-deduction format
from notation.md (conclusion first, premises indented below).

### Definitions

```
Nat ≜ μ(self : Nat). Π(P : Nat→Type). P zero → (Π(k:Nat). P k → P (succ k)) → P self
```

Abbreviation for the body after μ-elim:

```
NE(t) ≜ Π(P : Nat→Type). P zero → (Π(k:Nat). P k → P (succ k)) → P t
```

So `Nat = μ(self : Nat). NE(self)` and the μ-elim rule gives
`t : Nat ⟹ t : NE(t)`.

```
zero ≜ μ(z : Nat). λ(P : Nat→Type). λ(base : P z). λ(step : Π(k:Nat). P k → P (succ k)). base

succ ≜ λ(k : Nat). μ(sk : Nat). λ(P : Nat→Type). λ(base : P zero). λ(step : Π(k':Nat). P k' → P (succ k')). step k (k P base step)

add ≜ λ(n : Nat). λ(m : Nat). n (λ(_ : Nat). Nat) m (λ(k : Nat). λ(ih : Nat). succ ih)
```

Note: `zero`'s annotations say `P z` (referring to itself), `succ`'s
body uses `k P base step` (μ-elim on k to invoke its elimination
principle). Both are self-referential — the μ makes this explicit.

### Typing `zero` (μ-intro)

Goal: `⊢ zero : Nat`.

Since `zero = μ(z : Nat). body`, we need μ-intro: show that `body`
satisfies `NE(z)` when `z` refers to the μ being defined.

```
⊢ zero : Nat                                                        [μ-Intro]
  z : Nat ⊢ body : NE(z)                                            [Lam] ×3
    -- body = λ(P : Nat→Type). λ(base : P z). λ(step : ...). base
    -- NE(z) = Π(P : Nat→Type). Π(base : P z). Π(step : ...). P z
    -- so we need: base : P z  ✓  (base is bound with that type)
    Γ₀ ⊢ base : P z                                                 [Var]
      -- where Γ₀ = z:Nat, P:Nat→Type, base:P z, step:Π(k:Nat).P k→P (succ k)
```

Clean: `base` has exactly the right type. The self-reference (`P z`
mentions `z`) is handled by μ-intro — `z` is in scope, referring to
the μ expression.

**Observation:** μ-intro requires checking the body against `NE(z)`,
which means the body's binder annotations (`P z`) must align with the
target type. The annotation on μ (`z : Nat`) tells us z's type, which
is needed to validate `P z : Type` (since `P : Nat → Type` and
`z : Nat`).

### Typing `succ` (μ-intro + μ-elim)

Goal: `⊢ succ : Nat → Nat`.

```
⊢ succ : Nat → Nat                                                  [Lam]
  k : Nat ⊢ μ(sk : Nat). body_s : Nat                               [μ-Intro]
    Γ₁ ⊢ body_s : NE(sk)                                            [Lam] ×3
      -- where Γ₁ = k:Nat, sk:Nat, P:Nat→Type, base:P zero, step:Π(k':Nat).P k'→P (succ k')
      -- body_s = λP. λbase. λstep. step k (k P base step)
      -- NE(sk) = Π(P:Nat→Type). P zero → (Π(k':Nat). P k' → P (succ k')) → P sk
      -- need: step k (k P base step) : P sk
      --        ^^^^^^^^^^^^^^^^^^^^^^
      --  but sk = succ k, so need: P (succ k)
```

Wait — `sk` is the μ-bound name for `succ k`. In the μ-intro rule,
we check the body against `NE(sk)`, and the return type is `P sk`.
But `sk` refers to the μ expression `succ k` itself. We need
`P (succ k)`, not `P sk` — unless the checker knows `sk = succ k`.

**This is a problem.** In the μ-intro rule, `sk` is just a variable
in scope. The checker doesn't automatically know `sk = succ k`. But
the return type `P sk` must equal `P (succ k)` for the derivation to
work.

How is this resolved? Two options:

**(a)** The μ-intro rule substitutes the FULL μ expression for `self`,
not just a variable: check `body : NE(succ k)` instead of `NE(sk)`.
Then the return type is `P (succ k)` directly.

**(b)** Use the fact that `sk : Nat` and `succ k : Nat` and rely on
the subtype checker to compare `P sk ⊑ P (succ k)` using the
information that `sk` was defined as `succ k`.

Option (a) is simpler and matches the standard self-intro rule from
the literature: `t : T[self := t]`, where `t` is the actual term (not
a fresh variable). Let's use (a).

Revised derivation with self-substitution:

```
⊢ succ : Nat → Nat                                                  [Lam]
  k : Nat ⊢ μ(sk : Nat). body_s : Nat                               [μ-Intro]
    -- μ-intro: check body_s : NE(self)[self := μ(sk:Nat).body_s]
    -- Let S = μ(sk:Nat).body_s  (the whole succ-k expression)
    -- NE(S) = Π(P:Nat→Type). P zero → (Π(k':Nat). P k'→P (succ k')) → P S
    -- In the body, sk is bound to S (the μ expression itself)
    Γ₂ ⊢ step k (k P base step) : P S                               [App] ×2
      -- where Γ₂ = k:Nat, sk=S, P:Nat→Type, base:P zero, step:Π(k':Nat).P k'→P (succ k')
```

Now type the inner application `step k (k P base step)`:

```
      Γ₂ ⊢ step k (k P base step) : P (succ k)                     [App]
        Γ₂ ⊢ step k : P k → P (succ k)                             [App]
          Γ₂ ⊢ step : Π(k':Nat). P k' → P (succ k')                [Var]
          Γ₂ ⊢ k : Nat                                              [Var]
        Γ₂ ⊢ k P base step : P k                                    [App] ×3 + μ-Elim
          Γ₂ ⊢ k : NE(k)                                            [μ-Elim]
            Γ₂ ⊢ k : Nat                                            [Var]
          -- NE(k) = Π(P:Nat→Type). P zero → (...) → P k
          -- apply to P: Π(base:P zero). Π(step:...). P k
          Γ₂ ⊢ P : Nat → Type                                       [Var]
          -- apply to base: Π(step:...). P k
          Γ₂ ⊢ base : P zero                                        [Var]
          -- apply to step: P k
          Γ₂ ⊢ step : Π(k':Nat). P k' → P (succ k')                [Var]
          -- result: P k                                              ✓
```

So `step k (k P base step) : P (succ k)`. But we need `P S` where
`S = μ(sk:Nat).body_s` is the whole succ-k expression.

**We need `P (succ k) = P S`.** This requires `succ k = S`, i.e.,
the μ expression that IS `succ k` equals `succ k`. This is
essentially: "the succ-k value, when substituted for self, produces
something equivalent to succ-k." This is the fixed-point property —
it's true by construction but not syntactically obvious.

In practice, the checker must either:
- Recognize that `S` reduces to `succ k` (by evaluating the μ), or
- Accept `P (succ k) ⊑ P S` via the subtype checker.

This is not a blocker — it's exactly the kind of check the μ-intro
rule must do. But it reveals that **μ-intro is not purely syntactic**.
It requires evaluation or subtyping to verify that the body, when
self-substituted, has the right type.

### Typing `add` (μ-elim in action)

Goal: `⊢ add : Nat → Nat → Nat`.

Let `Mot ≜ λ(_:Nat). Nat` and `step ≜ λ(k:Nat). λ(ih:Nat). succ ih`.

```
⊢ add : Nat → Nat → Nat                                             [Lam] ×2
  Γ ⊢ n Mot m step : Nat                                            -- Γ = n:Nat, m:Nat
```

The core: typing the application chain `((n Mot) m) step`.

```
    Γ ⊢ n : NE(n)                                                   [μ-Elim]
      Γ ⊢ n : Nat                                                   [Var]
      -- Nat = μ(self:Nat). NE(self)
      -- μ-elim: NE(self)[self := n] = NE(n)
      -- NE(n) = Π(P:Nat→Type). P zero → (Π(k:Nat). P k → P (succ k)) → P n
```

Apply n to Mot:

```
    Γ ⊢ n Mot : Mot zero → (Π(k:Nat). Mot k → Mot (succ k)) → Mot n   [App]
      Γ ⊢ n : NE(n)                                                     (above)
      Γ ⊢ Mot : Nat → Type                                              [Lam]
      -- substitute P := Mot in remaining type:
      --   Π(z: Mot zero). Π(s: Π(k:Nat). Mot k → Mot (succ k)). Mot n
```

β-reduce Mot applications (`Mot = λ(_:Nat). Nat` ignores its arg):

```
      -- Mot zero    →β  Nat
      -- Mot k       →β  Nat
      -- Mot (succ k)→β  Nat
      -- Mot n       →β  Nat
      -- so the type simplifies to:
      --   Nat → (Π(k:Nat). Nat → Nat) → Nat
```

Apply to m:

```
    Γ ⊢ n Mot m : (Π(k:Nat). Nat → Nat) → Nat                      [App]
      Γ ⊢ n Mot : Nat → (Π(k:Nat). Nat → Nat) → Nat                (above, after β)
      Γ ⊢ m : Nat                                                    [Var]
```

Apply to step:

```
    Γ ⊢ n Mot m step : Nat                                           [App]
      Γ ⊢ n Mot m : (Π(k:Nat). Nat → Nat) → Nat                    (above)
      Γ ⊢ step : Π(k:Nat). Nat → Nat                                [Lam] ×2
        Γ, k:Nat, ih:Nat ⊢ succ ih : Nat                            [App]
          ⊢ succ : Nat → Nat                                        [Var]
          Γ, k:Nat, ih:Nat ⊢ ih : Nat                               [Var]
```

Result: `n Mot m step : Nat`. ∎

### What this reveals

**1. The context must carry types, not just abstract values.**

At the critical μ-elim step, we need to know that `n`'s TYPE is
`Nat = μ(self:Nat). NE(self)`. Currently Och's `Env = List (Name × Expr)`
stores abstract values only — for `n`, it stores `var n` (neutral).
That's not enough. The env must store the type separately:

```
Env = List (Name × Expr × Expr)   -- (name, abstract_value, type)
```

When absEval processes `λ(n : Nat). body`, it must record BOTH:
- Value: `var n` (neutral — we don't know which Nat it is)
- Type: `Nat` (we know it IS a Nat)

The app case then uses the type to resolve stuck applications:
if `absEval(f) = var n` (stuck) and `n`'s type is `μ(self:T). body`,
unfold via μ-elim to get a function type.

**2. μ-elim in the app case is not optional.**

Without μ-elim, `n : Nat` is not a function type. The application
`n Mot` would be stuck — absEval would return `app n Mot` as an
opaque expression with unknown type. Every downstream application
(`n Mot m`, `n Mot m step`) would also be stuck. The final result
would be a stuck application, not `Nat`.

This is the "type-directed evaluation" that the self-types research
doc identified as the main open question. This worked example confirms
it's unavoidable and shows exactly where it's needed: the app case
must look up the type of a stuck function and attempt μ-elim.

**3. μ-intro requires evaluation, not just syntax.**

The `succ` derivation revealed that μ-intro checks `body : NE(S)`
where `S = μ(sk:Nat).body_s` is the whole self-referential expression.
The return type `P S` must match `P (succ k)`, which requires knowing
that `S` is equivalent to `succ k`. This is not syntactically obvious
— it requires evaluating or comparing the μ expression against its
intended meaning.

**4. β-reduction of the motive is essential.**

After applying `n` to `Mot`, the result type contains `Mot zero`,
`Mot k`, `Mot n`. These must β-reduce to `Nat` for the subsequent
applications to typecheck. With the constant motive `λ(_:Nat). Nat`
this is trivial. With a dependent motive like `λ(k:Nat). Vec k Nat`,
the result would be `Vec n Nat` — a type that mentions the abstract
`n`. The evaluator must be able to β-reduce in types.

**5. `add` itself needs no μ — only its arguments do.**

`add` is not self-referential. It's a plain lambda that USES μ-typed
arguments. The μ appears in `Nat`'s definition and in `zero`/`succ`'s
definitions, but `add` is just function application. The self-reference
is in the data, not in the function.

(This would change for a recursive `add` defined via μ instead of
Church-style iteration. But Church + μ gives us iteration for free
via application.)

**6. Dependent motive case (sketch).**

With `Mot = λ(k:Nat). Vec k Nat` instead of `λ(_:Nat). Nat`:

```
Mot zero     →β  Vec zero Nat
Mot k        →β  Vec k Nat
Mot (succ k) →β  Vec (succ k) Nat
Mot n        →β  Vec n Nat          -- stuck if n is abstract, but well-typed
```

The step function would need type `Π(k:Nat). Vec k Nat → Vec (succ k) Nat`
— a function that extends a vector by one element. The result type
`Vec n Nat` depends on the abstract `n`. This is the whole point of
dependent elimination: the return type tracks the input.

---

## Sharp edge: beware residual term/type thinking

When reasoning about fix vs iota, it is tempting to say: "fix's self-
reference points to the expression itself, while iota's self-reference
points to the inhabitant." This framing imports a term/type distinction
that Och does not have.

In Och, there is no difference between "an expression" and "an inhabitant
of a type." If `natId = lam(n: Nat). n`, you can apply `natId` to `3`
(a precise value) or to `Nat` itself (a less precise value) — both are
valid, the function does not know or care which it received. There is no
ontological boundary between terms and types; there are only expressions
at varying levels of precision.

So "the expression itself" and "the inhabitant" are not different kinds of
thing. They are both Expr. The only difference is how determined the self-
reference is at evaluation time:

- **Concrete eval:** self is determined (we have the actual expression)
- **Abstract eval:** self is undetermined (we have a neutral variable)

This is the concrete/abstract split, not a term/type split. Any
description of mu that relies on "the expression" vs "the inhabitant" as
if they were categorically different is smuggling in assumptions that Och
rejects. The correct framing is: mu binds a name to "self," and the
evaluation mode determines how much is known about that self.

This matters practically because framing the distinction as term-vs-type
can lead to design decisions that reify that distinction — separate
evaluation rules, separate subtyping rules, separate constructors — when
the whole point of mu is that one set of rules suffices.
