# Self Types for Och

This document is part research survey, part design exploration. The first half
covers self types as they exist in the literature. The second half works through
how they would interact with Och's specific design -- its terms-as-types
philosophy, dual evaluation, and Church-encoding-only data representation.

---

## Part 1: Self Types Objectively

### 1.1 What Self Types Are

A **self type** is a type former that lets a type refer to the term it is
typing. Written `iota x. T`, it binds `x` to the term being typed inside `T`.

The idea originates with Peng Fu and Aaron Stump (2014), who introduced
**System S** -- a type-assignment version of the Calculus of Constructions
extended with one new type former. The motivation is direct: Church-encoded data
in CoC can express *iteration* (non-dependent folds) but not *induction*
(dependent elimination). Geuvers (2001) proved this is a fundamental limitation
-- no encoding in lambda-P2 can derive an induction principle. Self types break
through this barrier with a single, minimal extension.

The key insight: a Church numeral like `3 = lam X. lam z. lam s. s (s (s z))`
already *computes* recursion over itself. If we could let its *type* mention the
numeral itself, then the type of applying `3` to a predicate `P`, a base case,
and a step function would be `P 3` -- exactly induction. Self types provide
exactly this ability.

### 1.2 The Typing Rules

Self types have three rules: formation, introduction, and elimination. The
presentation below follows Fu and Stump's System S, with Cedille Core's notation
where helpful.

**Formation (selfForm):**

```
    Gamma, x : T |- T : Type
    -------------------------
    Gamma |- iota x. T : Type
```

A self type `iota x. T` is well-formed when `T` is a valid type under the
assumption that `x` has type `T`. Note the apparent circularity: `x` is assumed
to have the very type being defined. This is well-founded because `T` is a type
expression, not a computation -- the formation rule only asks that `T` classifies
as a type, not that it reduces to a value.

**Introduction (selfGen / selfIntro):**

```
    Gamma |- t : T[x := t]
    -----------------------
    Gamma |- t : iota x. T
```

To show that `t` has self type `iota x. T`, show that `t` has type `T` with `x`
replaced by `t` itself. This is the rule that enables induction: you prove that a
numeral satisfies the induction principle *for itself*.

Why this is not circular: The premise `t : T[x := t]` is a standard typing
judgment. It does not require first establishing `t : iota x. T`. The self type
merely *packages* the information that `t` satisfies `T` when `T` mentions `t`.
There is no regress because the inner typing derivation uses the ordinary rules
of the calculus, not the self-introduction rule again.

**Elimination (selfInst / selfElim):**

```
    Gamma |- t : iota x. T
    -----------------------
    Gamma |- t : T[x := t]
```

Given that `t` has self type `iota x. T`, extract the fact that `t` has type
`T[x := t]`. This is the rule that *uses* the induction principle: it
instantiates the self-referential type with the actual term.

Introduction and elimination are inverses -- the self type is transparent. The
term itself is unchanged; only the type-level view changes. In Cedille/Kind
implementations, self-introduction is often implicit, and elimination is
triggered by using a self-typed term as a function (applying it to a predicate
and base/step cases).

### 1.3 How Nat Is Encoded with Self Types

Without self types, Church Nat has the type:

```
cNat = forall X : Type. X -> (X -> X) -> X
```

The eliminator `n X base step` returns something of type `X`, which is fixed
before elimination begins. This is merely iteration -- `X` cannot depend on `n`
or on which constructor was taken.

With self types, we define:

```
Nat = iota n. (P : Nat -> Type) ->
      P zero ->
      ((k : Nat) -> P k -> P (succ k)) ->
      P n
```

Here `n` refers to the numeral being typed. A value of type `Nat` is
simultaneously a Church numeral *and* a proof of its own induction principle.
Let us see why, step by step.

**zero:**

```
zero = lam P. lam z. lam s. z
```

We must show `zero : iota n. (P : Nat -> Type) -> P zero -> (...) -> P n`.
By selfIntro, we need `zero : T[n := zero]`, which is:

```
zero : (P : Nat -> Type) -> P zero -> ((k : Nat) -> P k -> P (succ k)) -> P zero
```

This holds trivially -- `zero` returns its second argument `z`, which has type
`P zero`.

**succ:**

```
succ = lam k. lam P. lam z. lam s. s k (k P z s)
```

We must show `succ k : iota n. (P : Nat -> Type) -> P zero -> (...) -> P n`,
i.e., `succ k : ... -> P (succ k)`.

The body `s k (k P z s)` has type `P (succ k)` because:
- `k : Nat`, so by selfElim, `k` has type `(P : Nat -> Type) -> P zero -> (...) -> P k`
- Therefore `k P z s : P k` (the inductive hypothesis)
- And `s k (k P z s) : P (succ k)` by the type of `s`

This is the crucial point: the successor *uses* the predecessor's induction
principle (obtained via self-elimination on `k`) to produce the inductive step.

### 1.4 How Dependent Elimination Works

Given `n : Nat`, `P : Nat -> Type`, `z : P zero`, and
`s : (k : Nat) -> P k -> P (succ k)`, we want to produce a term of type `P n`.

The induction principle is simply:

```
ind = lam P. lam z. lam s. lam n. n P z s
```

This works because:
1. `n : Nat = iota n. (P : Nat -> Type) -> P zero -> (...) -> P n`
2. By selfElim, `n : (P : Nat -> Type) -> P zero -> (...) -> P n`
3. Therefore `n P z s : P n`

The dependent eliminator is *free* -- it is just function application! The self
type ensures that what Church numerals already compute (recursion) is reflected
at the type level (induction). No additional primitive eliminator is needed.

**Concrete example: proving `P n` from `P 0` and `forall k. P k -> P (succ k)`.**

For `n = 3`:
```
3 P z s
= s 2 (2 P z s)
= s 2 (s 1 (1 P z s))
= s 2 (s 1 (s 0 (0 P z s)))
= s 2 (s 1 (s 0 z))
```

Each step applies `s` with the current predecessor and the inductive hypothesis
for that predecessor. The final result has type `P 3`.

### 1.5 How Other Types Are Encoded

**Bool:**

```
Bool = iota b. (P : Bool -> Type) ->
       P true ->
       P false ->
       P b

true  = lam P. lam t. lam f. t
false = lam P. lam t. lam f. f
```

Dependent elimination of booleans: given `b : Bool`, `P : Bool -> Type`,
`t : P true`, `f : P false`, we get `b P t f : P b`.

**List:**

```
List = lam A. iota l. (P : List A -> Type) ->
       P (nil A) ->
       ((x : A) -> (xs : List A) -> P xs -> P (cons A x xs)) ->
       P l

nil  = lam A. lam P. lam n. lam c. n
cons = lam A. lam x. lam xs. lam P. lam n. lam c. c x xs (xs P n c)
```

The pattern is the same: each value carries its own induction principle, and
the `cons` case uses the tail's self-typed induction principle to get `P xs`
(the inductive hypothesis).

**Sigma types (dependent pairs):**

```
Sigma = lam A. lam B. iota p. (P : Sigma A B -> Type) ->
        ((a : A) -> (b : B a) -> P (dpair A B a b)) ->
        P p

dpair = lam A. lam B. lam a. lam b. lam P. lam k. k a b
```

**Vec (length-indexed lists):**

This is where self types become especially powerful. In Kind, Victor Maia and
collaborators encode Vec by *case-splitting on the index* within the self type:

```
Vec : Type -> Nat -> Type
Vec = lam A. lam n.
  case n of
    zero   => iota v. (P : Vec A zero -> Type) ->
              P (vnil A) -> P v
    succ k => iota v. (P : Vec A (succ k) -> Type) ->
              ((x : A) -> (xs : Vec A k) -> P (vcons A k x xs)) ->
              P v
```

When the length is zero, there is only the `vnil` constructor. When the length
is `succ k`, there is only the `vcons` constructor. Pattern matching on a
`Vec A (succ k)` need not handle the nil case at all -- it is ruled out by the
type. This is a form of GADT-like refinement achieved purely through self types
and Church-style case analysis on indices.

### 1.6 The Typing Rules in Detail

The three rules (formation, introduction, elimination) from Section 1.2 are the
complete set. But several subtleties deserve attention:

**Erasure.** In Cedille and Kind, self types are Curry-style -- the introduction
and elimination forms have no runtime content. A term `t` of type `iota x. T` is
computationally identical to the same term `t` viewed at type `T[x := t]`. The
self type is purely a type-level discipline. This matters for efficiency: self
types add no runtime overhead.

**Impredicativity.** System S uses an impredicative universe (types can quantify
over all types, including themselves). The Nat encoding above quantifies
`P : Nat -> Type` where `Nat` itself is a type -- this is impredicative. Fu and
Stump prove strong normalization for System S by erasure to F-omega with positive
recursive types. The interaction of impredicativity with self types is delicate
but well-understood in their framework.

**Implicit products (erased quantification).** Cedille/CDLE adds implicit
products `forall x : T. T'` where the argument `x` is erased at runtime. This
is important for the encoding: the induction motive `P` does not appear in the
erased (computational) term. Without implicit products, Church numerals would
need to carry the motive as a runtime argument, changing the computational
behavior. In Kind/Formality, erased arguments are marked explicitly.

**No separate dependent intersection.** Fu and Stump's original self type
`iota x. T` binds `x` in `T` where `x` refers to the term being typed. Stump
later generalized this in CDLE to **dependent intersections** `iota x : T1. T2`,
where a term simultaneously has type `T1` and type `T2[x := t]`. This is
strictly more general: `iota x. T` is `iota x : T. T` (the term satisfies `T`
when `T` mentions itself). For Nat encoding, CDLE uses the two-component form:
the first component is the Church Nat (cNat), and the second is the induction
principle parameterized by the first. This avoids the mutual recursion between
Nat and its constructors that occurs in the single-self-type version.

### 1.7 Known Issues and Subtleties

**Large elimination.** A "large elimination" is one where the motive `P` returns
a type rather than a term -- e.g., `P : Nat -> Type` where `P 0 = Unit` and
`P (succ k) = Pair Nat (P k)`. Standard self-type encodings support this in
principle, but Jenkins, Stump, and Diehl (2021) showed that making large
eliminations *compute correctly* in Cedille requires additional work. The issue
is that large elimination creates terms at the type level whose definitional
equality must be checked, and impredicative encodings can make this equality
undecidable. Their solution uses a derived notion of extensional type equality
within CDLE. For a system like Och that already accepts undecidable type
checking, this may be less problematic.

**Mutual recursion in definitions.** The single-self-type encoding of Nat
(Section 1.3) has `Nat` referring to `zero` and `succ` in its definition, and
`zero`/`succ` referring to `Nat` in their types. This mutual recursion caused
difficulties for early formalizations. Victor Maia noted this made it "hard to
provide a semantics for self types." Stump's CDLE approach resolves this by
separating the Church encoding (cNat) from the induction encoding, using
dependent intersections to combine them. The single-self-type approach requires
well-founded recursive type definitions.

**Conversion checking and infinite loops.** In Kind2, Victor Maia encountered a
specific practical issue: checking equality of self-encoded types like
`List Nat == List Char` could trigger infinite loops. The self-type unfolds to
mention the type being defined, and naive reduction keeps unfolding. The solution
was to annotate the self binder with its type, enabling a *similarity check*
(component-wise comparison) that avoids full reduction. This is documented in
Maia's GitHub gist on Kind2 type checking.

**Function extensionality.** Maia proved that function extensionality follows
from self types -- a surprising result. Self-dependent function types
`forall f(x : A). B(f, x)` (where the return type depends on both the argument
*and the function itself*) are powerful enough to derive funext. This is a bonus
but also a warning: self types are more expressive than they first appear, and
unexpected principles may be derivable.

**Consistency with general recursion.** Self types alone (System S) are strongly
normalizing. But Och has `fix` for general recursion. In a system with both self
types and unrestricted recursion, logical consistency is lost -- you can prove
any type is inhabited by looping. This is the same situation as Och without self
types (fix already destroys consistency). For Och's purposes this is acceptable:
Och is not a logic, it is a programming language with types. The question is
soundness of the type system (if the type checker says `e : T`, does `e`
evaluate to a value in `T`?), not logical consistency.

### 1.8 Practical Experience from Formality/Kind

Victor Maia built two languages based on self types: **Formality** (later
**Kind1**) and **Kind2**.

**What worked:**
- The core is extremely small. **FormCoreJS**, a reference implementation, is
  ~700 lines of JavaScript with no dependencies. It supports dependent types,
  induction, and theorem proving.
- In FormCoreJS, self types are integrated into the dependent function type:
  `All(eras, self, name, bind, body)` where `self` is a variable that binds the
  function being typed. This means there is no separate self-type former -- it is
  folded into Pi/forall. This is an elegant implementation choice.
- All standard datatypes (Nat, Bool, List, Vec, Sigma, Equality) can be encoded.
  Kind users can manually tweak the self-encodings when the default desugaring
  does not suffice.
- The system compiles all datatypes to pure lambda calculus, enabling
  optimal reduction via interaction nets (the HVM runtime).

**What was difficult:**
- The formal semantics took multiple iterations to get right. Early versions of
  Formality had soundness issues that were only resolved when Stump provided
  the dependent-intersection foundation via CDLE.
- Conversion checking is the main practical bottleneck. Without a termination
  checker, checking `A == B` for complex types can diverge. Kind uses timeouts
  and heuristics (similarity checking) to mitigate this.
- Large eliminations required careful encoding. In practice, users rarely need
  large elimination for everyday programming, but it matters for serious theorem
  proving.
- Error messages are hard. When a self-type check fails, explaining *why* to the
  user is difficult because the failure involves self-referential type
  instantiation.

---

## Part 2: Application to Och

### 2.1 Syntax Changes

Och currently has 6 term formers: `var`, `lam`, `app`, `asc`, `type`, `fix`.
Adding self types requires deciding between several options:

**Option A: Three new forms (most explicit)**

```
e, tau ::= ...
  | iota x. T           -- self type formation
  | selfIntro t          -- self type introduction (or implicit)
  | selfElim t           -- self type elimination (or implicit)
```

This adds 3 forms (bringing the total to 9). But in practice, introduction and
elimination can be implicit -- the type checker can insert them automatically.
A term `t` at type `iota x. T` is computationally identical to `t` at type
`T[x := t]`, so intro/elim have no runtime content.

**Option B: One new form (most minimal)**

```
e, tau ::= ...
  | iota x. T           -- self type formation
```

Introduction and elimination are handled by the type checker implicitly: when
checking `t` against `iota x. T`, unfold to check `t` against `T[x := t]`.
When inferring the type of `t` and finding `iota x. T`, unfold to `T[x := t]`.

This is the most aligned with Och's minimalism. However, it requires the type
checker (absEval) to recognize self types and handle them specially.

**Option C: Fold self into lambda (a la FormCoreJS)**

```
e, tau ::= ...
  | slam x. e           -- self-dependent lambda: like lam, but x refers to the function itself
```

Instead of a separate self type, extend the lambda form to optionally bind the
function itself. This mirrors FormCoreJS's `All(eras, self, name, bind, body)`.

**Recommended approach for Och: Option B.** One new constructor `iota` in the
`Expr` type. Introduction and elimination are implicit in evaluation. This adds
the minimum syntax while gaining dependent elimination. The change to `Expr`:

```lean
inductive Expr where
  | var    : Name -> Expr
  | lam    : Name -> (dom : Expr) -> (body : Expr) -> Expr
  | app    : Expr -> Expr -> Expr
  | asc    : (term : Expr) -> (ty : Expr) -> Expr
  | type   : Expr
  | fix    : Expr -> Expr
  | iota   : Name -> (body : Expr) -> Expr    -- NEW: self type
```

### 2.2 Abstract Evaluation of Self Types

This is the key novel question: how does Och's abstract evaluator handle self
types?

Och's central idea is that abstract evaluation (typing) and concrete evaluation
(runtime) share the same evaluator, diverging only at ascription. Self types
challenge this because they are a purely type-level construct -- there is no
runtime analog.

**Formation: `iota x. T`**

When absEval encounters `iota x. T`, it should treat it as a value (like `lam`
and `type`). The self type is already in normal form. absEval normalizes the
body under the binder:

```
absEval fuel Gamma (iota x T) =
  match absEval fuel ((x, var x) :: Gamma) T with
  | some T' => some (iota x T')
  | none => none
```

This parallels the lambda case: normalize the body with `x` as neutral.

**Introduction: checking `t : iota x. T`**

When the abstract evaluator encounters an ascription `(t : iota x. T)`, it
needs to check that `t : T[x := t]`. In Och's framework, ascription `(e : tau)`
abstractly evaluates to `tau`. So:

```
absEval fuel Gamma (asc t (iota x T)) = absEval fuel Gamma (iota x T)
```

But the well-typedness check must verify `absEval fuel Gamma t <=
T[x := t_concrete]`. This is where it gets subtle -- `T[x := t]` requires
knowing `t`'s value, but at abstract evaluation time, `t` might be abstract.

There are two options:

1. **Lazy approach:** Treat `iota x. T` as opaque in absEval. When the term `t`
   with type `iota x. T` is later *used* (applied to arguments), unfold the self
   type at that point with the actual value of `t`.

2. **Eager approach:** At the ascription point, substitute the abstract value of
   `t` into `T` and check the result. This gives `T[x := absEval(t)]`.

The lazy approach is simpler and more robust. It defers unfolding until the
self-typed value is actually used as an eliminator.

**Elimination: using a self-typed value**

When a term `t` with abstract type `iota x. T` is applied (used as a function),
the abstract evaluator unfolds the self type:

```
-- If absEval fuel Gamma f = some (iota x T), and absEval fuel Gamma a = some aVal:
-- Unfold: f has type T[x := f_value], then apply as usual
absEval fuel Gamma (app f a) =
  match absEval fuel Gamma f with
  | some (iota x T) =>
    -- Unfold self type: replace x with f's value
    let T_unfolded = T.subst x f_value
    -- Now T_unfolded should be a function type; apply it
    ...
```

**This is where the design becomes uncertain.** The self type `iota x. T`
packages the induction principle, but *using* that principle requires unfolding
and applying `T[x := t]`. In standard self-type systems, `t` is an untyped
lambda term, and `T[x := t]` is a type expression. In Och, terms and types are
the same thing, which actually simplifies this: `T[x := t]` is just a
substitution in an `Expr`, which Och already supports.

The concrete evaluator does not need to change at all for self types. At
runtime, a self-typed value is just a lambda. The `iota` wrapper has no
computational content. This preserves Och's "dual evaluation" property: the
concrete evaluator erases `iota` just as it erases `asc`.

```
concEval fuel gamma (iota x T) = concEval fuel gamma T   -- or just T as a value?
```

Actually, `iota` would only appear in type positions, not in terms being
evaluated at runtime. A self-typed *value* like `zero` or `succ k` is a
lambda at runtime. The `iota` only appears in its type annotation.

### 2.3 Subtyping with Self Types

How does subtyping interact with self types?

**Self-to-self subtyping:**

```
iota x. T1 <= iota x. T2   when   T1[x := t] <= T2[x := t]  for all t
```

But "for all t" is not directly checkable. A practical approximation:

```
iota x. T1 <= iota x. T2   when   T1 <= T2   (with x as neutral)
```

This matches Och's existing function subtyping: check covariance of the body
with the bound variable as neutral/abstract.

**Self-to-non-self subtyping:**

```
iota x. T <= U   when   T[x := t] <= U   for some canonical t
```

This is harder. In practice, we unfold: if `t : iota x. T`, then `t : T[x := t]`,
and we check `T[x := t] <= U`. The subtyping check would need to handle iota
unfolding.

**For the `subCheckNF` function in Subtyping.lean:**

```
-- When comparing (iota x T1) with (iota x T2):
--   Check T1 <= T2 with x as neutral (pointwise, like lam bodies)
-- When comparing (iota x T) with some other U:
--   Unfold: check T[x := neutral_x] <= U
-- When comparing some V with (iota x T):
--   V <= T[x := V]  (if V is the value being checked)
```

This is analogous to how Och currently handles lambda subtyping: pointwise
comparison under binders. The `iota` binder is handled similarly to a `lam`
binder in the subtyping checker.

### 2.4 Concrete Worked Example: appendArrays with Self Types

This is the motivating example. Currently, Och cannot type `appendArrays`
because the return type `Array (add n m) T` depends on which branch of `n`
is taken, and Church Nat's eliminator has a fixed return type.

**Step 1: Define Nat with self types in Och syntax.**

```
Nat = iota n. lam(P: lam(_: Nat). Type).
              lam(z: P zero).
              lam(s: lam(k: Nat). lam(_: P (var "k")). P (succ (var "k"))).
              P n
```

Or, using Och's let-binding sugar and being more explicit:

```
-- Nat: a natural number n is a function that, given any predicate P,
-- a base case of type P zero, and a step case, produces P n.
Nat = iota n.
  lam(P: lam(_: Nat). Type).
  lam(z: P zero).
  lam(s: lam(k: Nat). lam(ih: P k). P (succ k)).
  P n
```

**Step 2: Define zero and succ.**

```
zero = lam(P: lam(_: Nat). Type).
       lam(z: P zero).
       lam(s: lam(k: Nat). lam(ih: P k). P (succ k)).
       z

succ = lam(k: Nat).
       lam(P: lam(_: Nat). Type).
       lam(z: P zero).
       lam(s: lam(k': Nat). lam(ih: P k'). P (succ k')).
       s k (k P z s)
```

Note the crucial step in `succ`: `k P z s` has type `P k` (by self-elimination
on `k`), and then `s k (k P z s)` has type `P (succ k)`.

**Step 3: The dependent eliminator.**

```
indNat = lam(n: Nat).
         lam(P: lam(_: Nat). Type).
         lam(z: P zero).
         lam(s: lam(k: Nat). lam(ih: P k). P (succ k)).
         n P z s
```

This is just application -- `n` *is* its own eliminator by virtue of its self
type.

**Step 4: appendArrays using the dependent eliminator.**

Recall:
```
Array = lam(n: Nat). lam(T: Type). n Type Unit (lam(acc: Type). Pair T acc)
```

We want:
```
appendArrays : lam(T: Type). lam(n: Nat). lam(m: Nat).
               lam(a: Array n T). lam(b: Array m T). Array (add n m) T
```

Using the dependent eliminator on `n`:

```
appendArrays = lam(T: Type). lam(n: Nat). lam(m: Nat).
  lam(a: Array n T). lam(b: Array m T).
  (indNat n
    -- Motive P: given k, we want Array k T -> Array (add k m) T
    (lam(k: Nat). lam(_: Array k T). Array (add k m) T)
    -- Base case (k = 0): Array 0 T -> Array (add 0 m) T = Array m T
    -- Array 0 T = Unit, so this receives unit and returns b
    (lam(_: Unit). b)
    -- Step case (k = succ k'):
    -- Given k': Nat, ih: Array k' T -> Array (add k' m) T
    -- Produce: Array (succ k') T -> Array (add (succ k') m) T
    -- Array (succ k') T = Pair T (Array k' T)
    -- Array (add (succ k') m) T = Array (succ (add k' m)) T = Pair T (Array (add k' m) T)
    (lam(k': Nat). lam(ih: lam(_: Array k' T). Array (add k' m) T).
     lam(arr: Pair T (Array k' T)).
       -- Decompose arr into head and tail
       arr (Pair T (Array (add k' m) T))
         (lam(hd: T). lam(tl: Array k' T).
           pair T (Array (add k' m) T) hd (ih tl))))
  a
```

**Step 5: How the abstract evaluator steps through this with abstract `n : Nat`.**

When `n` is abstract (ascribed as `(... : Nat)`), the abstract evaluator sees:

1. `indNat n P_motive base step` = `n P_motive base step`
2. `n : Nat = iota n. (P : Nat -> Type) -> P zero -> ... -> P n`
3. By self-elimination, `n : (P : Nat -> Type) -> P zero -> ... -> P n`
4. The result type is `P_motive n`, which is `Array n T -> Array (add n m) T`
5. Applying this to `a : Array n T` gives `Array (add n m) T`

The abstract evaluator cannot reduce `n P_motive base step` further (n is
abstract), but it knows the result type is `P_motive n` = `Array (add n m) T`.
This is a *stuck application* whose type is inferred from the self type.

This is the key difference from the current system: without self types, the
abstract evaluator sees `n` applied to arguments and gets stuck with return type
`X` (the fixed type parameter). With self types, the return type is `P n`, which
carries the dependency.

**However, there is a subtlety here.** Och's current abstract evaluator does not
"infer types" of stuck applications -- it just returns the stuck application as
a syntactic expression. The self-type approach requires the evaluator to
recognize that a stuck application of a self-typed value should produce a result
whose type is `P n`. This might require extending absEval to track type
information for stuck terms, or it might require a different approach to
handling self-typed values.

One possibility: when absEval encounters `app f a` where `f` evaluates to a
term whose declared type (from the environment) is `iota x. T`, it could:
1. Unfold: `f` has type `T[x := f]`
2. If `T[x := f]` is a function type, apply it to `a`'s abstract value
3. Return the result type

This is a form of **type-directed** abstract evaluation, which Och currently
avoids. Whether this can be integrated while preserving Och's simplicity is an
open question.

### 2.5 What Changes in the Lean Mechanization

**New constructor in `Expr`:**

```lean
inductive Expr where
  | var    : Name -> Expr
  | lam    : Name -> (dom : Expr) -> (body : Expr) -> Expr
  | app    : Expr -> Expr -> Expr
  | asc    : (term : Expr) -> (ty : Expr) -> Expr
  | type   : Expr
  | fix    : Expr -> Expr
  | iota   : Name -> (body : Expr) -> Expr    -- NEW
```

**New case in `subst`:**

```lean
| .iota y body =>
  if y == x then .iota y body  -- x is shadowed
  else .iota y (body.subst x s)
```

**New case in `absEval`:**

```lean
| .iota x body =>
  -- Normalize body under the binder, like lambda
  match absEval fuel ((x, .var x) :: Gamma) body with
  | some body' => some (.iota x body')
  | none => none
```

**New case in `concEval`/`concEvalS`:**

```lean
| .iota _ body => concEval fuel gamma body  -- or: some (.iota x body) as value
```

Since `iota` is a type-level construct, it should probably not appear in
terms being concretely evaluated. If it does appear, the concrete evaluator
can either erase it (like ascription) or treat it as a value.

**New case in `Subtype'`:**

```lean
| iota_body {x : Name} {body1 body2 : Expr} :
    Subtype' body2 body1 -> Subtype' (.iota x body2) (.iota x body1)
```

This mirrors `lam_body`: covariant in the body, same binder name.

**New cases in `subCheckNF`:**

```lean
| .iota x bodyA, .iota y bodyB =>
  let bodyB' := if x == y then bodyB else bodyB.subst y (.var x)
  subCheckNF fuel ((x, .iota x bodyA) :: ctx) bodyA bodyB'
| .iota x body, _ =>
  -- Unfold self type and check
  subCheckNF fuel ctx (body.subst x a_original) b
```

### 2.6 Impact on Existing Proofs

**Monotonicity (`absEval_mono`):** Needs a new `iota` case. This should be
straightforward -- it is structurally identical to the `lam` case. absEval
normalizes the body under a binder, and monotonicity follows by the IH on the
body with the extended environment.

**Soundness (`soundness_gen`):** Needs a new `iota` case. Again structurally
similar to `lam`. The concrete evaluator erases or passes through `iota`, the
abstract evaluator normalizes the body, and the soundness IH relates them.

**Subtype inversion lemmas:** Need `iota` analogs of the existing `lam`
lemmas:
- `Subtype'.iota_rhs_shape`: if `Subtype' e (iota x body)` then `e` is
  an `iota` with related body
- `SubtypeTrans.iota_target_shape`: transitive version
- `SubtypeTrans.iota_inv`: body extraction through transitive closure

These are mechanical -- the proofs would follow the exact same structure as
the `lam` versions.

**What should NOT break:** The existing `var`, `lam`, `app`, `asc`, `type`,
`fix` cases in all proofs should be completely unaffected. Adding a new
constructor to `Expr` means Lean will ask for the new case in every match, but
the existing cases remain unchanged. The `iota` case in each proof would be new
code, not modifications to existing code.

**Estimated effort:** Adding `iota` to Och's Lean mechanization is a medium
task. The syntax change is trivial. The evaluator changes are small. The
subtyping changes are small. The proof changes are moderate -- each existing
proof needs a new case, but each new case follows an established pattern (the
`lam` case). The *hard* part is the app case in soundness/monotonicity: when
`f` evaluates to `iota x. T` (a stuck self-type), how do we handle application?
This requires new reasoning that does not have a `lam` analog.

### 2.7 Risks and Open Questions

**Risk 1: Self types vs. Och's "terms are types" philosophy.**

In standard self-type systems (Cedille, Kind), there is a distinction between
terms and types -- self types live in the type language. In Och, terms and
types are the same. This means `iota x. T` is simultaneously a value and a
type. What value does it represent? Semantically, it represents the *set* of
all terms `t` such that `t : T[x := t]`. This is consistent with Och's
philosophy: a type is a set of values, and `iota x. T` is the set of
self-satisfying values. But it is unusual -- no other system treats self types
as first-class values.

**Risk 2: Abstract evaluation of stuck self-type applications.**

As noted in Section 2.4, when the abstract evaluator encounters `app f a` where
`f` is an abstract self-typed value, it currently has no mechanism to infer the
result type. This is a gap that would need to be filled, either by:
- Type-directed evaluation (checking `f`'s declared type in the environment)
- Returning a stuck `app` and relying on later subtyping checks
- Extending the evaluator to track types of stuck terms

This is the single largest open design question.

**Risk 3: Interaction with `fix`.**

`fix` provides general recursion. A fixpoint function with a self-typed return
value could create subtle issues. For instance, `fix (lam f : iota x. T. body)`
-- the abstract evaluator currently handles `fix` by returning the declared
domain type. If the domain is `iota x. T`, the evaluator would return the self
type, which would need to be unfolded when the fixpoint is applied. This should
work but needs careful verification.

**Risk 4: Conversion checking divergence.**

As Kind2 experienced, checking equality of self-typed expressions can diverge
when the self type unfolds recursively. Och already accepts undecidable type
checking, but infinite loops in practice are still undesirable. The mitigation
strategies from Kind2 (similarity checking, timeouts) may be needed.

**Risk 5: Subtyping for self types may be more complex than outlined.**

The subtyping rules in Section 2.3 are approximate. A more careful analysis
might reveal that self-type subtyping requires the system to know *which*
value is being checked, not just compare types structurally. For example,
`3 <= Nat` currently works because Och's subtyping checker normalizes and
compares pointwise. With self types, checking `3 <= iota n. T` requires
checking `3 : T[n := 3]`, which involves substituting a value into a type --
a different operation from structural comparison.

**Risk 6: The alternative -- extending partition/narrowing.**

It is worth considering whether Och's existing partition mechanism (Section 4.2
of the spec) could be extended to achieve dependent elimination *without* self
types. The abstract evaluator already partitions on Church-encoded eliminators:
when `isZero n` is applied with abstract `n : Nat`, the evaluator narrows `n`
to `0` in the true branch and `succ k` in the false branch. If this narrowing
could refine *return types* (not just environments), it might achieve the same
effect as self types for the specific case of Church-encoded data, without
adding a new type former. This would be a novel approach with no precedent in
the literature, and formalizing it would be significantly harder than adopting
self types, but it would preserve Och's existing 6-form syntax.

**Open question: Is `iota` alone sufficient, or are implicit products needed?**

In Cedille, implicit products (erased quantification) are essential for the Nat
encoding. The motive `P` is erased -- it does not appear in the computational
term. In Och, all arguments are explicit. This means Church numerals with self
types would carry `P` as a runtime argument, which changes their computational
behavior. Whether this matters depends on whether Och needs the computational
content of Church numerals to match their standard behavior. If Och does need
implicit products, that is a second type former to add, increasing the core
from 6 to 8 forms.

**Open question: Does self-introduction interact with Och's well-typedness checks?**

When Och encounters `(e : tau)`, it checks `e <= tau` (ascription soundness).
If `tau = iota x. T`, the check becomes: does `absEval(e)` satisfy `T[x := e]`?
This substitution of a *term* into a *type* is standard in self-type systems
but novel in Och, where types are not separate from terms. The subtyping
checker would need to handle this case.

---

## References

- Fu, P. & Stump, A. (2014). "Self Types for Dependently Typed Lambda Encodings."
  RTA-TLCA 2014. https://homepage.divms.uiowa.edu/~astump/papers/fu-stump-rta-tlca-14.pdf

- Stump, A. (2018). "Syntax and Typing for Cedille Core." arXiv:1811.01318.
  https://arxiv.org/abs/1811.01318

- Jenkins, C., Stump, A. & Diehl, L. (2021). "Simulating Large Eliminations in Cedille."
  TYPES 2021. https://arxiv.org/abs/2112.07817

- Stump, A. "The Calculus of Dependent Lambda Eliminations" (draft).
  https://homepage.cs.uiowa.edu/~astump/papers/cedille-draft.pdf

- Maia, V. (2018). "About Induction on the Calculus of Constructions."
  https://medium.com/@maiavictor/about-induction-on-the-calculus-of-constructions-581fcfdb89c5

- Maia, V. (2018). "Funext follows from Self-Types."
  https://medium.com/@maiavictor/funext-follows-from-self-types-1a95cdd400d3

- VictorTaelin. Kind2 self-type equality checking gist.
  https://gist.github.com/VictorTaelin/3f748a46e95071e29462b1ac93c294c5

- Burnham, J.C. "A Taxonomy of Self Types."
  https://gist.github.com/johnchandlerburnham/1ac8ee3690917a144b69667359afd6a7

- FormCoreJS. A minimal proof language based on self-dependent types (~700 LOC).
  https://github.com/HigherOrderCO/FormCoreJS

- Kind1 blog: "Beyond Inductive Datatypes."
  https://github.com/HigherOrderCO/Kind1/blob/master/blog/1-beyond-inductive-datatypes.md

- Geuvers, H. (2001). "Induction Is Not Derivable in Second Order Dependent Type Theory."
  TLCA 2001.
