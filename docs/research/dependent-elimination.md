# Research: Dependent Elimination in Minimal Type Theories

This document surveys how various minimal dependent type theories achieve
**dependent elimination** -- the ability for the return type of a pattern match
or eliminator to depend on which constructor was matched. This is the key
capability that Church encodings in standard CoC/System F lack (Geuvers 2001).

The research is motivated by Och's design: Och currently uses Church encodings
for all data, but Church-encoded eliminators only support *non-dependent*
elimination (the return type is fixed across all branches). This document
evaluates approaches for adding dependent elimination, ranging from primitive
inductive types to encoding tricks.

---

## Table of Contents

1. [The Problem: Why Church Encodings Fail](#1-the-problem)
2. [CIC / Coq -- Primitive Inductive Types](#2-cic)
3. [Cedille / CDLE -- Deriving Inductives from a Small Core](#3-cedille)
4. [Self Types (Fu & Stump)](#4-self-types)
5. [Observational Type Theory (Altenkirch & McBride)](#5-ott)
6. [W-Types](#6-w-types)
7. [Decidable Type Checking Approaches](#7-decidable)
8. [Comparison Table](#8-comparison)
9. [Implications for Och](#9-implications)

---

## 1. The Problem: Why Church Encodings Fail {#1-the-problem}

### Geuvers' Theorem (2001)

Herman Geuvers proved that **induction is not derivable in second-order
dependent type theory** (lambda-P2). This result is fundamental:

- It does not depend on the specific encoding chosen (Church, Scott, Parigot, etc.)
- It proves there *cannot exist* any encoding of natural numbers in lambda-P2
  such that the induction principle is satisfied
- The method extends to all data types (booleans, lists, trees, etc.)
- The proof works by constructing a counter-model using saturated sets

**What this means for Och:** In a pure CoC-like system (which Och's core
resembles), you can define `Nat` and its Church numeral constructors, and you
can write a non-dependent eliminator (iterator/recursor). But you *cannot*
derive a dependent eliminator where the return type varies based on which
constructor was matched. For example, you cannot type:

```
-- We want: given n : Nat, produce a proof of P n
-- Church Nat gives: Nat = forall X. X -> (X -> X) -> X
-- Eliminating: n X base step : X   (return type is just X, not P n)
```

The return type `X` cannot mention `n` -- it is universally quantified and
fixed before the elimination begins.

### What Dependent Elimination Looks Like

The goal is a typing judgment like:

```
n : Nat
P : Nat -> Type
z : P zero
s : (k : Nat) -> P k -> P (succ k)
--------------------------------------
elim n P z s : P n
```

The return type `P n` *depends on* which `n` we are eliminating. When `n` is
`zero`, the result has type `P zero`; when `n` is `succ k`, the result has
type `P (succ k)`, and the step function receives the inductive hypothesis
`P k`.

---

## 2. CIC / Coq -- Primitive Inductive Types {#2-cic}

### Overview

The Calculus of Inductive Constructions (CIC), used as the kernel of
Coq/Rocq, takes the most direct approach: **add primitive inductive type
declarations and a primitive match/case construct** to the core calculus.

### What Is Added to the Core

CIC extends the Calculus of Constructions with:

1. **Inductive type declarations** -- a new kind of global declaration that
   introduces a type constructor, its constructors, and its recursor/eliminator
2. **match expressions** -- a primitive case-analysis construct with a
   *motive* (return-type annotation)
3. **fix expressions** -- guarded fixpoints for recursive definitions
4. **Universes** -- a predicative hierarchy Prop, Set, Type(i)

Core term formers: variables, sorts (SProp, Prop, Set, Type_i), dependent
products (Pi), lambda abstractions, applications, let-in, match, fix, and
constants (including constructors and eliminators of inductive types).
Approximately **10-12 term formers** depending on how you count.

### Typing Rule for Match (Dependent Elimination)

The match expression in CIC has the form:

```
match m as x in I a1 ... ap return P with
| c1 y1 ... yk1 => e1
| c2 y1 ... yk2 => e2
| ...
end
```

The key components:
- `m` : the term being matched (the *scrutinee*)
- `as x` : binds the scrutinee as variable `x` in the return type
- `in I a1 ... ap` : binds the index variables of the inductive type
- `return P` : the *motive* -- a type expression that may mention `x` and the indices
- Each branch `ci y1 ... yki => ei` must satisfy: `ei : P[x := ci y1 ... yki]`

The typing rule (simplified):

```
Gamma |- m : I t1 ... tp
P : forall (a1 : A1) ... (ap : Ap), I a1 ... ap -> Sort
For each constructor ci with ci : forall (y1:B1)...(yki:Bki), I u1 ... up:
  Gamma, y1:B1, ..., yki:Bki |- ei : P u1 ... up (ci y1 ... yki)
----------------------------------------------------------------------
Gamma |- match m as x in I a1...ap return P a1...ap x with ... end : P t1 ... tp m
```

The critical insight: **the motive `P` is a function from the indices and
the scrutinee to a sort**. Each branch must inhabit `P` applied to the
specific indices and constructor for that case. The overall result type is
`P` applied to the actual indices and scrutinee.

### Recursors (Lean's Approach)

Lean 4 takes a variant approach: instead of primitive `match` and `fix`,
Lean's kernel has **recursors** generated from inductive declarations.
Pattern matching is elaborated into applications of recursors.

A recursor for `Nat` looks like:

```
Nat.rec : {P : Nat -> Sort u} ->
          P zero ->
          ((n : Nat) -> P n -> P (succ n)) ->
          (n : Nat) -> P n
```

The motive `P` plays the same role. This is computationally equivalent
to CIC's match+fix but packaged as a single primitive.

### Properties

- **Termination checker:** Yes, required. CIC uses syntactic guardedness
  for fixpoints (structural recursion on a decreasing argument). Lean uses
  a more sophisticated termination checker.
- **Core size:** Medium-large. Approximately 10-12 term formers plus the
  inductive declaration mechanism.
- **Soundness:** Well-studied. CIC's metatheory has been extensively
  formalized (e.g., MetaCoq). Known subtleties include:
  - The interaction of impredicativity (Prop) with large elimination
  - Guard condition for fixpoints is complex and has had bugs
  - Universe polymorphism adds complexity
- **Decidability:** Type checking is decidable (assuming termination of
  the conversion check, which is guaranteed by the guardedness condition).

### References

- Coq/Rocq Reference Manual, "Typing rules": https://rocq-prover.org/doc/V8.18.0/refman/language/cic.html
- Barras et al., "A New Elimination Rule for the Calculus of Inductive Constructions" (2008)
- Sozeau et al., MetaCoq project for formalized metatheory

---

## 3. Cedille / CDLE -- Deriving Inductives from a Small Core {#3-cedille}

### Overview

Cedille implements the **Calculus of Dependent Lambda Eliminations (CDLE)**,
designed by Aaron Stump. CDLE is the most relevant existing system for Och
because it derives inductive types (with dependent elimination!) from a small
core that has *no primitive inductive types*.

### What Is Added to the Core

CDLE extends the (extrinsically typed, impredicative) Calculus of Constructions
with exactly **three new type formers**:

1. **Dependent intersection types** `iota x : T . T'`
   - A term `t` inhabits `iota x:T. T'` iff `t : T` and `t : T'[x := t]`
   - The key insight: `T'` can refer to `t` itself, but viewed through
     the "weaker lens" of type `T`
   - Introduction: if `t : T` and `t : T'[x := t]`, then `t : iota x:T. T'`
   - Elimination (two projections): from `t : iota x:T. T'`, derive
     `t : T` (first projection) or `t : T'[x := t]` (second projection)

2. **Implicit products** `forall x : T . T'`
   - Like Pi types but the argument is *erased* -- it does not appear in
     the untyped term
   - Introduction: if `t : T'[x := a]` for all `a : T` (with `x` not
     free in the erasure of `t`), then `t : forall x:T. T'`
   - Elimination: from `t : forall x:T. T'` and `a : T`, derive
     `t : T'[x := a]` (but `a` is erased at runtime)

3. **Untyped equality** `{ t1 = t2 }`
   - States that two untyped (erased) terms are beta-eta equal
   - Inhabited by *any* term whenever `t1` and `t2` are beta-eta equal
     (proof irrelevance)
   - Used to cast/transport terms between provably equal types

### How Dependent Elimination Is Derived

The key technique uses **Leivant's observation**: a Church-encoded natural
number can simultaneously serve as both an iterator *and* a proof of its
own induction principle. CDLE's dependent intersections connect these two
views.

The encoding works as follows:

```
-- Standard Church Nat (non-dependent)
cNat = forall X : Type . X -> (X -> X) -> X

-- Inductive Nat: intersection of being a cNat AND satisfying induction
Nat = iota n : cNat . (P : cNat -> Type) ->
      P czero ->
      ((m : cNat) -> P m -> P (csucc m)) ->
      P n
```

A natural number `n` of type `Nat` is simultaneously:
- A Church numeral (first component of the intersection)
- A proof that `P n` holds for any predicate `P` closed under zero/succ
  (second component, which refers to `n` from the first component)

The induction principle falls out directly: given `n : Nat`, project out
the second component, which has type
`(P : cNat -> Type) -> P czero -> (...) -> P n`. This *is* the dependent
eliminator -- the return type `P n` depends on `n`.

### Properties

- **Termination checker:** No traditional termination checker. CDLE is
  Curry-style (extrinsically typed) -- the term language is just the
  untyped lambda calculus. Type checking is *undecidable* in principle.
  In practice, Cedille lets the user set a timeout.
- **Core size:** Very small. The term language is just lambda, application,
  and variables (the untyped lambda calculus). The *type* language adds
  Pi, forall (implicit), iota (intersection), equality, plus type-level
  lambda/application. Approximately **6-8 type formers** on top of the
  untyped lambda calculus. The entire type checker (Cedille Core) is
  approximately 1000 lines of Haskell with 20 typing rules.
- **Soundness:** CDLE's logical consistency has been established but the
  proofs are more delicate than CIC's:
  - Strong normalization is proven by erasure to F-omega with positive
    recursive types
  - The interaction of impredicativity + dependent intersections requires
    careful treatment
  - Large eliminations (where the return type is itself a type, not just
    a term) require additional encoding work -- see Jenkins et al.,
    "Simulating Large Eliminations in Cedille" (2021)
- **Decidability:** Type checking is undecidable. Conversion checking for
  the untyped lambda calculus is undecidable in general.

### References

- Stump, "The Calculus of Dependent Lambda Eliminations" (draft): https://homepage.cs.uiowa.edu/~astump/papers/cedille-draft.pdf
- Stump, "Syntax and Typing for Cedille Core" (2018): https://arxiv.org/abs/1811.01318
- Jenkins et al., "Simulating Large Eliminations in Cedille" (2021): https://arxiv.org/abs/2112.07817
- Cedille documentation: https://cedille.github.io/docs/about.html

---

## 4. Self Types (Fu & Stump) {#4-self-types}

### Overview

Self types, introduced by Peng Fu and Aaron Stump (2014), are the
theoretical predecessor to CDLE's dependent intersections. They add a
single type construct `iota x. T` (where `x` refers to the term being
typed) to enable dependent elimination for lambda-encoded data.

### What Is Added to the Core

Self types add **one new type former** to a type-assignment version of CoC:

- **Self type** `iota x . T` -- the type `T` may refer to the term `x`
  being typed

Plus supporting infrastructure:
- Miquel's implicit products (erased quantification)
- Restricted recursive type definitions (for well-foundedness)

The resulting system is called **System S**.

### Typing Rules

```
Self-Formation:
  Gamma, x : T |- T : Type
  -------------------------
  Gamma |- iota x. T : Type

Self-Introduction:
  Gamma |- t : T[x := t]
  -----------------------
  Gamma |- t : iota x. T

Self-Elimination:
  Gamma |- t : iota x. T
  -----------------------
  Gamma |- t : T[x := t]
```

The introduction rule is remarkable: to show `t : iota x. T`, you must
show `t : T[x := t]` -- the type `T` is allowed to mention the very
term `t` being typed. This is *not* circular because `T` is a type
expression, not a computation.

### How Dependent Elimination Works

With self types, `Nat` can be defined as:

```
Nat = iota n . (P : Nat -> Type) ->
      P zero ->
      ((k : Nat) -> P k -> P (succ k)) ->
      P n
```

The self-type binds `n` to the numeral itself. So a natural number `n`
has type `(P : Nat -> Type) -> P zero -> (...) -> P n`. Applying `n`
to a predicate `P`, a base case, and a step function yields something
of type `P n` -- exactly the induction principle.

This is essentially the same mechanism as CDLE's dependent intersections
but presented as a single primitive rather than as an intersection of
two types. (CDLE's `iota x:T. T'` generalizes this by allowing two
distinct types to be intersected.)

### Formality / Kind (Victor Maia)

Victor Maia (VictorTaelin) built programming languages **Formality** and
**Kind** based on self types. In these languages:

- `$self` is used to define an inductive datatype as its own elimination
  principle
- `@T` instantiates constructors
- `~` eliminates (unfolds) self types
- All data types desugar to pure lambda calculus
- The entire language compiles to lambdas and nothing else

This demonstrates that self types are practical, not just theoretical.

### Properties

- **Termination checker:** System S proves strong normalization by erasure
  to F-omega with positive recursive types. No separate termination
  checker is needed for the core theory. In practice (Formality/Kind),
  a termination checker or fuel-based approach may be used.
- **Core size:** Extremely small. The term language is the untyped lambda
  calculus. One type former (self type) is added on top of CoC's
  existing type formers. Approximately **4-5 type formers** total
  (Pi, self, implicit product, plus type-level lambda/application).
- **Soundness:** Strong normalization of System S is proven. However:
  - The interaction of self types with impredicativity requires care
  - Victor Maia noted that the formal semantics were initially unclear;
    Stump later provided rigorous foundations via dependent intersections
  - Function extensionality is derivable from self types (Maia 2018),
    which is surprising and required careful verification
- **Decidability:** Type checking is undecidable (same issue as CDLE --
  conversion checking for untyped lambda calculus).

### References

- Fu & Stump, "Self Types for Dependently Typed Lambda Encodings" (2014): https://homepage.divms.uiowa.edu/~astump/papers/fu-stump-rta-tlca-14.pdf
- Maia, "About Induction on the Calculus of Constructions" (blog post): https://medium.com/@maiavictor/about-induction-on-the-calculus-of-constructions-581fcfdb89c5
- VictorTalin GitHub gist explaining how Kind does this (2024): https://gist.github.com/VictorTaelin/3f748a46e95071e29462b1ac93c294c5

---

## 5. Observational Type Theory (Altenkirch & McBride) {#5-ott}

### Overview

Observational Type Theory (OTT) is primarily about *equality* rather than
elimination, but it has important implications for dependent matching.
OTT combines the benefits of intensional type theory (decidable type
checking) with extensional type theory (function extensionality, proof
irrelevance for propositions).

### What Is Added to the Core

OTT's core includes:

1. **Equality types** -- both type equality and heterogeneous term equality
2. **Coercion** -- `coerce : (A = B) -> A -> B`, transports terms along
   type equalities, with type-directed computation rules
3. **Coherence** -- proves that a term is heterogeneously equal to its
   coercion
4. **Reflexivity** constructors for equalities
5. Standard type formers: Pi, Sigma, Bool, Nat, a universe

The Simplified OTT (SOTT, by Bob Atkey) has approximately **11 major
constructs**.

### Dependent Elimination

OTT handles dependent matching through the standard approach (primitive
eliminators for each inductive type) but with an enhanced equality theory:

- Each inductive family has *at least two* eliminators: one classical
  and one "up to propositional equality"
- The coercion mechanism is type-directed: `coerce` at function type
  produces a function, at pair type produces a pair, etc.
- Equality proofs are proof-irrelevant: all proofs of the same equality
  are definitionally equal

The key contribution is not a new elimination mechanism per se, but
rather making dependent elimination *work better* by providing a richer
notion of equality. In standard intensional type theory, you often need
the K axiom (uniqueness of identity proofs) to complete dependent pattern
matches. OTT avoids K by building in the right computational behavior
for equality.

### McBride's Dependent Pattern Matching

Conor McBride's PhD thesis (1999) showed how to **compile** dependent
pattern matching (as written by programmers in Epigram-style) down to
*eliminators* plus a heterogeneous equality type (John Major equality / JMeq).
This compilation:

- Translates user-written pattern matches into sequences of eliminator
  applications
- Uses equality proofs to refine types in each branch
- Requires the K axiom (or an equivalent) for completeness in the
  intensional setting
- Jesper Cockx later showed how to do "Pattern Matching Without K"
  (2014) for HoTT compatibility

### Properties

- **Termination checker:** Yes, OTT has primitive inductive types with
  structural recursion.
- **Core size:** Medium-large. OTT's full specification is substantial
  (approximately 11+ type/term formers).
- **Soundness:** Canonicity is proven (any closed term reduces to a
  canonical value). Strong normalization holds.
- **Decidability:** Type checking is decidable. This is a key design
  goal -- OTT achieves extensional equality principles while retaining
  decidable conversion.

### References

- Altenkirch & McBride, "Towards Observational Type Theory" (2006): https://personal.cis.strath.ac.uk/conor.mcbride/ott.pdf
- Altenkirch, McBride & Swierstra, "Observational Equality, Now!" (2007): https://personal.cis.strath.ac.uk/conor.mcbride/obseqnow.pdf
- Atkey, SOTT implementation: https://github.com/bobatkey/sott
- McBride, "Dependently Typed Functional Programs and their Proofs" (PhD thesis, 1999)
- Cockx, "Pattern Matching Without K" (2014): https://jesper.sikanda.be/files/pattern-matching-without-K.pdf

---

## 6. W-Types {#6-w-types}

### Overview

W-types (well-founded tree types) are the classic way to represent *all*
strictly positive inductive types via a **single type former**. Introduced
by Per Martin-Lof in his Intuitionistic Type Theory, they provide a
uniform representation of tree-structured data.

### What Is Added to the Core

W-types add exactly **one type former** with one constructor and one
eliminator:

**Formation:**
```
A : Type    B : A -> Type
--------------------------
W x:A . B(x) : Type
```

Intuition: `A` is the type of "node labels" and `B(a)` is the type of
"children positions" for a node labeled `a`. A tree is a node with a
label `a : A` and a child for each position in `B(a)`.

**Introduction (sup constructor):**
```
a : A    f : B(a) -> W x:A. B(x)
----------------------------------
sup(a, f) : W x:A. B(x)
```

**Dependent Elimination (W-rec / W-elim):**
```
P : W A B -> Type
step : (a : A) -> (f : B(a) -> W A B) ->
       ((b : B(a)) -> P (f b)) ->
       P (sup a f)
w : W A B
------------------------------------------
wrec P step w : P w
```

**Computation rule:**
```
wrec P step (sup a f) = step a f (lambda b. wrec P step (f b))
```

### Examples of Encodings

Natural numbers:
```
Nat = W x : Bool . (if x then Empty else Unit)
-- Bool labels: true = zero (no children), false = succ (one child)
-- zero = sup(true, absurd)      -- no children since B(true) = Empty
-- succ n = sup(false, \_ => n)  -- one child (the predecessor)
```

Lists:
```
List A = W x : Maybe A . (case x of Nothing => Empty | Just _ => Unit)
-- Nothing = nil (no children), Just a = cons a (one child = tail)
```

Binary trees:
```
BTree A = W x : Maybe A . (case x of Nothing => Empty | Just _ => Bool)
-- Nothing = leaf, Just a = node a (two children indexed by Bool)
```

### Properties

- **Termination checker:** W-types inherently support well-founded
  recursion via the eliminator. The computation rule is structurally
  recursive. However, encoding complex inductive types (mutual,
  nested, indexed families) as W-types can be awkward and may require
  identity types.
- **Core size:** Minimal addition. One type former (W), one constructor
  (sup), one eliminator (wrec). Approximately **3 new constructs**.
- **Soundness:** W-types are very well-studied. Sound in extensional
  MLTT. In intensional type theory, representing indexed inductive
  families requires identity types, and the equivalence with general
  inductive types is more subtle.
- **Decidability:** Type checking with W-types is decidable (in
  intensional MLTT with the usual conversion rule).
- **Known issues:**
  - Nested and mutual inductive types require non-trivial encodings
    (Altenkirch & Morris, "Representing Nested Inductive Types using
    W-types", 2004)
  - Indexed inductive families (like `Vec : Nat -> Type -> Type`)
    cannot be directly represented -- they require W-types + identity
    types, and the resulting encoding is complex
  - Computational behavior of encoded types can be worse than primitive
    inductives (extra unfolding steps)

### References

- Martin-Lof, "Intuitionistic Type Theory" (1984): https://archive-pml.github.io/martin-lof/pdfs/Bibliopolis-Book-retypeset-1984.pdf
- nLab, W-type: https://ncatlab.org/nlab/show/W-type
- Altenkirch & Morris, "Representing Nested Inductive Types using W-types" (2004)
- 1Lab, W-types: https://1lab.dev/Data.Wellfounded.W.html

---

## 7. Decidable Type Checking Approaches {#7-decidable}

### The Fundamental Tension

In dependent type theory, type checking requires checking equality of
terms (since terms appear in types). This creates a fundamental tension:

- **Extensional type theory (ETT):** Propositional and definitional
  equality coincide. Type checking is *undecidable*.
- **Intensional type theory (ITT):** Definitional equality is restricted
  to computational rules (beta, delta, iota). Type checking is
  *decidable* if all terms in types terminate.
- **Undecidable by default:** If arbitrary (potentially non-terminating)
  terms can appear in types, type equality involves deciding program
  equivalence, which is undecidable.

### Approaches to Decidability

**1. Totality requirement (Coq, Agda, Lean)**

All functions must be total (terminating and covering). This ensures
that conversion checking always terminates. The cost is a termination
checker that restricts what programs can be written.

- Coq: syntactic guardedness condition for fixpoints
- Agda: size-based termination, structural recursion
- Lean: well-founded recursion, structural recursion

**2. Restricted conversion (Cedille approach)**

Accept undecidable type checking. CDLE's term language is the untyped
lambda calculus. Type checking involves beta-eta equality of untyped
terms, which is undecidable. In practice, a timeout is used.

**3. Typed conversion only**

Some calculi restrict conversion to only fire on well-typed terms,
ensuring that reduction always terminates on well-typed terms even if
the untyped lambda calculus has non-terminating terms. This is the
approach of systems like Coq where the guard condition ensures all
fixpoints terminate.

**4. Bidirectional type checking**

Systems like Andras Kovacs' "elaboration zoo" and various implementations
use bidirectional type checking to minimize the amount of conversion
checking needed. This doesn't solve decidability per se but makes
implementations practical.

### Decidable Fragments with Dependent Elimination

**DOT (Dependent Object Types):** The core calculus of Scala 3 has path-dependent
types and has been proven sound, but type checking is undecidable. Decidable
fragments (D<:) have been identified.

**Observational Type Theory:** Achieves decidable type checking while supporting
extensional equality principles. The price is a more complex core theory.

**Martin-Lof Type Theory (intensional):** With W-types and identity types,
provides decidable type checking with dependent elimination. The most
classical approach.

### Relevance to Och

Och explicitly accepts undecidable type checking (see Och spec section 7.6).
This is the same position as Cedille. For Och, the question is not "how to
make type checking decidable" but rather "how to add dependent elimination
while maintaining soundness and the terms-as-types philosophy."

---

## 8. Comparison Table {#8-comparison}

| Approach | New Constructs | Core Size | Dep. Elim. | Termination Checker | Decidable TC | Soundness Status |
|----------|---------------|-----------|------------|--------------------|--------------|--------------------|
| **CIC/Coq** | Inductive decls + match + fix | ~12 term formers | Primitive | Yes (guard condition) | Yes | Well-studied, formalized (MetaCoq) |
| **Lean 4** | Inductive decls + recursors | ~10 term formers | Primitive (recursors) | Yes | Yes | Formalized (Lean4Lean) |
| **Cedille/CDLE** | 3 type formers (iota, forall, eq) | ~8 type formers, untyped terms | Derived via encoding | No | No | SN proven; large elim. requires work |
| **Self Types** | 1 type former (self) + implicit prod | ~5 type formers, untyped terms | Derived via encoding | No (SN proven) | No | SN proven for System S |
| **OTT** | Eq types + coercion + coherence | ~11 constructs | Primitive + enhanced eq | Yes | Yes | Canonicity proven |
| **W-Types** | 1 type (W) + 1 ctor (sup) + 1 elim | +3 constructs | Primitive (wrec) | Built into elim rule | Yes | Very well-studied |
| **Och (current)** | None (Church encodings only) | 5 term formers | Not supported | No | No (by design) | In progress |

---

## 9. Implications for Och {#9-implications}

### Option A: Add Primitive ADTs (CIC-lite approach)

Add `data` declarations and a `match` construct with a motive.

**Pros:**
- Well-understood metatheory
- Straightforward to implement
- Clear typing rules

**Cons:**
- Significantly increases core size (from 5 to ~10+ term formers)
- Requires a termination checker for recursive definitions
- Breaks the "no native data types" philosophy
- The motive annotation is an ergonomic burden

### Option B: Add Self Types (Stump/Maia approach)

Add `iota x. T` (self types) to Och's core.

**Pros:**
- Minimal addition: one new type former
- Preserves Church encodings as the data representation
- Dependent elimination emerges naturally
- Aligns with Och's minimalist philosophy
- Proven to work in practice (Formality, Kind)

**Cons:**
- Type checking becomes even more undecidable (Och already accepts this)
- Soundness proofs are more subtle than CIC
- Self-referential typing is conceptually unusual
- Large eliminations (where the motive returns a Type) require extra work

**Fit with Och:** Self types are strikingly compatible with Och's
"terms are their own most precise types" philosophy. In Och, a value
already *is* its type. Self types formalize exactly this: `iota x. T`
says "the type `T` may refer to the value `x` being typed." This is
essentially what Och already does informally with its abstract
interpretation approach.

### Option C: Add Dependent Intersections (CDLE approach)

Add `iota x:T. T'` (dependent intersections), implicit products, and
equality types.

**Pros:**
- More general than self types alone
- Well-studied in Cedille
- Still preserves Church encodings
- The three additions are each independently useful

**Cons:**
- Three new type formers instead of one
- Equality types add significant complexity
- Implicit products require an erasure discipline
- Curry-style typing may not fit with Och's approach

### Option D: Add W-Types

Add W-types as the sole inductive type former.

**Pros:**
- Very minimal (one type former)
- Covers all strictly positive inductive types in principle
- Well-understood metatheory
- Dependent elimination is built in

**Cons:**
- Encodings of specific types (Nat, List, etc.) are awkward
- Indexed families require identity types (another addition)
- Computational behavior is worse than direct inductives
- Does not preserve Church encodings

### Recommendation

For Och, **Option B (self types)** appears most aligned with the existing
design philosophy:

1. It is the most minimal addition (one type former)
2. It preserves the Church-encoding approach
3. It directly solves the dependent elimination problem
4. The self-referential nature mirrors Och's "terms are types" philosophy
5. It has been proven to work (System S, Formality, Kind)

The key risk is the subtlety of the soundness proof, particularly the
interaction of self types with Och's abstract interpretation semantics.
The Och-specific question would be: does `iota x. T` interact well with
Och's subtyping (`iota x. T1 <= iota x. T2` when `T1 <= T2`?) and
with the abstract evaluator?

A secondary consideration is whether Och's existing mechanism of
"partition on Church-encoded eliminators" (section 4.2 of the spec)
could be extended to achieve dependent elimination *without* self types,
by having the abstract interpreter track which constructor was matched
and refine the return type accordingly. This would be a novel approach
but would need careful formalization.
