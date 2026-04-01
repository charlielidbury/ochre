# Research: Categorical Semantics of Och

This document surveys categorical frameworks relevant to Och's design and
investigates what kind of categorical semantics Och admits. The goal is not to
nail down a single definitive model but to map out the landscape: which existing
categorical structures capture which aspects of Och, where do they fall short,
and what might a purpose-built categorical account look like.

The research is motivated by two questions: (1) which categorical structures
capture which aspects of Och, and (2) more practically, what can categorical
thinking actually *do* for the Och project that direct Lean proofs cannot.

Section 0 addresses the second question up front. The remaining sections survey
the landscape for readers who want the technical details.

---

## Table of Contents

0. [What Can Be Gained?](#0-what-can-be-gained)
1. [Summary of Och's Key Features](#1-key-features)
2. [The Galois Connection: Abstract Interpretation](#2-galois)
3. [Domain Theory and Scott Semantics](#3-domain-theory)
4. [Cartesian Closed Categories](#4-ccc)
5. [Semantic Subtyping (Castagna/Frisch)](#5-semantic-subtyping)
6. [Realizability Models](#6-realizability)
7. [Categorical Abstract Interpretation](#7-categorical-ai)
8. [The "Terms = Types" Collapse](#8-collapse)
9. [Towards a Categorical Model of Och](#9-model)
10. [Open Questions](#10-questions)

---

## 0. What Can Be Gained? {#0-what-can-be-gained}

Och's core metatheory (soundness, monotonicity) is already being proved directly
in Lean. So the question is sharp: what would a categorical perspective give the
project that direct proofs do not?

### High-value directions

**Guiding design decisions for upcoming stages.** This is the biggest payoff.
Categorical structure can surface design mistakes *before* you commit to a
formalization.

- **Are abstract closures the right notion of function type?** The question of
  whether Och is cartesian closed -- i.e., whether abstract closures satisfy the
  universal property of exponentials -- is a concrete design question. If they
  don't, there are functions that Och's type system cannot represent, which would
  be a bug. Checking the universal property categorically is a targeted way to
  find out, without having to encounter the problem downstream in a failed proof.

- **How should unions be added (Och₁)?** Semantic subtyping (Castagna/Frisch)
  has a well-understood categorical story for boolean type algebras (union,
  intersection, negation over a set-theoretic model). Understanding where Och's
  current type lattice sits relative to this -- a bounded distributive lattice?
  a frame? -- constrains the design space for Och₁ and can prevent choices that
  break properties like decidability of subtyping.

- **Compositionality across stages.** Och₀ → Och₁ → ... → Ochre is a sequence
  of extensions. If each stage's semantics is a functor and each extension is a
  natural transformation, later soundness results might follow from earlier ones
  structurally. Whether this actually saves work (vs. reproving from scratch)
  depends on whether the categorical framework is lighter than the direct proofs
  -- unclear, but worth investigating at the Och₁ boundary.

### Moderate-value directions

- **The realizability / PER connection clarifies "terms = types."** Och's most
  distinctive feature -- the most precise type of a value is the value itself --
  corresponds to *singleton PERs* in realizability semantics. This gives a known
  framework to reference in papers and talks, rather than having to explain Och's
  philosophy from scratch every time. It is useful for communication and academic
  positioning, but does not directly advance the Lean formalization.

- **The Galois connection story is clean and cheap.** Soundness is an adjunction
  between posets; monotonicity is functoriality. Stating this takes one paragraph
  and gives readers with a categorical background an instant mental model. Low
  effort, moderate value for exposition.

### Low-value directions (at this stage)

- **Proving Och is a topos.** It almost certainly isn't (no negation types, no
  subobject classifier), and knowing this doesn't help the project.

- **Full domain-theoretic model construction.** Building a continuous-function
  model (Scott domain, solve the recursive domain equation, prove adequacy) is
  a large amount of work. The fuel/step-indexing already works for the Lean
  proofs; the domain-theoretic model would confirm that a denotational semantics
  exists but would not change any design decisions.

- **The 2-categorical story for non-transitive subtyping.** Intellectually
  interesting (the non-transitive `Subtype'` as generating 2-cell, its
  transitive closure `SubtypeTrans` as free composition) but the direct Lean
  proofs already handle lambda inversion fine. This is a "nice to know" rather
  than "need to know."

### Recommendation

Focus categorical investigation on the two design-guiding questions: **(1)** the
universal property of abstract closures (exponentials), and **(2)** the lattice
structure needed for Och₁ unions. Use the Galois connection and realizability
stories for exposition in papers. Defer everything else until a concrete need
arises.

---

## 1. Summary of Och's Key Features {#1-key-features}

For context, here are the features of Och that any categorical semantics must
account for. (See `docs/what-is-och.md` for full details.)

- **Syntax.** Five term formers: variables, lambda abstraction (with domain
  annotation), application, type ascription, and `Type` (top/universe). Plus
  `fix` for recursion.
- **Terms are types.** The most precise type of a value is the value itself.
  Types are sets of values; subtyping is set inclusion.
- **Two evaluators.** Concrete evaluation (`concEval`) and abstract evaluation
  (`absEval`) share identical structure, differing only at ascription: concrete
  eval takes the LHS (the term), abstract eval takes the RHS (the type
  annotation).
- **Closures.** Values include closures (environment + lambda body). Abstract
  evaluation produces "abstract closures" that approximate sets of closures.
- **Subtyping.** A non-transitive base relation `Subtype'` (enabling lambda
  inversion) plus its transitive closure `SubtypeTrans`.
- **Soundness.** If concrete eval produces `v` and abstract eval produces `τ`,
  then `SubtypeTrans v τ`.
- **Monotonicity.** If `Γ₂ ⊑ Γ₁` (pointwise subtyping of environments), then
  `absEval Γ₂ e ⊑ absEval Γ₁ e`.

The combination of (a) typing as abstract interpretation, (b) terms and types
sharing a single syntactic category, and (c) subtyping as literal set inclusion
is unusual enough that no single off-the-shelf categorical framework captures
everything. The sections below examine the relevant pieces.

---

## 2. The Galois Connection: Abstract Interpretation {#2-galois}

### Background

The foundational categorical structure underlying abstract interpretation is the
**Galois connection**. A Galois connection between posets (C, ≤) and (A, ≤) is
a pair of monotone maps α : C → A ("abstraction") and γ : A → C
("concretization") satisfying:

```
α(c) ≤ a   ⟺   c ≤ γ(a)
```

Equivalently, α ∘ γ ≥ id and γ ∘ α ≤ id. This is precisely an adjunction
between the posets viewed as thin categories: α ⊣ γ.

Cousot & Cousot's framework (1977, 2014) formulates all of abstract
interpretation in terms of Galois connections. The concrete domain is the
powerset of program states ℘(S) ordered by ⊆. The abstract domain is some
lattice A ordered by ⊑. Soundness of an abstract interpreter is exactly the
statement that the abstract semantics over-approximates the concrete semantics
through this connection.

### Application to Och

Och's two evaluators fit this pattern, but with an important twist.

**Concrete domain.** The poset of closed values (Expr or CVal) under the
identity (each value is a point).

**Abstract domain.** The poset of abstract types (Expr or AVal) under
`Subtype'`, where `Type` (top) is the maximal element.

**The "abstraction" map.** In standard abstract interpretation, α maps a set of
concrete values to its best abstract approximation. In Och, the closest analogue
is the identity on syntax: the most precise type of a value `v` is `v` itself.
So α is conceptually the injection of values into types. This is degenerate --
α is (morally) the identity, reflecting the "terms are types" design.

**The "concretization" map.** γ maps an abstract type τ to the set of concrete
values that are subtypes of τ: `γ(τ) = { v | SubtypeTrans v τ }`.

**Soundness as Galois connection.** Och's soundness theorem states:

```
concEval γ e = v  ∧  absEval Γ e = τ  ∧  EnvConsistent γ Γ  ⟹  SubtypeTrans v τ
```

This is the statement that the concrete result is in the concretization of the
abstract result: `v ∈ γ(τ)`. This is weaker than a full Galois connection (which
would require α to exist as a total function on sets), but it is the standard
**soundness condition** of abstract interpretation.

**Monotonicity as functoriality.** Och's monotonicity theorem states that
`absEval` is a monotone map from the poset of environments (under `EnvSub`) to
the poset of types (under `Subtype'`). In categorical terms, `absEval(−, e)` is
a functor between thin categories (posets viewed as categories).

### What this captures and what it misses

The Galois connection framework captures Och's soundness and monotonicity
naturally. What it does *not* capture is the higher-order structure: closures,
beta-reduction, and the fact that types themselves are lambda terms that compute.
For that, we need richer categorical structures.

---

## 3. Domain Theory and Scott Semantics {#3-domain-theory}

### Background

Dana Scott's domain theory (1970s) provides denotational semantics for the
untyped lambda calculus by interpreting terms as continuous functions on domains
(particular kinds of partial orders). The key construction is a domain D
satisfying D ≅ [D → D] -- the domain is isomorphic to the space of continuous
functions on itself. This self-referential equation is what makes untyped lambda
calculus interpretable.

A **Scott domain** is a bounded-complete algebraic cpo. The category **Dom** of
Scott domains and continuous functions is cartesian closed, and the solution to
D ≅ [D → D] exists in this category.

### Application to Och

Och's value domain has a similar self-referential structure. A value is either:
- `Type` (the top element)
- A closure `(x, dom, body, env)` where `env` maps names to values

So the value domain V must satisfy something like:

```
V ≅ 1 + (Name × Expr × Expr × (Name →fin V))
```

This is a domain equation of the kind routinely solved in domain theory. The
ordered structure on V is given by `Subtype'`, with `Type` at the top.

**Interpreting abstract evaluation.** Abstract evaluation can be viewed as a
continuous function on this domain: given an environment (a finite map from names
to V) and an expression, it produces a value in V. Monotonicity ensures this
function is order-preserving; if we could show continuity (preservation of
directed suprema), we'd have a standard domain-theoretic interpretation.

**The role of fuel.** Och's evaluators are parameterised by `fuel : Nat`, giving
them a step-indexed flavour. The "true" semantics is the limit as fuel → ∞.
Domain-theoretically, each fuel level gives an approximation, and the sequence
is increasing (more fuel = more defined results). The limit is the least fixed
point of the "one more step" operator, which is exactly how Scott constructs
denotational semantics.

### What this captures

- The self-referential value domain (closures containing environments of values)
- Monotonicity as order-preservation
- Fuel/step-indexing as finite approximation converging to a fixed point
- The existence of a mathematical model in which beta-reduction is well-defined

### What it misses

- The "terms are types" collapse: in standard domain theory, types and values
  live in different universes. In Och, they share a syntax. Domain theory gives
  you a *model* of Och but does not directly explain why terms and types can be
  identified.
- The specific role of type ascription (the only source of information loss).

---

## 4. Cartesian Closed Categories {#4-ccc}

### Background

The Curry-Howard-Lambek correspondence identifies:

| Logic                 | Type Theory      | Category Theory         |
|-----------------------|------------------|-------------------------|
| Implication A ⊃ B     | Function type A → B | Exponential object B^A |
| Conjunction A ∧ B     | Product type A × B  | Product A × B          |
| Truth ⊤               | Unit type           | Terminal object 1      |

The simply typed lambda calculus is the internal language of **cartesian closed
categories** (CCCs). Every CCC gives a model of STLC, and vice versa.

### Application to Och

Och is *not* simply typed -- it has dependent domain annotations, subtyping, and
the "terms = types" collapse. However, the underlying lambda calculus structure
(abstraction + application) still suggests CCC-like structure.

**The category.** One candidate: objects are Och types (i.e., Och values, since
terms are types), and morphisms from A to B are Och closures that, when applied
to any value in A, produce a value in B. Composition is function composition.
The terminal object is `Type` (the top type, which contains everything).

**Problems with this candidate:**
1. **Subtyping.** In a CCC, there is at most one morphism between any two
   objects in a posetal collapse, but Och has both computational morphisms
   (functions) and subtyping morphisms (inclusions). This suggests we need a
   **category enriched over posets** or a **2-category** where subtyping is a
   2-cell.
2. **Exponentials.** In Och, the type of a function `λ(x: A). body` is an
   abstract closure -- not a standard exponential B^A. The abstract closure
   carries the full body and environment, making it strictly more informative
   than an exponential.
3. **Dependent types.** Lambda domain annotations create dependency: the type of
   `λ(x: A). body` depends on the *choice* of A. This goes beyond CCCs into the
   territory of **locally cartesian closed categories** or
   **categories with families**.

### Verdict

Och's lambda calculus structure has CCC-like features, but the subtyping
ordering, dependent annotations, and terms-as-types collapse mean a plain CCC
is too restrictive. The CCC structure lives *inside* whatever Och's categorical
semantics is, but it is not the whole story.

---

## 5. Semantic Subtyping (Castagna/Frisch) {#5-semantic-subtyping}

### Background

Semantic subtyping (Frisch, Castagna, and Hosoya, 2002–2008) interprets types
as sets of values in a model, and defines subtyping as set inclusion:

```
A <: B   ⟺   ⟦A⟧ ⊆ ⟦B⟧
```

This is more expressive than syntactic subtyping: you get boolean operations on
types (union, intersection, negation) for free, and subtyping is decidable if
the model is well-chosen.

The model is typically a **set-theoretic model** D satisfying:

```
D = K + (D → D) + (D × D) + ...
```

where K is a set of base constants. Types are interpreted as subsets of D, and
the key technical result is that D can be constructed as a limit of
approximations (an inverse limit construction, similar to Scott domains).

### Application to Och

Och's design is explicitly inspired by semantic subtyping. The key correspondences:

| Semantic Subtyping | Och |
|----|-----|
| Types are sets of values | Types are sets of values |
| Subtyping is ⊆ | Subtyping is `SubtypeTrans` |
| Model D = K + (D → D) + ... | Values = Type + Closure(Name × Expr × Expr × Env) |
| Boolean type algebra | Not yet in Och (planned for Och₁: unions) |
| Type interpretation ⟦−⟧ | Abstract evaluation `absEval` |

**Key difference: precision.** In Castagna/Frisch, function types A → B are
interpreted as the set of all functions that map A-values to B-values. In Och,
the type of a function is an *abstract closure* -- a specific lambda term that
approximates the function's behavior. This is strictly more precise: an Och
"function type" carries the function's body and captured environment, not just
its input-output contract.

This means Och's function types are **intensional** (they carry computational
content), whereas Castagna/Frisch function types are **extensional** (they only
record input-output behaviour). Categorically, the distinction is between:
- **Extensional:** morphisms in a CCC (characterised by their graph)
- **Intensional:** morphisms in a **realizability model** (characterised by
  their computational witness)

**Categorical structure of semantic subtyping.** Castagna et al.'s model can be
viewed as a **complete Boolean algebra** of types (with union, intersection,
negation). Categorically, this is a Boolean topos structure on the powerset
lattice ℘(D). Och, lacking negation and (currently) unions, lives in a smaller
fragment -- more like a **bounded distributive lattice** or **frame**.

### What this captures

- Subtyping as set inclusion
- The value domain as a recursive equation
- The planned extension to unions (Och₁) and atoms (Och₂)

### What it misses

- The intensional nature of Och's function types (abstract closures vs. sets of functions)
- The dual-evaluator design (semantic subtyping has a single interpretation, not
  two evaluators connected by soundness)

---

## 6. Realizability Models {#6-realizability}

### Background

Realizability (Kleene 1945, modernised by Hyland, Longley, van Oosten, and
others) is a semantics in which types are interpreted as sets of "realisers"
-- programs that witness membership. A **partial combinatory algebra (PCA)** A is
the basic structure: a set with a partial application operation. Types are then
subsets of A (or, more carefully, partial equivalence relations on A).

A **realizability topos** RT(A) is an elementary topos built from a PCA A. Its
objects can be thought of as "sets equipped with computational witnesses." The
internal logic of RT(A) is constructive and validates principles like Church's
Thesis (every total function is computable) and Markov's Principle.

### Application to Och

Realizability is arguably the best categorical fit for Och, because it
naturally handles the "terms are types" collapse.

**The PCA.** Och's values (closures + Type) with application as the partial
operation form a PCA-like structure. Application is partial because applying
`Type` to anything is not a standard beta-reduction (Och treats it specially).

**Types as sets of realisers.** In Och, a type τ denotes the set of values v
with `SubtypeTrans v τ`. This is exactly a "realizability set" -- a subset of
the PCA.

**Terms realise their own types.** In standard realizability, a term t of type A
is a realiser: t ∈ ⟦A⟧. In Och, the most precise type of t is t itself, so t
trivially realises its own most-precise type. This is the "terms = types"
principle restated in realizability language.

**Abstract closures as realisers.** An Och abstract closure `(x, dom, body, Γ)`
can be thought of as a realiser for the function type it represents. The
environment Γ carries evidence of the closure's captured context, which is
exactly the kind of computational witness realizability tracks.

**The value relation `VR_abs`.** The `VR_abs` relation in `Och/Closure.lean`
(which relates concrete closures to abstract closures by requiring pointwise
relatedness of captured environments) is structurally identical to a **logical
relation** or **simulation**. In realizability semantics, such relations are used
to establish adequacy theorems. The fact that Och already has this structure is
evidence that a realizability model is natural.

### The realizability topos connection

If we take Och's value domain V as a PCA and construct RT(V), the resulting
topos would have:
- **Objects:** Sets-with-realisers, where realisers are Och values
- **Morphisms:** Functions tracked by Och closures (a function f : A → B is
  realised by a closure that maps A-realisers to B-realisers)
- **Subobject classifier:** A type Ω where propositions are realised by
  evidence (Och values that witness truth)

Och's soundness theorem would then be a statement about the adequacy of the
realizability interpretation: concrete evaluation produces valid realisers for
the types computed by abstract evaluation.

### What this captures

- Terms and types living in the same universe (realisers and realizability sets
  are both built from the same PCA)
- Closures as computational witnesses
- The value relation VR_abs as a logical/simulation relation
- Soundness as adequacy

### Limitations

- Realizability toposes are constructive and intuitionistic. Och's `Type` (top)
  is a classical element (everything is a subtype of it). This may require
  working with a **modified realizability** variant.
- Och does not currently have a propositions-as-types interpretation -- its
  types are sets of values, not propositions. Extending to a full realizability
  topos would require clarifying the logical content.
- Standard realizability uses *total* combinatory algebras for the cleanest
  theory; Och's partiality (fuel, non-termination from fix) requires **partial
  realizability** (based on partial combinatory algebras), which is less
  well-studied.

---

## 7. Categorical Abstract Interpretation {#7-categorical-ai}

### Background

Recent work by Abramsky et al. and by Ong and others develops a fully
categorical framework for abstract interpretation, going beyond Galois
connections between posets.

**Key paper:** "A Categorical Framework for Program Semantics and Semantic
Abstraction" (arxiv 2309.08822) structures abstract interpretation using:

- **Oplax functors** in the category of posets: these capture how abstract
  domains approximate concrete semantics
- **Lax natural transformations** representing concretizations: these mediate
  between concrete and abstract interpretations functorially
- **Composition of abstractions** via horizontal composition of natural
  transformations

This gives a systematic way to compose and refine abstractions, and to prove
soundness of composed abstract interpreters.

### Application to Och

Och's structure fits this framework well:

1. **The syntactic category.** Let **Syn** be the category whose objects are
   Och expressions and whose morphisms are `SubtypeTrans` relationships. (This
   is a thin category / preorder.)

2. **The concrete semantics functor.** `concEval(γ, −) : Syn → Val` maps
   expressions to their concrete values (given an environment γ).

3. **The abstract semantics functor.** `absEval(Γ, −) : Syn → Typ` maps
   expressions to their abstract types (given an abstract environment Γ).

4. **The concretization natural transformation.** The soundness theorem
   establishes a natural transformation from the abstract functor to the
   concrete functor (via the concretization γ(τ) = {v | v ⊑ τ}).

Monotonicity ensures that these are indeed functors (order-preserving maps
between posets). Soundness ensures the naturality condition.

### Compositional structure

As Och evolves through its planned stages (Och₀ → Och₁ → ... → Ochre), each
extension adds new abstract domain structure (unions, atoms, match, pairs,
ownership). The categorical framework suggests these extensions should be
modelled as **refinements of the abstract domain** -- the base abstraction is
composed with new abstractions via the lax natural transformation machinery.

This could provide a principled way to prove that each stage's soundness
follows from the previous stage's, rather than reproving from scratch.

---

## 8. The "Terms = Types" Collapse {#8-collapse}

This is Och's most distinctive feature and the hardest to capture categorically.
Here we catalogue the structures that come close.

### 8.1 Universes à la Tarski

In Martin-Löf type theory, a **universe à la Tarski** is a type U equipped with
a decoding function `El : U → Type`. Elements of U are *codes* for types, and
`El` maps codes to the types they name. This creates a (partial) collapse: some
terms (elements of U) are also types (via El).

Och goes further: *every* term is a type (the most precise type of itself). This
is like having U = V (the universe of all values) and El = identity. In MLTT
terms, this is a universe that contains everything, including itself -- a
**type-in-type** scenario.

Categorically, a universe à la Tarski is a map `El : U → Ob(C)` in a
**category with families (CwF)** or **comprehension category**. Och's collapse
would require U to be a *universal* object in some sense.

### 8.2 Untyped = Uni-typed

There is an old observation (attributed to Dana Scott and Robert Harper) that
the untyped lambda calculus is not "untyped" but "uni-typed" -- there is one
type, and everything has it. Och's `Type` (top) plays exactly this role: every
value has type `Type`.

But Och also has *more precise* types (every value is its own most precise type),
so it is simultaneously uni-typed (via Type) and precisely typed (via itself).
The subtyping lattice interpolates between these extremes.

Categorically, this is reminiscent of a **slice category** C/Type where every
object sits over the terminal object, but can also sit over more precise objects
via the subtyping morphisms.

### 8.3 PER models and the collapse

In **PER (partial equivalence relation) models**, types are PERs on a PCA, and
terms of a type are equivalence classes. The "type" and "term" levels are both
built from the same raw material (elements of the PCA), with PERs providing the
typing discipline.

In Och's terms: two values v₁, v₂ have the same type τ iff both
`SubtypeTrans v₁ τ` and `SubtypeTrans v₂ τ`. The "type" τ partitions values
into those that are subtypes of it and those that aren't, analogous to how a
PER partitions PCA elements into equivalence classes.

The collapse (term = most precise type of itself) corresponds to the
**singleton PER**: the PER that equates a value only with itself. Every value
induces a singleton PER, and this singleton PER "is" the value's most precise
type.

This is the tightest categorical connection to Och's philosophy that I'm aware of.

### 8.4 Subobject fibrations

In any category with a notion of subobjects (monomorphisms), there is a
**subobject fibration** Sub : C^op → Pos mapping each object to its poset of
subobjects. In Och's categorical model, the subobjects of a type τ are the
more-precise types σ with `SubtypeTrans σ τ`.

The "terms = types" collapse means that the poset of subobjects of Type is the
entire value domain -- every value is a subobject of Type. This fibration
captures the full subtyping lattice.

---

## 9. Towards a Categorical Model of Och {#9-model}

Putting the pieces together, here is a sketch of what a categorical model of
Och might look like.

### The category Och

**Objects.** Och values: closures and Type. These play dual roles as both values
and types.

**Morphisms.** A morphism from A to B is a closure f such that for all v with
`SubtypeTrans v A`, applying f to v yields some w with `SubtypeTrans w B`. That
is, morphisms are *tracked* functions (functions with computational witnesses),
exactly as in realizability.

**Composition.** Function composition, tracked by the closure that composes the
two trackers.

**Identity.** The identity closure λ(x: A). x, which is tracked by itself.

### Structure on Och

- **Terminal object.** `Type` (everything subtypes it).
- **Products.** Church-encoded pairs (once Och has them at stage Och₄).
- **Exponentials.** Abstract closures: the exponential B^A is the abstract
  closure that approximates all functions from A to B.
- **Subobject classifier.** Not clear yet. Och does not have a notion of
  propositions or truth values distinct from types. This is an open question.
- **Subtyping.** A 2-categorical structure: for objects A, B there is a poset
  Hom(A, B) ordered by pointwise subtyping of closures, plus a separate
  "subtyping 2-cell" A ⊑ B (not a morphism, but a relationship between objects).
  Alternatively, subtyping is a **preorder enrichment** on the category.

### The two functors

Let **Syn** be the syntactic category (expressions + subtyping).

- `⟦−⟧_c : Syn × Env → Val` -- concrete evaluation
- `⟦−⟧_a : Syn × Env → Val` -- abstract evaluation

Both are functors (by monotonicity). The soundness theorem is a natural
transformation from `⟦−⟧_c` to `γ ∘ ⟦−⟧_a` (where γ is concretization).

### The Galois-realizability bridge

The model combines:
1. **Galois connections** (soundness, monotonicity) -- the "vertical" structure
   relating concrete and abstract
2. **Realizability** (closures as realisers, values as PCA elements) -- the
   "horizontal" structure giving computational content
3. **Domain theory** (recursive domain equation for values, fuel as
   approximation) -- the "foundational" structure ensuring the model exists

This combination does not correspond to a single named categorical structure in
the literature. The closest existing notion is a **realizability model over a
domain-theoretic PCA, equipped with a Galois connection between concrete and
abstract interpretations**.

---

## 10. Open Questions {#10-questions}

### 10.1 Is the category Och cartesian closed?

For this, we need to show that exponentials B^A exist for all A, B and satisfy
the universal property. Och's abstract closures are candidates for exponentials,
but it's not clear they satisfy the full universal property (every morphism A → B
factors uniquely through eval : A × B^A → B).

### 10.2 Does Och form a topos?

A topos requires a subobject classifier (a type Ω such that subobjects of A
correspond to morphisms A → Ω). Och's type lattice is rich, but without
negation or complement types, it likely forms a **Heyting algebra** at best,
not a Boolean algebra. Whether this yields a topos structure is open.

### 10.3 What happens when unions are added (Och₁)?

Unions (join in the type lattice) would give Och a **lattice** structure on
types. If intersections (meet) are also derivable, we get a distributive
lattice, which is the algebraic backbone of semantic subtyping. The categorical
model would then gain coproducts (union types) and potentially become a
**regular** or **coherent** category.

### 10.4 How does the non-transitive subtyping relate categorically?

Och deliberately uses a non-transitive base relation `Subtype'` (to enable
lambda inversion) with a separate transitive closure `SubtypeTrans`. This is
unusual. Categorically, a non-transitive relation is not a preorder and does not
form a category. The transitive closure *does* form a category (thin category /
preorder), but the proofs work by leveraging the non-transitive version's
structural properties. This two-level approach may correspond to a
**2-categorical** or **double-categorical** structure where `Subtype'` is a
"generating" 2-cell and `SubtypeTrans` is its free composition.

### 10.5 What is the initial algebra / terminal coalgebra story?

In standard categorical semantics, inductive types are initial algebras and
coinductive types are terminal coalgebras. Och uses Church encodings for data
and fix for recursion. The relationship between fix (which constructs coalgebra-
like objects) and Church encodings (which are universal morphisms from initial
algebras) in Och's setting is unclear. This connects to the self-types research
(`docs/research/self-types-for-och.md`).

### 10.6 Does the fuel parameter have categorical meaning?

The fuel/step-indexing could be viewed as defining a **chain of approximations**
in a directed system, with the true semantics as the colimit. This is standard
in domain theory but has categorical content: it means the semantic functors are
really **filtered colimits** of finite approximations. The question is whether
Och's specific fuel structure (uniform across all subterms) gives additional
structure to this colimit.

### 10.7 Can monotonicity be strengthened to continuity?

Monotonicity (order-preservation) gives functoriality between posets. Continuity
(preservation of directed suprema) would give functoriality between **dcpos**
(directed-complete partial orders), which is the standard requirement for
domain-theoretic models. The question is whether Och's abstract evaluation
preserves directed suprema of environments, not just finite approximations.

---

## References

- Cousot, P. & Cousot, R. (1977). "Abstract Interpretation: A Unified Lattice
  Model for Static Analysis of Programs by Construction or Approximation of
  Fixpoints." POPL.
- Cousot, P. & Cousot, R. (2014). "A Galois Connection Calculus for Abstract
  Interpretation." POPL.
- Frisch, A., Castagna, G., & Hosoya, A. (2008). "Semantic Subtyping: Dealing
  Set-Theoretically with Function, Union, Intersection, and Negation Types."
  JACM 55(4).
- Scott, D. (1972). "Continuous Lattices." Springer LNM 274.
- Abramsky, S. & Jung, A. (1994). "Domain Theory." Handbook of Logic in
  Computer Science, Vol. 3.
- van Oosten, J. (2008). *Realizability: An Introduction to its Categorical
  Side.* Elsevier.
- Longley, J. (1995). "Realizability Toposes and Language Semantics." PhD
  thesis, University of Edinburgh.
- Hyland, J.M.E. (1982). "The Effective Topos." Studies in Logic and the
  Foundations of Mathematics 110.
- "A Categorical Framework for Program Semantics and Semantic Abstraction."
  arxiv 2309.08822.
- Jacobs, B. (1999). *Categorical Logic and Type Theory.* Elsevier.
