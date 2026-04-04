# Arithmetic Equality in Dependent Type Systems

## The Problem

When implementing `reverse : Array n T -> Array n T` using an accumulator pattern, the recursive call produces a value of type `Array (add (pred n) (succ m)) T`, but the expected return type involves `Array (add n m) T`. For this to type-check, the system must establish:

```
add (pred n) (succ m) = add n m
```

In Och, natural numbers are Church-encoded:

```
Nat  = \X:Type. \z:X. \s:(X->X). X
add  = \n:Nat. \m:Nat. n Nat m succ
pred = \n:Nat. <pair-based Kleisli trick>
succ = \n:Nat. \X:Type. \z:X. \s:(X->X). s (n X z s)
```

When `n` is an abstract bound variable (not a concrete numeral), `add (pred n) (succ m)` and `add n m` are both *neutral terms* -- stuck on the variable `n`. Since `add` unfolds to `n Nat m succ`, and Church-encoded `pred` cannot reduce on an abstract `n`, these two expressions are structurally different and cannot be made equal by beta-reduction alone.

This is a fundamental challenge: the equality is *propositionally* true (it holds for all concrete `n >= 1`) but not *definitionally* true (the type checker cannot verify it by computation).

---

## 1. Definitional Equality / Conversion Checking

### How Coq, Agda, and Lean Handle This

All three systems use **weak head normal form (WHNF) reduction** followed by structural comparison for definitional equality. The algorithm:

1. Reduce both sides to WHNF
2. If heads match, recurse on subterms
3. If heads differ, try further reductions (delta-unfolding definitions, iota-reduction for pattern matching)

**Key point about neutral terms**: When a term is stuck on an abstract variable (e.g., `add n m` where `n` is universally quantified), reduction halts and the term stays in neutral form. Two neutral terms are definitionally equal only if they are structurally identical -- same head variable, same spine of arguments.

For *inductive* naturals in these systems, `add (suc n) m` reduces to `suc (add n m)` by iota-reduction (the pattern match on the first argument fires). But `add (pred n) (suc m)` does *not* reduce when `n` is abstract, because `pred n` is itself stuck.

**Lean 4 specifics** (Carneiro, "Type Checking in Lean 4"): Lean uses lazy delta reduction with reducibility hints. It does *not* compute full normal forms -- instead it tries to "match up" terms using minimal reductions. For natural number literals, it has special support: `Nat.succ` and `Nat.zero` are recognized and compared structurally. But this does not help with abstract arithmetic.

**What the programmer must do**: In Coq/Agda/Lean, when the type checker encounters `add (pred n) (succ m)` vs `add n m`, the programmer must supply an explicit proof term (of type `add (pred n) (succ m) = add n m`) and use a `rewrite` tactic or `transport` to coerce the term. This proof typically proceeds by induction on `n`.

### Normalization by Evaluation (NbE)

NbE is the dominant technique for conversion checking in dependent type checkers (Agda, Lean, Coq's kernel). The key idea: evaluate terms into a semantic domain, then *read back* (quote) the semantic values into normal forms. Two terms are equal iff their normal forms are syntactically identical after readback.

**How it handles stuck terms.** When evaluation encounters a variable with no binding, it constructs a *neutral value* -- a semantic object representing a stuck computation. Applications where the function is neutral produce larger neutral values rather than failing. NbE will normalize `add (pred n) (succ m)` by unfolding definitions and beta-reducing wherever possible, but will get *stuck* on `n` -- the Church numeral `n` is applied to arguments but `n` itself is a variable, so the fold cannot proceed. The two sides will have different normal forms because the pair-based predecessor leaves syntactic residue around the stuck variable `n`.

### Assessment for Och

| Criterion | Rating |
|-----------|--------|
| Fit with structural subtyping | Poor -- relies on propositional equality and explicit rewrites |
| Implementation complexity | N/A -- Och already has normalization; the *missing* piece is what to do when normalization is not enough |
| Works for Church/Scott encodings | No -- iota-reduction requires inductive types |

**Bottom line**: Definitional equality checking is necessary infrastructure (and Och already has the equivalent in absEval), but it fundamentally cannot solve `add (pred n) (succ m) = add n m` for abstract `n`. The programmer would need to supply a proof, which Och has no mechanism to accept.

### References
- Carneiro, "Type Checking in Lean 4" (https://ammkrn.github.io/type_checking_in_lean4/type_checking/definitional_equality.html)
- Abel, "Normalization by Evaluation: Dependent Types and Impredicativity" (habilitation, 2013)
- Christiansen, "Checking Dependent Types with Normalization by Evaluation: A Tutorial"
- The Rocq Prover reference manual, "Reasoning with equalities" (https://rocq-prover.org/doc/master/refman/proofs/writing-proofs/equality.html)

---

## 2. Congruence Closure / Equational Reasoning

### The Approach

Instead of relying solely on beta-reduction for definitional equality, extend the type checker with a set of known equalities and close under congruence. This is the approach taken by the **Zombie** language (Sjoberg & Weirich, "Programming up to Congruence", POPL 2015).

In Zombie:
- The definitional equality is the **congruence closure** of equations in the typing context
- Equations can come from user-supplied proofs, pattern matching refinements, or axioms
- The type checker automatically applies symmetry, reflexivity, transitivity, constructor injectivity, and rewriting of subexpressions

**Critical design choice in Zombie**: Beta-reduction is *not* part of definitional equality (because Zombie supports general recursion and terms may diverge). Instead, all equalities -- including `(\x. e) v = e[v/x]` -- must be explicitly assumed or proven.

For arithmetic, this means the programmer could prove `add (pred n) (succ m) = add n m` and add it to the context. The congruence closure engine would then automatically apply this equation wherever the LHS pattern appears in types.

### Agda's Rewrite Rules

Agda supports user-defined **rewrite rules** that extend definitional equality. Once registered, a rewrite rule causes Agda to automatically replace instances of the LHS with the RHS during reduction. For example:

```agda
{-# REWRITE plus-zero #-}   -- registers: n + 0 = n
{-# REWRITE plus-succ #-}   -- registers: m + (suc n) = suc (m + n)
```

After registration, `m + 0` reduces to `m` definitionally. This is a form of **equality reflection** -- propositional equalities are promoted to definitional ones.

**Soundness concern**: Rewrite rules can break consistency if they introduce contradictions. Agda provides no built-in guarantee that user-defined rewrite rules are confluent or terminating. Cockx et al., "Type Theory Unchained" (2020) study conditions under which rewrite rules preserve type safety.

### E-Graphs and Equality Saturation

E-graphs are data structures that efficiently represent equivalence classes of terms under a set of equalities. **Equality saturation** repeatedly applies rewrite rules to an e-graph until a fixpoint is reached, building up all equivalent forms simultaneously. This avoids the phase-ordering problem inherent in sequential rewriting.

Recent work has begun applying e-graphs to type checking. The basic idea: represent types as nodes in an e-graph, add known equalities (from beta-reduction, arithmetic laws, user proofs), saturate, and then check whether two types are in the same equivalence class.

### Congruence Closure in Intensional Type Theory

Selsam & de Moura ("Congruence Closure in Intensional Type Theory", 2016) developed an efficient congruence closure procedure that works with dependent types. The main challenge is that in dependent type theory, the types of function arguments can depend on earlier arguments, so merging equivalence classes requires careful handling of type dependencies. Their procedure handles arbitrary dependent functions and relies only on the commonly assumed uniqueness of identity proofs axiom.

### Assessment for Och

| Criterion | Rating |
|-----------|--------|
| Fit with structural subtyping | Moderate -- equalities become bidirectional subtypings; must verify monotonicity |
| Implementation complexity | Medium (basic congruence closure) to Medium-High (e-graphs with saturation) |
| Works for Church/Scott encodings | Yes, if the right equalities are provided |

**Key challenge for Och**: Where do the equalities come from? Och has no proof terms. Options:
1. **Built-in axioms** about arithmetic operations -- hardcoded in the evaluator
2. **Derived automatically** by absEval during symbolic evaluation
3. **Consequences of type refinement** (e.g., if `n <: succ Nat`, then `succ (pred n) = n`)

**Specific proposal**: Rather than full congruence closure, a targeted set of reduction rules for Church-encoded arithmetic could be added to absEval. When absEval encounters neutral applications involving `succ`, `pred`, and `add`, it applies known simplification rules.

### References
- Sjoberg & Weirich, "Programming up to Congruence" (https://www.cs.yale.edu/homes/vilhelm/papers/popl15congruence.pdf)
- Sjoberg, "A Dependently Typed Language with Nontermination" (https://www.sigplan.org/Awards/Dissertation/2016_sjoberg.pdf)
- Selsam & de Moura, "Congruence Closure in Intensional Type Theory" (https://arxiv.org/abs/1701.04391)
- Cockx et al., "Type Theory Unchained" (https://drops.dagstuhl.de/entities/document/10.4230/LIPIcs.TYPES.2019.2)

---

## 3. Self Types / Cedille

### How Cedille Works

Cedille (Stump et al.) is the closest existing system to Och in its approach to data encoding. It uses **self types** (`iota x : T. T'`) -- a dependent intersection where `T'` can refer to the subject of typing `x` -- to derive induction principles for Church/Mendler-encoded datatypes *without* built-in inductive types.

### The Self-Type Mechanism

A self type `iota x : T. T'` types a term `t` if:
1. `t : T`
2. `t : T'[x := t]`

This allows the type of `t` to refer to `t` itself. For natural numbers, this means Church numerals can carry their own induction principle: the type of a Church numeral `n` can state that `n` satisfies any property `P` that is closed under zero and successor.

### Arithmetic in Cedille

Cedille derives the **induction principle** for Church-encoded Nat:

```
NatInd : (n : Nat) -> (P : Nat -> Type) -> P zero -> ((m : Nat) -> P m -> P (succ m)) -> P n
```

Using this induction principle, one can prove arithmetic identities like `add n 0 = n` or `add (pred n) (succ m) = add n m` as propositional equalities. The proofs proceed by induction on `n`, just as in Coq/Agda.

**However**: These are still *propositional* equalities. The type checker does not automatically recognize `add (pred n) (succ m)` as definitionally equal to `add n m`. The programmer must explicitly use the proof to transport/rewrite (via Cedille's `rho` construct).

### Cedille's Curry-Style Advantage

Cedille is **Curry-style** (terms are unannotated; types are erasable). Conversion checking compares unannotated terms, which means some equalities that are blocked in Church-style systems (due to differing annotations) hold definitionally in Cedille. This does not help with the `pred`/`succ` cancellation problem specifically, but it is a useful design principle.

### The Definitional Equality Limitation

Cedille *cannot* establish `succ (pred n) = n` as a definitional equality for abstract `n`. The predecessor uses pair-based iteration that does not beta-eta-reduce to `n` even when wrapped in `succ`. This is the same fundamental limitation as every other system surveyed.

### What Och's Mu Types Already Provide

Och already uses self types (mu types) for recursive types, serving a similar role to Cedille's iota types for equi-recursive self-reference. The appendArrays function in the codebase already uses mu for its recursive type annotation.

### Assessment for Och

| Criterion | Rating |
|-----------|--------|
| Fit with structural subtyping | Good conceptual fit -- Cedille's Curry-style erasure aligns with Och's semantic approach |
| Implementation complexity | High -- deriving induction principles from self types is complex |
| Works for Church/Scott encodings | Yes -- this is exactly what Cedille is designed for |

**Key insight**: Even Cedille, which shares Och's Church-encoding-only philosophy, relies on propositional equality + explicit rewriting for equations beyond beta-eta. **No existing system establishes `succ (pred n) = n` as a definitional equality.** This is a genuinely hard problem.

**What Och could borrow**: The technique of using self types to derive eliminators that carry more type information. If the eliminator for `Nat` could express that `n = succ (pred n)` for nonzero `n`, this could potentially be used in the subtype checker.

### References
- Fu & Stump, "Self Types for Dependently Typed Lambda Encodings" (https://homepage.divms.uiowa.edu/~astump/papers/fu-stump-rta-tlca-14.pdf)
- Stump, "Generic Derivation of Induction for Impredicative Encodings in Cedille" (https://homepage.cs.uiowa.edu/~astump/papers/cpp-2018.pdf)
- Stump, "Dependently typed programming with lambda encodings in Cedille" (https://homepage.cs.uiowa.edu/~astump/papers/tfp-2016.pdf)
- Jenkins, McDonald, Stump, "Monotone Recursive Types and Recursive Data Representations in Cedille" (https://ar5iv.labs.arxiv.org/html/2001.02828)

---

## 4. Ornaments / McBride-Style Approaches

### The "Faking It" Paper

McBride's "Faking It: Simulating Dependent Types in Haskell" (JFP 2002) demonstrates encoding dependent-type-like reasoning in a language without full dependent types using type-level computation via type classes. The key insight is using type-level proxies ("counterfeit copies") of data to guide computation. This is specifically about simulating dependent types in non-dependent languages -- the opposite direction from Och's needs.

### With-Abstraction and Views (Agda/Epigram)

In Agda, the **with-abstraction** mechanism allows pattern matching on intermediate computations, which refines the types of other terms in scope. The **rewrite** keyword lets you use a propositional equality to rewrite the goal:

```agda
f n rewrite add-pred-succ n m = ...
-- where add-pred-succ : (n : Nat) -> NonZero n -> add (pred n) (succ m) = add n m
```

This is syntactic sugar for transport along the equality proof.

The common arithmetic issue in Agda illustrates the problem well: `0 + m` computes to `m` (by definition of `add` matching on the first argument), but `m + 0` does *not* reduce definitionally -- it requires a proof by induction. The `rewrite` mechanism exists precisely because definitional equality is insufficient for such cases.

### Assessment for Och

| Criterion | Rating |
|-----------|--------|
| Fit with structural subtyping | Poor -- requires propositional equality types and explicit proof terms |
| Implementation complexity | N/A (not applicable to Och's architecture) |
| Works for Church/Scott encodings | No -- relies on pattern matching on inductive types |

**Bottom line**: These approaches fundamentally depend on (1) propositional equality types, (2) a mechanism to use equality proofs to rewrite goals, and (3) inductive types with pattern matching. Och has none of these.

### References
- McBride, "Faking It: Simulating Dependent Types in Haskell" (JFP, 2002)

---

## 5. SMT-Based Approaches

### How They Work

**Liquid Haskell**, **F\***, and **Dafny** outsource proof obligations to SMT solvers (typically Z3). The workflow:

1. The type checker generates verification conditions (VCs) from the program
2. VCs are encoded as first-order logic formulas, with types becoming predicates
3. The SMT solver attempts to prove the formulas valid
4. If the solver succeeds, the program type-checks

**F\*** (from official documentation): F\* encodes all types into a single SMT sort `Term` with boxing/unboxing. Arithmetic on `int` maps to SMT's built-in linear arithmetic theory. Natural numbers are refinements of integers: `nat = x:int{x >= 0}`. Uses "fuel-instrumented" versions of recursive functions to prevent divergence -- `HasTypeFuel` predicates guard recursive unfolding. Type checking in F\* is undecidable because Z3 can check validity of formulas with universal and existential quantification over infinite ranges.

**Liquid Haskell**: Restricts refinements to an SMT-decidable logic (linear arithmetic + uninterpreted functions). The key advantage: `add (pred n) (succ m) = add n m` is trivially provable by Z3's integer arithmetic theory if `n >= 1`. Refinement types are of the form `{v : T | p}` where `p` is a logical predicate.

**Dafny**: Does not use dependent types; instead uses pre/post-conditions and loop invariants. All arithmetic reasoning is handled by Z3. Array lengths are runtime values with specification-level constraints rather than type-level indices.

### Assessment for Och

| Criterion | Rating |
|-----------|--------|
| Fit with structural subtyping | Moderate -- architectural tension between abstract interpretation and SMT |
| Implementation complexity | Very High -- encoding Church numerals to SMT is non-trivial |
| Works for Church/Scott encodings | Partially -- requires mapping higher-order encoded data to first-order SMT |

**Advantages**:
- SMT solvers are *very* good at arithmetic. The equality `add (pred n) (succ m) = add n m` for `n >= 1` is trivial for Z3.
- Well-tested technology with decades of engineering.

**Disadvantages**:
- **Architectural mismatch**: Och's type checker is an abstract interpreter (absEval). Introducing an SMT solver creates a second, fundamentally different reasoning engine.
- **Encoding Church numerals for SMT**: Church-encoded naturals are higher-order functions. SMT solvers work in first-order logic. The encoding would need to map Church numeral operations to SMT integer arithmetic, losing the structural connection to the actual terms.
- **Soundness**: Any bug in the encoding could introduce unsoundness. F\*'s encoding is thousands of lines and has had soundness issues.
- **Undecidability**: SMT solving is undecidable in the theories F\* uses. Type checking becomes unpredictable -- small changes can cause timeouts.
- **Dependency**: Adds a large external dependency (Z3) to a currently self-contained system.

### References
- Vazou et al., "Liquid Haskell: Experience with Refinement Types in the Real World" (https://goto.ucsd.edu/~nvazou/real_world_liquid.pdf)
- F\* tutorial, "Understanding how F\* uses Z3" (https://fstar-lang.org/tutorial/book/under_the_hood/uth_smt.html)
- Vazou et al., "Abstract Refinement Types" (https://goto.ucsd.edu/~rjhala/liquid/abstract_refinement_types.pdf)

---

## 6. Structural / Encoding Tricks

### The Core Question

Is there an encoding of natural numbers where `add (pred n) (succ m)` reduces to `add n m` by beta-reduction alone, even when `n` is abstract?

### Analysis of Encodings

**Church encoding** (what Och currently uses):
- `add n m = n Nat m succ` -- applies `succ` n times to `m`
- `pred n` uses the Kleisli/pair trick -- O(n) and stuck on abstract `n`
- `add (pred n) (succ m)` reduces to `(pred n) Nat (succ m) succ`, which is `fst (n PairNN (pair 0 0) step) Nat (succ m) succ` -- stuck on `n`
- Meanwhile `add n m` reduces to `n Nat m succ` -- structurally different
- **Verdict**: Does not reduce.

**Scott encoding**:
- `succ n = \z. \s. s n`
- `pred (succ n) = n` -- reduces in one step! (constant time)
- But `add n m` must be defined recursively (linear time), stuck on abstract `n`
- **Verdict**: `pred (succ n)` reduces, but `pred n` for abstract `n` is still stuck.

**Parigot encoding** (combination of Church and Scott):
- Carries both the Church-style iterator and the Scott-style destructor
- `pred` is O(1), `add` is O(n)
- Still stuck on abstract `n` for the same reasons
- Representation size is O(2^n) without sharing
- **Verdict**: Does not help with the core problem.

**Mendler-style encoding** (used in Cedille):
- Provides constant-time predecessor while maintaining linear representation size
- More practical than Parigot, but same fundamental limitation on abstract variables

### The Fundamental Limitation

**No lambda encoding can make `pred` reduce on an abstract variable `n`.** The reason is information-theoretic: `pred n` requires *inspecting* `n` (is it zero or successor?), and if `n` is abstract, there is nothing to inspect. This is not an encoding problem -- it is an information problem.

An encoding where `succ (pred n) = n` holds definitionally for all `n` would require `pred` and `succ` to be literal inverses at the syntactic level. But `succ` adds structure (wraps in a lambda) while `pred` must *count* to remove structure. This asymmetry between construction (O(1)) and destruction is fundamental.

### The Most Promising Trick: Avoid `pred` Entirely

Instead of using `pred` explicitly, restructure algorithms to use the Church numeral's **built-in iteration**:

```
-- Instead of: reverse n arr = go n arr empty
--   where go n arr acc = if n == 0 then acc else go (pred n) (tail arr) (cons (head arr) acc)

-- Use: the Church numeral n as the loop driver
reverse n arr = n (\(arr, acc). (tail arr, cons (head arr) acc)) (arr, empty) .snd
```

This eliminates `pred` entirely. The Church numeral `n` guarantees exactly `n` iterations. The type of the fold ensures the accumulator grows by one and the input shrinks by one at each step, without needing to prove `add (pred n) (succ m) = add n m`.

**Limitation**: Not all algorithms can be restructured this way. Algorithms that need random access to the "remaining count" (not just decrement-and-recurse) may still need `pred`.

### Assessment for Och

| Criterion | Rating |
|-----------|--------|
| Fit with structural subtyping | High -- pure computation, no new type theory |
| Implementation complexity | Low -- just restructure algorithms |
| Works for Church/Scott encodings | Yes -- this is the natural pattern for Church data |

### References
- Wikipedia, "Church encoding" (https://en.wikipedia.org/wiki/Church_encoding)
- Wikipedia, "Mogensen-Scott encoding" (https://en.wikipedia.org/wiki/Mogensen%E2%80%93Scott_encoding)
- Stump, "Efficiency of lambda-encodings in total type theory" (https://www.cambridge.org/core/journals/journal-of-functional-programming/article/efficiency-of-lambdaencodings-in-total-type-theory/61BB015E068EAC16C6C31D5F7654F3AD)
- Gonzalez, "Morte: an intermediate language for super-optimizing functional programs" (https://hackage.haskell.org/package/morte)

---

## 7. Cubical Type Theory / HoTT

### The Approach

Cubical type theory provides a computational interpretation of paths (equalities). The key primitive is **transport**: given a path `p : A = B` in the universe, and a value `a : A`, you get `transport p a : B`. In cubical type theory (Cohen, Coquand, Huber, Mortberg 2018), transport *computes* -- it reduces to a concrete value when the path and the value are concrete.

### How It Helps with Arithmetic

In cubical Agda, you can prove `add (pred n) (succ m) = add n m` by induction on `n`, obtaining a path. Then `transport` along this path converts a value of type `F (add (pred n) (succ m))` to one of type `F (add n m)`.

When `n` is concrete, the transport reduces away entirely. When `n` is abstract, the transport remains as a neutral term, but the *types match* because the path witnesses their equality.

Cubical type theory also provides **function extensionality** as a theorem (not an axiom), and canonicity for natural numbers: given a derivation of `t : Nat`, there is a unique `n` such that `t` computes to `S^n 0`.

### Assessment for Och

| Criterion | Rating |
|-----------|--------|
| Fit with structural subtyping | Very Poor -- requires identity/path types, which Och lacks |
| Implementation complexity | Very High -- interval variables, face constraints, Kan composition, glue types |
| Works for Church/Scott encodings | No -- assumes inductive types with eliminators |

**The one useful insight**: Transport as computation (rather than as an axiom) aligns with Och's philosophy of types-as-computation. If Och ever introduces an equality type, a computational interpretation would be the natural choice.

### References
- Cohen, Coquand, Huber, Mortberg, "Cubical Type Theory: A Constructive Interpretation of the Univalence Axiom"
- Angiuli, Harper, Wilson, "Syntax and Models of Cartesian Cubical Type Theory" (https://www.cs.cmu.edu/~rwh/papers/uniform/uniform.pdf)

---

## 8. Supercompilation / Partial Evaluation

### The Approach

Supercompilation (Turchin, 1986) and partial evaluation evaluate programs *more aggressively* than standard reduction by symbolically executing with abstract variables and case-splitting on unknowns.

**Key operations:**
- **Driving**: Symbolically evaluate, unfolding function definitions and propagating abstract variables
- **Case splitting**: When a variable is encountered in a decision position, branch on its possible forms
- **Generalization**: When driving produces growing terms, generalize to a common pattern
- **Folding**: Detect when a previously seen configuration is reached, creating a loop

### How It Could Help

For `add (pred n) (succ m)`:
1. **Case split on n**: Either `n = zero` or `n = succ k`
2. **Zero case**: `add (pred zero) (succ m) = add zero (succ m) = succ m`. And `add zero m = m`. So `succ m != m` -- the equality does not hold at zero. (This is correct -- the equality only holds for `n >= 1`.)
3. **Successor case**: `pred (succ k) = k` (reduces). So `add (pred (succ k)) (succ m) = add k (succ m)`. And `add (succ k) m = succ (add k m)`. We need `add k (succ m) = succ (add k m)`, which is itself provable by induction on `k`.

The supercompiler discovers that the equality holds in the successor case but must perform *inductive reasoning* to establish the remaining equality. This is the same hard problem -- supercompilation can automate the case-split but not the inductive step.

### Morte: Fusion via Normalization

Morte (Gabriel Gonzalez) is a minimal Calculus of Constructions implementation where all data is Church-encoded. Its sole optimization is beta-eta normalization, which automatically fuses composed Church-encoded operations:
- `map f . map g` normalizes to `map (f . g)`
- `map id` normalizes to `id`

This works because Church-encoded data *is* the fold -- composing two operations creates beta redexes that the normalizer eliminates. However, this only works for *closed* terms. Open terms with abstract variables get stuck, just as in Och.

### Assessment for Och

| Criterion | Rating |
|-----------|--------|
| Fit with structural subtyping | Moderate -- case splitting aligns with abstract interpretation |
| Implementation complexity | High -- full supercompilation; Medium for targeted case splitting |
| Works for Church/Scott encodings | Partially -- helps with case splits but not inductive steps |

**Most relevant insight for Och**: absEval could perform **case refinement** -- when a branch narrows a variable to a specific form (e.g., `n` is known nonzero), substitute `n = succ k` and re-evaluate. This is a limited form of supercompilation that aligns with Och's abstract interpretation philosophy and is planned for later stages (flow sensitivity / match).

### References
- Turchin, "The concept of a supercompiler" (1986)
- Bolingbroke & Peyton Jones, "Supercompilation by Evaluation" (https://dl.acm.org/doi/10.1145/2088456.1863540)
- Gonzalez, "Morte" (https://hackage.haskell.org/package/morte)
- Sorensen, Gluck, Jones, "Towards Unifying Partial Evaluation, Deforestation, Supercompilation, and GPC" (ESOP 1994)

---

## Recommendations for Och

### Ranking by Feasibility

| Rank | Approach | Feasibility | Impact | Complexity | Notes |
|------|----------|-------------|--------|------------|-------|
| 1 | **Encoding tricks (avoid pred)** | High | Medium | Low | Restructure algorithms to use Church iteration |
| 2 | **Targeted reduction rules in absEval** | High | High | Medium | Built-in arithmetic simplifications |
| 3 | **Lightweight congruence closure** | Medium | High | Medium | Close known equalities under congruence |
| 4 | **Case refinement in absEval** | Medium | High | Medium | Branch on forms of abstract variables |
| 5 | **E-graphs / equality saturation** | Medium | High | Medium-High | More general than (3) |
| 6 | **SMT as optional oracle** | Medium | Very High | Very High | Fallback for complex arithmetic |
| 7 | **Self-type-derived eliminators** | Low-Medium | Medium | High | Cedille-style induction principles |
| 8 | **Supercompilation (full)** | Low | Medium | High | Diminishing returns vs case refinement |
| 9 | **Cubical / HoTT** | Very Low | Low | Very High | Massive architectural change |
| 10 | **McBride-style rewrite** | Very Low | N/A | N/A | Requires propositional equality |

### Detailed Recommendations

#### Tier 1: Do Now

**1. Restructure algorithms to use Church iteration (avoid `pred`)**

The cheapest intervention. For `reverse`, instead of an accumulator that explicitly decrements a counter, use the Church numeral itself as the loop driver:

```
reverse n arr = n (\(arr, acc). (tail arr, cons (head arr) acc)) (arr, empty) .snd
```

This eliminates `pred` entirely. The Church numeral `n` guarantees exactly `n` iterations. The fold's type ensures the accumulator grows and the input shrinks at each step, without needing `add (pred n) (succ m) = add n m`.

**Limitation**: Not all algorithms can be restructured this way.

#### Tier 2: Targeted Enhancement to absEval

**2. Add arithmetic reduction rules to absEval**

Extend absEval with pattern-based reductions for common Church-numeral identities. When absEval encounters neutral applications involving `succ`, `pred`, and `add`, apply known simplification rules:

- `pred (succ n) -> n` (always valid, even for Scott encoding this is immediate)
- `succ (pred n) -> n` (when `n` is known nonzero, i.e., `n <: succ Nat`)
- `add n zero -> n`
- `add zero n -> n` (already reduces with Church encoding)
- `add (succ n) m -> succ (add n m)`
- `add n (succ m) -> succ (add n m)`

These rules would be built into the evaluator, not user-definable. Each rule must be validated for soundness with respect to the semantic subtyping model.

**Key subtlety**: The rule `succ (pred n) -> n` is only valid when `n >= 1`. Och's subtype checker would need to determine that `n` has type `succ Nat` (i.e., is nonzero) before applying this rule. This is a form of **refinement** -- the rule is conditional on type information.

**Implementation**: A small term rewriting system layered on absEval's existing normalization. Rules fire only on neutral terms (when beta-reduction is stuck). Confluence of the combined system (beta + arithmetic rules) needs verification.

**3. Case refinement in absEval**

When the abstract evaluator enters a branch where `n` is known to be nonzero (e.g., after `isZero n` returns false), refine `n` to `succ k` for a fresh variable `k` and continue evaluation. Under this substitution, `pred (succ k)` computes, and `add k (succ m)` can be compared with `add (succ k) m`.

This is essentially what supercompilation does, applied in a targeted way. It aligns with Och's abstract-interpretation philosophy and connects to the flow sensitivity planned for Och_3.

#### Tier 3: Future Consideration

**4. Lightweight congruence closure**

If targeted rules become insufficient, maintain a set of equalities between normal-form expressions and close under congruence using an e-graph. The equalities could be derived from:
- Beta-reduction (already handled by absEval)
- The arithmetic rules above
- Type information (if `n : succ Nat`, then `succ (pred n) = n`)

The subtype checker would consult the e-graph: `a <: b` if `a` and `b` are in the same equivalence class.

**5. SMT as an oracle (very long term)**

If Och eventually needs complex arithmetic (e.g., associativity of addition), an SMT solver could serve as an optional fallback:
- absEval normalizes as much as possible
- If subCheckNF fails on arithmetic terms, generate an SMT query
- Map Church-numeral operations to integer arithmetic
- If Z3 says "valid", accept the subtyping

This keeps the SMT solver as a fallback, preserving Och's self-contained architecture.

### The Fundamental Tension

The core tension for Och is between:

1. **Autonomy of the type checker**: Och's philosophy is that typing *is* abstract interpretation -- the type checker should figure things out by computing, not by checking proofs supplied by the programmer.

2. **Inductive reasoning is required**: The equality `add (pred n) (succ m) = add n m` is inherently an inductive fact. No amount of beta-reduction can establish it for abstract `n`. Something beyond pure computation is needed.

The approaches above resolve this tension in different ways:
- **Encoding tricks** side-step the issue by restructuring computation to avoid the problematic pattern
- **Targeted rules** hard-code specific inductive facts into the evaluator (the evaluator "knows" arithmetic)
- **Case refinement** automates the case-split step of inductive reasoning, though not the inductive step itself
- **Congruence closure / SMT** provide general-purpose reasoning engines that can handle arbitrary equalities

For Och's current stage (proving soundness of the core calculus), the recommendation is to start with encoding tricks and targeted rules. These are minimally invasive and sufficient for immediate goals like type-checking `appendArrays` and `reverse`. More general approaches (case refinement, congruence closure) can be explored once the core is stable and the need for them is demonstrated by concrete examples.
