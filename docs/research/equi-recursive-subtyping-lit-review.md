# Literature Review: Equi-Recursive Subtyping and Transitivity

## Context

Och has equi-recursive types via `mu x. body` with both self-intro and self-elim by
unfolding, contravariant function domain subtyping, a fuel-bounded evaluator (concrete +
abstract), and ascription `(e : tau)` that splits eval modes. The soundness proof's
ascription case needs transitivity: `v <= sigma` and `sigma <= tau` implies `v <= tau`.
The current inductive SubtypeCore cannot express equi-recursive unfolding or
contra-domain without breaking structural induction for transitivity.

---

## 1. The Amber Rule / Amadio-Cardelli Approach

### Amadio & Cardelli, "Subtyping Recursive Types" (1993)
- **Citation:** Roberto M. Amadio and Luca Cardelli. *Subtyping Recursive Types.* ACM TOPLAS 15(4), 575-631, 1993.
- **Key technique:** The "Amber rule" for equi-recursive subtyping. When comparing `mu alpha. S <= mu beta. T`, introduce a hypothesis `alpha <= beta` into the context and check `S <= T`. The context tracks pairs of type variables assumed to be subtypes.
- **How transitivity is handled:** Transitivity is proved as a metatheorem, not built into the rules. The proof is complex -- it requires showing that the coinductive (tree-based) characterisation (infinite unfoldings are subtypes) corresponds to the syntactic rules. Transitivity of the tree-based relation is easy; the hard part is the correspondence.
- **Mechanized:** Not originally mechanized. Later work showed mechanizing this is quite difficult.
- **Relevance to Och:** The Amber approach is the classical starting point. However, (a) transitivity is notoriously hard to prove for the Amber rules, and (b) the Amber rules require reflexivity to be built in, making them less modular. Since Och needs transitivity for the ascription case, the Amber rules are a poor fit unless we move to the tree-based characterisation.

### Gapeyev, Levin & Pierce, "Recursive Subtyping Revealed" (2000/2002)
- **Citation:** Vladimir Gapeyev, Michael Y. Levin, Benjamin C. Pierce. *Recursive Subtyping Revealed.* ICFP 2000 (Functional Pearl); also JFP 12(6), 511-548, 2002. Also appears as Ch. 21 of *Types and Programming Languages* (Pierce, 2002).
- **Key technique:** End-to-end tutorial on equi-recursive subtyping, from the coinductive tree-based definition to efficient algorithms. The coinductive characterisation is: two types are subtypes iff their infinite unfoldings are subtypes (checking this amounts to simulation on infinite regular trees).
- **How transitivity is handled:** Crucially, they observe that **coinductive inference systems with an explicit transitivity rule are trivially true** (you can build an infinite derivation of anything using only transitivity). Therefore, declarative coinductive subtyping must *not* include an explicit transitivity rule; transitivity must either be a metatheorem of the algorithm, or handled via mixed induction/coinduction.
- **Mechanized:** Not mechanized. Tutorial/survey nature.
- **Relevance to Och:** This is the key reference for understanding *why* transitivity is hard with coinductive subtyping. The observation about trivial coinductive transitivity directly applies to Och: if we define subtyping coinductively (to handle mu), we cannot add a transitivity rule. This motivates either (a) proving transitivity as a metatheorem of the algorithmic checker, or (b) using mixed induction/coinduction.

---

## 2. Coinductive Axiomatizations

### Brandt & Henglein, "Coinductive Axiomatization of Recursive Type Equality and Subtyping" (1997/1998)
- **Citation:** Michael Brandt and Fritz Henglein. *Coinductive Axiomatization of Recursive Type Equality and Subtyping.* Fundamenta Informaticae 33(4), 309-353, 1998. (Conference version: TLCA 1997.)
- **Key technique:** A finitary coinduction principle (the "fixpoint rule"): from `A, P |- P` deduce `A |- P`, where the proof of the premise must be *contractive* (i.e., make progress through at least one type constructor). This captures coinductive reasoning within an inductive proof system.
- **How transitivity is handled:** Transitivity is *not* built in as a rule. Instead, the axiomatization is more concise than Amadio-Cardelli because it does not need a separate axiomatization of type equality. The coinductive characterisation via simulation/bisimulation gives transitivity of the semantic relation directly; the fixpoint rule lets you reason about it syntactically.
- **Mechanized:** Not mechanized.
- **Relevance to Och:** The fixpoint/contractivity idea is elegant and relates to Och's `seen` set: the seen set in Och's checker is essentially tracking which pairs have been visited, and the contractivity requirement is analogous to requiring that the checker "makes progress" before revisiting a pair. However, the Brandt-Henglein system does not directly give a transitivity proof for the algorithmic checker.

---

## 3. Mixed Induction and Coinduction

### Danielsson & Altenkirch, "Subtyping, Declaratively" (2010)
- **Citation:** Nils Anders Danielsson and Thorsten Altenkirch. *Subtyping, Declaratively: An Exercise in Mixed Induction and Coinduction.* MPC 2010, LNCS 6120.
- **Key technique:** Mixed induction and coinduction. The structural rules (for function types, products, etc.) are coinductive, while the transitivity rule is inductive. This means: a derivation can unfold types infinitely (coinduction), but any chain of transitive steps must be finite (induction). This avoids the trivial-coinductive-transitivity problem.
- **How transitivity is handled:** Transitivity is *built in* as an explicit rule, but constrained to be inductive (finitely many uses). This is the key innovation: you get a declarative system with explicit transitivity that is not trivial.
- **Mechanized:** **Yes, in Agda.** The formalization uses Agda's native support for mixed induction/coinduction (sized types or musical notation).
- **Types supported:** Function types with top and bottom. Based on Brandt & Henglein's type language.
- **Relevance to Och:** **Highly relevant.** This is the closest existing approach to what Och needs. The mixed induction/coinduction approach lets you have:
  - Coinductive unfolding of `mu` types (via the structural/coinductive layer)
  - Contravariant function subtyping (in the coinductive layer)
  - An explicit transitivity rule (in the inductive layer) for the ascription case
  
  **Challenge for Lean 4:** Lean 4 does not have native mixed induction/coinduction in the way Agda does. You would need to encode this, possibly via step-indexing or well-founded recursion on the inductive part plus coinductive definitions (via QPF or manual encodings) for the coinductive part.

---

## 4. Double Unfolding (Iso-Recursive)

### Zhou, Oliveira & Zhao, "Revisiting Iso-Recursive Subtyping" (2020/2022)
- **Citation:** Yaoda Zhou, Bruno C. d. S. Oliveira, Jinxu Zhao. *Revisiting Iso-Recursive Subtyping.* OOPSLA 2020; extended version in ACM TOPLAS 2022.
- **Key technique:** Replace the Amber rule with a "double unfolding" rule: when comparing `mu alpha. S <= mu beta. T`, unfold *both* sides and compare `S[alpha := mu alpha. S] <= T[beta := mu beta. T]`, tracking which pairs have been seen. This is for *iso*-recursive types, not equi-recursive.
- **How transitivity is handled:** **Transitivity is easy to prove** with the double unfolding rule. This is one of the main selling points over the Amber rule. The rule is also modular (does not require reflexivity built in).
- **Mechanized:** **Yes, in Coq.** Available at [github.com/juda/Iso-Recursive-Subtyping](https://github.com/juda/Iso-Recursive-Subtyping). Uses locally nameless representation.
- **Relevance to Och:** **Very relevant, but with caveats.** Och uses *equi*-recursive types, not iso-recursive. The double unfolding idea is still applicable: in the algorithmic checker, when encountering `v <= mu x. T`, unfold to `v <= T[x := mu x. T]` (and similarly for `mu x. S <= T`). The key insight is that tracking seen pairs of types + double unfolding gives both termination and easy transitivity. This is essentially what Och's `seen` set already does.

### Zhou, Oliveira & Zhao, "Recursive Subtyping for All" (2023)
- **Citation:** Yaoda Zhou, Bruno C. d. S. Oliveira, Jinxu Zhao. *Recursive Subtyping for All.* POPL 2023; also JFP 2023.
- **Key technique:** Extends iso-recursive subtyping with bounded quantification (F-sub style). Presents F<=mu calculus. Uses double unfolding.
- **How transitivity is handled:** Type soundness, transitivity, conservativity over F<=, and sound + complete algorithmic formulation all proved.
- **Mechanized:** **Yes, in Coq.** Available at [github.com/juda/Recursive-Subtyping-for-All](https://github.com/juda/Recursive-Subtyping-for-All).
- **Relevance to Och:** Shows that the double-unfolding approach scales to richer type systems. If Och adds bounded quantification or other features, this shows it remains tractable.

---

## 5. Mechanized Soundness for Recursive Subtyping

### Jones & Pearce, "A Mechanical Soundness Proof for Subtyping Over Recursive Types" (2016)
- **Citation:** Timothy Jones and David J. Pearce. *A Mechanical Soundness Proof for Subtyping Over Recursive Types.* FTfJP@ECOOP 2016.
- **Key technique:** Distinguish between *inductive* types (finite representations, as in source code) and *coinductive* types (infinite regular trees, the mathematical ideal). Define subtyping coinductively on infinite trees, then show the algorithmic checker on finite representations is sound w.r.t. the coinductive relation.
- **How transitivity is handled:** Transitivity holds on the coinductive (tree) relation by construction (simulation is transitive). Soundness of the algorithmic checker w.r.t. the tree relation gives transitivity "for free."
- **Mechanized:** **Yes, in Agda.** Code at [github.com/zmthy/recursive-types](https://github.com/zmthy/recursive-types/tree/ftfjp16).
- **Types supported:** Products, unions, recursive types.
- **Relevance to Och:** **Highly relevant.** This is close to Och's approach: prove the algorithmic checker sound w.r.t. a semantic/coinductive relation, and get transitivity from the semantic relation. The Agda mechanization provides a template, though it would need to be adapted to Lean 4.

### Komendantsky, "Subtyping by Folding an Inductive Relation into a Coinductive One" (2012)
- **Citation:** Vladimir Komendantsky. *Subtyping by Folding an Inductive Relation into a Coinductive One.* TFP 2012.
- **Key technique:** Defines a subtype relation that is neither purely inductive nor purely coinductive, using a "fold" construction in a dependently typed language with both inductive and coinductive types.
- **Mechanized:** Formalized in a dependently typed language (Coq-like).
- **Relevance to Och:** Shows another encoding strategy for mixed relations, though less directly applicable than Danielsson-Altenkirch.

---

## 6. Self Types (Cedille / Fu-Stump)

### Fu & Stump, "Self Types for Dependently Typed Lambda Encodings" (2014)
- **Citation:** Peng Fu and Aaron Stump. *Self Types for Dependently Typed Lambda Encodings.* RTA-TLCA 2014.
- **Key technique:** Self types `iota x. T` where `T` can refer to the subject `x` being typed. Allows dependent elimination for lambda encodings. The resulting "System S" achieves dependent pattern matching and induction for Church-encoded data.
- **Soundness:** Strong normalization proved by erasure to F-omega with positive recursive types. Type preservation proved directly.
- **How does this relate to mu?** Self types are *not* the same as equi-recursive mu types. Self types allow a type to refer to *the term being typed*, not to the type itself. However, mu types can be *derived* within CDLE (see below).
- **Relevance to Och:** Och's `mu` types are not self types -- they are recursive types. Self types allow `T` to mention the *value* `x`, while mu types allow `T` to mention *the type itself*. However, the Cedille approach of deriving recursive types from more primitive constructs is interesting for future work.

### Stump, "From Realizability to Induction via Dependent Intersection" (2018)
- **Citation:** Aaron Stump. *From Realizability to Induction via Dependent Intersection.* Annals of Pure and Applied Logic 169(7), 637-655, 2018.
- **Key technique:** Extends lambda-P2 with dependent intersections, proving induction is derivable. Realizability semantics shows consistency.
- **Relevance to Och:** Provides the theoretical foundation for Cedille's metatheory. Not directly relevant to Och's equi-recursive subtyping, but relevant if Och ever wants to derive induction principles.

### Jenkins, Stump et al., "Monotone Recursive Types and Recursive Data Representations in Cedille" (2020)
- **Citation:** Christopher Jenkins and Aaron Stump. *Monotone Recursive Types and Recursive Data Representations in Cedille.* MSCS 2021 (arXiv 2020).
- **Key technique:** Derives mu types within CDLE using Tarski's fixpoint theorem. Uses "casts" (functions provably equal to identity) as a preorder on types, rather than a subtyping judgment. Monotonicity of the type scheme is required as explicit evidence.
- **Soundness:** Existing CDLE metatheory (confluence, logical consistency, normalization) applies automatically -- no new soundness proof needed.
- **How transitivity is handled:** The Cast preorder is reflexive and transitive by construction (composition of casts).
- **Relevance to Och:** The "casts instead of subtyping" idea is interesting. In Och's setting, this would mean proving subtyping by constructing coercion functions. However, Och's `mu` types are primitive (not derived), so this is more of a conceptual alternative than a direct approach.

---

## 7. Soundness via Definitional Interpreters (Fuel-Bounded)

### Amin & Rompf, "Type Soundness Proofs with Definitional Interpreters" (2017)
- **Citation:** Nada Amin and Tiark Rompf. *Type Soundness Proofs with Definitional Interpreters.* POPL 2017.
- **Key technique:** Define a big-step evaluator with a fuel parameter in Coq. Prove soundness by induction on fuel. The evaluator is a *definitional interpreter* (high-level, not a small-step relation).
- **How transitivity is handled:** **Key insight: narrowing and subtyping transitivity only need to hold for runtime objects, not for code that is never executed.** This means inconsistent subtyping contexts are permitted for dead code. Transitivity is proved by induction on fuel, restricted to "valid runtime objects."
- **Mechanized:** **Yes, in Coq.** Covers System F<:, mutable references, and extensions towards DOT.
- **Relevance to Och:** **Extremely relevant -- this is the closest existing work to Och's architecture.** Och also has a fuel-bounded evaluator (both concrete and abstract), and the soundness statement is essentially the same: if abstract eval returns tau and concrete eval returns v, then v <= tau. The Amin-Rompf insight that transitivity only needs to hold for runtime objects is directly applicable to Och's ascription case: in `(e : tau)`, we know `v` is a concrete value (runtime object) and `sigma` is its abstract type, so transitivity `v <= sigma <= tau` only involves runtime values.
  
  **Specific implications for Och:**
  - The fuel metric is the induction measure (same as Och).
  - Subtyping transitivity at runtime is strictly easier than in general.
  - The Coq development provides a concrete template, though Lean 4 does not have the same tactic infrastructure.

### Rompf & Amin, "Type Soundness for Dependent Object Types (DOT)" (2016)
- **Citation:** Nada Amin and Tiark Rompf. *Type Soundness for Dependent Object Types (DOT).* OOPSLA 2016.
- **Key technique:** Same fuel-bounded approach applied to DOT (Scala's core calculus). DOT cannot simultaneously support narrowing and subtyping transitivity in general, but can at runtime.
- **Relevance to Och:** Demonstrates the approach scales to very complex type systems with path-dependent types.

---

## 8. Step-Indexed Logical Relations

### Appel & McAllester, "An Indexed Model of Recursive Types" (2001)
- **Citation:** Andrew W. Appel and David McAllester. *An Indexed Model of Recursive Types for Foundational Proof-Carrying Code.* ACM TOPLAS 23(5), 657-683, 2001.
- **Key technique:** The seminal step-indexed approach. Types are predicates on values indexed by a step count k. A value v has type tau at index k if v behaves like a tau for k steps. Recursive types are well-founded because each unfolding decreases the index.
- **How transitivity is handled:** Transitivity of the logical relation is trivial (it is a semantic relation defined by subset inclusion of value sets at each index).
- **Relevance to Och:** Step-indexing is the standard way to handle recursive types in semantic models. Och's fuel parameter is already a step index. If Och defines `v <= tau` as "the checker accepts v <= tau with any fuel", this is essentially a step-indexed logical relation.

### Ahmed, "Step-Indexed Syntactic Logical Relations for Recursive and Quantified Types" (2006)
- **Citation:** Amal Ahmed. *Step-Indexed Syntactic Logical Relations for Recursive and Quantified Types.* ESOP 2006.
- **Key technique:** Extends Appel-McAllester to quantified types (System F + recursive types). Defines the logical relation syntactically (using operational semantics) rather than domain-theoretically.
- **Mechanized:** Not mechanized in a proof assistant (paper proofs).
- **Relevance to Och:** Shows the step-indexed approach handles both recursive types and polymorphism. If Och adds polymorphism, this is the reference.

### Dreyer, Ahmed, Birkedal, "Logical Step-Indexed Logical Relations" (2011)
- **Citation:** Derek Dreyer, Amal Ahmed, Lars Birkedal. *Logical Step-Indexed Logical Relations.* LMCS 7(2), 2011.
- **Key technique:** Introduces a modal logic (LSLR) with a "later" operator to abstract over step-index arithmetic. Proofs become cleaner because you reason in the logic rather than directly manipulating indices.
- **Relevance to Och:** If step-index proofs become tedious in Lean 4, the LSLR approach (or its successor, Iris) provides better abstractions.

### Timany, Krebbers, Dreyer, Birkedal, "A Logical Approach to Type Soundness" (2024)
- **Citation:** Amin Timany, Robbert Krebbers, Derek Dreyer, Lars Birkedal. *A Logical Approach to Type Soundness.* JACM, 2024.
- **Key technique:** Uses Iris (a higher-order concurrent separation logic in Coq) to build semantic type soundness proofs at a high level of abstraction. Step-indexing is hidden inside Iris's model.
- **Mechanized:** **Yes, in Coq (via Iris).**
- **Relevance to Och:** This is the state-of-the-art for semantic soundness proofs. However, it requires the Iris framework, which has substantial infrastructure. There is a **Lean 4 port of Iris** in progress ([github.com/leanprover-community/iris-lean](https://github.com/leanprover-community/iris-lean)), but its maturity is unclear.

---

## 9. Algebraic Subtyping with Equi-Recursive Types

### Dolan & Mycroft, "Polymorphism, Subtyping, and Type Inference in MLsub" (2017)
- **Citation:** Stephen Dolan and Alan Mycroft. *Polymorphism, Subtyping, and Type Inference in MLsub.* POPL 2017. Also: Dolan's PhD thesis, *Algebraic Subtyping* (2017).
- **Key technique:** Equi-recursive types with union and intersection types, using an algebraic (lattice-theoretic) characterisation of subtyping. Types form a distributive lattice; subtyping is lattice ordering; recursive types are greatest/least fixpoints in the lattice.
- **How transitivity is handled:** Transitivity is immediate from the lattice ordering.
- **Relevance to Och:** If Och ever adds union/intersection types, this is the reference. The algebraic approach gives transitivity for free but requires significant lattice-theoretic infrastructure.

### Chau & Parreaux, "The Simple Essence of Boolean-Algebraic Subtyping" (POPL 2026)
- **Citation:** Chun Yin Chau and Lionel Parreaux. *The Simple Essence of Boolean-Algebraic Subtyping: Semantic Soundness for Algebraic Union, Intersection, Negation, and Equi-recursive Types.* POPL 2026.
- **Key technique:** Proves semantic soundness of Boolean-algebraic subtyping (BAS) using five families of characteristic Boolean homomorphisms. Handles equi-recursive types, union, intersection, and negation.
- **Mechanized:** Artifact available ([zenodo.org/records/17348546](https://zenodo.org/records/17348546)).
- **Relevance to Och:** Demonstrates that semantic approaches to equi-recursive subtyping soundness are feasible. The specific lattice-theoretic machinery is heavier than Och needs, but the idea of semantic homomorphisms for soundness is interesting.

---

## 10. Pure Subtype Systems

### Hutchins (2009) / Abel & Vezzosi (2024), "Pure Subtype Systems Are Type-Safe"
- **Citation:** Abel and Vezzosi. *Pure Subtype Systems Are Type-Safe.* arXiv:2407.13882, 2024.
- **Key technique:** In pure subtype systems (PSS), subtyping *is* the typing judgment -- there is no separate typing relation. Type safety rests on transitivity elimination for higher-order subtyping.
- **Relevance to Och:** The idea of "subtyping as the sole judgment" resonates with Och's Option (a): making the algorithmic checker the subtyping relation itself. PSS does *not* handle recursive types, but the transitivity elimination technique may be adaptable.

---

## 11. Lean 4 Infrastructure Status

### Coinductive Types in Lean 4
- **QPF package:** [github.com/alexkeizer/QpfTypes](https://github.com/alexkeizer/QpfTypes) provides a `codata` command for coinductive types in Lean 4 via quotients of polynomial functors. Status: WIP, does not yet support mutually (co)inductive types.
- **Iris-Lean:** [github.com/leanprover-community/iris-lean](https://github.com/leanprover-community/iris-lean) is a Lean 4 port of Iris. If mature enough, it could provide step-indexed logical relations infrastructure.
- **Native support:** Lean 4 does *not* have native coinduction in its kernel (unlike Agda and Coq). All coinductive reasoning must be encoded.

### Implication for Och
- Mixed induction/coinduction (Danielsson-Altenkirch style) would require manual encoding in Lean 4.
- Step-indexing (Appel-McAllester / Amin-Rompf style) is more natural in Lean 4 because it only uses induction on natural numbers.
- The fuel-bounded approach (Amin-Rompf) is the most directly applicable since Och already has a fuel parameter.

---

## Summary: Recommended Approaches for Och

### Option A: Prove transitivity of the algorithmic checker directly
- **Relevant work:** Zhou-Oliveira-Zhao (double unfolding, Coq); Amin-Rompf (fuel-bounded, transitivity only for runtime objects, Coq).
- **Pros:** Avoids defining a separate declarative subtyping relation. The checker *is* the relation.
- **Cons:** Proving transitivity of an algorithmic checker with fuel, seen sets, and inferType fallback is novel -- no existing mechanization covers exactly this combination.
- **Recommended reading:** Amin-Rompf POPL 2017, Zhou-Oliveira-Zhao OOPSLA 2020.

### Option B: Define a semantic/coinductive subtyping relation, prove checker sound w.r.t. it
- **Relevant work:** Jones-Pearce (Agda); Danielsson-Altenkirch (mixed induction/coinduction, Agda); Gapeyev-Levin-Pierce (tutorial).
- **Pros:** Transitivity of the semantic relation is easy/free. Separates concerns cleanly.
- **Cons:** Requires defining an additional relation and proving the checker sound w.r.t. it. Coinductive definitions in Lean 4 require encoding.
- **Recommended reading:** Danielsson-Altenkirch MPC 2010, Jones-Pearce FTfJP 2016.

### Option C: Step-indexed logical relation
- **Relevant work:** Appel-McAllester 2001; Ahmed 2006; Timany et al. 2024 (Iris).
- **Pros:** Standard, well-understood. Transitivity trivial. Natural fit for Lean 4 (induction on Nat). Och's fuel is already a step index.
- **Cons:** Requires defining a step-indexed value-type relation, which is additional infrastructure. Step-index arithmetic can be tedious without Iris-like abstractions.
- **Recommended reading:** Appel-McAllester 2001, Amin-Rompf POPL 2017.

### Recommended Path for Och
**Option A (Amin-Rompf style)** is the most natural fit because:
1. Och already has a fuel-bounded checker.
2. The key Amin-Rompf insight -- transitivity only for runtime objects -- directly addresses Och's ascription case.
3. It avoids introducing coinductive machinery in Lean 4.
4. The fuel metric provides the induction measure.

The main challenge is handling the `seen` set and `inferType` fallback in the transitivity proof. The Zhou-Oliveira-Zhao double-unfolding technique (tracking seen pairs) provides a template for this part.

---

## References (Sorted by Year)

1. Amadio & Cardelli (1993). *Subtyping Recursive Types.* ACM TOPLAS.
2. Kozen, Palsberg & Schwartzbach (1995). *Efficient Recursive Subtyping.* MSCS.
3. Brandt & Henglein (1998). *Coinductive Axiomatization of Recursive Type Equality and Subtyping.* Fundamenta Informaticae.
4. Gapeyev, Levin & Pierce (2000/2002). *Recursive Subtyping Revealed.* ICFP / JFP.
5. Appel & McAllester (2001). *An Indexed Model of Recursive Types.* ACM TOPLAS.
6. Ahmed (2006). *Step-Indexed Syntactic Logical Relations.* ESOP.
7. Danielsson & Altenkirch (2010). *Subtyping, Declaratively.* MPC.
8. Dreyer, Ahmed & Birkedal (2011). *Logical Step-Indexed Logical Relations.* LMCS.
9. Komendantsky (2012). *Subtyping by Folding.* TFP.
10. Fu & Stump (2014). *Self Types for Dependently Typed Lambda Encodings.* RTA-TLCA.
11. Jones & Pearce (2016). *A Mechanical Soundness Proof for Subtyping Over Recursive Types.* FTfJP.
12. Amin & Rompf (2016). *Type Soundness for DOT.* OOPSLA.
13. Amin & Rompf (2017). *Type Soundness Proofs with Definitional Interpreters.* POPL.
14. Dolan & Mycroft (2017). *Polymorphism, Subtyping, and Type Inference in MLsub.* POPL.
15. Stump (2018). *From Realizability to Induction via Dependent Intersection.* APAL.
16. Zhou, Oliveira & Zhao (2020/2022). *Revisiting Iso-Recursive Subtyping.* OOPSLA / TOPLAS.
17. Jenkins & Stump (2021). *Monotone Recursive Types in Cedille.* MSCS.
18. Zhou, Oliveira & Zhao (2023). *Recursive Subtyping for All.* POPL / JFP.
19. Abel & Vezzosi (2024). *Pure Subtype Systems Are Type-Safe.* arXiv.
20. Timany, Krebbers, Dreyer & Birkedal (2024). *A Logical Approach to Type Soundness.* JACM.
21. Chau & Parreaux (2026). *The Simple Essence of Boolean-Algebraic Subtyping.* POPL.
