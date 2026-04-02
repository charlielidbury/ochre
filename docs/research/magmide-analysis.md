# Magmide: Research Analysis for Ochre

## 1. What is Magmide?

Magmide is a dependently-typed proof language created by Blaine Hansen, intended to make provably correct bare metal code possible for working software engineers. The project's tagline is "Correct, Fast, Productive: pick three."

**Core vision:** Create a single unified tool where engineers can write high-performance imperative code, logically prove the code correct, and compile/run that code -- all within the same language ecosystem. The explicit goal is to take formal verification out of academia and into mainstream software engineering.

**Relationship to existing systems:**

- **Coq:** Magmide's Logic language is based on the Calculus of Constructions, the same foundation as Coq. Coq was intended to bootstrap Magmide's first version. Hansen views Coq as powerful but hopelessly academic -- "more knife than handle" -- with terrible ergonomics, clunky tooling, and documentation written for review committees rather than practitioners. Magmide aims to be "what Rust is to C" but for proof assistants relative to Coq.

- **Rust:** Rust serves as the "Host" language in Magmide's architecture. The plan was: build Magmide (the proof assistant) in Rust, formalize Rust's semantics inside Magmide (following RustBelt/Iris), then build a "reflective proof rule" that lets Magmide formally certify actual Rust code. Rust is to Magmide what OCaml is to Coq.

- **Iris separation logic:** Central to the design. Hansen sees Iris as the key breakthrough that makes verifying imperative code practical. Magmide's entire approach to reasoning about mutation, concurrency, and unsafe code was planned to be built on Iris. Hansen studied Iris extensively (the repo contains detailed notes on Iris internals, step-indexing, resource algebras, etc.).

- **F\*:** Hansen considers F\* "frustratingly close" to Magmide's goals but criticizes it for muddying pure logic with effectful computation, using SteelCore (a weaker separation logic than Iris), and remaining too academic.

- **Lean:** Viewed as a cleaner Coq that still makes the mistake of overemphasizing pure functional programming and conflating the logical and computational layers.

**The key architectural insight** is what Hansen calls the "split Logic/Host" architecture:

```
         represents and
           implements
  +------------+------------+
  |            |            |
  v            |            |
Logic          +---------> Host
  |                         ^
  |                         |
  +-------------------------+
        logically defines
          and verifies
```

Logic (dependent type theory, purely compile-time) defines and constrains Host (imperative Rust code, runs on real machines). Host implements both Logic and itself. Hansen frames this as "Logic is the type system of Host, which just happens to itself be a dependently typed functional programming language."


## 2. Magmide's Technical Approach

### Type Theory

- **Calculus of Constructions** (CIC variant), same foundation as Coq.
- **No `Set` type:** Uses `Type{0}` uniformly, avoiding the Coq confusion between `Set` and `Type`.
- **Proof-irrelevant `Prop`:** Explored making `Prop` proof-irrelevant (following HoTT research), though this was not finalized.
- **Unified inductive/coinductive types:** Single `ind` keyword; whether a type is used inductively or coinductively would be inferred from context (recursive vs. corecursive function usage).
- **Asserted types (subset types):** Built-in syntax for subset types like `nat & < 256` or `Person & .age >= 18`, which are syntactic sugar over dependent pairs with proofs. This is a broader variant of liquid/refinement types.
- **Anonymous union types:** `bool | nat | str` as syntactic sugar for one-off discriminated unions.

### Handling Systems-Level Concerns

- **Mutation and ownership:** Entirely delegated to Iris separation logic. The plan was to formalize Rust's ownership/borrowing semantics using Iris (following RustBelt), then reason about imperative code using separation logic predicates. Hansen explicitly rejected the pure functional approach: "real computers aren't pure or functional... every action is impure and effectful."

- **Memory layout:** Not directly addressed. Magmide planned to eventually formalize LLVM or build an LLVM analogue to reach all the way to hardware semantics. Memory model details were deferred.

- **Trackable Effects:** A planned system where dangerous operations (like potential panics) require giving up a piece of a "correctness token." Effects are composable *resources* (following Iris's Iron obligation management), not wrappers. This would allow gradual verification -- you can write unverified code, but the effect system tracks what safety conditions remain unproven. Custom trackable effects could be defined for domain-specific safety properties. This system was explicitly described as "handwaving goes here" in the design docs.

- **Corruption panics vs. assumption panics:** A planned distinction between panics caused by hardware failure (provably impossible under hardware axioms) and panics contingent on unproven logical conjectures.

### Compilation Strategy

- **Phase 1:** Build a proof assistant in Rust (Magmide = Logic language).
- **Phase 2:** Formalize Rust semantics inside Magmide (translating Iris and RustBelt).
- **Phase 3:** Build "Host reflection" rule -- given an AST of a Rust function + a Magmide proof that this AST is a "certifier," compile and run the certifier as a reflective proof.
- **Phase 4 (long-term):** Extend formal foundations to hardware, verify LLVM/compiler, self-verify the proof checker via MetaCoq-style bootstrapping.

### Metaprogramming

Tactics would be written in Rust (not an interpreted language like Coq's Ltac), giving bare-metal performance for proof search. The tactic system would be a metaprogrammatic entrypoint, not baked in -- users could define their own tactic languages. Three syntactic entrypoints: inline macros, block macros, and file-level import macros.

### Performance Strategy

Hansen identified proof assistant performance as a critical barrier to mainstream adoption. The plan was:
1. Rust-native tactics (not interpreted).
2. Aggressive incremental compilation to avoid re-running proof search.
3. Heavy use of computational reflection (running certifier functions instead of checking large proof terms).


## 3. Current Status

**The project is effectively dormant.** Key evidence:

- The entire git history was squashed to a single commit on April 1, 2024 ("going back to bare bones"), suggesting a reset or abandonment.
- The repo has 836 GitHub stars and 15 forks, but zero open issues (all 18 historical issues are closed).
- Last push was April 1, 2024.
- The README prominently states: "Magmide is purely a research project at this point. This repo is still very early and rough, it's mostly just notes, speculative writing, and exploratory theorem proving."

**What was actually implemented:**

The implementation is minimal. The Rust source code (`src/`) contains:
- A basic parser (using `nom`) for an indentation-sensitive syntax supporting type definitions, procedures, match expressions, and access chains.
- A rudimentary type checker that handles: unit types, union types, procedures with parameters, match expressions, and simple assignability checking (equality-based).
- Tests covering basic type errors and a "day of week" example from Software Foundations.
- An AST with types for `Term`, `TypeBody` (Unit/Union), `ProcedureDefinition`, `LetStatement`, `MatchArm`.
- A `main.rs` that is entirely commented out.

There is no:
- Dependent type checking
- Universe hierarchy
- Proof objects or tactics
- Separation logic
- Iris integration
- LLVM/assembly formalization
- Any form of compilation to machine code

The `theory/` directory contains Coq explorations: a formalization of a simple assembly-like instruction language with `Inst_Add`, machine state as string maps, and instruction stepping -- but no proofs about it beyond stubs.

The `old/` directory contains earlier attempts at a checker and parser in Rust, plus Coq formalizations.

**What was thoroughly developed:** The *design documentation* is extensive and thoughtful. The `posts/` directory contains detailed essays on the design philosophy, comparisons with other projects, tutorials on verification concepts, and Iris study notes. The README and design docs represent the most complete artifact of the project.


## 4. Comparison to Ochre

### Shared Goals

Both Magmide and Ochre aim to be "Rust + Dependent Types in one language" -- a systems programming language with full dependent types for verification. Both:
- Want to verify properties of imperative, mutable, systems-level code
- Reject the pure functional paradigm as the interface for systems programmers
- Want dependent types not just for types but for proving arbitrary properties
- See existing proof assistants as too academic and inaccessible
- Want to be practical tools for working engineers

### Fundamental Architectural Differences

**Magmide: Two-language split architecture.**
Logic (CIC/CoC, pure, compile-time) is a separate language from Host (Rust, imperative, runtime). They have a symbiotic relationship but are explicitly different languages with different semantics. Separation logic (Iris) bridges the gap between them -- it lets the pure Logic language reason about the impure Host language.

**Ochre: Single-language, typing-as-abstract-interpretation.**
Types and terms share a single syntax. The type checker *is* an abstract interpreter that executes programs. Type annotations only lose information (widen). There is no separate "logic language" -- the same language is used for both computation and specification.

This is a profound difference:
- Magmide says "logic and computation are fundamentally different activities that need different languages."
- Ochre says "typing IS computation -- just abstract computation."

**Magmide: Builds on existing Rust.**
Magmide takes Rust as-is and builds a proof assistant alongside it. The plan was to formalize Rust's semantics after the fact and then certify Rust code.

**Ochre: Designs a new language from scratch.**
Ochre integrates ownership, borrowing, and dependent types into a single new type system, rather than layering proofs on top of an existing language.

**Magmide: Separation logic as the bridge.**
Iris separation logic was Magmide's answer to "how do you prove things about mutable state." The pure logic world reasons about the imperative world through separation logic predicates.

**Ochre: Abstract interpretation as the bridge.**
Ochre's type checker directly abstractly interprets imperative code. Ownership and borrowing are built into the type system itself, not reasoned about through an external logic.

### Design Decisions Ochre Could Learn From

1. **Asserted types / subset types as first-class syntax.** Magmide's `nat & < 256` syntax is ergonomic and intuitive. Making refinement types cheap to write encourages their use. Ochre's "types are just abstract values" approach may naturally support this, but explicit syntactic sugar could help.

2. **Gradual verification via trackable effects.** The idea that unverified code carries an "effect" that bubbles up, allowing teams to see exactly how much of their codebase is unverified, is powerful. Even if Ochre doesn't use effects, the concept of quantifying "how verified is this code?" is worth considering.

3. **Corruption panics vs. assumption panics.** Distinguishing between "this can't happen assuming correct hardware" and "this can't happen assuming unproven conjecture X" is a useful conceptual distinction for practical systems.

4. **Reflective proofs / computational reflection.** Using verified functions as proof certificates (rather than checking large proof trees) is a powerful performance technique. If Ochre's type checker abstractly interprets programs anyway, it may already get this "for free" -- but it's worth ensuring.

5. **The importance of cargo-like tooling and education.** Hansen's extensive writing about research debt, documentation quality, and tooling ergonomics is correct. Ochre should internalize this: the language won't succeed on technical merits alone.

6. **Metaprogramming as a force multiplier.** Hansen identified metaprogramming as the single best primitive for implementation-overhead-to-expressiveness ratio. A language that can't be extended by its users will always be limited.

### Problems Magmide Encountered That Ochre Should Anticipate

1. **The "incentive no man's land" problem.** Magmide's most honest writing is in `crossing-no-mans-land.md`, where Hansen admits: "In order to achieve *any* of the goal, you unfortunately have to achieve basically *all* of it." Every incremental milestone provides functionality already available in other tools. The project can't deliver value until it's essentially complete. This is the existential risk for any project in this space, including Ochre.

2. **The bootstrapping problem.** How do you build a verified tool when the tool itself isn't verified yet? Magmide planned to use Coq for bootstrapping and MetaCoq for eventual self-verification. Ochre needs a clear story for this: either a trusted-core approach (small kernel that's auditable) or bootstrapping from an existing verified system.

3. **Formalization scope explosion.** Magmide planned to formalize Rust's semantics, translate Iris, and build reflective proof rules -- each of which is a multi-year research project on its own. Ochre should be careful about how much formalization infrastructure is truly needed before the language is useful.

4. **The separation logic learning curve.** Even Hansen, after extensive study, found Iris intimidating (his notes show him wrestling with step-indexing, resource algebras, CMRAs, etc.). If Ochre requires users to understand separation logic to write proofs, adoption will suffer. Ochre's approach of making ownership/borrowing part of the type system (rather than a separate logic) may avoid this, but the complexity has to go somewhere.

5. **Community building requires concrete deliverables.** Hansen eventually pivoted to writing "Coq for Programmers" as a way to build community before the language existed. Ochre should consider what concrete, demonstrable capabilities it can show early -- even toy examples of verified systems code would be more compelling than design docs.

### Magmide's Soundness Story

Magmide's soundness story was **essentially deferred**. The design docs mention:

- Using MetaCoq (which formalizes and verifies Coq in Coq) as a model for eventual self-verification.
- Building on Iris's existing soundness proofs for the separation logic layer.
- Using Coq to bootstrap correctness of the initial proof checker.
- The "Host reflection" rule would need careful justification to avoid introducing unsoundness.

But none of this was implemented. The design documents explicitly mark several critical areas (trackable effects, Host reflection, etc.) with comments like "handwaving goes here."

**Mutation and dependent types interaction:** Magmide's answer was simply "use Iris." The pure Logic language cannot observe mutation directly; instead, separation logic predicates describe the state of mutable resources, and proofs in Logic reason about these predicates. This cleanly separates the worlds but requires users to work with separation logic whenever reasoning about mutation -- a significant usability burden.

Ochre's approach of making the type checker an abstract interpreter that directly handles mutation is potentially more elegant, but also more novel and therefore needs its own soundness argument. The RustBelt/Iris work provides Magmide with a well-studied theoretical foundation; Ochre is charting newer territory.


## 5. Lessons for Ochre

### What Worked (Conceptually)

1. **The "Logic as type system" framing is pedagogically powerful.** Even though Magmide didn't implement it, the idea that "your type system is actually a full theorem prover" is an excellent way to explain dependent types to working engineers. Ochre's "typing IS abstract interpretation" is an even better version of this insight -- it's more unified and less arbitrary.

2. **Identifying Iris/separation logic as the key to verifying imperative code.** Hansen was right that separation logic (particularly Iris's higher-order variant) is the most promising approach for reasoning about mutation and concurrency. Ochre should study whether its abstract-interpretation approach achieves equivalent expressiveness.

3. **Criticisms of existing tools are accurate.** Hansen's analysis of Coq (too academic, "designed by accretion"), Lean (still too functional), and F\* (effects in the wrong place, SteelCore weaker than Iris) is largely correct and well-articulated.

4. **The comparison framework (max out logical power, computational power, expressive power) is useful.** Any project in this space should be evaluated against these three axes. Ochre should ask: where does it sit on each axis?

### What Didn't Work

1. **Design without implementation.** Magmide produced thousands of words of design documentation and a ~600-line toy type checker. The design docs became increasingly speculative without implementation feedback. Many critical questions ("handwaving goes here") were never forced to resolution. Ochre benefits from being built in Lean where the type checker itself is a working artifact.

2. **Scope was too large from the start.** Building a proof assistant + formalizing Rust + building Host reflection + verifying LLVM + self-hosting is not a tractable plan for a solo developer or small team. Magmide's roadmap was essentially "do all of formal verification research, but better." Ochre should have a much more focused minimum viable product.

3. **The two-language split creates friction.** Having Logic and Host be separate languages means users must context-switch between paradigms, learn two sets of semantics, and deal with the interface between them. Ochre's single-language approach avoids this.

4. **Depending on Iris for everything.** Iris is brilliant but enormously complex. Making it the foundation means inheriting all that complexity. Ochre's approach of building ownership/borrowing into the type system from the ground up may be harder initially but could be simpler in the long run.

5. **Solo development on an impossibly ambitious project.** The project needed a community, but had nothing concrete to show the community. This is the core lesson: build something that works (even if limited) before writing the grand design docs.

### Concrete Recommendations for Ochre

1. **Keep building working prototypes.** Magmide's failure mode was "design without implementation." Ochre's approach of building in Lean and having passing tests is fundamentally better. Continue this.

2. **Don't try to formalize everything.** Magmide wanted to formalize Rust, LLVM, hardware, and verify the compiler. Pick the smallest vertical slice that demonstrates the value proposition and make it work end-to-end.

3. **Ochre's "typing as abstract interpretation" is a genuine insight.** This is a simpler and more unified story than Magmide's Logic/Host split. Lean into it. The fact that type checking IS evaluation (just abstract evaluation) means there's one conceptual framework, not two.

4. **Study Iris but don't depend on it.** Iris's ideas about resource algebras, ghost state, and step-indexed logical relations may inform Ochre's design, but Ochre doesn't need to literally embed Iris. The ownership/borrowing type system may already provide equivalent guarantees for the common cases.

5. **Have an early "wow moment."** What's the smallest example where Ochre provably catches a bug that Rust wouldn't? Or proves a property that Rust's type system can't express? Find that example and make it sing. Magmide never had a working "wow moment" -- just descriptions of future ones.

6. **Be honest about soundness from day one.** Ochre's current approach of acknowledging consistency is deferred but focusing on soundness first is correct. Magmide handwaved soundness; don't do that. Even if the soundness argument is informal at first, it should exist and be documented.


## Sources

- [Magmide GitHub repository](https://github.com/magmide/magmide)
- [Design of Magmide](https://github.com/magmide/magmide/blob/main/posts/design-of-magmide.md)
- [My Path to Magmide (blog post)](https://blainehansen.me/post/my-path-to-magmide/)
- [Comparisons with other projects](https://github.com/magmide/magmide/blob/main/posts/comparisons-with-other-projects.md)
- [Magmide README.future.md](https://github.com/magmide/magmide/blob/main/README.future.md)
- [Issue #8: Thoughts on making this a practical language](https://github.com/magmide/magmide/issues/8)
