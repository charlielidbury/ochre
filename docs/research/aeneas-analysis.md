# Aeneas: Analysis and Comparison to Ochre

**Source:** Son Ho and Jonathan Protzenko, "Aeneas: Rust Verification by Functional Translation," ICFP 2022.
**Repo:** https://github.com/AeneasVerif/aeneas

---

## 1. How Aeneas Works

### The Pipeline

Aeneas is a verification toolchain, not a language. It takes existing Rust programs and translates them into pure functional code that can be reasoned about in a theorem prover. The pipeline is:

```
Rust source
  --> rustc (compile to MIR)
  --> Charon (Rust compiler plugin, MIR --> LLBC)
  --> Aeneas (LLBC --> pure lambda calculus)
  --> Backend extraction (F*, Coq, HOL4, Lean)
  --> User writes proofs in the target prover
```

**Charon** is a Rust compiler plugin (~9.5 kLoC) that extracts Rust's MIR (Mid-level Intermediate Representation) into LLBC (Low-Level Borrow Calculus). Charon performs mundane but essential tasks: computing dependency graphs, reordering definitions, grouping mutual recursion, reconstructing structured control flow (MIR uses goto-based CFGs), and desugaring idioms that are too low-level for reasoning.

**Aeneas** itself (~13.5 kLoC OCaml) picks up the LLBC AST and runs a single interpreter in two modes:
- **Concrete mode**: executes closed terms to a final value (used for testing).
- **Symbolic mode**: abstractly executes programs with symbolic variables, tracking ownership and aliasing, and simultaneously emitting a pure lambda-calculus translation.

The output is pure functional code with no notion of memory, addresses, or pointer arithmetic. It uses a simple error monad (for panics and arithmetic overflow) and, for functions that may diverge, a fuel-based or coinductive divergence monad.

### Intermediate Representations

1. **MIR** -- Rust's internal SSA-like representation with gotos, drops, and explicit moves.
2. **LLBC** -- Aeneas's input language. Retains structured control flow (if/else, match, loops) from MIR but makes all moves, copies, and borrows explicit. Variables are bound at function entry. Uses a "place" system (base variable + projection path) akin to lvalues. No memory addresses or pointer arithmetic.
3. **Pure lambda calculus** -- Aeneas's output. A standard functional language with algebraic data types, pattern matching, and a monadic error type. No references, no mutation, no memory model.

### How It Handles Ownership, Borrowing, and Mutation

This is the core technical contribution. Aeneas defines an **ownership-centric operational semantics** for LLBC that maps variables to *values* (not memory locations). The value domain includes:
- Concrete values (integers, booleans, ADT constructors, tuples)
- `borrow^m l v` -- a mutable borrow with loan identifier `l` owning value `v`
- `borrow^s l` -- a shared borrow pointing to loan `l`
- `loan^m l` -- a mutable loan (the "hole" left when a value is mutably borrowed)
- `loan^s {l...} v` -- a shared loan (value `v` is shared, with outstanding borrows `{l...}`)
- `bottom` -- moved/uninitialized

Key properties:
- **No memory addresses.** The environment maps variable names directly to structured values.
- **Aliasing graph is always a tree** (never a DAG or cycle), because Rust bans aliased mutation.
- **Focused reasoning**: to understand what happens through a mutable borrow, you only need to look at the borrow itself -- it uniquely owns its value.

The semantics is **lazy about borrow termination** -- borrows are only reorganized (terminated) when the environment needs to provide a value, not eagerly when lifetimes end. This is declarative and captures the *essence* of Rust's borrow semantics rather than its syntactic lifetime implementation.

### Backward Functions -- The Key Technical Innovation

When a Rust function returns a mutable borrow, the caller later needs to "give back" the modified value to the original owner (when the borrow's region/lifetime ends). Aeneas handles this by splitting such functions into two:

- A **forward function** that computes the return value (the "get" of a lens).
- A **backward function** that propagates updates back to the original owners (the "put" of a lens).

Example: `choose(b, &mut x, &mut y) -> &mut T` becomes:
```
choose_fwd(b, x, y) : T           -- returns the selected value
choose_back(b, x, y, ret) : (T, T) -- given the (possibly modified) return value,
                                     -- produces updated x and y
```

The backward function is called when the corresponding region/lifetime terminates. This is akin to a **bidirectional lens**: the forward function extracts; the backward function puts back. For recursive data structure traversals (e.g., `list_nth_mut`), the backward function mirrors the forward function's control flow, recursively reconstructing the data structure with the updated element.

### Region Abstractions

To handle function calls modularly (without inlining), Aeneas introduces **region abstractions** -- abstract representations of the ownership transferred during a function call. A region abstraction is like a "magic wand" (in separation logic terms): it records what borrows were consumed and what loans were produced. Introducing an abstraction models the function call; terminating it models the end of the borrow's lifetime, triggering the backward function call.

---

## 2. What Aeneas Proves and How

### What Can Be Verified

With Aeneas, users can verify **functional correctness properties** of safe Rust programs:
- A hash table's `insert` correctly maintains the map invariant
- Arithmetic operations don't overflow
- Data structure invariants are preserved
- Functions produce the correct outputs for all valid inputs

The key advantage: because the translation eliminates memory, the proofs are about **pure functional behavior**, not memory layout. There are no separation logic frame rules, no pointer reasoning, no memory-related proof obligations.

### Proof Methodology

1. **Translation is automatic** -- Charon + Aeneas runs in seconds per file.
2. **Proofs are extrinsic** -- users write lemmas about the translated functions as separate theorems, not as inline annotations in the Rust source.
3. **No annotation language needed** -- the Rust code remains unannotated. Properties are stated and proved entirely in the target prover.
4. **Proofs are modular** -- function specifications are lemmas about the forward/backward functions. Callers use these lemmas without looking at function bodies.

For termination, Aeneas emits a `decreases` annotation that the user fills in with a termination measure.

### Backends

- **F*** -- the original and (at the time of the paper) most mature backend. Benefits from F*'s SMT integration for automated proofs.
- **Lean 4** -- now one of the most mature backends. Includes specialized tactics (`progress` for stepping through monadic code) and a divergence monad with coinductive termination proofs.
- **HOL4** -- also mature, with partial function support and specialized tactics.
- **Coq** -- supported.

### Case Study: Resizable Hash Table

The main case study is a resizable hash table with `insert`, `get`, `get_mut`, and `remove` operations, using linked-list buckets. This was (at the time) the first verified hash table in Rust. The proof took 4 person-days for 201 LoC of implementation, which compares very favorably with:
- VST (a separation logic framework for C): ~3 days for a simpler non-resizing hash table
- CFML (for OCaml): ~1 week for a similar table

The proofs focus on functional properties (the table behaves like an associative list) rather than memory layout, which is the direct benefit of the functional translation.

---

## 3. The Key Insight: Rust and Functional Purity

### Why Rust Programs Can Be Translated to Pure Functional Form

The central observation of Aeneas is profound:

> "For the most part, references and borrows serve the purpose of optimizing either performance (e.g., passing by reference instead of by value), or memory representation (e.g., by controlling aliasing and taking inner pointers within data structures). That is, Rust's references do not serve any semantic purpose; coupled with the fact that the type system is enforcing a linear discipline, such programs are functional in essence, and can be naturally translated to a pure functional equivalent."

In other words: **Rust's ownership system ensures that safe Rust programs are already pure functional programs in disguise.** The mutation is an implementation detail. Here's why:

1. **Unique ownership = functional update.** When you have `&mut x` and modify `*x`, no one else can observe `x` during the borrow. This is semantically identical to taking `x` by value, producing a new value, and returning it. The mutation is just an optimization that avoids the copy.

2. **Shared borrows = copying.** When you have `&x`, no one can mutate `x`. This is semantically identical to having a copy of `x`'s value.

3. **The aliasing graph is a tree.** Rust guarantees either (a) one mutable reference and no other references, or (b) any number of shared references and no mutable references. This means the aliasing structure never forms a DAG or cycle -- it's always a tree. Trees can be directly represented as pure functional values.

4. **Borrow termination = functional "put back".** When a mutable borrow ends, Rust gives back the (possibly modified) value to the original owner. This is exactly a functional lens operation: get a value, transform it, put it back.

### The Wadler Observation, Reversed

Wadler (1990) observed that **a linear type system allows compiling pure programs using imperative updates** (since linear values are used exactly once, mutation is safe). Aeneas leverages the reverse: **imperative programs with a strong enough ownership discipline admit a pure functional equivalent** (Chargu\'eraud and Pottier, 2008). The ownership system *is* a linearity discipline, and linearity *is* functional purity.

### What This Means

This insight is deeper than "we can translate Rust to F*." It means:

1. **Rust's borrow checker is secretly a purity checker** for safe code. Any safe Rust program is semantically pure.
2. **The "right" semantics for Rust ownership is functional**, not memory-based. You don't need a heap model to reason about safe Rust.
3. **Dependent types and Rust-style ownership are naturally compatible**, because both operate on a world of pure values. Ownership just controls who can see and modify which part of the value tree at any given time.

---

## 4. Limitations of Aeneas's Approach

### Unsupported Rust Features

At the time of the paper (2022), Aeneas could not handle:
- **Unsafe code** -- by design, as unsafe breaks the ownership invariants that enable functional translation.
- **Interior mutability** (`Cell`, `RefCell`, `Mutex`) -- these use unsafe internally to provide shared mutation, which breaks the "tree aliasing" property.
- **Trait objects / dynamic dispatch** -- not supported at paper time (now partially supported via `dyn`).
- **Closures** -- not supported at paper time (now supported).
- **Loops with complex control flow** -- `break`/`continue` to outer loops, `return` inside nested loops (technical limitation, not fundamental).
- **Concurrency** -- fundamentally requires reasoning about shared mutable state.
- **Nested borrows in function signatures** -- a restriction of the symbolic semantics.
- **Type declarations containing borrows** -- another restriction.

As of 2026, the repo shows significant progress: closures, traits, `dyn`, and basic loops are now supported. The main remaining gaps are unsafe code, concurrency, and interior mutability, which are being addressed via separation logic extensions.

### Multi-Language Pipeline Friction

The translation pipeline creates several sources of friction:

1. **Two-language burden.** Developers write Rust but prove in Lean/F*/Coq. They must understand the translated code, which, while readable, is not the code they wrote.

2. **No inline specifications.** You cannot annotate the Rust source with pre/post-conditions or loop invariants. Specifications live entirely in the target prover, disconnected from the source.

3. **Backward function complexity.** For deeply nested data structure operations, the backward functions can become complex. Users must understand the forward/backward splitting to write proofs.

4. **Opaque external dependencies.** Any code outside the translated crate (standard library, external crates) must be manually modeled as opaque functions with hand-written specifications.

5. **Translation trust.** The translation itself is not formally verified (though extensive invariant checking is performed). Users must trust that the pure code is semantically equivalent to the Rust code.

6. **Termination obligations.** Users must manually provide termination measures for recursive functions.

7. **Build system complexity.** The pipeline involves rustc, Charon, Aeneas, and the target prover's build system, all of which must be version-compatible.

---

## 5. Comparison to Ochre's Approach

### Aeneas: Translator | Ochre: Native Language

Aeneas takes existing Rust code and translates it to a pure language for verification. Ochre aims to be a single language where Rust-like code and dependent types coexist natively. This is a fundamental architectural difference with far-reaching consequences.

### What Ochre Gains by Being a Single Language

1. **Unified specification and implementation.** In Ochre, types ARE specifications. A function's type can express its full behavioral contract. There is no separate specification language and no gap between the code and what is verified about it.

2. **No translation trust gap.** Aeneas must be trusted to produce a semantically equivalent translation. Ochre's soundness proof would directly establish that well-typed programs satisfy their type-level specifications -- there is no intermediate translation to trust.

3. **Inline verification.** Strong mutation tracking means that after `x = 5`, the type of `x` is `5` (a singleton type). Verification happens continuously as the type checker executes the program abstractly. There is no separate "proof writing" phase.

4. **No backward functions needed.** Ochre's strong mutation tracks the actual state of variables through borrows and assignments. When a mutable borrow ends, the type system already knows the new value's type. Aeneas needs backward functions because it must translate imperative updates into a pure language that lacks mutation; Ochre's type system natively understands mutation.

5. **Loop invariants via typing.** In Aeneas, loop invariants must be stated as lemmas in the target prover. In Ochre, the type checker's abstract interpretation of the loop body could, in principle, infer loop invariants (or the programmer could annotate types to provide them).

6. **Ecosystem unity.** Libraries, specifications, and proofs all live in one language with one build system.

### What Ochre Loses

1. **Maturity and ecosystem.** Aeneas targets Lean, Coq, F*, and HOL4 -- mature provers with extensive libraries, tactics, and communities. Ochre must build its proof ecosystem from scratch.

2. **Existing Rust code.** Aeneas can verify *existing* Rust programs without modification. Ochre requires code to be written (or rewritten) in Ochre.

3. **Backend flexibility.** Aeneas users can choose their favorite prover. Ochre's verification is tied to its own type system.

4. **Separation of concerns.** In Aeneas, the Rust code can be compiled and shipped without any verification artifacts. In Ochre, types and code are intertwined, which could make it harder to write "just code" without thinking about verification (though type inference could mitigate this).

5. **Proof automation.** Lean and F* have sophisticated tactic frameworks and SMT integration. Ochre's type-checking-as-verification approach may need comparable automation, which is hard to build.

6. **Tooling.** Rust has world-class tooling (cargo, rust-analyzer, clippy, etc.). Ochre would need to build equivalent tooling.

### Where Ochre Must Solve the Same Problems

Aeneas encountered several hard problems that Ochre will face in different forms:

1. **Loops and termination.** Aeneas translates loops to recursive functions and requires termination proofs. Ochre will need either (a) a totality checker (which would restrict expressiveness), (b) a fuel/divergence monad (which would complicate types), or (c) accepting partial functions (which would complicate soundness). The interaction of loops with dependent types is notoriously difficult.

2. **Trait objects and dynamic dispatch.** Aeneas now supports `dyn` traits but with limitations. Ochre will need to express dynamic dispatch in its type system -- likely via existential types or dependent pairs.

3. **Closures and environments.** Aeneas now handles closures. Ochre will need closure types that capture their environment's types precisely -- which is natural for dependent types but complex when combined with borrowing.

4. **External/opaque code.** Any real system interacts with code whose source isn't available. Aeneas handles this with opaque modules and hand-written models. Ochre would need a similar mechanism -- likely abstract/opaque type declarations with axiomatized properties.

5. **Interior mutability and unsafe.** Aeneas explicitly excludes these for now, deferring to separation logic. Ochre must eventually address them too. If Ochre wants to verify `RefCell` or `Vec` internals, it needs a story for reasoning about raw pointers and shared mutation -- likely requiring some form of separation logic or capability system integrated into the type system.

6. **Disjunctions in control flow (the "join" problem).** After an if/else, Aeneas requires that both branches produce symbolically compatible environments. In the paper, this means disjunctions must be in "terminal position" (duplicating continuations). Ochre faces the same issue: after `if b { x = 1 } else { x = 2 }`, the type of `x` must be the join (union) of `1` and `2`. Ochre's structural subtyping with unions is designed to handle this, but computing precise joins is expensive and handling them soundly with mutation is the exact problem that caused Ochre's original unsoundness.

### What Aeneas's Translation Strategy Suggests for Ochre's Type System

1. **Ownership is the key enabler.** Aeneas confirms that ownership/linearity is what makes dependent reasoning about imperative code tractable. Ochre's ownership system is not just a performance feature -- it is *essential* for soundness of the type system.

2. **The forward/backward decomposition hints at how mutation should interact with dependent types.** When a mutable borrow is active, the type system needs to track two things: (a) the current type of the borrowed value (the "forward" view), and (b) how changes to it affect the original owner's type (the "backward" effect). Ochre's strong mutation naturally handles (a). For (b), Ochre needs the borrow termination to correctly update the original variable's type -- which is exactly what "backward functions" encode. This suggests Ochre's type system should have a precise story for "what type does `x` have after a mutable borrow of `x` ends and the borrower modified it?"

3. **Region abstractions suggest modular type-checking boundaries.** Aeneas uses region abstractions to reason about function calls without inlining. Ochre needs analogous modular reasoning: when calling a function, the type checker should be able to determine the output type and the effect on borrowed arguments from the function's signature alone, without examining the body. Function types in Ochre should encode enough information for this.

4. **The "tree shape" of the aliasing graph is crucial.** Aeneas's entire approach depends on the aliasing graph being a tree. Ochre should carefully preserve this property. Any extension that allows aliasing (interior mutability, unsafe, raw pointers) must be carefully quarantined to avoid breaking the core reasoning.

---

## 6. Implications for Ochre's Soundness Proof

### What Aeneas Tells Us About Proving Properties of Rust-Shaped Programs

1. **The ownership-centric semantics is the right foundation.** Aeneas's experience shows that an ownership-based, value-oriented semantics (no memory addresses, no heap model) is sufficient for reasoning about a large class of programs. Ochre's approach of "typing IS abstract interpretation" over values is well-aligned with this.

2. **Borrow termination is the hard part.** Aeneas's most complex machinery (backward functions, region abstractions, projectors) all exist to handle the moment when a borrow ends and ownership returns to the original variable. This is likely where Ochre's soundness proof will face the most difficulty too. The question "what is the type of `x` after a borrow of `x.field` ends?" requires precise tracking of how sub-values were modified.

3. **The join problem is real.** Aeneas sidesteps the "join problem" (what happens when control flow merges and the symbolic state differs between branches) by requiring terminal-position disjunctions. Ochre cannot sidestep this -- its type system must compute joins of types after branches. The original Ochre unsoundness (subtyping preservation under environment narrowing failure) is likely related to this challenge. Aeneas's experience confirms this is a genuine difficulty.

4. **Modular reasoning requires careful abstraction.** Aeneas's region abstractions were necessary to achieve modular translation. Ochre's type system needs analogous abstraction at function boundaries. The function type must encode enough information about borrowing behavior that the caller can determine the output type and environment updates without examining the function body. Getting this abstraction right -- expressive enough to be useful, restrictive enough to be sound -- is a key design challenge.

5. **Safe-only first is a viable strategy.** Aeneas intentionally restricts to safe Rust and achieves a lot. Ochre should similarly focus on safe programs first and get that sound, before attempting to handle unsafe/interior mutability. The safe fragment is where ownership-based reasoning shines, and it covers a large class of useful programs.

6. **The formalization is tractable.** Aeneas formalized its semantics and published a proof that its symbolic execution correctly implements a borrow checker (ICFP 2024). This suggests that formalizing ownership-centric semantics is achievable, which is encouraging for Ochre's mechanized soundness proof in Lean. However, Ochre's proof is strictly harder because it must also handle dependent types interacting with mutation and ownership -- something Aeneas never touches (it offloads dependent reasoning to the target prover).

### Specific Risks for Ochre

- **Mutation + dependent types + subtyping.** Aeneas never faces this combination because it translates mutation away. Ochre must handle all three simultaneously. The interaction of strong mutation (types change after assignment) with subtyping (types can be widened) and dependent types (types depend on values) is where the original unsoundness was found. Aeneas's experience doesn't directly help here because it sidesteps the issue entirely.

- **Decidability.** Aeneas's translation produces code that humans then verify with potentially undecidable proof obligations. Ochre's type checking must terminate and be decidable (or at least predictable). This constrains what type-level computation can express.

- **Proof ergonomics at scale.** Aeneas's case studies show that even with a clean functional translation, proofs take effort (4 person-days for a hash table). Ochre aims to make verification more integrated, but the underlying proof obligations don't disappear -- they just change form. Whether type-level reasoning is actually easier than writing lemmas in Lean remains to be demonstrated.

---

## Does Ownership Eliminate the Need for Separation Logic?

Ochre restricts to ownership-disciplined mutation (safe Rust style: no shared mutable state, no interior mutability). A central question for the soundness proof is whether this restriction allows Ochre to avoid separation logic (Iris-style reasoning) entirely. The evidence from the literature strongly suggests **yes, for the safe fragment**.

### 1. The Heap Reduces to a Stack of Owned Values

If ownership guarantees exclusive access, the "heap" is always reducible to a stack of owned values. This is not merely a conjecture -- it is the core technical observation that Aeneas, Creusot, and Oxide all exploit.

**Aeneas** defines a value-based operational semantics with "no notion of memory, addresses, or pointer arithmetic." The environment maps variable names directly to structured values (not to memory locations). The aliasing graph is always a tree, never a DAG or cycle, because Rust's ownership discipline forbids aliased mutation. This means the entire program state can be represented as a nested tree of owned values, which is isomorphic to a pure functional data structure. There is no separate heap in Aeneas's semantics -- and the approach works for the full safe fragment of Rust.

**Oxide** (Weiss et al., 2019) formalizes core Rust and proves type safety via standard progress and preservation -- the classical syntactic method -- with no separation logic whatsoever. Oxide does model a store (mapping locations to values), but this store is only needed because Oxide models references as location-based indirections. Crucially, the ownership discipline ensures that the store behaves like a tree of owned values: each mutable reference is the unique path to its referent, so there is no aliasing to reason about. The proof goes through without any frame rules, magic wands, or ownership predicates from separation logic.

**Creusot** (Denis et al., 2022) similarly translates safe Rust to pure functional programs for verification via SMT solvers, explicitly avoiding separation logic. Its specification language uses "prophecies" (the future value a mutable borrow will have when its lifetime ends) rather than heap predicates.

**Implication for Ochre:** If Ochre restricts to ownership-disciplined mutation, its soundness proof can model the program state as a tree of typed values -- essentially a typing environment that maps variables to their current (dependent) types. No separate heap model is needed. Mutable references are just paths into this tree, and the ownership discipline guarantees that each path is unique. This is a significant simplification compared to languages that require heap reasoning.

### 2. Concurrency with Ownership Transfer

When Ochre eventually adds concurrency, the question is whether ownership-transfer-based concurrency (Rust-style channels, move semantics, no shared mutable state) still avoids separation logic.

**The answer is: mostly yes, with caveats.**

In Rust's concurrency model, sending a value through a channel transfers ownership. The sender can no longer access the value; the receiver gets exclusive ownership. This is semantically equivalent to a pure functional "handoff" -- no shared state exists, so no separation logic framing is needed to reason about disjointness.

The key insight is that ownership transfer between threads is isomorphic to passing arguments to a function: the caller gives up the value, the callee receives it. If all inter-thread communication is via ownership transfer, each thread's local reasoning is identical to sequential reasoning -- the thread owns its entire state exclusively.

**However**, Rust's actual concurrency model includes `Mutex<T>`, `RwLock<T>`, `Arc<T>`, and atomics. These all involve shared mutable state internally (even if the API presents an ownership-based facade). Verifying the implementations of these primitives requires separation logic or an equivalent. But if Ochre treats these as trusted primitives with axiomatized specifications (e.g., "acquiring a `Mutex<T>` gives you exclusive `&mut T` access"), then user code that uses them can still be verified without separation logic -- the separation reasoning is confined to the primitive implementations.

**Implication for Ochre:** Pure ownership-transfer concurrency (channels, move semantics, `spawn` with move closures) does not require separation logic. Shared-state concurrency primitives (`Mutex`, `Arc`) would require either (a) trusted axiomatizations or (b) separation logic for their internal verification. Ochre should design its concurrency story around ownership transfer as the primary mechanism, with shared-state primitives as opaque, axiomatized building blocks.

### 3. Do Even Unique References Require Separation Logic?

**No.** This is the strongest finding from the literature.

The concern is that references, even unique ones, create indirection -- a reference "points to" something, and reasoning about pointing-to relationships is traditionally the domain of separation logic. But Oxide's proof demonstrates that unique/mutable references can be handled by standard syntactic methods (progress and preservation) without separation logic.

The reason is that unique references do not create aliasing. A mutable reference `&mut T` is the sole access path to its referent. This means:
- There is no need for a "separating conjunction" (the frame rule) because there is nothing to separate -- each reference uniquely owns its target.
- There is no need for step-indexed logical relations to handle reference cycles, because ownership prevents reference cycles in safe code.
- There is no need for ghost state or invariant protocols because the type system statically tracks who owns what.

Shared references (`&T`) are also fine: they are read-only, so no mutation can occur through them, and they are semantically equivalent to copies of the value.

The one subtlety is **reborrowing** -- creating a new reference from an existing one. But reborrowing in safe Rust always follows the ownership discipline: the original reference is "frozen" while the reborrow is active, so there is still no aliasing of mutable access. Aeneas handles this with its loan/borrow value structure; Oxide handles it with its provenance-based type system. Neither requires separation logic.

**Step-indexed logical relations** are sometimes used for soundness proofs of languages with recursive types and general references (where references can alias and form cycles). But Rust's ownership discipline prevents exactly these situations. A language with only unique references and shared (immutable) references, without recursive reference types that form cycles, does not require step-indexing. If Ochre has recursive types (which it likely does), step-indexing may be needed for the recursive type interpretation, but this is orthogonal to references -- it is needed for mu-types, not for ownership.

**Implication for Ochre:** Unique references do not require separation logic in the soundness proof. Standard techniques (progress and preservation, or a direct semantic argument) suffice. Step-indexing may be needed if Ochre has recursive types, but that is independent of the ownership/reference question.

### 4. Unsafe Code and Interior Mutability Require Iris-Style Reasoning

**Yes.** This is the one area where separation logic becomes necessary.

**RustBelt** (Jung et al., 2018) uses Iris specifically because Rust's standard library contains unsafe code that breaks the ownership discipline. Types like `RefCell<T>`, `Cell<T>`, `Mutex<T>`, `Rc<T>`, and `Vec<T>` (which uses raw pointers internally) all violate the "tree aliasing" property. RustBelt must verify that these unsafe implementations are "observationally safe" -- that they behave as if they respected the ownership discipline when viewed through their safe API.

This verification fundamentally requires:
- **A heap model**: because raw pointers create genuine aliasing that cannot be abstracted away.
- **Separation logic**: to reason about disjoint ownership of heap regions that may be aliased at the pointer level.
- **Ghost state / invariant protocols**: to reason about the internal invariants maintained by unsafe code (e.g., `RefCell`'s runtime borrow count).
- **Step-indexed logical relations**: to handle the circularity that arises when types are stored in the heap and the type interpretation depends on the heap contents.

Dreyer's key argument (in the Jane Street talk and the CACM 2021 article) is that syntactic type safety "totally doesn't work if you have any unsafe code in your language." As soon as any part of the program is outside the syntactic typing rules, progress-and-preservation tells you nothing. RustBelt's semantic approach (interpreting types as Iris predicates) is needed to bridge the safe/unsafe boundary.

**But crucially**: RustBelt needs Iris *because of unsafe code*. If Rust had no unsafe code at all, a syntactic proof (like Oxide's) would suffice. The Iris machinery is not needed for the safe fragment per se -- it is needed to verify that unsafe code correctly implements the ownership discipline's guarantees.

**Implication for Ochre:** If Ochre eventually wants to verify unsafe code or interior mutability, it will need Iris-style reasoning (or an equivalent). But this can be deferred. The safe fragment -- which is Ochre's current focus -- does not require it. If Ochre later adds an `unsafe` escape hatch, the separation logic reasoning can be confined to verifying the implementations of unsafe primitives, while all user-facing safe code continues to use the simpler ownership-based reasoning.

### 5. What the Literature Says: A Synthesis

| Project | Fragment | Proof Method | Separation Logic? | Heap Model? |
|---------|----------|-------------|-------------------|-------------|
| **Oxide** (Weiss et al., 2019) | Safe Rust core | Progress + preservation | No | Store (tree-shaped) |
| **Patina** (Reed, 2015) | Safe Rust subset | Informal proof | No | Memory model (tree-shaped) |
| **Aeneas** (Ho & Protzenko, 2022) | Safe Rust (broad) | Functional translation | No | None (value-based) |
| **Creusot** (Denis et al., 2022) | Safe Rust (broad) | SMT via Why3 | No | None (prophecy-based) |
| **RustBelt** (Jung et al., 2018) | Safe + unsafe Rust | Semantic (Iris) | Yes | Full heap |
| **RustHornBelt** (Matsushita et al., 2022) | Safe + unsafe Rust | CHC + Iris | Yes | Full heap |
| **RefinedRust** (Sammler et al., 2024) | Safe + unsafe Rust | Refinement types + Iris | Yes | Full heap |

The pattern is unambiguous: **every project that restricts to safe Rust avoids separation logic; every project that handles unsafe code requires it.**

**Aeneas explicitly chose not to use separation logic** because, for safe Rust, "references and borrows serve the purpose of optimizing either performance or memory representation" -- they do not serve any semantic purpose. The ownership discipline makes mutation a transparent optimization over pure functional behavior. The Aeneas team is now adding separation logic support specifically to extend coverage to unsafe code and concurrency -- confirming that it was not needed for the safe fragment.

**Oxide proved that the safe fragment admits a standard syntactic soundness proof.** This is the strongest evidence that ownership-disciplined mutation does not inherently require separation logic. Oxide's proof uses structural induction on typing derivations -- the most conventional possible technique. No Kripke worlds, no step-indexing (for references), no frame rules.

**RustBelt's Dreyer explicitly states** that the reason RustBelt uses Iris is that syntactic type safety "doesn't work if you have any unsafe code." The implication is clear: for safe-only code, syntactic methods work.

### Conclusion for Ochre

**Ochre can avoid separation logic in its soundness proof**, provided it restricts to ownership-disciplined mutation (the current plan). The evidence is strong:

1. **No heap model needed.** The program state is a tree of owned values, representable as a typing environment. Aeneas proved this works in practice for a broad subset of safe Rust.

2. **No separation logic needed.** Oxide proved type safety for safe Rust core via progress and preservation. Aeneas and Creusot verify programs without any separation logic.

3. **Unique references are not a problem.** They do not create aliasing, so there is nothing to "separate." Standard techniques handle them.

4. **Ownership-transfer concurrency is fine.** It reduces to sequential reasoning per thread. Shared-state primitives can be axiomatized.

5. **Unsafe / interior mutability is where separation logic becomes necessary.** This can be deferred and, when needed, confined to primitive implementations.

This is good news for Ochre's soundness proof. The combination of ownership + dependent types is already hard enough. Not having to also integrate separation logic into the proof is a significant simplification. The soundness proof can focus on the interaction of dependent types with mutation and subtyping -- which is the genuinely novel and difficult part -- without also needing to reason about heap disjointness, frame rules, or ghost state.

**Sources consulted:**
- [Aeneas: Rust Verification by Functional Translation (ICFP 2022)](https://dl.acm.org/doi/10.1145/3547647)
- [Oxide: The Essence of Rust (Weiss et al.)](https://arxiv.org/abs/1903.00982)
- [Patina: A Formalization of the Rust Programming Language (Reed, 2015)](https://dada.cs.washington.edu/research/tr/2015/03/UW-CSE-15-03-02.pdf)
- [RustBelt: Securing the Foundations of the Rust Programming Language (POPL 2018)](https://plv.mpi-sws.org/rustbelt/popl18/paper.pdf)
- [Safe Systems Programming in Rust (CACM 2021)](https://iris-project.org/pdfs/2021-rustbelt-cacm-final.pdf)
- [RustBelt: Logical Foundations for the Future of Safe Systems Programming (Jane Street talk)](https://www.janestreet.com/tech-talks/rustbelt/)
- [Creusot: A Foundry for the Deductive Verification of Rust Programs (ICFEM 2022)](https://inria.hal.science/hal-03737878v1/document)
- [A Hybrid Approach to Semi-automated Rust Verification (2024)](https://arxiv.org/html/2403.15122v1)
- [RefinedRust: A Type System for High-Assurance Verification of Rust Programs (PLDI 2024)](https://iris-project.org/pdfs/2024-pldi-refinedrust.pdf)
- [RustHornBelt: A Semantic Foundation for Functional Verification of Rust Programs with Unsafe Code (PLDI 2022)](https://dl.acm.org/doi/10.1145/3519939.3523704)

---

## Summary

Aeneas validates the fundamental insight that underlies Ochre: **Rust's ownership discipline makes programs amenable to dependent reasoning.** Aeneas does this by translating to a pure language; Ochre aims to do it natively.

The key takeaways for Ochre:

1. **Ownership is the linchpin.** Get the ownership/borrowing semantics right and sound, and the rest follows.
2. **Borrow termination is the technical crux.** This is where Aeneas's most complex machinery lives, and where Ochre's soundness proof will be hardest.
3. **The join problem is real and central.** Ochre's structural subtyping with unions is the right approach but must be handled with extreme care.
4. **Focus on safe code first.** Unsafe and interior mutability can wait.
5. **Aeneas is a complement, not a competitor.** Aeneas verifies existing Rust code; Ochre would be for new code where verification is a first-class goal. They serve different use cases.
