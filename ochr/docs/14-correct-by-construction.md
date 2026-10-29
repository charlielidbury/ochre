# 14. Correct by construction: what theory makes Ochr's rules right

Started by team-lead on 2026-10-29 from a discussion with the user. Status: **open**.

## The goal

The user's goal: Ochr is proven correct by construction, by a unifying theory from which it follows that the rules *must* be correct. Not a pile of side conditions each forced by a counterexample, and not "fix every bug the tests find until none are left", which has no point at which you know you are finished.

## Where Ochr is

- **Paper.** Consistency, stability (the two evaluation paths agree) and naturality are conjectures. Theorem 19 proves soundness for a first-order fragment, conditional on naturality and on invariants of the machine that are not proved. The set model (A.6) is a sketch.
- **Lean.** Consistency is stated against the checker with the proof left `sorry` (branch `consistency-spec`). The checker is total; correctness is `lake build` (`ochr/core/CLAUDE.md`).
- **The rules accrete by counterexample.** Figure 16 lists 27 side conditions, each with the program that forced it. Recent ones: D71 (no borrow-typed parameters, forced by the Fording attacks), D72 (a stuck block's arms are whole-again points), and D72's own attack pass immediately found the next gap (a caller writing through a returned borrow of an index field, `GetN`), which turned out to be a closed proof of `False` on main (`BoomI2`), closed the same day by D73 (a lent part is unknown at a whole-again point). The dependent-field rules ([Open], [Repack], whole-again points) are accreting fastest.
- **The nearest thing to a unifying principle** is §6.3's "no decision that changes a result is read from a normal form". Many of the closed proofs of `False` found so far broke it (the others came from positivity, subsingleton elimination and the dependent-field rules, D73 among them). It is applied by hand, case by case.

## What "correct" should mean

Three properties, which a theory may deliver separately:
- **Consistency:** no closed term has type `False`. Without it, every statement is provable and the theorem prover is worthless.
- **Adequacy:** an accepted `Id` statement holds when the programs actually run. Without it, Ochr could be consistent but prove things about its programs that are not true of them.
- **Type safety:** an accepted program runs without error.

## Background: the vocabulary

There are three standard ways to say what a language *means*, and every route below relates two of them.

- **Operational semantics** says how programs *run*: a set of rules for stepping a program to a result. Ochr already has one: the machine (the paper's big-step judgement ⟨Ω, t⟩ ⇓ ⟨Ω′, v⟩). Ochr's checker runs it, and Ochr's typing is the machine run with types.
- **Denotational semantics** says what programs *are*: each type is interpreted as a mathematical object (usually a set), and each program as an element or a function. Running is not mentioned. To connect it to how programs run you prove an **adequacy theorem**: running a program gives the value its denotation says.
- **Translation** (also called a *syntactic model*) says what programs mean by translating them into another language whose meaning is already trusted, such as Lean or Coq. This is what Aeneas does: Rust programs become Lean programs.

And two ways to prove a type system right:

- **Syntactic type safety**, the textbook method (Pierce's *TAPL*; Wright and Felleisen): prove that a well-typed program either has finished or can take a step (*progress*), and that a step keeps it well-typed (*preservation*). This needs a typing judgement separate from running, and a substitution lemma. Ochr has neither in that form, since its typing *is* running; that is why the paper's version of preservation (stability) is its hardest conjecture.
- **Semantic type safety**: define what each type *means* in terms of behaviour, then prove every well-typed program has that behaviour. The tool is a **logical relation** (explained under R2). The modern case for it, and its relation to the syntactic method, is Timany, Krebbers, Dreyer and Birkedal's *A Logical Approach to Type Soundness* (J. ACM, 2024).

## The routes

### R1. A denotational model: derive the rules from what programs mean

**What it is.** Give every Ochr type a mathematical meaning, independent of the machine: `Nat` means the set of natural numbers, a proposition means a set with at most one element (a "subsingleton": empty if false, one element if true), and a function type with borrow parameters means a set of functions that take the current contents of the borrowed places and return the result *and* the final contents of those places, as Aeneas's forward and backward functions do. `Id` means equality of what the two computations return and leave behind. Then each typing rule becomes a lemma: if the premises hold in the model, so does the conclusion. Consistency follows because `False` means the empty set, so nothing can inhabit it. This is how Lean's consistency is proved (Werner; Carneiro's thesis) and it is the shape of the paper's A.6 sketch.

**How it makes the rules correct by construction.** You no longer ask "is there a counterexample to this rule?" but "is this rule true in the model?". A rule that is not true there is wrong before anyone finds a program that breaks it, and a side condition that the model does not need can be removed.

- For: the textbook route to "the rules must be correct"; explains *why* each rule holds; gives the paper a theorem for every program; can remove side conditions as well as justify them.
- Against: the largest up-front cost. The model must give a meaning to the machine's peculiar features: closing off, sealed programs, generalisation, conversion by running code, so the two paths agreeing is still the hard lemma, now stated inside the model. Dependent fields need a meaning for an "open" value. It gives consistency directly, but adequacy and type safety need a separate adequacy theorem connecting the model to the machine. A Lean mechanisation is a large project, and bounded by Gödel: a model of every universe level needs more strength than Lean has, so a paper proof, or bounded levels, may be the realistic form.
- Learn more: Glynn Winskel, *The Formal Semantics of Programming Languages* (MIT Press, 1993) for denotational semantics in general; Benjamin Werner, *Sets in Types, Types in Sets* (TACS 1997) and Mario Carneiro, *The Type Theory of Lean* (2019; `docs/papers/theory-of-lean.pdf`, §6) for set models of type theories like Lean's.

### R2. Semantic types defined over the machine's runs (an operational logical relation)

**What it is.** Instead of interpreting types as sets (R1), interpret them as properties of what the *machine* does. For each type `T`, define which values "behave like a `T`", by induction on `T`:
- a value behaves like a `Nat` if it is a numeral;
- a value behaves like a function from `A` to `B` if, whenever it is given a value that behaves like an `A`, the machine runs it to a value that behaves like a `B`;
- a borrow behaves like an `&T` if what it holds behaves like a `T` and whatever is written back through it does too;
- `False` is behaved like by nothing.

This family of definitions is the **logical relation**. It is "logical" because each case follows the type's logical structure (a function relates related inputs to related outputs), and "operational" because it is phrased in terms of the machine's runs rather than sets. A term is **semantically well-typed** if running it gives a value that behaves like its type. The central theorem, the **fundamental lemma**, says every program the checker accepts is semantically well-typed, and it is proved one typing rule at a time. Type safety and consistency fall out: a semantically well-typed program does not go wrong, and nothing behaves like `False`.

**Why it suits Ochr.** Ochr's typing already *is* running, so "types are properties of runs" is close to how Ochr thinks. It gives type safety and adequacy directly, with no separate adequacy theorem. It is also how Rust's type system was proved sound: RustBelt interprets each Rust type as a property of memory and runs, in the Iris program logic, and proves each typing rule against it; the same method then proves unsafe library code (such as `Vec`) safe to use.

- For: covers all three properties at once; matches Ochr's "typing is running"; the method that worked for Rust's borrows; extensible to trusted native code (Ochr's `implemented by` natives) by proving each native semantically well-typed.
- Against: borrows need a logic of ownership and resources to state "behaves like `&T`" (RustBelt needed all of Iris for this); recursion needs *step-indexing* (counting machine steps so that the definition is well-founded), which adds technicality; dependent types make the relation depend on values, which is harder than for Rust's non-dependent types; it is a large mechanisation either way.
- Learn more: *Software Foundations*, volume 2, *Programming Language Foundations*, chapter "Norm" (a first logical relation, for a tiny language, mechanised in Coq): https://softwarefoundations.cis.upenn.edu/ ; Lau Skorstengaard, *An Introduction to Logical Relations* (lecture notes, arXiv 2019); Amal Ahmed's lectures on logical relations at the Oregon Programming Languages Summer School (OPLSS); Jung, Jourdan, Krebbers and Dreyer, *RustBelt* (POPL 2018); the Iris project: https://iris-project.org/ ; Timany et al., *A Logical Approach to Type Soundness* (J. ACM, 2024).

### R3. Operational simulation: prove the symbolic run faithful to the concrete one

**What it is.** The checker runs programs on unknown inputs (abstract values, sealed programs); real programs run on concrete ones. A **simulation** is a relation between the two kinds of state such that every step of the symbolic run corresponds to the concrete run's steps, for every way of filling in the unknowns. Prove that relation is preserved by every rule, and whatever the checker concluded symbolically holds for every concrete run. This is the paper's existing proof for the first-order fragment (A.8): its relation is "agreement" (conditions A1–A5), and its Assumption 10 (naturality, step by step) is exactly the simulation, assumed rather than proved. It is also how Aeneas's 2024 paper proves its symbolic semantics sound, and how the CompCert compiler is proved correct.

- For: the closest to the current design: no new model and no translation; the paper already has the relation and the proof structure for a fragment; the simulation is checkable rule by rule in Lean against the existing checker; gives adequacy and type safety.
- Against: it proves the checker's symbolic reasoning faithful to running programs, not that the logic's rules are consistent as a logic; consistency still needs an argument on top (Theorem 19 is one, for the fragment). The relation has to grow with every feature (closures, stuck blocks, dependent fields), and the paper lists the risky cases for the fragment alone.
- Learn more: Son Ho, Aymeric Fromherz and Jonathan Protzenko, *Sound Borrow-Checking for Rust via Symbolic Semantics* (ICFP 2024), the direct ancestor of Ochr's machine; Xavier Leroy, *Formal Verification of a Realistic Compiler* (CACM, 2009) for simulation proofs in general; the paper's own A.8.

### R4. A certifying checker: translate each accepted program into Lean

**What it is.** For every program the checker accepts, it also emits a translation into Lean: data types as Lean inductives, functions with borrow parameters as Lean functions returning their results and final contents (Aeneas's translation, done lazily, per program), and Ochr's proofs as Lean proofs. Lean's kernel then checks that translation. If it checks, the program's theorems are true in Lean, which is trusted to be consistent. Checking the output each time, rather than proving the checker correct once, is called **translation validation** or a **certifying** tool.

- For: correctness by construction for each accepted program, now, with no theorem about all programs: consistency is inherited from Lean. Incremental: start with a fragment and grow. Fits the north star of Ochr as a full theorem prover. A wrong rule shows up as a translation that does not check, not as a silent proof of `False`.
- Against: Ochr's definitional equality (running effectful code, closing off, observational `Eq`, η at `Unit`) goes beyond Lean's, so where an Ochr proof relies on two things being equal by computation, the translation must produce a Lean proof of that equality, possibly large. It does not explain why the rules are right, and gives no theorem "Ochr is consistent", only "every accepted program is checked". Whether the Lean translation means what the program does when run is a separate claim (adequacy of the translation).
- Learn more: Simon Boulier, Pierre-Marie Pédrot and Nicolas Tabareau, *The Next 700 Syntactical Models of Type Theory* (CPP 2017) for translations as models; Amir Pnueli, Michael Siegel and Eli Singerman, *Translation Validation* (TACAS 1998) for the per-run checking idea; Aeneas (ICFP 2022) for the translation of borrows into pure functions.

## Not routes to consistency

The two items below are often discussed alongside the routes, but neither delivers consistency on its own.

### Supporting: enforce the two-paths principle in the code's types

*Status:* done for the decisions read from declared types (branch `two-paths`, D74): they live in `Ochr/Decide.lean`, which cannot run the machine. Census: `ochr/core/notes/two-paths-census.md`.

**What it is.** Not a correctness story itself, but a way of making one of Ochr's conjectures true by construction. The checker's decision functions (erasure, capture modes, footprints, [Close]'s row, whether a match is on a proof) take only syntax and declared types as arguments, never evaluated values, and Lean's type checker enforces it. Then the two evaluation paths cannot decide differently, because the decision functions cannot see what differs between them.

- For: cheap; removes by construction the bug class behind many of the closed proofs of `False` found so far; makes "the two paths make the same decisions" a corollary of the checker's structure rather than a conjecture, which every route above needs.
- Against: shows only that the two paths agree, not that what they agree on is right. Some steps legitimately depend on values ([Split] takes the arm the value names; `Eq` computes on values), so the boundary of "decision" must be drawn carefully. It does not touch the dependent-field gaps (`GetN`), which are about what a value is allowed to be, not about which path decides.
- Learn more: this is the paper's §6.3 principle made mechanical; the general idea, using a type system to rule out a class of bugs, is "make illegal states unrepresentable" (Yaron Minsky).

### The baseline: the status quo

Rules forced by counterexamples, regression tests, near-miss twins, and the fuzzer. This is what Ochr does today, and what the routes would replace or underpin.
- For: incremental; has found every bug so far.
- Against: never yields consistency, only the absence of known counterexamples; it does not converge; it is the reviewers' main criticism of the paper.

## Cross-cutting

- **Where to start a theory.** The dependent-field rules are the part most visibly patched by counterexample (D64, D72, D73). A small model of values with a telescope and an "open" state, from which [Open], [Repack] and the whole-again points are derived rather than listed, would test R1 or R2 on the part that needs it most.
- **What a theory may remove.** Deriving rules can show some side conditions to be unnecessary as well as missing ones; correct by construction is also how Ochr becomes minimal, as `BRIEF.md` asks.
- **The role of testing under a theory.** Two uses remain: checking that the checker implements the theory (until the checker is derived from it or verified against it), and falsifying a candidate lemma cheaply before proving it, by aiming a generator at exactly that statement. Not bug hunting for its own sake; this is why fuzzing Forded declarations was not pursued.

## Where the discussion stands

The user's view: the goal is correctness by construction, and fuzzing does not move the project towards it except by accident. The team-lead's current leaning: the two-paths enforcement now, since it is cheap, removes the known failure mode and every route needs it. Then a correctness story: R2 (semantic types over the machine) fits Ochr's "typing is running" best and delivers all three properties, but is the largest; R3 (simulation) is the continuation of the paper's existing fragment proof and the cheapest way to a real theorem; R4 (certifying checker) gives per-program guarantees soonest and fits the theorem-prover north star. R1 is the classic route to consistency but needs a separate adequacy theorem to say anything about running programs.
