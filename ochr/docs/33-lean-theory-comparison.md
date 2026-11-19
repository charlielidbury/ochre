# 33. Lean's metatheory and ours: the differences, and which we could remove

Written 2026-11-19 by a fork of the orchestrating session. It compares Mario Carneiro's thesis *The Type Theory of Lean* (`docs/papers/theory-of-lean.pdf`, all 44 pages read) with our consistency plan (`ochr/docs/18-consistency-proof-plan.typ` on main at `2b156769`) and the Lean development on the `spine` branch (`ochr/core/lean/Ochr/Meaning/`). The standing instruction is to follow Lean as closely as is reasonable, on the presumption that its choices were made for good reasons. So for each difference this note says what Lean does, what we do, why we differ, and whether we should stop differing.

Every verdict is this author's judgement, made from reading and not from trying. Where a verdict is a guess, it says so. Section numbers (§) are the thesis's.

## Summary

| # | Difference | Forced, or an accident of how our model grew | Verdict | Size of the change |
|---|---|---|---|---|
| 1 | Lean interprets typed terms directly; we simulate the checker's steps by a reference run over states | Forced: we check by running, with state | Keep ours | none |
| 2 | Lean proves a declarative system sound and shows its algorithm is inside it; we prove the algorithm directly | A choice, not forced | Unclear; worth a one-day trial | large if adopted |
| 3 | In Lean a type's meaning can be a tagged code that remembers how it was built (§6.4); ours is a set with optional side information bolted on | Accident | Adopt Lean's, uniformly | large |
| 4 | Lean never looks inside a value without its type; our reference run did | Accident | Adopt Lean's (already under way) | small |
| 5 | Lean's model lives in untyped ZFC sets; ours in Lean's own types, with elements tagged by type and three hard-coded levels | Forced by mechanising in Lean without a set-theory library | Keep ours | huge if changed |
| 6 | Which universe statement is proved | Forced by proving inside Lean | Keep ours; adopt Lean's wording | trivial |
| 7 | `Prop` sits in `Type₁` for us, in `Type₀` for Lean; we have no universe polymorphism | Forced (what may be borrowed), and a simplification | Keep ours | none |
| 8 | Lean splits proofs from data using unique typing (§6.1); we read it from syntax | A deliberate divergence | Keep ours: it is simpler than Lean's | none |
| 9 | Lean needs unique typing and Church–Rosser (§4); we need neither | Follows from 1 and 8 | Keep ours | none |
| 10 | Definitional equality: Lean's is declarative and undecidable, with an incomplete algorithm; ours is one algorithm on normal forms that runs code | Forced by checking by running | Keep ours; say plainly what we do not claim | trivial |
| 11 | η: Lean has it for functions; we have it for `Unit` and one-constructor types and not for functions | Accident | Unclear; an incompleteness, not a soundness matter | medium |
| 12 | `let` and definitions are substitution in Lean; in ours a `let` is a place and a definition is re-run | Forced by state | Keep ours | none |
| 13 | What inductive types may be declared | A simplification | Keep for the proof; two expressiveness gaps to weigh | none now |
| 14 | How inductive types are modelled: Lean reduces to eight fixed formers and well-founded trees; we model each declaration directly, with existence unproved | Accident | Unclear; borrow Lean's "skeleton plus predicate" when the existence proof is attempted | medium |
| 15 | Recursion: recursors in Lean's kernel; `fix` with a decreasing argument in ours | A choice that suits in-place code | Keep ours | none |
| 16 | Eliminating a proof to produce data: Lean allows more, and pays with undecidability | A deliberate restriction | Keep ours | none |
| 17 | Equality: an inductive family in Lean; a primitive that computes on constructors in ours, plus `Id` | A choice | Keep; low confidence | medium if changed |
| 18 | Quotients, propositional extensionality, choice: Lean has them; we have no axioms | Not yet wanted | Keep; all three could be added without changing the model | none |
| 19 | What fails in Lean (§3): undecidable equality, non-transitive checking, no subject reduction for the algorithm | Different causes | Nothing to adopt | none |
| 20 | Function types | Forced by borrows | Keep ours | none |
| 21 | Things with no counterpart in Lean | Forced | Keep | none |

## The three changes most worth making

1. **Make a type's meaning a tagged code, uniformly, as §6.4 does (entries 3 and 4).** Our model began with "a type means a set" and has since had a level tag, a function shape and a data-type name with parameters added to it one fault at a time. Each open fault in the reference run's treatment of types (the result of a call loses its function shape and its data parameters; a function type computed by a call has no shape; a field read loses the same structure; a value was decoded by guessing its declaration from its set) is a place where the side information was not carried. Lean's tagged types carry it everywhere by construction, because the code of a function type holds a function from arguments to codes, not to bare sets. The redesign of a call's result is already queued; doing it Lean's way would close the others in the same move. Confidence: medium. The cost is real: Lean the proof assistant has no direct way to define codes together with their decoding, so it needs an encoding (codes indexed by the type they decode to), and the four core lemmas would be re-proved.
2. **Try, for one day, putting a declarative judgment between the checker and the model, as Lean does (entry 2).** Lean never reasons about its type-checking algorithm semantically. It proves a rule system sound, and separately that whatever the algorithm accepts is derivable in the rules. We reason about the algorithm itself, and a large share of the statement faults found this week were about the algorithm's plumbing (step budgets, logs, label counters, values in flight) and not about meaning. This is the most speculative of the three, and it adds a third formal object to keep in step with the checker. A trial on the one step now being proved, the drop at the join, would show whether the semantic proof gets shorter.
3. **When the existence of the data model is proved, use Lean's "skeleton plus predicate" (§5.2) and a native tree type (entry 14).** Our generic model of user data types is built by stages and a quotient, its existence for every accepted program is unproved, and it has two known gaps. Lean's translation erases what varies between occurrences to get a plain tree type and then carves out the good trees with a predicate. Confidence: low to medium; it should be weighed when that work starts, not now.

Three places where we are already simpler than Lean, and should not move towards it: reading "is this a proof" from syntax (entry 8), forbidding recursion on proofs (entry 16), and having no axioms (entry 18).

## The entries

### 1. The shape of the soundness theorem

**Lean.** The model interprets typed terms in a context directly. §6.2 defines `⟦Γ ⊢ e⟧γ` by recursion on the size of the term, where γ is an element of `⟦Γ⟧`, a choice of a value for each variable. Theorem 6.7 has four parts: a proposition denotes a subset of `{•}`; a proof denotes `•`; a well-typed term denotes an element of its type's set; definitionally equal terms denote the same thing. It is proved by induction on typing derivations, after two basic lemmas (6.6): weakening and substitution.

**Ours.** There are no typing derivations to induct on: the checker checks a definition by running it once on unknowns. So docs/18 (the main theorem, "meaning preservation, membership and well-formedness") gives every state the checker reaches a meaning under an *assignment* of its unknowns, defines a *reference run* that says what a term means as a transformer of such states, and proves that each checker step is matched by it. The pieces correspond closely: our assignment is Lean's γ; the types of our unknowns are Lean's context Γ; our membership part is Lean's third part; our conversion lemma is Lean's fourth; our four core lemmas and the unproved "locality in the unknowns" are Lean's substitution and weakening.

**Why we differ.** Forced, twice over. The checker is an evaluator, so the only "derivation" is its run. And terms have effects on a state with borrows, so a term means a state transformer, not an element.

**Verdict: keep ours.** Nothing in Lean's shape removes the need to relate the checker's intermediate states to meanings. High confidence. But see entry 2 for the one part of Lean's shape we did not copy and could.

### 2. A declarative system between the algorithm and the model

**Lean.** The thesis keeps two judgments apart from the first page of the rules (§2.2): the "ideal" typing and definitional equality, and the "algorithmic" equality that Lean's kernel actually checks. The soundness theorem is about the ideal system only. The algorithm is connected to it by a syntactic lemma (3.4, part 3: algorithmic equality of well-typed terms implies definitional equality), and §3 opens by saying that this is the plan: "anything Lean verifies as type-correct will be derivable in this axiom system and hence Lean will not certify a contradiction". The algorithm's own awkward properties (it is incomplete and not transitive, §3.1.1) never touch the model.

**Ours.** There is no ideal system in the proof. The Lean statement is about `checkProgram` at a fuel, and every step lemma is about a function of the checker run in its state monad. docs/18 says why this was chosen ("Rules and checker": the correspondence of the paper's rules with the checker "is tested, not proved. A proof against the checker makes this moot"). The price is visible in what the mechanisation has had to repair: a step budget fixed so that the induction hypothesis did not apply to sub-calls; a run that was assumed to start from an empty log; label counters that differ between the two sides and needed a renaming; values "in flight" in the checker and parked in a temporary in the reference; an induction that is a knot tied over the budget because no step can be proved alone.

**Why we differ.** A choice, not forced. The paper's rules exist, the checker fires each rule by name, and a trace in the rules' names is already produced.

**Verdict: unclear; worth a bounded trial.** Lean's arrangement would be: (a) the paper's rules as an inductive relation in Lean, a big-step judgment on the checker's own state type; (b) a syntactic proof that an accepting run of the checker yields a derivation, which involves no meanings at all; (c) the semantic proof by induction on derivations, where the induction hypothesis is available at every sub-derivation without a budget. It could delete the budget-indexed knot and much of the plumbing above from the semantic proof. It costs a third formal object beside the checker and the reference run, which must be kept in step with the checker, and part (b) is a proof over all 4,200 lines of the checker. I am speculating about the size of the saving; the earlier route decision (docs/23) may have considered and rejected this, and I did not re-read it. A fair test is one day on the step now open, the drop of one place at a join: write its rules, and see whether the semantic half is shorter than the current statement's proof plan.

### 3. What a type means: a set, or a code that remembers its construction

**Lean.** In the main model a type denotes a set and nothing more. §6.4 ("Type injectivity") then observes: "The semantics we have given for types collapses many types into the same ZFC set, somewhat by accident in the sense that ZFC does not track the complete construction of a type". Its remedy is a set of *tagged* types: a type denotes a code such as `(Π, A, B)`, `(Σ, A, B)`, `(W, A, B)`, `(+, A, B)` or `(U, n)`, with a decoding function from codes to sets, and in the code of a function type `B` is a function from the elements of `A` to *codes*. Elements are taken from the decoding. The soundness proof is "virtually unchanged", since "none of the tags affect any of the reasoning" (Theorem 6.9).

**Ours.** On paper (docs/18, "meaning of types"; docs/24, choice C2) a type means a set outright, as in Lean's main model. In the mechanisation a type's meaning is `TyM` (`Sem.lean`): a Lean type tagged with its level. The reference run then needed more than the set, and three pieces of side information were added in a record around it (`TyS`, `Pi.lean`): a function type's *shape* (its parameters and result, without which a function value cannot be applied), the label of a borrow, and a data type's declaration name and parameters (without which a constructor value's parameters cannot be read). Each was added after a fault. The record is not closed under the type formers: a function shape's result is a function to bare `TyM`, so the result of a call has no shape and no data (`Regress/ShapeAgree.lean`, `call_noShape`). docs/18 lists what this leaves open: a function returned by a call cannot be called; a parameter whose function type is computed by a call (`f : Fn(Nat)`) cannot be called; a field read loses the same structure; and until this is redesigned the mechanised theorem is false on such accepted programs.

**Why we differ.** An accident of how the model grew: the paper model needs only sets, and the need for construction information appeared one case at a time in the mechanisation.

**Verdict: adopt Lean's, uniformly.** Make the meaning of a type a code that is closed under every type former and decodes to a carrier, so that every type the run ever holds, including one returned by a call or read from a field, has its full structure. This is the same thing the queued redesign of a call's result (docs/31, the entry on a function type's shape) does for one case. What it would delete: the open differences listed above, the optional fields of `TyS`, and the class of fault in entry 4. What it costs: codes and their decoding are defined together, which Lean the proof assistant cannot do directly; the usual encoding indexes each code by the type it decodes to. The spine's notes record that a nested definition was avoided once for cost. The four core lemmas would be re-proved. Size: large. Confidence that it is the right direction: medium; that it is cheaper than closing the gaps one by one: low to medium.

### 4. Looking inside a value

**Lean.** Never without its type. Every eliminator in the model is typed: the recursor of a tree type is interpreted with that type's set as a parameter, the eliminator of a sum is a function on the disjoint union of the two given sets (§6.2). Two types that denote the same set are no problem, and §2.7.2 notes that Lean itself lets one "write exactly the same inductive definition twice and get two possibly distinct (but isomorphic) types".

**Ours.** The reference run navigates values held at places in a state: the tag a match reads, a field at a path, a write or a drop at a path. It found the declaration by taking the first one whose carrier equalled the value's type, and two declarations can have equal carriers; with `B1 := T1 | F1` and `B2 := F2 | T2` the model computed the wrong arm (found on the spine on 2026-11-19, `Regress/DataOfChoice.lean`). The fix under way decodes through the stored type's declaration name and parameters.

**Why we differ.** Accident. Navigating by path through a state is forced; doing it without the type was not.

**Verdict: adopt Lean's; it is being adopted.** The fix is the thesis's discipline. It needs a new clause of the invariant (a constructor value's recorded parameters are those of its position's type). Small. High confidence. It becomes automatic under entry 3.

### 5. Where the model lives

**Lean.** In ZFC. Everything is an untyped set in one hierarchy: a pair is a pair, a function is a set of pairs, a universe is a stage `V_κ` of the hierarchy (§6.2), a sum's elements are marked pairs. Meaning is defined first and membership proved afterwards.

**Ours.** On paper, the same (docs/18 cites §6.2 as what it adapts). In the mechanisation, inside Lean's own type theory: a type means a Lean type holding only its good elements, and a value means an element tagged with the Lean type it belongs to (`Sem.el0 A a`, and the same at two more levels). `Sem.lean` gives the reason: "Lean has no small type closed under its own function space, so an untyped universe holding functions on itself cannot be an inductive type". Consequences: three hard-coded levels with one constructor each in the types of meanings, elements and carriers; meaning and membership built together (docs/24, "Where the paper and the encoding differ"); an explicit error value; and carriers that are opaque, which is the root of entries 3 and 4.

**Why we differ.** Forced by mechanising in Lean with Lean's core library only. The alternative is a set theory inside Lean (Mathlib has one), which would let the model be the thesis's almost literally.

**Verdict: keep ours.** A ZFC-in-Lean model would remove the level triplication and the opacity, but it is a rewrite of everything built, adds a large dependency, and trades Lean functions (which compute, so concrete runs can be checked by the kernel) for sets of pairs (which do not). I am not confident the grass is greener; I am confident it is too late to find out cheaply. Entry 3 recovers most of what opacity costs.

### 6. Universes: what is assumed and what is proved

**Lean.** Universe levels are expressions with variables, `max` and `imax`; universes are not cumulative (§2.1, §2.8). The model sets `U₀ = {∅, {•}}` and `Uₙ₊₁ = V_κₙ` for inaccessible cardinals κₙ (§6.2). Each soundness statement is "there exists a k such that if the first k cardinals are inaccessible, then…" (Theorem 6.7), so a given proof uses finitely many, and the corollary is that Lean is consistent if ZFC with n inaccessibles is, for every n (6.8). §1.2 adds the converse from Werner: Lean with n+2 universes proves ZFC with n inaccessibles consistent.

**Ours.** The paper target assumes "one inaccessible cardinal per universe level used", which is Theorem 6.7's k. The Lean statement being mechanised is bounded: the program writes nothing above `Type₁` (`consistencyBounded`). docs/18's first open question asks whether a uniform statement over all levels is wanted.

**Why we differ.** Forced by the host. A proof inside Lean cannot quantify over universe levels, and by the Werner result quoted in §1.2 Lean cannot prove a statement that needs all levels at once if Ochr is as strong as Lean.

**Verdict: keep the bounded statement, and adopt Lean's wording for the paper.** "For each accepted program there is a k, the highest level it writes, such that…" is exactly the thesis's form, and the bounded Lean theorem is its instance at the k every program in the suite uses. That removes the appearance of a gap. Trivial. High confidence.

### 7. The universe structure

**Lean.** `Prop` is the lowest sort and lies in `Type₀`. Definitions are universe polymorphic.

**Ours.** `Prop : Type₁`, beside `Type₀ : Type₁`, as in Coq (`ochr/core/RULES.md`; the decision that made it so is D66 in `DECISIONS.md`). No level variables that I could find in `RULES.md`.

**Why we differ.** Forced by borrows: a borrow `&A` is allowed exactly when `A : Type₀`, so `Type₀` must hold only runtime types, and propositions and universes must be outside it. D66 records Lean's arrangement as the fallback "if a real use of `Prop` at `Type₀` appears".

**Verdict: keep ours.** The model is unaffected. Having no level polymorphism is a simplification the thesis itself treats as harmless ("universe polymorphism is a luxury", §2.8).

### 8. Telling proofs from data

**Lean.** The model must interpret a function type into a proposition differently from one into data (the first as a truth value, the second as a set of functions; both clauses are in §6.2). Which one a term is cannot be read from Lean's syntax, so §6.1 first translates every term into a "proof split" language with two kinds of λ, application and Π, using a `sort` function that exists only because of unique typing (Lemma 6.1). The introduction notes a way round: with Barras's trick of encoding functions so that the constant function to `•` is `•` itself, "we can avoid the dependency on unique typing in the proof of soundness".

**Ours.** The split is in the language. Whether a term is a proof or forms a type is read from syntax and declared types without evaluating anything (docs/18, "Erasure and private copies": "Sorts are syntactic"), a function type carries its *class* (returns types, returns proofs, other) from its codomain term, and function types of different class are not convertible. The model's clause for a function type into a proposition is the same truth value as Lean's.

**Why we differ.** A deliberate design decision, taken because decisions read from computed values had produced closed proofs of `False` (`ochr/core/CLAUDE.md`, "Decisions never read a run").

**Verdict: keep ours.** This is one of the places we are simpler than Lean: the whole of §4 exists in the thesis largely to make §6.1 possible. High confidence.

### 9. Unique typing and Church–Rosser

**Lean.** §4 proves that a term's type is unique up to definitional equality, through a Church–Rosser theorem for a modified reduction; the thesis calls the argument "tricky" and "novel". It is needed for the proof splitting of entry 8.

**Ours.** Neither is stated or needed. There is no reduction relation on terms to be confluent (the evaluator is deterministic), and the typing facts a step needs are carried by the invariant proved in the same induction (membership, and clauses of well-formedness).

**Why we differ.** It follows from entries 1 and 8.

**Verdict: keep ours.** One caution: our substitute is that typing facts are part of the invariant, and several are still only "read off the checker" (docs/18 lists clauses of well-formedness not yet shown preserved). Lean pays for these facts once, syntactically; we pay per step.

### 10. Definitional equality

**Lean.** A declarative relation with β, η, unfolding of definitions and `let`, the computation rules of recursors, and proof irrelevance (§2.2 to §2.6). It is undecidable (§3.1). The kernel checks an algorithmic approximation that is incomplete and not transitive (§3.1.1). Soundness is stated for the declarative relation.

**Ours.** One algorithm, on values kept in normal form: structural comparison, sealed programs compared by their text, and two function values compared by running each at fresh unknowns and comparing what is observed (docs/18, "Conversion"). In substance the last rule is Lean's rule for comparing two λs under a binder, done by evaluation; the observation replaces "the bodies are equal" because bodies have effects. Its soundness (docs/18, "conversion respects meaning") is argued under assignments and shares the main theorem's induction, because the check runs code.

**Why we differ.** Forced by checking by running. The entanglement with the main induction comes with that.

**Verdict: keep ours; say plainly what we do not claim.** docs/18 already says consistency needs no termination. It should also say, as the thesis does of Lean, that our conversion is not claimed complete, transitive or decidable, and that none of the three is used: each successful check is justified by equal meanings, and equality of meanings is transitive whatever the algorithm is. Trivial.

### 11. η

**Lean.** η for functions is a definitional rule (§2.2). Proof irrelevance makes every two proofs equal. The thesis adds η for pairs and lifts only for its reduction (§5.1).

**Ours.** "There is no η-rule" in conversion (docs/18, "Conversion"). Instead a value is `()` wherever its declared type reads as `Unit`, an unknown of a one-constructor type is refined to that constructor when needed, and every proof is the one value `⋆`. For functions, two function values are compared only if their captured values are pairwise convertible, so `f` and `λx. f(x)` are not convertible, though they mean the same function in the model.

**Why we differ.** Accident, as far as I can tell: the model satisfies function extensionality (it is proved in the slice, `pi_ext`), so the checker is stricter than its own model here.

**Verdict: unclear.** This is an incompleteness, not a risk to consistency; docs/18 lists a relative of it ("two copies of a function that inspects its argument are not convertible"). Dropping the condition on captures might be all that function η needs, but docs/18 also warns that conversion must stay "least" because a looser reading identified stuck functions and proved `Eq(Nat, S(Z), Z)`, and I cannot tell whether the condition on captures is part of that guard. Not for now.

### 12. `let` and definitions

**Lean.** Both are substitution: a `let` unfolds (§2.4), a definition unfolds (§2.5), and each is a conservative extension for that reason.

**Ours.** A `let` binds a place that can be borrowed, written, moved out of and dropped at the end of its scope. A definition is checked once and then run again at each call with known arguments, or closed off into a sealed program when the call is stuck.

**Why we differ.** Forced by state and in-place mutation.

**Verdict: keep ours.**

### 13. Which inductive types may be declared

**Lean.** General inductive families: parameters and indices, recursive arguments under functions (so infinitely branching trees), at any universe, with the constraint that a constructor's arguments fit the type's universe (§2.6.1).

**Ours.** Parameters only, with an index fixed by an equation field ("Fording"); recursive occurrences only as whole field types or nested at a "nestable" parameter, never under a function type; declarations only in `Prop` or `Type₀`, with every field in `Prop` or `Type₀` (docs/18, conditions (I1) to (I6) under "the model is well defined").

**Why we differ.** A simplification. With no recursion under a function type the least fixed point is reached in ω stages, so ranks are natural numbers; docs/18 notes this "is one reason Ochr may be weaker than Lean". The universe restriction keeps data in the universe that may be borrowed.

**Verdict: keep for the proof.** Two gaps against "as good as Lean for proving" should be weighed by the language's owners, not by the proof: no infinitely branching trees, and no data type with a field that is itself a type (so no record that packages a type with operations on it). Both could be lifted later along the thesis's lines (§6.2.1 gives the fixed-point construction that needs transfinite stages) at a cost to the model. I am guessing at how much either matters in practice.

### 14. How inductive types are modelled

**Lean.** Not directly. §5 reduces every inductive type to eight fixed ones (empty, dependent pair, sum, lift, truncation, well-founded trees, equality, accessibility) and the model handles only those (§6.2, §6.2.1). A family with indices becomes a plain tree type, the "skeleton", together with a predicate `good` picking out the trees that belong at each index (§5.2). The reduction is unfinished: §5.4 leaves the constructors, the recursor and its computation rule "as future work" and proceeds "with the understanding that the eight inductive types … are indeed sufficient".

**Ours.** Each declaration is modelled directly. `DataGeneric.lean` builds a carrier for every parameter tuple as the limit of ω stages, a quotient of the union of the stages, behind an interface (`DataModel`) of packing, tag, fields and rank. That such a model exists for every accepted program is stated and unproved (`exists_dataModel`), and docs/18 names two gaps (recursion nested through an earlier type, and fields typed by a parameter).

**Why we differ.** Accident of the route: our fields are first-order, so stages looked simplest, and the slice built type functions the same way.

**Verdict: unclear; borrow one idea when the existence proof is attempted.** We should not copy the reduction: it is the part of the thesis its author did not finish. But §5.2's idea fits us well. Our recursion is finitary, so the skeleton of a declaration is an ordinary Lean tree type with a constructor tag, the non-recursive fields and finitely many children, which Lean gives with its induction principle and a height for free; the non-uniform parameters and the telescope conditions go into a predicate. That would replace stages and the quotient. Whether it is less work than finishing what exists I cannot say without trying. Medium size, low to medium confidence.

### 15. Recursion

**Lean.** The kernel has only recursors; user-level recursion is compiled to them. §2.8 says of Coq's alternative, a `fix` with a check that recursive calls are on smaller arguments: "in theory these approaches are equivalent, the fix/match approach is more expressive, and the equivalence is sensitive to the exact rules".

**Ours.** Coq's alternative: `fix` with a named decreasing parameter, checked by the recursion rule (each recursive call's argument is a strict part of the entry value). The model gives every `fix` a meaning by recursion guarded on the rank of that argument, and membership says the guard never fires (docs/18, "meaning of a state"; docs/24, choice C6).

**Why we differ.** A choice that suits the language: recursion over a borrowed structure, updating it in place, is written directly, and a recursor, which takes its cases as functions, does not fit code with effects.

**Verdict: keep ours.** High confidence. The cost is the recursion rule's own obligations (docs/18, "Recursion"), which Lean avoids by having nothing to check.

### 16. Eliminating a proof to produce data

**Lean.** Allowed for an inductive proposition with at most one constructor whose non-recursive arguments are propositions or appear in the output type (§2.6.2). That admits equality and accessibility, and with them recursion on a proof of accessibility. Together with proof irrelevance this is what makes definitional equality undecidable and the checking algorithm non-transitive (§3.1).

**Ours.** A match on a proof may produce data or a type only when the proposition has no constructor, or one whose fields are all proofs; and recursion is never on a proof (docs/18, conditions (I7) and (I8)). Equality is a primitive with its own transport.

**Why we differ.** A deliberate restriction.

**Verdict: keep ours.** It keeps us out of the thesis's §3.1 entirely. The costs are stated in docs/18's list of incompletenesses (elimination from a proposition whose index leaves one constructor possible is refused) and in entry 15 (no recursion justified by a well-founded relation). High confidence for the proof; the expressiveness cost is the language owners' call.

### 17. Equality

**Lean.** An inductive family with one constructor, eliminated by its recursor, with a special reduction rule that lets the recursor compute on any proof (§2.6.2, §2.6.4). That constructors are injective and distinct is derived, not built in.

**Ours.** `Eq` is primitive and computes: on two values of one constructor to the conjunction of the fields' equations, on different constructors to `False`, on convertible values to `True`, and it decides on the moved-out marker; otherwise it is stuck. Transport computes only at convertible endpoints. And there is a second equality, `Id`, between two computations, which has no counterpart in Lean (entry 21). Both models read an equation as the truth of "the two sides mean the same".

**Why we differ.** A choice: proofs by computation, and `Id` computing to a conjunction of plain equations.

**Verdict: keep; low confidence.** Lean's version would delete the condition on how `Eq` may decide ((I9) in docs/18), the steps for the computing cases, and the rule for moved-out values in equations, which was the site of one of the closed proofs of `False`. It would cost the ergonomics the case studies rely on. I would not reopen it for the proof's sake.

### 18. Quotients, propositional extensionality, choice

**Lean.** All three, as axioms; the model interprets each (§2.7, §6.2; choice needs a choice function on the whole model).

**Ours.** None. docs/18: "Every definition has a body, so holes are the only axioms."

**Why we differ.** Not yet wanted.

**Verdict: keep.** Nothing to remove. All three hold in our model as they do in Lean's (propositions are two-valued, functions are set functions, and our own proofs already use Lean's choice), so any could be added later without touching the proof; quotients would need a new type former and one model clause.

### 19. What fails in Lean

**Lean.** §3: definitional equality is undecidable; the algorithmic equality is not transitive; the algorithmic typing judgment does not have subject reduction. "Lean's typechecker is not complete."

**Ours.** The specific cause (accessibility with proof irrelevance) is absent by entry 16. Our own checker is incomplete for other reasons: it runs with a fuel budget and can answer "undecided", and docs/18 lists true programs it rejects. Subject reduction does not arise: there is no reduction of typed terms.

**Verdict: nothing to adopt.** Worth one sentence in docs/18, with entry 10's.

### 20. Function types

**Lean.** One binder at a time; a function denotes a set function.

**Ours.** All parameters at once, calls saturated, and a parameter may be a borrow. A function type with borrow parameters denotes functions that also return the final contents of what they borrowed, or, when they return a borrow, a forward value and a *backward function*, which must be injective (docs/18, "meaning of types" and "injectivity relation").

**Why we differ.** Forced by borrows.

**Verdict: keep ours.**

### 21. Things with no counterpart in Lean

States and places; borrows, loans and the "future" a state's meaning depends on; lending and when a borrow ends; closing off a stuck call into a sealed program; splitting on an unknown and its worlds; statements run on a private copy; the drop at the join of a match; `Id` and its observation; the well-formedness invariant. All are forced by in-place mutation and by checking by running. They are where almost all of our proof effort goes, and the thesis has nothing to say about them. The nearest published guide for them is the Aeneas work that docs/18 already cites, not Lean's metatheory.

## What this comparison does not cover

I did not re-read docs/23 (the decision for the meaning-preservation route) or the paper's appendix of rules, so entry 2 may repeat a path already considered. I did not check any claim about the spine by building it; file names and statement names are as the sources state them on `origin/spine` at the time of writing.
