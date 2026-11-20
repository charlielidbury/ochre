# 35. Four themes behind the problems of the consistency proof, and what would remove them

Written 2026-11-20 by the orchestrating session of the consistency effort, at the user's request. It is numbered 35 because 34 is the data-model note on the `spine` branch.

Most documents here record one problem and its fix. This one steps back from about a week in which the effort landed eleven checker changes, rebuilt the model several times and found some twenty of its own statements false, and asks what those problems have in common. Each theme below names a pattern, gives the incidents that show it, and proposes one conceptual change that would stop the whole class from arising instead of solving its members one at a time.

These are the orchestrator's judgements. The incidents are facts, recorded in `docs/32` (work units, with the per-area counts), `docs/31` and `docs/34` on `spine`, and `core/DECISIONS.md`. The proposals are untried except where a section says otherwise.

| Theme | Size | Who decides | Status |
|---|---|---|---|
| 1. Ochr is defined by an algorithm, not by rules | large | the user: it changes what the paper means by "the rules" | a bounded trial on one area is planned (the user agreed, 2026-11-20) |
| 2. One evaluator, written three times | medium | the user, as a refactor of the checker | not started; much of it falls out of theme 1 |
| 3. Classifications re-derived by parallel readers | small to medium | the orchestrator, change by change | under way piecemeal (two of the eleven changes were this) |
| 4. Statements are found false by proving them | small (tooling) | the orchestrator | partly in place (tests on recorded states); the next step is costed below |

## Theme 1. Ochr is defined by an algorithm, not by rules

### The pattern

The checker is a machine of about 4,400 lines (`Machine.lean`) that runs a program on symbolic states. The consistency proof is a proof about that machine: for each of its functions there is a statement saying the function's effect on the machine's state is matched by a step of the model. So every detail of how the machine does its work is a detail the proof has to speak about, whether or not it has anything to do with the language.

Most of the statements found false in the week were false about such details, not about the language:

- A conversion of two functions was said to leave the state unchanged. It creates unknowns on a private copy, and their types are kept afterwards.
- A substitution was said to leave the state unchanged. It re-runs stuck programs, and those runs keep the unknowns they make.
- Nine obligations of the first slice were false from one cause: a step that creates unknowns must conclude under an extended context and extended decisions, and they concluded under the context they started with.
- The steps read the machine's tail-position flag at the wrong one of its two levels, so a body's `let` was compared with the model out of tail position.
- Leaving one world of a split concluded nothing about the context, so no step could follow it.
- A private copy held one borrow twice (fixed in the checker).
- The checker's syntactic decisions wrote caches into its state, so "a decision leaves the state unchanged" was false until the caches were removed at a 13 to 16 percent cost in check time.
- A decision read an unknown's type, which a later refinement rewrites; the fix was to freeze each unknown's reading when it is created.
- The model has to re-do the checker's solving of a constructor's parameters from its fields, and cannot (below).
- Every statement carries fuel, and the recursion argument needed a strong induction on it.
- The form of the statements themselves changed four times while the first composition was being proved.

None of these says anything a programmer would recognise as a fact about Ochr. Each is a fact about tables that grow, copies that are restored, flags and fuel.

One incident shows the pattern exactly. The checker accepts `let w = MkW(t)` with `t : Tag(3)` and `inductive Wrap (n : Nat) := MkW(t : Tag(n))`, solving `n := 3` from the field's type. That is inference: it finds an argument the programmer left out. Because the machine does it while running, the model's run has to do it too, from meanings, and it cannot, because recovering `3` from the meaning of `Tag(3)` needs `Tag` to be injective. The decision taken is to stop the checker inferring such parameters. In Lean the same inference is harmless: the elaborator guesses `3`, writes it into the term, and the kernel checks a term in which nothing is left to solve.

### The change

Split the definition of the language the way Lean and Rust both do.

- **A core with nothing left to decide.** Terms in which every choice the machine now makes on the fly is written down: where each borrow ends, what is lent at a call, what the join drops, whether a read copies or moves, what is erased as a proof, a constructor's parameters, whether a match computes, splits or closes off, which captures a stuck block touches on entry. The proof already carries most of this as a table of decisions beside the term; the core is the term with that table written into it.
- **Rules over the core.** A typing judgement in which each rule's premises are checks, never searches, and a separate relation saying when two types are equal. The paper already presents the language as named rules, and the checker already tags each step with one of about 110 rule names (`Rules.lean`) and logs which fired. Today that log is text and nothing checks it.
- **The machine as elaborator.** The present machine keeps doing what it does, and its output is a core term (or a derivation). How it finds that term, with which tables, copies, flags and fuel, stops being part of the language.

The proof then has two parts that do not touch each other. (A) Each rule is sound in the model: one lemma per rule, about meanings, with no machine state in it. (B) Whatever the machine accepts has a derivation. For (B) there are two options: prove it, which is a syntactic argument about the machine that never mentions the model; or do not prove it and instead re-check the machine's output with a small independent checker of the rules, so that the theorem is about that small checker and the machine is untrusted. The second is Lean's arrangement (an untrusted elaborator and a small kernel) and Rust's (borrow checking on a lower-level form with explicit drops).

### What it would erase, and what it would not

It would erase from the model-side proof: growing tables, private copies and their restoration, the tail flags, fuel, the alignment of decisions and their extension after each step, the caches and frozen readings, and the need for the model to imitate inference. Those are the subject of most of the false statements listed above and of a large share of what the step statements still to be proved have to say.

It would not erase the hard semantic content, which is the same under either arrangement: the set model and its data layer, the meaning of a state with live borrows, the substitution lemmas, the recursion argument, and dependent values that are partly moved or lent.

What carries over unchanged: the model (types as codes, tree values, the data layer), the four core lemmas, and the reference run, which is already close to a semantics of such a core: it takes its decisions from a table, it never gets stuck, and it never infers anything. The breadth pass's decomposition of each area into named pieces carries over too, since a named piece is roughly a rule.

### Why not simply switch

The current route is converging. The last five areas attacked forced no change to the simulation relation and one small change to the model, and the top-level chain now closes, from named statements, for constants and for recursive functions. So this is not a rescue. The case for it is about what remains: the leaves are where the machine's bookkeeping is thickest, and every later change to the checker's implementation, even a refactor that changes no verdict, invalidates proofs about the machine, where it would leave proofs about rules alone.

The risks are real. Symbolic running with unknowns and stuck programs is how the checker decides type equality, and a declarative account of it has to be found, not assumed; `docs/33` (items 1, 2 and 10) judged "we check by running, with state" to be forced and a declarative layer to be "unclear; worth a one-day trial". Borrow state has to appear in the judgement; the symbolic semantics mechanised in `aeneas/` is a precedent for rules of that kind, not a proof it fits here. And part (B) could turn out to be as much work as what it replaces.

### The bounded trial

Agreed with the user on 2026-11-20. One area, a few days at most, run before provers are spread over the remaining leaves, because its result decides how those leaves should be proved.

- **Area:** equality and `J`. It is small, its step statements and sixteen named pieces already exist to compare against, and it is where the bookkeeping (private copies, unknowns that outlive a conversion) caused the most false statements per line.
- **Deliverables:** (1) the area's rules as an inductive judgement in Lean over explicit terms, taken from the paper's rules for it; (2) each rule proved or attacked for soundness in the existing model, with no checker state in the statements; (3) for the same accepted and rejected programs the area's regress file uses, the derivation the machine's run corresponds to, built by hand or by a small function from the machine's log, and a statement of what the log would have to carry for a checker to rebuild it; (4) a written comparison with the area's present statements.
- **It succeeds if** the rule-soundness statements mention none of tables, copies, flags, fuel or extended decisions; the false statements this area produced could not have been written in the new form; and the link from the machine to the rules is either mechanically checkable from an extended log or a syntactic argument visibly smaller than the sixteen pieces.
- **It fails if** the rules need the machine's state to be stated at all (for instance, if equality of types cannot be given except as "what the machine computes"), or the link from the machine is as large as the present proof. A failure is recorded here with its reason, and the present route continues unchanged.
- **Either way** the present route is not paused for it.

Started 2026-11-20, late evening (branch `rules-trial`), narrowed on starting to one real piece instead of a paper design: the checker's comparison functions for equality (`conv`, `convPi`, `convFn`, `mkEqM`), whose statements are open obligations of the present proof. The paper already defines conversion as "the least relation closed under" five named rules, so the trial writes that relation in Lean, proves it sound in the model, proves the machine's run yields a derivation, and composes the two into the existing statements. A proved obligation comes out of it whichever way the verdict goes. One correction to this section's claims, to be tested by the trial: a step that creates an unknown its result mentions must conclude under an extended context under any architecture; only the unknowns nothing mentions afterwards are bookkeeping.

First checkpoint (2026-11-20, late evening): the relations, both halves stated, and the composition into the existing statements proved from the two halves. What it showed so far:

- The rules needed only values and declarations, nothing of the machine's state. The soundness half mentions no table, copy, flag or fuel.
- It found three of the area's existing statements false, with counterexamples checked in Lean, within hours and after the area had just been attacked the usual way.
- The largest finding is not about bookkeeping. The paper's conversion is untyped and the model is typed, and the proof has no notion of a value being well typed inside: `Eq(A, a, b)` being a proposition says nothing about `a` and `b`. Conversion's rules preserve meaning only on well-typed values. A declarative system has this by construction (every subterm has a derivation); here it has to come from somewhere. Candidate under assessment: make the model's meanings strict (a type former means an error unless its parts are well typed, as closures and applications already do), so that "has a meaning" is "well typed inside".
- Against this section's claim: for the two rules that compare functions, the machine's bookkeeping is moved into the rule's premise, not removed, as long as evaluation itself is not also given as rules. And some growth of the state is inherent: the computed proposition can name an unknown made during the computation.
- One leak of exactly the kind this theme is about: a comparison's private copy leaves a record behind that can name an unknown of an empty type, after which no assignment makes the state good. Root fix being probed: a comparison returns a boolean, so it should restore the state it started from entirely; the statement "a conversion leaves the state unchanged", written first and withdrawn as false, would then be true by construction.

## Theme 2. One evaluator, written three times

### The pattern

A function body is run by the checker in two ways: generically, with unknowns for its parameters, and as an instance, when a call's arguments are known. The model's reference run is a third evaluator. Much of the machine's code exists in two forms for the two ways, with different precision at a few points, and nothing makes the forms agree except care.

Most of the week's checker changes did nothing but make two of the checker's own paths agree:

- When a borrow ends was discovered afresh by each run, the generic run over-approximating and an instance being precise. Three accepted functions failed when called. Fixed by making borrow ends a decision every run shares.
- A stuck match touched its captures at a different point from an instance's match.
- A field read ran as a one-arm match whose entry read the whole value, where the model read the field directly, so the two disagreed on which borrows were live.
- An `Id` observation could end a borrow over moved content where nothing else could.
- A call that ran returned its argument's borrow label where a stuck call returned a fresh one.

And between the checker and the model's third copy: sixteen differences found in the first comparison, and still this week the model typed a written value differently from the checker and read a field step the checker never reads.

### The change

One evaluator in which a known constructor is the special case of an unknown value, so that the instance run is the generic run with nothing unknown, by construction. The property the fixes above each restore by hand, that an accepted generic run stands for every instance, is then one theorem about that evaluator (more information never changes what a step does, only how far it gets), proved once.

Under theme 1 most of this is free: both runs become readings of one explicit term, and the points where they used to choose differently are written in the term. Without theme 1 it is a refactor of `Machine.lean` that changes no verdict, sizeable, and worth doing before the leaf proofs and not after, since those proofs are about the code it would rewrite.

## Theme 3. Classifications re-derived by parallel readers

### The pattern

Whether a type is a proposition, whether it is a copy, what sort it has, what class a function type has: the checker answers each from syntax and declared types, by a reader in `Decide.lean` that is deliberately unable to run code. That design removed a whole class of old proofs of `False` (decisions read from normal forms) and should stay. But there are several readers, each answering a nearby question, and they can disagree with each other and with the types the machine actually computes:

- The reader for a function type's sort was wrong (the function-sort bug, found while the decisions were being packaged for the model, and fixed before this week).
- The copy reader had no case for a function into proofs while the erasure reader had one, so a value was a proof to one and a resource to the other. Fixed by making the copy reader call the erasure reader.
- A binding carried a "this is a proof" flag set one way, and its declared type read the other way; a recursive lemma with a non-tail match was rejected with an internal error. Fixed by reading the declared type in both places.
- A reader looked up an unknown's type, which a later refinement can rewrite. Fixed by freezing the reading at creation.
- The proof now owes "the checker's reading of a type's sort is sound for the model", and carries a layer aligning every decision with the model and extending it after each step.
- The model's drop at the join asked "does the model read a proof at this place?" where the checker asks whether its own stored value is a proof. The two questions agree only if the model's types and the checker's readings agree, so a structural step (write "moved" at a place) came to depend on sort soundness, on reads respecting types, on dependent values being whole, and on stuck calls stored as types being well typed. The first slice spent a day on those before the question was asked whether the step should read the model's value at all. Answer (2026-11-20): it should decide by the shared copy decision alone.

### The change

Answer each such question once, at the point a type or a binder is formed, by the one reader, and store the answer with the thing it classifies. The model follows the same rule: where the checker acts on a classification, the model acts on the same stored classification, never on a second test of its own made on meanings. Every later consumer reads the stored answer and no second reader exists. This is how Lean has it: a type's sort is part of its typing, not a separate inspection. The last three fixes above are each a step this way. Finishing it means listing every classification the checker makes, checking each has exactly one place it is computed, and stating once that the stored answer agrees with the model, which is where the alignment layer shrinks to a lemma per kind of type.

Under theme 1 these are annotations on the core term, checked by the rules.

## Theme 4. Statements are found false by proving them

### The pattern

About twenty statements written by the effort's own leads were false, and most were found only when someone tried to prove or assemble them, sometimes days after they were written and after other statements had been built on them. One judgement made by reading alone ("this gap at the join is harmless") was where a real checker fault was then found.

What found faults early and cheaply was never reading. It was running something:

- Testing a candidate clause of the invariant on every recorded checker state of the suite (about 71,500 states). On its first use this refuted three clauses that had been read off the checker; since then it has gated every new clause, found a borrow held twice, and found the copy omission of theme 3.
- Checking the model's own run of a small accepted program in Lean's kernel beside the checker's verdict. This is how the model's gaps on computed function types and on recursive data were found, and how the substitution lemma for unknowns was shown false at the smallest possible text before any prover was given it.

But the tests on recorded states cover only the clauses that talk about syntax. The clauses about meanings (the assignment is typed, values are members of their types, the globals mean members, the decisions agree with the model) are neither proved nor tested, and the simulation relation itself is tested only on hand-picked programs.

### The change

Make as much as possible of the relation and of each step statement executable, and run it on every recorded step of the suite before anyone proves it. For a closed program the reference run computes, so for each recorded pair of checker states a harness can run the model's step and compare what is computable: shapes, which places hold borrows and where they are lent, first-order data, records. Meanings that are sets or functions cannot be compared in general; their computable shadows (a type's code, a function applied to the arguments that occur) can. The proof's lead has been asked what a first version would cost and what it cannot reach.

The rule this hardens, already in force: no fact about the checker becomes a clause until it has been tested on recorded states, and no statement counts as likely true because it was read carefully.

## A fifth candidate, weighed and not taken

A value whose later field's type mentions an earlier field, with the earlier field moved or lent, is where one of the old proofs of `False` lived. It is the riskiest remaining row of the work table, and it is the source of the model's most intricate parts (partial membership, values that are "open", reads typed at a field that has changed). Rust has no dependent types and Lean has no moves, so neither sets a bar here. Forbidding a move or a mutable loan of a field that another field's type mentions would remove the area. It was weighed with the user on 2026-11-19 and the precision was kept, because accessors that return a borrow into data an invariant mentions are ordinary code. It is reopened only if that row fails.

## How the themes relate

Themes 2 and 3 are largely consequences of theme 1: with an explicit core, the two runs of the checker read the same choices from the term, and classifications are annotations. Theme 4 is independent of the others and pays under any architecture. So the order of work is: theme 4's harness as soon as a place is free, since it protects whatever is proved next; the trial of theme 1 before provers are spread over the leaves; themes 2 and 3 decided by the trial's result, with theme 3 continuing piecemeal meanwhile.
