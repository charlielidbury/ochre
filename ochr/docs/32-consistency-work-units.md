# 32. The consistency proof as work units: done and to do

Written 2026-11-19; rows and estimates last revised 2026-11-20; the two status paragraphs under "To do" 2026-11-21. This file is the map and the list of design changes awaiting acknowledgement, not a log: what happened and why is in docs/31 (the proof), `ochr/core/DECISIONS.md` (the checker), docs/18 (the plan) and the commit messages. A map of the whole consistency effort (Target A of docs/18), one row per unit of work of roughly one agent's size. The plan itself is docs/18; the detailed record of the Lean development is docs/31 on the `spine` branch.

The numbers are estimates by the orchestrating session, not measurements.

- **P(failure)** is the chance the unit cannot be finished on the current plan: it needs a language feature redesigned, or a different proof architecture. Two outcomes count as success, because the work continues as planned after them. One is a tweaked statement: a lemma restated, a hypothesis added or a model definition repaired, the claim staying true in spirit. The other is a local checker fix: one rule tightened so that a class of wrongly accepted programs is rejected, as when a stuck block's arm was forbidden to return a borrow of a place the block takes by move.
- **Time** is the unit's share of all the effort the consistency proof needs. The column sums to 100% over both tables: about 31% is in finished rows and 69% in unfinished ones (re-estimated 2026-11-21: the whole grew by about a fifth since 2026-11-20, mostly in rows 1 and 13). Counting the work already done inside unfinished rows, about half of the whole is done.
- **The set of rows is fixed.** When a piece of work turns out bigger than estimated, or needs a repair or a fix nobody planned, that work is folded into the row it was done in service of, and the row's time and risk are re-estimated. No row is added for it.

## Done (31%)

| Work unit | What it contains | P(failure) | Time |
|---|---|---|---|
| Route and paper tests (`model-slice`, `model-slice-lean`, and the work behind docs/23, 25, 26 and 27) | Chose the meaning-preservation route. Showed the set model exists on a slice. Showed each old proof of `False` is a failed step. Audited every checker decision. Worked a higher-order slice. | done | 4% |
| Checker fixes (`etaboom-fix`, `bot-conv-fix`, `pisort-fix`, the join-drop change, and three later fixes) | Fixed accepted programs that proved `False` or went wrong, so that the theorem is true of the checker. | done | 5% |
| `spine` (first lead) | Lean definitions of a state's meaning and the reference run. Skeleton of 73 step statements and the final assembly, all unproved. | done; many statements later found false | 5% |
| `data-generic` | The model of user-defined data types, for any declaration. | done | 2% |
| `mono-lemmas` | Monotonicity lemmas for the reference run. | done | 1% |
| `prog-decisions` | The meaning of a whole program, and the checker's syntactic decisions packaged for the model. Found the function-sort bug. | done | 2% |
| `m2-proofs` | The four core lemmas: substitution and congruence, for values and for runs. No `sorry`. | done | 3% |
| `prover-borrow` | Pilot prover on the borrow steps. It tested the statement form, not the proofs. | done as a pilot; proofs not closed | 1% |
| `spine2` | Compared the reference run with the checker case by case: 16 differences, 11 fixed. Refuted the old statement form and introduced the simulation form. | done | 4% |
| `spine3`: prerequisites and riskiest steps, attacked | The two lemmas the statement migration waited on, then attacks on the two steps judged riskiest, the drop at the join and `Id`. An attack here means reading the statement against the checker from a related state and checking counterexamples in Lean; it is NOT a proof, and both steps are still `sorry`. Found and fixed: five faults of the simulation relation (it did not compare function shapes; it asked for a renaming of labels that cannot exist after a private copy; it compared states by an order where it needed equality; and two more), six faults of the model (among them: a partly moved value was a member of no type; reading one field ended a borrow of another; `Id` compared re-pointed borrows at untyped written values), and statement faults (the `Id` and `Eq` statements were satisfied by any wrong witness). Well-formedness gained a clause: no stored type or record holds a loan. One judgement made by reading was wrong: the gap at the join that was called harmless is where the checker fault of row 1 below was then found. | done; no checker change | 4% |

Not counted, because they are off the consistency path: `id-audit` and `subst-survey` (the dropped `Id` target), `runtime-j` (type safety), `paper-claims` and `docs18-sync` (document upkeep).

## To do (69%)

No step lemma of the simulation is proved end to end yet (2026-11-21). What is proved is the half of the theorem that concerns the model alone: from a good reference state a successful strict run returns a member of its type and leaves a good state, with no gap beneath it and applied to concrete runs. The simulation's statements are being re-made in the form that half needs (a step concludes that the strict run succeeds), proved first on a narrow column before the rest are restated.

**What can depend on what.** Nothing depends on a proof: once a statement is fixed, other work assumes it. Work depends only on definitions and statements. So the two rows that change definitions and statements (1 and 2) come first and everything else builds on them, and no arrow in the diagram leaves a prover row except into the assembly. Among the prover rows the order is a choice, not a dependency: the highest P(failure) for the least time first, so that risk comes forward. Matches and arms leads because it holds the first proof of any step, which is the first real test of the statement form.

| # | Work unit | What it contains | P(failure) | Time |
|---|---|---|---|---|
| 1 | Reference-run redesigns (running) | Making the model's reference run and the checker agree. Folded in, because it is the largest disagreement there was: the checker's borrow-ends redesign. Each run used to discover afresh when a borrow ends, the generic run over-approximating and an instance being precise, which gave three checker faults found on 2026-11-19 (accepted functions whose closed calls fail: `EJ`, `EI`, `G1`, in `ochr/core/probes/static-ends/`) and forced the model to carry a set of early-ended borrows. Now when a borrow ends is a decision every run takes the same way, as Rust does: a call that returns a borrow lends every place it borrowed, and a non-tail match on a known constructor treats outer places as the stuck match would (decision D90, on main since 2026-11-19 at 46dd2d9a; one existing verdict changed, which Rust also rejects). A stuck match now also touches its captures before its arms are checked (D91, on main at 9c78a376), so the generic run and an instance have the same borrows live at every point. The Lean model is rebuilt on the new checker (`spine5`): the reference run ends borrows from a table of lent places and never from meanings. Decided and built on 2026-11-20 (`spine` ffc4458e; built and axiom-checked independently by the orchestrator): the model's data values are self-describing. A constructor value's meaning carries its declaration, its parameters, its constructor and its fields, so the reference finds its way inside a value by reading the value alone, as the checker does and as an element of Lean's set model does. Twice in one evening the old form (an opaque element of a set, decoded with a declaration or a type taken from elsewhere) made the model wrong on an accepted program: two declarations with the same set, and a field whose type's index had been moved. With it a call's result now carries its data type; its function shape is still lost. The reference run's tail-position flag, match entry and capture access are built too (`spine` cf732702), with the checker's decisions made part of the context every step carries. One disagreement was left on purpose: the checker runs a field read as a one-arm match whose entry reads the whole value, where the model reads the field directly. That was removed in the checker (D93, below), not copied into the model; the model is being aligned with it. Built since (`spine` 060a8335, docs/31 D59–D61): types mean codes, as in Lean's own metatheory, so a call's result, a function type computed by a call (`f : Fn(Nat)`, the predicate idiom) and a field keep their structure, and a proof read at a place has its place's type; the model's own run gives the checker's answer on the accepted programs that showed these gaps, and the four core lemmas are re-proved on codes. Found on the way and fixed: every recursive closure meant `err` (D60). A data type's code now names its declaration, parameters and carrier, and fields are read through the data model, so recursive and nested inductives have meanings (`spine` bfc0ad7f, D61; kernel-checked runs on `List` and `Rose` beside the checker's verdicts); the existence of a data model for every accepted program now also owes a reading coherent with it. Still to do here: the comparison at other futures; and restricting the claim about untyped runs. | 3% | 15% |
| 2 | Statement migration | The form every step statement takes. The simulation relation is re-made on the redesign, with no set of early-ended borrows and no witness clause: the same borrows held in the same positions, lent at the same places, readings equal. Proving the first composition changed the form in four ways (a run may start from any log; a step may conclude under an extended context of unknowns; the drop's grain is a hypothesis; scope is preserved along a list). Still to do: the remaining step statements moved onto it: reads, borrows, assignments, access, drops, calls, `J`, closing off and the tail forms. The eval forms, matches, observation and `Eq` were migrated to the earlier relation and are re-stated. | 3% | 5% |
| 3 | Provers: matches and arms | The drop at the join, splitting on an unknown, and leaving an arm. The drop at the join was the first proof attempted of any step; the attempt on the old checker found the fault that led to the redesign in row 1. On the redesigned checker the drop of a list of places is proved from the drop of one place, and that one is proved apart from named obligations: three typing facts (a non-copy data place never reads as a proof), that an access loses no unknown, that the copy decision leaves the state unchanged, and the run context after each step. Proving it changed the checker twice more (the join rejects an arm that moves a place its type does not have; one-constructor matches refine in place) and the model several times. Still to do: those obligations, then splitting on an unknown and leaving an arm. | 4% | 6% |
| 4 | Provers: dependent values | Give a partly opened dependent value a meaning in the reference run, which it lacks today, so the step can be stated. Then prove or refute that membership is restored when a value whose type depends on its own fields is made whole again, under every future of the parts still lent. One of the old proofs of `False` lived here. | 5% | 6% |
| 5 | Provers: `Id` | Prove the corrected statements: `Id` observes every place either side can write, and its computing to a conjunction over those places keeps the meaning. | 4% | 4% |
| 6 | Provers: well-formedness | The borrow discipline is preserved by every step, including the clause that no stored type or record holds a loan. | 4% | 4% |
| 7 | Universes | Deciding which statement Lean can prove over all programs. The bounded-levels statement is what the Lean development already builds; the open part is whether a uniform statement is provable (about 40% that it is not, which is a tweak, not a failure). | 1% | 1% |
| 8 | Prover tooling | A shared library about positions in a state, and the standard prover brief. | under 1% | 1% |
| 9 | Provers: equality | Conversion, `Eq` and `J` computing, and rewriting. | 3% | 4% |
| 10 | Provers: calls and stuck calls | Calls, closing a stuck call into a sealed program, re-running one, and the label-renaming lemma. | 4% | 7% |
| 11 | Provers: types and decisions | The model reads types and syntactic decisions the same way as the checker (18 statements). | 2% | 4% |
| 12 | Provers: simple steps | Borrow primitives, substitution, plain evaluation, tail forms. | 1% | 3% |
| 13 | Assembly | The top-level theorems, closing the induction, and the data model for a whole program. | 5% | 9% |

**Progress inside the to-do rows** (2026-11-21; a row moves to the done table only when it is finished). Row 1, reference-run redesigns: done in substance (the run is strict; the model's fundamental lemma is proved); left: what a call run in place and a closure body leave good, that a run in a frame neither depends on nor disturbs what lies below it, and the model's `Id` following the checker's. Row 2, statement migration: restarted on the new form; about a third. Row 3, matches and arms: the drop at the join is assembled and rests on about 25 open leaves; nothing closed. Row 4, dependent values: the model's side done (open values, writes at a field, the invalidation mirrored); the simulation's side not started. Row 5, `Id`: the checker corrected twice; the step's statement is false until the model follows. Row 6, well-formedness: tested on every recorded state at every call depth, three checker changes from it; not proved. Row 13, assembly: the existence of the data model was false as stated and is repaired; a first instance is being built. Rows 7 to 12: statements only.

## Reading the risk column

A unit fails only if it cannot be finished on the current plan. Restating a lemma, repairing a model definition and tightening one checker rule are all successes: the proof goes ahead as planned after each. Nearly every refutation so far has ended in one of the first two, and the accepted proofs of `False` found earlier ended in the third.

- **Chance at least one remaining unit needs a local checker fix** (a success): about 85%. Found so far: the three faults of 2026-11-19 with one root (when a borrow ends), answered by the redesign in row 1, which counts as a feature redesign; and since then sixteen local changes (the list at the end of this file), three of them closing accepted proofs of `False`.
- **Chance at least one remaining unit fails**, so that a feature is redesigned or part of the proof is re-planned: about 30%. The rows are not independent (a fault in the simulation relation would hit several at once), so this is less than the rows multiplied out.
- **Chance the route itself fails**, so that meaning preservation has to be abandoned: about 7%.
- **Riskiest rows:** dependent values, where one of the old `False` proofs lived; then matches and arms, because it holds the first step proof: no step has been proved yet, and an earlier pilot under the old statement form closed nothing.

## Is it converging

Asked by the user on 2026-11-20: the effort keeps finding problems and no row of the table closes. This section keeps the evidence in one place so the question is answered by counts, not by feel. Updated at each half-day.

| Period | Checker changes landed | Of those, changing a verdict | Model definitions rebuilt | Simulation relation restated | Steps proved end to end | Areas attacked by proof |
|---|---|---|---|---|---|---|
| 19 Nov 16:30 to 20 Nov 04:00 | 3 (D90, D91, D92) | 1 (D90: three accepted functions that failed when run) | 2 (static lending; self-describing data values) | 2 | 0 | 1 (the join) |
| 20 Nov 04:00 to 16:30 | 6 (D93 to D98) | 3 (D93: two bugs and Rust's disjoint fields; D94: an ill-typed dead arm; D98: nine probe rows) | 3 (coded types; data codes; reads at recorded values) | 2 | 0 | 2 (the join, calls) |
| 20 Nov 16:30 to 21 Nov 11:00 | 16 (D99 to D114) | 8, three of them closing accepted proofs of `False` (D107 positivity, D110 and D112 writes to dependent fields); the others: a recursive lemma wrongly rejected (D100), an arm that moves through a non-borrow (D101), one inferred parameter (D105), `Id` hiding a write (D113), `Id` theorems disagreeing with their instances (D114) | 6 (the strict run; reads typed from the value; open values; records as paths; recursion by weakened stages; typed futures at whole members with strict ends) | 2, of the statements' form, not of the relation (the decision table fixed for a run; a step concludes that the strict run succeeds) | 0 | every area (the breadth pass); the half about the model alone proved |

Per area, since the breadth-first pass began (2026-11-20, evening). "Statements false" counts statements found false or empty by the attack.

| Area attacked | Checker faults | Model definitions changed | Relation changed | Statements false | Note |
|---|---|---|---|---|---|
| Calls | 1 (a returned borrow kept its argument's label; fixed as D99, no verdict change) | 1 | 0 | 4 | found by writing the proofs that glue the pieces |
| The data model | 1, the most serious of the effort: an accepted closed proof of `False` through a positivity hole (main's D107), found when the existence of a model for every accepted declaration was first attacked | 2 (recursion through nested types; large type parameters) and a redesign, ported on 2026-11-20 (a data value means its own tree; the whole library builds on it, rebuilt and axiom-checked independently; a dropped value is now below the original and a partly moved value is a member in the form first stated, both of which the old layer got the other way; the statement that the type `False` has no member is now proved). The port found one disagreement with the checker: the checker solves a constructor's value parameter from the type of a field (`MkW(t)` with `t : Tag(3)` gives `Wrap(3)`), which the model cannot mirror because it does not treat `Tag` as injective. No program in the suite does this; three constructed ones do. Decided, then revised the same evening: the model is extended to follow the checker here, and the checker stops inferring only function parameters (see the list of design changes) | 0 | 2 (the existence statement is satisfied by a model that ignores the program) | found before anything was built |
| The top-level chain | 0 | 0 | 0 | 2 | the chain closed for a constant and stopped at a function: the context assumed, of the definition being checked, what was to be proved of it. The plan's outer induction on the decreasing argument was missing from the Lean statements; it changes the context every step assumes, not the relation. Built since (2026-11-20, late evening): the context names the definition being checked and assumes of it only its good behaviour on smaller arguments; the chain now closes for a recursive function too, every gap a named statement, and a real recursive definition goes through the induction in Lean's kernel. Building it found no statement false, but see "The largest gap found so far" below: one of the named statements it rests on, the return check's, was later shown false. The data layer then found two of the statements it was asked to supply false as written, with kernel-checked counterexamples before any proof was tried. The serious one: the function's meaning while it is being checked (good only on smaller arguments) is not an element of its function type unless every result type is already known to be inhabited, which is what the induction is proving. Direction set and confirmed against the model's codes the same evening: give that partial meaning a weakened type whose results above the bound are trivially inhabited (the unit type; for a returned borrow, a borrow of unit), so it is an honest element of a function type and is built by the ordinary construction, with no appeal to anything being inhabited. The closure lemmas are proved in the forms that hold; the recursion argument's statements are to be restated on them by the lead |
| `Id` | 0 | 0 | 0 | 1 (the observation's statement said nothing about the state a side leaves) | the step follows from four named pieces; observations checked in Lean on a write through a borrow, with rejected controls |
| Equality and `J` | 0 | 0 | 0 | 3 (a conversion was said to leave the state unchanged, but comparing two functions creates unknowns that stay; the steps read the wrong tail flag, so a body's `let` was compared out of tail position; a type's evaluation started from the wrong state) and 2 incomplete | both steps follow from their named pieces; checked in Lean on accepted and rejected programs and on the reference's own runs. The trial of docs/35 then went through the same area a second way and found three more of its statements false, each with a counterexample checked in Lean: conversion's soundness (the checker's conversion is untyped and the statement assumed nothing about the insides of the values compared); the computation of `Eq` (no hypothesis on its sides); and the claim that after a comparison of function types some assignment still makes the state good (a record left behind by the comparison's private copy can name an unknown of an empty type) |
| Splits and worlds | 0 | 0 | 0 | 2 of the lead's (a substitution was said to leave the state unchanged, but re-running a stuck program keeps the unknowns it makes; leaving a world concluded nothing about the context) and 9 of the slice's unproved obligations, all from one cause: a step that creates unknowns must conclude under an extended context | the statement that refining an unknown keeps every meaning is in final form and was checked first on the checker's own states: a stuck program re-run after a refinement, a refinement of an unknown that a record or a stored type mentions, and a refinement in one arm followed by the join |
| The well-formedness table, and the substitution lemma for unknowns | 0 | 0 made, 1 proposed (the reference run types a value written in a program's text less precisely than the checker does; to be aligned at the end of the data layer's port) | 0 | 1 (the run-level substitution lemma for unknowns is false as the run stands, shown by a kernel-checked counterexample at the smallest text) | every clause of the invariant now has a row saying which steps make it true and which must keep it. Proofs that a clause is kept exist only for three kinds of write; most borrow-discipline clauses are tested on every recorded state and not proved; the clauses about meanings are neither. One small new clause (an unknown read as a sort has a sort as its type; true on all 76,568 recorded states) makes "the checker's reading of a type's sort is sound" a lemma instead of an assumption |
| The first slice (the easy half of the drop, by proving) | 1 (a function into proofs was read as not a copy although its values are proofs) and an internal error that rejected a recursive lemma with a non-tail match; both fixed as D100, nothing accepted became rejected | 0 | 0 | 4 (the context after a read cannot answer for unknowns the read created; a typing fact was tested but never made part of the invariant; the two leaves about a data place never reading as a proof were false at a function's own binding, by the checker fault) | the first two by the prover's first pass; the checker fault by sweeping the candidate clause on every recorded state before assuming it |

Reading on 2026-11-21, late morning: the model has stopped moving where it is proved (its fundamental lemma has no gap beneath it and is applied to concrete runs), and the checker's latest faults are of a milder kind (an internal error on a legal program; invariants broken with no wrong program behind them). The simulation has not started to converge: no step is closed, and its statements are still being found false at about the earlier rate, now before proofs are built on them. The first evidence either way is the narrow column being proved in the new form.

Reading on 2026-11-20, late evening: the last five areas attacked by the lead (the top-level chain, `Id`, equality and `J`, splits and worlds, the well-formedness table) forced no change to the relation and one small proposed change to the model; their faults were all in statements and were fixed in the same pass. The pass has now covered every area that does not wait on the data layer's port (closures and recursion, and dependent values, do). By the stop rule's first test the architecture stands; its second test, a step closed end to end within a week, is still open. Qualification added later the same evening: the pass tested the simulation half of the statements. The membership half had a gap the pass did not see (below, "The largest gap found so far"), because no area's attack tried to assemble a step that stores an evaluated value. The one checker fault since came from the slice, by testing a clause on recorded states before assuming it.

What the counts say (written before the breadth pass). The checker changes are getting less serious: the first fixed real faults; most since change no verdict and only make the checker's own paths agree. The model and the relation are not settling yet: each new area attacked by proof has forced a change to them. No step is closed. Six areas have not been attacked at all (dependent values, `Id`, equality and `J`, splits and worlds, closures and recursion, well-formedness), and the pattern so far is that an area's first real attack finds its faults.

What changes because of it. (1) Breadth before depth: after the call steps are stated and checked on concrete runs, every remaining area gets a bounded attack of the kind that has worked (its statements in final form, concrete runs checked in Lean beside the checker's verdicts, any needed fact swept on recorded states; no reading-only judgements), before more leaf lemmas are proved. That brings the remaining redesigns forward and shows whether the stream of faults is drying up. (2) A stop rule: if a full pass over the remaining areas still forces a change to the relation or a model rebuild per area, or if no step is closed end to end within a week of that pass, the architecture is re-examined (first candidate: a declarative rule system between the checker and the model, docs/33 item 2) instead of continuing. The themes behind the problems found so far, and a bounded trial of that candidate on one area which the user agreed to on 2026-11-20 whatever the stop rule says, are in docs/35.

## Design changes awaiting acknowledgement

Changes to the language or the checker made in service of the proof. Each stays here until the user has acknowledged it; none waits on that.

- **A stuck match touches its captures before its arms are checked** (D91; on main since 2026-11-19 at 9c78a376). It removes the last point at which the generic run and an instance could have different borrows live. No existing verdict changed; three probe programs that were rejected are now accepted, as Rust accepts them (an `Id` inside a match arm reading a place a live borrow points to).
- **A private copy that evaluates a call's parameter or result types takes a borrow argument instead of binding a second copy** (D92; on main since 2026-11-20 at ca81b410). Found by the invariant sweep: one borrow was held twice inside such copies. Only discarded copies differ; no verdict or message changed.
- **One-constructor matches refine in place instead of closing off, with no entry and no join** (D93; on main since 2026-11-20 at ca91d72b). A field read, a destructuring `let` and a one-arm match run directly on every path. It restores Rust's precision for disjoint fields of a pair, fixes two checker faults (`clone(x.0)` counted as a move; an internal error when a stuck match borrows a field of a captured place), and removes a disagreement between the checker and the model. Three rejected dependent-field programs became accepted (a borrow of an index field through which nothing is written, which Rust accepts; a broken local that is dropped; a proposition false on every path, whose proof is still rejected). Eleven rejections keep their verdict with a different reason. An asserted block of 25 attempts to carry a broken dependent value past a directly run arm are all rejected.

- **The join rejects an arm that moves a place its type does not have** (D94; on main since 2026-11-20 at 8035f7ed). When the join could not make a place exist, the checker dropped the longest existing prefix whole. Now it drops the place if it exists, does nothing if the prefix is already moved or a proof, and otherwise rejects the definition. No existing verdict changed; eleven well-typed programs written to reach the rejection are all accepted; only an ill-typed place in an arm that is never run is rejected.

- **The decision procedures write no cache** (D95; on main since 2026-11-20 at fc762af7). Two caches that the checker's syntactic decisions wrote into its state are removed; the decisions recompute. No verdict, message or location changed. Checking is 13 to 16 percent slower (the examples build goes from about 161 s to about 187 s). A pure way to get the time back is recorded and not taken.
- **Each unknown's declared reading is fixed when the unknown is created** (D96; on main since 2026-11-20 at 72fae0a9). The checker's syntactic decisions used to look up an unknown's type, which a later refinement can rewrite. They now read a write-once table filled when the unknown is made, and the decision code no longer reads the unknowns' types at all. No verdict, message or location changed; 31 adversarial programs (a type parameter or a stuck type refined to a proposition, a sort or a function type) take the same verdicts before and after.
- **A stuck program whose text still holds a borrow's hole is never run** (D97; on main since 2026-11-20 at 2222d517). It stays as it is until its last hole is filled, and runs then. Nothing can observe a lent place's content until the borrow ends. No verdict, message or location changed; the build is about 1 percent faster. It removes the hardest case from the proof of calls: a nested run that writes a hole whose borrow only the outer state holds.
- **A borrow never ends over moved content, inside an `Id` observation as anywhere** (D98; on main since 2026-11-20). The checker had an unwritten exception letting an `Id`'s observation end a borrow whose content a side had moved out. It is removed, which is what RULES and the paper already said. Nine rows go from accepted to rejected, all of one shape (both sides move out through a borrow and never put it back, as in `Id(Unit, (let a = *y; ()), (let b = *y; ()))`); the programmer clones or refills instead. No case study or book example relied on it; Rust rejects each such side.

- **A call's returned borrow is always a fresh one** (D99; on main since 2026-11-20 at 874584e1). When a function returned its own borrow parameter and the call ran, the result kept the argument's label, where a stuck call and the model's application of a function both give a fresh one. Now all three agree. No verdict, message or location changed; it is a renaming of labels.

- **Every proposition is a copy, and a proof function's own binding is read as a proof** (D100; on main since 2026-11-20 at f51c97ad). Two rules. (1) The copy test had no case for a function type whose result is a proposition, so a place holding a proof function read as a resource although its values are proofs; found by testing a clause of the proof on every recorded checker state. On its own this changes no verdict (reading a proof never moved it). (2) A recursive lemma whose non-tail match calls itself in an arm was rejected with an internal error, because the lemma's binding of itself was classified one way before running and another way after. Now it is classified by its declared type both times. Two programs of that shape go from the internal rejection to accepted; nothing goes from accepted to rejected. A tempting simpler fix was tried and refused: it accepted a non-decreasing proof of `False` through a closure.

Also on main (in the order they were decided):
- **The join rejects an arm that moves through a dereference of something not declared a borrow** (D101; on main since 2026-11-20 at c4628e33). Measured at landing: of 2,311 rows, six change. Four are the new programs written to show the hole (accepted before, rejected now); two were already rejected and only change message, the check now being made from declared types before anything runs. Nothing that was accepted in the suite is rejected. A borrow chosen by a match (`let r = match b { Z => &x, S _ => &y }`) still reads as a borrow, so a dereference of it in an arm the run does not take is still accepted. An arm the run never takes is never checked, but its moves feed the join. With the `Nat` prelude, `def DP1 (h : Eq(Nat, Z, Z)) : Unit := (let k = Z; match k { Z => (), S m => (let a = *h; ()) })` is accepted today and will be rejected; the programmer does not dereference a proof. No program in the suite changes verdict; Rust rejects such an arm.
- **A side of `Id` may end a borrow it consumes, on every path** (D114; on main since 2026-11-21 at 1b17aa44; rebuilt by the orchestrator, 3,526 verdicts, and the example below run before and after). The check that a side of `Id` ends no borrow held outside it now decides by the set of bindings the side consumes, read from the side's text, so it decides alike on every path. With the `Nat` prelude:
  ```
  def Eat (r : &Nat) : Unit := ()
  def A1 (n : Nat) (x : &Nat) : Id(Unit, match n { Z => Eat(x), S _ => () }, match n { Z => Eat(x), S _ => () }) := refl
  def A1z : ⊤ := (let c = 0; A1(0, &c))
  -- rejected before ("a side of Id ends the borrow x, which a binding outside the Id holds"), accepted now
  def A1s : ⊤ := (let c = 0; A1(1, &c))
  ```
  Before, the theorem `A1` was accepted and its closed instance `A1s` rejected: in the arm that does not use `x` the join drops it in place, which the check took for ending a borrow held outside. It was fail-safe (no accepted program was wrong). Measured on 119 `Id` theorems, each checked generically and at every small instance: 53 had an instance disagreeing with the generic verdict before; after, none goes from accepted to rejected, 183 instance verdicts go from rejected to accepted, and 8 theorems still differ, all in the safe direction (the theorem rejected, an instance accepted), for a reason that is not about `Id`: a match whose one arm moves a borrow and whose other arm reads its lender ends the borrow at entry, before any arm runs. One of the 8 is asserted beside the same match outside `Id`. Known and left: where a re-pointed borrow points is still invisible at a one-value type such as `Unit`.
- **No borrow held by a value in flight is ended** (D106; on main since 2026-11-21 at 14aeb9cd). One check at the single place every access ends a borrow, measured at every call depth by the build; no accepted definition reaches it; three already-rejected programs change message.
- **`Id` observes what a re-pointed borrow points to** (D113; on main since 2026-11-21 at 75e79291; rebuilt by the orchestrator, 2,864 verdicts, and the example below run before and after). When a side of `Id` re-points a borrow binding, `Id` now also compares what that binding points to on each side, as it already does for a borrow a side returns. Before, a side could write through the borrow it had just re-pointed and the write went unobserved. With the `Nat` prelude:
  ```
  -- accepted before, rejected now: after the two sides, `y := &w; x` gives 0 and 5
  reject def Hide : Unit := (let x = 0; let w = 0; let y = &w; let h : Id(Unit, y := &x, (y := &x; *y := 5)) = refl; ())
  -- accepted before and now: the same sides without the hidden write, and with it on both
  def Honest : Unit := (let x = 0; let w = 0; let y = &w; let h : Id(Unit, y := &x, y := &x) = refl; ())
  def BothWrite : Unit := (let x = 0; let w = 0; let y = &w; let h : Id(Unit, (y := &x; *y := 5), (y := &x; *y := 5)) = refl; ())
  ```
  It was not a route to `False`; it makes `Id` say what it means. Eleven hiding programs of this class were accepted and are rejected now, each asserted beside its honest twin; two programs that re-point two bindings were wrongly rejected and are accepted. Every other verdict is unchanged; one message gains an equation.
- **A type may be nested only where that is sound, its own occurrences included** (D107; a soundness fix; on main since 2026-11-21 at 89765d9b). Accepted today, with only the built-in prelude, and a closed proof of `False`:
  ```
  def Neg (X : Type) (n : Nat) : Prop := (match n { Z => False, S _ => (Π(x : X). False) })
  inductive Q (A : Type) (n : Nat) := MkQ(z : Q(Q(A, n), 1), e : Eq(Nat, n, 0)) | Stop(f : Neg(A, n))
  def Delta (x : Q(Unit, 0)) : False := (
    match x {
      MkQ(z, e) => match z { MkQ(z2, e2) => e2, Stop(f) => f(x) },
      Stop(f) => f,
    }
  )
  def Boom : False := Delta(MkQ[Unit, 0](Stop[Q(Unit, 0), 1](Delta), refl))
  ```
  `Q(Unit, 0)` is exactly `Q(Unit, 0) → False`. After the fix `Q` is rejected: a type being declared may sit as an argument of an inductive type, itself included, only at a parameter that the inductive uses in data positions alone (never passed to a type function, never in a function's domain). Nested types whose model exists, such as `DD (A : Type) := DLeaf | DNode(x : DD(DD(A)))`, stay accepted.
- **An in-place write to a dependent field stores only data** (D110; a soundness fix; on main since 2026-11-21 at 9eea122f). Landed with every earlier verdict unchanged and no case study affected. The hunt before the fix found two more routes to `False` through the same unchecked write (by a borrow parameter, where the path's ending in an empty match skipped the re-check; and with no proof stored, through a loan left dangling by a borrow written inside a constructor value), and that this write was the only one in a typed run that stored a value without comparing types. A proof, a borrow, a type or a function may still be written into such a field when it has the field's type; it is then an ordinary checked write. With the `Nat` prelude, every declaration below is accepted today and `BoomF` is a closed proof of `False`:
  ```
  inductive Void : Type
  inductive One := O
  def Fin1 (n : Nat) : Type := match n { Z => Void, S(m) => One, }
  inductive V := MkV(n : Nat, x : Fin1(n))
  def Bad : Void := (let c = MkV(S(Z), O); match c { MkV(n, x) => (x := refl; n := Z; let z : Void = match x {}; z), })
  def AbsurdV (v : Void) : False := match v {}
  def BoomF : False := AbsurdV(Bad)
  ```
  After the fix `x := refl` is rejected: a proof, a borrow or a type cannot be written into a data field. Writing data there (`x := O`), then the index, then repairing the field, stays as it is.
- **A dependent field that is not a data type behaves like a proof field** (D112; on main since 2026-11-21 at 59e9bee7; rebuilt and the examples below re-checked independently). A dependent field whose type is a data type at every index (a vector's buffer) is unchanged. Any other dependent field (its type is a number, a unit, a function or a proposition at some index) is set to "moved" when its index is written or borrowed, and an assignment to it is checked at the current index. No case study changes; one test row added by the previous night's fix changes verdict; check time unchanged. Each pair below was accepted before; the first is now rejected, the second is the rewrite. With the `Nat` prelude:
  ```
  inductive Bit := B0 | B1
  def Payload (b : Bit) : Type := match b { B0 => Nat, B1 => Unit, }
  inductive Tagged := MkT(b : Bit, x : Payload(b))
  -- 1. reading the payload after changing the tag: take it out first
  reject def ReadAfter (p : &Tagged) : Nat := match *p { MkT(b, x) => match b { B0 => (b := B1; let old = x; x := (); old), B1 => 0, }, }
  def TakeFirst (p : &Tagged) : Nat := match *p { MkT(b, x) => match b { B0 => (let old = x; b := B1; x := (); old), B1 => 0, }, }
  -- 2. writing the payload before the tag: tag first
  reject def PayloadFirst (p : &Tagged) : Unit := match *p { MkT(b, x) => (x := (); b := B1), }
  def TagFirst (p : &Tagged) : Unit := match *p { MkT(b, x) => (b := B1; x := ()), }
  -- 3. using a borrow of the payload after the tag changed: use it first
  reject def UseAfter (p : &Tagged) : Unit := match *p { MkT(b, x) => match b { B0 => (let r = &x; b := B1; *r := 5; x := ()), B1 => (), }, }
  def UseBefore (p : &Tagged) : Unit := match *p { MkT(b, x) => match b { B0 => (let r = &x; *r := 5; b := B1; x := ()), B1 => (), }, }

  inductive Void : Type
  inductive One := O
  def Fin1 (n : Nat) : Type := match n { Z => Void, S(m) => One, }
  inductive V := MkV(n : Nat, x : Fin1(n))
  -- 4. parking a number in a field whose type is a data type at every index: leave it moved out
  reject def Park (v : &V) : Unit := match *v { MkV(n, x) => (let old = x; x := 5; x := old), }
  def NoPark (v : &V) : Unit := match *v { MkV(n, x) => (let old = x; x := old), }

  inductive PosN := MkPosN(n : Nat, h : Eq(Nat, n, 1))
  -- 5. reading a proof after a match one arm of which writes its index: read it before
  reject def ReadProofAfter (c0 : PosN) : Unit := (let c = c0; match c { MkPosN(n, h) => (match S(Z) { Z => (n := n; ()), S(m) => (), }; let h2 = h; ()), }; ())
  def ReadProofBefore (c0 : PosN) : Unit := (let c = c0; match c { MkPosN(n, h) => (let h2 = h; match S(Z) { Z => (n := n; ()), S(m) => (), }; ()), }; ())
  ```
  Found while landing: the check of such a field assigned while its index is lent is needed for soundness itself (a number would pass at `Nat` and the borrow could then move the index to where the field's type is empty).
- **Typing reads through the mark of a place lent to a call's returned borrow** (an amendment to D112; on main since 2026-11-21 at d1cd9941; rebuilt, 2,812 verdicts, and the example below re-checked independently before and after). A field lent to a borrow that a call returns holds a mark over its content. Paths and the repacking of a borrow's content already read through the mark; typing did not, which first gave the third proof of `False` (closed by D112) and then, after D112, wrongly rejected ordinary reads. Now a mark has the type of the content it marks. It only repairs: every earlier verdict is unchanged. With the `Nat` prelude:
  ```
  def KeepN (r : &Nat) : &Nat := r
  def Payload (b : Nat) : Type := match b { Z => Nat, S(m) => Unit, }
  inductive L := MkL(b : Nat, p : Payload(b))
  -- accepted throughout
  def ReadPlain : Nat := (let c = MkL(Z, 5); match c { MkL(b, p) => (let r = &p; let k : Nat = p; k), })
  -- the same through an identity call: an internal error after D112, accepted now, and it computes 5
  def ReadKept : Nat := (let c = MkL(Z, 5); match c { MkL(b, p) => (let r = KeepN(&p); let k : Nat = p; k), })
  def ReadKeptRuns : Eq(Nat, ReadKept, 5) := refl

  inductive Void : Type
  inductive One := O
  def Fin1 (n : Nat) : Type := match n { Z => Void, S(m) => One, }
  inductive V := MkV(n : Nat, x : Fin1(n))
  def Keep (r : &One) : &One := r
  -- the route to `False`: still rejected, now with an ordinary type error ("the ascribed term has type One, expected Void")
  reject def A2 : Void := (let c = MkV(S(Z), O); match c { MkV(n, x) => (let r = Keep(&x); n := Z; let k : Void = x; k), })
  ```
  With it came a census of everything a typed run can leave in a dependent field (a constructor value, a number, an unknown, a stuck program, a loan, a mark over any of these, a proof marker, a moved marker), each with the reason its type can be read; the remaining "type cannot be read" error is an assertion with that census behind it.
- **A borrow is never left without its end** (D111; on main since 2026-11-21 at ff9b0a74; rebuilt by the orchestrator, 2,813 verdicts). Overwriting content that held a borrow below the top of a value ended nothing, and the lender kept a loan for ever. D110 removed the one known way to get there; this closes it at the root: where a value is overwritten, dropped or read, the checker rejects with an internal error if a borrow sits below the top of a value or a loan has lost its borrow. It changes no verdict, and the error never fires on the suite, the case studies or the probes; a census in the decision's entry gives one rejected program for each way a borrow could come to sit there. The one new row, with the `Nat` prelude: `inductive One := O`, `def Fin3 (n : Nat) : Type := match n { Z => Nat, S(m) => Nat, }`, `inductive V3 := MkV3(n : Nat, x : Fin3(n))` and `reject def DanglingRead : Nat := (let c = MkV3(Z, 0); match c { MkV3(n, x) => (let w = O; x := &w; x := 0; let v : One = w; match v { O => 0, }), })`, rejected at `x := &w` (a borrow is not a `Nat`).
- **Where the checker looks a stuck program up among its records, it compares exactly** (D108; on main since 2026-11-21 at 95edadc0). Landed with an instrumented build that would have rejected on any difference between the old and the new comparison at any lookup; it never fired, on the suite, the probes or the probe files. No verdict moved. Its equality on values ignores the type parameters a constructor value records and the names of binders; that is right inside conversion, where both sides have one type, and wrong as a lookup key, where two programs that mean different things could match. On all of the roughly 36,000 lookups of the suite the match was already exact, so no verdict should change.
- **A loop in the checker is bounded by the fuel** (D109; on main since 2026-11-21 at 35ab3cd0). Verdicts identical; the bound is never reached in the suite, the case studies or the probes. With it came a tool that walks everything reachable from the checker's entry point and lists what Lean's kernel cannot see into: after this change the only such constant of the checker's own is the one sanctioned exception. The checker's standards file now names `while` and `repeat` among the forbidden constructs. The loop that refines the places a stuck match captures was written as a `while`, which Lean builds on a partial function, against the checker's own standard that all its code is total. Nothing about a stuck match could be proved while it stood. Running out of fuel there becomes the usual "I don't know". A list of every other construct of that kind is being drawn up.
- **Nothing inspects a type's constructors while it is being declared** (part of D107). While a declaration is checked its entry has no constructors, and a match with no arms on a value of that type was accepted as vacuous, so a declaration could carry a field type that is ill-typed once the declaration is complete. No route to `False` was found through it; it is closed with the positivity fix.
- **The join never ends a borrow held by the match's own result** (to be D106; widened to the drop of a `let`'s binding and a frame's pop: no step that accesses places while a value is in flight ends a borrow that value holds). The join already rejects an arm that moves a place while the result borrows it. One path was not covered: when the place lies under a lent parent, the join's access of the parent ended the borrow silently. Thirteen programs written to exploit it are all rejected today, but in tail position only because an unrelated rule fires afterwards. The join's check is made uniform; expected effect, a different rejection message for two of those programs and no verdict changed, measured on the whole suite before landing.
- **Every value the checker holds in flight carries its type** (D104; on main since 2026-11-20 at 490c0a6a). The checker's rule is that every binding has a stored type; a value between being computed and being stored was the one exception, and the root of the largest gap in the proof. Each such value now has beside it the type the checker already had in hand (the type its evaluation returned, the call's result type for a function body's result, a block's declared argument types). The checker never reads it: every verdict, message and location is identical on all rows, and it costs under 1 percent of check time. Measured by a new permanent census of every push at every call depth: where a typed run used to hold about 13,000 values with no type, it now holds three, all bare proof tokens whose proposition was checked on a private copy. In the run of a known function's body, which computes no types, a borrow in flight still has none; the proof keeps its own record for those. This is state kept for the proof's sake.
- **A constructor's parameter is not inferred from its fields where it stands only at a position of a higher universe** (D105; on main since 2026-11-21 at 2a1c31c5). The last piece of the inference decision: `MkW(t)` with `t : Tag(3)` and a type through any depth of nesting keep being inferred, and the model follows them; a parameter that is a function into a universe, a type in `Type₁`, or a value of such a type must be written or come from the expected type, with a message naming the parameter. Three programs written to do it are rejected, each beside its accepted rewrite; no earlier verdict changes. Landed with it, a checker bug found on the way: a wrong index in the decision whether a constructor value records its type parameters, which left some values recording none inside a called function's run. No verdict was wrong, and fixing it made checking about 13 percent cheaper (it had been computing a type for nothing), which gives back what removing the decision caches cost.
- **The join's test "this place holds a proof: do nothing" is removed** (D102; on main since 2026-11-20 at 04edce76). Verdicts, messages and the test on recorded states identical before and after; an assertion that the removed test could still fire never did, checked again after typed temporaries landed. Since D100 it never fires at a place that is not a copy; removing it changes no verdict and no line of the test on recorded states.
- **A comparison keeps nothing but names** (D103; on main since 2026-11-21 at 4c6641f7; amended before landing). Landed measurements: verdicts, messages, locations and the test on recorded states identical; across the whole suite a comparison's private copy never once made a record or changed the recursion check's lists, so nothing was lost; the three stability proofs about comparisons are re-proved; check time within half a percent. The state that falsified the proof's invariant (a record naming an unknown of an empty type after comparing two function types) is now an asserted test. Comparing two values, function types or functions runs on a private copy, and the checker kept the records the copy made. One such record can name an unknown of an empty type, after which the proof's invariant cannot hold. A comparison returns only yes or no, so nothing it made can be needed: on exit the records made inside are dropped. The fresh names it used are NOT given back: a name is never reused within a definition's check, which the proof relies on (below). The first form of this change restored the state entirely; that would have rewound the name counters. No verdict of the suite changes, and across the suite the dropped records were always empty.
- **Inference of a constructor's parameters from its fields is kept, except for function parameters** (decision revised 2026-11-20, late evening). The checker solves a parameter the programmer left out from the types of the fields: a number, as in `let w = MkW(t)` with `t : Tag(3)` and `inductive Wrap (n : Nat) := MkW(t : Tag(n))`, or a type through nesting, as in `MkGrid(v)` with `v : List(List(Nat))`. The model could not follow either step. First decision: stop the checker inferring them. Withdrawn the same evening, because pinning the rule showed it would also have dropped inference through nesting, and Rust infers both. Now the model is extended to follow the checker (a type's meaning keeps its number-like parameters, and reads type parameters back at any depth), and the checker will stop inferring only what the model truly cannot follow: a parameter that is a function, and a type parameter that appears only at a position of a higher universe. No program in the suite is affected either way. Done so far: the model reads type parameters back at any depth (the nested example is checked in Lean's kernel). Done as well (2026-11-20, late evening): a type's meaning keeps its number-like parameters, so `MkW(t)` with `t : Tag(3)` runs in the model to a value of `Wrap(3)`, and `Tag(3)` and `Tag(4)` are different types there. What is left for the checker to stop inferring: a parameter that stands in the fields' types only at positions of a higher universe (a function into a universe among them).

Acknowledged: borrow ends become a decision every run shares (D90; proposed by the user and acknowledged 2026-11-19).

Decided and not yet on main:
- **No value the checker holds lives outside its state while anything runs** (to be D115). A call's arguments, a constructor's fields, an assignment's right-hand side, a new borrow during the invalidation of dependent fields, and an arm's result at a join were held in the checker's own variables while other code ran. They now stay in the state as typed temporaries. No verdict changes.
- **`clone` of a proof is that proof** (to be D116). With the `Nat` prelude, `def K7 (h : ⊤) : ⊤ := clone(h)` is rejected today with an internal error; after the fix it is accepted, and `def K3 (h : ⊤) : Nat := clone(h)` is rejected by the ordinary type rule, as `def K9 (h : ⊤) : Nat := h` is.
- **The frame in which a dependent field's type is computed binds what a loan stands for, not the loan** (to be D117). Today typing a value whose index is lent can end the index's borrow, which wrongly rejects a side of `Id` that only reads the value. No verdict in the suite changes; the example is added when it lands.

## Design questions to ask before each risky unit

The bar is "as good as Rust for borrowing, as good as Lean for proving". Where a unit is hard because the design is more precise than that, the design is questioned before the proof is attempted.

- **Borrow ends (row 1):** asked and answered: the redesign in row 1.
- **Matches and arms (row 3):** asked 2026-11-19, while the drop of one place was open. Part of that proof exists only because the checker has to find a place that does not exist yet (a field of an unknown pair, of a stuck value, or under a lent parent). Keeping values of one-constructor types expanded into their fields would make such places always exist, and is the parked change that also restores Rust's precision for disjoint fields. The proof lead's estimate: it would delete about a third of that one proof, and none of the lemmas that carry the risk (an access, an end, marking a part moved, the two ways of finding a place agreeing), which every other step needs anyway. Conclusion at the time: do not make the change for the proof's sake. Revised 2026-11-20: the change is being made after all, because four things now point at it (the disjoint-fields gap against Rust, two checker faults, and a disagreement between the checker and the model on which borrows are live after a field read), not because of the proof it would shorten.
- **How the model decodes a data value (row 1):** asked 2026-11-20, after two faults with one root. Options weighed: self-describing values; a type skeleton kept beside each position; Lean's coded types alone; and, for the partial-move case only, tightening the checker so the join's drop does the checks a move does. Conclusion: self-describing values, with types of data as codes naming the declaration and its parameters. It removes the root, mirrors the checker's own values and Lean's set-theoretic elements, and deletes an invariant clause and a restriction; Lean's coded types alone would not cover a value whose type's index has been moved, which Lean never has. The checker is not changed. Recorded as docs/31, D32, and compared against Lean in docs/33.
- **Dependent values (row 4):** asked 2026-11-19, with the user. The difficulty is a value whose later field's type depends on an earlier field that is lent or half-written. Conclusion, in two parts. (1) Inside a function body there is no problem to solve in the language: once such a value is open, the checker types the later field by what it holds, not by the earlier field, so its type does not follow the lent field. The model does not do this yet (it re-reads the earlier field through the borrow), and that is the fault to fix, in the model. (2) At a point where the value must be whole again (a return, a call), the checker does not require the loan ended: it checks the value with the lent part replaced by a fresh unknown of its type, so the invariant must hold whatever the borrow later writes. Requiring every loan ended there would be simpler, but it would reject accessors that return a borrow into data an invariant mentions (the examples' user-land vector, whose invariant says its first cells are full, returns a borrow into a cell's payload), and Rust has those. So the rule stays; it is also what closed the two proofs of `False` found here. The step to prove is then the natural one: a check that passes for a fresh unknown gives membership under every final content of the borrow.
- **`Id` (row 5):** its rules about when a borrow ends (a side may not end a borrow held outside it) exist because sides run on private copies. Once ends are a shared decision, check which of those rules are still needed.

## Dependencies

An arrow from X to Y means Y builds on definitions or statements that X produces. Green is done, yellow is running, orange means the step is proved from named pieces and the pieces are open, grey is to do. The percentages are the tables' (time, then P(failure)). No arrow leaves a prover row except into the assembly, because nothing depends on a proof; the order among prover rows is the table's.

```mermaid
flowchart TD
    classDef done fill:#c8e6c9,stroke:#2e7d32,color:#000
    classDef running fill:#fff59d,stroke:#f9a825,color:#000
    classDef stated fill:#ffe0b2,stroke:#ef6c00,color:#000
    classDef todo fill:#eeeeee,stroke:#757575,color:#000
    classDef goal fill:#bbdefb,stroke:#1565c0,color:#000

    tests["Route and paper tests<br/>5%"]:::done
    fixes["Checker fixes<br/>6%"]:::done
    spine["spine: definitions and<br/>statement skeleton<br/>6%"]:::done
    datagen["data-generic<br/>2%"]:::done
    mono["mono-lemmas<br/>1%"]:::done
    progdec["prog-decisions<br/>2%"]:::done
    m2["m2-proofs: four core lemmas<br/>4%"]:::done
    pborrow["prover-borrow: pilot<br/>1%"]:::done
    spine2["spine2: run audit and<br/>simulation form<br/>4%"]:::done

    spine3["spine3: prerequisites and<br/>riskiest steps, attacked<br/>5%"]:::done

    redesign["1. Reference-run redesigns<br/>(borrow-ends redesign folded in;<br/>data layer ported)<br/>12%, fail 6%"]:::running
    migrate["2. Statement migration<br/>(the breadth-first pass)<br/>4%, fail 3%"]:::running

    pMatch["3. Provers: matches and arms<br/>(the first slice)<br/>7%, fail 4%"]:::running
    dep["4. Provers: dependent values<br/>5%, fail 8%"]:::todo
    idn["5. Provers: Id<br/>4%, fail 4%"]:::stated
    wf["6. Provers: well-formedness<br/>4%, fail 4%"]:::todo
    universes["7. Universes<br/>1%, fail 1%"]:::todo
    tooling["8. Prover tooling<br/>1%, fail under 1%"]:::todo
    pEq["9. Provers: equality<br/>5%, fail 3%"]:::stated
    pCalls["10. Provers: calls and stuck calls<br/>8%, fail 4%"]:::stated
    pTypes["11. Provers: types and decisions<br/>5%, fail 2%"]:::todo
    pSimple["12. Provers: simple steps<br/>4%, fail 1%"]:::todo

    assembly["13. Assembly<br/>4%, fail 1%"]:::stated
    goal(["Consistency:<br/>no closed proof of False"]):::goal

    tests --> fixes
    tests --> spine
    fixes --> spine
    spine --> datagen
    spine --> mono
    spine --> progdec
    spine --> m2
    spine --> pborrow
    mono --> m2
    m2 --> spine2
    pborrow --> spine2
    progdec --> spine2

    spine2 --> spine3
    spine3 --> redesign
    spine3 --> migrate
    redesign --> migrate

    migrate --> pMatch
    migrate --> dep
    migrate --> idn
    migrate --> wf
    migrate --> pEq
    migrate --> pCalls
    migrate --> pTypes
    migrate --> pSimple
    progdec --> pTypes

    pMatch --> assembly
    dep --> assembly
    idn --> assembly
    wf --> assembly
    pEq --> assembly
    pCalls --> assembly
    pTypes --> assembly
    pSimple --> assembly
    tooling --> assembly
    datagen --> assembly
    progdec --> assembly
    universes --> assembly
    assembly --> goal
```
