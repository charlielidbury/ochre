# 32. The consistency proof as work units: done and to do

Written 2026-11-19; last updated the same day, after both checker changes landed on main (9c78a376). A map of the whole consistency effort (Target A of docs/18), one row per unit of work of roughly one agent's size. The plan itself is docs/18; the detailed record of the Lean development is docs/31 on the `spine` branch.

The numbers are estimates by the orchestrating session, not measurements.

- **P(failure)** is the chance the unit cannot be finished on the current plan: it needs a language feature redesigned, or a different proof architecture. Two outcomes count as success, because the work continues as planned after them. One is a tweaked statement: a lemma restated, a hypothesis added or a model definition repaired, the claim staying true in spirit. The other is a local checker fix: one rule tightened so that a class of wrongly accepted programs is rejected, as when a stuck block's arm was forbidden to return a borrow of a place the block takes by move.
- **Time** is the unit's share of all the effort the consistency proof needs. The column sums to 100% over both tables: about 36% is done and 64% remains.
- **The set of rows is fixed.** When a piece of work turns out bigger than estimated, or needs a repair or a fix nobody planned, that work is folded into the row it was done in service of, and the row's time and risk are re-estimated. No row is added for it.

## Done (36%)

| Work unit | What it contains | P(failure) | Time |
|---|---|---|---|
| Route and paper tests (`model-slice`, `model-slice-lean`, and the work behind docs/23, 25, 26 and 27) | Chose the meaning-preservation route. Showed the set model exists on a slice. Showed each old proof of `False` is a failed step. Audited every checker decision. Worked a higher-order slice. | done | 5% |
| Checker fixes (`etaboom-fix`, `bot-conv-fix`, `pisort-fix`, the join-drop change, and three later fixes) | Fixed accepted programs that proved `False` or went wrong, so that the theorem is true of the checker. | done | 6% |
| `spine` (first lead) | Lean definitions of a state's meaning and the reference run. Skeleton of 73 step statements and the final assembly, all unproved. | done; many statements later found false | 6% |
| `data-generic` | The model of user-defined data types, for any declaration. | done | 2% |
| `mono-lemmas` | Monotonicity lemmas for the reference run. | done | 1% |
| `prog-decisions` | The meaning of a whole program, and the checker's syntactic decisions packaged for the model. Found the function-sort bug. | done | 2% |
| `m2-proofs` | The four core lemmas: substitution and congruence, for values and for runs. No `sorry`. | done | 4% |
| `prover-borrow` | Pilot prover on the borrow steps. It tested the statement form, not the proofs. | done as a pilot; proofs not closed | 1% |
| `spine2` | Compared the reference run with the checker case by case: 16 differences, 11 fixed. Refuted the old statement form and introduced the simulation form. | done | 4% |
| `spine3`: prerequisites and riskiest steps, attacked | The two lemmas the statement migration waited on, then attacks on the two steps judged riskiest, the drop at the join and `Id`. An attack here means reading the statement against the checker from a related state and checking counterexamples in Lean; it is NOT a proof, and both steps are still `sorry`. Found and fixed: five faults of the simulation relation (it did not compare function shapes; it asked for a renaming of labels that cannot exist after a private copy; it compared states by an order where it needed equality; and two more), six faults of the model (among them: a partly moved value was a member of no type; reading one field ended a borrow of another; `Id` compared re-pointed borrows at untyped written values), and statement faults (the `Id` and `Eq` statements were satisfied by any wrong witness). Well-formedness gained a clause: no stored type or record holds a loan. One judgement made by reading was wrong: the gap at the join that was called harmless is where the checker fault of row 1 below was then found. | done; no checker change | 5% |

Not counted, because they are off the consistency path: `id-audit` and `subst-survey` (the dropped `Id` target), `runtime-j` (type safety), `paper-claims` and `docs18-sync` (document upkeep).

## To do (64%)

No step lemma is proved end to end yet, but the first one is close (2026-11-20, `spine` 0a71dd94): the drop at the join is proved from the drop of one place, and the drop of one place is proved apart from a short list of named obligations (three typing facts, two facts about the checker, and what the run context is after each step). That is the evidence that the statement form supports a proof. What else is done is definitions, the four core lemmas, and attacks that corrected the statements.

**What can depend on what.** Nothing depends on a proof: once a statement is fixed, other work assumes it. Work depends only on definitions and statements. So the two rows that change definitions and statements (1 and 2) come first and everything else builds on them, and no arrow in the diagram leaves a prover row except into the assembly. Among the prover rows the order is a choice, not a dependency: the highest P(failure) for the least time first, so that risk comes forward. Matches and arms leads because it holds the first proof of any step, which is the first real test of the statement form.

| # | Work unit | What it contains | P(failure) | Time |
|---|---|---|---|---|
| 1 | Reference-run redesigns (running) | Making the model's reference run and the checker agree. Folded in, because it is the largest disagreement there was: the checker's borrow-ends redesign. Each run used to discover afresh when a borrow ends, the generic run over-approximating and an instance being precise, which gave three checker faults found on 2026-11-19 (accepted functions whose closed calls fail: `EJ`, `EI`, `G1`, in `ochr/core/probes/static-ends/`) and forced the model to carry a set of early-ended borrows. Now when a borrow ends is a decision every run takes the same way, as Rust does: a call that returns a borrow lends every place it borrowed, and a non-tail match on a known constructor treats outer places as the stuck match would (decision D90, on main since 2026-11-19 at 46dd2d9a; one existing verdict changed, which Rust also rejects). A stuck match now also touches its captures before its arms are checked (D91, on main at 9c78a376), so the generic run and an instance have the same borrows live at every point. The Lean model is rebuilt on the new checker (`spine5`): the reference run ends borrows from a table of lent places and never from meanings. Decided and built on 2026-11-20 (`spine` ffc4458e; built and axiom-checked independently by the orchestrator): the model's data values are self-describing. A constructor value's meaning carries its declaration, its parameters, its constructor and its fields, so the reference finds its way inside a value by reading the value alone, as the checker does and as an element of Lean's set model does. Twice in one evening the old form (an opaque element of a set, decoded with a declaration or a type taken from elsewhere) made the model wrong on an accepted program: two declarations with the same set, and a field whose type's index had been moved. With it a call's result now carries its data type; its function shape is still lost. The reference run's tail-position flag, match entry and capture access are built too (`spine` cf732702), with the checker's decisions made part of the context every step carries. One disagreement was left on purpose: the checker runs a field read as a one-arm match whose entry reads the whole value, where the model reads the field directly. That was removed in the checker (D93, below), not copied into the model; the model is being aligned with it. Built since (`spine` 060a8335, docs/31 D59–D61): types mean codes, as in Lean's own metatheory, so a call's result, a function type computed by a call (`f : Fn(Nat)`, the predicate idiom) and a field keep their structure, and a proof read at a place has its place's type; the model's own run gives the checker's answer on the accepted programs that showed these gaps, and the four core lemmas are re-proved on codes. Found on the way and fixed: every recursive closure meant `err` (D60). A data type's code now names its declaration, parameters and carrier, and fields are read through the data model, so recursive and nested inductives have meanings (`spine` bfc0ad7f, D61; kernel-checked runs on `List` and `Rose` beside the checker's verdicts); the existence of a data model for every accepted program now also owes a reading coherent with it. Still to do here: the comparison at other futures; and restricting the claim about untyped runs. | 6% | 12% |
| 2 | Statement migration | The form every step statement takes. The simulation relation is re-made on the redesign, with no set of early-ended borrows and no witness clause: the same borrows held in the same positions, lent at the same places, readings equal. Proving the first composition changed the form in four ways (a run may start from any log; a step may conclude under an extended context of unknowns; the drop's grain is a hypothesis; scope is preserved along a list). Still to do: the remaining step statements moved onto it: reads, borrows, assignments, access, drops, calls, `J`, closing off and the tail forms. The eval forms, matches, observation and `Eq` were migrated to the earlier relation and are re-stated. | 3% | 4% |
| 3 | Provers: matches and arms | The drop at the join, splitting on an unknown, and leaving an arm. The drop at the join was the first proof attempted of any step; the attempt on the old checker found the fault that led to the redesign in row 1. On the redesigned checker the drop of a list of places is proved from the drop of one place, and that one is proved apart from named obligations: three typing facts (a non-copy data place never reads as a proof), that an access loses no unknown, that the copy decision leaves the state unchanged, and the run context after each step. Proving it changed the checker twice more (the join rejects an arm that moves a place its type does not have; one-constructor matches refine in place) and the model several times. Still to do: those obligations, then splitting on an unknown and leaving an arm. | 4% | 7% |
| 4 | Provers: dependent values | Give a partly opened dependent value a meaning in the reference run, which it lacks today, so the step can be stated. Then prove or refute that membership is restored when a value whose type depends on its own fields is made whole again, under every future of the parts still lent. One of the old proofs of `False` lived here. | 8% | 5% |
| 5 | Provers: `Id` | Prove the corrected statements: `Id` observes every place either side can write, and its computing to a conjunction over those places keeps the meaning. | 4% | 4% |
| 6 | Provers: well-formedness | The borrow discipline is preserved by every step, including the clause that no stored type or record holds a loan. | 4% | 4% |
| 7 | Universes | Deciding which statement Lean can prove over all programs. The bounded-levels statement is what the Lean development already builds; the open part is whether a uniform statement is provable (about 40% that it is not, which is a tweak, not a failure). | 1% | 1% |
| 8 | Prover tooling | A shared library about positions in a state, and the standard prover brief. | under 1% | 1% |
| 9 | Provers: equality | Conversion, `Eq` and `J` computing, and rewriting. | 3% | 5% |
| 10 | Provers: calls and stuck calls | Calls, closing a stuck call into a sealed program, re-running one, and the label-renaming lemma. | 4% | 8% |
| 11 | Provers: types and decisions | The model reads types and syntactic decisions the same way as the checker (18 statements). | 2% | 5% |
| 12 | Provers: simple steps | Borrow primitives, substitution, plain evaluation, tail forms. | 1% | 4% |
| 13 | Assembly | The top-level theorems, closing the induction, and the data model for a whole program. | 1% | 4% |

**Progress inside the to-do rows** (estimated 2026-11-20; a row moves to the done table only when it is finished). Row 1, reference-run redesigns: about four fifths (the checker redesign, the model rebuilt on it, self-describing data values, coded types built; a nested inductive's code and the older open differences left; re-estimated after D59, 2026-11-21). Row 2, statement migration: about half (the relation re-made, about a fifth of the statements in the new form). Row 3, matches and arms: about half (the drop at the join proved apart from named obligations). Every other row: not started, apart from invariant clauses for row 6 that are tested by the sweep and not yet proved preserved. That is about 14 of the 64 points, so roughly half of the whole effort is done.

## Reading the risk column

A unit fails only if it cannot be finished on the current plan. Restating a lemma, repairing a model definition and tightening one checker rule are all successes: the proof goes ahead as planned after each. Nearly every refutation so far has ended in one of the first two, and the accepted proofs of `False` found earlier ended in the third.

- **Chance at least one remaining unit needs a local checker fix** (a success): about 65%. Found so far, on 2026-11-19: three faults with one root, when a borrow ends. They were answered by the redesign in row 1, which counts as a feature redesign, not a local fix.
- **Chance at least one remaining unit fails**, so that a feature is redesigned or part of the proof is re-planned: about 30%. The rows are not independent (a fault in the simulation relation would hit several at once), so this is less than the rows multiplied out.
- **Chance the route itself fails**, so that meaning preservation has to be abandoned: about 7%.
- **Riskiest rows:** dependent values, where one of the old `False` proofs lived; then matches and arms, because it holds the first step proof: no step has been proved yet, and an earlier pilot under the old statement form closed nothing.

## Is it converging

Asked by the user on 2026-11-20: the effort keeps finding problems and no row of the table closes. This section keeps the evidence in one place so the question is answered by counts, not by feel. Updated at each half-day.

| Period | Checker changes landed | Of those, changing a verdict | Model definitions rebuilt | Simulation relation restated | Steps proved end to end | Areas attacked by proof |
|---|---|---|---|---|---|---|
| 19 Nov 16:30 to 20 Nov 04:00 | 3 (D90, D91, D92) | 1 (D90: three accepted functions that failed when run) | 2 (static lending; self-describing data values) | 2 | 0 | 1 (the join) |
| 20 Nov 04:00 to 16:30 | 6 (D93 to D98) | 3 (D93: two bugs and Rust's disjoint fields; D94: an ill-typed dead arm; D98: nine probe rows) | 3 (coded types; data codes; reads at recorded values) | 2 | 0 | 2 (the join, calls) |

What the counts say. The checker changes are getting less serious: the first fixed real faults; most since change no verdict and only make the checker's own paths agree. The model and the relation are not settling yet: each new area attacked by proof has forced a change to them. No step is closed. Six areas have not been attacked at all (dependent values, `Id`, equality and `J`, splits and worlds, closures and recursion, well-formedness), and the pattern so far is that an area's first real attack finds its faults.

What changes because of it. (1) Breadth before depth: after the call steps are stated and checked on concrete runs, every remaining area gets a bounded attack of the kind that has worked (its statements in final form, concrete runs checked in Lean beside the checker's verdicts, any needed fact swept on recorded states; no reading-only judgements), before more leaf lemmas are proved. That brings the remaining redesigns forward and shows whether the stream of faults is drying up. (2) A stop rule: if a full pass over the remaining areas still forces a change to the relation or a model rebuild per area, or if no step is closed end to end within a week of that pass, the architecture is re-examined (first candidate: a declarative rule system between the checker and the model, docs/33 item 2) instead of continuing.

## The two things running in parallel (from 2026-11-20)

**The first vertical slice: one step proved all the way down.** The step is the drop at the join, the first step of row 3. Its proof is split into pieces and the glue between the pieces is proved. What is left, in words:
- *The half where the place to drop already exists* is nearly closed. It needs a few small typing facts (a data place never reads as a proof), and the bookkeeping that the run's context is still right after a read.
- *The half where the place has to be made first* (an unknown pair refined into its fields, or a stuck value generalised) is the real work. It needs the counterpart, for unknowns, of the substitution lemma already proved for borrows: replacing an unknown by what a refinement says it is keeps every meaning. That is one large proof, of the size of a core lemma, plus the re-running of stuck programs after a refinement.
- *Two facts about the checker alone* (a read loses no unknown; reading a decision leaves the state as it was) are true by inspection; one is long because it is an induction over the whole interpreter.
- The rest of row 3 (matching on a known constructor, splitting on an unknown, closing a stuck match into a block, leaving an arm) is stated but not yet broken into pieces. The stuck match is the largest and riskiest step in the row.
Agreed with the user on 2026-11-20: a dedicated prover takes the easy half first; the hard half waits until the breadth pass has covered refinement, since that decides the statement of its large lemma.

At most three agents run at once (agreed with the user): the proof's lead on the breadth pass over the step areas, one agent on the data layer, and the slice prover; a checker fix, when one is needed, takes the place of one of them for its duration.

**The breadth-first pass: every remaining area attacked before more is proved.** The pattern so far is that an area's first real attack finds its faults (the join forced two rebuilds of the model, calls three, the data model four findings before anything was built). So before leaf lemmas are proved elsewhere, each remaining area gets a bounded attack, about half a day at most, by the proof's lead:
1. its statements written in their final form;
2. two to four small accepted programs whose run in the model is checked in Lean beside the checker's verdict, with rejected controls;
3. any fact about the checker that the statements need, tested on every recorded state of the suite before it is assumed;
4. the short proof that the area's step follows from its named pieces, where there is one;
5. a list of findings. A checker fault stops work and is reported with a minimal program; a fault of the model or of a statement is fixed in the open.
No judgement made by reading alone counts. The areas, in order: calls (finishing at the statement level); the top-level chain from the step statements to "an accepted definition means an element of its type" (the cheapest test of the whole architecture); `Id`; equality and `J`; splits and worlds; a table of which step establishes and which preserves each clause of the invariant; then, after the data model's new form is ported, closures and recursion, and dependent values. The counts per area go in the table above; the stop rule is stated there.

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

Acknowledged: borrow ends become a decision every run shares (D90; proposed by the user and acknowledged 2026-11-19).

## Design questions to ask before each risky unit

The bar is "as good as Rust for borrowing, as good as Lean for proving". Where a unit is hard because the design is more precise than that, the design is questioned before the proof is attempted.

- **Borrow ends (row 1):** asked and answered: the redesign in row 1.
- **Matches and arms (row 3):** asked 2026-11-19, while the drop of one place was open. Part of that proof exists only because the checker has to find a place that does not exist yet (a field of an unknown pair, of a stuck value, or under a lent parent). Keeping values of one-constructor types expanded into their fields would make such places always exist, and is the parked change that also restores Rust's precision for disjoint fields. The proof lead's estimate: it would delete about a third of that one proof, and none of the lemmas that carry the risk (an access, an end, marking a part moved, the two ways of finding a place agreeing), which every other step needs anyway. Conclusion at the time: do not make the change for the proof's sake. Revised 2026-11-20: the change is being made after all, because four things now point at it (the disjoint-fields gap against Rust, two checker faults, and a disagreement between the checker and the model on which borrows are live after a field read), not because of the proof it would shorten.
- **How the model decodes a data value (row 1):** asked 2026-11-20, after two faults with one root. Options weighed: self-describing values; a type skeleton kept beside each position; Lean's coded types alone; and, for the partial-move case only, tightening the checker so the join's drop does the checks a move does. Conclusion: self-describing values, with types of data as codes naming the declaration and its parameters. It removes the root, mirrors the checker's own values and Lean's set-theoretic elements, and deletes an invariant clause and a restriction; Lean's coded types alone would not cover a value whose type's index has been moved, which Lean never has. The checker is not changed. Recorded as docs/31, D32, and compared against Lean in docs/33.
- **Dependent values (row 4):** asked 2026-11-19, with the user. The difficulty is a value whose later field's type depends on an earlier field that is lent or half-written. Conclusion, in two parts. (1) Inside a function body there is no problem to solve in the language: once such a value is open, the checker types the later field by what it holds, not by the earlier field, so its type does not follow the lent field. The model does not do this yet (it re-reads the earlier field through the borrow), and that is the fault to fix, in the model. (2) At a point where the value must be whole again (a return, a call), the checker does not require the loan ended: it checks the value with the lent part replaced by a fresh unknown of its type, so the invariant must hold whatever the borrow later writes. Requiring every loan ended there would be simpler, but it would reject accessors that return a borrow into data an invariant mentions (the examples' user-land vector, whose invariant says its first cells are full, returns a borrow into a cell's payload), and Rust has those. So the rule stays; it is also what closed the two proofs of `False` found here. The step to prove is then the natural one: a check that passes for a fresh unknown gives membership under every final content of the borrow.
- **`Id` (row 5):** its rules about when a borrow ends (a side may not end a borrow held outside it) exist because sides run on private copies. Once ends are a shared decision, check which of those rules are still needed.

## Dependencies

An arrow from X to Y means Y builds on definitions or statements that X produces. Green is done, yellow is running, grey is to do. No arrow leaves a prover row except into the assembly, because nothing depends on a proof; the order among prover rows is the table's.

```mermaid
flowchart TD
    classDef done fill:#c8e6c9,stroke:#2e7d32,color:#000
    classDef running fill:#fff59d,stroke:#f9a825,color:#000
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

    redesign["1. Reference-run redesigns<br/>(borrow-ends redesign folded in)<br/>10%, fail 5%"]:::running
    migrate["2. Statement migration<br/>(the relation re-made)<br/>4%, fail 3%"]:::todo

    pMatch["3. Provers: matches and arms<br/>6%, fail 5%"]:::todo
    dep["4. Provers: dependent values<br/>5%, fail 8%"]:::todo
    idn["5. Provers: Id<br/>4%, fail 4%"]:::todo
    wf["6. Provers: well-formedness<br/>4%, fail 4%"]:::todo
    universes["7. Universes<br/>1%, fail 1%"]:::todo
    tooling["8. Prover tooling<br/>1%, fail under 1%"]:::todo
    pEq["9. Provers: equality<br/>5%, fail 3%"]:::todo
    pCalls["10. Provers: calls and stuck calls<br/>9%, fail 4%"]:::todo
    pTypes["11. Provers: types and decisions<br/>5%, fail 2%"]:::todo
    pSimple["12. Provers: simple steps<br/>6%, fail 1%"]:::todo

    assembly["13. Assembly<br/>4%, fail 1%"]:::todo
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
