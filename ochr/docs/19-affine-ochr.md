# 19. Making Ochr affine: what it buys the metatheory, and what it costs the programmer

Written on 2026-11-03 at the user's request. Status: **draft for review, not a decision.** The question comes from BendTT (`docs/papers/bend-tt.pdf`), which keeps `Type : Type`, impredicative function types and negative datatypes and is still consistent, because its running code is affine and may not copy a function. Could Ochr take the same route, and what would that do to (i) the proof of consistency and (ii) writing Ochr programs?

## The short answer

- **Metatheory.** Affinity would replace the hardest *semantic* half of the consistency plan (docs/18) with a syntactic argument: no set model, no inaccessible cardinals, no logical relation, no Girard candidates, and no gap between "true in the model" and "the machine ran it". It would **not** remove the hardest *operational* half: the two evaluation paths must still agree (the stability conjecture), because for Ochr "evaluation keeps the type" is exactly that conjecture. It also only works if proofs stop being erased in the metatheory, which is a large change to Ochr's core.
- **Programmer experience.** Owned data is already affine in Ochr (D53). What would change is functions and proofs: a closure could be called at most once, so `map`-style higher-order code and several of the case studies' combinators stop checking, and a hypothesis of function type (an implication or a "for all") could be used once in a proof. In return Ochr could drop universe levels and the positivity rule. A Rust-style variant, calling functions through borrows, would keep most of the ergonomics, but whether it keeps the simple termination argument is unknown.

## 1. What "affine" would mean for Ochr

Bend's live code follows three rules (bend-tt §1): a variable is used at most once; only a variable whose type is `Data` (labels, pairs, equality proofs, no functions) may be used more than once; a definition calls only earlier definitions, and itself only on smaller arguments. Types, annotations and erased arguments are *dead* code and are exempt.

Ochr already satisfies much of this:

| Bend rule | Ochr today |
|---|---|
| Owned values are used at most once | **Yes for data.** Since D53 a runtime read of a non-copy value moves it, and `clone` is explicit. |
| Only first-order data is copyable | **Mostly.** Copy types are `Unit`, sorts, propositions, inductives declared `copy` (`Word`) and non-recursive inductives with copy fields. **But** a closure is copyable when everything it captures is, as Rust's `Fn` (D53(e)). |
| A call consumes the function | **No.** A call does not consume its function (D53(e)), so a function variable can be called many times. |
| A match consumes its scrutinee | **No.** Ochr matches on *places*: pattern variables name sub-places, and the scrutinee stays usable afterwards. |
| Proofs are live and affine | **No.** Proofs are erased: their value is `⋆` (D27, D49), calls at a proposition are not run, and a hypothesis can be used any number of times. |
| Types are dead and exempt | **Yes.** Statements run on a private copy that is discarded (P2, D68), so a type may mention a variable many times. |
| Definitions call earlier ones, and themselves only on smaller arguments | **Yes.** Items are checked in order, there is no mutual recursion, and [Rec] demands structural descent on the declared `by` parameter. |
| Functions may not be stored in data | **Stricter than Bend.** Ochr forbids function-typed fields altogether (D36, K4); Bend allows them and relies on affinity instead. |

So "making Ochr affine" means four concrete changes, of which the last is the big one:

1. **Functions are never copyable.** A closure is not a copy type, whatever it captures.
2. **Calling a function variable consumes it**, or (variant B below) a function can be called repeatedly only through a borrow.
3. **A match on an owned value consumes it**, or (variant B) follows Rust's partial-move and borrow-conflict rules, so that `match b { MkBad(f) => f(b) }` is rejected because `b` is used after `f` was taken out of it.
4. **Proofs are live in the metatheory.** A proof has a value that can be run, and proof code obeys rules 1 to 3. The compiler may still erase proofs, as Bend's compiler erases dead code; what matters is that the consistency argument can run a proof.

Two variants are worth distinguishing:

- **Variant A, Bend-strict:** rules 1 to 4 exactly as Bend has them. A closure is called at most once; repeated application needs a named definition, a compile-time template, or a copyable data parameter (bend-tt §7).
- **Variant B, Rust-style:** functions are never copied, but may be called repeatedly through a borrow (`&f`, Rust's `FnMut`), and matches follow Rust's partial-move rules. Ochr's existing rules already forbid borrows inside data and borrows captured by closures, which is exactly what would stop a self-applying function from being built out of a borrow (`MkBad(&f)` cannot exist). Whether variant B keeps Bend's termination argument is the main open question (§2.4).

## 2. The metatheory

### 2.1 What affinity buys

Bend's consistency proof is short (bend-tt §1, §6): suppose an accepted definition `k` had the empty type. `k` is live, so its evaluation ends; evaluation keeps the type and does not get stuck, so it ends in a value of the empty type; there is no such value. Four theorems carry it: termination of live code, subject reduction, progress, and "no value has the empty type". All four are proved in about 4,000 lines of Lean, against the checker that runs, with no axioms of its own.

For Ochr, the same shape would remove most of what the three referees found wrong with docs/18:

- **No set model is needed.** "True" becomes "a closed live proof runs to a value". The main gap the referees found, that truth in the set model ranges over non-computable functions while the soundness walk only covers machine values (the halting-decider `L3`, the closed `UseK`), disappears: there is no set-theoretic truth to match.
- **No logical relation, and no Girard candidates.** Termination comes from a multiset measure on pending calls that ignores types; it works because affine code never copies work still to be done (bend-tt §6). Impredicative `Prop` costs nothing, because no step of the argument normalises a type.
- **No inaccessible cardinals and no Gödel obstacle.** Bend proves its theorem inside Lean. A system whose consistency follows from a call-counting measure is weaker than Lean, so the uniform Lean statement becomes provable in principle (docs/18 Q8 goes away).
- **The statement already has the right shape.** Bend's theorem is about the checker that runs (`Book.check`), as `Ochr.Consistency.consistency` is.
- **Simplifications to the calculus.** Positivity (D36, K4 and their Figure 16 rows) and universe stratification (D66 and the non-cumulativity rows) could be dropped, as Bend drops them. Ochr's ban on function-typed fields could be relaxed to allow negative and higher-order datatypes.

### 2.2 What affinity does not buy

- **Stability does not go away; it becomes subject reduction.** In Bend, "evaluation keeps the type" is a standard result about a pure calculus with a declarative typing judgement, proved via confluence of parallel reduction. In Ochr, typing *is* the machine run at a definition's generic call, with closing off, sealed programs and observations. When a live proof `k` runs and steps into a lemma it calls, the lemma's body runs at concrete arguments, and its type must be the lemma's statement at those arguments: the statement checked once, generically, must hold at the instance. That is the stability conjecture (docs/18 §7, lemma N with its parts (P), (C), (Sp), and M). Affinity removes the model half of the plan, not the simulation half.
- **Ochr is not a pure calculus.** Bend's proofs use confluence of parallel reduction on terms. Ochr has places, borrows, loans, mutation and an ordered machine; progress and preservation would be about machine states, which is where the machine invariants T1 to T5 of docs/18 live. That is the same work the current plan needs.
- **Checker bugs remain checker bugs.** `EtaBoom`, `BoomJ` and `BoomCap` were mismatches between the generic path and the instance. A syntactic consistency theorem would rule them out only once it is proved, and proving it requires exactly the stability lemmas that would have caught them.

### 2.3 What affinity costs the metatheory

- **Proofs must run.** Bend's argument runs a proof to a value. Ochr binds proof parameters to `⋆` at the generic call (D27), gives every proof the value `⋆` (D49), skips calls at a proposition, and decides matches on proofs by type. The metatheory would need a second, proof-relevant evaluation in which proofs have real values and run, related to the checker's proof-irrelevant one. That relation is new work with no counterpart in the current plan.
- **Proof irrelevance and subsingleton elimination interact.** Large elimination from subsingletons (D45) lets a proof decide data. With live proofs, a match on a proof must consume it (rule 3), and the argument that two proofs of one proposition are interchangeable must be re-established for the proof-relevant evaluation.
- **The termination measure must cover Ochr's machine**: mutation, borrows, closing off, stuck blocks and the re-running of sealed programs. Ochr's existing restrictions help: closures capture no borrows, data holds no functions, so Landin's knot (recursion through a mutable cell holding a function) cannot be built. But the measure has never been stated for a stateful machine.

### 2.4 Open questions

1. **Variant B's termination.** Calling a function through a borrow repeatedly runs its body many times, which is "copying work still to be done" in Bend's sense. A named definition can also be called many times, and Bend's measure handles that through the order on definitions; whether closures called through borrows can be given a place in the same order is unknown. This is the question that decides whether an ergonomic affine Ochr exists.
2. **Relating proof-relevant and proof-irrelevant evaluation** (§2.3), and whether conversion's proof irrelevance survives.
3. **Whether the dead part may stay inconsistent.** Bend's dead part can hold Girard's paradox. Ochr's statements are dead, but they run code (an `Id` statement runs the programs it compares). A statement that loops is harmless (fuel makes it undecided), but any rule that lets a dead fact influence a live decision would bring the paradox back into live code.

## 3. The programmer experience

### 3.1 Comparison

| | Lean | Rust | Ochr today | Affine Ochr, variant A (Bend-strict) | Affine Ochr, variant B (Rust-style) |
|---|---|---|---|---|---|
| Owned data | Persistent, copied freely; in place only when uniquely referenced | Moved; `Copy` types copied; `clone` explicit | Moved (D53); copy types copied; `clone` explicit | Same as today | Same as today |
| Calling a function value twice (`map`, `fold`, callbacks) | Free | Yes, through `Fn`/`FnMut` | Yes: calls do not consume, closures are copyable if their captures are | **No.** A closure is called at most once; use a named definition, a template, or a copyable data parameter | Yes, through a borrow of the function |
| Copying a closure | Free | Only if it is `Copy`/`Clone` | Yes, if its captures are copy | Never | Never; borrow it instead |
| Matching, then using the scrutinee again | Free | Partial moves and borrow conflicts are checked | Free: pattern variables name sub-places | Match consumes the scrutinee | Rust's rules |
| Matching through a borrow (in-place code, `AddM`) | n/a | Binds sub-borrows | Binds sub-places | Must bind reborrows: unchanged in practice | Unchanged |
| Using a hypothesis twice in a proof | Free | n/a (no proofs) | Free: proofs are erased | Equality proofs and proofs built from data: free. Implications and "for all" hypotheses: **once** | Once by value, repeatedly through a borrow |
| Mentioning a variable many times in a statement | Free | n/a | Free (statements are erased) | Free (statements are dead) | Free |
| Universe levels | Yes, with polymorphism | n/a | Yes, non-cumulative | **None needed** (`Type : Type`) | None needed |
| Negative or higher-order datatypes (HOAS terms) | Rejected by positivity | Allowed (no logic) | Rejected; no function-typed fields at all | **Allowed** | Allowed |
| Church encodings and iterated functions | Free | n/a | Allowed | Rejected (they apply `f` twice) | Through borrows |
| Recursion | Structural, well-founded, mutual | Unrestricted | Structural (`by`), no mutual; fuel for the rest | Same as today | Same as today |

### 3.2 Effect on the existing code

Owned-data code and in-place code through borrows (`AddM`, `TailM`, the slice operations) are unaffected: they are already affine. The changes fall on higher-order code and on proofs:

- **`FromFnS` and `ArrFromFn`** (`Examples/Array.lean:143`, `:205`) apply `f` at every index and pass `f` to the recursive call: Bend's rejected `map`, line for line. `EmptySlots` and `EmptyFrom` in the hash map build their arrays this way.
- **`Recurse`** in quicksort (`Examples/Quicksort.lean:60`) calls `rec` and then `clone(rec)`, copying a closure. Its own comment says "a closure may run again, D53". Variant A rejects it; variant B would call `rec` twice through a borrow.
- **`RecWith`** returns a closure built from `qs`, and the quicksort driver passes closures to `Recurse`.
- **Proof combinators that take a "for all" hypothesis.** Many quicksort and hash map lemmas take a hypothesis such as `hz : Π(q : Word) (hq : Lt(p, q)). Eq(…)` and pass closures built from it (`Quicksort.lean` has 40 lines with a λ and `HashMap.lean` 13; 67 declarations across the examples take a function-typed parameter). Some already use such a hypothesis at most once on every path (`AllLeOfCounts` calls `hz` in one arm and captures it in the other), and would check unchanged; any that applies a hypothesis at two points on one path would need it restated as a named lemma or passed by borrow.

The workarounds are the ones Bend documents (bend-tt §7): name the function as a top-level definition (names are not variables and can be called freely), pass it as a compile-time template (closed only), or turn the loop into its own definition with the captured value as a copyable data parameter. All three trade closures for top-level definitions, which moves Ochr's style towards first-order functional code.

### 3.3 Relative to Lean and Rust

- **Against Lean**, variant A gives up free use of higher-order functions and of implication hypotheses in proofs, which Lean users rely on constantly (`simp`-style reasoning, `∀` hypotheses applied at many points). It gains `Type : Type` and negative datatypes, which Lean forbids, but Lean users rarely miss those.
- **Against Rust**, variant A is stricter than Rust for functions: Rust's `Fn`/`FnMut` closures can be called many times, and idiomatic Rust leans on iterator adaptors that do exactly that. Variant B matches Rust closely: owned values move, functions are called through borrows, and matches follow Rust's partial-move rules. For a Rust programmer, variant B would feel like Rust; variant A would feel like Rust without closures.
- **Against current Ochr**, which already feels like Rust for data and like Lean for proofs, variant A makes both functions and proofs more restrictive; variant B mostly restricts proofs.

## 4. Where this leaves the decision

Affinity is a real alternative for the *semantic* half of the consistency argument: it would replace the set model, the logical relation, the inaccessibles and the referees' main gap with a call-counting termination argument that has been mechanised for BendTT. It is not an alternative for the *operational* half: the stability lemmas, reframed as subject reduction, remain, and they are where every closed proof of `False` found so far came from. The price is proofs that run in the metatheory (a significant change to D27, D49 and P2) and, in the strict variant, the loss of repeatedly called closures, which the case studies already use.

The variant worth investigating, if any, is B: Rust-style affinity with repeated calls through borrows, which keeps most of today's programming style. Its viability turns on one question, whether calls through borrows fit a Bend-style termination measure (§2.4, question 1). A bounded probe could answer it before any design change: state the measure for a small calculus with closures, borrows and Ochr's no-borrows-in-data rule, and either prove termination or find the self-applying counterexample.
