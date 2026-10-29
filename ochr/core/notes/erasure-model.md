# Erasure, private copies and stuck-block captures: a model

Branch `erasure-model`, off `theory-integration` (`db8fedd4`). The fourth model lane, after `depfields-model` (D75, D76), `split-model` (worlds, `Id`) and `rec-model` (D78). **No new hole found.** Erasure is already sound by construction, with a single place where an erased term is run, and the stuck-block capture rules are an over-approximation that is safe by a short argument. The probes are kept as a regression block (`ClosingOff.lean`, block `BlockCaptures`, 8 declarations, total 1,732).

## 1. Erasure

**What erasure means.** A statement position (a type, a proof, an erased call and its arguments, `J`'s endpoints and motive, a side of `Eq`, an `Id` side's observation) has a *value* (⋆, or a type), never an *effect*: the compiled program does not run it. So checking may run it, but whatever it does to the state must be invisible afterwards, and what the checker decides from it must be the same whether it ran or not.

Five principles:

- **(E1) Discard.** Every erased term runs on a private copy of the state it would start in, and the copy is thrown away. In the checker this has one entry: `eval`'s wrapper, which decides `erasedHere` by the pre-pass and runs the term under `onCopy` (`Machine.evalAt`). The other statement positions (`evalType`, `J`, `Eq`, `callType`, `observe`, a Π-type's capture) call `onCopy`/`stmtCopy` themselves. Nested erased terms each get their own copy.
- **(E2) Decided by declaration.** Whether a term is erased is read from syntax and declared types (D28, D35, D55, D74, D77), so both evaluation paths make the same decision. With D55 a term's declared sort *is* its computed sort, so "is a proof" is a property of the term itself, not of its context: when a stuck block's body drops a `let`'s annotation (`let h : True = (x := 1; I)` becomes `let h = (*x := 1; refl : ⊤)` in the sealed program), the bound term is still a proof by its own declaration and is still erased on the re-run (probe E6).
- **(E3) Only copy-independent facts survive a copy** (`restoreKeep`): name counters (a counter states no fact; D37); the types of names created in the copy (no one outside can mention them); generalisation records (a record maps a *closed* program text to a fresh `σ`; the text normalises the same in any state, and its type is the matched place's, which D64 makes the content's own type when the value is open); η-refinements (read off a one-constructor type, true everywhere); [Rec] obligations already checked; pure caches. Everything else, Ω, stored types, the goal, refinements, the move log, is restored. Copies nest inside worlds (`split-model`'s X), so a world fact made inside a copy is still dropped at the world's exit.
- **(E4) In place means in the statement's copy.** A borrow-typed argument of a statement runs in place, not on its own copy (`stmtArgIf`, `Decide.stmtArgInPlace`), because the borrow must be the real one. This is safe because a statement callee's call is itself erased by the pre-pass (a callee returning types or proofs makes its call a statement; the pre-pass assertion catches any disagreement), so "in place" is relative to the enclosing copy. Probe `ProofLendsInArm`.
- **(E5) Reads move inside statements as at runtime** (D68), on the copy. Their only visible consequence is inside the statement itself: a side that reads `x` and then observes `x` sees `⊥`, which makes its equation stuck (fail-safe; probe E1).

## 2. Stuck-block captures

**What a block means.** A stuck match is closed off as a call of an anonymous function of the places it captures; at each instance the direct path instead runs the arm the value selects, in place. The block is right if the code after it, checked at the generic call, never assumes less than some arm actually did.

- **(K1) Over-approximation.** For every outer place `q` and every arm `i`, the block's mode for `q` is at least arm `i`'s effect on it, in the order none ⊑ read (copy) ⊑ write or borrow (`&`) ⊑ move; effects are measured at the granularity of the place an arm moves (`q.1` moved while `q.0` is lent), net of the arm's own refills (an arm that moves `a` and assigns it again has written `a`, not moved it); and a closure or Π-type in an arm counts as moving what it mentions, whether or not the run took that arm (D68).
- **(K2) Over-approximation is safe.** A stricter generic call only removes options from the code after the block: a read of a place the block moved reads `⊥` and is rejected; a borrow variable the block moved holds `⊥`, so its owners leave the footprint only where later code assigns the variable as a whole (paper Lemma 14), and an equation over a moved place is stuck. None of these adds an acceptance.
- **(K3) Effects are measured where they happen.** An arm's moves come from its run's log (`placeLog`, `armMoves`), so a move inside a nested block is that block's move of its argument (they compose), and a move inside a statement is discarded with the statement's copy (E1), as at runtime.
- **(K4) The re-run decides as the direct arm does.** A block's sealed programs re-run its arms under later refinements; by E2 every erasure decision there is the direct arm's.

## 3. Derived rules against the current ones

| Current rule (code) | Principle |
|---|---|
| `eval` wrapper: `erasedHere` ⇒ `onCopy` | E1 |
| `stmtCopy`, `onCopy` at statement positions (`evalType`, `J`, `Eq`, `callType`, `observe`, Π capture) | E1 |
| pre-pass and its after-the-fact assertion; `Decide.lean` | E2 |
| `restoreKeep`'s kept fields | E3 |
| `stmtArgIf` / `stmtArgInPlace` | E4 |
| D68 erased reads move | E5 |
| `closeBlock`: syntactic uses, max mode per maximal place | K1 |
| `armMoves` (net of refills), `moved` | K1, K3 |
| `fnOccs`: closures/Π in arms move | K1 |
| split of a capture into fields when an arm moves part of it | K1 (granularity) |
| a proof place is never taken by `&` | K1: a write through a matched proof's pattern variable is local to the proof's value, which is ⋆ |
| a borrow variable read or assigned whole is moved in | K1 |

**Missing obligations: none found.**

## 4. Probes

Each run with verdicts printed explicitly and a rejected control (`def Ctrl : False := refl`).

| Probe | Shape | Verdict | Reading |
|---|---|---|---|
| E1 | a proof assigns `x` inside an `Id` side | rejected (`Eq(Nat, ⊥, ⊥)`) | E5: the side read `x`; fail-safe incompleteness |
| E1b | the same, claiming the write happened | rejected | E1 |
| E3 | a statement in an arm reads `x`; `x` read after | accepted | E1 |
| E4 | a closure inside a statement in an arm mentions `x`; `x` read after | rejected | K1 (D68), stricter than the direct path: incompleteness |
| E5 / `ProofLendsInArm` | a proof in an arm lends `x` to a lemma | accepted | E4 |
| E6 | an erased write to `x` in an arm, `Id` after | rejected (goal stuck) | the block takes `x` by `&` because the write occurs syntactically; true statement, incompleteness (see P-c) |
| E7 | the same, claiming the write happened | rejected | E1, K4 |
| `MovedField` | an arm moves `q.0`; read after | rejected | K1 |
| `RefilledField` | an arm moves and refills `q.0`; read after | accepted | K1 (net) |
| `LentSibling` | one arm lends `q.0`, the other moves `q.1`; read `q.0` | accepted | K1 (granularity) |
| `MovedSibling` | same; read `q.1` | rejected | K1 |
| `StmtInArm` | a statement in an arm reads `x`; `Id` of `x` after | accepted | E1, K3 |

## 5. Proposals

Landed (verdict-neutral):

- **P-a, one statement combinator.** `Env.inStatement` (E1–E5 are its docstring) is the one place a statement position runs: `eval`'s erasure wrapper, `evalType`, a Π-type's captures, `Eq` and each of its sides, `J`'s endpoints and motive, an inductive's parameters, a statement call's arguments (`stmtArgIf`) and an `Id` side (`observe`). The checker's own scaffolding, which binds parameters, captures or field values to compute a type, a hint, a sealed program's type, an [Open] check or [Conv-fun]'s observation, runs through `Env.privately` instead, whose docstring says why none of it is a statement position. `onCopy` is now private to `Env.lean`, so every discarded run is one of the two, by name; `stmtCopy` is gone. What survives either is `restoreKeep` (E3). Two sites gained `withErased` (`stmtArgIf`, `observe`): an instrumented run of all 1,732 registered verdicts found both always already inside an erased term, so on the suite this is a no-op, and no verdict changed.
- **P-b, K1 as a function.** `Machine.blockCaptures`, called by `closeBlock`, is the capture computation, moved verbatim; its docstring is K1, with clauses (a)–(g) marked in the code where each is computed and the fuzz-port findings they came from named beside them. It carries the two-paths marker for census site 13, as `closeBlock` does.

Not landed (a rule change, for the user):
- **P-c, incompleteness.** Three true shapes are rejected: (i) an `Id` side that reads a place it also writes observes `⊥` (E1); (ii) a closure inside a statement inside an arm moves its captures at the generic call (E4); (iii) the block takes a place by `&` because an *erased* term in an arm assigns it (E6), so the statement about it is stuck. (iii) could be lifted by counting only occurrences outside erased positions when computing modes, which the pre-pass decides syntactically (E2); it is a rule change and is left to the user.

## 6. Open

As in every model lane, K4 and E2's re-run argument rest on the stability lemma N (part P): a sealed program re-run under a refinement agrees with the direct arm. Nothing here adds an obligation beyond N.
