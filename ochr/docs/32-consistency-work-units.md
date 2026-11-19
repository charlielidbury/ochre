# 32. The consistency proof as work units: done and to do

Written 2026-11-19. A map of the whole consistency effort (Target A of docs/18), one row per unit of work of roughly one agent's size. The plan itself is docs/18; the detailed record of the Lean development is docs/31 on the `spine` branch.

The numbers are estimates by the orchestrating session, not measurements.

- **P(success)** is the chance the unit goes through without changing the checker's rules or the form of the main theorem.
- **Time** is the unit's share of all the effort the consistency proof needs. The column sums to 100% over both tables: about 31% is done and 69% remains.

## Done (31%)

| Work unit | What it contains | P(success) | Time |
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

Not counted, because they are off the consistency path: `id-audit` and `subst-survey` (the dropped `Id` target), `runtime-j` (type safety), `paper-claims` and `docs18-sync` (document upkeep).

## To do (69%)

| Work unit | What it contains | P(success) | Time |
|---|---|---|---|
| `spine3` (running) | Two prerequisite lemmas. Then prove or refute the two riskiest steps in the new form: the drop at the join, and `Id`'s observation. | 0.6 | 5% |
| Statement migration | Move the remaining ~70 step statements to the simulation form, one file at a time. | 0.85 | 4% |
| Reference-run redesigns | The five open differences from the checker, the comparison at other futures, and restricting the claim about untyped runs. | 0.7 | 7% |
| Prover tooling | A shared library about positions in a state, and the standard prover brief. | 0.95 | 2% |
| Provers: simple steps | Borrow primitives, substitution, plain evaluation, tail forms. | 0.85 | 9% |
| Provers: calls and stuck calls | Calls, closing a stuck call into a sealed program, re-running one, and the label-renaming lemma. | 0.65 | 9% |
| Provers: matches and arms | Splitting on an unknown, leaving an arm, and the drop at the join. | 0.7 | 6% |
| Provers: equality | Conversion, `Eq` and `J` computing, and rewriting. | 0.75 | 5% |
| Provers: `Id` | `Id` observes every place either side can write. | 0.6 | 4% |
| Provers: types and decisions | The model reads types and syntactic decisions the same way as the checker (18 statements). | 0.8 | 5% |
| Provers: well-formedness | The borrow discipline is preserved by every step. | 0.7 | 4% |
| Provers: dependent values | Membership is restored when a value whose type depends on its own fields is made whole again. | 0.55 | 4% |
| Assembly | The top-level theorems, closing the induction, and the data model for a whole program. | 0.85 | 4% |
| Universes | Deciding which statement Lean can prove over all programs. | 0.6 uniform; 0.95 with bounded levels | 1% |

## Reading the risk column

A failure in one row rarely ends the project. It usually means a fix to a statement or to the checker, then continuing; every refutation so far has gone that way.

- **Chance at least one remaining unit forces a checker change:** about 60%.
- **Chance the route itself fails:** about 10%.
- **Riskiest rows:** dependent values, where one of the old `False` proofs lived, and `Id`.

## Dependencies

An arrow from X to Y means Y builds on X. Green is done, yellow is running, grey is to do. The eight prover units are independent of each other: each proves its steps from the shared induction hypothesis, so they can run in parallel once the statements are migrated.

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

    spine3["spine3: prerequisites and<br/>riskiest steps<br/>5%, P 0.6"]:::running
    migrate["Statement migration<br/>4%, P 0.85"]:::todo
    redesign["Reference-run redesigns<br/>7%, P 0.7"]:::todo
    tooling["Prover tooling<br/>2%, P 0.95"]:::todo

    pSimple["Provers: simple steps<br/>9%, P 0.85"]:::todo
    pCalls["Provers: calls and stuck calls<br/>9%, P 0.65"]:::todo
    pMatch["Provers: matches and arms<br/>6%, P 0.7"]:::todo
    pEq["Provers: equality<br/>5%, P 0.75"]:::todo
    pId["Provers: Id<br/>4%, P 0.6"]:::todo
    pTypes["Provers: types and decisions<br/>5%, P 0.8"]:::todo
    pWF["Provers: well-formedness<br/>4%, P 0.7"]:::todo
    pDep["Provers: dependent values<br/>4%, P 0.55"]:::todo

    universes["Universes<br/>1%, P 0.6"]:::todo
    assembly["Assembly<br/>4%, P 0.85"]:::todo
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
    spine2 --> redesign
    spine3 --> migrate
    spine3 --> tooling

    migrate --> pSimple
    migrate --> pCalls
    migrate --> pMatch
    migrate --> pEq
    migrate --> pId
    migrate --> pTypes
    migrate --> pWF
    migrate --> pDep
    tooling --> pSimple
    tooling --> pCalls
    tooling --> pMatch
    tooling --> pId
    tooling --> pWF
    tooling --> pDep
    redesign --> pCalls
    redesign --> pDep
    progdec --> pTypes

    pSimple --> assembly
    pCalls --> assembly
    pMatch --> assembly
    pEq --> assembly
    pId --> assembly
    pTypes --> assembly
    pWF --> assembly
    pDep --> assembly
    datagen --> assembly
    progdec --> assembly
    universes --> assembly
    assembly --> goal
```
