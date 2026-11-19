# Probes: static borrow ends (D90)

Programs from the static-ends lane (2026-11-19). Each file runs with
`lake env lean ../probes/static-ends/<file>.lean` from `ochr/core/lean`, and is silent on the
checker after D90: its `def`/`reject def` expectations are D90's verdicts. What each showed on
main before D90 (a869a275) is below. The programs marked *asserted* are also in the asserted
examples (`Ochr/Examples/ReturnedBorrows.lean`, blocks `StaticEnds` and `StaticEndsRuns`), where
they are checked by every build.

| file | programs | on main before D90 | after D90 |
|---|---|---|---|
| `EIsmall.lean` | `EI`, `EIRun`, `EIRun0` | `EI` accepted, `EIRun` rejected ([Id-typestate]: a side ends `r`) | all accepted (asserted) |
| `EJ.lean` | `EJ`, `EJ1`, `EJRun`, `EJRun0` | `EJ` accepted, `EJ1` and `EJRun` rejected ([D53] partly moved) | all accepted (asserted: `EJ`, `EJRun`, `EJRun0`) |
| `Census.lean` | `G1`–`G8` and closed calls | `G1` accepted and `G1Run` rejected (the third fault: `movedPlace` generalised a fill holding a live hole); `G4`, `G6` accepted; `G2`, `G3`, `G5`, `G7`, `G8` rejected | `G1`, `G6` newly rejected; `G4` accepted (asserted: `G1`, `G1Run`, `G3`, `G4`, `G5`; `G6` as `PickZ`) |
| `CensusBlock.lean` | `EIB`, `EJB`, `GJ`, `GJI` and closed calls | `EIB`, `EJB`, `GJI` accepted with their closed calls rejected (the faults through a stuck block's captures, and through `J`'s); `GJ` rejected | `EIB`, `EJB`, `GJI` and their calls accepted (asserted) |
| `Census2.lean` | reborrow transfer `G8`/`G8K`, nested calls `Nest`/`NestK`, `Pick2`, a tail match in a proof match's arm `PT`, `Local` | `G8K`, `NestK` accepted; the rest as after | `G8K`, `NestK` rejected (Rust rejects both) |
| `Census3.lean` | `SplitKeeps`, `SplitKeeps0` | both accepted (a split world's re-run of `b`'s fill dropped `r`'s hole) | both rejected: `b` stays lent (Rust rejects) |
| `Fields.lean` | `F1`–`F4`, disjoint field borrows | `F1`–`F3` rejected (abstract `x`), `F4` accepted (known `x`) | all rejected: D90's known gap F4 (Rust accepts all four) |
| `Snapshot.lean` | `EK` | `EK` and its closed calls accepted | `EK` rejected (asserted): D90's known gap EK (Rust accepts) |
| `Sealed.lean` | `SF`, `SF0` | both accepted | both rejected: a place below a sealed fill has the fill's holes on its path |
| `Reborrow.lean` | `RB`: a reborrow of a part of `*r` outlives the returned borrow `r` | all accepted | all accepted; the place `r` points into stays marked (`lent_r loan_r`), so the whole of it is handed to the reborrow when `r` ends |
| `CloneProj.lean` | `CL`, `CLg`, `CLrun` | `CLg` accepted, `CLrun` rejected | the same: **not a D90 probe**, a fault on main found while writing D90 (`clone(x.0)` moves `x.0` at the projection match's join) |
