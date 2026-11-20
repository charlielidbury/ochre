# Lead handoff (sixth lead, from 2026-11-20 evening)

Branch `spine-lead` (worktree `/home/charlielidbury/repos/ochre-spine`), from `origin/spine` 1216caba. Read with docs/31 (from D81 on).

## Decided / found
- Item 1 of the first job (evaluation is not type-sound in the statements): CONFIRMED, `Regress/EvalMemGap.lean` (987a2b60), standard axioms.
  - `bodyReturns_sound_stmt` is FALSE (`bodyReturns_false`): [Return] checks only [Repack], a no-op on non-dependent values; `0` at `Unit` passes.
  - A typed `let` cannot be assembled: `Good` after its push contains the value's membership (`good_withBind_mem`); `eval_step`'s conclusion holds with a non-member in flight (`good_S0T`, `not_good_push`).
  - Same root, second fault: `Good` is false of any state with a borrow argument in a temporary whose lender is typed (`borrowArg_not_good`), so the call statements' hypothesis `Good (st.withTemps …)` is unsatisfiable at borrow arguments.

- Also false: `repackCheck_sound_stmt` (`repackCheck_false`), same cause.
- Items 2–4 (docs/31 D81): design = typed temporaries (every value the machine holds has a stored type); prototype in `Steps/EvalMem.lean` (`TempTys`, `GoodT`, `goodT_push_mem`, `SimConclTT`, `eval_step_stmtT`, `RepackSound`, `return_member` proved, `app_mem` stated); concrete runs in `Regress/EvalMemRuns.lean` (`goodT_SB`, four typed runs, the untyped `let x = (0 : Unit)`).
- Open from D81: untyped runs already owe membership they cannot establish (route (A) vs (B)); whether a borrow is ever held untyped in an untyped run (measure); strict meanings decide pmem vs HWT.

## In flight
- Waiting on the orchestrator: decision on where the type lives; the fixed-decision-table change landing on `spine` before `Statements.lean` is touched.
- Second job: `Ochr/Meaning/OPEN.md` inventory (not started).

## Do not touch (other lanes)
- `Steps/Statements.lean` and every existing file under `Steps/` until the orchestrator says the fixed-decision-table change is on `spine`.
- `Steps/DropOne*`, `MovedPlace*`, `JoinNoop*`, `Slice/*` (slice prover); `Sem`, `Pi`, `Data`, `DataLib/*`, `DataModel/*`, `Closure*`, `Places` (data layer); `Rules/*` (trial).

## Traps
- The checker's accesses (`firstLiveLoanOnPath`) are well-founded recursion: `decide +kernel`/`rfl` do not reduce a run that reads a place; use `#guard` on a Bool fingerprint (as `Regress/StaticLend`).
- `set_option … in` goes before a docstring, not between it and its `def`.
- A refutation of a fuel-indexed statement must use the statement's own fuel in the `Runs` (a mismatch sends `whnf` into the machine and times out).
- `Ochr/Meaning.lean` (the library root) is shared; add imports next to a related line to limit conflicts.
