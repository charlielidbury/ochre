# Machine lane: working note (keep current; a successor continues from this alone)

Worktree `/home/charlielidbury/repos/ochre-machine`, branch `spine-machine` (push there; never `spine`
or `main`). Lean project `ochr/core/lean`; build `taskset -c 0-14 lake build <Module>`, and
`taskset -c 0-14 lake build OchrMeaning` before each push. Report to `main` by SendMessage, then end
the turn. Owned files: `Steps/MachineMono.lean`, everything under `Steps/Machine/`. Never edit the
checker or other files.

## What is proved (standard axioms only: `propext`, `Classical.choice`, `Quot.sound`)

The property is `GrowsIn tb x` (`GrowsIn.lean`): every successful run of `x` from a state whose
globals and declarations are `tb` only extends the tables (`TablesGrow`, `Defs.lean`). It is relative
to `tb` because a private copy's exit (`restoreKeep saved`, `exitWorld w`) takes the globals and the
declarations from the saved state, which keeps them only if the saved state had them: true when it
was read earlier in the same run (`get`, `enterWorld` give `OnTab tb s` for what they read).
`GrowsM x ↔ ∀ tb, GrowsIn tb x` (`growsM_of_growsIn`, `growsIn_of_growsM`, `GrowsIn.runs`).

- `Comb.lean`: the monad's combinators (bind, pure, get, modify, ite, loops over lists/arrays/ranges,
  `mapM`, `anyM`, `foldlM`, `onFail`, `tryCatch`, `catchStuck`, `locateErrors`, `tick`, the log),
  the brackets (`withLive`, `withErased`, `withRuntime`, `withCopying`, `privately`,
  `inStatement`, `restoreKeep`, `enterWorld`/`inWorld`/`exitWorld`), `freshAbs`, `freshLoan`;
  `GrowsAt s x` (runs from one known state) for read-then-write-back code; `growsIn_get_restore`
  (read `cur`, anything, write `cur` back: `closeBlock`'s `set e … set cur`).
- `EnvLeaves`, `DecideLeaves`, `MachineLeaves`: every function outside the machine's mutual block
  that it calls (Env, Rules, Located, Obs, Decide, Machine before the block). Decide functions
  covered by `Slice.decideKeep` keep the state; the others, and `jdMoves`/`jdAssigns`, by their own
  inductions. `recCheck` and `located` (read, keep, write back) by `GrowsAt`.
- `IH.lean`: `MachineGrows tb nf`, one field per function of the mutual block (113; `joinLogged`,
  which takes no fuel, separately), each `∀ args, GrowsIn tb (f nf args)`; a function taking a
  computation assumes it of it; `joinContRet` says `joinCont` returns a growing continuation
  (`RetOk`, used through `growsIn_bind_ret`).
- `Zero.lean` (all at fuel 0), `Step*.lean` (each at `nf + 1` from the hypothesis at `nf`),
  `All.lean`: `machineGrows : ∀ nf, MachineGrows tb nf`.
- `MachineMono.lean`'s statements are proved from these, except the two below that are false.
- `False.lean`: `not_grows_restoreKeep` (kernel-checked).
- Decisions agree across fuels (`FuelDefs.lean`, `DecideFuel.lean`): `FuelLe x y` (every success of
  `x` is one of `y`, same value and final state, from any budget and log: the decision procedures
  never touch the budget or the log); each function of Decide's block at `n` is `FuelLe` itself at
  `n + 1` (`decideFuelLe`, `jdFuelLe`, `jaFuelLe`, `fuelLe_typeState`; macro tactics `fuel_go`,
  `fuel_ih` in DecideScope's style, both sides walked in step); `FuelAgree`/`FuelMono` for each
  field of `Decisions` as `checkerDecisions₀` reads it (`fuelAgree_flags`, …, `_typeDecl`). Not
  `blockCaps` (`ckBlockCaps` runs the machine: a whole-block fuel induction, blocked by the `while`).
- `MachineMono.restoreKeep_grows`: the corrected `grows_restoreKeep` (hypothesis `TablesGrow saved cur`).
  `eq_step_asm` goes through with it (checked on a scratch copy; the replacement is a forward chain of
  `TablesGrow` along the run, then the `back`s).

## Open (all inside the induction, in `StepPending.lean`)

- `step_blockCaptures`: its K1(g) loop is a `while`. `while` is `Loop.forIn` = `repeatM`,
  `@[implemented_by]` over a `partial def`; a run that never ends has an unspecified value (a fixed
  point chosen by `Classical.choice`), so nothing is provable without the loop ending from every
  state. Options: the checker bounds it by the fuel (recommended; also the standard "no
  implemented_by in checker code"), or a termination proof (each pass replaces a place by its
  fields, whose contents are strict sub-values; measure Σ 2^size(content); the unfolding is
  `Lean.Loop.forIn_eq_of_monadTail`, which needs a `MonadTail M` instance, hence `Nonempty Fuel`).
- the comparison (`conv`, `convList`, `convTList`, `convPi`, `convT`, `convFn`, `convFnRun`) and
  `dropAtJoin`: held until main's changes to them land (main's instruction).

## False as written (reported to main)

- `grows_restoreKeep saved` (counterexample `False.not_grows_restoreKeep`); corrected
  `restoreKeep_grows` (the saved state has the current globals and declarations). Used by
  `EqJAsm.eq_step_asm`.
- `grows_closeBlock` with no hypothesis on the arms (an arm that lowers the frozen readings leaves
  them lowered: `exitWorld` keeps the arm's `absDecl`); corrected `grows_closeBlock_of`. No kernel
  counterexample: every run of `closeBlock` goes through the `while` loop, which the kernel cannot
  evaluate.

## The tactic (`Tactic.lean`) and its idioms

`grows_go` / `grows_go ih` walks a `GrowsIn` goal by the head constant of the computation, never by
unfolding (`with_reducible` unification throughout): `@[grows]` lemmas indexed by head (`Attr.lean`,
an env extension; the last registered is tried first), the field of `ih` named after the function,
a local hypothesis (binders, `have`s and `∧` opened), a match on a constructor reduced
(`reduceMatcher?`, which is how the fuel's `n + 1` match goes) or else `split` (then
`fuelCleanup` substitutes `n + 1 = k + 1` and closes `0 = k + 1`), `∀ a ∈ [..]/map/[]` rewritten
elementwise, a projection of a constructor reduced, a refuted case of a functional induction closed
(`growsAbsurd`). It never fails: open goals are left for the caller.

Traps:
- `grows_go ih` takes the identifier only on the same line (`colGt`), or a following `all_goals`
  would be read as the identifier.
- Equation lemmas of `evalType` and `observe` (fuel match under `inStatement`) time out when
  generated (realized with the default heartbeats, which `set_option` does not reach): state the
  `n + 1` unfolding yourself and prove it by `rfl` (`evalType_succ`, `observe_succ`).
- `step_callFn` needs `maxHeartbeats 2000000` (about 90 s).
- `lean_run_code` (the MCP) runs in ANOTHER worktree (`ochre-exists`): test in a scratch module of
  this worktree with `lake env lean` instead (`Scratch.lean`, never committed).
- Value-recursive functions: `f.mutual_induct` (or `f.induct` when only one motive concludes);
  fuel-recursive: plain induction on the fuel with the hypothesis as a structure (`JdGrows`,
  `LendGrows`).
- Loops whose body may only run at the list's elements: `growsIn_forIn_list_mem` (registered).

## Next

1. main's answers: the `while` loop (checker change or termination proof); go-ahead for the
   comparison and `dropAtJoin` (generate their steps with the script pattern of `Step*.lean`:
   `unfold Ochr.f; grows_go ih`).
2. `DecTab.back`.
3. The closing comment's other machine-only facts.
