# Machine lane: working note (keep current; a successor continues from this alone)

Worktree `/home/charlielidbury/repos/ochre-machine`, branch `spine-machine` (push there; never `spine`
or `main`). Lean project `ochr/core/lean`; build `taskset -c 0-14 lake build <Module>` (long builds in
the background), and `taskset -c 0-14 lake build OchrMeaning` before each push. Report to the lead
(`main`) by SendMessage, then end the turn. Owned: `Steps/MachineMono.lean`, everything under
`Steps/Machine/`. Never edit the checker or other files (to check a consumer, copy it into a scratch
module here, build that, delete it).

STATUS LINE: see "Build state" at the end (kept current at every push).

## What is proved (standard axioms only: `propext`, `Classical.choice`, `Quot.sound`)

### (a) The tables only grow (`grows_*`)

The property is `GrowsIn tb x` (`GrowsIn.lean`): every successful run of `x` from a state whose
globals and declarations are `tb` only extends the tables (`TablesGrow`, `Defs.lean`). Relative to
`tb` because a private copy's exit (`restoreKeep saved`, `exitWorld w`) takes the globals and the
declarations from the saved state, which keeps them only if the saved state had them: true when it
was read earlier in the same run (`get`, `enterWorld` give `OnTab tb s`).
`GrowsM x ↔ ∀ tb, GrowsIn tb x` (`growsM_of_growsIn`, `growsIn_of_growsM`, `GrowsIn.runs`).

- `Comb.lean`: the monad's combinators, Env's brackets (`withLive`, `withErased`, `withRuntime`,
  `withCopying`, `privately`, `inStatement`, `restoreKeep`, worlds), `freshAbs`, `freshLoan`;
  `GrowsAt s x` for read-then-write-back code; `growsIn_get_restore` (`closeBlock`'s `set e … set cur`).
- `EnvLeaves`, `DecideLeaves`, `MachineLeaves`: every function outside the machine's mutual block
  that the block calls.
- `IH.lean`: `MachineGrows tb nf`, one field per function of the block (generated; functions taking
  no fuel, `joinLogged` and `lentInFields`, proved on their own); `joinContRet` (`RetOk`).
- `Zero.lean`, `Step*.lean`, `All.lean`: `machineGrows : ∀ nf, MachineGrows tb nf`.
- The files `IH`'s fields, `Zero`, `Step*` and `All`'s two structure instances are GENERATED from
  `Machine.lean`'s signatures by the scratchpad scripts `gen.py`/`gen2.py`/`regen.py` (described under
  "Regenerating" below); hand edits in them are `evalType_succ`, `observe_succ` (the `n + 1`
  unfolding by `rfl`: those two functions' equation lemmas time out when generated) and the
  heartbeats of `step_callFn`.
- `MachineMono.lean`'s `grows_*` follow from these; `restoreKeep_grows` is the corrected
  `grows_restoreKeep` (hypothesis `TablesGrow saved cur`); `grows_closeBlock_of` the corrected
  `grows_closeBlock` (hypothesis: every arm grows). The two false ones stay, flagged, until
  `EqJAsm` moves (`False.lean` has `not_grows_restoreKeep`; `eq_step_asm` goes through with
  `restoreKeep_grows`, checked on a scratch copy: a forward chain of `TablesGrow` along the run,
  then the same `back`s; `J_split` must give the arm's growth for `grows_closeBlock_of`).

### Decisions agree across fuels (`FuelDefs.lean`, `DecideFuel.lean`)

`FuelLe x y`: every success of `x` is one of `y` (same value and final state) from the same state and
ANY budget and log (the decision procedures never touch either). Each function of Decide's block the
decisions reach is `FuelLe` itself one fuel up (`decideFuelLe`, `jdFuelLe`, `jaFuelLe`,
`fuelLe_typeState`; macro tactics `fuel_go`, `fuel_ih`, both bodies walked in step). Hence
`FuelAgree`/`FuelMono` for each field of `Decisions` as `checkerDecisions₀` and `DecTab` read it
(`fuelAgree_flags`, `_placeDecl`, `_declOf`, `_copy`, `_piSort`, `_joinMoves`, `_rePointed`,
`_typeState`, `_typeDecl`). `DecisionsFF.decide_fuel_agree` (a `sorry` on `spine`) is proved in its
own form as `decide_fuel_agree'` (`DecideFuelFF.lean`); `DecisionsFF` imports only `Statements`, so it
can import `DecideFuel` and take that proof term verbatim. NOT the block captures (`ckBlockCaps` runs the machine: a fuel induction over the
whole block, the same shape as (a) but relational; see the queue).

## Non-total constructs in the checker (read-only census, 2026-11-21, at the merge with spine 1e226c6a)

Reachable from `checkProgram`: `Loc.termAddr` (`opaque`/`implemented_by`, the standard's one allowed
exception); well-founded recursion, total but not kernel-reducible: `Machine.firstLiveLoanOnPath`
(Machine.lean:76), `Obs.owners` (Obs.lean:175), `Loc.Locs.relocate` (Loc.lean:113). None blocks this
lane's proofs (the tactic treats pure functions as values); they block only kernel evaluation of
concrete runs (`decide +kernel` counterexamples through an access or an end). No `while`/`repeat`
remains (`blockCaptures`' loop is fuel-bounded since D104). Not reachable from `checkProgram`: the
`ochr` command's elaborator (`Notation.lean`: nine `partial def`s, `evalBlock` `unsafe`/
`implemented_by`/`opaque`), `RuleGuard.lean` (three `partial def`s, build-time tooling), `Run.lean`'s
`exportsWith`/`libWith` (WF; they assemble a block's library before it is checked, outside `checkProgram`), `Consistency.holeIn` (WF; the statement side).

## The tactic (`Tactic.lean`) and its idioms

`grows_go` / `grows_go ih` walks a `GrowsIn` goal by the head constant of each sub-computation, never
by unfolding: `@[grows]` lemmas indexed by head (`Attr.lean`; the last registered is tried first), the
field of `ih` named after the function, a local hypothesis (binders, `have`s and `∧` opened), a match
on a constructor reduced (`reduceMatcher?`: the fuel's `n + 1`) or else `split` (then `fuelCleanup`),
`∀ a ∈ [..]/map/[]` elementwise, a projection of a constructor reduced, a refuted case of a functional
induction closed (`growsAbsurd`), `bind` of a function returning a computation through the `…Ret`
field (`growsIn_bind_ret`). It never fails; open goals are left for the caller.

Traps: `grows_go ih` takes the identifier on the same line only (`colGt`). `lean_run_code` (the MCP)
runs in ANOTHER worktree: test in a scratch module here with `lake env lean`. Value-recursive
functions: `f.mutual_induct` (or `f.induct`). `while` loops are `repeatM` (opaque: unprovable); the
checker's one `while` is gone (D104's fuel-bounded loop in `blockCaptures`).

## Regenerating after a checker change

The scripts are in `gen/`; run them from an empty scratch directory, in order: `python3 gen.py &&
python3 gen2.py && python3 regen.py`. `gen.py` (reads `Machine.lean`'s mutual block, found as the
`mutual` after line 700 and the last column-0 `end`; writes `sigs.json`), `gen2.py` (writes `fields.lean`, the IH's
fields, and `stubs.json`, each step's and base's text; `HYP` lists the hypotheses of functions taking
a computation), `regen.py` (writes the `Step*` files grouped as listed, `Zero.lean`, `All.lean`'s two
instances, re-applying the hand edits). Then paste `fields.lean` into `IH.lean`'s structure. If the
scripts are lost: each step is `intro …; unfold Ochr.f; grows_go ih`, each base `unfold Ochr.f; grows_go`.

## The queue (the lead's, 2026-11-21) and how each would be stated

1. Close the induction: every step on the merged checker (see Build state).
2. `DecTab.back` (`MachineMono`): a ONE-WAY simulation of the decision procedures from a state to one
   whose tables extend it (old frozen readings equal, globals and declarations equal):
   `SimFwd R x` = every success from `s₁` is a success from `s₂` with the same value, `R` after.
   `DecideScope.Sim` needs both runs to end alike, so it does not fit; the `FuelLe` closure lemmas
   are the template (same shape: success transfers one way). Moderate: a re-run of the
   seventeen-function induction with `absReading` the one place the relation matters.
3. The five facts lead7 needs (statements proposed; none written yet):
   - (M-a) data writes have no live loan or mark on their path. Not a property of one function: a
     trace property of `setPlace`'s call sites. Proposed form: each split lemma of a writing rule
     (`assign_split` and the like, which expose the state before the write) gains a conjunct
     `firstLiveLoanOnPath st₁.env (valAt st₁.env pos) ss = none` at that state, proved from
     `accessPath`'s postcondition (it loops until that is `none`: easy) plus "nothing between the
     access and the write puts a live loan on the path" (per site; the risky part). Exclude the
     join's mark write by name. The data writes (at the merge with spine 1e226c6a): `openWrite`
     (`setPlace fp .bot`), `readPlace` (two moves), `borrowPlace` (`setPlace p (.loan l)`),
     `assignPlace`, `capture` (a move into a closure), `dropAtJoin`; the mark write is `joinEnds`'
     `setPlace q (lentTo [k] w)`. MEDIUM, per site.
   - (M-b) CORRECTED (holds only outside private copies: `endTopLoan`'s D106 check is skipped at
     `privateDepth > 0`): `Runs (accessPath fuel p) st b () st' → st.privateDepth = 0 →
     findBorrow st.env l = some (.temp f i) → findBorrow st'.env l = some (.temp f i)`, the same for
     `accessInside` and `accessNeutralHead` (an access pushes and pops no temporary and does not
     change `privateDepth`). Needs "`endBorrow` of one label leaves every other borrow where it is"
     (`setAt` of the holder, `substEnv` of the loan, `lendEnv` of marks; `substEnv` re-normalises
     sealed programs, which hold no borrows). MEDIUM.
   - (M-c) `endBorrow` succeeds on `l` only if the content is whole and repacked: `Runs (endBorrow
     (fuel+1) l) st b () st' → findBorrow st.env l = some p → (valAt st.env p).takeBorrow l = some (c,
     rest) → c.hasHole = false ∧ (st.typing → valAt is a borrow → tyAt p = some (.tRef A) → ∃ run of
     repackCheck fuel "a borrow of it ends" c A from st)`. EASY (inversion of one body; `hasHole` is
     "has `⊥`").
   - (8a) CORRECTED (as worded it is too weak: a decision about `.const n` reads `n`'s stored type, a
     value that can mention other globals (`gfn m`, through `valueDecl`/`closedTypeDecl`), and a term
     can hold unknowns (`Term.val`) read by their frozen readings). Form the chain needs: `st₂`
     extends `st₁` (equal `inds`; `st₁.globals` a prefix of `st₂.globals`, or `find?` equal at every
     name `st₁` has; `st₁.absDecl` a prefix of `st₂.absDecl`), and every global name `t` mentions is
     one of `st₁` (an unknown name reads `.any` at `st₁` but may resolve at `st₂`); then for every
     scope and field, `chainDecisions fuel st₁` and `chainDecisions fuel st₂` agree on `t` and on its
     subterms. The closure under the globals' stored types then comes for free (a global of `st₁`
     was checked at `st₁`, so its type's names are `st₁`'s; that is a separate machine fact about
     `checkItem`, the same shape as (8b)). Proof: the one-way simulation of `DecTab.back` with this
     relation, then `decide_fuel_agree'` to move from fixed fuels to the table. HARD.
   - (8b) `checkItem (.ind d)` ok ⇒ every global name in `d`'s parameter and field-type terms is a
     global: DOUBTFUL. It holds only if the checker looks up every such name. `checkInd` runs
     `telescope … true` over the parameters and `typePos … true` over every field type, but Decide's
     readers answer `.any` for an unknown constant (`declOf`'s `.const` case: "an unknown name is the
     machine's error, reported where it is met"), so only evaluation finds one. It evaluates the
     parameter types and the field types at generic values, and a Π-type's codomain is evaluated too
     (`piSort` runs `evalType c` at generic arguments); but evaluation need not reach every subterm
     (an arm a match on a known constructor does not take, a λ's body), so a name there may never be
     looked up. Measurement first (sweep, report clause): at every accepted `ind` item, every
     constant of its parameter and field-type terms is a global of the state; and a probe that hides
     an unknown name where evaluation does not reach it, e.g. inside a λ passed as a value parameter
     of a type former in a field type (`D(λy. NoSuchName)`, `D` with a function-typed parameter: the
     λ is captured, its body not run). If the probe is accepted, (8b) is false and the checker
     change I would propose is a syntactic check in [Ind-decl] (and [Def]): every constant a
     declaration's parameter and field-type terms mention is declared (a scan of the terms against
     `globals`, read from syntax, so it is a decision of the kind the checker's standard allows);
     then (8b) is that check's postcondition. HARD only if the measurement fails and the change is
     refused.
4. The rest of `Meaning/OPEN.md`'s machine-only section (an access losing no unknown; the resolution
   facts; the well-formedness preservation statements, `borrow_wf` suspected false).

## Build state

2026-11-21, `spine-machine` after merging `spine` 1e226c6a: the whole lane builds; `machineGrows` has NO
`sorry` (`#print axioms`: the three standard), all 118 steps proved on the merged checker (main's D102
to D114, the fuel-bounded loop and D103's `restoreNames` included); `decide_fuel_agree'` proved. What the
merge broke (repaired): five new block functions and ten changed signatures (regenerated), `pushTemp`'s
type and site (`notePush`), `located`'s split (`locatedCore`, `noteStateAt`), new leaves (`underProof`,
`neutralLookup`, `ctorNeedsCtx`, `inferFrom`, `inferablePos`, `fieldIsLeaf`, `restoreNames`, `lentInFields`),
a name clash (`paramDecls`), `evalCore`'s step now needs 4M heartbeats. D115 (to come on main) changes
`evalCall`, `callFn`, `runBodyCore`, `closeCall`, `evalCtor`, `joinEnds`: re-run the generator then.
