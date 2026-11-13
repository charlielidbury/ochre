import Ochr.Meaning.Places
import Ochr.Decide

/-!
# The checker's decisions as the run's (`Decisions` instantiated by `Decide.lean`)

`Decisions` (`Places.lean`) is what the reference run reads from syntax and declared types:
whether a call is a statement, the declared readings of places and terms, copy or move, a
Π-term's sort, and D84's drop at the join. Here each field is the checker's own function, called
as `Machine.lean` calls it, so "aligned" is true by construction up to the gaps listed below.
The step lemmas need to know these gaps.

## How a decision is read

The checker's decisions are `M` computations. They read the state's tables (`globals`, `inds`,
Δ = `absTy`, the pure caches `constDecls` and `classCache`) and the declared readings of the top
frame's bindings (`liveDecl`, under `withLive true`). They never read a value, a stored type or a
run (`ochr/core/CLAUDE.md`, "Decisions never read a run"; `Decide.lean` does not import the
machine). The run has the readings (`scopeOf`: the top frame's `SBinding.decl`s, innermost first)
and no `MState`. So the instance is parameterised by the checker state `st` whose tables the
decisions read, and it reads a decision in `scopeState st sc`: `st` with its frames replaced by
one frame whose bindings carry exactly the readings `sc`. Each field then runs the checker's call
as the machine makes it (`withLive true (… [] …)`) in that state.
* What the step lemmas need: at the checker's state `st'`, a decision equals the one in
  `scopeState st' (top frame's readings)`. Decisions read the frames only through `liveDecl`. And
  `st'` agrees with the `st` the instance was built at on what decisions read: Σ is fixed during
  an item's check, Δ only grows, and the caches are consistent.
* `fuel`: every decision recurses on fuel and is `exhausted` when it runs out. The instance's fuel
  must be at least the checker's (2000000 for `checkDefs`' default); then, by fuel monotonicity
  (`Consistency.lean`, obstacle 2, not proved), its reading is the checker's. Decisions never
  `tick`, so the `runMachine` fuel layer is unused.
* A decision that fails (`err`, or exhaustion) reads a default (`readDecision`). No accepted check
  meets one: `Fail.error` is never caught below the verdict boundary (`Catch.lean`), and
  decisions are never stuck. So the defaults are immaterial and chosen as the readers' own
  "nothing known" values.

## Fields, and where they do not match (reported to the spine)

* `flags`: `Machine.evalAt`'s pre-pass, `preFlags t (declOf … t)` (`none`, the reading `any`, is
  "not erased"). Exact for a term the machine classifies itself. Since D19 the run asks `flags`
  of every term whose clause can change the state or return a label (`SM.stmtIf`), as `evalAt`
  classifies every term but an embedded value. Two notes on the run's side. A `let`'s or `seq`'s
  tail is classified by its parent's reading (`tailDecl`), which equals its own reading by
  `declOf`'s `letIn`/`seq` clauses whenever `refineDecl` is the identity. A call's head is not
  classified by the machine (`headEval`); the run reads a place head in place (`SM.headOf`) and
  asks `flags` of any other head, which agrees wherever a head that is a statement makes its call
  one.
* `placeDecl`, `declOf`: `withLive true (placeDecl fuel [] p)` (`Machine.copyRead`) and
  `withLive true (declOf fuel false [] [] u)` (`evalAt`, `letIn`). Exact.
* `copy`: `declCopy fuel r` (`copyRead`). Exact.
* `piSort`: **mismatch, recorded as a lemma obligation** (docs/31's implementer ledger; the spine's
  decision, not a checker change). No checker function takes a scope and a Π-*term*. The machine's
  decision is `Decide.sortOf (tPi cs t' rd)` on the *captured* Π-value (`evalCore`'s `.pi` clause,
  after `capture`; in typing `Machine.piSort` runs the types and is asserted equal). `sortOf` reads
  the capture scope from the captured values (`valueDecl`), not from the bindings' readings, which
  `capture` records in `rd` and `sortOf` ignores. The instance is
  `withLive true (sortOf fuel (.tPi [] t []))`, with the bindings' readings as scope, so it
  differs exactly there. The obligation: `valueDecl` of a captured value agrees with its
  binding's reading wherever `declSort` and `typeDecl` read it.
  Separately, a checker bug (relayed to the lead): `sortOf` reads a Π-term domain or codomain
  through `declSort → declOf false`, where `typePos` answers 1 without `chk`. Two consequences:
  - `Π(f : Π(x : Nat). Prop). Nat` has declared sort 1 but computed sort 2, and
    `Π(x : Nat). Π(y : Nat). Eq(Nat, y, y)` has declared sort 1 but computed sort 0. Both are
    rejected in typing by the INTERNAL [D55] assertion.
  - Stored as a global's type, which no assertion checks, both pass D66's `isBorrowable`.
  The instance reproduces it (`piSort_nested`).
* `joinMoves`: **a parameter** until D84's `Decide.jdMoves` (branch `d84`, not on spine's base)
  lands. Its second argument is the set of places already `⊥` at the match. The run passes
  `movedPlaces φ s`, the top frame's variables holding `moved`. On `d84`, `Machine.staticJoin`
  calls `withLive true (jdMoves fuel [] [] t entry)` with `entry` = `botPlaces` of the frame's
  values, which includes sub-places with `⊥` inside a value: the run's whole-variable set is a
  documented gap for those. Once `jdMoves` lands, the field is
  `fun sc entry t => readDecision (scopeState st sc) fuel [] (withLive true (jdMoves fuel [] [] t entry))`.
-/

namespace Ochr.Meaning

/-- The checker state a decision is read in: `st`'s tables, with its frames replaced by one frame
whose bindings carry the readings `sc` (innermost first, `scopeOf`'s order; `liveDecl` reads the
last binding as variable 0) and nothing else: `⊥` with no stored type, the checker's own unknown
slot (`Binding.ty`). -/
def scopeState (st : MState) (sc : List DeclInfo) : MState :=
  { st with env := #[{ binds := (sc.reverse.map fun d =>
      ({ hint := ⟨"_"⟩, ty := none, val := .bot, decl := d } : Binding)).toArray }] }

/-- Run a decision in `st` with `fuel`: its answer, or `dflt` where it fails or runs out (which no
accepted check meets). -/
def readDecision {α : Type} (st : MState) (fuel : Nat) (dflt : α) (x : M α) : α :=
  match (runMachine x st fuel).1 with
  | .ok a _ => a
  | _ => dflt

/-- The checker's decisions at the tables of `st`, each read as `Machine.lean` calls it; D84's
`joinMoves` is `Decide.jdMoves` as `staticJoin` calls it, and `rePointed` is `Decide.typeState`'s
`repointed` as `idType` reads it. See the module docstring for the one mismatch (`piSort`). -/
def checkerDecisions (st : MState) (fuel : Nat) : Decisions where
  -- `Machine.evalAt`: `withLive true (declOf … t)`, then `preFlags`; `none` is "not erased"
  flags sc t := readDecision (scopeState st sc) fuel (false, false) do
    let d ← withLive true (Ochr.declOf fuel false [] [] t)
    pure ((← preFlags t d).getD (false, false))
  -- `Machine.copyRead`'s reading
  placeDecl sc p := readDecision (scopeState st sc) fuel .other (withLive true (Ochr.placeDecl fuel [] p))
  -- `Machine.evalAt` and `letIn`'s reading
  declOf sc t := readDecision (scopeState st sc) fuel .other (withLive true (Ochr.declOf fuel false [] [] t))
  -- `Machine.copyRead`'s test (no scope: `declCopy` reads closed field types)
  copy r := readDecision (scopeState st []) fuel false (declCopy fuel r)
  -- `Decide.sortOf` on the uncaptured Π-term, the scope the bindings' readings (the mismatch)
  piSort sc t := readDecision (scopeState st sc) fuel 1 (withLive true (sortOf fuel (.tPi [] t [])))
  -- `Machine.staticJoin`: D84's [Join] set, from the match term and the places already `⊥`
  joinMoves sc entry t := readDecision (scopeState st sc) fuel entry (withLive true (jdMoves fuel [] [] t entry))
  -- `Machine.idType`: [Id-typestate]'s re-pointed component ([Obs-ref]'s set)
  rePointed sc t := readDecision (scopeState st sc) fuel [] (do pure (← withLive true (typeState fuel t)).repointed)
  -- `Decide.typeDecl`, the reading of a type term, with the scope as the live frame (as
  -- `Decide.telescope` reads a parameter's type in the scope of the earlier ones)
  typeDecl sc T := readDecision (scopeState st sc) fuel .other (withLive true (Ochr.typeDecl fuel false [] [] T))

/-! ## Sanity: the fields compute (by the kernel, at any tables `st`) -/

namespace DecisionsSanity

variable (st : MState) (jm : List DeclInfo → List Place → Term → List Place)

/-- `Unit` is a copy type (D80, P3). -/
theorem copy_unit : (checkerDecisions st 10).copy .unit = true := rfl

/-- A variable reads its binding's reading, innermost first; a variable beyond the scope reads
`other`, as `liveDecl` does beyond the frame. -/
theorem placeDecl_var : (checkerDecisions st 10).placeDecl [.unit, .other] (.var 0) = .unit := rfl

theorem placeDecl_var_outer : (checkerDecisions st 10).placeDecl [.unit, .ind "Pair" []] (.var 1) =
    .ind "Pair" [] := rfl

theorem placeDecl_beyond : (checkerDecisions st 10).placeDecl [.unit, .other] (.var 5) = .other := rfl

theorem declOf_var : (checkerDecisions st 10).declOf [.unit] (.place (.var 0)) = .unit := rfl

/-- A call through a variable whose reading returns types is erased and not a proof (D35). -/
theorem flags_typeCall :
    (checkerDecisions st 10).flags [.pi (.sort 1)] (.call (.place (.var 0)) [.zero] false) = (true, false) :=
  rfl

/-- A call through a variable whose reading returns data runs. -/
theorem flags_dataCall :
    (checkerDecisions st 10).flags [.pi .other] (.call (.place (.var 0)) [.zero] false) = (false, false) :=
  rfl

/-- `Π(x : Nat). Eq(Nat, x, x)` is a proposition (impredicative `Prop`). -/
theorem piSort_prop :
    (checkerDecisions st 10).piSort [] (.pi [⟨"x"⟩] [.nat] (.eq .nat (.place (.var 0)) (.place (.var 0)))) = 0 :=
  rfl

/-- `Π(x : Nat). Nat` is in `Type₀`. -/
theorem piSort_data : (checkerDecisions st 10).piSort [] (.pi [⟨"x"⟩] [.nat] .nat) = 1 := rfl

/-- `Π(x : Nat). Prop` is in `Type₁` (`Pow`'s sort). -/
theorem piSort_pow : (checkerDecisions st 10).piSort [] (.pi [⟨"x"⟩] [.nat] (.sort 0)) = 2 := rfl

/-- A domain read off the scope: `Π(y : A). Nat` with `A : Type₁` in scope is in `Type₁`. -/
theorem piSort_scope : (checkerDecisions st 10).piSort [.sort 2] (.pi [⟨"y"⟩] [.place (.var 0)] .nat) = 2 :=
  rfl

/-- `Π(f : Π(x : Nat). Prop). Nat` has a domain in `Type₁`, so it is in `Type₁` (the instance used
to reproduce a checker bug here: `Decide.sortOf` said `Type₀`, its `declSort` reading the Π-term
domain through `declOf false`; D86 on main reads a Π-term's declared sort in every mode, so the
instance now agrees with `Machine.piSort`). -/
theorem piSort_nested :
    (checkerDecisions st 10).piSort [] (.pi [⟨"f"⟩] [.pi [⟨"x"⟩] [.nat] (.sort 0)] .nat) = 2 := rfl

/-- D19, R3: a parameter declared `Unit` reads as `Unit`, a copy type; a function's parameters
and codomain read their type terms (`Decide.paramDecls`), each in the scope of the earlier ones. -/
theorem typeDecl_unit : (checkerDecisions st 10).typeDecl [] .unit = .unit := rfl

theorem fixDecls_unit_unit : (checkerDecisions st 10).fixDecls [] [.unit] .unit = ([.unit], .unit) := rfl

/-- So a read of a `Unit` parameter is a copy (`CopyParam (u : Unit) : Unit × Unit := (u, u)`). -/
theorem copy_unit_param :
    (checkerDecisions st 10).copy ((checkerDecisions st 10).placeDecl
      (((checkerDecisions st 10).fixDecls [] [.unit] .unit).1.getD 0 .other :: []) (.var 0)) = true := rfl

/-- A parameter that is a function into `Prop` reads as one, so a call through it is a proof. -/
theorem fixDecls_lemma_param :
    ((checkerDecisions st 10).fixDecls [] [.pi [⟨"n"⟩] [.nat] (.eq .nat (.place (.var 0)) (.place (.var 0)))] .unit).1
      = [.pi .prop] := rfl

end DecisionsSanity

end Ochr.Meaning
