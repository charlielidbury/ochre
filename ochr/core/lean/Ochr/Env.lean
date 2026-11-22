import Ochr.Catch

/-!
# The environment Ω and the machine state

Ω is a stack of frames (RULES §2). A frame holds named bindings `x : A ↦ v` and
*temporaries*: values in flight during evaluation (an evaluated argument waiting for
the next one, the right-hand side of an assignment, a result while its frame is
popped). Temporaries are part of Ω so that [End] can find and substitute into them. Each
has a stored type, as a binding has (D104, `Frame.tempTys`), which the checker never reads.
-/

namespace Ochr

structure Binding where
  hint : Hint
  ty : Option Value     -- its declared type (D82); `none` only for an unknown slot (`⊥`) of a
                        -- checker-internal frame, which is never read
  val : Value
  proof : Bool := false -- v1.7 (D35): its declared type has declared sort Prop (read off syntax)
  decl : DeclInfo := .other   -- what its declared type says (the erasure pre-pass)
  cap : Bool := false         -- a closure's captured value (D53 (e): its body may not move it out)
  /-- D78 [Rec]: this binding names a function whose body is being checked: the
  `RecCtx.uid` of its frame. Set on the function's binding of itself, and on a closure's
  capture of such a binding, so a recursive call is recognised by the name it is made
  through (syntax), never by comparing function values, which a refinement, an [End] or
  a re-normalisation inside a capture can change (§6.3: which calls recurse is read from
  syntax). -/
  recUid : Option Nat := none
  /-- D82: a declared type evaluated only when it is read (lazily): `(Π, w̄, i)` says it is the
  `i`-th parameter type of the Π-type `Π` at the arguments `w̄` as they were passed, or, for `i`
  its number of parameters, its codomain there (a `let` bound to a call) (`Machine.bindTy?`). Its
  `ty` is `none` until then. A refinement reaches it as it reaches stored types (`mapState`). A
  borrow's type is never deferred: what decides on borrows reads `ty` directly. -/
  lazyTy : Option (Value × List Value × Nat) := none
deriving Inhabited

structure Frame where
  binds : Array Binding := #[]
  temps : Array Value := #[]
  /-- D104: each temporary's stored type, beside it (`tempTys[i]` is `temps[i]`'s): the type the
  machine had in hand when it pushed the value (the type its evaluation returned, or the declared
  type of the position it is headed for), `none` where it had none (an untyped run that computed
  none). The checker never reads it (`tyAt` of a temporary is `none`): it is kept so that every
  value the machine holds has a stored type, as a binding has, and the invariant of the
  consistency proof is a predicate on the checker's state alone. -/
  tempTys : Array (Option Value) := #[]
deriving Inhabited

abbrev Env := Array Frame

/-- A position in Ω. Ordered by frame, then bindings before temporaries. -/
inductive Pos where
  | bind (f i : Nat)
  | temp (f i : Nat)
deriving BEq, Inhabited, Repr

def Pos.key : Pos → Nat × Nat × Nat
  | .bind f i => (f, 0, i)
  | .temp f i => (f, 1, i)

def Pos.lt (a b : Pos) : Bool :=
  let (a1, a2, a3) := a.key
  let (b1, b2, b3) := b.key
  a1 < b1 || (a1 == b1 && (a2 < b2 || (a2 == b2 && a3 < b3)))

/-- A top-level definition. -/
structure GDef where
  name : String
  ty : Value            -- a `tPi [] (pi …)` for functions
  fn? : Option Term     -- the closed `fix` term of a function
  val : Value           -- `gfn name` for functions, the value otherwise
  model : Bool := false -- model code (K2/K3): `implemented by` (native), or a parameter or result of an
                        -- unsized type by value, so it never runs at runtime
  absTys : List (Nat × Value) := []  -- the abstract values `ty` and `val` mention, with their types:
                        -- a hole's value (docs/07) is an axiom of Σ, so it outlives the declaration
                        -- that made it (`Check.seedHoles`)
  absDecls : List (Nat × DeclInfo) := []  -- D96: ... and their frozen declared readings

/-- A declared inductive type (v2.0, D45/D46): uniform parameters (a telescope of type
terms, each in the scope of the earlier parameters), a sort (`0` = `Prop`, `1` = `Type₀`),
and zero or more constructors with named fields, whose types are terms in the scope of
the parameters (de Bruijn: the last parameter is `var 0`) and of the constructor's fields
(D64: field `j` of `k` is `var (np + k - 1 - j)`, after the parameters; [Ind] admits only
the earlier fields). -/
structure IndDecl where
  name : String
  params : List (Hint × Term) := []
  sort : Nat := 1
  ctors : List (String × List (String × Term)) := []
  copy : Bool := false    -- declared `copy` (D53): a cost-model statement, reads copy
  abstract : Bool := false  -- declared `abstract` (K3): its constructors, and matches on them, only in erased
                            -- positions and model code (`implemented by` bodies, model functions)
  unsized : Bool := false   -- declared `unsized` (K2): at runtime, outside model code, a place of this type is
                            -- only borrowed (never read, moved, assigned or matched)
  nestable : List Bool := [] -- D107: which parameters are nestable (`Check.nestableSet`), in declaration order;
                            -- computed from the fields and stored by [Ind-decl], empty until then
  declaring : Bool := false -- D107: the entry [Ind-decl] holds while checking this declaration's own fields, with no
                            -- constructors yet: they are not known, so a match with no arms on it is not vacuous
deriving Inhabited

/-- D107: the error of a term that reads the constructors of a type whose declaration is being
checked (a match on an earlier field of that type, with or without arms, a field projection of
it, one of its constructors, a split on it): while `D` is declared its entry has no constructors,
and a reader of the entry would answer as if `D` were empty (`W(let k : False = match b {}; k)`
with `b : D` was accepted). A decision that reads them and cannot reject answers conservatively
instead (`declCopy`, `largeElim`; η and the join's grain see no single constructor). -/
def IndDecl.declaringMsg (d : IndDecl) (what : String) : String :=
  s!"{what} reads the constructors of {d.name}, which are not known while {d.name} is declared (D107)"

/-- [Ind-decl] (D71, Fording): parameter `i` of `d` is a *type parameter* when its declared
type is syntactically a sort (`A : Type`, `P : Prop`); any other parameter (`n : Word`,
`a : A`) is a *value parameter*. In `D(ā)` and `C(ā; t̄)` an argument at a type parameter
stands in a type position, and one at a value parameter in an erased position, as `Eq`'s
sides do: it is any term, run on a private copy, whose declared type need not be a sort. -/
def IndDecl.paramIsType (d : IndDecl) (i : Nat) : Bool :=
  match d.params[i]? with
  | some (_, .sort _) => true
  | some _ => false
  | none => true

/-- D64: the fields of constructor `c` that the field type term `FT` mentions, as field
indices (read off the declaration). -/
def IndDecl.fieldRefs (d : IndDecl) (c : Nat) (FT : Term) : List Nat :=
  let np := d.params.length
  let k := ((d.ctors[c]?).map (·.2.length)).getD 0
  FT.freeVars.filterMap fun v => if np ≤ v && v < np + k then some (np + k - 1 - v) else none

/-- D64: the *index fields* of constructor `c`: the fields some later field's type mentions
(syntactic, read off the declaration). -/
def IndDecl.indexFields (d : IndDecl) (c : Nat) : List Nat :=
  let fs := ((d.ctors[c]?).map (·.2)).getD []
  (List.range fs.length).filter fun j => fs.any fun (_, FT) => (d.fieldRefs c FT).contains j

/-- D64: constructor `c` has a dependent field (a field whose type mentions an earlier one). -/
def IndDecl.dependent (d : IndDecl) (c : Nat) : Bool := !(d.indexFields c).isEmpty

/-- D64: field `i`'s declared type mentions an earlier field. -/
def IndDecl.fieldDependent (d : IndDecl) (c i : Nat) : Bool :=
  match (d.ctors[c]?).bind (·.2[i]?) with
  | some (_, FT) => !(d.fieldRefs c FT).isEmpty
  | none => false

/-- A function whose body is being checked, for [Rec]: its entry values and the
recursive positions that have survived its recursive calls so far. The candidates are
an accumulator: a state restore (a branch, a private copy) keeps them, matched to the
frame by `uid`, so no nested computation can reset or shift them (the recCands fix). -/
structure RecCtx where
  fn : Value
  entries : Array (Option Nat)   -- entry abstract value of each parameter (through the borrow)
  cands : List Nat               -- the positions that survive every recursive call so far
  uid : Nat                      -- identifies the frame across state restores
deriving Inhabited

/-- What a run records: `trace` and `derivation`, which never change a verdict. The checker
has no rule switches (D70): which rules it applies is internal, and a test says only whether a
program is accepted, rejected or runs to a given result. -/
structure Config where
  trace : Bool := false          -- record goals, splits and call types (for inspection)
  derivation : Bool := false     -- record every rule application, in the paper's names (`fire`, Rules.lean)
  /-- Dev tooling (`lake exe sweep`, `Sweep.lean`): in `located` mode, record the whole machine
  state at each located term, on entry and on a successful exit (`LogEntry.state`). Off by
  default, and off in every run that produces a verdict (the `ochr` command, the tests): it only
  adds log entries, which no decision reads. -/
  recordStates : Bool := false
  /-- Dev tooling (`lake exe sweep --pushes`): log each temporary pushed with no stored type in a
  typed run, or holding a borrow with none (`LogEntry.push`), at every call depth, which
  `recordStates` does not reach. Off in every run that produces a verdict; no decision reads it. -/
  recordPushes : Bool := false
  /-- Dev tooling (`lake exe sweep --deep`): log the whole machine state on entry to every
  evaluation and on its successful exit at every call depth above 0 (a callee's body, a sealed
  program's re-run), which `recordStates` does not reach (`LogEntry.deep`); outside private copies,
  and inside them too with `recordDeepPrivate`. Off in every run that produces a verdict; no
  decision reads it. -/
  recordDeep : Bool := false
  recordDeepPrivate : Bool := false
deriving Inhabited, Repr, BEq

/-- The universe a sort lives in: `Type_l : Type_{l+1}`, and `Prop : Type₁` beside `Type₀`
(D66, Coq's arrangement: `Type₀` holds only runtime types). Level `0` is `Prop`, `1` is `Type₀`. -/
def sortSucc (l : Nat) : Nat := if l == 0 then 2 else l + 1

structure MState where
  env : Env := #[{}]
  globals : List GDef := []
  inds : List IndDecl := []
  nextLoan : Nat := 0
  nextAbs : Nat := 0
  absTy : Array Value := #[]
  /-- D96: each abstract value's declared reading (what its type says, `Decide.valTypeDecl`),
  frozen when it is made: written once, never refined, so every decision about an unknown reads
  the same answer at every later point (the decision procedures never read `absTy`). -/
  absDecl : Array DeclInfo := #[]
  refs : List (Nat × Value) := []     -- [Split] refinements made so far: σ ↦ Z | S σ'
  etaRefs : List (Nat × Value) := []  -- D68: η-refinements of one-constructor abstract values (σ ↦ C(σ₁, …)), kept across private copies, so every copy names σ's fields alike, and scoped to the world that made them (`exitWorld`), since the fields' types are that world's
  goal : Option Value := none
  recStack : List RecCtx := []        -- the functions whose bodies enclose the current point (top first)
  nextRecUid : Nat := 0               -- fresh `RecCtx.uid`s (never reused)
  cfg : Config := {}
  lastErased : Bool := false          -- set by `eval`: was the term just evaluated erased (D28)?
  lastProof : Bool := false           -- ... and is it a proof (its declared type has sort Prop, D35)?
  convStack : List (Value × Value) := []  -- function pairs being compared observationally (D30)
  neutrals : List (Value × Nat) := []     -- [Split] generalisations: sealed program ↦ its σ (finding G1)
  depth : Nat := 0                        -- call depth (bounded, like fuel: the checker must terminate)
  placeLog : Array (Nat × Nat × Place × Bool) := #[]  -- D53: every move (true) and assignment (false), at its
                                          -- root binding's position (restored with the state)
  curDecl : Option DeclInfo := none        -- the pre-pass's reading of the term being evaluated
  tailDecl : Option DeclInfo := none       -- ... handed to its tail, whose reading it is (one-shot)
  liveScope : Bool := false               -- declared-type reading: variables beyond the local scope are the top frame's
  headEval : Bool := false                -- the next `eval` is of a call's head (not classified by the pre-pass)
  /-- Static ends, rule 2: the next `eval` is in tail position of the body being run (one-shot,
  consumed by `evalAt`), as `checkTail` recurses: a body, a `let`'s body, a sequence's tail, an
  arm of a match in tail position. A match there is split at the generic call, never closed off
  as a block, so it does not end what a block would. -/
  tailNext : Bool := false
  curTail : Bool := false                 -- ... and the term being evaluated is (read by `evalCore` first)
  /-- D82: the next `eval`'s context reads its type (one-shot, consumed by `evalAt`). An untyped
  run computes a term's type only then; typing always does. -/
  wantTy : Bool := false
  wantHere : Bool := false                -- D82: whether the term being evaluated must give its type
  /-- D82: the next `eval` is a `let`'s right-hand side call, whose binding takes its type lazily
  (one-shot, consumed by `evalAt`, D130) -/
  deferCallTy : Bool := false
  /-- D130: ... and the term being evaluated is (read by `evalCall`) -/
  deferHere : Bool := false
  /-- D82: the Π-type and arguments of the call just made, when its `let` defers its type (cleared
  when an evaluation starts, D130, so a run that makes no call leaves none) -/
  callTyLater : Option (Value × List Value) := none
  erasedDepth : Nat := 0                  -- D53: > 0 while evaluating an erased term, whose reads copy
  /-- > 0 inside a private copy (`inStatement`, `privately`): what the run does there is
  discarded with the copy, so [Frame]'s F4 check (`Machine.endTopLoan`) does not apply. -/
  privateDepth : Nat := 0
  inPlace : Bool := false                 -- D53: the next read is in place (a call's head, a block's read-only capture)
  modelDepth : Nat := 0                   -- K2/K3: > 0 inside model code, which never runs at runtime
  copying : Bool := false      -- inside `clone`/`peek`: reads copy (the explicit copy, not an erased-read mode)
  /-- D84 [Id-typestate], ending a borrow: while a side of `Id` runs, the frame the `Id` is formed in, how
  many bindings and temporaries it had then, and (D114) the positions of the borrow bindings the
  side consumes (its type-state's); a side may not end a borrow one of the others holds. A run
  from a fresh environment (a sealed program's re-run, a comparison) has none. -/
  obsFrame : Option (Nat × Nat × Nat × List Nat) := none
  typing : Bool := false                  -- the term being evaluated is part of the checked program (`eval true`),
                                          -- where D64's [Repack] points are checked
  locs : Locs := {}                       -- the editor: where the declaration's terms are (`located`)
  /-- D85: the run is the erased program's, a closed call of accepted code (`Ochr/Runtime.lean`,
  `runCall`, the one place that sets it), where `J` is its transported term ([J-run]). The checker
  never sets it: every state it starts from (`checkDefs`, `globalsAfterFrom`) has it off, so its
  runs, its untyped ones included (callee bodies, [Seal]'s re-runs, private copies), keep [J] and
  [J-stuck]. -/
  runtime : Bool := false
deriving Inhabited

/-- What the editor shows on hover at a located term, for one check of it (`Located.note`). -/
inductive Note where
  | value (v : Value) (T : Option Value) (pointsTo : List String)   -- its value and type; a borrow's lender
  | goal (G : Value)                                               -- the goal a tail term is checked against
  | expected (A : Value)                                           -- the type an argument is checked against
  | rule (name : String)                                           -- a rule applied here (`Rules.fire`)
  | hole (G : Value) (Ω : List (String × Option Value × Value))    -- a hole's goal, and Ω there

/-- An entry of the log: a trace line (`Config.trace`), or a note for the editor, at a source
range, with the [Split] refinements of the path it was made on, or (`Config.recordStates`, dev
tooling) the whole machine state at a located term: on entry to its evaluation (`exit = false`)
or as it leaves it, successfully (`exit = true`), with the term's value and the type its
evaluation returned, which the checker then holds in its monad and not in `st` (`flight`, for an
evaluated term; none for a tail term). -/
inductive LogEntry where
  | line (s : String)
  | note (l : Loc) (refs : List (Nat × Value)) (n : Note)
  | state (l : Loc) (exit : Bool) (flight : Option (Value × Option Value)) (st : MState)
  /-- Dev tooling (`Config.recordPushes`): a temporary pushed at the push site `site` with no stored
  type, in a typed run (`typing`) or holding a borrow, at call depth `depth`. -/
  | push (site : String) (typing : Bool) (v : Value) (depth : Nat)
  /-- Dev tooling (`Config.recordDeep`): the whole state on entry to an evaluation at call depth
  above 0 (`exit = false`), or as it leaves it successfully, with its value and type (`flight`). -/
  | deep (exit : Bool) (flight : Option (Value × Option Value)) (st : MState)

/-- The machine monad. The inner `StateM` holds the log (the trace, and the editor's notes),
which survives both state restores and errors (so a rejected definition still shows how far
it got). -/
abbrev M := StateT MState (ExceptT Fail (ExceptT Exhausted (StateT Fuel (StateM (Array LogEntry)))))

def err {α : Type} (msg : String) : M α := throw (.error msg)

/-- Stuck on a neutral (RULES §3 [Match]); the innermost enclosing call closes off. -/
def stuckNow {α : Type} : M α := throw (.stuck none)

/-- Stuck on a match whose scrutinee's content is the neutral `v` (D61: `split` follows
these to find what to split on). -/
def stuckOn {α : Type} (v : Value) : M α := throw (.stuck (some v))

/-- Out of fuel, or past a depth limit: a failure no handler below the verdict boundary catches
(`Ochr/Catch.lean`), so it is a rejection that says so, never a decision. -/
def exhausted {α : Type} (msg : String) : M α := throwThe Exhausted ⟨msg⟩

def tick : M Unit := do
  let f ← getThe Fuel
  if f.left == 0 then exhausted "out of fuel"
  modifyThe Fuel fun f => ⟨f.left - 1⟩

/-- How a run of the machine ended: a value (and the final state), a failure, or exhaustion
(the checker does not know). -/
inductive Outcome (α : Type) where
  | ok (a : α) (st : MState)
  | fail (f : Fail)
  | exhausted (msg : String)

/-- Run `x` from `st` with `fuel`: the outcome, the fuel left, and the log. The one place where
the layers of `M` are taken apart (the verdict boundary and the test harnesses use it). -/
def runMachine {α : Type} (x : M α) (st : MState) (fuel : Nat) : Outcome α × Nat × Array LogEntry :=
  let ((r, fl), log) := (((((x.run st).run).run).run ⟨fuel⟩).run #[])
  let o := match r with
    | .error e => Outcome.exhausted e.msg
    | .ok (.error f) => .fail f
    | .ok (.ok (a, st')) => .ok a st'
  (o, fl.left, log)

/-- Restore a saved state, keeping the [Rec] accumulators: each saved
[Rec] frame takes the candidates of the current frame with the same `uid`, if there is
one (a computation that replaced the stack, e.g. `sealedType`, cannot wipe them). -/
def restoreKeep (saved : MState) : M Unit :=
  modify fun cur =>
    let keepCands (fr : RecCtx) : RecCtx :=
      match cur.recStack.find? (·.uid == fr.uid) with
      | some c => { fr with cands := c.cands }
      | none => fr
    let s := { saved with recStack := saved.recStack.map keepCands, nextRecUid := cur.nextRecUid }
    -- D37 (v1.8): fresh names are never reused, and generalisation and η records survive a
    -- private copy, which stays within one world (`exitWorld` scopes them to it). Only
    -- the types of abstract values created by the nested run are kept: a refinement of an
    -- older one's type ([Split] substitutes into every stored type) is that run's alone, and
    -- must not reach a sibling arm (arrays-library's arm leak)
    { s with nextAbs := cur.nextAbs, nextLoan := cur.nextLoan, neutrals := cur.neutrals, etaRefs := cur.etaRefs,
             absTy := saved.absTy ++ cur.absTy.extract saved.absTy.size cur.absTy.size,
             absDecl := cur.absDecl }

/-- D103: leave a comparison (`conv`, `convPi`, `convFn`): put back the state it started from,
keeping only the names made inside, as every private computation keeps them (D37's first half:
fresh names are never reused, so `nextAbs`, `nextLoan`, `nextRecUid`, the frozen readings
`absDecl` and the types of the unknowns made inside, the tail of `absTy`, only grow). Unlike
`restoreKeep`, the records made inside (generalisations `neutrals`, η-refinements `etaRefs`)
and the copy's changes to the recursion check's candidate lists are dropped: a comparison's
result is a boolean, which can mention nothing it made. -/
def restoreNames (saved : MState) : M Unit :=
  modify fun cur =>
    { saved with nextAbs := cur.nextAbs, nextLoan := cur.nextLoan, nextRecUid := cur.nextRecUid,
                 absTy := saved.absTy ++ cur.absTy.extract saved.absTy.size cur.absTy.size,
                 absDecl := cur.absDecl }

/-- A [Split] world (notes/split-model.md): the state an arm of a case split starts from.
Each arm of a split on an unknown `σ` is checked in its own world, the one where `σ` is that
arm's constructor; the worlds are exclusive (principle X), so nothing an arm establishes may
be visible in a sibling. `enterWorld` takes the snapshot before the first arm, each arm runs
inside `inWorld`, and `exitWorld` leaves it. Every arm of [Split], [Split-gen],
[T-Split-goal], a by-type match on a proof and `split f` goes through these three, so what a
world keeps is decided here, once. -/
structure World where
  saved : MState

/-- Take the snapshot every arm of a split starts from. -/
def enterWorld : M World := do pure ⟨← get⟩

/-- Leave an arm's world: restore the snapshot, keeping only what is true in every world.

Restored (world facts, principle X): Ω and the stored types, the goal, the refinements `refs`,
the types of abstract values that existed before the split (an arm's refinement substituted
into them), the generalisation records `neutrals` and the η-refinements `etaRefs` the arm
made. Both kinds of record map a value to abstract values typed in this world, so both are
scoped to it:
- A generalisation record names a program text at the type it has in this world; the same
  text can have another type in a sibling, since it may mention the value the arm refined
  (principle G; reviewer-6's A1: `⌈g(())⌉ := σ3 : Box(Unit)` from the arm `n := Z`, reused in
  the arm `n := S m`, where `g(())` is a `Box(Bool)`).
- An η-refinement `σ := C(σ̄)` of a one-constructor type has the same constructor in every
  world, but its fields `σ̄` are fresh unknowns whose types are read off `σ`'s type in this
  world, and that type can mention what the arm refined: a value parameter (`DQ(n)` with
  `y : G(n)`) or, through a dependent field, an earlier field. EtaBoom (docs/17): `σ : DP(n)`
  η-refined in the arm `n := Z` has `σy : G(Z, σx) = Void`; kept, the arm `n := S m` reused it
  where `y` is a `Nat`, and `match y {}` proved `False` (`CaseSplits.ArmEta`). A sibling that
  needs the fields derives its own record, with its own fresh names, which is what a kept
  record would be wherever the fields' types do not depend on the arm. Within one world
  private copies keep the record (`restoreKeep`), which is why it is recorded at all (D68).

Kept (true in every world, or names only):
- `nextAbs`, `nextLoan`, `nextRecUid`: name counters. Keeping them is what makes a fresh name
  never reused (D37); a counter states no fact.
- the types of abstract values created inside the arm: their names are fresh, and once the
  arm's records are dropped nothing outside the arm names them.
- the [Rec] candidates (`recStack` frames by `uid`): facts about calls, not about `σ`.

A field added to `MState` is restored by default; keeping one here is a claim that it holds in
every world, and needs the argument above. -/
def exitWorld (w : World) : M Unit :=
  modify fun cur =>
    let saved := w.saved
    let keepCands (fr : RecCtx) : RecCtx :=
      match cur.recStack.find? (·.uid == fr.uid) with
      | some c => { fr with cands := c.cands }
      | none => fr
    { saved with recStack := saved.recStack.map keepCands, nextRecUid := cur.nextRecUid,
                 nextAbs := cur.nextAbs, nextLoan := cur.nextLoan,
                 absTy := saved.absTy ++ cur.absTy.extract saved.absTy.size cur.absTy.size,
                 absDecl := cur.absDecl }

/-- Check one arm in world `w`: run `x` (which makes the arm's refinement and checks the arm),
then leave the world. The result is what `x` returns, read before the world is left. -/
def inWorld {α : Type} (w : World) (x : M α) : M α := do
  let a ← x
  exitWorld w
  pure a

/-- D53: run `x` as an erased term, whose reads copy. -/
def withErased {α : Type} (x : M α) : M α := do
  modify fun s => { s with erasedDepth := s.erasedDepth + 1 }
  let r ← onFail x (modify fun s => { s with erasedDepth := s.erasedDepth - 1 })
  modify fun s => { s with erasedDepth := s.erasedDepth - 1 }
  pure r

/-- D53: run `x` as code (a function's body, a sealed program's re-run), whose reads move,
even where the term that started it is erased: erasure applies to the reads written in
the erased term, not to the bodies of the functions it calls. -/
def withRuntime {α : Type} (x : M α) : M α := do
  let d := (← get).erasedDepth
  let c := (← get).copying
  modify fun s => { s with erasedDepth := 0, copying := false }
  let r ← onFail x (modify fun s => { s with erasedDepth := d, copying := c })
  modify fun s => { s with erasedDepth := d, copying := c }
  pure r

/-- D53: `withErased x` if `b`, else `x`. -/
def withErasedIf {α : Type} (b : Bool) (x : M α) : M α := if b then withErased x else x

/-- `clone` and closing off's `peek`: reads copy (with `erasedMoves`, erased reads alone move). -/
def withCopying {α : Type} (x : M α) : M α := do
  let c := (← get).copying
  modify fun s => { s with copying := true }
  let r ← onFail x (modify fun s => { s with copying := c })
  modify fun s => { s with copying := c }
  pure r

/-- Run `x` on a private copy of the state (P2, P6): its effects are discarded, and what
survives is decided by `restoreKeep`. Private to this file: the machine reaches it only
through `inStatement` (a statement position of the program) or `privately` (the checker's own
scaffolding), so that every discarded run is one of those two, by name. -/
private def onCopy {α : Type} (x : M α) : M α := do
  let saved ← get
  modify fun s => { s with privateDepth := s.privateDepth + 1 }
  let r ← onFail x (restoreKeep saved)
  restoreKeep saved
  pure r

/-- A statement position of the program (`notes/erasure-model.md`, E1–E5): a type, a proof, an
erased term and each argument of an erased call, a constructor argument of a proposition, `J`'s
endpoints and motive, a side of `Eq`, a side of `Id` (`observe`), an inductive's parameters, a
Π-type's captures. A statement has a value (⋆, or a type), never an effect: the compiled program
does not run it. Every statement position runs here, and only here:
- (E1) on a private copy of the state, which is thrown away: what it moves, writes, borrows or
  allocates is undone with the copy, as at runtime, where it does not run at all. So running a
  proof and skipping it are indistinguishable, and a statement's observation never depends on a
  discarded copy;
- (E5) as an erased term (`withErased`): its reads move as at runtime (D68), on the copy, and the
  runtime-only checks (`atRuntime`: K2/K3; a closure's moves of its captures) do not apply;
- (E3) what survives the copy is decided by `restoreKeep`, once: only facts that hold whatever
  the copy did (name counters, the types of names it created, generalisation records of closed
  program text, η-refinements, [Rec] obligations already checked, pure caches).

Whether a term is in a statement position is decided from syntax and declared types (E2,
`Decide.lean`), never here. A borrow-typed argument of a statement runs in place rather than on a
copy of its own (E4, `stmtArgIf`): the statement call it belongs to is itself in a statement
position, so in place means within that statement's copy. Nesting needs nothing: each nested
statement gets its own copy. -/
def inStatement {α : Type} (x : M α) : M α := onCopy (withErased x)

/-- The checker's own private computation, not a position of the program: scaffolding that binds
parameters, captures or field values in order to compute a type ([Call-type]'s codomain at the
arguments, an inductive's parameter types, a field's type, a Π-type's sort, an argument's
hint), a sealed program's type, an [Open] check with lent parts unknown, and [Conv-fun]'s
observation of two functions' generic calls. Its effects are discarded as a statement's are
(through `restoreKeep`), but it is not itself erased: the terms it runs keep their own status,
and every statement among them (the types it evaluates, by `evalType`) runs through
`inStatement`. -/
def privately {α : Type} (x : M α) : M α := onCopy x


def trace (msg : Unit → String) : M Unit := do
  if (← get).cfg.trace then modifyThe (Array LogEntry) (·.push (.line (msg ())))

def freshLoan : M Nat := do
  let s ← get
  set { s with nextLoan := s.nextLoan + 1 }
  pure s.nextLoan

/-- A fresh abstract value of type `ty`, whose declared reading `d` is frozen with it (D96). -/
def freshAbs (ty : Value) (d : DeclInfo) : M Nat := do
  let s ← get
  set { s with nextAbs := s.nextAbs + 1, absTy := s.absTy.push ty, absDecl := s.absDecl.push d }
  pure s.nextAbs

/-- D82: the next `eval`'s context reads its type, or not (`MState.wantTy`). -/
def demand (b : Bool) : M Unit := modify fun s => { s with wantTy := b }

/-- D82: whether the term being evaluated must give its type (`MState.wantHere`). -/
def wanted : M Bool := do pure (← get).wantHere

/-- The erasure flags of the term just evaluated (`lastErased`, `lastProof`). -/
def getFlags : M (Bool × Bool) := do
  let s ← get
  pure (s.lastErased, s.lastProof)

def setFlags (f : Bool × Bool) : M Unit :=
  modify fun s => { s with lastErased := f.1, lastProof := f.2 }

def absType (σ : Nat) : M Value := do
  match (← get).absTy[σ]? with
  | some T => pure T
  | none => err s!"unknown abstract value σ{σ}"

def lookupInd (n : String) : M IndDecl := do
  match (← get).inds.find? (·.name == n) with
  | some d => pure d
  | none => err s!"unknown inductive type {n}"

def lookupGlobal (n : String) : M GDef := do
  match (← get).globals.find? (·.name == n) with
  | some g => pure g
  | none => err s!"unknown constant {n}"

/-! ## Frames, bindings, temporaries -/

def topIdx : M Nat := do pure ((← get).env.size - 1)

def modifyFrame (f : Nat) (g : Frame → Frame) : M Unit :=
  modify fun s => { s with env := s.env.modify f g }

def pushFrame (fr : Frame := {}) : M Unit := modify fun s => { s with env := s.env.push fr }

def popFrameRaw : M Frame := do
  let s ← get
  match s.env.back? with
  | some fr => set { s with env := s.env.pop }; pure fr
  | none => err "internal: pop of empty environment"

def pushBind (h : Hint) (ty : Option Value) (v : Value) (proof : Bool := false)
    (decl : DeclInfo := .other) : M Unit := do
  modifyFrame (← topIdx) fun fr =>
    { fr with binds := fr.binds.push { hint := h, ty, val := v, proof, decl } }

/-- Run a declared-type reading whose free variables beyond its local scope are the
current frame's bindings (read in place, not copied into a list). -/
def withLive {α : Type} (live : Bool) (x : M α) : M α := do
  let old := (← get).liveScope
  modify fun s => { s with liveScope := live }
  let r ← onFail x (modify fun s => { s with liveScope := old })
  modify fun s => { s with liveScope := old }
  pure r

/-- What the declared type of the current frame's `i`-th variable (de Bruijn) says. -/
def liveDecl (i : Nat) : M DeclInfo := do
  let top := (← get).env.size - 1
  let bs := (← get).env[top]!.binds
  pure (if i < bs.size then bs[bs.size - 1 - i]!.decl else .other)

/-- Dev tooling (`Config.recordPushes`, `lake exe sweep --pushes`): log a push with no stored type in
a typed run, or of a borrow with none. -/
def notePush (site : String) (v : Value) (T : Option Value) : M Unit := do
  let s ← get
  if s.cfg.recordPushes && T.isNone && (s.typing || v.isBorrow) then
    modifyThe (Array LogEntry) (·.push (.push site s.typing v s.depth))

/-- Push the temporary `v` onto the top frame with its stored type `T` (D104: the type in hand at
the push, `none` where there is none; every push site says which, and names itself, `site`, for
the dev tooling's census). -/
def pushTemp (v : Value) (T : Option Value) (site : String := "") : M Unit := do
  notePush site v T
  modifyFrame (← topIdx) fun fr => { fr with temps := fr.temps.push v, tempTys := fr.tempTys.push T }

def pushTempAt (f : Nat) (v : Value) (T : Option Value) (site : String := "") : M Unit := do
  notePush site v T
  modifyFrame f fun fr => { fr with temps := fr.temps.push v, tempTys := fr.tempTys.push T }

/-- Pop the top frame's last temporary, and its stored type with it (never read: D104). -/
def popTemp : M Value := do
  let f ← topIdx
  match (← get).env[f]!.temps.back? with
  | some v => modifyFrame f (fun fr => { fr with temps := fr.temps.pop, tempTys := fr.tempTys.pop }); pure v
  | none => err "internal: no temporary to pop"

/-- D115: the top frame's last `n` temporaries, read in place (a constructor's fields while its
field types are checked). -/
def topTemps (n : Nat) : M (Array Value) := do
  let ts := (← get).env[(← get).env.size - 1]!.temps
  if ts.size < n then err s!"internal: {n} temporaries expected, {ts.size} held"
  pure (ts.extract (ts.size - n) ts.size)

def popTemps (n : Nat) : M (Array Value) := do
  let mut out := #[]
  for _ in [0:n] do out := out.push (← popTemp)
  pure out.reverse

/-- D115: a call's head and arguments, the last `n + 1` temporaries of frame `f` (the head first),
read in place. A call holds them there, in Ω, from their evaluation until the callee's frame binds
them, a sealed program's text takes them ([Close]), or they end (P5): every value the machine
holds is in Ω while anything else runs (D104), so whatever maps over Ω (an [End], a fill, a mark)
reaches them, and a loan of an argument's borrow is live. -/
def callTemps (f n : Nat) : M (Value × Array Value) := do
  let ts := (← get).env[f]!.temps
  if ts.size < n + 1 then err s!"internal: a call of {n} argument(s) holds only {ts.size} temporaries"
  let base := ts.size - (n + 1)
  pure (ts[base]!, ts.extract (base + 1) ts.size)

/-- D115: the position of argument `i` of the call whose `n` arguments are the last temporaries of
frame `f` (`callTemps`). -/
def callArgPos (f n i : Nat) : M Pos := do
  let sz := (← get).env[f]!.temps.size
  if sz < n + 1 || i ≥ n then err s!"internal: no argument {i} among a call's {n} temporaries"
  pure (.temp f (sz - n + i))

/-- D115: take a call's head and arguments off frame `f` (`callTemps`), where the callee's frame
binds them or a sealed program's text has taken them. -/
def takeCallTemps (f n : Nat) : M (Value × Array Value) := do
  let r ← callTemps f n
  let base := (← get).env[f]!.temps.size - (n + 1)
  modifyFrame f fun fr => { fr with temps := fr.temps.extract 0 base, tempTys := fr.tempTys.extract 0 base }
  pure r

/-- The position of de Bruijn variable `i` in the top frame. -/
def varPos (i : Nat) : M Pos := do
  let f ← topIdx
  let n := (← get).env[f]!.binds.size
  if i < n then pure (.bind f (n - 1 - i)) else err s!"internal: unbound variable #{i}"

def getAt : Pos → M Value
  | .bind f i => do pure (← get).env[f]!.binds[i]!.val
  | .temp f i => do pure (← get).env[f]!.temps[i]!

def setAt (p : Pos) (v : Value) : M Unit :=
  match p with
  | .bind f i => modifyFrame f fun fr => { fr with binds := fr.binds.modify i ({ · with val := v }) }
  | .temp f i => modifyFrame f fun fr => { fr with temps := fr.temps.set! i v }

/-- A binding's stored type. A temporary's (`Frame.tempTys`, D104) is not read by the checker, so
this is `none` there, as it was before temporaries had one. -/
def tyAt : Pos → M (Option Value)
  | .bind f i => do pure (← get).env[f]!.binds[i]!.ty
  | .temp _ _ => pure none

/-- All positions of Ω, in the order of Ω. -/
def allPos (env : Env) : List Pos := Id.run do
  let mut out := #[]
  for h : f in [0:env.size] do
    let fr := env[f]
    for i in [0:fr.binds.size] do out := out.push (Pos.bind f i)
    for i in [0:fr.temps.size] do out := out.push (Pos.temp f i)
  pure out.toList

def valAt (env : Env) : Pos → Value
  | .bind f i => env[f]!.binds[i]!.val
  | .temp f i => env[f]!.temps[i]!

/-- Apply `f` to every value position of the state, in one fixed order: each value of Ω and,
with `types`, the stored type of its binding or temporary (D104) right after it; then, with
`types`, the type of every abstract value and the goal. Types are values used as types, so they
run erased.

This is the one place that says what a change to the state must reach. A refinement
(`substEnv` with `types`), the fill of a loan (`substEnv` without: types hold no live loan)
and the re-normalisation after a generalised neutral is refined (`renormAll`) all go
through it, so a sealed program cannot be left stale in one of them because a position was
missed in another (closing off's obligation (S-all), `notes/closeoff-model.md`; before this,
`renormAll` skipped the types of abstract values that `substEnv` reached). -/
def mapState (f : Value → M Value) (types : Bool) : M Unit := do
  for p in allPos (← get).env do
    setAt p (← f (← getAt p))
    if types then
      if let .bind fi i := p then
        if let some T := (← get).env[fi]!.binds[i]!.ty then
          let T' ← withErased (f T)
          modifyFrame fi fun fr => { fr with binds := fr.binds.modify i ({ · with ty := some T' }) }
        -- D82: a deferred parameter type's inputs, as its type would be if it had been evaluated
        if let some (P, ws, j) := (← get).env[fi]!.binds[i]!.lazyTy then
          let P' ← withErased (f P)
          let ws' ← withErased (ws.mapM f)
          modifyFrame fi fun fr => { fr with binds := fr.binds.modify i ({ · with lazyTy := some (P', ws', j) }) }
      -- D104: a temporary's stored type, as a binding's (never read, but kept as Ω's are)
      if let .temp fi i := p then
        if let some (some T) := (← get).env[fi]!.tempTys[i]? then
          let T' ← withErased (f T)
          modifyFrame fi fun fr => { fr with tempTys := fr.tempTys.set! i (some T') }
  if types then
    withErased do
      let n := (← get).absTy.size
      for i in [0:n] do
        let T' ← f (← get).absTy[i]!
        modify fun s => { s with absTy := s.absTy.set! i T' }
      if let some g := (← get).goal then
        let g' ← f g
        modify fun s => { s with goal := some g' }

end Ochr
