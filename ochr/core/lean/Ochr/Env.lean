import Ochr.Catch

/-!
# The environment Ω and the machine state

Ω is a stack of frames (RULES §2). A frame holds named bindings `x : A ↦ v` and
*temporaries*: values in flight during evaluation (an evaluated argument waiting for
the next one, the right-hand side of an assignment, a result while its frame is
popped). Temporaries are part of Ω so that [End] can find and substitute into them.
-/

namespace Ochr

/-- What a declared type says, read off its term without normalising (D55, and the
syntactic erasure pre-pass): the sort `l` itself (whatever has it is a type), a
proposition (whatever has it is a proof), a Π-type with what its codomain says, a borrow
type, or anything else (data). `any` is the type of a zero-arm match, which agrees with
every other. -/
inductive DeclInfo where
  | sort (l : Nat)
  | prop
  | pi (cod : DeclInfo)
  | ref (A : DeclInfo)
  | other
  | any
  | conflict    -- a match whose arms disagree about being proofs: it has no declared type (D63)
deriving BEq, Inhabited, Repr

/-- A proof: a value of a proposition, or a function into proofs (impredicative `Prop`). -/
def DeclInfo.isProof : DeclInfo → Bool
  | .prop => true
  | .pi r => r.isProof
  | _ => false

structure Binding where
  hint : Hint
  ty : Option Value     -- `none` for bindings pushed by the untyped machine
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
deriving Inhabited

structure Frame where
  binds : Array Binding := #[]
  temps : Array Value := #[]
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
deriving Inhabited

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
  refs : List (Nat × Value) := []     -- [Split] refinements made so far: σ ↦ Z | S σ'
  etaRefs : List (Nat × Value) := []  -- D68: η-refinements of one-constructor abstract values (σ ↦ C(σ₁, …)), global like fresh names, so every private copy names σ's fields alike
  goal : Option Value := none
  recStack : List RecCtx := []        -- the functions whose bodies enclose the current point (top first)
  nextRecUid : Nat := 0               -- fresh `RecCtx.uid`s (never reused)
  cfg : Config := {}
  lastErased : Bool := false          -- set by `eval`: was the term just evaluated erased (D28)?
  lastProof : Bool := false           -- ... and is it a proof (its declared type has sort Prop, D35)?
  classCache : List (Value × Nat) := []   -- erasure class of function types (D28), a pure cache
  convStack : List (Value × Value) := []  -- function pairs being compared observationally (D30)
  neutrals : List (Value × Nat) := []     -- [Split] generalisations: sealed program ↦ its σ (finding G1)
  depth : Nat := 0                        -- call depth (bounded, like fuel: the checker must terminate)
  placeLog : Array (Nat × Nat × Place × Bool) := #[]  -- D53: every move (true) and assignment (false), at its
                                          -- root binding's position (restored with the state)
  constDecls : List (String × DeclInfo) := []   -- what each global's declared type says (a pure cache)
  curDecl : Option DeclInfo := none        -- the pre-pass's reading of the term being evaluated
  tailDecl : Option DeclInfo := none       -- ... handed to its tail, whose reading it is (one-shot)
  liveScope : Bool := false               -- declared-type reading: variables beyond the local scope are the top frame's
  headEval : Bool := false                -- the next `eval` is of a call's head (not classified by the pre-pass)
  erasedDepth : Nat := 0                  -- D53: > 0 while evaluating an erased term, whose reads copy
  inPlace : Bool := false                 -- D53: the next read is in place (a call's head, a block's read-only capture)
  modelDepth : Nat := 0                   -- K2/K3: > 0 inside model code, which never runs at runtime
  copying : Bool := false      -- inside `clone`/`peek`: reads copy (the explicit copy, not an erased-read mode)
  observing : Bool := false    -- D68: `Id` reading a side's final state: a borrow may end over a moved-out part, observed as `⊥`
  typing : Bool := false                  -- the term being evaluated is part of the checked program (`eval true`),
                                          -- where D64's [Repack] points are checked
  locs : Locs := {}                       -- the editor: where the declaration's terms are (`located`)
deriving Inhabited

/-- What the editor shows on hover at a located term, for one check of it (`Located.note`). -/
inductive Note where
  | value (v : Value) (T : Option Value) (pointsTo : List String)   -- its value and type; a borrow's lender
  | goal (G : Value)                                               -- the goal a tail term is checked against
  | expected (A : Value)                                           -- the type an argument is checked against
  | rule (name : String)                                           -- a rule applied here (`Rules.fire`)
  | hole (G : Value) (Ω : List (String × Option Value × Value))    -- a hole's goal, and Ω there

/-- An entry of the log: a trace line (`Config.trace`), or a note for the editor, at a source
range, with the [Split] refinements of the path it was made on. -/
inductive LogEntry where
  | line (s : String)
  | note (l : Loc) (refs : List (Nat × Value)) (n : Note)

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
    let s := { saved with classCache := cur.classCache, constDecls := cur.constDecls,
                          recStack := saved.recStack.map keepCands, nextRecUid := cur.nextRecUid }
    -- D37 (v1.8): fresh names are never reused, and generalisation records are global. Only
    -- the types of abstract values created by the nested run are kept: a refinement of an
    -- older one's type ([Split] substitutes into every stored type) is that run's alone, and
    -- must not reach a sibling arm (arrays-library's arm leak)
    { s with nextAbs := cur.nextAbs, nextLoan := cur.nextLoan, neutrals := cur.neutrals, etaRefs := cur.etaRefs,
             absTy := saved.absTy ++ cur.absTy.extract saved.absTy.size cur.absTy.size }

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
into them), and the generalisation records `neutrals` the arm made. A record names a program
text at the type it has in this world; the same text can have another type in a sibling, since
it may mention the value the arm refined (principle G; reviewer-6's A1: `⌈g(())⌉ := σ3 :
Box(Unit)` from the arm `n := Z`, reused in the arm `n := S m`, where `g(())` is a
`Box(Bool)`).

Kept (true in every world, or names only):
- `nextAbs`, `nextLoan`, `nextRecUid`: name counters. Keeping them is what makes a fresh name
  never reused (D37); a counter states no fact.
- the types of abstract values created inside the arm: their names are fresh, so no sibling
  can mention them.
- `etaRefs`: an η-refinement `σ := C(σ̄)` of a one-constructor type is read off `σ`'s type
  alone, so it holds in every world, unlike a case split's refinement or a generalisation
  record (`neutrals`), which hold in one. Both are maps from values to abstract values; they
  are scoped oppositely for that reason.
- the [Rec] candidates (`recStack` frames by `uid`) and the pure caches (`classCache`,
  `constDecls`): facts about declarations and calls, not about `σ`.

A field added to `MState` is restored by default; keeping one here is a claim that it holds in
every world, and needs the argument above. -/
def exitWorld (w : World) : M Unit :=
  modify fun cur =>
    let saved := w.saved
    let keepCands (fr : RecCtx) : RecCtx :=
      match cur.recStack.find? (·.uid == fr.uid) with
      | some c => { fr with cands := c.cands }
      | none => fr
    { saved with classCache := cur.classCache, constDecls := cur.constDecls,
                 recStack := saved.recStack.map keepCands, nextRecUid := cur.nextRecUid,
                 nextAbs := cur.nextAbs, nextLoan := cur.nextLoan, etaRefs := cur.etaRefs,
                 absTy := saved.absTy ++ cur.absTy.extract saved.absTy.size cur.absTy.size }

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

def freshAbs (ty : Value) : M Nat := do
  let s ← get
  set { s with nextAbs := s.nextAbs + 1, absTy := s.absTy.push ty }
  pure s.nextAbs

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

def pushTemp (v : Value) : M Unit := do
  modifyFrame (← topIdx) fun fr => { fr with temps := fr.temps.push v }

def pushTempAt (f : Nat) (v : Value) : M Unit :=
  modifyFrame f fun fr => { fr with temps := fr.temps.push v }

def popTemp : M Value := do
  let f ← topIdx
  match (← get).env[f]!.temps.back? with
  | some v => modifyFrame f (fun fr => { fr with temps := fr.temps.pop }); pure v
  | none => err "internal: no temporary to pop"

def popTemps (n : Nat) : M (Array Value) := do
  let mut out := #[]
  for _ in [0:n] do out := out.push (← popTemp)
  pure out.reverse

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
with `types`, the stored type of its binding right after it; then, with `types`, the type of
every abstract value and the goal. Types are values used as types, so they run erased.

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
