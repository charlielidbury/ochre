import Ochr.Pretty

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
  blockRef : Bool := false    -- a stuck block's borrow parameter for a place it writes (a
                              -- checker device: a closure in the block captures through it)
  cap : Bool := false         -- a closure's captured value (D53 (e): its body may not move it out)
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

/-- A declared inductive type (v2.0, D45/D46): uniform parameters (a telescope of type
terms, each in the scope of the earlier parameters), a sort (`0` = `Prop`, `1` = `Type₀`),
and zero or more constructors with named fields, whose types are terms in the scope of
the parameters (de Bruijn: the last parameter is `var 0`). -/
structure IndDecl where
  name : String
  params : List (Hint × Term) := []
  sort : Nat := 1
  ctors : List (String × List (String × Term)) := []
  copy : Bool := false    -- declared `copy` (D53): a cost-model statement, reads copy
deriving Inhabited

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

/-- Switches for counterfactual runs: each disables one rule of v1 (or one fix of
this checker), so that the regression tests can show which rule blocks which attack. -/
structure Config where
  p5 : Bool := true              -- D14: calls at a proposition are not run
  multiOwner : Bool := true      -- D18: the footprint observes every owner of a hole
  recGuard : Bool := true        -- D17: [Rec] entry-value guard
  accessInside : Bool := true    -- D19: [Access] ends loans inside the accessed content
  selfHeadOnly : Bool := true    -- this checker's fix L1: `f` occurs only as the head of a call in its body
  argNotBot : Bool := true       -- this checker's fix L2: an argument must not be ⊥ at the call point
  generalize : Bool := true      -- clarification C8: [Split] on a sealed program generalises it to a fresh σ first
  blockMoves : Bool := true      -- clarification C5: a stuck block moves in a borrow variable that an arm moves
  inferRecPos : Bool := false    -- v1 behaviour: infer the decreasing parameter instead of reading `by xⱼ`
  eraseOnCopy : Bool := true     -- v1.3 P2 (D26): a term whose type is a proposition runs on a private copy
  proofParamsStar : Bool := true -- v1.4 D27: a proof parameter is ⋆ at the generic call (not an abstract σ)
  recNested : Bool := true       -- v1.3 (L3): [Rec] also checks recursive calls inside nested functions
  erasureByDecl : Bool := true   -- v1.5 D28: erasure decided per definition / syntactically, not from values
  matchEndsInside : Bool := true -- v1.5 D29: matching ends loans anywhere inside a neutral head
  closureConv : Nat := 0         -- v1.5 D30: 0 = generic-call observation, 1 = syntactic, 2 = result only
  unboundWithoutBy : Bool := true -- v1.5 D31: without `by`, f is not in scope in its body
  patternWritesVisible : Bool := true -- v1.5 D32: writes through pattern variables are writes to the scrutinee
  genConsistent : Bool := true   -- finding G1: a generalised neutral stays generalised when normalisation re-derives it
  classBySyntax : Bool := true   -- v1.7 D35: a function's class is read from its codomain term, never evaluated
  blockRule : Nat := 2           -- v1.7 D35, a stuck block is erased: 2 = when every arm is a proof (its match would
                                 -- be, finding P2); 1 = when its computed type has sort Prop; 0 = v1.6, by the
                                 -- call rule on its computed codomain (a sort: erased as returning types)
  seqByProof : Bool := true      -- v1.7 D35: a let, sequence or match is erased iff it is a proof (its tail is);
                                 -- v1.6: iff its tail is erased, so also when the tail returns types
  rowByDecl : Bool := true       -- v1.7 D35: [Close]'s row is read from the declared codomain
  leafRule : Nat := 2            -- a place, constant or λ is a proof (erased): 2 = when declared of sort Prop (a
                                 -- variable's flag, finding P3); 1 = when its value is ⋆ (finding P1, unstable);
                                 -- 0 = never (v1.6)
  positivity : Bool := true      -- v1.7 D36: constructor fields are first-order data
  globalRecords : Bool := true   -- v1.8 D37: generalisation records and fresh names survive private copies
  obsBorrow : Bool := true       -- v1.8 D38: a borrow result is observed through a fresh value written into it
  headGuardNeutral : Bool := true -- v1.8 D39: [Seal]'s head guard covers neutral-headed calls
  genPlaceType : Bool := true    -- v1.8: a generalised σ has the matched place's type
  confine : Bool := true         -- v1.9 D41: an erased term may not assign, borrow or move a place that outlives it
  borrowParam : Bool := true     -- v1.9 D44: a function type returning `&T` has a borrow parameter
  capTypes : Bool := true        -- captured neutral data and proofs keep their types (reviewer-2, lean-checker)
  byType : Bool := true          -- v2.0 D45: a match on a proof (a Prop inductive) is by its type, not its content
  subsingleton : Bool := true    -- v2.0 D45: a match on a proof returns a non-proof only from a subsingleton
                                 -- (zero constructors, or one whose fields are all proofs)
  propValues : Bool := true      -- v2.0 D42: a constructor application of a Prop inductive is a proof (⋆, erased)
  disjoint : Bool := true        -- v2.0 D47: `Eq D (C ā) (C' b̄) ≡ False` for distinct constructors C ≠ C'
  scrutTyped : Bool := true      -- finding (v2.0 round): a match's scrutinee must have the constructors' type
  refData : Bool := true         -- D48 (1): `&A` only for a data type A (never a universe, Π-type or proposition)
  injective : Bool := true      -- D52: Eq on two values of one constructor is the conjunction over its fields
  refTop : Bool := true          -- D48 (2): `&` only at the top of a declared type, never produced by computation
  sortsSyntactic : Bool := true  -- D55: a term written where a type is expected has a declared type that is syntactically a sort
  classInType : Bool := true     -- D54: a Π-type's erasure class and [Close] row are part of it (conversion compares them)
  prePass : Bool := true         -- erasure is decided before evaluation, from declared types (the syntactic pre-pass)
  jStuck : Bool := true          -- D56: J computes only when its endpoints are convertible, otherwise it is stuck
  zeroArmStuck : Bool := true    -- D58: a zero-arm match outside a proof position is stuck, not ⋆
  moves : Bool := true           -- D53: a runtime read of data whose type is not a copy type moves it; erased reads copy
  ghosts : Bool := true          -- D53 (c): a move leaves a ghost of the value, which erased terms still read
  fnRule : Bool := true          -- D53 (e): a call does not consume its function; a closure is copy iff its captures are, and its body may not move them out
  unitNorm : Bool := false       -- counterfactual D50: the unit laws normalise stored types (v2.0 as first built)
  piUnder : Bool := true         -- D48 (3): Π-types are compared under their binders, at generic values
  proofDataFields : Bool := true -- D49 (3): a data field of a matched proof is a fresh abstract value (not ⋆)
  confineBodies : Bool := false  -- an extension of D41, not in RULES: the body of a function whose calls are
                                 -- erased, and each arm of an erased stuck block, are confined too
  trace : Bool := false          -- record goals, splits and call types (for inspection)
deriving Inhabited, Repr, BEq

/-- The pre-pass is checked against the after-the-fact classification under the rules as
they stand; a counterfactual run switches a rule off and measures that alone. -/
def Config.prePassAssert (c : Config) : Bool :=
  c.prePass && { c with trace := false } == ({} : Config)

/-- D41: one assignment, borrow or move, by the position of its place's root. It is
`pending` once an erased run it belongs to has affected a place outliving that run: an
enclosing erased term in which the place is local resolves it, anything else rejects. -/
structure Effect where
  f : Nat
  i : Nat
  kind : String
  place : Place
  root : String          -- the root binding's name (printed only on an error)
  pending : Bool := false
deriving Inhabited

def Effect.desc (e : Effect) : String :=
  s!"{e.kind} {e.place.pp ((List.replicate e.place.root "?") ++ [e.root])}"

structure MState where
  env : Env := #[{}]
  globals : List GDef := []
  inds : List IndDecl := []
  nextLoan : Nat := 0
  nextAbs : Nat := 0
  absTy : Array Value := #[]
  refs : List (Nat × Value) := []     -- [Split] refinements made so far: σ ↦ Z | S σ'
  goal : Option Value := none
  recStack : List RecCtx := []        -- the functions whose bodies enclose the current point (top first)
  nextRecUid : Nat := 0               -- fresh `RecCtx.uid`s (never reused)
  fuel : Nat := 2000000
  cfg : Config := {}
  lastErased : Bool := false          -- set by `eval`: was the term just evaluated erased (D28)?
  lastProof : Bool := false           -- ... and is it a proof (its declared type has sort Prop, D35)?
  classCache : List (Value × Nat) := []   -- erasure class of function types (D28), a pure cache
  convStack : List (Value × Value) := []  -- function pairs being compared observationally (D30)
  neutrals : List (Value × Nat) := []     -- [Split] generalisations: sealed program ↦ its σ (finding G1)
  depth : Nat := 0                        -- call depth (bounded, like fuel: the checker must terminate)
  effects : Array Effect := #[]           -- D41: assigns, borrows and moves so far (restored with the state)
  preAssert : Option Bool := none         -- `cfg.prePassAssert`, computed once
  constDecls : List (String × DeclInfo) := []   -- what each global's declared type says (a pure cache)
  curDecl : Option DeclInfo := none        -- the pre-pass's reading of the term being evaluated
  tailDecl : Option DeclInfo := none       -- ... handed to its tail, whose reading it is (one-shot)
  liveScope : Bool := false               -- declared-type reading: variables beyond the local scope are the top frame's
  headEval : Bool := false                -- the next `eval` is of a call's head (not classified by the pre-pass)
  erasedDepth : Nat := 0                  -- D53: > 0 while evaluating an erased term, whose reads copy
  inPlace : Bool := false                 -- D53: the next read is in place (a call's head, a block's read-only capture)
deriving Inhabited

inductive Fail where
  | stuck (fuel : Nat)
  | error (msg : String)

instance : Inhabited Fail := ⟨.error "?"⟩

/-- The machine monad. The inner `StateM` holds the trace, which survives both state
restores and errors (so a rejected definition still shows how far it got). -/
abbrev M := StateT MState (ExceptT Fail (StateM (Array String)))

def err {α : Type} (msg : String) : M α := throw (.error msg)

/-- Stuck on a neutral (RULES §3 [Match]); the innermost enclosing call closes off. -/
def stuckNow {α : Type} : M α := do throw (.stuck (← get).fuel)

def tick : M Unit := do
  let s ← get
  if s.fuel == 0 then err "out of fuel"
  set { s with fuel := s.fuel - 1 }

/-- Restore a saved state, keeping the fuel spent and the [Rec] accumulators: each saved
[Rec] frame takes the candidates of the current frame with the same `uid`, if there is
one (a computation that replaced the stack, e.g. `sealedType`, cannot wipe them). -/
def restoreKeep (saved : MState) : M Unit :=
  modify fun cur =>
    let keepCands (fr : RecCtx) : RecCtx :=
      match cur.recStack.find? (·.uid == fr.uid) with
      | some c => { fr with cands := c.cands }
      | none => fr
    let s := { saved with fuel := cur.fuel, classCache := cur.classCache, constDecls := cur.constDecls,
                          recStack := saved.recStack.map keepCands, nextRecUid := cur.nextRecUid }
    -- D37 (v1.8): fresh names are never reused, and generalisation records are global
    if cur.cfg.globalRecords then
      { s with nextAbs := cur.nextAbs, absTy := cur.absTy, nextLoan := cur.nextLoan, neutrals := cur.neutrals }
    else s

/-- D53: run `x` as an erased term, whose reads copy. -/
def withErased {α : Type} (x : M α) : M α := do
  modify fun s => { s with erasedDepth := s.erasedDepth + 1 }
  let r ← tryCatch x (fun e => do modify (fun s => { s with erasedDepth := s.erasedDepth - 1 }); throw e)
  modify fun s => { s with erasedDepth := s.erasedDepth - 1 }
  pure r

/-- D53: run `x` as code (a function's body, a sealed program's re-run), whose reads move,
even where the term that started it is erased: erasure applies to the reads written in
the erased term, not to the bodies of the functions it calls. -/
def withRuntime {α : Type} (x : M α) : M α := do
  let d := (← get).erasedDepth
  modify fun s => { s with erasedDepth := 0 }
  let r ← tryCatch x (fun e => do modify (fun s => { s with erasedDepth := d }); throw e)
  modify fun s => { s with erasedDepth := d }
  pure r

/-- D53: `withErased x` if `b`, else `x`. -/
def withErasedIf {α : Type} (b : Bool) (x : M α) : M α := if b then withErased x else x

/-- Run `x` on a private copy of the state (P2, P6): its effects are discarded. -/
def onCopy {α : Type} (x : M α) : M α := do
  let saved ← get
  let r ← tryCatch x (fun e => do restoreKeep saved; throw e)
  restoreKeep saved
  pure r

def trace (msg : Unit → String) : M Unit := do
  if (← get).cfg.trace then modifyThe (Array String) (·.push (msg ()))

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
    (decl : DeclInfo := .other) (blockRef : Bool := false) : M Unit := do
  modifyFrame (← topIdx) fun fr =>
    { fr with binds := fr.binds.push { hint := h, ty, val := v, proof, decl, blockRef } }

/-- Run a declared-type reading whose free variables beyond its local scope are the
current frame's bindings (read in place, not copied into a list). -/
def withLive {α : Type} (live : Bool) (x : M α) : M α := do
  let old := (← get).liveScope
  modify fun s => { s with liveScope := live }
  let r ← tryCatch x (fun e => do modify (fun s => { s with liveScope := old }); throw e)
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

end Ochr
