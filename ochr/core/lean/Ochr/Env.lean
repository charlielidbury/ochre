import Ochr.Pretty

/-!
# The environment Ω and the machine state

Ω is a stack of frames (RULES §2). A frame holds named bindings `x : A ↦ v` and
*temporaries*: values in flight during evaluation (an evaluated argument waiting for
the next one, the right-hand side of an assignment, a result while its frame is
popped). Temporaries are part of Ω so that [End] can find and substitute into them.
-/

namespace Ochr

structure Binding where
  hint : Hint
  ty : Option Value     -- `none` for bindings pushed by the untyped machine
  val : Value
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

/-- The function whose body is being checked, for [Rec]. -/
structure RecCtx where
  fn : Value
  entries : Array (Option Nat)   -- entry abstract value of each parameter (through the borrow)
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
  trace : Bool := false          -- record goals, splits and call types (for inspection)
deriving Inhabited, Repr

structure MState where
  env : Env := #[{}]
  globals : List GDef := []
  nextLoan : Nat := 0
  nextAbs : Nat := 0
  absTy : Array Value := #[]
  refs : List (Nat × Value) := []     -- [Split] refinements made so far: σ ↦ Z | S σ'
  goal : Option Value := none
  recStack : List RecCtx := []        -- the functions whose bodies enclose the current point
  recCands : List (List Nat) := []    -- per function (top first): surviving recursive positions;
                                      -- accumulators, they survive branch restores
  fuel : Nat := 2000000
  cfg : Config := {}
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

/-- Restore a saved state, keeping the fuel spent and the [Rec] accumulators. -/
def restoreKeep (saved : MState) : M Unit :=
  modify fun cur => { saved with fuel := cur.fuel,
                                 recCands := cur.recCands.drop (cur.recCands.length - saved.recCands.length) }

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

def absType (σ : Nat) : M Value := do
  match (← get).absTy[σ]? with
  | some T => pure T
  | none => err s!"unknown abstract value σ{σ}"

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

def pushBind (h : Hint) (ty : Option Value) (v : Value) : M Unit := do
  modifyFrame (← topIdx) fun fr => { fr with binds := fr.binds.push ⟨h, ty, v⟩ }

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
