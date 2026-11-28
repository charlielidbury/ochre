import Ochr.Examples.Nat

/-! # Unit tests of individual rules, run directly on the machine functions

Not part of the tour: these call the checker's functions on hand-built values, for
[Seal] (a sealed program re-runs when a refinement is substituted) and for the owners and
footprint of RULES §4. The programs they need (`AddM`, `TailM`) come from
`Nats`. -/

open Ochr Ochr.Test Ochr.Surface

namespace Ochr.Units

/-- The globals after checking a block (its library first). -/
def globalsOf (b : Block) : List GDef :=
  let p := Ochr.Test.libOf {} 2000000 b ++ b.decls
  (globalsAfter {} (p.filterMap fun d => (resolveProgram p d).toOption)).1

def st (b : Block) (nAbs : Nat) : MState :=
  { globals := globalsOf b, nextAbs := nAbs, absTy := (List.replicate nAbs Value.tNat).toArray }

def ok? {α : Type} : Except String α → Option α
  | .ok a => some a
  | .error _ => none

/-- `N(v, w) := ⌈let c1 : Nat = v; AddM(&c1, w); c1⌉`, what [Close] leaves in `AddM`'s borrowed
place (the final read of `c1` is an observation, `peek`: it copies, D53; the cell has its
declared type, D82). -/
def N (v w : Value) : Value :=
  .sealed (.letIn ⟨"c1"⟩ (.ascribe (.val v) (.val .tNat)) (.seq (.call (.val (.gfn "AddM")) [.borrow (.var 0), .val w] true) (.prim "peek" [.place (.var 0)])))

/-- `B(v)[h] := ⌈let c1 : Nat = v; let r = TailM(&c1); *r := h; c1⌉`, `TailM`'s effect with its hole. -/
def B (v h : Value) : Value :=
  .sealed (.letIn ⟨"c1"⟩ (.ascribe (.val v) (.val .tNat)) (.letIn ⟨"r"⟩ (.call (.val (.gfn "TailM")) [.borrow (.var 0)] true)
    (.seq (.assign (.deref (.var 0)) (.val h)) (.prim "peek" [.place (.var 1)]))))

-- [Seal] (D9): refining σ0 := S σ1 re-runs N(σ0, 0); the inner call closes off, the
-- head call does not, so the S surfaces (deriver-e1 lemma S2)
#guard ok? (runM (do substV (← fuelLeft) (.abs 0) (.succ (.abs 1)) (N (.abs 0) .zero)) (st Nats 2)) == some (.succ (N (.abs 1) .zero))
-- deriver-e1 S1: N(0, 0) ≡ 0
#guard ok? (runM (do substV (← fuelLeft) (.abs 0) .zero (N (.abs 0) .zero)) (st Nats 1)) == some .zero
-- deriver-e1 S0: N(σ, 0) is normal (its own head call is not closed off again: no loop)
#guard ok? (runM (do substV (← fuelLeft) (.abs 5) .zero (N (.abs 0) .zero)) (st Nats 6)) == some (N (.abs 0) .zero)
-- deriver-e2 §3.4: B(S σ1)[τ] ≡ S B(σ1)[τ]
#guard ok? (runM (do substV (← fuelLeft) (.abs 0) (.succ (.abs 1)) (B (.abs 0) (.abs 2))) (st Nats 3)) == some (.succ (B (.abs 1) (.abs 2)))
-- deriver-e2 F3 / D11, changed by D97: a program whose text holds a loan (a hole) is not run, so
-- substituting into `B(σ0)[loan_9]` leaves it sealed; it runs when the hole is filled (next test)
#guard ok? (runM (do substV (← fuelLeft) (.abs 0) .zero (B (.abs 0) (.loan 9))) (st Nats 1)) == some (B .zero (.loan 9))
-- ending the borrow fills the hole by substitution and re-normalises (D11)
#guard ok? (runM (do substV (← fuelLeft) (.loan 9) (.abs 2) (B .zero (.loan 9))) (st Nats 3)) == some (.abs 2)

-- D18: owners(ℓ) is a set. Ω = [a ↦ S loan_5, b ↦ ⌈… loan_5 …⌉, r ↦ borrow_5 0]
def envD18 : Env := #[{ binds := #[{ hint := ⟨"a"⟩, ty := some .tNat, val := .succ (.loan 5) },
                                  { hint := ⟨"b"⟩, ty := some .tNat, val := .sealed (.val (.loan 5)) },
                                  { hint := ⟨"r"⟩, ty := some (.tRef .tNat), val := .borrow 5 .zero }] }]
#guard owners envD18 5 == [.bind 0 0, .bind 0 1]
-- W(*r := 0, *r := 1) observes both owners
#guard footprint envD18 [.assign (.deref (.var 0)) .zero, .assign (.deref (.var 0)) (.succ .zero)] == [.bind 0 0, .bind 0 1]
-- an occurrence inside another borrow's content contributes that borrow's owners
def envChain : Env := #[{ binds := #[{ hint := ⟨"c"⟩, ty := some .tNat, val := .loan 0 }] },
                        { binds := #[{ hint := ⟨"x"⟩, ty := some (.tRef .tNat), val := .borrow 0 (.succ (.loan 1)) },
                                     { hint := ⟨"x'"⟩, ty := some (.tRef .tNat), val := .borrow 1 (.abs 0) }] }]
#guard owners envChain 1 == [.bind 0 0]

end Ochr.Units

/-! ## Blocks that use other blocks

`AttrUser` uses `AttrLib`. Only `AttrLib`'s accepted, non-`reject` declarations are visible
to it; they are checked again in `AttrUser`, ahead of its own declarations. -/

ochr AttrLib {
  def Swap (P : Prop) (Q : Prop) (h : P ∧ Q) : Q ∧ P := match h { Intro(a, b) => ⟨b, a⟩ }
  reject def Hidden : Nat := ()
}

ochr AttrUser uses AttrLib {
  def UseSwap (P : Prop) (Q : Prop) (h : P ∧ Q) : Q ∧ P := Swap(P, Q, h)
  def Alone : Nat := 0
  -- a `reject` declaration of a used block is not visible
  reject def SeesHidden : Nat := Hidden
}

-- a block's report has rows for its own declarations only
open Ochr.Test in
#guard (run "AttrUser" AttrUser).rows.map (·.name) == ["UseSwap", "Alone", "SeesHidden"]

-- one flat namespace: redeclaring a name a used block declares is a clash (the `ochr` command
-- reports it when the block is elaborated), but a `reject` declaration of the used block is
-- not in the namespace
open Ochr.Surface in
#guard (Block.mk "Clashy" [AttrLib] [{ name := "Swap", expectAccept := true }]).clashes ==
  ["Clashy declares Swap, which AttrLib (used by Clashy) already declares; the declarations of a block and the blocks it uses share one namespace"]
open Ochr.Surface in
#guard (Block.mk "NoClash" [AttrLib] [{ name := "Hidden", expectAccept := true }]).clashes == []
open Ochr.Surface in
#guard (Block.mk "Twice" [AttrLib, AttrUser] []).closure.map (·.name) == ["AttrLib", "AttrUser"]

/-! ## Σ's names are fresh ([Def], [Const], [Ind-decl]), and verdicts are positional

The `ochr` command rejects a block that redeclares a name (`Block.clashes`), so these
programs are put together here from separate blocks, as `checkProgram` takes any list. A
definition or an inductive type, or a constructor, named like a declaration before it is
rejected by the checker itself; and each declaration reports its own verdict, so a rejected
`DupX : False` is not reported with the accepted `DupX : Nat` before it (as when verdicts
were looked up by name). -/

ochr DupA {
  def DupX : Nat := 0
  inductive DupTy := DupC
}

ochr DupB {
  reject def DupX : False := refl
}

ochr DupD {
  def DupX : Nat := 1
  def DupTy : Nat := 0
  def DupC : Nat := 0
}

ochr DupE {
  inductive DupX := DupMk
}

ochr DupG {
  inductive DupX3 := DupX
}

ochr DupF {
  reject inductive DupSelf := DupSelf
}

namespace Ochr.Units
open Ochr.Test

/-- The verdicts of `bs`' declarations, checked as one program after the library: name,
accepted, and the start of the rejection's message. -/
def dupVerdicts (bs : List Ochr.Surface.Block) : List (String × Bool × String) :=
  let own := bs.flatMap (·.decls)
  (checkProgram (Prelude.decls ++ own) {} 2000000).drop Prelude.decls.length |>.map
    fun (n, v, _) => (n, v.ok, match v with | .rejected m _ => (m.splitOn ",").headD "" | .accepted => "" | .undecided m => m)

#guard dupVerdicts [DupA, DupB] ==
  [("DupX", true, ""), ("DupTy", true, ""), ("DupX", false, "DupX is already declared")]
#guard dupVerdicts [DupA, DupD] ==
  [("DupX", true, ""), ("DupTy", true, ""),
   ("DupX", false, "DupX is already declared"),
   ("DupTy", false, "DupTy is already declared"),
   ("DupC", false, "DupC is already declared")]
#guard dupVerdicts [DupA, DupE, DupG, DupF] ==
  [("DupX", true, ""), ("DupTy", true, ""),
   ("DupX", false, "DupX is already declared"),
   ("DupX3", false, "DupX3: the constructor name DupX is already used (constructors are resolved by name)"),
   ("DupSelf", false, "DupSelf: the constructor name DupSelf is already used (constructors are resolved by name)")]

end Ochr.Units

/-! ## A comparison keeps nothing but names (D103)

`conv`, `convPi` and `convFn` put back, on every exit, the state they started from, keeping only
the names made inside (the counters, the frozen readings, the new unknowns' types). Before D103 a
comparison kept the η-records its private copy made: comparing `Π(x : E1). match x { MkE1(e) =>
Nat }` with `Π(y : E1). Nat`, over `E1 := MkE1(e : Empty)`, refined the generic argument in
place (D93) and left a record naming an unknown of type `Empty`, after which no assignment of
the unknowns is typed (found by the rules trial, `Meaning/Rules/EmptyDomain.lean` on
`rules-trial`). Each comparison below answers `true`, adds its unknowns to the table (names are
never reused, D37) and now leaves no record. -/

namespace Ochr.Units

#guard_msgs (drop warning) in
ochr CompareEmpty uses Nats {
  inductive Empty : Type
  inductive E1 : Type := MkE1(e : Empty)
  def F (x : Empty) : Nat := Z
  def G (y : Empty) : Nat := Z
  def P2 : Type := Π(x : E1). (match x { MkE1(e) => Nat })
  def Q2 : Type := Π(y : E1). Nat
  def F3 (x : E1) (n : (match x { MkE1(e) => Nat })) : Nat := Z
  def G3 (y : E1) (m : (match y { MkE1(e) => Nat })) : Nat := Z
  def TAt (n : Nat) : Nat := ?
}

/-- The checker's state at the hole of `TAt`, after the block's declarations. -/
def cmpSt : MState :=
  let r := runWith (some Prelude) "CompareEmpty" CompareEmpty { recordStates := true } (located := true)
  match r.rows.find? (·.name == "TAt") with
  | some row => (row.trace.toList.filterMap fun
      | .state _ false _ st => some st | _ => none).getLast?.getD default
  | none => default

def cmpVal (n : String) : Value := ((cmpSt.globals.find? (·.name == n)).map (·.val)).getD .unit

/-- A comparison from `cmpSt`: its answer, how many unknowns it added, and how many records
(η and generalisation) it left. -/
def cmpLeaves (x : M Bool) : Option (Bool × Nat × Nat) :=
  match (runMachine x cmpSt 1000000).1 with
  | .ok b st' => some (b, st'.absTy.size - cmpSt.absTy.size,
      (st'.etaRefs.length - cmpSt.etaRefs.length) + (st'.neutrals.length - cmpSt.neutrals.length))
  | _ => none

#guard cmpSt.absTy.size == 1
#guard cmpLeaves (conv 100000 (.gfn "F") (.gfn "G")) == some (true, 1, 0)
-- before D103: `some (true, 2, 1)` and `some (true, 3, 1)`, a record naming the unknown of `Empty`
#guard cmpLeaves (conv 100000 (cmpVal "P2") (cmpVal "Q2")) == some (true, 2, 0)
#guard cmpLeaves (conv 100000 (.gfn "F3") (.gfn "G3")) == some (true, 3, 0)

end Ochr.Units

/-! ## The call-deferral flag is consumed when an evaluation starts (D130)

An untyped `let` of a call sets `deferCallTy`, so that the call records its callee's type and
arguments (`callTyLater`) and the binding's type is computed only if it is read. `evalAt` reads the
flag into the state the evaluation starts from (`deferHere`, which `evalCall` reads) and clears it,
as it does the other one-shot flags, and clears the record. Before D130 only `evalCall` cleared the
flag, so a flag left set was read by the next call the run made, whichever it was:
`let y = (Z; Add(x, 0)); y` from a state with the flag set bound `y` with no type. No run of a
program leaves the flag set; these runs start from a state that has it set. -/

namespace Ochr.Units

/-- An untyped run of `t` from the state after `Nats`, with `x ↦ 0 : Nat` bound and the type wanted
(as at a `let`'s right-hand side), the deferral flag and a stale record set as `stale` says: the
type it gives, and whether the flag and the record are set after it. -/
def deferRun (t : Term) (stale : Bool) : Option (Option Value × Bool × Bool) :=
  let fr : Frame := { binds := #[{ hint := ⟨"x"⟩, ty := some .tNat, val := .zero, decl := .other }] }
  let rec0 : Option (Value × List Value) := if stale then some (.tUnit, []) else none
  let s0 : MState := { st Nats 0 with env := #[fr], wantTy := true, deferCallTy := stale, callTyLater := rec0 }
  match (runMachine (Ochr.eval 1000 false t) s0 1000000).1 with
  | .ok (_, T) s => some (T, s.deferCallTy, s.callTyLater.isSome)
  | _ => none

/-- `Add(x, 0)`. -/
def addX : Term := .call (.const "Add") [.place (.var 0), .zero] false

-- a run consumes the flag; one with no call leaves no record (before D130 it left both set,
-- `some (some Nat, true, true)`)
#guard deferRun .zero true == some (some .tNat, false, false)
-- a call whose evaluation starts with the flag set is the deferred call: it gives no type and leaves
-- its record, for its `let` to read
#guard deferRun addX true == some (none, false, true)
-- the binding of `let y = (Z; Add(x, 0)); y` has its type (before D130 the call in the `;`'s tail read
-- the flag and deferred its type, and the `let`, not bound to a call, read no record: `y` was bound
-- with no type, and the run gave none though its type was wanted, `some (none, false, false)`)
#guard deferRun (.letIn ⟨"y"⟩ (.seq .zero addX) (.place (.var 0))) true == some (some .tNat, false, false)
-- a `let`'s tail never reads a flag its right-hand side's evaluation could have left: `let y = Z;
-- Add(y, 0)` from a state with the flag set (before D130 this held because the `let` cleared the flag
-- after its right-hand side; since D130 because the `let`'s own evaluation consumed it on entry)
#guard deferRun (.letIn ⟨"y"⟩ .zero addX) true == some (some .tNat, false, false)
-- a `let` of a call still defers its type to the binding, which gives it when read
#guard deferRun (.letIn ⟨"y"⟩ addX (.place (.var 0))) false == some (some .tNat, false, false)
#guard deferRun (.letIn ⟨"y"⟩ addX (.place (.var 0))) true == some (some .tNat, false, false)

end Ochr.Units

/-! ## A deferred call's head type is tested when the type is recorded (D134)

An untyped run computes a call's type, when wanted, with `declCallType`, which rejects a head type
that is not a function type written as one and a wrong arity. A `let` bound to the call defers the
type (D82, `callTyLater`), and that path recorded the head type untested, so the same call was
rejected outside a `let` and went on inside one with a record nobody could use. Since D134 both
paths make the one test (`callPi`). No surface program reaches the difference (the hunt: a parameter
refined by a split, a function behind a type function's result, a sealed function, an unknown at a
stuck type-function type, each called inside and outside a `let`, at the generic call, an instance
and a generic caller, all accepted alike), so it is pinned on a state: `f` holds `Add` but is stored
at a type that is not its own (the proof lane's `KindCE.stG`). -/

namespace Ochr.Units

/-- An untyped call `f(0, 0)` from the state after `Nats`, `f ↦ Add` stored at `T`, its type wanted,
deferred (as a `let` starts it) or not: its error, or its value, type and record. -/
def callKind (T : Value) (defer : Bool) : Except String (Value × Option Value × Option (Value × List Value)) :=
  let fr : Frame := { binds := #[{ hint := ⟨"f"⟩, ty := some T, val := .gfn "Add", decl := .other }] }
  let s0 : MState := { st Nats 0 with env := #[fr], wantTy := true, deferCallTy := defer }
  runM (do
    let (v, T') ← Ochr.eval 1000 false (.call (.place (.var 0)) [.zero, .zero] false)
    pure (v, T', (← get).callTyLater)) s0

/-- The error's message starts with `pre`. -/
def failsWith {α : Type} (r : Except String α) (pre : String) : Bool :=
  match r with
  | .error m => pre.isPrefixOf m
  | .ok _ => false

-- a head stored at `Nat`: rejected on both paths (before D134 the deferred one returned `0` with
-- no type and the record `(Nat, [0, 0])`)
#guard failsWith (callKind .tNat false) "not a function type: Nat"
#guard failsWith (callKind .tNat true) "not a function type: Nat"
-- a head stored at a function type of one parameter, called with two: rejected on both paths
#guard failsWith (callKind (.tPi [] (.pi [⟨"m"⟩] [.nat] .nat) []) false) "arity: 1 parameters, 2 arguments"
#guard failsWith (callKind (.tPi [] (.pi [⟨"m"⟩] [.nat] .nat) []) true) "arity: 1 parameters, 2 arguments"
-- at its own type, the deferred path records it, and the binding's type is computed when read
#guard match callKind (.tPi [] (.pi [⟨"x"⟩, ⟨"y"⟩] [.nat, .nat] .nat) []) true with
  | .ok (_, none, some (.tPi .., [.zero, .zero])) => true
  | _ => false

end Ochr.Units

/-! ## A function's own-name slot holds it only when it has `by` (D78, D148)

The first binding of a body's frame after the captures is the function's own-name slot. Since D148
it holds the function itself, at its Π-type, with a fresh mark (`Binding.recUid`, its [Rec]
entry's), only for a function that declares `by`: its body calls it, and [Rec] recognises the calls
by the mark. For every other function, a top-level definition without `by` or a local function,
the slot holds `()` at `Unit`, unnamed and unmarked, in the check of the body (`checkFix`) and at
every call (`runBodyCore`): its name is not in scope in its body (D31), and the consistency proof's
model has nothing there for the function itself. (D136's amendment had marked every function's
slot, holding the function; the proof's relation now finds a non-recursive function's slot by its
position.) Pinned on the states at each function's hole, and on hand-built core terms that read the
slot, which no checked body can (D31 rejects it in `checkFix`): only a body run without its check
reaches it, a closure or a global made by hand. -/

namespace Ochr.Units

#guard_msgs (drop warning) in
ochr SelfMarks uses Nats {
  -- a top-level definition that does not recurse
  def NR (n : Nat) : Nat := ?
  -- one that does
  def R (n : Nat) : Nat by n := match n { Z => ?, S(m) => R(m), }
  -- a local function (never recursive, D136) inside one that does not recurse, and inside one that does
  def L (n : Nat) : Nat := (fix go (y : Nat) : Nat := ?)(n)
  def RL (n : Nat) : Nat by n := match n { Z => (fix go (y : Nat) : Nat := ?)(n), S(m) => RL(m), }
}

/-- At each recorded state of `name`'s own code (`Config.recordStates`, located; its body, the
hole included): the own-name slot of the top frame (its first binding that is not a capture), as
its name, value, type and mark, and the marks of the [Rec] stack's entries. -/
def selfMarks (name : String) : List ((String × Value × Option Value × Option Nat) × List Nat) :=
  let r := runWith (some Prelude) "SelfMarks" SelfMarks { recordStates := true } (located := true)
  match r.rows.find? (·.name == name) with
  | some row => row.trace.toList.filterMap fun
      | .state _ false _ st => (st.env.back!.binds.find? (!·.cap)).map fun b =>
          ((b.hint.name, b.val, b.ty, b.recUid), st.recStack.map (·.uid))
      | _ => none
  | none => []

/-- The slot of a function without `by`: `()` at `Unit`, unnamed, unmarked. -/
def unitSlot : String × Value × Option Value × Option Nat → Bool
  | ("_", .unit, some .tUnit, none) => true
  | _ => false

-- the hole of a non-recursive global's body: its slot is `()`, and the [Rec] stack is empty (before
-- D148 it held the global, marked)
#guard !(selfMarks "NR").isEmpty && (selfMarks "NR").all fun (b, rs) => unitSlot b && rs.isEmpty
-- a recursive global: its slot holds it, at its Π-type, and its mark is its [Rec] entry's, the
-- only one on the stack
#guard !(selfMarks "R").isEmpty && (selfMarks "R").all fun
  | (("R", .gfn "R", some (.tPi ..), some m), rs) => rs == [m]
  | _ => false
-- a local function's slot is `()` too, and it has no [Rec] entry; inside a recursive global, the
-- stack holds the global's entry only
#guard !(selfMarks "L").isEmpty && (selfMarks "L").all fun (b, rs) => unitSlot b && rs.isEmpty
#guard (selfMarks "RL").any (fun (b, rs) => unitSlot b && rs.length == 1)

/-- A body made by hand that reads its own-name slot (`.var 1`, after the parameter `x`), with or
without `by`. -/
def readSelf (dec : Option Nat) : Term := .fix ⟨"g"⟩ [⟨"x"⟩] [.nat] .nat dec (.place (.var 1))

/-- The untyped call `f(0)` from the state after `Nats` with the global `G` made by hand from
`readSelf dec`: its value or its error. -/
def callSelf (f : Term) (dec : Option Nat) : String :=
  let G : GDef := { name := "G", ty := .tPi [] (.pi [⟨"x"⟩] [.nat] .nat) [], fn? := some (readSelf dec), val := .gfn "G" }
  match runM (do pure (← Ochr.eval 1000 false (.call f [.zero] false) none).1)
      { st Nats 0 with globals := globalsOf Nats ++ [G] } with
  | .ok v => s!"{v}"
  | .error m => m

-- a closure without `by` reads `()` in its slot (before D148: the closure itself)
#guard callSelf (.val (.clo [] (readSelf none) [])) none == "()"
-- a global without `by` likewise (before D148: `G`)
#guard callSelf (.const "G") none == "()"
-- a global with `by`: its slot holds it
#guard callSelf (.const "G") (some 0) == "G"

end Ochr.Units

/-! ## A definition without `by` enters Σ after its check (D147)

A constant is added to the globals after its body is checked; a function definition was added
before, with or without `by`. So during the check of a non-recursive `f`, `f ∈ Σ`, and the core term
`f(a)` ran `f`'s unchecked body in place. No source program reaches it (D31 takes `f` out of scope
in its body, D118 rejects a written name not in Σ, D55's pass rejects the embedded global), but the
consistency proof speaks of every core term at every state the check reaches. Since D147 only a
definition with `by` is in Σ during its own check (its body calls it); one without `by` is added
once its check succeeds, as a constant is. Pinned on the states the check of each body records
(`Config.recordStates`, located): there, the call `NR(0)` of the non-recursive `NR` names no global
(before D147 it ran `NR`'s body and gave `1`), while the recursive `R` is in Σ and `R(0)` closes off
(D135). After its check `NR` is in Σ and runs. -/

namespace Ochr.Units

#guard_msgs (drop warning) in
ochr InSigma uses Nats {
  def NR (n : Nat) : Nat := S(n)
  def R (n : Nat) : Nat by n := match n { Z => 0, S(m) => S(R(m)), }
  def NRRuns : Eq(Nat, NR(0), 1) := refl
}

/-- At each state recorded in `name`'s own code (`Config.recordStates`, located): whether `name` is
in Σ there, and what the untyped core call `name(0)` gives from that state (its value or its
error). -/
def inSigma (name : String) : List (Bool × String) :=
  let r := runWith (some Prelude) "InSigma" InSigma { recordStates := true } (located := true)
  match r.rows.find? (·.name == name) with
  | some row => row.trace.toList.filterMap fun
      | .state _ false _ st => some (st.globals.any (·.name == name),
          match runM (do pure (← Ochr.eval 1000 false (.call (.const name) [.zero] false) none).1) st with
          | .ok v => s!"{v}"
          | .error m => m)
      | _ => none
  | none => []

-- inside the check of the non-recursive `NR`: not in Σ, and `NR(0)` is an unknown name
#guard !(inSigma "NR").isEmpty && (inSigma "NR").all (· == (false, "unknown constant NR"))
-- inside the check of the recursive `R`: in Σ, and `R(0)` closes off (D135)
#guard !(inSigma "R").isEmpty && (inSigma "R").all (· == (true, "⌈R(0)⌉"))

end Ochr.Units
