import Ochr.Meaning.Steps.Machine.StoredTypeCE

/-!
# The kind facts are false at states the invariant admits (machine12, 2026-11-22; step 1 of the lead's brief)

The invariant's clause (K) (`Form.KindTyped`, docs/31 D188) asks nothing of a binding whose type is DEFERRED (`ty =
none`, `lazyTy = some (P, ws, j)`), and no clause of `Pre` (`CtxS`, `Inv`, `Asg`) says what a deferred type evaluates to,
or that a global's function body is one the checker accepted. Three facts stated over "every state meeting `Pre`" are
false there (each run below is the checker's own):

* `Master.EvalKindT` and `Master.EvalKindW` (READ FALSE as stated), the borrow part: at `stL` (`y ↦ loan_0 : Nat`,
  `x ↦ borrow_0(Z)` at the deferred type "parameter 0 of `Π(m : Nat). Nat` at `[Z]`", i.e. `Nat`; the readings
  `other`, label counter 1: machine11's `StoredTypeCE.stB` with `x`'s stored type deferred, so every clause of `Inv`
  holds as there, (K) asking nothing of `x`, (WF11) satisfied by a deferred type holding no loan) the typed read of
  `x`, and the untyped one with its type wanted, return `borrow_0(Z)` at `Nat` (`readL`): `bindTy?` evaluates the
  deferred type.
* `EvalKindT`'s function part: at `stG` (a real hole's state, `StoredTypeCE.st0F`, plus `f ↦ g`, the global function,
  at the same deferred type) the typed read of `f` returns `g` at `Nat` (`readG`).
* `Machine.LaterPiG` (READ FALSE as stated): at `stG`, the untyped call `f(Z)` with its type wanted and the deferral
  flag set (how a `let` starts it) returns `Z` with no type and records `(Nat, [Z])`, not a Π-type (`callG`). And
  WITHOUT a deferred type: at `stU` (the hole's state plus a fresh unknown `σ` whose own type is `Π(m : Nat). Nat`,
  held by `f` stored at `Nat`; (K) asks nothing of an unknown, and no clause ties a holder's stored type to its
  unknown's type) the same call returns the sealed `σ(Z)` with no type and records `(Nat, [Z])` (`callU`): the record
  is the head's stored type (`funType` returns `fT`), while the class is read off the unknown's own type (`clsTy`), so
  `declKind` does not reject it.
* `EvalKindT` (borrow part) again, at a global the checker never accepted: with `gb : Π(r : &Nat). Nat` whose body
  is `r` (`checkDef` rejects it), the typed call `gb(&x)` returns `borrow_0(0)` at `Nat` (`callGB`). `Pre`'s
  `CtxS.globals` constrains a global by its meaning only (its closure means a member of its type; the reference means
  a borrow by its content), so it does not exclude this; I did not check `GlobalsOk.mem` at a concrete model.

Every reachable state is fine: the sweep's clause (K) checks deferred types by evaluating them (none wrong in 1,029,853
states), its report on records finds every record a Π written as one, and an accepted global's body is typed.

Minimal restatements (the lead's call; each consumer needs more than one line, so none is made here):
1. (K) extended to deferred types, by evaluation: at a binding holding a borrow or a function value whose type is
   deferred, every successful `bindTy?` at it returns a type of the value's kind (a borrow at `&A`, a function value at
   a Π written as one). For borrows a syntactic form may do: the deferred domain or codomain is WRITTEN `&A` (a `.ref`
   term), since `&` in a term position is a borrow, never a type, so no type function returns a borrow type.
2. For `LaterPiG`, additionally a clause tying a neutral head's holder to the neutral's own type (an unknown's holder
   stores a Π written as one where the unknown's type is one), or `LaterPiG` asked only of a head that is a variable
   holding a function value.
3. For the ill-typed global: a clause "every global function's body is one `checkDef` accepted at its type", or the
   kind facts asked only of states whose globals the program's run made.
-/

namespace Ochr.Meaning.Steps.Machine.KindCE
open Ochr Ochr.Meaning Ochr.Test

def piNN : Value := .tPi [] (.pi [⟨"m"⟩] [.nat] .nat) []

/-- `y ↦ loan_0 : Nat`, `x ↦ borrow_0(Z)` at the deferred type "parameter 0 of `Π(m : Nat). Nat` at `[Z]`" (`Nat`). -/
def stL : MState :=
  { env := #[{ binds := #[{ hint := ⟨"y"⟩, ty := some .tNat, val := .loan 0 },
                          { hint := ⟨"x"⟩, ty := none, val := .borrow 0 .zero, lazyTy := some (piNN, [.zero], 0) }] }],
    nextLoan := 1 }

/-- The read of `x` (variable 0), its type wanted: typed, or untyped. -/
def readL (typed : Bool) : Option (Value × Option Value) :=
  match (runMachine (do
      modify fun s => { s with wantTy := true }
      Ochr.eval 100 typed (.place (.var 0)) none) stL 100000).1 with
  | .ok r _ => some r
  | _ => none

#guard readL true == some (.borrow 0 .zero, some .tNat)
#guard readL false == some (.borrow 0 .zero, some .tNat)

/-- A real hole's state (`StoredTypeCE.st0F`, `g` declared) plus `f ↦ g` at the same deferred type. -/
def stG : MState :=
  { StoredTypeCE.st0F with env := StoredTypeCE.st0F.env.modify (StoredTypeCE.st0F.env.size - 1) fun fr =>
    { fr with binds := fr.binds.push { hint := ⟨"f"⟩, ty := none, val := .gfn "g", lazyTy := some (piNN, [.zero], 0) } } }

def readG : Option (Value × Option Value) :=
  match (runMachine (do
      modify fun s => { s with wantTy := true }
      Ochr.eval 1000 true (.place (.var 0)) none) stG 1000000).1 with
  | .ok r _ => some r
  | _ => none

#guard readG == some (.gfn "g", some .tNat)

/-- The untyped call `f(Z)` as a `let`'s right-hand side starts it (type wanted, flag set): value, type, record. -/
def callAt (st : MState) : Option (Value × Option Value × Option (Value × List Value)) :=
  match (runMachine (do
      modify fun s => { s with wantTy := true, deferCallTy := true }
      let (v, T) ← Ochr.eval 1000 false (.call (.place (.var 0)) [.zero] false) none
      pure (v, T, (← get).callTyLater)) st 1000000).1 with
  | .ok r _ => some r
  | _ => none

#guard callAt stG == some (.zero, none, some (.tNat, [.zero]))

/-- The hole's state plus a fresh unknown `σ` of type `Π(m : Nat). Nat`, held by `f` stored at `Nat`. -/
def stU : MState :=
  let k := StoredTypeCE.st0F.nextAbs
  { StoredTypeCE.st0F with
    env := StoredTypeCE.st0F.env.modify (StoredTypeCE.st0F.env.size - 1) fun fr =>
      { fr with binds := fr.binds.push { hint := ⟨"f"⟩, ty := some .tNat, val := .abs k } },
    absTy := StoredTypeCE.st0F.absTy.push piNN, absDecl := StoredTypeCE.st0F.absDecl.push .other,
    nextAbs := k + 1 }

#guard match callAt stU with
  | some (.sealed _, none, some (T, [.zero])) => T == .tNat
  | _ => false

/-- A global the checker never accepted: `gb (r : &Nat) : Nat := r`. -/
def gBad : GDef :=
  { name := "gb", ty := .tPi [] (.pi [⟨"r"⟩] [.ref .nat] .nat) [],
    fn? := some (.fix ⟨"gb"⟩ [⟨"r"⟩] [.ref .nat] .nat none (.place (.var 0))), val := .gfn "gb" }

def stGB : MState := { env := #[{ binds := #[{ hint := ⟨"x"⟩, ty := some .tNat, val := .zero }] }], globals := [gBad] }

def callGB : Option (Value × Option Value) :=
  match (runMachine (do
      modify fun s => { s with wantTy := true }
      Ochr.eval 1000 true (.call (.const "gb") [.borrow (.var 0)] false) none) stGB 1000000).1 with
  | .ok r _ => some r
  | _ => none

#guard match callGB with
  | some (.borrow _ .zero, some T) => T == .tNat
  | _ => false

end Ochr.Meaning.Steps.Machine.KindCE
