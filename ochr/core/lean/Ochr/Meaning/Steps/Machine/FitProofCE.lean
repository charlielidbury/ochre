import Ochr.Meaning.Steps.Statements
import Ochr.Examples.Nat

/-!
# A proof read as data: `EvalFitsT` and the invariant's (C⋆) are false (machine11, 2026-11-22)

READ FALSE: `Master.EvalFitsT` (`Steps/MasterLet.lean`), its second clause (C⋆), and with it the invariant's
`ShapeFacts.proofCopy` at a state the checker reaches. Behind it, a CHECKER BUG: the generic call and an instance
disagree.

`J(Nat, a, b, λ(x : Nat) : PropF(x) => ⊤, h, refl)` with `PropF (n : Nat) : Type₁ := Prop`. Its type `P(b)` is the
proposition `⊤`, and its value is `⋆` (`valT uJ`). But the motive's codomain `PropF(x)` is a call of a type function
whose body is a sort, and `typeFnDecl` reads only a Π-type or data through a body ("a body that computes to a sort or a
proposition keeps the call's declared reading"), so the codomain reads `other` (the call's declared type `Type₁` is not
`Prop`), the motive reads `Π → other` (not `Π → Prop`), `jErased` says no, and `declOf` of the `J` is `other`:
data, not a copy (`declCopy .other = false`). So a `let` of it binds `⋆` at a reading that is not a copy: (C⋆) fails
at the new binding's root (no step, so `GrainOk` holds), and `EvalFitsT`'s `FitsAt` fails at `p = var 0`.

The checker itself goes wrong at the join: a read of `⋆` never moves it (`readPlace`'s `v == .proof` exit), but the
join's moved places are decided from readings (`jdMoves` adds a place whose reading is not a copy), so at an instance a
match on a known number drops `y` (writes `⊥`) where the generic call, whose stuck block takes `y` through a read,
leaves `⋆`. `V1` is accepted; its call `V2 := V1(Z)` is REJECTED ("[Read] y was moved out … (reading ⊥)"). With the
codomain written `Prop` (`V3`, `V4`) both are accepted (the controls).

Minimal fixes, for the lead: in the checker, read a type function's call whose body reads a sort as that sort for the
erasure class (here `PropF(x)` as `Prop`), or require a codomain whose declared type is a universe above `Prop` and
whose value is a sort to be written as a sort (D128's rule, for a function's codomain); in the facts, nothing smaller:
the invariant's (C⋆) is itself false after the `let`.
-/

open Ochr.Test

ochr FitProofCE uses Nats {
  def PropF (n : Nat) : Type₁ := Prop
  def V1 (k : Nat) : Unit := (let y = J(Nat, Z, Z, λ(x : Nat) : PropF(x) => ⊤, refl, refl); match k { Z => (let z = y; ()), S(j) => () }; let w = y; ())
  -- BUG: the generic call accepts `V1`, its instance rejects it (the join drops the `⋆` read as data)
  reject def V2 : Unit := V1(Z)
  -- controls: the codomain written `Prop`
  def V3 (k : Nat) : Unit := (let y = J(Nat, Z, Z, λ(x : Nat) : Prop => ⊤, refl, refl); match k { Z => (let z = y; ()), S(j) => () }; let w = y; ())
  def V4 : Unit := V3(Z)
}

#guard (Ochr.Test.runWith (some Prelude) "FitProofCE" FitProofCE {} (located := false)).allAsExpected

#guard_msgs (drop warning) in
ochr FitProofAt uses Nats {
  def PropF (n : Nat) : Type₁ := Prop
  def W3 (a : Nat) (b : Nat) (h : Eq(Nat, a, b)) : Unit := ?
}

namespace Ochr.Meaning.Steps.Machine.FitProofCE
open Ochr Ochr.Meaning Ochr.Meaning.Steps

/-- The checker's state at `W3`'s hole: `a ↦ σ0` (variable 2), `b ↦ σ1` (variable 1), `h ↦ ⋆` (variable 0). -/
def stW : MState :=
  let r := Ochr.Test.runWith (some Prelude) "FitProofAt" FitProofAt { recordStates := true } (located := true)
  match r.rows.find? (·.name == "W3") with
  | some row => (row.trace.toList.filterMap fun
      | .state _ false _ st => some st | _ => none).getLast?.getD default
  | none => default

/-- `λ(x : Nat) : PropF(x) => ⊤`. -/
def lamP : Term := .fix ⟨"P"⟩ [⟨"x"⟩] [.nat] (.call (.const "PropF") [.place (.var 0)] false) none (.tind "True" [])
/-- `J(Nat, a, b, λ(x : Nat) : PropF(x) => ⊤, h, refl)` at the hole's scope. -/
def uJ : Term := .prim "J" [.nat, .place (.var 2), .place (.var 1), lamP, .place (.var 0), .ctor "True" 0 ⟨"I"⟩ [] []]

/-- The typed run of `u` as a `let`'s right-hand side (the type wanted, no hint): its value. -/
def valT (u : Term) : Option Value :=
  match (runMachine (do
      modify fun s => { s with wantTy := true }
      pure (← Ochr.eval 1000 true u none).1) stW 1000000).1 with
  | .ok v _ => some v
  | _ => none

/-- The checker's reading of `u` in the hole's scope (`declOf`), and whether a reading is a copy (`declCopy`). -/
def readT (u : Term) : Option DeclInfo :=
  match (runMachine (withLive true (Ochr.declOf 1000 false [] [] u)) stW 1000000).1 with
  | .ok d _ => some d
  | _ => none
def copyT (d : DeclInfo) : Option Bool :=
  match (runMachine (Ochr.declCopy 1000 d) stW 1000000).1 with
  | .ok c _ => some c
  | _ => none

-- the typed run returns `⋆`
#guard valT uJ == some .proof
-- the term is read `other` (the motive `Π → other`), which is not a copy
#guard (readT uJ).any (· matches .other)
#guard (readT lamP).any (· matches .pi .other)
#guard (readT uJ).bind copyT == some false
-- control: with the codomain written `Prop` the motive reads `Π → Prop`, the term `prop`, a copy
def lamQ : Term := .fix ⟨"P"⟩ [⟨"x"⟩] [.nat] (.sort 0) none (.tind "True" [])
def uJQ : Term := .prim "J" [.nat, .place (.var 2), .place (.var 1), lamQ, .place (.var 0), .ctor "True" 0 ⟨"I"⟩ [] []]
#guard (readT uJQ).any (· matches .prop)
#guard (readT uJQ).bind copyT == some true

end Ochr.Meaning.Steps.Machine.FitProofCE
