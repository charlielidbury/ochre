import Ochr.Meaning.Steps.Statements
import Ochr.Examples.Nat

/-!
# The fit of a value to its reading, at the checker's own state (lead27, 2026-11-22; docs/31 D185)

`Master.EvalFitsT` (`Steps/MasterLet.lean`): the value a typed evaluation returns fits the table's reading of its term
(`FitsAt`: at every place under the binding a `let` gives it, a place read as an inductive holds one of its
constructors or a stand-in, and a place holding `⋆` is read as a copy). Pinned here at the hole of a real program,
for the kinds of right-hand side a `let` binds: a constructor, a read that moves a constructor out, a read of an
unknown, a match closed off as a block, a proof. Each check is a computation of the checker (`declOf` for the term's
reading, `placeDecl` for a field under the new binding); each is paired with a wrong expectation that fails.
-/

open Ochr.Test

#guard_msgs (drop warning) in
ochr FitAt uses Nats {
  inductive B := T | F
  inductive Box := MkBox(b : B)
  def At (c : B) (x : Box) : Unit := (let y = MkBox(T); ?)
}

namespace Ochr.Meaning.Steps.FitGuards

open Ochr Ochr.Meaning Ochr.Meaning.Steps

/-- The checker's state at `At`'s hole: `c ↦ σ` (variable 2), `x ↦ σ'` (variable 1), `y ↦ MkBox(T)` (variable 0). -/
def stAt : MState :=
  let r := Ochr.Test.runWith (some Prelude) "FitAt" FitAt { recordStates := true } (located := true)
  match r.rows.find? (·.name == "At") with
  | some row => (row.trace.toList.filterMap fun
      | .state _ false _ st => some st | _ => none).getLast?.getD default
  | none => default

/-- The typed run of `u` as a `let`'s right-hand side (the type wanted, no hint): its value. -/
def valT (u : Term) : Option Value :=
  match (runMachine (do
      modify fun s => { s with wantTy := true }
      pure (← Ochr.eval 1000 true u none).1) stAt 1000000).1 with
  | .ok v _ => some v
  | _ => none

/-- The table's reading of `u` in the hole's scope (the checker's `declOf`). -/
def readT (u : Term) : Option DeclInfo :=
  match (runMachine (withLive true (Ochr.declOf 1000 false [] [] u)) stAt 1000000).1 with
  | .ok d _ => some d
  | _ => none

/-- The reading of a place under a new binding read `du`, in the hole's scope (the checker's `placeDecl`). -/
def placeT (du : DeclInfo) (p : Place) : Option DeclInfo :=
  match (runMachine (withLive true (Ochr.placeDecl 1000 (du :: DecideScope.topReadings stAt) p)) stAt 1000000).1 with
  | .ok d _ => some d
  | _ => none

/-- Whether a reading is the inductive `n`. -/
def isInd (n : String) : Option DeclInfo → Bool
  | some (.ind m _) => m == n
  | _ => false

def fieldB : FieldRef := ⟨"Box", 0, 0, "b"⟩
abbrev mkBox (t : Term) : Term := .ctor "Box" 0 ⟨"MkBox"⟩ [] [t]
abbrev ctorF : Term := .ctor "B" 1 ⟨"F"⟩ [] []

-- a constructor: `MkBox(F)` is read `Box`, its value is a `Box`, and its field `b` is read `B` and holds a `B`
#guard isInd "Box" (readT (mkBox ctorF))
#guard ((valT (mkBox ctorF)).map (Value.fitsInd "Box")) == some true
#guard ((valT (mkBox ctorF)).map (Value.fitsInd "B")) == some false
#guard (readT (mkBox ctorF)).any fun du => isInd "B" (placeT du (.field fieldB (.var 0)))
#guard ((valT (mkBox ctorF)).bind (·.follow [.field fieldB])).map (Value.fitsInd "B") == some true
#guard ((valT (mkBox ctorF)).bind (·.follow [.field fieldB])).map (Value.fitsInd "Box") == some false
-- a read that moves a constructor out: `y` is read `Box` and holds `MkBox(T)`
#guard isInd "Box" (readT (.place (.var 0)))
#guard ((valT (.place (.var 0))).map (Value.fitsInd "Box")) == some true
#guard ((valT (.place (.var 0))).map (Value.fitsInd "B")) == some false
-- a read of an unknown: `x` is read `Box` and holds a stand-in (an unknown), which fits any inductive
#guard isInd "Box" (readT (.place (.var 1)))
#guard ((valT (.place (.var 1))).map (Value.fitsInd "Box")) == some true
#guard ((valT (.place (.var 1))).map fun v => match v with | .abs _ => true | _ => false) == some true
-- a match on an unknown, closed off as a block: read `B`, its value a sealed program (a stand-in)
#guard isInd "B" (readT (.matchInd (.var 2) "B" [(⟨"T"⟩, ctorF), (⟨"F"⟩, .ctor "B" 0 ⟨"T"⟩ [] [])]))
#guard ((valT (.matchInd (.var 2) "B" [(⟨"T"⟩, ctorF), (⟨"F"⟩, .ctor "B" 0 ⟨"T"⟩ [] [])])).map
  fun v => match v with | .sealed _ => true | _ => false) == some true
-- a number is not read as an inductive (nothing to fit), and a number does not fit `B` (the guard distinguishes)
#guard !isInd "B" (readT .zero)
#guard ((valT .zero).map (Value.fitsInd "B")) == some false

end Ochr.Meaning.Steps.FitGuards
