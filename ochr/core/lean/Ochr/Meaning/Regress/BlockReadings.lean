import Ochr.Meaning.Steps.ParGuards
import Ochr.Meaning.DecisionsInst

/-!
# A closed-off block whose parameter's stored reading differs from its type value's reading (lead19, 2026-11-21; docs/31 D143)

docs/31 D137 ruled (A) (the model's `CapsOk` reads a closure value's captures against the first readings only) and
recorded (B) as the endpoint: the `.clo` clause should hand `rd.drop caps.length` to the `.fix` run as the parameters'
declared readings, as the checker does, instead of the decision `paramDecls` on the domain terms (`.val T`, the
stored type VALUES). (A) alone is wrong exactly where a block takes a place whose DECLARED reading (`placeDecl`, frozen
in `rd` by `closeBlock`) differs from the reading of its type's value.

The candidate named in D137, main's `FrozenReadings.KeepTP` (`h : TP(n)`, `TP` proposition-valued), is NOT one: there
`h` is a proof (`⋆`, read `.prop`) and `match k { Z => h, S _ => h }` is itself a proof, so no block is closed off; and
where a block does take such a proof place (`A1` below) the domain is ascribed `(⌈TP(σ0)⌉ : Prop)`, whose reading is
`.prop` too. **The smallest accepted program found where they differ** is `A3`: a parameter `f : TF2(n)` whose type
function is a Π-type at every index but is stuck at `σ0`, kept through a block:

  `def A3 (n : Nat) (f : TF2(n)) (k : Nat) : TF2(n) := (let r = match k { Z => f, S _ => f }; r)`

The checker stores `f`'s reading `.pi .other` (its declaration `TF2(n)`); the reading of its type's value
`⌈TF2(σ0)⌉`, as the checker's own `typeDecl` decides it (what `DecTab.typeDecl` aligns the model's `paramDecls` with),
is `.other`. This is the test (B) must pass: the model's run of the block's code should bind `f` at `.pi .other`.
Whether the difference changes any run's outcome is not established: the block's body only moves `f`, and a call of
`f` inside the block is rejected by the checker (`A2`: "not a function type").

Every `#guard` runs the checker (compiled, not kernel-checked).
-/

open Ochr.Test

ochr BlockReadingsProbe {
  def TP (n : Nat) : Prop := match n { Z => True, S _ => True }
  def TF2 (n : Nat) : Type := match n { Z => Π(m : Nat). Nat, S _ => Π(m : Nat). Nat }
  def A1 (n : Nat) (h : TP(n)) (k : Nat) : Nat := (let r = match k { Z => (h; 0), S _ => 1 }; r)
  reject def A2 (n : Nat) (f : TF2(n)) (k : Nat) : Nat := (let r = match k { Z => f(0), S _ => f(1) }; r)
  def A3 (n : Nat) (f : TF2(n)) (k : Nat) : TF2(n) := (let r = match k { Z => f, S _ => f }; r)
}

namespace Ochr.Meaning.Regress.BlockReadings

open Ochr Ochr.Meaning Ochr.Meaning.Steps.Form
open Ochr.Meaning.Regress.GenNeutralContent (isOk outSt outVal)

#guard (Ochr.Test.run "BlockReadingsProbe" BlockReadingsProbe).rejectedWith [("A2", "not a function type")]

/-- The checker's recorded states on entry to the located terms of a declaration (with the Prelude). -/
def entriesP (name : String) : List MState :=
  let r := Ochr.Test.runWith (some Prelude) BlockReadingsProbe.name BlockReadingsProbe { recordStates := true } (located := true)
  match r.rows.find? (·.name == name) with
  | some row => row.trace.toList.filterMap fun
      | .state _ false _ st => some st | _ => none
  | none => []

/-- The body's start state: the first recorded state whose top frame binds the function and its three parameters. -/
def startOf (name : String) : MState :=
  ((entriesP name).find? fun st => (st.env.toList.getLast?.map (·.binds.size)).getD 0 == 4).getD {}

/-- The block: the right-hand side of the body's `let`. -/
def blockOf (name : String) : Term :=
  match ParGuards.bodyOf BlockReadingsProbe name with
  | .letIn _ u _ => u
  | _ => .zero

/-- The block's value, run as the checker runs it from the body's start state. -/
def blockVal (name : String) : Value := (outVal (Ochr.eval 1000 true (blockOf name) none) (startOf name) 100000).1

/-- The block's stored readings (`rd`) and its code's domains, read off its value. -/
def rdOf : Value → List DeclInfo
  | .sealed (.call (.val (.clo _ _ rd)) _ _) => rd.map (·.1)
  | _ => []
def domsOf : Value → List Term
  | .sealed (.call (.val (.clo _ (.fix _ _ ds _ _ _) _)) _ _) => ds
  | _ => []

/-- The readings the model's `.fix` run gives the block's parameters: `paramDecls [] doms`, each domain's reading
decided by the checker's `typeDecl` at the scope of the earlier ones (what `DecTab.typeDecl` aligns the table with), at
the state after the block. -/
def modelReadings (name : String) : List DeclInfo := Id.run do
  let st := outSt (Ochr.eval 1000 true (blockOf name) none) (startOf name) 100000
  let mut sc : List DeclInfo := []
  for d in domsOf (blockVal name) do
    sc := outVal (withLive true (Ochr.typeDecl 100 false [] [] d)) (scopeState st sc) 1000 :: sc
  pure sc.reverse

def isPiOther : DeclInfo → Bool
  | .pi .other => true
  | _ => false
def isOther : DeclInfo → Bool
  | .other => true
  | _ => false
def isProp : DeclInfo → Bool
  | .prop => true
  | _ => false

-- `A3`: the block is closed off, called on `f`'s and `k`'s unknowns
#guard isOk (Ochr.eval 1000 true (blockOf "A3") none) (startOf "A3") 100000
#guard match blockVal "A3" with
  | .sealed (.call (.val (.clo [] (.fix _ [f, k] [_, _] _ none _) [_, _])) [.val (.abs 1), .val (.abs 2)] true) =>
    f.name == "f" && k.name == "k"
  | _ => false
-- **the checker stores `f` at `.pi .other`; the reading of its type's value is `.other`**
#guard match rdOf (blockVal "A3") with | [d₁, d₂] => isPiOther d₁ && isOther d₂ | _ => false
#guard match modelReadings "A3" with | [d₁, d₂] => isOther d₁ && isOther d₂ | _ => false
-- `A1`: a block that takes a proof place; the domain is ascribed `(⌈TP(σ0)⌉ : Prop)`, both readings `.prop`
#guard match rdOf (blockVal "A1") with | [d₁, d₂] => isProp d₁ && isOther d₂ | _ => false
#guard match modelReadings "A1" with | [d₁, d₂] => isProp d₁ && isOther d₂ | _ => false

end Ochr.Meaning.Regress.BlockReadings
