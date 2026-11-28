import Ochr.Meaning.Steps.StageBlockCE
import Ochr.Meaning.Steps.UnderCheckAttack

/-!
# A λ that calls the function under check captures it at its declared type: D232's obstruction with no block
(spine-exp-block, lead38; docs/31 D237)

The checker lane's probe `CL` (checker14's report, item (d)), on `main` and on `exp-block-text` alike: a λ formed inside
a recursive definition that calls the definition CAPTURES the definition's own binding, so the closure value holds the
global as a captured value at the binding's DECLARED type. Pinned here at the smallest program whose λ is formed at
every assignment (so at the knot's first bound): `CL0 (m n : Nat) : Nat by n := let g = (λ(j : Nat) : Nat => match n {
Z => Z, S k => CL0(j, clone(k)) }); ?` (accepted; and `CL0r`, which returns `g(m)`). At the hole:
`g ↦ fix _ (j : Nat) : Nat := match κ2 { Z => 0, S _ => κ1(j, clone(κ2.0)) } where κ1 = CL0, κ2 = σ1`, the capture `κ1`
recorded at reading `.pi .other` and type `Π(m : Nat) (n : Nat). Nat`; and `CL0 ↦ ⊥`, `n ↦ ⊥` (K1: the capture moves
them).

**The obstruction, the same as `MB0r`'s (D232) with no block.** Under the knot's context `K_b` the definition means its
stage-`b` closure at the WEAKENED function type. The model reads the checker's closure value `g` by `meanV`'s `.clo`
clause, STRICT: `CapsOk` asks each captured value to be a member of its recorded type, here the stage closure a member
of the declared `Π(m : Nat) (n : Nat). Nat`. At bound `0` it is not (`StageBlock.stage0_not_mem`, kernel-checked;
`capsOk_stage0` below), so `g` means `err`; the reference's direct run forms the λ from its own state, where the
function's binding holds the stage closure at the weakened type, and gets a member (at `n = 0` its function is `0`
everywhere). So the relation fails at `g`, and for `CL0r` at the leaf `g(m)` (the checker closes the call off, its
meaning `err`; the reference's `0`). The link from `meanV` of the recorded type value to `piTyAt _ 1 psMB natOut` is by
reading (the `.pi` clause at `Nat`, `Nat`, sort `1`), as D232's link was.

**The repair, by the same principle** (a function under check occurs only as the head of a call; D139's first part,
which `exp-block-text` builds for blocks): a closure formed in the body of a function under check names that function
in its code by its GLOBAL (`Term.inlineReads` with `.val (.gfn f)`, as `closeBlock` does), and does not keep it as a
capture; the capture is still TAKEN as K1 says (the binding moved on every path, as for a block), only not kept. Then the
model's `.clo` clause never asks the stage closure's membership: the call in the λ's body reads the global's meaning and
`callOf` applies it along its own type, at arguments of rank below the bound (here `k`, a part of `n`). What it changes:
the code and capture list of such closures (printing; conversion of two closures of the definition under check, which
now compare the global in the code instead of a capture), nothing about moves; no verdict expected to change (the
global is the binding's value since D136). Not built (a checker change, main and the experiment alike).
-/

open Ochr.Test

#guard_msgs (drop warning) in
ochr LamAtk {
  def CL (m : Nat) (n : Nat) : Nat by n := match n { Z => Z, S k => (let g = (λ(j : Nat) : Nat => CL(j, clone(k))); let r = (match m { Z => g(Z), S q => Z }); ?) }
  def CL0 (m : Nat) (n : Nat) : Nat by n := (let g = (λ(j : Nat) : Nat => match n { Z => Z, S k => CL0(j, clone(k)) }); ?)
  def CL0r (m : Nat) (n : Nat) : Nat by n := (let g = (λ(j : Nat) : Nat => match n { Z => Z, S k => CL0r(j, clone(k)) }); g(m))
}

namespace Ochr.Meaning.Steps.Form.LamCapture

open Ochr Ochr.Meaning

/-- Every environment a hole of definition `nm` reports. -/
def holes (nm : String) : List (List (String × Option Value × Value)) :=
  let r := Ochr.Test.runWith (some Prelude) "LamAtk" LamAtk {} (located := true)
  match r.rows.find? (·.name == nm) with
  | some row => row.trace.toList.filterMap fun
      | .note _ _ (.hole _ Ω) => some Ω | _ => none
  | none => []

/-- The innermost binding named `x` at a hole. -/
def valOf (Ω : List (String × Option Value × Value)) (x : String) : Option Value :=
  (Ω.reverse.find? (·.1 == x)).map (·.2.2)

/-- `CL0`'s declared type as the checker stores it. -/
def piMB : Value := .tPi [] (.pi [⟨"m"⟩, ⟨"n"⟩] [.nat, .nat] .nat) []

/-- The closure's captures hold the global `CL0` at reading `.pi .other` and its declared type, then `σ1` at `Nat`. -/
def capturesGlobal : Value → Bool
  | .clo [.gfn "CL0", .abs 1] _ [(.pi .other, T), (.other, .tNat)] => T == piMB
  | _ => false

-- all three accepted
#guard (Ochr.Test.runWith (some Prelude) "LamAtk" LamAtk {} (located := false)).allAsExpected
-- at `CL0`'s hole: `g` captures the function under check at its declared type; the capture moved `CL0` and `n`
#guard (holes "CL0").map (fun Ω => (valOf Ω "g").map capturesGlobal) == [some true]
#guard (holes "CL0").map (fun Ω => (valOf Ω "CL0", valOf Ω "n")) == [(some .bot, some .bot)]
#guard (holes "CL0").map (fun Ω => (valOf Ω "g").map toString) ==
  [some "fix _ (j : Nat) : Nat := match κ2 { Z => 0, S _ => κ1(j, clone(κ2.0)) } where κ1 = CL0, κ2 = σ1"]

end Ochr.Meaning.Steps.Form.LamCapture

namespace Ochr.Meaning.Steps.StageBlock

open Ochr Ochr.Meaning

/-- **The model's strict reading of `g` fails at bound `0`**: a capture list whose first value is the stage-`0` closure
of a function of type `Π(m : Nat) (n : Nat). Nat`, recorded at that declared type, is not `CapsOk` (so the closure
value means `err`, `meanV`'s `.clo` clause). -/
theorem capsOk_stage0 (R : DataRead) (rk : List Sem → Nat) (φ : Future) (g : List Sem → Option BodyOut)
    (d : DeclInfo) (vs : List Sem) (ts : List (DeclInfo × TyS)) :
    ¬ CapsOk R (closureAt R 1 φ psMB (weakCod 1 rk 0 natOut) g :: vs) ((d, .plain (piTyAt R 1 psMB natOut)) :: ts) :=
  fun h => stage0_not_mem R rk φ g h.1

end Ochr.Meaning.Steps.StageBlock
