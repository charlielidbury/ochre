import Ochr.Meaning.Regress.EqJ

/-!
# The rules trial: the decisions do not agree on convertible terms (compiled checks)

The term-level part of [Conv-cong] (closure code, sealed programs) needs the model's run of two
convertible programs to agree. The run reads the decision table at terms (`K.D.declOf`,
`K.D.flags`, the copy decision through `placeDecl`), and `CtxOk.dec` makes that table the
checker's. The existing congruences do not cover this: `run_congr` changes the future,
`run_congrA` the assignment, and `SubstAbs` replaces ONE unknown by a value of the same meaning and
run type under `DecInvariantAbs` (the decisions do not see that substitution). The smallest
invariance [Conv-cong] would need is the same for every pair of convertible embedded values: the
decisions agree on terms that differ only by convertible embedded values.

It is false of the checker's decisions. `F (n : Nat) : Unit := ()` and `H (n : Nat) : TF(Z) := ()`
with `TF(n) := match n { Z => Unit, S _ => Nat }` are convertible (same Π-type after computing,
same observation), but the declared reading of `F` is `Π … . Unit` and of `H` is `Π … . other`
(a type that is `Unit` only by computation is not read as `Unit`, D80), so the calls `F(0)` and
`H(0)`, convertible by [Conv-cong], read `unit` and `other`: copy and not copy. The checker itself
treats them apart: it accepts `let x = F(0); Mk(x, x)` and rejects `let x = H(0); Mk(x, x)` ("x was
moved out", verdicts asserted by the build). In the model the two programs' runs read the same
decisions, so they differ the same way (a guess: the model's run of either is not computed here).
So [Conv-cong] on programs is not sound for the model's run as it stands: two convertible programs
need not run alike.
-/

open Ochr.Test
#guard_msgs (drop warning) in
ochr DecAt uses Nats {
  def UnitAlias : Type := Unit
  def F (n : Nat) : Unit := ()
  def G (n : Nat) : UnitAlias := ()
  def TF (n : Nat) : Type := match n { Z => Unit, S _ => Nat }
  def H (n : Nat) : TF(Z) := ()
  def UseF : Pair(Unit, Unit) := let x = F(0); Mk(x, x)
  reject def UseH : Pair(Unit, Unit) := let x = H(0); Mk(x, x)
  def EqFG : Eq(Π(n : Nat). Unit, F, G) := refl
  def TAt (n : Nat) : Nat := ?
}
namespace DecProbe
open Ochr
def stT : MState :=
  let r := Ochr.Test.runWith (some Prelude) "DecAt" DecAt { recordStates := true } (located := true)
  match r.rows.find? (·.name == "TAt") with
  | some row => (row.trace.toList.filterMap fun
      | .state _ false _ st => some st | _ => none).getLast?.getD default
  | none => default
def show' {α : Type} [ToString α] (x : M α) : String :=
  match (runMachine x stT 1000000).1 with
  | .ok a _ => s!"ok {a}"
  | .fail _ => s!"fail"
  | .exhausted m => s!"exhausted {m}"
partial def dpp : DeclInfo → String
  | .sort l => s!"sort {l}" | .prop => "prop" | .pi c => s!"pi({dpp c})" | .ref a => s!"ref({dpp a})"
  | .unit => "unit" | .ind n _ => s!"ind {n}" | .alt _ => "alt" | .other => "other" | .any => "any"
  | .conflict => "conflict"
instance : ToString DeclInfo := ⟨dpp⟩
#guard show' (Ochr.conv 100000 (.gfn "F") (.gfn "G")) == "ok true"
#guard show' (withLive true (Ochr.declOf 1000 false [] [] (.val (.gfn "F")))) == "ok pi(unit)"
#guard show' (withLive true (Ochr.declOf 1000 false [] [] (.call (.val (.gfn "F")) [.zero] false))) == "ok unit"
#guard show' (Ochr.conv 100000 (.gfn "F") (.gfn "H")) == "ok true"
#guard show' (withLive true (Ochr.declOf 1000 false [] [] (.val (.gfn "H")))) == "ok pi(other)"
#guard show' (withLive true (Ochr.declOf 1000 false [] [] (.call (.val (.gfn "H")) [.zero] false))) == "ok other"
end DecProbe
