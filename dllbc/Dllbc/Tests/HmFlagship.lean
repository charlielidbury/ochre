import Dllbc.Program
import Dllbc.Boundary
import Dllbc.ProgMacro
import Dllbc.Std
import Dllbc.StdLemmas
import Dllbc.Tests.Diff
import Dllbc.Tests.Direct

/-!
# The hashmap flagship — `docs/13-hashmap-flagship.md`

A verified, resizable, in-place hashmap mirroring the Aeneas ICFP'22 case study
(`competitors/aeneas-hashmap/`). See the problem statement for the fixed layout, ops,
specs, and acceptance battery; this file is staged S1 (fixed-capacity, full specs) →
S2 (resize) → S3 (twins + differential + writeup).

## §0 — the ported arithmetic (`hm-probe-mod`, verified here against current `main`)

`Mod`/`Div`/`Mul` and the two lemmas a slot access needs (`ModLtN`, `ModDec`) now
live in `StdLemmas.lean`, ported verbatim from the probe. This section re-runs the
probe's own `chkL` checks against THIS tree, so a divergence between the probe's base
commit and current `main` is caught here rather than three ops downstream.
-/

open Dllbc
open Dllbc.StdLemmas (LeRefl LeTrans LeAdd LeAddL LeAddSucc LeRwL LeRwR AddSucc AddZero
  IdTrans IdCongr IdSym Znots LebTrueLe LebFalseGt LePredL EqbRefl EqbGtFalse EqbLtFalse
  NatRw
  NextR NextC NextQ ModC Mod DivC Div Mul StepInv StepInvTy ModCLt ModCLtTy
  ModLtN ModLtNTy ModDec ModDecTy)

namespace Dllbc.Tests.HmFlagship

/-- Type-check a closed term against a closed type in the pure seed (ArraySort's `chkL`). -/
def chkL (tm ty : Term) : Bool :=
  match (do let v ← readC 8000 tm; let t ← readC 8000 ty; hasTypeT 8000 v t).run (seedPure [] []) with
  | .ok r _ => r
  | .error _ _ => false

def pv (t : Term) : Term := Pure.nf 4000000 t
def modOf (a b : Nat) : Term := pv prog{ Mod %(Term.nat a) %(Term.nat b) }
def divOf (a b : Nat) : Term := pv prog{ Div %(Term.nat a) %(Term.nat b) }

example : (modOf 7 3).natOf? == some 1 := by native_decide
example : (modOf 0 3).natOf? == some 0 := by native_decide
example : (divOf 7 3).natOf? == some 2 := by native_decide

-- The Aeneas hashmap's own `test1` keys at its own capacity: `0, 128, 1024, 1056`
-- all land in slot 0 of 32, which is what makes that test exercise the collision list.
example : (modOf 0 32).natOf? == some 0 := by native_decide
example : (modOf 128 32).natOf? == some 0 := by native_decide
example : (modOf 1024 32).natOf? == some 0 := by native_decide
example : (modOf 1056 32).natOf? == some 0 := by native_decide

example : chkL StepInv StepInvTy = true := by native_decide
example : chkL ModCLt ModCLtTy = true := by native_decide
example : chkL ModLtN ModLtNTy = true := by native_decide
example : chkL ModDec ModDecTy = true := by native_decide

end Dllbc.Tests.HmFlagship
