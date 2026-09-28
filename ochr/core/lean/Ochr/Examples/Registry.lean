import Ochr.Examples.Units
import Ochr.Examples.Probes

/-! # Every example program, for the test runner and the counterfactual ledger -/

open Ochr Ochr.Test Ochr.Surface

namespace Ochr.Registry

def programs : List (String × Program) :=
  [("E1", E1), ("E2", E2), ("E3", E3), ("E4", E4), ("E6", E6), ("Attacks", Attacks), ("More", More), ("Probes", Probes),
   ("D18", Ochr.Units.D18)]

def reports (cfg : Config := {}) : List Report := programs.map fun (n, p) => run n p cfg

/-- The declarations whose verdict under `cfg` differs from the default, as
`program.name:verdict`. -/
def flips (cfg : Config) : List String := Id.run do
  let mut out := []
  for (base, alt) in (reports {}).zip (reports cfg) do
    for (r, r') in base.rows.zip alt.rows do
      if r.verdict.ok != r'.verdict.ok then
        out := out ++ [s!"{base.program}.{r.name}:{if r'.verdict.ok then "accepted" else "rejected"}"]
  pure out

/-- Each switch disables one rule; the ledger records what it was guarding. -/
def switches : List (String × Config) :=
  [("P5 (D14): calls at a proposition are not run", { p5 := false }),
   ("D18: owners are sets", { multiOwner := false }),
   ("D17: [Rec] entry-value guard", { recGuard := false }),
   ("D19: [Access] ends loans inside the content", { accessInside := false }),
   ("L1: self only as a call head", { selfHeadOnly := false }),
   ("L2: no ⊥ argument", { argNotBot := false }),
   ("C8: generalise before splitting on a sealed program", { generalize := false }),
   ("C5: a stuck block moves in a borrow variable an arm moves", { blockMoves := false })]

end Ochr.Registry

/-! ## The counterfactual ledger (asserted)

Switching one rule off flips exactly the verdicts below and nothing else. An empty
entry means no example depends on the rule (D18: see notes/lean-checker.md §4; its
effect is asserted directly in `Units.lean`). -/

open Ochr.Registry in
#guard flips { p5 := false } == ["E4.TwiceMZero':rejected", "Attacks.FP2:rejected", "Attacks.BoomIsTrue:rejected"]
open Ochr.Registry in
#guard flips { multiOwner := false } == []
open Ochr.Registry in
#guard flips { recGuard := false } ==
  ["Attacks.Loop:accepted", "Attacks.Bot':accepted", "Attacks.Loop2:accepted", "Attacks.Spin:accepted",
   "Attacks.KnotL:accepted", "Attacks.KnotLBoom:accepted", "Probes.OuterBad:accepted"]
open Ochr.Registry in
#guard flips { accessInside := false } == ["Attacks.BadA1:accepted"]
open Ochr.Registry in
#guard flips { selfHeadOnly := false } == ["Attacks.Knot:accepted", "Attacks.KnotBoom:accepted"]
open Ochr.Registry in
#guard flips { argNotBot := false } == ["More.Dead:accepted", "More.DeadTwice:accepted"]
open Ochr.Registry in
#guard flips { generalize := false } == ["More.MatchAfterOpaque:rejected"]
open Ochr.Registry in
#guard flips { blockMoves := false } == ["Probes.MovedByBlock:accepted"]
