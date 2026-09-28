import Ochr.Examples.Units
import Ochr.Examples.E5
import Ochr.Examples.V15
import Ochr.Examples.Inductives
import Ochr.Examples.Probes

/-! # Every example program, for the test runner and the counterfactual ledger -/

open Ochr Ochr.Test Ochr.Surface

namespace Ochr.Registry

def programs : List (String × Program) :=
  [("E1", E1), ("E2", E2), ("E3", E3), ("E4", E4), ("E5", E5), ("E6", E6), ("Attacks", Attacks), ("More", More), ("Probes", Probes), ("V15", V15), ("Inductives", Inductives),
   ("D18", Ochr.Units.D18)]

def reports (cfg : Config := {}) (fuel : Nat := 2000000) : List Report :=
  programs.map fun (n, p) => run n p cfg fuel

/-- The declarations whose verdict under `cfg` differs from the default, as
`program.name:verdict`. -/
def flips (cfg : Config) : List String := Id.run do
  let mut out := []
  -- counterfactual runs may not terminate (e.g. without [Rec]); a smaller fuel bounds them
  for (base, alt) in (reports {} 300000).zip (reports cfg 300000) do
    for (r, r') in base.rows.zip alt.rows do
      if r.verdict.ok != r'.verdict.ok then
        out := out ++ [s!"{base.program}.{r.name}:{if r'.verdict.ok then "accepted" else "rejected"}"]
  pure out

/-- Each switch disables one rule; the ledger records what it was guarding. -/
def switches : List (String × Config) :=
  [("P2 (v1.3, D26): proofs run on a private copy", { eraseOnCopy := false }),
   ("D18: owners are sets", { multiOwner := false }),
   ("D17: [Rec] entry-value guard", { recGuard := false }),
   ("D19: [Access] ends loans inside the content", { accessInside := false }),
   ("L1: self only as a call head", { selfHeadOnly := false }),
   ("L2: no ⊥ argument", { argNotBot := false }),
   ("C8: generalise before splitting on a sealed program", { generalize := false }),
   ("C5: a stuck block moves in a borrow variable an arm moves", { blockMoves := false }),
   ("D27 (v1.4): proof parameters are ⋆ at the generic call", { proofParamsStar := false }),
   ("L3 (v1.3): [Rec] covers nested functions", { recNested := false }),
   ("D28 (v1.5): erasure by declared class, not by value", { erasureByDecl := false }),
   ("D29 (v1.5): matching ends loans inside a neutral head", { matchEndsInside := false }),
   ("D30 (v1.5): closures compared by generic-call observation (vs result only)", { closureConv := 2 }),
   ("D31 (v1.5): without `by`, f is not in scope", { unboundWithoutBy := false }),
   ("D32 (v1.5): writes through pattern variables are writes to the scrutinee", { patternWritesVisible := false }),
   ("G1 (finding): a generalised neutral stays generalised under normalisation", { genConsistent := false })]

end Ochr.Registry

/-- The total number of verdict assertions; a truncated example file changes it. -/
def Ochr.Registry.expectedTotal : Nat := 185

open Ochr.Registry Ochr.Test in
#guard ((reports {}).map Report.count).foldl (· + ·) 0 == expectedTotal
open Ochr.Registry Ochr.Test in
#guard (reports {}).all Report.allAsExpected

/-! ## The counterfactual ledger (asserted)

Switching one rule off flips exactly the verdicts below and nothing else. (v1's P5
switch, `p5 := false`, is not in the ledger: since v1.3 skipping a proof is an
optimisation of P2, and in this checker switching it off also switches off the `⋆`
representation of proofs, so its row would not isolate one rule.) -/

open Ochr.Registry in
#guard flips { eraseOnCopy := false } ==
  ["E5.TwoPhase:rejected", "E6.LemmaMoves:rejected", "Attacks.N1Closed:accepted", "Attacks.QBoom:accepted",
   "Probes.EffArg:accepted", "Probes.EffArgErased:rejected", "Probes.TypeErased:rejected"]
open Ochr.Registry in
#guard flips { multiOwner := false } ==
  ["D18.BadD18:accepted", "D18.ClosedD18:accepted", "D18.GR:accepted", "D18.BadR:accepted"]
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
#guard flips { generalize := false } ==
  ["More.MatchAfterOpaque:rejected", "Inductives.InsertM:rejected", "Inductives.Insert:rejected",
   "Inductives.InsertMEq:rejected", "Inductives.InsertMSwap:rejected", "Inductives.SizeInsert:rejected"]
open Ochr.Registry in
#guard flips { blockMoves := false } == ["Probes.MovedByBlock:accepted"]
open Ochr.Registry in
#guard flips { proofParamsStar := false } == ["E5.ProofIrr:rejected"]
open Ochr.Registry in
#guard flips { recNested := false } == ["Attacks.KnotL:accepted", "Attacks.KnotLBoom:accepted"]
open Ochr.Registry in
#guard flips { erasureByDecl := false } == ["V15.Boom:accepted", "V15.MainW0:rejected"]
open Ochr.Registry in
#guard flips { matchEndsInside := false } == ["V15.Bad:accepted", "V15.Main:accepted"]
open Ochr.Registry in
#guard flips { closureConv := 2 } == ["V15.Boom3:accepted"]
open Ochr.Registry in
#guard flips { unboundWithoutBy := false } == ["V15.Loop:accepted", "V15.Boom4:accepted"]
open Ochr.Registry in
#guard flips { patternWritesVisible := false } == ["V15.Clear:accepted", "V15.Boom5:accepted"]
open Ochr.Registry in
#guard flips { genConsistent := false } == ["Inductives.InsertMEq:rejected", "Inductives.SizeInsert:rejected"]
