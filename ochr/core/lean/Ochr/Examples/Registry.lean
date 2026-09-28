import Ochr.Examples.Units
import Ochr.Examples.E5
import Ochr.Examples.V15
import Ochr.Examples.V19
import Ochr.Examples.Inductives
import Ochr.Examples.Probes

/-! # Every example program, for the test runner and the counterfactual ledger -/

open Ochr Ochr.Test Ochr.Surface

namespace Ochr.Registry

def programs : List (String × Program) :=
  [("E1", E1), ("E2", E2), ("E3", E3), ("E4", E4), ("E5", E5), ("E6", E6), ("Attacks", Attacks), ("More", More), ("Probes", Probes), ("V15", V15), ("V17", V17), ("V18", V18), ("Positivity", Positivity), ("GenTy", GenTy), ("V19", V19), ("Inductives", Inductives),
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
  [("P2 (v1.3, D26): erased terms run on a private copy", { eraseOnCopy := false }),
   ("P2 without D41 (v1.8)", { eraseOnCopy := false, confine := false }),
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
   ("G1 (finding): a generalised neutral stays generalised under normalisation", { genConsistent := false }),
   ("D35 (v1.7): a function's class is read from its codomain term", { classBySyntax := false }),
   ("D35/D40: a stuck block is erased iff each arm is, not by the call rule", { blockRule := 0 }),
   ("D40 (P2): ... and not when its computed type has sort Prop", { blockRule := 1 }),
   ("D35 (v1.7): a let, sequence or match is erased iff it is a proof", { seqByProof := false }),
   ("D35 (v1.7): [Close]'s row is read from the declared codomain", { rowByDecl := false }),
   ("P1 (finding): a variable declared of sort Prop is a proof (redundant under D41)", { leafRule := 0 }),
   ("P1 without D41", { leafRule := 0, confine := false }),
   ("P3 (finding): ... by its declaration, not its value ⋆ (redundant under D41)", { leafRule := 1 }),
   ("P3 without D41", { leafRule := 1, confine := false }),
   ("P1 together with the computed-type block rule of P2", { blockRule := 1, leafRule := 0 }),
   ("D36 (v1.7): constructor fields are first-order data", { positivity := false }),
   ("D37 (v1.8): generalisation records and fresh names survive private copies", { globalRecords := false }),
   ("D38 (v1.8): a borrow result is observed through a fresh value written into it", { obsBorrow := false }),
   ("D39 (v1.8): [Seal]'s head guard covers neutral-headed calls", { headGuardNeutral := false }),
   ("D41 (v1.9): erased terms are confined", { confine := false }),
   ("extension (switched ON): bodies of erased-class functions and arms of erased blocks are confined", { confineBodies := true })]

end Ochr.Registry

/-- The total number of verdict assertions; a truncated example file changes it. -/
def Ochr.Registry.expectedTotal : Nat := 247

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
  ["E5.TwoPhase:rejected", "E6.LemmaMoves:rejected", "Probes.TypeErased:rejected"]
open Ochr.Registry in
#guard flips { eraseOnCopy := false, confine := false } ==
  ["E5.TwoPhase:rejected", "E6.LemmaMoves:rejected", "Attacks.N1T:accepted", "Attacks.N1Closed:accepted", "Attacks.Q:accepted", "Attacks.QBoom:accepted", "Probes.EffArg:accepted", "Probes.TypeErased:rejected", "V17.LieP:accepted", "V17.BoomP:accepted", "V19.Write:accepted", "V19.Borrow:accepted", "V19.Move:accepted"]
open Ochr.Registry in
#guard flips { multiOwner := false } ==
  ["D18.BadD18:accepted", "D18.ClosedD18:accepted", "D18.GR:accepted", "D18.BadR:accepted"]
open Ochr.Registry in
#guard flips { recGuard := false } ==
  ["Attacks.Loop:accepted", "Attacks.Bot':accepted", "Attacks.Loop2:accepted", "Attacks.Spin:accepted", "Attacks.KnotL:accepted", "Attacks.KnotLBoom:accepted", "Probes.OuterBad:accepted"]
open Ochr.Registry in
#guard flips { accessInside := false } ==
  ["Attacks.BadA1:accepted"]
open Ochr.Registry in
#guard flips { selfHeadOnly := false } ==
  ["Attacks.Knot:accepted", "Attacks.KnotBoom:accepted"]
open Ochr.Registry in
#guard flips { argNotBot := false } ==
  ["More.Dead:accepted", "More.DeadTwice:accepted"]
open Ochr.Registry in
#guard flips { generalize := false } ==
  ["More.MatchAfterOpaque:rejected", "GenTy.GenL:rejected", "Inductives.InsertM:rejected", "Inductives.Insert:rejected", "Inductives.InsertMEq:rejected", "Inductives.InsertMSwap:rejected", "Inductives.SizeInsert:rejected"]
open Ochr.Registry in
#guard flips { blockMoves := false } ==
  ["Probes.MovedByBlock:accepted"]
open Ochr.Registry in
#guard flips { proofParamsStar := false } ==
  ["E5.ProofIrr:rejected"]
open Ochr.Registry in
#guard flips { recNested := false } ==
  ["Attacks.KnotL:accepted", "Attacks.KnotLBoom:accepted"]
open Ochr.Registry in
#guard flips { erasureByDecl := false } ==
  ["Probes.TypeErased:rejected", "V15.MainW0:rejected", "V17.TruthB:rejected", "V17.LieG:accepted", "V17.TruthG:rejected", "V17.SeqT:rejected", "V17.RowI:accepted", "V18.LieH:rejected"]
open Ochr.Registry in
#guard flips { matchEndsInside := false } ==
  ["V15.Bad:accepted", "V15.Main:accepted"]
open Ochr.Registry in
#guard flips { closureConv := 2 } ==
  ["V15.Boom3:accepted"]
open Ochr.Registry in
#guard flips { unboundWithoutBy := false } ==
  ["V15.Loop:accepted", "V15.Boom4:accepted"]
open Ochr.Registry in
#guard flips { patternWritesVisible := false } ==
  ["V15.Clear:accepted", "V15.Boom5:accepted"]
open Ochr.Registry in
#guard flips { genConsistent := false } ==
  ["Inductives.InsertMEq:rejected", "Inductives.SizeInsert:rejected"]
open Ochr.Registry in
#guard flips { classBySyntax := false } ==
  ["V17.BoomL:accepted", "V17.TruthG:rejected", "V18.Boom8:accepted", "V18.Direct8:accepted", "V18.LieH:rejected"]
open Ochr.Registry in
#guard flips { blockRule := 0 } ==
  ["V17.LieB:accepted", "V17.BoomB:accepted", "V17.TruthB:rejected", "V17.LieG:accepted", "V17.BoomG:accepted", "V17.TruthG:rejected", "V18.Lie7:accepted", "V18.Boom7:accepted"]
open Ochr.Registry in
#guard flips { blockRule := 1 } ==
  ["V17.LieG:accepted", "V17.BoomG:accepted", "V17.TruthG:rejected"]
open Ochr.Registry in
#guard flips { seqByProof := false } ==
  ["V17.SeqT:rejected"]
open Ochr.Registry in
#guard flips { rowByDecl := false } ==
  ["V17.RowI:accepted"]
open Ochr.Registry in
#guard flips { leafRule := 0 } ==
  []
open Ochr.Registry in
#guard flips { leafRule := 0, confine := false } ==
  ["Attacks.N1T:accepted", "Attacks.Q:accepted", "Probes.EffArgErased:accepted", "V19.Write:accepted", "V19.Borrow:accepted", "V19.Move:accepted"]
open Ochr.Registry in
#guard flips { leafRule := 1 } ==
  []
open Ochr.Registry in
#guard flips { leafRule := 1, confine := false } ==
  ["Attacks.N1T:accepted", "Attacks.Q:accepted", "Probes.EffArgErased:accepted", "V17.LieP:accepted", "V18.BoomH:accepted", "V19.Write:accepted", "V19.Borrow:accepted", "V19.Move:accepted"]
open Ochr.Registry in
#guard flips { blockRule := 1, leafRule := 0 } ==
  ["V17.LieP:accepted", "V17.BoomP:accepted", "V17.LieG:accepted", "V17.BoomG:accepted", "V17.TruthG:rejected"]
open Ochr.Registry in
#guard flips { positivity := false } ==
  ["Positivity.Bad:accepted", "Positivity.L:accepted", "Positivity.K:accepted", "Positivity.bad:accepted", "Positivity.Boom:accepted"]
open Ochr.Registry in
#guard flips { globalRecords := false } ==
  ["V18.Esc:accepted", "V18.BoomE:accepted"]
open Ochr.Registry in
#guard flips { obsBorrow := false } ==
  ["V18.ConvPick:accepted", "V18.TY:accepted", "V18.BoomX4:accepted"]
open Ochr.Registry in
#guard flips { headGuardNeutral := false } ==
  ["V18.P1:rejected"]
open Ochr.Registry in
#guard flips { confine := false } ==
  ["Attacks.N1T:accepted", "Attacks.Q:accepted", "Probes.EffArgErased:accepted", "V17.LieP:accepted", "V19.Write:accepted", "V19.Borrow:accepted", "V19.Move:accepted"]
open Ochr.Registry in
#guard flips { confineBodies := true } ==
  ["E4.TwiceMZero':rejected", "Attacks.P2:rejected", "Attacks.FP2:rejected", "Attacks.BoomIsTrue:rejected", "Attacks.p2:rejected", "Attacks.TA2:rejected", "Probes.F5:rejected", "Probes.TypeErased:rejected", "V17.F:rejected", "V17.SeqT:rejected", "V19.TailSteps:rejected"]
-- `genPlaceType` changes no verdict; V18.lean asserts its effect on the generalised σ's type
