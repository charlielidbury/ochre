import Ochr.Examples.Registry

namespace Ochr.Registry

/-- A row's class is checked with its flips: a completeness row flips only to rejected,
any other row flips its named witnesses to accepted. -/
def classOk (k : String) (ws fs : List String) : Bool :=
  if k == "completeness" then !fs.isEmpty && fs.all (·.endsWith ":rejected")
  else ws.all fun w => fs.contains s!"{w}:accepted"

/-- One ledger row: switching `c` off flips exactly `e`, and `e` fits the row's class. -/
def rowOk (c : Config) (e : List String) : Bool :=
  let fs := flips c
  fs == e && match (switches.zip rowClass).find? (fun ((_, c'), _) => reprStr c' == reprStr c) with
    | some (_, (k, ws)) => classOk k ws fs
    | none => false

end Ochr.Registry

/-! ## The counterfactual ledger (asserted)

Switching one rule off flips exactly the verdicts below and nothing else. (v1's P5
switch, `p5 := false`, is not in the ledger: since v1.3 skipping a proof is an
optimisation of P2, and in this checker switching it off also switches off the `⋆`
representation of proofs, so its row would not isolate one rule.) -/
open Ochr.Registry in
#guard rowOk { eraseOnCopy := false }
  ["CurrentState.TwoPhase:rejected", "Erasure.LemmaMoves:rejected", "Erasure.TypeErased:rejected"]
open Ochr.Registry in
#guard rowOk { eraseOnCopy := false, confine := false }
  ["Subsingletons.EffInline:accepted", "CurrentState.TwoPhase:rejected", "Erasure.LemmaMoves:rejected",
   "Erasure.TypeErased:rejected", "Erasure.EffArg:accepted", "Erasure.Write:accepted",
   "Erasure.Borrow:accepted", "Erasure.Move:accepted", "Erasure.N1T:accepted", "Erasure.N1Closed:accepted",
   "Erasure.Q:accepted", "Erasure.QBoom:accepted", "ErasureBySyntax.LieP:accepted",
   "ErasureBySyntax.BoomP:accepted"]
open Ochr.Registry in
#guard rowOk { multiOwner := false }
  ["Owners.BadD18:accepted", "Owners.ClosedD18:accepted", "Owners.GR:accepted", "Owners.BadR:accepted"]
open Ochr.Registry in
#guard rowOk { recGuard := false }
  ["Recursion.Loop:accepted", "Recursion.Bot':accepted", "Recursion.Loop2:accepted",
   "Recursion.Spin:accepted", "Recursion.OuterBad:accepted", "Recursion.KnotL:accepted",
   "Recursion.KnotLBoom:accepted"]
open Ochr.Registry in
#guard rowOk { accessInside := false }
  ["Borrows.BadA1:accepted"]
open Ochr.Registry in
#guard rowOk { selfHeadOnly := false }
  ["Recursion.Knot:accepted", "Recursion.KnotBoom:accepted"]
open Ochr.Registry in
#guard rowOk { argNotBot := false }
  ["Borrows.Dead:accepted", "Borrows.DeadTwice:accepted"]
open Ochr.Registry in
#guard rowOk { generalize := false }
  ["CaseSplits.MatchAfterOpaque:rejected", "GenType.GenL:rejected", "Trees.InsertM:rejected",
   "Trees.Insert:rejected", "Trees.InsertMEq:rejected", "Trees.InsertMSwap:rejected",
   "Trees.SizeInsert:rejected"]
open Ochr.Registry in
#guard rowOk { blockMoves := false }
  ["ClosingOff.MovedByBlock:accepted"]
open Ochr.Registry in
#guard rowOk { proofParamsStar := false }
  ["Propositions.AndTrue:rejected", "Propositions.Swap:rejected", "Propositions.Fst:rejected",
   "Propositions.FstSwap:rejected", "Propositions.AndL2:rejected", "Propositions.Snd:rejected",
   "Propositions.Twice:rejected", "Propositions.SplitId:rejected", "Propositions.TwoOwners:rejected",
   "Propositions.TwoOwnersR:rejected", "Propositions.ThreeOwners:rejected", "Subsingletons.OrComm:rejected",
   "Subsingletons.OrElim:rejected", "Subsingletons.OrLet:rejected", "CurrentState.ProofIrr:rejected"]
open Ochr.Registry in
#guard rowOk { recNested := false }
  ["Recursion.KnotL:accepted", "Recursion.KnotLBoom:accepted"]
open Ochr.Registry in
#guard rowOk { erasureByDecl := false }
  ["ClosingOff.RowI:accepted", "Erasure.TypeErased:rejected", "ErasureBySyntax.MainW0:rejected",
   "ErasureBySyntax.TruthB:rejected", "ErasureBySyntax.LieG:accepted", "ErasureBySyntax.TruthG:rejected",
   "ErasureBySyntax.SeqT:rejected", "ErasureBySyntax.LieH:rejected"]
open Ochr.Registry in
#guard rowOk { matchEndsInside := false }
  ["ReturnedBorrows.Bad:accepted", "ReturnedBorrows.Main:accepted"]
open Ochr.Registry in
#guard rowOk { closureConv := 2 }
  ["Functions.Boom3:accepted", "Functions.CoInd:accepted"]
open Ochr.Registry in
#guard rowOk { unboundWithoutBy := false }
  ["Recursion.LoopNoBy:accepted", "Recursion.LoopNoByBoom:accepted"]
open Ochr.Registry in
#guard rowOk { patternWritesVisible := false }
  ["ClosingOff.Clear:accepted", "ClosingOff.Boom5:accepted"]
open Ochr.Registry in
#guard rowOk { genConsistent := false }
  ["Trees.InsertMEq:rejected", "Trees.SizeInsert:rejected"]
open Ochr.Registry in
#guard rowOk { classBySyntax := false }
  ["ErasureBySyntax.BoomL:accepted", "ErasureBySyntax.Boom8:accepted", "ErasureBySyntax.Direct8:accepted",
   "ErasureBySyntax.TruthG:rejected", "ErasureBySyntax.LieH:rejected"]
open Ochr.Registry in
#guard rowOk { blockRule := 0 }
  ["ErasureBySyntax.LieB:accepted", "ErasureBySyntax.BoomB:accepted", "ErasureBySyntax.TruthB:rejected",
   "ErasureBySyntax.Lie7:accepted", "ErasureBySyntax.Boom7:accepted", "ErasureBySyntax.LieG:accepted",
   "ErasureBySyntax.BoomG:accepted", "ErasureBySyntax.TruthG:rejected"]
open Ochr.Registry in
#guard rowOk { blockRule := 1 }
  ["ErasureBySyntax.LieG:accepted", "ErasureBySyntax.BoomG:accepted", "ErasureBySyntax.TruthG:rejected"]
open Ochr.Registry in
#guard rowOk { seqByProof := false }
  ["ErasureBySyntax.SeqT:rejected"]
open Ochr.Registry in
#guard rowOk { rowByDecl := false }
  ["ClosingOff.RowI:accepted"]
open Ochr.Registry in
#guard rowOk { leafRule := 0 }
  ["Snapshots.CapP:rejected", "Snapshots.CapP2:rejected", "Subsingletons.OrLet:rejected"]
open Ochr.Registry in
#guard rowOk { leafRule := 0, confine := false }
  ["Snapshots.CapP:rejected", "Snapshots.CapP2:rejected", "Subsingletons.OrLet:rejected",
   "Subsingletons.EffInline:accepted", "Erasure.EffArgErased:accepted", "Erasure.Write:accepted",
   "Erasure.Borrow:accepted", "Erasure.Move:accepted", "Erasure.N1T:accepted", "Erasure.Q:accepted"]
open Ochr.Registry in
#guard rowOk { leafRule := 1 }
  ["Snapshots.CapP:rejected", "Snapshots.CapP2:rejected"]
open Ochr.Registry in
#guard rowOk { leafRule := 1, confine := false }
  ["Snapshots.CapP:rejected", "Snapshots.CapP2:rejected", "Subsingletons.EffInline:accepted",
   "Erasure.EffArgErased:accepted", "Erasure.Write:accepted", "Erasure.Borrow:accepted",
   "Erasure.Move:accepted", "Erasure.N1T:accepted", "Erasure.Q:accepted", "ErasureBySyntax.LieP:accepted",
   "ErasureBySyntax.BoomH:accepted"]
open Ochr.Registry in
#guard rowOk { blockRule := 1, leafRule := 0 }
  ["Snapshots.CapP:rejected", "Snapshots.CapP2:rejected", "Subsingletons.OrLet:rejected",
   "ErasureBySyntax.LieG:accepted", "ErasureBySyntax.BoomG:accepted", "ErasureBySyntax.TruthG:rejected",
   "ErasureBySyntax.LieP:accepted", "ErasureBySyntax.BoomP:accepted"]
open Ochr.Registry in
#guard rowOk { positivity := false }
  ["Positivity.Bad:accepted", "Positivity.L:accepted", "Positivity.K:accepted", "Positivity.bad:accepted",
   "Positivity.Boom:accepted", "PositivityParams.Bad:accepted", "PositivityParams.L:accepted",
   "PositivityParams.K:accepted", "PositivityParams.bad:accepted", "PositivityParams.Boom:accepted",
   "PositivityParams.Neg:accepted", "PositivityPaper.Bad:accepted", "PositivityPaper.L:accepted",
   "PositivityPaper.Bad4:accepted"]
open Ochr.Registry in
#guard rowOk { globalRecords := false }
  ["GlobalRecords.Esc:accepted", "GlobalRecords.Bad5:accepted"]
open Ochr.Registry in
#guard rowOk { obsBorrow := false }
  ["Functions.ConvPick:accepted", "Functions.TY:accepted", "Functions.BoomX4:accepted"]
open Ochr.Registry in
#guard rowOk { headGuardNeutral := false }
  ["ReturnedBorrows.Inj:rejected", "ClosingOff.P1:rejected", "BorrowTypes.HO:rejected"]
open Ochr.Registry in
#guard rowOk { confine := false }
  ["Subsingletons.EffInline:accepted", "Erasure.EffArgErased:accepted", "Erasure.Write:accepted",
   "Erasure.Borrow:accepted", "Erasure.Move:accepted", "Erasure.N1T:accepted", "Erasure.Q:accepted",
   "ErasureBySyntax.LieP:accepted"]
open Ochr.Registry in
#guard rowOk { confineBodies := true }
  ["ReturnedBorrows.Inj:rejected", "Snapshots.CapPi:rejected", "Functions.TwiceMZero':rejected",
   "Erasure.F5:rejected", "Erasure.TypeErased:rejected", "Erasure.TailSteps:rejected", "Erasure.P2:rejected",
   "Erasure.FP2:rejected", "Erasure.BoomIsTrue:rejected", "Erasure.p2:rejected", "Erasure.TA2:rejected",
   "ErasureBySyntax.F:rejected", "ErasureBySyntax.SeqT:rejected"]
open Ochr.Registry in
#guard rowOk { borrowParam := false }
  ["ReturnedBorrows.LeakT:accepted", "ReturnedBorrows.Q:accepted", "ReturnedBorrows.Boom:accepted",
   "ReturnedBorrows.QF:accepted"]
open Ochr.Registry in
#guard rowOk { capTypes := false }
  ["Snapshots.CapS:rejected", "Snapshots.CapSId:rejected", "Snapshots.CapPi:rejected",
   "Snapshots.CapP:rejected", "Snapshots.CapP2:rejected"]
-- `genPlaceType` changes no verdict; 08CaseSplits.lean asserts its effect on the generalised σ's type
-- v2.0 D45 by type, switched off: a match on a proof inspects its content (⋆) like data: completeness only
open Ochr.Registry in
#guard rowOk { byType := false }
  ["Propositions.AndTrue:rejected", "Propositions.Swap:rejected", "Propositions.Fst:rejected",
   "Propositions.FstSwap:rejected", "Propositions.AndL2:rejected", "Propositions.Snd:rejected",
   "Propositions.Twice:rejected", "Propositions.SplitId:rejected", "Propositions.TwoOwners:rejected",
   "Propositions.TwoOwnersR:rejected", "Propositions.ThreeOwners:rejected", "Propositions.FromTrue:rejected",
   "Propositions.FromTrueIs:rejected", "Propositions.Two:rejected", "Propositions.TwoIs:rejected",
   "Propositions.WriteIf:rejected", "Propositions.WriteIfId:rejected", "Propositions.WriteIfAt:rejected",
   "Propositions.TwoAt:rejected", "Subsingletons.OrComm:rejected", "Subsingletons.OrElim:rejected",
   "Subsingletons.OrLet:rejected", "Subsingletons.SqTrue:rejected", "Subsingletons.SqSplit:rejected",
   "Subsingletons.EffL:rejected", "Subsingletons.EffLNoop:rejected"]
-- v2.0 D45 subsingleton elimination, switched off: large elimination from Or and Sq is accepted (IsL, Get have no
-- model; OrLie is Eq Bool tt ff in the model), but no closed False: D42 erases the constructor it would inspect
open Ochr.Registry in
#guard rowOk { subsingleton := false }
  ["Subsingletons.IsL:accepted", "Subsingletons.Irr:accepted", "Subsingletons.OrLie:accepted",
   "Subsingletons.Get:accepted", "Subsingletons.SqIrr:accepted"]
-- v2.0 D42 for constructors, switched off: Prop constructor applications are data values, not proofs (completeness)
open Ochr.Registry in
#guard rowOk { propValues := false }
  ["Subsingletons.OrComm:rejected", "Subsingletons.SqTrue:rejected", "Subsingletons.SqSplit:rejected",
   "Subsingletons.EffL:rejected", "Subsingletons.EffLNoop:rejected"]
-- both off: the closed proofs of False (Subsingletons.Boom, SqBoom) go through
open Ochr.Registry in
#guard rowOk { subsingleton := false, propValues := false }
  ["Subsingletons.EffLNoop:rejected", "Subsingletons.EffInline:accepted", "Subsingletons.IsL:accepted",
   "Subsingletons.Irr:accepted", "Subsingletons.Boom:accepted", "Subsingletons.Get:accepted",
   "Subsingletons.SqIrr:accepted", "Subsingletons.SqBoom:accepted"]
-- v2.0 D47 switched off: Eq Nat Z (S Z) is irreducible again, so False and Eq Nat 0 1 part ways
open Ochr.Registry in
#guard rowOk { disjoint := false }
  ["ReturnedBorrows.L:rejected", "ReturnedBorrows.Inj:rejected", "ReturnedBorrows.PF:rejected",
   "Equality.NotAdd01:rejected", "Equality.WriteNeq:rejected", "Equality.WriteDisj:rejected",
   "Equality.NoConf:rejected", "Equality.NoConfS:rejected", "Equality.NoConfMatch:rejected",
   "Equality.NoConfBack:rejected", "Equality.BoolDisj:rejected"]
-- finding (v2.0 round): v1.9 assumed a data match's scrutinee type from its arms
open Ochr.Registry in
#guard rowOk { scrutTyped := false }
  ["ScrutineeTypes.f:accepted", "ScrutineeTypes.g:accepted"]
-- D48 (1) switched off: &Type makes Type₀ impredicative (System U⁻), and &Prop, &True, &Π, &A pass
open Ochr.Registry in
#guard rowOk { refData := false }
  ["Universes.Impred:accepted", "Universes.PolyId:accepted", "Universes.SelfApp:accepted",
   "Universes.SelfAppEq:accepted", "Universes.PolyTy:accepted", "BorrowTypes.PIref:accepted",
   "BorrowTypes.RefTrue:accepted", "BorrowTypes.RefFun:accepted", "BorrowTypes.SwapT:accepted"]
-- D48 (2) switched off: a codomain computing to &Nat; the accepted G reads ⊥ at n = 0
open Ochr.Registry in
#guard rowOk { refTop := false }
  ["BorrowTypes.InPair:accepted", "BorrowTypes.F:accepted", "BorrowTypes.G:accepted"]
-- D48 (3) switched off: Π-types compared by captures and code (reviewer-3 C3)
open Ochr.Registry in
#guard rowOk { piUnder := false }
  ["Functions.Cap:rejected", "Functions.CapEq:rejected", "Functions.P1:rejected", "Functions.P3:rejected",
   "Functions.PassZeroAdd:rejected", "Functions.PassA:rejected"]
-- D49 (3) switched off: a data field of a matched proof is ⋆, and cannot be split
open Ochr.Registry in
#guard rowOk { proofDataFields := false }
  ["Subsingletons.SqSplit:rejected"]
-- D50 switched off (normalising unit laws, as v2.0 was first built): True ∧ P loses its And
open Ochr.Registry in
#guard rowOk { unitNorm := true }
  ["Propositions.AndTrue:rejected"]

-- every row of `switches` has a class
open Ochr.Registry in
#guard rowClass.length == switches.length
