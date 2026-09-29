import Ochr.Examples.Registry

namespace Ochr.Registry

/-- A row's class is checked with its flips: a completeness row flips only to rejected, a
subsumed row flips nothing, any other row flips its named witnesses to accepted. -/
def classOk (k : String) (ws fs : List String) : Bool :=
  if k == "completeness" then !fs.isEmpty && fs.all (·.endsWith ":rejected")
  else if k == "subsumed" then fs.isEmpty
  else ws.all fun w => fs.contains s!"{w}:accepted"

/-- One ledger row: switching `c` off flips exactly `e`, blocks exactly `bl` (declarations
that fail only because a library declaration they use flipped; none so far), and `e` fits
the row's class. -/
def rowOk (c : Config) (e : List String) (bl : List String := []) : Bool :=
  let (fs, bs) := flipsDetail c
  fs == e && bs == bl && match (switches.zip rowClass).find? (fun ((_, c'), _) => reprStr c' == reprStr c) with
    | some (_, (k, ws)) => classOk k ws fs
    | none => false

end Ochr.Registry

/-! ## The counterfactual ledger (asserted)

Switching one rule off flips exactly the verdicts below and nothing else. (v1's P5
switch, `p5 := false`, is not in the ledger: since v1.3 skipping a proof is an
optimisation of P2, and in this checker switching it off also switches off the `⋆`
representation of proofs, so its row would not isolate one rule.) -/
-- P2 switched off: confinement lets an erased term pass an outer place to an erased call,
-- whose writes then persist on the direct path but not on the closed-off one, so `BoomP2`
-- is a closed proof of False (fuzz-port; the row was classed completeness until then)
open Ochr.Registry in
#guard rowOk { eraseOnCopy := false }
  ["Functions.RunGGen:rejected", "Functions.RunIGen:rejected", "Functions.RunPowGen:rejected",
   "CurrentState.TwoPhase:rejected", "Erasure.LemmaMoves:rejected", "Erasure.TypeErased:rejected",
   "Erasure.BoomP2Pair:accepted", "Erasure.BoomP2:accepted"]
open Ochr.Registry in
#guard rowOk { eraseOnCopy := false, confine := false }
  ["Functions.RunGGen:rejected", "Functions.RunIGen:rejected", "Functions.RunPowGen:rejected",
   "CurrentState.TwoPhase:rejected", "Erasure.LemmaMoves:rejected", "Erasure.TypeErased:rejected",
   "Erasure.EffArg:accepted", "Erasure.Write:accepted", "Erasure.Borrow:accepted", "Erasure.Move:accepted",
   "Erasure.BoomP2Pair:accepted", "Erasure.BoomP2:accepted", "Erasure.N1T:accepted",
   "Erasure.N1Closed:accepted", "Erasure.Q:accepted", "Erasure.QBoom:accepted",
   "ErasureBySyntax.LieP:accepted", "ErasureBySyntax.BoomP:accepted"]
open Ochr.Registry in
#guard rowOk { multiOwner := false }
  ["Owners.BadD18:accepted", "Owners.ClosedD18:accepted", "Owners.GR:accepted", "Owners.BadR:accepted"]
open Ochr.Registry in
#guard rowOk { recGuard := false }
  ["Recursion.Loop:accepted", "Recursion.Bot':accepted", "Recursion.Loop2:accepted",
   "Recursion.Spin:accepted", "Recursion.OuterBad:accepted", "Recursion.KnotL:accepted",
   "Recursion.KnotLBoom:accepted", "Recursion.Lie:accepted", "Recursion.Boom:accepted",
   "Recursion.LieCap:accepted", "Recursion.BoomCap:accepted", "Recursion.LieRead:accepted",
   "Recursion.BoomRead:accepted", "Recursion.LieId:accepted", "Recursion.BoomId:accepted"]
-- D19 switched off flips nothing since η for `Unit` (D59): its witness `BadA1` passes a live
-- loan into a stuck `Unit` call, whose result, a sealed program now rather than `()`, carries
-- the loan, and discarding it is a [Drop] error (the [Close] precondition is unchecked)
open Ochr.Registry in
#guard rowOk { accessInside := false }
  []
open Ochr.Registry in
#guard rowOk { selfHeadOnly := false }
  ["Recursion.Knot:accepted", "Recursion.KnotBoom:accepted"]
open Ochr.Registry in
#guard rowOk { argNotBot := false }
  ["Borrows.Dead:accepted", "Borrows.DeadTwice:accepted"]
open Ochr.Registry in
#guard rowOk { generalize := false }
  ["ClosingOff.UseDec:rejected", "Equality.CastMatch:rejected", "CaseSplits.MatchAfterOpaque:rejected",
   "GenType.GenL:rejected", "RenormPi.G:rejected", "RenormPi.Plain:rejected", "RenormPi.InPi:rejected",
   "RenormPi.InConj:rejected", "Splitting.Pick:rejected", "Splitting.PickNotZero:rejected",
   "Splitting.PickNotZeroCopy:rejected", "Splitting.Pick22:rejected", "Splitting.Pick22NotZero:rejected",
   "Splitting.PickTwo:rejected", "Splitting.DoubleVal:rejected", "Trees.InsertM:rejected",
   "Trees.Insert:rejected", "Trees.InsertMEq:rejected", "Trees.InsertMSwap:rejected",
   "Trees.SizeInsert:rejected", "InPlaceTrees.InsertM:rejected", "InPlaceTrees.Insert:rejected",
   "InPlaceTrees.InsertMIsInsert:rejected", "InPlaceTrees.SizeInsert:rejected",
   "InPlaceTrees.SizeInsertRw:rejected"]
open Ochr.Registry in
#guard rowOk { blockMoves := false }
  ["ClosingOff.MovedByBlock:accepted"]
open Ochr.Registry in
#guard rowOk { proofParamsStar := false }
  ["ArmLocal.AndL:rejected", "ArmLocal.Leak:rejected", "Propositions.AndTrue:rejected",
   "Propositions.Swap:rejected", "Propositions.Fst:rejected", "Propositions.FstSwap:rejected",
   "Propositions.AndL2:rejected", "Propositions.Snd:rejected", "Propositions.Twice:rejected",
   "Propositions.SplitId:rejected", "Propositions.TwoOwners:rejected", "Propositions.TwoOwnersR:rejected",
   "Propositions.ThreeOwners:rejected", "Destructuring.DAnd:rejected", "Destructuring.DAnd3:rejected",
   "Destructuring.DNested:rejected", "Destructuring.DWild:rejected", "Destructuring.DCallField:rejected",
   "Subsingletons.OrComm:rejected", "Subsingletons.OrElim:rejected", "Subsingletons.OrLet:rejected",
   "CurrentState.ProofIrr:rejected"]
open Ochr.Registry in
#guard rowOk { recNested := false }
  ["Recursion.KnotL:accepted", "Recursion.KnotLBoom:accepted"]
open Ochr.Registry in
#guard rowOk { erasureByDecl := false }
  ["Functions.RunG:rejected", "Functions.RunGGen:rejected", "Functions.RunI:rejected",
   "Functions.RunIGen:rejected", "Functions.RunPow:rejected", "Functions.RunPowGen:rejected",
   "Erasure.TypeErased:rejected", "Erasure.LieP2:rejected", "ErasureBySyntax.SeqT:rejected"]
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
  ["RenormPi.Plain:rejected", "RenormPi.InPi:rejected", "RenormPi.InConj:rejected",
   "Splitting.PickNotZero:rejected", "Splitting.PickNotZeroCopy:rejected",
   "Splitting.Pick22NotZero:rejected", "Splitting.PickTwo:rejected", "Trees.InsertMEq:rejected",
   "Trees.SizeInsert:rejected", "InPlaceTrees.SizeInsert:rejected", "InPlaceTrees.SizeInsertRw:rejected"]
open Ochr.Registry in
#guard rowOk { leafRule := 0 }
  ["Equality.Om:rejected", "Snapshots.CapP:rejected", "Snapshots.CapP2:rejected", "Snapshots.CapOf:rejected",
   "Snapshots.UseCapOf:rejected"]
open Ochr.Registry in
#guard rowOk { leafRule := 0, confine := false }
  ["Equality.Om:rejected", "Snapshots.CapP:rejected", "Snapshots.CapP2:rejected", "Snapshots.CapOf:rejected",
   "Snapshots.UseCapOf:rejected", "Erasure.EffArgErased:accepted", "Erasure.Write:accepted",
   "Erasure.Borrow:accepted", "Erasure.Move:accepted", "Erasure.N1T:accepted", "Erasure.Q:accepted",
   "ErasureBySyntax.LieP:accepted"]
open Ochr.Registry in
#guard rowOk { leafRule := 1 }
  ["Equality.Om:rejected", "Snapshots.CapP:rejected", "Snapshots.CapP2:rejected", "Snapshots.CapOf:rejected",
   "Snapshots.UseCapOf:rejected"]
open Ochr.Registry in
#guard rowOk { leafRule := 1, confine := false }
  ["Equality.Om:rejected", "Snapshots.CapP:rejected", "Snapshots.CapP2:rejected", "Snapshots.CapOf:rejected",
   "Snapshots.UseCapOf:rejected", "Erasure.EffArgErased:accepted", "Erasure.Write:accepted",
   "Erasure.Borrow:accepted", "Erasure.Move:accepted", "Erasure.N1T:accepted", "Erasure.Q:accepted",
   "ErasureBySyntax.LieP:accepted"]
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
  ["Erasure.EffArgErased:accepted", "Erasure.Write:accepted", "Erasure.Borrow:accepted",
   "Erasure.Move:accepted", "Erasure.N1T:accepted", "Erasure.Q:accepted", "ErasureBySyntax.LieP:accepted"]
open Ochr.Registry in
#guard rowOk { confineBodies := true }
  ["ReturnedBorrows.Inj:rejected", "Snapshots.CapPi:rejected", "Functions.TwiceMZero':rejected",
   "Erasure.F5:rejected", "Erasure.TypeErased:rejected", "Erasure.TailSteps:rejected", "Erasure.P2:rejected",
   "Erasure.FP2:rejected", "Erasure.BoomIsTrue:rejected", "Erasure.p2:rejected", "Erasure.TA2:rejected",
   "Erasure.LieP2:rejected", "ErasureBySyntax.F:rejected", "ErasureBySyntax.SeqT:rejected"]
open Ochr.Registry in
#guard rowOk { borrowParam := false }
  ["ReturnedBorrows.LeakT:accepted", "ReturnedBorrows.Q:accepted", "ReturnedBorrows.Boom:accepted",
   "ReturnedBorrows.QF:accepted"]
open Ochr.Registry in
#guard rowOk { capTypes := false }
  ["ClosingOff.UseDec:rejected", "ClosingOff.UseApply:rejected", "Equality.Om:rejected",
   "Owners.IdThroughRet:rejected", "Snapshots.CapS:rejected", "Snapshots.CapSId:rejected",
   "Snapshots.CapPi:rejected", "Snapshots.CapP:rejected", "Snapshots.CapP2:rejected",
   "Snapshots.CapOf:rejected", "Snapshots.UseCapOf:rejected", "RenormPi.InPi:rejected",
   "RenormPi.InConj:rejected", "ArmLocal.JoinS:rejected", "ArmLocal.AllGe:rejected", "ArmLocal.Leak:rejected"]
-- `genPlaceType` changes no verdict; 08CaseSplits.lean asserts its effect on the generalised σ's type
-- v2.0 D45 by type, switched off: a match on a proof inspects its content (⋆) like data: completeness only
open Ochr.Registry in
#guard rowOk { byType := false }
  ["ArmLocal.AndL:rejected", "ArmLocal.Leak:rejected", "Propositions.AndTrue:rejected",
   "Propositions.Swap:rejected", "Propositions.Fst:rejected", "Propositions.FstSwap:rejected",
   "Propositions.AndL2:rejected", "Propositions.Snd:rejected", "Propositions.Twice:rejected",
   "Propositions.SplitId:rejected", "Propositions.TwoOwners:rejected", "Propositions.TwoOwnersR:rejected",
   "Propositions.ThreeOwners:rejected", "Propositions.FromTrue:rejected", "Propositions.FromTrueIs:rejected",
   "Propositions.Two:rejected", "Propositions.TwoIs:rejected", "Propositions.WriteIf:rejected",
   "Propositions.WriteIfId:rejected", "Propositions.WriteIfAt:rejected", "Propositions.TwoAt:rejected",
   "Destructuring.DAnd:rejected", "Destructuring.DAnd3:rejected", "Destructuring.DNested:rejected",
   "Destructuring.DWild:rejected", "Destructuring.DCallField:rejected", "Destructuring.DTerm:rejected",
   "Subsingletons.OrComm:rejected", "Subsingletons.OrElim:rejected", "Subsingletons.OrLet:rejected",
   "Subsingletons.SqTrue:rejected", "Subsingletons.SqSplit:rejected", "ErasureBySyntax.R8Field:rejected"]
-- v2.0 D45 subsingleton elimination, switched off: large elimination from Or and Sq is accepted (IsL, Get have no
-- model; OrLie is Eq Bool tt ff in the model), but no closed False: D42 erases the constructor it would inspect
open Ochr.Registry in
#guard rowOk { subsingleton := false }
  ["Subsingletons.IsL:accepted", "Subsingletons.Irr:accepted", "Subsingletons.OrLie:accepted",
   "Subsingletons.Get:accepted", "Subsingletons.SqIrr:accepted", "ErasureBySyntax.R8Field:rejected"]
-- v2.0 D42 for constructors, switched off: Prop constructor applications are data values, not proofs (completeness)
open Ochr.Registry in
#guard rowOk { propValues := false }
  ["Subsingletons.OrComm:rejected", "Subsingletons.SqTrue:rejected", "Subsingletons.SqSplit:rejected",
   "Erasure.LieP2:rejected", "ErasureBySyntax.R8Field:rejected"]
-- both off: the closed proofs of False (Subsingletons.Boom, SqBoom) go through
open Ochr.Registry in
#guard rowOk { subsingleton := false, propValues := false }
  ["Subsingletons.IsL:accepted", "Subsingletons.Irr:accepted", "Subsingletons.Boom:accepted",
   "Subsingletons.Get:accepted", "Subsingletons.SqIrr:accepted", "Subsingletons.SqBoom:accepted",
   "Erasure.LieP2:rejected", "ErasureBySyntax.R8Field:rejected"]
-- v2.0 D47 switched off: Eq Nat Z (S Z) is irreducible again, so False and Eq Nat 0 1 part ways
open Ochr.Registry in
#guard rowOk { disjoint := false }
  ["ReturnedBorrows.L:rejected", "ReturnedBorrows.Inj:rejected", "ReturnedBorrows.PF:rejected",
   "Equality.NotAdd01:rejected", "Equality.WriteNeq:rejected", "Equality.WriteDisj:rejected",
   "Equality.NoConf:rejected", "Equality.NoConfS:rejected", "Equality.NoConfMatch:rejected",
   "Equality.NoConfBack:rejected", "Equality.BoolDisj:rejected", "RenormPi.Plain:rejected",
   "RenormPi.InPi:rejected", "RenormPi.InConj:rejected", "Splitting.PickTwo:rejected"]
-- v2.1 D52 switched off: equal constructors are not taken apart in Eq, so programs that
-- need an equation between successors or pairs taken apart are rejected (completeness)
open Ochr.Registry in
#guard rowOk { injective := false }
  ["Equality.Inj:rejected", "Equality.PairInj:rejected", "Recursion.AddZeroCopy:rejected",
   "Recursion.InjStep:rejected", "CurrentState.AddSubIdReborrow:rejected"]
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
-- (InPair, `Nat × &Nat`, no longer flips: since D52 a pair type is the library's Pair, whose
-- parameters may not be borrow types whatever this switch says)
open Ochr.Registry in
#guard rowOk { refTop := false }
  ["BorrowTypes.F:accepted", "BorrowTypes.G:accepted"]
-- D48 (3) switched off: Π-types compared by captures and code (reviewer-3 C3)
open Ochr.Registry in
#guard rowOk { piUnder := false }
  ["ClosingOff.UseApply:rejected", "Equality.Om:rejected", "RenormPi.InPi:rejected",
   "RenormPi.InConj:rejected", "Functions.Cap:rejected", "Functions.CapEq:rejected", "Functions.P1:rejected",
   "Functions.P3:rejected", "Functions.PassZeroAdd:rejected", "Functions.PassA:rejected",
   "Functions.RunUH:rejected"]
-- D49 (3) switched off: a data field of a matched proof is ⋆, and cannot be split
open Ochr.Registry in
#guard rowOk { proofDataFields := false }
  ["Subsingletons.SqSplit:rejected", "ErasureBySyntax.R8Field:rejected"]
-- D50 switched off (normalising unit laws, as v2.0 was first built): True ∧ P loses its And
open Ochr.Registry in
#guard rowOk { unitNorm := true }
  ["Propositions.AndTrue:rejected"]
-- v2.1 D54 switched off: a function type's class is not part of it, so `H`, which returns
-- data, passes where a function returning types is expected. Before the erasure pre-pass,
-- `Boom` and `BoomI` were closed proofs of False (reviewer-5); with it, `g(&c)` is erased by
-- its declared type on both paths. A parameter whose type is a Π-type only by computation
-- (`RefPred(0)`) has no declared Π to read in an untyped run, which reads the value's class,
-- so `BoomPow` is a closed proof of False
open Ochr.Registry in
#guard rowOk { classInType := false }
  ["Functions.BoomPow:accepted"]
-- v2.1 D56 switched off: J returns t whatever its endpoints (equality reflection): `Om`
-- exceeds the depth bound, and `CastMatch` matches 5 against Bool's constructors (reviewer-4 W4)
open Ochr.Registry in
#guard rowOk { jStuck := false }
  ["Equality.Om:rejected", "Equality.CastMatch:rejected"]
-- v2.1 D58 switched off: a zero-arm match yields ⋆ at any type, so re-running `GetZ` under a
-- false hypothesis returns ⋆ for a borrow, and `*q` fails before the proof's own arm (hashmap-port)
open Ochr.Registry in
#guard rowOk { zeroArmStuck := false }
  ["Propositions.GetZIs:rejected"]
-- v2.1 D55 switched off: a type whose sort is known only by computation may be written as a
-- type, so a proposition can have relevant inhabitants that a data function tells apart
-- (reviewer-4 W2: `TT`, with `K1` and `K2` both accepted, has no set-theoretic model); the
-- closed proofs of False of W1 are still caught at their arguments by D54
open Ochr.Registry in
#guard rowOk { sortsSyntactic := false }
  ["Functions.WV:accepted", "Subsingletons.EffL:accepted", "Subsingletons.EffLNoop:accepted",
   "ErasureBySyntax.LieH:accepted", "Sorts.W:accepted", "Sorts.f:accepted", "Sorts.TT:accepted",
   "Sorts.g2:accepted", "Sorts.k:accepted", "Sorts.K1:accepted", "Sorts.K2:accepted"]
-- D53's rows are measured on the D53 blocks (`Test.d53Blocks`, the `Moves` block), the only
-- ones D53 applies to until its acceptance run passes. D53 switched off: reads copy
-- everything, so data is duplicated without `clone`, and a place moved out through a borrow
-- is not caught (the cost model's rule, not the logic's)
open Ochr.Registry in
#guard rowOk { moves := false }
  ["Moves.UseAfterMove:accepted", "Moves.TwiceNat:accepted", "Moves.TakeFromBorrow:accepted",
   "Moves.ReturnMovedBorrow:accepted", "Moves.ClosureMovesCapture:accepted", "Moves.ClosureMoved:accepted",
   "Moves.MoveInArm:accepted", "Moves.RetMoved:accepted"]
-- D53 (c) switched off: a move leaves `⊥`, so a proof that mentions a moved value fails
open Ochr.Registry in
#guard rowOk { ghosts := false }
  ["Moves.GhostRead:rejected"]
-- D53 (e) switched off: calls consume their function and a closure is never a copy, so a
-- function cannot be called twice
open Ochr.Registry in
#guard rowOk { fnRule := false }
  ["Moves.CallTwice:rejected", "Moves.ClosureClones:rejected", "Moves.ClosureCopy:rejected"]
-- D59 switched off: a call written to return `Unit` returns `()` and one that only computes
-- to `Unit` a sealed program, and two values of `Unit` need not be equal
open Ochr.Registry in
#guard rowOk { unitEta := false }
  ["ClosingOff.RowI:rejected"]

-- every row of `switches` has a class
open Ochr.Registry in
#guard rowClass.length == switches.length
