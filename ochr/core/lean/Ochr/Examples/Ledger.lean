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
  ["E5.TwoPhase:rejected", "E6.LemmaMoves:rejected", "Probes.TypeErased:rejected"]
open Ochr.Registry in
#guard rowOk { eraseOnCopy := false, confine := false }
  ["E5.TwoPhase:rejected", "E6.LemmaMoves:rejected", "Attacks.N1T:accepted", "Attacks.N1Closed:accepted", "Attacks.Q:accepted", "Attacks.QBoom:accepted", "Probes.EffArg:accepted", "Probes.TypeErased:rejected", "V17.LieP:accepted", "V17.BoomP:accepted", "V19.Write:accepted", "V19.Borrow:accepted", "V19.Move:accepted", "OrAttack.EffInline:accepted"]
open Ochr.Registry in
#guard rowOk { multiOwner := false }
  ["D18.BadD18:accepted", "D18.ClosedD18:accepted", "D18.GR:accepted", "D18.BadR:accepted"]
open Ochr.Registry in
#guard rowOk { recGuard := false }
  ["Attacks.Loop:accepted", "Attacks.Bot':accepted", "Attacks.Loop2:accepted", "Attacks.Spin:accepted", "Attacks.KnotL:accepted", "Attacks.KnotLBoom:accepted", "Probes.OuterBad:accepted"]
open Ochr.Registry in
#guard rowOk { accessInside := false }
  ["Attacks.BadA1:accepted"]
open Ochr.Registry in
#guard rowOk { selfHeadOnly := false }
  ["Attacks.Knot:accepted", "Attacks.KnotBoom:accepted"]
open Ochr.Registry in
#guard rowOk { argNotBot := false }
  ["More.Dead:accepted", "More.DeadTwice:accepted"]
open Ochr.Registry in
#guard rowOk { generalize := false }
  ["More.MatchAfterOpaque:rejected", "GenTy.GenL:rejected", "Inductives.InsertM:rejected", "Inductives.Insert:rejected", "Inductives.InsertMEq:rejected", "Inductives.InsertMSwap:rejected", "Inductives.SizeInsert:rejected"]
open Ochr.Registry in
#guard rowOk { blockMoves := false }
  ["Probes.MovedByBlock:accepted"]
open Ochr.Registry in
#guard rowOk { proofParamsStar := false }
  ["E5.ProofIrr:rejected", "ByType.Swap:rejected", "ByType.Fst:rejected", "ByType.FstSwap:rejected", "ByType.Snd:rejected", "ByType.Twice:rejected", "ByType.SplitId:rejected", "ByType.AndTrue:rejected", "OrAttack.OrComm:rejected", "OrAttack.OrElim:rejected", "OrAttack.OrLet:rejected", "AndElim.AndL:rejected", "AndElim.AndL2:rejected", "AndElim.Two:rejected", "AndElim.TwoR:rejected", "AndElim.Three:rejected"]
open Ochr.Registry in
#guard rowOk { recNested := false }
  ["Attacks.KnotL:accepted", "Attacks.KnotLBoom:accepted"]
open Ochr.Registry in
#guard rowOk { erasureByDecl := false }
  ["Probes.TypeErased:rejected", "V15.MainW0:rejected", "V17.TruthB:rejected", "V17.LieG:accepted", "V17.TruthG:rejected", "V17.SeqT:rejected", "V17.RowI:accepted", "V18.LieH:rejected"]
open Ochr.Registry in
#guard rowOk { matchEndsInside := false }
  ["V15.Bad:accepted", "V15.Main:accepted"]
open Ochr.Registry in
#guard rowOk { closureConv := 2 }
  ["V15.Boom3:accepted"]
open Ochr.Registry in
#guard rowOk { unboundWithoutBy := false }
  ["V15.Loop:accepted", "V15.Boom4:accepted"]
open Ochr.Registry in
#guard rowOk { patternWritesVisible := false }
  ["V15.Clear:accepted", "V15.Boom5:accepted"]
open Ochr.Registry in
#guard rowOk { genConsistent := false }
  ["Inductives.InsertMEq:rejected", "Inductives.SizeInsert:rejected"]
open Ochr.Registry in
#guard rowOk { classBySyntax := false }
  ["V17.BoomL:accepted", "V17.TruthG:rejected", "V18.Boom8:accepted", "V18.Direct8:accepted", "V18.LieH:rejected"]
open Ochr.Registry in
#guard rowOk { blockRule := 0 }
  ["V17.LieB:accepted", "V17.BoomB:accepted", "V17.TruthB:rejected", "V17.LieG:accepted", "V17.BoomG:accepted", "V17.TruthG:rejected", "V18.Lie7:accepted", "V18.Boom7:accepted"]
open Ochr.Registry in
#guard rowOk { blockRule := 1 }
  ["V17.LieG:accepted", "V17.BoomG:accepted", "V17.TruthG:rejected"]
open Ochr.Registry in
#guard rowOk { seqByProof := false }
  ["V17.SeqT:rejected"]
open Ochr.Registry in
#guard rowOk { rowByDecl := false }
  ["V17.RowI:accepted"]
open Ochr.Registry in
#guard rowOk { leafRule := 0 }
  ["D44.CapP:rejected", "D44.CapP2:rejected", "OrAttack.OrLet:rejected"]
open Ochr.Registry in
#guard rowOk { leafRule := 0, confine := false }
  ["Attacks.N1T:accepted", "Attacks.Q:accepted", "Probes.EffArgErased:accepted", "V19.Write:accepted", "V19.Borrow:accepted", "V19.Move:accepted", "D44.CapP:rejected", "D44.CapP2:rejected", "OrAttack.OrLet:rejected", "OrAttack.EffInline:accepted"]
open Ochr.Registry in
#guard rowOk { leafRule := 1 }
  ["D44.CapP:rejected", "D44.CapP2:rejected"]
open Ochr.Registry in
#guard rowOk { leafRule := 1, confine := false }
  ["Attacks.N1T:accepted", "Attacks.Q:accepted", "Probes.EffArgErased:accepted", "V17.LieP:accepted", "V18.BoomH:accepted", "V19.Write:accepted", "V19.Borrow:accepted", "V19.Move:accepted", "D44.CapP:rejected", "D44.CapP2:rejected", "OrAttack.EffInline:accepted"]
open Ochr.Registry in
#guard rowOk { blockRule := 1, leafRule := 0 }
  ["V17.LieP:accepted", "V17.BoomP:accepted", "V17.LieG:accepted", "V17.BoomG:accepted", "V17.TruthG:rejected", "D44.CapP:rejected", "D44.CapP2:rejected", "OrAttack.OrLet:rejected"]
open Ochr.Registry in
#guard rowOk { positivity := false }
  ["Positivity.Bad:accepted", "Positivity.L:accepted", "Positivity.K:accepted", "Positivity.bad:accepted", "Positivity.Boom:accepted", "PosParam.Bad:accepted", "PosParam.L:accepted", "PosParam.K:accepted", "PosParam.bad:accepted", "PosParam.Boom:accepted", "PosParam.Neg:accepted"]
open Ochr.Registry in
#guard rowOk { globalRecords := false }
  ["V18.Esc:accepted", "V18.BoomE:accepted"]
open Ochr.Registry in
#guard rowOk { obsBorrow := false }
  ["V18.ConvPick:accepted", "V18.TY:accepted", "V18.BoomX4:accepted"]
open Ochr.Registry in
#guard rowOk { headGuardNeutral := false }
  ["V18.P1:rejected", "D48.HO:rejected"]
open Ochr.Registry in
#guard rowOk { confine := false }
  ["Attacks.N1T:accepted", "Attacks.Q:accepted", "Probes.EffArgErased:accepted", "V17.LieP:accepted", "V19.Write:accepted", "V19.Borrow:accepted", "V19.Move:accepted", "OrAttack.EffInline:accepted"]
open Ochr.Registry in
#guard rowOk { confineBodies := true }
  ["E4.TwiceMZero':rejected", "Attacks.P2:rejected", "Attacks.FP2:rejected", "Attacks.BoomIsTrue:rejected", "Attacks.p2:rejected", "Attacks.TA2:rejected", "Probes.F5:rejected", "Probes.TypeErased:rejected", "V17.F:rejected", "V17.SeqT:rejected", "V19.TailSteps:rejected", "D44.CapPi:rejected"]
open Ochr.Registry in
#guard rowOk { borrowParam := false } ["D44.Q:accepted", "D44.Boom:accepted", "D44.LeakT:accepted"]
open Ochr.Registry in
#guard rowOk { capTypes := false }
  ["D44.CapS:rejected", "D44.CapSId:rejected", "D44.CapPi:rejected", "D44.CapP:rejected", "D44.CapP2:rejected"]
-- `genPlaceType` changes no verdict; V18.lean asserts its effect on the generalised σ's type
-- v2.0 D45 by type, switched off: a match on a proof inspects its content (⋆) like data: completeness only
open Ochr.Registry in
#guard rowOk { byType := false }
  ["Logic.FromTrue:rejected", "Logic.FromTrueIs:rejected", "ByType.Swap:rejected", "ByType.Fst:rejected", "ByType.FstSwap:rejected", "ByType.Two:rejected", "ByType.TwoIs:rejected", "ByType.WriteIf:rejected", "ByType.WriteIfId:rejected", "ByType.WriteIfAt:rejected", "ByType.TwoAt:rejected", "ByType.Snd:rejected", "ByType.Twice:rejected", "ByType.SplitId:rejected", "ByType.AndTrue:rejected", "OrAttack.OrComm:rejected", "OrAttack.OrElim:rejected", "OrAttack.OrLet:rejected", "OrAttack.SqTrue:rejected", "OrAttack.EffL:rejected", "OrAttack.EffLNoop:rejected", "D49.SqSplit:rejected", "AndElim.AndL:rejected", "AndElim.AndL2:rejected", "AndElim.Two:rejected", "AndElim.TwoR:rejected", "AndElim.Three:rejected"]
-- v2.0 D45 subsingleton elimination, switched off: large elimination from Or and Sq is accepted (IsL, Get have no
-- model; OrLie is Eq Bool tt ff in the model), but no closed False: D42 erases the constructor it would inspect
open Ochr.Registry in
#guard rowOk { subsingleton := false }
  ["OrAttack.IsL:accepted", "OrAttack.Irr:accepted", "OrAttack.OrLie:accepted", "OrAttack.Get:accepted", "OrAttack.SqIrr:accepted"]
-- v2.0 D42 for constructors, switched off: Prop constructor applications are data values, not proofs (completeness)
open Ochr.Registry in
#guard rowOk { propValues := false }
  ["OrAttack.OrComm:rejected", "OrAttack.SqTrue:rejected", "OrAttack.EffL:rejected", "OrAttack.EffLNoop:rejected", "D49.SqSplit:rejected"]
-- both off: the closed proofs of False (OrAttack.Boom, SqBoom) go through
open Ochr.Registry in
#guard rowOk { subsingleton := false, propValues := false }
  ["OrAttack.IsL:accepted", "OrAttack.Irr:accepted", "OrAttack.Boom:accepted", "OrAttack.Get:accepted", "OrAttack.SqIrr:accepted", "OrAttack.SqBoom:accepted", "OrAttack.EffLNoop:rejected", "OrAttack.EffInline:accepted"]
-- v2.0 D47 switched off: Eq Nat Z (S Z) is irreducible again, so False and Eq Nat 0 1 part ways
open Ochr.Registry in
#guard rowOk { disjoint := false }
  ["E6.NotAdd01:rejected", "Logic.NoConf:rejected", "Logic.NoConfS:rejected", "Logic.NoConfMatch:rejected", "Logic.NoConfBack:rejected", "Logic.BoolDisj:rejected", "Logic.WriteDisj:rejected"]
-- finding (v2.0 round): v1.9 assumed a data match's scrutinee type from its arms
open Ochr.Registry in
#guard rowOk { scrutTyped := false }
  ["Scrut.f:accepted", "Scrut.g:accepted"]
-- D48 (1) switched off: &Type makes Type₀ impredicative (System U⁻), and &Prop, &True, &Π, &A pass
open Ochr.Registry in
#guard rowOk { refData := false }
  ["D48.Impred:accepted", "D48.PolyId:accepted", "D48.SelfApp:accepted", "D48.SelfAppEq:accepted", "D48.PolyTy:accepted", "D48.PIref:accepted", "D48.RefTrue:accepted", "D48.RefFun:accepted", "D48.SwapT:accepted"]
-- D48 (2) switched off: a codomain computing to &Nat; the accepted G reads ⊥ at n = 0
open Ochr.Registry in
#guard rowOk { refTop := false }
  ["D48.F:accepted", "D48.G:accepted", "D48.InPair:accepted"]
-- D48 (3) switched off: Π-types compared by captures and code (reviewer-3 C3)
open Ochr.Registry in
#guard rowOk { piUnder := false }
  ["PiConv.Cap:rejected", "PiConv.CapEq:rejected", "PiConv.P1:rejected", "PiConv.P3:rejected", "PiConv.PassZeroAdd:rejected", "PiConv.PassA:rejected"]
-- D49 (3) switched off: a data field of a matched proof is ⋆, and cannot be split
open Ochr.Registry in
#guard rowOk { proofDataFields := false }
  ["D49.SqSplit:rejected"]
-- D50 switched off (normalising unit laws, as v2.0 was first built): True ∧ P loses its And
open Ochr.Registry in
#guard rowOk { unitNorm := true }
  ["ByType.AndTrue:rejected"]

-- every row of `switches` has a class
open Ochr.Registry in
#guard rowClass.length == switches.length
