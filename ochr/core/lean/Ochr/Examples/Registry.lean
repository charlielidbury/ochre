import Ochr.Examples.Bool
import Ochr.Examples.Logic
import Ochr.Examples.Nat
import Ochr.Examples.Word
import Ochr.Examples.List
import Ochr.Examples.Option
import Ochr.Examples.Box
import Ochr.Examples.Fixtures
import Ochr.Examples.Array
import Ochr.Examples.Numbers
import Ochr.Examples.Borrows
import Ochr.Examples.ReturnedBorrows
import Ochr.Examples.ClosingOff
import Ochr.Examples.Equality
import Ochr.Examples.Snapshots
import Ochr.Examples.Recursion
import Ochr.Examples.CaseSplits
import Ochr.Examples.Functions
import Ochr.Examples.Inductives
import Ochr.Examples.Propositions
import Ochr.Examples.CurrentState
import Ochr.Examples.Erasure
import Ochr.Examples.Universes
import Ochr.Examples.BorrowTypes
import Ochr.Examples.ArrayBench
import Ochr.Examples.Quicksort
import Ochr.Examples.HashMap
import Ochr.Examples.DependentFields
import Ochr.Examples.Sugar
import Ochr.Examples.Units
import Ochr.Examples.Fording

/-! # Every example program, for the test runner

The library blocks (one per file: `Bool.lean` … `Fixtures.lean`), then the programs of the tour,
in reading order (`Examples/README.md`; the blocks of each file in order). The arrays library
(`Array.lean`) is registered with the case studies, whose blocks it is checked with. -/

open Ochr Ochr.Test Ochr.Surface

namespace Ochr.Registry

def programs : List (String × Block) :=
  [("Prelude", Prelude), ("Bools", Bools), ("Logic", Logic), ("Nats", Nats), ("WordType", WordType), ("Words", Words), ("Lists", Lists),
   ("Options", Options), ("OptionRuns", OptionRuns), ("Boxes", Boxes), ("Fixtures", Fixtures), ("Numbers", Numbers), ("Borrows", Borrows), ("Drops", Drops), ("FrameModel", FrameModel), ("Moves", Moves), ("MovedBorrows", MovedBorrows), ("ReturnedBorrows", ReturnedBorrows), ("Reborrows", Reborrows), ("StaticEnds", StaticEnds), ("StaticEndsRuns", StaticEndsRuns), ("BlockEntry", BlockEntry), ("BlockEntryRuns", BlockEntryRuns), ("OneConstructor", OneConstructor), ("OneConstructorRuns", OneConstructorRuns), ("JoinPlaces", JoinPlaces), ("JoinDeref", JoinDeref), ("JoinPrefix", JoinPrefix), ("JoinEntry", JoinEntry), ("SplitJoin", SplitJoin), ("SplitJoinInd", SplitJoinInd), ("SplitJoinLent", SplitJoinLent), ("HoleSites", HoleSites), ("ObsMoved", ObsMoved), ("FreshResult", FreshResult),
   ("ClosingOff", ClosingOff), ("Naturality", Naturality), ("BlockCaptures", BlockCaptures), ("CloseOffModel", CloseOffModel), ("DeclaredReadings", DeclaredReadings), ("Equality", Equality), ("BotConv", BotConv), ("Moves84", Moves84), ("ObsRef", ObsRef), ("IdConsumed", IdConsumed), ("RuntimeJ", RuntimeJ), ("Rewriting", Rewriting),
   ("Owners", Owners), ("Snapshots", Snapshots), ("Recursion", Recursion), ("ProofCopies", ProofCopies), ("CloneProof", CloneProof), ("CloneK2", CloneK2), ("CloneK3", CloneK3), ("CloneCaptured", CloneCaptured),
   ("CaseSplits", CaseSplits), ("GenType", GenType), ("RenormPi", RenormPi), ("Splitting", Splitting), ("SplitCallable", SplitCallable), ("ScrutineeTypes", ScrutineeTypes),
   ("GlobalRecords", GlobalRecords), ("ArmLocal", ArmLocal), ("ArmLocalBoom", ArmLocalBoom), ("ArmRecords", ArmRecords), ("ArmEta", ArmEta), ("Functions", Functions), ("ConvModel", ConvModel), ("CallUnknown", CallUnknown), ("InFlight", InFlight), ("CallArgs", CallArgs), ("Undeclared", Undeclared), ("NatLists", NatLists), ("Trees", Trees), ("InPlaceTrees", InPlaceTrees),
   ("PolyLists", PolyLists), ("ParamInference", ParamInference), ("UntypedHints", UntypedHints), ("Positivity", Positivity), ("PositivityParams", PositivityParams),
   ("PositivityPaper", PositivityPaper),
   ("PositivitySelf", PositivitySelf), ("PositivityCurry", PositivityCurry), ("PositivityChain", PositivityChain), ("PositivityTyFn", PositivityTyFn), ("PositivityPropRoute", PositivityPropRoute), ("PositivitySwap", PositivitySwap), ("PositivitySecondHole", PositivitySecondHole), ("PositivityRoutes", PositivityRoutes), ("PositivityDeclaring", PositivityDeclaring), ("PositivityKeep", PositivityKeep), ("PositivityProbesNest", PositivityProbesNest), ("PositivityProbesLarge", PositivityProbesLarge), ("PositivityProbesAdv", PositivityProbesAdv), ("PositivityControls", PositivityControls), ("NestReads", NestReads), ("NestProps", NestProps),
   ("FrozenReadings", FrozenReadings), ("Propositions", Propositions), ("Destructuring", Destructuring),
   ("Subsingletons", Subsingletons), ("CurrentState", CurrentState), ("Erasure", Erasure),
   ("ErasureBySyntax", ErasureBySyntax), ("Universes", Universes), ("Sorts", Sorts), ("PiSorts", PiSorts), ("BorrowTypes", BorrowTypes), ("BlockRow", BlockRow), ("FnBorrows", FnBorrows),
   ("Abstraction", Abstraction), ("DepFields", DepFields), ("StuckBlocks", StuckBlocks), ("LentIndex", LentIndex), ("ScaffoldLoans", ScaffoldLoans), ("StrongUpdate", StrongUpdate), ("LeafFields", LeafFields), ("MarkedFields", MarkedFields), ("MarkedTableTree1", MarkedTableTree1), ("MarkedTableTree2", MarkedTableTree2), ("MarkedTableLeaf1", MarkedTableLeaf1), ("MarkedTableLeaf2", MarkedTableLeaf2), ("MarkedNested", MarkedNested), ("OpenAttacks", OpenAttacks), ("EarlyEnd", EarlyEnd), ("JBlocks", JBlocks), ("Producers", Producers), ("DirectArm", DirectArm), ("Sugar", Sugar),
   ("SugarOwnBool", SugarOwnBool), ("SugarNoBool", SugarNoBool),
   ("FordVec", FordVec), ("FordLe", FordLe), ("FordRel", FordRel), ("FordAttack", FordAttack), ("WrittenSorts", WrittenSorts), ("InductiveModel", InductiveModel)]

/-- The arrays library and the case studies (`Array`, `ArrayBench`, `Quicksort`, `HashMap`,
`DependentFields`' `DepVec`): checked and counted with the tour, and timed by `lake exe
tests`. -/
def caseStudies : List (String × Block) :=
  [("Arrays", Arrays), ("ArrayLemmas", ArrayLemmas), ("ArrayBench", ArrayBench),
   ("Quicksort", Quicksort),
   ("HashMap", HashMap), ("HashMapTests", HashMapTests), ("HashMapLookup", HashMapLookup),
   ("HashMapLookupTests", HashMapLookupTests), ("HashMapLength", HashMapLength), ("HashMapLengthTests", HashMapLengthTests),
   ("HashMapResize", HashMapResize), ("HashMapResizeTests", HashMapResizeTests),
   ("DepVec", DepVec)]

def reports (cfg : Config := {}) (fuel : Nat := 2000000) : List Report :=
  (programs ++ caseStudies).map fun (n, p) => run n p cfg fuel

end Ochr.Registry

/-- The total number of verdict assertions; a truncated example file changes it. -/
def Ochr.Registry.expectedTotal : Nat := 5034

open Ochr.Registry Ochr.Test in
#guard ((programs ++ caseStudies).map (·.2.decls.length)).foldl (· + ·) 0 == expectedTotal

namespace Ochr.Registry

/-- D128, over the whole registry: the parameters of a block's accepted inductive declarations whose
declared type reads as a sort (`telescope`, the reading a field's type is typed by, D55) without
being written as one (`paramIsType`), as `D.x`. Read in the state after the block and its library,
where a lookup by name finds what it found when the declaration was checked. A block none of whose
inductive declarations has a parameter written otherwise than as a sort has none (a sort reads as
itself), and is not run again. -/
def sortParamsNotWritten (b : Block) (fuel : Nat := 2000000) : List String :=
  if !(b.decls.any fun d => d.ind?.isSome && d.indParams.any fun (_, t) => !(t.unloc matches .sort _)) then [] else
  let p := libOf {} fuel b ++ b.decls
  let items := p.filterMap fun d => match resolveProgram p d fuel with | .ok it => some it | .error _ => none
  let (gs, inds) := globalsAfter {} items
  (inds.filter fun d => b.decls.any (·.name == d.name)).flatMap fun d =>
    match runM (telescope fuel false [] [] (d.params.map (·.1)) (d.params.map (·.2))) { globals := gs, inds := inds } fuel with
    | .ok (sc, _, _) =>
      ((d.params.zip sc.reverse).filter fun ((_, PT), r) => (r matches .sort _) && !(PT matches .sort _)).map
        fun ((h, _), _) => s!"{d.name}.{h.name}"
    | .error e => [s!"{d.name}: {e}"]

end Ochr.Registry

open Ochr.Registry in
#guard (programs ++ caseStudies).all fun (_, b) => (sortParamsNotWritten b).isEmpty
