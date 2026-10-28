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

/-! # Every example program, for the test runner and the counterfactual ledger

The library blocks (one per file: `Bool.lean` … `Fixtures.lean`), then the programs of the tour,
in reading order (`Examples/README.md`; the blocks of each file in order). The arrays library
(`Array.lean`) is registered with the case studies, whose blocks it is checked with. The
counterfactual ledger (`Ledger.lean`) switches one rule off at a time and lists the verdicts
that flip, in this order. -/

open Ochr Ochr.Test Ochr.Surface

namespace Ochr.Registry

def programs : List (String × Block) :=
  [("Prelude", Prelude), ("Bools", Bools), ("Logic", Logic), ("Nats", Nats), ("WordType", WordType), ("Words", Words), ("Lists", Lists),
   ("Options", Options), ("Boxes", Boxes), ("Fixtures", Fixtures), ("Numbers", Numbers), ("Borrows", Borrows), ("Drops", Drops), ("Moves", Moves), ("ReturnedBorrows", ReturnedBorrows), ("Reborrows", Reborrows),
   ("ClosingOff", ClosingOff), ("Naturality", Naturality), ("Equality", Equality), ("Rewriting", Rewriting),
   ("Owners", Owners), ("Snapshots", Snapshots), ("Recursion", Recursion),
   ("CaseSplits", CaseSplits), ("GenType", GenType), ("RenormPi", RenormPi), ("Splitting", Splitting), ("ScrutineeTypes", ScrutineeTypes),
   ("GlobalRecords", GlobalRecords), ("ArmLocal", ArmLocal), ("ArmLocalBoom", ArmLocalBoom), ("ArmRecords", ArmRecords), ("Functions", Functions), ("NatLists", NatLists), ("Trees", Trees), ("InPlaceTrees", InPlaceTrees),
   ("PolyLists", PolyLists), ("Positivity", Positivity), ("PositivityParams", PositivityParams),
   ("PositivityPaper", PositivityPaper), ("Propositions", Propositions), ("Destructuring", Destructuring),
   ("Subsingletons", Subsingletons), ("CurrentState", CurrentState), ("Erasure", Erasure),
   ("ErasureBySyntax", ErasureBySyntax), ("Universes", Universes), ("Sorts", Sorts), ("BorrowTypes", BorrowTypes), ("FnBorrows", FnBorrows),
   ("Abstraction", Abstraction), ("DepFields", DepFields), ("Sugar", Sugar),
   ("SugarOwnBool", SugarOwnBool), ("SugarNoBool", SugarNoBool)]

/-- The arrays library and the case studies (`Array`, `ArrayBench`, `Quicksort`, `HashMap`,
`DependentFields`' `DepVec`): checked and counted with the tour, and timed by `lake exe
tests`, but not re-run by the counterfactual ledger, which is about the rules. A case study's
programs are large and chained (each block re-checks the blocks it uses), so each ledger row
would re-check them twice; their flips are measured once instead, by
`Ochr/Examples/CaseStudyLedger.lean` (run it with `lake env lean`), and reported in
`notes/arrays-library.md` and `notes/hashmap-case-study.md`. -/
def caseStudies : List (String × Block) :=
  [("Arrays", Arrays), ("ArrayLemmas", ArrayLemmas), ("ArrayBench", ArrayBench),
   ("Quicksort", Quicksort),
   ("HashMap", HashMap), ("HashMapTests", HashMapTests), ("HashMapLookup", HashMapLookup),
   ("HashMapLookupTests", HashMapLookupTests), ("HashMapLength", HashMapLength), ("HashMapLengthTests", HashMapLengthTests),
   ("HashMapResize", HashMapResize), ("HashMapResizeTests", HashMapResizeTests),
   ("DepVec", DepVec)]

def reports (cfg : Config := {}) (fuel : Nat := 2000000) : List Report :=
  (programs ++ caseStudies).map fun (n, p) => run n p cfg fuel

/-- The declarations whose verdict under `cfg` differs from the default, as
`program.name:verdict`, and the declarations that flip only because a library declaration
they use flipped, as `program.name blocked by Home.decl`. A library declaration that flips is
attributed once, to its home block; a block that uses it and then fails because of it is
"blocked", not a further flip (`Ochr.Test.blockedBy`). -/
def flipsDetail (cfg : Config) : List String × List String :=
  -- counterfactual runs may not terminate (e.g. without [Rec]); a smaller fuel bounds them
  programs.foldl (fun (fs, bl) (n, b) =>
    let (f, g) := blockFlips n b cfg 300000
    (fs ++ f, bl ++ g)) ([], [])

/-- The ledger's flips under `cfg` (blocked declarations excluded). -/
def flips (cfg : Config) : List String := (flipsDetail cfg).1

/-- Each switch disables one rule; the ledger records what it was guarding. -/
def switches : List (String × Config) :=
  [("P2 (v1.3, D26): erased terms run on a private copy", { eraseOnCopy := false }),
   ("D18: owners are sets", { multiOwner := false }),
   ("D17: [Rec] entry-value guard", { recGuard := false }),
   ("D19: [Access] ends loans inside the content", { accessInside := false }),
   ("L1: self only as a call head", { selfHeadOnly := false }),
   ("L2: no ⊥ argument", { argNotBot := false }),
   ("C8: generalise before splitting on a sealed program", { generalize := false }),
   ("C5: a stuck block moves in a borrow variable an arm moves", { blockMoves := false }),
   ("D27 (v1.4): proof parameters are ⋆ at the generic call", { proofParamsStar := false }),
   ("L3 (v1.3): [Rec] covers nested functions", { recNested := false }),
   ("D29 (v1.5): matching ends loans inside a neutral head", { matchEndsInside := false }),
   ("D30 (v1.5): closures compared by generic-call observation (vs result only)", { closureConv := 2 }),
   ("D31 (v1.5): without `by`, f is not in scope", { unboundWithoutBy := false }),
   ("D32 (v1.5): writes through pattern variables are writes to the scrutinee", { patternWritesVisible := false }),
   ("G1 (finding): a generalised neutral stays generalised under normalisation", { genConsistent := false }),
   ("P1 (finding): a variable declared of sort Prop is a proof", { leafRule := 0 }),
   ("P3 (finding): ... by its declaration, not its value ⋆", { leafRule := 1 }),
   ("D36 (v1.7): constructor fields are first-order data", { positivity := false }),
   ("D37 (v1.8): generalisation records and fresh names survive private copies", { globalRecords := false }),
   ("D38 (v1.8): a borrow result is observed through a fresh value written into it", { obsBorrow := false }),
   ("D39 (v1.8): [Seal]'s head guard covers neutral-headed calls", { headGuardNeutral := false }),
   ("D44 (v1.9): a function type returning a borrow has a borrow parameter", { borrowParam := false }),
   ("captured neutral data and proofs keep their types", { capTypes := false }),
   ("D45 (v2.0): a match on a proof is by its type, not its content", { byType := false }),
   ("D45 (v2.0): subsingleton elimination", { subsingleton := false }),
   ("D42 (v2.0): a constructor application of a Prop inductive is a proof (⋆, erased)", { propValues := false }),
   ("D45 + D42 (v2.0): subsingleton elimination and erased Prop values, both off", { subsingleton := false, propValues := false }),
   ("D47 (v2.0): distinct constructors are disjoint in Eq", { disjoint := false }),
   ("D52 (v2.1): Eq is injective on constructors", { injective := false }),
   ("finding (v2.0 round), D63: a match's scrutinee has its constructors' type (read, not assumed), Nat's included", { scrutTyped := false }),
   ("D48 (1), D66: only what is in Type₀ is borrowed", { refData := false }),
   ("D66: the borrow test is A : Type₀ (off: D48 (1)'s data-only test)", { borrowUniverse := false }),
   ("D66: Prop : Type₁, beside Type₀ (off: Prop : Type₀)", { propUp := false }),
   ("D48 (2): & only at the top of a declared type", { refTop := false }),
   ("D48 (3): Π-types are compared under their binders", { piUnder := false }),
   ("D49 (3): a data field of a matched proof is a fresh abstract value", { proofDataFields := false }),
   ("D50 (switched ON): the unit laws normalise stored types instead of converting", { unitNorm := true }),
   ("D54 (v2.1): a Π-type's erasure class, and whether it returns a borrow, are part of it", { classInType := false }),
   ("D56 (v2.1): J computes only when its endpoints are convertible", { jStuck := false }),
   ("D58 (v2.1): a zero-arm match outside a proof position is stuck, not ⋆", { zeroArmStuck := false }),
   ("D55 (v2.1): sorts are syntactic (one notion of proposition)", { sortsSyntactic := false }),
   ("D68: reads in a statement move, as at runtime (a statement runs on its own copy)", { erasedMoves := false }),
   ("D53 (e): the Fn rule (a call does not consume its function; closure bodies do not move their captures)", { fnRule := false }),
   ("D59 (refined): η-normal forms at Unit (the readback at Unit is (); [Close] has no Unit row)", { unitEta := false }),
   ("K3: an abstract type's constructors and matches only in erased positions and model code", { abstractTypes := false }),
   ("K2: outside model code, a place of an unsized type is only borrowed at runtime", { unsizedTypes := false }),
   ("D63: a match whose arms disagree about being proofs has no declared type", { armsAgree := false }),
   ("D63: [Id] observes with the typing judgement in untyped runs too", { typedObs := false }),
   ("D67: [Access] before an assignment ends only the loans the place owns (a reborrow behind a held borrow survives)", { reborrowSurvives := false }),
   ("D64 [Repack]: a value of a dependent type is of its telescope again at every whole-again point", { repack := false }),
   ("D64 (D52 restricted): Eq takes a dependent constructor apart only while its index fields are convertible", { depInj := false }),
   ("K4: a field type may call an earlier type function", { k4 := false }),
   ("K4's nesting condition: no nesting at a parameter passed to a type function", { k4Nest := false }),
   ("D65 amended: [Drop] of a lent place ends only borrowers held in bindings; one in flight is an error", { dropEndsBound := false }),
   ("each side of Eq runs on its own private copy of the state", { eqSidesApart := false }),
   ("D68: a value is copied only when its type is a copy type (a function type is not)", { copyByType := false }),
   ("D68: an equation over a moved place is stuck, and a moved binding stays observed", { movedStuck := false }),
   ("D64 amended: a proof field assigned while part of its value is lent is checked with what the borrow holds unknown", { lentProofs := false })]


/-- The class of each ledger row, in the order of `switches` (reviewer-3's request):
* `soundness`: switching the rule off accepts a closed proof of a false proposition, or a
  program that goes wrong when run (a use of `⊥`); the witnesses are named;
* `false lemma`: it accepts a false open lemma, whose closed instances another rule still
  rejects;
* `model`: it accepts definitions with no set-theoretic model (an impredicative `Type₀`,
  a large elimination from a non-subsingleton, a refutation of a type Rust inhabits), but
  the suite has no closed false proof;
* `policy`: it accepts only programs that are true under the other rules (a fail-safe or
  a stability condition, with no witness here);
* `completeness`: it only rejects good programs;
 -/
def rowClass : List (String × List String) :=
  [("soundness", ["Erasure.BoomP2"]),
   ("soundness", ["Owners.ClosedD18", "Owners.BadR"]),
   ("soundness", ["Recursion.KnotLBoom"]),
   ("soundness", ["Borrows.BadA1", "Borrows.V", "Borrows.W"]),
   ("soundness", ["Recursion.KnotBoom"]),
   ("soundness", ["Borrows.Dead"]),
   ("completeness", []),
   ("soundness", ["ClosingOff.MovedByBlock"]),
   ("completeness", []),
   ("soundness", ["Recursion.KnotLBoom"]),
   ("soundness", ["ReturnedBorrows.Main"]),
   ("soundness", ["Functions.Boom3"]),
   ("soundness", ["Recursion.LoopNoByBoom"]),
   ("soundness", ["ClosingOff.Boom5"]),
   ("completeness", []),
   ("completeness", []),
   ("completeness", []),
   ("soundness", ["Positivity.Boom", "PositivityParams.Boom"]),
   ("soundness", ["GlobalRecords.Bad5"]),
   ("soundness", ["Functions.BoomX4"]),
   ("completeness", []),
   ("model", ["ReturnedBorrows.Boom"]),
   ("completeness", []),
   ("completeness", []),
   ("model", ["Subsingletons.IsL", "Subsingletons.Get"]),
   ("completeness", []),
   ("soundness", ["Subsingletons.Boom", "Subsingletons.SqBoom"]),
   ("completeness", []),
   ("completeness", []),
   ("soundness", ["ScrutineeTypes.g", "ScrutineeTypes.NatTUse", "ScrutineeTypes.M2"]),
   ("model", ["Universes.Impred", "Universes.SelfApp"]),
   ("completeness", []),
   ("policy", ["FnBorrows.SwapProps"]),
   ("soundness", ["BorrowTypes.G"]),
   ("completeness", []),
   ("completeness", []),
   ("completeness", []),
   ("soundness", ["Functions.BoomPow"]),
   ("policy", ["Equality.JT"]),
   ("completeness", []),
   ("model", ["Sorts.K1", "Sorts.K2"]),
   ("policy", ["ClosingOff.LamWriteInBlock"]),
   ("completeness", []),
   ("completeness", []),
   ("policy", ["Abstraction.Peek"]),
   ("policy", ["Abstraction.Take"]),
   ("policy", ["ErasureBySyntax.MixPos"]),
   ("completeness", []),
   ("completeness", []),
   ("soundness", ["DepFields.Boom"]),
   ("policy", ["DepFields.InjLen"]),
   ("completeness", []),
   ("soundness", ["DepFields.Boom2"]),
   ("soundness", ["Drops.Blk", "Drops.UseG"]),
   ("model", ["Equality.SideShared"]),
   ("policy", ["Moves.ClosureCopy"]),
   ("model", ["Equality.MovedBothSides"]),
   ("soundness", ["DepFields.BoomLent", "DepFields.BoomGetLent"])]


end Ochr.Registry

/-- The total number of verdict assertions; a truncated example file changes it. -/
def Ochr.Registry.expectedTotal : Nat := 1481

open Ochr.Registry Ochr.Test in
#guard ((programs ++ caseStudies).map (·.2.decls.length)).foldl (· + ·) 0 == expectedTotal
