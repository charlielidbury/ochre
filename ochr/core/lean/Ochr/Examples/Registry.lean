import Ochr.Examples.Units
import Ochr.Examples.E5
import Ochr.Examples.V15
import Ochr.Examples.Logic
import Ochr.Examples.Inductives
import Ochr.Examples.Probes

/-! # Every example program, for the test runner and the counterfactual ledger -/

open Ochr Ochr.Test Ochr.Surface

namespace Ochr.Registry

def programs : List (String × Program) :=
  [("E1", E1), ("E2", E2), ("E3", E3), ("E4", E4), ("E5", E5), ("E6", E6), ("Attacks", Attacks), ("More", More), ("Probes", Probes), ("V15", V15), ("V17", V17), ("V18", V18), ("Positivity", Positivity), ("GenTy", GenTy), ("V19", V19), ("D44", D44), ("Inductives", Inductives),
   ("Logic", Logic), ("ByType", ByType), ("OrAttack", OrAttack), ("PList", PList), ("PosParam", PosParam),
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
   ("D44 (v1.9): a function type returning a borrow has a borrow parameter", { borrowParam := false }),
   ("captured neutral data and proofs keep their types", { capTypes := false }),
   ("D45 (v2.0): a match on a proof is by its type, not its content", { byType := false }),
   ("D45 (v2.0): subsingleton elimination", { subsingleton := false }),
   ("D42 (v2.0): a constructor application of a Prop inductive is a proof (⋆, erased)", { propValues := false }),
   ("D45 + D42 (v2.0): subsingleton elimination and erased Prop values, both off", { subsingleton := false, propValues := false }),
   ("D47 (v2.0): distinct constructors are disjoint in Eq", { disjoint := false }),
   ("extension (switched ON): bodies of erased-class functions and arms of erased blocks are confined", { confineBodies := true })]

end Ochr.Registry

/-- The total number of verdict assertions; a truncated example file changes it. -/
def Ochr.Registry.expectedTotal : Nat := 350

open Ochr.Registry Ochr.Test in
#guard ((reports {}).map Report.count).foldl (· + ·) 0 == expectedTotal
open Ochr.Registry Ochr.Test in
#guard (reports {}).all Report.allAsExpected
