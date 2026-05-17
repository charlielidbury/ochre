import Pss.Checker.Term
import Pss.Checker.PathSelector
import Pss.Checker.Reduction
import Pss.Checker.Subtyping
import Pss.Checker.OrSplit
import Pss.Checker.MacroExpand
import Pss.Checker.Refl
import Pss.Checker.Encodings
import Pss.Checker.Replay
import Pss.Checker.Parser
import Pss.Checker.Examples

/-! # PSS Checker — Lean port of the Pasquale & García-Pérez 2025 PPDP artifact

This umbrella module bundles the Lean port of the interactive type-checker
described in *PSS — An Interactive Subtyping Checker for Pure Subtype
Systems* (PPDP 2025).  See `Pss/Checker/*.lean` for the individual modules
and `pss/CHECKER-PORT-INVESTIGATION.md` for the porting rationale.

The port faithfully reproduces the artifact's pure logic:
* term grammar (`Term.lean`)
* path navigation (`PathSelector.lean`)
* β / Y / top-application reduction (`Reduction.lean`)
* subtype primitives — promote (`Subtyping.lean`)
* OR-split (`OrSplit.lean`)
* macro expand / collapse (`MacroExpand.lean`)
* α-equivalence (`Refl.lean`)
* Scott encodings of int / bool / arithmetic (`Encodings.lean`)
* replay interpreter (`Replay.lean`)

The Emacs-buffer-driven UI in the original `src/interactive/` is **not**
ported — paths are supplied explicitly to the rewrite operations, just as
in the artifact's recorded proof scripts (`examples/subtyping/proofs/*.txt`).

`Examples.lean` exercises the worked examples from §4 of the paper as
`#eval`-checked theorems.
-/
