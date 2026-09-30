import Ochr.Fuzz.Shrink

/-!
# Fuzzer: replaying a printed counterexample

A counterexample printed by `lake exe fuzz` is an `ochr { … }` block whose last
declaration is `def Stmt (params) : Prop := Id A lhs rhs`. Pasted into a Lean file it
elaborates to a `Program`; `replay` runs the oracles on it:

```
ochr Cex { … }
#eval IO.println (replay Cex)
#eval IO.println (replay Cex { confine := false })     -- with one rule switched off
```
-/

namespace Ochr.Fuzz
open Ochr Ochr.Surface

/-- The case of a program whose last declaration is the statement. -/
def Case.ofProgram (p : Program) : Case :=
  match p.getLast? with
  | some d =>
    let isConv (x : SDecl) := ["ConvF", "ConvG", "ConvEq"].contains x.name
    let conv := match p.find? (·.name == "ConvF"), p.find? (·.name == "ConvG") with
      | some f, some g => some (f.ret, f.body, g.body)
      | _, _ => none
    let extra := p.dropLast.filter (!isConv ·)
    match d.body with
    | .app "Id" [A, l, r] => { extra := extra, params := d.params, ty := A, lhs := l, rhs := r, conv := conv }
    | _ => { extra := extra, conv := conv }
  | none => {}

/-- Run every oracle on a printed counterexample; ground instances drawn from `seed`. -/
def replay (b : Block) (cfg : Config := {}) (seed : Nat := 0) : String :=
  let c := Case.ofProgram (b.decls.map SDecl.strip)
  let res := checkCase { cfg := cfg } c (caseRng seed 0)
  let fs := res.findings.map Finding.show
  s!"status: {res.status}; {res.findings.length} finding(s)\n" ++ "\n".intercalate fs

/-- The finding kinds of a replayed counterexample (for `#guard` regression tests). -/
def replayKeys (b : Block) (cfg : Config := {}) (seed : Nat := 0) : List String :=
  ((checkCase { cfg := cfg } (Case.ofProgram (b.decls.map SDecl.strip)) (caseRng seed 0)).findings.map Finding.key).eraseDups

end Ochr.Fuzz
