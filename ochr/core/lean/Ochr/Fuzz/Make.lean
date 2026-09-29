import Ochr.Fuzz.Shrink

/-!
# Fuzzer: making case `i` of a run

Phase 1 draws the templates and random functions; the library is then checked (always
under the default rules, so a seed gives the same case whatever rule switch is being
tested); phase 2 draws the statement over the accepted functions only.
-/

namespace Ochr.Fuzz
open Ochr Ochr.Surface

/-- The names of the library declarations the checker accepts, in order. -/
def acceptedNames (cfg : Config) (fuel : Nat) (decls : List SDecl) : List String := Id.run do
  let mut globals : List GDef := []
  let mut inds : List IndDecl := []
  let mut ok : List String := []
  for d in decls do
    match resolveProgram decls d with
    | .error _ => pure ()
    | .ok it =>
      match runSt (checkItem it) { globals := globals, inds := inds, cfg := cfg, fuel := fuel } with
      | .ok ((), st') => globals := st'.globals; inds := st'.inds; ok := ok ++ [d.name]
      | .error _ => pure ()
  pure ok

def genExtras (lib : List String) : Gen (List (SDecl × LibFn)) := do
  let k ← weighted [(5, pure 0), (3, pure 1), (2, pure 2)]
  let mut fns := libFns.filter (lib.contains ·.name)
  let mut out := #[]
  for j in [0:k] do
    let (d, f) ← genFn s!"R{j}" fns (indsOf lib)
    out := out.push (d, f)
    fns := fns ++ [f]
  pure out.toList

def mkCase (seed i : Nat) (fuel : Nat := 200000) : Case × Rng := Id.run do
  let phase1 : Gen (List String × List (SDecl × LibFn)) := do
    let lib ← genTemplates
    pure (lib, ← genExtras lib)
  let ((lib, extras), g1) := phase1.run { rng := caseRng seed i }
  let ok := acceptedNames {} fuel ((Block.decls Prelude) ++ lib.filterMap libDecl ++ extras.map (·.1))
  let extras := extras.filter fun (d, _) => ok.contains d.name
  -- attack templates are offered even when the default rules reject them (live with a switch off)
  let fns := libFns.filter (fun f => ok.contains f.name || (f.attack && lib.contains f.name)) ++ extras.map (·.2)
  let ((ps, A, lhs, rhs), g2) := (genStmt fns (indsOf lib)).run g1
  -- a quarter of the cases also carry a conversion pair
  let mutate (b : STerm) : List STerm := [.seq .unitLit b, .letIn "z9" none (.num 0) b] ++ shrinkT b
  let ((conv, _), g3) := (do
      if ← chance 25 then pure (← genConvPair fns (indsOf lib) mutate, ()) else pure (none, ())).run g2
  ({ lib := lib, extra := extras.map (·.1), params := ps, ty := A, lhs := lhs, rhs := rhs, conv := conv }, g3.rng)

end Ochr.Fuzz
