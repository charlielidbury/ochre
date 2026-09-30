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

/-- Reviewer-6's A1/L1 family (W10): a parameter `n0 : Nat` and an abstract function
`g1 : Π(u : Unit). Fam(n0)` (or over `&Nat`) whose codomain depends on `n0` through a
family whose arms are different data types (`TF`: `Bx(Unit)`/`Bx(B2)`, one constructor at two
parameters, as A1's `Box`; `TG`: `Nat`/`B2`, as L1). A match on
`n0` calls `g1` in several arms and uses the result at that arm's type: splits it, or (in
the `S` arm) observes it with a type-level function (`CmpBx`, `CmpB2`) whose `Id` compares
a place at its type. A split in one arm generalises the call; the other arm re-derives the
same program text. Returns the statement and the family's own proof candidates. -/
def genA1 : Gen (List (String × STerm) × STerm × STerm × STerm × List STerm) := do
  let tf ← chance 60
  let fam := if tf then "TF" else "TG"
  let byRef ← chance 25
  let dom : STerm := if byRef then .amp (.ident "Nat") else .ident "Unit"
  let ps : List (String × STerm) :=
    [("n0", .ident "Nat"), ("g1", .pi [("u", dom)] (.call (.ident fam) [.ident "n0"]))]
  let callG : STerm := if byRef then .call (.ident "g1") [.amp (.ident "c9")] else .call (.ident "g1") [.unitLit]
  let bind (x : String) (body : STerm) : STerm :=
    let b := STerm.letIn x none callG body
    if byRef then .letIn "c9" none (.num 0) b else b
  -- the Z arm's value (at the family's Z type) and the S arm's (at its S type), as a proposition
  -- or as a number
  let prop ← chance 70
  let splitZ (x : String) (e : STerm) : STerm :=
    if tf then .matchGen (.ident x) [("MkBx", ["v"], e)]
    else .matchGen (.ident x) [("Z", [], e), ("S", ["_"], e)]
  let splitS (y : String) (ef et : STerm) : STerm :=
    if tf then .matchGen (.ident y) [("MkBx", ["v"], .matchGen (.ident "v") [("F", [], ef), ("T", [], et)])]
    else .matchGen (.ident y) [("F", [], ef), ("T", [], et)]
  let observe (y : String) : STerm := .call (.ident (if tf then "CmpBx" else "CmpB2")) [.ident y]
  let armZ ← if prop then
      weighted [(3, pure (bind "x5" (splitZ "x5" .top))), (1, pure (bind "x5" .top)), (1, pure .top)]
    else
      weighted [(3, pure (bind "x5" (splitZ "x5" (.num 0)))), (1, pure (.num 0))]
  let armS ← if prop then
      weighted [(3, pure (bind "y6" (observe "y6"))), (1, pure (bind "y6" (splitS "y6" .top (.ident "False")))),
                (1, pure (bind "y6" .top))]
    else
      weighted [(3, pure (bind "y6" (splitS "y6" (.num 1) (.num 2)))), (1, pure (.num 1))]
  -- which arm comes first in the program text: the Z arm is checked first either way
  let body := STerm.matchGen (.ident "n0") [("Z", [], armZ), ("S", ["p7"], armS)]
  let lhs ← weighted [(3, pure body), (1, pure (.letIn "a8" none body (.ident "a8")))]
  let A : STerm := if prop then .sort 0 else .ident "Nat"
  let rhs ← if prop then
      weighted [(2, pure .top), (2, pure (.matchGen (.ident "n0") [("Z", [], .top), ("S", ["_"], .ident "False")]))]
    else weighted [(1, pure (.num 1)), (1, pure (.num 0)), (1, pure lhs)]
  -- the family's proofs: A1's own shape (a split of the call in the Z arm, `refl` in the S arm)
  let zProof : STerm := bind "x5" (splitZ "x5" (.ident "refl"))
  let proofs := [.matchGen (.ident "n0") [("Z", [], zProof), ("S", ["_"], .ident "refl")]]
  pure (ps, A, lhs, rhs, proofs)

/-- The E family with a dependent codomain (reviewer-6 W10: E against A1). A stuck block
returns a closure whose codomain mentions a value the arm refined (`λ(u : Unit) : Fam(p1) =>
h(clone(p1))` in `match q0 { Mk(p1, p2) => … }`), so the block's inferred Π-type captures an
arm-local σ (class E); or, over `n0 : Nat`, each arm's closure has codomain `Fam(n0)`, with
or without the block annotated. The continuation calls the closure in several arms of a
match on the same data and splits or observes the result at that arm's type. -/
def genEDep : Gen (List (String × STerm) × STerm × STerm × STerm × List STerm) := do
  let tf ← chance 60
  let fam := if tf then "TF" else "TG"
  let famOf (t : STerm) : STerm := .call (.ident fam) [t]
  let clo (t : STerm) : STerm :=
    .fix "_" [("u", .ident "Unit")] (famOf t) none (.call (.ident "h") [.call (.ident "clone") [t]])
  let splitZ (x : String) (e : STerm) : STerm :=
    if tf then .matchGen (.ident x) [("MkBx", ["v"], e)]
    else .matchGen (.ident x) [("Z", [], e), ("S", ["_"], e)]
  let observe (y : String) : STerm := .call (.ident (if tf then "CmpBx" else "CmpB2")) [.ident y]
  let useZ ← pick [STerm.letIn "x5" none (.call (.ident "f") [.unitLit]) (splitZ "x5" .top), .top]
  let useS ← pick [STerm.letIn "y6" none (.call (.ident "f") [.unitLit]) (observe "y6"), .top]
  let hTy : STerm := .pi [("n", .ident "Nat")] (famOf (.ident "n"))
  -- data: a match on the result of `h`, whose type is the family at a parameter (stuck at the
  -- generic call), with the patterns of one of the family's types
  if ← chance 30 then
    let ps : List (String × STerm) := [("n0", .ident "Nat"), ("h", hTy)]
    let x : STerm := .call (.ident "h") [.ident "n0"]
    let m := if tf then STerm.matchGen (.ident "x5") [("MkBx", ["v"], .num 0)]
      else STerm.matchGen (.ident "x5") [("Z", [], .num 0), ("S", ["_"], .num 1)]
    let lhs := STerm.letIn "x5" none x m
    return (ps, .ident "Nat", lhs, ← pick [STerm.num 0, .num 1], [])
  let pairScrut ← chance 60
  if pairScrut then
    let ps : List (String × STerm) := [("q0", .prod (.ident "Nat") (.ident "Nat")), ("h", hTy)]
    let block := STerm.matchGen (.ident "q0") [("Mk", ["p1", "p2"], clo (.ident "p1"))]
    let cont := STerm.matchGen (.ident "q0") [("Mk", ["a", "b"], .matchGen (.ident "a") [("Z", [], useZ), ("S", ["_"], useS)])]
    let lhs := STerm.letIn "f" none block cont
    let rhs ← pick [STerm.top, .matchGen (.ident "q0") [("Mk", ["a", "b"], .matchGen (.ident "a") [("Z", [], .top), ("S", ["_"], .ident "False")])]]
    let zProof : STerm := .letIn "f" none block (.letIn "x5" none (.call (.ident "f") [.unitLit]) (splitZ "x5" (.ident "refl")))
    let proofs := [.matchGen (.ident "q0") [("Mk", ["a", "b"], .matchGen (.ident "a") [("Z", [], .ident "refl"), ("S", ["_"], .ident "refl")])],
                   .matchGen (.ident "q0") [("Mk", ["a", "b"], .matchGen (.ident "a") [("Z", [], zProof), ("S", ["_"], .ident "refl")])]]
    pure (ps, .sort 0, lhs, rhs, proofs)
  else
    let ps : List (String × STerm) := [("n0", .ident "Nat"), ("h", hTy)]
    let annotated ← chance 50
    let block := STerm.matchGen (.ident "n0") [("Z", [], clo (.ident "n0")), ("S", ["p"], clo (.ident "n0"))]
    let fTy : STerm := .pi [("u", .ident "Unit")] (famOf (.ident "n0"))
    let cont := STerm.matchGen (.ident "n0") [("Z", [], useZ), ("S", ["_"], useS)]
    let lhs := STerm.letIn "f" (if annotated then some fTy else none) block cont
    let rhs ← pick [STerm.top, .matchGen (.ident "n0") [("Z", [], .top), ("S", ["_"], .ident "False")]]
    let zProof : STerm := .letIn "f" (if annotated then some fTy else none) block
      (.letIn "x5" none (.call (.ident "f") [.unitLit]) (splitZ "x5" (.ident "refl")))
    let proofs := [.matchGen (.ident "n0") [("Z", [], zProof), ("S", ["_"], .ident "refl")]]
    pure (ps, .sort 0, lhs, rhs, proofs)

/-- The template names the A1 family needs. -/
def a1Lib : List String := ["B2", "Bx", "TF", "TG", "CmpBx", "CmpB2", "HG", "HF"]

def mkCase (seed i : Nat) (fuel : Nat := 200000) (a1 : Nat := 0) (edep : Nat := 0) : Case × Rng := Id.run do
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
  let c0 : Case := { lib := lib, extra := extras.map (·.1), params := ps, ty := A, lhs := lhs, rhs := rhs, conv := conv }
  -- `a1` percent of the cases are the A1 family instead, drawn from their own streams so
  -- that every other case is the one it would be without the family
  let (x, _) := (caseRng seed (i + 1000003)).next
  if a1 > 0 && x.toNat % 100 < a1 then
    let ((ps, A, lhs, rhs, prf), g4) := genA1.run { rng := caseRng seed (i + 2000003) }
    return ({ c0 with lib := closeDeps (lib ++ a1Lib), params := ps, ty := A, lhs := lhs, rhs := rhs,
                      conv := none, extraProofs := prf }, g4.rng)
  let (y, _) := (caseRng seed (i + 3000017)).next
  if edep > 0 && y.toNat % 100 < edep then
    let ((ps, A, lhs, rhs, prf), g5) := genEDep.run { rng := caseRng seed (i + 4000037) }
    return ({ c0 with lib := closeDeps (lib ++ a1Lib), params := ps, ty := A, lhs := lhs, rhs := rhs,
                      conv := none, extraProofs := prf }, g5.rng)
  (c0, g3.rng)

end Ochr.Fuzz
