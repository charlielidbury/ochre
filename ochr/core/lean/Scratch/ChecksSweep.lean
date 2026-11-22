import Ochr.Meaning.DataModel.Exists.Knot.Checks
import Ochr.Examples.Registry
import Ochr.Meaning.DataModel.Exists.HintShapes

/-! The bundle `IndChecks` (and `FieldsNoVal`, and no nestable value parameter) evaluated at every
stored inductive declaration of every registered block: an empirical test of the named bridge
`CheckIndGivesChecks`. Run with `SWEEP_HALF=0` / `1` to split the blocks. -/

open Ochr Ochr.Test Ochr.Registry Ochr.Meaning.DataModel.Exists.Knot

def allFieldsB (d : IndDecl) (P : Nat → Term → Bool) : Bool :=
  d.ctors.zipIdx.all fun (cs, c) => cs.2.all fun (_, FT) => P c FT

def checksFail (Γ0 : List IndDecl) (d : IndDecl) : List String :=
  [("fresh", (Γ0.find? (·.name == d.name)).isNone),
   ("nest", d.nestable == nestableSet (nestTableOf Γ0) (sortTableOf Γ0 d) d),
   ("tele", d.ctors.zipIdx.all fun (cs, c) => cs.2.zipIdx.all fun (f, i) => (d.fieldRefs c f.2).all (· < i)),
   ("fo", allFieldsB d fun _ FT => foB (declEnv Γ0 d) (ownNest Γ0 d) d.name d.params.length FT),
   ("rv", allFieldsB d fun c FT => !rvB (declEnv Γ0 d) (readsOf d c) FT),
   ("sv", allFieldsB d fun _ FT => (sortNestViolation (sortTableOf Γ0 d) d.name d.sort FT).isNone),
   ("noval", allFieldsB d fun _ FT => !FT.anyAtom (fun _ => true)),
   ("val", (List.range d.params.length).all fun j => !nestOf d j || d.paramIsType j)
  ].filterMap fun (n, b) => if b then none else some n

def sweep (blocks : List (String × Surface.Block)) : List (String × String × List String) :=
  blocks.flatMap fun (bn, b) =>
    let prog : Surface.Program := libOf {} 2000000 b ++ b.decls
    let items : List Item := prog.filterMap fun d => match Surface.resolveProgram prog d with
      | .ok it => some it
      | .error _ => none
    let inds := (globalsAfter {} items).2
    let own := b.decls.map (·.name)
    (inds.zipIdx.filter fun (d, _) => own.contains d.name).map fun (d, k) =>
      (bn, d.name, checksFail (inds.take k) d)

def blocks : List (String × Surface.Block) :=
  (programs ++ caseStudies) ++ [("HintShapes", Ochr.Meaning.DataModel.Exists.HintShapes.HintShapes)]

#eval show IO Unit from do
  let fr := ((← IO.getEnv "SWEEP_FROM").bind String.toNat?).getD 0
  let to := ((← IO.getEnv "SWEEP_TO").bind String.toNat?).getD blocks.length
  let bs := (blocks.drop fr).take (to - fr)
  let mut n := 0
  let mut nbad := 0
  for (b, k) in bs.zipIdx do
    let r := sweep [b]
    n := n + r.length
    for x in r do
      if !x.2.2.isEmpty then
        nbad := nbad + 1
        IO.println (repr x)
    IO.println s!"block {fr + k} {b.1}: {r.length} stored"
    (← IO.getStdout).flush
  IO.println s!"blocks {fr}..{to} of {blocks.length}: declarations stored: {n}, failing: {nbad}"
