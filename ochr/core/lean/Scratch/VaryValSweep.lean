import Ochr.Meaning.DataModel.Exists.Knot.Checks
import Ochr.Examples.Registry
import Ochr.Meaning.DataModel.Exists.HintShapes

/-! exists9: `Records.VaryValFree` (no field type reads a varying value parameter) and "no parameter
type holds an embedded value", at every stored inductive declaration of every registered block. -/

open Ochr Ochr.Test Ochr.Registry Ochr.Meaning.DataModel.Exists.Knot

def allFieldsB (d : IndDecl) (P : Nat → Term → Bool) : Bool :=
  d.ctors.zipIdx.all fun (cs, c) => cs.2.all fun (_, FT) => P c FT

def varyValB (d : IndDecl) : Bool :=
  let np := d.params.length
  allFieldsB d fun _ FT => FT.freeVars.all fun v => !(v < np) || !paramVaries d (np - 1 - v) || d.paramIsType (np - 1 - v)

def checksFail (d : IndDecl) : List String :=
  [("varyval", varyValB d),
   ("pnoval", d.params.all fun p => !p.2.anyAtom (fun _ => true)),
   ("hasVaryingValueParam", !((List.range d.params.length).any fun j => paramVaries d j && !d.paramIsType j))
  ].filterMap fun (n, b) => if b then none else some n

def sweep (blocks : List (String × Surface.Block)) : List (String × String × List String) :=
  blocks.flatMap fun (bn, b) =>
    let prog : Surface.Program := libOf {} 2000000 b ++ b.decls
    let items : List Item := prog.filterMap fun d => match Surface.resolveProgram prog d with
      | .ok it => some it
      | .error _ => none
    let inds := (globalsAfter {} items).2
    let own := b.decls.map (·.name)
    (inds.filter fun d => own.contains d.name).map fun d => (bn, d.name, checksFail d)

def blocks : List (String × Surface.Block) :=
  (programs ++ caseStudies) ++ [("HintShapes", Ochr.Meaning.DataModel.Exists.HintShapes.HintShapes)]

#eval show IO Unit from do
  let fr := ((← IO.getEnv "SWEEP_FROM").bind String.toNat?).getD 0
  let to := ((← IO.getEnv "SWEEP_TO").bind String.toNat?).getD blocks.length
  let bs := (blocks.drop fr).take (to - fr)
  let mut n := 0
  let mut nbad := 0
  for (b, _) in bs.zipIdx do
    let r := sweep [b]
    n := n + r.length
    for x in r do
      if !x.2.2.isEmpty then
        nbad := nbad + 1
        IO.println (repr x)
    IO.println s!"block {b.1}: {r.length}"
    (← IO.getStdout).flush
  IO.println s!"blocks {fr}..{to} of {blocks.length}: declarations stored: {n}, flagged: {nbad}"
