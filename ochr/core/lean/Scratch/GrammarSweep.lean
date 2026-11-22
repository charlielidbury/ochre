import Ochr.Meaning.DataModel.Exists.Knot.Grammar
import Ochr.Examples.Registry
import Ochr.Meaning.DataModel.Exists.HintShapes

open Ochr Ochr.Test Ochr.Registry Ochr.Meaning.DataModel.Exists.Knot

def gramB (Γ : List IndDecl) (d : IndDecl) : Bool :=
  d.ctors.zipIdx.all fun (cs, c) => cs.2.all fun (_, FT) =>
    if d.sort == 0 then pspineB Γ d c FT else spineB Γ d c FT

def badFields (Γ : List IndDecl) (d : IndDecl) : List String :=
  d.ctors.zipIdx.flatMap fun (cs, c) => cs.2.filterMap fun (fn, FT) =>
    let ok := (if d.sort == 0 then pspineB Γ d c FT else spineB Γ d c FT)
    if ok then none else some s!"{cs.1}.{fn} : {FT.pp []}"

def sweep (blocks : List (String × Surface.Block)) : List (String × String × Nat × Bool × Bool × List String) :=
  blocks.flatMap fun (bn, b) =>
    let prog : Surface.Program := libOf {} 2000000 b ++ b.decls
    let items : List Item := prog.filterMap fun d => match Surface.resolveProgram prog d with
      | .ok it => some it
      | .error _ => none
    let inds := (globalsAfter {} items).2
    let own := b.decls.map (·.name)
    (inds.filter fun d => own.contains d.name).map fun d =>
      let g := gramB inds d
      let a := true
      (bn, d.name, d.sort, g, a, badFields inds d)

#eval do
  let all := sweep ((programs ++ caseStudies) ++ [("HintShapes", Ochr.Meaning.DataModel.Exists.HintShapes.HintShapes)])
  let r := all.filter fun (x : String × String × Nat × Bool × Bool × List String) => !(x.2.2.2.1 && x.2.2.2.2.1)
  let np := (all.filter fun (x : String × String × Nat × Bool × Bool × List String) => x.2.2.1 == 0).length
  IO.println s!"declarations stored: {all.length}, Prop-sorted: {np}, failures: {r.length}"
  for x in r do IO.println (repr x)
