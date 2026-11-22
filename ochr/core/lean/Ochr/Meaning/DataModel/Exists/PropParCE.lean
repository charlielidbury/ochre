import Ochr.Test

/-!
# What a data type's knot asks of an earlier `Prop`-sorted declaration (exists10, 2026-11-22)

`knot_exists` asked, until exists10, that the records of EVERY other declaration be parametric in their
nestable parameters (`hpar`: lists agreeing below depth `n` at the nestable parameters, equal elsewhere,
give records agreeing below `n`). The assembly must supply that from the earlier stages, and for a
`Prop`-sorted declaration the model's records are the truth spec's (`truth_exists`), which come with
monotonicity, not parametricity. They need not be parametric: `Q` below is accepted with its parameter
stored nestable, and the truth spec reads `Q`'s own occurrence `Q(A)` in `Step` as the proposition
`T(A)`, `T` the least fixed point; at `A` the code of a data type at a record `R`, `T(A)` is "the
carrier at `R` is inhabited", which two records agreeing below any depth can answer differently (a
chain whose leaf at depth `n + 5` is empty in one and `Unit` in the other). So the record of `Q` at
the two lists differs at the key of `Step`'s field, of length one. (Argued here, not kernel-checked:
the restatement below does not rest on it.)

The knot never needs it. It reads an earlier declaration's records at two different lists only where
the declaration is applied to an argument that mentions `d` or a varying (nestable) parameter of `d`,
and the checker's rule (A*) (D121) makes such a declaration `d`'s own sort:
* (i) `sortNestViolation`: an applied declaration whose arguments mention `d` has `d`'s sort (`D`
  below is rejected);
* (ii) `nestableSet`: a parameter passed to a declaration of the other sort is not nestable (`W`'s
  parameter below is stored non-nestable, so `Q(B)` in `W` is steady).

So `knot_exists` now asks parametricity of the DATA-sorted declarations only, and that a `Prop`-sorted
declaration heading a field type has steady arguments (`Knot.TopSortOk`, derived from the checks in
`FromChecks.grammar_of_checks`); `Knot.ParHyp` is the pair. A data-sorted declaration nested inside an
argument of a `Prop`-sorted one is rejected by (i) as well, and inside an argument the knot's grammar
already asked the head to be data-sorted (`SpineArgs.type`'s `hA`).
-/

namespace Ochr.Meaning.DataModel.Exists.PropParCE

open Ochr Ochr.Test

ochr PropPar {
  inductive Q (A : Type) : Prop := Base(x : A) | Step(q : Q(A))
  reject inductive D := MkD(h : Q(D))
  inductive W (B : Type) := MkW(h : Q(B))
  inductive V := Leaf | MkV(h : Q(Nat), v : V)
}

#guard (Ochr.Test.run "PropPar" PropPar).rejectedWith [
  ("D", "field h of MkD : Q(D): D, a type of data, occurs inside an argument of Q, a proposition, and a nested occurrence passes only through declarations of its own sort (D121; Lean's kernel: \"mutually inductive types must live in the same universe\")")]

def items : List Item :=
  (Prelude.decls ++ PropPar.decls).filterMap fun d => match Surface.resolveProgram (Prelude.decls ++ PropPar.decls) d with
    | .ok it => some it
    | .error _ => none

-- `Q`'s parameter is stored nestable (so `hpar` at `Q` would be asked at lists that differ there);
-- `W`'s is not (it is passed to `Q`, of the other sort), so `Q(B)` is steady in `W`
#guard ((globalsAfter {} items).2.filter (fun d => ["Q", "D", "W", "V"].contains d.name)).map
  (fun d => (d.name, d.nestable, d.sort)) == [("Q", [true], 0), ("W", [false], 1), ("V", [], 1)]

end Ochr.Meaning.DataModel.Exists.PropParCE
