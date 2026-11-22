import Ochr.Meaning.DataModel.Exists.PreludeModel
import Ochr.Test

/-!
# Nesting across sorts: accepted by the checker, rejected by Lean (exists6, 2026-11-22)

Rule (A) (docs/34 §18.6) checks, at an occurrence `M(…d…)` of a data-sorted `d`, that `M` is
data-sorted. It does not follow the parameter on: `M` may pass it to a declaration of the other sort.
The checker accepts all of the following (asserted below), and Lean's kernel rejects `D`, `QW` and `Q`
("mutually inductive types must live in the same universe", checked with the local toolchain):
* `PP (A : Type) : Prop := MkPP(x : A)`, `E (A : Type) := MkE(p : PP(A))`, `D := MkD(e : E(D))`: a
  data-sorted `D` nested in data-sorted `E`, which passes it to the `Prop`-sorted `PP`;
* `Wrap (P : Prop) := MkWrap(h : P)`, `QW : Prop := MkQW(w : Wrap(QW))`: a `Prop`-sorted declaration
  nested directly in a data-sorted one;
* `E2 (P : Prop) : Prop := MkE2(w : Wrap(P))`, `Q : Prop := MkQ(e : E2(Q))`: a `Prop`-sorted one nested
  in a `Prop`-sorted one, which passes it to a data-sorted one.

The checker stores `E`'s parameter as nestable (asserted). What follows (argued, not kernel-checked):
* `knot_exists`'s hypothesis `hpar` (every earlier declaration's records are parametric in its
  nestable parameters, `RAgree`) is false for `E` in every program that declares `E`, `D` or no `D`:
  a faithful record of `E` at a type code `A` holds at `p`'s key, at depth 0, the proposition "`PP(A)`
  is inhabited", that is "`A` is inhabited", which two codes agreeing below any depth can disagree on.
* `General.mono_prop`'s hypothesis (the shapes at `ps` and `ps'` are equal or weaker proposition
  leaves) cannot hold of `E2`'s records: the shape at `w` is `Wrap`'s record at `P`, a sub-record.

The repair proposed to the lead (rule (A*), Lean's): a nested occurrence passes only through
declarations of the occurring declaration's sort.
-/

namespace Ochr.Meaning.DataModel.Exists.CrossSortCE

open Ochr Ochr.Test

ochr CrossSort {
  inductive PP (A : Type) : Prop := MkPP(x : A)
  inductive E (A : Type) := MkE(p : PP(A))
  inductive D := MkD(e : E(D))
  inductive Wrap (P : Prop) := MkWrap(h : P)
  inductive QW : Prop := MkQW(w : Wrap(QW))
  inductive E2 (P : Prop) : Prop := MkE2(w : Wrap(P))
  inductive Q : Prop := MkQ(e : E2(Q))
}

-- all seven are accepted
#guard (Ochr.Test.run "CrossSort" CrossSort).rejectedWith []

def items : List Item :=
  (Prelude.decls ++ CrossSort.decls).filterMap fun d => match Surface.resolveProgram (Prelude.decls ++ CrossSort.decls) d with
    | .ok it => some it
    | .error _ => none

-- `PP`'s, `E`'s, `Wrap`'s and `E2`'s parameters are stored nestable
#guard ((globalsAfter {} items).2.filter (fun d => ["PP", "E", "Wrap", "E2"].contains d.name)).map
  (fun d => (d.name, d.nestable)) == [("PP", [true]), ("E", [true]), ("Wrap", [true]), ("E2", [true])]

end Ochr.Meaning.DataModel.Exists.CrossSortCE
