import Ochr.Meaning.Sem

/-!
# The model of inductive types

An inductive declaration means, at each tuple of parameter meanings, the least family of sets
closed under its constructors (docs/18 Def. "meaning of types"). In Lean that family is a small
type built by the stage construction of `Ochr/Model/Slice.lean` §4 generalised to telescopes
(stage `k + 1` is a `Σ` over constructors of the telescope of field carriers, recursive fields at
stage `k`; the carrier is the colimit). The spine does not fix the construction: it fixes the
*interface* a data type must provide to the step lemmas, `DataModel`, and states its laws. The
library's declarations are modelled by hand (`libModel`, as `Slice.lean` models `Nat` and `Pair`);
the generic construction for every accepted program is milestone 2's `genericDataModel` (Q2).

`Nat` and `Unit` are not declarations (`Value.tNat`, `Value.tUnit`, `zero`, `succ`, `unit`) and
are modelled directly in `Value.lean` as `Nat` and `Unit`.
-/

namespace Ochr.Meaning

/-- The model of the program's inductive declarations. Parameters are passed as meanings: a
type parameter as `Sem.ty T`, a value parameter (D71) as the value's meaning. `fieldTy d ps c i
earlier` is the meaning of the declared type of field `i` of constructor `c` at the parameters
and the meanings of the earlier fields (the telescope, D64), as the reference run computes it;
it is part of the model because the laws are stated with it. `covers d` says which declarations
the model speaks for; the laws hold for those. -/
structure DataModel where
  covers : IndDecl → Prop
  /-- The carrier of `D(ps)`: a small Lean type. -/
  car : IndDecl → List Sem → Type
  fieldTy : IndDecl → List Sem → Nat → Nat → List Sem → TyM
  /-- The meaning of the declared type of parameter `i` at the earlier parameters (a type
  parameter's is its sort; a value parameter's, D71, a data type). -/
  paramTy : IndDecl → Nat → List Sem → TyM
  /-- Pack a constructor's fields, given as meanings, into an element; `none` if some field is
  not a member of its field type (the fields are read in telescope order). -/
  pack : (d : IndDecl) → (ps : List Sem) → Nat → List Sem → Option (car d ps)
  tag : {d : IndDecl} → {ps : List Sem} → car d ps → Nat
  fields : {d : IndDecl} → {ps : List Sem} → car d ps → List Sem
  /-- The rank, for guarded recursion (docs/24): a recursive field has a smaller rank. -/
  rank : {d : IndDecl} → {ps : List Sem} → car d ps → Nat
  tag_pack : ∀ {d ps c fs} (x : car d ps), covers d → pack d ps c fs = some x → tag x = c
  fields_pack : ∀ {d ps c fs} (x : car d ps), covers d → pack d ps c fs = some x → fields x = fs
  /-- Every element is a constructor applied to its fields (the carrier is a least fixed point). -/
  pack_fields : ∀ {d ps} (x : car d ps), covers d → pack d ps (tag x) (fields x) = some x
  /-- Packing succeeds exactly when each field is a member of its field type at the earlier
  fields, and there are as many as the constructor declares. -/
  pack_isSome : ∀ {d ps c fs}, covers d →
    ((pack d ps c fs).isSome ↔
      ∃ ctor, d.ctors[c]? = some ctor ∧ fs.length = ctor.2.length ∧
        ∀ i (h : i < fs.length), fs[i] ∈ₛ fieldTy d ps c i (fs.take i))
  /-- A recursive field, an element of the same inductive at any parameters, has smaller rank. -/
  rank_lt : ∀ {d ps ps'} (x : car d ps) (y : car d ps'), covers d →
    Sem.el0 (car d ps') y ∈ fields x → rank y < rank x

namespace DataModel

variable (dm : DataModel)

/-- The meaning of the type `D(ps)`: a data type is its carrier; a `Prop`-sorted declaration
the truncation of the same fixed point, true when it is inhabited. -/
def tyM (d : IndDecl) (ps : List Sem) : TyM :=
  if d.sort == 0 then .prop (Nonempty (dm.car d ps)) else .ty0 (dm.car d ps)

/-- Parameters whose carrier is the type `T` (docs/31 D8): for a constructor value that records
no parameters, read at the type of its position. Chosen classically; any choice with that
carrier gives an element tagged `T`'s carrier (`paramsOf_car`). -/
noncomputable def paramsOf (d : IndDecl) : TyM → Option (List Sem)
  | .ty0 A => open Classical in
    if h : ∃ ps, dm.car d ps = A then some (Classical.choose h) else none
  | _ => none

theorem paramsOf_car (d : IndDecl) (A : Type) (ps : List Sem) (h : dm.paramsOf d (.ty0 A) = some ps) :
    dm.car d ps = A := by
  by_cases hex : ∃ ps, dm.car d ps = A
  · have : dm.paramsOf d (.ty0 A) = some (Classical.choose hex) := by
      simp [paramsOf, hex]
    rw [this] at h
    cases h
    exact Classical.choose_spec hex
  · simp [paramsOf, hex] at h

/-- The meaning of a constructor value `C(ps; fs)` of a data type whose fields already mean
`fs`: packed into the carrier when every field is whole, kept as an untyped tuple when some
field holds `moved` (D84: a definite value lying in no type), the error value when a whole
field is not of its type. A `Prop`-sorted declaration's constructor values are `⋆` already
(`Machine.evalCtor`, D42), so `ctorM` is only applied to data. -/
noncomputable def ctorM (d : IndDecl) (ps : List Sem) (c : Nat) (fs : List Sem) : Sem :=
  open Classical in
  if ∀ f ∈ fs, f.whole then
    match dm.pack d ps c fs with
    | some x => .el0 (dm.car d ps) x
    | none => .err
  else .ctor d.name c fs

/-- The fields of a meaning of a constructor value, if it is one. -/
noncomputable def fieldsOf (d : IndDecl) (ps : List Sem) : Sem → Option (Nat × List Sem)
  | .el0 A x => open Classical in
    if h : A = dm.car d ps then some (dm.tag (h ▸ x), dm.fields (h ▸ x)) else none
  | .ctor n c fs => if n = d.name then some (c, fs) else none
  | _ => none

/-! ## The library's declarations, modelled by hand -/

/-- The carrier of a level-0 type meaning, for the hand-written models (`PEmpty` off level 0). -/
def TyM.el0 : TyM → Type
  | .ty0 A => A
  | .prop P => PLift P
  | _ => PEmpty

/-- `Pair(A, B)` means `A × B`; `False` the empty type, `True` the unit type and `And(P, Q)` the
product of proofs (so their truncations are `False`, `True` and `P ∧ Q`). -/
def libCar : IndDecl → List Sem → Type
  | ⟨"Pair", _, _, _, _, _, _⟩, [.ty A, .ty B] => TyM.el0 A × TyM.el0 B
  | ⟨"False", _, _, _, _, _, _⟩, [] => PEmpty
  | ⟨"True", _, _, _, _, _, _⟩, [] => PUnit
  | ⟨"And", _, _, _, _, _, _⟩, [.ty P, .ty Q] => TyM.el0 P × TyM.el0 Q
  | _, _ => PEmpty

/-- The library model (`Prelude.decls`: `Pair`, `False`, `True`, `And`). Its laws are routine
case analyses, left to provers. -/
noncomputable def libModel : DataModel where
  covers d := d.name ∈ ["Pair", "False", "True", "And"]
  car := libCar
  fieldTy d ps _ i _ := match d.name, ps with
    | "Pair", [.ty A, .ty B] | "And", [.ty A, .ty B] => if i = 0 then A else B
    | _, _ => .err
  paramTy d _ _ := if d.name = "Pair" then .univ 1 else if d.name = "And" then .univ 0 else .err
  pack := sorry
  tag := sorry
  fields := sorry
  rank _ := 0
  tag_pack := sorry
  fields_pack := sorry
  pack_fields := sorry
  pack_isSome := sorry
  rank_lt := sorry

end DataModel

end Ochr.Meaning
