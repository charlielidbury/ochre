import Ochr.Meaning.DataModel.Exists.Knot.Grammar
import Ochr.Meaning.DataModel.Canonical.Knot

/-!
# The knot, part 3: the interpreter and its canonical frame (exists5)

The knot's field types (`ftyK`), read off the field-type term:
* along the spine: `M(ā)` is `M`'s record at the arguments (`d`'s own through the knot's record
  function `R`, an earlier declaration's through the model's); a parameter is itself;
* elsewhere (a steady node: an equation, a call, a value argument): the run's value under `K` at a
  CANONICAL frame (`canFrame`) rebuilt from the record key: the earlier fields that are an index and do
  not vary are rebuilt as the members of their canonical types with the key's small readings, the
  parameters that do not vary are themselves, and everything else (what varies, the fields that are no
  index) is a dummy `0 : Nat`; the fields not yet bound are `moved` at the error type, as the checker's
  `fieldTele` binds them.

`semT` gives a term's value (what the run gives as a value: a type's code, a parameter, a steady
node's run), `itpT` its field type (`FTy`), `itpArgs` the arguments of an applied declaration, each at
its parameter's type at the earlier ones as the hint (as `runParams` runs them).
-/

namespace Ochr.Meaning.DataModel.Exists.Knot

open Ochr Ochr.Meaning Ochr.Meaning.DataLib Ochr.Meaning.Canonical
open Classical

variable (K : RunCtx) (ρ : Assignment) (d : IndDecl)

/-- A dummy binding at a declared reading: `0 : Nat`. -/
noncomputable def dummyB (dc : DeclInfo) : SBinding := faithBind TyM.nat (.el0 Nat 0) dc

/-- The run's value of a term at a frame and hint, under `K` (`err` where the run is undefined). -/
noncomputable def valOf (s : SState) (h : TyS) (t : Term) : Sem :=
  match runT K ρ noFuture false h t s with
  | some (r, _) => r.1
  | none => .err

/-- A member of `T` with the small reading `sm` (there is at most one, `Piece3.memTy_small_inj`;
`err` when there is none). -/
noncomputable def rebuild (T : TyM) (sm : Small) : Sem :=
  if h : ∃ v, v ∈ₛ[K.dm.read] T ∧ v.small = sm then h.choose else .err

/-- The shape a field type gives (what `uShape` reads off a record holding its kind and
continuation at the field's key). -/
noncomputable def shapeOf (F : FTy) : Shape :=
  match F.kind with
  | .data d' => if d'.sort == 0 then .prf d' F.cont else .sub d' F.cont
  | .leaf B c => .leaf B c
  | _ => .leaf PEmpty .err

/-- The record an applied declaration is read at: `d`'s through the knot's record function, an
earlier one's through the model's. -/
noncomputable def recFor (R : List Sem → Rec) (M : IndDecl) : List Sem → Rec :=
  if M = d then R else K.dm.recOf M

mutual
/-- A term's value at the canonical frame `s` and the hint `h`. -/
noncomputable def semT (R : List Sem → Rec) (ps : List Sem) (s : SState) (h : TyS) : Term → Sem
  | .tind n as => match K.Γ.find? (·.name == n) with
    | some M => .ty (uTyR M (recFor K d R M (itpArgs R ps s M 0 [] as)))
    | none => .ty TyM.err
  | .place (.var v) =>
    if v < d.params.length then ps.getD (d.params.length - 1 - v) .err else valOf K ρ s h (.place (.var v))
  | t => valOf K ρ s h t

/-- The arguments of `M(…)` from parameter `j`, after the values `pre`. -/
noncomputable def itpArgs (R : List Sem → Rec) (ps : List Sem) (s : SState) (M : IndDecl) :
    Nat → List Sem → List Term → List Sem
  | _, _, [] => []
  | j, pre, a :: as =>
    argSem R ps s M j pre a :: itpArgs R ps s M (j + 1) (pre ++ [argSem R ps s M j pre a]) as

/-- One argument's value: a type argument read by `semT`, a value argument as its run (it is steady). -/
noncomputable def argSem (R : List Sem → Rec) (ps : List Sem) (s : SState) (M : IndDecl) (j : Nat)
    (pre : List Sem) : Term → Sem
  | a => if M.paramIsType j then semT R ps s (.plain TyM.err) a
    else valOf K ρ s (.plain TyM.err) a
end

/-- A term's field type at the canonical frame `s` and the hint `h`. -/
noncomputable def itpT (R : List Sem → Rec) (ps : List Sem) (s : SState) (h : TyS) : Term → FTy
  | .tind n as => match K.Γ.find? (·.name == n) with
    | some M => .data M (recFor K d R M (itpArgs K ρ d R ps s M 0 [] as))
    | none => .ty TyM.err
  | t => .ty (semT K ρ d R ps s h t).asTy

/-- **The canonical frame** of field `i` of constructor `c`, at the parameters `ps` and the key's
projected small readings `es`, given the canonical types of the earlier fields (`tyOf`). -/
noncomputable def canFrame (ps : List Sem) (c i : Nat) (es : List Small) (tyOf : Nat → TyM) : SState :=
  stateOf 0 (((List.range (arity d c)).map fun j =>
      if j < i then
        if fieldVaries d c j = false ∧ (d.indexFields c).contains j = true then
          faithBind (tyOf j) (rebuild K (tyOf j) (es.getD j .other))
            (if fieldProof K.D d c j then .prop else .other)
        else dummyB (if fieldProof K.D d c j then .prop else .other)
      else faithBind TyM.err .moved .other) ++
    (List.range d.params.length).map fun j =>
      if paramVaries d j then dummyB ((paramDecls K.D d (arity d c)).getD j .other)
      else faithBind (if j < ps.length then K.dm.paramTy d j (ps.take j) else TyM.err) (ps.getD j .err)
        ((paramDecls K.D d (arity d c)).getD j .other))

/-- **The knot's field types**: field `i`'s term read by the interpreter at its canonical frame, the
earlier fields' canonical types read off their own field types (strong recursion on `i`). -/
noncomputable def ftyK (R : List Sem → Rec) (ps : List Sem) (c : Nat) : Nat → List Small → FTy
  | i, es => match fieldTerm d c i with
    | some FT => itpT K ρ d R ps
        (canFrame K d ps c i es fun j => if _h : j < i then shapeTyP (shapeOf (ftyK R ps c j (es.take j))) else TyM.err)
        (.plain (TyM.univ 1)) FT
    | none => .ty TyM.err
termination_by i => i

end Ochr.Meaning.DataModel.Exists.Knot
