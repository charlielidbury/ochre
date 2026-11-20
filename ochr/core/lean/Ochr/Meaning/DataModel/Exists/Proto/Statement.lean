import Ochr.Meaning.DataModel.Faithful

/-!
# Prototype: faithfulness restated (tasks 2b, 2c, 2d)

What `DataModel/Faithful.lean` becomes at the port, here beside the old forms:
* **2b** the parameter list has the declaration's length (`StatementCE.fieldsFaithful_false_short`);
* **2c** the telescope's frame binds as the checker's `Machine.fieldTele` does
  (`StatementCE.fieldsFaithful_false_frame`): the fields first, each at `other` until its type is
  computed and then at `prop` if the checker reads it as a proof (`isProof`, the checker's
  `Decide.fieldTermIsProp`), else `other`; then each parameter at its declared reading
  (`Decisions.typeDecl` of its type term in the scope of the fields and the earlier parameters,
  as `fieldTele`'s `typeDecl` reads it with the frame live);
* **2d** conditional: wherever the run of the declared type is defined, it means the model's type
  (definedness comes to the consumers from their own simulation of the checker's `evalType`).
2a (a leaf's type is its code) is `Proto/Layout.shapeTyP`.
-/

namespace Ochr.Meaning.DataModel.Exists.Proto

open Ochr Ochr.Meaning

/-- A binding holding `v` at type `T`, read as `dc`. -/
def faithBindD (T : TyM) (v : Sem) (dc : DeclInfo) : SBinding := { ty := .plain T, val := fun _ => v, decl := dc }

/-- The declared readings of the parameters, as `fieldTele` binds them: each its type term's
reading in the scope of the earlier parameters (innermost first) above `k` fields read `other`. -/
def paramDecls (D : Decisions) (d : IndDecl) (k : Nat) : List DeclInfo :=
  d.params.foldl (fun acc hp => acc ++ [D.typeDecl (acc.reverse ++ List.replicate k .other) hp.2]) []

/-- **2c**: the frame `fieldTele` evaluates field `e.length` of constructor `c` in, as meanings. -/
noncomputable def teleFrameR (dm : DataModel) (D : Decisions) (isProof : IndDecl → Nat → Nat → Bool)
    (d : IndDecl) (ps : List Sem) (c : Nat) (e : List Sem) : SState :=
  let k := ((d.ctors[c]?).map (·.2.length)).getD 0
  let fs := e ++ List.replicate (k - e.length) Sem.moved
  let pds := paramDecls D d k
  stateOf 0 (fs.zipIdx.map (fun vi => faithBindD (dm.fieldTy d ps c vi.2 (e.take vi.2)) vi.1
      (if vi.2 < e.length && isProof d c vi.2 then .prop else .other)) ++
    ps.zipIdx.map (fun vj => faithBindD (dm.paramTy d vj.2 (ps.take vj.2)) vj.1 (pds.getD vj.2 .other)))

/-- The frame parameter `j`'s declared type is evaluated in: the earlier parameters at their
readings. -/
noncomputable def paramFrameR (dm : DataModel) (D : Decisions) (d : IndDecl) (ps : List Sem) : SState :=
  let pds := paramDecls D d 0
  stateOf 0 (ps.zipIdx.map (fun vj => faithBindD (dm.paramTy d vj.2 (ps.take vj.2)) vj.1 (pds.getD vj.2 .other)))

/-- **Field types, restated** (2b, 2c, 2d). -/
def FieldsFaithfulR (K : RunCtx) (ρ : Assignment) (isProof : IndDecl → Nat → Nat → Bool) : Prop :=
  ∀ d ∈ K.Γ, ∀ (ps : List Sem) (c i : Nat) (e : List Sem) (FT : Term),
    ps.length = d.params.length → ParamsTyped K.dm d ps → FieldsTyped K.dm d ps c e → e.length = i →
    fieldTerm d c i = some FT →
    ∀ r s', run K ρ noFuture (.plain (TyM.univ 1)) FT (teleFrameR K.dm K.D isProof d ps c e) = some (r, s') →
      r.1.asTy = K.dm.fieldTy d ps c i e

/-- **Parameter types, restated** (2b, 2c, 2d). -/
def ParamsFaithfulR (K : RunCtx) (ρ : Assignment) : Prop :=
  ∀ d ∈ K.Γ, ∀ (ps : List Sem) (j : Nat) (hn : Hint) (PT : Term),
    ParamsTyped K.dm d ps → ps.length = j → d.params[j]? = some (hn, PT) →
    ∀ r s', run K ρ noFuture (.plain (TyM.univ 2)) PT (paramFrameR K.dm K.D d ps) = some (r, s') →
      r.1.asTy = K.dm.paramTy d j ps

/-- **The run context's data model is faithful, restated.** `RecordsFaithful` keeps its three
clauses (its `types` clause reads a parameter's type by continuation at the port, §3 of the
lane's report). -/
def CtxFaithfulR (K : RunCtx) (isProof : IndDecl → Nat → Nat → Bool) : Prop :=
  ∀ (Δ : Nat → TyS) (ρ : Assignment),
    FieldsFaithfulR { K with Δ := Δ } ρ isProof ∧ ParamsFaithfulR { K with Δ := Δ } ρ ∧ RecordsFaithful K

end Ochr.Meaning.DataModel.Exists.Proto
