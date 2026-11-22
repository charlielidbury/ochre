import Ochr.Meaning.Run

/-!
# Faithfulness: the data model reads the declared types as the reference run does (docs/34 §9, §14)

What a data model owes the program beyond covering its declarations, and what `CtxOk` carries
(`faithful`) and the existence statement concludes (`Assembly.DataFaithful`):

1. **Field types** (`FieldsFaithful`): at a parameter list of the declaration's length, well
   typed with its earlier fields (`ParamsTyped`, `FieldsTyped`), WHEREVER the reference run of the
   declared field-type term is defined, in the frame the checker's `fieldTele` evaluates it in
   (`teleFrame`: the fields, each at `prop` or `other` as the checker marks it, the later ones
   `moved`, then the parameters at their declared readings), it means `dm.fieldTy`. Under the
   model itself: a field `List(A)` runs to `dm.tyM List [A]`. Type functions in field types read
   the program's earlier globals, so the run context is the program meaning's.
2. **Parameter types** (`ParamsFaithful`): the same for the declared parameter types and `paramTy`.
3. **Records keep the parameters `unifyTyS` reads back** (`RecordsFaithful`): the record at
   parameters keeps a level-0 type parameter's type (read by continuation, `paramTyOf`), and a value
   parameter of a level-0 type read small, at `paramKey`, which is where the run's constructor
   clause reads a parameter back off a field's type (`unifyTyS`); and it reads a value parameter
   only small, so the rebuilt parameter gives the same record.

Restated at the port of docs/34 §18 (`Exists/StatementCE.lean` for why): the length (a list too
short reads a field for a parameter), the frame's readings (`other` read a type parameter by move,
the checker copies it), and conditional (definedness at every well-typed input is evaluation
soundness, which the consumers get from their own simulation of the checker's `evalType`). The
degenerate model is still not faithful (`DataModel/Degenerate.lean`): its refutation uses a run
that is defined.

Restated again by the rulings (M-a) and (S) (exists2, 2026-11-21): as it stood, `RecordsFaithful` had
no instance at any non-empty `Γ` (`Exists/RecordsCE.lean`, at 1765a998). A `Prop`-sorted
declaration's raw data code was a member of `Type₀` and no record could mean it; it now has no level
(`Code0.level`, (M-a)). And `leafOk` read every key of the form `[(c, i, es)]`, parameter keys
included; it now reads the genuine field keys (`RecLeafOk`), `types` speaks of type parameters of a
full-length list, and `ParamsTyped` asks membership (its "or any type value" disjunct is gone).
-/

namespace Ochr.Meaning

/-- A binding holding `v` at type `T`, read as `dc`. -/
def faithBind (T : TyM) (v : Sem) (dc : DeclInfo := .other) : SBinding := { ty := .plain T, val := fun _ => v, decl := dc }

/-- The checker's verdict that field `i` of constructor `c` of `d` is a proof field
(`Decide.fieldTermIsProp`, which `Machine.fieldTele` marks a computed field by), as the decisions
read it: a field place's reading is `prop` exactly then (`Decide.placeDecl`'s `.field` case reads
`fieldIsProof` first). -/
def fieldProof (D : Decisions) (d : IndDecl) (c i : Nat) : Bool :=
  D.placeDecl [] (.field ⟨d.name, c, i, ""⟩ (.var 0)) matches .prop

/-- The declared readings of the parameters, as `Machine.fieldTele` binds them: each its type term's
reading in the scope of the earlier parameters (innermost first) above `k` fields read `other`. -/
def paramDecls (D : Decisions) (d : IndDecl) (k : Nat) : List DeclInfo :=
  d.params.foldl (fun acc hp => acc ++ [D.typeDecl (acc.reverse ++ List.replicate k .other) hp.2]) []

/-- **The frame `Machine.fieldTele` evaluates field `e.length` of constructor `c` in**, as meanings
(docs/34 §18, task 2c): the fields (the earlier ones `e`, each at its field type and read `prop` if
the checker reads it as a proof and `other` else; the rest, the field being typed among them,
`moved` at the error type and read `other`, as the checker binds them `⊥` with no type), then the
parameters, each at its type and at its declared reading.

The fields not yet bound are typed `err` (docs/31 D160, docs/34 §18.6): until then the field being
typed carried its own type, read from the model, which the checker's frame does not have (it fills
a field's type in only after evaluating it) and which made the knot's canonical frame
self-referential. `Exists/TeleFrameGuard.lean` pins the checker's frame. -/
noncomputable def teleFrame (dm : DataModel) (D : Decisions) (d : IndDecl) (ps : List Sem) (c : Nat)
    (e : List Sem) : SState :=
  let k := ((d.ctors[c]?).map (·.2.length)).getD 0
  let fs := e ++ List.replicate (k - e.length) Sem.moved
  let pds := paramDecls D d k
  stateOf 0 (fs.zipIdx.map (fun vi =>
      faithBind (if vi.2 < e.length then dm.fieldTy d ps c vi.2 (e.take vi.2) else TyM.err) vi.1
      (if vi.2 < e.length && fieldProof D d c vi.2 then .prop else .other)) ++
    ps.zipIdx.map (fun vj => faithBind (dm.paramTy d vj.2 (ps.take vj.2)) vj.1 (pds.getD vj.2 .other)))

/-- The frame parameter `j`'s declared type is evaluated in: the earlier parameters at their
readings. -/
noncomputable def paramFrame (dm : DataModel) (D : Decisions) (d : IndDecl) (ps : List Sem) : SState :=
  let pds := paramDecls D d 0
  stateOf 0 (ps.zipIdx.map (fun vj => faithBind (dm.paramTy d vj.2 (ps.take vj.2)) vj.1 (pds.getD vj.2 .other)))

/-- Parameters each a member of its declared type at the earlier ones. (A disjunct "or any type
value", from 84b67f95 with no stated reason, was deleted by the ruling (S): the run reads a parameter
strictly, `readPlace`'s `ReadGood`, so at a type value that is not a member the runs faithfulness
speaks of were undefined anyway, and the disjunct only made `RecordsFaithful` speak of junk.) -/
def ParamsTyped (dm : DataModel) (d : IndDecl) (ps : List Sem) : Prop :=
  ∀ j (h : j < ps.length), ps[j] ∈ₛ[dm.read] dm.paramTy d j (ps.take j)

/-- Earlier fields each of their field type at the ones before. -/
def FieldsTyped (dm : DataModel) (d : IndDecl) (ps : List Sem) (c : Nat) (e : List Sem) : Prop :=
  ∀ i (h : i < e.length), e[i] ∈ₛ[dm.read] dm.fieldTy d ps c i (e.take i)

/-- **Field types are the run's readings of the declared field-type terms** (docs/34 §18): at a
parameter list of the declaration's length (2b), in the frame the checker's `fieldTele` evaluates
in (2c), WHEREVER the run is defined (2d: definedness comes to the consumers from their own
simulation of the checker's `evalType`). -/
def FieldsFaithful (K : RunCtx) (ρ : Assignment) : Prop :=
  ∀ d ∈ K.Γ, ∀ (ps : List Sem) (c i : Nat) (e : List Sem) (FT : Term),
    ps.length = d.params.length → ParamsTyped K.dm d ps → FieldsTyped K.dm d ps c e → e.length = i →
    fieldTerm d c i = some FT →
    ∀ r s', run K ρ noFuture (.plain (TyM.univ 1)) FT (teleFrame K.dm K.D d ps c e) = some (r, s') →
      r.1.asTy = K.dm.fieldTy d ps c i e

/-- **Parameter types are the run's readings of the declared parameter types**, wherever the run is
defined. -/
def ParamsFaithful (K : RunCtx) (ρ : Assignment) : Prop :=
  ∀ d ∈ K.Γ, ∀ (ps : List Sem) (j : Nat) (hn : Hint) (PT : Term),
    ParamsTyped K.dm d ps → ps.length = j → d.params[j]? = some (hn, PT) →
    ∀ r s', run K ρ noFuture (.plain (TyM.univ 2)) PT (paramFrame K.dm K.D d ps) = some (r, s') →
      r.1.asTy = K.dm.paramTy d j ps

/-- **Records keep what `unifyTyS` reads back off a field's type** (docs/34 §14, Handoff 3b): at
`paramKey`, each level-0 type parameter's entry (`types`) and each value parameter of a level-0
type read small (`values`); and a record reads a value parameter only small (`smallOnly`: parameter
lists that differ only in value parameters with the same small readings have the same record), so
the parameter `unifyTyS` rebuilds from the small reading (`ofSmall`, `small_ofSmall`) gives the
written one's record. -/
structure RecordsFaithful (K : RunCtx) : Prop where
  types : ∀ d ∈ K.Γ, ∀ (ps : List Sem) (j : Nat) (A : Type) (c : Code0 A),
    ps.length = d.params.length → d.paramIsType j = true →
    ParamsTyped K.dm d ps → ps[j]? = some (.ty (.t0 A c)) →
    K.dm.paramTyOf (K.dm.recOf d ps) j = .t0 A c
  values : ∀ d ∈ K.Γ, ∀ (ps : List Sem) (j : Nat) (v : Sem) (A : Type) (c : Code0 A),
    ParamsTyped K.dm d ps → ps[j]? = some v → K.dm.paramTy d j (ps.take j) = .t0 A c →
    v ∈ₛ[K.dm.read] .t0 A c → K.dm.recOf d ps (paramKey j) = .small v.small
  smallOnly : ∀ d ∈ K.Γ, ∀ (ps ps' : List Sem), ParamsTyped K.dm d ps → ps'.length = ps.length →
    (∀ (j : Nat) (v v' : Sem), ps[j]? = some v → ps'[j]? = some v' →
      v' = v ∨ ((∃ (A : Type) (c : Code0 A), K.dm.paramTy d j (ps.take j) = .t0 A c ∧ v ∈ₛ[K.dm.read] .t0 A c) ∧
        v'.small = v.small)) →
    K.dm.recOf d ps' = K.dm.recOf d ps
  /-- A record at parameters keeps a data code over the model's own carrier as a `.data` entry,
  never as a leaf, at its genuine field keys (docs/34 §18, ruling (S)): what `ctorOut_mem` and the
  read lemma ask of a record. -/
  leafOk : ∀ d ∈ K.Γ, ∀ (ps : List Sem), ps.length = d.params.length → ParamsTyped K.dm d ps →
    K.dm.RecLeafOk d (K.dm.recOf d ps)

/-- **A field's level is the one its declaration's check gave it** (the lead's addition, stated,
not yet part of `CtxFaithful`): at well-typed parameters and earlier fields, a field the checker
reads as a proof (`isProof`, to be the checker's `Decide.fieldTermIsProp` on the field's declared
type, decided once when the declaration is checked) has a type of level `0`, and any other field a
type of another level. So "the checker reads this field as data" means "the model's field type is
not a proposition" with nothing evaluated at the use site. Checked against the syntax
`fieldTermIsProp` reads (`DataModel/Probes.lean`, `DMProbeLevel`): a proof field is a `Prop`
parameter, a `Prop`-sorted inductive (its code is `tyR`, of the declaration's sort), an equation,
or a call of a global declared to return `Prop` (its result is a member of `Sort 0`, a code of level
`0`); the ways a proposition could hide from that syntax (an `Id` field, a codomain that is a sort
only by computation) are rejected. -/
def FieldLevelsFaithful (K : RunCtx) (isProof : IndDecl → Nat → Nat → Bool) : Prop :=
  ∀ d ∈ K.Γ, ∀ (ps : List Sem) (c i : Nat) (e : List Sem),
    ParamsTyped K.dm d ps → FieldsTyped K.dm d ps c e → e.length = i → (fieldTerm d c i).isSome →
      ((K.dm.fieldTy d ps c i e).level = some 0 ↔ isProof d c i = true)

/-- **The run context's data model is faithful to its declarations**, at every assignment and
every Δ (the runs of declared types read neither). A field of `CtxOk`. -/
def CtxFaithful (K : RunCtx) : Prop :=
  ∀ (Δ : Nat → TyS) (ρ : Assignment),
    FieldsFaithful { K with Δ := Δ } ρ ∧ ParamsFaithful { K with Δ := Δ } ρ ∧ RecordsFaithful K

/-- Faithfulness does not read Δ. -/
theorem CtxFaithful.withΔ {K : RunCtx} (h : CtxFaithful K) (Δ : Nat → TyS) : CtxFaithful { K with Δ := Δ } :=
  fun Δ' ρ =>
    let ⟨h1, h2, h3⟩ := h Δ' ρ
    ⟨h1, h2, ⟨h3.types, h3.values, h3.smallOnly, h3.leafOk⟩⟩

/-! ## Faithfulness, one declaration at a time -/

/-- `FieldsFaithful` at one declaration. -/
def FieldsFaithfulAt (K : RunCtx) (ρ : Assignment) (d : IndDecl) : Prop :=
  ∀ (ps : List Sem) (c i : Nat) (e : List Sem) (FT : Term),
    ps.length = d.params.length → ParamsTyped K.dm d ps → FieldsTyped K.dm d ps c e → e.length = i →
    fieldTerm d c i = some FT →
    ∀ r s', run K ρ noFuture (.plain (TyM.univ 1)) FT (teleFrame K.dm K.D d ps c e) = some (r, s') →
      r.1.asTy = K.dm.fieldTy d ps c i e

/-- `ParamsFaithful` at one declaration. -/
def ParamsFaithfulAt (K : RunCtx) (ρ : Assignment) (d : IndDecl) : Prop :=
  ∀ (ps : List Sem) (j : Nat) (hn : Hint) (PT : Term),
    ParamsTyped K.dm d ps → ps.length = j → d.params[j]? = some (hn, PT) →
    ∀ r s', run K ρ noFuture (.plain (TyM.univ 2)) PT (paramFrame K.dm K.D d ps) = some (r, s') →
      r.1.asTy = K.dm.paramTy d j ps

/-- `RecordsFaithful` at one declaration. -/
structure RecordsFaithfulAt (K : RunCtx) (d : IndDecl) : Prop where
  types : ∀ (ps : List Sem) (j : Nat) (A : Type) (c : Code0 A),
    ps.length = d.params.length → d.paramIsType j = true →
    ParamsTyped K.dm d ps → ps[j]? = some (.ty (.t0 A c)) →
    K.dm.paramTyOf (K.dm.recOf d ps) j = .t0 A c
  values : ∀ (ps : List Sem) (j : Nat) (v : Sem) (A : Type) (c : Code0 A),
    ParamsTyped K.dm d ps → ps[j]? = some v → K.dm.paramTy d j (ps.take j) = .t0 A c →
    v ∈ₛ[K.dm.read] .t0 A c → K.dm.recOf d ps (paramKey j) = .small v.small
  smallOnly : ∀ (ps ps' : List Sem), ParamsTyped K.dm d ps → ps'.length = ps.length →
    (∀ (j : Nat) (v v' : Sem), ps[j]? = some v → ps'[j]? = some v' →
      v' = v ∨ ((∃ (A : Type) (c : Code0 A), K.dm.paramTy d j (ps.take j) = .t0 A c ∧ v ∈ₛ[K.dm.read] .t0 A c) ∧
        v'.small = v.small)) →
    K.dm.recOf d ps' = K.dm.recOf d ps
  leafOk : ∀ (ps : List Sem), ps.length = d.params.length → ParamsTyped K.dm d ps →
    K.dm.RecLeafOk d (K.dm.recOf d ps)

/-- **One declaration is faithful at a context**, at every Δ and assignment. -/
def DeclFaithful (K : RunCtx) (d : IndDecl) : Prop :=
  ∀ (Δ : Nat → TyS) (ρ : Assignment),
    FieldsFaithfulAt { K with Δ := Δ } ρ d ∧ ParamsFaithfulAt { K with Δ := Δ } ρ d ∧ RecordsFaithfulAt K d

/-- **A context is faithful when each of its declarations is.** -/
theorem ctxFaithful_of_decls {K : RunCtx} (h : ∀ d ∈ K.Γ, DeclFaithful K d) : CtxFaithful K := by
  intro Δ ρ
  refine ⟨fun d hd => (h d hd Δ ρ).1, fun d hd => (h d hd Δ ρ).2.1, ⟨?_, ?_, ?_, ?_⟩⟩
  · exact fun d hd => (h d hd Δ ρ).2.2.types
  · exact fun d hd => (h d hd Δ ρ).2.2.values
  · exact fun d hd => (h d hd Δ ρ).2.2.smallOnly
  · exact fun d hd => (h d hd Δ ρ).2.2.leafOk


/-- **Faithfulness at the declarations `ds` only, the runs at the context's whole list** (the one-list
ruling, docs/31 D174, docs/34 §18.13). The reference's declaration list `K.Γ` is the whole program's at
every stage; the checker's state at stage `k` holds a prefix of it, and faithfulness is asked for the
declarations OF THAT PREFIX: a later declaration's field types may call globals the stage does not
have yet, which the stage's context means as `err`. What `CtxS` and `CtxOk` carry at `st.inds`. -/
def DeclsFaithful (K : RunCtx) (ds : List IndDecl) : Prop := ∀ d ∈ ds, DeclFaithful K d

/-- Faithfulness at every declaration of the list gives faithfulness at any of its declarations. -/
theorem CtxFaithful.decls {K : RunCtx} (h : CtxFaithful K) {ds : List IndDecl} (hds : ∀ d ∈ ds, d ∈ K.Γ) :
    DeclsFaithful K ds := fun d hd Δ ρ =>
  let ⟨h1, h2, h3⟩ := h Δ ρ
  ⟨h1 d (hds d hd), h2 d (hds d hd), ⟨h3.types d (hds d hd), h3.values d (hds d hd), h3.smallOnly d (hds d hd),
    h3.leafOk d (hds d hd)⟩⟩

/-- A prefix's declarations are the list's. -/
theorem CtxFaithful.prefix {K : RunCtx} (h : CtxFaithful K) {ds : List IndDecl} (hds : ds <+: K.Γ) :
    DeclsFaithful K ds :=
  h.decls fun _ hd => hds.subset hd

/-- Faithfulness at the declarations `ds` does not read Δ. -/
theorem DeclsFaithful.withΔ {K : RunCtx} {ds : List IndDecl} (h : DeclsFaithful K ds) (Δ : Nat → TyS) :
    DeclsFaithful { K with Δ := Δ } ds :=
  fun d hd Δ' ρ =>
    let ⟨h1, h2, h3⟩ := h d hd Δ' ρ
    ⟨h1, h2, ⟨h3.types, h3.values, h3.smallOnly, h3.leafOk⟩⟩

/-- Faithfulness at a sub-list. -/
theorem DeclsFaithful.mono {K : RunCtx} {ds ds' : List IndDecl} (h : DeclsFaithful K ds) (hs : ∀ d ∈ ds', d ∈ ds) :
    DeclsFaithful K ds' := fun d hd => h d (hs d hd)

/-- The field-type clause of faithfulness at one declaration of `ds`. -/
theorem DeclsFaithful.fields {K : RunCtx} {ds : List IndDecl} (h : DeclsFaithful K ds) (ρ : Assignment)
    {d : IndDecl} (hd : d ∈ ds) : FieldsFaithfulAt K ρ d :=
  (h d hd K.Δ ρ).1


/-- **An element a prefix finds is found identically in the longer list** (any predicate; the
one-list ruling's link, docs/31 D174: a declaration the checker's state finds by name is the one the
context's whole-program list finds). `Exists.find_of_prefix` is its instance at declaration names. -/
theorem find?_of_prefix {α : Type _} {l₀ l : List α} (h : l₀ <+: l) {p : α → Bool} {a : α}
    (hd : l₀.find? p = some a) : l.find? p = some a := by
  obtain ⟨t, rfl⟩ := h
  rw [List.find?_append, hd]; rfl

end Ochr.Meaning
