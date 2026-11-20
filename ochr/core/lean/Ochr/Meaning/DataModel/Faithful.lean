import Ochr.Meaning.Run

/-!
# Faithfulness: the data model reads the declared types as the reference run does (docs/34 §9, §14)

What a data model owes the program beyond covering its declarations, and what `CtxOk` carries
(`faithful`) and the existence statement concludes (`Assembly.DataFaithful`):

1. **Field types** (`FieldsFaithful`): at well-typed parameters and earlier fields
   (`ParamsTyped`, `FieldsTyped`), the reference run of the declared field-type term, in the frame
   the checker's `fieldTele` evaluates it in (`teleFrame`: the fields, the later ones `moved`, as the
   checker binds `⊥`, then the parameters, each at its type), is defined and means `dm.fieldTy`.
   Under the model itself: a field `List(A)` runs to `dm.tyM List [A]`. Type functions in field
   types read the program's earlier globals, so the run context is the program meaning's.
2. **Parameter types** (`ParamsFaithful`): the same for the declared parameter types and `paramTy`.
3. **Records keep the parameters `unifyTyS` reads back** (`RecordsFaithful`): the record at
   parameters keeps a level-0 type parameter's entry, and a value parameter of a level-0 type read
   small, at `paramKey`, which is where the run's constructor clause reads a parameter back off a
   field's type (`unifyTyS`); and it reads a value parameter only small, so the rebuilt parameter
   gives the same record. (Guess, for the canonical model: a member of a data type is determined by
   its small reading and its type, so records computed from the run's readings of the field types,
   whose `Eq`s compare members of one type, are functions of the value parameters' small readings.)

Definedness is asked, so a run made undefined cannot make faithfulness vacuous. The degenerate
model, which met the existence statement before the port, is not faithful
(`DataModel/Degenerate.lean`).
-/

namespace Ochr.Meaning

/-- A binding holding `v` at type `T`. -/
def faithBind (T : TyM) (v : Sem) : SBinding := { ty := .plain T, val := fun _ => v }

/-- The frame `Machine.fieldTele` evaluates constructor `c`'s field types in, as meanings: the
fields (the earlier ones `e`, the rest `moved`, as the checker binds `⊥`), then the parameters,
each at its type. -/
noncomputable def teleFrame (dm : DataModel) (d : IndDecl) (ps : List Sem) (c : Nat) (e : List Sem) : SState :=
  let k := ((d.ctors[c]?).map (·.2.length)).getD 0
  let fs := e ++ List.replicate (k - e.length) Sem.moved
  stateOf 0 (fs.zipIdx.map (fun vi => faithBind (dm.fieldTy d ps c vi.2 (e.take vi.2)) vi.1) ++
    ps.zipIdx.map (fun vj => faithBind (dm.paramTy d vj.2 (ps.take vj.2)) vj.1))

/-- The frame parameter `j`'s declared type is evaluated in: the earlier parameters. -/
noncomputable def paramFrame (dm : DataModel) (d : IndDecl) (ps : List Sem) : SState :=
  stateOf 0 (ps.zipIdx.map (fun vj => faithBind (dm.paramTy d vj.2 (ps.take vj.2)) vj.1))

/-- Parameters each of their declared type at the earlier ones (a type parameter: a type). -/
def ParamsTyped (dm : DataModel) (d : IndDecl) (ps : List Sem) : Prop :=
  ∀ j (h : j < ps.length), ps[j] ∈ₛ[dm.read] dm.paramTy d j (ps.take j) ∨ ∃ T, ps[j] = .ty T

/-- Earlier fields each of their field type at the ones before. -/
def FieldsTyped (dm : DataModel) (d : IndDecl) (ps : List Sem) (c : Nat) (e : List Sem) : Prop :=
  ∀ i (h : i < e.length), e[i] ∈ₛ[dm.read] dm.fieldTy d ps c i (e.take i)

/-- **Field types are the run's readings of the declared field-type terms.** -/
def FieldsFaithful (K : RunCtx) (ρ : Assignment) : Prop :=
  ∀ d ∈ K.Γ, ∀ (ps : List Sem) (c i : Nat) (e : List Sem) (FT : Term),
    ParamsTyped K.dm d ps → FieldsTyped K.dm d ps c e → e.length = i → fieldTerm d c i = some FT →
    ∃ r s', run K ρ noFuture (.plain (TyM.univ 1)) FT (teleFrame K.dm d ps c e) = some (r, s') ∧
      r.1.asTy = K.dm.fieldTy d ps c i e

/-- **Parameter types are the run's readings of the declared parameter types.** -/
def ParamsFaithful (K : RunCtx) (ρ : Assignment) : Prop :=
  ∀ d ∈ K.Γ, ∀ (ps : List Sem) (j : Nat) (hn : Hint) (PT : Term),
    ParamsTyped K.dm d ps → ps.length = j → d.params[j]? = some (hn, PT) →
    ∃ r s', run K ρ noFuture (.plain (TyM.univ 2)) PT (paramFrame K.dm d ps) = some (r, s') ∧
      r.1.asTy = K.dm.paramTy d j ps

/-- **Records keep what `unifyTyS` reads back off a field's type** (docs/34 §14, Handoff 3b): at
`paramKey`, each level-0 type parameter's entry (`types`) and each value parameter of a level-0
type read small (`values`); and a record reads a value parameter only small (`smallOnly`: parameter
lists that differ only in value parameters with the same small readings have the same record), so
the parameter `unifyTyS` rebuilds from the small reading (`ofSmall`, `small_ofSmall`) gives the
written one's record. -/
structure RecordsFaithful (K : RunCtx) : Prop where
  types : ∀ d ∈ K.Γ, ∀ (ps : List Sem) (j : Nat) (A : Type) (c : Code0 A),
    ParamsTyped K.dm d ps → ps[j]? = some (.ty (.t0 A c)) →
    K.dm.entryTy (K.dm.recOf d ps (paramKey j)) = .t0 A c
  values : ∀ d ∈ K.Γ, ∀ (ps : List Sem) (j : Nat) (v : Sem) (A : Type) (c : Code0 A),
    ParamsTyped K.dm d ps → ps[j]? = some v → K.dm.paramTy d j (ps.take j) = .t0 A c →
    v ∈ₛ[K.dm.read] .t0 A c → K.dm.recOf d ps (paramKey j) = .small v.small
  smallOnly : ∀ d ∈ K.Γ, ∀ (ps ps' : List Sem), ParamsTyped K.dm d ps → ps'.length = ps.length →
    (∀ (j : Nat) (v v' : Sem), ps[j]? = some v → ps'[j]? = some v' →
      v' = v ∨ ((∃ (A : Type) (c : Code0 A), K.dm.paramTy d j (ps.take j) = .t0 A c ∧ v ∈ₛ[K.dm.read] .t0 A c) ∧
        v'.small = v.small)) →
    K.dm.recOf d ps' = K.dm.recOf d ps

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
    ⟨h1, h2, ⟨h3.types, h3.values, h3.smallOnly⟩⟩

end Ochr.Meaning
