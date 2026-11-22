import Ochr.Meaning.Consistency
import Ochr.Meaning.DataModel.Exists.Knot.Exists
import Ochr.Meaning.DataModel.Exists.Knot.TruthExists
import Ochr.Meaning.DataModel.Exists.Knot.FromChecks

/-!
# The assembly: the induction's invariant (exists8; OUTSIDE the default build, it has `sorry`)

`Assembly.exists_dataModel` by induction over the items, one model per stage. Stage `k` is the
program meaning of the first `k` items under the stage's model (`stage`). The invariant `Inv` at
stage `k` says, of the stage's model:
* it covers every declaration (`covers := True`);
* `congr`: every earlier stage's program meaning reads the model only at that stage's declarations
  (a model agreeing there gives the same `ProgState`): what lets the final model, which adds later
  declarations, keep every earlier stage's meaning;
* `faithful`: every declaration of every stage up to `k` is faithful (`DeclFaithful`) at EVERY run
  context that extends that stage (`Extends`: the same records and parameter types at its
  declarations, a declaration list with them as a prefix, the same globals' meanings, and the
  checker's decisions at a state over that list extending its globals);
* what the next declaration's construction assumes of the earlier ones: `par` (`knot_exists`'s
  `hpar`), `mono` (`truth_exists`'s `hmono`), `pty` (`ParamTyLocal`), `val` (`grammar_of_checks`'s
  `hval`).

`exists_of_inv` (PROVED here, no assumed fact) is the check that the invariant at the last stage
gives `exists_dataModel`'s conclusion; `inv_zero` (PROVED) starts it; `inv_step` (`sorry`) is the
work, and its docstring lists what it rests on.
-/

namespace Ochr.Meaning.DataModel.Exists.Assembly

open Ochr Ochr.Meaning Ochr.Meaning.DataLib Ochr.Meaning.Canonical Ochr.Meaning.DataModel.Exists.Knot

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

/-! ## Stages, and the contexts that extend one -/

section
variable (D : MState → Decisions) (fuel : Nat) (items : List Item)

/-- The program meaning of the first `k` items under the model `dm`, as `exists_dataModel` reads it. -/
noncomputable abbrev stage (dm : DataModel) (k : Nat) : ProgState :=
  progMeaning dm D (fun _ => .err) {} fuel (items.take k)

/-- **A run context extends a stage** (for the model `dm`): the same records and parameter types at
the stage's declarations, a declaration list with them as a prefix, the stage's globals meaning the
same, and the checker's decisions at a state over that list extending the stage's globals. -/
structure Extends (dm : DataModel) (P : ProgState) (K : RunCtx) : Prop where
  agree : ∀ d ∈ P.inds, K.dm.recOf d = dm.recOf d ∧ K.dm.paramTy d = dm.paramTy d
  gamma : P.inds <+: K.Γ
  globals : ∀ n, (P.means.find? (·.1 == n)).isSome → K.C.global n = P.baseC.global n
  dec : ∃ st : MState, st.inds = K.Γ ∧ P.globals <+: st.globals ∧ K.D = D st

/-- **The induction's invariant at stage `k`** (see the module docstring). -/
structure Inv (k : Nat) (dm : DataModel) : Prop where
  covers : ∀ d, dm.covers d
  congr : ∀ k' ≤ k, ∀ dm' : DataModel,
    (∀ d ∈ (stage D fuel items dm k').inds, dm'.recOf d = dm.recOf d ∧ dm'.paramTy d = dm.paramTy d) →
    stage D fuel items dm' k' = stage D fuel items dm k'
  faithful : ∀ k' ≤ k, ∀ d ∈ (stage D fuel items dm k').inds, ∀ K : RunCtx,
    Extends D dm (stage D fuel items dm k') K → DeclFaithful K d
  par : ∀ M ∈ (stage D fuel items dm k).inds, ∀ n,
    RAgree (fun j => M.nestable.getD j false) n (dm.recOf M) (dm.recOf M)
  mono : ∀ M ∈ (stage D fuel items dm k).inds, M.sort = 0 → ∀ ps ps', PropLe M ps ps' → ∀ c i es,
    es.length = i → ShapeLe (uShape M (dm.recOf M ps) c i es) (uShape M (dm.recOf M ps') c i es)
  pty : ParamTyLocal dm (stage D fuel items dm k).inds
  val : ∀ M ∈ (stage D fuel items dm k).inds, ∀ j, nestOf M j = true → M.paramIsType j = true

/-- **The invariant at the last stage gives the existence statement** (no assumed fact). -/
theorem exists_of_inv {dm : DataModel} (h : Inv D fuel items items.length dm) :
    (progMeaning dm D (fun _ => .err) {} fuel items).Covered dm ∧
      ∀ k, k ≤ items.length → Ochr.Meaning.Assembly.DataFaithful dm D (progMeaning dm D (fun _ => .err) {} fuel (items.take k)) := by
  refine ⟨fun d _ => h.covers d, fun k hk st hst hgl => ctxFaithful_of_decls fun d hd => ?_⟩
  have hd' : d ∈ (stage D fuel items dm k).inds := by
    show d ∈ (progMeaning dm D (fun _ => .err) {} fuel (items.take k)).inds
    simp only [ProgState.ctx] at hd; rw [← hst]; exact hd
  refine h.faithful k hk d hd' _ ⟨fun _ _ => ⟨rfl, rfl⟩, ?_, fun _ _ => rfl, ⟨st, rfl, hgl, rfl⟩⟩
  show (stage D fuel items dm k).inds <+: st.inds
  rw [hst]; exact List.prefix_refl _

/-- **The invariant holds at stage 0**, for the model that covers everything and keeps nothing. -/
theorem inv_zero : Inv D fuel items 0 { covers := fun _ => True, recOf := fun _ _ _ => .none, paramTy := fun _ _ _ => TyM.err } := by
  have h0 : ∀ dm : DataModel, stage D fuel items dm 0 = {} := fun dm => by
    simp [stage, progMeaning, progMeaningFrom]
  refine ⟨fun _ => trivial, fun k' hk' dm' _ => ?_, fun k' hk' d hd => ?_, ?_, ?_, ?_, ?_⟩
  · have : k' = 0 := by omega
    subst this; rw [h0, h0]
  · have : k' = 0 := by omega
    subst this; rw [h0] at hd; cases hd
  all_goals (intro M hM; rw [h0] at hM; cases hM)

/-- **The step** (OPEN). From the invariant at stage `k` for a model, the invariant at stage `k + 1`
for a model that agrees with it at stage `k`'s declarations. By the `k`-th item's verdict:
* not accepted: the stage is unchanged (`ProgState.step`), the same model;
* an accepted definition: the same model; the declarations are unchanged (a named machine fact:
  `checkDef` leaves `inds` alone); `congr` at `k + 1` needs the run's congruence in the model at the
  stage's declarations (piece 1, `Decomposition.runT_congrDM`, for definition bodies and the stored
  type's `Value.tyS`);
* an accepted inductive declaration `d` (`CheckIndGivesChecks`: one new entry, passing `IndChecks`):
  its parameter types by the run (piece 7), then its records by `knot_exists` (data-sorted) or
  `truth_exists` (`Prop`-sorted) at a context of the new stage, with the grammar from
  `grammar_of_checks`; the new model is the old one with `d`'s records and parameter types set.
  `faithful` at `d` then needs the transfer from that context to EVERY context extending the new
  stage: the assignment and Δ by `runT_congrA` (`FieldsNoVal`); the model at later declarations by
  the model congruence (`Congr.runT_congrR`, extended to parameter types); the globals by a
  congruence at the constants a field type names; the decisions by a named machine fact (piece 8:
  the field-type runs do not change with the state's later globals and declarations); and the
  declaration list, which the run reads not only at the names a term mentions but at the name a
  strong-updated tree carries (`DataModel.readTy`'s `ownTy`, through `Sem.follow` only: `Sem.updAt`
  does not read the list; `ScopeCE.run_differs`): the open point of the assembly (docs/34 §18.13). -/
theorem inv_step (k : Nat) (hk : k < items.length) (dm : DataModel) (h : Inv D fuel items k dm) :
    ∃ dm' : DataModel, Inv D fuel items (k + 1) dm' ∧
      ∀ d ∈ (stage D fuel items dm k).inds, dm'.recOf d = dm.recOf d ∧ dm'.paramTy d = dm.paramTy d := by
  sorry

theorem inv_all : ∀ k, k ≤ items.length → ∃ dm, Inv D fuel items k dm
  | 0, _ => ⟨_, inv_zero D fuel items⟩
  | k + 1, hk => by
    obtain ⟨dm, h⟩ := inv_all k (by omega)
    obtain ⟨dm', h', -⟩ := inv_step D fuel items k (by omega) dm h
    exact ⟨dm', h'⟩

/-- `exists_dataModel`, from the step. -/
theorem exists_dataModel' :
    ∃ dm : DataModel,
      (progMeaning dm D (fun _ => .err) {} fuel items).Covered dm ∧
      ∀ k, k ≤ items.length → Ochr.Meaning.Assembly.DataFaithful dm D (progMeaning dm D (fun _ => .err) {} fuel (items.take k)) := by
  obtain ⟨dm, h⟩ := inv_all D fuel items items.length (Nat.le_refl _)
  exact ⟨dm, exists_of_inv D fuel items h⟩

end

end Ochr.Meaning.DataModel.Exists.Assembly
