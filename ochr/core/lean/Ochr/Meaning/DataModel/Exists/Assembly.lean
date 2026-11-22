import Ochr.Meaning.Consistency
import Ochr.Meaning.DataModel.Exists.Knot.Exists
import Ochr.Meaning.DataModel.Exists.Knot.TruthExists
import Ochr.Meaning.DataModel.Exists.Knot.FromChecks
import Ochr.Meaning.DataModel.Exists.Params
import Ochr.Meaning.DataModel.Exists.Knot.CongrN

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

/-! Faithfulness one declaration at a time (`FieldsFaithfulAt`, `ParamsFaithfulAt`, `RecordsFaithfulAt`,
`DeclFaithful`, `ctxFaithful_of_decls`, `DeclsFaithful`) moved to `DataModel/Faithful.lean` (docs/31 D174),
where the simulation's context reads it. -/

/-! ## Stages, and the contexts that extend one -/

section
variable (D : MState → Decisions) (fuel : Nat) (items : List Item)

/-- The program meaning of the first `k` items under the model `dm`, as `exists_dataModel` reads it:
at the whole program's declaration list (`indsOf`, the one-list ruling, docs/31 D174). -/
noncomputable abbrev stage (dm : DataModel) (k : Nat) : ProgState :=
  progMeaning dm D (indsOf {} fuel items) (fun _ => .err) {} fuel (items.take k)

/-- The model at the declarations no stage has reached yet: records `none`, parameter types `err`
(constant, so parametric, monotone and local whatever the declaration). -/
def dm0 : DataModel := { covers := fun _ => True, recOf := fun _ _ _ => .none, paramTy := fun _ _ _ => TyM.err }

/-- **A run context extends a stage** (for the model `dm`), at the ONE list (docs/31 D174, docs/34
§18.13). What an extension may change, and what it may not:
* the declaration list: NOT changed; it is the whole program's (`gamma`);
* the model: the same records and parameter types at the stage's declarations (`agree`); anything at
  the later declarations of the list and at declarations off it;
* the globals: the same meaning and type at every global the stage has a meaning for (`globals`);
  anything at the later ones (a later stage has more);
* the decisions: the checker's at any state over more declarations and more globals, within the
  whole list (`dec`): the field-type runs are asked not to depend on which (piece 8, a named fact);
* Δ: anything (`DeclFaithful` quantifies it); Λ and the definition being checked: as the program
  meaning's contexts have them (`lam`, `cur`). -/
structure Extends (dm : DataModel) (P : ProgState) (K : RunCtx) : Prop where
  gamma : K.Γ = indsOf {} fuel items
  agree : ∀ d ∈ P.inds, K.dm.recOf d = dm.recOf d ∧ K.dm.paramTy d = dm.paramTy d
  globals : ∀ n, (P.means.find? (·.1 == n)).isSome → K.C.global n = P.baseC.global n
  dec : ∃ st : MState, P.inds <+: st.inds ∧ st.inds <+: indsOf {} fuel items ∧ P.globals <+: st.globals ∧ K.D = D st
  lam : K.Λ = fun _ => .plain .err
  cur : K.cur = none

/-- **The induction's invariant at stage `k`**, at the one list (exists9). Against exists8's:
`Extends` fixes the list; `rest` says the model is still `dm0` at every declaration the stage has not
reached (so the next construction's hypotheses about the earlier records hold at the later ones too:
`knot_exists` and `truth_exists` quantify over the whole list); `pty` is gone (the knot reads only the
declaration's OWN parameter types locally, docs/34 §18.14). -/
structure Inv (k : Nat) (dm : DataModel) : Prop where
  covers : ∀ d, dm.covers d
  rest : ∀ M, M ∉ indsOf {} fuel (items.take k) → dm.recOf M = dm0.recOf M ∧ dm.paramTy M = dm0.paramTy M
  congr : ∀ k' ≤ k, ∀ dm' : DataModel,
    (∀ d ∈ indsOf {} fuel (items.take k'), dm'.recOf d = dm.recOf d ∧ dm'.paramTy d = dm.paramTy d) →
    stage D fuel items dm' k' = stage D fuel items dm k'
  faithful : ∀ k' ≤ k, ∀ d ∈ indsOf {} fuel (items.take k'), ∀ K : RunCtx,
    Extends D fuel items dm (stage D fuel items dm k') K → DeclFaithful K d
  par : ∀ M ∈ indsOf {} fuel (items.take k), ∀ n,
    RAgree (fun j => M.nestable.getD j false) n (dm.recOf M) (dm.recOf M)
  mono : ∀ M ∈ indsOf {} fuel (items.take k), M.sort = 0 → ∀ ps ps', PropLe M ps ps' → ∀ c i es,
    es.length = i → ShapeLe (uShape M (dm.recOf M ps) c i es) (uShape M (dm.recOf M ps') c i es)
  val : ∀ M ∈ indsOf {} fuel (items.take k), ∀ j, nestOf M j = true → M.paramIsType j = true

theorem stage_inds (dm : DataModel) (k : Nat) : (stage D fuel items dm k).inds = indsOf {} fuel (items.take k) :=
  progMeaning_inds _ _ _ _ _ _ _

/-- **The invariant at the last stage gives the existence statement**, at the one list (docs/31 D174),
assuming that every stage's declarations are a prefix of the whole program's (`hpre`: a fact of the
checker, `Assembly.inds_prefix` for an accepted program). -/
theorem exists_of_inv {dm : DataModel} (h : Inv D fuel items items.length dm)
    (hpre : ∀ k, k ≤ items.length → indsOf {} fuel (items.take k) <+: indsOf {} fuel items) :
    (progMeaning dm D (indsOf {} fuel items) (fun _ => .err) {} fuel items).Covered dm ∧
      ∀ k, k ≤ items.length → Ochr.Meaning.Assembly.DataFaithful dm D (indsOf {} fuel items)
        (progMeaning dm D (indsOf {} fuel items) (fun _ => .err) {} fuel (items.take k)) := by
  refine ⟨fun d _ => h.covers d, fun k hk st hst hgl d hd => ?_⟩
  have hd' : d ∈ indsOf {} fuel (items.take k) := by rw [← stage_inds D fuel items dm k]; exact hd
  have hp : (stage D fuel items dm k).inds <+: indsOf {} fuel items := by
    rw [stage_inds]; exact hpre k hk
  refine h.faithful k hk d hd' _ ⟨rfl, fun _ _ => ⟨rfl, rfl⟩, fun _ _ => rfl, ⟨st, ?_, ?_, hgl, rfl⟩, rfl, rfl⟩
  · show (stage D fuel items dm k).inds <+: st.inds
    rw [hst]; exact List.prefix_refl _
  · show st.inds <+: indsOf {} fuel items
    rw [hst]; exact hp

/-- **The invariant holds at stage 0**, for `dm0`. -/
theorem inv_zero : Inv D fuel items 0 dm0 := by
  have h0 : ∀ dm : DataModel, stage D fuel items dm 0 = {} := fun dm => by
    simp [stage, progMeaning, progMeaningFrom]
  have hi : indsOf {} fuel (items.take 0) = [] := by simp [indsOf, sigAfterFrom]
  refine ⟨fun _ => trivial, fun _ _ => ⟨rfl, rfl⟩, fun k' hk' dm' _ => ?_, fun k' hk' d hd => ?_, ?_, ?_, ?_⟩
  · have : k' = 0 := by omega
    subst this; rw [h0, h0]
  · have : k' = 0 := by omega
    subst this; rw [hi] at hd; cases hd
  all_goals (intro M hM; rw [hi] at hM; cases hM)

/-! ## The facts the step rests on, stated (exists9)

Each is named in the honest count (docs/34 §18.14). The first three are about the checker; `DecStable`
is an obligation on the decisions (piece 8). -/

/-- **One accepted item, as the checker stores it** (about the checker, enforced but not derived; an
extension of `CheckIndGivesChecks` to `checkItem`, whose `seedHoles` comes first): an accepted inductive
declaration appends one entry passing `IndChecks` and leaves the globals; an accepted definition leaves
the declarations and appends its globals. -/
def ItemFacts : Prop :=
  ∀ (it : Item) (st st' : MState) (fuel : Nat), (runMachine (checkItem it) st fuel).1 = .ok () st' →
    (∀ d, it = .ind d → ∃ d', st'.inds = st.inds ++ [d'] ∧ Knot.IndChecks st.inds d' ∧ Knot.FieldsNoVal d' ∧
      Records.VaryValFree d' ∧ st'.globals = st.globals) ∧
    (∀ d, it = .defn d → st'.inds = st.inds ∧ st.globals <+: st'.globals)

/-- **Piece 8 (an obligation on the decisions, for the machine lane)**: a declared field type and a
declared parameter type of a declaration of the state `st0` run the same, in the frames the checker
types them in, under the decisions at `st0` and at any state over more declarations and more globals. -/
def DecStable (D : MState → Decisions) : Prop :=
  ∀ (st0 st : MState), st0.inds <+: st.inds → st0.globals <+: st.globals → ∀ d ∈ st0.inds,
    (∀ (K : RunCtx) (ρ : Assignment) (ps : List Sem) (c i : Nat) (e : List Sem) (FT : Term), fieldTerm d c i = some FT →
      run { K with D := D st } ρ noFuture (.plain (TyM.univ 1)) FT (teleFrame K.dm (D st) d ps c e) =
        run { K with D := D st0 } ρ noFuture (.plain (TyM.univ 1)) FT (teleFrame K.dm (D st0) d ps c e)) ∧
    (∀ (K : RunCtx) (ρ : Assignment) (ps : List Sem) (j : Nat) (mask : Bool), j < d.params.length →
      run { K with D := D st } ρ noFuture (.plain (TyM.univ 2)) (Knot.paramTerm d j) (Params.frameP d (K.dm.paramTy d) (D st) mask ps) =
        run { K with D := D st0 } ρ noFuture (.plain (TyM.univ 2)) (Knot.paramTerm d j) (Params.frameP d (K.dm.paramTy d) (D st0) mask ps))

/-- **The names a stage's code mentions are the stage's** (about the checker: resolution and D118):
every field type and parameter type of a stored declaration, every accepted definition's body, domains,
codomain and stored type name only types the state declares and globals the stage has a meaning for,
and hold no embedded value (field and parameter types; a definition's code may hold values, whose names
are tested the same way, `Knot.Value.nok`). Stated per stage through `Knot.NameOk`. -/
def NamesOk (Γ : List IndDecl) (P : ProgState) : Knot.NameOk where
  ty n := P.inds.any (·.name == n) && (Γ.find? (·.name == n)).isSome
  rc n := P.inds.any (·.name == n)
  gl n := (P.means.find? (·.1 == n)).isSome

/-- **The step** (OPEN; exists9's plan, docs/34 §18.14). From the invariant at stage `k` for a model, the
invariant at stage `k + 1` for a model agreeing with it at stage `k`'s declarations. By the `k`-th item's
verdict (`ItemFacts`):
* not accepted: the stage is unchanged, the same model;
* an accepted definition: the same model; `congr` at `k + 1` is `Knot.runT_congrN`/`meanV_congrN` for the
  definition's body and stored type at models agreeing at the stage's declarations (`NamesOk`);
  `faithful` at `k + 1` from `k`: an extension of stage `k + 1` extends stage `k` (more means, more
  globals, the same declarations);
* an accepted inductive declaration `d` (`ItemFacts`: one new entry passing `IndChecks`): the build
  context `K0` (the whole list, the model at stage `k`, the stage's globals, the decisions at the stage's
  state `st0`, `ρ = err`); parameter types `Params.pty K0 ρ d` (piece 7: `pty_local`, `pty_faithful`);
  records `Records.recCanon` from `knot_exists` (or `truth_exists`, OPEN: the `Prop`-sorted analogue of
  `Records.lean`) at `K0` with `d`'s parameter types set, grammar from `grammar_of_checks`; the new
  model sets both. `faithful` at `d`: from any extension `K`, `runT_congrA` (Δ, ρ: no embedded values),
  `DecStable` (the decisions), `runT_congrN` (the model and globals; at `d` itself records agree only on
  typed lists, which is all `.tind d` reads), the knot's conclusion and `fieldTy_knot`; parameter types
  the same with `pty_faithful`; records `Records.recordsFaithful_canon` (`leafOk` OPEN). `par` is
  `Records.par_canon`; `val` is `grammar_of_checks`' third conclusion; `rest` and the earlier stages
  by `congr`. -/
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

/-- `exists_dataModel`, from the step (and the prefix fact `hpre`). -/
theorem exists_dataModel' (hpre : ∀ k, k ≤ items.length → indsOf {} fuel (items.take k) <+: indsOf {} fuel items) :
    ∃ dm : DataModel,
      (progMeaning dm D (indsOf {} fuel items) (fun _ => .err) {} fuel items).Covered dm ∧
      ∀ k, k ≤ items.length → Ochr.Meaning.Assembly.DataFaithful dm D (indsOf {} fuel items)
        (progMeaning dm D (indsOf {} fuel items) (fun _ => .err) {} fuel (items.take k)) := by
  obtain ⟨dm, h⟩ := inv_all D fuel items items.length (Nat.le_refl _)
  exact ⟨dm, exists_of_inv D fuel items h hpre⟩

end

/-! ## The statement at ONE declaration list (the lead's ruling, 2026-11-22)

Built (docs/31 D174): `Assembly.DataFaithful` (`Consistency.lean`) IS the one-list statement that stood
here as `DataFaithfulOne` (at the whole program's list `Γ`, faithfulness for the stage's declarations
only, `DeclsFaithful`), and `Assembly.exists_dataModel` is stated at `indsOf {} fuel items`, the list
`ExistsDataModelOne` named; both definitions are deleted. -/

end Ochr.Meaning.DataModel.Exists.Assembly
