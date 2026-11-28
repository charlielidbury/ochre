import Ochr.Meaning.Program
import Ochr.Meaning.DataModel.Exists.Knot.Exists
import Ochr.Meaning.DataModel.Exists.Knot.TruthExists
import Ochr.Meaning.DataModel.Exists.Knot.FromChecks
import Ochr.Meaning.DataModel.Exists.Params
import Ochr.Meaning.DataModel.Exists.Knot.CongrN
import Ochr.Meaning.DataModel.Exists.DeclStep
import Ochr.Meaning.Steps.Machine.CheckItem
import Ochr.Meaning.Steps.Machine.CheckIndSpec
import Ochr.Meaning.DataModel.Exists.FieldLevel
import Ochr.Meaning.DataModel.Exists.GlobalCalls

/-!
# The assembly: the induction's invariant, and the existence of the data model (exists8–exists10)

`Assembly.exists_dataModel` by induction over the items, one model per stage, at the whole program's
declaration list (the one-list ruling, docs/31 D174). Stage `k` is the program meaning of the first `k`
items under the stage's model (`stage`). The invariant `Inv` at stage `k` says, of the stage's model:
* `rest`: it is the constant `dm0` at every declaration the stage has not reached;
* `congr`: every earlier stage's program meaning reads the model only at that stage's declarations;
* `faithful`: every declaration of every stage up to `k` is faithful (`DeclFaithful`) at EVERY run
  context that extends that stage (`Extends`);
* what the next declaration's construction assumes of the earlier ones: `par` (data-sorted ones'
  records parametric, `Knot.ParHyp`), `mono` (`Prop`-sorted ones' records monotone), `val`.

PROVED, standard axioms, in the default build: `inv_zero`, `inv_step` (a rejected item, `inv_reject`;
an accepted definition, `inv_defn`; an accepted inductive declaration of either sort, `inv_ind_core`
with `inv_ind_faithful`), `exists_of_inv`, `globalCallLevels` (exists12, `GlobalCalls.lean`), and
`exists_dataModel_facts`, which assumes the facts in `DataFacts` (docs/34 §18.16 and §18.17 give each
one's exact statement and status):
* about the checker: `NamesFact` (read true for resolved items) and `VaryValFact` (read true since
  main's D128; not derived: its `.any` case at an inductive's type parameter is decided by a run,
  `FactsCE.dVS`); `ItemFacts` is PROVED (`itemFacts`, exists12: `CheckIndGivesChecks` assembled,
  `Steps/Machine/CheckIndSpec.lean`); `FieldHeads` is PROVED (`fieldHeads`, exists13, from main's D140:
  `Steps.Machine.runs_checkInd_heads`);
* about resolution: `NoValFact` (no embedded value in an inductive item's types), PROVED for the items a
  program resolves to (exists12, `Steps.Machine.noVal_runResolve`); a separate hypothesis of
  `exists_dataModel_facts`, discharged by `Consistency.exists_dataModel` from the resolution;
* obligations on the checker's decisions: `DecCaps`, `DecLocal`'s `caps` part, at every state (read
  true, not derived; the other three parts are PROVED at the chain's decisions, `DecLocal3`: `inv` and
  `rep` by exists12, `Steps/Machine/RepLocal.lean`, `join` by machine11, `JoinLocal.lean`, and taken by
  `exists_dataModel_facts` as its own hypothesis) and `DecStable` (at the states the checker reaches).
The one fact about the model, `GlobalCallLevels` (a global whose stored codomain is `Prop` or `Type`
calls to level-0 type values, which with `FieldHeads` gives the field types' level,
`FieldLevel.fieldLevel0_of`), is PROVED and no longer assumed. The stage prefix fact is proved
(machine10's `Steps.Machine.indsOf_take_prefix`). The old forms' counterexamples are in `FactsCE.lean`.
-/

namespace Ochr.Meaning.DataModel.Exists.Assembly

open Ochr Ochr.Meaning Ochr.Meaning.DataLib Ochr.Meaning.Canonical Ochr.Meaning.DataModel.Exists.Knot

/-! Faithfulness one declaration at a time (`FieldsFaithfulAt`, `ParamsFaithfulAt`, `RecordsFaithfulAt`,
`DeclFaithful`, `ctxFaithful_of_decls`, `DeclsFaithful`) moved to `DataModel/Faithful.lean` (docs/31 D174),
where the simulation's context reads it. -/

/-! ## Name lookups in a prefix, and the congruences the step uses (exists10) -/

/-- The name tests for code checked at stage `P`: applied types and constructors of the stage's
declarations, globals the stage has a meaning for. -/
def stageNames (Γ : List IndDecl) (P : ProgState) : Knot.NameOk where
  ty n := P.inds.any (·.name == n) && (Γ.find? (·.name == n)).isSome
  rc n := P.inds.any (·.name == n)
  gl n := (P.means.find? (·.1 == n)).isSome

/-- The name tests for the field types of `d`, added at stage `P`: applied types may also be `d`. -/
def fieldNames (Γ : List IndDecl) (P : ProgState) (d : IndDecl) : Knot.NameOk where
  ty n := (P.inds ++ [d]).any (·.name == n) && (Γ.find? (·.name == n)).isSome
  rc n := P.inds.any (·.name == n)
  gl n := (P.means.find? (·.1 == n)).isSome

theorem find_in_prefix {Γ0 Γ : List IndDecl} (hp : Γ0 <+: Γ) {n : String} {M : IndDecl}
    (ha : Γ0.any (·.name == n) = true) (hM : Γ.find? (·.name == n) = some M) : M ∈ Γ0 := by
  obtain ⟨M', hM'⟩ : ∃ M', Γ0.find? (·.name == n) = some M' := by
    cases h : Γ0.find? (·.name == n) with
    | none =>
      rw [List.find?_eq_none] at h
      obtain ⟨x, hx, hxn⟩ := List.any_eq_true.1 ha
      exact absurd hxn (h x hx)
    | some M' => exact ⟨M', rfl⟩
  rw [find_of_prefix hp hM'] at hM
  cases hM
  exact List.mem_of_find?_eq_some hM'

/-- The models agree at the stage's declarations and the globals at the stage's: `AgreeN` for the
stage's name tests. -/
theorem agreeN_stage {K : RunCtx} {dm' : DataModel} {P : ProgState} (Γ : List IndDecl) (hKΓ : K.Γ = Γ)
    (hp : P.inds <+: Γ)
    (hag : ∀ M ∈ P.inds, dm'.recOf M = K.dm.recOf M ∧ dm'.paramTy M = K.dm.paramTy M)
    {C' : CodeMeaning} (hgl : ∀ n, (P.means.find? (·.1 == n)).isSome = true → C'.global n = K.C.global n) :
    Knot.AgreeN K dm' C' (stageNames Γ P) where
  ty n M h hM := by
    rw [hKΓ] at hM
    have hM' := find_in_prefix hp (by simp only [stageNames, Bool.and_eq_true] at h; exact h.1) hM
    exact ⟨(hag M hM').2, fun ps _ => by rw [(hag M hM').1]⟩
  rc n M h hM := by
    rw [hKΓ] at hM
    have hM' := find_in_prefix hp h hM
    exact ⟨(hag M hM').1, (hag M hM').2⟩
  gl n h := hgl n h

/-- The same for a new declaration's field types (`fieldNames`): at `d` itself, the parameter types
agree and the records agree at well-typed parameters. -/
theorem agreeN_field {K : RunCtx} {dm' : DataModel} {P : ProgState} {d : IndDecl} (Γ : List IndDecl) (hKΓ : K.Γ = Γ)
    (hp : P.inds ++ [d] <+: Γ)
    (hag : ∀ M ∈ P.inds, dm'.recOf M = K.dm.recOf M ∧ dm'.paramTy M = K.dm.paramTy M)
    (hpd : dm'.paramTy d = K.dm.paramTy d) (hrd : ∀ ps, paramsOk K.dm d ps → dm'.recOf d ps = K.dm.recOf d ps)
    {C' : CodeMeaning} (hgl : ∀ n, (P.means.find? (·.1 == n)).isSome = true → C'.global n = K.C.global n) :
    Knot.AgreeN K dm' C' (fieldNames Γ P d) where
  ty n M h hM := by
    rw [hKΓ] at hM
    have hM' := find_in_prefix hp (by simp only [fieldNames, Bool.and_eq_true] at h; exact h.1) hM
    rcases List.mem_append.1 hM' with hM' | hM'
    · exact ⟨(hag M hM').2, fun ps _ => by rw [(hag M hM').1]⟩
    · rw [List.mem_singleton] at hM'
      subst hM'
      exact ⟨hpd, hrd⟩
  rc n M h hM := by
    rw [hKΓ] at hM
    have hM' := find_in_prefix ((List.prefix_append _ _).trans hp) h hM
    exact ⟨(hag M hM').1, (hag M hM').2⟩
  gl n h := hgl n h

/-- **A definition's meaning reads the model only at the names its code mentions.** -/
theorem defMeaning_congrN (K : RunCtx) (dm' : DataModel) (N : Knot.NameOk) (hA : Knot.AgreeN K dm' K.C N)
    (ρ : Assignment) (d : Def) (T : Value) (h1 : Knot.Term.nok N d.body = true)
    (h2 : Knot.Term.nok N (.fix ⟨d.name⟩ d.hs d.doms d.cod d.dec d.body) = true) (h3 : Knot.Value.nok N T = true) :
    defMeaning ρ { K with dm := dm' } d T = defMeaning ρ K d T := by
  have hT : globalTyS ρ { K with dm := dm' } T = globalTyS ρ K T := by
    unfold globalTyS Value.tyS
    rw [meanV_eq_mean, meanV_eq_mean]
    exact congrArg (fun v => TyS.plain v.asTy) (Knot.meanV_congrN K dm' K.C N ρ _ hA T _ h3).symm
  unfold defMeaning
  rw [hT]
  dsimp only
  rw [Knot.run_congrN K dm' K.C N ρ noFuture hA _ _ _ h1, Knot.run_congrN K dm' K.C N ρ noFuture hA _ _ _ h2]

/-- `Assembly.DataFaithful` (`Consistency.lean`), unfolded: this file sits below `Consistency.lean`,
which proves `exists_dataModel` from `exists_dataModel'` (docs/31 D174's one-list statement). -/
def DataFaithfulU (dm : DataModel) (D : MState → Decisions) (Γ : List IndDecl) (P : ProgState) : Prop :=
  ∀ st : MState, st.inds = P.inds → P.globals <+: st.globals → DeclsFaithful (P.ctx dm D Γ st) P.inds

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
  par : ∀ M ∈ indsOf {} fuel (items.take k), M.sort ≠ 0 → ∀ n,
    RAgree (fun j => M.nestable.getD j false) n (dm.recOf M) (dm.recOf M)
  mono : ∀ M ∈ indsOf {} fuel (items.take k), M.sort = 0 → ∀ ps ps', PropLe M ps ps' → ∀ c i es,
    es.length = i → ShapeLe (uShape M (dm.recOf M ps) c i es) (uShape M (dm.recOf M ps') c i es)
  val : ∀ M ∈ indsOf {} fuel (items.take k), ∀ j, nestOf M j = true → M.paramIsType j = true

theorem stage_inds (dm : DataModel) (k : Nat) : (stage D fuel items dm k).inds = indsOf {} fuel (items.take k) :=
  progMeaning_inds _ _ _ _ _ _ _

/-- The checker's Σ after the first `k` items (`sigAfterFrom`): the stage's, whatever the model. -/
def sig (k : Nat) : List GDef × List IndDecl := sigAfterFrom {} fuel ([], []) (items.take k)

/-- The checker's state the `k`-th item is checked from. -/
def stSt (k : Nat) : MState := { globals := (sig fuel items k).1, inds := (sig fuel items k).2, cfg := {} }

theorem stage_sig (dm : DataModel) (k : Nat) :
    (stage D fuel items dm k).globals = (sig fuel items k).1 ∧ (stage D fuel items dm k).inds = (sig fuel items k).2 := by
  have h := progMeaningFrom_sigAfter dm D (indsOf {} fuel items) (fun _ => .err) {} fuel {} (items.take k)
  simp only at h
  exact ⟨congrArg Prod.fst h, congrArg Prod.snd h⟩

/-- The `k`-th item's verdict. -/
def verdict (k : Nat) (hk : k < items.length) : Outcome Unit := (runMachine (checkItem items[k]) (stSt fuel items k) fuel).1

theorem stage_succ (dm : DataModel) (k : Nat) (hk : k < items.length) :
    stage D fuel items dm (k + 1) =
      ProgState.step dm D (indsOf {} fuel items) (fun _ => .err) {} fuel (stage D fuel items dm k) items[k] := by
  unfold stage progMeaning progMeaningFrom
  rw [List.take_add_one, List.getElem?_eq_getElem hk, List.foldl_append]
  rfl

theorem stage_succ_eq (dm : DataModel) (k : Nat) (hk : k < items.length) :
    stage D fuel items dm (k + 1) = match verdict fuel items k hk with
      | .ok () st' => { globals := st'.globals, inds := st'.inds, means := match items[k] with
          | .defn d => (stage D fuel items dm k).means ++ [(d.name,
              (defMeaning (fun _ => .err)
                ((stage D fuel items dm k).ctx dm D (indsOf {} fuel items) st') d
                (((st'.globals.find? (·.name == d.name)).map (·.ty)).getD .bot)).getD (.err, .plain .err))]
          | .ind _ => (stage D fuel items dm k).means }
      | _ => stage D fuel items dm k := by
  rw [stage_succ D fuel items dm k hk]
  unfold ProgState.step verdict stSt
  obtain ⟨hg, hi⟩ := stage_sig D fuel items dm k
  rw [hg, hi]
  rfl

theorem verdict_eq (dm : DataModel) (k : Nat) (hk : k < items.length) :
    verdict fuel items k hk = (runMachine (checkItem items[k])
      { globals := (stage D fuel items dm k).globals, inds := (stage D fuel items dm k).inds, cfg := {} } fuel).1 := by
  obtain ⟨hg, hi⟩ := stage_sig D fuel items dm k
  rw [hg, hi]; rfl

theorem defMeaning_label (ρ : Assignment) (K : RunCtx) (d : Def) (T : Value) :
    ((defMeaning ρ K d T).getD (.err, .plain .err)).2.label = none := by
  unfold defMeaning
  dsimp only
  split
  · cases run K ρ noFuture _ d.body (emptyState 0) <;> rfl
  · cases run K ρ noFuture (.plain .err) _ (emptyState 0) <;> rfl

/-- Every meaning the stage keeps has a type with no label. -/
theorem stage_means_label (dm : DataModel) : ∀ k, k ≤ items.length → ∀ e ∈ (stage D fuel items dm k).means,
    e.2.2.label = none
  | 0, _, e, he => by simp [stage, progMeaning, progMeaningFrom] at he
  | k + 1, hk, e, he => by
    have ih := stage_means_label dm k (by omega)
    rw [stage_succ_eq D fuel items dm k (by omega)] at he
    split at he
    · split at he
      · rcases List.mem_append.1 he with he | he
        · exact ih e he
        · simp only [List.mem_singleton] at he
          subst he
          exact defMeaning_label _ _ _ _
      · exact ih e he
    · exact ih e he

/-- Every global's type the stage knows carries no label. -/
theorem stage_label (dm : DataModel) (k : Nat) (hk : k ≤ items.length) (g : String) :
    ((stage D fuel items dm k).baseC.global g).2.label = none := by
  show (ProgState.globalTy _ g).label = none
  unfold ProgState.globalTy
  split
  · rename_i n v T hf
    exact stage_means_label D fuel items dm k hk _ (List.mem_of_find?_eq_some hf)
  · rfl

/-- **The invariant at the last stage gives the existence statement**, at the one list (docs/31 D174),
assuming that every stage's declarations are a prefix of the whole program's (`hpre`: a fact of the
checker, `Assembly.inds_prefix` for an accepted program). -/
theorem exists_of_inv {dm : DataModel} (h : Inv D fuel items items.length dm)
    (hpre : ∀ k, k ≤ items.length → indsOf {} fuel (items.take k) <+: indsOf {} fuel items) :
    (progMeaning dm D (indsOf {} fuel items) (fun _ => .err) {} fuel items).Covered dm ∧
      ∀ k, k ≤ items.length → DataFaithfulU dm D (indsOf {} fuel items)
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

/-- A declared parameter type holds no embedded value (resolution, as `Knot.FieldsNoVal`). -/
def ParamsNoVal (d : IndDecl) : Prop := ∀ j, (Knot.paramTerm d j).anyAtom (fun _ => true) = false

/-- **One accepted item, as the checker stores it** (about the checker; PROVED, `itemFacts`, exists12:
machine10's `Steps.Machine.checkItem_tables` and the bridge `Steps.Machine.runs_checkInd_checks`;
the stored entry is `{ d with nestable := nestableSet … }`; `IndChecks` is `Knot.CheckIndGivesChecks`
through `checkItem`, whose `seedHoles` comes first and writes neither table): an accepted inductive
declaration `d` appends one entry `d'` passing `IndChecks`, with `d`'s parameters and constructors,
and leaves the globals; an accepted definition leaves the declarations and extends the globals.

Restated by exists11 (docs/34 §18.16). Before, it also concluded `FieldsNoVal d'`, `ParamsNoVal d'`
(no embedded value in a field or parameter type) and `Records.VaryValFree d'`, at EVERY item and
state, and so was false two ways (`FactsCE.lean`): the checker accepts a core declaration holding an
embedded value (`EV`, `EP`), which resolution never produces, so the first two are now `NoValFact`, a
fact about the program's items; and it accepts a surface declaration breaking the third (`TL`), which
is now `VaryValFact`, false until main's D128. -/
def ItemFacts : Prop :=
  ∀ (it : Item) (st st' : MState) (fuel : Nat), (runMachine (checkItem it) st fuel).1 = .ok () st' →
    (∀ d, it = .ind d → ∃ d', st'.inds = st.inds ++ [d'] ∧ Knot.IndChecks st.inds d' ∧
      d'.params = d.params ∧ d'.ctors = d.ctors ∧ st'.globals = st.globals) ∧
    (∀ d, it = .defn d → st'.inds = st.inds ∧ st.globals <+: st'.globals)

/-- **`ItemFacts` holds** (PROVED, no hypothesis; exists12): machine10's `checkItem_tables` for the
tables, and `Steps.Machine.runs_checkInd_checks` (the bridge `CheckIndGivesChecks`, assembled from
machine10's pieces) for `IndChecks`; `seedHoles`, which `checkItem` runs first, writes neither table. -/
theorem itemFacts : ItemFacts := by
  intro it st st' fuel h
  have hr := Steps.Machine.runs_of_runMachine_fst h
  obtain ⟨hI, hD⟩ := Steps.Machine.checkItem_tables it st st' fuel h
  refine ⟨fun d hd => ?_, fun d hd => ?_⟩
  rotate_left
  · obtain ⟨h1, g, h2⟩ := hD d hd
    exact ⟨h1, by rw [h2]; exact List.prefix_append _ _⟩
  obtain ⟨h1, h2⟩ := hI d hd
  subst hd
  unfold checkItem at hr
  obtain ⟨_, s₁, b₁, hs, hc⟩ := Steps.Runs.bind_inv hr
  obtain ⟨-, hi⟩ := Steps.Machine.runs_seedHoles_tables hs
  have := Steps.Machine.runs_checkInd_checks hc
  rw [hi] at this
  exact ⟨_, h1, this, rfl, rfl, h2⟩

/-- **Resolution builds no embedded value** (a fact about the program's items as resolution produces
them, NOT about the checker, which accepts core declarations holding one: `FactsCE.EV`, `FactsCE.EP`):
no parameter type and no field type of an inductive item holds an embedded value (`Term.val`). Stated
of the items `exists_dataModel` is given. PROVED for the items a program resolves to (exists12,
`Steps.Machine.noVal_runResolve`, with machine12's `RRet` tool: no clause of `resolveF`, `bindersF` or
`resolveDecl` builds a `Term.val`; `Consistency.noValFact_of_resolvesTo`). -/
def NoValFact : Prop :=
  ∀ d, Item.ind d ∈ items → Knot.FieldsNoVal d ∧ ParamsNoVal d

/-- **No field type of an accepted declaration reads a varying value parameter** (about the checker,
not derived; FALSE TODAY, true after main's D128). Of the entry `d'` the checker stores for the
program's `k`-th item, `Records.VaryValFree d'`. Counterexample today (`FactsCE.tl_accepted`,
`FactsCE.tl_not_varyValFree`): the surface declaration `inductive TL (A : Type) (B : (let z = A; Type))
:= MkTL(x : B)` is accepted, with `B` varying (its type reads `A`) and not a type parameter
(`paramIsType` sees a `let`, not a written sort), while D55 lets the field `x : B` stand because
`typeDecl` reads `B`'s declared type through the `let` as `Type`. D128 (a parameter whose declared
reading is a sort must be written as a sort) rejects `TL`; machine10 found no other route
(any other read of a varying value parameter makes the parameter it reads non-nestable). Its consumer
(`Records.recordsFaithful_canon`, `_canonP`) needs less: at `TL`'s `B` the parameter type is the
universe, where the two parameter lists agree anyway. -/
def VaryValFact : Prop :=
  ∀ (k : Nat) (hk : k < items.length) (st' : MState) (d0 d' : IndDecl),
    verdict fuel items k hk = .ok () st' → items[k] = .ind d0 → st'.inds = indsOf {} fuel (items.take k) ++ [d'] →
    Records.VaryValFree d'

/-- **Piece 8 (an obligation on the decisions, for the machine lane; not derived)**: a field type and a
parameter type of the declaration `d'` the checker accepts at the program's `k`-th item run the same,
in the frames the checker types them in, under the decisions at the state `st'` that accepted it and
at any state `st` over more declarations (within the program's) and more globals.

Restated by exists11 (docs/34 §18.16). The old form asked it of ANY state `st0` and any declaration of
it, and was false (`FactsCE.lean`, the pair `E`/`F`): a declaration of an arbitrary state can call a
global only the later state has, and the call's flags differ. The lead's first ruling added the
hypotheses that `d`'s field and parameter types name only `st0`'s declarations, globals and `d`, and
hold no embedded value. That is still false at a state the checker never reaches, one step removed:
the decisions at a call `F(Z)` read `F`'s stored type, and a global of an arbitrary `st0` may have a
stored type that calls a global only `st` has (argued, not kernel-checked). So it is asked only at the
states the checker reaches on the program, where every stored type and field type names only earlier
names (D118's `undeclaredCheck` at each item, and `NamesFact`), and `d'`'s own types name only the
stage's (`NamesFact`) and hold no embedded value (`NoValFact`). Every lookup by name then finds the
same entry in `st'` and `st`. Not constrained, and read by no decision on these runs as far as
machine10 read (`absDecl` only at an embedded abstract value; `env` replaced by `scopeState`;
counters and `cfg` never): the other fields of `st`. -/
def DecStable : Prop :=
  ∀ (k : Nat) (hk : k < items.length) (st' : MState) (d0 d' : IndDecl),
    verdict fuel items k hk = .ok () st' → items[k] = .ind d0 → st'.inds = indsOf {} fuel (items.take k) ++ [d'] →
    ∀ st : MState, st'.inds <+: st.inds → st.inds <+: indsOf {} fuel items → st'.globals <+: st.globals →
    (∀ (K : RunCtx) (ρ : Assignment) (ps : List Sem) (c i : Nat) (e : List Sem) (FT : Term), fieldTerm d' c i = some FT →
      run { K with D := D st } ρ noFuture (.plain (TyM.univ 1)) FT (teleFrame K.dm (D st) d' ps c e) =
        run { K with D := D st' } ρ noFuture (.plain (TyM.univ 1)) FT (teleFrame K.dm (D st') d' ps c e)) ∧
    (∀ (K : RunCtx) (ρ : Assignment) (ps : List Sem) (j : Nat) (mask : Bool), j < d'.params.length →
      run { K with D := D st } ρ noFuture (.plain (TyM.univ 2)) (Knot.paramTerm d' j) (Params.frameP d' (K.dm.paramTy d') (D st) mask ps) =
        run { K with D := D st' } ρ noFuture (.plain (TyM.univ 2)) (Knot.paramTerm d' j) (Params.frameP d' (K.dm.paramTy d') (D st') mask ps))

/-- **The names an accepted item's code mentions are the stage's** (about the checker: resolution
and D118, `undeclaredCheck`; not derived): an accepted definition's body, its `fix` term and its stored
type name only the stage's declarations and globals; an accepted inductive declaration's field types
name only the stage's declarations and itself (as an applied type), its constructors only the stage's
declarations', and its globals the stage's; its parameter types only the stage's. Stated at any model
(the names do not depend on it). -/
def NamesFact : Prop :=
  ∀ (dm : DataModel) (k : Nat) (hk : k < items.length) (st' : MState),
    verdict fuel items k hk = .ok () st' →
    (∀ d, items[k] = .defn d →
      Knot.Term.nok (stageNames (indsOf {} fuel items) (stage D fuel items dm k)) d.body = true ∧
      Knot.Term.nok (stageNames (indsOf {} fuel items) (stage D fuel items dm k))
        (.fix ⟨d.name⟩ d.hs d.doms d.cod d.dec d.body) = true ∧
      Knot.Value.nok (stageNames (indsOf {} fuel items) (stage D fuel items dm k))
        (((st'.globals.find? (·.name == d.name)).map (·.ty)).getD .bot) = true) ∧
    (∀ d0 d', items[k] = .ind d0 → st'.inds = (stage D fuel items dm k).inds ++ [d'] →
      (∀ c i FT, fieldTerm d' c i = some FT →
        Knot.Term.nok (fieldNames (indsOf {} fuel items) (stage D fuel items dm k) d') FT = true) ∧
      ∀ j, Knot.Term.nok (stageNames (indsOf {} fuel items) (stage D fuel items dm k)) (Knot.paramTerm d' j) = true)

/-- What the checker establishes of a field type's head (`FieldHeads`): a parameter heading it is
declared at a written sort `Prop` or `Type`; a global heading it (a call) has a stored type whose
codomain is the sort `Prop` or `Type`. -/
def HeadLevels (gs : List GDef) (d : IndDecl) : Prop :=
  (∀ c i v, fieldTerm d c i = some (.place (.var v)) → v < d.params.length →
    ∃ l, l ≤ 1 ∧ Knot.paramTerm d (d.params.length - 1 - v) = .sort l) ∧
  (∀ c i f as hd, fieldTerm d c i = some (.call (.const f) as hd) →
    ∃ (cs : List Value) (hs : List Hint) (ds : List Term) (l : Nat) (rd : List (DeclInfo × Value)), l ≤ 1 ∧
      (gs.find? (·.name == f)).map (·.ty) = some (.tPi cs (.pi hs ds (.sort l)) rd))

/-- **The heads of an accepted declaration's field types are at level 0** (the checker's part of
exists10's `FieldLevels`; about the checker; PROVED, `fieldHeads` below, exists13). Of the entry `d'`
the checker stores for the program's `k`-th item, `HeadLevels` at the stage's globals. Since main's
D140 both parts are read from what is written, before anything runs: a parameter that is a field's
whole type is written `Prop` or `Type`; a global whose call is one has its codomain written `Prop` or
`Type` (D140), and `firstOrderTerm`'s call clause finds it with a written Π-type into a sort. Before
D140 the level and call parts were decided by the run-based level check (`sortOf` at the generic
telescope), and the parameter part was false until D128 (`FactsCE.fieldHeads_false`, `TL`). -/
def FieldHeads : Prop :=
  ∀ (k : Nat) (hk : k < items.length) (st' : MState) (d0 d' : IndDecl),
    verdict fuel items k hk = .ok () st' → items[k] = .ind d0 → st'.inds = indsOf {} fuel (items.take k) ++ [d'] →
    HeadLevels st'.globals d'

/-- **`FieldHeads` holds** (PROVED, no hypothesis; exists13, from main's D140): the checker's run on the
`k`-th item is `seedHoles` (which writes neither table) then `checkInd d0`, whose D140 loop and
`firstOrderTerm` give `HeadLevels` of `d0` at the globals it starts from
(`Steps.Machine.runs_checkInd_heads`); the stored entry `d'` is `d0` with its nestable set
(`runs_checkInd_tables`, so its parameters and constructors are `d0`'s) and the globals are unchanged. -/
theorem fieldHeads : FieldHeads fuel items := by
  intro k hk st' d0 d' hv hit hI
  unfold verdict at hv
  have hr := Steps.Machine.runs_of_runMachine_fst hv
  rw [hit] at hr
  unfold checkItem at hr
  obtain ⟨_, s₁, b₁, hs, hc⟩ := Steps.Runs.bind_inv hr
  obtain ⟨hT1, hT2⟩ := Steps.Machine.runs_checkInd_tables hc
  obtain ⟨hP, hC⟩ := Steps.Machine.runs_checkInd_heads hc
  rw [hT2] at hI
  obtain ⟨-, he⟩ := List.append_inj' hI.symm rfl
  simp only [List.cons.injEq, and_true] at he
  subst he
  rw [hT1]
  exact ⟨fun c i v h1 h2 => hP c i v h1 h2, fun c i f as hd h1 => hC c i f as hd h1⟩

/-- **A global whose stored codomain is `Prop` or `Type` calls to level-0 type values** (the
model's part of exists10's `FieldLevels`; about the model; PROVED, `globalCallLevels` below, exists12).
At every stage, at every model's read, every call through the stage's meaning of such a global gives
a level-0 type value or no type value (`FieldLevel.CallsLevel0`). The proof (`GlobalCalls.lean`): the
stage's type of the global is `err` or the meaning (`globalTyS`) of `.bot` or of the first stored
entry of its name (`GlobalCalls.TyInv`, kept by every item); that meaning is `err` or
`piTyAt R l' ps out` with `out` constantly `univ l` (`globalTyS_tPi_sort`); at `l' ≠ 3` it is not a
level-2 code (`FieldLevel.callsLevel0_of_not_t2`), and at `l' = 3` (a domain in `Type₁`, the hard
case) every leaf of the telescope is `code2 (univ l)`, a lifted level-1 code, so a call is its
encoding there, a level-0 type value (`GlobalCalls.callOfL_datLeaf`, the referee's Y3 lemma). -/
def GlobalCallLevels : Prop :=
  ∀ (dm : DataModel) (k : Nat), k ≤ items.length →
    ∀ (f : String) (cs : List Value) (hs : List Hint) (ds : List Term) (l : Nat) (rd : List (DeclInfo × Value)), l ≤ 1 →
      ((stage D fuel items dm k).globals.find? (·.name == f)).map (·.ty) = some (.tPi cs (.pi hs ds (.sort l)) rd) →
      ∀ dmR : DataModel, FieldLevel.CallsLevel0 dmR ((stage D fuel items dm k).baseC.global f)

/-- **`GlobalCallLevels` holds** (PROVED, no hypothesis; exists12): every stage keeps
`GlobalCalls.TyInv` (`tyInv_progMeaningFrom`), from which `callsLevel0_of_tyInv`. -/
theorem globalCallLevels : GlobalCallLevels D fuel items :=
  fun dm _ _ f cs hs ds l rd hl hf dmR =>
    GlobalCalls.callsLevel0_of_tyInv (fun _ => .err) _
      (GlobalCalls.tyInv_progMeaningFrom dm D _ _ {} fuel _ {} (GlobalCalls.tyInv_empty _)) f cs hs ds l rd hl hf dmR

theorem fieldsNoVal_of_ctors {d d' : IndDecl} (h : d'.ctors = d.ctors) (hv : Knot.FieldsNoVal d) :
    Knot.FieldsNoVal d' := fun c i FT hFT => hv c i FT (by unfold fieldTerm at hFT ⊢; rw [← h]; exact hFT)

theorem paramsNoVal_of_params {d d' : IndDecl} (h : d'.params = d.params) (hv : ParamsNoVal d) :
    ParamsNoVal d' := fun j => by have := hv j; unfold Knot.paramTerm at this ⊢; rw [h]; exact this

/-- **`DecLocal`'s `caps` part** (an obligation on the decisions, for the [Entry] captures; read TRUE by
machine10, not derived): every capture a block's [Entry] takes is in the entry or rooted at a free
variable of the term. At the chain's decisions it is `BlockCaps.staticBlockCaps`; its derivation needs,
besides the join's (`decLocal_join_ff`) and the closures' (`fnOccs_ok`) roots, that `Array.qsort`
(the captures' sort) keeps membership, which Lean's core does not state. -/
def DecCaps (D : Decisions) : Prop :=
  ∀ sc entry t qk, qk ∈ (D.blockCaps sc entry t).2 → qk.1 ∈ entry ∨ qk.1.root ∈ t.freeVars

/-- `DecLocal` but its `caps` part: PROVED at the chain's decisions (`Steps.Machine.decLocal_inv_chain`,
`decLocal_join_chain`, `decLocal_rep_chain`; exists12, machine11). -/
def DecLocal3 (D : Decisions) : Prop :=
  (∀ sc p q, q ∈ D.invalidated sc p → q.root = p.root) ∧
  (∀ sc entry t q, q ∈ D.joinMoves sc entry t → q ∈ entry ∨ q.root ∈ t.freeVars) ∧
  (∀ sc t q, q ∈ D.rePointed sc t → q.root ∈ t.freeVars)

/-- **The facts the existence of the data model rests on**, together (`exists_dataModel_facts`): about
the checker, `NamesFact`, `VaryValFact`; obligations on the checker's decisions,
`DecCaps` (`DecLocal`'s `caps` part) at every state and `DecStable`. No longer a field (exists13):
`FieldHeads`, proved from main's D140 (`fieldHeads`). No longer fields (exists12):
`DecLocal`'s other three parts (`DecLocal3`, proved at the chain's decisions, its own hypothesis of
`exists_dataModel_facts`); `ItemFacts`, proved
(`itemFacts`); the fact about the model, `GlobalCallLevels`, proved (`globalCallLevels`); the fact about
resolution, `NoValFact`, proved for the items a program resolves to (`Steps.Machine.noVal_runResolve`),
which `exists_dataModel_facts` takes as its own hypothesis and `Consistency.exists_dataModel` derives
from the resolution. -/
structure DataFacts : Prop where
  varyVal : VaryValFact fuel items
  names : NamesFact D fuel items
  decCaps : ∀ st, DecCaps (D st)
  decStable : DecStable D fuel items

/-! ## The step's bookkeeping (exists10) -/

include D in
theorem inds_succ (hIF : ItemFacts) (k : Nat) (hk : k < items.length) :
    indsOf {} fuel (items.take k) <+: indsOf {} fuel (items.take (k + 1)) := by
  rw [← stage_inds D fuel items dm0 k, ← stage_inds D fuel items dm0 (k + 1), stage_succ_eq D fuel items dm0 k hk]
  split
  · rename_i st' hv
    rw [verdict_eq D fuel items dm0 k hk] at hv
    obtain ⟨hI, hD⟩ := hIF _ _ _ _ hv
    cases hit : items[k] with
    | ind d =>
      obtain ⟨d', h1, -⟩ := hI d hit
      show _ <+: st'.inds
      rw [h1]; exact List.prefix_append _ _
    | defn d =>
      show _ <+: st'.inds
      rw [(hD d hit).1]; exact List.prefix_refl _
  · exact List.prefix_refl _

include D in
theorem inds_mono (hIF : ItemFacts) (k' : Nat) : ∀ k, k' ≤ k → k ≤ items.length →
    indsOf {} fuel (items.take k') <+: indsOf {} fuel (items.take k)
  | 0, hle, _ => by
    have : k' = 0 := by omega
    subst this; exact List.prefix_refl _
  | k + 1, hle, hk => by
    rcases Nat.lt_or_ge k' (k + 1) with h | h
    · exact (inds_mono hIF k' k (by omega) (by omega)).trans (inds_succ D fuel items hIF k (by omega))
    · have : k' = k + 1 := by omega
      subst this; exact List.prefix_refl _

/-- **The earlier stages carry over to a model agreeing at the stage's declarations.** -/
theorem inv_carry (hIF : ItemFacts) {k : Nat} (hk : k ≤ items.length) {dm dm' : DataModel} (h : Inv D fuel items k dm)
    (hag : ∀ d ∈ indsOf {} fuel (items.take k), dm'.recOf d = dm.recOf d ∧ dm'.paramTy d = dm.paramTy d) :
    (∀ k' ≤ k, ∀ dm'' : DataModel,
      (∀ d ∈ indsOf {} fuel (items.take k'), dm''.recOf d = dm'.recOf d ∧ dm''.paramTy d = dm'.paramTy d) →
        stage D fuel items dm'' k' = stage D fuel items dm' k') ∧
    (∀ k' ≤ k, ∀ d ∈ indsOf {} fuel (items.take k'), ∀ K : RunCtx,
      Extends D fuel items dm' (stage D fuel items dm' k') K → DeclFaithful K d) := by
  have hsub : ∀ k' ≤ k, ∀ d ∈ indsOf {} fuel (items.take k'), d ∈ indsOf {} fuel (items.take k) :=
    fun k' hk' d hd => (inds_mono D fuel items hIF k' k hk' hk).subset hd
  have hst : ∀ k' ≤ k, stage D fuel items dm' k' = stage D fuel items dm k' :=
    fun k' hk' => h.congr k' hk' dm' fun d hd => hag d (hsub k' hk' d hd)
  refine ⟨fun k' hk' dm'' h'' => ?_, fun k' hk' d hd K hK => ?_⟩
  · rw [hst k' hk', h.congr k' hk' dm'' fun d hd =>
      ⟨(h'' d hd).1.trans (hag d (hsub k' hk' d hd)).1, (h'' d hd).2.trans (hag d (hsub k' hk' d hd)).2⟩]
  · rw [hst k' hk'] at hK
    refine h.faithful k' hk' d hd K ⟨hK.gamma, fun d' hd' => ?_, hK.globals, hK.dec, hK.lam, hK.cur⟩
    have hd'' : d' ∈ indsOf {} fuel (items.take k') := by rwa [stage_inds] at hd'
    rw [(hK.agree d' hd').1, (hK.agree d' hd').2, (hag d' (hsub k' hk' d' hd'')).1, (hag d' (hsub k' hk' d' hd'')).2]
    exact ⟨rfl, rfl⟩

/-- **A rejected item**: the stage does not change. -/
theorem inv_reject (k : Nat) (hk : k < items.length) (dm : DataModel) (h : Inv D fuel items k dm)
    (hv : ∀ st', verdict fuel items k hk ≠ .ok () st') : Inv D fuel items (k + 1) dm := by
  have hst : ∀ dm', stage D fuel items dm' (k + 1) = stage D fuel items dm' k := fun dm' => by
    rw [stage_succ_eq D fuel items dm' k hk]
    split
    · rename_i st' e; exact absurd e (hv st')
    · rfl
  have hind : indsOf {} fuel (items.take (k + 1)) = indsOf {} fuel (items.take k) := by
    rw [← stage_inds D fuel items dm0, ← stage_inds D fuel items dm0, hst]
  refine ⟨h.covers, ?_, fun k' hk' dm' hag => ?_, fun k' hk' d hd K hK => ?_, ?_, ?_, ?_⟩
  · rw [hind]; exact h.rest
  · rcases Nat.lt_or_ge k' (k + 1) with hl | hl
    · exact h.congr k' (by omega) dm' hag
    · have : k' = k + 1 := by omega
      subst this
      rw [hst, hst]; rw [hind] at hag; exact h.congr k (Nat.le_refl _) dm' hag
  · rcases Nat.lt_or_ge k' (k + 1) with hl | hl
    · exact h.faithful k' (by omega) d hd K hK
    · have : k' = k + 1 := by omega
      subst this
      rw [hst] at hK; rw [hind] at hd; exact h.faithful k (Nat.le_refl _) d hd K hK
  · rw [hind]; exact h.par
  · rw [hind]; exact h.mono
  · rw [hind]; exact h.val

/-- The stage after an accepted item, at any model, read through its verdict. -/
theorem stage_ok (dm : DataModel) (k : Nat) (hk : k < items.length) (st' : MState)
    (hv : verdict fuel items k hk = .ok () st') :
    stage D fuel items dm (k + 1) = { globals := st'.globals, inds := st'.inds, means := match items[k] with
      | .defn d => (stage D fuel items dm k).means ++ [(d.name,
          (defMeaning (fun _ => .err) ((stage D fuel items dm k).ctx dm D (indsOf {} fuel items) st') d
            (((st'.globals.find? (·.name == d.name)).map (·.ty)).getD .bot)).getD (.err, .plain .err))]
      | .ind _ => (stage D fuel items dm k).means } := by
  rw [stage_succ_eq D fuel items dm k hk]
  split
  · rename_i st'' e; rw [hv] at e; cases e; rfl
  · rename_i hne; exact absurd hv (hne st')

/-- An extension of a later stage with the same declarations, more meanings appended and more globals
extends the earlier stage. -/
theorem extends_of_more {dm : DataModel} {P P' : ProgState} {K : RunCtx} (hK : Extends D fuel items dm P' K)
    (hi : P.inds <+: P'.inds) (hg : P.globals <+: P'.globals) (hm : ∃ xs, P'.means = P.means ++ xs) :
    Extends D fuel items dm P K := by
  obtain ⟨xs, hxs⟩ := hm
  refine ⟨hK.gamma, fun d hd => hK.agree d (hi.subset hd), fun n hn => ?_, ?_, hK.lam, hK.cur⟩
  · obtain ⟨y, hy⟩ := Option.isSome_iff_exists.1 hn
    have e : P'.means.find? (·.1 == n) = some y := by rw [hxs, List.find?_append, hy]; rfl
    rw [hK.globals n (by rw [e]; rfl)]
    simp only [ProgState.baseC, ProgState.globalMean, ProgState.globalTy, e, hy]
  · obtain ⟨st, h1, h2, h3, h4⟩ := hK.dec
    exact ⟨st, hi.trans h1, h2, hg.trans h3, h4⟩

/-- **An accepted definition**: the same model; the new meaning reads it only at the stage's
declarations (`NamesFact`, `defMeaning_congrN`). -/
theorem inv_defn (hIF : ItemFacts) (hN : NamesFact D fuel items)
    (hpre : ∀ k, k ≤ items.length → indsOf {} fuel (items.take k) <+: indsOf {} fuel items)
    (k : Nat) (hk : k < items.length) (dm : DataModel) (h : Inv D fuel items k dm)
    (st' : MState) (d : Def) (hv : verdict fuel items k hk = .ok () st') (hit : items[k] = .defn d) :
    Inv D fuel items (k + 1) dm := by
  have hv' := hv
  rw [verdict_eq D fuel items dm k hk] at hv'
  obtain ⟨hi, hg⟩ := (hIF _ _ _ _ hv').2 d hit
  have hi' : st'.inds = (stage D fuel items dm k).inds := hi
  have hstage : ∀ dm', stage D fuel items dm' (k + 1) =
      { globals := st'.globals, inds := st'.inds,
        means := (stage D fuel items dm' k).means ++ [(d.name,
          (defMeaning (fun _ => .err) ((stage D fuel items dm' k).ctx dm' D (indsOf {} fuel items) st') d
            (((st'.globals.find? (·.name == d.name)).map (·.ty)).getD .bot)).getD (.err, .plain .err))] } := by
    intro dm'
    rw [stage_ok D fuel items dm' k hk st' hv]
    simp only [hit]
  have hind : indsOf {} fuel (items.take (k + 1)) = indsOf {} fuel (items.take k) := by
    rw [← stage_inds D fuel items dm (k + 1), ← stage_inds D fuel items dm k, hstage dm]
    exact hi'
  refine ⟨h.covers, ?_, fun k' hk' dm' hag => ?_, fun k' hk' d0 hd K hK => ?_, ?_, ?_, ?_⟩
  · rw [hind]; exact h.rest
  · rcases Nat.lt_or_ge k' (k + 1) with hl | hl
    · exact h.congr k' (by omega) dm' hag
    · have : k' = k + 1 := by omega
      subst this
      rw [hind] at hag
      rw [hstage dm', hstage dm, h.congr k (Nat.le_refl _) dm' hag]
      obtain ⟨h1, h2, h3⟩ := (hN dm k hk st' hv).1 d hit
      have hA := agreeN_stage (K := (stage D fuel items dm k).ctx dm D (indsOf {} fuel items) st') (dm' := dm')
        (P := stage D fuel items dm k) _ rfl (by rw [stage_inds]; exact hpre k (by omega))
        (fun M hM => hag M (by rw [← stage_inds D fuel items dm k]; exact hM)) (fun _ _ => rfl)
      rw [show (stage D fuel items dm k).ctx dm' D (indsOf {} fuel items) st' =
        { (stage D fuel items dm k).ctx dm D (indsOf {} fuel items) st' with dm := dm' } from rfl,
        defMeaning_congrN _ dm' _ hA _ d _ h1 h2 h3]
  · rcases Nat.lt_or_ge k' (k + 1) with hl | hl
    · exact h.faithful k' (by omega) d0 hd K hK
    · have : k' = k + 1 := by omega
      subst this
      rw [hind] at hd
      rw [hstage dm] at hK
      exact h.faithful k (Nat.le_refl _) d0 hd K (extends_of_more D fuel items hK (by rw [← hi']; exact List.prefix_refl _)
        hg ⟨_, rfl⟩)
  · rw [hind]; exact h.par
  · rw [hind]; exact h.mono
  · rw [hind]; exact h.val

/-! ## An accepted inductive declaration -/

open Classical in
/-- A model with `d`'s parameter types replaced. -/
noncomputable def setPty (dm : DataModel) (d : IndDecl) (P : Nat → List Sem → TyM) : DataModel :=
  { dm with paramTy := fun M => if M = d then P else dm.paramTy M }

/-- The build context of the declaration accepted at item `k`: the stage's model and globals, the
whole list, the decisions after the declaration. -/
noncomputable def ctx0 (dm : DataModel) (k : Nat) (st' : MState) : RunCtx :=
  (stage D fuel items dm k).ctx dm D (indsOf {} fuel items) st'

/-- The new declaration's parameter types (`Params.pty`, piece 7). -/
noncomputable def ptyAt (dm : DataModel) (k : Nat) (st' : MState) (d : IndDecl) : Nat → List Sem → TyM :=
  Params.pty (ctx0 D fuel items dm k st') (fun _ => .err) d

/-- The build context with the new declaration's parameter types set: where its records are built. -/
noncomputable def ctx1 (dm : DataModel) (k : Nat) (st' : MState) (d : IndDecl) : RunCtx :=
  (stage D fuel items dm k).ctx (setPty dm d (ptyAt D fuel items dm k st' d)) D (indsOf {} fuel items) st'

theorem paramsOk_typed {dm : DataModel} {d : IndDecl} {ps : List Sem} (h : paramsOk dm d ps) : ParamsTyped dm d ps :=
  fun j hj => h j _ (List.getElem?_eq_getElem hj)

/-- **The new declaration is faithful at every extension of the stage that accepts it.** -/
theorem inv_ind_faithful (hN : NamesFact D fuel items)
    (hDL : ∀ st, FrameLocal.DecLocal (D st)) (hDS : DecStable D fuel items)
    (k : Nat) (hk : k < items.length) (dm : DataModel)
    (st' : MState) (d0 d' : IndDecl) (hv : verdict fuel items k hk = .ok () st') (hit : items[k] = .ind d0)
    (hI : st'.inds = (stage D fuel items dm k).inds ++ [d']) (hgl : st'.globals = (stage D fuel items dm k).globals)
    (hfresh : d' ∉ (stage D fuel items dm k).inds) (hpnv : ParamsNoVal d') (hnv : Knot.FieldsNoVal d')
    (hFL0 : ∀ (dm'' : DataModel) (ρ : Assignment),
      ParamsFaithfulAt ((stage D fuel items dm k).ctx dm'' D (indsOf {} fuel items) st') ρ d' →
      FieldLevel.FieldLevel0 ((stage D fuel items dm k).ctx dm'' D (indsOf {} fuel items) st') ρ d')
    (S : KnotSpec) (Rc : List Sem → Rec)
    (hagree : DeclStep.SpecAgree (ctx1 D fuel items dm k st' d') (fun _ => .err) d' S)
    (hRc : ∀ ps, ParamsTyped (ctx1 D fuel items dm k st' d').dm d' ps → Rc ps = recK S ps)
    (hrecF : ∀ K : RunCtx, K.dm.recOf d' = Rc → K.dm.paramTy d' = ptyAt D fuel items dm k st' d' →
      RecordsFaithfulAt K d')
    (hΓp : (stage D fuel items dm k).inds ++ [d'] <+: indsOf {} fuel items)
    (hPi : (stage D fuel items dm k).inds = indsOf {} fuel (items.take k))
    {dm' : DataModel} (hsk : stage D fuel items dm' k = stage D fuel items dm k)
    (hagP : ∀ M ∈ (stage D fuel items dm k).inds, dm'.recOf M = dm.recOf M ∧ dm'.paramTy M = dm.paramTy M)
    (hdm'_d : dm'.recOf d' = Rc ∧ dm'.paramTy d' = ptyAt D fuel items dm k st' d')
    (K : RunCtx)
    (hK : Extends D fuel items dm' { globals := st'.globals, inds := st'.inds, means := (stage D fuel items dm' k).means } K) :
    DeclFaithful K d' := by
  have hmeans : (stage D fuel items dm' k).means = (stage D fuel items dm k).means := by rw [hsk]
  have hpP : (stage D fuel items dm k).inds <+: indsOf {} fuel items := (List.prefix_append _ _).trans hΓp
  have hd' : d' ∈ st'.inds := by rw [hI]; exact List.mem_append_right _ (List.mem_singleton_self _)
  have hKrec : K.dm.recOf d' = Rc := (hK.agree d' hd').1.trans hdm'_d.1
  have hKpt : K.dm.paramTy d' = ptyAt D fuel items dm k st' d' := (hK.agree d' hd').2.trans hdm'_d.2
  have hKM : ∀ M ∈ (stage D fuel items dm k).inds, K.dm.recOf M = dm.recOf M ∧ K.dm.paramTy M = dm.paramTy M :=
    fun M hM =>
      have hM' : M ∈ st'.inds := by rw [hI]; exact List.mem_append_left _ hM
      ⟨(hK.agree M hM').1.trans (hagP M hM).1, (hK.agree M hM').2.trans (hagP M hM).2⟩
  have hKgl : ∀ n, ((stage D fuel items dm k).means.find? (·.1 == n)).isSome = true →
      K.C.global n = (stage D fuel items dm k).baseC.global n := fun n hn => by
    have := hK.globals n (by show ((stage D fuel items dm' k).means.find? _).isSome = true; rw [hmeans]; exact hn)
    rw [this]
    simp only [ProgState.baseC, ProgState.globalMean, ProgState.globalTy, hmeans]
  have hI0 : st'.inds = indsOf {} fuel (items.take k) ++ [d'] := by rw [hI, hPi]
  have hst'Γ : st'.inds <+: indsOf {} fuel items := by rw [hI]; exact hΓp
  obtain ⟨st, h1, h2, h3, hKD⟩ := hK.dec
  obtain ⟨hDSf, hDSp⟩ := hDS k hk st' d0 d' hv hit hI0 st h1 h2 h3
  have hlab : ∀ g, ((stage D fuel items dm k).baseC.global g).2.label = none :=
    stage_label D fuel items dm k (by omega)
  have hnames := (hN dm k hk st' hv).2 d0 d' hit hI
  have hK1pt : (ctx1 D fuel items dm k st' d').dm.paramTy d' = ptyAt D fuel items dm k st' d' := by
    simp [ctx1, ProgState.ctx, setPty]
  -- the knot's context
  let Kb : RunCtx := { ctx1 D fuel items dm k st' d' with dm := setRec (ctx1 D fuel items dm k st' d').dm d' (recK S) }
  have hKbM : ∀ M ∈ (stage D fuel items dm k).inds, Kb.dm.recOf M = dm.recOf M ∧ Kb.dm.paramTy M = dm.paramTy M := by
    intro M hM
    have hMd : M ≠ d' := fun e => hfresh (e ▸ hM)
    simp [Kb, ctx1, ProgState.ctx, setRec, setPty, hMd]
  have hKbd : Kb.dm.recOf d' = recK S ∧ Kb.dm.paramTy d' = ptyAt D fuel items dm k st' d' := by
    simp [Kb, ctx1, ProgState.ctx, setRec, setPty]
  -- `d'`'s parameter types are faithful at the knot's context (what `hFL0` asks)
  have hPFb : ParamsFaithfulAt Kb (fun _ => .err) d' := by
    obtain ⟨-, hDSp'⟩ := hDS k hk st' d0 d' hv hit hI0 st' (List.prefix_refl _) hst'Γ (List.prefix_refl _)
    apply DeclStep.paramsFaithful_pty (ctx0 D fuel items dm k st') (fun _ => .err) d' hlab (hDL st') Kb _ hKbd.2
    intro ps j hn Q hps hl hj
    have hjl : j < d'.params.length := (List.getElem?_eq_some_iff.1 hj).1
    have hQ : Knot.paramTerm d' j = Q := by simp [Knot.paramTerm, hj]
    exact DeclStep.param_transfer (st := st') (st' := st') hQ (fun K' ρ' ps' mask => hDSp' K' ρ' ps' j mask hjl)
      Kb (ctx0 D fuel items dm k st') rfl rfl rfl rfl rfl (stageNames (indsOf {} fuel items) (stage D fuel items dm k))
      (agreeN_stage (K := { Kb with Δ := (ctx0 D fuel items dm k st').Δ, D := D st' }) _ rfl hpP
        (fun M hM => ⟨(hKbM M hM).1.symm, (hKbM M hM).2.symm⟩) (fun _ _ => rfl))
      (hQ ▸ hpnv j) (hQ ▸ hnames.2 j) _ _ ps _ hKbd.2
  intro Δ ρ
  refine ⟨?_, ?_, hrecF K hKrec hKpt⟩
  · -- fields
    have hrecT : ∀ ps, ParamsTyped K.dm d' ps → K.dm.recOf d' ps = recK S ps := fun ps hps => by
      rw [hKrec]; exact hRc ps (DeclStep.paramsTyped_congr (hKpt.trans hK1pt.symm) hps)
    apply DeclStep.fieldsFaithful_spec (ctx1 D fuel items dm k st' d') (fun _ => .err) d' S hagree { K with Δ := Δ } ρ
      hrecT (hKpt.trans hK1pt.symm)
    · intro ps c i e FT hl hps he hei hFT
      refine DeclStep.field_transfer (st := st) (st' := st') (i := i) (fun K' ρ' ps' e' => hDSf K' ρ' ps' c i e' FT hFT)
        { K with Δ := Δ } Kb hKD rfl hK.gamma hK.lam hK.cur
        (fieldNames (indsOf {} fuel items) (stage D fuel items dm k) d') ?_ (hnv c i FT hFT) (hnames.1 c i FT hFT)
        ρ _ ps e ?_ ?_
      · exact agreeN_field (K := { { K with Δ := Δ } with Δ := Kb.Δ, D := D st' }) _ hK.gamma hΓp
          (fun M hM => ⟨(hKbM M hM).1.trans (hKM M hM).1.symm, (hKbM M hM).2.trans (hKM M hM).2.symm⟩)
          (hKbd.2.trans hKpt.symm)
          (fun ps' hok => by rw [hKbd.1]; exact (hrecT ps' (paramsOk_typed hok)).symm)
          (fun n hn => (hKgl n hn).symm)
      · exact (hrecT ps hps).trans (congrFun hKbd.1.symm ps)
      · exact hKpt.trans hKbd.2.symm
    · intro ps c i e FT r s' hl hps he hei hFT hr
      exact hFL0 Kb.dm (fun _ => .err) hPFb ps c i e FT r s' hl
        (DeclStep.paramsTyped_congr (hKpt.trans hKbd.2.symm) hps)
        (DeclStep.fieldsTyped_congr ((hrecT ps hps).trans (congrFun hKbd.1.symm ps)) he) hei hFT hr
  · -- parameter types
    apply DeclStep.paramsFaithful_pty (ctx0 D fuel items dm k st') (fun _ => .err) d' hlab (hDL st') { K with Δ := Δ } ρ hKpt
    intro ps j hn Q hps hl hj
    have hjl : j < d'.params.length := (List.getElem?_eq_some_iff.1 hj).1
    have hQ : Knot.paramTerm d' j = Q := by simp [Knot.paramTerm, hj]
    exact DeclStep.param_transfer (st := st) (st' := st') hQ (fun K' ρ' ps' mask => hDSp K' ρ' ps' j mask hjl)
      { K with Δ := Δ } (ctx0 D fuel items dm k st') hKD rfl hK.gamma hK.lam hK.cur
      (stageNames (indsOf {} fuel items) (stage D fuel items dm k))
      (agreeN_stage (K := { { K with Δ := Δ } with Δ := (ctx0 D fuel items dm k st').Δ, D := D st' }) _ hK.gamma hpP
        (fun M hM => ⟨(hKM M hM).1.symm, (hKM M hM).2.symm⟩) (fun n hn => (hKgl n hn).symm))
      (hQ ▸ hpnv j) (hQ ▸ hnames.2 j) ρ _ ps _ hKpt

/-- **The step at an accepted inductive declaration `d'`, for either sort**, given its records `Rc`
and a spec `S` with `S`'s agreement at the build context, `Rc` the spec's records at well-typed
parameters, `Rc` faithful as records, parametric (data-sorted) or monotone (`Prop`-sorted). The new
model sets `d'`'s parameter types (`ptyAt`) and records (`Rc`). -/
theorem inv_ind_core (hIF : ItemFacts) (hN : NamesFact D fuel items)
    (hDL : ∀ st, FrameLocal.DecLocal (D st)) (hDS : DecStable D fuel items)
    (hpre : ∀ k, k ≤ items.length → indsOf {} fuel (items.take k) <+: indsOf {} fuel items)
    (k : Nat) (hk : k < items.length) (dm : DataModel) (h : Inv D fuel items k dm)
    (st' : MState) (d0 d' : IndDecl) (hv : verdict fuel items k hk = .ok () st') (hit : items[k] = .ind d0)
    (hI : st'.inds = (stage D fuel items dm k).inds ++ [d']) (hgl : st'.globals = (stage D fuel items dm k).globals)
    (hfresh : d' ∉ (stage D fuel items dm k).inds) (hpnv : ParamsNoVal d') (hnv : Knot.FieldsNoVal d')
    (hFL0 : ∀ (dm'' : DataModel) (ρ : Assignment),
      ParamsFaithfulAt ((stage D fuel items dm k).ctx dm'' D (indsOf {} fuel items) st') ρ d' →
      FieldLevel.FieldLevel0 ((stage D fuel items dm k).ctx dm'' D (indsOf {} fuel items) st') ρ d')
    (S : KnotSpec) (Rc : List Sem → Rec)
    (hagree : DeclStep.SpecAgree (ctx1 D fuel items dm k st' d') (fun _ => .err) d' S)
    (hRc : ∀ ps, ParamsTyped (ctx1 D fuel items dm k st' d').dm d' ps → Rc ps = recK S ps)
    (hrecF : ∀ K : RunCtx, K.dm.recOf d' = Rc → K.dm.paramTy d' = ptyAt D fuel items dm k st' d' →
      RecordsFaithfulAt K d')
    (hpar' : d'.sort ≠ 0 → ∀ n, RAgree (fun j => d'.nestable.getD j false) n Rc Rc)
    (hmono' : d'.sort = 0 → ∀ ps ps', PropLe d' ps ps' → ∀ c i es, es.length = i →
      ShapeLe (uShape d' (Rc ps) c i es) (uShape d' (Rc ps') c i es))
    (hval' : ∀ j, nestOf d' j = true → d'.paramIsType j = true) :
    ∃ dm' : DataModel, Inv D fuel items (k + 1) dm' ∧
      ∀ d ∈ (stage D fuel items dm k).inds, dm'.recOf d = dm.recOf d ∧ dm'.paramTy d = dm.paramTy d := by
  have hPi : (stage D fuel items dm k).inds = indsOf {} fuel (items.take k) := stage_inds D fuel items dm k
  let PT := ptyAt D fuel items dm k st' d'
  let dm' := setRec (setPty dm d' PT) d' Rc
  have hdm'_ne : ∀ M, M ≠ d' → dm'.recOf M = dm.recOf M ∧ dm'.paramTy M = dm.paramTy M := by
    intro M hM; simp [dm', setRec, setPty, hM]
  have hdm'_d : dm'.recOf d' = Rc ∧ dm'.paramTy d' = PT := by simp [dm', setRec, setPty]
  have hagP : ∀ M ∈ (stage D fuel items dm k).inds, dm'.recOf M = dm.recOf M ∧ dm'.paramTy M = dm.paramTy M :=
    fun M hM => hdm'_ne M (fun e => hfresh (e ▸ hM))
  obtain ⟨hcongr, hfaith⟩ := inv_carry D fuel items hIF (by omega) h (fun M hM => hagP M (hPi ▸ hM))
  have hstage : ∀ dm'', stage D fuel items dm'' (k + 1) =
      { globals := st'.globals, inds := st'.inds, means := (stage D fuel items dm'' k).means } := by
    intro dm''
    rw [stage_ok D fuel items dm'' k hk st' hv]
    simp only [hit]
  have hind : indsOf {} fuel (items.take (k + 1)) = (stage D fuel items dm k).inds ++ [d'] := by
    rw [← stage_inds D fuel items dm (k + 1), hstage, hI]
  have hsk : stage D fuel items dm' k = stage D fuel items dm k :=
    h.congr k (Nat.le_refl _) dm' fun M hM => hagP M (hPi ▸ hM)
  have hΓp : (stage D fuel items dm k).inds ++ [d'] <+: indsOf {} fuel items := by
    rw [← hind]; exact hpre (k + 1) (by omega)
  refine ⟨dm', ⟨fun d => h.covers d, ?_, ?_, ?_, ?_, ?_, ?_⟩, hagP⟩
  · -- rest
    intro M hM
    rw [hind] at hM
    have hMd : M ≠ d' := fun e => hM (e ▸ List.mem_append_right _ (List.mem_singleton_self _))
    have hMP : M ∉ indsOf {} fuel (items.take k) := fun e => hM (List.mem_append_left _ (hPi ▸ e))
    rw [(hdm'_ne M hMd).1, (hdm'_ne M hMd).2]
    exact h.rest M hMP
  · -- congr
    intro k' hk' dm'' hag
    rcases Nat.lt_or_ge k' (k + 1) with hl | hl
    · exact hcongr k' (by omega) dm'' hag
    · have : k' = k + 1 := by omega
      subst this
      rw [hstage dm'', hstage dm', hcongr k (Nat.le_refl _) dm'' fun d hd =>
        hag d (by rw [hind]; exact List.mem_append_left _ (hPi ▸ hd))]
  · -- faithful
    intro k' hk' d hd K hK
    rcases Nat.lt_or_ge k' (k + 1) with hl | hl
    · exact hfaith k' (by omega) d hd K hK
    have : k' = k + 1 := by omega
    subst this
    rw [hind] at hd
    rw [hstage dm'] at hK
    rcases List.mem_append.1 hd with hd | hd
    · refine hfaith k (Nat.le_refl _) d (hPi ▸ hd) K (extends_of_more D fuel items hK ?_ ?_ ⟨[], by simp⟩)
      · show (stage D fuel items dm' k).inds <+: st'.inds
        rw [hsk, hI]; exact List.prefix_append _ _
      · show (stage D fuel items dm' k).globals <+: st'.globals
        rw [hsk, hgl]; exact List.prefix_refl _
    rw [List.mem_singleton] at hd
    subst hd
    exact inv_ind_faithful D fuel items hN hDL hDS k hk dm st' d0 d hv hit hI hgl hfresh hpnv hnv hFL0 S Rc hagree hRc
      hrecF hΓp hPi hsk hagP hdm'_d K hK
  · -- par
    intro M hM hMs n
    rw [hind] at hM
    rcases List.mem_append.1 hM with hM | hM
    · rw [(hagP M hM).1]; exact h.par M (hPi ▸ hM) hMs n
    · rw [List.mem_singleton] at hM; subst hM; rw [hdm'_d.1]; exact hpar' hMs n
  · -- mono
    intro M hM hMs
    rw [hind] at hM
    rcases List.mem_append.1 hM with hM | hM
    · rw [(hagP M hM).1]; exact h.mono M (hPi ▸ hM) hMs
    · rw [List.mem_singleton] at hM; subst hM; rw [hdm'_d.1]; exact hmono' hMs
  · -- val
    intro M hM
    rw [hind] at hM
    rcases List.mem_append.1 hM with hM | hM
    · exact h.val M (hPi ▸ hM)
    · rw [List.mem_singleton] at hM; subst hM; exact hval'

/-- **The step** (exists10). From the invariant at stage `k` for a model, the invariant at stage `k + 1`
for a model agreeing with it at stage `k`'s declarations. By the `k`-th item's verdict:
* not accepted: the stage is unchanged, the same model (`inv_reject`);
* an accepted definition: the same model; the new meaning reads it only at the stage's declarations
  (`NamesFact`, `defMeaning_congrN`) (`inv_defn`);
* an accepted inductive declaration `d'` (`ItemFacts`: one new entry passing `IndChecks`): the
  parameter types `ptyAt` (piece 7) at the build context `ctx0` (the stage's model and globals, the
  decisions after `d'`); at `ctx1` (with them set) the records: a data-sorted `d'`'s the knot's at the
  canonical parameters (`Records.recCanon`, hypotheses `Knot.ParHyp` from `par`, `rest` and
  `grammar_of_checks`' `TopSortOk`), a `Prop`-sorted one's the truth spec's (`Records.recCanonP`,
  hypothesis `hmono` from `mono` and `rest`). `d'` is faithful at every extension (`inv_ind_faithful`,
  through `DeclStep`'s transfers: `DecStable`, `Knot.runT_congrN` with `NamesFact`, no embedded value;
  the field types' level by `FieldLevel.fieldLevel0_of` from `FieldHeads` and `GlobalCallLevels`). -/
theorem inv_step (hIF : ItemFacts) (hNV : NoValFact items) (hVV : VaryValFact fuel items) (hN : NamesFact D fuel items) (hFH : FieldHeads fuel items) (hGC : GlobalCallLevels D fuel items)
    (hDL : ∀ st, FrameLocal.DecLocal (D st)) (hDS : DecStable D fuel items)
    (hpre : ∀ k, k ≤ items.length → indsOf {} fuel (items.take k) <+: indsOf {} fuel items)
    (k : Nat) (hk : k < items.length) (dm : DataModel) (h : Inv D fuel items k dm) :
    ∃ dm' : DataModel, Inv D fuel items (k + 1) dm' ∧
      ∀ d ∈ (stage D fuel items dm k).inds, dm'.recOf d = dm.recOf d ∧ dm'.paramTy d = dm.paramTy d := by
  cases hv : verdict fuel items k hk with
  | fail f => exact ⟨dm, inv_reject D fuel items k hk dm h (fun st' e => by rw [hv] at e; cases e), fun _ _ => ⟨rfl, rfl⟩⟩
  | exhausted m => exact ⟨dm, inv_reject D fuel items k hk dm h (fun st' e => by rw [hv] at e; cases e), fun _ _ => ⟨rfl, rfl⟩⟩
  | ok u st' =>
  cases u
  cases hit : items[k] with
  | defn d => exact ⟨dm, inv_defn D fuel items hIF hN hpre k hk dm h st' d hv hit, fun _ _ => ⟨rfl, rfl⟩⟩
  | ind d0 =>
  have hv' := hv
  rw [verdict_eq D fuel items dm k hk] at hv'
  obtain ⟨d', hI, hchk, hpar0, hctor0, hgl⟩ := (hIF _ _ _ _ hv').1 d0 hit
  have hI' : st'.inds = (stage D fuel items dm k).inds ++ [d'] := hI
  have hgl' : st'.globals = (stage D fuel items dm k).globals := hgl
  have hPi : (stage D fuel items dm k).inds = indsOf {} fuel (items.take k) := stage_inds D fuel items dm k
  have hmem : Item.ind d0 ∈ items := by rw [← hit]; exact List.getElem_mem hk
  have hnv : Knot.FieldsNoVal d' := fieldsNoVal_of_ctors hctor0 (hNV d0 hmem).1
  have hpnv : ParamsNoVal d' := paramsNoVal_of_params hpar0 (hNV d0 hmem).2
  have hfree : Records.VaryValFree d' := hVV k hk st' d0 d' hv hit (by rw [hI', hPi])
  have hfresh : d' ∉ (stage D fuel items dm k).inds := fun hm => by
    have := List.find?_eq_none.1 hchk.fresh d' hm
    simp at this
  have hΓp : (stage D fuel items dm k).inds ++ [d'] <+: indsOf {} fuel items := by
    have := hpre (k + 1) (by omega)
    rw [← stage_inds D fuel items dm (k + 1), stage_ok D fuel items dm k hk st' hv] at this
    rw [← hI']; exact this
  obtain ⟨rest, hrest⟩ := hΓp
  have hΓ : indsOf {} fuel items = (stage D fuel items dm k).inds ++ d' :: rest := by
    rw [← hrest]; simp
  have hval0 : ∀ M ∈ (stage D fuel items dm k).inds, ∀ j, Knot.nestOf M j = true → M.paramIsType j = true :=
    fun M hM => h.val M (hPi ▸ hM)
  obtain ⟨hgram, hpgram, hval', htop⟩ := Knot.grammar_of_checks hchk hnv hval0 rest
  rw [← hΓ] at hgram hpgram htop
  let K1 := ctx1 D fuel items dm k st' d'
  have hK1Γ : K1.Γ = indsOf {} fuel items := rfl
  have hdΓ : d' ∈ K1.Γ := by rw [hK1Γ, hΓ]; simp
  have hK1pt : K1.dm.paramTy d' = ptyAt D fuel items dm k st' d' := by simp [K1, ctx1, ProgState.ctx, setPty]
  have hK1rec : ∀ M, K1.dm.recOf M = dm.recOf M := fun M => rfl
  have hpty : ParamTyLocalD K1.dm d' := by
    intro j ps ps' h1 h2 h3 h4
    rw [hK1pt]
    exact Params.pty_local _ _ _ j ps ps' h1 h2 h3 h4
  have hD : FrameLocal.DecLocal K1.D := hDL st'
  have hK : ∀ g, (K1.C.global g).2.label = none := stage_label D fuel items dm k (by omega)
  have hTyP : ∀ j qs, d'.paramIsType j = true → ∀ (A : Type) (c : Code0 A) (v : Sem), K1.dm.paramTy d' j qs = .t0 A c →
      ¬ v ∈ₛ[K1.dm.read] .t0 A c := fun j qs hj A c v hT => by
    rw [hK1pt] at hT
    exact Params.pty_type (ctx0 D fuel items dm k st') (fun _ => .err) d' j qs hj A c v hT
  -- the field types' level (`FieldLevel.fieldLevel0_of`): the grammar's top shapes, the heads' levels
  -- from the checker (`FieldHeads`), the globals' calls from the model (`GlobalCallLevels`)
  have hheads := hFH k hk st' d0 d' hv hit (by rw [hI', hPi])
  have hTop : ∀ c i FT, fieldTerm d' c i = some FT → FieldLevel.Top d' FT := fun c i FT hFT => by
    by_cases hs : d'.sort = 0
    · exact FieldLevel.top_of_pspine (Knot.pspineB_sound (hpgram hs c i FT hFT))
    · exact FieldLevel.top_of_spine (Knot.spineB_sound (hgram hs c i FT hFT))
  have hFL0 : ∀ (dm'' : DataModel) (ρ : Assignment),
      ParamsFaithfulAt ((stage D fuel items dm k).ctx dm'' D (indsOf {} fuel items) st') ρ d' →
      FieldLevel.FieldLevel0 ((stage D fuel items dm k).ctx dm'' D (indsOf {} fuel items) st') ρ d' :=
    fun dm'' ρ hPF => FieldLevel.fieldLevel0_of _ ρ d' hTop hheads.1 (fun c i f as hd hFT => by
      obtain ⟨cs, hs', ds, l, rd, hl, hty⟩ := hheads.2 c i f as hd hFT
      exact hGC dm k (by omega) f cs hs' ds l rd hl (by rw [← hgl']; exact hty) dm'') hPF
  by_cases hs : d'.sort = 0
  · -- a `Prop`-sorted declaration: the truth spec
    have hpspine : ∀ c i FT, fieldTerm d' c i = some FT → Knot.PSpine K1.Γ d' c FT :=
      fun c i FT hFT => Knot.pspineB_sound (hpgram hs c i FT hFT)
    have hmono : ∀ M ∈ K1.Γ, M ≠ d' → M.sort = 0 → ∀ qs qs', PropLe M qs qs' → ∀ c i es, es.length = i →
        ShapeLe (uShape M (K1.dm.recOf M qs) c i es) (uShape M (K1.dm.recOf M qs') c i es) := by
      intro M hM hMd hMs qs qs' hq c i es hes
      show ShapeLe (uShape M (dm.recOf M qs) c i es) (uShape M (dm.recOf M qs') c i es)
      by_cases hMP : M ∈ indsOf {} fuel (items.take k)
      · exact h.mono M hMP hMs qs qs' hq c i es hes
      · rw [(h.rest M hMP).1]; exact .inl rfl
    let G : Knot.TruthHyp K1 d' := ⟨hs, hdΓ, hpspine, hmono, hpty⟩
    let T := Knot.truthP K1 (fun _ => .err) d'
    refine inv_ind_core D fuel items hIF hN hDL hDS hpre k hk dm h st' d0 d' hv hit hI' hgl' hfresh hpnv hnv hFL0
      (Knot.truthSpec K1 (fun _ => .err) d' T) (Records.recCanonP K1 (fun _ => .err) d' T)
      (Knot.truth_agree K1 (fun _ => .err) d' G (Knot.steadyAt_spec K1 (fun _ => .err) d' _ hD hK)) ?_ ?_
      (fun hs' => absurd hs hs') ?_ hval'
    · intro ps hps
      show recK _ (Records.canonPs _ _ _ ps) = _
      rw [Records.canonPs_typed _ _ _ ps hps]
    · intro K hrec hpt
      exact Records.recordsFaithful_canonP K1 (fun _ => .err) d' T hdΓ hpspine hpty hTyP hfree K hrec (hpt.trans hK1pt.symm)
    · intro _ ps ps' hp c i es hes
      exact Records.mono_canonP K1 (fun _ => .err) d' T hpty (fun _ _ hq => Knot.truthRec_mono G hq) ps ps' hp c i es hes
  · -- a data-sorted declaration: the knot
    have hspine : ∀ c i FT, fieldTerm d' c i = some FT → Knot.Spine K1.Γ d' c FT :=
      fun c i FT hFT => Knot.spineB_sound (hgram hs c i FT hFT)
    have hpar : Knot.ParHyp K1 d' := by
      refine ⟨fun M hM hMd hMs n => ?_, htop hs⟩
      show RAgree _ n (dm.recOf M) (dm.recOf M)
      by_cases hMP : M ∈ indsOf {} fuel (items.take k)
      · exact h.par M hMP hMs n
      · rw [(h.rest M hMP).1]; intro ps ps' _ q _; rfl
    refine inv_ind_core D fuel items hIF hN hDL hDS hpre k hk dm h st' d0 d' hv hit hI' hgl' hfresh hpnv hnv hFL0
      (Knot.knotK K1 (fun _ => .err) d' hs hdΓ hspine hpar hpty) (Records.recCanon K1 (fun _ => .err) d' hs hdΓ hspine hpar hpty)
      (Knot.knotK_agree K1 (fun _ => .err) d' hs hdΓ hspine hpar hpty
        (Knot.steadyAt_knotK K1 (fun _ => .err) d' hs hdΓ hspine hpar hpty hD hK)) ?_ ?_
      (fun _ n => Records.par_canon K1 (fun _ => .err) d' hs hdΓ hspine hpar hpty n) (fun hs' => absurd hs' hs) hval'
    · intro ps hps
      show recK _ (Records.canonPs _ _ _ ps) = _
      rw [Records.canonPs_typed _ _ _ ps hps]
    · intro K hrec hpt
      exact Records.recordsFaithful_canon K1 (fun _ => .err) d' hs hdΓ hspine hpar hpty hTyP hfree K hrec
        (hpt.trans hK1pt.symm)

theorem inv_all (hIF : ItemFacts) (hNV : NoValFact items) (hVV : VaryValFact fuel items) (hN : NamesFact D fuel items) (hFH : FieldHeads fuel items) (hGC : GlobalCallLevels D fuel items)
    (hDL : ∀ st, FrameLocal.DecLocal (D st)) (hDS : DecStable D fuel items)
    (hpre : ∀ k, k ≤ items.length → indsOf {} fuel (items.take k) <+: indsOf {} fuel items) :
    ∀ k, k ≤ items.length → ∃ dm, Inv D fuel items k dm
  | 0, _ => ⟨_, inv_zero D fuel items⟩
  | k + 1, hk => by
    obtain ⟨dm, h⟩ := inv_all hIF hNV hVV hN hFH hGC hDL hDS hpre k (by omega)
    obtain ⟨dm', h', -⟩ := inv_step D fuel items hIF hNV hVV hN hFH hGC hDL hDS hpre k (by omega) dm h
    exact ⟨dm', h'⟩

/-- `exists_dataModel`, from the step (and the prefix fact `hpre`). -/
theorem exists_dataModel' (hIF : ItemFacts) (hNV : NoValFact items) (hVV : VaryValFact fuel items) (hN : NamesFact D fuel items) (hFH : FieldHeads fuel items) (hGC : GlobalCallLevels D fuel items)
    (hDL : ∀ st, FrameLocal.DecLocal (D st)) (hDS : DecStable D fuel items)
    (hpre : ∀ k, k ≤ items.length → indsOf {} fuel (items.take k) <+: indsOf {} fuel items) :
    ∃ dm : DataModel,
      (progMeaning dm D (indsOf {} fuel items) (fun _ => .err) {} fuel items).Covered dm ∧
      ∀ k, k ≤ items.length → DataFaithfulU dm D (indsOf {} fuel items)
        (progMeaning dm D (indsOf {} fuel items) (fun _ => .err) {} fuel (items.take k)) := by
  obtain ⟨dm, h⟩ := inv_all D fuel items hIF hNV hVV hN hFH hGC hDL hDS hpre items.length (Nat.le_refl _)
  exact ⟨dm, exists_of_inv D fuel items h hpre⟩

/-- **The data model exists**, from the facts it rests on (`DataFacts`), the items' having no
embedded value (`NoValFact`, true of a resolved program: `Consistency.noValFact_of_resolvesTo`) and
`DecLocal` but its `caps` part (`DecLocal3`, true of the chain's decisions:
`Steps.Machine.decLocal_inv_chain`, `decLocal_join_chain`, `decLocal_rep_chain`); the stage prefix fact
is machine10's PROVED `Steps.Machine.indsOf_take_prefix`. -/
theorem exists_dataModel_facts (hNV : NoValFact items) (hDL : ∀ st, DecLocal3 (D st)) (hF : DataFacts D fuel items) :
    ∃ dm : DataModel,
      (progMeaning dm D (indsOf {} fuel items) (fun _ => .err) {} fuel items).Covered dm ∧
      ∀ k, k ≤ items.length → DataFaithfulU dm D (indsOf {} fuel items)
        (progMeaning dm D (indsOf {} fuel items) (fun _ => .err) {} fuel (items.take k)) :=
  exists_dataModel' D fuel items itemFacts hNV hF.varyVal hF.names (fieldHeads fuel items) (globalCallLevels D fuel items)
    (fun st => ⟨(hDL st).1, (hDL st).2.1, (hDL st).2.2, hF.decCaps st⟩) hF.decStable
    (fun k _ => Steps.Machine.indsOf_take_prefix {} fuel items k)

end

/-! ## The statement at ONE declaration list (the lead's ruling, 2026-11-22)

Built (docs/31 D174): `Assembly.DataFaithful` (`Consistency.lean`) IS the one-list statement that stood
here as `DataFaithfulOne` (at the whole program's list `Γ`, faithfulness for the stage's declarations
only, `DeclsFaithful`), and `Assembly.exists_dataModel` is stated at `indsOf {} fuel items`, the list
`ExistsDataModelOne` named; both definitions are deleted. -/

end Ochr.Meaning.DataModel.Exists.Assembly
