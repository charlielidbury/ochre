import Ochr.Meaning.Program
import Ochr.Meaning.Bounded
import Ochr.Meaning.Steps.Tail
import Ochr.Meaning.Steps.Knot
import Ochr.Meaning.Steps.FixKnot
import Ochr.Meaning.DecisionsFF

/-!
# Milestone 4: the assembly of `consistencyBounded` (docs/18 Corollaries 15 and 16)

The chain, each link a statement here; `consistencyBounded_assembled`, `consistency_rel`,
`defn_member` and `step_member` are assembled with no `sorry` in their bodies (docs/31 D72), from
the leaves below and the step lemmas (`Steps/*.lean`). Writing them found the knot of [Def]
(`step_member_fix`, `Regress/DefKnot.lean`):
1. **Acceptance resolves.** `Accepted (Prelude.decls ++ q) fuel` means every declaration resolves
   to an item (`Run.checkProgram`'s first loop) and `checkDefs` gives each item `accepted`; so
   the items are checked in order from the Σ of the earlier ones, exactly as `progMeaning`
   steps through them (`Program.progMeaning_sig`).
2. **Every accepted definition means an element of its type** (`defn_member`): by induction on
   the items, an accepted function's closure is a member of its Π-type (`step_member_fix`, the knot)
   and an accepted constant's value a member of its goal (`checkConst_sound`), under the globals'
   meanings so far; the data model covers every accepted declaration (`checkInd_sound`).
3. **`False` means the empty proposition**: the library's `False` has no constructors, so it has
   no member and `tyM` gives `prop False` (`false_means_empty`, from the data model's library:
   membership is the least set closed under the constructors, docs/34 §14).
4. **Consistency**: a parameterless definition of type `False` would mean a member of `prop
   False`, that is, a proof of `False` (`Sem.mem proof (prop P) = P`); so there is none.
A data model covering and faithful to every accepted program exists (`exists_dataModel`, docs/34),
which turns the relative statement into `consistencyBounded`.

What the assembly covers as the run stands (docs/31 D12): definitions whose Π-type is in `Type₀`
or `Prop`; polymorphic definitions wait on the level-1 construction.
-/

namespace Ochr.Meaning.Assembly

open Ochr.Meaning Ochr.Surface Ochr.Consistency

section
variable (dm : DataModel) (D : MState → Decisions) (Γ : List IndDecl)

/-- **The data model is faithful to the program** (a named hypothesis of the chain, docs/31 D72,
docs/34 §9): at every checker state over the program's declarations whose globals extend the
program's (the state a definition's check ends in), the run context's data model reads the
declared field types, parameter types and records as the run does (`CtxFaithful`, what `CtxOk`
carries). Before docs/34's port the existence statement asked only `covers`, and a model ignoring
the program met it (`DataModel/Counterexamples.degenerate_meets`, against the frozen copy); that
model is not faithful (`DataModel/Degenerate.lean`). The globals are restricted because the
decisions read them: a field type calling a global is run under the decisions at the state.

At ONE declaration list (the lead's ruling, docs/31 D174, docs/34 §18.13): the context's list `Γ` is
the whole program's at every stage, and faithfulness is asked only for the stage's declarations
(`DeclsFaithful`; a later declaration's field types may call globals the stage does not have yet).
This is `DataModel/Exists/Assembly.lean`'s `DataFaithfulOne`, which it replaces. -/
def DataFaithful (P : ProgState) : Prop :=
  ∀ st : MState, st.inds = P.inds → P.globals <+: st.globals → DeclsFaithful (P.ctx dm D Γ st) P.inds

/-- Every accepted definition so far means a member of its type. -/
def MeansMember (P : ProgState) : Prop := ∀ n s T, (n, s, T) ∈ P.means → s ∈ₛ[dm.read] T.m

/-- The item `it` is accepted from the Σ of `P` (`checkDefs`' verdict boundary). -/
def ItemAccepted (fuel : Nat) (P : ProgState) (it : Item) : Prop :=
  (runMachine (checkItem it) { globals := P.globals, inds := P.inds } fuel).1 matches .ok () _

/-- **A constant's check taken apart** (leaf): `checkDef`'s constant branch, the environment reset to
one empty frame, the goal evaluated, then the body evaluated typed at the goal, then [Return]
(`bodyReturns`), then the global stored at the goal. At the body's start the state is good and meets
the context's conditions under the program's context so far (Σ's globals are members: the chain's
induction, `hP`; the data model covering and faithful), and it is related to the empty state at its
counter (`Steps.Rel.start`: it holds no borrow), out of tail position. -/
theorem const_split (fuel : Nat) (P : ProgState) (d : Def) (st' : MState) (hd : d.doms = [])
    (hP : MeansMember dm P) (hΓ : st'.inds <+: Γ) (hcov : ∀ d' ∈ Γ, dm.covers d') (hfaith : DataFaithful dm D Γ P) (hDec : ∀ st, Steps.DecAligned (D st) st)
    (hrun : (runMachine (checkItem (.defn d)) { globals := P.globals, inds := P.inds } fuel).1 = .ok () st') :
    ∃ (f : Nat) (st₁ st₂ st₃ : MState) (b₁ b₂ : Nat) (goal v : Value) (T? : Option Value),
      Good dm (P.ctx dm D Γ st').M (P.ctx dm D Γ st').Γ (fun _ => .err) st₁ ∧ Steps.CtxOk (P.ctx dm D Γ st') (fun _ => .err) st₁ ∧
      Steps.Rel (P.ctx dm D Γ st') (fun _ => .err) noFuture id st₁ (emptyState st₁.nextLoan) ∧ st₁.tailNext = false ∧
      Steps.Runs (Ochr.eval f true d.body (some goal)) st₁ b₁ (v, T?) st₂ ∧
      -- the item's final decisions are aligned after the body (the tables only grow to the end)
      Steps.DecTab (P.ctx dm D Γ st').D st₂ ∧
      Steps.Runs (Ochr.bodyReturns f s!"{d.name} is defined as it" v goal [] "") st₂ b₂ () st₃ ∧
      ((st'.globals.find? (·.name == d.name)).map (·.ty)).getD .bot = goal := by
  sorry

/-- The typing constraints on each label have a common member: a whole member of every type a typed
holder of the label and every flight entry for it gives. -/
def LabelsInhabited (K : RunCtx) (ρ : Assignment) (st : MState) (fl : Flight) : Prop :=
  ∀ l, ∃ x : Sem, (∀ p T, Env.shape st.env p = some l → MState.posTyM K.dm K.M K.Γ ρ st p = some T → x ∈ₛ[K.dm.read] T) ∧
    ∀ T, (l, T) ∈ fl → x ∈ₛ[K.dm.read] T

/-- **A typed future exists where each label's constraints are inhabited** (proved). As first stated
it assumed only `GoodF`, which holds vacuously when a constraint is empty: FALSE
(`Regress/OpenFalse.typedFutureF_exists_false`, a flight typing a label at `False`). At its use the
inhabitants are the reference's records (`labelsInhabited_of_rel`). -/
theorem typedFutureF_exists (K : RunCtx) (ρ : Assignment) (st : MState) (fl : Flight)
    (hinh : LabelsInhabited K ρ st fl) : ∃ ψ, TypedFutureF K.dm K.M K.Γ ρ st fl ψ :=
  ⟨fun l => (hinh l).choose, fun p l hl T hT => ((hinh l).choose_spec.1 p T hl hT),
    fun l T h => (hinh l).choose_spec.2 T h⟩

/-- (leaf) **At a related state, each label's constraints are inhabited by the reference's record**
(`Rel.records`: every live label's record is a whole member of its holder's content type), given that
the flight types a label at its holder's type. To be restated with typed temporaries (D81), where the
flight goes and the holders' types are the checker's. -/
theorem labelsInhabited_of_rel (K : RunCtx) (ρ : Assignment) (φ : Future) (π : Nat → Nat) (st : MState)
    (s : SState) (fl : Flight) (hs : Steps.Rel K ρ φ π st s) (hg : GoodF K.dm K.M K.Γ ρ st fl) :
    LabelsInhabited K ρ st fl := by
  sorry

/-- **The constant's meaning is the checker's value's** (leaf): the reference's run of the body from
the empty state at the counter `0` and the constant future (`defMeaning`) is the run the step lemma
compared (from the empty state at the checker's counter, `FrameProp.run_counter_indep`; under the
extended assignment, which the closed body does not read, `run_abs_congr`; at a future the value
does not read once [Return] ended its borrows), at the goal (`hintM` is `globalTyS` at the stored
type), and at a proposition it is `•` (`constMean`): so the membership [Return] gives is the
definition's. -/
theorem const_value (fuel : Nat) (P : ProgState) (d : Def) (st' st₁ : MState) (goal v : Value) (hd : d.doms = [])
    (hgoal : ((st'.globals.find? (·.name == d.name)).map (·.ty)).getD .bot = goal)
    (ρ' : Assignment) (Δ' : Nat → TyS) (π' : Nat → Nat) (r : Res) (s₂ : SState)
    (hrun : runT (P.ctx dm D Γ st') ρ' noFuture false (Steps.hintM (P.ctx dm D Γ st') (fun _ => .err) (some goal)) d.body
      (emptyState st₁.nextLoan) = some (r, s₂))
    (hmean : meanV { P.ctx dm D Γ st' with Δ := Δ' } ρ' (fun l => noFuture (π' l)) r.2 v = r.1) (ψ : Future)
    (hmem : meanV { P.ctx dm D Γ st' with Δ := Δ' } ρ' ψ (Value.tyS dm ({ P.ctx dm D Γ st' with Δ := Δ' } : RunCtx).M
        (P.ctx dm D Γ st').Γ ρ' goal) v ∈ₛ[dm.read]
      (meanV { P.ctx dm D Γ st' with Δ := Δ' } ρ' noFuture (.plain .err) goal).asTy) :
    ∃ m, defMeaning (fun _ => .err) (P.ctx dm D Γ st') d goal = some m ∧ m.1 ∈ₛ[dm.read] m.2.m := by
  sorry

/-- **An accepted constant means a member of its type** (assembled): the check taken apart
(`const_split`), the body by the step lemma (`eval_step`, from the start related to the empty state),
[Return]'s membership (`bodyReturns_sound`, in the extended context, the value in flight), the
constant's meaning that value's (`const_value`). -/
theorem step_member_const (fuel : Nat) (P : ProgState) (d : Def) (st' : MState) (hd : d.doms = [])
    (hP : MeansMember dm P) (hΓ : st'.inds <+: Γ) (hcov : ∀ d' ∈ Γ, dm.covers d') (hfaith : DataFaithful dm D Γ P) (hDec : ∀ st, Steps.DecAligned (D st) st)
    (hrun : (runMachine (checkItem (.defn d)) { globals := P.globals, inds := P.inds } fuel).1 = .ok () st') :
    ∃ m, defMeaning (fun _ => .err) (P.ctx dm D Γ st') d
        (((st'.globals.find? (·.name == d.name)).map (·.ty)).getD .bot) = some m ∧ m.1 ∈ₛ[dm.read] m.2.m := by
  obtain ⟨f, st₁, st₂, st₃, b₁, b₂, goal, v, T?, hg₁, hctx₁, hs₁, htl, hev, hD₂, hbr, hgoal⟩ :=
    const_split dm D Γ fuel P d st' hd hP hΓ hcov hfaith hDec hrun
  obtain ⟨ρ', Δ', π', -, -, -, -, r, s₂, hrunr, hmean, -, hctx₂, hs₂, hg₂⟩ :=
    (Steps.stepsIH f (P.ctx dm D Γ st') (fun _ => .err) noFuture).eval_step st₁ st₂ true d.body (some goal) v T? hg₁
      hctx₁ _ id hs₁ (fun h => absurd h (by decide)) hD₂ b₁ hev
  rw [htl] at hrunr
  obtain ⟨ψ, hψ⟩ := typedFutureF_exists { P.ctx dm D Γ st' with Δ := Δ' } ρ' _ _
    (labelsInhabited_of_rel _ ρ' noFuture π' _ s₂ _ hs₂ hg₂)
  have hmem := ((Steps.stepsIH f { P.ctx dm D Γ st' with Δ := Δ' } ρ' ψ).bodyReturns_sound st₂ st₃ _ v goal [] ""
    (Steps.flightOf r.2) hg₂ hctx₂ b₂ hbr hψ).1
  rw [hgoal]
  exact const_value dm D Γ fuel P d st' st₁ goal v hd hgoal ρ' Δ' π' r s₂ hrunr hmean ψ hmem

/-- (leaf, OPEN; to be routed: the function-type case of sort soundness) **An accepted definition's
function type obeys the sort rule, as the model reads its parts** (`Steps.SortRule`), at the decided
sort of its Π-term (`D.piSort`, aligned with the checker's `Machine.piSort`, `piSort_aligned_stmt`)
and the run's reading of its domains and codomain (`runDoms`, `codOf`; what `run_fix_def` builds the
closure along): the sort is at most `3`; at sort `0` the codomain is not a returned borrow and is a
proposition (level `0`) at every member argument tuple; at a data sort the levels of the codomain and
of every domain are at most the sort. `fix_split` gives `PiFits` from it and `fix_canon`
(`Steps.piFits_of_rules`), and its step's `MemBelow` gives `PiCallable` the same way.

Stronger than `sortOf_sound_stmt` as stated: that equates the level of a whole stored type with the
checker's `sortOf` of it, so of the Π-type it gives only the Π's own level (`piTyAt_level`; with
`le_three_of_piTyAt_level`, the bound `3` when the stored Π-type has a level). The components' part
follows from `sortOf_sound_stmt` at the body's generic state (the parameters' types and the goal are
stored types there, and the run's reading of the domain and codomain terms at the arguments is their
meaning) together with a fact of the checker alone: `Machine.piSort` is at least the `sortOf` of
each domain and of the codomain at a data sort, and is `0` only for a codomain of sort `0` that is
not a borrow type (`Machine.piSort`: `if lb == 0 then 0 else max l lb`, a borrow type being of sort
`1`). One point to check when routing: a borrow parameter `&A` counts at `sortOf (&A) = 1`, while the
model reads its content `A`, so the rule needs `A` of level at most `1` ((WF7)). -/
theorem fix_sortRule (fuel : Nat) (P : ProgState) (d : Def) (st' : MState) (hd : d.doms ≠ [])
    (hP : MeansMember dm P) (hΓ : st'.inds <+: Γ) (hcov : ∀ d' ∈ Γ, dm.covers d') (hfaith : DataFaithful dm D Γ P) (hDec : ∀ st, Steps.DecAligned (D st) st)
    (hrun : (runMachine (checkItem (.defn d)) { globals := P.globals, inds := P.inds } fuel).1 = .ok () st') :
    Steps.SortRule dm.read ((P.ctx dm D Γ st').D.piSort (scopeOf (emptyState 0)) (.pi d.hs d.doms d.cod))
      (runDoms (P.ctx dm D Γ st') (fun _ => .err) noFuture (emptyState 0) d.doms)
      (codOf (P.ctx dm D Γ st') (fun _ => .err) noFuture (emptyState 0)
        (bindsOf (P.ctx dm D Γ st') (fun _ => .err) noFuture (emptyState 0) d.doms) d.cod) := by
  sorry

/-- (leaf, OPEN) **The parts of an accepted definition's function type are canonical codes**
(`Steps.CanonRule`: no lifted code at the top, where `toTy ∘ codeOf` would not give the type back).
An instance of an invariant of the run: every type value it produces is canonical (the model's
constructors are; a member of a universe is, `mem_univ_canon`, which covers the arguments a type
parameter is read at; a call's type result is encoded at its universe's code). Not small: it is an
induction over the run, as `RunPresInd` is. -/
theorem fix_canon (fuel : Nat) (P : ProgState) (d : Def) (st' : MState) (hd : d.doms ≠ [])
    (hP : MeansMember dm P) (hΓ : st'.inds <+: Γ) (hcov : ∀ d' ∈ Γ, dm.covers d') (hfaith : DataFaithful dm D Γ P) (hDec : ∀ st, Steps.DecAligned (D st) st)
    (hrun : (runMachine (checkItem (.defn d)) { globals := P.globals, inds := P.inds } fuel).1 = .ok () st') :
    Steps.CanonRule dm.read (runDoms (P.ctx dm D Γ st') (fun _ => .err) noFuture (emptyState 0) d.doms)
      (codOf (P.ctx dm D Γ st') (fun _ => .err) noFuture (emptyState 0)
        (bindsOf (P.ctx dm D Γ st') (fun _ => .err) noFuture (emptyState 0) d.doms) d.cod) := by
  sorry

/-- **`checkDef`'s function branch, taken apart** (leaf; docs/31 D73, D79). Two halves.
(1) The meaning. The reference runs the definition's `fix` term from the empty state (`run_fix_def`;
neither a statement nor a proof, by the aligned flags): the closure built along the code
`piTyAt l ds out`, at the declared sort `l ≤ 3`, of its function, the guarded fixpoint by stages
(`fixG`: at arguments of rank `r`, the stage `r + 1`, `fixStage`, the rank `fixRank`; a non-recursive
function is the stage `1` at rank `0`, its `self` the weakened stage `0`, never read; docs/31 D113); and the stored type's code is
that code (the checker stores `Π(x̄ : Ā). B`, which the `fix` term's domains and codomain run to).
(2) The function type fits its sort (`Steps.PiFits` at every member argument: at sort `0` a
borrow-free codomain that is a proposition, at a data sort `l ≤ 3` a codomain that fits the level):
`Steps.piFits_of_rules` from the sort rule (`fix_sortRule`, open, to be routed) and canonical codes
(`fix_canon`, open), `l`, `ds`, `out` being the run's reading of the definition's Π-term.
(3) The step of the induction on the bound, in the run's shape: from stage `b` good below `b`,
stage `b + 1` is good below `b + 1` (`Steps.OutGood'`: the result a member of the codomain, the
borrow parameters' final contents members, one per borrow parameter, and at a returned borrow its
label and an injective backward function). Its proof is the checker's run of the body (`checkFix`)
read through the step statements under the context that names the definition at the bound
(`RunCtx.cur := (f, b)`) and gives its global the meaning of the run's own `self` at stage `b + 1`:
stage `b`'s closure at the weakened function type (`RunCongr.fixStage`; so the checker's `self`,
`.gfn f`, and the reference's frame's `self` mean the same at the generic state), where `CtxOk` asks
of the global only `MemBelow b` with the function the stage `b`, which the hypothesis gives (no
stage stability: a self call below the bound reads stage `b` itself, `Steps.memBelow_apply`).
Then: the generic state good for the assignment giving each parameter its argument
(`generic_good`) and related to the body's frame (`Rel.start`, the frame property, D70);
`checkTail_step` along the case tree to a leaf; the leaf's value is stage `b + 1` at the arguments,
and its membership in the codomain (with the borrow parameters' final contents, the frame's pop at
`fixReturn`) is `OutGood'`. (The return check's statement, `bodyReturns_step_stmt`, is being
restated: the membership of a body's value is to come from the evaluation step; this leaf is the
knot's one reader of it.) The one place the context's meaning of a global differs from
`defMeaning`'s: inside this step, the global means the stage-`b` closure at the weakened type (D79). -/
theorem fix_split (fuel : Nat) (P : ProgState) (d : Def) (st' : MState) (hd : d.doms ≠ [])
    (hP : MeansMember dm P) (hΓ : st'.inds <+: Γ) (hcov : ∀ d' ∈ Γ, dm.covers d') (hfaith : DataFaithful dm D Γ P) (hDec : ∀ st, Steps.DecAligned (D st) st)
    (hrun : (runMachine (checkItem (.defn d)) { globals := P.globals, inds := P.inds } fuel).1 = .ok () st') :
    ∃ (l : Nat) (ds : List PiDom) (out : PiCod) (stage : Nat → List Sem → Option BodyOut) (rank : List Sem → Nat),
      Steps.PiFits dm.read l ds out (fun _ => True) ∧
      defMeaning (fun _ => .err) (P.ctx dm D Γ st') d (((st'.globals.find? (·.name == d.name)).map (·.ty)).getD .bot)
        = some (closureAt dm.read l noFuture ds out (fun args => stage (rank args + 1) args),
            globalTyS (fun _ => .err) (P.ctx dm D Γ st') (((st'.globals.find? (·.name == d.name)).map (·.ty)).getD .bot)) ∧
      (globalTyS (fun _ => .err) (P.ctx dm D Γ st') (((st'.globals.find? (·.name == d.name)).map (·.ty)).getD .bot)).m
        = piTyAt dm.read l ds out ∧
      (∀ b, (∀ a, Steps.DomMembers dm.read ds a → rank a < b →
          ∃ o, stage b a = some o ∧ Steps.OutGood' dm.read ds out a o) →
        ∀ a, Steps.DomMembers dm.read ds a → rank a < b + 1 →
          ∃ o, stage (b + 1) a = some o ∧ Steps.OutGood' dm.read ds out a o) := by
  sorry

/-- **An accepted function means a member of its type** (assembled, no `sorry` in the body; THE KNOT,
docs/31 D72, D73, D79; docs/34): the branch taken apart (`fix_split`), the induction on the bound in
the run's shape (`Steps.stages_below`, proved) makes the guarded fixpoint good at every member
argument, and a closure whose function is total and good is a member of its code
(`Steps.closure_mem_of_total`, the data layer's; together `Steps.knot_member`). Not
`checkFix_sound`: `CtxOk` at the state it starts from asked the function to be a member of its type
(`Regress/DefKnot.ctx_contains_fix_member`); it now asks only membership below the bound
(`RunCtx.cur`, `MemBelow`). -/
theorem step_member_fix (fuel : Nat) (P : ProgState) (d : Def) (st' : MState) (hd : d.doms ≠ [])
    (hP : MeansMember dm P) (hΓ : st'.inds <+: Γ) (hcov : ∀ d' ∈ Γ, dm.covers d') (hfaith : DataFaithful dm D Γ P) (hDec : ∀ st, Steps.DecAligned (D st) st)
    (hrun : (runMachine (checkItem (.defn d)) { globals := P.globals, inds := P.inds } fuel).1 = .ok () st') :
    ∃ m, defMeaning (fun _ => .err) (P.ctx dm D Γ st') d
        (((st'.globals.find? (·.name == d.name)).map (·.ty)).getD .bot) = some m ∧ m.1 ∈ₛ[dm.read] m.2.m := by
  obtain ⟨l, ds, out, stage, rank, hfit, hdm, hA, hstep⟩ := fix_split dm D Γ fuel P d st' hd hP hΓ hcov hfaith hDec hrun
  refine ⟨_, hdm, ?_⟩
  show closureAt dm.read l noFuture ds out (fun args => stage (rank args + 1) args) ∈ₛ[dm.read] _
  rw [hA]
  exact Steps.knot_member dm.read l noFuture ds out stage rank hfit hstep

/-- **One item keeps every definition a member** (assembled): an inductive declaration adds no
definition; a definition's meaning is a member by `step_member_const` or `step_member_fix`. -/
theorem step_member (fuel : Nat) (P : ProgState) (it : Item) (hP : MeansMember dm P)
    (hacc : ItemAccepted fuel P it)
    (hcov : ∀ d' ∈ Γ, dm.covers d') (hΓ : (ProgState.step dm D Γ (fun _ => .err) {} fuel P it).inds <+: Γ)
    (hfaith : DataFaithful dm D Γ P) (hDec : ∀ st, Steps.DecAligned (D st) st) :
    MeansMember dm (ProgState.step dm D Γ (fun _ => .err) {} fuel P it) := by
  unfold ItemAccepted at hacc
  rcases hr : (runMachine (checkItem it) { globals := P.globals, inds := P.inds } fuel).1 with ⟨u, st'⟩ | f | e
  · cases u
    intro n s T hmem
    simp only [ProgState.step, hr] at hmem hΓ
    cases it with
    | ind d' => exact hP n s T hmem
    | defn d =>
      simp only [List.mem_append, List.mem_singleton] at hmem
      rcases hmem with hmem | hmem
      · exact hP n s T hmem
      · have hm : ∃ m, defMeaning (fun _ => .err) (P.ctx dm D Γ st') d
            (((st'.globals.find? (·.name == d.name)).map (·.ty)).getD .bot) = some m ∧ m.1 ∈ₛ[dm.read] m.2.m := by
          by_cases hd : d.doms = []
          · exact step_member_const dm D Γ fuel P d st' hd hP hΓ hcov hfaith hDec hr
          · exact step_member_fix dm D Γ fuel P d st' hd hP hΓ hcov hfaith hDec hr
        obtain ⟨m, hdm, hmm⟩ := hm
        rw [hdm] at hmem
        simp only [Option.getD_some, Prod.mk.injEq] at hmem
        obtain ⟨-, rfl, rfl⟩ := hmem
        exact hmm
  · rw [hr] at hacc; simp at hacc
  · rw [hr] at hacc; simp at hacc

/-- The items of a surface program, when every declaration resolves (`Run.checkProgram`'s first
loop, `runResolve`), in order. -/
def ResolvesTo (p : Program) (fuel : Nat) (items : List Item) : Prop :=
  items.length = p.length ∧
  ∀ (i : Nat) (d : SDecl) (it : Item), p[i]? = some d → items[i]? = some it →
    ∃ st, (runResolve p d fuel false).1 = .ok (.ok it) ∧ (runResolve p d fuel false).2 = st

/-- (1) An accepted program resolves to items each of which `checkDefs` accepts; and the state
each item is checked from is the Σ of the items before it. -/
theorem accepted_resolves (p : Program) (fuel : Nat) (acc : Accepted p fuel) :
    ∃ items, ResolvesTo p fuel items ∧
      ∀ (i : Nat) (it : Item), items[i]? = some it →
        let P := progMeaning dm D Γ (fun _ => .err) {} fuel (items.take i)
        (runMachine (checkItem it) { globals := P.globals, inds := P.inds } fuel).1 matches .ok () _ := by
  sorry


/-- (2) Every accepted definition's meaning is a member of its type, at the empty assignment
(assembled): by induction on the items, one item at a time (`step_member`), the data model
covering and faithful at each prefix. -/
theorem defn_member (items : List Item) (fuel : Nat)
    (hacc : ∀ (i : Nat) (it : Item), items[i]? = some it →
      ItemAccepted fuel (progMeaning dm D Γ (fun _ => .err) {} fuel (items.take i)) it)
    (hcov : ∀ d' ∈ Γ, dm.covers d')
    (hΓ : ∀ k, k ≤ items.length → (progMeaning dm D Γ (fun _ => .err) {} fuel (items.take k)).inds <+: Γ)
    (hfaith : ∀ k, k ≤ items.length → DataFaithful dm D Γ (progMeaning dm D Γ (fun _ => .err) {} fuel (items.take k)))
    (hDec : ∀ st, Steps.DecAligned (D st) st) :
    MeansMember dm (progMeaning dm D Γ (fun _ => .err) {} fuel items) := by
  have key : ∀ k, k ≤ items.length → MeansMember dm (progMeaning dm D Γ (fun _ => .err) {} fuel (items.take k)) := by
    intro k
    induction k with
    | zero => intro _ n s T h; simp [progMeaning, progMeaningFrom] at h
    | succ k ih =>
      intro hk
      have hk' : k < items.length := hk
      have htake : items.take (k + 1) = items.take k ++ [items[k]] := List.take_succ_eq_append_getElem hk'
      have hfold : progMeaning dm D Γ (fun _ => .err) {} fuel (items.take k ++ [items[k]]) =
          ProgState.step dm D Γ (fun _ => .err) {} fuel (progMeaning dm D Γ (fun _ => .err) {} fuel (items.take k)) items[k] := by
        unfold progMeaning progMeaningFrom; rw [List.foldl_append]; rfl
      have hc := hΓ (k + 1) hk
      rw [htake, hfold] at hc ⊢
      exact step_member dm D Γ fuel _ _ (ih (Nat.le_of_lt hk')) (hacc k items[k] (List.getElem?_eq_getElem hk')) hcov hc
        (hfaith k (Nat.le_of_lt hk')) hDec
  have := key items.length (Nat.le_refl _)
  rwa [List.take_length] at this

/-- (3) The library's `False` means the empty proposition: `tyM` of a `Prop`-sorted declaration is
the proposition that it has a member (`DataModel.tyR_prop`), and a declaration with no
constructors has none (`DataLib.mem_iff`: a member is a constructor applied to fields). -/
theorem false_means_empty (d : IndDecl) (hd : d.name = "False" ∧ d.ctors = [] ∧ d.sort = 0)
    (_hcov : dm.covers d) : dm.tyM d [] = .prop False := by
  unfold DataModel.tyM
  rw [DataModel.tyR_prop dm d _ (by simp [hd.2.2])]
  congr 1
  apply propext
  constructor
  · rintro ⟨v, hv⟩
    obtain ⟨⟨c, hc⟩, -⟩ := (DataLib.mem_iff dm.sig d _ v).1 hv
    rw [hd.2.1] at hc
    exact absurd hc (Nat.not_lt_zero _)
  · exact False.elim

/-- The stored type of a parameterless definition declared `: False` is the library's `False`
applied to nothing, once the library is in front (names are distinct: `Check.declared`). -/
theorem falseConst_ty (q : Program) (fuel : Nat) (items : List Item) (d : SDecl)
    (hres : ResolvesTo (Prelude.decls ++ q) fuel items) (hd : d ∈ q) (hf : d.IsFalseConst) :
    let P := progMeaning dm D Γ (fun _ => .err) {} fuel items
    ∃ s T, (d.name, s, T) ∈ P.means ∧ T.m = .prop False := by
  sorry

/-- (4) Consistency, relative to a data model covering the program, faithful to it, and the decisions
read from the checker (assembled): no accepted, hole-free, level-bounded program has a parameterless
definition of type `False`. Its meaning would be a member of `prop False`, a proof of `False`. -/
theorem consistency_rel (q : Program) (fuel : Nat)
    (holes : NoHoles q) (levels : LevelsBelow 2 q)
    (acc : Accepted (Prelude.decls ++ q) fuel)
    (hcov : ∀ d' ∈ Γ, dm.covers d')
    (hΓ : ∀ items, ResolvesTo (Prelude.decls ++ q) fuel items →
      ∀ k, k ≤ items.length → (progMeaning dm D Γ (fun _ => .err) {} fuel (items.take k)).inds <+: Γ)
    (hfaith : ∀ items, ResolvesTo (Prelude.decls ++ q) fuel items →
      ∀ k, k ≤ items.length → DataFaithful dm D Γ (progMeaning dm D Γ (fun _ => .err) {} fuel (items.take k)))
    (hDec : ∀ st, Steps.DecAligned (D st) st) :
    ∀ d ∈ q, ¬ d.IsFalseConst := by
  intro d hd hf
  obtain ⟨items, hres, hacc⟩ := accepted_resolves dm D Γ (Prelude.decls ++ q) fuel acc
  have hacc' : ∀ (i : Nat) (it : Item), items[i]? = some it →
      ItemAccepted fuel (progMeaning dm D Γ (fun _ => .err) {} fuel (items.take i)) it := hacc
  have hmem := defn_member dm D Γ items fuel hacc' hcov (hΓ items hres) (hfaith items hres) hDec
  obtain ⟨s, T, hin, hT⟩ := falseConst_ty dm D Γ q fuel items d hres hd hf
  have h := hmem _ s T hin
  rw [hT] at h
  obtain ⟨⟨a⟩, -⟩ := h
  exact a

end

/-- **A data model covering and faithful to every accepted program exists** (docs/34), under the
checker's decisions, read with no fuel (`DecisionsFF.chainDecisions`, docs/31 D84: the fixed-fuel
instance never met `DecTab`; an existential choice of decisions could make the runs faithfulness asks
for undefined, or align them with nothing). What a data model is since
docs/34's port: the program decides only which declarations it covers, the signature (each field's
shape at a record and the earlier fields read small), the record of a declaration at parameters and
the parameters' types; carriers, membership (the least set closed under the constructors), the
reading (a bijection onto the members, so whole: `DataModel.read_wholeFields`) and the rank (the
height of a meaning) are defined from that and their laws are the library's theorems
(`DataLib`). So the statement owes only `covers` and faithfulness (`DataFaithful`), which excludes
the degenerate model (`DataModel/Degenerate.lean`). The model relies on one property of the
checker, kept as an assumption of the construction, not a hypothesis here: the checker never
decides that two applications of a type former to different arguments are different (a record
keeps what field types read of the parameters, not the parameters; docs/34 §8, §13). -/
theorem exists_dataModel (items : List Item) (fuel : Nat) :
    ∃ dm : DataModel,
      (progMeaning dm (chainDecisions fuel) (indsOf {} fuel items) (fun _ => .err) {} fuel items).Covered dm ∧
      ∀ k, k ≤ items.length → DataFaithful dm (chainDecisions fuel) (indsOf {} fuel items)
        (progMeaning dm (chainDecisions fuel) (indsOf {} fuel items) (fun _ => .err) {} fuel (items.take k)) := by
  sorry

/-- (leaf, checker) **Every stage's declarations are a prefix of the whole program's** (docs/31 D174):
along accepted items Σ's inductive declarations only grow at the end (a definition adds none; a
declaration appends a placeholder and, accepted, replaces the entry of its own name, which names
being distinct is its own: `checkInd`, `Check.declared`). -/
theorem inds_prefix (p : Program) (fuel : Nat) (acc : Accepted p fuel) (items : List Item)
    (hres : ResolvesTo p fuel items) :
    ∀ k, k ≤ items.length → indsOf {} fuel (items.take k) <+: indsOf {} fuel items := by
  sorry

/-- (leaf, checker) An accepted program resolves: `checkProgram`'s first loop gives every
declaration an item. -/
theorem resolves_of_accepted (p : Program) (fuel : Nat) (acc : Accepted p fuel) :
    ∃ items, ResolvesTo p fuel items := by
  sorry

/-- (leaf, checker) Resolution is a function of the program: two resolutions are the same items. -/
theorem resolvesTo_unique (p : Program) (fuel : Nat) (items items' : List Item)
    (h : ResolvesTo p fuel items) (h' : ResolvesTo p fuel items') : items = items' := by
  sorry

/-- `consistencyBounded` from the relative statement and the existence of a data model. -/
theorem consistencyBounded_assembled (q : Program) (fuel : Nat)
    (holes : NoHoles q) (levels : LevelsBelow 2 q)
    (acc : Accepted (Prelude.decls ++ q) fuel) :
    ∀ d ∈ q, ¬ d.IsFalseConst := by
  obtain ⟨items, hres⟩ := resolves_of_accepted (Prelude.decls ++ q) fuel acc
  obtain ⟨dm, hcov, hfaith⟩ := exists_dataModel items fuel
  refine consistency_rel dm (chainDecisions fuel) (indsOf {} fuel items) q fuel holes levels acc
    (fun d' hd' => hcov d' (by rw [progMeaning_inds]; exact hd')) (fun items' h' => ?_) (fun items' h' => ?_)
    (chainDecisions_aligned fuel)
  · rw [resolvesTo_unique _ _ _ _ h' hres]
    intro k hk
    rw [progMeaning_inds]
    exact inds_prefix _ fuel acc items hres k hk
  · rw [resolvesTo_unique _ _ _ _ h' hres]; exact hfaith

end Ochr.Meaning.Assembly
