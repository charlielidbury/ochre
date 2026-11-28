import Ochr.Meaning.Steps.TopFix
import Ochr.Meaning.Steps.TopSorts

/-!
# `consistency_of_master`: the consistency statement from the 32 steps and named links (lead43; docs/31 D254)

The top assembled: the program-level induction (`Top.inv_all`) on the invariant `StageOk`, item by item; an
inductive declaration keeps it (`stageOk_ind`, PROVED); a constant's meaning is a member (`const_member`, from `EvalAt`);
a function's is (`fix_member`, the knot, from `TailAt`); each definition's `GlobalsOk` clauses at every later check come
from its own (`GlobGrowG`, consuming the knot's output `FnGoodAt`); at the end, the closed definition of `False` would
be a member of `False` (`FalseConstG`). The data model is `Assembly.exists_dataModel`'s (assuming `DataFacts`).
-/

namespace Ochr.Meaning.Steps.Form.Top

open Ochr Ochr.Meaning Ochr.Meaning.Steps Ochr.Meaning.Steps.Form Ochr.Meaning.Steps.Form.Master
open Ochr.Meaning.Steps.Form.FixEqDesc
open Ochr.Meaning.Assembly

section
variable {dm : DataModel} {D : MState → Decisions} {Γ : List IndDecl} {fuel : Nat}

/-- **An inductive declaration keeps the invariant** (PROVED): it adds no meaning and no global
(`Machine.checkItem_tables`), so every later check of the next stage is one of this stage's. -/
theorem stageOk_ind (P : ProgState) (d' : IndDecl) (st' : MState)
    (hr : (runMachine (checkItem (.ind d')) { globals := P.globals, inds := P.inds } fuel).1 = .ok () st')
    (hP : StageOk dm D Γ P) : StageOk dm D Γ (ProgState.step dm D Γ (fun _ => .err) {} fuel P (.ind d')) := by
  obtain ⟨hI, -⟩ := Steps.Machine.checkItem_tables (.ind d') _ st' fuel hr
  obtain ⟨hinds0, hglob0⟩ := hI d' rfl
  have hglob : st'.globals = P.globals := hglob0
  have hinds : P.inds <+: st'.inds := by rw [hinds0]; exact List.prefix_append _ _
  have hstep : ProgState.step dm D Γ (fun _ => .err) {} fuel P (.ind d') =
      { globals := st'.globals, inds := st'.inds, means := P.means } := by
    unfold ProgState.step; dsimp only; rw [hr]
  rw [hstep]
  refine ⟨hP.mem, hP.lab, fun e he => ?_, fun Dd cu hD hcu => ?_⟩
  · obtain ⟨g, hg, hn⟩ := hP.names e he; exact ⟨g, by rw [hglob]; exact hg, hn⟩
  obtain ⟨st, hDd, hg, hi⟩ := hD
  have hPD : LaterDec D P Dd := ⟨st, hDd, by rw [← hglob]; exact hg, hinds.trans hi⟩
  have h := hP.glob Dd cu hPD hcu
  rw [hglob]
  exact h

end

section
variable (dm : DataModel) (D : MState → Decisions) (Γ : List IndDecl) (fuel : Nat)

/-- **The context grows by the definition's meaning** (MIXED; PROVED for the constant of `def one : Nat := 1`,
`Top.One.globGrow_one`; for a function unread at any program but by reading at `R`, docs/31 D259: its `fixEq` part
computed there, its closure tools `Top.RT.closureAt_nat_congr` and `GG_R` proved, `ty`, `fn`, `accepted`, `retKind`
not assembled). After an accepted definition, every
global of the next stage meets `GlobalsOk`'s clauses at the context of every later check. Its parts: (i) the earlier
globals' clauses carry from this stage's contexts to the next's (one more global, the decisions of a later state): the
code runs alike there (the names an item mentions are the stage's, `NamesFact`; the decisions on a code are stable at
later states, as `DecStable` is for field types: UNREAD for definitions' code); (ii) the new global's clauses: `ty`,
`fn`, `mem`, `const` from its meaning (`defMeaning`, a member: `const_member`, `fix_member`) carried to every later
context by (i); for a function, `accepted` (its stored meaning is the closure every later context forms), `fixEq` (from
the knot's output `FnGoodAt`, HYPOTHESIS here, and the descent clause `RecDescG` at its code, READ TRUE as restated but
derived only through a second simulation of its check under two good selves, which needs `MemBelow` widened, D232),
`retKind` (R3: from the labels at its check's leaves), `codeValFree` (resolution builds no `.val`). -/
def GlobGrowG (items : List Item) : Prop :=
  ∀ (P : ProgState) (d : Def) (st' : MState), AtStage dm D Γ fuel items P (.defn d) →
    (runMachine (checkItem (.defn d)) { globals := P.globals, inds := P.inds } fuel).1 = .ok () st' →
    StageOk dm D Γ P → DataFaithful dm D Γ P → (∀ d' ∈ Γ, dm.covers d') → P.inds <+: Γ → MeansMember dm (ProgState.step dm D Γ (fun _ => .err) {} fuel P (.defn d)) →
    (d.doms ≠ [] → ∀ ρ φ, FnGoodAt (P.ctx dm D Γ st') ρ φ d.hs d.doms d.cod d.dec d.body) →
    ∀ (Dd : Decisions) (cu : Option (String × Nat × (Sem × TyS))),
      LaterDec D (ProgState.step dm D Γ (fun _ => .err) {} fuel P (.defn d)) Dd →
      (∀ x ∈ cu, (ProgState.step dm D Γ (fun _ => .err) {} fuel P (.defn d)).isGlobal x.1 = false) →
      GlobalsOk (ctxAt dm Γ (ProgState.step dm D Γ (fun _ => .err) {} fuel P (.defn d)) Dd cu)
        { globals := (ProgState.step dm D Γ (fun _ => .err) {} fuel P (.defn d)).globals }

/-- **The links of the top** (each a named fact with its class and status in its docstring). -/
structure TopLinks (items : List Item) : Prop where
  const : ConstG dm D Γ fuel items
  func : FixG dm D Γ fuel items
  globGrow : GlobGrowG dm D Γ fuel items

end


section
variable {dm : DataModel} {D : MState → Decisions} {Γ : List IndDecl} {fuel : Nat}

/-- **An accepted definition keeps the invariant** (assembled): its meaning a member (`const_member` or `fix_member`),
with no label (`defMeaning_label`), and its `GlobalsOk` clauses at every later check (`GlobGrowG`, given the knot's
output for a function). -/
theorem stageOk_defn
    (hsteps : ∀ (K : RunCtx) (φ : Future), (∀ Δ, Strict.FundCtx { K with Δ := Δ }) → AllSteps K φ)
    (hsorts : SortsG Γ) (items : List Item) (hL : TopLinks dm D Γ fuel items) (P : ProgState) (d : Def) (st' : MState)
    (hin : AtStage dm D Γ fuel items P (.defn d)) (hr : (runMachine (checkItem (.defn d)) { globals := P.globals, inds := P.inds } fuel).1 = .ok () st')
    (hP : StageOk dm D Γ P) (hfaith : DataFaithful dm D Γ P) (hcov : ∀ d' ∈ Γ, dm.covers d') (hΓP : P.inds <+: Γ) :
    StageOk dm D Γ (ProgState.step dm D Γ (fun _ => .err) {} fuel P (.defn d)) := by
  have hstep : ProgState.step dm D Γ (fun _ => .err) {} fuel P (.defn d) =
      { globals := st'.globals, inds := st'.inds,
        means := P.means ++ [(d.name, (defMeaning (fun _ => .err) (P.ctx dm D Γ st') d
          (((st'.globals.find? (·.name == d.name)).map (·.ty)).getD .bot)).getD (.err, .plain .err))] } := by
    unfold ProgState.step; dsimp only; rw [hr]
  -- the new meaning is a member, and the definition's own entry is Σ's last
  have hnew : (∃ m, defMeaning (fun _ => .err) (P.ctx dm D Γ st') d
      (((st'.globals.find? (·.name == d.name)).map (·.ty)).getD .bot) = some m ∧ m.1 ∈ₛ[dm.read] m.2.m) ∧
      (∃ g ∈ st'.globals, g.name = d.name) ∧
      (d.doms ≠ [] → ∀ ρ φ, FnGoodAt (P.ctx dm D Γ st') ρ φ d.hs d.doms d.cod d.dec d.body) := by
    by_cases hd : d.doms = []
    · obtain ⟨w, hck, hst, hlf, hmn⟩ := hL.const P d st' hin hd hr hP hfaith hcov hΓP
      obtain ⟨g, hg, hgn, -⟩ := hck.2.2.2.2.2.2.2.2.1
      refine ⟨const_member hsteps hsorts items hL.const P d st' hin hd hP hfaith hcov hΓP hr, ⟨g, by rw [hg]; simp, hgn⟩,
        fun h => absurd hd h⟩
    · obtain ⟨w, hck, hfit, hst, hcg, hlf, hpa, hcl, hfl⟩ := hL.func P d st' hin hd hr hP hfaith hcov hΓP
      have hmn := fixMeanAt_of dm D Γ P d st' hd hcl hpa hfl
      refine ⟨fix_member hsteps hsorts P d st' hP w hck hfit hst hcg hlf hmn,
        ⟨fnEntry d w.model, by rw [hck.2.2.2.2.2.2.2.2.1]; simp, rfl⟩,
        fun _ ρ φ => fnGoodAt_of_knot hsteps hsorts P d st' hP w hck hfit hst hcg hlf ρ φ⟩
  obtain ⟨⟨m, hdm, hmm⟩, ⟨g, hg, hgn⟩, hknot⟩ := hnew
  have hMM : MeansMember dm (ProgState.step dm D Γ (fun _ => .err) {} fuel P (.defn d)) := by
    rw [hstep]
    intro n s T hin
    simp only [List.mem_append, List.mem_singleton] at hin
    rcases hin with hin | hin
    · exact hP.mem n s T hin
    · rw [hdm, Option.getD_some] at hin
      obtain ⟨-, hm⟩ := Prod.mk.inj hin
      subst hm
      exact hmm
  have hgrow := hL.globGrow P d st' hin hr hP hfaith hcov hΓP hMM hknot
  rw [hstep] at hgrow hMM ⊢
  have hpre : P.globals <+: st'.globals := by
    obtain ⟨-, hD⟩ := Steps.Machine.checkItem_tables (.defn d) _ st' fuel hr
    obtain ⟨-, g', hg'⟩ := hD d rfl
    rw [show st'.globals = P.globals ++ [g'] from hg']; exact List.prefix_append _ _
  refine ⟨hMM, ?_, ?_, hgrow⟩
  · intro e he
    simp only [List.mem_append, List.mem_singleton] at he
    rcases he with he | rfl
    · exact hP.lab e he
    · exact DataModel.Exists.Assembly.defMeaning_label _ _ _ _
  · intro e he
    simp only [List.mem_append, List.mem_singleton] at he
    rcases he with he | rfl
    · obtain ⟨g', hg', hn⟩ := hP.names e he; exact ⟨g', hpre.subset hg', hn⟩
    · exact ⟨g, hg, hgn⟩

/-- **Every item keeps the invariant** (assembled). -/
theorem itemStep
    (hsteps : ∀ (K : RunCtx) (φ : Future), (∀ Δ, Strict.FundCtx { K with Δ := Δ }) → AllSteps K φ)
    (hsorts : SortsG Γ) (items : List Item) (hL : TopLinks dm D Γ fuel items) (hcov : ∀ d' ∈ Γ, dm.covers d') :
    ItemStep dm D Γ fuel items (StageOk dm D Γ) := by
  intro P it hin hP hacc hΓP _ hfaith
  unfold ItemAccepted at hacc
  rcases hr : (runMachine (checkItem it) { globals := P.globals, inds := P.inds } fuel).1 with ⟨u, st'⟩ | f | e
  · cases u
    cases it with
    | ind d' => exact stageOk_ind P d' st' hr hP
    | defn d => exact stageOk_defn hsteps hsorts items hL P d st' hin hr hP hfaith hcov hΓP
  · rw [hr] at hacc; simp at hacc
  · rw [hr] at hacc; simp at hacc

end

open Ochr.Consistency Ochr.Surface in
/-- **The accepted program resolves, each item accepted from the Σ of the earlier ones** (CHECKER; its resolution half
PROVED at `def one : Nat := 1`, `Top.One.resolves_one`; the per-item acceptance unread at any program, docs/31 D258: the content
of the old chain's `accepted_resolves`, `sorry` there; `checkProgram`'s first loop and `checkDefs`). -/
def ResolveG (q : Program) (fuel : Nat) : Prop :=
  Accepted (Prelude.decls ++ q) fuel → ∃ items, ResolvesTo (Prelude.decls ++ q) fuel items ∧
    ∀ (dm : DataModel) (D : MState → Decisions) (Γ : List IndDecl) (i : Nat) (it : Item), items[i]? = some it →
      ItemAccepted fuel (progMeaning dm D Γ (fun _ => .err) {} fuel (items.take i)) it

open Ochr.Consistency Ochr.Surface in
/-- **A closed definition of `False` is recorded at a type with no member** (MIXED; PROVED at `def one : Nat := 1`,
vacuously, `Top.One.falseConst_one`; the old chain's `falseConst_ty`, `sorry`
there and SUSPECT for lacking an acceptance and a coverage hypothesis, both added: the checker records the accepted
parameterless `d` with its stored type the library's `False` (names distinct, `Check.declared`; the library in front);
the model's `False` means the empty proposition, `Assembly.false_means_empty`, PROVED).

**Restated (docs/31 D256)**: as lead43 stated it, it concluded that the recorded type IS `prop False`. But
`ProgState.step` records `(err, err)` for a definition whose reference run fails, so that form was provable only from the
constant's run succeeding, which is the knot's output (`const_member`), not a fact about the checker. The recorded type
has no member in both cases (`prop False`, and `err`, whose carrier is empty), which is all the final contradiction
reads. -/
def FalseConstG (q : Program) (fuel : Nat) : Prop :=
  Accepted (Prelude.decls ++ q) fuel → ∀ items, ResolvesTo (Prelude.decls ++ q) fuel items →
    ∀ dm : DataModel,
      (progMeaning dm (chainDecisions fuel) (indsOf {} fuel items) (fun _ => .err) {} fuel items).Covered dm →
      ∀ d ∈ q, d.IsFalseConst →
        ∃ s T, (d.name, s, T) ∈ (progMeaning dm (chainDecisions fuel) (indsOf {} fuel items) (fun _ => .err) {} fuel items).means ∧
          ¬ ∃ x, x ∈ₛ[dm.read] T.m

open Ochr.Consistency Ochr.Surface in
/-- **CONSISTENCY FROM `master`** (assembled in Lean; the project's statement in `consistencyBounded`'s form: no accepted,
hole-free, level-bounded program has a closed definition of `False`). ASSUMES:
* the 32 step statements at every context meeting the fundamental lemma's condition (`hsteps`; FALSE until main's D147
  and `EvalAt`/`TailAt` carrying `RecCurG` both ways, at a context with a function under check, D253 item 3);
* the data model's theorem's facts (`hdata`, `DataFacts`; `Assembly.exists_dataModel` itself PROVED from them);
* the checker's resolution (`ResolveG`) and the recorded `False` constant (`FalseConstG`);
* the per-item links (`TopLinks`), at every data model covering the declarations and faithful at every stage (restated
  docs/31 D256 from "at every data model": every link already took both at its stage; the hypothesis now says so).
The restriction that no data declaration is at `Type₁` (`SortsG`) was a hypothesis; it is PROVED at every program
(`sortsG_indsOf`, docs/31 D256: the checker rejects such a declaration), so it is no longer assumed; what lifting it would
need is the model's. The fundamental lemma (`Strict.fund_all`) is PROVED and used inside (`const_member`, `knot_step`), as are `FundCtx` at each
item's context (`fundCtx_progCtx`, `fundCtx_ctxAt`), the stage closure's membership, the knot's induction
(`knot_member`, `stages_below`), an inductive declaration's step (`stageOk_ind`), and the program-level induction. -/
theorem consistency_of_master (q : Program) (fuel : Nat) (_holes : NoHoles q) (_levels : LevelsBelow 2 q)
    (acc : Accepted (Prelude.decls ++ q) fuel)
    (hsteps : ∀ (K : RunCtx) (φ : Future), (∀ Δ, Strict.FundCtx { K with Δ := Δ }) → AllSteps K φ)
    (hdata : ∀ items, ResolvesTo (Prelude.decls ++ q) fuel items →
      DataModel.Exists.Assembly.DataFacts (chainDecisions fuel) fuel items)
    (hres : ResolveG q fuel) (hfalse : FalseConstG q fuel)
    (hlinks : ∀ items, ResolvesTo (Prelude.decls ++ q) fuel items →
      ∀ dm, (∀ d' ∈ indsOf {} fuel items, dm.covers d') →
        (∀ k, k ≤ items.length → DataFaithful dm (chainDecisions fuel) (indsOf {} fuel items)
          (progMeaning dm (chainDecisions fuel) (indsOf {} fuel items) (fun _ => .err) {} fuel (items.take k))) →
        TopLinks dm (chainDecisions fuel) (indsOf {} fuel items) fuel items) :
    ∀ d ∈ q, ¬ d.IsFalseConst := by
  intro d hd hf
  obtain ⟨items, hri, hacc⟩ := hres acc
  obtain ⟨dm, hcov, hfaith⟩ := exists_dataModel _ items fuel hri (hdata items hri)
  have hcov' : ∀ d' ∈ indsOf {} fuel items, dm.covers d' := fun d' hd' => hcov d' (by rw [progMeaning_inds]; exact hd')
  have hS := inv_all dm (chainDecisions fuel) (indsOf {} fuel items) fuel items (stageOk_empty _ _ _)
    (itemStep hsteps (sortsG_indsOf {} fuel items) items (hlinks items hri dm hcov' hfaith) hcov') (fun i it h => hacc dm _ _ i it h)
    (fun k _ => by rw [progMeaning_inds]; exact Steps.Machine.indsOf_take_prefix {} fuel items k) hfaith
  obtain ⟨s, T, hin, hT⟩ := hfalse acc items hri dm hcov d hd hf
  exact hT ⟨s, hS.mem _ s T hin⟩

end Ochr.Meaning.Steps.Form.Top
