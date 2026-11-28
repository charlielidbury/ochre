import Ochr.Meaning.Steps.TopFix

/-!
# The top, a function WITHOUT `by`: the constant's route, with `TailAt` for `EvalAt` (lead50; docs/31 D296, D297)

R-dec (docs/31 D255, D296; main's D147/D148): a function has a self exactly when it has `by`. Without `by`, `checkDef`
checks the function from the earlier items' Σ (it is appended after its check, as a constant is), with no function
under check (`K.cur = none`), an empty [Rec] stack and `()` at `Unit` in the body frame's own-name slot; the reference's
closure is ONE run of the body with the same slot (`fixBodyU`): no stage, no bound, no knot.

So the route is the constant's (`Steps/TopConst.lean`): the check is simulated at the item's context AT THE STATE THE
BODY'S CHECK ENDS IN (`P.ctx … w.st₁`, whose Σ is the stage's: at the item's final state the steps' alignment
hypothesis is unsatisfiable, D256's finding for constants, since `declOf` of the function's own name reads `.any` before
its entry and its type after), the leaf gives the body's run good at every member argument, the closure is a member by
`closure_mem_of_total` (one application, no induction on a bound), and a stability link moves the function's parts from
the check's decisions to the final state's, where the program meaning forms the closure (`defMeaning`), as
`ConstMeanAt` does for a constant.
-/

namespace Ochr.Meaning.Steps.Form.Top

open Ochr Ochr.Meaning Ochr.Meaning.Steps Ochr.Meaning.Steps.Form Ochr.Meaning.Steps.Form.Master
open Ochr.Meaning.Steps.Form.FixEqDesc
open Ochr.Meaning.Assembly

/-- The closure's frame at the arguments `a` without `by` (`fixBodyU`'s state before the body runs): the forming state
under a fresh bottom frame, the own-name slot `()` at `Unit`, then the parameters (a borrow parameter at a fresh label
with a cell of frame 0). -/
noncomputable def startU (K : RunCtx) (ρ : Assignment) (φ : Future) (ds : List Term) (c : Term) (a : List Sem) : SState :=
  ((a.zip (psG K ρ φ ds)).foldl (fixStep (fbG K ρ φ ds c)) (formG.under.pushBind unitSlot, [], [])).1

section
variable (dm : DataModel) (D : MState → Decisions) (Γ : List IndDecl) (fuel : Nat)

/-- **The function branch of `checkDef` without `by`, inverted to the body's tail check** (CHECKER; read true against
`checkDef`, `checkFix`, main's D147/D148). As `FixCheckAt`, but the generic state's Σ is the stage's (`P.globals`: the
entry is appended after the check) and its [Rec] stack is empty (no `by`, D136); the entry is in `st'` only. -/
def FixNCheckAt (P : ProgState) (d : Def) (st' : MState) (w : FixWit) : Prop :=
  ModeR w.st₀ ∧ w.st₀.tailNext = false ∧ 0 < w.st₀.env.size ∧ w.st₀.tailDecl = none ∧
  w.st₀.globals = P.globals ∧ w.st₀.recStack = [] ∧
  Runs (Ochr.checkTail w.n d.body (fixCont w.n d.name w.start)) w.st₀ w.bh () w.st₁ ∧
  (∀ v T, GrowsM (fixCont w.n d.name w.start v T)) ∧ (∀ v T, KeepsTab (fixCont w.n d.name w.start v T)) ∧
  st'.globals = P.globals ++ [fnEntry d w.model] ∧
  ((st'.globals.find? (·.name == d.name)).map (·.ty)).getD .bot = .tPi [] (.pi d.hs d.doms d.cod) []

/-- The check's context: the item's at the state the body's check ends in (`w.st₁`), reading the unknowns' types as
`Δa` (the start's to choose, as `ctxBΔ`'s). No function under check. -/
noncomputable abbrev ctxN (P : ProgState) (w : FixWit) (Δa : Nat → TyS) : RunCtx :=
  { P.ctx dm D Γ w.st₁ with Δ := Δa }

/-- **The start of the check** (MIXED; read true by parts; `FixStartAt` without the bound, the induction hypothesis
and the stage closure). At member arguments `a`: an assignment of the generic state's unknowns, a reading `Δa` and a
renaming under which `Pre`, the [Rec] stack's tie (`RecTie.nil`: empty stack, `K.cur = none`), the relation from the
generic state to the closure's frame at `a` (`startU`: the slot `()` on both sides), that frame good, the body holding
no embedded value, unknown or hole, the table aligned at the run's end, and the goal read under the assignment as the
codomain at `a`. -/
def FixNStartAt (P : ProgState) (d : Def) (w : FixWit) : Prop :=
  ∀ (ρ : Assignment) (φ : Future) (a : List Sem),
    DomMembers dm.read (psG (P.ctx dm D Γ w.st₁) ρ φ d.doms) a →
    ∃ (ρa : Assignment) (Δa : Nat → TyS) (π : Nat → Nat),
      Pre (ctxN dm D Γ P w Δa) ρa w.st₀ ∧ RecTie (ctxN dm D Γ P w Δa) ρa w.st₀ ∧
      Rel (ctxN dm D Γ P w Δa) ρa φ π w.st₀ (startU (P.ctx dm D Γ w.st₁) ρ φ d.doms d.cod a) ∧
      Strict.SGood dm Γ φ (startU (P.ctx dm D Γ w.st₁) ρ φ d.doms d.cod a) ∧
      d.body.valsOk (Strict.ValsP (ctxN dm D Γ P w Δa) ρa φ) ∧ d.body.absBelow w.st₀.absTy.size ∧
      d.body.hasHolePrim = false ∧ DecTab (D w.st₁) w.st₁ ∧
      hintM (ctxN dm D Γ P w Δa) ρa w.st₀.goal = (fbG (P.ctx dm D Γ w.st₁) ρ φ d.doms d.cod).2.1 a

/-- **The body runs alike at the start's assignment and `Δa` and at the closure's** (MODEL; read true: a resolved
body holds no unknown, so its run reads neither the assignment nor `Δ`, `AssignCongr`). The knot's `BodyCongrAt`
without its second context: the check and the closure are at the same decisions here. -/
def FixNCongrAt (P : ProgState) (d : Def) (w : FixWit) : Prop :=
  ∀ (ρ ρa : Assignment) (Δa : Nat → TyS) (φ : Future) (h : TyS) (s : SState),
    runT (ctxN dm D Γ P w Δa) ρa φ true h d.body s = runT (P.ctx dm D Γ w.st₁) ρ φ true h d.body s

/-- **The leaf** (MIXED; `FixLeafAt` without the stage: from `TailAt`'s conclusion at the start, the fundamental lemma
at the reference's run and the run being the closure's, the body's run with `()` in the slot is good at `a`). Derived
from the same three leaf facts as the knot's leaf at a data function (`Leaf.fixLeafG_of`'s argument). -/
def FixNLeafAt (P : ProgState) (d : Def) (w : FixWit) : Prop :=
  ∀ (ρ ρa : Assignment) (Δa : Nat → TyS) (φ : Future) (π : Nat → Nat) (a : List Sem),
    DomMembers dm.read (psG (P.ctx dm D Γ w.st₁) ρ φ d.doms) a →
    Pre (ctxN dm D Γ P w Δa) ρa w.st₀ →
    Rel (ctxN dm D Γ P w Δa) ρa φ π w.st₀ (startU (P.ctx dm D Γ w.st₁) ρ φ d.doms d.cod a) →
    hintM (ctxN dm D Γ P w Δa) ρa w.st₀.goal = (fbG (P.ctx dm D Γ w.st₁) ρ φ d.doms d.cod).2.1 a →
    TailConcl (ctxN dm D Γ P w Δa) ρa φ π w.st₀ (startU (P.ctx dm D Γ w.st₁) ρ φ d.doms d.cod a)
      d.body (runT (ctxN dm D Γ P w Δa) ρa φ true (hintM (ctxN dm D Γ P w Δa) ρa w.st₀.goal) d.body)
      (fixCont w.n d.name w.start) →
    runT (ctxN dm D Γ P w Δa) ρa φ true (hintM (ctxN dm D Γ P w Δa) ρa w.st₀.goal) d.body
        (startU (P.ctx dm D Γ w.st₁) ρ φ d.doms d.cod a) =
      runT (P.ctx dm D Γ w.st₁) ρ φ true ((fbG (P.ctx dm D Γ w.st₁) ρ φ d.doms d.cod).2.1 a) d.body
        (startU (P.ctx dm D Γ w.st₁) ρ φ d.doms d.cod a) →
    (∀ r s', runT (P.ctx dm D Γ w.st₁) ρ φ true ((fbG (P.ctx dm D Γ w.st₁) ρ φ d.doms d.cod).2.1 a) d.body
        (startU (P.ctx dm D Γ w.st₁) ρ φ d.doms d.cod a) = some (r, s') →
      Strict.GoodRes dm.read r ∧ Strict.SGood dm Γ φ s') →
    ∃ o, fixBodyU (P.ctx dm D Γ w.st₁) ρ φ (fbG (P.ctx dm D Γ w.st₁) ρ φ d.doms d.cod) formG
        (psG (P.ctx dm D Γ w.st₁) ρ φ d.doms) (outG (P.ctx dm D Γ w.st₁) ρ φ d.doms d.cod) 0 d.body a = some o ∧
      OutGood' dm.read (psG (P.ctx dm D Γ w.st₁) ρ φ d.doms) (outG (P.ctx dm D Γ w.st₁) ρ φ d.doms d.cod) a o

/-- **The function's parts are stable from the check's decisions to the final state's** (MODEL/DECISIONS; read true:
the two tables differ only on terms naming the function, which its code does not (D118), and on unknowns made after
`w.st₁`, which its code does not hold). What `ConstMeanAt` carries for a constant. -/
def FixNStableAt (P : ProgState) (d : Def) (st' : MState) (w : FixWit) : Prop :=
  ∀ (ρ : Assignment) (φ : Future),
    psG (P.ctx dm D Γ w.st₁) ρ φ d.doms = psG (P.ctx dm D Γ st') ρ φ d.doms ∧
    outG (P.ctx dm D Γ w.st₁) ρ φ d.doms d.cod = outG (P.ctx dm D Γ st') ρ φ d.doms d.cod ∧
    GG (P.ctx dm D Γ w.st₁) ρ φ d.hs d.doms d.cod none d.body = GG (P.ctx dm D Γ st') ρ φ d.hs d.doms d.cod none d.body

/-- **A function without `by`'s links, about its own check** (R-dec, docs/31 D296): an accepted function without `by`
at a stage meeting the invariant has a witness meeting all nine. -/
def FixNG (items : List Item) : Prop :=
  ∀ (P : ProgState) (d : Def) (st' : MState), AtStage dm D Γ fuel items P (.defn d) → d.doms ≠ [] → d.dec = none →
    (runMachine (checkItem (.defn d)) { globals := P.globals, inds := P.inds } fuel).1 = .ok () st' →
    StageOk dm D Γ P → DataFaithful dm D Γ P → (∀ d' ∈ Γ, dm.covers d') → P.inds <+: Γ →
    ∃ w : FixWit, FixNCheckAt P d st' w ∧ FixFitsAt dm D Γ P d st' ∧ FixNStartAt dm D Γ P d w ∧
      FixNCongrAt dm D Γ P d w ∧ FixNLeafAt dm D Γ P d w ∧ FixNStableAt dm D Γ P d st' w ∧
      FixPartsAt dm D Γ P d st' ∧ FixClosedAt d ∧ FixFlagAt dm D Γ P d st'

end

section
variable {dm : DataModel} {D : MState → Decisions} {Γ : List IndDecl} {fuel : Nat}

/-- **The body is good at every member argument** (assembled; no stage, no knot): `TailAt` at the body in the check's
context (`master`), started by `FixNStartAt`, the fundamental lemma at the reference's run (`FundCtx` at the item's
context, `fundCtx_progCtx`), the run being the closure's (`FixNCongrAt`), and the leaf. -/
theorem fixN_good
    (hsteps : ∀ (K : RunCtx) (φ : Future), (∀ Δ, Strict.FundCtx { K with Δ := Δ }) → AllSteps K φ)
    (hsorts : SortsG Γ) (P : ProgState) (d : Def) (st' : MState) (hP : StageOk dm D Γ P) (w : FixWit)
    (hck : FixNCheckAt P d st' w) (hstart : FixNStartAt dm D Γ P d w) (hcongr : FixNCongrAt dm D Γ P d w)
    (hleaf : FixNLeafAt dm D Γ P d w) (ρ : Assignment) (φ : Future) :
    ∀ a, DomMembers dm.read (psG (P.ctx dm D Γ w.st₁) ρ φ d.doms) a →
      ∃ o, fixBodyU (P.ctx dm D Γ w.st₁) ρ φ (fbG (P.ctx dm D Γ w.st₁) ρ φ d.doms d.cod) formG
          (psG (P.ctx dm D Γ w.st₁) ρ φ d.doms) (outG (P.ctx dm D Γ w.st₁) ρ φ d.doms d.cod) 0 d.body a = some o ∧
        OutGood' dm.read (psG (P.ctx dm D Γ w.st₁) ρ φ d.doms) (outG (P.ctx dm D Γ w.st₁) ρ φ d.doms d.cod) a o := by
  intro a ha
  obtain ⟨hm, htn, hsz, htd, -, -, hrt, hgr, hkt, -, -⟩ := hck
  obtain ⟨ρa, Δa, π, hpre, htie, hrel, hsg, hvals, hab, hhole, hdt, hhint⟩ := hstart ρ φ a ha
  have hfc0 : Strict.FundCtx (P.ctx dm D Γ w.st₁) := fundCtx_progCtx dm D Γ P w.st₁ hP.mem hP.lab hsorts
  have hfc : Strict.FundCtx (ctxN dm D Γ P w Δa) := ⟨hfc0.globals, hfc0.sorts⟩
  have hall := hsteps (ctxN dm D Γ P w Δa) φ (fun _ => ⟨hfc.globals, hfc.sorts⟩)
  have hT := tail_all hall ρa w.n d.body w.st₀ (fixCont w.n d.name w.start) _ π w.bh w.st₁ hm htn hsz htd hgr hkt hpre
    htie hrel hsg hvals hab hhole hdt hrt
  have heq := (congrArg (fun h => runT (ctxN dm D Γ P w Δa) ρa φ true h d.body
      (startU (P.ctx dm D Γ w.st₁) ρ φ d.doms d.cod a)) hhint).trans (hcongr ρ ρa Δa φ _ _)
  refine hleaf ρ ρa Δa φ π a ha hpre hrel hhint hT heq (fun r s' hx => ?_)
  rw [← heq] at hx
  have hF := Strict.fund_all hfc d.body hvals true _ _ s' r hsg hx
  exact ⟨hF.1, hF.2.2.2⟩

/-- **The function is good, at the final state's context** (assembled): `fixN_good` moved by stability, with the type
fitting its sort. What `GlobGrowG` consumes, as the knot's `fnGoodAt_of_knot` gives it for a function with `by`. -/
theorem fnGoodAtN
    (hsteps : ∀ (K : RunCtx) (φ : Future), (∀ Δ, Strict.FundCtx { K with Δ := Δ }) → AllSteps K φ)
    (hsorts : SortsG Γ) (P : ProgState) (d : Def) (st' : MState) (hP : StageOk dm D Γ P) (w : FixWit)
    (hdec : d.dec = none) (hck : FixNCheckAt P d st' w) (hfits : FixFitsAt dm D Γ P d st')
    (hstart : FixNStartAt dm D Γ P d w) (hcongr : FixNCongrAt dm D Γ P d w) (hleaf : FixNLeafAt dm D Γ P d w)
    (hstab : FixNStableAt dm D Γ P d st' w) (ρ : Assignment) (φ : Future) :
    FnGoodAt (P.ctx dm D Γ st') ρ φ d.hs d.doms d.cod d.dec d.body := by
  obtain ⟨hps, hout, hgg⟩ := hstab ρ φ
  refine ⟨hfits ρ φ, fun a ha => ?_⟩
  rw [← hps] at ha
  obtain ⟨o, ho, hg⟩ := fixN_good hsteps hsorts P d st' hP w hck hstart hcongr hleaf ρ φ a ha
  refine ⟨o, ?_, ?_⟩
  · rw [hdec, ← hgg]; exact ho
  · rw [← hps, ← hout]; exact hg

/-- **An accepted function without `by` means a member of its type** (assembled; no knot): `fnGoodAtN` at the
program's assignment and the constant future, the closure's membership by `closure_mem_of_total`, the meaning
(`FixMeanAt`). -/
theorem fixN_member
    (hsteps : ∀ (K : RunCtx) (φ : Future), (∀ Δ, Strict.FundCtx { K with Δ := Δ }) → AllSteps K φ)
    (hsorts : SortsG Γ) (P : ProgState) (d : Def) (st' : MState) (hP : StageOk dm D Γ P) (w : FixWit)
    (hdec : d.dec = none) (hck : FixNCheckAt P d st' w) (hfits : FixFitsAt dm D Γ P d st')
    (hstart : FixNStartAt dm D Γ P d w) (hcongr : FixNCongrAt dm D Γ P d w) (hleaf : FixNLeafAt dm D Γ P d w)
    (hstab : FixNStableAt dm D Γ P d st' w) (hmean : FixMeanAt dm D Γ P d st') :
    ∃ m, defMeaning (fun _ => .err) (P.ctx dm D Γ st') d
        (((st'.globals.find? (·.name == d.name)).map (·.ty)).getD .bot) = some m ∧ m.1 ∈ₛ[dm.read] m.2.m := by
  have hg := fnGoodAtN hsteps hsorts P d st' hP w hdec hck hfits hstart hcongr hleaf hstab (fun _ => .err) noFuture
  have hk := Steps.closure_mem_of_total dm.read _ noFuture _ _
    (GG (P.ctx dm D Γ st') (fun _ => .err) noFuture d.hs d.doms d.cod d.dec d.body) hg.1 hg.2
  rw [hck.2.2.2.2.2.2.2.2.2.2]
  exact hmean hk

end

end Ochr.Meaning.Steps.Form.Top
