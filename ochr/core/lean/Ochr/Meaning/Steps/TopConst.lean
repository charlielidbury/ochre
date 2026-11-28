import Ochr.Meaning.Steps.Top

/-!
# The top, a constant: from `EvalAt` at its body to its meaning being a member of its type (lead43; docs/31 D254)

A definition with no parameters (a constant, a closed proof) is checked by `checkDef`'s constant branch: one empty
frame, no goal, no [Rec] entry; the goal evaluated; the body EVALUATED (`eval true d.body (some goal)`, not `checkTail`);
the type converted to the goal; [Return]; the global stored at the goal (`⋆` at a proposition). So its link to the
general statement is `EvalAt` (not `TailAt`), at the context `P.ctx` of the item's final state, with no function under
check (`K.cur = none`: the constant is not in Σ during its own check, and its body cannot name it, D118).

`const_member` composes, in Lean: the checker's inversion (`ConstCheckG`), the start (`ConstStartG`), `EvalAt` at the
body (from the 32 steps, `master`), `FundCtx` at the item's context (PROVED from the invariant, `fundCtx_progCtx`, and
the checker's sort bound `SortsG`), the fundamental lemma (`Strict.fund_all`, PROVED) at the reference's run, the leaf
(`ConstLeafG`: conversion's soundness, [Return], the goal's level) and the meaning (`ConstMeanG`).
-/

namespace Ochr.Meaning.Steps.Form.Top

open Ochr Ochr.Meaning Ochr.Meaning.Steps Ochr.Meaning.Steps.Form Ochr.Meaning.Steps.Form.Master
open Ochr.Meaning.Assembly

section
variable (dm : DataModel) (D : MState → Decisions) (Γ : List IndDecl) (fuel : Nat)

/-- **No data declaration of the program at `Type₁`** (CHECKER; read true: `checkInd` and the surface reject a sort above
`Type₀`, "an inductive type is in Prop or Type"). A NAMED RESTRICTION of the top (the orchestrator, 2026-11-28): the
model reads every data declaration as a `Type₀` code (`FundCtx.sorts`); lifting it needs data declarations at `Type₁`
built at level 1 in the model (`Code1` carriers for declarations, and `FundCtx.sorts` dropped). -/
def SortsG : Prop := ∀ d ∈ Γ, d.sort ≠ 2

/-- What the checker's inversion of an accepted constant produces: the fuel and states of its check, its goal, its
body's value and type. Every other link of a constant is a predicate on THIS witness (asserted of the states the check
actually goes through, never of arbitrary ones: as first stated, about every state and definition, each was false at
junk arguments, which would have made the top vacuous; docs/31 D254). -/
structure ConstWit where
  n : Nat
  st₁ : MState
  st₂ : MState
  st₃ : MState
  st₄ : MState
  bh : Nat
  goal : Value
  v : Value
  T : Value

/-- **The constant branch of `checkDef`, inverted** (CHECKER; read true against `Check.checkDef`; PROVED at the program
`def one : Nat := 1`, `Top.One.one_check_inv`). The state the body is evaluated from (one frame, the plain mode, no
reading handed down, Σ the stage's), the body's typed run at the goal, the conversion of its type to the goal
(succeeding), [Return] (succeeding), and the entry stored: the constant's name, no `fix` code, the goal its type.

**Restated (docs/31 D258)**: the conversion and [Return] run from a state equal to the one before them BUT FOR THE
EDITOR'S LOCATIONS (`Machine.LocsEq`): `checkDef` runs the conversion inside `located d.body`, whose inversion
(`Runs.located_inv`) relates the states only up to `locs`. No consumer reads these two clauses (`const_member` drops
them); as first stated they asked the runs from `w.st₂` and `w.st₃` exactly, which needs a whole-machine fact (no run
writes the location table), not provable at one program. -/
def ConstCheckAt (P : ProgState) (d : Def) (st' : MState) (w : ConstWit) : Prop :=
  ModeR w.st₁ ∧ w.st₁.tailNext = false ∧ 0 < w.st₁.env.size ∧ w.st₁.tailDecl = none ∧ w.st₁.globals = P.globals ∧
  Runs (Ochr.eval w.n true d.body (some w.goal)) w.st₁ w.bh (w.v, some w.T) w.st₂ ∧
  (∃ s f b, Machine.LocsEq w.st₂ s ∧ Runs (Ochr.conv f w.T w.goal) s b true w.st₃) ∧
  (∃ s f b, Machine.LocsEq w.st₃ s ∧ Runs (Ochr.bodyReturns f s!"{d.name} is defined as it" w.v w.goal [] "") s b () w.st₄) ∧
  (∃ g : GDef, st'.globals = P.globals ++ [g] ∧ g.name = d.name ∧ g.fn? = none) ∧
  ((st'.globals.find? (·.name == d.name)).map (·.ty)).getD .bot = w.goal

/-- **The constant's start** (MIXED; read true by parts, unproved). At the state the body is evaluated from, under the
context of the item's check AT THE STATE THE BODY'S RUN ENDS IN (`w.st₂`, whose Σ is the stage's: the constant's own entry
is appended only after its check), at every assignment and future: `Pre` (its `CtxS`: the declarations a prefix of the
program's, the model covering and faithful, no global labelled, `GlobalsOk` from the invariant's `glob` at the stage's Σ,
`LaterDec` at `w.st₂`; its `Inv`, the checker's invariant at a state with one empty frame; its `Asg`, no unknown
referenced); the reference's reading of that state related to it (`Rel.start`: it holds no borrow) and good; the body
holding no embedded value, unknown or hole (resolution, `NoHoles`); the decision table aligned at the run's end
(`DecisionsFF.decTab_ff` at `w.st₂`).

**As lead43 stated it, FALSE at every accepted constant whose name the checker reads as more than `.any`** (docs/31 D256):
it ran the body at `P.ctx … st'`, the decisions at the state AFTER the constant's entry is in Σ, and asked
`DecTab (D st') w.st₂`; but at `w.st₂` the checker's `declOf (.const c)` finds no `c` and answers `.any`, while at `st'` it
reads `c`'s stored type (`TopAttack`, guarded on `def one : Nat := S(Z)`: `.any` against `.other`). So the steps' own
hypothesis (E9) was unsatisfiable at the top's context of every such constant, and the top vacuous at every program
holding one. -/
def ConstStartAt (P : ProgState) (d : Def) (_st' : MState) (w : ConstWit) : Prop :=
  ∀ (ρ : Assignment) (φ : Future),
    Pre (P.ctx dm D Γ w.st₂) ρ w.st₁ ∧ Rel (P.ctx dm D Γ w.st₂) ρ φ id w.st₁ (SM' (P.ctx dm D Γ w.st₂) ρ w.st₁) ∧
    Strict.SGood dm Γ φ (SM' (P.ctx dm D Γ w.st₂) ρ w.st₁) ∧ d.body.valsOk (Strict.ValsP (P.ctx dm D Γ w.st₂) ρ φ) ∧
    d.body.absBelow w.st₁.absTy.size ∧ HintBelow (some w.goal) w.st₁.absTy.size ∧ d.body.hasHolePrim = false ∧
    DecTab (D w.st₂) w.st₂

/-- **The constant's leaf** (MIXED; read true by parts, unproved: conversion's soundness at a type (N3), [Return] giving a
whole result, so its meaning is not `⊥`, the goal of a level-bounded program meaning a type that is not `err`, and the goal
holding no unknown, so its meaning is the same under every assignment). The reference's result good, MEANING THE CHECKER'S
VALUE (`OutL`'s meaning link), its type the checker's type there, the checker's type converting to the goal, [Return]
passed: the result is a member of the goal's meaning at the program's assignment.

**As lead43 stated it, FALSE wherever the step's own conclusion holds** (docs/31 D256): `r` was tied to the checker's run
only by its type, and `GoodRes` admits `r.1 = ⊥`, so the link asserted that `⊥` is a member of the goal
(`TopAttack.constLeafAt_old_forces_moved`, kernel-checked; false at `Nat`, `moved_not_mem_nat`). Repaired by the meaning
link, which `eval_all` gives. -/
def ConstLeafAt (P : ProgState) (_d : Def) (_st' : MState) (w : ConstWit) : Prop :=
  ∀ (ρ' : Assignment) (Δ' : Nat → TyS) (π' : Nat → Nat) (r : Res),
    Pre { P.ctx dm D Γ w.st₂ with Δ := Δ' } ρ' (w.st₂.withTempT w.v (some w.T)) →
    meanV { P.ctx dm D Γ w.st₂ with Δ := Δ' } ρ' (fun l => noFuture (π' l)) r.2 w.v = r.1 →
    StrAgree { P.ctx dm D Γ w.st₂ with Δ := Δ' } ρ' w.T r.2 → Strict.GoodRes dm.read r →
    r.1 ∈ₛ[dm.read] (globalTyS (fun _ => .err) (P.ctx dm D Γ w.st₂) w.goal).m

/-- **The constant's meaning is the simulated run's** (MODEL; its parts: the counter's independence (RL,
`run_counter_indep`, the shift from `w.st₁`'s label counter to `0`), the future's (the result holds no live label after
[Return]), the assignment's (a closed body), the hint (`hintM` of the goal, not deferred, is `globalTyS`'s reading), the
reference's state at the start being `emptyState` at the checker's counter, `•` at a proposition (`constMean`), and,
since docs/31 D256, the decisions' stability from `w.st₂` to `st'`: the two tables differ only at the constant's own name,
which its body cannot mention (D118), and at unknowns made after `w.st₂`, which its body does not hold). -/
def ConstMeanAt (P : ProgState) (d : Def) (st' : MState) (w : ConstWit) : Prop :=
  ∀ (ρ : Assignment) (φ : Future) (r : Res) (s' : SState),
    runT (P.ctx dm D Γ w.st₂) ρ φ false (hintM (P.ctx dm D Γ w.st₂) ρ (some w.goal)) d.body
        (SM' (P.ctx dm D Γ w.st₂) ρ w.st₁) = some (r, s') →
    r.1 ∈ₛ[dm.read] (globalTyS (fun _ => .err) (P.ctx dm D Γ w.st₂) w.goal).m →
    ∃ m, defMeaning (fun _ => .err) (P.ctx dm D Γ st') d w.goal = some m ∧ m.1 ∈ₛ[dm.read] m.2.m

/-- **A constant's links, about its own check**: an accepted constant at a stage meeting the invariant has a witness
meeting all four. -/
def ConstG (items : List Item) : Prop :=
  ∀ (P : ProgState) (d : Def) (st' : MState), AtStage dm D Γ fuel items P (.defn d) → d.doms = [] →
    (runMachine (checkItem (.defn d)) { globals := P.globals, inds := P.inds } fuel).1 = .ok () st' →
    StageOk dm D Γ P → DataFaithful dm D Γ P → (∀ d' ∈ Γ, dm.covers d') → P.inds <+: Γ →
    ∃ w : ConstWit, ConstCheckAt P d st' w ∧ ConstStartAt dm D Γ P d st' w ∧ ConstLeafAt dm D Γ P d st' w ∧
      ConstMeanAt dm D Γ P d st' w

end

/-! ## The composition -/

section
variable {dm : DataModel} {D : MState → Decisions} {Γ : List IndDecl} {fuel : Nat}

/-- **An accepted constant means a member of its type** (assembled in Lean; assumes the 32 steps at the item's context,
`SortsG`, `ConstCheckG`, `ConstStartG`, `ConstLeafG`, `ConstMeanG`): `EvalAt` at the body (`master`), from the start the
checker's inversion and the start give; `FundCtx` at the item's context from the invariant (`fundCtx_progCtx`); the
fundamental lemma at the reference's run (`fund_all`); the leaf; the meaning. -/
theorem const_member
    (hsteps : ∀ (K : RunCtx) (φ : Future), (∀ Δ, Strict.FundCtx { K with Δ := Δ }) → AllSteps K φ)
    (hsorts : SortsG Γ) (items : List Item) (hc : ConstG dm D Γ fuel items)
    (P : ProgState) (d : Def) (st' : MState) (hin : AtStage dm D Γ fuel items P (.defn d)) (hd : d.doms = [])
    (hP : StageOk dm D Γ P) (hfaith : DataFaithful dm D Γ P) (hcov : ∀ d' ∈ Γ, dm.covers d') (hΓP : P.inds <+: Γ)
    (hrun : (runMachine (checkItem (.defn d)) { globals := P.globals, inds := P.inds } fuel).1 = .ok () st') :
    ∃ m, defMeaning (fun _ => .err) (P.ctx dm D Γ st') d
        (((st'.globals.find? (·.name == d.name)).map (·.ty)).getD .bot) = some m ∧ m.1 ∈ₛ[dm.read] m.2.m := by
  obtain ⟨w, ⟨hm, htn, hsz, htd, hgl, hev, -, -, -, hfind⟩, hst', hleaf, hmean⟩ :=
    hc P d st' hin hd hrun hP hfaith hcov hΓP
  have hfc : Strict.FundCtx (P.ctx dm D Γ w.st₂) := fundCtx_progCtx dm D Γ P w.st₂ hP.mem hP.lab hsorts
  obtain ⟨hpre, hrel, hsg, hvals, hab, hhb, hhole, hdt⟩ := hst' (fun _ => .err) noFuture
  have hall := hsteps (P.ctx dm D Γ w.st₂) noFuture (fun _ => ⟨hfc.globals, hfc.sorts⟩)
  obtain ⟨⟨ρ', Δ', π', r, s', -, hx, hmv, hstr, -, hpre', -, -, -⟩, -⟩ :=
    eval_all hall (fun _ => .err) w.n d.body w.st₁ w.st₂ true (some w.goal) w.v (some w.T) _ id hm (fun _ => htn) hsz
      (Or.inl htd) hpre hrel hsg hvals hab hhb hhole (fun h => by cases h) hdt w.bh hev
  rw [htn] at hx
  have hgood := (Strict.fund_all hfc d.body hvals false _ _ s' r hsg hx).1
  have hmem := hleaf ρ' Δ' π' r hpre' hmv (hstr w.T rfl) hgood
  rw [hfind]
  exact hmean (fun _ => .err) noFuture r s' hx hmem

end

end Ochr.Meaning.Steps.Form.Top
