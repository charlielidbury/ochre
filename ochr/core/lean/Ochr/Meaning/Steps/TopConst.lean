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

/-- **The constant branch of `checkDef`, inverted** (CHECKER; read true against `Check.checkDef`; the machine lane's to
prove). The state the body is evaluated from (one frame, the plain mode, no reading handed down, Σ the stage's), the
body's typed run at the goal, the conversion of its type to the goal (succeeding), [Return] (succeeding), and the entry
stored: the constant's name, no `fix` code, the goal its type. -/
def ConstCheckAt (P : ProgState) (d : Def) (st' : MState) (w : ConstWit) : Prop :=
  ModeR w.st₁ ∧ w.st₁.tailNext = false ∧ 0 < w.st₁.env.size ∧ w.st₁.tailDecl = none ∧ w.st₁.globals = P.globals ∧
  Runs (Ochr.eval w.n true d.body (some w.goal)) w.st₁ w.bh (w.v, some w.T) w.st₂ ∧
  (∃ f b, Runs (Ochr.conv f w.T w.goal) w.st₂ b true w.st₃) ∧
  (∃ f b, Runs (Ochr.bodyReturns f s!"{d.name} is defined as it" w.v w.goal [] "") w.st₃ b () w.st₄) ∧
  (∃ g : GDef, st'.globals = P.globals ++ [g] ∧ g.name = d.name ∧ g.fn? = none) ∧
  ((st'.globals.find? (·.name == d.name)).map (·.ty)).getD .bot = w.goal

/-- **The constant's start** (MIXED; read true by parts, unproved). At the state the body is evaluated from, under the
item's context, at every assignment and future: `Pre` (its `CtxS`: the declarations a prefix of the program's, the model
covering and faithful, no global labelled, `GlobalsOk` from the invariant's `glob` at the stage's Σ; its `Inv`, the
checker's invariant at a state with one empty frame; its `Asg`, no unknown referenced); the reference's reading of that
state related to it (`Rel.start`: it holds no borrow) and good; the body holding no embedded value, unknown or hole
(resolution, `NoHoles`); the decision table aligned at the run's end (the item's, the tables only growing). -/
def ConstStartAt (P : ProgState) (d : Def) (st' : MState) (w : ConstWit) : Prop :=
  ∀ (ρ : Assignment) (φ : Future),
    Pre (P.ctx dm D Γ st') ρ w.st₁ ∧ Rel (P.ctx dm D Γ st') ρ φ id w.st₁ (SM' (P.ctx dm D Γ st') ρ w.st₁) ∧
    Strict.SGood dm Γ φ (SM' (P.ctx dm D Γ st') ρ w.st₁) ∧ d.body.valsOk (Strict.ValsP (P.ctx dm D Γ st') ρ φ) ∧
    d.body.absBelow w.st₁.absTy.size ∧ HintBelow (some w.goal) w.st₁.absTy.size ∧ d.body.hasHolePrim = false ∧
    DecTab (D st') w.st₂

/-- **The constant's leaf** (MIXED; unread as one fact; its parts: conversion's soundness at a type (N3), [Return] giving
a whole result (not `⊥`), the goal of a level-bounded program meaning a type that is not `err`, and the goal holding no
unknown (so its meaning is the same under every assignment)). The reference's result good, its type the checker's type
there, the checker's type converting to the goal, [Return] passed: the result is a member of the goal's meaning at the
program's assignment. -/
def ConstLeafAt (P : ProgState) (d : Def) (st' : MState) (w : ConstWit) : Prop :=
  ∀ (ρ' : Assignment) (Δ' : Nat → TyS) (r : Res),
    Pre { P.ctx dm D Γ st' with Δ := Δ' } ρ' (w.st₂.withTempT w.v (some w.T)) →
    StrAgree { P.ctx dm D Γ st' with Δ := Δ' } ρ' w.T r.2 → Strict.GoodRes dm.read r →
    r.1 ∈ₛ[dm.read] (globalTyS (fun _ => .err) (P.ctx dm D Γ st') w.goal).m

/-- **The constant's meaning is the simulated run's** (MODEL; its parts: the counter's independence (RL,
`run_counter_indep`, false as first stated, open), the future's (the result holds no live label after [Return]), the
assignment's (a closed body), the hint (`hintM` of the goal, not deferred, is `globalTyS`'s reading), the reference's
state at the start being `emptyState` at the checker's counter, and `•` at a proposition (`constMean`)). -/
def ConstMeanAt (P : ProgState) (d : Def) (st' : MState) (w : ConstWit) : Prop :=
  ∀ (ρ : Assignment) (φ : Future) (r : Res) (s' : SState),
    runT (P.ctx dm D Γ st') ρ φ false (hintM (P.ctx dm D Γ st') ρ (some w.goal)) d.body (SM' (P.ctx dm D Γ st') ρ w.st₁) =
      some (r, s') →
    r.1 ∈ₛ[dm.read] (globalTyS (fun _ => .err) (P.ctx dm D Γ st') w.goal).m →
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
  have hfc : Strict.FundCtx (P.ctx dm D Γ st') := fundCtx_progCtx dm D Γ P st' hP.mem hP.lab hsorts
  obtain ⟨hpre, hrel, hsg, hvals, hab, hhb, hhole, hdt⟩ := hst' (fun _ => .err) noFuture
  have hall := hsteps (P.ctx dm D Γ st') noFuture (fun _ => ⟨hfc.globals, hfc.sorts⟩)
  obtain ⟨⟨ρ', Δ', π', r, s', -, hx, -, hstr, -, hpre', -, -, -⟩, -⟩ :=
    eval_all hall (fun _ => .err) w.n d.body w.st₁ w.st₂ true (some w.goal) w.v (some w.T) _ id hm (fun _ => htn) hsz
      (Or.inl htd) hpre hrel hsg hvals hab hhb hhole (fun h => by cases h) hdt w.bh hev
  rw [htn] at hx
  have hgood := (Strict.fund_all hfc d.body hvals false _ _ s' r hsg hx).1
  have hmem := hleaf ρ' Δ' r hpre' (hstr w.T rfl) hgood
  rw [hfind]
  exact hmean (fun _ => .err) noFuture r s' hx hmem

end

end Ochr.Meaning.Steps.Form.Top
