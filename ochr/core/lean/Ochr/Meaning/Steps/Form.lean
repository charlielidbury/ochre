import Ochr.Meaning.Steps.StrictSim
import Ochr.Meaning.Strict.Fund

/-!
# The form of the simulation's step statements (lead7, 2026-11-21; docs/31 D107)

Part (II) of the plan of record (docs/31 D86): the checker's successful run makes the STRICT reference
run (`Run.lean`'s `runT`) succeed, on related states. Membership is not the checker's business any
more: it lives on the reference state (`Strict.SGood`), which (I), the fundamental lemma
(`Strict.fund_all`), carries through every successful strict run. So a step

* assumes, of the checker's state, `Pre`: what the run context owes the state and does not change
  (`CtxS`), the checker's syntactic invariant (`Inv`: well-formedness and the typing of places), and
  the meaning-level facts about the unknowns (`Asg`: the assignment typed and on its path condition,
  the unknowns' types and the goal with levels, `Δ` the state's); NOT membership;
* assumes, of the reference state, `Rel` (`Steps/Sim.lean`) and `Strict.SGood`;
* concludes `Out`: the strict run of the term SUCCEEDS from the reference state, the checker's value
  means its result, the checker's type its type (`StrAgree`), and the states after are related, with
  the value in flight counted as a temporary at its stored type (main's D104, `MState.withTempT`),
  under an extension of the assignment, of `Δ` and of the renaming (`Ext`); and `Pre` again.

`SGood` after a step is NEVER concluded: it is (I)'s last conjunct, applied to the strict run the step
has just shown to succeed (`sim_seqS`, `Sim`). The reference run in the conclusion is at the step's
STARTING context and assignment: it reads only the unknowns its term holds (`runT_congrA`), which are
the starting state's (`Term.absBelow`), so a run built of sub-runs is a plain bind.
-/

namespace Ochr.Meaning.Steps.Form

open Ochr Ochr.Meaning Ochr.Meaning.Steps

/-! ## What a step assumes of the checker's state -/

/-- A frame without its temporaries' stored types (main's D104: the checker writes them and never
reads them, and nothing the simulation reads reads them either, `Steps/FormErase.lean`). -/
def _root_.Ochr.Frame.erase (fr : Frame) : Frame := { fr with tempTys := #[] }

/-- An environment without its temporaries' stored types. -/
def _root_.Ochr.Env.erase (env : Env) : Env := env.map Frame.erase

/-- **The kernel of a checker state**: Ω (but its temporaries' stored types), Σ, the declarations, the counters, Δ and its
frozen readings, the records, the goal and the reading mode; every other field at its default. The checker
carries much besides (the flags and one-shot readings `eval` hands down, the log, the editor's
locations); a step's hypotheses read only the kernel, so the bookkeeping a checker function does
around a sub-run changes nothing a step assumes. -/
def _root_.Ochr.MState.norm (st : MState) : MState :=
  { env := st.env.erase, globals := st.globals, inds := st.inds, nextLoan := st.nextLoan, nextAbs := st.nextAbs,
    absTy := st.absTy, absDecl := st.absDecl, refs := st.refs, etaRefs := st.etaRefs, goal := st.goal,
    neutrals := st.neutrals, liveScope := st.liveScope }

/-- What the run context owes the checker state and a check does not change: its declarations, a
data model covering and faithful to them, globals with no label, and Σ (`CtxOk` without the
per-state parts).

**One declaration list** (the lead's ruling, docs/31 D174, docs/34 §18.13): the context's list `K.Γ`
is the whole program's at every stage, and the checker's declarations at this stage are a PREFIX of
it (`inds`): a name the checker finds is found identically in the context (`Exists.find_of_prefix`),
and a term at this stage names only declared things (main's D118). The model covers the whole list;
faithfulness is asked for the checker's declarations only (`faithful`, `DeclsFaithful`): a later
declaration's field types may call globals not yet defined at this stage. -/
structure CtxS (K : RunCtx) (st : MState) : Prop where
  inds : st.inds <+: K.Γ
  covers : ∀ d ∈ K.Γ, K.dm.covers d
  faithful : DeclsFaithful K st.inds
  noLabel : ∀ n, (K.C.global n).2.label = none
  globals : GlobalsOk K st

/-- A function type written as one: a Π-type value whose code is a `pi` term. What `callType` and `declCallType` take
apart, and what the `let` of a deferred call takes as its record (`if let .tPi _ (.pi …) _`). -/
def _root_.Ochr.Value.piWritten : Value → Bool
  | .tPi _ (.pi ..) _ => true
  | _ => false

/-- A function value: a global function or a closure (not an unknown, a sealed program or `⋆` at a function type). -/
def _root_.Ochr.Value.isFnVal : Value → Bool
  | .gfn _ | .clo .. => true
  | _ => false

/-- A borrow type as written, in either form the checker writes one: the term `&A`, or an embedded type value that is a
borrow type (what `closeBlock` puts in a stuck block's function type). -/
def _root_.Ochr.Term.refWritten : Term → Bool
  | .ref _ => true
  | .val (.tRef _) => true
  | _ => false

/-- Component `j` of a Π-type written as one (parameter `j`, or the codomain at `j = |ds|`, as `Machine.bindTy?` reads a
deferred type) is a borrow type as written (`Term.refWritten`). -/
def _root_.Ochr.Value.refAt : Value → Nat → Bool
  | .tPi _ (.pi _ ds c) _, j => if j < ds.length then (ds[j]?.map Term.refWritten).getD false else c.refWritten
  | _, _ => false

/-- (K) at one binding (restated by machine12 on the lead's rulings R1 and R2, docs/31 D192, D194): a binding holding a
borrow stores `&A` where its type is stored, and where its type is deferred, `(P, ws, j)`, `P` is a Π written as one
whose component `j` is a borrow type as written. -/
def _root_.Ochr.Binding.KindAt (b : Binding) : Prop :=
  (∀ l c, b.val = .borrow l c → ∀ T, b.ty = some T → ∃ A, T = .tRef A) ∧
  (∀ l c, b.val = .borrow l c → b.ty = none → ∀ P ws j, b.lazyTy = some (P, ws, j) → P.refAt j = true)

/-- (K) for a value and the type it is held at, if any: what a binder pushing `v` at `T?` keeps. -/
def _root_.Ochr.Value.KindOf (v : Value) (T? : Option Value) : Prop :=
  ∀ T, T? = some T → ∀ l c, v = .borrow l c → ∃ A, T = .tRef A

/-- **(K) A binding holding a borrow has a borrow type** (the lead's ruling, docs/31 D188; restated by machine12 on the
lead's ruling R1, docs/31 D192), about the checker's state alone:
* a binding holding a borrow (`borrow_ℓ c`; a loan `loan_ℓ` and a lent mark `lent_ℓ c` are the LENDER's side and are
  asked nothing: a lender stores its content's type) whose type is stored stores a borrow type `&A`;
* a binding holding a borrow whose type is DEFERRED (`lazyTy = (P, ws, j)`, `ty = none`) defers a borrow type as written
  (the lead's ruling R2, re-ruled, docs/31 D194): `P` is a Π-type written as one whose parameter `j` (or codomain, at
  `j = |ds|`) is the term `&A` or an embedded borrow type value (`closeBlock` writes a stuck block's codomain as
  `.val (&A)`: the first wording, the term only, failed on 42 reachable states of `CloseOffModel`, docs/31 D192). Fixed
  by the state's text; by the checker's D48 (`&` only as the whole declared type of a parameter, a result or an
  annotated term) the deferred type evaluates to `&A'`. Reached in a sealed program's re-run (ClosingOff's
  `AddToOneZero''`, `CoBlockBorrow`);
* a binding with neither a stored nor a deferred type is asked nothing;
* function values and globals are asked nothing (R1: the one consumer of "a function value sits at a function type"
  was the deferred call's record, `LaterPiG`, which the checker itself tests from main's D134).
Temporaries are not positions of this clause: `Inv` reads the kernel (`MState.norm`), which erases their stored types
(main's D104: written, never read). Checked on the checker's own states (`lake exe sweep --deep-private`, its clause
(K), mirrored; docs/31 D188, D192). -/
def KindTyped (st : MState) : Prop :=
  ∀ (f i : Nat) (b : Binding), st.env[f]?.bind (fun fr => fr.binds[i]?) = some b → b.KindAt

/-- The checker's syntactic invariant: the clauses of well-formedness (part (c)) that read no meaning
(all but (WF7) and (WF9), which read types' meanings and join `Asg` when a step needs them), the
checker's typing of places, the label counter above every label that occurs (borrows included;
(WF6) bounds the loans: a step whose private computation advances the counter keeps the relation by
it), and (K), a binding's stored type has its value's kind (`KindTyped`, docs/31 D188). Read off the checker and swept; its preservation is a fact about the
checker alone, given the decisions (`D`) and the declarations (`Γ`), which no extension changes. -/
def Inv (D : Decisions) (Γ : List IndDecl) (st : MState) : Prop :=
  WF1 st.env ∧ WF2 st.env ∧ WF3 st.env ∧ WF4 st.env ∧ WF6 st ∧ WF8 st ∧ WF10 Γ st ∧ WF11 st ∧
    WF12 st.env ∧ WF14 st.env ∧ WF15 st.env ∧ WF16 Γ st ∧ ShapeFacts D Γ st ∧
    (∀ l, st.Occurs l → l < st.nextLoan) ∧ KindTyped st

/-- The meaning-level facts about the unknowns of the checker's state: the assignment is typed and on
the path condition, the unknowns' types and the goal have levels, and `Δ` is the state's. -/
structure Asg (K : RunCtx) (ρ : Assignment) (st : MState) : Prop where
  asg : TypedAssignment K.dm K.M K.Γ ρ st
  absLv : ∀ σ, st.Refd σ → σ < st.absTy.size → (MState.absTyM K.dm K.M K.Γ ρ st σ).level.isSome
  goalLv : ∀ G, MState.goalM K.dm K.M K.Γ ρ st = some G → G.level.isSome
  delta : DeltaOk K ρ st

/-- **What a step assumes of the checker's state** (no membership: that is the reference state's),
read off its kernel (`MState.norm`). -/
structure Pre (K : RunCtx) (ρ : Assignment) (st : MState) : Prop where
  ctx : CtxS K st.norm
  inv : Inv K.D K.Γ st.norm
  asg : Asg K ρ st.norm

/-! ## What a step hands on -/

/-- **The extension a step hands on**: the tables only grew; the assignment and `Δ` agree with the
old ones on the unknowns of the starting state, the renaming on the labels it had issued. -/
structure Ext (K : RunCtx) (ρ : Assignment) (π : Nat → Nat) (st st' : MState)
    (ρ' : Assignment) (Δ' : Nat → TyS) (π' : Nat → Nat) : Prop where
  abs : st.absTy.size ≤ st'.absTy.size
  lab : st.nextLoan ≤ st'.nextLoan
  agree : ∀ σ, σ < st.absTy.size → ρ' σ = ρ σ ∧ Δ' σ = K.Δ σ
  ren : ∀ l, l < st.nextLoan → π' l = π l

theorem Ext.refl (K : RunCtx) (ρ : Assignment) (π : Nat → Nat) (st : MState) :
    Ext K ρ π st st ρ K.Δ π :=
  ⟨Nat.le_refl _, Nat.le_refl _, fun _ _ => ⟨rfl, rfl⟩, fun _ _ => rfl⟩

/-- Extensions compose. -/
theorem Ext.trans {K : RunCtx} {ρ ρ₁ ρ₂ : Assignment} {Δ₁ Δ₂ : Nat → TyS} {π π₁ π₂ : Nat → Nat}
    {st st₁ st₂ : MState} (h₁ : Ext K ρ π st st₁ ρ₁ Δ₁ π₁) (h₂ : Ext { K with Δ := Δ₁ } ρ₁ π₁ st₁ st₂ ρ₂ Δ₂ π₂) :
    Ext K ρ π st st₂ ρ₂ Δ₂ π₂ where
  abs := Nat.le_trans h₁.abs h₂.abs
  lab := Nat.le_trans h₁.lab h₂.lab
  agree := fun σ hσ => by
    obtain ⟨a₂, d₂⟩ := h₂.agree σ (Nat.lt_of_lt_of_le hσ h₁.abs)
    obtain ⟨a₁, d₁⟩ := h₁.agree σ hσ
    exact ⟨a₂.trans a₁, d₂.trans d₁⟩
  ren := fun l hl => (h₂.ren l (Nat.lt_of_lt_of_le hl h₁.lab)).trans (h₁.ren l hl)

/-- The borrow a value holds, as its position's shape reads it. -/
def _root_.Ochr.Value.heldLabel : Value → Option Nat
  | .borrow l _ => some l
  | _ => none

/-- **(II)'s conclusion** for a step of the checker from `st` to `st'` returning `v` at `T?`, against
the reference computation `x` from `s` (at the step's starting context): `x` SUCCEEDS; the checker's
value, read at the run's future pulled back along the renaming, is its result; the checker's type is
its type; the result's label is the borrow the checker's value holds, renamed (a `let` moves the
holder into its binding on both sides by it); the checker's state after, with `v` in flight at `T?`, meets `Pre` and is related to the
reference state after. -/
def Out (K : RunCtx) (ρ : Assignment) (φ : Future) (π : Nat → Nat) (st st' : MState) (s : SState)
    (x : SM Res) (v : Value) (T? : Option Value) : Prop :=
  ∃ (ρ' : Assignment) (Δ' : Nat → TyS) (π' : Nat → Nat) (r : Res) (s' : SState),
    Ext K ρ π st st' ρ' Δ' π' ∧ x s = some (r, s') ∧
    meanV { K with Δ := Δ' } ρ' (fun l => φ (π' l)) r.2 v = r.1 ∧
    (∀ T, T? = some T → StrAgree { K with Δ := Δ' } ρ' T r.2) ∧
    r.2.label = (Value.heldLabel v).map π' ∧
    Pre { K with Δ := Δ' } ρ' (st'.withTempT v T?) ∧
    Rel { K with Δ := Δ' } ρ' φ π' (st'.withTempT v T?) s'

/-- **A reference computation simulates a checker step**: from every reference state related to the
checker's and good, the step's conclusion. -/
def Sim (K : RunCtx) (ρ : Assignment) (φ : Future) (st st' : MState) (x : SM Res) (v : Value)
    (T? : Option Value) : Prop :=
  ∀ (s : SState) (π : Nat → Nat), Pre K ρ st → Rel K ρ φ π st s → Strict.SGood K.dm K.Γ φ s →
    Out K ρ φ π st st' s x v T?

/-! ## Composition -/

/-- **Two steps compose** (the strict form of `sim_seq`). The first step's conclusion, from a good
reference state; (I) at the first computation (`hI`), which makes the reference state between the two
good; and the second step from any state the first can hand on. The second step's computation is
given at the starting context (`x₂ r`): the caller moves it there from its own (`runT_congrA`). -/
theorem sim_seqS {K : RunCtx} {ρ : Assignment} {φ : Future} {π : Nat → Nat} {st st₁ st₂ : MState}
    {s : SState} {x₁ : SM Res} {x₂ : Res → SM Res} {v₁ v₂ : Value} {T₁ T₂ : Option Value}
    (hS : Strict.SGood K.dm K.Γ φ s) (hI : Strict.FundAt K.dm K.Γ φ x₁)
    (h₁ : Out K ρ φ π st st₁ s x₁ v₁ T₁)
    (h₂ : ∀ ρ₁ Δ₁ π₁ r s₁, Ext K ρ π st st₁ ρ₁ Δ₁ π₁ → x₁ s = some (r, s₁) →
      meanV { K with Δ := Δ₁ } ρ₁ (fun l => φ (π₁ l)) r.2 v₁ = r.1 →
      (∀ T, T₁ = some T → StrAgree { K with Δ := Δ₁ } ρ₁ T r.2) →
      r.2.label = (Value.heldLabel v₁).map π₁ →
      Pre { K with Δ := Δ₁ } ρ₁ (st₁.withTempT v₁ T₁) → Rel { K with Δ := Δ₁ } ρ₁ φ π₁ (st₁.withTempT v₁ T₁) s₁ →
      Strict.SGood K.dm K.Γ φ s₁ →
      Out { K with Δ := Δ₁ } ρ₁ φ π₁ st₁ st₂ s₁ (x₂ r) v₂ T₂) :
    Out K ρ φ π st st₂ s (x₁ >>= x₂) v₂ T₂ := by
  obtain ⟨ρ₁, Δ₁, π₁, r, s₁, he₁, hx₁, hm₁, ha₁, hl₁, hp₁, hr₁⟩ := h₁
  have hS₁ : Strict.SGood K.dm K.Γ φ s₁ := (hI s s₁ r hS hx₁).2.2.2
  obtain ⟨ρ₂, Δ₂, π₂, r₂, s₂, he₂, hx₂, hm₂, ha₂, hl₂, hp₂, hr₂⟩ := h₂ ρ₁ Δ₁ π₁ r s₁ he₁ hx₁ hm₁ ha₁ hl₁ hp₁ hr₁ hS₁
  refine ⟨ρ₂, Δ₂, π₂, r₂, s₂, he₁.trans he₂, ?_, hm₂, ha₂, hl₂, hp₂, hr₂⟩
  simp only [Bind.bind]
  rw [hx₁]
  exact hx₂

/-! ## The evaluation step

The evaluation step's statement is `Master.EvalAt` (`Steps/Master.lean`). The `eval_sim` that stood here
quantified over every mode and every handed-down reading, and was false (docs/31 D150, D154). -/

end Ochr.Meaning.Steps.Form
