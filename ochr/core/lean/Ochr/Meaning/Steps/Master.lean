import Ochr.Meaning.Steps.FormTail
import Ochr.Meaning.Steps.Column
import Ochr.Meaning.Steps.ColumnC

/-!
# The master induction of (II): the general step, by term former (lead22, 2026-11-22; docs/31 D150)

The checker's `eval` and `checkTail` recurse on fuel (one mutual block, `Machine.lean`), so (II) for
every term is one strong induction on fuel. This file fixes the statement that induction proves, its
induction hypothesis, and the list of what remains: one named step per term former of `eval` (the 26
constructors of `Term`) and one per shape `checkTail` matches (six), each "from the induction
hypothesis at every smaller fuel, the statement at this fuel for terms of this former". The induction
itself (`master`) is proved with no `sorry`; it ASSUMES the 32 step statements, bundled as `AllSteps`.

## The statement: `EvalAt`

`EvalAt K ρ φ n t` is the evaluation step at fuel `n` for one term. It is what `Form.lean`'s `eval_sim` stated,
for one term, with TWO more hypotheses (ruling (a) of docs/31 D150; `eval_sim` is deleted, D154), without which
the statement is false:

* `ModeR st` (no head evaluation, not copying, not in place; the erased depth free, D155). `Pre` reads the state's kernel (`MState.norm`),
  which forgets the mode, so `eval_sim` quantified over every mode; but in copying mode (inside `clone`) or in
  place (a call's head) the checker's read of a place of a non-copy type leaves the place as it was, where the
  reference's plain run of the same term moves it, and the states after are not related. Smallest program:
  `let x = S(Z); let y = clone(x); x`, at the read of `x` inside `clone` (`MasterGuards`).
* the reading handed down (`tailDecl`) is none or the table's reading of the term. A sequencing form hands its
  tail its own reading; a reading handed down that is not the table's would make the checker's pre-pass erase
  a term the reference runs.

`EvalAt` does NOT take `Column.EvalSim`'s hypothesis that the aligned table leaves the term unerased: the
master statement is for every term, erased ones included (each step owns its erased case).

**What a successful run keeps** (`Kept`, ruling (e) of D150; D154): its conclusion has, beside `Out`, that the
run ends in the mode it started in, with the frames and the top frame's readings it started with. Each step
proves it from its own facts and its sub-runs' induction hypotheses, so it is no whole-machine fact about the
checker (lead22's `EvalTop` was one, and is gone).

The statement for a run in tail position, `TailAt`, is `Form.TailSim` with the entry conditions of
`EvalAt` that a typed run needs (no `hok`: `checkTail` runs typed), and `Kept` at the leaf where the
continuation runs (`TailOutK`).

## The induction hypothesis, and why it has this shape

`IH K φ n`: at every fuel below `n`, at EVERY `Δ` and assignment, `EvalAt` and `TailAt` for EVERY term.
* Every fuel below: `eval (n + 1)` runs `evalAt n`, which runs `evalCore (n - 1)`, whose sub-runs are at
  `n - 2` or below through the helpers (`evalMatch`, `evalCall`, `closeBlock`, `runBody`, …); each step
  decides how far down its sub-runs are.
* Every `Δ` and assignment: a sub-run after the first starts under the extension the earlier ones
  handed on (`Ext`: `ρ'`, `Δ'`), as the fragment's `let` and `;` cases take their tails' hypotheses
  (`FragLet.letF_core`'s `ihw`). The other fields of the context (`dm`, `Γ`, `C`, `D`, `Λ`, `cur`) stay
  fixed within one check: a recursive function's stage changes `C` and `cur` (column `R`), but only
  between checks, outside this induction (the knot's induction on the bound is outside it).
* Both statements in one induction: `checkTail`'s default case runs `eval`, and `eval` reaches
  `checkTail` through `.fix` (`checkFix`), so the two are mutually recursive on fuel; one strong
  induction on the conjunction covers both, and no second induction is needed.
* Typed and untyped runs alike: an in-place call runs the callee's body untyped (`runBody`), so the
  hypothesis covers `typed = false`, with the strict run's success (`hok`) as its entry condition.
* The decision table: `DecTab K.D st'` at the END of each sub-run, which every step gets from its own
  end by `DecTab.back` (the checker's runs only extend the tables), the callee's body in place included.

The erased depth (ruling (b) of D150, applied in D155): the statements hold at EVERY erased depth (`ModeR`), so
the hypothesis covers the sub-runs one depth down: an erased term's `evalCore` (`inStatement`), the body of a
function whose calls are erased (`withErasedIf`), `clone`/`peek`'s operand (`withErased`). What it does NOT cover:
a sub-run in copying mode or in place (`clone`/`peek`'s operand under `withCopying`, a call's head); those steps
need their own statement (`clone`/`peek` of a place reads in place on both sides).
-/

namespace Ochr.Meaning.Steps.Form.Master

open Ochr Ochr.Meaning Ochr.Meaning.Steps Ochr.Meaning.Steps.Form

/-! ## What a successful run keeps -/

theorem _root_.Ochr.Meaning.Steps.Form.ModeEq.rfl' (a : MState) : ModeEq a a := ⟨rfl, rfl, rfl, rfl⟩

theorem _root_.Ochr.Meaning.Steps.Form.ModeEq.symm {a b : MState} (h : ModeEq a b) : ModeEq b a :=
  ⟨h.headEval.symm, h.copying.symm, h.inPlace.symm, h.erased.symm⟩

theorem _root_.Ochr.Meaning.Steps.Form.ModeEq.trans {a b c : MState} (h₁ : ModeEq a b) (h₂ : ModeEq b c) : ModeEq a c :=
  ⟨h₁.headEval.trans h₂.headEval, h₁.copying.trans h₂.copying, h₁.inPlace.trans h₂.inPlace,
    h₁.erased.trans h₂.erased⟩

/-- Two states in the plain mode are in one mode. -/
theorem _root_.Ochr.Meaning.Steps.Form.ModeEq.of_modes {a b : MState} (ha : Mode a) (hb : Mode b) : ModeEq a b :=
  ⟨ha.headEval.trans hb.headEval.symm, ha.copying.trans hb.copying.symm, ha.inPlace.trans hb.inPlace.symm,
    ha.erased.trans hb.erased.symm⟩

/-- **The mode at any erased depth** (ruling (b) of docs/31 D150; D155): no head evaluation, not copying, not in
place; the erased depth is FREE. `EvalAt` and `TailAt` are stated at it, because the checker runs every erased
term (`inStatement`), a function body whose calls are erased (`withErasedIf`) and `clone`'s operand one depth
down, and the hypothesis must cover those sub-runs. The checker reads the depth only in the runtime checks K2/K3
(`atRuntime`) and the capture-move checks (`readPlace`, `capture`), each of which rejects at depth `0` only; the
reference reads none of them (D155). -/
structure ModeR (st : MState) : Prop where
  headEval : st.headEval = false
  copying : st.copying = false
  inPlace : st.inPlace = false

theorem _root_.Ochr.Meaning.Steps.Form.Mode.toR {st : MState} (h : Mode st) : ModeR st := ⟨h.headEval, h.copying, h.inPlace⟩

theorem ModeR.of_modeEq {a b : MState} (hm : ModeR a) (h : ModeEq a b) : ModeR b :=
  ⟨h.headEval ▸ hm.headEval, h.copying ▸ hm.copying, h.inPlace ▸ hm.inPlace⟩

/-- **What a successful run keeps** (docs/31 D154; ruling (e) of D150): the mode it started in, its frames
(their number), and the top frame's readings. A conjunct of `EvalAt`'s conclusion beside `Out`, and of
`TailAt`'s at the leaf: each step proves it from its own facts and its sub-runs' induction hypotheses. -/
structure Kept (a b : MState) : Prop where
  mode : ModeEq a b
  size : b.env.size = a.env.size
  top : DecideScope.topReadings b = DecideScope.topReadings a

theorem Kept.rfl' (a : MState) : Kept a a := ⟨ModeEq.rfl' a, rfl, rfl⟩

theorem Kept.trans {a b c : MState} (h₁ : Kept a b) (h₂ : Kept b c) : Kept a c :=
  ⟨h₁.mode.trans h₂.mode, h₂.size.trans h₁.size, h₂.top.trans h₁.top⟩

/-- Bookkeeping that keeps the kernel and the mode keeps what `Kept` asks. -/
theorem Kept.of_kern {a b : MState} (hk : Kern a b) (hm : ModeEq a b) : Kept a b :=
  ⟨hm, (ColumnC.size_of_erase hk.env).symm, (ColumnC.topReadings_kern hk).symm⟩

/-! ## The statements -/

/-- **The hint names only the state's unknowns** (the lead's ruling on docs/31 D176, D179): every unknown of the
handed-down type is below the counter. The same condition `absBelow` puts on the term, on the other thing a run is
handed. In tail position an untyped `let`/`;` hands its tail the hint after its first sub-run has extended the
assignment above the counter, and moving the tail's run back (`runT_congrA`) needs the hint's meaning unchanged. -/
def HintBelow (hint : Option Value) (n : Nat) : Prop := ∀ T, hint = some T → ∀ σ, T.hasAbs σ = true → σ < n

theorem hintBelow_none (n : Nat) : HintBelow none n := fun _ h => by cases h

theorem HintBelow.mono {hint : Option Value} {a b : Nat} (h : HintBelow hint a) (hab : a ≤ b) : HintBelow hint b :=
  fun T hT σ hσ => Nat.lt_of_lt_of_le (h T hT σ hσ) hab

/-- **A deferred call type means the reference's result type** (the lead's ruling on docs/31 D180; D183): for a run
of a CALL from a state with the deferral flag set and the record clear (`deferCallTy`, `callTyLater`: how an untyped
`let` of a call starts it, `Machine.LetCallInvU`), a pair `(P, ws)` the end state records, `P` a Π-type with `|ds|`
domains, reads at its codomain (`CodeMeaning.paramTy`, as `Env.hintAt` reads a lazily typed binding) as the
reference's result type `R`. Vacuous for every other term and every other start: the checker does not clear the
record on entry, so a run that is not such a call can end with a stale record (`LaterGuards`), which no consumer
reads (the `let` clears it before its call and reads it right after). -/
def LaterOk (K : RunCtx) (ρ : Assignment) (t : Term) (st st' : MState) (R : TyS) : Prop :=
  (∃ f as hd, t = .call f as hd) → st.deferCallTy = true → st.callTyLater = none →
    ∀ caps hs ds cod rd ws, st'.callTyLater = some (.tPi caps (.pi hs ds cod) rd, ws) →
      K.M.paramTy ρ (.tPi caps (.pi hs ds cod) rd) ws ds.length = R

theorem laterOk_of_not_call {K : RunCtx} {ρ : Assignment} {t : Term} {st st' : MState} {R : TyS}
    (ht : ∀ f as hd, t ≠ .call f as hd) : LaterOk K ρ t st st' R :=
  fun ⟨f, as, hd, e⟩ => absurd e (ht f as hd)

/-- **`Out` with the deferred type** (the lead's ruling on D180; D183): `Out`, and inside its existential, at its
extended context and assignment, `LaterOk` for the run of `t`. `EvalAt`'s conclusion. -/
def OutL (K : RunCtx) (ρ : Assignment) (φ : Future) (π : Nat → Nat) (st st' : MState) (s : SState)
    (x : SM Res) (v : Value) (T? : Option Value) (t : Term) : Prop :=
  ∃ (ρ' : Assignment) (Δ' : Nat → TyS) (π' : Nat → Nat) (r : Res) (s' : SState),
    Ext K ρ π st st' ρ' Δ' π' ∧ x s = some (r, s') ∧
    meanV { K with Δ := Δ' } ρ' (fun l => φ (π' l)) r.2 v = r.1 ∧
    (∀ T, T? = some T → StrAgree { K with Δ := Δ' } ρ' T r.2) ∧
    r.2.label = (Value.heldLabel v).map π' ∧
    Pre { K with Δ := Δ' } ρ' (st'.withTempT v T?) ∧
    Rel { K with Δ := Δ' } ρ' φ π' (st'.withTempT v T?) s' ∧
    LaterOk { K with Δ := Δ' } ρ' t st st' r.2

theorem OutL.out {K : RunCtx} {ρ : Assignment} {φ : Future} {π : Nat → Nat} {st st' : MState} {s : SState}
    {x : SM Res} {v : Value} {T? : Option Value} {t : Term} (h : OutL K ρ φ π st st' s x v T? t) :
    Out K ρ φ π st st' s x v T? :=
  let ⟨ρ', Δ', π', r, s', he, hx, hm, ha, hl, hp, hr, _⟩ := h
  ⟨ρ', Δ', π', r, s', he, hx, hm, ha, hl, hp, hr⟩

theorem OutL.of_out {K : RunCtx} {ρ : Assignment} {φ : Future} {π : Nat → Nat} {st st' : MState} {s : SState}
    {x : SM Res} {v : Value} {T? : Option Value} {t : Term} (ht : ∀ f as hd, t ≠ .call f as hd)
    (h : Out K ρ φ π st st' s x v T?) : OutL K ρ φ π st st' s x v T? t :=
  let ⟨ρ', Δ', π', r, s', he, hx, hm, ha, hl, hp, hr⟩ := h
  ⟨ρ', Δ', π', r, s', he, hx, hm, ha, hl, hp, hr, laterOk_of_not_call ht⟩

/-- `EvalAt`'s conclusion read as `Out`'s (every consumer but the `let` of a call). -/
theorem outK_of_outLK {K : RunCtx} {ρ : Assignment} {φ : Future} {π : Nat → Nat} {st st' : MState} {s : SState}
    {x : SM Res} {v : Value} {T? : Option Value} {t : Term} (h : OutL K ρ φ π st st' s x v T? t ∧ Kept st st') :
    Out K ρ φ π st st' s x v T? ∧ Kept st st' :=
  ⟨h.1.out, h.2⟩

/-- A step for a term that is not a call concludes `EvalAt`'s form from `Out`'s. -/
theorem outLK_of_outK {K : RunCtx} {ρ : Assignment} {φ : Future} {π : Nat → Nat} {st st' : MState} {s : SState}
    {x : SM Res} {v : Value} {T? : Option Value} {t : Term} (ht : ∀ f as hd, t ≠ .call f as hd)
    (h : Out K ρ φ π st st' s x v T? ∧ Kept st st') : OutL K ρ φ π st st' s x v T? t ∧ Kept st st' :=
  ⟨OutL.of_out ht h.1, h.2⟩

/-- **The evaluation step at fuel `n`, for one term**: from a state in the plain mode at any erased depth
(`ModeR`) with a frame,
whose handed-down reading, if any, is the table's reading of `t`, meeting `Pre`, related to a good reference
state, the checker's successful run of `eval` makes the reference's run of `t` succeed (`Out`, with the deferred
type a call records: `OutL`, D183), and the run keeps the mode, the frames and the top frame's readings (`Kept`). -/
def EvalAt (K : RunCtx) (ρ : Assignment) (φ : Future) (n : Nat) (t : Term) : Prop :=
  ∀ (st st' : MState) (typed : Bool) (hint : Option Value) (v : Value) (T? : Option Value) (s : SState)
    (π : Nat → Nat),
    ModeR st → (typed = true → st.tailNext = false) → 0 < st.env.size →
    (st.tailDecl = none ∨ st.tailDecl = some (K.D.declOf (DecideScope.topReadings st) t)) →
    Pre K ρ st → Rel K ρ φ π st s → Strict.SGood K.dm K.Γ φ s →
    t.valsOk (Strict.ValsP K ρ φ) → t.absBelow st.absTy.size → HintBelow hint st.absTy.size → t.hasHolePrim = false →
    (typed = false → (runT K ρ φ st.tailNext (hintM K ρ hint) t s).isSome) →
    DecTab K.D st' →
    ∀ bh, Runs (Ochr.eval n typed t hint) st bh (v, T?) st' →
    OutL K ρ φ π st st' s (runT K ρ φ st.tailNext (hintM K ρ hint) t) v T? t ∧ Kept st st'

/-- **A tail step's conclusion, with what the run keeps**: `TailOut` (some leaf `stl` where the continuation
ran, `Out` there) with `Kept` from the start to the leaf. -/
def TailOutK (K : RunCtx) (ρ : Assignment) (φ : Future) (π : Nat → Nat) (st : MState) (s : SState) (x : SM Res)
    (k : Value → Value → M Unit) : Prop :=
  ∃ (stl : MState) (v T : Value), (∃ bk stk, Runs (k v T) stl bk () stk) ∧ Out K ρ φ π st stl s x v (some T) ∧
    Kept st stl

theorem TailOutK.tailOut {K : RunCtx} {ρ : Assignment} {φ : Future} {π : Nat → Nat} {st : MState} {s : SState}
    {x : SM Res} {k : Value → Value → M Unit} (h : TailOutK K ρ φ π st s x k) : TailOut K ρ φ π st s x k :=
  let ⟨stl, v, T, hk, hO, _⟩ := h
  ⟨stl, v, T, hk, hO⟩

/-- **The tail step at fuel `n`, for one term**: `Form.TailSim` for `t` with every continuation that only
extends the tables (`GrowsM`: so the table aligned at the run's end, after the continuation, is aligned at
each leaf, `DecTab.back`; `checkFix`'s continuation and every one `checkTail` builds from it are machine
code), from a state in the plain mode at any erased depth with no reading handed down, for a term the strict run accepts the
embedded values of, holding the state's unknowns and no hole; the leaf keeps what `Kept` asks. -/
def TailAt (K : RunCtx) (ρ : Assignment) (φ : Future) (n : Nat) (t : Term) : Prop :=
  ∀ (st : MState) (k : Value → Value → M Unit) (s : SState) (π : Nat → Nat) (bh : Nat) (st' : MState),
    ModeR st → st.tailNext = false → 0 < st.env.size → st.tailDecl = none → (∀ v T, GrowsM (k v T)) →
    Pre K ρ st → Rel K ρ φ π st s → Strict.SGood K.dm K.Γ φ s →
    t.valsOk (Strict.ValsP K ρ φ) → t.absBelow st.absTy.size → t.hasHolePrim = false →
    DecTab K.D st' →
    Runs (Ochr.checkTail n t k) st bh () st' →
    TailOutK K ρ φ π st s (runT K ρ φ true (hintM K ρ st.goal) t) k

/-- **The induction hypothesis at fuel `n`**: at every smaller fuel, every `Δ` and every assignment, the
evaluation step and the tail step for every term. -/
def IH (K : RunCtx) (φ : Future) (n : Nat) : Prop :=
  ∀ m, m < n → ∀ (Δ : Nat → TyS) (ρ : Assignment),
    (∀ t, EvalAt { K with Δ := Δ } ρ φ m t) ∧ (∀ t, TailAt { K with Δ := Δ } ρ φ m t)

/-! ## The column's forms with what a run keeps

`CoreSimK` and `EvalSimK` are `Column.CoreSim` and `Column.EvalSim` at any erased depth (`ModeR` for `Mode`)
with `Kept` beside `Out`: the forms a general step proves for a class of states before it is closed into
`EvalAt`. -/

/-- `Column.CoreSim` at any erased depth, with `Kept`. -/
def CoreSimK (K : RunCtx) (ρ : Assignment) (φ : Future) (n : Nat) (t : Term) (P : MState → Prop := fun _ => True)
    (TY : Bool → Prop := fun _ => True) : Prop :=
  ∀ (st st' : MState) (typed : Bool) (hint : Option Value) (v : Value) (T? : Option Value) (s : SState)
    (π : Nat → Nat),
    P st → TY typed → ModeR st → (typed = true → st.curTail = false) → st.tailNext = false → st.tailDecl = none →
    st.curDecl = some (K.D.declOf (DecideScope.topReadings st) t) → Pre K ρ st → Rel K ρ φ π st s →
    Strict.SGood K.dm K.Γ φ s →
    t.valsOk (Strict.ValsP K ρ φ) → t.absBelow st.absTy.size → HintBelow hint st.absTy.size → t.hasHolePrim = false →
    K.D.flags (scopeOf s) t = (false, false) →
    (typed = false → (runT K ρ φ st.curTail (hintM K ρ hint) t s).isSome) →
    DecTab K.D st' →
    ∀ bh, Runs (Ochr.evalCore n typed t hint) st bh (v, T?) st' →
    Out K ρ φ π st st' s (runT K ρ φ st.curTail (hintM K ρ hint) t) v T? ∧ Kept st st'

/-- `Column.EvalSim` at any erased depth, with `Kept`. -/
def EvalSimK (K : RunCtx) (ρ : Assignment) (φ : Future) (n : Nat) (t : Term) (P : MState → Prop := fun _ => True)
    (TY : Bool → Prop := fun _ => True) : Prop :=
  ∀ (st st' : MState) (typed : Bool) (hint : Option Value) (v : Value) (T? : Option Value) (s : SState)
    (π : Nat → Nat),
    P st → TY typed → ModeR st → (typed = true → st.tailNext = false) →
    (st.tailDecl = none ∨ st.tailDecl = some (K.D.declOf (DecideScope.topReadings st) t)) →
    Pre K ρ st → Rel K ρ φ π st s → Strict.SGood K.dm K.Γ φ s →
    t.valsOk (Strict.ValsP K ρ φ) → t.absBelow st.absTy.size → HintBelow hint st.absTy.size → t.hasHolePrim = false →
    K.D.flags (scopeOf s) t = (false, false) →
    (typed = false → (runT K ρ φ st.tailNext (hintM K ρ hint) t s).isSome) →
    DecTab K.D st' →
    ∀ bh, Runs (Ochr.eval n typed t hint) st bh (v, T?) st' →
    Out K ρ φ π st st' s (runT K ρ φ st.tailNext (hintM K ρ hint) t) v T? ∧ Kept st st'

/-- **`eval` around `evalCore`, at any erased depth** (a fact about the checker alone; `Machine.EvalInvR` with
`ModeR` for `Mode` and the mode's equalities for its `Mode` conclusions; PROVED, `MasterDepth.evalInvD`, by
`EvalInvR`'s proof: `evalAt`'s code reads no depth). -/
def EvalInvD : Prop :=
  ∀ (n : Nat) (typed : Bool) (t : Term) (hint : Option Value) (st st' : MState) (bh : Nat) (v : Value)
    (T? : Option Value) (D : Decisions),
    ModeR st → DecTab D st' → (∀ w, t ≠ .val w) → (∀ f as h, t ≠ .call f as h) →
    D.declOf (DecideScope.topReadings st) t ≠ .any → (D.declOf (DecideScope.topReadings st) t).isProof = false →
    (st.tailDecl = none ∨ st.tailDecl = some (D.declOf (DecideScope.topReadings st) t)) →
    Runs (Ochr.eval (n + 2) typed t hint) st bh (v, T?) st' →
    ∃ (st₀ st₁ : MState) (bh' : Nat), Kern st st₀ ∧ ModeEq st st₀ ∧ st₀.curTail = st.tailNext ∧
      st₀.tailNext = false ∧ st₀.tailDecl = none ∧ st₀.curDecl = some (D.declOf (DecideScope.topReadings st₀) t) ∧
      Runs (Ochr.evalCore n typed t hint) st₀ bh' (v, T?) st₁ ∧ Kern st₁ st' ∧ ModeEq st₁ st'

/-- **`eval` around `evalCore`, with what the run keeps**: `Column.eval_of_core` at any erased depth, carrying
`Kept` (the mode by `EvalInvD`'s equalities, the frames and readings by the kernel). -/
theorem eval_of_coreK {K : RunCtx} {ρ : Assignment} {φ : Future} (hE : EvalInvD) {n : Nat} {t : Term}
    {P : MState → Prop} {TY : Bool → Prop}
    (hP : ∀ a b, Kern a b → P a → P b) (ht : ∀ w, t ≠ .val w) (hcall : ∀ f as h, t ≠ .call f as h)
    (hany : ∀ st, P st → K.D.declOf (DecideScope.topReadings st) t ≠ .any ∧
      (K.D.declOf (DecideScope.topReadings st) t).isProof = false) (hc : CoreSimK K ρ φ n t P TY) :
    EvalSimK K ρ φ (n + 2) t P TY := by
  intro st st' typed hint v T? s π hPs hty hm htl htd hp hr hS hv hab hhb hnh hfl hok hD bh h
  obtain ⟨st₀, st₁, bh', hk₀, hm₀, hct, htn, htd₀, hcd₀, h₀, hk₁, hm₁⟩ :=
    hE n typed t hint st st' bh v T? K.D hm hD ht hcall (hany st hPs).1 (hany st hPs).2 htd h
  obtain ⟨hc', hkp⟩ := hc st₀ st₁ typed hint v T? s π (hP st st₀ hk₀ hPs) hty (hm.of_modeEq hm₀) (fun e => hct.trans (htl e)) htn htd₀ hcd₀ (hp.of_kern hk₀)
    (hr.of_kern hk₀) hS hv
    (by rw [← hk₀.absTy]; exact hab) (by rw [← hk₀.absTy]; exact hhb) hnh hfl (by rw [hct]; exact hok)
    (DecTab.of_kern hk₁.symm hD) bh' h₀
  rw [hct] at hc'
  exact ⟨Out.of_kern hk₀ hk₁ hc', ((Kept.of_kern hk₀ hm₀).trans hkp).trans (Kept.of_kern hk₁ hm₁)⟩

/-! ## The shapes `checkTail` matches -/

/-- The terms `Machine.checkTailAt` treats by their shape: `let`, `;`, the two matches, and the
primitives `split f in u`, `split f { … }`, `rewrite`/`rewriteR` with two arguments. Every other term in
tail position is evaluated (`eval fuel' true t goal`) and handed to the continuation. The patterns are
`checkTailAt`'s, in its order. -/
def tailShaped : Term → Bool
  | .letIn .. | .seq .. | .matchNat .. | .matchInd .. => true
  | .prim "split" [.const _, _] => true
  | .prim "splitArms" [.const _, .letIn ..] => true
  | .prim "rewrite" [_, _] | .prim "rewriteR" [_, _] => true
  | _ => false

/-! ## The steps, one per term former of `eval`

Each is "from the induction hypothesis at fuel `n`, at every `Δ` and assignment, `EvalAt` at fuel `n`
for every term of this former". -/

section
variable (K : RunCtx) (φ : Future)

/-- The step for a read of a place (`[Read]`; a place with a field step runs as a match, `projMatch`). -/
def StepPlace : Prop := ∀ n, IH K φ n → ∀ Δ ρ p, EvalAt { K with Δ := Δ } ρ φ n (.place p)
/-- The step for `&p` (`[Borrow]`). -/
def StepBorrow : Prop := ∀ n, IH K φ n → ∀ Δ ρ p, EvalAt { K with Δ := Δ } ρ φ n (.borrow p)
/-- The step for `p := u` (`[Assign]`). -/
def StepAssign : Prop := ∀ n, IH K φ n → ∀ Δ ρ p u, EvalAt { K with Δ := Δ } ρ φ n (.assign p u)
/-- The step for `let x = u; w` (`[Let]`, `[Drop]`). -/
def StepLetIn : Prop := ∀ n, IH K φ n → ∀ Δ ρ x u w, EvalAt { K with Δ := Δ } ρ φ n (.letIn x u w)
/-- The step for `u; w`. -/
def StepSeq : Prop := ∀ n, IH K φ n → ∀ Δ ρ u w, EvalAt { K with Δ := Δ } ρ φ n (.seq u w)
/-- The step for a match on a number (`evalMatch`: a known tag, a split closed off, [Entry], [Join]). -/
def StepMatchNat : Prop := ∀ n, IH K φ n → ∀ Δ ρ p z u, EvalAt { K with Δ := Δ } ρ φ n (.matchNat p z u)
/-- The step for a global's name (`const`). -/
def StepConst : Prop := ∀ n, IH K φ n → ∀ Δ ρ c, EvalAt { K with Δ := Δ } ρ φ n (.const c)
/-- The step for an embedded value (`val`; outside `eval_of_core`: the pre-pass does not classify it). -/
def StepVal : Prop := ∀ n, IH K φ n → ∀ Δ ρ w, EvalAt { K with Δ := Δ } ρ φ n (.val w)
/-- The step for a universe (`sort`). -/
def StepSort : Prop := ∀ n, IH K φ n → ∀ Δ ρ l, EvalAt { K with Δ := Δ } ρ φ n (.sort l)
/-- The step for a Π-type (`[T-Pi]`, its captures on a copy). -/
def StepPi : Prop := ∀ n, IH K φ n → ∀ Δ ρ hs ds c, EvalAt { K with Δ := Δ } ρ φ n (.pi hs ds c)
/-- The step for a function value (`[Closure]`, `checkFix`'s body in tail position). -/
def StepFix : Prop :=
  ∀ n, IH K φ n → ∀ Δ ρ self hs ds c dec body, EvalAt { K with Δ := Δ } ρ φ n (.fix self hs ds c dec body)
/-- The step for a call (`evalCall`, `callFn`, the body in place, [Call-type], [Close]). -/
def StepCall : Prop := ∀ n, IH K φ n → ∀ Δ ρ f as hd, EvalAt { K with Δ := Δ } ρ φ n (.call f as hd)
/-- The step for the type `Nat`. -/
def StepNat : Prop := ∀ n, IH K φ n → ∀ Δ ρ, EvalAt { K with Δ := Δ } ρ φ n .nat
/-- The step for `Z`. -/
def StepZero : Prop := ∀ n, IH K φ n → ∀ Δ ρ, EvalAt { K with Δ := Δ } ρ φ n .zero
/-- The step for `S(u)`. -/
def StepSucc : Prop := ∀ n, IH K φ n → ∀ Δ ρ u, EvalAt { K with Δ := Δ } ρ φ n (.succ u)
/-- The step for the type `Unit`. -/
def StepUnit : Prop := ∀ n, IH K φ n → ∀ Δ ρ, EvalAt { K with Δ := Δ } ρ φ n .unit
/-- The step for `()`. -/
def StepTt : Prop := ∀ n, IH K φ n → ∀ Δ ρ, EvalAt { K with Δ := Δ } ρ φ n .tt
/-- The step for `Eq(A, a, b)` (each side on its own copy). -/
def StepEq : Prop := ∀ n, IH K φ n → ∀ Δ ρ A a b, EvalAt { K with Δ := Δ } ρ φ n (.eq A a b)
/-- The step for `cong f h`. -/
def StepCong : Prop := ∀ n, IH K φ n → ∀ Δ ρ f h, EvalAt { K with Δ := Δ } ρ φ n (.cong f h)
/-- The step for the borrow type `&A`. -/
def StepRef : Prop := ∀ n, IH K φ n → ∀ Δ ρ A, EvalAt { K with Δ := Δ } ρ φ n (.ref A)
/-- The step for `Id(A, t, u)` (`idType`, `observe`). -/
def StepId : Prop := ∀ n, IH K φ n → ∀ Δ ρ A a b, EvalAt { K with Δ := Δ } ρ φ n (.id A a b)
/-- The step for `(u : A)`. -/
def StepAscribe : Prop := ∀ n, IH K φ n → ∀ Δ ρ u A, EvalAt { K with Δ := Δ } ρ φ n (.ascribe u A)
/-- The step for a primitive (`J`, `symm`, `trans`, `rewrite`, `rewriteR`, `split`, `splitArms`, a hole,
`clone`, `peek`, `inplace`, an unknown name). -/
def StepPrim : Prop := ∀ n, IH K φ n → ∀ Δ ρ nm as, EvalAt { K with Δ := Δ } ρ φ n (.prim nm as)
/-- The step for a declared inductive type at its parameters (`evalTInd`). -/
def StepTInd : Prop := ∀ n, IH K φ n → ∀ Δ ρ nm as, EvalAt { K with Δ := Δ } ρ φ n (.tind nm as)
/-- The step for a constructor application (`evalCtor`). -/
def StepCtor : Prop :=
  ∀ n, IH K φ n → ∀ Δ ρ ty c h ps as, EvalAt { K with Δ := Δ } ρ φ n (.ctor ty c h ps as)
/-- The step for a match on a declared inductive (`evalMatchInd`, `evalMatchByType`). -/
def StepMatchInd : Prop := ∀ n, IH K φ n → ∀ Δ ρ p ty arms, EvalAt { K with Δ := Δ } ρ φ n (.matchInd p ty arms)

/-! ## The steps in tail position, one per shape `checkTail` matches -/

/-- `let x = u; w` in tail position (`u` evaluated, `w` checked in tail position with the drop in the
continuation). -/
def TStepLetIn : Prop := ∀ n, IH K φ n → ∀ Δ ρ x u w, TailAt { K with Δ := Δ } ρ φ n (.letIn x u w)
/-- `u; w` in tail position. -/
def TStepSeq : Prop := ∀ n, IH K φ n → ∀ Δ ρ u w, TailAt { K with Δ := Δ } ρ φ n (.seq u w)
/-- A match on a number in tail position (the split into worlds, column `P`'s general form). -/
def TStepMatchNat : Prop := ∀ n, IH K φ n → ∀ Δ ρ p z u, TailAt { K with Δ := Δ } ρ φ n (.matchNat p z u)
/-- A match on a declared inductive in tail position (column `Not`'s general form). -/
def TStepMatchInd : Prop :=
  ∀ n, IH K φ n → ∀ Δ ρ p ty arms, TailAt { K with Δ := Δ } ρ φ n (.matchInd p ty arms)
/-- `split f in u`, `split f { … }`, `rewrite h u`, `rewriteR h u` in tail position. -/
def TStepPrim : Prop :=
  ∀ n, IH K φ n → ∀ Δ ρ nm as, tailShaped (.prim nm as) = true → TailAt { K with Δ := Δ } ρ φ n (.prim nm as)
/-- Every other term in tail position: evaluated with the goal as its hint, the result handed to the
continuation. -/
def TStepOther : Prop :=
  ∀ n, IH K φ n → ∀ Δ ρ t, tailShaped t = false → TailAt { K with Δ := Δ } ρ φ n t

/-- **The 32 step statements**: what remains of (II) for `eval` and `checkTail`, as a list one can count. -/
structure AllSteps : Prop where
  place : StepPlace K φ
  borrow : StepBorrow K φ
  assign : StepAssign K φ
  letIn : StepLetIn K φ
  seq : StepSeq K φ
  matchNat : StepMatchNat K φ
  const : StepConst K φ
  val : StepVal K φ
  sort : StepSort K φ
  pi : StepPi K φ
  fix : StepFix K φ
  call : StepCall K φ
  nat : StepNat K φ
  zero : StepZero K φ
  succ : StepSucc K φ
  unit : StepUnit K φ
  tt : StepTt K φ
  eq : StepEq K φ
  cong : StepCong K φ
  ref : StepRef K φ
  id : StepId K φ
  ascribe : StepAscribe K φ
  prim : StepPrim K φ
  tind : StepTInd K φ
  ctor : StepCtor K φ
  matchInd : StepMatchInd K φ
  tLetIn : TStepLetIn K φ
  tSeq : TStepSeq K φ
  tMatchNat : TStepMatchNat K φ
  tMatchInd : TStepMatchInd K φ
  tPrim : TStepPrim K φ
  tOther : TStepOther K φ

end

/-! ## The induction -/

/-- `{ { K with Δ := Δ } with Δ := Δ' }` is `{ K with Δ := Δ' }`. -/
theorem IH.restate {K : RunCtx} {φ : Future} {n : Nat} {Δ : Nat → TyS} (h : IH { K with Δ := Δ } φ n) :
    IH K φ n := h

/-- One step of the induction: the steps at fuel `n` from the hypothesis at `n`. -/
theorem master_step {K : RunCtx} {φ : Future} (hs : AllSteps K φ) {n : Nat} (ih : IH K φ n)
    (Δ : Nat → TyS) (ρ : Assignment) :
    (∀ t, EvalAt { K with Δ := Δ } ρ φ n t) ∧ (∀ t, TailAt { K with Δ := Δ } ρ φ n t) := by
  refine ⟨fun t => ?_, fun t => ?_⟩
  · cases t with
    | place p => exact hs.place n ih Δ ρ p
    | borrow p => exact hs.borrow n ih Δ ρ p
    | assign p u => exact hs.assign n ih Δ ρ p u
    | letIn x u w => exact hs.letIn n ih Δ ρ x u w
    | seq u w => exact hs.seq n ih Δ ρ u w
    | matchNat p z u => exact hs.matchNat n ih Δ ρ p z u
    | const c => exact hs.const n ih Δ ρ c
    | val w => exact hs.val n ih Δ ρ w
    | sort l => exact hs.sort n ih Δ ρ l
    | pi hs' ds c => exact hs.pi n ih Δ ρ hs' ds c
    | fix self hs' ds c dec body => exact hs.fix n ih Δ ρ self hs' ds c dec body
    | call f as hd => exact hs.call n ih Δ ρ f as hd
    | nat => exact hs.nat n ih Δ ρ
    | zero => exact hs.zero n ih Δ ρ
    | succ u => exact hs.succ n ih Δ ρ u
    | unit => exact hs.unit n ih Δ ρ
    | tt => exact hs.tt n ih Δ ρ
    | eq A a b => exact hs.eq n ih Δ ρ A a b
    | cong f h => exact hs.cong n ih Δ ρ f h
    | ref A => exact hs.ref n ih Δ ρ A
    | id A a b => exact hs.id n ih Δ ρ A a b
    | ascribe u A => exact hs.ascribe n ih Δ ρ u A
    | prim nm as => exact hs.prim n ih Δ ρ nm as
    | tind nm as => exact hs.tind n ih Δ ρ nm as
    | ctor ty c h ps as => exact hs.ctor n ih Δ ρ ty c h ps as
    | matchInd p ty arms => exact hs.matchInd n ih Δ ρ p ty arms
  · cases t with
    | letIn x u w => exact hs.tLetIn n ih Δ ρ x u w
    | seq u w => exact hs.tSeq n ih Δ ρ u w
    | matchNat p z u => exact hs.tMatchNat n ih Δ ρ p z u
    | matchInd p ty arms => exact hs.tMatchInd n ih Δ ρ p ty arms
    | prim nm as =>
      by_cases hsh : tailShaped (.prim nm as) = true
      · exact hs.tPrim n ih Δ ρ nm as hsh
      · exact hs.tOther n ih Δ ρ _ (by simpa using hsh)
    | _ => exact hs.tOther n ih Δ ρ _ rfl

/-- **The master induction**: from the 32 step statements, the evaluation step and the tail step at
every fuel, `Δ` and assignment, for every term. ASSUMES the 32 step statements (`AllSteps`) and nothing
else; what each step assumes in turn is its own (docs/31 D152's table). -/
theorem master {K : RunCtx} {φ : Future} (hs : AllSteps K φ) :
    ∀ n (Δ : Nat → TyS) (ρ : Assignment),
      (∀ t, EvalAt { K with Δ := Δ } ρ φ n t) ∧ (∀ t, TailAt { K with Δ := Δ } ρ φ n t) := by
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih => exact master_step hs (fun m hm Δ ρ => ih m hm Δ ρ)

/-- **(II) for `eval`, at the run's own context**: every fuel, every term (the `Δ` of `K` itself). -/
theorem eval_all {K : RunCtx} {φ : Future} (hs : AllSteps K φ) (ρ : Assignment) (n : Nat) (t : Term) :
    EvalAt K ρ φ n t :=
  (master hs n K.Δ ρ).1 t

/-- **(II) for `checkTail`, at the run's own context.** -/
theorem tail_all {K : RunCtx} {φ : Future} (hs : AllSteps K φ) (ρ : Assignment) (n : Nat) (t : Term) :
    TailAt K ρ φ n t :=
  (master hs n K.Δ ρ).2 t

end Ochr.Meaning.Steps.Form.Master
