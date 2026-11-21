import Ochr.Meaning.Steps.IH
import Ochr.Meaning.FrameProp
import Ochr.Meaning.Steps.Sim
import Ochr.Meaning.Steps.DropOne

/-!
# The call steps, assembled from named obligations (docs/31 D62, D71)

Each assembly below is a proof with no `sorry` in its body: it composes the induction hypothesis and
the named leaves stated here, each `sorry` with one line saying what it is. The point of writing them
is to test the decomposition: an assembly that cannot be closed from the statements as they stand
is a finding about the statements. Writing `runBody`'s found two (docs/31 D71): the induction
hypothesis ran every term out of tail position, where a body runs in tail position on both sides;
and the simulation form kept the run context and concluded no `CtxOk`, so no step could follow
another. Both are fixed in `Steps/Statements.lean`.

The checker's phases are named by copies of `Machine` code fragments (`bodyTail`), pinned by the
decomposition leaves (`runBody_front`).
-/

namespace Ochr.Meaning.Steps

open Ochr Ochr.Meaning

/-- The end of `Machine.runBody` after its body's run: the returned value checked whole, parked below
the callee's frame at the call's type `B` (main's D104: the stored type of that temporary is the
declared type of the position it is headed for), the frame popped (its borrows ended), the depth
restored, the value taken back, and a model function's depth counter undone. -/
def bodyTail (fuel d : Nat) (model : Bool) (B : Option Value) (v : Value) : M Value := do
  Ochr.wholeReturned v
  Ochr.pushTempAt ((← Ochr.topIdx) - 1) v B "runBodyCore"
  Ochr.popFrame fuel
  modify fun s => { s with depth := d }
  let r ← Ochr.popTemp
  if model then modify fun s => { s with modelDepth := s.modelDepth - 1 }
  pure r

theorem grows_bodyTail (fuel d : Nat) (model : Bool) (B : Option Value) (v : Value) :
    GrowsM (bodyTail fuel d model B v) := by
  unfold bodyTail
  grows_go

section
variable (K : RunCtx) (ρ : Assignment) (φ : Future)

open Classical in
theorem runBodyRef_eq (fres : Res) (cs : List Value) (self : Hint) (hs : List Hint) (ds : List Term) (c : Term)
    (dec : Option Nat) (body : Term) (rd : List (DeclInfo × Value)) (args : List Res) (s : SState) :
    runBodyRef K ρ φ fres cs (.fix self hs ds c dec body) rd args s =
      match runT K ρ φ true (.plain ((bodyFrame K ρ φ fres cs rd ds c args s).2.cod (args.map (·.1)))) body
          (bodyFrame K ρ φ fres cs rd ds c args s).1 with
      | some ((r, R), s₁) =>
        if EndsOk K φ (popEnds s.nextLoan (if (bodyFrame K ρ φ fres cs rd ds c args s).2.isRef then R.label else none) s₁) s₁ then
        some ((r, { R with label := if (bodyFrame K ρ φ fres cs rd ds c args s).2.isRef then R.label else none }),
          popCallFrame s.nextLoan (if (bodyFrame K ρ φ fres cs rd ds c args s).2.isRef then R.label else none) s₁)
        else none
      | none => none := rfl

/-- The body's run succeeds where the run in place does. -/
theorem body_isSome_of_runBodyRef (fres : Res) (cs : List Value) (self : Hint) (hs : List Hint) (ds : List Term)
    (c : Term) (dec : Option Nat) (body : Term) (rd : List (DeclInfo × Value)) (args : List Res) (s : SState)
    (h : (runBodyRef K ρ φ fres cs (.fix self hs ds c dec body) rd args s).isSome) :
    (runT K ρ φ true (.plain ((bodyFrame K ρ φ fres cs rd ds c args s).2.cod (args.map (·.1)))) body
      (bodyFrame K ρ φ fres cs rd ds c args s).1).isSome := by
  rw [runBodyRef_eq] at h
  revert h
  cases runT K ρ φ true (.plain ((bodyFrame K ρ φ fres cs rd ds c args s).2.cod (args.map (·.1)))) body
    (bodyFrame K ρ φ fres cs rd ds c args s).1 <;> simp

/-- The callee's unknowns are in the call's table: its code, its captures and their types. -/
def CalleeBounded (st : MState) (cs : List Value) (t : Term) (rd : List (DeclInfo × Value)) : Prop :=
  ∀ σ, (t.anyAtom (· == .abs σ) || Value.anyAtomList (· == .abs σ) cs || Value.anyAtomRd (· == .abs σ) rd) = true →
    σ < st.absTy.size

/-! ### Leaves (named, open) -/

/-- (checker) The callee a related call runs is bounded by the call's table: a closure in the state
names only unknowns it has a type for ((WF6)), and a global names none. -/
theorem callee_bounded (st : MState) (fv : Value) (cs : List Value) (t : Term) (rd : List (DeclInfo × Value))
    (ws : Array Value) (hg : Good K.dm K.M K.Γ ρ (st.withTemps (fv :: ws.toList)))
    (hfix : fv = .clo cs t rd ∨ ∃ n, fv = .gfn n ∧ Runs (Ochr.fixOf fv) st 0 (cs, t, rd) st) :
    CalleeBounded (st.withTemps (fv :: ws.toList)) cs t rd := by
  sorry

/-- **[Call]'s front, taken apart** (`Machine.runBody`, then `runBodyCore` up to the body): the callee's
frame pushed (captures at their types, `self`, the parameters at their types and readings), the depth
and the tail flag set; then the body's run; then `bodyTail`. The frame pushed is related to the run in
place's (`bodyFrame`) under the same assignment and renaming (a push issues no label; the parameters'
types are evaluated on copies, which may only add unknowns), and the body's hint is the code's
codomain at the arguments. -/
theorem runBody_front (fuel : Nat) (st st' : MState) (fv : Value) (cs : List Value) (t : Term) (rd : List (DeclInfo × Value))
    (ws : Array Value) (B : Option Value) (v : Value)
    (hg : Good K.dm K.M K.Γ ρ (st.withTemps (fv :: ws.toList))) (hctx : CtxOk K ρ st)
    (s : SState) (π : Nat → Nat) (hs : Rel K ρ φ π (st.withTemps (fv :: ws.toList)) s)
    (hfix : fv = .clo cs t rd ∨ ∃ n, fv = .gfn n ∧ Runs (Ochr.fixOf fv) st 0 (cs, t, rd) st)
    (fres : Res) (hf : run K ρ (fun l => φ (π l)) (.plain .err) (.val fv) s = some (fres, s))
    (as : List Res) (has : ArgsAgree K ρ φ π ws as)
    (bh : Nat) (h : Runs (Ochr.runBody (fuel + 1) fv cs t rd ws B) st bh v st') :
    ∃ (self : Hint) (hs' : List Hint) (ds : List Term) (c : Term) (dec : Option Nat) (body : Term)
      (hint : Option Value) (st₁ st₂ : MState) (b₁ b₂ d : Nat) (model : Bool) (v₀ : Value) (T₀ : Option Value),
      t = .fix self hs' ds c dec body ∧
      Runs (Ochr.eval (fuel - 1) false body hint) st₁ b₁ (v₀, T₀) st₂ ∧
      Runs (bodyTail (fuel - 1) d model B v₀) st₂ b₂ v st' ∧
      st₁.tailNext = true ∧ (st.withTemps (fv :: ws.toList)).absTy.size ≤ st₁.absTy.size ∧
      (st.withTemps (fv :: ws.toList)).nextLoan ≤ st₁.nextLoan ∧
      Good K.dm K.M K.Γ ρ st₁ ∧ CtxOk K ρ st₁ ∧
      Rel K ρ φ π st₁ (bodyFrame K ρ φ fres cs rd ds c as s).1 ∧
      hintM K ρ hint = .plain ((bodyFrame K ρ φ fres cs rd ds c as s).2.cod (as.map (·.1))) := by
  sorry

open Classical in
/-- The run in place under an assignment extending the call's at new unknowns only is the same: the
frame (captures, binders, codomain) and the body name only unknowns of the call's table
(`CalleeBounded`), and a run reads the assignment only at the unknowns its term names
(`AssignCongr.runT_congrA`). -/
theorem runBodyRef_extend (st : MState) (cs : List Value) (self : Hint) (hs : List Hint) (ds : List Term) (c : Term)
    (dec : Option Nat) (body : Term) (rd : List (DeclInfo × Value))
    (hb : CalleeBounded st cs (.fix self hs ds c dec body) rd) (fres : Res) (as : List Res) (s : SState)
    (ρ₁ ρ₂ : Assignment) (h₁ : ∀ σ, σ < st.absTy.size → ρ₁ σ = ρ σ) (h₂ : ∀ σ, σ < st.absTy.size → ρ₂ σ = ρ σ)
    (r : Res) (s₂ : SState)
    (hrun : runT K ρ₁ φ true (.plain ((bodyFrame K ρ φ fres cs rd ds c as s).2.cod (as.map (·.1)))) body
      (bodyFrame K ρ φ fres cs rd ds c as s).1 = some (r, s₂)) :
    -- model3: the pop is guarded by its strict ends since ruling (A) (`CallRef.runBodyRef`)
    runBodyRef K ρ₂ φ fres cs (.fix self hs ds c dec body) rd as s =
      if EndsOk K φ (popEnds s.nextLoan (if (bodyFrame K ρ φ fres cs rd ds c as s).2.isRef then r.2.label else none) s₂) s₂ then
      some ((r.1, { r.2 with label := if (bodyFrame K ρ φ fres cs rd ds c as s).2.isRef then r.2.label else none }),
        popCallFrame s.nextLoan (if (bodyFrame K ρ φ fres cs rd ds c as s).2.isRef then r.2.label else none) s₂)
      else none := by
  sorry

/-- **[Call]'s back** (`bodyTail` against `popCallFrame`): from related states after the body's run (the
reference's from the frame of the call, under the context `K₀` and assignment `ρ₀`), the checker's pop
(the value checked whole, parked below the frame, the frame's borrows ended, the value taken back) is
the run in place's: every label the frame holds or the body made ends, but the returned one, whose
holder moves to the caller's frame. The value means the same; the context may extend (an end of a
borrow of a dependent type checks its content again and keeps an unknown). -/
theorem runBody_back (fuel : Nat) (st₂ st' : MState) (s₂ : SState) (π : Nat → Nat) (v₀ : Value) (r : Res)
    (hg : GoodF K.dm K.M K.Γ ρ (st₂.withTemp v₀) (flightOf r.2)) (hctx : CtxOk K ρ st₂)
    (hs : Rel K ρ φ π (st₂.withTemp v₀) s₂)
    (K₀ : RunCtx) (ρ₀ ρ₁ : Assignment) (fres : Res) (cs : List Value) (rd : List (DeclInfo × Value)) (ds : List Term)
    (c : Term) (body : Term) (as : List Res) (s : SState)
    (hrun : runT K₀ ρ₁ φ true (.plain ((bodyFrame K₀ ρ₀ φ fres cs rd ds c as s).2.cod (as.map (·.1)))) body
      (bodyFrame K₀ ρ₀ φ fres cs rd ds c as s).1 = some (r, s₂))
    (hr : meanV K ρ (fun l => φ (π l)) r.2 v₀ = r.1)
    (d : Nat) (model : Bool) (B : Option Value) (b : Nat) (v : Value) (h : Runs (bodyTail fuel d model B v₀) st₂ b v st')
    (hD : DecTab K.D st') :
    ∃ (ρ' : Assignment) (Δ' : Nat → TyS) (π' : Nat → Nat), st₂.absTy.size ≤ st'.absTy.size ∧
      st₂.nextLoan ≤ st'.nextLoan ∧ (∀ σ, σ < st₂.absTy.size → ρ' σ = ρ σ ∧ Δ' σ = K.Δ σ) ∧
      (∀ l, l < st₂.nextLoan → π' l = π l) ∧
      meanV { K with Δ := Δ' } ρ' (fun l => φ (π' l))
        { r.2 with label := if (bodyFrame K₀ ρ₀ φ fres cs rd ds c as s).2.isRef then r.2.label else none } v = r.1 ∧
      CtxOk { K with Δ := Δ' } ρ' st' ∧
      Rel { K with Δ := Δ' } ρ' φ π' (st'.withTemp v)
        (popCallFrame s.nextLoan (if (bodyFrame K₀ ρ₀ φ fres cs rd ds c as s).2.isRef then r.2.label else none) s₂) ∧
      GoodF K.dm ({ K with Δ := Δ' } : RunCtx).M K.Γ ρ' (st'.withTemp v)
        (flightOf { r.2 with label := if (bodyFrame K₀ ρ₀ φ fres cs rd ds c as s).2.isRef then r.2.label else none }) := by
  sorry

/-! ### [Call]: the assembly -/

/-- **[Call], a known callee's body run in place** (`runBody_step_stmt`), assembled: the front
(`runBody_front`), the body by the induction hypothesis in tail position (at the body's fuel, one below
the call's: the hypothesis is at every fuel below, `StepsIHBelow`), the back (`runBody_back`), the run in place re-read under the final
assignment (`runBodyRef_extend`). -/
theorem runBody_step_asm (fuel : Nat) (ih : StepsIHBelow fuel) : runBody_step_stmt K ρ φ (fuel + 1) := by
  intro st st' fv cs t rd ws B v hg hctx s π hs hfix fres hf as has hok hD bh h
  obtain ⟨self, hs', ds, c, dec, body, hint, st₁, st₂, b₁, b₂, d, model, v₀, T₀, rfl, hev, htail, htl, habs₁, hnl₁,
    hg₁, hctx₁, hs₁, hhint⟩ := runBody_front K ρ φ fuel st st' fv cs t rd ws B v hg hctx s π hs hfix fres hf as has bh h
  have hok' : false = false →
      (runT K ρ φ st₁.tailNext (hintM K ρ hint) body (bodyFrame K ρ φ fres cs rd ds c as s).1).isSome := by
    intro _; rw [htl, hhint]; exact body_isSome_of_runBodyRef K ρ φ fres cs self hs' ds c dec body rd as s hok
  obtain ⟨ρ₁, Δ₁, π₁, habs₂, hnl₂, hext₁, hπ₁, r, s₂, hrun, hmean, -, hctx₂, hs₂, hg₂⟩ :=
    (ih (fuel - 1) (Nat.sub_le fuel 1) K ρ φ).eval_step st₁ st₂ false body hint v₀ T₀ hg₁ hctx₁ _ π hs₁ hok'
      (hD.of_rest (grows_bodyTail _ _ _ _ _) htail) b₁ hev
  rw [htl, hhint] at hrun
  obtain ⟨ρ₂, Δ₂, π₂, habs₃, hnl₃, hext₂, hπ₂, hmean', hctx₃, hs₃, hg₃⟩ :=
    runBody_back { K with Δ := Δ₁ } ρ₁ φ (fuel - 1) st₂ st' s₂ π₁ v₀ r hg₂ hctx₂ hs₂ K ρ ρ₁ fres cs rd ds c body as s hrun
      hmean d model B b₂ v htail hD
  have hb := callee_bounded K ρ st fv cs (.fix self hs' ds c dec body) rd ws hg hfix
  have hρ₁ : ∀ σ, σ < (st.withTemps (fv :: ws.toList)).absTy.size → ρ₁ σ = ρ σ := fun σ hσ =>
    (hext₁ σ (Nat.lt_of_lt_of_le hσ habs₁)).1
  have hρ₂ : ∀ σ, σ < (st.withTemps (fv :: ws.toList)).absTy.size → ρ₂ σ = ρ σ := fun σ hσ =>
    ((hext₂ σ (Nat.lt_of_lt_of_le hσ (Nat.le_trans habs₁ habs₂))).1).trans (hρ₁ σ hσ)
  -- the pop's strict ends hold: the run in place succeeds (`hok`), read under the extension
  have hend := runBodyRef_extend K ρ φ _ cs self hs' ds c dec body rd hb fres as s ρ₁ ρ hρ₁ (fun _ _ => rfl) r s₂ hrun
  replace hend : EndsOk K φ (popEnds s.nextLoan
      (if (bodyFrame K ρ φ fres cs rd ds c as s).2.isRef then r.2.label else none) s₂) s₂ := by
    rw [hend] at hok
    by_cases he : EndsOk K φ (popEnds s.nextLoan
      (if (bodyFrame K ρ φ fres cs rd ds c as s).2.isRef then r.2.label else none) s₂) s₂
    · exact he
    · rw [if_neg he] at hok; cases hok
  refine ⟨ρ₂, Δ₂, π₂, _, _, Nat.le_trans habs₁ (Nat.le_trans habs₂ habs₃),
    Nat.le_trans hnl₁ (Nat.le_trans hnl₂ hnl₃), fun σ hσ => ⟨hρ₂ σ hσ, ?_⟩, fun l hl => ?_,
    by show runBodyRef K ρ₂ φ fres cs _ rd as s = _
       rw [runBodyRef_extend K ρ φ _ cs self hs' ds c dec body rd hb fres as s ρ₁ ρ₂ hρ₁ hρ₂ r s₂ hrun, if_pos hend],
    hmean', hctx₃, hs₃, hg₃⟩
  · have hlt₁ := Nat.lt_of_lt_of_le hσ habs₁
    exact ((hext₂ σ (Nat.lt_of_lt_of_le hlt₁ habs₂)).2).trans (hext₁ σ hlt₁).2
  · have hlt₁ := Nat.lt_of_lt_of_le hl hnl₁
    exact (hπ₂ l (Nat.lt_of_lt_of_le hlt₁ hnl₂)).trans (hπ₁ l hlt₁)

/-! ### The nested run of a re-normalised sealed program (hole-free since main's D97) -/

/-- The checker's state a sealed program re-runs in (`Machine.nfSealed`): one empty frame, no
observation, one deeper. -/
def nestedStart (st : MState) : MState := { st with env := #[{}], obsFrame := none, depth := st.depth + 1 }

/-- What the re-run must give: an assignment and a context extending the outer ones at the unknowns
the run created, under which the result means the sealed program at every future, and the state
`restoreKeep` makes is good again. -/
def NestedOut (st st₁ : MState) (t : Term) (v : Value) (hint : TyS) : Prop :=
  ∃ (ρ' : Assignment) (Δ' : Nat → TyS), st.absTy.size ≤ st₁.absTy.size ∧
    (∀ σ, σ < st.absTy.size → ρ' σ = ρ σ ∧ Δ' σ = K.Δ σ) ∧ (∀ ψ, meanV { K with Δ := Δ' } ρ' ψ hint v = meanV K ρ ψ hint (.sealed t)) ∧
    ∀ st₂, Runs (Ochr.restoreKeep st) st₁ 0 () st₂ →
      CtxOk { K with Δ := Δ' } ρ' st₂ ∧ Good K.dm ({ K with Δ := Δ' } : RunCtx).M K.Γ ρ' st₂

/-- (leaf) The nested start is good and meets the context's conditions, is not in tail position, and
read as a reference state it is the empty state at the outer counter, holding no borrow. -/
theorem nested_start (st : MState) (hg : Good K.dm K.M K.Γ ρ st) (hctx : CtxOk K ρ st) :
    Good K.dm K.M K.Γ ρ (nestedStart st) ∧ CtxOk K ρ (nestedStart st) ∧ (nestedStart st).tailNext = false ∧
      SM' K ρ (nestedStart st) = emptyState st.nextLoan := by
  sorry

/-- (leaf) From the step at every future, one assignment for all: a loan-free text runs from an empty
frame reading the future only at labels it makes itself, so the unknowns it creates take values that
do not depend on the future; at it, the result means the sealed program (`meanV`'s `.sealed` clause,
the counter lemma `FrameProp.run_counter_indep` from the outer counter to `0`, and the hint
independence of a tail-hint-free text, `HintIndep.run_hintIndep`), and `restoreKeep` keeps only names,
the new unknowns' types and records, so its state is good under it. -/
theorem nested_uniform (st st₁ : MState) (t : Term) (v : Value) (T? : Option Value) (hint : TyS)
    (hg : Good K.dm K.M K.Γ ρ st) (hfree : t.loans = []) (htf : Term.tailHintFree K.Γ t = true)
    (hstep : ∀ ψ, ∃ (ρ' : Assignment) (Δ' : Nat → TyS) (π' : Nat → Nat), (nestedStart st).absTy.size ≤ st₁.absTy.size ∧
      (∀ σ, σ < (nestedStart st).absTy.size → ρ' σ = ρ σ ∧ Δ' σ = K.Δ σ) ∧
      ∃ (r : Res) (s' : SState), runT K ρ' ψ false (hintM K ρ none) t (emptyState st.nextLoan) = some (r, s') ∧
        meanV { K with Δ := Δ' } ρ' (fun l => ψ (π' l)) r.2 v = r.1 ∧
        CtxOk { K with Δ := Δ' } ρ' st₁ ∧ Rel { K with Δ := Δ' } ρ' ψ π' (st₁.withTemp v) s' ∧
        GoodF K.dm ({ K with Δ := Δ' } : RunCtx).M K.Γ ρ' (st₁.withTemp v) (flightOf r.2)) :
    NestedOut K ρ st st₁ t v hint := by
  sorry

/-- **The nested run** (`nestedRun_sim`), assembled: the start (`nested_start`), related to the empty
state by `Rel.start` (it holds no borrow, so no record is asked), the step by the induction
hypothesis at every future, one assignment for all (`nested_uniform`). -/
theorem nestedRun_sim_asm (fuel : Nat) (ih : StepsIHBelow fuel) (st st₁ : MState) (t : Term)
    (v : Value) (T? : Option Value) (hint : TyS)
    (hg : Good K.dm K.M K.Γ ρ st) (hctx : CtxOk K ρ st)
    (hfree : t.loans = []) (htf : Term.tailHintFree K.Γ t = true)
    (hok : ∀ ψ, (runT K ρ ψ false (hintM K ρ none) t (emptyState st.nextLoan)).isSome)
    (hD : DecTab K.D st₁)
    (bh : Nat) (h : Runs (Ochr.eval fuel false t none) (nestedStart st) bh (v, T?) st₁) :
    NestedOut K ρ st st₁ t v hint := by
  obtain ⟨hg₀, hctx₀, htl₀, hsm⟩ := nested_start K ρ st hg hctx
  apply nested_uniform K ρ st st₁ t v T? hint hg hfree htf
  intro ψ
  have hrel : Rel K ρ ψ id (nestedStart st) (SM' K ρ (nestedStart st)) :=
    Rel.start_noLive K ρ ψ (nestedStart st) (fun l hl => by
      rw [hsm] at hl
      exfalso
      simp [SState.Live, SState.liveLabels, emptyState, SState.positions] at hl)
  rw [hsm] at hrel
  have hok' : false = false → (runT K ρ ψ (nestedStart st).tailNext (hintM K ρ none) t (emptyState st.nextLoan)).isSome :=
    fun _ => by rw [htl₀]; exact hok ψ
  obtain ⟨ρ', Δ', π', habs, -, hext, -, r, s', hrun, hmean, -, hctx', hs', hg'⟩ :=
    (ih.at K ρ ψ).eval_step (nestedStart st) st₁ false t none v T? hg₀ hctx₀ _ id hrel hok' hD bh h
  rw [htl₀] at hrun
  exact ⟨ρ', Δ', π', habs, hext, r, s', hrun, hmean, hctx', hs', hg'⟩

end

/-- The checker's tail of a call after the call proper (`Machine.callFn` after `r`, at class `0`): the
result's lending finished (main's D99: a borrow result renamed into the reserved `g`, its loans and
marks becoming `g`'s, `LendOp.into`), the flags, the deferred call type, η at `Unit`. A copy of the
code, pinned by `callFn_front`. -/
def callTailM (fuel : Nat) (g? : Option Nat) (res : DeclInfo) (B : Option Value) (later : Bool) (piTy : Value)
    (ws : Array Value) (r : Value) : M (Value × Option Value) := do
  let r ← match g?, r with
    | some g, .borrow k u => do
      if k != g then Ochr.lendEnv fuel (.into k g)
      pure (Value.borrow g u)
    | some g, _ => do Ochr.lendEnv fuel (.ended g []); pure r
    | none, _ => pure r
  Ochr.setFlags (false, false)
  modify fun s => { s with callTyLater := if later then some (piTy, ws.toList) else none }
  pure (Ochr.etaUnit res r, B)

theorem grows_callTailM (fuel : Nat) (g? : Option Nat) (res : DeclInfo) (B : Option Value) (later : Bool)
    (piTy : Value) (ws : Array Value) (r : Value) : GrowsM (callTailM fuel g? res B later piTy ws r) := by
  unfold callTailM
  grows_go

section
variable (K : RunCtx) (ρ : Assignment) (φ : Future)

/-! ### A call (`callFn`) -/

/-- The reference's counterpart of the checker's reservation before a borrow-returning call (static
ends, rule 1): the result's label `g` taken from the counter and lent, as fills, where the borrow
arguments lent (`CallRef.runCallRef` does the same before the body; main's D99). -/
noncomputable def reserveRef (isRef : Bool) (as : List Res) (s : SState) : SState :=
  if isRef then
    let lentK := ((as.filterMap (·.2.label)).flatMap s.lent).map fun x : Site => { x with fill := true }
    (s.freshLoan.2).setLent s.freshLoan.1 lentK
  else s

/-- **A call taken apart** (`Machine.callFn` at a call that is neither a statement nor erased, class
`0` from `hns`): its front (the call's type and decisions, `recCheck`, the row, the class, and for a
borrow result the reservation of `g` with its marks) leaves a state related to the reference's after
`reserveRef`, under a renaming extended at `g`; then either the call closes off (`closeCall`, at once
for a neutral head, or after a body run that is stuck, whose state `catchStuck` restores), with
[Close]'s readings tied to the callee's code (`closeCall_step_stmt`'s side conditions), or a known
callee's body runs (`runBody`), whose run in place succeeds (`runBody_step_stmt`'s `hok`: the
callee's meaning is a member of its type at member arguments); then the tail (`callTailM`). `B`
is the call's type as the front computed it: the body run in place holds its result at it across
the frame's pop (main's D104), and the tail returns it. -/
theorem callFn_front (fuel : Nat) (st st' : MState) (typed : Bool) (f : Term) (args : List Term) (hd : Bool) (fv : Value)
    (fT : Option Value) (ws : Array Value) (tys : Array (Option Value)) (recUid? : Option Nat)
    (res : DeclInfo) (fills : Array Bool) (want defer : Bool) (v : Value) (T? : Option Value)
    (hg : Good K.dm K.M K.Γ ρ (st.withTemps (fv :: ws.toList))) (hctx : CtxOk K ρ st)
    (s : SState) (π : Nat → Nat) (hs : Rel K ρ φ π (st.withTemps (fv :: ws.toList)) s)
    (hns : K.D.flags (scopeOf s) (.call f args hd) = (false, false))
    (fres : Res) (hf : run K ρ (fun l => φ (π l)) (.plain .err) (.val fv) s = some (fres, s))
    (as : List Res) (has : ArgsAgree K ρ φ π ws as)
    (bh : Nat) (h : Runs (Ochr.callFn (fuel + 1) typed fv fT ws tys hd none recUid? res fills want defer) st bh (v, T?) st') :
    ∃ (isRef : Bool) (st₁ st₂ : MState) (π₁ : Nat → Nat) (w : Value) (b₁ : Nat) (B : Option Value),
      Good K.dm K.M K.Γ ρ (st₁.withTemps (fv :: ws.toList)) ∧ CtxOk K ρ st₁ ∧
      Rel K ρ φ π₁ (st₁.withTemps (fv :: ws.toList)) (reserveRef isRef as s) ∧
      (∀ l, l < (st.withTemps (fv :: ws.toList)).nextLoan → π₁ l = π l) ∧
      (st.withTemps (fv :: ws.toList)).absTy.size ≤ st₁.absTy.size ∧
      (st.withTemps (fv :: ws.toList)).nextLoan ≤ st₁.nextLoan ∧
      run K ρ (fun l => φ (π₁ l)) (.plain .err) (.val fv) (reserveRef isRef as s) = some (fres, reserveRef isRef as s) ∧
      ArgsAgree K ρ φ π₁ ws as ∧
      ((∃ (kind : Kind) (res' : DeclInfo) (fills' : Array Bool) (tys' : Array (Option Value)),
          Runs (Ochr.closeCall fuel fv ws kind res' fills' tys') st₁ b₁ w st₂ ∧ fres.2.m.isPi = true ∧
          (kind = .ref ↔ ∃ U, fres.2.m.codAt? K.dm.read (as.map (·.1)) = some (true, U)) ∧
          (res' = .unit → ∀ B, fres.2.m.codAt? K.dm.read (as.map (·.1)) = some (false, B) → B = TyM.unit) ∧
          (∀ i : Nat, fills'.getD i false = true → ∀ p,
            fres.2.m.paramAt? K.dm.read ((as.map (·.1)).take i) = some p → p.2 = TyM.unit) ∧
          (∀ (i l : Nat) (w : Value), ws[i]? = some (Value.borrow l w) → ∀ p,
            fres.2.m.paramAt? K.dm.read ((as.map (·.1)).take i) = some p →
            ∃ T : Value, tys'[i]? = some (some (Value.tRef T)) ∧ (Value.tyS K.dm K.M K.Γ ρ T).m = p.2)) ∨
       (∃ (cs : List Value) (t : Term) (rd : List (DeclInfo × Value)),
          (fv = .clo cs t rd ∨ ∃ n, fv = .gfn n ∧ Runs (Ochr.fixOf fv) st₁ 0 (cs, t, rd) st₁) ∧
          (runBodyRef K ρ φ fres cs t rd as (reserveRef isRef as s)).isSome ∧
          Runs (Ochr.runBody fuel fv cs t rd ws B) st₁ b₁ w st₂)) ∧
      ∃ (b₂ : Nat) (g? : Option Nat) (later : Bool) (piTy : Value),
        g?.isSome = isRef ∧ Runs (callTailM fuel g? res B later piTy ws w) st₂ b₂ (v, T?) st' := by
  sorry

/-- **The tail of a call that closed off** (leaf): from the call proper related to `callOf` run from
the reserved state (`closeCall_step_stmt`), the tail (the result renamed into `g`, main's D99; η at
`Unit`, `etaUnit_step_stmt`; the call's type, `callType_step_stmt`) gives the call related to
`callOf` run from the state before the reservation: reserving `g`, calling, and renaming the fresh
result into `g` is `callOf` (its fresh label is `g`), as main's D99 makes the checker do. -/
theorem callFn_tail_closed (fuel : Nat) (st st₁ st₂ st' : MState) (fv : Value) (ws : Array Value) (s : SState)
    (π π₁ : Nat → Nat) (isRef : Bool) (fres : Res) (as : List Res) (w v : Value) (T? : Option Value) (res : DeclInfo)
    (hπ₁ : ∀ l, l < (st.withTemps (fv :: ws.toList)).nextLoan → π₁ l = π l)
    (habs : (st.withTemps (fv :: ws.toList)).absTy.size ≤ st₁.absTy.size)
    (hnl : (st.withTemps (fv :: ws.toList)).nextLoan ≤ st₁.nextLoan)
    (hcall : SimConcl K ρ φ π₁ (st₁.withTemps (fv :: ws.toList)) st₂ (reserveRef isRef as s)
      (fun _ => callOf K.dm.read fres as) w)
    (b₂ : Nat) (g? : Option Nat) (B : Option Value) (later : Bool) (piTy : Value) (hg? : g?.isSome = isRef)
    (htail : Runs (callTailM fuel g? res B later piTy ws w) st₂ b₂ (v, T?) st') :
    SimConclT K ρ φ π (st.withTemps (fv :: ws.toList)) st' s (fun _ => callOf K.dm.read fres as) v T? := by
  sorry

/-- **The tail of a call that ran its body in place** (leaf): from the body's run related to the run
in place from the reserved state (`runBody_step_stmt`), the tail gives the call related to `callOf`
from the state before the reservation: the run in place with the reservation and the renaming is
`runCallRef`, which is `callOf` at a related call (`Call.callOf_inPlace_rel`); η and the type as for
a call that closed off. -/
theorem callFn_tail_ran (fuel : Nat) (st st₁ st₂ st' : MState) (fv : Value) (ws : Array Value) (s : SState)
    (π π₁ : Nat → Nat) (isRef : Bool) (fres : Res) (as : List Res) (cs : List Value) (t : Term)
    (rd : List (DeclInfo × Value)) (w v : Value) (T? : Option Value) (res : DeclInfo)
    (hπ₁ : ∀ l, l < (st.withTemps (fv :: ws.toList)).nextLoan → π₁ l = π l)
    (habs : (st.withTemps (fv :: ws.toList)).absTy.size ≤ st₁.absTy.size)
    (hnl : (st.withTemps (fv :: ws.toList)).nextLoan ≤ st₁.nextLoan)
    (hbody : SimConcl K ρ φ π₁ (st₁.withTemps (fv :: ws.toList)) st₂ (reserveRef isRef as s)
      (fun ρ' => runBodyRef K ρ' φ fres cs t rd as) w)
    (b₂ : Nat) (g? : Option Nat) (B : Option Value) (later : Bool) (piTy : Value) (hg? : g?.isSome = isRef)
    (htail : Runs (callTailM fuel g? res B later piTy ws w) st₂ b₂ (v, T?) st') :
    SimConclT K ρ φ π (st.withTemps (fv :: ws.toList)) st' s (fun _ => callOf K.dm.read fres as) v T? := by
  sorry

/-- **A call** (`callFn_step_stmt`), assembled: the front (`callFn_front`), then the call proper by the
induction hypothesis (`closeCall_step` or `runBody_step`, at the fuel below, with the hypotheses the
front supplies), then the tail (`callFn_tail_closed`, `callFn_tail_ran`). -/
theorem callFn_step_asm (fuel : Nat) (ih : StepsIHBelow fuel) : callFn_step_stmt K ρ φ (fuel + 1) := by
  intro st st' typed f args hd fv fT ws tys recUid? res fills want defer v T? hg hctx s π hs hns fres hf as has hD bh h
  obtain ⟨isRef, st₁, st₂, π₁, w, b₁, B, hg₁, hctx₁, hs₁, hπ₁, habs, hnl, hf₁, has₁, hpath, b₂, g?, later, piTy, hg?,
    htail⟩ := callFn_front K ρ φ fuel st st' typed f args hd fv fT ws tys recUid? res fills want defer v T? hg hctx s π hs
      hns fres hf as has bh h
  have hD₂ : DecTab K.D st₂ := hD.of_rest (grows_callTailM _ _ _ _ _ _ _ _) htail
  rcases hpath with ⟨kind, res', fills', tys', hcl, hpi, hkind, hres, hfills, htys⟩ | ⟨cs, t, rd, hfix, hok, hrb⟩
  · have hcall := (ih.at K ρ φ).closeCall_step st₁ st₂ fv ws kind res' fills' tys' w hg₁ hctx₁ _ π₁ hs₁ fres hf₁ hpi as
      has₁ hkind hres hfills htys hD₂ b₁ hcl
    exact callFn_tail_closed K ρ φ fuel st st₁ st₂ st' fv ws s π π₁ isRef fres as w v T? res hπ₁ habs hnl hcall b₂ g? B
      later piTy hg? htail
  · have hbody := (ih.at K ρ φ).runBody_step st₁ st₂ fv cs t rd ws B w hg₁ hctx₁ _ π₁ hs₁ hfix fres hf₁ as has₁ hok hD₂ b₁ hrb
    exact callFn_tail_ran K ρ φ fuel st st₁ st₂ st' fv ws s π π₁ isRef fres as cs t rd w v T? res hπ₁ habs hnl hbody b₂
      g? B later piTy hg? htail

end

/-! ### [Close]: a call closing off -/

/-- One fill of a call closing off (`Machine.closeCall`'s loop body): the fill substituted for the
borrow argument's loan everywhere, then the places it lent freed. -/
def closeFillM (fuel l : Nat) (fill : Value) : M Unit := do
  Ochr.substEnv fuel (.loan l) fill false
  Ochr.lendEnv fuel (.ended l [])

/-- The fills, in argument order. -/
def closeLoopM (fuel : Nat) : List (Nat × Value) → M Unit
  | [] => pure ()
  | (l, fill) :: rest => do closeFillM fuel l fill; closeLoopM fuel rest

/-- The reference's fixing of one consumed borrow argument (`callOf`'s `mapVals`, one label at a time):
its holder taken, every meaning reading its final content as `fin`. -/
noncomputable def fixLabelRef (l : Nat) (fin : SVal) (s : SState) : SState :=
  (s.takeLabel l).mapVals fun _ v φ' => v (φ'.upd l (fin φ'))

section
variable (K : RunCtx) (ρ : Assignment) (φ : Future)

/-- The checker's state and the reference's are related after some fills, the context extended:
the invariant of `closeCall`'s loop. -/
def FillRel (π : Nat → Nat) (st₀ st : MState) (ws : Array Value) (fv : Value) (s : SState) : Prop :=
  ∃ (ρ' : Assignment) (Δ' : Nat → TyS), st₀.absTy.size ≤ st.absTy.size ∧ st₀.nextLoan ≤ st.nextLoan ∧
    (∀ σ, σ < st₀.absTy.size → ρ' σ = ρ σ ∧ Δ' σ = K.Δ σ) ∧ CtxOk { K with Δ := Δ' } ρ' st ∧
    Rel { K with Δ := Δ' } ρ' φ π (st.withTemps (fv :: ws.toList)) s ∧
    Good K.dm ({ K with Δ := Δ' } : RunCtx).M K.Γ ρ' (st.withTemps (fv :: ws.toList))

/-- **One fill** (leaf): from related states, the checker's substitution of a fill for a consumed
borrow argument's loan and the end of its lending is the reference's fixing of the label to the
fill's meaning (`fixLabelRef`): every meaning that read the final content reads the fill's (the
substitution lemma, `meanV_substLoan`; the re-runs it causes are hole-free and `nestedRun_sim`'s, main's
D97), and the places it lent are free on both sides. The renaming is unchanged (no label is issued). -/
theorem closeFill_step (fuel : Nat) (st st' : MState) (fv : Value) (ws : Array Value) (s : SState) (π : Nat → Nat)
    (l : Nat) (fill : Value) (fin : SVal) (hfin : ∀ ψ, meanV K ρ ψ (.plain .err) fill = fin ψ)
    (hg : Good K.dm K.M K.Γ ρ (st.withTemps (fv :: ws.toList))) (hctx : CtxOk K ρ st)
    (hs : Rel K ρ φ π (st.withTemps (fv :: ws.toList)) s) (b : Nat) (h : Runs (closeFillM fuel l fill) st b () st')
    (hD : DecTab K.D st') :
    FillRel K ρ φ π st st' ws fv (fixLabelRef (π l) fin s) := by
  sorry

theorem grows_closeLoopM (fuel : Nat) : ∀ fx : List (Nat × Value), GrowsM (closeLoopM fuel fx)
  | [] => GrowsM.pure _
  | (l, fill) :: rest => by
    unfold closeLoopM closeFillM
    exact (by grows_go : GrowsM (do Ochr.substEnv fuel (.loan l) fill false; Ochr.lendEnv fuel (.ended l []))).bind
      fun _ => grows_closeLoopM fuel rest

/-- **The fills** (assembled): the loop by induction, one fill at a time (`closeFill_step`), the
context extended at each; each fill means its final content under every extension of the context at
the loop's start (`hfin`: the fills name only unknowns of that table). -/
theorem closeLoop_rel (fuel : Nat) (fv : Value) (ws : Array Value) (π : Nat → Nat) (st₀ : MState) :
    ∀ (fx : List (Nat × Value)) (fins : List SVal) (Δc : Nat → TyS) (ρc : Assignment)
      (st st' : MState) (s : SState) (b : Nat),
    fx.length = fins.length →
    (∀ (Δ' : Nat → TyS) (ρ' : Assignment), (∀ σ, σ < st₀.absTy.size → ρ' σ = ρ σ ∧ Δ' σ = K.Δ σ) →
      ∀ p ∈ fx.zip fins, ∀ ψ, meanV { K with Δ := Δ' } ρ' ψ (.plain .err) p.1.2 = p.2 ψ) →
    (∀ σ, σ < st₀.absTy.size → ρc σ = ρ σ ∧ Δc σ = K.Δ σ) → DecTab K.D st' →
    st₀.absTy.size ≤ st.absTy.size →
    Good K.dm ({ K with Δ := Δc } : RunCtx).M K.Γ ρc (st.withTemps (fv :: ws.toList)) →
    CtxOk { K with Δ := Δc } ρc st →
    Rel { K with Δ := Δc } ρc φ π (st.withTemps (fv :: ws.toList)) s → Runs (closeLoopM fuel fx) st b () st' →
    FillRel { K with Δ := Δc } ρc φ π st st' ws fv
      ((fx.zip fins).foldl (fun s p => fixLabelRef (π p.1.1) p.2 s) s)
  | [], [], Δc, ρc, st, st', s, b, _, _, _, _, _, hg, hctx, hs, h => by
    obtain ⟨-, rfl⟩ := runs_pure_inv h
    exact ⟨ρc, Δc, Nat.le_refl _, Nat.le_refl _, fun _ _ => ⟨rfl, rfl⟩, hctx, hs, hg⟩
  | (l, fill) :: rest, fin :: fins, Δc, ρc, st, st', s, b, hlen, hfin, hc, hD, hle, hg, hctx, hs, h => by
    obtain ⟨_, st₁, b₁, h1, h2⟩ := Runs.bind_inv h
    obtain ⟨ρ₁, Δ₁, habs₁, hnl₁, hext₁, hctx₁, hs₁, hg₁⟩ :=
      closeFill_step { K with Δ := Δc } ρc φ fuel st st₁ fv ws s π l fill fin
        (hfin Δc ρc hc _ (List.mem_cons_self ..)) hg hctx hs b h1 (hD.of_rest (grows_closeLoopM _ _) h2)
    have hc₁ : ∀ σ, σ < st₀.absTy.size → ρ₁ σ = ρ σ ∧ Δ₁ σ = K.Δ σ := fun σ hσ =>
      ⟨((hext₁ σ (Nat.lt_of_lt_of_le hσ hle)).1).trans (hc σ hσ).1, ((hext₁ σ (Nat.lt_of_lt_of_le hσ hle)).2).trans (hc σ hσ).2⟩
    obtain ⟨ρ₂, Δ₂, habs₂, hnl₂, hext₂, hctx₂, hs₂, hg₂⟩ := closeLoop_rel fuel fv ws π st₀ rest fins Δ₁ ρ₁ st₁ st'
      (fixLabelRef (π l) fin s) b₁ (by simpa using hlen)
      (fun Δ' ρ' he p hp ψ => hfin Δ' ρ' he p (List.mem_cons_of_mem _ hp) ψ) hc₁ hD
      (Nat.le_trans hle habs₁) hg₁ hctx₁ hs₁ h2
    refine ⟨ρ₂, Δ₂, Nat.le_trans habs₁ habs₂, Nat.le_trans hnl₁ hnl₂, fun σ hσ => ?_, hctx₂, hs₂, hg₂⟩
    have h1' := hext₁ σ hσ
    have h2' := hext₂ σ (Nat.lt_of_lt_of_le hσ habs₁)
    exact ⟨h2'.1.trans h1'.1, h2'.2.trans h1'.2⟩
  | [], _ :: _, _, _, _, _, _, _, hlen, _, _, _, _, _, _, _, _ => by simp at hlen
  | _ :: _, [], _, _, _, _, _, _, hlen, _, _, _, _, _, _, _, _ => by simp at hlen

/-- **[Close] taken apart** (leaf): a successful `closeCall` checks its arguments (nothing changes) and,
for a borrow result, takes a fresh label; the state is then related to the reference's; then it runs
its fills (`closeLoopM`), one per borrow argument in order, each the sealed text [Close] builds,
normalised, whose meaning under every extension of the context is the argument's final content in
`callOf` (`closeCall_means_data` and its `&T` twin). -/
theorem closeCall_split (fuel : Nat) (st st' : MState) (fv : Value) (ws : Array Value) (kind : Kind) (res : DeclInfo)
    (fills : Array Bool) (tys : Array (Option Value)) (v : Value)
    (hg : Good K.dm K.M K.Γ ρ (st.withTemps (fv :: ws.toList))) (hctx : CtxOk K ρ st)
    (s : SState) (π : Nat → Nat) (hs : Rel K ρ φ π (st.withTemps (fv :: ws.toList)) s)
    (fres : Res) (as : List Res) (has : ArgsAgree K ρ φ π ws as) (bh : Nat)
    (h : Runs (Ochr.closeCall (fuel + 1) fv ws kind res fills tys) st bh v st') :
    ∃ (st₁ st₂ : MState) (b₁ : Nat) (fx : List (Nat × Value)) (fins : List SVal),
      (st.withTemps (fv :: ws.toList)).absTy.size ≤ st₁.absTy.size ∧
      (st.withTemps (fv :: ws.toList)).nextLoan ≤ st₁.nextLoan ∧
      Good K.dm K.M K.Γ ρ (st₁.withTemps (fv :: ws.toList)) ∧ CtxOk K ρ st₁ ∧
      Rel K ρ φ π (st₁.withTemps (fv :: ws.toList)) s ∧ fx.length = fins.length ∧
      (∀ (Δ' : Nat → TyS) (ρ' : Assignment), (∀ σ, σ < st₁.absTy.size → ρ' σ = ρ σ ∧ Δ' σ = K.Δ σ) →
        ∀ p ∈ fx.zip fins, ∀ ψ, meanV { K with Δ := Δ' } ρ' ψ (.plain .err) p.1.2 = p.2 ψ) ∧
      Runs (closeLoopM fuel fx) st₁ b₁ () st₂ ∧ TablesGrow st₂ st' := by
  sorry

/-- **[Close]'s result** (leaf): after the fills, the checker returns the sealed result (`()` at a
declared `Unit`; for a borrow result `borrow_k` of it, `k` the fresh label); the reference's `callOf`
is its fixing of the consumed labels (`fixLabelRef`, in the same order) followed by its result (for a
borrow result the fresh label `k` held in a temporary, lent where the arguments lent, recorded), and
the result means `callOf`'s (`closeCall_means_data` and its twin). -/
theorem closeCall_post (fuel : Nat) (st st₁ st₂ st' : MState) (fv : Value) (ws : Array Value) (kind : Kind)
    (res : DeclInfo) (fills : Array Bool) (tys : Array (Option Value)) (v : Value) (s : SState) (π : Nat → Nat)
    (fres : Res) (as : List Res) (bh : Nat) (h : Runs (Ochr.closeCall (fuel + 1) fv ws kind res fills tys) st bh v st')
    (fx : List (Nat × Value)) (fins : List SVal) (b₁ : Nat) (hloop : Runs (closeLoopM fuel fx) st₁ b₁ () st₂)
    (habs : (st.withTemps (fv :: ws.toList)).absTy.size ≤ st₁.absTy.size)
    (hnl : (st.withTemps (fv :: ws.toList)).nextLoan ≤ st₁.nextLoan)
    (hrel : FillRel K ρ φ π st₁ st₂ ws fv ((fx.zip fins).foldl (fun s p => fixLabelRef (π p.1.1) p.2 s) s)) :
    SimConcl K ρ φ π (st.withTemps (fv :: ws.toList)) st' s (fun _ => callOf K.dm.read fres as) v := by
  sorry

/-- **[Close]** (`closeCall_step_stmt`), assembled: the checks and the fresh label (`closeCall_split`),
the fills one at a time (`closeLoop_rel`), the result (`closeCall_post`). -/
theorem closeCall_step_asm (fuel : Nat) (ih : StepsIHBelow fuel) : closeCall_step_stmt K ρ φ (fuel + 1) := by
  intro st st' fv ws kind res fills tys v hg hctx s π hs fres hf hpi as has hkind hres hfills htys hD bh h
  obtain ⟨st₁, st₂, b₁, fx, fins, habs, hnl, hg₁, hctx₁, hs₁, hlen, hfin, hloop, hpost⟩ :=
    closeCall_split K ρ φ fuel st st' fv ws kind res fills tys v hg hctx s π hs fres as has bh h
  have hrel := closeLoop_rel K ρ φ fuel fv ws π st₁ fx fins K.Δ ρ st₁ st₂ s b₁ hlen
    (fun Δ' ρ' he => hfin Δ' ρ' he) (fun _ _ => ⟨rfl, rfl⟩)
    (hD.back hpost) (Nat.le_refl _) hg₁ hctx₁ hs₁ hloop
  exact closeCall_post K ρ φ fuel st st₁ st₂ st' fv ws kind res fills tys v s π fres as bh h fx fins b₁ hloop habs hnl hrel

end

end Ochr.Meaning.Steps
