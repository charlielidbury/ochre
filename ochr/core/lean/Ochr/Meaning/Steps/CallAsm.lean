import Ochr.Meaning.Steps.IH
import Ochr.Meaning.FrameProp

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
the callee's frame, the frame popped (its borrows ended), the depth restored, the value taken back,
and a model function's depth counter undone. -/
def bodyTail (fuel d : Nat) (model : Bool) (v : Value) : M Value := do
  Ochr.wholeReturned v
  Ochr.pushTempAt ((← Ochr.topIdx) - 1) v
  Ochr.popFrame fuel
  modify fun s => { s with depth := d }
  let r ← Ochr.popTemp
  if model then modify fun s => { s with modelDepth := s.modelDepth - 1 }
  pure r

section
variable (K : RunCtx) (ρ : Assignment) (φ : Future)

/-- The callee's frame and codomain as the run in place computes them (`runBodyRef`'s `let`s). -/
noncomputable def bodyFrame (fres : Res) (cs : List Value) (rd : List (DeclInfo × Value)) (ds : List Term) (c : Term)
    (args : List Res) (s : SState) : SState × PiCod :=
  let s₀ := (capsState (capsVals K ρ φ cs) (capsTys K ρ φ rd)).foldl SState.pushBind s.pushFrame
  let bs := bindsOf K ρ φ s₀ ds
  (callFrame K ρ φ cs rd fres (K.D.typeDecl (K.D.teleDecls (scopeOf s₀) ds) c) bs args s, codOf K ρ φ s₀ bs c)

theorem runBodyRef_eq (fres : Res) (cs : List Value) (self : Hint) (hs : List Hint) (ds : List Term) (c : Term)
    (dec : Option Nat) (body : Term) (rd : List (DeclInfo × Value)) (args : List Res) (s : SState) :
    runBodyRef K ρ φ fres cs (.fix self hs ds c dec body) rd args s =
      match runT K ρ φ true (.plain ((bodyFrame K ρ φ fres cs rd ds c args s).2.cod (args.map (·.1)))) body
          (bodyFrame K ρ φ fres cs rd ds c args s).1 with
      | some ((r, R), s₁) =>
        some ((r, { R with label := if (bodyFrame K ρ φ fres cs rd ds c args s).2.isRef then R.label else none }),
          popCallFrame s.nextLoan (if (bodyFrame K ρ φ fres cs rd ds c args s).2.isRef then R.label else none) s₁)
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

/-- (checker) A run that succeeds at a fuel succeeds alike at more: running out of fuel is never
caught below the top level (`ochr/core/CLAUDE.md`), so it decides nothing. -/
theorem runs_eval_fuel_mono {f f' : Nat} (hf : f ≤ f') {typed : Bool} {t : Term} {hint : Option Value}
    {st st' : MState} {b : Nat} {a : Value × Option Value} (h : Runs (Ochr.eval f typed t hint) st b a st') :
    ∃ b', Runs (Ochr.eval f' typed t hint) st b' a st' := by
  sorry

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
    (ws : Array Value) (v : Value)
    (hg : Good K.dm K.M K.Γ ρ (st.withTemps (fv :: ws.toList))) (hctx : CtxOk K ρ st)
    (s : SState) (π : Nat → Nat) (hs : Rel K ρ φ π (st.withTemps (fv :: ws.toList)) s)
    (hfix : fv = .clo cs t rd ∨ ∃ n, fv = .gfn n ∧ Runs (Ochr.fixOf fv) st 0 (cs, t, rd) st)
    (fres : Res) (hf : run K ρ (fun l => φ (π l)) (.plain .err) (.val fv) s = some (fres, s))
    (as : List Res) (has : ArgsAgree K ρ φ π ws as)
    (bh : Nat) (h : Runs (Ochr.runBody (fuel + 1) fv cs t rd ws) st bh v st') :
    ∃ (self : Hint) (hs' : List Hint) (ds : List Term) (c : Term) (dec : Option Nat) (body : Term)
      (hint : Option Value) (st₁ st₂ : MState) (b₁ b₂ d : Nat) (model : Bool) (v₀ : Value) (T₀ : Option Value),
      t = .fix self hs' ds c dec body ∧
      Runs (Ochr.eval (fuel - 1) false body hint) st₁ b₁ (v₀, T₀) st₂ ∧
      Runs (bodyTail (fuel - 1) d model v₀) st₂ b₂ v st' ∧
      st₁.tailNext = true ∧ (st.withTemps (fv :: ws.toList)).absTy.size ≤ st₁.absTy.size ∧
      (st.withTemps (fv :: ws.toList)).nextLoan ≤ st₁.nextLoan ∧
      Good K.dm K.M K.Γ ρ st₁ ∧ CtxOk K ρ st₁ ∧
      Rel K ρ φ π st₁ (bodyFrame K ρ φ fres cs rd ds c as s).1 ∧
      hintM K ρ hint = .plain ((bodyFrame K ρ φ fres cs rd ds c as s).2.cod (as.map (·.1))) := by
  sorry

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
    runBodyRef K ρ₂ φ fres cs (.fix self hs ds c dec body) rd as s =
      some ((r.1, { r.2 with label := if (bodyFrame K ρ φ fres cs rd ds c as s).2.isRef then r.2.label else none }),
        popCallFrame s.nextLoan (if (bodyFrame K ρ φ fres cs rd ds c as s).2.isRef then r.2.label else none) s₂) := by
  sorry

/-- **[Call]'s back** (`bodyTail` against `popCallFrame`): from related states after the body's run (the
reference's from the frame of the call, under the context `K₀` and assignment `ρ₀`), the checker's pop
(the value checked whole, parked below the frame, the frame's borrows ended, the value taken back) is
the run in place's: every label the frame holds or the body made ends, but the returned one, whose
holder moves to the caller's frame. The value means the same; the context may extend (an end of a
borrow of a dependent type checks its content again and keeps an unknown). -/
theorem runBody_back (fuel : Nat) (st₂ st' : MState) (s₂ : SState) (π : Nat → Nat)
    (hg : Good K.dm K.M K.Γ ρ st₂) (hctx : CtxOk K ρ st₂) (hs : Rel K ρ φ π st₂ s₂)
    (K₀ : RunCtx) (ρ₀ ρ₁ : Assignment) (fres : Res) (cs : List Value) (rd : List (DeclInfo × Value)) (ds : List Term)
    (c : Term) (body : Term) (as : List Res) (s : SState) (r : Res)
    (hrun : runT K₀ ρ₁ φ true (.plain ((bodyFrame K₀ ρ₀ φ fres cs rd ds c as s).2.cod (as.map (·.1)))) body
      (bodyFrame K₀ ρ₀ φ fres cs rd ds c as s).1 = some (r, s₂))
    (v₀ : Value) (hr : meanV K ρ (fun l => φ (π l)) r.2 v₀ = r.1)
    (d : Nat) (model : Bool) (b : Nat) (v : Value) (h : Runs (bodyTail fuel d model v₀) st₂ b v st') :
    ∃ (ρ' : Assignment) (Δ' : Nat → TyS) (π' : Nat → Nat), st₂.absTy.size ≤ st'.absTy.size ∧
      st₂.nextLoan ≤ st'.nextLoan ∧ (∀ σ, σ < st₂.absTy.size → ρ' σ = ρ σ ∧ Δ' σ = K.Δ σ) ∧
      (∀ l, l < st₂.nextLoan → π' l = π l) ∧
      meanV { K with Δ := Δ' } ρ' (fun l => φ (π' l))
        { r.2 with label := if (bodyFrame K₀ ρ₀ φ fres cs rd ds c as s).2.isRef then r.2.label else none } v = r.1 ∧
      CtxOk { K with Δ := Δ' } ρ' st' ∧
      Rel { K with Δ := Δ' } ρ' φ π' st'
        (popCallFrame s.nextLoan (if (bodyFrame K₀ ρ₀ φ fres cs rd ds c as s).2.isRef then r.2.label else none) s₂) ∧
      Good K.dm ({ K with Δ := Δ' } : RunCtx).M K.Γ ρ' st' := by
  sorry

/-! ### [Call]: the assembly -/

/-- **[Call], a known callee's body run in place** (`runBody_step_stmt`), assembled: the front
(`runBody_front`), the body by the induction hypothesis in tail position (after lifting its fuel,
`runs_eval_fuel_mono`), the back (`runBody_back`), the run in place re-read under the final
assignment (`runBodyRef_extend`). -/
theorem runBody_step_asm (fuel : Nat) (ih : ∀ K' ρ φ, StepsIH K' ρ φ fuel) : runBody_step_stmt K ρ φ (fuel + 1) := by
  intro st st' fv cs t rd ws v hg hctx s π hs hfix fres hf as has hok bh h
  obtain ⟨self, hs', ds, c, dec, body, hint, st₁, st₂, b₁, b₂, d, model, v₀, T₀, rfl, hev, htail, htl, habs₁, hnl₁,
    hg₁, hctx₁, hs₁, hhint⟩ := runBody_front K ρ φ fuel st st' fv cs t rd ws v hg hctx s π hs hfix fres hf as has bh h
  obtain ⟨b₁', hev'⟩ := runs_eval_fuel_mono (Nat.sub_le fuel 1) hev
  have hok' : false = false →
      (runT K ρ φ st₁.tailNext (hintM K ρ hint) body (bodyFrame K ρ φ fres cs rd ds c as s).1).isSome := by
    intro _; rw [htl, hhint]; exact body_isSome_of_runBodyRef K ρ φ fres cs self hs' ds c dec body rd as s hok
  obtain ⟨ρ₁, Δ₁, π₁, habs₂, hnl₂, hext₁, hπ₁, r, s₂, hrun, hmean, -, hctx₂, hs₂, hg₂⟩ :=
    (ih K ρ φ).eval_step st₁ st₂ false body hint v₀ T₀ hg₁ hctx₁ _ π hs₁ hok' b₁' hev'
  rw [htl, hhint] at hrun
  obtain ⟨ρ₂, Δ₂, π₂, habs₃, hnl₃, hext₂, hπ₂, hmean', hctx₃, hs₃, hg₃⟩ :=
    runBody_back { K with Δ := Δ₁ } ρ₁ φ (fuel - 1) st₂ st' s₂ π₁ hg₂ hctx₂ hs₂ K ρ ρ₁ fres cs rd ds c body as s r hrun
      v₀ hmean d model b₂ v htail
  have hb := callee_bounded K ρ st fv cs (.fix self hs' ds c dec body) rd ws hg hfix
  have hρ₁ : ∀ σ, σ < (st.withTemps (fv :: ws.toList)).absTy.size → ρ₁ σ = ρ σ := fun σ hσ =>
    (hext₁ σ (Nat.lt_of_lt_of_le hσ habs₁)).1
  have hρ₂ : ∀ σ, σ < (st.withTemps (fv :: ws.toList)).absTy.size → ρ₂ σ = ρ σ := fun σ hσ =>
    ((hext₂ σ (Nat.lt_of_lt_of_le hσ (Nat.le_trans habs₁ habs₂))).1).trans (hρ₁ σ hσ)
  refine ⟨ρ₂, Δ₂, π₂, _, _, Nat.le_trans habs₁ (Nat.le_trans habs₂ habs₃),
    Nat.le_trans hnl₁ (Nat.le_trans hnl₂ hnl₃), fun σ hσ => ⟨hρ₂ σ hσ, ?_⟩, fun l hl => ?_,
    runBodyRef_extend K ρ φ _ cs self hs' ds c dec body rd hb fres as s ρ₁ ρ₂ hρ₁ hρ₂ r s₂ hrun,
    hmean', hctx₃, hs₃, hg₃⟩
  · have hlt₁ := Nat.lt_of_lt_of_le hσ habs₁
    exact ((hext₂ σ (Nat.lt_of_lt_of_le hlt₁ habs₂)).2).trans (hext₁ σ hlt₁).2
  · have hlt₁ := Nat.lt_of_lt_of_le hl hnl₁
    exact (hπ₂ l (Nat.lt_of_lt_of_le hlt₁ hnl₂)).trans (hπ₁ l hlt₁)

end

end Ochr.Meaning.Steps
