import Ochr.Meaning.Steps.MasterDepth
import Ochr.Meaning.Steps.Machine.FragFree

/-!
# The master induction's leaf steps: `Z` and `()` in general (lead22, 2026-11-22; docs/31 D151)

`stepZero` and `stepTt`: the step statements `Master.StepZero` and `Master.StepTt`, for every context, every
fuel, every state in the plain mode meeting `Pre`, every related good reference state, typed or not; no
fragment invariant and no program's state, at any erased depth (D155). Each from proved facts about the checker
(`evalLow`, `zeroInv`, `invSteps` the machine lane's; `evalInvD` at any depth, `zeroInvE`, `ttInvE` here), and
the table's answers at the two terms, read off `DecTab` by running the checker's decision procedures (no
fact assumed). So both steps ASSUME NOTHING.
-/

namespace Ochr.Meaning.Steps.Form.Master

open Ochr Ochr.Meaning Ochr.Meaning.Steps Ochr.Meaning.Steps.Form
open Ochr.Meaning.DecideScope Ochr.Meaning.Steps.Machine

/-! ## The table at a term whose reading is fixed -/

/-- **The table's reading and flags at a term whose reading the checker computes outright**: where
`declOf` of `t` returns `d` at every fuel above `0` and every state, and the pre-pass at `d` neither erases
nor makes a proof, a table aligned at any state reads `d` at every scope and leaves `t` unerased. -/
theorem decTab_fixed {D : Decisions} {st : MState} (hD : DecTab D st) (t : Term) (d : DeclInfo)
    (hdecl : ∀ (k : Nat) (S : MState) f l,
      runAll (Ochr.declOf (k + 1) false [] [] t) S f l = ((.ok (.ok (d, S)), f), l))
    (hpre : ∀ (S : MState) f l, runAll (Ochr.preFlags t d) S f l = ((.ok (.ok (some (false, false), S)), f), l)) :
    (∀ sc, D.declOf sc t = d) ∧ (∀ sc, D.flags sc t = (false, false)) := by
  have hw : ∀ sc f l, runAll (withLive true (Ochr.declOf 1 false [] [] t)) (scopeState st sc) f l =
      ((.ok (.ok (d, scopeState st sc)), f), l) := fun sc f l => runAll_withLive_pure (hdecl 0 _ f l)
  refine ⟨fun sc => hD.declOf 1 sc t d 0 _ (runs_of_runAll (hw sc ⟨0⟩ #[])), fun sc => ?_⟩
  have hfl : runAll (do
      let d ← withLive true (Ochr.declOf 1 false [] [] t)
      pure ((← Ochr.preFlags t d).getD (false, false))) (scopeState st sc) ⟨0⟩ #[] =
      ((.ok (.ok ((false, false), scopeState st sc)), ⟨0⟩), #[]) := by
    rw [runAll_bind, hw sc]
    simp only
    rw [runAll_bind, hpre]
    rfl
  exact hD.flags 1 sc t (false, false) 0 _ (runs_of_runAll hfl)

/-- The table at `Z`: read `.other`, not erased. -/
theorem decTab_zero {D : Decisions} {st : MState} (hD : DecTab D st) :
    (∀ sc, D.declOf sc .zero = .other) ∧ (∀ sc, D.flags sc .zero = (false, false)) :=
  decTab_fixed hD .zero .other (fun k S f l => by rw [Ochr.declOf]; rfl) (fun S f l => rfl)

/-- The table at `()`: read `.unit`, not erased. -/
theorem decTab_tt {D : Decisions} {st : MState} (hD : DecTab D st) :
    (∀ sc, D.declOf sc .tt = .unit) ∧ (∀ sc, D.flags sc .tt = (false, false)) :=
  decTab_fixed hD .tt .unit (fun k S f l => by rw [Ochr.declOf]; rfl) (fun S f l => rfl)

/-! ## `()` at `evalCore` -/

/-- **`evalCore` of `Z`, its state** (a fact about the checker alone, PROVED by computation, as `zeroInv`): the
value `Z` at `Nat`, the state as it was (so the kernel and the mode at any erased depth). -/
theorem zeroInvE (n : Nat) (typed : Bool) (hint : Option Value) (st st' : MState) (bh : Nat) (v : Value)
    (T? : Option Value) (h : Runs (Ochr.evalCore (n + 1) typed .zero hint) st bh (v, T?) st') :
    v = .zero ∧ T? = some .tNat ∧ st' = st := by
  obtain ⟨L, left, log, h⟩ := h
  cases bh with
  | zero =>
    have e : runMachineL (Ochr.evalCore (n + 1) typed .zero hint) st 0 L = (.exhausted "out of fuel", 0, L) := rfl
    rw [e] at h; cases h
  | succ k =>
    have e : runMachineL (Ochr.evalCore (n + 1) typed .zero hint) st (k + 1) L =
        (.ok (.zero, some .tNat) st, k, L) := rfl
    rw [e] at h
    simp only [Prod.mk.injEq, Outcome.ok.injEq] at h
    obtain ⟨⟨⟨rfl, rfl⟩, rfl⟩, -⟩ := h
    exact ⟨rfl, rfl, rfl⟩

/-- **`evalCore` of `()`** (a fact about the checker alone, PROVED by computation): the value `()` at `Unit`,
the state as it was. -/
theorem ttInvE (n : Nat) (typed : Bool) (hint : Option Value) (st st' : MState) (bh : Nat) (v : Value)
    (T? : Option Value) (h : Runs (Ochr.evalCore (n + 1) typed .tt hint) st bh (v, T?) st') :
    v = .unit ∧ T? = some .tUnit ∧ st' = st := by
  obtain ⟨L, left, log, h⟩ := h
  cases bh with
  | zero =>
    have e : runMachineL (Ochr.evalCore (n + 1) typed .tt hint) st 0 L = (.exhausted "out of fuel", 0, L) := rfl
    rw [e] at h; cases h
  | succ k =>
    have e : runMachineL (Ochr.evalCore (n + 1) typed .tt hint) st (k + 1) L =
        (.ok (.unit, some .tUnit) st, k, L) := rfl
    rw [e] at h
    simp only [Prod.mk.injEq, Outcome.ok.injEq] at h
    obtain ⟨⟨⟨rfl, rfl⟩, rfl⟩, -⟩ := h
    exact ⟨rfl, rfl, rfl⟩

section
variable {K : RunCtx} {ρ : Assignment} {φ : Future}

theorem runT_tt (tl : Bool) (hint : TyS) (s : SState) :
    runT K ρ φ tl hint .tt s = some ((.el0 Unit (), .plain TyM.unit), s) := by
  rw [runT]; rfl

/-- **`()`, at `evalCore`, at any erased depth**, from every state meeting `Pre` and every related reference
state. -/
theorem tt_coreSimK {n : Nat} {P : MState → Prop} {TY : Bool → Prop} : CoreSimK K ρ φ (n + 1) .tt P TY := by
  intro st st' typed hint v T? s π _ _ _ _ _ _ _ hp hr _ _ _ _ _ _ _ _ bh h
  obtain ⟨rfl, rfl, hst⟩ := ttInvE n typed hint st st' bh v T? h
  subst st'
  have hinv : Inv K.D K.Γ (st.withTempT .unit (some .tUnit)).norm :=
    invSteps.pushInert K.D K.Γ st .unit _ (.inr rfl) hp.inv
  refine ⟨⟨ρ, K.Δ, π, (.el0 Unit (), .plain TyM.unit), s, ⟨Nat.le_refl _, Nat.le_refl _, fun _ _ => ⟨rfl, rfl⟩,
    fun _ _ => rfl⟩, runT_tt _ _ _, rfl, fun T hT => ?_, rfl, ⟨hp.ctx.of_eq rfl rfl, hinv,
    asg_withTempT_inert hp.asg Value.inert_unit _⟩, rel_withTempT_inert hr Value.inert_unit _⟩, Kept.rfl' _⟩
  cases hT; rfl

/-- **`Z`, at `evalCore`, at any erased depth.** -/
theorem zero_coreSimK {n : Nat} {P : MState → Prop} {TY : Bool → Prop} : CoreSimK K ρ φ (n + 1) .zero P TY := by
  intro st st' typed hint v T? s π _ _ _ _ _ _ _ hp hr _ _ _ _ _ _ _ hD bh h
  refine ⟨zero_core zeroInv invSteps s π hp hr hD h, ?_⟩
  obtain ⟨-, -, hst⟩ := zeroInvE n typed hint st st' bh v T? h
  subst st'
  exact Kept.rfl' _

end

/-! ## The two steps -/

/-- **The step for `Z`, in general**: `StepZero` for every context and future. ASSUMES NOTHING (the facts
about the checker it uses are the machine lane's proved `evalLow`, `zeroInv`, `invSteps`, and `evalInvD`, `zeroInvE` proved here at any erased depth). -/
theorem stepZero (K : RunCtx) (φ : Future) : StepZero K φ := by
  intro n _ Δ ρ st st' typed hint v T? s π hm htl _ htd hp hr hS hv hab hhb hnh hok hD bh h
  by_cases hn : n < 3
  · exact absurd h (evalLow n typed .zero hint st st' bh _ hn (fun w e => by cases e))
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 + 2 := ⟨n - 3, by omega⟩
  obtain ⟨hdz, hfz⟩ := decTab_zero hD
  have hany : ∀ st : MState, True → K.D.declOf (DecideScope.topReadings st) .zero ≠ .any ∧
      (K.D.declOf (DecideScope.topReadings st) .zero).isProof = false :=
    fun st _ => by rw [hdz]; exact ⟨(fun e => by cases e), rfl⟩
  exact outLK_of_outK (fun f as h e => by cases e) <| eval_of_coreK (K := { K with Δ := Δ }) evalInvD (P := fun _ => True) (TY := fun _ => True)
    (fun _ _ _ _ => trivial) (fun w e => by cases e) (fun f as h e => by cases e)
    hany zero_coreSimK
    st st' typed hint v T? s π trivial trivial hm htl htd hp hr hS hv hab hhb hnh (hfz _) hok hD bh h

/-- **The step for `()`, in general**: `StepTt` for every context and future. ASSUMES NOTHING. -/
theorem stepTt (K : RunCtx) (φ : Future) : StepTt K φ := by
  intro n _ Δ ρ st st' typed hint v T? s π hm htl _ htd hp hr hS hv hab hhb hnh hok hD bh h
  by_cases hn : n < 3
  · exact absurd h (evalLow n typed .tt hint st st' bh _ hn (fun w e => by cases e))
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 + 2 := ⟨n - 3, by omega⟩
  obtain ⟨hdt, hft⟩ := decTab_tt hD
  have hany : ∀ st : MState, True → K.D.declOf (DecideScope.topReadings st) .tt ≠ .any ∧
      (K.D.declOf (DecideScope.topReadings st) .tt).isProof = false :=
    fun st _ => by rw [hdt]; exact ⟨(fun e => by cases e), rfl⟩
  exact outLK_of_outK (fun f as h e => by cases e) <| eval_of_coreK (K := { K with Δ := Δ }) evalInvD (P := fun _ => True) (TY := fun _ => True)
    (fun _ _ _ _ => trivial) (fun w e => by cases e) (fun f as h e => by cases e)
    hany tt_coreSimK
    st st' typed hint v T? s π trivial trivial hm htl htd hp hr hS hv hab hhb hnh (hft _) hok hD bh h

end Ochr.Meaning.Steps.Form.Master
