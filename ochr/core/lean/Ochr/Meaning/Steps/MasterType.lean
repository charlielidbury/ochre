import Ochr.Meaning.Steps.MasterLeaf

/-!
# The master induction's steps for the types `Nat` and `Unit`, in general (lead23, 2026-11-22; docs/31 D159)

`stepNat`, `stepUnit`: the step statements `Master.StepNat` and `Master.StepUnit` for every context and future,
every fuel, every state in the plain mode at any erased depth meeting `Pre`, every related good reference state,
typed or not. As `()`'s (`stepTt`) with a TYPE in flight: the checker's value is `Nat`/`Unit` at `Type₀` (`.sort 1`),
the reference's `.ty TyM.nat`/`.ty TyM.unit` at `univ 1`. Proved here: the checker's runs (`natInvE`, `unitInvE`, by
computation), the table at the two terms (`decTab_fixed`: read `.sort 1`, never erased), the relation and the
assignment with the type in flight (`rel_withTempT_inertO`; `refd_withTempT_noAbs`: a value naming no unknown
adds none). ASSUMES 1 fact about the checker, `InvPushType`: the invariant survives a type value in flight, as
`InvPushInert` (the machine lane's, proved) says for a number and `()`.
-/

namespace Ochr.Meaning.Steps.Form.Master

open Ochr Ochr.Meaning Ochr.Meaning.Steps Ochr.Meaning.Steps.Form
open Ochr.Meaning.DecideScope Ochr.Meaning.Steps.Machine

/-- **The invariant survives the type `Nat` or `Unit` in flight** (a fact about the checker alone, NEW; the
machine lane's `InvPushInert` covers numbers and `()`). -/
def InvPushType : Prop :=
  ∀ (D : Decisions) (Γ : List IndDecl) (st : MState) (v : Value) (T? : Option Value),
    (v = .tNat ∨ v = .tUnit) → Inv D Γ st.norm → Inv D Γ (st.withTempT v T?).norm

/-- **`evalCore` of `Nat`** (PROVED by computation): `Nat` at `Type₀`, the state as it was. -/
theorem natInvE (n : Nat) (typed : Bool) (hint : Option Value) (st st' : MState) (bh : Nat) (v : Value)
    (T? : Option Value) (h : Runs (Ochr.evalCore (n + 1) typed .nat hint) st bh (v, T?) st') :
    v = .tNat ∧ T? = some (.sort 1) ∧ st' = st := by
  obtain ⟨L, left, log, h⟩ := h
  cases bh with
  | zero =>
    have e : runMachineL (Ochr.evalCore (n + 1) typed .nat hint) st 0 L = (.exhausted "out of fuel", 0, L) := rfl
    rw [e] at h; cases h
  | succ k =>
    have e : runMachineL (Ochr.evalCore (n + 1) typed .nat hint) st (k + 1) L =
        (.ok (.tNat, some (.sort 1)) st, k, L) := rfl
    rw [e] at h
    simp only [Prod.mk.injEq, Outcome.ok.injEq] at h
    obtain ⟨⟨⟨rfl, rfl⟩, rfl⟩, -⟩ := h
    exact ⟨rfl, rfl, rfl⟩

/-- **`evalCore` of `Unit`** (PROVED by computation): `Unit` at `Type₀`, the state as it was. -/
theorem unitInvE (n : Nat) (typed : Bool) (hint : Option Value) (st st' : MState) (bh : Nat) (v : Value)
    (T? : Option Value) (h : Runs (Ochr.evalCore (n + 1) typed .unit hint) st bh (v, T?) st') :
    v = .tUnit ∧ T? = some (.sort 1) ∧ st' = st := by
  obtain ⟨L, left, log, h⟩ := h
  cases bh with
  | zero =>
    have e : runMachineL (Ochr.evalCore (n + 1) typed .unit hint) st 0 L = (.exhausted "out of fuel", 0, L) := rfl
    rw [e] at h; cases h
  | succ k =>
    have e : runMachineL (Ochr.evalCore (n + 1) typed .unit hint) st (k + 1) L =
        (.ok (.tUnit, some (.sort 1)) st, k, L) := rfl
    rw [e] at h
    simp only [Prod.mk.injEq, Outcome.ok.injEq] at h
    obtain ⟨⟨⟨rfl, rfl⟩, rfl⟩, -⟩ := h
    exact ⟨rfl, rfl, rfl⟩

/-- The table at `Nat`: read `Type₀`, not erased. -/
theorem decTab_nat {D : Decisions} {st : MState} (hD : DecTab D st) :
    (∀ sc, D.declOf sc .nat = .sort 1) ∧ (∀ sc, D.flags sc .nat = (false, false)) :=
  decTab_fixed hD .nat (.sort 1) (fun k S f l => by rw [Ochr.declOf]; rfl) (fun S f l => rfl)

/-- The table at `Unit`: read `Type₀`, not erased. -/
theorem decTab_unit {D : Decisions} {st : MState} (hD : DecTab D st) :
    (∀ sc, D.declOf sc .unit = .sort 1) ∧ (∀ sc, D.flags sc .unit = (false, false)) :=
  decTab_fixed hD .unit (.sort 1) (fun k S f l => by rw [Ochr.declOf]; rfl) (fun S f l => rfl)

/-- **A value in flight that names no unknown adds none** (`refd_withTempT_inert` for a value with no `.abs`). -/
theorem refd_withTempT_noAbs {st : MState} {v : Value} (hv : ∀ σ, v.hasAbs σ = false) (T? : Option Value) :
    ∀ σ, (st.withTempT v T?).norm.Refd σ → st.norm.Refd σ := by
  intro σ h
  induction h with
  | val w hw hab =>
    rcases values_withTempT_norm st v T? w hw with hw | rfl
    · exact .val w hw hab
    · rw [hv] at hab; cases hab
  | ty f i b T hb hT hab =>
    rw [binds_withTempT_norm] at hb
    exact .ty f i b T hb hT hab
  | lazyTy f i b P ws j hb hT hab =>
    rw [binds_withTempT_norm] at hb
    exact .lazyTy f i b P ws j hb hT hab
  | goal G hG hab => exact .goal G hG hab
  | neutral n σ' hn hab => exact .neutral n σ' hn hab
  | eta σ' w he hab => exact .eta σ' w he hab
  | dep σ' T _ hT hab ih => exact .dep σ' T ih hT hab

theorem inertO_tNat : Value.InertO .tNat := ⟨fun _ => rfl, fun _ => rfl, fun _ _ _ => rfl, rfl⟩
theorem inertO_tUnit : Value.InertO .tUnit := ⟨fun _ => rfl, fun _ => rfl, fun _ _ _ => rfl, rfl⟩

section
variable {K : RunCtx} {ρ : Assignment} {φ : Future}

/-- **A type value at `Type₀`, at `evalCore`, at any erased depth**, from the run's inversion. -/
theorem type_coreSimK (hIT : InvPushType) {n : Nat} {t : Term} {P : MState → Prop} {TY : Bool → Prop}
    (vt : Value) (m : TyM) (hvt : vt = .tNat ∨ vt = .tUnit)
    (hinv : ∀ typed hint st st' bh v T?, Runs (Ochr.evalCore (n + 1) typed t hint) st bh (v, T?) st' →
      v = vt ∧ T? = some (.sort 1) ∧ st' = st)
    (hrun : ∀ tl hint s, runT K ρ φ tl hint t s = some ((.ty m, .plain (TyM.univ 1)), s))
    (hmean : ∀ (Δ : Nat → TyS) (ρ' : Assignment) (φ' : Future) (h : TyS),
      meanV { K with Δ := Δ } ρ' φ' h vt = .ty m) :
    CoreSimK K ρ φ (n + 1) t P TY := by
  intro st st' typed hint v T? s π _ _ _ _ _ _ _ hp hr _ _ _ _ _ _ _ _ bh h
  obtain ⟨hv', hT', hst⟩ := hinv typed hint st st' bh v T? h
  subst v; subst T?; subst st'
  have hio : vt.InertO := by rcases hvt with rfl | rfl; exact inertO_tNat; exact inertO_tUnit
  have hna : ∀ σ, vt.hasAbs σ = false := by rcases hvt with rfl | rfl <;> exact fun _ => rfl
  refine ⟨⟨ρ, K.Δ, π, (.ty m, .plain (TyM.univ 1)), s, ⟨Nat.le_refl _, Nat.le_refl _, fun _ _ => ⟨rfl, rfl⟩,
    fun _ _ => rfl⟩, hrun _ _ _, hmean _ _ _ _, fun T hT => ?_, ?_, ⟨hp.ctx.of_eq rfl rfl,
    hIT K.D K.Γ st vt _ hvt hp.inv, hp.asg.of_refd rfl rfl rfl rfl rfl (refd_withTempT_noAbs hna _)⟩,
    rel_withTempT_inertO hr hio _⟩, Kept.rfl' _⟩
  · cases hT; rfl
  · rcases hvt with rfl | rfl <;> rfl

end

/-- **The step for `Nat`, in general**: `StepNat` for every context and future. ASSUMES 1 fact about the
checker, `InvPushType`. -/
theorem stepNat (hIT : InvPushType) (K : RunCtx) (φ : Future) : StepNat K φ := by
  intro n _ Δ ρ st st' typed hint v T? s π hm htl _ htd hp hr hS hv hab hhb hnh hok hD bh h
  by_cases hn : n < 3
  · exact absurd h (evalLow n typed .nat hint st st' bh _ hn (fun w e => by cases e))
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 + 2 := ⟨n - 3, by omega⟩
  obtain ⟨hdz, hfz⟩ := decTab_nat hD
  have hany : ∀ st : MState, True → K.D.declOf (DecideScope.topReadings st) .nat ≠ .any ∧
      (K.D.declOf (DecideScope.topReadings st) .nat).isProof = false :=
    fun st _ => by rw [hdz]; exact ⟨(fun e => by cases e), rfl⟩
  -- it returns a type (so the promised type's clause is vacuous)
  have hTs : TyWanted typed st → T?.isSome = true := fun _ => by
    obtain ⟨st₀, st₁, bh', -, -, -, -, -, -, h₀, -, -⟩ := evalInvD (m + 1) typed .nat hint st st' bh v T? K.D hm hD
      (fun w e => by cases e) (fun f as h e => by cases e) (hany st trivial).1 (hany st trivial).2 htd h
    obtain ⟨-, rfl, -⟩ := natInvE m typed hint st₀ st₁ bh' v T? h₀
    rfl
  exact outLK_of_outK (fun f as h e => by cases e) hTs <| eval_of_coreK (K := { K with Δ := Δ }) evalInvD (P := fun _ => True) (TY := fun _ => True)
    (fun _ _ _ _ => trivial) (fun w e => by cases e) (fun f as h e => by cases e)
    hany (type_coreSimK hIT .tNat TyM.nat (.inl rfl) (natInvE m) (fun _ _ _ => by rw [runT]; rfl)
      (fun _ _ _ _ => rfl))
    st st' typed hint v T? s π trivial trivial hm htl htd hp hr hS hv hab hhb hnh (hfz _) hok hD bh h

/-- **The step for `Unit`, in general**: `StepUnit` for every context and future. ASSUMES 1 fact about the
checker, `InvPushType`. -/
theorem stepUnit (hIT : InvPushType) (K : RunCtx) (φ : Future) : StepUnit K φ := by
  intro n _ Δ ρ st st' typed hint v T? s π hm htl _ htd hp hr hS hv hab hhb hnh hok hD bh h
  by_cases hn : n < 3
  · exact absurd h (evalLow n typed .unit hint st st' bh _ hn (fun w e => by cases e))
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 + 2 := ⟨n - 3, by omega⟩
  obtain ⟨hdz, hfz⟩ := decTab_unit hD
  have hany : ∀ st : MState, True → K.D.declOf (DecideScope.topReadings st) .unit ≠ .any ∧
      (K.D.declOf (DecideScope.topReadings st) .unit).isProof = false :=
    fun st _ => by rw [hdz]; exact ⟨(fun e => by cases e), rfl⟩
  -- it returns a type (so the promised type's clause is vacuous)
  have hTs : TyWanted typed st → T?.isSome = true := fun _ => by
    obtain ⟨st₀, st₁, bh', -, -, -, -, -, -, h₀, -, -⟩ := evalInvD (m + 1) typed .unit hint st st' bh v T? K.D hm hD
      (fun w e => by cases e) (fun f as h e => by cases e) (hany st trivial).1 (hany st trivial).2 htd h
    obtain ⟨-, rfl, -⟩ := unitInvE m typed hint st₀ st₁ bh' v T? h₀
    rfl
  exact outLK_of_outK (fun f as h e => by cases e) hTs <| eval_of_coreK (K := { K with Δ := Δ }) evalInvD (P := fun _ => True) (TY := fun _ => True)
    (fun _ _ _ _ => trivial) (fun w e => by cases e) (fun f as h e => by cases e)
    hany (type_coreSimK hIT .tUnit TyM.unit (.inr rfl) (unitInvE m) (fun _ _ _ => by rw [runT]; rfl)
      (fun _ _ _ _ => rfl))
    st st' typed hint v T? s π trivial trivial hm htl htd hp hr hS hv hab hhb hnh (hfz _) hok hD bh h

end Ochr.Meaning.Steps.Form.Master
