import Ochr.Meaning.Steps.ColumnTemp
import Ochr.Meaning.Steps.FormMachine

/-!
# The column: the form of `Steps/Form.lean` proved on a narrow set of steps (lead7)

Each step here is a theorem in (II)'s form, proved with no `sorry`, from:
* (I), the fundamental lemma, `Strict.fund_all` (or the operation lemmas of `Strict/`), where a good
  reference state between two sub-steps is needed;
* the facts about the checker alone of `Steps/FormMachine.lean`, as hypotheses;
* the step's sub-steps, as hypotheses of the same form, where it has any (the induction on fuel
  supplies them; the top-level assembly, `Steps/ColumnAssembly.lean`, supplies them for its program).

The steps: `Z` (`zero_core`); `eval` around `evalCore` for a term the pre-pass does not erase
(`eval_of_core`); …
-/

namespace Ochr.Meaning.Steps.Form

open Ochr Ochr.Meaning Ochr.Meaning.Steps

section
variable {K : RunCtx} {ρ : Assignment} {φ : Future}

theorem runT_zero (tl : Bool) (hint : TyS) (s : SState) :
    runT K ρ φ tl hint .zero s = some ((.el0 Nat 0, .plain TyM.nat), s) := by
  rw [runT]; rfl

/-- The checker's `Nat` is the run's. -/
theorem strAgree_tNat : StrAgree K ρ .tNat (.plain TyM.nat) := rfl

/-- `Pre` with a number in flight, given the invariant there (the checker's discipline). -/
theorem Pre.withTempT_num {st : MState} (hp : Pre K ρ st) {v : Value} (hv : v.Num) (T? : Option Value)
    (hinv : Inv K.D K.Γ (st.withTempT v T?).norm) : Pre K ρ (st.withTempT v T?) :=
  ⟨hp.ctx.of_eq rfl rfl, hinv, asg_withTempT_num hp.asg hv T?⟩

/-- **`Z`, at `evalCore`.** -/
theorem zero_core (hZ : ZeroInv) (hIC : InvCore) {n : Nat} {typed : Bool} {hint : Option Value}
    {st st' : MState} {bh : Nat} {v : Value} {T? : Option Value} (s : SState) (π : Nat → Nat)
    (hp : Pre K ρ st) (hr : Rel K ρ φ π st s) (hD : DecTab K.D st')
    (h : Runs (Ochr.evalCore (n + 1) typed .zero hint) st bh (v, T?) st') :
    Out K ρ φ π st st' s (runT K ρ φ st.curTail (hintM K ρ hint) .zero) v T? := by
  obtain ⟨rfl, rfl, hk, -⟩ := hZ n typed hint st st' bh v T? h
  have hinv : Inv K.D K.Γ (st'.withTempT .zero (some .tNat)).norm :=
    hIC (n + 1) typed .zero hint st st' bh .zero (some .tNat) K.D K.Γ hp.inv hD h
  refine ⟨ρ, K.Δ, π, (.el0 Nat 0, .plain TyM.nat), s, ⟨?_, ?_, fun _ _ => ⟨rfl, rfl⟩, fun _ _ => rfl⟩,
    runT_zero _ _ _, rfl, fun T hT => ?_, rfl, ?_, ?_⟩
  · rw [hk.absTy]; exact Nat.le_refl _
  · rw [hk.nextLoan]; exact Nat.le_refl _
  · cases hT; exact strAgree_tNat
  · exact (hp.of_kern hk).withTempT_num .zero _ hinv
  · exact rel_withTempT_num (hr.of_kern hk) .zero _

/-! ## The scope the reference reads is the checker's top frame's readings -/

theorem scopeOf_eq_skel (s : SState) :
    scopeOf s = (((s.env.map fun fr => fr.binds.map bindSkel).getLast?.map fun l => l.map Prod.snd).getD []).reverse := by
  unfold scopeOf
  rw [List.getLast?_map]
  cases s.env.getLast? with
  | none => rfl
  | some fr => simp [bindSkel, List.map_map, Function.comp_def]

theorem scopeOf_sstate' (st : MState) : scopeOf (SM' K ρ st) = DecideScope.topReadings st := by
  unfold scopeOf DecideScope.topReadings
  simp only [SM', MState.sstate, List.getLast?_map, List.getLast?_zipIdx, Array.getLast?_toList]
  cases st.env.back? with
  | none => rfl
  | some fr =>
    simp only [Option.map_some, Option.getD_some, List.map_map]
    congr 1
    conv => rhs; rw [← List.zipIdx_map_fst 0 fr.binds.toList, List.map_map]
    rfl

/-- **The reference's scope is the checker's**, at related states. -/
theorem scopeOf_rel {π : Nat → Nat} {st : MState} {s : SState} (hr : Rel K ρ φ π st s) :
    scopeOf s = DecideScope.topReadings st := by
  rw [← scopeOf_sstate', scopeOf_eq_skel, scopeOf_eq_skel (SM' K ρ st), hr.skel]

end

/-! ## `eval` around `evalCore` -/

/-- **The step at `evalCore`**, for one term: the conclusion of `eval_sim`, for a run of `evalCore`
entered as `eval` enters it (in `Mode`, the tail flag in `curTail`, the one-shot flag clear), the term
not erased by the aligned table. -/
def CoreSim (K : RunCtx) (ρ : Assignment) (φ : Future) (n : Nat) (t : Term) : Prop :=
  ∀ (st st' : MState) (typed : Bool) (hint : Option Value) (v : Value) (T? : Option Value) (s : SState)
    (π : Nat → Nat),
    Mode st → st.tailNext = false → Pre K ρ st → Rel K ρ φ π st s → Strict.SGood K.dm K.Γ φ s →
    t.valsOk (Strict.ValsP K ρ φ) → t.absBelow st.absTy.size → t.hasHolePrim = false →
    K.D.flags (scopeOf s) t = (false, false) →
    (typed = false → (runT K ρ φ st.curTail (hintM K ρ hint) t s).isSome) →
    DecTab K.D st' →
    ∀ bh, Runs (Ochr.evalCore n typed t hint) st bh (v, T?) st' →
    Out K ρ φ π st st' s (runT K ρ φ st.curTail (hintM K ρ hint) t) v T?

/-- **The step at `eval`**, for one term the aligned table does not erase: `eval_sim` with `Mode` and
the table's classification as hypotheses. -/
def EvalSim (K : RunCtx) (ρ : Assignment) (φ : Future) (n : Nat) (t : Term) : Prop :=
  ∀ (st st' : MState) (typed : Bool) (hint : Option Value) (v : Value) (T? : Option Value) (s : SState)
    (π : Nat → Nat),
    Mode st → Pre K ρ st → Rel K ρ φ π st s → Strict.SGood K.dm K.Γ φ s →
    t.valsOk (Strict.ValsP K ρ φ) → t.absBelow st.absTy.size → t.hasHolePrim = false →
    K.D.flags (scopeOf s) t = (false, false) →
    (typed = false → (runT K ρ φ st.tailNext (hintM K ρ hint) t s).isSome) →
    DecTab K.D st' →
    ∀ bh, Runs (Ochr.eval n typed t hint) st bh (v, T?) st' →
    Out K ρ φ π st st' s (runT K ρ φ st.tailNext (hintM K ρ hint) t) v T?

section
variable {K : RunCtx} {ρ : Assignment} {φ : Future}

/-- A step's conclusion carries across the bookkeeping around it. -/
theorem Out.of_kern {π : Nat → Nat} {st₀ st₁ st st' : MState} {s : SState} {x : SM Res} {v : Value}
    {T? : Option Value} (h₀ : Kern st st₀) (h₁ : Kern st₁ st') (h : Out K ρ φ π st₀ st₁ s x v T?) :
    Out K ρ φ π st st' s x v T? := by
  obtain ⟨ρ', Δ', π', r, s', he, hx, hm, ha, hl, hp, hr⟩ := h
  refine ⟨ρ', Δ', π', r, s', ⟨?_, ?_, ?_, ?_⟩, hx, hm, ha, hl, hp.of_kern (h₁.withTempT v T?), hr.of_kern (h₁.withTempT v T?)⟩
  · rw [h₀.absTy, ← h₁.absTy]; exact he.abs
  · rw [h₀.nextLoan, ← h₁.nextLoan]; exact he.lab
  · intro σ hσ; rw [h₀.absTy] at hσ; exact he.agree σ hσ
  · intro l hl; rw [h₀.nextLoan] at hl; exact he.ren l hl

/-- **`eval` around `evalCore`**: the step at `evalCore` gives the step at `eval`, for a term that is
not an embedded value, through the checker's `eval` (`EvalInv`). -/
theorem eval_of_core (hE : EvalInv) {n : Nat} {t : Term} (ht : ∀ w, t ≠ .val w) (hc : CoreSim K ρ φ n t) :
    EvalSim K ρ φ (n + 2) t := by
  intro st st' typed hint v T? s π hm hp hr hS hv hab hnh hfl hok hD bh h
  obtain ⟨st₀, st₁, bh', hk₀, hm₀, hct, htn, h₀, hk₁, -⟩ :=
    hE n typed t hint st st' bh v T? K.D hm hD (by rw [← scopeOf_rel hr]; exact hfl) ht h
  have hc' := hc st₀ st₁ typed hint v T? s π hm₀ htn (hp.of_kern hk₀) (hr.of_kern hk₀) hS hv
    (by rw [← hk₀.absTy]; exact hab) hnh hfl (by rw [hct]; exact hok) (DecTab.of_kern hk₁.symm hD) bh' h₀
  rw [hct] at hc'
  exact Out.of_kern hk₀ hk₁ hc'

end

end Ochr.Meaning.Steps.Form
