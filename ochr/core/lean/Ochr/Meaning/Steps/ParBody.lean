import Ochr.Meaning.Steps.ParSucc

/-!
# `I`'s body, `S(n)`, simulated from the generic state (lead13)

`body_simI`: the evaluation step (`EvalSim`) for `S(var 0)` at every fuel, from every state whose variable `0` holds an
unknown of type `Nat` (the parameter) and whose top frame reads `R`, assuming `ParDecI` of the table at
`R` (the decisions' lane) and the facts `EvalInv`, `EvalLow`, `SuccInv`, `InvSteps` (proved by the
machine lane), `VarNumAInv`, `InvNumA` (stated in `ParFacts`). At `I`'s generic state this is the
body's step; for every member `a` of `Nat` the assignment giving the parameter's unknown `a` meets
`Pre` there, so the one generic run simulates the reference's run at each argument.
-/

namespace Ochr.Meaning.Steps.Form

open Ochr Ochr.Meaning Ochr.Meaning.Steps

/-- `def I (n : Nat) : Nat := S(n)`: the body. -/
def bodyI : Term := .succ (.place (.var 0))

/-- The parameter's states: variable `0` holds an unknown of type `Nat`, the top frame reads `R`. -/
def ParSt (R : List DeclInfo) (st : MState) : Prop := AbsVar 0 st ∧ DecideScope.topReadings st = R

theorem ParSt.kern {R : List DeclInfo} {a b : MState} (hk : Kern a b) (h : ParSt R a) : ParSt R b :=
  ⟨h.1.of_kern hk, by rw [← ColumnC.topReadings_kern hk]; exact h.2⟩

/-- **The aligned table at `I`'s body** (a fact about the decisions, for the decisions' lane): at the
top frame's readings `R`, the read of the parameter is neither a statement nor a proof, and it and
`S(n)` read `.other`. -/
def ParDecI (D : Decisions) (R : List DeclInfo) : Prop :=
  D.flags R (.place (.var 0)) = (false, false) ∧ D.declOf R (.place (.var 0)) = .other ∧ D.declOf R bodyI = .other

theorem CoreSim.mono {K : RunCtx} {ρ : Assignment} {φ : Future} {n : Nat} {t : Term} {P Q : MState → Prop}
    {TY : Bool → Prop} (h : CoreSim K ρ φ n t P TY) (hQ : ∀ st, Q st → P st) : CoreSim K ρ φ n t Q TY :=
  fun st st' typed hint v T? s π hQs => h st st' typed hint v T? s π (hQ st hQs)

theorem tNat_beq : (Value.tNat == Value.tNat) = true := by
  first | rfl | simp [BEq.beq, Value.beq] | (unfold BEq.beq; simp [Value.beq])

/-- **What the parameter's read leaves** (from the machine's facts): a numeral over unknowns of type
`Nat` (the unknown itself), at `Nat`, with a frame. -/
theorem varAbs_run (hE : EvalInv) (hV : VarNumAInv) (hlow : EvalLow) {D : Decisions} {R : List DeclInfo}
    (hd : ParDecI D R) (n : Nat) (st₀ st₁ : MState) (bh : Nat) (v₀ : Value) (T₀ : Option Value)
    (hP : ParSt R st₀) (hm : Mode st₀) (htd : st₀.tailDecl = none) (hD : DecTab D st₁)
    (h : Runs (Ochr.eval n true (.place (.var 0)) none) st₀ bh (v₀, T₀) st₁) :
    v₀.NumA ∧ (∀ σ, v₀.hasAbs σ = true → st₁.absTy[σ]? = some .tNat) ∧ 0 < st₁.env.size ∧
      ∀ T, T₀ = some T → (T == .tNat) = true := by
  by_cases hn : n < 3
  · exact absurd h (hlow n true _ none st₀ st₁ bh _ hn (fun _ e => by cases e))
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 + 2 := ⟨n - 3, by omega⟩
  have hdo : D.declOf (DecideScope.topReadings st₀) (.place (.var 0)) = .other := by rw [hP.2]; exact hd.2.1
  obtain ⟨sa, sb, bh', hka, hma, -, -, -, -, ha, hkb, -⟩ :=
    hE (m + 1) true _ none st₀ st₁ bh v₀ T₀ D hm hD (fun _ e => by cases e) (fun _ _ _ e => by cases e)
      (by rw [hdo]; exact fun e => by cases e) (by rw [hdo]; rfl) (.inl htd) h
  obtain ⟨f, j, b, σ, hpos, hb, hbv, hty, hσT⟩ := (hP.1.of_kern hka)
  obtain ⟨rfl, hT, -, -, sq, hq, -, hcopy, hmove⟩ :=
    hV m true 0 none sa sb bh' v₀ T₀ f j b D hma hpos hb (by rw [hbv]; exact .abs σ) (by rw [hty]; rfl)
      (DecTab.of_kern hkb.symm hD) ha
  have hlt : σ < sa.absTy.size := by
    rcases Nat.lt_or_ge σ sa.absTy.size with h | h
    · exact h
    · rw [Array.getElem?_eq_none h] at hσT; cases hσT
  have hfpos : 0 < sa.env.size := by
    rcases hfr : sa.env[f]? with _ | fr
    · rw [hfr] at hb; cases hb
    · have := (Array.getElem?_eq_some_iff.mp hfr).1; omega
  have hsq : sq.absTy[σ]? = some .tNat ∧ 0 < sq.env.size := by
    refine ⟨by rw [hq.absTy σ hlt]; exact hσT, ?_⟩
    have := congrArg Array.size hq.env; simp only [Env.erase, Array.size_map] at this; omega
  have hend : sb.absTy[σ]? = some .tNat ∧ 0 < sb.env.size := by
    cases hc : D.copy (D.placeDecl (DecideScope.topReadings sa) (.var 0))
    · have hk := hmove hc
      refine ⟨by rw [← hk.absTy]; exact hsq.1, ?_⟩
      have := congrArg Array.size hk.env
      simp only [Env.erase, Array.size_map, Env.setAtE] at this
      rw [Array.size_modify] at this; omega
    · have hk := hcopy hc
      refine ⟨by rw [← hk.absTy]; exact hsq.1, ?_⟩
      have := congrArg Array.size hk.env; simp only [Env.erase, Array.size_map] at this; omega
  refine ⟨by rw [hbv]; exact .abs σ, fun σ' h' => ?_, ?_, fun T e => ?_⟩
  · rw [hbv] at h'; rw [abs_hasAbs_eq h', ← hkb.absTy]; exact hend.1
  · have := congrArg Array.size hkb.env; simp only [Env.erase, Array.size_map] at this; omega
  · have := hT T e; rw [hty] at this; cases this; exact tNat_beq

section
variable {K : RunCtx} {ρ : Assignment} {φ : Future}

/-- The parameter's read, entered as `eval` is. -/
theorem var0_sim (hE : EvalInv) (hV : VarNumAInv) (hN : InvNumA) (hlow : EvalLow) {R : List DeclInfo}
    (hd : ParDecI K.D R) : ∀ n, EvalSim K ρ φ n (.place (.var 0)) (ParSt R) (· = true) := by
  intro n
  by_cases hn : n < 3
  · intro st st' typed hint v T? s π _ _ _ _ _ _ _ _ _ _ _ _ _ bh h
    exact absurd h (hlow n typed _ hint st st' bh _ hn (fun _ e => by cases e))
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 + 2 := ⟨n - 3, by omega⟩
    refine eval_of_core hE (fun a b hk ha => ha.kern hk) (fun _ e => by cases e) (fun _ _ _ e => by cases e)
      (fun st hst => ?_) (CoreSim.mono (varAbs_core hV hN).restrict (fun st h => h.1))
    rw [hst.2, hd.2.1]; exact ⟨fun e => (by cases e), rfl⟩

/-- **`I`'s body, simulated**: the evaluation step (`EvalSim`) for `S(n)` at every fuel from every state whose parameter
holds an unknown of type `Nat` and whose top frame reads `R`, at a table meeting `ParDecI` there. -/
theorem body_simI (hE : EvalInv) (hS : SuccInv) (hI : InvSteps) (hV : VarNumAInv) (hN : InvNumA) (hlow : EvalLow)
    {R : List DeclInfo} (hd : ParDecI K.D R) : ∀ n, EvalSim K ρ φ n bodyI (ParSt R) (· = true) := by
  intro n
  by_cases hn : n < 3
  · intro st st' typed hint v T? s π _ _ _ _ _ _ _ _ _ _ _ _ _ bh h
    exact absurd h (hlow n typed _ hint st st' bh _ hn (fun _ e => by cases e))
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 + 2 := ⟨n - 3, by omega⟩
    refine eval_of_core hE (fun a b hk ha => ha.kern hk) (fun _ e => by cases e) (fun _ _ _ e => by cases e)
      (fun st hst => ?_) ?_
    · rw [hst.2, hd.2.2]; exact ⟨fun e => (by cases e), rfl⟩
    · exact succA_core hS hI hN (var0_sim hE hV hN hlow hd m) (fun a b hk ha => ha.kern hk)
        (fun st hst => by rw [hst.2]; exact hd.1)
        (fun s => by first | rfl | (rw [runT, runT]) | simp only [runT])
        (fun st₀ st₁ bh v₀ T₀ hP hm htd hD h => varAbs_run hE hV hlow hd m st₀ st₁ bh v₀ T₀ hP hm htd hD h)

end

end Ochr.Meaning.Steps.Form
