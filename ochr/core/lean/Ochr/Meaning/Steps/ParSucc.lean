import Ochr.Meaning.Steps.ParRead

/-!
# `S(u)` over a numeral holding an unknown (lead13)

`Column.succ_core` with `Value.NumA` for `Value.Num`: `I`'s body `S(n)` returns `S(σ₀)`. The meaning of
a numeral over unknowns is a number where the assignment gives its unknowns numbers (`NumA.mean`),
which the typed assignment does for unknowns of type `Nat` that the state names.
-/

namespace Ochr.Meaning.Steps.Form

open Ochr Ochr.Meaning Ochr.Meaning.Steps

theorem hasAbs_succ (v : Value) (σ : Nat) : (Value.succ v).hasAbs σ = v.hasAbs σ := by
  simp only [Value.hasAbs, Value.anyAtom]
  first | rfl | simp [BEq.beq, Value.beq] | (unfold BEq.beq; simp [Value.beq])

theorem _root_.Ochr.Value.NumA.inertA {v : Value} (h : v.NumA) : v.InertA := by
  refine ⟨fun P h0 _ _ hs ha => ?_, fun l => ?_, fun l pos path => ?_, ?_⟩
  · induction h with
    | zero => simp [Value.anyAtom, h0]
    | abs σ => simp [Value.anyAtom, ha σ]
    | succ _ ih => simp [Value.anyAtom, hs, ih]
  · induction h with
    | zero => rfl
    | abs σ => rfl
    | succ _ ih => simpa [Value.holdsBorrow] using ih
  · induction h generalizing path with
    | zero => simp [Value.sitesOf]
    | abs σ => simp [Value.sitesOf]
    | succ _ ih => simp [Value.sitesOf, ih]
  · cases h <;> rfl

/-- A numeral over unknowns means a number wherever its unknowns do. -/
theorem _root_.Ochr.Value.NumA.mean {v : Value} (h : v.NumA) {ρ : Assignment}
    (hρ : ∀ σ, v.hasAbs σ = true → ∃ m, ρ σ = .el0 Nat m) :
    ∃ m : Nat, ∀ (K : RunCtx) (φ : Future) (hint : TyS), meanV K ρ φ hint v = .el0 Nat m := by
  induction h with
  | zero => exact ⟨0, fun _ _ _ => rfl⟩
  | abs σ =>
    obtain ⟨m, hm⟩ := hρ σ (abs_hasAbs σ)
    exact ⟨m, fun _ _ _ => hm⟩
  | succ _ ih =>
    obtain ⟨m, hm⟩ := ih (fun σ hσ => hρ σ (by rw [hasAbs_succ]; exact hσ))
    refine ⟨m + 1, fun K φ hint => ?_⟩
    show (meanV K ρ φ (.plain TyM.nat) _).succ = _
    rw [hm, Sem.succ, Sem.asNat_el0]

/-- The value parked is among the state's values (where there is a frame to park it in). -/
theorem mem_values_withTempT (st : MState) (v : Value) (T? : Option Value) (hne : 0 < st.env.size) :
    v ∈ Env.values (st.withTempT v T?).norm.env := by
  obtain ⟨fr, hfr⟩ : ∃ fr, st.env[st.env.size - 1]? = some fr :=
    ⟨st.env[st.env.size - 1], Array.getElem?_eq_getElem (by omega)⟩
  show v ∈ Env.values (st.withTempT v T?).env.erase
  rw [← erase_withTemp st v T?, values_erase]
  show v ∈ Env.values (Env.pushTempE st.env v)
  rw [values_pushTempE st.env v fr hfr hne]; simp

section
variable {K : RunCtx} {ρ : Assignment} {φ : Future}

/-- **`S(u)` over a numeral holding unknowns** (`Column.succ_core` with `NumA`): the caller's run facts
say `u` returns a numeral whose unknowns are of type `Nat`, at `Nat`, with a frame to park it in. -/
theorem succA_core (hS : SuccInv) (hI : InvSteps) (hN : InvNumA) {n : Nat} {u : Term} {P Pu : MState → Prop}
    (hu : EvalSim K ρ φ n u Pu (· = true)) (hPu : ∀ a b, Kern a b → P a → Pu b)
    (hflu : ∀ st, P st → K.D.flags (DecideScope.topReadings st) u = (false, false))
    (hhint : ∀ s : SState, runT K ρ φ false (.plain TyM.nat) u s = runT K ρ φ false (.plain TyM.err) u s)
    (hnum : ∀ st₀ st₁ bh v₀ T₀, Pu st₀ → Mode st₀ → st₀.tailDecl = none → DecTab K.D st₁ →
      Runs (Ochr.eval n true u none) st₀ bh (v₀, T₀) st₁ → v₀.NumA ∧
        (∀ σ, v₀.hasAbs σ = true → st₁.absTy[σ]? = some .tNat) ∧ 0 < st₁.env.size ∧
        ∀ T, T₀ = some T → (T == .tNat) = true) :
    CoreSim K ρ φ (n + 1) (.succ u) P (· = true) := by
  intro st st' typed hint v T? s π hPst hty hm htn htd _ hp hr hSg hv hab hnh hfl hok hD bh h
  subst hty
  obtain ⟨st₀, st₁, v₀, T₀, bh₁, hk₀, hm₀, htn₀, htd₀, hu₀, rfl, rfl, hq, -, hDb, hty⟩ :=
    hS n true u hint st st' bh v T? hm htn htd h
  obtain ⟨st₂, bh₂, hx₂, hk₂⟩ := hty rfl
  obtain ⟨hv₀, hσ₀, hne₁, hTy⟩ := hnum st₀ st₁ bh₁ v₀ T₀ (hPu st st₀ hk₀ hPst) hm₀ htd₀ (hDb K.D hD) hu₀
  have hO := hu st₀ st₁ true none v₀ T₀ s π (hPu st st₀ hk₀ hPst) rfl hm₀ (.inl htd₀) (hp.of_kern hk₀)
    (hr.of_kern hk₀) hSg hv
    (by rw [← hk₀.absTy]; exact hab) hnh (by rw [scopeOf_rel hr]; exact hflu st hPst)
    (fun ht => by
      have hs := hok ht
      rw [runT_succ _ _ u s hfl] at hs
      rw [htn₀]
      show (runT K ρ φ false (.plain TyM.err) u s).isSome
      rw [← hhint]
      unfold SM.strictS at hs
      simp only [Bind.bind] at hs
      cases e : runT K ρ φ false (.plain TyM.nat) u s with
      | none => rw [e] at hs; simp at hs
      | some _ => rfl)
    (hDb K.D hD) bh₁ hu₀
  rw [htn₀] at hO
  obtain ⟨ρ₁, Δ₁, π₁, r, s₁, he, hx, hmean, -, -, hp₁, hr₁⟩ := hO
  have hρ₁ : ∀ σ, v₀.hasAbs σ = true → ∃ m, ρ₁ σ = .el0 Nat m := fun σ hσ =>
    asg_abs_nat (st := st₁.withTempT v₀ T₀) hp₁.asg (.val v₀ (mem_values_withTempT st₁ v₀ T₀ hne₁) hσ) (hσ₀ σ hσ)
  obtain ⟨m, hm'⟩ := hv₀.mean hρ₁
  have hr1 : r.1 = .el0 Nat m := by rw [← hmean, hm']
  have hx' : runT K ρ φ false (.plain TyM.nat) u s = some (r, s₁) := by rw [hhint]; exact hx
  have hrun : runT K ρ φ st.curTail (hintM K ρ hint) (.succ u) s = some ((.el0 Nat (m + 1), .plain TyM.nat), s₁) := by
    rw [runT_succ _ _ u s hfl]
    have hb : (runT K ρ φ false (.plain TyM.nat) u >>= fun x : Res => match x with
        | (v, _) => (pure (v.succ, TyS.plain TyM.nat) : SM Res)) s = some ((r.1.succ, .plain TyM.nat), s₁) := by
      simp only [Bind.bind]; rw [hx']; rfl
    unfold SM.strictS
    rw [hb]
    have hsu : r.1.succ = .el0 Nat (m + 1) := by rw [hr1, Sem.succ, Sem.asNat_el0]
    have hc : r.1.succ ∈ₛ[K.dm.read] (TyS.plain TyM.nat).m := by rw [hsu]; exact ⟨m + 1, rfl⟩
    dsimp only; rw [if_pos hc, hsu]
  have hq' := hq.withTempT v₀ T₀
  have hsucc : (Value.succ v₀).NumA := .succ hv₀
  have hne' : 0 < st'.env.size := by
    have := congrArg Array.size hq.env; simp only [Env.erase, Array.size_map] at this; omega
  refine ⟨ρ₁, Δ₁, π₁, (.el0 Nat (m + 1), .plain TyM.nat), s₁, ⟨?_, ?_, ?_, ?_⟩, hrun, ?_, fun T hT => ?_, rfl, ?_, ?_⟩
  · rw [hk₀.absTy]; exact Nat.le_trans he.abs hq.absSize
  · rw [hk₀.nextLoan]; exact Nat.le_trans he.lab hq.nextLoan
  · intro σ hσ; rw [hk₀.absTy] at hσ; exact he.agree σ hσ
  · intro l hl; rw [hk₀.nextLoan] at hl; exact he.ren l hl
  · show (meanV _ _ _ (.plain TyM.nat) v₀).succ = _
    rw [hm', Sem.succ, Sem.asNat_el0]
  · cases hT; exact strAgree_tNat
  · refine ⟨hp₁.ctx.of_eq (hq.inds.symm) (hq.globals.symm), ?_, ?_⟩
    · have h₁ : Inv K.D K.Γ st₁.norm := hN.pop K.D K.Γ st₁ v₀ T₀ hv₀ hp₁.inv
      have h₂ : Inv K.D K.Γ st'.norm := by rw [← hk₂.norm]; exact hI.expectTy n _ T₀ .tNat st₁ st₂ bh₂ hTy hx₂ K.D K.Γ h₁
      refine hN.push K.D K.Γ st' _ _ ⟨hsucc, fun σ hσ => ?_⟩ h₂
      rw [hasAbs_succ] at hσ
      have hlt : σ < st₁.absTy.size := by
        rcases Nat.lt_or_ge σ st₁.absTy.size with h | h
        · exact h
        · have := hσ₀ σ hσ; rw [Array.getElem?_eq_none h] at this; cases this
      rw [hq.absTy σ hlt]; exact hσ₀ σ hσ
    · have ha : Asg { K with Δ := Δ₁ } ρ₁ (st'.withTempT v₀ T₀).norm := Asg.of_quiet hq' hp₁.asg hp₁.inv.wf6
      exact ha.of_refd rfl rfl rfl rfl rfl (refd_withTempT_to rfl (refd_mono_withTempT v₀ T₀)
        (fun σ hσ => .val v₀ (mem_values_withTempT st' v₀ T₀ hne') (by rw [hasAbs_succ] at hσ; exact hσ)))
  · have h1 : Rel { K with Δ := Δ₁ } ρ₁ φ π₁ (st'.withTempT v₀ T₀) s₁ := hr₁.of_quiet hq' hp₁.labels
    exact rel_withTempT_inertA (rel_of_withTempT_inertA hv₀.inertA h1) hsucc.inertA _

end

end Ochr.Meaning.Steps.Form
