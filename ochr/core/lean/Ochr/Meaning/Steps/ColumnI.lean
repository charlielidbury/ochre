import Ochr.Meaning.Steps.ColumnIStart

/-!
# The column `I`: the body's reference run from the checker's start state (lead14)

`def I (n : Nat) : Nat := S(#0)`. From a successful typed run of the checker's `eval` on the body
from a state with `stI`'s kernel, in the plain mode: the checker's value is `S(σ0)` at `Nat` and its
end state holds no borrow (`run_bodyI`, from the machine's facts); and for every number `a` given to
`σ0`, the reference's strict run of the body from the checker's start state read as a reference state
succeeds with `S(a)` at `Nat` and no live label (`body_runI`, from `ParBody.body_simI` and the start
bundles of `ColumnIStart`).
-/

namespace Ochr.Meaning.Steps.Form.ColumnI

open Ochr Ochr.Meaning Ochr.Meaning.Steps Ochr.Meaning.Steps.Form

/-! ## The checker's side -/

/-- No position holds a borrow. -/
def NoBorrow (env : Env) : Prop := ∀ p, Env.shape env p = none

theorem NoBorrow.of_erase {e e' : Env} (h : e.erase = e'.erase) (hn : NoBorrow e) : NoBorrow e' := by
  intro p; rw [← shape_erase e', ← h, shape_erase]; exact hn p

theorem NoBorrow.setAtE_bot {e : Env} {f j : Nat} (hp : Pos.bind f j ∈ allPos e) (hn : NoBorrow e) :
    NoBorrow (Env.setAtE e (.bind f j) .bot) := by
  intro p
  by_cases hq : p = .bind f j
  · subst hq; rw [shape_eq_shapeOf, Machine.valAt_setAtE_self hp]; rfl
  · rw [shape_setAtE_other _ _ _ _ hq]; exact hn p

theorem noBorrow_stI : NoBorrow stI.env := Aux.shape_stI

theorem kern_absTy {a b : MState} (h : Kern a b) : a.absTy = b.absTy := h.absTy

/-- **The checker's run of `I`'s body**: its value is `S(σ0)`, at `Nat`, and its end state holds no
borrow. -/
theorem run_bodyI (hE : EvalInv) (hS : SuccInv) (hV : VarNumAInv) (hlow : EvalLow) {D : Decisions}
    (hd : ParDecI D [.other, .unit]) {n : Nat} {hint : Option Value} {st st' : MState} {bh : Nat}
    {v : Value} {T? : Option Value} (hk : Kern stI st) (hm : Mode st) (htd : st.tailDecl = none)
    (hD : DecTab D st') (h : Runs (Ochr.eval n true bodyI hint) st bh (v, T?) st') :
    v = .succ (.abs 0) ∧ T? = some .tNat ∧ NoBorrow st'.env := by
  have hR : DecideScope.topReadings st = [.other, .unit] := by
    rw [← ColumnC.topReadings_kern hk]; rfl
  by_cases hn : n < 3
  · exact absurd h (hlow n true _ hint st st' bh _ hn (fun _ e => by cases e))
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 + 2 := ⟨n - 3, by omega⟩
  obtain ⟨st₀, st₁, bh', hk₀, hm₀, -, htn₀, htd₀, -, h₀, hk₁, -⟩ :=
    hE (m + 1) true bodyI hint st st' bh v T? D hm hD (fun _ e => by cases e) (fun _ _ _ e => by cases e)
      (by rw [hR, hd.2.2]; exact fun e => by cases e) (by rw [hR, hd.2.2]; rfl) (.inl htd) h
  obtain ⟨sa, sb, v₀, T₀, bh₁, hka, hma, -, htda, ha, rfl, rfl, hq₁, -, hDb, -⟩ :=
    hS m true (.place (.var 0)) hint st₀ st₁ bh' v T? hm₀ htn₀ htd₀ h₀
  have hDsb : DecTab D sb := hDb D (DecTab.of_kern hk₁.symm hD)
  have hRa : DecideScope.topReadings sa = [.other, .unit] := by
    rw [← ColumnC.topReadings_kern hka, ← ColumnC.topReadings_kern hk₀, hR]
  by_cases hm3 : m < 3
  · exact absurd ha (hlow m true _ none sa sb bh₁ _ hm3 (fun _ e => by cases e))
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 + 2 := ⟨m - 3, by omega⟩
  obtain ⟨sa', sb', bh₂, hka', hma', -, -, -, -, ha', hkb', -⟩ :=
    hE (m' + 1) true (.place (.var 0)) none sa sb bh₁ v₀ T₀ D hma hDsb (fun _ e => by cases e)
      (fun _ _ _ e => by cases e) (by rw [hRa, hd.2.1]; exact fun e => by cases e) (by rw [hRa, hd.2.1]; rfl)
      (.inl htda) ha
  have hk' : Kern stI sa' := hk.trans (hk₀.trans (hka.trans hka'))
  -- the variable is `n ↦ σ0` at `Nat`
  have hpos : ckVarPos sa'.env 0 = some (.bind 1 1) := by
    rw [← ckVarPos_erase, ← hk'.env, ckVarPos_erase]; rfl
  obtain ⟨fr, hfr, hb⟩ : ∃ fr : Frame, sa'.env[1]? = some fr ∧ fr.binds[1]? = some { nB with } := by
    have e := congrArg (fun E : Env => E[1]?) hk'.env
    simp only [Env.erase, Array.getElem?_map] at e
    rcases hsa : sa'.env[1]? with _ | fr
    · rw [hsa] at e; simp [stI] at e
    · rw [hsa] at e
      have e' : Frame.erase { binds := #[unitB, nB] } = fr.erase := Option.some.inj e
      have eb := congrArg (fun F : Frame => F.binds[1]?) e'
      simp only [Frame.erase] at eb
      exact ⟨fr, rfl, by rw [← eb]; rfl⟩
  have hb' : sa'.env[1]?.bind (fun fr : Frame => fr.binds[1]?) = some nB := by rw [hfr]; exact hb
  obtain ⟨rfl, hT, -, -, sq, hq, -, hcopy, hmove⟩ :=
    hV m' true 0 none sa' sb' bh₂ v₀ T₀ 1 1 nB D hma' hpos hb' (.abs 0) rfl (DecTab.of_kern hkb'.symm hDsb) ha'
  refine ⟨rfl, rfl, ?_⟩
  have hn₀ : NoBorrow sa'.env := noBorrow_stI.of_erase hk'.env
  have hnq : NoBorrow sq.env := hn₀.of_erase hq.env
  have hnb' : NoBorrow sb'.env := by
    cases hc : D.copy (D.placeDecl (DecideScope.topReadings sa') (.var 0))
    · have hmem : Pos.bind 1 1 ∈ allPos sq.env := by
        rw [← allPos_erase, ← hq.env, allPos_erase]
        exact bind_mem_allPos _ 1 1 fr nB hfr hb
      exact (hnq.setAtE_bot hmem).of_erase (hmove hc).env
    · exact hnq.of_erase (hcopy hc).env
  exact ((hnb'.of_erase hkb'.env).of_erase hq₁.env).of_erase hk₁.env

theorem valAt_pushTempE_cases (env : Env) (v : Value) (p : Pos) :
    valAt (Env.pushTempE env v) p = v ∨ valAt (Env.pushTempE env v) p = valAt env p := by
  cases p with
  | bind f i => exact .inr (valAt_pushTempE_bind env v f i)
  | temp f i =>
    cases hfr : env[env.size - 1]? with
    | none =>
      have h0 : env.size = 0 := by
        rcases Nat.eq_zero_or_pos env.size with h | h
        · exact h
        · rw [Array.getElem?_eq_getElem (by omega)] at hfr; cases hfr
      have : env = #[] := Array.eq_empty_of_size_eq_zero h0
      subst this; exact .inr rfl
    | some fr =>
      by_cases hq : Pos.temp f i = .temp (env.size - 1) fr.temps.size
      · rw [hq]; exact .inl (valAt_pushTempE_new env v fr hfr)
      · exact .inr (valAt_pushTempE_old env v fr hfr f i hq)

theorem NoBorrow.withTempT {st : MState} {v : Value} (T? : Option Value) (hn : NoBorrow st.env)
    (hv : ∀ l w, v ≠ .borrow l w) : NoBorrow (st.withTempT v T?).env := by
  intro p
  rw [shape_eq_shapeOf, valAt_withTempT]
  rcases valAt_pushTempE_cases st.env v p with e | e <;> rw [e]
  · cases v <;> first | rfl | exact absurd rfl (hv _ _)
  · rw [← shape_eq_shapeOf]; exact hn p

/-- A reference state related to a checker state with no borrow has no live label. -/
theorem liveLabels_of_rel {K : RunCtx} {ρ : Assignment} {φ : Future} {π : Nat → Nat} {st : MState} {s : SState}
    (hr : Rel K ρ φ π st s) (hn : NoBorrow st.env) : s.liveLabels = [] := by
  have hs : ∀ p, s.shape p = none := by
    intro p
    cases hsp : s.shape p with
    | none => rfl
    | some l' =>
      cases p with
      | bind f i =>
        obtain ⟨l, hl, -⟩ := hr.sim.2.2.1 (.bind f i) l' (fun h => h) hsp
        exact absurd hl (by show Env.shape st.env _ ≠ _; rw [hn]; exact fun e => by cases e)
      | temp f j =>
        obtain ⟨i, l, hl, -⟩ := hr.sim.2.2.2.2 f j l' hsp
        exact absurd hl (by show Env.shape st.env _ ≠ _; rw [hn]; exact fun e => by cases e)
  rw [SState.liveLabels, List.filterMap_eq_nil_iff.mpr (fun p _ => hs p)]; simp

/-! ## The reference's run of the body -/

/-- `σ0` given the number `a`. -/
def ρAt (ρ : Assignment) (a : Nat) : Assignment := fun σ => if σ = 0 then .el0 Nat a else ρ σ

/-- **The body's reference run** from the checker's start state read as a reference state, under the
assignment giving `σ0` any number `a`: it succeeds with `S(a)` at `Nat` and leaves no live label. -/
theorem body_runI (hE : EvalInv) (hS : SuccInv) (hI : InvSteps) (hV : VarNumAInv) (hN : InvNumA) (hlow : EvalLow)
    (dm : DataModel) (D : Decisions) (ρ : Assignment) (φ : Future) (a : Nat) (hDI : DecTab D stI)
    {n : Nat} {hint : Option Value} {st st' : MState} {bh : Nat} {v : Value} {T? : Option Value}
    (hk : Kern stI st) (hm : Mode st) (htd : st.tailDecl = none) (hD : DecTab D st')
    (h : Runs (Ochr.eval n true bodyI hint) st bh (v, T?) st') :
    ∃ r s', runT (KI dm D φ) (ρAt ρ a) φ st.tailNext (hintM (KI dm D φ) (ρAt ρ a) hint) bodyI
        (SM' (KI dm D φ) (ρAt ρ a) stI) = some (r, s') ∧
      r.1 = .el0 Nat (a + 1) ∧ r.2.m = TyM.nat ∧ s'.liveLabels = [] := by
  have hpd := parDecI hDI
  obtain ⟨rfl, rfl, hnb⟩ := run_bodyI hE hS hV hlow hpd hk hm htd hD h
  have hρ : ∃ m, ρAt ρ a 0 = .el0 Nat m := ⟨a, rfl⟩
  have hsc : scopeOf (SM' (KI dm D φ) (ρAt ρ a) stI) = [.other, .unit] := by
    rw [scopeOf_sstate']; rfl
  obtain ⟨ρ', Δ', π', r, s', hext, hx, hmean, hagree, -, -, hrel⟩ :=
    body_simI (K := KI dm D φ) (ρ := ρAt ρ a) (φ := φ) hE hS hI hV hN hlow hpd n st st' true hint _ _
      (SM' (KI dm D φ) (ρAt ρ a) stI) id
      ⟨absVar_stI.of_kern hk, by rw [← ColumnC.topReadings_kern hk]; rfl⟩ rfl hm (.inl htd)
      ((pre_stI dm D (ρAt ρ a) φ hρ).of_kern hk) ((rel_stI dm D (ρAt ρ a) φ φ).of_kern hk)
      (sgood_stI dm D (ρAt ρ a) φ φ hρ) (by simp [bodyI, Term.valsOk])
      (fun σ hσ => by simp [bodyI, Term.anyAtom] at hσ) (by decide)
      (by rw [hsc]; exact flags_bodyI hDI) (fun e => by cases e) hD bh h
  refine ⟨r, s', hx, ?_, ?_, liveLabels_of_rel hrel (hnb.withTempT _ (fun _ _ e => by cases e))⟩
  · have h0 : ρ' 0 = ρAt ρ a 0 := (hext.agree 0 (by rw [← kern_absTy hk]; decide)).1
    rw [← hmean]
    show (ρ' 0).succ = _
    rw [h0]
    show Sem.succ (.el0 Nat a) = _
    rw [Sem.succ, Sem.asNat_el0]
  · rw [← hagree _ rfl]; rfl

end Ochr.Meaning.Steps.Form.ColumnI
