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
open Classical

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
def CoreSim (K : RunCtx) (ρ : Assignment) (φ : Future) (n : Nat) (t : Term) (P : MState → Prop := fun _ => True)
    (TY : Bool → Prop := fun _ => True) : Prop :=
  ∀ (st st' : MState) (typed : Bool) (hint : Option Value) (v : Value) (T? : Option Value) (s : SState)
    (π : Nat → Nat),
    P st → TY typed → Mode st → st.tailNext = false → Pre K ρ st → Rel K ρ φ π st s → Strict.SGood K.dm K.Γ φ s →
    t.valsOk (Strict.ValsP K ρ φ) → t.absBelow st.absTy.size → t.hasHolePrim = false →
    K.D.flags (scopeOf s) t = (false, false) →
    (typed = false → (runT K ρ φ st.curTail (hintM K ρ hint) t s).isSome) →
    DecTab K.D st' →
    ∀ bh, Runs (Ochr.evalCore n typed t hint) st bh (v, T?) st' →
    Out K ρ φ π st st' s (runT K ρ φ st.curTail (hintM K ρ hint) t) v T?

/-- **The step at `eval`**, for one term the aligned table does not erase: `eval_sim` with `Mode` and
the table's classification as hypotheses. -/
def EvalSim (K : RunCtx) (ρ : Assignment) (φ : Future) (n : Nat) (t : Term) (P : MState → Prop := fun _ => True)
    (TY : Bool → Prop := fun _ => True) : Prop :=
  ∀ (st st' : MState) (typed : Bool) (hint : Option Value) (v : Value) (T? : Option Value) (s : SState)
    (π : Nat → Nat),
    P st → TY typed → Mode st → Pre K ρ st → Rel K ρ φ π st s → Strict.SGood K.dm K.Γ φ s →
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
theorem eval_of_core (hE : EvalInv) {n : Nat} {t : Term} {P : MState → Prop} {TY : Bool → Prop}
    (hP : ∀ a b, Kern a b → P a → P b) (ht : ∀ w, t ≠ .val w) (hc : CoreSim K ρ φ n t P TY) :
    EvalSim K ρ φ (n + 2) t P TY := by
  intro st st' typed hint v T? s π hPs hty hm hp hr hS hv hab hnh hfl hok hD bh h
  obtain ⟨st₀, st₁, bh', hk₀, hm₀, hct, htn, h₀, hk₁, -⟩ :=
    hE n typed t hint st st' bh v T? K.D hm hD (by rw [← scopeOf_rel hr]; exact hfl) ht h
  have hc' := hc st₀ st₁ typed hint v T? s π (hP st st₀ hk₀ hPs) hty hm₀ htn (hp.of_kern hk₀) (hr.of_kern hk₀) hS hv
    (by rw [← hk₀.absTy]; exact hab) hnh hfl (by rw [hct]; exact hok) (DecTab.of_kern hk₁.symm hD) bh' h₀
  rw [hct] at hc'
  exact Out.of_kern hk₀ hk₁ hc'

/-! ## A quiet step (a private computation that only made unknowns nothing names) -/

/-- `Rel` survives a growth of the label counter, the environment kept, where every label that occurs
is below the old counter. -/
theorem _root_.Ochr.Meaning.Steps.Rel.of_env_le {K : RunCtx} {ρ : Assignment} {φ : Future} {π : Nat → Nat}
    {st st' : MState} {s : SState} (he : st'.env = st.env) (hl : st.nextLoan ≤ st'.nextLoan)
    (hlab : ∀ l, st.Occurs l → l < st.nextLoan) (hr : Rel K ρ φ π st s) : Rel K ρ φ π st' s := by
  have e1 : SM' K ρ st' = { SM' K ρ st with nextLoan := st'.nextLoan } := by simp only [SM', MState.sstate, he]
  have e2 : MState.mean K.dm K.M K.Γ ρ st' = MState.mean K.dm K.M K.Γ ρ st := by simp only [MState.mean, he]
  have e3 : ∀ l, st'.Occurs l ↔ st.Occurs l := fun l => by unfold MState.Occurs; rw [he]
  refine ⟨?_, ?_, ?_, ?_, ?_, hr.holders, hr.records⟩
  · rw [e1]; exact hr.skel
  · intro l _ ho
    have ho' := (e3 l).mp ho
    exact hr.fresh l (hlab l ho') ho'
  · rw [e2]; exact hr.sim
  · rw [he]; exact hr.inj
  · rw [he]; exact hr.sites

theorem occurs_norm (st : MState) (l : Nat) : st.norm.Occurs l ↔ st.Occurs l := by
  unfold MState.Occurs; show (∃ v ∈ Env.values st.env.erase, _) ↔ _; rw [values_erase]

/-- **`Rel` survives a quiet step.** -/
theorem _root_.Ochr.Meaning.Steps.Rel.of_quiet {K : RunCtx} {ρ : Assignment} {φ : Future} {π : Nat → Nat}
    {st st' : MState} {s : SState} (hq : Quiet st st') (hlab : ∀ l, st.Occurs l → l < st.nextLoan)
    (hr : Rel K ρ φ π st s) : Rel K ρ φ π st' s := by
  have h1 : Rel K ρ φ π { st with env := st.env.erase } s := rel_erase.mpr hr
  have h2 : Rel K ρ φ π { st' with env := st'.env.erase } s :=
    Rel.of_env_le (st := { st with env := st.env.erase }) (by show st'.env.erase = st.env.erase; exact hq.env.symm)
      hq.nextLoan (fun l ho => hlab l ((occurs_erase st l).mp ho)) h1
  exact rel_erase.mp h2

/-- The unknowns a quiet step's end names are its start's (with (WF6) at the start). -/
theorem refd_of_quiet {st st' : MState} (hq : Quiet st st') (h6 : ∀ σ, st.norm.Refd σ → σ < st.norm.absTy.size) :
    ∀ σ, st'.norm.Refd σ → st.norm.Refd σ := by
  have hb : ∀ f i : Nat, st'.norm.env[f]?.bind (fun fr : Frame => fr.binds[i]?) =
      st.norm.env[f]?.bind (fun fr : Frame => fr.binds[i]?) := fun f i => by
    show st'.env.erase[f]?.bind _ = st.env.erase[f]?.bind _; rw [hq.env]
  have hv : Env.values st'.norm.env = Env.values st.norm.env := by
    show Env.values st'.env.erase = Env.values st.env.erase; rw [hq.env]
  intro σ h
  induction h with
  | val w hw hab => rw [hv] at hw; exact .val w hw hab
  | ty f i b T hb' hT hab => rw [hb] at hb'; exact .ty f i b T hb' hT hab
  | lazyTy f i b P ws j hb' hT hab => rw [hb] at hb'; exact .lazyTy f i b P ws j hb' hT hab
  | goal G hG hab => exact .goal G (by rw [← hG]; exact hq.goal) hab
  | neutral n σ' hn hab => exact .neutral n σ' (by show (n, σ') ∈ st.neutrals; rw [hq.neutrals]; exact hn) hab
  | eta σ' w he hab => exact .eta σ' w (by show (σ', w) ∈ st.etaRefs; rw [hq.etaRefs]; exact he) hab
  | dep σ' T _ hT hab ih =>
    have hlt := h6 σ' ih
    have hT' : st.norm.absTy[σ']? = some T := by
      show st.absTy[σ']? = some T; rw [← hq.absTy σ' hlt]; exact hT
    exact .dep σ' T ih hT' hab

/-- **The assignment's facts survive a quiet step** (with (WF6) at its start). -/
theorem Asg.of_quiet {K : RunCtx} {ρ : Assignment} {st st' : MState} (hq : Quiet st st') (h : Asg K ρ st.norm)
    (h6 : WF6 st.norm) : Asg K ρ st'.norm := by
  have hR := refd_of_quiet hq h6.1
  have eA : ∀ σ, σ < st.absTy.size → MState.absTyM K.dm K.M K.Γ ρ st'.norm σ = MState.absTyM K.dm K.M K.Γ ρ st.norm σ :=
    fun σ hσ => by
      have e : st'.norm.absTy[σ]? = st.norm.absTy[σ]? := hq.absTy σ hσ
      unfold MState.absTyM; rw [e]
  obtain ⟨⟨hm, hne, het, hrf⟩, hlv, hglv, hd⟩ := h
  refine ⟨⟨fun σ hσ _ => ?_, fun n σ hmem => ?_, fun σ w hmem => ?_, fun σ r hmem => ?_⟩,
    fun σ hσ _ => ?_, fun G hG => ?_, fun σ hσ _ => ?_⟩
  · have hσ' := hR σ hσ; have hlt := h6.1 σ hσ'
    rw [eA σ hlt]; exact hm σ hσ' hlt
  · have hmem' : (n, σ) ∈ st.norm.neutrals := by show (n, σ) ∈ st.neutrals; rw [hq.neutrals]; exact hmem
    have hlt := h6.1 σ (.neutral n σ hmem' (.inl rfl))
    rw [eA σ hlt]; exact hne n σ hmem'
  · have hmem' : (σ, w) ∈ st.norm.etaRefs := by show (σ, w) ∈ st.etaRefs; rw [hq.etaRefs]; exact hmem
    have hlt := h6.1 σ (.eta σ w hmem' (.inl rfl))
    rw [eA σ hlt]; exact het σ w hmem'
  · have hmem' : (σ, r) ∈ st.norm.refs := by show (σ, r) ∈ st.refs; rw [hq.refs]; exact hmem
    have hlt := (h6.2.2.1 σ r hmem').1
    rw [eA σ hlt]; exact hrf σ r hmem'
  · have hσ' := hR σ hσ; have hlt := h6.1 σ hσ'
    rw [eA σ hlt]; exact hlv σ hσ' hlt
  · have : MState.goalM K.dm K.M K.Γ ρ st'.norm = MState.goalM K.dm K.M K.Γ ρ st.norm := by
      simp only [MState.goalM]; show Option.map _ st'.goal = Option.map _ st.goal; rw [hq.goal]
    rw [this] at hG; exact hglv G hG
  · have hσ' := hR σ hσ; have hlt := h6.1 σ hσ'
    have e : deltaOf K ρ st'.norm σ = deltaOf K ρ st.norm σ := by
      have e' : st'.norm.absTy[σ]? = st.norm.absTy[σ]? := hq.absTy σ hlt
      unfold deltaOf; rw [e']
    rw [e]; exact hd σ hσ' hlt

/-! ## Reading the invariant -/

theorem Inv.wf6 {D : Decisions} {Γ : List IndDecl} {st : MState} (h : Inv D Γ st) : WF6 st := h.2.2.2.2.1
theorem Inv.labels {D : Decisions} {Γ : List IndDecl} {st : MState} (h : Inv D Γ st) :
    ∀ l, st.Occurs l → l < st.nextLoan := h.2.2.2.2.2.2.2.2.2.2.2.2.2

/-- The labels that occur in a state are below its counter (`Inv`, read off the kernel). -/
theorem Pre.labels {K : RunCtx} {ρ : Assignment} {st : MState} (hp : Pre K ρ st) :
    ∀ l, st.Occurs l → l < st.nextLoan :=
  fun l ho => hp.inv.labels l ((occurs_norm st l).mpr ho)

theorem Quiet.withTempT {st st' : MState} (h : Quiet st st') (v : Value) (T? : Option Value) :
    Quiet (st.withTempT v T?) (st'.withTempT v T?) :=
  ⟨by rw [erase_withTempT, erase_withTempT, h.env], h.globals, h.inds, h.refs, h.etaRefs, h.goal, h.neutrals,
    h.liveScope, h.nextLoan, h.absSize, h.absTy⟩

theorem Quiet.of_kern {a b c : MState} (h₁ : Kern a b) (h₂ : Quiet b c) : Quiet a c :=
  ⟨h₁.env.trans h₂.env, h₁.globals.trans h₂.globals, h₁.inds.trans h₂.inds, h₁.refs.trans h₂.refs,
    h₁.etaRefs.trans h₂.etaRefs, h₁.goal.trans h₂.goal, h₁.neutrals.trans h₂.neutrals, h₁.liveScope.trans h₂.liveScope,
    h₁.nextLoan ▸ h₂.nextLoan, h₁.absTy ▸ h₂.absSize, fun σ hσ => by rw [h₂.absTy σ (h₁.absTy ▸ hσ), h₁.absTy]⟩

/-- A value counted in flight names at least what the state names. -/
theorem refd_mono_withTempT {st : MState} (v : Value) (T? : Option Value) :
    ∀ σ, st.norm.Refd σ → (st.withTempT v T?).norm.Refd σ := by
  intro σ h
  induction h with
  | val w hw hab =>
    refine .val w ?_ hab
    have e1 : Env.values (st.withTempT v T?).norm.env = Env.values (Env.pushTempE st.env v) := by
      show Env.values (st.withTempT v T?).env.erase = _
      rw [← erase_withTemp st v T?, values_erase]; rfl
    have e2 : Env.values st.norm.env = Env.values st.env := values_erase st.env
    rw [e2] at hw; rw [e1]
    rcases hfr : st.env[st.env.size - 1]? with _ | fr
    · have he : Env.pushTempE st.env v = st.env := by
        simp only [Env.pushTempE]
        apply Array.ext_getElem?
        intro f
        rw [Array.getElem?_modify]
        split
        · next h => subst h; rw [hfr]; rfl
        · rfl
      rw [he]; exact hw
    · have hne : 0 < st.env.size := by
        rcases Nat.eq_zero_or_pos st.env.size with h | h
        · have : st.env[st.env.size - 1]? = none := Array.getElem?_eq_none (by omega)
          rw [this] at hfr; cases hfr
        · exact h
      rw [values_pushTempE st.env v fr hfr hne]; exact List.mem_append_left _ hw
  | ty f i b T hb hT hab => rw [← binds_withTempT_norm st v T?] at hb; exact .ty f i b T hb hT hab
  | lazyTy f i b P ws j hb hT hab => rw [← binds_withTempT_norm st v T?] at hb; exact .lazyTy f i b P ws j hb hT hab
  | goal G hG hab => exact .goal G hG hab
  | neutral n σ' hn hab => exact .neutral n σ' hn hab
  | eta σ' w he hab => exact .eta σ' w he hab
  | dep σ' T _ hT hab ih => exact .dep σ' T ih hT hab

end

/-! ## `S(u)` -/

section
variable {K : RunCtx} {ρ : Assignment} {φ : Future}

/-- `S(u)`'s strict clause, where the aligned table does not erase it. -/
theorem runT_succ (tl : Bool) (hint : TyS) (u : Term) (s : SState) (hfl : K.D.flags (scopeOf s) (.succ u) = (false, false)) :
    runT K ρ φ tl hint (.succ u) s =
      SM.strictS K.dm.read (do let (v, _) ← runT K ρ φ false (.plain TyM.nat) u; pure (v.succ, .plain TyM.nat)) s := by
  rw [runT]; show SM.erasedIf (K.D.flags (scopeOf s) (.succ u)) _ s = _
  rw [hfl]; rfl

/-- **`S(u)`, at `evalCore`, for an argument whose value is a number** (`Value.Num`: what the column
needs; the general step needs the value in flight to hold no live loan, so that wrapping it moves no
site). Hypotheses beside the step for `u` (`hu`): `u`'s run reads no hint (the checker evaluates it
with none, the strict run at `Nat`), and its value is a number. The strict point (`S` of a member of
`Nat`) passes because the argument's meaning is a number. `P` is a precondition of the entry state
(the step for `u` gets `Pu` at the state it starts from, which has the entry's kernel); the
classification of `u` is asked at the entry's readings only, where `P` holds. -/
theorem succ_core (hS : SuccInv) (hIC : InvCore) {n : Nat} {u : Term} {P Pu : MState → Prop}
    (hu : EvalSim K ρ φ n u Pu) (hPu : ∀ a b, Kern a b → P a → Pu b)
    (hflu : ∀ st, P st → K.D.flags (DecideScope.topReadings st) u = (false, false))
    (hhint : ∀ s : SState, runT K ρ φ false (.plain TyM.nat) u s = runT K ρ φ false (.plain TyM.err) u s)
    (hnum : ∀ typed st₀ st₁ bh v₀ T₀, Pu st₀ → Mode st₀ → DecTab K.D st₁ →
      Runs (Ochr.eval n typed u none) st₀ bh (v₀, T₀) st₁ → v₀.Num) :
    CoreSim K ρ φ (n + 1) (.succ u) P := by
  intro st st' typed hint v T? s π hPst _ hm htn hp hr hSg hv hab hnh hfl hok hD bh h
  obtain ⟨st₀, st₁, v₀, T₀, bh₁, hk₀, hm₀, htn₀, hu₀, rfl, rfl, hq, hDb, -⟩ := hS n typed u hint st st' bh v T? hm h
  have hv₀ : v₀.Num := hnum typed st₀ st₁ bh₁ v₀ T₀ (hPu st st₀ hk₀ hPst) hm₀ (hDb K.D hD) hu₀
  have hO := hu st₀ st₁ typed none v₀ T₀ s π (hPu st st₀ hk₀ hPst) trivial hm₀ (hp.of_kern hk₀) (hr.of_kern hk₀) hSg hv
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
  obtain ⟨m, hm'⟩ := hv₀.mean
  have hr1 : r.1 = .el0 Nat m := by rw [← hmean, hm']
  have hx' : runT K ρ φ false (.plain TyM.nat) u s = some (r, s₁) := by rw [hhint]; exact hx
  have hrun : runT K ρ φ st.curTail (hintM K ρ hint) (.succ u) s = some ((.el0 Nat (m + 1), .plain TyM.nat), s₁) := by
    rw [runT_succ _ _ u s hfl]
    have hb : (runT K ρ φ false (.plain TyM.nat) u >>= fun x : Res => match x with
        | (v, _) => (pure (v.succ, TyS.plain TyM.nat) : SM Res)) s = some ((r.1.succ, .plain TyM.nat), s₁) := by
      simp only [Bind.bind]; rw [hx']; rfl
    unfold SM.strictS
    rw [hb]
    simp only [hr1, show (Sem.el0 Nat m).succ = .el0 Nat (m + 1) by rw [Sem.succ, Sem.asNat_el0]]
    rw [if_pos (show Sem.el0 Nat (m + 1) ∈ₛ[K.dm.read] (TyS.plain TyM.nat).m from ⟨m + 1, rfl⟩)]
  have hq' := hq.withTempT v₀ T₀
  have hsucc : (Value.succ v₀).Num := .succ hv₀
  refine ⟨ρ₁, Δ₁, π₁, (.el0 Nat (m + 1), .plain TyM.nat), s₁, ⟨?_, ?_, ?_, ?_⟩, hrun, ?_, fun T hT => ?_, rfl, ?_, ?_⟩
  · rw [hk₀.absTy]; exact Nat.le_trans he.abs hq.absSize
  · rw [hk₀.nextLoan]; exact Nat.le_trans he.lab hq.nextLoan
  · intro σ hσ; rw [hk₀.absTy] at hσ; exact he.agree σ hσ
  · intro l hl; rw [hk₀.nextLoan] at hl; exact he.ren l hl
  · show (meanV _ _ _ (.plain TyM.nat) v₀).succ = _
    rw [hm', Sem.succ, Sem.asNat_el0]
  · cases hT; exact strAgree_tNat
  · refine ⟨hp₁.ctx.of_eq (hq.inds.symm) (hq.globals.symm), ?_, ?_⟩
    · exact hIC (n + 1) typed (.succ u) hint st st' bh (.succ v₀) (some .tNat) K.D K.Γ hp.inv hD h
    · have ha : Asg { K with Δ := Δ₁ } ρ₁ (st'.withTempT v₀ T₀).norm := Asg.of_quiet hq' hp₁.asg hp₁.inv.wf6
      exact ha.of_refd rfl rfl rfl rfl rfl fun σ hσ =>
        refd_mono_withTempT v₀ T₀ σ (refd_withTempT_num hsucc (some .tNat) σ hσ)
  · have h1 : Rel { K with Δ := Δ₁ } ρ₁ φ π₁ (st'.withTempT v₀ T₀) s₁ := hr₁.of_quiet hq' hp₁.labels
    exact rel_withTempT_num (rel_of_withTempT_num hv₀ h1) hsucc _

end

end Ochr.Meaning.Steps.Form
