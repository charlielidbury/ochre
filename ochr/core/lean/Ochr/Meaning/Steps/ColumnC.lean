import Ochr.Meaning.Steps.ColumnStart
import Ochr.Meaning.Steps.MachineMono

/-!
# The column applied: `def C : Nat := let x = S(Z); x` (lead7)

The smallest top-level assembly of part (II). The steps of the column (`Column.lean`: `Z`, `S(u)`,
`eval` around `evalCore`; `ColumnRead.lean`: the read of a variable; `ColumnLet.lean`: the typed
`let`) are composed into the step for the body of `C` (`sim_bodyC`), and applied at the state
`checkDef` evaluates a constant's body from, with every bundle of hypotheses instantiated there
(`ColumnStart.lean`). The conclusion (`column_C`): for every accepted run of the checker on the
body, the strict run of the body from the reference state succeeds, and its value means `1`, a
member of `Nat`.

What is assumed, all facts about the checker alone (none about the model), each stated in
`FormMachine.lean` or `MachineMono.lean`: the inversions `EvalInv`, `ZeroInv`, `SuccInv`,
`VarNumInv`, `LetInv`, `DropNoopInv`; the invariant's preservation `InvCore`; and, for the table of
decisions, that a run only extends the tables (`GrowsM` of the body's `eval`) and that alignment
passes to a state with smaller tables (`DecTab.back`, stated here as `DecBack`). The decisions'
alignment at the end of the run (`DecTab D st'`) is the theorem's hypothesis, met by the fuel-free
table given `DecideFuelAgree` (`column_C_ff`).

The checker's run itself is not kernel-evaluable (the variable read goes through code the kernel
does not unfold), so it is `#guard`ed below: the checker accepts `C`, and its run of the body from
`stC` succeeds.
-/

namespace Ochr.Meaning.Steps.Form.ColumnC

open Ochr Ochr.Meaning Ochr.Meaning.Steps Ochr.Meaning.Steps.Form
open Classical

/-! ## Generic: monotonicity, `Z` as a step, scope readings under the kernel -/

section
variable {K : RunCtx} {ρ : Assignment} {φ : Future}

theorem CoreSim.mono {n : Nat} {t : Term} {P P' : MState → Prop} {TY TY' : Bool → Prop}
    (h : CoreSim K ρ φ n t P TY) (hP : ∀ st, P' st → P st) (hT : ∀ b, TY' b → TY b) : CoreSim K ρ φ n t P' TY' :=
  fun st st' typed hint v T? s π hp ht => h st st' typed hint v T? s π (hP st hp) (hT typed ht)

theorem zero_coreSim (hZ : ZeroInv) (hIC : InvCore) {n : Nat} {P : MState → Prop} {TY : Bool → Prop} :
    CoreSim K ρ φ (n + 1) .zero P TY := by
  intro st st' typed hint v T? s π _ _ _ _ _ _ hp hr _ _ _ _ _ _ hD bh h
  exact zero_core hZ hIC s π hp hr hD h

end

theorem topReadings_env {a b : MState} (h : a.env = b.env) : DecideScope.topReadings a = DecideScope.topReadings b := by
  simp only [DecideScope.topReadings, h]

theorem topReadings_erase (st : MState) :
    DecideScope.topReadings { st with env := Env.erase st.env } = DecideScope.topReadings st := by
  simp only [DecideScope.topReadings, Env.erase, Array.back?_map]
  cases st.env.back? <;> rfl

theorem topReadings_of_erase {a b : MState} (h : Env.erase a.env = Env.erase b.env) :
    DecideScope.topReadings a = DecideScope.topReadings b := by
  rw [← topReadings_erase a, ← topReadings_erase b]; exact topReadings_env h

theorem topReadings_kern {a b : MState} (h : Kern a b) : DecideScope.topReadings a = DecideScope.topReadings b :=
  topReadings_of_erase h.env

theorem size_of_erase {e₁ e₂ : Env} (h : Env.erase e₁ = Env.erase e₂) : e₁.size = e₂.size := by
  rw [← Env.erase_size e₁, h, Env.erase_size]

/-- Two environments with one erasure have their top frames' bindings in common. -/
theorem top_of_erase {e₁ e₂ : Env} (h : Env.erase e₁ = Env.erase e₂) {fr : Frame}
    (hfr : e₁[e₁.size - 1]? = some fr) : ∃ fr', e₂[e₂.size - 1]? = some fr' ∧ fr'.binds = fr.binds := by
  have hs := size_of_erase h
  have e := congrArg (fun e : Env => e[e₁.size - 1]?) h
  simp only [Env.erase_get?, hfr, Option.map_some] at e
  rw [← hs]
  rcases h2 : e₂[e₁.size - 1]? with _ | fr'
  · rw [h2] at e; cases e
  · rw [h2] at e
    exact ⟨fr', rfl, (congrArg Frame.binds (Option.some.inj e)).symm⟩

/-- The top frame after a binding is pushed. -/
theorem top_pushBindE {env : Env} {fr : Frame} (hfr : env[env.size - 1]? = some fr) (h : Hint) (ty : Option Value)
    (v : Value) (p : Bool) (d : DeclInfo) :
    (Env.pushBindE env h ty v p d)[(Env.pushBindE env h ty v p d).size - 1]? =
      some { fr with binds := fr.binds.push { hint := h, ty, val := v, proof := p, decl := d } } := by
  simp only [Env.pushBindE, Array.size_modify, Array.getElem?_modify, if_true, hfr, Option.map_some]

theorem topReadings_pushBindE {st : MState} {fr : Frame} (hfr : st.env[st.env.size - 1]? = some fr) (h : Hint)
    (ty : Option Value) (v : Value) (p : Bool) (d : DeclInfo) :
    DecideScope.topReadings { st with env := Env.pushBindE st.env h ty v p d } = d :: DecideScope.topReadings st := by
  have e := top_pushBindE hfr h ty v p d
  simp only [DecideScope.topReadings, Array.back?_eq_getElem?] at e ⊢
  rw [e, hfr]
  simp [Array.toList_push, List.map_append, List.reverse_append]

/-- The top frame after the top binding is overwritten with `⊥`. -/
theorem top_setAt_bot {env : Env} {fr : Frame} {b : Binding} (hfr : env[env.size - 1]? = some fr)
    (hb : fr.binds.back? = some b) :
    ∃ fr', (Env.setAtE env (.bind (env.size - 1) (fr.binds.size - 1)) .bot)[
        (Env.setAtE env (.bind (env.size - 1) (fr.binds.size - 1)) .bot).size - 1]? = some fr' ∧
      fr'.binds.back? = some { b with val := .bot } := by
  refine ⟨{ fr with binds := fr.binds.modify (fr.binds.size - 1) ({ · with val := .bot }) }, ?_, ?_⟩
  · simp only [Env.setAtE, Array.size_modify, Array.getElem?_modify, if_true, hfr, Option.map_some]
  · rw [Array.back?_eq_getElem?] at hb ⊢
    simp only [Array.size_modify, Array.getElem?_modify, if_true, hb, Option.map_some]

/-- The checker's position of the variable `0` is the top binding. -/
theorem ckVarPos_top {env : Env} {fr : Frame} {b : Binding} (hfr : env[env.size - 1]? = some fr)
    (hb : fr.binds.back? = some b) :
    ckVarPos env 0 = some (.bind (env.size - 1) (fr.binds.size - 1)) ∧
      env[env.size - 1]?.bind (fun fr' : Frame => fr'.binds[fr.binds.size - 1]?) = some b := by
  rw [Array.back?_eq_getElem?] at hb
  have hpos : 0 < fr.binds.size := by
    rcases Nat.eq_zero_or_pos fr.binds.size with h0 | h0
    · rw [Array.getElem?_eq_none (by omega)] at hb; cases hb
    · exact h0
  have hget : env[env.size - 1]! = fr := by
    rw [Array.getElem!_eq_getD, Array.getD_eq_getD_getElem?, hfr]; rfl
  refine ⟨?_, by rw [hfr]; exact hb⟩
  simp only [ckVarPos, hget, if_pos hpos, Nat.sub_zero]

/-! ## The program's entry predicates -/

/-- The entry states of `bodyC`, `S(Z)` and `Z`: the empty frame's readings, a frame present. -/
def Top (st : MState) : Prop := DecideScope.topReadings st = [] ∧ 0 < st.env.size

/-- The top binding holds a number stored at `Nat`. -/
def TopNum (st : MState) : Prop :=
  ∃ fr b, st.env[st.env.size - 1]? = some fr ∧ fr.binds.back? = some b ∧ b.val.Num ∧ b.ty = some .tNat

/-- The entry state of the read of `x`: `x` bound at `S(Z)`'s reading, holding a number. -/
def AtX (st : MState) : Prop := DecideScope.topReadings st = [duC] ∧ TopNum st

theorem Top.kern {a b : MState} (h : Kern a b) (ha : Top a) : Top b :=
  ⟨by rw [← topReadings_kern h]; exact ha.1, by rw [← size_of_erase h.env]; exact ha.2⟩

theorem TopNum.of_erase {a b : MState} (h : Env.erase a.env = Env.erase b.env) (ha : TopNum a) : TopNum b := by
  obtain ⟨fr, bd, hfr, hb, hn, ht⟩ := ha
  obtain ⟨fr', hfr', hbs⟩ := top_of_erase h hfr
  exact ⟨fr', bd, hfr', by rw [hbs]; exact hb, hn, ht⟩

theorem AtX.kern {a b : MState} (h : Kern a b) (ha : AtX a) : AtX b :=
  ⟨by rw [← topReadings_kern h]; exact ha.1, ha.2.of_erase h.env⟩

theorem TopNum.numVar {st : MState} (h : TopNum st) : NumVar 0 st := by
  obtain ⟨fr, b, hfr, hb, hn, ht⟩ := h
  obtain ⟨h1, h2⟩ := ckVarPos_top hfr hb
  exact ⟨_, _, b, h1, h2, hn, ht⟩

/-! ## The checker's runs of the program's sub-terms (from the machine facts) -/

section
variable {D : Decisions}

/-- `eval` of `Z`: the value `Z` at `Nat`, the kernel kept. -/
theorem run_zero (hE : EvalInv) (hZ : ZeroInv) {g : Nat} {typed : Bool} {hint : Option Value} {st st' : MState}
    {bh : Nat} {v : Value} {T? : Option Value} (hm : Mode st) (hD : DecTab D st')
    (hfl : D.flags (DecideScope.topReadings st) .zero = (false, false))
    (hany : D.declOf (DecideScope.topReadings st) .zero ≠ .any ∧ (D.declOf (DecideScope.topReadings st) .zero).isProof = false) (htd : st.tailDecl = none)
    (h : Runs (Ochr.eval (g + 3) typed .zero hint) st bh (v, T?) st') :
    v = .zero ∧ T? = some .tNat ∧ Kern st st' := by
  obtain ⟨st₀, st₁, bh', hk₀, -, -, -, -, -, h₀, hk₁, -⟩ :=
    hE (g + 1) typed .zero hint st st' bh v T? D hm hD (fun _ e => by cases e) (fun _ _ _ e => by cases e) hany.1 hany.2 (.inl htd) h
  obtain ⟨rfl, rfl, hk, -⟩ := hZ g typed hint st₀ st₁ bh' v T? h₀
  exact ⟨rfl, rfl, hk₀.trans (hk.trans hk₁)⟩

/-- `eval` of `S(Z)`: the value `S(Z)` at `Nat`, Ω kept (up to its temporaries' stored types). -/
theorem run_SZ (hE : EvalInv) (hZ : ZeroInv) (hS : SuccInv) {g : Nat} {typed : Bool} {hint : Option Value}
    {st st' : MState} {bh : Nat} {v : Value} {T? : Option Value} (hm : Mode st) (hD : DecTab D st')
    (hflS : D.flags (DecideScope.topReadings st) (.succ .zero) = (false, false))
    (hflZ : D.flags (DecideScope.topReadings st) .zero = (false, false))
    (hanyS : D.declOf (DecideScope.topReadings st) (.succ .zero) ≠ .any ∧ (D.declOf (DecideScope.topReadings st) (.succ .zero)).isProof = false)
    (hanyZ : D.declOf (DecideScope.topReadings st) .zero ≠ .any ∧ (D.declOf (DecideScope.topReadings st) .zero).isProof = false) (htd : st.tailDecl = none)
    (h : Runs (Ochr.eval (g + 6) typed (.succ .zero) hint) st bh (v, T?) st') :
    v = .succ .zero ∧ T? = some .tNat ∧ Env.erase st.env = Env.erase st'.env := by
  obtain ⟨st₀, st₁, bh', hk₀, hm₀, -, htn₀, htd₀, -, h₀, hk₁, -⟩ :=
    hE (g + 4) typed _ hint st st' bh v T? D hm hD (fun _ e => by cases e) (fun _ _ _ e => by cases e) hanyS.1 hanyS.2 (.inl htd) h
  obtain ⟨a, b, v₀, T₀, bh₁, hka, hma, -, htda, hrun, rfl, rfl, hq, hDb, -⟩ :=
    hS (g + 3) typed .zero hint st₀ st₁ bh' v T? .zero hm₀ htn₀ htd₀ h₀
  have hfa : D.flags (DecideScope.topReadings a) .zero = (false, false) := by
    rw [← topReadings_kern (hk₀.trans hka)]; exact hflZ
  have hza : D.declOf (DecideScope.topReadings a) .zero ≠ .any ∧ (D.declOf (DecideScope.topReadings a) .zero).isProof = false := by
    rw [← topReadings_kern (hk₀.trans hka)]; exact hanyZ
  obtain ⟨rfl, -, hkab⟩ := run_zero hE hZ hma (hDb D (DecTab.of_kern hk₁.symm hD)) hfa hza htda hrun
  exact ⟨rfl, rfl, hk₀.env.trans (hka.env.trans (hkab.env.trans (hq.env.trans hk₁.env)))⟩

/-- `eval` of `x` where the top binding holds a number at `Nat`: its value, at `Nat` in a typed run;
after it, the top binding is that number (a copy) or `⊥` (a move). -/
theorem run_x (hE : EvalInv) (hV : VarNumInv) {g : Nat} {typed : Bool} {hint : Option Value} {st st' : MState}
    {bh : Nat} {v : Value} {T? : Option Value} (hm : Mode st) (hD : DecTab D st') {fr : Frame} {b : Binding}
    (hfr : st.env[st.env.size - 1]? = some fr) (hb : fr.binds.back? = some b) (hn : b.val.Num)
    (ht : b.ty = some .tNat) (hfl : D.flags (DecideScope.topReadings st) (.place (.var 0)) = (false, false))
    (hany : D.declOf (DecideScope.topReadings st) (.place (.var 0)) ≠ .any ∧ (D.declOf (DecideScope.topReadings st) (.place (.var 0))).isProof = false)
    (htd : st.tailDecl = none ∨ st.tailDecl = some (D.declOf (DecideScope.topReadings st) (.place (.var 0))))
    (h : Runs (Ochr.eval (g + 6) typed (.place (.var 0)) hint) st bh (v, T?) st') :
    v = b.val ∧ (typed = true → T? = some .tNat) ∧
      ∃ fr' b', st'.env[st'.env.size - 1]? = some fr' ∧ fr'.binds.back? = some b' ∧ (b'.val = .bot ∨ b'.val.Num) := by
  obtain ⟨st₀, st₁, bh', hk₀, hm₀, -, -, -, -, h₀, hk₁, -⟩ :=
    hE (g + 4) typed _ hint st st' bh v T? D hm hD (fun _ e => by cases e) (fun _ _ _ e => by cases e) hany.1 hany.2 htd h
  obtain ⟨fr₀, hfr₀, hbs₀⟩ := top_of_erase hk₀.env hfr
  have hb₀ : fr₀.binds.back? = some b := by rw [hbs₀]; exact hb
  obtain ⟨hpos, hlk⟩ := ckVarPos_top hfr₀ hb₀
  obtain ⟨hv, hT, hTs, -, c, hq, hcopy, hmove⟩ :=
    hV (g + 3) typed 0 hint st₀ st₁ bh' v T? _ _ b D hm₀ hpos hlk hn (by rw [ht]; rfl) (DecTab.of_kern hk₁.symm hD) h₀
  refine ⟨hv, fun hty => ?_, ?_⟩
  · obtain ⟨T, hT'⟩ := Option.isSome_iff_exists.mp (hTs hty)
    rw [hT', Option.some.inj ((hT T hT').symm.trans ht)]
  obtain ⟨frc, hfrc, hbsc⟩ := top_of_erase hq.env hfr₀
  have hbc : frc.binds.back? = some b := by rw [hbsc]; exact hb₀
  have hsc : c.env.size = st₀.env.size := (size_of_erase hq.env).symm
  cases hc : D.copy (D.placeDecl (DecideScope.topReadings st₀) (.var 0))
  · -- a move: `⊥` at the binding
    have hk := hmove hc
    obtain ⟨frm, hfrm, hbm⟩ := top_setAt_bot hfrc hbc
    rw [hsc, hbsc] at hfrm
    obtain ⟨fr', hfr', hbs'⟩ := top_of_erase (hk.env.trans hk₁.env) hfrm
    exact ⟨fr', _, hfr', by rw [hbs']; exact hbm, .inl rfl⟩
  · -- a copy: the kernel kept
    obtain ⟨fr', hfr', hbs'⟩ := top_of_erase (hq.env.trans ((hcopy hc).env.trans hk₁.env)) hfr₀
    exact ⟨fr', b, hfr', by rw [hbs']; exact hb₀, .inr hn⟩

end

/-! ## The program's step -/

section
variable {K : RunCtx} {ρ : Assignment} {φ : Future}

/-- `x`'s entry state after `S(Z)` is bound: the value `S(Z)`, pushed at the empty frame's reading
of `S(Z)`. -/
theorem atX_push (hE : EvalInv) (hZ : ZeroInv) (hS : SuccInv) (hd : DecTab K.D stC) {g : Nat} (x : Hint)
    {st st₀ st₁ : MState} {bh : Nat} {v₀ : Value} {p : Bool} (hT : Top st) (hk : Kern st st₀) (hm₀ : Mode st₀)
    (htd₀ : st₀.tailDecl = none) (hD₁ : DecTab K.D st₁) (h : Runs (Ochr.eval (g + 6) true (.succ .zero) none) st₀ bh (v₀, some .tNat) st₁) :
    v₀ = .succ .zero ∧
      AtX { st₁ with env := Env.pushBindE st₁.env x (some .tNat) v₀ p (K.D.declOf (DecideScope.topReadings st₁) (.succ .zero)) } := by
  have hT₀ := hT.kern hk
  obtain ⟨rfl, -, he⟩ :=
    run_SZ hE hZ hS hm₀ hD₁ (by rw [hT₀.1]; exact flags_SZ hd) (by rw [hT₀.1]; exact flags_Z hd)
      (by rw [hT₀.1, declOf_SZ hd]; exact Aux.duC_ok) (by rw [hT₀.1]; exact declOf_Z_ok hd) htd₀ h
  have hr₁ : DecideScope.topReadings st₁ = [] := by rw [← topReadings_of_erase he]; exact hT₀.1
  have hs₁ : 0 < st₁.env.size := by rw [← size_of_erase he]; exact hT₀.2
  obtain ⟨fr, hfr⟩ : ∃ fr, st₁.env[st₁.env.size - 1]? = some fr := ⟨_, Array.getElem?_eq_getElem (by omega)⟩
  refine ⟨rfl, ?_, ?_⟩
  · rw [topReadings_pushBindE hfr, hr₁, declOf_SZ hd]
  · exact ⟨_, _, top_pushBindE hfr x (some .tNat) _ p _, Array.back?_push .., .succ .zero, rfl⟩

/-- **The step for the body of `C`** (`let x = S(Z); x`, typed, at any fuel from `9`): composed from
the column's steps, every side condition of each discharged for this program from the machine facts
and the table aligned at `stC`. -/
theorem sim_bodyC (hE : EvalInv) (hZ : ZeroInv) (hS : SuccInv) (hV : VarNumInv) (hL : LetInv)
    (hDN : DropNoopInv) (hIC : InvCore) (hc : Strict.FundCtx K) (hd : DecTab K.D stC) (g : Nat) :
    EvalSim K ρ φ (g + 9) bodyC Top (· = true) := by
  have hz : EvalSim K ρ φ (g + 3) .zero Top :=
    eval_of_core hE (fun a b h ha => ha.kern h) (fun _ e => by cases e) (fun _ _ _ e => by cases e)
      (fun st hst => by rw [hst.1]; exact declOf_Z_ok hd) (zero_coreSim hZ hIC)
  have hsz : EvalSim K ρ φ (g + 6) (.succ .zero) Top :=
    eval_of_core hE (fun a b h ha => ha.kern h) (fun _ e => by cases e) (fun _ _ _ e => by cases e)
      (fun st hst => by rw [hst.1, declOf_SZ hd]; exact Aux.duC_ok)
      (succ_core hS hIC .zero hz (fun a b h ha => ha.kern h) (fun st hst => by rw [hst.1]; exact flags_Z hd)
        (fun s => by rw [runT_zero, runT_zero])
        (fun typed st₀ st₁ bh v₀ T₀ hT₀ hm₀ htd₀ hD₁ h => by
          obtain ⟨rfl, -, -⟩ := run_zero hE hZ hm₀ hD₁ (by rw [hT₀.1]; exact flags_Z hd)
            (by rw [hT₀.1]; exact declOf_Z_ok hd) htd₀ h
          exact .zero))
  have hx : ∀ (Δ' : Nat → TyS) (ρ' : Assignment),
      EvalSim { K with Δ := Δ' } ρ' φ (g + 6) (.place (.var 0)) AtX (· = true) := fun Δ' ρ' =>
    eval_of_core hE (fun a b h ha => ha.kern h) (fun _ e => by cases e) (fun _ _ _ e => by cases e)
      (fun st hst => by rw [hst.1, declOf_x hd]; exact Aux.duC_ok)
      (CoreSim.mono (var_core (K := { K with Δ := Δ' }) (ρ := ρ') (φ := φ) hV hIC (n := g + 3) (i := 0))
        (fun _ h => h.2.numVar) (fun _ _ => trivial))
  have hlet : CoreSim K ρ φ (g + 7) bodyC Top (· = true) := by
    unfold bodyC
    refine let_core hL hDN hIC hc (.succ .zero) (.var 0)
      (fun st stB hst hB => by rw [hst.1, hB.1]; exact declOf_body_x hd) hsz (fun a b h ha => ha.kern h) hx
      (fun st hst => by rw [hst.1]; exact flags_SZ hd) (fun st hst => by rw [hst.1]; exact flags_x hd)
      (fun st₀ st₁ bh v₀ T₀ hT₀ hm₀ htd₀ hD₁ h => by
        obtain ⟨rfl, hT, -⟩ :=
          run_SZ hE hZ hS hm₀ hD₁ (by rw [hT₀.1]; exact flags_SZ hd) (by rw [hT₀.1]; exact flags_Z hd)
            (by rw [hT₀.1, declOf_SZ hd]; exact Aux.duC_ok) (by rw [hT₀.1]; exact declOf_Z_ok hd) htd₀ h
        exact ⟨.succ .zero, Option.some.inj hT⟩)
      (fun st st₀ st₁ bh v₀ p hst hk hm₀ htd₀ hD₁ h => (atX_push hE hZ hS hd _ hst hk hm₀ htd₀ hD₁ h).2)
      (fun a b h ha => ha.kern h) (fun _ _ => trivial) (fun m σ hσ => by simp [Term.anyAtom] at hσ) rfl
      (fun _ _ _ _ _ => rfl) (fun _ _ _ => rfl)
      (fun stB st₂ bh r T? hB hmB htdB hD₂ h => by
        obtain ⟨fr, b, hfr, hb, hn, ht⟩ := hB.2
        exact (run_x hE hV hmB hD₂ hfr hb hn ht (by rw [hB.1]; exact flags_x hd)
          (by rw [hB.1, declOf_x hd]; exact Aux.duC_ok) htdB h).2.2)
  exact eval_of_core hE (fun a b h ha => ha.kern h) (fun _ e => by cases e) (fun _ _ _ e => by cases e)
    (fun st hst => by rw [hst.1, declOf_bodyC hd]; exact Aux.duC_ok) hlet

end

/-! ## The assembly -/

/-- **Alignment at a larger table is alignment at a smaller one** (`MachineMono.DecTab.back`'s
statement, open in the machine lane), assumed. -/
def DecBack : Prop := ∀ (D : Decisions) (st st' : MState), DecTab D st' → TablesGrow st st' → DecTab D st

section
variable {K : RunCtx}

/-- **The checker's run of the body of `C`**: its value is `S(Z)`, at `Nat`. -/
theorem run_body (hE : EvalInv) (hZ : ZeroInv) (hS : SuccInv) (hV : VarNumInv) (hL : LetInv) (hDN : DropNoopInv)
    (hd : DecTab K.D stC) {g : Nat} {hint : Option Value} {st st' : MState} {bh : Nat} {v : Value}
    {T? : Option Value} (hT : Top st) (hm : Mode st)
    (htd : st.tailDecl = none ∨ st.tailDecl = some (K.D.declOf (DecideScope.topReadings st) bodyC)) (hD : DecTab K.D st')
    (h : Runs (Ochr.eval (g + 9) true bodyC hint) st bh (v, T?) st') : v = .succ .zero ∧ T? = some .tNat := by
  obtain ⟨st₀, st₁, bh', hk₀, hm₀, -, htn₀, htd₀, hcd₀, h₀, hk₁, -⟩ :=
    hE (g + 7) true bodyC hint st st' bh v T? K.D hm hD (fun _ e => by cases e) (fun _ _ _ e => by cases e)
      (by rw [hT.1, declOf_bodyC hd]; exact Aux.duC_ok.1) (by rw [hT.1, declOf_bodyC hd]; exact Aux.duC_ok.2) htd h
  obtain ⟨du, a₀, a₁, stB, a₂, a₃, v₀, r, T₀, p, b₁, b₂, b₃, hka, hma, -, htda, htdB, hru, hne₁, hdu, hrd₁, hkB, hmB,
    -, hrw, hrd, hk₃, hD₁, hD₂, -⟩ := hL (g + 6) ⟨"x"⟩ (.succ .zero) (.place (.var 0)) hint st₀ st₁ bh' v T? K.D K.Γ
      (.succ .zero) hm₀ htn₀ htd₀ (DecTab.of_kern hk₁.symm hD) h₀
  have hT₀ := hT.kern (hk₀.trans hka)
  obtain ⟨rfl, hT₀', -⟩ :=
    run_SZ hE hZ hS hma hD₁ (by rw [hT₀.1]; exact flags_SZ hd) (by rw [hT₀.1]; exact flags_Z hd)
      (by rw [hT₀.1, declOf_SZ hd]; exact Aux.duC_ok) (by rw [hT₀.1]; exact declOf_Z_ok hd) htda hru
  cases Option.some.inj hT₀'
  have hX := (atX_push hE hZ hS hd ⟨"x"⟩ (p := p) hT (hk₀.trans hka) hma htda hD₁ hru).2
  rw [hrd₁, hdu] at hX
  -- the binding `x` holds `S(Z)` at `Nat` where the read starts
  obtain ⟨fr₁, hfr₁⟩ : ∃ fr, a₁.env[a₁.env.size - 1]? = some fr := ⟨_, Array.getElem?_eq_getElem (by omega)⟩
  obtain ⟨frB, hfrB, hbsB⟩ := top_of_erase hkB.env (top_pushBindE hfr₁ ⟨"x"⟩ (some .tNat) (.succ .zero) p du)
  have hbB : frB.binds.back? = some { hint := ⟨"x"⟩, ty := some .tNat, val := .succ .zero, proof := p, decl := du } := by
    rw [hbsB]; exact Array.back?_push ..
  obtain ⟨rfl, hTr, fr₂, bx, hfr₂, hbx, hbxv⟩ := run_x hE hV hmB hD₂ hfrB hbB (.succ .zero) rfl
    (by rw [(hX.kern hkB).1]; exact flags_x hd) (by rw [(hX.kern hkB).1, declOf_x hd]; exact Aux.duC_ok)
    (by
      rcases htdB with e | e
      · exact .inl e
      · exact .inr (by rw [e, hcd₀, (hT.kern hk₀).1, (hX.kern hkB).1]; exact congrArg some (declOf_body_x hd))) hrw
  refine ⟨?_, hTr rfl⟩
  -- the drop pops the binding and leaves the read's value
  have hnl : bx.val.loans = [] := by
    rcases hbxv with e | e
    · rw [e]; simp [Value.loans]
    · exact e.loans
  have hnb : ∀ l, bx.val.holdsBorrow l = false := fun l => by
    rcases hbxv with e | e
    · rw [e]; rfl
    · exact e.holdsBorrow l
  have hnbor : ∀ l w, bx.val ≠ .borrow l w := fun l w => by
    rcases hbxv with e | e
    · rw [e]; intro e'; cases e'
    · exact e.not_borrow l w
  have hfrW : (a₂.withTempT (Value.succ .zero) T?).env[(a₂.withTempT (Value.succ .zero) T?).env.size - 1]? =
      some { fr₂ with temps := fr₂.temps.push (.succ .zero), tempTys := fr₂.tempTys.push T? } := by
    simp only [MState.withTempT, Array.size_modify, Array.getElem?_modify, if_true, hfr₂]; rfl
  have hne₂ : 0 < a₂.env.size := by
    rcases Nat.eq_zero_or_pos a₂.env.size with h0 | h0
    · rw [Array.getElem?_eq_none (by omega)] at hfr₂; cases hfr₂
    · exact h0
  exact popped_eq hne₂ (hDN (g + 6) _ a₃ b₃ _ bx hfrW hbx hnl hnbor hnb hrd) hk₃

end

/-- **The column applied to `def C : Nat := let x = S(Z); x`.** At every data model, assignment and
future, and every table of decisions aligned with the checker at the end of the run: for every run
of the checker on the body from a state with `stC`'s kernel, in mode (where `checkDef` evaluates a
constant's body), the strict run of the body from the reference state (`stC` read as one) succeeds,
and its value is `1`, a member of `Nat`, at the type `Nat`. Assumed: facts about the checker alone
(the module docstring). -/
theorem column_C (hE : EvalInv) (hZ : ZeroInv) (hS : SuccInv) (hV : VarNumInv) (hL : LetInv) (hDN : DropNoopInv)
    (hIC : InvCore) (hback : DecBack) {g : Nat} (hgrow : GrowsM (Ochr.eval (g + 9) true bodyC (some .tNat)))
    (dm : DataModel) (D : Decisions) (ρ : Assignment) (φ : Future) {st st' : MState} {bh : Nat} {v : Value}
    {T? : Option Value} (hk : Kern stC st) (hm : Mode st) (htd : st.tailDecl = none) (hD : DecTab D st')
    (h : Runs (Ochr.eval (g + 9) true bodyC (some .tNat)) st bh (v, T?) st') :
    ∃ r s', runT (KC dm D) ρ φ st.tailNext (hintM (KC dm D) ρ (some .tNat)) bodyC (SM' (KC dm D) ρ stC) = some (r, s') ∧
      r.1 = .el0 Nat 1 ∧ r.1 ∈ₛ[dm.read] TyM.nat ∧ r.2.m = TyM.nat := by
  have hd : DecTab D stC := DecTab.of_kern hk.symm (hback D st st' hD (hgrow st bh _ st' h))
  have hT : Top st := Top.kern hk ⟨topReadings_stC, by decide⟩
  obtain ⟨rfl, rfl⟩ := run_body (K := KC dm D) hE hZ hS hV hL hDN hd hT hm (.inl htd) hD h
  have hsc : scopeOf (SM' (KC dm D) ρ stC) = [] := by rw [scopeOf_sstate']; exact topReadings_stC
  obtain ⟨ρ', Δ', π', r, s', -, hx, hmean, hagree, -, -, -⟩ :=
    sim_bodyC (K := KC dm D) (ρ := ρ) (φ := φ) hE hZ hS hV hL hDN hIC (fundCtx_KC dm D) hd g st st' true (some .tNat)
      _ _ (SM' (KC dm D) ρ stC) id hT rfl hm (.inl htd) ((pre_stC dm D ρ).of_kern hk) ((rel_stC dm D ρ φ).of_kern hk)
      (sgood_stC dm D ρ φ) (valsOk_bodyC ρ φ _) (absBelow_bodyC _) hasHolePrim_bodyC
      (by rw [hsc]; exact flags_bodyC hd) (fun e => by cases e) hD bh h
  have h1 : r.1 = .el0 Nat 1 := by
    have hz : ∀ (K : RunCtx) ρ ψ hint, meanV K ρ ψ hint Value.zero = .el0 Nat 0 := fun _ _ _ _ => rfl
    rw [← hmean]; show (meanV _ _ _ (.plain TyM.nat) Value.zero).succ = _; rw [hz, Sem.succ, Sem.asNat_el0]
  refine ⟨r, s', hx, h1, by rw [h1]; exact ⟨1, rfl⟩, ?_⟩
  rw [← hagree _ rfl]; rfl

/-! ## The checker's side, run (not kernel-evaluable: `#guard`)

The checker accepts `C`; at its body's evaluation its state has `stC`'s kernel and is in mode, with
the goal `Nat`; and its run of the body from `stC` succeeds (the run `column_C` takes). -/

open Ochr.Meaning.Regress.GenNeutralContent (isOk outSt outVal)

/-- `C` as the checker reads it. -/
def defC : Def := { name := "C", hs := [], doms := [], cod := .nat, body := bodyC }

def acceptedC : Bool :=
  match checkDefs {} [.defn defC] with
  | [(_, .accepted, _)] => true
  | _ => false

#guard acceptedC

/-- `checkDef`'s constant branch up to the body's evaluation (`seedHoles`, the frame reset, the goal). -/
def atBodyC : M Value := do
  seedHoles
  modify fun s => { s with env := #[{}], goal := none, recStack := [], refs := [] }
  evalType 1000 defC.cod

#guard outVal atBodyC {} 100000 == .tNat

#guard
  let s := outSt atBodyC {} 100000
  s.env.size == 1 && s.env[0]!.binds.size == 0 && s.env[0]!.temps.size == 0 && s.globals.isEmpty &&
    s.inds.isEmpty && s.nextLoan == 0 && s.nextAbs == 0 && s.absTy.size == 0 && s.absDecl.size == 0 &&
    s.refs.isEmpty && s.etaRefs.isEmpty && s.goal.isNone && s.neutrals.isEmpty && !s.liveScope &&
    !s.headEval && !s.copying && !s.inPlace && s.erasedDepth == 0

#guard isOk (Ochr.eval 100 true bodyC (some .tNat)) stC 1000

-- `checkDef`'s state at the body also has no handed-down reading (`column_C`'s `htd`)
#guard (outSt atBodyC {} 100000).tailDecl.isNone

/-! ### Sanity runs of the assumed facts (the checker's own runs, compiled, not kernel-checked)

Each assumed `Prop` of `FormMachine.lean` is exercised on a concrete run at entry conditions it
must survive: a tail position (`tailNext`), a handed-down reading (`tailDecl`), a copy and a move.
They check the conclusions' shape on these runs, not the `Prop`s. -/

/-- One frame, `x ↦ S(Z) : Nat` read `other` (a move). -/
def stX (w : Value) : MState :=
  { env := #[{ binds := #[{ hint := ⟨"x"⟩, ty := some .tNat, val := w, decl := .other }] }] }

def xVal (s : MState) : Value := (s.env[0]!.binds[0]!).val

-- `VarNumInv`: the value is the binding's, at its stored type; a move leaves `⊥`; also in tail position
#guard outVal (Ochr.evalCore 100 true (.place (.var 0)) none) (stX (.succ .zero)) 1000 == (.succ .zero, some .tNat)
#guard xVal (outSt (Ochr.evalCore 100 true (.place (.var 0)) none) (stX (.succ .zero)) 1000) == .bot
#guard outVal (Ochr.evalCore 100 true (.place (.var 0)) none) { stX (.succ .zero) with tailNext := true } 1000 ==
  (.succ .zero, some .tNat)
-- `ZeroInv`, `SuccInv`: `S(Z)` at `Nat`, Ω kept
#guard outVal (Ochr.evalCore 100 true (.succ .zero) none) stC 1000 == (.succ .zero, some .tNat)
#guard (outSt (Ochr.evalCore 100 true (.succ .zero) none) stC 1000).env.size == 1
-- `LetInv`, `DropNoopInv`: the body's value at `Nat`, the binding dropped; also with a handed-down reading
#guard outVal (Ochr.evalCore 100 true bodyC none) stC 1000 == (.succ .zero, some .tNat)
#guard (outSt (Ochr.evalCore 100 true bodyC none) stC 1000).env[0]!.binds.size == 0
#guard isOk (Ochr.eval 100 true bodyC (some .tNat)) { stC with tailDecl := some .other } 1000
-- `AssignNumInv`: `x.0 := Z` over `S(S(Z))` leaves `S(Z)`; the value `()` at `Unit`
#guard outVal (Ochr.evalCore 100 true (.assign (.proj 0 (.var 0)) .zero) none) (stX (.succ (.succ .zero))) 1000 ==
  (.unit, some .tUnit)
#guard xVal (outSt (Ochr.evalCore 100 true (.assign (.proj 0 (.var 0)) .zero) none) (stX (.succ (.succ .zero))) 1000)
  == .succ .zero

end Ochr.Meaning.Steps.Form.ColumnC
