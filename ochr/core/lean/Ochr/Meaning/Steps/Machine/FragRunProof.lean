import Ochr.Meaning.Steps.Machine.FragRunLemmas
import Ochr.Meaning.Steps.FragTop

/-!
# `FragRun` with the counter (machine lane, machine6; IN PROGRESS)

`FragRun` is false as stated (machine6, 2026-11-21: `FSt` says nothing about the label counter, and
`&x` lends at the counter; counterexample in `HANDOFF.md`). `FragRunF` is it with the counter above
every label at the entry (`Fresh`), and that carried to the end with the value in flight. Proved by
induction on `FTy`; each case at `evalCore` (`CoreOut`), lifted to `eval` by `frag_lift_run`.
-/

namespace Ochr.Meaning.Steps.Machine

open Ochr Ochr.Meaning Ochr.Meaning.Steps Ochr.Meaning.DecideScope
open Ochr.Meaning.Steps.Form

/-- What a fragment term's typed run leaves: `FragRun`'s conclusion, with the counter. -/
def RunOut (Γ : List Form.FT) (A : Form.FT) (st st' : MState) (v : Value) (T? : Option Value) : Prop :=
  T? = some A.ty ∧ A.val v ∧ ModeEq st st' ∧ topReadings st' = topReadings st ∧ st'.env.size = st.env.size ∧
    FStT Γ (st'.withTempT v T?) ∧ Fresh (st'.withTempT v T?)

/-- **`FragRun` with the counter** (the restatement proposed to the lead). -/
def FragRunF (D : Decisions) : Prop :=
  ∀ Γ u A n hint st st' bh v T?, FTy Γ u A → FSt Γ st → Fresh st → Mode st →
    (st.tailDecl = none ∨ st.tailDecl = some (D.declOf (topReadings st) u)) → DecTab D st' →
    Runs (Ochr.eval n true u hint) st bh (v, T?) st' → RunOut Γ A st st' v T?

/-- What the run of `evalCore` leaves, a case of the induction. -/
def CoreOut (Γ : List Form.FT) (A : Form.FT) (st₀ st₁ : MState) (v : Value) (T? : Option Value) : Prop :=
  T? = some A.ty ∧ A.val v ∧ Mode st₁ ∧ topReadings st₁ = topReadings st₀ ∧ st₁.env.size = st₀.env.size ∧
    FStT Γ (st₁.withTempT v T?) ∧ Fresh (st₁.withTempT v T?)

/-- A case's hypotheses: `evalCore` entered as `eval` enters it. -/
def CoreCase (D : Decisions) (Γ : List Form.FT) (t : Term) (A : Form.FT) : Prop :=
  ∀ m st₀ st₁ hint bh v T?, FSt Γ st₀ → Fresh st₀ → Mode st₀ → st₀.tailNext = false → st₀.tailDecl = none →
    st₀.curDecl = some (D.declOf (topReadings st₀) t) → DecTab D st₁ →
    Runs (Ochr.evalCore (m + 1) true t hint) st₀ bh (v, T?) st₁ → CoreOut Γ A st₀ st₁ v T?

theorem _root_.Ochr.Meaning.Steps.Form.FTy.notVal {Γ : List Form.FT} {t : Term} {A : Form.FT} (h : FTy Γ t A) : ∀ w, t ≠ .val w := by
  intro w e; subst e; cases h

theorem _root_.Ochr.Meaning.Steps.Form.FTy.notCall {Γ : List Form.FT} {t : Term} {A : Form.FT} (h : FTy Γ t A) : ∀ f as hd, t ≠ .call f as hd := by
  intro f as hd e; subst e; cases h

theorem Fresh.kern {a b : MState} (hk : Kern a b) (h : Fresh a) : Fresh b :=
  h.of_erase hk.env (Nat.le_of_eq hk.nextLoan)

theorem modeEq_of_modes {a b : MState} (ha : Mode a) (hb : Mode b) : ModeEq a b :=
  ⟨ha.headEval.trans hb.headEval.symm, ha.copying.trans hb.copying.symm, ha.inPlace.trans hb.inPlace.symm,
    ha.erased.trans hb.erased.symm⟩

/-- **A case at `evalCore` gives the step at `eval`** (`EvalInv`; below fuel `3` no run succeeds). -/
theorem frag_lift_run {D : Decisions} (hdec : FragDec D) {Γ : List Form.FT} {t : Term} {A : Form.FT}
    (hty : FTy Γ t A) (hc : CoreCase D Γ t A) :
    ∀ n hint st st' bh v T?, FSt Γ st → Fresh st → Mode st →
      (st.tailDecl = none ∨ st.tailDecl = some (D.declOf (topReadings st) t)) → DecTab D st' →
      Runs (Ochr.eval n true t hint) st bh (v, T?) st' → RunOut Γ A st st' v T? := by
  intro n hint st st' bh v T? hP hfr hm htd hD h
  by_cases hn : n < 3
  · exact absurd h (evalLow n true t hint st st' bh _ hn hty.notVal)
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 + 2 := ⟨n - 3, by omega⟩
  have hrd := (hdec Γ t A st hty hP).2
  obtain ⟨st₀, st₁, bh', hk, hm₀, -, htn, htd₀, hcd, hrun, hk₁, hmode⟩ :=
    (evalInvR : EvalInv) (m + 1) true t hint st st' bh v T? D hm hD hty.notVal hty.notCall
      (by rw [hrd]; cases A <;> exact fun e => by cases e) (by rw [hrd]; cases A <;> rfl) htd h
  have hD₁ : DecTab D st₁ := DecTab.back hD
    (TablesGrow.of_fields hk₁.globals.symm hk₁.inds.symm hk₁.absDecl.symm hk₁.nextAbs.symm hk₁.nextLoan.symm)
  obtain ⟨hT, hv, hm₁, htr, hsz, hF, hf⟩ :=
    hc m st₀ st₁ hint bh' v T? (hP.kern hk) (hfr.kern hk) hm₀ htn htd₀ hcd hD₁ hrun
  refine ⟨hT, hv, modeEq_of_modes hm (hmode hm₁), ?_, ?_, hF.of_erase (hk₁.withTempT v T?).env,
    hf.kern (hk₁.withTempT v T?)⟩
  · rw [← ColumnC.topReadings_kern hk₁, htr, ← ColumnC.topReadings_kern hk]
  · rw [size_of_kern hk₁, hsz, size_of_kern hk]

/-! ## The cases -/

theorem core_zero (D : Decisions) (Γ : List Form.FT) : CoreCase D Γ .zero .nat := by
  intro m st₀ st₁ hint bh v T? hP hfr hm htn htd hcd hD h
  obtain ⟨rfl, rfl, hk, hmode⟩ := zeroInv m true hint st₀ st₁ bh v T? h
  have hP₁ := hP.kern hk
  refine ⟨rfl, .zero, hmode hm, (ColumnC.topReadings_kern hk).symm, size_of_kern hk, hP₁.pushNum (.inl .zero) _,
    (hfr.kern hk).pushNum (.inl .zero) _ hP₁.frame⟩

/-! ## Helpers for the read, `&x` and the writes -/

theorem topReadings_setAt (s : MState) (p : Pos) (w : Value) :
    topReadings { s with env := Env.setAtE s.env p w } = topReadings s := by
  unfold topReadings
  show (((Env.setAtE s.env p w).back?.map (fun fr : Frame => fr.binds.toList.map (·.decl))).getD []).reverse = _
  rw [back_setAtE_any]

theorem temps_setAt_bind (E : Env) (f j f' i : Nat) (w : Value) :
    valAt (Env.setAtE E (.bind f j) w) (.temp f' i) = valAt E (.temp f' i) :=
  valAt_setAtE_other _ _ _ _ (by intro e; cases e)

/-- A number variable's number or `⊥` overwritten by a number or `⊥`. -/
theorem _root_.Ochr.Meaning.Steps.Form.FSt.setInert {Γ : List Form.FT} {s : MState} (h : FSt Γ s) {f j : Nat}
    {w : Value} (hp : Pos.bind f j ∈ allPos s.env) (hold : (valAt s.env (.bind f j)).Num ∨ valAt s.env (.bind f j) = .bot)
    (hw : w.Num ∨ w = .bot)
    (hholds : ∀ i A, Γ[i]? = some A → ckVarPos s.env i = some (.bind f j) → A.holds w) :
    FSt Γ { s with env := Env.setAtE s.env (.bind f j) w } := by
  have hnl : ∀ (v : Value) l, (v.Num ∨ v = .bot) → v ≠ .loan l := fun v l hv e => by
    rcases hv with hv | hv <;> rw [e] at hv <;> cases hv
  have hnb : ∀ (v : Value) l c, (v.Num ∨ v = .bot) → v ≠ .borrow l c := fun v l c hv e => by
    rcases hv with hv | hv <;> rw [e] at hv <;> cases hv
  refine (h.toT.setAt hp (by rcases hw with hw | hw; exact .num hw; rw [hw]; exact .bot)
    (fun l => ⟨fun e => absurd e (hnl w l hw), fun e => absurd e (hnl _ l hold)⟩)
    (fun l => ⟨fun ⟨c, e⟩ => absurd e (hnb w l c hw), fun ⟨c, e⟩ => absurd e (hnb _ l c hold)⟩) hholds).toFSt ?_
  intro f' i hq
  show (valAt (Env.setAtE s.env (.bind f j) w) _).Num ∨ _
  rw [temps_setAt_bind]
  exact h.temps f' i (by have := hq; rwa [show allPos (Env.setAtE s.env (.bind f j) w) = allPos s.env from allPos_setAtE _ _ _] at this)

/-- The end of one borrow held at a binding, from a fragment state. -/
theorem _root_.Ochr.Meaning.Steps.Form.FSt.ofEnd {Γ : List Form.FT} {s : MState} (h : FSt Γ s)
    {fx jx fy jy l : Nat} {c : Value} (hF : EndAt s.env (.bind fx jx) (.bind fy jy) l c) :
    FSt Γ { s with env := endE s.env (.bind fx jx) (.bind fy jy) c } := by
  refine (h.toT.ofEnd hF).toFSt ?_
  intro f' i hq
  change (valAt (endE s.env (.bind fx jx) (.bind fy jy) c) (.temp f' i)).Num ∨
    valAt (endE s.env (.bind fx jx) (.bind fy jy) c) (.temp f' i) = .unit
  rw [hF.valAt_endE, if_neg (by intro e; cases e), if_neg (by intro e; cases e)]
  exact h.temps f' i (by have := hq; rwa [show allPos (endE s.env _ _ c) = allPos s.env from FEnd.allPos_endE] at this)

theorem holds_num {A : Form.FT} {w : Value} (hA : A = .nat) (hw : w.Num) : A.holds w := by subst hA; exact .inl hw

/-- The variables at a number variable's position are number variables. -/
theorem FSt.nat_at {Γ : List Form.FT} {s : MState} (h : FSt Γ s) {i k f j : Nat} (hi : Γ[i]? = some .nat)
    (hck : ckVarPos s.env i = some (.bind f j)) {A : Form.FT} (hk : Γ[k]? = some A)
    (hck' : ckVarPos s.env k = some (.bind f j)) : A = .nat := by
  have : k = i := by
    unfold ckVarPos at hck hck'
    split at hck
    · split at hck'
      · have e1 := (Pos.bind.inj (Option.some.inj hck)).2
        have e2 := (Pos.bind.inj (Option.some.inj hck')).2
        omega
      · cases hck'
    · cases hck
  subst this; rw [hi] at hk; exact (Option.some.inj hk).symm

end Ochr.Meaning.Steps.Machine
