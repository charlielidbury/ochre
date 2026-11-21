import Ochr.Meaning.Steps.Machine.FragRunLemmas
import Ochr.Meaning.Steps.FragTop

/-!
# `FragRun` with the counter (machine lane, machine6 and machine7; PROVED)

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
  T? = some A.ty ∧ A.val v ∧ Form.ModeEq st st' ∧ topReadings st' = topReadings st ∧ st'.env.size = st.env.size ∧
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

theorem modeEq_of_modes {a b : MState} (ha : Mode a) (hb : Mode b) : Form.ModeEq a b :=
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

/-! ## The read of a number variable -/

theorem quiet_size {a b : MState} (hq : Quiet a b) : b.env.size = a.env.size := by
  have := congrArg Array.size hq.env; simp only [Env.erase_size] at this; exact this.symm

theorem lookup_of_erase {a b : MState} (he : a.env.erase = b.env.erase) {f j : Nat} {bx : Binding}
    (hb : a.env[f]?.bind (fun fr : Frame => fr.binds[j]?) = some bx) :
    b.env[f]?.bind (fun fr : Frame => fr.binds[j]?) = some bx := by
  rw [← lookup_erase, ← he, lookup_erase]; exact hb

theorem noLabel_bot : ∀ l, (Value.bot = .loan l ∨ ∃ c, Value.bot = .borrow l c) → l < 0 := by
  intro l e; rcases e with e | ⟨c, e⟩ <;> cases e

/-- What the read's end leaves, from the state its access left (`X`) and the kernel after it. -/
theorem core_out_num {Γ : List Form.FT} {st₀ X st₁ : MState} {v : Value} {T? : Option Value}
    (hX : FSt Γ X) (hfX : Fresh X) (hk : Kern X st₁) (hv : v.Num) (hT : T? = some .tNat) (hm₁ : Mode st₁)
    (htr : topReadings X = topReadings st₀) (hsz : X.env.size = st₀.env.size) :
    CoreOut Γ .nat st₀ st₁ v T? :=
  have hP₁ := hX.kern hk
  ⟨hT, hv, hm₁, by rw [← ColumnC.topReadings_kern hk, htr], by rw [size_of_kern hk, hsz],
    hP₁.pushNum (.inl hv) _, (hfX.kern hk).pushNum (.inl hv) _ hP₁.frame⟩

theorem core_var (D : Decisions) (Γ : List Form.FT) (i : Nat) (hi : Γ[i]? = some .nat) :
    CoreCase D Γ (.place (.var i)) .nat := by
  intro m st₀ st₁ hint bh v T? hP hfr hm htn htd hcd hD h
  rcases hP.var_cases hi with ⟨f, j, b, hck, hb, hn, hty⟩ | ⟨f, j, b, f', j', l, c, hck, hb, hty, -, hF, -⟩ |
    ⟨f, j, b, hck, hb, hbot, hty⟩
  · obtain ⟨rfl, hT, hTs, hm₁, stq, hq, -, hcp, hmv⟩ :=
      varNumInv m true i hint st₀ st₁ bh v T? f j b D hm hck hb hn (by rw [hty]; rfl) hD h
    have hT' : T? = some .tNat := by
      obtain ⟨T, e⟩ := Option.isSome_iff_exists.mp (hTs rfl)
      have := hT T e; rw [hty] at this; rw [e, this]
    have hPq : FSt Γ stq := hP.of_erase hq.env
    have hfq : Fresh stq := hfr.of_erase hq.env hq.nextLoan
    have htq : topReadings stq = topReadings st₀ := (ColumnC.topReadings_of_erase hq.env).symm
    cases hc : D.copy (D.placeDecl (topReadings st₀) (.var i))
    · have hk := hmv hc
      have hbq := lookup_of_erase hq.env hb
      have hp := (lookup_pos hbq).1
      exact core_out_num (hPq.setInert hp (.inl (by rw [(lookup_pos hbq).2]; exact hn)) (.inr rfl)
          (fun _ _ _ _ => holds_bot _))
        (hfq.setAt hp (fun l e => absurd (noLabel_bot l e) (Nat.not_lt_zero l))) hk hn hT' hm₁
        (by rw [topReadings_setAt, htq]) (by show (Env.setAtE stq.env (.bind f j) .bot).size = _; rw [size_setAtE, quiet_size hq])
    · exact core_out_num hPq hfq (hcp hc) hn hT' hm₁ htq (quiet_size hq)
  · obtain ⟨hvc, hT, hTs, hm₁, stq, hq, -, hcp, hmv⟩ :=
      varLentInv m true i hint st₀ st₁ bh v T? f j b f' j' l c D hm hck hb hty hF hD h
    have hT' : T? = some .tNat := by
      obtain ⟨T, e⟩ := Option.isSome_iff_exists.mp (hTs rfl)
      rw [e, hT T e]
    have hvn : v.Num := hvc ▸ hF.c
    have hPq : FSt Γ stq := hP.of_erase hq.env
    have hfq : Fresh stq := hfr.of_erase hq.env hq.nextLoan
    have hFq := (hF.of_erase hq.env).endAt
    have hPe := hPq.ofEnd hFq
    have hfe := hfq.ofEnd hFq
    have hte : topReadings { stq with env := endE stq.env (.bind f j) (.bind f' j') c } = topReadings st₀ := by
      rw [topReadings_endE, ← ColumnC.topReadings_of_erase hq.env]
    have hse : (endE stq.env (.bind f j) (.bind f' j') c).size = st₀.env.size := by rw [size_endE, quiet_size hq]
    cases hc : D.copy (D.placeDecl (topReadings st₀) (.var i))
    · have hp : Pos.bind f j ∈ allPos (endE stq.env (.bind f j) (.bind f' j') c) := by
        rw [FEnd.allPos_endE]; exact hFq.hpx
      exact core_out_num (hPe.setInert hp (.inl (by rw [hFq.valAt_endE, if_pos rfl]; exact hFq.c)) (.inr rfl)
          (fun _ _ _ _ => holds_bot _))
        (hfe.setAt hp (fun l e => absurd (noLabel_bot l e) (Nat.not_lt_zero l))) (hmv hc) hvn hT' hm₁
        (by rw [topReadings_setAt, hte])
        (by show (Env.setAtE (endE stq.env (.bind f j) (.bind f' j') c) (.bind f j) .bot).size = _; rw [size_setAtE, hse])
    · exact core_out_num hPe hfe (hcp hc) hvn hT' hm₁ hte hse
  · exact absurd h (varBotInv m true i hint st₀ st₁ bh v T? f j b hck hb hbot hty)

/-! ## `&x` -/

theorem topReadings_lent (s : MState) (E : Env) (p : Pos) (w : Value) (k : Nat) :
    topReadings { s with env := Env.setAtE E p w, nextLoan := k } = topReadings { s with env := E } := by
  unfold topReadings
  show (((Env.setAtE E p w).back?.map (fun fr : Frame => fr.binds.toList.map (·.decl))).getD []).reverse = _
  rw [back_setAtE_any]

theorem core_bor (D : Decisions) (Γ : List Form.FT) (i : Nat) (hi : Γ[i]? = some .nat) :
    CoreCase D Γ (.borrow (.var i)) .ref := by
  intro m st₀ st₁ hint bh v T? hP hfr hm htn htd hcd hD h
  obtain ⟨f, j, b, hck, hb, hty, hrd, hv⟩ := hP.top i .nat hi
  have hty' : b.ty = some .tNat := hty
  have hrd' : b.decl = .other := hrd
  rcases hv with hn | hbot | ⟨l, hl⟩
  · obtain ⟨hm₁, stq, hq, -, rfl, rfl, hk⟩ := borrowNumInv m i hint st₀ st₁ bh v T? f j b D hm hck hb hn hty' hD h
    have hPq : FSt Γ stq := hP.of_erase hq.env
    have hfq : Fresh stq := hfr.of_erase hq.env hq.nextLoan
    obtain ⟨hF, hf⟩ := hPq.lend hfq (lookup_of_erase hq.env hb) hn ⟨hty', hrd'⟩ (some (.tRef .tNat))
    have hkw := hk.withTempT (.borrow stq.nextLoan b.val) (some (.tRef .tNat))
    refine ⟨rfl, ⟨_, _, rfl, hn⟩, hm₁, ?_, ?_, hF.of_erase hkw.env, hf.kern hkw⟩
    · rw [← ColumnC.topReadings_kern hk]
      exact (topReadings_setAt stq _ _).trans (ColumnC.topReadings_of_erase hq.env).symm
    · rw [size_of_kern hk]; show (Env.setAtE stq.env (.bind f j) _).size = _; rw [size_setAtE, quiet_size hq]
  · exact absurd h (borrowBotInv m i hint st₀ st₁ bh v T? f j b hck hb hbot hty')
  · obtain ⟨hp, hval⟩ := lookup_pos hb
    obtain ⟨f', j', c, hF⟩ := hP.fend hp (by rw [hval, hl])
    obtain ⟨hm₁, stq, hq, -, rfl, rfl, hk⟩ :=
      borrowLentInv m i hint st₀ st₁ bh v T? f j b f' j' l c D hm hck hb hty' hF hD h
    have hPq : FSt Γ stq := hP.of_erase hq.env
    have hfq : Fresh stq := hfr.of_erase hq.env hq.nextLoan
    have hFq := (hF.of_erase hq.env).endAt
    obtain ⟨b', hb', hv', hty₂, hrd₂⟩ := lookup_endE_px (ph := .bind f' j') (c := c) (lookup_of_erase hq.env hb)
    obtain ⟨hFT, hf⟩ := (hPq.ofEnd hFq).lend (hfq.ofEnd hFq) hb' (hv' ▸ hFq.c) ⟨hty₂.trans hty', hrd₂.trans hrd'⟩
      (some (.tRef .tNat))
    rw [hv'] at hFT hf
    have hkw := hk.withTempT (.borrow stq.nextLoan c) (some (.tRef .tNat))
    refine ⟨rfl, ⟨_, _, rfl, hFq.c⟩, hm₁, ?_, ?_, hFT.of_erase hkw.env, hf.kern hkw⟩
    · rw [← ColumnC.topReadings_kern hk, topReadings_lent, topReadings_endE]
      exact (ColumnC.topReadings_of_erase hq.env).symm
    · rw [size_of_kern hk]
      exact (size_setAtE _ _ _ _).trans ((size_endE _ _ _ _).trans (quiet_size hq))

/-! ## `S(u)` -/

/-- The induction's hypothesis at a sub-term: `frag_lift_run`'s conclusion. -/
def EvalCase (D : Decisions) (Γ : List Form.FT) (t : Term) (A : Form.FT) : Prop :=
  ∀ n hint st st' bh v T?, FSt Γ st → Fresh st → Mode st →
    (st.tailDecl = none ∨ st.tailDecl = some (D.declOf (topReadings st) t)) → DecTab D st' →
    Runs (Ochr.eval n true t hint) st bh (v, T?) st' → RunOut Γ A st st' v T?

theorem core_succ {D : Decisions} {Γ : List Form.FT} {u : Term} (ihu : EvalCase D Γ u .nat) :
    CoreCase D Γ (.succ u) .nat := by
  intro m st₀ st₁ hint bh v T? hP hfr hm htn htd hcd hD h
  obtain ⟨sa, sb, v₀, T₀, bh₁, hk₀, hma, -, htda, hru, rfl, rfl, hq, hme, hDb, -⟩ :=
    Form.succInv m true u hint st₀ st₁ bh v T? hm htn htd h
  obtain ⟨-, hv₀, hme₁, htr, hsz, hF, hf⟩ :=
    ihu m none sa sb bh₁ v₀ T₀ (hP.kern hk₀) (hfr.kern hk₀) hma (.inl htda) (hDb D hD) hru
  have hne : 0 < sb.env.size := by rw [hsz, size_of_kern hk₀]; exact hP.frame
  have hP₁ := (hF.untemp (.inl hv₀)).of_erase hq.env
  refine ⟨rfl, .succ hv₀, (hma.of_modeEq hme₁).of_modeEq hme, ?_, ?_, hP₁.pushNum (.inl (.succ hv₀)) _,
    ((hf.untemp hne).of_erase hq.env hq.nextLoan).pushNum (.inl (.succ hv₀)) _ hP₁.frame⟩
  · rw [← ColumnC.topReadings_of_erase hq.env, htr, ← ColumnC.topReadings_kern hk₀]
  · rw [quiet_size hq, hsz, size_of_kern hk₀]

/-! ## `x := u` -/

/-- What a case's end leaves, from the state its last write left (`X`) and the kernel after it. -/
theorem core_out_of {Γ : List Form.FT} {A : Form.FT} {st₀ X st₁ : MState} {v : Value} {T? : Option Value}
    (hX : FSt Γ X) (hfX : Fresh X) (hk : Kern X st₁) (hA : A.val v) (hin : v.Num ∨ v = .unit) (hT : T? = some A.ty)
    (hm₁ : Mode st₁) (htr : topReadings X = topReadings st₀) (hsz : X.env.size = st₀.env.size) :
    CoreOut Γ A st₀ st₁ v T? :=
  have hP₁ := hX.kern hk
  ⟨hT, hA, hm₁, by rw [← ColumnC.topReadings_kern hk, htr], by rw [size_of_kern hk, hsz],
    hP₁.pushNum hin _, (hfX.kern hk).pushNum hin _ hP₁.frame⟩

theorem _root_.Ochr.Meaning.Steps.Form.FSt.holds_nat {Γ : List Form.FT} {s : MState} (h : FSt Γ s) {i f j : Nat}
    (hi : Γ[i]? = some .nat) (hck : ckVarPos s.env i = some (.bind f j)) {w : Value} (hw : w.Num ∨ w = .bot) :
    ∀ k A, Γ[k]? = some A → ckVarPos s.env k = some (.bind f j) → A.holds w := by
  intro k A hk hck'
  rw [FSt.nat_at h hi hck hk hck']
  rcases hw with hw | hw
  · exact .inl hw
  · rw [hw]; exact holds_bot _

theorem core_asg {D : Decisions} {Γ : List Form.FT} {i : Nat} {u : Term} (hi : Γ[i]? = some .nat)
    (ihu : EvalCase D Γ u .nat) : CoreCase D Γ (.assign (.var i) u) .unit := by
  intro m st₀ st₁ hint bh v T? hP hfr hm htn htd hcd hD h
  obtain ⟨sa, sb, hu, v₀, T₀, bh₁, hk₀, hma, -, htda, hru, hDb, rfl, rfl, hpost⟩ :=
    assignVarInv m i u hint st₀ st₁ bh v T? D hm htn htd (fun f j b hpos hb => (hP.natVar hi hpos b hb).1) hD h
  obtain ⟨-, hv₀, hme₁, htr, hsz, hF, hf⟩ :=
    ihu m hu sa sb bh₁ v₀ T₀ (hP.kern hk₀) (hfr.kern hk₀) hma (.inl htda) hDb hru
  have hne : 0 < sb.env.size := by rw [hsz, size_of_kern hk₀]; exact hP.frame
  have hPb := hF.untemp (.inl hv₀)
  have hmb : Mode sb := hma.of_modeEq hme₁
  obtain ⟨f, j, b, hck, hb, -, -, hhold⟩ := hPb.top i .nat hi
  obtain ⟨sc, hq, -, hmode, hnum, hend⟩ := hpost f j b hck hb hv₀
  have hPq : FSt Γ sc := hPb.of_erase hq.env
  have hfq : Fresh sc := (hf.untemp hne).of_erase hq.env hq.nextLoan
  have htq : topReadings sc = topReadings st₀ := by
    rw [← ColumnC.topReadings_of_erase hq.env, htr, ← ColumnC.topReadings_kern hk₀]
  have hszq : sc.env.size = st₀.env.size := by rw [quiet_size hq, hsz, size_of_kern hk₀]
  have hckq : ckVarPos sc.env i = some (.bind f j) := by
    rw [← ckVarPos_erase, ← hq.env, ckVarPos_erase]; exact hck
  have hbq := lookup_of_erase hq.env hb
  have hp := (lookup_pos hbq).1
  have hnolab : ∀ l, (v₀ = .loan l ∨ ∃ c, v₀ = .borrow l c) → l < sc.nextLoan := fun l e => by
    rcases e with e | ⟨c, e⟩ <;> rw [e] at hv₀ <;> cases hv₀
  have hinert : ∀ w, (w.Num ∨ w = .bot) → b.val = w → CoreOut Γ .unit st₀ st₁ .unit (some .tUnit) := by
    intro w hw e
    have hk := hnum (by rw [e]; exact hw)
    exact core_out_of (hPq.setInert hp (by rw [(lookup_pos hbq).2, e]; exact hw) (.inl hv₀) (hPq.holds_nat hi hckq (.inl hv₀)))
      (hfq.setAt hp hnolab) hk rfl (.inr rfl) rfl (hmb.of_modeEq (hmode (by rw [e]; rcases hw with hw | hw; exact .inl hw; exact .inr (.inl hw))))
      (by rw [topReadings_setAt, htq]) (by show (Env.setAtE sc.env (.bind f j) v₀).size = _; rw [size_setAtE, hszq])
  rcases hhold with hn | hbot | ⟨l, hl⟩
  · exact hinert _ (.inl hn) rfl
  · exact hinert _ (.inr rfl) hbot
  · obtain ⟨hpb, hvalb⟩ := lookup_pos hb
    obtain ⟨f', j', c, hFE⟩ := hPb.fend hpb (by rw [hvalb, hl])
    have hFq := (hFE.of_erase hq.env).endAt
    have hPe := hPq.ofEnd hFq
    have hpe : Pos.bind f j ∈ allPos (endE sc.env (.bind f j) (.bind f' j') c) := by
      rw [FEnd.allPos_endE]; exact hFq.hpx
    exact core_out_of (hPe.setInert hpe (.inl (by rw [hFq.valAt_endE, if_pos rfl]; exact hFq.c)) (.inl hv₀)
        (hPe.holds_nat hi ((ckVarPos_endE _ _ _ _ _).trans hckq) (.inl hv₀)))
      ((hfq.ofEnd hFq).setAt hpe hnolab) (hend f' j' l c hFE) rfl (.inr rfl) rfl
      (hmb.of_modeEq (hmode (.inr (.inr ⟨f', j', l, c, hFE⟩))))
      (by rw [topReadings_setAt, topReadings_endE, htq])
      (by show (Env.setAtE (endE sc.env (.bind f j) (.bind f' j') c) (.bind f j) v₀).size = _
          rw [size_setAtE, size_endE, hszq])

/-! ## `*y := u` -/

/-- The variables at a variable's position have its type. -/
theorem FSt.ty_at {Γ : List Form.FT} {s : MState} {i k f j : Nat} {A B : Form.FT} (hi : Γ[i]? = some B)
    (hck : ckVarPos s.env i = some (.bind f j)) (hk : Γ[k]? = some A)
    (hck' : ckVarPos s.env k = some (.bind f j)) : A = B := by
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

/-- A write at a binding that keeps its labels, from a fragment state: a fragment state. -/
theorem _root_.Ochr.Meaning.Steps.Form.FSt.setKeep {Γ : List Form.FT} {s : MState} (h : FSt Γ s) {f j : Nat}
    {w : Value} (hp : Pos.bind f j ∈ allPos s.env) (hw : FVal w)
    (hl : ∀ l, w = .loan l ↔ valAt s.env (.bind f j) = .loan l)
    (hb : ∀ l, (∃ c, w = .borrow l c) ↔ (∃ c, valAt s.env (.bind f j) = .borrow l c))
    (hholds : ∀ i A, Γ[i]? = some A → ckVarPos s.env i = some (.bind f j) → A.holds w) :
    FSt Γ { s with env := Env.setAtE s.env (.bind f j) w } := by
  refine (h.toT.setAt hp hw hl hb hholds).toFSt ?_
  intro f' i hq
  show (valAt (Env.setAtE s.env (.bind f j) w) _).Num ∨ _
  rw [temps_setAt_bind]
  exact h.temps f' i (by have := hq; rwa [show allPos (Env.setAtE s.env (.bind f j) w) = allPos s.env from allPos_setAtE _ _ _] at this)

theorem core_asgD {D : Decisions} {Γ : List Form.FT} {i : Nat} {u : Term} (hi : Γ[i]? = some .ref)
    (ihu : EvalCase D Γ u .nat) : CoreCase D Γ (.assign (.deref (.var i)) u) .unit := by
  intro m st₀ st₁ hint bh v T? hP hfr hm htn htd hcd hD h
  obtain ⟨sa, sb, hu, v₀, T₀, bh₁, hk₀, hma, -, htda, hru, hDb, rfl, rfl, hnbot, hpost⟩ :=
    assignDerefInvF m i u hint st₀ st₁ bh v T? D hm htn htd (fun f j b hpos hb => (hP.refVar hi hpos b hb).1) hD h
  obtain ⟨-, hv₀, hme₁, htr, hsz, hF, hf⟩ :=
    ihu m hu sa sb bh₁ v₀ T₀ (hP.kern hk₀) (hfr.kern hk₀) hma (.inl htda) hDb hru
  have hne : 0 < sb.env.size := by rw [hsz, size_of_kern hk₀]; exact hP.frame
  have hPb := hF.untemp (.inl hv₀)
  obtain ⟨f, j, b, hck, hb, -, -, hhold⟩ := hPb.top i .ref hi
  rcases hhold with hbot | ⟨l, w, hbl, hw⟩
  · exact absurd hbot (hnbot f j b hck hb)
  obtain ⟨sc, hq, -, hme, hck₂, hb₂, hk⟩ := hpost f j b l w hck hb hbl hw
  have hPq : FSt Γ sc := hPb.of_erase hq.env
  have hfq : Fresh sc := (hf.untemp hne).of_erase hq.env hq.nextLoan
  have hp := (lookup_pos hb₂).1
  have hval : valAt sc.env (.bind f j) = .borrow l w := by rw [(lookup_pos hb₂).2, hbl]
  have hlt : l < sc.nextLoan := hfq _ hp l (.inr ⟨w, hval⟩)
  refine core_out_of (hPq.setKeep hp (.bor l hv₀) (fun l' => ?_) (fun l' => ?_) (fun k A hk hck' => ?_))
    (hfq.setAt hp (fun l' e => ?_)) hk rfl (.inr rfl) rfl ((hma.of_modeEq hme₁).of_modeEq hme)
    (by rw [topReadings_setAt, ← ColumnC.topReadings_of_erase hq.env, htr, ← ColumnC.topReadings_kern hk₀])
    (by show (Env.setAtE sc.env (.bind f j) _).size = _; rw [size_setAtE, quiet_size hq, hsz, size_of_kern hk₀])
  · rw [hval]; exact ⟨fun e => (by cases e), fun e => (by cases e)⟩
  · rw [hval]; exact ⟨fun ⟨_, e⟩ => ⟨w, by cases e; rfl⟩, fun ⟨_, e⟩ => ⟨v₀, by cases e; rfl⟩⟩
  · rw [FSt.ty_at hi hck₂ hk hck']; exact .inr ⟨l, v₀, rfl, hv₀⟩
  · rcases e with e | ⟨c, e⟩
    · cases e
    · cases e; exact hlt

/-! ## `let` -/

/-- Binding the value in flight keeps the counter above every label. -/
theorem Fresh.pushBind {s : MState} {v : Value} {T : Option Value} (h : Fresh (s.withTempT v T))
    (hne : 0 < s.env.size) (x : Hint) (ty : Option Value) (p : Bool) (d : DeclInfo) :
    Fresh { s with env := Env.pushBindE s.env x ty v p d } := by
  obtain ⟨fr, hfr⟩ : ∃ fr, s.env[s.env.size - 1]? = some fr :=
    ⟨_, Array.getElem?_eq_getElem (by omega : s.env.size - 1 < s.env.size)⟩
  obtain ⟨hA, hnew, -⟩ := push_view hfr v T
  have hs : Fresh s := h.untemp hne
  obtain ⟨A, B, h1, h2⟩ := allPos_pushBindE s.env x ty v p d fr hfr hne
  intro q hq l e
  have e' : valAt (Env.pushBindE s.env x ty v p d) q = .loan l ∨
      ∃ w, valAt (Env.pushBindE s.env x ty v p d) q = .borrow l w := e
  have hq' : q ∈ A ++ Pos.bind (s.env.size - 1) fr.binds.size :: B := h2 ▸ hq
  by_cases ep : q = .bind (s.env.size - 1) fr.binds.size
  · subst ep
    rw [valAt_pushBindE_new s.env x ty v p d fr hfr] at e'
    exact h (.temp (s.env.size - 1) fr.temps.size) (by rw [hA]; simp) l (by rw [hnew]; exact e')
  · have hqE : q ∈ allPos s.env := by
      rw [h1, List.mem_append]; rw [List.mem_append, List.mem_cons] at hq'
      rcases hq' with hq' | hq' | hq'
      · exact .inl hq'
      · exact absurd hq' ep
      · exact .inr hq'
    rw [valAt_pushBindE_ne s.env x ty v p d fr hfr q ep] at e'
    exact hs q hqE l e'

theorem modeEq_form {a b : MState} (h : ModeEq a b) : Form.ModeEq a b :=
  ⟨h.headEval, h.copying, h.inPlace, h.erased⟩

theorem core_let {D : Decisions} (hdec : FragDec D) {Γ : List Form.FT} {x : Hint} {u w : Term} {A B : Form.FT}
    (hu : FTy Γ u A) (hw : FTy (A :: Γ) w B) (ihu : EvalCase D Γ u A) (ihw : EvalCase D (A :: Γ) w B) :
    CoreCase D Γ (.letIn x u w) B := by
  intro m st₀ st₁ hint bh v T? hP hfr hm htn htd hcd hD h
  obtain ⟨du, sa, sb, sB, s₂, s₃, v₀, r, T₀, p, bh₁, bh₂, bh₃, hk₀, hma, -, htda, htdB, hru, hdu, hkB, hmeB, -,
    hrw, hrd, hk₃, hme₃, hD₁, hD₂⟩ := Form.letInv m x u w hint st₀ st₁ bh v T? D hm htn htd hD h
  obtain ⟨rfl, hv₀, hme₁, htr₁, hsz₁, hF₁, hf₁⟩ :=
    ihu m none sa sb bh₁ v₀ T₀ (hP.kern hk₀) (hfr.kern hk₀) hma (.inl htda) hD₁ hru
  have hduA : du = A.rd := hdu.symm.trans (hdec Γ u A st₀ hu hP).2
  subst hduA
  have hneb : 0 < sb.env.size := by rw [hsz₁, size_of_kern hk₀]; exact hP.frame
  have hszp : (Env.pushBindE sb.env x (some A.ty) v₀ p A.rd).size = sb.env.size := by simp [Env.pushBindE]
  obtain ⟨frb, hfrb⟩ : ∃ fr, sb.env[sb.env.size - 1]? = some fr :=
    ⟨_, Array.getElem?_eq_getElem (by omega : sb.env.size - 1 < sb.env.size)⟩
  have hPB : FSt (A :: Γ) sB := (fst_push hF₁ hv₀ x p).kern hkB
  have hfB : Fresh sB := (hf₁.pushBind hneb x (some A.ty) p A.rd).kern hkB
  have hmB : Mode sB := (hma.of_modeEq hme₁).of_modeEq hmeB
  have htdB' : sB.tailDecl = none ∨ sB.tailDecl = some (D.declOf (topReadings sB) w) :=
    .inr (by rw [htdB, hcd, (hdec Γ _ B st₀ (.letIn Γ x u w A B hu hw) hP).2, (hdec (A :: Γ) w B sB hw hPB).2])
  obtain ⟨hT, hr, hme₂, htr₂, hsz₂, hF₂, hf₂⟩ := ihw m none sB s₂ bh₂ r T? hPB hfB hmB htdB' hD₂ hrw
  obtain ⟨hF₃, hf₃, hme₃', htt₃, htr₃, hsz₃⟩ := frag_drop hF₂ hf₂ hrd
  have hne₂ : 0 < s₂.env.size := by
    rw [hsz₂, size_of_kern hkB]; exact Nat.lt_of_lt_of_eq hneb hszp.symm
  have hvr : v = r := popped_of_topTemps hne₂ htt₃ hk₃
  subst hvr
  have hm₂ : Mode s₂ := hmB.of_modeEq hme₂
  have hm₂' : Mode (s₂.withTempT v T?) := ⟨hm₂.headEval, hm₂.copying, hm₂.inPlace, hm₂.erased⟩
  have hm₃ : Mode s₃ := hm₂'.of_modeEq (modeEq_form hme₃')
  refine ⟨hT, hr, hm₃.of_modeEq hme₃, ?_, ?_, hF₃.of_erase hk₃.env, hf₃.kern hk₃⟩
  · rw [← topReadings_withTempT st₁ v T?, ← ColumnC.topReadings_kern hk₃, htr₃, topReadings_withTempT, htr₂,
      ← ColumnC.topReadings_kern hkB, topReadings_pushBindE sb.env x (some A.ty) v₀ p A.rd _ hfrb sb rfl, List.tail_cons, htr₁,
      ← ColumnC.topReadings_kern hk₀]
  · rw [← size_withTempT st₁ v T?, size_of_kern hk₃, hsz₃, size_withTempT, hsz₂, size_of_kern hkB]
    exact hszp.trans (hsz₁.trans (size_of_kern hk₀))

/-! ## `u; w` -/

/-- What the sequence leaves, from the tail's run at `stW`. -/
theorem core_seq_tail {D : Decisions} (hdec : FragDec D) {Γ : List Form.FT} {u w : Term} {A B : Form.FT}
    (hu : FTy Γ u A) (hw : FTy Γ w B) (ihw : EvalCase D Γ w B) {m : Nat} {st₀ stW st₁ : MState} {bh : Nat}
    {v : Value} {T? : Option Value} (hP : FSt Γ st₀) (hcd : st₀.curDecl = some (D.declOf (topReadings st₀) (.seq u w)))
    (hPW : FSt Γ stW) (hfW : Fresh stW) (hmW : Mode stW) (htdW : stW.tailDecl = none ∨ stW.tailDecl = st₀.curDecl)
    (htrW : topReadings stW = topReadings st₀) (hszW : stW.env.size = st₀.env.size) (hD : DecTab D st₁)
    (hrw : Runs (Ochr.eval m true w none) stW bh (v, T?) st₁) : CoreOut Γ B st₀ st₁ v T? := by
  have htdW' : stW.tailDecl = none ∨ stW.tailDecl = some (D.declOf (topReadings stW) w) := by
    rcases htdW with e | e
    · exact .inl e
    · exact .inr (by rw [e, hcd, (hdec Γ _ B st₀ (.seq Γ u w A B hu hw) hP).2, (hdec Γ w B stW hw hPW).2])
  obtain ⟨hT, hr, hme₂, htr₂, hsz₂, hF₂, hf₂⟩ := ihw m none stW st₁ bh v T? hPW hfW hmW htdW' hD hrw
  exact ⟨hT, hr, hmW.of_modeEq hme₂, htr₂.trans htrW, hsz₂.trans hszW, hF₂, hf₂⟩

theorem core_seq_inert {D : Decisions} (hdec : FragDec D) {Γ : List Form.FT} {u w : Term} {A B : Form.FT}
    (hA : A ≠ .ref) (hu : FTy Γ u A) (hw : FTy Γ w B) (ihu : EvalCase D Γ u A) (ihw : EvalCase D Γ w B) :
    CoreCase D Γ (.seq u w) B := by
  intro m st₀ st₁ hint bh v T? hP hfr hm htn htd hcd hD h
  obtain ⟨sa, sb, sW, v₀, T₀, bh₁, bh₂, hk₀, hma, -, htda, htdW, hru, hD₁, hdrop, -, hrw⟩ :=
    seqInv m u w hint st₀ st₁ bh v T? D hm htn htd hD h
  obtain ⟨-, hv₀, hme₁, htr₁, hsz₁, hF₁, hf₁⟩ :=
    ihu m none sa sb bh₁ v₀ T₀ (hP.kern hk₀) (hfr.kern hk₀) hma (.inl htda) hD₁ hru
  have hin : v₀.Num ∨ v₀ = .unit := by
    cases A with
    | nat => exact .inl hv₀
    | unit => exact .inr hv₀
    | ref => exact absurd rfl hA
  have hinert : v₀.Inert := by
    rcases hin with h | h
    · exact h.inert
    · rw [h]; exact Value.inert_unit
  have hloans : v₀.loans = [] := by
    rcases hin with h | h
    · exact h.loans
    · rw [h]; simp [Value.loans]
  obtain ⟨hkW, hmeW⟩ := hdrop hinert.holdsBorrow hloans
  have hne : 0 < sb.env.size := by rw [hsz₁, size_of_kern hk₀]; exact hP.frame
  exact core_seq_tail hdec hu hw ihw hP hcd ((hF₁.untemp hin).kern hkW) ((hf₁.untemp hne).kern hkW)
    ((hma.of_modeEq hme₁).of_modeEq hmeW) htdW
    (by rw [← ColumnC.topReadings_kern hkW, htr₁, ← ColumnC.topReadings_kern hk₀])
    (by rw [size_of_kern hkW, hsz₁, size_of_kern hk₀]) hD hrw

theorem core_seq_bor {D : Decisions} (hdec : FragDec D) {Γ : List Form.FT} {u w : Term} {B : Form.FT}
    (hu : FTy Γ u .ref) (hw : FTy Γ w B) (ihu : EvalCase D Γ u .ref) (ihw : EvalCase D Γ w B) :
    CoreCase D Γ (.seq u w) B := by
  intro m st₀ st₁ hint bh v T? hP hfr hm htn htd hcd hD h
  obtain ⟨sa, sb, sW, v₀, T₀, bh₁, bh₂, hk₀, hma, -, htda, htdW, hru, hD₁, hdrop, -, hrw⟩ :=
    seqBorInv m u w hint st₀ st₁ bh v T? D hm htn htd hD h
  obtain ⟨rfl, ⟨l, c, rfl, hcN⟩, hme₁, htr₁, hsz₁, hF₁, hf₁⟩ :=
    ihu m none sa sb bh₁ v₀ T₀ (hP.kern hk₀) (hfr.kern hk₀) hma (.inl htda) hD₁ hru
  have hne : 0 < sb.env.size := by rw [hsz₁, size_of_kern hk₀]; exact hP.frame
  obtain ⟨fr, hfr⟩ : ∃ fr, sb.env[sb.env.size - 1]? = some fr :=
    ⟨_, Array.getElem?_eq_getElem (by omega : sb.env.size - 1 < sb.env.size)⟩
  obtain ⟨hWpos, hWnew, hWold, hntq, -⟩ := push_view hfr (.borrow l c) (some FT.ref.ty)
  have hWmem : ∀ q, q ∈ allPos sb.env → q ∈ allPos (sb.withTempT (.borrow l c) (some FT.ref.ty)).env :=
    fun q hq => by rw [hWpos]; exact List.mem_append_left _ hq
  have hNmem : Pos.temp (sb.env.size - 1) fr.temps.size ∈ allPos (sb.withTempT (.borrow l c) (some FT.ref.ty)).env := by
    rw [hWpos]; exact List.mem_append_right _ (List.mem_singleton_self _)
  have hWcases : ∀ q, q ∈ allPos (sb.withTempT (.borrow l c) (some FT.ref.ty)).env →
      q = .temp (sb.env.size - 1) fr.temps.size ∨ q ∈ allPos sb.env := by
    intro q hq; rw [hWpos, List.mem_append, List.mem_singleton] at hq; exact hq.symm
  obtain ⟨px, hpxW, hxW⟩ := hF₁.lender _ l c hNmem hWnew
  have hpx : px ∈ allPos sb.env := (hWcases px hpxW).resolve_left (fun e => by rw [e, hWnew] at hxW; cases hxW)
  have hx : valAt sb.env px = .loan l := by rw [← hWold _ hpx]; exact hxW
  obtain ⟨fx, jx, rfl⟩ : ∃ fx jx, px = .bind fx jx := by
    cases px with
    | bind fx jx => exact ⟨fx, jx, rfl⟩
    | temp f' i' =>
      rcases hF₁.temps f' i' hpxW with h' | h' | ⟨m', w', h'⟩ <;> rw [hxW] at h' <;> cases h'
  have hnoB : ∀ q ∈ allPos sb.env, ∀ w', valAt sb.env q ≠ .borrow l w' := fun q hq w' e => hntq (by
    have e' := hF₁.bor1 q _ l w' c (hWmem _ hq) hNmem (by rw [hWold _ hq]; exact e) hWnew
    rw [← e']; exact hq)
  obtain ⟨sc, hq, -, hkW, hmeW⟩ := hdrop l c (.bind fx jx) rfl hcN
    (fun q hq => by rw [← hWold q hq]; exact hF₁.vals q (hWmem q hq)) hx hpx
    (fun q hq e => hF₁.loan1 q _ l (hWmem _ hq) hpxW (by rw [hWold _ hq]; exact e) hxW) hnoB
  have hPX : FSt Γ { sb with env := Env.setAtE sb.env (.bind fx jx) c } := hF₁.endTemp hcN hpx hx
  have hpxq : Pos.bind fx jx ∈ allPos sc.env := by rw [← allPos_erase, ← hq.env, allPos_erase]; exact hpx
  have hfX : Fresh { sc with env := Env.setAtE sc.env (.bind fx jx) c } :=
    ((hf₁.untemp hne).of_erase hq.env hq.nextLoan).setAt hpxq (fun l' e => by
      rcases e with e | ⟨c', e⟩ <;> rw [e] at hcN <;> cases hcN)
  exact core_seq_tail hdec hu hw ihw hP hcd
    ((hPX.of_erase (by
      show (Env.setAtE sb.env (.bind fx jx) c).erase = (Env.setAtE sc.env (.bind fx jx) c).erase
      rw [Machine.erase_setAtE, Machine.erase_setAtE, hq.env])).kern hkW)
    (hfX.kern hkW) ((hma.of_modeEq hme₁).of_modeEq hmeW) htdW
    (by rw [← ColumnC.topReadings_kern hkW, topReadings_setAt, ← ColumnC.topReadings_of_erase hq.env, htr₁,
      ← ColumnC.topReadings_kern hk₀])
    (by rw [size_of_kern hkW]; show (Env.setAtE sc.env (.bind fx jx) c).size = _
        rw [size_setAtE, quiet_size hq, hsz₁, size_of_kern hk₀]) hD hrw

/-! ## The induction, and `FragRun` -/

/-- **`FragRun` with the counter carried**, by induction on the fragment's typing. -/
theorem fragRunF {D : Decisions} (hdec : FragDec D) : FragRunF D := by
  intro Γ u A n hint st st' bh v T? hty
  revert n hint st st' bh v T?
  induction hty with
  | zero Γ => exact frag_lift_run hdec (.zero Γ) (core_zero D Γ)
  | succ Γ u hu ih => exact frag_lift_run hdec (.succ Γ u hu) (core_succ ih)
  | var Γ i hi => exact frag_lift_run hdec (.var Γ i hi) (core_var D Γ i hi)
  | bor Γ i hi => exact frag_lift_run hdec (.bor Γ i hi) (core_bor D Γ i hi)
  | asg Γ i u hi hu ih => exact frag_lift_run hdec (.asg Γ i u hi hu) (core_asg hi ih)
  | asgD Γ i u hi hu ih => exact frag_lift_run hdec (.asgD Γ i u hi hu) (core_asgD hi ih)
  | letIn Γ x u w A B hu hw ihu ihw =>
    exact frag_lift_run hdec (.letIn Γ x u w A B hu hw) (core_let hdec hu hw ihu ihw)
  | seq Γ u w A B hu hw ihu ihw =>
    cases A with
    | ref => exact frag_lift_run hdec (.seq Γ u w _ B hu hw) (core_seq_bor hdec hu hw ihu ihw)
    | nat => exact frag_lift_run hdec (.seq Γ u w _ B hu hw) (core_seq_inert hdec (fun e => by cases e) hu hw ihu ihw)
    | unit => exact frag_lift_run hdec (.seq Γ u w _ B hu hw) (core_seq_inert hdec (fun e => by cases e) hu hw ihu ihw)

/-- The checker invariant's last conjunct (the counter above every label that occurs) gives `Fresh` at
a fragment state. -/
theorem fresh_of_counter {Γ : List Form.FT} {st : MState} (hP : FSt Γ st)
    (hc : ∀ l, st.norm.Occurs l → l < st.norm.nextLoan) : Fresh st := by
  intro q hq l e
  apply hc l
  rw [occurs_norm]
  rcases e with e | ⟨w, e⟩
  · exact occurs_of_pos hq (by rw [e]; simp [Value.anyAtom, show (Value.loan l == Value.loan l) = (l == l) from rfl])
  · have hw : w.Num := by
      have := hP.vals q hq; rw [e] at this
      cases this with
      | num hn => cases hn
      | bor _ hw => exact hw
    exact occurs_of_pos hq (by rw [e]; simp [Value.anyAtom])

/-- **`FragRun`, restated with the counter (the lead's ruling, 2026-11-21), PROVED.** -/
theorem fragRun {D : Decisions} (hdec : FragDec D) : FragRun D := by
  intro Γ u A n hint st st' bh v T? hty hP hc hm htd hD h
  obtain ⟨hT, hv, hme, htr, hsz, hF, -⟩ :=
    fragRunF hdec Γ u A n hint st st' bh v T? hty hP (fresh_of_counter hP hc) hm htd hD h
  exact ⟨hT, hv, hme, htr, hsz, hF⟩

end Ochr.Meaning.Steps.Machine
