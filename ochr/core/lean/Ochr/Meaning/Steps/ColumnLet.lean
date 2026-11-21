import Ochr.Meaning.Steps.ColumnRead

/-!
# The column: a typed `let` whose value is pushed, bound and dropped (lead7)

`let h = u; w` in a typed run, where `u`'s value is a number at `Nat` and the binding holds no borrow
and has no site when it is dropped (what the column's program does). The step for `u`, then the
binding pushed on both sides (`rel_pushBind_num`), the reference state between good by (I)
(`Strict.fund_all` at `u`, and the model's `sgood_pushBindShaped`), the step for `w` at the extended
context, and the binding dropped on both sides (`rel_popBind_noSites`, `letLenders_noop`). This is
the case the earlier form could not assemble (docs/31 D81, `Regress/EvalMemGap.not_good_push`):
there the push asked the value's membership of the checker's invariant, which no step concluded;
here the checker's side asks no membership, and the reference state's goodness is (I)'s.
-/

namespace Ochr.Meaning.Steps.Form

open Ochr Ochr.Meaning Ochr.Meaning.Steps
open Classical

/-- The top frame's temporaries. -/
def topTemps (env : Env) : Option (Array Value) := env[env.size - 1]?.map (·.temps)

theorem topTemps_erase (env : Env) : topTemps env.erase = topTemps env := by
  simp only [topTemps, Env.erase_size, Env.erase_get?]; cases env[env.size - 1]? <;> rfl

theorem topTemps_popBindE (env : Env) : topTemps (Env.popBindE env) = topTemps env := by
  simp only [topTemps, Env.popBindE, Array.size_modify, Array.getElem?_modify, if_true]
  cases env[env.size - 1]? <;> rfl

theorem topTemps_withTempT (st : MState) (v : Value) (T? : Option Value) :
    topTemps (st.withTempT v T?).env = (topTemps st.env).map (·.push v) := by
  simp only [topTemps, MState.withTempT, Array.size_modify, Array.getElem?_modify, if_true]
  cases st.env[st.env.size - 1]? <;> rfl

/-- The value a `let` pops after dropping its binding is the one its tail returned, where the drop
ends nothing. -/
theorem popped_eq {st₂ st₃ st' : MState} {r v : Value} {T? : Option Value} (hne : 0 < st₂.env.size)
    (h₃ : Kern { st₂.withTempT r T? with env := Env.popBindE (st₂.withTempT r T?).env } st₃)
    (h' : Kern st₃ (st'.withTempT v T?)) : v = r := by
  have e := congrArg topTemps (h₃.env.trans h'.env)
  simp only [topTemps_erase, topTemps_popBindE, topTemps_withTempT] at e
  rcases h2 : st₂.env[st₂.env.size - 1]? with _ | fr₂
  · rw [Array.getElem?_eq_none_iff] at h2; omega
  rcases h1 : st'.env[st'.env.size - 1]? with _ | fr'
  · simp [topTemps, h1, h2] at e
  simp only [topTemps, h1, h2, Option.map_some, Option.some.injEq] at e
  have := congrArg Array.back? e
  simp only [Array.back?_push, Option.some.injEq] at this
  exact this.symm


/-! ## The assignment's facts across the push and the pop -/

theorem asg_pushBind_num {K : RunCtx} {ρ : Assignment} {st : MState} {v₀ : Value} (hv₀ : v₀.Num)
    (ha : Asg K ρ (st.withTempT v₀ (some .tNat)).norm) (hne : 0 < st.env.size) (x : Hint) (p : Bool)
    (d : DeclInfo) : Asg K ρ ({ st with env := Env.pushBindE st.env x (some .tNat) v₀ p d } : MState).norm := by
  rcases hfr : st.env[st.env.size - 1]? with _ | fr
  · rw [Array.getElem?_eq_none_iff] at hfr; omega
  refine ha.of_refd rfl rfl rfl rfl rfl fun σ hσ => refd_mono_withTempT v₀ (some .tNat) σ ?_
  refine refd_sub (st := st) (st' := { st with env := Env.pushBindE st.env x (some .tNat) v₀ p d })
    rfl rfl rfl rfl ?_ ?_ ?_ σ hσ
  · intro w hw σ' hσ'
    rcases mem_values_pushBindE st.env x (some .tNat) v₀ p d fr hfr hne hw with rfl | hw'
    · rw [hv₀.hasAbs] at hσ'; cases hσ'
    · exact ⟨w, hw', hσ'⟩
  · intro f i b T σ' hb hT hσ'
    by_cases e : Pos.bind f i = .bind (st.env.size - 1) fr.binds.size
    · cases e
      rw [bind_pushBindE_new st.env x (some .tNat) v₀ p d fr hfr] at hb
      cases hb; cases hT; cases hσ'
    · rw [bind_pushBindE_ne st.env x (some .tNat) v₀ p d fr hfr f i e] at hb
      exact .ty f i b T (by show st.env.erase[f]?.bind _ = _; rw [lookup_erase]; exact hb) hT hσ'
  · intro f i b P ws j σ' hb hl hσ'
    by_cases e : Pos.bind f i = .bind (st.env.size - 1) fr.binds.size
    · cases e
      rw [bind_pushBindE_new st.env x (some .tNat) v₀ p d fr hfr] at hb
      cases hb; cases hl
    · rw [bind_pushBindE_ne st.env x (some .tNat) v₀ p d fr hfr f i e] at hb
      exact .lazyTy f i b P ws j (by show st.env.erase[f]?.bind _ = _; rw [lookup_erase]; exact hb) hl hσ'

theorem asg_popBind {K : RunCtx} {ρ : Assignment} {st : MState} (ha : Asg K ρ st.norm) (fr : Frame)
    (hfr : st.env[st.env.size - 1]? = some fr) (hn : 0 < fr.binds.size) :
    Asg K ρ ({ st with env := Env.popBindE st.env } : MState).norm := by
  have hne : 0 < st.env.size := by
    rcases Nat.eq_zero_or_pos st.env.size with h | h
    · rw [Array.getElem?_eq_none (by omega)] at hfr; cases hfr
    · exact h
  refine ha.of_refd rfl rfl rfl rfl rfl (refd_sub rfl rfl rfl rfl ?_ ?_ ?_)
  · intro w hw σ hσ
    exact ⟨w, mem_values_popTop st.env fr hfr hn hne hw, hσ⟩
  · intro f i b T σ hb hT hσ
    by_cases e : Pos.bind f i = .bind (st.env.size - 1) (fr.binds.size - 1)
    · cases e
      have := bind_popTop_old st.env fr hfr
      have hb' : (st.env.modify (st.env.size - 1) popTop)[st.env.size - 1]?.bind (·.binds[fr.binds.size - 1]?) =
        some b := hb
      rw [this] at hb'; cases hb'
    · have hb' : (st.env.modify (st.env.size - 1) popTop)[f]?.bind (·.binds[i]?) = some b := hb
      rw [bind_popTop_ne st.env fr hfr f i e] at hb'
      exact .ty f i b T (by show st.env.erase[f]?.bind _ = _; rw [lookup_erase]; exact hb') hT hσ
  · intro f i b P ws j σ hb hl hσ
    by_cases e : Pos.bind f i = .bind (st.env.size - 1) (fr.binds.size - 1)
    · cases e
      have := bind_popTop_old st.env fr hfr
      have hb' : (st.env.modify (st.env.size - 1) popTop)[st.env.size - 1]?.bind (·.binds[fr.binds.size - 1]?) =
        some b := hb
      rw [this] at hb'; cases hb'
    · have hb' : (st.env.modify (st.env.size - 1) popTop)[f]?.bind (·.binds[i]?) = some b := hb
      rw [bind_popTop_ne st.env fr hfr f i e] at hb'
      exact .lazyTy f i b P ws j (by show st.env.erase[f]?.bind _ = _; rw [lookup_erase]; exact hb') hl hσ

theorem _root_.Ochr.Value.Num.loans {v : Value} (h : v.Num) : v.loans = [] := by
  induction h with
  | zero => simp [Value.loans]
  | succ _ ih => simpa [Value.loans] using ih

/-- An extension read between states with the same counters of unknowns and labels. -/
theorem Ext.congr {K : RunCtx} {ρ ρ' : Assignment} {Δ' : Nat → TyS} {π π' : Nat → Nat} {st₀ st₁ st st' : MState}
    (h : Ext K ρ π st₀ st₁ ρ' Δ' π') (ha₀ : st.absTy = st₀.absTy) (hl₀ : st.nextLoan = st₀.nextLoan)
    (ha₁ : st₁.absTy = st'.absTy) (hl₁ : st₁.nextLoan = st'.nextLoan) : Ext K ρ π st st' ρ' Δ' π' :=
  ⟨by rw [ha₀, ← ha₁]; exact h.abs, by rw [hl₀, ← hl₁]; exact h.lab,
   fun σ hσ => h.agree σ (by rw [← ha₀]; exact hσ), fun l hl => h.ren l (by rw [← hl₀]; exact hl)⟩

/-- **The reference holds nothing at its top binding** where the checker's top binding holds no
borrow (`Rel`'s holders, through `SimEq`). -/
theorem rel_top_shape_none {K : RunCtx} {ρ : Assignment} {φ : Future} {π : Nat → Nat} {st : MState} {s : SState}
    (hr : Rel K ρ φ π st s) (fr : Frame) (b : Binding) (hfr : st.env[st.env.size - 1]? = some fr)
    (hb : fr.binds.back? = some b) (hnb : ∀ l, b.val.holdsBorrow l = false) :
    ∃ frs, s.env.getLast? = some frs ∧ s.shape (.bind s.topIdx (frs.binds.length - 1)) = none ∧
      Pos.bind s.topIdx (frs.binds.length - 1) = .bind (st.env.size - 1) (fr.binds.size - 1) ∧
      valAt st.env (.bind (st.env.size - 1) (fr.binds.size - 1)) = b.val := by
  obtain ⟨frs, hfrs, htop, hlen⟩ := skel_align K ρ st s hr.skel fr hfr
  have hold : Pos.bind s.topIdx (frs.binds.length - 1) = Pos.bind (st.env.size - 1) (fr.binds.size - 1) := by
    rw [htop, hlen]
  rw [Array.back?_eq_getElem?] at hb
  have hbv : valAt st.env (.bind (st.env.size - 1) (fr.binds.size - 1)) = b.val := by
    rw [valAt_bind_lookup, hfr]; simp only [Option.bind_some, hb]; rfl
  have hvsh : Env.shape st.env (.bind (st.env.size - 1) (fr.binds.size - 1)) = none := by
    rw [shape_eq_shapeOf, hbv]
    cases e : b.val with
    | borrow l w => have := hnb l; rw [e] at this; simp [Value.holdsBorrow] at this
    | _ => rfl
  refine ⟨frs, by rw [List.getLast?_eq_getElem?]; exact hfrs, ?_, hold, hbv⟩
  cases e : s.shape (Pos.bind s.topIdx (frs.binds.length - 1)) with
  | none => rfl
  | some l' =>
    obtain ⟨l, h1, _⟩ := hr.sim.2.2.1 _ l' (by simp [IsTemp]) e
    rw [hold] at h1
    change Env.shape st.env _ = _ at h1
    rw [hvsh] at h1; cases h1

section
variable {K : RunCtx} {ρ : Assignment} {φ : Future}

/-- The `let` clause of the strict run, where the aligned table does not erase it. -/
theorem runT_letIn (tl : Bool) (hint : TyS) (x : Hint) (u w : Term) (s : SState)
    (hfl : K.D.flags (scopeOf s) (.letIn x u w) = (false, false)) :
    runT K ρ φ tl hint (.letIn x u w) s = (do
      let d := K.D.declOf (scopeOf s) u
      let ((v, T), s) ← runT K ρ φ false (.plain TyM.err) u s
      let s := pushBindShaped s { ty := T, val := fun _ => v, decl := d }
      let ((r, R), s) ← runT K ρ φ tl (.plain TyM.err) w s
      let held : Option Nat := match s.env.getLast? with
        | some fr => s.shape (.bind s.topIdx (fr.binds.length - 1))
        | none => none
      if (match held with | some l => EndOk K φ s l | none => LetLendersOk K φ s) then
        let s := match held with | some l => s.endLabel l | none => letLenders s
        some ((r, R), s.dropLast)
      else none) := by
  rw [runT]; show SM.erasedIf (K.D.flags (scopeOf s) _) _ s = _; rw [hfl]; rfl

/-- **A typed `let h = u; w` at `evalCore`**, for a right-hand side whose value is a number at `Nat`
and a binding that holds no borrow and has no site when it is dropped. From the steps for `u` (at
the starting context) and for `w` (at every extension: it runs after `u` made unknowns), the facts
about the checker alone (`LetInv`, `DropNoopInv`) and the invariant across the push and the drop (`InvSteps`), and (I) at `u`. -/
theorem let_core (hL : LetInv) (hDN : DropNoopInv) (hI : InvSteps) (hPL : PlaceLocal K.D) (hc : Strict.FundCtx K)
    {n : Nat} {x : Hint} {u w : Term} {Plet Pu Pw : MState → Prop}
    (htail : ∀ st stB, Plet st → Pw stB →
      K.D.declOf (DecideScope.topReadings st) (.letIn x u w) = K.D.declOf (DecideScope.topReadings stB) w)
    (hu : EvalSim K ρ φ n u Pu (· = true)) (hPu : ∀ a b, Kern a b → Plet a → Pu b)
    (hw : ∀ (Δ' : Nat → TyS) (ρ' : Assignment), EvalSim { K with Δ := Δ' } ρ' φ n w Pw (· = true))
    (hflu : ∀ st, Plet st → K.D.flags (DecideScope.topReadings st) u = (false, false))
    (hflw : ∀ st, Pw st → K.D.flags (DecideScope.topReadings st) w = (false, false))
    (hdo : ∀ st, Plet st → K.D.declOf (DecideScope.topReadings st) u = .other)
    (hnumu : ∀ st st₀ st₁ bh v₀ T₀, Plet st → Kern st st₀ → Mode st₀ → st₀.tailDecl = none → DecTab K.D st₁ →
      Runs (Ochr.eval n true u none) st₀ bh (v₀, T₀) st₁ → v₀.Num ∧ T₀ = some .tNat ∧ 0 < st₁.env.size ∧
        DecideScope.topReadings st₁ = DecideScope.topReadings st ∧ Mode st₁)
    (hPw : ∀ (st st₀ st₁ : MState) (bh : Nat) (v₀ : Value) (p : Bool), Plet st → Kern st st₀ → Mode st₀ →
      st₀.tailDecl = none → DecTab K.D st₁ → Runs (Ochr.eval n true u none) st₀ bh (v₀, some .tNat) st₁ →
      Pw { st₁ with env := Env.pushBindE st₁.env x (some .tNat) v₀ p (K.D.declOf (DecideScope.topReadings st₁) u) })
    (hPwk : ∀ a b, Kern a b → Pw a → Pw b)
    (hwv : ∀ (Δ' : Nat → TyS) (ρ' : Assignment), w.valsOk (Strict.ValsP { K with Δ := Δ' } ρ' φ))
    (hwa : ∀ m, w.absBelow m) (hwn : w.hasHolePrim = false)
    (hwcong : ∀ (Δ' : Nat → TyS) (ρ' : Assignment) tl hint s,
      runT { K with Δ := Δ' } ρ' φ tl hint w s = runT K ρ φ tl hint w s)
    (hwhint : ∀ tl hint s, runT K ρ φ tl hint w s = runT K ρ φ tl (.plain TyM.err) w s)
    (hdrop : ∀ stB st₂ bh r T?, Pw stB → Mode stB →
      (stB.tailDecl = none ∨ stB.tailDecl = some (K.D.declOf (DecideScope.topReadings stB) w)) → DecTab K.D st₂ →
      Runs (Ochr.eval n true w none) stB bh (r, T?) st₂ →
      ∃ fr b, st₂.env[st₂.env.size - 1]? = some fr ∧ fr.binds.back? = some b ∧ (b.val = .bot ∨ b.val.Num)) :
    CoreSim K ρ φ (n + 1) (.letIn x u w) Plet (· = true) := by
  intro st st' typed hint v T? s π hPst hty hm htn htd hcd hp hr hS hv hab hnh hfl _ hD bh h
  subst hty
  obtain ⟨du, st₀, st₁, stB, st₂, st₃, v₀, r, T₀, p, bh₁, bh₂, bh₃, hk₀, hm₀, htn₀, htd₀, htdB, hru, hdu,
    hkB, hmeB, htnB, hrw, hrd, hk₃, -, hD₁, hD₂⟩ := hL n x u w hint st st' bh v T? K.D hm htn htd hD h
  obtain ⟨hv₀, rfl, hne₁, hrd₁, hm₁⟩ := hnumu st st₀ st₁ bh₁ v₀ T₀ hPst hk₀ hm₀ htd₀ hD₁ hru
  have hmB : Mode stB := hm₁.of_modeEq hmeB
  have hduo : du = .other := hdu.symm.trans (hdo st hPst)
  have hvu : u.valsOk (Strict.ValsP K ρ φ) := hv.1
  have hvw : w.valsOk (Strict.ValsP K ρ φ) := hv.2
  -- the step for `u`
  have hOu := hu st₀ st₁ true none v₀ (some .tNat) s π (hPu st st₀ hk₀ hPst) rfl hm₀ (.inl htd₀) (hp.of_kern hk₀)
    (hr.of_kern hk₀) hS hvu
    (fun σ hσ => by rw [← hk₀.absTy]; exact hab σ (by simp [Term.anyAtom, hσ])) (by simp [Term.hasHolePrim] at hnh; exact hnh.1)
    (by rw [scopeOf_rel hr]; exact hflu st hPst) (fun e => by cases e) hD₁ bh₁ hru
  rw [htn₀] at hOu
  obtain ⟨ρ₁, Δ₁, π₁, ru, s₁, he₁, hxu, hmu, hau, hlu, hp₁, hr₁⟩ := hOu
  have hxu' : runT K ρ φ false (.plain TyM.err) u s = some (ru, s₁) := hxu
  -- (I) at `u`: the reference state after it is good
  obtain ⟨hgu, hlabu, hlouu, hS₁⟩ := Strict.fund_all hc u hvu false (.plain TyM.err) s s₁ ru hS hxu'
  -- the right-hand side's value: a number, at `Nat`, with no label
  obtain ⟨m, hmv⟩ := hv₀.vmean
  have hru1 : ru.1 = .el0 Nat m := by rw [← hmu, ← meanV_eq_mean]; exact hmv _ _ _ _ _ _
  have hru2 : (Value.tyS ({ K with Δ := Δ₁ } : RunCtx).dm ({ K with Δ := Δ₁ } : RunCtx).M ({ K with Δ := Δ₁ } : RunCtx).Γ
      ρ₁ .tNat).m = ru.2.m := hau _ rfl
  have hrul : ru.2.label = none := by rw [hlu, num_heldLabel hv₀]; rfl
  obtain ⟨fr₁, hfr₁⟩ : ∃ fr₁, st₁.env[st₁.env.size - 1]? = some fr₁ :=
    ⟨_, Array.getElem?_eq_getElem (by omega)⟩
  -- the push, on both sides
  have hr₁' : Rel { K with Δ := Δ₁ } ρ₁ φ π₁ st₁ s₁ := rel_of_withTempT_num hv₀ hr₁
  have hsc₁ : scopeOf s₁ = DecideScope.topReadings st₁ := scopeOf_rel hr₁'
  let bB : SBinding := { ty := ru.2, val := fun _ => ru.1, decl := du }
  have hpb : pushBindShaped s₁ { ty := ru.2, val := fun _ => ru.1, decl := K.D.declOf (scopeOf s) u } =
      s₁.pushBind bB := by
    rw [scopeOf_rel hr, hdu]; unfold pushBindShaped; rw [hrul]
  have hpb' : pushBindShaped s₁ bB = s₁.pushBind bB := by unfold pushBindShaped; rw [hrul]
  have hrB : Rel { K with Δ := Δ₁ } ρ₁ φ π₁ stB (s₁.pushBind bB) :=
    (rel_pushBind_num hr₁' hne₁ x .tNat hv₀ p du ru.2 hru2 ru.1
      (fun φ' hint' => by rw [hru1]; exact hmv _ _ _ _ _ _)).of_kern hkB
  have hpB : Pre { K with Δ := Δ₁ } ρ₁ stB :=
    ⟨hp₁.ctx.of_eq (by show stB.inds = st₁.inds; rw [← hkB.inds])
      (by show stB.globals = st₁.globals; rw [← hkB.globals]),
     by rw [← hkB.norm, hduo]; exact hI.bindNum K.D K.Γ st₁ x v₀ _ p hPL hv₀ hne₁ hp₁.inv,
     by rw [← hkB.norm]; exact asg_pushBind_num hv₀ hp₁.asg hne₁ x p du⟩
  have hs₁ne : s₁.env ≠ [] := by
    obtain ⟨frs, hfrs, -, -⟩ := skel_align { K with Δ := Δ₁ } ρ₁ st₁ s₁ hr₁'.skel fr₁ hfr₁
    intro e; rw [e] at hfrs; simp at hfrs
  have hSB : Strict.SGood K.dm K.Γ φ (s₁.pushBind bB) := by
    rw [← hpb']; exact Strict.sgood_pushBindShaped hS₁ bB rfl hgu hlabu hlouu hs₁ne
  -- the step for `w`, at the extended context
  have hPB : Pw stB := by
    have := hPw st st₀ st₁ bh₁ v₀ p hPst hk₀ hm₀ htd₀ hD₁ hru
    rw [hrd₁, hdu] at this; exact hPwk _ _ hkB this
  have htdB' : stB.tailDecl = none ∨ stB.tailDecl = some (K.D.declOf (DecideScope.topReadings stB) w) := by
    exact .inr (by rw [htdB, hcd, htail st stB hPst hPB])
  have hOw := hw Δ₁ ρ₁ stB st₂ true none r T? (s₁.pushBind bB) π₁ hPB rfl hmB htdB' hpB hrB hSB (hwv Δ₁ ρ₁)
    (fun σ hσ => hwa _ σ hσ) hwn (by rw [scopeOf_rel hrB]; exact hflw stB hPB) (fun e => by cases e) hD₂ bh₂ hrw
  rw [htnB] at hOw
  obtain ⟨ρ₂, Δ₂, π₂, rw', s₂, he₂, hxw, hmw, haw, hlw, hp₂, hr₂⟩ := hOw
  -- the drop: the binding `let` pushed is now `⊥` or a number, with no loan, borrow or site
  obtain ⟨fr₂, bx, hfr₂, hbx, hbxv⟩ := hdrop stB st₂ bh₂ r T? hPB hmB htdB' hD₂ hrw
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
  have hns : ∀ l pos, bx.val.sitesOf l pos [] = [] := fun l pos => by
    rcases hbxv with e | e
    · rw [e]; simp [Value.sitesOf]
    · exact e.sitesOf l pos []
  let frW : Frame := { fr₂ with temps := fr₂.temps.push r, tempTys := fr₂.tempTys.push T? }
  have hfrW : (st₂.withTempT r T?).env[(st₂.withTempT r T?).env.size - 1]? = some frW := by
    simp only [MState.withTempT, Array.size_modify, Array.getElem?_modify, if_true, hfr₂]; rfl
  have hbW : frW.binds.back? = some bx := hbx
  have hn₂ : 0 < frW.binds.size := by
    have := hbW; rw [Array.back?_eq_getElem?] at this
    rcases Nat.eq_zero_or_pos frW.binds.size with h0 | h0
    · rw [Array.getElem?_eq_none (by omega)] at this; cases this
    · exact h0
  have hne₂ : 0 < st₂.env.size := by
    rcases Nat.eq_zero_or_pos st₂.env.size with h0 | h0
    · rw [Array.getElem?_eq_none (by omega)] at hfr₂; cases hfr₂
    · exact h0
  have h₃ := hDN n (st₂.withTempT r T?) st₃ bh₃ frW bx hfrW hbW hnl hnbor hnb hrd
  obtain rfl : v = r := popped_eq hne₂ h₃ hk₃
  have hk' := h₃.trans hk₃
  -- the reference's drop ends nothing: it holds nothing there and nothing is lent there
  obtain ⟨frs, hlast, hsh, hpos, hbv⟩ := rel_top_shape_none hr₂ frW bx hfrW hbW hnb
  have hll : letLenders s₂ = s₂ := letLenders_noop frs hlast (by
    rw [hpos]; exact rel_noSites_at hr₂ (fun l => by rw [hbv]; exact hns l _))
  -- the reference's `let`
  have hxw' : runT K ρ φ st.curTail (.plain TyM.err) w (s₁.pushBind bB) = some (rw', s₂) := by
    rw [← hwhint _ (hintM { K with Δ := Δ₁ } ρ₁ none), ← hwcong Δ₁ ρ₁]; exact hxw
  have hxl : runT K ρ φ st.curTail (hintM K ρ hint) (.letIn x u w) s = some (rw', s₂.dropLast) := by
    rw [runT_letIn _ _ x u w s hfl, hxu']
    have hllok : LetLendersOk K φ s₂ := by
      unfold LetLendersOk; rw [hlast]
      exact accessOk_noSites (by rw [hpos]; exact rel_noSites_at hr₂ (fun l => by rw [hbv]; exact hns l _))
    simp only [bind, Option.bind]
    rw [hpb, hxw']
    simp only [hlast, hsh, hll, if_pos hllok]
  -- the conclusion
  have hext : Ext K ρ π st st' ρ₂ Δ₂ π₂ :=
    (he₁.congr hk₀.absTy hk₀.nextLoan hkB.absTy hkB.nextLoan).trans (he₂.congr rfl rfl hk'.absTy hk'.nextLoan)
  refine ⟨ρ₂, Δ₂, π₂, rw', s₂.dropLast, hext, hxl, hmw, haw, hlw, ?_, ?_⟩
  · refine Pre.of_kern hk' ⟨hp₂.ctx.of_eq rfl rfl, ?_, asg_popBind hp₂.asg frW hfrW hn₂⟩
    exact hI.popBind K.D K.Γ (st₂.withTempT v T?) frW bx hPL hfrW hbW hbxv hp₂.inv
  · exact (rel_popBind_noSites hr₂ frW bx hfrW hbW (fun l => hns l _) hnb).of_kern hk'

end

end Ochr.Meaning.Steps.Form
