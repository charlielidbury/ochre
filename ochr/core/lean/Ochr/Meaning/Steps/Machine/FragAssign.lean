import Ochr.Meaning.Steps.Machine.FragEnds
import Ochr.Meaning.Steps.Machine.AssignDerefInv

/-!
# The fragment's writes: `AssignVarInv` and `AssignDerefInvF` (machine lane, machine6)

`x := u` at a root number variable: `assignDerefInv`'s inversion with the place a variable
(`lentProofAssign`, `lentLeafCheck`, `strongUpdate`, `openWrite` do nothing at a root); the write
(`assignPlace`) at an old content that is a number or `⊥` ends nothing; at a lent variable its path
access ends the borrow first (`runs_accessPath_lentF`, `endE`). `*y := u`: `assignDerefInv`'s proof
with the case it left out: `y` holding `⊥` when `u` has run, where `assignPlace`'s `content (*y)` errs.
-/

namespace Ochr.Meaning.Steps.Machine

open Ochr Ochr.Meaning Ochr.Meaning.Steps Ochr.Meaning.DecideScope Ochr.Meaning.Steps.Slice
open Ochr.Meaning.Steps.Form

theorem lookup_of_bindPos {E : Env} {f j : Nat} (hp : Pos.bind f j ∈ allPos E) :
    ∃ bd, E[f]?.bind (fun fr : Frame => fr.binds[j]?) = some bd ∧ valAt E (.bind f j) = bd.val := by
  obtain ⟨fr, bd, hf, hbd⟩ := mem_allPos_bind E f j hp
  refine ⟨bd, by rw [hf]; exact hbd, ?_⟩
  rw [valAt_bind_eq, hf]; simp [hbd]

theorem runs_unsizedCheck_bot {p : Place} {w : String} {st st' : MState} {b : Nat} {u : Unit}
    (h : Runs (unsizedCheck p .bot w) st b u st') : st' = st := by
  unfold unsizedCheck atRuntime at h
  peel h; split at h <;> (peel h; exact (runs_pure_inv h).2)

theorem runs_lentProofAssign_var {k i : Nat} {u : Term} {st st' : MState} {b : Nat}
    {r : Option (Value × Option Value)} (h : Runs (lentProofAssign k (.var i) u) st b r st') : r = none ∧ st' = st := by
  cases k with
  | zero => unfold lentProofAssign at h; simp only [runs_exhausted_iff] at h
  | succ m => unfold lentProofAssign at h; exact runs_pure_inv h

theorem runs_lentLeafCheck_var {k i : Nat} {Tv : Option Value} {st st' : MState} {b : Nat} {r : Bool}
    (h : Runs (lentLeafCheck k (.var i) Tv) st b r st') : r = false ∧ st' = st := by
  cases k with
  | zero => unfold lentLeafCheck at h; simp only [runs_exhausted_iff] at h
  | succ m => unfold lentLeafCheck at h; exact runs_pure_inv h

theorem runs_strongUpdate_var {i : Nat} {st st' : MState} {b : Nat} {r : Bool}
    (h : Runs (strongUpdate (.var i)) st b r st') : r = false ∧ st' = st := by
  unfold strongUpdate at h; exact runs_pure_inv h

/-- **[Assign] at a root variable after its path access** (D115: the value is the top temporary):
the old content `w`, a number or `⊥`, ends nothing; the temporary popped and written at the variable. -/
theorem runs_assignPlace_after {k i f j : Nat} {w v₀ : Value} {st s st' : MState} {b : Nat}
    (hacc : ∀ m b₀ s₁, k = m + 1 → Runs (Ochr.accessPath m (.var i)) st b₀ () s₁ → s₁ = s)
    (hpos : ckVarPos s.env i = some (.bind f j)) (hv : valAt s.env (.bind f j) = w) (hw : w.Num ∨ w = .bot)
    (htop : (s.env[s.env.size - 1]!).temps.back? = some v₀)
    (h : Runs (assignPlace k (.var i)) st b () st') :
    ∃ X, st' = { s with env := Env.setAtE (Env.popTempE s.env) (.bind f j) v₀, placeLog := X } := by
  cases k with
  | zero => unfold assignPlace at h; simp only [runs_exhausted_iff] at h
  | succ m =>
    unfold assignPlace at h
    obtain ⟨_, s₂, b₂, ha, h₂⟩ := Runs.bind_inv h
    clear h
    have e2 : s₂ = s := hacc m _ _ rfl ha
    subst s₂
    obtain ⟨_, s₃, b₃, hai, h₃⟩ := Runs.bind_inv h₂
    clear h₂
    have e3 : s₃ = s := by
      rcases hw with hn | hb
      · obtain ⟨bd, hlk, hbv⟩ := lookup_of_bindPos (ckVarPos_mem _ hpos)
        exact runs_accessInside_num ⟨hpos, hlk, by rw [← hbv, hv]; exact hn⟩ hai
      · exact runs_accessInside_bot hpos (hv.trans hb) hai
    subst s₃
    obtain ⟨old, s₄, b₄, hc, h₄⟩ := Runs.bind_inv h₃
    clear h₃
    obtain ⟨e4, e5⟩ := runs_content_at hpos hv hc
    subst s₄ old
    obtain ⟨_, s₅, b₅, hu, h₅⟩ := Runs.bind_inv h₄
    clear h₄
    have e6 : s₅ = s := by
      rcases hw with hn | e
      · exact runs_unsizedCheck_num hn hu
      · subst e; exact runs_unsizedCheck_bot hu
    subst s₅
    have hbr : w.borrowBelowRoot = false := by
      rcases hw with hn | e
      · exact Value.Num.borrowBelowRoot_false hn
      · rw [e]; rfl
    rw [hbr] at h₅
    have hll : ∀ E : Env, liveLoansIn E w = [] := fun _ => liveLoansIn_nil (by
      rcases hw with hn | e
      · exact Value.Num.loans_nil hn
      · rw [e]; rfl)
    simp only [Bool.false_eq_true, if_false] at h₅
    have hcases : w = .zero ∨ (∃ w', w = .succ w') ∨ w = .bot := by
      rcases hw with hn | e
      · cases hn with
        | zero => exact .inl rfl
        | succ _ => exact .inr (.inl ⟨_, rfl⟩)
      · exact .inr (.inr e)
    rcases hcases with e | ⟨w', e⟩ | e <;> rw [e] at h₅ hll <;>
      simp only [runs_get_bind, hll, List.isEmpty_nil, Bool.not_true, Bool.false_eq_true, if_false] at h₅ <;>
    (obtain ⟨v', s₆, b₆, hp, h₆⟩ := Runs.bind_inv h₅
     obtain ⟨htop', e7⟩ := runs_popTemp_inv hp
     subst s₆
     have hv' : v' = v₀ := by rw [htop] at htop'; exact (Option.some.inj htop').symm
     subst v'
     obtain ⟨_, s₇, b₇, hle, h₇⟩ := Runs.bind_inv h₆
     obtain ⟨X, e8⟩ := runs_logEffect_inv hle
     subst s₇
     obtain ⟨pos, v'', hp', hu', e9⟩ := runs_setPlace_inv h₇
     subst st'
     have hp'' : ckVarPos (Env.popTempE s.env) i = some pos := hp'
     rw [ckVarPos_popTempE, hpos] at hp''
     cases hp''
     simp only [Place.steps, Value.updAt, Option.some.injEq] at hu'
     subst hu'
     exact ⟨X, rfl⟩)

theorem popTempE_setAtE_bind (E : Env) (f j : Nat) (v : Value) :
    Env.popTempE (Env.setAtE E (.bind f j) v) = Env.setAtE (Env.popTempE E) (.bind f j) v := by
  apply Array.ext_getElem?
  intro a
  simp only [Env.popTempE, Env.setAtE, Array.getElem?_modify, Array.size_modify]
  by_cases h1 : E.size - 1 = a <;> by_cases h2 : f = a <;> simp [h1, h2] <;> cases E[a]? <;> simp

theorem popTempE_endE_bind (E : Env) (f j f' j' : Nat) (c : Value) :
    Env.popTempE (endE E (.bind f j) (.bind f' j') c) = endE (Env.popTempE E) (.bind f j) (.bind f' j') c := by
  rw [endE, endE, popTempE_setAtE_bind, popTempE_setAtE_bind]

theorem topTemps_setAtE_bind' (E : Env) (f j : Nat) (v : Value) :
    ((Env.setAtE E (.bind f j) v)[(Env.setAtE E (.bind f j) v).size - 1]!).temps = (E[E.size - 1]!).temps := by
  have hs : (Env.setAtE E (.bind f j) v).size = E.size := size_setAtE_any _ _ _
  rw [hs]
  simp only [Env.setAtE, getElem!_def, Array.getElem?_modify]
  by_cases h : f = E.size - 1
  · rw [if_pos h]; cases E[E.size - 1]? <;> rfl
  · rw [if_neg h]

/-- `FEnd` with a number pushed as a temporary. -/
theorem _root_.Ochr.Meaning.Steps.Form.FEnd.withTempT_num {st : MState} {px ph : Pos} {l : Nat} {c v : Value}
    (hF : FEnd st.env px ph l c) (hv : v.Num) (T : Option Value) : FEnd (st.withTempT v T).env px ph l c := by
  have hne : 0 < st.env.size := by
    have hp := hF.hpx
    cases px with
    | bind f j => obtain ⟨fr, -, hf, -⟩ := mem_allPos_bind _ _ _ hp; have := lt_of_getElem?' hf; omega
    | temp f j => obtain ⟨fr, hf, -⟩ := mem_allPos_temp _ _ _ hp; have := lt_of_getElem?' hf; omega
  obtain ⟨fr, hfr⟩ : ∃ fr, st.env[st.env.size - 1]? = some fr :=
    ⟨_, Array.getElem?_eq_getElem (by omega : st.env.size - 1 < st.env.size)⟩
  have hA : allPos (st.withTempT v T).env = allPos st.env ++ [.temp (st.env.size - 1) fr.temps.size] := by
    rw [allPos_withTempT', allPos_pushTempE _ _ fr hfr hne]
  have hnew : valAt (st.withTempT v T).env (.temp (st.env.size - 1) fr.temps.size) = v := by
    rw [valAt_withTempT', valAt_pushTempE_new _ _ fr hfr]
  have hold : ∀ q ∈ allPos st.env, valAt (st.withTempT v T).env q = valAt st.env q := by
    intro q hq; rw [valAt_withTempT', valAt_pushTempE_mem (E := st.env) (v := v) (fr := fr) (hfr := hfr) hq]
  have hcases : ∀ q ∈ allPos (st.withTempT v T).env, q = .temp (st.env.size - 1) fr.temps.size ∨ q ∈ allPos st.env := by
    intro q hq; rw [hA, List.mem_append, List.mem_singleton] at hq; exact hq.symm
  have hnl : ∀ m, v ≠ .loan m := fun m e => by rw [e] at hv; cases hv
  have hnb : ∀ m w, v ≠ .borrow m w := fun m w e => by rw [e] at hv; cases hv
  refine ⟨fun q hq => ?_, fun f i m hq => ?_, by rw [hA]; exact List.mem_append_left _ hF.hpx,
    by rw [hA]; exact List.mem_append_left _ hF.hph, by rw [hold _ hF.hpx]; exact hF.x, by rw [hold _ hF.hph]; exact hF.y,
    hF.c, fun q hq e => ?_, fun q hq w e => ?_⟩
  · rcases hcases q hq with rfl | hq'
    · rw [hnew]; exact .num hv
    · rw [hold q hq']; exact hF.vals q hq'
  · rcases hcases _ hq with e | hq'
    · rw [e, hnew]; exact hnl m
    · rw [hold _ hq']; exact hF.tempNoLoan f i m hq'
  · rcases hcases q hq with rfl | hq'
    · rw [hnew] at e; exact absurd e (hnl l)
    · rw [hold q hq'] at e; exact hF.loan1 q hq' e
  · rcases hcases q hq with rfl | hq'
    · rw [hnew] at e; exact absurd e (hnb l w)
    · rw [hold q hq'] at e; exact hF.bor1 q hq' w e

set_option maxHeartbeats 4000000 in
/-- **`AssignVarInv`**: `x := u` at a root number variable. -/
theorem assignVarInv : AssignVarInv := by
  intro n i u hint st st' bh v T? D hm htn htd hty hD h
  unfold Ochr.evalCore at h
  obtain ⟨b₁, h⟩ := Runs.tick_bind h
  obtain ⟨want, s₁, b₂, hw, h⟩ := Runs.bind_inv (runs_get_bind.mp h)
  obtain ⟨hw1, hw2⟩ := runs_wanted_inv hw
  subst hw1; subst s₁
  simp only [Term.placeOperand?] at h
  obtain ⟨o, s₂, b₃, hp, h₁⟩ := Runs.bind_inv h
  clear h
  obtain ⟨rfl, hs2⟩ := runs_projIn_var hp
  subst s₂
  simp only [if_true] at h₁
  obtain ⟨r, s₃, b₄, hlp, h₂⟩ := Runs.bind_inv h₁
  clear h₁
  obtain ⟨rfl, hs3⟩ := runs_lentProofAssign_var hlp
  subst s₃
  simp only at h₂
  -- D124: `readsHint` is computed before the hint's `if` (the nested `←` is lifted); it reads only
  obtain ⟨rh, s₃', b₄', hrh, h₂'⟩ := Runs.bind_inv h₂
  clear h₂
  have := runs_keep (keep_readsHint _ _ _ _) hrh; subst s₃'
  obtain ⟨hu, s₄, b₅, hh, h₃⟩ := Runs.ite_bind_inv h₂'
  clear h₂'
  have hs4 : s₄ = st := by
    rcases hh with hh | hh
    · exact (runs_placeTypeQ_var_gen hty hh).2
    · exact (runs_pure_inv hh).2
  subst s₄
  obtain ⟨Tp0, s₅, b₆, htp, h₄⟩ := Runs.bind_inv h₃
  clear h₃
  obtain ⟨rfl, hs5⟩ := runs_placeTypeQ_var_gen hty htp
  subst s₅
  obtain ⟨strong, s₆, b₇, hsu, h₄⟩ := Runs.bind_inv h₄
  obtain ⟨rfl, hs6⟩ := runs_strongUpdate_var hsu
  subst s₆
  simp only [Bool.false_eq_true, if_false, Bool.false_and] at h₄
  obtain ⟨_, s₇, b₈, hp1, h₅⟩ := Runs.bind_inv h₄
  obtain ⟨-, hs7⟩ := runs_pure_inv hp1
  subst s₇
  obtain ⟨Td0, s₈, b₉, hp2, h₆⟩ := Runs.bind_inv h₅
  obtain ⟨rfl, hs8⟩ := runs_pure_inv hp2
  subst s₈
  obtain ⟨⟨v₀, T₀⟩, st₁, bh₁, hru, h₇⟩ := Runs.bind_inv h₆
  obtain ⟨_, sT, bT, hpu, h₇⟩ := Runs.bind_inv h₇
  have hsT := runs_pushTemp_inv hpu
  subst hsT
  simp only [Bool.false_and, Bool.and_false, Bool.not_false, Bool.and_self, Bool.false_eq_true, if_false,
    if_true] at h₇
  obtain ⟨lf, s₉, b₁₀, hlf, h₈⟩ := Runs.bind_inv h₇
  obtain ⟨rfl, hs9⟩ := runs_lentLeafCheck_var hlf
  subst s₉
  simp only [Bool.false_eq_true, if_false] at h₈
  obtain ⟨A, s₁₀, b₁₁, hpA, h₉⟩ := Runs.bind_inv h₈
  obtain ⟨rfl, hs10⟩ := runs_pure_inv hpA
  subst s₁₀
  obtain ⟨_, sE, b₁₂, hex, h₁₀⟩ := Runs.bind_inv h₉
  obtain ⟨_, s₁₁, b₁₃, hap, h₁₁⟩ := Runs.bind_inv h₁₀
  obtain ⟨_, s₁₂, b₁₄, how, h₁₂⟩ := Runs.bind_inv h₁₁
  obtain ⟨hvt, hs12⟩ := runs_pure_inv h₁₂
  subst s₁₂
  simp only [Prod.mk.injEq] at hvt
  obtain ⟨rfl, rfl⟩ := hvt
  have hg : TablesGrow st₁ st' :=
    (TablesGrow.withTempT _ _ _).trans ((Runs.grows (grows_expectTy _ _ _ _) hex).trans
      ((Runs.grows (growsM_of_growsIn fun _ => (machineGrows n).assignPlace _) hap).trans
        (Runs.grows (growsM_of_growsIn fun _ => (machineGrows n).openWrite _) how)))
  have how' := runs_openWrite_var how
  subst s₁₁
  refine ⟨st, st₁, hu, v₀, T₀, b₉, Kern.rfl' _, hm, htn, htd, hru, DecTab.back hD hg, rfl, rfl, ?_⟩
  intro f j bd hpos hb hv₀
  obtain ⟨hq, hme⟩ := expectTy_inv hex
  have hposT : ckVarPos (st₁.withTempT v₀ T₀).env i = some (.bind f j) := by
    rw [withTempT_env, ckVarPos_pushTempTyE]; exact hpos
  have hposE : ckVarPos sE.env i = some (.bind f j) := by
    rw [← ckVarPos_erase, ← hq.env, ckVarPos_erase]; exact hposT
  have hmem : Pos.bind f j ∈ allPos st₁.env := ckVarPos_mem _ hpos
  have hvE : valAt sE.env (.bind f j) = bd.val := by
    rw [← valAt_erase, ← hq.env, valAt_erase, valAt_withTempT', valAt_pushTempE_bind]
    obtain ⟨bd', hb', hv'⟩ := lookup_of_bindPos hmem
    rw [hb] at hb'; cases hb'; exact hv'
  have hne : 0 < st₁.env.size := by
    obtain ⟨fr, b', hf, -⟩ := mem_allPos_bind st₁.env f j hmem
    exact Nat.lt_of_le_of_lt (Nat.zero_le f) (Array.getElem?_eq_some_iff.mp hf).1
  have htopT : ((st₁.withTempT v₀ T₀).env[(st₁.withTempT v₀ T₀).env.size - 1]!).temps.back? = some v₀ := by
    rw [withTempT_env]
    have hs : (Env.pushTempTyE st₁.env v₀ T₀).size = st₁.env.size := by simp [Env.pushTempTyE]
    rw [hs]
    simp only [Env.pushTempTyE, getElem!_def, Array.getElem?_modify, if_true,
      Array.getElem?_eq_getElem (show st₁.env.size - 1 < st₁.env.size by omega), Option.map_some,
      Array.back?_push]
  have htopE : (sE.env[sE.env.size - 1]!).temps.back? = some v₀ := by
    have hs : sE.env.size = (st₁.withTempT v₀ T₀).env.size := by rw [← Env.erase_size, ← hq.env, Env.erase_size]
    rw [hs, ← temps_erase, ← hq.env, temps_erase]; exact htopT
  have henv : st₁.env.erase = (Env.popTempE sE.env).erase := by
    rw [erase_popTempE_congr hq.env.symm, withTempT_env, popTempE_pushTempTyE]
  -- the write where `x` holds a number or `⊥`, and where it is lent to a binding's borrow
  have hNB : (bd.val.Num ∨ bd.val = .bot) →
      ∃ X, st' = { sE with env := Env.setAtE (Env.popTempE sE.env) (.bind f j) v₀, placeLog := X } := by
    intro hbv
    refine runs_assignPlace_after (s := sE) (fun m b₀ s₁ _ ha => ?_) hposE hvE hbv htopE hap
    rcases hbv with hn | hbot
    · obtain ⟨bdE, hlkE, hvE'⟩ := lookup_of_bindPos (ckVarPos_mem _ hposE)
      exact runs_accessPath_num ⟨hposE, hlkE, by rw [← hvE', hvE]; exact hn⟩ ha
    · exact runs_accessPath_bot hposE (hvE.trans hbot) ha
  have hL : ∀ f' j' m c, FEnd st₁.env (.bind f j) (.bind f' j') m c →
      ∃ X, st' = { sE with
        env := Env.setAtE (Env.popTempE (endE sE.env (.bind f j) (.bind f' j') c)) (.bind f j) v₀
        placeLog := X } := by
    intro f' j' m c hF
    have hFE : FEnd sE.env (.bind f j) (.bind f' j') m c := (hF.withTempT_num hv₀ T₀).of_erase hq.env
    have hpos' : ckVarPos (endE sE.env (.bind f j) (.bind f' j') c) i = some (.bind f j) := by
      rw [ckVarPos_endE]; exact hposE
    have hv' : valAt (endE sE.env (.bind f j) (.bind f' j') c) (.bind f j) = c := by
      rw [hFE.valAt_endE, if_pos rfl]
    have htop' : ((endE sE.env (.bind f j) (.bind f' j') c)[(endE sE.env (.bind f j) (.bind f' j') c).size - 1]!).temps.back?
        = some v₀ := by
      rw [endE, topTemps_setAtE_bind', topTemps_setAtE_bind']; exact htopE
    exact runs_assignPlace_after (s := { sE with env := endE sE.env (.bind f j) (.bind f' j') c })
      (fun m' b₀ s₁ _ ha => runs_accessPath_lentF hFE hposE ha) hpos' hv' (.inl hFE.c) htop' hap
  refine ⟨{ sE with env := Env.popTempE sE.env },
    ⟨henv, hq.globals, hq.inds, hq.refs, hq.etaRefs, hq.goal, hq.neutrals, hq.liveScope, hq.nextLoan, hq.absSize,
      hq.absTy⟩,
    fun hT => ?_, fun hcase => ?_, fun hbv => ?_, fun f' j' m c hF => ?_⟩
  · have hsE : sE = st₁.withTempT v₀ T₀ := by
      cases T₀ with
      | none => exact runs_expectTy_none' hex
      | some T₀ => exact runs_expectTy_of_beq (hT T₀ rfl) hex
    subst hsE
    have e : ({ st₁.withTempT v₀ T₀ with env := Env.popTempE (st₁.withTempT v₀ T₀).env } : MState) = st₁ := by
      rw [withTempT_env, popTempE_pushTempTyE]; rfl
    rw [e]; exact fun _ _ h => h
  · rcases hcase with hn | hbot | ⟨f', j', m, c, hF⟩
    · obtain ⟨X, rfl⟩ := hNB (.inl hn); exact ⟨hme.headEval, hme.copying, hme.inPlace, hme.erased⟩
    · obtain ⟨X, rfl⟩ := hNB (.inr hbot); exact ⟨hme.headEval, hme.copying, hme.inPlace, hme.erased⟩
    · obtain ⟨X, rfl⟩ := hL f' j' m c hF; exact ⟨hme.headEval, hme.copying, hme.inPlace, hme.erased⟩
  · obtain ⟨X, rfl⟩ := hNB hbv
    exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  · obtain ⟨X, rfl⟩ := hL f' j' m c hF
    refine ⟨?_, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
    simp only [popTempE_endE_bind]

theorem noRun_content_deref_bot {i f j : Nat} {st st' : MState} {b : Nat} {v : Value}
    (hpos : ckVarPos st.env i = some (.bind f j)) (hv : valAt st.env (.bind f j) = .bot)
    (h : Runs (content (.deref (.var i))) st b v st') : False := by
  unfold content at h
  obtain ⟨pos, s₁, b₁, hvp, h₁⟩ := Runs.bind_inv h
  obtain ⟨rfl, hp⟩ := runs_varPos_inv hvp
  rw [hpos] at hp; cases hp
  obtain ⟨x, s₂, b₂, hg, h₂⟩ := Runs.bind_inv h₁
  obtain ⟨rfl, rfl⟩ := Steps.runs_getAt_inv hg
  simp only [Place.steps, List.nil_append] at h₂
  rw [hv] at h₂
  simp only [Value.follow, stepV, Option.bind_none] at h₂
  obtain ⟨_, _, _, _, he⟩ := Runs.bind_inv h₂
  simp only [runs_err_iff] at he

/-- **[Assign] at `*y` with `y` holding `⊥` fails**: the path access ends nothing (`⊥` has no path
`[*]`), and `accessInside` reads `content (*y)`, which errs ("no such place"). -/
theorem noRun_assignPlace_deref_bot {k i f j : Nat} {st st' : MState} {b : Nat}
    (hpos : ckVarPos st.env i = some (.bind f j)) (hv : valAt st.env (.bind f j) = .bot)
    (h : Runs (assignPlace k (.deref (.var i))) st b () st') : False := by
  cases k with
  | zero => unfold assignPlace at h; simp only [runs_exhausted_iff] at h
  | succ m =>
    unfold assignPlace at h
    obtain ⟨_, s₂, b₂, ha, h₂⟩ := Runs.bind_inv h
    have e2 : s₂ = st := by
      cases m with
      | zero => unfold accessPath at ha; simp only [runs_exhausted_iff] at ha
      | succ k =>
        unfold accessPath at ha
        simp only [Place.steps, List.nil_append] at ha
        rw [runs_get_bind] at ha
        obtain ⟨pos, s₁, b₁, hvp, h₁⟩ := Runs.bind_inv ha
        obtain ⟨rfl, hp⟩ := runs_varPos_inv hvp
        rw [hpos] at hp; cases hp
        rw [hv, show firstLiveLoanOnPath s₁.env .bot [.deref] = none by simp [firstLiveLoanOnPath, stepV]] at h₁
        exact (runs_pure_inv h₁).2
    subst s₂
    obtain ⟨_, s₃, b₃, hai, h₃⟩ := Runs.bind_inv h₂
    cases m with
    | zero => unfold accessInside at hai; simp only [runs_exhausted_iff] at hai
    | succ k =>
      unfold accessInside at hai
      obtain ⟨v, s₁, b₁, hc, -⟩ := Runs.bind_inv hai
      exact noRun_content_deref_bot hpos hv hc

set_option maxHeartbeats 4000000 in
/-- **`AssignDerefInvF`**: `assignDerefInv`'s decomposition, with the case it left out (`y` holding `⊥`
after `u`: the write fails). -/
theorem assignDerefInvF : AssignDerefInvF := by
  intro n i u hint st st' bh v T? D hm htn htd hty hD h
  unfold Ochr.evalCore at h
  obtain ⟨b₁, h⟩ := Runs.tick_bind h
  obtain ⟨want, s₁, b₂, hw, h⟩ := Runs.bind_inv (runs_get_bind.mp h)
  obtain ⟨hw1, hw2⟩ := runs_wanted_inv hw
  subst hw1; subst s₁
  simp only [Term.placeOperand?] at h
  obtain ⟨o, s₂, b₃, hp, h₁⟩ := Runs.bind_inv h
  clear h
  obtain ⟨rfl, hs2⟩ := runs_projIn_deref_var hp
  subst s₂
  simp only [if_true] at h₁
  obtain ⟨r, s₃, b₄, hlp, h₂⟩ := Runs.bind_inv h₁
  clear h₁
  obtain ⟨rfl, hs3⟩ := runs_lentProofAssign_deref hlp
  subst s₃
  simp only at h₂
  -- D124: `readsHint` is computed before the hint's `if` (the nested `←` is lifted); it reads only
  obtain ⟨rh, s₃', b₄', hrh, h₂'⟩ := Runs.bind_inv h₂
  clear h₂
  have := runs_keep (keep_readsHint _ _ _ _) hrh; subst s₃'
  obtain ⟨hu, s₄, b₅, hh, h₃⟩ := Runs.ite_bind_inv h₂'
  clear h₂'
  have hs4 : s₄ = st := by
    rcases hh with hh | hh
    · exact (runs_placeTypeQ_deref hty hh).2
    · exact (runs_pure_inv hh).2
  subst s₄
  obtain ⟨Tp0, s₅, b₆, htp, h₄⟩ := Runs.bind_inv h₃
  clear h₃
  obtain ⟨rfl, hs5⟩ := runs_placeTypeQ_deref hty htp
  subst s₅
  obtain ⟨strong, s₆, b₇, hsu, h₄⟩ := Runs.bind_inv h₄
  obtain ⟨rfl, hs6⟩ := runs_strongUpdate_deref hsu
  subst s₆
  simp only [Bool.false_eq_true, if_false, Bool.false_and] at h₄
  obtain ⟨_, s₇, b₈, hp1, h₅⟩ := Runs.bind_inv h₄
  obtain ⟨-, hs7⟩ := runs_pure_inv hp1
  subst s₇
  obtain ⟨Td0, s₈, b₉, hp2, h₆⟩ := Runs.bind_inv h₅
  obtain ⟨rfl, hs8⟩ := runs_pure_inv hp2
  subst s₈
  obtain ⟨⟨v₀, T₀⟩, st₁, bh₁, hru, h₇⟩ := Runs.bind_inv h₆
  -- D115: `u`'s value held as a temporary at its type
  obtain ⟨_, sT, bT, hpu, h₇⟩ := Runs.bind_inv h₇
  have hsT := runs_pushTemp_inv hpu
  subst hsT
  simp only [Bool.false_and, Bool.and_false, Bool.not_false, Bool.and_self, Bool.false_eq_true, if_false,
    if_true] at h₇
  obtain ⟨lf, s₉, b₁₀, hlf, h₈⟩ := Runs.bind_inv h₇
  obtain ⟨rfl, hs9⟩ := runs_lentLeafCheck_deref hlf
  subst s₉
  simp only [Bool.false_eq_true, if_false] at h₈
  obtain ⟨A, s₁₀, b₁₁, hpA, h₉⟩ := Runs.bind_inv h₈
  obtain ⟨rfl, hs10⟩ := runs_pure_inv hpA
  subst s₁₀
  obtain ⟨_, sE, b₁₂, hex, h₁₀⟩ := Runs.bind_inv h₉
  obtain ⟨_, s₁₁, b₁₃, hap, h₁₁⟩ := Runs.bind_inv h₁₀
  obtain ⟨_, s₁₂, b₁₄, how, h₁₂⟩ := Runs.bind_inv h₁₁
  obtain ⟨hvt, hs12⟩ := runs_pure_inv h₁₂
  subst s₁₂
  simp only [Prod.mk.injEq] at hvt
  obtain ⟨rfl, rfl⟩ := hvt
  have hg : TablesGrow st₁ st' :=
    (TablesGrow.withTempT _ _ _).trans ((Runs.grows (grows_expectTy _ _ _ _) hex).trans
      ((Runs.grows (growsM_of_growsIn fun _ => (machineGrows n).assignPlace _) hap).trans
        (Runs.grows (growsM_of_growsIn fun _ => (machineGrows n).openWrite _) how)))
  refine ⟨st, st₁, hu, v₀, T₀, b₉, Kern.rfl' _, hm, htn, htd, hru, DecTab.back hD hg, rfl, rfl, ?_, ?_⟩
  · -- `y` moved (its borrow ended by `u`): the write's `content (*y)` errs
    intro f j bd hpos hb hbot
    obtain ⟨hq, -⟩ := expectTy_inv hex
    have hposT : ckVarPos (st₁.withTempT v₀ T₀).env i = some (.bind f j) := by
      rw [withTempT_env, ckVarPos_pushTempTyE]; exact hpos
    have hposE : ckVarPos sE.env i = some (.bind f j) := by
      rw [← ckVarPos_erase, ← hq.env, ckVarPos_erase]; exact hposT
    have hvE : valAt sE.env (.bind f j) = .bot := by
      rw [← valAt_erase, ← hq.env, valAt_erase, valAt_withTempT', valAt_pushTempE_bind]
      obtain ⟨bd', hb', hv'⟩ := lookup_of_bindPos (ckVarPos_mem _ hpos)
      rw [hb] at hb'; cases hb'; rw [hv', hbot]
    exact noRun_assignPlace_deref_bot hposE hvE hap
  intro f j bd l w hpos hb hbv hwn
  obtain ⟨hq, hme⟩ := expectTy_inv hex
  have hnT : DerefAt (st₁.withTempT v₀ T₀) i f j bd l w := DerefAt.withTempT ⟨hpos, hb, hbv, hwn⟩ v₀ T₀
  have hnE : DerefAt sE i f j bd l w :=
    ⟨by rw [← ckVarPos_erase, ← hq.env, ckVarPos_erase]; exact hnT.pos,
     by rw [← lookup_erase, ← hq.env, lookup_erase]; exact hnT.bind, hbv, hwn⟩
  have hne : 0 < st₁.env.size := by
    obtain ⟨fr, b', hf, -⟩ := mem_allPos_bind st₁.env f j (ckVarPos_mem _ hpos)
    exact Nat.lt_of_le_of_lt (Nat.zero_le f) (Array.getElem?_eq_some_iff.mp hf).1
  have htopT : ((st₁.withTempT v₀ T₀).env[(st₁.withTempT v₀ T₀).env.size - 1]!).temps.back? = some v₀ := by
    rw [withTempT_env]
    have hs : (Env.pushTempTyE st₁.env v₀ T₀).size = st₁.env.size := by simp [Env.pushTempTyE]
    rw [hs]
    simp only [Env.pushTempTyE, getElem!_def, Array.getElem?_modify, if_true,
      Array.getElem?_eq_getElem (show st₁.env.size - 1 < st₁.env.size by omega), Option.map_some,
      Array.back?_push]
  have htopE : (sE.env[sE.env.size - 1]!).temps.back? = some v₀ := by
    have hs : sE.env.size = (st₁.withTempT v₀ T₀).env.size := by rw [← Env.erase_size, ← hq.env, Env.erase_size]
    rw [hs, ← temps_erase, ← hq.env, temps_erase]; exact htopT
  obtain ⟨X, rfl⟩ := runs_assignPlace_deref hnE htopE hap
  have := runs_openWrite_deref how
  subst this
  have hn₂ := hnE.popTempE
  have henv : st₁.env.erase = (Env.popTempE sE.env).erase := by
    rw [erase_popTempE_congr hq.env.symm, withTempT_env, popTempE_pushTempTyE]
  refine ⟨{ sE with env := Env.popTempE sE.env },
    ⟨henv, hq.globals, hq.inds, hq.refs, hq.etaRefs, hq.goal, hq.neutrals, hq.liveScope, hq.nextLoan, hq.absSize,
      hq.absTy⟩,
    fun hT => ?_, ⟨hme.headEval, hme.copying, hme.inPlace, hme.erased⟩, hn₂.pos, hn₂.bind,
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩⟩
  have hsE : sE = st₁.withTempT v₀ T₀ := by
    cases T₀ with
    | none => exact runs_expectTy_none' hex
    | some T₀ => exact runs_expectTy_of_beq (hT T₀ rfl) hex
  subst hsE
  have e : ({ st₁.withTempT v₀ T₀ with env := Env.popTempE (st₁.withTempT v₀ T₀).env } : MState) = st₁ := by
    rw [withTempT_env, popTempE_pushTempTyE]; rfl
  rw [e]; exact fun _ _ h => h


#print axioms assignVarInv
#print axioms assignDerefInvF

end Ochr.Meaning.Steps.Machine
