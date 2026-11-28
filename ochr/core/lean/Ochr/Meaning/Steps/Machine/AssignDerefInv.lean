import Ochr.Meaning.Steps.Machine.VarEndInv
import Ochr.Meaning.Steps.Machine.InvShape
import Ochr.Meaning.Steps.Machine.HintKeep

/-!
# `AssignDerefInv`: the write through a borrow variable (`*y := u`; machine lane)

The run (`Machine.evalCore`'s `.assign`, `p = *y`): `lentProofAssign` (none: `*y` is no field),
the hint and `Tp0` (`placeType?` of `*y`: the stored `&Nat`'s content type `Nat`, no state change),
`strongUpdate` (false: no field), `u`'s run, `lentLeafCheck` (false: no field), `expectTy` of `u`'s
type against `Nat` (quiet), `assignPlace` (a temporary pushed, the accesses at `*y`, which end
nothing where `y ↦ borrow_l w` with `w` a number, the old content `w` checked and dropped (no borrow,
no loan), the temporary popped, `y ↦ borrow_l v₀`), `openWrite` (no field prefix: nothing).
-/

namespace Ochr.Meaning.Steps.Machine

open Ochr Ochr.Meaning Ochr.Meaning.Steps Ochr.Meaning.DecideScope Ochr.Meaning.Steps.Slice
open Ochr.Meaning.Steps.Form

/-- The setting of the write: the variable `i` names the binding `bd` at `(f, j)`, holding `borrow_l w`
with `w` a number. -/
structure DerefAt (st : MState) (i f j : Nat) (bd : Binding) (l : Nat) (w : Value) : Prop where
  pos : ckVarPos st.env i = some (.bind f j)
  bind : st.env[f]?.bind (fun fr : Frame => fr.binds[j]?) = some bd
  val : bd.val = .borrow l w
  num : w.Num

section
variable {st : MState} {i f j : Nat} {bd : Binding} {l : Nat} {w : Value}

theorem DerefAt.valAt (h : DerefAt st i f j bd l w) : valAt st.env (.bind f j) = .borrow l w := by
  show (st.env[f]!).binds[j]!.val = _
  rw [binds_get! h.bind, h.val]

theorem withTempT_env (st : MState) (v : Value) (T : Option Value) :
    (st.withTempT v T).env = Env.pushTempTyE st.env v T := rfl

theorem binds_pushTempTyE (E : Env) (v : Value) (T : Option Value) (f i : Nat) :
    (Env.pushTempTyE E v T)[f]?.bind (fun fr : Frame => fr.binds[i]?) = E[f]?.bind (fun fr : Frame => fr.binds[i]?) := by
  simp only [Env.pushTempTyE, Array.getElem?_modify]
  split <;> cases E[f]? <;> rfl

theorem ckVarPos_pushTempTyE (E : Env) (v : Value) (T : Option Value) (i : Nat) :
    ckVarPos (Env.pushTempTyE E v T) i = ckVarPos E i := by
  have hs : (Env.pushTempTyE E v T).size = E.size := by simp [Env.pushTempTyE]
  have hb : (Env.pushTempTyE E v T)[E.size - 1]!.binds = E[E.size - 1]!.binds := by
    simp only [Env.pushTempTyE, getElem!_def, Array.getElem?_modify, if_true]
    cases E[E.size - 1]? <;> rfl
  unfold ckVarPos; rw [hs, hb]

theorem DerefAt.withTempT (h : DerefAt st i f j bd l w) (v : Value) (T : Option Value) :
    DerefAt (st.withTempT v T) i f j bd l w :=
  ⟨by rw [withTempT_env, ckVarPos_pushTempTyE]; exact h.pos,
   by rw [withTempT_env, binds_pushTempTyE]; exact h.bind, h.val, h.num⟩

theorem Value.Num.borrowBelowRoot_false {v : Value} (h : v.Num) : v.borrowBelowRoot = false := by
  have hb : v.hasBorrow = false := Value.Num.anyAtom h rfl (fun _ => rfl)
  cases h with
  | zero => exact hb
  | succ _ => exact hb

theorem runs_content_deref (hn : DerefAt st i f j bd l w) {st' : MState} {b : Nat} {v : Value}
    (h : Runs (content (.deref (.var i))) st b v st') : v = w ∧ st' = st := by
  unfold content at h
  obtain ⟨pos, s₁, b₁, hv, h₁⟩ := Runs.bind_inv h
  obtain ⟨rfl, hp⟩ := runs_varPos_inv hv
  rw [hn.pos] at hp; cases hp
  obtain ⟨x, s₂, b₂, hg, h₂⟩ := Runs.bind_inv h₁
  obtain ⟨rfl, rfl⟩ := Steps.runs_getAt_inv hg
  simp only [Place.steps, List.nil_append] at h₂
  rw [hn.valAt] at h₂
  simp only [Value.follow, stepV, Option.bind_some] at h₂
  obtain ⟨rfl, rfl⟩ := runs_pure_inv h₂
  exact ⟨rfl, rfl⟩

theorem firstLiveLoanOnPath_deref_num {env : Env} (hw : w.Num) :
    firstLiveLoanOnPath env (.borrow l w) [.deref] = none := by
  simp [firstLiveLoanOnPath, stepV, firstLiveLoanOnPath_num hw]

theorem runs_accessPath_deref (hn : DerefAt st i f j bd l w) {n : Nat} {st' : MState} {b : Nat} {u : Unit}
    (h : Runs (accessPath n (.deref (.var i))) st b u st') : st' = st := by
  cases n with
  | zero => unfold accessPath at h; simp only [runs_exhausted_iff] at h
  | succ k =>
    unfold accessPath at h
    simp only [Place.steps, List.nil_append] at h
    rw [runs_get_bind] at h
    obtain ⟨pos, s₁, b₁, hv, h₁⟩ := Runs.bind_inv h
    obtain ⟨rfl, hp⟩ := runs_varPos_inv hv
    rw [hn.pos] at hp; cases hp
    rw [hn.valAt, firstLiveLoanOnPath_deref_num hn.num] at h₁
    exact (runs_pure_inv h₁).2

theorem runs_accessInside_deref (hn : DerefAt st i f j bd l w) {n : Nat} {o : Bool} {st' : MState} {b : Nat}
    {u : Unit} (h : Runs (accessInside n (.deref (.var i)) o) st b u st') : st' = st := by
  cases n with
  | zero => unfold accessInside at h; simp only [runs_exhausted_iff] at h
  | succ k =>
    unfold accessInside at h
    obtain ⟨v, s₁, b₁, hc, h₁⟩ := Runs.bind_inv h
    obtain ⟨e, rfl⟩ := runs_content_deref hn hc
    rw [e] at h₁
    have h1 : liveOwnedLoansIn s₁.env w = [] := by
      simp [liveOwnedLoansIn, Value.Num.ownedLoans_nil hn.num]
    have h2 : liveLoansIn s₁.env w = [] := liveLoansIn_nil (Value.Num.loans_nil hn.num)
    cases o <;> (peel h₁; simp only [h1, h2, Bool.false_eq_true, if_false, if_true, List.isEmpty_nil] at h₁; peel h₁; exact (runs_pure_inv h₁).2)

theorem binds_popTempE (E : Env) (f i : Nat) :
    (Env.popTempE E)[f]?.bind (fun fr : Frame => fr.binds[i]?) = E[f]?.bind (fun fr : Frame => fr.binds[i]?) := by
  simp only [Env.popTempE, Array.getElem?_modify]
  split <;> cases E[f]? <;> rfl

theorem ckVarPos_popTempE (E : Env) (i : Nat) : ckVarPos (Env.popTempE E) i = ckVarPos E i := by
  have hs : (Env.popTempE E).size = E.size := by simp [Env.popTempE]
  have hb : (Env.popTempE E)[E.size - 1]!.binds = E[E.size - 1]!.binds := by
    simp only [Env.popTempE, getElem!_def, Array.getElem?_modify, if_true]
    cases E[E.size - 1]? <;> rfl
  unfold ckVarPos; rw [hs, hb]

theorem DerefAt.popTempE (h : DerefAt st i f j bd l w) :
    DerefAt { st with env := Env.popTempE st.env } i f j bd l w :=
  ⟨by show ckVarPos (Env.popTempE st.env) i = _; rw [ckVarPos_popTempE]; exact h.pos,
   by show (Env.popTempE st.env)[f]?.bind _ = _; rw [binds_popTempE]; exact h.bind, h.val, h.num⟩

/-- The temporaries' types forgotten, a pop is a pop of the forgotten environment. -/
theorem erase_popTempE (e : Env) :
    (Env.popTempE e).erase = e.erase.modify (e.erase.size - 1) fun fr => { fr with temps := fr.temps.pop } := by
  apply Array.ext_getElem?
  intro f
  simp only [Env.erase_get?, Env.popTempE, Array.getElem?_modify, Env.erase_size]
  split <;> cases e[f]? <;> rfl

theorem erase_popTempE_congr {e e' : Env} (h : e.erase = e'.erase) : (Env.popTempE e).erase = (Env.popTempE e').erase := by
  rw [erase_popTempE, erase_popTempE, h]

/-- [Assign] at `*y` (D115: the value is the top temporary, pushed by the caller): the accesses end
nothing, the old content `w` (a number) is dropped, the temporary popped and written at `[*]`. -/
theorem runs_assignPlace_deref (hn : DerefAt st i f j bd l w) {k : Nat} {v₀ : Value}
    (htop : (st.env[st.env.size - 1]!).temps.back? = some v₀)
    {st' : MState} {b : Nat} (h : Runs (assignPlace k (.deref (.var i))) st b () st') :
    ∃ X, st' = { st with env := Env.setAtE (Env.popTempE st.env) (.bind f j) (.borrow l v₀), placeLog := X } := by
  cases k with
  | zero => unfold assignPlace at h; simp only [runs_exhausted_iff] at h
  | succ m =>
    unfold assignPlace at h
    obtain ⟨_, s₂, b₂, ha, h₂⟩ := Runs.bind_inv h
    clear h
    have := runs_accessPath_deref hn ha
    subst this
    obtain ⟨_, s₃, b₃, hai, h₃⟩ := Runs.bind_inv h₂
    clear h₂
    have := runs_accessInside_deref hn hai
    subst this
    obtain ⟨old, s₄, b₄, hc, h₄⟩ := Runs.bind_inv h₃
    clear h₃
    obtain ⟨e, rfl⟩ := runs_content_deref hn hc
    rw [e] at h₄
    obtain ⟨_, s₅, b₅, hu, h₅⟩ := Runs.bind_inv h₄
    clear h₄
    have := runs_unsizedCheck_num hn.num hu
    subst this
    rw [Value.Num.borrowBelowRoot_false hn.num] at h₅
    have hx : ∀ x : Value, x.Num → x = .zero ∨ ∃ w', x = .succ w' := fun x hx => by
      cases hx with
      | zero => exact .inl rfl
      | succ _ => exact .inr ⟨_, rfl⟩
    have hll : ∀ E : Env, liveLoansIn E w = [] := fun _ => liveLoansIn_nil (Value.Num.loans_nil hn.num)
    simp only [Bool.false_eq_true, if_false] at h₅
    have hn' := hn.popTempE
    rcases hx _ hn.num with e | ⟨w', e⟩ <;> rw [e] at h₅ hll <;>
      simp only [runs_get_bind, hll, List.isEmpty_nil, Bool.not_true, Bool.false_eq_true, if_false] at h₅ <;>
    (obtain ⟨v', s₆, b₆, hp, h₆⟩ := Runs.bind_inv h₅
     obtain ⟨htop', rfl⟩ := runs_popTemp_inv hp
     have hv' : v' = v₀ := by rw [htop] at htop'; exact (Option.some.inj htop').symm
     obtain ⟨_, s₇, b₇, hle, h₇⟩ := Runs.bind_inv h₆
     obtain ⟨X, rfl⟩ := runs_logEffect_inv hle
     obtain ⟨pos, v'', hp', hu', rfl⟩ := runs_setPlace_inv h₇
     simp only [Place.steps, List.nil_append] at hp' hu'
     rw [hn'.pos] at hp'; cases hp'
     rw [hn'.valAt] at hu'
     simp only [Value.updAt, Option.map_some, Option.some.injEq] at hu'
     subst hu' hv'
     exact ⟨X, rfl⟩)

theorem runs_openWrite_deref {k i : Nat} {st st' : MState} {b : Nat} {u : Unit}
    (h : Runs (openWrite k (.deref (.var i))) st b u st') : st' = st := by
  cases k with
  | zero => unfold openWrite at h; simp only [runs_exhausted_iff] at h
  | succ m =>
    unfold openWrite at h
    simp only [Place.fieldPrefixes, List.forIn_nil] at h
    exact (runs_pure_inv h).2

theorem runs_lentProofAssign_deref {k : Nat} {q : Place} {u : Term} {st st' : MState} {b : Nat}
    {r : Option (Value × Option Value)} (h : Runs (lentProofAssign k (.deref q) u) st b r st') : r = none ∧ st' = st := by
  cases k with
  | zero => unfold lentProofAssign at h; simp only [runs_exhausted_iff] at h
  | succ m => unfold lentProofAssign at h; exact runs_pure_inv h

theorem runs_lentLeafCheck_deref {k : Nat} {q : Place} {Tv : Option Value} {st st' : MState} {b : Nat} {r : Bool}
    (h : Runs (lentLeafCheck k (.deref q) Tv) st b r st') : r = false ∧ st' = st := by
  cases k with
  | zero => unfold lentLeafCheck at h; simp only [runs_exhausted_iff] at h
  | succ m => unfold lentLeafCheck at h; exact runs_pure_inv h

theorem runs_strongUpdate_deref {q : Place} {st st' : MState} {b : Nat} {r : Bool}
    (h : Runs (strongUpdate (.deref q)) st b r st') : r = false ∧ st' = st := by
  unfold strongUpdate at h; exact runs_pure_inv h

/-- The variable's place reads the stored type every binding the variable may name has. -/
theorem runs_placeTypeQ_var_gen {n i : Nat} {T : Value} {st st' : MState} {b : Nat} {r : Option Value}
    (hty : ∀ f j bd, ckVarPos st.env i = some (.bind f j) → st.env[f]?.bind (fun fr : Frame => fr.binds[j]?) = some bd →
      bd.ty = some T)
    (h : Runs (placeType? n (.var i)) st b r st') : r = some T ∧ st' = st := by
  obtain ⟨p, hp⟩ := runs_placeTypeQ_var_pos h
  have hm := ckVarPos_mem _ hp
  obtain ⟨f, j, rfl⟩ : ∃ f j, p = .bind f j := by
    unfold ckVarPos at hp; split at hp <;> cases hp; exact ⟨_, _, rfl⟩
  obtain ⟨fr, bd, hf, hbd⟩ := mem_allPos_bind st.env f j hm
  have hb : st.env[f]?.bind (fun fr : Frame => fr.binds[j]?) = some bd := by rw [hf]; exact hbd
  exact runs_placeTypeQ_var hp hb (hty f j bd hp hb) h

theorem runs_placeTypeQ_deref {n i : Nat} {A : Value} {st st' : MState} {b : Nat} {r : Option Value}
    (hty : ∀ f j bd, ckVarPos st.env i = some (.bind f j) → st.env[f]?.bind (fun fr : Frame => fr.binds[j]?) = some bd →
      bd.ty = some (.tRef A))
    (h : Runs (placeType? n (.deref (.var i))) st b r st') : r = some A ∧ st' = st := by
  cases n with
  | zero => unfold placeType? at h; simp only [runs_exhausted_iff] at h
  | succ k =>
    unfold placeType? at h
    obtain ⟨o, s₁, b₁, hq, h₁⟩ := Runs.bind_inv h
    obtain ⟨rfl, rfl⟩ := runs_placeTypeQ_var_gen hty hq
    exact runs_pure_inv h₁

theorem runs_projIn_deref_var {n i : Nat} {st st' : MState} {b : Nat} {o : Option (Place × Nat × (Place → Place))}
    (h : Runs (projIn n (.deref (.var i))) st b o st') : o = none ∧ st' = st := by
  cases n with
  | zero => unfold projIn at h; simp only [runs_exhausted_iff] at h
  | succ k =>
    unfold projIn at h
    obtain ⟨o', s₁, b₁, hq, h₁⟩ := Runs.bind_inv h
    obtain ⟨rfl, rfl⟩ := runs_projIn_var hq
    obtain ⟨rfl, rfl⟩ := runs_pure_inv h₁
    exact ⟨rfl, rfl⟩

theorem runs_expectTy_none' {n : Nat} {w : String} {A : Value} {st st' : MState} {b : Nat}
    (h : Runs (Ochr.expectTy n w none A) st b () st') : st' = st := by
  cases n with
  | zero => unfold Ochr.expectTy at h; simp only [runs_exhausted_iff] at h
  | succ k => unfold Ochr.expectTy at h; peel h; exact (runs_pure_inv h).2

/-- A conditional whose branches share their continuation (a `do` join point the elaborator inlined):
the condition need not be named, which for a `matches` test in a large hypothesis is costly. -/
theorem Runs.ite_bind_inv {α β : Type} {c : Prop} [Decidable c] {A B : M α} {K : α → M β} {s s' : MState}
    {b : Nat} {r : β} (h : Runs (if c then A >>= K else B >>= K) s b r s') :
    ∃ a s₁ b₁, (Runs A s b a s₁ ∨ Runs B s b a s₁) ∧ Runs (K a) s₁ b₁ r s' := by
  by_cases hc : c
  · rw [if_pos hc] at h; obtain ⟨a, s₁, b₁, h1, h2⟩ := Runs.bind_inv h; exact ⟨a, s₁, b₁, .inl h1, h2⟩
  · rw [if_neg hc] at h; obtain ⟨a, s₁, b₁, h1, h2⟩ := Runs.bind_inv h; exact ⟨a, s₁, b₁, .inr h1, h2⟩

end

set_option maxHeartbeats 4000000 in
/-- **`AssignDerefInv`, proved** (the form restated by the machine lane, 2026-11-21). -/
theorem assignDerefInv : AssignDerefInv := by
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
  refine ⟨st, st₁, hu, v₀, T₀, b₉, Kern.rfl' _, hm, htn, htd, hru, DecTab.back hD hg, rfl, rfl, ?_⟩
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
      hq.absTy, hq.recStack⟩,
    fun hT => ?_, ⟨hme.headEval, hme.copying, hme.inPlace, hme.erased⟩, hn₂.pos, hn₂.bind,
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩⟩
  have hsE : sE = st₁.withTempT v₀ T₀ := by
    cases T₀ with
    | none => exact runs_expectTy_none' hex
    | some T₀ => exact runs_expectTy_of_beq (hT T₀ rfl) hex
  subst hsE
  have e : ({ st₁.withTempT v₀ T₀ with env := Env.popTempE (st₁.withTempT v₀ T₀).env } : MState) = st₁ := by
    rw [withTempT_env, popTempE_pushTempTyE]; rfl
  rw [e]; exact fun _ _ h => h

end Ochr.Meaning.Steps.Machine
