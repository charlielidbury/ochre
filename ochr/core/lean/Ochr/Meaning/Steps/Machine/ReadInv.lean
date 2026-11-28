import Ochr.Meaning.Steps.Machine.StepInv
import Ochr.Meaning.Steps.DropRuns

/-!
# The column's read of a variable holding a number (`VarNumInv`), proved

`evalCore` of `.place (.var i)` where the variable names a binding holding a number with a stored
type: the [Proj] pre-pass finds no field step (`projIn`), the type is the binding's stored type
(`placeType`, `bindTy?`, `tyAt`), the typed run's [Repack] does nothing (a number has no dependent
constructor: `hasDependent` is false), and `readPlace` (`runs_readPlace_num`): the [Access] ends
nothing (`firstLiveLoanOnPath` meets no loan on a number's empty path; a number holds no loan), the
checks pass and change nothing, and the read copies (the state as it was) or moves (`⊥` at the
binding, and the move log) as the copy decision says, which the table aligned at the entry gives
(`decTab_placeDecl_at`, `DecTab.copy`).
-/

namespace Ochr.Meaning.Steps.Machine

open Ochr Ochr.Meaning Ochr.Meaning.Steps Ochr.Meaning.DecideScope Ochr.Meaning.Steps.Slice
open Ochr.Meaning.Steps.Form

theorem liveLoansIn_nil {env : Env} {v : Value} (h : v.loans = []) : liveLoansIn env v = [] := by
  simp [liveLoansIn, h]

theorem Value.Num.outerLoans_nil {v : Value} (h : v.Num) : v.outerLoans = [] := by
  induction h with
  | zero => rfl
  | succ _ ih => simpa [Value.outerLoans] using ih

theorem Value.Num.loans_nil {v : Value} (h : v.Num) : v.loans = [] := by
  induction h with
  | zero => rfl
  | succ _ ih => simpa [Value.loans] using ih

theorem Value.Num.ownedLoans_nil {v : Value} (h : v.Num) : v.ownedLoans = [] := by
  induction h with
  | zero => rfl
  | succ _ ih => simpa [Value.ownedLoans] using ih

theorem Value.Num.ne_bot {v : Value} (h : v.Num) : v ≠ .bot := by cases h <;> intro e <;> cases e

theorem Value.Num.beq_proof {v : Value} (h : v.Num) : (v == Value.proof) = false := by
  cases e : (v == Value.proof)
  · rfl
  · have := eq_proof_of_beq e; subst this; cases h

theorem Value.Num.hasHole {v : Value} (h : v.Num) : v.hasHole = false := by
  unfold Value.hasHole
  induction h with
  | zero => rfl
  | succ _ ih => simpa [Value.anyAtom, BEq.beq, Value.beq] using ih

theorem firstLiveLoanOnPath_num {env : Env} {v : Value} (h : v.Num) : firstLiveLoanOnPath env v [] = none := by
  cases h <;> simp [firstLiveLoanOnPath]

theorem runs_hasDependent_num {v : Value} (hv : v.Num) {st st' : MState} {b : Nat} {r : Bool}
    (h : Runs (hasDependent v) st b r st') : r = false ∧ st' = st := by
  induction hv generalizing b r with
  | zero => unfold hasDependent at h; exact runs_pure_inv h
  | succ _ ih => unfold hasDependent at h; exact ih h

/-- The binding the checker's variable `i` names, read at a position (`env[f]!.binds[j]!`). -/
theorem binds_get! {env : Env} {f j : Nat} {b : Binding} (hb : env[f]?.bind (fun fr : Frame => fr.binds[j]?) = some b) :
    (env[f]!).binds[j]! = b := by
  rcases hf : env[f]? with _ | fr
  · rw [hf] at hb; cases hb
  · rw [hf] at hb
    simp only [Option.bind_some] at hb
    have e1 : env[f]! = fr := by rw [getElem!_def, hf]
    rw [e1, getElem!_def, hb]

theorem runs_projIn_var {n i : Nat} {st st' : MState} {b : Nat} {o : Option (Place × Nat × (Place → Place))}
    (h : Runs (projIn n (.var i)) st b o st') : o = none ∧ st' = st := by
  cases n with
  | zero => unfold projIn at h; simp only [runs_exhausted_iff] at h
  | succ k => unfold projIn at h; exact runs_pure_inv h

theorem Runs.log_inv {g : Array LogEntry → Array LogEntry} {st st' : MState} {b : Nat} {u : PUnit}
    (h : Runs (modifyThe (Array LogEntry) g) st b u st') : st' = st := by
  obtain ⟨L, left, log, h⟩ := h
  have e : runMachineL (modifyThe (Array LogEntry) g : M PUnit) st b L = (.ok () st, b, g L) := rfl
  rw [e] at h
  simp only [Prod.mk.injEq, Outcome.ok.injEq] at h
  exact h.1.2.symm

theorem runs_tyAt_inv {f j : Nat} {st st' : MState} {b : Nat} {T? : Option Value}
    (h : Runs (tyAt (.bind f j)) st b T? st') : T? = ((st.env[f]!).binds[j]!).ty ∧ st' = st := by
  unfold tyAt at h; peel h; exact runs_pure_inv h

/-- The variable's place reads the binding's stored type, where it has one. -/
theorem runs_placeTypeQ_var {n i f j : Nat} {bd : Binding} {T : Value} {st st' : MState} {b : Nat}
    {r : Option Value} (hpos : ckVarPos st.env i = some (.bind f j))
    (hb : st.env[f]?.bind (fun fr : Frame => fr.binds[j]?) = some bd) (hT : bd.ty = some T)
    (h : Runs (placeType? n (.var i)) st b r st') : r = some T ∧ st' = st := by
  cases n with
  | zero => unfold placeType? at h; simp only [runs_exhausted_iff] at h
  | succ k =>
    unfold placeType? at h
    peel h
    obtain ⟨pos, s₁, b₁, hv, h₁⟩ := Runs.bind_inv h
    obtain ⟨rfl, hp⟩ := runs_varPos_inv hv
    rw [hpos] at hp; cases hp
    cases k with
    | zero => unfold bindTy? at h₁; simp only [runs_exhausted_iff] at h₁
    | succ m =>
      unfold bindTy? at h₁
      peel h₁
      obtain ⟨T?, s₂, b₂, ht, h₂⟩ := Runs.bind_inv h₁
      obtain ⟨rfl, rfl⟩ := runs_tyAt_inv ht
      rw [binds_get! hb, hT] at h₂
      peel h₂
      exact runs_pure_inv h₂

theorem runs_placeType_var {n i f j : Nat} {bd : Binding} {T : Value} {st st' : MState} {b : Nat}
    {r : Value} (hpos : ckVarPos st.env i = some (.bind f j))
    (hb : st.env[f]?.bind (fun fr : Frame => fr.binds[j]?) = some bd) (hT : bd.ty = some T)
    (h : Runs (placeType n (.var i)) st b r st') : r = T ∧ st' = st := by
  cases n with
  | zero => unfold placeType at h; simp only [runs_exhausted_iff] at h
  | succ k =>
    unfold placeType at h
    peel h
    obtain ⟨o, s₁, b₁, hq, h₁⟩ := Runs.bind_inv h
    obtain ⟨rfl, rfl⟩ := runs_placeTypeQ_var hpos hb hT hq
    peel h₁
    exact runs_pure_inv h₁

/-- The setting of the read: the variable `i` names the binding `bd` at `(f, j)`, holding a number. -/
structure NumAt (st : MState) (i f j : Nat) (bd : Binding) : Prop where
  pos : ckVarPos st.env i = some (.bind f j)
  bind : st.env[f]?.bind (fun fr : Frame => fr.binds[j]?) = some bd
  num : bd.val.Num

theorem NumAt.valAt {st : MState} {i f j : Nat} {bd : Binding} (h : NumAt st i f j bd) :
    valAt st.env (.bind f j) = bd.val := by
  show (st.env[f]!).binds[j]!.val = bd.val
  rw [binds_get! h.bind]

theorem runs_content_var {i f j : Nat} {bd : Binding} {st st' : MState} {b : Nat} {v : Value}
    (hn : NumAt st i f j bd) (h : Runs (content (.var i)) st b v st') : v = bd.val ∧ st' = st := by
  unfold content at h
  obtain ⟨pos, s₁, b₁, hv, h₁⟩ := Runs.bind_inv h
  obtain ⟨rfl, hp⟩ := runs_varPos_inv hv
  rw [hn.pos] at hp; cases hp
  obtain ⟨w, s₂, b₂, hg, h₂⟩ := Runs.bind_inv h₁
  obtain ⟨rfl, rfl⟩ := Steps.runs_getAt_inv hg
  simp only [Place.steps, Value.follow] at h₂
  obtain ⟨rfl, rfl⟩ := runs_pure_inv h₂
  exact ⟨hn.valAt, rfl⟩

theorem runs_repackCheck_num {k : Nat} {w : String} {x T : Value} (hnum : x.Num) {st st' : MState} {b : Nat}
    (h₂ : Runs (repackCheck k w x T) st b () st') : st' = st := by
  cases k with
  | zero => unfold repackCheck at h₂; simp only [runs_exhausted_iff] at h₂
  | succ k' =>
    unfold repackCheck at h₂
    cases hnum with
    | zero =>
      peel h₂
      obtain ⟨d, s₃, b₃, hd, h₃⟩ := Runs.bind_inv h₂
      obtain ⟨rfl, rfl⟩ := runs_hasDependent_num .zero hd
      simp only [Bool.not_false, if_true] at h₃
      exact (runs_pure_inv h₃).2
    | succ hw =>
      peel h₂
      obtain ⟨d, s₃, b₃, hd, h₃⟩ := Runs.bind_inv h₂
      obtain ⟨rfl, rfl⟩ := runs_hasDependent_num (.succ hw) hd
      simp only [Bool.not_false, if_true] at h₃
      exact (runs_pure_inv h₃).2

theorem runs_repackAt_num {n i f j : Nat} {bd : Binding} {T : Value} {w : String} {st st' : MState} {b : Nat}
    (hn : NumAt st i f j bd) (h : Runs (repackAt n (.var i) T w) st b () st') : st' = st := by
  cases n with
  | zero => unfold repackAt at h; simp only [runs_exhausted_iff] at h
  | succ k =>
    unfold repackAt at h
    obtain ⟨o, s₁, b₁, hc, h₁⟩ := Runs.bind_inv h
    obtain ⟨rfl, pos, hp, rfl⟩ := runs_content?_inv hc
    simp only [Place.steps] at hp
    rw [hn.pos] at hp; cases hp
    simp only [Place.steps, Value.follow, hn.valAt] at h₁
    rw [if_neg (by have h0 := hn.num; revert h0; generalize bd.val = x; intro h0; cases h0 <;> simp)] at h₁
    obtain ⟨m, s₂, b₂, hm, h₂⟩ := Runs.bind_inv h₁
    obtain ⟨-, rfl⟩ := runs_ppPlace_inv hm
    have hnum := hn.num
    clear h₁ hc hm
    revert h₂
    generalize bd.val = x at hnum ⊢
    intro h₂
    exact runs_repackCheck_num hnum h₂

theorem runs_accessPath_num {n i f j : Nat} {bd : Binding} {st st' : MState} {b : Nat} {u : Unit}
    (hn : NumAt st i f j bd) (h : Runs (accessPath n (.var i)) st b u st') : st' = st := by
  cases n with
  | zero => unfold accessPath at h; simp only [runs_exhausted_iff] at h
  | succ k =>
    unfold accessPath at h
    simp only [Place.steps] at h
    rw [runs_get_bind] at h
    obtain ⟨pos, s₁, b₁, hv, h₁⟩ := Runs.bind_inv h
    obtain ⟨rfl, hp⟩ := runs_varPos_inv hv
    rw [hn.pos] at hp; cases hp
    rw [hn.valAt, firstLiveLoanOnPath_num hn.num] at h₁
    exact (runs_pure_inv h₁).2

theorem runs_accessInside_num {n i f j : Nat} {bd : Binding} {o : Bool} {st st' : MState} {b : Nat} {u : Unit}
    (hn : NumAt st i f j bd) (h : Runs (accessInside n (.var i) o) st b u st') : st' = st := by
  cases n with
  | zero => unfold accessInside at h; simp only [runs_exhausted_iff] at h
  | succ k =>
    unfold accessInside at h
    obtain ⟨v, s₁, b₁, hc, h₁⟩ := Runs.bind_inv h
    obtain ⟨rfl, rfl⟩ := runs_content_var hn hc
    have h1 : liveOwnedLoansIn s₁.env bd.val = [] := by
      simp [liveOwnedLoansIn, Value.Num.ownedLoans_nil hn.num]
    have h2 : liveLoansIn s₁.env bd.val = [] := liveLoansIn_nil (Value.Num.loans_nil hn.num)
    cases o <;> (peel h₁; simp only [h1, h2, Bool.false_eq_true, if_false, if_true, List.isEmpty_nil] at h₁; peel h₁; exact (runs_pure_inv h₁).2)

theorem runs_copyRead_inv {m : Nat} {p : Place} {st st' : MState} {b : Nat} {c : Bool}
    (h : Runs (copyRead m p) st b c st') :
    ∃ k d b₁ b₂, m = k + 1 ∧ Runs (withLive true (Ochr.placeDecl k [] p)) st b₁ d st ∧ Runs (declCopy k d) st b₂ c st ∧
      st' = st := by
  cases m with
  | zero => unfold copyRead at h; simp only [runs_exhausted_iff] at h
  | succ k =>
    unfold copyRead at h
    obtain ⟨d, s₁, b₁, hd, h₁⟩ := Runs.bind_inv h
    have hs := runs_placeDecl_keep hd
    subst hs
    have hs' := runs_declCopy_keep h₁
    subst hs'
    exact ⟨k, d, b, b₁, rfl, hd, h₁, rfl⟩

theorem runs_unsizedCheck_num {p : Place} {v : Value} {w : String} (hv : v.Num) {st st' : MState} {b : Nat} {u : Unit}
    (h : Runs (unsizedCheck p v w) st b u st') : st' = st := by
  unfold unsizedCheck atRuntime at h
  cases hv <;> (peel h; split at h <;> (peel h; exact (runs_pure_inv h).2))

theorem runs_isCapture_inv {i f j : Nat} {bd : Binding} {st st' : MState} {b : Nat} {c : Bool}
    (hn : NumAt st i f j bd) (h : Runs (isCapture (.var i)) st b c st') : c = bd.cap ∧ st' = st := by
  unfold isCapture at h
  obtain ⟨pos, s₁, b₁, hv, h₁⟩ := Runs.bind_inv h
  obtain ⟨rfl, hp⟩ := runs_varPos_inv hv
  simp only [Place.root] at hp
  rw [hn.pos] at hp; cases hp
  peel h₁
  obtain ⟨rfl, rfl⟩ := runs_pure_inv h₁
  rw [binds_get! hn.bind]; exact ⟨rfl, rfl⟩

set_option maxHeartbeats 4000000 in
/-- **The read of a variable holding a number**: its value; the access, the checks and the copy
decision change nothing; a copy leaves the state, a move writes `⊥` at the binding (and the move log). -/
theorem runs_readPlace_num {n i f j : Nat} {bd : Binding} {st st' : MState} {b : Nat} {v : Value}
    (hn : NumAt st i f j bd) (hip : st.inPlace = false) (hcp : st.copying = false)
    (h : Runs (Ochr.readPlace n (.var i)) st b v st') :
    v = bd.val ∧ ∃ k d c b₁ b₂, Runs (withLive true (Ochr.placeDecl k [] (.var i))) st b₁ d st ∧
      Runs (declCopy k d) st b₂ c st ∧ (c = true → st' = st) ∧
      (c = false → ∃ X, st' = { st with env := Env.setAtE st.env (.bind f j) .bot, placeLog := X }) := by
  cases n with
  | zero => unfold Ochr.readPlace at h; simp only [runs_exhausted_iff] at h
  | succ m =>
    unfold Ochr.readPlace at h
    obtain ⟨_, s₁, b₁, ha, h₁⟩ := Runs.bind_inv h
    clear h
    have := runs_accessPath_num hn ha
    subst this
    obtain ⟨_, s₂, b₂, hai, h₂⟩ := Runs.bind_inv h₁
    clear h₁
    have := runs_accessInside_num hn hai
    subst this
    obtain ⟨w, s₃, b₃, hc, h₃⟩ := Runs.bind_inv h₂
    clear h₂
    obtain ⟨rfl, rfl⟩ := runs_content_var hn hc
    peel h₃
    rw [Value.Num.outerLoans_nil hn.num] at h₃
    simp only [List.any_nil, Bool.false_eq_true, if_false] at h₃
    peel h₃
    obtain ⟨_, s₄, b₄, hu, h₄⟩ := Runs.bind_inv h₃
    clear h₃
    have := runs_unsizedCheck_num hn.num hu
    subst this
    peel h₄
    simp only [hip, Bool.false_eq_true, if_false] at h₄
    peel h₄
    have hnum := hn.num
    have hx : ∀ x : Value, x.Num → x = .zero ∨ ∃ w, x = .succ w := fun x hx => by
      cases hx with
      | zero => exact .inl rfl
      | succ _ => exact .inr ⟨_, rfl⟩
    have hh : ∀ x, bd.val = x → x.hasHole = false := fun x ex => ex ▸ Value.Num.hasHole hnum
    rcases hx _ hnum with e | ⟨w', e⟩ <;> rw [e] at h₄ <;>
      simp only [BEq.beq, Value.beq, Bool.false_eq_true, if_false, runs_get_bind, hcp] at h₄ <;>
      rw [hh _ e] at h₄ <;> simp only [Bool.false_eq_true, if_false] at h₄ <;>
      (obtain ⟨c, s₅, b₅, hcr, h₅⟩ := Runs.bind_inv h₄
       clear h₄
       obtain ⟨k, d, b₆, b₇, rfl, hpd, hdc, rfl⟩ := runs_copyRead_inv hcr
       cases c with
       | true =>
         simp only [if_true] at h₅
         obtain ⟨_, s₆, b₈, hf, h₆⟩ := Runs.bind_inv h₅
         have := Steps.runs_fire_inv hf
         subst this
         obtain ⟨rfl, rfl⟩ := runs_pure_inv h₆
         exact ⟨e.symm, k, d, true, b₆, b₇, hpd, hdc, fun _ => rfl, fun h => by cases h⟩
       | false =>
         simp only [Bool.false_eq_true, if_false] at h₅
         obtain ⟨cap, s₆, b₈, hic, h₆⟩ := Runs.bind_inv h₅
         obtain ⟨rfl, rfl⟩ := runs_isCapture_inv hn hic
         split at h₆
         · obtain ⟨_, s₇, b₉, hpp, h₇⟩ := Runs.bind_inv h₆
           exact absurd h₇ (fun h => by simp only [runs_err_bind] at h)
         · obtain ⟨_, s₇, b₉, hf, h₇⟩ := Runs.bind_inv h₆
           have := Steps.runs_fire_inv hf
           subst this
           obtain ⟨_, s₈, b₁₀, hle, h₈⟩ := Runs.bind_inv h₇
           obtain ⟨X, rfl⟩ := runs_logEffect_inv hle
           obtain ⟨_, s₉, b₁₁, hsp, h₉⟩ := Runs.bind_inv h₈
           obtain ⟨pos, v', hp, hu', rfl⟩ := runs_setPlace_inv hsp
           simp only [Place.steps] at hp hu'
           rw [hn.pos] at hp; cases hp
           simp only [Value.updAt, Option.some.injEq] at hu'
           subst hu'
           obtain ⟨rfl, rfl⟩ := runs_pure_inv h₉
           exact ⟨e.symm, k, d, false, b₆, b₇, hpd, hdc, (fun h => by cases h), fun _ => ⟨X, rfl⟩⟩)

theorem varNum_read {n i f j : Nat} {bd : Binding} {typed : Bool} {D : Decisions} {s st' : MState} {b' : Nat}
    {T' T? : Option Value} {v : Value} (hn : NumAt s i f j bd) (hm : Mode s) (hDs : DecTab D s)
    (hT' : ∀ T₀, T' = some T₀ → bd.ty = some T₀) (hTs : typed = true → T'.isSome)
    (hr : Runs (do let __do_lift ← Ochr.readPlace n (Place.var i); pure (__do_lift, T')) s b' (v, T?) st') :
    v = bd.val ∧ (∀ T₀, T? = some T₀ → bd.ty = some T₀) ∧ (typed = true → T?.isSome) ∧ Mode st' ∧
      ∃ st₁, Quiet s st₁ ∧ KeepsInv s st₁ ∧
        (D.copy (D.placeDecl (DecideScope.topReadings s) (.var i)) = true → Kern st₁ st') ∧
        (D.copy (D.placeDecl (DecideScope.topReadings s) (.var i)) = false →
          Kern { st₁ with env := Env.setAtE st₁.env (.bind f j) .bot } st') := by
  obtain ⟨w, s₄, b₄, hrp, h₄⟩ := Runs.bind_inv hr
  obtain ⟨hvt, rfl⟩ := runs_pure_inv h₄
  simp only [Prod.mk.injEq] at hvt
  obtain ⟨rfl, rfl⟩ := hvt
  obtain ⟨rfl, k, d, c, b₆, b₇, hpd, hdc, hct, hcf⟩ := runs_readPlace_num hn hm.inPlace hm.copying hrp
  have hd := decTab_placeDecl_at hDs hpd
  have hc := hDs.copy k d c b₇ _ hdc
  rw [hd, hc]
  cases c with
  | true =>
    obtain rfl := hct rfl
    exact ⟨rfl, hT', hTs, hm, _, Quiet.refl _, fun _ _ h => h, fun _ => Kern.rfl' _, (fun e => by cases e)⟩
  | false =>
    obtain ⟨X, rfl⟩ := hcf rfl
    exact ⟨rfl, hT', hTs, ⟨hm.headEval, hm.copying, hm.inPlace, hm.erased⟩, _, Quiet.refl _, fun _ _ h => h, (fun e => by cases e),
      fun _ => ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩⟩

set_option maxHeartbeats 4000000 in
theorem varNumInv : VarNumInv := by
  intro n typed i hint st st' bh v T? f j bd D hm hpos hb hnum hty hD h
  have hDst : DecTab D st := DecTab.back hD (Runs.grows (grows_evalCore _ _ _ _) h)
  have hn : NumAt st i f j bd := ⟨hpos, hb, hnum⟩
  obtain ⟨T, hT⟩ := Option.isSome_iff_exists.mp hty
  unfold Ochr.evalCore at h
  obtain ⟨b₁, h⟩ := Runs.tick_bind h
  obtain ⟨want, s₁, b₂, hw, h⟩ := Runs.bind_inv (runs_get_bind.mp h)
  obtain ⟨hw1, hw2⟩ := runs_wanted_inv hw
  subst hw1 hw2
  simp only [Term.placeOperand?] at h
  obtain ⟨o, s₂, b₃, hp, h₁⟩ := Runs.bind_inv h
  clear h
  obtain ⟨rfl, rfl⟩ := runs_projIn_var hp
  simp only at h₁
  cases typed with
  | true =>
    simp only [if_true] at h₁
    obtain ⟨T', s₃, b₄, hpt, h₂⟩ := Runs.bind_inv h₁
    clear h₁
    obtain ⟨T'', hpt', rfl⟩ := Runs.map_inv hpt
    obtain ⟨rfl, rfl⟩ := runs_placeType_var hpos hb hT hpt'
    try simp only [if_true] at h₂
    obtain ⟨_, s₄, b₅, hra, h₃⟩ := Runs.bind_inv h₂
    have := runs_repackAt_num hn hra
    subst this
    exact varNum_read hn hm hDst (fun T₀ e => by rw [← Option.some.inj e]; exact hT) (fun _ => rfl) h₃
  | false =>
    simp only [Bool.false_eq_true, if_false] at h₁
    split at h₁
    · obtain ⟨T', s₃, b₄, hpt, h₂⟩ := Runs.bind_inv h₁
      clear h₁
      obtain ⟨rfl, rfl⟩ := runs_placeTypeQ_var hpos hb hT hpt
      try simp only [Bool.false_eq_true, if_false, pure_bind] at h₂
      exact varNum_read hn hm hDst (fun T₀ e => by rw [← Option.some.inj e]; exact hT) (fun e => by cases e) h₂
    · try simp only [pure_bind, Bool.false_eq_true, if_false] at h₁
      exact varNum_read hn hm hDst (fun T₀ e => by cases e) (fun e => by cases e) h₁

end Ochr.Meaning.Steps.Machine
