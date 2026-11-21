import Ochr.Meaning.Steps.Machine.SeqInv
import Ochr.Meaning.Steps.Machine.InvSteps

/-!
# `VarEndInv`: the read of `x` lent to `y` (machine lane, in progress)

The run (Machine.lean): `placeType`; `repackAt` at `x ↦ loan_l` (the identity: a loan has no
dependent constructor); `readPlace`: `accessPath` ends `l` (`endTopLoan` → `endBorrow`: `y`'s content
`w` taken, `y ↦ ⊥`, `substEnv (.loan l) w` puts `w` at `x`, `lendEnv (.ended l [])` changes nothing),
the path then free; the rest of the read at `x ↦ w` as `runs_readPlace_num`.
-/

namespace Ochr.Meaning.Steps.Machine

open Ochr Ochr.Meaning Ochr.Meaning.Steps Ochr.Meaning.DecideScope Ochr.Meaning.Steps.Slice

theorem runs_substV_hit {k l : Nat} {r r' : Value} {s s' : MState} {b : Nat}
    (h : Runs (Ochr.substV k (.loan l) r (.loan l)) s b r' s') : r' = r ∧ s' = s := by
  cases k with
  | zero => unfold Ochr.substV at h; simp only [runs_exhausted_iff] at h
  | succ k =>
    unfold Ochr.substV at h
    have e : (Value.loan l).exact (.loan l) = true := by simp [Value.exact]
    simp only [Value.anyAtom, e, Bool.true_or, Bool.not_true, Bool.false_eq_true, if_false, if_true] at h
    exact runs_pure_inv h

theorem runs_substV_miss {k : Nat} {x r v r' : Value} {s s' : MState} {b : Nat}
    (hv : v.anyAtom (·.exact x) = false) (h : Runs (Ochr.substV k x r v) s b r' s') : r' = v ∧ s' = s := by
  cases k with
  | zero => unfold Ochr.substV at h; simp only [runs_exhausted_iff] at h
  | succ k =>
    unfold Ochr.substV at h
    simp only [hv, Bool.not_false, if_true] at h
    exact runs_pure_inv h

theorem runs_lendV_miss {k l : Nat} {to : List Nat} {v r' : Value} {s s' : MState} {b : Nat}
    (hv : (v.anyAtom fun | .loan m | .gloan m _ | .borrow m _ => m == l | _ => false) = false)
    (h : Runs (Ochr.lendV k (.ended l to) v) s b r' s') : r' = v ∧ s' = s := by
  cases k with
  | zero => unfold Ochr.lendV at h; simp only [runs_exhausted_iff] at h
  | succ k =>
    unfold Ochr.lendV at h
    simp only at h
    split at h
    · exact runs_pure_inv h
    · rename_i hc
      exact absurd (by rw [Bool.not_eq_true']; exact hv) hc

theorem runs_getAt_inv {p : Pos} {s s' : MState} {b : Nat} {v : Value} (h : Runs (Ochr.getAt p) s b v s') :
    v = valAt s.env p ∧ s' = s := by
  cases p <;> (unfold Ochr.getAt at h; peel h; obtain ⟨rfl, rfl⟩ := runs_pure_inv h; exact ⟨rfl, rfl⟩)

theorem runs_setAt_inv {p : Pos} {v : Value} {s s' : MState} {b : Nat} {u : Unit} (h : Runs (Ochr.setAt p v) s b u s') :
    s' = { s with env := Env.setAtE s.env p v } := by
  cases p <;> (unfold Ochr.setAt modifyFrame at h; exact runs_modify_inv h)

theorem runs_mapState_two {f : Value → M Value} {s s' : MState} {b : Nat} {p q : Pos} {vp vq : Value}
    (hpos : allPos s.env = [p, q]) (hne : q ≠ p)
    (hp : ∀ st b r st', Runs (f (valAt s.env p)) st b r st' → r = vp ∧ st' = st)
    (hq : ∀ st b r st', Runs (f (valAt s.env q)) st b r st' → r = vq ∧ st' = st)
    (h : Runs (Ochr.mapState f false) s b () s') :
    s' = { s with env := Env.setAtE (Env.setAtE s.env p vp) q vq } := by
  unfold Ochr.mapState at h
  peel h
  rw [hpos] at h
  simp only [List.forIn_cons, List.forIn_nil, Bool.false_eq_true, if_false] at h
  obtain ⟨_, s₀, b₀, hfor, htail⟩ := Runs.bind_inv h
  obtain ⟨x, s₁, b₁, h1, hrest⟩ := Runs.bind_inv hfor
  obtain ⟨v₁, s₂, b₂, hg, h1⟩ := Runs.bind_inv h1
  obtain ⟨e1, e2⟩ := runs_getAt_inv hg
  subst e1; have e2' := e2.symm; subst e2'
  obtain ⟨r₁, s₃, b₃, hf, h1⟩ := Runs.bind_inv h1
  obtain ⟨e3, e4⟩ := hp _ _ _ _ hf
  subst e3; have e4' := e4.symm; subst e4'
  obtain ⟨_, s₄, b₄, hs, h1⟩ := Runs.bind_inv h1
  have e5 := runs_setAt_inv hs; subst e5
  obtain ⟨e6, e7⟩ := runs_pure_inv h1
  subst e6 e7
  simp only at hrest
  obtain ⟨y, t₁, c₁, k1, krest⟩ := Runs.bind_inv hrest
  obtain ⟨u₁, t₂, c₂, kg, k1⟩ := Runs.bind_inv k1
  obtain ⟨e1, e2⟩ := runs_getAt_inv kg
  subst e1; have e2' := e2.symm; subst e2'
  rw [valAt_setAtE_other _ _ _ _ hne] at k1
  obtain ⟨r₂, t₃, c₃, kf, k1⟩ := Runs.bind_inv k1
  obtain ⟨e3, e4⟩ := hq _ _ _ _ kf
  subst e3; have e4' := e4.symm; subst e4'
  obtain ⟨_, t₄, c₄, ks, k1⟩ := Runs.bind_inv k1
  have e5 := runs_setAt_inv ks; subst e5
  obtain ⟨e6, e7⟩ := runs_pure_inv k1
  subst e6 e7
  simp only at krest
  obtain ⟨-, e8⟩ := runs_pure_inv krest
  obtain ⟨-, e9⟩ := runs_pure_inv htail
  rw [e9, e8]

section Two
variable {E : Env} {l : Nat} {w : Value} (hpos : allPos E = [.bind 0 0, .bind 0 1]) (hx : valAt E (.bind 0 0) = .loan l)
  (hy : valAt E (.bind 0 1) = .borrow l w) (hw : w.Num)
include hpos hx hy hw

theorem findBorrow_two : findBorrow E l = some (.bind 0 1) := by
  simp only [findBorrow, hpos, List.find?_cons, hx, hy, Value.holdsBorrow, List.find?_nil]
  simp

end Two

theorem setAtE_same (E : Env) (f i : Nat) (v v' : Value) :
    Env.setAtE (Env.setAtE E (.bind f i) v) (.bind f i) v' = Env.setAtE E (.bind f i) v' := by
  apply _root_.Array.ext_getElem?
  intro k
  simp only [Env.setAtE, Array.getElem?_modify, Array.size_modify]
  split
  · cases E[k]? with
    | none => rfl
    | some fr =>
      simp only [Option.map_some, Option.some.injEq]
      congr 1
      apply _root_.Array.ext_getElem?
      intro j
      simp only [Array.getElem?_modify, Array.size_modify]
      split <;> cases fr.binds[j]? <;> rfl
  · rfl

theorem setAtE_comm (E : Env) (f i f' i' : Nat) (v v' : Value) (hne : Pos.bind f i ≠ Pos.bind f' i') :
    Env.setAtE (Env.setAtE E (.bind f i) v) (.bind f' i') v' =
      Env.setAtE (Env.setAtE E (.bind f' i') v') (.bind f i) v := by
  apply _root_.Array.ext_getElem?
  intro k
  simp only [Env.setAtE, Array.getElem?_modify, Array.size_modify]
  by_cases h1 : f = k <;> by_cases h2 : f' = k
  · have hi : i ≠ i' := fun e => hne (by rw [h1, h2, e])
    simp only [if_pos h1, if_pos h2]
    cases E[k]? with
    | none => rfl
    | some fr =>
      simp only [Option.map_some, Option.some.injEq]
      congr 1
      apply _root_.Array.ext_getElem?
      intro j
      simp only [Array.getElem?_modify]
      by_cases e1 : i = j <;> by_cases e2 : i' = j
      · exact absurd (e1.trans e2.symm) hi
      all_goals simp [e1, e2]
  · simp only [if_pos h1, if_neg h2]
  · simp only [if_neg h1, if_pos h2]
  · simp only [if_neg h1, if_neg h2]

theorem runs_endTail_two {k : Nat} {s s' : MState} {b : Nat} {l : Nat} {w : Value}
    (hpos : allPos s.env = [.bind 0 0, .bind 0 1]) (hx : valAt s.env (.bind 0 0) = .loan l) (hw : w.Num)
    (h : Runs (do Ochr.setAt (.bind 0 1) .bot; Ochr.substEnv k (.loan l) w false
                  let e ← get; Ochr.lendEnv k (.ended l (liveLoansIn e.env w))) s b () s') :
    s' = { s with env := Env.setAtE (Env.setAtE s.env (.bind 0 1) .bot) (.bind 0 0) w } := by
  have hne : Pos.bind 0 1 ≠ Pos.bind 0 0 := by simp
  obtain ⟨_, s₁, b₁, hs, h⟩ := Runs.bind_inv h
  have e1 := runs_setAt_inv hs; subst e1
  obtain ⟨_, s₂, b₂, hsub, h⟩ := Runs.bind_inv h
  cases k with
  | zero => unfold Ochr.substEnv at hsub; simp only [runs_exhausted_iff] at hsub
  | succ k =>
    unfold Ochr.substEnv at hsub
    have hP1 : allPos (Env.setAtE s.env (.bind 0 1) .bot) = [.bind 0 0, .bind 0 1] := by rw [allPos_setAtE, hpos]
    have hv0 : valAt (Env.setAtE s.env (.bind 0 1) .bot) (.bind 0 0) = .loan l := by
      rw [valAt_setAtE_other _ _ _ _ hne.symm, hx]
    have hv1 : valAt (Env.setAtE s.env (.bind 0 1) .bot) (.bind 0 1) = .bot :=
      valAt_setAtE_self (E := s.env) (f := 0) (j := 1) (w := .bot) (by rw [hpos]; simp)
    have e2 := runs_mapState_two (s := { s with env := Env.setAtE s.env (.bind 0 1) .bot }) hP1 hne
      (fun st b r st' hr => by rw [hv0] at hr; exact runs_substV_hit hr)
      (fun st b r st' hr => by rw [hv1] at hr; exact runs_substV_miss (by simp [Value.anyAtom, Value.exact]) hr) hsub
    subst e2
    peel h
    unfold Ochr.lendEnv at h
    simp only at h
    have hP2 : allPos (Env.setAtE (Env.setAtE (Env.setAtE s.env (.bind 0 1) .bot) (.bind 0 0) w) (.bind 0 1) .bot) =
        [.bind 0 0, .bind 0 1] := by rw [allPos_setAtE, allPos_setAtE, allPos_setAtE, hpos]
    have hm : ∀ p ∈ allPos s.env, p ∈ allPos (Env.setAtE (Env.setAtE (Env.setAtE s.env (.bind 0 1) .bot) (.bind 0 0) w) (.bind 0 1) .bot) := by
      intro p hp; rw [allPos_setAtE, allPos_setAtE, allPos_setAtE]; exact hp
    have hw0 : valAt (Env.setAtE (Env.setAtE (Env.setAtE s.env (.bind 0 1) .bot) (.bind 0 0) w) (.bind 0 1) .bot) (.bind 0 0) = w := by
      rw [valAt_setAtE_other _ _ _ _ hne.symm, valAt_setAtE_self (E := Env.setAtE s.env (.bind 0 1) .bot) (f := 0) (j := 0) (w := w) (by rw [allPos_setAtE, hpos]; simp)]
    have hw1 : valAt (Env.setAtE (Env.setAtE (Env.setAtE s.env (.bind 0 1) .bot) (.bind 0 0) w) (.bind 0 1) .bot) (.bind 0 1) = .bot :=
      valAt_setAtE_self (E := Env.setAtE (Env.setAtE s.env (.bind 0 1) .bot) (.bind 0 0) w) (f := 0) (j := 1) (w := .bot)
        (by rw [allPos_setAtE, allPos_setAtE, hpos]; simp)
    have e3 := runs_mapState_two hP2 hne
      (fun st b r st' hr => by
        rw [hw0] at hr
        exact runs_lendV_miss (hw.anyAtom rfl (fun _ => rfl)) hr)
      (fun st b r st' hr => by rw [hw1] at hr; exact runs_lendV_miss rfl hr) h
    rw [e3]
    simp only [setAtE_same, setAtE_comm _ 0 1 0 0 _ _ hne]

theorem runs_endBorrow_two {k : Nat} {s s' : MState} {b : Nat} {l : Nat} {w : Value}
    (hpos : allPos s.env = [.bind 0 0, .bind 0 1]) (hx : valAt s.env (.bind 0 0) = .loan l)
    (hy : valAt s.env (.bind 0 1) = .borrow l w) (hw : w.Num) (h : Runs (Ochr.endBorrow k l) s b () s') :
    s' = { s with env := Env.setAtE (Env.setAtE s.env (.bind 0 1) .bot) (.bind 0 0) w } := by
  cases k with
  | zero => unfold Ochr.endBorrow at h; simp only [runs_exhausted_iff] at h
  | succ k =>
    unfold Ochr.endBorrow at h
    peel h
    rw [findBorrow_two hpos hx hy hw] at h
    simp only at h
    rw [hy] at h
    simp only [Value.takeBorrow, beq_self_eq_true, if_true, Value.Num.hasHole hw, Bool.false_eq_true, if_false] at h
    peel h
    have hK : ∀ {b₀ : Nat}, Runs (do
        let e ← get
        if e.typing = true then do
          let T ← Ochr.tyAt (Pos.bind 0 1)
          match (Value.borrow l w, T) with
          | (Value.borrow _ _, some (.tRef A)) => do
            Ochr.repackCheck k "a borrow of it ends" w A
            Ochr.setAt (Pos.bind 0 1) Value.bot
            Ochr.substEnv k (Value.loan l) w false
            let e ← get
            Ochr.lendEnv k (LendOp.ended l (liveLoansIn e.env w))
          | _ => do
            Ochr.setAt (Pos.bind 0 1) Value.bot
            Ochr.substEnv k (Value.loan l) w false
            let e ← get
            Ochr.lendEnv k (LendOp.ended l (liveLoansIn e.env w))
        else do
          Ochr.setAt (Pos.bind 0 1) Value.bot
          Ochr.substEnv k (Value.loan l) w false
          let e ← get
          Ochr.lendEnv k (LendOp.ended l (liveLoansIn e.env w))) s b₀ () s' →
        s' = { s with env := Env.setAtE (Env.setAtE s.env (.bind 0 1) .bot) (.bind 0 0) w } := by
      intro b₀ h
      peel h
      split at h
      · obtain ⟨T, s₁, b₁, ht, h⟩ := Runs.bind_inv h
        obtain ⟨-, e1⟩ := runs_tyAt_inv ht
        have e1' := e1.symm; subst e1'
        split at h
        · obtain ⟨_, s₂, b₂, hr, h⟩ := Runs.bind_inv h
          have e2 := runs_repackCheck_num hw hr
          have e2' := e2.symm; subst e2'
          exact runs_endTail_two hpos hx hw h
        · exact runs_endTail_two hpos hx hw h
      · exact runs_endTail_two hpos hx hw h
    split at h
    · split at h
      · exfalso
        obtain ⟨_, _, _, _, h⟩ := Runs.bind_inv h
        obtain ⟨_, _, _, he, _⟩ := Runs.bind_inv h
        simp only [runs_err_iff] at he
      · exact hK h
    · exact hK h

theorem runs_endTopLoan_two {k : Nat} {site : String} {p? : Option Place} {s s' : MState} {b : Nat} {l : Nat} {w : Value}
    (hpos : allPos s.env = [.bind 0 0, .bind 0 1]) (hx : valAt s.env (.bind 0 0) = .loan l)
    (hy : valAt s.env (.bind 0 1) = .borrow l w) (hw : w.Num) (h : Runs (Ochr.endTopLoan k l site p?) s b () s') :
    s' = { s with env := Env.setAtE (Env.setAtE s.env (.bind 0 1) .bot) (.bind 0 0) w } := by
  cases k with
  | zero => unfold Ochr.endTopLoan at h; simp only [runs_exhausted_iff] at h
  | succ k =>
    unfold Ochr.endTopLoan at h
    peel h
    rw [findBorrow_two hpos hx hy hw] at h
    simp only at h
    peel h
    split at h
    · obtain ⟨_, _, _, he, _⟩ := Runs.bind_inv h; simp only [runs_err_iff] at he
    · exact runs_endBorrow_two hpos hx hy hw h

theorem runs_accessPath_lent {k : Nat} {s s' : MState} {b : Nat} {l : Nat} {w : Value}
    (hpos : allPos s.env = [.bind 0 0, .bind 0 1]) (hx : valAt s.env (.bind 0 0) = .loan l)
    (hy : valAt s.env (.bind 0 1) = .borrow l w) (hw : w.Num) (hcv : ckVarPos s.env 1 = some (.bind 0 0))
    (h : Runs (Ochr.accessPath k (.var 1)) s b () s') :
    s' = { s with env := Env.setAtE (Env.setAtE s.env (.bind 0 1) .bot) (.bind 0 0) w } := by
  have hne : Pos.bind 0 1 ≠ Pos.bind 0 0 := by simp
  cases k with
  | zero => unfold Ochr.accessPath at h; simp only [runs_exhausted_iff] at h
  | succ k =>
    unfold Ochr.accessPath at h
    simp only [Place.steps] at h
    rw [runs_get_bind] at h
    obtain ⟨pos, s₁, b₁, hv, h₁⟩ := Runs.bind_inv h
    obtain ⟨e1, hp⟩ := runs_varPos_inv hv
    have e1' := e1.symm; subst e1'
    rw [hcv] at hp; cases hp
    have hl : liveLoan s.env l = true := by simp [liveLoan, findBorrow_two hpos hx hy hw]
    rw [hx] at h₁
    simp only [firstLiveLoanOnPath, hl, if_true] at h₁
    obtain ⟨_, s₂, b₂, he, h₂⟩ := Runs.bind_inv h₁
    have e2 := runs_endTopLoan_two hpos hx hy hw he
    subst e2
    cases k with
    | zero => unfold Ochr.accessPath at h₂; simp only [runs_exhausted_iff] at h₂
    | succ k =>
      unfold Ochr.accessPath at h₂
      simp only [Place.steps] at h₂
      rw [runs_get_bind] at h₂
      obtain ⟨pos, s₃, b₃, hv, h₃⟩ := Runs.bind_inv h₂
      obtain ⟨e3, hp⟩ := runs_varPos_inv hv
      have e3' := e3.symm; subst e3'
      simp only [ckVarPos_setAtE, hcv] at hp; cases hp
      have hw0 : valAt (Env.setAtE (Env.setAtE s.env (.bind 0 1) .bot) (.bind 0 0) w) (.bind 0 0) = w :=
        valAt_setAtE_self (E := Env.setAtE s.env (.bind 0 1) .bot) (f := 0) (j := 0) (w := w)
          (by rw [allPos_setAtE, hpos]; simp)
      simp only [hw0, firstLiveLoanOnPath_num hw] at h₃
      exact (runs_pure_inv h₃).2

theorem runs_repackCheck_loan {k : Nat} {w : String} {l : Nat} {T : Value} {st st' : MState} {b : Nat}
    (h : Runs (repackCheck k w (.loan l) T) st b () st') : st' = st := by
  cases k with
  | zero => unfold repackCheck at h; simp only [runs_exhausted_iff] at h
  | succ k' =>
    unfold repackCheck at h
    peel h
    obtain ⟨d, s₃, b₃, hd, h₃⟩ := Runs.bind_inv h
    unfold hasDependent at hd
    obtain ⟨rfl, rfl⟩ := runs_pure_inv hd
    simp only [Bool.not_false, if_true] at h₃
    exact (runs_pure_inv h₃).2

theorem runs_repackAt_lent {n : Nat} {T : Value} {w : String} {st st' : MState} {b l : Nat}
    (hcv : ckVarPos st.env 1 = some (.bind 0 0)) (hx : valAt st.env (.bind 0 0) = .loan l)
    (h : Runs (repackAt n (.var 1) T w) st b () st') : st' = st := by
  cases n with
  | zero => unfold repackAt at h; simp only [runs_exhausted_iff] at h
  | succ k =>
    unfold repackAt at h
    obtain ⟨o, s₁, b₁, hc, h₁⟩ := Runs.bind_inv h
    obtain ⟨rfl, pos, hp, rfl⟩ := runs_content?_inv hc
    simp only [Place.steps] at hp
    rw [hcv] at hp; cases hp
    simp only [Place.steps, Value.follow, hx] at h₁
    obtain ⟨m, s₂, b₂, hm, h₂⟩ := Runs.bind_inv h₁
    obtain ⟨-, rfl⟩ := runs_ppPlace_inv hm
    exact runs_repackCheck_loan h₂

/-- `runs_readPlace_num` from a state whose path access leads to the number state `st` (the read of
a lent variable: the access ends the borrow first). The proof is machine2's, its first step generic. -/
theorem runs_readPlace_after {n i f j : Nat} {bd : Binding} {st₀ st st' : MState} {b : Nat} {v : Value}
    (hacc : ∀ m b₀ s₁, n = m + 1 → Runs (Ochr.accessPath m (.var i)) st₀ b₀ () s₁ → s₁ = st)
    (hn : NumAt st i f j bd) (hip : st.inPlace = false) (hcp : st.copying = false)
    (h : Runs (Ochr.readPlace n (.var i)) st₀ b v st') :
    v = bd.val ∧ ∃ k d c b₁ b₂, Runs (withLive true (Ochr.placeDecl k [] (.var i))) st b₁ d st ∧
      Runs (declCopy k d) st b₂ c st ∧ (c = true → st' = st) ∧
      (c = false → ∃ X, st' = { st with env := Env.setAtE st.env (.bind f j) .bot, placeLog := X }) := by
  cases n with
  | zero => unfold Ochr.readPlace at h; simp only [runs_exhausted_iff] at h
  | succ m =>
    unfold Ochr.readPlace at h
    obtain ⟨_, s₁, b₁, ha, h₁⟩ := Runs.bind_inv h
    clear h
    have := hacc m _ _ rfl ha
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


/-! ## The assembly -/

section Assembly
open Ochr.Meaning.Steps.Form

/-- A path access to `.var i` succeeds only where the variable has a position. -/
theorem runs_accessPath_var_pos {k i : Nat} {s s' : MState} {b : Nat}
    (h : Runs (Ochr.accessPath k (.var i)) s b () s') : ∃ p, ckVarPos s.env i = some p := by
  cases k with
  | zero => unfold Ochr.accessPath at h; simp only [runs_exhausted_iff] at h
  | succ k =>
    unfold Ochr.accessPath at h
    simp only [Place.steps] at h
    rw [runs_get_bind] at h
    obtain ⟨pos, s₁, b₁, hv, -⟩ := Runs.bind_inv h
    obtain ⟨-, hp⟩ := runs_varPos_inv hv
    exact ⟨pos, hp⟩

theorem runs_readPlace_var_pos {n i : Nat} {s s' : MState} {b : Nat} {v : Value}
    (h : Runs (Ochr.readPlace n (.var i)) s b v s') : ∃ p, ckVarPos s.env i = some p := by
  cases n with
  | zero => unfold Ochr.readPlace at h; simp only [runs_exhausted_iff] at h
  | succ m =>
    unfold Ochr.readPlace at h
    obtain ⟨_, s₁, b₁, ha, -⟩ := Runs.bind_inv h
    exact runs_accessPath_var_pos ha

theorem runs_placeTypeQ_var_pos {n i : Nat} {st st' : MState} {b : Nat} {r : Option Value}
    (h : Runs (placeType? n (.var i)) st b r st') : ∃ p, ckVarPos st.env i = some p := by
  cases n with
  | zero => unfold placeType? at h; simp only [runs_exhausted_iff] at h
  | succ k =>
    unfold placeType? at h
    peel h
    obtain ⟨pos, s₁, b₁, hv, -⟩ := Runs.bind_inv h
    obtain ⟨-, hp⟩ := runs_varPos_inv hv
    exact ⟨pos, hp⟩

theorem runs_placeType_var_pos {n i : Nat} {st st' : MState} {b : Nat} {r : Value}
    (h : Runs (placeType n (.var i)) st b r st') : ∃ p, ckVarPos st.env i = some p := by
  cases n with
  | zero => unfold placeType at h; simp only [runs_exhausted_iff] at h
  | succ k =>
    unfold placeType at h
    peel h
    obtain ⟨o, s₁, b₁, hq, -⟩ := Runs.bind_inv h
    exact runs_placeTypeQ_var_pos hq

/-- At the two-binding state, the variable `1` that has a position is the binding `(0, 0)`: the
other position, `(0, 1)`, would need a third binding in frame `0`. (`allPos` alone does not give it:
an empty frame above would leave the variable no position.) -/
theorem ckVarPos_one_two {E : Env} {p : Pos} (hpos : allPos E = [.bind 0 0, .bind 0 1])
    (h : ckVarPos E 1 = some p) : ckVarPos E 1 = some (.bind 0 0) := by
  have hm := ckVarPos_mem _ h
  rw [hpos] at hm
  unfold ckVarPos at h ⊢
  split at h
  · rename_i hi
    cases h
    simp only [List.mem_cons, List.mem_nil_iff, or_false, Pos.bind.injEq] at hm
    have hne : 0 < E.size := by
      rcases Nat.eq_zero_or_pos E.size with e | e
      · rw [e, getElem!_neg E (0 - 1) (by omega)] at hi; exact absurd hi (Nat.not_lt_zero _)
      · exact e
    rw [if_pos hi]
    rcases hm with ⟨e1, e2⟩ | ⟨e1, e2⟩
    · rw [e2, e1]
    · exfalso
      rw [getElem!_pos E (E.size - 1) (by omega)] at hi e2
      have h2 : 2 < E[E.size - 1].binds.size := by omega
      have := bind_mem_allPos E (E.size - 1) 2 _ _ (Array.getElem?_eq_getElem (by omega)) (Array.getElem?_eq_getElem h2)
      rw [hpos, e1] at this
      simp at this
  · cases h

/-- The read after the access (`readPlace` at the two-binding state): the access ends `l`, then the
read of `x ↦ w` copies or moves as the aligned decision says, read at the ENDED state, whose top
readings are the entry's (`back_setAtE`). -/
theorem varEnd_read {n : Nat} {typed : Bool} {D : Decisions} {s st' : MState} {b' : Nat} {l : Nat} {w : Value}
    {T' T? : Option Value} {v : Value} {fr : Frame} {bx : Binding}
    (hpos : allPos s.env = [.bind 0 0, .bind 0 1]) (hx : valAt s.env (.bind 0 0) = .loan l)
    (hy : valAt s.env (.bind 0 1) = .borrow l w) (hw : w.Num)
    (hf : s.env[0]? = some fr) (hbx : fr.binds[0]? = some bx)
    (hm : Mode s) (hD : DecTab D st') (hg : TablesGrow s st')
    (hTs : typed = true → T' = some .tNat)
    (hr : Runs (do let __do_lift ← Ochr.readPlace n (Place.var 1); pure (__do_lift, T')) s b' (v, T?) st') :
    v = w ∧ (typed = true → T? = some .tNat) ∧ Mode st' ∧ ∃ st₁, Quiet s st₁ ∧ KeepsInv s st₁ ∧
      (D.copy (D.placeDecl (DecideScope.topReadings s) (.var 1)) = true →
        Kern { st₁ with env := Env.setAtE (Env.setAtE st₁.env (.bind 0 1) .bot) (.bind 0 0) w } st') ∧
      (D.copy (D.placeDecl (DecideScope.topReadings s) (.var 1)) = false →
        Kern { st₁ with env := Env.setAtE (Env.setAtE st₁.env (.bind 0 1) .bot) (.bind 0 0) .bot } st') := by
  obtain ⟨v', s₄, b₄, hrp, h₄⟩ := Runs.bind_inv hr
  obtain ⟨hvt, rfl⟩ := runs_pure_inv h₄
  simp only [Prod.mk.injEq] at hvt
  obtain ⟨e1, e2⟩ := hvt
  subst e2
  obtain ⟨p, hp0⟩ := runs_readPlace_var_pos hrp
  have hcv := ckVarPos_one_two hpos hp0
  have hbe : (Env.setAtE (Env.setAtE s.env (.bind 0 1) .bot) (.bind 0 0) w)[0]?.bind
      (fun fr : Frame => fr.binds[0]?) = some { bx with val := w } := by
    simp only [frame_setAtE, hf, Option.map_some, if_true, Option.bind_some, Array.getElem?_modify, hbx]
    simp
  have hn : NumAt { s with env := Env.setAtE (Env.setAtE s.env (.bind 0 1) .bot) (.bind 0 0) w } 1 0 0
      { bx with val := w } := ⟨by simp only [ckVarPos_setAtE, hcv], hbe, hw⟩
  obtain ⟨hv, k, d, c, b₆, b₇, hpd, hdc, hct, hcf⟩ :=
    runs_readPlace_after (fun m b₀ s₁ _ ha => runs_accessPath_lent hpos hx hy hw hcv ha) hn hm.inPlace hm.copying hrp
  have hvw : v = w := by first | exact e1.trans hv | exact e1.symm.trans hv
  have hDe : DecTab D { s with env := Env.setAtE (Env.setAtE s.env (.bind 0 1) .bot) (.bind 0 0) w } :=
    DecTab.back hD ⟨hg.globals, hg.inds, hg.size, hg.old, hg.nextAbs, hg.nextLoan⟩
  have htr : topReadings { s with env := Env.setAtE (Env.setAtE s.env (.bind 0 1) .bot) (.bind 0 0) w } =
      topReadings s := by
    unfold topReadings
    show (((Env.setAtE (Env.setAtE s.env (.bind 0 1) .bot) (.bind 0 0) w).back?.map
      (fun fr : Frame => fr.binds.toList.map (·.decl))).getD []).reverse = _
    rw [back_setAtE, back_setAtE]
  have hd := decTab_placeDecl_at hDe hpd
  have hc := hDe.copy k d c b₇ _ hdc
  rw [htr] at hd
  rw [hd, hc]
  cases c with
  | true =>
    obtain rfl := hct rfl
    exact ⟨hvw, hTs, ⟨hm.headEval, hm.copying, hm.inPlace, hm.erased⟩, s, Quiet.refl _, fun _ _ h => h,
      fun _ => Kern.rfl' _, (fun e => by cases e)⟩
  | false =>
    obtain ⟨X, rfl⟩ := hcf rfl
    refine ⟨hvw, hTs, ⟨hm.headEval, hm.copying, hm.inPlace, hm.erased⟩, s, Quiet.refl _, fun _ _ h => h,
      (fun e => by cases e), fun _ => ?_⟩
    have e := setAtE_same (Env.setAtE s.env (.bind 0 1) .bot) 0 0 w .bot
    exact ⟨by simp only [e], rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

set_option maxHeartbeats 4000000 in
/-- **`VarEndInv`, proved**: the read of `x` lent to `y`'s borrow at the two-binding state. -/
theorem varEndInv : VarEndInv := by
  intro n typed hint st st' bh v T? l w D hm hpos hx hy hw hty hD h
  have hg : TablesGrow st st' := Runs.grows (grows_evalCore _ _ _ _) h
  obtain ⟨fr, bx, hf, hbx⟩ := mem_allPos_bind st.env 0 0 (by rw [hpos]; simp)
  have hb : st.env[0]?.bind (fun fr : Frame => fr.binds[0]?) = some bx := by rw [hf]; exact hbx
  have hT : bx.ty = some .tNat := hty bx hb
  unfold Ochr.evalCore at h
  obtain ⟨b₁, h⟩ := Runs.tick_bind h
  obtain ⟨want, s₁, b₂, hw', h⟩ := Runs.bind_inv (runs_get_bind.mp h)
  obtain ⟨hw1, hw2⟩ := runs_wanted_inv hw'
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
    obtain ⟨p, hp0⟩ := runs_placeType_var_pos hpt'
    have hcv := ckVarPos_one_two hpos hp0
    obtain ⟨rfl, rfl⟩ := runs_placeType_var hcv hb hT hpt'
    try simp only [if_true] at h₂
    obtain ⟨_, s₄, b₅, hra, h₃⟩ := Runs.bind_inv h₂
    have := runs_repackAt_lent hcv hx hra
    subst this
    exact varEnd_read hpos hx hy hw hf hbx hm hD hg (fun _ => rfl) h₃
  | false =>
    simp only [Bool.false_eq_true, if_false] at h₁
    split at h₁
    · obtain ⟨T', s₃, b₄, hpt, h₂⟩ := Runs.bind_inv h₁
      clear h₁
      obtain ⟨p, hp0⟩ := runs_placeTypeQ_var_pos hpt
      have hcv := ckVarPos_one_two hpos hp0
      obtain ⟨rfl, rfl⟩ := runs_placeTypeQ_var hcv hb hT hpt
      try simp only [Bool.false_eq_true, if_false, pure_bind] at h₂
      exact varEnd_read hpos hx hy hw hf hbx hm hD hg (fun e => by cases e) h₂
    · try simp only [pure_bind, Bool.false_eq_true, if_false] at h₁
      exact varEnd_read hpos hx hy hw hf hbx hm hD hg (fun e => by cases e) h₁

end Assembly

end Ochr.Meaning.Steps.Machine
