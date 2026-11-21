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

end Ochr.Meaning.Steps.Machine
