import Ochr.Meaning.Steps.Machine.FragRuns
import Ochr.Meaning.Steps.Machine.FragFacts

/-!
# The end of one borrow in a fragment environment (machine lane)

`endBorrow l` and `endTopLoan l` where the environment holds fragment values, `loan_l` at `px` only
and `borrow_l c` (`c` a number) at `ph` only (`FEnd`): the result is `endE` (`ph ↦ ⊥`, `px ↦ c`).
The general form of `VarEndInv.lean`'s two-binding lemmas: `mapState` walked over any list of
positions (`runs_mapState_fold`), the fold computed where the map is the identity but at one
position (`setAtE_valAt_self`). The shared core of `VarLentInv`, `BorrowLentInv`, `DropBorrowInv`,
`AssignVarInv`, `SeqBorInv`.
-/

namespace Ochr.Meaning.Steps.Machine

open Ochr Ochr.Meaning Ochr.Meaning.Steps Ochr.Meaning.DecideScope Ochr.Meaning.Steps.Slice
open Ochr.Meaning.Steps.Form
open Classical

theorem setAtE_valAt_self {E : Env} {p : Pos} (hp : p ∈ allPos E) : Env.setAtE E p (valAt E p) = E := by
  cases p with
  | bind f i =>
    obtain ⟨fr, b, hf, hb⟩ := mem_allPos_bind E f i hp
    have hv : valAt E (.bind f i) = b.val := by
      show (E[f]!).binds[i]!.val = _; rw [binds_get! (by rw [hf]; exact hb)]
    rw [hv]
    apply Array.ext_getElem?
    intro k
    simp only [Env.setAtE, Array.getElem?_modify]
    split
    · subst_vars; rw [hf]; simp only [Option.map_some, Option.some.injEq]
      congr 1
      apply Array.ext_getElem?
      intro m
      simp only [Array.getElem?_modify]
      split
      · subst_vars; rw [hb]; rfl
      · rfl
    · rfl
  | temp f i =>
    obtain ⟨fr, hf, hi⟩ := mem_allPos_temp E f i hp
    have hv : valAt E (.temp f i) = fr.temps[i] := by
      rw [valAt_temp_eq]; simp [hf, Array.getElem?_eq_getElem hi]
    rw [hv]
    apply Array.ext_getElem?
    intro k
    simp only [Env.setAtE, Array.getElem?_modify]
    split
    · subst_vars; rw [hf]; simp only [Option.map_some, Option.some.injEq]
      congr 1
      simp [Array.set!, hi, Array.setIfInBounds, Array.set_getElem_self]
    · rfl

/-- A fold of writes that each write a position's own value back is the identity. -/
theorem foldl_setAtE_id {φ : Value → Value} :
    ∀ (L : List Pos) (E : Env), (∀ q ∈ L, q ∈ allPos E) → (∀ q ∈ L, φ (valAt E q) = valAt E q) →
      L.foldl (fun E p => Env.setAtE E p (φ (valAt E p))) E = E
  | [], _, _, _ => rfl
  | q :: L, E, hm, hφ => by
    rw [List.foldl_cons, hφ q (.head _), setAtE_valAt_self (hm q (.head _))]
    exact foldl_setAtE_id L E (fun q' h => hm q' (.tail _ h)) (fun q' h => hφ q' (.tail _ h))

/-- The fold over the positions where the map moves only `px`'s value. -/
theorem foldl_setAtE_one {φ : Value → Value} {E : Env} {px : Pos} (hpx : px ∈ allPos E)
    (hφ : ∀ q ∈ allPos E, q ≠ px → φ (valAt E q) = valAt E q)
    (hφx : ∀ q ∈ allPos E, q ≠ px → φ (valAt (Env.setAtE E px (φ (valAt E px))) q) = valAt (Env.setAtE E px (φ (valAt E px))) q) :
    (allPos E).foldl (fun E p => Env.setAtE E p (φ (valAt E p))) E = Env.setAtE E px (φ (valAt E px)) := by
  obtain ⟨L1, L2, hsplit⟩ := List.append_of_mem hpx
  have hnd := allPos_nodup E
  rw [hsplit] at hnd
  have hnd' := List.nodup_append.mp hnd
  have h1 : px ∉ L1 := fun h => by
    have := hnd'.2.2 px h px (.head _); exact this rfl
  have h2 : px ∉ L2 := (List.nodup_cons.mp hnd'.2.1).1
  rw [hsplit, List.foldl_append, List.foldl_cons]
  rw [foldl_setAtE_id L1 E (fun q h => by rw [hsplit]; exact List.mem_append_left _ h)
    (fun q h => hφ q (by rw [hsplit]; exact List.mem_append_left _ h) (fun e => h1 (e ▸ h)))]
  refine foldl_setAtE_id L2 _ (fun q h => ?_) (fun q h => hφx q (by rw [hsplit]; exact List.mem_append_right _ (.tail _ h)) (fun e => h2 (e ▸ h)))
  rw [allPos_setAtE, hsplit]; exact List.mem_append_right _ (.tail _ h)

/-- A `for` loop over positions whose body sets each position to `φ` of its value. -/
theorem runs_forIn_fold {body : Pos → PUnit → M (ForInStep PUnit)} {φ : Value → Value} {P : Value → Prop}
    (hP : ∀ v, P v → P (φ v))
    (hbody : ∀ p (s s' : MState) b r, p ∈ allPos s.env → (∀ q ∈ allPos s.env, P (valAt s.env q)) →
      Runs (body p PUnit.unit) s b r s' → r = .yield PUnit.unit ∧ s' = { s with env := Env.setAtE s.env p (φ (valAt s.env p)) }) :
    ∀ (L : List Pos) (s s' : MState) (b : Nat) (u : PUnit), (∀ q ∈ allPos s.env, P (valAt s.env q)) → (∀ q ∈ L, q ∈ allPos s.env) →
      Runs (forIn L PUnit.unit body) s b u s' → s' = { s with env := L.foldl (fun E p => Env.setAtE E p (φ (valAt E p))) s.env }
  | [], s, s', b, u, _, _, h => by
    simp only [List.forIn_nil] at h
    obtain ⟨-, rfl⟩ := runs_pure_inv h
    rfl
  | p :: L, s, s', b, u, hs, hm, h => by
    simp only [List.forIn_cons] at h
    obtain ⟨x, s₁, b₁, h1, hrest⟩ := Runs.bind_inv h
    obtain ⟨rfl, rfl⟩ := hbody p s s₁ b x (hm p (.head _)) hs h1
    simp only at hrest
    have hs' : ∀ q ∈ allPos (Env.setAtE s.env p (φ (valAt s.env p))), P (valAt (Env.setAtE s.env p (φ (valAt s.env p))) q) := by
      intro q hq
      rw [allPos_setAtE] at hq
      by_cases e : q = p
      · subst e; rw [Ochr.Meaning.Steps.valAt_setAtE_self _ hq]; exact hP _ (hs q hq)
      · rw [valAt_setAtE_other _ _ _ _ e]; exact hs q hq
    rw [runs_forIn_fold hP hbody L _ s' b₁ u hs'
      (fun q h => by show q ∈ allPos (Env.setAtE _ _ _); rw [allPos_setAtE]; exact hm q (.tail _ h)) hrest, List.foldl_cons]

/-- **`mapState f false`** where `f` acts as the pure map `φ` on every value it meets (values in `P`,
which `φ` keeps): each position in turn set to `φ` of its value. -/
theorem runs_mapState_fold {f : Value → M Value} {φ : Value → Value} {P : Value → Prop}
    (hf : ∀ v, P v → ∀ st b r st', Runs (f v) st b r st' → r = φ v ∧ st' = st) (hP : ∀ v, P v → P (φ v))
    {s s' : MState} {b : Nat} (hs : ∀ q ∈ allPos s.env, P (valAt s.env q))
    (h : Runs (Ochr.mapState f false) s b () s') :
    s' = { s with env := (allPos s.env).foldl (fun E p => Env.setAtE E p (φ (valAt E p))) s.env } := by
  unfold Ochr.mapState at h
  peel h
  obtain ⟨_, s₀, b₀, hfor, htail⟩ := Runs.bind_inv h
  obtain ⟨-, e9⟩ := runs_pure_inv htail
  rw [e9]
  clear h htail e9
  simp only [Bool.false_eq_true, ↓reduceIte] at hfor
  refine runs_forIn_fold hP (fun p s₁ s₂ b₁ r hp hs₁ h1 => ?_) _ s s₀ b _ hs (fun _ h => h) hfor
  obtain ⟨v₁, s₃, b₃, hg, h1⟩ := Runs.bind_inv h1
  obtain ⟨e1, e2⟩ := runs_getAt_inv hg
  subst e1; have e2' := e2.symm; subst e2'
  obtain ⟨r₁, s₄, b₄, hfr, h1⟩ := Runs.bind_inv h1
  obtain ⟨e3, e4⟩ := hf _ (hs₁ p hp) _ _ _ _ hfr
  subst e3; have e4' := e4.symm; subst e4'
  obtain ⟨_, s₅, b₅, hst, h1⟩ := Runs.bind_inv h1
  have e5 := runs_setAt_inv hst; subst e5
  obtain ⟨e6, e7⟩ := runs_pure_inv h1
  exact ⟨e6, e7⟩

/-- `tyAt` only reads. -/
theorem runs_tyAt_state {p : Pos} {s s' : MState} {b : Nat} {T? : Option Value}
    (h : Runs (Ochr.tyAt p) s b T? s') : s' = s := by
  cases p with
  | bind f j => exact (runs_tyAt_inv h).2
  | temp f i => unfold Ochr.tyAt at h; exact (runs_pure_inv h).2

/-- `substV` of `loan_l` by `c` on a fragment value: `c` at `loan_l`, the value itself elsewhere. -/
theorem runs_substV_fval {k l : Nat} {c v r : Value} {st st' : MState} {b : Nat} (hv : FVal v)
    (h : Runs (Ochr.substV k (.loan l) c v) st b r st') : r = (if v = .loan l then c else v) ∧ st' = st := by
  by_cases e : v = .loan l
  · subst e; rw [if_pos rfl]; exact runs_substV_hit h
  · rw [if_neg e]
    refine runs_substV_miss ?_ h
    cases hv with
    | num hn => exact hn.anyAtom rfl (fun _ => rfl)
    | unit => rfl
    | bot => rfl
    | loan m =>
      have hm : m ≠ l := fun e' => e (by rw [e'])
      simp [Value.anyAtom, Value.exact, hm]
    | bor m hw =>
      simp only [Value.anyAtom, Value.exact, Bool.false_or]
      exact hw.anyAtom rfl (fun _ => rfl)

/-- `lendV (.ended l _)` on a fragment value holding neither `loan_l` nor `borrow_l`: the value itself. -/
theorem runs_lendV_fval {k l : Nat} {to : List Nat} {v r : Value} {st st' : MState} {b : Nat} (hv : FVal v)
    (hl : v ≠ .loan l) (hb : ∀ w, v ≠ .borrow l w)
    (h : Runs (Ochr.lendV k (.ended l to) v) st b r st') : r = v ∧ st' = st := by
  refine runs_lendV_miss ?_ h
  cases hv with
  | num hn => exact hn.anyAtom rfl (fun _ => rfl)
  | unit => rfl
  | bot => rfl
  | loan m =>
    have hm : m ≠ l := fun e' => hl (by rw [e'])
    simp [Value.anyAtom, hm]
  | bor m hw =>
    have hm : m ≠ l := fun e' => hb _ (by rw [e'])
    show (m == l || _) = false
    rw [show (m == l) = false from by simpa using hm, Bool.false_or]
    exact hw.anyAtom rfl (fun _ => rfl)

/-- **The tail of an end in a fragment environment**: the holder `⊥`, `substEnv` gives `c` to the one
position holding `loan_l`, `lendEnv` changes nothing. -/
theorem runs_endTail_fend {k : Nat} {s s' : MState} {b : Nat} {px ph : Pos} {l : Nat} {c : Value}
    (hF : FEnd s.env px ph l c)
    (h : Runs (do Ochr.setAt ph .bot; Ochr.substEnv k (.loan l) c false
                  let e ← get; Ochr.lendEnv k (.ended l (liveLoansIn e.env c))) s b () s') :
    s' = { s with env := endE s.env px ph c } := by
  have hne : ph ≠ px := hF.ne
  obtain ⟨_, s₁, b₁, hs, h⟩ := Runs.bind_inv h
  have e1 := runs_setAt_inv hs; subst e1
  obtain ⟨_, s₂, b₂, hsub, h⟩ := Runs.bind_inv h
  cases k with
  | zero => unfold Ochr.substEnv at hsub; simp only [runs_exhausted_iff] at hsub
  | succ k =>
    unfold Ochr.substEnv at hsub
    -- the environment after the holder's `⊥`
    have hA1 : allPos (Env.setAtE s.env ph .bot) = allPos s.env := allPos_setAtE _ _ _
    have hv1 : ∀ q, valAt (Env.setAtE s.env ph .bot) q = if q = ph then .bot else valAt s.env q := by
      intro q
      split
      · next e => subst e; exact Ochr.Meaning.Steps.valAt_setAtE_self _ hF.hph
      · next e => exact valAt_setAtE_other _ _ _ _ e
    have hvals1 : ∀ q ∈ allPos (Env.setAtE s.env ph .bot), FVal (valAt (Env.setAtE s.env ph .bot) q) := by
      intro q hq; rw [hv1]; split
      · exact .bot
      · exact hF.vals q (hA1 ▸ hq)
    have e2 := runs_mapState_fold (s := { s with env := Env.setAtE s.env ph .bot })
      (φ := fun v => if v = .loan l then c else v) (P := FVal)
      (fun v hv st b r st' hr => runs_substV_fval hv hr)
      (fun v hv => by
        show FVal (if v = .loan l then c else v)
        split
        · exact .num hF.c
        · exact hv) hvals1 hsub
    subst e2
    have hx1 : valAt (Env.setAtE s.env ph .bot) px = .loan l := by rw [hv1, if_neg hne.symm]; exact hF.x
    -- off `px`, no position of the environment holds `loan_l`
    have hoff : ∀ q ∈ allPos (Env.setAtE s.env ph .bot), q ≠ px → valAt (Env.setAtE s.env ph .bot) q ≠ .loan l := by
      intro q hq hqx e
      rw [hv1] at e
      split at e
      · cases e
      · exact hqx (hF.loan1 q (hA1 ▸ hq) e)
    have hfold := foldl_setAtE_one (φ := fun v => if v = .loan l then c else v) (E := Env.setAtE s.env ph .bot)
      (by rw [hA1]; exact hF.hpx)
      (fun q hq hqx => if_neg (hoff q hq hqx))
      (fun q hq hqx => by
        show (if _ = _ then c else _) = _
        rw [valAt_setAtE_other _ _ _ _ hqx, if_neg (hoff q hq hqx)])
    rw [hfold, hx1, if_pos rfl] at h
    clear hfold hsub
    peel h
    unfold Ochr.lendEnv at h
    simp only at h
    -- the environment after the end: `endE`
    have hE : Env.setAtE (Env.setAtE s.env ph .bot) px c = endE s.env px ph c := rfl
    simp only [hE] at h ⊢
    have hP : ∀ q ∈ allPos (endE s.env px ph c), FVal (valAt (endE s.env px ph c) q) ∧
        valAt (endE s.env px ph c) q ≠ .loan l ∧ ∀ w, valAt (endE s.env px ph c) q ≠ .borrow l w := by
      intro q hq
      rw [FEnd.allPos_endE] at hq
      refine ⟨hF.vals_endE q (by rw [FEnd.allPos_endE]; exact hq), ?_, ?_⟩ <;> rw [hF.valAt_endE]
      · split
        · exact FVal.num_ne_loan hF.c l
        · split
          · intro e; cases e
          · next e1 _ => exact fun e => e1 (hF.loan1 q hq e)
      · intro w; split
        · exact fun e => hF.c.not_borrow l w e
        · split
          · intro e; cases e
          · next _ e2 => exact fun e => e2 (hF.bor1 q hq w e)
    have e3 := runs_mapState_fold (φ := id)
      (P := fun v => FVal v ∧ v ≠ .loan l ∧ ∀ w, v ≠ .borrow l w)
      (fun v hv st b r st' hr => runs_lendV_fval hv.1 hv.2.1 hv.2.2 hr) (fun v hv => hv) hP h
    rw [e3, foldl_setAtE_id (φ := id) _ _ (fun q h => h) (fun q _ => rfl)]

/-- **`endBorrow l` in a fragment environment** (`FEnd`): `ph ↦ ⊥`, `px ↦ c`, nothing else (the
[Repack] of a number passes and changes nothing; D98's test passes, a number being whole; an
observation's frame, where one is open, may reject the end). -/
theorem runs_endBorrow_fend {k : Nat} {s s' : MState} {b : Nat} {px ph : Pos} {l : Nat} {c : Value}
    (hF : FEnd s.env px ph l c) (h : Runs (Ochr.endBorrow k l) s b () s') :
    s' = { s with env := endE s.env px ph c } := by
  have hfb : findBorrow s.env l = some ph := by
    refine findBorrow_unique hF.hph (by rw [hF.y]; simp [Value.holdsBorrow]) (fun q hq hh => ?_)
    obtain ⟨w, hw⟩ := (FVal.holdsBorrow (hF.vals q hq) l).mp hh
    exact hF.bor1 q hq w hw
  have hnh : c.hasHole = false := Value.Num.hasHole hF.c
  cases k with
  | zero => unfold Ochr.endBorrow at h; simp only [runs_exhausted_iff] at h
  | succ k =>
    unfold Ochr.endBorrow at h
    peel h
    rw [hfb] at h
    simp only at h
    rw [hF.y] at h
    simp only [Value.takeBorrow, beq_self_eq_true, if_true, hnh, Bool.false_eq_true, if_false] at h
    peel h
    have hK : ∀ {b₀ : Nat}, Runs (do
        let e ← get
        if e.typing = true then do
          let T ← Ochr.tyAt ph
          match (Value.borrow l c, T) with
          | (Value.borrow _ _, some (.tRef A)) => do
            Ochr.repackCheck k "a borrow of it ends" c A
            Ochr.setAt ph Value.bot
            Ochr.substEnv k (Value.loan l) c false
            let e ← get
            Ochr.lendEnv k (LendOp.ended l (liveLoansIn e.env c))
          | _ => do
            Ochr.setAt ph Value.bot
            Ochr.substEnv k (Value.loan l) c false
            let e ← get
            Ochr.lendEnv k (LendOp.ended l (liveLoansIn e.env c))
        else do
          Ochr.setAt ph Value.bot
          Ochr.substEnv k (Value.loan l) c false
          let e ← get
          Ochr.lendEnv k (LendOp.ended l (liveLoansIn e.env c))) s b₀ () s' →
        s' = { s with env := endE s.env px ph c } := by
      intro b₀ h
      peel h
      split at h
      · obtain ⟨T, s₁, b₁, ht, h1⟩ := Runs.bind_inv h
        have e1 := runs_tyAt_state ht; subst e1
        split at h1
        · obtain ⟨_, s₂, b₂, hr, h2⟩ := Runs.bind_inv h1
          have e2 := runs_repackCheck_num hF.c hr
          subst e2
          exact runs_endTail_fend hF h2
        · exact runs_endTail_fend hF h1
      · exact runs_endTail_fend hF h
    split at h
    · cases ph with
      | bind f i =>
        simp only at h
        split at h
        · exfalso
          obtain ⟨_, _, _, _, h⟩ := Runs.bind_inv h
          obtain ⟨_, _, _, he, _⟩ := Runs.bind_inv h
          simp only [runs_err_iff] at he
        · exact hK h
      | temp f i =>
        simp only at h
        split at h
        · exfalso
          obtain ⟨_, _, _, _, h⟩ := Runs.bind_inv h
          obtain ⟨_, _, _, he, _⟩ := Runs.bind_inv h
          simp only [runs_err_iff] at he
        · exact hK h
    · exact hK h

theorem findBorrow_fend {E : Env} {px ph : Pos} {l : Nat} {c : Value} (hF : FEnd E px ph l c) :
    findBorrow E l = some ph := by
  refine findBorrow_unique hF.hph (by rw [hF.y]; simp [Value.holdsBorrow]) (fun q hq hh => ?_)
  obtain ⟨w, hw⟩ := (FVal.holdsBorrow (hF.vals q hq) l).mp hh
  exact hF.bor1 q hq w hw

/-- **`endTopLoan l` with the borrow held at a binding** (`FEnd`): the frame check (F4) passes or the
run fails; D106's test sees a binding; then `endBorrow`. -/
theorem runs_endTopLoan_fend {k : Nat} {site : String} {p? : Option Place} {s s' : MState} {b : Nat}
    {px : Pos} {f' j' l : Nat} {c : Value}
    (hF : FEnd s.env px (.bind f' j') l c) (h : Runs (Ochr.endTopLoan k l site p?) s b () s') :
    s' = { s with env := endE s.env px (.bind f' j') c } := by
  cases k with
  | zero => unfold Ochr.endTopLoan at h; simp only [runs_exhausted_iff] at h
  | succ k =>
    unfold Ochr.endTopLoan at h
    peel h
    rw [findBorrow_fend hF] at h
    simp only at h
    peel h
    split at h
    · obtain ⟨_, _, _, he, _⟩ := Runs.bind_inv h; simp only [runs_err_iff] at he
    · exact runs_endBorrow_fend hF h

end Ochr.Meaning.Steps.Machine
