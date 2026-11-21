import Ochr.Meaning.Steps.BotWriteRel
import Ochr.Meaning.KeyBridge

/-!
# `Good` after the write of `⊥` (L3's other half; docs/31 D50)

The checker's write of `⊥` at a path of a position (`setPlace q .bot` at the drop) keeps every
clause of `Good`: it removes a part, so every atom test that reads a value by its own data only
holds of the new value if it did of the old (`UpdBot.anyAtom_of_updAt_bot`), the loans outside
sealed programs of the new value are a sublist of the old's (`outerLoans_updAt_bot`), the stored
types and the borrows held are unchanged, the sites are unchanged after the access
(`sitesOf_setAtE_bot`), and the new meaning is the old with a part moved out (`movedOf_mean_updAt`),
which keeps partial membership (`pmem_moved_part`).
-/

namespace Ochr.Meaning.Steps

open Ochr.Meaning

theorem outerLoansList_set : ∀ (fs : List Value) (i : Nat) (w w' : Value), fs[i]? = some w →
    w'.outerLoans.Sublist w.outerLoans →
    (Value.outerLoansList (fs.set i w')).Sublist (Value.outerLoansList fs)
  | [], _, _, _, h, _ => by simp at h
  | x :: xs, 0, w, w', h, hw => by
    simp only [List.getElem?_cons_zero, Option.some.injEq] at h; subst h
    simp only [List.set_cons_zero, Value.outerLoansList]
    exact hw.append (List.Sublist.refl _)
  | x :: xs, i + 1, w, w', h, hw => by
    simp only [List.getElem?_cons_succ] at h
    simp only [List.set_cons_succ, Value.outerLoansList]
    exact (List.Sublist.refl _).append (outerLoansList_set xs i w w' h hw)

/-- **Writing `⊥` adds no loan outside sealed programs**: the new value's are a sublist. -/
theorem outerLoans_updAt_bot : ∀ (steps : List Step) (v v' : Value),
    Value.updAt (fun _ => .bot) steps v = some v' → v'.outerLoans.Sublist v.outerLoans
  | [], v, v', h => by
    simp only [Value.updAt, Option.some.injEq] at h; subst h
    simp [Value.outerLoans]
  | st :: ss, v, v', h => by
    cases v with
    | gloan m w =>
      simp only [Value.updAt] at h
      obtain ⟨w', hw', rfl⟩ := Option.map_eq_some_iff.mp h
      simp only [Value.outerLoans]; exact outerLoans_updAt_bot (st :: ss) w w' hw'
    | borrow m w =>
      cases st with
      | deref =>
        simp only [Value.updAt] at h
        obtain ⟨w', hw', rfl⟩ := Option.map_eq_some_iff.mp h
        simp only [Value.outerLoans]; exact outerLoans_updAt_bot ss w w' hw'
      | proj _ | field _ => simp [Value.updAt] at h
    | succ w =>
      cases st with
      | proj i =>
        cases i with
        | zero =>
          simp only [Value.updAt] at h
          obtain ⟨w', hw', rfl⟩ := Option.map_eq_some_iff.mp h
          simp only [Value.outerLoans]; exact outerLoans_updAt_bot ss w w' hw'
        | succ _ => simp [Value.updAt] at h
      | deref | field _ => simp [Value.updAt] at h
    | ind ty c hh ps fs =>
      obtain ⟨-, w, w', hw, hw', rfl⟩ := updAt_ind_inv h
      simp only [Value.outerLoans]
      exact (List.Sublist.refl _).append (outerLoansList_set fs _ w w' hw (outerLoans_updAt_bot ss w w' hw'))
    | _ => simp [Value.updAt] at h
termination_by steps v => (steps.length, sizeOf v)

theorem loansList_set : ∀ (fs : List Value) (i : Nat) (w w' : Value), fs[i]? = some w →
    w'.loans.Sublist w.loans → (Value.loansList (fs.set i w')).Sublist (Value.loansList fs)
  | [], _, _, _, h, _ => by simp at h
  | x :: xs, 0, w, w', h, hw => by
    simp only [List.getElem?_cons_zero, Option.some.injEq] at h; subst h
    simp only [List.set_cons_zero, Value.loansList]
    exact hw.append (List.Sublist.refl _)
  | x :: xs, i + 1, w, w', h, hw => by
    simp only [List.getElem?_cons_succ] at h
    simp only [List.set_cons_succ, Value.loansList]
    exact (List.Sublist.refl _).append (loansList_set xs i w w' h hw)

/-- **Writing `⊥` adds no loan**: the new value's loans are a sublist. -/
theorem loans_updAt_bot : ∀ (steps : List Step) (v v' : Value),
    Value.updAt (fun _ => .bot) steps v = some v' → v'.loans.Sublist v.loans
  | [], v, v', h => by
    simp only [Value.updAt, Option.some.injEq] at h; subst h
    simp [Value.loans]
  | st :: ss, v, v', h => by
    cases v with
    | gloan m w =>
      simp only [Value.updAt] at h
      obtain ⟨w', hw', rfl⟩ := Option.map_eq_some_iff.mp h
      simp only [Value.loans]; exact (loans_updAt_bot (st :: ss) w w' hw').cons₂ m
    | borrow m w =>
      cases st with
      | deref =>
        simp only [Value.updAt] at h
        obtain ⟨w', hw', rfl⟩ := Option.map_eq_some_iff.mp h
        simp only [Value.loans]; exact loans_updAt_bot ss w w' hw'
      | proj _ | field _ => simp [Value.updAt] at h
    | succ w =>
      cases st with
      | proj i =>
        cases i with
        | zero =>
          simp only [Value.updAt] at h
          obtain ⟨w', hw', rfl⟩ := Option.map_eq_some_iff.mp h
          simp only [Value.loans]; exact loans_updAt_bot ss w w' hw'
        | succ _ => simp [Value.updAt] at h
      | deref | field _ => simp [Value.updAt] at h
    | ind ty c hh ps fs =>
      obtain ⟨-, w, w', hw, hw', rfl⟩ := updAt_ind_inv h
      simp only [Value.loans]
      exact (List.Sublist.refl _).append (loansList_set fs _ w w' hw (loans_updAt_bot ss w w' hw'))
    | _ => simp [Value.updAt] at h
termination_by steps v => (steps.length, sizeOf v)

/-! ## The environment after the write -/

/-- An atom test true of no value of Ω is true of none after the write. -/
theorem values_anyAtom_setAtE {P : Value → Bool} (hP : ShallowAtom P) {env : Env} {pos : Pos}
    {steps : List Step} {v' : Value} (hp : pos ∈ allPos env)
    (hv : Value.updAt (fun _ => .bot) steps (valAt env pos) = some v')
    (hall : ∀ w ∈ Env.values env, w.anyAtom P = false) :
    ∀ w ∈ Env.values (Env.setAtE env pos v'), w.anyAtom P = false := by
  intro w hw
  rcases mem_values_setAtE hw with rfl | hw
  · cases e : w.anyAtom P
    · rfl
    · have := anyAtom_of_updAt_bot hP steps _ _ hv e
      rw [hall _ (List.mem_map.mpr ⟨pos, hp, rfl⟩)] at this; cases this
  · exact hall w hw

theorem shallow_bareCtor (Γ : List IndDecl) : ShallowAtom (Value.bareCtor Γ) where
  bot := rfl
  ind _ _ _ ps _ _ := by cases ps <;> rfl
  borrow _ _ _ := rfl
  gloan _ _ _ := rfl
  succ _ _ := rfl

theorem shallow_badCapture : ShallowAtom Value.badCapture where
  bot := rfl
  ind _ _ _ _ _ _ := rfl
  borrow _ _ _ := rfl
  gloan _ _ _ := rfl
  succ _ _ := rfl

theorem shallow_rdLoan (l : Nat) : ShallowAtom (Value.rdLoan l) where
  bot := rfl
  ind _ _ _ _ _ _ := rfl
  borrow _ _ _ := rfl
  gloan _ _ _ := rfl
  succ _ _ := rfl

theorem shallow_sealedHint (Γ : List IndDecl) : ShallowAtom (fun a => a.isSealed && !a.topHintFree Γ) where
  bot := rfl
  ind _ _ _ _ _ _ := rfl
  borrow _ _ _ := rfl
  gloan _ _ _ := rfl
  succ _ _ := rfl

theorem shallow_dataCtorBad (Γ : List IndDecl) : ShallowAtom (dataCtorBad Γ) where
  bot := rfl
  ind _ _ _ _ _ _ := rfl
  borrow _ _ _ := rfl
  gloan _ _ _ := rfl
  succ _ _ := rfl

theorem shallow_refMisplaced : ShallowAtom (fun
    | .tRef A => A.isRefV
    | .tInd _ ps => ps.any Value.isRefV
    | .ind _ _ _ ps _ => ps.any Value.isRefV
    | .tEq A a b => A.isRefV || a.isRefV || b.isRefV
    | _ => false) where
  bot := rfl
  ind _ _ _ _ _ _ := rfl
  borrow _ _ _ := rfl
  gloan _ _ _ := rfl
  succ _ _ := rfl

theorem shallow_abs (σ : Nat) : ShallowAtom (· == Value.abs σ) where
  bot := rfl
  ind _ _ _ _ _ _ := rfl
  borrow _ _ _ := rfl
  gloan _ _ _ := rfl
  succ _ _ := rfl

/-- The write changes a binding's value only: its stored and deferred types are the old ones. -/
theorem bind_setAtE (env : Env) (p : Pos) (v : Value) (f i : Nat) :
    ((Env.setAtE env p v)[f]?.bind (·.binds[i]?)).map (fun b => (b.ty, b.lazyTy)) =
      (env[f]?.bind (·.binds[i]?)).map (fun b => (b.ty, b.lazyTy)) := by
  cases p with
  | temp f' i' =>
    simp only [Env.setAtE, Array.getElem?_modify]
    by_cases h : f' = f
    · subst h; simp only [if_true]; cases env[f']? <;> rfl
    · simp only [h, if_false]
  | bind f' i' =>
    simp only [Env.setAtE, Array.getElem?_modify]
    by_cases h : f' = f
    · subst h; simp only [if_true]
      cases env[f']? with
      | none => rfl
      | some fr =>
        simp only [Option.map_some, Option.bind_some, Array.getElem?_modify]
        by_cases h2 : i' = i
        · subst h2; simp only [if_true]; cases fr.binds[i']? <;> rfl
        · simp only [h2, if_false]
    · simp only [h, if_false]

/-- A position's stored type is unchanged by the write. -/
theorem posTyM_setAtE (dm : DataModel) (C : CodeMeaning) (Γ : List IndDecl) (ρ : Assignment) (st : MState)
    (p : Pos) (v : Value) (q : Pos) :
    MState.posTyM dm C Γ ρ { st with env := Env.setAtE st.env p v } q = MState.posTyM dm C Γ ρ st q := by
  cases q with
  | temp f i => rfl
  | bind f i =>
    have h := bind_setAtE st.env p v f i
    simp only [MState.posTyM]
    revert h
    cases e1 : (Env.setAtE st.env p v)[f]?.bind (·.binds[i]?) <;>
      cases e2 : st.env[f]?.bind (·.binds[i]?) <;> intro h <;> simp only [Option.map_some, Option.map_none,
        reduceCtorEq, Option.some.injEq, Prod.mk.injEq] at h
    · rfl
    · rename_i b' b; simp only; rw [h.1, h.2]

/-- **The unknowns the state names after the write it named before** (the write removes a part). -/
theorem refd_setAtE {st : MState} {pos : Pos} {steps : List Step} {v' : Value} (hp : pos ∈ allPos st.env)
    (hv : Value.updAt (fun _ => .bot) steps (valAt st.env pos) = some v') :
    ∀ {σ}, ({ st with env := Env.setAtE st.env pos v' } : MState).Refd σ → st.Refd σ := by
  intro σ h
  induction h with
  | val w hw ha =>
    rcases mem_values_setAtE hw with rfl | hw
    · exact .val _ (List.mem_map.mpr ⟨pos, hp, rfl⟩) (anyAtom_of_updAt_bot (shallow_abs _) steps _ _ hv ha)
    · exact .val w hw ha
  | ty f i b T hb hT ha =>
    have e := bind_setAtE st.env pos v' f i
    rw [hb] at e
    cases e2 : st.env[f]?.bind (·.binds[i]?) with
    | none => rw [e2] at e; cases e
    | some b₀ =>
      rw [e2] at e; simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at e
      exact .ty f i b₀ T e2 (e.1 ▸ hT) ha
  | lazyTy f i b P ws j hb hT ha =>
    have e := bind_setAtE st.env pos v' f i
    rw [hb] at e
    cases e2 : st.env[f]?.bind (·.binds[i]?) with
    | none => rw [e2] at e; cases e
    | some b₀ =>
      rw [e2] at e; simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at e
      exact .lazyTy f i b₀ P ws j e2 (e.2 ▸ hT) ha
  | goal G hG ha => exact .goal G hG ha
  | neutral n σ' hn ha => exact .neutral n σ' hn ha
  | eta σ' w he ha => exact .eta σ' w he ha
  | dep σ' T _ hT ha ih => exact .dep σ' T ih hT ha

/-! ## Where the write leaves a `⊥` -/

theorem getElem?_set_ne' {α : Type _} (fs : List α) {i j : Nat} (h : j ≠ i) (a : α) : (fs.set i a)[j]? = fs[j]? := by
  rw [List.getElem?_set]; simp [Ne.symm h]

/-- A step into a constructor value whose field `i` was replaced: the old step, or the replaced
field at the step's key `(c, i)`. -/
theorem stepV_ind_set (x : Step) (ty : String) (c : Nat) (hh : Hint) (ps fs : List Value) (i : Nat) (w w' : Value)
    (hw : fs[i]? = some w) (u : Value) (h : stepV x (.ind ty c hh ps (fs.set i w')) = some u) :
    stepV x (.ind ty c hh ps fs) = some u ∨ (x.key = some (c, i) ∧ u = w' ∧ stepV x (.ind ty c hh ps fs) = some w) := by
  have hi : i < fs.length := (List.getElem?_eq_some_iff.mp hw).1
  cases x with
  | deref => simp [stepV] at h
  | proj j =>
    cases c with
    | succ _ => simp [stepV] at h
    | zero =>
      simp only [stepV] at h ⊢
      by_cases hj : j = i
      · subst hj
        rw [List.getElem?_set_self hi] at h
        simp only [Option.some.injEq] at h
        exact .inr ⟨rfl, h.symm, hw⟩
      · rw [getElem?_set_ne' fs hj] at h; exact .inl h
  | field g =>
    simp only [stepV] at h ⊢
    split at h
    · rename_i hc
      simp only [hc, if_true]
      by_cases hj : g.idx = i
      · rw [hj, List.getElem?_set_self hi] at h
        simp only [Option.some.injEq] at h
        simp only [Bool.and_eq_true, beq_iff_eq] at hc
        refine .inr ⟨by simp [Step.key, hc.2, hj], h.symm, by rw [hj]; exact hw⟩
      · rw [getElem?_set_ne' fs hj] at h; exact .inl h
    · cases h

/-- **A `⊥` after the write is an old one, or the written one**: following a path to `⊥` in the
written value follows it in the old, unless the path is the written one (by key). -/
theorem follow_updAt_bot : ∀ (steps : List Step) (v v' : Value), Value.updAt (fun _ => .bot) steps v = some v' →
    ∀ path, v'.follow path = some .bot → v.follow path = some .bot ∨ walkKey path = walkKey steps
  | [], v, v', h, path, hf => by
    simp only [Value.updAt, Option.some.injEq] at h; subst h
    cases path with
    | nil => exact .inr rfl
    | cons s ps => simp [Value.follow, stepV] at hf
  | st :: ss, v, v', h, path, hf => by
    cases v with
    | gloan m w =>
      simp only [Value.updAt] at h
      obtain ⟨w', hw', rfl⟩ := Option.map_eq_some_iff.mp h
      cases path with
      | nil => simp [Value.follow] at hf
      | cons s ps =>
        rw [follow_gloan_cons] at hf ⊢
        exact follow_updAt_bot (st :: ss) w w' hw' (s :: ps) hf
    | borrow m w =>
      cases st with
      | deref =>
        simp only [Value.updAt] at h
        obtain ⟨w', hw', rfl⟩ := Option.map_eq_some_iff.mp h
        cases path with
        | nil => simp [Value.follow] at hf
        | cons s ps =>
          cases s with
          | deref =>
            simp only [Value.follow, stepV, Option.bind_some] at hf ⊢
            rcases follow_updAt_bot ss w w' hw' ps hf with h1 | h1
            · exact .inl h1
            · right; simp [walkKey] at h1 ⊢; exact h1
          | proj _ | field _ => simp [Value.follow, stepV] at hf
      | proj _ | field _ => simp [Value.updAt] at h
    | succ w =>
      cases st with
      | proj i =>
        cases i with
        | zero =>
          simp only [Value.updAt] at h
          obtain ⟨w', hw', rfl⟩ := Option.map_eq_some_iff.mp h
          cases path with
          | nil => simp [Value.follow] at hf
          | cons s ps =>
            cases s with
            | proj j =>
              cases j with
              | zero =>
                simp only [Value.follow, stepV, Option.bind_some] at hf ⊢
                rcases follow_updAt_bot ss w w' hw' ps hf with h1 | h1
                · exact .inl h1
                · right; simp [walkKey] at h1 ⊢; exact h1
              | succ _ => simp [Value.follow, stepV] at hf
            | deref | field _ => simp [Value.follow, stepV] at hf
        | succ _ => simp [Value.updAt] at h
      | deref | field _ => simp [Value.updAt] at h
    | ind ty c hh ps fs =>
      obtain ⟨i, w, w', hci, hw, hw', rfl⟩ : ∃ i w w', st.key = some (c, i) ∧ fs[i]? = some w ∧
          Value.updAt (fun _ => .bot) ss w = some w' ∧ v' = .ind ty c hh ps (fs.set i w') := by
        cases st with
        | deref => simp [Value.updAt] at h
        | proj i =>
          cases c with
          | succ _ => simp [Value.updAt] at h
          | zero =>
            simp only [Value.updAt] at h
            split at h
            · rename_i w hw
              obtain ⟨w', hw', rfl⟩ := Option.map_eq_some_iff.mp h
              exact ⟨i, w, w', rfl, hw, hw', rfl⟩
            · cases h
        | field g =>
          simp only [Value.updAt] at h
          split at h
          · rename_i w hw
            obtain ⟨w', hw', rfl⟩ := Option.map_eq_some_iff.mp h
            split at hw
            · rename_i hc
              simp only [Bool.and_eq_true, beq_iff_eq] at hc
              exact ⟨g.idx, w, w', by simp [Step.key, hc.2], hw, hw', rfl⟩
            · cases hw
          · cases h
      cases path with
      | nil => simp [Value.follow] at hf
      | cons x rest =>
        simp only [Value.follow] at hf ⊢
        obtain ⟨u, hu, hfu⟩ := Option.bind_eq_some_iff.mp hf
        rcases stepV_ind_set x ty c hh ps fs i w w' hw u hu with h1 | ⟨hk, rfl, h1⟩
        · left; rw [h1, Option.bind_some]; exact hfu
        · rcases follow_updAt_bot ss w u hw' rest hfu with h2 | h2
          · left; rw [h1, Option.bind_some]; exact h2
          · right; simp only [walkKey, List.map_cons, List.cons.injEq] at h2 ⊢; exact ⟨hk.trans hci.symm, h2⟩
    | _ => simp [Value.updAt] at h
termination_by steps v => (steps.length, sizeOf v)

/-! ## The clauses one by one -/

/-- (WF1)'s first half at the written position: a borrow's content stays borrow-free, any other
value too. -/
def borrowWhole : Value → Prop
  | .borrow _ w => ¬ w.hasBorrow
  | v => ¬ v.hasBorrow

theorem borrowWhole_eq (v : Value) :
    borrowWhole v = (match v with | .borrow _ w => ¬ w.hasBorrow | v => ¬ v.hasBorrow) := by
  cases v <;> rfl

theorem wf1_updAt_bot {v v' : Value} {steps : List Step} (h : Value.updAt (fun _ => .bot) steps v = some v')
    (hwf : borrowWhole v) : borrowWhole v' := by
  rw [borrowWhole_eq] at hwf ⊢
  have hb : ∀ {a b : Value} {ss : List Step}, Value.updAt (fun _ => .bot) ss a = some b → ¬ a.hasBorrow → ¬ b.hasBorrow :=
    fun {a b ss} hab ha hb' => ha (anyAtom_of_updAt_bot shallow_borrow ss a b hab hb')
  cases steps with
  | nil =>
    simp only [Value.updAt, Option.some.injEq] at h; subst h
    simp [Value.hasBorrow, Value.anyAtom]
  | cons st ss =>
    cases v with
    | borrow m w =>
      cases st with
      | deref =>
        simp only [Value.updAt] at h
        obtain ⟨w', hw', rfl⟩ := Option.map_eq_some_iff.mp h
        exact hb hw' hwf
      | proj _ | field _ => simp [Value.updAt] at h
    | _ =>
      have htop := updAt_bot_top h
      cases v' with
      | borrow m w' => simp [topLabel] at htop
      | _ => exact hb h hwf

/-- A pointwise sublist of a list's images gives a sublist of their concatenations. -/
theorem flatMap_sublist {α β : Type _} {f g : α → List β} : ∀ (xs : List α), (∀ x ∈ xs, (f x).Sublist (g x)) →
    (xs.flatMap f).Sublist (xs.flatMap g)
  | [], _ => List.Sublist.refl _
  | x :: xs, h => by
    simp only [List.flatMap_cons]
    exact (h x (List.mem_cons_self ..)).append (flatMap_sublist xs fun y hy => h y (List.mem_cons_of_mem _ hy))

/-- After the write, Ω's loans outside sealed programs are a sublist of before. -/
theorem outerLoans_values_setAtE {env : Env} {pos : Pos} {steps : List Step} {v' : Value} (hp : pos ∈ allPos env)
    (hv : Value.updAt (fun _ => .bot) steps (valAt env pos) = some v') :
    ((Env.values (Env.setAtE env pos v')).flatMap Value.outerLoans).Sublist
      ((Env.values env).flatMap Value.outerLoans) := by
  simp only [Env.values, allPos_setAtE, List.flatMap_map]
  apply flatMap_sublist
  intro q _
  by_cases hq : q = pos
  · subst hq; rw [valAt_setAtE_self v' hp]; exact outerLoans_updAt_bot steps _ _ hv
  · rw [valAt_setAtE_other env pos q v' hq]; exact List.Sublist.refl _

/-- (WF14) after the write: a `⊥` is an old one (no live borrow lent strictly above it before,
and the sites are the same), or the written one (the access cleared every site over the place). -/
theorem wf14_setAtE {env : Env} {pos : Pos} {steps : List Step} {v' : Value} (hp : pos ∈ allPos env)
    (hv : Value.updAt (fun _ => .bot) steps (valAt env pos) = some v') (h14 : WF14 env)
    (hlive : ∀ l, liveLoan (Env.setAtE env pos v') l = liveLoan env l)
    (hsites : ∀ l, liveLoan env l = true → ∀ x, x ∈ Env.sitesOf (Env.setAtE env pos v') l ↔ x ∈ Env.sitesOf env l)
    (hclear : ∀ l, liveLoan env l = true → ∀ x ∈ Env.sitesOf env l, x.pos = pos → dataHit steps x.path = false) :
    WF14 (Env.setAtE env pos v') := by
  intro q path hq l hl x hx hxq k hk hkey
  rw [hlive] at hl
  have hx' := (hsites l hl x).mp hx
  by_cases hqp : q = pos
  · subst hqp
    rw [valAt_setAtE_self v' hp] at hq
    rcases follow_updAt_bot steps _ v' hv path hq with h1 | h1
    · exact h14 q path h1 l hl x hx' hxq k hk hkey
    · have hd := hclear l hl x hx' hxq
      simp only [dataHit, Bool.or_eq_false_iff] at hd
      have : (walkKey x.path).isPrefixOf (walkKey steps) = true := by
        rw [hkey, ← h1, walkKey, walkKey]
        exact List.isPrefixOf_iff_prefix.mpr ((List.take_prefix k path).map Step.key)
      -- a positional prefix is an erased one (`KeyBridge`, the free direction)
      have h' := pathKey_prefix_of_walkKey (List.isPrefixOf_iff_prefix.mp this)
      rw [← List.isPrefixOf_iff_prefix, hd.1] at h'; cases h'
  · rw [valAt_setAtE_other env pos q v' hqp] at hq
    exact h14 q path hq l hl x hx' hxq k hk hkey

/-- A borrow after the write was that borrow before, its content's loans a sublist. -/
theorem borrow_updAt_bot {steps : List Step} {v : Value} {m : Nat} {w : Value}
    (h : Value.updAt (fun _ => .bot) steps v = some (.borrow m w)) :
    ∃ w₀, v = .borrow m w₀ ∧ ∀ l ∈ w.loans, l ∈ w₀.loans := by
  cases steps with
  | nil => simp [Value.updAt] at h
  | cons st ss =>
    cases v with
    | borrow m' w₀ =>
      cases st with
      | deref =>
        simp only [Value.updAt] at h
        obtain ⟨w', hw', he⟩ := Option.map_eq_some_iff.mp h
        simp only [Value.borrow.injEq] at he
        obtain ⟨rfl, rfl⟩ := he
        exact ⟨w₀, rfl, fun l hl => (loans_updAt_bot ss w₀ _ hw').subset hl⟩
      | proj _ | field _ => simp [Value.updAt] at h
    | gloan m' w₀ =>
      simp only [Value.updAt] at h
      obtain ⟨w', -, he⟩ := Option.map_eq_some_iff.mp h; cases he
    | succ w₀ =>
      cases st with
      | proj i =>
        cases i with
        | zero =>
          simp only [Value.updAt] at h
          obtain ⟨w', -, he⟩ := Option.map_eq_some_iff.mp h; cases he
        | succ _ => simp [Value.updAt] at h
      | deref | field _ => simp [Value.updAt] at h
    | ind ty c hh ps fs =>
      obtain ⟨-, w₁, w₁', -, -, he⟩ := updAt_ind_inv h; cases he
    | _ => simp [Value.updAt] at h

/-! ## Writing `⊥` over `⊥` (the reference's drop of a place already moved, docs/31 D52) -/

/-- Writing a binding's own value back changes nothing. -/
theorem setAtE_self_bind (env : Env) (f i : Nat) (hp : Pos.bind f i ∈ allPos env) :
    Env.setAtE env (.bind f i) (valAt env (.bind f i)) = env := by
  obtain ⟨fr, b, hf, hb⟩ := mem_allPos_bind env f i hp
  have hv : valAt env (.bind f i) = b.val := by rw [valAt_bind_eq, hf]; simp [hb]
  rw [hv]
  simp only [Env.setAtE]
  apply Array.ext_getElem?
  intro j
  rw [Array.getElem?_modify]
  split
  · rename_i h; subst h
    rw [hf]
    simp only [Option.map_some, Option.some.injEq]
    have : fr.binds.modify i (fun x => { x with val := b.val }) = fr.binds := by
      apply Array.ext_getElem?
      intro k
      rw [Array.getElem?_modify]
      split
      · rename_i h; subst h; rw [hb]; rfl
      · rfl
    rw [this]
  · rfl

/-- Writing `⊥` where `⊥` is changes nothing. -/
theorem updAt_bot_self : ∀ (steps : List Step) (v : Value), v.follow steps = some .bot →
    Value.updAt (fun _ => .bot) steps v = some v
  | [], v, h => by simp only [Value.follow, Option.some.injEq] at h; subst h; simp [Value.updAt]
  | st :: ss, v, h => by
    cases v with
    | gloan m w =>
      rw [follow_gloan_cons] at h
      simp only [Value.updAt, updAt_bot_self (st :: ss) w h, Option.map_some]
    | borrow m w =>
      cases st with
      | deref =>
        simp only [Value.follow, stepV, Option.bind_some] at h
        simp only [Value.updAt, updAt_bot_self ss w h, Option.map_some]
      | proj _ | field _ => simp [Value.follow, stepV] at h
    | succ w =>
      cases st with
      | proj i =>
        cases i with
        | zero =>
          simp only [Value.follow, stepV, Option.bind_some] at h
          simp only [Value.updAt, updAt_bot_self ss w h, Option.map_some]
        | succ _ => simp [Value.follow, stepV] at h
      | deref | field _ => simp [Value.follow, stepV] at h
    | ind ty c hh ps fs =>
      cases st with
      | deref => simp [Value.follow, stepV] at h
      | proj i =>
        cases c with
        | succ _ => simp [Value.follow, stepV] at h
        | zero =>
          simp only [Value.follow, stepV] at h
          obtain ⟨w, hw, hf⟩ := Option.bind_eq_some_iff.mp h
          simp only [Value.updAt, hw, updAt_bot_self ss w hf, Option.map_some, Option.some.injEq]
          obtain ⟨hlt, rfl⟩ := List.getElem?_eq_some_iff.mp hw
          rw [List.set_getElem_self]
      | field g =>
        simp only [Value.follow, stepV] at h
        split at h
        · obtain ⟨w, hw, hf⟩ := Option.bind_eq_some_iff.mp h
          rename_i hc
          simp only [Value.updAt, hc, if_true, hw, updAt_bot_self ss w hf, Option.map_some, Option.some.injEq]
          obtain ⟨hlt, rfl⟩ := List.getElem?_eq_some_iff.mp hw
          rw [List.set_getElem_self]
        · simp at h
    | proof =>
      exfalso
      cases st with
      | deref => simp [Value.follow, stepV] at h
      | proj _ | field _ =>
        simp only [Value.follow, stepV, Option.bind_some] at h
        cases follow_proof ss _ h
    | _ => simp [Value.follow, stepV] at h
termination_by steps v => (steps.length, sizeOf v)

/-- **No live borrow has a site at, over or under a `⊥`**: over it by (WF14); at or under it no site
can be, since nothing along a site's own path is `⊥` (`site_not_bot`). The comparison is the
reference's (`dataHit`, `*` erased); the checker's clauses compare step by step, and (WF1) makes
the two agree at one position (`KeyBridge`, docs/31 D67). -/
theorem clear_of_bot {env : Env} {pos : Pos} {steps : List Step} (h1 : WF1 env) (h14 : WF14 env)
    (hbot : (valAt env pos).follow steps = some .bot) :
    ∀ l, liveLoan env l = true → ∀ x ∈ Env.sitesOf env l, x.pos = pos → dataHit steps x.path = false := by
  intro l hl x hx hxp
  have hx' := hx
  simp only [Env.sitesOf, List.mem_flatMap] at hx'
  obtain ⟨p, hpm, hxv⟩ := hx'
  have hpp : x.pos = p := (sitesOf_prefix l p [] _ x hxv).1
  rw [hxp] at hpp; subst hpp
  obtain ⟨ψ₀, hxψ, hnb⟩ := site_not_bot l pos [] _ x hxv
  simp only [List.nil_append] at hxψ
  have hv := wf1At_of_WF1 h1 hpm
  have hsx := site_shaped hv hxv
  have hws := walk_shaped hv hbot
  cases e : dataHit steps x.path
  · rfl
  · exfalso
    simp only [dataHit, Bool.or_eq_true, List.isPrefixOf_iff_prefix] at e
    -- at or under the `⊥`: nothing along a site's path is `⊥`
    have hunder : ¬ pathKey steps <+: pathKey x.path := fun e' =>
      hnb steps (by rw [← hxψ]; exact walkKey_prefix_of_walk_site hws hsx e') hbot
    rcases e with e | e
    · by_cases heq : pathKey x.path = pathKey steps
      · exact hunder (by rw [heq]; exact List.prefix_refl _)
      · obtain ⟨e, hne⟩ := walkKey_strict_of_site_walk hsx hws e heq
        obtain ⟨t, ht⟩ := id e
        have hlt : x.path.length < steps.length := by
          have h1 := congrArg List.length ht
          simp only [walkKey, List.length_append, List.length_map] at h1
          rcases t with _ | ⟨a, t⟩
          · simp at ht; exact absurd ht hne
          · simp at h1; omega
        apply h14 pos steps hbot l hl x hx hxp x.path.length hlt
        have hp := List.prefix_iff_eq_take.mp e
        simp only [walkKey, List.length_map] at hp
        rw [walkKey, walkKey, List.map_take]; exact hp
    · exact hunder e

/-! ## The assembly -/

section
variable (K : RunCtx) (ρ : Assignment)

/-- **`Good` after the write of `⊥`** (L3's other half): the typed assignment and the types are
untouched, the unknowns named are fewer (`refd_setAtE`), the written position's meaning is the old
with a part moved out, which keeps partial membership, and every clause of well-formedness
survives the removal of a part (the borrows held, their liveness and their sites are unchanged
after the access, `hclear`). PROVED (docs/31 D50). -/
theorem botWrite_good (st : MState) (pos : Pos) (steps : List Step) (v' : Value)
    (hg : Good K.dm K.M K.Γ ρ st) (hp : pos ∈ allPos st.env)
    (hv : Value.updAt (fun _ => .bot) steps (valAt st.env pos) = some v')
    (hroot : steps = [] → Env.shape st.env pos = none)
    (hclear : ∀ l, liveLoan st.env l = true → ∀ x ∈ Env.sitesOf st.env l, x.pos = pos →
      dataHit steps x.path = false)
    (hplain : (valAt st.env pos).anyAtom (Value.bareCtor K.Γ) = false ∧
      (valAt st.env pos).anyAtom (fun a => a.isSealed && !a.topHintFree K.Γ) = false)
    (hnat : ∀ ψ, NatAlong K.dm K.M K.Γ ρ ψ steps (valAt st.env pos)) :
    Good K.dm K.M K.Γ ρ { st with env := Env.setAtE st.env pos v' } := by
  obtain ⟨hta, hmem, h1, h2, h3, h4, h6, h7, h8, h9, h10, h11, h12, h14, h15, h16⟩ := hg
  have hv0 : valAt st.env pos ∈ Env.values st.env := List.mem_map.mpr ⟨pos, hp, rfl⟩
  have hhold : ∀ l, v'.holdsBorrow l = (valAt st.env pos).holdsBorrow l :=
    holdsBorrow_updAt_bot (h1.1 pos hp)
      (fun he => by rw [← shapeOf_eq_topLabel, ← shape_eq_shapeOf]; exact hroot he) hv
  have hlive := liveLoan_setAtE hp hhold
  have hshape : ∀ q, Env.shape (Env.setAtE st.env pos v') q = Env.shape st.env q := by
    intro q
    by_cases hq : q = pos
    · rw [hq, shape_eq_shapeOf, shape_eq_shapeOf, valAt_setAtE_self v' hp, shapeOf_eq_topLabel, shapeOf_eq_topLabel]
      rcases steps with _ | ⟨st0, ss⟩
      · simp only [Value.updAt, Option.some.injEq] at hv
        subst hv
        have := hroot rfl
        rw [shape_eq_shapeOf, shapeOf_eq_topLabel] at this
        rw [this]; rfl
      · exact updAt_bot_top hv
    · exact shape_setAtE_other st.env pos q v' hq
  have hsites : ∀ l, liveLoan st.env l = true → ∀ x,
      x ∈ Env.sitesOf (Env.setAtE st.env pos v') l ↔ x ∈ Env.sitesOf st.env l :=
    fun l hl => sitesOf_setAtE_bot hp hv l (hclear l hl)
  have hrefd : ∀ {σ}, ({ st with env := Env.setAtE st.env pos v' } : MState).Refd σ → st.Refd σ := fun h => refd_setAtE hp hv h
  have hposTy := posTyM_setAtE K.dm K.M K.Γ ρ st pos v'
  have hp' : pos ∈ allPos (Env.setAtE st.env pos v') := by rw [allPos_setAtE]; exact hp
  have hsub := outerLoans_values_setAtE hp hv
  refine ⟨⟨fun σ h hlt => hta.mem σ (hrefd h) hlt, hta.neutral, hta.eta, hta.refs⟩,
    ⟨fun φ hφ q T hT => ?_, fun σ h hlt => hmem.absTy σ (hrefd h) hlt, hmem.goal⟩, ?_⟩
  · have hφ' : TypedFuture K.dm K.M K.Γ ρ st φ := fun q' l hq' T' hT' =>
      hφ q' l (by rw [hshape]; exact hq') T' (by rw [hposTy]; exact hT')
    rw [hposTy] at hT
    by_cases hqp : q = pos
    · subst hqp
      have old := hmem.pos φ hφ' q T hT
      show DataModel.pmem K.dm K.Γ (Env.mean K.dm K.M K.Γ ρ φ (Env.setAtE st.env q v') q) T
      rw [mean_eq_valAt K.dm K.M K.Γ ρ _ _ _ hp', hintAt_setAtE, valAt_setAtE_self v' hp]
      rw [mean_eq_valAt K.dm K.M K.Γ ρ _ _ _ hp] at old
      exact pmem_moved_part (movedOf_mean_updAt K ρ φ steps _ _ v' hv hplain.1 hplain.2 (hnat φ)).1 old
    · show DataModel.pmem K.dm K.Γ (Env.mean K.dm K.M K.Γ ρ φ (Env.setAtE st.env pos v') q) T
      rw [mean_setAtE_other K.dm K.M K.Γ ρ st.env pos q v' φ hqp]
      exact hmem.pos φ hφ' q T hT
  have hb6 : ∀ {f i : Nat} {b : Binding}, (Env.setAtE st.env pos v')[f]?.bind (·.binds[i]?) = some b →
      ∃ b₀, st.env[f]?.bind (·.binds[i]?) = some b₀ ∧ b.ty = b₀.ty ∧ b.lazyTy = b₀.lazyTy := by
    intro f i b hb
    have e := bind_setAtE st.env pos v' f i
    rw [hb] at e
    cases e2 : st.env[f]?.bind (·.binds[i]?) with
    | none => rw [e2] at e; cases e
    | some b₀ =>
      rw [e2] at e; simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at e
      exact ⟨b₀, rfl, e.1, e.2⟩
  refine ⟨⟨fun q hq => ?_, fun q hq q' hq' l hl hl' => ?_⟩, ⟨fun w hw l hl => ?_, fun l => ?_⟩, ?_, fun w hw => ?_,
    ⟨fun σ h => h6.1 σ (hrefd h), h6.2.1, h6.2.2.1, h6.2.2.2.1, fun w hw l hl => ?_⟩,
    fun q T hT f i b hq hb A hA => ?_, ⟨fun w hw => ?_, fun f i b hb T hT => ?_, h8.2.2.1, h8.2.2.2⟩,
    fun q hq hne => ?_, values_anyAtom_setAtE (shallow_bareCtor K.Γ) hp hv h10,
    ⟨fun f i b hb => ?_, h11.2.1, h11.2.2.1, h11.2.2.2.1, h11.2.2.2.2⟩,
    fun k l hk hl x hx hxf y hy hyp hpre => ?_, wf14_setAtE hp hv h14 hlive hsites hclear,
    fun w hw l => values_anyAtom_setAtE (shallow_rdLoan l) hp hv (fun w hw => h15 w hw l) w hw,
    values_anyAtom_setAtE (shallow_sealedHint K.Γ) hp hv h16⟩
  · -- (WF1), borrows whole
    rw [allPos_setAtE] at hq
    by_cases hqp : q = pos
    · rw [hqp, valAt_setAtE_self v' hp]
      have hin : borrowWhole (valAt st.env pos) := by
        have := h1.1 pos hp
        revert this; generalize valAt st.env pos = x; intro hx; cases x <;> exact hx
      have := wf1_updAt_bot hv hin
      revert this; generalize v' = x; intro hx; cases x <;> exact hx
    · rw [valAt_setAtE_other st.env pos q v' hqp]; exact h1.1 q hq
  · -- (WF1), one holder
    rw [allPos_setAtE] at hq hq'; rw [hshape] at hl hl'
    exact h1.2 q hq q' hq' l hl hl'
  · -- (WF2), live
    rw [hlive]
    rcases mem_values_setAtE hw with rfl | hw
    · exact h2.1 _ hv0 l ((outerLoans_updAt_bot _ _ _ hv).subset hl)
    · exact h2.1 w hw l hl
  · -- (WF2), once
    exact Nat.le_trans (hsub.count_le l) (h2.2 l)
  · -- (WF3)
    refine Subrelation.wf (fun {l m} h => ?_) h3
    obtain ⟨q, hq, w, hqw, hl⟩ := h
    rw [allPos_setAtE] at hq
    by_cases hqp : q = pos
    · subst hqp
      rw [valAt_setAtE_self v' hp] at hqw; subst hqw
      obtain ⟨w₀, hw₀, hsub'⟩ := borrow_updAt_bot hv
      exact ⟨q, hq, w₀, hw₀, hsub' l hl⟩
    · rw [valAt_setAtE_other st.env pos q v' hqp] at hqw
      exact ⟨q, hq, w, hqw, hl⟩
  · -- (WF4)
    have := values_anyAtom_setAtE shallow_badCapture hp hv (fun w hw => by simpa using h4 w hw) w hw
    simp [this]
  · -- (WF6), loans below the counter
    rcases mem_values_setAtE hw with rfl | hw
    · exact h6.2.2.2.2 _ hv0 l ((loans_updAt_bot _ _ _ hv).subset hl)
    · exact h6.2.2.2.2 w hw l hl
  · -- (WF7)
    rw [hposTy] at hT
    obtain ⟨b₀, hb₀, hty, -⟩ := hb6 hb
    exact h7 q T hT f i b₀ hq hb₀ A (hty ▸ hA)
  · -- (WF8), values
    have := values_anyAtom_setAtE shallow_refMisplaced hp hv (fun w hw => h8.1 w hw) w hw
    exact this
  · -- (WF8), stored types
    obtain ⟨b₀, hb₀, hty, -⟩ := hb6 hb
    exact h8.2.1 f i b₀ hb₀ T (hty ▸ hT)
  · -- (WF9)
    rw [hposTy]; rw [allPos_setAtE] at hq
    by_cases hqp : q = pos
    · subst hqp
      rw [valAt_setAtE_self v' hp] at hne
      refine h9 q hp fun he => hne ?_
      have := outerLoans_updAt_bot _ _ _ hv
      rw [he] at this; exact List.eq_nil_of_sublist_nil this
    · rw [valAt_setAtE_other st.env pos q v' hqp] at hne; exact h9 q hq hne
  · -- (WF11), stored types
    obtain ⟨b₀, hb₀, hty, hlz⟩ := hb6 hb
    obtain ⟨ht, hl⟩ := h11.1 f i b₀ hb₀
    exact ⟨fun T hT => ht T (hty ▸ hT), fun P ws j hP => hl P ws j (hlz ▸ hP)⟩
  · -- (WF12)
    rw [hlive] at hk hl
    obtain ⟨z, hz, hzp, hzk, hzf⟩ := h12 k l hk hl x ((hsites k hk x).mp hx) hxf y ((hsites l hl y).mp hy) hyp hpre
    exact ⟨z, (hsites l hl z).mpr hz, hzp, hzk, hzf⟩

end

end Ochr.Meaning.Steps
