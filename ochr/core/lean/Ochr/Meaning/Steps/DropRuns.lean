import Ochr.Meaning.Steps.BotWriteRel

/-!
# The checker's drop of one place, taken apart (for `dropOne_step`'s assembly)

Inversions of the runs `dropOne_step` meets: `content?` (a read of the place, changing nothing),
`movedPlace` where the place exists (it returns it, changing nothing), and `dropAtJoin`'s cases.
-/

namespace Ochr.Meaning.Steps

open Ochr.Meaning

theorem runs_getAt_inv {pos : Pos} {st st' : MState} {b : Nat} {v : Value}
    (h : Runs (Ochr.getAt pos) st b v st') : st' = st ∧ v = valAt st.env pos := by
  obtain ⟨L, left, log, h⟩ := h
  cases pos <;> simp only [Ochr.getAt, runMachineL_bind, runMachineL_get, runMachineL_pure, Prod.mk.injEq,
    Outcome.ok.injEq] at h <;> exact ⟨h.1.2.symm, by rw [← h.1.1]; rfl⟩

/-- `content?` reads the place and changes nothing. -/
theorem runs_content?_inv {q : Place} {st st' : MState} {b : Nat} {o : Option Value}
    (h : Runs (Ochr.content? q) st b o st') :
    st' = st ∧ ∃ pos, ckVarPos st.env q.steps.1 = some pos ∧ o = (valAt st.env pos).follow q.steps.2 := by
  unfold Ochr.content? at h
  rcases hq : q.steps with ⟨i, ss⟩
  rw [hq] at h
  obtain ⟨pos, st₁, b₁, hv, h2⟩ := Runs.bind_inv h
  obtain ⟨hst₁, hpos⟩ := runs_varPos_inv hv
  subst hst₁
  obtain ⟨v, st₂, b₂, hg, h3⟩ := Runs.bind_inv h2
  obtain ⟨hst₂, hvv⟩ := runs_getAt_inv hg
  subst hst₂; subst hvv
  obtain ⟨L, left, log, h4⟩ := h3
  simp only [runMachineL_pure, Prod.mk.injEq, Outcome.ok.injEq] at h4
  exact ⟨h4.1.2.symm, pos, hpos, h4.1.1.symm⟩

/-- **The place exists: `movedPlace` returns it and changes nothing.** -/
theorem movedPlace_exists' (fuel : Nat) {st st₁ : MState} {q q' : Place} {pos : Pos} {w : Value} {b : Nat}
    (hpos : ckVarPos st.env q.steps.1 = some pos) (hw : (valAt st.env pos).follow q.steps.2 = some w)
    (h : Runs (Ochr.movedPlace (fuel + 1) q) st b q' st₁) : q' = q ∧ st₁ = st := by
  unfold Ochr.movedPlace at h
  obtain ⟨o, st₂, b₂, hc, h⟩ := Runs.bind_inv h
  obtain ⟨rfl, pos', hpos', rfl⟩ := runs_content?_inv hc
  rw [hpos] at hpos'
  cases hpos'
  rw [hw] at h
  obtain ⟨L, left, log, h⟩ := h
  simp only [Option.isSome_some, ↓reduceIte, runMachineL_pure, Prod.mk.injEq, Outcome.ok.injEq] at h
  exact ⟨h.1.1.symm, h.1.2.symm⟩

/-- A loop whose body never changes the state leaves it as it was. -/
theorem runs_forIn_keep {α : Type} (body : α → PUnit → M (ForInStep PUnit))
    (hb : ∀ x st b r st', Runs (body x ⟨⟩) st b r st' → st' = st) :
    ∀ (xs : List α) {st st' : MState} {b : Nat} {u : PUnit}, Runs (forIn xs ⟨⟩ body) st b u st' → st' = st
  | [], st, st', b, u, h => by
    obtain ⟨L, left, log, h⟩ := h
    simp only [List.forIn_nil, runMachineL_pure, Prod.mk.injEq, Outcome.ok.injEq] at h
    exact h.1.2.symm
  | x :: xs, st, st', b, u, h => by
    rw [List.forIn_cons] at h
    obtain ⟨r, st₁, b₁, h1, h2⟩ := Runs.bind_inv h
    have e1 := hb x st b r st₁ h1
    subst e1
    rcases r with ⟨⟩ | ⟨⟩
    · obtain ⟨L, left, log, h2⟩ := h2
      simp only [runMachineL_pure, Prod.mk.injEq, Outcome.ok.injEq] at h2
      exact h2.1.2.symm
    · exact runs_forIn_keep body hb xs h2

theorem runs_ppPlace_inv {q : Place} {st st' : MState} {b : Nat} {x : String}
    (h : Runs (Ochr.ppPlace q) st b x st') : st' = st := by
  obtain ⟨L, left, log, h⟩ := h
  simp only [Ochr.ppPlace, Ochr.topIdx, runMachineL_bind, runMachineL_get, runMachineL_pure, Prod.mk.injEq,
    Outcome.ok.injEq] at h
  exact h.1.2.symm

theorem runMachineL_modifyThe_log (g : Array LogEntry → Array LogEntry) (st : MState) (fuel : Nat)
    (L : Array LogEntry) :
    runMachineL (modifyThe (Array LogEntry) g : M Unit) st fuel L = (.ok () st, fuel, g L) := rfl

theorem runs_fire_inv {r : Rule} {m : Unit → String} {st st' : MState} {b : Nat} {u : Unit}
    (h : Runs (Ochr.fire r m) st b u st') : st' = st := by
  obtain ⟨L, left, log, h⟩ := h
  unfold Ochr.fire at h
  simp only [runMachineL_bind, runMachineL_get] at h
  split at h
  · split at h
    · (try simp only [runMachineL_modifyThe_log, runMachineL_pure] at h)
      split at h <;> first
        | (simp only [runMachineL_bind, runMachineL_modifyThe_log, runMachineL_pure, Prod.mk.injEq,
            Outcome.ok.injEq] at h; exact h.1.2.symm)
        | (simp only [Prod.mk.injEq, Outcome.ok.injEq] at h; exact h.1.2.symm)
    · (try simp only [runMachineL_pure] at h)
      split at h <;> first
        | (simp only [runMachineL_bind, runMachineL_modifyThe_log, runMachineL_pure, Prod.mk.injEq,
            Outcome.ok.injEq] at h; exact h.1.2.symm)
        | (simp only [Prod.mk.injEq, Outcome.ok.injEq] at h; exact h.1.2.symm)
  · (try simp only [runMachineL_pure] at h)
    split at h <;> first
      | (simp only [runMachineL_bind, runMachineL_modifyThe_log, runMachineL_pure, Prod.mk.injEq,
          Outcome.ok.injEq] at h; exact h.1.2.symm)
      | (simp only [Prod.mk.injEq, Outcome.ok.injEq] at h; exact h.1.2.symm)

/-- The cases of the checker's drop of one place (`Machine.dropAtJoin`): the place is missing,
`⊥` or `⋆` (nothing happens); it holds a borrow (its end); it is a copy (nothing happens); or it is
accessed, logged and written `⊥`. -/
theorem runs_dropAtJoin_inv {fuel : Nat} {q : Place} {st st' : MState} {b : Nat}
    (h : Runs (Ochr.dropAtJoin (fuel + 1) q) st b () st') :
    ∃ pos, ckVarPos st.env q.steps.1 = some pos ∧
      ((((valAt st.env pos).follow q.steps.2 = none ∨ (valAt st.env pos).follow q.steps.2 = some .bot ∨
          (valAt st.env pos).follow q.steps.2 = some .proof) ∧ st' = st) ∨
      (∃ l w, (valAt st.env pos).follow q.steps.2 = some (.borrow l w) ∧
        ∃ st₁ b₁ b₂, Runs (Ochr.logEffect q "moves") st b₁ () st₁ ∧ Runs (Ochr.endBorrow fuel l) st₁ b₂ () st') ∨
      (∃ v, (valAt st.env pos).follow q.steps.2 = some v ∧ v ≠ .bot ∧ v ≠ .proof ∧
        ∃ b₁, Runs (Ochr.copyRead fuel q) st b₁ true st') ∨
      (∃ v, (valAt st.env pos).follow q.steps.2 = some v ∧ (∀ l w, v ≠ .borrow l w) ∧ v ≠ .bot ∧ v ≠ .proof ∧
        ∃ st₁ st₂ st₃ b₁ b₂ b₃ b₄, Runs (Ochr.copyRead fuel q) st b₁ false st₁ ∧
          Runs (do Ochr.accessPath fuel q; Ochr.accessInside fuel q) st₁ b₂ () st₂ ∧
          Runs (Ochr.logEffect q "moves") st₂ b₃ () st₃ ∧ Runs (Ochr.setPlace q .bot) st₃ b₄ () st')) := by
  unfold Ochr.dropAtJoin at h
  obtain ⟨o, st₁, b₁, hc, hk⟩ := Runs.bind_inv h
  clear h
  obtain ⟨hst₁, pos, hpos, ho⟩ := runs_content?_inv hc
  rw [hst₁] at hk
  refine ⟨pos, hpos, ?_⟩
  rw [← ho]
  have h := hk
  clear hk
  have hpure : ∀ {st₀ : MState} {b₀ : Nat}, Runs (pure () : M Unit) st₀ b₀ () st' → st' = st₀ := by
    intro st₀ b₀ hp
    obtain ⟨L, left, log, hp⟩ := hp
    simp only [runMachineL_pure, Prod.mk.injEq, Outcome.ok.injEq] at hp
    exact hp.1.2.symm
  split at h
  · exact .inl ⟨.inl rfl, hpure h⟩
  · exact .inl ⟨.inr (.inl rfl), hpure h⟩
  · exact .inl ⟨.inr (.inr rfl), hpure h⟩
  · rename_i l w
    obtain ⟨_, st₂, b₂, hf, hk1⟩ := Runs.bind_inv h
    have e2 := runs_fire_inv hf
    rw [e2] at hk1
    obtain ⟨_, st₃, b₃, hl, hk2⟩ := Runs.bind_inv hk1
    exact .inr (.inl ⟨l, w, rfl, st₃, b₂, b₃, hl, hk2⟩)
  · rename_i _o v hbot hproof hborrow
    obtain ⟨c, st₂, b₂, hcr, hk1⟩ := Runs.bind_inv h
    cases c with
    | true =>
      simp only [if_true] at hk1
      have e := hpure hk1
      exact .inr (.inr (.inl ⟨v, rfl, fun e => hbot e, fun e => hproof e, b₁, by rw [e]; exact hcr⟩))
    | false =>
      simp only [Bool.false_eq_true, if_false] at hk1
      obtain ⟨g, st₃, b₃, hg, hk2⟩ := Runs.bind_inv hk1
      obtain ⟨L, left, log, hg⟩ := hg
      simp only [runMachineL_get, Prod.mk.injEq, Outcome.ok.injEq] at hg
      obtain ⟨⟨hg1, hg2⟩, -⟩ := hg
      rw [← hg2, ← hg1] at hk2
      obtain ⟨_, st₄, b₄, hloop, hk3⟩ := Runs.bind_inv hk2
      have e4 : st₄ = st₂ := by
        refine runs_forIn_keep _ (fun x st0 b0 r st1 hb => ?_) _ hloop
        obtain ⟨g', st5, b5, hg', hb2⟩ := Runs.bind_inv hb
        obtain ⟨L, left, log, hg'⟩ := hg'
        simp only [runMachineL_get, Prod.mk.injEq, Outcome.ok.injEq] at hg'
        obtain ⟨⟨hg1', hg2'⟩, -⟩ := hg'
        rw [← hg2', ← hg1'] at hb2
        split at hb2
        · obtain ⟨_, st6, b6, hpp, hb3⟩ := Runs.bind_inv hb2
          obtain ⟨_, st7, b7, herr, -⟩ := Runs.bind_inv hb3
          obtain ⟨L, left, log, herr⟩ := herr
          simp [runMachineL_err] at herr
        · obtain ⟨L, left, log, hb2⟩ := hb2
          simp only [runMachineL_pure, Prod.mk.injEq, Outcome.ok.injEq] at hb2
          exact hb2.1.2.symm
      rw [e4] at hk3
      obtain ⟨qs, st₅, b₅, hpp, hk4⟩ := Runs.bind_inv hk3
      rw [runs_ppPlace_inv hpp] at hk4
      obtain ⟨_, st₆, b₆, hf, hk5⟩ := Runs.bind_inv hk4
      rw [runs_fire_inv hf] at hk5
      simp only [← bind_assoc] at hk5
      obtain ⟨_, st₈, b₈, hk6, hset⟩ := Runs.bind_inv hk5
      obtain ⟨_, st₇, b₇, hacc, hlog⟩ := Runs.bind_inv hk6
      exact .inr (.inr (.inr ⟨v, rfl, fun l w e => hborrow l w e, fun e => hbot e, fun e => hproof e,
        st₂, st₇, st₈, b₁, b₆, b₇, b₈, hcr, hacc, hlog, hset⟩))

end Ochr.Meaning.Steps
