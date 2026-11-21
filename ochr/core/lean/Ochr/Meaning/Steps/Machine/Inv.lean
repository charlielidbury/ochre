import Ochr.Meaning.Steps.DropOne
import Ochr.Meaning.Steps.Machine.DecBack

/-!
# Inverting a successful run (the machine lane's tools)

A successful run of a `do` block is a successful run of each step at the state the previous step
left. These lemmas peel one step off a hypothesis `Runs (step >>= rest) st b y st'`: a read of the
state (`get`), a write (`modify`, `set`), a value (`pure`), a write of the log or the budget only (the
editor's notes, `tick`), a handler that only runs on failure (`onFail`, `locateErrors`). The
`runs_peel` tactic applies them, reduces the `do` block's local definitions and branches, and leaves
the real sub-runs to `Runs.bind_inv`.
-/

namespace Ochr.Meaning.Steps.Machine

open Ochr Ochr.Meaning Ochr.Meaning.Steps Ochr.Meaning.DecideScope Ochr.Meaning.Steps.Slice

variable {α β : Type}

theorem runs_get_bind {k : MState → M β} {st st' : MState} {b : Nat} {y : β} :
    Runs (get >>= k) st b y st' ↔ Runs (k st) st b y st' := Iff.rfl

theorem runs_modify_bind {g : MState → MState} {k : PUnit → M β} {st st' : MState} {b : Nat} {y : β} :
    Runs (modify g >>= k) st b y st' ↔ Runs (k ()) (g st) b y st' := Iff.rfl

theorem runs_set_bind {s₀ : MState} {k : PUnit → M β} {st st' : MState} {b : Nat} {y : β} :
    Runs (set s₀ >>= k) st b y st' ↔ Runs (k ()) s₀ b y st' := Iff.rfl

theorem runs_pure_bind' {a : α} {k : α → M β} {st st' : MState} {b : Nat} {y : β} :
    Runs (pure a >>= k) st b y st' ↔ Runs (k a) st b y st' := by rw [pure_bind]

theorem runs_err_bind {m : String} {k : α → M β} {st st' : MState} {b : Nat} {y : β} :
    Runs (err m >>= k) st b y st' ↔ False :=
  ⟨fun h => by obtain ⟨_, _, _, h₁, -⟩ := Runs.bind_inv h; exact runs_err_false h₁, False.elim⟩

theorem runs_err_iff {m : String} {st st' : MState} {b : Nat} {y : β} :
    Runs (err m : M β) st b y st' ↔ False := ⟨runs_err_false, False.elim⟩

theorem runs_exhausted_bind {m : String} {k : α → M β} {st st' : MState} {b : Nat} {y : β} :
    Runs (exhausted m >>= k) st b y st' ↔ False := by
  refine ⟨fun h => ?_, False.elim⟩
  obtain ⟨L, left, log, h⟩ := h
  simp [runMachineL_bind, runMachineL_exhausted] at h

theorem runs_exhausted_iff {m : String} {st st' : MState} {b : Nat} {y : β} :
    Runs (exhausted m : M β) st b y st' ↔ False := by
  refine ⟨fun h => ?_, False.elim⟩
  obtain ⟨L, left, log, h⟩ := h
  simp [runMachineL_exhausted] at h

theorem runs_pure_iff {a a' : α} {st st' : MState} {b : Nat} :
    Runs (pure a : M α) st b a' st' ↔ a' = a ∧ st' = st :=
  ⟨runs_pure_inv, fun ⟨h1, h2⟩ => ⟨#[], b, #[], by rw [h1, h2]; rfl⟩⟩

theorem runs_modify_inv {g : MState → MState} {st st' : MState} {b : Nat} {u : Unit}
    (h : Runs (modify g : M Unit) st b u st') : st' = g st := by
  obtain ⟨L, left, log, h⟩ := h
  simp only [runMachineL_modify, Prod.mk.injEq, Outcome.ok.injEq] at h
  exact h.1.2.symm

theorem runs_err_bind_false {α β : Type} {m : String} {k : α → M β} {st st' : MState} {b : Nat} {y : β}
    (h : Runs (err m >>= k) st b y st') : False := by
  obtain ⟨_, s₁, b₁, h₁, -⟩ := Runs.bind_inv h
  exact runs_err_false h₁

theorem runs_topIdx_inv {st st' : MState} {b f : Nat} (h : Runs (topIdx : M Nat) st b f st') :
    f = st.env.size - 1 ∧ st' = st := by
  unfold topIdx at h
  obtain ⟨_, s₁, b₁, h₁, h⟩ := Runs.bind_inv h
  obtain ⟨rfl, rfl⟩ := runs_get_inv h₁
  exact runs_pure_inv h

/-- A write of the log only (the editor's notes, the dev tooling's records). -/
theorem Runs.log_bind {g : Array LogEntry → Array LogEntry} {k : PUnit → M β} {st st' : MState} {b : Nat} {y : β}
    (h : Runs (modifyThe (Array LogEntry) g >>= k) st b y st') : Runs (k ()) st b y st' := by
  obtain ⟨L, left, log, h⟩ := h
  exact ⟨g L, left, log, h⟩

/-- `tick`: the budget only. -/
theorem runMachineL_tick_zero (st : MState) (L : Array LogEntry) :
    runMachineL tick st 0 L = (.exhausted "out of fuel", 0, L) := rfl

theorem runMachineL_tick_succ (st : MState) (k : Nat) (L : Array LogEntry) :
    runMachineL tick st (k + 1) L = (.ok () st, k, L) := rfl

theorem Runs.tick_bind {k : PUnit → M β} {st st' : MState} {b : Nat} {y : β}
    (h : Runs (tick >>= k) st b y st') : ∃ b', Runs (k ()) st b' y st' := by
  obtain ⟨L, left, log, h⟩ := h
  rw [runMachineL_bind] at h
  cases b with
  | zero => rw [runMachineL_tick_zero] at h; cases h
  | succ b => rw [runMachineL_tick_succ] at h; exact ⟨b, L, left, log, h⟩

/-- A handler run only on failure: a success is the body's. -/
theorem Runs.onFail_inv {x : M α} {c : M Unit} {st st' : MState} {b : Nat} {a : α}
    (h : Runs (onFail x c) st b a st') : Runs x st b a st' := by
  obtain ⟨L, f', l', e⟩ := runs_runAll h
  exact runs_of_runAll (runAll_onFail_ok e)

theorem Runs.noteStateAt_bind {β : Type} {l : Option Loc} {e : Bool} {v : Option (Value × Option Value)} {k : PUnit → M β}
    {st st' : MState} {b : Nat} {y : β} (h : Runs (noteStateAt l e v >>= k) st b y st') : Runs (k ()) st b y st' := by
  simp only [noteStateAt, bind_assoc, runs_get_bind] at h
  split at h
  · split at h
    · exact Runs.log_bind h
    · simpa only [runs_pure_bind'] using h
  · simpa only [runs_pure_bind'] using h

theorem Runs.atLoc_inv {α : Type} {l : Option Loc} {x : M α} {st st' : MState} {b : Nat} {a : α}
    (h : Runs (atLoc l x) st b a st') : Runs x st b a st' := by
  unfold atLoc at h
  split at h
  · exact h
  · obtain ⟨L, f', l', e⟩ := runs_runAll h
    refine runs_of_runAll (L := L) (f' := f') (l' := l') ?_
    unfold locateErrors tryCatchThe at e
    erw [DecideScope.runAll_tryCatch] at e
    revert e
    rcases e₀ : runAll x st ⟨b⟩ L with ⟨⟨e₁ | e₁ | ⟨c, s₁⟩, f₁⟩, l₁⟩
    · intro e; cases e
    · intro e; dsimp only at e; split at e <;> cases e
    · intro e; exact e

/-- Equal but for the editor's locations. -/
def LocsEq (a b : MState) : Prop := { a with locs := b.locs } = b

theorem LocsEq.refl (a : MState) : LocsEq a a := rfl

/-- Peel the noise steps off a run hypothesis: reads, writes, values, notes. -/
macro "peel" h:ident : tactic => `(tactic| repeat (first
  | (simp only [bind_assoc, runs_get_bind, runs_modify_bind, runs_set_bind, runs_pure_bind', pure_bind] at $h:ident)
  | (with_reducible replace $h:ident := Runs.log_bind $h:ident)
  | (with_reducible replace $h:ident := Runs.noteStateAt_bind $h:ident)))

theorem Runs.located_inv {α : Type} {t : Term} {x : M α} {fl : α → Option (Value × Option Value)} {ot : Option Bool}
    {st st' : MState} {b : Nat} {r : α}
    (h : Runs (located t x fl ot) st b r st') : ∃ st₀ b₀ st₁, LocsEq st st₀ ∧ Runs x st₀ b₀ r st₁ ∧ LocsEq st₁ st' := by
  simp only [located, locatedCore, bind_assoc, runs_get_bind] at h
  split at h <;> peel h <;> split at h <;> peel h <;> (try split at h) <;> (try simp only [bind_assoc] at h) <;>
    obtain ⟨r', s₁, b₁, hx, h2⟩ := Runs.bind_inv h <;> (try with_reducible replace hx := Runs.atLoc_inv hx) <;> peel h2
  all_goals (obtain ⟨rfl, rfl⟩ := runs_pure_inv h2; refine ⟨_, _, _, ?_, hx, ?_⟩)
  all_goals (unfold LocsEq; rfl)

theorem Runs.noteValue_inv {t : Term} {x : M (Value × Option Value)} {st st' : MState} {b : Nat}
    {r : Value × Option Value} (h : Runs (noteValue t x) st b r st') : ∃ b', Runs x st b' r st' := by
  unfold noteValue at h
  obtain ⟨r', s₁, b₁, hx, h2⟩ := Runs.bind_inv h
  repeat (any_goals first
    | (simp only [noteLoc, bind_assoc, runs_get_bind, pure_bind] at h2)
    | (with_reducible replace h2 := Runs.log_bind h2)
    | (split at h2))
  all_goals (obtain ⟨rfl, rfl⟩ := runs_pure_inv h2; exact ⟨b, hx⟩)

/-! ## The decision procedures the evaluation reads keep the state -/

theorem keep_getFlags : Keep getFlags := by unfold getFlags; keep_go
theorem keep_topIdx : Keep topIdx := by unfold topIdx; keep_go
theorem keep_varPos (i : Nat) : Keep (varPos i) := by
  unfold varPos; keep_go
  all_goals exact keep_topIdx
theorem keep_jErased (n : Nat) (P : Term) : Keep (jErased n P) := by
  unfold jErased; keep_go
  all_goals exact (decideKeep _).2.2.2.2.2.2.2.2.1 _ _ _ _
theorem keep_leafProof : ∀ (n : Nat) (t : Term) (v : Value), Keep (leafProof n t v)
  | 0, _, _ => by unfold leafProof; keep_go
  | n + 1, t, v => by
    unfold leafProof; keep_go
    all_goals first
      | exact keep_varPos _
      | exact keep_fieldIsProof _
      | exact keep_leafProof n _ _
      | exact (decideKeep _).2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 _
      | exact (decideKeep _).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2 _

theorem Runs.map_inv {α β : Type} {f : α → β} {x : M α} {st st' : MState} {b : Nat} {y : β}
    (h : Runs (f <$> x) st b y st') : ∃ a, Runs x st b a st' ∧ y = f a := by
  rw [map_eq_pure_bind] at h
  obtain ⟨a, s₁, b₁, h₁, h₂⟩ := Runs.bind_inv h
  obtain ⟨rfl, rfl⟩ := runs_pure_inv h₂
  exact ⟨a, h₁, rfl⟩

theorem DeclInfo.eq_any_of_beq {d : DeclInfo} (h : (d == .any) = true) : d = .any := by
  cases d <;> first | rfl | cases h

theorem preFlags_inv {t : Term} {d : DeclInfo} {st st' : MState} {b : Nat} {pre : Option (Bool × Bool)}
    (h : Runs (preFlags t d) st b pre st') (hany : d ≠ .any) (hpr : d.isProof = false)
    (hc : ∀ f as hd, t ≠ .call f as hd) : pre = some (false, false) ∧ st' = st := by
  have hs := runs_keep (keep_preFlags t d) h
  refine ⟨?_, hs⟩
  unfold preFlags at h
  peel h
  split at h
  · simp only [runs_err_bind] at h
  · peel h
    split at h
    · exact absurd (DeclInfo.eq_any_of_beq ‹_›) hany
    · peel h
      obtain ⟨rfl, -⟩ := runs_pure_inv h
      have hcall : (match t with | .call .. => true | _ => false) = false := by
        cases t <;> first | rfl | exact absurd rfl (hc _ _ _)
      simp [hpr]

end Ochr.Meaning.Steps.Machine
