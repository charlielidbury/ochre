import Ochr.Meaning.Steps.Statements
import Ochr.Meaning.RunLib

/-!
# The tables a decision reads only grow: the definitions (the machine lane)

`TablesGrow st st'` and `GrowsM x` (moved here from `Steps/MachineMono.lean`, which re-exports
them, so that the proofs under `Steps/Machine/` can be imported by it), and the state-relative
form the proofs use, `Machine.GrowsIn G x`: every successful run of `x` FROM A STATE WHOSE GLOBALS
AND DECLARATIONS ARE `G` only extends the tables. The relative form is what a private copy's exit
needs: `restoreKeep saved` and `exitWorld w` take the globals and the declarations from the saved
state, so they keep the tables only when the saved state has the current ones, which holds when
it was read (`get`, `enterWorld`) earlier in the same run. `GrowsM x ↔ ∀ G, GrowsIn G x`.

Nothing in this file mentions the model.
-/

namespace Ochr.Meaning.Steps

open Ochr Ochr.Meaning

/-- **The tables a decision reads only grow** from `st` to `st'`: the globals and the declarations
are kept, the frozen readings of the old unknowns are kept and new ones may follow, and the
counters of unknowns and labels are not lowered. -/
structure TablesGrow (st st' : MState) : Prop where
  globals : st'.globals = st.globals
  inds : st'.inds = st.inds
  size : st.absDecl.size ≤ st'.absDecl.size
  old : ∀ σ, σ < st.absDecl.size → st'.absDecl[σ]? = st.absDecl[σ]?
  nextAbs : st.nextAbs ≤ st'.nextAbs
  nextLoan : st.nextLoan ≤ st'.nextLoan

theorem TablesGrow.refl (st : MState) : TablesGrow st st :=
  ⟨rfl, rfl, Nat.le_refl _, fun _ _ => rfl, Nat.le_refl _, Nat.le_refl _⟩

theorem TablesGrow.trans {st₁ st₂ st₃ : MState} (h₁ : TablesGrow st₁ st₂) (h₂ : TablesGrow st₂ st₃) :
    TablesGrow st₁ st₃ :=
  ⟨h₂.globals.trans h₁.globals, h₂.inds.trans h₁.inds, Nat.le_trans h₁.size h₂.size,
    fun σ hσ => (h₂.old σ (Nat.lt_of_lt_of_le hσ h₁.size)).trans (h₁.old σ hσ),
    Nat.le_trans h₁.nextAbs h₂.nextAbs, Nat.le_trans h₁.nextLoan h₂.nextLoan⟩

/-- Every successful run of `x` only extends the tables. -/
def GrowsM {α : Type} (x : M α) : Prop := ∀ st b a st', Runs x st b a st' → TablesGrow st st'

theorem GrowsM.bind {α β : Type} {x : M α} {k : α → M β} (hx : GrowsM x) (hk : ∀ a, GrowsM (k a)) :
    GrowsM (x >>= k) := by
  intro st b c st' h
  obtain ⟨L, left, log, h⟩ := h
  rw [runMachineL_bind] at h
  rcases e : runMachineL x st b L with ⟨o, b₁, L₁⟩
  rw [e] at h
  rcases o with ⟨a, st₁⟩ | f | m
  · exact (hx st b a st₁ ⟨L, b₁, L₁, e⟩).trans (hk a st₁ b₁ c st' ⟨L₁, left, log, h⟩)
  · cases h
  · cases h

theorem GrowsM.pure {α : Type} (a : α) : GrowsM (Pure.pure a : M α) := by
  intro st b c st' h
  obtain ⟨L, left, log, h⟩ := h
  simp only [runMachineL_pure, Prod.mk.injEq, Outcome.ok.injEq] at h
  rw [← h.1.2]; exact TablesGrow.refl st

theorem GrowsM.get : GrowsM (MonadState.get : M MState) := by
  intro st b c st' h
  obtain ⟨L, left, log, h⟩ := h
  simp only [runMachineL_get, Prod.mk.injEq, Outcome.ok.injEq] at h
  rw [← h.1.2]; exact TablesGrow.refl st

/-- A write of the state that keeps the tables. -/
theorem GrowsM.modify {g : MState → MState} (hg : ∀ s, TablesGrow s (g s)) : GrowsM (modify g : M Unit) := by
  intro st b c st' h
  obtain ⟨L, left, log, h⟩ := h
  simp only [runMachineL_modify, Prod.mk.injEq, Outcome.ok.injEq] at h
  rw [← h.1.2]; exact hg st

theorem GrowsM.ite {α : Type} {c : Prop} [Decidable c] {x y : M α} (hx : GrowsM x) (hy : GrowsM y) :
    GrowsM (if c then x else y) := by
  split <;> assumption

theorem GrowsM.forIn {α β : Type} (xs : List α) (b : β) {body : α → β → M (ForInStep β)}
    (hb : ∀ a b, GrowsM (body a b)) : GrowsM (forIn xs b body) := by
  induction xs generalizing b with
  | nil => exact GrowsM.pure b
  | cons a as ih =>
    rw [List.forIn_cons]
    exact (hb a b).bind fun r => by cases r with
      | done b' => exact GrowsM.pure b'
      | yield b' => exact ih b'

/-- The tables after a run of `x` only grew. -/
theorem Runs.grows {α : Type} {x : M α} {st st' : MState} {b : Nat} {a : α} (hx : GrowsM x)
    (h : Runs x st b a st') : TablesGrow st st' :=
  hx st b a st' h

theorem GrowsM.err {α : Type} (m : String) : GrowsM (Ochr.err m : M α) := by
  intro st b c st' h
  obtain ⟨L, left, log, h⟩ := h
  simp [runMachineL_err] at h

theorem GrowsM.exhausted {α : Type} (m : String) : GrowsM (Ochr.exhausted m : M α) := by
  intro st b c st' h
  obtain ⟨L, left, log, h⟩ := h
  simp [runMachineL_exhausted] at h

theorem GrowsM.map {α β : Type} (g : α → β) {x : M α} (hx : GrowsM x) : GrowsM (g <$> x) := by
  rw [map_eq_pure_bind]
  exact hx.bind fun a => GrowsM.pure _

theorem GrowsM.discard {α : Type} {x : M α} (hx : GrowsM x) : GrowsM (discard x) := by
  show GrowsM (Functor.mapConst PUnit.unit x)
  rw [LawfulFunctor.map_const]
  exact hx.map _

end Ochr.Meaning.Steps
