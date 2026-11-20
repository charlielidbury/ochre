import Ochr.Meaning.Steps.Statements
import Ochr.Meaning.RunLib

/-!
# Facts about the machine alone (the slice, main's decision 2026-11-20; its own lane)

The context's decisions `K.D` are FIXED for a whole run of an item: the checker's own decisions
at the item's final state (`Consistency.const_split` builds the context so, `P.ctx dm D st'`). A
step statement assumes them aligned with the checker's tables at the state AFTER it
(`DecTab K.D st'`) and concludes `CtxOk` there under the same decisions; an assembly obtains that
hypothesis for each part of its run from its own, through (a) and (b) below:
- (a) a successful run of a machine function only extends the tables a decision reads
  (`TablesGrow`): the globals and the declarations are kept, the frozen readings `absDecl` only
  grow (an old entry is never rewritten, main's D96), and the counters are not lowered;
- (b) the decisions aligned at a larger table are aligned at a smaller one (`DecTab.back`).

**Fresh names are never reused within an item.** `freshAbs` pushes, and every exit from a private
computation (`inStatement`'s restore, `exitWorld`, and since main's amendment of the comparison
fix the comparison's exit) keeps `nextAbs`, `nextLoan`, `absDecl` and the new tail of `absTy`,
dropping only the records made inside. So one table answers for every unknown the run creates: the
proof relies on this here, and only here.

Nothing in this file mentions the model: no assignment, no reference state, no meaning.

## Other facts the proof owes that are about the machine alone

To be stated here as they are reached (from the slice's knowledge, 2026-11-20):
- the block's captures after a write: `Decisions.blockCaps` of the checker is static
  (`BlockCaps.staticBlockCaps`), so at every state the static instance at the state's readings and
  entry set is `Machine.blockCaptures`'s answer (D90's obligation 1), and in particular after a
  write of `⊥` changes the entry set (item 4 of the slice's queue measures it first);
- an access loses no unknown the state names, and makes only unknowns nothing names
  (`repackCheck`'s `lentUnknown`, docs/31 D35, D57);
- a decision's run leaves the state as it was (PROVED for the decisions the slice reads,
  `Slice.DecideKeep`), and a successful run at one fuel is a successful run with the same answer
  at every larger fuel (the decisions are asked at any fuel, `DecAligned`);
- a comparison's private copy leaves no record naming an unknown it made (main's comparison fix),
  and `placeType?`'s private copies likewise (to be swept before `placeType?`'s step is stated);
- (WF1)–(WF16) and `ShapeFacts` are kept by every step: about checker states only, but each step's
  proof reads its own; listed here so that whoever proves (a) can collect the ones whose proof
  is a closure induction of the same shape.
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

/-- The tables after a run of `x` only grew. -/
theorem Runs.grows {α : Type} {x : M α} {st st' : MState} {b : Nat} {a : α} (hx : GrowsM x)
    (h : Runs x st b a st') : TablesGrow st st' :=
  hx st b a st' h

/-! ## (b) Alignment at a larger table is alignment at a smaller one -/

/-- **(b) The transfer of alignment from a larger table to a smaller.** A decision whose run succeeds
at `st` reads only the tables' old entries (it names only unknowns `st` has, and their readings are
frozen), so it succeeds at `st'` with the same answer, which the decisions give. The one-way
simulation of `Decide.lean` (`DecideScope.decideSim`) for tables whose old entries agree, the
converse direction of `DecExtend.decAligned_grow` and the same lemma underneath. Open (the machine
lane). -/
theorem DecTab.back {D : Decisions} {st st' : MState} (hd : DecTab D st') (hg : TablesGrow st st') :
    DecTab D st := by
  sorry

/-- An assembly's tool: the decisions after the whole run are aligned after a part of it, where
the rest of the run only extends the tables. -/
theorem DecTab.of_rest {α : Type} {D : Decisions} {st₁ st' : MState} {rest : M α} {b : Nat} {a : α}
    (hd : DecTab D st') (hrest : GrowsM rest) (h : Runs rest st₁ b a st') : DecTab D st₁ :=
  hd.back (h.grows hrest)

/-! ## (a) Every machine function's successful run only extends the tables

One field per machine function a step statement or an assembly runs, at every fuel. The proof is a
closure induction over the machine's mutual block (`Slice.DecideKeep`'s technique, with
`TablesGrow` in place of equality): every write of the state either keeps the tables (`modify` of
the frames, the flags, the log, the records), or pushes an unknown (`freshAbs`), or is a private
computation's exit, which keeps the names (see the module docstring). Open (the machine lane). -/
structure MachineGrows (fuel : Nat) : Prop where
  -- filled as the change of form reaches each assembly
  dummy : True

theorem machineGrows : ∀ fuel, MachineGrows fuel := by
  sorry

end Ochr.Meaning.Steps
