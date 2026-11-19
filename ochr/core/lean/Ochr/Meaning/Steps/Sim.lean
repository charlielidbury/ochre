import Ochr.Meaning.Steps.Statements
import Ochr.Meaning.PosLib

/-!
# The relation that lets steps compose (docs/31, D20 item 1; second lead, 2026-11-13)

Every step statement of `Statements.lean` runs the reference from `SM' K ρ st`, the checker's own
state read as a reference state, and concludes `Below (MState.mean … st') s'.toMean`. Two faults,
both of the statements:

1. **It does not compose.** After a first step the reference is in its own state `s'`, not in
   `SM' st'`, and the second step's statement says nothing about a run from `s'`.
2. **It is false wherever a borrow was held** (`Regress/StaleTemp.lean`, kernel-checked on the
   reference's side, the checker's by `#guard`): `Below` reads every position, the reference
   parks borrows in temporaries the checker does not have, and `err ⊑ ⊥` is false.

The repair chosen is the **simulation form**: a step is stated from ANY reference state `s`
related to the checker's state (`Rel`), and concludes `Rel` of the two states after. Then
sequencing is by construction (`sim_seq`), and no lemma "the run is monotone in the state" is
needed. That lemma was the alternative; it is false for the relation `Below` (two states can be
`Below`-related with a witness future that is not the one an [End] would fix: the lower reads
`5` where the upper's holder holds `7`, and a read gives `5` against `7`), and for an
ends-generated relation it needs the run to fail on a forgotten holder, which a write through
`*r` does not (`Sem.updAt` at a `deref` of `⊥`). In the simulation form the checker's own run is
a hypothesis, and the checker never uses a holder it has ended.

`Rel` has three parts, each forced by a counterexample (docs/31, D20 item 1):

* `skel`: the same frames and, in each, the same bindings with the same types (meaning, Π-shape,
  data) and readings. `Below` relates meanings only; two states with the same meanings and
  different binding counts resolve `var 0` to different positions, and one whose bindings have
  lost their Π-shapes fails every call through a variable (docs/31 D22: the shape was first left
  out).
* `fresh`, with the renaming `π` of the checker's labels to the reference's: the two runs do
  NOT issue the same labels, and cannot be made to. The checker runs an erased term on a private
  copy and keeps the label counter (D37), so a proof that borrows consumes labels; the reference
  does not run a proof at all (the audit's A3), and its run could fail if it did. So shapes and
  futures are compared through `π`, and a step extends `π` at the labels it issues. The clause
  ranges over the labels that OCCUR in the checker's state: over every label below its counter
  it had no renaming after a statement that borrows (docs/31 D23, `Regress/CopyLabels.lean`).
  (The audit's A15, the counter after a private copy, is absorbed: `Rel.private_copy`.)
* `early`: the checker's state is the reference's after some of its borrows ended early (`E`),
  compared at the SAME future (`SimEq`), with bindings position by position and a borrow in
  flight by its label, the meanings EQUAL (with `⊑` the relation admitted a reference state with
  a value where the checker's has `⊥` inside a tuple, from which a match's join and `Id` differ:
  docs/31 D24). The futures range over those that agree with the run's off the labels
  live after the ends, which is D20 item 2's repair (a binding of an inert loan is the constant
  `φ ℓ` in the reference and `φ' ℓ` in the checker's state).

**Status.** The relation (`SimEq`, `Sim`, `Rel`) is defined in `Statements.lean`, where the
three statements refuted by `Regress/StaleTemp.lean` (`eval_step_stmt`, `evalCore_step_stmt`,
`letIn_step_stmt`) are now in the simulation form. Proved here: `Rel.start` (the relation holds
at the start) and `sim_seq` (steps in this form compose); in `Statements.lean`: `Sim.of_below`,
`Sim.of_simEq_below` (nothing true under the old order is lost); and `Rel.private_copy` (the
relation survives a private copy of the checker's, reference state and renaming unchanged). NOT done: the other statements
of `Statements.lean` that run the reference from `SM' K ρ st` still have the `Below` form;
migrating them is the next batch (each `Below (MState.mean … st') s'.toMean` conjunct becomes
`Rel`, each `SM' K ρ st` a universally quantified `s` with `Rel`, the returned value read at the
future pulled back along the renaming).
-/

namespace Ochr.Meaning.Steps
open Ochr Ochr.Meaning

section
variable (K : RunCtx) (ρ : Assignment) (φ : Future)

/-- **The relation holds at the start**: the checker's state read as a reference state simulates
it, with no renaming and no early end. (If this failed the relation would be unusable: every
top-level statement starts here.) -/
theorem Rel.start (st : MState) : Rel K ρ φ id st (SM' K ρ st) where
  skel := rfl
  fresh := fun _ h _ => h
  early := ⟨[], fun ψ _ p _ => by
      show _ = (MState.sstate K.dm K.M K.Γ ρ st).valAt p ψ
      rw [sstate_valAt]; rfl,
    fun _ _ _ h => h,
    fun f i l h => ⟨i, h, fun ψ _ => by
      show _ = (MState.sstate K.dm K.M K.Γ ρ st).valAt (.temp f i) ψ
      rw [sstate_valAt]; rfl⟩⟩

/-! ### A private copy (docs/31 D23; prerequisite (b) of the migration)

The checker runs a statement (a type, a proof, an erased term) on a private copy of its state and
then restores the snapshot (`restoreKeep`), keeping the name counters, the records and the types
of the unknowns created inside. The reference does not run a proof at all and runs a type on a
copy it discards, counter included. So after a statement the checker has issued labels the
reference has not, and the relation must survive with the reference state UNTOUCHED and the SAME
renaming. It does, because a label issued inside a copy occurs nowhere after it: Ω is the
snapshot's, and the records and types that survive hold no loan at all ((WF11)). -/

/-- What `restoreKeep` leaves: the snapshot's Ω and goal, the copy's counters and records. -/
theorem restoreKeep_spec (saved cur st' : MState) (fuel : Nat) (h : Runs (restoreKeep saved) cur fuel () st') :
    st'.env = saved.env ∧ st'.goal = saved.goal ∧ st'.inds = saved.inds ∧
    st'.nextLoan = cur.nextLoan ∧ st'.neutrals = cur.neutrals ∧ st'.etaRefs = cur.etaRefs := by
  unfold restoreKeep at h
  obtain ⟨-, rfl⟩ := Runs.unique h (runs_modify _ cur fuel)
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- A label occurs in a state through its Ω alone. -/
theorem occurs_of_env {st st' : MState} (h : st'.env = st.env) (l : Nat) : st'.Occurs l ↔ st.Occurs l := by
  unfold MState.Occurs; rw [h]

/-- **No label issued inside a private copy occurs after it**: with the labels of the snapshot's
Ω below its counter ((WF6), in the form `Occurs`), no label at or above that counter occurs in the
restored state. (Its types and records hold no loan at all: (WF11), a clause of `Good`.) -/
theorem private_copy_no_label (saved cur st' : MState) (fuel : Nat) (h : Runs (restoreKeep saved) cur fuel () st')
    (h6 : ∀ l, saved.Occurs l → l < saved.nextLoan) (l : Nat) (hl : saved.nextLoan ≤ l) : ¬ st'.Occurs l :=
  fun ho => absurd (h6 l ((occurs_of_env (restoreKeep_spec saved cur st' fuel h).1 l).mp ho)) (Nat.not_lt.mpr hl)

/-- **The relation survives a private copy**, with the reference state untouched and the same
renaming: whatever the copy did to the checker's counters and records, if Ω is the snapshot's
(and so are the declarations) the restored state is simulated as the snapshot was. This is the
step of an erased term on the checker's side; with `fresh` as first stated (every label below the
checker's counter) it was false (`Regress/CopyLabels.lean`). -/
theorem Rel.private_copy {π : Nat → Nat} {saved st' : MState} {s : SState} (hr : Rel K ρ φ π saved s)
    (henv : st'.env = saved.env) (h6 : ∀ l, saved.Occurs l → l < saved.nextLoan) : Rel K ρ φ π st' s where
  skel := by
    have e : (SM' K ρ st').env = (SM' K ρ saved).env := by
      simp only [SM', MState.sstate, henv]
    rw [e]; exact hr.skel
  fresh := fun l _ ho => hr.fresh l (h6 l ((occurs_of_env henv l).mp ho)) ((occurs_of_env henv l).mp ho)
  early := by
    have e : MState.mean K.dm K.M K.Γ ρ st' = MState.mean K.dm K.M K.Γ ρ saved := by
      simp only [MState.mean, henv]
    rw [e]; exact hr.early

/-- Steps stated in the simulation form compose: if the first runs from any reference state
related to `st` into one related to `st₁`, and the second from any related to `st₁` into one
related to `st₂`, their sequence runs from any related to `st` into one related to `st₂` (each
under the renaming the step before it hands on). With the `Below` form the second premise is
available only at `SM' st₁`, and this fails. -/
theorem sim_seq {α β : Type 3} (x₁ : SM α) (x₂ : α → SM β) (st st₁ st₂ : MState)
    (h₁ : ∀ s π, Rel K ρ φ π st s → ∃ a s₁ π₁, x₁ s = some (a, s₁) ∧ Rel K ρ φ π₁ st₁ s₁)
    (h₂ : ∀ a s₁ π₁, Rel K ρ φ π₁ st₁ s₁ → ∃ b s₂ π₂, x₂ a s₁ = some (b, s₂) ∧ Rel K ρ φ π₂ st₂ s₂) :
    ∀ s π, Rel K ρ φ π st s → ∃ b s₂ π₂, (x₁ >>= x₂) s = some (b, s₂) ∧ Rel K ρ φ π₂ st₂ s₂ := by
  intro s π hs
  obtain ⟨a, s₁, π₁, e₁, r₁⟩ := h₁ s π hs
  obtain ⟨b, s₂, π₂, e₂, r₂⟩ := h₂ a s₁ π₁ r₁
  refine ⟨b, s₂, π₂, ?_, r₂⟩
  simp only [Bind.bind]
  rw [e₁]
  exact e₂

end

end Ochr.Meaning.Steps
