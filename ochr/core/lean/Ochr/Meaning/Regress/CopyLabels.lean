import Ochr.Meaning.Steps.Sim
import Ochr.Meaning.RunPresInd
import Ochr.Machine

/-!
# The relation's label clause was false after a statement that borrows (built)

docs/31 D23 (third lead, 2026-11-19); prerequisite (b) of the migration to the simulation form.

`Rel.fresh` as first stated: every label below the CHECKER's counter is renamed below the
REFERENCE's. The checker runs a statement (a type, a proof, an erased term) on a private copy and
keeps its label counter when the copy is discarded (D37, `restoreKeep`); the reference runs a type
on a copy it discards, counter included, and does not run a proof at all. So after a statement
that borrows, the checker's counter is ahead of the reference's, and from a state whose counter is
`0` no renaming satisfies the clause. Checked on the type `Eq(Nat, (let r = &y; Z), Z)` from the
state where `y = Z` is bound and no label has been issued:

* `checkerCounts`: the checker accepts it (typed), leaves Ω as it was and its counter at `1`
  (a `#guard`: evaluated at build on `Machine.eval`, not kernel-checked);
* `eq_state`: the reference's run of any `Eq` leaves its state, counter included (kernel-checked);
* `old_fresh_false`: so no renaming sends every label below `1` below `0` (kernel-checked).

So `eval_step_stmt` and `evalCore_step_stmt`, which conclude `Rel` of the two states after, were
false on that program. A fault of the statement, not of the checker. The clause now ranges over
the labels that OCCUR in the checker's state (`MState.Occurs`), and a label issued inside a
private copy occurs nowhere after it (`Steps/Sim.private_copy_no_label`; its types and records
hold no loan, (WF11)); `Rel.private_copy` (kernel-checked) is the positive form: the relation
survives a private copy with the reference state untouched and the same renaming, which
`new_fresh_holds` instantiates on this program.
-/

namespace Ochr.Meaning.Regress.CopyLabels
open Ochr Ochr.Meaning Ochr.Meaning.Steps

/-- `Eq(Nat, (let r = &y; Z), Z)`, in a scope where `y` is variable `0`: a type, so a statement. -/
def tEqB : Term := .eq .nat (.letIn ⟨"r"⟩ (.borrow (.var 0)) .zero) .zero

/-- The checker's state with `y : Nat ↦ Z` bound, no temporary, and no label issued. -/
def stY : MState := { env := #[{ binds := #[{ hint := ⟨"y"⟩, ty := some .tNat, val := .zero }] }] }

/-- The checker accepts the type in typed mode, restores Ω (`y` is `Z`, no temporary) and has
issued one label. Evaluated at build (`#guard`), not proved. -/
def checkerCounts : Bool :=
  match (runMachine (Ochr.eval 100 true tEqB none) stY 1000).1 with
  | .ok _ st' => st'.nextLoan == 1 && st'.env.size == 1 && (st'.env[0]!).binds.size == 1 &&
      (st'.env[0]!).temps.size == 0 && (st'.env[0]!).binds[0]!.val == .zero
  | _ => false
#guard stY.nextLoan == 0
#guard checkerCounts

section
variable (K : RunCtx) (ρ : Assignment) (φ : Future)

/-- The reference's run of an `Eq` leaves its state as it was, label counter included. -/
theorem eq_state (hint : TyS) (A a b : Term) (s s' : SState) (r : Res)
    (h : run K ρ φ hint (.eq A a b) s = some (r, s')) : s' = s := by
  rw [run] at h
  exact SM.onCopy_state h

/-- **The clause as first stated has no renaming** once the checker has issued a label and the
reference none. -/
theorem old_fresh_false (st' : MState) (s : SState) (h1 : 0 < st'.nextLoan) (h0 : s.nextLoan = 0) :
    ¬ ∃ π : Nat → Nat, ∀ l, l < st'.nextLoan → π l < s.nextLoan := by
  rintro ⟨π, h⟩
  have := h 0 h1
  rw [h0] at this
  exact Nat.not_lt_zero _ this

/-- No label occurs in `stY`: its one value is `Z`. -/
theorem no_label_stY (l : Nat) : ¬ stY.Occurs l := by
  rintro ⟨v, hv, h⟩
  have hp : allPos stY.env = [.bind 0 0] := by rw [allPos_eq]; rfl
  simp only [Env.values, hp, List.map_cons, List.map_nil, List.mem_singleton] at hv
  subst hv
  have hz : valAt stY.env (.bind 0 0) = .zero := rfl
  rw [hz] at h
  simp [Value.anyAtom, BEq.beq, Value.beq] at h

/-- `stY`'s one value is `Z`, so its reading reads no future. -/
theorem stY_const (p : Pos) (ψ ψ' : Future) : (SM' K ρ stY).valAt p ψ = (SM' K ρ stY).valAt p ψ' := by
  show (MState.sstate K.dm K.M K.Γ ρ stY).valAt p ψ = (MState.sstate K.dm K.M K.Γ ρ stY).valAt p ψ'
  rw [sstate_valAt, sstate_valAt]
  cases p with
  | bind f i =>
    rcases f with _ | f
    · rcases i with _ | i
      · simp [Env.mean, stY, Value.mean]
      · simp [Env.mean, stY]
    · simp [Env.mean, stY]
  | temp f i =>
    rcases f with _ | f
    · simp [Env.mean, stY]
    · simp [Env.mean, stY]

/-- **The clause as it now stands holds after the statement**: any checker state with `stY`'s Ω,
whatever its counter, is simulated by the reference's unchanged state under the identity. -/
theorem new_fresh_holds (st' : MState) (henv : st'.env = stY.env) :
    Rel K ρ φ id st' (SM' K ρ stY) :=
  Rel.private_copy K ρ φ (Rel.start K ρ φ stY) henv
    (fun l h => absurd h (no_label_stY l))

end

end Ochr.Meaning.Regress.CopyLabels
