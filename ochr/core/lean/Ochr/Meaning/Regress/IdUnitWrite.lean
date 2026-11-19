import Ochr.Meaning.Locality
import Ochr.Examples.Nat
import Ochr.Examples.List
import Ochr.Examples.Box

/-!
# `Id` read the value written through a re-pointed borrow at every meaning, not at its type (built)

docs/31 D26 (third lead, 2026-11-19). [Obs-ref] (D84): where both sides of an `Id` re-point a
borrow binding `y`, the checker writes one fresh unknown `σ` of the BORROWED TYPE through `y`
after each side, ends every borrow and compares the owners, so that where `y` points is observed.
The reference's `Id` asked the two observations to be equal for EVERY written value `w : Sem`,
typed or not.

The two differ at a type with one element. `IdUnit` (accepted, by `refl`): `y : &Unit`, one side
re-points it at `a`, the other at `b`. For the checker the value written is a `Unit`, which is
`()`, and `a`, `b` are `()` after either side. For the reference `w` may be anything, and writing
`⊥` through `y` leaves it in `a` after one side and in `b` after the other: its `Id` was false.
`IdNat`, the same at `Nat`, is REJECTED: there the two do agree that the sides differ.

Kernel-checked here, on the two end states of `IdUnit`'s sides (`a`, `b`, and `y` holding the
borrow of label `0`; `a` lent after the first side, `b` after the second): the observations are
equal when the written value is `()` (`obs_unit`) and differ when it is `⊥` (`obs_moved`). So
the reference's proposition, a `∀` over every written value, was false, and it is true once the
written values range over the borrowed type.

Fixed: `run`'s `.id` clause quantifies over the values of each re-pointed binding's content type.
-/

open Ochr.Test

ochr IdUnitProbes uses Nats, Lists, Boxes {
  -- both sides re-point a borrow of a `Unit` at different places: `Id` holds, a `Unit` is `()`
  def IdUnit (a0 : Unit) (b0 : Unit) (c0 : Unit) : Nat := (
    let a = a0; let b = b0; let c = c0;
    let y = &c;
    let h : Id(Unit, (y := &a; ()), (y := &b; ())) = refl;
    Z)
  -- control: at `Nat` the two sides are told apart
  reject def IdNat (a0 : Nat) (b0 : Nat) (c0 : Nat) : Nat := (
    let a = a0; let b = b0; let c = c0;
    let y = &c;
    let h : Id(Unit, (y := &a; ()), (y := &b; ())) = refl;
    Z)
}

namespace Ochr.Meaning.Regress.IdUnitWrite
open Ochr Ochr.Meaning

/-- `()`. -/
def u : Sem := .el0 Unit ()

/-- The end state of a side: `a`, `b`, `y` in one frame, `y` holding the borrow of label `0`
(content `()`), and the lent one of `a`, `b` reading the label's final content. -/
def endState (lentA : Bool) : SState :=
  { env := [{ binds := [
      { ty := .plain (.ty0 Unit), val := if lentA then (fun ψ => ψ 0) else fun _ => u },
      { ty := .plain (.ty0 Unit), val := if lentA then (fun _ => u) else fun ψ => ψ 0 },
      { ty := .plain (.ty0 Unit), val := fun _ => u }] }],
    shape := fun p => if p = .bind 0 2 then some 0 else none,
    nextLoan := 1 }

/-- What [Obs-ref] and the end of every borrow leave at `a` and `b`, for the value `w` written
through `y`: `w` where `y` points, `()` at the other. -/
noncomputable def obsAB (lentA : Bool) (w : Sem) (φ : Future) : Sem × Sem :=
  let s := ((endState lentA).setAt (.bind 0 2) fun _ => w).endAt 0 (.bind 0 2)
  (s.valAt (.bind 0 0) φ, s.valAt (.bind 0 1) φ)

theorem positions_set (lentA : Bool) (w : Sem) :
    ((endState lentA).setAt (.bind 0 2) fun _ => w).positions = [.bind 0 0, .bind 0 1, .bind 0 2] := by
  rw [SState.positions_setAt, SState.positions_eq]
  cases lentA <;> rfl

theorem obsAB_eq (lentA : Bool) (w : Sem) (φ : Future) :
    obsAB lentA w φ = if lentA then (w, u) else (u, w) := by
  unfold obsAB
  simp only
  rw [SState.endAt_valAt _ _ _ _ (by rw [positions_set]; simp),
    SState.endAt_valAt _ _ _ _ (by rw [positions_set]; simp)]
  cases lentA <;> simp [endState, SState.setAt, SState.valAt, Future.upd]

/-- With `()` written, the two sides leave `a` and `b` alike. -/
theorem obs_unit (φ : Future) : obsAB true u φ = obsAB false u φ := by
  rw [obsAB_eq, obsAB_eq]; rfl

/-- With `⊥` written, they do not: it is in `a` after one side and in `b` after the other. -/
theorem obs_moved (φ : Future) : obsAB true .moved φ ≠ obsAB false .moved φ := by
  rw [obsAB_eq, obsAB_eq]
  simp [u]

/-- `obsAB` is what the run's `observation` reads at `a` and `b`: with `y` the one re-pointed
binding (variable `0`), it writes `w` at `y`'s position, ends the one live label, and reads. -/
theorem observation_eq (lentA : Bool) (w : Sem) (φ : Future) (r : Res) :
    observation φ [.var 0] [w] [.bind 0 0, .bind 0 1] r (endState lentA)
      = [r.1, (obsAB lentA w φ).1, (obsAB lentA w φ).2] := by
  have hres : resolve (endState lentA) (.var 0) = some (.bind 0 2, []) := by
    cases lentA <;> simp [resolve, SState.varPos, SState.topIdx, Ochr.Place.steps, endState]
  have hlive : ((endState lentA).setAt (.bind 0 2) fun _ => w).liveLabels = [0] := by
    unfold SState.liveLabels
    rw [positions_set]
    simp [SState.setAt, endState]
  have hhold : ((endState lentA).setAt (.bind 0 2) fun _ => w).holderOf 0 = some (.bind 0 2) := by
    unfold SState.holderOf
    rw [positions_set]
    simp [SState.setAt, endState]
  unfold observation
  simp only [List.zipIdx_cons, List.zipIdx_nil, List.foldl_cons, List.foldl_nil, hres, Nat.zero_add,
    List.getElem?_cons_zero, hlive, SState.endLabel_eq hhold, List.map_cons, List.map_nil]
  rfl

/-- **So the reference's `Id`, a `∀` over every written value, was false of the two sides**, and
it holds of them at the one value of the borrowed type. -/
theorem id_all_false (φ : Future) (r : Res) :
    ¬ ∀ ws : List Sem, observation φ [.var 0] ws [.bind 0 0, .bind 0 1] r (endState true)
      = observation φ [.var 0] ws [.bind 0 0, .bind 0 1] r (endState false) := by
  intro h
  have := h [.moved]
  rw [observation_eq, observation_eq] at this
  simp only [List.cons.injEq, true_and, and_true] at this
  exact obs_moved φ (Prod.ext this.1 this.2)

theorem id_unit_true (φ : Future) (r : Res) :
    observation φ [.var 0] [u] [.bind 0 0, .bind 0 1] r (endState true)
      = observation φ [.var 0] [u] [.bind 0 0, .bind 0 1] r (endState false) := by
  rw [observation_eq, observation_eq, obs_unit]

/-! ## The statements of `Id` and `Eq` said nothing

`idType_step_stmt` and `eq_step_stmt` ended `∃ r s', run … = some (r, s') ∧ ⟦P⟧ true ↔ ⟦r⟧ true`.
`∧` binds tighter than `↔`, so this is `∃ r s', (run … = some (r, s') ∧ ⟦P⟧ true) ↔ ⟦r⟧ true`,
which holds of any `r` that means no true proposition and is not the run's result. -/

/-- The conjunct as it parsed is true whatever the run returns and whatever `A` says. -/
theorem old_stmt_vacuous (x : Option (Res × SState)) (A : Prop) :
    ∃ (r : Res) (s' : SState), (x = some (r, s') ∧ A) ↔ (r.1.asTy).true := by
  refine ⟨(.err, .plain .err), ?_⟩
  have hf : ¬ (Sem.err.asTy).true := id
  cases x with
  | none => exact ⟨⟨[], fun _ => none, 0⟩, ⟨fun h => (nomatch h.1), fun h => absurd h hf⟩⟩
  | some rs =>
    refine ⟨{ rs.2 with nextLoan := rs.2.nextLoan + 1 }, ⟨fun h => ?_, fun h => absurd h hf⟩⟩
    have e := congrArg (fun o => (o.map (·.2.nextLoan))) h.1
    simp only [Option.map_some, Option.some.injEq] at e
    omega

end Ochr.Meaning.Regress.IdUnitWrite
