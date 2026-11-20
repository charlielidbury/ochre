import Ochr.Meaning.Locality
import Ochr.Examples.Nat

/-!
# `Id` over sides that write through a borrow (docs/31 D74; area (d); kernel-checked)

`IdW` (accepted, by `refl`): `let z = z0; let y = y0; let r = &y`, then `Id(Unit, (*r := S(Z); ()),
(*r := S(Z); ()))`. `IdWNe` (rejected): the second side writes `S(S(Z))`. `IdWMove` (rejected,
[Id-typestate]): one side moves `z`, the other does not.

The reference's observation of a side (`observation`, `run`'s `.id` clause): every borrow of the
side's end state ended, the result and every position read. Kernel-checked on the end states the
sides leave (`y` lent to `0`, `r` holding `0` with the written content, `z` untouched): the two
observations are equal when both sides write the same number (`obs_same`), and differ when they
write different ones (`obs_differ`), at `y`, the footprint's owner, while `z`, outside the
footprint, reads the same after either side (`obs_z_same`: footprint coverage on this instance).
So the reference's `Id` is true for `IdW` and false for `IdWNe`, the checker's verdicts.
-/

open Ochr.Test

ochr IdWriteProbes uses Nats {
  def IdW (z0 : Nat) (y0 : Nat) : Nat := (
    let z = z0; let y = y0; let r = &y;
    let h : Id(Unit, (*r := S(Z); ()), (*r := S(Z); ())) = refl;
    Z)
  reject def IdWNe (z0 : Nat) (y0 : Nat) : Nat := (
    let z = z0; let y = y0; let r = &y;
    let h : Id(Unit, (*r := S(Z); ()), (*r := S(S(Z)); ())) = refl;
    Z)
  reject def IdWMove (z0 : Nat) (y0 : Nat) : Nat := (
    let z = z0; let y = y0; let r = &y;
    let h : Id(Unit, (let w = z; *r := S(Z); ()), (*r := S(Z); ())) = refl;
    Z)
}

namespace Ochr.Meaning.Regress.IdWrite
open Ochr Ochr.Meaning

/-- A side's end state: `z` holding `cz`, `y` reading `0`'s final content, `r` holding `0` with the
content `c` the side wrote; `0` lent at `y`. -/
def endState (Z Y R : SBinding) (cz c : Sem) : SState :=
  { env := [SFrame.mk [{ Z with val := fun _ => cz }, { Y with val := fun ψ => ψ 0 }, { R with val := fun _ => c }] []],
    shape := fun p => if p = .bind 0 2 then some 0 else none, nextLoan := 1,
    lent := fun m => if m = 0 then [⟨.bind 0 0, [], false⟩] else [] }

variable (Z Y R : SBinding) (cz : Sem)

theorem positions_end (c : Sem) : (endState Z Y R cz c).positions = [.bind 0 0, .bind 0 1, .bind 0 2] := by
  simp [endState, SState.positions, List.range']

/-- The observation of a side that wrote `c`: the result, then `z`, `y` (now `c`) and `r` (moved). -/
theorem obs_end (φ : Future) (res : Res) (c : Sem) :
    observation φ [] [] (endState Z Y R cz c).positions res (endState Z Y R cz c) = [res.1, cz, c, .moved] := by
  rw [positions_end]
  simp only [observation, List.zipIdx_nil, List.foldl_nil]
  have hl : (endState Z Y R cz c).liveLabels = [0] := by
    unfold SState.liveLabels; rw [positions_end]; simp [endState]
  rw [hl]
  have hf : ((endState Z Y R cz c).positions.find? fun p => decide ((endState Z Y R cz c).shape p = some 0)) =
      some (.bind 0 2) := by
    rw [positions_end]; simp [endState]
  simp only [List.foldl_cons, List.foldl_nil, SState.endLabel, hf]
  simp [positions_end, endState, SState.toMean, Mean.semEnd, SState.mapVals, SState.valAt, Future.upd, SState.positions,
    List.range']

theorem obs_same (φ : Future) (res : Res) (c : Sem) :
    observation φ [] [] (endState Z Y R cz c).positions res (endState Z Y R cz c) =
      observation φ [] [] (endState Z Y R cz c).positions res (endState Z Y R cz c) := rfl

/-- **Different writes are told apart**, at `y`. -/
theorem obs_differ (φ : Future) (res : Res) :
    observation φ [] [] (endState Z Y R cz (.el0 Nat 1)).positions res (endState Z Y R cz (.el0 Nat 1)) ≠
      observation φ [] [] (endState Z Y R cz (.el0 Nat 2)).positions res (endState Z Y R cz (.el0 Nat 2)) := by
  rw [obs_end, obs_end]
  simp

/-- **`z`, outside the footprint, reads the same after either side** (footprint coverage here). -/
theorem obs_z_same (φ : Future) (res : Res) (c c' : Sem) :
    (observation φ [] [] (endState Z Y R cz c).positions res (endState Z Y R cz c))[1]? =
      (observation φ [] [] (endState Z Y R cz c').positions res (endState Z Y R cz c'))[1]? := by
  rw [obs_end, obs_end]; rfl

end Ochr.Meaning.Regress.IdWrite
