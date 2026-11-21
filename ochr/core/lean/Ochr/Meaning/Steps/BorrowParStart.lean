import Ochr.Meaning.Steps.BorrowPar
import Ochr.Meaning.Steps.Sim

/-!
# `W`'s and `K`'s body start: the model's state is not related to the checker's (lead18, 2026-11-21; docs/31 D138)

The reference runs a closure's body from `fixBodyAt`'s state (docs/31 D126, stage 2): frame 0 the parameter's CELL
`r° ↦ ψ l` at the content type, the top frame `self` then the parameter holding the argument, shaped with the fresh
label `l`, whose record (`heldMem`) is the argument and held type (`heldTy`) the content type. It does NOT record the
cell as `l`'s loan site: `lent l` stays empty (`fixStep` writes `env`, `shape`, `nextLoan`, `heldMem`, `heldTy` only).

The checker's start state (`stW`, `stK`, pinned) holds the cell `r° ↦ loan₀`, which IS a site of label `0`
(`Env.sitesOf`: a `loan` is the borrow's one loan site). `Rel.sites` asks the two sides' sites of every live label to be
the same, so no reference state built by `fixBodyAt` for a borrow parameter is related to the checker's start state
(`rel_start_false`): the step for `W`'s or `K`'s body cannot start.
-/

namespace Ochr.Meaning.Steps.Form.ColumnW

open Ochr Ochr.Meaning Ochr.Meaning.Steps Ochr.Meaning.Steps.Form

/-- `&Nat`'s domain, as the `.fix` clause reads it. -/
def psW : List PiDom := [⟨true, fun _ => TyM.nat⟩]

/-- **The reference's body state for a function with one borrow parameter** at argument `a` (`fixBodyAt`'s, given the
binding of itself `sb`, the binders `fb` the `.fix` clause read, and the parameter's domain `d`, a borrow). -/
noncomputable def startS (fb : List PBind × PBind) (sb : SBinding) (d : PiDom) (a : Sem) : SState :=
  (([a].zip [d]).foldl (fixStep fb) ((emptyState 0).under.pushBind sb, [], [])).1

theorem takeLabel_lent (s : SState) (l : Nat) : (s.takeLabel l).lent = s.lent := by
  unfold SState.takeLabel; split
  · rename_i r _; cases r <;> rfl
  · rfl

theorem pushBindShaped_lent (s : SState) (b : SBinding) : (pushBindShaped s b).lent = s.lent := by
  unfold pushBindShaped; split
  · dsimp only; split
    · show ((s.takeLabel _).pushBind b).lent = s.lent
      rw [show ((s.takeLabel _).pushBind b).lent = (s.takeLabel _).lent from rfl, takeLabel_lent]
    · show ((s.takeLabel _).pushBind b).lent = s.lent
      rw [show ((s.takeLabel _).pushBind b).lent = (s.takeLabel _).lent from rfl, takeLabel_lent]
  · rfl

/-- It records no loan site for the parameter's label: the cell is not `l`'s site. -/
theorem startS_lent (fb : List PBind × PBind) (sb : SBinding) {d : PiDom} (hd : d.isRef = true) (a : Sem) (l : Nat) :
    (startS fb sb d a).lent l = [] := by
  simp only [startS, List.zip_cons_cons, List.zip_nil_right, List.foldl_cons, List.foldl_nil, fixStep, hd, if_true]
  rw [pushBindShaped_lent]
  simp [SState.freshLoan, SState.pushCell, SState.pushBind, SState.under, emptyState]

/-- The checker's cell `r° ↦ loan₀` is label `0`'s one site, and label `0` is live (held by `r`). -/
theorem allPos_stW : allPos stW.env = [.bind 0 0, .bind 1 0, .bind 1 1] := by
  rw [allPos_eq]; simp [stW, frameAllPos, List.range_succ]
theorem allPos_stK : allPos stK.env = [.bind 0 0, .bind 1 0, .bind 1 1] := by
  rw [allPos_eq]; simp [stK, frameAllPos, List.range_succ]

theorem sitesOf_stW : Env.sitesOf stW.env 0 = [⟨.bind 0 0, [], false⟩] := by
  unfold Env.sitesOf; rw [allPos_stW]; rfl
theorem sitesOf_stK : Env.sitesOf stK.env 0 = [⟨.bind 0 0, [], false⟩] := by
  unfold Env.sitesOf; rw [allPos_stK]; rfl
theorem live_stW : liveLoan stW.env 0 = true := by rw [liveLoan, findBorrow, allPos_stW]; rfl
theorem live_stK : liveLoan stK.env 0 = true := by rw [liveLoan, findBorrow, allPos_stK]; rfl

/-- **No reference body state `fixBodyAt` builds is related to `W`'s start state** (nor to `K`'s), whatever the
context, assignment, future and renaming: `Rel.sites` asks the cell to be label `0`'s site on the reference's side. -/
theorem rel_start_false (K : RunCtx) (ρ : Assignment) (φ : Future) (π : Nat → Nat) (fb : List PBind × PBind)
    (sb : SBinding) {d : PiDom} (hd : d.isRef = true) (a : Sem) :
    ¬ Rel K ρ φ π stW (startS fb sb d a) ∧ ¬ Rel K ρ φ π stK (startS fb sb d a) := by
  refine ⟨fun hr => ?_, fun hr => ?_⟩
  · have h := (hr.sites 0 live_stW ⟨.bind 0 0, [], false⟩).mpr (by rw [sitesOf_stW]; simp)
    rw [startS_lent _ _ hd] at h; cases h
  · have h := (hr.sites 0 live_stK ⟨.bind 0 0, [], false⟩).mpr (by rw [sitesOf_stK]; simp)
    rw [startS_lent _ _ hd] at h; cases h

end Ochr.Meaning.Steps.Form.ColumnW
