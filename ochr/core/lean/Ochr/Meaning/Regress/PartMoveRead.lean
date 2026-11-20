import Ochr.Meaning.Regress.StaticLend
import Ochr.Meaning.Attack.RunEqs
import Ochr.Examples.List

/-!
# The read of `q` while `r`'s content is partly moved (docs/31 D68; kernel-checked)

`let r = &p; let z = (*r).0; let w = q; (*r).0 := z; w` (`ObsReturned.PartMove`, accepted), at
the read of `q`. The checker holds `p ↦ loan_0`, `q ↦ σ1`, `r ↦ borrow_0 (⊥, σ3)`, `z ↦ σ2` (read
at a hole of its real run, `PartMoveAt`). The reference (identity renaming, the checker's sites):
`p` reads `0`'s final content, `q` the meaning of `σ1`, `r` holds `0` with its content partly moved,
`z` the moved-out field; `0`'s record is the content it was made from, `p`'s pair.
- The read of `q` is at the typed future: it gives `0` its record, so it is typed whenever the record
  is a whole member of `r`'s type (`typed_at_read`), and the read is `σ1`'s meaning
  (`read_q`), which is the checker's value's meaning at every future (`checker_q`).
- The closed future, the read's future until D68, gives `0` `r`'s current content, which is partly
  moved, so it is not typed (`closed_not_typed`): the relation at typed futures did not apply to it.
-/

open Ochr.Test

#guard_msgs (drop warning) in
ochr PartMoveReadAt uses Nats, Lists {
  def PartMoveAt (p : Pair(List(Nat), Nat)) (q : Nat) : Nat := (let r = &p; let z = (*r).0; let w : Nat = ?; (*r).0 := z; w)
}

namespace Ochr.Meaning.Regress.PartMoveRead
open Ochr Ochr.Meaning

def atHole (name : String) : List Value :=
  let r := Ochr.Test.runWith (some Prelude) "PartMoveReadAt" PartMoveReadAt (located := true)
  match r.rows.find? (·.name == name) with
  | some row => (row.trace.toList.filterMap fun
      | .note _ _ (.hole _ Ω) => some (Ω.map (·.2.2)) | _ => none).headD []
  | none => []

def vPM : List Value := [.loan 0, .abs 1, .borrow 0 (.ind "Pair" 0 ⟨"Mk"⟩ [.tInd "List" [.tNat], .tNat] [.bot, .abs 3]), .abs 2]
#guard (atHole "PartMoveAt").map Value.pp == vPM.map Value.pp
def stPM : MState := StaticLend.stateAt "PartMoveAt" vPM 1 4

/-- The checker's sites: `0` is lent at `p` (a plain loan of the whole pair). -/
theorem pm_sites : StaticLend.sameSites (Env.sitesOf stPM.env 0) [⟨.bind 1 1, [], false⟩] = true := by
  decide +kernel

/-- The reference's state at the read: frame `1` holds the function, `p`, `q`, `r`, `z`. -/
def SPM (S P Q R Z : SBinding) (vs vq vb vz vp : Sem) (ps : Rec) : SState :=
  { env := [SFrame.mk [] [], SFrame.mk [{ S with val := fun _ => vs }, { P with val := fun ψ => ψ 0 },
      { Q with val := fun _ => vq }, { R with val := fun _ => .dat "Pair" ps 0 [.moved, vb] },
      { Z with val := fun _ => vz }] []],
    shape := fun p => if p = .bind 1 3 then some 0 else none, nextLoan := 1,
    lent := Env.sitesOf stPM.env, heldMem := fun m => if m = 0 then vp else .err }

variable (S P Q R Z : SBinding) (vs vq vb vz vp : Sem) (ps : Rec)

theorem positions_SPM : (SPM S P Q R Z vs vq vb vz vp ps).positions =
    [.bind 1 0, .bind 1 1, .bind 1 2, .bind 1 3, .bind 1 4] := by
  simp [SPM, SState.positions, List.range']

theorem live_SPM (l : Nat) : (SPM S P Q R Z vs vq vb vz vp ps).Live l ↔ l = 0 := by
  rw [SState.live_iff, positions_SPM]
  constructor
  · rintro ⟨p, hp, hs⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl <;> simp [SPM] at hs <;> omega
  · rintro rfl; exact ⟨.bind 1 3, by simp, by simp [SPM]⟩

theorem liveLabels_SPM : (SPM S P Q R Z vs vq vb vz vp ps).liveLabels = [0] := by
  unfold SState.liveLabels; rw [positions_SPM]; simp [SPM]

/-- **The future `q` is read at is typed** when the record, `p`'s pair, is a whole member of `r`'s type. -/
theorem typed_at_read (K : RunCtx) (φ : Future)
    (hvp : vp.whole ∧ vp ∈ₛ[K.dm.read] (R.ty.m)) :
    Steps.TypedLive K (SPM S P Q R Z vs vq vb vz vp ps) ((SPM S P Q R Z vs vq vb vz vp ps).typedFuture φ) := by
  intro l hl
  rw [live_SPM] at hl
  subst hl
  have hh : (SPM S P Q R Z vs vq vb vz vp ps).holderOf 0 = some (.bind 1 3) := by
    unfold SState.holderOf; rw [positions_SPM]; simp [SPM]
  simp only [SState.typedFuture, liveLabels_SPM, List.mem_singleton, if_true, Steps.holderTy, hh]
  simpa [SPM, SState.tyAt] using hvp

/-- **The read of `q`**: its meaning, at the typed future; the state unchanged. -/
theorem read_q (K : RunCtx) (φ : Future) :
    ∃ T, contentOf K φ (.var 2) (SPM S P Q R Z vs vq vb vz vp ps) =
      some ((vq, T, .bind 1 2, []), SPM S P Q R Z vs vq vb vz vp ps) := by
  have hr : resolve (SPM S P Q R Z vs vq vb vz vp ps) (.var 2) = some (.bind 1 2, []) := by
    simp [resolve, SState.varPos, SState.topIdx, Ochr.Place.steps, SPM]
  have ha : ∀ hit, (SPM S P Q R Z vs vq vb vz vp ps).access (.bind 1 2) hit = SPM S P Q R Z vs vq vb vz vp ps := by
    intro hit
    apply SState.access_of_unreached
    intro y hy
    rw [live_SPM] at hy; subst hy
    have hs : ((Env.sitesOf stPM.env 0).any fun x => decide (x.pos = .bind 1 2)) = false := by decide +kernel
    unfold SState.reached
    rw [List.any_eq_false]
    intro x hx hxp
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hxp
    rw [List.any_eq_false] at hs
    exact hs x hx (by simp [hxp.1])
  refine ⟨(SPM S P Q R Z vs vq vb vz vp ps).tyAt (.bind 1 2), ?_⟩
  simp only [contentOf, hr, ha]
  simp [SState.valAt, SPM, Sem.follow]

/-- **The checker's value there means the same at every future**: `q` holds the unknown `σ1`. -/
theorem checker_q (K : RunCtx) (ρ : Assignment) (ψ : Future) (H : TyS) :
    valAt stPM.env (.bind 1 2) = .abs 1 ∧ meanV K ρ ψ H (.abs 1) = ρ 1 :=
  ⟨rfl, rfl⟩

/-- **The closed future is not typed**: it gives `0` `r`'s current content, a pair with its first
field moved out. -/
theorem closed_not_typed (K : RunCtx) (φ : Future) :
    ¬ Steps.TypedLive K (SPM S P Q R Z vs vq vb vz vp ps) ((SPM S P Q R Z vs vq vb vz vp ps).closedFuture φ) := by
  intro h
  have h0 := (h 0 ((live_SPM S P Q R Z vs vq vb vz vp ps 0).mpr rfl)).1
  have hh : (SPM S P Q R Z vs vq vb vz vp ps).holderOf 0 = some (.bind 1 3) := by
    unfold SState.holderOf; rw [positions_SPM]; simp [SPM]
  unfold SState.closedFuture at h0
  rw [liveLabels_SPM] at h0
  simp only [List.length_singleton, List.range_one, List.foldl_cons, List.foldl_nil, hh] at h0
  simp [SState.valAt, SPM, Future.upd, Sem.whole] at h0

end Ochr.Meaning.Regress.PartMoveRead
