import Ochr.Meaning.Strict.Ops
import Ochr.Meaning.RunPresInd
import Ochr.Meaning.RunEnv

/-!
# The invariant's structural part, and the strict test that completes it

An assignment or a borrow at a FIELD path leaves a state that need not be good until D112's
invalidation has run (a later dependent field of the written value); the run then tests `StateOk`
(`Run.lentOk`), the value clauses of `SGood` at every typed future. The middle predicate is
`SStruct`: `SGood`'s clauses that speak of records, shapes and label order, not of values
(`held`, `holderTy`, `acyc`, `fresh`). It holds after the write or the borrow, every step of the
invalidation keeps it ([Access]'s ends, the `⊥` writes), and with `StateOk` it is `SGood`
(`sgood_of_stateOk`).
-/

namespace Ochr.Meaning.Strict
open Ochr.Meaning

/-- `SGood`'s clauses that do not read values: records, shapes, label order. -/
structure SStruct (dm : DataModel) (s : SState) : Prop where
  held : ∀ l ∈ s.liveLabels, s.heldMem l ∈ₛ[dm.read] s.heldTy l
  holderTy : ∀ f i l, s.shape (.bind f i) = some l → (s.tyAt (.bind f i)).m = s.heldTy l
  acyc : SState.RInv (fun _ => True) s
  fresh : s.ReadsBelow

section
variable {dm : DataModel} {Γ : List IndDecl} {φ : Future}

theorem SGood.struct {s : SState} (hs : SGood dm Γ φ s) : SStruct dm s :=
  ⟨hs.held, hs.holderTy, hs.acyc, hs.fresh⟩

/-- An end keeps the structural part (`endAt_sgood`'s last four clauses). -/
theorem SStruct.endAt {s : SState} {l : Nat} {r : Pos} (hs : SStruct dm s) (hh : s.holderOf l = some r) :
    SStruct dm (s.endAt l r) := by
  have hTy : ∀ q, (s.endAt l r).tyAt q = s.tyAt q := fun q => by unfold SState.endAt; rw [tyAt_mapVals]; rfl
  have hHT : (s.endAt l r).heldTy = s.heldTy := rfl
  have hHM : (s.endAt l r).heldMem = s.heldMem := rfl
  refine ⟨fun l' hl' => ?_, fun f i l' hl' => ?_, ?_, ?_⟩
  · rw [hHT, hHM]; exact hs.held l' (SState.endAt_live hl')
  · rw [SState.endAt_shape] at hl'
    simp only at hl'
    split at hl'
    · cases hl'
    · rw [hTy, hHT]; exact hs.holderTy f i l' hl'
  · have := SState.endLabel_rinv hs.acyc l
    rwa [SState.endLabel_eq hh] at this
  · have := SState.readsBelow_endLabel hs.fresh l
    rwa [SState.endLabel_eq hh] at this

theorem SStruct.endLabel {s : SState} (hs : SStruct dm s) (l : Nat) : SStruct dm (s.endLabel l) := by
  cases h : s.holderOf l with
  | none => rw [SState.endLabel_of_none h]; exact hs
  | some r => rw [SState.endLabel_eq h]; exact hs.endAt h

theorem SStruct.foldl_endLabel : ∀ (ls : List Nat) {s : SState}, SStruct dm s → SStruct dm (ls.foldl SState.endLabel s)
  | [], _, h => h
  | l :: ls, _, h => SStruct.foldl_endLabel ls (h.endLabel l)

/-- [Access] keeps the structural part. -/
theorem SStruct.access {s : SState} (hs : SStruct dm s) (p : Pos) (hit : List Step → Bool) :
    SStruct dm (s.access p hit) := by
  rw [SState.access_eq, SState.foldl_range_iterR]
  generalize s.liveLabels.length = k
  induction k with
  | zero => exact hs
  | succ k ih => exact SStruct.foldl_endLabel _ ih

/-- **With the strict test, the structural part is the invariant**: `StateOk` is `SGood`'s value
clauses at every typed future. -/
theorem sgood_of_stateOk {K : RunCtx} {s : SState} (hS : SStruct K.dm s) (hok : StateOk K φ s) :
    SGood K.dm K.Γ φ s :=
  ⟨fun ψ hψ f i hp => (hok ψ hψ).1 f i hp, fun ψ hψ q l hl => (hok ψ hψ).2 q l hl,
    hS.held, hS.holderTy, hS.acyc, hS.fresh⟩

end

section
variable {K : RunCtx} {φ : Future}

/-- A write at a path keeps the structural part (it changes one position's value only). -/
theorem SStruct.setContent {s s' : SState} {pos : Pos} {steps : List Step} {v : Sem} (hs : SStruct K.dm s)
    (h : setContent K φ pos steps v s = some (⟨⟩, s')) : SStruct K.dm s' := by
  have hacyc := (setContent_rinv K φ (fun _ => True) h hs.acyc).1
  rw [setContent_eq K φ h] at hacyc ⊢
  refine ⟨?_, fun f i l hl => ?_, hacyc, ?_⟩
  · rw [liveLabels_setAt, heldTy_setAt, heldMem_setAt]; exact hs.held
  · rw [SState.shape_setAt] at hl; rw [tyAt_setAt, heldTy_setAt]; exact hs.holderTy f i l hl
  · exact SState.readsBelow_setAt hs.fresh _ _ (fun l h => hs.fresh pos l
      (SVal.dependsOn_comp (v := s.valAt pos) (G := fun x => (Sem.updAt K.dm K.Γ (s.tyAt pos) (fun _ => v) steps x).getD .err) h))

/-- D112's invalidation of one place keeps the structural part: [Access], then `⊥` where defined. -/
theorem SStruct.invalidateOne {s : SState} (hs : SStruct K.dm s) (q : Place) :
    SStruct K.dm (invalidateOne K φ s q) := by
  unfold Ochr.Meaning.invalidateOne
  split
  · rename_i pos steps _
    dsimp only
    have hs₁ := hs.access pos (dataHit steps)
    split
    · rename_i u s'' hsc
      obtain ⟨⟨⟩, _⟩ := u
      exact hs₁.setContent hsc
    · exact hs₁
  · exact hs

theorem SStruct.invalidate {s : SState} (hs : SStruct K.dm s) (p : Place) :
    SStruct K.dm (invalidate K φ p s) := by
  unfold Ochr.Meaning.invalidate
  generalize K.D.invalidated (scopeOf s) p = qs
  induction qs generalizing s with
  | nil => exact hs
  | cons q qs ih => simp only [List.foldl_cons]; exact ih (hs.invalidateOne q)

end

/-- A place resolves the same across steps that keep the frames' bindings (`EnvLe`). -/
theorem varPos_envLe {s s' : SState} (h : EnvLe s s') (i : Nat) : s'.varPos i = s.varPos i := by
  unfold SState.varPos SState.topIdx
  rw [List.getLast?_eq_getElem?, List.getLast?_eq_getElem?, h.1]
  cases e : s.env[s.env.length - 1]? with
  | none =>
    have : s.env.length - 1 ≥ s.env.length := List.getElem?_eq_none_iff.mp e
    have e' : s'.env[s.env.length - 1]? = none := List.getElem?_eq_none_iff.mpr (by rw [h.1]; exact this)
    rw [e']
  | some fr =>
    obtain ⟨fr', e', hb, -⟩ := h.2 _ fr e
    rw [e']; simp only [hb]

theorem resolve_envLe {s s' : SState} (h : EnvLe s s') (p : Place) : resolve s' p = resolve s p := by
  unfold resolve; simp only [varPos_envLe h]

end Ochr.Meaning.Strict
