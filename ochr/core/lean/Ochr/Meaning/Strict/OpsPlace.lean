import Ochr.Meaning.Strict.Ops
import Ochr.Meaning.RunCongr
import Ochr.Meaning.MonoHolders

/-!
# The place operations keep the invariant: holder transfers, a `let`'s binding and drop, reads,
borrows, assignments

Each at a ROOT path or through a borrow (`[*]`) proved; at a FIELD path, a write (a move out of a
field, a borrow's lender, an assignment to a field) changes a part of a constructor value, which
later dependent fields' types read: that is the dependent-values area, isolated as named guesses
(`*_field_*`), each with what it would need.
-/

namespace Ochr.Meaning.Strict
open Ochr.Meaning

variable {K : RunCtx} {φ : Future}

/-! ## Helpers: pushing a temporary, typed futures across states with the same live labels -/

theorem env_ne_of_mem {s : SState} {p : Pos} (h : p ∈ s.positions) : s.env ≠ [] := by
  intro he
  rw [SState.mem_positions] at h
  cases p <;> simp [SState.lookup, he] at h

theorem lookup_pushTemp_bind (s : SState) (v : SVal) (f i : Nat) :
    (s.pushTemp v).lookup (.bind f i) = s.lookup (.bind f i) := by
  simp only [SState.lookup, SState.pushTemp, List.getElem?_modify]
  by_cases hf : s.topIdx = f <;> cases s.env[f]? <;> simp [hf]

theorem tyAt_pushTemp (s : SState) (v : SVal) (q : Pos) : (s.pushTemp v).tyAt q = s.tyAt q := by
  cases q with
  | temp => rfl
  | bind f i =>
    simp only [SState.tyAt, SState.pushTemp, List.getElem?_modify]
    by_cases hf : s.topIdx = f <;> cases s.env[f]? <;> simp [hf]

theorem bind_mem_pushTemp (s : SState) (v : SVal) (f i : Nat) :
    Pos.bind f i ∈ (s.pushTemp v).positions ↔ Pos.bind f i ∈ s.positions := by
  rw [SState.mem_positions, SState.mem_positions, lookup_pushTemp_bind]

theorem valAt_pushTemp_bind (s : SState) (v : SVal) (f i : Nat) :
    (s.pushTemp v).valAt (.bind f i) = s.valAt (.bind f i) := by
  rw [SState.valAt_eq, SState.valAt_eq, lookup_pushTemp_bind]

theorem tyAt_pushTempShaped (s : SState) (v : SVal) (l : Nat) (q : Pos) :
    (s.pushTempShaped v l).tyAt q = s.tyAt q := by
  rw [← tyAt_pushTemp s v q]; unfold SState.pushTempShaped; dsimp only; split <;> rfl

theorem heldTy_pushTempShaped (s : SState) (v : SVal) (l : Nat) : (s.pushTempShaped v l).heldTy = s.heldTy := by
  unfold SState.pushTempShaped; dsimp only; split <;> rfl

theorem heldMem_pushTempShaped (s : SState) (v : SVal) (l : Nat) : (s.pushTempShaped v l).heldMem = s.heldMem := by
  unfold SState.pushTempShaped; dsimp only; split <;> rfl

theorem bind_mem_pushTempShaped (s : SState) (v : SVal) (l : Nat) (f i : Nat) :
    Pos.bind f i ∈ (s.pushTempShaped v l).positions ↔ Pos.bind f i ∈ s.positions := by
  rw [SState.positions_pushTempShaped, bind_mem_pushTemp]

theorem valAt_pushTempShaped_bind (s : SState) (v : SVal) (l : Nat) (f i : Nat) :
    (s.pushTempShaped v l).valAt (.bind f i) = s.valAt (.bind f i) := by
  rw [SState.valAt_pushTempShaped, valAt_pushTemp_bind]

/-- A holder after a borrow is parked: an old holder (same value), or the new temporary (holding the
parked value, the parked label). -/
theorem pushTempShaped_holder {s : SState} (hsa : SState.ShapeAt s) (hne : s.env ≠ []) (w : SVal) (l : Nat)
    {p : Pos} {l' : Nat} (h : (s.pushTempShaped w l).shape p = some l') :
    (p ∈ s.positions ∧ s.shape p = some l' ∧ (s.pushTempShaped w l).valAt p = s.valAt p) ∨
      (l' = l ∧ (∀ f i, p ≠ .bind f i) ∧ (s.pushTempShaped w l).valAt p = w) := by
  rw [SState.valAt_pushTempShaped]
  obtain ⟨-, hv⟩ := pushTemp_last s w hne
  unfold SState.pushTempShaped at h
  dsimp only at h
  split at h
  · rename_i fr hfr
    simp only at h
    split at h
    · rename_i hp
      simp only [Option.some.injEq] at h
      subst h
      refine .inr ⟨rfl, ?_, ?_⟩
      · intro f i e; rw [hp] at e; cases e
      · rw [hp]
        rw [hfr] at hv
        simpa using hv
    · have := hsa p l' h
      exact .inl ⟨this.1, h, valAt_pushTemp_old s w this.1⟩
  · have := hsa p l' h
    exact .inl ⟨this.1, h, valAt_pushTemp_old s w this.1⟩

/-- Typed futures depend only on the live labels and their content types. -/
theorem typedF_congr {s s' : SState} (hl : ∀ y, y ∈ s'.liveLabels ↔ y ∈ s.liveLabels) (hh : s'.heldTy = s.heldTy)
    (ψ : Future) : TypedF K.dm K.Γ φ s' ψ ↔ TypedF K.dm K.Γ φ s ψ := by
  unfold TypedF
  simp only [hl, hh]

/-- `takeLabel` at a holder, unfolded. -/
theorem takeLabel_view {s : SState} {l : Nat} {r : Pos} (hr : s.holderOf l = some r) :
    (∀ q, (s.takeLabel l).valAt q = if q = r then (fun _ => .moved) else s.valAt q) ∧
    (∀ q, (s.takeLabel l).shape q = if q = r then none else s.shape q) ∧
    (∀ q, (s.takeLabel l).tyAt q = s.tyAt q) ∧ (s.takeLabel l).heldTy = s.heldTy ∧
    (s.takeLabel l).heldMem = s.heldMem := by
  obtain ⟨hrpos, -⟩ := SState.holderOf_spec hr
  have ht : s.takeLabel l = { s.setAt r (fun _ => .moved) with shape := fun p => if p = r then none else s.shape p } := by
    unfold SState.takeLabel; rw [hr]
  rw [ht]
  refine ⟨fun q => ?_, fun q => rfl, fun q => tyAt_setAt s r _ q, heldTy_setAt s r _, heldMem_setAt s r _⟩
  show (s.setAt r _).valAt q = _
  split
  · rename_i h; subst h; exact valAt_setAt_self s _ _ hrpos
  · rename_i h; exact SState.valAt_setAt_ne s _ _ q (Ne.symm h)

/-- A borrow's holder moves to a new temporary holding a partly moved member of its content type (a
move of a holder, `readPlace`). -/
theorem sgood_transfer {s : SState} (hs : SGood K.dm K.Γ φ s) {l : Nat} (hl : l ∈ s.liveLabels) {v : Sem}
    (hv : PMem K.dm.read K.Γ v (s.heldTy l)) :
    SGood K.dm K.Γ φ ((s.takeLabel l).pushTempShaped (fun _ => v) l) := by
  have hsa := hs.acyc.2.2
  obtain ⟨r, hr⟩ := SState.holderOf_of_live hl
  obtain ⟨hrpos, -⟩ := SState.holderOf_spec hr
  obtain ⟨hval₁, hsh₁, hty₁, hHT₁, hHM₁⟩ := takeLabel_view hr
  have hsa₁ : SState.ShapeAt (s.takeLabel l) := SState.takeLabel_shapeAt hsa l
  have hne₁ : (s.takeLabel l).env ≠ [] := env_ne_of_mem (p := r) (by rw [SState.takeLabel_positions]; exact hrpos)
  have hlive : ∀ y, y ∈ ((s.takeLabel l).pushTempShaped (fun _ => v) l).liveLabels ↔ y ∈ s.liveLabels := by
    intro y
    constructor
    · intro h
      rcases SState.live_pushTempShaped_new hsa₁ h with h | h
      · exact SState.takeLabel_live_rev h
      · rw [h]; exact hl
    · intro h
      by_cases hy : y = l
      · rw [hy]; exact SState.live_pushTempShaped_self _ _ l hne₁
      · exact SState.live_pushTempShaped_old (SState.takeLabel_live h hy)
  have hHT : ((s.takeLabel l).pushTempShaped (fun _ => v) l).heldTy = s.heldTy := by
    rw [heldTy_pushTempShaped, hHT₁]
  have hTF : ∀ ψ, TypedF K.dm K.Γ φ ((s.takeLabel l).pushTempShaped (fun _ => v) l) ψ ↔ TypedF K.dm K.Γ φ s ψ :=
    typedF_congr hlive hHT
  have hbval : ∀ f i, ((s.takeLabel l).pushTempShaped (fun _ => v) l).valAt (.bind f i) =
      if Pos.bind f i = r then (fun _ => .moved) else s.valAt (.bind f i) := by
    intro f i; rw [valAt_pushTempShaped_bind, hval₁]
  have hbty : ∀ q, ((s.takeLabel l).pushTempShaped (fun _ => v) l).tyAt q = s.tyAt q := by
    intro q; rw [tyAt_pushTempShaped, hty₁]
  refine ⟨fun ψ hψ f i hpi => ?_, fun ψ hψ p l' hl' => ?_, fun l' hl' => ?_, fun f i l' hl' => ?_, ?_, ?_,
    fun ψ hψ f i steps x U hf hx => ?_⟩
  · rw [hTF] at hψ
    rw [bind_mem_pushTempShaped, SState.takeLabel_positions] at hpi
    rw [hbval, hbty]
    split
    · exact .inl (.inl rfl)
    · exact hs.bind ψ hψ f i hpi
  · rw [hTF] at hψ
    rw [hHT]
    rcases pushTempShaped_holder hsa₁ hne₁ _ l hl' with ⟨-, hsh, hpv⟩ | ⟨rfl, -, hpv⟩
    · rw [hsh₁] at hsh
      split at hsh
      · cases hsh
      · rename_i hpr
        rw [hpv, hval₁, if_neg hpr]
        exact hs.holder ψ hψ p l' hsh
    · rw [hpv]; exact hv
  · rw [hlive] at hl'
    rw [hHT, heldMem_pushTempShaped, hHM₁]
    exact hs.held l' hl'
  · rw [hHT, hbty]
    rcases pushTempShaped_holder hsa₁ hne₁ _ l hl' with ⟨-, hsh, -⟩ | ⟨-, hnb, -⟩
    · rw [hsh₁] at hsh
      split at hsh
      · cases hsh
      · exact hs.holderTy f i l' hsh
    · exact absurd rfl (hnb f i)
  · exact SState.transfer_rinv hs.acyc l hl v
  · exact SState.readsBelow_pushTempShaped (SState.readsBelow_takeLabel hs.fresh l) _ _
      (fun _ ⟨_, _, h⟩ => absurd rfl h)
  · rw [hTF] at hψ
    rw [hbval, hbty] at hf
    split at hf
    · rw [follow_moved' K.dm K.Γ _ _ _ _ hf] at hx; exact absurd hx (by simp [Sem.whole])
    · exact hs.read ψ hψ f i steps x U hf hx

/-! ## Pushing a binding -/

/-- The binding slots after a push: the new one at the end of the top frame. -/
theorem pushBind_binds (s : SState) (b : SBinding) {fr0 : SFrame} (e2 : s.env[s.topIdx]? = some fr0) (f i : Nat) :
    (s.pushBind b).env[f]?.bind (·.binds[i]?) =
      if f = s.topIdx ∧ i = fr0.binds.length then some b else s.env[f]?.bind (·.binds[i]?) := by
  simp only [SState.pushBind, List.getElem?_modify]
  by_cases hf : s.topIdx = f
  · subst hf
    rw [e2]
    by_cases hi : i = fr0.binds.length
    · subst hi; simp
    · by_cases hlt : i < fr0.binds.length
      · simp [hi, List.getElem?_append_left hlt]
      · have h1 : fr0.binds[i]? = none := List.getElem?_eq_none (by omega)
        have h2 : (fr0.binds ++ [b])[i]? = none := List.getElem?_eq_none (by simp; omega)
        simp [hi, h1, h2]
  · have hn : ¬ (f = s.topIdx ∧ i = fr0.binds.length) := fun h => hf h.1.symm
    simp only [hf, if_false, hn]
    cases s.env[f]? <;> rfl

theorem pushBind_temps (s : SState) (b : SBinding) (f i : Nat) :
    (s.pushBind b).env[f]?.bind (·.temps[i]?) = s.env[f]?.bind (·.temps[i]?) := by
  simp only [SState.pushBind, List.getElem?_modify]
  split <;> cases s.env[f]? <;> simp

/-- **A pushed binding, unfolded**: a new position `N` (a binding, not among the old), holding the
binding's meaning at its type; everything else as before. -/
theorem pushBind_view (s : SState) (b : SBinding) (hne : s.env ≠ []) :
    ∃ f₀ i₀, Pos.bind f₀ i₀ ∉ s.positions ∧
      (∀ q, q ∈ (s.pushBind b).positions ↔ q ∈ s.positions ∨ q = .bind f₀ i₀) ∧
      (∀ q, (s.pushBind b).valAt q = if q = .bind f₀ i₀ then b.val else s.valAt q) ∧
      (∀ q, (s.pushBind b).tyAt q = if q = .bind f₀ i₀ then b.ty else s.tyAt q) ∧
      (s.pushBind b).shape = s.shape ∧ (s.pushBind b).heldTy = s.heldTy ∧
      (s.pushBind b).heldMem = s.heldMem ∧ (s.pushBind b).nextLoan = s.nextLoan ∧
      ∀ fr, (s.pushBind b).env.getLast? = some fr → Pos.bind (s.pushBind b).topIdx (fr.binds.length - 1) = .bind f₀ i₀ := by
  obtain ⟨fr0, e⟩ : ∃ fr0, s.env.getLast? = some fr0 := by
    cases h : s.env.getLast? with
    | none => exact absurd (List.getLast?_eq_none_iff.mp h) hne
    | some fr0 => exact ⟨fr0, rfl⟩
  have e2 : s.env[s.topIdx]? = some fr0 := by
    rw [List.getLast?_eq_getElem?] at e; simpa [SState.topIdx] using e
  have hB := pushBind_binds s b e2
  have hT := pushBind_temps s b
  refine ⟨s.topIdx, fr0.binds.length, ?_, fun q => ?_, fun q => ?_, fun q => ?_, rfl, rfl, rfl, rfl, fun fr hfr => ?_⟩
  · rw [SState.mem_positions]; simp [SState.lookup, e2]
  · rw [SState.mem_positions, SState.mem_positions]
    cases q with
    | temp f i => simp only [SState.lookup, hT, reduceCtorEq, or_false]
    | bind f i =>
      simp only [SState.lookup, hB, Pos.bind.injEq]
      by_cases h : f = s.topIdx ∧ i = fr0.binds.length
      · rw [if_pos h]; simp [h]
      · rw [if_neg h]; simp [h]
  · cases q with
    | temp f i => simp only [SState.valAt, hT, reduceCtorEq, if_false]
    | bind f i =>
      simp only [SState.valAt, hB, Pos.bind.injEq]
      by_cases h : f = s.topIdx ∧ i = fr0.binds.length
      · rw [if_pos h, if_pos h]
      · rw [if_neg h, if_neg h]
  · cases q with
    | temp f i => rfl
    | bind f i =>
      simp only [SState.tyAt, hB, Pos.bind.injEq]
      by_cases h : f = s.topIdx ∧ i = fr0.binds.length
      · rw [if_pos h, if_pos h]
      · rw [if_neg h, if_neg h]
  · rw [SState.pushBind_getLast, e] at hfr
    simp only [Option.map_some, Option.some.injEq] at hfr
    subst hfr
    simp [SState.pushBind_topIdx]

/-- On a type value, a read gives the value itself at the type it started from, or nothing. -/
theorem follow_ty (dm : DataModel) (Γ : List IndDecl) (X : TyM) : ∀ (T : TyS) (steps : List Step) (x : Sem) (U : TyS),
    Sem.follow dm Γ T (.ty X) steps = some (x, U) → x = .ty X ∧ U = T
  | _, [], _, _, h => by simp only [Sem.follow, Option.some.injEq, Prod.mk.injEq] at h; exact ⟨h.1.symm, h.2.symm⟩
  | T, st :: sts, x, U, h => by
    simp only [Sem.follow] at h
    cases st with
    | deref => exact follow_ty dm Γ X T sts x U (by simpa [Sem.step] using h)
    | proj i =>
      cases i with
      | zero => simp [Sem.step, Sem.asNat, Sem.as, Sem.stepField] at h
      | succ i => simp [Sem.step, Sem.stepField] at h
    | field g => simp [Sem.step, Sem.stepField] at h

/-- A good result's read paths: a member's (`MemReads`), `⊥`'s (nothing whole), a type value's (itself, at
the error type). -/
theorem GoodRes.reads (hMR : MemReads K.dm K.Γ) {v : Sem} {T : TyS} (hv : GoodRes K.dm.read (v, T))
    (steps : List Step) (x : Sem) (U : TyS) (hf : Sem.follow K.dm K.Γ T v steps = some (x, U)) (hx : x.whole) :
    x ∈ₛ[K.dm.read] U.m ∨ U.m = TyM.err := by
  rcases hv with hv | hv | ⟨he, X, hX⟩
  · exact hMR T v v hv (.refl v) steps x U hf hx
  · simp only at hv; subst hv
    rw [follow_moved' K.dm K.Γ _ _ _ _ hf] at hx; exact absurd hx (by simp [Sem.whole])
  · simp only at hX; subst hX
    obtain ⟨-, rfl⟩ := follow_ty K.dm K.Γ X T steps x U hf
    exact .inr he

theorem readsBelow_pushBind {s : SState} (hs : s.ReadsBelow) (b : SBinding) {c : Sem} (hb : b.val = fun _ => c) :
    (s.pushBind b).ReadsBelow := by
  intro q l ⟨ψ, x, hne⟩
  show l < s.nextLoan
  rcases SState.valAt_pushBind s b q with e | e
  · exact hs q l ⟨ψ, x, by simpa [SState.toMean, e] using hne⟩
  · rw [hb] at e; exfalso; simp [SState.toMean, e] at hne

/-- `takeLabel`, read position by position: a value is the old one or `⊥`; a holder after it held the
same label before, with the same value. -/
theorem takeLabel_facts (s : SState) (l : Nat) :
    (∀ q, (s.takeLabel l).valAt q = s.valAt q ∨ (s.takeLabel l).valAt q = fun _ => .moved) ∧
    (∀ q l', (s.takeLabel l).shape q = some l' → s.shape q = some l' ∧ (s.takeLabel l).valAt q = s.valAt q) ∧
    (∀ q, (s.takeLabel l).tyAt q = s.tyAt q) ∧ (s.takeLabel l).heldTy = s.heldTy ∧
    (s.takeLabel l).heldMem = s.heldMem ∧ (s.takeLabel l).positions = s.positions := by
  cases hr : s.holderOf l with
  | none =>
    have ht : s.takeLabel l = s := by unfold SState.takeLabel; rw [hr]
    rw [ht]; exact ⟨fun _ => .inl rfl, fun q l' h => ⟨h, rfl⟩, fun _ => rfl, rfl, rfl, rfl⟩
  | some r =>
    obtain ⟨hval, hsh, hty, hHT, hHM⟩ := takeLabel_view hr
    refine ⟨fun q => SState.takeLabel_valAt s l q, fun q l' h => ?_, hty, hHT, hHM, SState.takeLabel_positions s l⟩
    rw [hsh] at h
    split at h
    · cases h
    · rename_i hq; exact ⟨h, by rw [hval, if_neg hq]⟩

theorem withShape_valAt (S : SState) (sh : Pos → Option Nat) : ({ S with shape := sh } : SState).valAt = S.valAt := rfl
theorem withShape_tyAt (S : SState) (sh : Pos → Option Nat) : ({ S with shape := sh } : SState).tyAt = S.tyAt := rfl
theorem withShape_heldTy (S : SState) (sh : Pos → Option Nat) : ({ S with shape := sh } : SState).heldTy = S.heldTy := rfl
theorem withShape_heldMem (S : SState) (sh : Pos → Option Nat) : ({ S with shape := sh } : SState).heldMem = S.heldMem := rfl
theorem withShape_positions (S : SState) (sh : Pos → Option Nat) (q : Pos) :
    q ∈ ({ S with shape := sh } : SState).positions ↔ q ∈ S.positions := Iff.rfl

/-- **A binding pushed, abstractly** (both shapes of `pushBindShaped`): a new binding position `N`
holding a good result `v` at `T`, recording `T`'s label, over a state `s₁` that is `s` with a label's old
holder taken (`⊥`); the label is live in `s` or read by no one. -/
theorem sgood_push_generic (hMR : MemReads K.dm K.Γ) {s s₁ S : SState} (hs : SGood K.dm K.Γ φ s) {f₀ i₀ : Nat}
    {v : Sem} {T : TyS} {lab : Option Nat} (hN : Pos.bind f₀ i₀ ∉ s.positions)
    (hpos : ∀ q, q ∈ S.positions ↔ q ∈ s.positions ∨ q = .bind f₀ i₀)
    (hval : ∀ q, q ≠ .bind f₀ i₀ → S.valAt q = s₁.valAt q) (hvalN : S.valAt (.bind f₀ i₀) = fun _ => v)
    (hty : ∀ q, q ≠ .bind f₀ i₀ → S.tyAt q = s.tyAt q) (htyN : S.tyAt (.bind f₀ i₀) = T)
    (hsh : ∀ q, q ≠ .bind f₀ i₀ → S.shape q = s₁.shape q) (hshN : S.shape (.bind f₀ i₀) = lab)
    (h1val : ∀ q, s₁.valAt q = s.valAt q ∨ s₁.valAt q = fun _ => .moved)
    (h1sh : ∀ q l', s₁.shape q = some l' → s.shape q = some l' ∧ s₁.valAt q = s.valAt q)
    (hHT : S.heldTy = s.heldTy) (hHM : S.heldMem = s.heldMem)
    (hlive : ∀ y, y ∈ S.liveLabels ↔ y ∈ s.liveLabels ∨ lab = some y)
    (hv : GoodRes K.dm.read (v, T)) (hlab : LabOk K.dm s (v, T)) (hlabT : lab = T.label)
    (hind : ∀ l, lab = some l → l ∉ s.liveLabels → ∀ q, Indep l (s.valAt q))
    (hacyc : SState.RInv (fun _ => True) S) (hfresh : S.ReadsBelow) : SGood K.dm K.Γ φ S := by
  -- a future typed after, read before: the label, if it was not live, at the run's future
  let ψ₀ : Future → Future := fun ψ y => if y ∉ s.liveLabels ∧ lab = some y then φ y else ψ y
  have hT1 : ∀ ψ, TypedF K.dm K.Γ φ S ψ → TypedF K.dm K.Γ φ s (ψ₀ ψ) := by
    rintro ψ ⟨hag, hψ⟩
    refine ⟨fun y hy => ?_, fun y hy => ?_⟩
    · show (if y ∉ s.liveLabels ∧ lab = some y then φ y else ψ y) = φ y
      split
      · rfl
      · rename_i hc
        have hl : lab ≠ some y := fun e => hc ⟨hy, e⟩
        exact hag y (fun h => ((hlive y).1 h).elim hy hl)
    · show PMem _ _ (if y ∉ s.liveLabels ∧ lab = some y then φ y else ψ y) _
      rw [if_neg (fun h => h.1 hy)]
      have := hψ y ((hlive y).2 (.inl hy)); rwa [hHT] at this
  have hT2 : ∀ ψ q, s.valAt q (ψ₀ ψ) = s.valAt q ψ := by
    intro ψ q
    by_cases hc : ∃ l, lab = some l ∧ l ∉ s.liveLabels
    · obtain ⟨l, hl, hnl⟩ := hc
      have e : ψ₀ ψ = ψ.upd l (φ l) := by
        funext y
        show (if y ∉ s.liveLabels ∧ lab = some y then φ y else ψ y) = _
        by_cases hy : y = l
        · subst hy; rw [if_pos ⟨hnl, hl⟩, Future.upd_same]
        · rw [if_neg (fun h => hy (Option.some.inj (h.2.symm.trans hl))), Future.upd_other _ _ hy]
      rw [e]; exact hind l hl hnl q ψ (φ l)
    · have e : ψ₀ ψ = ψ := by
        funext y
        show (if y ∉ s.liveLabels ∧ lab = some y then φ y else ψ y) = _
        rw [if_neg (fun h => hc ⟨y, h.2, h.1⟩)]
      rw [e]
  have hPv : ∀ l, lab = some l → PMem K.dm.read K.Γ v (s.heldTy l) := by
    intro l hl
    obtain ⟨h1, h2⟩ := hlab l (hlabT ▸ hl)
    rw [h1]
    rcases hv with hv | hv | ⟨he, -⟩
    · exact .inr ⟨v, mem_whole K.dm.read_wholeFields hv, .refl v, hv⟩
    · exact .inl hv
    · rw [h1, he] at h2; exact absurd h2 (DataModel.err_mem_false _ _)
  refine ⟨fun ψ hψ f i hpi => ?_, fun ψ hψ p l' hl' => ?_, fun l' hl' => ?_, fun f i l' hl' => ?_, hacyc, hfresh,
    fun ψ hψ f i steps x U hf hx => ?_⟩
  · show GoodVal _ _ (S.valAt _ ψ) (S.tyAt _).m
    by_cases hq : Pos.bind f i = .bind f₀ i₀
    · rw [hq, hvalN, htyN]; exact hv.val K.dm.read_wholeFields K.Γ
    · have hpi' : Pos.bind f i ∈ s.positions := ((hpos _).1 hpi).resolve_right hq
      rw [hval _ hq, hty _ hq]
      rcases h1val (.bind f i) with e | e
      · rw [e, ← hT2 ψ]; exact hs.bind _ (hT1 ψ hψ) f i hpi'
      · rw [e]; exact .inl (.inl rfl)
  · rw [hHT]
    by_cases hq : p = .bind f₀ i₀
    · subst hq; rw [hshN] at hl'; rw [hvalN]; exact hPv l' hl'
    · rw [hsh _ hq] at hl'
      obtain ⟨hl'', e⟩ := h1sh p l' hl'
      rw [hval _ hq, e, ← hT2 ψ]
      exact hs.holder _ (hT1 ψ hψ) p l' hl''
  · rw [hHT, hHM]
    rcases (hlive l').1 hl' with h | h
    · exact hs.held l' h
    · exact (hlab l' (hlabT ▸ h)).2
  · rw [hHT]
    by_cases hq : Pos.bind f i = .bind f₀ i₀
    · rw [hq, htyN]; rw [hq, hshN] at hl'; exact (hlab l' (hlabT ▸ hl')).1.symm
    · rw [hty _ hq]; rw [hsh _ hq] at hl'
      exact hs.holderTy f i l' (h1sh _ l' hl').1
  · by_cases hq : Pos.bind f i = .bind f₀ i₀
    · rw [hq, hvalN, htyN] at hf; exact hv.reads hMR steps x U hf hx
    · rw [hval _ hq, hty _ hq] at hf
      rcases h1val (.bind f i) with e | e
      · rw [e, ← hT2 ψ] at hf; exact hs.read _ (hT1 ψ hψ) f i steps x U hf hx
      · rw [e] at hf; rw [follow_moved' K.dm K.Γ _ _ _ _ hf] at hx; exact absurd hx (by simp [Sem.whole])

/-- A `let`'s binding (`pushBindShaped`) of a good result whose label records its type.

ADDED HYPOTHESIS `hlou` (`RunPresInd`'s `LoU` for the label in flight: live, or read by no position, and
below the counter): the binding becomes the label's holder, so the label is live after; if it was not
live before, a position that read it would be read at a future the typed futures before did not
constrain there, and a label at or above the counter would break the label order (`RInv`'s `ShapeAt`).
`RunPresInd.runT_rinv` concludes exactly this of every result (`LoU s' r.2.label`), so the lemma's
induction carries it beside `LabOk`. -/
theorem sgood_pushBindShaped (hMR : MemReads K.dm K.Γ) {s : SState} (hs : SGood K.dm K.Γ φ s) (b : SBinding)
    {v : Sem} (hb : b.val = fun _ => v) (hv : GoodRes K.dm.read (v, b.ty)) (hlab : LabOk K.dm s (v, b.ty))
    (hlou : LoU s b.ty.label) (hne : s.env ≠ []) : SGood K.dm K.Γ φ (pushBindShaped s b) := by
  have hsa := hs.acyc.2.2
  have hacyc := SState.pushBindShaped_rinv hs.acyc b v hb
    (fun l hl => ⟨(hlou l hl).1.elim .inl (fun h => .inr (.inr h)), (hlou l hl).2⟩)
  have hlive : ∀ y, y ∈ (pushBindShaped s b).liveLabels ↔ y ∈ s.liveLabels ∨ b.ty.label = some y :=
    fun y => live_pushBindShaped hsa b hne y
  have hfresh : (pushBindShaped s b).ReadsBelow := by
    unfold pushBindShaped
    split
    · dsimp only
      split
      · intro q k h; exact readsBelow_pushBind (SState.readsBelow_takeLabel hs.fresh _) b hb q k h
      · exact readsBelow_pushBind (SState.readsBelow_takeLabel hs.fresh _) b hb
    · exact readsBelow_pushBind hs.fresh b hb
  have hind : ∀ l, b.ty.label = some l → l ∉ s.liveLabels → ∀ q, Indep l (s.valAt q) :=
    fun l hl hnl => (hlou l hl).1.resolve_left hnl
  generalize hS : pushBindShaped s b = S at hacyc hlive hfresh
  cases hl : b.ty.label with
  | none =>
    unfold pushBindShaped at hS; rw [hl] at hS; dsimp only at hS; subst hS
    obtain ⟨f₀, i₀, hN, hpos, hval, hty, hsh, hHT, hHM, -, -⟩ := pushBind_view s b hne
    have hshN : s.shape (.bind f₀ i₀) = none := by
      cases h : s.shape (.bind f₀ i₀) with
      | none => rfl
      | some x => exact absurd (hsa _ x h).1 hN
    refine sgood_push_generic hMR (s₁ := s) hs hN hpos (fun q hq => by rw [hval, if_neg hq])
      (by rw [hval, if_pos rfl, hb]) (fun q hq => by rw [hty, if_neg hq]) (by rw [hty, if_pos rfl])
      (fun q _ => by rw [hsh]) (by rw [hsh, hshN]) (fun _ => .inl rfl) (fun q l' h => ⟨h, rfl⟩) hHT hHM
      (fun y => by rw [hlive, hl]) hv hlab hl.symm (fun l h => by cases h) hacyc hfresh
  | some l =>
    have hne₁ : (s.takeLabel l).env ≠ [] := by
      intro he; apply hne
      have := (envLe_takeLabel s l).1
      rw [he] at this; exact List.eq_nil_of_length_eq_zero this.symm
    obtain ⟨f₀, i₀, hN, hpos, hval, hty, hsh, hHT, hHM, -, hlast⟩ := pushBind_view (s.takeLabel l) b hne₁
    obtain ⟨h1val, h1sh, h1ty, h1HT, h1HM, h1pos⟩ := takeLabel_facts s l
    obtain ⟨fr1, e1⟩ : ∃ fr1, (s.takeLabel l).env.getLast? = some fr1 := by
      cases h : (s.takeLabel l).env.getLast? with
      | none => exact absurd (List.getLast?_eq_none_iff.mp h) hne₁
      | some fr1 => exact ⟨fr1, rfl⟩
    have e2 : ((s.takeLabel l).pushBind b).env.getLast? = some { fr1 with binds := fr1.binds ++ [b] } := by
      rw [SState.pushBind_getLast, e1]; rfl
    have hN' := hlast _ e2
    unfold pushBindShaped at hS; rw [hl] at hS; dsimp only at hS; rw [e2] at hS; dsimp only at hS
    rw [hN'] at hS
    subst hS
    refine sgood_push_generic hMR (s₁ := s.takeLabel l) hs (by rwa [h1pos] at hN)
      (fun q => by rw [withShape_positions, hpos, h1pos])
      (fun q hq => by rw [withShape_valAt, hval, if_neg hq])
      (by rw [withShape_valAt, hval, if_pos rfl, hb])
      (fun q hq => by rw [withShape_tyAt, hty, if_neg hq, h1ty])
      (by rw [withShape_tyAt, hty, if_pos rfl])
      (fun q hq => by show (if q = _ then some l else _) = _; rw [if_neg hq, hsh])
      (by show (if _ = _ then some l else _) = _; rw [if_pos rfl])
      h1val h1sh (by rw [withShape_heldTy, hHT, h1HT])
      (by rw [withShape_heldMem, hHM, h1HM])
      (fun y => by rw [hlive, hl]) hv hlab hl.symm (fun l' h => by cases h; exact hind l hl)
      hacyc hfresh

/-! ## A `let`'s drop -/

/-- On the error value, a read gives `err` or nothing. -/
theorem follow_err (dm : DataModel) (Γ : List IndDecl) : ∀ (T : TyS) (steps : List Step) (x : Sem) (U : TyS),
    Sem.follow dm Γ T .err steps = some (x, U) → x = .err
  | _, [], _, _, h => by simp only [Sem.follow, Option.some.injEq, Prod.mk.injEq] at h; exact h.1.symm
  | T, st :: sts, x, U, h => by
    simp only [Sem.follow] at h
    cases st with
    | deref => exact follow_err dm Γ T sts x U (by simpa [Sem.step] using h)
    | proj i =>
      cases i with
      | zero => simp [Sem.step, Sem.asNat, Sem.as, Sem.stepField] at h
      | succ i => simp [Sem.step, Sem.stepField] at h
    | field g => simp [Sem.step, Sem.stepField] at h

theorem binds_dropLast (s : SState) (f i : Nat) (hq : some (Pos.bind f i) ≠ s.dropped) :
    s.dropLast.env[f]?.bind (·.binds[i]?) = s.env[f]?.bind (·.binds[i]?) := by
  simp only [SState.dropLast, List.getElem?_modify]
  split
  · rename_i hf
    cases e : s.env[f]? with
    | none => simp
    | some fr =>
      simp only [Functor.map, Option.map_some, Option.bind_some]
      have hlast : s.env.getLast? = some fr := by
        rw [List.getLast?_eq_getElem?]; rw [← hf] at e; simpa [SState.topIdx] using e
      have hi : i ≠ fr.binds.length - 1 := by
        intro hi; apply hq; simp [SState.dropped, hlast, hf, hi]
      by_cases hlt : i < fr.binds.length - 1
      · rw [List.getElem?_dropLast]; simp [hlt]
      · have h1 : fr.binds.dropLast[i]? = none := List.getElem?_eq_none (by simp; omega)
        have h2 : fr.binds[i]? = none := List.getElem?_eq_none (by omega)
        rw [h1, h2]
  · cases s.env[f]? <;> simp

theorem tyAt_dropLast (s : SState) (q : Pos) (hq : some q ≠ s.dropped) : s.dropLast.tyAt q = s.tyAt q := by
  cases q with
  | temp f i => rfl
  | bind f i =>
    show (match s.dropLast.env[f]?.bind (·.binds[i]?) with | some b => b.ty | none => .plain TyM.err) = _
    rw [binds_dropLast s f i hq]; rfl

/-- **Dropping the last binding keeps the invariant** where the label it may still hold is read by no
position (the `let`'s drop ends that label first): a future typed after, with that label set to its
record, is typed before, and nothing reads the label. -/
theorem sgood_dropLast {s : SState} (hs : SGood K.dm K.Γ φ s)
    (hind : ∀ r x, s.dropped = some r → s.shape r = some x → ∀ p, Indep x (s.valAt p)) :
    SGood K.dm K.Γ φ s.dropLast := by
  have hHT : s.dropLast.heldTy = s.heldTy := rfl
  have hHM : s.dropLast.heldMem = s.heldMem := rfl
  have hsub : ∀ p x, s.dropLast.shape p = some x → s.shape p = some x := (SState.shapeSub_dropLast s).1
  have hlive_sub : ∀ y, y ∈ s.dropLast.liveLabels → y ∈ s.liveLabels := by
    intro y hy
    obtain ⟨q, hq, h⟩ := (SState.live_iff _ y).1 hy
    exact (SState.live_iff s y).2 ⟨q, (SState.mem_positions_dropLast hq).1, hsub q y h⟩
  -- a label live before and not after was held only by the dropped binding, so nothing reads it
  have hgone : ∀ y, y ∈ s.liveLabels → y ∉ s.dropLast.liveLabels → ∀ p, Indep y (s.valAt p) := by
    intro y hy hny
    obtain ⟨q, hq, h⟩ := (SState.live_iff s y).1 hy
    by_cases hqd : some q = s.dropped
    · exact hind q y hqd.symm h
    · exact absurd ((SState.live_iff _ y).2 ⟨q, SState.mem_positions_dropLast' hq hqd,
        by rw [SState.dropLast_shape, if_neg hqd]; exact h⟩) hny
  let ψ' : Future → Future := fun ψ y => if y ∈ s.liveLabels ∧ y ∉ s.dropLast.liveLabels then s.heldMem y else ψ y
  have hT1 : ∀ ψ, TypedF K.dm K.Γ φ s.dropLast ψ → TypedF K.dm K.Γ φ s (ψ' ψ) := by
    rintro ψ ⟨hag, hψ⟩
    refine ⟨fun y hy => ?_, fun y hy => ?_⟩
    · show (if y ∈ s.liveLabels ∧ y ∉ s.dropLast.liveLabels then _ else ψ y) = φ y
      rw [if_neg (fun h => hy h.1)]; exact hag y (fun h => hy (hlive_sub y h))
    · show PMem _ _ (if y ∈ s.liveLabels ∧ y ∉ s.dropLast.liveLabels then _ else ψ y) _
      split
      · exact .inr ⟨_, mem_whole K.dm.read_wholeFields (hs.held y hy), .refl _, hs.held y hy⟩
      · rename_i hc
        have hy' : y ∈ s.dropLast.liveLabels := Classical.byContradiction fun h => hc ⟨hy, h⟩
        exact hψ y hy'
  have hT2 : ∀ ψ p, s.valAt p (ψ' ψ) = s.valAt p ψ := by
    intro ψ p
    -- the labels updated are each read by no one; there is at most the dropped binding's
    by_cases hc : ∃ y, y ∈ s.liveLabels ∧ y ∉ s.dropLast.liveLabels
    · obtain ⟨y, hy, hny⟩ := hc
      have huniq : ∀ z, z ∈ s.liveLabels ∧ z ∉ s.dropLast.liveLabels → z = y := by
        intro z ⟨hz, hnz⟩
        obtain ⟨q, hq, h⟩ := (SState.live_iff s z).1 hz
        obtain ⟨q', hq', h'⟩ := (SState.live_iff s y).1 hy
        have e1 : some q = s.dropped := Classical.byContradiction fun hqd => hnz ((SState.live_iff _ z).2
          ⟨q, SState.mem_positions_dropLast' hq hqd, by rw [SState.dropLast_shape, if_neg hqd]; exact h⟩)
        have e2 : some q' = s.dropped := Classical.byContradiction fun hqd => hny ((SState.live_iff _ y).2
          ⟨q', SState.mem_positions_dropLast' hq' hqd, by rw [SState.dropLast_shape, if_neg hqd]; exact h'⟩)
        have : q = q' := Option.some.inj (e1.trans e2.symm)
        subst this; exact Option.some.inj (h.symm.trans h')
      have e : ψ' ψ = ψ.upd y (s.heldMem y) := by
        funext z
        show (if z ∈ s.liveLabels ∧ z ∉ s.dropLast.liveLabels then s.heldMem z else ψ z) = _
        split
        · rename_i hz; rw [huniq z hz, Future.upd_same]
        · rename_i hz
          have hzy : z ≠ y := fun e => hz (e ▸ ⟨hy, hny⟩)
          rw [Future.upd_other _ _ hzy]
      rw [e]; exact hgone y hy hny p ψ _
    · have e : ψ' ψ = ψ := by
        funext z
        show (if z ∈ s.liveLabels ∧ z ∉ s.dropLast.liveLabels then s.heldMem z else ψ z) = _
        rw [if_neg (fun h => hc ⟨z, h⟩)]
      rw [e]
  refine ⟨fun ψ hψ f i hpi => ?_, fun ψ hψ p l' hl' => ?_, fun l' hl' => ?_, fun f i l' hl' => ?_, ?_, ?_,
    fun ψ hψ f i steps x U hf hx => ?_⟩
  · obtain ⟨hpi', hd⟩ := SState.mem_positions_dropLast hpi
    show GoodVal _ _ (s.dropLast.valAt _ ψ) (s.dropLast.tyAt _).m
    rw [SState.valAt_dropLast s _ hd, tyAt_dropLast s _ hd, ← hT2 ψ]
    exact hs.bind _ (hT1 ψ hψ) f i hpi'
  · rw [SState.dropLast_shape] at hl'
    split at hl'
    · cases hl'
    · rename_i hd
      rw [SState.valAt_dropLast s _ hd, hHT, ← hT2 ψ]
      exact hs.holder _ (hT1 ψ hψ) p l' hl'
  · rw [hHT, hHM]; exact hs.held l' (hlive_sub l' hl')
  · rw [SState.dropLast_shape] at hl'
    split at hl'
    · cases hl'
    · rename_i hd; rw [tyAt_dropLast s _ hd, hHT]; exact hs.holderTy f i l' hl'
  · exact SState.dropLast_rinv hs.acyc hind
  · intro q l ⟨ψ, x, hne⟩
    show l < s.nextLoan
    by_cases hd : some q = s.dropped
    · exfalso
      have hq : q ∉ s.dropLast.positions := fun h => (SState.mem_positions_dropLast h).2 hd
      apply hne; simp [SState.toMean, SState.valAt_of_not_mem _ _ hq]
    · exact hs.fresh q l ⟨ψ, x, by simpa [SState.toMean, SState.valAt_dropLast s _ hd] using hne⟩
  · by_cases hd : some (Pos.bind f i) = s.dropped
    · have hq : Pos.bind f i ∉ s.dropLast.positions := fun h => (SState.mem_positions_dropLast h).2 hd
      rw [SState.valAt_of_not_mem _ _ hq] at hf
      rw [follow_err K.dm K.Γ _ _ _ _ hf] at hx; exact absurd hx (by simp [Sem.whole])
    · rw [SState.valAt_dropLast s _ hd, tyAt_dropLast s _ hd, ← hT2 ψ] at hf
      exact hs.read _ (hT1 ψ hψ) f i steps x U hf hx

/-- A `let`'s drop: the borrow its binding holds ends, or the borrows lent at it end, then it goes. -/
theorem sgood_letDrop {s : SState} (hs : SGood K.dm K.Γ φ s) :
    SGood K.dm K.Γ φ ((match (match s.env.getLast? with
        | some fr => s.shape (.bind s.topIdx (fr.binds.length - 1))
        | none => none) with
      | some l => s.endLabel l
      | none => letLenders s).dropLast) := by
  have hi := hs.acyc
  generalize hH : (match s.env.getLast? with
      | some fr => s.shape (.bind s.topIdx (fr.binds.length - 1))
      | none => none) = held
  have hheld : held = match s.dropped with | some r => s.shape r | none => none := by
    rw [← hH]; unfold SState.dropped; cases s.env.getLast? <;> rfl
  apply sgood_dropLast
  · cases held with
    | none =>
      show SGood _ _ _ (letLenders s)
      unfold letLenders
      split
      · exact access_sgood hs _ _
      · exact hs
    | some l => exact endLabel_sgood hs l
  · intro r x hr hx
    cases held with
    | none =>
      simp only at hr hx ⊢
      rw [(letLenders_props (fun _ => True) hi).2.2.2.2.1] at hr
      rw [hr] at hheld; simp only at hheld
      rw [(letLenders_props (fun _ => True) hi).2.2.2.2.2 r x hx] at hheld; cases hheld
    | some l =>
      simp only at hr hx ⊢
      rw [dropped_endLabel] at hr
      rw [hr] at hheld; simp only at hheld
      have hrpos : r ∈ s.positions := (hi.2.2 r l hheld.symm).1
      obtain ⟨r', hr'⟩ := SState.holderOf_of_live (live_of_shape hrpos hheld.symm)
      obtain ⟨hr'pos, hr'shape⟩ := SState.holderOf_spec hr'
      rw [SState.endLabel_eq hr'] at hx ⊢
      rw [SState.endAt_shape] at hx
      simp only at hx
      split at hx
      · cases hx
      · rw [← hheld] at hx; cases hx
        exact SState.endAt_indep hi.2.1 hr'pos hr'shape

/-! ## Reads -/

/-- `contentOf`, unfolded: [Access] of the resolved position, then the read at its typed future. -/
theorem contentOf_view {p : Place} {s s₁ : SState} {v : Sem} {T : TyS} {pos : Pos} {steps : List Step}
    (h : contentOf K φ p s = some ((v, T, pos, steps), s₁)) :
    ∃ T', resolve s p = some (pos, steps) ∧ s₁ = s.access pos (dataHit steps) ∧
      Sem.follow K.dm K.Γ (s₁.tyAt pos) (s₁.valAt pos (s₁.typedFuture φ)) steps = some (v, T') ∧
      T = (if steps.isEmpty then s₁.tyAt pos else { T' with label := none }) := by
  unfold contentOf at h
  cases hr : resolve s p with
  | none => rw [hr] at h; cases h
  | some ps =>
    obtain ⟨pos', steps'⟩ := ps
    rw [hr] at h
    dsimp only at h
    cases hf : Sem.follow K.dm K.Γ (s.tyAt pos') ((s.access pos' (dataHit steps')).valAt pos'
        ((s.access pos' (dataHit steps')).typedFuture φ)) steps' with
    | none => rw [hf] at h; cases h
    | some x =>
      obtain ⟨v', T''⟩ := x
      rw [hf] at h
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨⟨rfl, rfl, rfl, rfl⟩, rfl⟩ := h
      exact ⟨T'', rfl, rfl, by rw [tyAt_access]; exact hf, rfl⟩

/-- The typed future of a good state is typed. -/
theorem typedF_typedFuture {s : SState} (hs : SGood K.dm K.Γ φ s) : TypedF K.dm K.Γ φ s (s.typedFuture φ) := by
  refine ⟨fun l hl => ?_, fun l hl => ?_⟩
  · show (if l ∈ s.liveLabels then s.heldMem l else φ l) = φ l
    rw [if_neg hl]
  · show PMem _ _ (if l ∈ s.liveLabels then s.heldMem l else φ l) _
    rw [if_pos hl]
    exact .inr ⟨_, mem_whole K.dm.read_wholeFields (hs.held l hl), .refl _, hs.held l hl⟩

/-- A whole good value at the error type is a type value. -/
theorem GoodVal.ty_of_err {v : Sem} {T : TyM} (h : GoodVal K.dm.read K.Γ v T) (hw : v.whole) (he : T = TyM.err) :
    ∃ X, v = .ty X := by
  rcases h with (h | ⟨t, -, -, ht | ho⟩) | ⟨-, h⟩
  · subst h; exact absurd hw (by simp [Sem.whole])
  · rw [he] at ht; exact absurd ht (DataModel.err_mem_false _ _)
  · rw [he] at ho; exact ho.elim
  · exact h

/-- **A read at a root or through `*`** (the value is the binding's own content). -/
theorem read_root_goodRes {s₁ : SState} (hs₁ : SGood K.dm K.Γ φ s₁) {f i : Nat} (hp : Pos.bind f i ∈ s₁.positions)
    {steps : List Step} (hst : steps = [] ∨ steps = [.deref]) {v : Sem} {T' : TyS}
    (hf : Sem.follow K.dm K.Γ (s₁.tyAt (.bind f i)) (s₁.valAt (.bind f i) (s₁.typedFuture φ)) steps = some (v, T'))
    (hw : v.whole) : v = s₁.valAt (.bind f i) (s₁.typedFuture φ) ∧ T' = s₁.tyAt (.bind f i) ∧
      GoodRes K.dm.read (v, s₁.tyAt (.bind f i)) := by
  have hψ := typedF_typedFuture hs₁
  have e : v = s₁.valAt (.bind f i) (s₁.typedFuture φ) ∧ T' = s₁.tyAt (.bind f i) := by
    rcases hst with rfl | rfl
    · simp only [Sem.follow, Option.some.injEq, Prod.mk.injEq] at hf; exact ⟨hf.1.symm, hf.2.symm⟩
    · simp only [Sem.follow, Sem.step, Option.bind_some, Option.some.injEq, Prod.mk.injEq] at hf
      exact ⟨hf.1.symm, hf.2.symm⟩
  refine ⟨e.1, e.2, ?_⟩
  rcases hs₁.read _ hψ f i steps v T' hf hw with h | h
  · rw [e.2] at h; exact .inl h
  · rw [e.2] at h
    have hg := hs₁.bind _ hψ f i hp
    rw [← e.1] at hg
    exact .inr (.inr ⟨h, hg.ty_of_err hw h⟩)

/-- **A read of a place at a root or through `*`**, copied or moved: the value read is the binding's
whole content, a member of its stored type (the read clause, at the typed future of the accessed
state), or a type value at `err`; a move writes `⊥` there and, at a holder, parks the borrow.

ADDED HYPOTHESIS `hp` (the path is `[]` or `[*]`). At a FIELD path two facts are missing:
(1) for a copy, the read clause `ReadOk` allows any whole value at `err`, where `GoodRes` asks a type
value; a read THROUGH `⋆` gives `⋆` at `err` (`Sem.stepField` on `⋆`, kernel-checked:
`follow_through_proof`), which is no good result, so the copy case needs the read clause's escape to be
`GoodRes`'s (or such reads classed as proofs, which `SM.erasedS` runs and fails at `err`); the copy
case is proved in that form (`readPlace_copy_reads`); (2) for a move, the write of `⊥` into a field
(`readPlace_field_move_sgood`, a guess: the dependent-values area). -/
theorem readPlace_fund (hMR : MemReads K.dm K.Γ) (p : Place) (hp : p.steps.2 = [] ∨ p.steps.2 = [.deref])
    (copy : Bool) : FundAt K.dm K.Γ φ (readPlace K φ p copy) := by
  intro s s' r hs h
  unfold readPlace at h
  simp only [Bind.bind, Option.bind_eq_some_iff] at h
  obtain ⟨⟨⟨v, T, pos, steps⟩, s₁⟩, h1, h⟩ := h
  obtain ⟨T', hres, rfl, hf, hT⟩ := contentOf_view h1
  have hsteps : steps = p.steps.2 := by
    unfold resolve at hres; cases hv : s.varPos p.steps.1 <;> simp_all
  obtain ⟨f, i, rfl⟩ : ∃ f i, pos = .bind f i := by
    have := resolve_bind hres
    cases pos with
    | bind f i => exact ⟨f, i, rfl⟩
    | temp => exact absurd this (by simp [IsTemp])
  have hs₁ := access_sgood hs (.bind f i) (dataHit steps)
  have hp₁ : Pos.bind f i ∈ (s.access (.bind f i) (dataHit steps)).positions := by
    rw [access_positions]; exact resolve_mem hres
  dsimp only at h
  generalize s.access (Pos.bind f i) (dataHit steps) = s₁ at h hf hT hs₁ hp₁
  by_cases hw : v.whole
  rotate_left
  · rw [if_pos hw] at h; cases h
  rw [if_neg (fun hn => hn hw)] at h
  have hst : steps = [] ∨ steps = [.deref] := hsteps ▸ hp
  obtain ⟨hv, hT', hgood⟩ := read_root_goodRes hs₁ hp₁ hst hf hw
  have hTm : T.m = (s₁.tyAt (.bind f i)).m := by rw [hT, hT']; split <;> rfl
  have hgoodT : ∀ X : TyS, X.m = T.m → GoodRes K.dm.read (v, X) := by
    intro X hX; unfold GoodRes at hgood ⊢; simp only at hgood ⊢; rw [hX, hTm]; exact hgood
  cases copy with
  | true =>
    rw [if_pos rfl] at h
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨hgoodT _ rfl, (fun l hl => by cases hl), hs₁⟩
  | false =>
    rw [if_neg (by simp)] at h
    have hsc : setContent K φ (.bind f i) steps .moved s₁ = some (⟨⟩, s₁.setAt (.bind f i) fun _ => .moved) := by
      rcases hst with rfl | rfl <;> rfl
    rw [hsc] at h
    simp only [Option.bind_some, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    have hs₂ : SGood K.dm K.Γ φ (s₁.setAt (.bind f i) fun _ => .moved) :=
      sgood_setAt_pmem hMR hs₁ hp₁ (fun _ _ _ => .inl rfl) (fun _ _ => .inl rfl)
    by_cases hsh : steps.isEmpty = true ∧ ∃ l, s₁.shape (.bind f i) = some l
    · obtain ⟨he, l, hl⟩ := hsh
      simp only [he, if_true, hl]
      have hlive : l ∈ (s₁.setAt (.bind f i) fun _ => .moved).liveLabels := by
        rw [liveLabels_setAt]; exact live_of_shape hp₁ hl
      have hPv : PMem K.dm.read K.Γ v ((s₁.setAt (.bind f i) fun _ => .moved).heldTy l) := by
        rw [heldTy_setAt, hv]; exact hs₁.holder _ (typedF_typedFuture hs₁) _ l hl
      have hHT : ((((s₁.setAt (.bind f i) fun _ => .moved).takeLabel l).pushTempShaped (fun _ => v) l)).heldTy
          = s₁.heldTy := by
        rw [heldTy_pushTempShaped, (takeLabel_facts _ l).2.2.2.1, heldTy_setAt]
      have hHM : ((((s₁.setAt (.bind f i) fun _ => .moved).takeLabel l).pushTempShaped (fun _ => v) l)).heldMem
          = s₁.heldMem := by
        rw [heldMem_pushTempShaped, (takeLabel_facts _ l).2.2.2.2.1, heldMem_setAt]
      refine ⟨hgoodT _ rfl, fun l' hl' => ?_, sgood_transfer hs₂ hlive hPv⟩
      simp only [Option.some.injEq] at hl'; subst hl'
      rw [hHT, hHM]
      refine ⟨?_, hs₁.held _ (live_of_shape hp₁ hl)⟩
      show s₁.heldTy l = T.m
      rw [hTm, hs₁.holderTy f i l hl]
    · have hlab : (if steps.isEmpty = true then s₁.shape (.bind f i) else none) = none := by
        split
        · rename_i he
          cases h' : s₁.shape (.bind f i) with
          | none => rfl
          | some l => exact absurd ⟨he, l, h'⟩ hsh
        · rfl
      simp only [hlab]
      exact ⟨hgoodT _ rfl, (fun l hl => by cases hl), hs₂⟩

/-- **A read through `⋆` gives `⋆` at the error type** (kernel-checked): `Sem.stepField` reads a field
of a proof as `⋆` at `err`, and `(⋆, err)` is no good result. So the read clause's escape (`U.m = err`)
does not give `GoodRes` at a field path: a read of `h.0` with `h` holding `⋆`, from a good state, would
return a result that is not good. -/
theorem follow_through_proof (T : TyS) :
    Sem.follow K.dm K.Γ T .proof [.proj 0] = some (.proof, .plain TyM.err) ∧
      ¬ GoodRes K.dm.read (.proof, .plain TyM.err) := by
  refine ⟨by simp [Sem.follow, Sem.step, Sem.asNat, Sem.as, Sem.stepField], ?_⟩
  rintro (h | h | ⟨-, X, hX⟩)
  · exact DataModel.err_mem_false _ _ h
  · cases h
  · cases hX

/-- **GUESS (the dependent-values area): moving out a part at a FIELD path keeps the invariant.**
`setContent … steps ⊥` at a path other than `[]`/`[*]` rebuilds a constructor value with that field
`⊥` (`Sem.updAt`, `reDat`). The binding stays a partly moved member (`MovedOf`), and a holder's content
too; what may fail is the READ clause at a LATER field of the same value whose declared type reads the
moved one: reads type a field by its declaration at the CURRENT earlier fields (`Places.contentTyS`,
`fieldTyR … (earlier.map Sem.small)`), and `⊥` reads small as `.other`, so the later field's read type
changes while its value does not (`MkDP(n : Nat, x : if n = 0 then Nat else Unit)`, move `n` out, read
`x`). Discharged if the signature gives `err` at an earlier field read `.other` (a read after a move out
of an index is then at `err`), or if the checker forbids moving a field a later field's type reads. -/
theorem setContent_field_moved_sgood {s s' : SState} (hs : SGood K.dm K.Γ φ s) {f i : Nat} {steps : List Step}
    (hst : steps ≠ [] ∧ steps ≠ [.deref]) (h : setContent K φ (.bind f i) steps .moved s = some (⟨⟩, s')) :
    SGood K.dm K.Γ φ s' := by
  sorry

/-- **A read of a place at any path**, in the read clause's form: the value read is a member of the
type the read gives it, or that type is `err` (`follow_through_proof`: not nec. a type value); the
state is good (a move at a FIELD path through `setContent_field_moved_sgood`). -/
theorem readPlace_reads (hMR : MemReads K.dm K.Γ) (p : Place) (copy : Bool) {s s' : SState} {r : Res}
    (hs : SGood K.dm K.Γ φ s) (h : readPlace K φ p copy s = some (r, s')) :
    (r.1 ∈ₛ[K.dm.read] r.2.m ∨ r.2.m = TyM.err) ∧ LabOk K.dm s' r ∧ SGood K.dm K.Γ φ s' := by
  by_cases hp : p.steps.2 = [] ∨ p.steps.2 = [.deref]
  · obtain ⟨hg, hl, hs'⟩ := readPlace_fund hMR p hp copy s s' r hs h
    refine ⟨?_, hl, hs'⟩
    rcases hg with hg | hg | ⟨he, -⟩
    · exact .inl hg
    · -- a read is whole
      exfalso
      unfold readPlace at h
      simp only [Bind.bind, Option.bind_eq_some_iff] at h
      obtain ⟨⟨⟨v, T, pos, steps⟩, s₁⟩, -, h⟩ := h
      dsimp only at h
      by_cases hw : v.whole
      · rw [if_neg (fun hn => hn hw)] at h
        split at h
        · simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, -⟩ := h
          simp only at hg; rw [hg] at hw; exact absurd hw (by simp [Sem.whole])
        · simp only [Option.bind_eq_some_iff] at h
          obtain ⟨_, -, h⟩ := h
          simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, -⟩ := h
          simp only at hg; rw [hg] at hw; exact absurd hw (by simp [Sem.whole])
      · rw [if_pos hw] at h; cases h
    · exact .inr he
  · unfold readPlace at h
    simp only [Bind.bind, Option.bind_eq_some_iff] at h
    obtain ⟨⟨⟨v, T, pos, steps⟩, s₁⟩, h1, h⟩ := h
    obtain ⟨T', hres, rfl, hf, hT⟩ := contentOf_view h1
    have hsteps : steps = p.steps.2 := by
      unfold resolve at hres; cases hv : s.varPos p.steps.1 <;> simp_all
    have hst : steps ≠ [] ∧ steps ≠ [.deref] := ⟨fun e => hp (.inl (hsteps ▸ e)), fun e => hp (.inr (hsteps ▸ e))⟩
    obtain ⟨f, i, rfl⟩ : ∃ f i, pos = .bind f i := by
      have := resolve_bind hres
      cases pos with
      | bind f i => exact ⟨f, i, rfl⟩
      | temp => exact absurd this (by simp [IsTemp])
    have hs₁ := access_sgood hs (.bind f i) (dataHit steps)
    dsimp only at h
    generalize s.access (Pos.bind f i) (dataHit steps) = s₁ at h hf hT hs₁
    have hne : steps.isEmpty = false := by cases steps with | nil => exact absurd rfl hst.1 | cons _ _ => rfl
    have hTm : T.m = T'.m := by rw [hT, hne]; rfl
    by_cases hw : v.whole
    rotate_left
    · rw [if_pos hw] at h; cases h
    rw [if_neg (fun hn => hn hw)] at h
    have hread := hs₁.read _ (typedF_typedFuture hs₁) f i steps v T' hf hw
    split at h
    · simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h
      exact ⟨by simp only; rw [hTm]; exact hread, (fun l hl => by cases hl), hs₁⟩
    · simp only [Option.bind_eq_some_iff] at h
      obtain ⟨⟨⟨⟩, s₂⟩, h2, h⟩ := h
      simp only [hne, Bool.false_eq_true, if_false, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨by simp only; rw [hTm]; exact hread, (fun l hl => by cases hl), setContent_field_moved_sgood hs₁ hst h2⟩

/-! ## Borrows -/

/-- **A fresh borrow of a binding, whole** (`&x`, `&*r`): the binding becomes the lender of the fresh
label `l` (reading `l`'s final content), a new temporary holds the content `v` (a member of the
binding's type), and `l` records that type and `v`. -/
theorem sgood_borrow_root (hMR : MemReads K.dm K.Γ) {s₁ : SState} (hs₁ : SGood K.dm K.Γ φ s₁) {f i : Nat}
    (hp : Pos.bind f i ∈ s₁.positions) {v : Sem} (hv : v ∈ₛ[K.dm.read] (s₁.tyAt (.bind f i)).m) (xs : List Site) :
    SGood K.dm K.Γ φ (((((s₁.freshLoan.2.setAt (.bind f i) fun φ' => φ' s₁.nextLoan).pushTempShaped
      (fun _ => v) s₁.nextLoan).setLent s₁.nextLoan xs).setHeldTy s₁.nextLoan (s₁.tyAt (.bind f i)).m).setHeldMem
        s₁.nextLoan v) := by
  have hsa₁ := hs₁.acyc.2.2
  generalize hl : s₁.nextLoan = l at *
  generalize hTm : (s₁.tyAt (.bind f i)).m = Tm at hv
  -- the stages
  have hF : s₁.freshLoan.2 = { s₁ with nextLoan := l + 1 } := by rw [← hl]; rfl
  rw [hF]
  generalize hS₂ : ({ s₁ with nextLoan := l + 1 } : SState) = S₂
  have h2pos : S₂.positions = s₁.positions := by rw [← hS₂]; rfl
  have h2val : S₂.valAt = s₁.valAt := by rw [← hS₂]; rfl
  have h2ty : S₂.tyAt = s₁.tyAt := by rw [← hS₂]; rfl
  have h2sh : S₂.shape = s₁.shape := by rw [← hS₂]
  have h2HT : S₂.heldTy = s₁.heldTy := by rw [← hS₂]
  have h2HM : S₂.heldMem = s₁.heldMem := by rw [← hS₂]
  have h2nl : S₂.nextLoan = l + 1 := by rw [← hS₂]
  have h2env : S₂.env = s₁.env := by rw [← hS₂]
  generalize hS₃ : S₂.setAt (.bind f i) (fun φ' => φ' l) = S₃
  have hp₂ : Pos.bind f i ∈ S₂.positions := by rw [h2pos]; exact hp
  have h3val : ∀ q, S₃.valAt q = if q = .bind f i then (fun φ' => φ' l) else s₁.valAt q := by
    intro q; rw [← hS₃]
    split
    · rename_i hq; subst hq; exact valAt_setAt_self S₂ _ _ hp₂
    · rename_i hq; rw [SState.valAt_setAt_ne S₂ _ _ q (Ne.symm hq), h2val]
  have h3ty : ∀ q, S₃.tyAt q = s₁.tyAt q := by intro q; rw [← hS₃, tyAt_setAt, h2ty]
  have h3sh : S₃.shape = s₁.shape := by rw [← hS₃, SState.shape_setAt, h2sh]
  have h3pos : S₃.positions = s₁.positions := by rw [← hS₃, SState.positions_setAt, h2pos]
  have h3HT : S₃.heldTy = s₁.heldTy := by rw [← hS₃, heldTy_setAt, h2HT]
  have h3HM : S₃.heldMem = s₁.heldMem := by rw [← hS₃, heldMem_setAt, h2HM]
  have h3env : S₃.env ≠ [] := env_ne_of_mem (p := .bind f i) (by rw [h3pos]; exact hp)
  have hsa₃ : SState.ShapeAt S₃ := by
    intro q x hq
    rw [h3sh] at hq
    obtain ⟨h1, h2⟩ := hsa₁ q x hq
    refine ⟨by rw [h3pos]; exact h1, ?_⟩
    rw [← hS₃, nextLoan_setAt, h2nl]; omega
  have h3live : ∀ y, y ∈ S₃.liveLabels ↔ y ∈ s₁.liveLabels := by
    intro y; unfold SState.liveLabels; rw [h3pos, h3sh]
  have hlnew : l ∉ s₁.liveLabels := fun h => by
    have := hs₁.live_lt h; rw [hl] at this; exact Nat.lt_irrefl l this
  -- the final state, `S`, read through `S₄`
  have hacyc : SState.RInv (fun _ => True) ((((S₃.pushTempShaped (fun _ => v) l).setLent l xs).setHeldTy l Tm).setHeldMem l v) := by
    show SState.RInv _ (S₃.pushTempShaped (fun _ => v) l)
    rw [← hS₃]
    refine SState.writeFresh_park_rinv ?_ _ _ l v (by rw [h2env]; exact env_ne_of_mem hp)
      (fun q x hq => ?_) (by rw [h2nl]; omega) (fun ψ ψ' h => h l (.inl trivial))
      (fun x _ ψ ψ' h => h l (.inr (.inr rfl)))
    · have := SState.freshLoan_rinv (L := fun _ => True) hs₁.acyc
      rwa [hF, hS₂] at this
    · rw [h2sh] at hq; have := (hsa₁ q x hq).2; rw [hl] at this; exact this
  have hfresh : ((((S₃.pushTempShaped (fun _ => v) l).setLent l xs).setHeldTy l Tm).setHeldMem l v).ReadsBelow := by
    show (S₃.pushTempShaped (fun _ => v) l).ReadsBelow
    refine SState.readsBelow_pushTempShaped ?_ _ _ (fun _ ⟨_, _, h⟩ => absurd rfl h)
    rw [← hS₃]
    have h₂ : S₂.ReadsBelow := by
      have := SState.readsBelow_freshLoan hs₁.fresh; rwa [hF, hS₂] at this
    refine SState.readsBelow_setAt h₂ _ _ (fun k ⟨ψ, x, hne⟩ => ?_)
    rw [h2nl]
    by_cases hk : k = l
    · omega
    · exact absurd (by simp [Future.upd, Ne.symm hk]) hne
  generalize hS : ((((S₃.pushTempShaped (fun _ => v) l).setLent l xs).setHeldTy l Tm).setHeldMem l v) = S at hacyc hfresh
  have hSval : ∀ q, S.valAt q = (S₃.pushTempShaped (fun _ => v) l).valAt q := by intro q; rw [← hS]; simp
  have hSty : ∀ q, S.tyAt q = s₁.tyAt q := by intro q; rw [← hS]; simp [tyAt_pushTempShaped, h3ty]
  have hSsh : S.shape = (S₃.pushTempShaped (fun _ => v) l).shape := by rw [← hS]; rfl
  have hSHT : ∀ y, S.heldTy y = if y = l then Tm else s₁.heldTy y := by
    intro y; rw [← hS]; simp only [SState.setHeldMem_heldTy]; show (if y = l then Tm else _) = _
    rw [show ((S₃.pushTempShaped (fun _ => v) l).setLent l xs).heldTy = (S₃.pushTempShaped (fun _ => v) l).heldTy
      from rfl, heldTy_pushTempShaped, h3HT]
  have hSHM : ∀ y, S.heldMem y = if y = l then v else s₁.heldMem y := by
    intro y; rw [← hS]; show (if y = l then v else _) = _
    rw [SState.setHeldTy_heldMem, show ((S₃.pushTempShaped (fun _ => v) l).setLent l xs).heldMem =
      (S₃.pushTempShaped (fun _ => v) l).heldMem from rfl, heldMem_pushTempShaped, h3HM]
  have hSbpos : ∀ f' i', Pos.bind f' i' ∈ S.positions ↔ Pos.bind f' i' ∈ s₁.positions := by
    intro f' i'; rw [← hS]; simp only [SState.setHeldMem_positions, SState.setHeldTy_positions, SState.setLent_positions]
    rw [bind_mem_pushTempShaped, h3pos]
  have hSlive : ∀ y, y ∈ S.liveLabels ↔ y ∈ s₁.liveLabels ∨ y = l := by
    intro y
    have e : y ∈ S.liveLabels ↔ y ∈ (S₃.pushTempShaped (fun _ => v) l).liveLabels := by
      rw [← hS]; rfl
    rw [e]
    constructor
    · intro h
      rcases SState.live_pushTempShaped_new hsa₃ h with h | h
      · exact .inl ((h3live y).1 h)
      · exact .inr h
    · rintro (h | rfl)
      · exact SState.live_pushTempShaped_old ((h3live y).2 h)
      · exact SState.live_pushTempShaped_self _ _ _ h3env
  have hT1 : ∀ ψ, TypedF K.dm K.Γ φ S ψ → TypedF K.dm K.Γ φ s₁ (ψ.upd l (φ l)) := by
    rintro ψ ⟨hag, hψ⟩
    refine ⟨fun y hy => ?_, fun y hy => ?_⟩
    · by_cases hyl : y = l
      · subst hyl; rw [Future.upd_same]
      · rw [Future.upd_other _ _ hyl]; exact hag y (fun h => ((hSlive y).1 h).elim hy hyl)
    · have hyl : y ≠ l := fun e => hlnew (e ▸ hy)
      rw [Future.upd_other _ _ hyl]
      have := hψ y ((hSlive y).2 (.inl hy)); rwa [hSHT, if_neg hyl] at this
  have hT2 : ∀ ψ q, s₁.valAt q (ψ.upd l (φ l)) = s₁.valAt q ψ := fun ψ q =>
    hs₁.indep_fresh q (by rw [hl]; exact Nat.le_refl l) ψ (φ l)
  have hψl : ∀ ψ, TypedF K.dm K.Γ φ S ψ → PMem K.dm.read K.Γ (ψ l) Tm := by
    rintro ψ ⟨-, hψ⟩; have := hψ l ((hSlive l).2 (.inr rfl)); rwa [hSHT, if_pos rfl] at this
  have hbval : ∀ f' i', S.valAt (.bind f' i') =
      if Pos.bind f' i' = .bind f i then (fun φ' => φ' l) else s₁.valAt (.bind f' i') := by
    intro f' i'; rw [hSval, valAt_pushTempShaped_bind, h3val]
  refine ⟨fun ψ hψ f' i' hpi => ?_, fun ψ hψ q l' hl' => ?_, fun y hy => ?_, fun f' i' l' hl' => ?_, hacyc, hfresh,
    fun ψ hψ f' i' steps x U hf hx => ?_⟩
  · show GoodVal _ _ (S.valAt _ ψ) (S.tyAt _).m
    rw [hbval, hSty]
    split
    · rename_i hq; rw [hq, hTm]; exact .inl (hψl ψ hψ).pmem
    · rw [← hT2]; exact hs₁.bind _ (hT1 ψ hψ) f' i' ((hSbpos f' i').1 hpi)
  · rw [hSsh] at hl'
    rcases pushTempShaped_holder hsa₃ h3env _ l hl' with ⟨hq3, hsh3, hv4⟩ | ⟨rfl, -, hv4⟩
    · rw [h3sh] at hsh3
      have hl'l : l' ≠ l := fun e => hlnew (e ▸ live_of_shape (h3pos ▸ hq3) hsh3)
      rw [hSHT, if_neg hl'l, hSval, hv4, h3val]
      split
      · rename_i hq; subst hq
        rw [← hs₁.holderTy f i l' hsh3, hTm]; exact hψl ψ hψ
      · rw [← hT2]; exact hs₁.holder _ (hT1 ψ hψ) q l' hsh3
    · rw [hSHT, if_pos rfl, hSval, hv4]
      exact .inr ⟨v, mem_whole K.dm.read_wholeFields hv, .refl v, hv⟩
  · rw [hSHM, hSHT]
    rcases (hSlive y).1 hy with h | rfl
    · have hyl : y ≠ l := fun e => hlnew (e ▸ h)
      rw [if_neg hyl, if_neg hyl]; exact hs₁.held y h
    · rw [if_pos rfl, if_pos rfl]; exact hv
  · rw [hSsh] at hl'
    rcases pushTempShaped_holder hsa₃ h3env _ l hl' with ⟨hq3, hsh3, -⟩ | ⟨-, hnb, -⟩
    · rw [h3sh] at hsh3
      have hl'l : l' ≠ l := fun e => hlnew (e ▸ live_of_shape (h3pos ▸ hq3) hsh3)
      rw [hSty, hSHT, if_neg hl'l]; exact hs₁.holderTy f' i' l' hsh3
    · exact absurd rfl (hnb f' i')
  · rw [hbval, hSty] at hf
    split at hf
    · rename_i hq; rw [hq] at hf
      have : PMem K.dm.read K.Γ (ψ l) (s₁.tyAt (.bind f i)).m := by rw [hTm]; exact hψl ψ hψ
      exact hMR.pmem this steps x U hf hx
    · rw [← hT2] at hf; exact hs₁.read _ (hT1 ψ hψ) f' i' steps x U hf hx

/-- **GUESS (the dependent-values area): a borrow of a FIELD keeps the invariant.** `&p.f` makes the
lender's FIELD read the fresh label's final content (`Sem.updAt … (φ' l)`), so at a typed future the
field holds some other (partly moved) member of its type, while the rest of the value is unchanged.
What may fail is the READ clause (and `bind`'s membership) at a LATER field whose declared type reads
the lent one: reads type a field by its declaration at the CURRENT earlier fields (`Places.contentTyS`,
`fieldTyR … (earlier.map Sem.small)`), so the later field's read type moves with the future while its
value does not (docs/31's `dws_Pair_dependent_fails`: a borrow of `p.0` of a dependent pair).
Discharged if the checker forbids lending a field a later field's type reads (its dependent-field
rules), or if the invariant compares a lender's later fields at the record's types only. -/
theorem borrowPlace_field_sgood {p : Place} {s s' : SState} {r : Res} (hs : SGood K.dm K.Γ φ s)
    (hfield : p.steps.2 ≠ [] ∧ p.steps.2 ≠ [.deref]) (h : borrowPlace K φ p s = some (r, s'))
    (hm : r.1 ∈ₛ[K.dm.read] r.2.m) : SGood K.dm K.Γ φ s' := by
  sorry

/-- **A borrow** (strict: the content is a member of the place's type). -/
theorem borrowPlace_fund (hMR : MemReads K.dm K.Γ) (p : Place) :
    FundAt K.dm K.Γ φ (SM.strictS K.dm.read (borrowPlace K φ p)) := by
  intro s s' r hs h
  unfold SM.strictS at h
  cases hb : borrowPlace K φ p s with
  | none => rw [hb] at h; cases h
  | some x =>
    rw [hb] at h
    obtain ⟨r₀, s₀⟩ := x
    simp only at h
    by_cases hm : r₀.1 ∈ₛ[K.dm.read] r₀.2.m
    rotate_left
    · rw [if_neg hm] at h; cases h
    rw [if_pos hm] at h
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    have hrinv := borrowPlace_rinv K φ (fun _ => True) hb hs.acyc
    have hfr := borrowPlace_readsBelow K φ p s hs.fresh hb
    have hb₀ := hb
    unfold borrowPlace at hb
    simp only [Bind.bind, Option.bind_eq_some_iff] at hb
    obtain ⟨⟨⟨v, T, pos, steps⟩, s₁⟩, h1, hb⟩ := hb
    dsimp only at hb
    by_cases hw : v.whole
    rotate_left
    · rw [if_pos hw] at hb; cases hb
    rw [if_neg (fun hn => hn hw)] at hb
    simp only [Option.some.injEq, Prod.mk.injEq] at hb
    obtain ⟨rfl, rfl⟩ := hb
    -- the result: a member, its label recording its type and the content
    have hlab : LabOk K.dm (((((s₁.freshLoan.2.setAt pos fun φ' => (Sem.updAt K.dm K.Γ (s₁.freshLoan.2.tyAt pos)
        (fun _ => φ' s₁.freshLoan.1) steps (s₁.freshLoan.2.valAt pos φ')).getD .err).pushTempShaped (fun _ => v)
        s₁.freshLoan.1).setLent s₁.freshLoan.1 [⟨pos, steps, false⟩]).setHeldTy s₁.freshLoan.1 T.m).setHeldMem
        s₁.freshLoan.1 v) (v, { T with label := some s₁.freshLoan.1 }) := by
      intro l hl
      simp only [Option.some.injEq] at hl; subst hl
      simp only [SState.setHeldMem, SState.setHeldTy, if_true]
      exact ⟨trivial, hm⟩
    refine ⟨.inl hm, hlab, ?_⟩
    by_cases hp : p.steps.2 = [] ∨ p.steps.2 = [.deref]
    · obtain ⟨T', hres, rfl, hf, hT⟩ := contentOf_view h1
      have hsteps : steps = p.steps.2 := by
        unfold resolve at hres; cases hv : s.varPos p.steps.1 <;> simp_all
      have hst : steps = [] ∨ steps = [.deref] := hsteps ▸ hp
      obtain ⟨f, i, rfl⟩ : ∃ f i, pos = .bind f i := by
        have := resolve_bind hres
        cases pos with
        | bind f i => exact ⟨f, i, rfl⟩
        | temp => exact absurd this (by simp [IsTemp])
      have hs₁ := access_sgood hs (.bind f i) (dataHit steps)
      have hp₁ : Pos.bind f i ∈ (s.access (.bind f i) (dataHit steps)).positions := by
        rw [access_positions]; exact resolve_mem hres
      generalize s.access (Pos.bind f i) (dataHit steps) = s₁ at hf hT hs₁ hp₁ hlab ⊢
      obtain ⟨-, hT', -⟩ := read_root_goodRes hs₁ hp₁ hst hf hw
      have hTm : T.m = (s₁.tyAt (.bind f i)).m := by rw [hT, hT']; split <;> rfl
      have hlend : (fun φ' => (Sem.updAt K.dm K.Γ (s₁.freshLoan.2.tyAt (.bind f i)) (fun _ => φ' s₁.freshLoan.1)
          steps (s₁.freshLoan.2.valAt (.bind f i) φ')).getD .err) = fun φ' => φ' s₁.nextLoan := by
        funext φ'; rcases hst with rfl | rfl <;> rfl
      rw [hlend, hTm]
      have hv : v ∈ₛ[K.dm.read] (s₁.tyAt (.bind f i)).m := by rw [← hTm]; exact hm
      exact sgood_borrow_root hMR hs₁ hp₁ hv _
    · exact borrowPlace_field_sgood hs ⟨fun e => hp (.inl e), fun e => hp (.inr e)⟩ hb₀ hm

/-- **An assignment's write** (`assignAt`), the value checked at the place's type at the write and its
label at that type (the strict `.assign` clause's test). -/
theorem assignAt_sgood (hMR : MemReads K.dm K.Γ) {p : Place} {v : Sem} {R : TyS} {s s' : SState} {r : Res}
    (hs : SGood K.dm K.Γ φ s) (hv : v ∈ₛ[K.dm.read] (placeTy K φ p s).m) (hl : labTyOk s R.label (placeTy K φ p s).m)
    (hlab : LabOk K.dm s (v, R)) (h : assignAt K φ p v R.label s = some (r, s')) :
    GoodRes K.dm.read r ∧ LabOk K.dm s' r ∧ SGood K.dm K.Γ φ s' := by
  sorry

end Ochr.Meaning.Strict
