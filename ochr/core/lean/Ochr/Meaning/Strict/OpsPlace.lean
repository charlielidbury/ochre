import Ochr.Meaning.Strict.OpsCall
import Ochr.Meaning.RunCongr
import Ochr.Meaning.MonoHolders
import Ochr.Meaning.Strict.WriteMoved
import Ochr.Meaning.Strict.Struct

/-!
# The place operations keep the invariant: holder transfers, a `let`'s binding and drop, reads,
borrows, assignments

PROVED (standard axioms): `sgood_transfer` (a move of a holder parks its borrow), `sgood_pushBindShaped`
(a `let`'s binding; via `sgood_push_generic`), `sgood_dropLast`/`sgood_letDrop` (a `let`'s drop),
`readPlace_fund` (a read at a root or through `*`, copied or moved; the value good by the strict read
test `ReadGood`), `sgood_borrow_root` and `borrowPlace_res` at a root or through `*`, `sgood_hold` and
`assignAt_sgood` at a root or through `*`. The clauses' tails (D112's `invalidate`, then the strict
test below a root `lentOk`): `borrow_fund`, `assign_tail_fund`, through `invalidate_sgood`.

ADDED HYPOTHESES, each with its reason in the docstring: `LoU` of the label in flight
(`sgood_pushBindShaped`, `assignAt_sgood`: the binding or root becomes its holder; `runT_rinv` gives it of
every result); `readPlace_fund` at `[]`/`[*]` only (a field path is `readPlace_fund_all`'s).

A write at a FIELD path (the orchestrator's write rule, 2026-11-21): `setContent_field_moved_sgood` (a
move out of a field; the run's test: the write is defined at every typed future; the model lemma
`WriteMoved.omem_updAt_moved`, which the join's drop and D112's invalidation share), and
`borrowPlace_field_sgood`/`setContent_field_sgood` (a field lent or assigned: the state between the
write and the test keeps the invariant's structural part, `Struct.SStruct`, the invalidation keeps it,
and the test `lentOk` at a field path is `StateOk`, the rest).
-/

namespace Ochr.Meaning.Strict
open Ochr.Meaning

variable {K : RunCtx} {φ : Future}

/-! ## Helpers: pushing a temporary, typed futures across states with the same live labels -/

theorem env_ne_of_mem {s : SState} {p : Pos} (h : p ∈ s.positions) : s.env ≠ [] := by
  intro he
  rw [SState.mem_positions] at h
  cases p <;> simp [SState.lookup, he] at h

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

/-- A borrow's holder moves to a new temporary holding an open member of its content type (a
move of a holder, `readPlace`). -/
theorem sgood_transfer {s : SState} (hs : SGood K.dm K.Γ φ s) {l : Nat} (hl : l ∈ s.liveLabels) {v : Sem}
    (hv : PMem K.dm K.Γ v (s.heldTy l)) :
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
  refine ⟨fun ψ hψ f i hpi => ?_, fun ψ hψ p l' hl' => ?_, fun l' hl' => ?_, fun f i l' hl' => ?_, ?_, ?_⟩
  · rw [hTF] at hψ
    rw [bind_mem_pushTempShaped, SState.takeLabel_positions] at hpi
    rw [hbval, hbty]
    split
    · exact .inl (.moved _)
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

/-- On `⋆`, a read gives `⋆`, at the type it started from (no step) or at `err` (a field of `⋆`). -/
theorem follow_proof (dm : DataModel) (Γ : List IndDecl) : ∀ (T : TyS) (steps : List Step) (x : Sem) (U : TyS),
    Sem.follow dm Γ T .proof steps = some (x, U) → x = .proof ∧ (U = T ∨ U.m = TyM.err)
  | _, [], _, _, h => by
    simp only [Sem.follow, Option.some.injEq, Prod.mk.injEq] at h; exact ⟨h.1.symm, .inl h.2.symm⟩
  | T, st :: sts, x, U, h => by
    simp only [Sem.follow] at h
    cases st with
    | deref =>
      obtain ⟨hx, hU | hU⟩ := follow_proof dm Γ T sts x U (by simpa [Sem.step] using h)
      · exact ⟨hx, .inl hU⟩
      · exact ⟨hx, .inr hU⟩
    | proj i =>
      cases i with
      | zero =>
        have hs : Sem.step dm Γ T (.proj 0) .proof = some (.proof, .plain TyM.err) := by
          simp only [Sem.step, Sem.asNat, Sem.as]
          split
          · rename_i heq; cases heq
          · rfl
        rw [hs, Option.bind_some] at h
        obtain ⟨hx, hU | hU⟩ := follow_proof dm Γ _ sts x U h
        · exact ⟨hx, .inr (by rw [hU]; rfl)⟩
        · exact ⟨hx, .inr hU⟩
      | succ i =>
        simp only [Sem.step, Sem.stepField, Option.bind_some] at h
        obtain ⟨hx, hU | hU⟩ := follow_proof dm Γ _ sts x U h
        · exact ⟨hx, .inr (by rw [hU]; rfl)⟩
        · exact ⟨hx, .inr hU⟩
    | field g =>
      simp only [Sem.step, Sem.stepField, Option.bind_some] at h
      obtain ⟨hx, hU | hU⟩ := follow_proof dm Γ _ sts x U h
      · exact ⟨hx, .inr (by rw [hU]; rfl)⟩
      · exact ⟨hx, .inr hU⟩

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
theorem sgood_push_generic {s s₁ S : SState} (hs : SGood K.dm K.Γ φ s) {f₀ i₀ : Nat}
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
  have hPv : ∀ l, lab = some l → PMem K.dm K.Γ v (s.heldTy l) := by
    intro l hl
    obtain ⟨h1, h2⟩ := hlab l (hlabT ▸ hl)
    rw [h1]
    rcases hv with hv | hv | ⟨he, -⟩
    · exact .mem hv
    · simp only at hv; rw [hv]; exact .moved _
    · rw [h1, he] at h2; exact absurd h2 (DataModel.err_mem_false _ _)
  refine ⟨fun ψ hψ f i hpi => ?_, fun ψ hψ p l' hl' => ?_, fun l' hl' => ?_, fun f i l' hl' => ?_, hacyc, hfresh⟩
  · show GoodVal _ _ (S.valAt _ ψ) (S.tyAt _).m
    by_cases hq : Pos.bind f i = .bind f₀ i₀
    · rw [hq, hvalN, htyN]; exact hv.val K.dm.read_wholeFields K.Γ
    · have hpi' : Pos.bind f i ∈ s.positions := ((hpos _).1 hpi).resolve_right hq
      rw [hval _ hq, hty _ hq]
      rcases h1val (.bind f i) with e | e
      · rw [e, ← hT2 ψ]; exact hs.bind _ (hT1 ψ hψ) f i hpi'
      · rw [e]; exact .inl (.moved _)
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

/-- A `let`'s binding (`pushBindShaped`) of a good result whose label records its type.

ADDED HYPOTHESIS `hlou` (`RunPresInd`'s `LoU` for the label in flight: live, or read by no position, and
below the counter): the binding becomes the label's holder, so the label is live after; if it was not
live before, a position that read it would be read at a future the typed futures before did not
constrain there, and a label at or above the counter would break the label order (`RInv`'s `ShapeAt`).
`RunPresInd.runT_rinv` concludes exactly this of every result (`LoU s' r.2.label`), so the lemma's
induction carries it beside `LabOk`. -/
theorem sgood_pushBindShaped {s : SState} (hs : SGood K.dm K.Γ φ s) (b : SBinding)
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
    refine sgood_push_generic (s₁ := s) hs hN hpos (fun q hq => by rw [hval, if_neg hq])
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
    refine sgood_push_generic (s₁ := s.takeLabel l) hs (by rwa [h1pos] at hN)
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
      · exact .mem (hs.held y hy)
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
  refine ⟨fun ψ hψ f i hpi => ?_, fun ψ hψ p l' hl' => ?_, fun l' hl' => ?_, fun f i l' hl' => ?_, ?_, ?_⟩
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
    exact .mem (hs.held l hl)

/-- A whole good value at the error type is a type value. -/
theorem GoodVal.ty_of_err {v : Sem} {T : TyM} (h : GoodVal K.dm K.Γ v T) (hw : v.whole) (he : T = TyM.err) :
    NoData v := by
  rcases h with h | ⟨-, h⟩
  · subst he
    cases h with
    | moved => exact absurd hw (by simp [Sem.whole])
    | mem h => exact absurd h (DataModel.err_mem_false _ _)
    | succ n h => exact absurd h (DataModel.err_mem_false _ _)
    | dat hdc => cases hdc
  · exact h

/-- **A read at a root or through `*`**: the value is the binding's own content, at its stored type. -/
theorem read_root_eq {s₁ : SState} {f i : Nat} {steps : List Step} (hst : steps = [] ∨ steps = [.deref])
    {v : Sem} {T' : TyS}
    (hf : Sem.follow K.dm K.Γ (s₁.tyAt (.bind f i)) (s₁.valAt (.bind f i) (s₁.typedFuture φ)) steps = some (v, T')) :
    v = s₁.valAt (.bind f i) (s₁.typedFuture φ) ∧ T' = s₁.tyAt (.bind f i) := by
  rcases hst with rfl | rfl
  · simp only [Sem.follow, Option.some.injEq, Prod.mk.injEq] at hf; exact ⟨hf.1.symm, hf.2.symm⟩
  · simp only [Sem.follow, Sem.step, Option.bind_some, Option.some.injEq, Prod.mk.injEq] at hf
    exact ⟨hf.1.symm, hf.2.symm⟩

/-- What the strict read test passes is a good result. -/
theorem goodRes_of_readGood {R : DataRead} {v : Sem} {T : TyS} (h : ReadGood R T.m v) : GoodRes R (v, T) := by
  rcases h with h | ⟨he, h⟩
  · exact .inl h
  · exact .inr (.inr ⟨he, h⟩)

/-- `if ¬ p then none else a`, succeeding. -/
theorem ite_not_none_some {α : Type _} {p : Prop} [Decidable p] {a : Option α} {b : α}
    (h : (if ¬ p then none else a) = some b) : p ∧ a = some b := by
  by_cases hp : p
  · rw [if_neg (fun hn => hn hp)] at h; exact ⟨hp, h⟩
  · rw [if_pos hp] at h; cases h

/-- **A read of a place at a root or through `*`**, copied or moved: the value read is the binding's
whole content, good at its stored type by the strict read test (`ReadGood`); a move writes `⊥` there
and, at a holder, parks the borrow. (A move at a FIELD path writes `⊥` into a field:
`setContent_field_moved_sgood`, in `readPlace_fund_all`.) -/
theorem readPlace_fund (p : Place) (hp : p.steps.2 = [] ∨ p.steps.2 = [.deref])
    (copy : Bool) : FundAt K.dm K.Γ φ (readPlace K φ p copy) := by
  intro s s' r hs h
  have hlou := (readPlace_rinv K φ (fun _ => True) h hs.acyc).2
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
  obtain ⟨hw, h⟩ := open Classical in ite_not_none_some h
  obtain ⟨hrg, h⟩ := open Classical in ite_not_none_some h
  have hst : steps = [] ∨ steps = [.deref] := hsteps ▸ hp
  obtain ⟨hv, hT'⟩ := read_root_eq hst hf
  have hTm : T.m = (s₁.tyAt (.bind f i)).m := by rw [hT, hT']; split <;> rfl
  have hgoodT : ∀ X : TyS, X.m = T.m → GoodRes K.dm.read (v, X) := by
    intro X hX; exact goodRes_of_readGood (T := X) (by rw [hX]; exact hrg)
  cases copy with
  | true =>
    rw [if_pos rfl] at h
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨hgoodT _ rfl, (fun l hl => by cases hl), hlou, hs₁⟩
  | false =>
    rw [if_neg (by simp)] at h
    have hsc : setContent K φ (.bind f i) steps .moved s₁ = some (⟨⟩, s₁.setAt (.bind f i) fun _ => .moved) :=
      setContent_root K φ _ _ _ hst
    rw [hsc] at h
    simp only [Option.bind_some, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    have hs₂ : SGood K.dm K.Γ φ (s₁.setAt (.bind f i) fun _ => .moved) :=
      sgood_setAt_pmem hs₁ hp₁ (fun _ _ _ => .moved _) (fun _ _ => .moved _)
    by_cases hsh : steps.isEmpty = true ∧ ∃ l, s₁.shape (.bind f i) = some l
    · obtain ⟨he, l, hl⟩ := hsh
      simp only [he, if_true, hl] at hlou ⊢
      have hlive : l ∈ (s₁.setAt (.bind f i) fun _ => .moved).liveLabels := by
        rw [liveLabels_setAt]; exact live_of_shape hp₁ hl
      have hPv : PMem K.dm K.Γ v ((s₁.setAt (.bind f i) fun _ => .moved).heldTy l) := by
        rw [heldTy_setAt, hv]; exact hs₁.holder _ (typedF_typedFuture hs₁) _ l hl
      have hHT : ((((s₁.setAt (.bind f i) fun _ => .moved).takeLabel l).pushTempShaped (fun _ => v) l)).heldTy
          = s₁.heldTy := by
        rw [heldTy_pushTempShaped, (takeLabel_facts _ l).2.2.2.1, heldTy_setAt]
      have hHM : ((((s₁.setAt (.bind f i) fun _ => .moved).takeLabel l).pushTempShaped (fun _ => v) l)).heldMem
          = s₁.heldMem := by
        rw [heldMem_pushTempShaped, (takeLabel_facts _ l).2.2.2.2.1, heldMem_setAt]
      refine ⟨hgoodT _ rfl, fun l' hl' => ?_, hlou, sgood_transfer hs₂ hlive hPv⟩
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
      simp only [hlab] at hlou ⊢
      exact ⟨hgoodT _ rfl, (fun l hl => by cases hl), hlou, hs₂⟩

/-- `⊥` written into a value with no data: the path enters nothing, so where defined it wrote the
whole value. -/
theorem updAt_moved_noData {U : TyS} : ∀ (steps : List Step) {x y : Sem}, NoData x →
    Sem.updAt K.dm K.Γ U (fun _ => .moved) steps x = some y → y = .moved
  | [], x, y, _, h => by rw [Sem.updAt.eq_def] at h; simp only [Option.some.injEq] at h; exact h.symm
  | .deref :: sts, x, y, hx, h => by
    rw [Sem.updAt.eq_def] at h; exact updAt_moved_noData sts hx h
  | .proj _ :: sts, x, y, hx, h => by
    rcases hx with ⟨T, rfl⟩ | rfl <;> (rw [Sem.updAt.eq_def] at h; simp [Sem.asNat, Sem.as] at h)
  | .field _ :: sts, x, y, hx, h => by
    rcases hx with ⟨T, rfl⟩ | rfl <;> (rw [Sem.updAt.eq_def] at h; simp [Sem.asNat, Sem.as] at h)

/-- **Moving out a part at a FIELD path keeps the invariant** (the orchestrator's write rule,
2026-11-21): the run writes only where the path update is DEFINED at every typed future
(`setContent`'s test, `setContent_defined`), and there `⊥` at a path of an open member leaves an open
member (`WriteMoved.omem_updAt_moved`); a value with no data is written whole (`updAt_moved_noData`).
Where the test fails the run fails: a position reading a live label along the path
(`Strict/FieldWriteCE`), excluded on states related to the checker's by the simulation (`OPEN.md`). -/
theorem setContent_field_moved_sgood {s s' : SState} (hs : SGood K.dm K.Γ φ s) {f i : Nat} {steps : List Step}
    (hp : Pos.bind f i ∈ s.positions) (h : setContent K φ (.bind f i) steps .moved s = some (⟨⟩, s')) :
    SGood K.dm K.Γ φ s' := by
  have hdef := setContent_defined K φ h
  rw [setContent_eq K φ h]
  have key : ∀ ψ, TypedF K.dm K.Γ φ s ψ → ∃ y, Sem.updAt K.dm K.Γ (s.tyAt (.bind f i)) (fun _ => .moved) steps
      (s.valAt (.bind f i) ψ) = some y := fun ψ hψ => Option.isSome_iff_exists.mp (hdef ψ hψ)
  refine sgood_setAt_comp (fun x => (Sem.updAt K.dm K.Γ (s.tyAt (.bind f i)) (fun _ => .moved) steps x).getD .err)
    hs hp (fun ψ hψ f' i' e => ?_) (fun ψ hψ l hl => ?_)
  · obtain ⟨y, hy⟩ := key ψ hψ
    simp only [hy, Option.getD_some]
    cases e
    rcases hs.bind ψ hψ f i hp with hm | ⟨he, hnd⟩
    · exact .inl (omem_updAt_moved steps hm hy)
    · rw [updAt_moved_noData steps hnd hy]; exact .inl (.moved _)
  · obtain ⟨y, hy⟩ := key ψ hψ
    simp only [hy, Option.getD_some]
    exact omem_updAt_moved steps (hs.holder ψ hψ _ l hl) hy

/-- **A read of a place at any path**: the value read is good at the type the read gives it by the
strict read test (`ReadGood`: a member, or `⋆`/a type value at `err`); the state is good (a move at a
FIELD path through `setContent_field_moved_sgood`). -/
theorem readPlace_fund_all (p : Place) (copy : Bool) :
    FundAt K.dm K.Γ φ (readPlace K φ p copy) := by
  intro s s' r hs h
  by_cases hp : p.steps.2 = [] ∨ p.steps.2 = [.deref]
  · exact readPlace_fund p hp copy s s' r hs h
  · have hlou := (readPlace_rinv K φ (fun _ => True) h hs.acyc).2
    unfold readPlace at h
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
    have hp₁ : Pos.bind f i ∈ (s.access (.bind f i) (dataHit steps)).positions := by
      rw [access_positions]; exact resolve_mem hres
    dsimp only at h
    generalize s.access (Pos.bind f i) (dataHit steps) = s₁ at h hf hT hs₁ hp₁
    have hne : steps.isEmpty = false := by cases steps with | nil => exact absurd rfl hst.1 | cons _ _ => rfl
    obtain ⟨-, h⟩ := open Classical in ite_not_none_some h
    obtain ⟨hrg, h⟩ := open Classical in ite_not_none_some h
    have hg' : ∀ lab, GoodRes K.dm.read (v, { T with label := lab }) := fun _ => goodRes_of_readGood hrg
    split at h
    · simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h
      exact ⟨hg' _, (fun l hl => by cases hl), hlou, hs₁⟩
    · simp only [Option.bind_eq_some_iff] at h
      obtain ⟨⟨⟨⟩, s₂⟩, h2, h⟩ := h
      simp only [hne, Bool.false_eq_true, if_false, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨hg' _, (fun l hl => by cases hl), hlou, setContent_field_moved_sgood hs₁ hp₁ h2⟩

/-! ## Borrows -/

/-- **A fresh borrow of a binding, whole** (`&x`, `&*r`): the binding becomes the lender of the fresh
label `l` (reading `l`'s final content), a new temporary holds the content `v` (a member of the
binding's type), and `l` records that type and `v`. -/
theorem sgood_borrow_root {s₁ : SState} (hs₁ : SGood K.dm K.Γ φ s₁) {f i : Nat}
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
  have hψl : ∀ ψ, TypedF K.dm K.Γ φ S ψ → PMem K.dm K.Γ (ψ l) Tm := by
    rintro ψ ⟨-, hψ⟩; have := hψ l ((hSlive l).2 (.inr rfl)); rwa [hSHT, if_pos rfl] at this
  have hbval : ∀ f' i', S.valAt (.bind f' i') =
      if Pos.bind f' i' = .bind f i then (fun φ' => φ' l) else s₁.valAt (.bind f' i') := by
    intro f' i'; rw [hSval, valAt_pushTempShaped_bind, h3val]
  refine ⟨fun ψ hψ f' i' hpi => ?_, fun ψ hψ q l' hl' => ?_, fun y hy => ?_, fun f' i' l' hl' => ?_, hacyc, hfresh⟩
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
      exact .mem hv
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

/-- **A borrow at any path leaves the structural part of the invariant** (`Struct.SStruct`): the fresh
label is parked in a new temporary, records the content's type and the content (a member: `hm`, the
strict test), and is not any old holder's; the lender's new meaning `G` is not read here. -/
theorem sstruct_borrow_park {s₁ : SState} (hs₁ : SGood K.dm K.Γ φ s₁) {pos : Pos} (hp : pos ∈ s₁.positions)
    (G : SVal) {v : Sem} {Tm : TyM} (hv : v ∈ₛ[K.dm.read] Tm) (xs : List Site)
    (hacyc : SState.RInv (fun _ => True) (((((s₁.freshLoan.2.setAt pos G).pushTempShaped
      (fun _ => v) s₁.nextLoan).setLent s₁.nextLoan xs).setHeldTy s₁.nextLoan Tm).setHeldMem s₁.nextLoan v))
    (hfresh : (((((s₁.freshLoan.2.setAt pos G).pushTempShaped
      (fun _ => v) s₁.nextLoan).setLent s₁.nextLoan xs).setHeldTy s₁.nextLoan Tm).setHeldMem s₁.nextLoan v).ReadsBelow) :
    SStruct K.dm (((((s₁.freshLoan.2.setAt pos G).pushTempShaped
      (fun _ => v) s₁.nextLoan).setLent s₁.nextLoan xs).setHeldTy s₁.nextLoan Tm).setHeldMem s₁.nextLoan v) := by
  have hsa₁ := hs₁.acyc.2.2
  have hlnew : s₁.nextLoan ∉ s₁.liveLabels := fun h => Nat.lt_irrefl _ (hs₁.live_lt h)
  have hF : s₁.freshLoan.2 = { s₁ with nextLoan := s₁.nextLoan + 1 } := rfl
  rw [hF] at hacyc hfresh ⊢
  generalize hl : s₁.nextLoan = l at *
  generalize hS₂ : ({ s₁ with nextLoan := l + 1 } : SState) = S₂ at hacyc hfresh ⊢
  have h2pos : S₂.positions = s₁.positions := by rw [← hS₂]; rfl
  have h2ty : S₂.tyAt = s₁.tyAt := by rw [← hS₂]; rfl
  have h2sh : S₂.shape = s₁.shape := by rw [← hS₂]
  have h2HT : S₂.heldTy = s₁.heldTy := by rw [← hS₂]
  have h2HM : S₂.heldMem = s₁.heldMem := by rw [← hS₂]
  have h2nl : S₂.nextLoan = l + 1 := by rw [← hS₂]
  generalize hS₃ : S₂.setAt pos G = S₃ at hacyc hfresh ⊢
  have h3ty : ∀ q, S₃.tyAt q = s₁.tyAt q := by intro q; rw [← hS₃, tyAt_setAt, h2ty]
  have h3sh : S₃.shape = s₁.shape := by rw [← hS₃, SState.shape_setAt, h2sh]
  have h3pos : S₃.positions = s₁.positions := by rw [← hS₃, SState.positions_setAt, h2pos]
  have h3HT : S₃.heldTy = s₁.heldTy := by rw [← hS₃, heldTy_setAt, h2HT]
  have h3HM : S₃.heldMem = s₁.heldMem := by rw [← hS₃, heldMem_setAt, h2HM]
  have h3env : S₃.env ≠ [] := env_ne_of_mem (p := pos) (by rw [h3pos]; exact hp)
  have hsa₃ : SState.ShapeAt S₃ := by
    intro q x hq
    rw [h3sh] at hq
    obtain ⟨h1, h2⟩ := hsa₁ q x hq
    refine ⟨by rw [h3pos]; exact h1, ?_⟩
    rw [← hS₃, nextLoan_setAt, h2nl]; omega
  have h3live : ∀ y, y ∈ S₃.liveLabels ↔ y ∈ s₁.liveLabels := by
    intro y; unfold SState.liveLabels; rw [h3pos, h3sh]
  generalize hS : ((((S₃.pushTempShaped (fun _ => v) l).setLent l xs).setHeldTy l Tm).setHeldMem l v) = S at hacyc hfresh ⊢
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
  have hSlive : ∀ y, y ∈ S.liveLabels → y ∈ s₁.liveLabels ∨ y = l := by
    intro y hy
    have e : y ∈ S.liveLabels ↔ y ∈ (S₃.pushTempShaped (fun _ => v) l).liveLabels := by
      rw [← hS]; rfl
    rcases SState.live_pushTempShaped_new hsa₃ (e.1 hy) with h | h
    · exact .inl ((h3live y).1 h)
    · exact .inr h
  refine ⟨fun y hy => ?_, fun f' i' l' hl' => ?_, hacyc, hfresh⟩
  · rw [hSHM, hSHT]
    rcases hSlive y hy with h | rfl
    · have hyl : y ≠ l := fun e => hlnew (e ▸ h)
      rw [if_neg hyl, if_neg hyl]; exact hs₁.held y h
    · rw [if_pos rfl, if_pos rfl]; exact hv
  · rw [hSsh] at hl'
    rcases pushTempShaped_holder hsa₃ h3env _ l hl' with ⟨hq3, hsh3, -⟩ | ⟨-, hnb, -⟩
    · rw [h3sh] at hsh3
      have hl'l : l' ≠ l := fun e => hlnew (e ▸ live_of_shape (h3pos ▸ hq3) hsh3)
      rw [hSty, hSHT, if_neg hl'l]; exact hs₁.holderTy f' i' l' hsh3
    · exact absurd rfl (hnb f' i')

/-- **A borrow of a FIELD, then D112's invalidation, keeps the invariant where the strict test passes**
(the orchestrator's write rule, 2026-11-21). `&p.f` makes the lender's FIELD read the fresh label's
final content; the state between the borrow and the test need not be good (a later dependent field of
the lender), but it keeps the invariant's structural part (`sstruct_borrow_park`), the invalidation
keeps that (`SStruct.invalidate`), and the run's test `lentOk` at a field path is `StateOk`, the value
clauses at every typed future (`sgood_of_stateOk`). -/
theorem borrowPlace_field_sgood {p : Place} {s s₁ : SState} {r : Res} (hs : SGood K.dm K.Γ φ s)
    (hfield : p.steps.2 ≠ [] ∧ p.steps.2 ≠ [.deref]) (h : borrowPlace K φ p s = some (r, s₁))
    (hm : r.1 ∈ₛ[K.dm.read] r.2.m) (hok : lentOk K φ p (invalidate K φ p s₁)) :
    SGood K.dm K.Γ φ (invalidate K φ p s₁) := by
  have hrinv := (borrowPlace_rinv K φ (fun _ => True) h hs.acyc).1
  have hfr : s₁.ReadsBelow := by obtain ⟨v₀, T₀⟩ := r; exact borrowPlace_readsBelow K φ p s hs.fresh h
  have hE : EnvLe s s₁ := borrowPlace_envLe K φ h
  have hb := h
  unfold borrowPlace at hb
  simp only [Bind.bind, Option.bind_eq_some_iff] at hb
  obtain ⟨⟨⟨v, T, pos, steps⟩, s₂⟩, h1, hb⟩ := hb
  obtain ⟨T', hres, rfl, -, -⟩ := contentOf_view h1
  have hsteps : steps = p.steps.2 := by
    unfold resolve at hres; cases hv : s.varPos p.steps.1 <;> simp_all
  dsimp only at hb
  by_cases hw : v.whole
  rotate_left
  · rw [if_pos hw] at hb; cases hb
  rw [if_neg (fun hn => hn hw)] at hb
  simp only [Option.some.injEq, Prod.mk.injEq] at hb
  obtain ⟨rfl, rfl⟩ := hb
  have hS₁ : SStruct K.dm _ := sstruct_borrow_park (access_sgood hs pos (dataHit steps))
    (by rw [access_positions]; exact resolve_mem hres) _ hm _ hrinv hfr
  have hS := hS₁.invalidate (φ := φ) p
  have hr : resolve (invalidate K φ p _) p = some (pos, steps) :=
    (resolve_envLe (hE.trans (invalidate_props K φ (fun _ => True) p hrinv).2.1) p).trans hres
  unfold lentOk at hok; rw [hr] at hok
  rcases hok with h0 | h0 | hok
  · exact absurd (hsteps ▸ h0) hfield.1
  · exact absurd (hsteps ▸ h0) hfield.2
  · exact sgood_of_stateOk hS hok

/-- **A borrow's strict content test**: the result is a member whose fresh label records its type and
the content; at a root or through `*` the state is good (`sgood_borrow_root`). -/
theorem borrowPlace_res (p : Place) {s s' : SState} {r : Res} (hs : SGood K.dm K.Γ φ s)
    (h : SM.strictS K.dm.read (borrowPlace K φ p) s = some (r, s')) :
    r.1 ∈ₛ[K.dm.read] r.2.m ∧ LabOk K.dm s' r ∧ LoU s' r.2.label ∧ borrowPlace K φ p s = some (r, s') ∧
      ((p.steps.2 = [] ∨ p.steps.2 = [.deref]) → SGood K.dm K.Γ φ s') := by
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
    refine ⟨hm, hlab, hrinv.2, rfl, fun hp => ?_⟩
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
      obtain ⟨-, hT'⟩ := read_root_eq hst hf
      have hTm : T.m = (s₁.tyAt (.bind f i)).m := by rw [hT, hT']; split <;> rfl
      have hlend : (fun φ' => (Sem.updAt K.dm K.Γ (s₁.freshLoan.2.tyAt (.bind f i)) (fun _ => φ' s₁.freshLoan.1)
          steps (s₁.freshLoan.2.valAt (.bind f i) φ')).getD .err) = fun φ' => φ' s₁.nextLoan := by
        funext φ'; rcases hst with rfl | rfl <;> rfl
      rw [hlend, hTm]
      have hv : v ∈ₛ[K.dm.read] (s₁.tyAt (.bind f i)).m := by rw [← hTm]; exact hm
      exact sgood_borrow_root hs₁ hp₁ hv _


theorem heldTy_endLabel (s : SState) (l : Nat) : (s.endLabel l).heldTy = s.heldTy := by
  unfold SState.endLabel; split <;> rfl

theorem heldMem_endLabel (s : SState) (l : Nat) : (s.endLabel l).heldMem = s.heldMem := by
  unfold SState.endLabel; split <;> rfl

theorem heldTy_foldl_endLabel : ∀ (ls : List Nat) (s : SState), (ls.foldl SState.endLabel s).heldTy = s.heldTy
  | [], _ => rfl
  | l :: ls, s => by rw [List.foldl_cons, heldTy_foldl_endLabel ls, heldTy_endLabel]

theorem heldMem_foldl_endLabel : ∀ (ls : List Nat) (s : SState), (ls.foldl SState.endLabel s).heldMem = s.heldMem
  | [], _ => rfl
  | l :: ls, s => by rw [List.foldl_cons, heldMem_foldl_endLabel ls, heldMem_endLabel]

theorem heldTy_access (s : SState) (p : Pos) (hit : List Step → Bool) : (s.access p hit).heldTy = s.heldTy := by
  unfold SState.access
  generalize List.range s.liveLabels.length = ns
  induction ns generalizing s with
  | nil => rfl
  | cons n ns ih => rw [List.foldl_cons, ih, heldTy_foldl_endLabel]

theorem heldMem_access (s : SState) (p : Pos) (hit : List Step → Bool) : (s.access p hit).heldMem = s.heldMem := by
  unfold SState.access
  generalize List.range s.liveLabels.length = ns
  induction ns generalizing s with
  | nil => rfl
  | cons n ns ih => rw [List.foldl_cons, ih, heldMem_foldl_endLabel]

/-! ## D112's invalidation keeps the invariant -/

theorem setContent_held {pos : Pos} {steps : List Step} {v : Sem} {s s' : SState}
    (h : setContent K φ pos steps v s = some (⟨⟩, s')) : s'.heldTy = s.heldTy ∧ s'.heldMem = s.heldMem := by
  unfold setContent at h
  simp only at h
  split at h
  · simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨_, rfl⟩ := h
    exact ⟨heldTy_setAt _ _ _, heldMem_setAt _ _ _⟩
  · cases h

theorem invalidateOne_held (s : SState) (q : Place) :
    (invalidateOne K φ s q).heldTy = s.heldTy ∧ (invalidateOne K φ s q).heldMem = s.heldMem := by
  unfold invalidateOne
  split
  · rename_i pos steps _
    dsimp only
    split
    · rename_i hsc
      obtain ⟨h1, h2⟩ := setContent_held hsc
      exact ⟨by rw [h1, heldTy_access], by rw [h2, heldMem_access]⟩
    · exact ⟨heldTy_access _ _ _, heldMem_access _ _ _⟩
  · exact ⟨rfl, rfl⟩

theorem invalidate_held (p : Place) (s : SState) :
    (invalidate K φ p s).heldTy = s.heldTy ∧ (invalidate K φ p s).heldMem = s.heldMem := by
  unfold invalidate
  generalize K.D.invalidated (scopeOf s) p = qs
  induction qs generalizing s with
  | nil => exact ⟨rfl, rfl⟩
  | cons q qs ih =>
    simp only [List.foldl_cons]
    obtain ⟨h1, h2⟩ := ih (invalidateOne K φ s q)
    obtain ⟨h3, h4⟩ := invalidateOne_held (K := K) (φ := φ) s q
    exact ⟨h1.trans h3, h2.trans h4⟩

theorem labOk_invalidate {p : Place} {s : SState} {r : Res} (h : LabOk K.dm s r) :
    LabOk K.dm (invalidate K φ p s) r := by
  intro l hl
  obtain ⟨h1, h2⟩ := invalidate_held (K := K) (φ := φ) p s
  rw [h1, h2]; exact h l hl

/-- **D112's invalidation of one place keeps the invariant**: [Access], then `⊥` at the place (at a
root or through `*` a whole write of `⊥`; at a field path `setContent_field_moved_sgood`). -/
theorem invalidateOne_sgood {s : SState} (hs : SGood K.dm K.Γ φ s) (q : Place) :
    SGood K.dm K.Γ φ (invalidateOne K φ s q) := by
  unfold invalidateOne
  cases hres : resolve s q with
  | none => exact hs
  | some ps =>
    obtain ⟨pos, steps⟩ := ps
    dsimp only
    have hs₁ := access_sgood hs pos (dataHit steps)
    obtain ⟨f, i, rfl⟩ : ∃ f i, pos = .bind f i := by
      have := resolve_bind hres
      cases pos with
      | bind f i => exact ⟨f, i, rfl⟩
      | temp => exact absurd this (by simp [IsTemp])
    have hp₁ : Pos.bind f i ∈ (s.access (.bind f i) (dataHit steps)).positions := by
      rw [access_positions]; exact resolve_mem hres
    generalize s.access (Pos.bind f i) (dataHit steps) = s₁ at hs₁ hp₁ ⊢
    cases hsc : setContent K φ (.bind f i) steps .moved s₁ with
    | none => exact hs₁
    | some x =>
      obtain ⟨⟨⟩, s₂⟩ := x
      dsimp only
      by_cases hst : steps = [] ∨ steps = [.deref]
      · have e : setContent K φ (.bind f i) steps .moved s₁ = some (⟨⟩, s₁.setAt (.bind f i) fun _ => .moved) :=
          setContent_root K φ _ _ _ hst
        rw [e] at hsc
        simp only [Option.some.injEq, Prod.mk.injEq] at hsc
        rw [← hsc.2]
        exact sgood_setAt_pmem hs₁ hp₁ (fun _ _ _ => .moved _) (fun _ _ => .moved _)
      · exact setContent_field_moved_sgood hs₁ hp₁ hsc

theorem invalidate_sgood (p : Place) {s : SState} (hs : SGood K.dm K.Γ φ s) :
    SGood K.dm K.Γ φ (invalidate K φ p s) := by
  unfold invalidate
  generalize K.D.invalidated (scopeOf s) p = qs
  induction qs generalizing s with
  | nil => exact hs
  | cons q qs ih => simp only [List.foldl_cons]; exact ih (invalidateOne_sgood hs q)

theorem lou_invalidate' (p : Place) {s : SState} (hi : SState.RInv (fun _ => True) s) {lab : Option Nat}
    (h : LoU s lab) : LoU (invalidate K φ p s) lab :=
  fun l hl => lou_invalidate K φ (fun _ => True) p hi (h l hl)

open Classical in
/-- **A borrow `&p`, the whole clause** (the strict content test, D112's invalidation, the strict test
below a root `lentOk`). -/
theorem borrow_fund (p : Place) :
    FundAt K.dm K.Γ φ (fun s => match SM.strictS K.dm.read (borrowPlace K φ p) s with
      | some (r, s₁) =>
        let s₂ := invalidate K φ p s₁
        if lentOk K φ p s₂ then some (r, s₂) else none
      | none => none) := by
  intro s s' r hs h
  simp only at h
  split at h
  · rename_i r₀ s₁ hb
    obtain ⟨hok, h⟩ := open Classical in ite_none_some h
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    obtain ⟨hm, hlab, hlou, hb', hroot⟩ := borrowPlace_res p hs hb
    have hi₁ := (borrowPlace_rinv K φ (fun _ => True) hb' hs.acyc).1
    refine ⟨.inl hm, labOk_invalidate hlab, lou_invalidate' p hi₁ hlou, ?_⟩
    by_cases hp : p.steps.2 = [] ∨ p.steps.2 = [.deref]
    · exact invalidate_sgood p (hroot hp)
    · exact borrowPlace_field_sgood hs ⟨fun e => hp (.inl e), fun e => hp (.inr e)⟩ hb' hm hok
  · cases h

/-! ## Assignments -/

/-- A meaning read at two futures that differ only at labels it does not read. -/
theorem eq_of_two_indep {f : SVal} {ψ ψ' : Future} {a b : Nat} (ha : ψ' a ≠ ψ a → Indep a f)
    (hb : ψ' b ≠ ψ b → Indep b f) (h : ∀ y, y ≠ a → y ≠ b → ψ' y = ψ y) : f ψ' = f ψ := by
  let ψ₁ : Future := fun y => if y = b then ψ y else ψ' y
  have e1 : f ψ' = f ψ₁ := by
    by_cases hbb : ψ' b = ψ b
    · congr 1; funext y; show ψ' y = if y = b then ψ y else ψ' y; split <;> simp_all
    · have : ψ' = ψ₁.upd b (ψ' b) := by
        funext y; simp only [Future.upd, ψ₁]; split <;> simp_all
      rw [this]; exact hb hbb ψ₁ (ψ' b)
  have e2 : f ψ₁ = f ψ := by
    by_cases haa : ψ₁ a = ψ a
    · congr 1; funext y
      show (if y = b then ψ y else ψ' y) = ψ y
      split
      · rfl
      · rename_i hyb
        by_cases hya : y = a
        · subst hya; simpa [ψ₁, hyb] using haa
        · exact h y hya hyb
    · have hab : a ≠ b := fun e => haa (by simp [ψ₁, e])
      have hψa : ψ' a ≠ ψ a := by simpa [ψ₁, hab] using haa
      have : ψ₁ = ψ.upd a (ψ₁ a) := by
        funext y
        simp only [Future.upd]
        split
        · rename_i hy; subst hy; rfl
        · rename_i hy
          show (if y = b then ψ y else ψ' y) = ψ y
          split
          · rfl
          · rename_i hyb; exact h y hy hyb
      rw [this]; exact ha hψa ψ (ψ₁ a)
  rw [e1, e2]

/-- **A root written with a borrow becomes its holder** (`assignAt`'s hold, `hold_rinv`): the label is
taken from its old holder (`⊥`) and the root, holding the member written, records it; the label the root
held before, if still recorded, is read by no one, and the label is live or read by no one. -/
theorem sgood_hold {s : SState} (hs : SGood K.dm K.Γ φ s) {f i : Nat} (hpos : Pos.bind f i ∈ s.positions)
    {v : Sem} (hval : s.valAt (.bind f i) = fun _ => v) (hv : v ∈ₛ[K.dm.read] (s.tyAt (.bind f i)).m) {l : Nat}
    (hTl : s.heldTy l = (s.tyAt (.bind f i)).m) (hMl : s.heldMem l ∈ₛ[K.dm.read] s.heldTy l) (hlou : LoU1 s l)
    (hold : ∀ x, s.shape (.bind f i) = some x → ∀ q, Indep x (s.valAt q)) :
    SGood K.dm K.Γ φ { s.takeLabel l with
      shape := fun q => if q = .bind f i then some l else (s.takeLabel l).shape q } := by
  obtain ⟨t1val, t1sh, t1ty, t1HT, t1HM, t1pos⟩ := takeLabel_facts s l
  have hsa := hs.acyc.2.2
  generalize hS : ({ s.takeLabel l with
      shape := fun q => if q = .bind f i then some l else (s.takeLabel l).shape q } : SState) = S
  have hSval : S.valAt = (s.takeLabel l).valAt := by rw [← hS]; rfl
  have hSty : ∀ q, S.tyAt q = s.tyAt q := by intro q; rw [← hS]; exact t1ty q
  have hSHT : S.heldTy = s.heldTy := by rw [← hS]; exact t1HT
  have hSHM : S.heldMem = s.heldMem := by rw [← hS]; exact t1HM
  have hSpos : S.positions = s.positions := by rw [← hS]; exact t1pos
  have hSsh : ∀ q, S.shape q = if q = .bind f i then some l else (s.takeLabel l).shape q := by intro q; rw [← hS]
  have hacyc : SState.RInv (fun _ => True) S := by
    rw [← hS]; exact hold_rinv (fun _ => True) hs.acyc _ hpos (fun ψ ψ' => by rw [hval]) hlou hold
  have hfresh : S.ReadsBelow := by
    rw [← hS]; intro q k h; exact SState.readsBelow_takeLabel hs.fresh l q k h
  -- the live labels: `l`, and those of `s` held elsewhere than at the root
  have hlive1 : ∀ y, y ∈ S.liveLabels → y ∈ s.liveLabels ∨ y = l := by
    intro y hy
    obtain ⟨q, hq, h⟩ := (SState.live_iff _ y).1 hy
    rw [hSsh] at h
    split at h
    · cases h; exact .inr rfl
    · exact .inl (live_of_shape (by rw [← hSpos]; exact hq) (t1sh q y h).1)
  have hlL : l ∈ S.liveLabels := (SState.live_iff _ l).2 ⟨.bind f i, by rw [hSpos]; exact hpos, by rw [hSsh]; simp⟩
  have hlive2 : ∀ y, y ∈ s.liveLabels → y ∉ S.liveLabels → s.shape (.bind f i) = some y := by
    intro y hy hny
    obtain ⟨q, hq, h⟩ := (SState.live_iff s y).1 hy
    have hyl : y ≠ l := fun e => hny (e ▸ hlL)
    by_cases hqp : q = .bind f i
    · subst hqp; exact h
    · exfalso; apply hny
      refine (SState.live_iff _ y).2 ⟨q, by rw [hSpos]; exact hq, ?_⟩
      rw [hSsh, if_neg hqp]
      cases hr : s.holderOf l with
      | none => have ht : s.takeLabel l = s := by unfold SState.takeLabel; rw [hr]
                rw [ht]; exact h
      | some r =>
        rw [(takeLabel_view hr).2.1, if_neg]; exact h
        intro e; subst e; rw [(SState.holderOf_spec hr).2] at h; exact hyl (Option.some.inj h).symm
  let a : Nat := match s.shape (.bind f i) with | some x => x | none => l
  let ψ' : Future → Future := fun ψ y =>
    if y ∈ s.liveLabels ∧ y ∉ S.liveLabels then s.heldMem y
    else if y ∉ s.liveLabels ∧ y ∈ S.liveLabels then φ y else ψ y
  have hT1 : ∀ ψ, TypedF K.dm K.Γ φ S ψ → TypedF K.dm K.Γ φ s (ψ' ψ) := by
    rintro ψ ⟨hag, hψ⟩
    refine ⟨fun y hy => ?_, fun y hy => ?_⟩
    · show (if y ∈ s.liveLabels ∧ y ∉ S.liveLabels then _ else if y ∉ s.liveLabels ∧ y ∈ S.liveLabels then φ y else ψ y) = φ y
      rw [if_neg (fun h => hy h.1)]
      split
      · rfl
      · rename_i hc; exact hag y (fun h => hc ⟨hy, h⟩)
    · show PMem _ _ (if y ∈ s.liveLabels ∧ y ∉ S.liveLabels then _ else if y ∉ s.liveLabels ∧ y ∈ S.liveLabels then φ y else ψ y) _
      split
      · exact .mem (hs.held y hy)
      · rename_i hc
        rw [if_neg (fun h => h.1 hy)]
        have hyS : y ∈ S.liveLabels := Classical.byContradiction fun h => hc ⟨hy, h⟩
        have := hψ y hyS; rwa [hSHT] at this
  have hdiff : ∀ ψ y, ψ' ψ y ≠ ψ y →
      (y ∈ s.liveLabels ∧ y ∉ S.liveLabels) ∨ (y ∉ s.liveLabels ∧ y ∈ S.liveLabels) := by
    intro ψ y hne
    by_cases h1 : y ∈ s.liveLabels ∧ y ∉ S.liveLabels
    · exact .inl h1
    · by_cases h2 : y ∉ s.liveLabels ∧ y ∈ S.liveLabels
      · exact .inr h2
      · exfalso; apply hne
        show (if y ∈ s.liveLabels ∧ y ∉ S.liveLabels then _ else if y ∉ s.liveLabels ∧ y ∈ S.liveLabels then φ y else ψ y) = ψ y
        rw [if_neg h1, if_neg h2]
  have ha_eq : ∀ y, s.shape (.bind f i) = some y → a = y := by
    intro y hy; simp only [a, hy]
  have hT2 : ∀ ψ q, s.valAt q (ψ' ψ) = s.valAt q ψ := by
    intro ψ q
    refine eq_of_two_indep (a := a) (b := l) (fun hne => ?_) (fun hne => ?_) (fun y hya hyl => ?_)
    · rcases hdiff ψ a hne with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact hold a (hlive2 a h1 h2) q
      · rcases hlive1 a h2 with h3 | h3
        · exact absurd h3 h1
        · rw [h3]; exact hlou.1.resolve_left (h3 ▸ h1) q
    · rcases hdiff ψ l hne with ⟨-, h2⟩ | ⟨h1, -⟩
      · exact absurd hlL h2
      · exact hlou.1.resolve_left h1 q
    · by_cases hy : ψ' ψ y = ψ y
      · exact hy
      · exfalso
        rcases hdiff ψ y hy with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · exact hya (ha_eq y (hlive2 y h1 h2)).symm
        · rcases hlive1 y h2 with h3 | h3
          · exact h1 h3
          · exact hyl h3
  have hval' : ∀ q, (s.takeLabel l).valAt q = s.valAt q ∨ (s.takeLabel l).valAt q = fun _ => .moved := t1val
  refine ⟨fun ψ hψ f' i' hpi => ?_, fun ψ hψ q l' hl' => ?_, fun y hy => ?_, fun f' i' l' hl' => ?_, hacyc, hfresh⟩
  · show GoodVal _ _ (S.valAt _ ψ) (S.tyAt _).m
    rw [hSval, hSty]
    rw [hSpos] at hpi
    rcases hval' (.bind f' i') with e | e
    · rw [e, ← hT2]; exact hs.bind _ (hT1 ψ hψ) f' i' hpi
    · rw [e]; exact .inl (.moved _)
  · rw [hSHT, hSval]
    rw [hSsh] at hl'
    split at hl'
    · rename_i hq; subst hq
      simp only [Option.some.injEq] at hl'; subst hl'
      rcases hval' (.bind f i) with e | e
      · rw [e, hval, hTl]; exact .mem hv
      · rw [e]; exact .moved _
    · obtain ⟨hsh, e⟩ := t1sh q l' hl'
      rw [e, ← hT2]; exact hs.holder _ (hT1 ψ hψ) q l' hsh
  · rw [hSHM, hSHT]
    rcases hlive1 y hy with h | rfl
    · exact hs.held y h
    · exact hMl
  · rw [hSty, hSHT]
    rw [hSsh] at hl'
    split at hl'
    · rename_i hq; rw [hq]; simp only [Option.some.injEq] at hl'; subst hl'; exact hTl.symm
    · exact hs.holderTy f' i' l' (t1sh _ l' hl').1

/-- **An assignment to a FIELD, then D112's invalidation, keeps the invariant where the strict test
passes** (the orchestrator's write rule, 2026-11-21). `p.f := v` (a path other than `[]`/`[*]`) writes
`v` at the path; the state between the write and the test need not be good (a later dependent field),
but the write and the invalidation keep the structural part (`SStruct.setContent`,
`SStruct.invalidate`), and the run's test `lentOk` at a field path is `StateOk` (`sgood_of_stateOk`).
The value's membership (`hv`) is not used: the test reads the written position whole. -/
theorem setContent_field_sgood {s s₁ : SState} (hs : SGood K.dm K.Γ φ s) {p : Place} {f i : Nat}
    {steps : List Step} (hres : resolve s p = some (.bind f i, steps)) (hst : steps ≠ [] ∧ steps ≠ [.deref])
    {v : Sem} (_hv : v ∈ₛ[K.dm.read] (placeTy K φ p s).m)
    (h : setContent K φ (.bind f i) steps v (s.access (.bind f i) (dataHit steps)) = some (⟨⟩, s₁))
    (hok : lentOk K φ p (invalidate K φ p s₁)) :
    SGood K.dm K.Γ φ (invalidate K φ p s₁) := by
  have hS₁ : SStruct K.dm s₁ := (hs.struct.access _ _).setContent h
  have hS := hS₁.invalidate (φ := φ) p
  have hE : EnvLe s (invalidate K φ p s₁) := (envLe_access s _ _).trans
    ((setContent_envLe K φ h).trans (invalidate_props K φ (fun _ => True) p hS₁.acyc).2.1)
  have hr : resolve (invalidate K φ p s₁) p = some (.bind f i, steps) := (resolve_envLe hE p).trans hres
  unfold lentOk at hok; rw [hr] at hok
  rcases hok with h0 | h0 | hok
  · exact absurd h0 hst.1
  · exact absurd h0 hst.2
  · exact sgood_of_stateOk hS hok

/-- The type of a place at a root or through `*`: its binding's stored type. -/
theorem placeTy_root {s : SState} {p : Place} {f i : Nat} {steps : List Step}
    (hres : resolve s p = some (.bind f i, steps)) (hst : steps = [] ∨ steps = [.deref]) :
    (placeTy K φ p s).m = (s.tyAt (.bind f i)).m := by
  unfold placeTy contentOf
  rw [hres]
  rcases hst with rfl | rfl
  · show (TyS.plain ((s.access (.bind f i) (dataHit [])).tyAt (.bind f i)).m).m = _
    rw [tyAt_access]; rfl
  · rfl

/-- **An assignment's write** (`assignAt`), the value checked at the place's type at the write and its
label at that type (the strict `.assign` clause's test), then D112's invalidation (`invalidate`), where
the strict test below a root (`lentOk`) passes.

ADDED HYPOTHESIS `hlou` (`RunPresInd`'s `LoU` for the label written, as in `sgood_pushBindShaped`): a
borrow written at a root makes the root its holder, so the label is live after; `runT_rinv` concludes it
of every result. -/
theorem assignAt_sgood {p : Place} {v : Sem} {R : TyS} {s s' : SState} {r : Res}
    (hs : SGood K.dm K.Γ φ s) (hv : v ∈ₛ[K.dm.read] (placeTy K φ p s).m) (hl : labTyOk s R.label (placeTy K φ p s).m)
    (hlab : LabOk K.dm s (v, R)) (hlou : LoU s R.label) (h : assignAt K φ p v R.label s = some (r, s'))
    (hok : lentOk K φ p (invalidate K φ p s')) :
    GoodRes K.dm.read r ∧ LabOk K.dm s' r ∧ SGood K.dm K.Γ φ (invalidate K φ p s') := by
  unfold assignAt at h
  cases hres : resolve s p with
  | none => rw [hres] at h; cases h
  | some ps =>
  obtain ⟨pos, steps⟩ := ps
  rw [hres] at h
  dsimp only at h
  obtain ⟨f, i, rfl⟩ : ∃ f i, pos = .bind f i := by
    have := resolve_bind hres
    cases pos with
    | bind f i => exact ⟨f, i, rfl⟩
    | temp => exact absurd this (by simp [IsTemp])
  have hpos : Pos.bind f i ∈ s.positions := resolve_mem hres
  have hpb : ¬ IsTemp (Pos.bind f i) := resolve_bind hres
  generalize hs₁e : (if (steps.isEmpty && (s.shape (Pos.bind f i)).isSome) = true then s
      else s.access (Pos.bind f i) (dataHit steps)) = s₁ at h
  have hs₁ : SGood K.dm K.Γ φ s₁ := by rw [← hs₁e]; split; exact hs; exact access_sgood hs _ _
  have hpos₁ : Pos.bind f i ∈ s₁.positions := by
    rw [← hs₁e]; split; exact hpos; rw [access_positions]; exact hpos
  have hty₁ : ∀ q, s₁.tyAt q = s.tyAt q := by intro q; rw [← hs₁e]; split; rfl; exact tyAt_access _ _ _ q
  have hHT₁ : s₁.heldTy = s.heldTy := by rw [← hs₁e]; split; rfl; exact heldTy_access _ _ _
  have hHM₁ : s₁.heldMem = s.heldMem := by rw [← hs₁e]; split; rfl; exact heldMem_access _ _ _
  have hlou₁ : LoU s₁ R.label := by
    rw [← hs₁e]; split
    · exact hlou
    · intro y hy; exact lou_access (fun _ => True) hs.acyc (hlou y hy) _ _
  split at h
  · cases h
  rename_i s₃ hsc
  simp only [Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  refine ⟨.inl ⟨(), rfl⟩, (fun l hl => by cases hl), ?_⟩
  by_cases hst : steps = [] ∨ steps = [.deref]
  · apply invalidate_sgood
    have hvT : v ∈ₛ[K.dm.read] (s.tyAt (.bind f i)).m := by rw [← placeTy_root hres hst]; exact hv
    rcases hst with rfl | rfl
    · -- a root: the old borrow ends, the value is written, a written borrow is held there
      obtain ⟨-, -, -, hpos₃, hlou₃, hroot⟩ := assign_mid K φ (fun _ => True) hs₁.acyc hpos₁ hpb hlou₁ hsc
      obtain ⟨-, hold⟩ := hroot rfl
      simp only [List.isEmpty_nil, if_true] at hsc
      obtain ⟨s₂, hs₂, hpos₂, hty₂, hHT₂, hHM₂, hsc₂⟩ : ∃ s₂, SGood K.dm K.Γ φ s₂ ∧ Pos.bind f i ∈ s₂.positions ∧
          (∀ q, s₂.tyAt q = s.tyAt q) ∧ s₂.heldTy = s.heldTy ∧ s₂.heldMem = s.heldMem ∧
          setContent K φ (Pos.bind f i) [] v s₂ = some (⟨⟩, s₃) := by
        cases hsh : s₁.shape (Pos.bind f i) with
        | none => simp only [hsh] at hsc; exact ⟨s₁, hs₁, hpos₁, hty₁, hHT₁, hHM₁, hsc⟩
        | some l =>
          simp only [hsh] at hsc
          exact ⟨s₁.endLabel l, endLabel_sgood hs₁ l, by rw [endLabel_positions]; exact hpos₁,
            fun q => by rw [tyAt_endLabel, hty₁], by rw [heldTy_endLabel, hHT₁], by rw [heldMem_endLabel, hHM₁], hsc⟩
      have e3 : s₃ = s₂.setAt (.bind f i) fun _ => v := by
        have : setContent K φ (Pos.bind f i) [] v s₂ = some (⟨⟩, s₂.setAt (.bind f i) fun _ => v) :=
          setContent_root K φ _ _ _ (.inl rfl)
        rw [this] at hsc₂; simp only [Option.some.injEq, Prod.mk.injEq] at hsc₂; exact hsc₂.2.symm
      subst e3
      have hs₃ : SGood K.dm K.Γ φ (s₂.setAt (.bind f i) fun _ => v) :=
        sgood_setAt_const hs₂ (by rw [hty₂]; exact hvT)
      cases hR : R.label with
      | none => exact hs₃
      | some l =>
        show SGood _ _ _ { (s₂.setAt (.bind f i) fun _ => v).takeLabel l with
          shape := fun q => if q = .bind f i then some l else ((s₂.setAt (.bind f i) fun _ => v).takeLabel l).shape q }
        have hlab' := hlab l hR
        refine sgood_hold hs₃ (by rw [SState.positions_setAt]; exact hpos₂) (valAt_setAt_self _ _ _ hpos₂)
          (by rw [tyAt_setAt, hty₂]; exact hvT) ?_ ?_ (hlou₃ l hR) hold
        · rw [heldTy_setAt, hHT₂, tyAt_setAt, hty₂, hl l hR, placeTy_root hres (.inl rfl)]
        · rw [heldTy_setAt, heldMem_setAt, hHT₂, hHM₂]; exact hlab'.2
    · -- through `*`: the holder's content written whole
      have e3 : s₃ = s₁.setAt (.bind f i) fun _ => v := by
        have : setContent K φ (Pos.bind f i) [.deref] v s₁ = some (⟨⟩, s₁.setAt (.bind f i) fun _ => v) :=
          setContent_root K φ _ _ _ (.inr rfl)
        simp only [List.isEmpty_cons, Bool.false_eq_true, if_false] at hsc
        rw [this] at hsc; simp only [Option.some.injEq, Prod.mk.injEq] at hsc; exact hsc.2.symm
      subst e3
      have hs₃ := sgood_setAt_const hs₁ (by rw [hty₁]; exact hvT)
      cases R.label <;> exact hs₃
  · -- a field: the dependent-values area
    have hne : steps.isEmpty = false := by
      cases steps with
      | nil => exact absurd (.inl rfl) hst
      | cons _ _ => rfl
    have hs₁a : s₁ = s.access (Pos.bind f i) (dataHit steps) := by rw [← hs₁e, hne]; rfl
    simp only [hne, Bool.false_eq_true, if_false] at hsc
    rw [hs₁a] at hsc
    cases hR : R.label with
    | none =>
      rw [hR] at hok
      exact setContent_field_sgood hs hres ⟨fun e => hst (.inl e), fun e => hst (.inr e)⟩ hv hsc hok
    | some l =>
      cases steps with
      | nil => exact absurd (.inl rfl) hst
      | cons _ _ =>
        rw [hR] at hok
        exact setContent_field_sgood hs hres ⟨fun e => hst (.inl e), fun e => hst (.inr e)⟩ hv hsc hok

open Classical in
/-- **An assignment's tail, the whole clause after the strict test** (the write, D112's invalidation,
the strict test below a root). -/
theorem assign_tail_fund {p : Place} {v : Sem} {R : TyS} {s s' : SState} {r : Res}
    (hs : SGood K.dm K.Γ φ s) (hv : v ∈ₛ[K.dm.read] (placeTy K φ p s).m) (hl : labTyOk s R.label (placeTy K φ p s).m)
    (hlab : LabOk K.dm s (v, R)) (hlou : LoU s R.label)
    (h : (match assignAt K φ p v R.label s with
      | some (r, s₁) =>
        let s₂ := invalidate K φ p s₁
        if lentOk K φ p s₂ then some (r, s₂) else none
      | none => none) = some (r, s')) :
    GoodRes K.dm.read r ∧ LabOk K.dm s' r ∧ LoU s' r.2.label ∧ SGood K.dm K.Γ φ s' := by
  split at h
  · rename_i r₀ s₁ ha
    obtain ⟨hok, h⟩ := open Classical in ite_none_some h
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    obtain ⟨hg, -, hs'⟩ := assignAt_sgood hs hv hl hlab hlou ha hok
    obtain ⟨-, hr, -, -⟩ := assignAt_rinv K φ (fun _ => True) ha hs.acyc hlou
    exact ⟨hg, (fun l h' => by rw [hr] at h'; cases h'), (fun l h' => by rw [hr] at h'; cases h'), hs'⟩
  · cases h

end Ochr.Meaning.Strict
