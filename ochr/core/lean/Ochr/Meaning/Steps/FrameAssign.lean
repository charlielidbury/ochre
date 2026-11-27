import Ochr.Meaning.Steps.FrameBorrow
import Ochr.Meaning.HintM

/-!
# The assignment clause of the frame property (lead35; docs/31 D224)

The paper's row "A borrow; an assignment through a borrow; field paths" of `<sec-frame-proof>` for `p := u`: the
right-hand side (the induction, at the place's stored type, whose label the run does not read: `runT_hintM`), the strict
test of the value and its label at the place's type (`labTyOk` through `FrameInv.heldAll`: the label may have ended), the
assignment's ends ([Access] (O4), the old borrow's end at a root (O3)), the write (O5), at a root a written borrow held
there ((O8), `holdAt_frameInvS`: nothing live is lent at the root after its ends), D112's invalidation (O9), and the
whole-state test below a root (O6).
-/

namespace Ochr.Meaning.Strict
open Ochr.Meaning

variable {K : RunCtx} {φ : Future}

/-- **An assignment's write keeps the structural part, and at a root or through `*` the invariant** (`assignAt_sgood`
before D112's invalidation and the test below a root): what the frame property's assignment clause carries between the
write and the whole-state test. -/
theorem assignAt_struct {p : Place} {v : Sem} {R : TyS} {s s' : SState} {r : Res}
    (hs : SGood K.dm K.Γ φ s) (hv : v ∈ₛ[K.dm.read] (placeTy K φ p s).m) (hl : labTyOk s R.label (placeTy K φ p s).m)
    (hlab : LabOk K.dm s (v, R)) (hlou : LoU s R.label) (hao : AssignOk K φ p s)
    (h : assignAt K φ p v R.label s = some (r, s')) :
    SStruct K.dm s' ∧ (p.steps.2 = [] ∨ p.steps.2 = [.deref] → SGood K.dm K.Γ φ s') := by
  unfold AssignOk at hao
  unfold assignAt at h
  cases hres : resolve s p with
  | none => rw [hres] at h; cases h
  | some ps =>
  obtain ⟨pos, steps⟩ := ps
  rw [hres] at h
  rw [hres] at hao
  dsimp only at h hao
  obtain ⟨f, i, rfl⟩ : ∃ f i, pos = .bind f i := by
    have := resolve_bind hres
    cases pos with
    | bind f i => exact ⟨f, i, rfl⟩
    | temp => exact absurd this (by simp [IsTemp])
  have hpos : Pos.bind f i ∈ s.positions := resolve_mem hres
  have hpb0 : IsTop s (Pos.bind f i) := resolve_top hres
  generalize hs₁e : (if (steps.isEmpty && (s.shape (Pos.bind f i)).isSome) = true then s
      else s.access (Pos.bind f i) (dataHit steps)) = s₁ at h hao
  have hpb : IsTop s₁ (Pos.bind f i) := by
    rw [← hs₁e]; split
    · exact hpb0
    · exact hpb0.envLe (envLe_access s _ _)
  have hs₁ : SGood K.dm K.Γ φ s₁ := by
    rw [← hs₁e]; split
    · exact hs
    · rename_i hc; exact access_sgood hs _ _ (hao.1 (by simpa using hc))
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
  have hsteps : steps = p.steps.2 := by
    unfold resolve at hres; cases hv : s.varPos p.steps.1 <;> simp_all
  by_cases hst : steps = [] ∨ steps = [.deref]
  · refine (fun hg => ⟨SGood.struct hg, fun _ => hg⟩) ?_
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
          exact ⟨s₁.endLabel l, endLabel_sgood hs₁ l (hao.2 rfl l hsh), by rw [endLabel_positions]; exact hpos₁,
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
  · -- a field: the structural part only
    have hne : steps.isEmpty = false := by
      cases steps with
      | nil => exact absurd (.inl rfl) hst
      | cons _ _ => rfl
    have hs₁a : s₁ = s.access (Pos.bind f i) (dataHit steps) := by rw [← hs₁e, hne]; rfl
    simp only [hne, Bool.false_eq_true, if_false] at hsc
    rw [hs₁a] at hsc
    refine ⟨?_, fun hr => absurd (hsteps ▸ hr) hst⟩
    have hS := (hs.struct.access (Pos.bind f i) (dataHit steps)).setContent hsc
    cases hR : R.label with
    | none => exact hS
    | some l =>
      cases steps with
      | nil => exact absurd (.inl rfl) hst
      | cons _ _ => exact hS

end Ochr.Meaning.Strict

namespace Ochr.Meaning.Steps.Form.FrameEnd

open Ochr Ochr.Meaning Ochr.Meaning.Strict

/-- A written borrow held at a root (`assignAt`'s last step). -/
noncomputable def holdAt (t : SState) (pos : Pos) (l : Nat) : SState :=
  { t.takeLabel l with shape := fun q => if q = pos then some l else (t.takeLabel l).shape q }

section
variable {K : RunCtx} {φ : Future} {σ : Nat → Nat} {s₀ : SState} {ks : List Nat}

/-- `live_corr` without goodness. -/
theorem live_corrS {s s' : SState} (h : FrameInvS K σ s₀ ks s s') (hs₀ : FrameStart s₀ ks) (l : Nat) :
    s.Live (σ l) ↔ s'.Live l := by
  refine ⟨fun hl => ?_, live_img h.acc.rel h.acc.shape⟩
  obtain ⟨p, hp, hps⟩ := (SState.live_iff s _).1 hl
  have hpf : p.frameOf < s.env.length := frameOf_lt_of_mem hp
  rw [h.acc.rel.frames.1] at hpf
  by_cases hlt : p.frameOf < s₀.topIdx
  · rw [h.acc.rel.lowerShape p hlt] at hps
    obtain ⟨hk, hl'⟩ := hs₀.callerHeld p _ hlt hps
    rcases h.srange l with e | e
    · exact absurd e hk
    · have := h.counter; omega
  · have hpf' : p.frameOf = s₀.topIdx := by unfold SState.topIdx at hlt ⊢; omega
    rw [h.acc.rel.topShape p hpf'] at hps
    cases e : s'.shape (upPos ks.length p) with
    | none => rw [e] at hps; cases hps
    | some l' =>
      rw [e] at hps
      have := h.acc.rel.inj _ _ (Option.some.inj hps); subst this
      exact (SState.live_iff s' _).2 ⟨_, h.acc.shape' _ _ e, e⟩

/-- **A written borrow held at a root** (`assignAt`'s hold, the paper's (O8)): the label moves from wherever it was held
(its parked temporary) to the root, on both sides; no live label is lent at the root (its ends saw to it), so lending
stays well founded; a label that had ended lends nothing (`ResAtTemp`, `ResDead`) and its records correspond
(`heldAll`). Both states' structural parts after, and the closure's locality after, are hypotheses. -/
theorem holdAt_frameInvS {t t' : SState} (h : FrameInvS K σ s₀ ks t t') (hs₀ : FrameStart s₀ ks) {pos : Pos}
    (hpf : pos.frameOf = s₀.topIdx) {l : Nat} (hres : ResAtTemp s₀ t (some (σ l))) (hresD : ResDead t' (some l))
    (hno : ∀ m (y : Site), t.Live m → y ∈ t.lent m → y.pos ≠ pos)
    (hS : SStruct K.dm (holdAt t pos (σ l))) (hS' : SStruct K.dm (holdAt t' (upPos ks.length pos) l))
    (hri' : SState.RInv (fun _ => False) (holdAt t' (upPos ks.length pos) l)) :
    FrameInvS K σ s₀ ks (holdAt t pos (σ l)) (holdAt t' (upPos ks.length pos) l) := by
  have hA := h.acc
  have htopC : t'.topIdx = 1 := topIdx_cl hA.rel
  have hltC : ∀ n, t'.Live n → n < t'.nextLoan := fun n hn => by
    obtain ⟨q, -, hq⟩ := (SState.live_iff t' n).1 hn
    exact (h.struct'.acyc.2.2 q n hq).2
  have hdeadI : ¬ t.Live (σ l) → t.lent (σ l) = [] := (hres (σ l) rfl).2
  have hdeadC : ¬ t'.Live l → t'.lent l = [] := (hresD l rfl).2
  have hr₁ := frameRel_takeLabel' hA.rel hs₀ hA.uniq hA.shape hA.shape' l (h.srange l)
  have hrec : (σ l ∉ ks → (t.takeLabel (σ l)).heldMem (σ l) = (t'.takeLabel l).heldMem l) ∧
      (t.takeLabel (σ l)).heldTy (σ l) = (t'.takeLabel l).heldTy l := by
    rw [takeLabel_heldMem', takeLabel_heldMem', takeLabel_heldTy', takeLabel_heldTy']
    by_cases hlv : t'.Live l
    · exact hA.rel.held l hlv
    · exact ⟨(h.heldAll l (hresD l rfl).1).2, (h.heldAll l (hresD l rfl).1).1⟩
  have hsites : ∀ x : Site, x.pos.frameOf = s₀.topIdx →
      (x ∈ (t.takeLabel (σ l)).lent (σ l) ↔ upSite ks.length x ∈ (t'.takeLabel l).lent l) := by
    intro x hx
    rw [takeLabel_lent', takeLabel_lent']
    by_cases hlv : t'.Live l
    · obtain ⟨q, -, hq⟩ := (SState.live_iff t _).1 (live_img hA.rel hA.shape hlv)
      exact hA.rel.lentTop l x hx ⟨q, hq⟩
    · have hlvI : ¬ t.Live (σ l) := fun h' => hlv ((live_corrS h hs₀ l).1 h')
      rw [hdeadI hlvI, hdeadC hlv]; simp
  have hr₃ := frameRel_hold hr₁ hpf (takeLabel_noHolder hA.uniq' hA.shape' l) hrec hsites (h.srange l)
    (shapeAt_takeLabel hA.shape' l)
  have hshI : ∀ q, (holdAt t pos (σ l)).shape q = if q = pos then some (σ l) else (t.takeLabel (σ l)).shape q :=
    fun q => rfl
  have hshC : ∀ q, (holdAt t' (upPos ks.length pos) l).shape q =
      if q = upPos ks.length pos then some l else (t'.takeLabel l).shape q := fun q => rfl
  have hlentI : (holdAt t pos (σ l)).lent = t.lent := takeLabel_lent' _ _
  have hposI : (holdAt t pos (σ l)).positions = t.positions := SState.takeLabel_positions _ _
  have hnextI : (holdAt t pos (σ l)).nextLoan = t.nextLoan := takeLabel_nextLoan' _ _
  have hnextC : (holdAt t' (upPos ks.length pos) l).nextLoan = t'.nextLoan := takeLabel_nextLoan' _ _
  have hrecI : (holdAt t pos (σ l)).heldTy = t.heldTy ∧ (holdAt t pos (σ l)).heldMem = t.heldMem :=
    ⟨takeLabel_heldTy' _ _, takeLabel_heldMem' _ _⟩
  have hrecC : (holdAt t' (upPos ks.length pos) l).heldTy = t'.heldTy ∧
      (holdAt t' (upPos ks.length pos) l).heldMem = t'.heldMem := ⟨takeLabel_heldTy' _ _, takeLabel_heldMem' _ _⟩
  have hliveI : ∀ a, (holdAt t pos (σ l)).Live a → t.Live a ∨ (a = σ l ∧ ¬ t.Live (σ l)) := fun a ha => by
    obtain ⟨q, -, hq⟩ := (SState.live_iff _ a).1 ha
    rw [hshI] at hq
    split at hq
    · cases hq
      by_cases hlv : t.Live (σ l)
      · exact .inl hlv
      · exact .inr ⟨rfl, hlv⟩
    · have hq' : t.shape q = some a := SState.takeLabel_shape_some hq
      exact .inl ((SState.live_iff t a).2 ⟨q, hA.shape q a hq', hq'⟩)
  have hliveC : ∀ a, (holdAt t' (upPos ks.length pos) l).Live a → a < t'.nextLoan := fun a ha => by
    obtain ⟨q, -, hq⟩ := (SState.live_iff _ a).1 ha
    rw [hshC] at hq
    split at hq
    · cases hq; exact (hresD l rfl).1
    · have hq' : t'.shape q = some a := SState.takeLabel_shape_some hq
      exact hltC a ((SState.live_iff t' a).2 ⟨q, hA.shape' q a hq', hq'⟩)
  refine FrameInvS.mk ?_ hS hS' (by rw [hnextI]; exact h.counter) h.srange
    (fun m y hy hf => h.bsites m y (by rw [hlentI] at hy; exact hy) hf) ?_ ?_ ?_ ?_
  · exact
    { rel := hr₃
      uniq := hS.uniq
      shape := fun p n hp => (hS.acyc.2.2 p n hp).1
      lend := by
        obtain ⟨rk, hrk⟩ := hA.lend
        refine ⟨rk, fun a c y ha hy hc => ?_⟩
        rw [hlentI] at hy
        rw [hshI] at hc
        split at hc
        · rename_i e
          rcases hliveI a ha with ha' | ⟨rfl, hd⟩
          · exact absurd e (hno a y ha' hy)
          · rw [hdeadI hd] at hy; cases hy
        · have hc' : t.shape y.pos = some c := SState.takeLabel_shape_some hc
          rcases hliveI a ha with ha' | ⟨rfl, hd⟩
          · exact hrk a c y ha' hy hc'
          · rw [hdeadI hd] at hy; cases hy
      pfill := fun k hk y hy hyf => hA.pfill k hk y (by rw [hlentI] at hy; exact hy) hyf
      held := hS.held
      cells := by
        show ks.length ≤ (((t'.takeLabel l).env.headD {}).binds.length)
        rw [headD_len_takeLabel]; exact hA.cells
      uniq' := hS'.uniq
      rinv' := hri'
      noParam := fun p hp => by
        show Ochr.Meaning.FT _ ((t'.takeLabel l).valAt p)
        rcases SState.takeLabel_valAt t' l p with e' | e' <;> rw [e']
        · exact hA.noParam p hp
        · exact FT.const _ _
      order := fun a c ha hc => h.orderAll a c (hliveC a ha) (hliveC c hc)
      mono := fun a c ha hc => h.monoAll a c (hliveC a ha) (hliveC c hc) }
  · intro m y hm hy hf
    rw [hlentI] at hy
    rw [hposI]
    rcases hliveI m hm with hm' | ⟨rfl, hd⟩
    · exact h.psites m y hm' hy hf
    · rw [hdeadI hd] at hy; cases hy
  · intro n hn
    rw [hnextC] at hn
    rw [hrecI.1, hrecI.2, hrecC.1, hrecC.2]
    exact h.heldAll n hn
  · intro a c ha hc; exact h.orderAll a c (hnextC ▸ ha) (hnextC ▸ hc)
  · intro a c ha hc; exact h.monoAll a c (hnextC ▸ ha) (hnextC ▸ hc)

end

/-! ## The assignment's ends -/

/-- `assignAt`'s state before the write: [Access] of what the place owns, then at a root the old borrow's end. -/
noncomputable def assignPre (t : SState) (pos : Pos) (steps : List Step) : SState :=
  let s := if steps.isEmpty && (t.shape pos).isSome then t else t.access pos (dataHit steps)
  if steps.isEmpty then (match s.shape pos with | some l => s.endLabel l | none => s) else s

/-- `assignAt`'s last step: at a root, a written borrow held there. -/
noncomputable def assignHold (lab : Option Nat) (steps : List Step) (s : SState) (pos : Pos) : SState :=
  match lab, steps with
  | some l, [] => holdAt s pos l
  | _, _ => s

theorem assignAt_eq {K : RunCtx} {φ : Future} {p : Place} {v : Sem} {lab : Option Nat} {t : SState} {pos : Pos}
    {steps : List Step} (hrp : resolve t p = some (pos, steps)) :
    assignAt K φ p v lab t = match setContent K φ pos steps v (assignPre t pos steps) with
      | none => none
      | some (⟨⟩, s) => some ((.el0 Unit (), .plain TyM.unit), assignHold lab steps s pos) := by
  unfold assignAt; rw [hrp]; rfl

section
variable {K : RunCtx} {φ : Future} {σ : Nat → Nat} {s₀ : SState} {ks : List Nat}

/-- The old borrow's strict end at corresponding roots. -/
theorem rootEnd_iff {a a' : SState} (hA : AccInv K σ s₀ ks a a') {pos : Pos} (hpf : pos.frameOf = s₀.topIdx) :
    (∀ l, a.shape pos = some l → EndOk K φ a l) ↔ (∀ l, a'.shape (upPos ks.length pos) = some l → EndOk K φ a' l) := by
  have e := hA.rel.topShape pos hpf
  cases hq : a'.shape (upPos ks.length pos) with
  | none =>
    rw [hq] at e
    exact ⟨fun _ l hl => (by cases hl), fun _ l hl => (by rw [e] at hl; cases hl)⟩
  | some l' =>
    rw [hq] at e
    have hlv : a'.Live l' := (SState.live_iff a' l').2 ⟨_, hA.shape' _ _ hq, hq⟩
    have hk := endOk_corr K φ hA.rel hA.uniq hA.shape hA.held hA.loc hlv
    constructor
    · intro h l hl; cases hl; exact hk.1 (h _ e)
    · intro h l hl; rw [e] at hl; cases hl; exact hk.2 (h l' rfl)

/-- **The assignment's ends across the internal relation** (the paper's (O4) and, at a root, (O3)): the strict test on
both sides or neither, and where it passes the internal relation after the access and the old borrow's end. -/
theorem assignPre_frameInv (hs₀ : FrameStart s₀ ks) {t t' : SState} (h : FrameInv K φ σ s₀ ks t t') {p : Place}
    {pos : Pos} {steps : List Step} (hrp : resolve t p = some (pos, steps))
    (hrp' : resolve t' p = some (upPos ks.length pos, steps)) (hpf : pos.frameOf = s₀.topIdx) :
    (AssignOk K φ p t ↔ AssignOk K φ p t') ∧
      (AssignOk K φ p t → FrameInv K φ σ s₀ ks (assignPre t pos steps) (assignPre t' (upPos ks.length pos) steps)) := by
  have hA := h.acc
  have hc : (t.shape pos).isSome = (t'.shape (upPos ks.length pos)).isSome := by
    rw [hA.rel.topShape pos hpf]; cases t'.shape _ <;> rfl
  obtain ⟨hacc, hacok⟩ := frameRel_access φ hs₀ hA hpf (dataHit steps)
  unfold AssignOk
  rw [hrp, hrp']
  dsimp only
  rw [← hc]
  -- the state after the access, related
  have hpre : ∀ (hok : (steps.isEmpty && (t.shape pos).isSome) = false → AccessOk K φ t pos (dataHit steps)),
      FrameInv K φ σ s₀ ks (if (steps.isEmpty && (t.shape pos).isSome) = true then t else t.access pos (dataHit steps))
        (if (steps.isEmpty && (t.shape pos).isSome) = true then t' else t'.access (upPos ks.length pos) (dataHit steps)) := by
    intro hok
    by_cases hcond : (steps.isEmpty && (t.shape pos).isSome) = true
    · rw [if_pos hcond, if_pos hcond]; exact h
    · rw [if_neg hcond, if_neg hcond]
      have ho := hok (by simpa using hcond)
      exact h.of_ops hacc (Strict.access_sgood h.good _ _ ho) (Strict.access_sgood h.good' _ _ (hacok.1 ho))
        (shrinks_access _ _ _) (shrinks_access _ _ _)
  have hpreA : AccInv K σ s₀ ks (if (steps.isEmpty && (t.shape pos).isSome) = true then t else t.access pos (dataHit steps))
        (if (steps.isEmpty && (t.shape pos).isSome) = true then t' else t'.access (upPos ks.length pos) (dataHit steps)) := by
    by_cases hcond : (steps.isEmpty && (t.shape pos).isSome) = true
    · rw [if_pos hcond, if_pos hcond]; exact hA
    · rw [if_neg hcond, if_neg hcond]; exact hacc
  refine ⟨and_congr (imp_congr_right fun _ => hacok) (imp_congr_right fun _ => rootEnd_iff hpreA hpf), ?_⟩
  rintro ⟨hok1, hok2⟩
  have hF := hpre hok1
  unfold assignPre
  dsimp only
  rw [← hc]
  generalize (if (steps.isEmpty && (t.shape pos).isSome) = true then t else t.access pos (dataHit steps)) = a at hF hok2 ⊢
  generalize (if (steps.isEmpty && (t.shape pos).isSome) = true then t' else
    t'.access (upPos ks.length pos) (dataHit steps)) = a' at hF ⊢
  by_cases hse : steps.isEmpty = true
  rotate_left
  · rw [if_neg hse, if_neg hse]; exact hF
  rw [if_pos hse, if_pos hse]
  have e := hF.acc.rel.topShape pos hpf
  cases hq : a'.shape (upPos ks.length pos) with
  | none => rw [hq] at e; rw [e]; exact hF
  | some l' =>
    rw [hq] at e; rw [e]
    dsimp only
    have hlv : a'.Live l' := (SState.live_iff a' l').2 ⟨_, hF.acc.shape' _ _ hq, hq⟩
    have hend := hok2 hse (σ l') e
    have hk := endOk_corr K φ hF.acc.rel hF.acc.uniq hF.acc.shape hF.acc.held hF.acc.loc hlv
    exact hF.of_ops (AccInv.endLabel hs₀ hF.acc hlv) (Strict.endLabel_sgood hF.good _ hend)
      (Strict.endLabel_sgood hF.good' _ (hk.1 hend)) (shrinks_endLabel _ _) (shrinks_endLabel _ _)

end

/-- **After an assignment's ends at a root, the root holds nothing and no live label is lent there**: its old borrow's
end re-roots every site at it (`endLabel_noSiteAt`), and where it held none, its access ended every live label lent there
(`access_noLiveSiteAt`). -/
theorem assignPre_root {t : SState} (hlend : LendWF t) (hu : t.Uniq) {pos : Pos} (hpos : pos ∈ t.positions) :
    (assignPre t pos []).shape pos = none ∧
      ∀ m (y : Site), (assignPre t pos []).Live m → y ∈ (assignPre t pos []).lent m → y.pos ≠ pos := by
  unfold assignPre
  cases hsh : t.shape pos with
  | some l₀ =>
    simp only [List.isEmpty_nil, hsh, Option.isSome_some, Bool.and_self, if_true]
    have hh : t.holderOf l₀ = some pos := by
      obtain ⟨r, hr⟩ := SState.holderOf_of_live ((SState.live_iff t l₀).2 ⟨pos, hpos, hsh⟩)
      rw [hu r pos l₀ (SState.holderOf_spec hr).2 hsh] at hr; exact hr
    refine ⟨?_, fun m y _ hy => endLabel_noSiteAt hlend hh m y hy⟩
    rw [SState.endLabel_eq hh, SState.endAt_shape]; simp
  | none =>
    simp only [List.isEmpty_nil, hsh, Option.isSome_none, Bool.and_false, Bool.false_eq_true, if_false, if_true]
    have hn : (t.access pos (dataHit [])).shape pos = none := by
      cases e : (t.access pos (dataHit [])).shape pos with
      | none => rfl
      | some x => have := (shrinks_access t pos (dataHit [])).shape pos x e; rw [hsh] at this; cases this
    rw [hn]
    exact ⟨hn, access_noLiveSiteAt t pos⟩

theorem shrinks_assignPre (t : SState) (pos : Pos) (steps : List Step) : Shrinks t (assignPre t pos steps) := by
  unfold assignPre
  dsimp only
  have h1 : Shrinks t (if (steps.isEmpty && (t.shape pos).isSome) = true then t else t.access pos (dataHit steps)) := by
    split
    · exact Shrinks.refl t
    · exact shrinks_access _ _ _
  generalize (if (steps.isEmpty && (t.shape pos).isSome) = true then t else t.access pos (dataHit steps)) = a at h1 ⊢
  split
  · split
    · exact h1.trans (shrinks_endLabel _ _)
    · exact h1
  · exact h1

theorem resolve_steps {u : SState} {p : Place} {pos : Pos} {steps : List Step} (h : resolve u p = some (pos, steps)) :
    steps = p.steps.2 := by
  unfold resolve at h; cases hv : u.varPos p.steps.1 <;> simp_all

/-- At a root or through `*` the test below a root passes. -/
theorem lentOk_of_root {K : RunCtx} {φ : Future} {p : Place} (u : SState) (h : p.steps.2 = [] ∨ p.steps.2 = [.deref]) :
    lentOk K φ p u := by
  unfold lentOk
  cases e : resolve u p with
  | none => trivial
  | some x =>
    obtain ⟨pos, steps⟩ := x
    rw [resolve_steps e]
    rcases h with h | h
    · exact .inl h
    · exact .inr (.inl h)

section
variable {K : RunCtx} {φ : Future} {σ : Nat → Nat} {s₀ : SState} {ks : List Nat}

open Classical in
/-- **An assignment's tail across the internal relation** (after the right-hand side and the strict test): the
assignment's strict test on both sides or neither (`assignPre_frameInv`), the write ((O5), `setContent_corr`), at a root
the written borrow held ((O8), `holdAt_frameInvS`), D112's invalidation ((O9)), the whole-state test below a root ((O6),
`lentOk_corr`), and goodness after from the strict fundamental lemma's assignment clause (`Strict.assign_tail_fund`). -/
theorem assignTail_agree (hs₀ : FrameStart s₀ ks) {t t' : SState} (h : FrameInv K φ σ s₀ ks t t') (p : Place) (v : Sem)
    {R R' : TyS} (hR : R = { R' with label := R'.label.map σ }) (hres : ResAtTemp s₀ t R.label)
    (hresD : ResDead t' R'.label)
    (hv : v ∈ₛ[K.dm.read] (placeTy K φ p t).m) (hl : labTyOk t R.label (placeTy K φ p t).m)
    (hv' : v ∈ₛ[K.dm.read] (placeTy K φ p t').m) (hl' : labTyOk t' R'.label (placeTy K φ p t').m)
    (hlab : LabOk K.dm t (v, R)) (hlou : LoU t R.label) (hlab' : LabOk K.dm t' (v, R')) (hlou' : LoU t' R'.label) :
    FrameAgreeI K φ σ s₀ ks
      (match SM.guarded (AssignOk K φ p) (assignAt K φ p v R.label) t with
        | some (r, s₁) =>
          let s₂ := invalidate K φ p s₁
          if InvalidateOk K φ p s₁ ∧ lentOk K φ p s₂ then some (r, s₂) else none
        | none => none)
      (match SM.guarded (AssignOk K φ p) (assignAt K φ p v R'.label) t' with
        | some (r, s₁) =>
          let s₂ := invalidate K φ p s₁
          if InvalidateOk K φ p s₁ ∧ lentOk K φ p s₂ then some (r, s₂) else none
        | none => none) := by
  have hA := h.acc
  obtain ⟨hres_c, hframe⟩ := resolve_corr hA.rel p
  cases hrp : resolve t p with
  | none =>
    have hrp' : resolve t' p = none := by rw [hres_c, hrp]; rfl
    have e1 : SM.guarded (AssignOk K φ p) (assignAt K φ p v R.label) t = none := by
      unfold SM.guarded assignAt; rw [hrp]; split <;> rfl
    have e2 : SM.guarded (AssignOk K φ p) (assignAt K φ p v R'.label) t' = none := by
      unfold SM.guarded assignAt; rw [hrp']; split <;> rfl
    rw [e1, e2]; trivial
  | some x =>
    obtain ⟨pos, steps⟩ := x
    have hpf := hframe pos steps hrp
    have hrp' : resolve t' p = some (upPos ks.length pos, steps) := by rw [hres_c, hrp]; rfl
    obtain ⟨haoI, hpre⟩ := assignPre_frameInv hs₀ h hrp hrp' hpf
    by_cases hao : AssignOk K φ p t
    rotate_left
    · have e1 : SM.guarded (AssignOk K φ p) (assignAt K φ p v R.label) t = none := by
        unfold SM.guarded; rw [if_neg hao]
      have e2 : SM.guarded (AssignOk K φ p) (assignAt K φ p v R'.label) t' = none := by
        unfold SM.guarded; rw [if_neg (fun h' => hao (haoI.2 h'))]
      rw [e1, e2]; trivial
    have hao' := haoI.1 hao
    have hP := hpre hao
    have hsc := setContent_corr φ hP.acc hpf steps v
    cases e1 : setContent K φ pos steps v (assignPre t pos steps) with
    | none =>
      rw [e1] at hsc
      cases e2 : setContent K φ (upPos ks.length pos) steps v (assignPre t' (upPos ks.length pos) steps) with
      | some _ => rw [e2] at hsc; exact hsc.elim
      | none =>
        have g1 : SM.guarded (AssignOk K φ p) (assignAt K φ p v R.label) t = none := by
          unfold SM.guarded; rw [if_pos hao, assignAt_eq hrp, e1]
        have g2 : SM.guarded (AssignOk K φ p) (assignAt K φ p v R'.label) t' = none := by
          unfold SM.guarded; rw [if_pos hao', assignAt_eq hrp', e2]
        rw [g1, g2]; trivial
    | some y =>
      rw [e1] at hsc
      cases e2 : setContent K φ (upPos ks.length pos) steps v (assignPre t' (upPos ks.length pos) steps) with
      | none => rw [e2] at hsc; exact hsc.elim
      | some y' =>
        rw [e2] at hsc
        obtain ⟨⟨⟩, sc⟩ := y
        obtain ⟨⟨⟩, sc'⟩ := y'
        obtain ⟨-, hc⟩ := hsc
        have hat : assignAt K φ p v R.label t = some ((.el0 Unit (), .plain TyM.unit), assignHold R.label steps sc pos) := by
          rw [assignAt_eq hrp, e1]
        have hat' : assignAt K φ p v R'.label t' =
            some ((.el0 Unit (), .plain TyM.unit), assignHold R'.label steps sc' (upPos ks.length pos)) := by
          rw [assignAt_eq hrp', e2]
        have g1 : SM.guarded (AssignOk K φ p) (assignAt K φ p v R.label) t =
            some ((.el0 Unit (), .plain TyM.unit), assignHold R.label steps sc pos) := by
          unfold SM.guarded; rw [if_pos hao, hat]
        have g2 : SM.guarded (AssignOk K φ p) (assignAt K φ p v R'.label) t' =
            some ((.el0 Unit (), .plain TyM.unit), assignHold R'.label steps sc' (upPos ks.length pos)) := by
          unfold SM.guarded; rw [if_pos hao', hat']
        rw [g1, g2]
        dsimp only
        have hS0 : FrameInvS K σ s₀ ks sc sc' := hP.toS.of_ops hc (hP.good.struct.setContent e1)
          (hP.good'.struct.setContent e2) (shrinks_setContent e1) (shrinks_setContent e2)
        obtain ⟨hSt, -⟩ := Strict.assignAt_struct h.good hv hl hlab hlou hao hat
        obtain ⟨hSt', -⟩ := Strict.assignAt_struct h.good' hv' hl' hlab' hlou' hao' hat'
        have hri' := (assignAt_rinv K φ (fun _ => False) hat' hA.rinv' hlou').1
        have hshr : Shrinks t sc := (shrinks_assignPre t pos steps).trans (shrinks_setContent e1)
        have hshr' : Shrinks t' sc' := (shrinks_assignPre t' _ steps).trans (shrinks_setContent e2)
        have hRl : R.label = R'.label.map σ := by rw [hR]
        -- the hold
        have hS : FrameInvS K σ s₀ ks (assignHold R.label steps sc pos)
            (assignHold R'.label steps sc' (upPos ks.length pos)) := by
          rcases Option.eq_none_or_eq_some R'.label with hl0 | ⟨l, hl0⟩
          · have hRn : R.label = none := by rw [hRl, hl0]; rfl
            rw [hRn, hl0]
            cases steps <;> exact hS0
          · have hRs : R.label = some (σ l) := by rw [hRl, hl0]; rfl
            rw [hRs, hl0]
            rw [hRs] at hSt hres; rw [hl0] at hSt' hri' hresD
            cases steps with
            | cons a st => exact hS0
            | nil =>
              have hpos : pos ∈ t.positions := resolve_mem hrp
              obtain ⟨-, hno0⟩ := assignPre_root hA.lend hA.uniq hpos
              have hno : ∀ m (y : Site), sc.Live m → y ∈ sc.lent m → y.pos ≠ pos := fun m y hm hy e => by
                obtain ⟨m', z, hm', hz, ez⟩ := (shrinks_setContent e1).liveSites m y hm hy
                exact hno0 m' z hm' hz (ez.trans e)
              exact holdAt_frameInvS hS0 hs₀ hpf (hres.shrinks hA.uniq hshr) (hresD.shrinks hshr') hno hSt hSt' hri'
        -- the invalidation
        obtain ⟨hS2, hiok⟩ := FrameInvS.invalidate φ hs₀ hS p
        by_cases hiv : InvalidateOk K φ p (assignHold R.label steps sc pos)
        rotate_left
        · rw [if_neg (fun h => hiv h.1), if_neg (fun h => hiv (hiok.2 h.1))]; trivial
        have hiv' := hiok.1 hiv
        -- the whole-state test below a root
        have hl2 : lentOk K φ p (invalidate K φ p (assignHold R.label steps sc pos)) ↔
            lentOk K φ p (invalidate K φ p (assignHold R'.label steps sc' (upPos ks.length pos))) := by
          have hsteps := resolve_steps hrp
          by_cases hst : steps = [] ∨ steps = [.deref]
          · have hst' : p.steps.2 = [] ∨ p.steps.2 = [.deref] := hsteps ▸ hst
            exact ⟨fun _ => lentOk_of_root _ hst', fun _ => lentOk_of_root _ hst'⟩
          · have hne : steps ≠ [] := fun e => hst (.inl e)
            obtain ⟨-, hR1, hT1⟩ := assignAt_goodOn h.good.struct h.good.goodOn hao hat hrp hne
            obtain ⟨-, hR1', hT1'⟩ := assignAt_goodOn h.good'.struct h.good'.goodOn hao' hat' hrp' hne
            have hT0 : t.topIdx = s₀.topIdx := topIdx_eq hA.rel
            have hT0' : t'.topIdx = 1 := topIdx_cl hA.rel
            have hR2 := GoodOn.invalidate (T := s₀.topIdx) p hS.struct (by rw [hT0] at hR1; exact hR1)
              (by rw [← hT0]; exact hT1) hiv
            have hR2' := GoodOn.invalidate (T := 1) p hS.struct' (by rw [hT0'] at hR1'; exact hR1')
              (by rw [← hT0']; exact hT1') hiv'
            exact lentOk_corr hS2.acc.rel hS2.acc.shape hS2.acc.shape' hS2.acc.held hS2.acc.loc hR2 hR2' p
        by_cases hlo : lentOk K φ p (invalidate K φ p (assignHold R.label steps sc pos))
        rotate_left
        · rw [if_neg (fun h => hlo h.2), if_neg (fun h => hlo (hl2.2 h.2))]; trivial
        rw [if_pos ⟨hiv, hlo⟩, if_pos ⟨hiv', hl2.1 hlo⟩]
        have hg := (Strict.assign_tail_fund h.good hv hl hlab hlou
          (by rw [g1]; dsimp only; rw [if_pos ⟨hiv, hlo⟩])).2.2.2
        have hg' := (Strict.assign_tail_fund h.good' hv' hl' hlab' hlou'
          (by rw [g2]; dsimp only; rw [if_pos ⟨hiv', hl2.1 hlo⟩])).2.2.2
        exact ⟨rfl, rfl, hS2.toInv hg hg', ⟨fun _ e => (by cases e), fun _ e => (by cases e)⟩⟩


/-- The place's type read on a copy is the same on both sides (the label dropped). -/
theorem placeTy_corr (hs₀ : FrameStart s₀ ks) {t t' : SState} (h : AccInv K σ s₀ ks t t') (p : Place) :
    placeTy K φ p t = placeTy K φ p t' := by
  obtain ⟨hc, -⟩ := contentOf_corr φ hs₀ h p
  unfold placeTy
  cases e1 : contentOf K φ p t with
  | none =>
    rw [e1] at hc
    cases e2 : contentOf K φ p t' with
    | none => rfl
    | some _ => rw [e2] at hc; exact hc.elim
  | some y =>
    rw [e1] at hc
    cases e2 : contentOf K φ p t' with
    | none => rw [e2] at hc; exact hc.elim
    | some y' =>
      rw [e2] at hc
      obtain ⟨⟨v, T, pos, steps⟩, u⟩ := y
      obtain ⟨⟨v', T', pos', steps'⟩, u'⟩ := y'
      obtain ⟨-, hT, -⟩ := hc
      dsimp only; rw [hT]

/-- An assignment's hint (the place's stored type, for a constructor or an embedded value) has the same type on both
sides: only its label differs. -/
theorem assignHint_m (hs₀ : FrameStart s₀ ks) {t t' : SState} (h : AccInv K σ s₀ ks t t') (p : Place) (u : Term) :
    (if u.assignHinted then (match contentOf K φ p t with
      | some ((_, T, _, _), _) => T
      | none => .plain .err) else .plain .err : TyS).m =
    (if u.assignHinted then (match contentOf K φ p t' with
      | some ((_, T, _, _), _) => T
      | none => .plain .err) else .plain .err : TyS).m := by
  split
  · obtain ⟨hc, -⟩ := contentOf_corr φ hs₀ h p
    cases e1 : contentOf K φ p t with
    | none =>
      rw [e1] at hc
      cases e2 : contentOf K φ p t' with
      | none => rfl
      | some _ => rw [e2] at hc; exact hc.elim
    | some y =>
      rw [e1] at hc
      cases e2 : contentOf K φ p t' with
      | none => rw [e2] at hc; exact hc.elim
      | some y' =>
        rw [e2] at hc
        obtain ⟨⟨v, T, pos, steps⟩, u⟩ := y
        obtain ⟨⟨v', T', pos', steps'⟩, u'⟩ := y'
        obtain ⟨-, hT, -⟩ := hc
        dsimp only; rw [hT]
  · rfl

/-- A result label's content type, across the relation (`FrameInv.heldAll`: the label may have ended). -/
theorem labTyOk_corr {t t' : SState} (h : FrameInv K φ σ s₀ ks t t') {R R' : TyS}
    (hR : R = { R' with label := R'.label.map σ }) (hresD : ResDead t' R'.label) (M : TyM) :
    labTyOk t R.label M ↔ labTyOk t' R'.label M := by
  have hRl : R.label = R'.label.map σ := by rw [hR]
  rcases Option.eq_none_or_eq_some R'.label with hl0 | ⟨l, hl0⟩
  · rw [hRl, hl0]; exact ⟨fun _ _ e => (by cases e), fun _ _ e => (by cases e)⟩
  · rw [hRl, hl0]
    have e := (h.heldAll l (hresD l hl0).1).1
    constructor
    · intro hk l' hl'; cases hl'; rw [← e]; exact hk _ rfl
    · intro hk l' hl'; cases hl'; rw [e]; exact hk _ rfl

end

section
variable {K : RunCtx} {ρ : Assignment} {φ : Future} {σ : Nat → Nat} {s₀ : SState} {ks : List Nat}

/-- The frame property at a term, at two hints with the same type (`runT_hintM`). -/
theorem termFrame_hint {u : Term} (ih : TermFrame K ρ φ σ s₀ ks u) {T T' : TyS} (hm : T.m = T'.m) (tl : Bool)
    {s s' : SState} (h : FrameInv K φ σ s₀ ks s s') :
    FrameAgreeI K φ σ s₀ ks (runT K ρ φ tl T u s) (runT K ρ φ tl T' u s') := by
  rw [runT_hintM K ρ φ tl u T T' hm]; exact ih tl T' s s' h

/-- **The frame property's clause for an assignment** (the paper's row "A borrow; an assignment through a borrow; field
paths"): the right-hand side at the place's stored type, its label renamed in place (`assignHint_m`, `termFrame_hint`);
the strict test of the value and its label at the place's type on both sides or neither (`placeTy_corr`,
`labTyOk_corr`); the assignment's tail (`assignTail_agree`). -/
theorem runFrameI_assign (hs₀ : FrameStart s₀ ks) {p : Place} {u : Term} (hfu : Strict.Fund K ρ φ u)
    (ihu : TermFrame K ρ φ σ s₀ ks u) : TermFrame K ρ φ σ s₀ ks (.assign p u) := by
  intro tl hint s s' hI
  rw [runT]; dsimp only
  rw [scopeOf_corr hI.acc.rel]
  refine agreeI_erasedIf _ hI ?_
  refine agreeI_bind_eq2 (termFrame_hint ihu (assignHint_m hs₀ hI.acc p u) false hI)
    fun v R R' t t' hrun hrun' hR ht hres => ?_
  dsimp only
  obtain ⟨-, hlab, hlou, -⟩ := hfu false _ s t (v, R) hI.good hrun
  obtain ⟨-, hlab', hlou', -⟩ := hfu false _ s' t' (v, R') hI.good' hrun'
  rw [placeTy_corr hs₀ ht.acc p]
  by_cases htest : v ∈ₛ[K.dm.read] (placeTy K φ p t').m ∧ labTyOk t' R'.label (placeTy K φ p t').m
  · have htestI : v ∈ₛ[K.dm.read] (placeTy K φ p t').m ∧ labTyOk t R.label (placeTy K φ p t').m :=
      ⟨htest.1, (labTyOk_corr ht hR hres.2 _).2 htest.2⟩
    rw [if_pos htestI, if_pos htest]
    exact assignTail_agree hs₀ ht p v hR hres.1 hres.2 (by rw [placeTy_corr hs₀ ht.acc p]; exact htest.1)
      (by rw [placeTy_corr hs₀ ht.acc p]; exact htestI.2) htest.1 htest.2 hlab hlou hlab' hlou'
  · rw [if_neg (fun h' => htest ⟨h'.1, (labTyOk_corr ht hR hres.2 _).1 h'.2⟩), if_neg htest]; trivial

end

end Ochr.Meaning.Steps.Form.FrameEnd
