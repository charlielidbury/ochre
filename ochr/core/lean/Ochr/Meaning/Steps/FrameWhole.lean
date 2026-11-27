import Ochr.Meaning.Steps.FrameLet
import Ochr.Meaning.Strict.Struct
import Ochr.Meaning.Steps.ColumnBorrow

/-!
# The whole-state test across the frame relation: the paper's (O6) (lead35; docs/31 D223)

After a write or a borrow at a field path and D112's invalidation, the strict run tests `StateOk`: every binding holds an
open member of its type, every holder of its label's content type, at every typed future (`lentOk`). In place the test
reads the caller's frames, in the closure its frame 0 (the cells). The paper's (O6): the callee's frames are related, and
the rest is good on each side, the caller's frames in place and the cells in the closure; inside the clause, after the
write and before the test, the rest stays good although the callee's frame may not be, since it changes only by ends,
which substitute whole members (the third referee's T7).

`GoodOn P` is `SGood`'s two value clauses at the positions `P` picks. With `SStruct` (`SGood`'s other clauses, which
every step of the clause keeps) it is kept by an end, an access, a write away from `P`, D112's invalidation of places
away from `P`, and a borrow away from `P`.
-/

namespace Ochr.Meaning.Steps.Form.FrameEnd

open Ochr Ochr.Meaning Ochr.Meaning.Strict

/-- `SGood`'s value clauses at the positions `P` picks. -/
structure GoodOn (dm : DataModel) (Γ : List IndDecl) (φ : Future) (P : Pos → Prop) (s : SState) : Prop where
  bind : ∀ ψ, TypedF dm Γ φ s ψ → ∀ f i, P (.bind f i) → Pos.bind f i ∈ s.positions →
    GoodVal dm Γ (s.valAt (.bind f i) ψ) (s.tyAt (.bind f i)).m
  holder : ∀ ψ, TypedF dm Γ φ s ψ → ∀ p l, P p → s.shape p = some l → PMem dm Γ (s.valAt p ψ) (s.heldTy l)

section
variable {dm : DataModel} {Γ : List IndDecl} {φ : Future} {P : Pos → Prop}

theorem _root_.Ochr.Meaning.Strict.SGood.goodOn {s : SState} (hs : SGood dm Γ φ s) : GoodOn dm Γ φ P s :=
  ⟨fun ψ hψ f i _ hp => hs.bind ψ hψ f i hp, fun ψ hψ p l _ hl => hs.holder ψ hψ p l hl⟩

theorem _root_.Ochr.Meaning.Strict.SStruct.holderIndep {s : SState} (hs : SStruct dm s) {p : Pos} {l : Nat}
    (hl : s.shape p = some l) : Indep l (s.valAt p) := by
  obtain ⟨-, h2, hsa⟩ := hs.acyc
  refine (h2 p l (hsa p l hl).1 hl).indep ?_
  rintro (⟨-, hn⟩ | ⟨-, hlt⟩)
  · exact hn ((SState.live_iff s l).2 ⟨p, (hsa p l hl).1, hl⟩)
  · exact Nat.lt_irrefl l hlt

/-- **An end keeps the value clauses wherever they held** (`endAt_sgood`'s argument, position by position): every
position but the holder reads its old meaning at the future that gives the ended label the holder's content, which is a
whole member at every typed future by the strict end; the holder reads `⊥`. -/
theorem GoodOn.endAt {s : SState} {l : Nat} {r : Pos} (hS : SStruct dm s) (hs : GoodOn dm Γ φ P s)
    (hh : s.holderOf l = some r) (hend : EndOkF dm Γ φ s l) : GoodOn dm Γ φ P (s.endAt l r) := by
  have hr : s.shape r = some l := (SState.holderOf_spec hh).2
  have hlive : l ∈ s.liveLabels := (SState.live_iff s l).2 ⟨r, (SState.holderOf_spec hh).1, hr⟩
  have hTy : ∀ q, (s.endAt l r).tyAt q = s.tyAt q := fun q => by unfold SState.endAt; rw [tyAt_mapVals]; rfl
  have hHT : (s.endAt l r).heldTy = s.heldTy := rfl
  have key : ∀ ψ', TypedF dm Γ φ (s.endAt l r) ψ' → TypedF dm Γ φ s (ψ'.upd l (s.valAt r ψ')) := by
    rintro ψ' ⟨hag, hψ'⟩
    have hag' : ∀ y, y ∉ s.liveLabels → ψ' y = φ y := fun y hy =>
      hag y (fun h => hy (SState.endAt_live h))
    refine ⟨fun y hy => ?_, fun l' hl' => ?_⟩
    · have hne : y ≠ l := fun e => hy (e ▸ hlive)
      rw [Future.upd_other _ _ hne]; exact hag' y hy
    by_cases e : l' = l
    · subst e
      rw [Future.upd_same]
      have hm : s.heldMem l' ∈ₛ[dm.read] s.heldTy l' := hS.held l' hl'
      have ht : TypedF dm Γ φ s (ψ'.upd l' (s.heldMem l')) := by
        refine ⟨fun y hy => ?_, fun y hy => ?_⟩
        · have hne : y ≠ l' := fun e => hy (e ▸ hl')
          rw [Future.upd_other _ _ hne]; exact hag' y hy
        by_cases ey : y = l'
        · subst ey; rw [Future.upd_same]; exact hm
        · rw [Future.upd_other _ _ ey]
          have := hψ' y (SState.live_endAt hr hy ey); rwa [hHT] at this
      have := hend r hh _ ht
      rwa [hS.holderIndep hr ψ' (s.heldMem l')] at this
    · rw [Future.upd_other _ _ e]
      have := hψ' l' (SState.live_endAt hr hl' e); rwa [hHT] at this
  refine ⟨fun ψ' hψ' f i hP hpi => ?_, fun ψ' hψ' p l'' hP hl'' => ?_⟩
  · show GoodVal _ _ ((s.endAt l r).valAt _ ψ') ((s.endAt l r).tyAt _).m
    rw [hTy]
    have hp : Pos.bind f i ∈ s.positions := by rwa [SState.endAt_positions] at hpi
    rw [SState.endAt_valAt s l r _ hp]
    split
    · exact .inl (.moved _)
    · exact hs.bind _ (key ψ' hψ') f i hP hp
  · rw [SState.endAt_shape] at hl''
    simp only at hl''
    split at hl''
    · cases hl''
    · rename_i hpr
      have hp : p ∈ s.positions := (hS.acyc.2.2 p l'' hl'').1
      rw [SState.endAt_valAt s l r _ hp]
      dsimp only
      rw [if_neg hpr, hHT]
      exact hs.holder _ (key ψ' hψ') p l'' hP hl''

theorem GoodOn.endLabel {s : SState} (hS : SStruct dm s) (hs : GoodOn dm Γ φ P s) (l : Nat)
    (hend : EndOkF dm Γ φ s l) : GoodOn dm Γ φ P (s.endLabel l) := by
  cases h : s.holderOf l with
  | none => rw [SState.endLabel_of_none h]; exact hs
  | some r => rw [SState.endLabel_eq h]; exact hs.endAt hS h hend

theorem GoodOn.foldl_endLabel : ∀ (ls : List Nat) {s : SState}, SStruct dm s → GoodOn dm Γ φ P s →
    FoldOk SState.endLabel (EndOkF dm Γ φ) ls s → GoodOn dm Γ φ P (ls.foldl SState.endLabel s)
  | [], _, _, h, _ => h
  | l :: ls, _, hS, h, hok => GoodOn.foldl_endLabel ls (hS.endLabel l) (h.endLabel hS l hok.1) hok.2

/-- [Access] keeps the value clauses wherever they held, where every end it makes is strict. -/
theorem GoodOn.access {s : SState} (hS : SStruct dm s) (hs : GoodOn dm Γ φ P s) (p : Pos) (hit : List Step → Bool)
    (hok : AccessOkF dm Γ φ s p hit) : GoodOn dm Γ φ P (s.access p hit) := by
  have key : ∀ k, k ≤ s.liveLabels.length →
      SStruct dm ((List.range k).foldl (fun t _ => accRound p hit t) s) ∧
      GoodOn dm Γ φ P ((List.range k).foldl (fun t _ => accRound p hit t) s) := by
    intro k
    induction k with
    | zero => intro _; exact ⟨hS, hs⟩
    | succ k ih =>
      intro hk
      rw [List.range_succ, List.foldl_append]
      obtain ⟨h1, h2⟩ := ih (by omega)
      exact ⟨SStruct.foldl_endLabel _ h1, GoodOn.foldl_endLabel _ h1 h2 (hok k (by omega))⟩
  exact (key s.liveLabels.length (Nat.le_refl _)).2


/-- A write at a position away from `P` keeps the value clauses at `P`. -/
theorem GoodOn.setAt {s : SState} (hs : GoodOn dm Γ φ P s) {p : Pos} (hp : ¬ P p) (g : SVal) :
    GoodOn dm Γ φ P (s.setAt p g) := by
  refine ⟨fun ψ hψ f i hP hpi => ?_, fun ψ hψ q l hP hl => ?_⟩
  · rw [typedF_setAt] at hψ
    have hne : p ≠ .bind f i := fun e => hp (e ▸ hP)
    rw [SState.valAt_setAt_ne s p g _ hne, tyAt_setAt]
    exact hs.bind ψ hψ f i hP (by rwa [SState.positions_setAt] at hpi)
  · rw [typedF_setAt] at hψ
    rw [SState.shape_setAt] at hl
    have hne : p ≠ q := fun e => hp (e ▸ hP)
    rw [SState.valAt_setAt_ne s p g _ hne, heldTy_setAt]
    exact hs.holder ψ hψ q l hP hl

end

section
variable {K : RunCtx} {φ : Future} {P : Pos → Prop}

theorem GoodOn.setContent {s s' : SState} {pos : Pos} {steps : List Step} {v : Sem}
    (hs : GoodOn K.dm K.Γ φ P s) (hp : ¬ P pos) (h : setContent K φ pos steps v s = some (⟨⟩, s')) :
    GoodOn K.dm K.Γ φ P s' := by
  rw [setContent_eq K φ h]; exact hs.setAt hp _

theorem topIdx_envLe {s s' : SState} (h : EnvLe s s') : s'.topIdx = s.topIdx := by
  unfold SState.topIdx; rw [h.1]

/-- D112's invalidation of one place of the top frame keeps the value clauses away from the top frame. -/
theorem GoodOn.invalidateOne {T : Nat} {s : SState} (hS : SStruct K.dm s)
    (hs : GoodOn K.dm K.Γ φ (fun p => p.frameOf ≠ T) s) (hT : s.topIdx = T) (q : Place) (hok : InvalOneOk K φ s q) :
    SStruct K.dm (invalidateOne K φ s q) ∧ GoodOn K.dm K.Γ φ (fun p => p.frameOf ≠ T) (invalidateOne K φ s q) ∧
      (invalidateOne K φ s q).topIdx = T := by
  refine ⟨hS.invalidateOne q, ?_, ?_⟩
  · unfold Ochr.Meaning.invalidateOne
    cases hres : resolve s q with
    | none => exact hs
    | some ps =>
      obtain ⟨pos, steps⟩ := ps
      dsimp only
      have hpT : pos.frameOf = T := by rw [← hT]; exact (resolve_top hres).2
      have hok' : AccessOkF K.dm K.Γ φ s pos (dataHit steps) := by
        unfold InvalOneOk at hok; rw [hres] at hok; exact hok
      have hs₁ := hs.access hS pos (dataHit steps) hok'
      generalize s.access pos (dataHit steps) = s₁ at hs₁ ⊢
      cases hsc : Ochr.Meaning.setContent K φ pos steps .moved s₁ with
      | none => exact hs₁
      | some x =>
        obtain ⟨⟨⟩, s₂⟩ := x
        exact hs₁.setContent (fun h => h hpT) hsc
  · unfold Ochr.Meaning.invalidateOne
    split
    · rename_i pos steps _
      dsimp only
      have e1 := envLe_access s pos (dataHit steps)
      split
      · rename_i u s'' hsc
        obtain ⟨⟨⟩, _⟩ := u
        rw [setContent_eq K φ hsc, topIdx_envLe (envLe_setAt _ _ _), topIdx_envLe e1, hT]
      · rw [topIdx_envLe e1, hT]
    · exact hT

/-- D112's invalidation keeps the value clauses away from the top frame, where every end it makes is strict. -/
theorem GoodOn.invalidate {T : Nat} (p : Place) {s : SState} (hS : SStruct K.dm s)
    (hs : GoodOn K.dm K.Γ φ (fun p => p.frameOf ≠ T) s) (hT : s.topIdx = T) (hok : InvalidateOk K φ p s) :
    GoodOn K.dm K.Γ φ (fun p => p.frameOf ≠ T) (invalidate K φ p s) := by
  unfold Ochr.Meaning.invalidate
  unfold InvalidateOk at hok
  generalize K.D.invalidated (scopeOf s) p = qs at hok
  induction qs generalizing s with
  | nil => exact hs
  | cons q qs ih =>
    simp only [List.foldl_cons]
    obtain ⟨h1, h2, h3⟩ := GoodOn.invalidateOne hS hs hT q hok.1
    exact ih h1 h2 h3 hok.2

end

/-! ## The callee's frame's part of the test, across the frame relation -/

section
variable {K : RunCtx} {φ : Future} {σ : Nat → Nat} {s₀ : SState} {ks : List Nat} {t t' : SState}

/-- The value clauses at frame `T`, at one future. -/
def TopOk (K : RunCtx) (T : Nat) (s : SState) (ψ : Future) : Prop :=
  (∀ i, Pos.bind T i ∈ s.positions → GoodVal K.dm K.Γ (s.valAt (.bind T i) ψ) (s.tyAt (.bind T i)).m) ∧
  (∀ q l, q.frameOf = T → s.shape q = some l → PMem K.dm K.Γ (s.valAt q ψ) (s.heldTy l))

/-- **The whole-state test, split**: the frame `T` at every typed future, and the value clauses elsewhere. -/
theorem stateOk_split (T : Nat) (s : SState) :
    StateOk K φ s ↔ (∀ ψ, TypedFut K φ s ψ → TopOk K T s ψ) ∧ GoodOn K.dm K.Γ φ (fun p => p.frameOf ≠ T) s := by
  constructor
  · intro h
    refine ⟨fun ψ hψ => ⟨fun i hi => (h ψ hψ).1 T i hi, fun q l _ hl => (h ψ hψ).2 q l hl⟩,
      fun ψ hψ f i _ hp => (h ψ hψ).1 f i hp, fun ψ hψ q l _ hl => (h ψ hψ).2 q l hl⟩
  · rintro ⟨hT, hR⟩ ψ hψ
    refine ⟨fun f i hp => ?_, fun q l hl => ?_⟩
    · by_cases hf : f = T
      · subst hf; exact (hT ψ hψ).1 i hp
      · exact hR.bind ψ hψ f i (by simpa [Pos.frameOf] using hf) hp
    · by_cases hf : q.frameOf = T
      · exact (hT ψ hψ).2 q l hf hl
      · exact hR.holder ψ hψ q l hf hl

/-- The callee's frame's bindings correspond. -/
theorem top_bind_mem (hr : FrameRel σ s₀ ks t t') (i : Nat) :
    Pos.bind s₀.topIdx i ∈ t.positions ↔ Pos.bind 1 i ∈ t'.positions := by
  obtain ⟨F, F', hF, hF', hl, -⟩ := hr.top
  have hs : t.env[s₀.topIdx]? = some F := by rw [← topIdx_eq hr]; exact env_top t hF
  have hs' : t'.env[1]? = some F' := by have := env_top t' hF'; rwa [topIdx_cl hr] at this
  rw [SState.mem_positions, SState.mem_positions]
  simp only [SState.lookup, hs, hs', Option.bind_some, Option.isSome_map]
  simp [hl]

/-- A future typed in place gives one typed in the closure that agrees with it through the renaming on the closure's
live labels. -/
theorem typed_push (hr : FrameRel σ s₀ ks t t') (hsa : ShapeAt t) {ψ : Future} (hψ : TypedFut K φ t ψ) :
    ∃ ψ', TypedFut K φ t' ψ' ∧ ∀ l, t'.Live l → ψ' l = ψ (σ l) := by
  refine ⟨fun m => if m ∈ t'.liveLabels then ψ (σ m) else φ m, ⟨fun m hm => by simp only [if_neg hm],
    fun m hm => ?_⟩, fun l hl => by have hl' : l ∈ t'.liveLabels := hl; simp only [if_pos hl']⟩
  simp only [if_pos hm]
  rw [← (hr.held m hm).2]; exact hψ.2 _ (live_img hr hsa hm)

/-- A future typed in the closure gives one typed in place that agrees with it through the renaming on the closure's
live labels (the in-place records elsewhere: members, `HeldOk`). -/
theorem typed_pull (hr : FrameRel σ s₀ ks t t') (hsa : ShapeAt t) (hh : HeldOk K t) {ψ' : Future}
    (hψ' : TypedFut K φ t' ψ') : ∃ ψ, TypedFut K φ t ψ ∧ ∀ l, t'.Live l → ψ (σ l) = ψ' l := by
  open Classical in
  let ψ : Future := fun m => if hm : ∃ l', t'.Live l' ∧ σ l' = m then ψ' (Classical.choose hm)
    else if m ∈ t.liveLabels then t.heldMem m else φ m
  have hψσ : ∀ l', t'.Live l' → ψ (σ l') = ψ' l' := fun l' hl' => by
    have hm : ∃ l'', t'.Live l'' ∧ σ l'' = σ l' := ⟨l', hl', rfl⟩
    simp only [ψ, dif_pos hm]
    rw [hr.inj _ _ (Classical.choose_spec hm).2]
  refine ⟨ψ, ⟨fun m hm => ?_, fun m hm => ?_⟩, hψσ⟩
  · have : ¬ ∃ l', t'.Live l' ∧ σ l' = m := fun ⟨l', hl', e⟩ => hm (e ▸ live_img hr hsa hl')
    simp only [ψ, dif_neg this, if_neg hm]
  · by_cases hm' : ∃ l', t'.Live l' ∧ σ l' = m
    · obtain ⟨l', hl', rfl⟩ := hm'
      rw [hψσ l' hl', (hr.held l' hl').2]; exact hψ'.2 l' hl'
    · simp only [ψ, dif_neg hm', if_pos hm]; exact hh m hm


/-- The callee's frame read at agreeing futures: the same meaning. -/
theorem top_valAt_ag (hr : FrameRel σ s₀ ks t t') (hloc : ∀ p, Ochr.Meaning.FT (fun l => t'.Live l) (t'.valAt p))
    {p : Pos} (hp : p.frameOf = s₀.topIdx) {ψ ψ' : Future} (hag : ∀ l, t'.Live l → ψ (σ l) = ψ' l) :
    t.valAt p ψ = t'.valAt (upPos ks.length p) ψ' := by
  rw [top_valAt hr p hp]; exact hloc _ _ _ fun l hl => hag l hl

/-- **(O6) at the callee's frame**: its part of the whole-state test holds in place exactly when in the closure. The
positions correspond, with the same types and the same meanings at corresponding typed futures (`typed_push`,
`typed_pull`); a holder's content type is its label's, which corresponds (`FrameRel.held`). -/
theorem topOk_corr (hr : FrameRel σ s₀ ks t t') (hsa : ShapeAt t) (hsa' : ShapeAt t') (hh : HeldOk K t)
    (hloc : ∀ p, Ochr.Meaning.FT (fun l => t'.Live l) (t'.valAt p)) :
    (∀ ψ, TypedFut K φ t ψ → TopOk K s₀.topIdx t ψ) ↔ (∀ ψ', TypedFut K φ t' ψ' → TopOk K 1 t' ψ') := by
  have hty : ∀ i, (t.tyAt (.bind s₀.topIdx i)).m = (t'.tyAt (.bind 1 i)).m := fun i => by
    rw [tyAt_corr hr (p := .bind s₀.topIdx i) rfl]; rfl
  constructor
  · intro h ψ' hψ'
    obtain ⟨ψ, hψ, hag⟩ := typed_pull hr hsa hh hψ'
    have hT := h ψ hψ
    refine ⟨fun i hi => ?_, fun q l hq hl => ?_⟩
    · have := hT.1 i ((top_bind_mem hr i).2 hi)
      rwa [top_valAt_ag hr hloc (p := .bind s₀.topIdx i) rfl hag, hty] at this
    · obtain ⟨p, hpf, rfl⟩ := hr.clShape q l hl
      have hsh : t.shape p = some (σ l) := by rw [hr.topShape p hpf, hl]; rfl
      have hlv : t'.Live l := (SState.live_iff t' l).2 ⟨_, (hsa' _ l hl), hl⟩
      have := hT.2 p (σ l) hpf hsh
      rwa [top_valAt_ag hr hloc hpf hag, (hr.held l hlv).2] at this
  · intro h ψ hψ
    obtain ⟨ψ', hψ', hag⟩ := typed_push hr hsa hψ
    have hT := h ψ' hψ'
    have hag' : ∀ l, t'.Live l → ψ (σ l) = ψ' l := fun l hl => (hag l hl).symm
    refine ⟨fun i hi => ?_, fun q l hq hl => ?_⟩
    · have := hT.1 i ((top_bind_mem hr i).1 hi)
      rw [top_valAt_ag hr hloc (p := .bind s₀.topIdx i) rfl hag', hty]; exact this
    · have e := hr.topShape q hq
      rw [hl] at e
      cases hq' : t'.shape (upPos ks.length q) with
      | none => rw [hq'] at e; cases e
      | some l' =>
        rw [hq', Option.map_some, Option.some.injEq] at e
        subst e
        have hlv : t'.Live l' := (SState.live_iff t' l').2 ⟨_, (hsa' _ l' hq'), hq'⟩
        have := hT.2 _ l' (upPos_frameOf _ _) hq'
        rw [top_valAt_ag hr hloc hq hag', (hr.held l' hlv).2]; exact this

end

/-! ## A borrow keeps the value clauses away from the top frame -/

section
open SStateB
variable {K : RunCtx} {φ : Future}

/-- **A borrow's park keeps the value clauses away from the top frame**: the lender (in the top frame) is written, the
fresh label is parked at a new temporary of the top frame and given its records; elsewhere every position keeps its
meaning, which reads no fresh label, and its holdership. -/
theorem goodOn_borrow_park {s₁ : SState} (hs₁ : SGood K.dm K.Γ φ s₁) (hne : s₁.env ≠ []) {pos : Pos}
    (hpT : pos.frameOf = s₁.topIdx) (G : SVal) (v : Sem) (Tm : TyM) (xs : List Site) :
    GoodOn K.dm K.Γ φ (fun q => q.frameOf ≠ s₁.topIdx) (((((s₁.freshLoan.2.setAt pos G).pushTempShaped
      (fun _ => v) s₁.nextLoan).setLent s₁.nextLoan xs).setHeldTy s₁.nextLoan Tm).setHeldMem s₁.nextLoan v) := by
  have hsa₁ := hs₁.acyc.2.2
  have hlnew : s₁.nextLoan ∉ s₁.liveLabels := fun h => Nat.lt_irrefl _ (hs₁.live_lt h)
  have hF : s₁.freshLoan.2 = { s₁ with nextLoan := s₁.nextLoan + 1 } := rfl
  rw [hF]
  generalize hS₃ : ({ s₁ with nextLoan := s₁.nextLoan + 1 } : SState).setAt pos G = S₃
  have h3T : S₃.topIdx = s₁.topIdx := by rw [← hS₃, topIdx_setAt]; rfl
  have h3val : ∀ q, q.frameOf ≠ s₁.topIdx → S₃.valAt q = s₁.valAt q := fun q hq => by
    rw [← hS₃, SState.valAt_setAt_ne _ _ _ _ (fun e => hq (by rw [← e]; exact hpT))]; rfl
  have h3ty : ∀ q, S₃.tyAt q = s₁.tyAt q := fun q => by rw [← hS₃, tyAt_setAt]; rfl
  have h3sh : S₃.shape = s₁.shape := by rw [← hS₃, SState.shape_setAt]
  have h3pos : S₃.positions = s₁.positions := by rw [← hS₃, SState.positions_setAt]; rfl
  have h3HT : S₃.heldTy = s₁.heldTy := by rw [← hS₃, heldTy_setAt]
  obtain ⟨fr, hfr⟩ : ∃ fr, S₃.env.getLast? = some fr := by
    cases h : S₃.env.getLast? with
    | some fr => exact ⟨fr, rfl⟩
    | none =>
      have : S₃.env = [] := List.getLast?_eq_none_iff.mp h
      rw [← hS₃] at this; cases pos <;> simp [SState.setAt] at this <;> exact absurd this hne
  have hnt : ∀ q, q.frameOf ≠ s₁.topIdx → q ≠ newTemp S₃ fr := fun q hq e => by
    rw [e] at hq; exact hq (by simp [newTemp, Pos.frameOf, h3T])
  generalize hl : s₁.nextLoan = l at hlnew
  generalize hS : ((((S₃.pushTempShaped (fun _ => v) l).setLent l xs).setHeldTy l Tm).setHeldMem l v) = S
  have hSval : ∀ q, q.frameOf ≠ s₁.topIdx → S.valAt q = s₁.valAt q := fun q hq => by
    rw [← hS]
    show (S₃.pushTempShaped (fun _ => v) l).valAt q = _
    rw [valAt_pushTempShaped' _ _ _ hfr, if_neg (hnt q hq), h3val q hq]
  have hSty : ∀ q, S.tyAt q = s₁.tyAt q := fun q => by
    rw [← hS]; show (S₃.pushTempShaped (fun _ => v) l).tyAt q = _; rw [tyAt_pushTempShaped, h3ty]
  have hSsh : ∀ q, S.shape q = if q = newTemp S₃ fr then some l else s₁.shape q := fun q => by
    rw [← hS]; show (S₃.pushTempShaped (fun _ => v) l).shape q = _; rw [shape_pushTempShaped _ _ _ hfr, h3sh]
  have hSpos : ∀ q, q ∈ S.positions ↔ q = newTemp S₃ fr ∨ q ∈ s₁.positions := fun q => by
    rw [← hS]; show q ∈ (S₃.pushTempShaped (fun _ => v) l).positions ↔ _
    rw [mem_positions_pushTempShaped _ _ _ hfr, h3pos]
  have hSHT : ∀ y, S.heldTy y = if y = l then Tm else s₁.heldTy y := fun y => by
    rw [← hS]; simp only [SState.setHeldMem_heldTy]; show (if y = l then Tm else _) = _
    rw [show ((S₃.pushTempShaped (fun _ => v) l).setLent l xs).heldTy = (S₃.pushTempShaped (fun _ => v) l).heldTy
      from rfl, heldTy_pushTempShaped, h3HT]
  have hlive : ∀ y, y ∈ S.liveLabels ↔ y ∈ s₁.liveLabels ∨ y = l := fun y => by
    show S.Live y ↔ s₁.Live y ∨ y = l
    rw [SState.live_iff, SState.live_iff]
    constructor
    · rintro ⟨q, hq, hsh⟩
      rw [hSsh] at hsh
      split at hsh
      · exact .inr (Option.some.inj hsh).symm
      · rename_i hqn
        exact .inl ⟨q, ((hSpos q).1 hq).resolve_left hqn, hsh⟩
    · rintro (⟨q, hq, hsh⟩ | rfl)
      · have hqn : q ≠ newTemp S₃ fr := fun e => newTemp_not_mem S₃ hfr (by rw [h3pos, ← e]; exact hq)
        exact ⟨q, (hSpos q).2 (.inr hq), by rw [hSsh, if_neg hqn, hsh]⟩
      · exact ⟨newTemp S₃ fr, (hSpos _).2 (.inl rfl), by rw [hSsh, if_pos rfl]⟩
  have key : ∀ ψ, TypedF K.dm K.Γ φ S ψ → TypedF K.dm K.Γ φ s₁ (ψ.upd l (φ l)) := by
    rintro ψ ⟨hag, hψ⟩
    refine ⟨fun y hy => ?_, fun y hy => ?_⟩
    · by_cases e : y = l
      · subst e; rw [Future.upd_same]
      · rw [Future.upd_other _ _ e]
        exact hag y fun h => ((hlive y).1 h).elim hy e
    · have e : y ≠ l := fun e => hlnew (e ▸ hy)
      rw [Future.upd_other _ _ e]
      have := hψ y ((hlive y).2 (.inl hy)); rwa [hSHT, if_neg e] at this
  have hind : ∀ q ψ, s₁.valAt q (ψ.upd l (φ l)) = s₁.valAt q ψ := fun q ψ =>
    hs₁.indep_fresh q (by omega) ψ (φ l)
  refine ⟨fun ψ hψ f i hP hpi => ?_, fun ψ hψ q m hP hm => ?_⟩
  · rw [hSval _ hP, hSty, ← hind]
    have hp : Pos.bind f i ∈ s₁.positions := ((hSpos _).1 hpi).resolve_left (hnt _ hP)
    exact hs₁.bind _ (key ψ hψ) f i hp
  · rw [hSsh, if_neg (hnt q hP)] at hm
    have hml : m ≠ l := fun e => hlnew (e ▸ (SState.live_iff s₁ m).2 ⟨q, (hsa₁ q m hm).1, hm⟩)
    rw [hSval _ hP, hSHT, if_neg hml, ← hind]
    exact hs₁.holder _ (key ψ hψ) q m hm


/-- **A borrow keeps the structural part, and the value clauses away from the top frame** (the content's access, its
ends strict by the content test; then the park). -/
theorem borrowPlace_goodOn {p : Place} {s s₁ : SState} {r : Res} (hs : SGood K.dm K.Γ φ s)
    (hco : ContentOk K φ p s) (h : borrowPlace K φ p s = some (r, s₁)) (hm : r.1 ∈ₛ[K.dm.read] r.2.m) :
    SStruct K.dm s₁ ∧ GoodOn K.dm K.Γ φ (fun q => q.frameOf ≠ s.topIdx) s₁ ∧ s₁.topIdx = s.topIdx := by
  have hrinv := (borrowPlace_rinv K φ (fun _ => True) h hs.acyc).1
  have hfr : s₁.ReadsBelow := by obtain ⟨v₀, T₀⟩ := r; exact borrowPlace_readsBelow K φ p s hs.fresh h
  have hE : EnvLe s s₁ := borrowPlace_envLe K φ h
  have hb := h
  unfold borrowPlace at hb
  simp only [Bind.bind, Option.bind_eq_some_iff] at hb
  obtain ⟨⟨⟨v, T, pos, steps⟩, s₂⟩, h1, hb⟩ := hb
  obtain ⟨T', hres, rfl, -, -⟩ := contentOf_view h1
  dsimp only at hb
  by_cases hw : v.whole
  rotate_left
  · rw [if_pos hw] at hb; cases hb
  rw [if_neg (fun hn => hn hw)] at hb
  simp only [Option.some.injEq, Prod.mk.injEq] at hb
  obtain ⟨rfl, rfl⟩ := hb
  have hsa := access_sgood hs pos (dataHit steps) (contentOk_access hco hres)
  have hp : pos ∈ (s.access pos (dataHit steps)).positions := by rw [access_positions]; exact resolve_mem hres
  refine ⟨sstruct_borrow_park hsa hp _ hm _ hrinv hfr, ?_, topIdx_envLe hE⟩
  have hT : (s.access pos (dataHit steps)).topIdx = s.topIdx := topIdx_envLe (envLe_access _ _ _)
  have hpT : pos.frameOf = (s.access pos (dataHit steps)).topIdx := by rw [hT]; exact (resolve_top hres).2
  have := goodOn_borrow_park hsa (env_ne_of_mem hp) hpT
    (fun φ' => (Sem.updAt K.dm K.Γ ((s.access pos (dataHit steps)).freshLoan.2.tyAt pos) (fun _ => φ' (s.access pos (dataHit steps)).nextLoan) steps
      ((s.access pos (dataHit steps)).freshLoan.2.valAt pos φ')).getD .err) v T.m [⟨pos, steps, false⟩]
  rw [hT] at this
  exact this


/-- **A write below a root keeps the structural part, and the value clauses away from the top frame** (its access, its
ends strict by the assignment's test; then the write, at the top frame; no old borrow ends and no label is held, the
path being below a root). -/
theorem assignAt_goodOn {p : Place} {v : Sem} {lab : Option Nat} {s s₁ : SState} {r : Res}
    (hS : SStruct K.dm s) (hg : GoodOn K.dm K.Γ φ (fun q => q.frameOf ≠ s.topIdx) s) (hok : AssignOk K φ p s)
    (h : assignAt K φ p v lab s = some (r, s₁)) {pos : Pos} {steps : List Step}
    (hres : resolve s p = some (pos, steps)) (hst : steps ≠ []) :
    SStruct K.dm s₁ ∧ GoodOn K.dm K.Γ φ (fun q => q.frameOf ≠ s.topIdx) s₁ ∧ s₁.topIdx = s.topIdx := by
  have hse : steps.isEmpty = false := by cases steps with | nil => exact absurd rfl hst | cons _ _ => rfl
  unfold AssignOk at hok
  rw [hres] at hok
  have hacc : AccessOkF K.dm K.Γ φ s pos (dataHit steps) := hok.1 (by rw [hse]; rfl)
  unfold assignAt at h
  rw [hres] at h
  simp only [hse, Bool.false_and, Bool.false_eq_true, if_false] at h
  have hpT : pos.frameOf = s.topIdx := (resolve_top hres).2
  have hT₁ : (s.access pos (dataHit steps)).topIdx = s.topIdx := topIdx_envLe (envLe_access _ _ _)
  cases hsc : Ochr.Meaning.setContent K φ pos steps v (s.access pos (dataHit steps)) with
  | none => rw [hsc] at h; cases h
  | some x =>
    obtain ⟨⟨⟩, s₂⟩ := x
    rw [hsc] at h
    have e : s₁ = s₂ := by
      cases lab with
      | none => simp only [Option.some.injEq, Prod.mk.injEq] at h; exact h.2.symm
      | some l =>
        cases steps with
        | nil => exact absurd rfl hst
        | cons _ _ => simp only [Option.some.injEq, Prod.mk.injEq] at h; exact h.2.symm
    subst e
    refine ⟨(hS.access pos (dataHit steps)).setContent hsc, (hg.access hS pos (dataHit steps) hacc).setContent
      (fun h => h hpT) hsc, ?_⟩
    rw [setContent_eq K φ hsc, topIdx_envLe (envLe_setAt _ _ _), hT₁]

end

/-! ## (O6) -/

section
variable {K : RunCtx} {φ : Future} {σ : Nat → Nat} {s₀ : SState} {ks : List Nat} {t t' : SState}

/-- **(O6) the whole-state test** (the paper's `<sec-frame>`, (O6)): in place exactly when in the closure, where the
rest of each state is good (in place the caller's frames, in the closure its frame 0): the callee's frames correspond
(`topOk_corr`). -/
theorem stateOk_corr (hr : FrameRel σ s₀ ks t t') (hsa : ShapeAt t) (hsa' : ShapeAt t') (hh : HeldOk K t)
    (hloc : ∀ p, Ochr.Meaning.FT (fun l => t'.Live l) (t'.valAt p))
    (hR : GoodOn K.dm K.Γ φ (fun q => q.frameOf ≠ s₀.topIdx) t) (hR' : GoodOn K.dm K.Γ φ (fun q => q.frameOf ≠ 1) t') :
    StateOk K φ t ↔ StateOk K φ t' := by
  rw [stateOk_split s₀.topIdx t, stateOk_split 1 t']
  have e := topOk_corr (φ := φ) hr hsa hsa' hh hloc
  exact ⟨fun ⟨a, _⟩ => ⟨e.1 a, hR'⟩, fun ⟨a, _⟩ => ⟨e.2 a, hR⟩⟩

/-- **(O6) at a place** (`lentOk`): at a root or through `*` both pass; below, the whole-state test (`stateOk_corr`). -/
theorem lentOk_corr (hr : FrameRel σ s₀ ks t t') (hsa : ShapeAt t) (hsa' : ShapeAt t') (hh : HeldOk K t)
    (hloc : ∀ p, Ochr.Meaning.FT (fun l => t'.Live l) (t'.valAt p))
    (hR : GoodOn K.dm K.Γ φ (fun q => q.frameOf ≠ s₀.topIdx) t) (hR' : GoodOn K.dm K.Γ φ (fun q => q.frameOf ≠ 1) t')
    (p : Place) : lentOk K φ p t ↔ lentOk K φ p t' := by
  unfold lentOk
  rw [(resolve_corr hr p).1]
  cases resolve t p with
  | none => exact Iff.rfl
  | some x => exact or_congr Iff.rfl (or_congr Iff.rfl (stateOk_corr hr hsa hsa' hh hloc hR hR'))

end

end Ochr.Meaning.Steps.Form.FrameEnd
