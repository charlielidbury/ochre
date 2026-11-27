import Ochr.Meaning.Steps.FrameAccess

/-!
# The frame property's state operations against the frame relation (lead33; docs/31 D216)

The paper's (O5) to (O8) (`18-principles`, `<sec-frame-proof>`): a write, a fresh label, pushes and drops, each made at
corresponding places of the callee's frame on the two sides. Most of them change only the top frame (the callee's frame in
place, frame 1 in the closure), and `FrameRel` compares the rest without reading the top frame's values; so one lemma
carries every such change (`frameRel_modTop`): if the two top frames stay related (`TopRel`), so do the states. The
operations that also change the shape (a borrow parked or bound, a holder moved, a binding dropped) add their own clauses.
-/

namespace Ochr.Meaning.Steps.Form.FrameEnd

open Ochr Ochr.Meaning

/-! ## The top frames -/

/-- **The two top frames are related** (`FrameRel.top`'s body): the same bindings, renamed, and the same temporaries. -/
def TopRel (σ : Nat → Nat) (F F' : SFrame) : Prop :=
  F.binds.length = F'.binds.length ∧
    (∀ (i : Nat) b b', F.binds[i]? = some b → F'.binds[i]? = some b' → BindRen σ b b') ∧
    F'.temps.length = F.temps.length ∧
    ∀ (j : Nat) v, F.temps[j]? = some v → ∃ v', F'.temps[j]? = some v' ∧ ∀ ψ, v ψ = v' (renF σ ψ)

/-- A change of the top frame alone. -/
def modTop (t : SState) (g : SFrame → SFrame) : SState := { t with env := t.env.modify t.topIdx g }

section
variable {σ : Nat → Nat} {s₀ : SState} {ks : List Nat} {s s' : SState}

@[simp] theorem modTop_length (t : SState) (g : SFrame → SFrame) : (modTop t g).env.length = t.env.length :=
  List.length_modify _ _ _

@[simp] theorem modTop_topIdx (t : SState) (g : SFrame → SFrame) : (modTop t g).topIdx = t.topIdx := by
  unfold SState.topIdx; rw [modTop_length]

theorem modTop_getLast? (t : SState) (g : SFrame → SFrame) : (modTop t g).env.getLast? = t.env.getLast?.map g := by
  rw [List.getLast?_eq_getElem?, List.getLast?_eq_getElem?, modTop_length]
  unfold modTop SState.topIdx
  rw [List.getElem?_modify]
  cases t.env[t.env.length - 1]? <;> simp

theorem modTop_env_ne (t : SState) (g : SFrame → SFrame) {f : Nat} (hf : f ≠ t.topIdx) :
    (modTop t g).env[f]? = t.env[f]? := by
  unfold modTop; rw [List.getElem?_modify]
  cases t.env[f]? <;> simp [Ne.symm hf]

theorem modTop_valAt_ne (t : SState) (g : SFrame → SFrame) {p : Pos} (hp : p.frameOf ≠ t.topIdx) :
    (modTop t g).valAt p = t.valAt p := by
  cases p with
  | bind f i => simp only [SState.valAt]; rw [modTop_env_ne t g (f := f) hp]
  | temp f i => simp only [SState.valAt]; rw [modTop_env_ne t g (f := f) hp]

theorem modTop_headD (t : SState) (g : SFrame → SFrame) (h : t.topIdx ≠ 0) : (modTop t g).env.headD {} = t.env.headD {} := by
  have := modTop_env_ne t g (f := 0) (Ne.symm h)
  cases e : t.env with
  | nil => simp [modTop, e]
  | cons a l =>
    cases e' : (modTop t g).env with
    | nil => have := modTop_length t g; rw [e, e'] at this; simp at this
    | cons a' l' => rw [e, e'] at this; simp at this; simp [this]

theorem topIdx_cl (hr : FrameRel σ s₀ ks s s') : s'.topIdx = 1 := by unfold SState.topIdx; rw [hr.frames.2]

theorem top_rel (hr : FrameRel σ s₀ ks s s') : ∃ F F', s.env.getLast? = some F ∧ s'.env.getLast? = some F' ∧ TopRel σ F F' :=
  hr.top

/-- **A change of the top frames alone keeps the relation**, if the frames stay related and the closure gains no live
label (a pushed position holds nothing: shape entries are at positions). -/
theorem frameRel_modTop (hr : FrameRel σ s₀ ks s s') {g g' : SFrame → SFrame}
    (hg : ∀ F F', TopRel σ F F' → TopRel σ (g F) (g' F')) (hlive : ∀ l, (modTop s' g').Live l → s'.Live l) :
    FrameRel σ s₀ ks (modTop s g) (modTop s' g') where
  inj := hr.inj
  fresh := hr.fresh
  frames := by simp only [modTop_length]; exact hr.frames
  lowerSkel := fun f hf => by
    rw [modTop_env_ne s g (by rw [topIdx_eq hr]; omega)]; exact hr.lowerSkel f hf
  lowerVal := fun p hp ψ => by
    rw [modTop_valAt_ne s g (by rw [topIdx_eq hr]; omega)]
    unfold cellsOf; rw [modTop_headD s' g' (by rw [topIdx_cl hr]; omega)]
    exact hr.lowerVal p hp ψ
  lowerShape := hr.lowerShape
  top := by
    obtain ⟨F, F', hF, hF', ht⟩ := top_rel hr
    exact ⟨g F, g' F', by rw [modTop_getLast?, hF]; rfl, by rw [modTop_getLast?, hF']; rfl, hg F F' ht⟩
  topShape := hr.topShape
  clShape := hr.clShape
  held := fun l hl => hr.held l (hlive l hl)
  lentTop := hr.lentTop
  lentImg := hr.lentImg
  lentCl := hr.lentCl
  lentCaller := hr.lentCaller
  topLabels := fun l hl => hr.topLabels l (hlive l hl)

end

/-! ## The top-frame operations -/

section
variable {σ : Nat → Nat} {s₀ : SState} {ks : List Nat} {s s' : SState}

theorem TopRel.setBind {F F' : SFrame} (h : TopRel σ F F') (i : Nat) {v v' : SVal} (hv : ∀ ψ, v ψ = v' (renF σ ψ)) :
    TopRel σ { F with binds := F.binds.modify i fun b => { b with val := v } }
      { F' with binds := F'.binds.modify i fun b => { b with val := v' } } := by
  obtain ⟨hl, hb, ht, htv⟩ := h
  refine ⟨by simp [hl], fun j b b' e e' => ?_, ht, htv⟩
  simp only [List.getElem?_modify] at e e'
  cases h1 : F.binds[j]? with
  | none => rw [h1] at e; cases e
  | some b0 =>
    cases h2 : F'.binds[j]? with
    | none => rw [h2] at e'; cases e'
    | some b0' =>
      rw [h1] at e; rw [h2] at e'
      simp only [Option.map_eq_map, Option.map_some, Option.some.injEq] at e e'
      have hr := hb j b0 b0' h1 h2
      subst e e'
      by_cases hij : i = j
      · simp only [if_pos hij]; exact ⟨hr.1, hr.2.1, hr.2.2.1, hv⟩
      · simp only [if_neg hij]; exact hr

theorem TopRel.setTemp {F F' : SFrame} (h : TopRel σ F F') (j : Nat) {v v' : SVal} (hv : ∀ ψ, v ψ = v' (renF σ ψ)) :
    TopRel σ { F with temps := F.temps.set j v } { F' with temps := F'.temps.set j v' } := by
  obtain ⟨hl, hb, ht, htv⟩ := h
  refine ⟨hl, hb, by simp [ht], fun k w e => ?_⟩
  simp only [List.getElem?_set] at e ⊢
  by_cases hjk : j = k
  · subst hjk
    simp only [if_true] at e ⊢
    split at e
    · rename_i hlt; cases e; exact ⟨v', by rw [if_pos (by omega)], hv⟩
    · cases e
  · simp only [if_neg hjk] at e ⊢; exact htv k w e

theorem TopRel.pushTemp {F F' : SFrame} (h : TopRel σ F F') {v v' : SVal} (hv : ∀ ψ, v ψ = v' (renF σ ψ)) :
    TopRel σ { F with temps := F.temps ++ [v] } { F' with temps := F'.temps ++ [v'] } := by
  obtain ⟨hl, hb, ht, htv⟩ := h
  refine ⟨hl, hb, by simp [ht], fun k w e => ?_⟩
  simp only at e ⊢
  by_cases hk : k < F.temps.length
  · rw [List.getElem?_append_left hk] at e
    obtain ⟨w', e', hw⟩ := htv k w e
    exact ⟨w', by rw [List.getElem?_append_left (by omega)]; exact e', hw⟩
  · rw [List.getElem?_append_right (by omega)] at e
    have hk' : k = F.temps.length := by
      cases e' : k - F.temps.length with
      | zero => omega
      | succ n => rw [e'] at e; simp at e
    subst hk'
    simp only [Nat.sub_self, List.getElem?_cons_zero, Option.some.injEq] at e
    subst e
    exact ⟨v', by rw [List.getElem?_append_right (by omega), ← ht, Nat.sub_self]; rfl, hv⟩

theorem TopRel.pushBind {F F' : SFrame} (h : TopRel σ F F') {b b' : SBinding} (hb' : BindRen σ b b') :
    TopRel σ { F with binds := F.binds ++ [b] } { F' with binds := F'.binds ++ [b'] } := by
  obtain ⟨hl, hb, ht, htv⟩ := h
  refine ⟨by simp [hl], fun i c c' e e' => ?_, ht, htv⟩
  simp only at e e'
  by_cases hi : i < F.binds.length
  · rw [List.getElem?_append_left hi] at e
    rw [List.getElem?_append_left (by omega)] at e'
    exact hb i c c' e e'
  · rw [List.getElem?_append_right (by omega)] at e
    rw [List.getElem?_append_right (by omega), ← hl] at e'
    cases e1 : i - F.binds.length with
    | zero => rw [e1] at e e'; simp at e e'; subst e e'; exact hb'
    | succ n => rw [e1] at e; simp at e

theorem TopRel.dropLastBind {F F' : SFrame} (h : TopRel σ F F') :
    TopRel σ { F with binds := F.binds.dropLast } { F' with binds := F'.binds.dropLast } := by
  obtain ⟨hl, hb, ht, htv⟩ := h
  refine ⟨by simp [hl], fun i c c' e e' => ?_, ht, htv⟩
  simp only [List.getElem?_dropLast] at e e'
  rw [← hl] at e'
  split at e
  · rename_i hi; rw [if_pos hi] at e'; exact hb i c c' e e'
  · cases e

/-- A closure with shape entries at its positions gains no live label by a change of its top frame. -/
theorem live_modTop {t : SState} (hsa : ShapeAt t) (g : SFrame → SFrame) {l : Nat} (h : (modTop t g).Live l) : t.Live l := by
  obtain ⟨p, -, hp⟩ := (SState.live_iff _ l).1 h
  exact (SState.live_iff t l).2 ⟨p, hsa p l hp, hp⟩

theorem setAt_bind_modTop (t : SState) {f i : Nat} (hf : f = t.topIdx) (v : SVal) :
    t.setAt (.bind f i) v = modTop t fun fr => { fr with binds := fr.binds.modify i fun b => { b with val := v } } := by
  subst hf; rfl

theorem setAt_temp_modTop (t : SState) {f i : Nat} (hf : f = t.topIdx) (v : SVal) :
    t.setAt (.temp f i) v = modTop t fun fr => { fr with temps := fr.temps.set i v } := by
  subst hf; rfl

theorem pushTemp_modTop (t : SState) (v : SVal) :
    t.pushTemp v = modTop t fun fr => { fr with temps := fr.temps ++ [v] } := rfl

theorem pushBind_modTop (t : SState) (b : SBinding) :
    t.pushBind b = modTop t fun fr => { fr with binds := fr.binds ++ [b] } := rfl

/-- **(O5)'s write, as values**: setting corresponding positions of the callee's frame to values related through the
renaming keeps the relation. -/
theorem frameRel_setAt (hr : FrameRel σ s₀ ks s s') (hsa' : ShapeAt s') {p : Pos} (hp : p.frameOf = s₀.topIdx)
    {v v' : SVal} (hv : ∀ ψ, v ψ = v' (renF σ ψ)) :
    FrameRel σ s₀ ks (s.setAt p v) (s'.setAt (upPos ks.length p) v') := by
  have ht : p.frameOf = s.topIdx := by rw [topIdx_eq hr]; exact hp
  cases p with
  | bind f i =>
    rw [setAt_bind_modTop s (f := f) ht, show upPos ks.length (.bind f i) = .bind 1 i from rfl,
      setAt_bind_modTop s' (f := 1) (topIdx_cl hr).symm]
    exact frameRel_modTop hr (fun F F' h => h.setBind i hv) fun l => live_modTop hsa' _
  | temp f i =>
    rw [setAt_temp_modTop s (f := f) ht, show upPos ks.length (.temp f i) = .temp 1 i from rfl,
      setAt_temp_modTop s' (f := 1) (topIdx_cl hr).symm]
    exact frameRel_modTop hr (fun F F' h => h.setTemp i hv) fun l => live_modTop hsa' _

/-- **(O8)'s push of a temporary** (no holder recorded): related values pushed on the two top frames. -/
theorem frameRel_pushTemp (hr : FrameRel σ s₀ ks s s') (hsa' : ShapeAt s') {v v' : SVal}
    (hv : ∀ ψ, v ψ = v' (renF σ ψ)) : FrameRel σ s₀ ks (s.pushTemp v) (s'.pushTemp v') := by
  rw [pushTemp_modTop, pushTemp_modTop]
  exact frameRel_modTop hr (fun F F' h => h.pushTemp hv) fun l => live_modTop hsa' _

/-- **(O8)'s push of a binding** (no holder recorded): related bindings pushed on the two top frames. -/
theorem frameRel_pushBind (hr : FrameRel σ s₀ ks s s') (hsa' : ShapeAt s') {b b' : SBinding}
    (hb : BindRen σ b b') : FrameRel σ s₀ ks (s.pushBind b) (s'.pushBind b') := by
  rw [pushBind_modTop, pushBind_modTop]
  exact frameRel_modTop hr (fun F F' h => h.pushBind hb) fun l => live_modTop hsa' _

end

/-! ## A fresh label, and a borrow parked in a temporary -/

section
variable {σ : Nat → Nat} {s₀ : SState} {ks : List Nat} {s s' : SState}

/-- **(O7) a fresh label**: the next labels correspond, and the relation is kept. -/
theorem frameRel_freshLoan (hr : FrameRel σ s₀ ks s s') :
    σ s'.freshLoan.1 = s.freshLoan.1 ∧ FrameRel σ s₀ ks s.freshLoan.2 s'.freshLoan.2 :=
  ⟨by have := hr.fresh 0; simpa [SState.freshLoan] using this,
    { hr with fresh := fun j => (by
        have := hr.fresh (1 + j)
        rw [← Nat.add_assoc, ← Nat.add_assoc] at this; exact this) }⟩

/-- A borrow parked in a fresh temporary of the top frame, lent at the sites `xs`, with its content type and record:
`borrowPlace`'s and `callOfL`'s last steps. -/
noncomputable def park (t : SState) (v : SVal) (l : Nat) (xs : List Site) (T : TyM) (m : Sem) : SState :=
  (((t.pushTempShaped v l).setLent l xs).setHeldTy l T).setHeldMem l m

/-- A site one frame up (the closure's frame for an in-place position of the callee's frame). -/
def upSite (c : Nat) (x : Site) : Site := { x with pos := upPos c x.pos }

theorem pushTempShaped_eq (t : SState) (v : SVal) (l : Nat) {F : SFrame} (hF : t.env.getLast? = some F) :
    t.pushTempShaped v l = { t.pushTemp v with
      shape := fun p => if p = .temp t.topIdx F.temps.length then some l else t.shape p } := by
  unfold SState.pushTempShaped
  have h1 : (t.pushTemp v).env.getLast? = some { F with temps := F.temps ++ [v] } := by
    rw [pushTemp_modTop, modTop_getLast?, hF]; rfl
  have h2 : (t.pushTemp v).topIdx = t.topIdx := by rw [pushTemp_modTop, modTop_topIdx]
  simp only [h1, h2, List.length_append, List.length_singleton, Nat.add_sub_cancel]
  rfl

theorem park_eq (t : SState) (v : SVal) (l : Nat) (xs : List Site) (T : TyM) (m : Sem) {F : SFrame}
    (hF : t.env.getLast? = some F) :
    park t v l xs T m = { t.pushTemp v with
      shape := fun p => if p = .temp t.topIdx F.temps.length then some l else t.shape p,
      lent := fun n => if n = l then xs else t.lent n,
      heldTy := fun n => if n = l then T else t.heldTy n,
      heldMem := fun n => if n = l then m else t.heldMem n } := by
  unfold park; rw [pushTempShaped_eq t v l hF]; rfl

/-- **(O8)'s push of a borrow, with (O7)'s fresh label**: a value parked in place at the image of a closure label held
nowhere, lent at corresponding sites of the callee's frame, with the same content type and record. -/
theorem frameRel_park (hr : FrameRel σ s₀ ks s s') (hsa' : ShapeAt s') {v v' : SVal} (hv : ∀ ψ, v ψ = v' (renF σ ψ))
    {l : Nat} (hnot : ∀ p, s.shape p ≠ some (σ l)) (hnot' : ∀ p, s'.shape p ≠ some l)
    {xs : List Site} (hxs : ∀ x ∈ xs, x.pos.frameOf = s₀.topIdx) (T : TyM) (m : Sem)
    (htop : σ l ∈ ks ∨ s₀.nextLoan ≤ σ l) :
    FrameRel σ s₀ ks (park s v (σ l) xs T m) (park s' v' l (xs.map (upSite ks.length)) T m) := by
  obtain ⟨F, F', hF, hF', ht⟩ := top_rel hr
  have hpush := frameRel_pushTemp hr hsa' hv
  have htI : s.topIdx = s₀.topIdx := topIdx_eq hr
  have htC : s'.topIdx = 1 := topIdx_cl hr
  have hlen : F'.temps.length = F.temps.length := ht.2.2.1
  -- the new temporaries correspond
  have hnew : upPos ks.length (.temp s.topIdx F.temps.length) = .temp s'.topIdx F'.temps.length := by
    rw [htC, hlen]; rfl
  rw [park_eq s v (σ l) xs T m hF, park_eq s' v' l _ T m hF']
  have hliveC : ∀ n, ({ s'.pushTemp v' with shape := fun p => if p = .temp s'.topIdx F'.temps.length then some l else s'.shape p, lent := fun n => if n = l then xs.map (upSite ks.length) else s'.lent n, heldTy := fun n => if n = l then T else s'.heldTy n, heldMem := fun n => if n = l then m else s'.heldMem n } : SState).Live n → n = l ∨ s'.Live n := fun n hn => by
    obtain ⟨q, hq, hqs⟩ := (SState.live_iff _ n).1 hn
    dsimp only at hqs
    split at hqs
    · cases hqs; exact .inl rfl
    · exact .inr ((SState.live_iff s' n).2 ⟨q, hsa' q n hqs, hqs⟩)
  have hσ : ∀ n, s'.Live n → σ n ≠ σ l := fun n hn e => by
    obtain ⟨q, -, hq⟩ := (SState.live_iff s' n).1 hn
    rw [hr.inj _ _ e] at hq; exact hnot' q hq
  refine
  { inj := hr.inj
    fresh := hpush.fresh
    frames := hpush.frames
    lowerSkel := hpush.lowerSkel
    lowerVal := hpush.lowerVal
    lowerShape := fun p hp => by
      show (if p = _ then _ else _) = _
      rw [if_neg (fun e => by subst e; simp [Pos.frameOf] at hp; omega)]; exact hr.lowerShape p hp
    top := hpush.top
    topShape := fun p hp => by
      show (if p = _ then _ else _) = Option.map σ (if upPos ks.length p = _ then _ else _)
      by_cases e : p = .temp s.topIdx F.temps.length
      · subst e; rw [if_pos rfl, hnew, if_pos rfl]; rfl
      · rw [if_neg e, if_neg (fun e' => e (upPos_inj (by rw [hp, ← htI]; rfl) (e'.trans hnew.symm)))]
        exact hr.topShape p hp
    clShape := fun q n hq => by
      dsimp only at hq
      split at hq
      · rename_i e; subst e; exact ⟨_, by rw [htI]; rfl, hnew.symm⟩
      · exact hr.clShape q n hq
    held := fun n hn => by
      rcases hliveC n hn with rfl | hn'
      · exact ⟨fun _ => by simp, by simp⟩
      · have e : σ n ≠ σ l := hσ n hn'
        have e' : n ≠ l := fun h => e (h ▸ rfl)
        simp only [if_neg e, if_neg e']
        exact hr.held n hn'
    lentTop := fun n x hx hheld => by
      dsimp only
      by_cases e : n = l
      · subst e; rw [if_pos rfl, if_pos rfl]
        constructor
        · intro h; exact List.mem_map.mpr ⟨x, h, rfl⟩
        · intro h
          obtain ⟨y, hy, hyx⟩ := List.mem_map.mp h
          have := site_up_inj (c := ks.length) (by rw [hxs y hy, hx]) hyx
          rw [← this]; exact hy
      · have e2 : σ n ≠ σ l := fun h => e (hr.inj _ _ h)
        rw [if_neg e2, if_neg e]
        obtain ⟨p, hp⟩ := hheld
        dsimp only at hp
        split at hp
        · exact absurd (Option.some.inj hp).symm e2
        · exact hr.lentTop n x hx ⟨p, hp⟩
    lentImg := fun n x hx hheld hxn => by
      dsimp only at hxn
      by_cases e : n = σ l
      · exact ⟨l, e⟩
      · rw [if_neg e] at hxn
        obtain ⟨p, hp⟩ := hheld
        dsimp only at hp
        split at hp
        · exact absurd (Option.some.inj hp).symm e
        · exact hr.lentImg n x hx ⟨p, hp⟩ hxn
    lentCl := fun n x hx => by
      dsimp only at hx
      split at hx
      · obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
        exact .inl ⟨y.pos, hxs y hy, rfl⟩
      · exact hr.lentCl n x hx
    lentCaller := fun n p hp hs => by
      show (if n = _ then _ else _) = _
      rw [if_neg (fun e => hnot p (by rw [hr.lowerShape p hp, hs, e]))]
      exact hr.lentCaller n p hp hs
    topLabels := fun n hn => by
      rcases hliveC n hn with rfl | hn'
      · exact htop
      · exact hr.topLabels n hn' }

end

/-! ## A holder forgotten: a move, a drop -/

section
variable {σ : Nat → Nat} {s₀ : SState} {ks : List Nat} {s s' : SState}

/-- The shape with the entry at `r` cleared. -/
def clearShape (t : SState) (r : Pos) : SState := { t with shape := fun p => if p = r then none else t.shape p }

theorem live_clearShape {t : SState} {r : Pos} {n : Nat} (h : (clearShape t r).Live n) : t.Live n := by
  obtain ⟨p, hp, hs⟩ := (SState.live_iff _ n).1 h
  simp only [clearShape] at hs
  split at hs
  · cases hs
  · exact (SState.live_iff t n).2 ⟨p, hp, hs⟩

/-- **Forgetting corresponding holders keeps the relation**: the entries at a position of the callee's frame and at the
closure's corresponding position are cleared together. -/
theorem frameRel_clearShape (hr : FrameRel σ s₀ ks s s') {r : Pos} (hrf : r.frameOf = s₀.topIdx) :
    FrameRel σ s₀ ks (clearShape s r) (clearShape s' (upPos ks.length r)) where
  inj := hr.inj
  fresh := hr.fresh
  frames := hr.frames
  lowerSkel := hr.lowerSkel
  lowerVal := hr.lowerVal
  lowerShape := fun p hp => by
    simp only [clearShape]; rw [if_neg (fun e => by subst e; omega)]; exact hr.lowerShape p hp
  top := hr.top
  topShape := fun p hp => by
    simp only [clearShape]
    by_cases e : p = r
    · subst e; simp
    · rw [if_neg e, if_neg (fun e' => e (upPos_inj (by rw [hp, hrf]) e'))]; exact hr.topShape p hp
  clShape := fun q n hq => by
    simp only [clearShape] at hq
    split at hq
    · cases hq
    · exact hr.clShape q n hq
  held := fun n hn => hr.held n (live_clearShape hn)
  lentTop := fun n x hx ⟨p, hp⟩ => by
    simp only [clearShape] at hp
    split at hp
    · cases hp
    · exact hr.lentTop n x hx ⟨p, hp⟩
  lentImg := fun n x hx ⟨p, hp⟩ hxn => by
    simp only [clearShape] at hp
    split at hp
    · cases hp
    · exact hr.lentImg n x hx ⟨p, hp⟩ hxn
  lentCl := hr.lentCl
  lentCaller := hr.lentCaller
  topLabels := fun n hn => hr.topLabels n (live_clearShape hn)

theorem takeLabel_eq {t : SState} {n : Nat} {r : Pos} (h : t.holderOf n = some r) :
    t.takeLabel n = clearShape (t.setAt r fun _ => .moved) r := by
  unfold SState.takeLabel clearShape; rw [h]; dsimp only; rw [SState.shape_setAt]

/-- **A move of a borrow (`takeLabel`)**: in place at the image of a closure-live label, in the closure at the label;
the holders correspond, both become `moved` and are forgotten. -/
theorem frameRel_takeLabel (hr : FrameRel σ s₀ ks s s') (hu : s.Uniq) (hsa : ShapeAt s) (hsa' : ShapeAt s')
    {l : Nat} (hl : s'.Live l) : FrameRel σ s₀ ks (s.takeLabel (σ l)) (s'.takeLabel l) := by
  obtain ⟨q, hq⟩ := SState.holderOf_of_live hl
  obtain ⟨p, hpf, rfl, hp⟩ := holder_frame hr hu hsa hq
  rw [takeLabel_eq hp, takeLabel_eq hq]
  exact frameRel_clearShape (frameRel_setAt hr hsa' hpf (v := fun _ => .moved) (v' := fun _ => .moved) fun _ => rfl) hpf

theorem dropLast_eq (t : SState) {F : SFrame} (hF : t.env.getLast? = some F) :
    t.dropLast = clearShape (modTop t fun fr => { fr with binds := fr.binds.dropLast }) (.bind t.topIdx (F.binds.length - 1)) := by
  unfold SState.dropLast clearShape modTop
  simp only [hF, Option.some.injEq]

/-- **(O8)'s drop of the top frame's last binding**, on both sides (its holdership forgotten with it). -/
theorem frameRel_dropLast (hr : FrameRel σ s₀ ks s s') (hsa' : ShapeAt s') :
    FrameRel σ s₀ ks s.dropLast s'.dropLast := by
  obtain ⟨F, F', hF, hF', ht⟩ := top_rel hr
  rw [dropLast_eq s hF, dropLast_eq s' hF']
  have h1 := frameRel_modTop hr (g := fun fr => { fr with binds := fr.binds.dropLast })
    (g' := fun fr => { fr with binds := fr.binds.dropLast }) (fun F F' h => h.dropLastBind) fun l => live_modTop hsa' _
  have e : upPos ks.length (.bind s.topIdx (F.binds.length - 1)) = .bind s'.topIdx (F'.binds.length - 1) := by
    rw [topIdx_cl hr, ← ht.1]; rfl
  rw [← e]
  exact frameRel_clearShape h1 (by rw [topIdx_eq hr]; rfl)

end

/-! ## A read (the paper's (O2)) and `contentOf` -/

theorem ft_and {S S' : Nat → Prop} {f : SVal} (h : Ochr.Meaning.FT S f) (h' : Ochr.Meaning.FT S' f) :
    Ochr.Meaning.FT (fun l => S l ∧ S' l) f := fun ψ ψ' e => by
  open Classical in
  let χ : Future := fun l => if S l then ψ l else ψ' l
  have h1 : f ψ = f χ := h ψ χ fun l hl => by simp only [χ, if_pos hl]
  have h2 : f χ = f ψ' := h' χ ψ' fun l hl => by
    simp only [χ]; split
    · rename_i hs; exact e l ⟨hs, hl⟩
    · rfl
  exact h1.trans h2

theorem stepField_m (dm : DataModel) (Γ : List IndDecl) (T : TyS) (c i : Nat) (v : Sem) :
    Sem.stepField dm Γ T c i v = Sem.stepField dm Γ ⟨T.m, none⟩ c i v := by
  unfold Sem.stepField; rfl

/-- A step other than `*` reads its type's meaning only, not its label. -/
theorem step_m (dm : DataModel) (Γ : List IndDecl) (T : TyS) (st : Step) (v : Sem) (h : st ≠ .deref) :
    Sem.step dm Γ T st v = Sem.step dm Γ ⟨T.m, none⟩ st v := by
  cases st with
  | deref => exact absurd rfl h
  | proj i =>
    cases i with
    | zero => simp only [Sem.step]; rw [stepField_m]
    | succ n => simp only [Sem.step]; rw [stepField_m]
  | field g => simp only [Sem.step]; split <;> rw [stepField_m]

/-- Following a path reads the type's meaning only: the same part, at a type with the same meaning. -/
theorem follow_m (dm : DataModel) (Γ : List IndDecl) : ∀ (st : List Step) (T T' : TyS) (v : Sem), T.m = T'.m →
    (Sem.follow dm Γ T v st).map (fun r => (r.1, r.2.m)) = (Sem.follow dm Γ T' v st).map (fun r => (r.1, r.2.m))
  | [], T, T', v, hm => by simp [Sem.follow, hm]
  | .deref :: sts, T, T', v, hm => by
    simp only [Sem.follow, Sem.step, Option.bind_some]; exact follow_m dm Γ sts T T' v hm
  | .proj i :: sts, T, T', v, hm => by
    simp only [Sem.follow]
    rw [step_m dm Γ T _ v (by simp), step_m dm Γ T' _ v (by simp), hm]
  | .field g :: sts, T, T', v, hm => by
    simp only [Sem.follow]
    rw [step_m dm Γ T _ v (by simp), step_m dm Γ T' _ v (by simp), hm]

section
variable {K : RunCtx} {σ : Nat → Nat} {s₀ : SState} {ks : List Nat} {s s' : SState}

theorem resolve_corr (hr : FrameRel σ s₀ ks s s') (p : Place) :
    resolve s' p = (resolve s p).map (fun x => (upPos ks.length x.1, x.2)) ∧
      ∀ pos steps, resolve s p = some (pos, steps) → pos.frameOf = s₀.topIdx := by
  obtain ⟨F, F', hF, hF', ht⟩ := top_rel hr
  unfold resolve SState.varPos
  rw [hF, hF', topIdx_cl hr]
  obtain ⟨i, steps⟩ := p.steps
  simp only [← ht.1]
  constructor
  · split <;> rfl
  · intro pos steps' h
    split at h
    · simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, -⟩ := h; exact topIdx_eq hr
    · cases h

/-- **The stored types of the callee's frame correspond**: the same, the label renamed. -/
theorem tyAt_corr (hr : FrameRel σ s₀ ks s s') {p : Pos} (hp : p.frameOf = s₀.topIdx) :
    s.tyAt p = { s'.tyAt (upPos ks.length p) with label := (s'.tyAt (upPos ks.length p)).label.map σ } := by
  obtain ⟨F, F', hF, hF', hl, hb, -⟩ := top_rel hr
  have hs : s.env[s₀.topIdx]? = some F := by rw [← topIdx_eq hr]; exact env_top s hF
  have hs' : s'.env[1]? = some F' := by have := env_top s' hF'; rwa [topIdx_cl hr] at this
  cases p with
  | bind f i =>
    simp only [Pos.frameOf] at hp; subst hp
    show (match s.env[s₀.topIdx]?.bind (·.binds[i]?) with | some b => b.ty | none => .plain TyM.err) =
      { (match s'.env[1]?.bind (·.binds[i]?) with | some b => b.ty | none => .plain TyM.err) with
        label := (match s'.env[1]?.bind (·.binds[i]?) with | some b => b.ty | none => .plain TyM.err).label.map σ }
    rw [hs, hs']
    simp only [Option.bind_some]
    cases h1 : F.binds[i]? with
    | none =>
      have : F'.binds[i]? = none := by rw [List.getElem?_eq_none_iff] at h1 ⊢; omega
      rw [this]; rfl
    | some b =>
      have hi : i < F'.binds.length := by rw [← hl]; exact (List.getElem?_eq_some_iff.1 h1).1
      rw [List.getElem?_eq_getElem hi]
      exact (hb i b _ h1 (List.getElem?_eq_getElem hi)).1
  | temp f j => rfl

/-- **(O2) a read**: a place of the callee's frame read at the state's typed future gives the same meaning on both
sides. The closure's frame reads only live labels other than the parameters' (locality and (I1)), whose records agree
(`FrameRel.held`); in place it reads the same labels through the renaming. -/
theorem read_corr (φ : Future) (h : AccInv K σ s₀ ks s s') {p : Pos} (hp : p.frameOf = s₀.topIdx) :
    s.valAt p (s.typedFuture φ) = s'.valAt (upPos ks.length p) (s'.typedFuture φ) := by
  rw [top_valAt h.rel p hp]
  refine ft_and (h.loc _) (h.noParam _ (upPos_frameOf _ _)) _ _ fun l ⟨hl, hk⟩ => ?_
  have hl' : σ l ∈ s.liveLabels := live_img h.rel h.shape hl
  have hl'' : l ∈ s'.liveLabels := hl
  simp only [renF, SState.typedFuture, if_pos hl', if_pos hl'']
  exact (h.rel.held l hl).1 hk

end

section
variable {K : RunCtx} {σ : Nat → Nat} {s₀ : SState} {ks : List Nat} {s s' : SState}

/-- Two `contentOf` outcomes agree across the frame relation: the same part, its type with the label renamed,
corresponding places, related states after the access. -/
def ContentAgree (K : RunCtx) (σ : Nat → Nat) (s₀ : SState) (ks : List Nat) :
    Option ((Sem × TyS × Pos × List Step) × SState) → Option ((Sem × TyS × Pos × List Step) × SState) → Prop
  | some ((v, T, pos, steps), t), some ((v', T', pos', steps'), t') =>
    v = v' ∧ T = { T' with label := T'.label.map σ } ∧ pos' = upPos ks.length pos ∧ pos.frameOf = s₀.topIdx ∧
      steps = steps' ∧ AccInv K σ s₀ ks t t'
  | none, none => True
  | _, _ => False

/-- **`contentOf` across the frame relation** (the read and borrow clauses' common part: [Access], then (O2)): the two
sides find the same part at corresponding places, with the same type up to the renamed label, from related states; and
the access's strict tests pass together. -/
theorem contentOf_corr (φ : Future) (hs₀ : FrameStart s₀ ks) (h : AccInv K σ s₀ ks s s') (p : Place) :
    ContentAgree K σ s₀ ks (contentOf K φ p s) (contentOf K φ p s') ∧ (ContentOk K φ p s ↔ ContentOk K φ p s') := by
  obtain ⟨hres, hframe⟩ := resolve_corr h.rel p
  cases hrp : resolve s p with
  | none =>
    have hrp' : resolve s' p = none := by rw [hres, hrp]; rfl
    unfold contentOf ContentOk; rw [hrp, hrp']; exact ⟨trivial, Iff.rfl⟩
  | some x =>
    obtain ⟨pos, steps⟩ := x
    have hpos := hframe pos steps hrp
    have hrp' : resolve s' p = some (upPos ks.length pos, steps) := by rw [hres, hrp]; rfl
    obtain ⟨hacc, hok⟩ := frameRel_access φ hs₀ h hpos (dataHit steps)
    refine ⟨?_, by unfold ContentOk; rw [hrp, hrp']; exact hok⟩
    have hread := read_corr φ hacc hpos
    have hT := tyAt_corr h.rel hpos
    have hT' := tyAt_corr hacc.rel hpos
    unfold contentOf; rw [hrp, hrp']; dsimp only
    rw [hread]
    generalize (s'.access (upPos ks.length pos) (dataHit steps)).valAt (upPos ks.length pos)
      ((s'.access (upPos ks.length pos) (dataHit steps)).typedFuture φ) = v at *
    have hf := follow_m K.dm K.Γ steps (s.tyAt pos) (s'.tyAt (upPos ks.length pos)) v (by rw [hT])
    cases e1 : Sem.follow K.dm K.Γ (s.tyAt pos) v steps with
    | none =>
      rw [e1] at hf
      cases e2 : Sem.follow K.dm K.Γ (s'.tyAt (upPos ks.length pos)) v steps with
      | none => trivial
      | some r => rw [e2] at hf; cases hf
    | some r =>
      obtain ⟨v1, T1⟩ := r
      rw [e1] at hf
      cases e2 : Sem.follow K.dm K.Γ (s'.tyAt (upPos ks.length pos)) v steps with
      | none => rw [e2] at hf; cases hf
      | some r' =>
        obtain ⟨v1', T1'⟩ := r'
        rw [e2] at hf
        simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at hf
        obtain ⟨rfl, hm⟩ := hf
        refine ⟨rfl, ?_, rfl, hpos, rfl, hacc⟩
        split
        · exact hT'
        · cases T1; cases T1'; simp only at hm; subst hm; rfl

end

/-! ## The internal relation of the frame property -/

/-- **The frame property's internal relation** (docs/31 D216): `FrameRel` with what [Access] needs (`AccInv`), both
states good (the paper's (H1), (H2)), and the in-place counter at or above the call's (a fresh label is the body's). The
paper's (H3) (locality) is `AccInv.rinv'` and `AccInv.noParam`; (H4) `AccInv.cells`; (H5) `AccInv.shape`; (I1) `noParam`
(through `top_noParam` in place); (I2) `FrameRel.lentImg`; (I3) `AccInv.pfill`; (I4) `LendWF`, `order`, `mono`. -/
structure FrameInv (K : RunCtx) (φ : Future) (σ : Nat → Nat) (s₀ : SState) (ks : List Nat) (s s' : SState) : Prop where
  acc : AccInv K σ s₀ ks s s'
  good : Strict.SGood K.dm K.Γ φ s
  good' : Strict.SGood K.dm K.Γ φ s'
  counter : s₀.nextLoan ≤ s.nextLoan
  /-- (lead34, docs/31 D219) the renaming sends every closure label to a parameter label or to a label the body makes: a
  label the closure's run returns, live or not, is never a caller's (an [Entry]'s lending at a match's result label then
  never reaches a caller's borrow, `FrameRel.lentCaller`). At a call it holds when the closure runs from counter `0`
  (a global, `stateOf 0`; under ruling R2 every closure): the cells are `0, …, n - 1` and `σ` sends the rest to the fresh
  labels in place. -/
  srange : ∀ l, σ l ∈ ks ∨ s₀.nextLoan ≤ σ l
  /-- (lead34, D219) every site in the callee's frame is at a binding: a place resolves to a binding (`resolve`), and an
  end, a call's lending and an entry's lending copy sites; so nothing is lent at a temporary, where a result is parked
  (what [Entry]'s lending of the result's label needs to keep lending well founded, `LendWF`). -/
  bsites : ∀ m (y : Site), y ∈ s.lent m → y.pos.frameOf = s₀.topIdx → ∃ i, y.pos = .bind s₀.topIdx i

/-- **A result's label, if live, is held by a temporary of the callee's frame** (lead34, D219): a result is parked
(`pushTempShaped`: a borrow, a move of a borrow, a call returning one) and every later step of the clause that returns it
only clears holders (an end, an access, a drop of a binding). [Entry]'s lending at a match's result label needs it: with
`FrameInv.bsites` nothing is lent at the label's holder, so lending it further keeps lending well founded. -/
def ResAtTemp (s₀ t : SState) (lab : Option Nat) : Prop :=
  ∀ k, lab = some k → t.Live k → ∃ j, t.shape (.temp s₀.topIdx j) = some k

/-- `FrameAgree` with the internal relation concluded (what the induction over `runT` carries; the third referee's R9:
`FrameAgree` concludes `FrameRel` only), and the in-place result's label parked (`ResAtTemp`). -/
def FrameAgreeI (K : RunCtx) (φ : Future) (σ : Nat → Nat) (s₀ : SState) (ks : List Nat) :
    Option (Res × SState) → Option (Res × SState) → Prop
  | some (r, t), some (r', t') => r.1 = r'.1 ∧ r.2 = { r'.2 with label := r'.2.label.map σ } ∧ FrameInv K φ σ s₀ ks t t' ∧
      ResAtTemp s₀ t r.2.label
  | none, none => True
  | _, _ => False

theorem FrameAgreeI.frameAgree {K : RunCtx} {φ : Future} {σ : Nat → Nat} {s₀ : SState} {ks : List Nat}
    {o o' : Option (Res × SState)} (h : FrameAgreeI K φ σ s₀ ks o o') : FrameAgree σ s₀ ks o o' := by
  match o, o', h with
  | some (_, _), some (_, _), ⟨h1, h2, h3, _⟩ => exact ⟨h1, h2, h3.acc.rel⟩
  | none, none, _ => trivial

/-- **The frame property over the internal relation** (OPEN; the form the induction over `runT` proves, one lemma per
clause, from the operation lemmas of `FrameAccess` and this file). -/
def RunFrameI : Prop :=
  ∀ (K : RunCtx) (ρ : Assignment) (φ : Future) (σ : Nat → Nat) (s₀ : SState) (ks : List Nat)
    (tl : Bool) (hint : TyS) (t : Term) (s s' : SState),
    Strict.FundCtx K → FrameStart s₀ ks → t.valsOk (Strict.ValsP K ρ φ) → (t.idFree = true ∨ ks = []) →
    FrameInv K φ σ s₀ ks s s' →
    FrameAgreeI K φ σ s₀ ks (runT K ρ φ tl hint t s) (runT K ρ φ tl hint t s')

section
variable {K : RunCtx} {φ : Future} {σ : Nat → Nat} {s₀ : SState} {ks : List Nat} {s s' : SState}

/-- **`RunFrame`'s hypotheses give the internal relation, with seven more**: lending well founded in place, parameter
labels lent in the callee's frame only as fills, the renaming's order on the closure's labels (two clauses), the
counter, the renaming's range (lead34) and the callee's frame's sites at bindings (lead34). `RunFrame` as stated (FrameRec) lacks them; by reading it is false at a state no call makes (two parameter
labels lent at each other's holders, reached by one access in orders the renaming reverses: the sites left differ),
as each earlier restatement was (D129, D201, D203). -/
theorem frameInv_of (hr : FrameRel σ s₀ ks s s')
    (hloc : ∀ p, Ochr.Meaning.FT (fun l => s'.Live l) (s'.valAt p))
    (hloc1 : ∀ p, p.frameOf = 1 → Ochr.Meaning.FT (fun l => s'.Live l ∧ σ l ∉ ks) (s'.valAt p))
    (hg : Strict.SGood K.dm K.Γ φ s) (hg' : Strict.SGood K.dm K.Γ φ s')
    (hcells : ks.length ≤ (s'.env.headD {}).binds.length)
    (hlend : LendWF s) (hpfill : ∀ k ∈ ks, ∀ y ∈ s.lent k, y.pos.frameOf = s₀.topIdx → y.fill = true)
    (horder : ∀ l l', s'.Live l → s'.Live l' → σ l ∈ ks → σ l' ∉ ks → l < l')
    (hmono : ∀ l l', s'.Live l → s'.Live l' → σ l ∉ ks → σ l' ∉ ks → l < l' → σ l < σ l')
    (hcounter : s₀.nextLoan ≤ s.nextLoan) (hsrange : ∀ l, σ l ∈ ks ∨ s₀.nextLoan ≤ σ l)
    (hbsites : ∀ m (y : Site), y ∈ s.lent m → y.pos.frameOf = s₀.topIdx → ∃ i, y.pos = .bind s₀.topIdx i) :
    FrameInv K φ σ s₀ ks s s' where
  acc :=
  { rel := hr
    uniq := hg.uniq
    shape := fun p l h => (hg.acyc.2.2 p l h).1
    lend := hlend
    pfill := hpfill
    held := hg.held
    cells := hcells
    uniq' := hg'.uniq
    rinv' := ⟨fun p => (hloc p).mono fun _ h => .inr h,
      fun r x hr hx => (ft_and (hg'.acyc.2.1 r x hr hx) (hloc r)).mono fun _ ⟨h1, h2⟩ =>
        .inr (h1.elim (fun h => absurd h2 h.2) fun h => h),
      hg'.acyc.2.2⟩
    noParam := fun p hp => (hloc1 p hp).mono fun _ h => h.2
    order := horder
    mono := hmono }
  good := hg
  good' := hg'
  counter := hcounter
  srange := hsrange
  bsites := hbsites

end

/-! ## The internal relation through a write -/

section
variable {K : RunCtx} {σ : Nat → Nat} {s₀ : SState} {ks : List Nat} {s s' : SState}

theorem setAt_lent (t : SState) (p : Pos) (v : SVal) : (t.setAt p v).lent = t.lent := by cases p <;> rfl
theorem setAt_heldTy (t : SState) (p : Pos) (v : SVal) : (t.setAt p v).heldTy = t.heldTy := by cases p <;> rfl
theorem setAt_heldMem (t : SState) (p : Pos) (v : SVal) : (t.setAt p v).heldMem = t.heldMem := by cases p <;> rfl
theorem setAt_nextLoan (t : SState) (p : Pos) (v : SVal) : (t.setAt p v).nextLoan = t.nextLoan := by cases p <;> rfl

theorem liveLabels_setAt (t : SState) (p : Pos) (v : SVal) : (t.setAt p v).liveLabels = t.liveLabels := by
  simp only [SState.liveLabels, SState.positions_setAt, SState.shape_setAt]

/-- **(O5)'s write against the internal relation**: corresponding positions of the callee's frame set to values related
through the renaming keep `AccInv`, when the closure's new value reads only live labels, no parameter label, and, at a
holder of `x`, only live labels above `x` (the locality clauses at the written position). Shape, sites, records and
counters are untouched. -/
theorem accInv_setAt (h : AccInv K σ s₀ ks s s') {p : Pos} (hp : p.frameOf = s₀.topIdx) {v v' : SVal}
    (hv : ∀ ψ, v ψ = v' (renF σ ψ)) (hl : Ochr.Meaning.FT (fun l => s'.Live l) v')
    (hnp : Ochr.Meaning.FT (fun l => σ l ∉ ks) v')
    (h2 : ∀ x, s'.shape (upPos ks.length p) = some x → Ochr.Meaning.FT (fun y => s'.Live y ∧ x < y) v') :
    AccInv K σ s₀ ks (s.setAt p v) (s'.setAt (upPos ks.length p) v') := by
  have hq := upPos_frameOf ks.length p
  have hval : ∀ q, (s'.setAt (upPos ks.length p) v').valAt q = s'.valAt q ∨
      (q = upPos ks.length p ∧ (s'.setAt (upPos ks.length p) v').valAt q = v') := fun q => by
    by_cases e : q = upPos ks.length p
    · subst e
      by_cases hm : upPos ks.length p ∈ s'.positions
      · exact .inr ⟨rfl, valAt_setAt_self _ _ _ hm⟩
      · left
        rw [SState.valAt_of_not_mem _ _ (by rw [SState.positions_setAt]; exact hm), SState.valAt_of_not_mem _ _ hm]
    · exact .inl (SState.valAt_setAt_ne _ _ _ _ (Ne.symm e))
  have hlive' : ∀ y, (s'.setAt (upPos ks.length p) v').Live y ↔ s'.Live y := fun y => SState.live_setAt _ _ _ y
  refine
  { rel := frameRel_setAt h.rel h.shape' hp hv
    uniq := fun a b l ha hb => h.uniq a b l (by rwa [SState.shape_setAt] at ha) (by rwa [SState.shape_setAt] at hb)
    shape := fun a l ha => by rw [SState.positions_setAt]; rw [SState.shape_setAt] at ha; exact h.shape a l ha
    lend := by
      obtain ⟨rk, hrk⟩ := h.lend
      exact ⟨rk, fun a b y ha hy hb => hrk a b y ((SState.live_setAt _ _ _ a).1 ha) (by rwa [setAt_lent] at hy)
        (by rwa [SState.shape_setAt] at hb)⟩
    pfill := fun k hk y hy => h.pfill k hk y (by rwa [setAt_lent] at hy)
    held := fun l hl => by rw [liveLabels_setAt] at hl; rw [setAt_heldTy, setAt_heldMem]; exact h.held l hl
    cells := by
      cases p with
      | bind f i =>
        unfold upPos; rw [setAt_bind_modTop s' (topIdx_cl h.rel).symm, modTop_headD _ _ (by rw [topIdx_cl h.rel]; omega)]
        exact h.cells
      | temp f i =>
        unfold upPos; rw [setAt_temp_modTop s' (topIdx_cl h.rel).symm, modTop_headD _ _ (by rw [topIdx_cl h.rel]; omega)]
        exact h.cells
    uniq' := fun a b l ha hb => h.uniq' a b l (by rwa [SState.shape_setAt] at ha) (by rwa [SState.shape_setAt] at hb)
    rinv' := ⟨fun q => by
        rcases hval q with e | ⟨-, e⟩ <;> rw [e]
        · exact (h.rinv'.1 q).mono fun y hy => hy.elim (fun h => h.elim) fun hy => .inr ((hlive' y).2 hy)
        · exact hl.mono fun y hy => .inr ((hlive' y).2 hy),
      fun r x hr hx => by
        rw [SState.positions_setAt] at hr; rw [SState.shape_setAt] at hx
        rcases hval r with e | ⟨rfl, e⟩ <;> rw [e]
        · exact (h.rinv'.2.1 r x hr hx).mono fun y hy => hy.elim (fun h => h.1.elim) fun hy =>
            .inr ⟨(hlive' y).2 hy.1, hy.2⟩
        · exact (h2 x hx).mono fun y hy => .inr ⟨(hlive' y).2 hy.1, hy.2⟩,
      fun a x ha => by
        rw [SState.shape_setAt] at ha; rw [SState.positions_setAt, setAt_nextLoan]
        exact h.rinv'.2.2 a x ha⟩
    noParam := fun q hq1 => by
      rcases hval q with e | ⟨-, e⟩ <;> rw [e]
      · exact h.noParam q hq1
      · exact hnp
    order := fun a b ha hb => h.order a b ((hlive' a).1 ha) ((hlive' b).1 hb)
    mono := fun a b ha hb => h.mono a b ((hlive' a).1 ha) ((hlive' b).1 hb) }

end

end Ochr.Meaning.Steps.Form.FrameEnd
