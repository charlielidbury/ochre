import Ochr.Meaning.Steps.FrameCallInv

/-!
# The `let` and `;` clauses of the frame property (lead35; docs/31 D222)

The paper's rows "`let` and `;` with labels" of `<sec-frame-proof>` ((O3), (O4), (O8)): a `let` runs its bound term,
binds the result (`pushBindShaped`: a borrow result's label moves from its temporary to the new binding), runs its body,
then ends what the binding holds (its borrow's end, or `letLenders`' access of it) and drops it. Two facts of the in-place
state carry it, both in the internal relation since this lead (`FrameInv.psites`, `ResAtTemp`'s second clause):
- every site of a live label in the callee's frame is at an existing position: the `let`'s end empties the position it
  drops of live labels' sites (`endLabel_noSiteAt`, `access_noLiveSiteAt`), so the binding a later `let` pushes there is
  lent nothing, and lending stays well founded when the result's label moves to it;
- a dead result label lends nothing, so binding it again revives no stale site.
-/

namespace Ochr.Meaning.Steps.Form.FrameEnd

open Ochr Ochr.Meaning

/-! ## A `let`'s end empties the position it drops -/

/-- After the end of a label, no label has a site at its old holder: the sites there are re-rooted at the ended label's,
which are not at its own holder (lending is well founded). -/
theorem endLabel_noSiteAt {t : SState} (hlend : LendWF t) {l : Nat} {r : Pos} (hh : t.holderOf l = some r) :
    ∀ m (y : Site), y ∈ (t.endLabel l).lent m → y.pos ≠ r := by
  intro m y hy e
  have hll : t.Live l := (SState.live_iff t l).2 ⟨r, (SState.holderOf_spec hh).1, (SState.holderOf_spec hh).2⟩
  rw [SState.endLabel_eq hh] at hy
  by_cases hml : m = l
  · subst hml; rw [endAt_lent, relend_eq, if_pos rfl] at hy; cases hy
  rw [endAt_lent, mem_relend hml] at hy
  rcases hy with ⟨-, hne⟩ | ⟨x₀, -, -, z, hz, rfl⟩
  · exact hne e
  · rw [relendSite_pos] at e
    obtain ⟨rk, hrk⟩ := hlend
    exact Nat.lt_irrefl _ (hrk l l z hll hz (by rw [e]; exact (SState.holderOf_spec hh).2))

/-- After an access, no live label reaches the place (the rounds' fixpoint). -/
theorem access_noReach (t : SState) (p : Pos) (hit : List Step → Bool) :
    (t.access p hit).liveLabels.filter ((t.access p hit).reached p hit) = [] := by
  rw [access_iterR]; exact round_nil_of_fix (iter_fix p hit t)

theorem dataHit_nil (ψ : List Step) : dataHit [] ψ = true := by
  unfold dataHit; simp

/-- After `letLenders`' access of a position, no live label has a site there. -/
theorem access_noLiveSiteAt (t : SState) (r : Pos) :
    ∀ m (y : Site), (t.access r (dataHit [])).Live m → y ∈ (t.access r (dataHit [])).lent m → y.pos ≠ r := by
  intro m y hm hy e
  have h0 := access_noReach t r (dataHit [])
  have hmem : m ∈ (t.access r (dataHit [])).liveLabels.filter ((t.access r (dataHit [])).reached r (dataHit [])) := by
    rw [List.mem_filter]
    refine ⟨hm, ?_⟩
    unfold SState.reached
    rw [List.any_eq_true]
    exact ⟨y, hy, by simp [e, dataHit_nil]⟩
  rw [h0] at hmem; cases hmem

/-! ## A label held anew -/

section
variable {σ : Nat → Nat} {s₀ : SState} {ks : List Nat} {s s' : SState}

/-- **A label held at corresponding new holders of the two top frames** (`pushBindShaped`'s last step): the label is held
nowhere before, its records and its sites in the callee's frame correspond, and its image is a parameter label or a
fresh one. -/
theorem frameRel_hold (hr : FrameRel σ s₀ ks s s') {p : Pos} (hp : p.frameOf = s₀.topIdx) {l : Nat}
    (hnot' : ∀ q, s'.shape q ≠ some l)
    (hrec : (σ l ∉ ks → s.heldMem (σ l) = s'.heldMem l) ∧ s.heldTy (σ l) = s'.heldTy l)
    (hsites : ∀ x : Site, x.pos.frameOf = s₀.topIdx → (x ∈ s.lent (σ l) ↔ upSite ks.length x ∈ s'.lent l))
    (htop : σ l ∈ ks ∨ s₀.nextLoan ≤ σ l) (hsa' : ShapeAt s') :
    FrameRel σ s₀ ks { s with shape := fun q => if q = p then some (σ l) else s.shape q }
      { s' with shape := fun q => if q = upPos ks.length p then some l else s'.shape q } where
  inj := hr.inj
  fresh := hr.fresh
  frames := hr.frames
  lowerSkel := hr.lowerSkel
  lowerVal := hr.lowerVal
  lowerShape := fun q hq => by
    show (if q = p then _ else _) = _
    rw [if_neg (fun e => by subst e; omega)]; exact hr.lowerShape q hq
  top := hr.top
  topShape := fun q hq => by
    show (if q = p then _ else _) = Option.map σ (if upPos ks.length q = upPos ks.length p then _ else _)
    by_cases e : q = p
    · subst e; rw [if_pos rfl, if_pos rfl]; rfl
    · rw [if_neg e, if_neg (fun e' => e (upPos_inj (by rw [hq, hp]) e'))]; exact hr.topShape q hq
  clShape := fun q n hq => by
    dsimp only at hq
    split at hq
    · rename_i e; subst e; exact ⟨p, hp, rfl⟩
    · exact hr.clShape q n hq
  held := fun n hn => by
    obtain ⟨q, hq, hqs⟩ := (SState.live_iff _ n).1 hn
    dsimp only at hqs
    split at hqs
    · cases hqs; exact hrec
    · exact hr.held n ((SState.live_iff s' n).2 ⟨q, hq, hqs⟩)
  lentTop := fun n x hx hheld => by
    by_cases e : n = l
    · subst e; exact hsites x hx
    · obtain ⟨q, hq⟩ := hheld
      dsimp only at hq
      split at hq
      · exact absurd (hr.inj _ _ (Option.some.inj hq).symm) e
      · exact hr.lentTop n x hx ⟨q, hq⟩
  lentImg := fun m x hx hheld hxm => by
    by_cases e : m = σ l
    · exact ⟨l, e⟩
    · obtain ⟨q, hq⟩ := hheld
      dsimp only at hq
      split at hq
      · exact absurd (Option.some.inj hq).symm e
      · exact hr.lentImg m x hx ⟨q, hq⟩ hxm
  lentCl := hr.lentCl
  lentCaller := hr.lentCaller
  topLabels := fun n hn => by
    obtain ⟨q, hq, hqs⟩ := (SState.live_iff _ n).1 hn
    dsimp only at hqs
    split at hqs
    · cases hqs; exact htop
    · exact hr.topLabels n ((SState.live_iff s' n).2 ⟨q, hq, hqs⟩)

end

/-! ## `pushBindShaped` and `dropLast` written out -/

theorem not_mem_newBind {t : SState} {F : SFrame} (hF : t.env.getLast? = some F) :
    Pos.bind t.topIdx F.binds.length ∉ t.positions := by
  rw [SState.mem_positions]
  simp only [SState.lookup, env_top t hF, Option.bind_some, List.getElem?_eq_none_iff.mpr (Nat.le_refl _)]
  simp

theorem takeLabel_getLast {t : SState} {F : SFrame} (hF : t.env.getLast? = some F) (l : Nat) :
    ∃ F₁ : SFrame, (t.takeLabel l).env.getLast? = some F₁ ∧ F₁.binds.length = F.binds.length := by
  have hle := envLe_takeLabel t l
  obtain ⟨F₁, hF₁, hb₁, -⟩ := hle.2 t.topIdx F (env_top t hF)
  refine ⟨F₁, ?_, hb₁⟩
  rw [List.getLast?_eq_getElem?, hle.1]; exact hF₁

/-- `pushBindShaped` of a borrow result, written out: the label taken, the binding pushed, the label held there. -/
theorem pushBindShaped_some {t : SState} {b : SBinding} {l : Nat} (hl : b.ty.label = some l) {F : SFrame}
    (hF : t.env.getLast? = some F) :
    pushBindShaped t b = { (t.takeLabel l).pushBind b with
      shape := fun q => if q = .bind t.topIdx F.binds.length then some l else ((t.takeLabel l).pushBind b).shape q } := by
  obtain ⟨F₁, hF₁, hb₁⟩ := takeLabel_getLast hF l
  have htop : (t.takeLabel l).topIdx = t.topIdx := by
    unfold SState.topIdx; rw [(envLe_takeLabel t l).1]
  unfold pushBindShaped
  rw [hl]; dsimp only
  rw [SState.pushBind_getLast, hF₁]
  rw [SState.pushBind_topIdx, htop]
  simp only [Option.map_some, List.length_append, List.length_singleton, Nat.add_sub_cancel, hb₁]

theorem pushBindShaped_none {t : SState} {b : SBinding} (hl : b.ty.label = none) : pushBindShaped t b = t.pushBind b := by
  unfold pushBindShaped; rw [hl]

theorem takeLabel_noHolder {t : SState} (hu : t.Uniq) (hsa : ShapeAt t) (l : Nat) : ∀ q, (t.takeLabel l).shape q ≠ some l := by
  intro q hq
  cases hh : t.holderOf l with
  | none =>
    unfold SState.takeLabel at hq; rw [hh] at hq
    obtain ⟨r, hr⟩ := SState.holderOf_of_live ((SState.live_iff t l).2 ⟨q, hsa q l hq, hq⟩)
    rw [hh] at hr; cases hr
  | some r =>
    rw [takeLabel_eq hh] at hq
    simp only [clearShape, SState.shape_setAt] at hq
    split at hq
    · cases hq
    · rename_i hqr; exact hqr (hu q r l hq (SState.holderOf_spec hh).2)

/-! ## A `let` binding its result -/

section
variable {K : RunCtx} {φ : Future} {σ : Nat → Nat} {s₀ : SState} {ks : List Nat} {s s' : SState}

/-- The labels made by the closure: its live ones are below its counter (`SGood`'s shape clause). -/
theorem live_lt_next {t : SState} (hg : Strict.SGood K.dm K.Γ φ t) {l : Nat} (hl : t.Live l) : l < t.nextLoan := by
  obtain ⟨p, -, hp⟩ := (SState.live_iff t l).1 hl
  exact (hg.acyc.2.2 p l hp).2

/-- **A `let` binding its result** (`pushBindShaped`, the paper's (O8)): a borrow result's label moves from its temporary
to the new binding, on both sides; nothing is lent at the new binding (`FrameInv.psites`: it is a position that did not
exist), so lending stays well founded; a result label that had ended lends nothing (`ResAtTemp`, `ResDead`) and its records
correspond (`FrameInv.heldAll`), so holding it again keeps the relation. -/
theorem pushBindShaped_frameInv (h : FrameInv K φ σ s₀ ks s s') (hs₀ : FrameStart s₀ ks) {b b' : SBinding}
    (hBR : BindRen σ b b') {v : Sem} (hbv : b'.val = fun _ => v)
    (hres : ResAtTemp s₀ s b.ty.label) (hresD : ResDead s' b'.ty.label)
    (hg : Strict.SGood K.dm K.Γ φ (pushBindShaped s b)) (hg' : Strict.SGood K.dm K.Γ φ (pushBindShaped s' b'))
    (hri' : SState.RInv (fun _ => False) (pushBindShaped s' b')) :
    FrameInv K φ σ s₀ ks (pushBindShaped s b) (pushBindShaped s' b') := by
  have hA := h.acc
  obtain ⟨F, F', hF, hF', hTR⟩ := top_rel hA.rel
  have htopI : s.topIdx = s₀.topIdx := topIdx_eq hA.rel
  have htopC : s'.topIdx = 1 := topIdx_cl hA.rel
  have hlab : b.ty.label = b'.ty.label.map σ := by rw [hBR.1]
  have hltC : ∀ l, s'.Live l → l < s'.nextLoan := fun l hl => live_lt_next h.good' hl
  rcases Option.eq_none_or_eq_some b'.ty.label with hl | ⟨l, hl⟩
  · have hlI : b.ty.label = none := by rw [hlab, hl]; rfl
    rw [pushBindShaped_none hlI] at hg ⊢; rw [pushBindShaped_none hl] at hg' hri' ⊢
    have hlive : ∀ y, (s.pushBind b).Live y → s.Live y := fun y hy => (SState.live_pushBind h.good.acyc.2.2 _ y).1 hy
    have hlive' : ∀ y, (s'.pushBind b').Live y → s'.Live y := fun y hy => (SState.live_pushBind h.good'.acyc.2.2 _ y).1 hy
    exact
    { acc :=
      { rel := frameRel_pushBind hA.rel hA.shape' hBR
        uniq := hg.uniq
        shape := fun p l hp => (hg.acyc.2.2 p l hp).1
        lend := by
          obtain ⟨rk, hrk⟩ := hA.lend
          exact ⟨rk, fun a b y ha hy hb => hrk a b y (hlive a ha) hy hb⟩
        pfill := hA.pfill
        held := hg.held
        cells := by
          rw [pushBind_modTop, modTop_headD _ _ (by rw [htopC]; omega)]; exact hA.cells
        uniq' := hg'.uniq
        rinv' := hri'
        noParam := fun p hp => by
          rcases SState.valAt_pushBind s' b' p with e | e <;> rw [e]
          · exact hA.noParam p hp
          · rw [hbv]; exact FT.const _ _
        order := fun a b ha hb => hA.order a b (hlive' a ha) (hlive' b hb)
        mono := fun a b ha hb => hA.mono a b (hlive' a ha) (hlive' b hb) }
      good := hg
      good' := hg'
      counter := h.counter
      srange := h.srange
      bsites := h.bsites
      psites := fun m y hm hy hf => SState.mem_positions_pushBind _ _ (h.psites m y (hlive m hm) hy hf)
      heldAll := h.heldAll
      orderAll := h.orderAll
      monoAll := h.monoAll }
  · have hlI : b.ty.label = some (σ l) := by rw [hlab, hl]; rfl
    rw [pushBindShaped_some hlI hF] at hg ⊢
    rw [pushBindShaped_some hl hF'] at hg' hri' ⊢
    have hup : upPos ks.length (.bind s.topIdx F.binds.length) = .bind s'.topIdx F'.binds.length := by
      rw [htopC, ← hTR.1]; rfl
    rw [← hup] at hg' hri' ⊢
    have hp : (Pos.bind s.topIdx F.binds.length).frameOf = s₀.topIdx := htopI
    have hdeadI : ¬ s.Live (σ l) → s.lent (σ l) = [] := (hres (σ l) hlI).2
    have hdeadC : ¬ s'.Live l → s'.lent l = [] := (hresD l hl).2
    -- the relation: the take, the push, the hold
    have hr₁ := frameRel_takeLabel' hA.rel hs₀ hA.uniq hA.shape hA.shape' l (h.srange l)
    have hr₂ := frameRel_pushBind hr₁ (shapeAt_takeLabel hA.shape' l) hBR
    have hrec : (σ l ∉ ks → ((s.takeLabel (σ l)).pushBind b).heldMem (σ l) = ((s'.takeLabel l).pushBind b').heldMem l) ∧
        ((s.takeLabel (σ l)).pushBind b).heldTy (σ l) = ((s'.takeLabel l).pushBind b').heldTy l := by
      show (σ l ∉ ks → (s.takeLabel (σ l)).heldMem (σ l) = (s'.takeLabel l).heldMem l) ∧
        (s.takeLabel (σ l)).heldTy (σ l) = (s'.takeLabel l).heldTy l
      rw [takeLabel_heldMem', takeLabel_heldMem', takeLabel_heldTy', takeLabel_heldTy']
      by_cases hlv : s'.Live l
      · exact hA.rel.held l hlv
      · exact ⟨(h.heldAll l (hresD l hl).1).2, (h.heldAll l (hresD l hl).1).1⟩
    have hsites : ∀ x : Site, x.pos.frameOf = s₀.topIdx →
        (x ∈ ((s.takeLabel (σ l)).pushBind b).lent (σ l) ↔ upSite ks.length x ∈ ((s'.takeLabel l).pushBind b').lent l) := by
      intro x hx
      show x ∈ (s.takeLabel (σ l)).lent (σ l) ↔ upSite ks.length x ∈ (s'.takeLabel l).lent l
      rw [takeLabel_lent', takeLabel_lent']
      by_cases hlv : s'.Live l
      · obtain ⟨q, -, hq⟩ := (SState.live_iff s _).1 (live_img hA.rel hA.shape hlv)
        exact hA.rel.lentTop l x hx ⟨q, hq⟩
      · have hlvI : ¬ s.Live (σ l) := fun h' => hlv ((live_corr h hs₀ l).1 h')
        rw [hdeadI hlvI, hdeadC hlv]; simp
    have hsa₂' : ShapeAt ((s'.takeLabel l).pushBind b') :=
      fun q n hq => SState.mem_positions_pushBind _ _ (shapeAt_takeLabel hA.shape' l q n hq)
    have hr₃ := frameRel_hold hr₂ hp (takeLabel_noHolder hA.uniq' hA.shape' l) hrec hsites (h.srange l) hsa₂'
    generalize hS₃ : ({ (s.takeLabel (σ l)).pushBind b with
      shape := fun q => if q = Pos.bind s.topIdx F.binds.length then some (σ l) else ((s.takeLabel (σ l)).pushBind b).shape q } :
      SState) = S₃ at hg hr₃ ⊢
    generalize hS₃' : ({ (s'.takeLabel l).pushBind b' with
      shape := fun q => if q = upPos ks.length (Pos.bind s.topIdx F.binds.length) then some l
        else ((s'.takeLabel l).pushBind b').shape q } : SState) = S₃' at hg' hri' hr₃ ⊢
    -- what the new states are
    have hshI : ∀ q, S₃.shape q = if q = .bind s.topIdx F.binds.length then some (σ l)
        else (s.takeLabel (σ l)).shape q := fun q => by rw [← hS₃]; rfl
    have hshC : ∀ q, S₃'.shape q = if q = upPos ks.length (.bind s.topIdx F.binds.length) then some l
        else (s'.takeLabel l).shape q := fun q => by rw [← hS₃']; rfl
    have hlentI : S₃.lent = s.lent := by rw [← hS₃]; exact takeLabel_lent' _ _
    have hposI : ∀ q ∈ s.positions, q ∈ S₃.positions := fun q hq => by
      rw [← hS₃]
      show q ∈ ((s.takeLabel (σ l)).pushBind b).positions
      exact SState.mem_positions_pushBind _ _ (by rw [SState.takeLabel_positions]; exact hq)
    have hnextI : S₃.nextLoan = s.nextLoan := by rw [← hS₃]; exact takeLabel_nextLoan' _ _
    have hnextC : S₃'.nextLoan = s'.nextLoan := by rw [← hS₃']; exact takeLabel_nextLoan' _ _
    have hrecI : S₃.heldTy = s.heldTy ∧ S₃.heldMem = s.heldMem := by
      rw [← hS₃]; exact ⟨takeLabel_heldTy' _ _, takeLabel_heldMem' _ _⟩
    have hrecC : S₃'.heldTy = s'.heldTy ∧ S₃'.heldMem = s'.heldMem := by
      rw [← hS₃']; exact ⟨takeLabel_heldTy' _ _, takeLabel_heldMem' _ _⟩
    have hliveI : ∀ a, S₃.Live a → s.Live a ∨ (a = σ l ∧ ¬ s.Live (σ l)) := fun a ha => by
      obtain ⟨q, -, hq⟩ := (SState.live_iff _ a).1 ha
      rw [hshI] at hq
      split at hq
      · cases hq
        by_cases hlv : s.Live (σ l)
        · exact .inl hlv
        · exact .inr ⟨rfl, hlv⟩
      · have hq' : s.shape q = some a := SState.takeLabel_shape_some hq
        exact .inl ((SState.live_iff s a).2 ⟨q, hA.shape q a hq', hq'⟩)
    have hliveC : ∀ a, S₃'.Live a → a < s'.nextLoan := fun a ha => by
      obtain ⟨q, -, hq⟩ := (SState.live_iff _ a).1 ha
      rw [hshC] at hq
      split at hq
      · cases hq; exact (hresD l hl).1
      · have hq' : s'.shape q = some a := SState.takeLabel_shape_some hq
        exact hltC a ((SState.live_iff s' a).2 ⟨q, hA.shape' q a hq', hq'⟩)
    exact
    { acc :=
      { rel := hr₃
        uniq := hg.uniq
        shape := fun p l hp => (hg.acyc.2.2 p l hp).1
        lend := by
          obtain ⟨rk, hrk⟩ := hA.lend
          refine ⟨rk, fun a c y ha hy hc => ?_⟩
          rw [hlentI] at hy
          rw [hshI] at hc
          split at hc
          · rename_i e
            rcases hliveI a ha with ha' | ⟨rfl, hd⟩
            · exact absurd (e ▸ h.psites a y ha' hy (by rw [e]; exact hp)) (not_mem_newBind hF)
            · rw [hdeadI hd] at hy; cases hy
          · have hc' : s.shape y.pos = some c := SState.takeLabel_shape_some hc
            rcases hliveI a ha with ha' | ⟨rfl, hd⟩
            · exact hrk a c y ha' hy hc'
            · rw [hdeadI hd] at hy; cases hy
        pfill := fun k hk y hy hyf => hA.pfill k hk y (by rw [hlentI] at hy; exact hy) hyf
        held := hg.held
        cells := by
          rw [← hS₃']
          show ks.length ≤ ((((s'.takeLabel l).pushBind b').env.headD {}).binds.length)
          have htopT : (s'.takeLabel l).topIdx ≠ 0 := by
            have e := htopC
            unfold SState.topIdx at e ⊢; rw [(envLe_takeLabel s' l).1]; omega
          rw [pushBind_modTop, modTop_headD _ _ htopT, headD_len_takeLabel]
          exact hA.cells
        uniq' := hg'.uniq
        rinv' := hri'
        noParam := fun p hp => by
          rw [← hS₃']
          show Ochr.Meaning.FT _ (((s'.takeLabel l).pushBind b').valAt p)
          rcases SState.valAt_pushBind (s'.takeLabel l) b' p with e | e <;> rw [e]
          · rcases SState.takeLabel_valAt s' l p with e' | e' <;> rw [e']
            · exact hA.noParam p hp
            · exact FT.const _ _
          · rw [hbv]; exact FT.const _ _
        order := fun a c ha hc => h.orderAll a c (hliveC a ha) (hliveC c hc)
        mono := fun a c ha hc => h.monoAll a c (hliveC a ha) (hliveC c hc) }
      good := hg
      good' := hg'
      counter := by rw [hnextI]; exact h.counter
      srange := h.srange
      bsites := fun m y hy hf => h.bsites m y (by rw [hlentI] at hy; exact hy) hf
      psites := fun m y hm hy hf => by
        rw [hlentI] at hy
        rcases hliveI m hm with hm' | ⟨rfl, hd⟩
        · exact hposI _ (h.psites m y hm' hy hf)
        · rw [hdeadI hd] at hy; cases hy
      heldAll := fun n hn => by
        rw [hnextC] at hn
        rw [hrecI.1, hrecI.2, hrecC.1, hrecC.2]
        exact h.heldAll n hn
      orderAll := fun a c ha hc => h.orderAll a c (hnextC ▸ ha) (hnextC ▸ hc)
      monoAll := fun a c ha hc => h.monoAll a c (hnextC ▸ ha) (hnextC ▸ hc) }
end

/-! ## A `let`'s end and drop -/

section
variable {K : RunCtx} {φ : Future} {σ : Nat → Nat} {s₀ : SState} {ks : List Nat}

/-- **The drop of the top frame's last binding** (the paper's (O8)) keeps the internal relation, given that no live label
is lent at it (a `let`'s end makes sure: `endLabel_noSiteAt`, `access_noLiveSiteAt`). -/
theorem dropLast_frameInv {t t' : SState} (h : FrameInv K φ σ s₀ ks t t') {F : SFrame} (hF : t.env.getLast? = some F)
    (hno : ∀ m (y : Site), t.Live m → y ∈ t.lent m → y.pos ≠ .bind t.topIdx (F.binds.length - 1))
    (hg : Strict.SGood K.dm K.Γ φ t.dropLast) (hg' : Strict.SGood K.dm K.Γ φ t'.dropLast)
    (hri' : SState.RInv (fun _ => False) t'.dropLast) :
    FrameInv K φ σ s₀ ks t.dropLast t'.dropLast := by
  have hA := h.acc
  obtain ⟨F₀, F₀', hF₀, hF₀', -⟩ := top_rel hA.rel
  have hdrop : t.dropped = some (.bind t.topIdx (F.binds.length - 1)) := by unfold SState.dropped; rw [hF]
  have hlive : ∀ (u : SState) y, u.dropLast.Live y → u.Live y := fun u y hy => by
    obtain ⟨q, hq, hs⟩ := (SState.live_iff _ y).1 hy
    obtain ⟨hq1, hq2⟩ := SState.mem_positions_dropLast hq
    rw [SState.dropLast_shape, if_neg hq2] at hs
    exact (SState.live_iff u y).2 ⟨q, hq1, hs⟩
  have hsh : ∀ q y, t.dropLast.shape q = some y → t.shape q = some y := fun q y hq => by
    rw [SState.dropLast_shape] at hq; split at hq
    · cases hq
    · exact hq
  exact
  { acc :=
    { rel := frameRel_dropLast hA.rel hA.shape'
      uniq := hg.uniq
      shape := fun p l hp => (hg.acyc.2.2 p l hp).1
      lend := by
        obtain ⟨rk, hrk⟩ := hA.lend
        exact ⟨rk, fun a b y ha hy hb => hrk a b y (hlive t a ha) hy (hsh _ _ hb)⟩
      pfill := hA.pfill
      held := hg.held
      cells := by
        have e : t'.dropLast.env.headD {} = t'.env.headD {} := by
          rw [dropLast_eq t' hF₀']; exact modTop_headD t' _ (by rw [topIdx_cl hA.rel]; omega)
        rw [e]; exact hA.cells
      uniq' := hg'.uniq
      rinv' := hri'
      noParam := fun p hp => by
        by_cases hq : some p = t'.dropped
        · have : p ∉ t'.dropLast.positions := fun hm => (SState.mem_positions_dropLast hm).2 hq
          rw [SState.valAt_of_not_mem _ _ this]; exact FT.const _ _
        · rw [SState.valAt_dropLast _ _ hq]; exact hA.noParam p hp
      order := fun a b ha hb => hA.order a b (hlive t' a ha) (hlive t' b hb)
      mono := fun a b ha hb => hA.mono a b (hlive t' a ha) (hlive t' b hb) }
    good := hg
    good' := hg'
    counter := h.counter
    srange := h.srange
    bsites := h.bsites
    psites := fun m y hm hy hf => by
      refine SState.mem_positions_dropLast' (h.psites m y (hlive t m hm) hy hf) ?_
      rw [hdrop]; intro e; exact hno m y (hlive t m hm) hy (Option.some.inj e)
    heldAll := h.heldAll
    orderAll := h.orderAll
    monoAll := h.monoAll }

/-- A result held at a temporary stays so through the drop of a binding. -/
theorem ResAtTemp.dropLast {t : SState} {lab : Option Nat} (h : ResAtTemp s₀ t lab) (hu : t.Uniq)
    (htop : t.topIdx = s₀.topIdx) : ResAtTemp s₀ t.dropLast lab := fun k hk => by
  have htemp : ∀ j, t.dropLast.shape (.temp s₀.topIdx j) = t.shape (.temp s₀.topIdx j) := fun j => by
    rw [SState.dropLast_shape, if_neg]; unfold SState.dropped; split <;> simp
  refine ⟨fun hl => ?_, fun hd => ?_⟩
  · obtain ⟨q, hq, hs⟩ := (SState.live_iff _ k).1 hl
    obtain ⟨hq1, hq2⟩ := SState.mem_positions_dropLast hq
    rw [SState.dropLast_shape, if_neg hq2] at hs
    obtain ⟨j, hj⟩ := (h k hk).1 ((SState.live_iff t k).2 ⟨q, hq1, hs⟩)
    exact ⟨j, by rw [htemp]; exact hj⟩
  · show t.lent k = []
    refine (h k hk).2 fun hl => hd ?_
    obtain ⟨j, hj⟩ := (h k hk).1 hl
    have hpos : Pos.temp s₀.topIdx j ∈ t.positions := by
      obtain ⟨q, hq, hs⟩ := (SState.live_iff t k).1 hl
      rw [hu q _ k hs hj] at hq; exact hq
    refine (SState.live_iff _ k).2 ⟨_, SState.mem_positions_dropLast' hpos ?_, by rw [htemp]; exact hj⟩
    unfold SState.dropped; split <;> simp

end

/-! ## A `let`'s end -/

section
variable {K : RunCtx} {φ : Future} {σ : Nat → Nat} {s₀ : SState} {ks : List Nat}

/-- The closure's result stays so through the drop of a binding: its label, if live, is held at a temporary (its in-place
image is, `ResAtTemp`, and holders correspond), which the drop keeps. -/
theorem ResDead.dropLast' {t t' : SState} {lab' : Option Nat} (hD : ResDead t' lab') (h : FrameInv K φ σ s₀ ks t t')
    (hRes : ResAtTemp s₀ t (lab'.map σ)) : ResDead t'.dropLast lab' := fun k hk => by
  refine ⟨(hD k hk).1, fun hd => (hD k hk).2 fun hl => hd ?_⟩
  obtain ⟨j, hj⟩ := (hRes (σ k) (by rw [hk]; rfl)).1 (live_img h.acc.rel h.acc.shape hl)
  have hj' : t'.shape (upPos ks.length (.temp s₀.topIdx j)) = some k := by
    have := h.acc.rel.topShape (.temp s₀.topIdx j) rfl
    rw [hj] at this
    cases e : t'.shape (upPos ks.length (.temp s₀.topIdx j)) with
    | none => rw [e] at this; cases this
    | some k' => rw [e] at this; rw [h.acc.rel.inj _ _ (Option.some.inj this)]
  have hnd : some (upPos ks.length (.temp s₀.topIdx j)) ≠ t'.dropped := by
    unfold SState.dropped; split <;> simp [upPos]
  refine (SState.live_iff _ k).2 ⟨_, SState.mem_positions_dropLast' (h.acc.shape' _ _ hj') hnd, ?_⟩
  rw [SState.dropLast_shape, if_neg hnd]; exact hj'

theorem getLast_of_envLe {t u : SState} (h : EnvLe t u) {F : SFrame} (hF : t.env.getLast? = some F) :
    ∃ F₂ : SFrame, u.env.getLast? = some F₂ ∧ F₂.binds.length = F.binds.length ∧ u.topIdx = t.topIdx := by
  obtain ⟨F₂, hF₂, hb, -⟩ := h.2 t.topIdx F (env_top t hF)
  refine ⟨F₂, ?_, hb, by unfold SState.topIdx; rw [h.1]⟩
  rw [List.getLast?_eq_getElem?, h.1]; exact hF₂

end

section
variable {K : RunCtx} {φ : Future} {σ : Nat → Nat} {s₀ : SState} {ks : List Nat}

open Classical in
/-- **A `let`'s end and drop** (the paper's rows for `let`: (O3) for the held borrow's end, (O4) for `letLenders`' access,
(O8) for the drop): the binding holds corresponding labels or none on the two sides; the strict tests hold together; the
states after are related. The dropped position is emptied of live labels' sites by the end (`endLabel_noSiteAt`,
`access_noLiveSiteAt`). -/
theorem letEnd_agree (hs₀ : FrameStart s₀ ks) {a a' : SState} (ha : FrameInv K φ σ s₀ ks a a') (r : Sem) {Rr Rr' : TyS}
    (hRr : Rr = { Rr' with label := Rr'.label.map σ }) (hresa : ResAtTemp s₀ a Rr.label ∧ ResDead a' Rr'.label) :
    FrameAgreeI K φ σ s₀ ks
      (if (match (match a.env.getLast? with
            | some fr => a.shape (.bind a.topIdx (fr.binds.length - 1))
            | none => none) with
          | some l => EndOk K φ a l
          | none => LetLendersOk K φ a) then
        some ((r, Rr), (match (match a.env.getLast? with
            | some fr => a.shape (.bind a.topIdx (fr.binds.length - 1))
            | none => none) with
          | some l => a.endLabel l
          | none => letLenders a).dropLast)
       else none)
      (if (match (match a'.env.getLast? with
            | some fr => a'.shape (.bind a'.topIdx (fr.binds.length - 1))
            | none => none) with
          | some l => EndOk K φ a' l
          | none => LetLendersOk K φ a') then
        some ((r, Rr'), (match (match a'.env.getLast? with
            | some fr => a'.shape (.bind a'.topIdx (fr.binds.length - 1))
            | none => none) with
          | some l => a'.endLabel l
          | none => letLenders a').dropLast)
       else none) := by
  obtain ⟨F, F', hF, hF', hTR⟩ := top_rel ha.acc.rel
  have htopI : a.topIdx = s₀.topIdx := topIdx_eq ha.acc.rel
  have htopC : a'.topIdx = 1 := topIdx_cl ha.acc.rel
  rw [hF, hF']
  dsimp only
  have hp : (Pos.bind a.topIdx (F.binds.length - 1)).frameOf = s₀.topIdx := htopI
  have hup : upPos ks.length (.bind a.topIdx (F.binds.length - 1)) = .bind a'.topIdx (F'.binds.length - 1) := by
    rw [htopC, ← hTR.1]; rfl
  have hsh := ha.acc.rel.topShape _ hp
  rw [hup] at hsh
  have hdropI : a.dropped = some (.bind a.topIdx (F.binds.length - 1)) := by unfold SState.dropped; rw [hF]
  have hdropC : a'.dropped = some (.bind a'.topIdx (F'.binds.length - 1)) := by unfold SState.dropped; rw [hF']
  rcases Option.eq_none_or_eq_some (a'.shape (.bind a'.topIdx (F'.binds.length - 1))) with hl | ⟨l, hl⟩
  · have hsI : a.shape (.bind a.topIdx (F.binds.length - 1)) = none := by rw [hsh, hl]; rfl
    simp only [hsI, hl]
    have hok := (frameRel_access φ hs₀ ha.acc hp (dataHit [])).2
    have hacc := (frameRel_access φ hs₀ ha.acc hp (dataHit [])).1
    rw [hup] at hok hacc
    have eL : LetLendersOk K φ a ↔ AccessOk K φ a (.bind a.topIdx (F.binds.length - 1)) (dataHit []) := by
      unfold LetLendersOk; rw [hF]
    have eL' : LetLendersOk K φ a' ↔ AccessOk K φ a' (.bind a'.topIdx (F'.binds.length - 1)) (dataHit []) := by
      unfold LetLendersOk; rw [hF']
    have eA : letLenders a = a.access (.bind a.topIdx (F.binds.length - 1)) (dataHit []) := by unfold letLenders; rw [hF]
    have eA' : letLenders a' = a'.access (.bind a'.topIdx (F'.binds.length - 1)) (dataHit []) := by
      unfold letLenders; rw [hF']
    by_cases he : LetLendersOk K φ a'
    · rw [if_pos (eL.2 (hok.2 (eL'.1 he))), if_pos he, eA, eA']
      have hgA := Strict.access_sgood ha.good _ _ (hok.2 (eL'.1 he))
      have hgA' := Strict.access_sgood ha.good' _ _ (eL'.1 he)
      have hE := ha.of_ops hacc hgA hgA' (shrinks_access _ _ _) (shrinks_access _ _ _)
      obtain ⟨F₂, hF₂, hb₂, ht₂⟩ := getLast_of_envLe (envLe_access a _ (dataHit [])) hF
      obtain ⟨F₂', hF₂', hb₂', ht₂'⟩ := getLast_of_envLe (envLe_access a' _ (dataHit [])) hF'
      have hnoneI : a.shape (.bind a.topIdx (F.binds.length - 1)) = none := by rw [hsh, hl]; rfl
      have hclear : (a.access (.bind a.topIdx (F.binds.length - 1)) (dataHit [])).shape
          (.bind a.topIdx (F.binds.length - 1)) = none := by
        cases e : (a.access (.bind a.topIdx (F.binds.length - 1)) (dataHit [])).shape (.bind a.topIdx (F.binds.length - 1)) with
        | none => rfl
        | some x => rw [(shrinks_access _ _ _).shape _ _ e] at hnoneI; cases hnoneI
      have hclear' : (a'.access (.bind a'.topIdx (F'.binds.length - 1)) (dataHit [])).shape
          (.bind a'.topIdx (F'.binds.length - 1)) = none := by
        cases e : (a'.access (.bind a'.topIdx (F'.binds.length - 1)) (dataHit [])).shape
            (.bind a'.topIdx (F'.binds.length - 1)) with
        | none => rfl
        | some x => rw [(shrinks_access _ _ _).shape _ _ e] at hl; cases hl
      have hind : ∀ r x, (a.access (.bind a.topIdx (F.binds.length - 1)) (dataHit [])).dropped = some r →
          (a.access (.bind a.topIdx (F.binds.length - 1)) (dataHit [])).shape r = some x → ∀ p,
          Indep x ((a.access (.bind a.topIdx (F.binds.length - 1)) (dataHit [])).valAt p) := fun r x hr hx => by
        unfold SState.dropped at hr; rw [hF₂, ht₂] at hr; simp only [hb₂, Option.some.injEq] at hr; subst hr
        rw [hclear] at hx; cases hx
      have hind' : ∀ r x, (a'.access (.bind a'.topIdx (F'.binds.length - 1)) (dataHit [])).dropped = some r →
          (a'.access (.bind a'.topIdx (F'.binds.length - 1)) (dataHit [])).shape r = some x → ∀ p,
          Indep x ((a'.access (.bind a'.topIdx (F'.binds.length - 1)) (dataHit [])).valAt p) := fun r x hr hx => by
        unfold SState.dropped at hr; rw [hF₂', ht₂'] at hr; simp only [hb₂', Option.some.injEq] at hr; subst hr
        rw [hclear'] at hx; cases hx
      have hD := dropLast_frameInv hE hF₂ (fun m y hm hy e => access_noLiveSiteAt a _ m y hm hy
          (by rw [e, ht₂, hb₂]))
        (Strict.sgood_dropLast hgA hind) (Strict.sgood_dropLast hgA' hind') (SState.dropLast_rinv hE.acc.rinv' hind')
      have hres1 := hresa.1.shrinks ha.acc.uniq (shrinks_access a (.bind a.topIdx (F.binds.length - 1)) (dataHit []))
      have hres2 := hresa.2.shrinks (shrinks_access a' (.bind a'.topIdx (F'.binds.length - 1)) (dataHit []))
      rw [hRr] at hres1
      refine ⟨rfl, hRr, hD, ?_, hres2.dropLast' hE hres1⟩
      rw [hRr]
      exact hres1.dropLast hE.acc.uniq (by rw [ht₂, htopI])
    · rw [if_neg (fun h => he (eL'.2 (hok.1 (eL.1 h)))), if_neg he]; trivial
  · have hsI : a.shape (.bind a.topIdx (F.binds.length - 1)) = some (σ l) := by rw [hsh, hl]; rfl
    simp only [hsI, hl]
    have hlive : a'.Live l := (SState.live_iff a' l).2 ⟨_, ha.acc.shape' _ _ hl, hl⟩
    have hok := endOk_corr K φ ha.acc.rel ha.acc.uniq ha.acc.shape ha.acc.held ha.acc.loc hlive
    by_cases he : EndOk K φ a' l
    · rw [if_pos (hok.2 he), if_pos he]
      have hgE := Strict.endLabel_sgood ha.good (σ l) (hok.2 he)
      have hgE' := Strict.endLabel_sgood ha.good' l he
      have hE := ha.of_ops (AccInv.endLabel hs₀ ha.acc hlive) hgE hgE' (shrinks_endLabel _ _) (shrinks_endLabel _ _)
      have hhI : a.holderOf (σ l) = some (.bind a.topIdx (F.binds.length - 1)) := by
        have hs : a.shape (.bind a.topIdx (F.binds.length - 1)) = some (σ l) := by rw [hsh, hl]; rfl
        obtain ⟨q, hq⟩ := SState.holderOf_of_live ((SState.live_iff a _).2 ⟨_, ha.acc.shape _ _ hs, hs⟩)
        rw [hq, ha.acc.uniq _ _ _ (SState.holderOf_spec hq).2 hs]
      have hhC : a'.holderOf l = some (.bind a'.topIdx (F'.binds.length - 1)) := by
        obtain ⟨q, hq⟩ := SState.holderOf_of_live hlive
        rw [hq, ha.acc.uniq' _ _ _ (SState.holderOf_spec hq).2 hl]
      obtain ⟨F₂, hF₂, hb₂, ht₂⟩ := getLast_of_envLe (envLe_endLabel a (σ l)) hF
      obtain ⟨F₂', hF₂', hb₂', ht₂'⟩ := getLast_of_envLe (envLe_endLabel a' l) hF'
      have hclear : (a.endLabel (σ l)).shape (.bind a.topIdx (F.binds.length - 1)) = none := by
        rw [SState.endLabel_eq hhI, SState.endAt_shape]; simp
      have hclear' : (a'.endLabel l).shape (.bind a'.topIdx (F'.binds.length - 1)) = none := by
        rw [SState.endLabel_eq hhC, SState.endAt_shape]; simp
      have hdropE : (a.endLabel (σ l)).dropped = some (.bind a.topIdx (F.binds.length - 1)) := by
        unfold SState.dropped; rw [hF₂, ht₂]; simp only [hb₂]
      have hdropE' : (a'.endLabel l).dropped = some (.bind a'.topIdx (F'.binds.length - 1)) := by
        unfold SState.dropped; rw [hF₂', ht₂']; simp only [hb₂']
      have hind : ∀ r x, (a.endLabel (σ l)).dropped = some r → (a.endLabel (σ l)).shape r = some x → ∀ p,
          Indep x ((a.endLabel (σ l)).valAt p) := fun r x hr hx => by
        rw [hdropE] at hr; cases hr; rw [hclear] at hx; cases hx
      have hind' : ∀ r x, (a'.endLabel l).dropped = some r → (a'.endLabel l).shape r = some x → ∀ p,
          Indep x ((a'.endLabel l).valAt p) := fun r x hr hx => by
        rw [hdropE'] at hr; cases hr; rw [hclear'] at hx; cases hx
      have hD := dropLast_frameInv hE hF₂ (fun m y hm hy e => endLabel_noSiteAt ha.acc.lend hhI m y hy
          (by rw [e, ht₂, hb₂]))
        (Strict.sgood_dropLast hgE hind) (Strict.sgood_dropLast hgE' hind') (SState.dropLast_rinv hE.acc.rinv' hind')
      have hres1 := hresa.1.shrinks ha.acc.uniq (shrinks_endLabel a (σ l))
      have hres2 := hresa.2.shrinks (shrinks_endLabel a' l)
      rw [hRr] at hres1
      refine ⟨rfl, hRr, hD, ?_, hres2.dropLast' hE hres1⟩
      rw [hRr]
      exact hres1.dropLast hE.acc.uniq (by rw [ht₂, htopI])
    · rw [if_neg (fun h => he (hok.1 h)), if_neg he]; trivial

end

/-! ## The clause -/

section
variable {K : RunCtx} {ρ : Assignment} {φ : Future} {σ : Nat → Nat} {s₀ : SState} {ks : List Nat}

/-- `agreeI_bind` with both outcomes' equations (what the fundamental lemma at the bound term needs on each side). -/
theorem agreeI_bind_eq2 {o o' : Option (Res × SState)} (h : FrameAgreeI K φ σ s₀ ks o o')
    {f f' : Res × SState → Option (Res × SState)}
    (hf : ∀ (v : Sem) (R R' : TyS) (t t' : SState), o = some ((v, R), t) → o' = some ((v, R'), t') →
      R = { R' with label := R'.label.map σ } → FrameInv K φ σ s₀ ks t t' → ResAtTemp s₀ t R.label ∧ ResDead t' R'.label →
      FrameAgreeI K φ σ s₀ ks (f ((v, R), t)) (f' ((v, R'), t'))) :
    FrameAgreeI K φ σ s₀ ks (o >>= f) (o' >>= f') := by
  match o, o', h with
  | none, none, _ => trivial
  | some ((v, R), t), some ((v', R'), t'), ⟨e, hR, hI, hres⟩ =>
    simp only at e; subst e; exact hf v R R' t t' rfl rfl hR hI hres

theorem runFrameI_letIn (hs₀ : FrameStart s₀ ks) {x : Hint} {u w : Term}
    (hfu : Strict.Fund K ρ φ u) (ihu : TermFrame K ρ φ σ s₀ ks u) (ihw : TermFrame K ρ φ σ s₀ ks w) :
    TermFrame K ρ φ σ s₀ ks (.letIn x u w) := by
  intro tl hint s s' hI
  rw [runT]; dsimp only
  rw [scopeOf_corr hI.acc.rel]
  refine agreeI_erasedIf _ hI ?_
  refine agreeI_bind_eq2 (ihu false _ s s' hI) fun v R R' t t' hrun hrun' hR ht hres => ?_
  dsimp only
  rw [scopeOf_corr hI.acc.rel]
  generalize K.D.declOf (scopeOf s') u = d
  -- the push
  obtain ⟨F₀, F₀', hF₀, hF₀', -⟩ := top_rel ht.acc.rel
  have hne : t.env ≠ [] := fun e => by rw [e] at hF₀; cases hF₀
  have hne' : t'.env ≠ [] := fun e => by rw [e] at hF₀'; cases hF₀'
  obtain ⟨hgr, hlab, hlou, -⟩ := hfu false _ s t (v, R) hI.good hrun
  obtain ⟨hgr', hlab', hlou', -⟩ := hfu false _ s' t' (v, R') hI.good' hrun'
  have hgP := Strict.sgood_pushBindShaped ht.good { ty := R, val := fun _ => v, decl := d } rfl hgr hlab hlou hne
  have hgP' := Strict.sgood_pushBindShaped ht.good' { ty := R', val := fun _ => v, decl := d } rfl hgr' hlab' hlou' hne'
  have hriP' := SState.pushBindShaped_rinv ht.acc.rinv' { ty := R', val := fun _ => v, decl := d } v rfl
    (fun l hl => ⟨(hlou' l hl).1.elim .inl (fun h => .inr (.inr h)), (hlou' l hl).2⟩)
  have hBR : BindRen σ { ty := R, val := fun _ => v, decl := d } { ty := R', val := fun _ => v, decl := d } :=
    ⟨hR, rfl, rfl, fun _ => rfl⟩
  have hP := pushBindShaped_frameInv ht hs₀ hBR rfl hres.1 hres.2 hgP hgP' hriP'
  -- the body, then the end and the drop
  refine agreeI_bind_eq2 (ihw tl _ _ _ hP) fun r Rr Rr' a a' _ _ hRr ha hresa => ?_
  dsimp only
  exact letEnd_agree hs₀ ha r hRr hresa


/-- **A discarded value's end** (`;`, [Drop] of a discarded value: the paper's (O3)): the same label (renamed) or none on
the two sides; the strict tests together; the states after related. -/
theorem discard_agree (hs₀ : FrameStart s₀ ks) {t t' : SState} (h : FrameInv K φ σ s₀ ks t t') (R' : TyS) :
    (DiscardOk K φ { R' with label := R'.label.map σ } t ↔ DiscardOk K φ R' t') ∧
      (DiscardOk K φ R' t' → FrameInv K φ σ s₀ ks (discardEnd { R' with label := R'.label.map σ } t) (discardEnd R' t')) := by
  unfold DiscardOk discardEnd
  rcases Option.eq_none_or_eq_some R'.label with hl | ⟨l, hl⟩
  · simp only [hl, Option.map_none]; exact ⟨trivial, fun _ => h⟩
  · simp only [hl, Option.map_some]
    by_cases hlv : t'.Live l
    · have hok := endOk_corr K φ h.acc.rel h.acc.uniq h.acc.shape h.acc.held h.acc.loc hlv
      refine ⟨hok, fun he => ?_⟩
      exact h.of_ops (AccInv.endLabel hs₀ h.acc hlv) (Strict.endLabel_sgood h.good (σ l) (hok.2 he))
        (Strict.endLabel_sgood h.good' l he) (shrinks_endLabel _ _) (shrinks_endLabel _ _)
    · have hlvI : ¬ t.Live (σ l) := fun h' => hlv ((live_corr h hs₀ l).1 h')
      have hn : t.holderOf (σ l) = none := by
        cases e : t.holderOf (σ l) with
        | none => rfl
        | some r => exact absurd ((SState.live_iff t _).2 ⟨r, (SState.holderOf_spec e).1, (SState.holderOf_spec e).2⟩) hlvI
      have hn' : t'.holderOf l = none := by
        cases e : t'.holderOf l with
        | none => rfl
        | some r => exact absurd ((SState.live_iff t' _).2 ⟨r, (SState.holderOf_spec e).1, (SState.holderOf_spec e).2⟩) hlv
      rw [SState.endLabel_of_none hn, SState.endLabel_of_none hn']
      refine ⟨⟨fun _ r hr => (by rw [hn'] at hr; cases hr), fun _ r hr => (by rw [hn] at hr; cases hr)⟩, fun _ => h⟩

/-- **The frame property's clause for `;`** (the paper's row "`let` and `;` with labels"): the first term (the
induction), the discarded value's end (`discard_agree`), the second term (the induction). -/
theorem runFrameI_seq (hs₀ : FrameStart s₀ ks) {u w : Term}
    (ihu : TermFrame K ρ φ σ s₀ ks u) (ihw : TermFrame K ρ φ σ s₀ ks w) :
    TermFrame K ρ φ σ s₀ ks (.seq u w) := by
  intro tl hint s s' hI
  rw [runT]; dsimp only
  rw [scopeOf_corr hI.acc.rel]
  refine agreeI_erasedIf _ hI ?_
  rw [sm_bind_eq, sm_bind_eq]
  refine agreeI_obind (ihu false _ s s' hI) fun r' t t' ht => ?_
  dsimp only
  rw [sm_bind_eq, sm_bind_eq]
  obtain ⟨hok, hinv⟩ := discard_agree hs₀ ht r'.2
  have e : (renRes σ r').2 = { r'.2 with label := r'.2.label.map σ } := rfl
  rw [e]
  unfold SM.guardMod
  by_cases hd : DiscardOk K φ r'.2 t'
  · rw [if_pos (hok.2 hd), if_pos hd]
    exact ihw tl _ _ _ (hinv hd)
  · rw [if_neg (fun h' => hd (hok.1 h')), if_neg hd]; trivial

end

end Ochr.Meaning.Steps.Form.FrameEnd
