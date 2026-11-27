import Ochr.Meaning.Steps.FrameAssign

/-!
# The read clause of the frame property (lead35; docs/31 D225)

`.place p`: a read of a place of the callee's frame, by its declared reading a copy (`readCopy_agree`, the call clause's
head) or a move: [Access] for the content ((O4), (O2)), `⊥` written in its place ((O5)), and a borrow held at a root moved
on with the value, parked at a fresh temporary ((O8), `repark_frameInvS`).
-/

namespace Ochr.Meaning.Steps.Form.FrameEnd

open Ochr Ochr.Meaning Ochr.Meaning.Strict

/-- A moved borrow parked at a fresh temporary (`readPlace`'s move of a whole position holding a borrow). -/
noncomputable def repark (w : SState) (l : Nat) (v : Sem) : SState := (w.takeLabel l).pushTempShaped (fun _ => v) l

section
variable {K : RunCtx} {φ : Future} {σ : Nat → Nat} {s₀ : SState} {ks : List Nat}

/-- **A moved borrow parked at a fresh temporary** (the paper's (O8)): the label moves from its holder in the callee's
frame to a fresh temporary of it, on both sides; nothing is lent at a temporary of the callee's frame (`bsites`), so
lending stays well founded; the live labels are the same. Both states' structural parts after, and the closure's
locality after, are hypotheses. -/
theorem repark_frameInvS {w w' : SState} (h : FrameInvS K σ s₀ ks w w') (hs₀ : FrameStart s₀ ks) {pos : Pos}
    (hpf : pos.frameOf = s₀.topIdx) {l : Nat} (hsh' : w'.shape (upPos ks.length pos) = some l) (v : Sem)
    (hS : SStruct K.dm (repark w (σ l) v)) (hS' : SStruct K.dm (repark w' l v))
    (hri' : SState.RInv (fun _ => False) (repark w' l v)) :
    FrameInvS K σ s₀ ks (repark w (σ l) v) (repark w' l v) ∧ ResAtTemp s₀ (repark w (σ l) v) (some (σ l)) ∧
      ResDead (repark w' l v) (some l) := by
  have hA := h.acc
  have hsh : w.shape pos = some (σ l) := by rw [hA.rel.topShape pos hpf, hsh']; rfl
  have hlv' : w'.Live l := (SState.live_iff w' l).2 ⟨_, hA.shape' _ _ hsh', hsh'⟩
  have hltl : l < w'.nextLoan := (h.struct'.acyc.2.2 _ _ hsh').2
  obtain ⟨F, F', hF, hF', hTR⟩ := top_rel hA.rel
  obtain ⟨F₁, hF₁, hb₁⟩ := takeLabel_getLast hF (σ l)
  obtain ⟨F₁', hF₁', hb₁'⟩ := takeLabel_getLast hF' l
  have hr₁ := frameRel_takeLabel' hA.rel hs₀ hA.uniq hA.shape hA.shape' l (h.srange l)
  have hr₂ := frameRel_pushTemp hr₁ (shapeAt_takeLabel hA.shape' l) (v := fun _ => v) (v' := fun _ => v) (fun _ => rfl)
  obtain ⟨G, G', hG, hG', hTG⟩ := top_rel hr₁
  have htop₁ : (w.takeLabel (σ l)).topIdx = s₀.topIdx := topIdx_eq hr₁
  have htop₁' : (w'.takeLabel l).topIdx = 1 := topIdx_cl hr₁
  have hnew : upPos ks.length (.temp (w.takeLabel (σ l)).topIdx G.temps.length) =
      .temp (w'.takeLabel l).topIdx G'.temps.length := by
    rw [htop₁', hTG.2.2.1]; rfl
  have hrec : (σ l ∉ ks → ((w.takeLabel (σ l)).pushTemp fun _ => v).heldMem (σ l) =
        ((w'.takeLabel l).pushTemp fun _ => v).heldMem l) ∧
      ((w.takeLabel (σ l)).pushTemp fun _ => v).heldTy (σ l) = ((w'.takeLabel l).pushTemp fun _ => v).heldTy l := by
    show (σ l ∉ ks → (w.takeLabel (σ l)).heldMem (σ l) = (w'.takeLabel l).heldMem l) ∧
      (w.takeLabel (σ l)).heldTy (σ l) = (w'.takeLabel l).heldTy l
    rw [takeLabel_heldMem', takeLabel_heldMem', takeLabel_heldTy', takeLabel_heldTy']
    exact hA.rel.held l hlv'
  have hsites : ∀ x : Site, x.pos.frameOf = s₀.topIdx →
      (x ∈ ((w.takeLabel (σ l)).pushTemp fun _ => v).lent (σ l) ↔
        upSite ks.length x ∈ ((w'.takeLabel l).pushTemp fun _ => v).lent l) := by
    intro x hx
    show x ∈ (w.takeLabel (σ l)).lent (σ l) ↔ upSite ks.length x ∈ (w'.takeLabel l).lent l
    rw [takeLabel_lent', takeLabel_lent']
    exact hA.rel.lentTop l x hx ⟨pos, hsh⟩
  have hsa₂' : ShapeAt ((w'.takeLabel l).pushTemp fun _ => v) :=
    fun q n hq => SState.mem_positions_pushTemp _ _ (shapeAt_takeLabel hA.shape' l q n hq)
  have hnot' : ∀ q, ((w'.takeLabel l).pushTemp fun _ => v).shape q ≠ some l :=
    takeLabel_noHolder hA.uniq' hA.shape' l
  have hpT : (Pos.temp (w.takeLabel (σ l)).topIdx G.temps.length).frameOf = s₀.topIdx := htop₁
  have hr₃ := frameRel_hold hr₂ hpT hnot' hrec hsites (h.srange l) hsa₂'
  rw [hnew] at hr₃
  have eI : repark w (σ l) v = { (w.takeLabel (σ l)).pushTemp (fun _ => v) with
      shape := fun q => if q = .temp (w.takeLabel (σ l)).topIdx G.temps.length then some (σ l)
        else ((w.takeLabel (σ l)).pushTemp fun _ => v).shape q } := pushTempShaped_eq _ _ _ hG
  have eC : repark w' l v = { (w'.takeLabel l).pushTemp (fun _ => v) with
      shape := fun q => if q = .temp (w'.takeLabel l).topIdx G'.temps.length then some l
        else ((w'.takeLabel l).pushTemp fun _ => v).shape q } := pushTempShaped_eq _ _ _ hG'
  rw [← eI, ← eC] at hr₃
  -- what the new states are
  have hshI : ∀ q, (repark w (σ l) v).shape q = if q = .temp (w.takeLabel (σ l)).topIdx G.temps.length then some (σ l)
      else (w.takeLabel (σ l)).shape q := fun q => by rw [eI]; rfl
  have hlentI : (repark w (σ l) v).lent = w.lent := by
    rw [eI]; exact takeLabel_lent' _ _
  have hlentC : (repark w' l v).lent = w'.lent := by
    rw [eC]; exact takeLabel_lent' _ _
  have hnextI : (repark w (σ l) v).nextLoan = w.nextLoan := by rw [eI]; exact takeLabel_nextLoan' _ _
  have hnextC : (repark w' l v).nextLoan = w'.nextLoan := by rw [eC]; exact takeLabel_nextLoan' _ _
  have hrecI : (repark w (σ l) v).heldTy = w.heldTy ∧ (repark w (σ l) v).heldMem = w.heldMem := by
    rw [eI]; exact ⟨takeLabel_heldTy' _ _, takeLabel_heldMem' _ _⟩
  have hrecC : (repark w' l v).heldTy = w'.heldTy ∧ (repark w' l v).heldMem = w'.heldMem := by
    rw [eC]; exact ⟨takeLabel_heldTy' _ _, takeLabel_heldMem' _ _⟩
  have hposI : ∀ q ∈ w.positions, q ∈ (repark w (σ l) v).positions := fun q hq => by
    rw [eI]
    show q ∈ ((w.takeLabel (σ l)).pushTemp fun _ => v).positions
    exact SState.mem_positions_pushTemp _ _ (by rw [SState.takeLabel_positions]; exact hq)
  have hliveI : ∀ a, (repark w (σ l) v).Live a → w.Live a := fun a ha => by
    obtain ⟨q, -, hq⟩ := (SState.live_iff _ a).1 ha
    rw [hshI] at hq
    split at hq
    · cases hq; exact (SState.live_iff w _).2 ⟨pos, hA.shape pos _ hsh, hsh⟩
    · have hq' : w.shape q = some a := SState.takeLabel_shape_some hq
      exact (SState.live_iff w a).2 ⟨q, hA.shape q a hq', hq'⟩
  have hliveC : ∀ a, (repark w' l v).Live a → w'.Live a := fun a ha => by
    obtain ⟨q, -, hq⟩ := (SState.live_iff _ a).1 ha
    rw [eC] at hq
    dsimp only at hq
    split at hq
    · cases hq; exact hlv'
    · have hq' : w'.shape q = some a := SState.takeLabel_shape_some hq
      exact (SState.live_iff w' a).2 ⟨q, hA.shape' q a hq', hq'⟩
  have notTemp : ∀ a (y : Site), y ∈ w.lent a → ∀ j, y.pos ≠ .temp s₀.topIdx j := fun a y hy j e => by
    obtain ⟨i, hi⟩ := h.bsites a y hy (by rw [e]; rfl)
    rw [e] at hi; cases hi
  have hshT : (repark w (σ l) v).shape (.temp s₀.topIdx G.temps.length) = some (σ l) := by
    rw [hshI, if_pos (by rw [htop₁])]
  refine ⟨FrameInvS.mk ?_ hS hS' (by rw [hnextI]; exact h.counter) h.srange
    (fun m y hy hf => h.bsites m y (by rw [hlentI] at hy; exact hy) hf)
    (fun m y hm hy hf => hposI _ (h.psites m y (hliveI m hm) (by rw [hlentI] at hy; exact hy) hf))
    (fun n hn => by rw [hnextC] at hn; rw [hrecI.1, hrecI.2, hrecC.1, hrecC.2]; exact h.heldAll n hn)
    (fun a c ha hc => h.orderAll a c (hnextC ▸ ha) (hnextC ▸ hc))
    (fun a c ha hc => h.monoAll a c (hnextC ▸ ha) (hnextC ▸ hc)), ?_, ?_⟩
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
        · rename_i e; exact absurd (e.trans (by rw [htop₁])) (notTemp a y hy _)
        · exact hrk a c y (hliveI a ha) hy (SState.takeLabel_shape_some hc)
      pfill := fun k hk y hy hyf => hA.pfill k hk y (by rw [hlentI] at hy; exact hy) hyf
      held := hS.held
      cells := by
        rw [eC]
        show ks.length ≤ ((((w'.takeLabel l).pushTemp fun _ => v).env.headD {}).binds.length)
        have htopT : (w'.takeLabel l).topIdx ≠ 0 := by rw [htop₁']; omega
        rw [pushTemp_modTop, modTop_headD _ _ htopT, headD_len_takeLabel]
        exact hA.cells
      uniq' := hS'.uniq
      rinv' := hri'
      noParam := fun p hp => by
        rw [eC]
        show Ochr.Meaning.FT _ (((w'.takeLabel l).pushTemp fun _ => v).valAt p)
        rcases SState.valAt_pushTemp (w'.takeLabel l) (fun _ => v) p with e | e <;> rw [e]
        · rcases SState.takeLabel_valAt w' l p with e' | e' <;> rw [e']
          · exact hA.noParam p hp
          · exact FT.const _ _
        · exact FT.const _ _
      order := fun a c ha hc => hA.order a c (hliveC a ha) (hliveC c hc)
      mono := fun a c ha hc => hA.mono a c (hliveC a ha) (hliveC c hc) }
  · intro k e; cases e
    exact ⟨fun _ => ⟨G.temps.length, hshT⟩, fun hd => absurd ((SState.live_iff _ _).2 ⟨_, (hS.acyc.2.2 _ _ hshT).1, hshT⟩) hd⟩
  · intro k e; cases e
    refine ⟨by rw [hnextC]; exact hltl, fun hd => absurd ?_ hd⟩
    have hshT' : (repark w' l v).shape (.temp (w'.takeLabel l).topIdx G'.temps.length) = some l := by
      rw [eC]; dsimp only; rw [if_pos rfl]
    exact (SState.live_iff _ _).2 ⟨_, (hS'.acyc.2.2 _ _ hshT').1, hshT'⟩


/-- **A move out of a place of the callee's frame** (the paper's (O4), (O2), (O5), (O8)): the content's access and
strict test on both sides or neither (`contentOf_corr`), `⊥` written in its place (`setContent_corr`), and at a root
holding a borrow the borrow moved on with the value (`repark_frameInvS`); goodness after from the strict fundamental
lemma's read (`Strict.readPlace_fund_all`). -/
theorem readMove_agree (hs₀ : FrameStart s₀ ks) {s s' : SState} (h : FrameInv K φ σ s₀ ks s s') (p : Place) :
    FrameAgreeI K φ σ s₀ ks (SM.guarded (ContentOk K φ p) (readPlace K φ p false) s)
      (SM.guarded (ContentOk K φ p) (readPlace K φ p false) s') := by
  have g1 : ∀ r t, SM.guarded (ContentOk K φ p) (readPlace K φ p false) s = some (r, t) → SGood K.dm K.Γ φ t :=
    fun r t ht => (Strict.readPlace_fund_all p false s t r h.good ht).2.2.2
  have g2 : ∀ r t, SM.guarded (ContentOk K φ p) (readPlace K φ p false) s' = some (r, t) → SGood K.dm K.Γ φ t :=
    fun r t ht => (Strict.readPlace_fund_all p false s' t r h.good' ht).2.2.2
  have ri : ∀ r t, SM.guarded (ContentOk K φ p) (readPlace K φ p false) s' = some (r, t) →
      SState.RInv (fun _ => False) t :=
    fun r t ht => (readPlace_rinv K φ (fun _ => False) (SM.guarded_some ht).2 h.acc.rinv').1
  obtain ⟨hc, hok⟩ := contentOf_corr φ hs₀ h.acc p
  unfold SM.guarded at g1 g2 ri ⊢
  by_cases hk : ContentOk K φ p s
  rotate_left
  · rw [if_neg hk, if_neg (fun h' => hk (hok.2 h'))]; trivial
  have hk' := hok.1 hk
  rw [if_pos hk] at g1 ⊢; rw [if_pos hk'] at g2 ri ⊢
  unfold readPlace at g1 g2 ri ⊢
  cases e1 : contentOf K φ p s with
  | none =>
    rw [e1] at hc
    cases e2 : contentOf K φ p s' with
    | none => trivial
    | some _ => rw [e2] at hc; exact hc.elim
  | some y =>
    rw [e1] at hc g1
    cases e2 : contentOf K φ p s' with
    | none => rw [e2] at hc; exact hc.elim
    | some y' =>
      rw [e2] at hc g2 ri
      obtain ⟨⟨v, T, pos, steps⟩, u⟩ := y
      obtain ⟨⟨v', T', pos', steps'⟩, u'⟩ := y'
      obtain ⟨rfl, hT, rfl, hpf, rfl, hacc⟩ := hc
      subst hT
      simp only [bind, Option.bind] at g1 g2 ri ⊢
      by_cases hw : v.whole
      rotate_left
      · simp only [hw, not_false_eq_true, if_true]; trivial
      by_cases hr : ReadGood K.dm.read T'.m v
      rotate_left
      · simp only [hw, hr, not_true_eq_false, not_false_eq_true, if_false, if_true]; trivial
      simp only [hw, hr, not_true_eq_false, if_false, Bool.false_eq_true] at g1 g2 ri ⊢
      obtain ⟨T₁, hres, hu, -, -⟩ := Strict.contentOf_view e1
      obtain ⟨T₁', hres', hu', -, -⟩ := Strict.contentOf_view e2
      have hgu : SGood K.dm K.Γ φ u := by
        rw [hu]; exact Strict.access_sgood h.good pos (dataHit steps) (Strict.contentOk_access hk hres)
      have hgu' : SGood K.dm K.Γ φ u' := by
        rw [hu']; exact Strict.access_sgood h.good' _ _ (Strict.contentOk_access hk' hres')
      have hU := h.of_ops hacc hgu hgu' (shrinks_contentOf e1) (shrinks_contentOf e2)
      have hsc := setContent_corr φ hacc hpf steps .moved
      cases e3 : setContent K φ pos steps .moved u with
      | none =>
        rw [e3] at hsc
        cases e4 : setContent K φ (upPos ks.length pos) steps .moved u' with
        | some _ => rw [e4] at hsc; exact hsc.elim
        | none => simp only [e3, e4]; trivial
      | some z =>
        rw [e3] at hsc
        cases e4 : setContent K φ (upPos ks.length pos) steps .moved u' with
        | none => rw [e4] at hsc; exact hsc.elim
        | some z' =>
          rw [e4] at hsc
          obtain ⟨⟨⟩, w⟩ := z
          obtain ⟨⟨⟩, w'⟩ := z'
          obtain ⟨-, hwA⟩ := hsc
          simp only [e3, e4] at g1 g2 ri ⊢
          have hW : FrameInvS K σ s₀ ks w w' := hU.toS.of_ops hwA (hU.good.struct.setContent e3)
            (hU.good'.struct.setContent e4) (shrinks_setContent e3) (shrinks_setContent e4)
          have hshW : ∀ q, w'.shape q = u'.shape q := fun q => by rw [setContent_eq K φ e4, SState.shape_setAt]
          have hshU := hU.acc.rel.topShape pos hpf
          by_cases hse : steps.isEmpty = true
          · simp only [hse, if_true] at g1 g2 ri ⊢
            rw [hshU] at g1 ⊢
            cases hq : u'.shape (upPos ks.length pos) with
            | none =>
              simp only [hq, Option.map_none] at g1 g2 ri ⊢
              exact ⟨rfl, rfl, hW.toInv (g1 _ _ rfl) (g2 _ _ rfl), ⟨fun _ e => (by cases e), fun _ e => (by cases e)⟩⟩
            | some l =>
              simp only [hq, Option.map_some] at g1 g2 ri ⊢
              have hg := g1 _ _ rfl
              have hg' := g2 _ _ rfl
              obtain ⟨hR, hres1, hdead1⟩ := repark_frameInvS hW hs₀ hpf (by rw [hshW]; exact hq) v hg.struct hg'.struct
                (ri _ _ rfl)
              exact ⟨rfl, rfl, hR.toInv hg hg', hres1, hdead1⟩
          · simp only [hse, Bool.false_eq_true, if_false] at g1 g2 ri ⊢
            exact ⟨rfl, rfl, hW.toInv (g1 _ _ rfl) (g2 _ _ rfl), ⟨fun _ e => (by cases e), fun _ e => (by cases e)⟩⟩


end

section
variable {K : RunCtx} {ρ : Assignment} {φ : Future} {σ : Nat → Nat} {s₀ : SState} {ks : List Nat}

/-- **The frame property's clause for a read** (`.place p`): by the place's declared reading (read off the callee's
frame, the same on both sides), a copy (`readCopy_agree`) or a move (`readMove_agree`). -/
theorem runFrameI_place (hs₀ : FrameStart s₀ ks) (p : Place) : TermFrame K ρ φ σ s₀ ks (.place p) := by
  intro tl hint s s' hI
  rw [runT]; dsimp only
  rw [scopeOf_corr hI.acc.rel]
  refine agreeI_erasedIf _ hI ?_
  cases K.D.copy (K.D.placeDecl (scopeOf s') p)
  · exact readMove_agree hs₀ hI p
  · exact readCopy_agree hs₀ hI p

end

end Ochr.Meaning.Steps.Form.FrameEnd
