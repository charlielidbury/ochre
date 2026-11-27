import Ochr.Meaning.Steps.FrameWhole

/-!
# The borrow clause of the frame property (lead35; docs/31 D223)

The paper's row "A borrow; an assignment through a borrow; field paths" of `<sec-frame-proof>`: [Access] for the content
((O4), (O2)), the fresh label ((O7)), the lender written ((O5)), the borrow parked ((O8)) and lent at the place, D112's
invalidation ((O9)), then the whole-state test below a root ((O6), `FrameWhole`).

Between the borrow and the whole-state test a state need not be good (a later dependent field of the lender), so the
internal relation is carried there without goodness (`FrameInvS`: `FrameInv` with `SGood`'s structural part in place of
`SGood`); the test, passed on both sides or neither, gives goodness back (`Strict.borrow_fund`).
-/

namespace Ochr.Meaning.Steps.Form.FrameEnd

open Ochr Ochr.Meaning Ochr.Meaning.Strict

/-- **The internal relation without goodness** (inside a clause, between a write below a root and the whole-state test):
`FrameInv` with `SGood`'s structural part (`SStruct`) on each side in place of `SGood`. -/
structure FrameInvS (K : RunCtx) (σ : Nat → Nat) (s₀ : SState) (ks : List Nat) (s s' : SState) : Prop where
  acc : AccInv K σ s₀ ks s s'
  struct : SStruct K.dm s
  struct' : SStruct K.dm s'
  counter : s₀.nextLoan ≤ s.nextLoan
  srange : ∀ l, σ l ∈ ks ∨ s₀.nextLoan ≤ σ l
  bsites : ∀ m (y : Site), y ∈ s.lent m → y.pos.frameOf = s₀.topIdx → ∃ i, y.pos = .bind s₀.topIdx i
  psites : ∀ m (y : Site), s.Live m → y ∈ s.lent m → y.pos.frameOf = s₀.topIdx → y.pos ∈ s.positions
  heldAll : ∀ l, l < s'.nextLoan → s.heldTy (σ l) = s'.heldTy l ∧ (σ l ∉ ks → s.heldMem (σ l) = s'.heldMem l)
  orderAll : ∀ l l', l < s'.nextLoan → l' < s'.nextLoan → σ l ∈ ks → σ l' ∉ ks → l < l'
  monoAll : ∀ l l', l < s'.nextLoan → l' < s'.nextLoan → σ l ∉ ks → σ l' ∉ ks → l < l' → σ l < σ l'

section
variable {K : RunCtx} {φ : Future} {σ : Nat → Nat} {s₀ : SState} {ks : List Nat}

theorem FrameInv.toS {s s' : SState} (h : FrameInv K φ σ s₀ ks s s') : FrameInvS K σ s₀ ks s s' :=
  ⟨h.acc, h.good.struct, h.good'.struct, h.counter, h.srange, h.bsites, h.psites, h.heldAll, h.orderAll, h.monoAll⟩

theorem FrameInvS.toInv {s s' : SState} (h : FrameInvS K σ s₀ ks s s') (hg : SGood K.dm K.Γ φ s)
    (hg' : SGood K.dm K.Γ φ s') : FrameInv K φ σ s₀ ks s s' :=
  ⟨h.acc, hg, hg', h.counter, h.srange, h.bsites, h.psites, h.heldAll, h.orderAll, h.monoAll⟩

/-- `FrameInv.of_ops` without goodness. -/
theorem FrameInvS.of_ops {s s' t t' : SState} (h : FrameInvS K σ s₀ ks s s') (hacc : AccInv K σ s₀ ks t t')
    (hS : SStruct K.dm t) (hS' : SStruct K.dm t') (hsh : Shrinks s t) (hsh' : Shrinks s' t') :
    FrameInvS K σ s₀ ks t t' :=
  { acc := hacc, struct := hS, struct' := hS', counter := hsh.next ▸ h.counter, srange := h.srange,
    bsites := BSites.shrinks (s₀ := s₀) h.bsites hsh,
    psites := fun m y hm hy hf => by
      obtain ⟨m', z, hm', hz, e⟩ := hsh.liveSites m y hm hy
      rw [hsh.positions, ← e]; exact h.psites m' z hm' hz (by rw [e]; exact hf),
    heldAll := fun l hl => by
      rw [hsh.records.1, hsh.records.2, hsh'.records.1, hsh'.records.2]; exact h.heldAll l (by rw [← hsh'.next]; exact hl)
    orderAll := fun l l' hl hl' => h.orderAll l l' (by rw [← hsh'.next]; exact hl) (by rw [← hsh'.next]; exact hl')
    monoAll := fun l l' hl hl' => h.monoAll l l' (by rw [← hsh'.next]; exact hl) (by rw [← hsh'.next]; exact hl') }

/-- D112's invalidation keeps the internal relation without goodness, and its strict test passes on both sides or
neither (`invalidate_corr`). -/
theorem FrameInvS.invalidate (φ : Future) (hs₀ : FrameStart s₀ ks) {s s' : SState} (h : FrameInvS K σ s₀ ks s s')
    (p : Place) :
    FrameInvS K σ s₀ ks (invalidate K φ p s) (invalidate K φ p s') ∧
      (InvalidateOk K φ p s ↔ InvalidateOk K φ p s') := by
  obtain ⟨hacc, hok⟩ := invalidate_corr φ hs₀ p h.acc
  exact ⟨h.of_ops hacc (h.struct.invalidate p) (h.struct'.invalidate p) (shrinks_invalidate K φ p s)
    (shrinks_invalidate K φ p s'), hok⟩

end

/-! ## The borrow's state -/

/-- The lender's new meaning: the fresh label's final content at the path. -/
noncomputable def lenderVal (K : RunCtx) (t : SState) (pos : Pos) (steps : List Step) : SVal := fun φ' =>
  (Sem.updAt K.dm K.Γ (t.freshLoan.2.tyAt pos) (fun _ => φ' t.nextLoan) steps (t.freshLoan.2.valAt pos φ')).getD .err

/-- `borrowPlace`'s state after the content's access `t`: the fresh label, the lender written, the borrow parked, lent at
the place, recorded. -/
noncomputable def borrowState (K : RunCtx) (t : SState) (pos : Pos) (steps : List Step) (v : Sem) (Tm : TyM) : SState :=
  ((((t.freshLoan.2.setAt pos (lenderVal K t pos steps)).pushTempShaped (fun _ => v) t.nextLoan).setLent t.nextLoan
    [⟨pos, steps, false⟩]).setHeldTy t.nextLoan Tm).setHeldMem t.nextLoan v

theorem borrowPlace_eq {K : RunCtx} {φ : Future} {p : Place} {s t : SState} {v : Sem} {T : TyS} {pos : Pos}
    {steps : List Step} (hc : contentOf K φ p s = some ((v, T, pos, steps), t)) (hw : v.whole) :
    borrowPlace K φ p s = some ((v, { T with label := some t.nextLoan }), borrowState K t pos steps v T.m) := by
  unfold borrowPlace
  simp only [Bind.bind, hc, Option.bind_some]
  rw [if_neg (fun hn => hn hw)]; rfl

theorem borrowPlace_none {K : RunCtx} {φ : Future} {p : Place} {s t : SState} {v : Sem} {T : TyS} {pos : Pos}
    {steps : List Step} (hc : contentOf K φ p s = some ((v, T, pos, steps), t)) (hw : ¬ v.whole) :
    borrowPlace K φ p s = none := by
  unfold borrowPlace
  simp only [Bind.bind, hc, Option.bind_some]
  rw [if_pos hw]

/-- `borrowState` is the park with no site, then lent at the place (what `accInv_setLent` adds). -/
theorem borrowState_park (K : RunCtx) (t : SState) (pos : Pos) (steps : List Step) (v : Sem) (Tm : TyM) :
    borrowState K t pos steps v Tm =
      (park (t.freshLoan.2.setAt pos (lenderVal K t pos steps)) (fun _ => v) t.nextLoan [] Tm v).setLent t.nextLoan
        ((park (t.freshLoan.2.setAt pos (lenderVal K t pos steps)) (fun _ => v) t.nextLoan [] Tm v).lent t.nextLoan ++
          [⟨pos, steps, false⟩]) := by
  unfold borrowState park
  generalize (t.freshLoan.2.setAt pos (lenderVal K t pos steps)).pushTempShaped (fun _ => v) t.nextLoan = P
  simp only [SState.setLent, SState.setHeldTy, SState.setHeldMem]
  congr 1
  funext n; split <;> simp_all

section
variable {K : RunCtx} {φ : Future} {σ : Nat → Nat} {s₀ : SState} {ks : List Nat} {t t' : SState}

/-- **The internal relation (without goodness) after a borrow** (the paper's (O7), (O5), (O8)): the fresh labels
correspond (`FrameRel.fresh`); the lender, a binding of the callee's frame, reads the fresh label at the path on both sides
(`frameRel_setAt`); the borrow is parked at a fresh temporary with no site (`frameRel_park`), then lent at the place
(`accInv_setLent`). Lending stays well founded: nothing is lent at a temporary of the callee's frame (`FrameInv.bsites`),
where the fresh label is held, and the fresh label is ranked below every other. The result's label is parked
(`ResAtTemp`). Both states' structural parts, and the closure's locality, are hypotheses (`borrowPlace_goodOn`,
`borrowPlace_rinv` give them). -/
theorem borrowState_frameInvS (h : FrameInv K φ σ s₀ ks t t') (hs₀ : FrameStart s₀ ks) {pos : Pos}
    (hpf : pos.frameOf = s₀.topIdx) (hpb : ∃ i, pos = .bind s₀.topIdx i) (hpos : pos ∈ t.positions)
    (steps : List Step) (v : Sem) (Tm : TyM)
    (hS : SStruct K.dm (borrowState K t pos steps v Tm))
    (hS' : SStruct K.dm (borrowState K t' (upPos ks.length pos) steps v Tm))
    (hri' : SState.RInv (fun _ => False) (borrowState K t' (upPos ks.length pos) steps v Tm)) :
    σ t'.nextLoan = t.nextLoan ∧
    FrameInvS K σ s₀ ks (borrowState K t pos steps v Tm) (borrowState K t' (upPos ks.length pos) steps v Tm) ∧
    ResAtTemp s₀ (borrowState K t pos steps v Tm) (some t.nextLoan) ∧
    ResDead (borrowState K t' (upPos ks.length pos) steps v Tm) (some t'.nextLoan) := by
  have hA := h.acc
  have hk : σ t'.nextLoan = t.nextLoan := by simpa using hA.rel.fresh 0
  have hkks : t.nextLoan ∉ ks := fun hm => by have := hs₀.ks_lt _ hm; have := h.counter; omega
  obtain ⟨-, hf⟩ := frameRel_freshLoan hA.rel
  have hsa1' : ShapeAt t'.freshLoan.2 := fun q l hq => hA.shape' q l hq
  have hv : ∀ ψ, lenderVal K t pos steps ψ = lenderVal K t' (upPos ks.length pos) steps (renF σ ψ) := by
    intro ψ; unfold lenderVal
    rw [updAt_T K.dm K.Γ _ steps (t.freshLoan.2.tyAt pos) (t'.freshLoan.2.tyAt (upPos ks.length pos))]
    have e1 : t.freshLoan.2.valAt pos ψ = t'.freshLoan.2.valAt (upPos ks.length pos) (renF σ ψ) := top_valAt hf pos hpf ψ
    have e2 : (renF σ ψ) t'.nextLoan = ψ t.nextLoan := by simp only [renF, hk]
    rw [e1, e2]
  have hset := frameRel_setAt hf hsa1' hpf hv
  rw [borrowState_park, borrowState_park] at *
  generalize ht2 : t.freshLoan.2.setAt pos (lenderVal K t pos steps) = t₂ at hset hS ⊢
  generalize ht2' : t'.freshLoan.2.setAt (upPos ks.length pos) (lenderVal K t' (upPos ks.length pos) steps) = t₂'
    at hset hS' hri' ⊢
  have hsh2 : ∀ q x, t₂.shape q = some x → t.shape q = some x := fun q x hq => by
    rw [← ht2, SState.shape_setAt] at hq; exact hq
  have hsh2' : ∀ q x, t₂'.shape q = some x → t'.shape q = some x := fun q x hq => by
    rw [← ht2', SState.shape_setAt] at hq; exact hq
  have hlent2 : t₂.lent = t.lent := by rw [← ht2, setAt_lent]; rfl
  have hlent2' : t₂'.lent = t'.lent := by rw [← ht2', setAt_lent]; rfl
  have hnext2 : t₂.nextLoan = t.nextLoan + 1 := by rw [← ht2, setAt_nextLoan]; rfl
  have hnext2' : t₂'.nextLoan = t'.nextLoan + 1 := by rw [← ht2', setAt_nextLoan]; rfl
  have hheld2 : t₂.heldTy = t.heldTy := by rw [← ht2, setAt_heldTy]; rfl
  have hheld2' : t₂'.heldTy = t'.heldTy := by rw [← ht2', setAt_heldTy]; rfl
  have hmem2 : t₂.heldMem = t.heldMem := by rw [← ht2, setAt_heldMem]; rfl
  have hmem2' : t₂'.heldMem = t'.heldMem := by rw [← ht2', setAt_heldMem]; rfl
  have hpos2 : t₂.positions = t.positions := by rw [← ht2, SState.positions_setAt]; rfl
  have hsa2' : ShapeAt t₂' := fun q l hq => by
    rw [← ht2', SState.positions_setAt]; rw [← ht2', SState.shape_setAt] at hq; exact hsa1' q l hq
  have hnot : ∀ q, t₂.shape q ≠ some t.nextLoan := fun q hq => by
    have := (h.good.acyc.2.2 q _ (hsh2 q _ hq)).2; omega
  have hnot' : ∀ q, t₂'.shape q ≠ some t'.nextLoan := fun q hq => by
    have := (h.good'.acyc.2.2 q _ (hsh2' q _ hq)).2; omega
  have hpark := frameRel_park hset hsa2' (v := fun _ => v) (v' := fun _ => v) (fun _ => rfl) (l := t'.nextLoan)
    (by rw [hk]; exact hnot) hnot' (xs := []) (fun _ h => by cases h) Tm v (h.srange _)
  rw [hk, List.map_nil] at hpark
  obtain ⟨i, rfl⟩ := hpb
  obtain ⟨F, F', hF, hF', -⟩ := top_rel hset
  have htop2 : t₂.topIdx = s₀.topIdx := topIdx_eq hset
  have htop2' : t₂'.topIdx = 1 := topIdx_cl hset
  have notTemp : ∀ a (y : Site), y ∈ t.lent a → ∀ j, y.pos ≠ .temp s₀.topIdx j := fun a y hy j e => by
    obtain ⟨i, hi⟩ := h.bsites a y hy (by rw [e]; rfl)
    rw [e] at hi; cases hi
  have liveS' : ∀ q a, t₂'.shape q = some a → t'.Live a := fun q a hq =>
    (SState.live_iff t' a).2 ⟨q, hA.shape' q a (hsh2' q a hq), hsh2' q a hq⟩
  have hP : AccInv K σ s₀ ks (park t₂ (fun _ => v) t.nextLoan [] Tm v) (park t₂' (fun _ => v) t'.nextLoan [] Tm v) :=
  { rel := hpark
    uniq := hS.uniq
    shape := fun q l hq => (hS.acyc.2.2 q l hq).1
    lend := by
      obtain ⟨rk, hrk⟩ := hA.lend
      refine ⟨rk, fun a b y ha hy hb => ?_⟩
      have hak : a ≠ t.nextLoan := by rintro rfl; rw [park_lent_self] at hy; cases hy
      rw [park_lent_ne _ _ _ _ hak, pushTempShaped_lent, hlent2] at hy
      rw [shape_park hF] at hb
      split at hb
      · rename_i e; exact absurd (e.trans (by rw [htop2])) (notTemp a y hy _)
      · rcases live_park_cases hF ha with e | ⟨q, hq⟩
        · exact absurd e hak
        · exact hrk a b y ((SState.live_iff t a).2 ⟨q, hA.shape q a (hsh2 q a hq), hsh2 q a hq⟩) hy (hsh2 _ _ hb)
    pfill := fun k0 hk0 y hy hyf => by
      have hne : k0 ≠ t.nextLoan := fun e => hkks (e ▸ hk0)
      rw [park_lent_ne _ _ _ _ hne, pushTempShaped_lent, hlent2] at hy
      exact hA.pfill k0 hk0 y hy hyf
    held := hS.held
    cells := by
      show ks.length ≤ ((t₂'.pushTempShaped (fun _ => v) t'.nextLoan).env.headD {}).binds.length
      rw [headD_len_pushTempShaped _ _ _ (by rw [htop2']; omega), ← ht2',
        show upPos ks.length (Pos.bind s₀.topIdx i) = .bind 1 i from rfl,
        setAt_bind_modTop _ (topIdx_cl hf).symm, modTop_headD _ _ (by rw [topIdx_cl hf]; omega)]
      exact hA.cells
    uniq' := hS'.uniq
    rinv' := hri'
    noParam := fun q hq => by
      show Ochr.Meaning.FT _ ((t₂'.pushTempShaped (fun _ => v) t'.nextLoan).valAt q)
      rw [SState.valAt_pushTempShaped]
      rcases SState.valAt_pushTemp t₂' (fun _ => v) q with e | e <;> rw [e]
      · rw [← ht2']
        rcases SState.valAt_setAt t'.freshLoan.2 (upPos ks.length (Pos.bind s₀.topIdx i))
          (lenderVal K t' (upPos ks.length (Pos.bind s₀.topIdx i)) steps) q with e' | e' <;> rw [e']
        · exact hA.noParam q hq
        · intro ψ ψ' e
          unfold lenderVal
          have e1 : t'.freshLoan.2.valAt (upPos ks.length (Pos.bind s₀.topIdx i)) ψ =
              t'.freshLoan.2.valAt (upPos ks.length (Pos.bind s₀.topIdx i)) ψ' :=
            hA.noParam (upPos ks.length (Pos.bind s₀.topIdx i)) (upPos_frameOf _ _) ψ ψ' e
          rw [e1, e t'.nextLoan (show σ t'.nextLoan ∉ ks by rw [hk]; exact hkks)]
      · exact FT.const _ _
    order := fun a b ha hb hak hbk => by
      rcases live_park_cases hF' ha with rfl | ⟨q, hq⟩
      · exact absurd hak (by rw [hk]; exact hkks)
      rcases live_park_cases hF' hb with rfl | ⟨q', hq'⟩
      · exact (h.good'.acyc.2.2 q a (hsh2' q a hq)).2
      · exact hA.order a b (liveS' q a hq) (liveS' q' b hq') hak hbk
    mono := fun a b ha hb hak hbk hab => by
      rcases live_park_cases hF' ha with rfl | ⟨q, hq⟩
      · rcases live_park_cases hF' hb with rfl | ⟨q', hq'⟩
        · omega
        · have := (h.good'.acyc.2.2 q' b (hsh2' q' b hq')).2; omega
      rcases live_park_cases hF' hb with rfl | ⟨q', hq'⟩
      · rw [hk]
        obtain ⟨p, -, hps⟩ := (SState.live_iff t _).1 (live_img hA.rel hA.shape (liveS' q a hq))
        exact (h.good.acyc.2.2 p _ hps).2
      · exact hA.mono a b (liveS' q a hq) (liveS' q' b hq') hak hbk hab }
  -- the fresh label lent at the place
  have hshP : ∀ (y : Site) a, y ∈ t.lent a → (park t₂ (fun _ => v) t.nextLoan [] Tm v).shape y.pos ≠
      some t.nextLoan := fun y a hy hs => by
    rw [shape_park hF] at hs
    split at hs
    · rename_i e; exact notTemp a y hy _ (e.trans (by rw [htop2]))
    · exact hnot _ hs
  have hnewS : (park t₂ (fun _ => v) t.nextLoan [] Tm v).shape (Pos.bind s₀.topIdx i) ≠ some t.nextLoan := by
    rw [shape_park hF, if_neg (by simp)]; exact hnot _
  have hSl := accInv_setLent hP t'.nextLoan [⟨Pos.bind s₀.topIdx i, steps, false⟩]
    [⟨upPos ks.length (Pos.bind s₀.topIdx i), steps, false⟩]
    (fun x hx => by
      simp only [List.mem_singleton, upSite]
      constructor
      · rintro rfl; rfl
      · intro e
        obtain ⟨xp, xπ, xf⟩ := x
        simp only [Site.mk.injEq] at e
        obtain ⟨e1, rfl, rfl⟩ := e
        rw [upPos_inj (by rw [hx]; rfl) e1])
    (fun x hx => by
      simp only [List.mem_singleton] at hx; subst hx
      exact .inl ⟨Pos.bind s₀.topIdx i, rfl, rfl⟩)
    (fun q hq hs => by
      obtain ⟨-, hlt⟩ := hs₀.callerHeld q _ hq hs; have := h.counter; rw [hk] at hlt; omega)
    (fun hm => absurd (hk ▸ hm) hkks)
    (fun _ a y _ hy hs => by
      rw [hk] at hs
      have hak : a ≠ t.nextLoan := by rintro rfl; rw [park_lent_self] at hy; cases hy
      rw [park_lent_ne _ _ _ _ hak, pushTempShaped_lent, hlent2] at hy
      exact hshP y a hy hs)
    (fun _ y hy hs => by
      simp only [List.mem_singleton] at hy; subst hy
      rw [hk] at hs; exact hnewS hs)
  rw [hk] at hSl
  refine ⟨hk, FrameInvS.mk hSl hS hS' ?_ h.srange ?_ ?_ ?_ ?_ ?_, ?_, ?_⟩
  · show s₀.nextLoan ≤ (t₂.pushTempShaped (fun _ => v) t.nextLoan).nextLoan
    rw [pushTempShaped_nextLoan, hnext2]; have := h.counter; omega
  · intro m y hy hf
    simp only [SState.setLent] at hy
    split at hy
    · rw [park_lent_self, List.nil_append, List.mem_singleton] at hy
      subst hy; exact ⟨i, rfl⟩
    · rename_i hne
      rw [park_lent_ne _ _ _ _ hne, pushTempShaped_lent, hlent2] at hy
      exact h.bsites m y hy hf
  · intro m y hm hy hf
    have hposP : ∀ q ∈ t.positions, q ∈ (park t₂ (fun _ => v) t.nextLoan [] Tm v).positions := fun q hq => by
      show q ∈ (t₂.pushTempShaped (fun _ => v) t.nextLoan).positions
      rw [SState.positions_pushTempShaped]; exact SState.mem_positions_pushTemp _ _ (by rw [hpos2]; exact hq)
    show y.pos ∈ (park t₂ (fun _ => v) t.nextLoan [] Tm v).positions
    simp only [SState.setLent] at hy
    split at hy
    · rw [park_lent_self, List.nil_append, List.mem_singleton] at hy
      subst hy; exact hposP _ hpos
    · rename_i hne
      rw [park_lent_ne _ _ _ _ hne, pushTempShaped_lent, hlent2] at hy
      have hm' : (park t₂ (fun _ => v) t.nextLoan [] Tm v).Live m := hm
      rcases live_park_cases hF hm' with e | ⟨q, hq⟩
      · exact absurd e hne
      · exact hposP _ (h.psites m y ((SState.live_iff t m).2 ⟨q, hA.shape q m (hsh2 q m hq), hsh2 q m hq⟩) hy hf)
  · intro l hl
    rw [SState.setLent_nextLoan, park_nextLoan, hnext2'] at hl
    rw [setLent_heldTy', setLent_heldTy', setLent_heldMem', setLent_heldMem', park_heldTy, park_heldTy, park_heldMem,
      park_heldMem, hheld2, hheld2', hmem2, hmem2']
    by_cases e : l = t'.nextLoan
    · subst e; simp [hk]
    · have e' : σ l ≠ t.nextLoan := fun h' => e (hA.rel.inj _ _ (h'.trans hk.symm))
      rw [if_neg e', if_neg e, if_neg e', if_neg e]
      exact h.heldAll l (by omega)
  · intro l l' hl hl' hlk hl'k
    rw [SState.setLent_nextLoan, park_nextLoan, hnext2'] at hl hl'
    by_cases e : l = t'.nextLoan
    · subst e; exact absurd (hk ▸ hlk) hkks
    by_cases e' : l' = t'.nextLoan
    · omega
    · exact h.orderAll l l' (by omega) (by omega) hlk hl'k
  · intro l l' hl hl' hlk hl'k hll
    rw [SState.setLent_nextLoan, park_nextLoan, hnext2'] at hl hl'
    by_cases e' : l' = t'.nextLoan
    · subst e'; rw [hk]; exact sigma_lt hA.rel (by omega)
    · exact h.monoAll l l' (by omega) (by omega) hlk hl'k hll
  · intro k0 e
    cases e
    have hsh : (park t₂ (fun _ => v) t.nextLoan [] Tm v).shape (.temp s₀.topIdx F.temps.length) = some t.nextLoan := by
      rw [shape_park hF, if_pos (by rw [htop2])]
    exact ⟨fun _ => ⟨F.temps.length, hsh⟩, fun hd => absurd ((SState.live_iff _ _).2 ⟨_, (hS.acyc.2.2 _ _ hsh).1, hsh⟩) hd⟩
  · intro k0 e
    cases e
    have hsh' : (park t₂' (fun _ => v) t'.nextLoan [] Tm v).shape (.temp t₂'.topIdx F'.temps.length) = some t'.nextLoan := by
      rw [shape_park hF', if_pos rfl]
    refine ⟨?_, fun hd => absurd ((SState.live_iff _ _).2 ⟨_, (hS'.acyc.2.2 _ _ hsh').1, hsh'⟩) hd⟩
    rw [SState.setLent_nextLoan, park_nextLoan, hnext2']; omega

end

/-! ## The clause -/

section
variable {K : RunCtx} {ρ : Assignment} {φ : Future} {σ : Nat → Nat} {s₀ : SState} {ks : List Nat}

theorem borrow_run_eq {p : Place} {s t : SState} {v : Sem} {T : TyS} {pos : Pos} {steps : List Step}
    (hk : ContentOk K φ p s) (e1 : contentOf K φ p s = some ((v, T, pos, steps), t)) (hw : v.whole)
    (hm : v ∈ₛ[K.dm.read] T.m) :
    SM.strictS K.dm.read (SM.guarded (ContentOk K φ p) (borrowPlace K φ p)) s =
      some ((v, { T with label := some t.nextLoan }), borrowState K t pos steps v T.m) := by
  unfold SM.strictS SM.guarded
  rw [if_pos hk, borrowPlace_eq e1 hw]
  dsimp only
  rw [if_pos hm]

theorem borrow_run_none {p : Place} {s t : SState} {v : Sem} {T : TyS} {pos : Pos} {steps : List Step}
    (hk : ContentOk K φ p s) (e1 : contentOf K φ p s = some ((v, T, pos, steps), t)) (hw : v.whole)
    (hm : ¬ v ∈ₛ[K.dm.read] T.m) :
    SM.strictS K.dm.read (SM.guarded (ContentOk K φ p) (borrowPlace K φ p)) s = none := by
  unfold SM.strictS SM.guarded
  rw [if_pos hk, borrowPlace_eq e1 hw]
  dsimp only
  rw [if_neg hm]

theorem borrow_run_none' {p : Place} {s : SState} (h : ContentOk K φ p s → borrowPlace K φ p s = none) :
    SM.strictS K.dm.read (SM.guarded (ContentOk K φ p) (borrowPlace K φ p)) s = none := by
  unfold SM.strictS SM.guarded
  by_cases hk : ContentOk K φ p s
  · rw [if_pos hk, h hk]
  · rw [if_neg hk]

theorem borrowPlace_of_none {p : Place} {s : SState} (e : contentOf K φ p s = none) : borrowPlace K φ p s = none := by
  unfold borrowPlace; simp only [Bind.bind, e]; rfl


/-- **The frame property's clause for a borrow** (the paper's row "A borrow; an assignment through a borrow; field paths":
(O4) and (O2) for the content, (O7), (O5), (O8) for the borrow, (O9) for D112's invalidation, (O6) for the whole-state
test): the content test and the strict test on both sides or neither, the internal relation without goodness after the
borrow (`borrowState_frameInvS`) and the invalidation, the whole-state test on both sides or neither (`lentOk_corr`, the
rest of each state good: `borrowPlace_goodOn`, `GoodOn.invalidate`), and goodness after from the strict fundamental
lemma's borrow clause (`Strict.borrow_fund`). -/
theorem runFrameI_borrow (hs₀ : FrameStart s₀ ks) (p : Place) : TermFrame K ρ φ σ s₀ ks (.borrow p) := by
  intro tl hint s s' hI
  rw [runT]; dsimp only
  rw [scopeOf_corr hI.acc.rel]
  refine agreeI_erasedIf _ hI ?_
  obtain ⟨hc, hok⟩ := contentOf_corr φ hs₀ hI.acc p
  by_cases hk : ContentOk K φ p s
  rotate_left
  · rw [borrow_run_none' (fun h => absurd h hk), borrow_run_none' (fun h' => absurd (hok.2 h') hk)]; trivial
  have hk' := hok.1 hk
  cases e1 : contentOf K φ p s with
  | none =>
    rw [e1] at hc
    cases e2 : contentOf K φ p s' with
    | some _ => rw [e2] at hc; exact hc.elim
    | none =>
      rw [borrow_run_none' (fun _ => borrowPlace_of_none e1), borrow_run_none' (fun _ => borrowPlace_of_none e2)]; trivial
  | some y =>
    rw [e1] at hc
    cases e2 : contentOf K φ p s' with
    | none => rw [e2] at hc; exact hc.elim
    | some y' =>
      rw [e2] at hc
      obtain ⟨⟨v, T, pos, steps⟩, t⟩ := y
      obtain ⟨⟨v', T', pos', steps'⟩, t'⟩ := y'
      obtain ⟨rfl, hT, rfl, hpf, rfl, hacc⟩ := hc
      subst hT
      by_cases hw : v.whole
      rotate_left
      · rw [borrow_run_none' (fun _ => borrowPlace_none e1 hw), borrow_run_none' (fun _ => borrowPlace_none e2 hw)]
        trivial
      by_cases hm : v ∈ₛ[K.dm.read] T'.m
      rotate_left
      · rw [borrow_run_none hk e1 hw hm, borrow_run_none hk' e2 hw hm]; trivial
      have hrun := borrow_run_eq hk e1 hw hm
      rw [hrun, borrow_run_eq hk' e2 hw hm]
      dsimp only
      obtain ⟨T₁, hres, ht, -, -⟩ := Strict.contentOf_view e1
      obtain ⟨T₁', hres', ht', -, -⟩ := Strict.contentOf_view e2
      have hgt : SGood K.dm K.Γ φ t := by
        rw [ht]; exact Strict.access_sgood hI.good pos (dataHit steps) (Strict.contentOk_access hk hres)
      have hgt' : SGood K.dm K.Γ φ t' := by
        rw [ht']; exact Strict.access_sgood hI.good' _ _ (Strict.contentOk_access hk' hres')
      have hft := hI.of_ops hacc hgt hgt' (shrinks_contentOf e1) (shrinks_contentOf e2)
      obtain ⟨hS, hR, hTs⟩ := borrowPlace_goodOn hI.good hk (borrowPlace_eq e1 hw) hm
      obtain ⟨hS', hR', hTs'⟩ := borrowPlace_goodOn hI.good' hk' (borrowPlace_eq e2 hw) hm
      have hri' := (borrowPlace_rinv K φ (fun _ => False) (borrowPlace_eq e2 hw) hI.acc.rinv').1
      have hpb : ∃ i, pos = .bind s₀.topIdx i := by
        have hpt := resolve_top hres
        cases pos with
        | bind f i => exact ⟨i, by simp only [Pos.frameOf] at hpf; rw [hpf]⟩
        | temp f j => exact absurd hpt.1 (by simp [IsTemp])
      have hpos : pos ∈ t.positions := by rw [ht, access_positions]; exact resolve_mem hres
      obtain ⟨hk1, hS1, hres1, hdead1⟩ := borrowState_frameInvS hft hs₀ hpf hpb hpos steps v T'.m hS hS' hri'
      obtain ⟨hS2, hiok⟩ := FrameInvS.invalidate φ hs₀ hS1 p
      have hT0 : s.topIdx = s₀.topIdx := topIdx_eq hI.acc.rel
      have hT0' : s'.topIdx = 1 := topIdx_cl hI.acc.rel
      by_cases hiv : InvalidateOk K φ p (borrowState K t pos steps v T'.m)
      rotate_left
      · rw [if_neg (fun h => hiv h.1), if_neg (fun h => hiv (hiok.2 h.1))]; trivial
      have hiv' := hiok.1 hiv
      have hR2 := GoodOn.invalidate (T := s₀.topIdx) p hS1.struct (by rw [hT0] at hR; exact hR)
        (by rw [← hT0]; exact hTs) hiv
      have hR2' := GoodOn.invalidate (T := 1) p hS1.struct' (by rw [hT0'] at hR'; exact hR')
        (by rw [← hT0']; exact hTs') hiv'
      have hl := lentOk_corr (φ := φ) hS2.acc.rel hS2.acc.shape hS2.acc.shape' hS2.acc.held hS2.acc.loc hR2 hR2' p
      by_cases hlo : lentOk K φ p (invalidate K φ p (borrowState K t pos steps v T'.m))
      rotate_left
      · rw [if_neg (fun h => hlo h.2), if_neg (fun h => hlo (hl.2 h.2))]; trivial
      rw [if_pos ⟨hiv, hlo⟩, if_pos ⟨hiv', hl.1 hlo⟩]
      have hg := (Strict.borrow_fund (K := K) (φ := φ) p s _ _ hI.good
        (by simp only [hrun]; rw [if_pos ⟨hiv, hlo⟩])).2.2.2
      have hg' := (Strict.borrow_fund (K := K) (φ := φ) p s' _ _ hI.good'
        (by simp only [borrow_run_eq hk' e2 hw hm]; rw [if_pos ⟨hiv', hl.1 hlo⟩])).2.2.2
      refine ⟨rfl, by simp [hk1], hS2.toInv hg hg', ?_, ?_⟩
      · exact hres1.shrinks hS1.struct.uniq (shrinks_invalidate K φ p _)
      · exact hdead1.shrinks (shrinks_invalidate K φ p _)

end

end Ochr.Meaning.Steps.Form.FrameEnd
