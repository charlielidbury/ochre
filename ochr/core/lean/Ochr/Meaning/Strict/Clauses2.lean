import Ochr.Meaning.Strict.Match

/-!
# The fundamental lemma's cases: sequences, `let`, matches, `J`, closures, reads in place

The drops after a sub-run (a `let`'s, a join's, the lending after a join) keep the sub-result's label
record (`heldTy`/`heldMem` are written only at fresh labels) and its liveness (`RunPresInd`'s
`letDrop_rinv`, `joinDrop_lou`, `lend_post`).
-/

namespace Ochr.Meaning.Strict
open Ochr.Meaning

section
variable {K : RunCtx} {ρ : Assignment} {φ : Future}

/-- Two states with the same label records. -/
def HeldSame (s s' : SState) : Prop := s'.heldTy = s.heldTy ∧ s'.heldMem = s.heldMem

theorem LabOk.of_held {s s' : SState} {r : Res} (h : LabOk K.dm s r) (he : HeldSame s s') : LabOk K.dm s' r := by
  intro l hl; rw [he.1, he.2]; exact h l hl

theorem heldSame_access (s : SState) (p : Pos) (hit : List Step → Bool) : HeldSame s (s.access p hit) :=
  ⟨heldTy_access s p hit, heldMem_access s p hit⟩

theorem heldSame_endLabel (s : SState) (l : Nat) : HeldSame s (s.endLabel l) :=
  ⟨heldTy_endLabel s l, heldMem_endLabel s l⟩

theorem heldSame_setAt (s : SState) (p : Pos) (g : SVal) : HeldSame s (s.setAt p g) :=
  ⟨heldTy_setAt s p g, heldMem_setAt s p g⟩

theorem HeldSame.trans {a b c : SState} (h₁ : HeldSame a b) (h₂ : HeldSame b c) : HeldSame a c :=
  ⟨h₂.1.trans h₁.1, h₂.2.trans h₁.2⟩

theorem heldSame_refl (s : SState) : HeldSame s s := ⟨rfl, rfl⟩

theorem heldSame_letDrop (s : SState) (held : Option Nat) :
    HeldSame s ((match held with | some l => s.endLabel l | none => letLenders s).dropLast) := by
  have h : HeldSame s (match held with | some l => s.endLabel l | none => letLenders s) := by
    cases held with
    | some l => exact heldSame_endLabel s l
    | none =>
      show HeldSame s (letLenders s)
      unfold letLenders
      split
      · exact heldSame_access _ _ _
      · exact heldSame_refl _
  exact ⟨h.1, h.2⟩

theorem heldSame_accessLentPrefix (pos : Pos) (steps : List Step) (s : SState) :
    HeldSame s (accessLentPrefix pos steps s) := by
  rcases accessLentPrefix_cases pos steps s with e | ⟨p', hit, e⟩
  · rw [e]; exact heldSame_refl _
  · rw [e]; exact heldSame_access _ _ _

theorem heldSame_dropAt (q : Place) (pos : Pos) (steps : List Step) (s : SState) :
    HeldSame s (dropAt K φ q pos steps s) := by
  unfold dropAt
  split
  · exact heldSame_endLabel _ _
  · dsimp only
    split
    · exact heldSame_refl _
    · split
      · exact (heldSame_access _ _ _).trans (heldSame_setAt _ _ _)
      · exact heldSame_refl _

theorem heldSame_joinDrop (entry : List Place) (t : Term) (s : SState) : HeldSame s (joinDrop K φ entry t s) := by
  unfold joinDrop
  generalize K.D.joinMoves (scopeOf s) entry t = qs
  induction qs generalizing s with
  | nil => exact heldSame_refl _
  | cons q qs ih =>
    rw [List.foldl_cons]
    refine HeldSame.trans ?_ (ih _)
    split
    · exact (heldSame_accessLentPrefix _ _ _).trans (heldSame_dropAt q _ _ _)
    · exact heldSame_refl _

end

end Ochr.Meaning.Strict

namespace Ochr.Meaning.Strict
open Ochr.Meaning

theorem pushBindShaped_nil (s : SState) (b : SBinding) (h : s.env = []) : pushBindShaped s b = s := by
  have hpos : s.positions = [] := by
    unfold SState.positions; simp [h, Std.Legacy.Range.forIn'_eq_forIn'_range', Std.Legacy.Range.size]
  have htake : ∀ l, s.takeLabel l = s := by
    intro l; unfold SState.takeLabel SState.holderOf; rw [hpos]; rfl
  have hpush : s.pushBind b = s := by
    unfold SState.pushBind; rw [h]; cases s; simp_all
  unfold pushBindShaped
  split
  · dsimp only
    rw [htake, hpush, h]
    rfl
  · exact hpush

end Ochr.Meaning.Strict

namespace Ochr.Meaning.Strict
open Ochr.Meaning

section
variable {K : RunCtx} {ρ : Assignment} {φ : Future}

/-- `u; w`: a borrow the discarded value holds ends. -/
theorem fund_seq {u w : Term} (hu : Fund K ρ φ u) (hw : Fund K ρ φ w) : Fund K ρ φ (.seq u w) := fun tl hint => by
  intro s s' r hs h
  rw [runT] at h
  refine fund_erasedS ?_ s s' r hs h
  intro s₀ s₃ r₀ hs₀ h₀
  obtain ⟨a, s₁, h1, h2⟩ := SM.bind_some h₀
  obtain ⟨⟨⟩, s₂, h3, h4⟩ := SM.bind_some h2
  obtain ⟨hdok, e⟩ := SM.guardMod_some h3
  subst e
  have hs₁ := (hu false _ _ _ _ hs₀ h1).2.2.2
  have hs₂ : SGood K.dm K.Γ φ (discardEnd a.2 s₁) := by
    unfold discardEnd; unfold DiscardOk at hdok; split
    · rename_i l hl; rw [hl] at hdok; exact endLabel_sgood hs₁ _ hdok
    · exact hs₁
  exact hw tl (tailHint tl hint) _ _ _ hs₂ h4

/-- `let x = u; w`: `u`'s result bound (`sgood_pushBindShaped`), `w` run, the binding dropped
(`sgood_letDrop`); the result's label record kept, its liveness by `RunPresInd.letDrop_rinv`. -/
theorem fund_letIn (_hc : FundCtx K) {x : Hint} {u w : Term} (hu : Fund K ρ φ u) (hw : Fund K ρ φ w) :
    Fund K ρ φ (.letIn x u w) := fun tl hint => by
  intro s s' r hs h
  rw [runT] at h
  refine fund_erasedS ?_ s s' r hs h
  intro s₀ s₄ r₀ hs₀ h₀
  simp only [Bind.bind, Option.bind_eq_some_iff] at h₀
  obtain ⟨⟨⟨v, T⟩, s₁⟩, h1, ⟨⟨r', R⟩, s₃⟩, h2, h3⟩ := h₀
  obtain ⟨hend, h3⟩ := open Classical in ite_none_some h3
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h3)
  obtain ⟨hv, hlab, hlou, hs₁⟩ := hu false _ _ _ _ hs₀ h1
  have hs₂ : SGood K.dm K.Γ φ (pushBindShaped s₁ { ty := T, val := fun _ => v, decl := K.D.declOf (scopeOf s₀) u }) := by
    by_cases hne : s₁.env = []
    · rw [pushBindShaped_nil _ _ hne]; exact hs₁
    · exact sgood_pushBindShaped hs₁ _ rfl hv hlab hlou hne
  obtain ⟨hg, hlab₃, hlou₃, hs₃⟩ := hw tl (tailHint tl hint) _ _ _ hs₂ h2
  refine ⟨hg, hlab₃.of_held (heldSame_letDrop _ _), ?_, sgood_letDrop hs₃ hend⟩
  exact (letDrop_rinv (fun _ => True) hs₃.acyc hlou₃ _ (by unfold SState.dropped; cases s₃.env.getLast? <;> rfl)).2.1

end

end Ochr.Meaning.Strict

namespace Ochr.Meaning.Strict
open Ochr.Meaning

section
variable {K : RunCtx} {ρ : Assignment} {φ : Future}

/-- After an arm: the drop at the join and the lending keep the invariant, the arm's result's label
record and liveness. -/
theorem fund_join (_hc : FundCtx K) {s₂ : SState} {r : Res} (lend : Option Nat → SState → SState)
    (hlend : ∀ lab s, lend lab s = s ∨ ∃ k xs, lend lab s = s.setLent k xs) (entry : List Place) (t : Term)
    (hg : GoodRes K.dm.read r) (hlab : LabOk K.dm s₂ r) (hlou : LoU s₂ r.2.label) (hs₂ : SGood K.dm K.Γ φ s₂)
    (hjok : JoinDropOk K φ entry t s₂) :
    GoodRes K.dm.read r ∧ LabOk K.dm (lend r.2.label (joinDrop K φ entry t s₂)) r ∧
      LoU (lend r.2.label (joinDrop K φ entry t s₂)) r.2.label ∧
      SGood K.dm K.Γ φ (lend r.2.label (joinDrop K φ entry t s₂)) := by
  have hj := sgood_joinDrop hs₂ entry t hjok
  have hjl : LoU (joinDrop K φ entry t s₂) r.2.label := fun y hy =>
    joinDrop_lou K φ (fun _ => True) entry t hs₂.acyc (hlou y hy)
  have hjh := hlab.of_held (heldSame_joinDrop (K := K) (φ := φ) entry t s₂)
  rcases hlend r.2.label (joinDrop K φ entry t s₂) with e | ⟨k, xs, e⟩
  · rw [e]; exact ⟨hg, hjh, hjl, hj⟩
  · rw [e]; exact ⟨hg, hjh, lou_setLent.mpr hjl, sgood_setLent hj k xs⟩

/-- A match on a number: the tag read (an access), the block entry (accesses), the arm, the join. -/
theorem fund_matchNat (hc : FundCtx K) {p : Place} {z u : Term} (hz : Fund K ρ φ z) (hu : Fund K ρ φ u) :
    Fund K ρ φ (.matchNat p z u) := fun tl hint => by
  intro s s' r hs h
  rw [runT] at h
  refine fund_erasedS ?_ s s' r hs h
  intro s₀ s₃ r₀ hs₀ h₀
  simp only [Bind.bind, Option.bind_eq_some_iff] at h₀
  obtain ⟨⟨tg, s₁⟩, h1, h₀⟩ := h₀
  obtain ⟨htok, h1⟩ := SM.guarded_some h1
  have hs₁ := sgood_tagOf hs₀ htok h1
  obtain ⟨_, hme, h₀⟩ := h₀
  have hs₁' := sgood_matchEntry (K := K) (φ := φ) hs₁ (!tl) (.matchNat p z u) (optCheck_some hme)
  have hlend := matchEntry_lend K φ (!tl) (.matchNat p z u) s₁
  generalize matchEntry K φ (!tl) (.matchNat p z u) s₁ = me at h₀ hs₁' hlend
  obtain ⟨s₂, lend⟩ := me
  dsimp only at h₀ hs₁' hlend
  split at h₀
  · cases h2 : runT K ρ φ tl (tailHint tl hint) z s₂ with
    | none => rw [h2] at h₀; cases h₀
    | some a =>
      rw [h2] at h₀
      obtain ⟨⟨r', R⟩, s₄⟩ := a
      simp only [Option.bind_some, Option.bind_eq_some_iff] at h₀
      obtain ⟨_, hjd, h₀⟩ := h₀
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h₀)
      obtain ⟨hg, hlab, hlou, hs₄⟩ := hz tl (tailHint tl hint) _ _ _ hs₁' h2
      exact fund_join hc lend hlend _ _ hg hlab hlou hs₄ (optCheck_some hjd)
  · cases h2 : runT K ρ φ tl (tailHint tl hint) u s₂ with
    | none => rw [h2] at h₀; cases h₀
    | some a =>
      rw [h2] at h₀
      obtain ⟨⟨r', R⟩, s₄⟩ := a
      simp only [Option.bind_some, Option.bind_eq_some_iff] at h₀
      obtain ⟨_, hjd, h₀⟩ := h₀
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h₀)
      obtain ⟨hg, hlab, hlou, hs₄⟩ := hu tl (tailHint tl hint) _ _ _ hs₁' h2
      exact fund_join hc lend hlend _ _ hg hlab hlou hs₄ (optCheck_some hjd)
  · cases h₀

end

end Ochr.Meaning.Strict

namespace Ochr.Meaning.Strict
open Ochr.Meaning

section
variable {K : RunCtx} {ρ : Assignment} {φ : Future}

theorem fund_runArmS : ∀ (arms : List (Hint × Term)), (∀ a ∈ arms, Fund K ρ φ a.2) →
    ∀ tl hint c, FundAt K.dm K.Γ φ (runArm K ρ φ tl hint c arms)
  | [], _, tl, hint, c => by intro s s' r hs h; simp [runArm, SM.fail] at h
  | (x, t) :: rest, ha, tl, hint, c => by
    intro s s' r hs h
    rw [runArm] at h
    split at h
    · exact ha (x, t) (List.mem_cons_self ..) tl hint s s' r hs h
    · exact fund_runArmS rest (fun a h' => ha a (List.mem_cons_of_mem _ h')) tl hint (c - 1) s s' r hs h

/-- A match on a constructor value: the tag read, the block entry, the arm, the join (none on a proof
or a one-constructor type). -/
theorem fund_matchInd (hc : FundCtx K) {p : Place} {n : String} {arms : List (Hint × Term)}
    (ha : ∀ a ∈ arms, Fund K ρ φ a.2) : Fund K ρ φ (.matchInd p n arms) := fun tl hint => by
  intro s s' r hs h
  rw [runT] at h
  refine fund_erasedS ?_ s s' r hs h
  intro s₀ s₃ r₀ hs₀ h₀
  simp only [Bind.bind, Option.bind_eq_some_iff] at h₀
  obtain ⟨⟨tg, s₁⟩, h1, h₀⟩ := h₀
  obtain ⟨htok, h1⟩ := SM.guarded_some h1
  have hs₁ := sgood_tagOf hs₀ htok h1
  obtain ⟨_, hme, h₀⟩ := h₀
  generalize hent : (!tl && !tg.isProof && !oneCtor K.Γ n) = ent at h₀ hme
  have hs₁' := sgood_matchEntry (K := K) (φ := φ) hs₁ ent (.matchInd p n arms) (optCheck_some hme)
  have hlend := matchEntry_lend K φ ent (.matchInd p n arms) s₁
  generalize matchEntry K φ ent (.matchInd p n arms) s₁ = me at h₀ hs₁' hlend
  obtain ⟨s₂, lend⟩ := me
  dsimp only at h₀ hs₁' hlend
  split at h₀
  · rename_i c _
    cases h2 : runArm K ρ φ tl (tailHint tl hint) c arms s₂ with
    | none => rw [h2] at h₀; cases h₀
    | some a =>
      rw [h2] at h₀
      obtain ⟨⟨r', R⟩, s₄⟩ := a
      simp only [Option.bind_some, Option.bind_eq_some_iff] at h₀
      obtain ⟨_, hjd, h₀⟩ := h₀
      have hjd := optCheck_some hjd
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h₀)
      obtain ⟨hg, hlab, hlou, hs₄⟩ := fund_runArmS arms ha tl (tailHint tl hint) c _ _ _ hs₁' h2
      split
      · exact ⟨hg, hlab, hlou, hs₄⟩
      · rename_i hnp
        split
        · exact ⟨hg, hlab, hlou, hs₄⟩
        · rename_i hone
          refine fund_join hc lend hlend _ _ hg hlab hlou hs₄ ?_
          rcases hjd with hp | ho | hj
          · exact absurd hp (by cases tg <;> simp_all [Sem.isProof])
          · exact absurd ho (by simpa using hone)
          · exact hj
  · -- an erased match on a proof with other than one arm: an arm ran, on a copy, to a proof at a
    -- type the lemma at the arm makes good; the state as it was, no label
    split at h₀
    · obtain ⟨c, R, s₄, -, h2, hr, hs'⟩ := SM.anyArm_some h₀
      subst hr hs'
      obtain ⟨hg, -, -, -⟩ := fund_runArmS arms ha tl (tailHint tl hint) c _ _ _ hs₁' h2
      refine ⟨hg, ?_, ?_, hs₁'⟩
      · intro l hl; simp at hl
      · intro l hl; simp at hl
    · cases h₀

end

end Ochr.Meaning.Strict

namespace Ochr.Meaning.Strict
open Ochr.Meaning

section
variable {K : RunCtx} {ρ : Assignment} {φ : Future}

/-- `J(A, a, b, P, h, t)`: the endpoints, motive and proof on copies, the block entry, the transported
term, the join. -/
theorem fund_J (hc : FundCtx K) {A a b P h t : Term} (ht : Fund K ρ φ t) :
    Fund K ρ φ (.prim "J" [A, a, b, P, h, t]) := fun tl hint => by
  intro s s' r hs hr
  rw [runT] at hr
  refine fund_erasedS ?_ s s' r hs hr
  intro s₀ s₃ r₀ hs₀ h₀
  obtain ⟨_, t₁, g₁, k₁⟩ := SM.bind_some h₀
  rw [SM.onCopy_state g₁] at k₁
  obtain ⟨_, t₂, g₂, k₂⟩ := SM.bind_some k₁
  rw [SM.onCopy_state g₂] at k₂
  obtain ⟨_, t₃, g₃, k₃⟩ := SM.bind_some k₂
  rw [SM.onCopy_state g₃] at k₃
  obtain ⟨_, t₄, g₄, k₄⟩ := SM.bind_some k₃
  rw [SM.onCopy_state g₄] at k₄
  obtain ⟨_, t₅, g₅, k₅⟩ := SM.bind_some k₄
  rw [SM.onCopy_state g₅] at k₅
  dsimp only at k₅
  obtain ⟨hme, k₅⟩ := open Classical in ite_none_some k₅
  have hs₁ := sgood_matchEntry (K := K) (φ := φ) hs₀ true t hme
  generalize (matchEntry K φ true t s₀).1 = s₂ at k₅ hs₁
  have h₀ := k₅
  split at h₀
  · rename_i r' R s₄ h2
    obtain ⟨hjd, h₀⟩ := open Classical in ite_none_some h₀
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h₀)
    obtain ⟨hg, hlab, hlou, hs₄⟩ := ht false (.plain TyM.err) _ _ _ hs₁ h2
    exact fund_join hc (fun _ s => s) (fun _ _ => .inl rfl) _ _ hg hlab hlou hs₄ hjd
  · cases h₀

/-- `clone`, `peek`, `inplace` of a term: a place read in place, or the term's run. -/
theorem fund_inPlace (_hc : FundCtx K) {u : Term} (hu : Fund K ρ φ u) {fl : Bool × Bool} (tl : Bool) (hint : TyS) :
    FundAt K.dm K.Γ φ (SM.erasedIf fl (SM.headOf u (fun p => SM.guarded (ContentOk K φ p) (readPlace K φ p true))
      (runT K ρ φ false hint u))) := by
  refine fund_erasedS ?_
  intro s s' r hs h
  rcases headOf_some' h with ⟨p, -, h⟩ | h
  · exact readPlace_fund_all p true s s' r hs h
  · exact hu false hint s s' r hs h

end

end Ochr.Meaning.Strict

namespace Ochr.Meaning.Strict
open Ochr.Meaning

section
variable {K : RunCtx} {ρ : Assignment} {φ : Future}

/-- One capture of a closure being formed: an access, then a move at the variable's root. -/
theorem sgood_capStep (_hc : FundCtx K) {s : SState} (hs : SGood K.dm K.Γ φ s) (i : Nat) (hok : CapOk K φ s i) :
    SGood K.dm K.Γ φ (capStep K s i) := by
  unfold capStep
  unfold CapOk at hok
  split
  · rename_i pos hv
    rw [hv] at hok
    have hs₁ := access_sgood hs pos (dataHit []) hok
    have hp₁ : pos ∈ (s.access pos (dataHit [])).positions := by rw [access_positions]; exact varPos_mem hv
    dsimp only
    split
    · exact hs₁
    · exact sgood_setAt_pmem hs₁ hp₁ (fun _ _ _ => .moved _) (fun _ _ => .moved _)
  · exact hs

theorem sgood_foldl_capStep (hc : FundCtx K) : ∀ (is : List Nat) {s : SState}, SGood K.dm K.Γ φ s →
    FoldOk (capStep K) (CapOk K φ) is s → SGood K.dm K.Γ φ (is.foldl (capStep K) s)
  | [], _, h, _ => h
  | i :: is, _, h, hok => sgood_foldl_capStep hc is (sgood_capStep hc h i hok.1) hok.2

/-- **A closure formed** (strict: a member of its function type; else `err` and the run fails): the
captures accessed and the non-copy ones moved. -/
theorem fund_fix (hc : FundCtx K) {self : Hint} {hs : List Hint} {ds : List Term} {c : Term} {dec : Option Nat}
    {body : Term} : Fund K ρ φ (.fix self hs ds c dec body) := fun tl hint => by
  intro s s' r hs' h
  rw [runT] at h
  refine fund_erasedS ?_ s s' r hs' h
  intro s₀ s₁ r₀ hs₀ h₀
  dsimp only at h₀
  obtain ⟨hcap, h₀⟩ := open Classical in ite_none_some h₀
  obtain ⟨h₀, hm⟩ := strictS_some h₀
  simp only [Option.some.injEq] at h₀
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj h₀
  exact ⟨.inl hm, (fun l h' => by cases h'), (fun l h' => by cases h'), sgood_foldl_capStep hc _ hs₀ hcap⟩

end

end Ochr.Meaning.Strict
