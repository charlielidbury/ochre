import Ochr.Meaning.Steps.FrameMatch

/-!
# The call clause of the frame property: a call's fixes against the frame relation (lead34; docs/31 D220)

The paper's row "A call inside the body" (`18-principles`, `<sec-frame-proof>`; docs/31 D202): `callOf` takes the borrow
arguments' holders and makes every position read each consumed label as the callee's final content for it (`mapVals` with
a list of fixes, read off the future at the fresh label for a returned borrow). In place the consumed labels are the
images of the closure's, and the fixes act in the callee's frame alike and in the caller's frames exactly where the cells
are read (`FrameRel.lowerVal`): a consumed label is a parameter label, read through its cell, or the body's, which no
caller position reads (`FrameStart.reads`, `FrameInv.srange`). This file proves that heart, `frameRel_mapFix`.
-/

namespace Ochr.Meaning.Steps.Form.FrameEnd

open Ochr Ochr.Meaning

/-! ## Fixes through the renaming -/

/-- A list of fixes renamed: the in-place keys are the images of the closure's. -/
def renFix (σ : Nat → Nat) (F : List (Nat × Sem)) : List (Nat × Sem) := F.map fun lx => (σ lx.1, lx.2)

/-- **The renaming commutes with fixing a list of labels** (`renF_upd`, along the list). -/
theorem renF_updList {σ : Nat → Nat} (hinj : ∀ a b, σ a = σ b → a = b) :
    ∀ (F : List (Nat × Sem)) (ψ : Future), renF σ (ψ.updList (renFix σ F)) = (renF σ ψ).updList F
  | [], _ => rfl
  | (l, x) :: F, ψ => by
    simp only [renFix, List.map_cons, Future.updList]
    rw [← renF_upd hinj ψ l x]
    exact renF_updList hinj F (ψ.upd (σ l) x)

/-- `updList` off its keys is the identity. -/
theorem updList_off : ∀ (F : List (Nat × Sem)) (ψ : Future) (m : Nat), m ∉ F.map (·.1) → ψ.updList F m = ψ m
  | [], _, _, _ => rfl
  | (l, x) :: F, ψ, m, h => by
    simp only [List.map_cons, List.mem_cons, not_or] at h
    simp only [Future.updList]
    rw [updList_off F _ m h.2, Future.upd, if_neg h.1]

section
variable {σ : Nat → Nat} {s₀ : SState} {ks : List Nat} {s s' : SState}

/-- **`cellFuture` after the fixes** agrees, below the counter at the call, with `cellFuture` of the cells after the
closure's fixes: each cell `c` becomes `fun ψ' => c (ψ'.updList (F ψ'))`. Needs a cell for every parameter label, and
every fixed label a parameter's or one at or above the counter (`cellFuture_end`, along a list). -/
theorem cellFuture_fix (hinj : ∀ a b, σ a = σ b → a = b) (ks : List Nat) (cells : List SVal)
    (hlen : ks.length ≤ cells.length) (n : Nat) (F : Future → List (Nat × Sem))
    (hF : ∀ ψ l x, (l, x) ∈ F ψ → σ l ∈ ks ∨ n ≤ σ l) (ψ : Future) (m : Nat) (hm : m < n) :
    cellFuture σ ks cells (ψ.updList (renFix σ (F (renF σ ψ)))) m =
      cellFuture σ ks (cells.map fun c ψ' => c (ψ'.updList (F ψ'))) ψ m := by
  unfold cellFuture
  rw [renF_updList hinj, List.map_map]
  apply updList_at
  by_cases hk : m ∈ (renFix σ (F (renF σ ψ))).map (·.1)
  · left
    rw [zip_keys _ _ (by simpa using hlen)]
    simp only [renFix, List.map_map, List.mem_map, Function.comp] at hk
    obtain ⟨⟨l, x⟩, hlx, rfl⟩ := hk
    rcases hF _ l x hlx with h | h
    · exact h
    · simp only at hm h; omega
  · right; exact updList_off _ ψ m hk

end

/-! ## The fixes, as a rewrite of every value -/

/-- Every value read at the future fixed by `G` (a call's fixes, possibly read off the future). -/
def fixVals (G : Future → List (Nat × Sem)) : Pos → SVal → SVal := fun _ v ψ => v (ψ.updList (G ψ))

theorem valAt_fixVals (t : SState) (G : Future → List (Nat × Sem)) (q : Pos) (ψ : Future) :
    (t.mapVals (fixVals G)).valAt q ψ = t.valAt q (ψ.updList (G ψ)) := by
  by_cases hq : q ∈ t.positions
  · rw [SState.valAt_mapVals_of_mem _ _ _ hq]; rfl
  · rw [SState.valAt_mapVals_of_not_mem _ _ _ hq, SState.valAt_of_not_mem _ _ hq]

theorem cellsOf_fixVals (t : SState) (c : Nat) (G : Future → List (Nat × Sem)) :
    cellsOf c (t.mapVals (fixVals G)) = (cellsOf c t).map fun v ψ => v (ψ.updList (G ψ)) := by
  apply List.ext_getElem?
  intro i
  rw [List.getElem?_map, cellsOf_getElem?, cellsOf_getElem?]
  split
  · rw [SState.bindAt?_mapVals]
    cases t.bindAt? 0 i <;> rfl
  · rfl

theorem envSkel_mapVals (t : SState) (g : Pos → SVal → SVal) (f : Nat) :
    ((t.mapVals g).env[f]?).map (fun fr => (fr.binds.map fun b => (b.ty, b.decl), fr.temps.length)) =
      (t.env[f]?).map (fun fr => (fr.binds.map fun b => (b.ty, b.decl), fr.temps.length)) := by
  unfold SState.mapVals
  simp only [List.getElem?_map, List.getElem?_zipIdx]
  cases t.env[f]? with
  | none => rfl
  | some fr =>
    simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq, List.map_map, List.length_map, List.length_zipIdx,
      and_true]
    conv => rhs; rw [← List.zipIdx_map_fst 0 fr.binds, List.map_map]
    rfl

theorem getLast?_mapVals (t : SState) (g : Pos → SVal → SVal) {F : SFrame} (h : t.env.getLast? = some F) :
    (t.mapVals g).env.getLast? = some (mapFrame t.topIdx g F) := by
  rw [List.getLast?_eq_getElem?] at h ⊢
  simp only [SState.mapVals, List.length_map, List.length_zipIdx, List.getElem?_map, List.getElem?_zipIdx, h,
    Option.map_some, SState.topIdx, Nat.zero_add]
  rfl

section
variable {σ : Nat → Nat} {s₀ : SState} {ks : List Nat} {s s' : SState}

/-- **A call's fixes against the frame relation** (the heart of the paper's row "A call inside the body"; docs/31 D202):
the closure fixes, at every position, the labels `F ψ` gives (read off its own future), and in place their images
(`renFix`) at the renamed future. The top frames stay related (`renF_updList`); the caller's frames read the fixes exactly
where they read the cells (`cellFuture_fix`), because a fixed label is a parameter label or one the body made, which no
caller position reads (`FrameStart.reads`). Hypotheses: the relation, `FrameStart`, a cell per parameter label, and each
fixed label's image a parameter label or at or above the call's counter (`FrameInv.srange` gives it for any label). -/
theorem frameRel_mapFix (hr : FrameRel σ s₀ ks s s') (hs₀ : FrameStart s₀ ks)
    (hcells : ks.length ≤ (s'.env.headD {}).binds.length) (F : Future → List (Nat × Sem))
    (hF : ∀ ψ l x, (l, x) ∈ F ψ → σ l ∈ ks ∨ s₀.nextLoan ≤ σ l) :
    FrameRel σ s₀ ks (s.mapVals (fixVals fun ψ => renFix σ (F (renF σ ψ)))) (s'.mapVals (fixVals F)) := by
  obtain ⟨F₁, F₁', hF₁, hF₁', hlen, hb, htl, ht⟩ := hr.top
  have hclen : ks.length ≤ (cellsOf ks.length s').length := by
    simp only [cellsOf, List.length_take, List.length_map]; exact Nat.le_min.mpr ⟨Nat.le_refl _, hcells⟩
  refine
  { inj := hr.inj
    fresh := hr.fresh
    frames := by simp only [SState.mapVals, List.length_map, List.length_zipIdx]; exact hr.frames
    lowerSkel := fun f hf => by rw [envSkel_mapVals]; exact hr.lowerSkel f hf
    lowerVal := fun q hq ψ => by
      rw [valAt_fixVals, hr.lowerVal q hq, cellsOf_fixVals]
      exact hs₀.reads q hq _ _ fun m hm => cellFuture_fix hr.inj ks _ hclen s₀.nextLoan F hF ψ m hm
    lowerShape := hr.lowerShape
    top := ⟨_, _, getLast?_mapVals _ _ hF₁, getLast?_mapVals _ _ hF₁', by simp [mapFrame, hlen], ?_,
      by simp [mapFrame, htl], ?_⟩
    topShape := hr.topShape
    clShape := hr.clShape
    held := fun l hl => hr.held l (SState.live_mapVals.1 hl)
    lentTop := hr.lentTop
    lentImg := hr.lentImg
    lentCl := hr.lentCl
    lentCaller := hr.lentCaller
    topLabels := fun l hl => hr.topLabels l (SState.live_mapVals.1 hl) }
  · intro i b b' h1 h2
    rw [mapFrame_bind] at h1 h2
    cases e1 : F₁.binds[i]? with
    | none => rw [e1] at h1; cases h1
    | some b₀ =>
      cases e2 : F₁'.binds[i]? with
      | none => rw [e2] at h2; cases h2
      | some b₀' =>
        rw [e1] at h1; rw [e2] at h2
        simp only [Option.map_some, Option.some.injEq] at h1 h2
        subst h1 h2
        obtain ⟨hty, hdecl, hrec, hv⟩ := hb i b₀ b₀' e1 e2
        refine ⟨hty, hdecl, hrec, fun ψ => ?_⟩
        simp only [fixVals]
        rw [hv, renF_updList hr.inj]
  · intro j v h1
    rw [mapFrame_temp] at h1
    cases e1 : F₁.temps[j]? with
    | none => rw [e1] at h1; cases h1
    | some v₀ =>
      rw [e1] at h1
      simp only [Option.map_some, Option.some.injEq] at h1
      subst h1
      obtain ⟨v₀', e2, hv⟩ := ht j v₀ e1
      refine ⟨_, by rw [mapFrame_temp, e2]; rfl, fun ψ => ?_⟩
      simp only [fixVals]
      rw [hv, renF_updList hr.inj]


/-! ## A call's takes -/

theorem shapeAt_takeLabel {t : SState} (h : ShapeAt t) (l : Nat) : ShapeAt (t.takeLabel l) := fun p n hp => by
  cases e : t.holderOf l with
  | none => unfold SState.takeLabel at hp ⊢; rw [e] at hp ⊢; exact h p n hp
  | some r =>
    rw [takeLabel_eq e] at hp ⊢
    simp only [clearShape, SState.shape_setAt] at hp
    split at hp
    · cases hp
    · show p ∈ (t.setAt r fun _ => .moved).positions
      rw [SState.positions_setAt]; exact h p n hp

/-- **A borrow argument's take** (`takeLabel`) against the frame relation, live or not: a closure label not live has an
image held nowhere in place (not in the callee's frame, `topShape`; not in the caller's, `FrameInv.srange` with
`FrameStart.callerHeld`), so both takes do nothing. -/
theorem frameRel_takeLabel' (hr : FrameRel σ s₀ ks s s') (hs₀ : FrameStart s₀ ks) (hu : s.Uniq) (hsa : ShapeAt s)
    (hsa' : ShapeAt s') (l : Nat) (hl : σ l ∈ ks ∨ s₀.nextLoan ≤ σ l) :
    FrameRel σ s₀ ks (s.takeLabel (σ l)) (s'.takeLabel l) := by
  by_cases hlive : s'.Live l
  · exact frameRel_takeLabel hr hu hsa hsa' hlive
  · have hn' : s'.holderOf l = none := by
      cases e : s'.holderOf l with
      | none => rfl
      | some r => exact absurd (SState.live_iff s' l |>.2 ⟨r, (SState.holderOf_spec e).1, (SState.holderOf_spec e).2⟩) hlive
    have hn : s.holderOf (σ l) = none := by
      cases e : s.holderOf (σ l) with
      | none => rfl
      | some r =>
        exfalso
        obtain ⟨hrp, hrs⟩ := SState.holderOf_spec e
        have h1 := frameOf_lt_of_mem hrp
        rw [hr.frames.1] at h1
        have h2 : r.frameOf ≤ s₀.topIdx := by unfold SState.topIdx; omega
        rcases Nat.lt_or_eq_of_le h2 with h3 | h3
        · have h4 : s₀.shape r = some (σ l) := by rw [← hr.lowerShape r h3]; exact hrs
          obtain ⟨hk, hlt⟩ := hs₀.callerHeld r (σ l) h3 h4
          rcases hl with h | h
          · exact hk h
          · omega
        · have := hr.topShape r h3
          rw [hrs] at this
          cases e' : s'.shape (upPos ks.length r) with
          | none => rw [e'] at this; cases this
          | some l' =>
            rw [e'] at this
            have : l' = l := hr.inj _ _ (Option.some.inj this).symm
            subst this
            exact hlive ((SState.live_iff s' l').2 ⟨_, hsa' _ _ e', e'⟩)
    unfold SState.takeLabel; rw [hn, hn']; exact hr

/-- **The takes of a call's borrow arguments**, along a list of closure labels and their images. -/
theorem frameRel_takes (hs₀ : FrameStart s₀ ks) (hsr : ∀ l, σ l ∈ ks ∨ s₀.nextLoan ≤ σ l) :
    ∀ (L : List Nat) {s s' : SState}, FrameRel σ s₀ ks s s' → s.Uniq → ShapeAt s → ShapeAt s' →
      FrameRel σ s₀ ks ((L.map σ).foldl SState.takeLabel s) (L.foldl SState.takeLabel s')
  | [], _, _, hr, _, _, _ => hr
  | l :: L, s, s', hr, hu, hsa, hsa' => by
    simp only [List.map_cons, List.foldl_cons]
    exact frameRel_takes hs₀ hsr L (frameRel_takeLabel' hr hs₀ hu hsa hsa' l (hsr l)) (hu.takeLabel _)
      (shapeAt_takeLabel hsa _) (shapeAt_takeLabel hsa' _)

theorem headD_len_takeLabel (t : SState) (l : Nat) :
    ((t.takeLabel l).env.headD {}).binds.length = (t.env.headD {}).binds.length := by
  cases e : t.holderOf l with
  | none => unfold SState.takeLabel; rw [e]
  | some r =>
    rw [takeLabel_eq e]
    show ((t.setAt r fun _ => .moved).env.headD {}).binds.length = _
    cases r with
    | bind f i =>
      unfold SState.setAt
      cases h : t.env with
      | nil => simp [h]
      | cons fr rest => cases f <;> simp [h]
    | temp f i =>
      unfold SState.setAt
      cases h : t.env with
      | nil => simp [h]
      | cons fr rest => cases f <;> simp [h]

theorem headD_len_takes : ∀ (L : List Nat) (t : SState),
    ((L.foldl SState.takeLabel t).env.headD {}).binds.length = (t.env.headD {}).binds.length
  | [], _ => rfl
  | l :: L, t => by rw [List.foldl_cons, headD_len_takes L, headD_len_takeLabel]

/-- The fixes `callOfL` makes from the borrow arguments' labels and the finals, renamed: the in-place labels are the
images of the closure's. -/
theorem fixes_ren (refL : List (Option Nat)) (fs : List Sem) :
    ((refL.map (Option.map σ)).zip fs).filterMap (fun lf => lf.1.map (·, lf.2)) =
      renFix σ ((refL.zip fs).filterMap fun lf => lf.1.map (·, lf.2)) := by
  induction refL generalizing fs with
  | nil => simp [renFix]
  | cons l? refL ih =>
    cases fs with
    | nil => simp [renFix]
    | cons f fs =>
      cases l? with
      | none => simpa [renFix] using ih fs
      | some l => simpa [renFix] using ih fs

/-- **A call returning data, against the frame relation** (the paper's row "A call inside the body", D202): the borrow
arguments' holders taken (in place their images) and every position fixed at the finals. -/
theorem frameRel_callData (hr : FrameRel σ s₀ ks s s') (hs₀ : FrameStart s₀ ks) (hu : s.Uniq) (hsa : ShapeAt s)
    (hsa' : ShapeAt s') (hcells : ks.length ≤ (s'.env.headD {}).binds.length)
    (hsr : ∀ l, σ l ∈ ks ∨ s₀.nextLoan ≤ σ l) (refL : List (Option Nat)) (fs : List Sem) :
    FrameRel σ s₀ ks
      ((((refL.map (Option.map σ)).filterMap id).foldl SState.takeLabel s).mapVals fun _ v φ' =>
        v (φ'.updList (((refL.map (Option.map σ)).zip fs).filterMap fun lf => lf.1.map (·, lf.2))))
      (((refL.filterMap id).foldl SState.takeLabel s').mapVals fun _ v φ' =>
        v (φ'.updList ((refL.zip fs).filterMap fun lf => lf.1.map (·, lf.2)))) := by
  have hL : (refL.map (Option.map σ)).filterMap id = (refL.filterMap id).map σ := by
    induction refL with
    | nil => rfl
    | cons l? refL ih => cases l? <;> simp [ih]
  rw [hL, fixes_ren]
  have ht := frameRel_takes hs₀ hsr (refL.filterMap id) hr hu hsa hsa'
  have hc : ks.length ≤ ((((refL.filterMap id).foldl SState.takeLabel s').env.headD {}).binds.length) := by
    rw [headD_len_takes]; exact hcells
  exact frameRel_mapFix ht hs₀ hc (fun _ => (refL.zip fs).filterMap fun lf => lf.1.map (·, lf.2)) (fun _ l _ _ => hsr l)


/-- `callOfL`'s fixes for a returned borrow, as written (a `match` on the decoded final content of the fresh label `k`),
are `fixVals` of the fixes read off the future at `k`. -/
theorem fixVals_dec {X : Type _} (dec : Sem → Option X) (k : Nat) (A : X → List (Nat × Sem)) (B : List (Nat × Sem)) :
    (fun (_ : Pos) (v : SVal) (φ' : Future) => match dec (φ' k) with
      | some x => v (φ'.updList (A x))
      | none => v (φ'.updList B)) =
    fixVals (fun φ' => match dec (φ' k) with | some x => A x | none => B) := by
  funext p v φ'
  simp only [fixVals]
  cases dec (φ' k) <;> rfl

/-- **A call returning a borrow: its fixes against the frame relation** (`callOfL`'s ref case, after the takes and the
fresh label): every position reads the consumed labels at the backward function's components at the fresh label's final
content, decoded; in place at the image of the closure's fresh label, so the in-place fixes are the renamed closure's at
the renamed future (`frameRel_mapFix`). -/
theorem frameRel_callRefFix (hr : FrameRel σ s₀ ks s s') (hs₀ : FrameStart s₀ ks)
    (hcells : ks.length ≤ (s'.env.headD {}).binds.length) (hsr : ∀ l, σ l ∈ ks ∨ s₀.nextLoan ≤ σ l)
    {X : Type _} (dec : Sem → Option X) (k : Nat) (A : X → List (Nat × Sem)) (B : List (Nat × Sem)) :
    FrameRel σ s₀ ks
      (s.mapVals fun _ v φ' => match dec (φ' (σ k)) with
        | some x => v (φ'.updList (renFix σ (A x)))
        | none => v (φ'.updList (renFix σ B)))
      (s'.mapVals fun _ v φ' => match dec (φ' k) with
        | some x => v (φ'.updList (A x))
        | none => v (φ'.updList B)) := by
  rw [fixVals_dec, fixVals_dec]
  have e : (fun φ' : Future => match dec (φ' (σ k)) with | some x => renFix σ (A x) | none => renFix σ B) =
      fun ψ => renFix σ ((fun φ' : Future => match dec (φ' k) with | some x => A x | none => B) (renF σ ψ)) := by
    funext ψ; simp only [renF]; cases dec (ψ (σ k)) <;> rfl
  rw [e]
  exact frameRel_mapFix hr hs₀ hcells (fun φ' => match dec (φ' k) with | some x => A x | none => B)
    fun _ l _ _ => hsr l

end

end Ochr.Meaning.Steps.Form.FrameEnd
