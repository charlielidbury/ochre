import Ochr.Meaning.Steps.FrameEndRel

/-!
# [Access] against the frame relation (lead33; docs/31 D214, D215)

The access ends, round by round, every live label lent at the accessed place; within a round in LABEL order. In place
and in the function's own frame the rounds end corresponding sets of labels (`reached_corr`), but the renaming does not
keep the order of two PARAMETER labels (docs/31 D211, `P3`; the paper's `P4`). Ruling R1 of the thirty-third brief: the
model follows the checker if that is routine; it is not taken (D214): a site-read order still needs a tie-break between
labels lent at the same path, which only label order gives, and the pop and an observation end parameter labels in
label order with no site to read, so the commutation of ends is owed whatever [Access] does. So the in-place round is
reordered into the closure's order by commuting ends, and the strict tests are carried across the orders.

Three layers. (1) Ends commute at the state level (`endLabel_comm_state`), from the semantic commutation
(`Mean.semEnd_comm`), the sites' (`relend_comm`), and an invariant of lending that no clause of `SGood` states:
`LendWF`, lending acyclic and every site at a holder under its `*` (the paper's (I4) says "lending is acyclic" and
never states it). (2) A permutation of labels whose holders read none of them gives the same state and the same strict
tests (`perm_fold`). (3) The frame relation: a round in place is the parameter labels it reaches, in some order, then the
others in the closure's order (`round_corr`), and the rounds iterate to the same fixpoint (`frameRel_access`).
-/

namespace Ochr.Meaning.Steps.Form.FrameEnd

open Ochr Ochr.Meaning

/-! ## Live labels are distinct -/

theorem framePos_nodup (f : Nat) (fr : SFrame) : (framePos f fr).Nodup := by
  unfold framePos
  rw [List.nodup_append]
  refine ⟨?_, ?_, ?_⟩
  · rw [List.nodup_iff_pairwise_ne, List.pairwise_map]
    exact (List.nodup_iff_pairwise_ne.mp List.nodup_range).imp fun h e => h (Pos.bind.inj e).2
  · rw [List.nodup_iff_pairwise_ne, List.pairwise_map]
    exact (List.nodup_iff_pairwise_ne.mp List.nodup_range).imp fun h e => h (Pos.temp.inj e).2
  · intro a ha b hb e
    obtain ⟨_, _, rfl⟩ := List.mem_map.mp ha
    obtain ⟨_, _, rfl⟩ := List.mem_map.mp hb
    cases e

theorem frameOf_framePos {f : Nat} {fr : SFrame} {p : Pos} (h : p ∈ framePos f fr) : p.frameOf = f := by
  unfold framePos at h
  rcases List.mem_append.mp h with h | h <;> obtain ⟨_, _, rfl⟩ := List.mem_map.mp h <;> rfl

theorem positions_nodup (s : SState) : s.positions.Nodup := by
  rw [SState.positions_eq, List.nodup_iff_pairwise_ne, List.pairwise_flatMap]
  refine ⟨fun f _ => ?_, ?_⟩
  · cases s.env[f]? with
    | none => exact List.Pairwise.nil
    | some fr => exact List.nodup_iff_pairwise_ne.mp (framePos_nodup f fr)
  · refine (List.nodup_iff_pairwise_ne.mp List.nodup_range).imp fun {f g} hfg x hx y hy e => hfg ?_
    subst e
    cases ef : s.env[f]? with
    | none => rw [ef] at hx; cases hx
    | some fr =>
      cases eg : s.env[g]? with
      | none => rw [eg] at hy; cases hy
      | some gr =>
        rw [ef] at hx; rw [eg] at hy
        exact (frameOf_framePos hx).symm.trans (frameOf_framePos hy)

/-- **With one holder per label, the live labels are distinct.** -/
theorem liveLabels_nodup {s : SState} (hu : s.Uniq) : s.liveLabels.Nodup := by
  unfold SState.liveLabels
  rw [(List.mergeSort_perm _ _).nodup_iff, List.nodup_iff_pairwise_ne, List.pairwise_filterMap]
  refine (List.nodup_iff_pairwise_ne.mp (positions_nodup s)).imp fun {p q} hpq b hb b' hb' e => hpq ?_
  subst e
  exact hu p q b hb hb'

/-- The live labels, in increasing order, strictly. -/
theorem liveLabels_lt {s : SState} (hu : s.Uniq) : s.liveLabels.Pairwise (· < ·) :=
  ((SState.liveLabels_sorted s).and (List.nodup_iff_pairwise_ne.mp (liveLabels_nodup hu))).imp
    fun ⟨h1, h2⟩ => Nat.lt_of_le_of_ne h1 h2

/-! ## Lending is well founded -/

/-- **Lending is acyclic, and every site at a holder lies under its `*`** (a run invariant no clause of `SGood` states;
the paper's (I4) assumes the first half as "lending is acyclic"). A live label `a` with a site at the holder of `b` (`a`
is lent inside `b`'s content) is ranked below `b`; at the checker's states it is (WF3) on loans, and every site at a borrow
holder is under its `*` (docs/31 D67). Ending a label contracts it: an edge through it becomes an edge past it. -/
def LendWF (s : SState) : Prop :=
  ∃ rk : Nat → Nat, ∀ a b (y : Site), s.Live a → y ∈ s.lent a → s.shape y.pos = some b →
    rk a < rk b ∧ ∃ π, y.path = .deref :: π

theorem live_of_endAt {s : SState} {l a : Nat} {r : Pos} (h : (s.endAt l r).Live a) : s.Live a ∧ ∀ p, p ∈ s.positions →
    (s.endAt l r).shape p = some a → p ≠ r := by
  rw [SState.live_iff, SState.endAt_positions, SState.endAt_shape] at h
  obtain ⟨p, hp, hs⟩ := h
  refine ⟨(SState.live_iff s a).2 ⟨p, hp, ?_⟩, fun q _ hq e => ?_⟩
  · dsimp only at hs; split at hs
    · cases hs
    · exact hs
  · rw [SState.endAt_shape] at hq; dsimp only at hq; rw [if_pos e] at hq; cases hq

theorem LendWF.endLabel {s : SState} (h : LendWF s) (l : Nat) : LendWF (s.endLabel l) := by
  cases hh : s.holderOf l with
  | none => rw [SState.endLabel_of_none hh]; exact h
  | some r =>
    rw [SState.endLabel_eq hh]
    obtain ⟨rk, hrk⟩ := h
    obtain ⟨hrpos, hrl⟩ := SState.holderOf_spec hh
    refine ⟨rk, fun a b y ha hy hb => ?_⟩
    have ha' := (live_of_endAt ha).1
    rw [SState.endAt_shape] at hb; dsimp only at hb
    split at hb
    · cases hb
    rename_i hyr
    by_cases hal : a = l
    · subst hal; rw [endAt_lent, relend_eq, if_pos rfl] at hy; cases hy
    rw [endAt_lent, mem_relend hal] at hy
    rcases hy with ⟨hy, -⟩ | ⟨x₀, hx₀, hx₀r, z, hz, rfl⟩
    · exact hrk a b y ha' hy hb
    · have hlive : s.Live l := (SState.live_iff s l).2 ⟨r, hrpos, hrl⟩
      have h1 := (hrk a l x₀ ha' hx₀ (by rw [hx₀r]; exact hrl)).1
      rw [relendSite_pos] at hb
      obtain ⟨h2, π, hπ⟩ := hrk l b z hlive hz hb
      refine ⟨Nat.lt_trans h1 h2, ?_⟩
      unfold relendSite; split
      · exact ⟨π, hπ⟩
      · exact ⟨π ++ inContent x₀.path, by simp [hπ]⟩

/-! ## Ends commute, as states -/

theorem holderOf_endLabel_ne (s : SState) {l l' : Nat} (hl : l ≠ l') : (s.endLabel l).holderOf l' = s.holderOf l' :=
  SState.find_endLabel s hl

/-- **Two ends commute, as states** (the paper's (I4), at the state level): the meanings by `Mean.semEnd_comm` (one
holder does not read the other's label), the sites by `relend_comm` (lending acyclic, sites at holders under `*`:
`LendWF`); stored types, readings, records and the counter are untouched by either end. -/
theorem endLabel_comm_state {s : SState} (hw : LendWF s) {a b : Nat}
    (hind : ∀ ra rb, s.holderOf a = some ra → s.holderOf b = some rb → ¬ s.dependsOn ra b ∨ ¬ s.dependsOn rb a) :
    (s.endLabel a).endLabel b = (s.endLabel b).endLabel a := by
  by_cases hab : a = b
  · subst hab; rfl
  cases ha : s.holderOf a with
  | none =>
    have : (s.endLabel b).holderOf a = none := by rw [holderOf_endLabel_ne s (Ne.symm hab)]; exact ha
    rw [SState.endLabel_of_none ha, SState.endLabel_of_none this]
  | some ra =>
  cases hb : s.holderOf b with
  | none =>
    have : (s.endLabel a).holderOf b = none := by rw [holderOf_endLabel_ne s hab]; exact hb
    rw [SState.endLabel_of_none hb, SState.endLabel_of_none this]
  | some rb =>
    obtain ⟨hra, hsa⟩ := SState.holderOf_spec ha
    obtain ⟨hrb, hsb⟩ := SState.holderOf_spec hb
    have hr : ra ≠ rb := fun e => hab (Option.some.inj (hsa.symm.trans (e ▸ hsb)))
    obtain ⟨rk, hrk⟩ := hw
    have hla : s.Live a := (SState.live_iff s a).2 ⟨ra, hra, hsa⟩
    have hlb : s.Live b := (SState.live_iff s b).2 ⟨rb, hrb, hsb⟩
    have hlent : ({ s with lent := s.relend a ra } : SState).relend b rb =
        ({ s with lent := s.relend b rb } : SState).relend a ra := by
      refine relend_comm s a b ra rb hab hr (fun y hy hyp => (hrk a b y hla hy (by rw [hyp]; exact hsb)).2)
        (fun y hy hyp => (hrk b a y hlb hy (by rw [hyp]; exact hsa)).2) ?_
      refine Classical.byContradiction fun hc => ?_
      rw [not_or] at hc
      obtain ⟨h1, h2⟩ := hc
      simp only [Classical.not_forall, Classical.not_not] at h1 h2
      obtain ⟨y, hy, hyp⟩ := h1
      obtain ⟨y', hy', hyp'⟩ := h2
      have e1 := (hrk b a y hlb hy (by rw [hyp]; exact hsa)).1
      have e2 := (hrk a b y' hla hy' (by rw [hyp']; exact hsb)).1
      omega
    have h1 : s.positions.find? (fun p => decide (s.shape p = some a)) = some ra := ha
    have h2 : s.positions.find? (fun p => decide (s.shape p = some b)) = some rb := hb
    rw [SState.endLabel_endLabel s h1 (by rw [SState.find_endLabel s hab]; exact h2) hr.symm,
      SState.endLabel_endLabel s h2 (by rw [SState.find_endLabel s (Ne.symm hab)]; exact h1) hr,
      Mean.semEnd_comm _ hr hab (hind ra rb ha hb)]
    rw [SState.endLabel_of_find s a ra h1, SState.endLabel_of_find s b rb h2]
    exact congrArg (fun L => ({ s with shape := ((s.toMean.semEnd rb b).semEnd ra a).shape, lent := L } : SState).mapVals
      fun p _ => (((s.toMean.semEnd rb b).semEnd ra a).val · p)) hlent

/-! ## The strict tests of two ends, in either order -/

section
variable (K : RunCtx) (φ : Future)

/-- Every live label's record is a member of its content type (`Strict.SGood.held`). -/
def HeldOk (t : SState) : Prop := ∀ l ∈ t.liveLabels, t.heldMem l ∈ₛ[K.dm.read] t.heldTy l

theorem heldTy_endLabel (t : SState) (l : Nat) : (t.endLabel l).heldTy = t.heldTy := by
  unfold SState.endLabel; split <;> rfl

theorem heldMem_endLabel (t : SState) (l : Nat) : (t.endLabel l).heldMem = t.heldMem := by
  unfold SState.endLabel; split <;> rfl

theorem live_of_endLabel {t : SState} {l m : Nat} (h : (t.endLabel l).Live m) : t.Live m := by
  cases hh : t.holderOf l with
  | none => rw [SState.endLabel_of_none hh] at h; exact h
  | some r => rw [SState.endLabel_eq hh] at h; exact (live_of_endAt h).1

theorem HeldOk.endLabel {t : SState} (h : HeldOk K t) (l : Nat) : HeldOk K (t.endLabel l) := fun m hm => by
  rw [heldTy_endLabel, heldMem_endLabel]; exact h m (live_of_endLabel hm)

/-- With one holder, the ended label is no longer live. -/
theorem not_live_endLabel {t : SState} (hu : t.Uniq) (l : Nat) : ¬ (t.endLabel l).Live l := by
  intro h
  cases hh : t.holderOf l with
  | none => rw [SState.endLabel_of_none hh] at h; obtain ⟨r, hr⟩ := SState.holderOf_of_live h; rw [hh] at hr; cases hr
  | some r =>
    rw [SState.endLabel_eq hh] at h
    obtain ⟨p, hp, hs⟩ := (SState.live_iff _ l).1 h
    rw [SState.endAt_positions] at hp
    rw [SState.endAt_shape] at hs; dsimp only at hs
    split at hs
    · cases hs
    · rename_i hpr; exact hpr (hu p r l hs (SState.holderOf_spec hh).2)

theorem live_endLabel_iff {t : SState} (hu : t.Uniq) {l m : Nat} : (t.endLabel l).Live m ↔ t.Live m ∧ m ≠ l :=
  ⟨fun h => ⟨live_of_endLabel h, fun e => not_live_endLabel hu l (e ▸ h)⟩, fun ⟨h, e⟩ => SState.live_endLabel h e⟩

/-- **A strict end does not see an end its holder does not read.** -/
theorem endOk_endLabel_indep {t : SState} (hu : t.Uniq) (hh : HeldOk K t) {a b : Nat} (hab : a ≠ b)
    (hind : ∀ rb, t.holderOf b = some rb → Indep a (t.valAt rb)) :
    EndOk K φ (t.endLabel a) b ↔ EndOk K φ t b := by
  unfold EndOk
  rw [holderOf_endLabel_ne t hab, heldTy_endLabel]
  refine forall_congr' fun rb => forall_congr' fun hrb => ?_
  have hi := hind rb hrb
  have hval : ∀ ψ, (t.endLabel a).valAt rb ψ = t.valAt rb ψ := fun ψ => by
    cases ha : t.holderOf a with
    | none => rw [SState.endLabel_of_none ha]
    | some ra =>
      rw [SState.endLabel_eq ha]
      have hne : rb ≠ ra := fun e =>
        hab (Option.some.inj ((SState.holderOf_spec ha).2.symm.trans (e ▸ (SState.holderOf_spec hrb).2)))
      rw [SState.endAt_valAt _ _ _ _ (SState.holderOf_spec hrb).1]
      simp only [if_neg hne]
      exact hi ψ _
  simp only [hval]
  have hlive : ∀ m, (t.endLabel a).Live m ↔ t.Live m ∧ m ≠ a := fun m => live_endLabel_iff hu
  constructor
  · intro h ψ hψ
    have := h (ψ.upd a (φ a)) ⟨fun m hm => ?_, fun m hm => ?_⟩
    · rwa [hi ψ (φ a)] at this
    · by_cases e : m = a
      · subst e; exact Future.upd_same _ _ _
      · rw [Future.upd_other _ _ e]; exact hψ.1 m fun hm' => hm ((hlive m).2 ⟨hm', e⟩)
    · have ⟨hm', e⟩ := (hlive m).1 hm
      rw [Future.upd_other _ _ e, heldTy_endLabel]; exact hψ.2 m hm'
  · intro h ψ hψ
    by_cases hla : t.Live a
    · have := h (ψ.upd a (t.heldMem a)) ⟨fun m hm => ?_, fun m hm => ?_⟩
      · rwa [hi ψ (t.heldMem a)] at this
      · have e : m ≠ a := fun e => hm (e ▸ hla)
        rw [Future.upd_other _ _ e]; exact hψ.1 m fun hm' => hm (((hlive m).1 hm').1)
      · by_cases e : m = a
        · subst e; rw [Future.upd_same]; exact hh m hm
        · rw [Future.upd_other _ _ e]; rw [← heldTy_endLabel t a]; exact hψ.2 m ((hlive m).2 ⟨hm, e⟩)
    · refine h ψ ⟨fun m hm => hψ.1 m fun hm' => hm ((hlive m).1 hm').1, fun m hm => ?_⟩
      have e : m ≠ a := fun e => hla (e ▸ hm)
      have := hψ.2 m ((hlive m).2 ⟨hm, e⟩)
      rwa [heldTy_endLabel] at this
end

/-! ## A permutation of labels whose holders read none of them -/

section
variable (K : RunCtx) (φ : Future)

/-- **What lets the labels of `P` be ended in any order**: one holder per label, lending well founded, every live
record a member, and no holder of a `P` label reading a `P` label. In the frame relation `P` is the parameter labels:
the callee's frame reads none of them (the paper's (I1)). -/
structure PInv (P : Nat → Prop) (t : SState) : Prop where
  uniq : t.Uniq
  lend : LendWF t
  held : HeldOk K t
  reads : ∀ r l, t.shape r = some l → P l → Ochr.Meaning.FT (fun y => ¬ P y) (t.valAt r)

theorem PInv.endLabel {P : Nat → Prop} {t : SState} (h : PInv K P t) {c : Nat} (hc : P c) : PInv K P (t.endLabel c) where
  uniq := h.uniq.endLabel c
  lend := h.lend.endLabel c
  held := h.held.endLabel K c
  reads := fun r l hr hl => by
    cases hh : t.holderOf c with
    | none => rw [SState.endLabel_of_none hh] at hr ⊢; exact h.reads r l hr hl
    | some rc =>
      rw [SState.endLabel_eq hh] at hr ⊢
      rw [SState.endAt_shape] at hr; dsimp only at hr
      split at hr
      · cases hr
      rename_i hrc
      have hf := h.reads r l hr hl
      by_cases hp : r ∈ t.positions
      · rw [SState.endAt_valAt _ _ _ _ hp]
        intro ψ ψ' e
        simp only [if_neg hrc]
        rw [Ochr.Meaning.FT.indep hf (fun h => h hc) ψ _, Ochr.Meaning.FT.indep hf (fun h => h hc) ψ' _]
        exact hf ψ ψ' e
      · rw [SState.endAt_valAt_not_mem _ _ _ _ hp]; exact hf

theorem PInv.comm {P : Nat → Prop} {t : SState} (h : PInv K P t) {a b : Nat} (ha : P a) (hb : P b) :
    (t.endLabel a).endLabel b = (t.endLabel b).endLabel a :=
  endLabel_comm_state h.lend fun ra _ hra _ => .inl fun hd =>
    (SState.dependsOn_iff t ra b).1 hd (Ochr.Meaning.FT.indep (h.reads ra a (SState.holderOf_spec hra).2 ha) (fun h => h hb))

theorem PInv.indep {P : Nat → Prop} {t : SState} (h : PInv K P t) {a b : Nat} (ha : P a) (hb : P b) :
    ∀ rb, t.holderOf b = some rb → Indep a (t.valAt rb) :=
  fun rb hrb => Ochr.Meaning.FT.indep (h.reads rb b (SState.holderOf_spec hrb).2 hb) (fun h => h ha)

theorem endsOk_cons (l : Nat) (L : List Nat) (t : SState) :
    EndsOk K φ (l :: L) t ↔ EndOk K φ t l ∧ EndsOk K φ L (t.endLabel l) := Iff.rfl

theorem endsOk_append : ∀ (L M : List Nat) (t : SState),
    EndsOk K φ (L ++ M) t ↔ EndsOk K φ L t ∧ EndsOk K φ M (L.foldl SState.endLabel t)
  | [], M, t => by simp [EndsOk, FoldOk]
  | l :: L, M, t => by
    rw [List.cons_append, endsOk_cons, endsOk_append L M, endsOk_cons, List.foldl_cons, and_assoc]

/-- **Ending the labels of `P` in two orders**: the same state and the same strict tests. -/
theorem perm_fold {P : Nat → Prop} {L₁ L₂ : List Nat} (hp : L₁.Perm L₂) :
    (∀ x ∈ L₁, P x) → ∀ t, PInv K P t →
      L₁.foldl SState.endLabel t = L₂.foldl SState.endLabel t ∧ (EndsOk K φ L₁ t ↔ EndsOk K φ L₂ t) := by
  induction hp with
  | nil => intro _ t _; exact ⟨rfl, Iff.rfl⟩
  | cons x _ ih =>
    intro hP t ht
    have hx := hP x (by simp)
    obtain ⟨e, i⟩ := ih (fun y hy => hP y (by simp [hy])) _ (ht.endLabel K hx)
    exact ⟨by simp only [List.foldl_cons]; exact e, by rw [endsOk_cons, endsOk_cons, i]⟩
  | swap x y l =>
    intro hP t ht
    have hx := hP x (by simp)
    have hy := hP y (by simp)
    have hc := ht.comm K hy hx
    refine ⟨by simp only [List.foldl_cons]; rw [hc], ?_⟩
    rw [endsOk_cons, endsOk_cons, endsOk_cons, endsOk_cons, hc]
    by_cases hxy : x = y
    · subst hxy; exact Iff.rfl
    rw [endOk_endLabel_indep K φ ht.uniq ht.held (Ne.symm hxy) (ht.indep K hy hx),
      endOk_endLabel_indep K φ ht.uniq ht.held hxy (ht.indep K hx hy)]
    constructor
    · rintro ⟨a, b, c⟩; exact ⟨b, a, c⟩
    · rintro ⟨a, b, c⟩; exact ⟨b, a, c⟩
  | trans h₁₂ _ ih₁ ih₂ =>
    intro hP t ht
    obtain ⟨e1, i1⟩ := ih₁ hP t ht
    obtain ⟨e2, i2⟩ := ih₂ (fun y hy => hP y (h₁₂.symm.subset hy)) t ht
    exact ⟨e1.trans e2, i1.trans i2⟩
end

/-! ## The strict end across the frame relation (the paper's (O1) for [End]) -/

section
variable (K : RunCtx) (φ : Future) {σ : Nat → Nat} {s₀ : SState} {ks : List Nat} {s s' : SState}

/-- A closure-live label's image is live in place. -/
theorem live_img (hr : FrameRel σ s₀ ks s s') (hsa : ShapeAt s) {l : Nat} (hl : s'.Live l) : s.Live (σ l) := by
  obtain ⟨q, -, hq⟩ := (SState.live_iff s' l).1 hl
  obtain ⟨p, hpf, rfl⟩ := hr.clShape q l hq
  have hp : s.shape p = some (σ l) := by rw [hr.topShape p hpf, hq]; rfl
  exact (SState.live_iff s _).2 ⟨p, hsa p _ hp, hp⟩

/-- **The strict end of corresponding labels** (`EndOk`, the paper's (O1) at an end): in place at `σ l` exactly when in
the closure at `l`. The holders correspond and are read through the renaming (`top_valAt`); the closure's holder reads
only live labels (locality), so a typed future on either side gives one on the other: through `σ` on the closure's live
labels (equal content types, `FrameRel.held`), the in-place records elsewhere (members, `HeldOk`). -/
theorem endOk_corr (hr : FrameRel σ s₀ ks s s') (hu : s.Uniq) (hsa : ShapeAt s) (hh : HeldOk K s)
    (hloc : ∀ p, Ochr.Meaning.FT (fun l => s'.Live l) (s'.valAt p)) {l : Nat} (hl : s'.Live l) :
    EndOk K φ s (σ l) ↔ EndOk K φ s' l := by
  obtain ⟨q, hq⟩ := SState.holderOf_of_live hl
  obtain ⟨p, hpf, rfl, hp⟩ := holder_frame hr hu hsa hq
  have hT : s.heldTy (σ l) = s'.heldTy l := (hr.held l hl).2
  unfold EndOk
  rw [hp, hq]
  simp only [Option.some.injEq, forall_eq', hT]
  constructor
  · intro h ψ' hψ'
    open Classical in
    let ψ : Future := fun m => if hm : ∃ l', s'.Live l' ∧ σ l' = m then ψ' (Classical.choose hm)
      else if m ∈ s.liveLabels then s.heldMem m else φ m
    have hψσ : ∀ l', s'.Live l' → ψ (σ l') = ψ' l' := fun l' hl' => by
      have hm : ∃ l'', s'.Live l'' ∧ σ l'' = σ l' := ⟨l', hl', rfl⟩
      simp only [ψ, dif_pos hm]
      rw [hr.inj _ _ (Classical.choose_spec hm).2]
    have hty : TypedFut K φ s ψ := by
      refine ⟨fun m hm => ?_, fun m hm => ?_⟩
      · have : ¬ ∃ l', s'.Live l' ∧ σ l' = m := fun ⟨l', hl', e⟩ => hm (e ▸ live_img hr hsa hl')
        simp only [ψ, dif_neg this, if_neg hm]
      · by_cases hm' : ∃ l', s'.Live l' ∧ σ l' = m
        · obtain ⟨l', hl', rfl⟩ := hm'
          rw [hψσ l' hl', (hr.held l' hl').2]; exact hψ'.2 l' hl'
        · simp only [ψ, dif_neg hm', if_pos hm]; exact hh m hm
    have := h ψ hty
    rw [top_valAt hr p hpf] at this
    rwa [hloc _ (renF σ ψ) ψ' fun l' hl' => hψσ l' hl'] at this
  · intro h ψ hψ
    let ψ' : Future := fun m => if m ∈ s'.liveLabels then ψ (σ m) else φ m
    have hty : TypedFut K φ s' ψ' := by
      refine ⟨fun m hm => by simp only [ψ', if_neg hm], fun m hm => ?_⟩
      simp only [ψ', if_pos hm]
      rw [← (hr.held m hm).2]; exact hψ.2 _ (live_img hr hsa hm)
    have := h ψ' hty
    rw [top_valAt hr p hpf]
    rwa [hloc _ (renF σ ψ) ψ' fun l' hl' => by
      have hl'' : l' ∈ s'.liveLabels := hl'
      simp only [ψ', renF, if_pos hl'']]

end

/-! ## The internal relation for [Access] -/

/-- What [Access] needs beside `FrameRel` (a part of the frame property's internal relation): in place one holder per
label, shape entries at positions, lending well founded (`LendWF`), the records members; in the closure one holder per
label, its locality (every position reads only live labels; a holder only labels above its own: `RInv`), its top frame
reading no parameter label (the paper's (I1)), a cell for every parameter label; and the renaming keeping the order of
the closure's labels but among parameter labels: parameter labels below the others (`order`), and monotone on the
others (`mono`; docs/31 D208's clause, true, not enough alone: the third referee's T6). -/
structure AccInv (K : RunCtx) (σ : Nat → Nat) (s₀ : SState) (ks : List Nat) (s s' : SState) : Prop where
  rel : FrameRel σ s₀ ks s s'
  uniq : s.Uniq
  shape : ShapeAt s
  lend : LendWF s
  held : HeldOk K s
  cells : ks.length ≤ (s'.env.headD {}).binds.length
  uniq' : s'.Uniq
  rinv' : SState.RInv (fun _ => False) s'
  noParam : ∀ p, p.frameOf = 1 → Ochr.Meaning.FT (fun l => σ l ∉ ks) (s'.valAt p)
  order : ∀ l l', s'.Live l → s'.Live l' → σ l ∈ ks → σ l' ∉ ks → l < l'
  mono : ∀ l l', s'.Live l → s'.Live l' → σ l ∉ ks → σ l' ∉ ks → l < l' → σ l < σ l'

section
variable {K : RunCtx} {σ : Nat → Nat} {s₀ : SState} {ks : List Nat} {s s' : SState}

theorem AccInv.loc (h : AccInv K σ s₀ ks s s') (p : Pos) : Ochr.Meaning.FT (fun l => s'.Live l) (s'.valAt p) :=
  (h.rinv'.1 p).mono fun _ hl => hl.elim (fun h => h.elim) id

theorem AccInv.shape' (h : AccInv K σ s₀ ks s s') : ShapeAt s' := fun p l hp => (h.rinv'.2.2 p l hp).1

/-- An end keeps a reading's independence of a set of labels when the holder's content keeps it too. -/
theorem ft_upd {S : Nat → Prop} {v x : SVal} {l : Nat} (hv : Ochr.Meaning.FT S v) (hx : Ochr.Meaning.FT S x) :
    Ochr.Meaning.FT S (fun ψ => v (ψ.upd l (x ψ))) := fun ψ ψ' e => hv _ _ fun y hy => by
  by_cases hyl : y = l
  · subst hyl; rw [Future.upd_same, Future.upd_same]; exact hx ψ ψ' e
  · rw [Future.upd_other _ _ hyl, Future.upd_other _ _ hyl]; exact e y hy

/-- The holder of a closure-live label is in the closure's frame. -/
theorem holder_frame1 (hr : FrameRel σ s₀ ks s s') {l : Nat} {q : Pos} (hq : s'.shape q = some l) : q.frameOf = 1 := by
  obtain ⟨p, -, rfl⟩ := hr.clShape q l hq
  cases p <;> rfl

theorem AccInv.endLabel (hs₀ : FrameStart s₀ ks) (h : AccInv K σ s₀ ks s s') {l : Nat} (hl : s'.Live l) :
    AccInv K σ s₀ ks (s.endLabel (σ l)) (s'.endLabel l) where
  rel := frameRel_endLabel h.rel hs₀ h.uniq h.shape h.cells hl
  uniq := h.uniq.endLabel _
  shape := shapeAt_endLabel h.shape _
  lend := h.lend.endLabel _
  held := h.held.endLabel K _
  cells := by rw [headD_len_endLabel]; exact h.cells
  uniq' := h.uniq'.endLabel _
  rinv' := SState.endLabel_rinv h.rinv' _
  noParam := fun p hp => by
    obtain ⟨q, hq⟩ := SState.holderOf_of_live hl
    obtain ⟨hqp, hqs⟩ := SState.holderOf_spec hq
    rw [SState.endLabel_eq hq]
    by_cases hpp : p ∈ s'.positions
    · rw [SState.endAt_valAt _ _ _ _ hpp]
      by_cases e : p = q
      · simp only [if_pos e]; exact Ochr.Meaning.FT.const _ _
      · simp only [if_neg e]; exact ft_upd (h.noParam p hp) (h.noParam q (holder_frame1 h.rel hqs))
    · rw [SState.endAt_valAt_not_mem _ _ _ _ hpp]; exact h.noParam p hp
  order := fun a b ha hb => h.order a b (live_of_endLabel ha) (live_of_endLabel hb)
  mono := fun a b ha hb => h.mono a b (live_of_endLabel ha) (live_of_endLabel hb)

/-- **Ends along corresponding lists, with the strict tests**: `frameRel_foldEnd` with the internal relation kept and
each end's strict test the same on both sides (`endOk_corr`). -/
theorem foldEnd_acc (φ : Future) (hs₀ : FrameStart s₀ ks) : ∀ (L : List Nat) {s s' : SState},
    AccInv K σ s₀ ks s s' → (∀ l ∈ L, s'.Live l) → L.Nodup →
    AccInv K σ s₀ ks ((L.map σ).foldl SState.endLabel s) (L.foldl SState.endLabel s') ∧
      (EndsOk K φ (L.map σ) s ↔ EndsOk K φ L s')
  | [], _, _, h, _, _ => ⟨h, Iff.rfl⟩
  | l :: L, s, s', h, hl, hnd => by
    have hnd' := List.nodup_cons.mp hnd
    have hl0 := hl l (by simp)
    obtain ⟨h1, h2⟩ := foldEnd_acc φ hs₀ L (h.endLabel hs₀ hl0)
      (fun m hm => SState.live_endLabel (hl m (by simp [hm])) (fun e => hnd'.1 (e ▸ hm))) hnd'.2
    refine ⟨by simpa only [List.map_cons, List.foldl_cons] using h1, ?_⟩
    rw [List.map_cons, endsOk_cons, endsOk_cons, h2, endOk_corr K φ h.rel h.uniq h.shape h.held h.loc hl0]
end

/-! ## One round -/

theorem split_sorted {P : Nat → Bool} : ∀ {L : List Nat}, L.Pairwise (· < ·) →
    (∀ x ∈ L, ∀ y ∈ L, P x = true → P y = false → x < y) → L = L.filter P ++ L.filter (fun x => !P x)
  | [], _, _ => rfl
  | x :: L, hp, hord => by
    obtain ⟨hx, hL⟩ := List.pairwise_cons.mp hp
    have ih := split_sorted hL fun a ha b hb => hord a (by simp [ha]) b (by simp [hb])
    cases hPx : P x
    · have hnil : L.filter P = [] := List.filter_eq_nil_iff.mpr fun y hy hPy =>
        Nat.lt_asymm (hx y hy) (hord y (by simp [hy]) x (by simp) (by simpa using hPy) hPx)
      rw [List.filter_cons_of_neg (by simp [hPx]), List.filter_cons_of_pos (by simp [hPx]), hnil, List.nil_append]
      rw [hnil, List.nil_append] at ih
      exact congrArg (x :: ·) ih
    · rw [List.filter_cons_of_pos (by simp [hPx]), List.filter_cons_of_neg (by simp [hPx]), List.cons_append]
      exact congrArg (x :: ·) ih

theorem eq_of_lt_sorted : ∀ {L M : List Nat}, L.Pairwise (· < ·) → M.Pairwise (· < ·) → (∀ x, x ∈ L ↔ x ∈ M) → L = M
  | [], [], _, _, _ => rfl
  | [], b :: _, _, _, h => absurd ((h b).2 (by simp)) (by simp)
  | a :: _, [], _, _, h => absurd ((h a).1 (by simp)) (by simp)
  | a :: L, b :: M, hL, hM, h => by
    obtain ⟨ha, hL'⟩ := List.pairwise_cons.mp hL
    obtain ⟨hb, hM'⟩ := List.pairwise_cons.mp hM
    have hab : a = b := by
      rcases List.mem_cons.mp ((h a).1 (by simp)) with e | e
      · exact e
      rcases List.mem_cons.mp ((h b).2 (by simp)) with e' | e'
      · exact e'.symm
      exact absurd (Nat.lt_trans (ha b e') (hb a e)) (Nat.lt_irrefl _)
    subst hab
    refine congrArg (a :: ·) (eq_of_lt_sorted hL' hM' fun x => ⟨fun hx => ?_, fun hx => ?_⟩)
    · rcases List.mem_cons.mp ((h x).1 (by simp [hx])) with e | e
      · exact absurd (e ▸ ha x hx) (Nat.lt_irrefl _)
      · exact e
    · rcases List.mem_cons.mp ((h x).2 (by simp [hx])) with e | e
      · exact absurd (e ▸ hb x hx) (Nat.lt_irrefl _)
      · exact e

section
variable {K : RunCtx} {σ : Nat → Nat} {s₀ : SState} {ks : List Nat} {s s' : SState}

theorem upPos_frameOf (c : Nat) (p : Pos) : (upPos c p).frameOf = 1 := by cases p <;> rfl

/-- In place the callee's frame reads no parameter label (the paper's (I1)), from the closure's. -/
theorem top_noParam (h : AccInv K σ s₀ ks s s') {q : Pos} (hq : q.frameOf = s₀.topIdx) :
    Ochr.Meaning.FT (fun y => y ∉ ks) (s.valAt q) := fun ψ ψ' e => by
  rw [top_valAt h.rel q hq ψ, top_valAt h.rel q hq ψ']
  exact h.noParam _ (upPos_frameOf _ _) _ _ fun l hl => e (σ l) hl

/-- A parameter label is held in the callee's frame (the caller holds none, `FrameStart.callerHeld`). -/
theorem param_holder_top (h : AccInv K σ s₀ ks s s') (hs₀ : FrameStart s₀ ks) {r : Pos} {k : Nat}
    (hr : s.shape r = some k) (hk : k ∈ ks) : r.frameOf = s₀.topIdx := by
  have h1 := frameOf_lt_of_mem (h.shape r k hr)
  rw [h.rel.frames.1] at h1
  have h2 : r.frameOf ≤ s₀.topIdx := by unfold SState.topIdx; omega
  rcases Nat.lt_or_eq_of_le h2 with h3 | h3
  · exact absurd hk (hs₀.callerHeld r k h3 (by rw [← h.rel.lowerShape r h3]; exact hr)).1
  · exact h3

theorem AccInv.pinv (h : AccInv K σ s₀ ks s s') (hs₀ : FrameStart s₀ ks) : PInv K (· ∈ ks) s where
  uniq := h.uniq
  lend := h.lend
  held := h.held
  reads := fun _ _ hr hk => top_noParam h (param_holder_top h hs₀ hr hk)

/-- **One round of [Access], in place, is the closure's round renamed**: the labels the in-place round ends, in label
order, are the parameter labels it reaches in some order, then the others in the closure's order (the renaming keeps
order off parameter labels, `AccInv.order`, `AccInv.mono`); the parameter labels' ends commute, strict tests included
(`perm_fold`, holders reading no parameter label). So the in-place round is the fold over the images of the closure's
round list, and passes its strict tests exactly when that fold does. -/
theorem round_corr (φ : Future) (hs₀ : FrameStart s₀ ks) (h : AccInv K σ s₀ ks s s') {q : Pos}
    (hq : q.frameOf = s₀.topIdx) (hit : List Step → Bool) :
    (s.liveLabels.filter (s.reached q hit)).foldl SState.endLabel s =
        ((s'.liveLabels.filter (s'.reached (upPos ks.length q) hit)).map σ).foldl SState.endLabel s ∧
      (EndsOk K φ (s.liveLabels.filter (s.reached q hit)) s ↔
        EndsOk K φ ((s'.liveLabels.filter (s'.reached (upPos ks.length q) hit)).map σ) s) := by
  generalize hAdef : s.liveLabels.filter (s.reached q hit) = A
  generalize hBdef : s'.liveLabels.filter (s'.reached (upPos ks.length q) hit) = B
  have hA : A.Pairwise (· < ·) := hAdef ▸ (liveLabels_lt h.uniq).filter _
  have hB : B.Pairwise (· < ·) := hBdef ▸ (liveLabels_lt h.uniq').filter _
  have hBl : ∀ l ∈ B, s'.Live l := fun l hl => by rw [← hBdef] at hl; exact (List.mem_filter.mp hl).1
  have hmem : ∀ m, m ∈ A ↔ ∃ l ∈ B, σ l = m := fun m => by
    rw [← hAdef, List.mem_filter]
    have := reached_corr h.rel hs₀ h.shape h.shape' hq hit m
    refine this.trans ⟨fun ⟨l, e, hl, hre⟩ => ⟨l, by rw [← hBdef, List.mem_filter]; exact ⟨hl, hre⟩, e.symm⟩,
      fun ⟨l, hl, e⟩ => ⟨l, e.symm, ?_⟩⟩
    rw [← hBdef, List.mem_filter] at hl; exact hl
  let Pk : Nat → Bool := fun m => decide (m ∈ ks)
  have hsplitA : A = A.filter Pk ++ A.filter (fun x => !Pk x) := split_sorted hA fun x hx y hy hPx hPy => by
    have hxk : x ∈ ks := by simpa [Pk] using hPx
    have hyk : y ∉ ks := by simpa [Pk] using hPy
    obtain ⟨l, hl, rfl⟩ := (hmem y).1 hy
    have h1 := hs₀.ks_lt x hxk
    rcases h.rel.topLabels l (hBl l hl) with h2 | h2
    · exact absurd h2 hyk
    · omega
  have hsplitB : B = B.filter (fun l => Pk (σ l)) ++ B.filter (fun l => !Pk (σ l)) :=
    split_sorted hB fun x hx y hy hPx hPy =>
      h.order x y (hBl x hx) (hBl y hy) (by simpa [Pk] using hPx) (by simpa [Pk] using hPy)
  have hc : A.filter (fun x => !Pk x) = (B.filter (fun l => !Pk (σ l))).map σ := by
    refine eq_of_lt_sorted (hA.filter _) ?_ fun x => ?_
    · rw [List.pairwise_map]
      refine ((List.Pairwise.and_mem.mp (hB.filter _)).imp fun ⟨ha, hb, hab⟩ => ?_)
      obtain ⟨ha1, ha2⟩ := List.mem_filter.mp ha
      obtain ⟨hb1, hb2⟩ := List.mem_filter.mp hb
      exact h.mono _ _ (hBl _ ha1) (hBl _ hb1) (by simpa [Pk] using ha2) (by simpa [Pk] using hb2) hab
    · rw [List.mem_filter, hmem, List.mem_map]
      constructor
      · rintro ⟨⟨l, hl, rfl⟩, hk⟩; exact ⟨l, List.mem_filter.mpr ⟨hl, hk⟩, rfl⟩
      · rintro ⟨l, hl, rfl⟩; obtain ⟨hl1, hl2⟩ := List.mem_filter.mp hl; exact ⟨⟨l, hl1, rfl⟩, hl2⟩
  have hp : (A.filter Pk).Perm ((B.filter (fun l => Pk (σ l))).map σ) := by
    refine (List.perm_ext_iff_of_nodup ?_ ?_).2 fun x => ?_
    · exact List.nodup_iff_pairwise_ne.2 ((hA.filter _).imp Nat.ne_of_lt)
    · rw [List.nodup_iff_pairwise_ne, List.pairwise_map]
      exact (hB.filter _).imp fun hab e => Nat.ne_of_lt hab (h.rel.inj _ _ e)
    · rw [List.mem_filter, hmem, List.mem_map]
      constructor
      · rintro ⟨⟨l, hl, rfl⟩, hk⟩; exact ⟨l, List.mem_filter.mpr ⟨hl, hk⟩, rfl⟩
      · rintro ⟨l, hl, rfl⟩; obtain ⟨hl1, hl2⟩ := List.mem_filter.mp hl; exact ⟨⟨l, hl1, rfl⟩, hl2⟩
  have hP : ∀ x ∈ A.filter Pk, x ∈ ks := fun x hx => by simpa [Pk] using (List.mem_filter.mp hx).2
  obtain ⟨e, i⟩ := perm_fold K φ hp hP s (h.pinv hs₀)
  rw [hsplitA, hsplitB, List.map_append, ← hc, List.foldl_append, List.foldl_append, e, endsOk_append,
    endsOk_append, i, e]
  exact ⟨rfl, Iff.rfl⟩
end

/-! ## The rounds, to the fixpoint -/

theorem iterR_add {α} (g : α → α) (n : Nat) : ∀ (d : Nat) (a : α), SState.iterR g (n + d) a = SState.iterR g d (SState.iterR g n a)
  | 0, _ => rfl
  | d + 1, a => by show g (SState.iterR g (n + d) a) = g (SState.iterR g d (SState.iterR g n a)); rw [iterR_add g n d a]

/-- A round that changes nothing reaches no live label. -/
theorem round_nil_of_fix {t : SState} {p : Pos} {hit : List Step → Bool} (h : SState.accStep p hit t = t) :
    t.liveLabels.filter (t.reached p hit) = [] := by
  cases hL : t.liveLabels.filter (t.reached p hit) with
  | nil => rfl
  | cons x L =>
    exfalso
    have hx : x ∈ t.liveLabels := (List.mem_filter.mp (hL ▸ List.mem_cons_self : x ∈ _)).1
    have h1 := SState.liveLabels_endLabel_lt t x hx
    have h2 := SState.liveLabels_foldl_endLabel_le L (t.endLabel x)
    have e : SState.accStep p hit t = L.foldl SState.endLabel (t.endLabel x) := by
      unfold SState.accStep; rw [hL]; rfl
    rw [← e, h] at h2
    omega

/-- **The rounds reach their fixpoint within as many rounds as there are live labels**: each round that ends something
ends a live label, and no end makes one live. -/
theorem iter_fix (p : Pos) (hit : List Step → Bool) (t : SState) :
    SState.accStep p hit (SState.iterR (SState.accStep p hit) t.liveLabels.length t) =
      SState.iterR (SState.accStep p hit) t.liveLabels.length t := by
  have key : ∀ k, SState.accStep p hit (SState.iterR (SState.accStep p hit) k t) = SState.iterR (SState.accStep p hit) k t ∨
      (SState.iterR (SState.accStep p hit) k t).liveLabels.length + k ≤ t.liveLabels.length := by
    intro k
    induction k with
    | zero => exact .inr (by simp [SState.iterR])
    | succ k ih =>
      rcases ih with h | h
      · exact .inl (by
          show SState.accStep p hit (SState.accStep p hit (SState.iterR (SState.accStep p hit) k t)) =
            SState.accStep p hit (SState.iterR (SState.accStep p hit) k t)
          rw [h, h])
      · by_cases hf : SState.accStep p hit (SState.iterR (SState.accStep p hit) k t) = SState.iterR (SState.accStep p hit) k t
        · exact .inl (by
            show SState.accStep p hit (SState.accStep p hit (SState.iterR (SState.accStep p hit) k t)) =
              SState.accStep p hit (SState.iterR (SState.accStep p hit) k t)
            rw [hf, hf])
        · refine .inr ?_
          show (SState.accStep p hit (SState.iterR (SState.accStep p hit) k t)).liveLabels.length + (k + 1) ≤ _
          generalize hu : SState.iterR (SState.accStep p hit) k t = u at h hf ⊢
          cases hL : u.liveLabels.filter (u.reached p hit) with
          | nil => exact absurd (by unfold SState.accStep; rw [hL]; rfl) hf
          | cons x L =>
            have hx : x ∈ u.liveLabels := (List.mem_filter.mp (hL ▸ List.mem_cons_self : x ∈ _)).1
            have h1 := SState.liveLabels_endLabel_lt u x hx
            have h2 := SState.liveLabels_foldl_endLabel_le L (u.endLabel x)
            have e : SState.accStep p hit u = L.foldl SState.endLabel (u.endLabel x) := by
              unfold SState.accStep; rw [hL]; rfl
            rw [e]; omega
  rcases key t.liveLabels.length with h | h
  · exact h
  · generalize hu : SState.iterR (SState.accStep p hit) t.liveLabels.length t = u at h
    have h0 : u.liveLabels = [] := List.eq_nil_of_length_eq_zero (by omega)
    unfold SState.accStep; rw [h0]; rfl

theorem iter_stable (p : Pos) (hit : List Step → Bool) (t : SState) (d : Nat) :
    SState.iterR (SState.accStep p hit) (t.liveLabels.length + d) t = SState.iterR (SState.accStep p hit) t.liveLabels.length t := by
  rw [iterR_add, SState.iterR_fix _ _ (iter_fix p hit t)]

theorem access_iterR (t : SState) (p : Pos) (hit : List Step → Bool) :
    t.access p hit = SState.iterR (SState.accStep p hit) t.liveLabels.length t := by
  rw [SState.access_eq, SState.foldl_range_iterR]

theorem accessOk_iff (K : RunCtx) (φ : Future) (t : SState) (p : Pos) (hit : List Step → Bool) :
    AccessOk K φ t p hit ↔ ∀ k, k < t.liveLabels.length →
      EndsOk K φ ((SState.iterR (SState.accStep p hit) k t).liveLabels.filter ((SState.iterR (SState.accStep p hit) k t).reached p hit))
        (SState.iterR (SState.accStep p hit) k t) := by
  unfold AccessOk
  have e : ∀ k, (List.range k).foldl (fun u _ => accRound p hit u) t = SState.iterR (SState.accStep p hit) k t :=
    fun k => SState.foldl_range_iterR (SState.accStep p hit) k t
  simp only [e]

section
variable {K : RunCtx} {σ : Nat → Nat} {s₀ : SState} {ks : List Nat} {s s' : SState}

/-- One round on each side, related: the internal relation kept and the round's strict tests the same. -/
theorem step_corr (φ : Future) (hs₀ : FrameStart s₀ ks) (h : AccInv K σ s₀ ks s s') {q : Pos}
    (hq : q.frameOf = s₀.topIdx) (hit : List Step → Bool) :
    AccInv K σ s₀ ks (SState.accStep q hit s) (SState.accStep (upPos ks.length q) hit s') ∧
      (EndsOk K φ (s.liveLabels.filter (s.reached q hit)) s ↔
        EndsOk K φ (s'.liveLabels.filter (s'.reached (upPos ks.length q) hit)) s') := by
  obtain ⟨e, i⟩ := round_corr φ hs₀ h hq hit
  have hBl : ∀ l ∈ s'.liveLabels.filter (s'.reached (upPos ks.length q) hit), s'.Live l :=
    fun l hl => (List.mem_filter.mp hl).1
  have hnd := List.nodup_iff_pairwise_ne.2
    (((liveLabels_lt h.uniq').filter (s'.reached (upPos ks.length q) hit)).imp Nat.ne_of_lt)
  obtain ⟨h1, h2⟩ := foldEnd_acc φ hs₀ _ h hBl hnd
  refine ⟨?_, i.trans h2⟩
  show AccInv K σ s₀ ks ((s.liveLabels.filter (s.reached q hit)).foldl SState.endLabel s) _
  rw [e]; exact h1

theorem iter_corr (φ : Future) (hs₀ : FrameStart s₀ ks) (h : AccInv K σ s₀ ks s s') {q : Pos}
    (hq : q.frameOf = s₀.topIdx) (hit : List Step → Bool) : ∀ k,
    AccInv K σ s₀ ks (SState.iterR (SState.accStep q hit) k s) (SState.iterR (SState.accStep (upPos ks.length q) hit) k s') ∧
      (EndsOk K φ ((SState.iterR (SState.accStep q hit) k s).liveLabels.filter ((SState.iterR (SState.accStep q hit) k s).reached q hit))
          (SState.iterR (SState.accStep q hit) k s) ↔
        EndsOk K φ ((SState.iterR (SState.accStep (upPos ks.length q) hit) k s').liveLabels.filter
          ((SState.iterR (SState.accStep (upPos ks.length q) hit) k s').reached (upPos ks.length q) hit))
          (SState.iterR (SState.accStep (upPos ks.length q) hit) k s'))
  | 0 => step_corr φ hs₀ h hq hit |>.imp (fun _ => h) id
  | k + 1 => by
    have ih := (iter_corr φ hs₀ h hq hit k).1
    exact step_corr φ hs₀ (step_corr φ hs₀ ih hq hit).1 hq hit |>.imp (fun _ => (step_corr φ hs₀ ih hq hit).1) id

/-- **[Access] against the frame relation** (the paper's (O4); docs/31 D215): accessing a place of the callee's frame in
place and the corresponding place in the function's own frame keeps the internal relation (`FrameRel` with what [Access]
needs, `AccInv`), and the strict tests of the two accesses (`AccessOk`) pass together. In place there are more rounds (the
caller's labels are live too), all past the fixpoint. Hypotheses: `FrameStart` at the call and `AccInv`, whose new clauses
are `LendWF` in place (lending well founded, sites at holders under `*`) and the renaming's order on the closure's labels. -/
theorem frameRel_access (φ : Future) (hs₀ : FrameStart s₀ ks) (h : AccInv K σ s₀ ks s s') {q : Pos}
    (hq : q.frameOf = s₀.topIdx) (hit : List Step → Bool) :
    AccInv K σ s₀ ks (s.access q hit) (s'.access (upPos ks.length q) hit) ∧
      (AccessOk K φ s q hit ↔ AccessOk K φ s' (upPos ks.length q) hit) := by
  have hc := iter_corr φ hs₀ h hq hit
  refine ⟨?_, ?_⟩
  · rw [access_iterR, access_iterR, ← iter_stable q hit s s'.liveLabels.length,
      ← iter_stable (upPos ks.length q) hit s' s.liveLabels.length, Nat.add_comm s'.liveLabels.length]
    exact (hc _).1
  · have nil : ∀ (p : Pos) (t : SState) (k : Nat), t.liveLabels.length ≤ k →
        (SState.iterR (SState.accStep p hit) k t).liveLabels.filter ((SState.iterR (SState.accStep p hit) k t).reached p hit) = [] :=
      fun p t k hk => by
        obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hk
        rw [iter_stable]; exact round_nil_of_fix (iter_fix p hit t)
    rw [accessOk_iff, accessOk_iff]
    constructor
    · intro H k _
      by_cases hk : k < s.liveLabels.length
      · exact (hc k).2.1 (H k hk)
      · exact (hc k).2.1 (by rw [nil q s k (Nat.le_of_not_lt hk)]; trivial)
    · intro H k _
      by_cases hk : k < s'.liveLabels.length
      · exact (hc k).2.2 (H k hk)
      · exact (hc k).2.2 (by rw [nil _ s' k (Nat.le_of_not_lt hk)]; trivial)
end

end Ochr.Meaning.Steps.Form.FrameEnd
