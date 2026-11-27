import Ochr.Meaning.Steps.FrameOps

/-!
# The match clause of the frame property (lead34; docs/31 D219)

The paper's per-clause lemma for a match (`18-principles`, `<sec-frame-proof>`, the row "A match"): the tag, [Entry]'s
accesses and invalidation, the arm (induction), the join's drop and [Entry]'s lending, each against the internal relation
`FrameInv`. This file holds the operations' correspondences; the clause itself is `runFrameI_matchNat` and
`runFrameI_matchInd` (below, once the parts are in).
-/

namespace Ochr.Meaning.Steps.Form.FrameEnd

open Ochr Ochr.Meaning

/-! ## What reads the callee's frame's skeleton reads the same on both sides -/

section
variable {K : RunCtx} {σ : Nat → Nat} {s₀ : SState} {ks : List Nat} {s s' : SState}

/-- **The scope (the top frame's declared readings) is the same on both sides**: every static decision reads it
(`Decisions.flags`, `blockCaps`, `joinMoves`, `invalidated`, `copy`, `placeDecl`, `declOf`). -/
theorem scopeOf_corr (hr : FrameRel σ s₀ ks s s') : scopeOf s = scopeOf s' := by
  obtain ⟨F, F', hF, hF', hlen, hb, -⟩ := hr.top
  unfold scopeOf; rw [hF, hF']
  dsimp only
  congr 1
  refine List.ext_getElem (by simp [hlen]) fun i h1 h2 => ?_
  simp only [List.getElem_map]
  have hi : i < F'.binds.length := by simpa [hlen] using h2
  exact (hb i _ _ (List.getElem?_eq_getElem (by simpa using h1)) (List.getElem?_eq_getElem hi)).2.1

/-- `Sem.updAt` does not read its type argument (it is only passed down). -/
theorem updAt_T (dm : DataModel) (Γ : List IndDecl) (f : Sem → Sem) :
    ∀ (st : List Step) (T T' : TyS), Sem.updAt dm Γ T f st = Sem.updAt dm Γ T' f st
  | [], _, _ => by funext v; rw [Sem.updAt.eq_def, Sem.updAt.eq_def]
  | .deref :: sts, T, T' => by
    funext v; rw [Sem.updAt.eq_def, Sem.updAt.eq_def]; dsimp only; rw [updAt_T dm Γ f sts T T']
  | .proj i :: sts, T, T' => by
    funext v; rw [Sem.updAt.eq_def, Sem.updAt.eq_def]; dsimp only; rw [updAt_T dm Γ f sts T T']
  | .field g :: sts, T, T' => by
    funext v; rw [Sem.updAt.eq_def, Sem.updAt.eq_def]; dsimp only; rw [updAt_T dm Γ f sts T T']

/-- **(O1), for any test of one position at every typed future** (the pattern of `endOk_corr`): a top-frame position
passes a test at every typed future in place exactly when its counterpart passes it at every typed future of the
closure. The closure's value reads only live labels (locality); a typed future on either side gives one on the other,
through `σ` on the closure's live labels (equal content types, `FrameRel.held`), the in-place records elsewhere. -/
theorem typedAll_corr (K : RunCtx) (φ : Future) (hr : FrameRel σ s₀ ks s s') (hsa : ShapeAt s) (hh : HeldOk K s)
    (hloc : ∀ p, Ochr.Meaning.FT (fun l => s'.Live l) (s'.valAt p)) {p : Pos} (hp : p.frameOf = s₀.topIdx)
    (P : Sem → Prop) :
    (∀ ψ, TypedFut K φ s ψ → P (s.valAt p ψ)) ↔ (∀ ψ', TypedFut K φ s' ψ' → P (s'.valAt (upPos ks.length p) ψ')) := by
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
    rw [top_valAt hr p hp] at this
    rwa [hloc _ (renF σ ψ) ψ' fun l' hl' => hψσ l' hl'] at this
  · intro h ψ hψ
    let ψ' : Future := fun m => if m ∈ s'.liveLabels then ψ (σ m) else φ m
    have hty : TypedFut K φ s' ψ' := by
      refine ⟨fun m hm => by simp only [ψ', if_neg hm], fun m hm => ?_⟩
      simp only [ψ', if_pos hm]
      rw [← (hr.held m hm).2]; exact hψ.2 _ (live_img hr hsa hm)
    have := h ψ' hty
    rw [top_valAt hr p hp]
    rwa [hloc _ (renF σ ψ) ψ' fun l' hl' => by
      have hl'' : l' ∈ s'.liveLabels := hl'
      simp only [ψ', renF, if_pos hl'']]

/-- The future at which the moved places are read (`lentFuture`: every live label `err`) is read alike: a closure
position reads only live labels, whose images are live in place. -/
theorem lentFuture_corr (φ : Future) (hr : FrameRel σ s₀ ks s s') (hsa : ShapeAt s)
    (hloc : ∀ p, Ochr.Meaning.FT (fun l => s'.Live l) (s'.valAt p)) {q : Pos} (hq : q.frameOf = s₀.topIdx) :
    s.valAt q (s.lentFuture φ) = s'.valAt (upPos ks.length q) (s'.lentFuture φ) := by
  rw [top_valAt hr q hq]
  refine hloc _ _ _ fun l hl => ?_
  have hl' : σ l ∈ s.liveLabels := live_img hr hsa hl
  have hl'' : l ∈ s'.liveLabels := hl
  simp only [renF, SState.lentFuture, if_pos hl', if_pos hl'']

/-- **The places moved at a match's start (`movedPlaces`) are the same on both sides**: read off the callee's frame at
the future giving every live label `err`, with the holders' `*`. -/
theorem movedPlaces_corr (φ : Future) (hr : FrameRel σ s₀ ks s s') (hsa : ShapeAt s)
    (hloc : ∀ p, Ochr.Meaning.FT (fun l => s'.Live l) (s'.valAt p)) : movedPlaces φ s = movedPlaces φ s' := by
  obtain ⟨F, F', hF, hF', hlen, -⟩ := hr.top
  unfold movedPlaces
  rw [hF, hF']
  dsimp only
  rw [hlen]
  congr 1
  funext i
  by_cases hi' : i < F'.binds.length
  · have hv : s.varPos i = some (.bind s₀.topIdx (F'.binds.length - 1 - i)) := by
      unfold SState.varPos; rw [hF]; simp [hlen, hi', topIdx_eq hr]
    have hv' : s'.varPos i = some (upPos ks.length (.bind s₀.topIdx (F'.binds.length - 1 - i))) := by
      unfold SState.varPos; rw [hF', topIdx_cl hr]; simp [hi', upPos]
    rw [hv, hv']
    dsimp only
    rw [lentFuture_corr φ hr hsa hloc rfl, hr.topShape _ rfl]
    cases s'.shape (upPos ks.length (.bind s₀.topIdx (F'.binds.length - 1 - i))) <;> rfl
  · have hv : s.varPos i = none := by unfold SState.varPos; rw [hF]; simp [hlen, hi']
    have hv' : s'.varPos i = none := by unfold SState.varPos; rw [hF']; simp [hi']
    rw [hv, hv']

end

/-! ## Outcomes of state operations, and folds of them -/

/-- Two outcomes of an operation agree: both fail, or the same value at states related by `R`. -/
def OAgree {α : Type 3} (R : SState → SState → Prop) : Option (α × SState) → Option (α × SState) → Prop
  | some (a, t), some (a', t') => a = a' ∧ R t t'
  | none, none => True
  | _, _ => False

/-- **A fold of one operation along a list, on related states** (the entry's accesses, D112's invalidation, the join's
drop): when one step keeps the relation and its strict test is the same on both sides, so does the fold. -/
theorem foldOk_corr {α : Type} {R : SState → SState → Prop} (f : SState → α → SState) (ok : SState → α → Prop)
    (h : ∀ t t' x, R t t' → R (f t x) (f t' x) ∧ (ok t x ↔ ok t' x)) :
    ∀ (xs : List α) (t t' : SState), R t t' → R (xs.foldl f t) (xs.foldl f t') ∧ (FoldOk f ok xs t ↔ FoldOk f ok xs t')
  | [], _, _, hR => ⟨hR, Iff.rfl⟩
  | x :: xs, t, t', hR => by
    obtain ⟨h1, h2⟩ := h t t' x hR
    obtain ⟨h3, h4⟩ := foldOk_corr f ok h xs _ _ h1
    exact ⟨h3, by simp only [FoldOk]; rw [h2, h4]⟩

theorem ft_comp {S : Nat → Prop} {f : SVal} (hf : Ochr.Meaning.FT S f) (g : Sem → Sem) :
    Ochr.Meaning.FT S (fun ψ => g (f ψ)) := fun ψ ψ' e => congrArg g (hf ψ ψ' e)

theorem nextLoan_access (t : SState) (p : Pos) (hit : List Step → Bool) : (t.access p hit).nextLoan = t.nextLoan := by
  unfold SState.access
  generalize List.range t.liveLabels.length = L
  induction L generalizing t with
  | nil => rfl
  | cons _ L ih =>
    simp only [List.foldl_cons]
    rw [ih]
    generalize t.liveLabels.filter (t.reached p hit) = M
    induction M generalizing t with
    | nil => rfl
    | cons m M ih' => simp only [List.foldl_cons]; rw [ih', nextLoan_endLabel]

section
variable {K : RunCtx} {σ : Nat → Nat} {s₀ : SState} {ks : List Nat} {s s' : SState}

/-- **A write of a function of the old content, at corresponding positions of the callee's frame, keeps the internal
relation for [Access]**: `accInv_setAt` with the locality clauses inherited from the old value (a function of it reads
what it reads). -/
theorem accInv_setAt_fn (h : AccInv K σ s₀ ks s s') {p : Pos} (hp : p.frameOf = s₀.topIdx) (g : Sem → Sem) :
    AccInv K σ s₀ ks (s.setAt p fun ψ => g (s.valAt p ψ))
      (s'.setAt (upPos ks.length p) fun ψ => g (s'.valAt (upPos ks.length p) ψ)) := by
  refine accInv_setAt h hp (fun ψ => by rw [top_valAt h.rel p hp]) (ft_comp (h.loc _) g)
    (ft_comp (h.noParam _ (upPos_frameOf _ _)) g) fun x hx => ?_
  have hpos := h.shape' _ _ hx
  exact ft_comp ((h.rinv'.2.1 _ x hpos hx).mono fun y hy => hy.elim (fun h => h.1.elim) id) g

/-- **`setContent` across the internal relation** (the paper's (O5) with (O1)): defined on both sides or on neither (its
test at every typed future, through `typedAll_corr`; `Sem.updAt` does not read its type), and related states after. -/
theorem setContent_corr (φ : Future) (h : AccInv K σ s₀ ks s s') {pos : Pos} (hp : pos.frameOf = s₀.topIdx)
    (steps : List Step) (v : Sem) :
    OAgree (AccInv K σ s₀ ks) (setContent K φ pos steps v s) (setContent K φ (upPos ks.length pos) steps v s') := by
  unfold setContent
  dsimp only
  have hc := typedAll_corr K φ h.rel h.shape h.held h.loc hp
    (fun x => (Sem.updAt K.dm K.Γ (s.tyAt pos) (fun _ => v) steps x).isSome = true)
  have eT := updAt_T K.dm K.Γ (fun _ => v) steps (s'.tyAt (upPos ks.length pos)) (s.tyAt pos)
  rw [eT]
  split
  · rename_i hd
    rw [if_pos (hc.1 hd)]
    exact ⟨rfl, accInv_setAt_fn h hp fun x => (Sem.updAt K.dm K.Γ (s.tyAt pos) (fun _ => v) steps x).getD .err⟩
  · rename_i hd
    rw [if_neg (fun h' => hd (hc.2 h'))]; trivial

/-- **Whether a live label is lent at a top-frame path is the same on both sides** (`reached_corr`). -/
theorem anyReached_corr (hs₀ : FrameStart s₀ ks) (h : AccInv K σ s₀ ks s s') {q : Pos} (hq : q.frameOf = s₀.topIdx)
    (hit : List Step → Bool) :
    s.liveLabels.any (s.reached q hit) = s'.liveLabels.any (s'.reached (upPos ks.length q) hit) := by
  apply Bool.eq_iff_iff.mpr
  simp only [List.any_eq_true]
  constructor
  · rintro ⟨m, hm, hre⟩
    obtain ⟨l, -, hl, hre'⟩ := (reached_corr h.rel hs₀ h.shape h.shape' hq hit m).1 ⟨hm, hre⟩
    exact ⟨l, hl, hre'⟩
  · rintro ⟨l, hl, hre'⟩
    exact ⟨σ l, ((reached_corr h.rel hs₀ h.shape h.shape' hq hit (σ l)).2 ⟨l, rfl, hl, hre'⟩).1,
      ((reached_corr h.rel hs₀ h.shape h.shape' hq hit (σ l)).2 ⟨l, rfl, hl, hre'⟩).2⟩

theorem lentPrefix_corr (hs₀ : FrameStart s₀ ks) (h : AccInv K σ s₀ ks s s') {q : Pos} (hq : q.frameOf = s₀.topIdx)
    (steps : List Step) : lentPrefix s q steps = lentPrefix s' (upPos ks.length q) steps := by
  unfold lentPrefix
  congr 1
  funext ψ
  exact anyReached_corr hs₀ h hq _

/-- **`movedPlace`'s access of a lent prefix, across the internal relation**: the same prefix found, the accesses
related, their strict tests the same. -/
theorem accessLentPrefix_corr (φ : Future) (hs₀ : FrameStart s₀ ks) (h : AccInv K σ s₀ ks s s') {q : Pos}
    (hq : q.frameOf = s₀.topIdx) (steps : List Step) :
    AccInv K σ s₀ ks (accessLentPrefix q steps s) (accessLentPrefix (upPos ks.length q) steps s') ∧
      (LentPrefixOk K φ q steps s ↔ LentPrefixOk K φ (upPos ks.length q) steps s') := by
  unfold accessLentPrefix LentPrefixOk
  rw [← lentPrefix_corr hs₀ h hq steps]
  cases lentPrefix s q steps with
  | none => exact ⟨h, Iff.rfl⟩
  | some ψ => exact frameRel_access φ hs₀ h hq (dataHit ψ)


/-! ## [Entry]'s accesses and D112's invalidation -/

/-- One invalidated place (D112): its access, then `⊥` written where the write is defined. -/
theorem invalidateOne_corr (φ : Future) (hs₀ : FrameStart s₀ ks) (q : Place) {t t' : SState}
    (h : AccInv K σ s₀ ks t t') :
    AccInv K σ s₀ ks (invalidateOne K φ t q) (invalidateOne K φ t' q) ∧ (InvalOneOk K φ t q ↔ InvalOneOk K φ t' q) := by
  obtain ⟨hres, hframe⟩ := resolve_corr h.rel q
  unfold invalidateOne InvalOneOk
  rw [hres]
  cases hrq : resolve t q with
  | none => exact ⟨h, Iff.rfl⟩
  | some x =>
    obtain ⟨pos, steps⟩ := x
    have hp := hframe pos steps hrq
    dsimp only [Option.map_some]
    obtain ⟨hacc, hok⟩ := frameRel_access φ hs₀ h hp (dataHit steps)
    refine ⟨?_, hok⟩
    have hsc := setContent_corr φ hacc hp steps .moved
    cases e1 : setContent K φ pos steps .moved (t.access pos (dataHit steps)) with
    | none =>
      rw [e1] at hsc
      cases e2 : setContent K φ (upPos ks.length pos) steps .moved (t'.access (upPos ks.length pos) (dataHit steps)) with
      | none => exact hacc
      | some _ => rw [e2] at hsc; exact hsc.elim
    | some y =>
      rw [e1] at hsc
      cases e2 : setContent K φ (upPos ks.length pos) steps .moved (t'.access (upPos ks.length pos) (dataHit steps)) with
      | none => rw [e2] at hsc; exact hsc.elim
      | some y' => rw [e2] at hsc; obtain ⟨⟨⟩, a⟩ := y; obtain ⟨⟨⟩, a'⟩ := y'; exact hsc.2

theorem invalidate_corr (φ : Future) (hs₀ : FrameStart s₀ ks) (p : Place) {t t' : SState}
    (h : AccInv K σ s₀ ks t t') :
    AccInv K σ s₀ ks (invalidate K φ p t) (invalidate K φ p t') ∧ (InvalidateOk K φ p t ↔ InvalidateOk K φ p t') := by
  unfold invalidate InvalidateOk
  rw [scopeOf_corr h.rel]
  exact foldOk_corr (R := AccInv K σ s₀ ks) (invalidateOne K φ) (InvalOneOk K φ)
    (fun t t' q hR => invalidateOne_corr φ hs₀ q hR) _ _ _ h

theorem entryReroot_corr (φ : Future) (hs₀ : FrameStart s₀ ks) (q : Place) {t t' : SState}
    (h : AccInv K σ s₀ ks t t') :
    AccInv K σ s₀ ks (entryReroot t q) (entryReroot t' q) ∧ (EntryRerootOk K φ t q ↔ EntryRerootOk K φ t' q) := by
  obtain ⟨hres, hframe⟩ := resolve_corr h.rel q
  unfold entryReroot EntryRerootOk
  rw [hres]
  cases hrq : resolve t q with
  | none => exact ⟨h, Iff.rfl⟩
  | some x =>
    obtain ⟨pos, steps⟩ := x
    exact accessLentPrefix_corr φ hs₀ h (hframe pos steps hrq) steps

theorem entryCap_corr (φ : Future) (hs₀ : FrameStart s₀ ks) (qk : Place × Nat) {t t' : SState}
    (h : AccInv K σ s₀ ks t t') :
    AccInv K σ s₀ ks (entryCap K φ t qk) (entryCap K φ t' qk) ∧ (EntryCapOk K φ t qk ↔ EntryCapOk K φ t' qk) := by
  obtain ⟨hres, hframe⟩ := resolve_corr h.rel qk.1
  have key : AccInv K σ s₀ ks (match resolve t qk.1 with | some (pos, steps) => t.access pos (dataHit steps) | none => t)
      (match resolve t' qk.1 with | some (pos, steps) => t'.access pos (dataHit steps) | none => t') ∧
      ((match resolve t qk.1 with | some (pos, steps) => AccessOk K φ t pos (dataHit steps) | none => True) ↔
       (match resolve t' qk.1 with | some (pos, steps) => AccessOk K φ t' pos (dataHit steps) | none => True)) := by
    rw [hres]
    cases hrq : resolve t qk.1 with
    | none => exact ⟨h, Iff.rfl⟩
    | some x =>
      obtain ⟨pos, steps⟩ := x
      exact frameRel_access φ hs₀ h (hframe pos steps hrq) (dataHit steps)
  obtain ⟨h1, h2⟩ := key
  obtain ⟨h3, h4⟩ := invalidate_corr φ hs₀ qk.1 h1
  unfold entryCap EntryCapOk
  dsimp only
  refine ⟨?_, and_congr h2 (imp_congr_right fun _ => h4)⟩
  split
  · exact h3
  · exact h1

/-- **[Entry]'s accesses across the internal relation** (the paper's row "A match": [Entry]'s accesses and invalidation,
(O4), (O9)): the re-rooted places' lent prefixes, then each capture accessed as data and, for a capture by `&`,
invalidated; related states after, and the strict tests the same. -/
theorem entryAccess_corr (φ : Future) (hs₀ : FrameStart s₀ ks) (bc : List Place × List (Place × Nat)) {t t' : SState}
    (h : AccInv K σ s₀ ks t t') :
    AccInv K σ s₀ ks (entryAccess K φ bc t) (entryAccess K φ bc t') ∧
      (EntryAccessOk K φ bc t ↔ EntryAccessOk K φ bc t') := by
  obtain ⟨h1, h2⟩ := foldOk_corr (R := AccInv K σ s₀ ks) entryReroot (EntryRerootOk K φ)
    (fun t t' q hR => entryReroot_corr φ hs₀ q hR) bc.1 t t' h
  obtain ⟨h3, h4⟩ := foldOk_corr (R := AccInv K σ s₀ ks) (entryCap K φ) (EntryCapOk K φ)
    (fun t t' qk hR => entryCap_corr φ hs₀ qk hR) bc.2 _ _ h1
  exact ⟨h3, and_congr h2 h4⟩

/-! ## The join's drop -/

open Classical in
/-- One dropped place at the join (`dropAt`): a borrow held at a root ends (`AccInv.endLabel`, `endOk_corr`);
otherwise, unless the place is a copy, its access and `⊥` written where defined at every typed future. -/
theorem dropAt_corr (φ : Future) (hs₀ : FrameStart s₀ ks) (q : Place) {pos : Pos} (hp : pos.frameOf = s₀.topIdx)
    (steps : List Step) {t t' : SState} (h : AccInv K σ s₀ ks t t') :
    AccInv K σ s₀ ks (dropAt K φ q pos steps t) (dropAt K φ q (upPos ks.length pos) steps t') ∧
      (DropOk K φ q pos steps t ↔ DropOk K φ q (upPos ks.length pos) steps t') := by
  have hsh := h.rel.topShape pos hp
  have hsc := scopeOf_corr h.rel
  obtain ⟨hacc, hok⟩ := frameRel_access φ hs₀ h hp (dataHit steps)
  have hc := typedAll_corr K φ hacc.rel hacc.shape hacc.held hacc.loc hp
    (fun x => (Sem.updAt K.dm K.Γ ((t.access pos (dataHit steps)).tyAt pos) (fun _ => .moved) steps x).isSome = true)
  have eT := updAt_T K.dm K.Γ (fun _ => Sem.moved) steps ((t'.access (upPos ks.length pos) (dataHit steps)).tyAt
    (upPos ks.length pos)) ((t.access pos (dataHit steps)).tyAt pos)
  -- the write branch: unless a copy, the access and `⊥` written where defined at every typed future
  have hw : ∀ (G G' : Prop) [Decidable G] [Decidable G'], (G ↔ G') →
      AccInv K σ s₀ ks (if G then t else if (∀ ψ, TypedFut K φ (t.access pos (dataHit steps)) ψ →
          (Sem.updAt K.dm K.Γ ((t.access pos (dataHit steps)).tyAt pos) (fun _ => .moved) steps
            ((t.access pos (dataHit steps)).valAt pos ψ)).isSome = true) then
          (t.access pos (dataHit steps)).setAt pos fun φ' => (Sem.updAt K.dm K.Γ ((t.access pos (dataHit steps)).tyAt pos)
            (fun _ => .moved) steps ((t.access pos (dataHit steps)).valAt pos φ')).getD .err else t)
        (if G' then t' else if (∀ ψ, TypedFut K φ (t'.access (upPos ks.length pos) (dataHit steps)) ψ →
          (Sem.updAt K.dm K.Γ ((t'.access (upPos ks.length pos) (dataHit steps)).tyAt (upPos ks.length pos))
            (fun _ => .moved) steps ((t'.access (upPos ks.length pos) (dataHit steps)).valAt (upPos ks.length pos) ψ)).isSome
              = true) then
          (t'.access (upPos ks.length pos) (dataHit steps)).setAt (upPos ks.length pos) fun φ' =>
            (Sem.updAt K.dm K.Γ ((t'.access (upPos ks.length pos) (dataHit steps)).tyAt (upPos ks.length pos))
              (fun _ => .moved) steps ((t'.access (upPos ks.length pos) (dataHit steps)).valAt (upPos ks.length pos) φ')).getD
              .err else t') := by
    intro G G' _ _ hG
    rw [eT]
    by_cases hg : G
    · rw [if_pos hg, if_pos (hG.1 hg)]; exact h
    · rw [if_neg hg, if_neg (fun h' => hg (hG.2 h'))]
      split
      · rename_i hd
        rw [if_pos (hc.1 hd)]
        exact accInv_setAt_fn hacc hp fun x =>
          (Sem.updAt K.dm K.Γ ((t.access pos (dataHit steps)).tyAt pos) (fun _ => .moved) steps x).getD .err
      · rename_i hd
        rw [if_neg (fun h' => hd (hc.2 h'))]; exact h
  have hwok : ((K.D.copy (K.D.placeDecl (scopeOf t) q) = false →
        (∀ ψ, TypedFut K φ (t.access pos (dataHit steps)) ψ →
          (Sem.updAt K.dm K.Γ ((t.access pos (dataHit steps)).tyAt pos) (fun _ => .moved) steps
            ((t.access pos (dataHit steps)).valAt pos ψ)).isSome) →
        AccessOk K φ t pos (dataHit steps)) ↔
       (K.D.copy (K.D.placeDecl (scopeOf t') q) = false →
        (∀ ψ, TypedFut K φ (t'.access (upPos ks.length pos) (dataHit steps)) ψ →
          (Sem.updAt K.dm K.Γ ((t'.access (upPos ks.length pos) (dataHit steps)).tyAt (upPos ks.length pos))
            (fun _ => .moved) steps ((t'.access (upPos ks.length pos) (dataHit steps)).valAt (upPos ks.length pos) ψ)).isSome) →
        AccessOk K φ t' (upPos ks.length pos) (dataHit steps))) := by
    rw [hsc, eT]; exact imp_congr_right fun _ => imp_congr hc hok
  unfold dropAt DropOk
  cases steps with
  | nil =>
    rw [hsh]
    cases e : t'.shape (upPos ks.length pos) with
    | none =>
      simp only [Option.map_none]
      exact ⟨hw _ _ (by rw [hsc]), hwok⟩
    | some l =>
      simp only [Option.map_some]
      have hl : t'.Live l := (SState.live_iff t' l).2 ⟨_, h.shape' _ _ e, e⟩
      exact ⟨h.endLabel hs₀ hl, endOk_corr K φ h.rel h.uniq h.shape h.held h.loc hl⟩
  | cons st sts => exact ⟨hw _ _ (by rw [hsc]), hwok⟩

end

/-! ## Operations that only clear holders and pass sites on

An end, an access, a write: every holder after is a holder before, every site after lies where some site lay before.
Two facts of the in-place state ride on it: every site in the callee's frame is at a binding (`FrameInv.bsites`), and
a result's label is held by a temporary (`ResAtTemp`). -/

/-- `u` comes from `t` by operations that only clear holders, rewrite values and move sites to positions where sites
were. -/
structure Shrinks (t u : SState) : Prop where
  shape : ∀ p l, u.shape p = some l → t.shape p = some l
  sites : ∀ m (y : Site), y ∈ u.lent m → ∃ (m' : Nat) (z : Site), z ∈ t.lent m' ∧ z.pos = y.pos
  positions : u.positions = t.positions
  next : u.nextLoan = t.nextLoan

theorem Shrinks.refl (t : SState) : Shrinks t t := ⟨fun _ _ h => h, fun m y hy => ⟨m, y, hy, rfl⟩, rfl, rfl⟩

theorem Shrinks.trans {t u v : SState} (h₁ : Shrinks t u) (h₂ : Shrinks u v) : Shrinks t v :=
  ⟨fun p l h => h₁.shape p l (h₂.shape p l h), fun m y hy => by
    obtain ⟨m', z, hz, e⟩ := h₂.sites m y hy
    obtain ⟨m'', w, hw, e'⟩ := h₁.sites m' z hz
    exact ⟨m'', w, hw, e'.trans e⟩, h₂.positions.trans h₁.positions, h₂.next.trans h₁.next⟩

theorem shrinks_foldl {α : Type} (f : SState → α → SState) (h : ∀ t x, Shrinks t (f t x)) :
    ∀ (xs : List α) (t : SState), Shrinks t (xs.foldl f t)
  | [], t => Shrinks.refl t
  | x :: xs, t => (h t x).trans (shrinks_foldl f h xs (f t x))

theorem shrinks_endLabel (t : SState) (l : Nat) : Shrinks t (t.endLabel l) := by
  cases hh : t.holderOf l with
  | none => rw [SState.endLabel_of_none hh]; exact Shrinks.refl t
  | some r =>
    rw [SState.endLabel_eq hh]
    refine ⟨fun p k hp => ?_, fun m y hy => ?_, SState.endAt_positions t l r, ?_⟩
    · rw [SState.endAt_shape] at hp; dsimp only at hp
      split at hp
      · cases hp
      · exact hp
    · by_cases hml : m = l
      · subst hml; rw [endAt_lent, relend_eq, if_pos rfl] at hy; cases hy
      rw [endAt_lent, mem_relend hml] at hy
      rcases hy with ⟨hy, -⟩ | ⟨x₀, -, -, z, hz, rfl⟩
      · exact ⟨m, y, hy, rfl⟩
      · exact ⟨l, z, hz, (relendSite_pos _ _).symm⟩
    · rw [← SState.endLabel_eq hh]; exact nextLoan_endLabel t l

theorem shrinks_access (t : SState) (p : Pos) (hit : List Step → Bool) : Shrinks t (t.access p hit) := by
  unfold SState.access
  exact shrinks_foldl _ (fun u _ => shrinks_foldl SState.endLabel shrinks_endLabel _ u) _ t

theorem shrinks_setAt (t : SState) (p : Pos) (v : SVal) : Shrinks t (t.setAt p v) :=
  ⟨fun q l h => by rwa [SState.shape_setAt] at h, fun m y hy => ⟨m, y, by rwa [setAt_lent] at hy, rfl⟩,
    SState.positions_setAt t p v, SState.nextLoan_setAt' t p v⟩

theorem shrinks_setContent {K : RunCtx} {φ : Future} {pos : Pos} {steps : List Step} {v : Sem} {t u : SState}
    {x : PUnit} (h : setContent K φ pos steps v t = some (x, u)) : Shrinks t u := by
  unfold setContent at h; dsimp only at h
  split at h
  · cases h; exact shrinks_setAt _ _ _
  · cases h

section
variable (K : RunCtx) (φ : Future)

theorem shrinks_accessLentPrefix (pos : Pos) (steps : List Step) (t : SState) :
    Shrinks t (accessLentPrefix pos steps t) := by
  unfold accessLentPrefix; split
  · exact shrinks_access _ _ _
  · exact Shrinks.refl t

theorem shrinks_invalidateOne (t : SState) (q : Place) : Shrinks t (invalidateOne K φ t q) := by
  unfold invalidateOne; split
  · dsimp only; split
    · rename_i h; exact (shrinks_access _ _ _).trans (shrinks_setContent h)
    · exact shrinks_access _ _ _
  · exact Shrinks.refl t

theorem shrinks_invalidate (p : Place) (t : SState) : Shrinks t (invalidate K φ p t) :=
  shrinks_foldl _ (shrinks_invalidateOne K φ) _ t

theorem shrinks_entryAccess (bc : List Place × List (Place × Nat)) (t : SState) : Shrinks t (entryAccess K φ bc t) := by
  unfold entryAccess
  refine (shrinks_foldl entryReroot (fun u q => ?_) _ t).trans (shrinks_foldl (entryCap K φ) (fun u qk => ?_) _ _)
  · unfold entryReroot; split
    · exact shrinks_accessLentPrefix _ _ _
    · exact Shrinks.refl u
  · unfold entryCap; dsimp only
    have h1 : Shrinks u (match resolve u qk.1 with | some (pos, steps) => u.access pos (dataHit steps) | none => u) := by
      split
      · exact shrinks_access _ _ _
      · exact Shrinks.refl u
    split
    · exact h1.trans (shrinks_invalidate K φ _ _)
    · exact h1

theorem shrinks_dropAt (q : Place) (pos : Pos) (steps : List Step) (t : SState) : Shrinks t (dropAt K φ q pos steps t) := by
  unfold dropAt
  split
  · exact shrinks_endLabel _ _
  · dsimp only
    split
    · exact Shrinks.refl t
    · split
      · exact (shrinks_access _ _ _).trans (shrinks_setAt _ _ _)
      · exact Shrinks.refl t

theorem shrinks_joinDrop (entry : List Place) (mt : Term) (t : SState) : Shrinks t (joinDrop K φ entry mt t) := by
  unfold joinDrop
  refine shrinks_foldl _ (fun u q => ?_) _ t
  split
  · exact (shrinks_accessLentPrefix _ _ _).trans (shrinks_dropAt K φ _ _ _ _)
  · exact Shrinks.refl u

theorem shrinks_tagOf {p : Place} {tag : Sem → TyS → Sem} {t u : SState} {tg : Sem}
    (h : tagOf K φ p tag t = some (tg, u)) : Shrinks t u := by
  unfold tagOf at h
  split at h
  · cases h; exact shrinks_access _ _ _
  · cases h

end

/-- Every site in the callee's frame is at a binding (`FrameInv.bsites`). -/
def BSites (s₀ t : SState) : Prop := ∀ m (y : Site), y ∈ t.lent m → y.pos.frameOf = s₀.topIdx → ∃ i, y.pos = .bind s₀.topIdx i

theorem BSites.shrinks {s₀ t u : SState} (h : BSites s₀ t) (hs : Shrinks t u) : BSites s₀ u := fun m y hy hf => by
  obtain ⟨m', z, hz, e⟩ := hs.sites m y hy
  rw [← e] at hf ⊢; exact h m' z hz hf

theorem ResAtTemp.shrinks {s₀ t u : SState} {lab : Option Nat} (h : ResAtTemp s₀ t lab) (hu : t.Uniq)
    (hs : Shrinks t u) : ResAtTemp s₀ u lab := fun k hk hl => by
  obtain ⟨q, hq, hqs⟩ := (SState.live_iff u k).1 hl
  have hqt := hs.shape q k hqs
  obtain ⟨j, hj⟩ := h k hk ((SState.live_iff t k).2 ⟨q, by rw [← hs.positions]; exact hq, hqt⟩)
  refine ⟨j, ?_⟩
  rw [hu _ _ _ hqt hj] at hqs; exact hqs

/-! ## A label lent at more places: [Entry]'s lending, a call's -/

section
variable {K : RunCtx} {σ : Nat → Nat} {s₀ : SState} {ks : List Nat} {t t' : SState}

/-- **A label lent at more places keeps the internal relation for [Access]** (the paper's row "A match", [Entry]'s
lending; (F8) kept): the label `σ l` gets new sites `ys` in place, `l` the corresponding `ys'` in the closure (the same
places of the callee's frame, through `upPos`; in the closure besides only the callee's frame and the cells), the label
is not a caller's, a parameter label is lent in the callee's frame only as a fill, and nothing is lent at the label's
holder nor is it lent there now (so lending stays well founded: the label is ranked below all). -/
theorem accInv_setLent (h : AccInv K σ s₀ ks t t') (l : Nat) (ys ys' : List Site)
    (hys : ∀ x : Site, x.pos.frameOf = s₀.topIdx → (x ∈ ys ↔ upSite ks.length x ∈ ys'))
    (hys' : ∀ x ∈ ys', (∃ p, p.frameOf = s₀.topIdx ∧ x.pos = upPos ks.length p) ∨ ∃ i, i < ks.length ∧ x.pos = .bind 0 i)
    (hcall : ∀ p, p.frameOf < s₀.topIdx → s₀.shape p ≠ some (σ l))
    (hfill : σ l ∈ ks → ∀ y ∈ ys, y.pos.frameOf = s₀.topIdx → y.fill = true)
    (hin : t.Live (σ l) → ∀ a (y : Site), t.Live a → y ∈ t.lent a → t.shape y.pos ≠ some (σ l))
    (hnew : t.Live (σ l) → ∀ y ∈ ys, t.shape y.pos ≠ some (σ l)) :
    AccInv K σ s₀ ks (t.setLent (σ l) (t.lent (σ l) ++ ys)) (t'.setLent l (t'.lent l ++ ys')) := by
  have hr := h.rel
  refine { h with rel := { hr with lentTop := ?_, lentImg := ?_, lentCl := ?_, lentCaller := ?_ }, lend := ?_, pfill := ?_ }
  · intro m x hx hm
    simp only [SState.setLent]
    by_cases e : m = l
    · subst e
      simp only [if_true, ite_true, List.mem_append]
      exact or_congr (hr.lentTop m x hx hm) (hys x hx)
    · have e' : σ m ≠ σ l := fun h' => e (hr.inj _ _ h')
      simp only [if_neg e, if_neg e']
      exact hr.lentTop m x hx hm
  · intro m x hx hm hxm
    simp only [SState.setLent] at hxm
    by_cases e : m = σ l
    · exact ⟨l, e⟩
    · rw [if_neg e] at hxm; exact hr.lentImg m x hx hm hxm
  · intro m x hxm
    simp only [SState.setLent] at hxm
    by_cases e : m = l
    · subst e; rw [if_pos rfl, List.mem_append] at hxm
      rcases hxm with hxm | hxm
      · exact hr.lentCl m x hxm
      · exact hys' x hxm
    · rw [if_neg e] at hxm; exact hr.lentCl m x hxm
  · intro m p hp hs
    simp only [SState.setLent]
    have : m ≠ σ l := fun e => hcall p hp (e ▸ hs)
    rw [if_neg this]; exact hr.lentCaller m p hp hs
  · obtain ⟨rk, hrk⟩ := h.lend
    by_cases hk : t.Live (σ l)
    · refine ⟨fun a => if a = σ l then 0 else rk a + 1, fun a b y ha hy hb => ?_⟩
      simp only [SState.setLent] at hy
      have hb' : b ≠ σ l := by
        rintro rfl
        by_cases e : a = σ l
        · subst e; rw [if_pos rfl, List.mem_append] at hy
          rcases hy with hy | hy
          · exact hin hk _ y hk hy hb
          · exact hnew hk y hy hb
        · rw [if_neg e] at hy; exact hin hk a y ha hy hb
      simp only [if_neg hb']
      by_cases e : a = σ l
      · simp only [if_pos e]; omega
      · simp only [if_neg e]; rw [if_neg e] at hy; have := hrk a b y ha hy hb; omega
    · refine ⟨rk, fun a b y ha hy hb => ?_⟩
      simp only [SState.setLent] at hy
      by_cases e : a = σ l
      · exact absurd (e ▸ ha) hk
      · rw [if_neg e] at hy; exact hrk a b y ha hy hb
  · intro k hk y hy hyf
    simp only [SState.setLent] at hy
    by_cases e : k = σ l
    · subst e; rw [if_pos rfl, List.mem_append] at hy
      rcases hy with hy | hy
      · exact h.pfill _ hk y hy hyf
      · exact hfill hk y hy hyf
    · rw [if_neg e] at hy; exact h.pfill k hk y hy hyf

end

/-! ## The tag of a match -/

section
variable {K : RunCtx} {σ : Nat → Nat} {s₀ : SState} {ks : List Nat} {s s' : SState}

/-- **A match's tag across the internal relation** (the paper's row "A match": the tag, (O4) with `tagHit`, then (O2)):
the same tag, related states after the access, the strict tests the same. For a tag that reads the value only
(`natTag`, `indTag`), not the type the path reaches. -/
theorem tagOf_corr (φ : Future) (hs₀ : FrameStart s₀ ks) (h : AccInv K σ s₀ ks s s') (p : Place)
    (tag : Sem → TyS → Sem) (htag : ∀ v T T', tag v T = tag v T') :
    OAgree (AccInv K σ s₀ ks) (tagOf K φ p tag s) (tagOf K φ p tag s') ∧ (TagOk K φ p s ↔ TagOk K φ p s') := by
  obtain ⟨hres, hframe⟩ := resolve_corr h.rel p
  cases hrp : resolve s p with
  | none =>
    have hrp' : resolve s' p = none := by rw [hres, hrp]; rfl
    unfold tagOf TagOk; rw [hrp, hrp']; exact ⟨trivial, Iff.rfl⟩
  | some x =>
    obtain ⟨pos, steps⟩ := x
    have hpos := hframe pos steps hrp
    have hrp' : resolve s' p = some (upPos ks.length pos, steps) := by rw [hres, hrp]; rfl
    obtain ⟨hacc, hok⟩ := frameRel_access φ hs₀ h hpos (tagHit steps)
    refine ⟨?_, by unfold TagOk; rw [hrp, hrp']; exact hok⟩
    unfold tagOf; rw [hrp, hrp']; dsimp only
    refine ⟨?_, hacc⟩
    rw [read_corr φ hacc hpos]
    generalize (s'.access (upPos ks.length pos) (tagHit steps)).valAt (upPos ks.length pos)
      ((s'.access (upPos ks.length pos) (tagHit steps)).typedFuture φ) = v
    have hf := follow_m K.dm K.Γ steps (s.tyAt pos) (s'.tyAt (upPos ks.length pos)) v (by rw [tyAt_corr h.rel hpos])
    unfold obsAt
    cases e1 : Sem.follow K.dm K.Γ (s.tyAt pos) v steps with
    | none =>
      rw [e1] at hf
      cases e2 : Sem.follow K.dm K.Γ (s'.tyAt (upPos ks.length pos)) v steps with
      | none => rfl
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
        obtain ⟨rfl, -⟩ := hf
        exact htag _ _ _

end

/-! ## The steps of a match against the frame property's internal relation -/

section
variable {K : RunCtx} {φ : Future} {σ : Nat → Nat} {s₀ : SState} {ks : List Nat}

/-- The internal relation after operations that keep `AccInv`, keep both states good, and in place only clear holders
and pass sites on (`Shrinks`: the counter, the bindings' sites). -/
theorem FrameInv.of_ops {s s' t t' : SState} (h : FrameInv K φ σ s₀ ks s s') (hacc : AccInv K σ s₀ ks t t')
    (hg : Strict.SGood K.dm K.Γ φ t) (hg' : Strict.SGood K.dm K.Γ φ t') (hsh : Shrinks s t) :
    FrameInv K φ σ s₀ ks t t' :=
  { acc := hacc, good := hg, good' := hg', counter := hsh.next ▸ h.counter, srange := h.srange,
    bsites := BSites.shrinks (s₀ := s₀) h.bsites hsh }

/-- **The tag step of a match** (its strict test, its access) keeps the internal relation. -/
theorem tag_frameInv (hs₀ : FrameStart s₀ ks) {s s' : SState} (h : FrameInv K φ σ s₀ ks s s') (p : Place)
    (tag : Sem → TyS → Sem) (htag : ∀ v T T', tag v T = tag v T') :
    OAgree (FrameInv K φ σ s₀ ks) (SM.guarded (TagOk K φ p) (tagOf K φ p tag) s)
      (SM.guarded (TagOk K φ p) (tagOf K φ p tag) s') := by
  obtain ⟨hc, hok⟩ := tagOf_corr φ hs₀ h.acc p tag htag
  unfold SM.guarded
  by_cases ht : TagOk K φ p s
  · have ht' := hok.1 ht
    rw [if_pos ht, if_pos ht']
    cases e1 : tagOf K φ p tag s with
    | none =>
      rw [e1] at hc
      cases e2 : tagOf K φ p tag s' with
      | none => trivial
      | some _ => rw [e2] at hc; exact hc.elim
    | some y =>
      rw [e1] at hc
      cases e2 : tagOf K φ p tag s' with
      | none => rw [e2] at hc; exact hc.elim
      | some y' =>
        rw [e2] at hc
        obtain ⟨tg, t⟩ := y
        obtain ⟨tg', t'⟩ := y'
        obtain ⟨rfl, hacc⟩ := hc
        exact ⟨rfl, h.of_ops hacc (Strict.sgood_tagOf h.good ht e1) (Strict.sgood_tagOf h.good' ht' e2)
          (shrinks_tagOf K φ e1)⟩
  · rw [if_neg ht, if_neg (fun h' => ht (hok.2 h'))]; trivial

/-- **[Entry] of a match** (`matchEntry`'s state, its strict test): related states after, the same test, and the same
places moved at the start (what the join drops is read from them). -/
theorem entry_frameInv (hs₀ : FrameStart s₀ ks) {s s' : SState} (h : FrameInv K φ σ s₀ ks s s') (ent : Bool)
    (mt : Term) :
    (MatchEntryOk K φ ent mt s ↔ MatchEntryOk K φ ent mt s') ∧
      (MatchEntryOk K φ ent mt s → FrameInv K φ σ s₀ ks (matchEntry K φ ent mt s).1 (matchEntry K φ ent mt s').1) := by
  have hbc : K.D.blockCaps (scopeOf s) (movedPlaces φ s) mt = K.D.blockCaps (scopeOf s') (movedPlaces φ s') mt := by
    rw [scopeOf_corr h.acc.rel, movedPlaces_corr φ h.acc.rel h.acc.shape h.acc.loc]
  generalize hb : K.D.blockCaps (scopeOf s') (movedPlaces φ s') mt = bc at hbc
  have e1 : ∀ e, MatchEntryOk K φ e mt s ↔ (e = true → EntryAccessOk K φ bc s) := fun e => by
    unfold MatchEntryOk; rw [hbc]
  have e1' : ∀ e, MatchEntryOk K φ e mt s' ↔ (e = true → EntryAccessOk K φ bc s') := fun e => by
    unfold MatchEntryOk; rw [hb]
  have e2 : (matchEntry K φ true mt s).1 = entryAccess K φ bc s := by unfold matchEntry; rw [hbc]; rfl
  have e2' : (matchEntry K φ true mt s').1 = entryAccess K φ bc s' := by unfold matchEntry; rw [hb]; rfl
  obtain ⟨hacc, hok⟩ := entryAccess_corr φ hs₀ bc h.acc
  refine ⟨by rw [e1, e1']; exact imp_congr_right fun _ => hok, fun hme => ?_⟩
  cases ent with
  | false => exact h
  | true =>
    have hme' := (e1 true).1 hme rfl
    have g1 := Strict.sgood_matchEntry (K := K) (φ := φ) h.good true mt hme
    have g2 := Strict.sgood_matchEntry (K := K) (φ := φ) h.good' true mt ((e1' true).2 fun _ => hok.1 hme')
    rw [e2] at g1 ⊢; rw [e2'] at g2 ⊢
    exact h.of_ops hacc g1 g2 (shrinks_entryAccess K φ _ _)

end

/-! ## The join's drop and [Entry]'s lending -/

section
variable {K : RunCtx} {φ : Future} {σ : Nat → Nat} {s₀ : SState} {ks : List Nat} {t t' : SState}

/-- **The join's drop across the internal relation** (the paper's row "A match": the end of a holder at a root (O3), or
an access and a write (O4), (O5)), each step after its lent prefix's access. -/
theorem joinDrop_corr (hs₀ : FrameStart s₀ ks) (entry : List Place) (mt : Term) {t t' : SState}
    (h : AccInv K σ s₀ ks t t') :
    AccInv K σ s₀ ks (joinDrop K φ entry mt t) (joinDrop K φ entry mt t') ∧
      (JoinDropOk K φ entry mt t ↔ JoinDropOk K φ entry mt t') := by
  unfold joinDrop JoinDropOk
  rw [scopeOf_corr h.rel]
  refine foldOk_corr (R := AccInv K σ s₀ ks) _ (JoinStepOk K φ) (fun u u' q hR => ?_) _ _ _ h
  obtain ⟨hres, hframe⟩ := resolve_corr hR.rel q
  unfold JoinStepOk
  rw [hres]
  cases hrq : resolve u q with
  | none => exact ⟨hR, Iff.rfl⟩
  | some x =>
    obtain ⟨pos, steps⟩ := x
    have hp := hframe pos steps hrq
    dsimp only [Option.map_some]
    obtain ⟨hA, hAok⟩ := accessLentPrefix_corr φ hs₀ hR hp steps
    obtain ⟨hD, hDok⟩ := dropAt_corr φ hs₀ q hp steps hA
    exact ⟨hD, and_congr hAok hDok⟩

/-- The sites `entryLend` makes for the captures by `&`, read at a state. -/
def capSites (bc2 : List (Place × Nat)) (t : SState) : List Site :=
  bc2.filterMap fun qk => if qk.2 == 1 then (resolve t qk.1).map fun ps => ({ pos := ps.1, path := ps.2, fill := true } : Site)
    else none

theorem entryLend_eq (bc : List Place × List (Place × Nat)) (snap : List Site) (k : Nat) (t : SState) :
    entryLend bc snap (some k) t = t.setLent k (t.lent k ++ (capSites bc.2 t ++ snap)) := by
  unfold entryLend capSites; simp only [List.append_assoc]

theorem capSites_corr (h : FrameRel σ s₀ ks t t') (bc2 : List (Place × Nat)) :
    capSites bc2 t' = (capSites bc2 t).map (upSite ks.length) := by
  unfold capSites
  rw [List.map_filterMap]
  congr 1; funext qk
  cases hq : (qk.2 == 1)
  · rfl
  · simp only [if_true]
    rw [(resolve_corr h qk.1).1]
    cases resolve t qk.1 <;> rfl

theorem mem_capSites {bc2 : List (Place × Nat)} {t : SState} {x : Site} (hx : x ∈ capSites bc2 t) :
    x.fill = true ∧ ∃ q steps, resolve t q = some (x.pos, steps) := by
  unfold capSites at hx
  obtain ⟨qk, -, hqk⟩ := List.mem_filterMap.mp hx
  split at hqk
  · cases e : resolve t qk.1 with
    | none => rw [e] at hqk; cases hqk
    | some ps =>
      rw [e] at hqk
      simp only [Option.map_some, Option.some.injEq] at hqk
      subst hqk
      exact ⟨rfl, qk.1, ps.2, e⟩
  · cases hqk

/-- **The snapshot an entry takes** (the sites of the borrows a block takes by move, as fills) **corresponds**: in the
callee's frame, the same places; in the closure, besides, only the cells; all fills; in place, at bindings. -/
structure SnapRel (σ : Nat → Nat) (s₀ : SState) (ks : List Nat) (snap snap' : List Site) : Prop where
  top : ∀ x : Site, x.pos.frameOf = s₀.topIdx → (x ∈ snap ↔ upSite ks.length x ∈ snap')
  cl : ∀ x ∈ snap', (∃ p, p.frameOf = s₀.topIdx ∧ x.pos = upPos ks.length p) ∨ ∃ i, i < ks.length ∧ x.pos = .bind 0 i
  fill : ∀ x ∈ snap, x.fill = true
  bind : ∀ x ∈ snap, x.pos.frameOf = s₀.topIdx → ∃ i, x.pos = .bind s₀.topIdx i

theorem SnapRel.nil : SnapRel σ s₀ ks [] [] :=
  ⟨fun _ _ => (by simp), fun _ h => (by cases h), fun _ h => (by cases h), fun _ h => (by cases h)⟩

theorem SnapRel.append {a a' b b' : List Site} (ha : SnapRel σ s₀ ks a a') (hb : SnapRel σ s₀ ks b b') :
    SnapRel σ s₀ ks (a ++ b) (a' ++ b') :=
  ⟨fun x hx => by simp only [List.mem_append]; exact or_congr (ha.top x hx) (hb.top x hx),
   fun x hx => (List.mem_append.mp hx).elim (ha.cl x) (hb.cl x),
   fun x hx => (List.mem_append.mp hx).elim (ha.fill x) (hb.fill x),
   fun x hx => (List.mem_append.mp hx).elim (ha.bind x) (hb.bind x)⟩

/-- A held label's sites, as fills, correspond (`FrameRel.lentTop`, `lentCl`). -/
theorem snap_label (h : FrameRel σ s₀ ks t t') (hb : BSites s₀ t) {p : Pos} (hp : p.frameOf = s₀.topIdx) {j : Nat}
    (hj : t'.shape (upPos ks.length p) = some j) :
    SnapRel σ s₀ ks ((t.lent (σ j)).map fun x => { x with fill := true })
      ((t'.lent j).map fun x => { x with fill := true }) := by
  have hps : t.shape p = some (σ j) := by rw [h.topShape p hp, hj]; rfl
  refine ⟨fun x hx => ?_, fun x hx => ?_, fun x hx => ?_, fun x hx hxf => ?_⟩
  · simp only [List.mem_map]
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨upSite ks.length y, (h.lentTop j y hx ⟨p, hps⟩).mp hy, rfl⟩
    · rintro ⟨y', hy', e⟩
      rcases h.lentCl j y' hy' with ⟨q, hqf, hq⟩ | ⟨i, -, hi⟩
      · refine ⟨{ y' with pos := q }, (h.lentTop j _ hqf ⟨p, hps⟩).mpr ?_, ?_⟩
        · obtain ⟨yp, yπ, yf⟩ := y'; simp only at hq ⊢; rw [← hq]; exact hy'
        · obtain ⟨yp, yπ, yf⟩ := y'; obtain ⟨xp, xπ, xf⟩ := x
          simp only [upSite, Site.mk.injEq] at e hq ⊢
          obtain ⟨e1, rfl, rfl⟩ := e
          refine ⟨?_, rfl, rfl⟩
          rw [hq] at e1
          cases q <;> cases xp <;> simp_all [upPos, Pos.frameOf]
      · exfalso
        obtain ⟨xp, xπ, xf⟩ := x
        simp only [upSite, Site.mk.injEq] at e
        have := e.1; rw [hi] at this
        cases xp <;> simp [upPos] at this
  · obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
    exact h.lentCl j y hy
  · obtain ⟨y, -, rfl⟩ := List.mem_map.mp hx; rfl
  · obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
    exact hb _ y hy hxf

theorem entrySnapshot_rel (h : AccInv K σ s₀ ks t t') (hb : BSites s₀ t) (bc : List Place × List (Place × Nat)) :
    SnapRel σ s₀ ks (entrySnapshot bc t) (entrySnapshot bc t') := by
  unfold entrySnapshot
  induction bc.2 with
  | nil => exact SnapRel.nil
  | cons qk qks ih =>
    simp only [List.flatMap_cons]
    refine SnapRel.append ?_ ih
    cases hq : (qk.2 == 2)
    · exact SnapRel.nil
    · simp only [if_true]
      obtain ⟨hres, hframe⟩ := resolve_corr h.rel qk.1
      rw [hres]
      cases hrq : resolve t qk.1 with
      | none => exact SnapRel.nil
      | some x =>
        obtain ⟨pos, steps⟩ := x
        have hp := hframe pos steps hrq
        dsimp only [Option.map_some]
        cases steps with
        | cons _ _ => exact SnapRel.nil
        | nil =>
          dsimp only
          rw [h.rel.topShape pos hp]
          cases hj : t'.shape (upPos ks.length pos) with
          | none => exact SnapRel.nil
          | some j => exact snap_label h.rel hb hp hj

end

section
variable {K : RunCtx} {φ : Future} {σ : Nat → Nat} {s₀ : SState} {ks : List Nat}

theorem capSites_pos {bc2 : List (Place × Nat)} {t t' : SState} (h : FrameRel σ s₀ ks t t') {x : Site}
    (hx : x ∈ capSites bc2 t) : x.fill = true ∧ x.pos.frameOf = s₀.topIdx ∧ ∃ i, x.pos = .bind s₀.topIdx i := by
  obtain ⟨hf, q, steps, hq⟩ := mem_capSites hx
  have hfr := (resolve_corr h q).2 _ _ hq
  refine ⟨hf, hfr, ?_⟩
  have hb := resolve_bind hq
  cases e : x.pos with
  | bind f i => rw [e] at hfr; exact ⟨i, by simp only [Pos.frameOf] at hfr; rw [hfr]⟩
  | temp f i => rw [e] at hb; exact absurd trivial hb

/-- **[Entry]'s lending after the join keeps the internal relation** (the paper's row "A match": the result's label is
held in the callee's frame; its new sites are corresponding places of the callee's frame and the snapshot; (F8) kept;
`P2`'s case when the arm returns a borrow parameter, (I3)). Given the result's label parked (`ResAtTemp`): nothing is
lent at its holder, so lending it further keeps lending well founded. -/
theorem lend_frameInv (hs₀ : FrameStart s₀ ks) {t t' : SState} (h : FrameInv K φ σ s₀ ks t t')
    (bc : List Place × List (Place × Nat)) {snap snap' : List Site} (hsn : SnapRel σ s₀ ks snap snap')
    (lab' : Option Nat) (hres : ResAtTemp s₀ t (lab'.map σ)) :
    FrameInv K φ σ s₀ ks (entryLend bc snap (lab'.map σ) t) (entryLend bc snap' lab' t') ∧
      ResAtTemp s₀ (entryLend bc snap (lab'.map σ) t) (lab'.map σ) := by
  cases lab' with
  | none => exact ⟨h, hres⟩
  | some l =>
    simp only [Option.map_some] at hres ⊢
    rw [entryLend_eq, entryLend_eq, capSites_corr h.acc.rel bc.2]
    have hpark : t.Live (σ l) → ∀ q, t.shape q = some (σ l) → ∃ j, q = .temp s₀.topIdx j := fun hk q hq => by
      obtain ⟨j, hj⟩ := hres (σ l) rfl hk
      exact ⟨j, h.acc.uniq _ _ _ hq hj⟩
    have hnotb : t.Live (σ l) → ∀ (y : Site), t.shape y.pos = some (σ l) →
        y.pos.frameOf = s₀.topIdx ∧ ∀ i, y.pos ≠ .bind s₀.topIdx i := fun hk y hy => by
      obtain ⟨j, hj⟩ := hpark hk _ hy
      rw [hj]; exact ⟨rfl, fun i => by simp⟩
    have hacc := accInv_setLent h.acc l (capSites bc.2 t ++ snap) ((capSites bc.2 t).map (upSite ks.length) ++ snap')
      (fun x hx => by
        simp only [List.mem_append]
        refine or_congr ⟨fun hm => List.mem_map_of_mem hm, fun hm => ?_⟩ (hsn.top x hx)
        obtain ⟨y, hy, e⟩ := List.mem_map.mp hm
        have hyf := (capSites_pos h.acc.rel hy).2.1
        rwa [site_up_inj (hyf.trans hx.symm) e] at hy)
      (fun x hx => by
        rcases List.mem_append.mp hx with hx | hx
        · obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
          exact .inl ⟨y.pos, (capSites_pos h.acc.rel hy).2.1, rfl⟩
        · exact hsn.cl x hx)
      (fun p hp hs => by
        obtain ⟨hk, hlt⟩ := hs₀.callerHeld p (σ l) hp hs
        rcases h.srange l with e | e
        · exact hk e
        · omega)
      (fun _ y hy _ => by
        rcases List.mem_append.mp hy with hy | hy
        · exact (capSites_pos h.acc.rel hy).1
        · exact hsn.fill y hy)
      (fun hk a y _ hy hs => by
        obtain ⟨hf, hnb⟩ := hnotb hk y hs
        obtain ⟨i, hi⟩ := h.bsites a y hy hf
        exact hnb i hi)
      (fun hk y hy hs => by
        obtain ⟨hf, hnb⟩ := hnotb hk y hs
        rcases List.mem_append.mp hy with hy | hy
        · obtain ⟨-, -, i, hi⟩ := capSites_pos h.acc.rel hy; exact hnb i hi
        · obtain ⟨i, hi⟩ := hsn.bind y hy hf; exact hnb i hi)
    refine ⟨⟨hacc, Strict.sgood_setLent h.good _ _, Strict.sgood_setLent h.good' _ _, h.counter, h.srange,
      fun m y hy hf => ?_⟩, hres⟩
    simp only [SState.setLent] at hy
    split at hy
    · rcases List.mem_append.mp hy with hy | hy
      · exact h.bsites _ y hy hf
      · rcases List.mem_append.mp hy with hy | hy
        · exact (capSites_pos h.acc.rel hy).2.2
        · exact hsn.bind y hy hf
    · exact h.bsites m y hy hf

end

/-! ## The frame property clause by clause -/

/-- **The frame property at one term** (`RunFrameI` at `t`, for fixed context, assignment, future, renaming, call point
and parameter labels): the in-place run and the closure's run from related states agree. The clause lemmas below derive
it at a term from its subterms. -/
def TermFrame (K : RunCtx) (ρ : Assignment) (φ : Future) (σ : Nat → Nat) (s₀ : SState) (ks : List Nat) (t : Term) : Prop :=
  ∀ (tl : Bool) (hint : TyS) (s s' : SState), FrameInv K φ σ s₀ ks s s' →
    FrameAgreeI K φ σ s₀ ks (runT K ρ φ tl hint t s) (runT K ρ φ tl hint t s')

section
variable {K : RunCtx} {ρ : Assignment} {φ : Future} {σ : Nat → Nat} {s₀ : SState} {ks : List Nat}

/-- **An erased term** (C1): a proof runs on a copy and is `⋆` at the true proposition; a statement runs on a copy and
keeps no label; either way the state is the one it started from. -/
theorem agreeI_erasedIf (fl : Bool × Bool) {x x' : SM Res} {s s' : SState} (h : FrameInv K φ σ s₀ ks s s')
    (hx : FrameAgreeI K φ σ s₀ ks (x s) (x' s')) :
    FrameAgreeI K φ σ s₀ ks (SM.erasedIf fl x s) (SM.erasedIf fl x' s') := by
  obtain ⟨f1, f2⟩ := fl
  cases hxs : x s with
  | none =>
    rw [hxs] at hx
    cases hxs' : x' s' with
    | some _ => rw [hxs'] at hx; exact hx.elim
    | none => cases f2 <;> cases f1 <;> simp [SM.erasedIf, SM.stmtIf, hxs, hxs', FrameAgreeI]
  | some y =>
    rw [hxs] at hx
    cases hxs' : x' s' with
    | none => rw [hxs'] at hx; exact hx.elim
    | some y' =>
      rw [hxs'] at hx
      obtain ⟨⟨v, R⟩, t⟩ := y
      obtain ⟨⟨v', R'⟩, t'⟩ := y'
      obtain ⟨hv, hR, hI, hres⟩ := hx
      simp only at hv; subst hv
      cases f2 with
      | true =>
        simp only [SM.erasedIf, if_true, hxs, hxs']
        cases v <;> first | trivial | exact ⟨rfl, rfl, h, fun _ e => by cases e⟩
      | false =>
        cases f1 with
        | true =>
          simp only [SM.erasedIf, SM.stmtIf, if_true, Bool.false_eq_true, if_false, hxs, hxs', Option.map_some]
          exact ⟨rfl, by subst hR; rfl, h, fun _ e => by cases e⟩
        | false =>
          simp only [SM.erasedIf, SM.stmtIf, Bool.false_eq_true, if_false, hxs, hxs']
          exact ⟨rfl, hR, hI, hres⟩

/-- A match's arm, by index, from the frame property at each arm. -/
theorem runArm_agree : ∀ (arms : List (Hint × Term)), (∀ a ∈ arms, TermFrame K ρ φ σ s₀ ks a.2) →
    ∀ (c : Nat) (tl : Bool) (hint : TyS) (s s' : SState), FrameInv K φ σ s₀ ks s s' →
      FrameAgreeI K φ σ s₀ ks (runArm K ρ φ tl hint c arms s) (runArm K ρ φ tl hint c arms s')
  | [], _, _, _, _, _, _, _ => by simp [runArm, SM.fail, FrameAgreeI]
  | (n, a) :: rest, harms, c, tl, hint, s, s', h => by
    simp only [runArm]
    split
    · exact harms (n, a) (List.mem_cons_self ..) tl hint s s' h
    · exact runArm_agree rest (fun b hb => harms b (List.mem_cons_of_mem _ hb)) (c - 1) tl hint s s' h

end

section
variable {K : RunCtx} {ρ : Assignment} {φ : Future} {σ : Nat → Nat} {s₀ : SState} {ks : List Nat}

theorem optCheck_neg.{u} {P : Prop} (h : ¬ P) : optCheck.{u} P = none := by
  unfold optCheck; rw [if_neg h]

/-- A bind on two outcomes that agree (`OAgree`), into agreeing runs. -/
theorem oagree_bind {α : Type 3} {R : SState → SState → Prop} {o o' : Option (α × SState)} (h : OAgree R o o')
    {f f' : α × SState → Option (Res × SState)}
    (hf : ∀ a t t', R t t' → FrameAgreeI K φ σ s₀ ks (f (a, t)) (f' (a, t'))) :
    FrameAgreeI K φ σ s₀ ks (o >>= f) (o' >>= f') := by
  match o, o', h with
  | none, none, _ => trivial
  | some (a, t), some (a', t'), ⟨e, hR⟩ => subst e; exact hf a t t' hR

/-- A bind on two agreeing runs (`FrameAgreeI`), into agreeing runs. -/
theorem agreeI_bind {o o' : Option (Res × SState)} (h : FrameAgreeI K φ σ s₀ ks o o')
    {f f' : Res × SState → Option (Res × SState)}
    (hf : ∀ (v : Sem) (R R' : TyS) (t t' : SState), R = { R' with label := R'.label.map σ } →
      FrameInv K φ σ s₀ ks t t' → ResAtTemp s₀ t R.label → FrameAgreeI K φ σ s₀ ks (f ((v, R), t)) (f' ((v, R'), t'))) :
    FrameAgreeI K φ σ s₀ ks (o >>= f) (o' >>= f') := by
  match o, o', h with
  | none, none, _ => trivial
  | some ((v, R), t), some ((v', R'), t'), ⟨e, hR, hI, hres⟩ => simp only at e; subst e; exact hf v R R' t t' hR hI hres

/-- **The join and [Entry]'s lending after an arm** (the paper's row "A match", after the arm): from the internal relation
before the entry (`t`, `t'`: the entry's places and lending are read from it) and after the arm, the join's drop and the
lending keep the internal relation and the result's label parked. -/
theorem joinLend_frameInv (hs₀ : FrameStart s₀ ks) {t t' : SState} (h₀ : FrameInv K φ σ s₀ ks t t') (ent : Bool)
    (mt : Term) (hme : MatchEntryOk K φ ent mt t) (entry : List Place) {u u' : SState} (h : FrameInv K φ σ s₀ ks u u')
    (lab' : Option Nat) (hres : ResAtTemp s₀ u (lab'.map σ)) (hj : JoinDropOk K φ entry mt u) :
    FrameInv K φ σ s₀ ks ((matchEntry K φ ent mt t).2 (lab'.map σ) (joinDrop K φ entry mt u))
        ((matchEntry K φ ent mt t').2 lab' (joinDrop K φ entry mt u')) ∧
      ResAtTemp s₀ ((matchEntry K φ ent mt t).2 (lab'.map σ) (joinDrop K φ entry mt u)) (lab'.map σ) := by
  obtain ⟨hjacc, hjok⟩ := joinDrop_corr (φ := φ) hs₀ entry mt h.acc
  have hsh := shrinks_joinDrop K φ entry mt u
  have hJ : FrameInv K φ σ s₀ ks (joinDrop K φ entry mt u) (joinDrop K φ entry mt u') :=
    h.of_ops hjacc (Strict.sgood_joinDrop h.good entry mt hj) (Strict.sgood_joinDrop h.good' entry mt (hjok.1 hj)) hsh
  have hresJ : ResAtTemp s₀ (joinDrop K φ entry mt u) (lab'.map σ) := hres.shrinks h.acc.uniq hsh
  have hbc : K.D.blockCaps (scopeOf t) (movedPlaces φ t) mt = K.D.blockCaps (scopeOf t') (movedPlaces φ t') mt := by
    rw [scopeOf_corr h₀.acc.rel, movedPlaces_corr φ h₀.acc.rel h₀.acc.shape h₀.acc.loc]
  cases ent with
  | false => exact ⟨hJ, hresJ⟩
  | true =>
    have hE := (entry_frameInv hs₀ h₀ true mt).2 hme
    unfold matchEntry at hE ⊢
    simp only [if_true] at hE ⊢
    rw [← hbc] at hE ⊢
    generalize K.D.blockCaps (scopeOf t) (movedPlaces φ t) mt = bc at hE ⊢
    rw [← scopeOf_corr hE.acc.rel]
    split
    · exact lend_frameInv hs₀ hJ bc (entrySnapshot_rel hE.acc hE.bsites bc) lab' hresJ
    · exact ⟨hJ, hresJ⟩

end

/-! ## The clause: a match on a number -/

section
variable {K : RunCtx} {ρ : Assignment} {φ : Future} {σ : Nat → Nat} {s₀ : SState} {ks : List Nat}

/-- **An arm of a match, then the join's drop and [Entry]'s lending** (the part of the match clause after the entry):
from the internal relation before the entry, the arm's frame property gives the whole tail. -/
theorem matchArm_agree (hs₀ : FrameStart s₀ ks) {t t' : SState} (ht : FrameInv K φ σ s₀ ks t t') (ent : Bool)
    (mt : Term) (hme : MatchEntryOk K φ ent mt t) {w : Term} (ihw : TermFrame K ρ φ σ s₀ ks w) (tl : Bool) (hint : TyS) :
    FrameAgreeI K φ σ s₀ ks
      (runT K ρ φ tl hint w (matchEntry K φ ent mt t).1 >>= fun x =>
        optCheck (JoinDropOk K φ (movedPlaces φ (matchEntry K φ ent mt t').1) mt x.2) >>= fun _ =>
          some ((x.1.1, x.1.2), (matchEntry K φ ent mt t).2 x.1.2.label
            (joinDrop K φ (movedPlaces φ (matchEntry K φ ent mt t').1) mt x.2)))
      (runT K ρ φ tl hint w (matchEntry K φ ent mt t').1 >>= fun x =>
        optCheck (JoinDropOk K φ (movedPlaces φ (matchEntry K φ ent mt t').1) mt x.2) >>= fun _ =>
          some ((x.1.1, x.1.2), (matchEntry K φ ent mt t').2 x.1.2.label
            (joinDrop K φ (movedPlaces φ (matchEntry K φ ent mt t').1) mt x.2))) := by
  refine agreeI_bind (ihw tl hint _ _ ((entry_frameInv hs₀ ht ent mt).2 hme)) fun v R R' a a' hR ha hres => ?_
  dsimp only
  have hlab : R.label = R'.label.map σ := by rw [hR]
  obtain ⟨-, hjok⟩ := joinDrop_corr (φ := φ) hs₀ (movedPlaces φ (matchEntry K φ ent mt t').1) mt ha.acc
  by_cases hj : JoinDropOk K φ (movedPlaces φ (matchEntry K φ ent mt t').1) mt a
  · rw [optCheck_of hj, optCheck_of (hjok.1 hj)]
    rw [hlab] at hres ⊢
    obtain ⟨hF, hres'⟩ := joinLend_frameInv hs₀ ht ent mt hme _ ha R'.label hres hj
    exact ⟨rfl, hR, hF, by show ResAtTemp s₀ _ R.label; rw [hlab]; exact hres'⟩
  · rw [optCheck_neg hj, optCheck_neg (fun h => hj (hjok.2 h))]; trivial

/-- **The frame property's clause for a match on a number** (the paper's row "A match", `<sec-frame-proof>`): the tag
(`tag_frameInv`), [Entry]'s accesses and invalidation (`entry_frameInv`), the arm (the induction: `ihz`, `ihu`), the join's
drop and [Entry]'s lending (`matchArm_agree`, `joinLend_frameInv`). -/
theorem runFrameI_matchNat (hs₀ : FrameStart s₀ ks) {p : Place} {z u : Term}
    (ihz : TermFrame K ρ φ σ s₀ ks z) (ihu : TermFrame K ρ φ σ s₀ ks u) :
    TermFrame K ρ φ σ s₀ ks (.matchNat p z u) := by
  intro tl hint s s' hI
  rw [runT]; dsimp only
  rw [scopeOf_corr hI.acc.rel]
  refine agreeI_erasedIf _ hI ?_
  refine oagree_bind (tag_frameInv hs₀ hI p natTag (fun _ _ _ => rfl)) fun tg t t' ht => ?_
  dsimp only
  obtain ⟨hmeI, hmeF⟩ := entry_frameInv hs₀ ht (!tl) (.matchNat p z u)
  by_cases hme : MatchEntryOk K φ (!tl) (.matchNat p z u) t
  · have hE := hmeF hme
    rw [optCheck_of hme, optCheck_of (hmeI.1 hme), movedPlaces_corr φ hE.acc.rel hE.acc.shape hE.acc.loc]
    rcases tg.asNat with _ | _ | n
    · trivial
    · exact matchArm_agree hs₀ ht _ _ hme ihz _ _
    · exact matchArm_agree hs₀ ht _ _ hme ihu _ _
  · rw [optCheck_neg hme, optCheck_neg (fun h => hme (hmeI.2 h))]; trivial

/-- An erased match on a proof with other than one arm (`SM.anyArm`): the arms on copies, the first that runs to a
proof chosen alike on both sides (a run to a proof is read off the value, which agrees). -/
theorem anyArm_agree {n : Nat} {f f' : Nat → SM Res} {s s' : SState} (h : FrameInv K φ σ s₀ ks s s')
    (hf : ∀ c, FrameAgreeI K φ σ s₀ ks (f c s) (f' c s')) :
    FrameAgreeI K φ σ s₀ ks (SM.anyArm n f s) (SM.anyArm n f' s') := by
  have hp : ∀ c, SM.ranProof (f c s) = SM.ranProof (f' c s') := fun c => by
    have := hf c
    revert this
    cases f c s with
    | none => cases f' c s' with
      | none => intro; rfl
      | some _ => intro h; exact h.elim
    | some y => cases f' c s' with
      | none => intro h; exact h.elim
      | some y' =>
        obtain ⟨⟨v, R⟩, t⟩ := y; obtain ⟨⟨v', R'⟩, t'⟩ := y'
        rintro ⟨e, -⟩; simp only at e; subst e; cases v <;> rfl
  unfold SM.anyArm
  simp only [hp]
  split
  · rename_i c _
    have := hf c
    revert this
    cases f c s with
    | none => cases f' c s' with
      | none => intro; trivial
      | some _ => intro h; exact h.elim
    | some y => cases f' c s' with
      | none => intro h; exact h.elim
      | some y' =>
        obtain ⟨⟨v, R⟩, t⟩ := y; obtain ⟨⟨v', R'⟩, t'⟩ := y'
        rintro ⟨e, hR, -, -⟩; simp only at e; subst e
        exact ⟨rfl, by subst hR; rfl, h, fun _ e => by cases e⟩
  · trivial

/-- **The arm of a match on an inductive, not on a proof**, then the join's drop and [Entry]'s lending, or, on a type with
one constructor (D93), neither. -/
theorem matchIndArm_agree (hs₀ : FrameStart s₀ ks) {t t' : SState} (ht : FrameInv K φ σ s₀ ks t t') (ent : Bool)
    (mt : Term) (hme : MatchEntryOk K φ ent mt t) {arms : List (Hint × Term)}
    (iharms : ∀ a ∈ arms, TermFrame K ρ φ σ s₀ ks a.2) (c : Nat) (tl : Bool) (hint : TyS) (one : Bool) :
    FrameAgreeI K φ σ s₀ ks
      (runArm K ρ φ tl hint c arms (matchEntry K φ ent mt t).1 >>= fun x =>
        optCheck (false = true ∨ one = true ∨ JoinDropOk K φ (movedPlaces φ (matchEntry K φ ent mt t').1) mt x.2) >>= fun _ =>
          some ((x.1.1, x.1.2), if one = true then x.2 else (matchEntry K φ ent mt t).2 x.1.2.label
            (joinDrop K φ (movedPlaces φ (matchEntry K φ ent mt t').1) mt x.2)))
      (runArm K ρ φ tl hint c arms (matchEntry K φ ent mt t').1 >>= fun x =>
        optCheck (false = true ∨ one = true ∨ JoinDropOk K φ (movedPlaces φ (matchEntry K φ ent mt t').1) mt x.2) >>= fun _ =>
          some ((x.1.1, x.1.2), if one = true then x.2 else (matchEntry K φ ent mt t').2 x.1.2.label
            (joinDrop K φ (movedPlaces φ (matchEntry K φ ent mt t').1) mt x.2))) := by
  refine agreeI_bind (runArm_agree arms iharms c tl hint _ _ ((entry_frameInv hs₀ ht ent mt).2 hme))
    fun v R R' a a' hR ha hres => ?_
  dsimp only
  cases one with
  | true =>
    rw [optCheck_of (Or.inr (Or.inl rfl)), optCheck_of (Or.inr (Or.inl rfl))]
    exact ⟨rfl, hR, ha, hres⟩
  | false =>
    have hlab : R.label = R'.label.map σ := by rw [hR]
    obtain ⟨-, hjok⟩ := joinDrop_corr (φ := φ) hs₀ (movedPlaces φ (matchEntry K φ ent mt t').1) mt ha.acc
    by_cases hj : JoinDropOk K φ (movedPlaces φ (matchEntry K φ ent mt t').1) mt a
    · rw [optCheck_of (Or.inr (Or.inr hj)), optCheck_of (Or.inr (Or.inr (hjok.1 hj)))]
      simp only [Bool.false_eq_true, if_false]
      rw [hlab] at hres ⊢
      obtain ⟨hF, hres'⟩ := joinLend_frameInv hs₀ ht ent mt hme _ ha R'.label hres hj
      exact ⟨rfl, hR, hF, by show ResAtTemp s₀ _ R.label; rw [hlab]; exact hres'⟩
    · have n1 : ¬ (false = true ∨ false = true ∨ JoinDropOk K φ (movedPlaces φ (matchEntry K φ ent mt t').1) mt a) := by
        simp [hj]
      have n2 : ¬ (false = true ∨ false = true ∨ JoinDropOk K φ (movedPlaces φ (matchEntry K φ ent mt t').1) mt a') := by
        simp only [Bool.false_eq_true, false_or]; exact fun h => hj (hjok.2 h)
      rw [optCheck_neg n1, optCheck_neg n2]; trivial

/-- **The one arm of a match on a proof** (no entry, no join: `Machine.evalMatchByType`). -/
theorem proofArm_agree {t t' : SState} (ht : FrameInv K φ σ s₀ ks t t') {arms : List (Hint × Term)}
    (iharms : ∀ a ∈ arms, TermFrame K ρ φ σ s₀ ks a.2) (c : Nat) (tl : Bool) (hint : TyS) (one : Bool)
    (J : SState → Prop) :
    FrameAgreeI K φ σ s₀ ks
      (runArm K ρ φ tl hint c arms t >>= fun x =>
        optCheck (true = true ∨ one = true ∨ J x.2) >>= fun _ => some ((x.1.1, x.1.2), x.2))
      (runArm K ρ φ tl hint c arms t' >>= fun x =>
        optCheck (true = true ∨ one = true ∨ J x.2) >>= fun _ => some ((x.1.1, x.1.2), x.2)) := by
  refine agreeI_bind (runArm_agree arms iharms c tl hint _ _ ht) fun v R R' a a' hR ha hres => ?_
  dsimp only
  rw [optCheck_of (Or.inl rfl), optCheck_of (Or.inl rfl)]
  exact ⟨rfl, hR, ha, hres⟩

/-- **The frame property's clause for a match on an inductive** (the paper's row "A match"): as for a number, the arm by
index (`runArm_agree`), no entry and no join on a proof or on a type with one constructor (D93), and an erased match on a
proof with other than one arm runs its arms on copies (`SM.anyArm`). -/
theorem runFrameI_matchInd (hs₀ : FrameStart s₀ ks) {p : Place} {n : String} {arms : List (Hint × Term)}
    (iharms : ∀ a ∈ arms, TermFrame K ρ φ σ s₀ ks a.2) :
    TermFrame K ρ φ σ s₀ ks (.matchInd p n arms) := by
  intro tl hint s s' hI
  rw [runT]; dsimp only
  rw [scopeOf_corr hI.acc.rel]
  refine agreeI_erasedIf _ hI ?_
  refine oagree_bind (tag_frameInv hs₀ hI p indTag (fun _ _ _ => rfl)) fun tg t t' ht => ?_
  dsimp only
  obtain ⟨hmeI, hmeF⟩ := entry_frameInv hs₀ ht (!tl && !tg.isProof && !oneCtor K.Γ n) (.matchInd p n arms)
  by_cases hme : MatchEntryOk K φ (!tl && !tg.isProof && !oneCtor K.Γ n) (.matchInd p n arms) t
  · have hE := hmeF hme
    rw [optCheck_of hme, optCheck_of (hmeI.1 hme), movedPlaces_corr φ hE.acc.rel hE.acc.shape hE.acc.loc]
    cases tg with
    | proof =>
      dsimp only [Sem.isProof]
      split
      · exact proofArm_agree hE iharms _ tl _ _ _
      · exact anyArm_agree hE fun c => runArm_agree arms iharms c tl _ _ _ hE
    | _ =>
      dsimp only [Sem.isProof]
      rcases Sem.asNat _ with _ | c
      · trivial
      · exact matchIndArm_agree hs₀ ht _ _ hme iharms c tl _ _
  · rw [optCheck_neg hme, optCheck_neg (fun h => hme (hmeI.2 h))]; trivial

end

end Ochr.Meaning.Steps.Form.FrameEnd
