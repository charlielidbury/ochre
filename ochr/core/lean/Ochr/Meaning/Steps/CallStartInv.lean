import Ochr.Meaning.Steps.CallInPlaceFrame

/-!
# The start of a call in place, its internal relation: `CallStartInvG` (lead39, 2026-11-28; docs/31 D240)

`CallStartInvG` (`CallInPlaceFrame`) is the half of the frame property's start condition that relates the two states a
call's body starts from: IN PLACE, the caller's state with the callee's frame pushed (`inStart`: `self`, then each
parameter holding its argument, a borrow parameter taking the argument's label from its holder in the caller's frames);
IN THE CLOSURE, the global's forming state under a fresh bottom frame with `self` and the parameters pushed (`clStart`:
a borrow parameter at a fresh label `i` with a cell in frame 0). This file proves it, clause by clause of `FrameInv`
(through `frameInv_of`), by the two folds' construction.

The two folds are characterised one step at a time (`inFold`, `clFold`), by induction on the number of parameters
pushed (`List.take`), and the clauses read off the characterisations.
-/

namespace Ochr.Meaning.Steps.Form.CallInPlace

open Ochr Ochr.Meaning Ochr.Meaning.Steps Ochr.Meaning.Steps.Form Ochr.Meaning.Steps.Form.FrameEnd

/-! ## The arguments' labels -/

/-- The arguments' meanings before parameter `j`. -/
def accOf (args : List Res) (j : Nat) : List Sem := (args.take j).map (·.1)

theorem accOf_succ {args : List Res} {j : Nat} {a : Res} (h : args[j]? = some a) :
    accOf args (j + 1) = accOf args j ++ [a.1] := by
  simp [accOf, List.take_add_one, h]

theorem argLabels_take_succ {args : List Res} {j : Nat} {a : Res} (h : args[j]? = some a) :
    argLabels (args.take (j + 1)) = argLabels (args.take j) ++ a.2.label.toList := by
  simp only [argLabels, List.take_add_one, h, Option.toList_some, List.filterMap_append, List.filterMap_cons,
    List.filterMap_nil]
  cases a.2.label <;> simp

/-- Two arguments carry distinct labels. -/
theorem argLabels_ne {args : List Res} (hnd : (argLabels args).Nodup) {i j : Nat} (hij : i < j) {a b : Res}
    (ha : args[i]? = some a) (hb : args[j]? = some b) {k : Nat} (hka : a.2.label = some k) (hkb : b.2.label = some k) :
    False := by
  have e : args = args.take j ++ args.drop j := (List.take_append_drop j args).symm
  have hnd' : (argLabels (args.take j) ++ argLabels (args.drop j)).Nodup := by
    unfold argLabels; rw [← List.filterMap_append, ← e]; exact hnd
  have h1 : k ∈ argLabels (args.take j) := by
    refine List.mem_filterMap.2 ⟨a, ?_, hka⟩
    exact List.mem_of_getElem? (i := i) (by rw [List.getElem?_take, if_pos hij]; exact ha)
  have h2 : k ∈ argLabels (args.drop j) := by
    refine List.mem_filterMap.2 ⟨b, ?_, hkb⟩
    exact List.mem_of_getElem? (i := 0) (by rw [List.getElem?_drop]; simpa using hb)
  exact (List.nodup_append.1 hnd').2.2 k h1 k h2 rfl

/-! ## The in-place fold -/

/-- **What the in-place push has done after `j` parameters** (`callFrame`'s fold): the top frame (index `E`) holds `self`
and the first `j` parameters, each at its binder's type with its argument's label, and no temporary; its holders are the
parameters' labels; the counter, the sites and the records are the call point's. -/
structure InTop (s : SState) (bs : List PBind) (args : List Res) (selfB : SBinding) (j : Nat) (t : SState) : Prop where
  len : t.env.length = s.env.length + 1
  top : ∃ F, t.env[s.env.length]? = some F ∧ F.temps = [] ∧ F.binds.length = j + 1 ∧ F.binds[0]? = some selfB ∧
    ∀ i a, i < j → args[i]? = some a → F.binds[i + 1]? = some (paramBind bs (accOf args i) a)
  shapeP : ∀ i a, i < j → args[i]? = some a → t.shape (.bind s.env.length (i + 1)) = a.2.label
  shape0 : t.shape (.bind s.env.length 0) = none
  shapeHi : ∀ i, j + 1 ≤ i → t.shape (.bind s.env.length i) = none
  shapeT : ∀ i, t.shape (.temp s.env.length i) = none
  next : t.nextLoan = s.nextLoan
  lent : t.lent = s.lent
  heldTy : t.heldTy = s.heldTy
  heldMem : t.heldMem = s.heldMem

/-- **A push of a binding on the top frame**, as `pushBindShaped` makes it: the top frame gains the binding, which holds its
label; the other top positions keep their holders; the counter, sites and records are unchanged; provided the label's old
holder (if any) is outside the top frame. -/
theorem pushBindShaped_top {t : SState} {E : Nat} {F : SFrame} (hlen : t.env.length = E + 1) (hF : t.env[E]? = some F)
    (b : SBinding) (hh : ∀ k r, b.ty.label = some k → t.holderOf k = some r → r.frameOf ≠ E)
    (hfree : t.shape (.bind E F.binds.length) = none) :
    (pushBindShaped t b).env.length = E + 1 ∧
    (pushBindShaped t b).env[E]? = some { F with binds := F.binds ++ [b] } ∧
    (pushBindShaped t b).shape (.bind E F.binds.length) = b.ty.label ∧
    (∀ q, q.frameOf = E → q ≠ .bind E F.binds.length → (pushBindShaped t b).shape q = t.shape q) ∧
    (pushBindShaped t b).nextLoan = t.nextLoan ∧ (pushBindShaped t b).lent = t.lent ∧
    (pushBindShaped t b).heldTy = t.heldTy ∧ (pushBindShaped t b).heldMem = t.heldMem := by
  -- the take of the label leaves the top frame and its holders alone
  have htake : ∀ k, b.ty.label = some k → (t.takeLabel k).env.length = E + 1 ∧ (t.takeLabel k).env[E]? = some F ∧
      (∀ q, q.frameOf = E → (t.takeLabel k).shape q = t.shape q) ∧ (t.takeLabel k).nextLoan = t.nextLoan ∧
      (t.takeLabel k).lent = t.lent ∧ (t.takeLabel k).heldTy = t.heldTy ∧ (t.takeLabel k).heldMem = t.heldMem := by
    intro k hk
    unfold SState.takeLabel
    cases hr : t.holderOf k with
    | none => exact ⟨hlen, hF, fun _ _ => rfl, rfl, rfl, rfl, rfl⟩
    | some r =>
      have hne := hh k r hk hr
      refine ⟨?_, ?_, fun q hq => ?_, by cases r <;> rfl, ?_, ?_, ?_⟩
      · cases r <;> simp [SState.setAt, hlen]
      · cases r with
        | bind f i =>
          simp only [SState.setAt, List.getElem?_modify, hF]
          simp only [Pos.frameOf] at hne; simp [hne]
        | temp f i =>
          simp only [SState.setAt, List.getElem?_modify, hF]
          simp only [Pos.frameOf] at hne; simp [hne]
      · show (if q = r then none else t.shape q) = t.shape q
        rw [if_neg (fun (e : q = r) => hne (e ▸ hq))]
      · cases r <;> rfl
      · cases r <;> rfl
      · cases r <;> rfl
  -- the push on a state whose top frame is `F` at index `E`
  have hpush : ∀ u : SState, u.env.length = E + 1 → u.env[E]? = some F →
      (u.pushBind b).env.length = E + 1 ∧ (u.pushBind b).env[E]? = some { F with binds := F.binds ++ [b] } ∧
      (u.pushBind b).topIdx = E ∧ (u.pushBind b).env.getLast? = some { F with binds := F.binds ++ [b] } := by
    intro u hl hu
    have ht : u.topIdx = E := by simp [SState.topIdx, hl]
    have h1 : (u.pushBind b).env.length = E + 1 := by simp [SState.pushBind, hl]
    have h2 : (u.pushBind b).env[E]? = some { F with binds := F.binds ++ [b] } := by
      simp only [SState.pushBind, ht, List.getElem?_modify, hu]; simp
    refine ⟨h1, h2, by simp [SState.topIdx, h1], ?_⟩
    rw [List.getLast?_eq_getElem?, h1]; exact h2
  unfold pushBindShaped
  cases hl : b.ty.label with
  | none =>
    obtain ⟨h1, h2, _, _⟩ := hpush t hlen hF
    dsimp only
    exact ⟨h1, h2, hfree, fun _ _ _ => rfl, rfl, rfl, rfl, rfl⟩
  | some k =>
    obtain ⟨t1, t2, t3, t4, t5, t6, t7⟩ := htake k hl
    obtain ⟨h1, h2, h3, h4⟩ := hpush (t.takeLabel k) t1 t2
    dsimp only
    rw [h4]; dsimp only
    refine ⟨h1, h2, ?_, fun q hq hne => ?_, t4, t5, t6, t7⟩
    · rw [h3]; simp
    · rw [h3, if_neg (by simpa using hne)]
      exact t3 q hq

/-- The fold's step keeps `InTop`. -/
theorem InTop.step {s : SState} {bs : List PBind} {args : List Res} {selfB : SBinding} {j : Nat} {t : SState}
    (h : InTop s bs args selfB j t) (hnd : (argLabels args).Nodup) {a : Res} (ha : args[j]? = some a) :
    InTop s bs args selfB (j + 1) (pushBindShaped t (paramBind bs (accOf args j) a)) := by
  obtain ⟨F, hF, hT, hL, h0, hP⟩ := h.top
  have hlab : (paramBind bs (accOf args j) a).ty.label = a.2.label := rfl
  have hh : ∀ k r, (paramBind bs (accOf args j) a).ty.label = some k → t.holderOf k = some r →
      r.frameOf ≠ s.env.length := by
    intro k r hk hr hrf
    rw [hlab] at hk
    have hsr := (SState.holderOf_spec hr).2
    cases r with
    | temp f i => simp only [Pos.frameOf] at hrf; subst hrf; rw [h.shapeT] at hsr; cases hsr
    | bind f i =>
      simp only [Pos.frameOf] at hrf; subst hrf
      cases i with
      | zero => rw [h.shape0] at hsr; cases hsr
      | succ i =>
        by_cases hi : i < j
        · obtain ⟨a', ha'⟩ : ∃ a', args[i]? = some a' := by
            cases e : args[i]? with
            | none => have := (List.getElem?_eq_none_iff.1 e); have := (List.getElem?_eq_some_iff.1 ha).1; omega
            | some a' => exact ⟨a', rfl⟩
          rw [h.shapeP i a' hi ha'] at hsr
          exact argLabels_ne hnd hi ha' ha hsr hk
        · rw [h.shapeHi (i + 1) (by omega)] at hsr; cases hsr
  have hfree : t.shape (.bind s.env.length F.binds.length) = none := h.shapeHi _ (by omega)
  obtain ⟨p1, p2, p3, p4, p5, p6, p7, p8⟩ := pushBindShaped_top h.len hF _ hh hfree
  have hne : ∀ i, i ≠ j + 1 → Pos.bind s.env.length i ≠ Pos.bind s.env.length F.binds.length := by
    intro i hi e; rw [hL] at e; injection e with _ e; exact hi e
  refine ⟨p1, ⟨_, p2, hT, by simp [hL], by rw [List.getElem?_append_left (by omega)]; exact h0, fun i a' hi ha' => ?_⟩,
    fun i a' hi ha' => ?_, ?_, fun i hi => ?_, fun i => ?_, by rw [p5, h.next], by rw [p6, h.lent],
    by rw [p7, h.heldTy], by rw [p8, h.heldMem]⟩
  · by_cases e : i = j
    · subst e; rw [ha] at ha'; cases ha'
      dsimp only; rw [← hL]; exact List.getElem?_concat_length
    · dsimp only; rw [List.getElem?_append_left (by omega)]; exact hP i a' (by omega) ha'
  · by_cases e : i = j
    · subst e; rw [ha] at ha'; cases ha'
      rw [show i + 1 = F.binds.length by omega, p3]; rfl
    · rw [p4 _ rfl (hne _ (by omega))]; exact h.shapeP i a' (by omega) ha'
  · rw [p4 _ rfl (hne _ (by omega))]; exact h.shape0
  · rw [p4 _ rfl (hne _ (by omega))]; exact h.shapeHi i (by omega)
  · rw [p4 _ rfl (by simp)]; exact h.shapeT i

/-- The first state of the fold: the frame pushed and `self` bound. -/
theorem InTop.start {s : SState} (bs : List PBind) (args : List Res) (selfB : SBinding)
    (hsa : ∀ p l, s.shape p = some l → p ∈ s.positions) :
    InTop s bs args selfB 0 (s.pushFrame.pushBind selfB) := by
  have hl : s.pushFrame.env.length = s.env.length + 1 := by simp [SState.pushFrame]
  have ht : s.pushFrame.topIdx = s.env.length := by simp only [SState.topIdx, hl]; omega
  have hshape : ∀ q, q.frameOf = s.env.length → (s.pushFrame.pushBind selfB).shape q = none := by
    intro q hq
    show s.shape q = none
    cases e : s.shape q with
    | none => rfl
    | some l => have := frameOf_lt_of_mem (hsa q l e); omega
  refine ⟨by simp [SState.pushBind, hl], ⟨⟨[selfB], []⟩, ?_, rfl, rfl, rfl, fun i _ hi => absurd hi (by omega)⟩,
    fun i _ hi => absurd hi (by omega), hshape _ rfl, fun i _ => hshape _ rfl, fun i => hshape _ rfl, rfl, rfl, rfl, rfl⟩
  have e : (s.pushFrame.pushBind selfB).env = (s.env ++ [({} : SFrame)]).modify s.env.length
      (fun fr => { fr with binds := fr.binds ++ [selfB] }) := by
    simp only [SState.pushBind, ht]; rfl
  rw [e, List.getElem?_modify]; simp

/-- **The in-place push, characterised**: after the first `j` parameters, `InTop`, and the earlier arguments' meanings. -/
theorem inFold {s : SState} (bs : List PBind) (args : List Res) (selfB : SBinding)
    (hsa : ∀ p l, s.shape p = some l → p ∈ s.positions) (hnd : (argLabels args).Nodup) :
    ∀ j, j ≤ args.length →
      ((args.take j).foldl (callStep bs) (s.pushFrame.pushBind selfB, [])).2 = accOf args j ∧
      InTop s bs args selfB j ((args.take j).foldl (callStep bs) (s.pushFrame.pushBind selfB, [])).1
  | 0, _ => ⟨rfl, InTop.start bs args selfB hsa⟩
  | j + 1, hj => by
    obtain ⟨a, ha⟩ : ∃ a, args[j]? = some a := ⟨args[j], List.getElem?_eq_getElem (by omega)⟩
    obtain ⟨ih1, ih2⟩ := inFold bs args selfB hsa hnd j (by omega)
    rw [List.take_add_one, ha, Option.toList_some, List.foldl_append, List.foldl_cons, List.foldl_nil]
    generalize ((args.take j).foldl (callStep bs) (s.pushFrame.pushBind selfB, [])) = r at ih1 ih2
    obtain ⟨t, acc⟩ := r
    dsimp only at ih1 ih2
    subst ih1
    exact ⟨(accOf_succ ha).symm, ih2.step hnd ha⟩

/-- `inStart` is the fold over every argument. -/
theorem inStart_fold (K : RunCtx) (ρ : Assignment) (φ : Future) (fres : Res) (ds : List Term) (c : Term)
    (args : List Res) (s : SState) :
    inStart K ρ φ fres ds c args s = ((args.take args.length).foldl (callStep (fbG K ρ φ ds c).1)
      (s.pushFrame.pushBind { ty := { fres.2 with label := none }, val := fun _ => fres.1, decl := .pi (fbG K ρ φ ds c).2.2 },
        [])).1 := by
  rw [List.take_length, inStart_eq]

/-! ## Goodness through the push -/

theorem tyAt_pushFrame (t : SState) : t.pushFrame.tyAt = t.tyAt := by
  funext p
  have e : t.pushFrame.env = t.env ++ [({} : SFrame)] := rfl
  cases p with
  | bind f i =>
    simp only [SState.tyAt, e]
    by_cases h : f < t.env.length
    · rw [List.getElem?_append_left h]
    · rw [List.getElem?_append_right (Nat.le_of_not_lt h), List.getElem?_eq_none (Nat.le_of_not_lt h)]
      cases f - t.env.length <;> simp
  | temp f i => rfl

theorem typedF_pushFrame {dm : DataModel} {Γ : List IndDecl} {φ : Future} {t : SState} {ψ : Future}
    (h : Strict.TypedF dm Γ φ t.pushFrame ψ) : Strict.TypedF dm Γ φ t ψ := by
  have e : ∀ l, l ∈ t.pushFrame.liveLabels ↔ l ∈ t.liveLabels := fun l => PushFrame.live_pushFrame t l
  have e' : t.pushFrame.heldTy = t.heldTy := rfl
  exact ⟨fun l hl => h.1 l (by rw [e]; exact hl), fun l hl => by have := h.2 l ((e l).2 hl); rwa [e'] at this⟩

/-- A pushed empty frame keeps goodness. -/
theorem sgood_pushFrame {dm : DataModel} {Γ : List IndDecl} {φ : Future} {t : SState} (h : Strict.SGood dm Γ φ t) :
    Strict.SGood dm Γ φ t.pushFrame := by
  have hv := PushFrame.valAt_pushFrame t
  have hty := tyAt_pushFrame t
  have hp := PushFrame.mem_positions_pushFrame t
  refine ⟨fun ψ hψ f i hfi => ?_, fun ψ hψ p l hpl => ?_, fun l hl => ?_, fun f i l hl => ?_, ?_, ?_, h.uniq⟩
  · rw [hv, hty]; exact h.bind ψ (typedF_pushFrame hψ) f i ((hp _).1 hfi)
  · rw [hv]; exact h.holder ψ (typedF_pushFrame hψ) p l hpl
  · exact h.held l ((PushFrame.live_pushFrame t l).1 hl)
  · rw [hty]; exact h.holderTy f i l hl
  · exact PushFrame.rinv_pushFrame h.acyc
  · intro q l hd
    obtain ⟨ψ, x, hne⟩ := hd
    exact h.fresh q l ⟨ψ, x, by simpa [SState.toMean, hv] using hne⟩

/-- **The in-place push keeps goodness**: `self` a member of its type; each argument a member of its binder's type at
the earlier arguments, its label (if any) live at the call point and recorded there at that type. -/
theorem inFold_good (K : RunCtx) (φ : Future) {s : SState} (bs : List PBind) (args : List Res) (selfB : SBinding)
    {v₀ : Sem} (hsv : selfB.val = fun _ => v₀) (hsl : selfB.ty.label = none) (hsg : Strict.GoodRes K.dm.read (v₀, selfB.ty))
    (hg : Strict.SGood K.dm K.Γ φ s) (hloc : SState.RInv (fun _ => False) s) (hnd : (argLabels args).Nodup)
    (hlive : ∀ a ∈ args, ∀ l, a.2.label = some l → s.Live l)
    (hmem : ∀ j a, args[j]? = some a → a.1 ∈ₛ[K.dm.read] (paramBind bs (accOf args j) a).ty.m)
    (hheld : ∀ j a k, args[j]? = some a → a.2.label = some k → s.heldTy k = (paramBind bs (accOf args j) a).ty.m) :
    ∀ j, j ≤ args.length →
      Strict.SGood K.dm K.Γ φ ((args.take j).foldl (callStep bs) (s.pushFrame.pushBind selfB, [])).1
  | 0, _ => by
    have e : pushBindShaped s.pushFrame selfB = s.pushFrame.pushBind selfB := by
      unfold pushBindShaped; rw [hsl]
    rw [List.take_zero, List.foldl_nil, ← e]
    exact Strict.sgood_pushBindShaped (sgood_pushFrame hg) selfB hsv hsg (fun l h => by rw [hsl] at h; cases h)
      (fun l h => by rw [hsl] at h; cases h) (by simp [SState.pushFrame])
  | j + 1, hj => by
    have hsa : ∀ p l, s.shape p = some l → p ∈ s.positions := fun p l h => (hloc.2.2 p l h).1
    obtain ⟨a, ha⟩ : ∃ a, args[j]? = some a := ⟨args[j], List.getElem?_eq_getElem (by omega)⟩
    have ih := inFold_good K φ bs args selfB hsv hsl hsg hg hloc hnd hlive hmem hheld j (by omega)
    obtain ⟨hacc, htop⟩ := inFold bs args selfB hsa hnd j (by omega)
    -- the labels live at the call point stay live through the push
    have hl0 : SState.RInv (fun _ => False) (s.pushFrame.pushBind selfB) :=
      SState.pushBind_rinv (PushFrame.rinv_pushFrame hloc) selfB v₀ hsv
    have hsa₀ : SState.ShapeAt s.pushFrame := (PushFrame.rinv_pushFrame hloc).2.2
    have hkeep := (fold_start bs s (args.take j) (s.pushFrame.pushBind selfB) [] [] hl0 (hg.uniq.pushBind selfB)
      (by simp [SState.pushBind, SState.pushFrame]) rfl rfl
      (fun l hl => (SState.live_pushBind hsa₀ selfB l).2 ((PushFrame.live_pushFrame s l).2 hl))
      (fun p l _ hl => ⟨hl, by simp⟩)
      (fun a' ha' => hlive a' (List.mem_of_mem_take ha'))).2.2.2.2.2.1
    rw [List.take_add_one, ha, Option.toList_some, List.foldl_append, List.foldl_cons, List.foldl_nil]
    generalize ((args.take j).foldl (callStep bs) (s.pushFrame.pushBind selfB, [])) = r at ih hacc htop hkeep
    obtain ⟨t, acc⟩ := r
    dsimp only at ih hacc htop hkeep ⊢
    subst hacc
    refine Strict.sgood_pushBindShaped ih _ rfl (.inl (hmem j a ha)) (fun k hk => ?_) (fun k hk => ?_)
      (fun e => by have := htop.len; rw [e] at this; simp at this)
    · rw [htop.heldTy, htop.heldMem]
      have hkl : s.Live k := hlive a (List.mem_of_getElem? ha) k hk
      exact ⟨hheld j a k ha hk, hg.held k hkl⟩
    · have hkl : s.Live k := hlive a (List.mem_of_getElem? ha) k hk
      refine ⟨.inl (hkeep k hkl), ?_⟩
      rw [htop.next]
      obtain ⟨q, _, hq⟩ := (SState.live_iff s k).1 hkl
      exact (hloc.2.2 q k hq).2

/-! ## The closure's push -/

/-- The borrow parameters among the first `j` (each takes the next fresh label in the closure). -/
def refBefore (xs : List (Sem × PiDom)) (j : Nat) : Nat := ((xs.take j).filter (·.2.isRef)).length

theorem refBefore_succ {xs : List (Sem × PiDom)} {j : Nat} {x : Sem × PiDom} (h : xs[j]? = some x) :
    refBefore xs (j + 1) = refBefore xs j + if x.2.isRef then 1 else 0 := by
  simp only [refBefore, List.take_add_one, h, Option.toList_some, List.filter_append, List.length_append]
  by_cases hr : x.2.isRef = true
  · simp [List.filter_cons, hr]
  · simp [List.filter_cons, hr]

theorem refBefore_mono (xs : List (Sem × PiDom)) {i j : Nat} (h : i ≤ j) : refBefore xs i ≤ refBefore xs j := by
  induction j with
  | zero => rw [Nat.le_zero.1 h]; exact Nat.le_refl _
  | succ j ih =>
    rcases Nat.lt_or_eq_of_le h with h | h
    · cases e : xs[j]? with
      | none =>
        have hl : xs.length ≤ j := List.getElem?_eq_none_iff.1 e
        have : refBefore xs (j + 1) = refBefore xs j := by
          simp only [refBefore, List.take_of_length_le (by omega : xs.length ≤ j + 1),
            List.take_of_length_le (by omega : xs.length ≤ j)]
        rw [this]; exact ih (by omega)
      | some x => rw [refBefore_succ e]; exact Nat.le_trans (ih (by omega)) (Nat.le_add_right _ _)
    · rw [h]; exact Nat.le_refl _

/-- A borrow parameter's label is below every later borrow parameter's, and below the count. -/
theorem refBefore_lt {xs : List (Sem × PiDom)} {i j : Nat} (hij : i < j) {x : Sem × PiDom} (hx : xs[i]? = some x)
    (hr : x.2.isRef = true) : refBefore xs i < refBefore xs j := by
  have h1 : refBefore xs (i + 1) = refBefore xs i + 1 := by rw [refBefore_succ hx, hr]; rfl
  have h2 : refBefore xs (i + 1) ≤ refBefore xs j := refBefore_mono xs (Nat.succ_le_of_lt hij)
  omega

/-- The labels the closure's borrow parameters take are the `refBefore`s of the borrow parameters. -/
theorem refBefore_surj (xs : List (Sem × PiDom)) : ∀ (n l : Nat), l < refBefore xs n →
    ∃ i x, i < n ∧ xs[i]? = some x ∧ x.2.isRef = true ∧ refBefore xs i = l
  | 0, l, h => by simp [refBefore] at h
  | n + 1, l, h => by
    cases e : xs[n]? with
    | none =>
      have hl : xs.length ≤ n := List.getElem?_eq_none_iff.1 e
      have : refBefore xs (n + 1) = refBefore xs n := by
        simp only [refBefore, List.take_of_length_le (by omega : xs.length ≤ n + 1),
          List.take_of_length_le (by omega : xs.length ≤ n)]
      rw [this] at h
      obtain ⟨i, x, hi, hx, hr, he⟩ := refBefore_surj xs n l h
      exact ⟨i, x, by omega, hx, hr, he⟩
    | some x =>
      rw [refBefore_succ e] at h
      by_cases hl : l < refBefore xs n
      · obtain ⟨i, x', hi, hx, hr, he⟩ := refBefore_surj xs n l hl
        exact ⟨i, x', by omega, hx, hr, he⟩
      · cases hr : x.2.isRef
        · rw [hr] at h; simp at h; omega
        · exact ⟨n, x, by omega, e, hr, by rw [hr] at h; simp at h; omega⟩

section
variable (fb : List PBind × PBind) (xs : List (Sem × PiDom))

/-- Parameter `j`'s type in the closure, at the earlier arguments (`fixStep`'s `T`). -/
noncomputable def clT (j : Nat) : TyS :=
  match fb.1[j]? with
  | some b => b.1 ((xs.take j).map (·.1))
  | none => .plain (((xs[j]?).map fun x => x.2.dom ((xs.take j).map (·.1))).getD TyM.err)

/-- Parameter `j`'s declared reading (`fixStep`'s `d`). -/
def clD (j : Nat) : DeclInfo := match fb.1[j]? with | some b => b.2 | none => .other

/-- Parameter `j`'s binding in the closure: at its type, a borrow parameter holding its fresh label. -/
noncomputable def clB (j : Nat) (x : Sem × PiDom) : SBinding :=
  { ty := { clT fb xs j with label := if x.2.isRef then some (refBefore xs j) else none }, val := fun _ => x.1,
    decl := clD fb j }

/-- A borrow parameter's cell, reading its label at the recorded content type. -/
def cellB (T : TyM) (l : Nat) : SBinding := { ty := .plain T, val := fun ψ => ψ l, decl := .other }

end

/-- **What the closure's push has done after `j` parameters** (`fixBodyAt`'s fold of `fixStep`): frame 0 holds one cell
per borrow parameter so far, reading its label at its recorded type; frame 1 holds `self` and the parameters; the
counter is the number of borrow parameters; each borrow parameter's label is lent at its cell only, held by the
parameter, recorded at its type with its argument. -/
structure ClTop (fb : List PBind × PBind) (xs : List (Sem × PiDom)) (selfB : SBinding) (j : Nat) (t : SState) : Prop where
  len : t.env.length = 2
  f0 : ∃ F0, t.env[0]? = some F0 ∧ F0.temps = [] ∧ F0.binds.length = refBefore xs j ∧
    ∀ l, l < refBefore xs j → F0.binds[l]? = some (cellB (t.heldTy l) l)
  f1 : ∃ F1, t.env[1]? = some F1 ∧ F1.temps = [] ∧ F1.binds.length = j + 1 ∧ F1.binds[0]? = some selfB ∧
    ∀ i x, i < j → xs[i]? = some x → F1.binds[i + 1]? = some (clB fb xs i x)
  next : t.nextLoan = refBefore xs j
  lent : ∀ l, t.lent l = if l < refBefore xs j then [⟨.bind 0 l, [], false⟩] else []
  shape : ∀ q l, t.shape q = some l ↔
    ∃ i x, i < j ∧ xs[i]? = some x ∧ x.2.isRef = true ∧ q = .bind 1 (i + 1) ∧ l = refBefore xs i
  held : ∀ i x, i < j → xs[i]? = some x → x.2.isRef = true →
    t.heldTy (refBefore xs i) = (clT fb xs i).m ∧ t.heldMem (refBefore xs i) = x.1

/-- `fixStep`'s type and reading of the next parameter. -/
noncomputable def fT (fb : List PBind × PBind) (acc : List Sem) (x : Sem × PiDom) : TyS :=
  match fb.1[acc.length]? with | some b => b.1 acc | none => .plain (x.2.dom acc)
def fD (fb : List PBind × PBind) (acc : List Sem) : DeclInfo :=
  match fb.1[acc.length]? with | some b => b.2 | none => .other

theorem fixStep_ref (fb : List PBind × PBind) (t : SState) (acc : List Sem) (cells : List Pos) (x : Sem × PiDom)
    (hr : x.2.isRef = true) :
    (fixStep fb (t, acc, cells) x).1 = pushBindShaped
      (((({ t with nextLoan := t.nextLoan + 1 }.pushCell (cellB (fT fb acc x).m t.nextLoan)).setLent t.nextLoan
        [⟨.bind 0 (((t.env[0]?).map (fun fr : SFrame => fr.binds.length)).getD 0), [], false⟩]).setHeldMem t.nextLoan x.1).setHeldTy
          t.nextLoan (fT fb acc x).m)
      { ty := { fT fb acc x with label := some t.nextLoan }, val := fun _ => x.1, decl := fD fb acc } := by
  dsimp only [fixStep]; rw [if_pos hr]; rfl

theorem fixStep_plain (fb : List PBind × PBind) (t : SState) (acc : List Sem) (cells : List Pos) (x : Sem × PiDom)
    (hr : x.2.isRef = false) :
    (fixStep fb (t, acc, cells) x).1 =
      t.pushBind { ty := { fT fb acc x with label := none }, val := fun _ => x.1, decl := fD fb acc } := by
  dsimp only [fixStep]; rw [if_neg (by simp [hr])]; rfl

theorem fixStep_acc (fb : List PBind × PBind) (t : SState) (acc : List Sem) (cells : List Pos) (x : Sem × PiDom) :
    (fixStep fb (t, acc, cells) x).2.1 = acc ++ [x.1] := by
  dsimp only [fixStep]; split <;> rfl

/-- A push of a binding holding a label nobody holds: the top frame gains it, and it holds the label. -/
theorem pushBindShaped_free {t : SState} {E : Nat} {F : SFrame} (hlen : t.env.length = E + 1) (hF : t.env[E]? = some F)
    (b : SBinding) {l : Nat} (hl : b.ty.label = some l) (hno : ∀ q, t.shape q ≠ some l) :
    (pushBindShaped t b).env = t.env.modify E (fun fr => { fr with binds := fr.binds ++ [b] }) ∧
    (pushBindShaped t b).shape = (fun q => if q = .bind E F.binds.length then some l else t.shape q) ∧
    (pushBindShaped t b).nextLoan = t.nextLoan ∧ (pushBindShaped t b).lent = t.lent ∧
    (pushBindShaped t b).heldTy = t.heldTy ∧ (pushBindShaped t b).heldMem = t.heldMem := by
  have hh : t.holderOf l = none := by
    unfold SState.holderOf
    exact List.find?_eq_none.2 fun q _ => by simpa using hno q
  have ht : t.topIdx = E := by simp only [SState.topIdx, hlen]; omega
  have htk : t.takeLabel l = t := by unfold SState.takeLabel; rw [hh]
  have hlast : (t.pushBind b).env.getLast? = some { F with binds := F.binds ++ [b] } := by
    rw [List.getLast?_eq_getElem?]
    simp only [SState.pushBind, ht, List.length_modify, hlen, List.getElem?_modify]
    simp [hF]
  have hti : (t.pushBind b).topIdx = E := by simp [SState.topIdx, SState.pushBind, hlen]
  unfold pushBindShaped
  rw [hl]; dsimp only
  rw [htk, hlast]; dsimp only
  refine ⟨by show t.env.modify t.topIdx _ = _; rw [ht], ?_, rfl, rfl, rfl, rfl⟩
  funext q; rw [hti]; simp only [List.length_append, List.length_singleton, Nat.add_sub_cancel]; rfl

theorem fT_eq {fb : List PBind × PBind} {xs : List (Sem × PiDom)} {j : Nat} {x : Sem × PiDom} (hx : xs[j]? = some x) :
    fT fb ((xs.take j).map (·.1)) x = clT fb xs j ∧ fD fb ((xs.take j).map (·.1)) = clD fb j := by
  have hj : j < xs.length := (List.getElem?_eq_some_iff.1 hx).1
  have hl : ((xs.take j).map (·.1)).length = j := by simp; omega
  unfold fT fD clT clD
  rw [hl, hx]
  exact ⟨rfl, rfl⟩

/-- The step of a borrow parameter keeps `ClTop`. -/
theorem ClTop.step_ref {fb : List PBind × PBind} {xs : List (Sem × PiDom)} {selfB : SBinding} {j : Nat} {t : SState}
    (h : ClTop fb xs selfB j t) {x : Sem × PiDom} (hx : xs[j]? = some x) (hr : x.2.isRef = true) (cells : List Pos) :
    ClTop fb xs selfB (j + 1) (fixStep fb (t, (xs.take j).map (·.1), cells) x).1 := by
  obtain ⟨hT, hD⟩ := fT_eq (fb := fb) hx
  rw [fixStep_ref fb t _ cells x hr, hT, hD]
  obtain ⟨F0, h0, h0t, h0l, h0c⟩ := h.f0
  obtain ⟨F1, h1, h1t, h1l, h1s, h1p⟩ := h.f1
  have hn := h.next
  have hrb : refBefore xs (j + 1) = refBefore xs j + 1 := by rw [refBefore_succ hx, hr]; rfl
  generalize hT' : (clT fb xs j).m = T
  generalize hu : (((({ t with nextLoan := t.nextLoan + 1 }.pushCell (cellB T t.nextLoan)).setLent t.nextLoan
        [⟨.bind 0 (((t.env[0]?).map (fun fr : SFrame => fr.binds.length)).getD 0), [], false⟩]).setHeldMem
          t.nextLoan x.1).setHeldTy t.nextLoan T) = u
  have hue : u.env = t.env.modify 0 (fun fr => { fr with binds := fr.binds ++ [cellB T t.nextLoan] }) := by
    rw [← hu]; rfl
  have hul : u.env.length = 2 := by rw [hue, List.length_modify, h.len]
  have hu1 : u.env[1]? = some F1 := by rw [hue, List.getElem?_modify]; simp [h1]
  have hu0 : u.env[0]? = some { F0 with binds := F0.binds ++ [cellB T t.nextLoan] } := by
    rw [hue, List.getElem?_modify]; simp [h0]
  have hush : u.shape = t.shape := by rw [← hu]; rfl
  have hno : ∀ q, u.shape q ≠ some t.nextLoan := by
    intro q e; rw [hush] at e
    obtain ⟨i, x', hi, hx', hr', _, hl⟩ := (h.shape q _).1 e
    have := refBefore_lt hi hx' hr'; omega
  generalize hbn : ({ ty := { clT fb xs j with label := some t.nextLoan }, val := fun _ => x.1, decl := clD fb j } :
    SBinding) = bn
  obtain ⟨e1, e2, e3, e4, e5, e6⟩ := pushBindShaped_free (E := 1) hul hu1 bn (by rw [← hbn]) hno
  have hsite : (((t.env[0]?).map (fun fr : SFrame => fr.binds.length)).getD 0) = t.nextLoan := by
    rw [h0]; simp [h0l, hn]
  have hb : bn = clB fb xs j x := by rw [← hbn]; simp [clB, hr, hn]
  refine ⟨by rw [e1, List.length_modify, hul], ⟨{ F0 with binds := F0.binds ++ [cellB T t.nextLoan] }, ?_, h0t, ?_, ?_⟩,
    ⟨{ F1 with binds := F1.binds ++ [bn] }, ?_, h1t, by simp [h1l], ?_, ?_⟩, ?_, fun m => ?_, fun q m => ?_, ?_⟩
  · rw [e1, List.getElem?_modify]; simp [hu0]
  · simp [h0l, hrb]
  · intro m hm
    rw [e5, ← hu]; simp only [SState.setHeldTy, SState.setHeldMem]
    by_cases hml : m = t.nextLoan
    · subst hml; rw [if_pos rfl, List.getElem?_append_right (by omega)]; simp [h0l, hn]
    · rw [if_neg hml, List.getElem?_append_left (by omega)]
      have := h0c m (by omega); rw [this]; rfl
  · rw [e1, List.getElem?_modify]; simp [hu1]
  · rw [List.getElem?_append_left (by omega)]; exact h1s
  · intro i x' hi hx'
    by_cases e : i = j
    · subst e; rw [hx] at hx'; cases hx'
      rw [← h1l, List.getElem?_concat_length, hb]
    · rw [List.getElem?_append_left (by omega)]; exact h1p i x' (by omega) hx'
  · rw [e3, ← hu]; show t.nextLoan + 1 = _; rw [hrb, hn]
  · rw [e4, ← hu]; simp only [SState.setHeldTy, SState.setHeldMem, SState.setLent, SState.pushCell]
    rw [hsite, hrb, ← hn]
    by_cases hml : m = t.nextLoan
    · subst hml; simp
    · rw [if_neg hml, h.lent m, hn]
      by_cases hm : m < refBefore xs j
      · rw [if_pos hm, if_pos (by omega)]
      · rw [if_neg hm, if_neg (by omega)]
  · rw [e2, h1l]; dsimp only
    by_cases hq : q = .bind 1 (j + 1)
    · subst hq; rw [if_pos rfl]
      constructor
      · intro e; cases e; exact ⟨j, x, by omega, hx, hr, rfl, hn⟩
      · rintro ⟨i, x', hi, hx', hr', hq', hl⟩
        injection hq' with _ hq'; have : i = j := by omega
        subst this; rw [hl, hn]
    · rw [if_neg hq, hush, h.shape q m]
      constructor
      · rintro ⟨i, x', hi, hx', hr', hq', hl⟩; exact ⟨i, x', by omega, hx', hr', hq', hl⟩
      · rintro ⟨i, x', hi, hx', hr', hq', hl⟩
        refine ⟨i, x', ?_, hx', hr', hq', hl⟩
        rcases Nat.lt_or_ge i j with hij | hij
        · exact hij
        · exfalso; have : i = j := by omega
          subst this; exact hq hq'
  · intro i x' hi hx' hr'
    rw [e5, e6, ← hu]; simp only [SState.setHeldTy, SState.setHeldMem]
    by_cases e : i = j
    · subst e; rw [hx] at hx'; cases hx'
      rw [hn, if_pos rfl, if_pos rfl]; exact ⟨hT'.symm, rfl⟩
    · have hlt := refBefore_lt (show i < j by omega) hx' hr'
      rw [if_neg (by omega), if_neg (by omega)]
      exact h.held i x' (by omega) hx' hr'

/-- The step of a plain parameter keeps `ClTop`. -/
theorem ClTop.step_plain {fb : List PBind × PBind} {xs : List (Sem × PiDom)} {selfB : SBinding} {j : Nat} {t : SState}
    (h : ClTop fb xs selfB j t) {x : Sem × PiDom} (hx : xs[j]? = some x) (hr : x.2.isRef = false) (cells : List Pos) :
    ClTop fb xs selfB (j + 1) (fixStep fb (t, (xs.take j).map (·.1), cells) x).1 := by
  obtain ⟨hT, hD⟩ := fT_eq (fb := fb) hx
  rw [fixStep_plain fb t _ cells x hr, hT, hD]
  obtain ⟨F0, h0, h0t, h0l, h0c⟩ := h.f0
  obtain ⟨F1, h1, h1t, h1l, h1s, h1p⟩ := h.f1
  have hrb : refBefore xs (j + 1) = refBefore xs j := by rw [refBefore_succ hx, hr]; rfl
  have ht : t.topIdx = 1 := by simp [SState.topIdx, h.len]
  generalize hbn : ({ ty := { clT fb xs j with label := none }, val := fun _ => x.1, decl := clD fb j } :
    SBinding) = bn
  have hb : bn = clB fb xs j x := by rw [← hbn]; simp [clB, hr]
  have he : (t.pushBind bn).env = t.env.modify 1 (fun fr => { fr with binds := fr.binds ++ [bn] }) := by
    show t.env.modify t.topIdx _ = _; rw [ht]
  refine ⟨by rw [he, List.length_modify, h.len], ⟨F0, ?_, h0t, by rw [h0l, hrb], fun l hl => ?_⟩,
    ⟨{ F1 with binds := F1.binds ++ [bn] }, ?_, h1t, by simp [h1l], ?_, ?_⟩, by rw [hrb]; exact h.next,
    fun m => by rw [hrb]; exact h.lent m, fun q m => ?_, ?_⟩
  · rw [he, List.getElem?_modify]; simp [h0]
  · exact h0c l (by rw [← hrb]; exact hl)
  · rw [he, List.getElem?_modify]; simp [h1]
  · rw [List.getElem?_append_left (by omega)]; exact h1s
  · intro i x' hi hx'
    by_cases e : i = j
    · subst e; rw [hx] at hx'; cases hx'
      rw [← h1l, List.getElem?_concat_length, hb]
    · rw [List.getElem?_append_left (by omega)]; exact h1p i x' (by omega) hx'
  · show t.shape q = some m ↔ _
    rw [h.shape q m]
    constructor
    · rintro ⟨i, x', hi, hx', hr', hq', hl⟩; exact ⟨i, x', by omega, hx', hr', hq', hl⟩
    · rintro ⟨i, x', hi, hx', hr', hq', hl⟩
      refine ⟨i, x', ?_, hx', hr', hq', hl⟩
      rcases Nat.lt_or_ge i j with hij | hij
      · exact hij
      · exfalso; have : i = j := by omega
        subst this; rw [hx] at hx'; cases hx'; rw [hr] at hr'; cases hr'
  · intro i x' hi hx' hr'
    by_cases e : i = j
    · subst e; rw [hx] at hx'; cases hx'; rw [hr] at hr'; cases hr'
    · exact h.held i x' (by omega) hx' hr'

/-- The first state of the closure's push: `self` bound in the global's forming state under a fresh frame. -/
theorem ClTop.start (fb : List PBind × PBind) (xs : List (Sem × PiDom)) (selfB : SBinding) :
    ClTop fb xs selfB 0 (formG.under.pushBind selfB) := by
  have hl : formG.under.env.length = 2 := rfl
  have ht : formG.under.topIdx = 1 := rfl
  have he : (formG.under.pushBind selfB).env = [{}, { binds := [selfB] }] := by
    show formG.under.env.modify formG.under.topIdx _ = _; rw [ht]; rfl
  refine ⟨by rw [he]; rfl, ⟨{}, by rw [he]; rfl, rfl, rfl, fun l hl => absurd hl (by simp [refBefore])⟩,
    ⟨{ binds := [selfB] }, by rw [he]; rfl, rfl, rfl, rfl, fun i _ hi => absurd hi (by omega)⟩, rfl,
    fun l => by simp [refBefore]; rfl, fun q l => ?_, fun i _ hi => absurd hi (by omega)⟩
  constructor
  · intro e
    have : (formG.under.pushBind selfB).shape q = none := by
      show (q.down?).bind (fun _ => none) = none; cases q.down? <;> rfl
    rw [this] at e; cases e
  · rintro ⟨i, _, hi, _⟩; exact absurd hi (by omega)

/-- **The closure's push, characterised**. -/
theorem clFold (fb : List PBind × PBind) (xs : List (Sem × PiDom)) (selfB : SBinding) :
    ∀ j, j ≤ xs.length →
      ((xs.take j).foldl (fixStep fb) (formG.under.pushBind selfB, [], [])).2.1 = (xs.take j).map (·.1) ∧
      ClTop fb xs selfB j ((xs.take j).foldl (fixStep fb) (formG.under.pushBind selfB, [], [])).1
  | 0, _ => ⟨rfl, ClTop.start fb xs selfB⟩
  | j + 1, hj => by
    obtain ⟨x, hx⟩ : ∃ x, xs[j]? = some x := ⟨xs[j], List.getElem?_eq_getElem (by omega)⟩
    obtain ⟨ih1, ih2⟩ := clFold fb xs selfB j (by omega)
    rw [List.take_add_one, hx, Option.toList_some, List.foldl_append, List.foldl_cons, List.foldl_nil]
    generalize ((xs.take j).foldl (fixStep fb) (formG.under.pushBind selfB, [], [])) = r at ih1 ih2
    obtain ⟨t, acc, cells⟩ := r
    dsimp only at ih1 ih2
    subst ih1
    refine ⟨by rw [fixStep_acc]; simp, ?_⟩
    cases hr : x.2.isRef
    · exact ih2.step_plain hx hr cells
    · exact ih2.step_ref hx hr cells

/-! ## The closure's start state: what each position holds, and its goodness -/

section ClGood
variable {fb : List PBind × PBind} {xs : List (Sem × PiDom)} {selfB : SBinding} {n : Nat} {t : SState}

/-- What a binding of the closure's start state is: a cell, `self`, or a parameter. -/
theorem ClTop.bindAt (h : ClTop fb xs selfB n t) (hn : n ≤ xs.length) {f i : Nat} {b : SBinding}
    (hb : t.env[f]?.bind (·.binds[i]?) = some b) :
    (f = 0 ∧ i < refBefore xs n ∧ b = cellB (t.heldTy i) i) ∨ (f = 1 ∧ i = 0 ∧ b = selfB) ∨
      (∃ k x, f = 1 ∧ i = k + 1 ∧ k < n ∧ xs[k]? = some x ∧ b = clB fb xs k x) := by
  obtain ⟨F0, h0, -, h0l, h0c⟩ := h.f0
  obtain ⟨F1, h1, -, h1l, h1s, h1p⟩ := h.f1
  match f, i with
  | 0, i =>
    rw [h0] at hb; simp only [Option.bind_some] at hb
    have hi : i < refBefore xs n := by rw [← h0l]; exact (List.getElem?_eq_some_iff.1 hb).1
    rw [h0c i hi] at hb; cases hb; exact .inl ⟨rfl, hi, rfl⟩
  | 1, 0 => rw [h1] at hb; simp only [Option.bind_some, h1s] at hb; cases hb; exact .inr (.inl ⟨rfl, rfl, rfl⟩)
  | 1, k + 1 =>
    rw [h1] at hb; simp only [Option.bind_some] at hb
    have hk : k < n := by have := (List.getElem?_eq_some_iff.1 hb).1; omega
    obtain ⟨x, hx⟩ : ∃ x, xs[k]? = some x := ⟨xs[k], List.getElem?_eq_getElem (by omega)⟩
    rw [h1p k x hk hx] at hb; cases hb; exact .inr (.inr ⟨k, x, rfl, rfl, hk, hx, rfl⟩)
  | f + 2, i =>
    have : t.env[f + 2]? = none := List.getElem?_eq_none (by rw [h.len]; omega)
    rw [this] at hb; cases hb

theorem ClTop.temps (h : ClTop fb xs selfB n t) (f i : Nat) : t.env[f]?.bind (·.temps[i]?) = none := by
  obtain ⟨F0, h0, h0t, -⟩ := h.f0
  obtain ⟨F1, h1, h1t, -⟩ := h.f1
  match f with
  | 0 => rw [h0]; simp [h0t]
  | 1 => rw [h1]; simp [h1t]
  | f + 2 => rw [List.getElem?_eq_none (by rw [h.len]; omega)]; rfl

theorem ClTop.valAt_temp (h : ClTop fb xs selfB n t) (f i : Nat) : t.valAt (.temp f i) = fun _ => .err := by
  simp only [SState.valAt, h.temps f i]

/-- The closure's live labels are the borrow parameters' labels, `0` to their number. -/
theorem ClTop.live_iff (h : ClTop fb xs selfB n t) (hn : n ≤ xs.length) (l : Nat) :
    t.Live l ↔ l < refBefore xs n := by
  obtain ⟨F1, h1, -, h1l, -, h1p⟩ := h.f1
  rw [SState.live_iff]
  constructor
  · rintro ⟨p, -, hp⟩
    obtain ⟨k, x, hk, hx, hr, -, rfl⟩ := (h.shape p l).1 hp
    exact refBefore_lt hk hx hr
  · intro hl
    obtain ⟨k, x, hk, hx, hr, rfl⟩ := refBefore_surj xs n l hl
    refine ⟨.bind 1 (k + 1), ?_, (h.shape _ _).2 ⟨k, x, hk, hx, hr, rfl, rfl⟩⟩
    rw [SState.mem_positions]; simp [SState.lookup, h1, h1p k x hk hx]

/-- A borrow parameter's binding holds its argument at its type. -/
theorem ClTop.holder (h : ClTop fb xs selfB n t) {q : Pos} {l : Nat} (hq : t.shape q = some l) :
    ∃ k x, k < n ∧ xs[k]? = some x ∧ x.2.isRef = true ∧ q = .bind 1 (k + 1) ∧ l = refBefore xs k ∧
      t.valAt q = (fun _ => x.1) ∧ (t.tyAt q).m = (clT fb xs k).m := by
  obtain ⟨k, x, hk, hx, hr, rfl, rfl⟩ := (h.shape q l).1 hq
  obtain ⟨F1, h1, -, -, -, h1p⟩ := h.f1
  refine ⟨k, x, hk, hx, hr, rfl, rfl, ?_, ?_⟩
  · simp only [SState.valAt, h1, Option.bind_some, h1p k x hk hx]; rfl
  · simp only [SState.tyAt, h1, Option.bind_some, h1p k x hk hx]; rfl

/-- A whole member is an open member. -/
theorem pmem_of_mem' (K : RunCtx) {v : Sem} {T : TyM} (hm : v ∈ₛ[K.dm.read] T) : K.dm.pmem K.Γ v T :=
  DataModel.pmem_of_mem K.dm K.Γ (Strict.mem_whole (DataModel.read_wholeFields K.dm) hm) hm

/-- **The closure's start state is good**: `self` and the arguments members of their types. -/
theorem ClTop.good (K : RunCtx) (φ : Future) (h : ClTop fb xs selfB n t) (hn : n ≤ xs.length) {v₀ : Sem}
    (hsv : selfB.val = fun _ => v₀) (hsg : v₀ ∈ₛ[K.dm.read] selfB.ty.m)
    (hmem : ∀ k x, k < n → xs[k]? = some x → x.1 ∈ₛ[K.dm.read] (clT fb xs k).m) :
    Strict.SGood K.dm K.Γ φ t := by
  have hlive := h.live_iff hn
  have hnext := h.next
  refine ⟨fun ψ hψ f i hfi => ?_, fun ψ hψ p l hpl => ?_, fun l hl => ?_, fun f i l hl => ?_, ⟨?_, ?_, ?_⟩, ?_, ?_⟩
  · rw [SState.mem_positions] at hfi
    simp only [SState.lookup] at hfi
    cases hb : t.env[f]?.bind (·.binds[i]?) with
    | none => rw [hb] at hfi; cases hfi
    | some b =>
    have hv : t.valAt (.bind f i) = b.val := by simp only [SState.valAt, hb]
    have hty : t.tyAt (.bind f i) = b.ty := by simp only [SState.tyAt, hb]
    rw [hv, hty]
    rcases h.bindAt hn hb with ⟨rfl, hi, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨k, x, rfl, rfl, hk, hx, rfl⟩
    · exact .inl (pmem_of_mem' K (hψ.2 i ((hlive i).2 hi)))
    · rw [hsv]; exact .inl (pmem_of_mem' K hsg)
    · exact .inl (pmem_of_mem' K (hmem k x hk hx))
  · obtain ⟨k, x, hk, hx, hr, rfl, rfl, hv, -⟩ := h.holder hpl
    rw [hv, (h.held k x hk hx hr).1]
    exact pmem_of_mem' K (hmem k x hk hx)
  · obtain ⟨p, -, hp⟩ := (SState.live_iff t l).1 hl
    obtain ⟨k, x, hk, hx, hr, rfl, rfl, -, -⟩ := h.holder hp
    rw [(h.held k x hk hx hr).1, (h.held k x hk hx hr).2]
    exact hmem k x hk hx
  · obtain ⟨k, x, hk, hx, hr, -, rfl, -, hty⟩ := h.holder hl
    rw [hty, (h.held k x hk hx hr).1]
  · intro p ψ ψ' e
    rw [show ψ = ψ' from funext fun y => e y (.inl trivial)]
  · intro r x _ hr
    obtain ⟨k, x', -, -, -, -, -, hv, -⟩ := h.holder hr
    rw [hv]; exact FT.const _ _
  · intro p x hp
    obtain ⟨k, x', hk, hx, hr, rfl, rfl, -⟩ := h.holder hp
    obtain ⟨F1, h1, -, -, -, h1p⟩ := h.f1
    refine ⟨?_, by rw [hnext]; exact refBefore_lt hk hx hr⟩
    rw [SState.mem_positions]; simp [SState.lookup, h1, h1p k x' hk hx]
  · intro p l ⟨ψ, x, hne⟩
    rw [hnext]
    simp only [SState.toMean] at hne
    cases p with
    | temp f i => rw [h.valAt_temp] at hne; exact absurd rfl hne
    | bind f i =>
      cases hb : t.env[f]?.bind (·.binds[i]?) with
      | none => simp only [SState.valAt, hb] at hne; exact absurd rfl hne
      | some b =>
        simp only [SState.valAt, hb] at hne
        rcases h.bindAt hn hb with ⟨rfl, hi, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨k, x', rfl, rfl, hk, hx, rfl⟩
        · simp only [cellB] at hne
          by_cases hli : i = l
          · subst hli; exact hi
          · rw [Future.upd_other _ _ hli] at hne; exact absurd rfl hne
        · rw [hsv] at hne; exact absurd rfl hne
        · exact absurd rfl hne
  · intro p q l hp hq
    obtain ⟨k, x, hk, hx, hr, rfl, rfl, -⟩ := h.holder hp
    obtain ⟨k', x', hk', hx', hr', rfl, e, -⟩ := h.holder hq
    rcases Nat.lt_trichotomy k k' with hlt | rfl | hlt
    · have := refBefore_lt hlt hx hr; omega
    · rfl
    · have := refBefore_lt hlt hx' hr'; omega

end ClGood

/-! ## The two pushes correspond -/

section Corr
variable {args : List Res} {ps : List PiDom}

theorem zip_get (hlen : (args.map (·.1)).length = ps.length) {j : Nat} {a : Res} {d : PiDom} (ha : args[j]? = some a)
    (hd : ps[j]? = some d) : ((args.map (·.1)).zip ps)[j]? = some (a.1, d) := by
  rw [List.getElem?_zip_eq_some]; exact ⟨by simp [ha], hd⟩

theorem zip_take_fst (hlen : (args.map (·.1)).length = ps.length) (j : Nat) :
    (((args.map (·.1)).zip ps).take j).map (·.1) = accOf args j := by
  unfold accOf
  rw [List.map_take, List.map_fst_zip (by omega), List.map_take]

/-- The borrow arguments' labels are, in order, the closure's borrow parameters' labels: `argLabels` of the first `j`
arguments has as many as there are borrow parameters among the first `j`, and a borrow argument's label is the
`refBefore`-th. -/
theorem argLabels_corr (hlen : (args.map (·.1)).length = ps.length)
    (hlab : ∀ (i : Nat) (a : Res) (d : PiDom), args[i]? = some a → ps[i]? = some d → (a.2.label.isSome = d.isRef)) :
    ∀ j, j ≤ args.length → (argLabels (args.take j)).length = refBefore ((args.map (·.1)).zip ps) j
  | 0, _ => by simp [argLabels, refBefore]
  | j + 1, hj => by
    obtain ⟨a, ha⟩ : ∃ a, args[j]? = some a := ⟨args[j], List.getElem?_eq_getElem (by omega)⟩
    have hpl : j < ps.length := by simp at hlen; omega
    obtain ⟨d, hd⟩ : ∃ d, ps[j]? = some d := ⟨ps[j], List.getElem?_eq_getElem hpl⟩
    rw [argLabels_take_succ ha, refBefore_succ (zip_get hlen ha hd), List.length_append,
      argLabels_corr hlen hlab j (by omega)]
    have := hlab j a d ha hd
    cases e : a.2.label <;> rw [e] at this <;> simp_all

theorem label_corr (hlen : (args.map (·.1)).length = ps.length)
    (hlab : ∀ (i : Nat) (a : Res) (d : PiDom), args[i]? = some a → ps[i]? = some d → (a.2.label.isSome = d.isRef))
    {j : Nat} {a : Res} {d : PiDom} (ha : args[j]? = some a) (hd : ps[j]? = some d) :
    a.2.label = if d.isRef then (argLabels args)[refBefore ((args.map (·.1)).zip ps) j]? else none := by
  have hj : j < args.length := (List.getElem?_eq_some_iff.1 ha).1
  have hc := argLabels_corr hlen hlab j (by omega)
  have hl := hlab j a d ha hd
  have e : argLabels args = argLabels (args.take j) ++ argLabels (args.drop j) := by
    unfold argLabels; rw [← List.filterMap_append, List.take_append_drop]
  have hdrop : args.drop j = a :: args.drop (j + 1) := by
    rw [List.drop_eq_getElem_cons hj]; congr; exact (List.getElem?_eq_some_iff.1 ha).2
  cases hr : d.isRef
  · rw [hr] at hl; cases e' : a.2.label <;> simp_all
  · rw [hr] at hl
    obtain ⟨k, hk⟩ := Option.isSome_iff_exists.1 hl
    rw [hk, if_pos rfl, e, ← hc, List.getElem?_append_right (Nat.le_refl _), Nat.sub_self, hdrop]
    simp [argLabels, hk]

theorem psOf_get : ∀ (bs : List PBind) (ds : List Term) (j : Nat) (d : PiDom), (psOf bs ds)[j]? = some d →
    ∃ b, bs[j]? = some b ∧ d.dom = fun acc => (b.1 acc).m
  | b :: bs, dt :: ds, 0, d, h => by simp [psOf] at h; subst h; exact ⟨b, rfl, rfl⟩
  | _ :: bs, _ :: ds, j + 1, d, h => by simp only [psOf, List.getElem?_cons_succ] at h; exact psOf_get bs ds j d h
  | [], _, _, _, h => by simp [psOf] at h
  | _ :: _, [], _, _, h => by simp [psOf] at h

/-- The in-place parameter's type and reading are the closure's. -/
theorem param_corr {bs : List PBind} {fb : List PBind × PBind} (hfb : fb.1 = bs) {args : List Res} {ps : List PiDom}
    (hlen : (args.map (·.1)).length = ps.length) {j : Nat} {a : Res} {b : PBind} (ha : args[j]? = some a)
    (hb : bs[j]? = some b) :
    (paramBind bs (accOf args j) a).ty.m = (clT fb ((args.map (·.1)).zip ps) j).m ∧
      (paramBind bs (accOf args j) a).decl = clD fb j ∧ (paramBind bs (accOf args j) a).ty.m = (b.1 (accOf args j)).m := by
  have hj : j < args.length := (List.getElem?_eq_some_iff.1 ha).1
  have hal : (accOf args j).length = j := by simp [accOf]; omega
  unfold paramBind clT clD
  rw [hal, hfb, hb, zip_take_fst hlen]
  exact ⟨rfl, rfl, rfl⟩

end Corr

/-! ## The start relation -/

theorem updList_self (ψ : Future) : ∀ fx : List (Nat × Sem), (∀ p ∈ fx, p.2 = ψ p.1) → ψ.updList fx = ψ
  | [], _ => rfl
  | (l, e) :: rest, h => by
    have he : e = ψ l := h (l, e) (List.mem_cons_self ..)
    have hu : ψ.upd l e = ψ := funext fun y => by
      by_cases hy : y = l
      · subst hy; rw [Future.upd_same, he]
      · rw [Future.upd_other _ _ hy]
    simp only [Future.updList, hu]
    exact updList_self ψ rest fun p hp => h p (List.mem_cons_of_mem _ hp)

/-- At the start the caller's frames are read at the future itself: each cell reads its own label, which the renaming
sends to its parameter label. -/
theorem cellFuture_start {ks : List Nat} {n : Nat} {t' : SState} {F0 : SFrame} (h0 : t'.env[0]? = some F0)
    (hl : F0.binds.length = ks.length) (hc : ∀ l, l < ks.length → ∃ T, F0.binds[l]? = some (cellB T l)) (ψ : Future) :
    cellFuture (callRen ks n) ks (cellsOf ks.length t') ψ = ψ := by
  unfold cellFuture
  apply updList_self
  intro p hp
  obtain ⟨i, hi⟩ := List.mem_iff_getElem?.1 hp
  rw [List.getElem?_zip_eq_some] at hi
  obtain ⟨hk, hv⟩ := hi
  have hik : i < ks.length := (List.getElem?_eq_some_iff.1 hk).1
  obtain ⟨T, hT⟩ := hc i hik
  have hh : t'.env.headD {} = F0 := by
    cases e : t'.env with
    | nil => rw [e] at h0; cases h0
    | cons F rest => rw [e] at h0; simp at h0; subst h0; rfl
  simp only [cellsOf, hh, List.getElem?_map, List.getElem?_take, if_pos hik, hT, Option.map_some] at hv
  rw [← Option.some.inj hv]
  show ψ (callRen ks n i) = ψ p.1
  rw [callRen_lt hik, (List.getElem?_eq_some_iff.1 hk).2]

section StartRel
variable {s : SState} {bs : List PBind} {fb : List PBind × PBind} {args : List Res} {ps : List PiDom}
  {selfB selfB' : SBinding} {t t' : SState}

/-- The closure's holder at a parameter's binding: its label exactly at a borrow parameter. -/
theorem ClTop.shape_param {xs : List (Sem × PiDom)} {n : Nat} (h : ClTop fb xs selfB' n t') {k : Nat} {x : Sem × PiDom}
    (hk : k < n) (hx : xs[k]? = some x) :
    t'.shape (.bind 1 (k + 1)) = if x.2.isRef then some (refBefore xs k) else none := by
  cases e : t'.shape (.bind 1 (k + 1)) with
  | none =>
    cases hr : x.2.isRef
    · rfl
    · exact absurd e (by rw [(h.shape _ _).2 ⟨k, x, hk, hx, hr, rfl, rfl⟩]; simp)
  | some l =>
    obtain ⟨i, x', _, hx', hr', hq, rfl⟩ := (h.shape _ _).1 e
    injection hq with _ hq; have : i = k := by omega
    subst this; rw [hx] at hx'; cases hx'; rw [hr', if_pos rfl]

theorem ClTop.shape_none {xs : List (Sem × PiDom)} {n : Nat} (h : ClTop fb xs selfB' n t') {q : Pos}
    (hq : ∀ k, k < n → q ≠ .bind 1 (k + 1)) : t'.shape q = none := by
  cases e : t'.shape q with
  | none => rfl
  | some l => obtain ⟨k, _, hk, -, -, rfl, -⟩ := (h.shape _ _).1 e; exact absurd rfl (hq k hk)

/-- The arguments and the parameters at index `k`. -/
theorem arg_at {xs : List (Sem × PiDom)} (hxs : xs = (args.map (·.1)).zip ps) (hlen : (args.map (·.1)).length = ps.length)
    {k : Nat} (hk : k < args.length) : ∃ a d, args[k]? = some a ∧ ps[k]? = some d ∧ xs[k]? = some (a.1, d) := by
  have hpk : k < ps.length := by simp at hlen; omega
  refine ⟨args[k], ps[k], List.getElem?_eq_getElem hk, List.getElem?_eq_getElem hpk, ?_⟩
  rw [hxs]; exact zip_get hlen (List.getElem?_eq_getElem hk) (List.getElem?_eq_getElem hpk)

/-- **The start relation** (`FrameRel` at the start of a call in place), from the two pushes' characterisations. -/
theorem startRel {xs : List (Sem × PiDom)} (hxs : xs = (args.map (·.1)).zip ps) (hfb : fb.1 = bs)
    (hps : ∀ (j : Nat) (d : PiDom), ps[j]? = some d → ∃ b, bs[j]? = some b)
    (hin : InTop s bs args selfB args.length t) (hcl : ClTop fb xs selfB' args.length t')
    (hself : BindRen (callRen (argLabels args) s.nextLoan) selfB selfB')
    (hlen : (args.map (·.1)).length = ps.length)
    (hlab : ∀ (i : Nat) (a : Res) (d : PiDom), args[i]? = some a → ps[i]? = some d → (a.2.label.isSome = d.isRef))
    (hnd : (argLabels args).Nodup) (hksn : ∀ k ∈ argLabels args, k < s.nextLoan)
    (hsites : ∀ l (y : Site), y ∈ s.lent l → y.pos ∈ s.positions)
    (hheld : ∀ j a k, args[j]? = some a → a.2.label = some k → s.heldTy k = (paramBind bs (accOf args j) a).ty.m) :
    FrameRel (callRen (argLabels args) s.nextLoan) t (argLabels args) t t' := by
  subst hxs
  have hM : refBefore ((args.map (·.1)).zip ps) args.length = (argLabels args).length := by
    rw [← argLabels_corr hlen hlab args.length (Nat.le_refl _), List.take_length]
  have htop : t.topIdx = s.env.length := by simp only [SState.topIdx, hin.len]; omega
  have hlow : ∀ (x : Site) l, x ∈ t.lent l → x.pos.frameOf < s.env.length := fun x l hx => by
    rw [hin.lent] at hx; exact frameOf_lt_of_mem (hsites l x hx)
  -- the closure's labels are the borrow parameters', sent to the arguments' labels
  have hσ : ∀ l, l < (argLabels args).length → callRen (argLabels args) s.nextLoan l ∈ argLabels args := fun l hl => by
    rw [callRen_lt hl]; exact List.getElem_mem hl
  have hlive' : ∀ l, t'.Live l → l < (argLabels args).length := fun l hl => by
    rw [← hM]; exact (hcl.live_iff (by simp at hlen ⊢; omega) l).1 hl
  -- a borrow parameter's label goes to its argument's label
  have hlabσ : ∀ (k : Nat) (a : Res) (d : PiDom), args[k]? = some a → ps[k]? = some d →
      a.2.label = (if d.isRef then some (refBefore ((args.map (·.1)).zip ps) k) else none).map
        (callRen (argLabels args) s.nextLoan) := by
    intro k a d ha hd
    rw [label_corr hlen hlab ha hd]
    cases hr : d.isRef
    · rfl
    · have hk : k < args.length := (List.getElem?_eq_some_iff.1 ha).1
      have hlt : refBefore ((args.map (·.1)).zip ps) k < (argLabels args).length := by
        rw [← hM]; exact refBefore_lt hk (zip_get hlen ha hd) hr
      simp [callRen_lt hlt, List.getElem?_eq_getElem hlt]
  obtain ⟨F, hF, hFt, hFl, hF0, hFp⟩ := hin.top
  obtain ⟨F1, h1, h1t, h1l, h1s, h1p⟩ := hcl.f1
  obtain ⟨F0, h0, -, h0l, h0c⟩ := hcl.f0
  refine ⟨callRen_inj hnd hksn, fun j => ?_, ⟨rfl, hcl.len⟩, fun _ _ => rfl, fun p _ ψ => ?_, fun _ _ => rfl,
    ⟨F, F1, ?_, ?_, by rw [hFl, h1l], ?_, by rw [hFt, h1t], fun j v hv => by rw [hFt] at hv; cases hv⟩,
    fun p hp => ?_, fun q l hq => ?_, fun l hl => ?_, fun l x hx _ => ?_, fun m x hx _ hxm => ?_,
    fun l x hx => ?_, fun _ _ _ _ => rfl, fun l hl => ?_⟩
  · rw [hcl.next, hM, hin.next, callRen_fresh]
  · rw [cellFuture_start h0 (by rw [h0l, hM]) (fun l hl => ⟨_, h0c l (by rw [hM]; exact hl)⟩)]
  · rw [List.getLast?_eq_getElem?, hin.len]; exact hF
  · rw [List.getLast?_eq_getElem?, hcl.len]; exact h1
  · intro i b b' hb hb'
    cases i with
    | zero => rw [hF0] at hb; rw [h1s] at hb'; cases hb; cases hb'; exact hself
    | succ k =>
      have hk : k < args.length := by have := (List.getElem?_eq_some_iff.1 hb).1; omega
      obtain ⟨a, d, ha, hd, hx⟩ := arg_at rfl hlen hk
      rw [hFp k a hk ha] at hb; rw [h1p k _ hk hx] at hb'; cases hb; cases hb'
      obtain ⟨bb, hbb⟩ := hps k d hd
      obtain ⟨e1, e2, -⟩ := param_corr hfb hlen ha hbb
      refine ⟨?_, e2, rfl, fun _ => rfl⟩
      have hext : ∀ (T T' : TyS), T.m = T'.m → T.label = T'.label → T = T' := fun ⟨_, _⟩ ⟨_, _⟩ h1 h2 => by
        simp only at h1 h2; rw [h1, h2]
      exact hext _ _ e1 (hlabσ k a d ha hd)
  · rw [htop] at hp
    cases p with
    | temp f i =>
      simp only [Pos.frameOf] at hp; subst hp
      rw [hin.shapeT, show upPos (argLabels args).length (.temp s.env.length i) = .temp 1 i from rfl,
        hcl.shape_none (fun k _ e => by cases e)]; rfl
    | bind f i =>
      simp only [Pos.frameOf] at hp; subst hp
      rw [show upPos (argLabels args).length (.bind s.env.length i) = .bind 1 i from rfl]
      cases i with
      | zero => rw [hin.shape0, hcl.shape_none (fun k _ e => by injection e with _ e; omega)]; rfl
      | succ k =>
        by_cases hk : k < args.length
        · obtain ⟨a, d, ha, hd, hx⟩ := arg_at rfl hlen hk
          rw [hin.shapeP k a hk ha, hcl.shape_param hk hx, hlabσ k a d ha hd]
        · rw [hin.shapeHi (k + 1) (by omega), hcl.shape_none (fun k' hk' e => by injection e with _ e; omega)]; rfl
  · obtain ⟨k, _, hk, -, -, rfl, -⟩ := (hcl.shape q l).1 hq
    exact ⟨.bind s.env.length (k + 1), by rw [htop]; rfl, rfl⟩
  · have hll := hlive' l hl
    refine ⟨fun hn => absurd (hσ l hll) hn, ?_⟩
    obtain ⟨k, x, hk, hx, hr, rfl⟩ := refBefore_surj _ args.length l (by rw [hM]; exact hll)
    obtain ⟨a, d, ha, hd, hx'⟩ := arg_at rfl hlen hk
    rw [hx] at hx'; cases hx'
    have hlab' := hlabσ k a d ha hd
    rw [hr, if_pos rfl, Option.map_some] at hlab'
    obtain ⟨bb, hbb⟩ := hps k d hd
    rw [hin.heldTy, hheld k a _ ha hlab', (hcl.held k _ hk hx hr).1, (param_corr hfb hlen ha hbb).1]
  · constructor
    · intro hm; have := hlow x _ hm; rw [htop] at hx; omega
    · intro hm; rw [hcl.lent l] at hm; split at hm
      · simp at hm; obtain ⟨pos, path, fill⟩ := x; cases pos <;> simp [upPos] at hm
      · cases hm
  · have := hlow x _ hxm; rw [htop] at hx; omega
  · rw [hcl.lent l] at hx
    split at hx
    · rename_i hl; simp at hx; subst hx
      exact .inr ⟨l, by rw [← hM]; exact hl, rfl⟩
    · cases hx
  · exact .inl (hσ l (hlive' l hl))

end StartRel

/-! ## `CallStartInvG`, proved -/

section
variable (K : RunCtx) (ρ : Assignment) (φ : Future)

/-- `clStart` is the closure's fold over every parameter. -/
theorem clStart_fold (ds : List Term) (c : Term) (piT : TyM) (selfM : Sem) (args : List Sem) :
    clStart K ρ φ ds c piT selfM args = ((((args.zip (psG K ρ φ ds))).take (args.zip (psG K ρ φ ds)).length).foldl
      (fixStep (fbG K ρ φ ds c)) (formG.under.pushBind
        { ty := .plain piT, val := fun _ => selfM, decl := .pi (fbG K ρ φ ds c).2.2 }, [], [])).1 := by
  rw [List.take_length]; rfl

/-- **`CallStartInvG`, PROVED** (docs/31 D240): the in-place state after the push and the closure's state after its push
are related by the frame property's internal relation under the call's renaming. -/
theorem callStartInvG : CallStartInvG K ρ φ := by
  intro hs ds c selfM piT args s _ hself hg hloc hl hsites hlive hnd hdom hlab hheld
  have hsa : ∀ p l, s.shape p = some l → p ∈ s.positions := fun p l h => (hloc.2.2 p l h).1
  have hlen : (args.map (·.1)).length = (psG K ρ φ ds).length := hdom.1
  have hxl : ((args.map (·.1)).zip (psG K ρ φ ds)).length = args.length := by simp at hlen ⊢; omega
  have hps : ∀ (j : Nat) (d : PiDom), (psG K ρ φ ds)[j]? = some d → ∃ b, (fbG K ρ φ ds c).1[j]? = some b :=
    fun j d hd => (psOf_get _ ds j d hd).imp fun _ h => h.1
  -- membership of the arguments in their binders' types
  have hmemIn : ∀ (j : Nat) (a : Res), args[j]? = some a →
      a.1 ∈ₛ[K.dm.read] (paramBind (fbG K ρ φ ds c).1 (accOf args j) a).ty.m := by
    intro j a ha
    have hj : j < args.length := (List.getElem?_eq_some_iff.1 ha).1
    obtain ⟨a', d, ha', hd, -⟩ := arg_at (ps := psG K ρ φ ds) rfl hlen hj
    rw [ha] at ha'; cases ha'
    obtain ⟨b, hb, hdom'⟩ := psOf_get _ ds j d hd
    have := hdom.2 j a.1 d (by simp [ha]) hd
    rw [hdom', show (args.map (·.1)).take j = accOf args j by simp [accOf, List.map_take]] at this
    rw [(param_corr (ps := psG K ρ φ ds) rfl hlen ha hb).2.2]; exact this
  have hheld' : ∀ (j : Nat) (a : Res) (k : Nat), args[j]? = some a → a.2.label = some k →
      s.heldTy k = (paramBind (fbG K ρ φ ds c).1 (accOf args j) a).ty.m := hheld
  -- the two pushes, characterised
  rw [inStart_fold, clStart_fold]
  obtain ⟨-, hin⟩ := inFold (s := s) (fbG K ρ φ ds c).1 args _ hsa hnd args.length (Nat.le_refl _)
  have hgin := inFold_good K φ (s := s) (fbG K ρ φ ds c).1 args
    { ty := { (selfM, TyS.plain piT).2 with label := none }, val := fun _ => selfM, decl := .pi (fbG K ρ φ ds c).2.2 }
    rfl rfl (.inl hself) hg hloc hnd hlive hmemIn hheld' args.length (Nat.le_refl _)
  obtain ⟨-, hcl⟩ := clFold (fbG K ρ φ ds c) ((args.map (·.1)).zip (psG K ρ φ ds))
    { ty := .plain piT, val := fun _ => selfM, decl := .pi (fbG K ρ φ ds c).2.2 } _ (Nat.le_refl _)
  rw [hxl] at hcl
  have hmemCl : ∀ k x, k < args.length → ((args.map (·.1)).zip (psG K ρ φ ds))[k]? = some x →
      x.1 ∈ₛ[K.dm.read] (clT (fbG K ρ φ ds c) ((args.map (·.1)).zip (psG K ρ φ ds)) k).m := by
    intro k x hk hx
    obtain ⟨a, d, ha, hd, hx'⟩ := arg_at (ps := psG K ρ φ ds) rfl hlen hk
    rw [hx] at hx'; cases hx'
    obtain ⟨b, hb⟩ := hps k d hd
    rw [← (param_corr (ps := psG K ρ φ ds) rfl hlen ha hb).1]; exact hmemIn k a ha
  have hgcl := hcl.good K φ (by rw [hxl]; exact Nat.le_refl _) rfl hself hmemCl
  -- the in-place fold's lower holders
  have hl0 : SState.RInv (fun _ => False) (s.pushFrame.pushBind
      { ty := { (selfM, TyS.plain piT).2 with label := none }, val := fun _ => selfM, decl := .pi (fbG K ρ φ ds c).2.2 }) :=
    SState.pushBind_rinv (PushFrame.rinv_pushFrame hloc) _ selfM rfl
  have hsa₀ : SState.ShapeAt s.pushFrame := (PushFrame.rinv_pushFrame hloc).2.2
  have hfs := fold_start (fbG K ρ φ ds c).1 s (args.take args.length) _ [] [] hl0 (hg.uniq.pushBind
    { ty := { (selfM, TyS.plain piT).2 with label := none }, val := fun _ => selfM, decl := .pi (fbG K ρ φ ds c).2.2 })
    (by simp [SState.pushBind, SState.pushFrame]) rfl rfl
    (fun l hl => (SState.live_pushBind hsa₀ _ l).2 ((PushFrame.live_pushFrame s l).2 hl))
    (fun p l _ hl => ⟨hl, by simp⟩) (fun a' ha' => hlive a' (List.mem_of_mem_take ha'))
  have hlowsh := hfs.2.2.2.2.2.2
  rw [List.take_length] at hin hgin hlowsh ⊢
  generalize (args.foldl (callStep (fbG K ρ φ ds c).1) (s.pushFrame.pushBind
      { ty := { (selfM, TyS.plain piT).2 with label := none }, val := fun _ => selfM,
        decl := .pi (fbG K ρ φ ds c).2.2 }, [])).1 = t at hin hgin hlowsh ⊢
  have htk : ((args.map (·.1)).zip (psG K ρ φ ds)).take args.length = (args.map (·.1)).zip (psG K ρ φ ds) := by
    rw [← hxl, List.take_length]
  rw [htk] at hcl hgcl; rw [List.take_length]
  generalize (((args.map (·.1)).zip (psG K ρ φ ds)).foldl (fixStep (fbG K ρ φ ds c)) (formG.under.pushBind
      { ty := .plain piT, val := fun _ => selfM, decl := .pi (fbG K ρ φ ds c).2.2 }, [], [])).1 = t' at hcl hgcl ⊢
  have hksn : ∀ k ∈ argLabels args, k < s.nextLoan := fun k hk => by
    obtain ⟨a, ha, hak⟩ := List.mem_filterMap.1 hk
    obtain ⟨q, _, hq⟩ := (SState.live_iff s k).1 (hlive a ha k hak)
    exact (hloc.2.2 q k hq).2
  have hrel := startRel (s := s) (ps := psG K ρ φ ds) rfl rfl hps hin hcl ⟨rfl, rfl, rfl, fun _ => rfl⟩ hlen hlab hnd hksn
    hsites hheld'
  have hM : refBefore ((args.map (·.1)).zip (psG K ρ φ ds)) args.length = (argLabels args).length := by
    rw [← argLabels_corr hlen hlab args.length (Nat.le_refl _), List.take_length]
  have htop : t.topIdx = s.env.length := by simp only [SState.topIdx, hin.len]; omega
  have hlive' : ∀ l, t'.Live l ↔ l < (argLabels args).length := fun l => by
    rw [← hM]; exact hcl.live_iff (by rw [hxl]; exact Nat.le_refl _) l
  have hσ : ∀ l, l < (argLabels args).length → callRen (argLabels args) s.nextLoan l ∈ argLabels args := fun l hl => by
    rw [callRen_lt hl]; exact List.getElem_mem hl
  have hnoTop : ∀ m (y : Site), y ∈ t.lent m → y.pos.frameOf ≠ t.topIdx := fun m y hy e => by
    rw [hin.lent] at hy; have := frameOf_lt_of_mem (hsites m y hy); rw [htop] at e; omega
  obtain ⟨F0, h0, -, h0l, -⟩ := hcl.f0
  have hn' : t'.nextLoan = (argLabels args).length := by rw [hcl.next, hM]
  refine frameInv_of hrel (fun p => ?_) (fun p hp => ?_) hgin hgcl ?_ ?_ (fun k _ y hy hyf => absurd hyf (hnoTop k y hy))
    (fun l l' _ hl' _ h' => absurd (hσ l' ((hlive' l').1 hl')) h')
    (fun l _ hl _ h _ _ => absurd (hσ l ((hlive' l).1 hl)) h) (Nat.le_refl _) (by rw [hin.next]; exact callRen_srange _ _)
    (fun m y hy hyf => absurd hyf (hnoTop m y hy)) (fun m y _ hy hyf => absurd hyf (hnoTop m y hy))
    (fun l hl => ?_) (fun l l' _ hl' _ h' => absurd (hσ l' (by rw [← hn']; exact hl')) h')
    (fun l _ hl _ h _ _ => absurd (hσ l (by rw [← hn']; exact hl)) h)
  · -- the closure reads only live labels
    cases p with
    | temp f i => rw [hcl.valAt_temp]; exact FT.const _ _
    | bind f i =>
      cases hb : t'.env[f]?.bind (·.binds[i]?) with
      | none => simp only [SState.valAt, hb]; exact FT.const _ _
      | some b =>
        simp only [SState.valAt, hb]
        rcases hcl.bindAt (by rw [hxl]; exact Nat.le_refl _) hb with ⟨rfl, hi, rfl⟩ | ⟨rfl, rfl, rfl⟩ |
          ⟨k, x, rfl, rfl, hk, hx, rfl⟩
        · intro ψ ψ' e; exact e i ((hcl.live_iff (by rw [hxl]; exact Nat.le_refl _) i).2 hi)
        · exact FT.const _ _
        · exact FT.const _ _
  · -- the closure's frame 1 holds constants
    cases p with
    | temp f i => rw [hcl.valAt_temp]; exact FT.const _ _
    | bind f i =>
      simp only [Pos.frameOf] at hp; subst hp
      cases hb : t'.env[1]?.bind (·.binds[i]?) with
      | none => simp only [SState.valAt, hb]; exact FT.const _ _
      | some b =>
        simp only [SState.valAt, hb]
        rcases hcl.bindAt (by rw [hxl]; exact Nat.le_refl _) hb with ⟨e, -, -⟩ | ⟨-, -, rfl⟩ |
          ⟨k, x, -, -, -, -, rfl⟩
        · cases e
        · exact FT.const _ _
        · exact FT.const _ _
  · -- a cell per parameter label
    have : t'.env.headD {} = F0 := by
      cases e : t'.env with
      | nil => rw [e] at h0; cases h0
      | cons F rest => rw [e] at h0; simp at h0; subst h0; rfl
    rw [this, h0l, hM]; exact Nat.le_refl _
  · -- lending stays well founded: the push moved holders only, and sites stay in the caller's frames
    obtain ⟨rk, hrk⟩ := hl
    refine ⟨rk, fun a b y ha hy hyb => hrk a b y ?_ (by rw [hin.lent] at hy; exact hy) ?_⟩
    · obtain ⟨p, hp, hpa⟩ := (SState.live_iff t a).1 ha
      by_cases hpf : p.frameOf < s.env.length
      · exact (SState.live_iff s a).2 ⟨p, hsa p a (hlowsh p a hpf hpa).1, (hlowsh p a hpf hpa).1⟩
      · have hpE : p.frameOf = s.env.length := by
          have := frameOf_lt_of_mem hp; rw [hin.len] at this; omega
        cases p with
        | temp f i => simp only [Pos.frameOf] at hpE; subst hpE; rw [hin.shapeT] at hpa; cases hpa
        | bind f i =>
          simp only [Pos.frameOf] at hpE; subst hpE
          cases i with
          | zero => rw [hin.shape0] at hpa; cases hpa
          | succ k =>
            by_cases hk : k < args.length
            · obtain ⟨a', ha'⟩ : ∃ a', args[k]? = some a' := ⟨args[k], List.getElem?_eq_getElem hk⟩
              rw [hin.shapeP k a' hk ha'] at hpa
              exact hlive a' (List.mem_of_getElem? ha') a hpa
            · rw [hin.shapeHi (k + 1) (by omega)] at hpa; cases hpa
    · rw [hin.lent] at hy
      have hyf := frameOf_lt_of_mem (hsites a y hy)
      exact (hlowsh y.pos b hyf hyb).1
  · -- every label the closure made is a live one
    have hl' : t'.Live l := (hlive' l).2 (by rw [← hn']; exact hl)
    exact ⟨(hrel.held l hl').2, fun h => absurd (hσ l (by rw [← hn']; exact hl)) h⟩

/-- **`CallStartG`, PROVED**: both halves of the start of a call in place (`frameStart_inStart`, `callStartInvG`). -/
theorem callStartG : CallStartG K ρ φ := callStartG_of K ρ φ (callStartInvG K ρ φ)

end

end Ochr.Meaning.Steps.Form.CallInPlace
