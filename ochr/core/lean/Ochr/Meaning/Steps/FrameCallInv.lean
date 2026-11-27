import Ochr.Meaning.Steps.FrameCall

/-!
# The call clause of the frame property: the internal relation after a call (lead35; docs/31 D221)

The paper's row "A call inside the body" (`18-principles`, `<sec-frame-proof>`; docs/31 D202, D220). `FrameCall` proved the
fixes (`frameRel_mapFix`, `frameRel_callData`, `frameRel_callRefFix`); this file carries the whole internal relation
(`FrameInv`) across `callOfL`, at both of its outcomes, and assembles the clause:
- the arguments' meanings agree, their labels renamed (`renRes`), so the in-place call consumes the images of the
  closure's consumed labels (`refLabels_ren`) and applies the same function to the same meanings;
- a call returning data: the takes and the fixes (`frameRel_callData`), every other clause of `AccInv` because the live
  labels only shrink and the sites stay (`callData_frameInv`);
- a call returning a borrow: the takes, a fresh label on both sides (`σ` sends the closure's to the in-place one,
  `FrameRel.fresh`), the fixes at the fresh label (`frameRel_callRefFix`), the result parked at a fresh temporary
  (`frameRel_park` with no site), then the fresh label lent wherever the consumed labels were (`accInv_setLent`): in place
  that includes caller sites of consumed parameter labels, in the closure their cells, which `FrameRel` compares only in the
  callee's frame. Lending stays well founded because nothing is lent at a temporary of the callee's frame
  (`FrameInv.bsites`), where the fresh label is held.
-/

namespace Ochr.Meaning.Steps.Form.FrameEnd

open Ochr Ochr.Meaning

/-! ## Results renamed -/

/-- A closure result read in place: the same meaning, its label renamed. -/
def renRes (σ : Nat → Nat) (r : Res) : Res := (r.1, { r.2 with label := r.2.label.map σ })

@[simp] theorem renRes_fst (σ : Nat → Nat) (r : Res) : (renRes σ r).1 = r.1 := rfl
@[simp] theorem renRes_label (σ : Nat → Nat) (r : Res) : (renRes σ r).2.label = r.2.label.map σ := rfl
@[simp] theorem renRes_m (σ : Nat → Nat) (r : Res) : (renRes σ r).2.m = r.2.m := rfl

theorem map_fst_renRes (σ : Nat → Nat) (as : List Res) : (as.map (renRes σ)).map (·.1) = as.map (·.1) := by
  simp [List.map_map, Function.comp_def]

/-- The labels at the borrow parameters, renamed: the in-place call consumes the images of the closure's. -/
theorem refLabels_ren (σ : Nat → Nat) : ∀ (as : List Res) (fl : List Bool),
    ((((as.map (renRes σ)).zip fl).filter (·.2)).map (·.1.2.label)) =
      (((as.zip fl).filter (·.2)).map (·.1.2.label)).map (Option.map σ)
  | [], _ => rfl
  | _ :: _, [] => rfl
  | a :: as, b :: fl => by
    cases b with
    | false => simpa using refLabels_ren σ as fl
    | true => simpa using refLabels_ren σ as fl

theorem filterMap_ren (σ : Nat → Nat) (refL : List (Option Nat)) :
    (refL.map (Option.map σ)).filterMap id = (refL.filterMap id).map σ := by
  induction refL with
  | nil => rfl
  | cons l? refL ih => cases l? <;> simp [ih]

theorem map_const_ren (σ : Nat → Nat) {α : Type 3} (x : α) (l : List (Option Nat)) :
    (l.map (Option.map σ)).map (fun _ => x) = l.map (fun _ => x) := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [ih]

theorem agree_renRes {K : RunCtx} {φ : Future} {σ : Nat → Nat} {s₀ : SState} {ks : List Nat} {r r' : Res} {t t' : SState}
    (h : FrameAgreeI K φ σ s₀ ks (some (r, t)) (some (r', t'))) : r = renRes σ r' := by
  obtain ⟨h1, h2, -⟩ := h
  rcases r with ⟨v, R⟩; rcases r' with ⟨v', R'⟩
  simp only at h1 h2; subst h1 h2; rfl

/-! ## The state operations of a call: what they keep -/

theorem headD_len_mapVals (t : SState) (g : Pos → SVal → SVal) :
    ((t.mapVals g).env.headD {}).binds.length = (t.env.headD {}).binds.length := by
  unfold SState.mapVals
  cases t.env with
  | nil => rfl
  | cons fr rest => simp

theorem takeLabel_lent' (t : SState) (l : Nat) : (t.takeLabel l).lent = t.lent := by
  unfold SState.takeLabel; split
  · rename_i r _; show (t.setAt r fun _ => .moved).lent = t.lent; exact setAt_lent _ _ _
  · rfl

theorem takeLabel_nextLoan' (t : SState) (l : Nat) : (t.takeLabel l).nextLoan = t.nextLoan := by
  unfold SState.takeLabel; split
  · rename_i r _; show (t.setAt r fun _ => .moved).nextLoan = t.nextLoan; exact setAt_nextLoan _ _ _
  · rfl

theorem takes_lent : ∀ (C : List Nat) (t : SState), (C.foldl SState.takeLabel t).lent = t.lent
  | [], _ => rfl
  | l :: C, t => by rw [List.foldl_cons, takes_lent C, takeLabel_lent']

theorem takes_nextLoan : ∀ (C : List Nat) (t : SState), (C.foldl SState.takeLabel t).nextLoan = t.nextLoan
  | [], _ => rfl
  | l :: C, t => by rw [List.foldl_cons, takes_nextLoan C, takeLabel_nextLoan']

theorem takes_positions : ∀ (C : List Nat) (t : SState), (C.foldl SState.takeLabel t).positions = t.positions
  | [], _ => rfl
  | l :: C, t => by rw [List.foldl_cons, takes_positions C, SState.takeLabel_positions]

theorem takeLabel_heldTy' (t : SState) (l : Nat) : (t.takeLabel l).heldTy = t.heldTy := by
  unfold SState.takeLabel; split
  · rename_i r _; show (t.setAt r fun _ => .moved).heldTy = t.heldTy; exact setAt_heldTy _ _ _
  · rfl

theorem takeLabel_heldMem' (t : SState) (l : Nat) : (t.takeLabel l).heldMem = t.heldMem := by
  unfold SState.takeLabel; split
  · rename_i r _; show (t.setAt r fun _ => .moved).heldMem = t.heldMem; exact setAt_heldMem _ _ _
  · rfl

theorem takes_heldTy : ∀ (C : List Nat) (t : SState), (C.foldl SState.takeLabel t).heldTy = t.heldTy
  | [], _ => rfl
  | l :: C, t => by rw [List.foldl_cons, takes_heldTy C, takeLabel_heldTy']

theorem takes_heldMem : ∀ (C : List Nat) (t : SState), (C.foldl SState.takeLabel t).heldMem = t.heldMem
  | [], _ => rfl
  | l :: C, t => by rw [List.foldl_cons, takes_heldMem C, takeLabel_heldMem']

theorem mapVals_heldTy (t : SState) (g : Pos → SVal → SVal) : (t.mapVals g).heldTy = t.heldTy := rfl
theorem mapVals_heldMem (t : SState) (g : Pos → SVal → SVal) : (t.mapVals g).heldMem = t.heldMem := rfl

theorem mapVals_lent (t : SState) (g : Pos → SVal → SVal) : (t.mapVals g).lent = t.lent := rfl
theorem mapVals_shape (t : SState) (g : Pos → SVal → SVal) : (t.mapVals g).shape = t.shape := rfl
theorem mapVals_nextLoan (t : SState) (g : Pos → SVal → SVal) : (t.mapVals g).nextLoan = t.nextLoan := rfl

/-- After the takes and fixes of a call, each position reads what it read before, with fixed labels read at given
values (or the constant `moved`, a taken holder; or nothing, off the positions). -/
theorem valAt_takes_fix (t : SState) (C : List Nat) (G : Pos → SVal → SVal) (q : Pos) :
    ((C.foldl SState.takeLabel t).mapVals G).valAt q = G q (t.valAt q) ∨
      ((C.foldl SState.takeLabel t).mapVals G).valAt q = G q (fun _ => .moved) ∨
      ((C.foldl SState.takeLabel t).mapVals G).valAt q = fun _ => .err := by
  by_cases hq : q ∈ (C.foldl SState.takeLabel t).positions
  · rw [SState.valAt_mapVals_of_mem _ _ _ hq]
    rcases SState.takeAll_valAt q C t with e | e <;> rw [e]
    · exact .inl rfl
    · exact .inr (.inl rfl)
  · rw [SState.valAt_mapVals_of_not_mem _ _ _ hq]; exact .inr (.inr rfl)

theorem live_takes_fix {t : SState} {C : List Nat} {G : Pos → SVal → SVal} {y : Nat}
    (h : ((C.foldl SState.takeLabel t).mapVals G).Live y) : t.Live y :=
  SState.takeAll_live_rev C (SState.live_mapVals.1 h)

theorem shape_takes_fix {t : SState} {C : List Nat} {G : Pos → SVal → SVal} {p : Pos} {y : Nat}
    (h : ((C.foldl SState.takeLabel t).mapVals G).shape p = some y) : t.shape p = some y :=
  SState.takeAll_shape_some C h

/-! ## A call returning data -/

section
variable {K : RunCtx} {φ : Future} {σ : Nat → Nat} {s₀ : SState} {ks : List Nat} {s s' : SState}

/-- **The internal relation after a call returning data** (the paper's row "A call inside the body"): the takes and
the fixes keep `FrameRel` (`frameRel_takes`, `frameRel_mapFix`); the live labels only shrink and the sites stay, so the
rest of `AccInv` is inherited; a fixed position of the closure's frame reads what it read but the consumed labels, so
still no parameter label. The goodness of the two states after, and the closure's locality after
(`Strict.callOfLS_rinv`), are hypotheses: the call site has them from the fundamental lemma's operations. -/
theorem callData_frameInv (h : FrameInv K φ σ s₀ ks s s') (hs₀ : FrameStart s₀ ks) (C : List Nat) (F : List (Nat × Sem))
    (hg : Strict.SGood K.dm K.Γ φ (((C.map σ).foldl SState.takeLabel s).mapVals fun _ v φ' => v (φ'.updList (renFix σ F))))
    (hg' : Strict.SGood K.dm K.Γ φ ((C.foldl SState.takeLabel s').mapVals fun _ v φ' => v (φ'.updList F)))
    (hri' : SState.RInv (fun _ => False) ((C.foldl SState.takeLabel s').mapVals fun _ v φ' => v (φ'.updList F))) :
    FrameInv K φ σ s₀ ks (((C.map σ).foldl SState.takeLabel s).mapVals fun _ v φ' => v (φ'.updList (renFix σ F)))
      ((C.foldl SState.takeLabel s').mapVals fun _ v φ' => v (φ'.updList F)) := by
  have hA := h.acc
  have ht := frameRel_takes hs₀ h.srange C hA.rel hA.uniq hA.shape hA.shape'
  have hc : ks.length ≤ (((C.foldl SState.takeLabel s').env.headD {}).binds.length) := by
    rw [headD_len_takes]; exact hA.cells
  have hrel := frameRel_mapFix ht hs₀ hc (fun _ => F) (fun _ l _ _ => h.srange l)
  have hlive' : ∀ y, ((C.foldl SState.takeLabel s').mapVals fun _ v φ' => v (φ'.updList F)).Live y → s'.Live y :=
    fun y hy => live_takes_fix hy
  refine
  { acc :=
    { rel := hrel
      uniq := hg.uniq
      shape := fun p l hp => (hg.acyc.2.2 p l hp).1
      lend := by
        obtain ⟨rk, hrk⟩ := hA.lend
        refine ⟨rk, fun a b y ha hy hb => hrk a b y (live_takes_fix ha) ?_ (shape_takes_fix hb)⟩
        rw [mapVals_lent, takes_lent] at hy; exact hy
      pfill := fun k hk y hy hyf => hA.pfill k hk y (by rw [mapVals_lent, takes_lent] at hy; exact hy) hyf
      held := hg.held
      cells := by rw [headD_len_mapVals]; exact hc
      uniq' := hg'.uniq
      rinv' := hri'
      noParam := fun p hp => by
        rcases valAt_takes_fix s' C (fun _ v φ' => v (φ'.updList F)) p with e | e | e <;> rw [e]
        · exact ((hA.noParam p hp).updList F).mono fun _ hy => hy.1
        · exact ((FT.const _ Sem.moved).updList F).mono fun _ hy => hy.1
        · exact FT.const _ _
      order := fun a b ha hb => hA.order a b (hlive' a ha) (hlive' b hb)
      mono := fun a b ha hb => hA.mono a b (hlive' a ha) (hlive' b hb) }
    good := hg
    good' := hg'
    counter := by
      show s₀.nextLoan ≤ (((C.map σ).foldl SState.takeLabel s)).nextLoan
      rw [takes_nextLoan]; exact h.counter
    srange := h.srange
    bsites := fun m y hy hf => h.bsites m y (by rw [mapVals_lent, takes_lent] at hy; exact hy) hf
    psites := fun m y hm hy hf => by
      rw [SState.positions_mapVals, takes_positions]
      exact h.psites m y (live_takes_fix hm) (by rw [mapVals_lent, takes_lent] at hy; exact hy) hf
    heldAll := fun l hl => by
      rw [mapVals_nextLoan, takes_nextLoan] at hl
      rw [mapVals_heldTy, mapVals_heldTy, takes_heldTy, takes_heldTy, mapVals_heldMem, mapVals_heldMem, takes_heldMem,
        takes_heldMem]
      exact h.heldAll l hl
    orderAll := fun l l' hl hl' => by
      rw [mapVals_nextLoan, takes_nextLoan] at hl hl'; exact h.orderAll l l' hl hl'
    monoAll := fun l l' hl hl' => by
      rw [mapVals_nextLoan, takes_nextLoan] at hl hl'; exact h.monoAll l l' hl hl' }

end

/-! ## A call returning a borrow -/

/-- `callOfL`'s state for a returned borrow, after the takes (`t`): the fresh label `k` (the counter), the fixes `G`
read at it, the result `v` parked at a fresh temporary, lent at `lK`, recorded at its type `T`. -/
noncomputable def refState (t : SState) (G : Pos → SVal → SVal) (v : Sem) (T : TyM) (lK : List Site) (k : Nat) : SState :=
  (((((t.freshLoan.2).mapVals G).pushTempShaped (fun _ => v) k).setLent k lK).setHeldTy k T).setHeldMem k v

/-- The fixes of a returned borrow, read at the fresh label's final content. -/
def refFix {X : Type _} (dec : Sem → Option X) (k : Nat) (A : X → List (Nat × Sem)) (B : List (Nat × Sem)) :
    Pos → SVal → SVal := fun _ w φ' => match dec (φ' k) with
  | some x => w (φ'.updList (A x))
  | none => w (φ'.updList B)

/-- The sites a returned borrow is lent at: wherever the consumed labels were, as fills. -/
def lentOf (t : SState) (C : List Nat) : List Site := (C.flatMap t.lent).map fun x => { x with fill := true }

/-- `refState` is the park with no site, then lent at `lK` (what `accInv_setLent` adds). -/
theorem refState_park (t : SState) (G : Pos → SVal → SVal) (v : Sem) (T : TyM) (lK : List Site) (k : Nat) :
    refState t G v T lK k =
      (park ((t.freshLoan.2).mapVals G) (fun _ => v) k [] T v).setLent k
        ((park ((t.freshLoan.2).mapVals G) (fun _ => v) k [] T v).lent k ++ lK) := by
  unfold refState park
  generalize ((t.freshLoan.2).mapVals G).pushTempShaped (fun _ => v) k = P
  simp only [SState.setLent, SState.setHeldTy, SState.setHeldMem]
  congr 1
  funext n; split <;> simp_all

theorem park_lent_self (t : SState) (v : SVal) (k : Nat) (T : TyM) (m : Sem) : (park t v k [] T m).lent k = [] := by
  simp [park, SState.setLent]

theorem park_lent_ne (t : SState) (v : SVal) {k n : Nat} (T : TyM) (m : Sem) (h : n ≠ k) :
    (park t v k [] T m).lent n = (t.pushTempShaped v k).lent n := by
  simp [park, SState.setLent, h]

theorem pushTempShaped_lent (t : SState) (v : SVal) (k : Nat) : (t.pushTempShaped v k).lent = t.lent := by
  unfold SState.pushTempShaped; dsimp only; split <;> rfl

theorem pushTempShaped_nextLoan (t : SState) (v : SVal) (k : Nat) : (t.pushTempShaped v k).nextLoan = t.nextLoan := by
  unfold SState.pushTempShaped; dsimp only; split <;> rfl

theorem pushTempShaped_heldTy (t : SState) (v : SVal) (k : Nat) : (t.pushTempShaped v k).heldTy = t.heldTy := by
  unfold SState.pushTempShaped; dsimp only; split <;> rfl

theorem pushTempShaped_heldMem (t : SState) (v : SVal) (k : Nat) : (t.pushTempShaped v k).heldMem = t.heldMem := by
  unfold SState.pushTempShaped; dsimp only; split <;> rfl

theorem setLent_heldTy' (t : SState) (l : Nat) (xs : List Site) : (t.setLent l xs).heldTy = t.heldTy := rfl
theorem setLent_heldMem' (t : SState) (l : Nat) (xs : List Site) : (t.setLent l xs).heldMem = t.heldMem := rfl

theorem park_heldTy (t : SState) (v : SVal) (l : Nat) (xs : List Site) (T : TyM) (m : Sem) (n : Nat) :
    (park t v l xs T m).heldTy n = if n = l then T else t.heldTy n := by
  show (if n = l then T else ((t.pushTempShaped v l).setLent l xs).heldTy n) = _
  rw [setLent_heldTy', pushTempShaped_heldTy]

theorem park_heldMem (t : SState) (v : SVal) (l : Nat) (xs : List Site) (T : TyM) (m : Sem) (n : Nat) :
    (park t v l xs T m).heldMem n = if n = l then m else t.heldMem n := by
  show (if n = l then m else (((t.pushTempShaped v l).setLent l xs).setHeldTy l T).heldMem n) = _
  rw [SState.setHeldTy_heldMem, setLent_heldMem', pushTempShaped_heldMem]

theorem park_nextLoan (t : SState) (v : SVal) (l : Nat) (xs : List Site) (T : TyM) (m : Sem) :
    (park t v l xs T m).nextLoan = t.nextLoan := pushTempShaped_nextLoan t v l

theorem headD_len_pushTempShaped (t : SState) (v : SVal) (k : Nat) (h : t.topIdx ≠ 0) :
    ((t.pushTempShaped v k).env.headD {}).binds.length = (t.env.headD {}).binds.length := by
  have e : (t.pushTempShaped v k).env = (t.pushTemp v).env := by
    unfold SState.pushTempShaped; dsimp only; split <;> rfl
  rw [e, show (t.pushTemp v).env = (modTop t fun fr => { fr with temps := fr.temps ++ [v] }).env from rfl,
    modTop_headD _ _ h]

/-- After the takes, the fresh label and the fixes, each position reads what it read before with the fixes applied, or
the fixes on `moved` (a taken holder), or nothing (off the positions). -/
theorem valAt_takes_fresh_fix (t : SState) (C : List Nat) (G : Pos → SVal → SVal) (q : Pos) :
    (((C.foldl SState.takeLabel t).freshLoan.2).mapVals G).valAt q = G q (t.valAt q) ∨
      (((C.foldl SState.takeLabel t).freshLoan.2).mapVals G).valAt q = G q (fun _ => .moved) ∨
      (((C.foldl SState.takeLabel t).freshLoan.2).mapVals G).valAt q = fun _ => .err :=
  valAt_takes_fix t C G q

theorem shapeAt_takes : ∀ (C : List Nat) {t : SState}, ShapeAt t → ShapeAt (C.foldl SState.takeLabel t)
  | [], _, h => h
  | l :: C, _, h => shapeAt_takes C (shapeAt_takeLabel h l)

theorem shape_park {t : SState} {F : SFrame} (hF : t.env.getLast? = some F) (v : SVal) (k : Nat) (xs : List Site)
    (T : TyM) (m : Sem) (q : Pos) :
    (park t v k xs T m).shape q = if q = .temp t.topIdx F.temps.length then some k else t.shape q := by
  rw [park_eq t v k xs T m hF]

theorem live_park_cases {t : SState} {F : SFrame} (hF : t.env.getLast? = some F) {v : SVal} {k : Nat}
    {xs : List Site} {T : TyM} {m : Sem} {y : Nat} (h : (park t v k xs T m).Live y) :
    y = k ∨ ∃ q, t.shape q = some y := by
  obtain ⟨q, -, hq⟩ := (SState.live_iff _ y).1 h
  rw [shape_park hF] at hq
  split at hq
  · cases hq; exact .inl rfl
  · exact .inr ⟨q, hq⟩

/-- A fixed meaning reads the fresh label and what the old one read. -/
theorem ft_refFix {S : Nat → Prop} {w : SVal} (hw : Ochr.Meaning.FT S w) {X : Type _} (dec : Sem → Option X) {k : Nat}
    (hk : S k) (A : X → List (Nat × Sem)) (B : List (Nat × Sem)) (p : Pos) :
    Ochr.Meaning.FT S (refFix dec k A B p w) := fun ψ ψ' e => by
  simp only [refFix]
  rw [e k hk]
  cases dec (ψ' k) with
  | some x => exact (hw.updList (A x)) ψ ψ' (fun y hy => e y hy.1)
  | none => exact (hw.updList B) ψ ψ' (fun y hy => e y hy.1)

theorem refState_lent (t : SState) (G : Pos → SVal → SVal) (v : Sem) (T : TyM) (lK : List Site) (k m : Nat) :
    (refState t G v T lK k).lent m = if m = k then lK else t.lent m := by
  unfold refState
  rw [SState.setHeldMem_lent, SState.setHeldTy_lent]
  show (if m = k then lK else _) = _
  split
  · rfl
  · rw [pushTempShaped_lent]; rfl

section
variable {K : RunCtx} {φ : Future} {σ : Nat → Nat} {s₀ : SState} {ks : List Nat} {s s' : SState}

/-- **The internal relation after a call returning a borrow** (the paper's row "A call inside the body", with (O7)): the
takes (`frameRel_takes`), the fresh labels, which correspond (`FrameRel.fresh`), the fixes read at the fresh label
(`frameRel_callRefFix`), the result parked at a fresh temporary with no site (`frameRel_park`), then lent wherever the
consumed labels were (`accInv_setLent`). Lending stays well founded: nothing is lent at a temporary of the callee's frame
(`FrameInv.bsites`), where the fresh label is held, and the fresh label is ranked below every other. The result's label
is parked (`ResAtTemp`). The goodness of both states after, and the closure's locality after, are hypotheses (the
fundamental lemma's call operations give them). -/
theorem callRef_frameInv (h : FrameInv K φ σ s₀ ks s s') (hs₀ : FrameStart s₀ ks) (C : List Nat)
    (hlive : ∀ l ∈ C, s'.Live l)
    {X : Type _} (dec : Sem → Option X) (A : X → List (Nat × Sem)) (B : List (Nat × Sem)) (v : Sem) (T : TyM)
    (hg : Strict.SGood K.dm K.Γ φ (refState ((C.map σ).foldl SState.takeLabel s)
      (refFix dec (σ s'.nextLoan) (fun x => renFix σ (A x)) (renFix σ B)) v T (lentOf ((C.map σ).foldl SState.takeLabel s).freshLoan.2 (C.map σ)) (σ s'.nextLoan)))
    (hg' : Strict.SGood K.dm K.Γ φ (refState (C.foldl SState.takeLabel s') (refFix dec s'.nextLoan A B) v T
      (lentOf (C.foldl SState.takeLabel s').freshLoan.2 C) s'.nextLoan))
    (hri' : SState.RInv (fun _ => False) (refState (C.foldl SState.takeLabel s') (refFix dec s'.nextLoan A B) v T
      (lentOf (C.foldl SState.takeLabel s').freshLoan.2 C) s'.nextLoan)) :
    FrameInv K φ σ s₀ ks
      (refState ((C.map σ).foldl SState.takeLabel s)
        (refFix dec (σ s'.nextLoan) (fun x => renFix σ (A x)) (renFix σ B)) v T (lentOf ((C.map σ).foldl SState.takeLabel s).freshLoan.2 (C.map σ)) (σ s'.nextLoan))
      (refState (C.foldl SState.takeLabel s') (refFix dec s'.nextLoan A B) v T (lentOf (C.foldl SState.takeLabel s').freshLoan.2 C) s'.nextLoan) ∧
    (ResAtTemp s₀ (refState ((C.map σ).foldl SState.takeLabel s)
        (refFix dec (σ s'.nextLoan) (fun x => renFix σ (A x)) (renFix σ B)) v T (lentOf ((C.map σ).foldl SState.takeLabel s).freshLoan.2 (C.map σ)) (σ s'.nextLoan))
      (some (σ s'.nextLoan)) ∧
      ResDead (refState (C.foldl SState.takeLabel s') (refFix dec s'.nextLoan A B) v T
        (lentOf (C.foldl SState.takeLabel s').freshLoan.2 C) s'.nextLoan) (some s'.nextLoan)) := by
  have e1 : lentOf ((C.map σ).foldl SState.takeLabel s).freshLoan.2 (C.map σ) = lentOf s (C.map σ) := by
    unfold lentOf; rw [show (((C.map σ).foldl SState.takeLabel s).freshLoan.2).lent = s.lent from takes_lent _ _]
  have e2 : lentOf (C.foldl SState.takeLabel s').freshLoan.2 C = lentOf s' C := by
    unfold lentOf; rw [show ((C.foldl SState.takeLabel s').freshLoan.2).lent = s'.lent from takes_lent _ _]
  rw [e1] at hg ⊢; rw [e2] at hg' hri' ⊢
  have hA := h.acc
  have hk : σ s'.nextLoan = s.nextLoan := by simpa using hA.rel.fresh 0
  have hkks : σ s'.nextLoan ∉ ks := fun hm => by
    have := hs₀.ks_lt _ hm; have := h.counter; omega
  -- the takes, the fresh labels, the fixes
  have ht := frameRel_takes hs₀ h.srange C hA.rel hA.uniq hA.shape hA.shape'
  have hf := (frameRel_freshLoan ht).2
  have hc : ks.length ≤ ((((C.foldl SState.takeLabel s').freshLoan.2).env.headD {}).binds.length) := by
    show ks.length ≤ (((C.foldl SState.takeLabel s').env.headD {}).binds.length)
    rw [headD_len_takes]; exact hA.cells
  have hfix : FrameRel σ s₀ ks (((C.map σ).foldl SState.takeLabel s).freshLoan.2.mapVals
        (refFix dec (σ s'.nextLoan) (fun x => renFix σ (A x)) (renFix σ B)))
      ((C.foldl SState.takeLabel s').freshLoan.2.mapVals (refFix dec s'.nextLoan A B)) :=
    frameRel_callRefFix hf hs₀ hc h.srange dec s'.nextLoan A B
  have hsh3 : ∀ q x, (((C.map σ).foldl SState.takeLabel s).freshLoan.2.mapVals
      (refFix dec (σ s'.nextLoan) (fun x => renFix σ (A x)) (renFix σ B))).shape q = some x → s.shape q = some x :=
    fun q x hq => SState.takeAll_shape_some _ hq
  have hsh3' : ∀ q x, ((C.foldl SState.takeLabel s').freshLoan.2.mapVals (refFix dec s'.nextLoan A B)).shape q = some x →
      s'.shape q = some x :=
    fun q x hq => SState.takeAll_shape_some _ hq
  have hlent3 : (((C.map σ).foldl SState.takeLabel s).freshLoan.2.mapVals
      (refFix dec (σ s'.nextLoan) (fun x => renFix σ (A x)) (renFix σ B))).lent = s.lent := takes_lent _ _
  have hnext3 : (((C.map σ).foldl SState.takeLabel s).freshLoan.2.mapVals
      (refFix dec (σ s'.nextLoan) (fun x => renFix σ (A x)) (renFix σ B))).nextLoan = s.nextLoan + 1 := by
    show ((C.map σ).foldl SState.takeLabel s).nextLoan + 1 = _; rw [takes_nextLoan]
  have hsa3' : ShapeAt ((C.foldl SState.takeLabel s').freshLoan.2.mapVals (refFix dec s'.nextLoan A B)) :=
    fun p l hp => by rw [SState.positions_mapVals]; exact shapeAt_takes C hA.shape' p l hp
  have hnoP3 : ∀ p, p.frameOf = 1 →
      Ochr.Meaning.FT (fun l => σ l ∉ ks) (((C.foldl SState.takeLabel s').freshLoan.2.mapVals
        (refFix dec s'.nextLoan A B)).valAt p) := fun p hp => by
    rcases valAt_takes_fresh_fix s' C (refFix dec s'.nextLoan A B) p with e | e | e <;> rw [e]
    · exact ft_refFix (hA.noParam p hp) dec hkks A B p
    · exact ft_refFix (FT.const _ _) dec hkks A B p
    · exact FT.const _ _
  have hpos3 : ∀ q ∈ s.positions, q ∈ (((C.map σ).foldl SState.takeLabel s).freshLoan.2.mapVals
      (refFix dec (σ s'.nextLoan) (fun x => renFix σ (A x)) (renFix σ B))).positions := fun q hq => by
    rw [SState.positions_mapVals]; show q ∈ ((C.map σ).foldl SState.takeLabel s).positions
    rw [takes_positions]; exact hq
  have hheld3 : (((C.map σ).foldl SState.takeLabel s).freshLoan.2.mapVals
      (refFix dec (σ s'.nextLoan) (fun x => renFix σ (A x)) (renFix σ B))).heldTy = s.heldTy := takes_heldTy _ _
  have hmem3 : (((C.map σ).foldl SState.takeLabel s).freshLoan.2.mapVals
      (refFix dec (σ s'.nextLoan) (fun x => renFix σ (A x)) (renFix σ B))).heldMem = s.heldMem := takes_heldMem _ _
  have hheld3' : ((C.foldl SState.takeLabel s').freshLoan.2.mapVals (refFix dec s'.nextLoan A B)).heldTy = s'.heldTy :=
    takes_heldTy _ _
  have hmem3' : ((C.foldl SState.takeLabel s').freshLoan.2.mapVals (refFix dec s'.nextLoan A B)).heldMem = s'.heldMem :=
    takes_heldMem _ _
  have hnext3' : ((C.foldl SState.takeLabel s').freshLoan.2.mapVals (refFix dec s'.nextLoan A B)).nextLoan =
      s'.nextLoan + 1 := by
    show (C.foldl SState.takeLabel s').nextLoan + 1 = _; rw [takes_nextLoan]
  have hc3 : ks.length ≤ ((((C.foldl SState.takeLabel s').freshLoan.2.mapVals
      (refFix dec s'.nextLoan A B)).env.headD {}).binds.length) := by rw [headD_len_mapVals]; exact hc
  simp only [refState_park] at hg hg' hri' ⊢
  generalize ((C.map σ).foldl SState.takeLabel s).freshLoan.2.mapVals
    (refFix dec (σ s'.nextLoan) (fun x => renFix σ (A x)) (renFix σ B)) = t3 at hfix hsh3 hlent3 hnext3 hpos3 hheld3 hmem3 hg ⊢
  generalize (C.foldl SState.takeLabel s').freshLoan.2.mapVals (refFix dec s'.nextLoan A B) = t3'
    at hfix hsh3' hsa3' hnoP3 hc3 hheld3' hmem3' hnext3' hg' hri' ⊢
  -- the parked results, with no site
  obtain ⟨F, F', hF, hF', hTR⟩ := top_rel hfix
  have htop3 : t3.topIdx = s₀.topIdx := topIdx_eq hfix
  have htop3' : t3'.topIdx = 1 := topIdx_cl hfix
  have hnot : ∀ p, t3.shape p ≠ some (σ s'.nextLoan) := fun p hp => by
    have := (h.good.acyc.2.2 p _ (hsh3 p _ hp)).2; rw [hk] at this; omega
  have hnot' : ∀ p, t3'.shape p ≠ some s'.nextLoan := fun p hp => by
    have := (h.good'.acyc.2.2 p _ (hsh3' p _ hp)).2; omega
  have hpark := frameRel_park hfix hsa3' (v := fun _ => v) (v' := fun _ => v) (fun _ => rfl) hnot hnot' (xs := [])
    (fun _ h => by cases h) T v (h.srange _)
  have notTemp : ∀ a (y : Site), y ∈ s.lent a → ∀ j, y.pos ≠ .temp s₀.topIdx j := fun a y hy j e => by
    obtain ⟨i, hi⟩ := h.bsites a y hy (by rw [e]; rfl)
    rw [e] at hi; cases hi
  have liveS' : ∀ q a, t3'.shape q = some a → s'.Live a := fun q a hq =>
    (SState.live_iff s' a).2 ⟨q, hA.shape' q a (hsh3' q a hq), hsh3' q a hq⟩
  have hP : AccInv K σ s₀ ks (park t3 (fun _ => v) (σ s'.nextLoan) [] T v) (park t3' (fun _ => v) s'.nextLoan [] T v) :=
  { rel := hpark
    uniq := hg.uniq
    shape := fun p l hp => (hg.acyc.2.2 p l hp).1
    lend := by
      obtain ⟨rk, hrk⟩ := hA.lend
      refine ⟨rk, fun a b y ha hy hb => ?_⟩
      have hak : a ≠ σ s'.nextLoan := by rintro rfl; rw [park_lent_self] at hy; cases hy
      rw [park_lent_ne _ _ _ _ hak, pushTempShaped_lent, hlent3] at hy
      rw [shape_park hF] at hb
      split at hb
      · rename_i e; exact absurd (e.trans (by rw [htop3])) (notTemp a y hy _)
      · rcases live_park_cases hF ha with e | ⟨q, hq⟩
        · exact absurd e hak
        · exact hrk a b y ((SState.live_iff s a).2 ⟨q, hA.shape q a (hsh3 q a hq), hsh3 q a hq⟩) hy (hsh3 _ _ hb)
    pfill := fun k0 hk0 y hy hyf => by
      have hne : k0 ≠ σ s'.nextLoan := fun e => hkks (e ▸ hk0)
      rw [park_lent_ne _ _ _ _ hne, pushTempShaped_lent, hlent3] at hy
      exact hA.pfill k0 hk0 y hy hyf
    held := hg.held
    cells := by
      show ks.length ≤ ((t3'.pushTempShaped (fun _ => v) s'.nextLoan).env.headD {}).binds.length
      rw [headD_len_pushTempShaped _ _ _ (by rw [htop3']; omega)]; exact hc3
    uniq' := hg'.uniq
    rinv' := hri'
    noParam := fun p hp => by
      show Ochr.Meaning.FT _ ((t3'.pushTempShaped (fun _ => v) s'.nextLoan).valAt p)
      rw [SState.valAt_pushTempShaped]
      rcases SState.valAt_pushTemp t3' (fun _ => v) p with e | e <;> rw [e]
      · exact hnoP3 p hp
      · exact FT.const _ _
    order := fun a b ha hb hak hbk => by
      rcases live_park_cases hF' ha with rfl | ⟨q, hq⟩
      · exact absurd hak hkks
      rcases live_park_cases hF' hb with rfl | ⟨q', hq'⟩
      · exact (h.good'.acyc.2.2 q a (hsh3' q a hq)).2
      · exact hA.order a b (liveS' q a hq) (liveS' q' b hq') hak hbk
    mono := fun a b ha hb hak hbk hab => by
      rcases live_park_cases hF' ha with rfl | ⟨q, hq⟩
      · rcases live_park_cases hF' hb with rfl | ⟨q', hq'⟩
        · omega
        · have := (h.good'.acyc.2.2 q' b (hsh3' q' b hq')).2; omega
      rcases live_park_cases hF' hb with rfl | ⟨q', hq'⟩
      · rw [hk]
        obtain ⟨p, -, hps⟩ := (SState.live_iff s _).1 (live_img hA.rel hA.shape (liveS' q a hq))
        exact (h.good.acyc.2.2 p _ hps).2
      · exact hA.mono a b (liveS' q a hq) (liveS' q' b hq') hak hbk hab }
  -- the fresh label lent wherever the consumed labels were
  have hheld : ∀ l ∈ C, ∃ p, s.shape p = some (σ l) := fun l hl => by
    obtain ⟨p, -, hp⟩ := (SState.live_iff s _).1 (live_img hA.rel hA.shape (hlive l hl)); exact ⟨p, hp⟩
  have hys : ∀ x : Site, x.pos.frameOf = s₀.topIdx → (x ∈ lentOf s (C.map σ) ↔ upSite ks.length x ∈ lentOf s' C) := by
    intro x hx
    simp only [lentOf, List.mem_map, List.mem_flatMap]
    constructor
    · rintro ⟨y, ⟨_, ⟨l, hl, rfl⟩, hy⟩, rfl⟩
      exact ⟨upSite ks.length y, ⟨l, hl, (hA.rel.lentTop l y hx (hheld l hl)).1 hy⟩, rfl⟩
    · rintro ⟨y', ⟨l, hl, hy'⟩, e⟩
      obtain ⟨yp, yπ, yf⟩ := y'
      obtain ⟨xp, xπ, xf⟩ := x
      simp only [upSite, Site.mk.injEq] at e
      obtain ⟨rfl, rfl, rfl⟩ := e
      exact ⟨⟨xp, yπ, yf⟩, ⟨σ l, ⟨l, hl, rfl⟩, (hA.rel.lentTop l ⟨xp, yπ, yf⟩ hx (hheld l hl)).2 hy'⟩, rfl⟩
  have hys' : ∀ x ∈ lentOf s' C, (∃ p, p.frameOf = s₀.topIdx ∧ x.pos = upPos ks.length p) ∨
      ∃ i, i < ks.length ∧ x.pos = .bind 0 i := fun x hx => by
    simp only [lentOf, List.mem_map, List.mem_flatMap] at hx
    obtain ⟨y, ⟨l, -, hy⟩, rfl⟩ := hx
    exact hA.rel.lentCl l y hy
  have hcall : ∀ p, p.frameOf < s₀.topIdx → s₀.shape p ≠ some (σ s'.nextLoan) := fun p hp hs => by
    obtain ⟨-, hlt⟩ := hs₀.callerHeld p _ hp hs; have := h.counter; rw [hk] at hlt; omega
  have hsitesK : ∀ y ∈ lentOf s (C.map σ), ∃ a, ∃ z ∈ s.lent a, z.pos = y.pos := fun y hy => by
    simp only [lentOf, List.mem_map, List.mem_flatMap] at hy
    obtain ⟨z, ⟨a, -, hz⟩, rfl⟩ := hy
    exact ⟨a, z, hz, rfl⟩
  have hshP : ∀ (y : Site) a, y ∈ s.lent a → (park t3 (fun _ => v) (σ s'.nextLoan) [] T v).shape y.pos ≠
      some (σ s'.nextLoan) := fun y a hy hs => by
    rw [shape_park hF] at hs
    split at hs
    · rename_i e; exact notTemp a y hy _ (e.trans (by rw [htop3]))
    · exact hnot _ hs
  have hS := accInv_setLent hP s'.nextLoan (lentOf s (C.map σ)) (lentOf s' C) hys hys' hcall
    (fun hm => absurd hm hkks)
    (fun _ a y _ hy hs => by
      have hak : a ≠ σ s'.nextLoan := by rintro rfl; rw [park_lent_self] at hy; cases hy
      rw [park_lent_ne _ _ _ _ hak, pushTempShaped_lent, hlent3] at hy
      exact hshP y a hy hs)
    (fun _ y hy hs => by
      obtain ⟨a, z, hz, e⟩ := hsitesK y hy
      rw [← e] at hs; exact hshP z a hz hs)
  refine ⟨{ acc := hS, good := hg, good' := hg', counter := ?_, srange := h.srange, bsites := ?_, psites := ?_,
             heldAll := ?_, orderAll := ?_, monoAll := ?_ }, ?_, ?_⟩
  · show s₀.nextLoan ≤ (t3.pushTempShaped (fun _ => v) (σ s'.nextLoan)).nextLoan
    rw [pushTempShaped_nextLoan, hnext3]; have := h.counter; omega
  · intro m y hy hf
    simp only [SState.setLent] at hy
    split at hy
    · rw [park_lent_self, List.nil_append] at hy
      obtain ⟨a, z, hz, e⟩ := hsitesK y hy
      rw [← e] at hf ⊢; exact h.bsites a z hz hf
    · rename_i hne
      rw [park_lent_ne _ _ _ _ hne, pushTempShaped_lent, hlent3] at hy
      exact h.bsites m y hy hf
  · intro m y hm hy hf
    have hposP : ∀ q ∈ s.positions, q ∈ (park t3 (fun _ => v) (σ s'.nextLoan) [] T v).positions := fun q hq => by
      show q ∈ (t3.pushTempShaped (fun _ => v) (σ s'.nextLoan)).positions
      rw [SState.positions_pushTempShaped]; exact SState.mem_positions_pushTemp _ _ (hpos3 q hq)
    show y.pos ∈ (park t3 (fun _ => v) (σ s'.nextLoan) [] T v).positions
    simp only [SState.setLent] at hy
    split at hy
    · rw [park_lent_self, List.nil_append] at hy
      simp only [lentOf, List.mem_map, List.mem_flatMap] at hy
      obtain ⟨z, ⟨_, ⟨l, hl, rfl⟩, hz⟩, rfl⟩ := hy
      exact hposP _ (h.psites _ z (live_img hA.rel hA.shape (hlive l hl)) hz hf)
    · rename_i hne
      rw [park_lent_ne _ _ _ _ hne, pushTempShaped_lent, hlent3] at hy
      have hm' : (park t3 (fun _ => v) (σ s'.nextLoan) [] T v).Live m := hm
      rcases live_park_cases hF hm' with e | ⟨q, hq⟩
      · exact absurd e hne
      · exact hposP _ (h.psites m y ((SState.live_iff s m).2 ⟨q, hA.shape q m (hsh3 q m hq), hsh3 q m hq⟩) hy hf)
  · intro l hl
    rw [SState.setLent_nextLoan, park_nextLoan, hnext3'] at hl
    rw [setLent_heldTy', setLent_heldTy', setLent_heldMem', setLent_heldMem', park_heldTy, park_heldTy, park_heldMem,
      park_heldMem, hheld3, hheld3', hmem3, hmem3']
    by_cases e : l = s'.nextLoan
    · subst e; simp
    · have e' : σ l ≠ σ s'.nextLoan := fun h' => e (hA.rel.inj _ _ h')
      rw [if_neg e', if_neg e, if_neg e', if_neg e]
      exact h.heldAll l (by omega)
  · intro l l' hl hl' hlk hl'k
    rw [SState.setLent_nextLoan, park_nextLoan, hnext3'] at hl hl'
    by_cases e : l = s'.nextLoan
    · subst e; exact absurd hlk hkks
    by_cases e' : l' = s'.nextLoan
    · omega
    · exact h.orderAll l l' (by omega) (by omega) hlk hl'k
  · intro l l' hl hl' hlk hl'k hll
    rw [SState.setLent_nextLoan, park_nextLoan, hnext3'] at hl hl'
    by_cases e' : l' = s'.nextLoan
    · subst e'; rw [hk]; exact sigma_lt hA.rel (by omega)
    · exact h.monoAll l l' (by omega) (by omega) hlk hl'k hll
  · intro k0 e
    cases e
    have hsh : (park t3 (fun _ => v) (σ s'.nextLoan) [] T v).shape (.temp s₀.topIdx F.temps.length) =
        some (σ s'.nextLoan) := by
      rw [shape_park hF, if_pos (by rw [htop3])]
    exact ⟨fun _ => ⟨F.temps.length, hsh⟩, fun hd => absurd ((SState.live_iff _ _).2 ⟨_, (hg.acyc.2.2 _ _ hsh).1, hsh⟩) hd⟩
  · intro k0 e
    cases e
    have hsh' : (park t3' (fun _ => v) s'.nextLoan [] T v).shape (.temp t3'.topIdx F'.temps.length) = some s'.nextLoan := by
      rw [shape_park hF', if_pos rfl]
    refine ⟨?_, fun hd => absurd ((SState.live_iff _ _).2 ⟨_, (hg'.acyc.2.2 _ _ hsh').1, hsh'⟩) hd⟩
    rw [SState.setLent_nextLoan, park_nextLoan, hnext3']; omega

end

section
variable {K : RunCtx} {φ : Future} {σ : Nat → Nat} {s₀ : SState} {ks : List Nat} {s s' : SState}

/-- `callRef_frameInv` for fixes given as any functions equal to the fixes (`callOfL` writes them with its own `match`). -/
theorem callRef_frameInv' (h : FrameInv K φ σ s₀ ks s s') (hs₀ : FrameStart s₀ ks) (C : List Nat)
    (hlive : ∀ l ∈ C, s'.Live l)
    {X : Type _} (dec : Sem → Option X) (A : X → List (Nat × Sem)) (B : List (Nat × Sem)) (v : Sem) (T : TyM)
    (G G' : Pos → SVal → SVal) (hG : G = refFix dec (σ s'.nextLoan) (fun x => renFix σ (A x)) (renFix σ B))
    (hG' : G' = refFix dec s'.nextLoan A B)
    (hg : Strict.SGood K.dm K.Γ φ (refState ((C.map σ).foldl SState.takeLabel s) G v T
      (lentOf ((C.map σ).foldl SState.takeLabel s).freshLoan.2 (C.map σ)) (σ s'.nextLoan)))
    (hg' : Strict.SGood K.dm K.Γ φ (refState (C.foldl SState.takeLabel s') G' v T
      (lentOf (C.foldl SState.takeLabel s').freshLoan.2 C) s'.nextLoan))
    (hri' : SState.RInv (fun _ => False) (refState (C.foldl SState.takeLabel s') G' v T
      (lentOf (C.foldl SState.takeLabel s').freshLoan.2 C) s'.nextLoan)) :
    FrameInv K φ σ s₀ ks
      (refState ((C.map σ).foldl SState.takeLabel s) G v T
        (lentOf ((C.map σ).foldl SState.takeLabel s).freshLoan.2 (C.map σ)) (σ s'.nextLoan))
      (refState (C.foldl SState.takeLabel s') G' v T (lentOf (C.foldl SState.takeLabel s').freshLoan.2 C) s'.nextLoan) ∧
    (ResAtTemp s₀ (refState ((C.map σ).foldl SState.takeLabel s) G v T
        (lentOf ((C.map σ).foldl SState.takeLabel s).freshLoan.2 (C.map σ)) (σ s'.nextLoan))
      (some (σ s'.nextLoan)) ∧
      ResDead (refState (C.foldl SState.takeLabel s') G' v T (lentOf (C.foldl SState.takeLabel s').freshLoan.2 C)
        s'.nextLoan) (some s'.nextLoan)) := by
  subst hG hG'
  exact callRef_frameInv h hs₀ C hlive dec A B v T hg hg' hri'

end

/-! ## A call, at a level -/

section
variable {K : RunCtx} {φ : Future} {σ : Nat → Nat} {s₀ : SState} {ks : List Nat} {s s' : SState}

/-- **A call at a level, across the internal relation** (the paper's row "A call inside the body"): the in-place call is
applied to the closure's arguments with their labels renamed; both apply the same function to the same meanings
(`applyFnL`), and the states after are related by `callData_frameInv` or `callRef_frameInv`. Hypotheses: every consumed
label is live in the closure (the strict test `BorrowArgsTyped`), and both states after are good (`Strict.callOfS_sgood`). -/
theorem callOfL_agree.{u} (L : Lvl.{u}) {Cd : Type u} (tel : Tel L.Code PUnit Cd) (fv : Sem) (args : List Res)
    (h : FrameInv K φ σ s₀ ks s s') (hs₀ : FrameStart s₀ ks)
    (hlive : ∀ l, some l ∈ (((args.zip (telRefsL L tel (args.map (·.1)))).filter (·.2)).map (·.1.2.label)) → s'.Live l)
    (hg : ∀ r u, callOfL L tel fv (args.map (renRes σ)) s = some (r, u) → Strict.SGood K.dm K.Γ φ u)
    (hg' : ∀ r u, callOfL L tel fv args s' = some (r, u) → Strict.SGood K.dm K.Γ φ u) :
    FrameAgreeI K φ σ s₀ ks (callOfL L tel fv (args.map (renRes σ)) s) (callOfL L tel fv args s') := by
  have hri' : ∀ r u, callOfL L tel fv args s' = some (r, u) → SState.RInv (fun _ => False) u :=
    fun r u hu => Strict.callOfLS_rinv L tel fv args h.acc.rinv' hu
  unfold callOfL at hg hg' hri' ⊢
  dsimp only at hg hg' hri' ⊢
  simp only [map_fst_renRes, refLabels_ren] at hg ⊢
  generalize (((args.zip (telRefsL L tel (args.map (·.1)))).filter (·.2)).map (·.1.2.label)) = refL
    at hlive hg hg' hri' ⊢
  have hlive' : ∀ l ∈ refL.filterMap id, s'.Live l := fun l hl => hlive l (by
    obtain ⟨a, ha, e⟩ := List.mem_filterMap.mp hl
    simp only [id] at e; subst e; exact ha)
  have hfst : ∀ t : SState, t.freshLoan.1 = t.nextLoan := fun _ => rfl
  have hk : σ s'.nextLoan = s.nextLoan := by simpa using h.acc.rel.fresh 0
  simp only [filterMap_ren, fixes_ren, map_const_ren, hfst, takes_nextLoan, ← hk] at hg hg' hri' ⊢
  cases happ : applyFnL L tel fv (args.map (·.1)) with
  | none => first | trivial | (simp only; trivial)
  | some res =>
    cases res with
    | data r T finals =>
      simp only [happ] at hg hg' hri' ⊢
      exact ⟨rfl, rfl, callData_frameInv h hs₀ _ _ (hg _ _ rfl) (hg' _ _ rfl) (hri' _ _ rfl), ⟨fun _ e => (by cases e),
        fun _ e => by cases e⟩⟩
    | ref U c fwd back =>
      simp only [happ] at hg hg' hri' ⊢
      refine ⟨rfl, rfl, callRef_frameInv' h hs₀ (refL.filterMap id) hlive' (L.dec c)
        (fun x => (refL.zip (back x)).filterMap fun lf => lf.1.map (·, lf.2))
        ((refL.zip (refL.map fun _ => Sem.moved)).filterMap fun lf => lf.1.map (·, lf.2)) (L.enc c fwd) (L.toTy c)
        _ _ ?_ ?_ (hg _ _ rfl) (hg' _ _ rfl) (hri' _ _ rfl) |>.1,
        callRef_frameInv' h hs₀ (refL.filterMap id) hlive' (L.dec c)
        (fun x => (refL.zip (back x)).filterMap fun lf => lf.1.map (·, lf.2))
        ((refL.zip (refL.map fun _ => Sem.moved)).filterMap fun lf => lf.1.map (·, lf.2)) (L.enc c fwd) (L.toTy c)
        _ _ ?_ ?_ (hg _ _ rfl) (hg' _ _ rfl) (hri' _ _ rfl) |>.2⟩ <;>
      · funext p w φ'; unfold refFix; split <;> (rename_i h; rw [h])

end

/-! ## Liveness corresponds, and the strict test of a call -/

section
variable {K : RunCtx} {φ : Future} {σ : Nat → Nat} {s₀ : SState} {ks : List Nat} {s s' : SState}

/-- **The strict test of a call holds on both sides or on neither** (`BorrowArgsTyped`: each borrow argument's label live
at its parameter's content type; (F6) and (F7)). -/
theorem borrowArgsTyped_corr (h : FrameInv K φ σ s₀ ks s s') (hs₀ : FrameStart s₀ ks) (R : DataRead) (fv : Res)
    (args : List Res) :
    BorrowArgsTyped R (renRes σ fv) (args.map (renRes σ)) s ↔ BorrowArgsTyped R fv args s' := by
  unfold BorrowArgsTyped refLabelsOf
  simp only [renRes_m, map_fst_renRes, refLabels_ren]
  generalize ((args.zip (refsOf R fv.2.m (args.map (·.1)))).filter (·.2)).map (·.1.2.label) = refL
  constructor
  · intro H i l hi
    have := H i (σ l) (by rw [List.getElem?_map, hi]; rfl)
    have hl := (live_corr h hs₀ l).1 this.1
    exact ⟨hl, by rw [← (h.acc.rel.held l hl).2]; exact this.2⟩
  · intro H i l hi
    rw [List.getElem?_map] at hi
    cases e : refL[i]? with
    | none => rw [e] at hi; cases hi
    | some o =>
      rw [e] at hi
      cases o with
      | none => cases hi
      | some l' =>
        simp only [Option.map_some, Option.some.injEq] at hi; subst hi
        obtain ⟨h1, h2⟩ := H i l' e
        exact ⟨(live_corr h hs₀ l').2 h1, by rw [(h.acc.rel.held l' h1).2]; exact h2⟩

/-- **A call at a level, its goodness supplied** (`Strict.callOfLS_sgood`): from the closure's strict test. -/
theorem callOfL_agree'.{u} (L : Lvl.{u}) (hE : L.EncMem) (hL : L.Lawful) (hME : L.MemEnc) (hR : L.read = K.dm.read)
    {Cd : Type u} (tel : Tel L.Code PUnit Cd) (fv : Sem) (args : List Res)
    (h : FrameInv K φ σ s₀ ks s s') (hs₀ : FrameStart s₀ ks)
    (ht : ∀ (i l : Nat), (((args.zip (telRefsL L tel (args.map (·.1)))).filter (·.2)).map (·.1.2.label))[i]? =
      some (some l) → l ∈ s'.liveLabels ∧ s'.heldTy l = (telRefTysL L tel (args.map (·.1))).getD i TyM.err) :
    FrameAgreeI K φ σ s₀ ks (callOfL L tel fv (args.map (renRes σ)) s) (callOfL L tel fv args s') := by
  refine callOfL_agree L tel fv args h hs₀ (fun l hl => ?_) (fun r u hu => ?_) (fun r u hu => ?_)
  · obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp hl
    exact (ht i l hi).1
  · refine (Strict.callOfLS_sgood L hE hL hME hR tel fv _ h.good (fun i l hi => ?_) (fun l hl => .inl ?_) hu).2
    · rw [map_fst_renRes, refLabels_ren, List.getElem?_map] at hi
      rw [map_fst_renRes]
      generalize (((args.zip (telRefsL L tel (args.map (·.1)))).filter (·.2)).map (·.1.2.label)) = refL at ht hi
      cases e : refL[i]? with
      | none => rw [e] at hi; cases hi
      | some o =>
        rw [e] at hi
        cases o with
        | none => cases hi
        | some l' =>
          simp only [Option.map_some, Option.some.injEq] at hi; subst hi
          obtain ⟨h1, h2⟩ := ht i l' e
          rw [(h.acc.rel.held l' h1).2]; exact h2
    · rw [map_fst_renRes, refLabels_ren] at hl
      obtain ⟨o, ho, e⟩ := List.mem_map.mp hl
      cases o with
      | none => cases e
      | some l' =>
        simp only [Option.map_some, Option.some.injEq] at e; subst e
        obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp ho
        exact live_img h.acc.rel h.acc.shape (ht i l' hi).1
  · exact (Strict.callOfLS_sgood L hE hL hME hR tel fv _ h.good' (fun i l hi => (ht i l hi).2)
      (fun l hl => .inl (by obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp hl; exact (ht i l hi).1)) hu).2

end

/-! ## A call, at its type -/

section
variable {K : RunCtx} {φ : Future} {σ : Nat → Nat} {s₀ : SState} {ks : List Nat} {s s' : SState}

/-- **A call across the internal relation** (`callOf`: the callee applied along its type's code, at its level), given
the closure's strict test (which holds on both sides or neither, `borrowArgsTyped_corr`). -/
theorem callOf_agree (h : FrameInv K φ σ s₀ ks s s') (hs₀ : FrameStart s₀ ks) (fv : Res) (args : List Res)
    (ht : BorrowArgsTyped K.dm.read fv args s') :
    FrameAgreeI K φ σ s₀ ks (callOf K.dm.read (renRes σ fv) (args.map (renRes σ)) s) (callOf K.dm.read fv args s') := by
  rcases fv with ⟨fv, ⟨T, lab⟩⟩
  unfold callOf
  simp only [renRes]
  cases T with
  | t0 A c => cases c <;> dsimp only <;> first | trivial | exact callOfL_agree' (lvl0 K.dm.read) (lvl0_encMem _) (lvl0_lawful _) (Strict.lvl0_memEnc _) rfl _ fv args h hs₀ ht
  | t1 A c => cases c <;> dsimp only <;> first | trivial | exact callOfL_agree' (lvl1 K.dm.read) (lvl1_encMem _) (lvl1_lawful _) (Strict.lvl1_memEnc _) rfl _ fv args h hs₀ ht
  | t2 A c => cases c <;> dsimp only <;> first | trivial | exact callOfL_agree' (lvl2 K.dm.read) (lvl2_encMem _) (lvl2_lawful _) (Strict.lvl2_memEnc _) rfl _ fv args h hs₀ ht

/-- A statement position across the internal relation: a statement's result carries no label and its state is the one
it started from. -/
theorem agreeI_stmtIf (b : Bool) {x x' : SM Res} {s s' : SState} (h : FrameInv K φ σ s₀ ks s s')
    (hx : FrameAgreeI K φ σ s₀ ks (x s) (x' s')) : FrameAgreeI K φ σ s₀ ks (SM.stmtIf b x s) (SM.stmtIf b x' s') := by
  cases b with
  | false => exact hx
  | true =>
    simp only [SM.stmtIf, if_true]
    cases hxs : x s with
    | none =>
      rw [hxs] at hx
      cases hxs' : x' s' with
      | none => trivial
      | some _ => rw [hxs'] at hx; exact hx.elim
    | some y =>
      rw [hxs] at hx
      cases hxs' : x' s' with
      | none => rw [hxs'] at hx; exact hx.elim
      | some y' =>
        rw [hxs'] at hx
        obtain ⟨⟨v, R⟩, t⟩ := y
        obtain ⟨⟨v', R'⟩, t'⟩ := y'
        obtain ⟨hv, hR, -, -⟩ := hx
        simp only at hv; subst hv
        exact ⟨rfl, by subst hR; rfl, h, ⟨fun _ e => (by cases e), fun _ e => (by cases e)⟩⟩

/-- Two argument lists' runs agree: the in-place results are the closure's with their labels renamed, from related
states. -/
def ArgsAgree (K : RunCtx) (φ : Future) (σ : Nat → Nat) (s₀ : SState) (ks : List Nat) :
    Option (List Res × SState) → Option (List Res × SState) → Prop
  | some (rs, t), some (rs', t') => rs = rs'.map (renRes σ) ∧ FrameInv K φ σ s₀ ks t t'
  | none, none => True
  | _, _ => False

theorem sm_cons_eq (y : SM Res) (g : Res → SM (List Res)) (u : SState) :
    ((y >>= fun r => g r >>= fun rest => pure (r :: rest)) u) =
      (y u).bind (fun p => (g p.1 p.2).bind fun q => some (p.1 :: q.1, q.2)) := by
  simp only [Bind.bind, Pure.pure]
  cases y u with
  | none => rfl
  | some p =>
    obtain ⟨r, t⟩ := p
    simp only [Option.bind_some]
    cases g r t with
    | none => rfl
    | some q => rfl

/-- An argument's run, then the rest's, across the internal relation. -/
theorem argsAgree_cons {x x' : SM Res} {s s' : SState} (hx : FrameAgreeI K φ σ s₀ ks (x s) (x' s'))
    (g : Res → SM (List Res))
    (hg : ∀ (r' : Res) (t t' : SState), FrameInv K φ σ s₀ ks t t' → ArgsAgree K φ σ s₀ ks (g (renRes σ r') t) (g r' t')) :
    ArgsAgree K φ σ s₀ ks ((x >>= fun r => g r >>= fun rest => pure (r :: rest)) s)
      ((x' >>= fun r => g r >>= fun rest => pure (r :: rest)) s') := by
  rw [sm_cons_eq, sm_cons_eq]
  cases hxs : x s with
  | none =>
    rw [hxs] at hx
    cases hxs' : x' s' with
    | none => trivial
    | some _ => rw [hxs'] at hx; exact hx.elim
  | some y =>
    rw [hxs] at hx
    cases hxs' : x' s' with
    | none => rw [hxs'] at hx; exact hx.elim
    | some y' =>
      rw [hxs'] at hx
      obtain ⟨⟨v, R⟩, t⟩ := y
      obtain ⟨⟨v', R'⟩, t'⟩ := y'
      have e : ((v, R) : Res) = renRes σ (v', R') := agree_renRes hx
      obtain ⟨-, -, hI, -⟩ := hx
      simp only [Option.bind_some]
      rw [e]
      have := hg (v', R') t t' hI
      revert this
      cases g (renRes σ (v', R')) t with
      | none => cases g (v', R') t' with
        | none => intro; trivial
        | some _ => intro h; exact h.elim
      | some q => cases g (v', R') t' with
        | none => intro h; exact h.elim
        | some q' =>
          rintro ⟨hq, hI'⟩
          exact ⟨by simp only [List.map_cons, hq], hI'⟩

theorem runArgs_agree (ρ : Assignment) : ∀ (args : List Term), (∀ a ∈ args, TermFrame K ρ φ σ s₀ ks a) →
    ∀ (stmt : Bool) (fT : TyM) (earlier : List Sem) (s s' : SState), FrameInv K φ σ s₀ ks s s' →
      ArgsAgree K φ σ s₀ ks (runArgs K ρ φ stmt fT earlier args s) (runArgs K ρ φ stmt fT earlier args s')
  | [], _, stmt, fT, earlier, s, s', h => by simp only [runArgs]; exact ⟨rfl, h⟩
  | a :: as, ha, stmt, fT, earlier, s, s', h => by
    simp only [runArgs]
    rw [scopeOf_corr h.acc.rel]
    refine argsAgree_cons (agreeI_stmtIf _ h (ha a (List.mem_cons_self ..) false _ s s' h)) _ fun r' t t' hI => ?_
    exact runArgs_agree ρ as (fun b hb => ha b (List.mem_cons_of_mem _ hb)) stmt fT _ t t' hI

end

/-! ## The head of a call, and the clause -/

section
variable {K : RunCtx} {φ : Future} {σ : Nat → Nat} {s₀ : SState} {ks : List Nat} {s s' : SState}

theorem shrinks_contentOf {p : Place} {t : SState} {x : Sem × TyS × Pos × List Step} {u : SState}
    (h : contentOf K φ p t = some (x, u)) : Shrinks t u := by
  unfold contentOf at h
  split at h
  · dsimp only at h
    split at h
    · cases h; exact shrinks_access _ _ _
    · cases h
  · cases h

/-- **A call's head read in place** (a place of the callee's frame, copied: (O2) after (O4), `contentOf_corr`): the same
value, no label, related states. -/
theorem readCopy_agree (hs₀ : FrameStart s₀ ks) (h : FrameInv K φ σ s₀ ks s s') (p : Place) :
    FrameAgreeI K φ σ s₀ ks (SM.guarded (ContentOk K φ p) (readPlace K φ p true) s)
      (SM.guarded (ContentOk K φ p) (readPlace K φ p true) s') := by
  have g1 : ∀ r t, SM.guarded (ContentOk K φ p) (readPlace K φ p true) s = some (r, t) → Strict.SGood K.dm K.Γ φ t :=
    fun r t ht => (Strict.readPlace_fund_all p true s t r h.good ht).2.2.2
  have g2 : ∀ r t, SM.guarded (ContentOk K φ p) (readPlace K φ p true) s' = some (r, t) → Strict.SGood K.dm K.Γ φ t :=
    fun r t ht => (Strict.readPlace_fund_all p true s' t r h.good' ht).2.2.2
  obtain ⟨hc, hok⟩ := contentOf_corr φ hs₀ h.acc p
  unfold SM.guarded at g1 g2 ⊢
  by_cases hk : ContentOk K φ p s
  · have hk' := hok.1 hk
    rw [if_pos hk] at g1 ⊢; rw [if_pos hk'] at g2 ⊢
    unfold readPlace at g1 g2 ⊢
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
        rw [e2] at hc g2
        obtain ⟨⟨v, T, pos, steps⟩, t⟩ := y
        obtain ⟨⟨v', T', pos', steps'⟩, t'⟩ := y'
        obtain ⟨rfl, hT, rfl, -, rfl, hacc⟩ := hc
        subst hT
        simp only [bind, Option.bind] at g1 g2 ⊢
        by_cases hw : v.whole
        · by_cases hr : ReadGood K.dm.read T'.m v
          · simp only [hw, hr, not_true_eq_false, if_false, if_true] at g1 g2 ⊢
            exact ⟨rfl, rfl, h.of_ops hacc (g1 _ _ rfl) (g2 _ _ rfl) (shrinks_contentOf e1) (shrinks_contentOf e2),
              ⟨fun _ e => (by cases e), fun _ e => (by cases e)⟩⟩
          · simp only [hw, hr, not_true_eq_false, not_false_eq_true, if_false, if_true]; trivial
        · simp only [hw, not_false_eq_true, if_true]; trivial
  · rw [if_neg hk, if_neg (fun h' => hk (hok.2 h'))]; trivial

end

section
variable {K : RunCtx} {ρ : Assignment} {φ : Future} {σ : Nat → Nat} {s₀ : SState} {ks : List Nat} {s s' : SState}

theorem sm_bind_eq {α β : Type 3} (x : SM α) (f : α → SM β) (u : SState) :
    (x >>= f) u = (x u).bind (fun p => f p.1 p.2) := by
  simp only [Bind.bind]; cases x u <;> rfl

/-- A bind on two agreeing runs, the continuation at the closure's result renamed. -/
theorem agreeI_obind {o o' : Option (Res × SState)} (h : FrameAgreeI K φ σ s₀ ks o o')
    {g g' : Res × SState → Option (Res × SState)}
    (hg : ∀ (r' : Res) (t t' : SState), FrameInv K φ σ s₀ ks t t' →
      FrameAgreeI K φ σ s₀ ks (g (renRes σ r', t)) (g' (r', t'))) :
    FrameAgreeI K φ σ s₀ ks (o.bind g) (o'.bind g') := by
  match o, o', h with
  | none, none, _ => trivial
  | some (r, t), some (r', t'), hrt =>
    have e : r = renRes σ r' := agree_renRes hrt
    subst e
    exact hg r' t t' hrt.2.2.1

/-- A bind on two agreeing argument lists. -/
theorem args_obind {o o' : Option (List Res × SState)} (h : ArgsAgree K φ σ s₀ ks o o')
    {g g' : List Res × SState → Option (Res × SState)}
    (hg : ∀ (rs' : List Res) (t t' : SState), FrameInv K φ σ s₀ ks t t' →
      FrameAgreeI K φ σ s₀ ks (g (rs'.map (renRes σ), t)) (g' (rs', t'))) :
    FrameAgreeI K φ σ s₀ ks (o.bind g) (o'.bind g') := by
  match o, o', h with
  | none, none, _ => trivial
  | some (rs, t), some (rs', t'), ⟨e, hI⟩ => subst e; exact hg rs' t t' hI

/-- **A call's head**: a place of the callee's frame read in place (`readCopy_agree`), or any other term, by the frame
property at it. -/
theorem head_agree (hs₀ : FrameStart s₀ ks) (f : Term) (ihf : TermFrame K ρ φ σ s₀ ks f)
    (h : FrameInv K φ σ s₀ ks s s') :
    FrameAgreeI K φ σ s₀ ks
      (SM.headOf f (fun p => SM.guarded (ContentOk K φ p) (readPlace K φ p true)) (runT K ρ φ false (.plain TyM.err) f) s)
      (SM.headOf f (fun p => SM.guarded (ContentOk K φ p) (readPlace K φ p true)) (runT K ρ φ false (.plain TyM.err) f)
        s') := by
  cases f <;> first | exact readCopy_agree hs₀ h _ | exact ihf false (.plain TyM.err) s s' h

/-- **The frame property's clause for a call inside the body** (the paper's row "A call inside the body",
`<sec-frame-proof>`; docs/31 D202, D220, D221): the head (`head_agree`), the arguments (`runArgs_agree`, a statement
argument on a copy), the strict test on both sides or neither (`borrowArgsTyped_corr`), and the application
(`callOf_agree`: the takes and fixes, and for a returned borrow the fresh label parked and lent). -/
theorem runFrameI_call (hs₀ : FrameStart s₀ ks) {f : Term} {args : List Term} {hd : Bool}
    (ihf : TermFrame K ρ φ σ s₀ ks f) (ihargs : ∀ a ∈ args, TermFrame K ρ φ σ s₀ ks a) :
    TermFrame K ρ φ σ s₀ ks (.call f args hd) := by
  intro tl hint s s' hI
  rw [runT]; dsimp only
  rw [scopeOf_corr hI.acc.rel]
  refine agreeI_erasedIf _ hI ?_
  rw [sm_bind_eq, sm_bind_eq]
  refine agreeI_obind (head_agree hs₀ f ihf hI) fun fv t t' ht => ?_
  dsimp only
  rw [sm_bind_eq, sm_bind_eq]
  refine args_obind (runArgs_agree ρ args ihargs _ _ [] t t' ht) fun as u u' hu => ?_
  dsimp only
  have hiff := borrowArgsTyped_corr hu hs₀ K.dm.read fv as
  by_cases hb : BorrowArgsTyped K.dm.read fv as u'
  · rw [if_pos (hiff.2 hb), if_pos hb]
    exact callOf_agree hu hs₀ fv as hb
  · rw [if_neg (fun h' => hb (hiff.1 h')), if_neg hb]; trivial

end

end Ochr.Meaning.Steps.Form.FrameEnd
