import Ochr.Meaning.Strict.Call
import Ochr.Meaning.Strict.Ops
import Ochr.Meaning.MonoHolders

/-!
# A call keeps the invariant (`callOf`)

The consumed borrow arguments' holders read `⊥`; every position reads its old meaning at the future
with the consumed labels fixed to the callee's final contents, which are members of the parameters'
content types (`ApplyMem.app_mem_finals`), so of the labels' (`BorrowArgsTyped`): a typed future of
the state before. At a returned borrow `k` (fresh), a typed future gives `k` an open member;
where it decodes, the finals are the backward function's (members); where it does not, `callOfL`
fixes them to `⊥`, an open member of anything.

One hypothesis beyond the stub's (`hlive`): each borrow argument's label is live, or no position
reads it (`RunPresInd`'s `LoU`, which every run gives its result). A label that is neither (a dead
label some position still reads) would read the callee's final content after the call where it read
the run's future before: `SGood` constrains the state only at futures agreeing with the run's at
non-live labels, so nothing says the position is good at the final content.
-/

namespace Ochr.Meaning.Strict
open Ochr.Meaning

universe u

/-! ## Futures updated at lists of labels -/

/-- A property of every value a list update can put at `y`, and of the old one, holds of the new. -/
theorem updList_prop (P : Sem → Prop) : ∀ (L : List (Nat × Sem)) (ψ : Future) (y : Nat),
    (∀ f, (y, f) ∈ L → P f) → (y ∉ L.map (·.1) → P (ψ y)) → P (ψ.updList L y)
  | [], ψ, y, _, h0 => h0 (by simp)
  | (l, e) :: rest, ψ, y, hL, h0 => by
    simp only [Future.updList]
    refine updList_prop P rest _ y (fun f hf => hL f (List.mem_cons_of_mem _ hf)) (fun hy => ?_)
    by_cases e' : y = l
    · subst e'; rw [Future.upd_same]; exact hL e (List.mem_cons_self ..)
    · rw [Future.upd_other _ _ e']
      exact h0 (by simp only [List.map_cons, List.mem_cons, not_or]; exact ⟨e', hy⟩)

/-- Updating a meaning's future at labels it does not read changes nothing. -/
theorem eq_updList_indep {v : SVal} (ψ : Future) : ∀ (E : List (Nat × Sem)), (∀ e ∈ E, Indep e.1 v) →
    v (ψ.updList E) = v ψ
  | [], _ => rfl
  | (y, x) :: rest, h => by
    simp only [Future.updList]
    rw [eq_updList_indep (ψ.upd y x) rest (fun e he => h e (List.mem_cons_of_mem _ he))]
    exact h (y, x) (List.mem_cons_self ..) ψ x

theorem updList_mem_keys {L : List (Nat × Sem)} {y : Nat} {f : Sem} (h : (y, f) ∈ L) : y ∈ L.map (·.1) :=
  List.mem_map.2 ⟨_, h, rfl⟩

/-- An entry of the fixes `callOfL` builds: a label and a final at the same index. -/
theorem fixes_mem : ∀ {ls : List (Option Nat)} {fs : List Sem} {y : Nat} {f : Sem},
    (y, f) ∈ (ls.zip fs).filterMap (fun (l?, f) => l?.map (·, f)) →
    ∃ i : Nat, ls[i]? = some (some y) ∧ fs[i]? = some f
  | [], _, _, _, h => by simp at h
  | _ :: _, [], _, _, h => by simp at h
  | l? :: ls, f' :: fs, y, f, h => by
    simp only [List.zip_cons_cons, List.filterMap_cons] at h
    cases l? with
    | none =>
      simp only [Option.map_none] at h
      obtain ⟨i, h1, h2⟩ := fixes_mem h
      exact ⟨i + 1, by simpa using h1, by simpa using h2⟩
    | some l =>
      simp only [Option.map_some, List.mem_cons, Prod.mk.injEq] at h
      rcases h with ⟨rfl, rfl⟩ | h
      · exact ⟨0, rfl, rfl⟩
      · obtain ⟨i, h1, h2⟩ := fixes_mem h
        exact ⟨i + 1, by simpa using h1, by simpa using h2⟩

/-- Members in order, read at an index. -/
theorem MemList.get {R : DataRead} : ∀ {fs : List Sem} {Ts : List TyM}, MemList R fs Ts →
    ∀ {i : Nat} {f : Sem}, fs[i]? = some f → ∃ T, Ts[i]? = some T ∧ f ∈ₛ[R] T
  | _, _, .nil, _, _, h => by simp at h
  | _, _, .cons hf hs, 0, _, h => by simp only [List.getElem?_cons_zero, Option.some.injEq] at h; subst h; exact ⟨_, rfl, hf⟩
  | _, _, .cons _ hs, i + 1, _, h => by simpa using MemList.get hs (by simpa using h)

/-! ## Taking the borrow arguments' holders -/

theorem tyAt_takeLabel (s : SState) (l : Nat) (q : Pos) : (s.takeLabel l).tyAt q = s.tyAt q := by
  unfold SState.takeLabel
  split
  · exact tyAt_setAt s _ _ q
  · rfl

theorem heldTy_takeLabel (s : SState) (l : Nat) : (s.takeLabel l).heldTy = s.heldTy := by
  unfold SState.takeLabel
  split
  · exact heldTy_setAt s _ _
  · rfl

theorem heldMem_takeLabel (s : SState) (l : Nat) : (s.takeLabel l).heldMem = s.heldMem := by
  unfold SState.takeLabel
  split
  · exact heldMem_setAt s _ _
  · rfl

section
variable (s : SState)

theorem takeAll_tyAt : ∀ (ls : List Nat) (q : Pos), (ls.foldl SState.takeLabel s).tyAt q = s.tyAt q := by
  intro ls
  induction ls generalizing s with
  | nil => intro q; rfl
  | cons l ls ih => intro q; rw [List.foldl_cons, ih, tyAt_takeLabel]

theorem takeAll_heldTy : ∀ (ls : List Nat), (ls.foldl SState.takeLabel s).heldTy = s.heldTy := by
  intro ls
  induction ls generalizing s with
  | nil => rfl
  | cons l ls ih => rw [List.foldl_cons, ih, heldTy_takeLabel]

theorem takeAll_heldMem : ∀ (ls : List Nat), (ls.foldl SState.takeLabel s).heldMem = s.heldMem := by
  intro ls
  induction ls generalizing s with
  | nil => rfl
  | cons l ls ih => rw [List.foldl_cons, ih, heldMem_takeLabel]

theorem takeAll_valAt : ∀ (ls : List Nat) (q : Pos),
    (ls.foldl SState.takeLabel s).valAt q = s.valAt q ∨ (ls.foldl SState.takeLabel s).valAt q = fun _ => .moved := by
  intro ls
  induction ls generalizing s with
  | nil => intro q; exact .inl rfl
  | cons l ls ih =>
    intro q
    rw [List.foldl_cons]
    rcases ih (s.takeLabel l) q with h | h
    · rw [h]; exact SState.takeLabel_valAt s l q
    · exact .inr h

theorem takeAll_live_rev : ∀ (ls : List Nat) {y : Nat}, (ls.foldl SState.takeLabel s).Live y → s.Live y := by
  intro ls
  induction ls generalizing s with
  | nil => intro y h; exact h
  | cons l ls ih => intro y h; exact SState.takeLabel_live_rev (ih (s.takeLabel l) h)

theorem takeAll_live : ∀ (ls : List Nat) {y : Nat}, s.Live y → y ∉ ls → (ls.foldl SState.takeLabel s).Live y := by
  intro ls
  induction ls generalizing s with
  | nil => intro y h _; exact h
  | cons l ls ih =>
    intro y h hn
    simp only [List.mem_cons, not_or] at hn
    exact ih (s.takeLabel l) (SState.takeLabel_live h hn.1) hn.2

theorem takeAll_shape : ∀ (ls : List Nat) {p : Pos} {y : Nat}, (ls.foldl SState.takeLabel s).shape p = some y →
    s.shape p = some y :=
  fun ls _ _ h => (SState.shapeSub_foldl_takeLabel ls s).1 _ _ h

end

/-! ## The future a position reads after the call, typed before it -/

open Classical in
/-- **Transport**: a future `ψ'` of the state after a call, fixed at the call's finals `F` (each an
open member of its label's content type), is, on the old positions, a typed future of the
state before: reset the fixed labels that are not live (no position reads them) and the extra
labels `E` (not live, unread: the returned borrow's fresh label) to the run's future. -/
theorem typed_transport {dm : DataModel} {Γ : List IndDecl} {φ : Future} {s : SState} (F : List (Nat × Sem))
    (E : List Nat) (ψ' : Future)
    (hF : ∀ y f, (y, f) ∈ F → f ∈ₛ[dm.read] s.heldTy y)
    (hFlive : ∀ y ∈ F.map (·.1), y ∈ s.liveLabels ∨ ∀ p, Indep y (s.valAt p))
    (hE : ∀ y ∈ E, y ∉ s.liveLabels ∧ ∀ p, Indep y (s.valAt p))
    (hlive : ∀ y ∈ s.liveLabels, y ∉ F.map (·.1) → ψ' y ∈ₛ[dm.read] s.heldTy y)
    (hagree : ∀ y, y ∉ s.liveLabels → y ∉ F.map (·.1) → y ∉ E → ψ' y = φ y) :
    ∃ ψ₀, TypedF dm Γ φ s ψ₀ ∧ ∀ p, s.valAt p (ψ'.updList F) = s.valAt p ψ₀ := by
  let D : List Nat := (F.map (·.1)).filter (fun y => decide (y ∉ s.liveLabels)) ++ E
  have hD : ∀ y ∈ D, y ∉ s.liveLabels ∧ ∀ p, Indep y (s.valAt p) := by
    intro y hy
    rcases List.mem_append.1 hy with hy | hy
    · obtain ⟨hk, hnl⟩ := List.mem_filter.1 hy
      have hnl' : y ∉ s.liveLabels := by simpa using hnl
      exact ⟨hnl', (hFlive y hk).resolve_left hnl'⟩
    · exact hE y hy
  let R : List (Nat × Sem) := D.map fun y => (y, φ y)
  have hRk : R.map (·.1) = D := by simp [R, List.map_map, Function.comp_def]
  refine ⟨(ψ'.updList F).updList R, ⟨fun y hy => ?_, fun y hy => ?_⟩, fun p => ?_⟩
  · by_cases hyD : y ∈ D
    · refine updList_prop (· = φ y) R _ y (fun f hf => ?_) (fun hn => absurd (hRk ▸ hyD) hn)
      obtain ⟨z, -, hz⟩ := List.mem_map.1 hf
      simp only [Prod.mk.injEq] at hz
      rw [← hz.2, hz.1]
    · rw [Future.updList_of_not_mem R _ y (by rw [hRk]; exact hyD)]
      have hyF : y ∉ F.map (·.1) := fun hm =>
        hyD (List.mem_append_left _ (List.mem_filter.2 ⟨hm, by simpa using hy⟩))
      have hyE : y ∉ E := fun hm => hyD (List.mem_append_right _ hm)
      rw [Future.updList_of_not_mem F _ y hyF]
      exact hagree y hy hyF hyE
  · have hyD : y ∉ D := fun hm => (hD y hm).1 hy
    rw [Future.updList_of_not_mem R _ y (by rw [hRk]; exact hyD)]
    exact updList_prop (fun f => f ∈ₛ[dm.read] s.heldTy y) F ψ' y (fun f hf => hF y f hf)
      (fun hn => hlive y hy hn)
  · refine (eq_updList_indep (v := s.valAt p) (ψ'.updList F) R fun e he => ?_).symm
    obtain ⟨y, hy, rfl⟩ := List.mem_map.1 he
    exact (hD y hy).2 p

/-! ## The label order and the fresh-label bound, for the repaired call (`callOfL`)

`callOfL` is `callOfL` with `⊥` for `err` in one branch, so these are `Locality.callOfL_ref_inv`,
`RunPres.callOfL_rinv` and `MonoHolders.callOfL_readsBelow`, re-run (`park_fix_inv` takes the
undecodable branch's list as a parameter). -/

theorem callOfLS_eq_data (Lv : Lvl.{u}) {C : Type u} {t : Tel Lv.Code PUnit C} {fv : Sem} {args : List Res}
    {s s' : SState} {r : Res} {r' : Sem} {T' : TyM} {finals : List Sem}
    (happ : applyFnL Lv t fv (args.map (·.1)) = some (.data r' T' finals))
    (h : callOfL Lv t fv args s = some (r, s')) : callOfL Lv t fv args s = some (r, s') := by
  unfold callOfL at h; unfold callOfL; dsimp only at h ⊢; rw [happ] at h ⊢; exact h

theorem callOfLS_ref_inv {L : Nat → Prop} (Lv : Lvl.{u}) {C : Type u} (t : Tel Lv.Code PUnit C) (fv : Sem)
    (args : List Res) {s s' : SState} (h1 : SState.Inv1 L s) (h2 : SState.Inv2 L s) (hsa : SState.ShapeAt s)
    {res : Res} (h : callOfL Lv t fv args s = some (res, s'))
    {U : Type u} {c : Lv.Code U} {fwd : U} {back : U → List Sem}
    (happ : applyFnL Lv t fv (args.map (·.1)) = some (.ref U c fwd back)) :
    SState.Inv1 L s' ∧ SState.Inv2 L s' := by
  unfold callOfL at h
  dsimp only at h
  rw [happ] at h
  simp only [SState.freshLoan, Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨_, rfl⟩ := h
  rw [SState.inv1_setHeldMem, SState.inv2_setHeldMem, SState.inv1_setHeldTy, SState.inv2_setHeldTy, SState.inv1_setLent, SState.inv2_setLent]
  unfold applyFnL at happ
  obtain ⟨F, hu, happ'⟩ : ∃ F, Lv.unpack C fv = some F ∧
      applyTelL Lv t (fun _ => []) F (args.map (·.1)) = some (.ref U c fwd back) := by
    cases hu : Lv.unpack C fv with
    | none => rw [hu] at happ; cases happ
    | some F => rw [hu] at happ; exact ⟨F, rfl, happ⟩
  obtain ⟨hlen, hfin⟩ := applyTelL_len Lv t (fun _ => []) F _ 0 (fun _ => rfl) _ happ'
  simp only [List.length_map] at hlen
  simp only [Nat.zero_add] at hfin
  have hcover : ∀ x, ∀ l ∈ (((args.zip (telRefsL Lv t (args.map (·.1)))).filter (·.2)).map (·.1.2.label)).filterMap id,
      l ∈ (((((args.zip (telRefsL Lv t (args.map (·.1)))).filter (·.2)).map (·.1.2.label)).zip (back x)).filterMap
        fun (y : Option Nat × Sem) => y.1.map (·, y.2)).map (·.1) := by
    intro x
    have hfx : (fun (y : Option Nat × Sem) => y.1.map (·, y.2)) = (fun (l?, f) => l?.map (·, f)) :=
      funext fun ⟨_, _⟩ => rfl
    rw [hfx]
    apply fixes_cover
    rw [List.length_map, zip_filter_len args _ hlen, hfin x]
    exact Nat.le_refl _
  have hcoverE : ∀ l ∈ (((args.zip (telRefsL Lv t (args.map (·.1)))).filter (·.2)).map (·.1.2.label)).filterMap id,
      l ∈ (((((args.zip (telRefsL Lv t (args.map (·.1)))).filter (·.2)).map (·.1.2.label)).zip
        ((((args.zip (telRefsL Lv t (args.map (·.1)))).filter (·.2)).map (·.1.2.label)).map fun _ => Sem.moved)).filterMap
        fun (y : Option Nat × Sem) => y.1.map (·, y.2)).map (·.1) := by
    have hfx : (fun (y : Option Nat × Sem) => y.1.map (·, y.2)) = (fun (l?, f) => l?.map (·, f)) :=
      funext fun ⟨_, _⟩ => rfl
    rw [hfx]
    apply fixes_cover
    simp only [List.length_map]
    exact Nat.le_refl _
  apply SState.park_fix_inv h1 h2 hsa _ (Lv.dec c) _ _ _ _ hcover _ hcoverE (Lv.enc c fwd)
  intro p v ψ
  cases hd : Lv.dec c (ψ ((((((args.zip (telRefsL Lv t (args.map (·.1)))).filter (·.2)).map (·.1.2.label)).filterMap id)).foldl
      SState.takeLabel s).nextLoan) with
  | none => exact .inr ⟨rfl, by simp only [hd]⟩
  | some x => exact .inl ⟨x, rfl, by simp only [hd]⟩

theorem callOfLS_rinv {L : Nat → Prop} (Lv : Lvl.{u}) {C : Type u} (t : Tel Lv.Code PUnit C) (fv : Sem)
    (args : List Res) {s s' : SState} {r : Res} (hi : SState.RInv L s)
    (h : callOfL Lv t fv args s = some (r, s')) : SState.RInv L s' := by
  obtain ⟨h1, h2, hsa⟩ := hi
  cases happ : applyFnL Lv t fv (args.map (·.1)) with
  | none => unfold callOfL at h; dsimp only at h; rw [happ] at h; cases h
  | some res =>
    cases res with
    | data r' T' finals =>
      exact (callOfL_rinv L Lv t fv args ⟨h1, h2, hsa⟩ (callOfLS_eq_data Lv happ h)).1
    | ref U c fwd back =>
      obtain ⟨i1, i2⟩ := callOfLS_ref_inv Lv t fv args h1 h2 hsa h happ
      have h' := h
      unfold callOfL at h'; dsimp only at h'; rw [happ] at h'
      simp only [SState.freshLoan, Option.some.injEq, Prod.mk.injEq] at h'
      obtain ⟨rfl, rfl⟩ := h'
      rw [SState.inv1_setHeldMem, SState.inv1_setHeldTy, SState.inv1_setLent] at i1
      rw [SState.inv2_setHeldMem, SState.inv2_setHeldTy, SState.inv2_setLent] at i2
      rw [rinv_setHeldMem, rinv_setHeldTy, rinv_setLent]
      generalize hS : (SState.mapVals _ _ : SState) = S at i1 i2 ⊢
      have hsaS : SState.ShapeAt S := by
        rw [← hS]
        apply shapeAt_mapVals
        intro p x hp
        obtain ⟨h1', h2'⟩ := shapeAt_takeAll _ hsa p x hp
        exact ⟨h1', Nat.lt_succ_of_lt h2'⟩
      have hnlS : S.nextLoan = (List.foldl SState.takeLabel s
          (List.filterMap id (List.map (fun x => x.1.2.label) (List.filter (fun x => x.2) (args.zip (telRefsL Lv t (args.map (·.1)))))))).nextLoan + 1 := by
        rw [← hS]; rfl
      by_cases hne : S.env = []
      · have hfin : S.pushTempShaped (fun _ => Lv.enc c fwd) (List.foldl SState.takeLabel s
            (List.filterMap id (List.map (fun x => x.1.2.label) (List.filter (fun x => x.2) (args.zip (telRefsL Lv t (args.map (·.1)))))))).nextLoan
            = S.pushTemp (fun _ => Lv.enc c fwd) := by
          unfold SState.pushTempShaped
          dsimp only
          rw [SState.pushTemp_getLast, hne]; rfl
        rw [hfin] at i1 i2 ⊢
        refine ⟨i1, i2, fun p x hp => ?_⟩
        obtain ⟨hp1, _⟩ := hsaS p x hp
        rw [SState.positions_eq, hne] at hp1; simp at hp1
      · exact ⟨i1, i2, SState.pushTempShaped_shapeAt hsaS hne _ _ (by rw [hnlS]; exact Nat.lt_succ_self _)⟩

theorem callOfLS_readsBelow (Lv : Lvl.{u}) {C : Type u} (t : Tel Lv.Code PUnit C) (fv : Sem)
    (args : List Res) (s : SState) (hs : s.ReadsBelow) {r : Res} {s' : SState}
    (h : callOfL Lv t fv args s = some (r, s')) : s'.ReadsBelow := by
  unfold callOfL at h
  try dsimp only at h
  have hs₀ := SState.readsBelow_foldl_takeLabel hs ((((args.zip (telRefsL Lv t (args.map (·.1)))).filter (·.2)).map (·.1.2.label)).filterMap id)
  split at h
  · simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨_, rfl⟩ := h
    exact SState.readsBelow_mapVals_updList hs₀ _
  · simp only [SState.freshLoan, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨_, rfl⟩ := h
    generalize ((((args.zip (telRefsL Lv t (args.map (·.1)))).filter (·.2)).map (·.1.2.label)).filterMap id).foldl SState.takeLabel s = s₀ at hs₀ ⊢
    refine SState.readsBelow_pushTempShaped ?_ _ _ fun _ ⟨_, _, hne⟩ => absurd rfl hne
    intro p l ⟨φ, x, hne⟩
    show l < s₀.nextLoan + 1
    by_cases hlk : l = s₀.nextLoan
    · omega
    · refine Nat.lt_succ_of_lt (Classical.byContradiction fun hl => hne ?_)
      have hlt : ¬ (s₀.valAt p).DependsOn l := fun hd => hl (hs₀ p l hd)
      show (SState.mapVals _ _).valAt p φ = (SState.mapVals _ _).valAt p (φ.upd l x)
      rw [SState.valAt_mapVals]
      split
      · dsimp only
        rw [Future.upd_other φ x (Ne.symm hlk)]
        cases hd : Lv.dec _ (φ s₀.nextLoan) with
        | none => exact (updList_indep hlt _ φ x).symm
        | some y => exact (updList_indep hlt _ φ x).symm
      · rfl
  · cases h

/-! ## A pushed temporary: bindings untouched, the new position holds the value -/

theorem lookup_pushTemp_bind (s : SState) (v : SVal) (f i : Nat) :
    (s.pushTemp v).lookup (.bind f i) = s.lookup (.bind f i) := by
  simp only [SState.lookup, SState.pushTemp, List.getElem?_modify]
  split <;> cases s.env[f]? <;> simp

theorem bind_mem_pushTemp (s : SState) (v : SVal) (f i : Nat) :
    Pos.bind f i ∈ (s.pushTemp v).positions ↔ Pos.bind f i ∈ s.positions := by
  rw [SState.mem_positions, SState.mem_positions, lookup_pushTemp_bind]

theorem valAt_pushTemp_bind (s : SState) (v : SVal) (f i : Nat) :
    (s.pushTemp v).valAt (.bind f i) = s.valAt (.bind f i) := by
  rw [SState.valAt_eq, SState.valAt_eq, lookup_pushTemp_bind]

theorem tyAt_pushTemp (s : SState) (v : SVal) (q : Pos) : (s.pushTemp v).tyAt q = s.tyAt q := by
  cases q with
  | temp => rfl
  | bind f i =>
    simp only [SState.tyAt, SState.pushTemp, List.getElem?_modify]
    by_cases hf : s.topIdx = f <;> cases s.env[f]? <;> simp [hf]

theorem valAt_pushTemp_new (s : SState) (v : SVal) {q : Pos} (hq : q ∈ (s.pushTemp v).positions)
    (hn : q ∉ s.positions) : (s.pushTemp v).valAt q = v := by
  cases q with
  | bind f i => exact absurd ((bind_mem_pushTemp s v f i).1 hq) hn
  | temp f i =>
    rw [SState.mem_positions] at hq hn
    rw [SState.valAt_eq]
    simp only [SState.lookup, SState.pushTemp, List.getElem?_modify] at hq hn ⊢
    by_cases hf : s.topIdx = f
    · cases hfr : s.env[f]? with
      | none => simp [hfr] at hq
      | some fr =>
        simp only [hfr, hf, if_true, Option.map_eq_map, Option.map_some, Option.bind_some] at hq hn ⊢
        have hi : ¬ i < fr.temps.length := fun hi => hn (by simp [hi])
        have hi' : i < fr.temps.length + 1 := by
          refine Classical.byContradiction fun hc => ?_
          rw [List.getElem?_eq_none (by simp; omega)] at hq
          simp at hq
        have hie : i = fr.temps.length := by omega
        subst hie
        simp
    · cases hfr : s.env[f]? with
      | none => simp [hfr] at hq
      | some fr => simp [hfr, hf] at hq hn; omega

/-! ## The finals are members of the borrow parameters' content types -/

section
variable (L : Lvl.{u})

/-- An application's final contents (a data result's, or a returned borrow's backward function's at
every content) are members of the given types. -/
def FinalsMem (tys : List TyM) : AppResultL L → Prop
  | .data _ _ fins => MemList L.read fins tys
  | .ref _ _ _ back => ∀ x, MemList L.read (back x) tys

/-- **The finals of any application are members** of the borrow parameters' content types (those
`readFin` already holds, then those the arguments reach): each is an encoding (`EncMem`). Unlike
`ApplyMem.applyTelL_mem` it needs no codomain and covers a returned borrow's backward function. -/
theorem applyTelL_finals (hE : L.EncMem) :
    ∀ {Fin C : Type u} (t : Tel L.Code Fin C) (readFin : Fin → List Sem) (tys : List TyM)
      (hread : ∀ fin, MemList L.read (readFin fin) tys) (F : C) (args : List Sem) (out : AppResultL L),
      applyTelL L t readFin F args = some out → FinalsMem L (tys ++ telRefTysL L t args) out
  | _, _, .dat Fin B' c, readFin, tys, hread, F, [], out, h => by
    simp only [applyTelL, Option.some.injEq] at h
    subst h
    simpa [FinalsMem, telRefTysL] using hread F.2
  | _, _, .ref Fin U c, readFin, tys, hread, F, [], out, h => by
    simp only [applyTelL, Option.some.injEq] at h
    subst h
    intro x
    simpa [FinalsMem, telRefTysL] using hread (F.val.2 x)
  | _, _, .param Fin isRef A c C' k, readFin, tys, hread, F, a :: as, out, h => by
    simp only [applyTelL] at h
    cases hx : L.dec c a with
    | none => rw [hx] at h; cases h
    | some x =>
      rw [hx] at h
      have hread' : ∀ fin, MemList L.read
          (extReadL isRef Fin A readFin (L.enc c) fin) (tys ++ if isRef then [L.toTy c] else []) := by
        intro fin
        cases isRef with
        | false => simpa [extReadL] using hread fin
        | true =>
          simp only [extReadL, if_true]
          exact MemList.append (hread fin.1) (.cons (hE c fin.2) .nil)
      have := applyTelL_finals hE (k x) _ _ hread' (F x) as out h
      simp only [telRefTysL, hx]
      simpa [List.append_assoc] using this
  | _, _, .dat .., _, _, _, _, _ :: _, _, h => by simp [applyTelL] at h
  | _, _, .ref .., _, _, _, _, _ :: _, _, h => by simp [applyTelL] at h
  | _, _, .param .., _, _, _, _, [], _, h => by simp [applyTelL] at h

end

/-! ## The state after a call: bindings and reads from a typed future of the state before -/

/-- On `err`, a read gives `err` or nothing. -/
theorem follow_err (dm : DataModel) (Γ : List IndDecl) : ∀ (T : TyS) (steps : List Step) (x : Sem) (U : TyS),
    Sem.follow dm Γ T .err steps = some (x, U) → x = .err
  | _, [], _, _, h => by simp only [Sem.follow, Option.some.injEq, Prod.mk.injEq] at h; exact h.1.symm
  | T, st :: sts, x, U, h => by
    simp only [Sem.follow] at h
    cases st with
    | deref => exact follow_err dm Γ T sts x U (by simpa [Sem.step] using h)
    | proj i =>
      cases i with
      | zero => simp [Sem.step, Sem.asNat, Sem.as, Sem.stepField] at h
      | succ i => simp [Sem.step, Sem.stepField] at h
    | field g => simp [Sem.step, Sem.stepField] at h

/-- Where every old binding reads, at `ψ'`, its old meaning at a typed future `ψ₀` of the state
before, or `⊥`, the bindings of the state after are good. -/
theorem sgood_bind_read {dm : DataModel} {Γ : List IndDecl} {φ : Future} {s S : SState} (hs : SGood dm Γ φ s)
    (hpos : ∀ f i, Pos.bind f i ∈ S.positions ↔ Pos.bind f i ∈ s.positions)
    (hty : ∀ f i, S.tyAt (.bind f i) = s.tyAt (.bind f i))
    {ψ' ψ₀ : Future} (hψ₀ : TypedF dm Γ φ s ψ₀)
    (hv : ∀ f i, Pos.bind f i ∈ s.positions →
      S.valAt (.bind f i) ψ' = s.valAt (.bind f i) ψ₀ ∨ S.valAt (.bind f i) ψ' = .moved) :
    ∀ f i, Pos.bind f i ∈ S.positions → GoodVal dm Γ (S.valAt (.bind f i) ψ') (S.tyAt (.bind f i)).m := by
  intro f i hp
  have hp' := (hpos f i).1 hp
  rw [hty]
  rcases hv f i hp' with e | e
  · rw [e]; exact hs.bind ψ₀ hψ₀ f i hp'
  · rw [e]; exact .inl (.moved _)

/-! ## The fixes of a call -/

section
variable {dm : DataModel} {Γ : List IndDecl} {φ : Future} (Lv : Lvl.{u}) {C : Type u} (t : Tel Lv.Code PUnit C)
  (args : List Res) {s : SState}

/-- Every entry of the fixes at finals that are members of the parameters' content types is a
member of its label's recorded content type (a borrow is invariant: `BorrowArgsTyped`). -/
theorem fixes_pmem (hR : Lv.read = dm.read)
    (ht : ∀ (i l : Nat), (((args.zip (telRefsL Lv t (args.map (·.1)))).filter (·.2)).map (·.1.2.label))[i]? = some (some l) →
      s.heldTy l = (telRefTysL Lv t (args.map (·.1))).getD i TyM.err)
    {fs : List Sem} (hfs : MemList Lv.read fs (telRefTysL Lv t (args.map (·.1)))) :
    ∀ y f, (y, f) ∈ ((((args.zip (telRefsL Lv t (args.map (·.1)))).filter (·.2)).map (·.1.2.label)).zip fs).filterMap
      (fun (l?, f) => l?.map (·, f)) → f ∈ₛ[dm.read] s.heldTy y := by
  intro y f hm
  obtain ⟨i, hi, hf⟩ := fixes_mem hm
  obtain ⟨T, hT, hfT⟩ := MemList.get hfs hf
  have e := ht i y hi
  rw [List.getD_eq_getElem?_getD, hT, Option.getD_some] at e
  rw [e]
  rw [hR] at hfT
  exact hfT

theorem fixes_keys_live
    (hlive : ∀ l, some l ∈ ((args.zip (telRefsL Lv t (args.map (·.1)))).filter (·.2)).map (·.1.2.label) →
      l ∈ s.liveLabels ∨ ∀ p, Indep l (s.valAt p)) (fs : List Sem) :
    ∀ y ∈ (((((args.zip (telRefsL Lv t (args.map (·.1)))).filter (·.2)).map (·.1.2.label)).zip fs).filterMap
      (fun (l?, f) => l?.map (·, f))).map (·.1), y ∈ s.liveLabels ∨ ∀ p, Indep y (s.valAt p) := by
  intro y hy
  obtain ⟨⟨y', f⟩, hm, rfl⟩ := List.mem_map.1 hy
  obtain ⟨i, hi, -⟩ := fixes_mem hm
  exact hlive y' (List.mem_of_getElem? hi)

end

/-! ## The taken state, its positions fixed at the finals -/

/-- **The state after a call returning data**, abstractly: the borrow arguments' holders taken
(`Ls`), every position read with the taken labels fixed to finals `FF` that cover them and are
open members of the labels' content types. -/
theorem sgood_mapVals_fix {dm : DataModel} {Γ : List IndDecl} {φ : Future} {s : SState} (hs : SGood dm Γ φ s)
    (Ls : List Nat) (FF : List (Nat × Sem))
    (hcov : ∀ l ∈ Ls, l ∈ FF.map (·.1))
    (hFm : ∀ y f, (y, f) ∈ FF → f ∈ₛ[dm.read] s.heldTy y)
    (hFl : ∀ y ∈ FF.map (·.1), y ∈ s.liveLabels ∨ ∀ p, Indep y (s.valAt p))
    (hacyc : SState.RInv (fun _ => True) ((Ls.foldl SState.takeLabel s).mapVals fun _ v φ' => v (φ'.updList FF)))
    (hfresh : ((Ls.foldl SState.takeLabel s).mapVals fun _ v φ' => v (φ'.updList FF)).ReadsBelow) :
    SGood dm Γ φ ((Ls.foldl SState.takeLabel s).mapVals fun _ v φ' => v (φ'.updList FF)) := by
  generalize hs₁ : Ls.foldl SState.takeLabel s = s₁ at hacyc hfresh ⊢
  have hpos₁ : s₁.positions = s.positions := by rw [← hs₁]; exact SState.takeAll_positions s Ls
  generalize hS : s₁.mapVals (fun _ v φ' => v (φ'.updList FF)) = S at hacyc hfresh ⊢
  have hposS : S.positions = s.positions := by rw [← hS, SState.positions_mapVals, hpos₁]
  have hliveS : S.liveLabels = s₁.liveLabels := by
    rw [← hS]; unfold SState.liveLabels; rw [SState.positions_mapVals]; rfl
  have hshapeS : S.shape = s₁.shape := by rw [← hS]; rfl
  have htyS : ∀ q, S.tyAt q = s.tyAt q := fun q => by rw [← hS, tyAt_mapVals, ← hs₁, takeAll_tyAt]
  have hHT : S.heldTy = s.heldTy := by rw [← hS, ← hs₁]; exact takeAll_heldTy s Ls
  have hHM : S.heldMem = s.heldMem := by rw [← hS, ← hs₁]; exact takeAll_heldMem s Ls
  have hval : ∀ p ∈ s.positions, ∀ ψ', S.valAt p ψ' = s₁.valAt p (ψ'.updList FF) := by
    intro p hp ψ'
    rw [← hS, SState.valAt_mapVals_of_mem _ _ _ (by rw [hpos₁]; exact hp)]
  have hlive_rev : ∀ y, y ∈ S.liveLabels → y ∈ s.liveLabels := by
    intro y hy; rw [hliveS, ← hs₁] at hy; exact takeAll_live_rev s Ls hy
  have hlive_fwd : ∀ y, y ∈ s.liveLabels → y ∉ Ls → y ∈ S.liveLabels := by
    intro y hy hn; rw [hliveS, ← hs₁]; exact takeAll_live s Ls hy hn
  -- a typed future after, read on the old positions, is a typed future before (or `⊥`)
  have key : ∀ ψ', TypedF dm Γ φ S ψ' → ∃ ψ₀, TypedF dm Γ φ s ψ₀ ∧
      ∀ p ∈ s.positions, S.valAt p ψ' = s.valAt p ψ₀ ∨ S.valAt p ψ' = .moved := by
    intro ψ' hψ'
    obtain ⟨ψ₀, hψ₀, heq⟩ := typed_transport (φ := φ) FF [] ψ' hFm hFl (fun _ h => absurd h List.not_mem_nil)
      (fun y hy hn => by
        have := hψ'.2 y (hlive_fwd y hy fun hL => hn (hcov y hL)); rwa [hHT] at this)
      (fun y hy _ _ => hψ'.1 y fun h => hy (hlive_rev y h))
    refine ⟨ψ₀, hψ₀, fun p hp => ?_⟩
    rw [hval p hp]
    rcases takeAll_valAt s Ls p with e | e
    · rw [← hs₁, e]; exact .inl (heq p)
    · rw [← hs₁, e]; exact .inr rfl
  refine ⟨fun ψ' hψ' f i hp => ?_, fun ψ' hψ' p l hl => ?_, fun l hl => ?_, fun f i l hl => ?_, hacyc, hfresh⟩
  · obtain ⟨ψ₀, hψ₀, hv⟩ := key ψ' hψ'
    exact sgood_bind_read hs (fun f i => by rw [hposS]) (fun f i => htyS _) hψ₀ (fun f i hp => hv _ hp) f i hp
  · obtain ⟨ψ₀, hψ₀, hv⟩ := key ψ' hψ'
    rw [hshapeS, ← hs₁] at hl
    have hl' := takeAll_shape s Ls hl
    have hp : p ∈ s.positions := (hs.acyc.2.2 p l hl').1
    rw [hHT]
    rcases hv p hp with e | e
    · rw [e]; exact hs.holder ψ₀ hψ₀ p l hl'
    · rw [e]; exact .moved _
  · rw [hHT, hHM]; exact hs.held l (hlive_rev l hl)
  · rw [hshapeS, ← hs₁] at hl
    rw [htyS, hHT]; exact hs.holderTy f i l (takeAll_shape s Ls hl)

/-! ## The state after a call returning a borrow -/

theorem tyAt_pushTempShaped (s : SState) (v : SVal) (l : Nat) (q : Pos) :
    (s.pushTempShaped v l).tyAt q = s.tyAt q := by
  unfold SState.pushTempShaped; dsimp only
  split
  · exact tyAt_pushTemp s v q
  · exact tyAt_pushTemp s v q

theorem heldTy_pushTempShaped (s : SState) (v : SVal) (l : Nat) : (s.pushTempShaped v l).heldTy = s.heldTy := by
  unfold SState.pushTempShaped; dsimp only; split <;> rfl

theorem heldMem_pushTempShaped (s : SState) (v : SVal) (l : Nat) : (s.pushTempShaped v l).heldMem = s.heldMem := by
  unfold SState.pushTempShaped; dsimp only; split <;> rfl

/-- The state after a call returning a borrow, from the taken state `s₁`: the counter past the fresh
label `s₁.nextLoan`, every position rewritten (`g`), the label parked with `c`, its sites, content type
and record set. -/
noncomputable def parkState (s₁ : SState) (g : Pos → SVal → SVal) (c : Sem) (le : List Site) (Tk : TyM) : SState :=
  ((((SState.mk s₁.env s₁.shape (s₁.nextLoan + 1) s₁.lent s₁.heldTy s₁.heldMem).mapVals g).pushTempShaped
    (fun _ => c) s₁.nextLoan).setLent s₁.nextLoan le |>.setHeldTy s₁.nextLoan Tk).setHeldMem s₁.nextLoan c

/-- **The state after a call returning a borrow**, abstractly (`park_fix_inv`'s shape): the borrow
arguments' holders taken (`Ls`), the fresh label `k` parked with a member `c` of its content type `Tk`,
and every old position read at the future fixed at the finals `fx x` (where `k`'s final content
decodes to `x`) or `ee` (where it does not), each covering the taken labels with open members
of their content types. -/
theorem sgood_park_fix {dm : DataModel} {Γ : List IndDecl} {φ : Future} {s : SState} (hs : SGood dm Γ φ s)
    {X : Type u} (Ls : List Nat) (dec : Sem → Option X) (fx : X → List (Nat × Sem)) (ee : List (Nat × Sem))
    (le : List Site) (Tk : TyM) (c : Sem) (hc : c ∈ₛ[dm.read] Tk) (g : Pos → SVal → SVal)
    (hcov : ∀ x, ∀ l ∈ Ls, l ∈ (fx x).map (·.1)) (hcovE : ∀ l ∈ Ls, l ∈ ee.map (·.1))
    (hFm : ∀ x y f, (y, f) ∈ fx x → f ∈ₛ[dm.read] s.heldTy y)
    (hdec : ∀ v, v ∈ₛ[dm.read] Tk → (dec v).isSome)
    (hFl : ∀ x, ∀ y ∈ (fx x).map (·.1), y ∈ s.liveLabels ∨ ∀ p, Indep y (s.valAt p))
    (hEl : ∀ y ∈ ee.map (·.1), y ∈ s.liveLabels ∨ ∀ p, Indep y (s.valAt p))
    (hg : ∀ p v ψ, (∃ x, dec (ψ (Ls.foldl SState.takeLabel s).nextLoan) = some x ∧ g p v ψ = v (ψ.updList (fx x))) ∨
      (dec (ψ (Ls.foldl SState.takeLabel s).nextLoan) = none ∧ g p v ψ = v (ψ.updList ee)))
    (hacyc : SState.RInv (fun _ => True) (parkState (Ls.foldl SState.takeLabel s) g c le Tk))
    (hfresh : (parkState (Ls.foldl SState.takeLabel s) g c le Tk).ReadsBelow) :
    SGood dm Γ φ (parkState (Ls.foldl SState.takeLabel s) g c le Tk) := by
  have hk : (Ls.foldl SState.takeLabel s).nextLoan = s.nextLoan := (SState.shapeSub_foldl_takeLabel Ls s).2
  have hpos₁ : (Ls.foldl SState.takeLabel s).positions = s.positions := SState.takeAll_positions s Ls
  have hval₁ := takeAll_valAt s Ls
  have hty₁ := takeAll_tyAt s Ls
  have hHT₁ := takeAll_heldTy s Ls
  have hHM₁ := takeAll_heldMem s Ls
  have hshape₁ : ∀ {p : Pos} {y : Nat}, (Ls.foldl SState.takeLabel s).shape p = some y → s.shape p = some y :=
    fun h => takeAll_shape s Ls h
  have hlive₁ : ∀ y, y ∈ s.liveLabels → y ∉ Ls → y ∈ (Ls.foldl SState.takeLabel s).liveLabels :=
    fun y hy hn => takeAll_live s Ls hy hn
  have hlive₁r : ∀ y, y ∈ (Ls.foldl SState.takeLabel s).liveLabels → y ∈ s.liveLabels :=
    fun y hy => takeAll_live_rev s Ls hy
  generalize Ls.foldl SState.takeLabel s = s₁ at *
  -- the stages
  generalize hS₃ : (SState.mk s₁.env s₁.shape (s₁.nextLoan + 1) s₁.lent s₁.heldTy s₁.heldMem).mapVals g = S₃ at hacyc hfresh ⊢
  have hS : parkState s₁ g c le Tk =
      ((S₃.pushTempShaped (fun _ => c) s₁.nextLoan).setLent s₁.nextLoan le |>.setHeldTy s₁.nextLoan Tk).setHeldMem
        s₁.nextLoan c := by rw [← hS₃]; rfl
  rw [hS] at hacyc hfresh ⊢
  generalize hS₄ : S₃.pushTempShaped (fun _ => c) s₁.nextLoan = S₄ at hacyc hfresh ⊢
  generalize hSdef : ((S₄.setLent s₁.nextLoan le).setHeldTy s₁.nextLoan Tk).setHeldMem s₁.nextLoan c = S at hacyc hfresh ⊢
  generalize hkk : s₁.nextLoan = k at *
  -- facts of each stage
  have hpos₃ : S₃.positions = s.positions := by rw [← hS₃, SState.positions_mapVals, ← hpos₁]; rfl
  have hshape₃ : S₃.shape = s₁.shape := by rw [← hS₃]; rfl
  have hty₃ : ∀ q, S₃.tyAt q = s.tyAt q := fun q => by rw [← hS₃, tyAt_mapVals, ← hty₁ q]; rfl
  have hHT₃ : S₃.heldTy = s.heldTy := by rw [← hS₃, ← hHT₁]; rfl
  have hHM₃ : S₃.heldMem = s.heldMem := by rw [← hS₃, ← hHM₁]; rfl
  have hval₃ : ∀ p ∈ s.positions, S₃.valAt p = g p (s₁.valAt p) := by
    intro p hp
    rw [← hS₃, SState.valAt_mapVals_of_mem _ _ _ (by rw [← hpos₁] at hp; exact hp)]; rfl
  have hposS : S.positions = (S₃.pushTemp fun _ => c).positions := by
    rw [← hSdef, ← hS₄]; exact SState.positions_pushTempShaped _ _ _
  have hvalS : ∀ q, S.valAt q = (S₃.pushTemp fun _ => c).valAt q := by
    intro q; rw [← hSdef, ← hS₄]; exact SState.valAt_pushTempShaped _ _ _ q
  have htyS : ∀ q, S.tyAt q = s.tyAt q := by
    intro q; rw [← hSdef, ← hS₄]; show (S₃.pushTempShaped _ _).tyAt q = _; rw [tyAt_pushTempShaped, hty₃]
  have hshapeS : S.shape = S₄.shape := by rw [← hSdef]; rfl
  have hHTS : ∀ y, S.heldTy y = if y = k then Tk else s.heldTy y := by
    intro y; rw [← hSdef, ← hS₄]
    show (if y = k then Tk else (S₃.pushTempShaped _ _).heldTy y) = _
    rw [heldTy_pushTempShaped, hHT₃]
  have hHMS : ∀ y, S.heldMem y = if y = k then c else s.heldMem y := by
    intro y; rw [← hSdef, ← hS₄]
    show (if y = k then c else (S₃.pushTempShaped _ _).heldMem y) = _
    rw [heldMem_pushTempShaped, hHM₃]
  have hliveS : S.liveLabels = S₄.liveLabels := by rw [← hSdef]; rfl
  have hlive₃ : S₃.liveLabels = s₁.liveLabels := by
    rw [← hS₃]; unfold SState.liveLabels; rw [SState.positions_mapVals]; rfl
  -- shapes are at positions, below the counter
  have hsa₃ : SState.ShapeAt S₃ := fun p x hp => by
    rw [hshape₃] at hp
    have h0 := hs.acyc.2.2 p x (hshape₁ hp)
    exact ⟨by rw [hpos₃]; exact h0.1, by rw [← hS₃]; show x < k + 1; omega⟩
  have hlt : ∀ y, y ∈ s.liveLabels → y < k := fun y hy => hk ▸ hs.live_lt hy
  have hliveS_rev : ∀ y, y ∈ S.liveLabels → y ∈ s.liveLabels ∨ y = k := by
    intro y hy
    rw [hliveS, ← hS₄] at hy
    rcases SState.live_pushTempShaped_new hsa₃ hy with h | h
    · exact .inl (hlive₁r y (by rw [← hlive₃]; exact h))
    · exact .inr h
  have hliveS_fwd : ∀ y, y ∈ s.liveLabels → y ∉ Ls → y ∈ S.liveLabels := by
    intro y hy hn
    rw [hliveS, ← hS₄]
    exact SState.live_pushTempShaped_old (by show y ∈ S₃.liveLabels; rw [hlive₃]; exact hlive₁ y hy hn)
  -- the old positions after the call
  have hvalOld : ∀ p ∈ s.positions, S.valAt p = g p (s₁.valAt p) := by
    intro p hp
    rw [hvalS, valAt_pushTemp_old _ _ (by rw [hpos₃]; exact hp), hval₃ p hp]
  have key : ∀ ψ', TypedF dm Γ φ S ψ' → ∃ ψ₀, TypedF dm Γ φ s ψ₀ ∧
      ∀ p ∈ s.positions, S.valAt p ψ' = s.valAt p ψ₀ ∨ S.valAt p ψ' = .moved := by
    intro ψ' hψ'
    -- with no frame there is no position: any typed future of `s` will do
    by_cases hkl : k ∈ S.liveLabels
    rotate_left
    · have he₃ : S₃.env = [] := Classical.byContradiction fun hne => hkl (by
        rw [hliveS, ← hS₄]; exact SState.live_pushTempShaped_self _ _ _ hne)
      have hnil : s.positions = [] := by rw [← hpos₃, SState.positions_eq, he₃]; rfl
      refine ⟨s.typedFuture φ, ⟨fun l hl => by simp [SState.typedFuture, hl], fun l hl => ?_⟩, fun p hp => ?_⟩
      · show WMem dm Γ (if l ∈ s.liveLabels then s.heldMem l else φ l) _
        rw [if_pos hl]; exact hs.held l hl
      · rw [hnil] at hp; cases hp
    -- the finals the future fixes: `k` holds a member of its content type at a typed future (ruling
    -- (A)), which decodes, so the undecodable branch is not taken
    obtain ⟨Fx, hFxm, hFxl, hFxc, hgx⟩ : ∃ Fx : List (Nat × Sem), (∀ y f, (y, f) ∈ Fx → f ∈ₛ[dm.read] s.heldTy y) ∧
        (∀ y ∈ Fx.map (·.1), y ∈ s.liveLabels ∨ ∀ p, Indep y (s.valAt p)) ∧ (∀ l ∈ Ls, l ∈ Fx.map (·.1)) ∧
        ∀ p v, g p v ψ' = v (ψ'.updList Fx) := by
      cases hd : dec (ψ' k) with
      | none =>
        exfalso
        have hk := hψ'.2 k hkl
        have hk' : ψ' k ∈ₛ[dm.read] Tk := by
          have : WMem dm Γ (ψ' k) (S.heldTy k) := hk
          rw [hHTS, if_pos rfl] at this; exact this
        have := hdec _ hk'
        rw [hd] at this; cases this
      | some x =>
        refine ⟨fx x, hFm x, hFl x, hcov x, fun p v => ?_⟩
        rcases hg p v ψ' with ⟨x', hx, e⟩ | ⟨hx, -⟩
        · rw [hd] at hx; cases hx; exact e
        · rw [hd] at hx; cases hx
    obtain ⟨ψ₀, hψ₀, heq⟩ := typed_transport (φ := φ) Fx [k] ψ' hFxm hFxl
      (fun y hy => by
        simp only [List.mem_singleton] at hy; subst hy
        exact ⟨fun h => Nat.lt_irrefl _ (hlt _ h), fun p => hs.indep_fresh p (by omega)⟩)
      (fun y hy hn => by
        have h1 := hψ'.2 y (hliveS_fwd y hy fun hL => hn (hFxc y hL))
        rwa [hHTS, if_neg (Nat.ne_of_lt (hlt y hy))] at h1)
      (fun y hy hn hk' => hψ'.1 y fun h => by
        rcases hliveS_rev y h with h | h
        · exact hy h
        · exact hk' (by simp [h]))
    refine ⟨ψ₀, hψ₀, fun p hp => ?_⟩
    rw [hvalOld p hp, hgx]
    rcases hval₁ p with e | e
    · rw [e]; exact .inl (heq p)
    · rw [e]; exact .inr rfl
  have hposB : ∀ f i, Pos.bind f i ∈ S.positions ↔ Pos.bind f i ∈ s.positions := by
    intro f i; rw [hposS, bind_mem_pushTemp, hpos₃]
  -- a holder after: an old one, or the parked borrow
  have hholder : ∀ p y, S.shape p = some y →
      (p ∈ s.positions ∧ s.shape p = some y ∧ y ≠ k) ∨ (p ∉ s.positions ∧ y = k ∧ ∀ ψ, S.valAt p ψ = c) := by
    intro p y hp
    by_cases hps : p ∈ s.positions
    · rw [hshapeS, ← hS₄, SState.pushTempShaped_shape_old _ _ _ (by rw [hpos₃]; exact hps), hshape₃] at hp
      have h0 := hshape₁ hp
      exact .inl ⟨hps, h0, Nat.ne_of_lt (hk ▸ (hs.acyc.2.2 p y h0).2)⟩
    · have hpS : p ∈ S.positions := (hacyc.2.2 p y hp).1
      refine .inr ⟨hps, ?_, fun ψ => ?_⟩
      · rw [hshapeS, ← hS₄] at hp
        obtain ⟨T, hT⟩ := SState.pushTempShaped_shape S₃ (fun _ => c) k
        rw [hT] at hp
        split at hp
        · cases hp; rfl
        · rw [hshape₃] at hp; exact absurd (hs.acyc.2.2 p y (hshape₁ hp)).1 hps
      · rw [hvalS, valAt_pushTemp_new _ _ (by rw [← hposS]; exact hpS) (by rw [hpos₃]; exact hps)]
  refine ⟨fun ψ' hψ' f i hp => ?_, fun ψ' hψ' p l hl => ?_, fun l hl => ?_, fun f i l hl => ?_, hacyc, hfresh⟩
  · obtain ⟨ψ₀, hψ₀, hv⟩ := key ψ' hψ'
    exact sgood_bind_read hs hposB (fun f i => htyS _) hψ₀ (fun f i hp => hv _ hp) f i hp
  · rcases hholder p l hl with ⟨hp, h0, hne⟩ | ⟨-, rfl, hc'⟩
    · obtain ⟨ψ₀, hψ₀, hv⟩ := key ψ' hψ'
      rw [hHTS, if_neg hne]
      rcases hv p hp with e | e
      · rw [e]; exact hs.holder ψ₀ hψ₀ p l h0
      · rw [e]; exact .moved _
    · rw [hHTS, if_pos rfl, hc']
      exact .mem hc
  · rw [hHTS, hHMS]
    rcases hliveS_rev l hl with h | rfl
    · rw [if_neg (Nat.ne_of_lt (hlt l h)), if_neg (Nat.ne_of_lt (hlt l h))]; exact hs.held l h
    · rw [if_pos rfl, if_pos rfl]; exact hc
  · rcases hholder _ l hl with ⟨hp, h0, hne⟩ | ⟨hp, -, -⟩
    · rw [htyS, hHTS, if_neg hne]; exact hs.holderTy f i l h0
    · exact absurd ((hposB f i).1 (hacyc.2.2 _ l hl).1) hp

/-! ## A call returning data -/

theorem callOfLS_sgood_data {dm : DataModel} {Γ : List IndDecl} {φ : Future} (Lv : Lvl.{u}) (hE : Lv.EncMem)
    (hR : Lv.read = dm.read) {C : Type u} (t : Tel Lv.Code PUnit C) (fv : Sem) (args : List Res)
    {s s' : SState} {r : Res} (hs : SGood dm Γ φ s)
    (ht : ∀ (i l : Nat), (((args.zip (telRefsL Lv t (args.map (·.1)))).filter (·.2)).map (·.1.2.label))[i]? = some (some l) →
      s.heldTy l = (telRefTysL Lv t (args.map (·.1))).getD i TyM.err)
    (hlive : ∀ l, some l ∈ ((args.zip (telRefsL Lv t (args.map (·.1)))).filter (·.2)).map (·.1.2.label) →
      l ∈ s.liveLabels ∨ ∀ p, Indep l (s.valAt p))
    {r' : Sem} {T' : TyM} {finals : List Sem}
    (happ : applyFnL Lv t fv (args.map (·.1)) = some (.data r' T' finals))
    (h : callOfL Lv t fv args s = some (r, s')) : LabOk dm s' r ∧ SGood dm Γ φ s' := by
  have hacyc := callOfLS_rinv Lv t fv args hs.acyc h
  have hfresh := callOfLS_readsBelow Lv t fv args s hs.fresh h
  -- the finals: members of the parameters' content types, one per borrow parameter
  obtain ⟨F, -, happ'⟩ : ∃ F, Lv.unpack C fv = some F ∧
      applyTelL Lv t (fun _ => []) F (args.map (·.1)) = some (.data r' T' finals) := by
    unfold applyFnL at happ
    cases hu : Lv.unpack C fv with
    | none => rw [hu] at happ; cases happ
    | some F => rw [hu] at happ; exact ⟨F, rfl, happ⟩
  have hfm : MemList Lv.read finals (telRefTysL Lv t (args.map (·.1))) := by
    simpa [FinalsMem] using applyTelL_finals Lv hE t (fun _ => []) [] (fun _ => .nil) F _ _ happ'
  obtain ⟨hlen, hfin⟩ := applyTelL_len Lv t (fun _ => []) F _ 0 (fun _ => rfl) _ happ'
  simp only [List.length_map] at hlen
  simp only [Nat.zero_add] at hfin
  have hcov := fixes_cover (((args.zip (telRefsL Lv t (args.map (·.1)))).filter (·.2)).map (·.1.2.label)) finals
    (by rw [List.length_map, zip_filter_len args _ (by simpa using hlen), hfin]; exact Nat.le_refl _)
  have hFm := fixes_pmem Lv t args hR ht hfm
  have hFl := fixes_keys_live Lv t args hlive finals
  -- the state
  unfold callOfL at h
  dsimp only at h
  rw [happ] at h
  simp only [Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  refine ⟨fun l hl => by simp [TyS.plain] at hl, ?_⟩
  exact sgood_mapVals_fix hs _ _ hcov hFm hFl hacyc hfresh

end Ochr.Meaning.Strict

namespace Ochr.Meaning.Strict
open Ochr.Meaning

universe v

/-! ## A call returning a borrow -/

/-- **A level's codes' members are encodings** (the converse of `Lvl.EncMem`). -/
def _root_.Ochr.Meaning.Lvl.MemEnc (L : Lvl.{v}) : Prop :=
  ∀ {A : Type v} (c : L.Code A) (x : Sem), x ∈ₛ[L.read] L.toTy c → ∃ a, L.enc c a = x

/-- **A member of a code's type decodes** (ruling (A): at a typed future a returned borrow's label
holds a member of its code's type, so `callOfL`'s undecodable branch is not taken there). -/
theorem _root_.Ochr.Meaning.Lvl.dec_of_mem {L : Lvl.{v}} (hL : L.Lawful) (hM : L.MemEnc) {A : Type v}
    (c : L.Code A) (x : Sem) (h : x ∈ₛ[L.read] L.toTy c) : (L.dec c x).isSome := by
  obtain ⟨a, rfl⟩ := hM c x h
  rw [hL.dec_enc]; rfl

theorem lvl0_memEnc (R : DataRead) : (lvl0 R).MemEnc := fun _ _ h => h

theorem lvl1_memEnc (R : DataRead) : (lvl1 R).MemEnc := by
  intro A c x h
  cases c with
  | lift B c => obtain ⟨b, hb⟩ := h; exact ⟨ULift.up b, hb⟩
  | univ0 => exact h
  | univ1 => exact h
  | pi C t => exact h

theorem lvl2_memEnc (R : DataRead) : (lvl2 R).MemEnc := by
  intro A c x h
  cases c with
  | lift B c =>
    cases c with
    | lift B' c' => obtain ⟨b, hb⟩ := h; exact ⟨ULift.up (ULift.up b), hb⟩
    | univ0 => obtain ⟨b, hb⟩ := h; exact ⟨ULift.up b, hb⟩
    | univ1 => obtain ⟨b, hb⟩ := h; exact ⟨ULift.up b, hb⟩
    | pi C t => obtain ⟨b, hb⟩ := h; exact ⟨ULift.up b, hb⟩
  | univ2 => exact h
  | pi C t => exact h

theorem callOfLS_sgood_ref {dm : DataModel} {Γ : List IndDecl} {φ : Future} (Lv : Lvl.{v}) (hE : Lv.EncMem)
    (hL : Lv.Lawful) (hME : Lv.MemEnc) (hR : Lv.read = dm.read) {C : Type v} (t : Tel Lv.Code PUnit C) (fv : Sem) (args : List Res)
    {s s' : SState} {r : Res} (hs : SGood dm Γ φ s)
    (ht : ∀ (i l : Nat), (((args.zip (telRefsL Lv t (args.map (·.1)))).filter (·.2)).map (·.1.2.label))[i]? = some (some l) →
      s.heldTy l = (telRefTysL Lv t (args.map (·.1))).getD i TyM.err)
    (hlive : ∀ l, some l ∈ ((args.zip (telRefsL Lv t (args.map (·.1)))).filter (·.2)).map (·.1.2.label) →
      l ∈ s.liveLabels ∨ ∀ p, Indep l (s.valAt p))
    {U : Type v} {c : Lv.Code U} {fwd : U} {back : U → List Sem}
    (happ : applyFnL Lv t fv (args.map (·.1)) = some (.ref U c fwd back))
    (h : callOfL Lv t fv args s = some (r, s')) : LabOk dm s' r ∧ SGood dm Γ φ s' := by
  have hacyc := callOfLS_rinv Lv t fv args hs.acyc h
  have hfresh := callOfLS_readsBelow Lv t fv args s hs.fresh h
  obtain ⟨F, -, happ'⟩ : ∃ F, Lv.unpack C fv = some F ∧
      applyTelL Lv t (fun _ => []) F (args.map (·.1)) = some (.ref U c fwd back) := by
    unfold applyFnL at happ
    cases hu : Lv.unpack C fv with
    | none => rw [hu] at happ; cases happ
    | some F => rw [hu] at happ; exact ⟨F, rfl, happ⟩
  have hfm : ∀ x, MemList Lv.read (back x) (telRefTysL Lv t (args.map (·.1))) := by
    intro x
    have := applyTelL_finals Lv hE t (fun _ => []) [] (fun _ => .nil) F _ _ happ'
    simpa [FinalsMem] using this x
  obtain ⟨hlen, hfin⟩ := applyTelL_len Lv t (fun _ => []) F _ 0 (fun _ => rfl) _ happ'
  simp only [List.length_map] at hlen
  simp only [Nat.zero_add] at hfin
  have hrl : (((args.zip (telRefsL Lv t (args.map (·.1)))).filter (·.2)).map (·.1.2.label)).length =
      ((telRefsL Lv t (args.map (·.1))).filter id).length := by
    rw [List.length_map, zip_filter_len args _ (by simpa using hlen)]
  have hcov := fun x => fixes_cover (((args.zip (telRefsL Lv t (args.map (·.1)))).filter (·.2)).map (·.1.2.label))
    (back x) (by rw [hrl, hfin x]; exact Nat.le_refl _)
  have hcovE := fixes_cover (((args.zip (telRefsL Lv t (args.map (·.1)))).filter (·.2)).map (·.1.2.label))
    ((((args.zip (telRefsL Lv t (args.map (·.1)))).filter (·.2)).map (·.1.2.label)).map fun _ => Sem.moved)
    (by simp only [List.length_map]; exact Nat.le_refl _)
  have hFm := fun x => fixes_pmem Lv t args hR ht (hfm x)
  have hFl := fun x => fixes_keys_live Lv t args hlive (back x)
  have hEl := fixes_keys_live Lv t args hlive
    ((((args.zip (telRefsL Lv t (args.map (·.1)))).filter (·.2)).map (·.1.2.label)).map fun _ => Sem.moved)
  have hc : Lv.enc c fwd ∈ₛ[dm.read] Lv.toTy c := hR ▸ hE c fwd
  unfold callOfL at h
  dsimp only at h
  rw [happ] at h
  simp only [SState.freshLoan, Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  refine ⟨fun l hl => ?_, ?_⟩
  · simp only [Option.some.injEq] at hl
    subst hl
    refine ⟨by simp [SState.setHeldMem, SState.setHeldTy], ?_⟩
    simpa [SState.setHeldMem, SState.setHeldTy] using hc
  · refine sgood_park_fix hs _ (Lv.dec c) _ _ _ _ _ hc _ hcov hcovE hFm
      (fun v hv => Lvl.dec_of_mem hL hME c v (hR ▸ hv)) hFl hEl ?_ hacyc hfresh
    intro p w ψ
    cases hd : Lv.dec c (ψ ((((((args.zip (telRefsL Lv t (args.map (·.1)))).filter (·.2)).map (·.1.2.label)).filterMap id)).foldl
        SState.takeLabel s).nextLoan) with
    | none => exact .inr ⟨rfl, by simp only [hd]⟩
    | some x => exact .inl ⟨x, rfl, by simp only [hd]⟩

end Ochr.Meaning.Strict

namespace Ochr.Meaning.Strict
open Ochr.Meaning

universe w

/-- A call at level `Lv` (`callOfL`) keeps the invariant. -/
theorem callOfLS_sgood {dm : DataModel} {Γ : List IndDecl} {φ : Future} (Lv : Lvl.{w}) (hE : Lv.EncMem)
    (hL : Lv.Lawful) (hME : Lv.MemEnc)
    (hR : Lv.read = dm.read) {C : Type w} (t : Tel Lv.Code PUnit C) (fv : Sem) (args : List Res)
    {s s' : SState} {r : Res} (hs : SGood dm Γ φ s)
    (ht : ∀ (i l : Nat), (((args.zip (telRefsL Lv t (args.map (·.1)))).filter (·.2)).map (·.1.2.label))[i]? = some (some l) →
      s.heldTy l = (telRefTysL Lv t (args.map (·.1))).getD i TyM.err)
    (hlive : ∀ l, some l ∈ ((args.zip (telRefsL Lv t (args.map (·.1)))).filter (·.2)).map (·.1.2.label) →
      l ∈ s.liveLabels ∨ ∀ p, Indep l (s.valAt p))
    (h : callOfL Lv t fv args s = some (r, s')) : LabOk dm s' r ∧ SGood dm Γ φ s' := by
  cases happ : applyFnL Lv t fv (args.map (·.1)) with
  | none => unfold callOfL at h; dsimp only at h; rw [happ] at h; cases h
  | some res =>
    cases res with
    | data r' T' finals => exact callOfLS_sgood_data Lv hE hR t fv args hs ht hlive happ h
    | ref U c fwd back => exact callOfLS_sgood_ref Lv hE hL hME hR t fv args hs ht hlive happ h

/-- **A call keeps the invariant**, and its result's label (a returned borrow's, fresh) records the
result's type. Beyond the stub's hypotheses: each borrow argument's label is live or read by no
position (`hlive`; `RunPresInd`'s `LoU` of each argument's run), see the module docstring. `hf` is
not needed. -/
theorem callOfS_sgood {K : RunCtx} {φ : Future} {fv : Res} {as : List Res}
    {s s' : SState} {r : Res} (hs : SGood K.dm K.Γ φ s) (_hf : GoodRes K.dm.read fv)
    (ht : BorrowArgsTyped K.dm.read fv as s)
    (h : callOf K.dm.read fv as s = some (r, s')) :
    LabOk K.dm s' r ∧ SGood K.dm K.Γ φ s' := by
  -- each borrow argument's label is live (the strict test)
  have hlive : ∀ l, some l ∈ refLabelsOf K.dm.read fv as → l ∈ s.liveLabels ∨ ∀ p, Indep l (s.valAt p) := by
    intro l hl
    obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp hl
    exact .inl (ht i l hi).1
  have ht' := fun i l h => (ht i l h).2
  clear ht
  rcases fv with ⟨fv, ⟨T, lab⟩⟩
  unfold callOf at h
  cases T with
  | t0 A c =>
    cases c with
    | pi C t => exact callOfLS_sgood (lvl0 K.dm.read) (lvl0_encMem _) (lvl0_lawful _) (lvl0_memEnc _) rfl t fv as hs ht' hlive h
    | _ => cases h
  | t1 A c =>
    cases c with
    | pi C t => exact callOfLS_sgood (lvl1 K.dm.read) (lvl1_encMem _) (lvl1_lawful _) (lvl1_memEnc _) rfl t fv as hs ht' hlive h
    | _ => cases h
  | t2 A c =>
    cases c with
    | pi C t => exact callOfLS_sgood (lvl2 K.dm.read) (lvl2_encMem _) (lvl2_lawful _) (lvl2_memEnc _) rfl t fv as hs ht' hlive h
    | _ => cases h

end Ochr.Meaning.Strict
