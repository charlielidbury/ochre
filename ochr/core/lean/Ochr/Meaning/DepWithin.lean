import Ochr.Meaning.Locality

/-!
# Dependence within sites (docs/31 D67)

The reference-only invariant that replaces the old `access_FT` in its static form: a place's
VALUE read at a path depends on the future only at labels that are not live, or that are lent at
the place on a path comparable with the one read (by key, `*` erased). Typed or not. The value
only: a data value describes itself, so the value read needs no type to be found, and a field is
typed at the closed future, as reads are (`Regress/DepSitesMore.lean`, the dependent pair).

Step 3, risk first: the clauses that write a label-reading meaning. Here `callOf`'s two rows: the
borrow-free row fixes the consumed argument labels to the finals (`dws_take_fix`), the borrow row
reads the new label through the backward function at the lent places, where it is lent as a fill
(`dws_park_fix`). The second needs that the run's positions read no label at or above the counter
(`FreshReads`, from (I1) and `ShapeAt`) and that the consumed labels are live.
-/

namespace Ochr.Meaning

variable (dm : DataModel) (Γ : List IndDecl)

/-- The value read off `v` at `steps`. -/
noncomputable def readV (v : Sem) (steps : List Step) : Option Sem :=
  (Sem.follow dm Γ (.plain TyM.err) v steps).map Prod.fst

/-- The value component of a reading does not read the type it starts at. -/
theorem follow_fst_indep : ∀ (steps : List Step) (s : Sem) (T T' : TyS),
    (Sem.follow dm Γ T s steps).map Prod.fst = (Sem.follow dm Γ T' s steps).map Prod.fst
  | [], _, _, _ => rfl
  | .deref :: ss, s, T, T' => by
    simp only [Sem.follow, Sem.step, Option.bind_some]
    exact follow_fst_indep ss s T T'
  | .proj i :: ss, s, T, T' => by
    have e : Sem.step dm Γ T (.proj i) s = Sem.step dm Γ T' (.proj i) s := by cases i <;> rfl
    simp only [Sem.follow, e]
  | .field g :: ss, s, T, T' => by
    have e : Sem.step dm Γ T (.field g) s = Sem.step dm Γ T' (.field g) s := rfl
    simp only [Sem.follow, e]

theorem follow_map_fst (T : TyS) (v : Sem) (steps : List Step) :
    (Sem.follow dm Γ T v steps).map Prod.fst = readV dm Γ v steps :=
  follow_fst_indep dm Γ steps v T _

/-- **Dependence within sites**: two futures that differ only at live labels with no site at `p` on
a path comparable with `steps` give the same value read at `p` and `steps`, typed or not. -/
def DepWithinSites (s : SState) : Prop :=
  ∀ (p : Pos) (steps : List Step) (ψ ψ' : Future),
    (∀ l, ψ l ≠ ψ' l → s.Live l ∧ s.reached p (dataHit steps) l = false) →
    readV dm Γ (s.valAt p ψ) steps = readV dm Γ (s.valAt p ψ') steps

/-- The positions read no label at or above the counter. -/
def FreshReads (s : SState) : Prop := ∀ p, FT (· < s.nextLoan) (s.valAt p)

theorem freshReads_of_inv1 {s : SState} (h1 : SState.Inv1 (· < s.nextLoan) s) (hsa : SState.ShapeAt s) :
    FreshReads s := fun p => (h1 p).mono fun y hy => by
  rcases hy with hy | hy
  · exact hy
  · obtain ⟨q, hq, hs⟩ := (SState.live_iff s y).mp hy
    exact (hsa q y hs).2

namespace SState

theorem takeLabel_lent (s : SState) (l : Nat) : (s.takeLabel l).lent = s.lent := by
  unfold takeLabel
  split
  · rename_i r _
    show (s.setAt r fun _ => .moved).lent = s.lent
    unfold setAt; split <;> rfl
  · rfl

theorem takeAll_lent : ∀ (ls : List Nat) (s : SState), (ls.foldl takeLabel s).lent = s.lent
  | [], _ => rfl
  | l :: ls, s => by rw [List.foldl_cons, takeAll_lent ls, takeLabel_lent]

end SState

open SState

/-- **`callOf`'s borrow-free row**: the consumed holders are taken and every position reads the
consumed labels fixed. A position that read one of them now reads its final; nothing reads it
after (it is not live, and fixed). -/
theorem dws_take_fix {s : SState} (hd : DepWithinSites dm Γ s) (ls : List Nat) (F : List (Nat × Sem)) :
    DepWithinSites dm Γ ((ls.foldl takeLabel s).mapVals fun _ v φ' => v (φ'.updList F)) := by
  intro p steps ψ ψ' hψ
  by_cases hp : p ∈ (ls.foldl takeLabel s).positions
  · rw [valAt_mapVals_of_mem _ _ _ hp]
    rcases takeAll_valAt p ls s with e | e
    · rw [e]
      apply hd p steps
      intro l hl
      have hlF : l ∉ F.map (·.1) := fun hm => hl (Future.updList_agree_mem F ψ ψ' l hm)
      rw [Future.updList_of_not_mem F ψ l hlF, Future.updList_of_not_mem F ψ' l hlF] at hl
      obtain ⟨hlive, hr⟩ := hψ l hl
      refine ⟨takeAll_live_rev ls (live_mapVals.mp hlive), ?_⟩
      have hlent : ((ls.foldl takeLabel s).mapVals fun _ v φ' => v (φ'.updList F)).lent = s.lent := by
        show (ls.foldl takeLabel s).lent = s.lent
        exact takeAll_lent ls s
      unfold SState.reached at hr ⊢
      rw [hlent] at hr
      exact hr
    · rw [e]
  · rw [valAt_mapVals_of_not_mem _ _ _ hp]

/-- **`callOf`'s borrow row** (`park_fix_inv`'s shape): the consumed holders are taken, a fresh
label `k` is parked with the forward value, every position reads the consumed labels fixed through
the backward function at `k`'s final content (or to the error fixing), and `k` is lent as a fill
wherever a consumed label was lent. A position that read a consumed label on a path comparable
with the one read now reads `k` there, where `k` is lent; one that did not reads neither. -/
theorem dws_park_fix.{u} {s : SState} (hd : DepWithinSites dm Γ s) (hfr : FreshReads s) (hsa : ShapeAt s)
    {X : Type u} (ls : List Nat) (hls : ∀ j ∈ ls, s.Live j)
    (dec : Sem → Option X) (fx : X → List (Nat × Sem)) (ee : List (Nat × Sem))
    (hkx : ∀ x, ∀ y ∈ (fx x).map (·.1), y ∈ ls) (hke : ∀ y ∈ ee.map (·.1), y ∈ ls)
    (ht : Nat → TyM) (c : Sem) (g : Pos → SVal → SVal)
    (hg : ∀ p v ψ, (∃ x, dec (ψ (ls.foldl takeLabel s).nextLoan) = some x ∧ g p v ψ = v (ψ.updList (fx x))) ∨
      (dec (ψ (ls.foldl takeLabel s).nextLoan) = none ∧ g p v ψ = v (ψ.updList ee)))
    (lentK : List Site) (hlK : ∀ j ∈ ls, ∀ x ∈ s.lent j, ∃ y ∈ lentK, y.pos = x.pos ∧ y.path = x.path) (T : TyM) :
    DepWithinSites dm Γ (((((SState.mk (ls.foldl takeLabel s).env (ls.foldl takeLabel s).shape
        ((ls.foldl takeLabel s).nextLoan + 1) (ls.foldl takeLabel s).lent ht).mapVals g).pushTempShaped (fun _ => c)
        (ls.foldl takeLabel s).nextLoan).setLent (ls.foldl takeLabel s).nextLoan lentK).setHeldTy (ls.foldl takeLabel s).nextLoan T) := by
  have hk' : (ls.foldl takeLabel s).nextLoan = s.nextLoan := (shapeSub_foldl_takeLabel ls s).2
  have hpos₁ : (ls.foldl takeLabel s).positions = s.positions := takeAll_positions s ls
  have hlent₁ : (ls.foldl takeLabel s).lent = s.lent := takeAll_lent ls s
  generalize hs₁ : ls.foldl takeLabel s = s₁ at hg hk' hpos₁ hlent₁ ⊢
  generalize hk : s₁.nextLoan = k at hg hk' ⊢
  generalize hs₂ : (SState.mk s₁.env s₁.shape (k + 1) s₁.lent ht).mapVals g = s₃
  have hpos₃ : s₃.positions = s.positions := by rw [← hs₂, positions_mapVals]; exact hpos₁
  have hlive₃ : ∀ y, s₃.Live y ↔ s₁.Live y := by intro y; rw [← hs₂, live_mapVals]; rfl
  have hshape₃ : s₃.shape = s₁.shape := by rw [← hs₂]; rfl
  have hval₃ : ∀ q ∈ s.positions, s₃.valAt q = g q (s₁.valAt q) := by
    intro q hq
    rw [← hs₂]
    exact valAt_mapVals_of_mem _ _ q (by show q ∈ s₁.positions; rw [hpos₁]; exact hq)
  have hsa₃ : ShapeAt s₃ := by
    intro p x hp
    rw [hshape₃] at hp
    have hp' := takeAll_shape_some ls (by rw [hs₁]; exact hp)
    refine ⟨by rw [hpos₃]; exact (hsa p x hp').1, ?_⟩
    rw [← hs₂]; show x < k + 1
    have := (hsa p x hp').2; omega
  have hnew : ∀ y, (s₃.pushTempShaped (fun _ => c) k).Live y → s.Live y ∨ y = k := by
    intro y hy
    rcases live_pushTempShaped_new hsa₃ hy with h | h
    · rw [hlive₃, ← hs₁] at h; exact .inl (takeAll_live_rev ls h)
    · exact .inr h
  have hv : ∀ q, (s₃.pushTempShaped (fun _ => c) k).valAt q = s₃.valAt q ∨
      (s₃.pushTempShaped (fun _ => c) k).valAt q = fun _ => c := by
    intro q; rw [valAt_pushTempShaped]; exact valAt_pushTemp s₃ _ q
  have hlentF : ∀ y, y ≠ k → (((s₃.pushTempShaped (fun _ => c) k).setLent k lentK).setHeldTy k T).lent y = s.lent y := by
    intro y hy
    show (if y = k then lentK else (s₃.pushTempShaped (fun _ => c) k).lent y) = s.lent y
    rw [if_neg hy, ← hlent₁]
    unfold SState.pushTempShaped; dsimp only
    split <;> (rw [← hs₂]; rfl)
  intro q σ ψ ψ' hψ
  simp only [SState.setHeldTy_valAt, SState.setLent_valAt]
  -- what the reference does not read: the consumed labels where none is reached, and `k`
  have hfix : ∀ (χ : Future) (F : List (Nat × Sem)), (∀ y ∈ F.map (·.1), y ∈ ls) →
      (∀ j ∈ ls, s.reached q (dataHit σ) j = false) →
      readV dm Γ (s.valAt q (χ.updList F)) σ = readV dm Γ (s.valAt q χ) σ := by
    intro χ F hF hj
    apply hd q σ
    intro y hy
    have hyF : y ∈ F.map (·.1) :=
      Classical.byContradiction fun hn => hy (Future.updList_of_not_mem F χ y hn)
    exact ⟨hls y (hF y hyF), hj y (hF y hyF)⟩
  have hdiff : ∀ y, ψ y ≠ ψ' y → y ≠ k → s.Live y ∧ s.reached q (dataHit σ) y = false := by
    intro y hy hyk
    obtain ⟨hl, hr⟩ := hψ y hy
    refine ⟨(hnew y hl).resolve_right hyk, ?_⟩
    unfold SState.reached at hr ⊢
    rw [hlentF y hyk] at hr
    exact hr
  rcases hv q with e | e
  · rw [e]
    by_cases hq : q ∈ s.positions
    · rw [hval₃ q hq]
      rcases (show s₁.valAt q = s.valAt q ∨ s₁.valAt q = fun _ => .moved by rw [← hs₁]; exact takeAll_valAt q ls s)
        with e1 | e1
      · rw [e1]
        by_cases hkk : ψ k = ψ' k
        · rcases hg q (s.valAt q) ψ with ⟨x, hx, ex⟩ | ⟨hx, ex⟩ <;>
            rcases hg q (s.valAt q) ψ' with ⟨x', hx', ex'⟩ | ⟨hx', ex'⟩ <;> rw [hkk] at hx
          · rw [hx] at hx'; cases hx'
            rw [ex, ex']
            apply hd q σ
            intro y hy
            have hyF : y ∉ (fx x).map (·.1) := fun hm => hy (Future.updList_agree_mem _ ψ ψ' y hm)
            rw [Future.updList_of_not_mem _ ψ y hyF, Future.updList_of_not_mem _ ψ' y hyF] at hy
            exact hdiff y hy (fun e => hy (e ▸ hkk))
          · rw [hx] at hx'; cases hx'
          · rw [hx] at hx'; cases hx'
          · rw [ex, ex']
            apply hd q σ
            intro y hy
            have hyF : y ∉ ee.map (·.1) := fun hm => hy (Future.updList_agree_mem _ ψ ψ' y hm)
            rw [Future.updList_of_not_mem _ ψ y hyF, Future.updList_of_not_mem _ ψ' y hyF] at hy
            exact hdiff y hy (fun e => hy (e ▸ hkk))
        · -- `k` differs, so it is not reached here, and no consumed label is
          have hk2 := (hψ k hkk).2
          have hj : ∀ j ∈ ls, s.reached q (dataHit σ) j = false := by
            intro j hjm
            unfold SState.reached
            rw [List.any_eq_false]
            intro x hx hxr
            simp only [Bool.and_eq_true, decide_eq_true_eq] at hxr
            obtain ⟨y, hy, hyp, hypa⟩ := hlK j hjm x hx
            unfold SState.reached at hk2
            rw [List.any_eq_false] at hk2
            apply hk2 y (by show y ∈ (if k = k then lentK else _); rw [if_pos rfl]; exact hy)
            simp [hyp, hypa, hxr.1, hxr.2]
          have hg1 : ∀ χ : Future, readV dm Γ (g q (s.valAt q) χ) σ = readV dm Γ (s.valAt q χ) σ := by
            intro χ
            rcases hg q (s.valAt q) χ with ⟨x, -, ex⟩ | ⟨-, ex⟩ <;> rw [ex]
            · exact hfix χ _ (hkx x) hj
            · exact hfix χ _ hke hj
          rw [hg1, hg1]
          -- `k` is at the counter: the old positions do not read it
          have hfr' : s.valAt q ψ = s.valAt q (ψ.upd k (ψ' k)) := by
            apply hfr q
            intro y hy
            have : y ≠ k := by omega
            simp [Future.upd, this]
          rw [hfr']
          apply hd q σ
          intro y hy
          by_cases hyk : y = k
          · subst hyk; simp [Future.upd] at hy
          · rw [Future.upd_other _ _ hyk] at hy
            exact hdiff y hy hyk
      · rw [e1]
        rcases hg q (fun _ => .moved) ψ with ⟨_, -, ex⟩ | ⟨-, ex⟩ <;>
          rcases hg q (fun _ => .moved) ψ' with ⟨_, -, ex'⟩ | ⟨-, ex'⟩ <;> rw [ex, ex']
    · have hq₃ : q ∉ s₃.positions := by rw [hpos₃]; exact hq
      rw [valAt_of_not_mem _ _ hq₃]
  · rw [e]

/-! ## The rows of `callOf` -/

theorem fixes_keys : ∀ (ls : List (Option Nat)) (fs : List Sem),
    ∀ y ∈ ((ls.zip fs).filterMap fun (y : Option Nat × Sem) => y.1.map (·, y.2)).map (·.1), y ∈ ls.filterMap id
  | [], _, y, h => by simp at h
  | _ :: _, [], y, h => by simp at h
  | l? :: ls, f :: fs, y, h => by
    cases l? with
    | none =>
      simp only [List.zip_cons_cons, List.filterMap_cons, Option.map_none, id] at h ⊢
      exact fixes_keys ls fs y h
    | some k =>
      simp only [List.zip_cons_cons, List.filterMap_cons, Option.map_some, List.map_cons, List.mem_cons, id] at h ⊢
      rcases h with rfl | h
      · exact .inl rfl
      · exact .inr (fixes_keys ls fs y h)

/-- **`callOf`'s borrow-free row keeps the invariant.** -/
theorem dws_callOfL_data.{u} (Lv : Lvl.{u}) {C : Type u} (t : Tel Lv.Code PUnit C) (fv : Sem) (args : List Res)
    {s s' : SState} (hd : DepWithinSites dm Γ s) {res : Res} (h : callOfL Lv t fv args s = some (res, s'))
    {r : Sem} {T : TyM} {finals : List Sem} (happ : applyFnL Lv t fv (args.map (·.1)) = some (.data r T finals)) :
    DepWithinSites dm Γ s' := by
  unfold callOfL at h
  dsimp only at h
  rw [happ] at h
  simp only [Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨_, rfl⟩ := h
  exact dws_take_fix dm Γ hd _ _

/-- **`callOf`'s borrow row keeps the invariant**, when the run's positions read no label at or
above the counter and the borrow arguments' labels are live. -/
theorem dws_callOfL_ref.{u} (Lv : Lvl.{u}) {C : Type u} (t : Tel Lv.Code PUnit C) (fv : Sem) (args : List Res)
    {s s' : SState} (hd : DepWithinSites dm Γ s) (hfr : FreshReads s) (hsa : ShapeAt s)
    (hlive : ∀ a ∈ args, ∀ j, a.2.label = some j → s.Live j)
    {res : Res} (h : callOfL Lv t fv args s = some (res, s'))
    {U : Type u} {c : Lv.Code U} {fwd : U} {back : U → List Sem}
    (happ : applyFnL Lv t fv (args.map (·.1)) = some (.ref U c fwd back)) :
    DepWithinSites dm Γ s' := by
  unfold callOfL at h
  dsimp only at h
  rw [happ] at h
  simp only [SState.freshLoan, Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨_, rfl⟩ := h
  have hls : ∀ j ∈ (((args.zip (telRefsL Lv t (args.map (·.1)))).filter (·.2)).map (·.1.2.label)).filterMap id,
      s.Live j := by
    intro j hj
    rw [List.mem_filterMap] at hj
    obtain ⟨l?, hl?, hj⟩ := hj
    obtain ⟨⟨a, b⟩, hab, rfl⟩ := List.mem_map.mp hl?
    have ha := (List.mem_filter.mp hab).1
    exact hlive a (List.of_mem_zip ha).1 j hj
  have hkx : ∀ x, ∀ y ∈ (((((args.zip (telRefsL Lv t (args.map (·.1)))).filter (·.2)).map (·.1.2.label)).zip (back x)).filterMap
        fun (y : Option Nat × Sem) => y.1.map (·, y.2)).map (·.1),
      y ∈ (((args.zip (telRefsL Lv t (args.map (·.1)))).filter (·.2)).map (·.1.2.label)).filterMap id :=
    fun x y hy => fixes_keys _ _ y hy
  have hke : ∀ y ∈ (((((args.zip (telRefsL Lv t (args.map (·.1)))).filter (·.2)).map (·.1.2.label)).zip
        ((((args.zip (telRefsL Lv t (args.map (·.1)))).filter (·.2)).map (·.1.2.label)).map fun _ => Sem.err)).filterMap
        fun (y : Option Nat × Sem) => y.1.map (·, y.2)).map (·.1),
      y ∈ (((args.zip (telRefsL Lv t (args.map (·.1)))).filter (·.2)).map (·.1.2.label)).filterMap id :=
    fun y hy => fixes_keys _ _ y hy
  refine dws_park_fix dm Γ hd hfr hsa _ hls (Lv.dec c) _ _ hkx hke _ _ _ ?_ _ ?_ _
  · intro p v ψ
    cases hdc : Lv.dec c (ψ ((((((args.zip (telRefsL Lv t (args.map (·.1)))).filter (·.2)).map (·.1.2.label)).filterMap
        id)).foldl SState.takeLabel s).nextLoan) with
    | none => exact .inr ⟨rfl, by simp only [hdc]⟩
    | some x => exact .inl ⟨x, rfl, by simp only [hdc]⟩
  · intro j hj x hx
    refine ⟨{ x with fill := true }, ?_, rfl, rfl⟩
    rw [List.mem_map]
    refine ⟨x, List.mem_flatMap.mpr ⟨j, hj, ?_⟩, rfl⟩
    rw [takeAll_lent]; exact hx

end Ochr.Meaning
