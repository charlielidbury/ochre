import Ochr.Meaning.Mono

/-!
# Future-locality of semantic states (infrastructure for `run_congr` and the substitution lemmas)

A meaning `f : SVal` *factors through* a label set `S` (`FT S f`) when it reads the future only
at `S`: two futures that agree on `S` give the same meaning. "Factors through" rather than
pointwise independence (`Indep`), because a value can change when infinitely many labels change
together while depending on no single one; the two meet on finite sets (`FT.removeList`).

The invariant the run keeps, relative to the labels `L` at which two futures agree:
* (I1) every position factors through `L ∪ live(s)`;
* (I2) the holder of label `x` factors through the non-live labels of `L` and the live labels
  above `x`: holder chains are acyclic and label-ordered, so ending `x` removes every dependence
  on it, and the closed future's iteration reaches its fixpoint.

From them: after `access p` the position `p` factors through `L` (R1), and a read at the closed
future does not see the futures' difference (R2).
-/

namespace Ochr.Meaning

/-- `f` reads the future only at the labels in `S`. -/
def FT (S : Nat → Prop) (f : SVal) : Prop :=
  ∀ ψ ψ' : Future, (∀ l, S l → ψ l = ψ' l) → f ψ = f ψ'

/-- `f` does not read label `l`. -/
def Indep (l : Nat) (f : SVal) : Prop := ∀ (ψ : Future) (x : Sem), f (ψ.upd l x) = f ψ

namespace FT

variable {S S' : Nat → Prop} {f : SVal}

theorem mono (h : ∀ l, S l → S' l) (hf : FT S f) : FT S' f :=
  fun ψ ψ' hψ => hf ψ ψ' fun l hl => hψ l (h l hl)

theorem const (S : Nat → Prop) (v : Sem) : FT S (fun _ => v) := fun _ _ _ => rfl

theorem indep {l : Nat} (hf : FT S f) (hl : ¬ S l) : Indep l f := fun ψ x =>
  hf _ _ fun l' hl' => by
    have : l' ≠ l := fun e => hl (e ▸ hl')
    simp [Future.upd, this]

theorem remove {l : Nat} (hf : FT S f) (hi : Indep l f) : FT (fun y => S y ∧ y ≠ l) f := fun ψ ψ' hψ => by
  rw [← hi ψ (ψ' l)]
  apply hf
  intro y hy
  by_cases e : y = l
  · subst e; simp [Future.upd]
  · simp only [Future.upd, e, if_false]; exact hψ y ⟨hy, e⟩

/-- Removing finitely many labels the meaning does not read, one at a time. -/
theorem removeList : ∀ (D : List Nat), FT (fun y => S y ∨ y ∈ D) f → (∀ y ∈ D, Indep y f) → FT S f
  | [], hf, _ => hf.mono fun l h => by simpa using h
  | d :: D, hf, hi => by
    have h1 := hf.remove (hi d (List.mem_cons_self ..))
    refine removeList D (h1.mono fun y ⟨hy, hne⟩ => ?_) fun y hy => hi y (List.mem_cons_of_mem _ hy)
    rcases hy with hy | hy
    · exact .inl hy
    · rcases List.mem_cons.mp hy with e | hy
      · exact absurd e hne
      · exact .inr hy

end FT

/-! ## The positions of a state, and what each holds -/

theorem foldl_push_toList {α β} (g : α → List β) : ∀ (l : List α) (b : Array β),
    (l.foldl (fun b x => b ++ (g x).toArray) b).toList = b.toList ++ l.flatMap g
  | [], b => by simp
  | x :: l, b => by
    simp only [List.foldl_cons, List.flatMap_cons]
    rw [foldl_push_toList g l]
    simp

/-- The positions of a frame. -/
def framePos (f : Nat) (fr : SFrame) : List Pos :=
  (List.range fr.binds.length).map (Pos.bind f) ++ (List.range fr.temps.length).map (Pos.temp f)

theorem SState.positions_eq (s : SState) :
    s.positions = (List.range s.env.length).flatMap fun f => (s.env[f]?.map (framePos f)).getD [] := by
  simp [SState.positions]
  rw [foldl_push_toList]
  simp only [List.nil_append]
  have key : ∀ (l : List Nat) (hl : ∀ x ∈ l, x < s.env.length),
      (l.attach.flatMap fun x => List.map (Pos.bind x.val) (List.range' 0 (s.env[x.val]'(hl x.val x.property)).binds.length) ++
          List.map (Pos.temp x.val) (List.range' 0 (s.env[x.val]'(hl x.val x.property)).temps.length))
        = l.flatMap fun f => (Option.map (framePos f) s.env[f]?).getD [] := by
    intro l hl
    induction l with
    | nil => simp
    | cons a l ih =>
      simp only [List.attach_cons, List.flatMap_cons, List.flatMap_map]
      rw [show s.env[a]? = some (s.env[a]'(hl a (List.mem_cons_self ..))) from List.getElem?_eq_getElem _]
      simp only [Option.map_some, Option.getD_some, framePos, List.range_eq_range']
      congr 1
      exact ih fun x hx => hl x (List.mem_cons_of_mem _ hx)
  rw [List.range_eq_range']
  exact key (List.range' 0 s.env.length) (fun x hx => by simp [List.mem_range'] at hx; omega)
  

namespace SState

/-- What position `p` holds, if it exists. -/
def lookup (s : SState) : Pos → Option SVal
  | .bind f i => (s.env[f]?.bind (·.binds[i]?)).map (·.val)
  | .temp f i => s.env[f]?.bind (·.temps[i]?)

theorem valAt_eq (s : SState) (p : Pos) : s.valAt p = (s.lookup p).getD fun _ => .err := by
  cases p with
  | bind f i => simp only [valAt, lookup]; cases s.env[f]?.bind (·.binds[i]?) <;> rfl
  | temp f i => simp only [valAt, lookup]; cases s.env[f]?.bind (·.temps[i]?) <;> rfl

theorem mem_framePos_bind (f f' i : Nat) (fr : SFrame) :
    Pos.bind f' i ∈ framePos f fr ↔ f' = f ∧ i < fr.binds.length := by
  simp only [framePos, List.mem_append, List.mem_map, List.mem_range, Pos.bind.injEq, reduceCtorEq, and_false,
    exists_false, or_false]
  constructor
  · rintro ⟨a, ha, rfl, rfl⟩; exact ⟨rfl, ha⟩
  · rintro ⟨rfl, hi⟩; exact ⟨i, hi, rfl, rfl⟩

theorem mem_framePos_temp (f f' i : Nat) (fr : SFrame) :
    Pos.temp f' i ∈ framePos f fr ↔ f' = f ∧ i < fr.temps.length := by
  simp only [framePos, List.mem_append, List.mem_map, List.mem_range, Pos.temp.injEq, reduceCtorEq, and_false,
    exists_false, false_or]
  constructor
  · rintro ⟨a, ha, rfl, rfl⟩; exact ⟨rfl, ha⟩
  · rintro ⟨rfl, hi⟩; exact ⟨i, hi, rfl, rfl⟩

theorem mem_positions (s : SState) (p : Pos) : p ∈ s.positions ↔ (s.lookup p).isSome := by
  rw [positions_eq]
  simp only [List.mem_flatMap, List.mem_range]
  constructor
  · rintro ⟨f', _, h⟩
    cases e : s.env[f']? with
    | none => simp [e] at h
    | some fr =>
      simp only [e, Option.map_some, Option.getD_some] at h
      cases p with
      | bind f i =>
        obtain ⟨rfl, hi⟩ := (mem_framePos_bind _ _ _ _).mp h
        simp [lookup, e, hi]
      | temp f i =>
        obtain ⟨rfl, hi⟩ := (mem_framePos_temp _ _ _ _).mp h
        simp [lookup, e, hi]
  · intro h
    cases p with
    | bind f i =>
      cases e : s.env[f]? with
      | none => simp [lookup, e] at h
      | some fr =>
        have hf : f < s.env.length := (List.getElem?_eq_some_iff.mp e).1
        refine ⟨f, hf, ?_⟩
        simp only [e, Option.map_some, Option.getD_some, mem_framePos_bind, true_and]
        simpa [lookup, e] using h
    | temp f i =>
      cases e : s.env[f]? with
      | none => simp [lookup, e] at h
      | some fr =>
        have hf : f < s.env.length := (List.getElem?_eq_some_iff.mp e).1
        refine ⟨f, hf, ?_⟩
        simp only [e, Option.map_some, Option.getD_some, mem_framePos_temp, true_and]
        simpa [lookup, e] using h

theorem positions_congr {s s' : SState} (hl : s.env.length = s'.env.length)
    (hf : ∀ f, s.env[f]?.map (framePos f) = s'.env[f]?.map (framePos f)) : s.positions = s'.positions := by
  rw [positions_eq, positions_eq, hl]
  congr 1
  funext f
  rw [hf f]

theorem lookup_mapVals (s : SState) (g : Pos → SVal → SVal) (p : Pos) :
    (s.mapVals g).lookup p = (s.lookup p).map (g p) := by
  cases p with
  | bind f i =>
    simp only [lookup, mapVals, List.getElem?_map, List.getElem?_zipIdx]
    cases s.env[f]? with
    | none => rfl
    | some fr =>
      simp only [Option.map_some, Option.bind_some, List.getElem?_map, List.getElem?_zipIdx]
      cases fr.binds[i]? <;> simp
  | temp f i =>
    simp only [lookup, mapVals, List.getElem?_map, List.getElem?_zipIdx]
    cases s.env[f]? with
    | none => rfl
    | some fr =>
      simp only [Option.map_some, Option.bind_some, List.getElem?_map, List.getElem?_zipIdx]
      cases fr.temps[i]? <;> simp

theorem valAt_mapVals_of_mem (s : SState) (g : Pos → SVal → SVal) (p : Pos) (h : p ∈ s.positions) :
    (s.mapVals g).valAt p = g p (s.valAt p) := by
  rw [mem_positions] at h
  rw [valAt_eq, valAt_eq, lookup_mapVals]
  cases e : s.lookup p with
  | none => rw [e] at h; cases h
  | some v => rfl

theorem valAt_of_not_mem (s : SState) (p : Pos) (h : p ∉ s.positions) : s.valAt p = fun _ => .err := by
  rw [mem_positions] at h
  rw [valAt_eq]
  cases e : s.lookup p with
  | none => rfl
  | some v => rw [e] at h; exact absurd rfl h

theorem valAt_mapVals_of_not_mem (s : SState) (g : Pos → SVal → SVal) (p : Pos) (h : p ∉ s.positions) :
    (s.mapVals g).valAt p = fun _ => .err := by
  apply valAt_of_not_mem
  rwa [positions_mapVals]

/-- `l` is live: some position holds its borrow. -/
def Live (s : SState) (l : Nat) : Prop := l ∈ s.liveLabels

theorem live_iff (s : SState) (l : Nat) : s.Live l ↔ ∃ p ∈ s.positions, s.shape p = some l := by
  simp [Live, liveLabels, List.mem_mergeSort, List.mem_filterMap]

theorem holderOf_spec {s : SState} {l : Nat} {r : Pos} (h : s.holderOf l = some r) :
    r ∈ s.positions ∧ s.shape r = some l := by
  unfold holderOf at h
  exact ⟨List.mem_of_find?_eq_some h, by simpa using List.find?_some h⟩

theorem holderOf_of_live {s : SState} {l : Nat} (h : s.Live l) : ∃ r, s.holderOf l = some r := by
  rw [live_iff] at h
  obtain ⟨p, hp, hs⟩ := h
  unfold holderOf
  cases e : s.positions.find? (fun p => decide (s.shape p = some l)) with
  | some r => exact ⟨r, rfl⟩
  | none =>
    have := List.find?_eq_none.mp e p hp
    simp [hs] at this

/-- The state after ending `l` at its holder `r`. -/
noncomputable def endAt (s : SState) (l : Nat) (r : Pos) : SState :=
  ({ s with shape := fun p => if p = r then none else s.shape p }).mapVals fun p _ ψ =>
    if p = r then .moved else s.valAt p (ψ.upd l (s.valAt r ψ))

theorem endLabel_eq {s : SState} {l : Nat} {r : Pos} (h : s.holderOf l = some r) : s.endLabel l = s.endAt l r := by
  unfold endLabel
  rw [show (s.positions.find? fun p => decide (s.shape p = some l)) = s.holderOf l from rfl, h]
  rfl

theorem endLabel_of_none {s : SState} {l : Nat} (h : s.holderOf l = none) : s.endLabel l = s := by
  unfold endLabel
  rw [show (s.positions.find? fun p => decide (s.shape p = some l)) = s.holderOf l from rfl, h]

theorem endAt_positions (s : SState) (l : Nat) (r : Pos) : (s.endAt l r).positions = s.positions := by
  unfold endAt; rw [positions_mapVals]; rfl

theorem endAt_shape (s : SState) (l : Nat) (r : Pos) :
    (s.endAt l r).shape = fun p => if p = r then none else s.shape p := rfl

theorem endAt_valAt (s : SState) (l : Nat) (r p : Pos) (hp : p ∈ s.positions) :
    (s.endAt l r).valAt p = fun ψ => if p = r then .moved else s.valAt p (ψ.upd l (s.valAt r ψ)) := by
  unfold endAt
  have hp' : p ∈ ({ s with shape := fun p => if p = r then none else s.shape p } : SState).positions := hp
  rw [valAt_mapVals_of_mem _ _ _ hp']

theorem endAt_valAt_not_mem (s : SState) (l : Nat) (r p : Pos) (hp : p ∉ s.positions) :
    (s.endAt l r).valAt p = s.valAt p := by
  unfold endAt
  have hp' : p ∉ ({ s with shape := fun p => if p = r then none else s.shape p } : SState).positions := hp
  rw [valAt_mapVals_of_not_mem _ _ _ hp', valAt_of_not_mem _ _ hp]

theorem endAt_live {s : SState} {l y : Nat} {r : Pos} (h : (s.endAt l r).Live y) : s.Live y := by
  rw [live_iff, endAt_positions, endAt_shape] at h
  obtain ⟨p, hp, hs⟩ := h
  simp only at hs
  split at hs
  · cases hs
  · exact (live_iff s y).mpr ⟨p, hp, hs⟩

theorem live_endAt {s : SState} {l y : Nat} {r : Pos} (hr : s.shape r = some l) (hy : s.Live y) (hne : y ≠ l) :
    (s.endAt l r).Live y := by
  rw [live_iff] at hy ⊢
  obtain ⟨p, hp, hs⟩ := hy
  refine ⟨p, (endAt_positions s l r).symm ▸ hp, ?_⟩
  rw [endAt_shape]
  simp only
  split
  · subst_vars; rw [hr] at hs; cases hs; exact absurd rfl hne
  · exact hs

/-! ## The invariant, and [End] keeping it -/

variable (L : Nat → Prop)

/-- (I1) every position factors through `L` and the live labels. -/
def Inv1 (s : SState) : Prop := ∀ p, FT (fun y => L y ∨ s.Live y) (s.valAt p)

/-- (I2) the holder of `x` factors through the non-live labels of `L` and the live labels above
`x`. -/
def Inv2 (s : SState) : Prop := ∀ r x, r ∈ s.positions → s.shape r = some x →
  FT (fun y => (L y ∧ ¬ s.Live y) ∨ (s.Live y ∧ x < y)) (s.valAt r)

variable {L}

theorem holder_indep {s : SState} (h2 : Inv2 L s) {r : Pos} {x : Nat} (hr : r ∈ s.positions)
    (hs : s.shape r = some x) : Indep x (s.valAt r) :=
  (h2 r x hr hs).indep fun h => by
    rcases h with ⟨_, hn⟩ | ⟨_, hlt⟩
    · exact hn ((live_iff s x).mpr ⟨r, hr, hs⟩)
    · exact absurd hlt (Nat.lt_irrefl x)

theorem endAt_indep {s : SState} (h2 : Inv2 L s) {l : Nat} {r : Pos} (hr : r ∈ s.positions)
    (hs : s.shape r = some l) (p : Pos) : Indep l ((s.endAt l r).valAt p) := by
  by_cases hp : p ∈ s.positions
  · rw [endAt_valAt _ _ _ _ hp]
    intro ψ x
    by_cases e : p = r
    · simp [e]
    · simp only [e, if_false, holder_indep h2 hr hs ψ x, Future.upd_upd_same]
  · rw [endAt_valAt_not_mem _ _ _ _ hp, valAt_of_not_mem _ _ hp]
    intro _ _; rfl

theorem endAt_inv1 {s : SState} (h1 : Inv1 L s) (h2 : Inv2 L s) {l : Nat} {r : Pos} (hr : r ∈ s.positions)
    (hs : s.shape r = some l) : Inv1 L (s.endAt l r) := by
  intro p
  by_cases hp : p ∈ s.positions
  · rw [endAt_valAt _ _ _ _ hp]
    intro ψ ψ' hψ
    by_cases e : p = r
    · simp [e]
    · simp only [e, if_false]
      have ha : s.valAt r ψ = s.valAt r ψ' := h2 r l hr hs ψ ψ' fun y hy => by
        rcases hy with ⟨hL, _⟩ | ⟨hy, hlt⟩
        · exact hψ y (.inl hL)
        · exact hψ y (.inr (live_endAt hs hy (Nat.ne_of_gt hlt)))
      rw [ha]
      apply h1 p
      intro y hy
      by_cases ey : y = l
      · subst ey; simp [Future.upd]
      · simp only [Future.upd, ey, if_false]
        rcases hy with hL | hy
        · exact hψ y (.inl hL)
        · exact hψ y (.inr (live_endAt hs hy ey))
  · rw [endAt_valAt_not_mem _ _ _ _ hp, valAt_of_not_mem _ _ hp]
    exact FT.const _ _

theorem endAt_inv2 {s : SState} (h2 : Inv2 L s) {l : Nat} {r : Pos} (hr : r ∈ s.positions)
    (hs : s.shape r = some l) : Inv2 L (s.endAt l r) := by
  intro h x hh hsx
  rw [endAt_positions] at hh
  rw [endAt_shape] at hsx
  simp only at hsx
  split at hsx
  · cases hsx
  rename_i hne
  rw [endAt_valAt _ _ _ _ hh]
  intro ψ ψ' hψ
  simp only [hne, if_false]
  apply h2 h x hh hsx
  intro y hy
  have hlive : s.Live l := (live_iff s l).mpr ⟨r, hr, hs⟩
  by_cases ey : y = l
  · subst ey
    have hxl : x < y := by
      rcases hy with ⟨_, hn⟩ | ⟨_, hlt⟩
      · exact absurd hlive hn
      · exact hlt
    simp only [Future.upd, if_true]
    apply h2 r y hr hs
    intro z hz
    rcases hz with ⟨hL, hn⟩ | ⟨hz, hlt⟩
    · exact hψ z (.inl ⟨hL, fun h' => hn (endAt_live h')⟩)
    · exact hψ z (.inr ⟨live_endAt hs hz (Nat.ne_of_gt hlt), Nat.lt_trans hxl hlt⟩)
  · simp only [Future.upd, ey, if_false]
    rcases hy with ⟨hL, hn⟩ | ⟨hy, hlt⟩
    · exact hψ y (.inl ⟨hL, fun h' => hn (endAt_live h')⟩)
    · exact hψ y (.inr ⟨live_endAt hs hy ey, hlt⟩)

theorem endLabel_inv {s : SState} (h1 : Inv1 L s) (h2 : Inv2 L s) (l : Nat) :
    Inv1 L (s.endLabel l) ∧ Inv2 L (s.endLabel l) := by
  cases e : s.holderOf l with
  | none => rw [endLabel_of_none e]; exact ⟨h1, h2⟩
  | some r =>
    obtain ⟨hr, hs⟩ := holderOf_spec e
    rw [endLabel_eq e]
    exact ⟨endAt_inv1 h1 h2 hr hs, endAt_inv2 h2 hr hs⟩

theorem foldl_endLabel_inv {s : SState} (h1 : Inv1 L s) (h2 : Inv2 L s) :
    ∀ ls : List Nat, Inv1 L (ls.foldl endLabel s) ∧ Inv2 L (ls.foldl endLabel s) := by
  intro ls
  induction ls generalizing s with
  | nil => exact ⟨h1, h2⟩
  | cons l ls ih =>
    obtain ⟨h1', h2'⟩ := endLabel_inv h1 h2 l
    exact ih h1' h2'

/-! ## Counting holders: ending a live label removes one -/

/-- How many positions hold the borrow of `y`. -/
def holders (s : SState) (y : Nat) : Nat := (s.positions.filter fun p => s.shape p = some y).length

theorem live_iff_holders (s : SState) (y : Nat) : s.Live y ↔ 0 < s.holders y := by
  rw [live_iff, holders, List.length_pos_iff_exists_mem]
  simp [List.mem_filter]

theorem filter_length_le {α} (P Q : α → Bool) (h : ∀ a, P a → Q a) :
    ∀ l : List α, (l.filter P).length ≤ (l.filter Q).length
  | [] => Nat.le_refl _
  | a :: l => by
    have ih := filter_length_le P Q h l
    by_cases hp : P a
    · simp [hp, h a hp, ih]
    · by_cases hq : Q a
      · simp [hp, hq]; omega
      · simp [hp, hq, ih]

theorem filter_length_lt {α} (P Q : α → Bool) (h : ∀ a, P a → Q a) (b : α) (hb : Q b) (hnb : ¬ P b) :
    ∀ l : List α, b ∈ l → (l.filter P).length < (l.filter Q).length
  | [], hm => absurd hm (List.not_mem_nil)
  | a :: l, hm => by
    rcases List.mem_cons.mp hm with rfl | hm
    · have := filter_length_le P Q h l
      simp [hb, hnb]; omega
    · have ih := filter_length_lt P Q h b hb hnb l hm
      by_cases hp : P a
      · simp [hp, h a hp]; omega
      · by_cases hq : Q a
        · simp [hp, hq]; omega
        · simp [hp, hq, ih]

theorem holders_endAt_le (s : SState) (l : Nat) (r : Pos) (z : Nat) : (s.endAt l r).holders z ≤ s.holders z := by
  unfold holders
  rw [endAt_positions, endAt_shape]
  apply filter_length_le
  intro p hp
  simp only [decide_eq_true_eq] at hp ⊢
  split at hp
  · cases hp
  · exact hp

theorem holders_endAt_lt (s : SState) (l : Nat) (r : Pos) (hr : r ∈ s.positions) (hs : s.shape r = some l) :
    (s.endAt l r).holders l < s.holders l := by
  unfold holders
  rw [endAt_positions, endAt_shape]
  apply filter_length_lt _ _ _ r (by simp [hs]) (by simp) _ hr
  intro p hp
  simp only [decide_eq_true_eq] at hp ⊢
  split at hp
  · cases hp
  · exact hp

theorem holders_endLabel_le (s : SState) (l z : Nat) : (s.endLabel l).holders z ≤ s.holders z := by
  cases e : s.holderOf l with
  | none => rw [endLabel_of_none e]; exact Nat.le_refl _
  | some r => rw [endLabel_eq e]; exact holders_endAt_le _ _ _ _

theorem holders_endLabel_sub (s : SState) (l : Nat) : (s.endLabel l).holders l ≤ s.holders l - 1 := by
  cases e : s.holderOf l with
  | none =>
    rw [endLabel_of_none e]
    have : s.holders l = 0 := by
      cases h : s.holders l with
      | zero => rfl
      | succ k =>
        obtain ⟨r, hr⟩ := holderOf_of_live ((live_iff_holders s l).mpr (by omega))
        rw [hr] at e; cases e
    omega
  | some r =>
    obtain ⟨hr, hs⟩ := holderOf_spec e
    rw [endLabel_eq e]
    have := holders_endAt_lt s l r hr hs
    omega

theorem holders_foldl_endLabel (z : Nat) : ∀ (ls : List Nat) (s : SState),
    (ls.foldl endLabel s).holders z ≤ s.holders z - ls.count z
  | [], s => by simp
  | l :: ls, s => by
    simp only [List.foldl_cons, List.count_cons]
    have ih := holders_foldl_endLabel z ls (s.endLabel l)
    by_cases e : l = z
    · subst e
      have := holders_endLabel_sub s l
      simp; omega
    · have := holders_endLabel_le s l z
      simp [e]; omega

theorem count_filterMap_shape (s : SState) (z : Nat) :
    ∀ l : List Pos, (l.filterMap s.shape).count z = (l.filter fun p => s.shape p = some z).length
  | [] => rfl
  | p :: l => by
    have ih := count_filterMap_shape s z l
    cases e : s.shape p with
    | none => simp [e, ih]
    | some y =>
      by_cases hy : y = z
      · subst hy; simp [e, ih]
      · simp [e, ih, hy]

theorem count_liveLabels (s : SState) (z : Nat) : s.liveLabels.count z = s.holders z := by
  rw [liveLabels, (List.mergeSort_perm _ _).count_eq, count_filterMap_shape]; rfl

/-- Ending every live label, as an observation does, leaves none live. -/
theorem not_live_endAll (s : SState) (z : Nat) : ¬ (s.liveLabels.foldl endLabel s).Live z := by
  rw [live_iff_holders]
  have := holders_foldl_endLabel z s.liveLabels s
  rw [count_liveLabels] at this
  omega

/-- (R3) After ending every live label, a position factors through `L`. -/
theorem endAll_FT {s : SState} (h1 : Inv1 L s) (h2 : Inv2 L s) (p : Pos) :
    FT L ((s.liveLabels.foldl endLabel s).valAt p) :=
  ((foldl_endLabel_inv h1 h2 _).1 p).mono fun y hy => hy.resolve_right (not_live_endAll s y)

/-! ## [Access]: after it, the accessed position factors through `L` -/

/-- The number of holders, with multiplicity. -/
def total (s : SState) : Nat := s.liveLabels.length

theorem filterMap_length_le {α β} (f g : α → Option β) (h : ∀ a, g a = none ∨ g a = f a) :
    ∀ l : List α, (l.filterMap g).length ≤ (l.filterMap f).length
  | [] => Nat.le_refl _
  | a :: l => by
    have ih := filterMap_length_le f g h l
    rcases h a with e | e
    · cases ef : f a <;> simp [e, ef] <;> omega
    · cases ef : f a <;> simp [e, ef, ih]

theorem filterMap_length_lt {α β} (f g : α → Option β) (h : ∀ a, g a = none ∨ g a = f a) (b : α)
    (hb : (f b).isSome) (hgb : g b = none) : ∀ l : List α, b ∈ l → (l.filterMap g).length < (l.filterMap f).length
  | [], hm => absurd hm List.not_mem_nil
  | a :: l, hm => by
    rcases List.mem_cons.mp hm with rfl | hm
    · have := filterMap_length_le f g h l
      cases ef : f b with
      | none => rw [ef] at hb; cases hb
      | some y => simp [hgb, ef]; omega
    · have ih := filterMap_length_lt f g h b hb hgb l hm
      rcases h a with e | e
      · cases ef : f a <;> simp [e, ef] <;> omega
      · cases ef : f a <;> simp [e, ef] <;> omega

theorem total_eq (s : SState) : s.total = (s.positions.filterMap s.shape).length := by
  simp [total, liveLabels, List.length_mergeSort]

theorem total_endAt_lt (s : SState) (l : Nat) (r : Pos) (hr : r ∈ s.positions) (hs : s.shape r = some l) :
    (s.endAt l r).total < s.total := by
  rw [total_eq, total_eq, endAt_positions, endAt_shape]
  apply filterMap_length_lt _ _ _ r (by simp [hs]) (by simp) _ hr
  intro p; by_cases e : p = r <;> simp [e]

theorem total_endAt_le (s : SState) (l : Nat) (r : Pos) : (s.endAt l r).total ≤ s.total := by
  rw [total_eq, total_eq, endAt_positions, endAt_shape]
  apply filterMap_length_le
  intro p; by_cases e : p = r <;> simp [e]

theorem total_endLabel_le (s : SState) (l : Nat) : (s.endLabel l).total ≤ s.total := by
  cases e : s.holderOf l with
  | none => rw [endLabel_of_none e]; exact Nat.le_refl _
  | some r => rw [endLabel_eq e]; exact total_endAt_le _ _ _

theorem total_endLabel_lt (s : SState) (l : Nat) (hl : s.Live l) : (s.endLabel l).total < s.total := by
  obtain ⟨r, e⟩ := holderOf_of_live hl
  obtain ⟨hr, hs⟩ := holderOf_spec e
  rw [endLabel_eq e]; exact total_endAt_lt _ _ _ hr hs

theorem total_foldl_endLabel_le : ∀ (ls : List Nat) (s : SState), (ls.foldl endLabel s).total ≤ s.total
  | [], _ => Nat.le_refl _
  | l :: ls, s => Nat.le_trans (total_foldl_endLabel_le ls _) (total_endLabel_le s l)

/-- One round of [Access] of `p` (`SState.access`'s `step`). -/
noncomputable def accStep (p : Pos) (s : SState) : SState :=
  open Classical in (s.liveLabels.filter fun l => decide (s.dependsOn p l)).foldl endLabel s

theorem access_eq (s : SState) (p : Pos) :
    s.access p = (List.range s.liveLabels.length).foldl (fun s _ => accStep p s) s := rfl

/-- `g` applied `k` times, outermost last. -/
def iterR {α} (g : α → α) : Nat → α → α
  | 0, a => a
  | k + 1, a => g (iterR g k a)

theorem foldl_range_iterR {α} (g : α → α) : ∀ (k : Nat) (a : α),
    (List.range k).foldl (fun a _ => g a) a = iterR g k a
  | 0, _ => rfl
  | k + 1, a => by
    rw [List.range_succ, List.foldl_append, foldl_range_iterR g k a]
    rfl

theorem iterR_succ' {α} (g : α → α) : ∀ (k : Nat) (a : α), iterR g (k + 1) a = iterR g k (g a)
  | 0, _ => rfl
  | k + 1, a => by
    show g (iterR g (k + 1) a) = g (iterR g k (g a))
    rw [iterR_succ' g k a]

theorem iterR_fix {α} (g : α → α) (a : α) (h : g a = a) : ∀ k, iterR g k a = a
  | 0 => rfl
  | k + 1 => by show g (iterR g k a) = a; rw [iterR_fix g a h k, h]

theorem dependsOn_iff (s : SState) (p : Pos) (l : Nat) : s.dependsOn p l ↔ ¬ Indep l (s.valAt p) := by
  simp only [dependsOn, Mean.dependsOn, toMean, Indep]
  constructor
  · rintro ⟨φ, x, h⟩ hi; exact h (hi φ x).symm
  · intro h
    apply Classical.byContradiction
    intro hn
    exact h fun ψ x => Classical.byContradiction fun hne => hn ⟨ψ, x, fun e => hne e.symm⟩

theorem accStep_inv {s : SState} (h1 : Inv1 L s) (h2 : Inv2 L s) (p : Pos) :
    Inv1 L (accStep p s) ∧ Inv2 L (accStep p s) := foldl_endLabel_inv h1 h2 _

open Classical in
theorem accStep_fix (s : SState) (p : Pos) (h : ∀ y, s.Live y → Indep y (s.valAt p)) : accStep p s = s := by
  unfold accStep
  rw [List.filter_eq_nil_iff.mpr]
  · rfl
  · intro y hy
    simp only [decide_eq_true_eq, dependsOn_iff, Classical.not_not]
    exact h y hy

theorem live_endLabel {s : SState} {l y : Nat} (hy : s.Live y) (hne : y ≠ l) : (s.endLabel l).Live y := by
  cases e : s.holderOf l with
  | none => rw [endLabel_of_none e]; exact hy
  | some r => rw [endLabel_eq e]; exact live_endAt (holderOf_spec e).2 hy hne

theorem total_foldl_lt (y : Nat) : ∀ (ls : List Nat) (s : SState), y ∈ ls → s.Live y →
    (ls.foldl endLabel s).total < s.total
  | [], _, hm, _ => absurd hm List.not_mem_nil
  | l :: ls, s, hm, hy => by
    simp only [List.foldl_cons]
    by_cases e : l = y
    · subst e
      exact Nat.lt_of_le_of_lt (total_foldl_endLabel_le ls _) (total_endLabel_lt s l hy)
    · have hm' : y ∈ ls := by
        rcases List.mem_cons.mp hm with h | h
        · exact absurd h.symm e
        · exact h
      exact Nat.lt_of_lt_of_le (total_foldl_lt y ls _ hm' (live_endLabel hy (Ne.symm e))) (total_endLabel_le s l)

open Classical in
theorem accStep_lt (s : SState) (p : Pos) (y : Nat) (hy : s.Live y) (hd : ¬ Indep y (s.valAt p)) :
    (accStep p s).total < s.total := by
  unfold accStep
  have hm : y ∈ s.liveLabels.filter fun l => decide (s.dependsOn p l) := by
    rw [List.mem_filter]; exact ⟨hy, by simpa [dependsOn_iff] using hd⟩
  exact total_foldl_lt y _ s hm hy

theorem access_settles (p : Pos) : ∀ (k : Nat) (s : SState), s.total ≤ k →
    ∀ y, (iterR (accStep p) k s).Live y → Indep y ((iterR (accStep p) k s).valAt p)
  | 0, s, hk, y, hy => by
    have : s.liveLabels = [] := List.eq_nil_of_length_eq_zero (Nat.eq_zero_of_le_zero hk)
    exact absurd (show y ∈ s.liveLabels from hy) (by rw [this]; exact List.not_mem_nil)
  | k + 1, s, hk, y, hy => by
    rw [iterR_succ'] at hy ⊢
    by_cases h : ∀ y, s.Live y → Indep y (s.valAt p)
    · rw [accStep_fix s p h, iterR_fix _ s (accStep_fix s p h)] at hy ⊢
      exact h y hy
    · have ⟨z, hz⟩ : ∃ z, s.Live z ∧ ¬ Indep z (s.valAt p) := by
        apply Classical.byContradiction
        intro hn
        exact h fun z hz => Classical.byContradiction fun hi => hn ⟨z, hz, hi⟩
      have hlt := accStep_lt s p z hz.1 hz.2
      exact access_settles p k _ (by omega) y hy

theorem iterR_accStep_inv (p : Pos) : ∀ (k : Nat) {s : SState}, Inv1 L s → Inv2 L s →
    Inv1 L (iterR (accStep p) k s) ∧ Inv2 L (iterR (accStep p) k s)
  | 0, _, h1, h2 => ⟨h1, h2⟩
  | k + 1, _, h1, h2 => by
    obtain ⟨h1', h2'⟩ := iterR_accStep_inv p k h1 h2
    exact accStep_inv h1' h2' p

/-- [Access] keeps the invariant. -/
theorem access_inv {s : SState} (h1 : Inv1 L s) (h2 : Inv2 L s) (p : Pos) :
    Inv1 L (s.access p) ∧ Inv2 L (s.access p) := by
  rw [access_eq, foldl_range_iterR]
  exact iterR_accStep_inv p _ h1 h2

/-- (R1) After [Access] of `p`, the meaning at `p` factors through `L`: every live label it read
has been ended, and what is left are the labels the two futures agree on. -/
theorem access_FT {s : SState} (h1 : Inv1 L s) (h2 : Inv2 L s) (p : Pos) : FT L ((s.access p).valAt p) := by
  have hset := access_settles p s.total s (Nat.le_refl _)
  rw [← foldl_range_iterR, show (List.range s.total).foldl (fun a _ => accStep p a) s = s.access p from rfl] at hset
  have hI := (access_inv h1 h2 p).1 p
  exact FT.removeList (s.access p).liveLabels hI fun y hy => hset y hy

/-! ## The closed future -/

/-- One pass of `closedFuture`: each live label, in label order, fixed to its holder's content. -/
noncomputable def cfPass (s : SState) (ψ : Future) : Future :=
  s.liveLabels.foldl (fun ψ l =>
    match s.holderOf l with
    | some r => ψ.upd l (s.valAt r ψ)
    | none => ψ) ψ

theorem closedFuture_eq (s : SState) (φ : Future) :
    s.closedFuture φ = (List.range s.liveLabels.length).foldl (fun ψ _ => s.cfPass ψ) φ := rfl

/-- The inner fold over a label-sorted list of live labels: a label not in it is unchanged; a label in
it is fixed to its holder's content *at the starting future*, since the holder reads only labels
above it, which the fold has not yet changed. -/
theorem cfFold_spec {s : SState} (h2 : Inv2 L s) :
    ∀ (ls : List Nat), ls.Pairwise (· ≤ ·) → (∀ u ∈ ls, s.Live u) → ∀ ψ : Future,
      (∀ u, u ∉ ls → (ls.foldl (fun ψ l => match s.holderOf l with
          | some r => ψ.upd l (s.valAt r ψ) | none => ψ) ψ) u = ψ u) ∧
      (∀ u r, u ∈ ls → s.holderOf u = some r → (ls.foldl (fun ψ l => match s.holderOf l with
          | some r => ψ.upd l (s.valAt r ψ) | none => ψ) ψ) u = s.valAt r ψ)
  | [], _, _, ψ => ⟨fun _ _ => rfl, fun _ _ h => absurd h List.not_mem_nil⟩
  | h :: t, hs, hl, ψ => by
    simp only [List.foldl_cons]
    obtain ⟨rh, erh⟩ := holderOf_of_live (hl h (List.mem_cons_self ..))
    rw [erh]
    have hsorted := List.pairwise_cons.mp hs
    obtain ⟨iha, ihb⟩ := cfFold_spec h2 t hsorted.2 (fun u hu => hl u (List.mem_cons_of_mem _ hu))
      (ψ.upd h (s.valAt rh ψ))
    refine ⟨fun u hu => ?_, fun u r hu er => ?_⟩
    · rw [iha u (fun h' => hu (List.mem_cons_of_mem _ h'))]
      have : u ≠ h := fun e => hu (e ▸ List.mem_cons_self ..)
      simp [Future.upd, this]
    · by_cases ht : u ∈ t
      · rw [ihb u r ht er]
        obtain ⟨hr, hsr⟩ := holderOf_spec er
        apply h2 r u hr hsr
        intro y hy
        by_cases ey : y = h
        · subst ey
          have hle : y ≤ u := hsorted.1 u ht
          rcases hy with ⟨_, hn⟩ | ⟨_, hlt⟩
          · exact absurd (hl y (List.mem_cons_self ..)) hn
          · exact absurd hlt (Nat.not_lt.mpr hle)
        · simp [Future.upd, ey]
      · have eu : u = h := by
          rcases List.mem_cons.mp hu with e | e
          · exact e
          · exact absurd e ht
        subst eu
        rw [iha u ht]
        rw [erh] at er; cases er
        simp [Future.upd]

theorem liveLabels_sorted (s : SState) : s.liveLabels.Pairwise (· ≤ ·) := by
  have := List.pairwise_mergeSort (le := fun a b => decide (a ≤ b)) (by intro a b c; simp; omega)
    (by intro a b; simp; omega) (s.positions.filterMap s.shape)
  simpa [liveLabels] using this

theorem cfPass_nonlive {s : SState} (h2 : Inv2 L s) (ψ : Future) (u : Nat) (hu : ¬ s.Live u) :
    s.cfPass ψ u = ψ u :=
  (cfFold_spec h2 s.liveLabels (liveLabels_sorted s) (fun _ h => h) ψ).1 u hu

theorem cfPass_live {s : SState} (h2 : Inv2 L s) (ψ : Future) (u : Nat) (r : Pos) (hr : s.holderOf u = some r) :
    s.cfPass ψ u = s.valAt r ψ := by
  have hu : s.Live u := (live_iff s u).mpr ⟨r, (holderOf_spec hr).1, (holderOf_spec hr).2⟩
  exact (cfFold_spec h2 s.liveLabels (liveLabels_sorted s) (fun _ h => h) ψ).2 u r hu hr

/-- The number of live labels (with multiplicity) above `u`: strictly smaller above a larger live
label, and below the total at a live label. -/
def above (s : SState) (u : Nat) : Nat := (s.liveLabels.filter fun z => decide (u < z)).length

theorem above_lt {s : SState} {u z : Nat} (hz : s.Live z) (huz : u < z) : s.above z < s.above u :=
  filter_length_lt (fun y => decide (z < y)) (fun y => decide (u < y))
    (fun y h => by simp at h ⊢; omega) z (by simpa using huz) (by simp) _ hz

theorem above_lt_total {s : SState} {u : Nat} (hu : s.Live u) : s.above u < s.liveLabels.length := by
  have := filter_length_lt (fun y => decide (u < y)) (fun _ => true) (fun _ _ => rfl) u rfl (by simp) _ hu
  have e : (s.liveLabels.filter fun _ => true) = s.liveLabels := List.filter_eq_self.mpr fun _ _ => rfl
  rw [e] at this
  exact this

/-- After `k` passes, the two closed futures agree on the non-live labels of `L`, and on every live
label with fewer than `k` live labels above it. -/
theorem cf_agree_iter {s : SState} (h2 : Inv2 L s) {φ φ' : Future} (hφ : ∀ l, L l → φ l = φ' l) :
    ∀ k : Nat, (∀ u, L u → ¬ s.Live u → iterR s.cfPass k φ u = iterR s.cfPass k φ' u) ∧
      (∀ u, s.Live u → s.above u < k → iterR s.cfPass k φ u = iterR s.cfPass k φ' u)
  | 0 => ⟨fun u hL _ => hφ u hL, fun _ _ h => absurd h (Nat.not_lt_zero _)⟩
  | k + 1 => by
    obtain ⟨ih1, ih2⟩ := cf_agree_iter h2 hφ k
    refine ⟨fun u hL hn => ?_, fun u hu hk => ?_⟩
    · show s.cfPass _ u = s.cfPass _ u
      rw [cfPass_nonlive h2 _ u hn, cfPass_nonlive h2 _ u hn]
      exact ih1 u hL hn
    · show s.cfPass _ u = s.cfPass _ u
      obtain ⟨r, hr⟩ := holderOf_of_live hu
      rw [cfPass_live h2 _ u r hr, cfPass_live h2 _ u r hr]
      obtain ⟨hrp, hrs⟩ := holderOf_spec hr
      apply h2 r u hrp hrs
      intro y hy
      rcases hy with ⟨hL, hn⟩ | ⟨hy, hlt⟩
      · exact ih1 y hL hn
      · exact ih2 y hy (Nat.lt_of_lt_of_le (above_lt hy hlt) (Nat.le_of_lt_succ hk))

/-- The closed futures of two futures that agree on `L` agree on `L` and on every live label. -/
theorem closedFuture_agree {s : SState} (h2 : Inv2 L s) {φ φ' : Future} (hφ : ∀ l, L l → φ l = φ' l) (u : Nat)
    (hu : L u ∨ s.Live u) : s.closedFuture φ u = s.closedFuture φ' u := by
  rw [closedFuture_eq, closedFuture_eq, foldl_range_iterR, foldl_range_iterR]
  obtain ⟨h1, h2'⟩ := cf_agree_iter h2 hφ s.liveLabels.length
  by_cases hl : s.Live u
  · exact h2' u hl (above_lt_total hl)
  · exact h1 u (hu.resolve_right hl) hl

/-- (R2) A read at the closed future does not see where two futures that agree on `L` differ. -/
theorem closedFuture_read {s : SState} (h1 : Inv1 L s) (h2 : Inv2 L s) {φ φ' : Future}
    (hφ : ∀ l, L l → φ l = φ' l) (p : Pos) :
    s.valAt p (s.closedFuture φ) = s.valAt p (s.closedFuture φ') :=
  h1 p _ _ fun u hu => closedFuture_agree h2 hφ u hu

end SState

/-! ## The call clause (start of the induction for `run_congr`)

`callOfL` reads no future: it applies the callee's meaning to the arguments' meanings and
rewrites the state structurally. So the call clause of `run_congr` is the induction hypotheses
for the callee and the arguments, and what remains is that the rewriting keeps the invariant. Its
one future-dependent operation is the fix of the borrow arguments' labels to their finals,
`v (ψ.updList fixes)`: a meaning composed with it no longer reads the fixed labels, and reads the
others as `v` did. -/

theorem Future.updList_of_not_mem : ∀ (fx : List (Nat × Sem)) (ψ : Future) (l : Nat), l ∉ fx.map (·.1) →
    ψ.updList fx l = ψ l
  | [], _, _, _ => rfl
  | (k, e) :: fx, ψ, l, h => by
    simp only [List.map_cons, List.mem_cons, not_or] at h
    show (ψ.upd k e).updList fx l = ψ l
    rw [Future.updList_of_not_mem fx _ l h.2, Future.upd_other _ _ h.1]

theorem Future.updList_agree_mem : ∀ (fx : List (Nat × Sem)) (ψ ψ' : Future) (l : Nat), l ∈ fx.map (·.1) →
    ψ.updList fx l = ψ'.updList fx l
  | [], _, _, _, h => absurd h List.not_mem_nil
  | (k, e) :: fx, ψ, ψ', l, h => by
    show (ψ.upd k e).updList fx l = (ψ'.upd k e).updList fx l
    by_cases hl : l ∈ fx.map (·.1)
    · exact Future.updList_agree_mem fx _ _ l hl
    · rw [Future.updList_of_not_mem fx _ l hl, Future.updList_of_not_mem fx _ l hl]
      simp only [List.map_cons, List.mem_cons] at h
      rcases h with rfl | h
      · simp [Future.upd]
      · exact absurd h hl

/-- Fixing labels to constants: the composed meaning reads only the labels `v` read, less the
fixed ones. -/
theorem FT.updList {S : Nat → Prop} {v : SVal} (hv : FT S v) (fx : List (Nat × Sem)) :
    FT (fun y => S y ∧ y ∉ fx.map (·.1)) (fun ψ => v (ψ.updList fx)) := fun ψ ψ' hψ => by
  apply hv
  intro y hy
  by_cases hm : y ∈ fx.map (·.1)
  · exact Future.updList_agree_mem fx ψ ψ' y hm
  · rw [Future.updList_of_not_mem fx _ y hm, Future.updList_of_not_mem fx _ y hm]
    exact hψ y ⟨hy, hm⟩

namespace SState

variable {L : Nat → Prop}

theorem positions_setAt (s : SState) (p : Pos) (v : SVal) : (s.setAt p v).positions = s.positions := by
  apply positions_congr
  · cases p <;> simp [setAt]
  · intro f
    cases p with
    | bind f' i =>
      simp only [setAt, List.getElem?_modify]
      by_cases h : f' = f
      · subst h; cases s.env[f']? <;> simp [framePos]
      · simp [h]
    | temp f' i =>
      simp only [setAt, List.getElem?_modify]
      by_cases h : f' = f
      · subst h; cases s.env[f']? <;> simp [framePos]
      · simp [h]

/-- Taking the holder of `l` keeps the positions; every meaning is the old one or `moved`. -/
theorem takeLabel_positions (s : SState) (l : Nat) : (s.takeLabel l).positions = s.positions := by
  unfold takeLabel
  cases s.holderOf l with
  | none => rfl
  | some r => exact positions_setAt s r _

theorem takeLabel_valAt (s : SState) (l : Nat) (q : Pos) :
    (s.takeLabel l).valAt q = s.valAt q ∨ (s.takeLabel l).valAt q = fun _ => .moved := by
  unfold takeLabel
  cases s.holderOf l with
  | none => exact .inl rfl
  | some r => exact valAt_setAt s r _ q

theorem takeLabel_live {s : SState} {l y : Nat} (hy : s.Live y) (hne : y ≠ l) : (s.takeLabel l).Live y := by
  unfold takeLabel
  cases e : s.holderOf l with
  | none => exact hy
  | some r =>
    have hr := (holderOf_spec e).2
    rw [live_iff] at hy ⊢
    obtain ⟨p, hp, hs⟩ := hy
    refine ⟨p, (positions_setAt s r _).symm ▸ hp, ?_⟩
    show (if p = r then none else s.shape p) = some y
    split
    · subst_vars; rw [hr] at hs; cases hs; exact absurd rfl hne
    · exact hs

/-- (I1) through a call's taking of a borrow argument's holder and fixing its label: what read
the taken label now reads its fixed final instead. -/
theorem take_fix_inv1 {s : SState} (h1 : Inv1 L s) {l : Nat} (fx : List (Nat × Sem)) (hl : l ∈ fx.map (·.1)) :
    Inv1 L ((s.takeLabel l).mapVals fun _ v ψ => v (ψ.updList fx)) := by
  intro p
  by_cases hp : p ∈ (s.takeLabel l).positions
  · rw [valAt_mapVals_of_mem _ _ _ hp]
    have hv : FT (fun y => L y ∨ s.Live y) ((s.takeLabel l).valAt p) := by
      rcases takeLabel_valAt s l p with e | e
      · rw [e]; exact h1 p
      · rw [e]; exact FT.const _ _
    refine (hv.updList fx).mono fun y ⟨hy, hn⟩ => ?_
    rcases hy with hL | hy
    · exact .inl hL
    · have hne : y ≠ l := fun e => hn (e ▸ hl)
      refine .inr ?_
      have := takeLabel_live hy hne
      rw [live_iff] at this ⊢
      obtain ⟨q, hq, hs⟩ := this
      exact ⟨q, by rw [positions_mapVals]; exact hq, hs⟩
  · rw [valAt_mapVals_of_not_mem _ _ _ hp]
    exact FT.const _ _

theorem takeLabel_shape_some {s : SState} {l x : Nat} {h : Pos} (hs : (s.takeLabel l).shape h = some x) :
    s.shape h = some x := by
  unfold takeLabel at hs
  cases e : s.holderOf l with
  | none => rw [e] at hs; exact hs
  | some r =>
    rw [e] at hs
    change (if h = r then none else s.shape h) = some x at hs
    split at hs
    · cases hs
    · exact hs

theorem takeLabel_live_rev {s : SState} {l y : Nat} (hy : (s.takeLabel l).Live y) : s.Live y := by
  rw [live_iff, takeLabel_positions] at hy
  obtain ⟨p, hp, hs⟩ := hy
  exact (live_iff s y).mpr ⟨p, hp, takeLabel_shape_some hs⟩

theorem live_mapVals {s : SState} {g : Pos → SVal → SVal} {y : Nat} : (s.mapVals g).Live y ↔ s.Live y := by
  rw [live_iff, live_iff, positions_mapVals]; rfl

/-- (I2) through a call's taking of a borrow argument's holder and fixing its label: a holder that
read the taken label (a reborrow chain) reads the fixed final instead. -/
theorem take_fix_inv2 {s : SState} (h2 : Inv2 L s) {l : Nat} (fx : List (Nat × Sem)) (hl : l ∈ fx.map (·.1)) :
    Inv2 L ((s.takeLabel l).mapVals fun _ v ψ => v (ψ.updList fx)) := by
  intro h x hh hsx
  rw [positions_mapVals] at hh
  have hsx' : (s.takeLabel l).shape h = some x := hsx
  rw [valAt_mapVals_of_mem _ _ _ hh]
  have hhs : h ∈ s.positions := by rw [← takeLabel_positions s l]; exact hh
  have hv : FT (fun y => (L y ∧ ¬ s.Live y) ∨ (s.Live y ∧ x < y)) ((s.takeLabel l).valAt h) := by
    rcases takeLabel_valAt s l h with e | e
    · rw [e]; exact h2 h x hhs (takeLabel_shape_some hsx')
    · rw [e]; exact FT.const _ _
  refine (hv.updList fx).mono fun y ⟨hy, hn⟩ => ?_
  rcases hy with ⟨hL, hnl⟩ | ⟨hy, hlt⟩
  · exact .inl ⟨hL, fun h' => hnl (takeLabel_live_rev (live_mapVals.mp h'))⟩
  · have hne : y ≠ l := fun e => hn (e ▸ hl)
    exact .inr ⟨live_mapVals.mpr (takeLabel_live hy hne), hlt⟩

end SState

end Ochr.Meaning
