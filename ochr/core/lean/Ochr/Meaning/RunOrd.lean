import Ochr.Meaning.RunEnv

/-!
# The run keeps its temporaries ordered (the fix frame's cells)

A `fix` body runs in a frame whose borrow parameters have *cells*: temporaries reading the
parameters' fresh labels, all at least the frame's start. After the pop, a cell must read only
`L` and the returned borrow's label (`FinalsIn`, for `closureAt_congr`). That holds because a cell
stays `Ordered` at the start (`ordered_after_pop`): it reads non-live labels of `L`, and live
labels at least the start. `OrdKeep L s s'` says a run step keeps every temporary of `s` that is
ordered at a bound below the counter ordered at that bound; every primitive does.

A temporary is never a place's root (`resolve` yields bindings), so the run writes it only by an
end (a substitution, `endLabel_ordered`), by a call's fixing of its arguments' labels, or, when it
holds a borrow, by a move (a constant). Otherwise only the live labels change, by labels at least
the counter coming in (fresh) and by labels no meaning reads coming in or going out.
-/

namespace Ochr.Meaning

open SState

universe u

/-- A temporary position. -/
def IsTemp : Pos → Prop
  | .temp _ _ => True
  | .bind _ _ => False

section
variable (L : Nat → Prop)

/-- A run step keeps its temporaries ordered: every temporary of `s` ordered at a bound at most
the counter is still ordered at that bound in `s'`; the counter does not go down. -/
def OrdKeep (s s' : SState) : Prop :=
  s.nextLoan ≤ s'.nextLoan ∧ ∀ (b : Nat) (c : Pos), b ≤ s.nextLoan → IsTemp c → c ∈ s.positions →
    Ordered L s b (s.valAt c) → Ordered L s' b (s'.valAt c)

variable {L}

theorem OrdKeep.refl (s : SState) : OrdKeep L s s := ⟨Nat.le_refl _, fun _ _ _ _ _ h => h⟩

theorem OrdKeep.trans' {a b c : SState} (h₁ : OrdKeep L a b) (e : ∀ q ∈ a.positions, q ∈ b.positions)
    (h₂ : OrdKeep L b c) : OrdKeep L a c :=
  ⟨Nat.le_trans h₁.1 h₂.1, fun x p hx ht hp ho =>
    h₂.2 x p (Nat.le_trans hx h₁.1) ht (e p hp) (h₁.2 x p hx ht hp ho)⟩

theorem OrdKeep.trans {a b c : SState} (h₁ : OrdKeep L a b) (e : EnvLe a b) (h₂ : OrdKeep L b c) :
    OrdKeep L a c :=
  h₁.trans' (fun _ hq => e.mem hq) h₂

/-- **An ordered meaning stays ordered** when it is kept or becomes a constant, and the live
labels change only by labels at least the bound or unread coming in, and unread going out. -/
theorem ordered_step {s s' : SState} {b : Nat} {f g : SVal} (hf : Ordered L s b f)
    (hv : g = f ∨ ∃ k, g = fun _ => k)
    (hadd : ∀ y, s'.Live y → ¬ s.Live y → b ≤ y ∨ Indep y f)
    (hrem : ∀ y, s.Live y → ¬ s'.Live y → Indep y f) : Ordered L s' b g := by
  rcases hv with rfl | ⟨k, rfl⟩
  · open Classical in
    refine FT.removeList ((s.liveLabels.filter fun y => decide (¬ s'.Live y)) ++
        (s'.liveLabels.filter fun y => decide (¬ s.Live y ∧ ¬ b ≤ y)))
      (hf.mono fun y hy => ?_) (fun y hy => ?_)
    · rcases hy with ⟨hL, hn⟩ | ⟨hy, hby⟩
      · by_cases h' : s'.Live y
        · by_cases hb : b ≤ y
          · exact .inl (.inr ⟨h', hb⟩)
          · exact .inr (List.mem_append_right _ (List.mem_filter.mpr ⟨h', by simp [hn, hb]⟩))
        · exact .inl (.inl ⟨hL, h'⟩)
      · by_cases h' : s'.Live y
        · exact .inl (.inr ⟨h', hby⟩)
        · exact .inr (List.mem_append_left _ (List.mem_filter.mpr ⟨hy, by simpa using h'⟩))
    · rcases List.mem_append.mp hy with hy | hy
      · obtain ⟨hl, hn⟩ := List.mem_filter.mp hy
        exact hrem y hl (by simpa using hn)
      · obtain ⟨hl, hn⟩ := List.mem_filter.mp hy
        simp only [decide_eq_true_eq] at hn
        exact (hadd y hl hn.1).resolve_left hn.2
  · exact FT.const _ _

/-- A step that keeps every temporary's meaning (or makes it a constant) and the counter. -/
theorem ordKeep_of {s s' : SState} (hn : s.nextLoan ≤ s'.nextLoan)
    (hv : ∀ c, IsTemp c → c ∈ s.positions → s'.valAt c = s.valAt c ∨ ∃ k, s'.valAt c = fun _ => k)
    (hadd : ∀ y, s'.Live y → ¬ s.Live y → s.nextLoan ≤ y ∨ ∀ q, Indep y (s.valAt q))
    (hrem : ∀ y, s.Live y → ¬ s'.Live y → ∀ q, Indep y (s.valAt q)) : OrdKeep L s s' :=
  ⟨hn, fun b c hb ht hc ho => ordered_step ho (hv c ht hc)
    (fun y h1 h2 => (hadd y h1 h2).imp (Nat.le_trans hb) (· c)) (fun y h1 h2 => hrem y h1 h2 c)⟩

theorem nextLoan_endLabel (s : SState) (l : Nat) : (s.endLabel l).nextLoan = s.nextLoan :=
  (shapeSub_endLabel s l).2

theorem ordKeep_endLabel {s : SState} (h2 : Inv2 L s) (l : Nat) : OrdKeep L s (s.endLabel l) :=
  ⟨by rw [nextLoan_endLabel]; exact Nat.le_refl _, fun _ _ _ _ _ ho => endLabel_ordered h2 l ho⟩

theorem ordKeep_foldl_endLabel : ∀ (ls : List Nat) {s : SState}, RInv L s → OrdKeep L s (ls.foldl endLabel s)
  | [], s, _ => OrdKeep.refl s
  | l :: ls, _, hi => (ordKeep_endLabel hi.2.1 l).trans (envLe_endLabel _ _)
      (ordKeep_foldl_endLabel ls (endLabel_rinv hi l))

theorem envLe_iterR (p : Pos) : ∀ (k : Nat) (s : SState), EnvLe s (iterR (accStep p) k s)
  | 0, s => EnvLe.refl s
  | k + 1, s => (envLe_iterR p k s).trans (envLe_foldl_endLabel _ _)

theorem ordKeep_access {s : SState} (hi : RInv L s) (p : Pos) : OrdKeep L s (s.access p) := by
  rw [access_eq, foldl_range_iterR]
  generalize s.liveLabels.length = k
  induction k with
  | zero => exact OrdKeep.refl s
  | succ k ih => exact ih.trans (envLe_iterR p k s) (ordKeep_foldl_endLabel _ (iterR_accStep_rinv p k hi))

/-! ## Writes at a binding, and the place primitives -/

theorem IsTemp.ne_bind {c : Pos} (h : IsTemp c) (f i : Nat) : c ≠ .bind f i := by
  cases c <;> simp_all [IsTemp]

theorem varPos_bind {s : SState} {i : Nat} {pos : Pos} (h : s.varPos i = some pos) : ¬ IsTemp pos := by
  unfold SState.varPos at h
  split at h
  · split at h
    · cases h; simp [IsTemp]
    · cases h
  · cases h

theorem resolve_bind {s : SState} {p : Place} {pos : Pos} {steps : List Step}
    (h : resolve s p = some (pos, steps)) : ¬ IsTemp pos := by
  unfold resolve at h
  cases e : s.varPos p.steps.1 with
  | none => simp [e] at h
  | some q =>
    simp only [e, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
    rw [← h.1]; exact varPos_bind e

theorem ordKeep_setAt {s : SState} {p : Pos} (hp : ¬ IsTemp p) (v : SVal) : OrdKeep L s (s.setAt p v) :=
  ordKeep_of (by rw [nextLoan_setAt']; exact Nat.le_refl _)
    (fun c ht _ => .inl (valAt_setAt_ne _ _ _ _ fun e => hp (e ▸ ht)))
    (fun y h1 h2 => absurd ((live_setAt s p v y).mp h1) h2)
    (fun y h1 h2 => absurd ((live_setAt s p v y).mpr h1) h2)

theorem ordKeep_setAt_const {s : SState} (p : Pos) (k : Sem) : OrdKeep L s (s.setAt p fun _ => k) :=
  ordKeep_of (by rw [nextLoan_setAt']; exact Nat.le_refl _)
    (fun c _ _ => by
      rcases valAt_setAt s p (fun _ => k) c with e | e
      · exact .inl e
      · exact .inr ⟨k, e⟩)
    (fun y h1 h2 => absurd ((live_setAt s p _ y).mp h1) h2)
    (fun y h1 h2 => absurd ((live_setAt s p _ y).mpr h1) h2)

section
variable (K : RunCtx) (φ : Future)

theorem contentOf_ordKeep {p : Place} {s s' : SState} {x : Sem × TyS × Pos × List Step} (hi : RInv L s)
    (h : contentOf K φ p s = some (x, s')) : OrdKeep L s s' ∧ ¬ IsTemp x.2.2.1 := by
  unfold contentOf at h
  cases hr : resolve s p with
  | none => rw [hr] at h; cases h
  | some ps =>
    obtain ⟨pos, steps⟩ := ps
    rw [hr] at h
    dsimp only at h
    split at h
    · simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨ordKeep_access hi pos, resolve_bind hr⟩
    · cases h

theorem setContent_ordKeep {pos : Pos} (hp : ¬ IsTemp pos) {steps : List Step} {v : Sem} {s s' : SState}
    (h : setContent K φ pos steps v s = some (⟨⟩, s')) : OrdKeep L s s' := by
  rw [setContent_eq K φ h]; exact ordKeep_setAt hp _

/-- A move's transfer: the holder is taken and the borrow parked again; the live labels are the
same. -/
theorem live_transfer {s : SState} (hsa : ShapeAt s) {l : Nat} (hl : s.Live l) (v : SVal) (y : Nat) :
    ((s.takeLabel l).pushTempShaped v l).Live y ↔ s.Live y := by
  have hne : (s.takeLabel l).env ≠ [] := by
    intro he
    obtain ⟨q, hq, _⟩ := (live_iff s l).mp hl
    have : q ∈ (s.takeLabel l).positions := by rw [takeLabel_positions]; exact hq
    rw [positions_eq, he] at this; simp at this
  constructor
  · intro h
    rcases live_pushTempShaped_new (takeLabel_shapeAt hsa l) h with h' | rfl
    · exact takeLabel_live_rev h'
    · exact hl
  · intro h
    by_cases hyl : y = l
    · subst hyl; exact live_pushTempShaped_self _ _ _ hne
    · exact live_pushTempShaped_old (takeLabel_live h hyl)

theorem valAt_pushTemp_old (s : SState) (v : SVal) {q : Pos} (hq : q ∈ s.positions) :
    (s.pushTemp v).valAt q = s.valAt q := by
  rw [valAt_eq, valAt_eq, lookup_pushTemp_old s v q ((mem_positions s q).mp hq)]

theorem ordKeep_transfer {s : SState} (hsa : ShapeAt s) {l : Nat} (hl : s.Live l) (v : SVal) :
    OrdKeep L s ((s.takeLabel l).pushTempShaped v l) :=
  ordKeep_of (by rw [nextLoan_pushTempShaped, (shapeSub_takeLabel s l).2]; exact Nat.le_refl _)
    (fun c _ hc => by
      rw [valAt_pushTempShaped, valAt_pushTemp_old _ _ (by rw [takeLabel_positions]; exact hc)]
      rcases takeLabel_valAt s l c with e | e
      · exact .inl e
      · exact .inr ⟨_, e⟩)
    (fun y h1 h2 => absurd ((live_transfer hsa hl v y).mp h1) h2)
    (fun y h1 h2 => absurd ((live_transfer hsa hl v y).mpr h1) h2)

theorem readPlace_ordKeep {p : Place} {copy : Bool} {s s' : SState} {r : Res}
    (h : readPlace K φ p copy s = some (r, s')) (hi : RInv L s) : OrdKeep L s s' := by
  unfold readPlace at h
  cases hc : contentOf K φ p s with
  | none => rw [hc] at h; cases h
  | some x =>
    obtain ⟨⟨v, T, pos, steps⟩, s₁⟩ := x
    rw [hc] at h
    obtain ⟨o₁, hpb⟩ := contentOf_ordKeep K φ hi hc
    have e₁ := contentOf_envLe K φ hc
    obtain ⟨hi₁, hpos⟩ := contentOf_rinv K φ L hc hi
    simp only [Bind.bind, Option.bind] at h
    split at h
    · cases h
    · split at h
      · simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        exact o₁
      · cases hs : setContent K φ pos steps .moved s₁ with
        | none => rw [hs] at h; cases h
        | some y =>
          obtain ⟨⟨⟩, s₂⟩ := y
          rw [hs] at h
          have o₂ := o₁.trans e₁ (setContent_ordKeep K φ hpb hs)
          have e₂ := e₁.trans (setContent_envLe K φ hs)
          obtain ⟨hi₂, hsh₂, hpos₂⟩ := setContent_rinv K φ L hs hi₁
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          split
          · rename_i l hlab
            have hlive : s₂.Live l := by
              split at hlab
              · exact live_of_shape (by rw [hpos₂]; exact hpos) (by rw [hsh₂]; exact hlab)
              · cases hlab
            exact o₂.trans e₂ (ordKeep_transfer hi₂.2.2 hlive _)
          · exact o₂

theorem borrowPlace_ordKeep {p : Place} {s s' : SState} {r : Res}
    (h : borrowPlace K φ p s = some (r, s')) (hi : RInv L s) : OrdKeep L s s' := by
  unfold borrowPlace at h
  cases hc : contentOf K φ p s with
  | none => rw [hc] at h; cases h
  | some x =>
    obtain ⟨⟨v, T, pos, steps⟩, s₁⟩ := x
    rw [hc] at h
    obtain ⟨o₁, hpb⟩ := contentOf_ordKeep K φ hi hc
    have e₁ := contentOf_envLe K φ hc
    obtain ⟨hi₁, hpos⟩ := contentOf_rinv K φ L hc hi
    simp only [Bind.bind, Option.bind] at h
    split at h
    · cases h
    simp only [SState.freshLoan, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    refine o₁.trans e₁ (ordKeep_of ?_ ?_ ?_ ?_)
    · rw [nextLoan_pushTempShaped, nextLoan_setAt']; exact Nat.le_succ _
    · intro c hct hcm
      rw [valAt_pushTempShaped, valAt_pushTemp_old _ _ (by rw [positions_setAt]; exact hcm),
        valAt_setAt_ne _ _ _ _ fun e => hpb (by show IsTemp pos; rw [e]; exact hct)]
      exact .inl rfl
    · intro y h1 h2
      rcases live_pushTempShaped_new (s := ({ s₁ with nextLoan := s₁.nextLoan + 1 } : SState).setAt pos _)
          (fun q x hq => by
            rw [shape_setAt'] at hq
            rw [positions_setAt, nextLoan_setAt']
            exact ⟨(hi₁.2.2 q x hq).1, Nat.lt_succ_of_lt (hi₁.2.2 q x hq).2⟩) h1 with h' | rfl
      · exact absurd ((live_setAt _ _ _ y).mp h') h2
      · exact .inl (Nat.le_refl _)
    · intro y h1 h2
      exact absurd (live_pushTempShaped_old ((live_setAt ({ s₁ with nextLoan := s₁.nextLoan + 1 } : SState)
        pos _ y).mpr h1)) h2

end

/-! ## A `let`: the binding pushed as a holder, and dropped -/

/-- The live labels after pushing a binding as a holder: the old ones and the binding's label. -/
theorem live_pushBindShaped {s : SState} (hsa : ShapeAt s) (b : SBinding) (hne : s.env ≠ []) (y : Nat) :
    (pushBindShaped s b).Live y ↔ s.Live y ∨ b.ty.label = some y := by
  unfold pushBindShaped
  cases hlab : b.ty.label with
  | none => simp only [live_pushBind hsa b y]; simp
  | some l =>
    have hsat := takeLabel_shapeAt hsa l
    dsimp only
    rw [pushBind_getLast]
    cases e : (s.takeLabel l).env.getLast? with
    | none =>
      exfalso
      have : (s.takeLabel l).env = [] := List.getLast?_eq_none_iff.mp e
      apply hne
      have hl := (envLe_takeLabel s l).1
      rw [this] at hl
      exact List.eq_nil_of_length_eq_zero hl.symm
    | some fr0 =>
      simp only [Option.map_some]
      have e2 : (s.takeLabel l).env[(s.takeLabel l).topIdx]? = some fr0 := by
        rw [List.getLast?_eq_getElem?] at e; simpa [SState.topIdx] using e
      have hnewpos : Pos.bind ((s.takeLabel l).pushBind b).topIdx ((fr0.binds ++ [b]).length - 1)
          ∈ ((s.takeLabel l).pushBind b).positions := by
        rw [pushBind_topIdx, mem_positions]
        simp only [lookup, SState.pushBind, List.getElem?_modify, e2]
        simp
      have hnewold : Pos.bind ((s.takeLabel l).pushBind b).topIdx ((fr0.binds ++ [b]).length - 1)
          ∉ (s.takeLabel l).positions := by
        rw [pushBind_topIdx, mem_positions]
        simp [lookup, e2]
      generalize Pos.bind ((s.takeLabel l).pushBind b).topIdx ((fr0.binds ++ [b]).length - 1) = N
        at hnewpos hnewold ⊢
      rw [live_iff]
      constructor
      · rintro ⟨q, hq, hs⟩
        simp only at hs
        split at hs
        · cases hs; exact .inr rfl
        · exact .inl (takeLabel_live_rev ((live_iff _ y).mpr ⟨q, (hsat q y hs).1, hs⟩))
      · intro hy
        by_cases hyl : y = l
        · subst hyl; exact ⟨N, hnewpos, by simp⟩
        · have hyt := takeLabel_live (hy.resolve_right (fun h => hyl (Option.some.inj h).symm)) hyl
          obtain ⟨q, hq, hs⟩ := (live_iff _ y).mp hyt
          refine ⟨q, mem_positions_pushBind _ b hq, ?_⟩
          have hqN : q ≠ N := by intro e'; rw [e'] at hq; exact hnewold hq
          simp only [if_neg hqN]; exact hs

theorem valAt_pushBindShaped_old {s : SState} (b : SBinding) {q : Pos} (hq : q ∈ s.positions) :
    (pushBindShaped s b).valAt q = s.valAt q ∨ (pushBindShaped s b).valAt q = fun _ => .moved := by
  unfold pushBindShaped
  cases b.ty.label with
  | none =>
    rcases valAt_pushBind s b q with e | e
    · exact .inl e
    · exact .inl (by rw [valAt_eq, valAt_eq, lookup_pushBind_old s b q ((mem_positions s q).mp hq)])
  | some l =>
    dsimp only
    have hq' : q ∈ (s.takeLabel l).positions := by rw [takeLabel_positions]; exact hq
    have hv : ((s.takeLabel l).pushBind b).valAt q = (s.takeLabel l).valAt q := by
      rw [valAt_eq, valAt_eq, lookup_pushBind_old _ b q ((mem_positions _ q).mp hq')]
    split
    · show ((s.takeLabel l).pushBind b).valAt q = _ ∨ ((s.takeLabel l).pushBind b).valAt q = _
      rw [hv]; exact takeLabel_valAt s l q
    · rw [hv]; exact takeLabel_valAt s l q

theorem mem_positions_pushBindShaped {s : SState} (b : SBinding) {q : Pos} (hq : q ∈ s.positions) :
    q ∈ (pushBindShaped s b).positions := by
  unfold pushBindShaped
  split
  · rename_i l _
    dsimp only
    have hq' : q ∈ ((s.takeLabel l).pushBind b).positions :=
      mem_positions_pushBind _ b (by rw [takeLabel_positions]; exact hq)
    split
    · exact hq'
    · exact hq'
  · exact mem_positions_pushBind _ b hq

theorem ordKeep_pushBindShaped {s : SState} (hi : RInv L s) (b : SBinding)
    (hl : ∀ l, b.ty.label = some l → (s.Live l ∨ ∀ q, Indep l (s.valAt q)) ∧ l < s.nextLoan) :
    OrdKeep L s (pushBindShaped s b) := by
  by_cases hne : s.env = []
  · -- no frame: no positions, so nothing to keep
    refine ⟨?_, fun _ c _ _ hc _ => ?_⟩
    · unfold pushBindShaped; split
      · dsimp only; split <;> exact (shapeSub_takeLabel s _).2.symm ▸ Nat.le_refl _
      · exact Nat.le_refl _
    · rw [positions_eq, hne] at hc; simp at hc
  refine ordKeep_of ?_ (fun c _ hc => ?_) (fun y h1 h2 => ?_) (fun y h1 h2 => ?_)
  · unfold pushBindShaped; split
    · dsimp only; split <;> exact (shapeSub_takeLabel s _).2.symm ▸ Nat.le_refl _
    · exact Nat.le_refl _
  · rcases valAt_pushBindShaped_old b hc with e | e
    · exact .inl e
    · exact .inr ⟨_, e⟩
  · rcases (live_pushBindShaped hi.2.2 b hne y).mp h1 with h' | h'
    · exact absurd h' h2
    · exact .inr ((hl y h').1.resolve_left h2)
  · exact absurd ((live_pushBindShaped hi.2.2 b hne y).mpr (.inl h1)) h2

theorem ordKeep_dropLast {s : SState}
    (hind : ∀ r x, s.dropped = some r → s.shape r = some x → ∀ p, Indep x (s.valAt p)) :
    OrdKeep L s s.dropLast := by
  refine ordKeep_of (Nat.le_refl _) (fun c ht hc => .inl ?_) (fun y h1 h2 => ?_) (fun y h1 h2 => ?_)
  · apply valAt_dropLast
    unfold dropped
    split
    · intro e; cases e; exact ht
    · intro e; cases e
  · rw [live_iff] at h1
    obtain ⟨q, hq, hs⟩ := h1
    obtain ⟨hq1, hq2⟩ := mem_positions_dropLast hq
    rw [dropLast_shape, if_neg hq2] at hs
    exact absurd ((live_iff s y).mpr ⟨q, hq1, hs⟩) h2
  · obtain ⟨q, hq, hs⟩ := (live_iff s y).mp h1
    by_cases hqd : some q = s.dropped
    · exact hind q y hqd.symm hs
    · refine absurd ((live_iff _ y).mpr ⟨q, mem_positions_dropLast' hq hqd, ?_⟩) h2
      rw [dropLast_shape, if_neg hqd]; exact hs

/-! ## An assignment's hold, a closure's moves, the join's drop -/

theorem ordKeep_hold {s : SState} {pos : Pos} (hpos : pos ∈ s.positions) {l : Nat} (hl : LoU1 s l)
    (hold : ∀ x, s.shape pos = some x → ∀ q, Indep x (s.valAt q)) :
    OrdKeep L s { s.takeLabel l with shape := fun q => if q = pos then some l else (s.takeLabel l).shape q } := by
  generalize hF : ({ s.takeLabel l with shape := fun q => if q = pos then some l else (s.takeLabel l).shape q }
    : SState) = F
  have hposF : F.positions = s.positions := by rw [← hF, ← takeLabel_positions s l]; rfl
  have hshF : ∀ q, F.shape q = if q = pos then some l else (s.takeLabel l).shape q := by
    intro q; rw [← hF]
  have hlF : F.Live l := (live_iff F l).mpr ⟨pos, by rw [hposF]; exact hpos, by rw [hshF]; simp⟩
  refine ordKeep_of ?_ (fun c _ _ => ?_) (fun y h1 h2 => ?_) (fun y h1 h2 => ?_)
  · rw [← hF]; exact Nat.le_of_eq (shapeSub_takeLabel s l).2.symm
  · rw [← hF]; exact (takeLabel_valAt s l c).imp id fun e => ⟨_, e⟩
  · obtain ⟨q, hq, hs⟩ := (live_iff F y).mp h1
    rw [hshF] at hs
    split at hs
    · cases hs; exact .inr (hl.1.resolve_left h2)
    · exact absurd (live_of_shape (by rw [← hposF]; exact hq) (takeLabel_shape_some hs)) h2
  · by_cases hyl : y = l
    · subst hyl; exact absurd hlF h2
    obtain ⟨q, hq, hs⟩ := (live_iff _ y).mp (takeLabel_live h1 hyl)
    by_cases hqp : q = pos
    · subst hqp; exact hold y (takeLabel_shape_some hs)
    · refine absurd ((live_iff F y).mpr ⟨q, by rw [hposF, ← takeLabel_positions s l]; exact hq, ?_⟩) h2
      rw [hshF, if_neg hqp]; exact hs

theorem ordKeep_foldl_moves (g : SState → Nat → SState)
    (hg : ∀ s i, g s i = s ∨ ∃ pos, g s i = s.setAt pos fun _ => .moved) :
    ∀ (vs : List Nat) (s : SState), OrdKeep L s (vs.foldl g s)
  | [], s => OrdKeep.refl s
  | v :: vs, s => by
    simp only [List.foldl_cons]
    rcases hg s v with e | ⟨pos, e⟩
    · rw [e]; exact ordKeep_foldl_moves g hg vs s
    · rw [e]; exact (ordKeep_setAt_const pos _).trans (envLe_setAt _ _ _) (ordKeep_foldl_moves g hg vs _)

section
variable (K : RunCtx) (φ : Future)

theorem joinDrop_ordKeep (entry : List Place) (t : Term) {s : SState} (hi : RInv L s) : OrdKeep L s (joinDrop K φ entry t s) := by
  unfold joinDrop
  generalize K.D.joinMoves (scopeOf s) entry t = qs
  induction qs generalizing s with
  | nil => exact OrdKeep.refl s
  | cons q qs ih =>
    simp only [List.foldl_cons]
    refine OrdKeep.trans ?o ?e (ih ?r)
    case r =>
      split
      · exact hi
      · split
        · rename_i pos steps hr
          have hia := access_rinv hi pos
          split
          · exact hia
          · exact hia
          · exact hia
          · have hie : RInv L (if steps.isEmpty = true then
                (match (s.access pos).shape pos with | some l => (s.access pos).endLabel l | none => s.access pos)
                else s.access pos) := by
              split
              · split
                · exact endLabel_rinv hia _
                · exact hia
              · exact hia
            generalize (if steps.isEmpty = true then
                (match (s.access pos).shape pos with | some l => (s.access pos).endLabel l | none => s.access pos)
                else s.access pos) = s₂ at hie ⊢
            exact setAt_rinv hie pos _
              ((hie.1 pos).comp (fun x => (Sem.updAt K.dm K.Γ (s₂.tyAt pos).m (fun _ => .moved) steps x).getD .err))
              (fun x hx => by
                by_cases hp : pos ∈ s₂.positions
                · exact (hie.2.1 pos x hp hx).comp
                    (fun x => (Sem.updAt K.dm K.Γ (s₂.tyAt pos).m (fun _ => .moved) steps x).getD .err)
                · exact absurd (hie.2.2 pos x hx).1 hp)
        · exact hi
    case e =>
      split
      · exact EnvLe.refl s
      · split
        · rename_i pos steps hr
          have ea := envLe_access s pos
          split
          · exact ea
          · exact ea
          · exact ea
          · have ee : EnvLe s (if steps.isEmpty = true then
                (match (s.access pos).shape pos with | some l => (s.access pos).endLabel l | none => s.access pos)
                else s.access pos) := by
              split
              · split
                · exact ea.trans (envLe_endLabel _ _)
                · exact ea
              · exact ea
            generalize (if steps.isEmpty = true then
                (match (s.access pos).shape pos with | some l => (s.access pos).endLabel l | none => s.access pos)
                else s.access pos) = s₂ at ee ⊢
            exact ee.trans (envLe_setAt _ _ _)
        · exact EnvLe.refl s
    case o =>
      split
      · exact OrdKeep.refl s
      · split
        · rename_i pos steps hr
          have hia := access_rinv hi pos
          have oa := ordKeep_access hi pos
          have ea := envLe_access s pos
          split
          · exact oa
          · exact oa
          · exact oa
          · have hoe : OrdKeep L s (if steps.isEmpty = true then
                (match (s.access pos).shape pos with | some l => (s.access pos).endLabel l | none => s.access pos)
                else s.access pos) ∧ EnvLe s (if steps.isEmpty = true then
                (match (s.access pos).shape pos with | some l => (s.access pos).endLabel l | none => s.access pos)
                else s.access pos) := by
              split
              · split
                · exact ⟨oa.trans ea (ordKeep_endLabel hia.2.1 _), ea.trans (envLe_endLabel _ _)⟩
                · exact ⟨oa, ea⟩
              · exact ⟨oa, ea⟩
            generalize (if steps.isEmpty = true then
                (match (s.access pos).shape pos with | some l => (s.access pos).endLabel l | none => s.access pos)
                else s.access pos) = s₂ at hoe ⊢
            exact hoe.1.trans hoe.2 (ordKeep_setAt (resolve_bind hr) _)
        · exact OrdKeep.refl s

end

/-! ## A call: the borrow arguments' labels taken and fixed -/

theorem takeAll_fix_ordKeep {s : SState} (ls : List Nat) (fx : List (Nat × Sem)) (hl : ∀ l ∈ ls, l ∈ fx.map (·.1)) :
    OrdKeep L s ((ls.foldl takeLabel s).mapVals fun _ v ψ => v (ψ.updList fx)) := by
  refine ⟨Nat.le_of_eq (shapeSub_foldl_takeLabel ls s).2.symm, fun b c _ _ hc ho => ?_⟩
  have hc' : c ∈ (ls.foldl takeLabel s).positions := by rw [takeAll_positions]; exact hc
  rw [valAt_mapVals_of_mem _ _ _ hc']
  have hv : Ordered L s b ((ls.foldl takeLabel s).valAt c) := by
    rcases takeAll_valAt c ls s with e | e
    · rw [e]; exact ho
    · rw [e]; exact FT.const _ _
  refine (hv.updList fx).mono fun y ⟨hy, hn⟩ => ?_
  rcases hy with ⟨hL, hnl⟩ | ⟨hy, hby⟩
  · exact .inl ⟨hL, fun h' => hnl (takeAll_live_rev ls (live_mapVals.mp h'))⟩
  · exact .inr ⟨live_mapVals.mpr (takeAll_live ls hy fun hm => hn (hl y hm)), hby⟩

theorem park_fix_ordKeep {s : SState} (hsa : ShapeAt s) {X : Type u} (ls : List Nat) (dec : Sem → Option X)
    (fx : X → List (Nat × Sem)) (hcov : ∀ x, ∀ l ∈ ls, l ∈ (fx x).map (·.1)) (c : Sem) (g : Pos → SVal → SVal)
    (hg : ∀ p v ψ, (∃ x, dec (ψ (ls.foldl takeLabel s).nextLoan) = some x ∧ g p v ψ = v (ψ.updList (fx x))) ∨
      (dec (ψ (ls.foldl takeLabel s).nextLoan) = none ∧ g p v ψ = .err)) :
    OrdKeep L s (((SState.mk (ls.foldl takeLabel s).env (ls.foldl takeLabel s).shape
      ((ls.foldl takeLabel s).nextLoan + 1)).mapVals g).pushTempShaped (fun _ => c) (ls.foldl takeLabel s).nextLoan) := by
  generalize hs₁ : ls.foldl takeLabel s = s₁
  generalize hk : s₁.nextLoan = k
  have hpos₁ : s₁.positions = s.positions := by rw [← hs₁]; exact takeAll_positions s ls
  have hk' : k = s.nextLoan := by rw [← hk, ← hs₁]; exact (shapeSub_foldl_takeLabel ls s).2
  rw [hs₁, hk] at hg
  generalize hs₃ : (SState.mk s₁.env s₁.shape (k + 1)).mapVals g = s₃
  have hpos₃ : s₃.positions = s.positions := by rw [← hs₃, positions_mapVals]; exact hpos₁
  have hlive₃ : ∀ y, s₃.Live y ↔ s₁.Live y := by intro y; rw [← hs₃, live_mapVals]; rfl
  have hsa₃ : ShapeAt s₃ := by
    intro p x hp
    have hp' : s₁.shape p = some x := by rw [← hs₃] at hp; exact hp
    have hp'' := takeAll_shape_some ls (by rw [hs₁]; exact hp')
    refine ⟨by rw [hpos₃]; exact (hsa p x hp'').1, ?_⟩
    rw [← hs₃]; show x < k + 1
    have := (hsa p x hp'').2; omega
  refine ⟨?_, fun b q hb _ hq ho => ?_⟩
  · rw [nextLoan_pushTempShaped, ← hs₃]; show s.nextLoan ≤ k + 1; omega
  have hq₃ : q ∈ s₃.positions := by rw [hpos₃]; exact hq
  rw [valAt_pushTempShaped, valAt_pushTemp_old _ _ hq₃, ← hs₃,
    valAt_mapVals_of_mem _ _ _ (by show q ∈ s₁.positions; rw [hpos₁]; exact hq), hs₃]
  have hv : Ordered L s b (s₁.valAt q) := by
    rcases takeAll_valAt q ls s with e | e
    · rw [hs₁] at e; rw [e]; exact ho
    · rw [hs₁] at e; rw [e]; exact FT.const _ _
  have hlive' : ∀ y, (s₃.pushTempShaped (fun _ => c) k).Live y → s₁.Live y ∨ y = k := fun y h =>
    (live_pushTempShaped_new hsa₃ h).imp_left (hlive₃ y).mp
  intro ψ ψ' hψ
  show g q (s₁.valAt q) ψ = g q (s₁.valAt q) ψ'
  have hkk : ψ k = ψ' k := by
    by_cases hne : s₃.env = []
    · -- no frame: no positions, so the temporary is not one
      exfalso; rw [positions_eq, hne] at hq₃; simp at hq₃
    · exact hψ k (.inr ⟨live_pushTempShaped_self _ _ _ hne, by omega⟩)
  rcases hg q (s₁.valAt q) ψ with ⟨x, hx, e⟩ | ⟨hx, e⟩ <;>
    rcases hg q (s₁.valAt q) ψ' with ⟨x', hx', e'⟩ | ⟨hx', e'⟩
  · rw [hkk, hx'] at hx; cases hx
    rw [e, e']
    apply hv
    apply updList_dec_agree (fx x)
    intro y hy hn
    rcases hy with ⟨hL, hnl⟩ | ⟨hy, hby⟩
    · by_cases hyk : y = k
      · rw [hyk]; exact hkk
      apply hψ y
      refine .inl ⟨hL, fun h' => ?_⟩
      rcases hlive' y h' with h'' | h''
      · exact hnl (takeAll_live_rev ls (by rw [hs₁]; exact h''))
      · exact hyk h''
    · apply hψ y
      refine .inr ⟨live_pushTempShaped_old ((hlive₃ y).mpr ?_), hby⟩
      rw [← hs₁]; exact takeAll_live ls hy fun hm => hn (hcov x y hm)
  · rw [hkk, hx'] at hx; cases hx
  · rw [hkk, hx'] at hx; cases hx
  · rw [e, e']

theorem callOfL_ordKeep.{v} (Lv : Lvl.{v}) (ps : List PiParam) (out : PiOut) (fv : Sem) (args : List Res)
    {s s' : SState} {r : Res} (hi : RInv L s) (h : callOfL Lv ps out fv args s = some (r, s')) :
    OrdKeep L s s' := by
  cases happ : applyFnL Lv ps out fv (args.map (·.1)) with
  | none => unfold callOfL at h; dsimp only at h; rw [happ] at h; cases h
  | some res =>
    unfold applyFnL at happ
    obtain ⟨F, hu, happ'⟩ : ∃ F, Lv.unpack (piCarL Lv ps [] PUnit out) fv = some F ∧
        applyTeleL Lv ps [] PUnit (fun _ => []) out F (args.map (·.1)) = some res := by
      cases hu : Lv.unpack (piCarL Lv ps [] PUnit out) fv with
      | none => rw [hu] at happ; cases happ
      | some F => rw [hu] at happ; exact ⟨F, rfl, happ⟩
    obtain ⟨hlen, hfin⟩ := applyTeleL_len Lv ps [] PUnit (fun _ => []) out F _ 0 (fun _ => rfl) _ happ'
    simp only [List.length_map] at hlen
    simp only [Nat.zero_add] at hfin
    have happ2 : applyFnL Lv ps out fv (args.map (·.1)) = some res := by
      unfold applyFnL; rw [hu]; exact happ'
    cases res with
    | data r' finals =>
      unfold callOfL at h; dsimp only at h; rw [happ2] at h
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨_, rfl⟩ := h
      apply takeAll_fix_ordKeep
      apply fixes_cover
      rw [List.length_map, zip_filter_len args ps hlen, hfin]
      exact Nat.le_refl _
    | ref U fwd back =>
      unfold callOfL at h; dsimp only at h; rw [happ2] at h
      simp only [SState.freshLoan, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨_, rfl⟩ := h
      have hcover : ∀ x, ∀ l ∈ (((args.zip ps).filter (·.2.isRef)).map (·.1.2.label)).filterMap id,
          l ∈ (((((args.zip ps).filter (·.2.isRef)).map (·.1.2.label)).zip (back x)).filterMap
            fun (y : Option Nat × Sem) => y.1.map (·, y.2)).map (·.1) := by
        intro x
        have hfx : (fun (y : Option Nat × Sem) => y.1.map (·, y.2)) = (fun (l?, f) => l?.map (·, f)) :=
          funext fun ⟨_, _⟩ => rfl
        rw [hfx]
        apply fixes_cover
        rw [List.length_map, zip_filter_len args ps hlen, hfin x]
        exact Nat.le_refl _
      apply park_fix_ordKeep hi.2.2 _ (Lv.dec U) _ hcover (Lv.enc U fwd)
      intro p v ψ
      cases hd : Lv.dec U (ψ ((((((args.zip ps).filter (·.2.isRef)).map (·.1.2.label)).filterMap id)).foldl
          SState.takeLabel s).nextLoan) with
      | none => exact .inr ⟨rfl, by simp only [hd]⟩
      | some x => exact .inl ⟨x, rfl, by simp only [hd]⟩

end

end Ochr.Meaning
