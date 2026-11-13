import Ochr.Meaning.LocalityRun

/-!
# The run keeps `run_congr`'s invariant (part (P) of the locality induction)

`run_rinv`: from a state with (I1), (I2) and `ShapeAt`, a successful run ends in such a state, and
the label its result carries (a borrow it returns) is live or read by no position ("live or
unread", `LoU`) — what the result's consumer (a `let`'s binding, an assignment) needs to hold it.
The globals are assumed to carry no label (`K.C.global`'s type component), as the program
meaning builds them.

This half does not compare futures: it is about one run. Part (E), `run_congr`, compares the runs
at two futures agreeing on `L` and reads (P) for the intermediate states.
-/

namespace Ochr.Meaning

open SState

section
variable (K : RunCtx) (ρ : Assignment) (φ : Future) (L : Nat → Prop)

/-- The label of a result is live, or no position reads it; either way it is below the counter (it
was issued). -/
def LoU (s : SState) (lab : Option Nat) : Prop :=
  ∀ l, lab = some l → (s.Live l ∨ ∀ q, Indep l (s.valAt q)) ∧ l < s.nextLoan

/-- A live label is below `nextLoan`. -/
theorem lou_live {s : SState} (hsa : ShapeAt s) {l : Nat} (h : s.Live l) :
    (s.Live l ∨ ∀ q, Indep l (s.valAt q)) ∧ l < s.nextLoan := by
  refine ⟨.inl h, ?_⟩
  obtain ⟨q, _, hs⟩ := (live_iff s l).mp h
  exact (hsa q l hs).2

theorem SM.bind_some {α β : Type 3} {x : SM α} {f : α → SM β} {s : SState} {r : β × SState}
    (h : (x >>= f) s = some r) : ∃ a s₁, x s = some (a, s₁) ∧ f a s₁ = some r := by
  simp only [Bind.bind, Monad.toBind, instMonadSM] at h
  cases hx : x s with
  | none => rw [hx] at h; cases h
  | some p => rw [hx] at h; exact ⟨p.1, p.2, rfl, h⟩

theorem SM.pure_some {α : Type 3} {a : α} {s : SState} {r : α × SState} (h : (pure a : SM α) s = some r) :
    r = (a, s) := by
  simp only [Pure.pure, Applicative.toPure, Monad.toApplicative, instMonadSM, Option.some.injEq] at h
  exact h.symm

/-- A meaning rewritten pointwise reads what it read. -/
theorem FT.comp {S : Nat → Prop} {f : SVal} (hf : FT S f) (g : Sem → Sem) : FT S (fun ψ => g (f ψ)) :=
  fun ψ ψ' h => by simp only [hf ψ ψ' h]

theorem endLabel_positions (s : SState) (l : Nat) : (s.endLabel l).positions = s.positions := by
  cases e : s.holderOf l with
  | none => rw [endLabel_of_none e]
  | some r => rw [endLabel_eq e, endAt_positions]

theorem foldl_endLabel_positions : ∀ (ls : List Nat) (s : SState), (ls.foldl SState.endLabel s).positions = s.positions
  | [], _ => rfl
  | l :: ls, s => by rw [List.foldl_cons, foldl_endLabel_positions ls, endLabel_positions]

theorem iterR_accStep_positions (p : Pos) : ∀ (k : Nat) (s : SState), (iterR (accStep p) k s).positions = s.positions
  | 0, _ => rfl
  | k + 1, s => by
    show (accStep p (iterR (accStep p) k s)).positions = _
    rw [accStep, foldl_endLabel_positions, iterR_accStep_positions p k]

theorem access_positions (s : SState) (p : Pos) : (s.access p).positions = s.positions := by
  rw [access_eq, foldl_range_iterR, iterR_accStep_positions]

theorem varPos_mem {s : SState} {i : Nat} {pos : Pos} (h : s.varPos i = some pos) : pos ∈ s.positions := by
  unfold SState.varPos at h
  cases e : s.env.getLast? with
  | none => rw [e] at h; cases h
  | some fr =>
    rw [e] at h
    simp only at h
    split at h
    · rename_i hi
      cases h
      rw [mem_positions]
      have e2 : s.env[s.topIdx]? = some fr := by
        rw [List.getLast?_eq_getElem?] at e; simpa [SState.topIdx] using e
      simp only [lookup, e2, Option.bind_some, Option.isSome_map]
      rw [List.getElem?_eq_getElem (by omega)]; rfl
    · cases h

theorem resolve_mem {s : SState} {p : Place} {pos : Pos} {steps : List Step}
    (h : resolve s p = some (pos, steps)) : pos ∈ s.positions := by
  unfold resolve at h
  cases e : s.varPos p.steps.1 with
  | none => simp [e] at h
  | some q =>
    simp only [e, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, _⟩ := h
    exact varPos_mem e

/-- [Access] then a read: the state is the accessed one, which keeps the invariant. -/
theorem contentOf_rinv {p : Place} {s s' : SState} {x : Sem × TyS × Pos × List Step}
    (h : contentOf K φ p s = some (x, s')) (hi : RInv L s) : RInv L s' ∧ x.2.2.1 ∈ s'.positions := by
  unfold contentOf at h
  cases hr : resolve s p with
  | none => rw [hr] at h; cases h
  | some ps =>
    obtain ⟨pos, steps⟩ := ps
    rw [hr] at h
    simp only at h
    split at h
    · simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      refine ⟨access_rinv hi pos, ?_⟩
      show pos ∈ (s.access pos).positions
      rw [access_positions]; exact resolve_mem hr
    · cases h

/-- A write of a constant at a path of a place keeps the invariant. -/
theorem setContent_rinv {pos : Pos} {steps : List Step} {v : Sem} {s s' : SState}
    (h : setContent K φ pos steps v s = some (⟨⟩, s')) (hi : RInv L s) : RInv L s' ∧ s'.shape = s.shape ∧
      s'.positions = s.positions := by
  unfold setContent at h
  simp only at h
  split at h
  · simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨_, rfl⟩ := h
    refine ⟨setAt_rinv hi pos _ ((hi.1 pos).comp (fun x => (Sem.updAt K.dm K.Γ (s.tyAt pos).m (fun _ => v) steps x).getD .err))
        (fun x hx => (hi.2.1 pos x ?_ hx).comp (fun x => (Sem.updAt K.dm K.Γ (s.tyAt pos).m (fun _ => v) steps x).getD .err)),
      shape_setAt' _ _ _, positions_setAt _ _ _⟩
    exact (hi.2.2 pos x hx).1
  · cases h

theorem live_of_shape {s : SState} {q : Pos} {l : Nat} (hq : q ∈ s.positions) (h : s.shape q = some l) : s.Live l :=
  (live_iff s l).mpr ⟨q, hq, h⟩

/-- **[Read]** keeps the invariant; a move carries the label the place held, still live (parked). -/
theorem readPlace_rinv {p : Place} {copy : Bool} {s s' : SState} {r : Res}
    (h : readPlace K φ p copy s = some (r, s')) (hi : RInv L s) : RInv L s' ∧ LoU s' r.2.label := by
  unfold readPlace at h
  cases hc : contentOf K φ p s with
  | none => rw [hc] at h; cases h
  | some x =>
    obtain ⟨⟨v, T, pos, steps⟩, s₁⟩ := x
    rw [hc] at h
    obtain ⟨hi₁, hpos⟩ := contentOf_rinv K φ L hc hi
    simp only [Bind.bind, Option.bind] at h
    split at h
    · cases h
    · split at h
      · simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        exact ⟨hi₁, fun l hl => by simp at hl⟩
      · cases hs : setContent K φ pos steps .moved s₁ with
        | none => rw [hs] at h; cases h
        | some y =>
          obtain ⟨⟨⟩, s₂⟩ := y
          rw [hs] at h
          obtain ⟨hi₂, hsh₂, hpos₂⟩ := setContent_rinv K φ L hs hi₁
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          generalize hlab : (if steps.isEmpty = true then s₁.shape pos else none) = lab
          cases lab with
          | none => exact ⟨hi₂, fun l' hl' => by simp at hl'⟩
          | some l =>
            have hlive : s₂.Live l := by
              split at hlab
              · exact live_of_shape (by rw [hpos₂]; exact hpos) (by rw [hsh₂]; exact hlab)
              · cases hlab
            refine ⟨transfer_rinv hi₂ l hlive v, fun l' hl' => ?_⟩
            simp only [Option.some.injEq] at hl'
            subst hl'
            apply lou_live (transfer_rinv hi₂ l hlive v).2.2
            have hne : (s₂.takeLabel l).env ≠ [] := by
              intro he
              obtain ⟨q, hq, _⟩ := (live_iff s₂ l).mp hlive
              have : q ∈ (s₂.takeLabel l).positions := by rw [takeLabel_positions]; exact hq
              rw [positions_eq, he] at this; simp at this
            exact live_pushTempShaped_self _ _ _ hne

/-- A meaning rewritten at the future's value at `l`: reads what it read and `l`. -/
theorem FT.withLabel {S : Nat → Prop} {f : SVal} (hf : FT S f) (l : Nat) (g : Sem → Sem → Sem) :
    FT (fun y => S y ∨ y = l) (fun ψ => g (ψ l) (f ψ)) := fun ψ ψ' h => by
  show g (ψ l) (f ψ) = g (ψ' l) (f ψ')
  rw [h l (.inr rfl), hf ψ ψ' fun y hy => h y (.inl hy)]

/-- **[Borrow]** keeps the invariant; the result carries the fresh label, live (parked). -/
theorem borrowPlace_rinv {p : Place} {s s' : SState} {r : Res}
    (h : borrowPlace K φ p s = some (r, s')) (hi : RInv L s) : RInv L s' ∧ LoU s' r.2.label := by
  unfold borrowPlace at h
  cases hc : contentOf K φ p s with
  | none => rw [hc] at h; cases h
  | some x =>
    obtain ⟨⟨v, T, pos, steps⟩, s₁⟩ := x
    rw [hc] at h
    obtain ⟨hi₁, hpos⟩ := contentOf_rinv K φ L hc hi
    simp only [Bind.bind, Option.bind] at h
    split at h
    · cases h
    simp only [SState.freshLoan, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    have hi₂ := freshLoan_rinv hi₁
    simp only [SState.freshLoan] at hi₂
    obtain ⟨h1, h2, hsa⟩ := hi₂
    have hne : ({ s₁ with nextLoan := s₁.nextLoan + 1 } : SState).env ≠ [] := by
      intro he
      have : pos ∈ ({ s₁ with nextLoan := s₁.nextLoan + 1 } : SState).positions := hpos
      rw [positions_eq, he] at this; simp at this
    refine ⟨writeFresh_park_rinv ⟨h1, h2, hsa⟩ pos _ s₁.nextLoan v hne
      (fun q x hq => (hi₁.2.2 q x hq).2) (Nat.lt_succ_self _) ?_ ?_, ?_⟩
    · exact ((h1 pos).withLabel s₁.nextLoan
          (fun a b => (Sem.updAt K.dm K.Γ (s₁.tyAt pos).m (fun _ => a) steps b).getD .err)).mono fun y hy => by
        rcases hy with hy | rfl
        · rcases hy with hL | hl
          · exact .inl hL
          · exact .inr (.inl hl)
        · exact .inr (.inr rfl)
    · intro x hx
      exact ((h2 pos x hpos hx).withLabel s₁.nextLoan
          (fun a b => (Sem.updAt K.dm K.Γ (s₁.tyAt pos).m (fun _ => a) steps b).getD .err)).mono fun y hy => by
        rcases hy with hy | rfl
        · rcases hy with h' | h'
          · exact .inl h'
          · exact .inr (.inl h')
        · exact .inr (.inr rfl)
    · intro l hl
      simp only [Option.some.injEq] at hl
      subst hl
      refine ⟨.inl ?_, ?_⟩
      · apply live_pushTempShaped_self
        cases pos <;> simpa [SState.setAt] using hne
      · rw [nextLoan_pushTempShaped, nextLoan_setAt']
        exact Nat.lt_succ_self _

/-- **D84's drop at the join** keeps the invariant: each dropped place is accessed, its root's borrow
ended, its content rewritten to `moved` at its path. -/
theorem joinDrop_rinv (entry : List Place) (t : Term) {s : SState} (hi : RInv L s) : RInv L (joinDrop K φ entry t s) := by
  unfold joinDrop
  generalize K.D.joinMoves (scopeOf s) entry t = qs
  induction qs generalizing s with
  | nil => exact hi
  | cons q qs ih =>
    simp only [List.foldl_cons]
    apply ih
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

theorem positions_mapVals' (s : SState) (g : Pos → SVal → SVal) : (s.mapVals g).positions = s.positions :=
  SState.positions_mapVals s g

theorem shapeAt_mapVals {s : SState} (hsa : ShapeAt s) (g : Pos → SVal → SVal) : ShapeAt (s.mapVals g) := by
  intro p x hp
  rw [positions_mapVals']
  exact hsa p x hp

theorem shapeAt_takeAll : ∀ (ls : List Nat) {s : SState}, ShapeAt s → ShapeAt (ls.foldl SState.takeLabel s)
  | [], _, h => h
  | l :: ls, _, h => shapeAt_takeAll ls (takeLabel_shapeAt h l)

/-- A state with no frame has no positions: every meaning reads nothing. -/
theorem indep_of_nil {s : SState} (he : s.env = []) (l : Nat) (q : Pos) : Indep l (s.valAt q) := by
  have : q ∉ s.positions := by rw [positions_eq, he]; simp
  rw [valAt_of_not_mem _ _ this]; intro _ _; rfl

/-- **A call** keeps the invariant; a returned borrow's fresh label is live (parked). -/
theorem callOfL_rinv.{u} (Lv : Lvl.{u}) (ps : List PiParam) (out : PiOut) (fv : Sem) (args : List Res)
    {s s' : SState} {r : Res} (hi : RInv L s) (h : callOfL Lv ps out fv args s = some (r, s')) :
    RInv L s' ∧ LoU s' r.2.label := by
  obtain ⟨h1, h2, hsa⟩ := hi
  cases happ : applyFnL Lv ps out fv (args.map (·.1)) with
  | none =>
    unfold callOfL at h; dsimp only at h; rw [happ] at h; cases h
  | some res =>
    cases res with
    | data r' finals =>
      have h' := h
      unfold callOfL at h'; dsimp only at h'; rw [happ] at h'
      simp only [Option.some.injEq, Prod.mk.injEq] at h'
      obtain ⟨rfl, rfl⟩ := h'
      obtain ⟨i1, i2⟩ := callOfL_data_inv Lv ps out fv args h1 h2 h (fun U fwd back e => by rw [happ] at e; cases e)
      exact ⟨⟨i1, i2, shapeAt_mapVals (shapeAt_takeAll _ hsa) _⟩, fun l hl => by simp [TyS.plain] at hl⟩
    | ref U fwd back =>
      obtain ⟨i1, i2⟩ := callOfL_ref_inv Lv ps out fv args h1 h2 hsa h happ
      have h' := h
      unfold callOfL at h'; dsimp only at h'; rw [happ] at h'
      simp only [SState.freshLoan, Option.some.injEq, Prod.mk.injEq] at h'
      obtain ⟨rfl, rfl⟩ := h'
      generalize hS : (SState.mapVals _ _ : SState) = S at i1 i2 ⊢
      have hsaS : ShapeAt S := by
        rw [← hS]
        apply shapeAt_mapVals
        intro p x hp
        obtain ⟨h1', h2'⟩ := shapeAt_takeAll _ hsa p x hp
        exact ⟨h1', Nat.lt_succ_of_lt h2'⟩
      have hnlS : S.nextLoan = (List.foldl SState.takeLabel s
          (List.filterMap id (List.map (fun x => x.1.2.label) (List.filter (fun x => x.2.isRef) (args.zip ps))))).nextLoan + 1 := by
        rw [← hS]; rfl
      by_cases hne : S.env = []
      · have hfin : S.pushTempShaped (fun _ => Lv.enc U fwd) (List.foldl SState.takeLabel s
            (List.filterMap id (List.map (fun x => x.1.2.label) (List.filter (fun x => x.2.isRef) (args.zip ps))))).nextLoan
            = S.pushTemp (fun _ => Lv.enc U fwd) := by
          unfold SState.pushTempShaped
          dsimp only
          rw [pushTemp_getLast, hne]; rfl
        rw [hfin] at i1 i2 ⊢
        have hnil : (S.pushTemp (fun _ => Lv.enc U fwd)).env = [] := by simp [SState.pushTemp, hne]
        refine ⟨⟨i1, i2, fun p x hp => ?_⟩, fun l hl => ⟨.inr fun q => indep_of_nil hnil l q, ?nl⟩⟩
        case nl =>
          simp only [Option.some.injEq] at hl
          subst hl
          show _ < (SState.pushTemp _ _).nextLoan
          rw [show (SState.pushTemp S _).nextLoan = S.nextLoan from rfl, hnlS]
          exact Nat.lt_succ_self _
        obtain ⟨hp1, _⟩ := hsaS p x hp
        rw [positions_eq, hne] at hp1; simp at hp1
      · refine ⟨⟨i1, i2, pushTempShaped_shapeAt hsaS hne _ _ (by rw [hnlS]; exact Nat.lt_succ_self _)⟩, ?_⟩
        intro l hl
        simp only [Option.some.injEq] at hl
        subst hl
        exact lou_live (pushTempShaped_shapeAt hsaS hne _ _ (by rw [hnlS]; exact Nat.lt_succ_self _))
          (live_pushTempShaped_self _ _ _ hne)

/-! ## A result's label stays live or unread

What runs after a sub-run inside a clause (a `let`'s drop, a match's drop at the join) keeps the
sub-result's label live or unread: ending the label itself leaves it read by no one (`endAt_indep`),
ending another or rewriting a meaning keeps both alternatives. -/

/-- The per-label part of `LoU`. -/
abbrev LoU1 (s : SState) (l : Nat) : Prop := (s.Live l ∨ ∀ q, Indep l (s.valAt q)) ∧ l < s.nextLoan

theorem lou_endLabel {s : SState} (h2 : Inv2 L s) {y : Nat} (hy : LoU1 s y) (x : Nat) : LoU1 (s.endLabel x) y := by
  cases e : s.holderOf x with
  | none => rw [endLabel_of_none e]; exact hy
  | some r =>
    rw [endLabel_eq e]
    obtain ⟨hr, hs⟩ := holderOf_spec e
    refine ⟨?_, hy.2⟩
    rcases hy.1 with hl | hu
    · by_cases hyx : y = x
      · subst hyx; exact .inr (endAt_indep h2 hr hs)
      · exact .inl (live_endAt hs hl hyx)
    · right
      intro q
      by_cases hq : q ∈ s.positions
      · rw [endAt_valAt _ _ _ _ hq]
        intro ψ c
        by_cases e' : q = r
        · simp [e']
        · simp only [e', if_false]
          rw [hu r ψ c]
          by_cases hyx : y = x
          · subst hyx; rw [Future.upd_upd_same]
          · rw [Future.upd_comm _ hyx]; exact hu q _ c
      · rw [endAt_valAt_not_mem _ _ _ _ hq]; exact hu q

theorem lou_foldl_endLabel {y : Nat} : ∀ (ls : List Nat) {s : SState}, RInv L s → LoU1 s y →
    LoU1 (ls.foldl endLabel s) y
  | [], _, _, hy => hy
  | l :: ls, _, hi, hy => lou_foldl_endLabel ls (endLabel_rinv hi l) (lou_endLabel L hi.2.1 hy l)

theorem lou_access {s : SState} (hi : RInv L s) {y : Nat} (hy : LoU1 s y) (p : Pos) : LoU1 (s.access p) y := by
  rw [access_eq, foldl_range_iterR]
  generalize s.liveLabels.length = k
  induction k with
  | zero => exact hy
  | succ k ih =>
    exact lou_foldl_endLabel L _ (iterR_accStep_rinv p k hi) ih

theorem lou_setAt {s : SState} {y : Nat} (hy : LoU1 s y) (p : Pos) (v : SVal)
    (hv : (∀ q, Indep y (s.valAt q)) → Indep y v) : LoU1 (s.setAt p v) y := by
  refine ⟨?_, by rw [nextLoan_setAt']; exact hy.2⟩
  rcases hy.1 with hl | hu
  · exact .inl ((live_setAt s p v y).mpr hl)
  · right
    intro q
    rcases valAt_setAt s p v q with e | e
    · rw [e]; exact hu q
    · rw [e]; exact hv hu

theorem indep_dropLast {s : SState} {y : Nat} (h : ∀ p, Indep y (s.valAt p)) (q : Pos) :
    Indep y (s.dropLast.valAt q) := by
  by_cases hq : q ∈ s.dropLast.positions
  · rw [valAt_dropLast s q (mem_positions_dropLast hq).2]; exact h q
  · rw [valAt_of_not_mem _ _ hq]; intro _ _; rfl

theorem lou_dropLast {s : SState} {y : Nat} (hy : LoU1 s y)
    (hind : ∀ r x, s.dropped = some r → s.shape r = some x → ∀ p, Indep x (s.valAt p)) :
    LoU1 s.dropLast y := by
  refine ⟨?_, hy.2⟩
  rcases hy.1 with hl | hu
  · obtain ⟨q, hq, hs⟩ := (live_iff s y).mp hl
    by_cases hqd : some q = s.dropped
    · exact .inr (indep_dropLast (hind q y hqd.symm hs))
    · refine .inl ((live_iff _ y).mpr ⟨q, mem_positions_dropLast' hq hqd, ?_⟩)
      rw [dropLast_shape, if_neg hqd]; exact hs
  · exact .inr (indep_dropLast hu)

/-- **D84's drop at the join** keeps a result's label live or unread (with the invariant). -/
theorem joinDrop_lou (entry : List Place) (t : Term) {s : SState} (hi : RInv L s) {y : Nat} (hy : LoU1 s y) :
    LoU1 (joinDrop K φ entry t s) y := by
  unfold joinDrop
  generalize K.D.joinMoves (scopeOf s) entry t = qs
  induction qs generalizing s with
  | nil => exact hy
  | cons q qs ih =>
    simp only [List.foldl_cons]
    apply ih
    · split
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
    · split
      · exact hy
      · split
        · rename_i pos steps hr
          have hia := access_rinv hi pos
          have hya := lou_access L hi hy pos
          split
          · exact hya
          · exact hya
          · exact hya
          · have hye : LoU1 (if steps.isEmpty = true then
                (match (s.access pos).shape pos with | some l => (s.access pos).endLabel l | none => s.access pos)
                else s.access pos) y := by
              split
              · split
                · exact lou_endLabel L hia.2.1 hya _
                · exact hya
              · exact hya
            generalize (if steps.isEmpty = true then
                (match (s.access pos).shape pos with | some l => (s.access pos).endLabel l | none => s.access pos)
                else s.access pos) = s₂ at hye ⊢
            exact lou_setAt hye pos _ fun hu ψ c => by
              show (Sem.updAt K.dm K.Γ (s₂.tyAt pos).m (fun _ => .moved) steps (s₂.valAt pos (ψ.upd y c))).getD .err
                = (Sem.updAt K.dm K.Γ (s₂.tyAt pos).m (fun _ => .moved) steps (s₂.valAt pos ψ)).getD .err
              rw [hu pos ψ c]
        · exact hy

end

end Ochr.Meaning
