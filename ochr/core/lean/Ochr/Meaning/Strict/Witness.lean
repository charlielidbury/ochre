import Ochr.Meaning.Strict.Fund
import Ochr.Meaning.Strict.FieldWriteCE
import Ochr.Meaning.Strict.ReadProto

/-!
# The fundamental lemma applied: runs that write at a field path (non-vacuity witnesses)

`Fund.fund_all` at concrete contexts whose obligations hold (`FundCtx`), applied to strict runs that
succeed from good states and write at a field path: a move out of a field (`w_move`), a refill of the
moved part (`w_refill`), the join's drop of a field (`w_joinDrop`), and a borrow of an index field
whose dependent sibling D112 invalidates (`w_borrowIndex`). Each says the run succeeds (so the strict
tests pass on it) and, by the lemma, leaves a good state. For the strict end (ruling (A), docs/31
D106): a borrow ended over content moved out through it fails the run (`run_endBad`), and one ended
after the moved part is refilled runs (`w_endOk`).
-/

namespace Ochr.Meaning.Strict.Witness

open Ochr Ochr.Meaning Ochr.Meaning.Strict
open Ochr.Meaning.Strict.FieldWriteCE (nat_mem)

/-! ## Helpers: states with no live label -/

section
variable {K : RunCtx} {φ : Future}

/-- A write at a path of a position whose meaning is a constant: the test is the update at it. -/
theorem setContent_const {s : SState} {pos : Pos} {steps : List Step} {v c c' : Sem}
    (hc : s.valAt pos = fun _ => c) (hu : Sem.updAt K.dm K.Γ (s.tyAt pos) (fun _ => v) steps c = some c') :
    setContent K φ pos steps v s = some (⟨⟩, s.setAt pos fun _ => c') := by
  unfold setContent
  rw [if_pos (fun ψ _ => by rw [hc]; simp [hu])]
  simp only [hc, hu, Option.getD_some]

/-- With no live label, the run's future is the one typed future. -/
theorem typedFut_noLive {s : SState} (hl : s.liveLabels = []) {ψ : Future} (h : TypedFut K φ s ψ) : ψ = φ :=
  funext fun l => h.1 l (by rw [hl]; simp)

theorem typedFut_self_noLive {s : SState} (hl : s.liveLabels = []) : TypedFut K φ s φ :=
  ⟨fun _ _ => rfl, fun l h => by rw [hl] at h; cases h⟩

/-- The run's future is typed where it gives each live label a member of its record's type. -/
theorem typedFut_self_live {s : SState} (h : ∀ l ∈ s.liveLabels, φ l ∈ₛ[K.dm.read] s.heldTy l) : TypedFut K φ s φ :=
  ⟨fun _ _ => rfl, h⟩

end

/-- [Access] that reaches no label is the identity. -/
theorem access_unreached {s : SState} {p : Pos} {hit : List Step → Bool} (h : ∀ l, s.reached p hit l = false) :
    s.access p hit = s := by
  have hstep : (s.liveLabels.filter (s.reached p hit)).foldl SState.endLabel s = s := by
    rw [List.filter_eq_nil_iff.mpr (fun l _ => by simp [h l])]; rfl
  unfold SState.access
  dsimp only
  generalize List.range s.liveLabels.length = L
  induction L with
  | nil => rfl
  | cons _ L ih => rw [List.foldl_cons, hstep, ih]

theorem access_noLive {s : SState} (hl : s.liveLabels = []) (p : Pos) (hit : List Step → Bool) :
    s.access p hit = s := by
  unfold SState.access
  rw [hl]
  rfl

/-- With no live label, nothing ends: every end test holds. -/
theorem accessOk_noLive {K : RunCtx} {φ : Future} {s : SState} (hl : s.liveLabels = []) (p : Pos)
    (hit : List Step → Bool) : AccessOk K φ s p hit := fun k hk => by rw [hl] at hk; cases hk

theorem contentOk_noLive {K : RunCtx} {φ : Future} {s : SState} (hl : s.liveLabels = []) (q : Place) :
    ContentOk K φ q s := by
  unfold ContentOk; split
  · exact accessOk_noLive hl _ _
  · trivial

theorem tagOk_noLive {K : RunCtx} {φ : Future} {s : SState} (hl : s.liveLabels = []) (q : Place) :
    TagOk K φ q s := by
  unfold TagOk; split
  · exact accessOk_noLive hl _ _
  · trivial

/-! ## The context: numbers only, nothing a proof, nothing copied -/

/-- The decisions: nothing a statement or a proof, nothing copied; the join drops `x.0`; a write
invalidates `inv`. -/
def Dw (inv : List Place) : Decisions where
  flags _ _ := (false, false)
  placeDecl _ _ := .other
  declOf _ _ := .other
  copy _ := false
  piSort _ _ := 1
  joinMoves _ _ _ := [.proj 0 (.var 1)]
  rePointed _ _ := []
  typeDecl _ _ := .other
  invalidated _ _ := inv

/-- A run context at any data model, nothing declared, every global the number `0`. -/
def Kw (dm : DataModel) (inv : List Place) : RunCtx where
  dm := dm
  Γ := []
  C := { global := fun _ => (.el0 Nat 0, .plain TyM.nat), sealed := fun _ _ _ _ => .err, clo := fun _ _ _ _ _ => .err,
         pi := fun _ _ _ _ _ => TyM.err, paramTy := fun _ _ _ _ => .plain TyM.err }
  D := Dw inv

/-- **The context obligations hold** (`FundCtx` inhabited). -/
theorem fundCtx_Kw (dm : DataModel) (inv : List Place) : FundCtx (Kw dm inv) :=
  ⟨fun _ => ⟨.inl (nat_mem dm 0), rfl⟩, fun _ h => absurd h List.not_mem_nil⟩

/-- The run's future: every label the number `0`. -/
def φw : Future := fun _ => .el0 Nat 0

/-- One frame, the bindings `bs` (variable `i` is the `i`-th from the end), no borrow. -/
def st (bs : List SBinding) : SState where
  env := [{ binds := bs }]
  shape := fun _ => none
  nextLoan := 0
  heldTy := fun _ => TyM.nat
  heldMem := fun _ => .el0 Nat 0

theorem live_st (bs : List SBinding) : (st bs).liveLabels = [] := by
  unfold SState.liveLabels
  have : ∀ (ps : List Pos), ps.filterMap (fun _ => (none : Option Nat)) = [] := fun ps => by
    induction ps with | nil => rfl | cons _ _ ih => simp [ih]
  simp only [st, this, List.mergeSort_nil]

/-- A number binding, constant. -/
def natB (c : Sem) : SBinding := { ty := .plain TyM.nat, val := fun _ => c }

/-! ## A move out of a field, and its refill -/

/-- `x : Nat`, the number `1`. -/
def sA : SState := st [natB (.el0 Nat 1)]

theorem positions_sA : sA.positions = [.bind 0 0] := by
  simp [sA, st, SState.positions]

theorem live_sA : sA.liveLabels = [] := live_st _

/-- `sA` is good. -/
theorem sA_good (dm : DataModel) : SGood dm [] φw sA := by
  refine ⟨fun ψ hψ f i hp => ?_, fun ψ hψ p l hl => ?_, fun l hl => ?_, fun f i l hl => ?_,
    ⟨fun p ψ ψ' h => ?_, fun r x _ hs ψ ψ' _ => ?_, fun p x hp => ?_⟩, fun p l ⟨ψ, x, hne⟩ => ?_⟩
  · rw [positions_sA] at hp
    simp only [List.mem_cons, Pos.bind.injEq, List.mem_nil_iff, or_false] at hp
    obtain ⟨rfl, rfl⟩ := hp
    exact .inl (.mem (nat_mem dm 1))
  · cases hl
  · rw [live_sA] at hl; cases hl
  · cases hl
  · have : ψ = ψ' := funext fun y => h y (.inl trivial)
    rw [this]
  · cases hs
  · cases hp
  · exfalso; apply hne
    cases p with
    | bind f i => rcases f with _ | f <;> rcases i with _ | i <;> rfl
    | temp f i => rcases f with _ | f <;> rfl

/-- The place `x.0`, the predecessor of `x` (variable `i`). -/
def pred (i : Nat) : Place := .proj 0 (.var i)

/-- After the move out of `x.0`: `x` is `S(⊥)`. -/
noncomputable def sB : SState := sA.setAt (.bind 0 0) fun _ => Sem.moved.succ

theorem updAt_pred_one (dm : DataModel) (Γ : List IndDecl) (T : TyS) :
    Sem.updAt dm Γ T (fun _ => .moved) [.proj 0] (.el0 Nat 1) = some Sem.moved.succ := by
  rw [Sem.updAt.eq_def]
  simp [Sem.asNat_el0]
  exact ⟨_, rfl, rfl⟩

/-- **The move out of `x.0` runs**, and reads `0`. -/
theorem run_move (dm : DataModel) (inv : List Place) (ρ : Assignment) (hint : TyS) :
    runT (Kw dm inv) ρ φw false hint (.place (pred 0)) sA =
      some ((.el0 Nat 0, { (TyS.plain TyM.nat) with label := none }), sB) := by
  rw [runT]
  show SM.guarded (ContentOk (Kw dm inv) φw (pred 0)) (readPlace (Kw dm inv) φw (pred 0) false) sA = _
  rw [SM.guarded_of (contentOk_noLive live_sA _)]
  have hc : contentOf (Kw dm inv) φw (pred 0) sA =
      some ((.el0 Nat 0, { (TyS.plain TyM.nat) with label := none }, .bind 0 0, [.proj 0]), sA) := by
    unfold contentOf
    rw [show resolve sA (pred 0) = some (.bind 0 0, [.proj 0]) from rfl]
    dsimp only
    rw [access_noLive live_sA]
    show (match Sem.follow dm [] (.plain TyM.nat) (.el0 Nat 1) [.proj 0] with
      | some (v, T) => some ((v, if [Step.proj 0].isEmpty then TyS.plain TyM.nat else { T with label := none },
          Pos.bind 0 0, [Step.proj 0]), sA)
      | none => none) = _
    simp [Sem.follow, Sem.step, Sem.asNat_el0]
  unfold readPlace
  rw [hc]
  have hrg : ReadGood dm.read ({ (TyS.plain TyM.nat) with label := none } : TyS).m (.el0 Nat 0) :=
    .inl (nat_mem dm 0)
  have hsc : setContent (Kw dm inv) φw (.bind 0 0) [.proj 0] .moved sA = some (⟨⟩, sB) :=
    setContent_const rfl (updAt_pred_one dm [] _)
  simp only [Kw, Dw] at hsc
  simp [Sem.whole, hrg, Kw, Dw, hsc]

/-- **The fundamental lemma applied to the move out of a field**: the run succeeds from the good
state `sA`, and the state it leaves is good. -/
theorem w_move (dm : DataModel) (inv : List Place) (ρ : Assignment) (hint : TyS) :
    runT (Kw dm inv) ρ φw false hint (.place (pred 0)) sA =
      some ((.el0 Nat 0, { (TyS.plain TyM.nat) with label := none }), sB) ∧ SGood dm [] φw sB :=
  ⟨run_move dm inv ρ hint, (fund_all (fundCtx_Kw dm inv) (.place (pred 0)) trivial false hint sA sB _
    (sA_good dm) (run_move dm inv ρ hint)).2.2.2⟩

theorem live_sB : sB.liveLabels = [] := by unfold sB; rw [liveLabels_setAt, live_sA]

theorem positions_sB : sB.positions = [.bind 0 0] := by unfold sB; rw [SState.positions_setAt, positions_sA]

theorem valAt_sB : sB.valAt (.bind 0 0) = fun _ => Sem.moved.succ :=
  valAt_setAt_self _ _ _ (by rw [positions_sA]; simp)

theorem tyAt_sB : sB.tyAt (.bind 0 0) = .plain TyM.nat := by unfold sB; rw [tyAt_setAt]; rfl

theorem moved_succ : Sem.moved.succ = .dat "Nat" natRec 1 [.moved] := by
  simp [Sem.succ, Sem.asNat, Sem.as, Sem.whole]

/-- After the refill: `x` is `1` again. -/
noncomputable def sA' : SState := sB.setAt (.bind 0 0) fun _ => .el0 Nat 1

theorem contentOf_sB (dm : DataModel) (inv : List Place) :
    contentOf (Kw dm inv) φw (pred 0) sB =
      some ((.moved, { (TyS.plain TyM.nat) with label := none }, .bind 0 0, [.proj 0]), sB) := by
  unfold contentOf
  rw [show resolve sB (pred 0) = some (.bind 0 0, [.proj 0]) from rfl]
  dsimp only
  rw [access_noLive live_sB, valAt_sB, tyAt_sB, moved_succ]
  rfl

theorem placeTy_sB (dm : DataModel) (inv : List Place) : placeTy (Kw dm inv) φw (pred 0) sB = .plain TyM.nat := by
  unfold placeTy; rw [contentOf_sB]; rfl

theorem updAt_refill (dm : DataModel) (Γ : List IndDecl) (T : TyS) :
    Sem.updAt dm Γ T (fun _ => .el0 Nat 0) [.proj 0] Sem.moved.succ = some (.el0 Nat 1) := by
  rw [moved_succ, Sem.updAt.eq_def]
  simp [Sem.asNat, Sem.as, Sem.succAt]
  rw [Sem.updAt.eq_def]
  simp

theorem assignAt_sB (dm : DataModel) (inv : List Place) :
    assignAt (Kw dm inv) φw (pred 0) (.el0 Nat 0) none sB = some ((.el0 Unit (), .plain TyM.unit), sA') := by
  unfold assignAt
  rw [show resolve sB (pred 0) = some (.bind 0 0, [.proj 0]) from rfl]
  dsimp only
  simp only [List.isEmpty_cons, Bool.false_and, Bool.false_eq_true, if_false]
  rw [access_noLive live_sB]
  have hsc : setContent (Kw dm inv) φw (.bind 0 0) [.proj 0] (.el0 Nat 0) sB = some (⟨⟩, sA') :=
    setContent_const valAt_sB (updAt_refill dm [] _)
  rw [hsc]

theorem stateOk_sA' (dm : DataModel) (inv : List Place) : StateOk (Kw dm inv) φw sA' := by
  intro ψ hψ
  have hl : sA'.liveLabels = [] := by unfold sA'; rw [liveLabels_setAt, live_sB]
  have hp : sA'.positions = [.bind 0 0] := by unfold sA'; rw [SState.positions_setAt, positions_sB]
  refine ⟨fun f i hpi => ?_, fun q l hq => ?_⟩
  · rw [hp] at hpi
    simp only [List.mem_cons, Pos.bind.injEq, List.mem_nil_iff, or_false] at hpi
    obtain ⟨rfl, rfl⟩ := hpi
    have hv : sA'.valAt (.bind 0 0) = fun _ => .el0 Nat 1 :=
      valAt_setAt_self _ _ _ (by rw [positions_sB]; simp)
    have ht : sA'.tyAt (.bind 0 0) = .plain TyM.nat := by unfold sA'; rw [tyAt_setAt, tyAt_sB]
    rw [hv, ht]
    exact .inl (.mem (nat_mem dm 1))
  · cases hq

/-- **The refill of `x.0` runs** from the state the move left: `x.0 := 0` makes `x` the number `1`. -/
theorem run_refill (dm : DataModel) (ρ : Assignment) (hint : TyS) :
    runT (Kw dm []) ρ φw false hint (.assign (pred 0) (.const "c")) sB =
      some ((.el0 Unit (), .plain TyM.unit), sA') := by
  have hconst : ∀ T, runT (Kw dm []) ρ φw false T (.const "c") sB = some ((.el0 Nat 0, .plain TyM.nat), sB) := by
    intro T; rw [runT]; rfl
  rw [runT]
  show SM.erasedIf (false, false) _ sB = _
  simp only [SM.erasedIf, SM.stmtIf, Bool.false_eq_true, if_false]
  simp only [hconst, Option.bind_eq_bind, Option.bind_some]
  rw [placeTy_sB]
  rw [if_pos ⟨nat_mem dm 0, fun _ h => by cases h⟩]
  have hao : AssignOk (Kw dm []) φw (pred 0) sB := by
    unfold AssignOk
    rw [show resolve sB (pred 0) = some (.bind 0 0, [.proj 0]) from rfl]
    exact ⟨fun _ => accessOk_noLive live_sB _ _, fun h => by cases h⟩
  rw [show (TyS.plain TyM.nat).label = none from rfl, SM.guarded_of hao, assignAt_sB]
  dsimp only
  have hinv : invalidate (Kw dm []) φw (pred 0) sA' = sA' := rfl
  rw [hinv, if_pos]
  refine ⟨trivial, ?_⟩
  unfold lentOk
  rw [show resolve sA' (pred 0) = some (.bind 0 0, [.proj 0]) from rfl]
  exact .inr (.inr (stateOk_sA' dm []))

/-- **The fundamental lemma applied to the refill**, from the state the move left (good by the lemma
applied to the move). -/
theorem w_refill (dm : DataModel) (ρ : Assignment) (hint : TyS) :
    runT (Kw dm []) ρ φw false hint (.assign (pred 0) (.const "c")) sB = some ((.el0 Unit (), .plain TyM.unit), sA') ∧
      SGood dm [] φw sA' :=
  ⟨run_refill dm ρ hint, (fund_all (fundCtx_Kw dm []) (.assign (pred 0) (.const "c")) trivial false hint sB sA' _
    (w_move dm [] ρ hint).2 (run_refill dm ρ hint)).2.2.2⟩

/-! ## The join's drop of a field -/

/-- `x : Nat` the number `1` (variable `1`), `y : Nat` the number `0` (variable `0`). -/
def sC : SState := st [natB (.el0 Nat 1), natB (.el0 Nat 0)]

theorem positions_sC : sC.positions = [.bind 0 0, .bind 0 1] := by
  simp [sC, st, SState.positions, List.range']

theorem live_sC : sC.liveLabels = [] := live_st _

/-- `sC` is good. -/
theorem sC_good (dm : DataModel) : SGood dm [] φw sC := by
  refine ⟨fun ψ hψ f i hp => ?_, fun ψ hψ p l hl => ?_, fun l hl => ?_, fun f i l hl => ?_,
    ⟨fun p ψ ψ' h => ?_, fun r x _ hs ψ ψ' _ => ?_, fun p x hp => ?_⟩, fun p l ⟨ψ, x, hne⟩ => ?_⟩
  · rw [positions_sC] at hp
    simp only [List.mem_cons, Pos.bind.injEq, List.mem_nil_iff, or_false] at hp
    rcases hp with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact .inl (.mem (nat_mem dm 1))
    · exact .inl (.mem (nat_mem dm 0))
  · cases hl
  · rw [live_sC] at hl; cases hl
  · cases hl
  · have : ψ = ψ' := funext fun y => h y (.inl trivial)
    rw [this]
  · cases hs
  · cases hp
  · exfalso; apply hne
    cases p with
    | bind f i => rcases f with _ | f <;> rcases i with _ | _ | i <;> rfl
    | temp f i => rcases f with _ | f <;> rfl

/-- After the join's drop of `x.0`: `x` is `S(⊥)`. -/
noncomputable def sD : SState := sC.setAt (.bind 0 0) fun _ => Sem.moved.succ

/-- The match on `y` whose second arm moves `x.0`: the first arm runs, and the join drops `x.0`. -/
def tJoin : Term := .matchNat (.var 0) (.const "c") (.place (pred 1))

theorem dropAt_sC (dm : DataModel) (inv : List Place) :
    dropAt (Kw dm inv) φw (pred 1) (.bind 0 0) [.proj 0] sC = sD := by
  unfold dropAt
  dsimp only
  rw [access_noLive live_sC]
  have hv : sC.valAt (.bind 0 0) = fun _ => .el0 Nat 1 := rfl
  rw [if_neg (by simp [Kw, Dw]), if_pos (fun ψ _ => by rw [hv, updAt_pred_one]; rfl)]
  unfold sD
  congr 1
  funext φ'
  rw [hv]
  show (Sem.updAt dm [] _ (fun _ => .moved) [.proj 0] (.el0 Nat 1)).getD .err = _
  rw [updAt_pred_one]; rfl

theorem joinDrop_sC (dm : DataModel) (inv : List Place) (entry : List Place) :
    joinDrop (Kw dm inv) φw entry tJoin sC = sD := by
  unfold joinDrop
  show (match resolve sC (pred 1) with
    | some (pos, steps) => dropAt (Kw dm inv) φw (pred 1) pos steps (accessLentPrefix pos steps sC)
    | none => sC) = sD
  rw [show resolve sC (pred 1) = some (.bind 0 0, [.proj 0]) from rfl]
  dsimp only
  have hlp : accessLentPrefix (.bind 0 0) [.proj 0] sC = sC := by
    unfold accessLentPrefix lentPrefix; rw [live_sC]; rfl
  rw [hlp, dropAt_sC]

/-- **The match runs**: the tag of `y` is `0`, the first arm reads `0`, and the join drops `x.0`. -/
theorem run_join (dm : DataModel) (inv : List Place) (ρ : Assignment) (hint : TyS) :
    runT (Kw dm inv) ρ φw true hint tJoin sC = some ((.el0 Nat 0, .plain TyM.nat), sD) := by
  have hconst : runT (Kw dm inv) ρ φw true hint (.const "c") sC = some ((.el0 Nat 0, .plain TyM.nat), sC) := by
    rw [runT]; rfl
  have htag : tagOf (Kw dm inv) φw (.var 0) natTag sC = some (.el0 Nat 0, sC) := by
    unfold tagOf
    rw [show resolve sC (.var 0) = some (.bind 0 1, []) from rfl]
    dsimp only
    rw [access_noLive live_sC]
    have hv : sC.valAt (.bind 0 1) (sC.typedFuture φw) = .el0 Nat 0 := rfl
    simp [obsAt, Sem.follow, natTag, hv, Sem.asNat_el0]
  unfold tJoin
  rw [runT]
  show SM.erasedIf (false, false) _ sC = _
  simp only [SM.erasedIf, SM.stmtIf, Bool.false_eq_true, if_false]
  rw [SM.guarded_of (tagOk_noLive live_sC _)]
  simp only [htag, Option.bind_eq_bind, Option.bind_some]
  rw [optCheck_of (show MatchEntryOk (Kw dm inv) φw (!true) (.matchNat (.var 0) (.const "c") (.place (pred 1))) sC
    from fun h => by cases h)]
  simp only [Option.bind_some]
  rw [show matchEntry (Kw dm inv) φw (!true) (.matchNat (.var 0) (.const "c") (.place (pred 1))) sC =
    (sC, fun _ s₂ => s₂) from rfl]
  dsimp only
  rw [Sem.asNat_el0]
  dsimp only
  rw [hconst]
  simp only [Option.bind_some]
  have hjd : JoinDropOk (Kw dm inv) φw (movedPlaces φw sC) (.matchNat (.var 0) (.const "c") (.place (pred 1))) sC := by
    unfold JoinDropOk
    show FoldOk _ _ [pred 1] sC
    refine ⟨?_, trivial⟩
    unfold JoinStepOk
    rw [show resolve sC (pred 1) = some (.bind 0 0, [.proj 0]) from rfl]
    have hlp : accessLentPrefix (.bind 0 0) [.proj 0] sC = sC := by
      unfold accessLentPrefix lentPrefix; rw [live_sC]; rfl
    refine ⟨by unfold LentPrefixOk lentPrefix; rw [live_sC]; trivial, ?_⟩
    rw [hlp]
    unfold DropOk
    exact fun _ _ => accessOk_noLive live_sC _ _
  rw [optCheck_of hjd]
  simp only [Option.bind_some]
  rw [show Term.matchNat (.var 0) (.const "c") (.place (pred 1)) = tJoin from rfl, joinDrop_sC]

/-- **The fundamental lemma applied to the join's drop of a field.** -/
theorem w_joinDrop (dm : DataModel) (inv : List Place) (ρ : Assignment) (hint : TyS) :
    runT (Kw dm inv) ρ φw true hint tJoin sC = some ((.el0 Nat 0, .plain TyM.nat), sD) ∧ SGood dm [] φw sD :=
  ⟨run_join dm inv ρ hint, (fund_all (fundCtx_Kw dm inv) tJoin ⟨trivial, trivial⟩ true hint sC sD _
    (sC_good dm) (run_join dm inv ρ hint)).2.2.2⟩

/-! ## A borrow of an index field whose dependent sibling D112 invalidates -/

section Borrow
open Ochr.Meaning.ReadProto (dE rE gV cE_mem)

/-- Field `n` of `C(n : Nat, v : X(n))` (`ReadProto.dE`), the index of field `v`. -/
def gN : FieldRef := { ty := "E", ctor := 0, idx := 0, name := "n" }

/-- `x : E`, the value `C(3, 7)`. -/
def bE (dm : DataModel) : SBinding := { ty := .plain (dm.tyR dE rE), val := fun _ => .dat "E" rE 0 [.el0 Nat 3, .el0 Nat 7] }

def sE (dm : DataModel) : SState := st [bE dm]

theorem live_sE (dm : DataModel) : (sE dm).liveLabels = [] := live_st _

/-- `&x.n` invalidates `x.v` (D112: the borrowed index's dependent sibling). -/
def KE (dm : DataModel) : RunCtx := Kw dm [.field gV (.var 0)]

/-- The lender after the borrow: `C(l, 7)`, its index the fresh label `0`'s final content. -/
def lendE : SVal := fun φ' => .dat "E" rE 0 [φ' 0, .el0 Nat 7]

/-- The state after `&x.n`: `x` reads `C(l, 7)`, a temporary holds the borrow `l = 0` of the content
`3`, recorded at `Nat`. -/
noncomputable def sE1 (dm : DataModel) : SState :=
  (((((sE dm).freshLoan.2.setAt (.bind 0 0) lendE).pushTempShaped (fun _ => .el0 Nat 3) 0).setLent 0
    [⟨.bind 0 0, [.field gN], false⟩]).setHeldTy 0 TyM.nat).setHeldMem 0 (.el0 Nat 3)

theorem updAt_lend (dm : DataModel) (Γ : List IndDecl) (T : TyS) (x : Sem) :
    Sem.updAt dm Γ T (fun _ => x) [.field gN] (.dat "E" rE 0 [.el0 Nat 3, .el0 Nat 7]) =
      some (.dat "E" rE 0 [x, .el0 Nat 7]) := by
  rw [Sem.updAt_dat' dm Γ T _ (.field gN) [] (fi := .el0 Nat 3) (by simp) (by decide) rfl, Sem.updAt_nil']
  rfl

theorem env_sE1 (dm : DataModel) : (sE1 dm).env =
    [{ binds := [{ bE dm with val := lendE }], temps := [fun _ => .el0 Nat 3] }] := rfl

theorem positions_sE1 (dm : DataModel) : (sE1 dm).positions = [.bind 0 0, .temp 0 0] := by
  simp [SState.positions, env_sE1]

theorem shape_sE1 (dm : DataModel) : (sE1 dm).shape = fun p => if p = .temp 0 0 then some 0 else none := rfl

theorem live_sE1 (dm : DataModel) : (sE1 dm).liveLabels = [0] := by
  unfold SState.liveLabels; rw [positions_sE1, shape_sE1]; simp

/-- Field `n` is read at `Nat`, whatever it holds (a `Nat` leaf). -/
theorem readTy_n (dm : DataModel) (Γ : List IndDecl) (f : Sem) : dm.readTy Γ dE rE 0 0 [] f = some TyM.nat := by
  have hown : ¬ dm.OwnCarrier Code0.nat := by
    rintro ⟨d, r, h, -⟩; cases h
  have hsh : dm.sig.shape dE rE 0 0 [] = .leaf Nat .nat := rfl
  unfold DataModel.readTy
  simp only [List.map_nil, hsh, DataModel.shapeReadTy, if_neg hown]
  rfl

theorem contentOf_sE (dm : DataModel) :
    contentOf (KE dm) φw (.field gN (.var 0)) (sE dm) =
      some ((.el0 Nat 3, { (TyS.plain TyM.nat) with label := none }, .bind 0 0, [.field gN]), sE dm) := by
  unfold contentOf
  rw [show resolve (sE dm) (.field gN (.var 0)) = some (.bind 0 0, [.field gN]) from rfl]
  dsimp only
  rw [access_noLive (live_sE dm)]
  have hdc : (TyS.plain (dm.tyR dE rE)).m.dataCode? = some (dE, rE) := rfl
  have hv : (sE dm).valAt (.bind 0 0) ((sE dm).typedFuture φw) = .dat "E" rE 0 [.el0 Nat 3, .el0 Nat 7] := rfl
  have ht : (sE dm).tyAt (.bind 0 0) = .plain (dm.tyR dE rE) := rfl
  rw [hv, ht]
  simp only [KE, Kw, Sem.follow, Sem.step, Sem.stepField, gN, hdc, Option.bind]
  simp [show dE.name = "E" from rfl, readTy_n]

theorem borrowPlace_sE (dm : DataModel) :
    borrowPlace (KE dm) φw (.field gN (.var 0)) (sE dm) =
      some ((.el0 Nat 3, { (TyS.plain TyM.nat) with label := some 0 }), sE1 dm) := by
  unfold borrowPlace
  rw [contentOf_sE]
  simp only [Bind.bind, Option.bind_some]
  rw [if_neg (by simp [Sem.whole])]
  unfold sE1
  have hG : (fun φ' => (Sem.updAt (KE dm).dm (KE dm).Γ ((sE dm).freshLoan.2.tyAt (.bind 0 0)) (fun _ => φ' (sE dm).freshLoan.1)
      [.field gN] ((sE dm).freshLoan.2.valAt (.bind 0 0) φ')).getD .err) = lendE := by
    funext φ'
    show (Sem.updAt dm [] _ (fun _ => φ' 0) [.field gN] (.dat "E" rE 0 [.el0 Nat 3, .el0 Nat 7])).getD .err = _
    rw [updAt_lend]; rfl
  simp only [hG]
  rfl

/-- The state after the invalidation of `x.v`: `x` reads `C(l, ⊥)`. -/
def dropE : SVal := fun φ' => .dat "E" rE 0 [φ' 0, .moved]

noncomputable def sE2 (dm : DataModel) : SState := (sE1 dm).setAt (.bind 0 0) dropE

theorem updAt_dropV (dm : DataModel) (Γ : List IndDecl) (T : TyS) (x : Sem) :
    Sem.updAt dm Γ T (fun _ => .moved) [.field gV] (.dat "E" rE 0 [x, .el0 Nat 7]) = some (.dat "E" rE 0 [x, .moved]) := by
  rw [Sem.updAt_dat' dm Γ T _ (.field gV) [] (fi := .el0 Nat 7) (by simp) (by decide) rfl, Sem.updAt_nil']
  rfl

theorem invalidate_sE1 (dm : DataModel) : invalidate (KE dm) φw (.field gN (.var 0)) (sE1 dm) = sE2 dm := by
  show invalidateOne (KE dm) φw (sE1 dm) (.field gV (.var 0)) = sE2 dm
  unfold invalidateOne
  rw [show resolve (sE1 dm) (.field gV (.var 0)) = some (.bind 0 0, [.field gV]) from rfl]
  dsimp only
  have hdh : dataHit [.field gV] [.field gN] = false := by decide
  have hlent : (sE1 dm).lent = fun m => if m = 0 then [⟨.bind 0 0, [.field gN], false⟩] else [] := by
    funext m; by_cases hm : m = 0
    · subst hm; rfl
    · rw [if_neg hm]; show (if m = 0 then _ else _) = _; rw [if_neg hm]; rfl
  rw [access_unreached (fun l => by
    unfold SState.reached
    rw [hlent]
    by_cases hl : l = 0
    · subst hl; simp [hdh]
    · simp [hl])]
  have hv : (sE1 dm).valAt (.bind 0 0) = lendE := rfl
  have hsc : setContent (KE dm) φw (.bind 0 0) [.field gV] .moved (sE1 dm) = some (⟨⟩, sE2 dm) := by
    unfold setContent
    rw [if_pos (fun ψ _ => by rw [hv]; simp only [lendE, updAt_dropV]; rfl)]
    unfold sE2
    congr 3
  rw [hsc]

/-- The invalidation's access of `x.v` reaches no label (the borrow is lent at `x.n`): no end. -/
theorem invalidateOk_sE1 (dm : DataModel) : InvalidateOk (KE dm) φw (.field gN (.var 0)) (sE1 dm) := by
  show FoldOk _ _ [Place.field gV (.var 0)] (sE1 dm)
  refine ⟨?_, trivial⟩
  unfold InvalOneOk
  rw [show resolve (sE1 dm) (.field gV (.var 0)) = some (.bind 0 0, [.field gV]) from rfl]
  have hdh : dataHit [.field gV] [.field gN] = false := by decide
  have hlent : (sE1 dm).lent = fun m => if m = 0 then [⟨.bind 0 0, [.field gN], false⟩] else [] := by
    funext m; by_cases hm : m = 0
    · subst hm; rfl
    · rw [if_neg hm]; show (if m = 0 then _ else _) = _; rw [if_neg hm]; rfl
  show AccessOk (KE dm) φw (sE1 dm) (.bind 0 0) (dataHit [.field gV])
  exact accessOkF_unreached (Γ := (KE dm).Γ) (fun l => by
    unfold SState.reached
    rw [hlent]
    by_cases hl : l = 0
    · subst hl; simp [hdh]
    · simp [hl])

/-- **The strict test passes after the invalidation**: at every typed future (label `0` any open
member of `Nat`), `x` is `C(l, ⊥)`, an open member of `E` (its index read at `Nat`, its dependent
field moved), and the temporary holds `3`. -/
theorem stateOk_sE2 (dm : DataModel) : StateOk (KE dm) φw (sE2 dm) := by
  intro ψ hψ
  have hp : (sE2 dm).positions = [.bind 0 0, .temp 0 0] := by unfold sE2; rw [SState.positions_setAt, positions_sE1]
  have hl : (sE2 dm).liveLabels = [0] := by unfold sE2; rw [liveLabels_setAt, live_sE1]
  have hψ0 : dm.OMem [] TyM.nat (ψ 0) := by
    have := hψ.2 0 (by rw [hl]; simp)
    exact .mem this
  refine ⟨fun f i hpi => ?_, fun q l hq => ?_⟩
  · rw [hp] at hpi
    simp only [List.mem_cons, Pos.bind.injEq, List.mem_nil_iff, or_false, reduceCtorEq] at hpi
    obtain ⟨rfl, rfl⟩ := hpi
    have hv : (sE2 dm).valAt (.bind 0 0) = dropE := valAt_setAt_self _ _ _ (by rw [positions_sE1]; simp)
    have ht : (sE2 dm).tyAt (.bind 0 0) = .plain (dm.tyR dE rE) := by unfold sE2; rw [tyAt_setAt]; rfl
    rw [hv, ht]
    left
    show dm.OMem [] (dm.tyR dE rE) (.dat dE.name rE 0 [ψ 0, .moved])
    exact .dat rfl (by decide) rfl (.cons (.at [] TyM.nat .nil (readTy_n dm [] (ψ 0)) hψ0) (.cons .moved .nil))
  · have hsh : (sE2 dm).shape = (sE1 dm).shape := by unfold sE2; rw [SState.shape_setAt]
    rw [hsh, shape_sE1] at hq
    dsimp only at hq
    by_cases hq0 : q = .temp 0 0
    · subst hq0
      simp only [if_true, Option.some.injEq] at hq
      subst hq
      have hv : (sE2 dm).valAt (.temp 0 0) = fun _ => .el0 Nat 3 := by
        unfold sE2; rw [SState.valAt_setAt_ne _ _ _ _ (by simp)]; rfl
      rw [hv]
      exact .mem (nat_mem dm 3)
    · rw [if_neg hq0] at hq; cases hq

/-- `sE` is good: `C(3, 7)` is a member of `E` (`ReadProto.cE_mem`). -/
theorem sE_good (dm : DataModel) : SGood dm [] φw (sE dm) := by
  have hpos : (sE dm).positions = [.bind 0 0] := by simp [sE, st, SState.positions]
  refine ⟨fun ψ hψ f i hp => ?_, fun ψ hψ p l hl => ?_, fun l hl => ?_, fun f i l hl => ?_,
    ⟨fun p ψ ψ' h => ?_, fun r x _ hs ψ ψ' _ => ?_, fun p x hp => ?_⟩, fun p l ⟨ψ, x, hne⟩ => ?_⟩
  · rw [hpos] at hp
    simp only [List.mem_cons, Pos.bind.injEq, List.mem_nil_iff, or_false] at hp
    obtain ⟨rfl, rfl⟩ := hp
    exact .inl (.mem (cE_mem dm))
  · cases hl
  · rw [live_sE] at hl; cases hl
  · cases hl
  · have : ψ = ψ' := funext fun y => h y (.inl trivial)
    rw [this]
  · cases hs
  · cases hp
  · exfalso; apply hne
    cases p with
    | bind f i => rcases f with _ | f <;> rcases i with _ | i <;> rfl
    | temp f i => rcases f with _ | f <;> rfl

/-- **The borrow of the index `x.n` runs**: the content `3` is lent, D112 invalidates `x.v`, and the
strict test passes. -/
theorem run_borrow (dm : DataModel) (ρ : Assignment) (tl : Bool) (hint : TyS) :
    runT (KE dm) ρ φw tl hint (.borrow (.field gN (.var 0))) (sE dm) =
      some ((.el0 Nat 3, { (TyS.plain TyM.nat) with label := some 0 }), sE2 dm) := by
  rw [runT]
  show SM.erasedIf (false, false) _ (sE dm) = _
  simp only [SM.erasedIf, SM.stmtIf, Bool.false_eq_true, if_false]
  unfold SM.strictS
  rw [SM.guarded_of (contentOk_noLive (live_sE dm) _), borrowPlace_sE]
  dsimp only
  rw [if_pos (show Sem.el0 Nat 3 ∈ₛ[(KE dm).dm.read] (TyS.plain TyM.nat).m from nat_mem dm 3)]
  dsimp only
  rw [invalidate_sE1, if_pos]
  refine ⟨invalidateOk_sE1 dm, ?_⟩
  unfold lentOk
  rw [show resolve (sE2 dm) (.field gN (.var 0)) = some (.bind 0 0, [.field gN]) from rfl]
  exact .inr (.inr (stateOk_sE2 dm))

/-- **The fundamental lemma applied to a borrow of an index with a dependent sibling.** -/
theorem w_borrowIndex (dm : DataModel) (ρ : Assignment) (tl : Bool) (hint : TyS) :
    runT (KE dm) ρ φw tl hint (.borrow (.field gN (.var 0))) (sE dm) =
      some ((.el0 Nat 3, { (TyS.plain TyM.nat) with label := some 0 }), sE2 dm) ∧ SGood dm [] φw (sE2 dm) :=
  ⟨run_borrow dm ρ tl hint, (fund_all (fundCtx_Kw dm _) (.borrow (.field gN (.var 0))) trivial tl hint (sE dm) (sE2 dm) _
    (sE_good dm) (run_borrow dm ρ tl hint)).2.2.2⟩

end Borrow

/-! ## Ends (ruling (A)): a borrow ended over moved-out content fails, one ended after a refill runs

`y` holds the borrow `0` of `x` (`x` reads `0`'s final content); `(*y).0` is moved out through the
borrow, then `x` is read, which ends the borrow (its [Access] reaches the site at `x`). Without a
refill the holder's content is `S(⊥)`, no member of `Nat`, and the strict end fails the run
(`run_endBad`), as the checker rejects ending a borrow over moved-out content (main's D98). With the
refill `(*y).0 := c` first, the content is `1` and the run succeeds (`run_endOk`); the lemma applies
(`w_endOk`). -/

section Ends

/-- `x : Nat`, the lender of label `0`. -/
def bxL : SBinding := { ty := .plain TyM.nat, val := fun ψ => ψ 0 }

/-- `y : Nat`, the holder of label `0`, holding `1`. -/
def byH (c : Sem) : SBinding := { ty := .plain TyM.nat, val := fun _ => c }

/-- `x` (variable `1`) lends label `0` at its root to `y` (variable `0`), which holds `c`. -/
def sF (c : Sem) : SState where
  env := [{ binds := [bxL, byH c] }]
  shape := fun p => if p = .bind 0 1 then some 0 else none
  nextLoan := 1
  lent := fun l => if l = 0 then [⟨.bind 0 0, [], false⟩] else []
  heldTy := fun _ => TyM.nat
  heldMem := fun _ => .el0 Nat 1

theorem positions_sF (c : Sem) : (sF c).positions = [.bind 0 0, .bind 0 1] := by
  simp [sF, SState.positions, List.range']

theorem live_sF (c : Sem) : (sF c).liveLabels = [0] := by
  unfold SState.liveLabels; rw [positions_sF]; simp [sF]

theorem shape_sF_some {c : Sem} {p : Pos} {l : Nat} (h : (sF c).shape p = some l) : p = .bind 0 1 ∧ l = 0 := by
  simp only [sF] at h
  split at h
  · rename_i hp; cases h; exact ⟨hp, rfl⟩
  · cases h

theorem valAt_sF_indep (c : Sem) (p : Pos) (ψ : Future) {l : Nat} (hl : l ≠ 0) (x : Sem) :
    (sF c).valAt p (ψ.upd l x) = (sF c).valAt p ψ := by
  cases p with
  | bind f i =>
    rcases f with _ | f
    · rcases i with _ | _ | i
      · show (ψ.upd l x) 0 = ψ 0
        rw [Future.upd_other _ _ (Ne.symm hl)]
      · rfl
      · rfl
    · rfl
  | temp f i =>
    rcases f with _ | f
    · rfl
    · rfl

/-- `sF c` is good when `c` is a member of `Nat`. -/
theorem sF_good (dm : DataModel) {c : Sem} (hc : c ∈ₛ[dm.read] TyM.nat) : SGood dm [] φw (sF c) := by
  refine ⟨fun ψ hψ f i hp => ?_, fun ψ hψ p l hl => ?_, fun l hl => ?_, fun f i l hl => ?_,
    ⟨fun p ψ ψ' h => ?_, fun r x _ hs ψ ψ' _ => ?_, fun p x hp => ?_⟩, fun p l ⟨ψ, x, hne⟩ => ?_⟩
  · rw [positions_sF] at hp
    simp only [List.mem_cons, Pos.bind.injEq, List.mem_nil_iff, or_false] at hp
    rcases hp with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact .inl (.mem (hψ.2 0 (by rw [live_sF]; simp)))
    · exact .inl (.mem hc)
  · obtain ⟨rfl, rfl⟩ := shape_sF_some hl
    exact .mem hc
  · rw [live_sF] at hl; simp only [List.mem_cons, List.mem_nil_iff, or_false] at hl; subst hl
    exact nat_mem dm 1
  · obtain ⟨he, rfl⟩ := shape_sF_some hl
    cases he; rfl
  · have : ψ = ψ' := funext fun y => h y (.inl trivial)
    rw [this]
  · obtain ⟨rfl, rfl⟩ := shape_sF_some hs
    rfl
  · obtain ⟨rfl, rfl⟩ := shape_sF_some hp
    exact ⟨by rw [positions_sF]; simp, by show 0 < 1; omega⟩
  · show l < 1
    by_cases hl : l = 0
    · omega
    · exact absurd (valAt_sF_indep c p ψ hl x).symm hne

/-- The place `(*y).0`, the predecessor of `y`'s content (`y` is variable `0`). -/
def qY : Place := .proj 0 (.deref (.var 0))

theorem resolve_qY (c : Sem) : resolve (sF c) qY = some (.bind 0 1, [.deref, .proj 0]) := rfl

/-- Nothing is lent at `y`: an access of `y` ends nothing. -/
theorem reached_sF_y (c : Sem) (hit : List Step → Bool) (l : Nat) : (sF c).reached (.bind 0 1) hit l = false := by
  unfold SState.reached
  by_cases hl : l = 0
  · subst hl; simp [sF]
  · simp [sF, hl]

theorem contentOk_sF_qY (dm : DataModel) (c : Sem) : ContentOk (Kw dm []) φw qY (sF c) := by
  unfold ContentOk; rw [resolve_qY]
  exact accessOkF_unreached (Γ := (Kw dm []).Γ) (reached_sF_y c _)

theorem updAt_qY_one (dm : DataModel) (Γ : List IndDecl) (T : TyS) :
    Sem.updAt dm Γ T (fun _ => .moved) [.deref, .proj 0] (.el0 Nat 1) = some Sem.moved.succ := by
  rw [Sem.updAt_deref']; exact updAt_pred_one dm Γ _

theorem sF_set (c c' : Sem) : (sF c).setAt (.bind 0 1) (fun _ => c') = sF c' := rfl

/-- **The move of `(*y).0` runs** from `y = 1`: it reads `0` and leaves `y = S(⊥)`, the borrow live. -/
theorem run_moveY (dm : DataModel) (ρ : Assignment) (hint : TyS) :
    runT (Kw dm []) ρ φw false hint (.place qY) (sF (.el0 Nat 1)) =
      some ((.el0 Nat 0, { (TyS.plain TyM.nat) with label := none }), sF Sem.moved.succ) := by
  rw [runT]
  show SM.guarded (ContentOk (Kw dm []) φw qY) (readPlace (Kw dm []) φw qY false) (sF (.el0 Nat 1)) = _
  rw [SM.guarded_of (contentOk_sF_qY dm _)]
  have hc : contentOf (Kw dm []) φw qY (sF (.el0 Nat 1)) =
      some ((.el0 Nat 0, { (TyS.plain TyM.nat) with label := none }, .bind 0 1, [.deref, .proj 0]), sF (.el0 Nat 1)) := by
    unfold contentOf
    rw [resolve_qY]
    dsimp only
    rw [access_unreached (reached_sF_y _ _)]
    show (match Sem.follow dm [] (.plain TyM.nat) (.el0 Nat 1) [.deref, .proj 0] with
      | some (v, T) => some ((v, if [Step.deref, Step.proj 0].isEmpty then TyS.plain TyM.nat else { T with label := none },
          Pos.bind 0 1, [Step.deref, Step.proj 0]), sF (.el0 Nat 1))
      | none => none) = _
    simp [Sem.follow, Sem.step, Sem.asNat_el0]
  unfold readPlace
  rw [hc]
  have hrg : ReadGood dm.read ({ (TyS.plain TyM.nat) with label := none } : TyS).m (.el0 Nat 0) :=
    .inl (nat_mem dm 0)
  have hsc : setContent (Kw dm []) φw (.bind 0 1) [.deref, .proj 0] .moved (sF (.el0 Nat 1)) =
      some (⟨⟩, sF Sem.moved.succ) := by
    rw [← sF_set (.el0 Nat 1) Sem.moved.succ]
    exact setContent_const rfl (updAt_qY_one dm [] _)
  simp only [Kw, Dw] at hsc
  simp [Sem.whole, hrg, Kw, Dw, hsc]

theorem holderOf_sF (c : Sem) : (sF c).holderOf 0 = some (.bind 0 1) := by
  unfold SState.holderOf; rw [positions_sF]; simp [sF]

/-- The access of `x` reaches the borrow `0` (lent at `x`'s root): one round ends it. -/
theorem accessRound_sF_x (c : Sem) :
    ((sF c).liveLabels.filter ((sF c).reached (.bind 0 0) (dataHit []))) = [0] := by
  rw [live_sF]; simp [SState.reached, sF, dataHit]

/-- **The strict end fails over moved-out content**: reading `x` would end the borrow while its holder
holds a value that is no member of `Nat`, at the typed future `φw`. -/
theorem not_contentOk_x (dm : DataModel) {c : Sem} (hc : ¬ c ∈ₛ[dm.read] TyM.nat) :
    ¬ ContentOk (Kw dm []) φw (.var 1) (sF c) := by
  unfold ContentOk
  rw [show resolve (sF c) (.var 1) = some (.bind 0 0, []) from rfl]
  intro h
  have h0 := h 0 (by rw [live_sF]; simp)
  simp only [List.range_zero, List.foldl_nil] at h0
  rw [accessRound_sF_x] at h0
  have hend : EndOk (Kw dm []) φw (sF c) 0 := h0.1
  have := hend (.bind 0 1) (holderOf_sF c) φw (typedFut_self_live (fun l hl => by
    rw [live_sF] at hl; simp only [List.mem_cons, List.mem_nil_iff, or_false] at hl; subst hl; exact nat_mem dm 0))
  exact hc this

/-- **Without the refill the run fails**: `(*y).0` moved out, then reading `x` ends the borrow over the
moved-out content (the strict end, ruling (A); the checker rejects this program by main's D98). -/
theorem run_endBad (dm : DataModel) (ρ : Assignment) (tl : Bool) (hint : TyS) :
    runT (Kw dm []) ρ φw tl hint (.seq (.place qY) (.place (.var 1))) (sF (.el0 Nat 1)) = none := by
  have hbad : ¬ ContentOk (Kw dm []) φw (.var 1) (sF Sem.moved.succ) :=
    not_contentOk_x dm (by rw [moved_succ]; rintro ⟨n, hn⟩; cases hn)
  rw [runT]
  show SM.erasedIf (false, false) _ (sF (.el0 Nat 1)) = _
  simp only [SM.erasedIf, SM.stmtIf, Bool.false_eq_true, if_false]
  show (runT (Kw dm []) ρ φw false (.plain TyM.err) (.place qY) >>= fun r =>
    SM.guardMod (DiscardOk (Kw dm []) φw r.2) (discardEnd r.2) >>= fun _ =>
      runT (Kw dm []) ρ φw tl hint (.place (.var 1))) (sF (.el0 Nat 1)) = none
  simp only [Bind.bind, run_moveY]
  rw [SM.guardMod_of (show DiscardOk (Kw dm []) φw { (TyS.plain TyM.nat) with label := none } (sF Sem.moved.succ) from trivial)]
  dsimp only
  rw [runT]
  show SM.guarded (ContentOk (Kw dm []) φw (.var 1)) (readPlace (Kw dm []) φw (.var 1) false) (discardEnd _ (sF Sem.moved.succ)) = none
  have hd : discardEnd { (TyS.plain TyM.nat) with label := none } (sF Sem.moved.succ) = sF Sem.moved.succ := rfl
  rw [hd]
  unfold SM.guarded
  rw [if_neg hbad]

theorem contentOf_sF_qY_moved (dm : DataModel) :
    contentOf (Kw dm []) φw qY (sF Sem.moved.succ) =
      some ((.moved, { (TyS.plain TyM.nat) with label := none }, .bind 0 1, [.deref, .proj 0]), sF Sem.moved.succ) := by
  unfold contentOf
  rw [resolve_qY]
  dsimp only
  rw [access_unreached (reached_sF_y _ _)]
  show (match Sem.follow dm [] (.plain TyM.nat) Sem.moved.succ [.deref, .proj 0] with
    | some (v, T) => some ((v, if [Step.deref, Step.proj 0].isEmpty then TyS.plain TyM.nat else { T with label := none },
        Pos.bind 0 1, [Step.deref, Step.proj 0]), sF Sem.moved.succ)
    | none => none) = _
  rw [moved_succ]
  rfl

theorem updAt_qY_refill (dm : DataModel) (Γ : List IndDecl) (T : TyS) :
    Sem.updAt dm Γ T (fun _ => .el0 Nat 0) [.deref, .proj 0] Sem.moved.succ = some (.el0 Nat 1) := by
  rw [Sem.updAt_deref']; exact updAt_refill dm Γ _

/-- **The refill `(*y).0 := c` runs** while the borrow is live: `y` is `1` again; the strict test
below a root (`StateOk`) passes at every typed future. -/
theorem run_assignY (dm : DataModel) (ρ : Assignment) (hint : TyS) :
    runT (Kw dm []) ρ φw false hint (.assign qY (.const "c")) (sF Sem.moved.succ) =
      some ((.el0 Unit (), .plain TyM.unit), sF (.el0 Nat 1)) := by
  have hconst : ∀ T, runT (Kw dm []) ρ φw false T (.const "c") (sF Sem.moved.succ) =
      some ((.el0 Nat 0, .plain TyM.nat), sF Sem.moved.succ) := by
    intro T; rw [runT]; rfl
  have hpt : placeTy (Kw dm []) φw qY (sF Sem.moved.succ) = .plain TyM.nat := by
    unfold placeTy; rw [contentOf_sF_qY_moved]; rfl
  have hao : AssignOk (Kw dm []) φw qY (sF Sem.moved.succ) := by
    unfold AssignOk; rw [resolve_qY]
    exact ⟨fun _ => accessOkF_unreached (Γ := (Kw dm []).Γ) (reached_sF_y _ _), fun h => by cases h⟩
  have hassign : assignAt (Kw dm []) φw qY (.el0 Nat 0) none (sF Sem.moved.succ) =
      some ((.el0 Unit (), .plain TyM.unit), sF (.el0 Nat 1)) := by
    unfold assignAt
    rw [resolve_qY]
    dsimp only
    simp only [List.isEmpty_cons, Bool.false_and, Bool.false_eq_true, if_false]
    rw [access_unreached (reached_sF_y _ _)]
    have hsc : setContent (Kw dm []) φw (.bind 0 1) [.deref, .proj 0] (.el0 Nat 0) (sF Sem.moved.succ) =
        some (⟨⟩, sF (.el0 Nat 1)) := by
      rw [← sF_set Sem.moved.succ (.el0 Nat 1)]
      exact setContent_const rfl (updAt_qY_refill dm [] _)
    rw [hsc]
  rw [runT]
  show SM.erasedIf (false, false) _ (sF Sem.moved.succ) = _
  simp only [SM.erasedIf, SM.stmtIf, Bool.false_eq_true, if_false]
  simp only [hconst, Option.bind_eq_bind, Option.bind_some]
  rw [hpt, if_pos ⟨nat_mem dm 0, fun _ h => by cases h⟩,
    show (TyS.plain TyM.nat).label = none from rfl, SM.guarded_of hao, hassign]
  dsimp only
  have hinv : invalidate (Kw dm []) φw qY (sF (.el0 Nat 1)) = sF (.el0 Nat 1) := rfl
  rw [hinv, if_pos]
  refine ⟨trivial, ?_⟩
  unfold lentOk
  rw [resolve_qY]
  have hs := sF_good dm (nat_mem dm 1)
  exact .inr (.inr fun ψ hψ => ⟨fun f i hp => hs.bind ψ hψ f i hp, fun q l hq => hs.holder ψ hψ q l hq⟩)

/-- Reading `x` accesses it: one round, which ends the borrow `0` at its holder `y`. -/
theorem access_sF_x (c : Sem) : (sF c).access (.bind 0 0) (dataHit []) = (sF c).endAt 0 (.bind 0 1) := by
  show (List.range (sF c).liveLabels.length).foldl
    (fun s _ => (s.liveLabels.filter (s.reached (.bind 0 0) (dataHit []))).foldl SState.endLabel s) (sF c) = _
  rw [show (sF c).liveLabels.length = 1 by rw [live_sF]; rfl]
  simp only [List.range_one, List.foldl_cons, List.foldl_nil]
  rw [accessRound_sF_x]
  simp only [List.foldl_cons, List.foldl_nil]
  exact SState.endLabel_eq (holderOf_sF c)

/-- **The strict end holds after the refill**: the holder's content is `1`, a member of `Nat`. -/
theorem contentOk_x_one (dm : DataModel) : ContentOk (Kw dm []) φw (.var 1) (sF (.el0 Nat 1)) := by
  unfold ContentOk
  rw [show resolve (sF (.el0 Nat 1)) (.var 1) = some (.bind 0 0, []) from rfl]
  intro k hk
  rw [live_sF] at hk
  obtain rfl : k = 0 := by simpa using hk
  simp only [List.range_zero, List.foldl_nil]
  rw [accessRound_sF_x]
  refine ⟨fun r hr ψ _ => ?_, trivial⟩
  rw [holderOf_sF] at hr; cases hr
  exact nat_mem dm 1

theorem valAt_x_after_end (ψ : Future) :
    ((sF (.el0 Nat 1)).endAt 0 (.bind 0 1)).valAt (.bind 0 0) ψ = .el0 Nat 1 := by
  rw [SState.endAt_valAt _ _ _ _ (by rw [positions_sF]; simp)]
  show (if Pos.bind 0 0 = Pos.bind 0 1 then Sem.moved else (ψ.upd 0 (Sem.el0 Nat 1)) 0) = _
  rw [if_neg (by decide), Future.upd_same]

/-- The end's state, then `x` moved out. -/
noncomputable def sX : SState := ((sF (.el0 Nat 1)).endAt 0 (.bind 0 1)).setAt (.bind 0 0) fun _ => .moved

/-- **Reading `x` runs after the refill**: the borrow ends (its content `1`, a member) and `x` reads `1`. -/
theorem run_readX (dm : DataModel) (ρ : Assignment) (tl : Bool) (hint : TyS) :
    runT (Kw dm []) ρ φw tl hint (.place (.var 1)) (sF (.el0 Nat 1)) =
      some ((.el0 Nat 1, { (TyS.plain TyM.nat) with label := none }), sX) := by
  rw [runT]
  show SM.guarded (ContentOk (Kw dm []) φw (.var 1)) (readPlace (Kw dm []) φw (.var 1) false) (sF (.el0 Nat 1)) = _
  rw [SM.guarded_of (contentOk_x_one dm)]
  have hc : contentOf (Kw dm []) φw (.var 1) (sF (.el0 Nat 1)) =
      some ((.el0 Nat 1, TyS.plain TyM.nat, .bind 0 0, []), (sF (.el0 Nat 1)).endAt 0 (.bind 0 1)) := by
    unfold contentOf
    rw [show resolve (sF (.el0 Nat 1)) (.var 1) = some (.bind 0 0, []) from rfl]
    dsimp only
    rw [access_sF_x, valAt_x_after_end]
    rfl
  unfold readPlace
  rw [hc]
  have hrg : ReadGood dm.read (TyS.plain TyM.nat).m (.el0 Nat 1) := .inl (nat_mem dm 1)
  have hsh : ((sF (.el0 Nat 1)).endAt 0 (.bind 0 1)).shape (.bind 0 0) = none := by
    rw [SState.endAt_shape]; simp [sF]
  have hsc : setContent (Kw dm []) φw (.bind 0 0) [] .moved ((sF (.el0 Nat 1)).endAt 0 (.bind 0 1)) =
      some (⟨⟩, sX) := setContent_root _ _ _ _ _ (.inl rfl)
  simp only [Kw, Dw] at hsc
  simp [Sem.whole, hrg, Kw, Dw, hsh, hsc]

/-- The program with the refill: `(*y).0; ((*y).0 := c; x)`. -/
def tEndOk : Term := .seq (.place qY) (.seq (.assign qY (.const "c")) (.place (.var 1)))

/-- **With the refill the run succeeds**: the move through the borrow, the refill, then the read of
`x`, whose access ends the borrow over the whole content `1`. -/
theorem run_endOk (dm : DataModel) (ρ : Assignment) (tl : Bool) (hint : TyS) :
    runT (Kw dm []) ρ φw tl hint tEndOk (sF (.el0 Nat 1)) =
      some ((.el0 Nat 1, { (TyS.plain TyM.nat) with label := none }), sX) := by
  unfold tEndOk
  rw [runT]
  show SM.erasedIf (false, false) _ (sF (.el0 Nat 1)) = _
  simp only [SM.erasedIf, SM.stmtIf, Bool.false_eq_true, if_false]
  show (runT (Kw dm []) ρ φw false (.plain TyM.err) (.place qY) >>= fun r =>
    SM.guardMod (DiscardOk (Kw dm []) φw r.2) (discardEnd r.2) >>= fun _ =>
      runT (Kw dm []) ρ φw tl hint (.seq (.assign qY (.const "c")) (.place (.var 1)))) (sF (.el0 Nat 1)) = _
  simp only [Bind.bind, run_moveY]
  rw [SM.guardMod_of (show DiscardOk (Kw dm []) φw { (TyS.plain TyM.nat) with label := none } (sF Sem.moved.succ) from trivial)]
  dsimp only
  rw [show discardEnd { (TyS.plain TyM.nat) with label := none } (sF Sem.moved.succ) = sF Sem.moved.succ from rfl]
  rw [runT]
  show SM.erasedIf (false, false) _ (sF Sem.moved.succ) = _
  simp only [SM.erasedIf, SM.stmtIf, Bool.false_eq_true, if_false]
  show (runT (Kw dm []) ρ φw false (.plain TyM.err) (.assign qY (.const "c")) >>= fun r =>
    SM.guardMod (DiscardOk (Kw dm []) φw r.2) (discardEnd r.2) >>= fun _ =>
      runT (Kw dm []) ρ φw tl hint (.place (.var 1))) (sF Sem.moved.succ) = _
  simp only [Bind.bind, run_assignY]
  rw [SM.guardMod_of (show DiscardOk (Kw dm []) φw (TyS.plain TyM.unit) (sF (.el0 Nat 1)) from trivial)]
  dsimp only
  rw [show discardEnd (TyS.plain TyM.unit) (sF (.el0 Nat 1)) = sF (.el0 Nat 1) from rfl]
  exact run_readX dm ρ tl hint

/-- **The fundamental lemma applied to a run that ends a borrow over refilled content.** -/
theorem w_endOk (dm : DataModel) (ρ : Assignment) (tl : Bool) (hint : TyS) :
    runT (Kw dm []) ρ φw tl hint tEndOk (sF (.el0 Nat 1)) =
      some ((.el0 Nat 1, { (TyS.plain TyM.nat) with label := none }), sX) ∧ SGood dm [] φw sX :=
  ⟨run_endOk dm ρ tl hint, (fund_all (fundCtx_Kw dm []) tEndOk (by simp [tEndOk, Term.valsOk]) tl hint
    (sF (.el0 Nat 1)) sX _ (sF_good dm (nat_mem dm 1)) (run_endOk dm ρ tl hint)).2.2.2⟩

end Ends

end Ochr.Meaning.Strict.Witness
