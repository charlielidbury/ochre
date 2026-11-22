import Ochr.Meaning.Strict.FrameLocCE
import Ochr.Meaning.Mono

/-!
# `RunFrameS` as D129 stated it is false: the closure's frame 0 is unconstrained (lead30; docs/31 D201)

`Steps/FrameFrag.RunFrameS` relates the in-place state `s` and the closure's state `s'` by `FrameRelS`. `FrameRel`
says the closure has two frames and compares its TOP frame with the callee's frame in place; of the closure's frame 0
(the cells of the borrow parameters, docs/31 D126) it says only that its first `ks.length` bindings' values are what
the caller's frames are read at (`lowerVal`, `cellFuture`). Its stored types, and any further binding, are free; and
RunFrameS asks goodness (`SGood`) of the in-place state only. But the whole-state strict test after a write or a
borrow at a field path (`lentOk`, `StateOk`) reads EVERY binding: in place the caller's frames, which `SGood s` makes
good; in the closure frame 0, which nothing does.

The counterexample (`runFrameS_false`): no parameter label (`ks = []`); in place `[{}, {self : Nat ↦ 0, x : Nat ↦ 1}]`;
the closure the same but for one binding in frame 0, `junk : Nat ↦ err` (reading no label, so the locality clauses
hold). The body `x.0 := c` (`c` the global `0`) writes at a field path: in place the run succeeds, the state after it
good; in the closure `StateOk` fails at `junk`, so the run fails. Every hypothesis of `RunFrameS` holds.

No call makes such a state: at a call the closure's frame 0 holds exactly the cells, `x° ↦ loan l` read at its label's
content type (`fixBodyAt`), which are good at every typed future. The repair is a hypothesis, not a change of the
relation: the closure's state is good too (`Strict.SGood K.dm K.Γ φ s'`), which the run keeps (`fund_all`), as it keeps
the in-place state's.
-/

namespace Ochr.Meaning.Strict.FrameCellCE

open Ochr Ochr.Meaning Ochr.Meaning.Strict Ochr.Meaning.Strict.Witness
open Ochr.Meaning.Strict.FieldWriteCE (nat_mem)
open Ochr.Meaning.Steps.Form.FrameJ2 (FrameRelS FrameAgreeS SelfRel topBind? setTopBind)

/-- The callee's frame: `self : Nat ↦ 0` (the function's own binding, index `0`), `x : Nat ↦ 1` (variable `0`). -/
def topF : SFrame := { binds := [natB (.el0 Nat 0), natB (.el0 Nat 1)] }

/-- A binding of the closure's frame 0 that is no cell: stored at `Nat`, holding `err`. -/
def junk : SBinding := { ty := .plain TyM.nat, val := fun _ => .err }

/-- In place: the caller's frame (empty) and the callee's. -/
def sIn : SState where
  env := [{}, topF]
  shape := fun _ => none
  nextLoan := 0
  heldTy := fun _ => TyM.nat
  heldMem := fun _ => .el0 Nat 0

/-- The closure: frame 0 holds `junk`, the top frame the callee's. -/
def sCl : SState := { sIn with env := [{ binds := [junk] }, topF] }

/-- The body: `x.0 := c`, a write at a field path. -/
def body : Term := .assign (pred 0) (.const "c")

theorem positions_sIn : sIn.positions = [.bind 1 0, .bind 1 1] := by
  simp [sIn, topF, SState.positions, List.range']

theorem positions_sCl : sCl.positions = [.bind 0 0, .bind 1 0, .bind 1 1] := by
  simp [sCl, sIn, topF, SState.positions, List.range']

theorem live_none {s : SState} (h : s.shape = fun _ => none) : s.liveLabels = [] := by
  unfold SState.liveLabels
  have : ∀ (ps : List Pos), ps.filterMap (fun _ => (none : Option Nat)) = [] := fun ps => by
    induction ps with | nil => rfl | cons _ _ ih => simp [ih]
  rw [h, this, List.mergeSort_nil]

theorem live_sIn : sIn.liveLabels = [] := live_none rfl
theorem live_sCl : sCl.liveLabels = [] := live_none rfl

theorem upd_one (dm : DataModel) (Γ : List IndDecl) (T : TyS) :
    Sem.updAt dm Γ T (fun _ => .el0 Nat 0) [.proj 0] (.el0 Nat 1) = some (.el0 Nat 1) := by
  rw [Sem.updAt.eq_def]
  simp [Sem.asNat_el0]
  rw [Sem.updAt.eq_def]
  simp [Sem.succ, Sem.asNat_el0]

/-! ## The run of `x.0 := c` from either state: it succeeds exactly where `StateOk` holds after the write -/

/-- The state after the write (the same number, `1`, written back at `x`). -/
noncomputable def after (s : SState) : SState := s.setAt (.bind 1 1) fun _ => .el0 Nat 1

open Classical in
theorem run_body (dm : DataModel) (ρ : Assignment) (tl : Bool) (hint : TyS) (s : SState)
    (hres : resolve s (pred 0) = some (.bind 1 1, [.proj 0]))
    (hres' : resolve (after s) (pred 0) = some (.bind 1 1, [.proj 0]))
    (hl : s.liveLabels = []) (hv : s.valAt (.bind 1 1) = fun _ => .el0 Nat 1)
    (ht : s.tyAt (.bind 1 1) = .plain TyM.nat) :
    runT (Kw dm []) ρ φw tl hint body s =
      if StateOk (Kw dm []) φw (after s) then some ((Sem.el0 Unit (), TyS.plain TyM.unit), after s) else none := by
  have hconst : ∀ T, runT (Kw dm []) ρ φw false T (.const "c") s = some ((.el0 Nat 0, .plain TyM.nat), s) := by
    intro T; rw [runT]; rfl
  have hc : contentOf (Kw dm []) φw (pred 0) s =
      some ((.el0 Nat 0, { (TyS.plain TyM.nat) with label := none }, .bind 1 1, [.proj 0]), s) := by
    unfold contentOf
    rw [hres]
    dsimp only
    rw [access_noLive hl, ht, hv]
    simp [Sem.follow, Sem.step, Sem.asNat_el0]
  have hpt : placeTy (Kw dm []) φw (pred 0) s = .plain TyM.nat := by
    unfold placeTy; rw [hc]; rfl
  have hao : AssignOk (Kw dm []) φw (pred 0) s := by
    unfold AssignOk
    rw [hres]
    exact ⟨fun _ => accessOk_noLive hl _ _, fun h => by cases h⟩
  have has : assignAt (Kw dm []) φw (pred 0) (.el0 Nat 0) none s = some ((.el0 Unit (), .plain TyM.unit), after s) := by
    unfold assignAt
    rw [hres]
    dsimp only
    simp only [List.isEmpty_cons, Bool.false_and, Bool.false_eq_true, if_false]
    rw [access_noLive hl]
    have hu : Sem.updAt (Kw dm []).dm (Kw dm []).Γ (s.tyAt (.bind 1 1)) (fun _ => .el0 Nat 0) [.proj 0] (.el0 Nat 1) =
        some (.el0 Nat 1) := upd_one dm [] _
    rw [setContent_const hv hu]
    rfl
  show runT (Kw dm []) ρ φw tl hint (.assign (pred 0) (.const "c")) s = _
  rw [runT]
  show SM.erasedIf (false, false) _ s = _
  simp only [SM.erasedIf, SM.stmtIf, Bool.false_eq_true, if_false]
  simp only [hconst, Option.bind_eq_bind, Option.bind_some]
  rw [hpt, if_pos ⟨nat_mem dm 0, fun _ h => by cases h⟩]
  rw [show (TyS.plain TyM.nat).label = none from rfl, SM.guarded_of hao, has]
  dsimp only
  have hinv : invalidate (Kw dm []) φw (pred 0) (after s) = after s := rfl
  have hio : InvalidateOk (Kw dm []) φw (pred 0) (after s) := trivial
  rw [hinv]
  unfold lentOk
  rw [hres']
  simp only [hio, true_and, List.cons.injEq, reduceCtorEq, false_and, false_or]

/-! ## `StateOk` after the write: true in place, false in the closure -/

theorem not_pmem_err (dm : DataModel) (Γ : List IndDecl) : ¬ dm.pmem Γ .err TyM.nat := by
  intro h
  cases h with
  | mem h => obtain ⟨n, hn⟩ := h; cases hn

theorem positions_after_in : (after sIn).positions = [.bind 1 0, .bind 1 1] := by
  unfold after; rw [SState.positions_setAt, positions_sIn]

theorem positions_after_cl : (after sCl).positions = [.bind 0 0, .bind 1 0, .bind 1 1] := by
  unfold after; rw [SState.positions_setAt, positions_sCl]

theorem stateOk_in (dm : DataModel) : StateOk (Kw dm []) φw (after sIn) := by
  intro ψ _
  refine ⟨fun f i hpi => ?_, fun q l hq => ?_⟩
  · rw [positions_after_in] at hpi
    simp only [List.mem_cons, Pos.bind.injEq, List.mem_nil_iff, or_false] at hpi
    rcases hpi with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact .inl (.mem (nat_mem dm 0))
    · have hv : (after sIn).valAt (.bind 1 1) = fun _ => .el0 Nat 1 :=
        valAt_setAt_self _ _ _ (by rw [positions_sIn]; simp)
      have ht : (after sIn).tyAt (.bind 1 1) = .plain TyM.nat := by unfold after; rw [tyAt_setAt]; rfl
      rw [hv, ht]
      exact .inl (.mem (nat_mem dm 1))
  · cases hq

theorem not_stateOk_cl (dm : DataModel) : ¬ StateOk (Kw dm []) φw (after sCl) := by
  intro h
  have hl : (after sCl).liveLabels = [] := by unfold after; rw [liveLabels_setAt, live_sCl]
  obtain ⟨hb, -⟩ := h φw (typedFut_self_noLive hl)
  have hj := hb 0 0 (by rw [positions_after_cl]; simp)
  have hv : (after sCl).valAt (.bind 0 0) = fun _ => .err := rfl
  have ht : (after sCl).tyAt (.bind 0 0) = .plain TyM.nat := rfl
  rw [hv, ht] at hj
  rcases hj with hj | ⟨hj, -⟩
  · exact not_pmem_err dm [] hj
  · have := congrArg TyM.isErr hj
    simp [TyM.isErr, TyM.nat, TyM.err, TyS.plain] at this

/-! ## Every hypothesis of `RunFrameS` holds at the two states -/

/-- The in-place state is good. -/
theorem sIn_good (dm : DataModel) : SGood dm [] φw sIn := by
  refine ⟨fun ψ _ f i hp => ?_, fun ψ _ p l hl => ?_, fun l hl => ?_, fun f i l hl => ?_,
    ⟨fun p ψ ψ' h => ?_, fun r x _ hs ψ ψ' _ => ?_, fun p x hp => ?_⟩, fun p l ⟨ψ, x, hne⟩ => ?_,
    fun p q l hp _ => by cases hp⟩
  · rw [positions_sIn] at hp
    simp only [List.mem_cons, Pos.bind.injEq, List.mem_nil_iff, or_false] at hp
    rcases hp with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact .inl (.mem (nat_mem dm 0))
    · exact .inl (.mem (nat_mem dm 1))
  · cases hl
  · rw [live_sIn] at hl; cases hl
  · cases hl
  · have : ψ = ψ' := funext fun y => h y (.inl trivial)
    rw [this]
  · cases hs
  · cases hp
  · exfalso; apply hne
    cases p with
    | bind f i => rcases f with _ | _ | f <;> rcases i with _ | _ | i <;> rfl
    | temp f i => rcases f with _ | _ | f <;> rfl

theorem frameStart_in : FrameStart sIn [] :=
  ⟨fun p hp ψ ψ' _ => by
      rcases p with ⟨f, i⟩ | ⟨f, i⟩ <;> simp [SState.topIdx, sIn] at hp <;> subst hp <;> simp [SState.valAt, sIn],
    by simp, fun p l _ hp => by simp [sIn] at hp, fun p l x _ hp => by simp [sIn] at hp, List.nodup_nil⟩

theorem setTop_cl : setTopBind sCl 0 (natB (.el0 Nat 0)) = sCl := rfl

/-- The two states are related by `FrameRelS` at the identity renaming, no parameter, the function's own binding `0`. -/
theorem frameRelS_cl (dm : DataModel) : FrameRelS dm.read id sIn [] 0 sIn sCl := by
  refine ⟨natB (.el0 Nat 0), natB (.el0 Nat 0), rfl, rfl,
    ⟨fun _ => nat_mem dm 0, fun _ => nat_mem dm 0, rfl, rfl, rfl, rfl⟩, ?_⟩
  rw [setTop_cl]
  have hnl : ∀ l, ¬ sCl.Live l := fun l hl => by simp [SState.Live, live_sCl] at hl
  refine ⟨fun l l' h => h, fun j => rfl, ⟨rfl, rfl⟩, fun f _ => rfl, fun p _ ψ => rfl,
    fun p _ => rfl, ?_, fun p _ => rfl, fun q l hq => by simp [sCl, sIn] at hq, fun l hl => absurd hl (hnl l),
    fun l x _ => by simp [sCl, sIn], fun m x _ hx => by simp [sIn] at hx, fun l x hx => by simp [sCl, sIn] at hx,
    fun l p _ hp => by simp [sIn] at hp, fun l hl => absurd hl (hnl l)⟩
  refine ⟨topF, topF, rfl, rfl, rfl, fun i b b' h h' => ?_, rfl, fun j v hv => by simp [topF] at hv⟩
  rw [h] at h'
  cases h'
  obtain ⟨⟨m, lab⟩, v, d, rb⟩ := b
  exact ⟨by simp, rfl, rfl, fun ψ => rfl⟩

/-- Every position of the closure's state reads no label. -/
theorem cl_futureFree (S : Nat → Prop) (p : Pos) : FT S (sCl.valAt p) := by
  intro ψ ψ' _
  cases p with
  | bind f i => rcases f with _ | _ | f <;> rcases i with _ | _ | i <;> rfl
  | temp f i => rcases f with _ | _ | f <;> rfl

/-! ## The refutation -/

/-- **`RunFrameS` as D129 stated it (`RunFrameS_old`) is false** (at the concrete data model `JoinDropCounterexample.dm`; any would do): from the two
states, every hypothesis met, `x.0 := c` succeeds in place and fails in the closure, at `StateOk`'s test of the
closure's frame-0 binding `junk`. -/
theorem runFrameS_false : ¬ Steps.Form.FrameFrag.RunFrameS_old := by
  intro h
  let dm := JoinDropCounterexample.dm
  have := h (Kw dm []) (fun _ => .err) φw id sIn [] 0 false (.plain TyM.err) body sIn sCl (fundCtx_Kw dm [])
    frameStart_in trivial (.inr rfl)
    (fun F' hF => by simp [sCl, sIn] at hF; subst hF; simp [body, pred, topF, Term.freeVars]; decide)
    (frameRelS_cl dm) (fun p => cl_futureFree _ p) (fun p _ => cl_futureFree _ p) (sIn_good dm)
  rw [run_body dm _ false _ sIn rfl rfl live_sIn rfl rfl, run_body dm _ false _ sCl rfl rfl live_sCl rfl rfl,
    if_pos (stateOk_in dm), if_neg (not_stateOk_cl dm)] at this
  exact this

end Ochr.Meaning.Strict.FrameCellCE
