import Ochr.Meaning.Strict.Witness
import Ochr.Meaning.ClosureCE
import Ochr.Meaning.FrameProp

/-!
# Two frames the fundamental lemma does not cover, attacked (kernel-checked)

**(1) A non-recursive closure bound `self` to `err`, so a body that writes at a field path never ran.**
The `.fix` clause runs a closure's body in a frame `[caps…, self, x̄]` (`bodyAt`; since docs/31 D126 above an
empty frame 0, as the states here are); for a closure with no
decreasing parameter `self` was bound to `err` at the closure's own function type (`fixG`'s old `none`
case), on the ground that such a body never reads `self` (the checker has no `self` in scope there). But
the strict test after an assignment or a borrow at a field path (`lentOk`, i.e. `StateOk`) asks EVERY
binding of the state to hold an open member of its stored type, and `err` is an open member of no type.
So the body of `x.0 := c` failed in such a frame at every argument (`body_errSelf`), and with it every
accepted closure of that shape: `def SetFstOwned (p : Pair(Nat, Nat)) : Unit := p.0 := Z`, `SetFst`
through a borrow, the suite's `PartMove` (accepted programs with no meaning; kernel-checked at the `.fix`
clause on `spine-model3` fa8847a6, `setT_none`, removed with the fix). With `self` an open member the same
body runs (`body_goodSelf`). Repaired (docs/31 D113): a non-recursive `fix` is the recursive one at rank
`0`, its `self` the weakened stage `0`, a member of that type. The run's exemption of `[*]` from the test,
made for `*x := S(*x)` in `Regress/CallInPlace`, was this fault met there; it is gone too.

**(2) The frame property as stated is false: the run in place tests the caller's frames.**
`FrameProp.run_frame` relates a run in place (the caller's frames below the callee's) with the run in the
closure's frame alone, under `FrameRel`, which says nothing of what the caller's frames hold. The same
test (`StateOk`) quantifies over every position of the state, so in place it reads the caller's frames:
a caller binding holding `err` makes the in-place run of `x.0 := c` fail where the closure's succeeds
(`run_frame_false`). The repair is a hypothesis on the caller's frames (the in-place state good,
`Strict.SGood`), which every use has.
-/

namespace Ochr.Meaning.Strict.FrameCE

open Ochr Ochr.Meaning Ochr.Meaning.Strict Ochr.Meaning.Strict.Witness
open Ochr.Meaning.Strict.FieldWriteCE (nat_mem)

/-! ## `x.0 := c` in a frame `[self, x]` -/

/-- The body: the predecessor field of the parameter `x` (variable `0`) assigned `c` (the number `0`). -/
def body : Term := .assign (pred 0) (.const "c")

/-- `self` at a type `T`, meaning `m` (as `bodyAt` binds it: reading `.pi` of the codomain's reading). -/
def selfB (T : TyM) (m : Sem) : SBinding := { ty := .plain T, val := fun _ => m, decl := .pi .other }

/-- The parameter `x : Nat`, holding `x`. -/
def xB (x : Sem) : SBinding := { ty := .plain TyM.nat, val := fun _ => x, decl := .other }

/-- The frames `low` (a caller's, in place) below the closure's frame `[self, x]`; nothing lent. -/
def sX (low : List SFrame) (T : TyM) (m : Sem) (x : Sem) : SState :=
  { env := low ++ [{ binds := [selfB T m, xB x] }], shape := fun _ => none, nextLoan := 0 }

theorem live_sX (low : List SFrame) (T : TyM) (m x : Sem) : (sX low T m x).liveLabels = [] := by
  unfold SState.liveLabels
  have : ∀ (ps : List Pos), ps.filterMap (fun _ => (none : Option Nat)) = [] := fun ps => by
    induction ps with | nil => rfl | cons _ _ ih => simp [ih]
  simp only [sX, this, List.mergeSort_nil]

theorem top_sX (low : List SFrame) (T : TyM) (m x : Sem) : (sX low T m x).topIdx = low.length := by
  simp [SState.topIdx, sX]

theorem resolve_sX (low : List SFrame) (T : TyM) (m x : Sem) :
    resolve (sX low T m x) (pred 0) = some (.bind low.length 1, [.proj 0]) := by
  simp [resolve, pred, Place.steps, SState.varPos, sX, SState.topIdx]

theorem valAt_sX (low : List SFrame) (T : TyM) (m x : Sem) :
    (sX low T m x).valAt (.bind low.length 1) = fun _ => x := by
  simp [SState.valAt, sX, xB]

theorem tyAt_sX (low : List SFrame) (T : TyM) (m x : Sem) :
    (sX low T m x).tyAt (.bind low.length 1) = .plain TyM.nat := by
  simp [SState.tyAt, sX, xB]

theorem updAt_pred_set (dm : DataModel) (Γ : List IndDecl) (T : TyS) :
    Sem.updAt dm Γ T (fun _ => .el0 Nat 0) [.proj 0] (.el0 Nat 1) = some (.el0 Nat 1) := by
  rw [Sem.updAt.eq_def]
  simp only [Sem.asNat_el0]
  rw [Sem.updAt.eq_def]
  simp [Sem.succ_el0]

/-- The write made: `x` is `S(0)` again, the number `1`. -/
theorem sX_set (low : List SFrame) (T : TyM) (m : Sem) :
    (sX low T m (.el0 Nat 1)).setAt (.bind low.length 1) (fun _ => .el0 Nat 1) = sX low T m (.el0 Nat 1) := by
  simp only [sX, SState.setAt, SState.mk.injEq, and_true]
  induction low with
  | nil => simp [List.modify, xB]
  | cons a l ih => simp only [List.length_cons, List.cons_append, List.modify_succ_cons, ih]

theorem contentOf_sX (dm : DataModel) (low : List SFrame) (T : TyM) (m : Sem) :
    contentOf (Kw dm []) φw (pred 0) (sX low T m (.el0 Nat 1)) =
      some ((.el0 Nat 0, { (TyS.plain TyM.nat) with label := none }, .bind low.length 1, [.proj 0]), sX low T m (.el0 Nat 1)) := by
  unfold contentOf
  rw [resolve_sX]
  dsimp only
  rw [access_noLive (live_sX _ _ _ _), valAt_sX, tyAt_sX]
  simp [Sem.follow, Sem.step, Sem.asNat_el0]

theorem placeTy_sX (dm : DataModel) (low : List SFrame) (T : TyM) (m : Sem) :
    placeTy (Kw dm []) φw (pred 0) (sX low T m (.el0 Nat 1)) = .plain TyM.nat := by
  unfold placeTy; rw [contentOf_sX]; rfl

theorem assignAt_sX (dm : DataModel) (low : List SFrame) (T : TyM) (m : Sem) :
    assignAt (Kw dm []) φw (pred 0) (.el0 Nat 0) none (sX low T m (.el0 Nat 1)) =
      some ((.el0 Unit (), .plain TyM.unit), sX low T m (.el0 Nat 1)) := by
  unfold assignAt
  rw [resolve_sX]
  dsimp only
  simp only [List.isEmpty_cons, Bool.false_and, Bool.false_eq_true, if_false]
  rw [access_noLive (live_sX _ _ _ _)]
  have hsc : setContent (Kw dm []) φw (.bind low.length 1) [.proj 0] (.el0 Nat 0) (sX low T m (.el0 Nat 1)) =
      some (⟨⟩, sX low T m (.el0 Nat 1)) := by
    rw [setContent_const (valAt_sX _ _ _ _) (updAt_pred_set dm [] _), sX_set]
  rw [hsc]

open Classical in
/-- The run of `x.0 := c` in the frame, up to the final test: it succeeds exactly where `StateOk` holds. -/
theorem run_body_iff (dm : DataModel) (ρ : Assignment) (low : List SFrame) (T : TyM) (m : Sem) (tl : Bool) (hint : TyS) :
    runT (Kw dm []) ρ φw tl hint body (sX low T m (.el0 Nat 1)) =
      if StateOk (Kw dm []) φw (sX low T m (.el0 Nat 1)) then some ((Sem.el0 Unit (), TyS.plain TyM.unit), sX low T m (.el0 Nat 1))
      else none := by
  have hconst : ∀ U, runT (Kw dm []) ρ φw false U (.const "c") (sX low T m (.el0 Nat 1)) =
      some ((.el0 Nat 0, .plain TyM.nat), sX low T m (.el0 Nat 1)) := by
    intro U; rw [runT]; rfl
  rw [body, runT]
  show SM.erasedIf (false, false) _ _ = _
  simp only [SM.erasedIf, SM.stmtIf, Bool.false_eq_true, if_false]
  simp only [hconst, Option.bind_eq_bind, Option.bind_some]
  rw [placeTy_sX]
  rw [if_pos ⟨nat_mem dm 0, fun _ h => by cases h⟩]
  have hao : AssignOk (Kw dm []) φw (pred 0) (sX low T m (.el0 Nat 1)) := by
    unfold AssignOk
    rw [resolve_sX]
    exact ⟨fun _ => accessOk_noLive (live_sX _ _ _ _) _ _, fun h => by cases h⟩
  rw [show (TyS.plain TyM.nat).label = none from rfl, SM.guarded_of hao, assignAt_sX]
  dsimp only
  have hinv : invalidate (Kw dm []) φw (pred 0) (sX low T m (.el0 Nat 1)) = sX low T m (.el0 Nat 1) := rfl
  have hlent : lentOk (Kw dm []) φw (pred 0) (sX low T m (.el0 Nat 1)) ↔ StateOk (Kw dm []) φw (sX low T m (.el0 Nat 1)) := by
    unfold lentOk; rw [resolve_sX]
    simp
  rw [hinv]
  by_cases h : StateOk (Kw dm []) φw (sX low T m (.el0 Nat 1))
  · rw [if_pos ⟨trivial, hlent.2 h⟩, if_pos h]
  · rw [if_neg (fun h' => h (hlent.1 h'.2)), if_neg h]


theorem positions_sX0 (T : TyM) (m x : Sem) : (sX [{}] T m x).positions = [.bind 1 0, .bind 1 1] := by
  simp [sX, SState.positions, List.range']

/-- With `self` an open member of its type and no caller frame, every binding is: the test passes. -/
theorem stateOk_goodSelf (dm : DataModel) (T : TyM) (m : Sem) (hm : dm.pmem [] m T) :
    StateOk (Kw dm []) φw (sX [{}] T m (.el0 Nat 1)) := by
  intro ψ _
  refine ⟨fun f i hpi => ?_, fun q l hq => by cases hq⟩
  rw [positions_sX0] at hpi
  simp only [List.mem_cons, Pos.bind.injEq, List.mem_nil_iff, or_false] at hpi
  rcases hpi with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact .inl hm
  · exact .inl (.mem (nat_mem dm 1))

/-- `err` is an open member of no type (a member is whole, `err` is not). -/
theorem not_pmem_err (dm : DataModel) (Γ : List IndDecl) (T : TyM) : ¬ dm.pmem Γ .err T := by
  intro h
  cases h with
  | mem h => exact absurd (mem_whole dm.read_wholeFields h) (by simp [Sem.whole])

/-- A binding holding `err` at a type other than `err` fails the test (at the run's future, the one
typed future of a state with no live label). -/
theorem not_stateOk_err (dm : DataModel) (s : SState) (hl : s.liveLabels = []) (f i : Nat)
    (hp : Pos.bind f i ∈ s.positions) (hv : s.valAt (.bind f i) φw = .err) (hT : (s.tyAt (.bind f i)).m ≠ TyM.err) :
    ¬ StateOk (Kw dm []) φw s := by
  intro h
  rcases (h φw (typedFut_self_noLive hl)).1 f i hp with h0 | ⟨h0, -⟩
  · rw [hv] at h0; exact not_pmem_err dm [] _ h0
  · exact hT h0

/-- **The body of a non-recursive closure that writes at a field path does not run when `self` is
`err`** at any type other than `err` (its function type among them), in or out of tail position, at
every hint. -/
theorem body_errSelf (dm : DataModel) (ρ : Assignment) (T : TyM) (hT : T ≠ TyM.err) (tl : Bool) (hint : TyS) :
    runT (Kw dm []) ρ φw tl hint body (sX [{}] T .err (.el0 Nat 1)) = none := by
  rw [run_body_iff, if_neg (not_stateOk_err dm _ (live_sX _ _ _ _) 1 0 (by rw [positions_sX0]; simp) rfl (by simpa [SState.tyAt, sX, selfB, TyS.plain] using hT))]

/-- **With `self` an open member (`moved`), the same body runs.** -/
theorem body_goodSelf (dm : DataModel) (ρ : Assignment) (T : TyM) (tl : Bool) (hint : TyS) :
    runT (Kw dm []) ρ φw tl hint body (sX [{}] T .moved (.el0 Nat 1)) =
      some ((.el0 Unit (), .plain TyM.unit), sX [{}] T .moved (.el0 Nat 1)) := by
  rw [run_body_iff, if_pos (stateOk_goodSelf dm T .moved (.moved T))]

/-! ## (2) The frame property: a caller frame holding `err` -/

/-- The caller's frame: one binding `z : Nat` holding `err`. -/
def lowJunk : List SFrame := [{ binds := [natB .err] }]

/-- **In place, below a caller frame holding `err`, the body does not run** (the test reads the caller's
binding). -/
theorem body_inPlace_junk (dm : DataModel) (ρ : Assignment) (T : TyM) (tl : Bool) (hint : TyS) :
    runT (Kw dm []) ρ φw tl hint body (sX lowJunk T .moved (.el0 Nat 1)) = none := by
  rw [run_body_iff, if_neg (not_stateOk_err dm _ (live_sX _ _ _ _) 0 0
    (by simp [sX, lowJunk, SState.positions, List.range']) rfl (by
      show TyM.nat ≠ TyM.err
      intro h; have := congrArg TyM.isErr h; simp [TyM.isErr, TyM.nat, TyM.err] at this))]

/-- The two states are related, as `FrameProp.run_frame` asks: the identity renaming, no parameter,
the caller's frame `lowJunk` below. -/
theorem frameRel_junk (T : TyM) :
    FrameRel (fun l => l) (sX lowJunk T .moved (.el0 Nat 1)) [] (sX lowJunk T .moved (.el0 Nat 1)) (sX [{}] T .moved (.el0 Nat 1)) := by
  have hnl : ∀ l, ¬ (sX [{}] T .moved (.el0 Nat 1)).Live l := fun l hl => by
    simp [SState.Live, live_sX] at hl
  refine ⟨fun l l' h => h, fun j => by simp [sX], ⟨rfl, rfl⟩, fun f _ => rfl, fun p _ ψ => ?_, fun p _ => rfl, ?_,
    fun p _ => by simp [sX], fun q l hq => by simp [sX] at hq, fun l hl => absurd hl (hnl l),
    fun l x _ => by simp [sX], fun m x _ hx => by simp [sX] at hx, fun l x hx => by simp [sX] at hx,
    fun l p _ hp => by simp [sX] at hp, fun l hl => absurd hl (hnl l)⟩
  · simp [cellFuture, Future.updList]
  · refine ⟨{ binds := [selfB T .moved, xB (.el0 Nat 1)] }, { binds := [selfB T .moved, xB (.el0 Nat 1)] }, by simp [sX, lowJunk],
      rfl, rfl, fun i b b' h h' => ?_, by simp, fun j v hv => by simp at hv⟩
    rw [h] at h'; cases h'
    refine ⟨?_, rfl, rfl, fun ψ => rfl⟩
    cases b with | mk ty v d rb => cases ty with | mk m lab => cases lab <;> rfl

theorem frameStart_junk (T : TyM) : FrameStart (sX lowJunk T .moved (.el0 Nat 1)) [] :=
  ⟨fun p hp ψ ψ' _ => by
      rcases p with ⟨f, i⟩ | ⟨f, i⟩ <;> simp [SState.topIdx, sX, lowJunk] at hp <;> subst hp <;>
        rcases i with _ | _ | i <;> simp [SState.valAt, sX, lowJunk, natB],
    by simp, fun p l _ hp => by simp [sX] at hp, fun p l x _ hp => by simp [sX] at hp, List.nodup_nil⟩

/-- **`FrameProp.run_frame` as first stated is false**, at every data model (restated since with the
in-place state good): from related states with no
parameter, the run in place fails (the caller's frame holds `err`, and the test after a write at a
field path reads it) where the run in the closure's frame succeeds. The repair: the in-place state good
(`Strict.SGood`), which excludes the caller's `err`. -/
theorem run_frame_false (dm : DataModel) (ρ : Assignment) :
    ¬ ∀ (σ : Nat → Nat) (s₀ : SState) (ks : List Nat) (_ : FrameStart s₀ ks) (tl : Bool) (hint : TyS) (t : Term)
      (_ : t.idFree = true ∨ ks = []) (s s' : SState) (_ : FrameRel σ s₀ ks s s'),
      FrameAgree σ s₀ ks (runT (Kw dm []) ρ φw tl hint t s) (runT (Kw dm []) ρ φw tl hint t s') := by
  intro h
  have := h (fun l => l) _ [] (frameStart_junk TyM.nat) false (.plain TyM.unit) body (.inr rfl) _ _ (frameRel_junk TyM.nat)
  rw [body_inPlace_junk, body_goodSelf] at this
  exact this

end Ochr.Meaning.Strict.FrameCE
