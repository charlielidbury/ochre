import Ochr.Meaning.Strict.Witness
import Ochr.Meaning.ClosureCE
import Ochr.Meaning.FrameProp

/-!
# Two frames the fundamental lemma does not cover, attacked (kernel-checked)

**(1) A non-recursive closure binds `self` to `err`, so a body that writes at a field path never runs.**
The `.fix` clause runs a closure's body in a frame `[caps…, self, x̄]` (`bodyAt`); for a closure with no
decreasing parameter `self` is bound to `err` at the closure's own function type (`fixG`'s `none` case),
on the ground that such a body never reads `self` (the checker has no `self` in scope there). But the
strict test after an assignment or a borrow at a field path (`lentOk`, i.e. `StateOk`) asks EVERY binding
of the state to hold an open member of its stored type, and `err` is an open member of no type. So the
body of `fix (x : Nat) : Unit := x.0 := c` fails at every argument, its closure is `err`, and the strict
`.fix` clause fails (`setT_none`). The checker accepts the same shape at a declared type
(`def SetFstOwned (p : Pair(Nat, Nat)) : Unit := p.0 := Z`, and the suite's `PartMove`, whose
`(*r).0 := z` is such a write): accepted programs with no meaning. With `self` an open member (here
`moved`) the same body runs (`body_goodSelf`). The run's exemption of `[*]` from the test
(`Run.lentOk`, "testing `[*]` rejected a run the checker accepts, `Regress/CallInPlace`") was this fault
met at `*x := S(*x)`, and hid it there.

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


theorem positions_sX0 (T : TyM) (m x : Sem) : (sX [] T m x).positions = [.bind 0 0, .bind 0 1] := by
  simp [sX, SState.positions, List.range']

/-- With `self` an open member of its type and no caller frame, every binding is: the test passes. -/
theorem stateOk_goodSelf (dm : DataModel) (T : TyM) (m : Sem) (hm : dm.pmem [] m T) :
    StateOk (Kw dm []) φw (sX [] T m (.el0 Nat 1)) := by
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
    runT (Kw dm []) ρ φw tl hint body (sX [] T .err (.el0 Nat 1)) = none := by
  rw [run_body_iff, if_neg (not_stateOk_err dm _ (live_sX _ _ _ _) 0 0 (by rw [positions_sX0]; simp) rfl (by simpa [SState.tyAt, sX, selfB, TyS.plain] using hT))]

/-- **With `self` an open member (`moved`), the same body runs.** -/
theorem body_goodSelf (dm : DataModel) (ρ : Assignment) (T : TyM) (tl : Bool) (hint : TyS) :
    runT (Kw dm []) ρ φw tl hint body (sX [] T .moved (.el0 Nat 1)) =
      some ((.el0 Unit (), .plain TyM.unit), sX [] T .moved (.el0 Nat 1)) := by
  rw [run_body_iff, if_pos (stateOk_goodSelf dm T .moved (.moved T))]

/-! ## (1) at the `.fix` clause: `fix (x : Nat) : Unit := x.0 := c` has no meaning -/

/-- The closure term: one parameter `x : Nat`, codomain `Unit`, no decreasing parameter. -/
def setT : Term := .fix ⟨"SetP"⟩ [⟨"x"⟩] [.nat] .unit none body

def psN : List PiDom := [⟨false, fun _ => TyM.nat⟩]
def outU : PiCod := ⟨false, fun _ => TyM.unit⟩

theorem runDoms_set (dm : DataModel) (ρ : Assignment) :
    runDoms (Kw dm []) ρ φw (stateOf 0 []) [.nat] = psN := rfl

theorem codOf_set (dm : DataModel) (ρ : Assignment) (bs : List PBind) :
    codOf (Kw dm []) ρ φw (stateOf 0 []) bs .unit = outU := rfl

/-- The closure's frame at argument `1`, as `bodyAt` builds it, is `[self ↦ err, x ↦ 1]`. -/
theorem frame_set (dm : DataModel) (ρ : Assignment) (T : TyM) :
    ([Sem.el0 Nat 1].zip psN).foldl (fixStep
        (bindsOf (Kw dm []) ρ φw (stateOf 0 []) [.nat], fixCod (Kw dm []) ρ φw (stateOf 0 [])
          (bindsOf (Kw dm []) ρ φw (stateOf 0 []) [.nat]) .unit, .other))
      ((stateOf 0 []).pushBind (selfB T .err), [], []) = (sX [] T .err (.el0 Nat 1), [Sem.el0 Nat 1], []) := by
  have hnat : ∀ s, runT (Kw dm []) ρ φw false (.plain TyM.err) .nat s = some ((.ty TyM.nat, .plain (TyM.univ 1)), s) := by
    intro s; rw [runT]; rfl
  have hpd : (Kw dm []).D.paramDecls (scopeOf ((stateOf 0 []).pushBind (selfB T .err))) [.nat] = [.other] := rfl
  have hpd' : (Kw dm []).D.paramDecls (scopeOf (stateOf 0 [])) [.nat] = [.other] := rfl
  simp [fixStep, psN, stateOf, SState.pushBind, SState.topIdx, sX, selfB, xB, bindsOf, runBinds, mkBind, TyS.plain, hnat,
    Sem.asTy, hpd, hpd', extendBy, extendBinds]
  refine ⟨?_, rfl⟩
  rw [runT]; rfl

/-- `fix (x : Nat) : Unit := x.0 := c`'s function type is a function type, not `err`. -/
theorem piSet_ne_err (dm : DataModel) : piTyAt dm.read 1 psN outU ≠ TyM.err := by
  intro h
  have := congrArg TyM.isErr h
  simp [piTyAt, piTyL, TyM.isErr, TyM.err, lvl0, Lvl.toTy] at this

/-- The closure's function: `fixG`'s `none` case, the body with `self` `err`. -/
noncomputable def gSet (dm : DataModel) (ρ : Assignment) : List Sem → Option BodyOut :=
  fixG (Kw dm []) ρ φw (bindsOf (Kw dm []) ρ φw (stateOf 0 []) [.nat], fixCod (Kw dm []) ρ φw (stateOf 0 [])
      (bindsOf (Kw dm []) ρ φw (stateOf 0 []) [.nat]) .unit, .other) 1 (stateOf 0 []) psN outU
    (piTyAt dm.read 1 psN outU) 0 none body

/-- **The body fails at the argument `1`.** -/
theorem gSet_one (dm : DataModel) (ρ : Assignment) : gSet dm ρ [Sem.el0 Nat 1] = none := by
  simp only [gSet, fixG, fixBodyAt]
  have hself : ({ ty := .plain (piTyAt dm.read 1 psN outU), val := fun _ => .err, decl := .pi .other } : SBinding) =
      selfB (piTyAt dm.read 1 psN outU) .err := rfl
  rw [hself, frame_set]
  simp only
  rw [body_errSelf dm ρ _ (piSet_ne_err dm)]

/-- **The closure is `err`**: its body fails at the argument `1`, so its telescope is not built
(`ClosureCE.mkTelL_param_some`). -/
theorem closure_set_err (dm : DataModel) (ρ : Assignment) : closureAt dm.read 1 φw psN outU (gSet dm ρ) = .err := by
  simp only [closureAt, closureL]
  split
  · rename_i F hF
    exfalso
    have h1 := ClosureCE.mkTelL_param_some hF (by exact (1 : Nat))
    have hg : gSet dm ρ ([] ++ [Code0.enc dm.read TyM.nat.code0.snd (by exact (1 : Nat))]) = none := gSet_one dm ρ
    simp only [telL, psN, outU, mkTelL] at h1
    rw [hg] at h1
    simp at h1
  · rfl

open Classical in
/-- **The strict `.fix` clause fails at `fix (x : Nat) : Unit := x.0 := c`**, at every data model, in
or out of tail position, at every hint: the closure it builds is `err`, a member of no type. -/
theorem setT_none (dm : DataModel) (ρ : Assignment) (tl : Bool) (hint : TyS) :
    runT (Kw dm []) ρ φw tl hint setT (stateOf 0 []) = none := by
  rw [setT, run_fix_def]
  simp only [SM.erasedIf, SM.stmtIf]
  show (if FoldOk (capStep (Kw dm [])) (CapOk (Kw dm []) φw) (capOrder setT) (stateOf 0 []) then _ else none) = none
  have hco : capOrder setT = [] := by decide
  rw [hco, if_pos (show FoldOk (capStep (Kw dm [])) (CapOk (Kw dm []) φw) [] (stateOf 0 []) from trivial)]
  have hcl : closureAt dm.read ((Kw dm []).D.piSort (scopeOf (stateOf 0 [])) (.pi [⟨"x"⟩] [.nat] .unit))
      φw (runDoms (Kw dm []) ρ φw (stateOf 0 []) [.nat])
      (codOf (Kw dm []) ρ φw (stateOf 0 []) (bindsOf (Kw dm []) ρ φw (stateOf 0 []) [.nat]) .unit)
      (fixG (Kw dm []) ρ φw (bindsOf (Kw dm []) ρ φw (stateOf 0 []) [.nat], fixCod (Kw dm []) ρ φw (stateOf 0 [])
          (bindsOf (Kw dm []) ρ φw (stateOf 0 []) [.nat]) .unit,
          (Kw dm []).D.typeDecl ((Kw dm []).D.teleDecls (scopeOf (stateOf 0 [])) [.nat]) .unit)
        ((Kw dm []).D.piSort (scopeOf (stateOf 0 [])) (.pi [⟨"x"⟩] [.nat] .unit)) (stateOf 0 [])
        (runDoms (Kw dm []) ρ φw (stateOf 0 []) [.nat])
        (codOf (Kw dm []) ρ φw (stateOf 0 []) (bindsOf (Kw dm []) ρ φw (stateOf 0 []) [.nat]) .unit)
        (piTyAt dm.read ((Kw dm []).D.piSort (scopeOf (stateOf 0 [])) (.pi [⟨"x"⟩] [.nat] .unit))
          (runDoms (Kw dm []) ρ φw (stateOf 0 []) [.nat])
          (codOf (Kw dm []) ρ φw (stateOf 0 []) (bindsOf (Kw dm []) ρ φw (stateOf 0 []) [.nat]) .unit))
        (stateOf 0 []).nextLoan none body) = .err := closure_set_err dm ρ
  simp only [SM.strictS]
  rw [if_neg]
  intro h
  erw [hcl] at h
  exact absurd (mem_whole dm.read_wholeFields h) (by simp [Sem.whole])

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
    FrameRel (fun l => l) (sX lowJunk T .moved (.el0 Nat 1)) [] (sX lowJunk T .moved (.el0 Nat 1)) (sX [] T .moved (.el0 Nat 1)) := by
  have hnl : ∀ l, ¬ (sX [] T .moved (.el0 Nat 1)).Live l := fun l hl => by
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

/-- **`FrameProp.run_frame` is false as stated**, at every data model: from related states with no
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
