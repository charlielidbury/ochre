import Ochr.Meaning.Attack.CloseCall

/-!
# Equation lemmas for the run layer, on the shapes the attacks meet

`simp [Sem.updAt]` fails (Lean cannot generate `Sem.updAt`'s equational theorems), and `run`'s
clauses are best used as rewrite rules on concrete constructors. The lemmas here are the
equations by `rfl`, for the attack files to rewrite with.
-/

namespace Ochr.Meaning.Attack

open Ochr.Meaning

theorem updAt_nil (dm : DataModel) (Γ : List IndDecl) (T : TyS) (f : Sem → Sem) (s : Sem) :
    Sem.updAt dm Γ T f [] s = some (f s) := rfl

theorem updAt_deref (dm : DataModel) (Γ : List IndDecl) (T : TyS) (f : Sem → Sem) (sts : List Step) (s : Sem) :
    Sem.updAt dm Γ T f (.deref :: sts) s = Sem.updAt dm Γ T f sts s := rfl

/-- Where the decisions classify no term as a statement or as erased (`hfl`; true of `K₀` by
`rfl`), `SM.erasedIf` is the run itself (D19: every clause that can change the state runs under
`Decisions.flags`). -/
theorem stmtIf_noStmt (K : RunCtx) (hfl : ∀ sc t, K.D.flags sc t = (false, false)) (t : Term) (x : SM Res) (s : SState) :
    SM.erasedIf (K.D.flags (scopeOf s) t) x s = x s := by
  rw [hfl]; rfl

open Classical in
/-- The strict ascription: the value is tested against the annotation, and its label must hold
the annotation's type. -/
theorem run_ascribe (K : RunCtx) (ρ : Assignment) (φ : Future) (hint : TyS) (u A : Term) (s : SState)
    (hfl : ∀ sc t, K.D.flags sc t = (false, false)) :
    runT K ρ φ false hint (.ascribe u A) s =
      SM.strictS K.dm.read (do
        let (TA, _) ← SM.onCopy (runT K ρ φ false (.plain .err) A)
        let T : TyS := .plain TA.asTy
        let (v, R) ← runT K ρ φ false T u
        fun s => if labTyOk s R.label T.m then some ((v, { T with label := R.label }), s) else none) s := by
  rw [runT]; exact stmtIf_noStmt K hfl _ _ s

theorem run_letIn (K : RunCtx) (ρ : Assignment) (φ : Future) (hint : TyS) (x : Hint) (u w : Term) (s : SState)
    (hfl : ∀ sc t, K.D.flags sc t = (false, false)) :
    runT K ρ φ false hint (.letIn x u w) s =
      (do
        let ((v, T), s) ← runT K ρ φ false (.plain .err) u s
        let s := pushBindShaped s { ty := T, val := fun _ => v, decl := K.D.declOf (scopeOf s) u }
        let ((r, R), s) ← runT K ρ φ false hint w s
        let held : Option Nat := match s.env.getLast? with
          | some fr => s.shape (.bind s.topIdx (fr.binds.length - 1))
          | none => none
        let s := match held with | some l => s.endLabel l | none => letLenders s
        some ((r, R), s.dropLast)) := by
  rw [runT]; exact stmtIf_noStmt K hfl _ _ s

theorem meanV_abs (K : RunCtx) (ρ : Assignment) (φ : Future) (hint : TyS) (σ : Nat) :
    meanV K ρ φ hint (.abs σ) = ρ σ := rfl

theorem meanV_tNat (K : RunCtx) (ρ : Assignment) (φ : Future) (hint : TyS) :
    meanV K ρ φ hint .tNat = .ty TyM.nat := rfl

theorem meanV_loan (K : RunCtx) (ρ : Assignment) (φ : Future) (hint : TyS) (l : Nat) :
    meanV K ρ φ hint (.loan l) = φ l := rfl

end Ochr.Meaning.Attack

namespace Ochr.Meaning.Attack

open Ochr.Meaning

/-- A binding pushed onto the one empty frame of `emptyState`: the frame holds just it. -/
theorem pushBind_emptyState (k : Nat) (b : SBinding) :
    (emptyState k).pushBind b = { env := [{ binds := [b] }], shape := fun _ => none, nextLoan := k } := by
  simp [emptyState, SState.pushBind, SState.topIdx]

/-- `var 0` in that state resolves to the binding, with no steps. -/
theorem resolve_var0_one (k : Nat) (b : SBinding) :
    resolve { env := [{ binds := [b] }], shape := fun _ => none, nextLoan := k } (.var 0)
      = some (.bind 0 0, []) := by
  simp [resolve, SState.varPos, SState.topIdx, Ochr.Place.steps]

end Ochr.Meaning.Attack

namespace Ochr.Meaning.Attack

open Ochr.Meaning

/-- No live label, no access: `access` is the identity on a state whose shape is empty. -/
theorem access_noShape (s : SState) (hs : s.shape = fun _ => none) (p : Pos) (hit : List Step → Bool) : s.access p hit = s := by
  have h0 : ∀ l : List Pos, List.filterMap (fun _ : Pos => (none : Option Nat)) l = [] := by
    intro l; induction l with
    | nil => rfl
    | cons _ _ ih => simpa [List.filterMap_cons] using ih
  have h : s.liveLabels = [] := by
    simp [SState.liveLabels, hs, h0]
  simp [SState.access, h]

/-- `contentOf (var 0)` on the one-binding shape-free state: the binding's value at `φ`, its
type, position `bind 0 0`, no steps; the state unchanged. -/
theorem contentOf_var0_one (K : RunCtx) (φ : Future) (k : Nat) (b : SBinding) :
    contentOf K φ (.var 0) { env := [{ binds := [b] }], shape := fun _ => none, nextLoan := k }
      = some ((b.val φ, b.ty, .bind 0 0, []), { env := [{ binds := [b] }], shape := fun _ => none, nextLoan := k }) := by
  have ha := fun hit => access_noShape { env := [{ binds := [b] }], shape := fun _ => none, nextLoan := k } rfl (.bind 0 0) hit
  have hcf : SState.typedFuture { env := [{ binds := [b] }], shape := fun _ => none, nextLoan := k } φ = φ := by
    have h0 : ∀ l : List Pos, List.filterMap (fun _ : Pos => (none : Option Nat)) l = [] := by
      intro l; induction l with
      | nil => rfl
      | cons _ _ ih => simpa [List.filterMap_cons] using ih
    funext l; simp [SState.typedFuture, SState.liveLabels, h0]
  simp only [contentOf, resolve_var0_one, ha, hcf, SState.tyAt, SState.valAt, Sem.follow]
  rfl

end Ochr.Meaning.Attack

namespace Ochr.Meaning.Attack

open Ochr.Meaning

/-- `&(var 0)` on the one-binding shape-free state, the content whole: label `k` (the state's
counter), the binding now reads `k`'s final content, the old content parked in temp `0` holding
`k`; the result is the old content at `φ` with `k` in its type. -/
theorem borrowPlace_var0_one (K : RunCtx) (φ : Future) (k : Nat) (b : SBinding) (hw : (b.val φ).whole) :
    borrowPlace K φ (.var 0) { env := [{ binds := [b] }], shape := fun _ => none, nextLoan := k }
      = some ((b.val φ, { b.ty with label := some k }),
          { env := [{ binds := [{ b with val := fun φ' => φ' k }], temps := [fun _ => b.val φ] }],
            shape := fun p => if p = .temp 0 0 then some k else none, nextLoan := k + 1,
            lent := fun m => if m = k then [⟨.bind 0 0, [], false⟩] else [],
            heldTy := fun m => if m = k then b.ty.m else TyM.err,
            heldMem := fun m => if m = k then b.val φ else .err }) := by
  simp only [borrowPlace, contentOf_var0_one, bind, Option.bind]
  simp [hw, SState.freshLoan, SState.pushTempShaped, SState.pushTemp, SState.setAt, SState.topIdx,
    SState.tyAt, SState.valAt, updAt_nil, SState.setLent, SState.setHeldTy, SState.setHeldMem]

end Ochr.Meaning.Attack

namespace Ochr.Meaning.Attack

open Ochr.Meaning

/-- Level 0's decoding at `Nat` reads a number by its tag. -/
theorem dec_nat_as (R : DataRead) (s : Sem) : Code0.nat.dec R s = s.as Nat := by
  by_cases h : ∃ a, Code0.enc R .nat a = s
  · obtain ⟨a, rfl⟩ := h
    rw [Code0.dec_enc]; simp [Code0.enc, Sem.as]
  · rw [Code0.dec, dif_neg h]
    cases s with
    | el0 B b =>
      simp only [Sem.as]
      split
      · rename_i hB; subst hB; exact absurd ⟨b, rfl⟩ h
      · rfl
    | _ => rfl

/-- Level 0's decoding at `Nat` on a number is the number. -/
theorem dec_nat_el0 (R : DataRead) (n : Nat) : Code0.nat.dec R (.el0 Nat n) = some n := Code0.dec_enc R .nat n

/-- Applying `σ_g`'s meaning `F` (tagged at its carrier) to a number, along its telescope code:
the borrow-returning result at `Nat`, forward value `(F n).val.1`, and the backward function
reads the one lent place from the final content. -/
theorem applyFnL_G (R : DataRead) (F : GCar) (n : Nat) :
    applyFnL (lvl0 R) telG (.el0 GCar F) [.el0 Nat n]
      = some (.ref Nat .nat (F n).val.1 fun v => [.el0 Nat ((F n).val.2 v).2]) := by
  have hu : Sem.as GCar (.el0 GCar F) = some F := by simp [Sem.as]
  simp only [applyFnL, lvl0, hu, Option.bind_some, telG, applyTelL, dec_nat_el0 R]
  rfl

end Ochr.Meaning.Attack

namespace Ochr.Meaning.Attack

open Ochr.Meaning

/-- The state after `&(var 0)` on the one-binding state (`borrowPlace_var0_one`'s output). -/
def S₂ (b : SBinding) (k : Nat) (c : Sem) : SState :=
  { env := [{ binds := [{ b with val := fun φ' => φ' k }], temps := [fun _ => c] }],
    shape := fun p => if p = .temp 0 0 then some k else none, nextLoan := k + 1,
    lent := fun m => if m = k then [⟨.bind 0 0, [], false⟩] else [],
    heldTy := fun m => if m = k then b.ty.m else TyM.err,
    heldMem := fun m => if m = k then c else .err }

/-- Where the call's states lend: `k`, the plain borrow of `c1`; `k+1`, the returned borrow, a fill
over `c1` (the call's [Lend], docs/31 D29). -/
def lentA (k : Nat) : Nat → List Site := fun m =>
  if m = k + 1 then [⟨.bind 0 0, [], true⟩] else if m = k then [⟨.bind 0 0, [], false⟩] else []

theorem positions_S₂ (b : SBinding) (k : Nat) (c : Sem) :
    (S₂ b k c).positions = [.bind 0 0, .temp 0 0] := by
  simp [S₂, SState.positions]

theorem holderOf_S₂ (b : SBinding) (k : Nat) (c : Sem) : (S₂ b k c).holderOf k = some (.temp 0 0) := by
  unfold SState.holderOf
  rw [positions_S₂]
  simp [S₂]

/-- A number is a member of `Nat`. -/
theorem mem_nat (R : DataRead) (m : Nat) : Sem.el0 Nat m ∈ₛ[R] TyM.nat := ⟨m, rfl⟩

/-- A meaning read as a number is a member of `Nat`, and one that reads as none is not. -/
theorem mem_nat_of_as {R : DataRead} {v : Sem} {x : Nat} (h : v.as Nat = some x) : v ∈ₛ[R] TyM.nat := by
  cases v with
  | el0 B b =>
    simp only [Sem.as] at h
    split at h
    · next hB => subst hB; cases h; exact ⟨b, rfl⟩
    · cases h
  | _ => cases h

theorem not_mem_nat_of_as {R : DataRead} {v : Sem} (h : v.as Nat = none) : ¬ v ∈ₛ[R] TyM.nat := by
  rintro ⟨a, rfl⟩
  simp [Sem.as, Code0.enc] at h

/-- The strict call's test at `S₂`: the borrow passed at `σ1`'s borrow parameter is live and holds
`Nat`, the parameter's content type. -/
theorem borrowArgs_S₂ (R : DataRead) (F : GCar) (n : Nat) (b : SBinding) (k : Nat) (c : Sem)
    (hb : b.ty.m = TyM.nat) :
    BorrowArgsTyped R (Sem.el0 GCar F, TyS.plain (.t0 GCar (.pi GCar telG)))
      [(Sem.el0 Nat n, { b.ty with label := some k })] (S₂ b k c) := by
  have hr : telRefsL (lvl0 R) telG [Sem.el0 Nat n] = [true] := by
    simp [telRefsL, telG, dec_nat_el0 R]
  intro i l h
  simp only [refLabelsOf, refsOf, TyS.plain, List.map_cons, List.map_nil, hr, List.zip_cons_cons,
    List.zip_nil_right, List.filter_cons_of_pos, List.filter_nil] at h
  cases i with
  | succ i => simp at h
  | zero =>
    simp only [List.map_cons, List.map_nil, List.getElem?_cons_zero, Option.some.injEq] at h
    subst h
    refine ⟨?_, ?_⟩
    · simp only [SState.liveLabels, List.mem_mergeSort, List.mem_filterMap]
      exact ⟨.temp 0 0, by rw [positions_S₂]; simp, by simp [S₂]⟩
    · simp [refTysOf, telRefTysL, telG, TyS.plain, dec_nat_el0 R, S₂, hb]
      rfl

/-- Consuming the borrow's holder: the temp is `moved`, nothing is in the shape. -/
theorem takeLabel_S₂ (b : SBinding) (k : Nat) (c : Sem) :
    (S₂ b k c).takeLabel k
      = { env := [{ binds := [{ b with val := fun φ' => φ' k }], temps := [fun _ => .moved] }],
          shape := fun _ => none, nextLoan := k + 1,
          lent := fun m => if m = k then [⟨.bind 0 0, [], false⟩] else [],
          heldTy := fun m => if m = k then b.ty.m else TyM.err,
          heldMem := fun m => if m = k then c else .err } := by
  simp only [SState.takeLabel, holderOf_S₂]
  simp [S₂, SState.setAt]
  funext p; split <;> simp_all

end Ochr.Meaning.Attack

namespace Ochr.Meaning.Attack

open Ochr.Meaning

/-- The state after the call `σ1(&c1)` on `S₂`: the borrow of `k` consumed (its temp `moved`),
a fresh label `k+1` for the returned borrow, the lent binding reads the backward function at
`k+1`'s final content, the result parked in temp `1` holding `k+1`. -/
noncomputable def S₃ (F : GCar) (n : Nat) (b : SBinding) (k : Nat) (c : Sem) : SState :=
  { env := [{ binds := [{ b with val := fun φ' => match (φ' (k+1)).as Nat with
                                                  | some x => .el0 Nat ((F n).val.2 x).2
                                                  | none => .moved }],
              temps := [fun φ' => match (φ' (k+1)).as Nat with | some _ => .moved | none => .moved,
                        fun _ => Sem.el0 Nat (F n).val.1] }],
    shape := fun p => if p = .temp 0 1 then some (k+1) else none, nextLoan := k + 2, lent := lentA k,
    heldTy := fun m => if m = k + 1 then TyM.nat else if m = k then b.ty.m else TyM.err,
    heldMem := fun m => if m = k + 1 then .el0 Nat (F n).val.1 else if m = k then c else .err }

set_option maxHeartbeats 1000000 in
theorem callOf_S₂ (R : DataRead) (F : GCar) (n : Nat) (b : SBinding) (k : Nat) (c : Sem) :
    callOf R (Sem.el0 GCar F, TyS.plain (.t0 GCar (.pi GCar telG)))
        [(Sem.el0 Nat n, { b.ty with label := some k })] (S₂ b k c)
      = some ((Sem.el0 Nat (F n).val.1, (⟨TyM.nat, some (k+1)⟩ : TyS)), S₃ F n b k c) := by
  have hr : telRefsL (lvl0 R) telG [Sem.el0 Nat n] = [true] := by
    simp [telRefsL, telG, dec_nat_el0 R]
  simp only [callOf, TyS.plain, callOfL, List.map, hr, List.filterMap, List.foldl, List.zip, List.zipWith,
    List.filter, id, Option.map, List.filter_cons_of_pos]
  have hA := applyFnL_G R F n
  rw [takeLabel_S₂, hA]
  simp only [SState.freshLoan, SState.mapVals, SState.pushTempShaped, SState.pushTemp, SState.topIdx,
    List.zipIdx, List.map, List.zip, List.zipWith, Future.updList, List.foldl, List.length, List.modify,
    List.getLast?, Option.some.injEq, List.append, List.modifyTailIdx, List.modifyHead, Nat.add_sub_cancel,
    List.getLast, Future.upd_same, List.modifyTailIdx.go]
  simp only [S₃, SState.setLent, SState.setHeldTy, SState.setHeldMem, List.cons_append, List.nil_append, List.length_cons, List.length_nil,
    Nat.zero_add, Nat.add_assoc, Nat.reduceAdd, Nat.reduceSub, dec_nat_as]
  congr 2
  · -- the frame: the values agree once the decoded content is cased on (the `match`
    -- auxiliaries differ by elaboration site)
    simp only [SState.mk.injEq, List.cons.injEq, SFrame.mk.injEq, SBinding.mk.injEq, and_true, true_and]
    and_intros
    all_goals first
      | rfl
      | (funext φ'; cases (φ' (k+1)).as Nat <;> rfl)
      | (funext φ'; cases (φ' (k+1)).as Nat <;> simp [Future.updList, Future.upd_same])
      | (trace_state; sorry)
  all_goals first
    | (funext m'; simp [lentA]; done)
    | (funext m'; by_cases h1 : m' = k + 1 <;> simp [h1, lvl0]; done)

/-- Level 0's encoding at `Nat`, by definition. -/
theorem lvl0_enc_nat (R : DataRead) (m : Nat) : (lvl0 R).enc Code0.nat m = .el0 Nat m := rfl

end Ochr.Meaning.Attack

namespace Ochr.Meaning.Attack

open Ochr.Meaning

/-- The result's binding: `r : &Nat` holding the returned borrow `k+1`. -/
noncomputable def rBind (F : GCar) (n : Nat) (k : Nat) : SBinding :=
  { ty := ⟨TyM.nat, some (k+1)⟩, val := fun _ => Sem.el0 Nat (F n).val.1 }

/-- The state after `let r = σ1(&c1)`: `r` bound, holding `k+1` (its temp consumed). -/
noncomputable def S₄ (F : GCar) (n : Nat) (b : SBinding) (k : Nat) (c : Sem) : SState :=
  { env := [{ binds := [{ b with val := fun φ' => match (φ' (k+1)).as Nat with
                                                  | some x => .el0 Nat ((F n).val.2 x).2
                                                  | none => .moved },
                        { ty := ⟨TyM.nat, some (k+1)⟩, val := fun _ => .el0 Nat (F n).val.1 }],
              temps := [fun φ' => match (φ' (k+1)).as Nat with | some _ => .moved | none => .moved,
                        fun _ => .moved] }],
    shape := fun p => if p = .bind 0 1 then some (k+1) else none, nextLoan := k + 2, lent := lentA k,
    heldTy := fun m => if m = k + 1 then TyM.nat else if m = k then b.ty.m else TyM.err,
    heldMem := fun m => if m = k + 1 then .el0 Nat (F n).val.1 else if m = k then c else .err }

theorem positions_S₃ (F : GCar) (n : Nat) (b : SBinding) (k : Nat) (c : Sem) :
    (S₃ F n b k c).positions = [.bind 0 0, .temp 0 0, .temp 0 1] := by
  simp [S₃, SState.positions, List.range', List.map]

theorem holderOf_S₃ (F : GCar) (n : Nat) (b : SBinding) (k : Nat) (c : Sem) :
    (S₃ F n b k c).holderOf (k+1) = some (.temp 0 1) := by
  unfold SState.holderOf
  rw [positions_S₃]
  simp [S₃]

theorem pushBindShaped_S₃ (F : GCar) (n : Nat) (b : SBinding) (k : Nat) (c : Sem) :
    pushBindShaped (S₃ F n b k c) (rBind F n k) = S₄ F n b k c := by
  simp only [pushBindShaped, rBind, SState.takeLabel, holderOf_S₃]
  simp only [S₃, S₄, SState.setAt, SState.pushBind, SState.topIdx, List.modify, List.modifyTailIdx,
    List.modifyTailIdx.go, List.modifyHead, List.length_cons, List.length_nil, List.getLast?, List.getLast,
    List.cons_append, List.nil_append, Nat.zero_add, Nat.reduceAdd, Nat.reduceSub]
  congr 1
  funext p; by_cases h : p = .bind 0 1 <;> by_cases h2 : p = .temp 0 1 <;> simp [h, h2]

end Ochr.Meaning.Attack

namespace Ochr.Meaning.Attack

open Ochr.Meaning

theorem positions_S₄ (F : GCar) (n : Nat) (b : SBinding) (k : Nat) (c : Sem) :
    (S₄ F n b k c).positions = [.bind 0 0, .bind 0 1, .temp 0 0, .temp 0 1] := by
  simp [S₄, SState.positions, List.range', List.map]

theorem liveLabels_S₄ (F : GCar) (n : Nat) (b : SBinding) (k : Nat) (c : Sem) :
    (S₄ F n b k c).liveLabels = [k+1] := by
  unfold SState.liveLabels
  rw [positions_S₄]
  simp [S₄]

/-- No borrow is lent at `r` (the returned borrow `k+1` is lent at `c1`). -/
theorem not_reached_r (F : GCar) (n : Nat) (b : SBinding) (k : Nat) (c : Sem) (hit : List Step → Bool) (l : Nat) :
    (S₄ F n b k c).reached (.bind 0 1) hit l = false := by
  simp only [SState.reached, S₄, lentA]
  split <;> (try split) <;> simp

/-- [Access] of `r` ends nothing: `r` holds `k+1`, which is lent at `c1`. -/
theorem access_S₄ (F : GCar) (n : Nat) (b : SBinding) (k : Nat) (c : Sem) (hit : List Step → Bool) :
    (S₄ F n b k c).access (.bind 0 1) hit = S₄ F n b k c := by
  simp [SState.access, liveLabels_S₄, not_reached_r]

/-- `peek(*r)` on `S₄`: the forward value, at `Nat`, the state unchanged. -/
theorem readPlace_deref_r (K : RunCtx) (φ : Future) (F : GCar) (n : Nat) (b : SBinding) (k : Nat) (c : Sem) :
    readPlace K φ (.deref (.var 0)) true (S₄ F n b k c)
      = some ((.el0 Nat (F n).val.1, .plain TyM.nat), S₄ F n b k c) := by
  have hr : resolve (S₄ F n b k c) (.deref (.var 0)) = some (.bind 0 1, [.deref]) := by
    simp [resolve, SState.varPos, SState.topIdx, Ochr.Place.steps, S₄]
  have hw : (Sem.el0 Nat (F n).val.1).whole := by simp [Sem.whole]
  simp only [readPlace, contentOf, hr, access_S₄, bind, Option.bind]
  simp [S₄, SState.tyAt, SState.valAt, Sem.follow, Sem.step, hw]
  rfl

end Ochr.Meaning.Attack

namespace Ochr.Meaning.Attack

open Ochr.Meaning

/-- A binding whose type carries no label is pushed plainly. -/
theorem pushBindShaped_noLabel (s : SState) (b : SBinding) (h : b.ty.label = none) :
    pushBindShaped s b = s.pushBind b := by
  simp [pushBindShaped, h]

end Ochr.Meaning.Attack

namespace Ochr.Meaning.Attack

open Ochr.Meaning

/-- `*r`'s content on `S₄`: the forward value at `Nat`, position `bind 0 1`, one `deref` step. -/
theorem contentOf_deref_r (K : RunCtx) (φ : Future) (F : GCar) (n : Nat) (b : SBinding) (k : Nat) (c : Sem) :
    contentOf K φ (.deref (.var 0)) (S₄ F n b k c)
      = some ((.el0 Nat (F n).val.1, .plain TyM.nat, .bind 0 1, [.deref]), S₄ F n b k c) := by
  have hr : resolve (S₄ F n b k c) (.deref (.var 0)) = some (.bind 0 1, [.deref]) := by
    simp [resolve, SState.varPos, SState.topIdx, Ochr.Place.steps, S₄]
  simp only [contentOf, hr, access_S₄]
  simp [S₄, SState.tyAt, SState.valAt, Sem.follow, Sem.step]
  rfl

theorem resolve_deref_r (F : GCar) (n : Nat) (b : SBinding) (k : Nat) (c : Sem) :
    resolve (S₄ F n b k c) (.deref (.var 0)) = some (.bind 0 1, [.deref]) := by
  simp [resolve, SState.varPos, SState.topIdx, Ochr.Place.steps, S₄]

/-- The state after `*r := w` on `S₄`: `r` holds `w`. -/
noncomputable def S₅ (F : GCar) (n : Nat) (b : SBinding) (k : Nat) (c : Sem) (w : Sem) : SState :=
  { env := [{ binds := [{ b with val := fun φ' => match (φ' (k+1)).as Nat with
                                                  | some x => .el0 Nat ((F n).val.2 x).2
                                                  | none => .moved },
                        { ty := ⟨TyM.nat, some (k+1)⟩, val := fun _ => w }],
              temps := [fun φ' => match (φ' (k+1)).as Nat with | some _ => .moved | none => .moved,
                        fun _ => .moved] }],
    shape := fun p => if p = .bind 0 1 then some (k+1) else none, nextLoan := k + 2, lent := lentA k,
    heldTy := fun m => if m = k + 1 then TyM.nat else if m = k then b.ty.m else TyM.err,
    heldMem := fun m => if m = k + 1 then .el0 Nat (F n).val.1 else if m = k then c else .err }

theorem setContent_deref_r (K : RunCtx) (φ : Future) (F : GCar) (n : Nat) (b : SBinding) (k : Nat) (c : Sem) (w : Sem) :
    setContent K φ (.bind 0 1) [.deref] w (S₄ F n b k c) = some (⟨⟩, S₅ F n b k c w) := by
  simp only [setContent, updAt_deref, updAt_nil]
  simp [S₄, S₅, SState.setAt, SState.tyAt, SState.valAt, List.modify, List.modifyTailIdx, List.modifyTailIdx.go,
    List.modifyHead]

end Ochr.Meaning.Attack

namespace Ochr.Meaning.Attack

open Ochr.Meaning

theorem positions_S₅ (F : GCar) (n : Nat) (b : SBinding) (k : Nat) (c : Sem) (w : Sem) :
    (S₅ F n b k c w).positions = [.bind 0 0, .bind 0 1, .temp 0 0, .temp 0 1] := by
  simp [S₅, SState.positions, List.range', List.map]

theorem liveLabels_S₅ (F : GCar) (n : Nat) (b : SBinding) (k : Nat) (c : Sem) (w : Sem) :
    (S₅ F n b k c w).liveLabels = [k+1] := by
  unfold SState.liveLabels
  rw [positions_S₅]
  simp [S₅]

/-- `c1` is lent to `k+1`, the returned borrow: a fill at `c1` (the call's [Lend]). -/
theorem reached_c1 (F : GCar) (n : Nat) (b : SBinding) (k : Nat) (c : Sem) (w : Sem) (hit : List Step → Bool) (hh : hit [] = true) :
    (S₅ F n b k c w).reached (.bind 0 0) hit (k+1) = true := by
  simp [SState.reached, S₅, lentA, hh]

end Ochr.Meaning.Attack

namespace Ochr.Meaning.Attack

open Ochr.Meaning

/-- The state after [Access] of `c1` on `S₅`: `r`'s borrow ends, fixing `k+1`'s final content to
`w`; `c1` now reads the backward function at `w`, `r` is forgotten, nothing is live. -/
noncomputable def S₆ (F : GCar) (n : Nat) (b : SBinding) (k : Nat) (c : Sem) (w : Sem) : SState :=
  { env := [{ binds := [{ b with val := fun _ => match w.as Nat with
                                                  | some x => .el0 Nat ((F n).val.2 x).2
                                                  | none => .moved },
                        { ty := ⟨TyM.nat, some (k+1)⟩, val := fun _ => .moved }],
              temps := [fun _ => match w.as Nat with | some _ => .moved | none => .moved,
                        fun _ => .moved] }],
    shape := fun _ => none, nextLoan := k + 2, lent := (S₅ F n b k c w).relend (k+1) (.bind 0 1),
    heldTy := (S₅ F n b k c w).heldTy, heldMem := (S₅ F n b k c w).heldMem }

theorem endLabel_S₅ (F : GCar) (n : Nat) (b : SBinding) (k : Nat) (c : Sem) (w : Sem) :
    (S₅ F n b k c w).endLabel (k+1) = S₆ F n b k c w := by
  unfold SState.endLabel
  rw [positions_S₅]
  simp only [S₅, S₆, Mean.semEnd, SState.toMean, SState.mapVals, SState.valAt, List.zipIdx, List.map,
    List.find?, Future.upd_same, reduceCtorEq, if_true, if_false, decide_eq_true_eq, decide_true, decide_false,
    List.getElem?_cons_zero, List.getElem?_cons_succ, List.getElem?_nil, Option.bind_some, Option.bind_none,
    Pos.bind.injEq, Pos.temp.injEq, Nat.reduceEqDiff, and_false, false_and, and_true, true_and, Option.some.injEq,
    decide_eq_false_iff_not, not_false_eq_true, ite_true, ite_false, Nat.zero_ne_one, Nat.one_ne_zero]
  first
    | (simp [Future.upd]; done)
    | (congr 1; all_goals first
        | rfl
        | (simp only [List.cons.injEq, SFrame.mk.injEq, SBinding.mk.injEq, and_true, true_and]
           and_intros
           all_goals first
             | rfl
             | (funext φ'; simp [Future.upd]; cases w.as Nat <;> rfl)
             | (funext φ'; simp [Future.upd])
             | (trace_state; sorry))
        | (funext p; simp)
        | (trace_state; sorry))
    | (trace_state; sorry)

end Ochr.Meaning.Attack

namespace Ochr.Meaning.Attack

open Ochr.Meaning

/-- [Access] of `c1` on `S₅`: the one live label `k+1` is read by `c1`, so it ends. -/
theorem access_S₅ (F : GCar) (n : Nat) (b : SBinding) (k : Nat) (c : Sem) (w : Sem) (hit : List Step → Bool)
    (hh : hit [] = true) :
    (S₅ F n b k c w).access (.bind 0 0) hit = S₆ F n b k c w := by
  have hd := reached_c1 F n b k c w hit hh
  have h6 : (S₆ F n b k c w).liveLabels = [] := by
    have h0 : ∀ l : List Pos, List.filterMap (fun _ : Pos => (none : Option Nat)) l = [] := by
      intro l; induction l with
      | nil => rfl
      | cons _ _ ih => simpa [List.filterMap_cons] using ih
    simp [SState.liveLabels, S₆, h0]
  simp [SState.access, liveLabels_S₅, hd, endLabel_S₅, h6]

/-- `peek(c1)` on `S₅`: the backward function's component for `c1` at the written value, when it
is a number; `err` (not whole, so the read fails) otherwise. -/
theorem readPlace_c1 (K : RunCtx) (φ : Future) (F : GCar) (n : Nat) (b : SBinding) (k : Nat) (c : Sem) (w : Sem)
    (hb : b.ty = .plain TyM.nat) :
    readPlace K φ (.var 1) true (S₅ F n b k c w)
      = match w.as Nat with
        | some x => some ((.el0 Nat ((F n).val.2 x).2, .plain TyM.nat), S₆ F n b k c w)
        | none => none := by
  have hr : resolve (S₅ F n b k c w) (.var 1) = some (.bind 0 0, []) := by
    simp [resolve, SState.varPos, SState.topIdx, Ochr.Place.steps, S₅]
  have h6 : (S₆ F n b k c w).typedFuture φ = φ := by
    have h0 : ∀ l : List Pos, List.filterMap (fun _ : Pos => (none : Option Nat)) l = [] := by
      intro l; induction l with
      | nil => rfl
      | cons _ _ ih => simpa [List.filterMap_cons] using ih
    funext l; simp [SState.typedFuture, SState.liveLabels, S₆, h0]
  simp only [readPlace, contentOf, hr, access_S₅ F n b k c w (dataHit []) rfl, h6, bind, Option.bind]
  simp only [S₆, SState.tyAt, SState.valAt, Sem.follow, dec_nat_as, hb]
  cases w.as Nat <;> simp [Sem.whole] <;> rfl

end Ochr.Meaning.Attack
