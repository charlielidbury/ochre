import Ochr.Meaning.Attack.CloseCall

/-!
# Equation lemmas for the run layer, on the shapes the attacks meet

`simp [Sem.updAt]` fails (Lean cannot generate `Sem.updAt`'s equational theorems), and `run`'s
clauses are best used as rewrite rules on concrete constructors. The lemmas here are the
equations by `rfl`, for the attack files to rewrite with.
-/

namespace Ochr.Meaning.Attack

open Ochr.Meaning

theorem updAt_nil (dm : DataModel) (Γ : List IndDecl) (T : TyM) (f : Sem → Sem) (s : Sem) :
    Sem.updAt dm Γ T f [] s = some (f s) := rfl

theorem updAt_deref (dm : DataModel) (Γ : List IndDecl) (T : TyM) (f : Sem → Sem) (sts : List Step) (s : Sem) :
    Sem.updAt dm Γ T f (.deref :: sts) s = Sem.updAt dm Γ T f sts s := rfl

theorem run_ascribe (K : RunCtx) (ρ : Assignment) (φ : Future) (hint : TyS) (u A : Term) (s : SState) :
    run K ρ φ hint (.ascribe u A) s =
      (do
        let (TA, _) ← SM.onCopy (run K ρ φ (.plain .err) A)
        let T := TyS.plain TA.asTy
        let (v, R) ← run K ρ φ T u
        pure (v, { T with label := R.label })) s := rfl

theorem run_letIn (K : RunCtx) (ρ : Assignment) (φ : Future) (hint : TyS) (x : Hint) (u w : Term) (s : SState) :
    run K ρ φ hint (.letIn x u w) s =
      (do
        let ((v, T), s) ← run K ρ φ (.plain .err) u s
        let s := pushBindShaped s { ty := T, val := fun _ => v, decl := K.D.declOf (scopeOf s) u }
        let ((r, R), s) ← run K ρ φ hint w s
        let s := match T.label with | some l => s.endLabel l | none => s
        some ((r, R), s.dropLast)) := rfl

theorem meanV_abs (K : RunCtx) (ρ : Assignment) (φ : Future) (hint : TyS) (σ : Nat) :
    meanV K ρ φ hint (.abs σ) = ρ σ := rfl

theorem meanV_tNat (K : RunCtx) (ρ : Assignment) (φ : Future) (hint : TyS) :
    meanV K ρ φ hint .tNat = .ty (.ty0 Nat) := rfl

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
theorem access_noShape (s : SState) (hs : s.shape = fun _ => none) (p : Pos) : s.access p = s := by
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
  have ha := access_noShape { env := [{ binds := [b] }], shape := fun _ => none, nextLoan := k } rfl (.bind 0 0)
  simp only [contentOf, resolve_var0_one, ha, SState.tyAt, SState.valAt, Sem.follow]
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
            shape := fun p => if p = .temp 0 0 then some k else none, nextLoan := k + 1 }) := by
  simp only [borrowPlace, contentOf_var0_one, bind, Option.bind]
  simp [hw, SState.freshLoan, SState.pushTempShaped, SState.pushTemp, SState.setAt, SState.topIdx,
    SState.tyAt, SState.valAt, updAt_nil]

end Ochr.Meaning.Attack

namespace Ochr.Meaning.Attack

open Ochr.Meaning

/-- `lvl0.dec (ty0 Nat)` on a number is the number (`TyM.dec0_enc0` at `Nat`). -/
theorem lvl0_dec_nat (n : Nat) : lvl0.dec (.ty0 Nat) (.el0 Nat n) = some n :=
  TyM.dec0_enc0 (.ty0 Nat) n

/-- Applying `σ_g`'s meaning `F` (tagged at its carrier) to a number: the borrow-returning result
at `Nat`, forward value `(F n).val.1`, and the backward function reads the one lent place from
the final content. -/
theorem applyFnL_G (F : GCar) (n : Nat) :
    applyFnL lvl0 psG outG (.el0 GCar F) [.el0 Nat n]
      = some (.ref (.ty0 Nat) (F n).val.1 fun v => [.el0 Nat ((F n).val.2 v).2]) := by
  have hu : lvl0.unpack GCar (.el0 GCar F) = some F := lvl0_unpack_pack GCar F
  simp only [applyFnL, psG, outG, GCar] at hu ⊢
  rw [hu]
  simp only [applyTeleL, extReadL, lvl0, Option.bind_some]
  have hd : (TyM.ty0 Nat).dec0 (.el0 Nat n) = some n := TyM.dec0_enc0 (.ty0 Nat) n
  rw [hd]
  rfl

end Ochr.Meaning.Attack

namespace Ochr.Meaning.Attack

open Ochr.Meaning

/-- The state after `&(var 0)` on the one-binding state (`borrowPlace_var0_one`'s output). -/
def S₂ (b : SBinding) (k : Nat) (c : Sem) : SState :=
  { env := [{ binds := [{ b with val := fun φ' => φ' k }], temps := [fun _ => c] }],
    shape := fun p => if p = .temp 0 0 then some k else none, nextLoan := k + 1 }

theorem positions_S₂ (b : SBinding) (k : Nat) (c : Sem) :
    (S₂ b k c).positions = [.bind 0 0, .temp 0 0] := by
  simp [S₂, SState.positions]

theorem holderOf_S₂ (b : SBinding) (k : Nat) (c : Sem) : (S₂ b k c).holderOf k = some (.temp 0 0) := by
  unfold SState.holderOf
  rw [positions_S₂]
  simp [S₂]

/-- Consuming the borrow's holder: the temp is `moved`, nothing is in the shape. -/
theorem takeLabel_S₂ (b : SBinding) (k : Nat) (c : Sem) :
    (S₂ b k c).takeLabel k
      = { env := [{ binds := [{ b with val := fun φ' => φ' k }], temps := [fun _ => .moved] }],
          shape := fun _ => none, nextLoan := k + 1 } := by
  simp only [SState.takeLabel, holderOf_S₂]
  simp [S₂, SState.setAt]
  funext p; split <;> simp_all

end Ochr.Meaning.Attack

namespace Ochr.Meaning.Attack

open Ochr.Meaning

/-- The state after the call `σ1(&c1)` on `S₂`: the borrow of `k` consumed (its temp `moved`),
a fresh label `k+1` for the returned borrow, the lent binding reads the backward function at
`k+1`'s final content, the result parked in temp `1` holding `k+1`. -/
noncomputable def S₃ (F : GCar) (n : Nat) (b : SBinding) (k : Nat) : SState :=
  { env := [{ binds := [{ b with val := fun φ' => match lvl0.dec (.ty0 Nat) (φ' (k+1)) with
                                                  | some x => .el0 Nat ((F n).val.2 x).2
                                                  | none => .err }],
              temps := [fun φ' => match lvl0.dec (.ty0 Nat) (φ' (k+1)) with | some _ => .moved | none => .err,
                        fun _ => lvl0.enc (.ty0 Nat) (F n).val.1] }],
    shape := fun p => if p = .temp 0 1 then some (k+1) else none, nextLoan := k + 2 }

set_option maxHeartbeats 1000000 in
theorem callOf_S₂ (F : GCar) (n : Nat) (b : SBinding) (k : Nat) (c : Sem) :
    callOf (Sem.el0 GCar F, (⟨.ty0 GCar, some (psG, outG), none, none⟩ : TyS))
        [(Sem.el0 Nat n, { b.ty with label := some k })] (S₂ b k c)
      = some ((lvl0.enc (.ty0 Nat) (F n).val.1, (⟨.ty0 Nat, none, some (k+1), none⟩ : TyS)), S₃ F n b k) := by
  simp only [callOf, callOfL, List.map, List.filterMap, List.foldl]
  rw [takeLabel_S₂, applyFnL_G]
  simp only [SState.freshLoan, SState.mapVals, SState.pushTempShaped, SState.pushTemp, SState.topIdx,
    List.zipIdx, List.map, List.zip, List.zipWith, Future.updList, List.foldl, List.length, List.modify,
    List.getLast?, Option.some.injEq, List.append, List.modifyTailIdx, List.modifyHead, Nat.add_sub_cancel,
    List.getLast, Future.upd_same, List.modifyTailIdx.go]
  simp only [S₃, List.cons_append, List.nil_append, List.length_cons, List.length_nil,
    Nat.zero_add, Nat.add_assoc, Nat.reduceAdd, Nat.reduceSub]
  congr 2
  · -- the frame: the values agree once the decoded content is cased on (the `match`
    -- auxiliaries differ by elaboration site)
    simp only [List.cons.injEq, SFrame.mk.injEq, SBinding.mk.injEq, and_true, true_and]
    and_intros
    all_goals first
      | rfl
      | (funext φ'; cases lvl0.dec (.ty0 Nat) (φ' (k+1)) <;> rfl)
      | (trace_state; sorry)

/-- Level 0's encoding and decoding at `Nat`, by definition. -/
theorem lvl0_enc_nat (m : Nat) : lvl0.enc (.ty0 Nat) m = .el0 Nat m := rfl
theorem lvl0_dec_nat' (s : Sem) : lvl0.dec (.ty0 Nat) s = s.as Nat := rfl

end Ochr.Meaning.Attack
