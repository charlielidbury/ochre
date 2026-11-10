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
