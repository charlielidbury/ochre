import Ochr.Meaning.Attack.RunEqs
import Ochr.Meaning.Regress.CE4_flipped
/-!
# The reference run fails on two accepted programs (archived record; NOT built: kernel-checked
# against spine 1d94e4eb, axioms propext, Classical.choice, Quot.sound)

`Regress/AdequacyProbes.lean` asserts that the checker accepts `Twice` and `ErasedLet`. Here the
reference run of 1d94e4eb is shown to fail on their shapes, for every run context whose declared
reading of the variable is not a copy type (every function type, and `List(Nat)`):

* `call_twice_fails`: `f(f(a))`, `f` a variable. The outer call's head read moves `f` out
  (`run f` is `readPlace … false`); the inner call's head read then finds `moved`.
* `stmt_let_moves`: `(let y = x; ()); x`. The `let` moves `x` whatever `Decisions.flags` says of
  it, since the run asks `flags` only of calls; the read of `x` then finds `moved`. (The accepted
  program is `let h : True = (let y = x; refl); x`: the same mechanism under an annotation.)

Both are definition faults of the reference run, fixed after 1d94e4eb (docs/31 D19); the flipped,
positive checks are `Regress/Adequacy_flipped.lean` (built).
-/
open Ochr Ochr.Meaning Ochr.Meaning.Attack Ochr.Meaning.Regress.CE4flip

namespace HeadCE
variable (K : RunCtx) (ρ : Assignment) (φ : Future)

/-- One frame holding one binding, no holder. -/
def one (b : SBinding) (k : Nat) : SState := { env := [{ binds := [b] }], shape := fun _ => none, nextLoan := k }

theorem scope_one (b : SBinding) (k : Nat) : scopeOf (one b k) = [b.decl] := by
  simp [scopeOf, one]

/-- Reading `var 0` by move: the value comes back and the binding holds `moved`. -/
theorem read_moves (b : SBinding) (k : Nat) (hw : (b.val φ).whole) :
    readPlace K φ (.var 0) false (one b k)
      = some ((b.val φ, { b.ty with label := none }), one { b with val := fun _ => .moved } k) := by
  rw [readPlace_of φ K (.var 0) false (one b k) _ _ _ _ _ (contentOf_var0_one K φ k b)]
  simp only [hw, not_true_eq_false, if_false, Bool.false_eq_true, List.isEmpty_nil, if_true]
  simp [setContent, one, SState.tyAt, SState.valAt, SState.setAt, updAt_nil, Bind.bind, Option.bind]

/-- Reading `var 0` when it holds `moved` fails. -/
theorem read_moved_fails (b : SBinding) (k : Nat) (copy : Bool) (hm : b.val φ = .moved) :
    readPlace K φ (.var 0) copy (one b k) = none := by
  rw [readPlace_of φ K (.var 0) copy (one b k) _ _ _ _ _ (contentOf_var0_one K φ k b)]
  simp [hm, Sem.whole]
end HeadCE

namespace HeadCE
variable (K : RunCtx) (ρ : Assignment) (φ : Future)

/-- A call whose head is `var 0`, a place whose declared reading is not a copy type, read when it
holds `moved`: the call fails, statement or not. -/
theorem call_moved_head_fails (b : SBinding) (k : Nat) (hint : TyS) (args : List Term) (hd : Bool)
    (hm : b.val φ = .moved) :
    run K ρ φ hint (.call (.place (.var 0)) args hd) (one b k) = none := by
  have h1 : run K ρ φ (.plain .err) (.place (.var 0)) (one b k) = none := by
    rw [run_place]; exact read_moved_fails K φ b k _ hm
  rw [run]
  simp only [SM.onCopy, bind, h1]
  split <;> rfl

/-- **The head is consumed.** `f(f(a))` with `f` the variable `var 0`, at a declared reading that is
not a copy type (every function type): the reference run fails, whatever `f` holds. The outer
call's head read moves `f` out; the inner call's head read then finds `moved`. The checker reads
a call's head in place (D53 (e)) and accepts `Twice (f : Π(n : Nat). Nat) (n : Nat) : Nat := f(f(n))`. -/
theorem call_twice_fails (b : SBinding) (k : Nat) (hint : TyS) (a : Term) (hd hd' : Bool)
    (hc : K.D.copy (K.D.placeDecl [b.decl] (.var 0)) = false) :
    run K ρ φ hint (.call (.place (.var 0)) [.call (.place (.var 0)) [a] hd'] hd) (one b k) = none := by
  by_cases hw : (b.val φ).whole
  · have h1 : run K ρ φ (.plain .err) (.place (.var 0)) (one b k)
        = some ((b.val φ, { b.ty with label := none }), one { b with val := fun _ => .moved } k) := by
      rw [run_place, scope_one, hc]; exact read_moves K φ b k hw
    have h2 : ∀ T, run K ρ φ T (.call (.place (.var 0)) [a] hd') (one { b with val := fun _ => .moved } k) = none :=
      fun T => call_moved_head_fails K ρ φ _ k T [a] hd' rfl
    rw [run]
    simp only [SM.onCopy, bind, h1, runArgs, h2]
    split <;> rfl
  · have h1 : run K ρ φ (.plain .err) (.place (.var 0)) (one b k) = none := by
      rw [run_place, readPlace_of φ K (.var 0) _ (one b k) _ _ _ _ _ (contentOf_var0_one K φ k b)]
      simp [hw]
    rw [run]
    simp only [SM.onCopy, bind, h1]
    split <;> rfl
end HeadCE

namespace HeadCE
variable (K : RunCtx) (ρ : Assignment) (φ : Future)

/-- **A statement that is not a call runs in place.** `(let y = x; ()); x` with `x` the variable
`var 0` at a declared reading that is not a copy type: the reference run fails, whatever
`K.D.flags` says of the `let` (the run asks `flags` only of calls). The checker runs an erased
term on a private copy, so it accepts `let h : True = (let y = x; refl); x`. -/
theorem stmt_let_moves (b : SBinding) (k : Nat) (hint : TyS) (y : Hint)
    (hc : K.D.copy (K.D.placeDecl [b.decl] (.var 0)) = false) :
    run K ρ φ hint (.seq (.letIn y (.place (.var 0)) .tt) (.place (.var 0))) (one b k) = none := by
  by_cases hw : (b.val φ).whole
  · have h1 : run K ρ φ (.plain .err) (.place (.var 0)) (one b k)
        = some ((b.val φ, { b.ty with label := none }), one { b with val := fun _ => .moved } k) := by
      rw [run_place, scope_one, hc]; exact read_moves K φ b k hw
    have h2 : run K ρ φ (.plain .err) (.letIn y (.place (.var 0)) .tt) (one b k)
        = some ((.el0 Unit (), .plain (.ty0 Unit)), one { b with val := fun _ => .moved } k) := by
      rw [Attack.run_letIn, h1]
      simp [run, pushBindShaped, one, SState.pushBind, SState.topIdx, SState.dropLast, pure, Option.bind]
    have h3 : ∀ T, run K ρ φ T (.place (.var 0)) (one { b with val := fun _ => .moved } k) = none := by
      intro T; rw [run_place]; exact read_moved_fails K φ _ k _ rfl
    rw [run_seq]
    simp [bind, h2, h3]
  · have h1 : run K ρ φ (.plain .err) (.place (.var 0)) (one b k) = none := by
      rw [run_place, readPlace_of φ K (.var 0) _ (one b k) _ _ _ _ _ (contentOf_var0_one K φ k b)]
      simp [hw]
    rw [run_seq]
    simp [bind, Attack.run_letIn, h1]
end HeadCE
