import Ochr.Meaning.Regress.Adequacy_flipped
/-!
# A function parameter cannot be called (archived record; NOT built: kernel-checked against the
# commit that fixed D19's R3, axioms propext, Classical.choice, Quot.sound)

`call_param_no_shape`: a call whose head is a variable bound at a type with no Π-shape, and which
is not a proof call, fails in the reference run, since `callOf` has no shape to apply the callee
along. The `.fix` clause binds every parameter at `.plain (dom …)` (a borrow parameter at
`⟨dom …, none, some l, none⟩`), which has no shape: `PiParam` carries a parameter's type as a
`TyM` and nothing else. So the body of every function that calls a function parameter has no
reference run. `Twice (f : Π(n : Nat). Nat) (n : Nat) : Nat := f(f(n))` is accepted by the checker
(`Regress/AdequacyProbes.lean`).

A definition fault of the reference run (docs/31 D19, R6), open: `PiParam` needs the parameter's
Π-shape as a function of the earlier parameters, read off its domain term's run, and `extendBy`
must bind the earlier parameters at their types and shapes for the later domain terms.
-/
open Ochr Ochr.Meaning Ochr.Meaning.Attack Ochr.Meaning.Regress.CE4flip Ochr.Meaning.Regress.AdequacyFlip

namespace NoShapeCE
variable (K : RunCtx) (ρ : Assignment) (φ : Future)

/-- A statement position fails where its run fails. -/
theorem stmtIf_none (b : Bool) (x : SM Res) (s : SState) (h : x s = none) : SM.stmtIf b x s = none := by
  cases b <;> simp [SM.stmtIf, h]

/-- **A function parameter cannot be called.** A call whose head is a variable bound at a type
with no Π-shape, and which is not a proof call, fails in the reference run: `callOf` has no shape
to apply the callee along. The `.fix` clause binds every parameter at `.plain (dom …)`, which has
no shape, so the body of `Twice (f : Π(n : Nat). Nat) (n : Nat) : Nat := f(f(n))`, and of every
function that calls a function parameter, has no reference run. -/
theorem call_param_no_shape (b : SBinding) (k : Nat) (hint : TyS) (args : List Term) (hd : Bool)
    (hb : b.ty.shape = none)
    (hpf : (K.D.flags (scopeOf (one b k)) (.call (.place (.var 0)) args hd)).2 = false) :
    run K ρ φ hint (.call (.place (.var 0)) args hd) (one b k) = none := by
  rw [run]
  apply stmtIf_none
  by_cases hw : (b.val φ).whole
  · rw [SM.bind_apply, head_in_place K φ b k _ hw]
    dsimp only
    rw [SM.bind_apply]
    cases hr : runArgs K ρ φ _ _ 0 [] args (one b k) with
    | none => rfl
    | some x =>
      obtain ⟨as, s₂⟩ := x
      dsimp only
      rw [hpf]
      simp [callOf, hb]
  · have h1 : SM.headOf (.place (.var 0)) (fun p => readPlace K φ p true)
        (run K ρ φ (.plain .err) (.place (.var 0))) (one b k) = none := by
      show readPlace K φ (.var 0) true (one b k) = none
      rw [readPlace_of φ K (.var 0) true (one b k) _ _ _ _ _ (contentOf_var0_one K φ k b)]
      simp [hw]
    rw [SM.bind_apply, h1]
end NoShapeCE
