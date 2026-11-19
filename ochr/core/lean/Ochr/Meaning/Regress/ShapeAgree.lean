import Ochr.Meaning.Steps.Statements
import Ochr.Meaning.RunSubst
import Ochr.Meaning.RunCongr

/-!
# Where a function type's shape does NOT survive (docs/31 D22; third lead, 2026-11-19; built)

Prerequisite (a) of the migration to the simulation form (docs/31 D20 item 1): "a Π-type's shape
does not depend on where it is read", so that a binding's shape in the reference state (made by
the run) is the shape the checker's stored type reads as (`Value.tyS`, through `tyShape`). In that
blanket form it is FALSE, in both directions. The lemmas here are the kernel-checked halves; the
checker's side of each (the program is accepted) is asserted by `Regress/ShapeProbes.lean`.

* **The reference has none where the checker's stored type has one.** `call_noShape`: a call's
  result never has a Π-shape or a data component, whatever the callee and the state
  (`callOf` types its result `.plain B`). `tyShape_tPi`: a stored Π-type value of a Π-term always
  has one. So after `let a = Adder(n)` the checker's binding `a : Π(m : Nat). Nat` has a shape and
  the reference's has none, and after `(f : Fn(Nat))`, with `Fn(A) := Π(x : A). A` computed by a
  call, the same holds of the parameter (probes `UseAdder`, `UseFn`: both accepted).
* **The reference has one where the checker's stored type has none.** `pi_shape`: the run of a
  Π-term returns the Π's shape in its result's TYPE, whose meaning is a universe; `tyShape_sort`: a
  stored universe has no shape. So after `let T = Π(n : Nat). Nat` the reference's binding `T`
  has a shape and the checker's `T : Type` read as a reference state has none, and from that state
  `let g : T = f; g(n)` fails (probe `Alias`: accepted).

Both are faults of the model (the structure of a value is carried beside its meaning, in the
type the run returns, and three clauses drop it), not of the checker.
-/

namespace Ochr.Meaning.Regress.ShapeAgree
open Ochr Ochr.Meaning

variable (K : RunCtx) (ρ : Assignment) (φ : Future)

/-- An applied callee's result has no Π-shape and no data, at every level. -/
theorem callOfL_noShape.{u} (L : Lvl.{u}) (ps : List PiParam) (out : PiOut) (fv : Sem) (args : List Res)
    (s s' : SState) (r : Res) (h : callOfL L ps out fv args s = some (r, s')) :
    r.2.shape = none ∧ r.2.data = none := by
  unfold callOfL at h
  dsimp only at h
  generalize applyFnL L ps out fv (args.map (·.1)) = a at h
  rcases a with _ | (_ | _)
  · cases h
  · simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact ⟨rfl, rfl⟩
  · simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact ⟨rfl, rfl⟩

theorem callOf_noShape (fv : Res) (args : List Res) (s s' : SState) (r : Res)
    (h : callOf fv args s = some (r, s')) : r.2.shape = none ∧ r.2.data = none := by
  unfold callOf at h
  split at h
  · split at h
    · exact callOfL_noShape _ _ _ _ _ _ _ _ h
    · exact callOfL_noShape _ _ _ _ _ _ _ _ h
    · exact callOfL_noShape _ _ _ _ _ _ _ _ h
    · cases h
  · cases h

/-- An erased term's result keeps "no shape, no data" if the term's own run has it. -/
theorem erasedIf_noShape (fl : Bool × Bool) (x : SM Res) (s s' : SState) (r : Res)
    (hx : ∀ r s', x s = some (r, s') → r.2.shape = none ∧ r.2.data = none)
    (h : SM.erasedIf fl x s = some (r, s')) : r.2.shape = none ∧ r.2.data = none := by
  unfold SM.erasedIf at h
  split at h
  · simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact ⟨rfl, rfl⟩
  · rcases SM.stmtIf_some h with ⟨-, h⟩ | ⟨-, -, -, r₀, s₀, h₀, rfl⟩
    · exact hx _ _ h
    · exact hx r₀ s₀ h₀

/-- **A call's result has no Π-shape and no data**, whatever the callee, the arguments and the
state. So a function returned by a call cannot be called, and a parameter whose type is a call of
a type function is bound with no shape. -/
theorem call_noShape (hint : TyS) (f : Term) (args : List Term) (hd : Bool) (s s' : SState) (r : Res)
    (h : run K ρ φ hint (.call f args hd) s = some (r, s')) : r.2.shape = none ∧ r.2.data = none := by
  rw [run] at h
  refine erasedIf_noShape _ _ _ _ _ (fun r s' hx => ?_) h
  simp only [Bind.bind] at hx
  split at hx
  · split at hx
    · exact callOf_noShape _ _ _ _ _ hx
    · cases hx
  · cases hx

/-- A stored Π-type value of a Π-term has a shape, at every assignment and future. -/
theorem tyShape_tPi (caps : List Value) (hs : List Hint) (ds : List Term) (c : Term) (rd : List (DeclInfo × Value)) :
    (tyShape K ρ φ (.tPi caps (.pi hs ds c) rd)).isSome = true := by
  rw [tyShape]
  cases c <;> simp [piShapeOf]

/-- **So the two never agree on a call's result**: the type the checker stores for a call that
returns a function is a Π-type value with a shape, and the reference's result has none. -/
theorem call_shape_ne (hint : TyS) (f : Term) (args : List Term) (hd : Bool) (s s' : SState) (r : Res)
    (h : run K ρ φ hint (.call f args hd) s = some (r, s')) (ψ : Future)
    (caps : List Value) (hs : List Hint) (ds : List Term) (c : Term) (rd : List (DeclInfo × Value)) :
    r.2.shape ≠ tyShape K ρ ψ (.tPi caps (.pi hs ds c) rd) := by
  intro e
  have h1 := (call_noShape K ρ φ hint f args hd s s' r h).1
  have h2 := tyShape_tPi K ρ ψ caps hs ds c rd
  rw [← e, h1] at h2
  cases h2

/-- The run of a Π-term returns the Π's shape in the type of its result, a universe. -/
theorem pi_shape (hint : TyS) (hs : List Hint) (ds : List Term) (c : Term) (s : SState) :
    ∃ r, run K ρ φ hint (.pi hs ds c) s = some (r, s) ∧ r.2.shape.isSome = true ∧
      r.2.m = .univ (K.D.piSort (scopeOf s) (.pi hs ds c)) := by
  rw [run_pi_def]
  exact ⟨_, rfl, rfl, rfl⟩

/-- A stored universe has no shape: a binding `T : Type` of a checker state, read as a reference
state, has none, whatever type `T` holds. -/
theorem tyShape_sort (l : Nat) : tyShape K ρ φ (.sort l) = none := by
  rw [tyShape]
  · intro _ _ _ h; cases h
  · intro _ h; cases h

theorem tyS_sort_shape (l : Nat) : (Value.tyS K.dm K.M K.Γ ρ (.sort l)).shape = none := by
  show tyShape K ρ noFuture (.sort l) = none
  exact tyShape_sort K ρ noFuture l

/-! ## What IS proved: the future does not matter -/

/-- A type value that holds no loan reads as the same type, with the same shape and data, at
every future. (So the checker's reading at the constant future, `Value.tyS`, is the reading at the
run's; what remains of "does not depend on where it is read" is the state, `piShape_step_stmt`.) -/
theorem tyStr_futureFree (hK : ∀ n, (K.C.global n).2.label = none) (T : Value)
    (hT : ∀ l, T.hasLoan l = false) (φ' : Future) (hint : TyS) :
    tyShape K ρ φ T = tyShape K ρ φ' T ∧ tyDataV K ρ φ T = tyDataV K ρ φ' T ∧
      meanV K ρ φ hint T = meanV K ρ φ' hint T :=
  ⟨tyShape_congrE K ρ φ φ' hK T (fun l h => by
      have := Value.hasLoan_of_hasLoanM h; rw [hT l] at this; cases this),
    tyDataV_congrE K ρ φ φ' hK T (fun l h => by
      have := Value.hasLoan_of_hasLoanM h; rw [hT l] at this; cases this),
    meanV_congrE K ρ φ φ' hK T hint (fun l h => by
      have := Value.hasLoan_of_hasLoanM h; rw [hT l] at this; cases this)⟩

/-! ## A17: a proof has no type in the run -/

/-- A term the decisions class as a proof is not run and its result is typed `err`. -/
theorem erased_proof_untyped (fl : Bool × Bool) (h : fl.2 = true) (x : SM Res) (s : SState) :
    SM.erasedIf fl x s = some ((.proof, .plain .err), s) := by
  simp [SM.erasedIf, h]

/-- A field whose run is typed `err` solves no parameter of its constructor. So `MkPBox(h)`, whose
one parameter is the proposition `h` proves, has an unsolved parameter after its fields, and the
`.ctor` clause fails (`sol.all (·.isSome)`); the checker reads the parameter off the type of `h`
(`Machine.unifyParams`) and accepts (`ShapeProbes.BoxProof`). -/
theorem unify_untyped (np : Nat) (FT : Term) (sol : List (Option Sem)) :
    unifyTyS np FT (.plain .err) sol = sol := rfl

end Ochr.Meaning.Regress.ShapeAgree
