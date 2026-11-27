import Ochr.Meaning.Steps.Statements
import Ochr.Meaning.RunSubst
import Ochr.Meaning.RunCongr

/-!
# A function type's structure survives where its shape did not (docs/31 D22, D59; built)

Prerequisite (a) of the migration to the simulation form (docs/31 D20 item 1): "a Π-type's
structure does not depend on where it is read". With the structure carried beside the meaning
(a Π-shape and data in the type the run returns), it was FALSE in both directions, and this file
held the kernel-checked halves: a call's result never had a shape (`call_noShape`) where the
checker's stored Π-type value had one, so after `let a = Adder(n)` or a parameter `f : Fn(Nat)`
the reference could not call `a` or `f` (probes `UseAdder`, `UseFn`); and the run of a Π-term
carried its shape in the TYPE of its result, a universe, which the checker's stored `T : Type`
has none of, so `let T = Π(n : Nat). Nat; let g : T = f; g(n)` failed (probe `Alias`).

Since D59 a type is its code, and the code holds the structure. The same places, positively:

* `call_cod`: a call's result is typed at the code the callee's telescope reaches at the
  arguments, so a function returned by a call is called along its own code (`UseAdder`), and a
  parameter whose type is a call of a type function is bound at the code that call computed
  (`UseFn`): the code is in the value the domain runs to, not beside it.
* `pi_code`: the run of a Π-term returns the type value holding its code, typed at the universe;
  the checker's binding `T : Type` holds the same value, so `g : T` is typed at `T`'s code
  (`Alias`).

The checker's side of each (the program is accepted) is asserted by `Regress/ShapeProbes.lean`.
-/

namespace Ochr.Meaning.Regress.ShapeAgree
open Ochr Ochr.Meaning

variable (K : RunCtx) (ρ : Assignment) (φ : Future)

/-- What an application gives back, as the codomain it reached: a data result's code, or a
returned borrow's content code. -/
def _root_.Ochr.Meaning.AppResultL.cod.{u} {L : Lvl.{u}} : AppResultL L → Bool × TyM
  | .data _ T _ => (false, T)
  | .ref _ c _ _ => (true, L.toTy c)

/-- **Applying along a telescope code reaches its codomain**: the result's type is the code
`telCodL` reads off the telescope at the same arguments. -/
theorem applyTelL_cod.{u} (L : Lvl.{u}) : ∀ {Fin C : Type u} (t : Tel L.Code Fin C) (readFin : Fin → List Sem)
    (f : C) (args : List Sem) (r : AppResultL L), applyTelL L t readFin f args = some r →
    telCodL L t args = some r.cod
  | _, _, .dat _ _ c, readFin, f, [], r, h => by
    simp only [applyTelL, Option.some.injEq] at h; subst h; rfl
  | _, _, .ref _ U c, readFin, f, [], r, h => by
    simp only [applyTelL, Option.some.injEq] at h; subst h; rfl
  | _, _, .param Fin isRef A c _ k, readFin, f, a :: as, r, h => by
    simp only [applyTelL] at h
    simp only [telCodL]
    cases hd : L.dec c a with
    | none => rw [hd] at h; cases h
    | some x =>
      rw [hd] at h
      exact applyTelL_cod L (k x) _ (f x) as r h
  | _, _, .dat .., _, _, _ :: _, _, h => by simp [applyTelL] at h
  | _, _, .ref .., _, _, _ :: _, _, h => by simp [applyTelL] at h
  | _, _, .param .., _, _, [], _, h => by simp [applyTelL] at h

/-- A call at level `L` is typed at the codomain its callee's telescope reaches. -/
theorem callOfL_cod.{u} (L : Lvl.{u}) {C : Type u} (t : Tel L.Code PUnit C) (fv : Sem) (args : List Res)
    {s s' : SState} {r : Res} (h : callOfL L t fv args s = some (r, s')) :
    ∃ b, telCodL L t (args.map (·.1)) = some (b, r.2.m) := by
  unfold callOfL at h
  dsimp only at h
  cases happ : applyFnL L t fv (args.map (·.1)) with
  | none => rw [happ] at h; cases h
  | some a =>
    obtain ⟨F, -, hF⟩ := Option.bind_eq_some_iff.mp happ
    have hc := applyTelL_cod L t _ F _ a hF
    rw [happ] at h
    cases a with
    | data res T fin =>
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨⟨-, rfl⟩, -⟩ := h
      exact ⟨false, hc⟩
    | ref U c fwd back =>
      simp only [SState.freshLoan, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨⟨-, rfl⟩, -⟩ := h
      exact ⟨true, hc⟩

/-- **A call is typed at the codomain code its callee's type reaches at the arguments.** -/
theorem callOf_cod (R : DataRead) (fv : Res) (args : List Res) {s s' : SState} {r : Res}
    (h : callOf R fv args s = some (r, s')) : ∃ b, fv.2.m.codAt? R (args.map (·.1)) = some (b, r.2.m) := by
  unfold callOf at h
  split at h
  · rename_i A C t e; rw [e]; exact callOfL_cod (lvl0 R) t _ _ h
  · rename_i A C t e; rw [e]; exact callOfL_cod (lvl1 R) t _ _ h
  · rename_i A C t e; rw [e]; exact callOfL_cod (lvl2 R) t _ _ h
  · cases h

open Classical in
/-- **A call's result has the code its callee's telescope reaches** (the positive form of what was
`call_noShape`): whatever the callee and the state, a call that is not erased is typed at the
codomain code of the callee's type at the argument meanings. So a function returned by a call is
called along its own code, and a type computed by a call keeps its structure. -/
theorem call_cod (hint : TyS) (f : Term) (args : List Term) (hd : Bool) (s s' : SState) (r : Res)
    (hfl : (K.D.flags (scopeOf s) (.call f args hd)).2 = false)
    (h : run K ρ φ hint (.call f args hd) s = some (r, s')) :
    ∃ (fv : Res) (as : List Res) (b : Bool), fv.2.m.codAt? K.dm.read (as.map (·.1)) = some (b, r.2.m) := by
  rw [run, runT] at h
  dsimp only at h
  unfold SM.erasedIf at h
  rw [if_neg (by simp [hfl])] at h
  have key : ∀ r₀ s₀, (do
      let fv ← SM.headOf f (fun p => SM.guarded (ContentOk K φ p) (readPlace K φ p true)) (runT K ρ φ false (.plain TyM.err) f)
      let as ← runArgs K ρ φ (K.D.flags (scopeOf s) (.call f args hd)).1 fv.2.m [] args
      fun s => if BorrowArgsTyped K.dm.read fv as s then callOf K.dm.read fv as s else none) s = some (r₀, s₀) →
      ∃ (fv : Res) (as : List Res) (b : Bool), fv.2.m.codAt? K.dm.read (as.map (·.1)) = some (b, r₀.2.m) := by
    intro r₀ s₀ h₀
    obtain ⟨fv, s₁, -, h₁⟩ := SM.bind_some h₀
    obtain ⟨as, s₂, -, h₂⟩ := SM.bind_some h₁
    split at h₂
    · obtain ⟨b, hb⟩ := callOf_cod K.dm.read fv as h₂
      exact ⟨fv, as, b, hb⟩
    · cases h₂
  rcases SM.stmtIf_some h with ⟨-, h⟩ | ⟨-, -, -, r₀, s₀, h₀, rfl⟩
  · exact key r s' h
  · exact key r₀ s₀ h₀

/-- **The run of a Π-term returns the type value holding the function type's code**, typed at the
universe of its declared sort (the positive form of what was `pi_shape`): the code is in the
value, so a binding `T = Π(n : Nat). Nat` holds it, and so does the checker's `T : Type`. -/
theorem pi_code (hint : TyS) (hs : List Hint) (ds : List Term) (c : Term) (s : SState)
    -- the strict Π-type: every domain and the codomain have a level at every typed argument tuple
    (hok : PiOk K.dm.read (runDoms K ρ φ s ds) [] (codOf K ρ φ s (bindsOf K ρ φ s ds) (ds.map Term.isRefTy) c)) :
    run K ρ φ hint (.pi hs ds c) s = some ((.ty (piTyAt K.dm.read (K.D.piSort (scopeOf s) (.pi hs ds c))
      (runDoms K ρ φ s ds) (codOf K ρ φ s (bindsOf K ρ φ s ds) (ds.map Term.isRefTy) c)),
        .plain (TyM.univ (K.D.piSort (scopeOf s) (.pi hs ds c)))), s) := by
  show runT K ρ φ false hint (.pi hs ds c) s = _
  rw [run_pi_def K ρ φ hint hs ds c s, if_pos hok]

/-- At a data sort the Π-type's code is a function type's (its telescope is what a call walks). -/
theorem piTyAt_isPi (R : DataRead) (l : Nat) (hl : l = 1 ∨ l = 2 ∨ l = 3) (ds : List PiDom) (out : PiCod) :
    (piTyAt R l ds out).isPi = true := by
  rcases hl with rfl | rfl | rfl <;> rfl

/-! ## The future does not matter -/

/-- A type value that holds no loan reads as the same code at every future. (So the checker's
reading at the constant future, `Value.tyS`, is the reading at the run's; what remains of "does
not depend on where it is read" is the state, `piShape_step_stmt`.) -/
theorem ty_futureFree (hK : ∀ n, (K.C.global n).2.label = none) (T : Value)
    (hT : ∀ l, T.hasLoan l = false) (φ' : Future) (hint : TyS) :
    meanV K ρ φ hint T = meanV K ρ φ' hint T :=
  meanV_congrE K ρ φ φ' hK T hint (fun l h => by
    have := Value.hasLoan_of_hasLoanM h; rw [hT l] at this; cases this)

/-! ## A17, superseded by the strict run: an erased proof is typed at `True` -/

/-- A term the decisions class as a proof runs on a copy of the state (the strict run's C1,
D83); its result is `•` at `True` where that run returned `•`, and nothing otherwise. (Before the
strict run, an erased proof other than a place was not run and was typed `err`, and a place was
typed at its stored type, `SM.erasedAt`.) -/
theorem erased_proof_true (fl : Bool × Bool) (h : fl.2 = true) (x : SM Res) (s : SState) :
    SM.erasedIf fl x s = match x s with
      | some ((.proof, _), _) => some ((.proof, .plain (TyM.prop True)), s)
      | _ => none := by
  simp only [SM.erasedIf, h, if_true]
  split <;> simp_all

/-- A field whose run is typed `err` solves no parameter of its constructor (`Machine.unifyParams`
reads the parameter off the field's type; before A17 a proof read at a place was typed `err`, so
`MkPBox(h)` failed where the checker accepts `ShapeProbes.BoxProof`). -/
theorem unify_untyped (dm : DataModel) (np : Nat) (FT : Term) (sol : List (Option Sem)) :
    unifyTyS dm np FT (.plain .err) sol = sol := by
  have he : (TyS.plain TyM.err).m.isErr = true := rfl
  unfold unifyTyS
  split <;> simp only [he, if_true]

end Ochr.Meaning.Regress.ShapeAgree
