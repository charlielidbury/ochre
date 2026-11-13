import Ochr.Meaning.Attack.RunEqs
import Ochr.Meaning.Regress.CE4_flipped

/-!
# D19's batch, flipped: positive checks for the fixed reference run (built)

`Regress/Adequacy_1d94e4eb.lean` (unbuilt) records the run of 1d94e4eb failing on `f(f(a))` and on
`(let y = x; ()); x`. With D19's fixes:

* `head_in_place`: a call's head, when it is a place, is read in place: the value comes back and
  the state is as it was, whatever the place's declared reading (R2). So the inner call of
  `f(f(a))` finds `f` where the outer one read it.
* `stmt_keeps`: a term the decisions classify as a statement (`Decisions.flags`) leaves the state
  as it was and returns no label, whatever it reads or writes (R1), for the sequencing forms, a
  place, an assignment and a call. So `x` is still there after `let h : True = (let y = x; refl)`.

Axioms: propext, Classical.choice, Quot.sound.
-/

namespace Ochr.Meaning.Regress.AdequacyFlip
open Ochr Ochr.Meaning Ochr.Meaning.Attack Ochr.Meaning.Regress.CE4flip

variable (K : RunCtx) (ρ : Assignment) (φ : Future)

/-- One frame holding one binding, no holder. -/
def one (b : SBinding) (k : Nat) : SState := { env := [{ binds := [b] }], shape := fun _ => none, nextLoan := k }

/-- R2: the head of a call, a place, is read in place. -/
theorem head_in_place (b : SBinding) (k : Nat) (rn : SM Res) (hw : (b.val φ).whole) :
    SM.headOf (.place (.var 0)) (fun p => readPlace K φ p true) rn (one b k)
      = some ((b.val φ, { b.ty with label := none }), one b k) := by
  show readPlace K φ (.var 0) true (one b k) = _
  rw [readPlace_of φ K (.var 0) true (one b k) _ _ _ _ _ (contentOf_var0_one K φ k b)]
  simp [hw, one]

/-- R1: a statement leaves the state as it was. -/
theorem stmt_keeps (t : Term) (hint : TyS) (s : SState) (hfl : (K.D.flags (scopeOf s) t).1 = true)
    (r : Res) (s' : SState) (h : run K ρ φ hint t s = some (r, s'))
    (ht : t matches .letIn .. | .seq .. | .matchNat .. | .matchInd .. | .assign .. | .place .. | .call ..) :
    s' = s ∧ r.2.label = none := by
  cases t <;> simp at ht <;>
    (rw [run] at h
     simp only [SM.erasedIf] at h
     split at h
     · obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h); exact ⟨rfl, rfl⟩
     · obtain ⟨hb, -⟩ | ⟨-, e, hl, -⟩ := SM.stmtIf_some h
       · rw [hfl] at hb; cases hb
       · exact ⟨e, hl⟩)

/-- The audit's A3: an erased term (`Machine.evalAt`'s second flag: a proof) is `•` unrun, the
state as it was, whatever its clause would do. In particular a match on a proof with two arms, or
none, no longer fails. -/
theorem erased_unrun (t : Term) (hint : TyS) (s : SState) (hfl : (K.D.flags (scopeOf s) t).2 = true)
    (ht : t matches .letIn .. | .seq .. | .matchNat .. | .matchInd .. | .assign .. | .place .. | .call .. | .ctor .. | .fix ..) :
    run K ρ φ hint t s = some ((.proof, .plain .err), s) := by
  cases t <;> simp at ht <;> (rw [run]; simp only [SM.erasedIf, hfl, if_true])

/-- The audit's A9: a field of type `A` (the one parameter) given a `Nat` solves `A := Nat`
(`Pair(a, b)`, `Cons(x, xs)`'s head). -/
example : unifyTyS 1 (.place (.var 0)) (.plain (.ty0 Nat)) [none] = [some (.ty (.ty0 Nat))] := rfl

/-- A9: a field of type `List(A)` given a value whose type records `List(Nat)` solves `A := Nat`. -/
example : unifyTyS 1 (.tind "List" [.place (.var 0)]) ⟨.ty0 (List Nat), none, none, some ("List", [.ty (.ty0 Nat)])⟩ [none]
    = [some (.ty (.ty0 Nat))] := by
  simp [unifyTyS, fillParam]

/-- A9: a solved parameter is not overwritten, and a field with no type (`err`) solves nothing. -/
example : unifyTyS 1 (.place (.var 0)) (.plain (.ty0 Nat)) [some (.ty (.ty0 Unit))] = [some (.ty (.ty0 Unit))] := rfl
example : unifyTyS 1 (.place (.var 0)) (.plain .err) [none] = [none] := rfl

/-- A9: the constructor clause with every parameter solved by its fields does not fail for want
of a hint: at no hint, `sol₀` is all unsolved, and the clause's result is decided by `runFields`'
solution alone. -/
theorem ctor_no_hint (ty : String) (c : Nat) (x : Hint) (args : List Term) (s : SState) (d : IndDecl)
    (hd : K.Γ.find? (·.name == ty) = some d) (hfl : K.D.flags (scopeOf s) (.ctor ty c x [] args) = (false, false))
    (fs : List Sem) (sol : List (Option Sem)) (s' : SState)
    (hf : runFields K ρ φ (d.sort == 0) d c 0 (List.replicate d.params.length none) [] args s = some ((fs, sol), s'))
    (hsol : sol.all (·.isSome) = true) (hs : (d.sort == 0) = false) :
    run K ρ φ (.plain .err) (.ctor ty c x [] args) s
      = some ((K.dm.ctorM d (solved sol) c fs, ⟨K.dm.tyM d (solved sol), none, none, some (ty, solved sol)⟩), s') := by
  rw [run]
  simp only [SM.erasedIf, hfl, SM.stmtIf, Bool.false_eq_true, if_false, hd, runParams, bind, pure, TyS.plain,
    List.isEmpty_nil, Bool.not_true, hs]
  rw [hs] at hf
  rw [hf]
  simp only [hsol, if_true]

end Ochr.Meaning.Regress.AdequacyFlip

namespace Ochr.Meaning.Regress.AdequacyFlip
open Ochr Ochr.Meaning

variable (K : RunCtx) (ρ : Assignment) (φ : Future)

/-- R6: a parameter whose domain term is a Π-type is bound with that Π's shape, so it can be
called (`Regress/NoShape_R6.lean` records the failure before: a parameter was bound at `.plain _`).
The `.fix` clause's frame binds parameter `i` at `(runBinds …)[i].1 acc`. -/
theorem pi_param_has_shape (s : SState) (dcs : List DeclInfo) (pre : List PBind) (hs : List Hint)
    (ds : List Term) (c : Term) (acc : List Sem) :
    ((mkBind dcs pre fun acc => run K ρ φ (.plain .err) (.pi hs ds c) (extendBy s pre acc)).1 acc).shape.isSome = true := by
  simp only [mkBind, run]
  rfl

/-- ... and that binder is the one `runBinds` gives a Π-typed parameter. -/
theorem runBinds_pi (s : SState) (dcs : List DeclInfo) (pre : List PBind) (hs : List Hint)
    (ds : List Term) (c : Term) (rest : List Term) :
    (runBinds K ρ φ s dcs pre (.pi hs ds c :: rest)).head?
      = some (mkBind dcs pre fun acc => run K ρ φ (.plain .err) (.pi hs ds c) (extendBy s pre acc)) := by
  simp only [runBinds, List.head?_cons]

end Ochr.Meaning.Regress.AdequacyFlip
