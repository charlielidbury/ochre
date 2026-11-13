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

open Classical in
/-- The audit's A1: [Access] for an observation that reads no live label ends nothing, whatever
the rest of the position's meaning reads. So reading `x.b` leaves a borrow of `x.a` live (the
content at `.b` does not depend on `x.a`'s final content), and matching a scrutinee leaves the
borrows inside its fields live (its tag does not depend on them); before, [Access] ended every
label the whole position's meaning read (`o = id`). -/
theorem access_ends_nothing (s : SState) (p : Pos) (o : Sem → Sem) (h : ∀ l, ¬ s.obsDep p o l) :
    s.access p o = s := by
  have hround : SState.accessRound p o s = s := by
    have hf : (s.liveLabels.filter fun l => decide (s.obsDep p o l)) = [] := by
      apply List.filter_eq_nil_iff.mpr
      intro l _
      simp only [decide_eq_true_eq]
      exact h l
    unfold SState.accessRound
    rw [hf]; rfl
  rw [SState.access_eq_rounds]
  generalize List.range s.liveLabels.length = ns
  induction ns with
  | nil => rfl
  | cons _ ns ih => rw [List.foldl_cons, hround]; exact ih

/-- A1, the instance: a position holding a pair-like tuple whose first component reads label `l`
and whose second is a constant. Observing the second component ends nothing; observing the whole
meaning depends on `l`. -/
theorem access_other_field (s : SState) (p : Pos) (l : Nat) (c : Sem)
    (hv : ∀ ψ, s.valAt p ψ = .ctor "P" 0 [ψ l, c]) :
    s.access p (fun x => match x with | .ctor _ _ [_, b] => b | _ => .err) = s ∧ s.obsDep p id l := by
  refine ⟨access_ends_nothing s p _ fun l' ⟨ψ, x, hne⟩ => hne (by simp only [hv]), ?_⟩
  refine ⟨fun _ => .err, .proof, ?_⟩
  simp [hv, Future.upd]

/-- The audit's A16: a checker binding whose stored type is a Π-type has that Π's shape in the
reference state, so it can be called (`Value.tyS` reads `CodeMeaning.tyShape`, the run's
`tyShape`; before, `Value.tyS` had no shape and `callOf` failed). -/
theorem stored_pi_has_shape (caps : List Value) (hs : List Hint) (ds : List Term) (c : Term) (rd : List (DeclInfo × Value)) :
    (Value.tyS K.dm K.M K.Γ ρ (.tPi caps (.pi hs ds c) rd)).shape.isSome = true := by
  show (tyShape K ρ noFuture (.tPi caps (.pi hs ds c) rd)).isSome = true
  rw [tyShape]
  cases c <;> simp [piShapeOf]

/-- The audit's A10: a closure's capture whose recorded type is a Π-type is bound with that Π's
shape (before, `capsTys` read every recorded type as `.plain _`). -/
theorem captured_pi_has_shape (d : DeclInfo) (caps : List Value) (hs : List Hint) (ds : List Term) (c : Term)
    (rd rest : List (DeclInfo × Value)) :
    ((capsTys K ρ φ ((d, .tPi caps (.pi hs ds c) rd) :: rest)).head?.map (·.2.shape.isSome)) = some true := by
  rw [capsTys]
  simp only [List.head?_cons, Option.map_some, Option.some.injEq]
  rw [tyShape]
  cases c <;> simp [piShapeOf]

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
