import Ochr.Meaning.Steps.Records
import Ochr.Examples.Nat

/-!
# A callee that returns its borrow parameter: the result keeps a label issued before the call

`IdP (x : &Nat) : &Nat := x` and `let y = 2; let r = IdP(&y); *r := 5; y` are accepted. At a
hole after the call the checker holds `y ↦ lent_0 loan_0` and `r ↦ borrow_0 2`: the call's result
is the borrow `0` the argument `&y` made BEFORE the call (`callFn` runs the body in place, the body
returns the parameter's borrow, and `.ended g [0]` hands the result's marks `lent_g` to it).

The reference applies the callee's meaning (`callOf`), whose `.ref` row returns a FRESH label, the
state's counter (`Steps.callOfL_ref_label`), so never a label issued before the call; the
argument's label is consumed. After `let r = IdP(&y)` the checker's binding `r` holds `0` and the
reference's holds its counter, so any renaming relating the two states sends `0` to a label that
was not `0`'s before the call. Part (a) of the main theorem (and `SimConcl`/`SimConclT`) asks the
renaming after a step to agree with the one before on every label the checker had issued
(`∀ l < st.nextLoan, π' l = π l`), which is false here: the statements of `callFn` and of every
step that runs a call, and `callOf_inPlace`'s renaming (`τ` fixes every label below the counter),
fail at this program (docs/31 D69).

A second record, for the reference's in-place run: `Pick2 (a : &Nat) (b : &Nat) : &Nat := &*a`
lends its result at `b`'s lender too.
-/

open Ochr.Test

ochr ReturnParam uses Nats {
  def IdP (x : &Nat) : &Nat := x
  def UseIdP (u : Unit) : Nat := (let y = 2; let r = IdP(&y); *r := 5; y)
}

-- A callee whose result reborrows one of two borrow arguments: the result is lent at both lenders
-- (the checker's marks `lent_g` at every borrow argument's lender, handed to the result), so reading
-- `y` ends `r` though `r` points into `x` (`UsePick2Read`, rejected)
ochr ReturnPick uses Nats {
  def Pick2 (a : &Nat) (b : &Nat) : &Nat := &*a
  def UsePick2 (u : Unit) : Nat := (let x = 1; let y = 2; let r = Pick2(&x, &y); *r := 5; x)
  reject def UsePick2Read (u : Unit) : Nat := (let x = 1; let y = 2; let r = Pick2(&x, &y); let z = clone(y); *r := 5; x)
}

#guard_msgs (drop warning) in
ochr ReturnParamAt uses Nats {
  def IdP (x : &Nat) : &Nat := x
  def UseIdPAt (u : Unit) : Nat := (let y = 2; let r = IdP(&y); ?)
  def Pick2 (a : &Nat) (b : &Nat) : &Nat := &*a
  def UsePick2At (u : Unit) : Nat := (let x = 1; let y = 2; let r = Pick2(&x, &y); ?)
}

namespace Ochr.Meaning.Regress.ReturnParam
open Ochr Ochr.Meaning

def atHole (name : String) : List Value :=
  let r := Ochr.Test.runWith (some Prelude) "ReturnParamAt" ReturnParamAt (located := true)
  match r.rows.find? (·.name == name) with
  | some row => (row.trace.toList.filterMap fun
      | .note _ _ (.hole _ Ω) => some (Ω.map (·.2.2)) | _ => none).headD []
  | none => []

-- The checker's state after the call: `r` holds the borrow `0`, the one `&y` made.
#guard (atHole "UseIdPAt").map Value.pp == ["()", "lent_0 loan_0", "borrow_0 2"]

-- After `Pick2(&x, &y)`: `r`'s borrow `3` is lent at `x` and, by the mark, at `y`. The reference's
-- in-place run lends its result every place a borrow argument lent before the call
-- (`CallRef.runCallRef`), as `callOf` does; as first written it kept the sites the pop's [End]s gave
-- the reborrow, `x`'s only.
#guard (atHole "UsePick2At").map Value.pp == ["()", "lent_3 loan_3", "lent_3 2", "borrow_3 1"]

/-- **No renaming that agrees before the call relates the result** (the reference's side): the
result of `callOf`'s `.ref` row is a label no state before the call had issued, so it is not the
image of the checker's result label `0` under a renaming that keeps `0`'s image from before the call,
which is below the reference's counter (`Rel.fresh`). -/
theorem result_not_old.{u} (Lv : Lvl.{u}) {C : Type u} (t : Tel Lv.Code PUnit C) (fv : Sem) (args : List Res)
    {s s' : SState} {res : Res} (h : callOfL Lv t fv args s = some (res, s'))
    {U : Type u} {c : Lv.Code U} {fwd : U} {back : U → List Sem}
    (happ : applyFnL Lv t fv (args.map (·.1)) = some (.ref U c fwd back))
    (π : Nat → Nat) (l : Nat) (hl : π l < s.nextLoan) : res.2.label ≠ some (π l) := by
  rw [Steps.callOfL_ref_label Lv t fv args h happ]
  intro he
  injection he with he
  omega

end Ochr.Meaning.Regress.ReturnParam
