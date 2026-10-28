import Ochr.Examples.Bool
import Ochr.Examples.Nat
import Ochr.Examples.HashMap

/-! # The editor: every error at the source responsible (docs/07)

Each `reject def` here is rejected, and `#ochr_error_at B D "before⟦t⟧after"` asserts that
the error is reported at the source text `t`, in that context. Where the term responsible is
not the one being evaluated, the checker says so: an argument's type is checked by the call
(`callType`), a borrow ended by a later argument is found at the call (`noteEnders`), and an
error inside a callee's body or a sealed program's re-run (call depth above 0) belongs to the
point in the declaration that started it. Source locations are a table keyed by the address
of each resolved term (`Ochr/Loc.lean`), which keeps every node it records alive, so an
address is never reused by another term while the table is in use: the second block checks
its declarations after the whole hash-map library, which allocates and frees a great deal. -/

open Ochr.Test

ochr EditorErrors uses Bools, Nats {
  def Count (k : Nat) : Nat by k := (
    match k {
      Z => 0,
      S p => S(Count(p)),
    }
  )

  def G (b : Bool) (k : Nat) : Nat := (
    match b {
      false => 0,
      true => Count(k),
    }
  )

  -- an ill-typed argument: the argument
  reject def BadArg (x : &Nat) : Unit := AddM(x, ())

  -- reading a moved borrow: the read
  reject def UseMoved (x : &Nat) : Unit := (
    AddM(x, 0);
    AddM(x, 1)
  )

  -- a later argument ends an earlier argument's borrow: the access that ended it
  reject def Dead (f : Π(a : &Nat) (b : Nat). Unit) (y : Nat) : Unit := f(&y, y)

  -- a failed `refl` in one arm: that `refl`
  reject def ArmRefl (x : &Nat) : Id(Nat, clone(*x), 0) := (
    match *x {
      Z => refl,
      S p => refl,
    }
  )

  -- inside a λ's body, which `capture` rebuilds: the argument inside the body
  reject def InLambda (y : Nat) : Nat := (
    let f = (λ(z : Nat) : Nat => Add(z, ()));
    f(y)
  )

  -- a surface error (no such place): the term
  reject def NotAPlace (x : &Nat) : Unit := AddM(&q, 0)

  -- `Deep : Nat := Count(3000)` and `ReRun`, a `G(b, 3000)` re-run when a split refines `b`,
  -- were tests here of an error inside a callee's body or a sealed program's re-run (call depth
  -- above 0), located at the call that started it. Their error was the call-depth limit, and
  -- running past a limit is no longer an error: the checker does not know, and the verdict is
  -- `undecided` (`Ochr/Catch.lean`, `notes/catch-census.md`), which has no source location. An
  -- accepted callee's body has no other way to fail, so no test of that location remains.
}


#ochr_error_at EditorErrors BadArg "AddM(x, ⟦()⟧)"
#ochr_error_at EditorErrors UseMoved "AddM(⟦x⟧, 1)"
#ochr_error_at EditorErrors Dead "f(&y, ⟦y⟧)"
#ochr_error_at EditorErrors ArmRefl "S p => ⟦refl⟧"
#ochr_error_at EditorErrors InLambda "Add(z, ⟦()⟧)"
#ochr_error_at EditorErrors NotAPlace "AddM(⟦&q⟧, 0)"

-- After the hash-map library, checked again as its library: these declarations are resolved
-- before the library is checked and checked after it, so their table must survive that.
ochr EditorAfterLibrary uses Nats, HashMap, HashMapLookup, HashMapLength, HashMapResize {
  reject def LateArg (x : &Nat) : Unit := AddM(x, ())

  reject def LateLambda (y : Nat) : Nat := (
    let f = (λ(z : Nat) : Nat => Add(z, ()));
    f(y)
  )

  reject def LateMoved (x : &Nat) : Unit := (
    AddM(x, 0);
    AddM(x, 2)
  )
}


#ochr_error_at EditorAfterLibrary LateArg "AddM(x, ⟦()⟧)"
#ochr_error_at EditorAfterLibrary LateLambda "Add(z, ⟦()⟧)"
#ochr_error_at EditorAfterLibrary LateMoved "AddM(⟦x⟧, 2)"
