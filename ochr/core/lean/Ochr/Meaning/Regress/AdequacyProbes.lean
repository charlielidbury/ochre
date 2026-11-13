import Ochr.Examples.Nat
import Ochr.Examples.List

/-!
# Checker verdicts the reference run must match (built: each verdict is asserted)

Five small programs the checker ACCEPTS, each with a flipped control it REJECTS, found by reading
`Run.lean`'s clauses against `Machine.evalAt`/`evalCore` (docs/31 D19). On each accepted one the
reference run of spine 1d94e4eb fails (`none`), so its closure means `err` and "an accepted
definition means an element of its type" is false of it: five definition faults of the reference
run, none of the checker. `Regress/Adequacy_1d94e4eb.lean` kernel-checks the first two failures.

* `Twice`: a call reads its head in place (D53 (e), `evalCall`: `inPlace`); the run read it by
  `run f`, which moves a function variable out.
* `ErasedLet`: an erased term that is not a call runs on a private copy (`evalAt`: `inStatement`);
  the run asked `Decisions.flags` only of calls.
* `CopyParam`: a parameter's declared reading is its Π-type's (`runBodyCore`: `paramDecls`); the
  run's `.fix` clause bound parameters at the reading `other`, which is never a copy type.
* `StmtArgs`: each argument of a statement call runs on its own private copy (`stmtArgIf`); the
  run ran them in sequence on the call's one copy.
* `AssignOrder`: an assignment evaluates its right-hand side before it accesses the place
  (`evalCore`'s `.assign`, then `assignPlace`); the run accessed the place first, which ends the
  borrow the right-hand side reads through.
-/

open Ochr.Test

ochr AdequacyProbes uses Nats, Lists {
  -- the head is read in place: `f` is still there for the second call
  def Twice (f : Π(n : Nat). Nat) (n : Nat) : Nat := f(f(n))
  def TwiceLet (f : Π(n : Nat). Nat) (n : Nat) : Nat := (let a = f(n); f(a))
  -- control: the function READ twice is moved by the first read
  reject def ReadTwice (f : Π(n : Nat). Nat) (n : Nat) : Nat := (let g = f; let h = f; g(n))

  -- a proof-valued `let` runs on a private copy: its move of `x` is undone with the copy
  def ErasedLet (x : List(Nat)) : List(Nat) := (
    let h : True = (let y = x; refl);
    x
  )
  -- control: the same right-hand side as data moves `x` for real
  reject def DataLet (x : List(Nat)) : List(Nat) := (
    let h : Nat = (let y = x; 0);
    x
  )

  -- a parameter whose declared type is a copy type is copied by each read
  def CopyParam (u : Unit) : Unit × Unit := (u, u)
  -- control: a parameter of a non-copy type is moved by the first
  reject def MoveParam (x : List(Nat)) : List(Nat) × List(Nat) := (x, x)

  -- each argument of a statement call runs on its own copy: `x` twice, and again after
  def LemTwo (a : List(Nat)) (b : List(Nat)) : True := refl
  def StmtArgs (x : List(Nat)) : List(Nat) := (let h : True = LemTwo(x, x); x)
  -- control: the same two arguments to a data call
  def DataTwo (a : List(Nat)) (b : List(Nat)) : Nat := 0
  reject def DataArgs (x : List(Nat)) : Nat := DataTwo(x, x)

  -- the right-hand side runs before the place is accessed: `*r` is read while `r` still lives
  def AssignOrder (y0 : Nat) : Nat := (let y = y0; let r = &y; y := clone(*r); y)
}
