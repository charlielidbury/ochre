import Ochr.Test

/-! # 3. Functions that return a borrow

A function may return a borrow into one of its borrow arguments, like Rust's
`fn tail(x: &mut Nat) -> &mut Nat`. `TailM(x)` returns a borrow of the `Z` at the bottom of
`*x`, and writing through it changes `*x`. When such a call gets stuck on an abstract
number, both what it returns and what it leaves in `*x` become sealed programs, with a
hole where the returned borrow's contents will go (RULES §3 [Close], its `&T` row).

A returned borrow always comes from a borrow argument: a function type that returns `&T`
must take a borrow (D44). This is Rust's lifetime-elision rule; Ochr has no `'static`
borrows.

Defined in RULES §1 (D44), §3 [Close] and §7. -/

open Ochr.Test

ochr ReturnedBorrows {
  def AddM (x : &Nat) (y : Nat) : Unit by x := {
    match *x {
      | Z => *x := y
      | S p => AddM(&p, y)
    }
  }

  -- A borrow of the final `Z` of `*x`.
  def TailM (x : &Nat) : &Nat by x := {
    match *x {
      | Z => x
      | S p => TailM(&p)
    }
  }

  -- Addition by writing through the returned borrow ...
  def AddM' (x : &Nat) (y : Nat) : Unit := {
    let t = TailM(x);
    *t := y
  }

  -- ... is the same as `AddM`, in its result and in what it leaves in `*x`. The proof is the
  -- same bare recursion as `AddMZero`'s.
  def AddMEq (x : &Nat) (y : Nat) : Id Unit (AddM(x, y)) (AddM'(x, y)) by x := {
    match *x {
      | Z => refl
      | S p => AddMEq(&p, y)
    }
  }

  def AddMEqOwned (x : Nat) : Id Unit (AddM(&x, 0)) (AddM'(&x, 0)) := AddMEq(&x, 0)

  -- Reading through the returned borrow, and not using it at all.
  def AddM1 (x : &Nat) : Id Unit (AddM(x, 1)) (let t = TailM(x); *t := S *t) by x := {
    match *x {
      | Z => refl
      | S p => AddM1(&p)
    }
  }

  def TailNoop (x : &Nat) : Id Unit (let t = TailM(x); ()) () by x := {
    match *x {
      | Z => refl
      | S p => TailNoop(&p)
    }
  }

  -- A returned borrow into a local would outlive the local.
  reject def DanglingTail (n : Nat) : &Nat := {
    let z = n;
    TailM(&z)
  }

  -- A function type that returns a borrow must have a borrow parameter for it to come from.
  def Keep (x : &Nat) (n : Nat) : &Nat := x
  def KeepT : Type := Π(x : &Nat) (n : Nat). &Nat
  reject def LeakT : Type := Π(n : Nat). &Nat

  -- Every function of type `Π(x : &Nat). &Nat` returns a borrow into `*x`, so writing
  -- different numbers through its result leaves different numbers in `*x`.
  def L (x : &Nat) (e : Id Unit (*x := 0) (*x := 1)) : False := e

  def Inj (g : Π(x : &Nat). &Nat) (x : &Nat) (e : Id Unit (let r = g(x); *r := 0) (let r = g(x); *r := 1)) :
      False := {
    let r = g(x);
    L(r, e)
  }

  -- ## What goes wrong without these rules
  -- Without D44 a function type could return a borrow that comes from nowhere. Closing off
  -- `g(5)` would give a borrow whose hole is in no place at all, so an `Id` about writes
  -- through it would observe nothing and be trivially true. `Q` would then refute
  -- `Π(n : Nat). &Nat`, which Rust inhabits with `Box::leak`: given such a function as an
  -- opaque `leak`, `Boom` is a closed proof of `Empty` (switch `borrowParam`).
  inductive Empty := E(e : Empty)

  def M (n : Nat) : Type := {
    match n {
      | Z => Unit
      | S _ => Empty
    }
  }

  def P (x : &Nat) (e : Id Unit (*x := 0) (*x := 1)) : Empty := J(Nat, 0, 1, M, e, ())
  reject def Q (g : Π(n : Nat). &Nat) : Empty := P(g(5), refl)
  reject def Boom (leak : Π(n : Nat). &Nat) : Empty := Q(leak)
  -- the same with the library's `False`
  def PF (x : &Nat) (e : Id Unit (*x := 0) (*x := 1)) : False := e
  reject def QF (g : Π(n : Nat). &Nat) : False := PF(g(5), refl)

  -- Matching on a place ends every borrow whose hole is inside the sealed program the
  -- place holds (D29). Here `*x` holds `TailM`'s sealed program, with the hole of `t` inside
  -- it, so `match *x` ends `t`, as the concrete run does when `*x` is `Z`. Without that
  -- (switch `matchEndsInside`), `Bad` is accepted, and `Main(0)` writes through an ended
  -- borrow when run.
  reject def Bad (x : &Nat) : Unit := {
    let t = TailM(&*x);
    match *x {
      | Z =>
        *t := S Z;
        let h : Id Nat (*x) Z = refl;
        ()
      | S _ => ()
    }
  }

  reject def Main (n : Nat) : Nat := {
    let c = n;
    Bad(&c);
    c
  }

  reject def Main0 : Nat := Main(0)
}

#eval IO.println (run "ReturnedBorrows" ReturnedBorrows).show

-- every verdict as expected, and the exact number of declarations (a truncated file changes it)
#guard (run "ReturnedBorrows" ReturnedBorrows).allAsExpected
#guard (run "ReturnedBorrows" ReturnedBorrows).count == 23
