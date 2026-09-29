import Ochr.Test

/-! # 4. Closing off: what a stuck computation leaves behind

Checking runs programs on abstract values, and a match on an abstract number gets stuck.
A call whose body is stuck is *closed off*: its result, and the final content of each
place it borrowed, are replaced by *sealed programs*, closed source programs that
compute them, such as `⌈let c = σ; AddM(&c, 0); c⌉` (RULES P4, [Close]). A sealed program
runs again when more is known about its inputs ([Seal]).

A match that gets stuck outside tail position (followed by more code, or inside a type)
is closed off the same way, as a call to an anonymous function of the places it uses. It
captures them as a Rust closure would: a place some arm moves out of is moved in, a place
some arm writes or borrows is borrowed, and any other place it reads is copied ("Stuck
blocks"). This is how a borrow chosen by a branch is handled.

Defined in RULES §3: [Close], [Seal], stuck blocks; [Split] in §5 checks the arms. -/

open Ochr.Test

ochr ClosingOff {
  def AddM (x : &Nat) (y : Nat) : Unit by x := (
    match *x {
      Z => *x := y,
      S p => AddM(&p, y),
    }
  )

  def AddMZero (x : &Nat) : Id Unit (AddM(x, 0)) () by x := (
    match *x {
      Z => refl,
      S p => AddMZero(&p),
    }
  )

  -- ## A borrow chosen by a branch
  -- The match is not in tail position: its arms are checked, then it is closed off, and the
  -- rest of the body runs once, on the borrow the closed-off block returns.
  def AddToOne (b : Nat) (x1 : &Nat) (x2 : &Nat) (y : Nat) : Unit := (
    let r = match b {
      Z => x1,
      S _ => x2,
    };
    AddM(r, y)
  )

  -- The same program with the continuation copied into each arm ...
  def AddToOne' (b : Nat) (x1 : &Nat) (x2 : &Nat) (y : Nat) : Unit := (
    match b {
      Z => AddM(x1, y),
      S _ => AddM(x2, y),
    }
  )

  -- ... and with the match moved into a function.
  def Pick (b : Nat) (x1 : &Nat) (x2 : &Nat) : &Nat := (
    match b {
      Z => x1,
      S _ => x2,
    }
  )

  def AddToOne'' (b : Nat) (x1 : &Nat) (x2 : &Nat) (y : Nat) : Unit := (
    let r = Pick(b, x1, x2);
    AddM(r, y)
  )

  -- Adding zero through the chosen borrow does nothing, in all three versions. For the
  -- first, the stuck match inside the goal is closed off the same way.
  def AddToOneZero (b : Nat) (x1 : &Nat) (x2 : &Nat) : Id Unit (AddToOne(b, x1, x2, 0)) () := (
    match b {
      Z => AddMZero(x1),
      S _ => AddMZero(x2),
    }
  )

  def AddToOneZero' (b : Nat) (x1 : &Nat) (x2 : &Nat) : Id Unit (AddToOne'(b, x1, x2, 0)) () := (
    match b {
      Z => AddMZero(x1),
      S _ => AddMZero(x2),
    }
  )

  def AddToOneZero'' (b : Nat) (x1 : &Nat) (x2 : &Nat) : Id Unit (AddToOne''(b, x1, x2, 0)) () := (
    match b {
      Z => AddMZero(x1),
      S _ => AddMZero(x2),
    }
  )

  -- The arms of a stuck match must agree on a type, or the match must be annotated.
  reject def ArmTypes (b : Nat) : Nat := (
    let r = match b {
      Z => 0,
      S _ => (),
    };
    0
  )

  def ArmAnnot (b : Nat) : Nat := (
    let r : Nat = match b {
      Z => 0,
      S _ => 1,
    };
    r
  )

  -- ## Stuck matches in statements
  -- Both sides close off into the same sealed program, so `refl` proves the equation.
  def StuckGoal (b : Nat) : Id Nat (match b { Z => 0, S _ => 1 }) (match b { Z => 0, S _ => 1 }) := refl

  -- After a case split on `b`, the sealed programs run again, to each arm's value.
  def StuckGoalSplit (b : Nat) : Id Nat (match b { Z => 0, S m => S m }) b := (
    match b {
      Z => refl,
      S _ => refl,
    }
  )

  -- A false statement stays unprovable (it fails when `b` is 2 or more).
  reject def StuckGoalWrong (b : Nat) : Id Nat (match b { Z => 0, S _ => 1 }) b := (
    match b {
      Z => refl,
      S _ => refl,
    }
  )

  -- A recursive call inside a match that is not in tail position is checked in its arm;
  -- the closed-off block then takes the function itself as a value argument.
  def NonTailRec (x : &Nat) : Unit by x := (
    match *x {
      Z => (),
      S p => NonTailRec(&p),
    };
    ()
  )

  -- ## What a stuck match captures
  -- A local the match writes (`c := 1`) is passed to the block by borrow, so the write is
  -- seen after the block.
  def WriteInBlock (b : Nat) :
      Id Nat (let c = b; match c { Z => c := 1, S _ => () }; c) (match b { Z => 1, S m => S m }) := (
    match b {
      Z => refl,
      S _ => refl,
    }
  )

  -- A borrow the match uses but does not move is reborrowed, so it stays usable afterwards.
  def ReborrowInBlock (b : Nat) (x : &Nat) : Unit := (
    match b {
      Z => AddM(&*x, 1),
      S _ => (),
    };
    AddM(x, 2)
  )

  -- A borrow some arm moves (`x1`, in arm `Z`) is moved into the block, so using it
  -- afterwards is a use after move. If the block only reborrowed it (switch `blockMoves`),
  -- `MovedByBlock` would be accepted, although in arm `Z` it uses `x1` after moving it into
  -- `r`.
  reject def AliasAfterBlock (b : Nat) (x1 : &Nat) (x2 : &Nat) : Unit := (
    let r = match b {
      Z => x1,
      S _ => x2,
    };
    AddM(x1, 1);
    AddM(r, 2)
  )

  reject def MovedByBlock (b : Nat) (x1 : &Nat) (x2 : &Nat) : Unit := (
    let r = match b {
      Z => x1,
      S _ => x2,
    };
    AddM(r, 1);
    AddM(x1, 2)
  )

  -- ## How a stuck call returns: the row of [Close]
  -- What a stuck call returns depends on its declared result type, read from the syntax: a
  -- call returning `Unit` returns `()`, any other data a sealed program. `UU(n)` computes to
  -- `Unit` for every `n`, but is not written `Unit`, so `G`'s stuck calls return a sealed
  -- program, and `RowI` needs induction (`RowIInd`).
  def UU (n : Nat) : Type := (
    match n {
      Z => Unit,
      S _ => Unit,
    }
  )

  def AddU (x : &Nat) : Unit by x := (
    match *x {
      Z => (),
      S p => AddU(&p),
    }
  )

  def G (x : &Nat) (n : Nat) : UU(n) by x := (
    match n {
      Z => match *x {
        Z => (),
        S p => G(&p, n),
      },
      S _ => AddU(x),
    }
  )

  def RowUnit (x : &Nat) : Id Unit (let c = *x; AddU(&c)) () := refl
  reject def RowI (x : &Nat) : Id Unit (let c = *x; G(&c, Z)) () := refl

  def RowIInd (x : &Nat) : Id Unit (let c = *x; G(&c, Z)) () by x := (
    match *x {
      Z => refl,
      S p => RowIInd(&p),
    }
  )

  -- ## What goes wrong without these rules
  -- The closed-off block of `Clear` writes through the pattern variable `p`, which names
  -- `(*x).1`: a write to `*x` (D32). If the block did not see that write (switch
  -- `patternWritesVisible`), it would copy `*x` instead of borrowing it, the write would be
  -- lost, and `Boom5` would prove `1 = 2`.
  reject def Clear (x : &Nat) : Id Unit (match *x { Z => (), S p => p := Z }) () := refl

  reject def Boom5 : Eq Nat (S Z) (S (S Z)) := (
    let c = S (S Z);
    Clear(&c)
  )

  -- A sealed program whose head is a call of an abstract function stays as it is when it is
  -- normalised (D39): it is not closed off again, which would loop. `P1` only has to be
  -- checked without looping (switch `headGuardNeutral`).
  def P1 (h : Π(x : &Nat) (y : &Nat). &Nat) : Prop := (
    Id Nat (let a = Z; let b = Z; (let r = h(&a, &b); ()); a) Z
  )

  -- An earlier version joined a match that is not in tail position by taking the refined
  -- types from its arms, so after `match b` the hypothesis `h : Id Nat b 0` could get the
  -- `S` arm's type, `False`. Closing the match off instead continues from the state before
  -- the split, where `h` still says `Id Nat b 0` (D15).
  reject def Bad (b : Nat) (h : Id Nat b 0) : False := (
    match b {
      Z => (),
      S _ => (),
    };
    h
  )
}

#eval IO.println (run "ClosingOff" ClosingOff).show

-- every verdict as expected, and the exact number of declarations (a truncated file changes it)
#guard (run "ClosingOff" ClosingOff).allAsExpected
#guard (run "ClosingOff" ClosingOff).count == 29

/-! ## Symbolic checking is not the same as checking every instance

At an abstract `n`, `Pick` returns a borrow that may point into `a` or into `b`, so its
hole is in both. Reading `b` then ends it, and the write through `r` in arm `Z` fails. At
each concrete `n` the program is fine. The checker is sound but rejects `PickEarly`: the
symbolic run agrees with the concrete ones only up to which borrows have ended (the
paper's §7, "naturality up to resolution"). -/

ochr Naturality {
  def Pick (n : Nat) (x : &Nat) (y : &Nat) : &Nat := (
    match n {
      Z => x,
      S _ => y,
    }
  )

  reject def PickEarly (n : Nat) (a : Nat) (b : Nat) : Unit := (
    let r = Pick(n, &a, &b);
    let z = b;
    match n {
      Z => *r := 5,
      S _ => (),
    }
  )

  def PickEarly0 (a : Nat) (b : Nat) : Unit := (
    let n = 0;
    let r = Pick(n, &a, &b);
    let z = b;
    match n {
      Z => *r := 5,
      S _ => (),
    }
  )

  def PickEarly1 (a : Nat) (b : Nat) : Unit := (
    let n = 1;
    let r = Pick(n, &a, &b);
    let z = b;
    match n {
      Z => *r := 5,
      S _ => (),
    }
  )
}

#eval IO.println (run "Naturality" Naturality).show

-- every verdict as expected, and the exact number of declarations (a truncated file changes it)
#guard (run "Naturality" Naturality).allAsExpected
#guard (run "Naturality" Naturality).count == 4
