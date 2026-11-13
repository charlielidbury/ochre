import Ochr.Examples.Nat
import Ochr.Examples.List
import Ochr.Examples.Box

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

/-! ## The audit's probes (docs/31, "Run against evalCore: audit")

One accepted program for each divergence the clause-by-clause audit found, beside a control the
checker rejects where one can be written. The rows are the audit table's (A1, A2, …). -/

ochr AdequacyProbes2 uses Nats, Lists, Boxes {
  -- A1 ([Access] is of a place, not of a variable): a field is read while another field of the
  -- same variable is lent; the borrow stays live, and the write through it is seen
  def Disjoint (x : Nat) (y : Nat) : Nat × Nat := (
    let p = (x, y);
    let r = &p.1;
    let a = p.0;
    *r := 5;
    (a, p.1)
  )
  def DisjointIs (x : Nat) (y : Nat) : Id(Nat × Nat, Disjoint(clone(x), clone(y)), (clone(x), 5)) := refl
  -- control: the SAME field is read, which ends the borrow; the write through it is an error
  reject def SameField (x : Nat) (y : Nat) : Nat × Nat := (
    let p = (x, y);
    let r = &p.1;
    let a = p.1;
    *r := 5;
    (a, p.0)
  )

  -- A2 (D67, an assignment over a borrow variable does not end what its content lends): the
  -- cursor is re-pointed at a part of what it borrows, and the write through it reaches `*l`
  def Walk (l : &List(Nat)) : Unit := (
    let c = &*l;
    match *c {
      Nil => (),
      Cons(h, t) => (c := &t; *c := Nil[Nat])
    }
  )
  -- control: a second borrow of the part, used after the cursor wrote over it
  reject def WalkBad (l : &List(Nat)) : Unit := (
    let c = &*l;
    match *c {
      Nil => (),
      Cons(h, t) => (let d = &t; *c := Nil[Nat]; *d := Nil[Nat])
    }
  )

  -- A3 (a proof is not run): a match on a proof of a proposition with two constructors, inside a
  -- data function
  inductive Or (P : Prop) (Q : Prop) : Prop := Inl(p : P) | Inr(q : Q)
  def UseOrInline (P : Prop) (h : Or(P, P)) (x : List(Nat)) : List(Nat) := (
    let k : Or(P, P) = (match h { Inl(a) => Inr[P, P](a), Inr(b) => Inl[P, P](b) });
    x
  )
  -- control: the same match into data (a proof of `Or` is not a subsingleton)
  reject def OrData (P : Prop) (Q : Prop) (h : Or(P, Q)) : Nat := (
    match h { Inl(a) => Z, Inr(b) => S(Z) }
  )

  -- A5 (`Id` observes the places that were there): one side borrows and the other does not
  def IdBorrow (x : Nat) : Id(Unit, (let r = &x; ()), ()) := refl
  -- control: the side that borrows also writes
  reject def IdBorrowW (x : Nat) : Id(Unit, (let r = &x; *r := Z), ()) := refl

  -- A7 (an annotation gives its term the type's structure): a function type, and `D(ā)` for a
  -- constructor whose parameters are not written
  def AnnFn (f : Π(n : Nat). Nat) (n : Nat) : Nat := (let g : Π(n : Nat). Nat = f; g(n))
  def NilAnn (n : Nat) : Nat := (let xs : List(Nat) = Nil; n)
  -- control: an annotation the term does not have
  reject def AnnFnBad (f : Π(n : Nat). Nat) (n : Nat) : Nat := (let g : Nat = f; n)

  -- A8 (a constructor's unwritten parameters come from its context): as a call's argument and as
  -- a function's result
  def LenAcc (xs : List(Nat)) (acc : List(Nat)) : Nat := Z
  def NilArg (xs : List(Nat)) : Nat := LenAcc(xs, Nil)
  def NilRes (n : Nat) : List(Nat) := Nil
  -- A9 (... or from its fields' types): an unannotated pair, an unannotated `Cons`
  def PairLet (x : Nat) (y : Nat) : Nat := (let p = (x, y); p.0)
  def ConsLet (x : Nat) (xs : List(Nat)) : List(Nat) := (let ys = Cons(x, xs); ys)
  -- control for both: nothing gives the parameter
  reject def NilBare (n : Nat) : Nat := (let xs = Nil; n)

  -- A10 (a closure value's captures keep their types' structure): a closure that calls two
  -- captured functions
  def Compose (f : Π(n : Nat). Nat) (g : Π(n : Nat). Nat) (n : Nat) : Nat := (
    let h = (λ(m : Nat) : Nat => f(g(m)));
    h(n)
  )
  -- control: a closure captures no borrow
  reject def CapBorrow (x : &Nat) : Nat := (let h = (λ(m : Nat) : Nat => clone(*x)); h(Z))

  -- A11 (a call's result has its codomain's structure): a function returned by a call is called
  def Adder (n : Nat) : (Π(m : Nat). Nat) := (λ(m : Nat) : Nat => Add(clone(n), m))
  def UseAdder (n : Nat) : Nat := (let a = Adder(n); a(Z))
  -- A12 (... and so has a field): a function read from a field is called
  def UseBoxFn (b : Box(Π(n : Nat). Nat)) : Nat := match b { MkBox(f) => f(0) }

  -- A13 ([Open]: a dependent value is open between two writes)
  inductive One := O
  def T2 (n : Nat) : Type := (match n { Z => Unit, S m => One })
  inductive W2 := MkW(n : Nat, x : T2(n))
  def Refill2 (v : &W2) : Unit := (
    match *v { MkW(n, x) => (n := S(Z); x := O) }
  )
  -- control: left open where the function returns
  reject def Refill2Open (v : &W2) : Unit := (
    match *v { MkW(n, x) => (n := S(Z)) }
  )
}
