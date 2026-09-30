import Ochr.Examples.«00Std»

/-! # 15. Borrow types: what may be borrowed, and where `&` may appear

`&A` is a type only when `A` is data: `Nat`, `Unit`, or an inductive type in `Type` at any
parameters, pairs included (D48 (1); a pair is the library's `Pair`, D52). It is never a
borrow of a universe, a proposition, a function type or a type variable. And `&A` may appear
only as the whole declared type of a parameter, a result or an annotated term: never inside
another type, so there are no borrows inside data, and never as the value of a type-level
computation (D48 (2)). These are the core's limits; Rust's iterators of borrows (`IterM`)
are outside it.

Defined in RULES §1 (the scope paragraph) and D48. -/

open Ochr.Test

ochr BorrowTypes uses Std {
  -- Data may be borrowed: an inductive type at any parameter (`Std`'s `List(A)`), a pair ...
  def RefList (A : Type) (xs : &List(A)) : Unit := ()
  def RefPair (p : &(Nat × Unit)) : Unit := *p := (0, ())

  -- ... including a box of propositions (`Std`'s `Box`), which is data even though what it
  -- holds is a type.
  def RefBoxProp (x : &Box(Prop)) : Unit := ()

  -- `&` at the top of a result (`Std`'s `TailM`), an annotation, and the parts of a Π-type.
  def Ann (x : &Nat) : Unit := (
    let r : &Nat = TailM(x);
    *r := 1
  )

  def HO (f : Π(x : &Nat). &Nat) (y : &Nat) : Unit := (
    let r = f(y);
    *r := 2
  )

  -- Not the universe of propositions, not a proposition, not a function type, and not a
  -- type variable, which might stand for any of these.
  reject def PIref (x : &Prop) (h1 : *x) (h2 : *x) : Id (*x) h1 h2 := refl
  reject def RefTrue (x : &True) : Nat := 0
  reject def RefFun (f : &(Π(n : Nat). Nat)) : Nat := 0
  reject def SwapT (A : Type) (x : &A) (y : &A) : Unit := ()

  -- ... and the same holds for the borrow term `&p`: the borrowed place's type is data
  -- (reviewer-6's A12: the check was made only for the type former). A proposition, a
  -- universe, a type variable, a function, a proof; and a place whose type is known only by
  -- computation, which a stuck match would have to borrow.
  reject def BorrowProp (x : Prop) : Unit := (let r = &x; ())
  reject def BorrowVar (A : Type) (x : A) : Unit := (let r = &x; ())
  reject def BorrowType (A : Type) : Unit := (let r = &A; *r := Nat)
  reject def BorrowTypeUse (A : Type) (a : A) : Nat := (let r = &A; *r := Nat; let b : *r = 5; b)
  reject def BorrowFn (f : Π(n : Nat). Nat) : Nat := (let r = &f; *r := (λ(n : Nat) : Nat => 0); f(3))
  reject def BorrowProof (P : Prop) (h : P) : Unit := (let r = &h; ())
  def TP (n : Nat) : Type := match n { Z => Prop, S _ => Nat }
  reject def BorrowStuck (n : Nat) (x : TP(n)) : Nat := (match n { Z => (let r = &x; ()), S _ => () }; 0)
  def TN (n : Nat) : Type := match n { Z => Nat, S _ => Nat }
  reject def BlockBorrowStuck (n : Nat) (x : TN(n)) : Nat := (match n { Z => (x := 5), S _ => () }; 0)
  def BorrowData (x : Nat × Nat) : Unit := (let r = &x; ())

  -- No `&` inside another type: not in a pair, in `Id`'s type, a list, or a field.
  reject def InPair (p : Nat × &Nat) : Nat := 0
  reject def InId (x : &Nat) (h : Id (&Nat) x x) : Nat := 0
  reject def IterM (xs : &List(Nat)) : List(&Nat) := Nil
  reject inductive RefCell := MkRef(r : &Nat)

  -- ## What goes wrong without this rule
  -- A result type that computes to `&Nat` at `n = 0` but is not written `&A`. [Close] reads
  -- the row from the declared result type, so at the generic call `F` returns data, while at
  -- `n = 0` it returns a live borrow of `a`. `G` then reads `a`: at the generic call that is
  -- fine, but at `n = 0` it ends the borrow `r`, so `G`'s read of `r` after it is of a dead
  -- borrow, and `UseG` reads `⊥` when run (switch `refTop`). (Until D53, `G` read `r` twice,
  -- which copied data but moved a borrow; reads of data move now too, so that witness was
  -- caught by D53 itself.)
  reject def F (n : Nat) (x : &Nat) : match n { Z => &Nat, S _ => Nat } := (
    match n {
      Z => x,
      S _ => 0,
    }
  )

  reject def G (n : Nat) (a : Nat) : Unit := (
    let r = F(n, &a);
    let b = a;
    let r2 = r;
    ()
  )

  reject def UseG : Unit := G(0, 5)
}

#eval IO.println (run "BorrowTypes" BorrowTypes).show

-- every verdict as expected, and the exact number of declarations (a truncated file changes it)
#guard (run "BorrowTypes" BorrowTypes).allAsExpected
#guard (run "BorrowTypes" BorrowTypes).count == 27

/-! ## Abstract and unsized types (K2, K3)

A library may keep a type's representation to itself. The constructors of an `abstract`
type, and matches on them, occur at runtime only in model code: the body of a function
`implemented by` native code (the checker runs the body, the compiler calls the native), or
of a model function, one that takes or returns an `unsized` value, which runtime code never
holds. In erased positions (types, statements, proofs) the model is unrestricted. At
runtime outside model code, a place of an `unsized` type is only borrowed: never read, moved,
assigned or matched. The arrays case study keeps its views this way (`16Arrays`,
reviewer-7's `Suffix`, `TwoParts`, `Rebuild`). -/

ochr Abstraction uses Std {
  unsized abstract inductive View := MkView(v : Nat)
  -- a model function (a view by value)
  def ViewVal (w : View) : Nat := match w { MkView(v) => v }
  -- natives: their bodies are the models the checker runs
  def Get (s : &View) : Nat := ViewVal(clone(*s)) implemented by "view_get"
  def Put (s : &View) (n : Nat) : Unit := (*s := MkView(n)) implemented by "view_put"
  -- runtime code goes through the natives ...
  def Bump (s : &View) : Unit := (let n = Get(&*s); Put(s, S n))
  -- ... and statements see the model
  def GetIs (s : &View) : Id Nat (Get(s)) (ViewVal(*s)) := refl
  -- matching, building, reading or assigning a view at runtime is not allowed
  reject def Peek (s : &View) : Nat := match *s { MkView(v) => clone(v) }
  reject def Poke (s : &View) : Unit := *s := MkView(0)
  reject def Take (s : &View) : Nat := ViewVal(clone(*s))
  -- ... nor is reading one, moving one into a call, or assigning one view to another (the
  -- paper's "only ever borrowed, never read, moved, assigned, cloned or matched")
  reject def ReadV (s : &View) : Unit := (let w = *s; *s := w)
  reject def PassV (s : &View) : Nat := ViewVal(*s)
  reject def AssignV (s : &View) (t : &View) : Unit := *s := *t
}

#eval IO.println (run "Abstraction" Abstraction).show

#guard (run "Abstraction" Abstraction).allAsExpected
#guard (run "Abstraction" Abstraction).count == 12
