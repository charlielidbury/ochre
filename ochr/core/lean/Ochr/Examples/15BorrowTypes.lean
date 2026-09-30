import Ochr.Examples.«00Std»

/-! # 15. Borrow types: what may be borrowed, and where `&` may appear

`&A` is a type exactly when `A : Type` (D66). `Prop` lives in `Type₁`, beside `Type`, so
everything in `Type` exists at runtime: data (`Nat`, `Unit`, an inductive type in `Type` at any
parameters, pairs included: a pair is the library's `Pair`, D52), function types into data or
functions, and a type variable declared in `Type`. A proposition, `Prop` and the universes are
not in `Type`, so they are never borrowed. The borrow term `&p` needs the same of the
borrowed place's type. And `&A` may appear only as the whole declared type of a parameter, a
result or an annotated term: never inside another type, so there are no borrows inside data,
and never as the value of a type-level computation (D48 (2)). These are the core's limits;
Rust's iterators of borrows (`IterM`) are outside it.

Defined in RULES §1 (the scope paragraph), D48 and D66. -/

open Ochr.Test

ochr BorrowTypes uses Std {
  -- Data may be borrowed: an inductive type at any parameter (`Std`'s `List(A)`), a pair ...
  def RefList (A : Type) (xs : &List(A)) : Unit := ()
  def RefPair (p : &(Nat × Unit)) : Unit := *p := (0, ())

  -- ... and so may functions and type variables: everything in `Type` exists at runtime.
  def RefFun (f : &(Π(n : Nat). Nat)) : Nat := 0
  def SwapT (A : Type) (x : &A) (y : &A) : Unit := ()

  -- `&` at the top of a result (`Std`'s `TailM`), an annotation, and the parts of a Π-type.
  def Ann (x : &Nat) : Unit := (
    let r : &Nat = TailM(x);
    *r := 1
  )

  def HO (f : Π(x : &Nat). &Nat) (y : &Nat) : Unit := (
    let r = f(y);
    *r := 2
  )

  -- Not the universe of propositions, not a proposition, and not a universe: none is in
  -- `Type`. A box of propositions is not even a type: `Box`'s parameter is in `Type`, and
  -- `Prop` is not (it was data before D66).
  reject def PIref (x : &Prop) (h1 : *x) (h2 : *x) : Id (*x) h1 h2 := refl
  reject def RefTrue (x : &True) : Nat := 0
  reject def RefType (x : &Type) : Nat := 0
  reject def RefBoxProp (x : &Box(Prop)) : Unit := ()

  -- ... and the same holds for the borrow term `&p` (reviewer-6's A12: the check was made
  -- only for the type former): a proposition, a universe and a proof are not borrowed; an
  -- inhabitant of a type variable and a function are.
  reject def BorrowProp (x : Prop) : Unit := (let r = &x; ())
  def BorrowVar (A : Type) (x : A) : Unit := (let r = &x; ())
  reject def BorrowType (A : Type) : Unit := (let r = &A; *r := Nat)
  reject def BorrowTypeUse (A : Type) (a : A) : Nat := (let r = &A; *r := Nat; let b : *r = 5; b)
  def BorrowFn (f : Π(n : Nat). Nat) : Nat := (let r = &f; *r := (λ(n : Nat) : Nat => 0); f(3))
  reject def BorrowProof (P : Prop) (h : P) : Unit := (let r = &h; ())

  -- A place whose type is known only by computation is borrowed by its type's declared
  -- universe. `TP(n)` is declared in `Type₁` (it is `Prop` at `0`), so neither the arm nor
  -- the stuck match around it may borrow `x : TP(n)`; `TN(n)` is declared in `Type`, so every
  -- instance is in `Type`, and the stuck match borrows `x`. A `Type` that is `Prop` at some
  -- instance is not a `Type` (`TPType`).
  def TP (n : Nat) : Type₁ := match n { Z => Prop, S _ => Type }
  reject def BorrowStuck (n : Nat) (x : TP(n)) : Nat := (match n { Z => (let r = &x; ()), S _ => () }; 0)
  def TN (n : Nat) : Type := match n { Z => Nat, S _ => Nat }
  def BlockBorrowStuck (n : Nat) (x : TN(n)) : Nat := (match n { Z => (x := 5), S _ => () }; 0)
  reject def TPType (n : Nat) : Type := match n { Z => Prop, S _ => Nat }
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
#guard (run "BorrowTypes" BorrowTypes).count == 29

/-! ## Borrowing functions and type variables (D66)

A function in a place is a closure like any other value: [Access], [Borrow], [End] and
[Assign] do not look at what a place holds, and a call through a borrow reads the place
without consuming it (D53's Fn rule). A stuck function with a function-typed borrow parameter
closes off as any other does: the final content of the borrowed place is a sealed program of
function type, and a later call of it is a call with an unknown head, which closes off too
(D26). Code generic over `V : Type` borrows `V`s: a swap, and the hash map's bucket lookup
with a generic value type. Functions are still compared by their generic calls (D30), with
no extensionality. -/

ochr FnBorrows uses Std {
  -- Borrow a closure, write another through the borrow, and call through it; the new
  -- closure may capture (a closure's body copies its captures: the Fn rule).
  def SetSucc (f : &(Π(n : Nat). Nat)) : Unit := *f := (λ(n : Nat) : Nat => S n)
  def SetAdder (f : &(Π(n : Nat). Nat)) (k : Nat) : Unit := *f := (λ(n : Nat) : Nat => Add(clone(k), n))
  def CallThrough (f : &(Π(n : Nat). Nat)) (n : Nat) : Nat := (*f)(n)
  def RunSucc : Id Nat (let g = (λ(n : Nat) : Nat => 0); SetSucc(&g); CallThrough(&g, 4)) 5 := refl
  def RunAdder : Id Nat (let g = (λ(n : Nat) : Nat => 0); SetAdder(&g, 3); g(4)) 7 := refl
  def RunAdderGen (k : Nat) : Id Nat (let g = (λ(n : Nat) : Nat => 0); SetAdder(&g, k); g(0)) (Add(k, 0)) := refl

  -- A function with a function-typed borrow parameter, stuck at an abstract `n`: `g`'s final
  -- content is a sealed program, and `g(3)` is a call with an unknown head.
  def SetIf (n : Nat) (f : &(Π(m : Nat). Nat)) : Unit := match n { Z => (), S _ => *f := (λ(m : Nat) : Nat => S m) }
  def UseSetIf (n : Nat) : Nat := (let g = (λ(m : Nat) : Nat => m); SetIf(n, &g); g(3))
  def UseSetIf0 : Id Nat (UseSetIf(0)) 3 := refl
  def UseSetIfS (n : Nat) : Id Nat (UseSetIf(S n)) 4 := refl
  reject def UseSetIfWrong (n : Nat) : Id Nat (UseSetIf(n)) 3 := refl

  -- A generic swap, at data and at functions.
  def Swap (V : Type) (a : &V) (b : &V) : Unit := (let t = *a; *a := *b; *b := t)
  def SwapNats : Id (Nat × Nat) (let x = 1; let y = 2; Swap(Nat, &x, &y); (x, y)) (2, 1) := refl
  def SwapFns : Id Nat (
    let f = (λ(n : Nat) : Nat => 0);
    let g = (λ(n : Nat) : Nat => S n);
    Swap(Π(n : Nat). Nat, &f, &g);
    f(6)) 7 := refl

  -- A bucket generic in its value type, and the borrow of a present key's value.
  inductive GBucket (V : Type) := GNil | GCons(k : Word, v : V, t : GBucket(V))
  def EqW (a : Word) (b : Word) : Bool by a := (
    match a {
      Zero => match b { Zero => true, Succ(_) => false },
      Succ(a') => match b { Zero => false, Succ(b') => EqW(a', b') },
    }
  )
  def GContains (V : Type) (b : &GBucket(V)) (k : Word) : Bool by b := (
    match *b {
      GNil => false,
      GCons(k', v', t) => (
        let e = EqW(k', k);
        match e { false => GContains(V, &t, k), true => true }
      ),
    }
  )
  def IsTrue (b : Bool) : Prop := match b { false => False, true => ⊤ }
  -- presence, on a copy, for statements (as the hash map's `BFind`)
  def GFind (V : Type) (b : GBucket(V)) (k : Word) : Bool := GContains(V, &b, k)
  def GHas (V : Type) (b : GBucket(V)) (k : Word) : Prop := IsTrue(GFind(V, b, k))
  def GGetMut (V : Type) (b : &GBucket(V)) (k : Word) (h : GHas(V, *b, k)) : &V by b := (
    match *b {
      GNil => match h {},
      GCons(k', v', t) => (
        let e = EqW(k', k);
        match e { false => GGetMut(V, &t, k, h), true => &v' }
      ),
    }
  )
  def RunGGetMut : Id Nat (
    let b = GCons(Zero, (λ(n : Nat) : Nat => n), GNil);
    let r = GGetMut(Π(n : Nat). Nat, &b, Zero, refl);
    *r := (λ(n : Nat) : Nat => S n);
    match b { GNil => 0, GCons(k, v, t) => v(4) }) 5 := refl

  -- Still not: a proposition, `Prop`, or a type variable in `Type₁`; and code generic over
  -- `A : Type` is not applied to `Prop`, which is in `Type₁`.
  reject def SwapProps (p : Prop) (q : Prop) : Unit := Swap(Prop, &p, &q)
  reject def SwapT1 (A : Type₁) (x : &A) (y : &A) : Unit := ()
  def IdT (A : Type) (a : A) : A := a
  reject def IdAtProp (P : Prop) : Prop := IdT(Prop, P)
  def IdT1 (A : Type₁) (a : A) : A := a
  def IdAtProp1 (P : Prop) : Prop := IdT1(Prop, P)

  -- A function type's universe: a Π over a proposition is in `Type₁`, so neither borrowed
  -- nor boxed; a Π over a proof, or returning a borrow, is in `Type`.
  reject def RefPropFn (f : &(Π(P : Prop). Nat)) : Nat := 0
  reject def BoxPropFn : Box(Π(P : Prop). Nat) := MkBox(λ(P : Prop) : Nat => 0)
  def RefProofFn (f : &(Π(h : ⊤). Nat)) : Nat := 0
  def RefRetFn (f : &(Π(x : &Nat). &Nat)) (y : &Nat) : Unit := (let r = (*f)(y); *r := 1)
  def BoxFn : Box(Π(n : Nat). Nat) := MkBox(λ(n : Nat) : Nat => n)
}

#eval IO.println (run "FnBorrows" FnBorrows).show
#guard (run "FnBorrows" FnBorrows).allAsExpected
#guard (run "FnBorrows" FnBorrows).count == 33

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
