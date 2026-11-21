import Ochr.Examples.Bool
import Ochr.Examples.Nat
import Ochr.Examples.Word
import Ochr.Examples.List
import Ochr.Examples.Fixtures
import Ochr.Examples.Logic
import Ochr.Examples.Box

/-! # 10. Inductive types: lists, trees, and parameters

`inductive D (a : A) … := C₁(f : T, …) | …` declares a type with constructors. A match on a
value of `D` has one arm per constructor, and its pattern variables name the field places
`p.f`, as `S y` names `p.0`. [Split] refines an abstract value to `C(σ₁, …, σₖ)`, and [Rec]
accepts a recursive call on any field. Parameters are uniform (`List(A)`); a constructor
takes them first, written `Cons[Nat](1, Nil[Nat])` or left out when they can be inferred
(D46, D49). A field's type is first-order data: other inductive types, the type itself,
`Nat`, `Unit`, `×` or a parameter, but no function type and no borrow (strict positivity,
D36). Constructor names are unique in a program.

Defined in RULES §8. -/

open Ochr.Test

/-! ## Lists

In-place append and its theorems are the same bare recursion as `AddM`'s, and `LastM` is
the list version of `TailM`. -/

ochr NatLists {
  -- A list of numbers declared here, without `Lists`' `List(A)`: the first inductive type.
  inductive List := Nil | Cons(h : Nat, t : List)

  -- In-place append, and appending `Nil` does nothing.
  def AppendM (xs : &List) (ys : List) : Unit by xs := (
    match *xs {
      Nil => *xs := ys,
      Cons(h, t) => AppendM(&t, ys),
    }
  )

  def AppendMNil (xs : &List) : Id(Unit, AppendM(&*xs, Nil), ()) by xs := (
    match *xs {
      Nil => refl,
      Cons(h, t) => AppendMNil(&t),
    }
  )

  -- Appending a one-element list does something.
  reject def AppendMOne (xs : &List) : Id(Unit, AppendM(&*xs, Cons(0, Nil)), ()) by xs := (
    match *xs {
      Nil => refl,
      Cons(h, t) => AppendMOne(&t),
    }
  )

  -- A borrow of the final `Nil`, and append by writing through it.
  def LastM (xs : &List) : &List by xs := (
    match *xs {
      Nil => xs,
      Cons(h, t) => LastM(&t),
    }
  )

  def AppendM' (xs : &List) (ys : List) : Unit := (
    let r = LastM(xs);
    *r := ys
  )

  def AppendMEq (xs : &List) (ys : List) : Id(Unit, AppendM(xs, ys), AppendM'(xs, ys)) by xs := (
    match *xs {
      Nil => refl,
      Cons(h, t) => AppendMEq(&t, ys),
    }
  )

  -- Constructors are resolved by name, so a name is declared once in a program.
  inductive A := Make(x : Nat)
  reject inductive B := Make(y : Unit)
}


/-! ## Binary search trees

In `InsertM` a comparison decides which subtree is changed. The comparison `Lt(k, v)` is a
sealed program, so a match on it first replaces it by a fresh value.
That the in-place insert is the pure insert is then bare recursion, provided the
replacement also reaches the copies of the comparison that the goal computes later (D34). The size theorem needs one arithmetic lemma, proved in place. -/

ochr Trees uses Bools, Nats, WordType {
  inductive Tree := Leaf | Node(l : Tree, v : Word, r : Tree)

  -- The order on keys: words, which every read copies (D53). The paper's trees define their
  -- own `Lt`, as printed there; it is `Words`' `LtB`.
  def Lt (a : Word) (b : Word) : Bool by a := (
    match a {
      Zero => match b {
        Zero => false,
        Succ _ => true,
      },
      Succ a' => match b {
        Zero => false,
        Succ b' => Lt(a', b'),
      },
    }
  )

  -- In-place insert.
  def InsertM (t : &Tree) (k : Word) : Unit by t := (
    match *t {
      Leaf => *t := Node(Leaf, k, Leaf),
      Node(l, v, r) => (
        let b = Lt(k, v);
        match b {
          true => InsertM(&l, k),
          false => InsertM(&r, k),
        }
      ),
    }
  )

  -- Pure insert.
  def Insert (t : Tree) (k : Word) : Tree by t := (
    match t {
      Leaf => Node(Leaf, k, Leaf),
      Node(l, v, r) => (
        let b = Lt(k, v);
        match b {
          false => Node(l, v, Insert(r, k)),
          true => Node(Insert(l, k), v, r),
        }
      ),
    }
  )

  -- The in-place insert is the pure insert.
  def InsertMEq (t : &Tree) (k : Word) : Id(Unit, InsertM(&*t, k), *t := Insert(*t, k)) by t := (
    match *t {
      Leaf => refl,
      Node(l, v, r) => (
        let b = Lt(k, v);
        match b {
          true => InsertMEq(&l, k),
          false => InsertMEq(&r, k),
        }
      ),
    }
  )

  -- An insert that goes the wrong way is not.
  def InsertMSwap (t : &Tree) (k : Word) : Unit by t := (
    match *t {
      Leaf => *t := Node(Leaf, k, Leaf),
      Node(l, v, r) => (
        let b = Lt(k, v);
        match b {
          false => InsertMSwap(&l, k),
          true => InsertMSwap(&r, k),
        }
      ),
    }
  )

  reject def InsertMSwapEq (t : &Tree) (k : Word) : Id(Unit, InsertMSwap(&*t, k), *t := Insert(*t, k)) by t := (
    match *t {
      Leaf => refl,
      Node(l, v, r) => (
        let b = Lt(k, v);
        match b {
          false => InsertMSwapEq(&l, k),
          true => InsertMSwapEq(&r, k),
        }
      ),
    }
  )

  -- Recursing on the node itself, not on a subtree, is not structural.
  reject def InsertLoop (t : &Tree) (k : Word) : Unit by t := (
    match *t {
      Leaf => (),
      Node(l, v, r) => InsertLoop(t, k),
    }
  )

  -- Inserting grows the size by one. In the `true` arm this follows from the induction
  -- hypothesis, since `Add` recurses on its first argument. The `false` arm needs
  -- `x + S(y) = S(x + y)`, `Nats`' `AddS`, itself proved in place by bare recursion (`AddMS`).
  -- Both arms rewrite with `J`.
  def Size (t : Tree) : Nat by t := (
    match t {
      Leaf => 0,
      Node(l, v, r) => S(Add(Size(l), Size(r))),
    }
  )

  def SizeInsert (t : Tree) (k : Word) : Id(Nat, S(Size(t)), Size(Insert(t, k))) by t := (
    match t {
      Leaf => refl,
      Node(l, v, r) => (
        let b = Lt(k, v);
        match b {
          false =>
            J(
              Nat,
              Add(Size(l), S(Size(r))),
              S(Add(Size(l), Size(r))),
              λ(z : Nat) : Prop => Id(Nat, S(clone(z)), S(Add(Size(clone(l)), Size(Insert(clone(r), k))))),
              AddS(Size(l), Size(r)),
              J(
                Nat,
                S(Size(r)),
                Size(Insert(r, k)),
                λ(z : Nat) : Prop => Id(Nat, S(Add(Size(clone(l)), S(Size(clone(r))))), S(Add(Size(clone(l)), clone(z)))),
                SizeInsert(r, k),
                refl
              )
            ),
          true =>
            J(
              Nat,
              S(Size(l)),
              Size(Insert(l, k)),
              λ(z : Nat) : Prop => Id(Nat, S(S(Add(Size(clone(l)), Size(clone(r))))), S(Add(clone(z), Size(clone(r))))),
              SizeInsert(l, k),
              refl
            ),
        }
      ),
    }
  )

  -- Without the arithmetic lemma the `false` arm does not check ...
  reject def SizeInsertNoLemma (t : Tree) (k : Word) : Id(Nat, S(Size(t)), Size(Insert(t, k))) by t := (
    match t {
      Leaf => refl,
      Node(l, v, r) => (
        let b = Lt(k, v);
        match b {
          false =>
            J(
              Nat,
              S(Size(r)),
              Size(Insert(r, k)),
              λ(z : Nat) : Prop => Id(Nat, S(S(Add(Size(clone(l)), Size(clone(r))))), S(Add(Size(clone(l)), clone(z)))),
              SizeInsertNoLemma(r, k),
              refl
            ),
          true =>
            J(
              Nat,
              S(Size(l)),
              Size(Insert(l, k)),
              λ(z : Nat) : Prop => Id(Nat, S(S(Add(Size(clone(l)), Size(clone(r))))), S(Add(clone(z), Size(clone(r))))),
              SizeInsertNoLemma(l, k),
              refl
            ),
        }
      ),
    }
  )

  -- ... and inserting does not grow the size by two.
  reject def SizeInsertTwo (t : Tree) (k : Word) : Id(Nat, S(S(Size(t))), Size(Insert(t, k))) by t := (
    match t {
      Leaf => refl,
      Node(l, v, r) => SizeInsertTwo(l, k),
    }
  )
}


/-! ## The paper's trees: the pure insert runs the in-place one

The paper (§2, Trees) defines the pure insert as `Add` is defined, by running the in-place
one on a copy, and proves the size theorem about it. `InsertM`, `Insert` and `SizeInsert`
are the paper's text, in its layout, with `Word` keys (D53: a key is only compared, so it is a
copy); `Lt` and `Size` are the ones it assumes, and `AddS` (`Nats`',
`x + S y = S (x + y)`) is proved in place by bare recursion (`AddMS`) and transferred to
`Add` by lending, as the prose says. The in-place insert is the pure one by definition
(`InsertMIsInsert`, by `refl`). -/

ochr InPlaceTrees uses Bools, Nats, WordType {
  inductive Tree := Leaf | Node(l : Tree, v : Word, r : Tree)

  -- The paper's own `Lt`, as `Trees`' (`Words`' `LtB`).
  def Lt (a : Word) (b : Word) : Bool by a := (
    match a {
      Zero => match b { Zero => false, Succ _ => true },
      Succ a' => match b { Zero => false, Succ b' => Lt(a', b') },
    }
  )

  def InsertM (t : &Tree) (k : Word) : Unit by t :=
    match *t { Leaf          => *t := Node(Leaf, k, Leaf),
               Node(l, v, r) => let b = Lt(k, v);
                                match b { true => InsertM(&l, k), false => InsertM(&r, k) } }
  def Insert (t : Tree) (k : Word) : Tree := InsertM(&t, k); t

  def InsertMIsInsert (t : &Tree) (k : Word) : Id(Unit, InsertM(&*t, k), *t := Insert(*t, k)) := refl

  def Size (t : Tree) : Nat by t := (
    match t {
      Leaf => 0,
      Node(l, v, r) => S(Add(Size(l), Size(r))),
    }
  )

  def SizeInsert (t : Tree) (k : Word) : Id(Nat, S(Size(t)), Size(Insert(t, k))) by t :=
    match t { Leaf => refl,
              Node(l, v, r) => let b = Lt(k, v); match b {
                true  => J(Nat, S(Size(l)), Size(Insert(l, k)),
                           λ(z : Nat) : Prop => Id(Nat, S(S(Add(Size(clone(l)), Size(clone(r))))), S(Add(clone(z), Size(clone(r))))),
                           SizeInsert(l, k), refl),
                false => J(Nat, Add(Size(l), S(Size(r))), S(Add(Size(l), Size(r))),
                           λ(z : Nat) : Prop => Id(Nat, S(clone(z)), S(Add(Size(clone(l)), Size(Insert(clone(r), k))))),
                           AddS(Size(l), Size(r)),
                           J(Nat, S(Size(r)), Size(Insert(r, k)),
                             λ(z : Nat) : Prop => Id(Nat, S(Add(Size(clone(l)), S(Size(clone(r))))), S(Add(Size(clone(l)), clone(z)))),
                             SizeInsert(r, k), refl)) } }

  -- The same theorem with D60's `rewrite` instead of `J`, in the paper's layout.
  def SizeInsertRw (t : Tree) (k : Word) : Id(Nat, S(Size(t)), Size(Insert(t, k))) by t :=
    match t { Leaf => refl,
              Node(l, v, r) => let b = Lt(k, v); match b {
                true  => rewrite SizeInsertRw(l, k) in refl,
                false => rewrite SizeInsertRw(r, k) in rewrite AddS(Size(l), Size(r)) in refl } }

  -- Without `AddS` the `false` arm does not check: rewriting with the induction hypothesis
  -- alone leaves `S(Add(Size(l), Size(r)))` against `Add(Size(l), S(Size(r)))`.
  reject def SizeInsertRwNoLemma (t : Tree) (k : Word) : Id(Nat, S(Size(t)), Size(Insert(t, k))) by t :=
    match t { Leaf => refl,
              Node(l, v, r) => let b = Lt(k, v); match b {
                true  => rewrite SizeInsertRwNoLemma(l, k) in refl,
                false => rewrite SizeInsertRwNoLemma(r, k) in refl } }

  -- Inserting does not grow the size by two.
  reject def SizeInsertTwo (t : Tree) (k : Word) : Id(Nat, S(S(Size(t))), Size(Insert(t, k))) by t := (
    match t {
      Leaf => refl,
      Node(l, v, r) => SizeInsertTwo(l, k),
    }
  )
}


/-! ## Parameters: a polymorphic list

`List(A)` is `Lists`'. -/

ochr PolyLists uses Lists {
  -- In-place append on `List(A)`, and appending `Nil` does nothing; `Nil`'s parameter comes
  -- from `AppendM`'s parameter type.
  def AppendM (A : Type) (xs : &List(A)) (ys : List(A)) : Unit by xs := (
    match *xs {
      Nil => *xs := ys,
      Cons(h, t) => AppendM(A, &t, ys),
    }
  )

  def AppendMNil (A : Type) (xs : &List(A)) : Id(Unit, AppendM(A, &*xs, Nil), ()) by xs := (
    match *xs {
      Nil => refl,
      Cons(h, t) => AppendMNil(A, &t),
    }
  )

  reject def AppendMOne (A : Type) (a : A) (xs : &List(A)) :
      Id(Unit, AppendM(A, &*xs, Cons(clone(a), Nil)), ()) by xs := (
    match *xs {
      Nil => refl,
      Cons(h, t) => AppendMOne(A, a, &t),
    }
  )

  -- The pure append, and its theorem from the in-place lemma (as `AddZero'` from
  -- `AddMZero`).
  def Append (A : Type) (xs : List(A)) (ys : List(A)) : List(A) := (
    AppendM(A, &xs, ys);
    xs
  )

  def AppendNil (A : Type) (xs : List(A)) : Id(List(A), Append(A, xs, Nil), xs) := AppendMNil(A, &xs)

  -- Instances: a list of lists, a closed list, and a wrong statement (the two lists have
  -- different constructors, D47).
  def AppendNilL (xs : List(List(Nat))) : Id(List(List(Nat)), Append(List(Nat), xs, Nil), xs) := (
    AppendNil(List(Nat), xs)
  )

  def Closed : Id(List(Nat), Append(Nat, Cons(1, Nil), Nil), Cons(1, Nil)) := AppendNil(Nat, Cons(1, Nil))
  reject def ClosedWrong : Id(List(Nat), Append(Nat, Cons(1, Nil), Nil), Nil) := AppendNil(Nat, Cons(1, Nil))

  -- Parameters written out ...
  def Explicit : List(Nat) := Cons[Nat](1, Nil[Nat])
  reject def ExplicitWrong : List(Nat) := Cons[Unit](1, Nil[Unit])
  def PairP (P : Prop) (Q : Prop) (h : P) (k : Q) : P ∧ Q := Intro[P, Q](h, k)

  -- ... or inferred: from the fields, else from the type the context requires, else it is
  -- an error.
  def Ann : List(Nat) := (
    let xs : List(Nat) = Nil;
    Cons(2, xs)
  )

  reject def NoParam : Nat := (
    let xs = Nil;
    0
  )

  reject def WrongParam : List(Nat) := Cons((), Nil)
  reject def Arity : List := Nil

  -- A constructor value records its parameters, so a closure that captures `Nil` can give
  -- it a type.
  def CapNil (u : Unit) : Nat := (
    let xs = Nil[Nat];
    let f = (λ(n : Nat) : List(Nat) => clone(xs));
    0
  )

  def CapNilAnn (u : Unit) : Nat := (
    let xs : List(Nat) = Nil;
    let f = (λ(n : Nat) : List(Nat) => clone(xs));
    0
  )

  -- No borrows inside data, through a parameter either.
  reject def BorrowList (x : &Nat) : Nat := (
    let l : List(&Nat) = Nil;
    0
  )

  reject def BorrowCons (x : &Nat) : Nat := (
    let l = Cons(x, (Nil : List(Nat)));
    0
  )
}


/-! ## Which parameters are inferred from the fields (D105)

An unwritten parameter of a constructor is inferred from a field's type where it stands, at any
depth, as an argument at a position declared `Prop` or `Type₀`, or declared a type in `Prop` or
`Type₀`: a type of data or a proposition, a number, a data value, a proof (`SC`, `SW`, `SO`,
`SN`). One that stands in the fields' types only at positions of a higher universe is not: a
type in `Type₁` (`ST`), a value of a type in `Type₁` (`SV`), a function into a universe (`SH`).
There it is written, or comes from the type the context expects (each `…w` and `…a`). A field
whose type is the parameter itself still solves it (`Pair`'s `Mk(a, b)`; a field's type is in
`Prop` or `Type₀`, so that parameter is a proposition or a type of data). The
checker decides this from the declarations (`Decide.inferablePos`), because the semantic model
reads a parameter back from a value's type only at the former positions; Lean, which infers
parameters by unification, infers all of these. -/

ochr ParamInference uses Nats {
  -- a type parameter, nested (the case studies' pattern: `Cell.MkC(h, t : SliceOf(R))`)
  inductive Sl (R : Type) := MkSl(c : R)
  inductive CellT (R : Type) := MkCT(h : Nat, t : Sl(R))
  def SC (s : Sl(Nat)) : Nat := (let c = MkCT(0, s); 0)
  def SN (s : Sl(Sl(Nat))) : Nat := (let c = MkSl(s); let d = MkCT(1, c); 0)
  -- a number
  inductive Tag (n : Nat) := MkTag(x : Nat)
  inductive Wrap (n : Nat) := MkW(t : Tag(n))
  def SW (t : Tag(3)) : Nat := (let w = MkW(t); 0)
  inductive Opt2 (n : Nat) := A2(t : Tag(n)) | B2(h : Eq(Nat, n, 3))
  def SO (t : Tag(3)) : Nat := (let w = A2(t); 0)
  -- a function into a universe
  def F0 (x : Nat) : Type := Nat
  inductive HL (f : Π(x : Nat). Type) := MkHL(y : Nat)
  inductive HW (f : Π(x : Nat). Type) := MkHW(t : HL(f))
  reject def SH (t : HL(F0)) : Nat := (let w = MkHW(t); 0)
  def SHw (t : HL(F0)) : Nat := (let w = MkHW[F0](t); 0)
  def SHa (t : HL(F0)) : Nat := (let w : HW(F0) = MkHW(t); 0)
  -- a type in `Type₁`
  inductive LT (T : Type₁) := MkLT(y : Nat)
  inductive WT (T : Type₁) := MkWT(t : LT(T))
  reject def ST (t : LT(Type)) : Nat := (let w = MkWT(t); 0)
  def STw (t : LT(Type)) : Nat := (let w = MkWT[Type](t); 0)
  def STa (t : LT(Type)) : Nat := (let w : WT(Type) = MkWT(t); 0)
  -- a value of a type in `Type₁`
  inductive LV (U : Type₁) (u : U) := MkLV(y : Nat)
  inductive WV (U : Type₁) (u : U) := MkWV(t : LV(U, u))
  reject def SV (t : LV(Type, Nat)) : Nat := (let w = MkWV(t); 0)
  def SVw (t : LV(Type, Nat)) : Nat := (let w = MkWV[Type, Nat](t); 0)
  def SVa (t : LV(Type, Nat)) : Nat := (let w : WV(Type, Nat) = MkWV(t); 0)
  -- which fields determine which parameters, at every field position: `R`'s second field is
  -- of type `A`, which does not determine the phantom `B`; an untyped run (`MkIt`'s body at a
  -- call) then takes `B` from the type its context declares, as typing does (D89)
  inductive Bool2 := T2 | F2
  inductive R (A : Type) (B : Type) := MkR(x : A, y : A)
  def MkIt (a : Nat) : R(Nat, Bool2) := MkR(clone(a), a)
  def UseMkIt : Eq(R(Nat, Bool2), MkIt(1), MkR[Nat, Bool2](1, 1)) := refl
  inductive R2 (A : Type) (B : Type) := MkR2(x : A, y : B)
  def MkIt2 (a : Nat) : R2(Nat, Nat) := MkR2(clone(a), a)
}

-- The values an untyped run builds record their parameters: `MkIt(1)`'s `MkR(1, 1)` records both
-- (before D105 it recorded none: the index read `y : A` as determining `B`).
#guard_msgs (drop warning) in
ochr ParamsRecorded uses ParamInference {
  def At (u : Unit) : Nat := (let v = MkIt(1); let w = MkIt2(1); ?)
}

/-- At the hole of `At`, each binding's name and, for a constructor value, how many parameters it
records. -/
def paramsRecorded : List (String × Nat) :=
  let r := runWith (some Prelude) "ParamsRecorded" ParamsRecorded (located := true)
  match r.rows.find? (·.name == "At") with
  | some row => (row.trace.toList.filterMap fun
      | .note _ _ (.hole _ Ω) => some (Ω.filterMap fun (n, _, v) => match v with
          | .ind _ _ _ ps _ => some (n, ps.length)
          | _ => none)
      | _ => none).headD []
  | none => []

#guard paramsRecorded == [("v", 2), ("w", 2)]

#guard (run "ParamInference" ParamInference).rejectedWith [
  ("SH", "cannot infer the parameter f of MkHW: it stands in its fields' types only at positions of a universe above Type₀"),
  ("ST", "cannot infer the parameter T of MkWT: it stands in its fields' types only at positions of a universe above Type₀"),
  ("SV", "cannot infer the parameter U of MkWV: it stands in its fields' types only at positions of a universe above Type₀")]


/-! ## What goes wrong without strict positivity

A field of function type can mention the type being declared negatively. Then `L(b)`
applies `b`'s own field to `b`, which never terminates, but `K` is typed by [Call-type]
alone and proofs are not run, so `Boom` is a closed proof of `False` (D36). Fields of first-order data are fine. `Empty` is in `Fixtures`. -/

ochr Positivity uses Fixtures {
  -- `Empty`'s own eliminator, by recursion (the attack is about `Empty`, not `Logic`'s `Void`).
  def absurd (e : Empty) : False by e := (
    match e {
      E(e') => absurd(e'),
    }
  )

  reject inductive Bad := MkBad(f : Π(x : Bad). Empty)

  -- twin of Bad: the field is an `Empty` itself, not a function from `Bad` to `Empty`
  inductive BadOk := MkBadOk(f : Empty)

  reject def L (b : Bad) : Empty := (
    match b {
      MkBad(f) => f(b),
    }
  )

  reject def K (b : Bad) : False := absurd(L(b))
  reject def bad : Bad := MkBad(λ(x : Bad) : Empty => L(x))
  reject def Boom : False := K(bad)

  -- twin of L: the field is the `Empty` itself, so no self-application
  def LOk (b : BadOk) : Empty := (
    match b {
      MkBadOk(f) => f,
    }
  )

  -- twin of K: through `LOk`
  def KOk (b : BadOk) : False := absurd(LOk(b))

  -- twin of bad: builds a `BadOk` from a given `Empty`, not from a function
  def badOk (e : Empty) : BadOk := MkBadOk(e)

  -- twin of Boom: proves the true `Empty → False` rather than `False`
  def BoomOk (e : Empty) : False := KOk(badOk(e))
  inductive Pairs := PNil | PCons(hd : Nat × Unit, tl : Pairs)
}


/-! The same, with the function type hidden inside a parameter: a field's parameter
arguments must be first-order too. Positive uses of parameters are fine: a list of the
type itself, and a proof field. `Box(A)` is `Boxes`', `List(A)` is `Lists`', and the empty
type `Void` and `absurdV` are `Logic`'s. -/

ochr PositivityParams uses Logic, Lists, Boxes {
  def unbox (A : Type) (b : Box(A)) : A := (
    match b {
      MkBox(x) => x,
    }
  )

  reject inductive Bad := MkBad(f : Box(Π(x : Bad). Void))

  -- twin of Bad: the boxed type is `Void`, not a function from `Bad`
  inductive BadOk := MkBadOk(f : Box(Void))

  reject def L (b : Bad) : Void := (
    match b {
      MkBad(f) => match f {
        MkBox(g) => g(b),
      },
    }
  )

  reject def K (b : Bad) : False := absurdV(L(b))
  reject def bad : Bad := MkBad(MkBox(λ(x : Bad) : Void => L(x)))
  reject def Boom : False := K(bad)
  reject inductive Neg (A : Type) := MkNeg(f : Π(x : A). Nat)

  -- twin of L: unboxes the `Void` itself, no self-application
  def LOk (b : BadOk) : Void := (
    match b {
      MkBadOk(f) => match f {
        MkBox(g) => g,
      },
    }
  )

  -- twin of K: through `LOk`
  def KOk (b : BadOk) : False := absurdV(LOk(b))

  -- twin of bad: built from a given `Void`, not from a function
  def badOk (v : Void) : BadOk := MkBadOk(MkBox(v))

  -- twin of Boom: proves the true `Void → False` rather than `False`
  def BoomOk (v : Void) : False := KOk(badOk(v))

  -- twin of Neg: the field is first-order data (`A × Nat`), not a function type
  inductive NegOk (A : Type) := MkNegOk(f : A × Nat)
  inductive Rose (A : Type) := Node(v : A, kids : List(Rose(A)))
  inductive Sig (P : Prop) := MkSig(n : Nat, h : P)

  def SigProof (P : Prop) (s : Sig(P)) : P := (
    match s {
      MkSig(n, h) => h,
    }
  )

  def SigAt : Eq(Nat, 1, 1) := SigProof(Eq(Nat, 1, 1), MkSig(3, refl))

  -- Universes are not cumulative: a proposition is not a `Type` parameter.
  reject def PropBox : Type := Box(Eq(Nat, 0, 1))
}


/-! The paper's version (appendix note 4), with `False` directly. -/

ochr PositivityPaper {
  reject inductive Bad := MkBad(f : Π(x : Bad). False)

  -- twin of Bad: the field is `False` itself, not a function from `Bad` to `False`
  inductive BadOk := MkBadOk(f : False)

  reject def L (b : Bad) : False := (
    match b {
      MkBad(f) => f(b),
    }
  )

  reject def Bad4 : False := L(MkBad(λ(x : Bad) : False => L(x)))

  -- twin of L: the field is the `False` itself
  def LOk (b : BadOk) : False := (
    match b {
      MkBadOk(f) => f,
    }
  )

  -- twin of Bad4: proves the true `False → False` rather than `False`
  def Bad4Ok (h : False) : False := LOk(MkBadOk(h))
}

/-! ## A type nested at its own parameter (D107)

Nesting is allowed only at a *nestable* parameter: one the inductive uses only as a whole field
type or at nestable parameters of inductives, never in a type function, an equation or a value,
where its argument may be used negatively (K4). Until D107 the condition was skipped for the type
being declared: while `Q` was checked its entry had no constructors, so the occurrence `Q(Q(A, n),
1)` of `Q` at its own parameter `A` went unchecked, though `Q` passes `A` to `Neg`. `Neg(A, n)` is
`False` at `0` and `A → False` at a successor, and stuck at the generic `n`, so the field is not a
function type there. Then `Q(Unit, 0)` is `Q(Unit, 0) → False` (Curry's paradox), `Delta` is the
diagonal, and `Boom` was a closed proof of `False`: `Delta` is a proof, so its call on its own
encoding is never run. Now the nestable parameters of the type being declared are computed from
its own fields, as the greatest set that the fields use only nestably (a parameter that `Q`'s own
occurrence carries to a parameter outside the set is outside it too). -/

ochr PositivitySelf {
  def Neg (X : Type) (n : Nat) : Prop := (match n { Z => False, S _ => (Π(x : X). False) })
  reject inductive Q (A : Type) (n : Nat) := MkQ(z : Q(Q(A, n), 1), e : Eq(Nat, n, 0)) | Stop(f : Neg(A, n))
  -- twin of Q: `Stop` holds an `A` rather than `Neg(A, n)`, so `A` is nestable in `QOk`
  inductive QOk (A : Type) (n : Nat) := MkQOk(z : QOk(QOk(A, n), 1), e : Eq(Nat, n, 0)) | StopOk(a : A)
  reject def Delta (x : Q(Unit, 0)) : False := (
    match x {
      MkQ(z, e) => match z {
        MkQ(z2, e2) => e2,
        Stop(f) => f(x),
      },
      Stop(f) => f,
    }
  )
  reject def Boom : False := Delta(MkQ[Unit, 0](Stop[Q(Unit, 0), 1](Delta), refl))
  -- twin of Boom: a `QOk(Unit, 0)` holds a `Unit`, not a refutation of itself
  def QOk0 : QOk(Unit, 0) := MkQOk[Unit, 0](StopOk[QOk(Unit, 0), 1](StopOk[Unit, 0](())), refl)
  -- the same through `Prop`: a proposition nested at its own parameter
  def NegP (X : Prop) (n : Nat) : Prop := (match n { Z => False, S _ => (Π(x : X). False) })
  reject inductive QP (A : Prop) (n : Nat) : Prop := MkQP(z : QP(QP(A, n), 1), e : Eq(Nat, n, 0)) | StopP(f : NegP(A, n))
  -- twin of QP: `StopP` holds a proof of `A`
  inductive QPOk (A : Prop) (n : Nat) : Prop := MkQPOk(z : QPOk(QPOk(A, n), 1), e : Eq(Nat, n, 0)) | StopPOk(a : A)
}

#guard (run "PositivitySelf" PositivitySelf).rejectedWith [
  ("Q", "field z of MkQ : Q(Q(A, n), 1): Q occurs at the parameter A of Q, which is not nestable in Q"),
  ("Delta", "unknown"),
  ("Boom", "unknown"),
  ("QP", "field z of MkQP : QP(QP(A, n), 1): QP occurs at the parameter A of QP, which is not nestable in QP")]

/-! The program that found it, as found (with `Bit`, an option type whose "none" is empty at
`B0`, and the diagonal behind a lemma), and the same hole reached through a chain of two
inductives, through a parameter that is a type function, and through a proof field. -/

ochr PositivityCurry {
  inductive Bit := B0 | B1
  inductive Void : Type
  def VF (v : Void) : False := (match v { })
  def FF (b : Bit) : Type := (match b { B0 => Void, B1 => Unit })
  inductive OptB (X : Type) (b : Bit) := NoneB(h : FF(b)) | SomeB(x : X)
  def FB (X : Type) (b : Bit) : Type := (match b { B1 => (Π(x : X). Void), B0 => Unit })
  reject inductive Q (A : Type) (b : Bit) := MkQ(y : FB(A, b), z : OptB(Q(Q(A, b), B1), b))
  reject def Delta (x : Q(Unit, B0)) : Void := (
    match x {
      MkQ(y, z) => match z {
        NoneB(h) => h,
        SomeB(w) => match w {
          MkQ(f, z2) => f(MkQ[Unit, B0](y, SomeB[Q(Q(Unit, B0), B1), B0](MkQ[Q(Unit, B0), B1](f, z2)))),
        },
      },
    }
  )
  reject def Lem (g : Π(x : Q(Unit, B0)). Void) : False :=
    VF(g(MkQ[Unit, B0]((), SomeB[Q(Q(Unit, B0), B1), B0](MkQ[Q(Unit, B0), B1](g, NoneB[Q(Q(Q(Unit, B0), B1), B1), B1](()))))))
  reject def Boom : False := Lem(Delta)
}

#guard (run "PositivityCurry" PositivityCurry).rejectedWith [
  ("Q", "field z of MkQ : OptB(Q(Q(A, b), B1), b): Q occurs at the parameter A of Q, which is not nestable in Q"),
  ("Delta", "unknown"), ("Lem", "unknown"), ("Boom", "unknown")]

ochr PositivityChain {
  inductive Bit := B0 | B1
  inductive Void : Type
  def VF (v : Void) : False := (match v { })
  def FF (b : Bit) : Type := (match b { B0 => Void, B1 => Unit })
  inductive OptB (X : Type) (b : Bit) := NoneB(h : FF(b)) | SomeB(x : X)
  def FB (X : Type) (b : Bit) : Type := (match b { B1 => (Π(x : X). Void), B0 => Unit })
  inductive P (A : Type) (b : Bit) := MkP(y : FB(A, b))
  reject inductive Q (A : Type) (b : Bit) := MkQ(p : P(A, b), z : OptB(Q(Q(A, b), B1), b))
  reject def Delta (x : Q(Unit, B0)) : Void := (
    match x {
      MkQ(p, z) => match z {
        NoneB(h) => h,
        SomeB(w) => match w {
          MkQ(p2, z2) => match p2 {
            MkP(f) => f(MkQ[Unit, B0](p, SomeB[Q(Q(Unit, B0), B1), B0](MkQ[Q(Unit, B0), B1](MkP[Q(Unit, B0), B1](f), z2)))),
          },
        },
      },
    }
  )
  reject def Lem (g : Π(x : Q(Unit, B0)). Void) : False :=
    VF(g(MkQ[Unit, B0](MkP[Unit, B0](()), SomeB[Q(Q(Unit, B0), B1), B0](MkQ[Q(Unit, B0), B1](MkP[Q(Unit, B0), B1](g), NoneB[Q(Q(Q(Unit, B0), B1), B1), B1](()))))))
  reject def Boom : False := Lem(Delta)
}

#guard (run "PositivityChain" PositivityChain).rejectedWith [
  ("Q", "field z of MkQ : OptB(Q(Q(A, b), B1), b): Q occurs at the parameter A of Q, which is not nestable in Q"),
  ("Delta", "unknown"), ("Lem", "unknown"), ("Boom", "unknown")]

ochr PositivityTyFn {
  inductive Bit := B0 | B1
  inductive Void : Type
  def VF (v : Void) : False := (match v { })
  def FF (b : Bit) : Type := (match b { B0 => Void, B1 => Unit })
  inductive OptB (X : Type) (b : Bit) := NoneB(h : FF(b)) | SomeB(x : X)
  def AppB (G : Π(X : Type). Type) (A : Type) (b : Bit) : Type := (match b { B1 => G(A), B0 => Unit })
  def Neg (X : Type) : Type := (Π(x : X). Void)
  reject inductive QG (G : Π(X : Type). Type) (A : Type) (b : Bit) := MkQG(y : AppB(G, A, b), z : OptB(QG(G, QG(G, A, b), B1), b))
  reject def Delta (x : QG(Neg, Unit, B0)) : Void := (
    match x {
      MkQG(y, z) => match z {
        NoneB(h) => h,
        SomeB(w) => match w {
          MkQG(f, z2) => f(MkQG[Neg, Unit, B0](y, SomeB[QG(Neg, QG(Neg, Unit, B0), B1), B0](MkQG[Neg, QG(Neg, Unit, B0), B1](f, z2)))),
        },
      },
    }
  )
  reject def Lem (g : Π(x : QG(Neg, Unit, B0)). Void) : False :=
    VF(g(MkQG[Neg, Unit, B0]((), SomeB[QG(Neg, QG(Neg, Unit, B0), B1), B0](MkQG[Neg, QG(Neg, Unit, B0), B1](g, NoneB[QG(Neg, QG(Neg, QG(Neg, Unit, B0), B1), B1), B1](()))))))
  reject def Boom : False := Lem(Delta)
}

#guard (run "PositivityTyFn" PositivityTyFn).rejectedWith [
  ("QG", "field z of MkQG : OptB(QG(G, QG(G, A, b), B1), b): QG occurs at the parameter A of QG, which is not nestable in QG"),
  ("Delta", "unknown"), ("Lem", "unknown"), ("Boom", "unknown")]

ochr PositivityPropRoute {
  inductive Bit := B0 | B1
  def FFP (b : Bit) : Prop := (match b { B0 => False, B1 => True })
  inductive OptP (X : Type) (b : Bit) := NoneP(h : FFP(b)) | SomeP(x : X)
  def FBP (X : Type) (b : Bit) : Prop := (match b { B1 => (Π(x : X). False), B0 => True })
  reject inductive QP (A : Type) (b : Bit) := MkQP(y : FBP(A, b), z : OptP(QP(QP(A, b), B1), b))
  reject def Delta (x : QP(Unit, B0)) : False := (
    match x {
      MkQP(y, z) => match z {
        NoneP(h) => h,
        SomeP(w) => match w {
          MkQP(f, z2) => f(MkQP[Unit, B0](y, SomeP[QP(QP(Unit, B0), B1), B0](MkQP[QP(Unit, B0), B1](f, z2)))),
        },
      },
    }
  )
  reject def Boom : False := Delta(MkQP[Unit, B0](I, SomeP[QP(QP(Unit, B0), B1), B0](MkQP[QP(Unit, B0), B1](Delta, NoneP[QP(QP(QP(Unit, B0), B1), B1), B1](I)))))
}

#guard (run "PositivityPropRoute" PositivityPropRoute).rejectedWith [
  ("QP", "field z of MkQP : OptP(QP(QP(A, b), B1), b): QP occurs at the parameter A of QP, which is not nestable in QP"),
  ("Delta", "unknown"), ("Boom", "unknown")]

/-! The nestable parameters of an inductive declared earlier are computed the same way, as the
greatest set its fields use only nestably, its own occurrences counted at their positions (D107).
Before, any parameter an inductive's own occurrence carried was taken to be nestable, wherever
it carried it: `E`'s `B` reaches only `E(B, A, 1)`, at the position of `A`, which `E` passes to
`Neg`, so `B` is not nestable, and `Bad` nested at it is `Bad → False`. -/

ochr PositivitySwap {
  def Neg (X : Type) (n : Nat) : Prop := (match n { Z => False, S _ => (Π(x : X). False) })
  inductive E (A : Type) (B : Type) (n : Nat) := MkE(z : E(B, A, 1), e : Eq(Nat, n, 0)) | StopE(f : Neg(A, n))
  reject inductive Bad := MkBad(e : E(Unit, Bad, 0))
  -- twin of Bad: `Bad` at no parameter of `E`
  inductive BadOk := MkBadOk(e : E(Unit, Unit, 0))
  reject def Delta (x : Bad) : False := (
    match x {
      MkBad(e) => match e {
        MkE(z, h) => match z {
          MkE(z2, h2) => h2,
          StopE(f) => f(x),
        },
        StopE(f) => f,
      },
    }
  )
  reject def Boom : False := Delta(MkBad(MkE[Unit, Bad, 0](StopE[Bad, Unit, 1](Delta), refl)))
  -- a swap that keeps both parameters nestable (the greatest set, not "the same position")
  inductive Alt (A : Type) (B : Type) := ANil | ACons(a : A, rest : Alt(B, A))
  inductive Zig := MkZig(z : Alt(Zig, Nat))
}

#guard (run "PositivitySwap" PositivitySwap).rejectedWith [
  ("Bad", "field e of MkBad : E(Unit, Bad, 0): Bad occurs at the parameter B of E, which is not nestable in E"),
  ("Delta", "unknown"), ("Boom", "unknown")]

/-! Finding 1 as the data model's battery states it (with `Void`, and the diagonal behind a lemma). -/

ochr PositivitySecondHole {
  inductive Void : Type
  def VF (v : Void) : False := (match v { })
  def Neg (X : Type) (n : Nat) : Type := (match n { Z => Void, S(k) => (Π(x : X). Void) })
  inductive E (A : Type) (B : Type) (n : Nat) := MkE(z : E(B, A, 1), e : Eq(Nat, n, 0)) | StopE(f : Neg(A, n))
  reject inductive Bad := MkBad(e : E(Unit, Bad, 0))
  reject def Lem (g : Π(x : Bad). Void) : False :=
    VF(g(MkBad(MkE[Unit, Bad, 0](StopE[Bad, Unit, 1](g), refl))))
  reject def Delta (x : Bad) : Void := (
    match x {
      MkBad(e) => match e {
        MkE(z, h) => match z {
          MkE(z2, h2) => match h2 { },
          StopE(f) => f(MkBad(MkE[Unit, Bad, 0](StopE[Bad, Unit, 1](f), h))),
        },
        StopE(f) => match f { },
      },
    }
  )
  reject def Boom : False := Lem(Delta)
}

#guard (run "PositivitySecondHole" PositivitySecondHole).rejectedWith [
  ("Bad", "field e of MkBad : E(Unit, Bad, 0): Bad occurs at the parameter B of E, which is not nestable in E"),
  ("Lem", "unknown"), ("Delta", "unknown"), ("Boom", "unknown")]

/-! Other routes from a declared type to a negative position, each rejected for its reason: through
a chain of inductives (at a computed value parameter, under `Box`), a type function at the type
itself (directly, under `Box`, at an index field, at a nested occurrence), an equation, a borrow,
a parameter that is a type function (applied in a field, applied by a global, given a lambda that
mentions the type). A value parameter whose type is a type parameter, with the type nested at it,
is positive and accepted. -/

ochr PositivityRoutes {
  inductive Void : Type
  def Neg (X : Type) (n : Nat) : Prop := (match n { Z => False, S _ => (Π(x : X). False) })
  def NegV (X : Type) (n : Nat) : Type := (match n { Z => Unit, S _ => (Π(x : X). Void) })
  inductive Box (A : Type) := MkBox(x : A)
  inductive F (A : Type) (n : Nat) := MkF(f : Neg(A, n))
  inductive E1 (A : Type) := MkE1(x : F(A, 1))
  inductive E2 (A : Type) (n : Nat) := MkE2(x : F(A, n))
  inductive E3 (A : Type) := MkE3(x : Box(F(A, 1)))
  reject inductive Bad1 := MkBad1(e : E1(Bad1))
  reject inductive Bad2 := MkBad2(e : E2(Bad2, 0))
  reject inductive Bad3 := MkBad3(e : E3(Bad3))
  -- twin of Bad1–Bad3: the type nested at `Box`, which keeps its parameter
  inductive Ok1 := MkOk1(e : Box(Ok1)) | Nil1
  reject inductive Bad4 := MkBad4(f : Neg(Bad4, 1))
  reject inductive Bad5 := MkBad5(b : Box(NegV(Bad5, 1)))
  reject inductive Bad6 := MkBad6(n : Nat, f : Neg(Bad6, n))
  reject inductive Bad7 (n : Nat) := MkBad7(f : Neg(Box(Bad7(n)), n))
  reject inductive Bad8 := MkBad8(b : Bad8, e : Eq(Bad8, b, b))
  reject inductive Bad9 := MkBad9(r : &Bad9)
  reject inductive H1 (G : Π(x : Nat). Type) := MkH1(x : G(0))
  def App (G : Π(X : Type). Type) (A : Type) : Type := G(A)
  inductive H2 (G : Π(X : Type). Type) (A : Type) := MkH2(x : App(G, A))
  def NegT (X : Type) : Type := Π(x : X). Void
  reject inductive Bad10 := MkBad10(h : H2(NegT, Bad10))
  reject inductive Bad11 := MkBad11(h : H2(λ(X : Type) : Type => (Π(x : Bad11). Void), Unit))
  -- twin of Bad10, Bad11: `H2` given the type at no parameter
  inductive Ok10 := MkOk10(h : H2(NegT, Unit))
  inductive G1 (A : Type) (a : A) := MkG1(x : A)
  inductive T1 := Leaf1 | Node1(t : T1, g : G1(T1, t))
}

#guard (run "PositivityRoutes" PositivityRoutes).rejectedWith [
  ("Bad1", "field e of MkBad1 : E1(Bad1): Bad1 occurs at the parameter A of E1, which is not nestable in E1"),
  ("Bad2", "field e of MkBad2 : E2(Bad2, 0): Bad2 occurs at the parameter A of E2, which is not nestable in E2"),
  ("Bad3", "field e of MkBad3 : E3(Bad3): Bad3 occurs at the parameter A of E3, which is not nestable in E3"),
  ("Bad4", "field f of MkBad4 : Neg(Bad4, 1): fields are first-order data"),
  ("Bad5", "field b of MkBad5 : Box(NegV(Bad5, 1)): fields are first-order data"),
  ("Bad6", "field f of MkBad6 : Neg(Bad6, n): fields are first-order data"),
  ("Bad7", "field f of MkBad7 : Neg(Box(Bad7(n)), n): fields are first-order data"),
  ("Bad8", "field e of MkBad8 : Eq(Bad8, b, b): fields are first-order data"),
  ("Bad9", "field r of MkBad9: no borrows inside data"),
  ("H1", "field x of MkH1 : G(0): fields are first-order data"),
  ("Bad10", "field h of MkBad10 : H2(NegT, Bad10): Bad10 occurs at the parameter A of H2, which is not nestable in H2"),
  ("Bad11", "field h of MkBad11 : H2(")]

/-! While a declaration is checked, its entry in Σ has no constructors yet, and a reader of that
entry would answer as if the type were empty (D107). A value argument in a field type may be any
term over the earlier fields not mentioning the type, and a match with no arms names no
constructor, so `E` was accepted with a field type that is ill-typed once `E` has its
constructors. Now any term that reads the constructors of the type being declared (a match on an
earlier field of it, with or without arms, by type for a proposition, a field projection of it,
one of its constructors) is rejected for that reason; a decision that reads them and cannot
reject answers conservatively (not a copy, not a subsingleton, no single constructor). -/

ochr PositivityDeclaring uses Lists {
  inductive W (h : False) := MkW
  inductive Tag (n : Nat) := MkTag
  -- a match with no arms on an earlier field of the type, of data and of a proposition (by type)
  reject inductive E := Leaf | Node(b : E, w : W(let k : False = match b {}; k))
  reject inductive EP : Prop := LeafP | NodeP(b : EP, w : W(let k : False = match b {}; k))
  -- the same through a list built without naming the type
  reject inductive EL := LeafL | NodeL(b : EL, w : W(let l = Cons(b, Nil); match l { Nil => (let k : False = match b {}; k), Cons(h, t) => (let k : False = match h {}; k) }))
  -- a match with arms, a field projection, a constructor of the type being declared
  reject inductive EA := LeafA | NodeA(b : EA, t : Tag(match b { LeafA => 0, NodeA(c, u) => 1 }))
  reject inductive EJ := NodeJ(b : EJ, t : Tag(let x = b.0; 0))
  reject inductive EC := LeafC | NodeC(b : EC, t : Tag(let x = LeafC; 0))
  -- an earlier field of the type read twice: it is not known to be a copy
  reject inductive ED := LeafD | NodeD(b : ED, t : Tag(let x = b; let y = b; 0))
  -- twins: what reads no constructor of the type being declared is accepted
  inductive EOk (h : False) := LeafOk | NodeOk(b : EOk(h), w : W(let k : False = match h {}; k))
  inductive EOnce := LeafO | NodeO(b : EOnce, t : Tag(let x = b; 0))
  inductive EClone := LeafCl | NodeCl(b : EClone, t : Tag(let x = clone(b); 0))
  -- a copy declaration counts the type itself as a copy (D53), whatever its entry says
  inductive Box (A : Type) := MkBox(x : A)
  copy inductive ECopy := LeafCp | NodeCp(b : Box(ECopy))
}

#guard (run "PositivityDeclaring" PositivityDeclaring).rejectedWith [
  ("E", "a match on b reads the constructors of E, which are not known while E is declared (D107)"),
  ("EP", "a match on b reads the constructors of EP, which are not known while EP is declared (D107)"),
  ("EL", "a match on l.h reads the constructors of EL, which are not known while EL is declared (D107)"),
  ("EA", "a match on b reads the constructors of EA, which are not known while EA is declared (D107)"),
  ("EJ", "b.0 reads the constructors of EJ, which are not known while EJ is declared (D107)"),
  ("EC", "the constructor LeafC reads the constructors of EC, which are not known while EC is declared (D107)"),
  ("ED", "[Read] b was moved out or its borrow ended")]

/-! Nested declarations that stay accepted: each nests the type at a parameter that the inner
inductive uses only as a whole field type or at nestable parameters, its own occurrences
included (`DD(DD(A))`, `Box(BB(Box(A)))`, `List(RN(Duo(A, A)))`); `HN` shifts a large value
parameter along the unfolding while nesting itself at `A`. With a recursive proposition as a
field, a type function returning data, and a type function at a parameter that is not nested.
The data model's construction models each (D107's battery). -/

ochr PositivityKeep uses Nats, Lists, Bools {
  inductive Duo (A : Type) (B : Type) := MkDuo(fst : A, snd : B)
  inductive Box (A : Type) := MkBox(x : A)
  inductive DD (A : Type) := DLeaf | DNode(x : DD(DD(A)))
  inductive RN (A : Type) := NodeN(a : A, kids : List(RN(Duo(A, A))))
  inductive BB (A : Type) := BLeaf(a : A) | BNode(b : Box(BB(Box(A))))
  inductive RP (A : Type) := NodeP(a : A, kids : List(Duo(RP(A), Nat)))
  inductive NN (A : Type) := NNode(kids : List(List(NN(A))))
  def App0 (f : Π(x : Nat). Type) : Type := f(0)
  inductive HN (f : Π(x : Nat). Type) (A : Type) := HB(a : A) | HS(y : App0(f), r : HN(λ(x : Nat) : Type => f(S(x)), HN(f, A)))
  inductive Ev (n : Nat) : Prop := EvZ(h : Eq(Nat, n, 0)) | EvSS(m : Nat, h : Ev(m), e : Eq(Nat, n, S(S(m))))
  inductive WithEv := MkWE(n : Nat, p : Ev(n))
  def EvT (b : Bool) : Type := (match b { false => Nat, true => List(Nat) })
  inductive TF := MkTF(b : Bool, x : EvT(b))
  def FBB (X : Type) (b : Bool) : Type := (match b { true => (Π(x : X). Nat), false => Unit })
  inductive FBox (A : Type) (b : Bool) := MkFBox(y : FBB(A, b))
  -- nested at the nestable parameters of the battery's own types
  inductive UseDD := MkUseDD(d : DD(UseDD)) | EndDD
  inductive UseBB := MkUseBB(b : BB(UseBB)) | EndBB
  inductive UseHN := MkUseHN(h : HN(λ(x : Nat) : Type => Nat, UseHN)) | EndHN
  -- and not at `FBox`'s, which it passes to a type function
  reject inductive UseFBox := MkUseFBox(b : FBox(UseFBox, true))
}

#guard (run "PositivityKeep" PositivityKeep).rejectedWith [
  ("UseFBox", "field b of MkUseFBox : FBox(UseFBox, true): UseFBox occurs at the parameter A of FBox, which is not nestable in FBox")]

/-! The data model's probes of nested and large declarations (D107's battery, from the data-model
lanes): each stays accepted, and each rejection keeps its reason. -/

ochr PositivityProbesNest uses Nats, Lists, Bools {
  inductive Rose (A : Type) := Node(a : A, kids : List(Rose(A)))
  -- recursion on a forest through the head tree's own forest
  def CountF (f : List(Rose(Nat))) : Nat by f := (
    match f {
      Nil => 0,
      Cons(t, rest) => match t {
        Node(a, k) => S(CountF(k)),
      },
    }
  )
  def F3 : Eq(Nat, CountF(Cons(Node(1, Cons(Node(2, Cons(Node(3, Nil), Nil)), Nil)), Nil)), 3) := refl
  reject def F2 : Eq(Nat, CountF(Cons(Node(1, Cons(Node(2, Cons(Node(3, Nil), Nil)), Nil)), Nil)), 2) := refl
  -- a field compared with a parameter, at a parameter type, instantiated at itself
  inductive Single (A : Type) (a : A) := MkS(x : A, e : Eq(A, x, a))
  def S1 : Single(Nat, 0) := MkS(0, refl)
  def S2 : Single(Single(Nat, 0), S1) := MkS(S1, refl)
  -- a type-function field reading an earlier field of declared data type
  def BF (b : Bool) : Type := (match b { false => Nat, true => Unit })
  inductive BW := MkBW(b : Bool, x : BF(b))
  def BW1 : BW := MkBW(true, ())
  def BW0 : BW := MkBW(false, 5)
  -- a type-function field computing to a function type at an instance
  def BG (b : Bool) : Type := (match b { false => Nat, true => (Π(n : Nat). Nat) })
  inductive BH := MkBH(b : Bool, x : BG(b))
  -- W-type shapes: a field that is a function into the declared type (controls)
  reject inductive WT := WLeaf | WNode(f : Π(n : Nat). WT)
  def FnTy (A : Type) : Type := (Π(n : Nat). A)
  reject inductive WT2 := WLeaf2 | WNode2(f : FnTy(WT2))
}

#guard (run "PositivityProbesNest" PositivityProbesNest).rejectedWith [
  ("F2", "the body of F2 has type ⊤, but the goal is False"),
  ("WT", "field f of WNode : Π(n : Nat). WT: fields are first-order data"),
  ("WT2", "field f of WNode2 : FnTy(WT2): fields are first-order data")]

ochr PositivityProbesLarge uses Nats, Lists, WordType {
  -- an equation between parameters of a type of sort `Type₁`
  inductive TEq (U : Type₁) (a : U) (b : U) := MkTEq(h : Eq(U, a, b))
  def te : TEq(Type, Word, Word) := MkTEq[Type, Word, Word](refl)
  def te2 : TEq(Π(x : Word). Type, λ(x : Word) : Type => Word, λ(y : Word) : Type => Word) :=
    MkTEq[Π(x : Word). Type, λ(x : Word) : Type => Word, λ(y : Word) : Type => Word](refl)
  reject def te3 : TEq(Π(x : Word). Type, λ(x : Word) : Type => Word, λ(y : Word) : Type => Unit) :=
    MkTEq[Π(x : Word). Type, λ(x : Word) : Type => Word, λ(y : Word) : Type => Unit](refl)
  -- a large type through a universe parameter
  def IdT (A : Type) (x : A) : A := x
  def te4 : TEq(Type, Word, Word) := IdT(TEq(Type, Word, Word), te)
  -- type functions taking, and applying, a large parameter in a field type
  def Pick (U : Type₁) (a : U) : Type := Word
  inductive LP (U : Type₁) (a : U) := MkLP(x : Pick(U, a))
  def App0 (f : Π(x : Word). Type) : Type := f(Zero)
  inductive HL3 (f : Π(x : Word). Type) := MkHL3(y : App0(f))
  def h3 : HL3(λ(x : Word) : Type => Word) := MkHL3[λ(x : Word) : Type => Word](Zero)
  reject def h3bad : HL3(λ(x : Word) : Type => Unit) := MkHL3[λ(x : Word) : Type => Unit](Zero)
  inductive H (f : Π(x : Word). Type) := HB | HS(y : App0(f), r : H(λ(x : Word) : Type => f(Succ(x))))
  -- the residual: a field type applying a function to parameter-typed data, used at itself
  inductive RV (A : Type) := MkRV(xs : List(A), v : Eq(Word, LenL(A, xs), LenL(A, xs)))
  def rv0 : RV(Nat) := MkRV[Nat](Nil, refl)
  def rv1 : RV(RV(Nat)) := MkRV[RV(Nat)](Cons(rv0, Nil), refl)
}

#guard (run "PositivityProbesLarge" PositivityProbesLarge).rejectedWith [
  ("te3", "field h of MkTEq has type ⊤, expected Eq(Π(x : Word). Type"),
  ("h3bad", "field y of MkHL3 has type Word, expected Unit")]

ochr PositivityProbesAdv uses Nats, Lists, WordType {
  inductive Tag (n : Word) := MkTag(x : Word)
  reject def TagNe (h : Eq(Type, Tag(Zero), Tag(Succ(Zero)))) : False := h
  reject def ListNe (h : Eq(Type, List(Word), List(Unit))) : False := h
  inductive PH (U : Type₁) := MkPH
  reject def PHNe (h : Eq(Type, PH(Type), PH(Prop))) : False := h
  inductive TEq (U : Type₁) (a : U) (b : U) := MkTEq(h : Eq(U, a, b))
  reject def TEqNe (h : Eq(Type, TEq(Type, Word, Word), TEq(Type, Unit, Unit))) : False := h
  reject def TEqNe2 (h : Eq(Type, TEq(Type, Word, Word), TEq(Π(x : Word). Type, λ(x : Word) : Type => Word, λ(x : Word) : Type => Word))) : False := h
  inductive TagA (n : Word) := MkTA(x : Word)
  inductive TagB (n : Word) := MkTB(x : Word)
  reject def TagAB (h : Eq(Type, TagA(Zero), TagB(Zero))) : False := h
  inductive RE (A : Type) := MkRE(xs : List(A), v : Eq(Word, LenL(A, xs), Succ(Zero)))
  def re0 : RE(Nat) := MkRE[Nat](Cons(0, Nil), refl)
  def re1 : RE(RE(Nat)) := MkRE[RE(Nat)](Cons(re0, Nil), refl)
  reject def reBad : RE(Nat) := MkRE[Nat](Nil, refl)
  reject inductive RoseL (A : Type) := NodeL(kids : List(RoseL(A)), v : Eq(Word, LenL(RoseL(A), kids), LenL(RoseL(A), kids)))
  inductive FP (f : Π(x : Word). Word) := MkFP(y : Word, e : Eq(Word, f(y), y))
  def App0 (f : Π(x : Word). Type) : Type := f(Zero)
  inductive H (f : Π(x : Word). Type) := HB | HS(y : App0(f), r : H(λ(x : Word) : Type => f(Succ(x))))
  def hh : H(λ(x : Word) : Type => Word) := HS[λ(x : Word) : Type => Word](Zero, HB)
  def AppU (U : Type₁) (F : Π(x : U). Type) (a : U) : Type := F(a)
  reject inductive LB (U : Type₁) (F : Π(x : U). Type) (a : U) := MkLB(y : AppU(U, F, a))
  def MG (G : Π(X : Type). Word) : Type := (match G(Word) { Zero => Word, Succ(k) => Unit })
  inductive MM (G : Π(X : Type). Word) := MkMM(y : MG(G))
  def mm0 : MM(λ(X : Type) : Word => Zero) := MkMM[λ(X : Type) : Word => Zero](Zero)
  reject def mm0Bad : MM(λ(X : Type) : Word => Zero) := MkMM[λ(X : Type) : Word => Zero](())
  def mm1 : MM(λ(X : Type) : Word => Succ(Zero)) := MkMM[λ(X : Type) : Word => Succ(Zero)](())
}

#guard (run "PositivityProbesAdv" PositivityProbesAdv).rejectedWith [
  ("TagNe", "the body of TagNe has type Eq(Type, Tag(Zero), Tag(Succ(Zero))), but the goal is False"),
  ("ListNe", "the body of ListNe has type Eq(Type, List(Word), List(Unit)), but the goal is False"),
  ("PHNe", "the body of PHNe has type Eq(Type, PH(Type), PH(Prop)), but the goal is False"),
  ("TEqNe", "the body of TEqNe has type Eq(Type, TEq(Type, Word, Word), TEq(Type, Unit, Unit)), but the goal is False"),
  ("TEqNe2", "the body of TEqNe2 has type Eq(Type, TEq(Type, Word, Word), TEq(Π(x : Word). Type"),
  ("TagAB", "the body of TagAB has type Eq(Type, TagA(Zero), TagB(Zero)), but the goal is False"),
  ("reBad", "field v of MkRE has type ⊤, expected False"),
  ("RoseL", "field v of NodeL : Eq(Word, LenL(RoseL(A), kids), LenL(RoseL(A), kids)): fields are first-order data"),
  ("LB", "κ is not a type: its declared type is not a sort"),
  ("mm0Bad", "field y of MkMM has type Unit, expected Word")]

/-! The battery's controls: a later declaration nested at a parameter passed to a type function,
and large elimination from a proposition that is not a subsingleton (D45). -/

ochr PositivityControls uses Nats, Bools {
  inductive Void : Type
  def FB (X : Type) (b : Bool) : Type := (match b { true => (Π(x : X). Void), false => Unit })
  inductive P (A : Type) (b : Bool) := MkP(y : FB(A, b))
  -- a later declaration nested at a parameter passed to a type function (K4)
  reject inductive E := MkE(p : P(E, true))
  -- large elimination from a proposition with two constructors, or a data field (D45)
  inductive POr : Prop := PL | PR
  reject def f (p : POr) : Bool := (match p { PL => false, PR => true })
  inductive PS : Prop := MkPS(n : Nat)
  reject def get (p : PS) : Nat := (match p { MkPS(n) => n })
}

#guard (run "PositivityControls" PositivityControls).rejectedWith [
  ("E", "field p of MkE : P(E, true): E occurs at the parameter A of P, which is not nestable in P"),
  ("f", "[D45] a match on a proof of POr returns a non-proof"),
  ("get", "[D45] a match on a proof of PS returns a non-proof")]

/-! ## Decisions read an unknown by the reading frozen when it was made (D96)

A decision about an abstract value (is it a proof, a type and of which sort, a function of which
class) reads its declared reading, frozen when the value is made, never its type, which a
refinement can rewrite. These programs make an unknown whose type is a type parameter or a stuck
type (`TP(n)`, `TS(n)`, `TF2(n)`), refined by a split to a proposition, a sort or a function type,
and read it where a decision does, at the generic call and at closed calls. Each takes the same
verdict as before D96, and the generic call and the closed calls agree. A function type computed
by a type function whose arms differ in class is rejected before any decision reads it (D77), and
so is a call through a type that is not known to be a function type. -/

ochr FrozenReadings uses Nats, Logic {
  -- a type function whose value is a sort at one index and a function type at another
  def TS (n : Nat) : Type₁ := match n { Z => Prop, S _ => Type }
  def TF (n : Nat) : Type := match n { Z => Π(m : Nat). Nat, S _ => Nat }
  def TP (n : Nat) : Prop := match n { Z => True, S _ => Eq(Nat, 0, 0) }
  -- 1. type parameter at a proposition: proof-ness of an embedded unknown after a split
  def KeepP (P : Prop) (h : P) (k : Nat) : P := match k { Z => h, S _ => h }
  def KeepPRun : True := KeepP(True, I, 1)
  -- 2. a stuck proposition refined by a split: erasure and proof-ness of `h`
  def KeepTP (n : Nat) (h : TP(n)) (k : Nat) : TP(n) := (let r = match k { Z => h, S _ => h }; r)
  def KeepTPRun0 : TP(0) := KeepTP(0, I, 1)
  def KeepTPRun1 : TP(1) := KeepTP(1, refl, 0)
  def KeepTPSplit (n : Nat) (h : TP(n)) : TP(n) := match n { Z => KeepTP(Z, h, 1), S m => KeepTP(S(m), h, 0) }
  -- 3. a stuck function type: a call's class through an unknown function after a split
  reject def CallTF (n : Nat) (f : TF(n)) : Nat := match n { Z => f(1), S _ => 0 }
  reject def CallTFRun : Nat := CallTF(0, λ(m : Nat) : Nat => m)
  reject def KeepTF (n : Nat) (f : TF(n)) (k : Nat) : TF(n) := (let r = match k { Z => f, S _ => f }; r)
  reject def KeepTFSplit (n : Nat) (f : TF(n)) : Nat := match n { Z => (let g = KeepTF(Z, f, 1); g(2)), S _ => 0 }
  reject def KeepTFSplitRun : Nat := KeepTFSplit(0, λ(m : Nat) : Nat => m)
  -- 3b. a stuck function type with one class: an unknown function passed to a stuck call, whose
  -- sealed program re-runs after the split refines its type to a Π-type
  def TF2 (n : Nat) : Type := match n { Z => Π(m : Nat). Nat, S _ => Π(m : Nat). Nat }
  def ApplyAt (k : Nat) (f : Π(m : Nat). Nat) : Nat := match k { Z => f(0), S _ => f(1) }
  reject def CallTF2 (n : Nat) (k : Nat) (f : TF2(n)) : Nat := (let r = ApplyAt(k, f); match n { Z => r, S _ => r })
  reject def CallTF2Run : Nat := CallTF2(0, 1, λ(m : Nat) : Nat => m)
  def CallTF2Split (n : Nat) (f : TF2(n)) : Nat := match n { Z => (let g = f; g(3)), S _ => f(4) }
  def CallTF2SplitRun : Nat := CallTF2Split(0, λ(m : Nat) : Nat => m)
  -- 3c. an unknown proposition-valued function: its calls are proofs on both paths
  def TQ (n : Nat) : Type₁ := match n { Z => Π(m : Nat). Prop, S _ => Π(m : Nat). Prop }
  reject def CallTQ (n : Nat) (q : TQ(n)) (k : Nat) : Prop := (let r = match k { Z => q(0), S _ => q(1) }; match n { Z => r, S _ => r })
  reject def CallTQRun : Prop := CallTQ(0, λ(m : Nat) : Prop => True, 1)
  -- 4. a stuck sort: a value whose type is `TS(n)`, a proposition at 0 and a type at 1
  def KeepTS (n : Nat) (x : TS(n)) (k : Nat) : TS(n) := (let r = match k { Z => x, S _ => x }; r)
  def KeepTSSplit (n : Nat) (x : TS(n)) : TS(n) := match n { Z => KeepTS(Z, x, 1), S m => KeepTS(S(m), x, 0) }
  def KeepTSRun0 : Prop := KeepTSSplit(0, True)
  def KeepTSRun1 : Type := KeepTSSplit(1, Nat)
  -- 5. a type parameter at a type of types
  def IdT (A : Type₁) (x : A) (k : Nat) : A := (let r = match k { Z => x, S _ => x }; r)
  def IdTProp : Prop := IdT(Prop, True, 1)
  def IdTType : Type := IdT(Type, Nat, 0)
  -- 6. a statement over the refined unknown: Id of two runs that keep `h`
  def StmtTP (n : Nat) (h : TP(n)) : Prop := match n { Z => Id(TP(Z), KeepTP(Z, h, 0), KeepTP(Z, h, 1)), S _ => True }
}

#guard (run "FrozenReadings" FrozenReadings).rejectedWith [
  ("CallTF", "[D77]"), ("CallTFRun", "unknown constant CallTF"),
  ("KeepTF", "[D63]"), ("KeepTFSplit", "[D77]"), ("KeepTFSplitRun", "unknown constant KeepTFSplit"),
  ("CallTF2", "argument 2 (f) has type ⌈TF2(σ0)⌉, expected Π(m : Nat). Nat"), ("CallTF2Run", "unknown constant CallTF2"),
  ("CallTQ", "not a function type"), ("CallTQRun", "unknown constant CallTQ")]
