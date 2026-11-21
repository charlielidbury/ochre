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
