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

/-! ## The untyped run hands a hint exactly where the typed check does (D124)

A constructor whose parameters are not written takes them from its hint, the type its position
expects, before its fields (D46, D89). The typed check hands a hint only at some positions: a call's
argument, a field and an assigned value when the term is a constructor (or an embedded value, a
`rewrite`, a hole), an ascription's term, and in tail position the goal. The untyped run, an
instance's run of checked code, handed hints by another test (D89's `needsCtx`: wherever the term
needed its context), and the tail of a `let` or a `;` and a match's arms got the hint whatever their
position. So a run of checked code could read a hint its check never had. Now the untyped run hands
a hint exactly where the typed check does. `UntypedHints` is the differential table: a bare
constructor `X` (`N`, which needs its hint; `C(n, N)`, whose fields determine it; `C[Nat](n, N[Nat])`,
written) under a wrapper (bare `b`, a `let`'s tail `l`, a `;`'s tail `s`, a match's arms `m`) at a
position (`T` the end of a body, `F` a field of a constructor with no parameter, `G` a field of
`C`, `A` a call's argument, `D` a `let` with a declared type, `S` an assigned value, `K` an
ascription as an argument, `U` a dropped argument), each a generic definition `G…` (the typed
check) and its closed instance `I…` (the untyped run of the body at a call) with its value by
`refl`; then a match on a proof in tail position, a body that needs no hint, and `J`. Every generic
definition and its instance have the same verdict, before and after. -/

ochr UntypedHints uses Logic, Nats {
  reject def Ctl : False := ()
  inductive L (A : Type) := N | C(h : A, t : L(A))
  inductive W := MkW(l : L(Nat))
  def IdL (l : L(Nat)) : L(Nat) := l
  def Len (l : L(Nat)) : Nat := 0
  def GTbN (n : Nat) : L(Nat) := N
  def ITbN : Eq(L(Nat), GTbN(3), N[Nat]) := refl
  def GTbC (n : Nat) : L(Nat) := C(clone(n), N)
  def ITbC : Eq(L(Nat), GTbC(3), C[Nat](3, N[Nat])) := refl
  def GTbW (n : Nat) : L(Nat) := C[Nat](clone(n), N[Nat])
  def ITbW : Eq(L(Nat), GTbW(3), C[Nat](3, N[Nat])) := refl
  def GTlN (n : Nat) : L(Nat) := (let y = Z; N)
  def ITlN : Eq(L(Nat), GTlN(3), N[Nat]) := refl
  def GTlC (n : Nat) : L(Nat) := (let y = Z; C(clone(n), N))
  def ITlC : Eq(L(Nat), GTlC(3), C[Nat](3, N[Nat])) := refl
  def GTlW (n : Nat) : L(Nat) := (let y = Z; C[Nat](clone(n), N[Nat]))
  def ITlW : Eq(L(Nat), GTlW(3), C[Nat](3, N[Nat])) := refl
  def GTsN (n : Nat) : L(Nat) := (Z; N)
  def ITsN : Eq(L(Nat), GTsN(3), N[Nat]) := refl
  def GTsC (n : Nat) : L(Nat) := (Z; C(clone(n), N))
  def ITsC : Eq(L(Nat), GTsC(3), C[Nat](3, N[Nat])) := refl
  def GTsW (n : Nat) : L(Nat) := (Z; C[Nat](clone(n), N[Nat]))
  def ITsW : Eq(L(Nat), GTsW(3), C[Nat](3, N[Nat])) := refl
  def GTmN (n : Nat) : L(Nat) := match clone(n) { Z => N, S k => N }
  def ITmN : Eq(L(Nat), GTmN(3), N[Nat]) := refl
  def GTmC (n : Nat) : L(Nat) := match clone(n) { Z => C(clone(n), N), S k => C(clone(n), N) }
  def ITmC : Eq(L(Nat), GTmC(3), C[Nat](3, N[Nat])) := refl
  def GTmW (n : Nat) : L(Nat) := match clone(n) { Z => C[Nat](clone(n), N[Nat]), S k => C[Nat](clone(n), N[Nat]) }
  def ITmW : Eq(L(Nat), GTmW(3), C[Nat](3, N[Nat])) := refl
  reject def GFbN (n : Nat) : W := MkW(N)
  reject def IFbN : Eq(W, GFbN(3), MkW(N[Nat])) := refl
  def GFbC (n : Nat) : W := MkW(C(clone(n), N))
  def IFbC : Eq(W, GFbC(3), MkW(C[Nat](3, N[Nat]))) := refl
  def GFbW (n : Nat) : W := MkW(C[Nat](clone(n), N[Nat]))
  def IFbW : Eq(W, GFbW(3), MkW(C[Nat](3, N[Nat]))) := refl
  reject def GFlN (n : Nat) : W := MkW((let y = Z; N))
  reject def IFlN : Eq(W, GFlN(3), MkW(N[Nat])) := refl
  def GFlC (n : Nat) : W := MkW((let y = Z; C(clone(n), N)))
  def IFlC : Eq(W, GFlC(3), MkW(C[Nat](3, N[Nat]))) := refl
  def GFlW (n : Nat) : W := MkW((let y = Z; C[Nat](clone(n), N[Nat])))
  def IFlW : Eq(W, GFlW(3), MkW(C[Nat](3, N[Nat]))) := refl
  reject def GFsN (n : Nat) : W := MkW((Z; N))
  reject def IFsN : Eq(W, GFsN(3), MkW(N[Nat])) := refl
  def GFsC (n : Nat) : W := MkW((Z; C(clone(n), N)))
  def IFsC : Eq(W, GFsC(3), MkW(C[Nat](3, N[Nat]))) := refl
  def GFsW (n : Nat) : W := MkW((Z; C[Nat](clone(n), N[Nat])))
  def IFsW : Eq(W, GFsW(3), MkW(C[Nat](3, N[Nat]))) := refl
  reject def GFmN (n : Nat) : W := MkW(match clone(n) { Z => N, S k => N })
  reject def IFmN : Eq(W, GFmN(3), MkW(N[Nat])) := refl
  def GFmC (n : Nat) : W := MkW(match clone(n) { Z => C(clone(n), N), S k => C(clone(n), N) })
  def IFmC : Eq(W, GFmC(3), MkW(C[Nat](3, N[Nat]))) := refl
  def GFmW (n : Nat) : W := MkW(match clone(n) { Z => C[Nat](clone(n), N[Nat]), S k => C[Nat](clone(n), N[Nat]) })
  def IFmW : Eq(W, GFmW(3), MkW(C[Nat](3, N[Nat]))) := refl
  def GGbN (n : Nat) : L(Nat) := C(0, N)
  def IGbN : Eq(L(Nat), GGbN(3), C[Nat](0, N[Nat])) := refl
  def GGbC (n : Nat) : L(Nat) := C(0, C(clone(n), N))
  def IGbC : Eq(L(Nat), GGbC(3), C[Nat](0, C[Nat](3, N[Nat]))) := refl
  def GGbW (n : Nat) : L(Nat) := C(0, C[Nat](clone(n), N[Nat]))
  def IGbW : Eq(L(Nat), GGbW(3), C[Nat](0, C[Nat](3, N[Nat]))) := refl
  reject def GGlN (n : Nat) : L(Nat) := C(0, (let y = Z; N))
  reject def IGlN : Eq(L(Nat), GGlN(3), C[Nat](0, N[Nat])) := refl
  def GGlC (n : Nat) : L(Nat) := C(0, (let y = Z; C(clone(n), N)))
  def IGlC : Eq(L(Nat), GGlC(3), C[Nat](0, C[Nat](3, N[Nat]))) := refl
  def GGlW (n : Nat) : L(Nat) := C(0, (let y = Z; C[Nat](clone(n), N[Nat])))
  def IGlW : Eq(L(Nat), GGlW(3), C[Nat](0, C[Nat](3, N[Nat]))) := refl
  reject def GGsN (n : Nat) : L(Nat) := C(0, (Z; N))
  reject def IGsN : Eq(L(Nat), GGsN(3), C[Nat](0, N[Nat])) := refl
  def GGsC (n : Nat) : L(Nat) := C(0, (Z; C(clone(n), N)))
  def IGsC : Eq(L(Nat), GGsC(3), C[Nat](0, C[Nat](3, N[Nat]))) := refl
  def GGsW (n : Nat) : L(Nat) := C(0, (Z; C[Nat](clone(n), N[Nat])))
  def IGsW : Eq(L(Nat), GGsW(3), C[Nat](0, C[Nat](3, N[Nat]))) := refl
  reject def GGmN (n : Nat) : L(Nat) := C(0, match clone(n) { Z => N, S k => N })
  reject def IGmN : Eq(L(Nat), GGmN(3), C[Nat](0, N[Nat])) := refl
  def GGmC (n : Nat) : L(Nat) := C(0, match clone(n) { Z => C(clone(n), N), S k => C(clone(n), N) })
  def IGmC : Eq(L(Nat), GGmC(3), C[Nat](0, C[Nat](3, N[Nat]))) := refl
  def GGmW (n : Nat) : L(Nat) := C(0, match clone(n) { Z => C[Nat](clone(n), N[Nat]), S k => C[Nat](clone(n), N[Nat]) })
  def IGmW : Eq(L(Nat), GGmW(3), C[Nat](0, C[Nat](3, N[Nat]))) := refl
  def GAbN (n : Nat) : L(Nat) := IdL(N)
  def IAbN : Eq(L(Nat), GAbN(3), N[Nat]) := refl
  def GAbC (n : Nat) : L(Nat) := IdL(C(clone(n), N))
  def IAbC : Eq(L(Nat), GAbC(3), C[Nat](3, N[Nat])) := refl
  def GAbW (n : Nat) : L(Nat) := IdL(C[Nat](clone(n), N[Nat]))
  def IAbW : Eq(L(Nat), GAbW(3), C[Nat](3, N[Nat])) := refl
  reject def GAlN (n : Nat) : L(Nat) := IdL((let y = Z; N))
  reject def IAlN : Eq(L(Nat), GAlN(3), N[Nat]) := refl
  def GAlC (n : Nat) : L(Nat) := IdL((let y = Z; C(clone(n), N)))
  def IAlC : Eq(L(Nat), GAlC(3), C[Nat](3, N[Nat])) := refl
  def GAlW (n : Nat) : L(Nat) := IdL((let y = Z; C[Nat](clone(n), N[Nat])))
  def IAlW : Eq(L(Nat), GAlW(3), C[Nat](3, N[Nat])) := refl
  reject def GAsN (n : Nat) : L(Nat) := IdL((Z; N))
  reject def IAsN : Eq(L(Nat), GAsN(3), N[Nat]) := refl
  def GAsC (n : Nat) : L(Nat) := IdL((Z; C(clone(n), N)))
  def IAsC : Eq(L(Nat), GAsC(3), C[Nat](3, N[Nat])) := refl
  def GAsW (n : Nat) : L(Nat) := IdL((Z; C[Nat](clone(n), N[Nat])))
  def IAsW : Eq(L(Nat), GAsW(3), C[Nat](3, N[Nat])) := refl
  reject def GAmN (n : Nat) : L(Nat) := IdL(match clone(n) { Z => N, S k => N })
  reject def IAmN : Eq(L(Nat), GAmN(3), N[Nat]) := refl
  def GAmC (n : Nat) : L(Nat) := IdL(match clone(n) { Z => C(clone(n), N), S k => C(clone(n), N) })
  def IAmC : Eq(L(Nat), GAmC(3), C[Nat](3, N[Nat])) := refl
  def GAmW (n : Nat) : L(Nat) := IdL(match clone(n) { Z => C[Nat](clone(n), N[Nat]), S k => C[Nat](clone(n), N[Nat]) })
  def IAmW : Eq(L(Nat), GAmW(3), C[Nat](3, N[Nat])) := refl
  def GDbN (n : Nat) : L(Nat) := (let v : L(Nat) = N; v)
  def IDbN : Eq(L(Nat), GDbN(3), N[Nat]) := refl
  def GDbC (n : Nat) : L(Nat) := (let v : L(Nat) = C(clone(n), N); v)
  def IDbC : Eq(L(Nat), GDbC(3), C[Nat](3, N[Nat])) := refl
  def GDbW (n : Nat) : L(Nat) := (let v : L(Nat) = C[Nat](clone(n), N[Nat]); v)
  def IDbW : Eq(L(Nat), GDbW(3), C[Nat](3, N[Nat])) := refl
  reject def GDlN (n : Nat) : L(Nat) := (let v : L(Nat) = (let y = Z; N); v)
  reject def IDlN : Eq(L(Nat), GDlN(3), N[Nat]) := refl
  def GDlC (n : Nat) : L(Nat) := (let v : L(Nat) = (let y = Z; C(clone(n), N)); v)
  def IDlC : Eq(L(Nat), GDlC(3), C[Nat](3, N[Nat])) := refl
  def GDlW (n : Nat) : L(Nat) := (let v : L(Nat) = (let y = Z; C[Nat](clone(n), N[Nat])); v)
  def IDlW : Eq(L(Nat), GDlW(3), C[Nat](3, N[Nat])) := refl
  reject def GDsN (n : Nat) : L(Nat) := (let v : L(Nat) = (Z; N); v)
  reject def IDsN : Eq(L(Nat), GDsN(3), N[Nat]) := refl
  def GDsC (n : Nat) : L(Nat) := (let v : L(Nat) = (Z; C(clone(n), N)); v)
  def IDsC : Eq(L(Nat), GDsC(3), C[Nat](3, N[Nat])) := refl
  def GDsW (n : Nat) : L(Nat) := (let v : L(Nat) = (Z; C[Nat](clone(n), N[Nat])); v)
  def IDsW : Eq(L(Nat), GDsW(3), C[Nat](3, N[Nat])) := refl
  reject def GDmN (n : Nat) : L(Nat) := (let v : L(Nat) = match clone(n) { Z => N, S k => N }; v)
  reject def IDmN : Eq(L(Nat), GDmN(3), N[Nat]) := refl
  def GDmC (n : Nat) : L(Nat) := (let v : L(Nat) = match clone(n) { Z => C(clone(n), N), S k => C(clone(n), N) }; v)
  def IDmC : Eq(L(Nat), GDmC(3), C[Nat](3, N[Nat])) := refl
  def GDmW (n : Nat) : L(Nat) := (let v : L(Nat) = match clone(n) { Z => C[Nat](clone(n), N[Nat]), S k => C[Nat](clone(n), N[Nat]) }; v)
  def IDmW : Eq(L(Nat), GDmW(3), C[Nat](3, N[Nat])) := refl
  def GSbN (n : Nat) : L(Nat) := (let v = C[Nat](5, N[Nat]); v := N; v)
  def ISbN : Eq(L(Nat), GSbN(3), N[Nat]) := refl
  def GSbC (n : Nat) : L(Nat) := (let v = C[Nat](5, N[Nat]); v := C(clone(n), N); v)
  def ISbC : Eq(L(Nat), GSbC(3), C[Nat](3, N[Nat])) := refl
  def GSbW (n : Nat) : L(Nat) := (let v = C[Nat](5, N[Nat]); v := C[Nat](clone(n), N[Nat]); v)
  def ISbW : Eq(L(Nat), GSbW(3), C[Nat](3, N[Nat])) := refl
  reject def GSlN (n : Nat) : L(Nat) := (let v = C[Nat](5, N[Nat]); v := (let y = Z; N); v)
  reject def ISlN : Eq(L(Nat), GSlN(3), N[Nat]) := refl
  def GSlC (n : Nat) : L(Nat) := (let v = C[Nat](5, N[Nat]); v := (let y = Z; C(clone(n), N)); v)
  def ISlC : Eq(L(Nat), GSlC(3), C[Nat](3, N[Nat])) := refl
  def GSlW (n : Nat) : L(Nat) := (let v = C[Nat](5, N[Nat]); v := (let y = Z; C[Nat](clone(n), N[Nat])); v)
  def ISlW : Eq(L(Nat), GSlW(3), C[Nat](3, N[Nat])) := refl
  reject def GSsN (n : Nat) : L(Nat) := (let v = C[Nat](5, N[Nat]); v := (Z; N); v)
  reject def ISsN : Eq(L(Nat), GSsN(3), N[Nat]) := refl
  def GSsC (n : Nat) : L(Nat) := (let v = C[Nat](5, N[Nat]); v := (Z; C(clone(n), N)); v)
  def ISsC : Eq(L(Nat), GSsC(3), C[Nat](3, N[Nat])) := refl
  def GSsW (n : Nat) : L(Nat) := (let v = C[Nat](5, N[Nat]); v := (Z; C[Nat](clone(n), N[Nat])); v)
  def ISsW : Eq(L(Nat), GSsW(3), C[Nat](3, N[Nat])) := refl
  reject def GSmN (n : Nat) : L(Nat) := (let v = C[Nat](5, N[Nat]); v := match clone(n) { Z => N, S k => N }; v)
  reject def ISmN : Eq(L(Nat), GSmN(3), N[Nat]) := refl
  def GSmC (n : Nat) : L(Nat) := (let v = C[Nat](5, N[Nat]); v := match clone(n) { Z => C(clone(n), N), S k => C(clone(n), N) }; v)
  def ISmC : Eq(L(Nat), GSmC(3), C[Nat](3, N[Nat])) := refl
  def GSmW (n : Nat) : L(Nat) := (let v = C[Nat](5, N[Nat]); v := match clone(n) { Z => C[Nat](clone(n), N[Nat]), S k => C[Nat](clone(n), N[Nat]) }; v)
  def ISmW : Eq(L(Nat), GSmW(3), C[Nat](3, N[Nat])) := refl
  def GKbN (n : Nat) : L(Nat) := IdL((N : L(Nat)))
  def IKbN : Eq(L(Nat), GKbN(3), N[Nat]) := refl
  def GKbC (n : Nat) : L(Nat) := IdL((C(clone(n), N) : L(Nat)))
  def IKbC : Eq(L(Nat), GKbC(3), C[Nat](3, N[Nat])) := refl
  def GKbW (n : Nat) : L(Nat) := IdL((C[Nat](clone(n), N[Nat]) : L(Nat)))
  def IKbW : Eq(L(Nat), GKbW(3), C[Nat](3, N[Nat])) := refl
  reject def GKlN (n : Nat) : L(Nat) := IdL(((let y = Z; N) : L(Nat)))
  reject def IKlN : Eq(L(Nat), GKlN(3), N[Nat]) := refl
  def GKlC (n : Nat) : L(Nat) := IdL(((let y = Z; C(clone(n), N)) : L(Nat)))
  def IKlC : Eq(L(Nat), GKlC(3), C[Nat](3, N[Nat])) := refl
  def GKlW (n : Nat) : L(Nat) := IdL(((let y = Z; C[Nat](clone(n), N[Nat])) : L(Nat)))
  def IKlW : Eq(L(Nat), GKlW(3), C[Nat](3, N[Nat])) := refl
  reject def GKsN (n : Nat) : L(Nat) := IdL(((Z; N) : L(Nat)))
  reject def IKsN : Eq(L(Nat), GKsN(3), N[Nat]) := refl
  def GKsC (n : Nat) : L(Nat) := IdL(((Z; C(clone(n), N)) : L(Nat)))
  def IKsC : Eq(L(Nat), GKsC(3), C[Nat](3, N[Nat])) := refl
  def GKsW (n : Nat) : L(Nat) := IdL(((Z; C[Nat](clone(n), N[Nat])) : L(Nat)))
  def IKsW : Eq(L(Nat), GKsW(3), C[Nat](3, N[Nat])) := refl
  reject def GKmN (n : Nat) : L(Nat) := IdL((match clone(n) { Z => N, S k => N } : L(Nat)))
  reject def IKmN : Eq(L(Nat), GKmN(3), N[Nat]) := refl
  def GKmC (n : Nat) : L(Nat) := IdL((match clone(n) { Z => C(clone(n), N), S k => C(clone(n), N) } : L(Nat)))
  def IKmC : Eq(L(Nat), GKmC(3), C[Nat](3, N[Nat])) := refl
  def GKmW (n : Nat) : L(Nat) := IdL((match clone(n) { Z => C[Nat](clone(n), N[Nat]), S k => C[Nat](clone(n), N[Nat]) } : L(Nat)))
  def IKmW : Eq(L(Nat), GKmW(3), C[Nat](3, N[Nat])) := refl
  def GUbN (n : Nat) : L(Nat) := (let u = Len(N); N[Nat])
  def IUbN : Eq(L(Nat), GUbN(3), N[Nat]) := refl
  def GUbC (n : Nat) : L(Nat) := (let u = Len(C(clone(n), N)); N[Nat])
  def IUbC : Eq(L(Nat), GUbC(3), N[Nat]) := refl
  def GUbW (n : Nat) : L(Nat) := (let u = Len(C[Nat](clone(n), N[Nat])); N[Nat])
  def IUbW : Eq(L(Nat), GUbW(3), N[Nat]) := refl
  reject def GUlN (n : Nat) : L(Nat) := (let u = Len((let y = Z; N)); N[Nat])
  reject def IUlN : Eq(L(Nat), GUlN(3), N[Nat]) := refl
  def GUlC (n : Nat) : L(Nat) := (let u = Len((let y = Z; C(clone(n), N))); N[Nat])
  def IUlC : Eq(L(Nat), GUlC(3), N[Nat]) := refl
  def GUlW (n : Nat) : L(Nat) := (let u = Len((let y = Z; C[Nat](clone(n), N[Nat]))); N[Nat])
  def IUlW : Eq(L(Nat), GUlW(3), N[Nat]) := refl
  reject def GUsN (n : Nat) : L(Nat) := (let u = Len((Z; N)); N[Nat])
  reject def IUsN : Eq(L(Nat), GUsN(3), N[Nat]) := refl
  def GUsC (n : Nat) : L(Nat) := (let u = Len((Z; C(clone(n), N))); N[Nat])
  def IUsC : Eq(L(Nat), GUsC(3), N[Nat]) := refl
  def GUsW (n : Nat) : L(Nat) := (let u = Len((Z; C[Nat](clone(n), N[Nat]))); N[Nat])
  def IUsW : Eq(L(Nat), GUsW(3), N[Nat]) := refl
  reject def GUmN (n : Nat) : L(Nat) := (let u = Len(match clone(n) { Z => N, S k => N }); N[Nat])
  reject def IUmN : Eq(L(Nat), GUmN(3), N[Nat]) := refl
  def GUmC (n : Nat) : L(Nat) := (let u = Len(match clone(n) { Z => C(clone(n), N), S k => C(clone(n), N) }); N[Nat])
  def IUmC : Eq(L(Nat), GUmC(3), N[Nat]) := refl
  def GUmW (n : Nat) : L(Nat) := (let u = Len(match clone(n) { Z => C[Nat](clone(n), N[Nat]), S k => C[Nat](clone(n), N[Nat]) }); N[Nat])
  def IUmW : Eq(L(Nat), GUmW(3), N[Nat]) := refl
  -- a match on a proof (by type) in tail position, its arm a bare constructor
  def GPb (h : ⊤ ∧ ⊤) : L(Nat) := match h { Intro(a, b) => N }
  def IPb : Eq(L(Nat), GPb(⟨refl, refl⟩), N[Nat]) := refl
  def GPc (n : Nat) (h : ⊤ ∧ ⊤) : L(Nat) := match h { Intro(a, b) => C(clone(n), N) }
  def IPc : Eq(L(Nat), GPc(3, ⟨refl, refl⟩), C[Nat](3, N[Nat])) := refl
  -- a body that needs no context (runBody hands no hint), its tail a constructor its fields determine
  def GBc (n : Nat) : L(Nat) := C(clone(n), N[Nat])
  def IBc : Eq(L(Nat), GBc(3), C[Nat](3, N[Nat])) := refl
  -- J's transported term (D124): the typed check hands it `P(a)` whether `J` is stuck (`GJs…`: `h`
  -- unknown, closed off) or computes (`GJr…`: `refl`), and the untyped run, the instance, where it
  -- reads it; a bare constructor, one its fields determine, one with its parameter written, and
  -- terms that are not constructors (a call, and a `let` whose tail is a bare constructor: no hint
  -- reaches a `let`'s tail out of tail position, so both paths reject it)
  def GJs (n : Nat) (h : Eq(Nat, n, 0)) : L(Nat) := J(Nat, n, 0, λ(z : Nat) : Type => L(Nat), h, N)
  def IJs : Eq(L(Nat), GJs(0, refl), N[Nat]) := refl
  def GJr (n : Nat) : L(Nat) := J(Nat, n, n, λ(z : Nat) : Type => L(Nat), refl, N)
  def IJr : Eq(L(Nat), GJr(3), N[Nat]) := refl
  def GJc (n : Nat) (h : Eq(Nat, n, 0)) : L(Nat) := J(Nat, n, 0, λ(z : Nat) : Type => L(Nat), h, C(clone(n), N))
  def IJc : Eq(L(Nat), GJc(0, refl), C[Nat](0, N[Nat])) := refl
  def GJrc (n : Nat) : L(Nat) := J(Nat, n, n, λ(z : Nat) : Type => L(Nat), refl, C(clone(n), N))
  def IJrc : Eq(L(Nat), GJrc(3), C[Nat](3, N[Nat])) := refl
  def GJw (n : Nat) (h : Eq(Nat, n, 0)) : L(Nat) := J(Nat, n, 0, λ(z : Nat) : Type => L(Nat), h, N[Nat])
  def IJw : Eq(L(Nat), GJw(0, refl), N[Nat]) := refl
  def GJrw (n : Nat) : L(Nat) := J(Nat, n, n, λ(z : Nat) : Type => L(Nat), refl, N[Nat])
  def IJrw : Eq(L(Nat), GJrw(3), N[Nat]) := refl
  def GJf (n : Nat) (h : Eq(Nat, n, 0)) : L(Nat) := J(Nat, n, 0, λ(z : Nat) : Type => L(Nat), h, IdL(C[Nat](clone(n), N[Nat])))
  def IJf : Eq(L(Nat), GJf(0, refl), C[Nat](0, N[Nat])) := refl
  def GJrf (n : Nat) : L(Nat) := J(Nat, n, n, λ(z : Nat) : Type => L(Nat), refl, IdL(C[Nat](clone(n), N[Nat])))
  def IJrf : Eq(L(Nat), GJrf(3), C[Nat](3, N[Nat])) := refl
  reject def GJl (n : Nat) (h : Eq(Nat, n, 0)) : L(Nat) := J(Nat, n, 0, λ(z : Nat) : Type => L(Nat), h, (let y = Z; N))
  reject def IJl : Eq(L(Nat), GJl(0, refl), N[Nat]) := refl
  reject def GJrl (n : Nat) : L(Nat) := J(Nat, n, n, λ(z : Nat) : Type => L(Nat), refl, (let y = Z; N))
  reject def IJrl : Eq(L(Nat), GJrl(3), N[Nat]) := refl
  -- `J` away from the end of a body: a `let`'s right-hand side and a call's argument
  def GJsLet (n : Nat) (h : Eq(Nat, n, 0)) : L(Nat) := (let r = J(Nat, n, 0, λ(z : Nat) : Type => L(Nat), h, N); r)
  def IJsLet : Eq(L(Nat), GJsLet(0, refl), N[Nat]) := refl
  def GJrLet (n : Nat) : L(Nat) := (let r = J(Nat, n, n, λ(z : Nat) : Type => L(Nat), refl, N); r)
  def IJrLet : Eq(L(Nat), GJrLet(3), N[Nat]) := refl
  def GJsA (n : Nat) (h : Eq(Nat, n, 0)) : Nat := Len(J(Nat, n, 0, λ(z : Nat) : Type => L(Nat), h, N))
  def IJsA : Eq(Nat, GJsA(0, refl), 0) := refl
  def GJrA (n : Nat) : Nat := Len(J(Nat, n, n, λ(z : Nat) : Type => L(Nat), refl, N))
  def IJrA : Eq(Nat, GJrA(3), 0) := refl
  -- a motive that depends on the endpoint: `P(a)` mentions `n`, stuck at the generic call
  def TN (z : Nat) : Type := match z { Z => Nat, S k => Unit }
  def GJds (n : Nat) (h : Eq(Nat, n, 0)) : L(Nat) := J(Nat, n, 0, λ(z : Nat) : Type => L(TN(z)), h, N)
  def IJds : Eq(L(Nat), GJds(0, refl), N[Nat]) := refl
  def GJdr (n : Nat) : L(TN(n)) := J(Nat, n, n, λ(z : Nat) : Type => L(TN(z)), refl, N)
  def IJdr : Eq(L(Unit), GJdr(3), N[Unit]) := refl
  def GJdw (n : Nat) (h : Eq(Nat, n, 0)) : L(Nat) := J(Nat, n, 0, λ(z : Nat) : Type => L(TN(z)), h, N[TN(n)])
  def IJdw : Eq(L(Nat), GJdw(0, refl), N[Nat]) := refl
  def GJdrw (n : Nat) : L(TN(n)) := J(Nat, n, n, λ(z : Nat) : Type => L(TN(z)), refl, N[TN(n)])
  def IJdrw : Eq(L(Unit), GJdrw(3), N[Unit]) := refl
  -- an erased `J` (its motive into `Prop`), a proof: it always computes; in a data function's body
  -- its untyped run is a statement
  inductive PN (A : Type) : Prop := PNil
  def GJe (n : Nat) : PN(Nat) := J(Nat, n, n, λ(z : Nat) : Prop => PN(Nat), refl, PNil)
  def GJeD (n : Nat) : Nat := (let p = J(Nat, n, n, λ(z : Nat) : Prop => PN(Nat), refl, PNil); 0)
  def IJeD : Eq(Nat, GJeD(3), 0) := refl
}

#guard (run "UntypedHints" UntypedHints).rejectedWith [
  ("Ctl", "the body of Ctl has type Unit"),
  ("GFbN", "cannot infer the parameter A of N"),
  ("GFlN", "cannot infer the parameter A of N"),
  ("GFsN", "cannot infer the parameter A of N"),
  ("GFmN", "cannot infer the parameter A of N"),
  ("GGlN", "cannot infer the parameter A of N"),
  ("GGsN", "cannot infer the parameter A of N"),
  ("GGmN", "cannot infer the parameter A of N"),
  ("GAlN", "cannot infer the parameter A of N"),
  ("GAsN", "cannot infer the parameter A of N"),
  ("GAmN", "cannot infer the parameter A of N"),
  ("GDlN", "cannot infer the parameter A of N"),
  ("GDsN", "cannot infer the parameter A of N"),
  ("GDmN", "cannot infer the parameter A of N"),
  ("GSlN", "cannot infer the parameter A of N"),
  ("GSsN", "cannot infer the parameter A of N"),
  ("GSmN", "cannot infer the parameter A of N"),
  ("GKlN", "cannot infer the parameter A of N"),
  ("GKsN", "cannot infer the parameter A of N"),
  ("GKmN", "cannot infer the parameter A of N"),
  ("GUlN", "cannot infer the parameter A of N"),
  ("GUsN", "cannot infer the parameter A of N"),
  ("GUmN", "cannot infer the parameter A of N"),
  ("GJl", "cannot infer the parameter A of N"),
  ("GJrl", "cannot infer the parameter A of N"),
  ("IJl", "unknown constant GJl"),
  ("IJrl", "unknown constant GJrl")]

namespace Ochr.Examples.UntypedHints
open Ochr

/-- `inductive L (A : Type) := N`. -/
def declL : IndDecl := { name := "L", params := [(⟨"A"⟩, .sort 1)], ctors := [("N", [])] }

/-- The parameters a constructor value records (`==` does not compare them). -/
def recorded : Except String (Value × Option Value) → Option (List Value)
  | .ok (.ind _ _ _ ps _, _) => some ps
  | _ => none

/-- An untyped run of `t` at the hint `L(Nat)`, from a frame binding `x ↦ 0 : Nat` and `l ↦ N[Nat] : L(Nat)`,
in tail position or not. -/
def runAt (t : Term) (tail : Bool) : Except String (Value × Option Value) :=
  let fr : Frame := { binds := #[
    { hint := ⟨"x"⟩, ty := some .tNat, val := .zero, decl := .other },
    { hint := ⟨"l"⟩, ty := some (.tInd "L" [.tNat]), val := .ind "L" 0 ⟨"N"⟩ [.tNat] [], decl := .other }] }
  runM (Ochr.eval 100 false t (some (.tInd "L" [.tNat]))) { env := #[fr], inds := [declL], tailNext := tail }

/-- `N`, bare. -/
def tN : Term := .ctor "L" 0 ⟨"N"⟩ [] []

-- a `let`'s tail, a `;`'s tail and a match's arms: out of tail position the bare `N` records no
-- parameter (before D124 it took `Nat` from the hint); in tail position it records `Nat`
#guard recorded (runAt (.letIn ⟨"y"⟩ .zero tN) false) == some []
#guard recorded (runAt (.letIn ⟨"y"⟩ .zero tN) true) == some [.tNat]
#guard recorded (runAt (.seq .zero tN) false) == some []
#guard recorded (runAt (.seq .zero tN) true) == some [.tNat]
#guard recorded (runAt (.matchNat (.var 1) tN tN) false) == some []
#guard recorded (runAt (.matchNat (.var 1) tN tN) true) == some [.tNat]
-- an assigned constructor takes the place's type, as in the typed check (before D124: none), and the
-- value assigned records it
#guard match runM (do discard (Ochr.eval 100 false (.assign (.var 0) tN) none); content? (.var 0))
    { env := #[{ binds := #[{ hint := ⟨"l"⟩, ty := some (.tInd "L" [.tNat]), val := .ind "L" 0 ⟨"N"⟩ [.tNat] [], decl := .other }] }],
      inds := [declL] } with
  | .ok (some (.ind _ _ _ ps _)) => ps.length == 1
  | _ => false

/-- `J(Nat, 0, 0, λ(z : Nat) : Type => L(Nat), (), t)`: `J` computes (its proof is never run). -/
def jR (t : Term) : Term :=
  .prim "J" [.nat, .zero, .zero, .fix ⟨"_"⟩ [⟨"z"⟩] [.nat] (.sort 1) none (.tind "L" [.nat]), .tt, t]

-- J's transported term where `J` computes: a bare `N` takes `Nat` from `P(a)`, as the typed check
-- hands it (before D124's site for `J`, the untyped run handed it nothing and it recorded none), in
-- tail position or not
#guard recorded (runAt (jR tN) false) == some [.tNat]
#guard recorded (runAt (jR tN) true) == some [.tNat]

/-- An untyped run of `t` at the hint `h`, in a context that reads its type (`want`, as a `let`'s
right-hand side and a borrow argument are). -/
def runWant (t : Term) (h : Option Value) : Option (Option Value) :=
  match runM (Ochr.eval 100 false t h) { env := #[{}], inds := [declL], wantTy := true } with
  | .ok (_, T) => some T
  | .error _ => none

-- an embedded value's type, where its context reads it: by its kind, as the typed check types it
-- (before D124's site for it, the untyped run took the hint, so `0` embedded at `L(Nat)` was typed
-- `L(Nat)`); a proof's is the hint, as in the typed check
#guard runWant (.val .zero) (some (.tInd "L" [.tNat])) == some (some .tNat)
#guard runWant (.val (.ind "L" 0 ⟨"N"⟩ [.tNat] [])) (some (.tInd "L" [.tUnit])) == some (some (.tInd "L" [.tNat]))
#guard runWant (.val .proof) (some (.tInd "True" [])) == some (some (.tInd "True" []))

end Ochr.Examples.UntypedHints


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
was accepted as positive (`T1`, given an earlier field of `T1` itself); Lean's kernel rejects it
("nested inductive datatypes parameters cannot contain local variables"), the data model cannot
build it (its value argument carries the model's record of `T1`), and D120 rejects it. With a value
argument of an unrelated type the nesting stays accepted (`T2`). -/

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
  reject inductive T1 := Leaf1 | Node1(t : T1, g : G1(T1, t))
  inductive G2 (A : Type) (n : Nat) := MkG2(x : A)
  inductive T2 := Leaf2 | Node2(n : Nat, g : G2(T2, n))
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
  ("Bad11", "field h of MkBad11 : H2("),
  ("T1", "field g of Node1 : G1(T1, t): the argument at the value parameter a of G1 reads t, whose declared type T1 mentions T1")]

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
  -- twins: what reads no constructor of the type being declared passes D107 (`EOk`); reading an
  -- earlier field of the type at all, as `EOnce` and `EClone` do, is rejected by D120
  inductive EOk (h : False) := LeafOk | NodeOk(b : EOk(h), w : W(let k : False = match h {}; k))
  reject inductive EOnce := LeafO | NodeO(b : EOnce, t : Tag(let x = b; 0))
  reject inductive EClone := LeafCl | NodeCl(b : EClone, t : Tag(let x = clone(b); 0))
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
  ("ED", "[Read] b was moved out or its borrow ended"),
  ("EOnce", "field t of NodeO : Tag(let x = b; 0): the argument at the value parameter n of Tag reads b, whose declared type EOnce mentions EOnce"),
  ("EClone", "field t of NodeCl : Tag(let x = clone(b); 0): the argument at the value parameter n of Tag reads b, whose declared type EClone mentions EClone")]

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
  -- accepted since D149 (before, "κ is not a type": `U` was bound with no reading, so `F`'s type,
  -- which captures it, read as no sort), as Lean accepts it; usable
  inductive LB (U : Type₁) (F : Π(x : U). Type) (a : U) := MkLB(y : AppU(U, F, a))
  def lb : LB(Type, λ(X : Type) : Type => X, Word) := MkLB[Type, λ(X : Type) : Type => X, Word](Zero)
  reject def lbBad : LB(Type, λ(X : Type) : Type => X, Word) := MkLB[Type, λ(X : Type) : Type => X, Word](())
  def lbY (l : LB(Type, λ(X : Type) : Type => X, Word)) : Word := match l { MkLB(y) => y, }
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
  ("lbBad", "field y of MkLB has type Unit, expected Word"),
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

/-! ## Lean's rules for nested declarations (D120, D121)

Three kinds of declaration were accepted that Lean's kernel rejects, and at each the data model's
construction fails (docs/34 §18.6): a nested occurrence whose value argument is an earlier field of
the type itself (`R1`, Lean: "nested inductive datatypes parameters cannot contain local
variables"); an equation, or any argument off the field type's spine, reading an earlier field
whose type mentions the type, directly or through a parameter the type is nested at later (`R4`,
`W1`/`U1`); and a type of data nested through a proposition at a `Prop` parameter (`D1`, Lean:
"mutually inductive types must live in the same universe"), and, further in, a type nested through
a declaration of the other sort at a parameter (`DE`, `QE`). None was a hole: a field type in these
shapes sees only a container's shape, or carries the type's values as positive data. They are
rejected by two of Lean's rules. D120: a variable mentions what its declared type mentions, so an
equation, a type function's argument or a value argument may not read a variable whose type
mentions the type being declared, and a parameter read so is not nestable. D121: a nested
occurrence passes only through declarations of its own sort (a type of data through types of data,
a proposition through propositions), and a parameter passed to a declaration of the other sort is
not nestable. Each rejected shape is beside its smallest neighbour that stays accepted. Lean rejects
every row rejected here. Two accepted rows differ from Lean, which rejects them: `K1` (a nested
occurrence's value argument reads a field of an unrelated type: Lean allows no local variable
there) and `K8` (a type nested at its own parameter, D107). `DF` passes a closed value at a
parameter whose declared type mentions the parameter the type is nested at; Lean accepts it, and so
does the checker. -/

ochr NestReads uses Logic, Nats, Lists {
  inductive Tag (n : Nat) := MkTag
  inductive Fin1 (n : Nat) := MkFin1
  inductive Pt (A : Type) (a : A) := MkPt
  inductive Pn (A : Type) (n : Nat) := MkPn(x : A)
  def TF (n : Nat) : Type := (match n { Z => Nat, S(k) => Unit })
  -- a value argument of a nested occurrence, reading the type directly (kind 1)
  reject inductive R1 := L1 | N1(x : R1, p : Pt(R1, x))
  -- twins: the nested occurrence's value argument reads a field of an unrelated type, or is closed
  inductive K1 := KL1 | KN1(n : Nat, p : Pn(K1, n))
  inductive K1c := KL1c | KN1c(p : Pn(K1c, 3))
  def k1 : K1 := KN1(2, MkPn[K1, 2](KN1(0, MkPn[K1, 0](KL1))))
  -- a value argument of a declaration the type is not nested in, reading the type directly
  reject inductive R2 := L2 | N2(x : R2, t : Tag(let y = x; 0))
  -- the same through a container, by a match in the argument
  reject inductive R3 := L3 | N3(xs : List(R3), t : Tag(match xs { Nil => 0, Cons(h, r) => 1 }))
  -- twins: a dependent field indexed by an earlier field of an unrelated type; a container of
  -- the type that nothing off the spine reads
  inductive K3 := MkK3(n : Nat, x : Fin1(n))
  inductive K3b := L3b | N3b(xs : List(K3b))
  -- an equation side reading a container of the type (kind 2), and the type directly
  reject inductive R4 := L4 | N4(xs : List(R4), e : Eq(Nat, match xs { Nil => 0, Cons(h, r) => 1 }, 1))
  reject inductive R4b := L4b | N4b(x : R4b, e : Eq(Nat, (let y = x; 0), 0))
  -- twin: an invariant on a field of an unrelated type, beside a container of the type
  inductive K4 := L4k | N4k(n : Nat, e : Eq(Nat, n, n), xs : List(K4))
  -- a type function's argument: closed already, as an argument is a variable, a numeral or a
  -- first-order type (D36), and no type function declared earlier takes the type's values
  reject inductive R5 := L5 | N5(xs : List(R5), y : TF(match xs { Nil => 0, Cons(h, r) => 1 }))
  -- twin: a type function's argument reading a field of an unrelated type
  inductive K5 := L5k | N5k(n : Nat, y : TF(n), xs : List(K5))
  -- the type's own value parameter, at its recursive occurrence, reading a container of the type
  reject inductive R6 (k : Nat) := L6 | N6(xs : List(R6(0)), r : R6(match xs { Nil => 0, Cons(h, t) => 1 }))
  -- twin: reading a field of an unrelated type there
  inductive K6 (k : Nat) := L6k | N6k(m : Nat, r : K6(m))
  -- a field of an unrelated type beside the read of a container of the type
  reject inductive R7 := L7 | N7(xs : List(R7), n : Nat, e : Eq(Nat, Add(n, match xs { Nil => 0, Cons(h, r) => 1 }), 1))
  -- the type nested at its own parameter, which a field reads through a variable of that type
  reject inductive R8 (A : Type) := L8 | N8(x : A, t : Tag(let y = x; 0), r : R8(R8(A)))
  -- twin: the parameter not read
  inductive K8 (A : Type) := L8k | N8k(x : A, r : K8(K8(A)))
  -- through a parameter nested later: an equation reading a container of the parameter (kind 2)
  inductive W1 (A : Type) := WL1 | WN1(ws : List(A), e : Eq(Nat, match ws { Nil => 0, Cons(h, t) => 1 }, 1))
  reject inductive U1 := MkU1(w : W1(U1))
  def w1 : W1(Nat) := WN1[Nat](Cons(0, Nil), refl)
  -- ... a value argument reading a field of the parameter's type
  inductive W2 (A : Type) := WN2(y : A, t : Tag(let z = y; 0))
  reject inductive U2 := UL2 | MkU2(w : W2(U2))
  -- ... a value parameter typed by the parameter, read
  inductive W3 (A : Type) (a : A) := WN3(t : Tag(let z = a; 0))
  reject inductive U3 := UL3 | MkU3(x : U3, w : W3(U3, x))
  -- ... a value parameter typed by a container of the parameter, read by an equation
  inductive W4 (A : Type) (l : List(A)) := WN4(e : Eq(Nat, match l { Nil => 0, Cons(h, t) => 1 }, 1))
  reject inductive U4 := UL4 | MkU4(x : U4, w : W4(U4, Cons(x, Nil)))
  -- ... through two declarations: the parameter passed on to one that reads it
  inductive W5 (A : Type) := WN5(w : W1(A))
  reject inductive U5 := MkU5(w : W5(U5))
  -- twin: a container of the parameter that nothing off the spine reads, and an equation on a
  -- field of an unrelated type
  inductive WK (A : Type) := WNK(ws : List(A), n : Nat, e : Eq(Nat, n, 1))
  inductive UK := MkUK(w : WK(UK))
  -- a closed value at a parameter whose declared type mentions the nested parameter (Lean accepts)
  inductive Void0 : Type
  def NegF (X : Type) (b : Nat) : Type := (match b { Z => Unit, S(k) => Π(x : X). Void0 })
  inductive NF (A : Type) (n : Nat) (f : NegF(A, n)) := MkNF(y : A)
  inductive DF := LeafF | NodeF(p : NF(DF, 0, ()))
}

#guard (run "NestReads" NestReads).rejectedWith [
  ("R1", "field p of N1 : Pt(R1, x): the argument at the value parameter a of Pt reads x, whose declared type R1 mentions R1, and a variable mentions what its declared type mentions"),
  ("R2", "field t of N2 : Tag(let y = x; 0): the argument at the value parameter n of Tag reads x, whose declared type R2 mentions R2"),
  ("R3", "field t of N3 : Tag(match xs { Nil => 0, Cons => 1 }): the argument at the value parameter n of Tag reads xs, whose declared type List(R3) mentions R3"),
  ("R4", "field e of N4 : Eq(Nat, match xs { Nil => 0, Cons => 1 }, 1): the equation reads xs, whose declared type List(R4) mentions R4"),
  ("R4b", "field e of N4b : Eq(Nat, let y = x; 0, 0): the equation reads x, whose declared type R4b mentions R4b"),
  ("R5", "field y of N5 : TF(match xs { Nil => 0, Cons => 1 }): fields are first-order data"),
  ("R6", "field r of N6 : R6(match xs { Nil => 0, Cons => 1 }): the argument at the value parameter k of R6 reads xs, whose declared type List(R6(0)) mentions R6"),
  ("R7", "field e of N7 : Eq(Nat, Add(n, match xs { Nil => 0, Cons => 1 }), 1): the equation reads xs, whose declared type List(R7) mentions R7"),
  ("R8", "field r of N8 : R8(R8(A)): R8 occurs at the parameter A of R8, which is not nestable in R8: a field of R8 reads, in an equation, a call or a value argument, a variable whose declared type mentions it"),
  ("U1", "field w of MkU1 : W1(U1): U1 occurs at the parameter A of W1, which is not nestable in W1: a field of W1 reads, in an equation, a call or a value argument, a variable whose declared type mentions it"),
  ("U2", "field w of MkU2 : W2(U2): U2 occurs at the parameter A of W2, which is not nestable in W2: a field of W2 reads"),
  ("U3", "field w of MkU3 : W3(U3, x): U3 occurs at the parameter A of W3, which is not nestable in W3: a field of W3 reads"),
  ("U4", "field w of MkU4 : W4(U4, Cons(x, Nil)): U4 occurs at the parameter A of W4, which is not nestable in W4: a field of W4 reads"),
  ("U5", "field w of MkU5 : W5(U5): U5 occurs at the parameter A of W5, which is not nestable in W5: W5 passes it to a type function, an equation, a value or a parameter that is not nestable")]

ochr NestProps uses Logic, Lists {
  inductive PP (A : Type) : Prop := MkPP(x : A)
  inductive Q (P : Prop) := MkQ(h : P)
  inductive QQ (P : Prop) : Prop := MkQQ(h : P)
  inductive Wrap (P : Prop) := MkWrap(h : P)
  inductive Box (A : Type) := MkBox(x : A)
  -- a type of data through a proposition (kind 3), deeper, through propositions only, at the type's
  -- own `Prop` parameter, and directly in a proposition at its `Type` parameter
  reject inductive D1 := MkD1(q : Q(PP(D1)))
  reject inductive D2 := MkD2(q : Q(And(PP(D2), True)))
  reject inductive D3 := MkD3(q : QQ(PP(D3)))
  reject inductive D4 (P : Prop) := L4 | N4(h : P, r : D4(PP(D4(P))))
  reject inductive D5 := MkD5(h : PP(D5))
  -- through a parameter nested later: `E` and `F` are accepted, their `A` is not nestable
  inductive E (A : Type) := MkE(p : PP(A))
  reject inductive DE := MkDE(e : E(DE))
  inductive F (A : Type) := MkF(q : Q(PP(A)))
  reject inductive G := MkG(f : F(G))
  def eNat : E(Nat) := MkE[Nat](MkPP[Nat](0))
  def fNat : F(Nat) := MkF[Nat](MkQ[PP(Nat)](MkPP[Nat](0)))
  -- a proposition through a type of data: directly, through a parameter nested later
  reject inductive QW : Prop := MkQW(w : Wrap(QW))
  reject inductive E3 : Prop := MkE3(q : Q(E3))
  inductive E2 (P : Prop) : Prop := MkE2(w : Wrap(P))
  reject inductive QE : Prop := MkQE(e : E2(QE))
  inductive FP (P : Prop) := MkFP(q : Q(And(P, True)))
  reject inductive EP : Prop := MkEP(f : FP(EP))
  -- twins: a proposition nested through propositions, a type of data through types of data
  inductive P1 : Prop := MkP1(h : And(P1, True))
  inductive P2 : Prop := MkP2(q : QQ(P2))
  inductive B1 := L1 | N1(b : Box(B1), l : List(Box(B1)))
  -- twins: a proposition in data and data in a proposition at no occurrence of the type
  inductive WithPP := MkWithPP(n : Nat, p : PP(Nat))
  inductive PWith (A : Type) : Prop := MkPWith(l : List(A))
  inductive UsePW : Prop := MkUsePW(p : PWith(Nat))
}

#guard (run "NestProps" NestProps).rejectedWith [
  ("D1", "field q of MkD1 : Q(PP(D1)): D1, a type of data, occurs inside an argument of PP, a proposition, and a nested occurrence passes only through declarations of its own sort (D121"),
  ("D2", "field q of MkD2 : Q(PP(D2) ∧ ⊤): D2, a type of data, occurs inside an argument of And, a proposition"),
  ("D3", "field q of MkD3 : QQ(PP(D3)): D3, a type of data, occurs inside an argument of QQ, a proposition"),
  ("D4", "field r of N4 : D4(PP(D4(P))): D4 occurs at the parameter P of D4, which is not nestable in D4: D4 passes it to a declaration of the other sort"),
  ("D5", "field h of MkD5 : PP(D5): D5, a type of data, occurs inside an argument of PP, a proposition"),
  ("DE", "field e of MkDE : E(DE): DE occurs at the parameter A of E, which is not nestable in E: E passes it to a declaration of the other sort, and a nested occurrence passes only through declarations of its own sort (D121"),
  ("G", "field f of MkG : F(G): G occurs at the parameter A of F, which is not nestable in F: F passes it to a declaration of the other sort"),
  ("QW", "field w of MkQW : Wrap(QW): QW, a proposition, occurs inside an argument of Wrap, a type of data"),
  ("E3", "field q of MkE3 : Q(E3): E3, a proposition, occurs inside an argument of Q, a type of data"),
  ("QE", "field e of MkQE : E2(QE): QE occurs at the parameter P of E2, which is not nestable in E2: E2 passes it to a declaration of the other sort"),
  ("EP", "field f of MkEP : FP(EP): EP occurs at the parameter P of FP, which is not nestable in FP: FP passes it to a declaration of the other sort")]

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
  -- `KeepTFSplit` names `KeepTF`, which is rejected, so not declared: D118 rejects it before it runs
  -- (before D118, its run reached [D77] first)
  ("KeepTF", "[D63]"), ("KeepTFSplit", "unknown constant KeepTF"), ("KeepTFSplitRun", "unknown constant KeepTFSplit"),
  ("CallTF2", "argument 2 (f) has type ⌈TF2(σ0)⌉, expected Π(m : Nat). Nat"), ("CallTF2Run", "unknown constant CallTF2"),
  ("CallTQ", "not a function type"), ("CallTQRun", "unknown constant CallTQ")]
