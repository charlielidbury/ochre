import Ochr.Examples.«16Arrays»

/-! # 18. Dependent fields

A field's type may mention the fields before it (docs/06, D64): `MkVec(n : Word, items :
Array(E, n))` stores a length next to an array of that length. The field types are a
telescope ([Ind]), and a field's type is computed from the earlier fields' current contents
(`type(p.items) = Array(E, content(p.n))`).

Fields can be written in place, so a write can break the dependency for a while: after
`n := Succ(n)`, `items` is still an array of the old length. The value is then *open*: each
dependent field is typed by what it holds. It must be *repacked*, of its telescope again, at
every point where it is used whole ([Repack]): read or moved whole, borrowed whole, passed, a
borrow of it ending (a borrow parameter's, when the function returns), returned, observed by
`Id`, or captured by a stuck block or a closure. A proof field cannot be repacked by what it
holds (a proof is `⋆`), so a write through a field its type mentions invalidates it until a new
proof is assigned ([Open]).

`Eq` takes a dependent constructor apart only while its index fields are convertible on both
sides (D52, restricted): otherwise the equation would be between values of different types.

A field type may call an earlier type function (`Array(E, n)`, K4), provided the type being
declared does not occur in its arguments, and is not nested at a parameter that an inductive
passes to a type function (a type function may use its argument negatively).

The first block is self-contained and is in the counterfactual ledger; `DepVec`, over the
arrays library, is a case study. -/

open Ochr.Test

ochr DepFields uses Std {
  inductive Empty0 : Type
  inductive One := O
  -- `Fin1(0)` has no values, `Fin1(n + 1)` has one
  def Fin1 (n : Word) : Type := (
    match n {
      Zero => Empty0,
      Succ(m) => One,
    }
  )
  inductive V := MkV(n : Word, x : Fin1(n))
  def VN (v : V) : Word := (
    match v {
      MkV(n, x) => n,
    }
  )
  def One1 : V := MkV(Succ(Zero), O)
  reject def NoneAt0 : V := MkV(Zero, O)

  -- a later field's type may mention only earlier fields
  reject inductive BadTele := MkBT(x : Fin1(n), n : Word)

  -- written in place in either order: open in between, repacked by the end
  def Refill (v : &V) : Unit := (
    match *v {
      MkV(n, x) => (
        n := Succ(Zero);
        x := O
      ),
    }
  )
  def RefillRev (v : &V) : Unit := (
    match *v {
      MkV(n, x) => (
        x := O;
        n := Succ(Zero)
      ),
    }
  )
  def Nop (v : &V) : Unit := ()

  -- the length lie: returns with `v` broken
  reject def LieV (v : &V) : Unit := (
    match *v {
      MkV(n, x) => n := Zero,
    }
  )
  -- used whole while broken
  reject def ReadBroken (v : &V) : Word := (
    match *v {
      MkV(n, x) => (
        let m = n;
        n := Zero;
        let k = VN(clone(*v));
        n := m;
        k
      ),
    }
  )
  reject def PassBroken (v : &V) : Unit := (
    match *v {
      MkV(n, x) => (
        let m = n;
        n := Zero;
        Nop(&*v);
        n := m
      ),
    }
  )
  reject def PassBrokenVar (v : &V) : Unit := (
    match *v {
      MkV(n, x) => (
        n := Zero;
        Nop(v)
      ),
    }
  )
  reject def IdBroken (v : &V) : Unit := (
    match *v {
      MkV(n, x) => (
        let m = n;
        n := Zero;
        let h : Id(Word, VN(clone(*v)), Zero) = refl;
        n := m
      ),
    }
  )
  reject def IdMakesBroken (v : &V) : Unit := (
    match *v {
      MkV(n, x) => (
        let h : Id(Unit, n := Zero, n := Zero) = refl;
        ()
      ),
    }
  )

  -- without [Repack] the lie is a closed proof of False: `Absurd` is true of every packed `V`
  def Absurd (v : V) (h : Eq(Word, VN(v), Zero)) : False := (
    match v {
      MkV(n, x) => match n {
        Zero => match x {},
        Succ(m) => match h {},
      },
    }
  )
  reject def Broken : V := (
    let v = MkV(Succ(Zero), O);
    LieV(&v);
    v
  )
  reject def Boom : False := Absurd(Broken, refl)
  -- fuzz-port's --dep family: the dependent field assigned a value of another type (`O : One`,
  -- not a `Fin1(0)`), with the index written first or last, set to a parameter (a stuck
  -- `⌈Fin1(σ)⌉`), or written through a borrow of the index field
  reject def LieZ (v : &V) : Unit := (
    match *v {
      MkV(n, x) => (
        n := Zero;
        x := O
      ),
    }
  )
  reject def LieZRev (v : &V) : Unit := (
    match *v {
      MkV(n, x) => (
        x := O;
        n := Zero
      ),
    }
  )
  reject def LieParam (v : &V) (k : Word) : Unit := (
    match *v {
      MkV(n, x) => (
        n := k;
        x := O
      ),
    }
  )
  reject def LieBorrow (v : &V) : Unit := (
    match *v {
      MkV(n, x) => (
        x := O;
        let r = &n;
        *r := Zero
      ),
    }
  )
  reject def BoomZ : False := Absurd((let v = MkV(Succ(Zero), O); LieZ(&v); v), refl)
  reject def BoomZRev : False := Absurd((let v = MkV(Succ(Zero), O); LieZRev(&v); v), refl)
  reject def BoomParam : False := Absurd((let v = MkV(Succ(Zero), O); LieParam(&v, Zero); v), refl)
  reject def BoomBorrow : False := Absurd((let v = MkV(Succ(Zero), O); LieBorrow(&v); v), refl)

  -- injectivity, restricted: equal lengths are taken apart; unequal ones are not, since
  -- `Eq(Fin1(a), x, y)` would compare values of different types
  def InjSame (a : Word) (x : Fin1(a)) (y : Fin1(a)) (h : Eq(V, MkV(a, x), MkV(a, y))) : Eq(Fin1(a), x, y) := h
  reject def InjLen (a : Word) (b : Word) (x : Fin1(a)) (y : Fin1(b)) (h : Eq(V, MkV(a, x), MkV(b, y))) : Eq(Word, a, b) := (
    let ⟨h1, h2⟩ = h;
    h1
  )
  def InjLenCong (a : Word) (b : Word) (x : Fin1(a)) (y : Fin1(b)) (h : Eq(V, MkV(a, x), MkV(b, y))) : Eq(Word, a, b) := cong(VN, h)

  -- a proof field: a write through the field its type mentions invalidates it
  def IsSucc (n : Word) : Prop := (
    match n {
      Zero => False,
      Succ(m) => ⊤,
    }
  )
  inductive Pos := MkPos(n : Word, h : IsSucc(n))
  def Grow (p : &Pos) : Unit := (
    match *p {
      MkPos(n, h) => (
        n := Succ(n);
        h := refl
      ),
    }
  )
  reject def ToZero (p : &Pos) : Unit := (
    match *p {
      MkPos(n, h) => n := Zero,
    }
  )
  reject def ToZeroProof (p : &Pos) : Unit := (
    match *p {
      MkPos(n, h) => (
        n := Zero;
        h := refl
      ),
    }
  )
  reject def StaleProof (p : &Pos) : IsSucc(Zero) := (
    match *p {
      MkPos(n, h) => (
        n := Zero;
        h
      ),
    }
  )
  -- in a proposition: the witness's proof is typed by the witness
  inductive ExSucc : Prop := WitS(w : Word, h : IsSucc(w))
  def ExOne : ExSucc := WitS(Succ(Zero), refl)
  def UseEx (e : ExSucc) : ⊤ := (
    match e {
      WitS(w, h) => match w {
        Zero => match h {},
        Succ(m) => refl,
      },
    }
  )

  -- K4: a type function in a field type. The type being declared may not be nested at a
  -- parameter that an inductive passes to a type function: here `NegIf(1, Bad)` is
  -- `Π(x : Bad). Void`, and nesting `Bad` in `NBox` is the positivity attack (D36)
  inductive Void : Type
  def absurdV (v : Void) : False := match v {}
  def NegIf (n : Word) (A : Type) : Type := (
    match n {
      Zero => Unit,
      Succ(m) => Π(x : A). Void,
    }
  )
  inductive NBox (A : Type) := MkNBox(n : Word, f : NegIf(n, A), h : IsSucc(n))
  reject inductive Bad := MkBad(b : NBox(Bad))
  reject def L (x : Bad) : Void := (
    match x {
      MkBad(b) => match b {
        MkNBox(n, f, h) => match n {
          Zero => match h {},
          Succ(m) => f(x),
        },
      },
    }
  )
  reject def K (x : Bad) : False := absurdV(L(x))
  reject def bad : Bad := MkBad(MkNBox[Bad](Succ(Zero), λ(y : Bad) : Void => L(y), refl))
  reject def Boom2 : False := K(bad)
  -- a type function whose value is a Π at the generic telescope is not first-order data
  def Neg (A : Type) : Type := Π(x : A). Void
  reject inductive NegBox (A : Type) := MkNegBox(f : Neg(A))
}

-- the exact number of declarations (a truncated file changes it)
#guard DepFields.decls.length == 51
-- each rejection for its reason
#guard (run "DepFields" DepFields).rejectedWith [
  ("NoneAt0", "field x of MkV has type One, expected Empty0"),
  ("BadTele", "[Ind] field x of MkBT: its type mentions n, which is not an earlier field"),
  ("LieV", "[Repack] a borrow of it ends, but it is open: field x of MkV holds a value of type ⌈Fin1(σ1)⌉, but its type from the earlier fields is Empty0"),
  ("ReadBroken", "[Repack] *v is read whole, but it is open"),
  ("PassBroken", "[Repack] *v is borrowed whole, but it is open"),
  ("PassBrokenVar", "[Repack] v is read whole, but it is open"),
  ("IdBroken", "[Repack] *v is read whole, but it is open"),
  ("IdMakesBroken", "[Repack] a borrow of it ends, but it is open"),
  ("Broken", "unknown constant LieV"),
  ("Boom", "unknown constant Broken"),
  ("LieZ", "[Repack] a borrow of it ends, but it is open: field x of MkV holds a value of type One, but its type from the earlier fields is Empty0"),
  ("LieZRev", "[Repack] a borrow of it ends, but it is open: field x of MkV holds a value of type One, but its type from the earlier fields is Empty0"),
  ("LieParam", "[Repack] a borrow of it ends, but it is open: field x of MkV holds a value of type One, but its type from the earlier fields is ⌈Fin1(σ1)⌉"),
  ("LieBorrow", "[Repack] a borrow of it ends, but it is open: field x of MkV holds a value of type One, but its type from the earlier fields is Empty0"),
  ("BoomZ", "unknown constant LieZ"),
  ("BoomParam", "unknown constant LieParam"),
  ("InjLen", "[Match] on h, whose type Eq(V, MkV(σ0, σ2), MkV(σ1, σ3)) is not an inductive type"),
  ("ToZero", "[Repack] a borrow of it ends, but it is open: field h of MkPos: it holds ⊥"),
  ("ToZeroProof", "the assigned value has type ⊤, expected False"),
  ("StaleProof", "[Open] (*p).h is a proof field invalidated by a write to a field its type mentions"),
  ("Bad", "field b of MkBad : NBox(Bad): Bad occurs at the parameter A of NBox, which NBox passes to a type function"),
  ("Boom2", "unknown constant K"),
  ("NegBox", "field f of MkNegBox : Neg(A) computes to Π")]

/-! ## A growable vector and a resizable hash table (a case study)

`Vec(E)` over the arrays library: push, in place and whole, an element borrow with a bound
against the length, lemmas about pushing, and `Table`, a hash table that stores its capacity
next to its slots and resizes by moving every entry into a new table. -/

ochr DepVec uses ArrayBench {
  inductive Vec (E : Type) := MkVec(n : Word, items : Array(E, n))
  def VNew (E : Type) : Vec(E) := MkVec[E](Zero, ArrEmpty(E))
  def VLen (E : Type) (v : Vec(E)) : Word := (
    match v {
      MkVec(n, items) => n,
    }
  )
  def Nop (v : &Vec(Word)) : Unit := ()

  -- rebuilt whole: [T-Ctor] checks the telescope
  def Push (E : Type) (v : &Vec(E)) (x : E) : Unit := (
    match *v {
      MkVec(n, items) => *v := MkVec[E](Succ(n), ArrPush(E, n, items, x)),
    }
  )
  reject def PushWrongLen (E : Type) (v : &Vec(E)) (x : E) : Unit := (
    match *v {
      MkVec(n, items) => *v := MkVec[E](n, ArrPush(E, n, items, x)),
    }
  )
  -- in place, either field first
  def PushInPlace (E : Type) (v : &Vec(E)) (x : E) : Unit := (
    match *v {
      MkVec(n, items) => (
        let m = n;
        n := Succ(m);
        items := ArrPush(E, m, items, x)
      ),
    }
  )
  def PushInPlaceRev (E : Type) (v : &Vec(E)) (x : E) : Unit := (
    match *v {
      MkVec(n, items) => (
        items := ArrPush(E, n, items, x);
        n := Succ(n)
      ),
    }
  )
  def Pop (E : Type) (v : &Vec(E)) (d : E) : E := (
    match *v {
      MkVec(n, items) => match n {
        Zero => d,
        Succ(m) => (
          let p = ArrPop(E, m, items);
          match p {
            Mk(rest, last) => (
              *v := MkVec[E](m, rest);
              last
            ),
          }
        ),
      },
    }
  )
  -- the user's example, `*v.0 := 2; *v.0 := [0,1]`, in both orders
  def Two : Array(Word, W(2)) := ArrPush(Word, Succ(Zero), ArrPush(Word, Zero, ArrEmpty(Word), Zero), Succ(Zero))
  def SetTwo (v : &Vec(Word)) : Unit := (
    match *v {
      MkVec(n, items) => (
        n := W(2);
        items := Two
      ),
    }
  )
  def SetTwoRev (v : &Vec(Word)) : Unit := (
    match *v {
      MkVec(n, items) => (
        items := Two;
        n := W(2)
      ),
    }
  )
  reject def Lie (E : Type) (v : &Vec(E)) : Unit := (
    match *v {
      MkVec(n, items) => n := Succ(n),
    }
  )
  reject def ReadBroken (v : &Vec(Word)) : Word := (
    match *v {
      MkVec(n, items) => (
        let m = n;
        n := Succ(m);
        let w = VLen(Word, clone(*v));
        n := m;
        w
      ),
    }
  )
  reject def MoveBroken (v : &Vec(Word)) : Unit := (
    match *v {
      MkVec(n, items) => (
        let m = n;
        n := Succ(m);
        let w = *v;
        *v := w
      ),
    }
  )
  reject def PassBroken (v : &Vec(Word)) : Unit := (
    match *v {
      MkVec(n, items) => (
        let m = n;
        n := Succ(m);
        Nop(&*v);
        n := m
      ),
    }
  )

  -- an element borrow, its bound against the length
  def VGetMut (v : &Vec(Word)) (i : Word) (h : Lt(i, VLen(Word, *v))) : &Word := (
    match *v {
      MkVec(n, items) => GetMut(n, AsSlice(Word, n, &items), i, h),
    }
  )
  def VSet (v : &Vec(Word)) (i : Word) (h : Lt(i, VLen(Word, *v))) (x : Word) : Unit := (
    let r = VGetMut(v, i, h);
    *r := x
  )
  -- (through the natives: runtime code does not see the array's representation, K3)
  def VGet (E : Type) (v : Vec(E)) (i : Word) (h : Lt(i, VLen(E, v))) : E := (
    match v {
      MkVec(n, items) => Read(E, n, AsSlice(E, n, &items), i, h),
    }
  )
  def PushRun : Id(Word, let v = VNew(Word); Push(Word, &v, W(3)); PushInPlace(Word, &v, W(4)); VLen(Word, v), W(2)) := refl
  def SetRun : Id(Word, 
      let v = VNew(Word);
      Push(Word, &v, W(3));
      PushInPlaceRev(Word, &v, W(4));
      VSet(&v, Succ(Zero), refl, W(9));
      VGet(Word, v, Succ(Zero), refl), W(9)) := refl
  def PopRun : Id(Word, let v = VNew(Word); Push(Word, &v, W(3)); Push(Word, &v, W(4)); Pop(Word, &v, Zero), W(4)) := refl
  reject def PushRunWrong : Id(Word, let v = VNew(Word); Push(Word, &v, W(3)); VLen(Word, v), W(2)) := refl

  -- pushing: the length grows by one, the old elements are unchanged, the new one is last
  def Pushed (E : Type) (v : Vec(E)) (x : E) : Vec(E) := (
    match v {
      MkVec(n, items) => MkVec[E](Succ(n), ArrPush(E, n, items, x)),
    }
  )
  def PushIs (E : Type) (v : &Vec(E)) (x : E) : Id(Unit, Push(E, v, x), *v := Pushed(E, clone(*v), x)) := (
    match *v {
      MkVec(n, items) => refl,
    }
  )
  def PushedLen (E : Type) (v : Vec(E)) (x : E) : Eq(Word, VLen(E, Pushed(E, v, x)), Succ(VLen(E, v))) := (
    match v {
      MkVec(n, items) => refl,
    }
  )
  reject def PushedLenTwo (E : Type) (v : Vec(E)) (x : E) : Eq(Word, VLen(E, Pushed(E, v, x)), Succ(Succ(VLen(E, v)))) := (
    match v {
      MkVec(n, items) => refl,
    }
  )
  def NthSnocLast (E : Type) (n : Word) (s : Slice(E, n)) (x : E) (h : Lt(n, Succ(n))) :
      Eq(E, Nth(E, Succ(n), SnocS(E, n, s, x), n, h), x) by n := (
    match n {
      Zero => refl,
      Succ(m) => match s {
        MkSlice(c) => match c {
          MkC(y, t) => NthSnocLast(E, m, t, x, h),
        },
      },
    }
  )
  def NthSnocOld (E : Type) (n : Word) (s : Slice(E, n)) (x : E) (i : Word) (h : Lt(i, n)) (h2 : Lt(i, Succ(n))) :
      Eq(E, Nth(E, Succ(n), SnocS(E, n, s, x), i, h2), Nth(E, n, s, i, h)) by i := (
    match n {
      Zero => match h {},
      Succ(m) => match s {
        MkSlice(c) => match c {
          MkC(y, t) => match i {
            Zero => refl,
            Succ(i2) => NthSnocOld(E, m, t, x, i2, h, h2),
          },
        },
      },
    }
  )
  def PushedLast (E : Type) (v : Vec(E)) (x : E) (h : Lt(VLen(E, v), VLen(E, Pushed(E, v, x)))) :
      Eq(E, VGet(E, Pushed(E, v, x), VLen(E, v), h), x) := (
    match v {
      MkVec(n, items) => match items {
        MkArray(s) => NthSnocLast(E, n, s, x, h),
      },
    }
  )
  def PushedOld (E : Type) (v : Vec(E)) (x : E) (i : Word) (h : Lt(i, VLen(E, v))) (h2 : Lt(i, VLen(E, Pushed(E, v, x)))) :
      Eq(E, VGet(E, Pushed(E, v, x), i, h2), VGet(E, v, i, h)) := (
    match v {
      MkVec(n, items) => match items {
        MkArray(s) => NthSnocOld(E, n, s, x, i, h, h2),
      },
    }
  )

  -- a hash table that stores its capacity and resizes
  inductive Table := MkTable(cap : Word, slots : Array(List(Entry), cap), len : Word)
  def TCap (t : Table) : Word := (
    match t {
      MkTable(cap, slots, len) => cap,
    }
  )
  def TLen (t : Table) : Word := (
    match t {
      MkTable(cap, slots, len) => len,
    }
  )
  def TNew (cap : Word) : Table := MkTable(cap, Replicate(List(Entry), cap, Nil), Zero)
  def TInsert (t : &Table) (k : Word) (v : Word) (hc : Lt(Zero, TCap(*t))) : Unit := (
    match *t {
      MkTable(cap, slots, len) => (
        let i = ModS(k, cap);
        let b = GetMutB(cap, AsSlice(List(Entry), cap, &slots), i, ModLt(k, cap, hc));
        let fresh = InsertB(b, k, v);
        match fresh {
          true => len := Succ(len),
          false => (),
        }
      ),
    }
  )
  def LeSuccL (a : Word) (b : Word) (h : Le(Succ(a), b)) : Le(a, b) by a := (
    match a {
      Zero => refl,
      Succ(a2) => match b {
        Zero => match h {},
        Succ(b2) => LeSuccL(a2, b2, h),
      },
    }
  )
  -- insert every entry of a bucket into the new slots
  def InsertAll (ncap : Word) (ns : &Slice(List(Entry), ncap)) (nl : &Word) (b : List(Entry)) (hc : Lt(Zero, ncap)) : Unit by b := (
    match b {
      Nil => (),
      Cons(e, rest) => match e {
        MkE(k, v) => (
          let bk = GetMutB(ncap, &*ns, ModS(k, ncap), ModLt(k, ncap, hc));
          let fresh = InsertB(bk, k, v);
          match fresh {
            true => *nl := Succ(*nl),
            false => (),
          };
          InsertAll(ncap, ns, nl, rest, hc)
        ),
      },
    }
  )
  -- re-insert the old buckets `0 … rem - 1`, by recursion over the old index
  def MoveAll (cap : Word) (old : &Slice(List(Entry), cap)) (ncap : Word) (ns : &Slice(List(Entry), ncap)) (nl : &Word)
      (rem : Word) (hr : Le(rem, cap)) (hc : Lt(Zero, ncap)) : Unit by rem := (
    match rem {
      Zero => (),
      Succ(r) => (
        let b = Read(List(Entry), cap, &*old, r, hr);
        InsertAll(ncap, &*ns, &*nl, b, hc);
        MoveAll(cap, old, ncap, ns, nl, r, LeSuccL(r, cap, hr), hc)
      ),
    }
  )
  def Resize (t : &Table) (ncap : Word) (hc : Lt(Zero, ncap)) : Unit := (
    match *t {
      MkTable(cap, slots, len) => (
        let ns = Replicate(List(Entry), ncap, Nil);
        let nl = Zero;
        MoveAll(cap, AsSlice(List(Entry), cap, &slots), ncap, AsSlice(List(Entry), ncap, &ns), &nl, cap, LeRefl(cap), hc);
        *t := MkTable(ncap, ns, nl)
      ),
    }
  )
  -- the new capacity with the old slots
  reject def ResizeKeep (t : &Table) (ncap : Word) : Unit := (
    match *t {
      MkTable(cap, slots, len) => cap := ncap,
    }
  )
  def ResizeRun : Id(Word, 
      let t = TNew(W(2));
      TInsert(&t, W(5), W(50), refl);
      TInsert(&t, W(3), W(30), refl);
      Resize(&t, W(4), refl);
      TInsert(&t, W(7), W(70), refl);
      TInsert(&t, W(5), W(51), refl);
      TLen(t), W(3)) := refl
  def ResizeRunCap : Id(Word, 
      let t = TNew(W(2));
      TInsert(&t, W(5), W(50), refl);
      Resize(&t, W(4), refl);
      TCap(t), W(4)) := refl
  reject def ResizeRunWrong : Id(Word, 
      let t = TNew(W(2));
      TInsert(&t, W(5), W(50), refl);
      Resize(&t, W(4), refl);
      TLen(t), W(2)) := refl
}

-- the exact number of declarations (a truncated file changes it)
#guard DepVec.decls.length == 44
-- each rejection for its reason
#guard (run "DepVec" DepVec).rejectedWith [
  ("PushWrongLen", "field items of MkVec has type ArrayOf(Cell(σ0, ⌈Cells(σ0, σ3)⌉)), expected ArrayOf(⌈Cells(σ0, σ3)⌉)"),
  ("Lie", "[Repack] a borrow of it ends, but it is open: field items of MkVec holds a value of type ArrayOf(⌈Cells(σ0, σ2)⌉), but its type from the earlier fields is ArrayOf(Cell(σ0, ⌈Cells(σ0, σ2)⌉))"),
  ("ReadBroken", "[Repack] *v is read whole, but it is open"),
  ("MoveBroken", "[Repack] *v is read whole, but it is open"),
  ("PassBroken", "[Repack] *v is borrowed whole, but it is open"),
  ("PushRunWrong", "the body of PushRunWrong has type ⊤, but the goal is False"),
  ("PushedLenTwo", "the body of PushedLenTwo has type ⊤, but the goal is Eq(Word, σ3, Succ(σ3))"),
  ("ResizeKeep", "[Repack] a borrow of it ends, but it is open: field slots of MkTable holds a value of type ArrayOf(⌈Cells(List(Entry), σ2)⌉), but its type from the earlier fields is ArrayOf(⌈Cells(List(Entry), σ1)⌉)"),
  ("ResizeRunWrong", "the body of ResizeRunWrong has type ⊤, but the goal is False")]
