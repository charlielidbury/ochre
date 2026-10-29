import Ochr.Examples.Logic
import Ochr.Examples.Word
import Ochr.Examples.Option
import Ochr.Examples.Array

/-! # 18. Dependent fields

A field's type may mention the fields before it (docs/06, D64): `MkVec(len : Word, cap : Word,
buf : Array(Opt(E), cap), hl : Le(len, cap))` stores a capacity next to an array of that many
cells, and a proof about both. The field types are a telescope ([Ind]), and a field's type is
computed from the earlier fields' current contents (`type(p.buf) = Array(Opt(E), content(p.cap))`).

Fields can be written in place, so a write can break the dependency for a while: after
`cap := Succ(cap)`, `buf` is still an array of the old length. The value is then *open*: each
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

The first block is self-contained; `DepVec`, over the arrays library, is a case study. -/

open Ochr.Test

ochr DepFields uses Logic, WordType, Options {
  inductive One := O
  -- `Fin1(0)` has no values (it is `Logic`'s `Void`), `Fin1(n + 1)` has one
  def Fin1 (n : Word) : Type := (
    match n {
      Zero => Void,
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
  -- twin of LieV: `n := n` instead of `n := Zero`, so `x` still has its type
  def LieVOk (v : &V) : Unit := (
    match *v {
      MkV(n, x) => n := n,
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
  -- twin of ReadBroken: `n` restored before `*v` is read whole
  def ReadBrokenOk (v : &V) : Word := (
    match *v {
      MkV(n, x) => (
        let m = n;
        n := Zero;
        n := m;
        let k = VN(clone(*v));
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
  -- twin of PassBroken: `n` restored before `*v` is borrowed whole
  def PassBrokenOk (v : &V) : Unit := (
    match *v {
      MkV(n, x) => (
        let m = n;
        n := Zero;
        n := m;
        Nop(&*v)
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
  -- twin of PassBrokenVar: no write to `n`, so `v` is packed when passed
  def PassBrokenVarOk (v : &V) : Unit := (
    match *v {
      MkV(n, x) => Nop(v),
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
  -- twin of IdBroken: `n` restored before `*v` is observed by `Id`
  def IdBrokenOk (v : &V) : Unit := (
    match *v {
      MkV(n, x) => (
        let m = n;
        n := Zero;
        n := m;
        let h : Id(Word, VN(clone(*v)), m) = refl;
        ()
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
  -- twin of IdMakesBroken: `n := n` in the `Id` sides, which breaks nothing
  def IdMakesBrokenOk (v : &V) : Unit := (
    match *v {
      MkV(n, x) => (
        let h : Id(Unit, n := n, n := n) = refl;
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
  -- twin of Broken: `Refill` (which repacks) instead of `LieV`
  def BrokenOk : V := (
    let v = MkV(Succ(Zero), O);
    Refill(&v);
    v
  )
  reject def Boom : False := Absurd(Broken, refl)
  -- twin of Boom: the true statement that the length is `Succ(Zero)`, not `Zero`
  def BoomOk : Eq(Word, VN(BrokenOk), Succ(Zero)) := refl
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
  -- twin of LieZ: `n := Succ(Zero)`, so `x := O` has the right type
  def LieZOk (v : &V) : Unit := (
    match *v {
      MkV(n, x) => (
        n := Succ(Zero);
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
  -- twin of LieZRev: `n := Succ(Zero)`, so `x := O` has the right type
  def LieZRevOk (v : &V) : Unit := (
    match *v {
      MkV(n, x) => (
        x := O;
        n := Succ(Zero)
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
  -- twin of LieParam: `n := Succ(k)`, so `Fin1(n)` is `One` for every `k`
  def LieParamOk (v : &V) (k : Word) : Unit := (
    match *v {
      MkV(n, x) => (
        n := Succ(k);
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
  -- twin of LieBorrow: the write through the borrow of `n` is `Succ(Zero)`
  def LieBorrowOk (v : &V) : Unit := (
    match *v {
      MkV(n, x) => (
        x := O;
        let r = &n;
        *r := Succ(Zero)
      ),
    }
  )
  reject def BoomZ : False := Absurd((let v = MkV(Succ(Zero), O); LieZ(&v); v), refl)
  -- twin of BoomZ: the true statement that the length is `Succ(Zero)`, using the repacking write
  def BoomZOk : Eq(Word, VN((let v = MkV(Succ(Zero), O); LieZOk(&v); v)), Succ(Zero)) := refl
  reject def BoomZRev : False := Absurd((let v = MkV(Succ(Zero), O); LieZRev(&v); v), refl)
  -- twin of BoomZRev: the true statement that the length is `Succ(Zero)`, using the repacking write
  def BoomZRevOk : Eq(Word, VN((let v = MkV(Succ(Zero), O); LieZRevOk(&v); v)), Succ(Zero)) := refl
  reject def BoomParam : False := Absurd((let v = MkV(Succ(Zero), O); LieParam(&v, Zero); v), refl)
  -- twin of BoomParam: the true statement that the length is `Succ(Zero)`, using the repacking write
  def BoomParamOk : Eq(Word, VN((let v = MkV(Succ(Zero), O); LieParamOk(&v, Zero); v)), Succ(Zero)) := refl
  reject def BoomBorrow : False := Absurd((let v = MkV(Succ(Zero), O); LieBorrow(&v); v), refl)
  -- twin of BoomBorrow: the true statement that the length is `Succ(Zero)`, using the repacking write
  def BoomBorrowOk : Eq(Word, VN((let v = MkV(Succ(Zero), O); LieBorrowOk(&v); v)), Succ(Zero)) := refl

  -- injectivity, restricted: equal lengths are taken apart; unequal ones are not, since
  -- `Eq(Fin1(a), x, y)` would compare values of different types
  def InjSame (a : Word) (x : Fin1(a)) (y : Fin1(a)) (h : Eq(V, MkV(a, x), MkV(a, y))) : Eq(Fin1(a), x, y) := h
  reject def InjLen (a : Word) (b : Word) (x : Fin1(a)) (y : Fin1(b)) (h : Eq(V, MkV(a, x), MkV(b, y))) : Eq(Word, a, b) := (
    let ⟨h1, h2⟩ = h;
    h1
  )
  -- twin of InjLen: the two lengths are the same `a`, so the equation is taken apart (as `InjSame`, to the equation between the fields)
  def InjLenOk (a : Word) (x : Fin1(a)) (y : Fin1(a)) (h : Eq(V, MkV(a, x), MkV(a, y))) : Eq(Fin1(a), x, y) := h
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
  -- D64 amended: a proof field assigned while the field its type mentions is lent must hold
  -- whatever the borrow leaves there. The borrow writes later, not through a field place, so
  -- nothing invalidates the proof again, and [Repack] cannot check a proof (`⋆`)
  reject def LieLent (p : &Pos) : Unit := (
    match *p {
      MkPos(n, h) => (
        let h0 = h;
        let r = &n;
        h := h0;
        *r := Zero
      ),
    }
  )
  -- twin of LieLent: no borrow of `n`, so the reassigned proof is about the same `n`
  def LieLentOk (p : &Pos) : Unit := (
    match *p {
      MkPos(n, h) => (
        let h0 = h;
        h := h0
      ),
    }
  )
  reject def BoomLent : False := (
    let p = MkPos(Succ(Zero), refl);
    LieLent(&p);
    match p {
      MkPos(n, h) => h,
    }
  )
  -- twin of BoomLent: the proof read back is about the same `n`, here `Succ(Zero)`
  def BoomLentOk : ⊤ := (
    let p = MkPos(Succ(Zero), refl);
    LieLentOk(&p);
    match p {
      MkPos(n, h) => h,
    }
  )
  -- the same through a returned borrow: the caller writes
  reject def GetLent (p : &Pos) : &Word := (
    match *p {
      MkPos(n, h) => (
        let h0 = h;
        let r = &n;
        h := h0;
        r
      ),
    }
  )
  reject def BoomGetLent : False := (
    let p = MkPos(Succ(Zero), refl);
    let r = GetLent(&p);
    *r := Zero;
    match p {
      MkPos(n, h) => h,
    }
  )
  -- a borrow still live when the proof is assigned (it could write again): refused, though
  -- it writes nothing more; ending it first is accepted (`RefillLent`)
  reject def RefillLentLive (p : &Pos) : Unit := (
    match *p {
      MkPos(n, h) => (
        let r = &n;
        *r := Succ(Zero);
        h := refl
      ),
    }
  )
  -- twin of RefillLentLive: the borrow ends (parenthesised) before the proof is assigned
  def RefillLentLiveOk (p : &Pos) : Unit := (
    match *p {
      MkPos(n, h) => (
        (let r = &n; *r := Succ(Zero));
        h := refl
      ),
    }
  )
  def RefillLent (p : &Pos) : Unit := (
    match *p {
      MkPos(n, h) => (
        (let r = &n; *r := Succ(Zero));
        h := refl
      ),
    }
  )
  -- an invariant that holds whatever the borrow writes: an element borrow out of a full cell
  inductive Cell := MkCell(o : Opt(Word), h : IsSome(Word, o))
  def CellGet (c : &Cell) : &Word := (
    match *c {
      MkCell(o, h) => match o {
        Some(v) => (
          let r = &v;
          h := refl;
          r
        ),
        None => match h {},
      },
    }
  )
  def CellGetRun : Id(Word, (
      let c = MkCell(Some(Zero), refl);
      let r = CellGet(&c);
      *r := Succ(Zero);
      match c {
        MkCell(o, h) => match o {
          Some(v) => v,
          None => match h {},
        },
      }), Succ(Zero)) := refl
  -- twin of GetLent: the invariant is `IsSome` of a cell (a `Cell`), which holds whatever the returned borrow writes
  def GetLentOk (c : &Cell) : &Word := (
    match *c {
      MkCell(o, h) => match o {
        Some(v) => (
          let h0 = h;
          let r = &v;
          h := h0;
          r
        ),
        None => match h {},
      },
    }
  )
  -- twin of BoomGetLent: the caller writes through a borrow whose invariant survives any write
  def BoomGetLentOk : Id(Word, (
      let c = MkCell(Some(Succ(Zero)), refl);
      let r = GetLentOk(&c);
      *r := Zero;
      match c {
        MkCell(o, h) => match o {
          Some(v) => v,
          None => match h {},
        },
      }), Zero) := refl
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
  def NegIf (n : Word) (A : Type) : Type := (
    match n {
      Zero => Unit,
      Succ(m) => Π(x : A). Void,
    }
  )
  inductive NBox (A : Type) := MkNBox(n : Word, f : NegIf(n, A), h : IsSucc(n))
  reject inductive Bad := MkBad(b : NBox(Bad))
  -- twin of Bad: `NBox` is given `Word` rather than the type being declared
  inductive BadOk := MkBadOk(b : NBox(Word))
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
  -- twin of L: over `BadOk`, applying `f` to a `Word` rather than to `x`
  def LOk (x : BadOk) : Void := (
    match x {
      MkBadOk(b) => match b {
        MkNBox(n, f, h) => match n {
          Zero => match h {},
          Succ(m) => f(Zero),
        },
      },
    }
  )
  reject def K (x : Bad) : False := absurdV(L(x))
  -- twin of K: over `BadOk` and `LOk`
  def KOk (x : BadOk) : False := absurdV(LOk(x))
  reject def bad : Bad := MkBad(MkNBox[Bad](Succ(Zero), λ(y : Bad) : Void => L(y), refl))
  reject def Boom2 : False := K(bad)
  -- twin of Boom2: over `BadOk`: from any `BadOk` (there is no closed one without a `Void`)
  def Boom2Ok (x : BadOk) : False := KOk(x)
  -- a type function whose value is a Π at the generic telescope is not first-order data
  def Neg (A : Type) : Type := Π(x : A). Void
  reject inductive NegBox (A : Type) := MkNegBox(f : Neg(A))
  -- twin of NegBox: the type function returns a pair `A × A` (first-order data), not a `Π`
  def Dup (A : Type) : Type := A × A
  inductive NegBoxOk (A : Type) := MkNegBoxOk(f : Dup(A))
}

-- each rejection for its reason
#guard (run "DepFields" DepFields).rejectedWith [
  ("NoneAt0", "field x of MkV has type One, expected Void"),
  ("BadTele", "[Ind] field x of MkBT: its type mentions n, which is not an earlier field"),
  ("LieV", "[Repack] a borrow of it ends, but it is open: field x of MkV holds a value of type ⌈Fin1(σ1)⌉, but its type from the earlier fields is Void"),
  ("ReadBroken", "[Repack] *v is read whole, but it is open"),
  ("PassBroken", "[Repack] *v is borrowed whole, but it is open"),
  ("PassBrokenVar", "[Repack] v is read whole, but it is open"),
  ("IdBroken", "[Repack] *v is read whole, but it is open"),
  ("IdMakesBroken", "[Repack] a borrow of it ends, but it is open"),
  ("Broken", "unknown constant LieV"),
  ("Boom", "unknown constant Broken"),
  ("LieZ", "[Repack] a borrow of it ends, but it is open: field x of MkV holds a value of type One, but its type from the earlier fields is Void"),
  ("LieZRev", "[Repack] a borrow of it ends, but it is open: field x of MkV holds a value of type One, but its type from the earlier fields is Void"),
  ("LieParam", "[Repack] a borrow of it ends, but it is open: field x of MkV holds a value of type One, but its type from the earlier fields is ⌈Fin1(σ1)⌉"),
  ("LieBorrow", "[Repack] a borrow of it ends, but it is open: field x of MkV holds a value of type One, but its type from the earlier fields is Void"),
  ("BoomZ", "unknown constant LieZ"),
  ("BoomParam", "unknown constant LieParam"),
  ("InjLen", "[Match] on h, whose type Eq(V, MkV(σ0, σ2), MkV(σ1, σ3)) is not an inductive type"),
  ("ToZero", "[Repack] a borrow of it ends, but it is open: field h of MkPos: it holds ⊥"),
  ("ToZeroProof", "the assigned value has type ⊤, expected False"),
  ("StaleProof", "[Open] (*p).h is a proof field invalidated by a write to a field its type mentions"),
  ("LieLent", "the proof assigned to h (while part of its value is lent, what the borrow holds unknown: [Open]) has type ⌈IsSucc(σ1)⌉, expected ⌈IsSucc(σ2)⌉"),
  ("BoomLent", "unknown constant LieLent"),
  ("GetLent", "the proof assigned to h (while part of its value is lent, what the borrow holds unknown: [Open]) has type ⌈IsSucc(σ1)⌉, expected ⌈IsSucc(σ2)⌉"),
  ("BoomGetLent", "unknown constant GetLent"),
  ("RefillLentLive", "the proof assigned to h (while part of its value is lent, what the borrow holds unknown: [Open]) has type ⊤, expected ⌈IsSucc(σ2)⌉"),
  ("Bad", "field b of MkBad : NBox(Bad): Bad occurs at the parameter A of NBox, which NBox passes to a type function"),
  ("Boom2", "unknown constant K"),
  ("NegBox", "field f of MkNegBox : Neg(A) computes to Π")]

/-! ## Stuck blocks are calls (D72)

A match on an abstract value that is followed by more code is closed off as a stuck block,
a call of an anonymous function of the places it uses ([Block]). A place the block takes by
borrow is its borrow parameter, whose borrow ends when the block returns: at the end of each
arm. So that end is a whole-again point ([Repack]), as a function's return is. Before D72 an
arm's lie about a dependent field was never re-checked there: the place received a sealed
program, which the dependency check cannot see into, and the direct path, which runs the arm
and checks nothing, kept a value of the wrong type (`LieSeq`) or a proof field ⊥ that fails
when the caller's borrow ends (`LieSeqProof`). In tail position the arms are checked to the
function's return, which caught the lie already (`LieV`). -/

ochr StuckBlocks uses DepFields {
  -- a data field: the arm lies, and code follows the match
  reject def LieSeq (v : &V) : Unit := (
    match *v {
      MkV(n, x) => n := Zero,
    };
    ()
  )
  -- twin of LieSeq: `n := n`, so `x` keeps its type
  def LieSeqOk (v : &V) : Unit := (
    match *v {
      MkV(n, x) => n := n,
    };
    ()
  )
  -- a proof field: the write invalidates `h`, which the block returns with
  reject def LieSeqProof (p : &Pos) : Unit := (
    match *p {
      MkPos(n, h) => n := Zero,
    };
    ()
  )
  -- twin of LieSeqProof: the proof is re-established before the arm returns
  def LieSeqProofOk (p : &Pos) : Unit := (
    match *p {
      MkPos(n, h) => (
        n := Succ(n);
        h := refl
      ),
    };
    ()
  )
  -- nested: the lie is in a block inside an arm of another block
  reject def LieNested (v : &V) (k : Word) : Unit := (
    match k {
      Zero => (
        match *v {
          MkV(n, x) => n := Zero,
        };
        ()
      ),
      Succ(j) => (),
    };
    ()
  )
  -- twin of LieNested: the inner arm writes `n := n`
  def LieNestedOk (v : &V) (k : Word) : Unit := (
    match k {
      Zero => (
        match *v {
          MkV(n, x) => n := n,
        };
        ()
      ),
      Succ(j) => (),
    };
    ()
  )
  -- the outer block is on another scrutinee and reaches `*v` only through its arm's match
  reject def LieOther (v : &V) (k : Word) : Unit := (
    match k {
      Zero => (
        match *v {
          MkV(n, x) => n := Zero,
        }
      ),
      Succ(j) => (),
    };
    ()
  )
  -- twin of LieOther: the inner match writes `n := n`
  def LieOtherOk (v : &V) (k : Word) : Unit := (
    match k {
      Zero => (
        match *v {
          MkV(n, x) => n := n,
        }
      ),
      Succ(j) => (),
    };
    ()
  )
  -- an owned local, read whole after the block
  reject def LieOwned (k : Word) : Word := (
    let w = One1;
    match k {
      Zero => (
        match w {
          MkV(n, x) => n := Zero,
        };
        ()
      ),
      Succ(j) => (),
    };
    VN(w)
  )
  -- twin of LieOwned: the arm writes `n := Succ(Zero)`, which `x : One` still fits
  def LieOwnedOk (k : Word) : Word := (
    let w = One1;
    match k {
      Zero => (
        match w {
          MkV(n, x) => n := Succ(Zero),
        };
        ()
      ),
      Succ(j) => (),
    };
    VN(w)
  )
  -- an arm that lends the broken value whole, and one that passes it on (both were already
  -- rejected inside the arm, by the whole use)
  reject def LieLend (v : &V) : Unit := (
    match *v {
      MkV(n, x) => (n := Zero; Nop(&*v)),
    };
    ()
  )
  -- twin of LieLend: the lend comes first, while `*v` is whole
  def LieLendOk (v : &V) : Unit := (
    match *v {
      MkV(n, x) => (Nop(&*v); ()),
    };
    ()
  )
  reject def LiePass (v : &V) : Unit := (
    match *v {
      MkV(n, x) => (n := Zero; Nop(v)),
    };
    ()
  )
  -- twin of LiePass: no write before `v` is passed on
  def LiePassOk (v : &V) : Unit := (
    match *v {
      MkV(n, x) => Nop(v),
    };
    ()
  )
  -- the lie in a closure's body, a stuck block there too
  reject def LieClosure (u : Unit) : Unit := (
    let f = (λ(w : &V) : Unit => (match *w { MkV(n, x) => n := Zero, }; ()));
    ()
  )
  -- twin of LieClosure: the closure's arm writes `n := n`
  def LieClosureOk (u : Unit) : Unit := (
    let f = (λ(w : &V) : Unit => (match *w { MkV(n, x) => n := n, }; ()));
    ()
  )
  -- the arm writes the index and returns a borrow into the value
  reject def LieRet (v : &V) : Unit := (
    let r = match *v { MkV(n, x) => (n := Succ(Zero); &n), };
    ()
  )
  -- twin of LieRet: the arm only returns the borrow
  def LieRetOk (v : &V) : Unit := (
    let r = match *v { MkV(n, x) => &n, };
    ()
  )
  -- a fail-safe incompleteness, pinned: a lie repaired by a second block. The direct path
  -- is whole again by the return, but the first block's borrow of `*v` ends with `*v` open
  reject def RepairLater (v : &V) : Unit := (
    match *v {
      MkV(n, x) => n := Zero,
    };
    match *v {
      MkV(n, x) => n := Succ(Zero),
    }
  )
  -- a fail-safe incompleteness, pinned: in a statement the side runs on its own copy, and a
  -- local it breaks is dropped broken on the direct path, harmlessly; the block's borrow of
  -- `w` still ends at its return
  reject def LieDropped (v : V) : Prop := Id(Unit, (let w = v; match w { MkV(n, x) => n := Zero, }; ()), ())
  -- twin of LieDropped: the side's arm writes `n := n`
  def LieDroppedOk (v : V) : Prop := Id(Unit, (let w = v; match w { MkV(n, x) => n := n, }; ()), ())
}

#guard (run "StuckBlocks" StuckBlocks).rejectedWith [
  ("LieSeq", "[Repack] *v is lent to a stuck match, whose arm returns with it, but it is open: field x of MkV holds a value of type ⌈Fin1(σ1)⌉, but its type from the earlier fields is Void"),
  ("LieSeqProof", "[Repack] *p is lent to a stuck match, whose arm returns with it, but it is open: field h of MkPos: it holds ⊥"),
  ("LieNested", "[Repack] *v is lent to a stuck match, whose arm returns with it, but it is open"),
  ("LieOther", "[Repack] *v is lent to a stuck match, whose arm returns with it, but it is open"),
  ("LieOwned", "[Repack] w is lent to a stuck match, whose arm returns with it, but it is open: field x of MkV holds a value of type One, but its type from the earlier fields is Void"),
  ("LieLend", "[Repack] *v is borrowed whole, but it is open"),
  ("LiePass", "[Repack] v is read whole, but it is open"),
  ("LieClosure", "[Repack] *w is lent to a stuck match, whose arm returns with it, but it is open"),
  ("LieRet", "[Repack] *v is lent to a stuck match, whose arm returns with it, but it is open: field x of MkV holds a value of type ⌈Fin1(σ1)⌉, but its type from the earlier fields is One"),
  ("RepairLater", "[Repack] *v is lent to a stuck match, whose arm returns with it, but it is open"),
  ("LieDropped", "[Repack] w is lent to a stuck match, whose arm returns with it, but it is open")]

/-! ## A growable vector (a case study)

An array never changes its length, so a growable vector is user code over one (docs/09 §7).
`Vec(E)` holds `len` elements in an array of `cap` cells of `Opt(E)`: `buf`'s type depends on
`cap`, and the proof field `hl` (`len ≤ cap`) on `len` and `cap`. That the first `len` cells hold
the elements and the rest nothing is `VInv`, a statement about a vector, not a field (`VGetP`
shows why). Push writes into cell `len`, and when the cells are full first moves every element
into a new array of `2·cap + 1` cells (`VMoveCells`, each cell exchanged with an empty one);
pop takes the last element out; get returns a borrow of an element, its cell's emptiness ruled
out by `VInv`. The lemmas say what each does (`PushLen`, `PushInv`, `PushAt`, `PushAtOld`,
`PopLen`, `PopInv`, `PopReturns`, `GetAt`), through the model of the moves (`MovedS`, `MoveIs`).
A hash table that stores its size next to its slots and resizes by moving every entry into a
new table is the hash map case study (`HashMap.lean`).

The cell representation is interim: `Opt(E)` cells cost a tag each at runtime, and the user is
weighing a tag-free `Uninit(E)` cell type (possibly the ⊥ a move leaves, docs/10), with which
"cells below `len` hold elements" could be a computed type rather than `VInv`. -/

ochr DepVec uses ArrayLemmas, Options {
  -- ## The cells
  -- A cell is `Options`' `Opt(E)`: an element or nothing (`IsSome`, `IsNone`).
  -- A borrow of the element in a cell known to hold one.
  def UnwrapMut (E : Type) (o : &Opt(E)) (h : IsSome(E, *o)) : &E := (
    match *o {
      None => match h {},
      Some(x) => &x,
    }
  )
  -- The first `len` cells of a view hold elements, and the rest nothing.
  def Packed (E : Type) (n : Word) (s : Slice(Opt(E), n)) (len : Word) : Prop by n := (
    match n {
      Zero => ⊤,
      Succ(m) => match s {
        MkSlice(c) => match c {
          MkC(x, t) => match len {
            Zero => IsNone(E, x) ∧ Packed(E, m, t, Zero),
            Succ(l) => IsSome(E, x) ∧ Packed(E, m, t, l),
          },
        },
      },
    }
  )

  -- ## The vector
  -- `len` elements in an array of `cap` cells: `buf`'s type depends on `cap`, and the proof field
  -- `hl` on `len` and `cap`. That the first `len` cells hold the elements is `VInv`, a statement
  -- about a vector rather than a field: a field would be invalidated by every borrow into `buf`,
  -- and `VGet` returns one.
  inductive Vec (E : Type) := MkVec(len : Word, cap : Word, buf : Array(Opt(E), cap), hl : Le(len, cap))
  def PackedA (E : Type) (n : Word) (a : Array(Opt(E), n)) (len : Word) : Prop := (
    match a {
      MkArray(s) => Packed(E, n, s, len),
    }
  )
  def VInv (E : Type) (v : Vec(E)) : Prop := (
    match v {
      MkVec(len, cap, buf, hl) => PackedA(E, cap, buf, len),
    }
  )
  def VNew (E : Type) : Vec(E) := MkVec[E](Zero, Zero, ([] : Array(Opt(E), Zero)), refl)
  def VLen (E : Type) (v : Vec(E)) : Word := (
    match v {
      MkVec(len, cap, buf, hl) => len,
    }
  )
  def VCap (E : Type) (v : Vec(E)) : Word := (
    match v {
      MkVec(len, cap, buf, hl) => cap,
    }
  )
  def Nop (v : &Vec(Word)) : Unit := ()

  -- ## Dependent fields at work
  -- rebuilt whole: [T-Ctor] checks the telescope
  def Clear (E : Type) (v : &Vec(E)) : Unit := *v := MkVec[E](Zero, Zero, ([] : Array(Opt(E), Zero)), refl)
  reject def ClearWrongCap (E : Type) (v : &Vec(E)) : Unit := *v := MkVec[E](Zero, Succ(Zero), ([] : Array(Opt(E), Zero)), refl)
  -- in place, in either order: the user's example (`*v.0 := 2; *v.0 := [0, 1]`), here with the
  -- capacity and the proof field too
  def Two : Array(Opt(Word), W(2)) := [Some(Zero), Some(Succ(Zero))]
  def SetTwo (v : &Vec(Word)) : Unit := (
    match *v {
      MkVec(len, cap, buf, hl) => (
        cap := W(2);
        buf := Two;
        len := W(2);
        hl := refl
      ),
    }
  )
  def SetTwoRev (v : &Vec(Word)) : Unit := (
    match *v {
      MkVec(len, cap, buf, hl) => (
        len := W(2);
        buf := Two;
        cap := W(2);
        hl := refl
      ),
    }
  )
  -- a capacity that is not the array's
  reject def Lie (E : Type) (v : &Vec(E)) : Unit := (
    match *v {
      MkVec(len, cap, buf, hl) => cap := Succ(cap),
    }
  )
  -- a write through `len` invalidates `hl` until it is proved again
  reject def LieLen (E : Type) (v : &Vec(E)) : Unit := (
    match *v {
      MkVec(len, cap, buf, hl) => len := Zero,
    }
  )
  def SetLenZero (E : Type) (v : &Vec(E)) : Unit := (
    match *v {
      MkVec(len, cap, buf, hl) => (
        len := Zero;
        hl := refl
      ),
    }
  )
  reject def ReadBroken (v : &Vec(Word)) : Word := (
    match *v {
      MkVec(len, cap, buf, hl) => (
        let c = cap;
        cap := Succ(c);
        let w = VLen(Word, clone(*v));
        cap := c;
        w
      ),
    }
  )
  reject def MoveBroken (v : &Vec(Word)) : Unit := (
    match *v {
      MkVec(len, cap, buf, hl) => (
        let c = cap;
        cap := Succ(c);
        let w = *v;
        *v := w
      ),
    }
  )
  reject def PassBroken (v : &Vec(Word)) : Unit := (
    match *v {
      MkVec(len, cap, buf, hl) => (
        let c = cap;
        cap := Succ(c);
        Nop(&*v);
        cap := c
      ),
    }
  )

  -- ## Push, pop and get
  -- Move cells `k, …, n - 1` of `os` into the same cells of `ns`, each by exchanging it with
  -- the cell it goes to (which holds nothing), by recursion on the count `rem` still to go.
  def VMoveCells (E : Type) (n : Word) (os : &Slice(Opt(E), n)) (m : Word) (ns : &Slice(Opt(E), m)) (k : Word) (rem : Word)
      (hr : Eq(Word, WAdd(rem, k), n)) (hnm : Le(n, m)) : Unit by rem := (
    match rem {
      Zero => (),
      Succ(r) => (
        let hk : Lt(k, n) = (rewrite hr in LeAddL(r, k));
        let hkm : Lt(k, m) = LeTrans(Succ(k), n, m, hk, hnm);
        let hr2 : Eq(Word, WAdd(r, Succ(k)), n) = (rewrite AddRS(r, k) in hr);
        SwapRefs(Opt(E), GetMut(Opt(E), n, &*os, k, hk), GetMut(Opt(E), m, &*ns, k, hkm));
        VMoveCells(E, n, os, m, ns, Succ(k), r, hr2, hnm)
      ),
    }
  )
  -- Push: write `Some(x)` into cell `len`. When the cells are full, first move the elements
  -- into a new array of `2·cap + 1` cells, and drop the old one.
  def VPush (E : Type) (v : &Vec(E)) (x : E) : Unit := (
    match *v {
      MkVec(len, cap, buf, hl) => (
        let d = LtDec(len, cap);
        match d {
          Yes(h) => (
            *GetMut(Opt(E), cap, AsSlice(Opt(E), cap, &buf), len, h) := Some(x);
            len := Succ(len);
            hl := h
          ),
          No(full) => (
            let ncap = Succ(WAdd(cap, cap));
            let hc : Le(cap, ncap) = LeStep(cap, WAdd(cap, cap), LeAddL(cap, cap));
            let h2 : Lt(len, ncap) = LeTrans(len, cap, WAdd(cap, cap), hl, LeAddL(cap, cap));
            let nb = ArrFromFn(Opt(E), ncap, λ(i : Word) : Opt(E) => None[E]);
            VMoveCells(E, cap, AsSlice(Opt(E), cap, &buf), ncap, AsSlice(Opt(E), ncap, &nb), Zero, cap, AddZeroR(cap), hc);
            cap := ncap;
            buf := nb;
            *GetMut(Opt(E), ncap, AsSlice(Opt(E), ncap, &buf), len, h2) := Some(x);
            len := Succ(len);
            hl := h2
          ),
        }
      ),
    }
  )
  -- Pop: take the element in cell `len - 1`, leaving nothing there; nothing for an empty vector.
  def VPop (E : Type) (v : &Vec(E)) : Opt(E) := (
    match *v {
      MkVec(len, cap, buf, hl) => match len {
        Zero => None[E],
        Succ(l) => (
          let h : Lt(l, cap) = hl;
          let l2 = l;
          let r = GetMut(Opt(E), cap, AsSlice(Opt(E), cap, &buf), l2, h);
          let o = *r;
          *r := None[E];
          len := l2;
          hl := LeOfLt(l2, cap, h);
          o
        ),
      },
    }
  )
  -- Cell `i < len` holds an element.
  def PackedNth (E : Type) (n : Word) (s : Slice(Opt(E), n)) (len : Word) (hp : Packed(E, n, s, len)) (i : Word) (hi : Lt(i, len)) (hn : Lt(i, n)) :
      IsSome(E, Nth(Opt(E), n, s, i, hn)) by i := (
    match n {
      Zero => match hn {},
      Succ(m) => match s {
        MkSlice(c) => match c {
          MkC(x, t) => match len {
            Zero => match hi {},
            Succ(l) => (
              let ⟨hx, ht⟩ = hp;
              match i {
                Zero => hx,
                Succ(i') => PackedNth(E, m, t, l, ht, i', hi, hn),
              }
            ),
          },
        },
      },
    }
  )
  -- ... so reading cell `i` through its borrow gives an element.
  def GetSome (E : Type) (cap : Word) (a : Array(Opt(E), cap)) (len : Word) (hp : PackedA(E, cap, a, len)) (i : Word)
      (h : Lt(i, len)) (hc : Lt(i, cap)) : IsSome(E, (let c = a; clone(*GetMut(Opt(E), cap, AsSlice(Opt(E), cap, &c), i, hc)))) := (
    match a {
      MkArray(s) => (
        let ⟨hv, hw⟩ = GetMutReadV(Opt(E), cap, s, i, hc);
        rewrite ← hv in PackedNth(E, cap, s, len, hp, i, h, hc)
      ),
    }
  )
  -- Get: a borrow of element `i`, whose cell holds one by the invariant.
  def VGet (E : Type) (v : &Vec(E)) (i : Word) (h : Lt(i, VLen(E, *v))) (inv : VInv(E, *v)) : &E := (
    match *v {
      MkVec(len, cap, buf, hl) => (
        let hc : Lt(i, cap) = LeTrans(Succ(i), len, cap, h, hl);
        let p = GetSome(E, cap, buf, len, inv, i, h, hc);
        UnwrapMut(E, GetMut(Opt(E), cap, AsSlice(Opt(E), cap, &buf), i, hc), p)
      ),
    }
  )
  def PushRun : Id(Word, (let v = VNew(Word); VPush(Word, &v, W(3)); VPush(Word, &v, W(4)); VPush(Word, &v, W(5)); VLen(Word, v)), W(3)) := refl
  def PushCapRun : Id(Word, (let v = VNew(Word); VPush(Word, &v, W(3)); VPush(Word, &v, W(4)); VCap(Word, v)), W(3)) := refl
  def PopRun : Id(Opt(Word), (let v = VNew(Word); VPush(Word, &v, W(3)); VPush(Word, &v, W(4)); VPop(Word, &v)), Some(W(4))) := refl
  def PopEmptyRun : Id(Opt(Word), (let v = VNew(Word); VPop(Word, &v)), None[Word]) := refl
  def GetRun : Id(Word, (let v = VNew(Word); VPush(Word, &v, W(3)); VPush(Word, &v, W(4)); *VGet(Word, &v, Succ(Zero), refl, refl)), W(4)) := refl
  def SetRun : Id(Word, (let v = VNew(Word); VPush(Word, &v, W(3)); VPush(Word, &v, W(4)); *VGet(Word, &v, Zero, refl, refl) := W(9); *VGet(Word, &v, Zero, refl, refl)), W(9)) := refl
  reject def PushRunWrong : Id(Word, (let v = VNew(Word); VPush(Word, &v, W(3)); VLen(Word, v)), W(2)) := refl

  -- ## What push, pop and get do
  -- The model of `VMoveCells`: both views, written cell by cell as the moves write them.
  def MovedS (E : Type) (n : Word) (ov : Slice(Opt(E), n)) (m : Word) (nv : Slice(Opt(E), m)) (k : Word) (rem : Word)
      (hr : Eq(Word, WAdd(rem, k), n)) (hnm : Le(n, m)) : Slice(Opt(E), m) by rem := (
    match rem {
      Zero => nv,
      Succ(r) => (
        let hk : Lt(k, n) = (rewrite hr in LeAddL(r, k));
        let hkm : Lt(k, m) = LeTrans(Succ(k), n, m, hk, hnm);
        let hr2 : Eq(Word, WAdd(r, Succ(k)), n) = (rewrite AddRS(r, k) in hr);
        MovedS(E, n, SetS(Opt(E), n, clone(ov), k, Nth(Opt(E), m, clone(nv), k, hkm)), m,
          SetS(Opt(E), m, nv, k, Nth(Opt(E), n, ov, k, hk)), Succ(k), r, hr2, hnm)
      ),
    }
  )
  -- One move: the two cells exchanged, on views given by value.
  def ExchNew (E : Type) (n : Word) (ov : Slice(Opt(E), n)) (m : Word) (nv : Slice(Opt(E), m)) (k : Word) (hk : Lt(k, n)) (hkm : Lt(k, m)) :
      Eq(Slice(Opt(E), m), (let co = ov; let cn = nv; SwapRefs(Opt(E), GetMut(Opt(E), n, &co, k, hk), GetMut(Opt(E), m, &cn, k, hkm)); cn),
        SetS(Opt(E), m, nv, k, Nth(Opt(E), n, ov, k, hk))) := (
    let ra = (let c = clone(ov); clone(*GetMut(Opt(E), n, &c, k, hk)));
    let ⟨ha, ha2⟩ = GetMutReadV(Opt(E), n, ov, k, hk);
    rewrite ← GetMutSetV(Opt(E), m, nv, k, ra, hkm) in rewrite ← ha in refl
  )
  def ExchOld (E : Type) (n : Word) (ov : Slice(Opt(E), n)) (m : Word) (nv : Slice(Opt(E), m)) (k : Word) (hk : Lt(k, n)) (hkm : Lt(k, m)) :
      Eq(Slice(Opt(E), n), (let co = ov; let cn = nv; SwapRefs(Opt(E), GetMut(Opt(E), n, &co, k, hk), GetMut(Opt(E), m, &cn, k, hkm)); co),
        SetS(Opt(E), n, ov, k, Nth(Opt(E), m, nv, k, hkm))) := (
    let rb = (let c = clone(nv); clone(*GetMut(Opt(E), m, &c, k, hkm)));
    let ⟨hb, hb2⟩ = GetMutReadV(Opt(E), m, nv, k, hkm);
    rewrite ← GetMutSetV(Opt(E), n, ov, k, rb, hk) in rewrite ← hb in refl
  )
  -- `VMoveCells` is its model.
  def MoveIs (E : Type) (n : Word) (ov : Slice(Opt(E), n)) (m : Word) (nv : Slice(Opt(E), m)) (k : Word) (rem : Word)
      (hr : Eq(Word, WAdd(rem, k), n)) (hnm : Le(n, m)) :
      Eq(Slice(Opt(E), m), (let co = ov; let cn = nv; VMoveCells(E, n, &co, m, &cn, k, rem, hr, hnm); cn),
        MovedS(E, n, ov, m, nv, k, rem, hr, hnm)) by rem := (
    match rem {
      Zero => refl,
      Succ(r) => (
        let hk : Lt(k, n) = (rewrite hr in LeAddL(r, k));
        let hkm : Lt(k, m) = LeTrans(Succ(k), n, m, hk, hnm);
        let hr2 : Eq(Word, WAdd(r, Succ(k)), n) = (rewrite AddRS(r, k) in hr);
        let ov1 = (let co = clone(ov); let cn = clone(nv); SwapRefs(Opt(E), GetMut(Opt(E), n, &co, k, hk), GetMut(Opt(E), m, &cn, k, hkm)); co);
        let nv1 = (let co = clone(ov); let cn = clone(nv); SwapRefs(Opt(E), GetMut(Opt(E), n, &co, k, hk), GetMut(Opt(E), m, &cn, k, hkm)); cn);
        rewrite ExchOld(E, n, ov, m, nv, k, hk, hkm) in rewrite ExchNew(E, n, ov, m, nv, k, hk, hkm) in
          MoveIs(E, n, ov1, m, nv1, Succ(k), r, hr2, hnm)
      ),
    }
  )
  -- Cells `k, …, n - 1` hold elements.
  def SomeFrom (E : Type) (n : Word) (s : Slice(Opt(E), n)) (k : Word) : Prop by n := (
    match n {
      Zero => ⊤,
      Succ(m) => match s {
        MkSlice(c) => match c {
          MkC(x, t) => match k {
            Zero => IsSome(E, x) ∧ SomeFrom(E, m, t, Zero),
            Succ(k') => SomeFrom(E, m, t, k'),
          },
        },
      },
    }
  )
  def SomeFromNth (E : Type) (n : Word) (s : Slice(Opt(E), n)) (k : Word) (hs : SomeFrom(E, n, s, k)) (hk : Lt(k, n)) :
      IsSome(E, Nth(Opt(E), n, s, k, hk)) by k := (
    match n {
      Zero => match hk {},
      Succ(m) => match s {
        MkSlice(c) => match c {
          MkC(x, t) => match k {
            Zero => (
              let ⟨hx, ht⟩ = hs;
              hx
            ),
            Succ(k') => SomeFromNth(E, m, t, k', hs, hk),
          },
        },
      },
    }
  )
  def SomeFromSet (E : Type) (n : Word) (s : Slice(Opt(E), n)) (k : Word) (y : Opt(E)) (hs : SomeFrom(E, n, s, k)) (hk : Lt(k, n)) :
      SomeFrom(E, n, SetS(Opt(E), n, s, k, y), Succ(k)) by k := (
    match n {
      Zero => match hk {},
      Succ(m) => match s {
        MkSlice(c) => match c {
          MkC(x, t) => match k {
            Zero => (
              let ⟨hx, ht⟩ = hs;
              ht
            ),
            Succ(k') => SomeFromSet(E, m, t, k', y, hs, hk),
          },
        },
      },
    }
  )
  -- Writing an element at `len` keeps the cells packed, one longer; taking the last one out,
  -- one shorter.
  def PackedSet (E : Type) (n : Word) (s : Slice(Opt(E), n)) (len : Word) (h : Lt(len, n)) (y : Opt(E)) (hy : IsSome(E, y))
      (hp : Packed(E, n, s, len)) : Packed(E, n, SetS(Opt(E), n, s, len, y), Succ(len)) by len := (
    match n {
      Zero => match h {},
      Succ(m) => match s {
        MkSlice(c) => match c {
          MkC(x, t) => match len {
            Zero => (
              let ⟨hx, ht⟩ = hp;
              ⟨hy, ht⟩
            ),
            Succ(l) => (
              let ⟨hx, ht⟩ = hp;
              ⟨hx, PackedSet(E, m, t, l, h, y, hy, ht)⟩
            ),
          },
        },
      },
    }
  )
  def PackedTake (E : Type) (n : Word) (s : Slice(Opt(E), n)) (l : Word) (h : Lt(l, n)) (hp : Packed(E, n, s, Succ(l))) :
      Packed(E, n, SetS(Opt(E), n, s, l, None[E]), l) by l := (
    match n {
      Zero => match h {},
      Succ(m) => match s {
        MkSlice(c) => match c {
          MkC(x, t) => match l {
            Zero => (
              let ⟨hx, ht⟩ = hp;
              ⟨refl, ht⟩
            ),
            Succ(l') => (
              let ⟨hx, ht⟩ = hp;
              ⟨hx, PackedTake(E, m, t, l', h, ht)⟩
            ),
          },
        },
      },
    }
  )
  -- Moving the elements from `k` on into cells that are packed up to `k` packs them all.
  def PackedMoved (E : Type) (n : Word) (ov : Slice(Opt(E), n)) (m : Word) (nv : Slice(Opt(E), m)) (k : Word) (rem : Word)
      (hr : Eq(Word, WAdd(rem, k), n)) (hnm : Le(n, m)) (hs : SomeFrom(E, n, ov, k)) (hp : Packed(E, m, nv, k)) :
      Packed(E, m, MovedS(E, n, ov, m, nv, k, rem, hr, hnm), n) by rem := (
    match rem {
      Zero => rewrite hr in hp,
      Succ(r) => (
        let hk : Lt(k, n) = (rewrite hr in LeAddL(r, k));
        let hkm : Lt(k, m) = LeTrans(Succ(k), n, m, hk, hnm);
        let hr2 : Eq(Word, WAdd(r, Succ(k)), n) = (rewrite AddRS(r, k) in hr);
        PackedMoved(E, n, SetS(Opt(E), n, ov, k, Nth(Opt(E), m, nv, k, hkm)), m, SetS(Opt(E), m, nv, k, Nth(Opt(E), n, ov, k, hk)),
          Succ(k), r, hr2, hnm,
          SomeFromSet(E, n, ov, k, Nth(Opt(E), m, nv, k, hkm), hs, hk),
          PackedSet(E, m, nv, k, hkm, Nth(Opt(E), n, ov, k, hk), SomeFromNth(E, n, ov, k, hs, hk), hp))
      ),
    }
  )
  -- Full cells hold elements from 0 on; new cells holding nothing are packed at 0.
  def PackedFull (E : Type) (n : Word) (s : Slice(Opt(E), n)) (l : Word) (e : Eq(Word, l, n)) (hp : Packed(E, n, s, l)) :
      SomeFrom(E, n, s, Zero) by n := (
    match n {
      Zero => refl,
      Succ(m) => match s {
        MkSlice(c) => match c {
          MkC(x, t) => match l {
            Zero => match e {},
            Succ(l') => (
              let ⟨hx, ht⟩ = hp;
              ⟨hx, PackedFull(E, m, t, l', e, ht)⟩
            ),
          },
        },
      },
    }
  )
  def PackedNone (E : Type) (m : Word) (k : Word) :
      Packed(E, m, FromFnS(Opt(E), m, λ(i : Word) : Opt(E) => None[E], k), Zero) by m := (
    match m {
      Zero => refl,
      Succ(m') => ⟨refl, PackedNone(E, m', Succ(k))⟩,
    }
  )
  def PushLen (E : Type) (v : &Vec(E)) (x : E) : Eq(Word, (let c = *v; VPush(E, &c, x); VLen(E, c)), Succ(VLen(E, *v))) := (
    match *v {
      MkVec(len, cap, buf, hl) => (
        let d = LtDec(len, cap);
        match d {
          Yes(h) => refl,
          No(full) => refl,
        }
      ),
    }
  )
  def PushInv (E : Type) (v : &Vec(E)) (x : E) (inv : VInv(E, *v)) : VInv(E, (let c = *v; VPush(E, &c, x); c)) := (
    match *v {
      MkVec(len, cap, buf, hl) => match buf {
        MkArray(s) => (
          let d = LtDec(len, cap);
          match d {
            Yes(h) => rewrite ← GetMutSetV(Opt(E), cap, s, len, Some(x), h) in PackedSet(E, cap, s, len, h, Some(x), refl, inv),
            No(full) => (
              -- full: the elements were moved into `2·cap + 1` new cells, then `x` written
              let e : Eq(Word, len, cap) = LeAntisym(len, cap, hl, full);
              let ncap = Succ(WAdd(cap, cap));
              let hc : Le(cap, ncap) = LeStep(cap, WAdd(cap, cap), LeAddL(cap, cap));
              let h2 : Lt(len, ncap) = LeTrans(len, cap, WAdd(cap, cap), hl, LeAddL(cap, cap));
              let nv = FromFnS(Opt(E), ncap, λ(i : Word) : Opt(E) => None[E], Zero);
              let mv = (let co = clone(s); let cn = clone(nv); VMoveCells(E, cap, &co, ncap, &cn, Zero, cap, AddZeroR(cap), hc); cn);
              rewrite ← GetMutSetV(Opt(E), ncap, mv, len, Some(x), h2) in
              rewrite ← MoveIs(E, cap, s, ncap, nv, Zero, cap, AddZeroR(cap), hc) in
              PackedSet(E, ncap, MovedS(E, cap, s, ncap, nv, Zero, cap, AddZeroR(cap), hc), len, h2, Some(x), refl,
                rewrite ← e in PackedMoved(E, cap, s, ncap, nv, Zero, cap, AddZeroR(cap), hc,
                  PackedFull(E, cap, s, len, e, inv), PackedNone(E, ncap, Zero)))
            ),
          }
        ),
      },
    }
  )
  -- Cell `i` of a view holds `o` (false past the end); of a vector's cells, `VAt`.
  def AtS (E : Type) (n : Word) (s : Slice(E, n)) (i : Word) (o : E) : Prop by n := (
    match n {
      Zero => False,
      Succ(m) => match s {
        MkSlice(c) => match c {
          MkC(x, t) => match i {
            Zero => Eq(E, x, o),
            Succ(i') => AtS(E, m, t, i', o),
          },
        },
      },
    }
  )
  def VAt (E : Type) (v : Vec(E)) (i : Word) (o : Opt(E)) : Prop := (
    match v {
      MkVec(len, cap, buf, hl) => match buf {
        MkArray(s) => AtS(Opt(E), cap, s, i, o),
      },
    }
  )
  def AtSetSame (E : Type) (n : Word) (s : Slice(E, n)) (i : Word) (y : E) (h : Lt(i, n)) : AtS(E, n, SetS(E, n, s, i, y), i, y) by i := (
    match n {
      Zero => match h {},
      Succ(m) => match s {
        MkSlice(c) => match c {
          MkC(x, t) => match i {
            Zero => refl,
            Succ(i') => AtSetSame(E, m, t, i', y, h),
          },
        },
      },
    }
  )
  def AtSetOther (E : Type) (n : Word) (s : Slice(E, n)) (i : Word) (j : Word) (y : E) (o : E) (ne : Π(e : Eq(Word, i, j)). False)
      (ha : AtS(E, n, s, i, o)) : AtS(E, n, SetS(E, n, s, j, y), i, o) by i := (
    match n {
      Zero => match ha {},
      Succ(m) => match s {
        MkSlice(c) => match c {
          MkC(x, t) => match i {
            Zero => match j {
              Zero => (
                let no = ne(refl);
                match no {}
              ),
              Succ(j') => ha,
            },
            Succ(i') => match j {
              Zero => ha,
              Succ(j') => AtSetOther(E, m, t, i', j', y, o, ne, ha),
            },
          },
        },
      },
    }
  )
  def AtNth (E : Type) (n : Word) (s : Slice(E, n)) (i : Word) (o : E) (h : Lt(i, n)) (ha : AtS(E, n, s, i, o)) :
      Eq(E, Nth(E, n, s, i, h), o) by i := (
    match n {
      Zero => match h {},
      Succ(m) => match s {
        MkSlice(c) => match c {
          MkC(x, t) => match i {
            Zero => ha,
            Succ(i') => AtNth(E, m, t, i', o, h, ha),
          },
        },
      },
    }
  )
  -- The moves leave the new cells below `k` alone, and put the old cells from `k` on in place.
  def AtMovedFrame (E : Type) (n : Word) (ov : Slice(Opt(E), n)) (m : Word) (nv : Slice(Opt(E), m)) (k : Word) (rem : Word)
      (hr : Eq(Word, WAdd(rem, k), n)) (hnm : Le(n, m)) (i : Word) (o : Opt(E)) (hik : Lt(i, k)) (ha : AtS(Opt(E), m, nv, i, o)) :
      AtS(Opt(E), m, MovedS(E, n, ov, m, nv, k, rem, hr, hnm), i, o) by rem := (
    match rem {
      Zero => ha,
      Succ(r) => (
        let hk : Lt(k, n) = (rewrite hr in LeAddL(r, k));
        let hkm : Lt(k, m) = LeTrans(Succ(k), n, m, hk, hnm);
        let hr2 : Eq(Word, WAdd(r, Succ(k)), n) = (rewrite AddRS(r, k) in hr);
        AtMovedFrame(E, n, SetS(Opt(E), n, ov, k, Nth(Opt(E), m, nv, k, hkm)), m, SetS(Opt(E), m, nv, k, Nth(Opt(E), n, ov, k, hk)),
          Succ(k), r, hr2, hnm, i, o, LeStep(Succ(i), k, hik),
          AtSetOther(Opt(E), m, nv, i, k, Nth(Opt(E), n, ov, k, hk), o, λ(e : Eq(Word, i, k)) : False => LtNe(i, k, hik, e), ha))
      ),
    }
  )
  def AtMoved (E : Type) (n : Word) (ov : Slice(Opt(E), n)) (m : Word) (nv : Slice(Opt(E), m)) (k : Word) (rem : Word)
      (hr : Eq(Word, WAdd(rem, k), n)) (hnm : Le(n, m)) (i : Word) (o : Opt(E)) (hi : Lt(i, n)) (hki : Le(k, i))
      (ha : AtS(Opt(E), n, ov, i, o)) : AtS(Opt(E), m, MovedS(E, n, ov, m, nv, k, rem, hr, hnm), i, o) by rem := (
    match rem {
      Zero => (
        let no = LtNe(i, i, LeTrans(Succ(i), k, i, rewrite ← hr in hi, hki), refl);
        match no {}
      ),
      Succ(r) => (
        let hk : Lt(k, n) = (rewrite hr in LeAddL(r, k));
        let hkm : Lt(k, m) = LeTrans(Succ(k), n, m, hk, hnm);
        let hr2 : Eq(Word, WAdd(r, Succ(k)), n) = (rewrite AddRS(r, k) in hr);
        let d = LtDec(k, i);
        match d {
          Yes(hlt) => AtMoved(E, n, SetS(Opt(E), n, ov, k, Nth(Opt(E), m, nv, k, hkm)), m, SetS(Opt(E), m, nv, k, Nth(Opt(E), n, ov, k, hk)),
            Succ(k), r, hr2, hnm, i, o, hi, hlt,
            AtSetOther(Opt(E), n, ov, i, k, Nth(Opt(E), m, nv, k, hkm), o, λ(e : Eq(Word, i, k)) : False => LtNe(k, i, hlt, rewrite e in refl), ha)),
          No(hge) => (
            let e : Eq(Word, k, i) = LeAntisym(k, i, hki, hge);
            AtMovedFrame(E, n, SetS(Opt(E), n, ov, k, Nth(Opt(E), m, nv, k, hkm)), m, SetS(Opt(E), m, nv, k, Nth(Opt(E), n, ov, k, hk)),
              Succ(k), r, hr2, hnm, i, o, rewrite e in LeRefl(Succ(k)),
              rewrite e in rewrite AtNth(Opt(E), n, ov, k, o, hk, rewrite ← e in ha) in AtSetSame(Opt(E), m, nv, k, Nth(Opt(E), n, ov, k, hk), hkm))
          ),
        }
      ),
    }
  )
  -- After a push the new element is last, and the old ones are where they were.
  def PushAt (E : Type) (v : &Vec(E)) (x : E) : VAt(E, (let c = *v; VPush(E, &c, x); c), VLen(E, *v), Some(x)) := (
    match *v {
      MkVec(len, cap, buf, hl) => match buf {
        MkArray(s) => (
          let d = LtDec(len, cap);
          match d {
            Yes(h) => rewrite ← GetMutSetV(Opt(E), cap, s, len, Some(x), h) in AtSetSame(Opt(E), cap, s, len, Some(x), h),
            No(full) => (
              let ncap = Succ(WAdd(cap, cap));
              let hc : Le(cap, ncap) = LeStep(cap, WAdd(cap, cap), LeAddL(cap, cap));
              let h2 : Lt(len, ncap) = LeTrans(len, cap, WAdd(cap, cap), hl, LeAddL(cap, cap));
              let nv = FromFnS(Opt(E), ncap, λ(i : Word) : Opt(E) => None[E], Zero);
              let mv = (let co = clone(s); let cn = clone(nv); VMoveCells(E, cap, &co, ncap, &cn, Zero, cap, AddZeroR(cap), hc); cn);
              rewrite ← GetMutSetV(Opt(E), ncap, mv, len, Some(x), h2) in
              rewrite ← MoveIs(E, cap, s, ncap, nv, Zero, cap, AddZeroR(cap), hc) in
              AtSetSame(Opt(E), ncap, MovedS(E, cap, s, ncap, nv, Zero, cap, AddZeroR(cap), hc), len, Some(x), h2)
            ),
          }
        ),
      },
    }
  )
  def PushAtOld (E : Type) (v : &Vec(E)) (x : E) (i : Word) (o : Opt(E)) (hi : Lt(i, VLen(E, *v))) (ha : VAt(E, *v, i, o)) :
      VAt(E, (let c = *v; VPush(E, &c, x); c), i, o) := (
    match *v {
      MkVec(len, cap, buf, hl) => match buf {
        MkArray(s) => (
          let l0 = len;
          let ne : Π(e : Eq(Word, i, l0)). False = (λ(e : Eq(Word, i, l0)) : False => LtNe(i, l0, hi, e));
          let d = LtDec(len, cap);
          match d {
            Yes(h) => rewrite ← GetMutSetV(Opt(E), cap, s, len, Some(x), h) in AtSetOther(Opt(E), cap, s, i, len, Some(x), o, ne, ha),
            No(full) => (
              let ncap = Succ(WAdd(cap, cap));
              let hc : Le(cap, ncap) = LeStep(cap, WAdd(cap, cap), LeAddL(cap, cap));
              let h2 : Lt(len, ncap) = LeTrans(len, cap, WAdd(cap, cap), hl, LeAddL(cap, cap));
              let nv = FromFnS(Opt(E), ncap, λ(i : Word) : Opt(E) => None[E], Zero);
              let mv = (let co = clone(s); let cn = clone(nv); VMoveCells(E, cap, &co, ncap, &cn, Zero, cap, AddZeroR(cap), hc); cn);
              rewrite ← GetMutSetV(Opt(E), ncap, mv, len, Some(x), h2) in
              rewrite ← MoveIs(E, cap, s, ncap, nv, Zero, cap, AddZeroR(cap), hc) in
              AtSetOther(Opt(E), ncap, MovedS(E, cap, s, ncap, nv, Zero, cap, AddZeroR(cap), hc), i, len, Some(x), o, ne,
                AtMoved(E, cap, s, ncap, nv, Zero, cap, AddZeroR(cap), hc, i, o, LeTrans(Succ(i), len, cap, hi, hl), refl, ha))
            ),
          }
        ),
      },
    }
  )
  -- A pop takes the last element out: one fewer, still packed, and the result is that element.
  def PopLen (E : Type) (v : &Vec(E)) : Eq(Word, (let c = *v; let o = VPop(E, &c); VLen(E, c)), Sub(VLen(E, *v), Succ(Zero))) := (
    match *v {
      MkVec(len, cap, buf, hl) => match len {
        Zero => refl,
        Succ(l) => refl,
      },
    }
  )
  def PopInv (E : Type) (v : &Vec(E)) (inv : VInv(E, *v)) : VInv(E, (let c = *v; let o = VPop(E, &c); c)) := (
    match *v {
      MkVec(len, cap, buf, hl) => match buf {
        MkArray(s) => match len {
          Zero => inv,
          Succ(l) => rewrite ← GetMutSetV(Opt(E), cap, s, l, None[E], hl) in PackedTake(E, cap, s, l, hl, inv),
        },
      },
    }
  )
  def PopReturns (E : Type) (v : &Vec(E)) (l : Word) (o : Opt(E)) (hn : Eq(Word, VLen(E, *v), Succ(l))) (ha : VAt(E, *v, l, o)) :
      Eq(Opt(E), (let c = *v; VPop(E, &c)), o) := (
    match *v {
      MkVec(len, cap, buf, hl) => match buf {
        MkArray(s) => match len {
          Zero => match hn {},
          Succ(l2) => (
            let h : Lt(l2, cap) = hl;
            let ⟨hv, hw⟩ = GetMutReadV(Opt(E), cap, s, l2, h);
            rewrite ← hv in AtNth(Opt(E), cap, s, l2, o, h, rewrite ← hn in ha)
          ),
        },
      },
    }
  )
  -- Reading through `VGet` gives the element in the cell.
  def GetAt (E : Type) (v : &Vec(E)) (i : Word) (y : E) (h : Lt(i, VLen(E, *v))) (inv : VInv(E, *v)) (ha : VAt(E, *v, i, Some(y))) :
      Eq(E, clone(*VGet(E, v, i, h, inv)), y) := (
    match *v {
      MkVec(len, cap, buf, hl) => match buf {
        MkArray(s) => (
          let hc : Lt(i, cap) = LeTrans(Succ(i), len, cap, h, hl);
          let ⟨hv, hw⟩ = GetMutReadV(Opt(E), cap, s, i, hc);
          let hn = AtNth(Opt(E), cap, s, i, Some(y), hc, ha);
          -- the cell read is the stuck read; split on it
          let o = (let c = clone(s); clone(*GetMut(Opt(E), cap, &c, i, hc)));
          match o {
            None => (
              let no : Eq(Opt(E), None[E], Some(y)) = trans(hv, hn);
              match no {}
            ),
            Some(y2) => trans(hv, hn),
          }
        ),
      },
    }
  )
  reject def PushLenTwo (E : Type) (v : &Vec(E)) (x : E) : Eq(Word, (let c = *v; VPush(E, &c, x); VLen(E, c)), Succ(Succ(VLen(E, *v)))) := (
    match *v {
      MkVec(len, cap, buf, hl) => (
        let d = LtDec(len, cap);
        match d {
          Yes(h) => refl,
          No(full) => refl,
        }
      ),
    }
  )
  -- Without the invariant, nothing rules out an empty cell.
  reject def VGetNoInv (E : Type) (v : &Vec(E)) (i : Word) (h : Lt(i, VLen(E, *v))) : &E := (
    match *v {
      MkVec(len, cap, buf, hl) => UnwrapMut(E, GetMut(Opt(E), cap, AsSlice(Opt(E), cap, &buf), i, LeTrans(Succ(i), len, cap, h, hl)), refl),
    }
  )
  -- Why the invariant is not a field: a get returns a borrow into `buf`, which clears such a field,
  -- and the vector must be whole again when the borrow parameter ends, with the get's borrow
  -- still live, so no proof can be assigned to it.
  inductive VecP (E : Type) := MkVecP(len : Word, cap : Word, buf : Array(Opt(E), cap), hl : Le(len, cap), hp : PackedA(E, cap, buf, len))
  reject def VGetP (E : Type) (v : &VecP(E)) (i : Word) (len : Word) (h : Lt(i, len)) : &E := (
    match *v {
      MkVecP(len2, cap, buf, hl, hp) => (
        let d = LtDec(i, len2);
        match d {
          Yes(hi) => (
            let hc : Lt(i, cap) = LeTrans(Succ(i), len2, cap, hi, hl);
            let p = GetSome(E, cap, buf, len2, hp, i, hi, hc);
            UnwrapMut(E, GetMut(Opt(E), cap, AsSlice(Opt(E), cap, &buf), i, hc), p)
          ),
          No(k) => match h {},
        }
      ),
    }
  )
}

-- each rejection for its reason
#guard (run "DepVec" DepVec).rejectedWith [
  ("ClearWrongCap", "field buf of MkVec has type ArrayOf(CellsEnd), expected ArrayOf(Cell(Opt(σ0), CellsEnd))"),
  ("Lie", "[Repack] a borrow of it ends, but it is open: field buf of MkVec holds a value of type ArrayOf(⌈Cells(Opt(σ0), σ3)⌉), but its type from the earlier fields is ArrayOf(Cell(Opt(σ0), ⌈Cells(Opt(σ0), σ3)⌉))"),
  ("LieLen", "[Repack] a borrow of it ends, but it is open: field hl of MkVec: it holds ⊥"),
  ("ReadBroken", "[Repack] *v is read whole, but it is open"),
  ("MoveBroken", "[Repack] *v is read whole, but it is open"),
  ("PassBroken", "[Repack] *v is borrowed whole, but it is open"),
  ("PushRunWrong", "the body of PushRunWrong has type ⊤, but the goal is False"),
  ("PushLenTwo", "the body of PushLenTwo has type ⊤, but the goal is Eq(Word, σ3, Succ(σ3))"),
  ("VGetNoInv", "argument 3 (h) has type ⊤, expected ⌈IsSome("),
  ("VGetP", "[Repack] a borrow of it ends, but it is open: field hp of MkVecP: it holds ⊥")]
