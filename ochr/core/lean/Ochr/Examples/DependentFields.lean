import Ochr.Examples.Nat
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
  -- D107: nested at its own parameter `A`, which it passes to `NegIf`: `QN(Unit, Zero)` is
  -- `QN(Unit, Zero) → Void` (Curry's paradox; the paper's example, appendix [Ind-decl])
  reject inductive QN (A : Type) (n : Word) := MkQN(z : QN(QN(A, n), Succ(Zero)), e : Eq(Word, n, Zero)) | StopN(f : NegIf(n, A), h : IsSucc(n))
  -- twin of QN: `StopN` holds an `A`, so `A` is nestable in `QNOk`
  inductive QNOk (A : Type) (n : Word) := MkQNOk(z : QNOk(QNOk(A, n), Succ(Zero)), e : Eq(Word, n, Zero)) | StopNOk(a : A, h : IsSucc(n))
  reject def DeltaQ (x : QN(Unit, Zero)) : False := (
    match x {
      MkQN(z, e) => match z {
        MkQN(z2, e2) => e2,
        StopN(f, h) => absurdV(f(x)),
      },
      StopN(f, h) => h,
    }
  )
  reject def BoomQ : False := DeltaQ(MkQN[Unit, Zero](StopN[QN(Unit, Zero), Succ(Zero)](λ(y : QN(Unit, Zero)) : Void => (let p = DeltaQ(y); let k : Void = match p {}; k), refl), refl))
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
  ("Bad", "field b of MkBad : NBox(Bad): Bad occurs at the parameter A of NBox, which is not nestable in NBox"),
  ("Boom2", "unknown constant K"),
  ("QN", "field z of MkQN : QN(QN(A, n), Succ(Zero)): QN occurs at the parameter A of QN, which is not nestable in QN"),
  ("DeltaQ", "unknown inductive type QN"), ("BoomQ", "unknown"),
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
function's return, which caught the lie already (`LieV`).

Since D93 a match on a value of a one-constructor type (`V`, `Pos`) is never closed off: an
unknown is refined in place and its one arm runs, at the generic call as at an instance. So the
one-constructor lies below are caught at the next whole-again point of the code after the match
(the borrow parameter's end at the return, `Id`'s observation, a whole read), and those inside
another match's block (`LieNested`, `LieOther`, `LieOwned`) still at that block's return. -/

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
  -- twin of LieRet: the arm returns a borrow of `x`, the field whose type depends, not of the
  -- index field: whatever is written through it has `x`'s type
  def LieRetOk (v : &V) : Unit := (
    let r = match *v { MkV(n, x) => &x, };
    ()
  )
  -- an arm that only returns a borrow of the index field: rejected by D73 while the match was a
  -- block (the borrow outlived the block's return); since D93 the match runs directly, nothing is
  -- written through `r`, and `*v` is whole when its borrow ends (Rust accepts `let r = &mut v.n;`)
  def LendIndex (v : &V) : Unit := (
    let r = match *v { MkV(n, x) => &n, };
    ()
  )
  -- a fail-safe incompleteness, pinned: a lie repaired later. Since D93 neither match is a
  -- block; at the return `n` is `Succ(Zero)` but `x` still has the type `Fin1(σ)` of the unknown
  -- length it came with, which `One` is not known to be
  reject def RepairLater (v : &V) : Unit := (
    match *v {
      MkV(n, x) => n := Zero,
    };
    match *v {
      MkV(n, x) => n := Succ(Zero),
    }
  )
  -- in a statement the side runs on its own copy, and a local it breaks is dropped broken,
  -- harmlessly: a fail-safe incompleteness while the match was a block (its borrow of `w` ended
  -- at its arm's return), accepted since D93, as the direct path always did
  def LieDropped (v : V) : Prop := Id(Unit, (let w = v; match w { MkV(n, x) => n := Zero, }; ()), (let w = v; ()))
  -- twin of LieDropped: the side's arm writes `n := n`
  def LieDroppedOk (v : V) : Prop := Id(Unit, (let w = v; match w { MkV(n, x) => n := n, }; ()), (let w = v; ()))
}

#guard (run "StuckBlocks" StuckBlocks).rejectedWith [
  ("LieSeq", "[Repack] a borrow of it ends, but it is open: field x of MkV holds a value of type ⌈Fin1(σ1)⌉, but its type from the earlier fields is Void"),
  ("LieSeqProof", "[Repack] a borrow of it ends, but it is open: field h of MkPos: it holds ⊥"),
  ("LieNested", "[Repack] *v is lent to a stuck match, whose arm returns with it, but it is open"),
  ("LieOther", "[Repack] *v is lent to a stuck match, whose arm returns with it, but it is open"),
  ("LieOwned", "[Repack] w is lent to a stuck match, whose arm returns with it, but it is open: field x of MkV holds a value of type One, but its type from the earlier fields is Void"),
  ("LieLend", "[Repack] *v is borrowed whole, but it is open"),
  ("LiePass", "[Repack] v is read whole, but it is open"),
  ("LieClosure", "[Repack] a borrow of it ends, but it is open"),
  ("LieRet", "[Repack] a borrow of it ends, but it is open: field x of MkV holds a value of type ⌈Fin1(σ1)⌉, but its type from the earlier fields is One"),
  ("RepairLater", "[Repack] a borrow of it ends, but it is open: field x of MkV holds a value of type ⌈Fin1(σ1)⌉, but its type from the earlier fields is One")]

/-! ## A lent part is unknown at a whole-again point (D73)

[Repack] checked a value whose part was still lent against what the borrow held at that
moment. A borrow of an index field that outlives a whole-again point lets its holder write
any value of the field's type later, after the check: `GetN` returns `&n` from a value whose
`x : Fin1(n)` depends on it, and its caller writes `Zero`. At a generic call `GetN` closes
off, so the owner holds a sealed program that no later check can look into; at an instance
the owner is `MkV(Zero, O)`, and a statement that never reads it whole computes to `False`
there (`BoomI2` was a closed proof of `False`). So a part that is still lent is checked as an
unknown of its type, as [Open] already checks a proof assigned while part of its value is
lent. A borrow of a field nothing depends on is unaffected (`GetW`); a borrow of an index
field whose dependents are proofs was already rejected, since the borrow sets them to ⊥. -/

ochr LentIndex uses DepFields {
  def Absurd1 (v : Void) : False := match v {}
  reject def GetN (v : &V) : &Word := match *v { MkV(n, x) => &n, }
  -- twin of GetN: a borrow of a field that no other field's type mentions
  inductive VW := MkVW(n : Word, x : Fin1(n), w : Word)
  def GetW (v : &VW) : &Word := match *v { MkVW(n, x, w) => &w, }
  -- the attack, as accepted before D73: the caller writes `Zero` through the borrow
  reject def A2e (v : &V) : Unit := (
    let r = GetN(v);
    *r := Zero;
    ()
  )
  -- every `V` has a nonzero length, since `Fin1(Zero)` is `Void`
  def NPos (v : V) : IsSucc(VN(v)) := (
    match v {
      MkV(n, x) => match n { Zero => match x {}, Succ(m) => refl, },
    }
  )
  -- a statement that inspects the length field without reading `c` whole
  reject def Boom2 (c0 : V) : Prop := (
    let c = c0;
    A2e(&c);
    match c { MkV(n, x) => IsSucc(clone(n)), }
  )
  reject def Boom2Pf (c0 : V) : Boom2(c0) := (
    let c = c0;
    A2e(&c);
    match c {
      MkV(n, x) => match n { Zero => match x {}, Succ(m) => refl, },
    }
  )
  reject def BoomI2 : False := Boom2Pf(One1)
  -- the same lie with a block in place of `GetN`
  reject def LendIndexWrite (v : &V) : Unit := (
    let r = match *v { MkV(n, x) => &n, };
    *r := Zero;
    ()
  )
  -- twin of LendIndexWrite: through a borrow of the independent field
  def LendFreeWrite (v : &VW) : Unit := (
    let r = match *v { MkVW(n, x, w) => &w, };
    *r := Zero;
    ()
  )
  -- and in a statement, with no helper at all: a proposition that is false on every path, which
  -- may be stated (rejected while the match was a block, D93); its proof is rejected, so no closed
  -- `False` follows: `x` keeps the type `Fin1(σ)` of the length it came with
  def BoomB (c0 : V) : Prop := (
    let c = c0;
    (let r = match c { MkV(n, x) => &n, }; *r := Zero; ());
    match c { MkV(n, x) => IsSucc(clone(n)), }
  )
  reject def BoomBPf (c0 : V) : BoomB(c0) := (
    let c = c0;
    (let r = match c { MkV(n, x) => &n, }; *r := Zero; ());
    match c {
      MkV(n, x) => match n { Zero => match x {}, Succ(m) => refl, },
    }
  )
  reject def BoomIB : False := BoomBPf(One1)
  -- The lent part is read as an unknown of its content's own type (docs/26, item 2). An index
  -- field is first-order data, so its content's type is always readable: a constructor value
  -- records its parameters (an unwritten one is an error, `None` here needs `None[Word]`), an
  -- unknown has its stored type, a sealed program its head's codomain. Were it unreadable, the
  -- loan would stay in the value and fail [Repack]'s leaf check, which reads the same type.
  def OptIdxTy (o : Opt(Word)) : Type := match o { None => One, Some(w) => Void, }
  inductive OptIdx := MkOI(o : Opt(Word), x : OptIdxTy(o))
  def VoidFalse (v : Void) : False := match v {}
  -- a concrete `None` in the lent index field
  reject def GetO (v : &OptIdx) : &Opt(Word) := (
    *v := MkOI(None[Word], O);
    match *v { MkOI(o, x) => &o, }
  )
  -- a sealed program there, typed through its head's codomain
  def OptOf (n : Word) : Opt(Word) := match n { Zero => None[Word], Succ(m) => Some(m), }
  reject def GetS (n : Word) (x0 : OptIdxTy(OptOf(n))) (v : &OptIdx) : &Opt(Word) := (
    *v := MkOI(OptOf(n), x0);
    match *v { MkOI(o, x) => &o, }
  )
  -- the whole attack in one closed definition, through a nested borrow of a concrete value
  reject def DirectFalse : False := (
    let c = MkOI(None[Word], O);
    let b = &c;
    let s = match *b { MkOI(o, x) => &o, };
    *s := Some(Zero);
    match c { MkOI(o, x) => match o { None => VoidFalse(match x {}), Some(w) => match x {}, }, }
  )
}

#guard (run "LentIndex" LentIndex).rejectedWith [
  ("GetO", "[Repack] a borrow of it ends, but it is open: field x of MkOI holds a value of type One, but its type from the earlier fields is ⌈OptIdxTy(σ"),
  ("GetS", "[Repack] a borrow of it ends, but it is open: field x of MkOI holds a value of type ⌈OptIdxTy(⌈OptOf(σ"),
  ("DirectFalse", "[Repack] a borrow of it ends, but it is open: field x of MkOI holds a value of type One, but its type from the earlier fields is ⌈OptIdxTy(σ"),
  ("GetN", "[Repack] a borrow of it ends, but it is open: field x of MkV holds a value of type ⌈Fin1(σ1)⌉, but its type from the earlier fields is"),
  ("A2e", "unknown constant GetN"),
  ("Boom2", "unknown constant A2e"),
  ("Boom2Pf", "unknown constant"),
  ("BoomI2", "unknown constant Boom2Pf"),
  ("LendIndexWrite", "[Repack] a borrow of it ends, but it is open: field x of MkV holds a value of type ⌈Fin1(σ1)⌉, but its type from the earlier fields is Void"),
  ("BoomBPf", "[Match] on c.x, whose type ⌈Fin1(σ1)⌉ is not an inductive type"),
  ("BoomIB", "unknown constant BoomBPf")]

/-! ## What a strong update may store (D110)

A strong update stores its value unchecked and types the field by what it holds ([Open]). That
reads back the field's type only from a value whose content determines it, so only a value whose
declared type is first-order data may be stored so; a proof, a borrow, a type or a function is
checked against the field's declared type at the current earlier fields, as any other write is.
Before, `x := refl` stored `⋆`, the field then read at its declared type `Fin1(Z) = Void` once the
index was rewritten, and a zero-arm match on it closed the goal (`Bad`, a closed proof of `False`
through `BoomF`): the value was a dropped local, and through a borrow parameter (`ViaParam`) the
path ended before the borrow's [Repack]. A borrow stored inside the value (`Leak`) left its lender
a loan nothing would fill, readable as data of any type and, stored back, at the field's declared
type (`ViaLoan`). Storing a constructor value of another type is the strong update's purpose and
stays (`OtherTree`), re-checked where the value must be whole again (`OtherTreeWhole`). Since D112
only a constructor value of a data inductive (a tree) is stored so, and only in a field whose
type is one at every instance: `Fin3(n)` is `Nat` at every instance, so `x : Fin3(n)` is a leaf
field and `x := O` is a checked write (`OtherData`, `OtherDataWhole`). -/

ochr StrongUpdate uses Nats {
  inductive Void : Type
  inductive One := O
  def Fin1 (n : Nat) : Type := match n { Z => Void, S(m) => One, }
  def Fin3 (n : Nat) : Type := match n { Z => Nat, S(m) => Nat, }
  inductive V := MkV(n : Nat, x : Fin1(n))
  inductive V3 := MkV3(n : Nat, x : Fin3(n))
  def AbsurdV (v : Void) : False := match v {}
  -- a proof: `refl`, a proof parameter, a proof of an arbitrary proposition
  reject def Bad : Void := (let c = MkV(S(Z), O); match c { MkV(n, x) => (x := refl; n := Z; let z : Void = match x {}; z), })
  reject def BoomF : False := AbsurdV(Bad)
  reject def BadSwap : Void := (let c = MkV(S(Z), O); match c { MkV(n, x) => (n := Z; x := refl; let z : Void = match x {}; z), })
  reject def ViaProofParam (h : Eq(Nat, Z, Z)) : Void := (let c = MkV(S(Z), O); match c { MkV(n, x) => (x := h; n := Z; let z : Void = match x {}; z), })
  reject def ViaAnyProof (P : Prop) (p : P) : Void := (let c = MkV(S(Z), O); match c { MkV(n, x) => (x := p; n := Z; let z : Void = match x {}; z), })
  -- through a borrow parameter, and through a borrow a call returns: no return point is reached
  reject def ViaParam (r : &V) : Void := ((*r).1 := refl; (*r).0 := Z; match (*r).1 {})
  def IdV (r : &V) : &V := r
  reject def ViaReturned (r : &V) : Void := (let s = IdV(r); (*s).1 := refl; (*s).0 := Z; match (*s).1 {})
  -- a borrow, a type, a function
  reject def Leak : Nat := (let c = MkV3(Z, 0); match c { MkV3(n, x) => (let w = Z; x := &w; *x := S(Z); x := 0; w), })
  reject def ViaLoan : Void := (let c = MkV(S(Z), O); match c { MkV(n, x) => (let w = O; x := &w; x := O; x := w; n := Z; let z : Void = match x {}; z), })
  reject def AType : Nat := (let c = MkV3(Z, 0); match c { MkV3(n, x) => (x := Nat; 0), })
  reject def AFunction : Nat := (let c = MkV3(Z, 0); match c { MkV3(n, x) => (x := (λ(u : Unit) : Nat => Z); 0), })
  -- the controls: the index rewritten alone (`x` keeps `O`, now not of `Void`); data of another
  -- type, the strong update's purpose, re-checked when the value is whole; a checked write of the
  -- field's own type; a borrow kept out of the value
  reject def Ctl1 : Void := (let c = MkV(S(Z), O); match c { MkV(n, x) => (n := Z; let z : Void = match x {}; z), })
  reject def OtherData : Nat := (let c = MkV3(Z, 0); match c { MkV3(n, x) => (x := O; 0), })
  reject def OtherDataWhole : V3 := (let c = MkV3(Z, 0); match c { MkV3(n, x) => (x := O; c), })
  inductive Two := TA | TB
  def OtherTree : Nat := (let c = MkV(S(Z), O); match c { MkV(n, x) => (x := TA; 0), })
  reject def OtherTreeWhole : V := (let c = MkV(S(Z), O); match c { MkV(n, x) => (x := TA; c), })
  def OwnType : V := (let c = MkV(S(Z), O); match c { MkV(n, x) => (x := O; c), })
  def BorrowOutside : Nat := (let w = Z; let r = &w; *r := S(Z); w)
}

#guard (run "StrongUpdate" StrongUpdate).rejectedWith [
  ("Bad", "the assigned value has type ⊤, expected One"),
  ("BoomF", "unknown constant Bad"),
  ("BadSwap", "the assigned value has type ⊤, expected Void"),
  ("ViaProofParam", "the assigned value has type ⊤, expected One"),
  ("ViaAnyProof", "the assigned value has type σ0, expected One"),
  ("ViaParam", "the assigned value has type ⊤, expected ⌈Fin1(σ1)⌉"),
  ("ViaReturned", "the assigned value has type ⊤, expected ⌈Fin1(σ1)⌉"),
  ("Leak", "the assigned value has type &Nat, expected Nat"),
  ("ViaLoan", "the assigned value has type &One, expected One"),
  ("AType", "the assigned value has type Type, expected Nat"),
  ("AFunction", "the assigned value has type Π(u : Unit). Nat, expected Nat"),
  ("Ctl1", "a match with no arms on c.x : One, which has constructors"),
  ("OtherData", "the assigned value has type One, expected Nat"),
  ("OtherDataWhole", "the assigned value has type One, expected Nat"),
  ("OtherTreeWhole", "[Repack] c is read whole, but it is open: field x of MkV holds a value of type Two, but its type from the earlier fields is One")]

/-! ## Leaf fields (D112)

A dependent field whose type is a data inductive at every instance (`Fin1(n)`, `Array(E, n)`) is a
TREE field: it holds a constructor value, which records its declaration and parameters, so while
its value is open it is typed by what it holds ([Open]). Any other dependent field is a LEAF
field (`Payload(b)` is `Nat` or `Unit`, `NF(b)` a function type or `Unit`): a number, the unit
value or a function does not say which instance of the field's type it was written at, and the
set model reads a leaf at its field's declared type. A leaf field is treated as a proof field is:
a write or borrow through an index its type mentions invalidates it (`⊥`, its borrows ended
first), an assignment is checked against its type at the current earlier fields (with the lent
parts unknown while part of the value is lent), and it is never typed by its content. A tree field
stores unchecked only a constructor value (D110, D112). A capture by `&` invalidates at a match's
entry on both paths, so a direct run of a match no longer keeps a proof its stuck form would
invalidate (`EntryKnown`). Each rejected shape stands beside an accepted rewrite; the runs are
checked by `refl`. -/
ochr LeafFields uses Nats {
  inductive Void : Type
  inductive One := O
  inductive Bit := B0 | B1
  def Payload (b : Bit) : Type := match b { B0 => Nat, B1 => Unit, }
  inductive Tagged := MkT(b : Bit, x : Payload(b))
  -- changing a tagged value in place: the tag first, then the payload
  def TagFirst (p : &Tagged) : Unit := match *p { MkT(b, x) => (b := B1; x := ()), }
  reject def PayloadFirst (p : &Tagged) : Unit := match *p { MkT(b, x) => (x := (); b := B1), }
  -- keeping the old payload: take it out before the tag changes
  def TakeOld (p : &Tagged) : Nat := match *p { MkT(b, x) => match b { B0 => (let old = x; b := B1; x := (); old), B1 => 0, }, }
  reject def ReadAfter (p : &Tagged) : Nat := match *p { MkT(b, x) => match b { B0 => (b := B1; let old = x; x := (); old), B1 => 0, }, }
  -- a borrow of the payload: used before the tag changes
  def LentUsedBefore (p : &Tagged) : Unit := match *p { MkT(b, x) => match b { B0 => (let r = &x; *r := 5; b := B1; x := ()), B1 => (), }, }
  reject def LentUsedAfter (p : &Tagged) : Unit := match *p { MkT(b, x) => match b { B0 => (let r = &x; b := B1; *r := 5; x := ()), B1 => (), }, }
  -- the whole value written
  def Whole (p : &Tagged) : Unit := (*p := MkT(B1, ()))
  def TagFirstRuns : Eq(Bit, (let t = MkT(B0, 3); TagFirst(&t); match t { MkT(b, x) => b, }), B1) := refl
  def TakeOldRuns : Eq(Nat, (let t = MkT(B0, 3); TakeOld(&t)), 3) := refl
  -- a leaf assigned while its index is lent is checked whatever the borrow may write
  def NV (b : Bit) : Type := match b { B0 => Nat, B1 => Void, }
  inductive DV := MkDV(b : Bit, x : NV(b))
  def AbsurdV (v : Void) : False := match v {}
  reject def LentIndexLie : Void := (let c = MkDV(B0, 3); match c { MkDV(b, x) => ((let r = &b; x := 4; *r := B1; ()); let z : Void = match x {}; z), })
  reject def BoomLent : False := AbsurdV(LentIndexLie)
  def LentIndexEnded : Nat := (let c = MkDV(B0, 3); match c { MkDV(b, x) => ((let r = &b; *r := B0; ()); x := 4; let y = x; y), })
  def LentIndexEndedRuns : Eq(Nat, LentIndexEnded, 4) := refl
  -- a function in a leaf field
  def NF (b : Bit) : Type := match b { B0 => Π(z : Nat). Nat, B1 => Unit, }
  inductive DF := MkDF(b : Bit, f : NF(b))
  def CallBefore : Nat := (let c = MkDF(B0, λ(z : Nat) : Nat => S(z)); match c { MkDF(b, f) => (let g = f; b := B1; f := (); g(2)), })
  reject def CallAfter : Nat := (let c = MkDF(B0, λ(z : Nat) : Nat => S(z)); match c { MkDF(b, f) => (b := B1; let g = f; f := (); g(2)), })
  def CallBeforeRuns : Eq(Nat, CallBefore, 3) := refl
  -- a field whose type is a data inductive at every instance stores only a constructor value
  def Fin1 (n : Nat) : Type := match n { Z => Void, S(m) => One, }
  inductive V := MkV(n : Nat, x : Fin1(n))
  reject def ParkNumber (v : &V) : Unit := match *v { MkV(n, x) => (let old = x; x := 5; x := old), }
  def ParkMoved (v : &V) : Unit := match *v { MkV(n, x) => (let old = x; x := old), }
  -- a capture by `&` in a match invalidates at the match's entry, whether it closes off or runs
  inductive PosN := MkPosN(n : Nat, h : Eq(Nat, n, 1))
  reject def EntryKnown (c0 : PosN) : Unit := (let c = c0; match c { MkPosN(n, h) => (match S(Z) { Z => (n := n; ()), S(m) => (), }; let h2 = h; ()), }; ())
  def EntryKnownBefore (c0 : PosN) : Unit := (let c = c0; match c { MkPosN(n, h) => (let h2 = h; match S(Z) { Z => (n := n; ()), S(m) => (), }; ()), }; ())
  reject def EntryStuck (k : Nat) (c0 : PosN) : Unit := (let c = c0; match c { MkPosN(n, h) => (match k { Z => (n := n; ()), S(m) => (), }; let h2 = h; ()), }; ())
  def EntryStuckBefore (k : Nat) (c0 : PosN) : Unit := (let c = c0; match c { MkPosN(n, h) => (let h2 = h; match k { Z => (n := n; ()), S(m) => (), }; ()), }; ())
  -- a borrow, a proof, a type or a function is never stored unchecked, in a tree field or a leaf
  -- field: each is a checked write and fails (D110, D112; D111 relies on it: a borrow never sits
  -- below the root of a value)
  reject def BorrowIntoTree (v : &V) : Unit := match *v { MkV(n, x) => (let old = x; let w = 0; x := &w; x := old), }
  reject def BorrowIntoLeaf (p : &Tagged) : Unit := match *p { MkT(b, x) => (let w = 0; x := &w; ()), }
  reject def ProofIntoTree (v : &V) : Unit := match *v { MkV(n, x) => (let old = x; x := refl; x := old), }
  reject def ProofIntoLeaf (p : &Tagged) : Unit := match *p { MkT(b, x) => (x := refl; ()), }
  reject def TypeIntoTree (v : &V) : Unit := match *v { MkV(n, x) => (let old = x; x := Nat; x := old), }
  reject def TypeIntoLeaf (p : &Tagged) : Unit := match *p { MkT(b, x) => (x := Nat; ()), }
  reject def FunctionIntoTree (v : &V) : Unit := match *v { MkV(n, x) => (let old = x; x := (λ(u : Unit) : Nat => 0); x := old), }
  reject def FunctionIntoLeaf (p : &Tagged) : Unit := match *p { MkT(b, x) => (x := (λ(u : Unit) : Nat => 0); ()), }
}

#guard (run "LeafFields" LeafFields).rejectedWith [
  ("PayloadFirst", "the assigned value has type Unit, expected ⌈Payload(σ1)⌉"),
  ("ReadAfter", "[Read] (*p).x was moved out or its borrow ended (reading ⊥)"),
  ("LentUsedAfter", "no such place *r: its path does not exist in ⊥"),
  ("LentIndexLie", "the value assigned to x (while part of its value is lent, what the borrow holds unknown: [Open]) has type Nat,"),
  ("BoomLent", "unknown constant LentIndexLie"),
  ("CallAfter", "[Read] c.f was moved out or its borrow ended (reading ⊥)"),
  ("ParkNumber", "the assigned value has type Nat, expected ⌈Fin1(σ1)⌉"),
  ("EntryKnown", "[Open] c.h is a proof field invalidated by a write to a field its type mentions"),
  ("EntryStuck", "[Open] c.h is a proof field invalidated by a write to a field its type mentions"),
  ("BorrowIntoTree", "the assigned value has type &Nat, expected ⌈Fin1(σ1)⌉"),
  ("BorrowIntoLeaf", "the assigned value has type &Nat, expected ⌈Payload(σ1)⌉"),
  ("ProofIntoTree", "the assigned value has type ⊤, expected ⌈Fin1(σ1)⌉"),
  ("ProofIntoLeaf", "the assigned value has type ⊤, expected ⌈Payload(σ1)⌉"),
  ("TypeIntoTree", "the assigned value has type Type, expected ⌈Fin1(σ1)⌉"),
  ("TypeIntoLeaf", "the assigned value has type Type, expected ⌈Payload(σ1)⌉"),
  ("FunctionIntoTree", "the assigned value has type Π(u : Unit). Nat, expected ⌈Fin1(σ1)⌉"),
  ("FunctionIntoLeaf", "the assigned value has type Π(u : Unit). Nat, expected ⌈Payload(σ1)⌉")]

/-! ## A field lent to a borrow a call returned (D112, amended)

A field lent to the borrow a call returns holds a mark over its content (`lent_g`, static ends,
D90/D99). Paths and the repack read through a mark; typing did not (`valType?` had no case for
one), so on main at 14aeb9cd a field so lent took its declared type at a rewritten index (`A2`,
`Direct`: a closed proof of `False` through `Boom`, the red team's), and after D112, which closed
that fallback, an ordinary read of such a field was rejected (`LeafLegit`, `LeafLegit2`,
`TreeLegit`). Typing now reads through a mark as through a loan, so a plain borrow and a borrow
returned by a call give the same verdict and message, row by row: a read, a write through it, a
re-borrow and a move of the field, each with and without an index write, in a tree field and in a
leaf field (`…Plain` against `…Ret`). The census rows read after an index write each form of
content a typed run leaves in a dependent field that the earlier blocks do not: a stuck program,
a fill of a stuck call's returned borrow, an unknown, a mark over a mark; each reads at the type
its content determines, and none reaches the error for a content of unreadable type. -/
ochr MarkedFields uses Nats {
  inductive Void : Type
  inductive One := O
  def Fin1 (n : Nat) : Type := match n { Z => Void, S(m) => One, }
  inductive V := MkV(n : Nat, x : Fin1(n))
  def AbsurdV (v : Void) : False := match v {}
  def Keep (r : &One) : &One := r
  def KeepN (r : &Nat) : &Nat := r
  def Payload (b : Nat) : Type := match b { Z => Nat, S(m) => Unit, }
  inductive L := MkL(b : Nat, p : Payload(b))
  reject def A2 : Void := (let c = MkV(S(Z), O); match c { MkV(n, x) => (let r = Keep(&x); n := Z; let k : Void = x; k), })
  reject def Boom : False := AbsurdV(A2)
  reject def Direct : Void := (let c = MkV(S(Z), O); match c { MkV(n, x) => (let r = Keep(&x); n := Z; x), })
  def LeafLegit : Nat := (let c = MkL(Z, 5); match c { MkL(b, p) => (let r = KeepN(&p); let k : Nat = p; k), })
  def LeafLegit2 : Nat := (let c = MkL(Z, 5); match c { MkL(b, p) => (let r = KeepN(&p); *r := 6; let k : Nat = p; k), })
  def TreeLegit : One := (let c = MkV(S(Z), O); match c { MkV(n, x) => (let r = Keep(&x); let k : One = x; k), })
  def TreeHonest : One := (let c = MkV(S(Z), O); match c { MkV(n, x) => (let r = Keep(&x); n := S(S(Z)); let y : One = x; y), })
  -- census: each form of content a typed run can leave in a dependent field, read after the index changes
  def StuckOne (k : Nat) : One := match k { Z => O, S(m) => O, }
  def CensusStuck (k : Nat) : One := (let c = MkV(S(Z), O); match c { MkV(n, x) => (x := StuckOne(k); n := S(S(Z)); let y : One = x; y), })
  reject def CensusStuckVoid (k : Nat) : Void := (let c = MkV(S(Z), O); match c { MkV(n, x) => (x := StuckOne(k); n := Z; let y : Void = x; y), })
  def PickOne (k : Nat) (a : &One) (b : &One) : &One := match k { Z => a, S(m) => b, }
  def CensusFill (k : Nat) : One := (let c = MkV(S(Z), O); match c { MkV(n, x) => (let w = O; let r = PickOne(k, &x, &w); n := S(S(Z)); let y : One = x; y), })
  reject def CensusFillVoid (k : Nat) : Void := (let c = MkV(S(Z), O); match c { MkV(n, x) => (let w = O; let r = PickOne(k, &x, &w); n := Z; let y : Void = x; y), })
  reject def CensusUnknown (c0 : V) : Void := (let c = c0; match c { MkV(n, x) => (n := Z; let y : Void = x; y), })
  def CensusMarkMark : One := (let c = MkV(S(Z), O); match c { MkV(n, x) => (let r = Keep(Keep(&x)); n := S(S(Z)); let y : One = x; y), })
  reject def CensusMarkMarkVoid : Void := (let c = MkV(S(Z), O); match c { MkV(n, x) => (let r = Keep(Keep(&x)); n := Z; let y : Void = x; y), })
  def LeafLegitRuns : Eq(Nat, LeafLegit, 5) := refl
  def LeafLegit2Runs : Eq(Nat, LeafLegit2, 6) := refl
  def TreeLegitRuns : Eq(One, TreeLegit, O) := refl
  def TreeReadPlain : One := (let c = MkV(S(Z), O); match c { MkV(n, x) => (let r = &x; let k : One = x; k), })
  def TreeReadRet : One := (let c = MkV(S(Z), O); match c { MkV(n, x) => (let r = Keep(&x); let k : One = x; k), })
  reject def TreeReadIdxPlain : Void := (let c = MkV(S(Z), O); match c { MkV(n, x) => (let r = &x; n := Z; let k : Void = x; k), })
  reject def TreeReadIdxRet : Void := (let c = MkV(S(Z), O); match c { MkV(n, x) => (let r = Keep(&x); n := Z; let k : Void = x; k), })
  def TreeWritePlain : One := (let c = MkV(S(Z), O); match c { MkV(n, x) => (let r = &x; *r := O; let k : One = x; k), })
  def TreeWriteRet : One := (let c = MkV(S(Z), O); match c { MkV(n, x) => (let r = Keep(&x); *r := O; let k : One = x; k), })
  reject def TreeWriteIdxPlain : Void := (let c = MkV(S(Z), O); match c { MkV(n, x) => (let r = &x; *r := O; n := Z; let k : Void = x; k), })
  reject def TreeWriteIdxRet : Void := (let c = MkV(S(Z), O); match c { MkV(n, x) => (let r = Keep(&x); *r := O; n := Z; let k : Void = x; k), })
  def TreeRebPlain : One := (let c = MkV(S(Z), O); match c { MkV(n, x) => (let r = &x; let s = &x; let k : One = *s; k), })
  def TreeRebRet : One := (let c = MkV(S(Z), O); match c { MkV(n, x) => (let r = Keep(&x); let s = &x; let k : One = *s; k), })
  reject def TreeRebIdxPlain : Void := (let c = MkV(S(Z), O); match c { MkV(n, x) => (let r = &x; n := Z; let s = &x; let k : Void = *s; k), })
  reject def TreeRebIdxRet : Void := (let c = MkV(S(Z), O); match c { MkV(n, x) => (let r = Keep(&x); n := Z; let s = &x; let k : Void = *s; k), })
  def TreeMovePlain : One := (let c = MkV(S(Z), O); match c { MkV(n, x) => (let r = &x; let k = x; k), })
  def TreeMoveRet : One := (let c = MkV(S(Z), O); match c { MkV(n, x) => (let r = Keep(&x); let k = x; k), })
  reject def TreeMoveIdxPlain : Void := (let c = MkV(S(Z), O); match c { MkV(n, x) => (let r = &x; n := Z; let k = x; k), })
  reject def TreeMoveIdxRet : Void := (let c = MkV(S(Z), O); match c { MkV(n, x) => (let r = Keep(&x); n := Z; let k = x; k), })
  def LeafReadPlain : Nat := (let c = MkL(Z, 5); match c { MkL(b, p) => (let r = &p; let k : Nat = p; k), })
  def LeafReadRet : Nat := (let c = MkL(Z, 5); match c { MkL(b, p) => (let r = KeepN(&p); let k : Nat = p; k), })
  reject def LeafReadIdxPlain : Nat := (let c = MkL(Z, 5); match c { MkL(b, p) => (let r = &p; b := S(Z); let k : Nat = p; k), })
  reject def LeafReadIdxRet : Nat := (let c = MkL(Z, 5); match c { MkL(b, p) => (let r = KeepN(&p); b := S(Z); let k : Nat = p; k), })
  def LeafWritePlain : Nat := (let c = MkL(Z, 5); match c { MkL(b, p) => (let r = &p; *r := 6; let k : Nat = p; k), })
  def LeafWriteRet : Nat := (let c = MkL(Z, 5); match c { MkL(b, p) => (let r = KeepN(&p); *r := 6; let k : Nat = p; k), })
  reject def LeafWriteIdxPlain : Nat := (let c = MkL(Z, 5); match c { MkL(b, p) => (let r = &p; *r := 6; b := S(Z); let k : Nat = p; k), })
  reject def LeafWriteIdxRet : Nat := (let c = MkL(Z, 5); match c { MkL(b, p) => (let r = KeepN(&p); *r := 6; b := S(Z); let k : Nat = p; k), })
  def LeafRebPlain : Nat := (let c = MkL(Z, 5); match c { MkL(b, p) => (let r = &p; let s = &p; let k : Nat = clone(*s); k), })
  def LeafRebRet : Nat := (let c = MkL(Z, 5); match c { MkL(b, p) => (let r = KeepN(&p); let s = &p; let k : Nat = clone(*s); k), })
  reject def LeafRebIdxPlain : Nat := (let c = MkL(Z, 5); match c { MkL(b, p) => (let r = &p; b := S(Z); let s = &p; 0), })
  reject def LeafRebIdxRet : Nat := (let c = MkL(Z, 5); match c { MkL(b, p) => (let r = KeepN(&p); b := S(Z); let s = &p; 0), })
  def LeafMovePlain : Nat := (let c = MkL(Z, 5); match c { MkL(b, p) => (let r = &p; let k = p; k), })
  def LeafMoveRet : Nat := (let c = MkL(Z, 5); match c { MkL(b, p) => (let r = KeepN(&p); let k = p; k), })
  reject def LeafMoveIdxPlain : Nat := (let c = MkL(Z, 5); match c { MkL(b, p) => (let r = &p; b := S(Z); let k = p; k), })
  reject def LeafMoveIdxRet : Nat := (let c = MkL(Z, 5); match c { MkL(b, p) => (let r = KeepN(&p); b := S(Z); let k = p; k), })
}

#guard (run "MarkedFields" MarkedFields).rejectedWith [
  ("A2", "the ascribed term has type One, expected Void"),
  ("Boom", "unknown constant A2"),
  ("Direct", "the body of Direct has type One, but the goal is Void"),
  ("CensusStuckVoid", "the ascribed term has type One, expected Void"),
  ("CensusFillVoid", "the ascribed term has type One, expected Void"),
  ("CensusUnknown", "the ascribed term has type ⌈Fin1(σ1)⌉, expected Void"),
  ("CensusMarkMarkVoid", "the ascribed term has type One, expected Void"),
  ("TreeReadIdxPlain", "the ascribed term has type One, expected Void"),
  ("TreeReadIdxRet", "the ascribed term has type One, expected Void"),
  ("TreeWriteIdxPlain", "the ascribed term has type One, expected Void"),
  ("TreeWriteIdxRet", "the ascribed term has type One, expected Void"),
  ("TreeRebIdxPlain", "the ascribed term has type One, expected Void"),
  ("TreeRebIdxRet", "the ascribed term has type One, expected Void"),
  ("TreeMoveIdxPlain", "the body of TreeMoveIdxPlain has type One, but the goal is Void"),
  ("TreeMoveIdxRet", "the body of TreeMoveIdxRet has type One, but the goal is Void"),
  ("LeafReadIdxPlain", "[Read] c.p was moved out or its borrow ended (reading ⊥)"),
  ("LeafReadIdxRet", "[Read] c.p was moved out or its borrow ended (reading ⊥)"),
  ("LeafWriteIdxPlain", "[Read] c.p was moved out or its borrow ended (reading ⊥)"),
  ("LeafWriteIdxRet", "[Read] c.p was moved out or its borrow ended (reading ⊥)"),
  ("LeafRebIdxPlain", "[Borrow] c.p was moved out (borrowing ⊥)"),
  ("LeafRebIdxRet", "[Borrow] c.p was moved out (borrowing ⊥)"),
  ("LeafMoveIdxPlain", "[Read] c.p was moved out or its borrow ended (reading ⊥)"),
  ("LeafMoveIdxRet", "[Read] c.p was moved out or its borrow ended (reading ⊥)")]

/-! ## Opened dependent values, attacked (D110, D112)

The attack of the dependent-values lane (`Meaning/Dep/HANDOFF.md`), as asserted rows. In order:
leaf fields read, borrowed or strongly updated after their index is rewritten (`L…`, `F…`); a
field read while its index is lent and the index then written through the borrow (`C3…`); a
positional write of the index (`B1`); a borrow of the dependent field kept across a rewrite of
the index (`B2…`); calls given the field at the new index's type (`B4…`); constructors, `Eq` and
`Id` at the new index (`B9…`, `B10…`); a match run on a known scrutinee (`J1…`); recursion passing
the open value on (`Rec…`); a proof extracted from a value whose parameters were not written
(`T…`); nested dependent values (`N…`); a proof's witness rewritten (`PS1`); a proof re-assigned
while the index is lent to a call's returned borrow (`G…`); closures and stuck blocks over an open
value (`CL…`, `SB…`); a repair through a borrow (`RB`); closed instances (`…r`, `…Runs`) and a
false equation as a control (`BadCtl`); strong updates of a number, unit, function, type, borrow
or proof into a tree field (`W…`, `H…`, `K…`). -/
ochr OpenAttacks uses DepFields {
  def NU (b : Word) : Type := match b { Zero => Nat, Succ(m) => Unit, }
  inductive DP := MkDP(b : Word, x : NU(b))
  def DP0 : DP := MkDP(Zero, 3)
  reject def Ctl : Unit := (3 : Unit)
  reject def L1 : Unit := (let c = MkDP(Zero, 3); match c { MkDP(b, x) => (b := Succ(Zero); let y = x; (y : Unit)), })
  reject def L1Nat : Nat := (let c = MkDP(Zero, 3); match c { MkDP(b, x) => (b := Succ(Zero); let y = x; y), })
  reject def L1NatRuns : Eq(Nat, L1Nat, 3) := refl
  reject def L2 (c0 : DP) : Unit := (let c = c0; match c { MkDP(b, x) => (b := Succ(Zero); let y = x; (y : Unit)), })
  reject def L2b (c0 : DP) : Unit := (let c = c0; match c { MkDP(b, x) => (b := Succ(Zero); let y = x; ()), })
  reject def L3 : Nat := (let c = MkDP(Succ(Zero), ()); match c { MkDP(b, x) => (x := 5; let y = x; y), })
  reject def L3Runs : Eq(Nat, L3, 5) := refl
  reject def L4 : Nat := (let c = MkDP(Zero, 3); match c { MkDP(b, x) => (b := Succ(Zero); let r = &x; let y = clone(*r); y), })
  reject def L4u : Unit := (let c = MkDP(Zero, 3); match c { MkDP(b, x) => (b := Succ(Zero); let r = &x; *r := (); ()), })
  reject def L5 : Unit := (let c = MkDP(Succ(Zero), ()); match c { MkDP(b, x) => (b := Zero; let y = x; y), })
  reject def L5n : Nat := (let c = MkDP(Succ(Zero), ()); match c { MkDP(b, x) => (b := Zero; let y = x; (y : Nat)), })
  def NF (b : Word) : Type := match b { Zero => Π(z : Nat). Nat, Succ(m) => Unit, }
  inductive DF := MkDF(b : Word, f : NF(b))
  reject def F1 : Nat := (let c = MkDF(Zero, λ(z : Nat) : Nat => S(z)); match c { MkDF(b, f) => (b := Succ(Zero); let g = f; g(2)), })
  reject def F1Runs : Eq(Nat, F1, 3) := refl
  reject def F1u : Unit := (let c = MkDF(Zero, λ(z : Nat) : Nat => S(z)); match c { MkDF(b, f) => (b := Succ(Zero); let g = f; (g : Unit)), })
  def VoidF (z : Void) : False := match z {}
  reject def C3a (v : &V) : False := match *v { MkV(n, x) => (let r = &n; let y = clone(x); *r := Zero; match y {}), }
  reject def C3b (v : &V) : False := match *v { MkV(n, x) => (let y = (let r = &n; let y0 = clone(x); *r := Zero; y0); match y {}), }
  reject def C3c (v : &V) : Unit := match *v { MkV(n, x) => (let y = (let r = &n; let y0 = clone(x); *r := Zero; y0); n := Succ(Zero); ()), }
  reject def C3d (c0 : V) : False := (let c = c0; match c { MkV(n, x) => (let y = (let r = &n; let y0 = clone(x); *r := Zero; y0); match y {}), })
  reject def C3e (c0 : V) : Void := (let c = c0; match c { MkV(n, x) => (let y = (let r = &n; let y0 = clone(x); *r := Zero; y0); y), })
  reject def B1 (p0 : Pos) : IsSucc(Zero) := (let p = p0; p.0 := Zero; match p { MkPos(n, h) => h, })
  def UseVoidRef (y : &Void) : False := match *y {}
  reject def B2 (c0 : V) : False := (let c = c0; match c { MkV(n, x) => (let rx = &x; let rn = &n; *rn := Zero; UseVoidRef(rx)), })
  reject def B2b (c0 : V) : Unit := (let c = c0; match c { MkV(n, x) => (let rx = &x; let rn = &n; *rn := Zero; *rx := O; ()), })
  reject def B4 (c0 : V) : False := (let c = c0; match c { MkV(n, x) => (n := Zero; UseVoidRef(&x)), })
  def UseFin (k : Word) (y : &Fin1(k)) : Unit := ()
  reject def B4b (c0 : V) : Unit := (let c = c0; match c { MkV(n, x) => (n := Zero; UseFin(Zero, &x)), })
  def B4c (c0 : V) : Unit := (let c = c0; match c { MkV(n, x) => (let m = clone(n); n := Zero; UseFin(m, &x); n := m), })
  reject def B9a : V := (let c = One1; match c { MkV(n, x) => (n := Zero; MkV(clone(n), x)), })
  def B9b : V := (let c = One1; match c { MkV(n, x) => (n := Zero; MkV(Succ(Zero), x)), })
  reject def B10a (c0 : V) : Prop := (let c = c0; match c { MkV(n, x) => n := Zero, }; Eq(V, c, c))
  reject def B10b (c0 : V) : Prop := (let c = c0; match c { MkV(n, x) => (n := Zero; Eq(Void, x, x)), })
  reject def B10c (c0 : V) : Prop := (let c = c0; match c { MkV(n, x) => (n := Zero; Id(Void, x, x)), })
  reject def B10d (c0 : V) : Prop := (let c = c0; match c { MkV(n, x) => n := Zero, }; Id(V, c, c))
  def J1 : Word := (let c = One1; match Zero { Zero => (match c { MkV(n, x) => n := Zero, }; ()), Succ(m) => (), }; match c { MkV(n, x) => clone(n), })
  reject def J1b : False := (let c = One1; match Zero { Zero => (match c { MkV(n, x) => n := Zero, }; ()), Succ(m) => (), }; match c { MkV(n, x) => match x {}, })
  reject def RecO (k : Nat) (v : &V) : Unit by k := match k { Z => (), S m => (match *v { MkV(n, x) => n := Zero, }; RecO(m, v)), }
  reject def RecF (k : Nat) (v : &V) : Unit by k := match k { Z => (), S m => match *v { MkV(n, x) => (n := Zero; RecF(m, v); n := Succ(Zero)), }, }
  inductive Tag (n : Word) := MkTag(h : IsSucc(n))
  inductive TW := MkTW(n : Word, y : Tag(n))
  def Mk1 : Tag(Succ(Zero)) := MkTag(refl)
  def Mk1L : Tag(Succ(Zero)) := (let t = MkTag[Succ(Zero)](refl); t)
  reject def T1 : IsSucc(Zero) := (let c = MkTW(Succ(Zero), Mk1); match c { MkTW(n, y) => (n := Zero; match y { MkTag(h) => h, }), })
  reject def T2 : IsSucc(Zero) := (let c = MkTW(Succ(Zero), Mk1L); match c { MkTW(n, y) => (n := Zero; match y { MkTag(h) => h, }), })
  reject def T3 : IsSucc(Zero) := (let c = MkTW(Succ(Zero), MkTag[Succ(Zero)](refl)); match c { MkTW(n, y) => (n := Zero; match y { MkTag(h) => h, }), })
  reject def T4 (c0 : TW) : IsSucc(Zero) := (let c = c0; match c { MkTW(n, y) => (n := Zero; match y { MkTag(h) => h, }), })
  def VAt (k : Word) : Type := match k { Zero => One, Succ(m) => V, }
  inductive WV := MkWV(k : Word, w : VAt(k))
  def N1 (c0 : WV) : Unit := (let c = c0; match c { MkWV(k, w) => (k := Succ(Zero); ()), })
  reject def N2 : False := (let c = MkWV(Succ(Zero), One1); match c { MkWV(k, w) => (k := Zero; match w { MkV(n, x) => (n := Zero; match x {}), }), })
  def N3 : Word := (let c = MkWV(Succ(Zero), One1); match c { MkWV(k, w) => (match w { MkV(n, x) => n := Zero, }; k := Zero; match w { MkV(n, x) => clone(n), }), })
  reject def N4 : False := (let c = MkWV(Succ(Zero), One1); match c { MkWV(k, w) => (match w { MkV(n, x) => n := Zero, }; match w { MkV(n, x) => match x {}, }), })
  reject def N5 : Unit := (let c = MkWV(Succ(Zero), One1); match c { MkWV(k, w) => (match w { MkV(n, x) => n := Zero, }; let ww = w; ()), })
  reject def PS1 (e : ExSucc) : IsSucc(Zero) := match e { WitS(w, h) => (w := Zero; h), }
  def PickW (k : Word) (a : &Word) (b : &Word) : &Word := match k { Zero => a, Succ(m) => b, }
  def G1 (p : &Pos) : Unit := match *p { MkPos(n, h) => (let h0 = h; let d = Succ(Zero); let r = PickW(Succ(Zero), &n, &d); h := h0; *r := Zero), }
  reject def G2 (p : &Pos) : Unit := match *p { MkPos(n, h) => (let h0 = h; let d = Succ(Zero); let r = PickW(Zero, &n, &d); h := h0; *r := Zero), }
  reject def G3 (k : Word) (p : &Pos) : Unit := match *p { MkPos(n, h) => (let h0 = h; let d = Succ(Zero); let r = PickW(k, &n, &d); h := h0; *r := Zero), }
  reject def G4 (k : Word) (p : &Pos) : Unit := match *p { MkPos(n, h) => (let h0 = h; let d = Succ(Zero); let r = PickW(k, &n, &d); h := h0; ()), }
  reject def CL1 (c0 : V) : Unit := (let c = c0; match c { MkV(n, x) => (n := Zero; let f = (λ(u : Unit) : Unit => (let y = x; ())); n := Succ(Zero); ()), })
  reject def CL2 (c0 : V) : Unit := (let c = c0; match c { MkV(n, x) => (n := Zero; let f = (λ(u : Unit) : Fin1(Zero) => x); ()), })
  def SB1 (k : Word) (c0 : V) : Unit := (let c = c0; match c { MkV(n, x) => (n := Zero; match k { Zero => (let r = &x; ()), Succ(m) => (), }; n := clone(n)), })
  def SB2 (k : Word) (v : &V) : Unit := match *v { MkV(n, x) => (let m = clone(n); n := Zero; match k { Zero => (let r = &x; ()), Succ(mm) => (), }; n := m), }
  def RB (v : &V) : Unit := match *v { MkV(n, x) => (let m = clone(n); let r = &n; *r := Zero; *r := m; ()), }
  def RBc : Word := (let c = One1; RB(&c); VN(c))
  def RBr : Eq(Word, RBc, Succ(Zero)) := refl
  def N3r : Eq(Word, N3, Zero) := refl
  def P1 : Pos := MkPos(Succ(Zero), refl)
  def G1c : Word := (let p = P1; G1(&p); match p { MkPos(n, h) => clone(n), })
  def G1r : Eq(Word, G1c, Succ(Zero)) := refl
  def SB2a : Word := (let c = One1; SB2(Zero, &c); VN(c))
  def SB2b : Word := (let c = One1; SB2(Succ(Zero), &c); VN(c))
  def SB2ar : Eq(Word, SB2a, Succ(Zero)) := refl
  def SB2br : Eq(Word, SB2b, Succ(Zero)) := refl
  reject def BadCtl : Eq(Word, RBc, Zero) := refl
  def N1c : Word := (let c = MkWV(Zero, O); N1(c); Zero)
  reject def W1 : Nat := (let c = One1; match c { MkV(n, x) => (x := 5; let y = x; x := O; y), })
  reject def W1r : Eq(Nat, W1, 5) := refl
  reject def W2 (c0 : V) : Nat := (let c = c0; match c { MkV(n, x) => (x := 5; let y = x; n := Succ(Zero); x := O; y), })
  reject def W3 (v : &V) : Unit := match *v { MkV(n, x) => (let old = x; x := (); x := old), }
  reject def W4 (v : &V) : Unit := match *v { MkV(n, x) => (x := (λ(z : Nat) : Nat => z); ()), }
  reject def H1 (v : &V) : Unit := match *v { MkV(n, x) => (let old = x; x := Nat; let T = x; x := old), }
  reject def H2 (v : &V) : Unit := match *v { MkV(n, x) => (let old = x; let w = Zero; x := &w; x := old), }
  reject def H3 (v : &V) : Unit := match *v { MkV(n, x) => (let old = x; x := refl; x := old), }
  reject def H4 (v : &V) : Nat := match *v { MkV(n, x) => (let old = x; x := Nat; let T = x; let k : T = 3; x := old; k), }
  reject def H5 : Eq(Nat, (let c = One1; H4(&c)), 3) := refl
  reject def K1 : False := (let c = One1; match c { MkV(n, x) => (x := refl; n := Zero; let z : False = match x {}; z), })
  reject def K2 : False := (let c = One1; match c { MkV(n, x) => (n := Zero; x := refl; let z : False = match x {}; z), })
  reject def K3 (v : &V) : False := match *v { MkV(n, x) => (let old = x; x := refl; n := Zero; let z : False = match x {}; z), }
  reject def K1Ctl : False := (let c = One1; match c { MkV(n, x) => (n := Zero; let z : False = match x {}; z), })
}

#guard (run "OpenAttacks" OpenAttacks).rejectedWith [
  ("Ctl", "the ascribed term has type Nat, expected Unit"),
  ("L1", "[Read] c.x was moved out or its borrow ended (reading ⊥)"),
  ("L1Nat", "[Read] c.x was moved out or its borrow ended (reading ⊥)"),
  ("L1NatRuns", "unknown constant L1Nat"),
  ("L2", "[Read] c.x was moved out or its borrow ended (reading ⊥)"),
  ("L2b", "[Read] c.x was moved out or its borrow ended (reading ⊥)"),
  ("L3", "the assigned value has type Nat, expected Unit"),
  ("L3Runs", "unknown constant L3"),
  ("L4", "[Borrow] c.x was moved out (borrowing ⊥)"),
  ("L4u", "[Borrow] c.x was moved out (borrowing ⊥)"),
  ("L5", "[Read] c.x was moved out or its borrow ended (reading ⊥)"),
  ("L5n", "[Read] c.x was moved out or its borrow ended (reading ⊥)"),
  ("F1", "[Read] c.f was moved out or its borrow ended (reading ⊥)"),
  ("F1Runs", "unknown constant F1"),
  ("F1u", "[Read] c.f was moved out or its borrow ended (reading ⊥)"),
  ("C3a", "[Match] on y, whose type ⌈Fin1(σ1)⌉ is not an inductive type"),
  ("C3b", "[Match] on y, whose type ⌈Fin1(σ1)⌉ is not an inductive type"),
  ("C3c", "[Repack] a borrow of it ends, but it is open: field x of MkV holds a value of ty"),
  ("C3d", "[Match] on y, whose type ⌈Fin1(σ1)⌉ is not an inductive type"),
  ("C3e", "the body of C3e has type ⌈Fin1(σ1)⌉, but the goal is Void"),
  ("B1", "[Open] p.h is a proof field invalidated by a write to a field its type mentions:"),
  ("B2", "argument 1 (y) has type &⌈Fin1(σ1)⌉, expected &Void"),
  ("B2b", "the assigned value has type One, expected ⌈Fin1(σ1)⌉"),
  ("B4", "argument 1 (y) has type &⌈Fin1(σ1)⌉, expected &Void"),
  ("B4b", "argument 2 (y) has type &⌈Fin1(σ1)⌉, expected &Void"),
  ("B9a", "field x of MkV has type One, expected Void"),
  ("B10a", "[Repack] c is read whole, but it is open: field x of MkV holds a value of type ⌈"),
  ("B10b", "the left side of Eq has type ⌈Fin1(σ1)⌉, expected Void"),
  ("B10c", "a side of Id has type ⌈Fin1(σ1)⌉, expected Void"),
  ("B10d", "[Repack] c is read whole, but it is open: field x of MkV holds a value of type ⌈"),
  ("J1b", "a match with no arms on c.x : One, which has constructors"),
  ("RecO", "[Repack] v is read whole, but it is open: field x of MkV holds a value of type ⌈"),
  ("RecF", "[Repack] v is read whole, but it is open: field x of MkV holds a value of type ⌈"),
  ("T1", "the body of T1 has type ⊤, but the goal is False"),
  ("T2", "the body of T2 has type ⊤, but the goal is False"),
  ("T3", "the body of T3 has type ⊤, but the goal is False"),
  ("T4", "the body of T4 has type ⌈IsSucc(σ1)⌉, but the goal is False"),
  ("N2", "a match with no arms on c.w.x : One, which has constructors"),
  ("N4", "a match with no arms on c.w.x : One, which has constructors"),
  ("N5", "[Repack] c.w is read whole, but it is open: field x of MkV holds a value of type"),
  ("PS1", "the body of PS1 has type ⌈IsSucc(σ0)⌉, but the goal is False"),
  ("G2", "the proof assigned to h (while part of its value is lent, what the borrow holds "),
  ("G3", "the proof assigned to h (while part of its value is lent, what the borrow holds "),
  ("G4", "the proof assigned to h (while part of its value is lent, what the borrow holds "),
  ("CL1", "[Repack] a closure or Π-type captures c, but it is open: field x of MkV holds a "),
  ("CL2", "[Repack] a closure or Π-type captures c, but it is open: field x of MkV holds a "),
  ("BadCtl", "the body of BadCtl has type ⊤, but the goal is False"),
  ("W1", "the assigned value has type Nat, expected One"),
  ("W1r", "unknown constant W1"),
  ("W2", "the assigned value has type Nat, expected ⌈Fin1(σ1)⌉"),
  ("W3", "the assigned value has type Unit, expected ⌈Fin1(σ1)⌉"),
  ("W4", "the assigned value has type Π(z : Nat). Nat, expected ⌈Fin1(σ1)⌉"),
  ("H1", "the assigned value has type Type, expected ⌈Fin1(σ1)⌉"),
  ("H2", "the assigned value has type &Word, expected ⌈Fin1(σ1)⌉"),
  ("H3", "the assigned value has type ⊤, expected ⌈Fin1(σ1)⌉"),
  ("H4", "[D55] T is written where a type is expected, but its declared type is not a sort"),
  ("H5", "unknown constant H4"),
  ("K1", "the assigned value has type ⊤, expected One"),
  ("K2", "the assigned value has type ⊤, expected Void"),
  ("K3", "the assigned value has type ⊤, expected ⌈Fin1(σ1)⌉"),
  ("K1Ctl", "a match with no arms on c.x : One, which has constructors")]

/-! ## A path that ends early leaves no value open at its caller (D106's negative result)

`StrongUpdate.ViaParam` reached `False` because its only path ended in a match with no arms, so the
[Repack] at the borrow parameter's end never ran, on a field D110 now never lets read as empty. With
D110 in place, every way of ending a path before its return was tried after opening the caller's
value (writing its index through a borrow parameter): a zero-arm match on an empty value the
function was given (`E1`), on a hypothesis false at every instance (`E2`), on a field made empty by
a split (`E3`, whose closed call takes the other arm, `E3C`): accepted, and unreachable at any
instance, since each needs an inhabitant of an empty type; on the opened field itself (`E4`, typed
by its content), moved out (`E5`), or a proof field the index write invalidated (`E6`): rejected; a
tail call passing the borrow on, whole or reborrowed (`E8`, `E9`), and a normal end after an opaque
call or a proof (`E10`, `E11`, `E12`): [Repack]. Only a manufactured emptiness, an opened field read
at its declared type, made the early end dangerous. -/

ochr EarlyEnd uses Nats {
  inductive Void : Type
  inductive One := O
  def Fin1 (n : Nat) : Type := match n { Z => Void, S(m) => One, }
  def Fin2 (n : Nat) : Type := match n { Z => Void, S(m) => Nat, }
  inductive V := MkV(n : Nat, x : Fin1(n))
  inductive V2 := MkV2(n : Nat, x : Fin2(n))
  inductive VP := MkVP(n : Nat, h : Eq(Nat, n, S(Z)))
  def ReadX (v : V) : Nat := match v { MkV(n, x) => 0, }
  def E1 (r : &V) (v : Void) : Unit := ((*r).0 := Z; match v {})
  def E2 (r : &V) (h : Eq(Nat, Z, S(Z))) : Unit := ((*r).0 := Z; match h {})
  def E3 (n : Nat) (x : Fin1(n)) (r : &V) : Unit := match n { Z => ((*r).0 := Z; match x {}), S(m) => (), }
  def E3C : Nat := (let c = MkV(S(Z), O); E3(S(Z), O, &c); ReadX(c))
  reject def E4 (r : &V) : Unit := ((*r).0 := Z; match (*r).1 {})
  reject def E5 (r : &V2) : Unit := (let y = (*r).1; (*r).0 := Z; match (*r).1 {})
  reject def E6 (r : &VP) : Unit := ((*r).0 := Z; match (*r).1 {})
  reject def E8 (k : Nat) (r : &V) : Unit by k := match k { Z => (), S(j) => ((*r).0 := Z; E8(j, r)), }
  reject def E9 (k : Nat) (r : &V) : Unit by k := match k { Z => (), S(j) => ((*r).0 := Z; E9(j, &*r)), }
  reject def E10 (r : &V) (h : Eq(Nat, (*r).0, S(Z))) : Eq(Nat, S(Z), S(Z)) := ((*r).0 := Z; refl)
  reject def E11 (f : Π(u : Unit). Void) (r : &V) : Void := ((*r).0 := Z; f(()))
  reject def E12 (r : &V) : Unit := ((*r).0 := Z; ())
}

#guard (run "EarlyEnd" EarlyEnd).rejectedWith [
  ("E4", "[Match] on (*r).1, whose type"),
  ("E5", "[Match] on (*r).1, which was moved out"),
  ("E6", "[Match] on (*r).1, which was moved out"),
  ("E8", "[Repack] r is read whole, but it is open"),
  ("E9", "[Repack] *r is borrowed whole, but it is open"),
  ("E10", "[Repack] a borrow of it ends, but it is open"),
  ("E11", "[Repack] a borrow of it ends, but it is open"),
  ("E12", "[Repack] a borrow of it ends, but it is open")]

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

-- ## A `J` that closes off is a block too (D75)
-- When `J`'s endpoints are not convertible, [T-J-stuck] checks the transported term `t` on a
-- private copy and closes the `J` off as a stuck block, which takes `t`'s places. Before D75 the
-- block's borrows were never checked where `t` ends (D72 checked only a stuck match's arms):
-- `JLie`'s `t` writes the length of `*v`, the block takes `*v` by `&`, and `*v` became a sealed
-- program of type `V`, which a later match splits as a whole `V` while the direct path, where the
-- endpoints are equal and `t` runs, leaves `*v` with length zero. `BoomJ` was a closed proof of
-- `False` (found by the dependent-fields model, notes/depfields-model.md).
ochr JBlocks uses DepFields {
  reject def JLie (a : Word) (b : Word) (h : Eq(Word, a, b)) (v : &V) : Unit := (
    match *v {
      MkV(n0, x0) => J(Word, a, b, λ(z : Word) : Type => Unit, h, match *v { MkV(n, x) => (n := Zero; ()), }),
    }
  )
  reject def LenStmt (c0 : V) : Prop := (
    let c = c0;
    JLie(Zero, Zero, refl, &c);
    match c { MkV(n, x) => IsSucc(clone(n)), }
  )
  reject def LenPf (c0 : V) : LenStmt(c0) := (
    let c = c0;
    JLie(Zero, Zero, refl, &c);
    match c {
      MkV(n, x) => match n { Zero => match x {}, Succ(m) => refl, },
    }
  )
  reject def BoomJ : False := LenPf(One1)
  -- twin of JLie: the transported term writes the length back unchanged, so `*v` is whole
  -- where the block's borrow ends
  def JSame (a : Word) (b : Word) (h : Eq(Word, a, b)) (v : &V) : Unit := (
    match *v {
      MkV(n0, x0) => J(Word, a, b, λ(z : Word) : Type => Unit, h, match *v { MkV(n, x) => (n := n; ()), }),
    }
  )
  -- and the same chain over it states and proves a true statement
  def LenStmtOk (c0 : V) : Prop := (
    let c = c0;
    JSame(Zero, Zero, refl, &c);
    match c { MkV(n, x) => IsSucc(clone(n)), }
  )
  def LenPfOk (c0 : V) : LenStmtOk(c0) := (
    let c = c0;
    JSame(Zero, Zero, refl, &c);
    match c {
      MkV(n, x) => match n { Zero => match x {}, Succ(m) => refl, },
    }
  )
  def PosOne : LenStmtOk(One1) := LenPfOk(One1)
}

#guard (run "JBlocks" JBlocks).rejectedWith [
  ("JLie", "[Repack] *v is lent to a stuck match, whose arm returns with it, but it is open"),
  ("LenStmt", "unknown constant JLie"),
  ("LenPf", "unknown constant LenStmt"),
  ("BoomJ", "unknown constant LenPf")]

-- ## The producer obligation (D76): every producer of a neutral of a dependent type
-- A sealed program is treated as whole on the generic path, so whatever produced it must have
-- checked whole what it stands for: a function at its body's return, a block at each arm's end
-- (`closeBlock` runs the arms itself). These attacks aim at the producers one at a time: a
-- closure's body (a block inside it, and its own return), an `Id` side, a `J` inside a closure,
-- and a block arm's result. Each lie is rejected at a [Return] or a whole-again point, and its
-- twin, which leaves the value whole, is accepted.
ochr Producers uses DepFields {
  reject def ClosLie (v : &V) : Unit := (
    let f = (λ(w : &V) : Unit => (match *w { MkV(n, x) => n := Zero, }; ()));
    f(v)
  )
  def ClosHonest (v : &V) : Unit := (
    let f = (λ(w : &V) : Unit => (match *w { MkV(n, x) => n := n, }; ()));
    f(v)
  )
  reject def ClosLieTail (v : &V) : Unit := (
    let f = (λ(w : &V) : Unit => match *w { MkV(n, x) => n := Zero, });
    f(v)
  )
  def ClosHonestTail (v : &V) : Unit := (
    let f = (λ(w : &V) : Unit => match *w { MkV(n, x) => n := n, });
    f(v)
  )
  reject def IdSideLie (c0 : V) : Prop := (let c = c0; Id(Unit, match c { MkV(n, x) => n := Zero, }, ()))
  def IdSideOk (c0 : V) : Prop := (let c = c0; Id(Unit, match c { MkV(n, x) => n := n, }, ()))
  reject def JInClos (a : Word) (b : Word) (h : Eq(Word, a, b)) (v : &V) : Unit := (
    let f = (λ(w : &V) : Unit => J(Word, a, b, λ(z : Word) : Type => Unit, h, (match *w { MkV(n, x) => (n := Zero; ()), }; ())));
    f(v)
  )
  def JInClosOk (a : Word) (b : Word) (h : Eq(Word, a, b)) (v : &V) : Unit := (
    let f = (λ(w : &V) : Unit => J(Word, a, b, λ(z : Word) : Type => Unit, h, (match *w { MkV(n, x) => (n := n; ()), }; ())));
    f(v)
  )
  reject def ArmResult (v : &V) : Word := (let y = match *v { MkV(n, x) => (n := Zero; clone(n)), }; y)
  def ArmResultOk (v : &V) : Word := (let y = match *v { MkV(n, x) => clone(n), }; y)
}

#guard (run "Producers" Producers).rejectedWith [
  ("ClosLie", "[Repack] a borrow of it ends, but it is open"),
  ("ClosLieTail", "[Repack] a borrow of it ends, but it is open"),
  ("IdSideLie", "[Repack] Id observes it, but it is open"),
  ("JInClos", "[Repack] *w is lent to a stuck match, whose arm returns with it, but it is open"),
  ("ArmResult", "[Repack] a borrow of it ends, but it is open")]

-- ## A one-constructor arm runs directly (D93): its lies are caught after it
-- Since D93 a match on a value of a one-constructor type never closes off, so the end of its arm
-- is no longer a block's return. A value it breaks stays open after it, as after a write outside
-- any match (D64), and every way the value reaches code that relies on its type is a whole-again
-- point the generic path checks, or a read of a field typed by its content ([Open]). These
-- attacks carry a broken `V` past the end of a directly run arm: read by the field's telescope
-- type, copied, moved, passed, returned (whole, reborrowed, a field, the index), captured, observed,
-- through `J` (direct and closed off), into a stuck call (whole, or its index field), through a
-- join and a later partial repair, and into a statement whose proof would be a closed `False`.
-- Each is rejected, at the check its reason names.
ochr DirectArm uses DepFields {
  def VoidF (v : Void) : False := match v {}
  def Stuck (k : Word) (v : &V) : Unit := match k { Zero => (), Succ(m) => () }
  def StuckN (k : Word) (n : &Word) : Unit := match k { Zero => (), Succ(m) => () }
  reject def ProjAfter (c0 : V) : False := (let c = c0; match c { MkV(n, x) => n := Zero, }; match c.1 {})
  reject def MatchAfter (c0 : V) : False := (let c = c0; match c { MkV(n, x) => n := Zero, }; match c { MkV(n, x) => match x {}, })
  reject def InArm (c0 : V) : False := (let c = c0; match c { MkV(n, x) => (n := Zero; match x {}), })
  reject def CloneAfter (c0 : V) : False := (let c = c0; match c { MkV(n, x) => n := Zero, }; let y = clone(c); match y { MkV(n, x) => match x {}, })
  reject def CloneThrough (v : &V) : False := (match *v { MkV(n, x) => n := Zero, }; let y = clone(*v); match y { MkV(n, x) => match x {}, })
  reject def MoveAfter (c0 : V) : False := (let c = c0; match c { MkV(n, x) => n := Zero, }; let y = c; match y { MkV(n, x) => match x {}, })
  reject def PassAfter (c0 : V) : Word := (let c = c0; match c { MkV(n, x) => n := Zero, }; VN(c))
  reject def RetWhole (v : &V) : &V := (match *v { MkV(n, x) => n := Zero, }; v)
  reject def RetReborrow (v : &V) : &V := (match *v { MkV(n, x) => n := Zero, }; &*v)
  reject def RetField (v : &V) : &Fin1(Zero) := (match *v { MkV(n, x) => (n := Zero; &x), })
  reject def RetIndex (v : &V) : &Word := match *v { MkV(n, x) => &n, }
  reject def ClosAfter (c0 : V) : Unit := (let c = c0; match c { MkV(n, x) => n := Zero, }; let f = (λ(u : Unit) : Word => VN(c)); ())
  reject def IdAfter (c0 : V) : Prop := (let c = c0; Id(Unit, (match c { MkV(n, x) => n := Zero, }; ()), ()))
  -- an `Eq` side's lie is discarded with its copy, unobserved: harmless
  def EqSide (c0 : V) : Prop := (let c = c0; Eq(Unit, (match c { MkV(n, x) => n := Zero, }; ()), ()))
  reject def JDirect (v : &V) : Unit := (J(Word, Zero, Zero, λ(z : Word) : Type => Unit, refl, (match *v { MkV(n, x) => n := Zero, }; ())); ())
  reject def JStuck (a : Word) (b : Word) (h : Eq(Word, a, b)) (v : &V) : Unit := (J(Word, a, b, λ(z : Word) : Type => Unit, h, (match *v { MkV(n, x) => n := Zero, }; ())); ())
  reject def StuckCallWhole (k : Word) (v : &V) : Unit := (match *v { MkV(n, x) => n := Zero, }; Stuck(k, v))
  reject def StuckCallIdx (k : Word) (v : &V) : Unit := (match *v { MkV(n, x) => n := Zero, }; StuckN(k, &(*v).0); ())
  -- a fail-safe incompleteness, pinned: a stuck call given the index field leaves a sealed
  -- program there, against which `x`'s type cannot be checked
  reject def StuckCallIdxNoLie (k : Word) (v : &V) : Unit := (StuckN(k, &(*v).0); ())
  reject def JoinLie (k : Word) (v : &V) : Unit := (match k { Zero => (match *v { MkV(n, x) => n := Zero, }; ()), Succ(m) => (), }; ())
  reject def JoinLieTail (k : Word) (v : &V) : Unit := match k { Zero => (match *v { MkV(n, x) => n := Zero, }; ()), Succ(m) => (), }
  reject def RepairOnePath (k : Word) (v : &V) : Unit := (
    match *v { MkV(n, x) => n := Zero, };
    match k { Zero => (match *v { MkV(n, x) => n := Succ(Zero), }; ()), Succ(m) => (), };
    ())
  def LenS (c0 : V) : Prop := (let c = c0; match c { MkV(n, x) => n := Zero, }; match c { MkV(n, x) => IsSucc(clone(n)), })
  reject def LenSPf (c0 : V) : LenS(c0) := (
    let c = c0;
    match c { MkV(n, x) => n := Zero, };
    match c { MkV(n, x) => match n { Zero => match x {}, Succ(m) => refl, }, })
  reject def BoomS : False := VoidF(match LenSPf(One1) {})
}

#guard (run "DirectArm" DirectArm).rejectedWith [
  ("ProjAfter", "[Match] on c.1, whose type ⌈Fin1(σ1)⌉ is not an inductive type"),
  ("MatchAfter", "[Match] on c.x, whose type ⌈Fin1(σ1)⌉ is not an inductive type"),
  ("InArm", "[Match] on c.x, whose type ⌈Fin1(σ1)⌉ is not an inductive type"),
  ("CloneAfter", "[Repack] c is read whole, but it is open"),
  ("CloneThrough", "[Repack] *v is read whole, but it is open"),
  ("MoveAfter", "[Repack] c is read whole, but it is open"),
  ("PassAfter", "[Repack] c is read whole, but it is open"),
  ("RetWhole", "[Repack] v is read whole, but it is open"),
  ("RetReborrow", "[Repack] *v is borrowed whole, but it is open"),
  ("RetField", "[Repack] a borrow of it ends, but it is open"),
  ("RetIndex", "[Repack] a borrow of it ends, but it is open"),
  ("ClosAfter", "[Repack] a closure or Π-type captures c, but it is open"),
  ("IdAfter", "[Repack] Id observes it, but it is open"),
  ("JDirect", "[Repack] a borrow of it ends, but it is open"),
  ("JStuck", "[Repack] *v is lent to a stuck match, whose arm returns with it, but it is open"),
  ("StuckCallWhole", "[Repack] v is read whole, but it is open"),
  ("StuckCallIdx", "[Repack] a borrow of it ends, but it is open"),
  ("StuckCallIdxNoLie", "[Repack] a borrow of it ends, but it is open"),
  ("JoinLie", "[Repack] *v is lent to a stuck match, whose arm returns with it, but it is open"),
  ("JoinLieTail", "[Repack] a borrow of it ends, but it is open"),
  ("RepairOnePath", "[Repack] *v is lent to a stuck match, whose arm returns with it, but it is open"),
  ("LenSPf", "[Match] on c.x, whose type ⌈Fin1(σ1)⌉ is not an inductive type"),
  ("BoomS", "unknown constant LenSPf")]

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
