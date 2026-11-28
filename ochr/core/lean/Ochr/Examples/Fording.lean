import Ochr.Test
import Ochr.Examples.Word
import Ochr.Examples.List

/-! # Fording: indexed families with Ochr's own means (D71, docs/13 option B)

Indexed families written with Ochr's own means, after three relaxations of [Ind-decl]: a
parameter whose declared type is not a sort is a *value parameter*, whose argument is an erased
position rather than a type position; a field may be an equation (a proof field); and a recursive
occurrence may take other arguments than the declared parameters (`VecF(A, m)` inside
`VecF(A, n)`). An impossible arm receives an equation that computes to `False`; at an unknown
index it stays an unsolved equation, and the arm must split the index first. Induction on a
`Prop` derivation is still refused (the decreasing parameter must be a `Type₀` inductive); a
derivation declared as data (`LeD`) is recursed on instead. -/
open Ochr.Test

ochr FordVec uses WordType {
  inductive TagN (n : Nat) := MkTagN(x : Word)
  -- value parameters
  inductive Tag (n : Word) := MkTag(x : Word)
  def t3 : Tag(Succ(Zero)) := MkTag[Succ(Zero)](Zero)
  def tn (n : Word) : Tag(n) := MkTag[n](Zero)
  -- a value parameter's argument is erased: it runs on a private copy, and its declared type need not be a sort
  def tNat (n : Nat) : Nat := (let t : TagN(n) = MkTagN[n](Zero); n)
  -- values at different value parameters have different types, though conversion ignores a constructor's recorded parameters
  reject def ParamConv : Eq(Tag(Zero), MkTag[Zero](Zero), MkTag[Succ(Zero)](Zero)) := refl
  -- closed non-uniform type arguments (the paper's old rule forbade them, the checker accepted them; both allow them now)
  inductive Nest (A : Type) := Leaf(x : A) | Deeper(d : Nest(Unit))
  def nest : Nest(Word) := Deeper[Word](Leaf[Unit](()))

  -- a Forded vector
  inductive VecF (A : Type) (n : Word) := VNil(h : Eq(Word, n, Zero)) | VCons(m : Word, x : A, xs : VecF(A, m), h : Eq(Word, n, Succ(m)))
  def v0 : VecF(Word, Zero) := VNil[Word, Zero](refl)
  def v1 : VecF(Word, Succ(Zero)) := VCons[Word, Succ(Zero)](Zero, Zero, VNil[Word, Zero](refl), refl)
  reject def vBad : VecF(Word, Succ(Zero)) := VNil[Word, Succ(Zero)](refl)

  -- case analysis: the impossible arm's equation computes to False
  def Head (A : Type) (n : Word) (v : VecF(A, Succ(n))) : A := match v { VNil(h) => match h {}, VCons(m, x, xs, h) => x }

  -- structural recursion on a Forded datatype
  def Len (A : Type) (n : Word) (v : VecF(A, n)) : Word by v := match v { VNil(h) => Zero, VCons(m, x, xs, h) => Succ(Len(A, m, xs)) }
  -- a later split of the index re-normalises an equation field's type to False ([Split] refines stored types)
  def Mixed (n : Word) (v : VecF(Word, n)) : Word := match v {
    VNil(h) => match n { Zero => Zero, Succ(p) => match h {} },
    VCons(m, x, xs, h) => x,
  }
  -- running Forded code inside a statement
  def HeadOne : Id(Word, Head(Word, Zero, VCons[Word, Succ(Zero)](Zero, Succ(Zero), VNil[Word, Zero](refl), refl)), Succ(Zero)) := refl
  def LenIdx (A : Type) (n : Word) (v : VecF(A, n)) : Eq(Word, Len(A, n, v), n) by v := match v {
    VNil(h) => rewrite h in refl,
    VCons(m, x, xs, h) => rewrite ← h in LenIdx(A, m, xs),
  }
}

ochr FordLe uses WordType {
  -- Le as a Forded inductive predicate
  inductive LeF (n : Word) (m : Word) : Prop := LeRefl(h : Eq(Word, n, m)) | LeStep(k : Word, d : LeF(n, k), e : Eq(Word, m, Succ(k)))
  def le02 : LeF(Zero, Succ(Succ(Zero))) := LeStep[Zero, Succ(Succ(Zero))](Succ(Zero), LeStep[Zero, Succ(Zero)](Zero, LeRefl[Zero, Zero](refl), refl), refl)
  reject def le10 : LeF(Succ(Zero), Zero) := LeRefl[Succ(Zero), Zero](refl)
  -- case analysis: both arms impossible
  def NotLeS0 (n : Word) (d : LeF(Succ(n), Zero)) : False := match d { LeRefl(h) => match h {}, LeStep(k, d2, e) => match e {} }
  -- induction on a proof: rejected (recursion is never on a proof)
  reject def LeZ (m : Word) (d : LeF(Zero, m)) : LeF(Zero, m) by d := match d { LeRefl(h) => LeRefl[Zero, m](h), LeStep(k, d2, e) => LeStep[Zero, m](k, LeZ(k, d2), e) }

  -- the data variant: a derivation in Type, recursed on, used only in statements
  inductive LeD (n : Word) (m : Word) := DRefl(h : Eq(Word, n, m)) | DStep(k : Word, d : LeD(n, k), e : Eq(Word, m, Succ(k)))
  def DToF (n : Word) (m : Word) (d : LeD(n, m)) : LeF(n, m) by d := match d { DRefl(h) => LeRefl[n, m](h), DStep(k, d2, e) => LeStep[n, m](k, DToF(n, k, d2), e) }
  -- transitivity by induction on the second derivation
  def DTrans (a : Word) (b : Word) (c : Word) (d1 : LeD(a, b)) (d2 : LeD(b, c)) : LeD(a, c) by d2 := match d2 {
    DRefl(h) => J(Word, b, c, λ(z : Word) : Type => LeD(a, z), h, d1),
    DStep(k, d3, e) => DStep[a, c](k, DTrans(a, b, k, d1, d3), e),
  }
}

ochr FordRel uses Lists {
  -- reflexive-transitive closure of a concrete step relation (a field calls an earlier relation)
  def StepR (x : Word) (y : Word) : Prop := Eq(Word, y, Succ(x))
  inductive Reach (x : Word) (z : Word) : Prop := RRefl(h : Eq(Word, x, z)) | RStep(y : Word, s : StepR(x, y), r : Reach(y, z))
  def r02 : Reach(Zero, Succ(Succ(Zero))) := RStep[Zero, Succ(Succ(Zero))](Succ(Zero), refl, RStep[Succ(Zero), Succ(Succ(Zero))](Succ(Succ(Zero)), refl, RRefl[Succ(Succ(Zero)), Succ(Succ(Zero))](refl)))

  -- permutation by adjacent swaps, congruence and transitivity
  inductive Perm (xs : List(Word)) (ys : List(Word)) : Prop :=
      PRefl(h : Eq(List(Word), xs, ys))
    | PSwap(a : Word, b : Word, t : List(Word), h1 : Eq(List(Word), xs, Cons[Word](a, Cons[Word](b, t))), h2 : Eq(List(Word), ys, Cons[Word](b, Cons[Word](a, t))))
    | PCons(a : Word, t1 : List(Word), t2 : List(Word), p : Perm(t1, t2), h1 : Eq(List(Word), xs, Cons[Word](a, t1)), h2 : Eq(List(Word), ys, Cons[Word](a, t2)))
    | PTrans(zs : List(Word), p1 : Perm(xs, zs), p2 : Perm(zs, ys))
  def pSw : Perm(Cons[Word](Zero, Cons[Word](Succ(Zero), Nil[Word])), Cons[Word](Succ(Zero), Cons[Word](Zero, Nil[Word]))) :=
    PSwap[Cons[Word](Zero, Cons[Word](Succ(Zero), Nil[Word])), Cons[Word](Succ(Zero), Cons[Word](Zero, Nil[Word]))](Zero, Succ(Zero), Nil[Word], refl, refl)
  -- inversion: nothing is a permutation-by-swap of the empty list's one-step rearrangement
  def NoSwapNil (ys : List(Word)) (a : Word) (b : Word) (t : List(Word)) (h1 : Eq(List(Word), Nil[Word], Cons[Word](a, Cons[Word](b, t)))) : False := match h1 {}

  -- a tiny typing judgement
  inductive Ex := ENum(n : Word) | EPair(a : Ex, b : Ex) | EFst(e : Ex)
  inductive Ty := TW | TP(a : Ty, b : Ty)
  inductive Typed (e : Ex) (T : Ty) : Prop :=
      TNum(n : Word, h1 : Eq(Ex, e, ENum(n)), h2 : Eq(Ty, T, TW))
    | TPair(a : Ex, b : Ex, A : Ty, B : Ty, da : Typed(a, A), db : Typed(b, B), h1 : Eq(Ex, e, EPair(a, b)), h2 : Eq(Ty, T, TP(A, B)))
    | TFst(e1 : Ex, B : Ty, d : Typed(e1, TP(T, B)), h : Eq(Ex, e, EFst(e1)))
  def tyFst : Typed(EFst(EPair(ENum(Zero), ENum(Zero))), TW) :=
    TFst[EFst(EPair(ENum(Zero), ENum(Zero))), TW](EPair(ENum(Zero), ENum(Zero)), TW,
      TPair[EPair(ENum(Zero), ENum(Zero)), TP(TW, TW)](ENum(Zero), ENum(Zero), TW, TW,
        TNum[ENum(Zero), TW](Zero, refl, refl), TNum[ENum(Zero), TW](Zero, refl, refl), refl, refl), refl)
  -- inversion: a numeral never has a pair type
  def NumNotPair (n : Word) (A : Ty) (B : Ty) (d : Typed(ENum(n), TP(A, B))) : False := match d {
    TNum(m, h1, h2) => match h2 {},
    TPair(a, b, A2, B2, da, db, h1, h2) => match h1 {},
    TFst(e1, B3, d2, h) => match h {},
  }
}

ochr FordAttack uses Lists {
  inductive VecF (A : Type) (n : Word) := VNil(h : Eq(Word, n, Zero)) | VCons(m : Word, x : A, xs : VecF(A, m), h : Eq(Word, n, Succ(m)))

  -- A1: the type being declared inside an equation field
  reject inductive SelfEq := MkSE(x : SelfEq, h : Eq(SelfEq, x, x))
  -- A1': ... or nested through a parameter that an equation field uses
  inductive EqF (A : Type) (a : A) (b : A) : Prop := MkEqF(h : Eq(A, a, b))
  reject inductive Loop := MkLoop(x : Loop, e : EqF(Loop, x, x))

  -- A2: a one-constructor proposition with only equation fields eliminates into data (a subsingleton)
  def UnEqF (a : Word) (b : Word) (e : EqF(Word, a, b)) : Eq(Word, a, b) := match e { MkEqF(h) => h }
  def DataFromEqF (e : EqF(Word, Zero, Zero)) : Word := match e { MkEqF(h) => Succ(Zero) }

  -- A3: writing an index field invalidates an equation field ([Open]), and [Repack] refuses the lie
  inductive VS := MkVS(n : Word, h : Eq(Word, n, Zero))
  reject def LieVS (r : &VS) : Unit := match *r { MkVS(n, h) => n := Succ(Zero) }
  reject def LieVS2 (r : &VS) : Unit := match *r { MkVS(n, h) => (n := Succ(Zero); h := refl) }
  def HonestVS (r : &VS) : Unit := match *r { MkVS(n, h) => (n := Zero; h := refl) }
  reject def LentVS (r : &VS) : Unit := match *r { MkVS(n, h) => (let p = &n; h := refl; *p := Succ(Zero)) }
  -- ... through a non-uniform recursive field as well
  inductive Grow (n : Word) := Base(h : Eq(Word, n, Zero)) | Up(m : Word, g : Grow(m), h : Eq(Word, n, Succ(m)))
  reject def LieGrow (n : Word) (g : &Grow(n)) : Unit := match *g { Base(h) => (), Up(m, g2, h) => m := Succ(m) }

  -- A4: transport along an equation field computes only at convertible endpoints
  def CastV (n : Word) (m : Word) (h : Eq(Word, n, m)) (v : VecF(Word, n)) : VecF(Word, m) := J(Word, n, m, λ(z : Word) : Type => VecF(Word, z), h, v)
  def CastRefl (v : VecF(Word, Zero)) : Prop := Id(VecF(Word, Zero), CastV(Zero, Zero, refl, clone(v)), clone(v))

  -- A5: injectivity at a Forded constructor waits for its index fields
  def InjV (m : Word) (x : Word) (y : Word) (xs : VecF(Word, m)) (ys : VecF(Word, m)) (h1 : Eq(Word, Succ(m), Succ(m))) (h2 : Eq(Word, Succ(m), Succ(m)))
    (e : Eq(VecF(Word, Succ(m)), VCons[Word, Succ(m)](m, x, xs, h1), VCons[Word, Succ(m)](m, y, ys, h2))) : Eq(Word, x, y) := match e { Intro(l, r) => l }

  -- A6: an impossible arm's equation stays stuck at an unknown index, so `match h {}` there is refused
  reject def NotEmptyGen (n : Word) (v : VecF(Word, n)) : Word := match v { VNil(h) => match h {}, VCons(m, x, xs, h) => x }

  -- A7: a stuck block over a Forded value, in a statement
  def BlockStmt (n : Word) (v : VecF(Word, n)) : Prop := Id(Word, match v { VNil(h) => Zero, VCons(m, x, xs, h) => m }, Zero)

  -- A8: a borrow as a value parameter would put a borrow inside a type and a constructor value
  reject inductive RefP (r : &Word) := MkRP(x : Word)
  -- A9: equations only over first-order data: not over functions, sorts or propositions
  reject inductive FunEq (f : Π(x : Word). Word) := MkFE(h : Eq(Π(x : Word). Word, f, f))
  reject inductive SortEq := MkSortEq(h : Eq(Type₁, Prop, Prop))
  -- A10: a one-constructor proposition with a data field beside its equation is not a subsingleton,
  -- so its witness cannot be extracted into data
  inductive ExW (n : Word) : Prop := Wit(w : Word, h : Eq(Word, n, w))
  reject def GetW (n : Word) (e : ExW(n)) : Word := match e { Wit(w, h) => w }
  def UseW (n : Word) (e : ExW(n)) : ExW(n) := match e { Wit(w, h) => Wit[n](w, h) }
  -- A11: replacing a Forded tail by one of another length: [Repack] checks the field against its
  -- telescope type at the current index (`m` is unknown, `Zero` is not convertible with it)
  reject def SwapTail (n : Word) (v : &VecF(Word, n)) : Unit := match *v { VNil(h) => (), VCons(m, x, xs, h) => xs := VNil[Word, Zero](refl) }
  def SetHead (n : Word) (v : &VecF(Word, n)) : Unit := match *v { VNil(h) => (), VCons(m, x, xs, h) => x := Zero }
  -- A12: a stale proof through a closure: `f` was formed at the old index, so after the write its
  -- result does not have the type the equation field now needs
  reject def StaleProof (r : VS) : Unit := match r { MkVS(n, h) => (let f = (λ(u : Unit) : Eq(Word, n, Zero) => h); n := Succ(Zero); h := f(())) }
  -- A13: an honest write inside one side of an `Id`, and the lying version: the side's match runs
  -- directly (D93: one constructor), and the observation ends every borrow, `*r`'s with `*r` open
  -- (D72's block, whose borrow of `*r` ended at its arm's return, caught it before)
  def IdHonest (r : &VS) : Prop := Id(Unit, match *r { MkVS(n, h) => (n := Zero; h := refl) }, ())
  reject def IdLie (r : &VS) : Prop := Id(Unit, match *r { MkVS(n, h) => n := Succ(Zero) }, ())
  -- the same lie in a match followed by more code (D72; since D93 caught where `r`'s borrow ends),
  -- and its honest twin
  reject def SeqLie (r : &VS) : Unit := (match *r { MkVS(n, h) => n := Succ(Zero) }; ())
  -- D76: the producer obligation on a closed-off `J` over Forded values. The transported term
  -- writes an index (the equation field becomes ⊥), or the length of a tail behind a
  -- non-uniform recursive field; the block's return finds the value open. The twins rewrite the
  -- equation after the index, and write a field nothing depends on.
  reject def JLieF (a : Word) (b : Word) (h : Eq(Word, a, b)) (r : &VS) : Unit := (
    match *r { MkVS(n0, h0) => J(Word, a, b, λ(z : Word) : Type => Unit, h, match *r { MkVS(n, h1) => (n := Succ(Zero); ()), }), }
  )
  def JHonestF (a : Word) (b : Word) (h : Eq(Word, a, b)) (r : &VS) : Unit := (
    match *r { MkVS(n0, h0) => J(Word, a, b, λ(z : Word) : Type => Unit, h, match *r { MkVS(n, h1) => (n := Zero; h1 := refl; ()), }), }
  )
  reject def JLieV (a : Word) (b : Word) (h : Eq(Word, a, b)) (v : &VecF(Word, Succ(Zero))) : Unit := (
    J(Word, a, b, λ(z : Word) : Type => Unit, h,
      match *v { VNil(h0) => (), VCons(m, x, xs, h1) => (m := Succ(Zero); ()), })
  )
  def JHonestV (a : Word) (b : Word) (h : Eq(Word, a, b)) (v : &VecF(Word, Succ(Zero))) : Unit := (
    J(Word, a, b, λ(z : Word) : Type => Unit, h,
      match *v { VNil(h0) => (), VCons(m, x, xs, h1) => (x := Zero; ()), })
  )
  def SeqHonest (r : &VS) : Unit := (match *r { MkVS(n, h) => (n := Zero; h := refl) }; ())
  -- A14: an impossible arm eliminated at an unknown index inside a statement's stuck block
  reject def BlockElim (n : Word) (v : VecF(Word, n)) : Prop := Id(Word, match v { VNil(h) => match h {}, VCons(m, x, xs, h) => x }, Zero)
  -- A15: a non-uniform recursive field reassigned at its own index is fine; at another index it is a lie
  def KeepGrow (n : Word) (g : &Grow(n)) : Unit := match *g { Base(h) => (), Up(m, g2, h) => g2 := clone(g2) }
  -- A16: a value parameter whose declared type merely computes to a sort cannot type a field ([Type-pos], D55)
  def U (n : Word) : Type₁ := match n { Zero => Type, Succ(p) => Type }
  reject inductive Sneak (T : U(Zero)) := MkSneak(x : T)

  -- Not a Fording gap, but found by these attacks (D71): a length lie in an arm of a match
  -- followed by more code was accepted, because the match is closed off as a stuck block and
  -- its arms were not checked at a whole-again point. Closed by D72 (`IdLie`, `SeqLie` above;
  -- DepFields' `StuckBlocks` for plain dependent fields).
}

-- each rejection for its reason
#guard (run "FordVec" FordVec).rejectedWith [
  ("ParamConv", "the right side of Eq has type Tag(Succ(Zero)), expected Tag(Zero)"),
  ("vBad", "field h of VNil has type ⊤, expected False")]
#guard (run "FordLe" FordLe).rejectedWith [
  ("le10", "field h of LeRefl has type ⊤, expected False"),
  ("LeZ", "`by d`: the decreasing parameter must have an inductive type (or be a borrow of one)")]
#guard (run "FordAttack" FordAttack).rejectedWith [
  ("SelfEq", "field h of MkSE : Eq(SelfEq, x, x): fields are first-order data (inductive types, Nat, Unit, ×, earlier type functions) or parameters, D36"),
  ("Loop", "field e of MkLoop : EqF(Loop, x, x): Loop occurs at the parameter A of EqF, which is not nestable in EqF"),
  ("LieVS", "[Repack] a borrow of it ends, but it is open: field h of MkVS: it holds ⊥ (moved out, or a proof invalidated by a write to a field its type mentions)"),
  ("LieVS2", "the assigned value has type ⊤, expected False"),
  ("LentVS", "the proof assigned to h (while part of its value is lent, what the borrow holds unknown: [Open]) has type ⊤, expected Eq(Word, σ2, Zero)"),
  ("LieGrow", "[Repack] a borrow of it ends, but it is open: field g of Up holds a value of type Grow(σ2), but its type from the earlier fields is Grow(Succ(σ2))"),
  ("NotEmptyGen", "[Match] on v.h, whose type Eq(Word, σ0, Zero) is not an inductive type"),
  ("RefP", "RefP: the parameter r has the borrow type &Word: no borrows inside data or types"),
  ("FunEq", "field h of MkFE : Eq(Π(x : Word). Word, f, f): fields are first-order data (inductive types, Nat, Unit, ×, earlier type functions) or parameters, D36"),
  ("SortEq", "field h of MkSortEq : Eq(Type₁, Prop, Prop): fields are first-order data (inductive types, Nat, Unit, ×, earlier type functions) or parameters, D36"),
  ("GetW", "[D45] a match on a proof of ExW returns a non-proof, but ExW is not a subsingleton (its constructor has a field that is not a proposition): large elimination would tell apart proofs that proof irrelevance identifies"),
  ("StaleProof", "the assigned value has type Eq(Word, σ1, Zero), expected False"),
  ("SwapTail", "[Repack] a borrow of it ends, but it is open: field xs of VCons holds a value of type VecF(Word, Zero), but its type from the earlier fields is VecF(Word, σ2)"),
  ("BlockElim", "[Match] on v.h, whose type Eq(Word, σ0, Zero) is not an inductive type"),
  ("Sneak", "[D55] T is written where a type is expected, but its declared type is not a sort (it is a type only by computation)"),
  ("IdLie", "[Repack] a borrow of it ends, but it is open: field h of MkVS: it holds ⊥"),
  ("SeqLie", "[Repack] a borrow of it ends, but it is open: field h of MkVS: it holds ⊥"),
  ("JLieF", "[Repack] *r is lent to a stuck match, whose arm returns with it, but it is open: field h of MkVS: it holds ⊥"),
  ("JLieV", "[Repack] *v is lent to a stuck match, whose arm returns with it, but it is open: field xs of VCons")]

/-! ## A type parameter is written as a sort (D128)

A parameter is a type parameter when its declared type is written as a sort (`paramIsType`, D71):
an argument at it stands in a type position, and the type being declared may nest there (D107).
A field's type is typed by what the parameter's declared type reads as (D55), so the two tests
disagreed on a parameter whose declared type reads as a sort without being written as one:
`TL`'s `B : (let z = A; Type)` was a type for its field and a value for nesting, and a field type
read a value parameter that varies, which the data model's proof rules out. Since D128 such a
parameter is rejected, with the sort to write. Each spelling that reads as a sort (a `let`, a `;`,
a `let` naming the sort, a match whose arms all return it), at each sort, with a field reading the
parameter (`…F`) and with none (`…N`), sits beside its twin written as the sort (`…W`), whose
verdict is unchanged. The spellings that read as a value (an ascription, a call, a constant, a
type function, an earlier parameter, a match whose arms disagree) are value parameters, as before:
accepted, and rejected by D55 as a field's type. Generated by `ochr/core/probes/written-sorts/gen.py`. -/
ochr WrittenSorts uses Lists {
  -- the proof lane's counterexample (`FactsCE.dTL`), and the same parameter nested in a list
  reject inductive TL (A : Type) (B : (let z = A; Type)) := MkTL(x : B)
  inductive TLW (A : Type) (B : Type) := MkTLW(x : B)
  reject inductive TLL (A : Type) (B : (let z = A; Type)) := MkTLL(x : List(B))
  inductive TLLW (A : Type) (B : Type) := MkTLLW(x : List(B))
  -- reads as Prop: rejected, beside the same declaration with B written as Prop
  reject inductive LetpF (A : Type) (B : (let z = A; Prop)) := MkLetpF(x : B)
  inductive LetpFW (A : Type) (B : Prop) := MkLetpFW(x : B)
  reject inductive LetpN (A : Type) (B : (let z = A; Prop)) := MkLetpN
  inductive LetpNW (A : Type) (B : Prop) := MkLetpNW
  reject inductive Let0pF (B : (let z = 0; Prop)) := MkLet0pF(x : B)
  inductive Let0pFW (B : Prop) := MkLet0pFW(x : B)
  reject inductive Let0pN (B : (let z = 0; Prop)) := MkLet0pN
  inductive Let0pNW (B : Prop) := MkLet0pNW
  reject inductive LetNpF (A : Type) (B : (let z = A; let w = z; Prop)) := MkLetNpF(x : B)
  inductive LetNpFW (A : Type) (B : Prop) := MkLetNpFW(x : B)
  reject inductive LetNpN (A : Type) (B : (let z = A; let w = z; Prop)) := MkLetNpN
  inductive LetNpNW (A : Type) (B : Prop) := MkLetNpNW
  reject inductive SeqpF (B : ((); Prop)) := MkSeqpF(x : B)
  inductive SeqpFW (B : Prop) := MkSeqpFW(x : B)
  reject inductive SeqpN (B : ((); Prop)) := MkSeqpN
  inductive SeqpNW (B : Prop) := MkSeqpNW
  reject inductive SeqApF (A : Type) (B : (A; Prop)) := MkSeqApF(x : B)
  inductive SeqApFW (A : Type) (B : Prop) := MkSeqApFW(x : B)
  reject inductive SeqApN (A : Type) (B : (A; Prop)) := MkSeqApN
  inductive SeqApNW (A : Type) (B : Prop) := MkSeqApNW
  reject inductive LetSpF (B : (let T = Prop; T)) := MkLetSpF(x : B)
  inductive LetSpFW (B : Prop) := MkLetSpFW(x : B)
  reject inductive LetSpN (B : (let T = Prop; T)) := MkLetSpN
  inductive LetSpNW (B : Prop) := MkLetSpNW
  reject inductive LetSApF (A : Type) (B : (let T = Prop; let z = A; T)) := MkLetSApF(x : B)
  inductive LetSApFW (A : Type) (B : Prop) := MkLetSApFW(x : B)
  reject inductive LetSApN (A : Type) (B : (let T = Prop; let z = A; T)) := MkLetSApN
  inductive LetSApNW (A : Type) (B : Prop) := MkLetSApNW
  reject inductive MatchLpF (B : match 0 { Z => Prop, S(m) => Prop }) := MkMatchLpF(x : B)
  inductive MatchLpFW (B : Prop) := MkMatchLpFW(x : B)
  reject inductive MatchLpN (B : match 0 { Z => Prop, S(m) => Prop }) := MkMatchLpN
  inductive MatchLpNW (B : Prop) := MkMatchLpNW
  reject inductive MatchNpF (n : Nat) (B : match n { Z => Prop, S(m) => Prop }) := MkMatchNpF(x : B)
  inductive MatchNpFW (n : Nat) (B : Prop) := MkMatchNpFW(x : B)
  reject inductive MatchNpN (n : Nat) (B : match n { Z => Prop, S(m) => Prop }) := MkMatchNpN
  inductive MatchNpNW (n : Nat) (B : Prop) := MkMatchNpNW
  reject inductive MatchWpF (w : Word) (B : match w { Zero => Prop, Succ(v) => Prop }) := MkMatchWpF(x : B)
  inductive MatchWpFW (w : Word) (B : Prop) := MkMatchWpFW(x : B)
  reject inductive MatchWpN (w : Word) (B : match w { Zero => Prop, Succ(v) => Prop }) := MkMatchWpN
  inductive MatchWpNW (w : Word) (B : Prop) := MkMatchWpNW
  reject inductive LetMpF (n : Nat) (B : (let z = n; match z { Z => Prop, S(m) => Prop })) := MkLetMpF(x : B)
  inductive LetMpFW (n : Nat) (B : Prop) := MkLetMpFW(x : B)
  reject inductive LetMpN (n : Nat) (B : (let z = n; match z { Z => Prop, S(m) => Prop })) := MkLetMpN
  inductive LetMpNW (n : Nat) (B : Prop) := MkLetMpNW
  reject inductive MatchLetpF (n : Nat) (B : match n { Z => (let w = n; Prop), S(m) => Prop }) := MkMatchLetpF(x : B)
  inductive MatchLetpFW (n : Nat) (B : Prop) := MkMatchLetpFW(x : B)
  reject inductive MatchLetpN (n : Nat) (B : match n { Z => (let w = n; Prop), S(m) => Prop }) := MkMatchLetpN
  inductive MatchLetpNW (n : Nat) (B : Prop) := MkMatchLetpNW
  reject inductive LetMatchSpF (n : Nat) (B : (let T = Prop; match n { Z => T, S(m) => T })) := MkLetMatchSpF(x : B)
  inductive LetMatchSpFW (n : Nat) (B : Prop) := MkLetMatchSpFW(x : B)
  reject inductive LetMatchSpN (n : Nat) (B : (let T = Prop; match n { Z => T, S(m) => T })) := MkLetMatchSpN
  inductive LetMatchSpNW (n : Nat) (B : Prop) := MkLetMatchSpNW
  -- reads as a value of Type₁, not as a sort: a value parameter, as before (no field may have it as its type)
  reject inductive AscpF (B : (Prop : Type₁)) := MkAscpF(x : B)
  inductive AscpN (B : (Prop : Type₁)) := MkAscpN
  def WSFp (u : Unit) : Type₁ := Prop
  reject inductive CallpF (B : WSFp(())) := MkCallpF(x : B)
  inductive CallpN (B : WSFp(())) := MkCallpN
  def WSCp : Type₁ := Prop
  reject inductive ConstpF (B : WSCp) := MkConstpF(x : B)
  inductive ConstpN (B : WSCp) := MkConstpN
  def WSIp (X : Type₁) : Type₁ := X
  reject inductive IdFnpF (B : WSIp(Prop)) := MkIdFnpF(x : B)
  inductive IdFnpN (B : WSIp(Prop)) := MkIdFnpN
  reject inductive ParampF (U : Type₁) (B : U) := MkParampF(x : B)
  inductive ParampN (U : Type₁) (B : U) := MkParampN
  -- reads as Type: rejected, beside the same declaration with B written as Type
  reject inductive LettF (A : Type) (B : (let z = A; Type)) := MkLettF(x : B)
  inductive LettFW (A : Type) (B : Type) := MkLettFW(x : B)
  reject inductive LettN (A : Type) (B : (let z = A; Type)) := MkLettN
  inductive LettNW (A : Type) (B : Type) := MkLettNW
  reject inductive Let0tF (B : (let z = 0; Type)) := MkLet0tF(x : B)
  inductive Let0tFW (B : Type) := MkLet0tFW(x : B)
  reject inductive Let0tN (B : (let z = 0; Type)) := MkLet0tN
  inductive Let0tNW (B : Type) := MkLet0tNW
  reject inductive LetNtF (A : Type) (B : (let z = A; let w = z; Type)) := MkLetNtF(x : B)
  inductive LetNtFW (A : Type) (B : Type) := MkLetNtFW(x : B)
  reject inductive LetNtN (A : Type) (B : (let z = A; let w = z; Type)) := MkLetNtN
  inductive LetNtNW (A : Type) (B : Type) := MkLetNtNW
  reject inductive SeqtF (B : ((); Type)) := MkSeqtF(x : B)
  inductive SeqtFW (B : Type) := MkSeqtFW(x : B)
  reject inductive SeqtN (B : ((); Type)) := MkSeqtN
  inductive SeqtNW (B : Type) := MkSeqtNW
  reject inductive SeqAtF (A : Type) (B : (A; Type)) := MkSeqAtF(x : B)
  inductive SeqAtFW (A : Type) (B : Type) := MkSeqAtFW(x : B)
  reject inductive SeqAtN (A : Type) (B : (A; Type)) := MkSeqAtN
  inductive SeqAtNW (A : Type) (B : Type) := MkSeqAtNW
  reject inductive LetStF (B : (let T = Type; T)) := MkLetStF(x : B)
  inductive LetStFW (B : Type) := MkLetStFW(x : B)
  reject inductive LetStN (B : (let T = Type; T)) := MkLetStN
  inductive LetStNW (B : Type) := MkLetStNW
  reject inductive LetSAtF (A : Type) (B : (let T = Type; let z = A; T)) := MkLetSAtF(x : B)
  inductive LetSAtFW (A : Type) (B : Type) := MkLetSAtFW(x : B)
  reject inductive LetSAtN (A : Type) (B : (let T = Type; let z = A; T)) := MkLetSAtN
  inductive LetSAtNW (A : Type) (B : Type) := MkLetSAtNW
  reject inductive MatchLtF (B : match 0 { Z => Type, S(m) => Type }) := MkMatchLtF(x : B)
  inductive MatchLtFW (B : Type) := MkMatchLtFW(x : B)
  reject inductive MatchLtN (B : match 0 { Z => Type, S(m) => Type }) := MkMatchLtN
  inductive MatchLtNW (B : Type) := MkMatchLtNW
  reject inductive MatchNtF (n : Nat) (B : match n { Z => Type, S(m) => Type }) := MkMatchNtF(x : B)
  inductive MatchNtFW (n : Nat) (B : Type) := MkMatchNtFW(x : B)
  reject inductive MatchNtN (n : Nat) (B : match n { Z => Type, S(m) => Type }) := MkMatchNtN
  inductive MatchNtNW (n : Nat) (B : Type) := MkMatchNtNW
  reject inductive MatchWtF (w : Word) (B : match w { Zero => Type, Succ(v) => Type }) := MkMatchWtF(x : B)
  inductive MatchWtFW (w : Word) (B : Type) := MkMatchWtFW(x : B)
  reject inductive MatchWtN (w : Word) (B : match w { Zero => Type, Succ(v) => Type }) := MkMatchWtN
  inductive MatchWtNW (w : Word) (B : Type) := MkMatchWtNW
  reject inductive LetMtF (n : Nat) (B : (let z = n; match z { Z => Type, S(m) => Type })) := MkLetMtF(x : B)
  inductive LetMtFW (n : Nat) (B : Type) := MkLetMtFW(x : B)
  reject inductive LetMtN (n : Nat) (B : (let z = n; match z { Z => Type, S(m) => Type })) := MkLetMtN
  inductive LetMtNW (n : Nat) (B : Type) := MkLetMtNW
  reject inductive MatchLettF (n : Nat) (B : match n { Z => (let w = n; Type), S(m) => Type }) := MkMatchLettF(x : B)
  inductive MatchLettFW (n : Nat) (B : Type) := MkMatchLettFW(x : B)
  reject inductive MatchLettN (n : Nat) (B : match n { Z => (let w = n; Type), S(m) => Type }) := MkMatchLettN
  inductive MatchLettNW (n : Nat) (B : Type) := MkMatchLettNW
  reject inductive LetMatchStF (n : Nat) (B : (let T = Type; match n { Z => T, S(m) => T })) := MkLetMatchStF(x : B)
  inductive LetMatchStFW (n : Nat) (B : Type) := MkLetMatchStFW(x : B)
  reject inductive LetMatchStN (n : Nat) (B : (let T = Type; match n { Z => T, S(m) => T })) := MkLetMatchStN
  inductive LetMatchStNW (n : Nat) (B : Type) := MkLetMatchStNW
  -- reads as a value of Type₁, not as a sort: a value parameter, as before (no field may have it as its type)
  reject inductive AsctF (B : (Type : Type₁)) := MkAsctF(x : B)
  inductive AsctN (B : (Type : Type₁)) := MkAsctN
  def WSFt (u : Unit) : Type₁ := Type
  reject inductive CalltF (B : WSFt(())) := MkCalltF(x : B)
  inductive CalltN (B : WSFt(())) := MkCalltN
  def WSCt : Type₁ := Type
  reject inductive ConsttF (B : WSCt) := MkConsttF(x : B)
  inductive ConsttN (B : WSCt) := MkConsttN
  def WSIt (X : Type₁) : Type₁ := X
  reject inductive IdFntF (B : WSIt(Type)) := MkIdFntF(x : B)
  inductive IdFntN (B : WSIt(Type)) := MkIdFntN
  reject inductive ParamtF (U : Type₁) (B : U) := MkParamtF(x : B)
  inductive ParamtN (U : Type₁) (B : U) := MkParamtN
  -- reads as Type₁: rejected, beside the same declaration with B written as Type₁
  reject inductive LetuF (A : Type) (B : (let z = A; Type₁)) := MkLetuF(x : B)
  reject inductive LetuFW (A : Type) (B : Type₁) := MkLetuFW(x : B)
  reject inductive LetuN (A : Type) (B : (let z = A; Type₁)) := MkLetuN
  inductive LetuNW (A : Type) (B : Type₁) := MkLetuNW
  reject inductive Let0uF (B : (let z = 0; Type₁)) := MkLet0uF(x : B)
  reject inductive Let0uFW (B : Type₁) := MkLet0uFW(x : B)
  reject inductive Let0uN (B : (let z = 0; Type₁)) := MkLet0uN
  inductive Let0uNW (B : Type₁) := MkLet0uNW
  reject inductive LetNuF (A : Type) (B : (let z = A; let w = z; Type₁)) := MkLetNuF(x : B)
  reject inductive LetNuFW (A : Type) (B : Type₁) := MkLetNuFW(x : B)
  reject inductive LetNuN (A : Type) (B : (let z = A; let w = z; Type₁)) := MkLetNuN
  inductive LetNuNW (A : Type) (B : Type₁) := MkLetNuNW
  reject inductive SequF (B : ((); Type₁)) := MkSequF(x : B)
  reject inductive SequFW (B : Type₁) := MkSequFW(x : B)
  reject inductive SequN (B : ((); Type₁)) := MkSequN
  inductive SequNW (B : Type₁) := MkSequNW
  reject inductive SeqAuF (A : Type) (B : (A; Type₁)) := MkSeqAuF(x : B)
  reject inductive SeqAuFW (A : Type) (B : Type₁) := MkSeqAuFW(x : B)
  reject inductive SeqAuN (A : Type) (B : (A; Type₁)) := MkSeqAuN
  inductive SeqAuNW (A : Type) (B : Type₁) := MkSeqAuNW
  reject inductive LetSuF (B : (let T = Type₁; T)) := MkLetSuF(x : B)
  reject inductive LetSuFW (B : Type₁) := MkLetSuFW(x : B)
  reject inductive LetSuN (B : (let T = Type₁; T)) := MkLetSuN
  inductive LetSuNW (B : Type₁) := MkLetSuNW
  reject inductive LetSAuF (A : Type) (B : (let T = Type₁; let z = A; T)) := MkLetSAuF(x : B)
  reject inductive LetSAuFW (A : Type) (B : Type₁) := MkLetSAuFW(x : B)
  reject inductive LetSAuN (A : Type) (B : (let T = Type₁; let z = A; T)) := MkLetSAuN
  inductive LetSAuNW (A : Type) (B : Type₁) := MkLetSAuNW
  reject inductive MatchLuF (B : match 0 { Z => Type₁, S(m) => Type₁ }) := MkMatchLuF(x : B)
  reject inductive MatchLuFW (B : Type₁) := MkMatchLuFW(x : B)
  reject inductive MatchLuN (B : match 0 { Z => Type₁, S(m) => Type₁ }) := MkMatchLuN
  inductive MatchLuNW (B : Type₁) := MkMatchLuNW
  reject inductive MatchNuF (n : Nat) (B : match n { Z => Type₁, S(m) => Type₁ }) := MkMatchNuF(x : B)
  reject inductive MatchNuFW (n : Nat) (B : Type₁) := MkMatchNuFW(x : B)
  reject inductive MatchNuN (n : Nat) (B : match n { Z => Type₁, S(m) => Type₁ }) := MkMatchNuN
  inductive MatchNuNW (n : Nat) (B : Type₁) := MkMatchNuNW
  reject inductive MatchWuF (w : Word) (B : match w { Zero => Type₁, Succ(v) => Type₁ }) := MkMatchWuF(x : B)
  reject inductive MatchWuFW (w : Word) (B : Type₁) := MkMatchWuFW(x : B)
  reject inductive MatchWuN (w : Word) (B : match w { Zero => Type₁, Succ(v) => Type₁ }) := MkMatchWuN
  inductive MatchWuNW (w : Word) (B : Type₁) := MkMatchWuNW
  reject inductive LetMuF (n : Nat) (B : (let z = n; match z { Z => Type₁, S(m) => Type₁ })) := MkLetMuF(x : B)
  reject inductive LetMuFW (n : Nat) (B : Type₁) := MkLetMuFW(x : B)
  reject inductive LetMuN (n : Nat) (B : (let z = n; match z { Z => Type₁, S(m) => Type₁ })) := MkLetMuN
  inductive LetMuNW (n : Nat) (B : Type₁) := MkLetMuNW
  reject inductive MatchLetuF (n : Nat) (B : match n { Z => (let w = n; Type₁), S(m) => Type₁ }) := MkMatchLetuF(x : B)
  reject inductive MatchLetuFW (n : Nat) (B : Type₁) := MkMatchLetuFW(x : B)
  reject inductive MatchLetuN (n : Nat) (B : match n { Z => (let w = n; Type₁), S(m) => Type₁ }) := MkMatchLetuN
  inductive MatchLetuNW (n : Nat) (B : Type₁) := MkMatchLetuNW
  reject inductive LetMatchSuF (n : Nat) (B : (let T = Type₁; match n { Z => T, S(m) => T })) := MkLetMatchSuF(x : B)
  reject inductive LetMatchSuFW (n : Nat) (B : Type₁) := MkLetMatchSuFW(x : B)
  reject inductive LetMatchSuN (n : Nat) (B : (let T = Type₁; match n { Z => T, S(m) => T })) := MkLetMatchSuN
  inductive LetMatchSuNW (n : Nat) (B : Type₁) := MkLetMatchSuNW
  -- reads as a value of Type₂, not as a sort: a value parameter, as before (no field may have it as its type)
  reject inductive AscuF (B : (Type₁ : Type₂)) := MkAscuF(x : B)
  inductive AscuN (B : (Type₁ : Type₂)) := MkAscuN
  def WSFu (u : Unit) : Type₂ := Type₁
  reject inductive CalluF (B : WSFu(())) := MkCalluF(x : B)
  inductive CalluN (B : WSFu(())) := MkCalluN
  def WSCu : Type₂ := Type₁
  reject inductive ConstuF (B : WSCu) := MkConstuF(x : B)
  inductive ConstuN (B : WSCu) := MkConstuN
  def WSIu (X : Type₂) : Type₂ := X
  reject inductive IdFnuF (B : WSIu(Type₁)) := MkIdFnuF(x : B)
  inductive IdFnuN (B : WSIu(Type₁)) := MkIdFnuN
  reject inductive ParamuF (U : Type₂) (B : U) := MkParamuF(x : B)
  inductive ParamuN (U : Type₂) (B : U) := MkParamuN
  -- arms that disagree (Type, Prop) read as neither: a value parameter
  reject inductive MatchMixF (n : Nat) (B : match n { Z => Type, S(m) => Prop }) := MkMatchMixF(x : B)
  inductive MatchMixN (n : Nat) (B : match n { Z => Type, S(m) => Prop }) := MkMatchMixN
}

#guard (run "WrittenSorts" WrittenSorts).rejectedWith [
  ("TL", "[D128] the parameter B of TL is declared at "),
  ("TLL", "[D128] the parameter B of TLL is declared at "),
  ("LetpF", "[D128] the parameter B of LetpF is declared at "),
  ("LetpN", "[D128] the parameter B of LetpN is declared at "),
  ("Let0pF", "[D128] the parameter B of Let0pF is declared at "),
  ("Let0pN", "[D128] the parameter B of Let0pN is declared at "),
  ("LetNpF", "[D128] the parameter B of LetNpF is declared at "),
  ("LetNpN", "[D128] the parameter B of LetNpN is declared at "),
  ("SeqpF", "[D128] the parameter B of SeqpF is declared at "),
  ("SeqpN", "[D128] the parameter B of SeqpN is declared at "),
  ("SeqApF", "[D128] the parameter B of SeqApF is declared at "),
  ("SeqApN", "[D128] the parameter B of SeqApN is declared at "),
  ("LetSpF", "[D128] the parameter B of LetSpF is declared at "),
  ("LetSpN", "[D128] the parameter B of LetSpN is declared at "),
  ("LetSApF", "[D128] the parameter B of LetSApF is declared at "),
  ("LetSApN", "[D128] the parameter B of LetSApN is declared at "),
  ("MatchLpF", "[D128] the parameter B of MatchLpF is declared at "),
  ("MatchLpN", "[D128] the parameter B of MatchLpN is declared at "),
  ("MatchNpF", "[D128] the parameter B of MatchNpF is declared at "),
  ("MatchNpN", "[D128] the parameter B of MatchNpN is declared at "),
  ("MatchWpF", "[D128] the parameter B of MatchWpF is declared at "),
  ("MatchWpN", "[D128] the parameter B of MatchWpN is declared at "),
  ("LetMpF", "[D128] the parameter B of LetMpF is declared at "),
  ("LetMpN", "[D128] the parameter B of LetMpN is declared at "),
  ("MatchLetpF", "[D128] the parameter B of MatchLetpF is declared at "),
  ("MatchLetpN", "[D128] the parameter B of MatchLetpN is declared at "),
  ("LetMatchSpF", "[D128] the parameter B of LetMatchSpF is declared at "),
  ("LetMatchSpN", "[D128] the parameter B of LetMatchSpN is declared at "),
  ("AscpF", "[D55] B is written where a type is expected, but its declared type is not a sort"),
  ("CallpF", "[D55] B is written where a type is expected, but its declared type is not a sort"),
  ("ConstpF", "[D55] B is written where a type is expected, but its declared type is not a sort"),
  ("IdFnpF", "[D55] B is written where a type is expected, but its declared type is not a sort"),
  ("ParampF", "[D55] B is written where a type is expected, but its declared type is not a sort"),
  ("LettF", "[D128] the parameter B of LettF is declared at "),
  ("LettN", "[D128] the parameter B of LettN is declared at "),
  ("Let0tF", "[D128] the parameter B of Let0tF is declared at "),
  ("Let0tN", "[D128] the parameter B of Let0tN is declared at "),
  ("LetNtF", "[D128] the parameter B of LetNtF is declared at "),
  ("LetNtN", "[D128] the parameter B of LetNtN is declared at "),
  ("SeqtF", "[D128] the parameter B of SeqtF is declared at "),
  ("SeqtN", "[D128] the parameter B of SeqtN is declared at "),
  ("SeqAtF", "[D128] the parameter B of SeqAtF is declared at "),
  ("SeqAtN", "[D128] the parameter B of SeqAtN is declared at "),
  ("LetStF", "[D128] the parameter B of LetStF is declared at "),
  ("LetStN", "[D128] the parameter B of LetStN is declared at "),
  ("LetSAtF", "[D128] the parameter B of LetSAtF is declared at "),
  ("LetSAtN", "[D128] the parameter B of LetSAtN is declared at "),
  ("MatchLtF", "[D128] the parameter B of MatchLtF is declared at "),
  ("MatchLtN", "[D128] the parameter B of MatchLtN is declared at "),
  ("MatchNtF", "[D128] the parameter B of MatchNtF is declared at "),
  ("MatchNtN", "[D128] the parameter B of MatchNtN is declared at "),
  ("MatchWtF", "[D128] the parameter B of MatchWtF is declared at "),
  ("MatchWtN", "[D128] the parameter B of MatchWtN is declared at "),
  ("LetMtF", "[D128] the parameter B of LetMtF is declared at "),
  ("LetMtN", "[D128] the parameter B of LetMtN is declared at "),
  ("MatchLettF", "[D128] the parameter B of MatchLettF is declared at "),
  ("MatchLettN", "[D128] the parameter B of MatchLettN is declared at "),
  ("LetMatchStF", "[D128] the parameter B of LetMatchStF is declared at "),
  ("LetMatchStN", "[D128] the parameter B of LetMatchStN is declared at "),
  ("AsctF", "[D55] B is written where a type is expected, but its declared type is not a sort"),
  ("CalltF", "[D55] B is written where a type is expected, but its declared type is not a sort"),
  ("ConsttF", "[D55] B is written where a type is expected, but its declared type is not a sort"),
  ("IdFntF", "[D55] B is written where a type is expected, but its declared type is not a sort"),
  ("ParamtF", "[D55] B is written where a type is expected, but its declared type is not a sort"),
  ("LetuF", "[D128] the parameter B of LetuF is declared at "),
  ("LetuFW", "[D140] field x of MkLetuFW: its type is the parameter B, declared at Type₁: a parameter heading a field's type is written Prop or Type"),
  ("LetuN", "[D128] the parameter B of LetuN is declared at "),
  ("Let0uF", "[D128] the parameter B of Let0uF is declared at "),
  ("Let0uFW", "[D140] field x of MkLet0uFW: its type is the parameter B, declared at Type₁: a parameter heading a field's type is written Prop or Type"),
  ("Let0uN", "[D128] the parameter B of Let0uN is declared at "),
  ("LetNuF", "[D128] the parameter B of LetNuF is declared at "),
  ("LetNuFW", "[D140] field x of MkLetNuFW: its type is the parameter B, declared at Type₁: a parameter heading a field's type is written Prop or Type"),
  ("LetNuN", "[D128] the parameter B of LetNuN is declared at "),
  ("SequF", "[D128] the parameter B of SequF is declared at "),
  ("SequFW", "[D140] field x of MkSequFW: its type is the parameter B, declared at Type₁: a parameter heading a field's type is written Prop or Type"),
  ("SequN", "[D128] the parameter B of SequN is declared at "),
  ("SeqAuF", "[D128] the parameter B of SeqAuF is declared at "),
  ("SeqAuFW", "[D140] field x of MkSeqAuFW: its type is the parameter B, declared at Type₁: a parameter heading a field's type is written Prop or Type"),
  ("SeqAuN", "[D128] the parameter B of SeqAuN is declared at "),
  ("LetSuF", "[D128] the parameter B of LetSuF is declared at "),
  ("LetSuFW", "[D140] field x of MkLetSuFW: its type is the parameter B, declared at Type₁: a parameter heading a field's type is written Prop or Type"),
  ("LetSuN", "[D128] the parameter B of LetSuN is declared at "),
  ("LetSAuF", "[D128] the parameter B of LetSAuF is declared at "),
  ("LetSAuFW", "[D140] field x of MkLetSAuFW: its type is the parameter B, declared at Type₁: a parameter heading a field's type is written Prop or Type"),
  ("LetSAuN", "[D128] the parameter B of LetSAuN is declared at "),
  ("MatchLuF", "[D128] the parameter B of MatchLuF is declared at "),
  ("MatchLuFW", "[D140] field x of MkMatchLuFW: its type is the parameter B, declared at Type₁: a parameter heading a field's type is written Prop or Type"),
  ("MatchLuN", "[D128] the parameter B of MatchLuN is declared at "),
  ("MatchNuF", "[D128] the parameter B of MatchNuF is declared at "),
  ("MatchNuFW", "[D140] field x of MkMatchNuFW: its type is the parameter B, declared at Type₁: a parameter heading a field's type is written Prop or Type"),
  ("MatchNuN", "[D128] the parameter B of MatchNuN is declared at "),
  ("MatchWuF", "[D128] the parameter B of MatchWuF is declared at "),
  ("MatchWuFW", "[D140] field x of MkMatchWuFW: its type is the parameter B, declared at Type₁: a parameter heading a field's type is written Prop or Type"),
  ("MatchWuN", "[D128] the parameter B of MatchWuN is declared at "),
  ("LetMuF", "[D128] the parameter B of LetMuF is declared at "),
  ("LetMuFW", "[D140] field x of MkLetMuFW: its type is the parameter B, declared at Type₁: a parameter heading a field's type is written Prop or Type"),
  ("LetMuN", "[D128] the parameter B of LetMuN is declared at "),
  ("MatchLetuF", "[D128] the parameter B of MatchLetuF is declared at "),
  ("MatchLetuFW", "[D140] field x of MkMatchLetuFW: its type is the parameter B, declared at Type₁: a parameter heading a field's type is written Prop or Type"),
  ("MatchLetuN", "[D128] the parameter B of MatchLetuN is declared at "),
  ("LetMatchSuF", "[D128] the parameter B of LetMatchSuF is declared at "),
  ("LetMatchSuFW", "[D140] field x of MkLetMatchSuFW: its type is the parameter B, declared at Type₁: a parameter heading a field's type is written Prop or Type"),
  ("LetMatchSuN", "[D128] the parameter B of LetMatchSuN is declared at "),
  ("AscuF", "[D55] B is written where a type is expected, but its declared type is not a sort"),
  ("CalluF", "[D55] B is written where a type is expected, but its declared type is not a sort"),
  ("ConstuF", "[D55] B is written where a type is expected, but its declared type is not a sort"),
  ("IdFnuF", "[D55] B is written where a type is expected, but its declared type is not a sort"),
  ("ParamuF", "[D55] B is written where a type is expected, but its declared type is not a sort"),
  ("MatchMixF", "[D55] B is written where a type is expected, but its declared type is not a sort")]

/-! ## The head of a field's type has a small result, read from what is written (D140)

A field's type headed by a parameter (the field's whole type is `B`) or by a call of a global (the
field's whole type is `G(ā)`) is checked from what is written, before anything runs: the parameter
is written `Prop` or `Type`, and the global is declared with the codomain `Prop` or `Type` written.
The consistency proof's model of the data types rests on that fact (`FieldHeads`); before D140 it
could be read only off a run (the level check at the generic telescope, `sortOf`). Every program it
rejects was rejected before: a parameter written `Type₁` or `Type₂`, or a call of a global into
`Type₁`, by the level check or as computing to a sort; a parameter written as a hole or a match
with no arms by its evaluation; a global whose codomain is `let z = 0; Type` or `(); Type` by an
internal error (the pre-pass read its call as erased, the run did not). Each rewrites to the
spelling it names: `Type` or `Prop` written. A head whose declared type does not read as a sort
keeps D55's message, one that reads as a sort through a `let`, a `;` or a match D128's, and one
nested in an inductive's argument (`HBox(B)`) is typed there, as before. -/

ochr FieldHeads {
  inductive HBox (A : Type) := MkHBox(x : A)
  def HTT : Type₁ := Type
  def HIdT (X : Type₁) : Type₁ := X
  -- a parameter heading a field's type
  inductive PType (B : Type) := MkPType(x : B)
  inductive PProp (B : Prop) := MkPProp(x : B)
  reject inductive PT1 (B : Type₁) := MkPT1(x : B)
  reject inductive PT2 (B : Type₂) := MkPT2(x : B)
  reject inductive PT1Prop (B : Type₁) : Prop := MkPT1Prop(x : B)
  reject inductive PT1Dep (B : Type₁) := MkPT1Dep(n : Nat, x : B)
  reject inductive PT1Two (B : Type₁) := MkPT1Two | MkPT1Two2(x : B)
  inductive PT1None (B : Type₁) := MkPT1None
  reject inductive PMatch0 (e : False) (B : match e {}) := MkPMatch0(x : B)
  reject inductive PHole (B : ?) := MkPHole(x : B)
  -- ... each other spelling, rejected as before (D128, D55), and one nested (typed in place)
  reject inductive PLet (B : (let z = 0; Type)) := MkPLet(x : B)
  reject inductive PSeq (B : ((); Type)) := MkPSeq(x : B)
  reject inductive PMatchEq (n : Nat) (B : match n { Z => Type, S(m) => Type }) := MkPMatchEq(x : B)
  reject inductive PAsc (B : (Type : Type₁)) := MkPAsc(x : B)
  reject inductive PAlias (B : HTT) := MkPAlias(x : B)
  reject inductive PFn (B : HIdT(Type)) := MkPFn(x : B)
  reject inductive PMatchMix (n : Nat) (B : match n { Z => Type, S(m) => Prop }) := MkPMatchMix(x : B)
  reject inductive PEarlier (U : Type₁) (B : U) := MkPEarlier(x : B)
  reject inductive PT1Nest (B : Type₁) := MkPT1Nest(x : HBox(B))
  -- a global heading a field's type
  def GT (n : Nat) : Type := Nat
  def GP (n : Nat) : Prop := Eq(Nat, n, n)
  def G1 (n : Nat) : Type₁ := Type
  def G2 (n : Nat) : Type₁ := match n { Z => Type, S(p) => Prop, }
  def G3 (A : Type₁) : Type₁ := A
  -- D143: a codomain that reads as a sort without being written as one is rejected where it is
  -- written (each of these was accepted, and every use of it an internal error, until D143)
  reject def GL (n : Nat) : (let z = 0; Type) := Nat
  reject def GS (n : Nat) : ((); Type) := Nat
  def GA (n : Nat) : HTT := Nat
  def GF (n : Nat) : HIdT(Type) := Nat
  inductive WGT (k : Nat) := MkWGT(x : GT(k))
  inductive WGP (k : Nat) := MkWGP(h : GP(k))
  reject inductive WG1 := MkWG1(x : G1(Z))
  reject inductive WG1k (k : Nat) := MkWG1k(x : G1(k))
  reject inductive WG2 (k : Nat) := MkWG2(x : G2(k))
  reject inductive WG2Z := MkWG2Z(x : G2(Z))
  reject inductive WG3 := MkWG3(x : G3(Type))
  reject inductive WG3B (B : Type₁) := MkWG3B(x : G3(B))
  reject inductive WGL := MkWGL(x : GL(Z))
  reject inductive WGS := MkWGS(x : GS(Z))
  -- ... each other spelling, rejected as before (D55), and one nested
  reject inductive WGA := MkWGA(x : GA(Z))
  reject inductive WGF := MkWGF(x : GF(Z))
  reject inductive WG1Nest := MkWG1Nest(x : HBox(G1(Z)))
}

private def paramHead (n f B : String) : String :=
  s!"[D140] field x of Mk{n}: its type is the parameter B, declared at {B}: a parameter heading a field's type is written Prop or Type"
private def callHead (n f G cod : String) : String :=
  s!"[D140] field {f} of Mk{n}: its type is a call of {G}, declared to return {cod}: a function heading a field's type is declared to return Prop or Type"
private def notSort (B : String) : String :=
  s!"[D55] {B} is written where a type is expected, but its declared type is not a sort"

#guard (run "FieldHeads" FieldHeads).rejectedWith [
  ("PT1", paramHead "PT1" "x" "Type₁"), ("PT2", paramHead "PT2" "x" "Type₂"),
  ("PT1Prop", paramHead "PT1Prop" "x" "Type₁"), ("PT1Dep", paramHead "PT1Dep" "x" "Type₁"),
  ("PT1Two", paramHead "PT1Two2" "x" "Type₁"),
  -- D141 fires first: a parameter whose type says nothing about its values
  ("PMatch0", "[D141] the parameter B of PMatch0 is declared at match e {  }, which says nothing"),
  ("PHole", "[D141] the parameter B of PHole is declared at hole, which says nothing"),
  ("PLet", "[D128] the parameter B of PLet is declared at let z = 0; Type"),
  ("PSeq", "[D128] the parameter B of PSeq is declared at (); Type"),
  ("PMatchEq", "[D128] the parameter B of PMatchEq is declared at match n { Z => Type, S _ => Type }"),
  ("PAsc", notSort "B"), ("PAlias", notSort "B"), ("PFn", notSort "B"), ("PMatchMix", notSort "B"),
  ("PEarlier", notSort "B"),
  ("PT1Nest", "the parameter A of HBox has type Type₁, expected Type"),
  ("WG1", callHead "WG1" "x" "G1" "Type₁"), ("WG1k", callHead "WG1k" "x" "G1" "Type₁"),
  ("WG2", callHead "WG2" "x" "G2" "Type₁"), ("WG2Z", callHead "WG2Z" "x" "G2" "Type₁"),
  ("WG3", callHead "WG3" "x" "G3" "Type₁"), ("WG3B", callHead "WG3B" "x" "G3" "Type₁"),
  ("GL", "[D143] the result type of GL is declared at let z = 0; Type, which reads as the sort Type"),
  ("GS", "[D143] the result type of GS is declared at (); Type, which reads as the sort Type"),
  ("WGL", "unknown constant GL"), ("WGS", "unknown constant GS"),
  ("WGA", notSort "GA(0)"), ("WGF", notSort "GF(0)"),
  ("WG1Nest", "the parameter A of HBox has type Type₁, expected Type")]

/-! ## A parameter's declared type can be read (D141)

An inductive declaration's parameter whose declared type reads as "any" tells the readers nothing
about its values: a hole, a match with no arms, a `;`, a `let` or an ascription ending in one, a
call whose head's result type is one. D55 lets such a parameter stand wherever a type does
(`Box(B)`), and D128 sees no sort, so before D141 only the evaluation of the parameter's type
rejected it ("the type expected here is not known"), or D140 where it headed a field. The proof
lane's instance is `VS`. Now each is rejected before anything runs. An unknown name reads as "any"
too and keeps D118's message (`U0`); a match with a hole in one arm reads as its other arms (`MS`,
D128); a parameter whose type is a function type into a hole reads as a function (`CP0`), not as
"any", and is rejected by its evaluation, as before; a later parameter's type that calls it reads
as "any" (`CP1`). -/

ochr ReadableParams {
  inductive Box (A : Type) := MkBox(x : A)
  -- the proof lane's instance
  reject inductive VS (A : Type) (B : (A; ?)) := MkVS(y : Box(B))
  -- a hole: no field, heading a field, nested, a proposition, between two others
  reject inductive H0 (B : ?) := MkH0
  reject inductive H1 (B : ?) := MkH1(x : B)
  reject inductive H2 (B : ?) := MkH2(y : Box(B))
  reject inductive H3 (B : ?) : Prop := MkH3
  reject inductive H4 (A : Type) (B : ?) (C : Type) := MkH4(c : C)
  -- a `;` ending in a hole
  reject inductive S0 (A : Type) (B : (A; ?)) := MkS0
  reject inductive S1 (B : ((); ?)) := MkS1
  reject inductive S2 (B : ((); ?)) := MkS2(y : Box(B))
  reject inductive S3 (A : Type) (B : (A; ?)) := MkS3(x : B)
  -- a `let` ending in a hole, or naming one
  reject inductive L0 (B : (let z = 0; ?)) := MkL0
  reject inductive L1 (A : Type) (B : (let z = A; ?)) := MkL1(y : Box(B))
  reject inductive L2 (B : (let z = 0; let w = z; ?)) := MkL2(x : B)
  reject inductive L3 (B : (let T = ?; T)) := MkL3(y : Box(B))
  -- a match with no arms, or whose arms are all holes
  reject inductive M0 (e : False) (B : match e {}) := MkM0
  reject inductive M1 (e : False) (B : match e {}) := MkM1(y : Box(B))
  reject inductive M2 (e : False) (B : (let z = 0; match e {})) := MkM2(y : Box(B))
  reject inductive MH (n : Nat) (B : match n { Z => ?, S(m) => ? }) := MkMH(y : Box(B))
  -- an ascription at a hole
  reject inductive A0 (B : (Nat : ?)) := MkA0
  reject inductive A1 (B : (Type : ?)) := MkA1(y : Box(B))
  reject inductive A2 (A : Type) (B : (A : ?)) := MkA2(y : Box(B))
  reject inductive A3 (B : (Type : (let z = 0; ?))) := MkA3(y : Box(B))
  -- a call whose head's result type is a hole: a parameter's, a λ's
  reject inductive CP1 (F : Π(n : Nat). ?) (B : F(Z)) := MkCP1
  reject inductive CP2 (F : Π(n : Nat). ?) (B : F(Z)) := MkCP2(y : Box(B))
  reject inductive CP3 (F : Π(n : Nat). ?) (B : F(Z)) := MkCP3(x : B)
  reject inductive CP4 (F : Π(n : Nat). (Nat; ?)) (B : F(Z)) := MkCP4(y : Box(B))
  reject inductive LC (B : (λ(x : Nat) : ? => Type)(Z)) := MkLC(y : Box(B))
  -- the edges: an unknown name (D118), a hole in one arm only (D128), a function into a hole (its
  -- evaluation)
  reject inductive U0 (B : Foo) := MkU0(y : Box(B))
  reject inductive MS (n : Nat) (B : match n { Z => ?, S(m) => Type }) := MkMS(y : Box(B))
  reject inductive CP0 (F : Π(n : Nat). ?) := MkCP0
  -- controls
  inductive CT (B : Type) := MkCT(y : Box(B))
  inductive CN (B : Nat) := MkCN
}

private def unread (n B T : String) : String :=
  s!"[D141] the parameter {B} of {n} is declared at {T}, which says nothing about its values"

#guard (run "ReadableParams" ReadableParams).rejectedWith [
  ("VS", unread "VS" "B" "A; hole"),
  ("H0", unread "H0" "B" "hole"), ("H1", unread "H1" "B" "hole"), ("H2", unread "H2" "B" "hole"),
  ("H3", unread "H3" "B" "hole"), ("H4", unread "H4" "B" "hole"),
  ("S0", unread "S0" "B" "A; hole"), ("S1", unread "S1" "B" "(); hole"),
  ("S2", unread "S2" "B" "(); hole"), ("S3", unread "S3" "B" "A; hole"),
  ("L0", unread "L0" "B" "let z = 0; hole"), ("L1", unread "L1" "B" "let z = A; hole"),
  ("L2", unread "L2" "B" "let z = 0; let w = z; hole"), ("L3", unread "L3" "B" "let T = hole; T"),
  ("M0", unread "M0" "B" "match e {  }"), ("M1", unread "M1" "B" "match e {  }"),
  ("M2", unread "M2" "B" "let z = 0; match e {  }"),
  ("MH", unread "MH" "B" "match n { Z => hole, S _ => hole }"),
  ("A0", unread "A0" "B" "(Nat : hole)"), ("A1", unread "A1" "B" "(Type : hole)"),
  ("A2", unread "A2" "B" "(A : hole)"), ("A3", unread "A3" "B" "(Type : let z = 0; hole)"),
  ("CP1", unread "CP1" "B" "F(0)"), ("CP2", unread "CP2" "B" "F(0)"), ("CP3", unread "CP3" "B" "F(0)"),
  ("CP4", unread "CP4" "B" "F(0)"),
  ("LC", unread "LC" "B" "(fix _ (x : Nat) : hole := Type)(0)"),
  ("U0", "unknown constant Foo"),
  ("MS", "[D128] the parameter B of MS is declared at match n { Z => hole, S _ => Type }"),
  ("CP0", "?: the type expected here is not known")]

/-! ## A codomain that reads as a sort is written as one (D143)

D128's rule at a function's result type (a definition's, a λ's, a function type's, wherever it is
written). The class of a function's calls is read from its written codomain (a written sort
returns types), and the erasure pre-pass reads each call by the codomain's declared reading. A
codomain that reads as a sort without being written as one, through a `let`, a `;` or a match whose
arms all return the sort, made the two disagree: `GL` was accepted and every use of it, as a type,
in a `let`, an equation or a call, was rejected with "INTERNAL [pre-pass] GL(0): erased/proof =
(true, false) by its declared type, (false, false) after running". Each such codomain is now
rejected where it is written, before anything runs, dead code included (`Dead`), at every depth (a
parameter's function type, `HL`; a curried codomain, `HN`; inside an equation, `EqPi`; an
inductive's parameter, `IP`). A codomain that reads as data although its value is a sort (an
ascription, a constant or a type function computing `Type`: `GA`, `GC`, `GF`) is read as data on
both paths, as D55 allows (`P0 : Type₁ := Prop` used as a codomain), and is not held: its calls run,
and its uses are held by D55 and D131 as before (`UA1`, `UA4`). A constant's declared type is read
from its value (`CL`). -/

ochr WrittenCodomains {
  def TT : Type₁ := Type
  def PP : Type₁ := Prop
  def IdT (X : Type₁) : Type₁ := X
  def useTy (A : Type) : Nat := 3
  -- definitions whose codomain reads as a sort without being written as one
  reject def GL (n : Nat) : (let z = 0; Type) := Nat
  reject def GS (n : Nat) : ((); Type) := Nat
  reject def GLp (n : Nat) : (let z = 0; Prop) := Eq(Nat, n, n)
  reject def GL1 (n : Nat) : (let z = 0; Type₁) := Type
  reject def GLL (n : Nat) : (let T = Type; T) := Nat
  reject def GM (n : Nat) : match n { Z => Type, S(m) => Type } := match n { Z => Nat, S(m) => Nat }
  reject def GMl (n : Nat) : (let k = 0; match k { Z => Type, S(m) => Type }) := Nat
  -- their uses (each was an internal error)
  reject def UL1 : Nat := (let y : GL(0) = 3; y)
  reject def UL2 (x : GL(0)) : Nat := Z
  reject def UL3 : Type := GL(0)
  reject def UL4 (n : Nat) : Nat := (let T = GL(n); Z)
  reject def UL5 : Eq(Type, GL(0), Nat) := refl
  reject def UM4 (n : Nat) : Nat := (let T = GM(n); Z)
  -- λs, function types and their places
  reject def LL (n : Nat) : Nat := (let f = (λ(m : Nat) : (let z = 0; Type) => Nat); Z)
  reject def LLc (n : Nat) : Nat := (let f = (λ(m : Nat) : (let z = 0; Type) => Nat); let T = f(0); Z)
  reject def Dead (n : Nat) : Nat := (let z = Z; match z { Z => Z, S(k) => (let f = (λ(m : Nat) : (let q = 0; Type) => Nat); Z), })
  reject def HL (f : Π(m : Nat). (let z = 0; Type)) : Nat := Z
  reject def HLc (f : Π(m : Nat). (let z = 0; Type)) : Nat := (let T = f(0); Z)
  reject def HM (f : Π(m : Nat). match m { Z => Type, S(k) => Type }) : Nat := Z
  reject def HN (f : Π(m : Nat). Π(k : Nat). (let z = 0; Type)) : Nat := Z
  reject def LamPar (n : Nat) : Nat := (let f = (λ(g : Π(m : Nat). (let q = 0; Type)) : Nat => Z); Z)
  reject def AnnL (n : Nat) : Nat := (let g : Π(m : Nat). (let z = 0; Type) = (λ(m : Nat) : Type => Nat); Z)
  reject def CodPi (n : Nat) : (Π(m : Nat). (let z = 0; Type)) := (λ(m : Nat) : Type => Nat)
  reject def TyPi : Type₁ := Π(m : Nat). (let z = 0; Type)
  reject def EqPi : Eq(Type₁, Π(n : Nat). (let z = 0; Type), Π(n : Nat). Type) := refl
  reject inductive IP (F : Π(n : Nat). (let z = 0; Type)) := MkIP
  -- unchanged: written sorts; codomains that read as data (their calls run, D55 and D131 hold their
  -- uses); a constant; data and proof codomains through a `let`
  def GT (n : Nat) : Type := Nat
  def GA (n : Nat) : (Type : Type₁) := Nat
  def GC (n : Nat) : TT := Nat
  def GCp (n : Nat) : PP := Eq(Nat, n, n)
  def GF (n : Nat) : IdT(Type) := Nat
  def GMix (n : Nat) : match n { Z => Type, S(m) => Prop } := match n { Z => Nat, S(m) => Eq(Nat, m, m) }
  def UA2 (k : Nat) : Nat := useTy(GA(k))
  def UA5 : Eq(Type, GA(0), Nat) := refl
  reject def UA1 : Nat := (let y : GA(0) = 3; y)
  reject def UA4 (n : Nat) : Nat := (let T = GA(n); Z)
  def CL : (let z = 0; Type) := Nat
  def UCL : Nat := (let y : CL = 3; y)
  def GN (n : Nat) : (let z = 0; Nat) := 3
  def GPr (n : Nat) : (let z = 0; Eq(Nat, n, n)) := refl
  def LT (n : Nat) : Nat := (let f = (λ(m : Nat) : Type => Nat); let T = f(0); Z)
  def LA (n : Nat) : Nat := (let f = (λ(m : Nat) : (Type : Type₁) => Nat); Z)
  def HT (f : Π(m : Nat). Type) : Nat := (let T = f(0); Z)
  def HA (f : Π(m : Nat). (Type : Type₁)) : Nat := Z
  inductive IPok (F : Π(n : Nat). Type) := MkIPok
  def Curried (n : Nat) : (Π(m : Nat). Type) := (λ(m : Nat) : Type => Nat)
  def CurriedUse (n : Nat) : Nat := (let T = Curried(0)(0); Z)
}

private def codNotWritten (what C S : String) : String :=
  s!"[D143] the result type of {what} is declared at {C}, which reads as the sort {S} without being written as one"

#guard (run "WrittenCodomains" WrittenCodomains).rejectedWith [
  ("GL", codNotWritten "GL" "let z = 0; Type" "Type"), ("GS", codNotWritten "GS" "(); Type" "Type"),
  ("GLp", codNotWritten "GLp" "let z = 0; Prop" "Prop"), ("GL1", codNotWritten "GL1" "let z = 0; Type₁" "Type₁"),
  ("GLL", codNotWritten "GLL" "let T = Type; T" "Type"),
  ("GM", codNotWritten "GM" "match n { Z => Type, S _ => Type }" "Type"),
  ("GMl", codNotWritten "GMl" "let k = 0; match k { Z => Type, S _ => Type }" "Type"),
  ("UL1", "unknown constant GL"), ("UL2", "unknown constant GL"), ("UL3", "unknown constant GL"),
  ("UL4", "unknown constant GL"), ("UL5", "unknown constant GL"), ("UM4", "unknown constant GM"),
  ("LL", codNotWritten "a λ" "let z = 0; Type" "Type"), ("LLc", codNotWritten "a λ" "let z = 0; Type" "Type"),
  ("Dead", codNotWritten "a λ" "let q = 0; Type" "Type"),
  ("HL", codNotWritten "the function type Π(m : Nat). let z = 0; Type" "let z = 0; Type" "Type"),
  ("HLc", codNotWritten "the function type Π(m : Nat). let z = 0; Type" "let z = 0; Type" "Type"),
  ("HM", codNotWritten "the function type Π(m : Nat). match m { Z => Type, S _ => Type }" "match m { Z => Type, S _ => Type }" "Type"),
  ("HN", codNotWritten "the function type Π(k : Nat). let z = 0; Type" "let z = 0; Type" "Type"),
  ("LamPar", codNotWritten "the function type Π(m : Nat). let q = 0; Type" "let q = 0; Type" "Type"),
  ("AnnL", codNotWritten "the function type Π(m : Nat). let z = 0; Type" "let z = 0; Type" "Type"),
  ("CodPi", codNotWritten "the function type Π(m : Nat). let z = 0; Type" "let z = 0; Type" "Type"),
  ("TyPi", codNotWritten "the function type Π(m : Nat). let z = 0; Type" "let z = 0; Type" "Type"),
  ("EqPi", codNotWritten "the function type Π(n : Nat). let z = 0; Type" "let z = 0; Type" "Type"),
  ("IP", codNotWritten "the function type Π(n : Nat). let z = 0; Type" "let z = 0; Type" "Type"),
  ("UA1", "[D55] GA(0) is written where a type is expected, but its declared type is not a sort"),
  ("UA4", "[D131] T is a type (its type Type is a sort), but its declared type reads as data")]

/-! ## The inductive model's probes (notes/inductive-model.md)

Each declaration exercises one condition the model of inductive declarations derives (a least
fixed point per parameter value for a `Type₀` inductive, a subsingleton for a `Prop` one, `{•}` or
`∅` for an equation field). The accepted ones are true or well-formed; the rejected ones are
rejected for the reason given below. `TT0` is an incompleteness Lean shares: a proposition with two
constructors never eliminates into data, even where one is impossible. -/
ochr InductiveModel uses Lists {
  -- (I1) a parameter's type cannot mention the type being declared (it would need all of its parameters; since
  -- D133 its own name is not declared there)
  reject inductive PD (A : Type) (x : PD(A)) := MkPD
  -- (E3) an equation field over a type parameter of sort Type₁ is an equation between types; it holds only by conversion
  inductive TEq (U : Type₁) (a : U) (b : U) := MkTEq(h : Eq(U, a, b))
  def te : TEq(Type, Word, Word) := MkTEq[Type, Word, Word](refl)
  reject def teBad : TEq(Type, Word, Unit) := MkTEq[Type, Word, Unit](refl)
  -- (T1) the telescope order applies to an equation field's sides
  reject inductive LateEq := MkLE(h : Eq(Word, x, Zero), x : Word)
  -- (S1) a proposition with one constructor whose fields are equations is a subsingleton: it eliminates into data and types
  inductive IsZ (n : Word) : Prop := MkZ(h : Eq(Word, n, Zero))
  def UseIsZ (n : Word) (p : IsZ(n)) : Word := match p { MkZ(h) => Succ(Zero) }
  def TOf (n : Word) (p : IsZ(n)) : Type := match p { MkZ(h) => Word }
  -- (S2) a recursive subsingleton with no base case is empty: eliminating it is fine, building one needs a recursion [Rec] refuses
  inductive Inf (n : Word) : Prop := MkInf(p : Inf(Succ(n)))
  def FromInf (n : Word) (p : Inf(n)) : Word := match p { MkInf(q) => Zero }
  reject def InfLoop (n : Word) : Inf(n) by n := MkInf[n](InfLoop(Succ(n)))
  -- (S3) no large elimination from a proposition with two constructors (Forded or not)
  inductive Two (n : Word) : Prop := TA(h : Eq(Word, n, Zero)) | TB(h : Eq(Word, n, Succ(Zero)))
  reject def TT (n : Word) (p : Two(n)) : Type := match p { TA(h) => Word, TB(h) => Unit }
  reject def TT0 (p : Two(Zero)) : Word := match p { TA(h) => Zero, TB(h) => match h {} }
  -- (P2) a non-uniform occurrence may nest through a nestable parameter of another inductive
  inductive NL (A : Type) := NLeaf(x : A) | NNode(ks : List(NL(Pair(A, A))))
  def nl : NL(Word) := NNode[Word](Nil[NL(Pair(Word, Word))])
  -- (P3) a value parameter of function type indexes the family but is never called in a field type,
  -- and an argument at a value parameter may not mention the type being declared
  inductive HL (f : Π(x : Word). Type) := MkHL(y : Word)
  def hl : HL(λ(x : Word) : Type => Word) := MkHL[λ(x : Word) : Type => Word](Zero)
  reject inductive HL2 (f : Π(x : Word). Type) := MkHL2(y : f(Zero))
  inductive G (F : Π(X : Type). Type) := GB | GS(r : G(λ(X : Type) : Type => F(F(X))))
  reject inductive NegV (F : Π(X : Type). Type) := MkNegV(r : NegV(λ(X : Type) : Type => Π(y : X). NegV(F)))
  -- (E2) an equation field over a type parameter instantiated at a function type compares functions by conversion
  inductive EqF (A : Type) (a : A) (b : A) := MkEqF(h : Eq(A, a, b))
  def ef : EqF(Π(x : Word). Word, λ(x : Word) : Word => x, λ(y : Word) : Word => y) := MkEqF[Π(x : Word). Word, λ(x : Word) : Word => x, λ(y : Word) : Word => y](refl)
  reject def efBad : EqF(Π(x : Word). Word, λ(x : Word) : Word => x, λ(y : Word) : Word => Zero) := MkEqF[Π(x : Word). Word, λ(x : Word) : Word => x, λ(y : Word) : Word => Zero](refl)
}

#guard (run "InductiveModel" InductiveModel).rejectedWith [
  ("PD", "[D133] PD is not declared in its own parameters' types"),
  ("teBad", "field h of MkTEq has type ⊤, expected Eq(Type, Word, Unit)"),
  ("LateEq", "[Ind] field h of MkLE: its type mentions x, which is not an earlier field"),
  ("InfLoop", "[Rec] at InfLoop(Succ(σ0)): the argument in the decreasing position is not a strict subterm"),
  ("TT", "[D45] a match on a proof of Two returns a non-proof"),
  ("TT0", "[D45] a match on a proof of Two returns a non-proof"),
  ("HL2", "field y of MkHL2 : f(Zero): fields are first-order data"),
  ("NegV", "field r of MkNegV"),
  ("efBad", "field h of MkEqF has type ⊤, expected Eq(Π(x : Word). Word")]

/-! ## An inductive declaration binds its earlier parameters with their declared readings (D149)

While a declaration's later parameters and its fields are evaluated, its earlier parameters are
bound; they were bound with no declared reading (`other`), where a definition's are bound with
theirs. A function parameter into `Type` or `Prop` was then data to the erasure pre-pass, so a later
parameter typed by a call of it read as data and was found a type or a proof by the run: with
`F : Π(n : Nat). Type`, `inductive CPT (F : Π(n : Nat). Type) (B : F(Z)) := MkCPT` was rejected
with "INTERNAL [pre-pass] #0(0): erased/proof = (false, false) by its declared type, (true, false)
after running", while `def KT` with the same parameters was accepted; and a parameter typed by a
type a large parameter's function type captured read as no sort (`CPQ`, "κ is not a type"). Since
D149 each is bound with its reading (`telescope`'s, the one D128 and D141 read): each declaration
below is accepted and usable, or rejected by an ordinary rule (D36: a field typed by a call of a
parameter), and no internal error is reachable. Nothing else moves: D128, D140 and D141 are
decided before the parameters are bound, and D107's nesting and D120 in the field loop pass as
for any declaration (a field typed by `Nat`, `CPTx`; no field mentions the type being declared). -/

ochr ParamReadings {
  inductive Box (A : Type) := MkBox(x : A)
  def TF (n : Nat) : Type := match n { Z => Nat, S(m) => Unit, }
  -- the same parameters on a definition, accepted before D149
  def KT (F : Π(n : Nat). Type) (B : F(Z)) : Nat := Z
  def KP (P : Π(n : Nat). Prop) (h : P(Z)) : Nat := Z
  def KD (f : Π(n : Nat). Nat) (k : Eq(Nat, f(Z), Z)) : Nat := Z
  -- a later parameter typed by a call of an earlier function parameter into `Type`
  inductive CPT (F : Π(n : Nat). Type) (B : F(Z)) := MkCPT
  inductive CPT2 (F : Π(n : Nat). Type) (B : F(Z)) (C : F(S(Z))) := MkCPT2
  inductive CPTx (F : Π(n : Nat). Type) (B : F(Z)) := MkCPTx(y : Nat)
  inductive CPV (F : Π(n : Nat). Type) (m : Nat) (B : F(m)) := MkCPV
  inductive CPE (F : Π(n : Nat). Type) (B : F(Z)) (e : Eq(F(Z), B, B)) := MkCPE
  inductive CPH (G : Π(n : Nat). Type) (H : Π(x : G(Z)). Nat) := MkCPH
  inductive CPS (F : Π(n : Nat). Type) (G : Π(x : F(Z)). Prop) := MkCPS
  -- ... into `Prop`, of a data and of a proof declaration
  inductive CPP (P : Π(n : Nat). Prop) (h : P(Z)) := MkCPP
  inductive CPPp (P : Π(n : Nat). Prop) (h : P(Z)) : Prop := MkCPPp
  -- a type a large parameter's function type captures
  inductive CPQ (A : Type) (F : Π(x : A). Type) (a : A) (b : F(a)) := MkCPQ
  -- unchanged: a data function in an equation, a global type function, a match on an earlier
  -- parameter, a parameter at `Unit`
  inductive CPL (f : Π(n : Nat). Nat) (k : Eq(Nat, f(Z), Z)) := MkCPL
  inductive CPG (n : Nat) (B : TF(n)) := MkCPG
  inductive CPGf (f : Π(n : Nat). Nat) (B : TF(f(Z))) := MkCPGf
  inductive CPM (n : Nat) (B : match n { Z => Nat, S(m) => Unit, }) := MkCPM
  inductive CPU (u : Unit) (k : Eq(Unit, u, ())) := MkCPU
  -- a field typed by a call of a parameter: D36, as before (`CPN`, `CPNv`: the internal error before)
  reject inductive CPF (F : Π(n : Nat). Type) := MkCPF(y : Box(F(Z)))
  reject inductive CPN (F : Π(n : Nat). Type) (B : F(Z)) := MkCPN(y : Box(Box(F(Z))))
  reject inductive CPNv (F : Π(n : Nat). Type) (B : F(Z)) := MkCPNv(y : Box(Nat), e : Eq(F(Z), B, B))
  reject inductive CPPf (P : Π(n : Nat). Prop) := MkCPPf(h : P(Z))
  -- uses: values at closed and generic arguments, a match
  def UseCPT : CPT(λ(n : Nat) : Type => Nat, 3) := MkCPT
  def UseCPTGen (F : Π(n : Nat). Type) (b : F(Z)) : CPT(F, b) := MkCPT
  def UseCPTx (c : CPTx(λ(n : Nat) : Type => Nat, 3)) : Nat := match c { MkCPTx(y) => y, }
  def UseCPTxRun : Eq(Nat, UseCPTx(MkCPTx(4)), 4) := refl
  def UseCPV : CPV(λ(n : Nat) : Type => Nat, 2, 5) := MkCPV
  def UseCPE : CPE(λ(n : Nat) : Type => Nat, 3, refl) := MkCPE
  def UseCPS : CPS(λ(n : Nat) : Type => Nat, λ(x : Nat) : Prop => ⊤) := MkCPS
  def UseCPP : CPP(λ(n : Nat) : Prop => ⊤, refl) := MkCPP
  def UseCPQ : CPQ(Nat, λ(x : Nat) : Type => Nat, 1, 2) := MkCPQ
  def UseCPL : CPL(λ(n : Nat) : Nat => Z, refl) := MkCPL
  -- an argument of the wrong type at the later parameter
  reject def BadCPT : CPT(λ(n : Nat) : Type => Nat, ()) := MkCPT
}

#guard (run "ParamReadings" ParamReadings).rejectedWith [
  ("CPF", "field y of MkCPF : Box(F(0)): fields are first-order data"),
  ("CPN", "field y of MkCPN : Box(Box(F(0))): fields are first-order data"),
  ("CPNv", "field e of MkCPNv : Eq(F(0), B, B): fields are first-order data"),
  ("CPPf", "field h of MkCPPf : P(0): fields are first-order data")]
