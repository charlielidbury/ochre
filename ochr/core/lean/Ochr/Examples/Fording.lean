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
  def CastRefl (v : VecF(Word, Zero)) : Prop := Id(VecF(Word, Zero), CastV(Zero, Zero, refl, clone(v)), v)

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
  -- A13: an honest write inside one side of an `Id`, and the lying version: the side's match is
  -- closed off as a stuck block, whose borrow of `*r` ends at its arm's return (D72)
  def IdHonest (r : &VS) : Prop := Id(Unit, match *r { MkVS(n, h) => (n := Zero; h := refl) }, ())
  reject def IdLie (r : &VS) : Prop := Id(Unit, match *r { MkVS(n, h) => n := Succ(Zero) }, ())
  -- the same lie in a match followed by more code (D72), and its honest twin
  reject def SeqLie (r : &VS) : Unit := (match *r { MkVS(n, h) => n := Succ(Zero) }; ())
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
  ("Loop", "field e of MkLoop : EqF(Loop, x, x): Loop occurs at the parameter A of EqF, which EqF passes to a type function (one may use its argument negatively): not strictly positive (K4, D36)"),
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
  ("IdLie", "[Repack] *r is lent to a stuck match, whose arm returns with it, but it is open: field h of MkVS: it holds ⊥"),
  ("SeqLie", "[Repack] *r is lent to a stuck match, whose arm returns with it, but it is open: field h of MkVS: it holds ⊥")]
