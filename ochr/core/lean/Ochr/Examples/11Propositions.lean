import Ochr.Examples.«00Std»

/-! # 11. Propositions: `False`, `True`, `And`, and matching on proofs

The logical connectives are ordinary inductive declarations in `Prop`, in the library:
`False` has no constructors, `True` has one (`I`, written `refl`), and `And(P, Q)` has one
with two proof fields (`⟨h, k⟩`, and `P ∧ Q` for the type). A proof's value is always `⋆`,
so a match on a proof cannot look at it: it is decided by the proof's type (D45). A match
on a proof of `False` has no arms, `match h {}`, and fits any type; a match on `And` takes
it apart. A proof can produce data (or effects) only if its type has no constructor or one
constructor whose fields are all proofs (subsingleton elimination, as in Lean).

Defined in RULES §1 (the library) and §8. -/

open Ochr.Test

ochr Propositions uses Std {
  -- ## False
  -- `False` has no constructors, so a match on a proof of it has no arms and fits any
  -- result type: data, a proposition, a statement about effects.
  def absurd (h : False) : Nat := match h {}
  def absurdP (P : Prop) (h : False) : P := match h {}
  def absurdId (x : &Nat) (h : False) : Id Unit (*x := 5) () := match h {}

  def absurdLet (h : False) : Nat := (
    let n : Nat = match h {};
    S n
  )

  -- Ex falso by transport, without the match: along `0 = 1`, a motive that is `True` at `0`
  -- and `G` elsewhere carries `refl` to a proof of `G`.
  def ExFalso (G : Prop) (h : Eq Nat Z (S Z)) : G := (
    J(Nat, Z, S Z, λ(n : Nat) : Prop => match n { Z => ⊤, S _ => G }, h, refl)
  )

  -- No closed term has type `False`.
  reject def Bot1 : False := refl
  reject def Bot2 : False := ⟨refl, refl⟩

  reject def Bot3 : False := (
    let h : False = refl;
    h
  )

  reject def Bot4 : False := absurdP(False, refl)

  -- A match with no arms needs a type with no constructors.
  reject def NotEmpty (h : True) : Nat := match h {}
  reject def NotEmptyNat (n : Nat) : Nat := match n {}

  -- ## True and And
  -- The notation is the library: `⟨h, k⟩` is `Intro(h, k)`, `⊤` is `True`, `refl` is `I`.
  def AndPair (P : Prop) (Q : Prop) (h : P) (k : Q) : P ∧ Q := ⟨h, k⟩
  def PairI (P : Prop) (Q : Prop) (h : P) (k : Q) : And(P, Q) := Intro(h, k)
  def ReflI : True := I
  reject def AndWrong (P : Prop) (Q : Prop) (h : P) (k : Q) : Q ∧ P := ⟨h, k⟩

  -- `True` is a unit for `And`, by conversion (D50): a proof of `⊤ ∧ P` keeps its type, so
  -- it can be taken apart, and it also converts to `P`.
  def TopUnit (P : Prop) (h : P) : ⊤ ∧ P := h

  def AndTrue (P : Prop) (h : ⊤ ∧ P) : P := (
    match h {
      Intro(a, b) => b,
    }
  )

  def AndTrueConv (P : Prop) (h : ⊤ ∧ P) : P := h

  -- ## Matching on proofs
  -- The arm binds the fields as places holding `⋆`, with the field types.
  def Swap (P : Prop) (Q : Prop) (h : P ∧ Q) : Q ∧ P := (
    match h {
      Intro(a, b) => ⟨b, a⟩,
    }
  )

  def Fst (P : Prop) (Q : Prop) (h : P ∧ Q) : P := (
    match h {
      Intro(a, b) => a,
    }
  )

  reject def FstWrong (P : Prop) (Q : Prop) (h : P ∧ Q) : Q := (
    match h {
      Intro(a, b) => a,
    }
  )

  def FstSwap (P : Prop) (Q : Prop) (h : P ∧ Q) : Q := Fst(Q, P, Swap(P, Q, h))

  def AndL2 (a : Nat) (b : Nat) (h : Eq Nat a 0 ∧ Eq Nat b 0) : Eq Nat a 0 := (
    match h {
      Intro(l, r) => l,
    }
  )

  -- There is no projection on proofs, since a proof is `⋆`: match instead.
  reject def Proj (P : Prop) (Q : Prop) (h : P ∧ Q) : P := h.1

  -- A match on a proof outside tail position, then used.
  def Snd (x : &Nat) (h : Eq Nat (*x) 0 ∧ Id Unit (AddM(x, 0)) ()) : Id Unit (AddM(x, 0)) () := (
    let k = match h {
      Intro(a, b) => b,
    };
    k
  )

  -- Matching on a proof does not move or inspect it: it is still usable afterwards.
  def Twice (P : Prop) (Q : Prop) (h : P ∧ Q) : P ∧ P := (
    let a = Fst(P, Q, h);
    match h {
      Intro(u, v) => ⟨a, u⟩,
    }
  )

  -- An `Id` over several places computes to a conjunction, which a match takes apart.
  def SplitId (x : &Nat) (y : &Nat) (h : Id Unit (*x := 1; *y := 2) (*x := 3; *y := 4)) : Eq Nat 1 3 := (
    match h {
      Intro(a, b) => a,
    }
  )

  def TwoOwners (x : &Nat) (y : &Nat) (h : Id Unit (*x := 0; *y := 0) ()) : Eq Nat 0 (*x) := (
    match h {
      Intro(l, r) => l,
    }
  )

  def TwoOwnersR (x : &Nat) (y : &Nat) (h : Id Unit (*x := 0; *y := 0) ()) : Eq Nat 0 (*y) := (
    match h {
      Intro(l, r) => r,
    }
  )

  reject def TwoOwnersWrong (x : &Nat) (y : &Nat) (h : Id Unit (*x := 0; *y := 0) ()) : Eq Nat 0 (*y) := (
    match h {
      Intro(l, r) => l,
    }
  )

  def ThreeOwners (x : &Nat) (y : &Nat) (z : &Nat) (h : Id Unit (*x := 0; *y := 0; *z := 0) ()) : Eq Nat 0 (*z) := (
    match h {
      Intro(l, r) => match r {
        Intro(m, n) => n,
      },
    }
  )

  -- ## Data and effects from a proof
  -- `True` and `And` are subsingletons (one constructor, only proof fields), so a match on
  -- them may return data ...
  def FromTrue (h : True) : Nat := (
    match h {
      I => 5,
    }
  )

  def FromTrueIs : Eq Nat (FromTrue(refl)) 5 := refl

  def Two (P : Prop) (Q : Prop) (h : P ∧ Q) : Nat := (
    match h {
      Intro(a, b) => 2,
    }
  )

  def TwoIs (P : Prop) (Q : Prop) (h : P ∧ Q) : Eq Nat (Two(P, Q, h)) 2 := refl

  -- ... or have an effect.
  def WriteIf (x : &Nat) (P : Prop) (Q : Prop) (h : P ∧ Q) : Unit := (
    match h {
      Intro(a, b) => *x := 7,
    }
  )

  def WriteIfId (x : &Nat) (P : Prop) (Q : Prop) (h : P ∧ Q) : Id Unit (WriteIf(x, P, Q, h)) (*x := 7) := refl

  reject def WriteIfLie (x : &Nat) (P : Prop) (Q : Prop) (h : P ∧ Q) :
      Id Unit (WriteIf(x, P, Q, h)) () := refl

  -- The lemmas above were checked at `h = ⋆`, their generic call. Here they are used at
  -- propositions about a mutated place, where the statements are computed by running
  -- `WriteIf` and `Two` directly: the two ways of computing them agree.
  def WriteIfAt (x : &Nat) (y : &Nat) (e : Id Unit (AddM(y, 0)) ()) :
      Id Unit (WriteIf(x, Id Unit (AddM(y, 0)) (), Eq Nat (*y) (*y), ⟨e, refl⟩)) (*x := 7) := (
    WriteIfId(x, Id Unit (AddM(y, 0)) (), Eq Nat (*y) (*y), ⟨e, refl⟩)
  )

  reject def WriteIfAtLie (x : &Nat) (y : &Nat) (e : Id Unit (AddM(y, 0)) ()) :
      Id Unit (WriteIf(x, Id Unit (AddM(y, 0)) (), Eq Nat (*y) (*y), ⟨e, refl⟩)) (*x := 8) := (
    WriteIfId(x, Id Unit (AddM(y, 0)) (), Eq Nat (*y) (*y), ⟨e, refl⟩)
  )

  def TwoAt (y : &Nat) : Eq Nat (Two(Id Unit (AddM(y, 0)) (), ⊤, ⟨AddMZero(y), refl⟩)) 2 := (
    TwoIs(Id Unit (AddM(y, 0)) (), ⊤, ⟨AddMZero(y), refl⟩)
  )

  reject def TwoAtLie (y : &Nat) : Eq Nat (Two(Id Unit (AddM(y, 0)) (), ⊤, ⟨AddMZero(y), refl⟩)) 3 := (
    TwoIs(Id Unit (AddM(y, 0)) (), ⊤, ⟨AddMZero(y), refl⟩)
  )

  -- A match with no arms is unreachable in a closed run, but an open one reaches it when a
  -- refinement makes a hypothesis false: `GetZIs` splits `*x`, and in its `S` arm the sealed
  -- `GetZ(&*x, h)` is re-run with `*x` a successor. Outside a proof position such a match is
  -- stuck, not `⋆` (D58), so `*q` stays a sealed program and the arm, `match h {}`, checks.
  -- As `⋆` (switch `zeroArmStuck`), `*q` would read through a `⋆`, a type error.
  def IsZ (n : Nat) : Prop := (
    match n {
      Z => ⊤,
      S _ => False,
    }
  )

  def GetZ (x : &Nat) (h : IsZ(*x)) : &Nat := (
    match *x {
      Z => x,
      S _ => match h {},
    }
  )

  def GetZIs (x : &Nat) (h : IsZ(*x)) : Id Nat (let q = GetZ(&*x, h); clone(*q)) 0 := (
    match *x {
      Z => refl,
      S _ => match h {},
    }
  )
}

-- the exact number of declarations (a truncated file changes it)
#guard Propositions.decls.length == 45

/-! ## Destructuring `let`

`let ⟨x, y⟩ = p; u` is `match p { Intro(x, y) => u }`, and `let (x, y) = p; u` is
`match p { Mk(x, y) => u }`: surface sugar for a one-arm match (D60). `⟨a, b, c⟩` is
`⟨a, ⟨b, c⟩⟩`, patterns nest, and `_` ignores a field. On a place the names are its
sub-places, as in any match; any other term is bound to a temporary first. -/

ochr Destructuring uses Std {
  def AndPair (P : Prop) (Q : Prop) (h : P) (k : Q) : P ∧ Q := ⟨h, k⟩

  def DAnd (P : Prop) (Q : Prop) (h : P ∧ Q) : Q ∧ P := (
    let ⟨a, b⟩ = h;
    ⟨b, a⟩
  )

  def DAnd3 (P : Prop) (Q : Prop) (R : Prop) (h : P ∧ (Q ∧ R)) : R := (
    let ⟨a, b, c⟩ = h;
    c
  )

  def DNested (P : Prop) (Q : Prop) (R : Prop) (h : (P ∧ Q) ∧ R) : Q := (
    let ⟨⟨a, b⟩, c⟩ = h;
    b
  )

  def DWild (P : Prop) (Q : Prop) (h : P ∧ Q) : Q := (
    let ⟨_, b⟩ = h;
    b
  )

  -- A field that is a function into proofs is called like any function, and the call is a
  -- proof (hashmap-port: the pre-pass once read it as data).
  def DCallField (P : Prop) (h : P ∧ (Π(k : Nat). Eq Nat k k)) : Eq Nat 0 0 := (
    let ⟨_, f⟩ = h;
    f(0)
  )

  -- On a term: a temporary holds it.
  def DTerm (P : Prop) (Q : Prop) (h : P) (k : Q) : Q := (
    let ⟨a, b⟩ = AndPair(P, Q, h, k);
    b
  )

  -- Pairs; on `*p` the names are places inside `*p`, so writing them writes `*p`.
  def DPair (p : Nat × Nat) : Nat := (
    let (a, b) = p;
    Add(a, b)
  )

  def DPairSwap (p : &(Nat × Nat)) : Unit := (
    let (a, b) = *p;
    let t = a;
    a := b;
    b := t
  )

  def DPairSwapIs : Id (Nat × Nat) (let p = (1, 2); DPairSwap(&p); p) (2, 1) := refl

  -- The fields have their own types, and the pattern must fit the scrutinee's type.
  reject def DWrongField (P : Prop) (Q : Prop) (h : P ∧ Q) : P := (
    let ⟨a, b⟩ = h;
    b
  )

  reject def DNotPair (n : Nat) : Nat := (
    let (a, b) = n;
    a
  )
}

-- the exact number of declarations (a truncated file changes it)
#guard Destructuring.decls.length == 12

/-! ## Subsingleton elimination

`Or` has two constructors, so it is not a subsingleton: a match on a proof of `Or` may only
produce a proof, and is itself a proof, erased wherever it runs. The same holds for a
single constructor with a data field (`Sq`). -/

ochr Subsingletons uses Std, Fixtures {
  inductive Or (P : Prop) (Q : Prop) : Prop := Inl(p : P) | Inr(q : Q)

  -- Elimination into propositions: every arm is a proof, so the match is one.
  def OrComm (P : Prop) (Q : Prop) (h : Or(P, Q)) : Or(Q, P) := (
    match h {
      Inl(p) => Inr(p),
      Inr(q) => Inl(q),
    }
  )

  def OrElim (P : Prop) (Q : Prop) (R : Prop) (h : Or(P, Q)) (f : Π(p : P). R) (g : Π(q : Q). R) : R := (
    match h {
      Inl(p) => f(p),
      Inr(q) => g(q),
    }
  )

  def OrLet (P : Prop) (h : Or(P, P)) : P := (
    let k : P = match h {
      Inl(p) => p,
      Inr(q) => q,
    };
    k
  )

  -- `Sq` has one constructor with a data field. Elimination into propositions is fine, and
  -- the data field is bound to a fresh abstract value, which can be split on (D49) ...
  inductive Sq : Prop := MkSq(n : Nat)

  def SqTrue (h : Sq) : True := (
    match h {
      MkSq(n) => refl,
    }
  )

  def SqSplit (h : Sq) : True := (
    match h {
      MkSq(n) => match n {
        Z => refl,
        S m => refl,
      },
    }
  )

  -- ... but nothing is known about it.
  reject def SqZero (h : Sq) : Id Nat 0 0 := (
    match h {
      MkSq(n) => (refl : Id Nat n 0),
    }
  )

  -- A match that cannot pick an arm is a proof, erased wherever it runs (RULES P2). `EffL`'s
  -- body is such a match, so its calls write nothing. (Its own check runs each arm's write
  -- in tail position, where confinement does not apply: see `Erasure`.)
  -- Rejected since D55: `V(Z)` is a type only by computation (its declared type `U(Z)` is not a sort).
  reject def EffL (x : &Nat) (h : Or(⊤, ⊤)) : V(Z) := (
    match h {
      Inl(p) => (
        *x := 1;
        refl
      ),
      Inr(q) => (
        *x := 2;
        refl
      ),
    }
  )

  -- Rejected since D55, with `EffL`.
  reject def EffLNoop (x : &Nat) (h : Or(⊤, ⊤)) : Id Unit (let t = EffL(x, h); ()) () := refl
  reject def EffLOne (x : &Nat) (h : Or(⊤, ⊤)) : Id Unit (let t = EffL(x, h); ()) (*x := 1) := refl

  -- Inline, outside tail position, the arms are erased terms, each on its own copy (D68).
  -- Rejected since D55: `V(Z)` is a type only by computation (its declared type `U(Z)` is not a sort).
  reject def EffInline (x : &Nat) (h : Or(⊤, ⊤)) : Nat := (
    let t : V(Z) = match h {
      Inl(p) => (
        *x := 1;
        refl
      ),
      Inr(q) => (
        *x := 2;
        refl
      ),
    };
    0
  )

  -- ## What goes wrong without subsingleton elimination
  -- Data from `Or` would tell `Inl` from `Inr`, which proof irrelevance identifies. `Irr`
  -- holds at its generic call (`h` and `k` are both `⋆`), so `Irr(Inl(refl), Inr(refl))`
  -- would say `true = false`, which is `False` (D45). In this checker a proof is always `⋆`,
  -- so the closed `Boom` needs both D45 and D42 switched off (switches `subsingleton` and
  -- `propValues`); with D45 alone off, `OrLie` is accepted, whose meaning in the model is
  -- `true = false`: `IsL` has no set-theoretic meaning.
  reject def IsL (h : Or(True, True)) : Bool := (
    match h {
      Inl(p) => true,
      Inr(q) => false,
    }
  )

  reject def Irr (h : Or(True, True)) (k : Or(True, True)) : Eq Bool (IsL(h)) (IsL(k)) := refl
  reject def Boom : False := Irr(Inl(refl), Inr(refl))
  reject def OrLie : Eq Bool (IsL(Inl(refl))) (IsL(Inr(refl))) := refl

  -- One constructor with a data field is not a subsingleton either: the field is not known.
  reject def Get (h : Sq) : Nat := (
    match h {
      MkSq(n) => n,
    }
  )

  reject def SqIrr (h : Sq) (k : Sq) : Eq Nat (Get(h)) (Get(k)) := refl
  reject def SqBoom : False := SqIrr(MkSq(0), MkSq(1))
}

-- the exact number of declarations (a truncated file changes it)
#guard Subsingletons.decls.length == 19
