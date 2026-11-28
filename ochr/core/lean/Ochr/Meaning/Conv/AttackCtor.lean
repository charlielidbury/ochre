import Ochr.Meaning.Conv.Probe

/-!
# Attacks at constructor values, on the real checker (conv2, 2026-11-28)

Verdicts asserted by the build (`def` accepted, `reject def` rejected), the reasons that matter by
`rejectedWith`. A `reject def` is a FALSE statement conversion or `Eq` must not accept (an acceptance
would be a soundness finding) or a TRUE one the checker does not reach (an incompleteness, marked).

**A constructor value at a type unknown** (`ConvAtkTy`; premise (b), the report's task 1): the model
reads a type's declaration only where a constructor value sits at the type, and none ever sits at a
type unknown: `T1`, `T2`, `T2b` are rejected at typing; a `J` out of `Eq(Type, Bool, A)` makes a
sealed block at `A`, and an equation between two of them stays stuck (`T5`); a phantom parameter is
compared across types only after conversion of the types, which fails (`T6b`, `T6c`); a refutation
through an unknown function into `A` stays stuck (`T11`). At the program's own types under a type
parameter the checker decides (`T6`: `False`; `T7`: injectivity at `Box(A)`).

**`Eq` and conversion at constructor values** (`ConvAtkCtor`, `ConvAtkMoved`; task 3):
- equal fields at parameters convertible by the unit laws (`P1`, accepted, true: `And(True, True)`
  and `True` mean the same proposition, so the records agree), or the same value parameter (`P2`);
  injectivity reaching `False` (`P3`);
- a proof field (`F1`, `F3`: proofs are `⋆`; `F2`, true but rejected: `PF`'s proof field mentions `n`,
  so `n` is an index field, and D64 blocks injectivity at index fields not convertible: an
  incompleteness, fail-safe);
- refutations under a type an unknown may refine (`D1` at `Two(A)`, `D2` at `Opt(TF(n))`, true,
  accepted); an equation between two stuck calls at a stuck type stays stuck (`D3`) and is `False` at
  an instance (`D4`); injectivity under a stuck type (`D5`);
- one-constructor types: a field access refines an unknown in place (η), but a goal or a hypothesis
  formed before it is not re-read (`H1`, `H2`: true, rejected, incompletenesses); two unknowns of a
  one-constructor type are not identified (`H3`, false, rejected);
- partly moved values against each other in `Id` (`M1`, `M2`, accepted, true: injectivity reaches the
  moved field, `⊥ ≡ ⊥`); a partly moved DEPENDENT value is never observed (`M3` to `M6`: [Repack]),
  so no equation over a partly moved value stays stuck.
-/

open Ochr Ochr.Test Ochr.Meaning.Conv

ochr ConvAtkTy uses Nats, Fixtures {
  inductive Bool := false | true
  inductive Box (A : Type) := MkBox(x : A)
  inductive Ph (A : Type) := MkPh(n : Nat)
  reject def T1 (A : Type) : A := true
  reject def T2 (A : Type) (x : A) : Box(A) := MkBox[A](true)
  reject def T2b (A : Type) (x : A) : Box(A) := MkBox(true)
  def T3 (A : Type) (h : Eq(Type, Bool, A)) : A := J(Type, Bool, A, λ(X : Type) : Type => X, h, true)
  def T3f (A : Type) (h : Eq(Type, Bool, A)) : A := J(Type, Bool, A, λ(X : Type) : Type => X, h, false)
  def T4 (A : Type) (h : Eq(Type, Bool, A)) : Eq(A, T3(A, h), T3(A, h)) := refl
  reject def T5 (A : Type) (h : Eq(Type, Bool, A)) (e : Eq(A, T3(A, h), T3f(A, h))) : False := e
  def T6 (A : Type) (e : Eq(Ph(A), MkPh[A](Z), MkPh[A](S(Z)))) : False := e
  reject def T6b (A : Type) (e : Eq(Ph(A), MkPh[A](Z), MkPh[Bool](S(Z)))) : False := e
  reject def T6c (A : Type) : Eq(Ph(A), MkPh[A](Z), MkPh[Bool](Z)) := refl
  def T7 (A : Type) (x : A) (y : A) (e : Eq(Box(A), MkBox(x), MkBox(y))) : Eq(A, x, y) := e
  def T8 (A : Type) (x : A) (e : Eq(A, x, x)) : True := e
  reject def T11 (A : Type) (f : Π(b : Bool). A) (e : Eq(A, f(true), f(false))) : False := e
}

#guard (run "ConvAtkTy" ConvAtkTy).rejectedWith [
  ("T1", "the body of T1 has type Bool, but the goal is σ0"),
  ("T2", "field x of MkBox has type Bool, expected σ0"),
  ("T5", "the body of T5 has type Eq(σ0, ⌈T3(σ0, ⋆)⌉, ⌈T3f(σ0, ⋆)⌉), but the goal is False"),
  ("T6c", "the right side of Eq has type Ph(Bool), expected Ph(σ0)"),
  ("T11", "the body of T11 has type Eq(σ0, ⌈σ2(true)⌉, ⌈σ2(false)⌉), but the goal is False")]

ochr ConvAtkCtor uses Nats, Fixtures {
  inductive Bool := false | true
  inductive PB (P : Prop) := MkPB(n : Nat)
  inductive NB (n : Nat) := MkNB(x : Nat)
  inductive Two (A : Type) := L(x : A) | R(y : A)
  inductive Opt (A : Type) := None | Some(x : A)
  inductive PF := MkPF(n : Nat, h : Eq(Nat, n, n))
  inductive Box (A : Type) := MkBox(x : A)
  def TF (n : Nat) : Type := match n { Z => Bool, S _ => Bool }
  def G1 (n : Nat) : TF(n) := match n { Z => true, S _ => true }
  def G2 (n : Nat) : TF(n) := match n { Z => false, S _ => false }
  def P1 : Eq(PB(True), MkPB[And(True, True)](Z), MkPB[True](Z)) := refl
  def P2 (n : Nat) : Eq(NB(n), MkNB[clone(n)](Z), MkNB[clone(n)](Z)) := refl
  def P3 (e : Eq(PB(True), MkPB[And(True, True)](Z), MkPB[True](S(Z)))) : False := e
  def F1 : Eq(PF, MkPF(Z, refl), MkPF(Z, refl)) := refl
  reject def F2 (e : Eq(PF, MkPF(Z, refl), MkPF(S(Z), refl))) : False := e
  def F3 (h : Eq(Nat, Z, Z)) (k : Eq(Nat, Z, Z)) : Eq(PF, MkPF(Z, h), MkPF(Z, k)) := refl
  def D1 (A : Type) (x : A) (y : A) (e : Eq(Two(A), L(x), R(y))) : False := e
  def D2 (n : Nat) (x : TF(n)) (e : Eq(Opt(TF(n)), None[TF(n)], Some(x))) : False := e
  reject def D3 (k : Nat) (e : Eq(TF(k), G1(k), G2(k))) : False := e
  def D4 (k : Nat) (e : Eq(TF(S(k)), G1(S(k)), G2(S(k)))) : False := e
  def D5 (k : Nat) (e : Eq(Box(TF(k)), MkBox(G1(k)), MkBox(G2(k)))) : Eq(TF(k), G1(k), G2(k)) := e
  reject def H1 (b : Box(Nat)) : Eq(Box(Nat), b, MkBox(clone(b.0))) := refl
  reject def H2 (A : Type) (b : Box(A)) (c : Box(A)) (e : Eq(A, b.0, c.0)) : Eq(Box(A), b, c) := e
  reject def H3 (b : Box(Nat)) (c : Box(Nat)) : Eq(Box(Nat), b, c) := refl
}

#guard (run "ConvAtkCtor" ConvAtkCtor).rejectedWith [
  ("F2", "the body of F2 has type Eq(PF, MkPF(0, ⋆), MkPF(1, ⋆)), but the goal is False"),
  ("D3", "the body of D3 has type Eq(⌈TF(σ0)⌉, ⌈G1(σ0)⌉, ⌈G2(σ0)⌉), but the goal is False"),
  ("H1", "the body of H1 has type ⊤, but the goal is Eq(Box(Nat), σ0, MkBox(σ1))"),
  ("H2", "the body of H2 has type Eq(σ0, σ3, σ4), but the goal is Eq(Box(σ0), σ1, σ2)"),
  ("H3", "the body of H3 has type ⊤, but the goal is Eq(Box(Nat), σ0, σ1)")]

ochr ConvAtkMoved uses Nats, Fixtures {
  inductive PF2 := MkPF2(n : Nat, m : Nat, h : Eq(Nat, n, n))
  inductive W := MkW(a : PF2, b : Nat)
  def M1 (q : Pair(Nat, Nat)) : Id(Unit, (let a = q.0; q.1 := Z; ()), (let a = q.0; q.1 := Z; ())) := refl
  def M2 (q : Pair(Nat, Nat)) (e : Id(Unit, (let a = q.0; q.1 := Z; ()), (let a = q.0; q.1 := S(Z); ()))) :
    False := e
  reject def M3 (q : PF2) : Id(Unit, match q { MkPF2(n, m, h) => (let a = m; n := Z; h := refl; ()) },
      match q { MkPF2(n, m, h) => (let a = m; n := S(Z); h := refl; ()) }) := refl
  reject def M4 (q : W) : Id(Unit,
      match q { MkW(a, b) => match a { MkPF2(n, m, h) => (let z = m; n := Z; h := refl; ()) } },
      match q { MkW(a, b) => match a { MkPF2(n, m, h) => (let z = m; n := S(Z); h := refl; ()) } }) := refl
  reject def M6 (q : PF2) (k : Nat) : Prop := Id(Unit,
      match q { MkPF2(n, m, h) => (let a = m; n := Z; h := refl; ()) },
      match q { MkPF2(n, m, h) => (let a = m; n := clone(k); h := refl; ()) })
}

#guard (run "ConvAtkMoved" ConvAtkMoved).rejectedWith [
  ("M3", "[Repack] Id observes it, but it is open: field m of MkPF2: it holds ⊥ (moved out, or a proof invalidated by a write to a field its type mentions)"),
  ("M4", "[Repack] Id observes it, but it is open: in field a of MkW, field m of MkPF2: it holds ⊥ (moved out, or a proof invalidated by a write to a field its type mentions)")]

/-! **Code inside the compared values** (`ConvAtkCode`; `CodeOk`, and D64 at index fields that are only convertible):
two globals with one generic observation are convertible (`FE`: `Add(Z, x)` and `x`), so are two stuck calls that
differ only in such a function (`SE`: [Conv-cong] on sealed programs, `CodeOk.sealed`), two closures (`Lam`), stuck
calls embedding them (`LamS`), constructor values holding them (`BoxF`); a function that differs at its generic call is
not (`SE3`, false, rejected). A dependent constructor whose index fields are convertible but not identical (two such
stuck calls) is taken apart (`DPa`, true, accepted): the later field's type is computed from the left side's index,
which means what the right side's means, so both are read at one hint (what `CtorEq.eqTo_fo`'s walk proves). -/

ochr ConvAtkCode uses Nats, Fixtures {
  inductive Bool := false | true
  inductive Box (A : Type) := MkBox(x : A)
  def ZAdd (x : Nat) : Nat := Add(Z, x)
  def Idn (x : Nat) : Nat := x
  def Two (x : Nat) : Nat := S(S(Z))
  def FE : Eq(Π(x : Nat). Nat, ZAdd, Idn) := refl
  def App (f : Π(x : Nat). Nat) (n : Nat) : Nat := match n { Z => f(Z), S _ => f(n) }
  def SE (k : Nat) : Eq(Nat, App(ZAdd, k), App(Idn, k)) := refl
  reject def SE3 (k : Nat) (e : Eq(Nat, App(Two, k), App(Idn, k))) : False := e
  def Lam (k : Nat) : Eq(Π(x : Nat). Nat, λ(x : Nat) : Nat => Add(Z, x), λ(y : Nat) : Nat => y) := refl
  def LamS (k : Nat) : Eq(Nat, App(λ(x : Nat) : Nat => Add(Z, x), k), App(λ(y : Nat) : Nat => y, k)) := refl
  def BoxF (k : Nat) : Eq(Box(Π(x : Nat). Nat), MkBox(ZAdd), MkBox(Idn)) := refl
  def TF (n : Nat) : Type := match n { Z => Bool, S _ => Bool }
  inductive DP := MkDP(n : Nat, v : TF(n))
  def DPa (k : Nat) (x : TF(App(ZAdd, k))) (y : TF(App(Idn, k)))
      (e : Eq(DP, MkDP(App(ZAdd, k), x), MkDP(App(Idn, k), y))) : Eq(TF(App(ZAdd, k)), x, y) := e
}

#guard (run "ConvAtkCode" ConvAtkCode).rejectedWith [
  ("SE3", "the body of SE3 has type Eq(Nat, ⌈App(Two, σ0)⌉, ⌈App(Idn, σ0)⌉), but the goal is False")]

/-! **Π-types and functions at constructor values** (`ConvAtkPi`; `PremPi`, `PremFn`): domains that are inductive
types applied to an earlier parameter compare at the generic argument (`Pi1`: `NB(n)` and `NB(Add(Z, m))`, true,
accepted), with parameters convertible by the unit laws (`Pi3`), through a type function (`Pi5`, true; `Pi6`,
false, rejected); two functions returning a constructor value whose parameter one writes and the other takes from
the codomain (`F12`, true, accepted); a function returning its argument against one returning a constant (`F13`,
false, rejected). -/

ochr ConvAtkPi uses Nats, Fixtures {
  inductive Bool := false | true
  inductive Ph (A : Type) := MkPh(n : Nat)
  inductive NB (n : Nat) := MkNB(x : Nat)
  inductive PB (P : Prop) := MkPB(n : Nat)
  def TF (n : Nat) : Type := match n { Z => Bool, S _ => Nat }
  def ZAdd (x : Nat) : Nat := Add(Z, x)
  def Pi1 : Eq(Type, Π(n : Nat) (x : NB(n)). Nat, Π(m : Nat) (y : NB(ZAdd(m))). Nat) := refl
  def Pi3 : Eq(Type, Π(x : PB(And(True, True))). Nat, Π(x : PB(True)). Nat) := refl
  def Pi5 : Eq(Type, Π(n : Nat) (x : TF(n)). Nat, Π(n : Nat) (x : TF(ZAdd(n))). Nat) := refl
  reject def Pi6 : Eq(Type, Π(n : Nat) (x : TF(n)). Nat, Π(n : Nat) (x : TF(S(n))). Nat) := refl
  def F1 (A : Type) (x : Ph(A)) : Ph(A) := MkPh[A](Z)
  def F2 (B : Type) (y : Ph(B)) : Ph(B) := MkPh(Z)
  def F12 : Eq(Π(A : Type) (x : Ph(A)). Ph(A), F1, F2) := refl
  def F3 (A : Type) (x : Ph(A)) : Ph(A) := x
  reject def F13 : Eq(Π(A : Type) (x : Ph(A)). Ph(A), F1, F3) := refl
}

#guard (run "ConvAtkPi" ConvAtkPi).rejectedWith [
  ("F13", "the body of F13 has type ⊤, but the goal is Eq(Π(A : Type) (x : Ph(A)). Ph(A), F1, F3)")]
