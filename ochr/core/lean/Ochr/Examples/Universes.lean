import Ochr.Test

/-! # 14. Universes

`Prop` and `Type` both live in `Type₁`, side by side, as `Prop` and `Set` do in Coq (D66):
`Type` holds only types that exist at runtime, which is what lets every `A : Type` be
borrowed (`BorrowTypes`). There is no `Type : Type`, and universes are not cumulative, so a
proposition is not a `Type` (RULES preamble). Non-cumulativity matters for erasure: with
`Prop ≤ Type`, a function declared to return a `Type` could return a proposition, and whether
its calls are erased would depend on the value (D28).

Defined in the preamble of RULES, in P2 and in D66. -/

open Ochr.Test

ochr Universes {
  -- `Prop` and `Type` are types in `Type₁` ...
  def PropInType1 : Type₁ := Prop
  def TypeInType1 : Type₁ := Type

  -- ... but neither is a `Type`: `Prop` is not in `Type` (D66) ...
  reject def PropInType : Type := Prop
  reject def TypeInType : Type := Type

  -- ... and a proposition is not a `Type`.
  reject def NonCumul (P : Prop) : Type := P

  -- ## What goes wrong with borrows of types
  -- A borrow of a type would make `Type` impredicative (D48 (1)): `Impred` quantifies over all
  -- of `Type` and is itself in `Type`, and `SelfApp` applies the polymorphic identity to
  -- itself. An impredicative `Type` with the impredicative `Prop` beside it admits Hurkens'
  -- paradox, a proof of `False`, and has no set-theoretic model. So only what is in `Type`
  -- may be borrowed, and `Type` itself is in `Type₁` (see `BorrowTypes`).
  reject def Impred : Type := Π(x : &Type) (a : *x). *x
  -- twin of Impred: the borrow is of a `Nat`, which is in `Type`, not of `Type` itself, so the dependent `*x` becomes `Nat`
  def ImpredOk : Type := Π(x : &Nat) (a : Nat). Nat
  reject def PolyId (x : &Type) (a : *x) : *x := a
  -- twin of PolyId: borrows a `Nat` instead of `Type`
  def PolyIdOk (x : &Nat) (a : Nat) : Nat := a

  reject def SelfApp (u : Unit) : Impred := (
    let T = Impred;
    PolyId(&T, PolyId)
  )

  -- twin of SelfApp: applies the twin identity to a borrowed `Nat`, no self-application at a borrowed `Type`
  def SelfAppOk (u : Unit) : Nat := (
    let c = 0;
    PolyIdOk(&c, 3)
  )

  reject def SelfAppEq (n : Nat) :
      Id(Nat, let T = Impred; let f = PolyId(&T, PolyId); let N = Nat; f(&N, n), n) := refl

  -- twin of SelfAppEq: the twin identity applied to a borrowed `Nat` returns its argument
  def SelfAppEqOk (n : Nat) :
      Id(Nat, let f = PolyIdOk; let c = 0; f(&c, n), n) := refl

  reject def PolyTy : Type := Π(x : &Type) (a : Nat). Nat
  -- twin of PolyTy: borrows a `Nat` instead of `Type`
  def PolyTyOk : Type := Π(x : &Nat) (a : Nat). Nat
}


/-! ## Sorts are syntactic

A term written where a type is expected must have a *declared* type that is a sort, read
from the declared types of its heads without normalising (D55). `T(Z)` computes to `⊤`, but
its declared type is `P(Z)`, which is a sort only by computation, so it cannot be written as a
type. Before D55 Ochr had two notions of "proposition", the declared sort (erasure) and the
computed one (conversion), and moving values between them gave closed proofs of `False`
(reviewer-4 W1: `Boom`, `Boom2`, `Boom4`) and a proposition with two distinguishable proofs
(W2: `TT`, `K1`, `K2`). The programs are reviewer-4's, verbatim except that `P` is declared in `Type₁`, where `Prop` lives since D66; with D55 each falls where
`T(Z)` is written as a type (D54 alone already rejects `Boom`,
`Boom2`, `RunIs` and `Lie4` at their arguments).

Defined in RULES P2 ("Sorts are syntactic"). -/

ochr Sorts {
  def P (n : Nat) : Type₁ := match n { Z => Prop, S _ => Prop }
  def T (n : Nat) : P(n) := match n { Z => ⊤, S _ => ⊤ }
  reject def W (u : Unit) : T(Z) := refl
  -- twin of W: the type is written `⊤`, whose declared type is a sort, instead of `T(Z)`
  def WOk (u : Unit) : ⊤ := refl
  reject def f (x : &Nat) : T(Z) := (*x := S(Z); W(()))
  -- twin of f: result type written `⊤` instead of `T(Z)`
  def fOk (x : &Nat) : ⊤ := (*x := S(Z); WOk(()))
  def RunK (k : Π(x : &Nat). ⊤) (x : &Nat) : Unit := (k(x); ())
  def Stmt (k : Π(x : &Nat). ⊤) (x : &Nat) : Id(Unit, RunK(k, &*x), ()) := refl
  reject def Boom : False := (let c = 0; Stmt(f, &c))

  def RunGen (k : Π(x : &Nat). ⊤) : Id(Nat, let c = 0; RunK(k, &c); c, 0) := refl
  reject def Boom2 : False := RunGen(f)
  reject def RunIs : Id(Nat, let c = 0; RunK(f, &c); c, 1) := refl

  reject def Lie4 (n : Nat) : Id(Nat, (let c = Z; match n {
      Z => (let q : (Π(x : &Nat). ⊤) = f; q(&c); ()),
      S _ => (let q : (Π(x : &Nat). ⊤) = f; q(&c); ()) }; c), 1) := match n { Z => refl, S _ => refl }
  reject def Boom4 : False := Lie4(0)

  reject def TT : Prop := Π(x : &Nat). T(Z)
  -- twin of TT: `⊤` instead of `T(Z)`
  def TTOk : Prop := Π(x : &Nat). ⊤
  reject def g2 (x : &Nat) : T(Z) := W(())
  -- twin of g2: result type written `⊤` instead of `T(Z)`
  def g2Ok (x : &Nat) : ⊤ := WOk(())
  reject def k (h : Π(x : &Nat). T(Z)) : Nat := (let c = Z; h(&c); c)
  -- twin of k: the argument's result type is written `⊤` instead of `T(Z)`
  def kOk (h : Π(x : &Nat). ⊤) : Nat := (let c = Z; h(&c); c)
  reject def K1 : Eq(Nat, k(f), 1) := refl
  -- twin of K1: the `⊤`-typed `kOk` and `fOk`, whose call is erased, so the count stays 0 rather than 1
  def K1Ok : Eq(Nat, kOk(fOk), 0) := refl
  reject def K2 : Eq(Nat, k(g2), 0) := refl
  -- twin of K2: the `⊤`-typed `kOk` and `g2Ok`
  def K2Ok : Eq(Nat, kOk(g2Ok), 0) := refl
}



/-! ## A Π-type inside a type (D86)

The sort of a Π-type is read from the declared sorts of its parameter types and codomain
(RULES P2), and a parameter type or codomain that is itself a Π-type is no exception.
`Π(x : Nat). Prop` is in `Type₁`, so a Π over it is in `Type₁` too, and
`Π(y : Nat). Eq(Nat, y, y)` is a proposition, so a Π into it is a proposition. Before D86
the readers read every Π-type written inside a type, or bound by a `let`, as `Type`. Typing
rejected `Pred1` and `Curried` with its INTERNAL [D55] assertion, and `LetProp` and `LetCod`,
whose `A` was then not a proposition, with its INTERNAL [pre-pass] assertion. A function's type
is never asserted, so D66 borrowed a function in `Type₁` (`BorrowG`), a proof (`BorrowQ`) and
the place of a stuck match (`StuckG`), while the same types written through `Pow` were
rejected (`BorrowG2`, `StuckG2`).

Defined in RULES P2 ("The sort of a Π-type is read from declared sorts") and D66. -/

ochr PiSorts {
  -- A Π over predicates on `Nat` is in `Type₁` ...
  def Pred1 : Type₁ := Π(f : Π(x : Nat). Prop). Nat
  -- twin of Pred1: universes are not cumulative, so it is not in `Type₂` ...
  reject def Pred2 : Type₂ := Π(f : Π(x : Nat). Prop). Nat
  -- ... and not in `Type`
  reject def Pred0 : Type := Π(f : Π(x : Nat). Prop). Nat
  -- twin of Pred0: a Π over functions into data is in `Type`
  def Fn0 : Type := Π(f : Π(x : Nat). Nat). Nat
  -- A Π-type in a Π-type in a domain.
  def PredPred1 : Type₁ := Π(f : Π(g : Π(x : Nat). Prop). Nat). Nat
  reject def PredPred0 : Type := Π(f : Π(g : Π(x : Nat). Prop). Nat). Nat
  -- twin of PredPred0: data all the way in
  def FnFn0 : Type := Π(f : Π(g : Π(x : Nat). Nat). Nat). Nat
  def UnivUniv2 : Type₂ := Π(f : Π(g : Π(A : Type₁). Nat). Nat). Nat
  reject def UnivUniv1 : Type₁ := Π(f : Π(g : Π(A : Type₁). Nat). Nat). Nat
  -- A proposition over a Π-type domain is still a proposition (impredicativity), and so is a
  -- curried one, whose codomain is a Π-type into `Prop`.
  def AllPred : Prop := Π(f : Π(x : Nat). Prop). Π(y : Nat). Eq(Nat, y, y)
  reject def AllPred1 : Type₁ := Π(f : Π(x : Nat). Prop). Π(y : Nat). Eq(Nat, y, y)
  def AllPredPred : Prop := Π(f : Π(g : Π(x : Nat). Prop). Nat). Eq(Nat, 0, 0)
  def Curried : Prop := Π(x : Nat). Π(y : Nat). Eq(Nat, y, y)
  reject def CurriedT : Type := Π(x : Nat). Π(y : Nat). Eq(Nat, y, y)
  def CurriedProp : Type₁ := Π(x : Nat). Π(y : Nat). Prop

  -- ## Borrows (D66)
  -- A function's type is read as a written Π-type is: `g`'s is in `Type₁` and `q`'s is a
  -- proposition (`q` is a proof), so neither is borrowed, as `g2`'s, written through `Pow`, is not.
  def g (f : Π(x : Nat). Prop) : Nat := 0
  def q (x : Nat) : (Π(y : Nat). Eq(Nat, y, y)) := λ(y : Nat) : Eq(Nat, y, y) => refl
  def Pow (X : Type) : Type₁ := Π(a : X). Prop
  def g2 (f : Pow(Nat)) : Nat := 0
  reject def BorrowG (n : Nat) : Unit := (let r = g; let b = &r; ())
  reject def BorrowG2 (n : Nat) : Unit := (let r = g2; let b = &r; ())
  reject def BorrowQ (n : Nat) : Unit := (let r = q; let b = &r; ())
  -- twins of BorrowG, BorrowG2 and BorrowQ: functions in `Type`, over functions into data or
  -- returning functions into data
  def h (f : Π(x : Nat). Nat) : Nat := 0
  def k (x : Nat) : (Π(y : Nat). Nat) := λ(y : Nat) : Nat => y
  def BorrowH (n : Nat) : Unit := (let r = h; let b = &r; ())
  def BorrowK (n : Nat) : Unit := (let r = k; let b = &r; ())
  -- The same for a closure's type, and for the borrow type `&A` ...
  reject def BorrowPredClo (n : Nat) : Unit := (let f = (λ(p : Π(x : Nat). Prop) : Nat => 0); let b = &f; ())
  reject def BorrowFamId (n : Nat) : Unit := (let f = (λ(T : Π(x : Nat). Type) (m : Nat) (a : T(m)) : T(m) => a); let b = &f; ())
  reject def BorrowCurriedClo (n : Nat) : Unit := (let f = (λ(x : Nat) : (Π(y : Nat). Eq(Nat, y, y)) => (λ(y : Nat) : Eq(Nat, y, y) => refl)); let b = &f; ())
  reject def RefPredFn (f : &(Π(p : Π(x : Nat). Prop). Nat)) : Nat := 0
  -- twins of BorrowPredClo, BorrowFamId, BorrowCurriedClo and RefPredFn: closures and a Π-type
  -- in `Type`
  def BorrowFnClo (n : Nat) : Unit := (let f = (λ(p : Π(x : Nat). Nat) : Nat => 0); let b = &f; ())
  def BorrowFamApp (n : Nat) : Unit := (let f = (λ(t : Π(x : Nat). Nat) (m : Nat) : Nat => t(m)); let b = &f; ())
  def BorrowCurriedDataClo (n : Nat) : Unit := (let f = (λ(x : Nat) : (Π(y : Nat). Nat) => (λ(y : Nat) : Nat => y)); let b = &f; ())
  def RefFnFn (f : &(Π(p : Π(x : Nat). Nat). Nat)) : Nat := 0
  -- ... and for the place a stuck match borrows, here because an arm assigns it.
  reject def StuckG (n : Nat) : Nat := (let r = g; match n { Z => (r := g), S _ => () }; 0)
  reject def StuckG2 (n : Nat) : Nat := (let r = g2; match n { Z => (r := g2), S _ => () }; 0)
  -- twin of StuckG and StuckG2: the place holds a function in `Type`
  def StuckH (n : Nat) : Nat := (let r = h; match n { Z => (r := h), S _ => () }; 0)

  -- ## Proofs
  -- A proof annotated with a `let`-bound proposition is a proof: its write is erased with it.
  def LetProp (x : &Nat) : Id(Nat, (let A = (Π(y : Nat). ⊤); let p : A = (*x := 5; λ(y : Nat) : ⊤ => refl); clone(*x)), clone(*x)) := refl
  -- twin of LetProp: the write is not seen
  reject def LetPropWrites (x : &Nat) : Id(Nat, (let A = (Π(y : Nat). ⊤); let p : A = (*x := 5; λ(y : Nat) : ⊤ => refl); clone(*x)), 5) := refl
  -- A closure into a `let`-bound proposition is a proof, so its call is erased, write and all.
  def LetCod (n : Nat) : Id(Nat, (let c = 0; let A = (Π(y : Nat). ⊤); let f = (λ(x : &Nat) : A => (*x := 1; λ(y : Nat) : ⊤ => refl)); f(&c); c), 0) := refl
  -- twin of LetCod: the write is not seen
  reject def LetCodRuns (n : Nat) : Id(Nat, (let c = 0; let A = (Π(y : Nat). ⊤); let f = (λ(x : &Nat) : A => (*x := 1; λ(y : Nat) : ⊤ => refl)); f(&c); c), 1) := refl
  -- So is a closure into a curried proposition. Its class is read from its codomain's syntax,
  -- so this held before D86 too.
  def CurriedErased (n : Nat) : Id(Nat, (let c = 0; let f = (λ(x : &Nat) : (Π(y : Nat). Eq(Nat, y, y)) => (*x := 1; λ(y : Nat) : Eq(Nat, y, y) => refl)); f(&c); c), 0) := refl
  -- twin of CurriedErased: the write is not seen
  reject def CurriedRuns (n : Nat) : Id(Nat, (let c = 0; let f = (λ(x : &Nat) : (Π(y : Nat). Eq(Nat, y, y)) => (*x := 1; λ(y : Nat) : Eq(Nat, y, y) => refl)); f(&c); c), 1) := refl
}

#guard (run "PiSorts" PiSorts).rejectedWith [
  ("Pred2", "the body of Pred2 has type Type₁, but the goal is Type₂"),
  ("Pred0", "the body of Pred0 has type Type₁, but the goal is Type"),
  ("PredPred0", "the body of PredPred0 has type Type₁, but the goal is Type"),
  ("UnivUniv1", "the body of UnivUniv1 has type Type₂, but the goal is Type₁"),
  ("AllPred1", "the body of AllPred1 has type Prop, but the goal is Type₁"),
  ("CurriedT", "the body of CurriedT has type Prop, but the goal is Type"),
  ("BorrowG", "[D66] &r: its type Π(f : Π(x : Nat). Prop). Nat is not in Type₀"),
  ("BorrowG2", "[D66] &r: its type Π(f : Pow(Nat)). Nat is not in Type₀"),
  ("BorrowQ", "[D66] &r: its type Π(x : Nat). Π(y : Nat). Eq(Nat, y, y) is not in Type₀"),
  ("BorrowPredClo", "[D66] &f: its type Π(p : Π(x : Nat). Prop). Nat is not in Type₀"),
  ("BorrowFamId", "[D66] &f: its type Π(T : Π(x : Nat). Type) (m : Nat) (a : T(m)). T(m) is not in Type₀"),
  ("BorrowCurriedClo", "[D66] &f: its type Π(x : Nat). Π(y : Nat). Eq(Nat, y, y) is not in Type₀"),
  ("RefPredFn", "[D66] &Π(p : Π(x : Nat). Prop). Nat: Π(p : Π(x : Nat). Prop). Nat is not in Type₀"),
  ("StuckG", "[D66] a stuck match would borrow r, whose type Π(f : Π(x : Nat). Prop). Nat is not known to be in Type₀"),
  ("StuckG2", "[D66] a stuck match would borrow r, whose type Π(f : Pow(Nat)). Nat is not known to be in Type₀"),
  ("LetPropWrites", "the body of LetPropWrites has type ⊤, but the goal is Eq(Nat, σ0, 5)"),
  ("LetCodRuns", "the body of LetCodRuns has type ⊤, but the goal is False"),
  ("CurriedRuns", "the body of CurriedRuns has type ⊤, but the goal is False")]

/-! ## A binding's reading agrees with its type and its value (D131)

The declared-type readers see a sort only where one is written (D55). Behind a call of a function
whose body is a sort (`PropF(x)` with `PropF (n : Nat) : Type₁ := Prop`), an ascription, a
constant, a call under `;` or `let`, or a match whose arms disagree, a type reads as data, and so
does a proof whose type is formed from it (a `J` through a motive with such a codomain). The
decisions that consume a reading (the join, copy or move, a capture) then disagreed with the run:
`V1` was accepted and its call `V1(Z)` rejected, because the join moved the proof `⋆` read as data
at the instance, where the read never moves `⋆`. Since D131, at every binding a typed run makes (a
`let`, a parameter, a λ's parameter) the reading's class (a proof, a type, data) agrees with the
class of the stored type (a proposition, a sort, anything else) and with the class of the value (a
proof value `⋆` is read as a proof). Each hidden form by each binder is rejected, the `J` whose
type is stuck on the hidden sort (`SJ…`, `SCap…`, `SMove…`) by the value; with `Prop` written,
each is accepted, with its instance and a generic caller. Generated by
`ochr/core/probes/hidden-sorts/gen.py`. -/

ochr HiddenSorts {
  def PropF (n : Nat) : Type₁ := Prop
  def PC : Type₁ := Prop
  def GHCall (n : Nat) : PropF(n) := ⊤
  def GHAsc (n : Nat) : (Prop : Type₁) := ⊤
  def GHConst (n : Nat) : PC := ⊤
  def GHSeq (n : Nat) : ((); PropF(n)) := ⊤
  def GHLet (n : Nat) : (let z = 0; PropF(n)) := ⊤
  def GHPlain (n : Nat) : Prop := ⊤
  -- the proof lane's example (`FitProofCE.V1`), and its control with the codomain written `Prop`
  reject def V1 (k : Nat) : Unit := (let y = J(Nat, Z, Z, λ(x : Nat) : PropF(x) => ⊤, refl, refl); match k { Z => (let z = y; ()), S(j) => (), }; let w = y; ())
  def V3 (k : Nat) : Unit := (let y = J(Nat, Z, Z, λ(x : Nat) : Prop => ⊤, refl, refl); match k { Z => (let z = y; ()), S(j) => (), }; let w = y; ())
  def V4 : Unit := V3(Z)
  reject def GJCall (k : Nat) : Unit := (let y = J(Nat, Z, Z, (λ(x : Nat) : PropF(x) => ⊤), refl, refl); match k { Z => (let z = y; ()), S(j) => () }; let w = y; ())
  reject def GCapCall (k : Nat) : Unit := (let y = J(Nat, Z, Z, (λ(x : Nat) : PropF(x) => ⊤), refl, refl); let g = (λ(u : Unit) : Unit => (let a = y; u)); match k { Z => g(()), S(j) => () }; let w = y; ())
  reject def GAnnCall (k : Nat) : Unit := (let y : PropF(k) = ⊤; match k { Z => (let z = y; ()), S(j) => () }; let w = y; ())
  reject def GRetCall (k : Nat) : Unit := (let y = GHCall(k); match k { Z => (let z = y; ()), S(j) => () }; let w = y; ())
  reject def GParCall (k : Nat) (P : PropF(k)) : Unit := (match k { Z => (let z = P; ()), S(j) => () }; let w = P; ())
  reject def GLamCall (k : Nat) : Unit := (let f = (λ(P : PropF(k)) : Unit => (match k { Z => (let z = P; ()), S(j) => () }; let w = P; ())); f(⊤))
  reject def GSJCall (k : Nat) (e : Eq(Nat, Z, k)) : Unit := (let y = J(Nat, Z, k, (λ(x : Nat) : PropF(x) => match x { Z => ⊤, S(m) => ⊤ }), e, refl); match k { Z => (let z = y; ()), S(j) => () }; let w = y; ())
  reject def GSCapCall (k : Nat) (e : Eq(Nat, Z, k)) : Unit := (let y = J(Nat, Z, k, (λ(x : Nat) : PropF(x) => match x { Z => ⊤, S(m) => ⊤ }), e, refl); let g = (λ(u : Unit) : Unit => (let a = y; u)); match k { Z => g(()), S(j) => () }; let w = y; ())
  reject def GSMoveCall (k : Nat) (e : Eq(Nat, Z, k)) : Unit := (let y = J(Nat, Z, k, (λ(x : Nat) : PropF(x) => match x { Z => ⊤, S(m) => ⊤ }), e, refl); let a = y; let b = y; ())
  reject def GJAsc (k : Nat) : Unit := (let y = J(Nat, Z, Z, (λ(x : Nat) : (Prop : Type₁) => ⊤), refl, refl); match k { Z => (let z = y; ()), S(j) => () }; let w = y; ())
  reject def GCapAsc (k : Nat) : Unit := (let y = J(Nat, Z, Z, (λ(x : Nat) : (Prop : Type₁) => ⊤), refl, refl); let g = (λ(u : Unit) : Unit => (let a = y; u)); match k { Z => g(()), S(j) => () }; let w = y; ())
  reject def GAnnAsc (k : Nat) : Unit := (let y : (Prop : Type₁) = ⊤; match k { Z => (let z = y; ()), S(j) => () }; let w = y; ())
  reject def GRetAsc (k : Nat) : Unit := (let y = GHAsc(k); match k { Z => (let z = y; ()), S(j) => () }; let w = y; ())
  reject def GParAsc (k : Nat) (P : (Prop : Type₁)) : Unit := (match k { Z => (let z = P; ()), S(j) => () }; let w = P; ())
  reject def GLamAsc (k : Nat) : Unit := (let f = (λ(P : (Prop : Type₁)) : Unit => (match k { Z => (let z = P; ()), S(j) => () }; let w = P; ())); f(⊤))
  reject def GSJAsc (k : Nat) (e : Eq(Nat, Z, k)) : Unit := (let y = J(Nat, Z, k, (λ(x : Nat) : (Prop : Type₁) => match x { Z => ⊤, S(m) => ⊤ }), e, refl); match k { Z => (let z = y; ()), S(j) => () }; let w = y; ())
  reject def GSCapAsc (k : Nat) (e : Eq(Nat, Z, k)) : Unit := (let y = J(Nat, Z, k, (λ(x : Nat) : (Prop : Type₁) => match x { Z => ⊤, S(m) => ⊤ }), e, refl); let g = (λ(u : Unit) : Unit => (let a = y; u)); match k { Z => g(()), S(j) => () }; let w = y; ())
  reject def GSMoveAsc (k : Nat) (e : Eq(Nat, Z, k)) : Unit := (let y = J(Nat, Z, k, (λ(x : Nat) : (Prop : Type₁) => match x { Z => ⊤, S(m) => ⊤ }), e, refl); let a = y; let b = y; ())
  reject def GJConst (k : Nat) : Unit := (let y = J(Nat, Z, Z, (λ(x : Nat) : PC => ⊤), refl, refl); match k { Z => (let z = y; ()), S(j) => () }; let w = y; ())
  reject def GCapConst (k : Nat) : Unit := (let y = J(Nat, Z, Z, (λ(x : Nat) : PC => ⊤), refl, refl); let g = (λ(u : Unit) : Unit => (let a = y; u)); match k { Z => g(()), S(j) => () }; let w = y; ())
  reject def GAnnConst (k : Nat) : Unit := (let y : PC = ⊤; match k { Z => (let z = y; ()), S(j) => () }; let w = y; ())
  reject def GRetConst (k : Nat) : Unit := (let y = GHConst(k); match k { Z => (let z = y; ()), S(j) => () }; let w = y; ())
  reject def GParConst (k : Nat) (P : PC) : Unit := (match k { Z => (let z = P; ()), S(j) => () }; let w = P; ())
  reject def GLamConst (k : Nat) : Unit := (let f = (λ(P : PC) : Unit => (match k { Z => (let z = P; ()), S(j) => () }; let w = P; ())); f(⊤))
  reject def GSJConst (k : Nat) (e : Eq(Nat, Z, k)) : Unit := (let y = J(Nat, Z, k, (λ(x : Nat) : PC => match x { Z => ⊤, S(m) => ⊤ }), e, refl); match k { Z => (let z = y; ()), S(j) => () }; let w = y; ())
  reject def GSCapConst (k : Nat) (e : Eq(Nat, Z, k)) : Unit := (let y = J(Nat, Z, k, (λ(x : Nat) : PC => match x { Z => ⊤, S(m) => ⊤ }), e, refl); let g = (λ(u : Unit) : Unit => (let a = y; u)); match k { Z => g(()), S(j) => () }; let w = y; ())
  reject def GSMoveConst (k : Nat) (e : Eq(Nat, Z, k)) : Unit := (let y = J(Nat, Z, k, (λ(x : Nat) : PC => match x { Z => ⊤, S(m) => ⊤ }), e, refl); let a = y; let b = y; ())
  reject def GJSeq (k : Nat) : Unit := (let y = J(Nat, Z, Z, (λ(x : Nat) : ((); PropF(x)) => ⊤), refl, refl); match k { Z => (let z = y; ()), S(j) => () }; let w = y; ())
  reject def GCapSeq (k : Nat) : Unit := (let y = J(Nat, Z, Z, (λ(x : Nat) : ((); PropF(x)) => ⊤), refl, refl); let g = (λ(u : Unit) : Unit => (let a = y; u)); match k { Z => g(()), S(j) => () }; let w = y; ())
  reject def GAnnSeq (k : Nat) : Unit := (let y : ((); PropF(k)) = ⊤; match k { Z => (let z = y; ()), S(j) => () }; let w = y; ())
  reject def GRetSeq (k : Nat) : Unit := (let y = GHSeq(k); match k { Z => (let z = y; ()), S(j) => () }; let w = y; ())
  reject def GParSeq (k : Nat) (P : ((); PropF(k))) : Unit := (match k { Z => (let z = P; ()), S(j) => () }; let w = P; ())
  reject def GLamSeq (k : Nat) : Unit := (let f = (λ(P : ((); PropF(k))) : Unit => (match k { Z => (let z = P; ()), S(j) => () }; let w = P; ())); f(⊤))
  reject def GSJSeq (k : Nat) (e : Eq(Nat, Z, k)) : Unit := (let y = J(Nat, Z, k, (λ(x : Nat) : ((); PropF(x)) => match x { Z => ⊤, S(m) => ⊤ }), e, refl); match k { Z => (let z = y; ()), S(j) => () }; let w = y; ())
  reject def GSCapSeq (k : Nat) (e : Eq(Nat, Z, k)) : Unit := (let y = J(Nat, Z, k, (λ(x : Nat) : ((); PropF(x)) => match x { Z => ⊤, S(m) => ⊤ }), e, refl); let g = (λ(u : Unit) : Unit => (let a = y; u)); match k { Z => g(()), S(j) => () }; let w = y; ())
  reject def GSMoveSeq (k : Nat) (e : Eq(Nat, Z, k)) : Unit := (let y = J(Nat, Z, k, (λ(x : Nat) : ((); PropF(x)) => match x { Z => ⊤, S(m) => ⊤ }), e, refl); let a = y; let b = y; ())
  reject def GJLet (k : Nat) : Unit := (let y = J(Nat, Z, Z, (λ(x : Nat) : (let z = 0; PropF(x)) => ⊤), refl, refl); match k { Z => (let z = y; ()), S(j) => () }; let w = y; ())
  reject def GCapLet (k : Nat) : Unit := (let y = J(Nat, Z, Z, (λ(x : Nat) : (let z = 0; PropF(x)) => ⊤), refl, refl); let g = (λ(u : Unit) : Unit => (let a = y; u)); match k { Z => g(()), S(j) => () }; let w = y; ())
  reject def GAnnLet (k : Nat) : Unit := (let y : (let z = 0; PropF(k)) = ⊤; match k { Z => (let z = y; ()), S(j) => () }; let w = y; ())
  reject def GRetLet (k : Nat) : Unit := (let y = GHLet(k); match k { Z => (let z = y; ()), S(j) => () }; let w = y; ())
  reject def GParLet (k : Nat) (P : (let z = 0; PropF(k))) : Unit := (match k { Z => (let z = P; ()), S(j) => () }; let w = P; ())
  reject def GLamLet (k : Nat) : Unit := (let f = (λ(P : (let z = 0; PropF(k))) : Unit => (match k { Z => (let z = P; ()), S(j) => () }; let w = P; ())); f(⊤))
  reject def GSJLet (k : Nat) (e : Eq(Nat, Z, k)) : Unit := (let y = J(Nat, Z, k, (λ(x : Nat) : (let z = 0; PropF(x)) => match x { Z => ⊤, S(m) => ⊤ }), e, refl); match k { Z => (let z = y; ()), S(j) => () }; let w = y; ())
  reject def GSCapLet (k : Nat) (e : Eq(Nat, Z, k)) : Unit := (let y = J(Nat, Z, k, (λ(x : Nat) : (let z = 0; PropF(x)) => match x { Z => ⊤, S(m) => ⊤ }), e, refl); let g = (λ(u : Unit) : Unit => (let a = y; u)); match k { Z => g(()), S(j) => () }; let w = y; ())
  reject def GSMoveLet (k : Nat) (e : Eq(Nat, Z, k)) : Unit := (let y = J(Nat, Z, k, (λ(x : Nat) : (let z = 0; PropF(x)) => match x { Z => ⊤, S(m) => ⊤ }), e, refl); let a = y; let b = y; ())
  reject def GParMatch (k : Nat) (P : match k { Z => Prop, S(m) => PropF(m) }) : Unit := (match k { Z => (let z = P; ()), S(j) => () }; let w = P; ())
  reject def GLamMatch (k : Nat) : Unit := (let f = (λ(P : match k { Z => Prop, S(m) => PropF(m) }) : Unit => (match k { Z => (let z = P; ()), S(j) => () }; let w = P; ())); f(⊤))
  reject def GSJMatch (k : Nat) (e : Eq(Nat, Z, k)) : Unit := (let y = J(Nat, Z, k, (λ(x : Nat) : match x { Z => Prop, S(m) => PropF(m) } => match x { Z => ⊤, S(m) => ⊤ }), e, refl); match k { Z => (let z = y; ()), S(j) => () }; let w = y; ())
  reject def GSCapMatch (k : Nat) (e : Eq(Nat, Z, k)) : Unit := (let y = J(Nat, Z, k, (λ(x : Nat) : match x { Z => Prop, S(m) => PropF(m) } => match x { Z => ⊤, S(m) => ⊤ }), e, refl); let g = (λ(u : Unit) : Unit => (let a = y; u)); match k { Z => g(()), S(j) => () }; let w = y; ())
  reject def GSMoveMatch (k : Nat) (e : Eq(Nat, Z, k)) : Unit := (let y = J(Nat, Z, k, (λ(x : Nat) : match x { Z => Prop, S(m) => PropF(m) } => match x { Z => ⊤, S(m) => ⊤ }), e, refl); let a = y; let b = y; ())
  def GJPlain (k : Nat) : Unit := (let y = J(Nat, Z, Z, (λ(x : Nat) : Prop => ⊤), refl, refl); match k { Z => (let z = y; ()), S(j) => () }; let w = y; ())
  def CJPlain : Unit := GJPlain(Z)
  def HJPlain (k : Nat) : Unit := GJPlain(k)
  def GCapPlain (k : Nat) : Unit := (let y = J(Nat, Z, Z, (λ(x : Nat) : Prop => ⊤), refl, refl); let g = (λ(u : Unit) : Unit => (let a = y; u)); match k { Z => g(()), S(j) => () }; let w = y; ())
  def CCapPlain : Unit := GCapPlain(Z)
  def HCapPlain (k : Nat) : Unit := GCapPlain(k)
  def GAnnPlain (k : Nat) : Unit := (let y : Prop = ⊤; match k { Z => (let z = y; ()), S(j) => () }; let w = y; ())
  def CAnnPlain : Unit := GAnnPlain(Z)
  def HAnnPlain (k : Nat) : Unit := GAnnPlain(k)
  def GRetPlain (k : Nat) : Unit := (let y = GHPlain(k); match k { Z => (let z = y; ()), S(j) => () }; let w = y; ())
  def CRetPlain : Unit := GRetPlain(Z)
  def HRetPlain (k : Nat) : Unit := GRetPlain(k)
  def GParPlain (k : Nat) (P : Prop) : Unit := (match k { Z => (let z = P; ()), S(j) => () }; let w = P; ())
  def CParPlain : Unit := GParPlain(Z, ⊤)
  def HParPlain (k : Nat) (P : Prop) : Unit := GParPlain(k, P)
  def GLamPlain (k : Nat) : Unit := (let f = (λ(P : Prop) : Unit => (match k { Z => (let z = P; ()), S(j) => () }; let w = P; ())); f(⊤))
  def CLamPlain : Unit := GLamPlain(Z)
  def HLamPlain (k : Nat) : Unit := GLamPlain(k)
  def GSJPlain (k : Nat) (e : Eq(Nat, Z, k)) : Unit := (let y = J(Nat, Z, k, (λ(x : Nat) : Prop => match x { Z => ⊤, S(m) => ⊤ }), e, refl); match k { Z => (let z = y; ()), S(j) => () }; let w = y; ())
  def CSJPlain : Unit := GSJPlain(Z, refl)
  def HSJPlain (k : Nat) (e : Eq(Nat, Z, k)) : Unit := GSJPlain(k, e)
  def GSCapPlain (k : Nat) (e : Eq(Nat, Z, k)) : Unit := (let y = J(Nat, Z, k, (λ(x : Nat) : Prop => match x { Z => ⊤, S(m) => ⊤ }), e, refl); let g = (λ(u : Unit) : Unit => (let a = y; u)); match k { Z => g(()), S(j) => () }; let w = y; ())
  def CSCapPlain : Unit := GSCapPlain(Z, refl)
  def HSCapPlain (k : Nat) (e : Eq(Nat, Z, k)) : Unit := GSCapPlain(k, e)
  def GSMovePlain (k : Nat) (e : Eq(Nat, Z, k)) : Unit := (let y = J(Nat, Z, k, (λ(x : Nat) : Prop => match x { Z => ⊤, S(m) => ⊤ }), e, refl); let a = y; let b = y; ())
  def CSMovePlain : Unit := GSMovePlain(Z, refl)
  def HSMovePlain (k : Nat) (e : Eq(Nat, Z, k)) : Unit := GSMovePlain(k, e)
}

#guard (run "HiddenSorts" HiddenSorts).rejectedWith [
  ("V1", "[D131] y is a proof"),
  ("GJCall", "[D131] y is a proof"),
  ("GCapCall", "[D131] y is a proof"),
  ("GAnnCall", "[D131] y is a type"),
  ("GRetCall", "[D131] y is a type"),
  ("GParCall", "[D131] P is a type"),
  ("GLamCall", "[D131] P is a type"),
  ("GSJCall", "[D131] y holds a proof"),
  ("GSCapCall", "[D131] y holds a proof"),
  ("GSMoveCall", "[D131] y holds a proof"),
  ("GJAsc", "[D131] y is a proof"),
  ("GCapAsc", "[D131] y is a proof"),
  ("GAnnAsc", "[D131] y is a type"),
  ("GRetAsc", "[D131] y is a type"),
  ("GParAsc", "[D131] P is a type"),
  ("GLamAsc", "[D131] P is a type"),
  ("GSJAsc", "[D131] y holds a proof"),
  ("GSCapAsc", "[D131] y holds a proof"),
  ("GSMoveAsc", "[D131] y holds a proof"),
  ("GJConst", "[D131] y is a proof"),
  ("GCapConst", "[D131] y is a proof"),
  ("GAnnConst", "[D131] y is a type"),
  ("GRetConst", "[D131] y is a type"),
  ("GParConst", "[D131] P is a type"),
  ("GLamConst", "[D131] P is a type"),
  ("GSJConst", "[D131] y holds a proof"),
  ("GSCapConst", "[D131] y holds a proof"),
  ("GSMoveConst", "[D131] y holds a proof"),
  ("GJSeq", "[D131] y is a proof"),
  ("GCapSeq", "[D131] y is a proof"),
  ("GAnnSeq", "[D131] y is a type"),
  ("GRetSeq", "[D131] y is a type"),
  ("GParSeq", "[D131] P is a type"),
  ("GLamSeq", "[D131] P is a type"),
  ("GSJSeq", "[D131] y holds a proof"),
  ("GSCapSeq", "[D131] y holds a proof"),
  ("GSMoveSeq", "[D131] y holds a proof"),
  ("GJLet", "[D131] y is a proof"),
  ("GCapLet", "[D131] y is a proof"),
  ("GAnnLet", "[D131] y is a type"),
  ("GRetLet", "[D131] y is a type"),
  ("GParLet", "[D131] P is a type"),
  ("GLamLet", "[D131] P is a type"),
  ("GSJLet", "[D131] y holds a proof"),
  ("GSCapLet", "[D131] y holds a proof"),
  ("GSMoveLet", "[D131] y holds a proof"),
  ("GParMatch", "[D131] z is a type"),
  ("GLamMatch", "[D131] z is a type"),
  ("GSJMatch", "[D131] y holds a proof"),
  ("GSCapMatch", "[D131] y holds a proof"),
  ("GSMoveMatch", "[D131] y holds a proof")]
