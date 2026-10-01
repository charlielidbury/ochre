import Ochr.Examples.«00Std»

/-! # 13. Erasure: proofs and types leave no trace

Proofs and types are erased when a program runs, so whether the checker runs them or skips
them must make no difference. It runs every erased term (argument evaluation included) on
a private copy of the environment and throws the copy away (RULES P2, D26). A proof may
still use local state of its own.

Which terms are erased is decided from the syntax alone, never from a computed value: a
function returns proofs if its declared result type is a proposition and types if it is a
sort, a call is erased if its function's is, and a match that is closed off is erased
when each of its arms is (D28, D35, D40, D42). As a fail-safe, an erased term may not
write, borrow or move a place that outlives it, except by passing it to another erased
call (D41, *confinement*).

Most of this file is what goes wrong otherwise. A statement is computed twice, once at a
definition's generic call through closing off and once directly at each use, and the two
must agree on which terms are erased. Every disagreement found so far gave a closed proof
of a false equation.

Defined in RULES P2. -/

open Ochr.Test

ochr Erasure uses Std {
  -- ## Erased terms run on a private copy
  -- Citing a lemma about `x`, argument included, does not move `x` (switch `eraseOnCopy`).
  def LemmaMoves (x : &Nat) : Unit := (
    let h = AddMZero(x);
    AddM(x, 0)
  )

  -- A call whose result type is a sort is erased too: `F5` writes, but `F5(&*x)` leaves no
  -- trace.
  def F5 (x : &Nat) : Prop := (
    *x := 5;
    ⊤
  )

  def TypeErased (x : &Nat) : Id(Nat, let T = F5(&*x); *x, *x) := refl

  -- A proof's argument runs on the copy as well, so `W5`'s write inside it is not seen ...
  def Lemma (u : Unit) : ⊤ := refl
  def W5 (x : &Nat) : Unit := *x := 5
  reject def EffArg (x : &Nat) : Id(Unit, Lemma(W5(&*x)); (), *x := 5) := refl

  -- ... and since the argument writes `*x` for a call that is not erased, confinement makes
  -- it an error rather than a silent no-op.
  reject def EffArgErased (x : &Nat) : Id(Unit, Lemma(W5(&*x)); (), ()) := refl

  -- ## Confinement
  -- A proof may change its own locals ...
  def Local (x : &Nat) : Nat := (
    let h : ⊤ = (let y = 0; y := 1; refl);
    clone(*x)
  )

  -- ... and hand an outer place to another proof (as `AddMZero`'s recursive call does) ...
  def Pass (x : &Nat) : Nat := (
    let h = AddMZero(&*x);
    clone(*x)
  )

  -- ... but may not write, borrow or move one itself.
  reject def Write (x : &Nat) : Nat := (
    let h : ⊤ = (*x := 5; refl);
    clone(*x)
  )

  reject def Borrow (x : &Nat) : Nat := (
    let h : ⊤ = (AddM(&*x, 0); refl);
    clone(*x)
  )

  reject def Move (x : &Nat) : Nat := (
    let h : ⊤ = (let y = x; refl);
    0
  )

  -- A proof in tail position is not an erased term as a whole: its steps run, here a call
  -- that is not erased on the borrow parameter. Confinement does not apply to it.
  def TailSteps (x : &Nat) : ⊤ := (
    AddM(&*x, 0);
    refl
  )

  -- ## Proofs with effects are indistinguishable from proofs without
  -- `P1` and `P2` both prove `Π(x : &Nat). ⊤`; `P2` writes, but calls of it are erased, so no
  -- observation sees the write, and identifying `P1` with `P2` is sound: `F(P2)`, "calling
  -- `P2` leaves its argument alone", is true ...
  def P1 (x : &Nat) : ⊤ := refl

  def P2 (x : &Nat) : ⊤ := (
    *x := 7;
    refl
  )

  def F (h : Π(x : &Nat). ⊤) : Prop := Id(Nat, let a = 0; h(&a); a, 0)
  def FP2 : Id(Nat, let a = 0; P2(&a); a, 0) := refl

  def BoomIsTrue : ⊤ := (
    J(Π(x : &Nat). ⊤, P1, P2, λ(g : Π(x : &Nat). ⊤) : Prop => F(g), (refl : Eq(Π(x : &Nat). ⊤, P1, P2)), refl)
  )

  -- ... and transporting along `P1 = P2` gives no proof of `False`.
  reject def Boom : False := (
    J(Π(x : &Nat). ⊤, P1, P2, λ(g : Π(x : &Nat). ⊤) : Prop => F(g), (refl : Eq(Π(x : &Nat). ⊤, P1, P2)), refl)
  )

  -- The same through a function that runs its argument on a local: `k(P1)` and `k(P2)` are
  -- both `0`.
  reject def Boom' : Eq(Nat, 0, 1) := (
    (λ(k : Π(h : Π(x : &Nat). ⊤). Nat) : Eq(Nat, k(P1), k(P2)) => refl)(
      λ(h : Π(x : &Nat). ⊤) : Nat => (let a = 0; h(&a); a)
    )
  )

  -- The same inside a stuck match: sealing `UseP(p2, &c, n)` and then refining `n`, or running
  -- it directly, both leave `c` at `0`.
  def p1 (x : &Nat) : Eq(Nat, 0, 0) := refl

  def p2 (x : &Nat) : Eq(Nat, 0, 0) := (
    *x := S(Z);
    refl
  )

  def UseP (h : Π(x : &Nat). Eq(Nat, 0, 0)) (x : &Nat) (n : Nat) : Unit := (
    match n {
      Z => (
        h(x);
        ()
      ),
      S _ => (
        h(x);
        ()
      ),
    }
  )

  def TA2 (n : Nat) : Id(Nat, let c = 0; UseP(p1, &c, n); c, let c = 0; UseP(p2, &c, n); c) := refl
  reject def TA2Z : Eq(Nat, 0, 1) := TA2(0)

  -- ## What goes wrong without the private copy
  -- Confinement lets an erased term pass an outer place to an erased call, as a proof passes
  -- `x` to a lemma. Without the private copy (switch `eraseOnCopy`) that call's writes persist
  -- on the direct path: in the `S` arm, `F5(&*x)` writes `*x := 5`, while the closed-off
  -- block, being erased, skips it. So `LieP2`, true as checked, is false at `1`, and
  -- `BoomP2` is a closed proof of `False` (fuzz-port).
  def LieP2 (x : &Nat) : Id(Nat, (let a = match *x { Z => refl, S p => (F5(&*x); refl) }; *x), *x) := refl
  reject def BoomP2Pair : False ∧ False := (let c = 1; LieP2(&c))

  reject def BoomP2 : False := (
    let b = BoomP2Pair;
    match b {
      Intro(l, r) => l,
    }
  )

  -- ## What goes wrong without confinement
  -- A match whose arms are proofs that write `a`. An earlier version erased it when it was
  -- closed off but ran it when it ran directly, so sealing then refining gave `0` and running
  -- directly gave `1`: `N1Closed` proved `1 = 0`. With the private copy both give `0`; with
  -- confinement, a proof that writes `a` is an error. Switching both off accepts `N1Closed`
  -- and `QBoom` (switches `eraseOnCopy` and `confine`).
  reject def N1T (n : Nat) :
      Id(Nat, (let a = 0; let h = match n { Z => (a := S(Z); refl), S _ => refl }; a), 0) := refl

  reject def N1Closed : Id(Nat, 1, 0) := N1T(0)

  reject def Q (b : Nat) (a : Nat) :
      Id(⊤, (match b { Z => (a := S(Z); refl), S _ => (a := S(Z); refl) }), refl) := refl

  reject def QBoom : False := (
    J(Nat, S(Z), Z, λ(n : Nat) : Prop => match n { Z => False, S _ => ⊤ }, Q(0, 0), refl)
  )
}

-- the exact number of declarations (a truncated file changes it)
#guard Erasure.decls.length == 32

/-! ## What goes wrong when erasure is decided from values

Each program below makes the two ways of computing a statement disagree about whether some
term is erased, if that is decided from a computed value instead of the syntax. `Fixtures`' `U(n)` is
`Prop` for every `n`, but only after computing it: at an abstract `n` it is the stuck
`⌈U(σ)⌉`. `V(n)` is a proof of `U(n)`. Each `Lie…` is a statement about whether a write to
`c` happens, and each `Boom…` its instance at `Z`. If the generic call and the instance
disagreed about whether the write is erased, some `Boom…` would be a closed proof of a
false equation. Under the rules the write happens on both paths, so each `Lie…` is either
true, with a true instance, or rejected. The ledger names the switch each one depends on;
since the erasure pre-pass decides erasure from declared types before a term runs, D35's
after-the-fact clauses have no switches (they flipped nothing), and their witnesses stay as
regressions. -/

ochr ErasureBySyntax uses Fixtures {
  -- A top-level function whose result type computes to a sort (D28, switch `erasureByDecl`).
  -- `W` returns data, by its declared result type `U(n)`, so its write runs at every
  -- instance; `MainW(0)` really is `1`, as compiled code computes.
  def W (x : &Nat) (n : Nat) : U(n) := (
    *x := S(Z);
    V(n)
  )

  def Lie (n : Nat) : Id(Nat, let c = Z; W(&c, n); c, S(Z)) := refl
  reject def Boom : Eq(Nat, Z, S(Z)) := Lie(Z)

  def MainW (n : Nat) : Nat := (
    let c = Z;
    W(&c, n);
    c
  )

  def MainW0 : Id(Nat, MainW(0), 1) := refl

  -- A local function whose result type computes to a sort: its class is read from the
  -- result type as written, `U(n)`, so `h(&c)` runs on both paths (D35; appendix note 1).
  -- The erasure pre-pass reads it before the call runs, so the old after-the-fact switch is
  -- gone.
  def LieL (n : Nat) :
      Id(Nat, let h = (λ(x : &Nat) : U(n) => (*x := S(Z); V(n))); let c = Z; h(&c); c, S(Z)) := refl

  reject def BoomL : Eq(Nat, Z, S(Z)) := LieL(Z)

  -- The same, with the closure made by a top-level function.
  def MkClosure (n : Nat) : (Π(x : &Nat). U(n)) := λ(x : &Nat) : U(n) => (*x := S(Z); V(clone(n)))
  def Lie8 (n : Nat) : Id(Nat, let c = Z; let g = MkClosure(n); g(&c); c, S(Z)) := refl
  reject def Boom8 : Eq(Nat, Z, S(Z)) := Lie8(Z)
  reject def Direct8 : Id(Nat, let c = Z; let g = MkClosure(0); g(&c); c, Z) := refl

  -- A match whose value is a type. Closed off, it looked like a call returning types and
  -- was erased; run directly, it was not. A closed-off match is erased only when each of
  -- its arms is (D35, D40; appendix note 2; the pre-pass, no switch since). The true
  -- statement is proved by splitting on `n`.
  reject def LieB (n : Nat) :
      Id(Nat, (let c = Z; let T = match n { Z => (c := S(Z); ⊤), S _ => (c := S(Z); ⊤) }; c), Z) := refl

  reject def BoomB : Eq(Nat, S(Z), Z) := LieB(Z)

  def TruthB (n : Nat) :
      Id(Nat, (let c = Z; let T = match n { Z => (c := S(Z); ⊤), S _ => (c := S(Z); ⊤) }; c), S(Z)) := (
    match n {
      Z => refl,
      S _ => refl,
    }
  )

  -- The same with an annotation: the type `Prop` is not a proposition, so the match is not
  -- erased on either path; and with a data annotation the write is kept.
  reject def Lie7 (n : Nat) :
      Id(Nat, (let c = Z; let T : Prop = match n { Z => (c := S(Z); ⊤), S _ => (c := S(Z); ⊤) }; c), Z) := refl

  reject def Boom7 : Eq(Nat, S(Z), Z) := Lie7(Z)

  reject def P3d (n : Nat) : Nat := (
    let c = Z;
    let T : Nat = match n {
      Z => (
        c := S(Z);
        0
      ),
      S _ => (
        c := S(Z);
        0
      ),
    };
    let h : Id(Nat, c, Z) = refl;
    c
  )

  -- A closed-off match erased because its computed type is a proposition disagrees with the
  -- direct path, where `f`'s calls are classed by syntax: `V(Z)` computes to `⊤` but is not
  -- declared a proposition, so `f(&c)` runs.
  -- Rejected since D55: `V(Z)` is a type only by computation (its declared type `U(Z)` is not a sort).
  reject def LieG (m : Nat) (g : Π(y : Nat). V(Z)) :
      Id(Nat, (
          let c = Z;
          let f = (λ(x : &Nat) : V(Z) => (*x := S(Z); g(0)));
          let T = match m { Z => f(&c), S _ => f(&c) };
          c
        ), Z) := (
    refl
  )

  -- Rejected since D55: `V(Z)` is a type only by computation (its declared type `U(Z)` is not a sort).
  reject def BoomG : Eq(Nat, S(Z), Z) := LieG(Z, λ(y : Nat) : V(Z) => refl)

  -- Rejected since D55: `V(Z)` is a type only by computation (its declared type `U(Z)` is not a sort).
  reject def TruthG (m : Nat) (g : Π(y : Nat). V(Z)) :
      Id(Nat, (
          let c = Z;
          let f = (λ(x : &Nat) : V(Z) => (*x := S(Z); g(0)));
          let T = match m { Z => f(&c), S _ => f(&c) };
          c
        ), S(Z)) := (
    match m {
      Z => refl,
      S _ => refl,
    }
  )

  -- A sequence whose tail returns a type is not erased; only the call `F(&c)` runs on a
  -- private copy (D35; the pre-pass, no switch since).
  def F (x : &Nat) : Prop := (
    *x := S(Z);
    ⊤
  )

  def SeqT : Id(Nat, let c = Z; let T = (c := S(Z); F(&c)); c, S(Z)) := refl

  -- A place holding a proof was once not treated as a proof, so a sequence ending in one
  -- was not erased, and at `n = Z` the match ran for real. Its arms write `c`, which
  -- confinement now rejects.
  reject def LieP (n : Nat) :
      Id(Nat, (let c = Z; let h : ⊤ = refl; let T = match n { Z => (c := S(Z); h), S _ => (c := S(Z); h) }; c), Z) := (
    refl
  )

  reject def BoomP : Eq(Nat, S(Z), Z) := LieP(Z)

  -- Whether a variable is a proof is read from its declaration, not from its value: `g(0)`
  -- is `⋆` at an instance but a sealed program at the generic call (D42, switch `leafRule`;
  -- appendix note 3).
  -- Rejected since D55: `V(Z)` is a type only by computation (its declared type `U(Z)` is not a sort).
  reject def LieH (g : Π(y : Nat). V(Z)) : Id(Nat, let c = Z; let h = g(0); (c := S(Z); h); c, S(Z)) := refl
  -- Rejected since D55: `V(Z)` is a type only by computation (its declared type `U(Z)` is not a sort).
  reject def BoomH : Eq(Nat, Z, S(Z)) := LieH(λ(y : Nat) : V(Z) => refl)

  -- The pre-pass reads a stuck block's captured proofs as proofs (fuzz-port's R8, true
  -- statements it once rejected with its INTERNAL check): a proof-function parameter, called
  -- on a sub-place; a captured λ into proofs; and a proof whose data field an arm writes
  -- inside a proof, which the block takes by value, never by `&` (D48 (1)).
  def R8Param (n : Nat) (h2 : Π(z0 : &Nat). ⊤) : Id(Nat, (match n { Z => 0, S p => h2(&p); 0 }), 0) := (
    match n { Z => refl, S _ => refl }
  )
  def R8Lam (n : Nat) :
      Id(Nat, (let a5 = (λ(y6 : Nat) (y7 : ⊤ ∧ ⊤) : ⊤ ∧ ⊤ => y7); match n { Z => 0, S p => a5(p, ⟨refl, refl⟩); 0 }), 0) := (
    match n { Z => refl, S _ => refl }
  )
  inductive ExN : Prop := Wit(n : Nat, e : ⊤)
  def R8Field (n : Nat) (h3 : ExN) :
      Id(Nat, (match n { Z => 0, S p => (match h3 { Wit(k, e) => k := 0; refl } : ⊤); 0 }), 0) := (
    match n { Z => refl, S _ => refl }
  )
  -- A match whose arms differ in class (a proof in one, data in another) has no declared type:
  -- a match's is each arm's, and they disagree. It is rejected wherever its declared type is
  -- read, in a type position ([Type-pos], `MixPos`) and by the erasure pre-pass (`R9Arms`,
  -- `R9Nested`), D63. The earlier reading (fuzz-port R9, switch `armsAgree`) let the arm that
  -- runs decide, which reads erasure off the scrutinee's value.
  -- (the proof arm is a proof variable, so the conflict does not depend on D42's reading of
  -- `refl`; fuzz-port R9's originals used `refl`)
  reject def R9Arms (h : ⊤) : Nat := (let n = 0; let a = match n { Z => h, S _ => 0 }; n)
  reject def R9Nested (n1 : Nat) (h : ⊤) : Nat := (let a = match n1 { Z => match n1 { Z => h, S p => 0 }, S p => h }; n1)
  reject def MixPos (h : ⊤) : Nat := (let n = 0; let x : (match n { Z => Nat, S _ => h }) = 5; x)
  -- ... and where it is written, dead arms included: typing checks only the arm a known
  -- scrutinee takes, but the machine reads the declared type of every term it runs, so
  -- `MixDead(0)` would fail when run (fuzz-port's execution oracle, seed 1, case 28948)
  reject def MixDead (n : Nat) (h : ⊤) : Nat := (match n { Z => match n { Z => 0, S _ => h }, S _ => 0 })

  -- Arms that are proofs of different shapes (a proof variable, a λ into proofs) agree on a proof.
  def RunP (k : Π(x : &Nat). ⊤) (x : &Nat) : Unit := (k(x); ())
  def R8Arms (n : Nat) (h0 : Π(z0 : &Nat). ⊤) (m : Nat) :
      Id(Unit, (match n { Z => RunP(match m { Z => h0, S _ => (λ(y2 : &Nat) : ⊤ => refl) }, &m), S _ => () }), ()) := (
    match n { Z => match m { Z => refl, S _ => refl }, S _ => refl }
  )
}

-- the exact number of declarations (a truncated file changes it)
#guard ErasureBySyntax.decls.length == 36
