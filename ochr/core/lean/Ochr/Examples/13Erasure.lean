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

  def TypeErased (x : &Nat) : Id Nat (let T = F5(&*x); *x) (*x) := refl

  -- A proof's argument runs on the copy as well, so `W5`'s write inside it is not seen ...
  def Lemma (u : Unit) : ⊤ := refl
  def W5 (x : &Nat) : Unit := *x := 5
  reject def EffArg (x : &Nat) : Id Unit (Lemma(W5(&*x)); ()) (*x := 5) := refl

  -- ... and since the argument writes `*x` for a call that is not erased, confinement makes
  -- it an error rather than a silent no-op.
  reject def EffArgErased (x : &Nat) : Id Unit (Lemma(W5(&*x)); ()) () := refl

  -- ## Confinement
  -- A proof may change its own locals ...
  def Local (x : &Nat) : Nat := (
    let h : ⊤ = (let y = 0; y := 1; refl);
    *x
  )

  -- ... and hand an outer place to another proof (as `AddMZero`'s recursive call does) ...
  def Pass (x : &Nat) : Nat := (
    let h = AddMZero(&*x);
    *x
  )

  -- ... but may not write, borrow or move one itself.
  reject def Write (x : &Nat) : Nat := (
    let h : ⊤ = (*x := 5; refl);
    *x
  )

  reject def Borrow (x : &Nat) : Nat := (
    let h : ⊤ = (AddM(&*x, 0); refl);
    *x
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

  def F (h : Π(x : &Nat). ⊤) : Prop := Id Nat (let a = 0; h(&a); a) 0
  def FP2 : Id Nat (let a = 0; P2(&a); a) 0 := refl

  def BoomIsTrue : ⊤ := (
    J(Π(x : &Nat). ⊤, P1, P2, λ(g : Π(x : &Nat). ⊤) : Prop => F(g), (refl : Eq (Π(x : &Nat). ⊤) P1 P2), refl)
  )

  -- ... and transporting along `P1 = P2` gives no proof of `False`.
  reject def Boom : False := (
    J(Π(x : &Nat). ⊤, P1, P2, λ(g : Π(x : &Nat). ⊤) : Prop => F(g), (refl : Eq (Π(x : &Nat). ⊤) P1 P2), refl)
  )

  -- The same through a function that runs its argument on a local: `k(P1)` and `k(P2)` are
  -- both `0`.
  reject def Boom' : Eq Nat 0 1 := (
    (λ(k : Π(h : Π(x : &Nat). ⊤). Nat) : Eq Nat (k(P1)) (k(P2)) => refl)(
      λ(h : Π(x : &Nat). ⊤) : Nat => (let a = 0; h(&a); a)
    )
  )

  -- The same inside a stuck match: sealing `UseP(p2, &c, n)` and then refining `n`, or running
  -- it directly, both leave `c` at `0`.
  def p1 (x : &Nat) : Eq Nat 0 0 := refl

  def p2 (x : &Nat) : Eq Nat 0 0 := (
    *x := S Z;
    refl
  )

  def UseP (h : Π(x : &Nat). Eq Nat 0 0) (x : &Nat) (n : Nat) : Unit := (
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

  def TA2 (n : Nat) : Id Nat (let c = 0; UseP(p1, &c, n); c) (let c = 0; UseP(p2, &c, n); c) := refl
  reject def TA2Z : Eq Nat 0 1 := TA2(0)

  -- ## What goes wrong without confinement
  -- A match whose arms are proofs that write `a`. An earlier version erased it when it was
  -- closed off but ran it when it ran directly, so sealing then refining gave `0` and running
  -- directly gave `1`: `N1Closed` proved `1 = 0`. With the private copy both give `0`; with
  -- confinement, a proof that writes `a` is an error. Switching both off accepts `N1Closed`
  -- and `QBoom` (switches `eraseOnCopy` and `confine`).
  reject def N1T (n : Nat) :
      Id Nat (let a = 0; let h = match n { Z => (a := S Z; refl), S _ => refl }; a) 0 := refl

  reject def N1Closed : Id Nat 1 0 := N1T(0)

  reject def Q (b : Nat) (a : Nat) :
      Id ⊤ (match b { Z => (a := S Z; refl), S _ => (a := S Z; refl) }) refl := refl

  reject def QBoom : False := (
    J(Nat, S Z, Z, λ(n : Nat) : Prop => match n { Z => False, S _ => ⊤ }, Q(0, 0), refl)
  )
}

#eval IO.println (run "Erasure" Erasure).show

-- every verdict as expected, and the exact number of declarations (a truncated file changes it)
#guard (run "Erasure" Erasure).allAsExpected
#guard (run "Erasure" Erasure).count == 29

/-! ## What goes wrong when erasure is decided from values

Each program below makes the two ways of computing a statement disagree about whether some
term is erased, if that is decided from a computed value instead of the syntax. `Std`'s `U(n)` is
`Prop` for every `n`, but only after computing it: at an abstract `n` it is the stuck
`⌈U(σ)⌉`. `V(n)` is a proof of `U(n)`. Each `Lie…` is a statement about whether a write to
`c` happens, and each `Boom…` its instance at `Z`. If the generic call and the instance
disagreed about whether the write is erased, some `Boom…` would be a closed proof of a
false equation. Under the rules the write happens on both paths, so each `Lie…` is either
true, with a true instance, or rejected. The ledger names the switch each one depends on. -/

ochr ErasureBySyntax uses Std {
  -- A top-level function whose result type computes to a sort (D28, switch `erasureByDecl`).
  -- `W` returns data, by its declared result type `U(n)`, so its write runs at every
  -- instance; `MainW(0)` really is `1`, as compiled code computes.
  def W (x : &Nat) (n : Nat) : U(n) := (
    *x := S Z;
    V(n)
  )

  def Lie (n : Nat) : Id Nat (let c = Z; W(&c, n); c) (S Z) := refl
  reject def Boom : Eq Nat Z (S Z) := Lie(Z)

  def MainW (n : Nat) : Nat := (
    let c = Z;
    W(&c, n);
    c
  )

  def MainW0 : Id Nat (MainW(0)) 1 := refl

  -- A local function whose result type computes to a sort: its class is read from the
  -- result type as written, `U(n)`, so `h(&c)` runs on both paths (D35, switch
  -- `classBySyntax`; appendix note 1).
  def LieL (n : Nat) :
      Id Nat (let h = (λ(x : &Nat) : U(n) => (*x := S Z; V(n))); let c = Z; h(&c); c) (S Z) := refl

  reject def BoomL : Eq Nat Z (S Z) := LieL(Z)

  -- The same, with the closure made by a top-level function.
  def Mk (n : Nat) : (Π(x : &Nat). U(n)) := λ(x : &Nat) : U(n) => (*x := S Z; V(n))
  def Lie8 (n : Nat) : Id Nat (let c = Z; let g = Mk(n); g(&c); c) (S Z) := refl
  reject def Boom8 : Eq Nat Z (S Z) := Lie8(Z)
  reject def Direct8 : Id Nat (let c = Z; let g = Mk(0); g(&c); c) Z := refl

  -- A match whose value is a type. Closed off, it looked like a call returning types and
  -- was erased; run directly, it was not. A closed-off match is erased only when each of
  -- its arms is (D35, D40, switch `blockRule`; appendix note 2). The true statement is
  -- proved by splitting on `n`.
  reject def LieB (n : Nat) :
      Id Nat (let c = Z; let T = match n { Z => (c := S Z; ⊤), S _ => (c := S Z; ⊤) }; c) Z := refl

  reject def BoomB : Eq Nat (S Z) Z := LieB(Z)

  def TruthB (n : Nat) :
      Id Nat (let c = Z; let T = match n { Z => (c := S Z; ⊤), S _ => (c := S Z; ⊤) }; c) (S Z) := (
    match n {
      Z => refl,
      S _ => refl,
    }
  )

  -- The same with an annotation: the type `Prop` is not a proposition, so the match is not
  -- erased on either path; and with a data annotation the write is kept.
  reject def Lie7 (n : Nat) :
      Id Nat (let c = Z; let T : Prop = match n { Z => (c := S Z; ⊤), S _ => (c := S Z; ⊤) }; c) Z := refl

  reject def Boom7 : Eq Nat (S Z) Z := Lie7(Z)

  reject def P3d (n : Nat) : Nat := (
    let c = Z;
    let T : Nat = match n {
      Z => (
        c := S Z;
        0
      ),
      S _ => (
        c := S Z;
        0
      ),
    };
    let h : Id Nat c Z = refl;
    c
  )

  -- A closed-off match erased because its computed type is a proposition disagrees with the
  -- direct path, where `f`'s calls are classed by syntax: `V(Z)` computes to `⊤` but is not
  -- declared a proposition, so `f(&c)` runs.
  reject def LieG (m : Nat) (g : Π(y : Nat). V(Z)) :
      Id Nat
        (
          let c = Z;
          let f = (λ(x : &Nat) : V(Z) => (*x := S Z; g(0)));
          let T = match m { Z => f(&c), S _ => f(&c) };
          c
        )
        Z := (
    refl
  )

  reject def BoomG : Eq Nat (S Z) Z := LieG(Z, λ(y : Nat) : V(Z) => refl)

  def TruthG (m : Nat) (g : Π(y : Nat). V(Z)) :
      Id Nat
        (
          let c = Z;
          let f = (λ(x : &Nat) : V(Z) => (*x := S Z; g(0)));
          let T = match m { Z => f(&c), S _ => f(&c) };
          c
        )
        (S Z) := (
    match m {
      Z => refl,
      S _ => refl,
    }
  )

  -- A sequence whose tail returns a type is not erased; only the call `F(&c)` runs on a
  -- private copy (switch `seqByProof`).
  def F (x : &Nat) : Prop := (
    *x := S Z;
    ⊤
  )

  def SeqT : Id Nat (let c = Z; let T = (c := S Z; F(&c)); c) (S Z) := refl

  -- A place holding a proof was once not treated as a proof, so a sequence ending in one
  -- was not erased, and at `n = Z` the match ran for real. Its arms write `c`, which
  -- confinement now rejects.
  reject def LieP (n : Nat) :
      Id Nat
        (let c = Z; let h : ⊤ = refl; let T = match n { Z => (c := S Z; h), S _ => (c := S Z; h) }; c)
        Z := (
    refl
  )

  reject def BoomP : Eq Nat (S Z) Z := LieP(Z)

  -- Whether a variable is a proof is read from its declaration, not from its value: `g(0)`
  -- is `⋆` at an instance but a sealed program at the generic call (D42, switch `leafRule`;
  -- appendix note 3).
  def LieH (g : Π(y : Nat). V(Z)) : Id Nat (let c = Z; let h = g(0); (c := S Z; h); c) (S Z) := refl
  reject def BoomH : Eq Nat Z (S Z) := LieH(λ(y : Nat) : V(Z) => refl)
}

#eval IO.println (run "ErasureBySyntax" ErasureBySyntax).show

-- every verdict as expected, and the exact number of declarations (a truncated file changes it)
#guard (run "ErasureBySyntax" ErasureBySyntax).allAsExpected
#guard (run "ErasureBySyntax" ErasureBySyntax).count == 26
