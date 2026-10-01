import Ochr.Examples.«00Std»
open Ochr Ochr.Test
/-! Probe (meta-order, 2026-09-30; typed-fragment plan, risk R3): the footprint of an `Id`
through a returned borrow is larger on the symbolic path than at a ground instance, and the
extra conjuncts are harmless.

`r = Pick(n, &a, &b)` at an abstract `n` has its hole in the fills of both `a` and `b`, so the
type of `Probe`'s `e` at `z = r` is a conjunction over the owners `{a, b}` (`UseSym`). At
`n = 0` it is the one equation over `{a}`, which is `False` (`UseZero`), and it is the same
when `n` is refined before the type is formed (`UseArm`). When the type is formed at the
abstract `n` and refined afterwards (`PreFormed`), the extra conjunct over `b` becomes `⊤`:
in the refined state `b`'s fill no longer contains the hole, so both sides leave `b` with the
same normal form. `False ∧ ⊤` is convertible with `False` by `And`'s unit laws (D50).

So @lem-stable's item (2) is false as literally stated ("the places of each footprint are the
same"). What holds is: the footprint formed at Ω contains the one formed at Ωα, and each
extra place's conjunct refines to `⊤`, so the two types are convertible. Not a soundness
lead: the symbolic type is the stronger one, and after refinement it is convertible with the
ground one. -/
ochr FootprintProbe uses Fixtures {
  def Probe (z : &Nat) (e : Id(Unit, *z := 0, *z := 1)) : Unit := ()
  -- formed at an abstract n: owners of r = {a, b}
  reject def UseSym (n : Nat) (a : Nat) (b : Nat) : Unit := (
    let r = Pick(n, &a, &b);
    Probe(r, refl)
  )
  -- formed at n = 0: owners of r = {a}
  reject def UseZero (a : Nat) (b : Nat) : Unit := (
    let r = Pick(0, &a, &b);
    Probe(r, refl)
  )
  -- formed after refining n := Z inside the arm
  reject def UseArm (n : Nat) (a : Nat) (b : Nat) : Unit := (
    let r = Pick(clone(n), &a, &b);
    match n {
      Z => Probe(r, refl),
      S _ => (),
    }
  )
  -- formed at an abstract n, then refined in the arms (annotated block)
  reject def PreFormed (n : Nat) (a : Nat) (b : Nat) : Unit := (
    let r = Pick(clone(n), &a, &b);
    let e : Id(Unit, *r := 0, *r := 1) = match n {
      Z => refl,
      S _ => refl,
    };
    ()
  )
  -- a true lemma about writes through a borrow
  def Same (z : &Nat) : Id(Unit, *z := 1; *z := 0, *z := 0) := refl
  -- its result at a call site with an abstract n has a conjunct per owner; the b conjunct
  -- is used below as a fact
  def Keep (n : Nat) (a : Nat) (b : Nat) : Unit := (
    let r = Pick(n, &a, &b);
    let h = Same(r);
    ()
  )
  -- a lemma whose two sides leave different (abstract) contents behind the borrow
  def Reset (z : &Nat) (h : Eq(Nat, *z, 0)) : Id(Unit, *z := 0, ()) := (
    rewrite h in refl
  )
  -- its hypothesis and result at a call site with an abstract n: one conjunct per owner
  reject def ResetShow (n : Nat) (a : Nat) (b : Nat) (h : Eq(Nat, a, 0)) : False := (
    let r = Pick(n, &a, &b);
    Reset(r, h)
  )
  -- the same at n = 0
  reject def ResetShowZero (a : Nat) (b : Nat) (h : Eq(Nat, a, 0)) : False := (
    let r = Pick(0, &a, &b);
    Reset(r, h)
  )
}
#eval IO.println (run "FootprintProbe" FootprintProbe).show
#guard (run "FootprintProbe" FootprintProbe).allAsExpected
#guard (run "FootprintProbe" FootprintProbe).count == 10
