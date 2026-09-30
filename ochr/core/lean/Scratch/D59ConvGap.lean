import Ochr.Examples.«00Std»
open Ochr Ochr.Test
/-! Closed by D59 refined (η-normal forms at `Unit`, ochr-core-lean): the first two are accepted
now, and are `ClosingOff.StuckResultUnit`/`StuckResultArgs`. The original note follows.

D59 (η for `Unit`) moves a completeness gap rather than only closing one. Conversion has
no η for `Unit` (an abstract `u : Unit` is not `()`), and since D59 a stuck call written to
return `Unit` returns its sealed program instead of `()`. So a type that mentions such a
result is compared by that program: the three `reject`s below are true statements (`Unit`
has one value), rejected with D59 and accepted with it switched off. They are kept out of
the suite because each would flip to accepted in the D59 ledger row, whose class is
completeness. The first one's message prints the stuck call's result, the §2 display's
`⌈let c = σ; AddM(&c, 0)⌉`: "the goal is ⌈σ2(⌈let c1 = σ0; AddM(&c1, 0)⌉)⌉". -/
ochr D59ConvGap uses Std {
  def UU (n : Nat) : Type := (
    match n {
      Z => Unit,
      S _ => Unit,
    }
  )
  def StuckResultUnit (x : &Nat) (P : Unit → Prop) (h : P(())) : P(let c = *x; AddM(&c, 0)) := h
  def StuckResultArgs (x : &Nat) (P : Unit → Prop) (h : P(let c = *x; AddM(&c, 0))) : P(let c = *x; AddM(&c, 1)) := h
  -- (since D53 `let c = *x` moves `*x` out of the parameter, which then ends partly moved;
  -- with `clone(*x)` it is `ClosingOff.ConvUnitWritten`)
  reject def ConvUnitWrittenAddM :
      Eq (Π(x : &Nat). UU(Z)) (λ(x : &Nat) : UU(Z) => ()) (λ(x : &Nat) : UU(Z) => (let c = *x; AddM(&c, 0))) := (
    refl
  )
}
#eval IO.println (run "D59ConvGap" D59ConvGap).show
#eval IO.println (run "D59ConvGap" D59ConvGap { unitEta := false }).show
