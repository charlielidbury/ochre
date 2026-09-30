import Ochr.Examples.«00Std»
open Ochr Ochr.Test
/-! dep-fields, 2026-09-30: K4 as arrays-library §3 states it ("a field type may call an earlier
data-valued type function on parameters; positivity is unaffected, because the function was
declared earlier and cannot mention the type being declared") is not positive. The function
cannot mention `Bad`, but its *argument* can, through the parameter of the inductive that calls
it: `NBox(A)` has the field type `Neg(A)`, and `Bad` nests itself as `NBox(Bad)`, which D36
accepts as first-order syntax. Under D36 today only `NBox` is rejected; admit it and the rest is
the D36 attack, down to a closed `Boom : False`. -/
ochr K4Probe uses Std {
  inductive Void : Type
  def absurdV (v : Void) : False := match v {}
  def Neg (A : Type) : Type := Π(x : A). Void
  -- the K4 shape: a type function applied to a parameter
  reject inductive NBox (A : Type) := MkNBox(f : Neg(A))
  reject inductive Bad := MkBad(b : NBox(Bad))
  reject def L (x : Bad) : Void := (
    match x {
      MkBad(b) => match b {
        MkNBox(f) => f(x),
      },
    }
  )
  reject def K (x : Bad) : False := absurdV(L(x))
  reject def bad : Bad := MkBad(MkNBox[Bad](λ(y : Bad) : Void => L(y)))
  reject def Boom : False := K(bad)
}

#eval IO.println (run "K4Probe" K4Probe).show
#eval IO.println (run "K4Probe" K4Probe { positivity := false }).show
