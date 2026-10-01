import Ochr.Examples.«00Std»
open Ochr Ochr.Test
/-! Probe: a proof field re-assigned while a borrow of the field it mentions is live and returned. -/
ochr ProofLent uses Std {
  def IsZ (n : Word) : Prop := (
    match n {
      Zero => ⊤,
      Succ(m) => False,
    }
  )
  inductive ZBox := MkZ(x : Word, h : IsZ(x))
  def GetX (b : &ZBox) : &Word := (
    match *b {
      MkZ(x, h) => (
        let h0 = h;
        let r = &x;
        h := h0;
        r
      ),
    }
  )
  def Break (b : &ZBox) : Unit := (
    let r = GetX(b);
    *r := Succ(Zero)
  )
  def Boom : False := (
    let b = MkZ(Zero, refl);
    Break(&b);
    match b {
      MkZ(x, h) => h,
    }
  )
}
#eval (run "ProofLent" ProofLent).rows.map fun r => (r.name, r.verdict.ok)
