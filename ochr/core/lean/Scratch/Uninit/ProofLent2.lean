import Ochr.Examples.«00Std»
open Ochr Ochr.Test
ochr ProofLent2 uses Std {
  def IsZ (n : Word) : Prop := (
    match n {
      Zero => ⊤,
      Succ(m) => False,
    }
  )
  inductive ZBox := MkZ(x : Word, h : IsZ(x))
  def Lie (b : &ZBox) : Unit := (
    match *b {
      MkZ(x, h) => (
        let h0 = h;
        let r = &x;
        h := h0;
        *r := Succ(Zero)
      ),
    }
  )
  def Boom : False := (
    let b = MkZ(Zero, refl);
    Lie(&b);
    match b {
      MkZ(x, h) => h,
    }
  )
  -- control: without re-assigning h, the write through r leaves h invalidated
  reject def NoReassign (b : &ZBox) : Unit := (
    match *b {
      MkZ(x, h) => (
        let r = &x;
        *r := Succ(Zero)
      ),
    }
  )
}
#eval (run "ProofLent2" ProofLent2).rows.map fun r => (r.name, r.verdict.ok)
