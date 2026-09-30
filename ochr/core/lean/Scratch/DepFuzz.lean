import Ochr.Test
open Ochr Ochr.Test
/-! Dependent fields (D64, dep-fields 7d3d21e9): closed proofs of `False` found by the fuzzer's
`--dep` family. Each `Lie…` breaks the dependency of `DV := MkDV(n : Nat, x : Fin1(n))`; `AbsurdDV` is true of every
packed `DV`. Verdicts as they stand on dep-fields 7d3d21e9: `LieK`/`BoomK` and `LieR2`/`BoomR2`
are accepted (the bugs), `LieK1` and `LieR` are rejected as they should be. When fixed, the
four become `reject`. -/
ochr DepFuzz {
  inductive Empty0 : Type
  inductive One := O
  def Fin1 (n : Nat) : Type := match n { Z => Empty0, S _ => One }
  inductive DV := MkDV(n : Nat, x : Fin1(n))
  def DVN (v : DV) : Nat := match v { MkDV(n, x) => n }
  def AbsurdDV (v : DV) (h : Eq Nat (DVN(v)) 0) : False := match v { MkDV(n, x) => match n { Z => match x {}, S m => match h {} } }
  -- (1) an index set to a parameter, then the dependent field assigned at the index's stuck type
  def LieK (v : &DV) (k : Nat) : Unit := match *v { MkDV(n, x) => (n := k; x := O) }
  def BrokenK : DV := (let v = MkDV(1, O); LieK(&v, 0); v)
  def BoomK : False := AbsurdDV(BrokenK, refl)
  -- (1') the index alone set to a parameter: the field keeps its old value
  reject def LieK1 (v : &DV) (k : Nat) : Unit := match *v { MkDV(n, x) => n := k }
  reject def BoomK1 : False := AbsurdDV((let v = MkDV(1, O); LieK1(&v, 0); v), refl)
  -- (2') the dependent field assigned first, then the index written through a borrow
  def LieR2 (v : &DV) : Unit := match *v { MkDV(n, x) => (x := O; let r = &n; *r := 0) }
  def BoomR2 : False := AbsurdDV((let v = MkDV(1, O); LieR2(&v); v), refl)
  -- (2) the index written through a borrow of the field
  reject def LieR (v : &DV) : Unit := match *v { MkDV(n, x) => (let r = &n; *r := 0) }
  reject def BrokenR : DV := (let v = MkDV(1, O); LieR(&v); v)
  reject def BoomR : False := AbsurdDV(BrokenR, refl)
}
#eval IO.println (run "DepFuzz" DepFuzz).show
