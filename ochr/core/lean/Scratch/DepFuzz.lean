import Ochr.Test
open Ochr Ochr.Test
/-! Dependent fields (D64, dep-fields 7d3d21e9): closed proofs of `False` found by the fuzzer's
`--dep` family. Each `Lie…` breaks the dependency of `DV := MkDV(n : Nat, x : Fin1(n))`; `AbsurdDV` is true of every
packed `DV`. Verdicts as they stand on dep-fields 7d3d21e9: `Lie0`/`Boom0`, `Lie0R`/`Boom0R`, `LieK`/`BoomK`
and `LieR2`/`BoomR2` are accepted (the bugs; (0) is the root, the rest are variants of it),
`LieK1` and `LieR` are rejected as they should be. When fixed, the eight become `reject`. -/
ochr DepFuzz {
  inductive Empty0 : Type
  inductive One := O
  def Fin1 (n : Nat) : Type := match n { Z => Empty0, S _ => One }
  inductive DV := MkDV(n : Nat, x : Fin1(n))
  def DVN (v : DV) : Nat := match v { MkDV(n, x) => n }
  def AbsurdDV (v : DV) (h : Eq Nat (DVN(v)) 0) : False := match v { MkDV(n, x) => match n { Z => match x {}, S m => match h {} } }
  -- (0) the root, in either order: once the dependent field is assigned, the value is
  -- accepted as repacked whatever the index says (the same with `Word` and the tour's `V`)
  def Lie0 (v : &DV) : Unit := match *v { MkDV(n, x) => (n := 0; x := O) }
  def Boom0 : False := AbsurdDV((let v = MkDV(1, O); Lie0(&v); v), refl)
  def Lie0R (v : &DV) : Unit := match *v { MkDV(n, x) => (x := O; n := 0) }
  def Boom0R : False := AbsurdDV((let v = MkDV(1, O); Lie0R(&v); v), refl)
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
