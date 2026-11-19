import Ochr.Examples.Nat
open Ochr.Test

-- census probes: each pair is a generic definition and a closed call of it
ochr CensusA uses Nats {
  def PickP (n : Nat) (x : &(Nat × Nat)) (y : &(Nat × Nat)) : &(Nat × Nat) := (
    match n { Z => x, S _ => y }
  )
  def Pick (n : Nat) (x : &Nat) (y : &Nat) : &Nat := ( match n { Z => x, S _ => y } )
  -- G1: a stuck block's by-move capture `a.0` generalises `a`'s fill, dropping r's hole
  def G1 (n : Nat) (k : Nat) (a : Nat × Nat) (b : Nat × Nat) : Unit := (
    let r = PickP(n, &a, &b);
    match k { Z => (let z = a.0; ()), S _ => () };
    *r := (Z, Z);
    ()
  )
  -- G2: a stuck block's & capture ends a borrower the running arm does not touch
  def G2 (k : Nat) (a : Nat) : Unit := (
    let r = &a;
    match k { Z => (a := 5; ()), S _ => () };
    *r := 3;
    ()
  )
  -- G3: a non-tail match returning a borrow
  def G3 (k : Nat) (a : Nat) (b : Nat) : Unit := (
    let r = match k { Z => &a, S _ => &b };
    let z = clone(a);
    *r := 5;
    ()
  )
  -- G4: tail match, the arm that runs uses r, the other ends it
  def G4 (k : Nat) (a : Nat) : Unit := (
    let r = &a;
    match k { Z => (a := 1; ()), S _ => (*r := 2; ()) }
  )
  -- G5: non-tail version of G4
  def G5 (k : Nat) (a : Nat) : Unit := (
    let r = &a;
    match k { Z => (a := 1; ()), S _ => (*r := 2; ()) };
    ()
  )
  -- G6: computed Pick, the result used after b is read
  def G6 (a : Nat) (b : Nat) : Unit := (
    let r = Pick(Z, &a, &b);
    let z = clone(b);
    *r := 5;
    ()
  )
  -- G7: reborrow through a returned borrow outlives it; reading a
  def G7 (n : Nat) (a : Nat) (b : Nat) : Unit := (
    let r = Pick(n, &a, &b);
    let s = &*r;
    let z = clone(b);
    *s := 4;
    ()
  )
  def G8 (n : Nat) (a : Nat) (b : Nat) : Unit := (
    let r = Pick(n, &a, &b);
    let s = &*r;
    let z = clone(a);
    *s := 4;
    ()
  )
}
ochr CensusB uses Nats, CensusA {
  def G1Run : Unit := G1(0, 1, (1, 2), (3, 4))
  def G2Run : Unit := G2(1, 0)
  def G3Run : Unit := G3(1, 0, 0)
  def G4Run : Unit := G4(1, 0)
  def G5Run : Unit := G5(1, 0)
  def G7Run0 : Unit := G7(0, 1, 2)
  def G7Run1 : Unit := G7(1, 1, 2)
  def G8Run0 : Unit := G8(0, 1, 2)
  def G8Run1 : Unit := G8(1, 1, 2)
}
