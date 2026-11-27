import Ochr
open Ochr Ochr.Test

-- checker14: the shapes of stuck block, verdicts and the values at every hole
ochr Blk14 {
  inductive BB := TT | FF
  -- the four faults
  def MB0r (m : Nat) (n : Nat) : Nat by n := (let r = (match m { Z => Z, S p => match n { Z => Z, S k => MB0r(p, k) } }); r)
  def MB0 (m : Nat) (n : Nat) : Nat by n := (let r = (match m { Z => Z, S p => match n { Z => Z, S k => MB0(p, k) } }); ?)
  def NTr (n : Nat) (m : Nat) : Nat := match n { Z => Z, S p => (let r = (match m { Z => clone(n), S q => clone(p) }); r) }
  def NT (n : Nat) (m : Nat) : Nat := match n { Z => Z, S p => (let r = (match m { Z => clone(n), S q => clone(p) }); ?) }
  -- the neighbours
  def MB (m : Nat) (n : Nat) : Nat by n := match n { Z => Z, S k => (let r = (match m { Z => MB(Z, k), S p => MB(S(Z), k) }); ?) }
  def TBB (b : BB) (x : &Nat) : &Nat by x := match *x { Z => x, S p => (let r = (match b { TT => TBB(TT, &p), FF => TBB(FF, &p) }); ?) }
  def NU (n : Nat) (m : Nat) : Nat := match n { Z => Z, S p => (let r = (match m { Z => (n := Z; Z), S q => clone(p) }); ?) }
  def RB (n : Nat) (k : Nat) : Nat by n := match n { Z => Z, S m => (let r = (match k { Z => RB(m, Z), S j => Z }); match k { Z => (let u = r; ?), S j => (let u = r; ?) }) }
  -- a block returning a borrow (a reborrow of either argument), written through, then a split
  def BR (b : BB) (x : &Nat) (y : &Nat) : Nat := (let r = (match b { TT => &*x, FF => &*y }); *r := Z; match b { TT => ?, FF => ? })
  def BR0 (b : BB) (x : &Nat) (y : &Nat) : Nat := (let r = (match b { TT => &*x, FF => &*y }); ?)
  -- a block whose arm ends stuck again after a later split
  def BS (n : Nat) (m : Nat) : Nat := (let r = (match n { Z => Z, S p => match m { Z => Z, S q => S(q) } }); match n { Z => ?, S p => ? })
  -- a block inside a block
  def BB2 (n : Nat) (m : Nat) : Nat := (let r = (match n { Z => Z, S p => (let s = (match m { Z => Z, S q => clone(q) }); S(s)) }); ?)
  def BB2s (n : Nat) (m : Nat) : Nat := (let r = (match n { Z => Z, S p => (let s = (match m { Z => Z, S q => clone(q) }); S(s)) }); match n { Z => ?, S p => match m { Z => ?, S q => ? } })
  -- a block re-run after a later split refines what it captured
  def RR (n : Nat) : Nat := (let r = (match n { Z => Z, S p => clone(p) }); match n { Z => ?, S q => ? })
  -- a block taking a place by borrow (an arm writes it), re-run after a split
  def BW (n : Nat) (x : &Nat) : Nat := (let r = (match n { Z => (*x := Z; Z), S p => (*x := S(Z); clone(p)) }); match n { Z => ?, S q => ? })
  -- a J block
  def JB (a : Nat) (b : Nat) (h : Eq(Nat, a, b)) : Nat := (let r = J(Nat, a, b, λ(z : Nat) : Type => Nat, h, Z); ?)
  def JBs (a : Nat) (b : Nat) (h : Eq(Nat, a, b)) : Nat := (let r = J(Nat, a, b, λ(z : Nat) : Type => Nat, h, S(Z)); match a { Z => match b { Z => ?, S q => ? }, S p => ? })
  -- a block capturing by borrow a place an erased term in an arm assigns
  def BE (m : Nat) : Nat := (let x = Z; let r = (match m { Z => (let h : Eq(Nat, (x := S(Z); clone(x)), S(Z)) = refl; Z), S q => Z }); ?)
  -- a block whose arm calls a λ formed outside it, and one forming a λ inside
  def BL (m : Nat) : Nat := (let f = (λ(k : Nat) : Nat => S(k)); let r = (match m { Z => f(Z), S q => f(q) }); ?)
  def BLi (m : Nat) (n : Nat) : Nat := (let r = (match m { Z => (let g = (λ(k : Nat) : Nat => S(k)); g(n)), S q => Z }); ?)
  -- a block in a recursive function whose arm forms a λ that calls the function
  def BLR (m : Nat) (n : Nat) : Nat by n := match n { Z => Z, S k => (let r = (match m { Z => (let g = (λ(j : Nat) : Nat => BLR(j, clone(k))); g(Z)), S q => Z }); ?) }
  -- a stuck block at type Unit, and at a type of sort Prop's neighbour (a type-valued block)
  def BU (m : Nat) (x : &Nat) : Unit := (let r = (match m { Z => (*x := Z; ()), S q => () }); ?)
  def BT (m : Nat) : Type := (let r = (match m { Z => Nat, S q => Unit }); r)
}

#eval show IO Unit from do
  let r := runWith (some Prelude) "Blk14" Blk14 {} 2000000 (located := true)
  for row in r.rows do
    let v := match row.verdict with
      | .accepted => "accepted"
      | .rejected m _ => s!"rejected: {m}"
      | .undecided m => "undecided: " ++ m
    IO.println s!"ROW {row.name}: {v}"
    let mut k := 0
    for e in row.trace do
      match e with
      | .note _ _ (.hole _ Ω) =>
        k := k + 1
        for (x, _, val) in Ω do
          IO.println s!"  hole{k} {x} ↦ {val}"
      | _ => pure ()
