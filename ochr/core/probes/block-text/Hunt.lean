import Ochr
open Ochr Ochr.Test

-- checker14: more shapes of stuck block (the extended hunt), verdicts and the values at every hole
ochr Hunt14 {
  inductive BB := TT | FF
  def F (n : Nat) : Nat := match n { Z => Z, S p => S(Z) }
  def Id1 (k : Nat) : Nat := k
  -- a block whose cell holds a sealed program (a stuck call's result)
  def SC (n : Nat) (m : Nat) : Nat := (let a = F(clone(n)); let r = (match m { Z => a, S q => Z }); match n { Z => ?, S p => ? })
  -- a block generalised by a split on its result, then a split on what it captured
  def GB (n : Nat) : Nat := (let r = (match n { Z => Z, S p => S(Z) }); match r { Z => match n { Z => ?, S q => ? }, S q => ? })
  -- the same text derived twice, generalised once
  def GB2 (n : Nat) : Nat := (let r = (match n { Z => Z, S p => S(Z) }); let s = (match n { Z => Z, S p => S(Z) }); match r { Z => ?, S q => ? })
  -- a block capturing a proof that a λ in an arm captures
  def PB (n : Nat) (h : Eq(Nat, n, n)) : Nat := (let r = (match n { Z => (let f = (λ(k : Nat) : Nat => (h; k)); f(Z)), S p => S(Z) }); match n { Z => ?, S q => ? })
  -- a block splitting a captured pair (an arm moves one field out)
  def SP (q : Nat × Nat) (m : Nat) : Nat := (let r = (match m { Z => (let a = q.0; a), S j => clone(q.1) }); match m { Z => ?, S j => ? })
  -- two blocks with the same text compared, and with different texts
  def EqSame (n : Nat) : Eq(Nat, (let r = (match n { Z => Z, S p => S(Z) }); r), (let r = (match n { Z => Z, S p => S(Z) }); r)) := refl
  reject def EqDiff (n : Nat) : Eq(Nat, (let r = (match n { Z => Z, S p => S(Z) }); r), (let r = (match n { Z => Z, S p => clone(p) }); r)) := refl
  -- two J blocks whose motives are convertible closures of different code
  def EqJ (a : Nat) (b : Nat) (h : Eq(Nat, a, b)) : Eq(Nat, J(Nat, a, b, λ(z : Nat) : Type => Nat, h, Z), J(Nat, a, b, λ(z : Nat) : Type => (let w = Nat; w), h, Z)) := refl
  -- a block in a type position (a type-valued block) used as a binder's type
  def TB (m : Nat) (x : (let t = (match m { Z => Nat, S q => Nat }); t)) : Nat := Z
  -- a block whose arm holds an `Id` over a stuck match on one of its cells: on a re-run the side
  -- is split and closed off as a block of its own, inside the outer block's run
  def BI (n : Nat) (m : Nat) : Nat := (let r = (match n { Z => (let h : Id(Nat, match m { Z => Z, S q => S(Z) }, Z) = ?; Z), S p => Z }); match n { Z => ?, S p => ? })
  -- a block capturing a λ that calls the function under check (the λ is the program's, not the block's)
  def CL (m : Nat) (n : Nat) : Nat by n := match n { Z => Z, S k => (let g = (λ(j : Nat) : Nat => CL(j, clone(k))); let r = (match m { Z => g(Z), S q => Z }); ?) }
  -- a block moving whole the borrow variables it returns, written through, then split
  def BRm (b : BB) (x : &Nat) (y : &Nat) : Nat := (let r = (match b { TT => x, FF => y }); *r := Z; match b { TT => ?, FF => ? })
  -- a block moving whole a borrow variable declared `&Unit`: the fill of its lent place is `()`
  def BUF (n : Nat) (x : &Unit) : Unit := (let r = (match n { Z => (let y = x; ()), S p => () }); ?)
  def BUN (n : Nat) (x : &Nat) : Unit := (let r = (match n { Z => (let y = x; ()), S p => () }); ?)
  -- a block inside a λ inside a recursive function, calling it through the λ's capture of it
  def LB (m : Nat) (n : Nat) : Nat by n := match n { Z => Z, S k => (let g = (λ(j : Nat) : Nat => (let r = (match j { Z => LB(j, clone(k)), S q => Z }); r)); g(m)) }
  def LBh (m : Nat) (n : Nat) : Nat by n := match n { Z => Z, S k => (let g = (λ(j : Nat) : Nat => (let r = (match j { Z => LBh(j, clone(k)), S q => Z }); ?)); g(m)) }
  -- a J block whose transported term calls the function under check
  def JR (a : Nat) (b : Nat) (h : Eq(Nat, a, b)) (n : Nat) : Nat by n := match n { Z => Z, S k => (let r = J(Nat, a, b, λ(z : Nat) : Type => Nat, h, JR(a, b, h, k)); ?) }
  -- a block in a side of Id
  def IdB (n : Nat) (x : &Nat) : Prop := Id(Unit, match n { Z => *x := Z, S p => () }, match n { Z => *x := Z, S p => () })
  def IdBHolds (n : Nat) (x : &Nat) : IdB(n, x) := refl
  -- a block re-run where its cell is a borrow whose content a split refines
  def BX (x : &Nat) (m : Nat) : Nat := (let r = (match m { Z => clone(*x), S q => Z }); match *x { Z => ?, S p => ? })
  -- a block inside a λ (captures of the λ's frame), re-run
  def BIL (n : Nat) : Nat := (let g = (λ(k : Nat) : Nat => (let r = (match k { Z => Z, S p => clone(p) }); r)); g(n))
  -- a block whose arm calls a global with a borrow of a captured place
  def AddOne (x : &Nat) : Unit := (*x := S(clone(*x)); ())
  def BC (n : Nat) (x : &Nat) : Nat := (let r = (match n { Z => (AddOne(&*x); Z), S p => Z }); match n { Z => ?, S q => ? })
  -- a nested block whose inner match is on a place the outer block took by borrow
  def NB (n : Nat) (m : Nat) (x : &Nat) : Nat := (let r = (match n { Z => (let s = (match m { Z => (*x := Z; Z), S q => Z }); s), S p => Z }); match n { Z => match m { Z => ?, S q => ? }, S p => ? })
}

#eval show IO Unit from do
  let r := runWith (some Prelude) "Hunt14" Hunt14 {} 2000000 (located := true)
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
