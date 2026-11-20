import Ochr.Examples.Registry

/-!
# Probes for `lake exe sweep --probes` (DEV TOOLING)

Not part of the checker, of the suite's verdict count or of the artefact: programs written to
make the premise of a `Good` clause arise, so that the sweep (`Sweep.lean`) tests the clause on
states where it says something. `lake exe sweep --probes` checks these blocks with the states
recorded and prints the clauses' premise counts and violations. The `ochr` command asserts each
verdict when this module is built, like the suite's.

## (WF12): a live borrow's site strictly under another live borrow's fill

Across the whole suite, the premise of (WF12) never arises: a live fill exists in 1,786 states,
but no state has a live site strictly under another live borrow's fill. These programs try to
make it arise. Each is written with the code in the declaration's own body, since the sweep only
records states at call depth 0. That means a closed body for the runs at known values, and a body
with parameters for the generic call. The programs take returned borrows of parts, reborrow parts
through a returned borrow, end the two in each order, nest calls that return borrows of a
borrow's content, return a borrow from a stuck block, a stuck call and a `J` whose places are
already lent, and assign through a returned borrow while a part of it is reborrowed.

What the runs show (`lake exe sweep --probes`, after D93). In 224 of their 538 states a live fill
exists. In 18 of them another live borrow has a site at the position of a live fill (`TwoParts`,
accepted since D93: two disjoint parts of a returned borrow's place lent onward), in 3 at the same
path, never strictly below it; in the suite's 1,825 states with a live fill, none. The premise
of (WF12) does not arise. A fill has nothing of another borrow below it for two reasons. First, a returned borrow's mark wraps the whole place it is lent, with the reborrow's
loan inside it: after `let a = (let r = Whole(&c); &(*r).0)` the state is
`c = lent_3 (loan_3, 2), a = borrow_3 1`. Second, when the returned borrow ends, its mark passes to
the borrow its content was lent onward to, at the same place. Putting another borrow's site below
a live mark needs an access through the mark, and that access ends the mark's borrow first (D90).
Lending a place whole that already has a borrowed part needs an access of the place, and that
access ends the part's borrow. A sealed fill has no path below it.
-/

open Ochr

ochr LentUnder uses Nats, Fixtures {
  def Whole (x : &(Nat × Nat)) : &(Nat × Nat) := x
  def Fst (x : &(Nat × Nat)) : &Nat := &(*x).0
  def IdN (x : &Nat) : &Nat := x
  def PickP (n : Nat) (x : &(Nat × Nat)) (y : &(Nat × Nat)) : &(Nat × Nat) := (match n { Z => x, S _ => y })
  def MN (z : Nat) : Type := Nat
  -- a reborrow of a part through a returned borrow; the returned borrow ends first (dropped at
  -- its block's end, the reborrow escaping), then the reborrow
  def OuterFirst : Nat × Nat := (
    let c = (1, 2);
    let a = (let r = Whole(&c); &(*r).0);
    *a := 3;
    let d = c; d)
  def OuterFirstG (c : Nat × Nat) : Nat × Nat := (
    let a = (let r = Whole(&c); &(*r).0);
    *a := 3;
    let d = c; d)
  -- ... the reborrow ends first (an access of the returned borrow's content)
  def InnerFirst : Nat × Nat := (
    let c = (1, 2);
    let r = Whole(&c);
    let a = &(*r).0;
    *a := 3;
    let z = clone(*r);
    let d = c; d)
  -- nested calls: a returned borrow of a part of a returned borrow's content
  def Nested : Nat × Nat := (
    let c = (1, 2);
    let a = (let r = Whole(&c); Fst(&*r));
    *a := 3;
    let d = c; d)
  def NestedG (c : Nat × Nat) : Nat × Nat := (
    let a = (let r = Whole(&c); Fst(&*r));
    *a := 3;
    let d = c; d)
  def NestedPart : Nat × Nat := (
    let c = (1, 2);
    let a = (let r = Whole(&c); IdN(&(*r).1));
    *a := 3;
    let d = c; d)
  -- two borrows of disjoint parts through one returned borrow, live together (Rust accepts;
  -- rejected before D93, when a borrow of a part ended the borrows of its siblings)
  def TwoParts : Nat × Nat := (
    let c = (1, 2);
    let e = (0, 0);
    let r = Whole(&c);
    let a = IdN(&(*r).0);
    let b = &(*r).1;
    *a := 3;
    *b := 4;
    r := &e;
    let d = c; d)
  -- the returned borrow overwritten while a reborrow of its part is live
  def Overwritten : Nat × Nat := (
    let c = (1, 2);
    let e = (0, 0);
    let r = Whole(&c);
    let a = IdN(&(*r).0);
    r := &e;
    let d = c; d)
  -- a stuck call over a returned borrow's part
  def StuckCall (n : Nat) (c : Nat × Nat) (y : Nat) : Nat × Nat := (
    let a = (let r = Whole(&c); Pick(n, &(*r).0, &y));
    *a := 3;
    let d = c; d)
  -- a stuck block returning a borrow of a captured place that is itself lent
  def StuckBlock (k : Nat) (c : Nat) (e : Nat) : Nat := (
    let s = (let r = IdN(&c); match k { Z => &*r, S _ => &e });
    *s := 7;
    let d = c; d)
  def StuckBlockRun : Nat := (
    let c = 1; let e = 2; let k = 1;
    let s = (let r = IdN(&c); match k { Z => &*r, S _ => &e });
    *s := 7;
    let d = c; d)
  -- the same through `J`
  def StuckJ (m : Nat) (h : Eq(Nat, m, Z)) (c : Nat) : Nat := (
    let r = IdN(&c);
    let v = J(Nat, m, Z, MN, h, (let t = IdN(&*r); *t := 1; Z));
    let d = c; d)
  -- assignment through a returned borrow while a part of it is reborrowed
  def AssignThrough : Nat × Nat := (
    let c = (1, 2);
    let r = Whole(&c);
    let a = IdN(&(*r).0);
    *r := (5, 6);
    let d = c; d)
  -- two stuck picks over the same places, a part of each reborrowed
  def PickParts (n : Nat) (n2 : Nat) (c : Nat × Nat) (e : Nat × Nat) : Nat := (
    let s = (let q = PickP(n, &c, &e); IdN(&(*q).1));
    *s := 1;
    let r = PickP(n2, &c, &e);
    let a = IdN(&(*r).0);
    0)
}

/-
Not in the block: two programs of the same family that the checker rejects with "internal: stuck
escaped to the top" (on main as of 207eed2f, reported to the lead). A stuck block or `J` whose
code borrows a FIELD of a captured place. Once fixed, they belong in the block above:

  def StuckBlockField (k : Nat) (c : Nat × Nat) : Nat := (match k { Z => (let t = &c.0; ()), S _ => () }; 0)
  def StuckJField (m : Nat) (h : Eq(Nat, m, Z)) (c : Nat × Nat) : Nat × Nat := (
    let r = Whole(&c);
    let v = J(Nat, m, Z, MN, h, (let t = IdN(&(*r).0); *t := 1; Z));
    let d = c; d)
-/

/-! ## The join drops a field under an open value (the slice, 2026-11-20)

Written to make the join drop a field of a value that is open (D64: a field of a type its earlier
fields no longer give): rewrite or lend the index of a dependent constructor, then let one arm of a
non-tail match move a non-copy field, so that the join drops it in the other arm. Accepted: `O1`
(the capacity rewritten, the buffer moved), `O2` (the same through a borrow, repaired after the
join), `O3` (the capacity lent instead), `O4b` (one level down, the match in tail position), `O5`
(another non-copy field of the same open value). Rejected: `O4` (one level down, a non-tail match:
the stuck block captures the open value whole, [Repack]). A rewritten index invalidates the proof
field that mentions it (`⊥`), so the open value is partly moved too. -/
ochr OpenJoin uses ArrayLemmas, Options, DepVec {
  def O1 (k : Word) (v0 : Vec(Word)) : Unit := (
    let v = v0;
    match v { MkVec(len, cap, buf, hl) => cap := Succ(cap), };
    match k { Zero => (let b = v.2; ()), Succ(m) => () };
    ()
  )
  def O2 (k : Word) (v : &Vec(Word)) : Unit := (
    match *v {
      MkVec(len, cap, buf, hl) => (
        cap := Succ(cap);
        match k { Zero => (let b = buf; ()), Succ(m) => () };
        cap := Zero;
        buf := ([] : Array(Opt(Word), Zero));
        len := Zero;
        hl := refl
      ),
    }
  )
  def O3 (k : Word) (v0 : Vec(Word)) : Unit := (
    let v = v0;
    let r = &v.1;
    match k { Zero => (let b = v.2; ()), Succ(m) => () };
    ()
  )
  reject def O4 (k : Word) (v0 : Vec(Word)) : Unit := (
    let p = Mk(v0, Zero);
    match p.0 { MkVec(len, cap, buf, hl) => cap := Succ(cap), };
    match k { Zero => (let b = (p.0).2; ()), Succ(m) => () };
    ()
  )
  def O4b (k : Word) (v0 : Vec(Word)) : Unit := (
    let p = Mk(v0, Zero);
    match p.0 { MkVec(len, cap, buf, hl) => cap := Succ(cap), };
    match k { Zero => (let b = (p.0).2; ()), Succ(m) => () }
  )
  inductive L := LNil | LCons(h : Word, t : L)
  inductive V2 := MkV2(cap : Word, buf : Array(Opt(Word), cap), other : L)
  def O5 (k : Word) (v0 : V2) : Unit := (
    let v = v0;
    match v { MkV2(cap, buf, other) => cap := Succ(cap), };
    match k { Zero => (let b = v.2; ()), Succ(m) => () };
    ()
  )
}

namespace Sweep

/-- The probe blocks (`lake exe sweep --probes`). -/
def probes : List (String × Ochr.Surface.Block) := [("LentUnder", LentUnder), ("OpenJoin", OpenJoin)]

end Sweep
