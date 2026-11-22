import Ochr.Examples.Nat
import Ochr.Examples.Word
import Ochr.Examples.Fixtures

/-! # 2. Borrows: moving, copying, reborrowing, and the borrow checker

`&p` borrows the place `p`, and `*r` is the place a borrow `r` points to. Reading a place
moves what it holds out, and the place is dead afterwards, unless its type is a copy type
(`Unit`, `Bool`, a `Word`, a pair of copies; not `Nat`), which a read copies. `clone(p)`
copies anything. A term that is erased (a type, a proof, a statement) reads without moving,
and still sees what was moved (D53). A borrow is always moved (RULES P3). `&*x` reborrows: it lends `*x` for a while
and leaves `x` usable afterwards. Before a place is used, every borrow that might still
reach it is ended ([Access]); using an ended borrow is an error. A local that dies while a
variable still borrows it ends that borrow too, but one that dies while a value in flight
borrows it (a block or a function returning a borrow of its own local) is an error ([Drop],
D65). This is the whole borrow checker.

Defined in RULES §3: [Read], [Borrow], [Assign], [Access], [End], [Drop], [Call]. -/

open Ochr.Test

ochr Borrows uses Nats, WordType {
  -- Passing `x` moves the borrow into the call, so the second call reads a dead place.
  reject def UseMoved (x : &Nat) : Unit := (
    AddM(x, 0);
    AddM(x, 0)
  )

  -- Reborrowing `&*x` for the first call leaves `x` usable for the second.
  def UseReborrowed (x : &Nat) : Unit := (
    AddM(&*x, 0);
    AddM(x, 0)
  )

  -- A statement is erased, and its reads copy, so `Add(x, x)` reads `x` twice, and
  -- `x + x = x` is a well-formed statement (a false one).
  def AddXX (x : Nat) : Prop := Id(Nat, Add(clone(x), x), x)

  -- A borrow of a local writes to the local: after `*y := 2` through `y = &x`, `x` is `2`.
  def LetZ (x : Nat) : Nat := (
    let z = (let y = &x; *y := 2; x);
    let h : Id(Nat, clone(z), 2) = refl;
    z
  )

  -- Returning a borrow of a local: the local is dropped at the end of the call while the
  -- returned borrow still points to it.
  reject def DanglingLocal (u : Unit) : &Nat := (
    let z = 0;
    &z
  )

  reject def DanglingReborrow (z : Nat) : &Nat := (
    let r = &z;
    &*r
  )

  -- Arguments are evaluated left to right, each into a temporary that later arguments can
  -- see. Reading `x` for the second argument ends the borrow `&x` made for the first, so
  -- the callee would receive a dead borrow.
  reject def Dead (f : Π(a : &Nat) (b : Nat). Unit) (x : Nat) : Unit := f(&x, x)
  -- twin of Dead: the borrow is made last, after the read of `x`, so nothing ends it
  def DeadOk (f : Π(a : Nat) (b : &Nat). Unit) (x : Nat) : Unit := f(clone(x), &x)
  reject def DeadTwice (f : Π(a : &Nat) (b : &Nat). Unit) (x : Nat) : Unit := f(&x, &x)
  -- twin of DeadTwice: the two borrows are of different places
  def DeadTwiceOk (f : Π(a : &Nat) (b : &Nat). Unit) (x : Nat) (y : Nat) : Unit := f(&x, &y)

  -- The other way round is fine when `x` is a copy (a `Word`, D53): it is copied first, then
  -- borrowed. A `Nat` is moved by the first argument, so it needs `clone(x)` there.
  def NotDead (f : Π(a : Word) (b : &Word). Unit) (x : Word) : Unit := f(x, &x)

  -- A statement about two separate borrows ...
  def g (x : &Nat) (y : &Nat) : Id(Nat, *x := 0; *y := 1; clone(*x), *x := 0; *y := 1; 0) := refl

  -- ... cannot be used on two borrows of the same place: passing `z` ends the reborrow `a`,
  -- in whichever order the two are passed (D19).
  reject def attack (z : &Nat) : Id(Nat, 1, 0) := (
    let a = &*z;
    g(z, a)
  )

  reject def attack' (z : &Nat) : Id(Nat, 1, 0) := (
    let a = &*z;
    g(a, z)
  )

  -- ## What goes wrong without these rules
  -- Without the check that no argument is dead, `Dead` is accepted: an
  -- opaque callee receives a dead borrow, and a concrete run goes wrong as soon as it writes
  -- through it.

  -- [Access] ends every borrow of a place inside the content being passed, not only borrows
  -- of the place itself (D19). Here `r` borrows the predecessor inside `*b`; passing `b` to
  -- `G1` must end `r` first. Without that, the call's stuck result
  -- would keep `r`'s loan inside `a`, and the later write through `r` would go to a place
  -- that no longer exists. (With the stuck `Unit` call's result `()`, its η-normal form,
  -- D59 refined, `BadA1` needs D19 again; for a while the result was a sealed program carrying
  -- the loan, which [Drop] caught.)
  def G1 (x : &Nat) (n : Nat) : Unit := (
    match n {
      Z => (),
      S _ => *x := 0,
    }
  )

  reject def BadA1 (n : Nat) : Nat := (
    let a = S(Z);
    (let b = &a; let r = &(*b).0; G1(b, n); *r := S(Z));
    a
  )

  -- twin of BadA1: the write through `r` comes before `b` is passed to `G1`, so `r` is not used after the call ends it
  def BadA1Ok (n : Nat) : Nat := (
    let a = S(Z);
    (let b = &a; let r = &(*b).0; *r := S(Z); G1(b, n));
    a
  )

  -- D19's witnesses since then (fuzz-port). In `V` a stuck block
  -- returns a borrow of `n0`, so `n0` holds a sealed program with that borrow's loan inside
  -- it; reading `n0` must end the borrow, and the write through `a0` then has no place.
  -- Without D19, `V` is accepted and `V(0)` goes wrong: the block runs, the read of `n0`
  -- ends `a0`, and the write is to nothing.
  reject def V (n0 : Nat) : Unit := (let a0 = match n0 { Z => &n0, S _ => &n0 }; *a0 := n0)
  -- twin of V: the value written is `0`, so `n0` is not read while `a0` is live
  def VOk (n0 : Nat) : Unit := (let a0 = match n0 { Z => &n0, S _ => &n0 }; *a0 := 0)
  reject def VRun : Unit := V(0)

  -- [Close]'s precondition (a stuck call's arguments hold no live loans): `&a` holds `r`'s
  -- loan inside, [Close] would seal it into `out`, and the write through `r` would be
  -- accepted; at `n = 1` the call runs and overwrites `a` while `r` borrows inside it. The
  -- result goes to `out`, declared before `r`, so `r` dies first and [Drop] never sees the
  -- loan in it (bound after `r`, as in `BadA1`, [Drop] catches it even without D19).
  def G2 (x : &Nat) (n : Nat) : Nat := (match n { Z => 0, S _ => *x := 0; 0 })
  reject def W (n : Nat) : Nat := (let a = S(Z); let out = 0; (let r = &a.0; out := G2(&a, n); *r := S(Z)); out)
  -- twin of W: the write through `r` comes before the call, so `&a` holds no live loan when passed
  def WOk (n : Nat) : Nat := (let a = S(Z); let out = 0; (let r = &a.0; *r := S(Z); out := G2(&a, n)); out)
  reject def WRun : Nat := W(1)
}


/-! ## A place that dies while lent (D65 amended)

When an owned place is dropped while something borrows it, a borrower held in a binding (a
variable, or a place inside one) is ended, as a write through [Access] would end it: Rust's
non-lexical-lifetime reading, where the borrower is not used again. A borrower still in flight
(the value a block or function is returning) makes the drop an error: a block or function may
not return a borrow of its own local. The symbolic path can end a borrow earlier than a ground
run does (a returned borrow's hole sits in every possible owner's fill; a match on a sealed
fill ends every loan in it), so an error at [Drop] for a live loan would let a function pass
generically and fail at an instance (meta-order's `Bad2`, reviewer-9's `Bad4`, fuzz-port's
Drop family). Each accepted function below also runs at the instance that used to fail. -/

ochr Drops uses Nats, Fixtures {
  -- `Pick`'s hole sits in `a`'s fill and `b`'s; reading `b` ends `x` symbolically, while at
  -- `n = 0` `x` still borrows `a` when `a` dies, and is ended there
  def Bad2 (n : Nat) (b : Nat) (x : &Nat) : Unit := (let a = 0; x := Pick(n, &a, &b); let z = b; ())
  def Bad2Run : Unit := (let y = 7; Bad2(0, 5, &y))
  -- the same with a local borrow declared before `a`
  def Bad3 (n : Nat) (b : Nat) : Unit := (let c = 1; let x = &c; let a = 0; x := Pick(n, &a, &b); let z = b; ())
  def Bad3Run : Unit := Bad3(0, 5)
  -- one owner: the match on `a`'s sealed fill ends `x` symbolically; at `a = 1` the loan sits
  -- in `a.0` and survives the match
  def Bad4 (x : &Nat) (a : Nat) : Unit := (x := TailM(&a); match a { Z => (), S _ => () })
  def Bad4Run : Unit := (let c = 0; Bad4(&c, 1))
  -- the same with a local borrow declared before the owner (reviewer-9)
  def Bad5 (a : Nat) : Unit := (let c = 1; let x = &c; let b = a; x := TailM(&b); match b { Z => (), S _ => () })
  def Bad5Run : Unit := Bad5(1)
  -- a stuck match instead of a call; a write, or a borrow, of the other owner; the owners
  -- the other way round (fuzz-port's Drop family)
  def D1 (n : Nat) (b : Nat) (x : &Nat) : Unit := (let a = 0; x := match n { Z => &a, S _ => &b }; let z = b; ())
  def D1Run : Unit := (let y = 7; D1(0, 5, &y))
  def D2 (n : Nat) (b : Nat) (x : &Nat) : Unit := (let a = 0; x := Pick(n, &a, &b); b := 0)
  def D2Run : Unit := (let y = 7; D2(0, 5, &y))
  def D3 (n : Nat) (b : Nat) (x : &Nat) : Unit := (let a = 0; x := Pick(n, &a, &b); let w = &b; ())
  def D3Run : Unit := (let y = 7; D3(0, 5, &y))
  def D4 (n : Nat) (b : Nat) (x : &Nat) : Unit := (let a = 0; x := Pick(n, &b, &a); let z = b; ())
  def D4Run : Unit := (let y = 7; D4(1, 5, &y))
  -- a statement can mention a borrow variable the symbolic path has ended: reassigning it is
  -- not an error (reviewer-9)
  def AssignBot (n : Nat) (a : Nat) (b : Nat) (c : Nat) : Unit := (
    let x = Pick(n, &a, &b);
    let z = clone(b);
    let h : Id(Unit, x := &c; *x := 5, x := &c; *x := 5) = refl;
    ()
  )
  def AssignBotRun : Unit := AssignBot(0, 1, 2, 3)
  -- `a`'s death ends `x`, so writing through `x` afterwards is an error
  reject def UseEnded (c : Nat) : Unit := (let x = &c; (let a = 0; x := &a; ()); *x := 1)
  -- a borrower in flight: returning a borrow of a local (no separate result check)
  reject def RetLocal (x : &Nat) : &Nat := (let a = 0; &a)
  -- twin of RetLocal: returns the borrow parameter instead of a borrow of the local
  def RetLocalOk (x : &Nat) : &Nat := (let a = 0; x)
  -- a let-block's result borrows the block's own local (`Pick`'s hole sits in `a`'s fill)
  reject def E1 (n : Nat) (b : Nat) : Unit := (let q = (let a = 0; Pick(n, &a, &b)); ())
  -- twin of E1: `a` is declared outside the `q` block, so it outlives the borrow
  def E1Ok (n : Nat) (b : Nat) : Unit := (let a = 0; let q = Pick(n, &a, &b); ())
  -- a tail match whose arm returns a borrow of an arm-local
  reject def FR (n : Nat) (x : &Nat) : &Nat := (match n { Z => (let a = 0; &a), S _ => x })
  -- twin of FR: the arm returns `x` rather than a borrow of its local
  def FROk (n : Nat) (x : &Nat) : &Nat := (match n { Z => (let a = 0; x), S _ => x })
  -- the same inside a stuck block: [Split] discards arm values and [Close] gives the block a
  -- fresh live borrow, so ending the arm's borrow would pass generically and fail at `n = 0`
  reject def Blk (n : Nat) (b : Nat) : Unit := (
    let r : &Nat = match n { Z => (let q = 0; &q), S _ => &b };
    *r := 5
  )
  -- twin of Blk: `q` is declared before the match, so the arm borrows a place that outlives it
  def BlkOk (n : Nat) (b : Nat) : Unit := (
    let q = 0;
    let r : &Nat = match n { Z => &q, S _ => &b };
    *r := 5
  )
  reject def G (n : Nat) (b : &Nat) : &Nat := (
    let r : &Nat = match n { Z => (let q = 0; &q), S _ => &*b };
    r
  )
  -- twin of G: both arms reborrow `b`, none borrows an arm-local
  def GOk (n : Nat) (b : &Nat) : &Nat := (
    let r : &Nat = match n { Z => &*b, S _ => &*b };
    r
  )
  -- a caller of `G`, which is rejected, so `G` is not in scope here
  reject def UseG (n : Nat) (c : Nat) : Unit := (let r = G(n, &c); *r := 7)
  -- twin of UseG: calls `GOk`, which is accepted and so in scope
  def UseGOk (n : Nat) (c : Nat) : Unit := (let r = GOk(n, &c); *r := 7)
}


/-- The message rejecting `Drops.name`. -/
def dropsMessage (name : String) : String :=
  match ((run "Drops" Drops).rows.find? (·.name == name)).map (·.verdict) with
  | some (Ochr.Verdict.rejected m _) => m
  | _ => ""

-- each borrower-in-flight witness is rejected by [Drop] itself, not by a later use of ⊥
#guard ["RetLocal", "E1", "FR", "Blk", "G"].all fun n =>
  ((dropsMessage n).splitOn "dies while a value in flight borrows it").length == 2
#guard ((dropsMessage "UseG").splitOn "unknown constant G").length == 2

/-! ## Moves and copies (D53)

Reading data whose type is not a copy type moves it; `clone` copies; a copy type is declared
`copy` or is not recursive with copy fields; erased reads copy and see ghosts; the Fn rule;
and a stuck match's effect on what it captures, moves included (RULES P3, D53). -/

ochr Moves uses Nats, WordType {
  -- Reading a `Nat` moves it: after `let m = n`, `n` is gone ...
  def MoveNat (n : Nat) : Nat := (
    let m = n;
    m
  )

  reject def UseAfterMove (n : Nat) : Nat := (
    let m = n;
    n
  )

  -- ... unless it is cloned. A `Word` is declared `copy`, so every read copies it.
  def CloneNat (n : Nat) : Nat × Nat := (clone(n), n)
  reject def TwiceNat (n : Nat) : Nat × Nat := (n, n)
  def TwiceWord (w : Word) : Word × Word := (w, w)

  -- A type is a copy type when it is declared `copy` (its fields must be copies) or when it
  -- is not recursive and its fields are copies.
  copy inductive Pt := MkPt(x : Word, y : Word)
  reject copy inductive NatBox := MkNatBox(n : Nat)
  def TwicePt (p : Pt) : Pt × Pt := (p, p)

  -- A statement reads like any code (D68): `n` was moved into `m`, so the statement cannot
  -- read it (it runs on its own copy of the state, which has `n` moved out too).
  reject def GhostRead (n : Nat) : Nat := (
    let m = n;
    let h : Id(Nat, clone(n), clone(m)) = refl;
    m
  )

  -- Moving out through a borrow is allowed when the place is whole again by the time the
  -- borrow ends ...
  def TakeAndRestore (x : &Nat) : Nat := (
    let v = *x;
    *x := Z;
    v
  )

  -- ... and an error otherwise, as is returning a borrow of what was moved out.
  reject def TakeFromBorrow (x : &Nat) : Nat := *x

  reject def ReturnMovedBorrow (x : &Nat) (y : &Nat) : &Nat := (
    let v = *y;
    y
  )

  -- A call does not consume the function it calls, so a function can be called twice. A
  -- closure may run again, so its body may not move out of what it captured: returning a
  -- captured `Nat` needs `clone`. A function type is not a copy type, so reading a place
  -- that holds a function moves it, whatever it captured (D68: copy-ness is the type's).
  def CallTwice (f : Π(x : Nat). Nat) (x : Nat) : Nat := f(f(x))

  reject def ClosureMovesCapture (n : Nat) : Nat × Nat := (
    let f = (λ(u : Unit) : Nat => n);
    (f(()), f(()))
  )

  def ClosureClones (n : Nat) : Nat × Nat := (
    let f = (λ(u : Unit) : Nat => clone(n));
    (f(()), f(()))
  )

  reject def ClosureCopy (w : Word) : Word × Word := (
    let f = (λ(u : Unit) : Word => w);
    let g = f;
    (f(()), g(()))
  )
  -- twin of ClosureCopy: the closure is called twice instead of being copied
  def ClosureCopyOk (w : Word) : Word × Word := (
    let f = (λ(u : Unit) : Word => w);
    (f(()), f(()))
  )

  reject def ClosureMoved (n : Nat) : Nat := (
    let f = (λ(u : Unit) : Nat => clone(n));
    let g = f;
    f(())
  )

  -- A match that moves out of a borrowed place in one arm leaves the borrow partly moved
  -- when it ends. Closed off, the same program is re-run for its result and for what it
  -- leaves in `*x0`, and each re-run moves again: the re-runs have runtime semantics, and
  -- only the final read of the result is an observation (fuzz-port shape (b)).
  reject def MoveInArm (x0 : &Nat) : Nat := (
    match *x0 {
      Z => *x0,
      S p3 => 0,
    }
  )

  -- A stuck match reads its scrutinee in place, so closing it off does not move a `Nat` it
  -- only reads ...
  def BlockReads (n0 : Nat) : Nat := (
    let l = match n0 {
      Z => 0,
      S _ => 1,
    };
    n0
  )

  -- ... and moves in only the part an arm moves out, `q1.0`, so `q1.1` is still there
  -- (fuzz-port shape (a)).
  def BlockMovesField (q1 : Nat × Nat) : Nat := (
    let a = match q1 {
      Mk(p7, p8) => p7,
    };
    match q1 {
      Mk(p9, p10) => p10,
    }
  )

  -- A function that moves out of `*y10` and returns `y10` hands back a borrow of a moved
  -- place, an error as when a borrow ends partly moved. Compared by their results only
  -- through a fresh value written into them (D38), it looked equal to the one that just
  -- returns `y10` (fuzz-port shape (c)).
  reject def RetMoved : Eq(Π(y9 : &Nat) (y10 : &Nat). &Nat, (λ(y9 : &Nat) (y10 : &Nat) : &Nat => (*y10; y10)), (λ(y9 : &Nat) (y10 : &Nat) : &Nat => y10)) := refl

  -- A stuck match's effect on what it captures is the direct path's, moves included, at
  -- every granularity (fuzz-port's execution oracle: each of these was accepted and went
  -- wrong when run). M1: an arm moves a field its pattern exposed, so `q0` (and `n0`) is
  -- partly moved afterwards; a pair is refined to its one constructor to say which part.
  reject def A1 (q0 : Nat × Nat) : Nat × Nat := (let a = match q0 { Mk(p, _) => p }; q0)
  reject def A2 (n0 : Nat) : Nat := (let a = match n0 { Z => 0, S p => p }; n0)
  def A3 (q0 : Nat × Nat) : Nat := (let a = match q0 { Mk(p, _) => p }; a)
  -- M2: an arm moves a captured place that is not a whole variable (`*x0`, `*x1`), so the
  -- block moves it in and the borrow ends partly moved
  reject def B1 (x0 : &Nat) (n1 : Nat) : Nat := (let a = match n1 { Z => 0, S _ => *x0 }; a)
  reject def B2 (q0 : Nat × Nat) (x1 : &Nat) : Nat := S(match q0 { Mk(_, _) => *x1 })
  reject def B3 (x0 : &Nat) (x1 : &Nat) : &Nat := (match *x1 { Z => (), S _ => *x1 := *x0 }; x0)
  -- M2b: one arm moves the borrow into the block, another moves out through it, and the
  -- block's frame ends the borrow partly moved
  reject def B4 (x0 : &Nat) : Nat := S((match *x0 { Z => x0; 0, S _ => *x0 }))
  -- M3: statement positions run on their own copy, whichever path runs them: `J`'s endpoints
  -- and motive (as run by a call, untyped), and an `Id` side. A statement reads like any code
  -- (D68), so `J`'s endpoint cannot read the moved `n`.
  reject def J1 (n : Nat) (h : Eq(Nat, n, 1)) : Nat := (let m = n; J(Nat, n, 1, λ(z : Nat) : Type => Nat, h, m))
  reject def J1Run : Nat := J1(1, refl)
  def I1 (n1 : Nat) : Nat := (let m = n1; let a0 = Id(Unit, (), n1 := 0); 0)
  def I1Run : Nat := I1(0)
  -- A block's effect on its captures is read from its arms' moves and assignments, by place
  -- (not by comparing values, which are abstract or sealed), so it composes through nested
  -- blocks (N1), sees a borrow moved in whole by an inner block's capture (N2), and gives
  -- each part of a captured place its own mode: `q1.0` moved, `q1.1` lent (N3). A move that
  -- the arm restores, or that goes through a local borrow, counts as the owner's.
  reject def N1 (x0 : &(Nat × Nat)) (n1 : Nat) : Nat := (
    let a = match n1 { Z => match *x0 { Mk(p, _) => p }, S _ => 0 }; a)
  reject def N2 (x0 : &Nat) : Nat := (
    let a = match *x0 { Z => match *x0 { Z => 0, S _ => x0; 0 }, S _ => *x0 }; a)
  reject def N3 (q1 : Nat × Nat) : Nat × Nat := (
    let a = match q1 { Mk(p1, p2) => match p2 { Z => p1; &p2, S _ => &p2 } }; q1)
  def N3Other (q1 : Nat × Nat) : Nat := (
    let a = match q1 { Mk(p1, p2) => match p2 { Z => p1; &p2, S _ => &p2 } }; 0)
  def MoveRestore (x0 : &Nat) (n1 : Nat) : Nat := (
    let a = match n1 { Z => 0, S _ => (let v = *x0; *x0 := 0; v) }; a)
  reject def ThroughLocal (q0 : Nat × Nat) (n1 : Nat) : Nat × Nat := (
    let a = match n1 { Z => 0, S _ => (let r = &q0; match *r { Mk(u, _) => u }) }; q0)

  -- A borrow whose content is moved out, wholly or partly, is not read at all (D127): it is not
  -- passed to a call, returned or moved to another name until its content is whole again, so a
  -- helper cannot be handed it to refill (`TakeRefill`, accepted before D127, when a call that
  -- runs could refill it). Refill it through the borrow in the same function, by an assignment,
  -- which is a write and not a read (`TakeAssign`), or before handing it on (`RefillFirst`).
  -- Before D127 the same rule held only where the call is not run: a call that closes off seals
  -- the borrowed content (hiding the hole), and an erased call's writes vanish at runtime
  -- (fuzz-port P; `P1`, `P2`).
  def G1 (x : &Nat) (n : Nat) : Unit := match n { Z => (), S _ => *x := 0 }
  def F5 (x : &Nat) : Prop := (*x := 5; ⊤)
  def Refill (x : &Nat) (v : Nat) : Unit := *x := v
  reject def P1 (x0 : &Nat) : Unit := (let a3 = *x0; G1(x0, a3))
  reject def P2 (x1 : &Nat) : Unit := ((let a0 = *x1; match a0 { Z => (), S _ => F5(x1); () }); ())
  reject def TakeRefill (x : &Nat) : Unit := (let v = *x; Refill(x, v))
  def TakeAssign (x : &Nat) : Unit := (let v = *x; *x := v)
  def RefillFirst (x : &Nat) : Unit := (let v = *x; *x := 0; Refill(x, v))
  -- reviewer-7's attacks (§4.1): a borrow moved whole, or partly, out of before a call that
  -- closes off; `Thm1` was a false equation about an accepted program (`FullMove(&3, 0)`
  -- errs when run)
  def H (x : &Nat) (n : Nat) : Unit := (match n { Z => (), S _ => match *x { Z => (), S q => *x := q } })
  reject def FullMove (x : &Nat) (n : Nat) : Nat := (let v = *x; H(x, n); v)
  reject def PartMove (x : &Nat) (n : Nat) : Unit := (match *x { Z => (), S p => (let v = p; H(x, n)) })
  reject def PartMoveOpaque (g : Π(y : &Nat). Unit) (x : &Nat) : Unit := (
    match *x { Z => (), S p => (let v = p; g(x)) })
  reject def Thm1 : Id(Nat, let c = 3; FullMove(&c, 0), 3) := refl
  reject def TailMove (x : &Nat) (n : Nat) : Nat := (let t = TailM(x); let v = *t; H(t, n); v)
  -- A closure made in an arm that captures (moves) `q0` for its `q0.0` moves `q0` (Q); a
  -- move of `a4.1` in one arm and an inspection of `a4` in another split `a4`, whichever way
  -- the field is written (`.1` or a pattern's `snd`: K)
  reject def Q1 (q0 : Nat × Nat) (n1 : Nat) : Nat × Nat := (
    match q0 { Mk(p0, p1) => let a2 = match n1 { Z => (λ(y4 : Nat) : Unit => p0 := y4), S p6 => (λ(y8 : Nat) : Unit => ()) }; (p0, 0) })
  inductive Sw := SwF | SwT
  reject def K1 (b0 : Sw) : Nat × Nat := (
    let a4 = (0, 0); let t = match b0 { SwF => match a4 { Mk(p, q) => 0 }, SwT => let s = a4.1; 0 }; a4)

  -- RN: a split in a data function re-normalises its hypotheses' types, as types (reads copy)
  def DataSplit (n : Nat) (h : Id(Nat × Nat, (match n { Z => (clone(n), n), S p => (clone(p), p) }), (match n { Z => (0, 0), S p => (clone(p), p) }))) : Nat := (
    match n { Z => 0, S _ => 1 })
}

#guard (run "Moves" Moves).rejectedWith [
  ("TakeRefill", "[Read] x is a borrow whose content was moved out: refill it through x (*x := …) before reading x (D127)"),
  ("P1", "[Read] x0 is a borrow whose content was moved out: refill it through x0 (*x0 := …) before reading x0 (D127)"),
  ("P2", "[Read] x1 is a borrow whose content was moved out: refill it through x1 (*x1 := …) before reading x1 (D127)"),
  ("FullMove", "[Read] x is a borrow whose content was moved out: refill it through x (*x := …) before reading x (D127)"),
  ("TailMove", "[Read] t is a borrow whose content was moved out: refill it through t (*t := …) before reading t (D127)"),
  ("ReturnMovedBorrow", "[Read] y is a borrow whose content was moved out: refill it through y (*y := …) before reading y (D127)"),
  ("RetMoved", "[Read] y10 is a borrow whose content was moved out: refill it through y10 (*y10 := …) before reading y10 (D127)"),
  ("B3", "[Read] x0 is a borrow whose content was moved out: refill it through x0 (*x0 := …) before reading x0 (D127)")]

/-! ### A borrow whose content is partly moved out is not read (D127)

Before D127 a place holding a borrow was read (moved to another name, passed to a call, assigned,
returned) whatever its content held, so a borrow whose content was partly moved out could be
handed on, as long as whoever received it wrote the moved part back before reading it: a callee
that runs was checked on the actual state (`CallFillP`). The consistency proof's model defines a
function on the members of its parameter types, and such a borrow is not a member of `&T`, so it
is no longer read at all: the content is restored first, through the same borrow (`…W`, each
beside its `…P`). A partly moved place is not read by copy either (`clone`, an erased read:
`CloneDP`, `CloneOP`, `EqOP`, `EqDP`). The hunt, kept: every route by which such a borrow could
flow (a `let`, a call that runs and one that closes off, a result, an assignment, a capture, a
match through it, a reborrow, a stuck block's arm, `clone`), each `…P` beside its `…W`. Before
D127 the `…P` rows `MB2`, `LetF`, `CallFillP`, `CallFill0P`, `AsgP`, `ParP`, `ParCallP`, `NestP`,
`CloneDP`, `CloneOP`, `EqOP`, `EqDP` were accepted, every one restoring the hole before any read
of it, and every route that read the hole was already rejected. -/

ochr MovedBorrows uses Nats {
  inductive Box := MkBox(n : Nat)
  def Fill (q : &Pair(Box, Nat)) : Unit := *q := (MkBox(Z), Z)
  def Fill0 (q : &Pair(Box, Nat)) : Unit := (*q).0 := MkBox(Z)
  def ReadB (q : &Pair(Box, Nat)) : Nat := clone((*q).1)
  def ReadAR (q : &Pair(Box, Nat)) : Nat := (let MkBox(m) = clone((*q).0); m)
  def FillK (q : &Pair(Box, Nat)) (k : Nat) : Unit := match k { Z => *q := (MkBox(Z), Z), S j => *q := (MkBox(Z), Z) }
  def ReadK (q : &Pair(Box, Nat)) (k : Nat) : Nat := match k { Z => (let MkBox(m) = clone((*q).0); m), S j => 0 }
  def PassOn (q : &Pair(Box, Nat)) : &Pair(Box, Nat) := q
  -- the lead's three
  def MB1 (a : Nat) (b : Nat) : Unit := (let x = (MkBox(a), b); let r = &x; let y = (*r).0; *r := (MkBox(Z), Z); ())
  reject def MB2 (a : Nat) (b : Nat) : Unit := (let x = (MkBox(a), b); let r = &x; let y = (*r).0; let r2 = r; *r2 := (MkBox(Z), Z); ())
  reject def MB3 (a : Nat) (b : Nat) : Unit := (let x = (MkBox(a), b); let r = &x; let y = (*r).0; ())
  def MB2W (a : Nat) (b : Nat) : Unit := (let x = (MkBox(a), b); let r = &x; let y = (*r).0; (*r).0 := MkBox(Z); let r2 = r; *r2 := (MkBox(Z), Z); ())
  -- a let, the hole restored through the new name by a field write
  reject def LetF (a : Nat) (b : Nat) : Unit := (let x = (MkBox(a), b); let r = &x; let y = (*r).0; let r2 = r; (*r2).0 := MkBox(Z); ())
  -- a let, no restore
  reject def LetN (a : Nat) (b : Nat) : Unit := (let x = (MkBox(a), b); let r = &x; let y = (*r).0; let r2 = r; ())
  -- a let, then a read of the hole through the new name
  reject def LetR (a : Nat) (b : Nat) : Nat := (let x = (MkBox(a), b); let r = &x; let y = (*r).0; let r2 = r; let MkBox(m) = clone((*r2).0); m)
  -- a call that runs: the callee restores whole / restores the field / reads the other field / reads the hole
  reject def CallFillP (a : Nat) (b : Nat) : Unit := (let x = (MkBox(a), b); let r = &x; let y = (*r).0; Fill(r))
  def CallFillW (a : Nat) (b : Nat) : Unit := (let x = (MkBox(a), b); let r = &x; let y = (*r).0; (*r).0 := MkBox(Z); Fill(r))
  reject def CallFill0P (a : Nat) (b : Nat) : Unit := (let x = (MkBox(a), b); let r = &x; let y = (*r).0; Fill0(r))
  reject def CallReadBP (a : Nat) (b : Nat) : Nat := (let x = (MkBox(a), b); let r = &x; let y = (*r).0; ReadB(r))
  reject def CallReadARP (a : Nat) (b : Nat) : Nat := (let x = (MkBox(a), b); let r = &x; let y = (*r).0; ReadAR(r))
  def CallReadARW (a : Nat) (b : Nat) : Nat := (let x = (MkBox(a), b); let r = &x; let y = (*r).0; (*r).0 := MkBox(Z); ReadAR(r))
  -- a call that closes off (k unknown), and its instances
  reject def CallFillKP (a : Nat) (b : Nat) (k : Nat) : Unit := (let x = (MkBox(a), b); let r = &x; let y = (*r).0; FillK(r, k))
  def CallFillKW (a : Nat) (b : Nat) (k : Nat) : Unit := (let x = (MkBox(a), b); let r = &x; let y = (*r).0; (*r).0 := MkBox(Z); FillK(r, k))
  reject def CallReadKP (a : Nat) (b : Nat) (k : Nat) : Nat := (let x = (MkBox(a), b); let r = &x; let y = (*r).0; ReadK(r, k))
  def CallReadKW (a : Nat) (b : Nat) (k : Nat) : Nat := (let x = (MkBox(a), b); let r = &x; let y = (*r).0; (*r).0 := MkBox(Z); ReadK(r, k))
  reject def CallReadKPI : Eq(Nat, CallReadKP(1, 2, 0), 0) := refl
  reject def CallFillKPI : Eq(Unit, CallFillKP(1, 2, 0), ()) := refl
  -- a function's result
  reject def RetP (x : &Pair(Box, Nat)) : &Pair(Box, Nat) := (let y = (*x).0; x)
  def RetW (x : &Pair(Box, Nat)) : &Pair(Box, Nat) := (let y = (*x).0; (*x).0 := MkBox(Z); x)
  reject def RetPassP (a : Nat) (b : Nat) : Unit := (let x = (MkBox(a), b); let r = &x; let y = (*r).0; let r2 = PassOn(r); *r2 := (MkBox(Z), Z); ())
  -- an assignment's right-hand side (re-pointing a borrow binding)
  reject def AsgP (a : Nat) (b : Nat) : Unit := (let x = (MkBox(a), b); let x2 = (MkBox(Z), Z); let r = &x; let r2 = &x2; let y = (*r).0; r2 := r; *r2 := (MkBox(Z), Z); ())
  def AsgW (a : Nat) (b : Nat) : Unit := (let x = (MkBox(a), b); let x2 = (MkBox(Z), Z); let r = &x; let r2 = &x2; let y = (*r).0; (*r).0 := MkBox(Z); r2 := r; *r2 := (MkBox(Z), Z); ())
  -- a closure's capture
  reject def CapP (a : Nat) (b : Nat) : Unit := (let x = (MkBox(a), b); let r = &x; let y = (*r).0; let c = (λ(u : Unit) : Unit => (let z = r; ())); *r := (MkBox(Z), Z); ())
  -- a match's scrutinee through the borrow, the moved field unused / used
  def MatchP (a : Nat) (b : Nat) : Nat := (let x = (MkBox(a), b); let r = &x; let y = (*r).0; let v = match *r { Mk(p, q) => clone(q) }; *r := (MkBox(Z), Z); v)
  reject def MatchUseP (a : Nat) (b : Nat) : Nat := (let x = (MkBox(a), b); let r = &x; let y = (*r).0; let v = match *r { Mk(p, q) => (let MkBox(m) = clone(p); m) }; *r := (MkBox(Z), Z); v)
  -- a reborrow
  reject def ReP (a : Nat) (b : Nat) : Unit := (let x = (MkBox(a), b); let r = &x; let y = (*r).0; let r2 = &*r; *r2 := (MkBox(Z), Z); ())
  def ReW (a : Nat) (b : Nat) : Unit := (let x = (MkBox(a), b); let r = &x; let y = (*r).0; (*r).0 := MkBox(Z); let r2 = &*r; *r2 := (MkBox(Z), Z); ())
  -- clone and peek of it
  reject def CloneP (a : Nat) (b : Nat) : Unit := (let x = (MkBox(a), b); let r = &x; let y = (*r).0; let r2 = clone(r); *r := (MkBox(Z), Z); ())
  reject def CloneDP (a : Nat) (b : Nat) : Unit := (let x = (MkBox(a), b); let r = &x; let y = (*r).0; let c = clone(*r); *r := (MkBox(Z), Z); ())
  -- a statement (erased): Eq of the borrow's content and of a read of the borrow
  def StmtP (a : Nat) (b : Nat) : Unit := (let x = (MkBox(a), b); let r = &x; let y = (*r).0; let e : Eq(Nat, clone((*r).1), clone((*r).1)) = refl; *r := (MkBox(Z), Z); ())
  reject def StmtRP (a : Nat) (b : Nat) : Unit := (let x = (MkBox(a), b); let r = &x; let y = (*r).0; let e : Eq(Nat, ReadB(r), clone((*r).1)) = refl; *r := (MkBox(Z), Z); ())
  -- a parameter borrow, passed on partly moved inside a function that restores later (the generic call)
  reject def ParP (q : &Pair(Box, Nat)) : Unit := (let y = (*q).0; let q2 = q; *q2 := (MkBox(Z), Z); ())
  reject def ParCallP (q : &Pair(Box, Nat)) : Unit := (let y = (*q).0; Fill(q))
  reject def ParReadAP (q : &Pair(Box, Nat)) : Nat := (let y = (*q).0; ReadAR(q))
  reject def ParCallI (a : Nat) (b : Nat) : Unit := (let x = (MkBox(a), b); ParCallP(&x))
  def ParW (q : &Pair(Box, Nat)) : Unit := (let y = (*q).0; (*q).0 := MkBox(Z); let q2 = q; *q2 := (MkBox(Z), Z); ())
  def ParCallW (q : &Pair(Box, Nat)) : Unit := (let y = (*q).0; (*q).0 := MkBox(Z); Fill(q))
  def CallFill0W (a : Nat) (b : Nat) : Unit := (let x = (MkBox(a), b); let r = &x; let y = (*r).0; (*r).0 := MkBox(Z); Fill0(r))
  def LetFW (a : Nat) (b : Nat) : Unit := (let x = (MkBox(a), b); let r = &x; let y = (*r).0; (*r).0 := MkBox(Z); let r2 = r; (*r2).0 := MkBox(Z); ())
  -- a nested borrow: the hole one level down, read through a borrow of the outer pair
  reject def NestP (a : Nat) (b : Nat) (c : Nat) : Unit := (let x = ((MkBox(a), b), c); let r = &x; let y = ((*r).0).0; let r2 = r; *r2 := ((MkBox(Z), Z), Z); ())
  -- the borrow read in place: a reborrow passed and the original kept (a call that runs)
  -- a stuck block (k unknown) whose arm reads the borrow, out of tail position and in it; an instance
  reject def BlkP (a : Nat) (b : Nat) (k : Nat) : Unit := (let x = (MkBox(a), b); let r = &x; let y = (*r).0; let u = match k { Z => (let r2 = r; *r2 := (MkBox(Z), Z); ()), S j => (*r := (MkBox(Z), Z); ()) }; ())
  def BlkW (a : Nat) (b : Nat) (k : Nat) : Unit := (let x = (MkBox(a), b); let r = &x; let y = (*r).0; (*r).0 := MkBox(Z); let u = match k { Z => (let r2 = r; *r2 := (MkBox(Z), Z); ()), S j => (*r := (MkBox(Z), Z); ()) }; ())
  reject def BlkTP (a : Nat) (b : Nat) (k : Nat) : Unit := (let x = (MkBox(a), b); let r = &x; let y = (*r).0; match k { Z => (let r2 = r; *r2 := (MkBox(Z), Z); ()), S j => (*r := (MkBox(Z), Z); ()) })
  reject def BlkPI : Eq(Unit, BlkP(1, 2, 0), ()) := refl
  -- the copying read (clone, an erased read) of a partly moved place, owned or through a borrow
  def CloneDW (a : Nat) (b : Nat) : Unit := (let x = (MkBox(a), b); let r = &x; let y = (*r).0; (*r).0 := MkBox(Z); let c = clone(*r); *r := (MkBox(Z), Z); ())
  reject def CloneOP (a : Nat) (b : Nat) : Unit := (let x = (MkBox(a), b); let y = x.0; let c = clone(x); ())
  def CloneOW (a : Nat) (b : Nat) : Unit := (let x = (MkBox(a), b); let y = x.0; x.0 := MkBox(Z); let c = clone(x); ())
  def CloneOF (a : Nat) (b : Nat) : Nat := (let x = (MkBox(a), b); let y = x.0; clone(x.1))
  reject def EqOP (a : Nat) (b : Nat) : Unit := (let x = (MkBox(a), b); let y = x.0; let e : Eq(Pair(Box, Nat), clone(x), clone(x)) = refl; ())
  def EqOW (a : Nat) (b : Nat) : Unit := (let x = (MkBox(a), b); let y = x.0; x.0 := MkBox(Z); let e : Eq(Pair(Box, Nat), clone(x), clone(x)) = refl; ())
  reject def EqDP (a : Nat) (b : Nat) : Unit := (let x = (MkBox(a), b); let r = &x; let y = (*r).0; let e : Eq(Pair(Box, Nat), clone(*r), clone(*r)) = refl; *r := (MkBox(Z), Z); ())
  reject def CloneUse (a : Nat) (b : Nat) : Nat := (let x = (MkBox(a), b); let r = &x; let y = (*r).0; let c = clone(*r); *r := (MkBox(Z), Z); let MkBox(m) = c.0; m)
  reject def RebP (a : Nat) (b : Nat) : Unit := (let x = (MkBox(a), b); let r = &x; let y = (*r).0; Fill(&*r); ())
}

#guard (run "MovedBorrows" MovedBorrows).rejectedWith [
  ("MB2", "[Read] r is a borrow whose content is partly moved out ((⊥, σ1)): restore it before reading r (D127)"),
  ("MB3", "[D53] a borrow ends while its content is partly moved out ((⊥, σ1))"),
  ("LetF", "[Read] r is a borrow whose content is partly moved out ((⊥, σ1)): restore it before reading r (D127)"),
  ("LetN", "[Read] r is a borrow whose content is partly moved out ((⊥, σ1)): restore it before reading r (D127)"),
  ("LetR", "[Read] r is a borrow whose content is partly moved out ((⊥, σ1)): restore it before reading r (D127)"),
  ("CallFillP", "[Read] r is a borrow whose content is partly moved out ((⊥, σ1)): restore it before reading r (D127)"),
  ("CallFill0P", "[Read] r is a borrow whose content is partly moved out ((⊥, σ1)): restore it before reading r (D127)"),
  ("CallReadBP", "[Read] r is a borrow whose content is partly moved out ((⊥, σ1)): restore it before reading r (D127)"),
  ("CallReadARP", "[Read] r is a borrow whose content is partly moved out ((⊥, σ1)): restore it before reading r (D127)"),
  ("CallFillKP", "[Read] r is a borrow whose content is partly moved out ((⊥, σ1)): restore it before reading r (D127)"),
  ("CallReadKP", "[Read] r is a borrow whose content is partly moved out ((⊥, σ1)): restore it before reading r (D127)"),
  ("CallReadKPI", "unknown constant CallReadKP"),
  ("CallFillKPI", "unknown constant CallFillKP"),
  ("RetP", "[Read] x is a borrow whose content is partly moved out ((⊥, σ2)): restore it before reading x (D127)"),
  ("RetPassP", "[Read] r is a borrow whose content is partly moved out ((⊥, σ1)): restore it before reading r (D127)"),
  ("AsgP", "[Read] r is a borrow whose content is partly moved out ((⊥, σ1)): restore it before reading r (D127)"),
  ("CapP", "a closure or Π-type captures the borrow r (closures capture no borrows, RULES §1)"),
  ("MatchUseP", "[Read] (*r).fst was moved out or its borrow ended (reading ⊥)"),
  ("ReP", "[Borrow] *r was partly moved out (D53)"),
  ("CloneP", "[Read] r is a borrow whose content is partly moved out ((⊥, σ1)): restore it before reading r (D127)"),
  ("CloneDP", "[Read] *r was partly moved out, and is not copied either (D127)"),
  ("StmtRP", "[Read] r is a borrow whose content is partly moved out ((⊥, σ1)): restore it before reading r (D127)"),
  ("ParP", "[Read] q is a borrow whose content is partly moved out ((⊥, σ2)): restore it before reading q (D127)"),
  ("ParCallP", "[Read] q is a borrow whose content is partly moved out ((⊥, σ2)): restore it before reading q (D127)"),
  ("ParReadAP", "[Read] q is a borrow whose content is partly moved out ((⊥, σ2)): restore it before reading q (D127)"),
  ("ParCallI", "unknown constant ParCallP"),
  ("NestP", "[Read] r is a borrow whose content is partly moved out (((⊥, σ1), σ2)): restore it before reading r (D127)"),
  ("BlkP", "[Read] r is a borrow whose content is partly moved out ((⊥, σ1)): restore it before reading r (D127)"),
  ("BlkTP", "[Read] r is a borrow whose content is partly moved out ((⊥, σ1)): restore it before reading r (D127)"),
  ("BlkPI", "unknown constant BlkP"),
  ("CloneOP", "[Read] x was partly moved out, and is not copied either (D127)"),
  ("EqOP", "[Read] x was partly moved out, and is not copied either (D127)"),
  ("EqDP", "[Read] *r was partly moved out, and is not copied either (D127)"),
  ("CloneUse", "[Read] *r was partly moved out, and is not copied either (D127)"),
  ("RebP", "[Borrow] *r was partly moved out (D53)")]


/-! ## The frame property (notes/frame-model.md)

A run changes the state below its own frame only through the borrows its frame holds; so a
borrow of a local can never reach a caller (F4), a closure writes only its own copy of what it
captured (F1), and re-pointing a borrow parameter at a local cuts it off from the caller's place
(F2). Each probe is a true statement, accepted, beside the false one, rejected. -/

ochr FrameModel uses Nats, Fixtures, WordType {
  -- F4: a borrow of a local escaping through a stuck call: at the generic call `TailM(&a)` closes
  -- off, its hole sits in `a`'s fill, and `a` dies while the result in flight borrows it
  reject def RetHole (x : &Nat) (n : Nat) : &Nat := (let a = n; TailM(&a))
  -- twin of RetHole: the stuck call borrows the parameter, which outlives the call
  def RetHoleOk (x : &Nat) (n : Nat) : &Nat := (let a = n; TailM(x))
  -- F1: a closure that assigns its capture assigns its own copy
  def ClosOwn (w : Word) : Id(Word, (let y = w; let f = (λ(u : Unit) : Unit => (y := Zero)); f(()); y), w) := refl
  -- twin of ClosOwn: the false statement that the closure wrote the caller's place
  reject def ClosOwnLie (w : Word) : Id(Word, (let y = w; let f = (λ(u : Unit) : Unit => (y := Zero)); f(()); y), Zero) := refl
  -- F2: re-pointing a borrow parameter at a local ends the old borrow (its content goes back to
  -- the caller) and writes after that land in the local, not in the caller's place
  def ReassignParam (x : &Nat) : Unit := (let a = 5; x := &a; *x := 7)
  def ReassignStmt (c0 : Nat) : Id(Nat, (let c = c0; ReassignParam(&c); c), c0) := refl
  -- twin of ReassignStmt: the false statement that the write reached the caller
  reject def ReassignLie (c0 : Nat) : Id(Nat, (let c = clone(c0); ReassignParam(&c); c), 7) := refl
}
