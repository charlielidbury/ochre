import Ochr.Examples.Nat
import Ochr.Examples.Fixtures

/-! # 7. Recursion and induction hypotheses

A recursive definition names its decreasing parameter with `by x`, and each recursive call
must pass, in that position, a strict part of the value `x` had on entry ([Rec], D17).
Without `by`, a definition cannot call itself (D31). Only a top-level definition is recursive: a
local function (a `fix` inside a body) may not declare `by` (D136), and a recursive helper is a
top-level function taking what it used from the enclosing body as parameters. A definition is
checked once, at its
*generic call*: each borrow parameter points to a fresh place holding an abstract value,
and the other parameters are abstract values ([Def]). The type of a recursive call is
computed in the caller's environment, after its arguments ([Call-type]), so a call about
`&p`, a borrow of a part of `*x`, is a statement about all of `*x`: this is what makes an
induction hypothesis useful without congruence lemmas.

Defined in RULES §5: [Def], [Call-type], [Rec]. -/

open Ochr.Test

ochr Recursion uses Nats, Fixtures {
  -- The pure theorem by recursion on a copy of the predecessor: the induction hypothesis is
  -- about `p` and the goal about `S(p)`, an equation between two successors, which `Eq`
  -- takes apart (injectivity, D52), so no congruence step is written. (`AddZero` in
  -- `Numbers` lends the predecessor field instead; without injectivity only that works.)
  def AddZeroCopy (x : Nat) : Id(Nat, Add(x, 0), x) by x := (
    match x {
      Z => refl,
      S p => AddZeroCopy(p),
    }
  )

  -- The paper's displays for `AddMZero`'s successor arm (§2): the goal `Eq(Nat, N(S(σ')), S(σ'))`
  -- runs one step to `Eq(Nat, S(N(σ')), S(σ'))`, which `Eq` takes apart to `Eq(Nat, N(σ'), σ')`
  -- (injectivity, D52); `Add(n, 0)` computes `N(σ')` for `n = σ'` ...
  def SuccGoal (n : Nat) (h : Eq(Nat, Add(S(n), 0), S(n))) : Eq(Nat, S(Add(n, 0)), S(n)) := h
  def InjStep (n : Nat) (h : Eq(Nat, S(Add(n, 0)), S(n))) : Eq(Nat, Add(n, 0), n) := h

  -- ... and the recursive call's statement, computed at the call site, is that proposition:
  -- the borrow of `p` sits inside `*x`, so the call observes `*x` whole, successor included.
  def CallSite (x : &Nat) : Nat := (
    match *x {
      Z => 0,
      S p => (
        let h : Eq(Nat, S(Add(p, 0)), S(p)) = AddMZero(&p);
        0
      ),
    }
  )

  -- (It is not the statement about `p` alone with the successor added on one side.)
  reject def CallSiteWrong (x : &Nat) : Nat := (
    match *x {
      Z => 0,
      S p => (
        let h : Eq(Nat, Add(p, 0), S(p)) = AddMZero(&p);
        0
      ),
    }
  )

  -- With the congruence convenience `cong` (outside the core) the copy works. The
  -- recursive call is inside a closure, and is still checked against the outer entry
  -- value: `q` is its predecessor.
  def AddZeroC (x : Nat) : Id(Nat, Add(x, 0), x) by x := (
    match x {
      Z => refl,
      S p => (
        let q = p;
        cong(S, (λ(u : Unit) : Id(Nat, Add(q, 0), q) => AddZeroC(q))(()))
      ),
    }
  )

  -- A local function is not recursive (D136): `Outer` was accepted before, with `go` checked
  -- at its own generic call. Lifted, `go` is a top-level function (`OuterGo`), here with
  -- nothing to take from `Outer`'s body.
  reject def Outer (x : &Nat) : Unit := (fix go (y : &Nat) : Unit by y := match *y { Z => (), S p => go(&p) })(x)
  def OuterGo (y : &Nat) : Unit by y := match *y { Z => (), S p => OuterGo(&p) }
  def OuterLift (x : &Nat) : Unit := OuterGo(x)

  -- A definition may not mention itself in its own type.
  reject def SelfType (n : Nat) : Id(Nat, SelfType(n), n) := refl

  -- ## What goes wrong without these rules
  -- Recursion is measured on entry values (D17): after `*x := S(*x)`, the predecessor of `*x`
  -- is the old `*x`, not a part of it, so `Loop` would never terminate, and `Bot'` would be a
  -- closed proof of `False`.
  reject def Loop (x : &Nat) (y : Nat) : False by x := (
    match y {
      Z => (
        *x := S(*x);
        match *x {
          Z => refl,
          S p => (
            let q = p;
            Loop(&p, q)
          ),
        }
      ),
      S q => (
        *x := S(*x);
        match *x {
          Z => refl,
          S p => Loop(&p, q),
        }
      ),
    }
  )

  reject def Bot' (n : Nat) : False := (
    let a = n;
    Loop(&a, n)
  )

  -- The same with an owned parameter, writing before the match ...
  reject def Loop2 (x : Nat) : False by x := (
    match x {
      Z => (
        x := S(Z);
        match x {
          Z => refl,
          S y => Loop2(y),
        }
      ),
      S p => (
        x := S(S(p));
        match x {
          Z => refl,
          S y => Loop2(y),
        }
      ),
    }
  )

  -- twin of Loop2: no write to `x`, so the recursive call is on a strict part of the entry value
  def Loop2Ok (x : Nat) : Unit by x := (
    match x {
      Z => (),
      S p => Loop2Ok(p),
    }
  )

  -- ... or after it, through the pattern variable.
  reject def Spin (x : Nat) : False by x := (
    match x {
      Z => (
        x := S(Z);
        match x {
          Z => refl,
          S y => Spin(y),
        }
      ),
      S y => (
        x := S(x);
        Spin(y)
      ),
    }
  )

  -- twin of Spin: no write to `x` after the match, so `y` is still a part of the entry value
  def SpinOk (x : Nat) : Unit by x := (
    match x {
      Z => (),
      S y => SpinOk(y),
    }
  )

  -- A local function that calls itself on its own argument: a local recursive function (D136);
  -- lifted, the call on its own argument is rejected by [Rec].
  reject def OuterBad (x : Nat) : Eq(Nat, 0, 1) := (fix go (y : Nat) : Eq(Nat, 0, 1) by y := go(y))(x)
  reject def OuterBadGo (y : Nat) : Eq(Nat, 0, 1) by y := OuterBadGo(y)

  -- twin of OuterBad: the local function calls itself on the predecessor, and states a true
  -- thing; accepted before D136, and lifted now
  reject def OuterBadOk (x : Nat) : Unit := (fix go (y : Nat) : Unit by y := match y { Z => (), S p => go(p) })(x)
  def OuterBadOkGo (y : Nat) : Unit by y := match y { Z => (), S p => OuterBadOkGo(p) }
  def OuterBadOkLift (x : Nat) : Unit := OuterBadOkGo(x)

  -- A recursive function may appear only as the head of a call. Passed as a value, it
  -- would escape the check on its arguments, and `Knot(0)` would be a closed proof of
  -- `False`.
  def Apply (f : Π(x : Nat). False) (x : Nat) : False := f(x)
  reject def Knot (x : Nat) : False by x := Apply(Knot, x)
  reject def KnotBoom : False := Knot(0)

  -- twin of Knot: the function is only the head of a call, on a strict part, and the statement is true
  def KnotOk (x : Nat) : Unit by x := (
    match x {
      Z => (),
      S p => KnotOk(p),
    }
  )

  -- twin of KnotBoom: the call is fine now that `KnotOk` is, and no longer proves `False`
  def KnotBoomOk : Unit := KnotOk(0)

  -- Recursive calls inside a nested closure are checked against the enclosing function's
  -- entry value: `y` is a fresh argument of the closure, not a part of `x`.
  reject def KnotL (x : Nat) : False by x := (
    let g = (λ(y : Nat) : False => KnotL(y));
    g(x)
  )

  reject def KnotLBoom : False := KnotL(0)

  -- D78: a recursive call is recognised by the name it is made through, not by comparing
  -- function values. `go` captures `n`; splitting on `n` inside `go`'s body refines the
  -- capture, so the refined closure no longer equals the one being checked, and its
  -- recursive calls went unchecked: `CapSplit` was accepted and `BoomCapSplit` was a closed
  -- proof of `False` (rec-model). Since D136 a local function is not recursive, so `CapSplit`
  -- is rejected at `go`'s `by`; lifted (`CapSplitGo`, `n` a parameter), [Rec] rejects it.
  reject def CapSplit (n : Nat) (x : Nat) : False := (fix go (y : Nat) : False by y := match n { Z => go(y), S q => go(y) })(x)
  reject def BoomCapSplit : False := CapSplit(0, 0)
  reject def CapSplitGo (n : Nat) (y : Nat) : False by y := match n { Z => CapSplitGo(Z, y), S q => CapSplitGo(S(q), y) }
  -- the same through a closure formed in each arm: capturing `go` moves it (a closure over
  -- non-copy data is not a copy), so the capture is recognised by the binding's mark, not its
  -- value; `BoomCapLam` was a closed proof of `False` too. Lifted, the closure captures the
  -- top-level function, and [Rec] rejects its call.
  reject def CapSplitLam (n : Nat) (x : Nat) : False := (fix go (y : Nat) : False by y := match n { Z => (let h = (λ(u : Unit) : False => go(clone(y))); h(())), S q => (let h = (λ(u : Unit) : False => go(clone(y))); h(())) })(x)
  reject def BoomCapLam : False := CapSplitLam(0, 0)
  reject def CapSplitLamGo (n : Nat) (y : Nat) : False by y := match n { Z => (let h = (λ(u : Unit) : False => CapSplitLamGo(Z, clone(y))); h(())), S q => (let h = (λ(u : Unit) : False => CapSplitLamGo(S(clone(q)), clone(y))); h(())) }
  -- twin of CapSplit: the same split on the capture, with recursive calls on a strict part of
  -- `y`; accepted before D136, and lifted now
  reject def CapSplitOk (n : Nat) (x : Nat) : Unit := (fix go (y : Nat) : Unit by y := match n { Z => match y { Z => (), S p => go(p) }, S q => match y { Z => (), S p => go(p) } })(x)
  def CapSplitOkGo (n : Nat) (y : Nat) : Unit by y := match n { Z => match y { Z => (), S p => CapSplitOkGo(Z, p) }, S q => match y { Z => (), S p => CapSplitOkGo(S(q), p) } }
  def CapSplitOkLift (n : Nat) (x : Nat) : Unit := CapSplitOkGo(n, x)
  -- twin of CapSplitLam: the closure formed in the arm recurses on a strict part; accepted
  -- before D136, and lifted now (a closure inside a top-level function may call it)
  reject def CapSplitLamOk (n : Nat) (x : Nat) : Unit := (fix go (y : Nat) : Unit by y := match n { Z => match y { Z => (), S p => (let h = (λ(u : Unit) : Unit => go(clone(p))); h(())) }, S q => () })(x)
  def CapSplitLamOkGo (n : Nat) (y : Nat) : Unit by y := match n { Z => match y { Z => (), S p => (let h = (λ(u : Unit) : Unit => CapSplitLamOkGo(Z, clone(p))); h(())) }, S q => () }
  def CapSplitLamOkLift (n : Nat) (x : Nat) : Unit := CapSplitLamOkGo(n, x)
  def CapSplitLamOkRuns : Eq(Unit, CapSplitLamOkLift(0, 3), ()) := refl

  -- twin of KnotL: inside the closure the recursive call is on `q`, a copy of `p`, a strict part of the entry value
  def KnotLOk (x : Nat) : Eq(Nat, Z, Z) by x := (
    match x {
      Z => refl,
      S p => (
        let q = p;
        let g = (λ(u : Unit) : Eq(Nat, Z, Z) => KnotLOk(q));
        g(())
      ),
    }
  )

  -- twin of KnotLBoom: calls `KnotLOk`, which is sound and proves only `Eq(Nat, Z, Z)`
  def KnotLBoomOk : Eq(Nat, Z, Z) := KnotLOk(0)

  -- Without `by`, the function is not in scope in its own body (D31).
  reject def LoopNoBy (x : Nat) : Eq(Nat, Z, S(Z)) := LoopNoBy(x)
  reject def LoopNoByBoom : Eq(Nat, Z, S(Z)) := LoopNoBy(Z)

  -- twin of LoopNoBy: declares `by x`, recurses on the predecessor, and states the true `Eq(Nat, Z, Z)`
  def LoopNoByOk (x : Nat) : Eq(Nat, Z, Z) by x := (
    match x {
      Z => refl,
      S p => LoopNoByOk(p),
    }
  )

  -- twin of LoopNoByBoom: the closed call is accepted, at the true statement
  def LoopNoByBoomOk : Eq(Nat, Z, Z) := LoopNoByOk(Z)

  -- ## Regressions: typing a sealed program keeps the [Rec] state
  -- A place with no stored type (a pattern variable, a closure's capture) is typed from its
  -- value, and a sealed program is typed by running it on a private copy, outside the
  -- enclosing functions. That run once wiped the positions that had survived the recursive
  -- calls so far, so no later recursive call was checked and each `Boom` below was a closed
  -- proof of `False` (the recCands fix, an implementation bug). Here the
  -- sealed program is the parameter `Le(σ, 1)` of the conjunction matched on (`Le` on `Nat`,
  -- the witness's own) ...
  def Le (a : Nat) (b : Nat) : Prop by a := (
    match a {
      Z => ⊤,
      S a' => match b {
        Z => False,
        S b' => Le(a', b'),
      },
    }
  )

  reject def Lie (n : Nat) (h : Le(n, 1) ∧ ⊤) : False by n := (
    match h {
      Intro(a, b) => Lie(n, h),
    }
  )

  reject def Boom : False := Lie(0, ⟨refl, refl⟩)

  -- twin of Lie: recurses on `p`, a strict part of `n`, and proves `Unit` rather than `False`
  def LieOk (n : Nat) (h : Le(Z, 1) ∧ ⊤) : Unit by n := (
    match h {
      Intro(a, b) => match n {
        Z => (),
        S p => LieOk(p, h),
      },
    }
  )

  -- twin of Boom: the closed call to the sound `LieOk`
  def BoomOk : Unit := LieOk(0, ⟨refl, refl⟩)

  -- ... and in the rest `n`, which `TailM`'s borrow left sealed, is captured by a closure
  -- that reads it in its type, in its body, or in an `Id`'s footprint.
  reject def LieCap (n : Nat) : False by n := (
    let r = TailM(&n);
    let f = (λ(y : &Nat) : U(n) => V(n));
    LieCap(n)
  )

  reject def BoomCap : False := LieCap(0)

  reject def LieRead (n : Nat) : False by n := (
    let r = TailM(&n);
    let f = (λ(y : Nat) : Nat => (let c = n; c));
    LieRead(n)
  )

  reject def BoomRead : False := LieRead(0)

  reject def LieId (n : Nat) : False by n := (
    let r = TailM(&n);
    let f = (λ(y : Nat) : Unit => (let h : Id(Unit, n := 0, n := 0) = refl; ()));
    LieId(n)
  )

  reject def BoomId : False := LieId(0)
}

/-- D136: the message for a local function `f` that declares `by x`. -/
private def localRec (f x : String) : String :=
  s!"[Rec] {f} declares `by {x}`, but a local function is not recursive (D136): recursion is for top-level definitions. Define {f} at the top level, with what it uses from the enclosing body as parameters"

#guard (run "Recursion" Recursion).rejectedWith [
  ("Outer", localRec "go" "y"), ("OuterBad", localRec "go" "y"), ("OuterBadOk", localRec "go" "y"),
  ("OuterBadGo", "[Rec] at OuterBadGo(σ0): the argument in the decreasing position"),
  ("CapSplit", localRec "go" "y"), ("CapSplitLam", localRec "go" "y"),
  ("CapSplitOk", localRec "go" "y"), ("CapSplitLamOk", localRec "go" "y"),
  ("CapSplitGo", "[Rec] at CapSplitGo(0, σ1): the argument in the decreasing position"),
  ("CapSplitLamGo", "[Rec] at CapSplitLamGo(0, σ1): the argument in the decreasing position")]


/-! ## A function being checked is not run (D135)

While a function is being checked, a call of it closes off at once, as a call of an unknown
function does, whatever path reaches it; its body runs only once the definition is accepted (in
Lean, too, the function being defined does not unfold inside its own body). Before, a typed
recursive call that passed [Rec] ran the body in place, untyped: code the check had not finished
with, whose calls no [Rec] test saw and whose unchecked arms ran. `Loop` ended "undecided (call
depth exceeded)" instead of being rejected, and `HAt` made an untested call before its rejection.

The rows are the class, hunted route by route: a typed call (`Loop`); a sealed program's head call
re-run after a later split (`ReRun`), a stuck block's re-run (`BlkRe`); a call through a λ's
capture, called or passed on (`LamCall`, `HoCall`); an inner recursive function, during its check
and after it (`InLoop`, `OutIn`, `OutIn2`); conversion of function values (`ConvLoop`); a borrow
in the decreasing position (`BLoop`); a call returning a type, which runs on a private copy
(`TLoop`); a sealed function's type, read by typing its program from the empty state (`FR`).
Each now meets [Rec] at the call it should. The function being checked is found by its code, not
by its value: a split on a local function's capture (`CapRe`, `CapLam`, `Nest`), or on what a
captured proof's type mentions (`CapPrf`), changes the value but not the code, and every route
but the name reaches the value only.

The loss, of one kind: a body that needs its own recursive call to compute (`Sel`: inside `Sel`,
with `m` refined to `Z`, `Sel(m)` is `⌈Sel(0)⌉`, not `0`). The same equation stated after the
definition holds (`Sel2After`), a well-founded definition computes once accepted (`OkRuns`), and
an inner function, once its own check has ended, runs inside the outer one's (`InnerRuns`).

Since D136 a local function is not recursive, so every row here whose recursive function is local
(`CapSel0` to `CapPrf0`, `CapBlkSel`, `CapLam`, `CapLamSel`, `InLoop`, `OutIn` to `Nest`) is
rejected at that function's `by`, before any of these routes is reached; lifted, a local function
is a top-level one whose captures are parameters, and its routes are the global rows'. `InnerRuns`
was accepted, and is lost; its lifted form `InnerRunsLift` is accepted. -/

ochr UnderCheck uses Nats {
  inductive BB := TT | FF
  inductive Box (A : Type) := MkBox(x : A)
  def App (f : Π(u : Unit). Nat) : Nat := f(())
  def Le (a : Nat) (b : Nat) : Prop by a := match a { Z => ⊤, S(a') => match b { Z => False, S(b') => Le(a', b'), }, }

  -- a typed call: its in-place run reached the arm `FF`, unchecked, and made an untested call
  reject def HAt (p : BB) (n : Nat) : Nat by n := match p {
    TT => match n { Z => Z, S(m) => match m { Z => (HAt(FF, Z); Z), S(k) => Z, }, },
    FF => match n { Z => (HAt(TT, S(S(S(Z)))); Z), S(m) => Z, }, }
  reject def H2 (p : BB) (n : Nat) : Nat by n := match p {
    TT => match n { Z => Z, S(m) => H2(FF, m), },
    FF => H2(TT, n), }
  reject def Loop (p : BB) (n : Nat) : Nat by n := match p {
    TT => match n { Z => Z, S(m) => Loop(FF, m), },
    FF => Loop(FF, n), }
  def Ok (p : BB) (n : Nat) : Nat by n := match p {
    TT => match n { Z => Z, S(m) => match m { Z => Ok(FF, m), S(k) => Ok(FF, m), }, },
    FF => match n { Z => Z, S(m) => Ok(TT, m), }, }
  def OkRuns : Eq(Nat, Ok(TT, S(S(S(Z)))), Z) := refl
  -- the loss: the body states an equation about its own call
  reject def Sel (n : Nat) : Nat by n := match n {
    Z => Z,
    S(m) => match m { Z => (let e : Eq(Nat, Sel(m), Z) = refl; Z), S(k) => Z, }, }
  def Sel2 (n : Nat) : Nat by n := match n {
    Z => Z,
    S(m) => match m { Z => (let r = Sel2(m); Z), S(k) => Z, }, }
  def Sel2After : Eq(Nat, Sel2(Z), Z) := refl

  -- a sealed program's head call, re-run after a later split
  reject def ReRun (p : BB) (n : Nat) : Nat by n := match p {
    TT => match n { Z => Z, S(m) => (let r = ReRun(FF, clone(m)); match m { Z => r, S(k) => r, }), },
    FF => match n { Z => ReRun(FF, n), S(k) => Z, }, }
  reject def ReSel (n : Nat) : Nat by n := match n {
    Z => Z,
    S(m) => (let r = ReSel(clone(m)); match m { Z => (let e : Eq(Nat, r, Z) = refl; Z), S(k) => Z, }), }
  -- ... of a local function: the split refines the argument only
  reject def CapSel0 (n : Nat) (x : Nat) : Nat := (fix go (y : Nat) : Nat by y := match y {
    Z => Z,
    S(p) => (let r = go(clone(p)); match p { Z => (let e : Eq(Nat, r, Z) = refl; Z), S(k) => Z, }), })(x)
  -- ... and a split refines its capture `n`, so its value is no longer the frame's
  reject def CapSel (n : Nat) (x : Nat) : Nat := (fix go (y : Nat) : Nat by y := match y {
    Z => Z,
    S(p) => (let r = go(clone(p)); match n { Z => match p { Z => (let e : Eq(Nat, r, Z) = refl; Z), S(k) => Z, }, S(j) => Z, }), })(x)
  reject def CapRe (n : Nat) (x : Nat) : Nat := (fix go (p : BB) (y : Nat) : Nat by y := match p {
    TT => match y { Z => Z, S(m) => (let r = go(FF, clone(m)); match n { Z => match m { Z => r, S(k) => r, }, S(j) => r, }), },
    FF => match y { Z => go(FF, y), S(k) => Z, }, })(TT, x)
  -- ... and its code holds a captured proof's type, `Le(n, 5)`, which the split refines
  reject def CapPrf (n : Nat) (h : Le(n, 5)) (x : Nat) : Nat := (fix go (y : Nat) : Nat by y := match y {
    Z => Z,
    S(p) => (let k = h; let r = go(clone(p)); match n { Z => match p { Z => (let e : Eq(Nat, r, Z) = refl; Z), S(j) => Z, }, S(j) => Z, }), })(x)
  reject def CapPrf0 (n : Nat) (h : Le(n, 5)) (x : Nat) : Nat := (fix go (y : Nat) : Nat by y := match y {
    Z => Z,
    S(p) => (let k = h; let r = go(clone(p)); match p { Z => (let e : Eq(Nat, r, Z) = refl; Z), S(j) => Z, }), })(x)

  -- a stuck block's re-run after a later split
  reject def BlkRe (p : BB) (q : BB) (n : Nat) : Nat by n := match p {
    TT => match n { Z => Z, S(m) => (let r = match q { TT => BlkRe(FF, TT, clone(m)), FF => Z, }; match q { TT => match m { Z => r, S(k) => r, }, FF => r, }), },
    FF => match n { Z => BlkRe(FF, TT, n), S(k) => Z, }, }
  reject def BlkSel (q : BB) (n : Nat) : Nat by n := match n {
    Z => Z,
    S(m) => (let r = match q { TT => BlkSel(TT, clone(m)), FF => Z, }; match q { TT => match m { Z => (let e : Eq(Nat, r, Z) = refl; Z), S(k) => Z, }, FF => Z, }), }
  reject def CapBlkSel (n : Nat) (b : BB) (x : Nat) : Nat := (fix go (q : BB) (y : Nat) : Nat by y := match y {
    Z => Z,
    S(m) => (let r = match q { TT => go(TT, clone(m)), FF => Z, }; match n { Z => match q { TT => match m { Z => (let e : Eq(Nat, r, Z) = refl; Z), S(k) => Z, }, FF => Z, }, S(j) => Z, }), })(b, x)

  -- a call through a λ's capture: the λ called, or passed to a complete higher-order function
  reject def LamCall (p : BB) (n : Nat) : Nat by n := match p {
    TT => match n { Z => Z, S(m) => (let g = (λ(u : Unit) : Nat => LamCall(FF, clone(m))); g(())), },
    FF => LamCall(FF, n), }
  reject def LamSel (n : Nat) : Nat by n := match n {
    Z => Z,
    S(m) => match m { Z => (let g = (λ(u : Unit) : Nat => LamSel(clone(m))); let e : Eq(Nat, g(()), Z) = refl; Z), S(k) => Z, }, }
  reject def HoCall (p : BB) (n : Nat) : Nat by n := match p {
    TT => match n { Z => Z, S(m) => App(λ(u : Unit) : Nat => HoCall(FF, clone(m))), },
    FF => HoCall(FF, n), }
  reject def HoSel (n : Nat) : Nat by n := match n {
    Z => Z,
    S(m) => match m { Z => (let e : Eq(Nat, App(λ(u : Unit) : Nat => HoSel(clone(m))), Z) = refl; Z), S(k) => Z, }, }
  -- ... of a local function whose capture a split has refined (the λ's call of it is untyped)
  reject def CapLam (n : Nat) (x : Nat) : Nat := (fix go (p : BB) (y : Nat) : Nat by y := match n {
    Z => match p { TT => match y { Z => Z, S(m) => (let g = (λ(u : Unit) : Nat => go(FF, clone(m))); g(())), }, FF => go(FF, y), },
    S(j) => Z, })(TT, x)
  reject def CapLamSel (n : Nat) (x : Nat) : Nat := (fix go (y : Nat) : Nat by y := match n {
    Z => match y { Z => Z, S(m) => match m { Z => (let g = (λ(u : Unit) : Nat => go(clone(m))); let e : Eq(Nat, g(()), Z) = refl; Z), S(k) => Z, }, },
    S(j) => Z, })(x)

  -- an inner recursive function: its own calls during its check ...
  reject def InLoop (q : Nat) : Nat := (fix go (p : BB) (n : Nat) : Nat by n := match p {
    TT => match n { Z => Z, S(m) => go(FF, m), },
    FF => go(FF, n), })(TT, q)
  -- ... its calls of the outer one during its check ...
  reject def OutIn (p : BB) (n : Nat) : Nat by n := match p {
    TT => match n { Z => Z, S(m) => (fix go (y : Nat) : Nat by y := match y { Z => OutIn(FF, clone(m)), S(k) => go(k), })(Z), },
    FF => OutIn(FF, n), }
  -- ... and after it: it runs (it is accepted code), and its calls of the outer one close off
  reject def OutIn2 (p : BB) (n : Nat) : Nat by n := match p {
    TT => match n { Z => Z, S(m) => (fix go (y : Nat) : Nat by y := match y { Z => OutIn2(FF, clone(m)), S(k) => go(k), })(S(Z)), },
    FF => OutIn2(FF, n), }
  reject def OutInSel (n : Nat) : Nat by n := match n {
    Z => Z,
    S(m) => match m { Z => (let e : Eq(Nat, (fix go (y : Nat) : Nat by y := match y { Z => OutInSel(clone(m)), S(k) => go(k), })(S(Z)), Z) = refl; Z), S(k) => Z, }, }
  reject def InnerRuns (n : Nat) : Nat by n := match n {
    Z => Z,
    S(m) => (let e : Eq(Nat, (fix go (y : Nat) : Nat by y := match y { Z => Z, S(k) => go(k), })(S(S(Z))), Z) = refl; InnerRuns(m)), }
  def InnerGo (y : Nat) : Nat by y := match y { Z => Z, S(k) => InnerGo(k), }
  def InnerRunsLift (n : Nat) : Nat by n := match n {
    Z => Z,
    S(m) => (let e : Eq(Nat, InnerGo(S(S(Z))), Z) = refl; InnerRunsLift(m)), }
  -- ... the outer one local, its capture refined, called by the inner one after the inner's check
  reject def Nest (n : Nat) (x : Nat) : Nat := (fix outer (p : BB) (y : Nat) : Nat by y := match n {
    Z => match p { TT => match y { Z => Z, S(m) => (fix go (k : Nat) : Nat by k := match k { Z => outer(FF, clone(m)), S(j) => go(j), })(Z), }, FF => outer(FF, y), },
    S(j) => Z, })(TT, x)

  -- conversion of function values runs both λs' generic calls
  reject def ConvFn (n : Nat) : Nat by n := match n {
    Z => Z,
    S(m) => match m { Z => (let e : Eq(Π(u : Unit). Nat, λ(u : Unit) : Nat => ConvFn(clone(m)), λ(u : Unit) : Nat => (let z = ConvFn(clone(m)); Z)) = refl; Z), S(k) => Z, }, }
  reject def ConvLoop (p : BB) (n : Nat) : Nat by n := match p {
    TT => match n { Z => Z, S(m) => (let e : Eq(Π(u : Unit). Nat, λ(u : Unit) : Nat => ConvLoop(FF, clone(m)), λ(u : Unit) : Nat => ConvLoop(FF, clone(m))) = refl; Z), },
    FF => ConvLoop(FF, n), }

  -- a borrow in the decreasing position
  reject def BLoop (p : BB) (x : &Nat) : Nat by x := match p {
    TT => match *x { Z => Z, S(m) => BLoop(FF, &m), },
    FF => BLoop(FF, x), }
  reject def BSel (x : &Nat) : Nat by x := match *x {
    Z => Z,
    S(m) => match m { Z => (let e : Eq(Nat, BSel(&m), Z) = refl; Z), S(k) => Z, }, }

  -- erased calls: a call returning a proof returns at once (unchanged); one returning a type runs
  reject def PLoop (p : BB) (n : Nat) : Eq(Nat, Z, Z) by n := match p {
    TT => match n { Z => refl, S(m) => PLoop(FF, m), },
    FF => PLoop(FF, n), }
  reject def TLoop (p : BB) (n : Nat) : Type by n := match p {
    TT => match n { Z => Nat, S(m) => TLoop(FF, m), },
    FF => TLoop(FF, n), }
  reject def TSel (n : Nat) : Type by n := match n {
    Z => Nat,
    S(m) => match m { Z => (let x : TSel(m) = Z; Nat), S(k) => Nat, }, }

  -- a sealed value's type: calling a sealed function types its program from the empty state
  reject def STy (p : BB) (n : Nat) : Nat by n := match p {
    TT => match n { Z => Z, S(m) => (let b = MkBox(STy(FF, m)); Z), },
    FF => STy(FF, n), }
  def STyOk (p : BB) (n : Nat) : Nat by n := match p {
    TT => match n { Z => Z, S(m) => (let b = MkBox(STyOk(FF, m)); Z), },
    FF => match n { Z => Z, S(m) => STyOk(FF, m), }, }
  reject def FR (p : BB) (n : Nat) : (Π(u : Unit). Nat) by n := match p {
    TT => match n { Z => λ(u : Unit) : Nat => Z, S(m) => (let h = FR(FF, m); let z = h(()); λ(u : Unit) : Nat => Z), },
    FF => FR(FF, n), }
  def FROk (p : BB) (n : Nat) : (Π(u : Unit). Nat) by n := match p {
    TT => match n { Z => λ(u : Unit) : Nat => Z, S(m) => (let h = FROk(FF, m); let z = h(()); λ(u : Unit) : Nat => Z), },
    FF => match n { Z => λ(u : Unit) : Nat => Z, S(m) => FROk(FF, m), }, }
}

private def recAt (f a : String) : String :=
  s!"[Rec] at {f}({a}): the argument in the decreasing position is not a strict subterm of that parameter's entry value as refined so far"
private def sealedSelf (e : String) : String := s!"the ascribed term has type ⊤, expected Eq(Nat, ⌈{e}"

#guard (run "UnderCheck" UnderCheck).rejectedWith [
  ("HAt", recAt "HAt" "TT, 3"), ("H2", recAt "H2" "TT, σ1"), ("Loop", recAt "Loop" "FF, σ1"),
  ("Sel", sealedSelf "Sel(0)⌉, 0)"),
  ("ReRun", recAt "ReRun" "FF, 0"), ("ReSel", sealedSelf "ReSel(0)⌉, 0)"),
  ("CapSel0", localRec "go" "y"),
  ("CapSel", localRec "go" "y"),
  ("CapRe", localRec "go" "y"),
  ("CapPrf", localRec "go" "y"),
  ("CapPrf0", localRec "go" "y"),
  ("BlkRe", recAt "BlkRe" "FF, TT, 0"), ("BlkSel", sealedSelf "BlkSel(TT, 0)⌉, 0)"),
  ("CapBlkSel", localRec "go" "y"),
  ("LamCall", recAt "LamCall" "FF, σ1"), ("LamSel", sealedSelf "LamSel(0)⌉, 0)"),
  ("HoCall", recAt "HoCall" "FF, σ1"), ("HoSel", sealedSelf "HoSel(0)⌉, 0)"),
  ("CapLam", localRec "go" "y"),
  ("CapLamSel", localRec "go" "y"),
  ("InLoop", localRec "go" "n"),
  ("OutIn", localRec "go" "y"), ("OutIn2", localRec "go" "y"), ("OutInSel", localRec "go" "y"),
  ("InnerRuns", localRec "go" "y"),
  ("Nest", localRec "outer" "y"),
  ("ConvFn", "the ascribed term has type ⊤, expected Eq(Π(u : Unit). Nat, fix _ (u : Unit) : Nat := ConvFn(clone(κ1.0)) where κ1 = 1,"),
  ("ConvLoop", recAt "ConvLoop" "FF, σ1"),
  ("BLoop", recAt "BLoop" "FF, borrow_0 σ1"), ("BSel", sealedSelf "let c1 = 0; BSel(&c1)⌉, 0)"),
  ("PLoop", recAt "PLoop" "FF, σ1"), ("TLoop", recAt "TLoop" "FF, σ1"),
  ("TSel", "the ascribed term has type Nat, expected ⌈TSel(0)⌉"),
  ("STy", recAt "STy" "FF, σ1"), ("FR", recAt "FR" "FF, σ1")]


/-! ## A local function is not recursive (D136)

Recursion is for top-level definitions. A local function (a `fix` formed inside a body or a type)
may not declare `by`, and without `by` it cannot name itself (D31), so no local function calls
itself. Lean's kernel has no local recursion either: `let rec` and `where` are lifted to top-level
definitions, with what they capture as parameters, and that is how a recursive helper is written
here (the `…Lift` rows). The consistency proof's model treats the function being checked as "some
function good on smaller arguments" for top-level definitions only; a local recursive function had
no counterpart there, and it is what cost the closed proof of `False` of D78 and the recognition by
code of D135.

A local function has no entry on the [Rec] stack, whose entries are the functions being checked
that declare `by`: the top-level definition. So a λ being checked is not taken for an accepted
closure of the same code (`SameCode`, rejected before, when every function being checked had an
entry and D135 compared code).

The rows: the rule, where a local function is checked, in a constant, inside a local or a top-level
function, passed to a higher-order function, and in a type (`LocConst` … `HoLoc`, `TopIn`, `Twice`,
`TyCod` … `TyLoop`), each beside its lifted form, accepted where it is well founded. A helper that
calls the enclosing top-level function back cannot become a second top-level function calling the
first (top-level functions are not mutually recursive): it takes that call as a function
(`TopInLift`), or its value when the helper makes it more than once on a path (`TwiceLift`). Then
the routes by which a local function without `by` could reach itself, each already closed: by D31
(`Self1` … `Self5`, `InOut`), and by capture (`Knot1`: a closure captures no borrow; `Knot2`: a
captured function is a snapshot, so reassigning the place it came from ties no knot). -/

ochr LocalRec uses Nats {
  def App (f : Π(u : Unit). Nat) : Nat := f(())
  def Ap1 (f : Π(y : Nat). Nat) (x : Nat) : Nat := f(x)
  def Go (y : Nat) : Nat by y := match y { Z => Z, S(p) => Go(p), }
  -- the rule: a local function declaring `by`, in a constant, at a call on its own argument,
  -- inside a local function or around one, passed to a higher-order function
  reject def LocConst : Nat := (fix go (y : Nat) : Nat by y := match y { Z => Z, S(p) => go(p), })(3)
  reject def LocLoop (x : Nat) : Nat := (fix go (y : Nat) : Nat by y := go(y))(x)
  reject def InBy (x : Nat) : Nat := (fix outer (y : Nat) : Nat := (fix inner (z : Nat) : Nat by z := match z { Z => Z, S(p) => inner(p), })(y))(x)
  reject def InOutBy (x : Nat) : Nat := (fix outer (y : Nat) : Nat by y := (fix inner (z : Nat) : Nat := match z { Z => Z, S(p) => outer(p), })(y))(x)
  reject def HoLoc (n : Nat) (x : Nat) : Nat := Ap1((fix go (y : Nat) : Nat by y := match y { Z => clone(n), S(k) => go(k), }), x)
  -- ... lifted: what the local function captured becomes a parameter; a lifted call on its own
  -- argument, or on a part of an inner function's argument, is rejected by [Rec] as before
  def LocConstLift : Nat := Go(3)
  def LocConstRuns : Eq(Nat, LocConstLift, 0) := refl
  reject def LocLoopGo (y : Nat) : Nat by y := LocLoopGo(y)
  def InByLift (x : Nat) : Nat := (fix outer (y : Nat) : Nat := Go(y))(x)
  reject def InOutGo (y : Nat) : Nat by y := (fix inner (z : Nat) : Nat := match z { Z => Z, S(p) => InOutGo(p), })(y)
  def HoGo (n : Nat) (y : Nat) : Nat by y := match y { Z => n, S(k) => HoGo(n, k), }
  def HoLift (n : Nat) (x : Nat) : Nat := Ap1(λ(y : Nat) : Nat => HoGo(clone(n), y), x)
  def HoLiftRuns : Eq(Nat, HoLift(4, 2), 4) := refl
  -- a local function that calls the enclosing top-level one back: lifted, it takes that call as
  -- a function, or its value when it makes the call more than once on a path
  reject def TopIn (n : Nat) : Nat by n := match n { Z => Z, S(m) => (fix go (y : Nat) : Nat by y := match y { Z => TopIn(clone(m)), S(k) => go(k), })(S(Z)), }
  def TopInGo (f : Π(u : Unit). Nat) (y : Nat) : Nat by y := match y { Z => f(()), S(k) => TopInGo(f, k), }
  def TopInLift (n : Nat) : Nat by n := match n { Z => Z, S(m) => TopInGo(λ(u : Unit) : Nat => TopInLift(clone(m)), S(Z)), }
  def TopInRuns : Eq(Nat, TopInLift(3), 0) := refl
  reject def Twice (n : Nat) : Nat by n := match n { Z => S(Z), S(m) => (fix go (y : Nat) : Nat by y := match y { Z => Twice(clone(m)), S(k) => Add(Twice(clone(m)), go(k)) })(S(Z)), }
  def TwiceGo (r : Nat) (y : Nat) : Nat by y := match y { Z => r, S(k) => Add(clone(r), TwiceGo(r, k)), }
  def TwiceLift (n : Nat) : Nat by n := match n { Z => S(Z), S(m) => TwiceGo(TwiceLift(clone(m)), S(Z)), }
  def TwiceRuns : Eq(Nat, TwiceLift(2), 4) := refl
  -- in a type: a codomain, a parameter's type, a `let`'s annotation, the sides of `Eq` and `Id`,
  -- a Π-type; and lifted
  reject def TyCod (n : Nat) : (let k = (fix go (y : Nat) : Nat by y := match y { Z => Z, S(p) => go(p), })(clone(n)); Nat) := Z
  reject def TyPar (n : Nat) (m : (let k = (fix go (y : Nat) : Nat by y := match y { Z => Z, S(p) => go(p), })(clone(n)); Nat)) : Nat := Z
  reject def TyLet (n : Nat) : Nat := (let a : (let k = (fix go (y : Nat) : Nat by y := match y { Z => Z, S(p) => go(p), })(clone(n)); Nat) = Z; a)
  reject def TyEq (n : Nat) : Nat := (let e : Eq(Nat, (fix go (y : Nat) : Nat by y := match y { Z => Z, S(p) => go(p), })(clone(n)), (fix go (y : Nat) : Nat by y := match y { Z => Z, S(p) => go(p), })(clone(n))) = refl; Z)
  reject def TyId (n : Nat) : Nat := (let e : Id(Nat, (fix go (y : Nat) : Nat by y := match y { Z => Z, S(p) => go(p), })(Z), Z) = refl; Z)
  reject def TyPi (n : Nat) : Type := Π(u : Unit). (let k = (fix go (y : Nat) : Nat by y := match y { Z => Z, S(p) => go(p), })(clone(n)); Nat)
  reject def TyLoop (n : Nat) : (let k = (fix go (y : Nat) : Nat by y := go(y))(clone(n)); Nat) := Z
  def TyCodLift (n : Nat) : (let k = Go(clone(n)); Nat) := Z
  def TyEqLift (n : Nat) : Nat := (let e : Eq(Nat, Go(clone(n)), Go(clone(n))) = refl; Z)
  def TyIdLift (n : Nat) : Nat := (let e : Id(Nat, Go(Z), Z) = refl; Z)
  -- the routes by which a local function without `by` could reach itself, closed by D31: a call,
  -- a nested λ, a stuck block's arm, a λ passed to a higher-order function, an assignment, and an
  -- inner function calling the outer one
  reject def Self1 (x : Nat) : Nat := (fix go (y : Nat) : Nat := go(y))(x)
  reject def Self2 (x : Nat) : Nat := (fix go (y : Nat) : Nat := (λ(u : Unit) : Nat => go(clone(y)))(()))(x)
  reject def Self3 (x : Nat) : Nat := (fix go (y : Nat) : Nat := (let r = match y { Z => Z, S(p) => go(p), }; r))(x)
  reject def Self4 (x : Nat) : Nat := (fix go (y : Nat) : Nat := App(λ(u : Unit) : Nat => go(clone(y))))(x)
  reject def Self5 (x : Nat) : Nat := (fix go (y : Nat) : Nat := (go := (λ(z : Nat) : Nat => z); y))(x)
  reject def InOut (x : Nat) : Nat := (fix outer (y : Nat) : Nat := (fix inner (z : Nat) : Nat := match z { Z => Z, S(p) => outer(p), })(y))(x)
  -- ... and by capture: a closure captures no borrow, and a captured function is a snapshot, so
  -- reassigning the place it came from ties no knot
  reject def Knot1 (x : Nat) : Nat := (let c = Z; let r = &c; let g = (λ(u : Unit) : Nat => clone(*r)); g(()))
  def Knot2 (x : Nat) : Nat := (let f = (λ(y : Nat) : Nat => Z); let g = (λ(y : Nat) : Nat => f(y)); f := g; f(x))
  def Knot2Runs : Eq(Nat, Knot2(5), Z) := refl
  -- a later local function calls an earlier one
  def Sib (x : Nat) : Nat := (let f = (λ(y : Nat) : Nat => y); let g = (λ(y : Nat) : Nat => f(y)); g(x))
  def SibRuns : Eq(Nat, Sib(3), 3) := refl
  -- a λ being checked calls an accepted closure of the same code (`l` and `k` are both
  -- `λ(y). let e : Eq(Nat, κ1(clone(y)), y) = refl; y`): rejected while local functions had a
  -- [Rec] frame and D135 found the function being checked by its code, which took `k` for `l`
  -- and closed its call off; a local function has no frame now, and `k` runs
  def SameCode (n : Nat) : Nat := (
    let k0 = (λ(y : Nat) : Nat => y);
    let k = (λ(y : Nat) : Nat => (let e : Eq(Nat, k0(clone(y)), y) = refl; y));
    let l = (λ(y : Nat) : Nat => (let e : Eq(Nat, k(clone(y)), y) = refl; y));
    l(n))
  def SameCodeRuns : Eq(Nat, SameCode(3), 3) := refl
}

private def notInScope (f : String) : String :=
  s!"{f} is not in scope in its own body: it declares no decreasing parameter (`by x`), so it is not recursive (D31)"

#guard (run "LocalRec" LocalRec).rejectedWith [
  ("LocConst", localRec "go" "y"), ("LocLoop", localRec "go" "y"), ("InBy", localRec "inner" "z"),
  ("InOutBy", localRec "outer" "y"), ("HoLoc", localRec "go" "y"), ("TopIn", localRec "go" "y"),
  ("Twice", localRec "go" "y"),
  ("TyCod", localRec "go" "y"), ("TyPar", localRec "go" "y"), ("TyLet", localRec "go" "y"),
  ("TyEq", localRec "go" "y"), ("TyId", localRec "go" "y"), ("TyPi", localRec "go" "y"),
  ("TyLoop", localRec "go" "y"),
  ("LocLoopGo", recAt "LocLoopGo" "σ0"), ("InOutGo", recAt "InOutGo" "σ2"),
  ("Self1", notInScope "go"), ("Self2", notInScope "go"), ("Self3", notInScope "go"),
  ("Self4", notInScope "go"), ("Self5", notInScope "go"), ("InOut", notInScope "outer"),
  ("Knot1", "a closure or Π-type captures the borrow r (closures capture no borrows")]


/-! ## A function being checked is named by its global in a closure's code (D139)

A recursive definition may call itself from a λ formed in its body (fix L1: it occurs there only
as the head of a call). The λ does not keep the function among its captures: its code names it by
its global, `CL0(j, …)`, and its captures, their declared types and its Π-type's captures leave it
out. A Π-type naming it (its codomain, a λ's parameter type) is formed the same way. The variable
that held it is still taken as every capture is, so forming the closure moves it as before (`MV`).
The consistency proof reads a function under check as "some function good on smaller arguments",
which is not a member of its declared type: it can be called, not held as a value at that type.

The rows: each route by which the function came to rest in the state inside a closure or a Π-type
(the hunt of D139: a λ called, a λ calling it from its own body, nested λs, a λ in a type, a
Π-type, a λ's parameter type or codomain, a field, an argument of a higher-order function or of
the function itself, a deferred type, a generalisation record, a sealed re-run, a comparison of
function values, a λ inside a stuck block's arm), with closed runs; the function as a value other
than a call's head, rejected by fix L1 (`HO1` … `HO10`); and the printed code and types that show
the rule (`…Code`, `…Ty`). `NL`, a λ nested in a λ calling the function, was rejected before
(D53: the inner λ moved the outer one's capture of the function) and is accepted now. A stuck
block still takes the function as a parameter (`BL`): that is left to the decision on blocks. A
guard over every state the block's checks record, at every call depth and inside private copies,
asserts that no closure or Π-type keeps a function under check, and that no capture binding holds
one or carries its mark. -/

ochr NamedByGlobal uses Nats {
  inductive Bx (A : Type) := MkBx(x : A)
  def Ap1 (f : Π(j : Nat). Nat) (a : Nat) : Nat := f(a)
  def Ap2 (f : Π(a : Nat) (b : Nat). Nat) (a : Nat) (b : Nat) : Nat := f(a, b)
  -- a λ called; a λ calling it from its own body; nested λs (rejected by D53 before)
  def CL0 (m : Nat) (n : Nat) : Nat by n := (let g = (λ(j : Nat) : Nat => match n { Z => Z, S(k) => CL0(j, clone(k)), }); g(m))
  def CL0Runs : Eq(Nat, CL0(3, 2), 0) := refl
  def CLIn (m : Nat) (n : Nat) : Nat by n := match n { Z => Z, S(k) => (let g = (λ(j : Nat) : Nat => (let x = CLIn(j, clone(k)); x)); g(m)), }
  def CLInRuns : Eq(Nat, CLIn(3, 2), 0) := refl
  def NL (m : Nat) (n : Nat) : Nat by n := match n { Z => Z, S(k) => (let g = (λ(u : Unit) : Nat => (let d = clone(k); let h = (λ(j : Nat) : Nat => NL(j, clone(d))); h(Z))); g(())), }
  def NLRuns : Eq(Nat, NL(3, 2), 0) := refl
  -- in a type: λs as the sides of an equation, a Π-type, a λ's parameter type and codomain, a
  -- Π-typed annotation
  def TyL (m : Nat) (n : Nat) : Nat by n := match n { Z => Z, S(k) => (let e : Eq(Π(j : Nat). Nat, λ(j : Nat) : Nat => TyL(j, clone(k)), λ(j : Nat) : Nat => TyL(j, clone(k))) = refl; TyL(m, k)), }
  def PiC (m : Nat) (n : Nat) : Nat by n := match n { Z => Z, S(k) => (let T = (Π(j : Nat). Eq(Nat, PiC(j, clone(k)), Z)); PiC(m, k)), }
  def LP (m : Nat) (n : Nat) : Nat by n := match n { Z => Z, S(k) => (let g = (λ(e : Eq(Nat, LP(clone(m), clone(k)), Z)) : Nat => Z); Z), }
  def LC (m : Nat) (n : Nat) : Nat by n := match n { Z => Z, S(k) => (let g = (λ(j : Nat) : Eq(Nat, LC(j, clone(k)), LC(j, clone(k))) => refl); LC(m, k)), }
  def PiH (m : Nat) (n : Nat) : Nat by n := match n { Z => Z, S(k) => (let h : Π(j : Nat). Eq(Nat, PiH(j, clone(k)), PiH(j, clone(k))) = (λ(j : Nat) : Eq(Nat, PiH(j, clone(k)), PiH(j, clone(k))) => refl); PiH(m, k)), }
  -- held: in a field, as an argument of a higher-order function and of the function itself
  def BX (m : Nat) (n : Nat) : Nat by n := match n { Z => Z, S(k) => (let b = MkBx(λ(j : Nat) : Nat => BX(j, clone(k))); match b { MkBx(f) => f(m) }), }
  def BXRuns : Eq(Nat, BX(3, 2), 0) := refl
  def HoL (m : Nat) (n : Nat) : Nat by n := match n { Z => Z, S(k) => Ap1(λ(j : Nat) : Nat => HoL(j, clone(k)), m), }
  def HoLRuns : Eq(Nat, HoL(3, 2), 0) := refl
  def FA (f : Π(j : Nat). Nat) (n : Nat) : Nat by n := match n { Z => f(Z), S(k) => (let c = clone(k); FA(λ(j : Nat) : Nat => FA(λ(i : Nat) : Nat => i, clone(c)), k)), }
  def FARuns : Eq(Nat, FA(λ(i : Nat) : Nat => S(i), 2), 0) := refl
  -- a deferred type, a generalisation record, a sealed re-run, a comparison of function values
  def DT (m : Nat) (n : Nat) : Nat by n := match n { Z => Z, S(k) => (let g = (λ(j : Nat) : Nat => DT(j, clone(k))); let h = (λ(u : Unit) : Nat => (let r = g(Z); r)); h(())), }
  def DTRuns : Eq(Nat, DT(3, 2), 0) := refl
  def GR (m : Nat) (n : Nat) : Nat by n := match n { Z => Z, S(k) => (let g = (λ(j : Nat) : Nat => match j { Z => GR(Z, clone(k)), S(q) => Z, }); let r = g(clone(m)); match r { Z => Z, S(q) => Z, }), }
  def SR (m : Nat) (n : Nat) : Nat by n := match n { Z => Z, S(k) => (let g = (λ(j : Nat) : Nat => match j { Z => SR(Z, clone(k)), S(q) => Z, }); let r = g(clone(m)); match m { Z => r, S(q) => Z, }), }
  def CV (m : Nat) (n : Nat) : Nat by n := match n { Z => Z, S(k) => (let e : Eq(Π(j : Nat). Nat, λ(j : Nat) : Nat => CV(j, clone(k)), λ(j : Nat) : Nat => (let z = CV(j, clone(k)); z)) = refl; Z), }
  -- the function's own sealed call, generalised by a split (a call's head: the rule's own form)
  def SG (m : Nat) (n : Nat) : Nat by n := match n { Z => Z, S(k) => (let r = SG(m, clone(k)); match r { Z => Z, S(q) => Z, }), }
  -- the binding the λ took is moved, as before
  reject def MV (m : Nat) (n : Nat) : Nat by n := match n { Z => Z, S(k) => (let g = (λ(j : Nat) : Nat => MV(j, clone(k))); MV(m, k)), }
  -- a λ inside a stuck block's arm: the λ names the global; the block takes the function as a
  -- parameter (left to the decision on blocks)
  def BL (m : Nat) (n : Nat) : Nat by n := match n { Z => Z, S(k) => (let r = match m { Z => Z, S(p) => (λ(j : Nat) : Nat => BL(j, clone(k)))(p), }; r), }
  -- the function as a value other than a call's head (fix L1): an argument of a higher-order
  -- call, of a λ, a `let`, `clone`, a borrow, an assignment, an ascribed head, a field, a side of `Eq`
  reject def HO1 (m : Nat) (n : Nat) : Nat by n := match n { Z => Z, S(k) => Ap2(HO1, m, k), }
  reject def HO2 (m : Nat) (n : Nat) : Nat by n := (let h = HO2; Z)
  reject def HO3 (m : Nat) (n : Nat) : Nat by n := (λ(f : Π(a : Nat) (b : Nat). Nat) : Nat => Z)(HO3)
  reject def HO4 (m : Nat) (n : Nat) : Nat by n := (let h = clone(HO4); Z)
  reject def HO5 (m : Nat) (n : Nat) : Nat by n := (let h = &HO5; Z)
  reject def HO6 (m : Nat) (n : Nat) : Nat by n := (HO6 := (λ(a : Nat) (b : Nat) : Nat => a); Z)
  reject def HO7 (m : Nat) (n : Nat) : Nat by n := match n { Z => Z, S(k) => (HO7 : Π(a : Nat) (b : Nat). Nat)(m, k), }
  reject def HO8 (m : Nat) (n : Nat) : Nat by n := (let b = MkBx(HO8); Z)
  reject def HO9 (m : Nat) (n : Nat) : Nat by n := (let e : Eq(Π(a : Nat) (b : Nat). Nat, HO9, HO9) = refl; Z)
  -- the printed code and types: the function by its name, not a capture `κ`
  reject def CL0Code (m : Nat) (n : Nat) : Nat by n := (let g = (λ(j : Nat) : Nat => match n { Z => Z, S(k) => CL0Code(j, clone(k)), }); let e : Eq(Π(j : Nat). Nat, g, λ(j : Nat) : Nat => Z) = refl; Z)
  reject def CL0Ty (m : Nat) (n : Nat) : Nat by n := (let g = (λ(j : Nat) : Nat => match n { Z => Z, S(k) => CL0Ty(j, clone(k)), }); (g : Nat))
  reject def NLCode (m : Nat) (n : Nat) : Nat by n := match n { Z => Z, S(k) => (let g = (λ(u : Unit) : Nat => (let d = clone(k); let h = (λ(j : Nat) : Nat => NLCode(j, clone(d))); let e : Eq(Π(j : Nat). Nat, h, λ(j : Nat) : Nat => Z) = refl; Z)); g(())), }
  reject def PiCode (m : Nat) (n : Nat) : Nat by n := match n { Z => Z, S(k) => (let T = (Π(j : Nat). Eq(Nat, PiCode(j, clone(k)), Z)); let e : Eq(Prop, T, True) = refl; Z), }
  reject def FACode (f : Π(j : Nat). Nat) (n : Nat) : Nat by n := match n { Z => f(Z), S(k) => (let c = clone(k); let r = FACode(λ(j : Nat) : Nat => FACode(λ(i : Nat) : Nat => i, clone(c)), k); let e : Eq(Nat, r, Z) = refl; Z), }
  reject def BXCode (m : Nat) (n : Nat) : Nat by n := match n { Z => Z, S(k) => (let b = MkBx(λ(j : Nat) : Nat => BXCode(j, clone(k))); (b : Nat)), }
  reject def LPCode (m : Nat) (n : Nat) : Nat by n := match n { Z => Z, S(k) => (let g = (λ(e : Eq(Nat, LPCode(clone(m), clone(k)), Z)) : Nat => Z); (g : Nat)), }
}

private def notHead (f : String) : String :=
  s!"[Rec] {f} occurs in its own body other than as the head of a call (fix L1)"

#guard (run "NamedByGlobal" NamedByGlobal).rejectedWith [
  ("MV", "[Read] MV was moved out or its borrow ended (reading ⊥)"),
  ("HO1", notHead "HO1"), ("HO2", notHead "HO2"), ("HO3", notHead "HO3"), ("HO4", notHead "HO4"),
  ("HO5", notHead "HO5"), ("HO6", notHead "HO6"), ("HO7", notHead "HO7"), ("HO8", notHead "HO8"),
  ("HO9", notHead "HO9"),
  ("CL0Code", "the ascribed term has type ⊤, expected Eq(Π(j : Nat). Nat, fix _ (j : Nat) : Nat := match κ1 { Z => 0, S _ => CL0Code(j, clone(κ1.0)) } where κ1 = σ1, fix _ (j : Nat) : Nat := 0)"),
  ("CL0Ty", "the ascribed term has type Π(j : Nat). Nat where κ1 = σ1, expected Nat"),
  ("NLCode", "the ascribed term has type ⊤, expected Eq(Π(j : Nat). Nat, fix _ (j : Nat) : Nat := NLCode(j, clone(κ1)) where κ1 = σ2, fix _ (j : Nat) : Nat := 0)"),
  ("PiCode", "the ascribed term has type ⊤, expected Eq(Prop, Π(j : Nat). Eq(Nat, PiCode(j, clone(κ1.0)), 0) where κ1 = S(σ2), ⊤)"),
  ("FACode", "the ascribed term has type ⊤, expected Eq(Nat, ⌈FACode(fix _ (j : Nat) : Nat := FACode(fix _ (i : Nat) : Nat := i, clone(κ1)) where κ1 = σ3, σ3)⌉, 0)"),
  ("BXCode", "the ascribed term has type Bx(Π(j : Nat). Nat where κ1 = S(σ2)), expected Nat"),
  ("LPCode", "the ascribed term has type Π(e : Eq(Nat, LPCode(clone(κ1), clone(κ2.0)), 0)). Nat where κ1 = σ0, κ2 = S(σ2), expected Nat")]

namespace Ochr.Examples.NamedByGlobal
open Ochr

/-- D139: some closure or Π-type inside `v` (at any depth: captures, code, sealed programs, fields)
keeps one of the functions `fs` among its captures. -/
def keeps (fs : List String) (v : Value) : Bool :=
  v.anyAtom fun
    | .clo cs _ _ | .tPi cs _ _ => cs.any fun | .gfn f => fs.contains f | _ => false
    | _ => false

/-- D139: in the state `st` (with the value in flight, if any), a closure or Π-type keeps a function
under check (the function of an entry of the [Rec] stack), or a capture binding holds one or
carries an entry's mark. Every part of the state that holds values is read. -/
def stateKeeps (st : MState) (flight : Option (Value × Option Value)) : Bool :=
  let fs := st.recStack.filterMap fun c => match c.fn with | .gfn f => some f | _ => none
  let uids := st.recStack.map (·.uid)
  let k := keeps fs
  let kT : Option Value → Bool := fun T? => T?.any k
  st.env.any (fun fr =>
      fr.binds.any (fun b => k b.val || kT b.ty || b.lazyTy.any (fun (P, ws, _) => k P || ws.any k)
        || (b.cap && ((match b.val with | .gfn f => fs.contains f | _ => false) || b.recUid.any uids.contains)))
      || fr.temps.any k || fr.tempTys.any kT)
    || st.absTy.any k || st.refs.any (k ·.2) || st.etaRefs.any (k ·.2) || kT st.goal
    || st.convStack.any (fun (a, b) => k a || k b) || st.neutrals.any (k ·.1)
    || st.callTyLater.any (fun (P, ws) => k P || ws.any k)
    || flight.any (fun (v, T?) => k v || kT T?)

/-- Every state the checks of the block's rows record (located terms at call depth 0, every
evaluation above it, private copies included): how many, and how many of them break D139, with
how many hold a function under check in a closure's code (so the guard is not vacuous). A
function, so that no executable importing this module runs it when it starts. -/
def census (_ : Unit) : Nat × Nat × Nat := Id.run do
  let cfg : Config := { recordStates := true, recordDeep := true, recordDeepPrivate := true }
  let r := Ochr.Test.runWith (some Prelude) "NamedByGlobal" NamedByGlobal cfg (located := true)
  let mut n := 0
  let mut bad := 0
  let mut code := 0
  for row in r.rows do
    for e in row.trace do
      let some (st, fl) := (match e with
        | .state _ _ fl st => some (st, fl)
        | .deep _ fl st => some (st, fl)
        | _ => none) | continue
      n := n + 1
      if stateKeeps st fl then bad := bad + 1
      let fs := st.recStack.filterMap fun c => match c.fn with | .gfn f => some f | _ => none
      let inCode := fun (v : Value) => v.anyAtom fun
        | .clo _ t _ => t.anyAtom fun | .gfn f => fs.contains f | _ => false
        | _ => false
      if st.env.any (·.binds.any (inCode ·.val)) then code := code + 1
  pure (n, bad, code)

-- states are recorded, some hold a closure whose code names a function under check, none breaks it
#guard let (n, bad, code) := census (); n > 1000 && code > 100 && bad == 0

end Ochr.Examples.NamedByGlobal

/-! ## Proof functions are copies, and a proof function's own binding is a proof (D100)

A Π-type into proofs is a proposition, so its values are proofs, erased to `⋆`, and the place
that holds one is a copy, like every proof: a proof-function parameter can be passed, bound,
captured and used again, as in Lean. Reading a proof never moved it before either, so no verdict
of these changes; the declared copy-ness now agrees with what erasure says the value is. A type
function is not a proof and stays not a copy (`TyFnTwice`), as does a data closure (`DataCloTwice`).

A proof function's binding of itself is a proof by its declared reading too, though it holds the
function, not `⋆`, so that [Rec] sees the recursive calls made through it. A stuck block that
captures it (a recursive call in a match that is not in tail position, `C1`) used to fail an
internal assertion: a proof by the pre-pass, not one by the binding's flag. A recursive call
through a non-tail match or a closure must still decrease (`BadBlk`, `BadClo`). -/

ochr ProofCopies uses Nats {
  def Refl (x : Nat) : Eq(Nat, x, x) := refl
  def G (h : Π(x : Nat). Eq(Nat, x, x)) : Eq(Nat, 0, 0) := h(0)
  def D (h : Π(x : Nat). Eq(Nat, x, x)) (n : Nat) : Nat := n
  -- a proof-function parameter used twice: called, passed, bound, captured, used by one arm
  def CallTwice (f : Π(x : Nat). Eq(Nat, x, x)) (n : Nat) : Nat := (let a = f(0); let b = f(1); n)
  def ArgTwice (f : Π(x : Nat). Eq(Nat, x, x)) (n : Nat) : Nat := (let a = G(f); let b = D(f, 0); D(f, n))
  def LetTwice (f : Π(x : Nat). Eq(Nat, x, x)) (n : Nat) : Nat := (let g = f; let h = f; let a = h(0); n)
  def CapTwice (f : Π(x : Nat). Eq(Nat, x, x)) (n : Nat) : Nat := (
    let c1 = (λ(u : Unit) : Eq(Nat, 0, 0) => f(0));
    let c2 = (λ(u : Unit) : Eq(Nat, 0, 0) => f(0));
    let a = c1(()); let b = c2(()); n)
  def ArmUse (k : Nat) (f : Π(x : Nat). Eq(Nat, x, x)) (n : Nat) : Nat := (
    let u : Nat = match k { Z => D(f, 0), S _ => 1 };
    D(f, n))
  def CallTwiceAt : Eq(Nat, CallTwice(Refl, 3), 3) := refl
  def ArgTwiceAt : Eq(Nat, ArgTwice(Refl, 3), 3) := refl
  def LetTwiceAt : Eq(Nat, LetTwice(Refl, 3), 3) := refl
  def CapTwiceAt : Eq(Nat, CapTwice(Refl, 3), 3) := refl
  def ArmUseAt0 : Eq(Nat, ArmUse(0, Refl, 3), 3) := refl
  def ArmUseAt1 : Eq(Nat, ArmUse(1, Refl, 3), 3) := refl
  def UseTwiceF (f : Π(x : Nat). False) : False := (let a = f(Z); f(Z))
  def Curried (h : Π(x : Nat). Π(y : Nat). Eq(Nat, y, y)) (n : Nat) : Nat := (let a = h; let b = h; n)
  -- never borrowed (D66), never a field (D36)
  reject def BorrowF (f : Π(x : Nat). Eq(Nat, x, x)) (n : Nat) : Nat := (let r = &f; n)
  reject inductive PB := MkPB(u : Unit, h : Π(x : Nat). Eq(Nat, x, x))
  -- not proofs, so not copies
  reject def TyFnTwice (T : Π(x : Nat). Type) (n : Nat) : Nat := (let a = T; let b = T; n)
  reject def DataCloTwice (n : Nat) : Nat := (let c = (λ(u : Unit) : Nat => clone(n)); let d = c; let e = c; 0)
  -- a closure into proofs is erased where it is made: its captures are untouched, so `n` is
  -- still there, and nothing can be taken out of it through the closure
  def CapNC (n : Nat) : Nat := (let c = (λ(u : Unit) : Eq(Nat, n, n) => refl); let d = c; let e = c; let m = n; m)
  def CapNCAt : Eq(Nat, CapNC(3), 3) := refl
  inductive Ex : Prop := MkEx(k : Nat)
  reject def DupThrough (n : Nat) : Nat := (let c = (λ(u : Unit) : Ex => MkEx(n)); match c(()) { MkEx(k) => Add(k, n) })
  -- a proof function's own binding captured by a stuck block (the internal fault), and its controls
  def C1 (x : Nat) : Id(Nat, x, x) by x := (
    match x { Z => (), S q => (C1(q); ()) };
    refl
  )
  def C3 (x : Nat) : Id(Nat, x, x) by x := match x { Z => refl, S q => (C3(q); refl) }
  def L0 (x : Nat) : Id(Nat, x, x) := refl
  def C2 (x : Nat) : Id(Nat, x, x) := (
    match x { Z => (), S q => (L0(q); ()) };
    refl
  )
  def SelfArm (x : Nat) : Eq(Nat, x, x) by x := (
    let u : Unit = match x { Z => (), S q => (let h = SelfArm(q); ()) };
    match x { Z => refl, S q => SelfArm(q) })
  -- a recursive call through a non-tail match or a closure still has to decrease
  reject def BadBlk (x : Nat) : Id(Nat, x, x) by x := (
    match x { Z => (), S q => (BadBlk(x); ()) };
    refl
  )
  reject def BadClo (x : Nat) : False by x := (let c = (λ(u : Unit) : False => BadClo(x)); c(()))
  def GoodClo (x : Nat) : Id(Nat, x, x) by x := match x { Z => refl, S q => (let c = (λ(u : Unit) : Id(Nat, q, q) => GoodClo(q)); c(()); refl) }
}

#guard (run "ProofCopies" ProofCopies).rejectedWith [
  ("BorrowF", "[D66] &f: its type Π(x : Nat). Eq(Nat, x, x) is not in Type₀"),
  ("PB", "field h of MkPB"),
  ("TyFnTwice", "[Read] T was moved out or its borrow ended (reading ⊥)"),
  ("DataCloTwice", "[Read] c was moved out or its borrow ended (reading ⊥)"),
  ("DupThrough", "[D45] a match on a proof of Ex returns a non-proof"),
  ("BadBlk", "[Rec] at BadBlk(S(σ1))"),
  ("BadClo", "[Rec] at BadClo(σ0)")]

/-! ## `clone` of a proof is that proof (D116)

A proposition is a copy (D100), so `clone(p)` of a place holding a proof is that proof, `⋆`, and
the run flags it as a proof, as the erasure pre-pass reads it from `p`'s declared type
(`Decide.declOf` reads `clone(p)` as `p`). Before D116 the run's classification of a `clone`
term was the default (data), so every `clone` of a proof place, in any position, was an internal
error ("INTERNAL [pre-pass] clone(#0): erased/proof = (true, true) by its declared type, (false,
false) after running"). Now the legitimate uses are accepted and the ill-typed ones are rejected by
the ordinary type rule, as the same programs without `clone` are. `CloneProof` has one program
per position a proof can be cloned in, with closed runs; `CloneK2` and `CloneK3` are the red
team's two batches (2026-11-21), verbatim: a proof, a proposition or a type where data is expected
and the reverse, with and without `clone`, a proof field, an ascription, both sides of an `Id`,
the arguments of `symm`, `trans` and `rewrite`, and an arm of a match. -/

ochr CloneProof uses Nats {
  -- accepted: the red team's
  def K7 (h : ⊤) : ⊤ := clone(h)
  def K10 (n : Nat) (h : Eq(Nat, n, n)) : Eq(Nat, n, n) := clone(h)
  def KLet (n : Nat) (h : Eq(Nat, n, n)) : Eq(Nat, n, n) := (let k = clone(h); k)
  -- rejected (a type error, as K9)
  reject def K3 (h : ⊤) : Nat := clone(h)
  reject def K9 (h : ⊤) : Nat := h
  -- accepted: other places a proof sits
  def KLocal (n : Nat) : Eq(Nat, n, n) := (let h : Eq(Nat, n, n) = refl; clone(h))
  def KTwice (h : ⊤) : ⊤ := (let a = clone(h); let b = clone(h); h)
  def KField (p : And(⊤, Eq(Nat, 1, 1))) : Eq(Nat, 1, 1) := clone(p.1)
  def KFieldMatch (p : And(⊤, Eq(Nat, 1, 1))) : Eq(Nat, 1, 1) := match p { Intro(a, b) => clone(b) }
  def KFn (f : Π(x : Nat). Eq(Nat, x, x)) : Eq(Nat, 3, 3) := (let g = clone(f); g(3))
  def KArg (n : Nat) (h : Eq(Nat, n, n)) : Eq(Nat, n, n) := K10(clone(n), clone(h))
  def KClo (h : ⊤) : ⊤ := (let c = (λ(u : Unit) : ⊤ => clone(h)); c(()))
  def KArm (k : Nat) (h : ⊤) : ⊤ := (let r : ⊤ = match k { Z => clone(h), S _ => h }; r)
  def KArmData (k : Nat) (h : ⊤) (n : Nat) : Nat := (let r = match k { Z => (let q = clone(h); 0), S _ => 1 }; Add(r, n))
  def KStmt (n : Nat) (h : Eq(Nat, n, n)) : Eq(⊤, clone(h), h) := refl
  def KRuns : Eq(Nat, KArmData(0, refl, 2), 2) := refl
  -- a proof cloned in a data function's body, which the machine runs untyped at an instance
  def KBody (h : ⊤) (n : Nat) : Nat := (let q = clone(h); n)
  def KBodyRun : Eq(Nat, KBody(refl, 5), 5) := refl
  -- data, as before
  def KData (n : Nat) : Nat := clone(n)
  def KDataRun : Eq(Nat, KData(4), 4) := refl
}

#guard (run "CloneProof" CloneProof).rejectedWith [
  ("K3", "the body of K3 has type ⊤, but the goal is Nat"),
  ("K9", "the body of K9 has type ⊤, but the goal is Nat")]

ochr CloneK2 uses Nats {
  reject def Ctl : False := ()
  inductive B := MkB(n : Nat)
  inductive PB (P : Prop) : Prop := MkPB(h : P)
  def Id1 (x : Nat) : Nat := x
  def Pf (h : ⊤) : ⊤ := h
  -- a proof / proposition / type where data is expected
  def P1 (h : ⊤) : ⊤ := clone(h)
  reject def P2 (h : ⊤) : Nat := h
  reject def P3 (h : ⊤) : Nat := Id1(h)
  def P4 (h : ⊤) : Nat := (let x = clone(h); 0)
  def P5 (h : ⊤) : Nat := match h { I => 0 }
  reject def P6 : Nat := ⊤
  reject def P7 : Nat := Nat
  reject def P8 : Nat := clone(⊤)
  reject def P9 (P : Prop) : Nat := clone(P)
  reject def P10 (A : Type) : Nat := clone(A)
  reject def P11 (h : ⊤) : B := MkB(Id1(clone(h)))
  reject def P12 (h : ⊤) : Nat := S(clone(h))
  reject def P13 (h : ⊤) : Nat × Nat := (clone(h), 0)
  reject def P14 (h : ⊤) (x : &Nat) : Unit := *x := clone(h)
  reject def P15 (h : ⊤) : Nat := (let r = &h; 0)
  reject def P16 (h : ⊤) : Nat := (let f = (λ(u : Unit) : Nat => clone(h)); 0)
  reject def P17 (h : ⊤) : Eq(Nat, clone(h), 0) := refl
  reject def P18 (h : ⊤) : Nat := match clone(h) { Z => 0, S _ => 1 }
  -- data where a proof is expected
  reject def D1 (n : Nat) : ⊤ := clone(n)
  reject def D2 (n : Nat) : ⊤ := n
  reject def D3 (n : Nat) : ⊤ := Pf(clone(n))
  reject def D4 (n : Nat) : PB(⊤) := MkPB(clone(n))
  reject def D5 (n : Nat) : ⊤ := (let h : ⊤ = clone(n); h)
  reject def D6 (n : Nat) : ⊤ := S(n)
  reject def D7 (n : Nat) : Prop := clone(n)
  reject def D8 (n : Nat) : Type := clone(n)
}

#guard (run "CloneK2" CloneK2).rejectedWith [
  ("Ctl", "the body of Ctl has type Unit"),
  ("P2", "the body of P2 has type ⊤, but the goal is Nat"),
  ("P3", "argument 1 (x) has type ⊤, expected Nat"),
  ("P6", "the body of P6 has type Prop"),
  ("P7", "the body of P7 has type Type"),
  ("P8", "(surface) clone takes a place"),
  ("P9", "the body of P9 has type Prop"),
  ("P10", "the body of P10 has type Type"),
  ("P11", "argument 1 (x) has type ⊤, expected Nat"),
  ("P12", "argument 1 (n) has type ⊤, expected Nat"),
  ("P13", "field fst of Mk has type ⊤, expected Nat"),
  ("P14", "the assigned value has type ⊤, expected Nat"),
  ("P15", "[D66] &h"),
  ("P16", "the body of _ has type ⊤, but the goal is Nat"),
  ("P17", "the left side of Eq has type ⊤, expected Nat"),
  ("P18", "[Match] on ⋄clone(…) with `Z`/`S`, but its type ⊤ is not Nat"),
  ("D1", "the body of D1 has type Nat, but the goal is ⊤"),
  ("D2", "the body of D2 has type Nat, but the goal is ⊤"),
  ("D3", "argument 1 (h) has type Nat, expected ⊤"),
  ("D4", "field h of MkPB has type Nat, expected ⊤"),
  ("D5", "the ascribed term has type Nat, expected ⊤"),
  ("D6", "the body of D6 has type Nat, but the goal is ⊤"),
  ("D7", "the body of D7 has type Nat, but the goal is Prop"),
  ("D8", "the body of D8 has type Nat, but the goal is Type")]

ochr CloneK3 uses Nats {
  reject def Ctl : False := ()
  inductive B := MkB(n : Nat)
  def Pf (n : Nat) : Eq(Nat, n, n) := refl
  def Id1 (x : Nat) : Nat := x
  -- proof-valued call where data is expected
  reject def Q1 (n : Nat) : Nat := Pf(clone(n))
  reject def Q2 (n : Nat) : Nat := Id1(Pf(clone(n)))
  reject def Q3 (n : Nat) : B := MkB(Pf(clone(n)))
  reject def Q4 (n : Nat) : Nat := S(Pf(clone(n)))
  reject def Q5 (n : Nat) : Nat := (Pf(clone(n)) : Nat)
  reject def Q6 (n : Nat) : Nat := match Pf(clone(n)) { Z => 0, S _ => 1 }
  -- projections and ascriptions of proofs
  reject def Q7 (h : ⊤ ∧ ⊤) : Nat := h.0
  reject def Q8 (h : ⊤ ∧ ⊤) : Nat := clone(h.0)
  reject def Q9 (h : ⊤) : Nat := (h : Nat)
  reject def Q10 (h : ⊤) : Nat := (clone(h) : ⊤)
  -- proof places under *, &, in Id sides
  def Q11 (h : ⊤) : Unit := (let e : Id(Unit, (let k = clone(h); ()), ()) = refl; ())
  def Q12 (h : ⊤) : Unit := (let e : Id(⊤, h, h) = refl; ())
  def Q13 (h : ⊤) : Unit := (let e : Id(⊤, clone(h), h) = refl; ())
  -- data / props / types as proof arguments
  reject def Q14 (n : Nat) : Eq(Nat, 0, 0) := symm(n)
  reject def Q15 (n : Nat) : Eq(Nat, 0, 0) := trans(n, n)
  reject def Q16 (n : Nat) : Eq(Nat, 0, 0) := cong(Id1, n)
  reject def Q17 (n : Nat) : Eq(Nat, 0, 0) := rewrite n in refl
  def Q18 (h : Eq(Nat, 0, 0)) : Eq(Nat, 0, 0) := symm(clone(h))
  def Q19 (h : Eq(Nat, 0, 0)) : Eq(Nat, 0, 0) := trans(clone(h), h)
  def Q20 (h : Eq(Nat, 0, 0)) : Eq(Nat, 0, 0) := rewrite clone(h) in refl
  reject def Q21 : Eq(Nat, 0, 0) := symm(⊤)
  reject def Q22 : Eq(Nat, 0, 0) := symm(Nat)
  -- a proof-valued block where data is expected
  def Q23 (n : Nat) (h : ⊤) : Nat := (let k = match n { Z => h, S _ => h }; 0)
  def Q24 (n : Nat) (h : ⊤) : Nat := (let k = match n { Z => clone(h), S _ => h }; 0)
}

#guard (run "CloneK3" CloneK3).rejectedWith [
  ("Ctl", "the body of Ctl has type Unit"),
  ("Q1", "the body of Q1 has type ⊤, but the goal is Nat"),
  ("Q2", "argument 1 (x) has type ⊤, expected Nat"),
  ("Q3", "field n of MkB has type ⊤, expected Nat"),
  ("Q4", "argument 1 (n) has type ⊤, expected Nat"),
  ("Q5", "the ascribed term has type ⊤, expected Nat"),
  ("Q6", "[Match] on ⋄Pf(…) with `Z`/`S`, but its type ⊤ is not Nat"),
  ("Q7", "the body of Q7 has type ⊤, but the goal is Nat"),
  ("Q8", "the body of Q8 has type ⊤, but the goal is Nat"),
  ("Q9", "the ascribed term has type ⊤, expected Nat"),
  ("Q10", "the body of Q10 has type ⊤, but the goal is Nat"),
  ("Q14", "symm: not an equation"),
  ("Q15", "[Read] n was moved out"),
  ("Q16", "cong: the proof has type Nat, which is not an equation"),
  ("Q17", "rewrite: the proof has type Nat, which is not an equation"),
  ("Q21", "symm: not an equation"),
  ("Q22", "symm: not an equation")]

/-! ## `clone` and `peek` take a place, in the core too (D122)

The surface accepts `clone` of a place only ("clone takes a place"); the core ran `clone(u)` of any
term in copying mode, where a read leaves what it reads in place, so a core `let x = S(Z); let y =
clone(S(x)); x` was accepted, with `x` still there (the guards below). Now `evalCore` rejects
`clone` and `peek` of a term that is not a place, for every core term, written or built. The checker
built one such term itself: `capture` inlines each read of a captured proof as `(⋆ : T)`, so
`clone(h)` in a closure's or a Π-type's text became `clone((⋆ : T))`. It now inlines the clone of
such a read as the proof itself, `(⋆ : T)` (D116: the clone of a proof is that proof). `CloneCaptured`
is the hunt for that producer, one program per place a closure or a Π-type can clone a captured
proof, every one accepted before and after, with closed runs; and the comparisons of two closures,
or two function types, whose texts differed only by that `clone` before (now they are the same
text). -/

ochr CloneCaptured uses Nats {
  reject def Ctl : False := ()
  -- a closure's body (λ), cloning a captured proof
  def KClo (h : ⊤) : ⊤ := (let c = (λ(u : Unit) : ⊤ => clone(h)); c(()))
  def KCloRun : Eq(Nat, (let k = KClo(refl); 0), 0) := refl
  -- a closure's declared codomain and parameter type
  def KCod (h : ⊤) : ⊤ := (let c = (λ(u : Unit) : Eq(⊤, clone(h), h) => refl); h)
  def KDom (h : ⊤) : ⊤ := (let c = (λ(e : Eq(⊤, clone(h), h)) : Unit => ()); h)
  -- a Π-type's codomain and domain, a Π-type as a result type and a λ of it
  def KPiC (h : ⊤) : Prop := Π(u : Unit). Eq(⊤, clone(h), h)
  def KPiD (h : ⊤) : Type := Π(e : Eq(⊤, clone(h), h)). Unit
  def KPiR (h : ⊤) : (Π(u : Unit). Eq(⊤, clone(h), h)) := λ(u : Unit) : Eq(⊤, clone(h), h) => refl
  -- nested closures: the outer capture inlines into the inner closure's text
  def KNest (h : ⊤) : ⊤ := (let c = (λ(u : Unit) : ⊤ => (let d = (λ(v : Unit) : ⊤ => clone(h)); d(()))); c(()))
  -- a captured proof's field is not inlined (a place inside the closure)
  def KFld (p : And(⊤, ⊤)) : ⊤ := (let c = (λ(u : Unit) : ⊤ => clone(p.0)); c(()))
  -- a let-bound local proof, captured
  def KLoc (n : Nat) : Eq(Nat, n, n) := (let h : Eq(Nat, n, n) = refl; let c = (λ(u : Unit) : Eq(Nat, n, n) => clone(h)); c(()))
  -- a closure as an argument of a data function, with its closed run
  def App (f : Π(u : Unit). ⊤) : Nat := (let r = f(()); 0)
  def KArg (h : ⊤) : Nat := App(λ(u : Unit) : ⊤ => clone(h))
  def KArgRun : Eq(Nat, KArg(refl), 0) := refl
  -- a data closure that clones a captured proof and a captured number, with its closed run
  def KData (h : ⊤) (n : Nat) : Nat := (let c = (λ(u : Unit) : Nat => (let q = clone(h); clone(n))); c(()))
  def KDataRun : Eq(Nat, KData(refl, 5), 5) := refl
  -- a closure in a stuck match's arm, and in a side of Id
  def KArm (k : Nat) (h : ⊤) : ⊤ := (let r : ⊤ = match k { Z => (let c = (λ(u : Unit) : ⊤ => clone(h)); c(())), S _ => h }; r)
  def KId (h : ⊤) : Id(⊤, (let c = (λ(u : Unit) : ⊤ => clone(h)); c(())), h) := refl
  -- controls: captured data is a place inside the closure; a captured proof read without clone
  def CData (n : Nat) : Nat := (let c = (λ(u : Unit) : Nat => clone(n)); c(()))
  def CPlain (h : ⊤) : ⊤ := (let c = (λ(u : Unit) : ⊤ => h); c(()))
  -- comparisons of two closures whose texts differed only by the clone, by Eq and by Id
  def CEq (h : ⊤) : Eq(Π(u : Unit). ⊤, λ(u : Unit) : ⊤ => clone(h), λ(u : Unit) : ⊤ => h) := refl
  def CId (h : ⊤) : Id(Π(u : Unit). ⊤, λ(u : Unit) : ⊤ => clone(h), λ(u : Unit) : ⊤ => h) := refl
  def CEqD (h : ⊤) : Eq(Π(u : Unit). Nat, λ(u : Unit) : Nat => (let q = clone(h); 0), λ(u : Unit) : Nat => (let q = h; 0)) := refl
  def CIdD (h : ⊤) : Id(Π(u : Unit). Nat, λ(u : Unit) : Nat => (let q = clone(h); 0), λ(u : Unit) : Nat => (let q = h; 0)) := refl
  def CSelf (h : ⊤) : Id(Π(u : Unit). ⊤, λ(u : Unit) : ⊤ => clone(h), λ(u : Unit) : ⊤ => clone(h)) := refl
  -- two function types, by Eq and by Id, and a binding's declared type against its value's
  def PEq (h : ⊤) : Eq(Prop, Π(u : Unit). Eq(⊤, clone(h), h), Π(u : Unit). Eq(⊤, h, h)) := refl
  def PId (h : ⊤) : Id(Prop, Π(u : Unit). Eq(⊤, clone(h), h), Π(u : Unit). Eq(⊤, h, h)) := refl
  def PEqT (h : ⊤) : Eq(Type, Π(e : Eq(⊤, clone(h), h)). Unit, Π(e : Eq(⊤, h, h)). Unit) := refl
  def PIdT (h : ⊤) : Id(Type, Π(e : Eq(⊤, clone(h), h)). Unit, Π(e : Eq(⊤, h, h)). Unit) := refl
  def CBind (h : ⊤) : ⊤ := (let f : (Π(u : Unit). Eq(⊤, clone(h), h)) = (λ(u : Unit) : Eq(⊤, h, h) => refl); h)
  def CBindR (h : ⊤) : ⊤ := (let f : (Π(u : Unit). Eq(⊤, h, h)) = (λ(u : Unit) : Eq(⊤, clone(h), h) => refl); h)
}

#guard (run "CloneCaptured" CloneCaptured).rejectedWith [
  ("Ctl", "the body of Ctl has type Unit")]

namespace Ochr.Examples.CloneCore
open Ochr

/-- A core definition `CL : Nat := body` (no parameters), checked alone. -/
def clDef (body : Term) : Def := { name := "CL", hs := [], doms := [], cod := .nat, dec := none, body := body }

/-- The verdict of `clDef body`: `""` if accepted, else the message. -/
def clVerdict (body : Term) : String :=
  match runM (checkDef (clDef body)) {} with
  | .ok () => ""
  | .error m => m

-- `let x = S(Z); let y = clone(S(x)); x` (the proof lane's guard, `MasterGuards.bodyCL`): before
-- D122 accepted, with `x` still there after the clone; now rejected, as the surface rejects it
#guard clVerdict (.letIn ⟨"x"⟩ (.succ .zero) (.letIn ⟨"y"⟩ (.prim "clone" [.succ (.place (.var 0))]) (.place (.var 1))))
  |>.startsWith "[D122] clone takes a place: clone(S("
-- `peek` likewise
#guard clVerdict (.letIn ⟨"x"⟩ (.succ .zero) (.letIn ⟨"y"⟩ (.prim "peek" [.succ (.place (.var 0))]) (.place (.var 1))))
  |>.startsWith "[D122] peek takes a place: peek(S("
-- `clone` of the place `x` itself is accepted, and `x` is still there
#guard clVerdict (.letIn ⟨"x"⟩ (.succ .zero) (.letIn ⟨"y"⟩ (.prim "clone" [.place (.var 0)]) (.place (.var 1)))) == ""
-- without `clone` the read of `x` in `S(x)` moves it, and the last read is rejected
#guard clVerdict (.letIn ⟨"x"⟩ (.succ .zero) (.letIn ⟨"y"⟩ (.succ (.place (.var 0))) (.place (.var 1)))) != ""

end Ochr.Examples.CloneCore

/-! ## A definition during its own check (D147)

A function definition without `by` enters Σ once its check has succeeded, as a constant does; one
with `by` is in Σ during its check, since its body calls it. A source program cannot tell the two
apart: without `by` the name is out of scope in the body (D31: `NSelf`, `NSelfL`), it cannot occur
in its own type (`NTy`, `NTyP`), and `split` names a global by its written name, which D118 checks
before the definition is added either way (`NSp`, `RSp`). The rows below are every other route by
which a definition's check could reach the definition by its name or its global: a λ formed in the
body, called, passed to an earlier higher-order global, nested in a λ; a stuck block; a call of an
earlier global that mentions it in no way; the erased classes (a type function and a lemma, with a
λ); a recursive definition, a λ and a block inside it; closures called inside a recursive global
and inside closures; a sealed program's re-run of a closure and of a global; comparisons of
function values; a rejected definition, absent from Σ (`UseBad`). Each verdict and message is as it
was before D147; the change is pinned on the states inside a check (`Units.lean`, `InSigma`). -/

ochr InOwnCheck uses Nats {
  inductive Bx (A : Type) := MkBx(x : A)
  def Ap1 (f : Π(j : Nat). Nat) (a : Nat) : Nat := f(a)
  def Id1 (n : Nat) : Nat := n
  -- a body that forms a λ, called and passed to an earlier higher-order global; a λ in a λ
  def NL1 (n : Nat) : Nat := (let g = (λ(j : Nat) : Nat => S(j)); g(n))
  def NL1Runs : Eq(Nat, NL1(2), 3) := refl
  def NHo (n : Nat) : Nat := Ap1(λ(j : Nat) : Nat => S(j), n)
  def NHoRuns : Eq(Nat, NHo(2), 3) := refl
  def NLL (n : Nat) : Nat := (let g = (λ(j : Nat) : Nat => (let h = (λ(k : Nat) : Nat => S(k)); h(j))); g(n))
  def NLLRuns : Eq(Nat, NLL(2), 3) := refl
  -- a stuck block (a match on the parameter, not at the end)
  def NB (n : Nat) : Nat := (let r = match n { Z => 0, S(m) => m, }; r)
  def NBRuns : Eq(Nat, NB(3), 2) := refl
  def NBEq (n : Nat) : Eq(Nat, NB(n), NB(n)) := refl
  -- a call of an earlier global that mentions it in no way
  def NE (n : Nat) : Nat := Id1(Id1(n))
  def NERuns : Eq(Nat, NE(2), 2) := refl
  -- its own name in its body without `by` (D31), and in its type
  reject def NSelf (n : Nat) : Nat := NSelf(n)
  reject def NSelfL (n : Nat) : Nat := (let g = (λ(j : Nat) : Nat => NSelfL(j)); g(n))
  reject def NTy (n : Nat) : Eq(Nat, NTy(n), n) := refl
  reject def NTyP (n : Eq(Nat, NTyP(0), 0)) : Nat := 0
  -- `split` naming the definition itself, with and without `by`
  reject def NSp (n : Nat) : Eq(Nat, n, n) := split NSp in refl
  reject def RSp (n : Nat) : Eq(Nat, n, n) by n := split RSp in refl
  -- a rejected definition is absent from Σ
  reject def Bad (n : Nat) : Nat := Eq(Nat, n, n)
  reject def UseBad (n : Nat) : Nat := Bad(n)
  -- the erased classes: a type function and a lemma, directly and through a λ, used after
  def TF (n : Nat) : Type := match n { Z => Nat, S(m) => Unit, }
  def UseTF : TF(0) := 3
  def Lm (n : Nat) : Eq(Nat, n, n) := refl
  def UseLm : Eq(Nat, 2, 2) := Lm(2)
  def TFL (n : Nat) : Type := (let g = (λ(j : Nat) : Type => match j { Z => Nat, S(m) => Unit, }); g(n))
  def UseTFL : TFL(0) := 3
  def LmL (n : Nat) : Eq(Nat, n, n) := (let g = (λ(j : Nat) : Eq(Nat, j, j) => refl); g(n))
  def PL (n : Nat) : Eq(Nat, n, n) := (let g = (λ(j : Nat) : Eq(Nat, j, j) => refl); g(n))
  def TL (n : Nat) : Nat := (let g = (λ(j : Nat) : Type => Nat); let x : g(n) = 0; x)
  -- a recursive definition, in Σ during its check; a λ calling it (D139); a stuck block of it
  def R (n : Nat) : Nat by n := match n { Z => 0, S(m) => S(R(m)), }
  def RRuns : Eq(Nat, R(3), 3) := refl
  def RL (m : Nat) (n : Nat) : Nat by n := (let g = (λ(j : Nat) : Nat => match n { Z => Z, S(k) => RL(j, clone(k)), }); g(m))
  def RLRuns : Eq(Nat, RL(3, 2), 0) := refl
  def RB (n : Nat) : Nat by n := (let r = match n { Z => 0, S(m) => RB(m), }; r)
  def RBRuns : Eq(Nat, RB(3), 0) := refl
  -- a closure called inside a recursive global, and inside a closure inside one
  def RC (n : Nat) : Nat by n := match n { Z => 0, S(m) => (let g = (λ(j : Nat) : Nat => S(j)); g(RC(m))), }
  def RCRuns : Eq(Nat, RC(3), 3) := refl
  def RCC (n : Nat) : Nat by n := match n { Z => 0, S(m) => (let g = (λ(j : Nat) : Nat => (let h = (λ(k : Nat) : Nat => S(k)); h(j))); g(RCC(m))), }
  def RCCRuns : Eq(Nat, RCC(3), 3) := refl
  -- a non-recursive global called inside a recursive one, and inside a closure
  def RN (n : Nat) : Nat by n := match n { Z => 0, S(m) => NL1(RN(m)), }
  def RNRuns : Eq(Nat, RN(2), 2) := refl
  def CN (n : Nat) : Nat := (let g = (λ(j : Nat) : Nat => NL1(j)); g(n))
  def CNRuns : Eq(Nat, CN(2), 3) := refl
  -- a sealed program's re-run (stuck at the generic call, re-run after the split) of a closure
  -- and of a non-recursive global
  def SRL (n : Nat) : Nat := (let g = (λ(j : Nat) : Nat => match j { Z => 0, S(k) => 1, }); let r = g(clone(n)); match n { Z => (let e : Eq(Nat, r, 0) = refl; r), S(m) => (let e : Eq(Nat, r, 1) = refl; r), })
  def SRLRuns : Eq(Nat, SRL(0), 0) := refl
  def Sw (j : Nat) : Nat := match j { Z => 0, S(k) => 1, }
  def SRG (n : Nat) : Nat := (let r = Sw(clone(n)); match n { Z => (let e : Eq(Nat, r, 0) = refl; r), S(m) => (let e : Eq(Nat, r, 1) = refl; r), })
  -- comparisons of function values: two λs by Eq and by Id, a λ and a global
  def CV1 : Eq(Π(j : Nat). Nat, λ(j : Nat) : Nat => S(j), λ(j : Nat) : Nat => S(j)) := refl
  def CV2 (n : Nat) : Eq(Π(j : Nat). Nat, λ(j : Nat) : Nat => Id1(j), Id1) := refl
  def CV3 (n : Nat) : Id(Π(j : Nat). Nat, λ(j : Nat) : Nat => S(j), λ(j : Nat) : Nat => S(j)) := refl
  -- a λ over a borrow parameter's content
  def CapB (x : &Nat) : Nat := (let g = (λ(j : Nat) : Nat => S(j)); g(clone(*x)))
}

#guard (run "InOwnCheck" InOwnCheck).rejectedWith [
  ("NSelf", "NSelf is not in scope in its own body: it declares no decreasing parameter (`by x`), so it is not recursive (D31)"),
  ("NSelfL", "NSelfL is not in scope in its own body: it declares no decreasing parameter (`by x`), so it is not recursive (D31)"),
  ("NTy", "NTy occurs in its own type"), ("NTyP", "NTyP occurs in its own type"),
  ("NSp", "unknown constant NSp"), ("RSp", "unknown constant RSp"),
  ("Bad", "the body of Bad has type Prop, but the goal is Nat"), ("UseBad", "unknown constant Bad")]
