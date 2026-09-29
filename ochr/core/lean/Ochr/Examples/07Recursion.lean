import Ochr.Examples.«00Std»

/-! # 7. Recursion and induction hypotheses

A recursive definition names its decreasing parameter with `by x`, and each recursive call
must pass, in that position, a strict part of the value `x` had on entry ([Rec], D17).
Without `by`, a definition cannot call itself (D31). A definition is checked once, at its
*generic call*: each borrow parameter points to a fresh place holding an abstract value,
and the other parameters are abstract values ([Def]). The type of a recursive call is
computed in the caller's environment, after its arguments ([Call-type]), so a call about
`&p`, a borrow of a part of `*x`, is a statement about all of `*x`: this is what makes an
induction hypothesis useful without congruence lemmas.

Defined in RULES §5: [Def], [Call-type], [Rec]. -/

open Ochr.Test

ochr Recursion uses Std {
  -- The pure theorem by recursion on a copy of the predecessor: the induction hypothesis is
  -- about `p` and the goal about `S p`, an equation between two successors, which `Eq`
  -- takes apart (injectivity, D52), so no congruence step is written. (`AddZero` in
  -- `Numbers` lends the predecessor field instead; without injectivity only that works.)
  def AddZeroCopy (x : Nat) : Id Nat (Add(x, 0)) x by x := (
    match x {
      Z => refl,
      S p => AddZeroCopy(p),
    }
  )

  -- The paper's displays for `AddMZero`'s successor arm (§2): the goal `Eq Nat N(S σ') (S σ')`
  -- runs one step to `Eq Nat (S N(σ')) (S σ')`, which `Eq` takes apart to `Eq Nat N(σ') σ'`
  -- (injectivity, D52); `Add(n, 0)` computes `N(σ')` for `n = σ'` ...
  def SuccGoal (n : Nat) (h : Eq Nat (Add(S n, 0)) (S n)) : Eq Nat (S (Add(n, 0))) (S n) := h
  def InjStep (n : Nat) (h : Eq Nat (S (Add(n, 0))) (S n)) : Eq Nat (Add(n, 0)) n := h

  -- ... and the recursive call's statement, computed at the call site, is that proposition:
  -- the borrow of `p` sits inside `*x`, so the call observes `*x` whole, successor included.
  def CallSite (x : &Nat) : Nat := (
    match *x {
      Z => 0,
      S p => (
        let h : Eq Nat (S (Add(p, 0))) (S p) = AddMZero(&p);
        0
      ),
    }
  )

  -- (It is not the statement about `p` alone with the successor added on one side.)
  reject def CallSiteWrong (x : &Nat) : Nat := (
    match *x {
      Z => 0,
      S p => (
        let h : Eq Nat (Add(p, 0)) (S p) = AddMZero(&p);
        0
      ),
    }
  )

  -- With the congruence convenience `cong` (outside the core) the copy works. The
  -- recursive call is inside a closure, and is still checked against the outer entry
  -- value: `q` is its predecessor.
  def AddZeroC (x : Nat) : Id Nat (Add(x, 0)) x by x := (
    match x {
      Z => refl,
      S p => (
        let q = p;
        cong S ((λ(u : Unit) : Id Nat (Add(q, 0)) q => AddZeroC(q))(()))
      ),
    }
  )

  -- A local recursive function is checked at its own generic call.
  def Outer (x : &Nat) : Unit := (fix go (y : &Nat) : Unit by y := match *y { Z => (), S p => go(&p) })(x)

  -- A definition may not mention itself in its own type.
  reject def SelfType (n : Nat) : Id Nat (SelfType(n)) n := refl

  -- ## What goes wrong without these rules
  -- Recursion is measured on entry values (D17): after `*x := S *x`, the predecessor of `*x`
  -- is the old `*x`, not a part of it, so `Loop` would never terminate, and `Bot'` would be a
  -- closed proof of `False` (switch `recGuard`).
  reject def Loop (x : &Nat) (y : Nat) : False by x := (
    match y {
      Z => (
        *x := S *x;
        match *x {
          Z => refl,
          S p => (
            let q = p;
            Loop(&p, q)
          ),
        }
      ),
      S q => (
        *x := S *x;
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
        x := S Z;
        match x {
          Z => refl,
          S y => Loop2(y),
        }
      ),
      S p => (
        x := S (S p);
        match x {
          Z => refl,
          S y => Loop2(y),
        }
      ),
    }
  )

  -- ... or after it, through the pattern variable.
  reject def Spin (x : Nat) : False by x := (
    match x {
      Z => (
        x := S Z;
        match x {
          Z => refl,
          S y => Spin(y),
        }
      ),
      S y => (
        x := S x;
        Spin(y)
      ),
    }
  )

  -- A local recursive function that calls itself on its own argument.
  reject def OuterBad (x : Nat) : Eq Nat 0 1 := (fix go (y : Nat) : Eq Nat 0 1 by y := go(y))(x)

  -- A recursive function may appear only as the head of a call. Passed as a value, it
  -- would escape the check on its arguments, and `Knot(0)` would be a closed proof of
  -- `False` (switch `selfHeadOnly`).
  def Apply (f : Π(x : Nat). False) (x : Nat) : False := f(x)
  reject def Knot (x : Nat) : False by x := Apply(Knot, x)
  reject def KnotBoom : False := Knot(0)

  -- Recursive calls inside a nested closure are checked against the enclosing function's
  -- entry value: `y` is a fresh argument of the closure, not a part of `x` (switch
  -- `recNested`).
  reject def KnotL (x : Nat) : False by x := (
    let g = (λ(y : Nat) : False => KnotL(y));
    g(x)
  )

  reject def KnotLBoom : False := KnotL(0)

  -- Without `by`, the function is not in scope in its own body (D31).
  reject def LoopNoBy (x : Nat) : Eq Nat Z (S Z) := LoopNoBy(x)
  reject def LoopNoByBoom : Eq Nat Z (S Z) := LoopNoBy(Z)
}

#eval IO.println (run "Recursion" Recursion).show

-- every verdict as expected, and the exact number of declarations (a truncated file changes it)
#guard (run "Recursion" Recursion).allAsExpected
#guard (run "Recursion" Recursion).count == 20
