import Ochr.Examples.«00Std»

/-! # 5. Observational equality: `Id` and `Eq`

`Id A t u` runs `t` and `u`, each on its own copy of the current environment, and
compares what they return together with what they leave in the places they may write.
Those places are the *footprint*: every place either side assigns or borrows, and the
places a borrow variable points into (its *owners*). `Id` is not a new primitive: it
computes to `Eq` between the two observations (RULES P6, §4).

`Eq` computes too: an equation between equal normal forms is `True` (proved by `refl`),
one between two values built by the same constructor is the conjunction of the equations
between their fields (injectivity, D52: `S a = S b` is `a = b`, and pairs compare component
by component), and one between different constructors is `False` (D47). An `Id` is the
conjunction of the equations over its result and each observed place, built directly (not
through a pair, D52). `J(A, a, b, P, h, t)` transports `t : P(a)` along `h : Eq A a b` to
`P(b)`.

Defined in RULES §4. -/

open Ochr.Test

ochr Equality uses Std {
  -- The footprint is read from the syntax, so an unrelated `let` does not change what is
  -- compared, and the proof is the same as `AddMZero`'s.
  def AddMZeroLet (x : &Nat) : Id Unit (let n = 0; AddM(x, n)) () by x := (
    match *x {
      Z => refl,
      S p => AddMZeroLet(&p),
    }
  )

  -- Owned locals are observed too: `x := 6` and `()` differ in what they leave in `x` ...
  reject def OwnedLocal (x : Nat) : Id Unit (x := 6) () := refl

  -- ... and assuming they agree gives exactly the equation between the two contents.
  def OwnedLocalNeq (x : Nat) (h : Id Unit (x := 6) ()) : Eq Nat 6 x := h

  -- `0 = 1` has no proof.
  reject def ZeroIsOne : Id Nat 0 1 := refl

  -- Adding 0 and adding 1 in place differ, so no induction proves them equal ...
  reject def Add01 (x : Nat) : Id Unit (AddM(&x, 0)) (AddM(&x, 1)) by x := (
    match x {
      Z => refl,
      S p => Add01(p),
    }
  )

  -- ... and their difference is provable by the same induction. The borrow of `p` inside
  -- `*x` puts the `S` back around both sides, so it does not need injectivity (see `Inj`).
  def NotAdd01 (x : &Nat) (h : Id Unit (AddM(x, 0)) (AddM(x, 1))) : False by x := (
    match *x {
      Z => h,
      S p => NotAdd01(&p, h),
    }
  )

  -- Writing 0 and writing 1 leave different contents, so the `Id` is `False`: it can be
  -- eliminated by `match e {}` or used as a proof of `False` directly.
  def WriteNeq (x : &Nat) (e : Id Unit (*x := 0) (*x := 1)) : Nat := match e {}
  def WriteDisj (x : &Nat) (h : Id Unit (*x := 0) (*x := 1)) : False := h
  reject def WriteSame (x : &Nat) (h : Id Unit (*x := 0) (*x := 0)) : False := h

  -- Distinct constructors are disjoint: `Eq Nat Z (S Z)` computes to `False`, in both
  -- directions and at any inductive type (D47).
  def NoConf (h : Eq Nat Z (S Z)) : False := h
  def NoConfS (n : Nat) (h : Eq Nat Z (S n)) : False := h
  def NoConfMatch (n : Nat) (h : Eq Nat (S n) Z) : Nat := match h {}
  def NoConfBack (h : False) : Eq Nat 0 1 := h
  def BoolDisj (h : Eq Bool false true) : False := h

  -- Equal constructors are taken apart (injectivity, D52): `Eq Nat (S a) (S b)` computes to
  -- `Eq Nat a b` ...
  def Inj (a : Nat) (b : Nat) (h : Eq Nat (S a) (S b)) : Eq Nat a b := h

  -- ... and not to anything else.
  reject def InjWrong (a : Nat) (b : Nat) (h : Eq Nat (S a) (S b)) : Eq Nat a 0 := h

  -- On pairs: an equation between two pairs is the conjunction of the equations between
  -- their components ...
  def PairInj (a : Nat) (b : Nat) (h : Eq (Nat × Nat) (a, b) (1, 2)) : Eq Nat a 1 ∧ Eq Nat b 2 := h

  -- ... and not the other way round.
  reject def PairInjWrong (a : Nat) (b : Nat) (h : Eq (Nat × Nat) (a, b) (1, 2)) : Eq Nat a 2 ∧ Eq Nat b 1 := h

  -- `J` names both endpoints, because `Eq A a a` computes to `True` and would forget them.
  def Transport (a : Nat) (b : Nat) (h : Eq Nat a b) (t : Id Nat (Add(a, 0)) a) : Id Nat (Add(b, 0)) b := (
    J(Nat, a, b, λ(z : Nat) : Prop => Id Nat (Add(z, 0)) z, h, t)
  )

  -- The transported proof must be about the first endpoint.
  reject def TransportBack (a : Nat) (b : Nat) (h : Eq Nat a b) (t : Id Nat (Add(b, 0)) b) :
      Id Nat (Add(a, 0)) a := (
    J(Nat, a, b, λ(z : Nat) : Prop => Id Nat (Add(z, 0)) z, h, t)
  )

  -- `J` computes only when its endpoints are convertible (D56, Lean's rule for `Eq.rec`) ...
  def CastRefl (n : Nat) : Id Nat (J(Nat, n, n, λ(z : Nat) : Type => Nat, refl, 5)) 5 := refl

  -- ... and is otherwise a stuck cast. Under the false hypotheses that `Nat → Nat` and
  -- `(Nat → Nat) → Nat` are equal, `Om` applies a stuck cast instead of running forever, and
  -- `CastMatch` splits on the stuck cast of `5` instead of matching `5` against `Bool`'s
  -- constructors. Returning `t` whatever the endpoints (switch `jStuck`) is equality
  -- reflection: checking `Om` would not terminate (the checker's depth bound stops it), and
  -- `CastMatch` would meet a number where a `Bool` is due.
  def C1 (h : Eq Type (Nat → Nat) ((Nat → Nat) → Nat)) (x : Nat → Nat) : ((Nat → Nat) → Nat) := (
    J(Type, Nat → Nat, (Nat → Nat) → Nat, λ(X : Type) : Type => X, h, x)
  )

  def C2 (h : Eq Type ((Nat → Nat) → Nat) (Nat → Nat)) (f : (Nat → Nat) → Nat) : (Nat → Nat) := (
    J(Type, (Nat → Nat) → Nat, Nat → Nat, λ(X : Type) : Type => X, h, f)
  )

  def Om (h1 : Eq Type (Nat → Nat) ((Nat → Nat) → Nat)) (h2 : Eq Type ((Nat → Nat) → Nat) (Nat → Nat)) : Nat := (
    let f = (λ(x : Nat → Nat) : Nat => (C1(h1, x))(x));
    f(C2(h2, f))
  )

  def CastMatch (h : Eq Type Nat Bool) : Nat := (
    let b = J(Type, Nat, Bool, λ(X : Type) : Type => X, h, 5);
    match b {
      false => 0,
      true => 1,
    }
  )
}

#eval IO.println (run "Equality" Equality).show

-- every verdict as expected, and the exact number of declarations (a truncated file changes it)
#guard (run "Equality" Equality).allAsExpected
#guard (run "Equality" Equality).count == 25

/-! ## All the owners of a returned borrow are observed

`Pick(n, &a, &b)` returns a borrow into `a` or `b`, depending on `n`. At an abstract `n`,
the hole for its contents is in both `a` and `b`, so an `Id` about writes through it
observes both: it is a conjunction with one equation per owner (D18). -/

ochr Owners uses Fixtures {
  def Probe (z : &Nat) (e : Id Unit (*z := 0) (*z := 1)) : Unit := ()

  -- `Probe`'s second parameter, at `z = r`, is a conjunction over `a` and `b`, which `refl`
  -- does not prove. (The guards after this block check the conjunction.)
  reject def Use (n : Nat) (a : Nat) (b : Nat) : Unit := (
    let r = Pick(n, &a, &b);
    Probe(r, refl)
  )

  -- ## What goes wrong without this rule
  -- The annotated block below forms the type of `e` while the hole is in both `a` and `b`.
  -- In its `S` arm `r` points into `b`, so the equation about `a` holds by `refl`, but the
  -- one about `b` is `0 = 1`, and the arm is rejected. If only the first owner were observed
  -- (switch `multiOwner`), `BadD18` would be accepted, and `ClosedD18` would be a closed
  -- proof of `0 = 1`.
  def Pick3 (x : &Nat) (y : &Nat) (s : Nat) : &Nat := (
    match s {
      Z => x,
      S _ => y,
    }
  )

  def K (z : &Nat) (e : Id Unit (*z := 0) (*z := 1)) : Eq Nat 0 1 := e

  reject def BadD18 (s : Nat) (hs : Eq Nat s 1) (a : Nat) (b : Nat) : Eq Nat 0 1 := (
    let r = Pick3(&a, &b, s);
    let e : Id Unit (*r := 0) (*r := 1) = match s {
      Z => hs,
      S _ => refl,
    };
    K(r, e)
  )

  reject def ClosedD18 : Eq Nat 0 1 := BadD18(1, refl, 0, 0)

  -- The same without an annotated block: the hypothesis `h` recomputes, with local copies,
  -- exactly the sealed program that `a1` holds after `Pick`.
  def Neq (y : &Nat) (h : Id Unit (*y := Z) (*y := S Z)) : Eq Nat Z (S Z) := h

  reject def GR (a1 : Nat) (a2 : Nat) (b : Nat)
      (h : Eq Nat
        (let c1 = a1; let c2 = a2; let r = Pick(b, &c1, &c2); *r := Z; c1)
        (let c1 = a1; let c2 = a2; let r = Pick(b, &c1, &c2); *r := S Z; c1)) :
      Eq Nat Z (S Z) := (
    let r = Pick(b, &a1, &a2);
    Neq(r, h)
  )

  reject def BadR : Eq Nat Z (S Z) := GR(0, 0, 1, refl)

  -- The curried form of the attack cannot even be stated: `G`'s result type is a Π-type
  -- that would capture the borrow `z`, and types capture values, never borrows (RULES §1).
  reject def G (z : &Nat) : (Π(e : Id Unit (*z := 0) (*z := 1)). False) := (
    λ(e : Id Unit (*z := 0) (*z := 1)) : False => e
  )

  reject def BadC2 (n : Nat) (a : Nat) (b : Nat) : Id Nat n 0 := (
    let r = Pick(n, &a, &b);
    let h = G(r);
    match n {
      Z => refl,
      S m => h(refl),
    }
  )
}

#eval IO.println (run "Owners" Owners).show

-- every verdict as expected, and the exact number of declarations (a truncated file changes it)
#guard (run "Owners" Owners).allAsExpected
#guard (run "Owners" Owners).count == 11

/-- The message rejecting `Owners.Use` under `cfg`: it states `Probe`'s parameter type. -/
def useMessage (cfg : Ochr.Config) : String :=
  match ((run "Owners" Owners cfg).rows.find? (·.name == "Use")).map (·.verdict) with
  | some (Ochr.Verdict.rejected m) => m
  | _ => ""

-- all owners: the expected parameter type is a conjunction over a and b
#guard ((useMessage {}).splitOn "∧").length == 2
-- a single owner (switch `multiOwner`): one equation only
#guard ((useMessage { multiOwner := false }).splitOn "∧").length == 1

#eval IO.println (useMessage {})
