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

  -- The paper's first `Id` (§2): at a definition taking `x : &Nat`, `Id Unit (AddM(x, 0)) ()`
  -- is `Eq Unit ⌈…⌉ () ∧ Eq Nat N(σ) σ`. The stuck call returns its sealed program `⌈…⌉`,
  -- which is also what `let c = *x; AddM(&c, 0)` returns, and leaves `N(σ)` in `x`'s owner,
  -- which is also what `Add(*x, 0)` computes. An equation at `Unit` is `⊤` (η for `Unit`,
  -- D59), whatever its sides, so the whole is the single equation `Eq Nat N(σ) σ`, in both
  -- directions.
  def IdIsConjSealed (x : &Nat) (h : Id Unit (AddM(x, 0)) ()) : Eq Unit (let c = *x; AddM(&c, 0)) () ∧ Eq Nat (Add(*x, 0)) (*x) := h
  def IdIsConj (x : &Nat) (h : Id Unit (AddM(x, 0)) ()) : Eq Unit () () ∧ Eq Nat (Add(*x, 0)) (*x) := h
  def IdIsEq (x : &Nat) (h : Id Unit (AddM(x, 0)) ()) : Eq Nat (Add(*x, 0)) (*x) := h
  def EqIsId (x : &Nat) (h : Eq Nat (Add(*x, 0)) (*x)) : Id Unit (AddM(x, 0)) () := h
  reject def IdIsWrong (x : &Nat) (h : Id Unit (AddM(x, 0)) ()) : Eq Nat (Add(*x, 1)) (*x) := h

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

  -- An equation a refinement made impossible computes to `False`, and so does its symmetric
  -- one: `symm` of a proof of `False` is a proof of `False` (fuzz-port R7: here `n1 = S p`
  -- and `n0 = 0` make both `False`, and the branch is unreachable).
  def SymmUnreachable (n0 : Nat) (n1 : Nat) (h2 : Eq Nat n0 n1) : Nat := (
    match n0 {
      Z => match n1 {
        Z => 0,
        S p => J(Nat, n1, n0, λ(z : Nat) : Type => Nat, symm h2, p),
      },
      S _ => 0,
    }
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
    let f = (λ(x : Nat → Nat) : Nat => (C1(h1, clone(x)))(x));
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
#guard (run "Equality" Equality).count == 31

/-! ## Rewriting

`rewrite h in t`, for `h : Eq A a b`, proves the goal `G` from `t : G'`, where `G'` is `G`
with every occurrence of `b`'s normal form replaced by `a` (the replacement a case split
uses to generalise a sealed program, D34, here local to the goal). `rewrite ← h in t`
replaces `a` by `b`. It is `J(A, a, b, λz. G[z/b], h, t)` with the motive read off the goal,
so it needs a known goal: tail position, a call's argument, or an annotated `let` (D60). -/

ochr Rewriting uses Std {
  -- Symmetry and transitivity, and congruence without a motive.
  def RwSymm (x : Nat) (y : Nat) (h : Eq Nat x y) : Eq Nat y x := rewrite h in refl
  def RwTrans (x : Nat) (y : Nat) (z : Nat) (h1 : Eq Nat x y) (h2 : Eq Nat y z) : Eq Nat x z := rewrite h2 in h1
  def RwCong (x : Nat) (y : Nat) (h : Eq Nat x y) : Eq Nat (Add(x, 2)) (Add(y, 2)) := rewrite h in refl
  def RwBack (x : Nat) (y : Nat) (h : Eq Nat x y) : Eq Nat (Add(x, 2)) (Add(y, 2)) := rewrite ← h in refl

  -- A sealed program is rewritten like any value: `Add(x, 0)` becomes `x`.
  def RwSealed (x : Nat) (h : Eq Nat (Add(x, 0)) x) : Eq Nat (Add(Add(x, 0), 1)) (Add(x, 1)) := rewrite ← h in refl

  -- The goal comes from the context: a parameter's type, or an annotation. In tail
  -- position the rewritten goal is the path's goal, so the rest may split.
  def UseEq (a : Nat) (b : Nat) (p : Eq Nat a b) : Eq Nat a b := p
  def RwArg (x : Nat) (y : Nat) (h : Eq Nat x y) : Eq Nat y x := UseEq(y, x, rewrite h in refl)

  def RwLet (x : Nat) (y : Nat) (h : Eq Nat x y) : Eq Nat y x := (
    let p : Eq Nat y x = (rewrite h in refl);
    p
  )

  def RwSplit (x : Nat) (y : Nat) (h : Eq Nat x y) : Id Nat (Add(y, 0)) x := (
    rewrite h in match x {
      Z => refl,
      S p => AddMZero(&p),
    }
  )

  -- The direction matters: `h : x = y` rewrites `y` to `x`, and a goal about `x` needs
  -- `rewrite ← h`. A rewrite that finds nothing is an error.
  def RwRightDir (x : Nat) (y : Nat) (h : Eq Nat x y) (k : Eq Nat y 3) : Eq Nat x 3 := rewrite ← h in k
  reject def RwWrongDir (x : Nat) (y : Nat) (h : Eq Nat x y) (k : Eq Nat y 3) : Eq Nat x 3 := rewrite h in k

  -- Here the wrong direction finds `x` inside `Add(x, 0)` too, and leaves a goal `refl`
  -- does not prove.
  reject def RwSealedWrongDir (x : Nat) (h : Eq Nat (Add(x, 0)) x) : Eq Nat (Add(Add(x, 0), 1)) (Add(x, 1)) := rewrite h in refl

  -- The rewritten goal must be what `t` proves; `h` must be an equation; the goal must be
  -- known and a proposition; and an equation between equal sides rewrites nothing.
  reject def RwMismatch (x : Nat) (y : Nat) (h : Eq Nat x y) : Eq Nat (Add(y, 1)) 7 := rewrite h in refl
  reject def RwNotEq (P : Prop) (p : P) : P := rewrite p in p

  reject def RwNoGoal (x : Nat) (y : Nat) (h : Eq Nat x y) : Nat := (
    let p = (rewrite h in refl);
    0
  )

  reject def RwData (x : Nat) (y : Nat) (h : Eq Nat x y) : Nat := rewrite h in x
  reject def RwFalse (x : Nat) (h : Eq Nat x x) : Eq Nat x (S x) := rewrite h in refl
}

#eval IO.println (run "Rewriting" Rewriting).show

-- every verdict as expected, and the exact number of declarations (a truncated file changes it)
#guard (run "Rewriting" Rewriting).allAsExpected
#guard (run "Rewriting" Rewriting).count == 17

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

  -- The owners are observed in the order the two sides first reach them, not in Ω's order:
  -- closed off, the match below binds `n0` before `x2`'s content, and the conjunction must
  -- still come out as written (fuzz-port's R6: the order was Ω's, and the true statement
  -- `IdOrder` was rejected at the generic call, where `OrderSwapped` was accepted).
  def IdOrder (n0 : Nat) (x2 : &Nat) :
      Id Prop (match n0 { Z => Id Unit (*x2 := 1) (n0 := *x2), S p2 => ⊤ })
        (match n0 { Z => Eq Nat 1 *x2 ∧ Eq Nat 0 *x2, S p2 => ⊤ }) := (
    match n0 { Z => refl, S _ => refl }
  )
  reject def OrderSwapped (n0 : Nat) (x2 : &Nat) :
      Id Prop (match n0 { Z => Id Unit (*x2 := 1) (n0 := *x2), S p2 => ⊤ })
        (match n0 { Z => Eq Nat 0 *x2 ∧ Eq Nat 1 *x2, S p2 => ⊤ }) := (
    match n0 { Z => refl, S _ => refl }
  )
  def OrderAtZero (x2 : &Nat) :
      Id Prop (let n0 = 0; Id Unit (*x2 := 1) (n0 := *x2)) (Eq Nat 1 *x2 ∧ Eq Nat 0 *x2) := refl
  -- Written places come first, then places only read through a borrow: closed off, `n1`
  -- becomes a borrow parameter, and its read in `(1, n1)` must not put it first.
  def IdOrderRead (x0 : &(Nat × Nat)) (n1 : Nat) :
      Id Prop (match n1 { Z => ⊤, S p => Id Unit (*x0 := (1, n1)) (n1 := 0) })
        (match n1 { Z => ⊤, S p => Eq (Nat × Nat) (1, n1) *x0 ∧ Eq Nat n1 0 }) := (
    match n1 { Z => refl, S _ => refl }
  )

  -- An owner reached through a returned borrow, in a sealed program's re-run, where its cell
  -- is untyped and still lent out: it is typed by what the observation reads from it
  -- (fuzz-port's R1 residual, once rejected with "cannot infer the type of the value loan").
  def RetSub (x0 : &Nat) : &Nat := match *x0 { Z => &*x0, S p3 => &p3 }
  def IdThroughRet (x0 : &Nat) (x1 : &Nat) :
      Id Prop (match *x0 { Z => let a6 = RetSub(x1); Id Unit (*x0 := *a6) (), S p7 => ⊤ })
        (match *x0 { Z => let a6 = RetSub(x1); Id Unit (*x0 := *a6) (), S p7 => ⊤ ∧ ⊤ }) := (
    match *x0 { Z => refl, S _ => refl }
  )
}

#eval IO.println (run "Owners" Owners).show

-- every verdict as expected, and the exact number of declarations (a truncated file changes it)
#guard (run "Owners" Owners).allAsExpected
#guard (run "Owners" Owners).count == 17

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
