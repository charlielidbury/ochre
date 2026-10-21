import Ochr.Examples.«00Std»

/-! # Surface sugar: destructuring `let`, `if`, and `match` on any term

Three desugarings in the surface elaborator (`Ochr/Notation.lean`, `Ochr/Surface.lean`). None
adds a rule: each is a form the core already has, written more briefly.

* `let C(x̄) = e; u` is `match e { C(x̄) => u }`, for a constructor `C` whose type has exactly
  one constructor. Fields are bound by position, `_` ignores one, and patterns nest. And's
  `let ⟨h, k⟩ = p` and Pair's `let (a, b) = p` are instances of it (`Destructuring`, in
  `11Propositions.lean`). On a place the names are its sub-places, so writing one writes the
  place.
* `if c { a } else { b }` is `match c { true => a, false => b }` on `Bool` (whichever block
  in scope declares `false | true`), with
  `else if` chains. Without `else` the branch must be `Unit`, and the missing one is `()`.
* `match e { … }` on a term `e` that is not a place is `let x = e; match x { … }`, with a fresh
  `x`. A place is matched in place, as before: binding it first would move it. In a proof,
  matching the temporary, whose content is the call's stuck result, generalises the call and
  splits on it ([Split]), so the same call computes in each arm wherever the goal makes it.

Each has accepted programs, its error cases, and runs showing that it computes as the form it
stands for. -/

open Ochr.Test

ochr Sugar uses Std {
  -- ## Destructuring `let`
  inductive Triple := T3(a : Word, b : Word, c : Word)
  inductive Map := MkMap(n : Word, len : Word, keys : List(Word))
  inductive Wrap := MkW(p : Word × Word, t : Triple)
  inductive MaybeW := NoW | SomeW(v : Word)

  def Mid (t : Triple) : Word := (
    let T3(_, y, _) = t;
    y
  )

  -- The match it stands for: the two compute to the same thing at an unknown `t`.
  def MidMatch (t : Triple) : Word := (
    match t {
      T3(x, y, z) => y,
    }
  )

  def MidIsMatch (t : Triple) : Eq(Word, (let T3(_, y, _) = t; y), (match t { T3(x, y, z) => y })) := refl

  def MidRun : Id(Word, Mid(T3(Zero, Succ(Zero), Zero)), Succ(Zero)) := refl

  -- On a place the names are its sub-places: `len := …` writes the field of `*m`.
  def Bump (m : &Map) : Unit := (
    let MkMap(n, len, keys) = *m;
    len := Succ(len)
  )

  def BumpMatch (m : &Map) : Unit := (
    match *m {
      MkMap(n, len, keys) => len := Succ(len),
    }
  )

  def BumpRun : Id(Map, (let m = MkMap(Zero, Zero, Nil[Word]); Bump(&m); m), MkMap(Zero, Succ(Zero), Nil[Word])) := refl

  -- Same effect as the match, at an unknown map.
  def BumpIsMatch (m : &Map) : Id(Unit, Bump(&*m), BumpMatch(m)) := (
    match *m {
      MkMap(n, len, keys) => refl,
    }
  )

  -- Patterns nest: a pair pattern and a constructor pattern inside one.
  def Nested (w : Wrap) : Word := (
    let MkW((x, y), T3(_, b, _)) = w;
    b
  )

  def NestedRun : Id(Word, Nested(MkW((Zero, Zero), T3(Zero, Succ(Zero), Zero))), Succ(Zero)) := refl

  -- And's constructor written out is `⟨a, b⟩`.
  def AndCtor (P : Prop) (Q : Prop) (h : P ∧ Q) : Q := (
    let Intro(a, b) = h;
    b
  )

  -- On a term that is not a place: a temporary holds it.
  def MkT (x : Word) : Triple := T3(x, Succ(x), x)

  def MidOfTerm (x : Word) : Eq(Word, (let T3(_, y, _) = MkT(x); y), Succ(x)) := refl

  -- A proposition with one constructor and a data field (D49: a fresh abstract value).
  def IsSucc (n : Word) : Prop := (
    match n {
      Zero => False,
      Succ(_) => ⊤,
    }
  )

  inductive Pos : Prop := Wit(w : Word, h : IsSucc(w))

  def PosNotZero (p : Pos) : ⊤ := (
    let Wit(w, h) = p;
    refl
  )

  -- `MaybeW` has two constructors, so a destructuring `let` cannot take it apart: use `match`.
  reject def LetOpt (o : MaybeW) : Word := (
    let SomeW(v) = o;
    v
  )

  -- `Nat` has two constructors too.
  reject def LetSucc (n : Nat) : Nat := (
    let S(p) = n;
    p
  )

  -- One name per field.
  reject def LetFewer (t : Triple) : Word := (
    let T3(x, y) = t;
    x
  )

  -- ## `if`
  def Choose (b : Bool) (x : Word) (y : Word) : Word := if b { x } else { y }

  def ChooseRun : Id(Word × Word, (Choose(true, Zero, Succ(Zero)), Choose(false, Zero, Succ(Zero))), (Zero, Succ(Zero))) := refl

  -- The match it stands for, at an unknown `b`.
  def ChooseIsMatch (b : Bool) (x : Word) (y : Word) : Eq(Word, (if b { x } else { y }), (match b { true => x, false => y })) := refl

  -- `else if` chains.
  def Rank (a : Bool) (b : Bool) : Word := (
    if a {
      Zero
    } else if b {
      Succ(Zero)
    } else {
      Succ(Succ(Zero))
    }
  )

  def RankRun : Id(Word × (Word × Word), (Rank(true, false), (Rank(false, true), Rank(false, false))), (Zero, (Succ(Zero), Succ(Succ(Zero))))) := refl

  -- No `else`: the branch is `Unit`, and the other one is `()`.
  def ResetIf (b : Bool) (x : &Word) : Unit := if b { *x := Zero }

  def ResetIfRun : Id(Word × Word, ((let x = Succ(Zero); ResetIf(true, &x); x), (let y = Succ(Zero); ResetIf(false, &y); y)), (Zero, Succ(Zero))) := refl

  -- A condition that is not a place is bound to a temporary first.
  def Flip (b : Bool) : Bool := if b { false } else { true }

  def Xor (a : Bool) (b : Bool) : Bool := if Flip(a) { b } else { Flip(b) }

  def XorRun : Id(Bool × Bool, (Xor(true, true), Xor(false, true)), (false, true)) := refl

  -- In a proof, `if` is a case split, like the match it stands for.
  def ChooseSame (b : Bool) (x : Word) : Eq(Word, Choose(b, x, x), x) := if b { refl } else { refl }

  -- The condition must be a `Bool`.
  reject def IfWord (n : Word) : Word := if n { Zero } else { n }

  -- Without `else` the branch must be `Unit`.
  reject def IfNoElse (b : Bool) : Word := if b { Zero }

  -- ## `match` on any term
  def IsZero (n : Word) : Bool := (
    match n {
      Zero => true,
      Succ(_) => false,
    }
  )

  -- A match on a call's result: the call is bound to a temporary, which is matched.
  def AtLeastOne (n : Word) : Word := (
    match IsZero(n) {
      true => Succ(Zero),
      false => n,
    }
  )

  -- The same, with the temporary written out.
  def AtLeastOneLet (n : Word) : Word := (
    let z = IsZero(n);
    match z {
      true => Succ(Zero),
      false => n,
    }
  )

  def AtLeastOneRun : Id(Word × Word, (AtLeastOne(Zero), AtLeastOne(Succ(Succ(Zero)))), (Succ(Zero), Succ(Succ(Zero)))) := refl

  -- In a proof, the match on `IsZero(n)` generalises that call and splits on its result.
  -- Wherever the goal makes the same call, here twice (inside `AtLeastOne(n)`, and on its
  -- result `n` in the `false` arm), it computes in each arm.
  def AtLeastOneNotZero (n : Word) : Eq(Bool, IsZero(AtLeastOne(n)), false) := (
    match IsZero(n) {
      true => refl,
      false => refl,
    }
  )

  -- As the hand-written form does, matching the place that holds the call's result.
  def AtLeastOneNotZeroLet (n : Word) : Eq(Bool, IsZero(AtLeastOne(n)), false) := (
    let z = IsZero(n);
    match z {
      true => refl,
      false => refl,
    }
  )

  -- Both functions make the call, so one split on it settles their equation.
  def AtLeastOneIsLet (n : Word) : Eq(Word, AtLeastOne(n), AtLeastOneLet(n)) := (
    match IsZero(n) {
      true => refl,
      false => refl,
    }
  )

  -- Without the split, the goal is stuck on the call.
  reject def AtLeastOneNotZeroRefl (n : Word) : Eq(Bool, IsZero(AtLeastOne(n)), false) := refl

  -- A match with no arms on a call whose type is empty.
  def NoZeroSucc (n : Word) (h : Eq(Word, Zero, Succ(n))) : False := match h {}

  def FromNoZeroSucc (n : Word) (h : Eq(Word, Zero, Succ(n))) : Eq(Word, n, Zero) := match NoZeroSucc(n, h) {}

  -- Not in tail position: the match on the temporary is a stuck block, as any match is.
  def ClampIn (x : &Word) : Unit := (
    match IsZero(*x) {
      true => *x := Succ(Zero),
      false => (),
    };
    ()
  )

  def ClampInRun : Id(Word × Word, ((let x = Zero; ClampIn(&x); x), (let y = Succ(Succ(Zero)); ClampIn(&y); y)), (Succ(Zero), Succ(Succ(Zero)))) := refl
}

-- each rejection for its reason
#guard (run "Sugar" Sugar).rejectedWith [
  ("LetOpt", "(surface) let SomeW(…) = …: MaybeW has 2 constructors (NoW, SomeW), and a destructuring let needs a type with exactly one: use match"),
  ("LetSucc", "(surface) let S(…) = …: Nat has 2 constructors (Z, S)"),
  ("LetFewer", "(surface) pattern T3 needs 3 variables"),
  ("IfWord", "[Match] on n : Word, with the constructors of Bool"),
  ("IfNoElse", "the body of IfNoElse has type Unit, but the goal is Word"),
  ("AtLeastOneNotZeroRefl", "the body of AtLeastOneNotZeroRefl has type ⊤, but the goal is Eq(Bool, ⌈IsZero(⌈AtLeastOne(σ0)⌉)⌉, false)")]

-- and where it is reported
#ochr_error_at Sugar LetOpt "let SomeW(v) = o;\n    v"
#ochr_error_at Sugar IfWord "if n { Zero } else { n }"

/-! `if`'s arms name `true` and `false`, which resolve like any constructors: it works on the
`Bool` of whatever block declares one, and says so where there is none. -/

ochr SugarOwnBool {
  inductive Bool := false | true

  def Pick (b : Bool) (x : Nat) (y : Nat) : Nat := if b { x } else { y }

  def PickRun : Id(Nat, Pick(false, 1, 2), 2) := refl
}

ochr SugarNoBool {
  reject def IfNoBool (n : Nat) : Nat := if n { 0 } else { 1 }
}

#guard (run "SugarNoBool" SugarNoBool).rejectedWith [
  ("IfNoBool", "(surface) true is not a constructor: `if` and a match on true/false need a declared Bool := false | true")]
