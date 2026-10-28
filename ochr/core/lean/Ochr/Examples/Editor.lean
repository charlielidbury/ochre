import Ochr.Examples.Bool
import Ochr.Examples.Nat
import Ochr.Examples.HashMap

/-! # The editor: every error at the source responsible (docs/07)

Each `reject def` here is rejected, and `#ochr_error_at B D "before⟦t⟧after"` asserts that
the error is reported at the source text `t`, in that context. Where the term responsible is
not the one being evaluated, the checker says so: an argument's type is checked by the call
(`callType`), a borrow ended by a later argument is found at the call (`noteEnders`), and an
error inside a callee's body or a sealed program's re-run (call depth above 0) belongs to the
point in the declaration that started it. Source locations are a table keyed by the address
of each resolved term (`Ochr/Loc.lean`), which keeps every node it records alive, so an
address is never reused by another term while the table is in use: the second block checks
its declarations after the whole hash-map library, which allocates and frees a great deal. -/

open Ochr.Test

ochr EditorErrors uses Bools, Nats {
  def Count (k : Nat) : Nat by k := (
    match k {
      Z => 0,
      S p => S(Count(p)),
    }
  )

  def G (b : Bool) (k : Nat) : Nat := (
    match b {
      false => 0,
      true => Count(k),
    }
  )

  -- an ill-typed argument: the argument
  reject def BadArg (x : &Nat) : Unit := AddM(x, ())

  -- reading a moved borrow: the read
  reject def UseMoved (x : &Nat) : Unit := (
    AddM(x, 0);
    AddM(x, 1)
  )

  -- a later argument ends an earlier argument's borrow: the access that ended it
  reject def Dead (f : Π(a : &Nat) (b : Nat). Unit) (y : Nat) : Unit := f(&y, y)

  -- a failed `refl` in one arm: that `refl`
  reject def ArmRefl (x : &Nat) : Id(Nat, clone(*x), 0) := (
    match *x {
      Z => refl,
      S p => refl,
    }
  )

  -- inside a λ's body, which `capture` rebuilds: the argument inside the body
  reject def InLambda (y : Nat) : Nat := (
    let f = (λ(z : Nat) : Nat => Add(z, ()));
    f(y)
  )

  -- a surface error (no such place): the term
  reject def NotAPlace (x : &Nat) : Unit := AddM(&q, 0)

  -- `Deep : Nat := Count(3000)` and `ReRun`, a `G(b, 3000)` re-run when a split refines `b`,
  -- were tests here of an error inside a callee's body or a sealed program's re-run (call depth
  -- above 0), located at the call that started it. Their error was the call-depth limit, and
  -- running past a limit is no longer an error: the checker does not know, and the verdict is
  -- `undecided` (`Ochr/Catch.lean`, `notes/catch-census.md`), which has no source location. An
  -- accepted callee's body has no other way to fail, so no test of that location remains.
}


#ochr_error_at EditorErrors BadArg "AddM(x, ⟦()⟧)"
#ochr_error_at EditorErrors UseMoved "AddM(⟦x⟧, 1)"
#ochr_error_at EditorErrors Dead "f(&y, ⟦y⟧)"
#ochr_error_at EditorErrors ArmRefl "S p => ⟦refl⟧"
#ochr_error_at EditorErrors InLambda "Add(z, ⟦()⟧)"
#ochr_error_at EditorErrors NotAPlace "AddM(⟦&q⟧, 0)"

-- After the hash-map library, checked again as its library: these declarations are resolved
-- before the library is checked and checked after it, so their table must survive that.
ochr EditorAfterLibrary uses Nats, HashMap, HashMapLookup, HashMapLength, HashMapResize {
  reject def LateArg (x : &Nat) : Unit := AddM(x, ())

  reject def LateLambda (y : Nat) : Nat := (
    let f = (λ(z : Nat) : Nat => Add(z, ()));
    f(y)
  )

  reject def LateMoved (x : &Nat) : Unit := (
    AddM(x, 0);
    AddM(x, 2)
  )
}


#ochr_error_at EditorAfterLibrary LateArg "AddM(x, ⟦()⟧)"
#ochr_error_at EditorAfterLibrary LateLambda "Add(z, ⟦()⟧)"
#ochr_error_at EditorAfterLibrary LateMoved "AddM(⟦x⟧, 2)"

/-! ## Holes are axioms of Σ (docs/07)

A hole `?` stands for a value of the type its context requires, so the rest is checked around
it. At a proposition its value is `⋆`; at any other type it is a fresh abstract value, an
axiom of that type. A constant defined by a hole keeps that value in Σ, so a later declaration
must still know the abstract value's type and must never reuse its name for one of its own
(`Check.seedHoles`). Without that, using `HE` below failed with "unknown abstract value σ0",
and `HAll`, which says every number is `HN`, checked by `refl`, since its parameter `n` and
`HN` were both `σ0`. The blocks are wrapped so that the build does not print each hole's
goal view; their verdicts are asserted as everywhere else. -/

#guard_msgs (drop warning) in
ochr Holes uses Nats {
  -- a constant by a hole, at an empty type, used by a later declaration
  inductive HVoid : Type
  def HE : HVoid := ?
  def HAbsurd (e : HVoid) : False := match e {}
  def HUseE : False := HAbsurd(HE)

  -- a hole's value is one unknown: equal to itself, not to another hole's, and not to a
  -- later declaration's own unknowns
  def HN : Nat := ?
  def HM : Nat := ?
  def HSelf : Eq(Nat, HN, HN) := refl
  reject def HSame : Eq(Nat, HN, HM) := refl
  reject def HAll (n : Nat) : Eq(Nat, n, HN) := refl
  -- ... also inside a sealed program
  def HK : Nat := (let h : Nat = ?; Add(h, 1))
  reject def HAllK (n : Nat) : Eq(Nat, Add(n, 1), HK) := refl
  def HUseK : Eq(Nat, HK, HK) := refl

  -- a hole in a function's body: a call to it is stuck, and closes off
  def HG (x : Nat) : Nat := ?
  def HUseG : Nat := HG(3)

  -- a type by a hole, and a value of that type by another
  def HT : Type := ?
  def HX : HT := ?
  def HY : HT := HX
  def HXY : Eq(HT, HX, HY) := refl

  -- a hole's value captured by a closure, and one taken apart by a later match
  def HC : (Π(x : Nat). Nat) := (let h : Nat = ?; (λ(x : Nat) : Nat => clone(h)))
  def HUseC : Nat := HC(0)
  def HP : Nat × Nat := ?
  def HUseP : Nat := match HP { Mk(a, b) => clone(a) }

  -- in a later inductive declaration's use
  inductive HWrap := HW(v : HVoid)
  def HUseW : HWrap := HW(HE)
}

-- a hole in a block another block uses
#guard_msgs (drop warning) in
ochr HolesLib {
  def HL : Nat := ?
}

ochr HolesUser uses HolesLib {
  def HLSelf : Eq(Nat, HL, HL) := refl
  reject def HLAll (n : Nat) : Eq(Nat, n, HL) := refl
}
