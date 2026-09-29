import Ochr.Test

/-! # 8. Case splits and refinement

When a program being checked matches on a place that holds an abstract value `σ`, each arm
is checked with `σ` replaced by that arm's constructor everywhere: in the environment, in
the goal, and in the stored type of every variable ([Split]). So a type computed by a
program becomes known in each arm (dependent pattern matching). A match on a sealed
program first replaces that program by a fresh abstract value, and the replacement is
remembered: wherever the same closed program appears again, it is the same value (D34).

Defined in RULES §5 [Split]. -/

open Ochr.Test

ochr CaseSplits {
  -- A type computed by a program.
  def T (b : Nat) : Type := {
    match b {
      | Z => Nat
      | S _ => Unit
    }
  }

  def UseT0 (x : T(0)) : Nat := x
  def UseT (b : Nat) (x : T(b)) : T(b) := x

  -- In arm `Z` the split refines `x`'s stored type `T(b)` to `T(0)`, which is `Nat` ...
  def DepMatch (b : Nat) (x : T(b)) : Nat := {
    match b {
      | Z => x
      | S _ => 0
    }
  }

  -- ... and in arm `S` to `Unit`, so `x` is not a number there.
  reject def DepMatchWrong (b : Nat) (x : T(b)) : Nat := {
    match b {
      | Z => 0
      | S _ => x
    }
  }

  -- After an opaque call, `*x` holds a sealed program. Matching on it first generalises it
  -- to a fresh abstract value, then splits on that (switch `generalize`).
  def MatchAfterOpaque (f : Π(_ : &Nat). Unit) (x : &Nat) : Unit := {
    f(&*x);
    match *x {
      | Z => ()
      | S _ => ()
    }
  }
}

#eval IO.println (run "CaseSplits" CaseSplits).show

-- every verdict as expected, and the exact number of declarations (a truncated file changes it)
#guard (run "CaseSplits" CaseSplits).allAsExpected
#guard (run "CaseSplits" CaseSplits).count == 6

/-! ## A generalised value has the matched place's type

Here `l` holds the sealed program `⌈let c1 = σ; AppendM(&c1, Nil); c1⌉`. The fresh value that
replaces it gets the type of the place `l`, `List`; its own head call says nothing about the
type. The guards below read the checker's trace (switch `genPlaceType`: an earlier version
gave it type `Nat`). -/

ochr GenType {
  inductive List := Nil | Cons(h : Nat, t : List)

  def AppendM (xs : &List) (ys : List) : Unit by xs := {
    match *xs {
      | Nil => *xs := ys
      | Cons(h, t) => AppendM(&t, ys)
    }
  }

  def GenL (xs : List) : Nat := {
    let l = xs;
    AppendM(&l, Nil);
    match l {
      | Nil => 0
      | Cons(h, t) => 1
    }
  }
}

def genTrace (cfg : Ochr.Config) : String := (run "GenType" GenType { cfg with trace := true }).showTrace "GenL"
#guard (run "GenType" GenType).allAsExpected
#guard (run "GenType" GenType).count == 3
#guard ((genTrace {}).splitOn "c1⌉ to σ1 : List").length == 2
#guard ((genTrace { genPlaceType := false }).splitOn "c1⌉ to σ1 : Nat").length == 2

/-! ## What goes wrong without these rules

A match must be on a place whose type is the arms' inductive type, read from the place's
stored type (not assumed from the arms). An earlier checker assumed it from the arms: it
accepted `f` below by splitting `x : T(n)` with `L`'s constructors, and `g(5)` would then run
`L`'s arms on the number 5 (switch `scrutTyped`). -/

ochr ScrutineeTypes {
  inductive L := LNil | LCons(h : Nat, t : L)

  def T (n : Nat) : Type := {
    match n {
      | Z => L
      | S _ => Nat
    }
  }

  reject def f (n : Nat) (x : T(n)) : Nat := {
    match x {
      | LNil => 0
      | LCons(h, t) => 0
    }
  }

  reject def g (x : Nat) : Nat := f(1, x)

  -- At `T(0)`, which is `L`, the match is fine.
  def f0 (x : T(0)) : Nat := {
    match x {
      | LNil => 0
      | LCons(h, t) => h
    }
  }
}

#eval IO.println (run "ScrutineeTypes" ScrutineeTypes).show

-- every verdict as expected, and the exact number of declarations (a truncated file changes it)
#guard (run "ScrutineeTypes" ScrutineeTypes).allAsExpected
#guard (run "ScrutineeTypes" ScrutineeTypes).count == 5

/-! Generalisations are global (D37). Forming `Esc`'s goal generalises a sealed program on a
private copy of the environment, and names it with a fresh abstract value. That record,
and the counter of fresh names, must survive the copy. Otherwise the body's split issues
the same name again, for the field `x`; `Esc` then proves that `Double(n)` is zero exactly
when `x` is, for every `n` and `x`, and its instance `Bad5` is a closed proof of `1 = 0`
(switch `globalRecords`). This is note 5 of the paper's appendix, as printed. -/

ochr GlobalRecords {
  inductive Box := Mk(x : Nat)

  def Double (n : Nat) : Nat by n := {
    match n {
      | Z => Z
      | S p => S (S (Double(p)))
    }
  }

  reject def Esc (n : Nat) (m : Box) :
      Id Nat
        (let b = Double(n); match b { Z => 0 | S _ => 1 })
        (match m { Mk(x) => match x { Z => 0 | S _ => 1 } }) := {
    match m {
      | Mk(x) => match x {
        | Z => refl
        | S _ => refl
      }
    }
  }

  reject def Bad5 : Eq Nat 1 0 := Esc(1, Mk(0))
}

#eval IO.println (run "GlobalRecords" GlobalRecords).show

-- every verdict as expected, and the exact number of declarations (a truncated file changes it)
#guard (run "GlobalRecords" GlobalRecords).allAsExpected
#guard (run "GlobalRecords" GlobalRecords).count == 4
