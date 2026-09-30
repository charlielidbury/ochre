import Ochr.Examples.«00Std»

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
  def T (b : Nat) : Type := (
    match b {
      Z => Nat,
      S _ => Unit,
    }
  )

  def UseT0 (x : T(0)) : Nat := x
  def UseT (b : Nat) (x : T(b)) : T(b) := x

  -- In arm `Z` the split refines `x`'s stored type `T(b)` to `T(0)`, which is `Nat` ...
  def DepMatch (b : Nat) (x : T(b)) : Nat := (
    match b {
      Z => x,
      S _ => 0,
    }
  )

  -- ... and in arm `S` to `Unit`, so `x` is not a number there.
  reject def DepMatchWrong (b : Nat) (x : T(b)) : Nat := (
    match b {
      Z => 0,
      S _ => x,
    }
  )

  -- After an opaque call, `*x` holds a sealed program. Matching on it first generalises it
  -- to a fresh abstract value, then splits on that (switch `generalize`).
  def MatchAfterOpaque (f : Π(_ : &Nat). Unit) (x : &Nat) : Unit := (
    f(&*x);
    match *x {
      Z => (),
      S _ => (),
    }
  )
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

  def AppendM (xs : &List) (ys : List) : Unit by xs := (
    match *xs {
      Nil => *xs := ys,
      Cons(h, t) => AppendM(&t, ys),
    }
  )

  def GenL (xs : List) : Nat := (
    let l = xs;
    AppendM(&l, Nil);
    match l {
      Nil => 0,
      Cons(h, t) => 1,
    }
  )
}

def genTrace (cfg : Ochr.Config) : String := (run "GenType" GenType { cfg with trace := true }).showTrace "GenL"
#guard (run "GenType" GenType).allAsExpected
#guard (run "GenType" GenType).count == 3
#guard ((genTrace {}).splitOn "c1⌉ to σ1 : List").length == 2
#guard ((genTrace { genPlaceType := false }).splitOn "c1⌉ to σ1 : Nat").length == 2

/-! A generalisation re-derived inside a Π-type. After splitting on `F(n)`'s result, a sealed
program that computes `F(n)` inside, `⌈G(σ)⌉`, is re-normalised to use the split value
(finding G1). That reaches the captures of closures and Π-types too: `InPi`'s goal holds
`⌈G(σ)⌉` as a capture of its Π, and was left stale (arrays-library). -/

ochr RenormPi uses Std {
  def F (n : Nat) : Nat by n := match n { Z => 0, S m => F(m) }
  def G (n : Nat) : Nat := (let x = F(n); match x { Z => 1, S _ => 2 })
  def Plain (n : Nat) (h : Eq Nat (F(n)) 0) : (let k = G(n); Eq Nat k 1) := (
    let r = F(n); match r { Z => refl, S j => match h {} })
  def InPi (n : Nat) (h : Eq Nat (F(n)) 0) : (let k = G(n); Π(u : Nat). Eq Nat k 1) := (
    let r = F(n); match r { Z => λ(u : Nat) : Eq Nat 1 1 => refl, S j => match h {} })
  def InConj (n : Nat) (h : Eq Nat (F(n)) 0) : (let k = G(n); Eq Nat k 1 ∧ (Π(u : Nat). Eq Nat k 1)) := (
    let r = F(n); match r { Z => ⟨refl, λ(u : Nat) : Eq Nat 1 1 => refl⟩, S j => match h {} })
}

#eval IO.println (run "RenormPi" RenormPi).show

#guard (run "RenormPi" RenormPi).allAsExpected
#guard (run "RenormPi" RenormPi).count == 5

/-! ## Splitting on a result the goal is stuck on

`split f in t` finds, in the goal, a sealed program whose run is stuck on the result of a
call of `f`, generalises that result as a match on a place holding it would (D34), and
checks `t` in every arm; `split f { C(x̄) => t, … }` gives each arm. "Finds" is fixed: the
goal's sealed programs in order, left to right, each followed down the chain of results its
run is stuck on, and the first result whose head call is `f`, or which stands for one that
an earlier split generalised (D61). It saves computing the result again into a place just
to match on it. -/

ochr Splitting uses Std {
  def IsZ (n : Nat) : Bool := (
    match n {
      Z => true,
      S _ => false,
    }
  )

  def Pick (n : Nat) : Nat := (
    let b = IsZ(n);
    match b {
      false => 1,
      true => 2,
    }
  )

  -- `Pick(n)` is stuck on the sealed `IsZ(n)`, so the goal is too. `split IsZ` finds that
  -- sealed result in the goal and splits on it, as a match on a place holding it would.
  def PickNotZero (n : Nat) : Eq Bool (IsZ(Pick(n))) false := split IsZ in refl

  -- The same proof without `split`: compute `IsZ(n)` again into a place, and match on it.
  def PickNotZeroCopy (n : Nat) : Eq Bool (IsZ(Pick(n))) false := (
    let b = IsZ(n);
    match b {
      false => refl,
      true => refl,
    }
  )

  -- Without a split the goal stays stuck.
  reject def PickNotZeroNoSplit (n : Nat) : Eq Bool (IsZ(Pick(n))) false := refl

  -- Nested: in the second arm of the outer split, `IsZ(m)` has already been generalised
  -- (in the first arm's inner split), and the record says so; `split` finds it all the same.
  def Pick22 (n : Nat) (m : Nat) : Nat := (
    let a = IsZ(n);
    let b = IsZ(m);
    match a {
      false => match b {
        false => 1,
        true => 2,
      },
      true => match b {
        false => 3,
        true => 4,
      },
    }
  )

  def Pick22NotZero (n : Nat) (m : Nat) : Eq Bool (IsZ(Pick22(n, m))) false := split IsZ in split IsZ in refl

  -- With arms, when they differ; a hypothesis about the split result is refined too.
  def PickTwo (n : Nat) (h : Eq Bool (IsZ(n)) true) : Eq Nat (Pick(n)) 2 := (
    split IsZ {
      false => match h {},
      true => refl,
    }
  )

  -- The arms bind the fields of the split value, as a match's do.
  inductive Opt := None | Some(v : Nat)

  def Look (n : Nat) : Opt := (
    match n {
      Z => None,
      S m => Some(m),
    }
  )

  def Double (o : Opt) : Nat := (
    match o {
      None => 0,
      Some(v) => Add(clone(v), v),
    }
  )

  def Val (o : Opt) : Nat := (
    match o {
      None => 0,
      Some(v) => v,
    }
  )

  def DoubleVal (n : Nat) : Eq Nat (Double(Look(n))) (Add(Val(Look(n)), Val(Look(n)))) := (
    split Look {
      None => refl,
      Some(x) => refl,
    }
  )

  -- `split f` needs the goal to be stuck on a result of `f`; the arms must be the
  -- constructors of its type, and each must prove its refined goal. A split cannot prove
  -- a false statement, and it needs the goal, so it is only in tail position.
  reject def NothingToSplit (n : Nat) : Eq Nat n n := split IsZ in refl
  reject def WrongHead (n : Nat) : Eq Bool (IsZ(Pick(n))) false := split Look in refl
  reject def WrongArm (n : Nat) (h : Eq Bool (IsZ(n)) true) : Eq Nat (Pick(n)) 2 := (
    split IsZ {
      false => refl,
      true => refl,
    }
  )
  reject def WrongCtors (n : Nat) : Eq Bool (IsZ(Pick(n))) false := (
    split IsZ {
      None => refl,
      Some(x) => refl,
    }
  )
  reject def SplitLie (n : Nat) : Eq Nat (Pick(n)) 1 := split IsZ in refl
  reject def NotTail (n : Nat) : Eq Bool (IsZ(Pick(n))) false := (
    let p : Eq Bool (IsZ(Pick(n))) false = (split IsZ in refl);
    p
  )
}

#eval IO.println (run "Splitting" Splitting).show

-- every verdict as expected, and the exact number of declarations (a truncated file changes it)
#guard (run "Splitting" Splitting).allAsExpected
#guard (run "Splitting" Splitting).count == 19

/-! ## What goes wrong without these rules

A match must be on a place whose type is the arms' inductive type, read from the place's
stored type (not assumed from the arms). An earlier checker assumed it from the arms: it
accepted `f` below by splitting `x : T(n)` with `L`'s constructors, and `g(5)` would then run
`L`'s arms on the number 5 (switch `scrutTyped`). -/

ochr ScrutineeTypes {
  inductive L := LNil | LCons(h : Nat, t : L)

  def T (n : Nat) : Type := (
    match n {
      Z => L,
      S _ => Nat,
    }
  )

  reject def f (n : Nat) (x : T(n)) : Nat := (
    match x {
      LNil => 0,
      LCons(h, t) => 0,
    }
  )

  reject def g (x : Nat) : Nat := f(1, x)

  -- At `T(0)`, which is `L`, the match is fine.
  def f0 (x : T(0)) : Nat := (
    match x {
      LNil => 0,
      LCons(h, t) => h,
    }
  )

  -- A `Nat` match reads the stored type too (rule-audit item 2, fuzz-port's M2, D63). Without
  -- it, `NatT` split an `x` of a type variable with Nat's constructors, and `NatTUse(BT)` ran
  -- the match on `BT`; `M2` did the same through a stuck family, and `M2Run` goes wrong.
  inductive B2 := BF | BT
  def TG (n : Nat) : Type := match n { Z => Nat, S _ => B2 }
  def HB (n : Nat) : TG(n) := match n { Z => 0, S _ => BF }
  reject def NatT (A : Type) (x : A) : Nat := (match x { Z => 0, S _ => 1 })
  reject def NatTUse (b : B2) : Nat := NatT(B2, b)
  reject def NatTNT (A : Type) (x : A) : Nat := (let r = match x { Z => 0, S _ => 1 }; r)
  reject def M2 (n : Nat) (h : Π(n : Nat). TG(n)) : Nat := (let x = h(n); match x { Z => 0, S _ => 1 })
  reject def M2Run : Nat := M2(1, HB)

  -- Where the family computes to `Nat`, the match is fine.
  def M2Zero (h : Π(n : Nat). TG(n)) : Nat := (let x = h(0); match x { Z => 0, S _ => 1 })
}

#eval IO.println (run "ScrutineeTypes" ScrutineeTypes).show

-- every verdict as expected, and the exact number of declarations (a truncated file changes it)
#guard (run "ScrutineeTypes" ScrutineeTypes).allAsExpected
#guard (run "ScrutineeTypes" ScrutineeTypes).count == 14

/-! Generalisations are global (D37). Forming `Esc`'s goal generalises a sealed program on a
private copy of the environment, and names it with a fresh abstract value. That record,
and the counter of fresh names, must survive the copy. Otherwise the body's split issues
the same name again, for the field `x`; `Esc` then proves that `Double(n)` is zero exactly
when `x` is, for every `n` and `x`, and its instance `Bad5` is a closed proof of `1 = 0`
(switch `globalRecords`). This is note 5 of the paper's appendix, as printed. -/

ochr GlobalRecords {
  inductive Box := MkBox(x : Nat)

  def Double (n : Nat) : Nat by n := (
    match n {
      Z => Z,
      S p => S (S (Double(p))),
    }
  )

  reject def Esc (n : Nat) (m : Box) :
      Id Nat
        (let b = Double(n); match b { Z => 0, S _ => 1 })
        (match m { MkBox(x) => match x { Z => 0, S _ => 1 } }) := (
    match m {
      MkBox(x) => match x {
        Z => refl,
        S _ => refl,
      },
    }
  )

  reject def Bad5 : Eq Nat 1 0 := Esc(1, MkBox(0))
}

#eval IO.println (run "GlobalRecords" GlobalRecords).show

-- every verdict as expected, and the exact number of declarations (a truncated file changes it)
#guard (run "GlobalRecords" GlobalRecords).allAsExpected
#guard (run "GlobalRecords" GlobalRecords).count == 4

/-! A refinement belongs to its arm (arrays-library's arm leak). [Split] substitutes into
every stored type, the types of abstract values included. Those types are kept across a
private copy or an arm only for the abstract values that the copy or arm created (D37:
fresh names are never reused). An older value's type is restored like the environment.
Otherwise, after the arm `n := Z`, a parameter `r : Slice(n)` has type `Slice(0)` in the
arm `n := S m` wherever it is typed through its value: in a closure that captures it, or
in an inferred conjunct. `Leak` is a true lemma that the stale type rejected. `T7` states
that a slice of any length is the empty one, by a closure in the second arm that sees
`r : Slice(0)`, and its instance `BoomLeak` is a closed proof of `False`. -/

ochr ArmLocal uses Std {
  def Le (a : Nat) (b : Nat) : Prop by a := (
    match a {
      Z => ⊤,
      S a' => match b {
        Z => False,
        S b' => Le(a', b'),
      },
    }
  )
  def Sub (a : Nat) (b : Nat) : Nat by b := (
    match b {
      Z => a,
      S b' => match a {
        Z => Z,
        S a' => Sub(a', b'),
      },
    }
  )
  inductive SliceOf (R : Type) := MkSlice(c : R)
  inductive Cell (R : Type) := MkC(h : Nat, t : SliceOf(R))
  inductive CellsEnd := End
  def Cells (n : Nat) : Type by n := (
    match n {
      Z => CellsEnd,
      S m => Cell(Cells(m)),
    }
  )
  def Slice (n : Nat) : Type := SliceOf(Cells(n))
  def JoinS (n : Nat) (k : Nat) (l : Slice(k)) (r : Slice(Sub(n, k))) : Slice(n) by k := (
    match k {
      Z => r,
      S k' => match n {
        Z => MkSlice(End),
        S m => match l {
          MkSlice(c) => match c {
            MkC(x, t) => MkSlice(MkC(x, JoinS(m, k', t, r))),
          },
        },
      },
    }
  )
  def AllGe (n : Nat) (s : Slice(n)) (p : Nat) : Prop by n := (
    match n {
      Z => ⊤,
      S m => match s {
        MkSlice(c) => match c {
          MkC(x, t) => Le(p, x) ∧ AllGe(m, t, p),
        },
      },
    }
  )
  def AndL (P : Prop) (Q : Prop) (h : P ∧ Q) : P := match h { Intro(p, q) => p }

  -- The arm `n := Z` is checked before the arm `n := S m`; the conjuncts of `⟨…⟩` there
  -- are typed through `r`'s value, whose type must not be the `Z` arm's `Slice(0)`.
  def Leak (n : Nat) (k : Nat) (l : Slice(k)) (r : Slice(Sub(n, k))) (a : Nat) (hl : AllGe(k, l, a))
      (ih : Π(m : Nat) (k' : Nat) (t : Slice(k')) (r2 : Slice(Sub(m, k'))). AllGe(m, JoinS(m, k', t, r2), a)) :
      AllGe(n, JoinS(n, k, l, r), a) := (
    match k {
      Z => ih(n, 0, l, r),
      S k' => match n {
        Z => ih(Z, S k', l, r),
        S m => match l {
          MkSlice(c) => match c {
            MkC(y, t) => ⟨AndL(Le(a, y), AllGe(k', t, a), hl), ih(m, k', t, r)⟩,
          },
        },
      },
    }
  )
}

#eval IO.println (run "ArmLocal" ArmLocal).show

#guard (run "ArmLocal" ArmLocal).allAsExpected
#guard (run "ArmLocal" ArmLocal).count == 11

ochr ArmLocalBoom {
  inductive Emp := E(e : Emp)
  def AbsurdEq (x : Emp) (A : Type) (a : A) (b : A) : Eq A a b by x := match x { E(e) => AbsurdEq(e, A, a, b) }
  inductive Opt (R : Type) := N0 | S0(x : R)
  inductive SliceOf (R : Type) := MkSlice(c : R)
  def Cells (n : Nat) : Type by n := match n { Z => Opt(Emp), S m => Opt(Nat) }
  def Slice (n : Nat) : Type := SliceOf(Cells(n))
  -- every `Slice(0)` is the empty one
  def EmptyEq (s : Slice(0)) : Eq (Slice(0)) s (MkSlice(N0[Emp])) := (
    match s { MkSlice(c) => match c { N0 => refl, S0(x) => AbsurdEq(x, Slice(0), MkSlice(S0[Emp](x)), MkSlice(N0[Emp])) } })
  -- `r : Slice(S m)` in the second arm, where `Eq (Slice(0)) r …` is ill-typed
  reject def T6 (n : Nat) (r : Slice(n)) : Prop := (
    match n { Z => ⊤, S m => (λ(u : Nat) : Prop => Eq (Slice(0)) r (MkSlice(N0[Emp])))(0) })
  reject def T7 (n : Nat) (r : Slice(n)) : T6(n, r) := (
    match n { Z => refl, S m => (λ(u : Nat) : Eq (Slice(0)) r (MkSlice(N0[Emp])) => EmptyEq(clone(r)))(0) })
  reject def BoomLeak : False := T7(1, MkSlice(S0[Nat](9)))
}

#eval IO.println (run "ArmLocalBoom" ArmLocalBoom).show

#guard (run "ArmLocalBoom" ArmLocalBoom).allAsExpected
#guard (run "ArmLocalBoom" ArmLocalBoom).count == 10

/-! Generalisation records belong to their arm too (reviewer-6's A1, a closed proof of `False`
in the default checker until then). In the arm `n := Z`, `match x` generalises the stuck
call `⌈g(())⌉` to a fresh `σ` of type `T(0) = Box(Unit)`. The arm `n := S m` derives the same
program text `⌈g(())⌉`, whose type there is `T(S m) = Box(Bool)`. With the record global, it
was mapped to that `σ`, typed `Box(Unit)`: `Cmp2(y)` then compared `MkBox(true)` with
`MkBox(false)` at `Unit`, which η made true, and `L2` returned `False`. Records survive a
private copy (D37), which stays within one world, but sibling arms are different worlds, so
a record an arm makes is dropped with the arm (`restoreArm`). `FLie` is the fuzzer's shape
(fuzz-port, `--a1`): the statement's arm does not call `g`, the proof's arm makes the record.
(Since η at `Unit` is a property of values, D59 refined, the comparison is no longer true at a
stale type either: `true` and `false` are distinct constructors whatever the type says.) -/

ochr ArmRecords uses Std {
  def T (n : Nat) : Type := match n { Z => Box(Unit), S _ => Box(Bool) }
  def Cmp2 (b : Box(Bool)) : Prop := (let c = clone(b); Id Unit (c := MkBox(true)) (c := MkBox(false)))
  def L2 (b : Box(Bool)) (h : Cmp2(b)) : False := h
  def G (n : Nat) : Prop := match n { Z => ⊤, S _ => False }
  reject def F (n : Nat) (g : Π(u : Unit). T(n)) : G(n) := (
    match n {
      Z => (let x = g(()); match x { MkBox(v) => refl }),
      S _ => (let y = g(()); L2(y, refl)),
    }
  )
  reject def Boom : False := F(1, λ(u : Unit) : T(1) => MkBox(true))
  reject def FLie (n0 : Nat) (g1 : Π(u : Unit). T(n0)) :
      Id Prop (match n0 { Z => ⊤, S p7 => let y6 = g1(()); Cmp2(y6) }) ⊤ := (
    match n0 { Z => (let x5 = g1(()); match x5 { MkBox(v) => refl }), S _ => refl })
  reject def FBoom : False := (
    let h = FLie(1, λ(u : Unit) : T(1) => MkBox(true));
    J(Prop, ⊤, False, λ(P : Prop) : Prop => P, symm h, refl))
}

#eval IO.println (run "ArmRecords" ArmRecords).show

#guard (run "ArmRecords" ArmRecords).allAsExpected
#guard (run "ArmRecords" ArmRecords).count == 8
