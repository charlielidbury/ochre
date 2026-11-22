import Ochr.Examples.Bool
import Ochr.Examples.Nat
import Ochr.Examples.Option
import Ochr.Examples.Box

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
  -- to a fresh abstract value, then splits on that.
  def MatchAfterOpaque (f : Π(_ : &Nat). Unit) (x : &Nat) : Unit := (
    f(&*x);
    match *x {
      Z => (),
      S _ => (),
    }
  )
}


/-! ## A generalised value has the matched place's type

Here `l` holds the sealed program `⌈let c1 = σ; AppendM(&c1, Nil); c1⌉`. The fresh value that
replaces it gets the type of the place `l`, `List`; its own head call says nothing about the
type. The guard below reads the checker's trace (an earlier version gave it type `Nat`). -/

ochr GenType {
  -- Its own list of numbers, not `Lists`' `List(A)`: the guards below read the type's name.
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

def genTrace : String := (run "GenType" GenType { trace := true }).showTrace "GenL"
#guard (genTrace.splitOn "c1⌉ to σ1 : List").length == 2

/-! A generalisation re-derived inside a Π-type. After splitting on `F(n)`'s result, a sealed
program that computes `F(n)` inside, `⌈G(σ)⌉`, is re-normalised to use the split value
(finding G1). That reaches the captures of closures and Π-types too: `InPi`'s goal holds
`⌈G(σ)⌉` as a capture of its Π, and was left stale (arrays-library). -/

ochr RenormPi {
  def F (n : Nat) : Nat by n := match n { Z => 0, S m => F(m) }
  def G (n : Nat) : Nat := (let x = F(n); match x { Z => 1, S _ => 2 })
  def Plain (n : Nat) (h : Eq(Nat, F(n), 0)) : (let k = G(n); Eq(Nat, k, 1)) := (
    let r = F(n); match r { Z => refl, S j => match h {} })
  def InPi (n : Nat) (h : Eq(Nat, F(n), 0)) : (let k = G(n); Π(u : Nat). Eq(Nat, k, 1)) := (
    let r = F(n); match r { Z => λ(u : Nat) : Eq(Nat, 1, 1) => refl, S j => match h {} })
  def InConj (n : Nat) (h : Eq(Nat, F(n), 0)) : (let k = G(n); Eq(Nat, k, 1) ∧ (Π(u : Nat). Eq(Nat, k, 1))) := (
    let r = F(n); match r { Z => ⟨refl, λ(u : Nat) : Eq(Nat, 1, 1) => refl⟩, S j => match h {} })
}


/-! ## Splitting on a result the goal is stuck on

`split f in t` finds, in the goal, a sealed program whose run is stuck on the result of a
call of `f`, generalises that result as a match on a place holding it would (D34), and
checks `t` in every arm; `split f(ā) { C(x̄) => t, … }` gives each arm, and is `split f in
match f(ā) { … }`: it names the call (D126), so a run of the code can pick the arm. "Finds" is fixed: the
goal's sealed programs in order, left to right, each followed down the chain of results its
run is stuck on, and the first result whose head call is `f`, or which stands for one that
an earlier split generalised (D61). It saves computing the result again into a place just
to match on it. -/

ochr Splitting uses Bools, Nats, Options {
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
  def PickNotZero (n : Nat) : Eq(Bool, IsZ(Pick(n)), false) := split IsZ in refl

  -- The same proof without `split`: compute `IsZ(n)` again into a place, and match on it.
  def PickNotZeroCopy (n : Nat) : Eq(Bool, IsZ(Pick(n)), false) := (
    let b = IsZ(n);
    match b {
      false => refl,
      true => refl,
    }
  )

  -- Without a split the goal stays stuck.
  reject def PickNotZeroNoSplit (n : Nat) : Eq(Bool, IsZ(Pick(n)), false) := refl

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

  def Pick22NotZero (n : Nat) (m : Nat) : Eq(Bool, IsZ(Pick22(n, m)), false) := split IsZ in split IsZ in refl

  -- With arms, when they differ; a hypothesis about the split result is refined too.
  def PickTwo (n : Nat) (h : Eq(Bool, IsZ(n), true)) : Eq(Nat, Pick(n), 2) := (
    split IsZ(n) {
      false => match h {},
      true => refl,
    }
  )

  -- The arms bind the fields of the split value, as a match's do (`Opt` is `Options`').
  def Look (n : Nat) : Opt(Nat) := (
    match n {
      Z => None,
      S m => Some(m),
    }
  )

  def Double (o : Opt(Nat)) : Nat := (
    match o {
      None => 0,
      Some(v) => Add(clone(v), v),
    }
  )

  def Val (o : Opt(Nat)) : Nat := (
    match o {
      None => 0,
      Some(v) => v,
    }
  )

  def DoubleVal (n : Nat) : Eq(Nat, Double(Look(n)), Add(Val(Look(clone(n))), Val(Look(n)))) := (
    split Look(n) {
      None => refl,
      Some(x) => refl,
    }
  )

  -- The split result's type is the head's declared result type at the call's arguments:
  -- here `Opt(A)` at the caller's `A`, the result of a generic function.
  def Wrap (A : Type) (x : A) (n : Nat) : Opt(A) := (
    match n {
      Z => None[A],
      S _ => Some(x),
    }
  )

  def Short (A : Type) (o : Opt(A)) : Prop := (
    match o {
      None => ⊤,
      Some(y) => ⊤,
    }
  )

  def WrapShort (A : Type) (x : A) (n : Nat) : Short(A, Wrap(A, x, n)) := split Wrap in refl

  -- `split f` needs the goal to be stuck on a result of `f`; the arms must be the
  -- constructors of its type, and each must prove its refined goal. A split cannot prove
  -- a false statement, and it needs the goal, so it is only in tail position.
  reject def NothingToSplit (n : Nat) : Eq(Nat, n, n) := split IsZ in refl
  reject def WrongHead (n : Nat) : Eq(Bool, IsZ(Pick(n)), false) := split Look in refl
  reject def WrongArm (n : Nat) (h : Eq(Bool, IsZ(n), true)) : Eq(Nat, Pick(n), 2) := (
    split IsZ(n) {
      false => refl,
      true => refl,
    }
  )
  reject def WrongCtors (n : Nat) : Eq(Bool, IsZ(Pick(n)), false) := (
    split IsZ(n) {
      None => refl,
      Some(x) => refl,
    }
  )
  reject def SplitLie (n : Nat) : Eq(Nat, Pick(n), 1) := split IsZ in refl
  reject def NotTail (n : Nat) : Eq(Bool, IsZ(Pick(n)), false) := (
    let p : Eq(Bool, IsZ(Pick(n)), false) = (split IsZ in refl);
    p
  )
}


/-! ## A function that ends in a split can be called (D125), and the braces form names its call (D126)

The check of a body splits the goal at a `split`, but a run of the body has no goal: before D125
the evaluation rejected `split` wherever it ran, so a data function ending in one was accepted and
every call of it rejected ("split: only in tail position"). `G` below was accepted and `H`
rejected. Now the untyped run of `split f in u` runs `u` (a typed run away from the end of a body
still rejects it). D61's braces form `split f { C(x̄) => t, … }` named no call: it bound the
generalised result found in the goal, which a run cannot find. D126 writes the call:
`split f(ā) { C(x̄) => t, … }` is `split f in match f(ā) { C(x̄) => t, … }`, and the old spelling is
rejected with what to write.

`SplitCallable` is the hunt for the class, asserted: every form the check of a body accepts at
the end of a data-valued function (the split in both forms, bare, under a `let`, under a `;`, in
the arms of a match on a number, on an inductive value, on a known constructor, on a proof, on a
value of a type with one constructor, and on a stuck call; a match on the call with no split,
`SPlain`; a call of such a function, `SCall`), each called at a known argument (`…K`, values `…KV`,
`…KU`), at an unknown argument inside another function, where the body runs (`…U`) or the call
closes off (`…S`, re-run at closed instances `…SV`, `…SU`), and through a closure (a lambda ending
in the form, `…C`, `…CV`; a lambda calling it, passed on, `…H`, `…HU`; the function passed itself,
`…G`). On main every generic definition was accepted and every call of a split rejected; only the
split was. Generated by `ochr/core/probes/split-callable/gen.py`. -/

ochr SplitCallable uses Nats {
  -- the lead's example (D125), in D126's braces form and in the `in` form
  inductive BB := TT | FF
  def IsZB (n : Nat) : BB := match n { Z => TT, S(m) => FF, }
  def VB (b : BB) : Type := match b { TT => Nat, FF => Unit, }
  def G (n : Nat) : VB(IsZB(n)) := split IsZB(n) { TT => Z, FF => (), }
  def H : Nat := G(Z)
  def HV : Eq(Nat, H, Z) := refl
  def Gi (n : Nat) : VB(IsZB(n)) := split IsZB in match IsZB(n) { TT => Z, FF => (), }
  def Hi : Nat := Gi(Z)
  def HiV : Eq(Nat, Hi, Z) := refl
  -- D61's spelling names no call: rejected with what to write
  reject def GOld (n : Nat) : VB(IsZB(n)) := split IsZB { TT => Z, FF => (), }
  inductive B := T | F
  def IsZ (n : Nat) : B := match n { Z => T, S(m) => F, }
  def V (b : B) : Type := match b { T => Nat, F => Unit, }
  def Gm (n : Nat) : V(IsZ(n)) := match IsZ(n) { T => 1, F => (), }
  def AppZ (f : Π(n : Nat). V(IsZ(n))) : Nat := f(Z)
  def AppS (f : Π(n : Nat). V(IsZ(n))) (m : Nat) : Unit := f(S(m))
  def SIn (n : Nat) : V(IsZ(n)) := split IsZ in match IsZ(n) { T => 1, F => (), }
  def SInK : Nat := SIn(Z)
  def SInKV : Eq(Nat, SIn(Z), 1) := refl
  def SInKU : Eq(Unit, SIn(S(Z)), ()) := refl
  def SInU (m : Nat) : Unit := SIn(S(m))
  def SInS (m : Nat) : V(IsZ(m)) := SIn(m)
  def SInSV : Eq(Nat, SInS(Z), 1) := refl
  def SInSU : Eq(Unit, SInS(S(Z)), ()) := refl
  def SInC : Nat := (let c = (λ(n : Nat) : V(IsZ(n)) => (split IsZ in match IsZ(n) { T => 1, F => (), })); c(Z))
  def SInCV : Eq(Nat, (let c = (λ(n : Nat) : V(IsZ(n)) => (split IsZ in match IsZ(n) { T => 1, F => (), })); c(Z)), 1) := refl
  def SInH : Eq(Nat, AppZ(λ(n : Nat) : V(IsZ(n)) => SIn(n)), 1) := refl
  def SInHU (m : Nat) : Eq(Unit, AppS(λ(n : Nat) : V(IsZ(n)) => SIn(n), m), ()) := refl
  def SInG : Eq(Nat, AppZ(SIn), 1) := refl
  def SBr (n : Nat) : V(IsZ(n)) := split IsZ(n) { T => 1, F => (), }
  def SBrK : Nat := SBr(Z)
  def SBrKV : Eq(Nat, SBr(Z), 1) := refl
  def SBrKU : Eq(Unit, SBr(S(Z)), ()) := refl
  def SBrU (m : Nat) : Unit := SBr(S(m))
  def SBrS (m : Nat) : V(IsZ(m)) := SBr(m)
  def SBrSV : Eq(Nat, SBrS(Z), 1) := refl
  def SBrSU : Eq(Unit, SBrS(S(Z)), ()) := refl
  def SBrC : Nat := (let c = (λ(n : Nat) : V(IsZ(n)) => (split IsZ(n) { T => 1, F => (), })); c(Z))
  def SBrCV : Eq(Nat, (let c = (λ(n : Nat) : V(IsZ(n)) => (split IsZ(n) { T => 1, F => (), })); c(Z)), 1) := refl
  def SBrH : Eq(Nat, AppZ(λ(n : Nat) : V(IsZ(n)) => SBr(n)), 1) := refl
  def SBrHU (m : Nat) : Eq(Unit, AppS(λ(n : Nat) : V(IsZ(n)) => SBr(n), m), ()) := refl
  def SBrG : Eq(Nat, AppZ(SBr), 1) := refl
  def SBare (n : Nat) : V(IsZ(n)) := split IsZ in Gm(n)
  def SBareK : Nat := SBare(Z)
  def SBareKV : Eq(Nat, SBare(Z), 1) := refl
  def SBareKU : Eq(Unit, SBare(S(Z)), ()) := refl
  def SBareU (m : Nat) : Unit := SBare(S(m))
  def SBareS (m : Nat) : V(IsZ(m)) := SBare(m)
  def SBareSV : Eq(Nat, SBareS(Z), 1) := refl
  def SBareSU : Eq(Unit, SBareS(S(Z)), ()) := refl
  def SBareC : Nat := (let c = (λ(n : Nat) : V(IsZ(n)) => (split IsZ in Gm(n))); c(Z))
  def SBareCV : Eq(Nat, (let c = (λ(n : Nat) : V(IsZ(n)) => (split IsZ in Gm(n))); c(Z)), 1) := refl
  def SBareH : Eq(Nat, AppZ(λ(n : Nat) : V(IsZ(n)) => SBare(n)), 1) := refl
  def SBareHU (m : Nat) : Eq(Unit, AppS(λ(n : Nat) : V(IsZ(n)) => SBare(n), m), ()) := refl
  def SBareG : Eq(Nat, AppZ(SBare), 1) := refl
  def SLetIn (n : Nat) : V(IsZ(n)) := (let a = 0; split IsZ in match IsZ(n) { T => 1, F => (), })
  def SLetInK : Nat := SLetIn(Z)
  def SLetInKV : Eq(Nat, SLetIn(Z), 1) := refl
  def SLetInKU : Eq(Unit, SLetIn(S(Z)), ()) := refl
  def SLetInU (m : Nat) : Unit := SLetIn(S(m))
  def SLetInS (m : Nat) : V(IsZ(m)) := SLetIn(m)
  def SLetInSV : Eq(Nat, SLetInS(Z), 1) := refl
  def SLetInSU : Eq(Unit, SLetInS(S(Z)), ()) := refl
  def SLetInC : Nat := (let c = (λ(n : Nat) : V(IsZ(n)) => ((let a = 0; split IsZ in match IsZ(n) { T => 1, F => (), }))); c(Z))
  def SLetInCV : Eq(Nat, (let c = (λ(n : Nat) : V(IsZ(n)) => ((let a = 0; split IsZ in match IsZ(n) { T => 1, F => (), }))); c(Z)), 1) := refl
  def SLetInH : Eq(Nat, AppZ(λ(n : Nat) : V(IsZ(n)) => SLetIn(n)), 1) := refl
  def SLetInHU (m : Nat) : Eq(Unit, AppS(λ(n : Nat) : V(IsZ(n)) => SLetIn(n), m), ()) := refl
  def SLetInG : Eq(Nat, AppZ(SLetIn), 1) := refl
  def SLetBr (n : Nat) : V(IsZ(n)) := (let a = 0; split IsZ(n) { T => 1, F => (), })
  def SLetBrK : Nat := SLetBr(Z)
  def SLetBrKV : Eq(Nat, SLetBr(Z), 1) := refl
  def SLetBrKU : Eq(Unit, SLetBr(S(Z)), ()) := refl
  def SLetBrU (m : Nat) : Unit := SLetBr(S(m))
  def SLetBrS (m : Nat) : V(IsZ(m)) := SLetBr(m)
  def SLetBrSV : Eq(Nat, SLetBrS(Z), 1) := refl
  def SLetBrSU : Eq(Unit, SLetBrS(S(Z)), ()) := refl
  def SLetBrC : Nat := (let c = (λ(n : Nat) : V(IsZ(n)) => ((let a = 0; split IsZ(n) { T => 1, F => (), }))); c(Z))
  def SLetBrCV : Eq(Nat, (let c = (λ(n : Nat) : V(IsZ(n)) => ((let a = 0; split IsZ(n) { T => 1, F => (), }))); c(Z)), 1) := refl
  def SLetBrH : Eq(Nat, AppZ(λ(n : Nat) : V(IsZ(n)) => SLetBr(n)), 1) := refl
  def SLetBrHU (m : Nat) : Eq(Unit, AppS(λ(n : Nat) : V(IsZ(n)) => SLetBr(n), m), ()) := refl
  def SLetBrG : Eq(Nat, AppZ(SLetBr), 1) := refl
  def SSeqIn (n : Nat) : V(IsZ(n)) := ((); split IsZ in match IsZ(n) { T => 1, F => (), })
  def SSeqInK : Nat := SSeqIn(Z)
  def SSeqInKV : Eq(Nat, SSeqIn(Z), 1) := refl
  def SSeqInKU : Eq(Unit, SSeqIn(S(Z)), ()) := refl
  def SSeqInU (m : Nat) : Unit := SSeqIn(S(m))
  def SSeqInS (m : Nat) : V(IsZ(m)) := SSeqIn(m)
  def SSeqInSV : Eq(Nat, SSeqInS(Z), 1) := refl
  def SSeqInSU : Eq(Unit, SSeqInS(S(Z)), ()) := refl
  def SSeqInC : Nat := (let c = (λ(n : Nat) : V(IsZ(n)) => (((); split IsZ in match IsZ(n) { T => 1, F => (), }))); c(Z))
  def SSeqInCV : Eq(Nat, (let c = (λ(n : Nat) : V(IsZ(n)) => (((); split IsZ in match IsZ(n) { T => 1, F => (), }))); c(Z)), 1) := refl
  def SSeqInH : Eq(Nat, AppZ(λ(n : Nat) : V(IsZ(n)) => SSeqIn(n)), 1) := refl
  def SSeqInHU (m : Nat) : Eq(Unit, AppS(λ(n : Nat) : V(IsZ(n)) => SSeqIn(n), m), ()) := refl
  def SSeqInG : Eq(Nat, AppZ(SSeqIn), 1) := refl
  def SSeqBr (n : Nat) : V(IsZ(n)) := ((); split IsZ(n) { T => 1, F => (), })
  def SSeqBrK : Nat := SSeqBr(Z)
  def SSeqBrKV : Eq(Nat, SSeqBr(Z), 1) := refl
  def SSeqBrKU : Eq(Unit, SSeqBr(S(Z)), ()) := refl
  def SSeqBrU (m : Nat) : Unit := SSeqBr(S(m))
  def SSeqBrS (m : Nat) : V(IsZ(m)) := SSeqBr(m)
  def SSeqBrSV : Eq(Nat, SSeqBrS(Z), 1) := refl
  def SSeqBrSU : Eq(Unit, SSeqBrS(S(Z)), ()) := refl
  def SSeqBrC : Nat := (let c = (λ(n : Nat) : V(IsZ(n)) => (((); split IsZ(n) { T => 1, F => (), }))); c(Z))
  def SSeqBrCV : Eq(Nat, (let c = (λ(n : Nat) : V(IsZ(n)) => (((); split IsZ(n) { T => 1, F => (), }))); c(Z)), 1) := refl
  def SSeqBrH : Eq(Nat, AppZ(λ(n : Nat) : V(IsZ(n)) => SSeqBr(n)), 1) := refl
  def SSeqBrHU (m : Nat) : Eq(Unit, AppS(λ(n : Nat) : V(IsZ(n)) => SSeqBr(n), m), ()) := refl
  def SSeqBrG : Eq(Nat, AppZ(SSeqBr), 1) := refl
  def SNatIn (n : Nat) (k : Nat) : V(IsZ(n)) := match k { Z => split IsZ in match IsZ(n) { T => 1, F => (), }, S(j) => split IsZ in match IsZ(n) { T => 1, F => (), }, }
  def SNatInK : Nat := SNatIn(Z, Z)
  def SNatInKV : Eq(Nat, SNatIn(Z, Z), 1) := refl
  def SNatInKU : Eq(Unit, SNatIn(S(Z), Z), ()) := refl
  def SNatInU (m : Nat) : Unit := SNatIn(S(m), Z)
  def SNatInS (m : Nat) : V(IsZ(m)) := SNatIn(m, Z)
  def SNatInSV : Eq(Nat, SNatInS(Z), 1) := refl
  def SNatInSU : Eq(Unit, SNatInS(S(Z)), ()) := refl
  def SNatInC : Nat := (let c = (λ(n : Nat) (k : Nat) : V(IsZ(n)) => (match k { Z => split IsZ in match IsZ(n) { T => 1, F => (), }, S(j) => split IsZ in match IsZ(n) { T => 1, F => (), }, })); c(Z, Z))
  def SNatInCV : Eq(Nat, (let c = (λ(n : Nat) (k : Nat) : V(IsZ(n)) => (match k { Z => split IsZ in match IsZ(n) { T => 1, F => (), }, S(j) => split IsZ in match IsZ(n) { T => 1, F => (), }, })); c(Z, Z)), 1) := refl
  def SNatInH : Eq(Nat, AppZ(λ(n : Nat) : V(IsZ(n)) => SNatIn(n, Z)), 1) := refl
  def SNatInHU (m : Nat) : Eq(Unit, AppS(λ(n : Nat) : V(IsZ(n)) => SNatIn(n, Z), m), ()) := refl
  def SNatBr (n : Nat) (k : Nat) : V(IsZ(n)) := match k { Z => split IsZ(n) { T => 1, F => (), }, S(j) => split IsZ(n) { T => 1, F => (), }, }
  def SNatBrK : Nat := SNatBr(Z, Z)
  def SNatBrKV : Eq(Nat, SNatBr(Z, Z), 1) := refl
  def SNatBrKU : Eq(Unit, SNatBr(S(Z), Z), ()) := refl
  def SNatBrU (m : Nat) : Unit := SNatBr(S(m), Z)
  def SNatBrS (m : Nat) : V(IsZ(m)) := SNatBr(m, Z)
  def SNatBrSV : Eq(Nat, SNatBrS(Z), 1) := refl
  def SNatBrSU : Eq(Unit, SNatBrS(S(Z)), ()) := refl
  def SNatBrC : Nat := (let c = (λ(n : Nat) (k : Nat) : V(IsZ(n)) => (match k { Z => split IsZ(n) { T => 1, F => (), }, S(j) => split IsZ(n) { T => 1, F => (), }, })); c(Z, Z))
  def SNatBrCV : Eq(Nat, (let c = (λ(n : Nat) (k : Nat) : V(IsZ(n)) => (match k { Z => split IsZ(n) { T => 1, F => (), }, S(j) => split IsZ(n) { T => 1, F => (), }, })); c(Z, Z)), 1) := refl
  def SNatBrH : Eq(Nat, AppZ(λ(n : Nat) : V(IsZ(n)) => SNatBr(n, Z)), 1) := refl
  def SNatBrHU (m : Nat) : Eq(Unit, AppS(λ(n : Nat) : V(IsZ(n)) => SNatBr(n, Z), m), ()) := refl
  def SIndIn (n : Nat) (c : B) : V(IsZ(n)) := match c { T => split IsZ in match IsZ(n) { T => 1, F => (), }, F => split IsZ in match IsZ(n) { T => 1, F => (), }, }
  def SIndInK : Nat := SIndIn(Z, T)
  def SIndInKV : Eq(Nat, SIndIn(Z, T), 1) := refl
  def SIndInKU : Eq(Unit, SIndIn(S(Z), T), ()) := refl
  def SIndInU (m : Nat) : Unit := SIndIn(S(m), T)
  def SIndInS (m : Nat) : V(IsZ(m)) := SIndIn(m, T)
  def SIndInSV : Eq(Nat, SIndInS(Z), 1) := refl
  def SIndInSU : Eq(Unit, SIndInS(S(Z)), ()) := refl
  def SIndInC : Nat := (let c = (λ(n : Nat) (c : B) : V(IsZ(n)) => (match c { T => split IsZ in match IsZ(n) { T => 1, F => (), }, F => split IsZ in match IsZ(n) { T => 1, F => (), }, })); c(Z, T))
  def SIndInCV : Eq(Nat, (let c = (λ(n : Nat) (c : B) : V(IsZ(n)) => (match c { T => split IsZ in match IsZ(n) { T => 1, F => (), }, F => split IsZ in match IsZ(n) { T => 1, F => (), }, })); c(Z, T)), 1) := refl
  def SIndInH : Eq(Nat, AppZ(λ(n : Nat) : V(IsZ(n)) => SIndIn(n, T)), 1) := refl
  def SIndInHU (m : Nat) : Eq(Unit, AppS(λ(n : Nat) : V(IsZ(n)) => SIndIn(n, T), m), ()) := refl
  def SIndBr (n : Nat) (c : B) : V(IsZ(n)) := match c { T => split IsZ(n) { T => 1, F => (), }, F => split IsZ(n) { T => 1, F => (), }, }
  def SIndBrK : Nat := SIndBr(Z, T)
  def SIndBrKV : Eq(Nat, SIndBr(Z, T), 1) := refl
  def SIndBrKU : Eq(Unit, SIndBr(S(Z), T), ()) := refl
  def SIndBrU (m : Nat) : Unit := SIndBr(S(m), T)
  def SIndBrS (m : Nat) : V(IsZ(m)) := SIndBr(m, T)
  def SIndBrSV : Eq(Nat, SIndBrS(Z), 1) := refl
  def SIndBrSU : Eq(Unit, SIndBrS(S(Z)), ()) := refl
  def SIndBrC : Nat := (let c = (λ(n : Nat) (c : B) : V(IsZ(n)) => (match c { T => split IsZ(n) { T => 1, F => (), }, F => split IsZ(n) { T => 1, F => (), }, })); c(Z, T))
  def SIndBrCV : Eq(Nat, (let c = (λ(n : Nat) (c : B) : V(IsZ(n)) => (match c { T => split IsZ(n) { T => 1, F => (), }, F => split IsZ(n) { T => 1, F => (), }, })); c(Z, T)), 1) := refl
  def SIndBrH : Eq(Nat, AppZ(λ(n : Nat) : V(IsZ(n)) => SIndBr(n, T)), 1) := refl
  def SIndBrHU (m : Nat) : Eq(Unit, AppS(λ(n : Nat) : V(IsZ(n)) => SIndBr(n, T), m), ()) := refl
  def SKnownIn (n : Nat) : V(IsZ(n)) := (let c = F; match c { T => split IsZ in match IsZ(n) { T => 1, F => (), }, F => split IsZ in match IsZ(n) { T => 1, F => (), }, })
  def SKnownInK : Nat := SKnownIn(Z)
  def SKnownInKV : Eq(Nat, SKnownIn(Z), 1) := refl
  def SKnownInKU : Eq(Unit, SKnownIn(S(Z)), ()) := refl
  def SKnownInU (m : Nat) : Unit := SKnownIn(S(m))
  def SKnownInS (m : Nat) : V(IsZ(m)) := SKnownIn(m)
  def SKnownInSV : Eq(Nat, SKnownInS(Z), 1) := refl
  def SKnownInSU : Eq(Unit, SKnownInS(S(Z)), ()) := refl
  def SKnownInC : Nat := (let c = (λ(n : Nat) : V(IsZ(n)) => ((let c = F; match c { T => split IsZ in match IsZ(n) { T => 1, F => (), }, F => split IsZ in match IsZ(n) { T => 1, F => (), }, }))); c(Z))
  def SKnownInCV : Eq(Nat, (let c = (λ(n : Nat) : V(IsZ(n)) => ((let c = F; match c { T => split IsZ in match IsZ(n) { T => 1, F => (), }, F => split IsZ in match IsZ(n) { T => 1, F => (), }, }))); c(Z)), 1) := refl
  def SKnownInH : Eq(Nat, AppZ(λ(n : Nat) : V(IsZ(n)) => SKnownIn(n)), 1) := refl
  def SKnownInHU (m : Nat) : Eq(Unit, AppS(λ(n : Nat) : V(IsZ(n)) => SKnownIn(n), m), ()) := refl
  def SKnownInG : Eq(Nat, AppZ(SKnownIn), 1) := refl
  def SKnownBr (n : Nat) : V(IsZ(n)) := (let c = F; match c { T => split IsZ(n) { T => 1, F => (), }, F => split IsZ(n) { T => 1, F => (), }, })
  def SKnownBrK : Nat := SKnownBr(Z)
  def SKnownBrKV : Eq(Nat, SKnownBr(Z), 1) := refl
  def SKnownBrKU : Eq(Unit, SKnownBr(S(Z)), ()) := refl
  def SKnownBrU (m : Nat) : Unit := SKnownBr(S(m))
  def SKnownBrS (m : Nat) : V(IsZ(m)) := SKnownBr(m)
  def SKnownBrSV : Eq(Nat, SKnownBrS(Z), 1) := refl
  def SKnownBrSU : Eq(Unit, SKnownBrS(S(Z)), ()) := refl
  def SKnownBrC : Nat := (let c = (λ(n : Nat) : V(IsZ(n)) => ((let c = F; match c { T => split IsZ(n) { T => 1, F => (), }, F => split IsZ(n) { T => 1, F => (), }, }))); c(Z))
  def SKnownBrCV : Eq(Nat, (let c = (λ(n : Nat) : V(IsZ(n)) => ((let c = F; match c { T => split IsZ(n) { T => 1, F => (), }, F => split IsZ(n) { T => 1, F => (), }, }))); c(Z)), 1) := refl
  def SKnownBrH : Eq(Nat, AppZ(λ(n : Nat) : V(IsZ(n)) => SKnownBr(n)), 1) := refl
  def SKnownBrHU (m : Nat) : Eq(Unit, AppS(λ(n : Nat) : V(IsZ(n)) => SKnownBr(n), m), ()) := refl
  def SKnownBrG : Eq(Nat, AppZ(SKnownBr), 1) := refl
  def SProofIn (n : Nat) (h : And(⊤, ⊤)) : V(IsZ(n)) := match h { Intro(a, b) => split IsZ in match IsZ(n) { T => 1, F => (), }, }
  def SProofInK : Nat := SProofIn(Z, ⟨refl, refl⟩)
  def SProofInKV : Eq(Nat, SProofIn(Z, ⟨refl, refl⟩), 1) := refl
  def SProofInKU : Eq(Unit, SProofIn(S(Z), ⟨refl, refl⟩), ()) := refl
  def SProofInU (m : Nat) : Unit := SProofIn(S(m), ⟨refl, refl⟩)
  def SProofInS (m : Nat) : V(IsZ(m)) := SProofIn(m, ⟨refl, refl⟩)
  def SProofInSV : Eq(Nat, SProofInS(Z), 1) := refl
  def SProofInSU : Eq(Unit, SProofInS(S(Z)), ()) := refl
  def SProofInC : Nat := (let c = (λ(n : Nat) (h : And(⊤, ⊤)) : V(IsZ(n)) => (match h { Intro(a, b) => split IsZ in match IsZ(n) { T => 1, F => (), }, })); c(Z, ⟨refl, refl⟩))
  def SProofInCV : Eq(Nat, (let c = (λ(n : Nat) (h : And(⊤, ⊤)) : V(IsZ(n)) => (match h { Intro(a, b) => split IsZ in match IsZ(n) { T => 1, F => (), }, })); c(Z, ⟨refl, refl⟩)), 1) := refl
  def SProofInH : Eq(Nat, AppZ(λ(n : Nat) : V(IsZ(n)) => SProofIn(n, ⟨refl, refl⟩)), 1) := refl
  def SProofInHU (m : Nat) : Eq(Unit, AppS(λ(n : Nat) : V(IsZ(n)) => SProofIn(n, ⟨refl, refl⟩), m), ()) := refl
  def SProofBr (n : Nat) (h : And(⊤, ⊤)) : V(IsZ(n)) := match h { Intro(a, b) => split IsZ(n) { T => 1, F => (), }, }
  def SProofBrK : Nat := SProofBr(Z, ⟨refl, refl⟩)
  def SProofBrKV : Eq(Nat, SProofBr(Z, ⟨refl, refl⟩), 1) := refl
  def SProofBrKU : Eq(Unit, SProofBr(S(Z), ⟨refl, refl⟩), ()) := refl
  def SProofBrU (m : Nat) : Unit := SProofBr(S(m), ⟨refl, refl⟩)
  def SProofBrS (m : Nat) : V(IsZ(m)) := SProofBr(m, ⟨refl, refl⟩)
  def SProofBrSV : Eq(Nat, SProofBrS(Z), 1) := refl
  def SProofBrSU : Eq(Unit, SProofBrS(S(Z)), ()) := refl
  def SProofBrC : Nat := (let c = (λ(n : Nat) (h : And(⊤, ⊤)) : V(IsZ(n)) => (match h { Intro(a, b) => split IsZ(n) { T => 1, F => (), }, })); c(Z, ⟨refl, refl⟩))
  def SProofBrCV : Eq(Nat, (let c = (λ(n : Nat) (h : And(⊤, ⊤)) : V(IsZ(n)) => (match h { Intro(a, b) => split IsZ(n) { T => 1, F => (), }, })); c(Z, ⟨refl, refl⟩)), 1) := refl
  def SProofBrH : Eq(Nat, AppZ(λ(n : Nat) : V(IsZ(n)) => SProofBr(n, ⟨refl, refl⟩)), 1) := refl
  def SProofBrHU (m : Nat) : Eq(Unit, AppS(λ(n : Nat) : V(IsZ(n)) => SProofBr(n, ⟨refl, refl⟩), m), ()) := refl
  def SOneIn (n : Nat) (p : Pair(Nat, Nat)) : V(IsZ(n)) := (let (x, y) = p; split IsZ in match IsZ(n) { T => 1, F => (), })
  def SOneInK : Nat := SOneIn(Z, (0, 0))
  def SOneInKV : Eq(Nat, SOneIn(Z, (0, 0)), 1) := refl
  def SOneInKU : Eq(Unit, SOneIn(S(Z), (0, 0)), ()) := refl
  def SOneInU (m : Nat) : Unit := SOneIn(S(m), (0, 0))
  def SOneInS (m : Nat) : V(IsZ(m)) := SOneIn(m, (0, 0))
  def SOneInSV : Eq(Nat, SOneInS(Z), 1) := refl
  def SOneInSU : Eq(Unit, SOneInS(S(Z)), ()) := refl
  def SOneInC : Nat := (let c = (λ(n : Nat) (p : Pair(Nat, Nat)) : V(IsZ(n)) => ((let (x, y) = p; split IsZ in match IsZ(n) { T => 1, F => (), }))); c(Z, (0, 0)))
  def SOneInCV : Eq(Nat, (let c = (λ(n : Nat) (p : Pair(Nat, Nat)) : V(IsZ(n)) => ((let (x, y) = p; split IsZ in match IsZ(n) { T => 1, F => (), }))); c(Z, (0, 0))), 1) := refl
  def SOneInH : Eq(Nat, AppZ(λ(n : Nat) : V(IsZ(n)) => SOneIn(n, (0, 0))), 1) := refl
  def SOneInHU (m : Nat) : Eq(Unit, AppS(λ(n : Nat) : V(IsZ(n)) => SOneIn(n, (0, 0)), m), ()) := refl
  def SOneBr (n : Nat) (p : Pair(Nat, Nat)) : V(IsZ(n)) := (let (x, y) = p; split IsZ(n) { T => 1, F => (), })
  def SOneBrK : Nat := SOneBr(Z, (0, 0))
  def SOneBrKV : Eq(Nat, SOneBr(Z, (0, 0)), 1) := refl
  def SOneBrKU : Eq(Unit, SOneBr(S(Z), (0, 0)), ()) := refl
  def SOneBrU (m : Nat) : Unit := SOneBr(S(m), (0, 0))
  def SOneBrS (m : Nat) : V(IsZ(m)) := SOneBr(m, (0, 0))
  def SOneBrSV : Eq(Nat, SOneBrS(Z), 1) := refl
  def SOneBrSU : Eq(Unit, SOneBrS(S(Z)), ()) := refl
  def SOneBrC : Nat := (let c = (λ(n : Nat) (p : Pair(Nat, Nat)) : V(IsZ(n)) => ((let (x, y) = p; split IsZ(n) { T => 1, F => (), }))); c(Z, (0, 0)))
  def SOneBrCV : Eq(Nat, (let c = (λ(n : Nat) (p : Pair(Nat, Nat)) : V(IsZ(n)) => ((let (x, y) = p; split IsZ(n) { T => 1, F => (), }))); c(Z, (0, 0))), 1) := refl
  def SOneBrH : Eq(Nat, AppZ(λ(n : Nat) : V(IsZ(n)) => SOneBr(n, (0, 0))), 1) := refl
  def SOneBrHU (m : Nat) : Eq(Unit, AppS(λ(n : Nat) : V(IsZ(n)) => SOneBr(n, (0, 0)), m), ()) := refl
  def SSealIn (n : Nat) (k : Nat) : V(IsZ(n)) := match IsZ(k) { T => split IsZ in match IsZ(n) { T => 1, F => (), }, F => split IsZ in match IsZ(n) { T => 1, F => (), }, }
  def SSealInK : Nat := SSealIn(Z, Z)
  def SSealInKV : Eq(Nat, SSealIn(Z, Z), 1) := refl
  def SSealInKU : Eq(Unit, SSealIn(S(Z), Z), ()) := refl
  def SSealInU (m : Nat) : Unit := SSealIn(S(m), Z)
  def SSealInS (m : Nat) : V(IsZ(m)) := SSealIn(m, Z)
  def SSealInSV : Eq(Nat, SSealInS(Z), 1) := refl
  def SSealInSU : Eq(Unit, SSealInS(S(Z)), ()) := refl
  def SSealInC : Nat := (let c = (λ(n : Nat) (k : Nat) : V(IsZ(n)) => (match IsZ(k) { T => split IsZ in match IsZ(n) { T => 1, F => (), }, F => split IsZ in match IsZ(n) { T => 1, F => (), }, })); c(Z, Z))
  def SSealInCV : Eq(Nat, (let c = (λ(n : Nat) (k : Nat) : V(IsZ(n)) => (match IsZ(k) { T => split IsZ in match IsZ(n) { T => 1, F => (), }, F => split IsZ in match IsZ(n) { T => 1, F => (), }, })); c(Z, Z)), 1) := refl
  def SSealInH : Eq(Nat, AppZ(λ(n : Nat) : V(IsZ(n)) => SSealIn(n, Z)), 1) := refl
  def SSealInHU (m : Nat) : Eq(Unit, AppS(λ(n : Nat) : V(IsZ(n)) => SSealIn(n, Z), m), ()) := refl
  def SSealBr (n : Nat) (k : Nat) : V(IsZ(n)) := match IsZ(k) { T => split IsZ(n) { T => 1, F => (), }, F => split IsZ(n) { T => 1, F => (), }, }
  def SSealBrK : Nat := SSealBr(Z, Z)
  def SSealBrKV : Eq(Nat, SSealBr(Z, Z), 1) := refl
  def SSealBrKU : Eq(Unit, SSealBr(S(Z), Z), ()) := refl
  def SSealBrU (m : Nat) : Unit := SSealBr(S(m), Z)
  def SSealBrS (m : Nat) : V(IsZ(m)) := SSealBr(m, Z)
  def SSealBrSV : Eq(Nat, SSealBrS(Z), 1) := refl
  def SSealBrSU : Eq(Unit, SSealBrS(S(Z)), ()) := refl
  def SSealBrC : Nat := (let c = (λ(n : Nat) (k : Nat) : V(IsZ(n)) => (match IsZ(k) { T => split IsZ(n) { T => 1, F => (), }, F => split IsZ(n) { T => 1, F => (), }, })); c(Z, Z))
  def SSealBrCV : Eq(Nat, (let c = (λ(n : Nat) (k : Nat) : V(IsZ(n)) => (match IsZ(k) { T => split IsZ(n) { T => 1, F => (), }, F => split IsZ(n) { T => 1, F => (), }, })); c(Z, Z)), 1) := refl
  def SSealBrH : Eq(Nat, AppZ(λ(n : Nat) : V(IsZ(n)) => SSealBr(n, Z)), 1) := refl
  def SSealBrHU (m : Nat) : Eq(Unit, AppS(λ(n : Nat) : V(IsZ(n)) => SSealBr(n, Z), m), ()) := refl
  def SPlain (n : Nat) : V(IsZ(n)) := match IsZ(n) { T => 1, F => (), }
  def SPlainK : Nat := SPlain(Z)
  def SPlainKV : Eq(Nat, SPlain(Z), 1) := refl
  def SPlainKU : Eq(Unit, SPlain(S(Z)), ()) := refl
  def SPlainU (m : Nat) : Unit := SPlain(S(m))
  def SPlainS (m : Nat) : V(IsZ(m)) := SPlain(m)
  def SPlainSV : Eq(Nat, SPlainS(Z), 1) := refl
  def SPlainSU : Eq(Unit, SPlainS(S(Z)), ()) := refl
  def SPlainC : Nat := (let c = (λ(n : Nat) : V(IsZ(n)) => (match IsZ(n) { T => 1, F => (), })); c(Z))
  def SPlainCV : Eq(Nat, (let c = (λ(n : Nat) : V(IsZ(n)) => (match IsZ(n) { T => 1, F => (), })); c(Z)), 1) := refl
  def SPlainH : Eq(Nat, AppZ(λ(n : Nat) : V(IsZ(n)) => SPlain(n)), 1) := refl
  def SPlainHU (m : Nat) : Eq(Unit, AppS(λ(n : Nat) : V(IsZ(n)) => SPlain(n), m), ()) := refl
  def SPlainG : Eq(Nat, AppZ(SPlain), 1) := refl
  def SCall (n : Nat) : V(IsZ(n)) := SIn(n)
  def SCallK : Nat := SCall(Z)
  def SCallKV : Eq(Nat, SCall(Z), 1) := refl
  def SCallKU : Eq(Unit, SCall(S(Z)), ()) := refl
  def SCallU (m : Nat) : Unit := SCall(S(m))
  def SCallS (m : Nat) : V(IsZ(m)) := SCall(m)
  def SCallSV : Eq(Nat, SCallS(Z), 1) := refl
  def SCallSU : Eq(Unit, SCallS(S(Z)), ()) := refl
  def SCallC : Nat := (let c = (λ(n : Nat) : V(IsZ(n)) => (SIn(n))); c(Z))
  def SCallCV : Eq(Nat, (let c = (λ(n : Nat) : V(IsZ(n)) => (SIn(n))); c(Z)), 1) := refl
  def SCallH : Eq(Nat, AppZ(λ(n : Nat) : V(IsZ(n)) => SCall(n)), 1) := refl
  def SCallHU (m : Nat) : Eq(Unit, AppS(λ(n : Nat) : V(IsZ(n)) => SCall(n), m), ()) := refl
  def SCallG : Eq(Nat, AppZ(SCall), 1) := refl
}

#guard (run "SplitCallable" SplitCallable).rejectedWith [
  ("GOld", "(surface) split IsZB { … } names no call: write the call of IsZB the goal is stuck on, `split IsZB(a, …) { … }`, which is `split IsZB in match IsZB(a, …) { … }` (D126)")]


/-! ## What goes wrong without these rules

A match must be on a place whose type is the arms' inductive type, read from the place's
stored type (not assumed from the arms). An earlier checker assumed it from the arms: it
accepted `f` below by splitting `x : T(n)` with `L`'s constructors, and `g(5)` would then run
`L`'s arms on the number 5. -/

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

  -- twin of f: the match is on `x` at the type `T(n)` refined by splitting `n` first, so `x : L` in the arm
  def fOk (n : Nat) (x : T(n)) : Nat := (
    match n {
      Z => match x {
        LNil => 0,
        LCons(h, t) => 0,
      },
      S _ => 0,
    }
  )

  -- twin of g: the argument is an `L`, passed at `T(0)`
  def gOk (x : L) : Nat := fOk(0, x)

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

  -- twin of NatT: `x` is a `Nat`, not a type variable
  def NatTOk (x : Nat) : Nat := (match x { Z => 0, S _ => 1 })
  -- twin of NatTUse: calls `NatTOk` at a `Nat`
  def NatTUseOk (b : Nat) : Nat := NatTOk(b)
  -- twin of NatTNT: `x` is a `Nat`, not a type variable
  def NatTNTOk (x : Nat) : Nat := (let r = match x { Z => 0, S _ => 1 }; r)
  -- twin of M2: `h` returns `Nat` instead of the stuck family `TG(n)`
  def M2Ok (n : Nat) (h : Π(n : Nat). Nat) : Nat := (let x = h(n); match x { Z => 0, S _ => 1 })

  -- Where the family computes to `Nat`, the match is fine.
  def M2Zero (h : Π(n : Nat). TG(n)) : Nat := (let x = h(0); match x { Z => 0, S _ => 1 })
}


/-! Generalisations are global (D37). Forming `Esc`'s goal generalises a sealed program on a
private copy of the environment, and names it with a fresh abstract value. That record,
and the counter of fresh names, must survive the copy. Otherwise the body's split issues
the same name again, for the field `x`; `Esc` then proves that `Double(n)` is zero exactly
when `x` is, for every `n` and `x`, and its instance `Bad5` is a closed proof of `1 = 0`. This is note 5 of the paper's appendix, as printed. -/

ochr GlobalRecords {
  -- As printed in the paper, with its own `Box` of a number.
  inductive Box := MkBox(x : Nat)

  def Double (n : Nat) : Nat by n := (
    match n {
      Z => Z,
      S p => S(S(Double(p))),
    }
  )

  reject def Esc (n : Nat) (m : Box) :
      Id(Nat, (let b = Double(clone(n)); match b { Z => 0, S _ => 1 }), (match m { MkBox(x) => match x { Z => 0, S _ => 1 } })) := (
    match m {
      MkBox(x) => match x {
        Z => refl,
        S _ => refl,
      },
    }
  )

  reject def Bad5 : Eq(Nat, 1, 0) := Esc(1, MkBox(0))

  -- twin of Esc: both sides are the same sealed program, so the (true) statement does not tie a split of `Double(n)` to the field `x`
  def EscOk (n : Nat) (m : Box) :
      Id(Nat, (let b = Double(n); match b { Z => 0, S _ => 1 }), (let c = Double(n); match c { Z => 0, S _ => 1 })) := (
    match m {
      MkBox(x) => match x {
        Z => refl,
        S _ => refl,
      },
    }
  )

  -- twin of Bad5: instance of the true `EscOk`, at `n := 1`
  def Bad5Ok : Id(Nat, (let b = Double(1); match b { Z => 0, S _ => 1 }), (let c = Double(1); match c { Z => 0, S _ => 1 })) := EscOk(1, MkBox(0))
}


/-! A refinement belongs to its arm (arrays-library's arm leak). [Split] substitutes into
every stored type, the types of abstract values included. Those types are kept across a
private copy or an arm only for the abstract values that the copy or arm created (D37:
fresh names are never reused). An older value's type is restored like the environment.
Otherwise, after the arm `n := Z`, a parameter `r : Slice(n)` has type `Slice(0)` in the
arm `n := S m` wherever it is typed through its value: in a closure that captures it, or
in an inferred conjunct. `Leak` is a true lemma that the stale type rejected. `T7` states
that a slice of any length is the empty one, by a closure in the second arm that sees
`r : Slice(0)`, and its instance `BoomLeak` is a closed proof of `False`. -/

ochr ArmLocal {
  -- The witness's own model, on `Nat` (an older copy of the arrays library's): its meaning
  -- depends on these definitions, so it keeps them rather than `Words` and `Array.lean`.
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

  -- The arm `n := Z` is checked before the arm `n := S(m)`; the conjuncts of `⟨…⟩` there
  -- are typed through `r`'s value, whose type must not be the `Z` arm's `Slice(0)`.
  def Leak (n : Nat) (k : Nat) (l : Slice(k)) (r : Slice(Sub(n, k))) (a : Nat) (hl : AllGe(k, l, a))
      (ih : Π(m : Nat) (k' : Nat) (t : Slice(k')) (r2 : Slice(Sub(m, k'))). AllGe(m, JoinS(m, k', t, r2), a)) :
      AllGe(n, JoinS(n, k, l, r), a) := (
    match k {
      Z => ih(n, 0, l, r),
      S k' => match n {
        Z => ih(Z, S(k'), l, r),
        S m => match l {
          MkSlice(c) => match c {
            MkC(y, t) => ⟨AndL(Le(a, y), AllGe(k', t, a), hl), ih(m, k', t, r)⟩,
          },
        },
      },
    }
  )
}


ochr ArmLocalBoom {
  inductive Emp := E(e : Emp)
  def AbsurdEq (x : Emp) (A : Type) (a : A) (b : A) : Eq(A, a, b) by x := match x { E(e) => AbsurdEq(e, A, a, b) }
  -- Its own option type and slices: a minimal witness, using no other block.
  inductive Opt (R : Type) := N0 | S0(x : R)
  inductive SliceOf (R : Type) := MkSlice(c : R)
  def Cells (n : Nat) : Type by n := match n { Z => Opt(Emp), S m => Opt(Nat) }
  def Slice (n : Nat) : Type := SliceOf(Cells(n))
  -- every `Slice(0)` is the empty one
  def EmptyEq (s : Slice(0)) : Eq(Slice(0), s, MkSlice(N0[Emp])) := (
    match s { MkSlice(c) => match c { N0 => refl, S0(x) => AbsurdEq(x, Slice(0), MkSlice(S0[Emp](x)), MkSlice(N0[Emp])) } })
  -- `r : Slice(S(m))` in the second arm, where `Eq(Slice(0), r, …)` is ill-typed
  reject def T6 (n : Nat) (r : Slice(n)) : Prop := (
    match n { Z => ⊤, S m => (λ(u : Nat) : Prop => Eq(Slice(0), r, MkSlice(N0[Emp])))(0) })
  reject def T7 (n : Nat) (r : Slice(n)) : T6(n, r) := (
    match n { Z => refl, S m => (λ(u : Nat) : Eq(Slice(0), r, MkSlice(N0[Emp])) => EmptyEq(clone(r)))(0) })
  reject def BoomLeak : False := T7(1, MkSlice(S0[Nat](9)))
}


/-! Generalisation records belong to their arm too (reviewer-6's A1, a closed proof of `False`
in the default checker until then). In the arm `n := Z`, `match x` generalises the stuck
call `⌈g(())⌉` to a fresh `σ` of type `T(0) = Box(Unit)`. The arm `n := S m` derives the same
program text `⌈g(())⌉`, whose type there is `T(S m) = Box(Bool)`. With the record global, it
was mapped to that `σ`, typed `Box(Unit)`: `Cmp2(y)` then compared `MkBox(true)` with
`MkBox(false)` at `Unit`, which η made true, and `L2` returned `False`. Records survive a
private copy (D37), which stays within one world, but sibling arms are different worlds, so
a record an arm makes is dropped with the arm (`exitWorld`). `FLie` is the fuzzer's shape
(fuzz-port, `--a1`): the statement's arm does not call `g`, the proof's arm makes the record.
(Since η at `Unit` is a property of values, D59 refined, the comparison is no longer true at a
stale type either: `true` and `false` are distinct constructors whatever the type says.) -/

ochr ArmRecords uses Bools, Boxes {
  def T (n : Nat) : Type := match n { Z => Box(Unit), S _ => Box(Bool) }
  def Cmp2 (b : Box(Bool)) : Prop := (let c = clone(b); Id(Unit, c := MkBox(true), c := MkBox(false)))
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
      Id(Prop, (match n0 { Z => ⊤, S p7 => let y6 = g1(()); Cmp2(y6) }), ⊤) := (
    match n0 { Z => (let x5 = g1(()); match x5 { MkBox(v) => refl }), S _ => refl })
  reject def FBoom : False := (
    let h = FLie(1, λ(u : Unit) : T(1) => MkBox(true));
    J(Prop, ⊤, False, λ(P : Prop) : Prop => P, symm(h), refl))
}



/-! η-refinements belong to their arm too (EtaBoom, `docs/reviews/2026-11-02-plan18-simulation.md`,
a closed proof of `False` in the default checker until then). Re-rooting a moved place through
an abstract value `σ` of a one-constructor type η-refines it, `σ := MkDP(σx, σy, σz)`, and the
record is reused so that every private copy names `σ`'s fields alike (D68). The fields' types
are read at `σ`'s type in the world that made the record. In the arm `n := Z` that is
`DP(Z)`, so `σy : G(Z, σx) = Void`; with the record kept across arms, the arm `n := S m`
reused it, `d.y` held an unknown of type `Void` where the telescope gives `Nat`, the
dependent-field rules typed the open field by its content, and `match y {}` proved `False`.
The constructor of an η-refinement is the same in every world, but its field unknowns and
their types are the world's, so a record an arm makes is dropped with the arm (`exitWorld`),
like a generalisation record (`ArmRecords`). `NoReuse` is the referee's twin (no record to
reuse); `UseY` is the same shape used as data, which the stale `Void` rejected; `OnlyZ` makes
the `Z` arm's ex falso, which is legitimate there. The leak is not about dependent fields:
`DQ`'s one constructor is not dependent, but its field's type `G1(n)` mentions the value
parameter `n`, which the arm refines. A field place is typed by the telescope at `d`'s type, which is
right, but a closure types what it captures through its value, so `CapY` saw the stale
`Void` (`Boom5` was a second closed proof of `False`), and its true twin `CapUseY` was
rejected. -/

ochr ArmEta {
  inductive Void : Type
  inductive Bool := false | true
  def G (n : Nat) (b : Bool) : Type := ( match n { Z => Void, S(m) => Nat } )
  inductive DP (n : Nat) := MkDP(x : Bool, y : G(n, x), z : Nat)
  def Eat (k : Nat) : Unit := ()
  def H (n : Nat) : Prop := match n { Z => False, S _ => ⊤ }
  reject def Bad1 (n : Nat) (d : DP(n)) : False := (
    match n {
      Z => ( let u : Unit = match d { MkDP(x, y, z) => Eat(z) };
             match d { MkDP(x, y, z) => match y {} } ),
      S(m) => ( let u : Unit = match d { MkDP(x, y, z) => Eat(z) };
                match d { MkDP(x, y, z) => match y {} } ),
    }
  )
  reject def Boom : False := Bad1(S(Z), MkDP(true, Z, Z))
  -- the twin: the arm `n := S m` makes no record of its own to reuse
  reject def NoReuse (n : Nat) (d : DP(n)) : False := (
    match n {
      Z => ( let u : Unit = match d { MkDP(x, y, z) => Eat(z) };
             match d { MkDP(x, y, z) => match y {} } ),
      S(m) => match d { MkDP(x, y, z) => match y {} },
    }
  )
  -- the same shape, true: in the arm `n := S m` the field `y` is a `Nat`
  def UseY (n : Nat) (d : DP(n)) : Unit := (
    match n {
      Z => ( let u : Unit = match d { MkDP(x, y, z) => Eat(z) }; () ),
      S(m) => ( let u : Unit = match d { MkDP(x, y, z) => Eat(z) };
                match d { MkDP(x, y, z) => Eat(y) } ),
    }
  )
  -- and in the arm `n := Z` the field `y` is a `Void`, so ex falso is sound there
  def OnlyZ (n : Nat) (d : DP(n)) : H(n) := (
    match n {
      Z => ( let u : Unit = match d { MkDP(x, y, z) => Eat(z) };
             match d { MkDP(x, y, z) => match y {} } ),
      S(m) => ( let u : Unit = match d { MkDP(x, y, z) => Eat(z) }; refl ),
    }
  )
  -- not dependent: `y`'s type mentions only the value parameter
  def G1 (n : Nat) : Type := ( match n { Z => Void, S(m) => Nat } )
  inductive DQ (n : Nat) := MkDQ(y : G1(n), z : Nat)
  reject def CapY (n : Nat) (d : DQ(n)) : False := (
    match n {
      Z => ( let u : Unit = match d { MkDQ(y, z) => Eat(z) };
             match d { MkDQ(y, z) => match y {} } ),
      S(m) => ( let u : Unit = match d { MkDQ(y, z) => Eat(z) };
                let w = match d { MkDQ(y, z) => y };
                (λ(u : Unit) : False => match w {})(()) ),
    }
  )
  reject def Boom5 : False := CapY(S(Z), MkDQ(Z, Z))
  def CapUseY (n : Nat) (d : DQ(n)) : Unit := (
    match n {
      Z => ( let u : Unit = match d { MkDQ(y, z) => Eat(z) }; () ),
      S(m) => ( let u : Unit = match d { MkDQ(y, z) => Eat(z) };
                let w = match d { MkDQ(y, z) => y };
                (λ(u : Unit) : Unit => Eat(clone(w)))(()) ),
    }
  )
}

#guard (run "ArmEta" ArmEta).rejectedWith [
  ("Bad1", "[Match] on d.y, whose type Nat is not an inductive type"),
  ("Boom", "unknown constant Bad1"),
  ("NoReuse", "[Match] on d.y, whose type Nat is not an inductive type"),
  ("CapY", "[Match] on κ, whose type Nat is not an inductive type"),
  ("Boom5", "unknown constant CapY")]
