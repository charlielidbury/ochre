import Ochr.Examples.Bool
import Ochr.Examples.Nat
import Ochr.Examples.Fixtures
import Ochr.Runtime

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

ochr Equality uses Bools, Nats {
  -- The footprint is read from the syntax, so an unrelated `let` does not change what is
  -- compared, and the proof is the same as `AddMZero`'s.
  def AddMZeroLet (x : &Nat) : Id(Unit, let n = 0; AddM(&*x, n), ()) by x := (
    match *x {
      Z => refl,
      S p => AddMZeroLet(&p),
    }
  )

  -- The paper's first `Id` (§2): at a definition taking `x : &Nat`, `Id(Unit, AddM(&*x, 0), ())`
  -- is `Eq(Unit, ⌈…⌉, ()) ∧ Eq(Nat, N(σ), σ)`. The stuck call returns its sealed program `⌈…⌉`,
  -- which is also what `let c = *x; AddM(&c, 0)` returns, and leaves `N(σ)` in `x`'s owner,
  -- which is also what `Add(*x, 0)` computes. An equation at `Unit` is `⊤` (η for `Unit`,
  -- D59), whatever its sides, so the whole is the single equation `Eq(Nat, N(σ), σ)`, in both
  -- directions.
  def IdIsConjSealed (x : &Nat) (h : Id(Unit, AddM(&*x, 0), ())) : Eq(Unit, let c = *x; AddM(&c, 0), ()) ∧ Eq(Nat, Add(*x, 0), *x) := h
  def IdIsConj (x : &Nat) (h : Id(Unit, AddM(&*x, 0), ())) : Eq(Unit, (), ()) ∧ Eq(Nat, Add(*x, 0), *x) := h
  def IdIsEq (x : &Nat) (h : Id(Unit, AddM(&*x, 0), ())) : Eq(Nat, Add(*x, 0), *x) := h
  def EqIsId (x : &Nat) (h : Eq(Nat, Add(*x, 0), *x)) : Id(Unit, AddM(&*x, 0), ()) := h
  reject def IdIsWrong (x : &Nat) (h : Id(Unit, AddM(&*x, 0), ())) : Eq(Nat, Add(*x, 1), *x) := h

  -- Owned locals are observed too: `x := 6` and `()` differ in what they leave in `x` ...
  reject def OwnedLocal (x : Nat) : Id(Unit, x := 6, ()) := refl

  -- ... and assuming they agree gives exactly the equation between the two contents.
  def OwnedLocalNeq (x : Nat) (h : Id(Unit, x := 6, ())) : Eq(Nat, 6, x) := h

  -- `0 = 1` has no proof.
  reject def ZeroIsOne : Id(Nat, 0, 1) := refl

  -- Adding 0 and adding 1 in place differ, so no induction proves them equal ...
  reject def Add01 (x : Nat) : Id(Unit, AddM(&x, 0), AddM(&x, 1)) by x := (
    match x {
      Z => refl,
      S p => Add01(p),
    }
  )

  -- ... and their difference is provable by the same induction. The borrow of `p` inside
  -- `*x` puts the `S` back around both sides, so it does not need injectivity (see `Inj`).
  def NotAdd01 (x : &Nat) (h : Id(Unit, AddM(x, 0), AddM(x, 1))) : False by x := (
    match *x {
      Z => h,
      S p => NotAdd01(&p, h),
    }
  )

  -- Writing 0 and writing 1 leave different contents, so the `Id` is `False`: it can be
  -- eliminated by `match e {}` or used as a proof of `False` directly.
  def WriteNeq (x : &Nat) (e : Id(Unit, *x := 0, *x := 1)) : Nat := match e {}
  def WriteDisj (x : &Nat) (h : Id(Unit, *x := 0, *x := 1)) : False := h
  reject def WriteSame (x : &Nat) (h : Id(Unit, *x := 0, *x := 0)) : False := h

  -- Distinct constructors are disjoint: `Eq(Nat, Z, S(Z))` computes to `False`, in both
  -- directions and at any inductive type (D47).
  def NoConf (h : Eq(Nat, Z, S(Z))) : False := h
  def NoConfS (n : Nat) (h : Eq(Nat, Z, S(n))) : False := h
  def NoConfMatch (n : Nat) (h : Eq(Nat, S(n), Z)) : Nat := match h {}
  def NoConfBack (h : False) : Eq(Nat, 0, 1) := h
  def BoolDisj (h : Eq(Bool, false, true)) : False := h

  -- Equal constructors are taken apart (injectivity, D52): `Eq(Nat, S(a), S(b))` computes to
  -- `Eq(Nat, a, b)` ...
  def Inj (a : Nat) (b : Nat) (h : Eq(Nat, S(a), S(b))) : Eq(Nat, a, b) := h

  -- ... and not to anything else.
  reject def InjWrong (a : Nat) (b : Nat) (h : Eq(Nat, S(a), S(b))) : Eq(Nat, a, 0) := h

  -- On pairs: an equation between two pairs is the conjunction of the equations between
  -- their components ...
  def PairInj (a : Nat) (b : Nat) (h : Eq(Nat × Nat, (a, b), (1, 2))) : Eq(Nat, a, 1) ∧ Eq(Nat, b, 2) := h

  -- ... and not the other way round.
  reject def PairInjWrong (a : Nat) (b : Nat) (h : Eq(Nat × Nat, (a, b), (1, 2))) : Eq(Nat, a, 2) ∧ Eq(Nat, b, 1) := h

  -- `J` names both endpoints, because `Eq(A, a, a)` computes to `True` and would forget them.
  def Transport (a : Nat) (b : Nat) (h : Eq(Nat, a, b)) (t : Id(Nat, Add(a, 0), a)) : Id(Nat, Add(b, 0), b) := (
    J(Nat, a, b, λ(z : Nat) : Prop => Id(Nat, Add(z, 0), z), h, t)
  )

  -- The transported proof must be about the first endpoint.
  reject def TransportBack (a : Nat) (b : Nat) (h : Eq(Nat, a, b)) (t : Id(Nat, Add(b, 0), b)) :
      Id(Nat, Add(a, 0), a) := (
    J(Nat, a, b, λ(z : Nat) : Prop => Id(Nat, Add(z, 0), z), h, t)
  )

  -- An equation a refinement made impossible computes to `False`, and so does its symmetric
  -- one: `symm` of a proof of `False` is a proof of `False` (fuzz-port R7: here `n1 = S(p)`
  -- and `n0 = 0` make both `False`, and the branch is unreachable).
  def SymmUnreachable (n0 : Nat) (n1 : Nat) (h2 : Eq(Nat, n0, n1)) : Nat := (
    match n0 {
      Z => match n1 {
        Z => 0,
        S p => J(Nat, n1, n0, λ(z : Nat) : Type => Nat, symm(h2), p),
      },
      S _ => 0,
    }
  )

  -- `J` computes only when its endpoints are convertible (D56, Lean's rule for `Eq.rec`) ...
  def CastRefl (n : Nat) : Id(Nat, J(Nat, n, n, λ(z : Nat) : Type => Nat, refl, 5), 5) := refl

  -- ... and is otherwise a stuck cast. Under the false hypotheses that `Nat → Nat` and
  -- `(Nat → Nat) → Nat` are equal, `Om` applies a stuck cast instead of running forever, and
  -- `CastMatch` splits on the stuck cast of `5` instead of matching `5` against `Bool`'s
  -- constructors. Returning `t` whatever the endpoints is equality
  -- reflection: checking `Om` would not terminate (the checker's depth bound stops it), and
  -- `CastMatch` would meet a number where a `Bool` is due.
  def C1 (h : Eq(Type, Nat → Nat, (Nat → Nat) → Nat)) (x : Nat → Nat) : ((Nat → Nat) → Nat) := (
    J(Type, Nat → Nat, (Nat → Nat) → Nat, λ(X : Type) : Type => X, h, x)
  )

  def C2 (h : Eq(Type, (Nat → Nat) → Nat, Nat → Nat)) (f : (Nat → Nat) → Nat) : (Nat → Nat) := (
    J(Type, (Nat → Nat) → Nat, Nat → Nat, λ(X : Type) : Type => X, h, f)
  )

  def Om (h1 : Eq(Type, Nat → Nat, (Nat → Nat) → Nat)) (h2 : Eq(Type, (Nat → Nat) → Nat, Nat → Nat)) : Nat := (
    let f = (λ(x : Nat → Nat) : Nat => (C1(h1, clone(x)))(x));
    f(C2(h2, f))
  )

  def CastMatch (h : Eq(Type, Nat, Bool)) : Nat := (
    let b = J(Type, Nat, Bool, λ(X : Type) : Type => X, h, 5);
    match b {
      false => 0,
      true => 1,
    }
  )

  -- [J-stuck]: with endpoints that are not convertible, `J` does not run `t` at all. The run is
  -- stuck, and the call containing it closes off (D63, rule-audit item 5); typing checks `t`
  -- on a private copy and closes the `J` off as a stuck block. So at `JT`'s generic call `c`
  -- holds a sealed program, and `refl` does not prove the equation. The earlier checker ran
  -- `t` first and returned a stuck cast of its value, so `c` was already 5.
  def JF (a : Nat) (b : Nat) (h : Eq(Nat, a, b)) (x : &Nat) : Nat := J(Nat, a, b, λ(z : Nat) : Type => Nat, h, (*x := 5; 0))
  reject def JT (a : Nat) (b : Nat) (h : Eq(Nat, a, b)) : Id(Nat, let c = 0; JF(clone(a), clone(b), h, &c); c, 5) := refl
  -- twin of JT: the endpoints are convertible (both `0`, proved by `refl`), so `J` runs `t` and `c` is 5
  def JTOk : Id(Nat, let c = 0; JF(0, 0, refl, &c); c, 5) := refl

  -- `J`'s motive is erased: it runs on its own private copy, so a write to an outer place
  -- there lands on the copy and is discarded (D68; D41 made it an error, [Erase-err], until
  -- D68 deleted confinement). The earlier checker ran it in place, with copying reads.
  def JMotiveConf (x : Nat) : Nat := J(Nat, 0, 0, (x := 5; λ(z : Nat) : Type => Nat), refl, 7)

  -- `Id` computes the same way wherever it is evaluated ([Obs] is stated with the typing
  -- judgement): built in a function's body, run by the machine, its side's stuck match is
  -- closed off as a block, as when the same `Id` is formed directly (D63, rule-audit item 9).
  -- The earlier checker observed untyped there, so `FId(n, x)` was the stuck ⌈FId(σ0, σ1)⌉.
  def FId (n : Nat) (x : Nat) : Prop := Id(Nat, (match n { Z => x, S _ => x }), x)
  def Conv1 (n : Nat) (x : Nat) (h : Id(Nat, (match n { Z => x, S _ => x }), x)) : FId(n, x) := h

  -- Each side of `Eq` runs on its own private copy of the state, by the ordinary rules: a
  -- write in a side is seen by the rest of that side, and by nothing else; the other side
  -- starts from the state as it was. So mutating `*x` inside a side
  -- states what the mutated value is ...
  def EffInSide (x : &Nat) : Eq(Nat, *x := S(*x); *x, S(*x)) := refl
  def AddMInSide (x : &Nat) : Eq(Nat, AddM(&*x, 1); *x, Add(*x, 1)) := refl
  -- ... the right side does not see the left side's write ...
  def SideOld (x : &Nat) : Eq(Nat, let c = *x; *x := 7; c, *x) := refl
  -- ... so this is not provable: at `*x = 5` the left side is 1 and the right side is 6.
  reject def SideShared (x : &Nat) : Eq(Nat, *x := 0; 1, S(*x)) := refl
  -- twin of SideShared: the right side no longer reads `*x`, so it cannot disagree with the left
  def SideSharedOk (x : &Nat) : Eq(Nat, *x := 0; 1, S(Z)) := refl

  -- A move is definite (D84): a match leaves moved, on every path, what any of its arms moves
  -- (its join drops it in the others). So both sides below leave `x` moved at every `n`, at an
  -- instance as at the generic call, where a stuck block takes `x` by move, and `⊥ = ⊥` is `⊤`.
  -- (Until D84 a match on a known constructor ran only its arm, so at `n = 0` only the left side
  -- moved `x`, and D68 kept the equation stuck; fuzz case 11014.)
  def MovedBothSides (n : Nat) (x : Nat) :
      Id(Unit, (let r = &x; match n { Z => (let y = x; ()), S _ => () }), (let r = &x; match n { Z => (), S _ => (let y = x; ()) })) := refl
  -- twin of MovedBothSides: neither side moves `x` (the move is replaced by a clone), so `x` keeps its content
  def MovedBothSidesOk (n : Nat) (x : Nat) :
      Id(Unit, (let r = &x; match n { Z => (let y = clone(x); ()), S _ => () }), (let r = &x; match n { Z => (), S _ => (let y = clone(x); ()) })) := refl
}

/-! ## Moved places are definite: D83's tests under D84

D83 made a value holding `⊥` convertible with nothing, because `⊥` meant "lost track of": a
stuck block took a place by move if any arm moved it, while at an instance only the taken arm
ran. D84 drops at a match's join what any arm moves, so `⊥` means "moved on every path", on the
generic call and at every instance alike: it is a value of its own, `⊥ = ⊥` is `⊤` and `⊥ = v`
is `False` for every other `v`, and [Conv-bot] is retired. And an `Id` is well formed only when
its sides leave the same type-state ([Id-typestate]): here, the same places moved. Each side
below that matches on `n` moves `x` at every `n` (its arm `Z` moves it). -/

ochr BotConv uses Nats {
  -- True now: both sides of both `Id`s move `x` on every path, so both types are `⊤`.
  def Same (n : Nat) (x : Nat)
      (h : Id(Unit, match n { Z => (let y = x; ()), S _ => (x := 5; ()) }, match n { Z => (let y = x; ()), S _ => (x := 5; ()) }))
    : Id(Unit, match n { Z => (let y = x; ()), S _ => (x := 5; ()) }, match n { Z => (let y = x; ()), S _ => (x := 6; ()) }) := h
  -- ... and at `n = 1` its type is `⊤` too (arm `S` writes `x`, and the join drops it), not `False`
  reject def Boom : False := Same(S(Z), Z, refl)
  -- ill-formed now: one side moves `x`, the other writes it ([Id-typestate])
  reject def SelfBot (n : Nat) (x : Nat)
      (h : Id(Unit, match n { Z => (let y = x; ()), S _ => (x := 5; ()) }, (x := 5; ())))
    : Id(Unit, match n { Z => (let y = x; ()), S _ => (x := 5; ()) }, (x := 5; ())) := h
  -- twin of SelfBot: arm `Z` clones `x`, so neither side moves it, and the block takes it by `&`
  -- (arm `S` writes it): the stuck equation `Eq(Nat, ⌈…⌉, 5)` is convertible with itself
  def SelfKept (n : Nat) (x : Nat)
      (h : Id(Unit, match n { Z => (let y = clone(x); ()), S _ => (x := 5; ()) }, (x := 5; ())))
    : Id(Unit, match n { Z => (let y = clone(x); ()), S _ => (x := 5; ()) }, (x := 5; ())) := h

  -- ill-formed now, for the same reason: `h`'s right side moves `x`, its left side does not
  reject def TrBot (n : Nat) (x : Nat)
      (h : Id(Unit, (x := 5; ()), match n { Z => (let y = x; ()), S _ => (x := 5; ()) }))
      (k : Id(Unit, match n { Z => (let y = x; ()), S _ => (x := 6; ()) }, (x := 6; ())))
    : Id(Unit, (x := 5; ()), (x := 6; ())) := trans(h, k)
  reject def TrBotBoom : False := TrBot(S(Z), Z, refl, refl)
  -- twin of TrBot: with clones the middle points are the same sealed program, and compose
  def TrKept (n : Nat) (x : Nat)
      (h : Id(Unit, (x := 5; ()), match n { Z => (let y = clone(x); ()), S _ => (x := 5; ()) }))
      (k : Id(Unit, match n { Z => (let y = clone(x); ()), S _ => (x := 5; ()) }, (x := 5; ())))
    : Id(Unit, (x := 5; ()), (x := 5; ())) := trans(h, k)

  -- ill-formed now: `h`'s left side moves `x`
  reject def RwBot (n : Nat) (x : Nat)
      (h : Id(Unit, match n { Z => (let y = x; ()), S _ => (x := 5; ()) }, (x := 5; ())))
    : Id(Unit, match n { Z => (let y = x; ()), S _ => (x := 6; ()) }, (x := 5; ())) := rewrite ← h in refl
  reject def RwBotBoom : False := RwBot(S(Z), Z, refl)
  -- twin of RwBot: with a clone, `h : Eq(Nat, ⌈…⌉, 5)` rewrites the goal's `⌈…⌉`, the same
  -- sealed program, to 5
  def RwKept (n : Nat) (x : Nat)
      (h : Id(Unit, match n { Z => (let y = clone(x); ()), S _ => (x := 5; ()) }, (x := 5; ())))
    : Id(Unit, match n { Z => (let y = clone(x); ()), S _ => (x := 5; ()) }, (x := 5; ())) := rewrite ← h in refl
}

#guard (run "BotConv" BotConv).rejectedWith [
  ("Boom", "the body of Boom has type ⊤, but the goal is False"),
  ("SelfBot", "[Id-typestate] the left side of Id moves x, the right side does not"),
  ("TrBot", "[Id-typestate] the right side of Id moves x, the left side does not"),
  ("TrBotBoom", "unknown constant TrBot"),
  ("RwBot", "[Id-typestate] the left side of Id moves x, the right side does not"),
  ("RwBotBoom", "unknown constant RwBot")]

/-! ## Moves are definite; `Id` compares computations that leave the same type-state (D84)

A read of a place whose declared type is not a copy type moves it, and a match leaves moved,
on every path, what any of its arms moves: the arms that do not move it drop it at their end
([Join], the lattice join of the arms' end states, moved ⊔ whole = moved). The places are read
from the match's syntax and declared types, so the generic call (a stuck block takes them by
move) and every instance (one arm runs, the join drops the rest) agree, each at the grain the
declared types give: a field is named only through a value whose declared type is an inductive
with one constructor, not one computed by a match.

`Id(A, t, u)` is well formed only where `t` and `u` leave the same type-state
([Id-typestate]): the same places moved, the same borrows consumed, re-pointed and left moved
through. So a context that accepts one can accept the other as far as moves and borrows go. A
side may not end a borrow that a binding or a value in flight outside it holds. A borrow both
sides re-point is observed by where it points ([Obs-ref]). -/

ochr Moves84 uses Nats {
  def F (n : Nat) : Unit := ()
  -- `F(x)` consumes `x`, `F(y)` consumes `y`: not substitutable for each other
  reject def FxFy (x : Nat) (y : Nat) : Id(Unit, F(x), F(y)) := refl
  -- twin of FxFy: both sides consume `x`
  def FxFx (x : Nat) : Id(Unit, F(x), (let z = x; ())) := refl
  -- the same with the places bound in the statement, around the `Id` ...
  reject def FxFyLet : (let x = 5; let y = 5; Id(Unit, F(x), F(y))) := refl
  -- ... and inside each side, where each side's `x` and `y` die with it: nothing can tell them apart
  def FxFyLocal : Id(Unit, (let x = 5; let y = 5; F(x)), (let x = 5; let y = 5; F(y))) := refl

  -- A borrow passed whole is consumed; a reborrow is not
  reject def Consumes (x : &Nat) : Id(Unit, AddM(x, 0), ()) := AddMZero(x)
  def Reborrows (x : &Nat) : Id(Unit, AddM(&*x, 0), ()) := AddMZero(x)
  -- a side that moves out through a borrow and does not refill it leaves it open
  reject def LeftOpen (y : &Nat) : Id(Unit, (let a = *y; ()), ()) := refl
  def LeftOpenBoth (y : &Nat) : Id(Unit, (let a = *y; ()), (let b = *y; ())) := refl
  -- re-pointing a borrow binding: on one side only, ill-formed; on both, observed by where it
  -- points ([Obs-ref]), so different targets are told apart and the same target is not
  reject def RePointOne (x : Nat) (y : &Nat) : Id(Unit, (y := &x; ()), ()) := refl
  reject def RePoint (x : Nat) (z : Nat) (y : &Nat) : Id(Unit, (y := &x; ()), (y := &z; ())) := refl
  def SameTarget (x : Nat) (y : &Nat) : Id(Unit, (y := &x; ()), (y := &x; ())) := refl
  reject def SwapB (y1 : &Nat) (y2 : &Nat) : Id(Unit, (let t = y1; y1 := y2; y2 := t), ()) := refl
  -- a side may not end a borrow a binding outside it holds: reading `x` ends `y`
  reject def KillRead (x : Nat) : Unit := (let y = &x; let h : Id(Unit, (let a = clone(x); ()), ()) = refl; *y := 5)
  def KillReadAfter (x : Nat) : Unit := (let h : Id(Unit, (let a = clone(x); ()), ()) = refl; let y = &x; *y := 5)
  -- ... nor one a value in flight holds: `&x`, `Put`'s first argument, is evaluated before the `Id`
  def Put (r : &Nat) (u : Unit) : Unit := (*r := 5; ())
  reject def KillTemp (x : Nat) : Unit := Put(&x, (let h : Id(Unit, (let a = clone(x); ()), ()) = refl; ()))
  def KillTempBefore (x : Nat) : Unit := (let h : Id(Unit, (let a = clone(x); ()), ()) = refl; Put(&x, ()))
  -- a constructor's parameters are types, evaluated on a copy: `MkNBox[n](0)` does not move `n`,
  -- so it and a side that moves `n` are not substitutable (D84 amendment)
  inductive NBox (k : Nat) := MkNBox(v : Nat)
  reject def CP (n : Nat) : Id(Unit, (let b = MkNBox[n](0); ()), (let z = n; ())) := refl
  -- twin of CP: both sides move `n`
  def CPok (n : Nat) : Id(Unit, (let b = MkNBox[clone(n)](0); let z = n; ()), (let z = n; ())) := refl
  def CL (n : Nat) : Nat := ((let b = MkNBox[n](0); ()); n)
  reject def CR (n : Nat) : Nat := ((let z = n; ()); n)
  -- with `n` in the footprint: was well formed and `False`, now ill-formed
  reject def C1 (n : Nat) : Id(Unit, (let r = &n; let b = MkNBox[n](0); ()), (let r = &n; let z = n; ())) := refl

  -- The join in a direct run: at `n = 1` arm `S` runs, and the join drops `x`, which arm `Z`
  -- moves, so the left side leaves `x` moved there as at the generic call
  def MovesAt (n : Nat) (x : Nat) : Prop := Id(Unit, (let r = &x; match n { Z => (let y = x; ()), S _ => () }), (let r = &x; let y = x; ()))
  def AtOneTrue (x : Nat) : MovesAt(S(Z), x) := refl
  def GenTrue (n : Nat) (x : Nat) : MovesAt(n, x) := refl

  -- The lattice join: `x` is moved before the match and refilled by one arm only, so it is
  -- moved after it on every path ...
  reject def RefillOne (x : Nat) : Nat := (let y = x; match Z { Z => (x := 5; ()), S _ => () }; x)
  -- ... and whole when every arm refills it
  def RefillBoth (x : Nat) : Nat := (let y = x; match Z { Z => (x := 5; ()), S _ => (x := 6; ()) }; x)

  -- The grain of a move, from declared types. `TF`'s arms agree on `Pr`, but its value is a
  -- stuck program at an unknown `k` (the generic call cannot name `x.a`) and `Pr` at an instance,
  -- so a move of `x.a` is a move of `x` at the join, on every path: `G` is well formed and true,
  -- and `Boom` (a closed proof of `False` on D84's viability prototype, which kept `x.a` at the
  -- instance) has type `⊤`. `&x` puts `x` in the footprint
  inductive Pr := MkPr(a : Nat, b : Nat)
  def TF (n : Nat) : Type := match n { Z => Pr, S _ => Pr }
  def G (k : Nat) (x : TF(k)) :
      Id(Unit, (let r = &x; match k { Z => match x { MkPr(a, b) => (let y = a; ()) }, S _ => () }), (let r = &x; let z = x; ())) := refl
  reject def Boom : False := G(Z, MkPr(1, 2))
  -- twin of G: declared `Pr`, `x`'s fields are named on every path, so only `x.a` is moved
  def GPr (k : Nat) (x : Pr) :
      Id(Unit, (let r = &x; match k { Z => match x { MkPr(a, b) => (let y = a; ()) }, S _ => () }), (let r = &x; let z = x.0; ())) := refl
  reject def GPrWhole (k : Nat) (x : Pr) :
      Id(Unit, (let r = &x; match k { Z => match x { MkPr(a, b) => (let y = a; ()) }, S _ => () }), (let r = &x; let z = x; ())) := refl
  -- a sealed value of a type with one constructor: generalised and refined, its fields named
  def MkPrF (n : Nat) : Pr := match n { Z => MkPr(0, 0), S _ => MkPr(1, 1) }
  def St (k : Nat) (n : Nat) : Prop :=
    (let x = MkPrF(n); Id(Unit, (let r = &x; match k { Z => match x { MkPr(a, b) => (let y = a; ()) }, S _ => () }), (let r = &x; let z = x.0; ())))
  def StTrue (k : Nat) (n : Nat) : St(k, n) := refl
  -- a field of an unknown constructor: the scrutinee is moved whole
  inductive Ch := L(u : Nat) | R(v : Nat)
  def Gc (k : Nat) (c : Ch) : Id(Unit, (let r = &c; match k { Z => match c { L(u) => (let y = u; ()), R(v) => () }, S _ => () }), (let r = &c; let z = c; ())) := refl
  -- a place lent at the join: its field is named as the arm that moves it names it (its borrow
  -- ended first), on the generic call as at an instance where the borrow is still live
  def LentField (k : Nat) (q : Pr) : Id(Unit, (let r = &q; match k { Z => (let y = q.0; ()), S _ => () }; ()), (let r = &q; let y = q.0; ())) := refl
  reject def LentWhole (k : Nat) (q : Pr) : Id(Unit, (let r = &q; match k { Z => (let y = q.0; ()), S _ => () }; ()), (let r = &q; let y = q; ())) := refl
  -- K1(g): a place one arm uses whole (here borrows) and another moves part of is moved whole
  def WholeUse (k : Nat) (q : Pr) : Id(Unit, (match k { Z => (let y = q.0; ()), S _ => (let r = &q; ()) }), (let r = &q; let y = q; ())) := refl
  reject def WholeUseField (k : Nat) (q : Pr) : Id(Unit, (match k { Z => (let y = q.0; ()), S _ => (let r = &q; ()) }), (let r = &q; let y = q.0; ())) := refl
}

#guard (run "Moves84" Moves84).rejectedWith [
  ("FxFy", "[Id-typestate] the left side of Id moves x, the right side does not"),
  ("FxFyLet", "[Id-typestate] the left side of Id moves x, the right side does not"),
  ("Consumes", "[Id-typestate] the left side of Id consumes the borrow x, the right side does not (pass a reborrow, &*x)"),
  ("LeftOpen", "[Id-typestate] the left side of Id leaves moved, through a borrow, *y, the right side does not"),
  ("RePointOne", "[Id-typestate] the left side of Id re-points the borrow y, the right side does not"),
  ("RePoint", "the body of RePoint has type ⊤, but the goal is Eq(Nat, σ3, σ0) ∧ Eq(Nat, σ1, σ3)"),
  ("SwapB", "[Id-typestate] the left side of Id re-points the borrow y1, the right side does not"),
  ("KillRead", "[Id-typestate] a side of Id ends the borrow y"),
  ("KillTemp", "[Id-typestate] a side of Id ends a borrow that a value in flight around the Id holds"),
  ("CP", "[Id-typestate] the right side of Id moves n, the left side does not"),
  ("CR", "[Read] n was moved out or its borrow ended (reading ⊥)"),
  ("C1", "[Id-typestate] the right side of Id moves n, the left side does not"),
  ("RefillOne", "[Read] x was moved out or its borrow ended (reading ⊥)"),
  ("Boom", "the body of Boom has type ⊤, but the goal is False"),
  ("GPrWhole", "[Id-typestate] the left side of Id moves x.a, the right side does not"),
  ("LentWhole", "[Id-typestate] the left side of Id moves q.0, the right side does not"),
  ("WholeUseField", "[Id-typestate] the left side of Id moves q, the right side does not")]

/-! ## `J` at runtime (D85)

The checker computes `J(A, a, b, P, h, t)` to `t` only when `a` and `b` are convertible ([J]),
and is otherwise stuck ([J-stuck]), in all its runs. Functions are convertible when their generic
calls are, so two functions with one graph and different code are not: `IdA` and `IdB` both mean
the identity on `Nat`, but at an unknown `σ` one returns `σ` and the other is stuck,
`⌈IdB(σ)⌉`. `CastFn` is accepted (its generic call closes the `J` off, [T-J-stuck]), and at the
closed call `CastFn(IdA, IdB, ⋆, MkFnBox(0))`, whose equation is true though not provable, the
checker's rule is stuck. The runtime (`Ochr/Runtime.lean`) runs the erased program, where `J` is
`t` unconditionally ([J-run]): its endpoints, motive and proof are statements, which the erased
program does not have. That is sound because the proof parameters' types are true, so the
endpoints mean the same (docs/29, Lean: `Model.Safety.castRT_safe`). The checker never runs in
runtime mode, so its verdicts here are those of [J] and [J-stuck]. -/

ochr RuntimeJ {
  inductive FnBox (k : Π(n : Nat). Nat) := MkFnBox(x : Nat)
  def IdA (n : Nat) : Nat := n
  def IdB (n : Nat) : Nat := match n { Z => Z, S m => S(m) }
  -- the two encodings are not convertible, so `refl` does not prove them equal
  reject def IdAB : Eq(Π(n : Nat). Nat, IdA, IdB) := refl
  -- a cast along an equation between functions
  def CastFn (f : Π(n : Nat). Nat) (g : Π(n : Nat). Nat) (h : Eq(Π(n : Nat). Nat, f, g)) (b : FnBox(f)) : FnBox(g) :=
    J(Π(n : Nat). Nat, f, g, λ(k : Π(n : Nat). Nat) : Type => FnBox(k), h, b)
  -- the checker runs `CastFn`'s body with its own rule: at endpoints that are not convertible
  -- the `J` is stuck and the call closes off, so `refl` does not prove the cast is `t` ...
  reject def CastFnRuns (h : Eq(Π(n : Nat). Nat, IdA, IdB)) :
      Id(FnBox(IdB), CastFn(IdA, IdB, h, MkFnBox[IdA](0)), MkFnBox[IdB](0)) := refl
  -- ... and at convertible endpoints it computes ([J])
  def CastFnSame : Id(FnBox(IdA), CastFn(IdA, IdA, refl, MkFnBox[IdA](0)), MkFnBox[IdA](0)) := refl
}

#guard (run "RuntimeJ" RuntimeJ).rejectedWith [
  ("IdAB", "the body of IdAB has type ⊤, but the goal is Eq(Π(n : Nat). Nat, IdA, IdB)"),
  ("CastFnRuns", "the body of CastFnRuns has type ⊤, but the goal is")]

namespace Ochr.RuntimeJTest
open Ochr Ochr.Surface

/-- `RuntimeJ`'s globals and inductive types, after checking it (its library first). -/
def sig : List GDef × List IndDecl :=
  let p := Ochr.Test.libOf {} 2000000 RuntimeJ ++ RuntimeJ.decls
  globalsAfter {} (p.filterMap fun d => (resolveProgram p d).toOption)

def box (f : String) : Value := .ind "FnBox" 0 ⟨"MkFnBox"⟩ [.gfn f] [.zero]

def result? : Outcome Value → Option Value
  | .ok v _ => some v
  | _ => none

/-- `CastFn(f, g, ⋆, MkFnBox(0))`, the proof erased, by the runtime (`runtime`) or by the
checker's own untyped run. -/
def castFn (runtime : Bool) (f g : String) : Outcome Value :=
  closedCall sig.1 sig.2 "CastFn" [.gfn f, .gfn g, .proof, box f] runtime

-- the runtime's entry point: `J` returns the transported term ([J-run])
#guard result? (runCall sig.1 sig.2 "CastFn" [.gfn "IdA", .gfn "IdB", .proof, box "IdA"]) == some (box "IdA")
-- twin: the same call under the checker's rule is stuck at `J` ([J-stuck]), so it closes off
-- ([Close]): its result is the sealed program of the call
#guard match result? (castFn false "IdA" "IdB") with
  | some (.sealed (.call (.val (.gfn "CastFn")) _ _)) => true
  | _ => false
-- at convertible endpoints the two rules agree ([J])
#guard result? (castFn false "IdA" "IdA") == some (box "IdA")
#guard result? (castFn true "IdA" "IdA") == some (box "IdA")

end Ochr.RuntimeJTest


/-! ## Rewriting

`rewrite h in t`, for `h : Eq A a b`, proves the goal `G` from `t : G'`, where `G'` is `G`
with every occurrence of `b`'s normal form replaced by `a` (the replacement a case split
uses to generalise a sealed program, D34, here local to the goal). `rewrite ← h in t`
replaces `a` by `b`. It is `J(A, a, b, λz. G[z/b], h, t)` with the motive read off the goal,
so it needs a known goal: tail position, a call's argument, or an annotated `let` (D60). -/

ochr Rewriting uses Nats {
  -- Symmetry and transitivity, and congruence without a motive.
  def RwSymm (x : Nat) (y : Nat) (h : Eq(Nat, x, y)) : Eq(Nat, y, x) := rewrite h in refl
  def RwTrans (x : Nat) (y : Nat) (z : Nat) (h1 : Eq(Nat, x, y)) (h2 : Eq(Nat, y, z)) : Eq(Nat, x, z) := rewrite h2 in h1
  def RwCong (x : Nat) (y : Nat) (h : Eq(Nat, x, y)) : Eq(Nat, Add(x, 2), Add(y, 2)) := rewrite h in refl
  def RwBack (x : Nat) (y : Nat) (h : Eq(Nat, x, y)) : Eq(Nat, Add(x, 2), Add(y, 2)) := rewrite ← h in refl

  -- A sealed program is rewritten like any value: `Add(x, 0)` becomes `x`.
  def RwSealed (x : Nat) (h : Eq(Nat, Add(x, 0), x)) : Eq(Nat, Add(Add(x, 0), 1), Add(x, 1)) := rewrite ← h in refl

  -- The goal comes from the context: a parameter's type, or an annotation. In tail
  -- position the rewritten goal is the path's goal, so the rest may split.
  def UseEq (a : Nat) (b : Nat) (p : Eq(Nat, a, b)) : Eq(Nat, a, b) := p
  def RwArg (x : Nat) (y : Nat) (h : Eq(Nat, x, y)) : Eq(Nat, y, x) := UseEq(y, x, rewrite h in refl)

  def RwLet (x : Nat) (y : Nat) (h : Eq(Nat, x, y)) : Eq(Nat, y, x) := (
    let p : Eq(Nat, y, x) = (rewrite h in refl);
    p
  )

  def RwSplit (x : Nat) (y : Nat) (h : Eq(Nat, x, y)) : Id(Nat, Add(clone(y), 0), clone(x)) := (
    rewrite h in match x {
      Z => refl,
      S p => AddMZero(&p),
    }
  )

  -- The direction matters: `h : x = y` rewrites `y` to `x`, and a goal about `x` needs
  -- `rewrite ← h`. A rewrite that finds nothing leaves the goal as it is ([T-Rewrite] has no
  -- premise that `b` occurs; rule-audit C22), so `k` does not prove it in `RwWrongDir`, and
  -- `RwNothing`'s `refl` does.
  def RwRightDir (x : Nat) (y : Nat) (h : Eq(Nat, x, y)) (k : Eq(Nat, y, 3)) : Eq(Nat, x, 3) := rewrite ← h in k
  reject def RwWrongDir (x : Nat) (y : Nat) (h : Eq(Nat, x, y)) (k : Eq(Nat, y, 3)) : Eq(Nat, x, 3) := rewrite h in k
  def RwNothing (a : Nat) (b : Nat) (h : Eq(Nat, a, b)) : ⊤ := rewrite h in refl

  -- Here the wrong direction finds `x` inside `Add(x, 0)` too, and leaves a goal `refl`
  -- does not prove.
  reject def RwSealedWrongDir (x : Nat) (h : Eq(Nat, Add(x, 0), x)) : Eq(Nat, Add(Add(x, 0), 1), Add(x, 1)) := rewrite h in refl

  -- The rewritten goal must be what `t` proves; `h` must be an equation; the goal must be
  -- known and a proposition; and an equation between equal sides rewrites nothing.
  reject def RwMismatch (x : Nat) (y : Nat) (h : Eq(Nat, x, y)) : Eq(Nat, Add(y, 1), 7) := rewrite h in refl
  reject def RwNotEq (P : Prop) (p : P) : P := rewrite p in p

  reject def RwNoGoal (x : Nat) (y : Nat) (h : Eq(Nat, x, y)) : Nat := (
    let p = (rewrite h in refl);
    0
  )

  reject def RwData (x : Nat) (y : Nat) (h : Eq(Nat, x, y)) : Nat := rewrite h in x
  reject def RwFalse (x : Nat) (h : Eq(Nat, x, x)) : Eq(Nat, x, S(x)) := rewrite h in refl
}


/-! ## All the owners of a returned borrow are observed

`Pick(n, &a, &b)` returns a borrow into `a` or `b`, depending on `n`. At an abstract `n`,
the hole for its contents is in both `a` and `b`, so an `Id` about writes through it
observes both: it is a conjunction with one equation per owner (D18). -/

ochr Owners uses Fixtures {
  def Probe (z : &Nat) (e : Id(Unit, *z := 0, *z := 1)) : Unit := ()

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
  --, `BadD18` would be accepted, and `ClosedD18` would be a closed
  -- proof of `0 = 1`.
  def Pick3 (x : &Nat) (y : &Nat) (s : Nat) : &Nat := (
    match s {
      Z => x,
      S _ => y,
    }
  )

  def K (z : &Nat) (e : Id(Unit, *z := 0, *z := 1)) : Eq(Nat, 0, 1) := e

  reject def BadD18 (s : Nat) (hs : Eq(Nat, s, 1)) (a : Nat) (b : Nat) : Eq(Nat, 0, 1) := (
    let r = Pick3(&a, &b, clone(s));
    let e : Id(Unit, *r := 0, *r := 1) = match s {
      Z => hs,
      S _ => refl,
    };
    K(r, e)
  )

  -- twin of BadD18: the two equations agree (`0 = 0`), so both owners hold by `refl` and the statement is true
  def K0 (z : &Nat) (e : Id(Unit, *z := 0, *z := 0)) : Eq(Nat, 0, 0) := e

  def BadD18Ok (s : Nat) (hs : Eq(Nat, s, 1)) (a : Nat) (b : Nat) : Eq(Nat, 0, 0) := (
    let r = Pick3(&a, &b, clone(s));
    let e : Id(Unit, *r := 0, *r := 0) = match s {
      Z => refl,
      S _ => refl,
    };
    K0(r, e)
  )

  reject def ClosedD18 : Eq(Nat, 0, 1) := BadD18(1, refl, 0, 0)
  -- twin of ClosedD18: calls the corrected `BadD18Ok`, proving the true `0 = 0`
  def ClosedD18Ok : Eq(Nat, 0, 0) := BadD18Ok(1, refl, 0, 0)

  -- The same without an annotated block: the hypothesis `h` recomputes, with local copies,
  -- exactly the sealed program that `a1` holds after `Pick`.
  def Neq (y : &Nat) (h : Id(Unit, *y := Z, *y := S(Z))) : Eq(Nat, Z, S(Z)) := h

  reject def GR (a1 : Nat) (a2 : Nat) (b : Nat)
      (h : Eq(Nat, let c1 = a1; let c2 = a2; let r = Pick(b, &c1, &c2); *r := Z; c1, let c1 = a1; let c2 = a2; let r = Pick(b, &c1, &c2); *r := S(Z); c1)) :
      Eq(Nat, Z, S(Z)) := (
    let r = Pick(b, &a1, &a2);
    Neq(r, h)
  )

  -- twin of GR: both sides write the same value (`Z`), so the conjunction is provable and the claim is `Z = Z`
  def Neq0 (y : &Nat) (h : Id(Unit, *y := Z, *y := Z)) : Eq(Nat, Z, Z) := h

  def GROk (a1 : Nat) (a2 : Nat) (b : Nat)
      (h : Eq(Nat, let c1 = a1; let c2 = a2; let r = Pick(b, &c1, &c2); *r := Z; c1, let c1 = a1; let c2 = a2; let r = Pick(b, &c1, &c2); *r := Z; c1)) :
      Eq(Nat, Z, Z) := (
    let r = Pick(b, &a1, &a2);
    Neq0(r, h)
  )

  reject def BadR : Eq(Nat, Z, S(Z)) := GR(0, 0, 1, refl)
  -- twin of BadR: calls the corrected `GROk`, proving `Z = Z`
  def BadROk : Eq(Nat, Z, Z) := GROk(0, 0, 1, refl)

  -- The curried form of the attack cannot even be stated: `G`'s result type is a Π-type
  -- that would capture the borrow `z`, and types capture values, never borrows (RULES §1).
  reject def G (z : &Nat) : (Π(e : Id(Unit, *z := 0, *z := 1)). False) := (
    λ(e : Id(Unit, *z := 0, *z := 1)) : False => e
  )

  reject def BadC2 (n : Nat) (a : Nat) (b : Nat) : Id(Nat, clone(n), 0) := (
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
      Id(Prop, (match n0 { Z => Id(Unit, *x2 := 1, n0 := clone(*x2)), S p2 => ⊤ }), (match n0 { Z => Eq(Nat, 1, *x2) ∧ Eq(Nat, 0, *x2), S p2 => ⊤ })) := (
    match n0 { Z => refl, S _ => refl }
  )
  reject def OrderSwapped (n0 : Nat) (x2 : &Nat) :
      Id(Prop, (match n0 { Z => Id(Unit, *x2 := 1, n0 := clone(*x2)), S p2 => ⊤ }), (match n0 { Z => Eq(Nat, 0, *x2) ∧ Eq(Nat, 1, *x2), S p2 => ⊤ })) := (
    match n0 { Z => refl, S _ => refl }
  )
  def OrderAtZero (x2 : &Nat) :
      Id(Prop, let n0 = 0; Id(Unit, *x2 := 1, n0 := clone(*x2)), Eq(Nat, 1, *x2) ∧ Eq(Nat, 0, *x2)) := refl
  -- Written places come first, then places only read through a borrow: closed off, `n1`
  -- becomes a borrow parameter, and its read in `(1, n1)` must not put it first.
  def IdOrderRead (x0 : &(Nat × Nat)) (n1 : Nat) :
      Id(Prop, (match n1 { Z => ⊤, S p => Id(Unit, *x0 := (1, clone(n1)), n1 := 0) }), (match n1 { Z => ⊤, S p => Eq(Nat × Nat, (1, n1), *x0) ∧ Eq(Nat, n1, 0) })) := (
    match n1 { Z => refl, S _ => refl }
  )

  -- An owner reached through a returned borrow, in a sealed program's re-run, where its cell
  -- is untyped and still lent out: it is typed by what the observation reads from it
  -- (fuzz-port's R1 residual, once rejected with "cannot infer the type of the value loan").
  def RetSub (x0 : &Nat) : &Nat := match *x0 { Z => &*x0, S p3 => &p3 }
  def IdThroughRet (x0 : &Nat) (x1 : &Nat) :
      Id(Prop, (match *x0 { Z => let a6 = RetSub(x1); Id(Unit, *x0 := clone(*a6), ()), S p7 => ⊤ }), (match *x0 { Z => let a6 = RetSub(x1); Id(Unit, *x0 := clone(*a6), ()), S p7 => ⊤ ∧ ⊤ })) := (
    match *x0 { Z => refl, S _ => refl }
  )
}


/-- The message rejecting `Owners.Use`: it states `Probe`'s parameter type. -/
def useMessage : String :=
  match ((run "Owners" Owners).rows.find? (·.name == "Use")).map (·.verdict) with
  | some (Ochr.Verdict.rejected m _) => m
  | _ => ""

-- all owners: the expected parameter type is a conjunction over a and b
#guard (useMessage.splitOn "∧").length == 2

#eval IO.println useMessage
