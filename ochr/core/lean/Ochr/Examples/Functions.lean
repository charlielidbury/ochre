import Ochr.Examples.Nat
import Ochr.Examples.Box
import Ochr.Examples.Fixtures

/-! # 9. Functions as values: opaque functions, closures and Π-types

A parameter may have a function type `Π(x : A). B` (or `A → B`). Nothing is known about
such a function but its type, so a call of it is closed off at once ([Call]); when it takes
a borrow, what it leaves there is a sealed program too. A `λ` is a function without `by`,
and `fix` a local recursive one.

Two function values are equal when their generic calls have the same observation: the
same result and the same effects on their borrow arguments (RULES P1, D30). Π-types are
compared the same way, by instantiating their binders with fresh values (D48 (3)). A
function that returns a borrow is observed by writing a fresh value through its result,
which shows where the result points (D38).

Defined in RULES P1, §1 (Π, `fix`, calls), §3 [Call] and §4. -/

open Ochr.Test

ochr Functions uses Nats, Boxes, Fixtures {
  -- ## Opaque functions
  -- `f` has no borrow argument, so it cannot write anything: its calls return `()` and
  -- `Twice(f)` does nothing.
  def Twice (f : Π(_ : Unit). Unit) : Unit := (
    f(());
    f(())
  )

  def TwiceNoop (f : Π(_ : Unit). Unit) : Id(Unit, Twice(f), ()) := refl

  -- With a borrow argument, `f` may write, and what it leaves is a sealed program. Moving
  -- `x` into the second call instead of reborrowing it makes no difference.
  def TwiceM (f : Π(_ : &Nat). Unit) (x : &Nat) : Unit := (
    f(&*x);
    f(&*x)
  )

  def TwiceMMove (f : Π(_ : &Nat). Unit) (x : &Nat) : Id(Unit, TwiceM(f, x), f(&*x); f(x)) := refl

  -- Instantiated with a function that adds zero, `TwiceM` does nothing, by induction ...
  def TwiceMZero (x : &Nat) : Id(Unit, TwiceM(λ(z : &Nat) : Unit => AddM(z, 0), x), ()) by x := (
    match *x {
      Z => refl,
      S p => TwiceMZero(&p),
    }
  )

  -- ... or by citing the lemma twice. A cited lemma runs on a private copy, so it leaves `*x`
  -- alone; `J` composes the two instances. `Add(s, 0)` closes off into the same sealed program
  -- as `AddM(&*x, 0)`.
  def TwiceMZero' (x : &Nat) : Id(Unit, TwiceM(λ(z : &Nat) : Unit => AddM(z, 0), x), ()) := (
    let s = clone(*x);
    let h1 = AddMZero(&*x);
    AddM(&*x, 0);
    let h2 = AddMZero(&*x);
    J(Nat, Add(s, 0), s, λ(z : Nat) : Prop => Id(Nat, Add(Add(s, 0), 0), z), h1, h2)
  )

  -- `A → B` is a Π-type with an unnamed parameter.
  def ApplyArrow (f : Nat → Nat) (n : Nat) : Nat := f(n)

  -- ## Comparing functions
  -- Functions are compared by what their generic calls do, not by their code.
  def Conv : Eq(Π(x : &Nat). Unit, (λ(x : &Nat) : Unit => ()), (λ(x : &Nat) : Unit => (let y = 0; ()))) := refl

  def ConvW :
      Eq(Π(x : &Nat). Unit, (λ(x : &Nat) : Unit => *x := S(*x)), (λ(x : &Nat) : Unit => (let y = S(*x); *x := y))) := (
    refl
  )

  -- A closure that captures a variable has a closed Π-type ...
  def Apply (f : Π(n : Nat). Nat) (n : Nat) : Nat := f(n)
  def Cap (m : Nat) : Nat := Apply(λ(n : Nat) : Nat => Add(n, clone(m)), 0)
  def CapEq (m : Nat) : Id(Nat, Apply(λ(n : Nat) : Nat => Add(n, m), 0), Add(0, m)) := refl

  -- A closure is stored in data only through a type parameter, as in `Box(Π(n : Nat). Nat)`
  -- (paper §4.3), and one returning a borrow too (the model's `Box(Π(y : &Nat). &Nat)`) ...
  def BoxFn : Box(Π(n : Nat). Nat) := MkBox(λ(n : Nat) : Nat => n)
  def UseBoxFn (b : Box(Π(n : Nat). Nat)) : Nat := match b { MkBox(f) => f(0) }
  def UseBoxFnIs : Id(Nat, UseBoxFn(MkBox(λ(n : Nat) : Nat => S(n))), 1) := refl
  def BoxBorrowFn (b : Box(Π(y : &Nat). &Nat)) (x : &Nat) : Unit := match b { MkBox(g) => (let r = g(x); *r := 0) }

  -- ... never as a field of its own (fields are first-order, D36).
  reject inductive FnBox := MkFnBox(f : Π(n : Nat). Nat)

  -- twin of FnBox: the field is first-order data (`Nat`) instead of a function
  inductive FnBoxOk := MkFnBoxOk(n : Nat)

  -- ... type abbreviations unfold under binders ...
  def Pow (X : Type) : Type₁ := Π(a : X). Prop
  def P1 : Pow(Nat) := λ(a : Nat) : Prop => ⊤
  def UseP (p : Pow(Nat)) : Prop := p(0)
  def P3 (u : Unit) : Prop := UseP(λ(a : Nat) : Prop => ⊤)

  -- ... and lemma statements are compared by what they compute to, under their binders.
  def ZeroAdd (n : Nat) : Id(Nat, Add(0, n), n) := refl
  def UseRefl (h : Π(n : Nat). Id(Nat, n, n)) : Unit := ()
  def PassZeroAdd (u : Unit) : Unit := UseRefl(ZeroAdd)

  -- Under a borrow binder, one generic place serves both sides.
  def UseA (h : Π(x : &Nat). Id(Unit, AddM(x, 0), ())) : Unit := ()
  def PassA (h : Π(y : &Nat). Id(Unit, let t = 0; AddM(y, t), ())) : Unit := UseA(h)

  -- Statements that differ at the generic arguments stay different.
  reject def PassStuck (h : Π(n : Nat). Id(Nat, Add(n, 0), n)) : Unit := UseRefl(h)
  reject def PassWrong (h : Π(n : Nat). Id(Nat, n, 0)) : Unit := UseRefl(h)
  def UseW (h : Π(x : &Nat). Id(Unit, *x := 0, *x := 0)) : Unit := ()
  reject def PassW (h : Π(x : &Nat). Id(Unit, *x := 0, *x := 1)) : Unit := UseW(h)
  reject def PassDom (f : Π(n : Unit). Nat) : Nat := Apply(f, 0)

  -- Two functions returning a borrow into different arguments ...
  def PickX (x : &Nat) (y : &Nat) : &Nat := x
  def PickY (x : &Nat) (y : &Nat) : &Nat := y

  -- ... and a property that tells them apart: writing through the result changes `*x`.
  def Q (h : Π(x : &Nat) (y : &Nat). &Nat) : Prop := (
    Π(x : &Nat) (y : &Nat). Id(Unit, let r = h(x, y); *r := S(Z), *x := S(Z))
  )

  def TX : Q(PickX) := (
    let h = PickX;
    λ(x : &Nat) (y : &Nat) : Id(Unit, let r = h(x, y); *r := S(Z), *x := S(Z)) => refl
  )

  -- ## What goes wrong without these rules
  -- Compared by their results only, `λx. ()` and `λx. (*x := 1)` would
  -- be equal, and `J` along that equation would prove `1 = 0` (D30).
  def P (h : Π(x : &Nat). Unit) : Prop := Id(Nat, let c = Z; h(&c); c, Z)

  reject def Boom3 : Eq(Nat, S(Z), Z) := (
    J(Π(x : &Nat). Unit, λ(x : &Nat) : Unit => (), λ(x : &Nat) : Unit => *x := S(Z), P, refl, refl)
  )

  -- twin of Boom3: `J` along the reflexive equation (both sides `λx. ()`), proving the true `0 = 0`
  def Boom3Ok : Eq(Nat, Z, Z) := (
    J(Π(x : &Nat). Unit, λ(x : &Nat) : Unit => (), λ(x : &Nat) : Unit => (), P, refl, refl)
  )

  -- Equality of functions is the least relation closed under the rules: two closures that
  -- are stuck at their generic calls are not identified. Read coinductively, these two would
  -- be equal, and `J` would prove `1 = 0`.
  reject def CoInd :
      Eq(Π(x : &Nat). Unit, (λ(x : &Nat) : Unit => match *x { Z => (), S _ => *x := Z }), (λ(x : &Nat) : Unit => match *x { Z => *x := S(Z), S _ => () })) := (
    refl
  )

  -- twin of CoInd: the two closures are the same one, so `refl` applies
  def CoIndOk :
      Eq(Π(x : &Nat). Unit, (λ(x : &Nat) : Unit => match *x { Z => (), S _ => *x := Z }), (λ(x : &Nat) : Unit => match *x { Z => (), S _ => *x := Z })) := (
    refl
  )

  -- Observing a returned borrow only through its current contents would
  -- identify `PickX` and `PickY`, since neither writes anything, and transport would prove
  -- `0 = 1 ∧ 1 = 0` (D38).
  reject def ConvPick : Eq(Π(x : &Nat) (y : &Nat). &Nat, PickX, PickY) := refl

  -- twin of ConvPick: `PickX` against itself
  def ConvPickOk : Eq(Π(x : &Nat) (y : &Nat). &Nat, PickX, PickX) := refl
  reject def TY : Q(PickY) := J(Π(x : &Nat) (y : &Nat). &Nat, PickX, PickY, Q, refl, TX)

  -- twin of TY: transport along the reflexive `PickX = PickX`, concluding `Q(PickX)`
  def TYOk : Q(PickX) := J(Π(x : &Nat) (y : &Nat). &Nat, PickX, PickX, Q, refl, TX)

  reject def BoomX4 : Eq(Nat, 0, 1) ∧ Eq(Nat, 1, 0) := (
    let c = Z;
    let d = Z;
    TY(&c, &d)
  )

  -- twin of BoomX4: uses `TYOk` and states the true `0 = 0 ∧ 1 = 1`
  def BoomX4Ok : Eq(Nat, 0, 0) ∧ Eq(Nat, 1, 1) := (
    let c = Z;
    let d = Z;
    TYOk(&c, &d)
  )

  -- A function's erasure class and [Close] row are part of its type (D54). `H` returns a
  -- `P0`, which is `Prop` but not written as a sort, so `H` returns data and its calls run,
  -- while calls of a `Π(x : &Nat). Prop` return types and are erased. Were the two types
  -- convertible, `RunGGen`'s generic call would erase `g(&c)` and its
  -- instance at `H` would run it, and `Boom` would be a closed proof of `False`, as would
  -- `BoomI` through an identity function.
  def P0 : Type₁ := Prop

  def H (x : &Nat) : P0 := (
    *x := S(Z);
    ⊤
  )

  def RunG (f : Π(x : &Nat). Prop) : Nat := (
    let c = Z;
    let g = f;
    g(&c);
    c
  )

  def RunGGen (f : Π(x : &Nat). Prop) : Id(Nat, RunG(f), Z) := refl
  reject def Boom : False := RunGGen(H)
  reject def RunGH : Id(Nat, RunG(H), 1) := refl

  def IdF (f : Π(x : &Nat). Prop) : (Π(x : &Nat). Prop) := f

  def RunI (f : Π(x : &Nat). Prop) : Nat := (
    let c = Z;
    IdF(f)(&c);
    c
  )

  def RunIGen (f : Π(x : &Nat). Prop) : Id(Nat, RunI(f), Z) := refl
  reject def BoomI : False := RunIGen(H)

  -- The pre-pass reads `f`'s class above from its declared type, which is a Π-type as
  -- written, so the two paths agree even without D54. A parameter whose type is a Π-type
  -- only by computation, `RefPred(0)`, is different: an untyped run (a body called to compute
  -- a value) has no stored type to read, so the call through it takes the class of the
  -- function the parameter holds. At the generic call that is an abstract value of type
  -- `Π(x : &Nat). Prop`, which returns types, and `p(&c)` is erased; at the instance it is
  -- `H`, which returns data, and runs. Without D54 `H` is accepted at `RefPred(0)`, and
  -- `BoomPow` is a closed proof of `False`.
  def RefPred (n : Nat) : Type₁ := Π(x : &Nat). Prop

  def RunPow (p : RefPred(0)) : Nat := (
    let c = Z;
    p(&c);
    c
  )

  def RunPowGen (p : RefPred(0)) : Id(Nat, RunPow(p), Z) := refl
  reject def BoomPow : False := RunPowGen(H)

  -- twin of BoomPow: a function whose codomain is written `Prop` (same class as `RefPred(0)`'s), so the generic and instance runs agree
  def HPure (x : &Nat) : Prop := ⊤
  def BoomPowOk : Id(Nat, RunPow(HPure), Z) := RunPowGen(HPure)

  -- D77 (`notes/stability.md`, site 7): a binding's class is read from its type's syntax, a
  -- type function's Π-type off its body, so a function value that is stuck at an instance (a
  -- sealed program, `PickP(n)`) is erased as at the generic call. Read from the value, it was
  -- data at the instance and erased at the generic call, and these true statements were
  -- rejected with an internal error
  def PickP (n : Nat) : RefPred(0) := match n { Z => HPure, S _ => HPure, }
  def InstPow (n : Nat) : Id(Nat, RunPow(PickP(n)), Z) := RunPowGen(PickP(n))
  def InstPowZ : Id(Nat, RunPow(PickP(Z)), Z) := InstPow(Z)
  def DirectPow (n : Nat) : Id(Nat, RunPow(PickP(n)), Z) := refl
  -- a constant type reads as its value's Π-type
  def T0 : Type₁ := Π(x : &Nat). Prop
  def RunT0 (p : T0) : Nat := (let c = Z; p(&c); c)
  def RunT0Gen (p : T0) : Id(Nat, RunT0(p), Z) := refl
  -- a family whose arms are Π-types of different erasure classes has no class: which one a
  -- binding of it takes would be decided by computation
  def MixT (n : Nat) : Type₁ := match n { Z => Π(x : Type). Nat, S _ => Π(x : &Nat). Prop, }
  reject def RunMix (n : Nat) (f : MixT(n)) : Nat := match n { Z => Z, S m => (let c = Z; f(&c); c), }
  -- twin of RunMix: both arms return types
  def SameT (n : Nat) : Type₁ := match n { Z => Π(x : &Nat). Prop, S _ => Π(x : &Nat). Prop, }
  def RunSame (n : Nat) (f : SameT(n)) : Nat := match n { Z => Z, S m => (let c = Z; f(&c); c), }
  -- a recursive type function: a call of itself in its body says nothing new, so its class is
  -- its Π arm's; mixing classes through the recursion is still a conflict
  def RecP (n : Nat) : Type₁ by n := match n { Z => Π(x : &Nat). Prop, S m => RecP(m), }
  def RunRec (n : Nat) (p : RecP(n)) : Nat := match n { Z => (let c = Z; p(&c); c), S m => Z, }
  def RunRecGen (n : Nat) (p : RecP(n)) : Id(Nat, RunRec(n, p), Z) := match n { Z => refl, S m => refl, }
  def MixR (n : Nat) : Type₁ by n := match n { Z => Π(x : &Nat). Prop, S m => match m { Z => Π(x : Type). Nat, S k => MixR(k), }, }
  reject def UseMixR (n : Nat) (p : MixR(n)) : Nat := Z
  -- a body that names its Π-type with a `let` reads as that Π-type
  def LetP (n : Nat) : Type₁ := (let A = (Π(x : &Nat). Prop); A)
  def RunLet (p : LetP(0)) : Nat := (let c = Z; p(&c); c)
  -- a function into `Prop` is a statement, so its write is erased wherever a `RecP(0)` is
  -- expected, at the instance as at the generic call
  def WriteProp (x : &Nat) : Prop := (*x := S(Z); ⊤)
  def AtRec : Id(Nat, RunRec(0, WriteProp), Z) := RunRecGen(0, WriteProp)
  -- a type function that returns its type parameter reads as its argument: the call's
  -- argument is substituted into the body's reading, never evaluated, so `p`'s calls are erased
  -- on both paths, a sealed argument (`PickP(n)`) included
  def IdTy (A : Type₁) : Type₁ := A
  def RunIdTy (p : IdTy(Π(x : &Nat). Prop)) : Nat := (let c = Z; p(&c); c)
  def RunIdTyGen (p : IdTy(Π(x : &Nat). Prop)) : Id(Nat, RunIdTy(p), Z) := refl
  def AtIdTy : Id(Nat, RunIdTy(WriteProp), Z) := RunIdTyGen(WriteProp)
  def AtIdTySealed (n : Nat) : Id(Nat, RunIdTy(PickP(n)), Z) := RunIdTyGen(PickP(n))
  def IdTy2 (B : Type₁) : Type₁ := IdTy(B)
  def RunIdTy2 (p : IdTy2(Π(x : &Nat). Prop)) : Nat := (let c = Z; p(&c); c)
  def LetTy (B : Type₁) : Type₁ := (let C = B; C)
  def RunLetTy (p : LetTy(Π(x : &Nat). Prop)) : Nat := (let c = Z; p(&c); c)
  -- a type parameter in one arm and a Π-type in the other: they agree only at the same class
  def MixArg (A : Type₁) (n : Nat) : Type₁ := match n { Z => A, S _ => Π(x : &Nat). Prop, }
  reject def UseMixArg (n : Nat) (p : MixArg(Π(x : Type). Nat, n)) : Nat := Z
  def UseSameArg (n : Nat) (p : MixArg(Π(y : &Nat). Prop, n)) : Nat := match n { Z => Z, S m => (let c = Z; p(&c); c), }
  -- a type variable of the definition itself is unknown at the generic call: a value of it
  -- is not known to be a function there, so it cannot be called
  reject def UseTyVar (A : Type₁) (p : IdTy(A)) : Nat := (let c = Z; p(&c); c)

  -- The same for the class "returns proofs", with a codomain `V(Z)` that computes to `⊤`.
  -- D54 alone rejects `BoomP` at the argument; since D55 the codomain cannot even be written
  -- (`V(Z)`'s declared type `U(Z)` is not a sort).
  def RunP (f : Π(x : &Nat). ⊤) : Nat := (
    let c = Z;
    let g = f;
    g(&c);
    c
  )

  def RunPGen (f : Π(x : &Nat). ⊤) : Id(Nat, RunP(f), Z) := refl
  reject def WV (u : Unit) : V(Z) := refl

  -- twin of WV: the codomain is the sort-typed `⊤` rather than `V(Z)`
  def WVOk (u : Unit) : ⊤ := refl
  reject def BoomP : False := RunPGen(λ(x : &Nat) : V(Z) => (*x := S(Z); WV(())))

  -- `UU(n)` is `Unit` only by computation, yet `H2` passes where a `Π(x : &Nat). Unit` is
  -- expected (D54 compares only whether a function returns a borrow). Before η for `Unit`
  -- (D59), [Close] returned `()` for a codomain written `Unit` and a sealed program for
  -- `UU(Z)`, so the two paths gave `RunUH`'s statement different types, both true. Now every
  -- stuck call returns its sealed program and an equation at `Unit` is `⊤`, on both paths.
  def UU (n : Nat) : Type := (
    match n {
      Z => Unit,
      S _ => Unit,
    }
  )

  def H2 (x : &Nat) : UU(Z) := (
    *x := S(Z);
    ()
  )

  def RunU (f : Π(x : &Nat). Unit) (n : Nat) : Id(Unit, let c = n; f(&c), ()) := refl
  def RunUH (n : Nat) : ⊤ := RunU(H2, n)
}


/-! ## Conversion, modelled (`notes/conv-model.md`)

Conversion is equality of meanings in the set model: two convertible values denote the same
element, so `J` and transport preserve truth. A function value's meaning is fixed by its captured
values and the observation of its generic call (result, what a returned borrow holds at the return,
and the final contents of the generic owned places); a function that inspects an abstract argument
is closed off there and is convertible only with itself. Each pair below is a true equation the
checker proves, or a false or unprovable one it rejects, with the reason asserted. -/

ochr ConvModel uses Nats, Fixtures {
  -- reading a place and writing the same value back is the identity on it
  def RW (x : &Nat) : Unit := (let v = clone(*x); *x := v)
  def Noop (x : &Nat) : Unit := ()
  def RWEq : Eq(Π(x : &Nat). Unit, RW, Noop) := refl
  -- ... so transport along it keeps truth
  def PW (h : Π(x : &Nat). Unit) : Prop := Id(Nat, let c = S(Z); h(&c); c, S(Z))
  def PNoop : PW(Noop) := refl
  def PRW : PW(RW) := J(Π(x : &Nat). Unit, Noop, RW, PW, refl, PNoop)
  -- moving a borrowed number out and writing its successor back is writing the successor
  def MvS (x : &Nat) : Unit := (let v = *x; *x := S(v))
  def CpS (x : &Nat) : Unit := (*x := S(clone(*x)))
  def MvCp : Eq(Π(x : &Nat). Unit, MvS, CpS) := refl
  reject def MvNoop : Eq(Π(x : &Nat). Unit, MvS, Noop) := refl
  -- a returned borrow is observed with what it holds at the return, not only where it points
  def W5 (x : &Nat) : &Nat := (*x := S(Z); x)
  def Id0 (x : &Nat) : &Nat := x
  reject def W5Eq : Eq(Π(x : &Nat). &Nat, W5, Id0) := refl
  def W5Self : Eq(Π(x : &Nat). &Nat, W5, W5) := refl
  -- η at Unit: a Unit argument carries nothing
  def UU (u : Unit) : Unit := u
  def UK (u : Unit) : Unit := ()
  def UUEq : Eq(Π(u : Unit). Unit, UU, UK) := refl
  -- a function that inspects its argument is closed off at its generic call, so it is
  -- convertible only with itself: a true equation between two copies is rejected (incomplete,
  -- as conversion is the least relation)
  def IsZ (n : Nat) : Nat := match n { Z => S(Z), S _ => Z }
  def IsZ2 (n : Nat) : Nat := match n { Z => S(Z), S _ => Z }
  reject def IsZEq : Eq(Π(n : Nat). Nat, IsZ, IsZ2) := refl
  def IsZSelf : Eq(Π(n : Nat). Nat, IsZ, IsZ) := refl
  -- two wrappers of one stuck call observe the same sealed program
  def WrapA (n : Nat) : Nat := IsZ(n)
  def WrapB (n : Nat) : Nat := IsZ(n)
  def WrapEq : Eq(Π(n : Nat). Nat, WrapA, WrapB) := refl
  -- returned closures are compared by their captures and their generic calls
  def MkA (n : Nat) : (Π(m : Nat). Nat) := λ(m : Nat) : Nat => clone(n)
  def MkB (n : Nat) : (Π(m : Nat). Nat) := λ(m : Nat) : Nat => clone(n)
  def MkEq : Eq(Π(n : Nat). (Π(m : Nat). Nat), MkA, MkB) := refl
  -- [Conv-pi]: statements are compared by what they compute to at generic arguments
  def UseTriv (h : Π(x : &Nat). Id(Unit, (), ())) : Unit := ()
  def PassW0 (h : Π(x : &Nat). Id(Unit, *x := 0, *x := 0)) : Unit := UseTriv(h)
  reject def PassW1 (h : Π(x : &Nat). Id(Unit, *x := 0, ())) : Unit := UseTriv(h)
  def UseTop (h : Π(n : Nat). ⊤) : Unit := ()
  def PassAnd (h : Π(n : Nat). ⊤ ∧ Eq(Nat, n, n)) : Unit := UseTop(h)
  -- transport across two convertible functions keeps truth
  def PZ (h : Π(n : Nat). Nat) : Prop := Eq(Nat, h(Z), S(Z))
  def PZA : PZ(WrapA) := refl
  def PZB : PZ(WrapB) := J(Π(n : Nat). Nat, WrapA, WrapB, PZ, refl, PZA)
}

#guard (run "ConvModel" ConvModel).rejectedWith [
  ("MvNoop", "the body of MvNoop has type ⊤, but the goal is Eq(Π(x : &Nat). Unit, MvS, Noop)"),
  ("W5Eq", "the body of W5Eq has type ⊤, but the goal is Eq(Π(x : &Nat). &Nat, W5, Id0)"),
  ("IsZEq", "the body of IsZEq has type ⊤, but the goal is Eq(Π(n : Nat). Nat, IsZ, IsZ2)"),
  ("PassW1", "argument 1 (h) has type Π(x : &Nat). Id(Unit, *x := 0, ()), expected Π(x : &Nat). Id(Unit, (), ())")]
