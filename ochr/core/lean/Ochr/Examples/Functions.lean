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

  def TwiceNoop (f : Π(_ : Unit). Unit) : Id(Unit, Twice(clone(f)), ()) := refl

  -- With a borrow argument, `f` may write, and what it leaves is a sealed program. Moving
  -- `x` into the second call instead of reborrowing it makes no difference.
  def TwiceM (f : Π(_ : &Nat). Unit) (x : &Nat) : Unit := (
    f(&*x);
    f(&*x)
  )

  def TwiceMMove (f : Π(_ : &Nat). Unit) (x : &Nat) : Id(Unit, TwiceM(clone(f), x), f(&*x); f(x)) := refl

  -- Instantiated with a function that adds zero, `TwiceM` does nothing, by induction ...
  def TwiceMZero (x : &Nat) : Id(Unit, TwiceM(λ(z : &Nat) : Unit => AddM(z, 0), &*x), ()) by x := (
    match *x {
      Z => refl,
      S p => TwiceMZero(&p),
    }
  )

  -- ... or by citing the lemma twice. A cited lemma runs on a private copy, so it leaves `*x`
  -- alone; `J` composes the two instances. `Add(s, 0)` closes off into the same sealed program
  -- as `AddM(&*x, 0)`.
  def TwiceMZero' (x : &Nat) : Id(Unit, TwiceM(λ(z : &Nat) : Unit => AddM(z, 0), &*x), ()) := (
    let s = clone(*x);
    let h1 = AddMZero(&*x);
    AddM(&*x, 0);
    let h2 = AddMZero(&*x);
    J(Nat, Add(s, 0), s, λ(z : Nat) : Prop => Id(Nat, Add(Add(clone(s), 0), 0), clone(z)), h1, h2)
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
  def UseA (h : Π(x : &Nat). Id(Unit, AddM(&*x, 0), ())) : Unit := ()
  def PassA (h : Π(y : &Nat). Id(Unit, let t = 0; AddM(&*y, t), ())) : Unit := UseA(h)

  -- Statements that differ at the generic arguments stay different.
  reject def PassStuck (h : Π(n : Nat). Id(Nat, Add(n, 0), n)) : Unit := UseRefl(h)
  reject def PassWrong (h : Π(n : Nat). Id(Nat, clone(n), 0)) : Unit := UseRefl(h)
  def UseW (h : Π(x : &Nat). Id(Unit, *x := 0, *x := 0)) : Unit := ()
  reject def PassW (h : Π(x : &Nat). Id(Unit, *x := 0, *x := 1)) : Unit := UseW(h)
  reject def PassDom (f : Π(n : Unit). Nat) : Nat := Apply(f, 0)

  -- Two functions returning a borrow into different arguments ...
  def PickX (x : &Nat) (y : &Nat) : &Nat := x
  def PickY (x : &Nat) (y : &Nat) : &Nat := y

  -- ... and a property that tells them apart: writing through the result changes `*x`.
  def Q (h : Π(x : &Nat) (y : &Nat). &Nat) : Prop := (
    Π(x : &Nat) (y : &Nat). Id(Unit, let r = h(&*x, &*y); *r := S(Z), *x := S(Z))
  )

  def TX : Q(PickX) := (
    let h = PickX;
    λ(x : &Nat) (y : &Nat) : Id(Unit, let r = h(&*x, &*y); *r := S(Z), *x := S(Z)) => refl
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

  def RunGGen (f : Π(x : &Nat). Prop) : Id(Nat, RunG(clone(f)), Z) := refl
  reject def Boom : False := RunGGen(H)
  reject def RunGH : Id(Nat, RunG(H), 1) := refl

  def IdF (f : Π(x : &Nat). Prop) : (Π(x : &Nat). Prop) := f

  def RunI (f : Π(x : &Nat). Prop) : Nat := (
    let c = Z;
    IdF(f)(&c);
    c
  )

  def RunIGen (f : Π(x : &Nat). Prop) : Id(Nat, RunI(clone(f)), Z) := refl
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

  def RunPowGen (p : RefPred(0)) : Id(Nat, RunPow(clone(p)), Z) := refl
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
  def InstPow (n : Nat) : Id(Nat, RunPow(PickP(clone(n))), Z) := RunPowGen(PickP(n))
  def InstPowZ : Id(Nat, RunPow(PickP(Z)), Z) := InstPow(Z)
  def DirectPow (n : Nat) : Id(Nat, RunPow(PickP(clone(n))), Z) := refl
  -- a constant type reads as its value's Π-type
  def T0 : Type₁ := Π(x : &Nat). Prop
  def RunT0 (p : T0) : Nat := (let c = Z; p(&c); c)
  def RunT0Gen (p : T0) : Id(Nat, RunT0(clone(p)), Z) := refl
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
  def RunRecGen (n : Nat) (p : RecP(n)) : Id(Nat, RunRec(clone(n), clone(p)), Z) := match n { Z => refl, S m => refl, }
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
  def RunIdTyGen (p : IdTy(Π(x : &Nat). Prop)) : Id(Nat, RunIdTy(clone(p)), Z) := refl
  def AtIdTy : Id(Nat, RunIdTy(WriteProp), Z) := RunIdTyGen(WriteProp)
  def AtIdTySealed (n : Nat) : Id(Nat, RunIdTy(PickP(clone(n))), Z) := RunIdTyGen(PickP(n))
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

  def RunU (f : Π(x : &Nat). Unit) (n : Nat) : Id(Unit, let c = clone(n); f(&c), ()) := refl
  def RunUH (n : Nat) : ⊤ := RunU(H2, n)

  -- ## Called bodies are typed by declaration (D82)
  -- Every binding has its declared type in every run: a called body's parameters, a closure's
  -- captures, a `let`, a sealed program's cells. Nothing reads a binding's type off its value.

  -- A closure capturing data, run at an instance: its body projects the captured pair, which
  -- needs the capture's type; the closure recorded its declared type when it was formed.
  def ApplyAtUnit (f : Π(u : Unit). Nat) : Nat := f(())
  def SndOf (p : Nat × Nat) : Nat := ApplyAtUnit(λ(u : Unit) : Nat => clone(p).1)
  def SndOfRun : Id(Nat, SndOf((1, 2)), 2) := refl
  reject def SndOfWrong : Id(Nat, SndOf((1, 2)), 1) := refl
  def SndOfGen (a : Nat) (b : Nat) : Id(Nat, SndOf((clone(a), clone(b))), clone(b)) := refl

  -- A pattern variable whose value has a moved-out hole: when `a.1` is read, `a` holds `(⊥, y)`,
  -- which has no type of its own; its declared type, the field type of `q`'s, says it is a pair.
  def TakeBoth (q : (Nat × Nat) × Nat) : Nat := (
    let Mk(a, b) = q;
    let x = a.0;
    let y = a.1;
    Add(x, y)
  )
  def TakeBothRun : Id(Nat, TakeBoth(((1, 2), 3)), 3) := refl
  reject def TakeBothWrong : Id(Nat, TakeBoth(((1, 2), 3)), 4) := refl

  -- A stuck side of `Id` in a called body (a type function's): typed from the start, its match on
  -- the unknown `*x` is split and closed off as a block, as when the `Id` is written directly.
  def StuckIdSame (x : &Nat) : Prop := Id(Nat, match *x { Z => 0, S _ => 1 }, match *x { Z => 0, S _ => 1 })
  def StuckIdSameHolds (x : &Nat) : StuckIdSame(x) := refl
  def StuckIdDiff (x : &Nat) : Prop := Id(Nat, match *x { Z => 0, S _ => 1 }, match *x { Z => 1, S _ => 0 })
  reject def StuckIdDiffHolds (x : &Nat) : StuckIdDiff(x) := refl

  -- A value with no type of its own, read by a stuck side of `Id`: `MkT`'s body builds
  -- `MkTag(n)` without writing its parameter, so the value records none, and only `t`'s declared
  -- type (`MkT`'s codomain, `Tag(Nat)`) says what it is. Before D82, `t` had no stored type in the
  -- machine, and typing the side read the value.
  inductive Tag (A : Type) := MkTag(n : Nat)
  def MkT (n : Nat) : Tag(Nat) := MkTag(n)
  def TagSame (x : &Nat) : Prop := (
    let t = MkT(clone(*x));
    Id(Tag(Nat), match *x { Z => clone(t), S _ => clone(t) }, match *x { Z => clone(t), S _ => clone(t) })
  )
  def TagSameHolds (x : &Nat) : TagSame(x) := refl
  def TagDiff (x : &Nat) : Prop := (
    let t = MkT(clone(*x));
    Id(Tag(Nat), match *x { Z => clone(t), S _ => clone(t) }, match *x { Z => clone(t), S _ => MkTag[Nat](0) })
  )
  reject def TagDiffHolds (x : &Nat) : TagDiff(x) := refl

  -- The same value captured by a closure whose body is run by a call (`PropAtUnit`'s): the
  -- closure records `t`'s declared type with it, and its body's stuck `Id` side reads `t` by it.
  -- Before D82 the capture had no type and the definitions themselves were rejected ("cannot
  -- infer the type of the place κ").
  def PropAtUnit (P : Π(u : Unit). Prop) : Prop := P(())
  def CapSame (n : Nat) : Prop := (
    let t = MkT(clone(n));
    PropAtUnit(λ(u : Unit) : Prop =>
      Id(Tag(Nat), match n { Z => clone(t), S _ => clone(t) }, match n { Z => clone(t), S _ => clone(t) }))
  )
  def CapSameHolds (n : Nat) : CapSame(n) := refl
  def CapSameAt : CapSame(3) := refl
  def CapDiff (n : Nat) : Prop := (
    let t = MkT(clone(n));
    PropAtUnit(λ(u : Unit) : Prop =>
      Id(Tag(Nat), match n { Z => clone(t), S _ => clone(t) }, match n { Z => clone(t), S _ => MkTag[Nat](0) }))
  )
  reject def CapDiffHolds (n : Nat) : CapDiff(n) := refl
  def CapDiffAtZ : CapDiff(Z) := refl
}

-- D82: the twins are rejected because their statements are false, not because a type could not
-- be read (before D82, `TagDiffHolds` failed with "cannot infer the type of the place t")
#guard (run "Functions" Functions).rejectedWith [
  ("SndOfWrong", "the body of SndOfWrong has type ⊤, but the goal is False"),
  ("TakeBothWrong", "the body of TakeBothWrong has type ⊤, but the goal is False"),
  ("StuckIdDiffHolds", "the body of StuckIdDiffHolds has type ⊤, but the goal is Eq(Nat, "),
  ("TagDiffHolds", "the body of TagDiffHolds has type ⊤, but the goal is Eq(Tag(Nat), "),
  ("CapDiffHolds", "the body of CapDiffHolds has type ⊤, but the goal is Eq(Tag(Nat), ")]


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

/-! ## A call through an unknown whose type is a sort

A parameter `f : A` with `A : Type` is a value of an unknown type, not a function: calling it is
rejected at the generic call, before a class or [Close] row is read from its type (`callFn`).
`Stability.lean`'s `DecisionsCommute` relies on this order: its class and row fields speak only
of Π-type values, since an instance `A := Π(n : Nat). Nat` would read a class and a row the
generic run never decided. `CallPi` is the same call through a Π-typed parameter. -/

ochr CallUnknown uses Nats {
  def CallPi (f : Π(n : Nat). Nat) : Nat := f(Z)
  reject def CallSort (A : Type) (f : A) : Nat := f(Z)
}

#guard (run "CallUnknown" CallUnknown).rejectedWith [("CallSort", "not a function type: σ0")]

/-! ## Values in flight carry their types (D104)

Every binding has a stored type (D82); so does every temporary, a value the machine holds between
computing it and storing or consuming it: a call's earlier arguments while a later one runs, a
constructor's earlier fields, an assignment's right-hand side, a discarded value, a result across
a `let`'s drop, the join or a frame's pop. Each is held with the type the machine has in hand when
it pushes it. The checker never reads it, so no verdict depends on it; it is there so that the
consistency proof's invariant ("values have their types") covers values in flight. Each program
below holds such a value; the guards read the recorded states (`Config.recordStates`) at each term
of each declaration's own code: every temporary there has a stored type, a borrow at a borrow
type. The recorded states are at the declaration's own terms only; `inFlightPushes` reads every
push, at every call depth (`Config.recordPushes`): none in a typed run lacks a type but `⋆`. -/

ochr InFlight uses Nats {
  def Snd (x : &Nat) (y : Nat) : Nat := y
  def IdR (x : &Nat) : &Nat := x
  -- a call's earlier argument, a borrow, held while the later one runs
  def ArgBorrow (a : Nat) (b : Nat) : Nat := Snd(&a, b)
  def ArgBorrowRun : Eq(Nat, ArgBorrow(1, 2), 2) := refl
  -- two calls deep: the outer call's head and borrow, then the inner call's
  def Nested (a : Nat) (b : Nat) : Nat := Snd(&a, Snd(&b, S(Z)))
  -- a returned borrow, held as an argument while the later one runs
  def ArgReturned (a : Nat) (b : Nat) : Nat := Snd(IdR(&a), b)
  -- a constructor's earlier field held while the later one runs
  def Fields (a : Nat) (b : Nat) : Pair(Nat, Nat) := Mk(S(a), Add(b, Z))
  -- an assignment's right-hand side, held while the old content is dropped
  def Assign (a : &Nat) (b : Nat) : Unit := *a := S(b)
  -- a discarded value, a borrow
  def Discard (a : Nat) : Nat := (&a; a)
  -- a result held across the drop of a `let`'s binding, the binding a borrow
  def LetDrop (a : Nat) : Nat := (let r = &a; S(Z))
  -- an arm's result held across the join, which drops what the other arm moves
  def Join (a : Nat) : Nat := (let k = S(Z); let x = match k { Z => a, S _ => Z }; x)
  -- a known function's result, a borrow, held at the call's type across its frame's pop (its
  -- body runs untyped and has no type of its own)
  def UseIdR (u : Unit) : Nat := (let y = 1; let r = IdR(&y); 0)
  -- a stuck block's call: its head and its by-move argument held at the block's function type
  -- and domain
  def Blk (n : Nat) (x : Nat) : Nat := (let r = match n { Z => x, S _ => Z }; r)
}

/-- The temporaries of the top frame, `value : type`, at each recorded state on entry to a term
of `name`'s own code (`Config.recordStates`, located). -/
def inFlightTemps (name : String) : List (List String) :=
  let r := runWith (some Prelude) "InFlight" InFlight { recordStates := true } (located := true)
  match r.rows.find? (·.name == name) with
  | some row => row.trace.toList.filterMap fun
      | .state _ false _ st =>
        let fr := st.env.back!
        some ((List.range fr.temps.size).map fun i =>
          s!"{fr.temps[i]!.pp} : {match fr.tempTys[i]?.join with | some T => T.pp | none => "(no type)"}")
      | _ => none
  | none => []

/-- Every temporary of every frame, at every recorded state of every declaration of `InFlight`
(entry and exit), has a stored type, and one that is a borrow type exactly when it holds a borrow. -/
def inFlightAllTyped : Bool :=
  let r := runWith (some Prelude) "InFlight" InFlight { recordStates := true } (located := true)
  r.rows.all fun row => row.trace.all fun
    | .state _ _ _ st => st.env.all fun fr =>
        fr.temps.size == fr.tempTys.size &&
        (fr.temps.zip fr.tempTys).all fun (v, T) => match v, T with
          | .borrow .., some (.tRef _) => true
          | .borrow .., _ => false
          | .bot, some _ => true
          | _, some (.tRef _) => false
          | _, some _ => true
          | v, none => v == .proof
    | _ => true

#guard inFlightAllTyped

/-- The pushes of `InFlight`'s rows with no stored type in a typed run, at every call depth
(`Config.recordPushes`): `(site, value)`, `⋆` excluded. -/
def inFlightPushes : List (String × String) :=
  let r := runWith (some Prelude) "InFlight" InFlight { recordPushes := true }
  r.rows.flatMap fun row => row.trace.toList.filterMap fun
    | .push site true v _ => if v == .proof then none else some (site, v.pp)
    | _ => none

#guard inFlightPushes.isEmpty

-- the outer call's head and borrow argument, then the inner call's, all typed
#guard (inFlightTemps "Nested").contains ["Snd : Π(x : &Nat) (y : Nat). Nat", "borrow_0 σ0 : &Nat",
  "Snd : Π(x : &Nat) (y : Nat). Nat", "borrow_1 σ1 : &Nat"]
-- a borrow a call returned (its fresh label, D99), at the call's declared type
#guard (inFlightTemps "ArgReturned").contains ["Snd : Π(x : &Nat) (y : Nat). Nat", "borrow_1 σ0 : &Nat"]
-- a constructor's first field while the second is evaluated
#guard (inFlightTemps "Fields").contains ["S(σ0) : Nat", "Add : Π(x : Nat) (y : Nat). Nat"]

/-! ## A `let` of a call that returns a type or a proof has its type in a run (D132)

In an untyped run (a called body, a sealed program's re-run) a `let` whose right-hand side is a
call defers the call's type to its binding, computed if the binding's type is read (D82, D130). A
call that returns a type or a proof is erased: it runs as a statement, on a private copy of the
state, and the record of its deferred type went with the copy, so the binding had no type at all.
Every function below was accepted and most of the closed calls (`C…`) and generic callers (`H…`)
of those whose binding's type is read later were rejected: "cannot infer the type of the place X",
or "INTERNAL [Capture] X has no stored type". Since D132 a `let` defers only a call the pre-pass
does not erase; an erased call's type comes back with its value. Each right-hand side (a type, one
that closes off at an unknown argument, a call of a closure, a proposition, a function type, a
proof; and, as controls, the same wrapped so that it is not a bare call) by each way the
binding's type is read later (an annotation, a Π-type, the tail, a capture, an argument, `clone`, a
copy, a field, `J`, a match, an ascription). Generated by `ochr/core/probes/erased-lets/gen.py`. -/
ochr ErasedLets uses Nats {
  def TF (n : Nat) : Type := Nat
  def PF (n : Nat) : Prop := Eq(Nat, n, n)
  def FT (n : Nat) : Type := Π(x : Nat). Nat
  def TS (n : Nat) : Type := match n { Z => Nat, S(m) => Nat }
  def lem (n : Nat) : Eq(Nat, n, n) := refl
  inductive IsZ (n : Nat) : Prop := MkZ(h : Eq(Nat, n, n))
  def lemZ (n : Nat) : IsZ(n) := MkZ[n](refl)
  def useTy (A : Type) : Nat := 3
  def useProp (P : Prop) : Nat := 3
  def useP (n : Nat) (h : Eq(Nat, n, n)) : Nat := 3
  def useZ (n : Nat) (h : IsZ(n)) : Nat := 3
  inductive WP (n : Nat) := MkWP(p : Eq(Nat, n, n))
  def GTFAnn (n : Nat) : Nat := (let X = TF(n); let z : X = 3; 3)
  def CTFAnn : Eq(Nat, GTFAnn(1), 3) := refl
  def HTFAnn (n : Nat) : Nat := GTFAnn(n)
  def GTFArg (n : Nat) : Nat := (let X = TF(n); useTy(X))
  def CTFArg : Eq(Nat, GTFArg(1), 3) := refl
  def HTFArg (n : Nat) : Nat := GTFArg(n)
  def GTFClone (n : Nat) : Nat := (let X = TF(n); let c = clone(X); 3)
  def CTFClone : Eq(Nat, GTFClone(1), 3) := refl
  def HTFClone (n : Nat) : Nat := GTFClone(n)
  def GTFCopy (n : Nat) : Nat := (let X = TF(n); let y = X; 3)
  def CTFCopy : Eq(Nat, GTFCopy(1), 3) := refl
  def HTFCopy (n : Nat) : Nat := GTFCopy(n)
  def GTFPi (n : Nat) : Nat := (let X = TF(n); let f : (Π(a : X). X) = (λ(a : X) : X => a); 3)
  def CTFPi : Eq(Nat, GTFPi(1), 3) := refl
  def HTFPi (n : Nat) : Nat := GTFPi(n)
  def GTFRet (n : Nat) : Nat := (let X = TF(n); (let z : X = 3; z))
  def CTFRet : Eq(Nat, GTFRet(1), 3) := refl
  def HTFRet (n : Nat) : Nat := GTFRet(n)
  def GTFCap (n : Nat) : Nat := (let X = TF(n); let g = (λ(m : Nat) : Nat => (let q : X = m; q)); g(3))
  def CTFCap : Eq(Nat, GTFCap(1), 3) := refl
  def HTFCap (n : Nat) : Nat := GTFCap(n)
  def GTSArg (n : Nat) : Nat := (let X = TS(n); useTy(X))
  def CTSArg : Eq(Nat, GTSArg(1), 3) := refl
  def HTSArg (n : Nat) : Nat := GTSArg(n)
  def GTSClone (n : Nat) : Nat := (let X = TS(n); let c = clone(X); 3)
  def CTSClone : Eq(Nat, GTSClone(1), 3) := refl
  def HTSClone (n : Nat) : Nat := GTSClone(n)
  def GTSCopy (n : Nat) : Nat := (let X = TS(n); let y = X; 3)
  def CTSCopy : Eq(Nat, GTSCopy(1), 3) := refl
  def HTSCopy (n : Nat) : Nat := GTSCopy(n)
  def GTSPi (n : Nat) : Nat := (let X = TS(n); let f : (Π(a : X). X) = (λ(a : X) : X => a); 3)
  def CTSPi : Eq(Nat, GTSPi(1), 3) := refl
  def HTSPi (n : Nat) : Nat := GTSPi(n)
  def GCloAnn (n : Nat) : Nat := (let X = (let F = (λ(m : Nat) : Type => Nat); F(n)); let z : X = 3; 3)
  def CCloAnn : Eq(Nat, GCloAnn(1), 3) := refl
  def HCloAnn (n : Nat) : Nat := GCloAnn(n)
  def GCloArg (n : Nat) : Nat := (let X = (let F = (λ(m : Nat) : Type => Nat); F(n)); useTy(X))
  def CCloArg : Eq(Nat, GCloArg(1), 3) := refl
  def HCloArg (n : Nat) : Nat := GCloArg(n)
  def GCloClone (n : Nat) : Nat := (let X = (let F = (λ(m : Nat) : Type => Nat); F(n)); let c = clone(X); 3)
  def CCloClone : Eq(Nat, GCloClone(1), 3) := refl
  def HCloClone (n : Nat) : Nat := GCloClone(n)
  def GCloCopy (n : Nat) : Nat := (let X = (let F = (λ(m : Nat) : Type => Nat); F(n)); let y = X; 3)
  def CCloCopy : Eq(Nat, GCloCopy(1), 3) := refl
  def HCloCopy (n : Nat) : Nat := GCloCopy(n)
  def GCloPi (n : Nat) : Nat := (let X = (let F = (λ(m : Nat) : Type => Nat); F(n)); let f : (Π(a : X). X) = (λ(a : X) : X => a); 3)
  def CCloPi : Eq(Nat, GCloPi(1), 3) := refl
  def HCloPi (n : Nat) : Nat := GCloPi(n)
  def GCloRet (n : Nat) : Nat := (let X = (let F = (λ(m : Nat) : Type => Nat); F(n)); (let z : X = 3; z))
  def CCloRet : Eq(Nat, GCloRet(1), 3) := refl
  def HCloRet (n : Nat) : Nat := GCloRet(n)
  def GCloCap (n : Nat) : Nat := (let X = (let F = (λ(m : Nat) : Type => Nat); F(n)); let g = (λ(m : Nat) : Nat => (let q : X = m; q)); g(3))
  def CCloCap : Eq(Nat, GCloCap(1), 3) := refl
  def HCloCap (n : Nat) : Nat := GCloCap(n)
  def GCloLAnn (n : Nat) : Nat := (let F = (λ(m : Nat) : Type => Nat); let X = F(n); let z : X = 3; 3)
  def CCloLAnn : Eq(Nat, GCloLAnn(1), 3) := refl
  def HCloLAnn (n : Nat) : Nat := GCloLAnn(n)
  def GCloLArg (n : Nat) : Nat := (let F = (λ(m : Nat) : Type => Nat); let X = F(n); useTy(X))
  def CCloLArg : Eq(Nat, GCloLArg(1), 3) := refl
  def HCloLArg (n : Nat) : Nat := GCloLArg(n)
  def GCloLClone (n : Nat) : Nat := (let F = (λ(m : Nat) : Type => Nat); let X = F(n); let c = clone(X); 3)
  def CCloLClone : Eq(Nat, GCloLClone(1), 3) := refl
  def HCloLClone (n : Nat) : Nat := GCloLClone(n)
  def GCloLCopy (n : Nat) : Nat := (let F = (λ(m : Nat) : Type => Nat); let X = F(n); let y = X; 3)
  def CCloLCopy : Eq(Nat, GCloLCopy(1), 3) := refl
  def HCloLCopy (n : Nat) : Nat := GCloLCopy(n)
  def GCloLPi (n : Nat) : Nat := (let F = (λ(m : Nat) : Type => Nat); let X = F(n); let f : (Π(a : X). X) = (λ(a : X) : X => a); 3)
  def CCloLPi : Eq(Nat, GCloLPi(1), 3) := refl
  def HCloLPi (n : Nat) : Nat := GCloLPi(n)
  def GCloLRet (n : Nat) : Nat := (let F = (λ(m : Nat) : Type => Nat); let X = F(n); (let z : X = 3; z))
  def CCloLRet : Eq(Nat, GCloLRet(1), 3) := refl
  def HCloLRet (n : Nat) : Nat := GCloLRet(n)
  def GCloLCap (n : Nat) : Nat := (let F = (λ(m : Nat) : Type => Nat); let X = F(n); let g = (λ(m : Nat) : Nat => (let q : X = m; q)); g(3))
  def CCloLCap : Eq(Nat, GCloLCap(1), 3) := refl
  def HCloLCap (n : Nat) : Nat := GCloLCap(n)
  def GPFAnn (n : Nat) : Nat := (let X = PF(n); let z : X = refl; 3)
  def CPFAnn : Eq(Nat, GPFAnn(1), 3) := refl
  def HPFAnn (n : Nat) : Nat := GPFAnn(n)
  def GPFArg (n : Nat) : Nat := (let X = PF(n); useProp(X))
  def CPFArg : Eq(Nat, GPFArg(1), 3) := refl
  def HPFArg (n : Nat) : Nat := GPFArg(n)
  def GPFClone (n : Nat) : Nat := (let X = PF(n); let c = clone(X); 3)
  def CPFClone : Eq(Nat, GPFClone(1), 3) := refl
  def HPFClone (n : Nat) : Nat := GPFClone(n)
  def GPFCopy (n : Nat) : Nat := (let X = PF(n); let y = X; 3)
  def CPFCopy : Eq(Nat, GPFCopy(1), 3) := refl
  def HPFCopy (n : Nat) : Nat := GPFCopy(n)
  def GFTAnn (n : Nat) : Nat := (let X = FT(n); let z : X = (λ(x : Nat) : Nat => x); 3)
  def CFTAnn : Eq(Nat, GFTAnn(1), 3) := refl
  def HFTAnn (n : Nat) : Nat := GFTAnn(n)
  def GFTArg (n : Nat) : Nat := (let X = FT(n); useTy(X))
  def CFTArg : Eq(Nat, GFTArg(1), 3) := refl
  def HFTArg (n : Nat) : Nat := GFTArg(n)
  def GFTApp (n : Nat) : Nat := (let X = FT(n); let f : X = (λ(x : Nat) : Nat => x); f(3))
  def CFTApp : Eq(Nat, GFTApp(1), 3) := refl
  def HFTApp (n : Nat) : Nat := GFTApp(n)
  def GFTCopy (n : Nat) : Nat := (let X = FT(n); let y = X; 3)
  def CFTCopy : Eq(Nat, GFTCopy(1), 3) := refl
  def HFTCopy (n : Nat) : Nat := GFTCopy(n)
  def GLemAnn (n : Nat) : Nat := (let X = lem(n); let k : Eq(Nat, n, n) = X; 3)
  def CLemAnn : Eq(Nat, GLemAnn(1), 3) := refl
  def HLemAnn (n : Nat) : Nat := GLemAnn(n)
  def GLemArg (n : Nat) : Nat := (let X = lem(n); useP(n, X))
  def CLemArg : Eq(Nat, GLemArg(1), 3) := refl
  def HLemArg (n : Nat) : Nat := GLemArg(n)
  def GLemClone (n : Nat) : Nat := (let X = lem(n); let c = clone(X); 3)
  def CLemClone : Eq(Nat, GLemClone(1), 3) := refl
  def HLemClone (n : Nat) : Nat := GLemClone(n)
  def GLemFieldP (n : Nat) : Nat := (let X = lem(n); let w = MkWP[n](X); 3)
  def CLemFieldP : Eq(Nat, GLemFieldP(1), 3) := refl
  def HLemFieldP (n : Nat) : Nat := GLemFieldP(n)
  def GLemJ (n : Nat) : Nat := (let X = lem(n); J(Nat, n, n, (λ(x : Nat) : Type => Nat), X, 3))
  def CLemJ : Eq(Nat, GLemJ(1), 3) := refl
  def HLemJ (n : Nat) : Nat := GLemJ(n)
  def GLemCopy (n : Nat) : Nat := (let X = lem(n); let y = X; 3)
  def CLemCopy : Eq(Nat, GLemCopy(1), 3) := refl
  def HLemCopy (n : Nat) : Nat := GLemCopy(n)
  def GLemAsc (n : Nat) : Nat := (let X = lem(n); let k = (X : Eq(Nat, n, n)); 3)
  def CLemAsc : Eq(Nat, GLemAsc(1), 3) := refl
  def HLemAsc (n : Nat) : Nat := GLemAsc(n)
  def GLemCap (n : Nat) : Nat := (let X = lem(n); let g = (λ(m : Nat) : Nat => (let q = X; m)); g(3))
  def CLemCap : Eq(Nat, GLemCap(1), 3) := refl
  def HLemCap (n : Nat) : Nat := GLemCap(n)
  def GLemZMatch (n : Nat) : Nat := (let X = lemZ(n); match X { MkZ(e) => 3 })
  def CLemZMatch : Eq(Nat, GLemZMatch(1), 3) := refl
  def HLemZMatch (n : Nat) : Nat := GLemZMatch(n)
  def GLemZCap (n : Nat) : Nat := (let X = lemZ(n); let g = (λ(m : Nat) : Nat => (let q = X; m)); g(3))
  def CLemZCap : Eq(Nat, GLemZCap(1), 3) := refl
  def HLemZCap (n : Nat) : Nat := GLemZCap(n)
  def GLemZArg (n : Nat) : Nat := (let X = lemZ(n); useZ(n, X))
  def CLemZArg : Eq(Nat, GLemZArg(1), 3) := refl
  def HLemZArg (n : Nat) : Nat := GLemZArg(n)
  def GLemZClone (n : Nat) : Nat := (let X = lemZ(n); let c = clone(X); 3)
  def CLemZClone : Eq(Nat, GLemZClone(1), 3) := refl
  def HLemZClone (n : Nat) : Nat := GLemZClone(n)
  def GLemZCopy (n : Nat) : Nat := (let X = lemZ(n); let y = X; 3)
  def CLemZCopy : Eq(Nat, GLemZCopy(1), 3) := refl
  def HLemZCopy (n : Nat) : Nat := GLemZCopy(n)
  def GSeqTFAnn (n : Nat) : Nat := (let X = ((); TF(n)); let z : X = 3; 3)
  def CSeqTFAnn : Eq(Nat, GSeqTFAnn(1), 3) := refl
  def HSeqTFAnn (n : Nat) : Nat := GSeqTFAnn(n)
  def GSeqTFArg (n : Nat) : Nat := (let X = ((); TF(n)); useTy(X))
  def CSeqTFArg : Eq(Nat, GSeqTFArg(1), 3) := refl
  def HSeqTFArg (n : Nat) : Nat := GSeqTFArg(n)
  def GSeqTFClone (n : Nat) : Nat := (let X = ((); TF(n)); let c = clone(X); 3)
  def CSeqTFClone : Eq(Nat, GSeqTFClone(1), 3) := refl
  def HSeqTFClone (n : Nat) : Nat := GSeqTFClone(n)
  def GSeqTFCopy (n : Nat) : Nat := (let X = ((); TF(n)); let y = X; 3)
  def CSeqTFCopy : Eq(Nat, GSeqTFCopy(1), 3) := refl
  def HSeqTFCopy (n : Nat) : Nat := GSeqTFCopy(n)
  def GSeqTFPi (n : Nat) : Nat := (let X = ((); TF(n)); let f : (Π(a : X). X) = (λ(a : X) : X => a); 3)
  def CSeqTFPi : Eq(Nat, GSeqTFPi(1), 3) := refl
  def HSeqTFPi (n : Nat) : Nat := GSeqTFPi(n)
  def GSeqTFRet (n : Nat) : Nat := (let X = ((); TF(n)); (let z : X = 3; z))
  def CSeqTFRet : Eq(Nat, GSeqTFRet(1), 3) := refl
  def HSeqTFRet (n : Nat) : Nat := GSeqTFRet(n)
  def GSeqTFCap (n : Nat) : Nat := (let X = ((); TF(n)); let g = (λ(m : Nat) : Nat => (let q : X = m; q)); g(3))
  def CSeqTFCap : Eq(Nat, GSeqTFCap(1), 3) := refl
  def HSeqTFCap (n : Nat) : Nat := GSeqTFCap(n)
  def GAscTFAnn (n : Nat) : Nat := (let X = (TF(n) : Type); let z : X = 3; 3)
  def CAscTFAnn : Eq(Nat, GAscTFAnn(1), 3) := refl
  def HAscTFAnn (n : Nat) : Nat := GAscTFAnn(n)
  def GAscTFArg (n : Nat) : Nat := (let X = (TF(n) : Type); useTy(X))
  def CAscTFArg : Eq(Nat, GAscTFArg(1), 3) := refl
  def HAscTFArg (n : Nat) : Nat := GAscTFArg(n)
  def GAscTFClone (n : Nat) : Nat := (let X = (TF(n) : Type); let c = clone(X); 3)
  def CAscTFClone : Eq(Nat, GAscTFClone(1), 3) := refl
  def HAscTFClone (n : Nat) : Nat := GAscTFClone(n)
  def GAscTFCopy (n : Nat) : Nat := (let X = (TF(n) : Type); let y = X; 3)
  def CAscTFCopy : Eq(Nat, GAscTFCopy(1), 3) := refl
  def HAscTFCopy (n : Nat) : Nat := GAscTFCopy(n)
  def GAscTFPi (n : Nat) : Nat := (let X = (TF(n) : Type); let f : (Π(a : X). X) = (λ(a : X) : X => a); 3)
  def CAscTFPi : Eq(Nat, GAscTFPi(1), 3) := refl
  def HAscTFPi (n : Nat) : Nat := GAscTFPi(n)
  def GAscTFRet (n : Nat) : Nat := (let X = (TF(n) : Type); (let z : X = 3; z))
  def CAscTFRet : Eq(Nat, GAscTFRet(1), 3) := refl
  def HAscTFRet (n : Nat) : Nat := GAscTFRet(n)
  def GAscTFCap (n : Nat) : Nat := (let X = (TF(n) : Type); let g = (λ(m : Nat) : Nat => (let q : X = m; q)); g(3))
  def CAscTFCap : Eq(Nat, GAscTFCap(1), 3) := refl
  def HAscTFCap (n : Nat) : Nat := GAscTFCap(n)
  def GSeqLemAnn (n : Nat) : Nat := (let X = ((); lem(n)); let k : Eq(Nat, n, n) = X; 3)
  def CSeqLemAnn : Eq(Nat, GSeqLemAnn(1), 3) := refl
  def HSeqLemAnn (n : Nat) : Nat := GSeqLemAnn(n)
  def GSeqLemArg (n : Nat) : Nat := (let X = ((); lem(n)); useP(n, X))
  def CSeqLemArg : Eq(Nat, GSeqLemArg(1), 3) := refl
  def HSeqLemArg (n : Nat) : Nat := GSeqLemArg(n)
  def GSeqLemClone (n : Nat) : Nat := (let X = ((); lem(n)); let c = clone(X); 3)
  def CSeqLemClone : Eq(Nat, GSeqLemClone(1), 3) := refl
  def HSeqLemClone (n : Nat) : Nat := GSeqLemClone(n)
  def GSeqLemFieldP (n : Nat) : Nat := (let X = ((); lem(n)); let w = MkWP[n](X); 3)
  def CSeqLemFieldP : Eq(Nat, GSeqLemFieldP(1), 3) := refl
  def HSeqLemFieldP (n : Nat) : Nat := GSeqLemFieldP(n)
  def GSeqLemJ (n : Nat) : Nat := (let X = ((); lem(n)); J(Nat, n, n, (λ(x : Nat) : Type => Nat), X, 3))
  def CSeqLemJ : Eq(Nat, GSeqLemJ(1), 3) := refl
  def HSeqLemJ (n : Nat) : Nat := GSeqLemJ(n)
  def GSeqLemCopy (n : Nat) : Nat := (let X = ((); lem(n)); let y = X; 3)
  def CSeqLemCopy : Eq(Nat, GSeqLemCopy(1), 3) := refl
  def HSeqLemCopy (n : Nat) : Nat := GSeqLemCopy(n)
  def GSeqLemAsc (n : Nat) : Nat := (let X = ((); lem(n)); let k = (X : Eq(Nat, n, n)); 3)
  def CSeqLemAsc : Eq(Nat, GSeqLemAsc(1), 3) := refl
  def HSeqLemAsc (n : Nat) : Nat := GSeqLemAsc(n)
  def GSeqLemCap (n : Nat) : Nat := (let X = ((); lem(n)); let g = (λ(m : Nat) : Nat => (let q = X; m)); g(3))
  def CSeqLemCap : Eq(Nat, GSeqLemCap(1), 3) := refl
  def HSeqLemCap (n : Nat) : Nat := GSeqLemCap(n)
}

/-! ## A call's arguments stay in Ω until the callee binds them (D115)

No value the machine holds lives only in the checker's own variables while anything runs or maps
over Ω. A call holds its head and its arguments as temporaries of the caller's frame from their
evaluation until the callee's frame binds them (or [Close] puts them in a sealed program's text, or
P5 ends a proof call's borrow arguments unrun), and its result while [Lend] renames its label; a
constructor holds its fields until its value is built, an assignment its right-hand side while
it is checked, a borrow its value while [Open] invalidates, and a borrow-typed match its result
while the join lends. Before D115 they were taken off the temporaries before the
call ran its scaffolding, and held only in the checker's own variables: in that window a borrow
argument had no holder in Ω, so its lender's loan read as a loan of an ended borrow (the meaning
spine's (WF2), at 662,366 states of 770 declarations, inside private copies at call depth above 0).
One program per operation that runs in that window, each with a closed run, and the rejected
attempts to put a sibling's loan into an argument: a proof call's borrow arguments ending (P5),
the marks of a borrow-returning call's lenders (rule 1), [Close]'s fills, [Rec]'s reading of the
arguments, a call evaluated as another call's argument; and the join of a borrow-typed match, whose
result is held while the join lends (its entry ends every borrow that could lend into the result
first). `callArgsLive` reads every state at every call depth, private copies included
(`Config.recordDeep`): every loan outside a sealed program is live. -/

ochr CallArgs uses Nats, Fixtures {
  -- the window inside a borrow parameter's type (the shape the sweep found, `Drops.Bad5Run`)
  def Pass (a : Nat) : Unit := (let b = a; let x = TailM(&b); ())
  def PassRun : Unit := Pass(1)
  -- (1) P5: a proof call's borrow arguments end in the window, one by one
  def P2 (x : &Nat) (y : &Nat) : True := refl
  def UseP2 : Nat := (let a = 1; let b = 2; let h : True = P2(&a, &b); Add(a, b))
  def UseP2Run : Eq(Nat, UseP2, 3) := refl
  def UseP2R (x : &(Nat × Nat)) : Unit := (let h : True = P2(&(*x).0, &(*x).1); ())
  def UseP2RRun : Eq(Nat × Nat, (let p = (1, 2); UseP2R(&p); p), (1, 2)) := refl
  def P3 (x : &Nat) (n : Nat) : Eq(Nat, n, n) := refl
  def UseP3 (n : Nat) (a : Nat) : Nat := (let h : Eq(Nat, n, n) = P3(&a, clone(n)); Add(a, n))
  -- (2) rule 1: the lenders of a borrow-returning call's arguments are marked in the window
  def M1 (n : Nat) (a : Nat) (b : Nat) : Nat := (let r = Pick(n, &a, &b); *r := 7; Add(a, b))
  def M1Run0 : Eq(Nat, M1(0, 1, 2), 9) := refl
  def M1Run1 : Eq(Nat, M1(1, 1, 2), 8) := refl
  def M2 (n : Nat) (m : Nat) (a : Nat) (b : Nat) (c : Nat) : Nat := (let r = Pick(n, &a, &b); let s = Pick(m, &*r, &c); *s := 7; Add(Add(a, b), c))
  def M2Run : Eq(Nat, M2(1, 0, 1, 2, 3), 11) := refl
  def M3 (n : Nat) (m : Nat) (a : Nat) (b : Nat) (c : Nat) : Nat := (let r = Pick(n, &a, &b); let s = Pick(m, &c, r); *s := 7; Add(Add(a, b), c))
  def M3Run : Eq(Nat, M3(0, 1, 1, 2, 3), 12) := refl
  -- (3) [Close] in the window: stuck calls with borrow arguments, beside arguments mentioning unknowns
  def C1 (n : Nat) (a : Nat) : Nat := (let b = clone(n); AddM(&a, b); a)
  def C1Run : Eq(Nat, C1(2, 3), 5) := refl
  def C2 (n : Nat) (a : Nat) (b : Nat) : Nat := (let r = Pick(clone(n), &a, &b); AddM(&*r, n); Add(a, b))
  def C2Run : Eq(Nat, C2(1, 4, 5), 10) := refl
  def C3 (n : Nat) (m : Nat) (a : Nat) (b : Nat) (c : Nat) : Nat := (let r = Pick(n, &a, &b); let s = Pick(m, r, &c); *s := 9; Add(Add(a, b), c))
  def C3Run : Eq(Nat, C3(0, 1, 1, 2, 3), 12) := refl
  -- (4) [Rec] in the window: a recursive call reads its arguments
  def R1 (x : &Nat) (y : Nat) : Unit by x := match *x { Z => (), S p => R1(&p, clone(y)) }
  def R2 (x : Nat) (y : &Nat) : Unit by x := match x { Z => (), S p => (AddM(&*y, 1); R2(p, &*y)) }
  def R2Run : Eq(Nat, (let k = 0; R2(3, &k); k), 3) := refl
  def R3 (x : &Nat) : &Nat by x := match *x { Z => x, S p => R3(&p) }
  def R3Run : Eq(Nat, (let k = 2; let t = R3(&k); *t := 5; k), 7) := refl
  -- (5) an argument holding a loan of a sibling's borrow: never formed ([Access], D106; P5's copy)
  reject def S1 (a : Nat) : Unit := (let q = &a; AddM(q, a))
  reject def S2 (a : Nat) : Unit := (let q = &a; AddM(&*q, a))
  reject def S3 (a : Nat) : Unit := (let q = &a; let h : True = P2(q, &a); ())
  -- (6) a call evaluated as another call's argument, inside the outer call's window
  def N1 (n : Nat) (a : Nat) (b : Nat) : Nat := (AddM(Pick(clone(n), &a, &b), Add(n, 1)); Add(a, b))
  def N1Run : Eq(Nat, N1(0, 1, 2), 4) := refl
  -- (7) a borrow-typed match's result held while the join lends: a borrow the block takes by move
  -- whose lender lies in the result's content is ended at the entry, so no mark can be left there
  reject def JE (x : &(Nat × Nat)) : Nat := (let k = Z; let q = &(*x).0; let r : &(Nat × Nat) = match k { Z => (AddM(q, 1); &*x), S _ => (AddM(q, 2); &*x) }; clone((*r).0))
  reject def JEU (k : Nat) (x : &(Nat × Nat)) : Nat := (let q = &(*x).0; let r : &(Nat × Nat) = match k { Z => (AddM(q, 1); &*x), S _ => (AddM(q, 2); &*x) }; clone((*r).0))
  reject def JER (x : &(Nat × Nat)) : Nat := (let k = Z; let r0 = &*x; let q = &(*r0).0; let r : &(Nat × Nat) = match k { Z => (AddM(q, 1); r0), S _ => (AddM(q, 2); r0) }; clone((*r).0))
  -- (8) the other values in flight: a borrow assigned (held while it is checked), a constructor's
  -- fields (held while their types are checked)
  def AssignB (a : Nat) (b : Nat) : Nat := (let r = &a; r := &b; *r := 3; Add(a, b))
  def AssignBRun : Eq(Nat, AssignB(1, 2), 4) := refl
  def CtorF (a : Nat) (b : Nat) : Nat × Nat := (let r = &a; *r := 2; (Add(clone(a), b), a))
}

#guard (run "CallArgs" CallArgs).rejectedWith [
  ("S1", "[Access] reading or writing a ends a borrow that a value in flight holds"),
  ("S2", "[Access] reading or writing a ends a borrow that a value in flight holds"),
  ("S3", "[Call] argument 1 is ⊥ at the call point"),
  ("JE", "[Read] q was moved out or its borrow ended"),
  ("JEU", "[Read] q was moved out or its borrow ended"),
  ("JER", "[Read] q was moved out or its borrow ended")]

/-- Every state at every call depth of `CallArgs`'s rows, private copies included
(`Config.recordDeep`), and its value in flight on an exit: every loan outside a sealed program is
live, its borrow in Ω (D115: before it, a borrow argument was held outside Ω between its call's
`popTemps` and the callee's frame, and its lender's loan read as a loan of an ended borrow). -/
def callArgsLive : Bool :=
  let r := runWith (some Prelude) "CallArgs" CallArgs { recordDeep := true, recordDeepPrivate := true }
  r.rows.all fun row => row.trace.all fun
    | .deep _ fl st =>
      let env := match fl with
        | some (v, T) => st.env.modify (st.env.size - 1) fun fr =>
            { fr with temps := fr.temps.push v, tempTys := fr.tempTys.push T }
        | none => st.env
      (Ochr.allPos env).all fun p => (Ochr.valAt env p).outerLoans.all (Ochr.liveLoan env ·)
    | _ => true

#guard callArgsLive

/-! ## Every name a declaration mentions is declared (D118)

A declaration is rejected before anything runs if any of its terms mentions a constant or an
inductive type that is not declared at that point: not in Σ, which holds only the accepted
declarations before it (an inductive type's own name in its fields aside; a function's own name
in its body is its bound `self`). It is read from syntax and Σ, so it covers code that no run
reaches. Before D118 such a name was looked up only when a run reached it, so in the other arm of
a match on a known constructor (`H4`, `K1`, `K2`, a closure's body `Clo`, a match an outer split
already decided `RS`), in a type whose dead arm is never evaluated (`PT`, `RT`, `IP`, `TP`, `TLv`,
a statement `ES`, an `Id` side `IdS`), in a field type (`Q4`, through a λ), as a `split` target
(`SC`) or as a constant's own name (`SelfC`) it was accepted, while the same name in a live arm was
rejected (`H4L`, `H4U`, `H4Lam`). A name declared later is not declared yet, a constant
(`Later1`) or an inductive type (`LT3`, a match on its constructors; `LT2`, a constructor value,
was rejected before by the declared readings), nor is a rejected declaration (`UsesBad`). The controls with declared names are accepted. -/

ochr Undeclared uses Nats {
  def Known : Nat := 7
  inductive PF (f : Π(x : Nat). Nat) := MkPF
  reject def H4 : Nat := (let z = 0; match z { Z => 0, S n => NoSuchNameD })
  def H4K : Nat := (let z = 0; match z { Z => 0, S n => Known })
  reject def H4L : Nat := (let z = 1; match z { Z => 0, S n => NoSuchNameD })
  reject def H4U (z : Nat) : Nat := match z { Z => 0, S n => NoSuchNameD }
  reject def H4Lam : Nat → Nat := λ(y : Nat) : Nat => NoSuchNameF
  reject inductive Q4 := MkQ4(p : PF(λ(y : Nat) : Nat => (let z = 0; match z { Z => 0, S n => NoSuchNameE })))
  inductive Q4K := MkQ4K(p : PF(λ(y : Nat) : Nat => (let z = 0; match z { Z => 0, S n => Known })))
  reject def K1 : Nat := (let z = 0; match z { Z => 0, S n => NoSuchFn(n) })
  reject def K2 (x : Nat) : Nat := (let z = 0; match z { Z => x, S n => match n { Z => Undeclared1, S _ => 0 } })
  reject def Clo (u : Unit) : Nat → Nat := λ(y : Nat) : Nat => (let z = 0; match z { Z => y, S _ => NoSuchC7 })
  reject def RS (n : Nat) : Nat := match n { Z => match n { Z => 0, S _ => NoSuchR1 }, S _ => 0 }
  def RSK (n : Nat) : Nat := match n { Z => match n { Z => 0, S _ => Known }, S _ => 0 }
  reject def PT (x : (let z = 0; match z { Z => Nat, S _ => NoSuchT1 })) : Nat := 0
  reject def RT (u : Unit) : (let z = 0; match z { Z => Nat, S _ => NoSuchT2 }) := 0
  reject inductive IP (k : (let z = 0; match z { Z => Nat, S _ => NoSuchT3 })) := MkIP
  reject def TP (n : Nat) : Type := match n { Z => Nat, S _ => Π(x : Nat). (let z = 0; match z { Z => Nat, S _ => NoSuchT7 }) }
  def TL (n : Nat) : Type := match n { Z => Nat, S _ => (Nat → Nat) }
  reject def TLv (u : Unit) : TL(1) := λ(x : Nat) : Nat => (let z = 0; match z { Z => x, S _ => NoSuchL1 })
  reject def ES (u : Unit) : Eq(Nat, (let z = 0; match z { Z => 0, S _ => NoSuchE1 }), 0) := refl
  reject def IdS (u : Unit) : Id(Nat, (let z = 0; match z { Z => 0, S _ => NoSuchC5 }), 0) := refl
  def IdSK (u : Unit) : Id(Nat, (let z = 0; match z { Z => 0, S _ => Known }), 0) := refl
  reject def SC (n : Nat) : Eq(Nat, n, n) := (let z = 0; match z { Z => refl, S _ => split NoSuchF in refl })
  reject def SelfC : Nat := (let z = 0; match z { Z => 0, S _ => SelfC })
  def SelfRec (n : Nat) : Nat by n := match n { Z => 0, S m => SelfRec(m) }
  inductive OwnL := ONil | OCons(t : OwnL)
  reject def Later1 (u : Unit) : Nat := (let z = 0; match z { Z => 0, S _ => LaterC })
  def LaterC : Nat := 1
  def Later1K (u : Unit) : Nat := (let z = 0; match z { Z => 0, S _ => LaterC })
  reject def LT2 (u : Unit) : Nat := (let z = 0; match z { Z => 0, S _ => (let q = MkLateT; match q { MkLateT => 0 }) })
  reject def LT3 (y : Nat) : Nat := (let z = 0; match z { Z => 0, S _ => match y { MkLateT => 0 } })
  inductive LateT := MkLateT
  def LT2K (u : Unit) : Nat := (let z = 0; match z { Z => 0, S _ => (let q = MkLateT; match q { MkLateT => 0 }) })
  reject def Bad : Nat := NoSuchAtAll
  reject def UsesBad (u : Unit) : Nat := (let z = 0; match z { Z => 0, S _ => Bad })
  inductive Void0 : Prop
  def NoArms (v : Void0) : Nat := (let x : Nat = match v {}; x)
}

#guard (run "Undeclared" Undeclared).rejectedWith [
  ("H4", "unknown constant NoSuchNameD"), ("H4L", "unknown constant NoSuchNameD"),
  ("H4U", "unknown constant NoSuchNameD"), ("H4Lam", "unknown constant NoSuchNameF"),
  ("Q4", "unknown constant NoSuchNameE"), ("K1", "unknown constant NoSuchFn"),
  ("K2", "unknown constant Undeclared1"), ("Clo", "unknown constant NoSuchC7"),
  ("RS", "unknown constant NoSuchR1"), ("PT", "unknown constant NoSuchT1"),
  ("RT", "unknown constant NoSuchT2"), ("IP", "unknown constant NoSuchT3"),
  ("TP", "unknown constant NoSuchT7"), ("TLv", "unknown constant NoSuchL1"),
  ("ES", "unknown constant NoSuchE1"), ("IdS", "unknown constant NoSuchC5"),
  ("SC", "unknown constant NoSuchF"), ("SelfC", "unknown constant SelfC"),
  ("Later1", "unknown constant LaterC"), ("LT2", "unknown inductive type LateT"),
  ("LT3", "unknown inductive type LateT"),
  ("Bad", "unknown constant NoSuchAtAll"), ("UsesBad", "unknown constant Bad")]

/-! ## An inductive type's own name stands in its fields only (D133)

D118's check that a declaration names only declared things let an inductive declaration's own
name through in its parameters' types as well as in its fields: `Q6`, with its own name in a dead
arm of a parameter's type, was accepted. The type does not exist while its parameters are
checked, so since D133 its name is not declared there. Each position, rejected: a dead arm, bare
and applied, under a `let`, in an earlier parameter's type, inside a `Π`, a type function's
argument, an equation, a box. Written live, the name was rejected before for its arity (`QD`,
`QDa`, `QPD`), or, applied to all its parameters, made the checker run away (`Q3`, `Q3b`:
evaluating `Q3(A, n, n)` checked its arguments against `Q3`'s parameter types, among them
`Q3(A, n, n)` again; fuel bounded the depth, but every level kept a copy of the state, and the run
exhausted the machine's memory first); the name check runs before anything is evaluated, so each
is now rejected at once. The own name in the fields stays (`QF`, `QFB`), as does another type's in
a parameter's type (`QO`); another undeclared name keeps D118's message (`QU`). -/

ochr OwnName uses Boxes {
  def TFid (A : Type) : Type := A
  reject inductive Q6 (A : Type) (x : (let z = Z; match z { Z => A, S(k) => Q6 })) := MkQ6
  reject inductive Q6a (A : Type) (x : (let z = Z; match z { Z => A, S(k) => Q6a(A, A) })) := MkQ6a
  reject inductive QL (A : Type) (x : (let z = Z; let T = match z { Z => A, S(k) => QL }; T)) := MkQL
  reject inductive QE (x : (let z = Z; match z { Z => Nat, S(k) => QE })) (B : Type) := MkQE
  reject inductive QP (f : Π(y : (let z = Z; match z { Z => Nat, S(k) => QP })). Nat) := MkQP
  reject inductive QT (x : (let z = Z; match z { Z => Nat, S(k) => TFid(QT) })) := MkQT
  reject inductive QQ (h : Eq(Type, Nat, (let z = Z; match z { Z => Nat, S(k) => QQ }))) := MkQQ
  reject inductive QBx (x : (let z = Z; match z { Z => Nat, S(k) => Box(QBx) })) := MkQBx
  reject inductive QD (x : QD) := MkQD
  reject inductive QDa (A : Type) (x : QDa(A)) := MkQDa
  reject inductive QPD (A : Type) (x : Box(QPD(A))) := MkQPD
  reject inductive Q3 (A : Type) (n : Nat) (x : Q3(A, n, n)) := MkQ3
  reject inductive Q3b (A : Type) (x : Q3b(A, A)) := MkQ3b
  inductive QF (A : Type) := QN | QC(x : QF(A))
  inductive QFB (A : Type) := QFBN | QFBC(x : Box(QFB(A)))
  inductive QO (x : (let z = Z; match z { Z => Nat, S(k) => Box(Nat) })) := MkQO
  reject inductive QU (x : (let z = Z; match z { Z => Nat, S(k) => NoSuchQ })) := MkQU
}

#guard (run "OwnName" OwnName).rejectedWith
  ((["Q6", "Q6a", "QL", "QE", "QP", "QT", "QQ", "QBx", "QD", "QDa", "QPD", "Q3", "Q3b"].map fun n =>
    (n, s!"[D133] {n} is not declared in its own parameters' types: an inductive type's own name may stand in its fields only")) ++
   [("QU", "unknown constant NoSuchQ")])
