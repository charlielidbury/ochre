import Ochr.Examples.«00Std»

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

ochr Functions uses Std, Fixtures {
  -- ## Opaque functions
  -- `f` has no borrow argument, so it cannot write anything: its calls return `()` and
  -- `Twice(f)` does nothing.
  def Twice (f : Π(_ : Unit). Unit) : Unit := (
    f(());
    f(())
  )

  def TwiceNoop (f : Π(_ : Unit). Unit) : Id Unit (Twice(f)) () := refl

  -- With a borrow argument, `f` may write, and what it leaves is a sealed program. Moving
  -- `x` into the second call instead of reborrowing it makes no difference.
  def TwiceM (f : Π(_ : &Nat). Unit) (x : &Nat) : Unit := (
    f(&*x);
    f(&*x)
  )

  def TwiceMMove (f : Π(_ : &Nat). Unit) (x : &Nat) : Id Unit (TwiceM(f, x)) (f(&*x); f(x)) := refl

  -- Instantiated with a function that adds zero, `TwiceM` does nothing, by induction ...
  def TwiceMZero (x : &Nat) : Id Unit (TwiceM(λ(z : &Nat) : Unit => AddM(z, 0), x)) () by x := (
    match *x {
      Z => refl,
      S p => TwiceMZero(&p),
    }
  )

  -- ... or by citing the lemma twice. A cited lemma runs on a private copy, so it leaves `*x`
  -- alone; `J` composes the two instances. `Add(s, 0)` closes off into the same sealed program
  -- as `AddM(&*x, 0)`.
  def TwiceMZero' (x : &Nat) : Id Unit (TwiceM(λ(z : &Nat) : Unit => AddM(z, 0), x)) () := (
    let s = *x;
    let h1 = AddMZero(&*x);
    AddM(&*x, 0);
    let h2 = AddMZero(&*x);
    J(Nat, Add(s, 0), s, λ(z : Nat) : Prop => Id Nat (Add(Add(s, 0), 0)) z, h1, h2)
  )

  -- `A → B` is a Π-type with an unnamed parameter.
  def ApplyArrow (f : Nat → Nat) (n : Nat) : Nat := f(n)

  -- ## Comparing functions
  -- Functions are compared by what their generic calls do, not by their code.
  def Conv : Eq (Π(x : &Nat). Unit) (λ(x : &Nat) : Unit => ()) (λ(x : &Nat) : Unit => (let y = 0; ())) := refl

  def ConvW :
      Eq (Π(x : &Nat). Unit)
        (λ(x : &Nat) : Unit => *x := S *x)
        (λ(x : &Nat) : Unit => (let y = S *x; *x := y)) := (
    refl
  )

  -- A closure that captures a variable has a closed Π-type ...
  def Apply (f : Π(n : Nat). Nat) (n : Nat) : Nat := f(n)
  def Cap (m : Nat) : Nat := Apply(λ(n : Nat) : Nat => Add(n, clone(m)), 0)
  def CapEq (m : Nat) : Id Nat (Apply(λ(n : Nat) : Nat => Add(n, m), 0)) (Add(0, m)) := refl

  -- A closure is stored in data only through a type parameter, as in `Box(Π(n : Nat). Nat)`
  -- (paper §4.3), and one returning a borrow too (the model's `Box(Π(y : &Nat). &Nat)`) ...
  def BoxFn : Box(Π(n : Nat). Nat) := MkBox(λ(n : Nat) : Nat => n)
  def UseBoxFn (b : Box(Π(n : Nat). Nat)) : Nat := match b { MkBox(f) => f(0) }
  def UseBoxFnIs : Id Nat (UseBoxFn(MkBox(λ(n : Nat) : Nat => S n))) 1 := refl
  def BoxBorrowFn (b : Box(Π(y : &Nat). &Nat)) (x : &Nat) : Unit := match b { MkBox(g) => (let r = g(x); *r := 0) }

  -- ... never as a field of its own (fields are first-order, D36).
  reject inductive FnBox := MkFnBox(f : Π(n : Nat). Nat)

  -- ... type abbreviations unfold under binders ...
  def Pow (X : Type) : Type₁ := Π(a : X). Prop
  def P1 : Pow(Nat) := λ(a : Nat) : Prop => ⊤
  def UseP (p : Pow(Nat)) : Prop := p(0)
  def P3 (u : Unit) : Prop := UseP(λ(a : Nat) : Prop => ⊤)

  -- ... and lemma statements are compared by what they compute to, under their binders.
  def ZeroAdd (n : Nat) : Id Nat (Add(0, n)) n := refl
  def UseRefl (h : Π(n : Nat). Id Nat n n) : Unit := ()
  def PassZeroAdd (u : Unit) : Unit := UseRefl(ZeroAdd)

  -- Under a borrow binder, one generic place serves both sides.
  def UseA (h : Π(x : &Nat). Id Unit (AddM(x, 0)) ()) : Unit := ()
  def PassA (h : Π(y : &Nat). Id Unit (let t = 0; AddM(y, t)) ()) : Unit := UseA(h)

  -- Statements that differ at the generic arguments stay different.
  reject def PassStuck (h : Π(n : Nat). Id Nat (Add(n, 0)) n) : Unit := UseRefl(h)
  reject def PassWrong (h : Π(n : Nat). Id Nat n 0) : Unit := UseRefl(h)
  def UseW (h : Π(x : &Nat). Id Unit (*x := 0) (*x := 0)) : Unit := ()
  reject def PassW (h : Π(x : &Nat). Id Unit (*x := 0) (*x := 1)) : Unit := UseW(h)
  reject def PassDom (f : Π(n : Unit). Nat) : Nat := Apply(f, 0)

  -- Two functions returning a borrow into different arguments ...
  def PickX (x : &Nat) (y : &Nat) : &Nat := x
  def PickY (x : &Nat) (y : &Nat) : &Nat := y

  -- ... and a property that tells them apart: writing through the result changes `*x`.
  def Q (h : Π(x : &Nat) (y : &Nat). &Nat) : Prop := (
    Π(x : &Nat) (y : &Nat). Id Unit (let r = h(x, y); *r := S Z) (*x := S Z)
  )

  def TX : Q(PickX) := (
    let h = PickX;
    λ(x : &Nat) (y : &Nat) : Id Unit (let r = h(x, y); *r := S Z) (*x := S Z) => refl
  )

  -- ## What goes wrong without these rules
  -- Compared by their results only (switch `closureConv`), `λx. ()` and `λx. (*x := 1)` would
  -- be equal, and `J` along that equation would prove `1 = 0` (D30).
  def P (h : Π(x : &Nat). Unit) : Prop := Id Nat (let c = Z; h(&c); c) Z

  reject def Boom3 : Eq Nat (S Z) Z := (
    J(Π(x : &Nat). Unit, λ(x : &Nat) : Unit => (), λ(x : &Nat) : Unit => *x := S Z, P, refl, refl)
  )

  -- Equality of functions is the least relation closed under the rules: two closures that
  -- are stuck at their generic calls are not identified. Read coinductively, these two would
  -- be equal, and `J` would prove `1 = 0`.
  reject def CoInd :
      Eq (Π(x : &Nat). Unit)
        (λ(x : &Nat) : Unit => match *x { Z => (), S _ => *x := Z })
        (λ(x : &Nat) : Unit => match *x { Z => *x := S Z, S _ => () }) := (
    refl
  )

  -- Observing a returned borrow only through its current contents (switch `obsBorrow`) would
  -- identify `PickX` and `PickY`, since neither writes anything, and transport would prove
  -- `0 = 1 ∧ 1 = 0` (D38).
  reject def ConvPick : Eq (Π(x : &Nat) (y : &Nat). &Nat) PickX PickY := refl
  reject def TY : Q(PickY) := J(Π(x : &Nat) (y : &Nat). &Nat, PickX, PickY, Q, refl, TX)

  reject def BoomX4 : Eq Nat 0 1 ∧ Eq Nat 1 0 := (
    let c = Z;
    let d = Z;
    TY(&c, &d)
  )

  -- A function's erasure class and [Close] row are part of its type (D54). `H` returns a
  -- `P0`, which is `Prop` but not written as a sort, so `H` returns data and its calls run,
  -- while calls of a `Π(x : &Nat). Prop` return types and are erased. Were the two types
  -- convertible (switch `classInType`), `RunGGen`'s generic call would erase `g(&c)` and its
  -- instance at `H` would run it, and `Boom` would be a closed proof of `False`, as would
  -- `BoomI` through an identity function.
  def P0 : Type₁ := Prop

  def H (x : &Nat) : P0 := (
    *x := S Z;
    ⊤
  )

  def RunG (f : Π(x : &Nat). Prop) : Nat := (
    let c = Z;
    let g = f;
    g(&c);
    c
  )

  def RunGGen (f : Π(x : &Nat). Prop) : Id Nat (RunG(f)) Z := refl
  reject def Boom : False := RunGGen(H)
  reject def RunGH : Id Nat (RunG(H)) 1 := refl

  def IdF (f : Π(x : &Nat). Prop) : (Π(x : &Nat). Prop) := f

  def RunI (f : Π(x : &Nat). Prop) : Nat := (
    let c = Z;
    IdF(f)(&c);
    c
  )

  def RunIGen (f : Π(x : &Nat). Prop) : Id Nat (RunI(f)) Z := refl
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

  def RunPowGen (p : RefPred(0)) : Id Nat (RunPow(p)) Z := refl
  reject def BoomPow : False := RunPowGen(H)

  -- The same for the class "returns proofs", with a codomain `V(Z)` that computes to `⊤`.
  -- D54 alone rejects `BoomP` at the argument; since D55 the codomain cannot even be written
  -- (`V(Z)`'s declared type `U(Z)` is not a sort).
  def RunP (f : Π(x : &Nat). ⊤) : Nat := (
    let c = Z;
    let g = f;
    g(&c);
    c
  )

  def RunPGen (f : Π(x : &Nat). ⊤) : Id Nat (RunP(f)) Z := refl
  reject def WV (u : Unit) : V(Z) := refl
  reject def BoomP : False := RunPGen(λ(x : &Nat) : V(Z) => (*x := S Z; WV(())))

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
    *x := S Z;
    ()
  )

  def RunU (f : Π(x : &Nat). Unit) (n : Nat) : Id Unit (let c = n; f(&c)) () := refl
  def RunUH (n : Nat) : ⊤ := RunU(H2, n)
}

-- the exact number of declarations (a truncated file changes it)
#guard Functions.decls.length == 63
