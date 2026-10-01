import Ochr.Examples.«00Std»
open Ochr Ochr.Test

set_option ochr.uninitTypes true in
ochr UninitLib uses Std {
  untagged inductive Uninit (E : Type) := Empty | Full(x : E)
  def Init (E : Type) (u : Uninit(E)) : Prop := (
    match u {
      Empty => False,
      Full(x) => ⊤,
    }
  )
  def UGet (E : Type) (u : &Uninit(E)) (h : Init(E, *u)) : &E := (
    match *u {
      Full(x) => &x,
      Empty => match h {},
    }
  )
  def UTake (E : Type) (u : &Uninit(E)) (h : Init(E, *u)) : E := (
    let y = *u;
    *u := Empty;
    match y {
      Full(x) => x,
      Empty => match h {},
    }
  )
  def UWrite (E : Type) (u : &Uninit(E)) (x : E) : Unit := *u := Full(x)
  -- no tag: a runtime match with two live arms is refused
  reject def IsFull (E : Type) (u : &Uninit(E)) : Bool := (
    match *u {
      Full(x) => true,
      Empty => false,
    }
  )
  -- in a statement it is fine
  def InitDec (E : Type) (u : Uninit(E)) : Prop := (
    match u {
      Full(x) => ⊤,
      Empty => ⊤,
    }
  )
  -- a known value needs `refl` for its hypothesis
  def KnownFull (x : Word) : Word := (
    let u = Full(x);
    let h : Init(Word, u) = refl;
    match u {
      Full(y) => y,
      Empty => match h {},
    }
  )
  reject def KnownEmpty (x : Word) : Word := (
    let u : Uninit(Word) = Empty;
    let h : Init(Word, u) = refl;
    match u {
      Full(y) => y,
      Empty => match h {},
    }
  )
  -- Uninit(Word) is a copy type, Uninit(Nat) is not
  def CopyW (u : Uninit(Word)) : Uninit(Word) × Uninit(Word) := (u, u)
  reject def CopyN (u : Uninit(Nat)) : Uninit(Nat) × Uninit(Nat) := (u, u)
  -- taking and writing back
  def TakeThenWrite (u : &Uninit(Nat)) (h : Init(Nat, *u)) : Unit := (
    let x = UTake(Nat, &*u, h);
    UWrite(Nat, u, S(x))
  )
  def TakeRun : Id(Uninit(Nat), (let c = Full(3); let h : Init(Nat, c) = refl; TakeThenWrite(&c, h); c), Full(4)) := refl
  def GetRun : Id(Uninit(Nat), (let c = Full(3); let h : Init(Nat, c) = refl; let r = UGet(Nat, &c, h); *r := 7; c), Full(7)) := refl
  -- an equation over the empty value computes
  def EmptyEq (E : Type) : Eq(Uninit(E), Empty[E], Empty[E]) := refl
  reject def EmptyFull (E : Type) (x : E) : Eq(Uninit(E), Empty[E], Full(x)) := refl
  def EmptyFullNeg (E : Type) (x : E) (e : Eq(Uninit(E), Empty[E], Full(x))) : False := match e {}
}
#eval (run "UninitLib" UninitLib { uninitTypes := true }).rows.map fun r => (r.name, r.expectAccept == r.verdict.ok, match r.verdict with | .accepted => "" | .rejected m _ => m)
