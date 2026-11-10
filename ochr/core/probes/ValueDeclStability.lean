import Ochr.Test
open Ochr.Test

/-!
# Probe: can `valueDecl (.abs σ)` flip a decision between the generic call and an instance?

`Decide.valueDecl (.abs σ)` reads `valTypeDecl (absType σ)`, the *stored* Δ type, which [Split]'s
refinement rewrites (`mapState` with types). A stuck type-function call `⌈F(σn)⌉` reads `.other`
(sealed, its head's codomain not `Prop`), and once `n` splits, a Π-type reads `.pi r`. So a
decision that consumed that reading as a Π, such as a call through σ (its erasure class) or a
Π-type whose sort or class reads σ's capture, could differ. Every such consumer is rejected while
the type is stuck ("not a function type"), and accepted once a split has made it concrete, after
which refinement keeps the head. Run: `lake env lean ochr/core/probes/ValueDeclStability.lean`
from `ochr/core/lean`. It elaborates without errors when every verdict is as written.
-/

ochr ValueDeclStability {
  def F (n : Nat) : Type₁ := match n { Z => Π(x : Nat). Prop, S m => Π(x : Nat). Prop }
  def RF (n : Nat) : Type₁ := match n { Z => Π(x : &Nat). Prop, S m => Π(x : &Nat). Prop }
  -- calls once a split has made the type concrete: accepted
  def K (n : Nat) (f : F(n)) : Prop := match n { Z => f(0), S m => f(1) }
  def L (n : Nat) (f : F(n)) : Prop := K(n, f)
  def M (f : F(0)) : Prop := L(0, f)
  def P2s (n : Nat) (f : RF(n)) (y : Nat) : Nat :=
    (let r = &y; let q = match n { Z => f(r), S m => f(r) }; y)
  -- the type concrete from the start (flipped control): accepted
  def P2c (b : Nat) (f : RF(0)) (y : Nat) : Nat :=
    (let r = &y; let q = match b { Z => f(r), S m => f(r) }; y)
  -- a call through a stuck-typed σ, inside a stuck block on another scrutinee: rejected
  reject def P2 (n : Nat) (b : Nat) (f : RF(n)) (y : Nat) : Nat :=
    (let r = &y; let q = match b { Z => f(r), S m => f(r) }; y)
  -- the same through a let-bound copy (whose reading `declOf` gives): rejected
  reject def P2l (n : Nat) (b : Nat) (f : RF(n)) (y : Nat) : Nat :=
    (let g = f; let r = &y; let q = g(r); y)
  -- a Π-type (and a closure into it, with a write erasure would undo) whose sort and class read
  -- the stuck-typed capture `g`: rejected at formation
  reject def T1 (n : Nat) (g : F(n)) : Type₁ := Π(x : Nat). g(x)
  reject def T2 (n : Nat) (g : F(n)) (y : Nat) : Nat :=
    (let h = (λ(x : &Nat) : g(0) => (*x := 5; ?)); let r = &y; let u = h(r); y)
  -- flipped control for T1: split first, then form: accepted
  def T1s (n : Nat) (g : F(n)) : Prop := match n { Z => Π(x : Nat). g(x), S m => Π(x : Nat). g(x) }
}
