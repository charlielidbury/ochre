#import "../style.typ": *

This section introduces Ochr through its running examples. Everything is informal here; @sec-calculus onwards makes it precise.

== Imperative code is evaluated inside types

Ochr programs are made of definitions with parameters and a body. Borrow types `&T` are Rust's mutable references; places are variables `x`, dereferences `*p` and the predecessor field `p.1` of a number. A `match` on a place binds its pattern variable to a _sub-place_, not a copy, so in `match *x { Z => … | S p => … }` the name `p` stands for the field `(*x).1` and `&p` reborrows it.

`Add` wraps `AddM` behind a pure interface. It owns its first argument, lends it to `AddM`, and returns it:

```
Add(x : Nat, y : Nat) : Nat := AddM(&x, y); x
```

Because definitional equality is evaluation, `Id Nat (Add(2, 3)) 5` holds by `refl`: the checker runs `Add(2, 3)`, which runs `AddM` in place on a local copy, and compares the result with `5`. There is nothing special about imperative code here, and nothing special about `Add` being "pure": it is simply a program whose observable output is its result.

The machine that does this is the symbolic semantics of Aeneas's low-level borrow calculus @aeneas. An environment Ω maps variables to values; borrowing `x` moves its content into the borrow and leaves a _loan_ behind; ending the borrow moves the content back. Running `Add(2, 3)` passes through these states:

```
{ x ↦ 2 }                                     // enter Add
{ x ↦ loan₀ } ⊢ AddM(borrow₀ 2, 3)            // &x: the content moves into the borrow
{ x ↦ loan₀ | x' ↦ borrow₀ (S loan₁), … }     // AddM matched S and reborrowed the field
…
{ x ↦ 5 }                                     // borrows ended, contents returned
```

== Symbolic inputs, and what a stuck call leaves behind

To reason about all numbers at once, the checker runs programs on _abstract values_ `σ`, which play the role of Lean's free variables. Running `Add(σ, 0)` borrows `x ↦ σ` and calls `AddM(borrow₀ σ, 0)`, whose body immediately gets stuck: it must match on `σ`.

In a pure type theory a stuck term is its own normal form. Here the call has also produced something that lives in the environment, namely the final content of the place it borrowed, and that content needs a name. We _close off_ the call: the call returns, and the loan it held is filled with a _sealed program_, a closed source program that owns its state and computes that content:

```
{ x ↦ loan₀ } ⊢ AddM(borrow₀ σ, 0)
   ⟶  { x ↦ ⌈let c = σ; AddM(&c, 0); c⌉ } ⊢ ()
```

Write `N(σ)` for #seal(`let c = σ; AddM(&c, 0); c`). It is a neutral value, like a stuck `Nat.rec` in Lean, and it is literally the body of `Add(σ, 0)`: the sealed program _is_ the pure wrapper, generated on demand. It is also exactly the value that Aeneas's backward function for `AddM` would compute @aeneas, written without leaving the source language. When a later case split refines `σ` to `S σ'`, `N(S σ')` runs again, now makes progress through one successor, closes off the inner recursive call, and normalises to `S N(σ')`.

== Equality between computations

The type `Id Unit (AddM(x, 0)) ()` compares two computations. It is evaluated at the environment where it is formed. Each side runs on its own copy of that environment; the result and the final contents of the places the side may write form its _observation_; and `Id` computes to ordinary equality between the two observations. For a definition taking `x : &Nat`, the checker works at the definition's _generic call_ `AddMZero(&c)` from `{ c ↦ σ }`, so the place that may be written is `c`, the owner of `x`'s loan:

```
⟦AddM(x, 0)⟧  =  ((), N(σ))          // the call is stuck, so c receives the sealed program
⟦()⟧          =  ((), σ)             // nothing happens; ending x's borrow returns σ to c

Id Unit (AddM(x, 0)) ()  ≡  Eq (Unit × Nat) ((), N(σ)) ((), σ)  ≡  Eq Nat N(σ) σ
```

The last step uses the observational computation rules for equality @ott: equality of pairs is a conjunction, reflexive equations are `⊤`, and `⊤` is a unit for `∧`. The statement "running `AddM(x, 0)` has no effect" has become the ordinary proposition that `N(σ)` equals `σ`.

== The environment performs the congruence

Now the proof:

```
AddMZero(x : &Nat) : Id Unit (AddM(x, 0)) () :=
  match *x { Z => refl | S p => AddMZero(&p) }
```

The match on `*x` splits on `σ`. In the `Z` branch the goal is `Eq Nat N(Z) Z`; `N(Z)` runs to `Z`, the equation is reflexive and so `⊤`, and `refl` proves it. In the `S` branch the goal is `Eq Nat N(S σ') (S σ')`, which normalises to `Eq Nat (S N(σ')) (S σ')`.

The recursive call is checked by the same rule that produced the goal: the callee's statement is evaluated at the call site, with its parameter bound to the argument. At the call site the environment is

```
{ c ↦ loan₀ | x ↦ borrow₀ (S loan₁) }   and the argument is   borrow₁ σ'
```

because matching `S p` through the borrow and taking `&p` leaves the successor in place, around a loan for the predecessor. The owner of the argument's loan is found by following it outwards: `loan₁` sits inside `x`'s borrow, whose loan sits in `c`. So the recursive call's statement observes `c`, and running `AddM` on the argument fills `loan₁` with `N(σ')`, after which `c` holds `S N(σ')`:

```
⟦AddM(x', 0)⟧ at the call site  =  ((), S N(σ'))
⟦()⟧          at the call site  =  ((), S σ')
AddMZero(&p) : Eq Nat (S N(σ')) (S σ')
```

This is the goal, symbol for symbol. The successor that a pure proof would add with `cong S` was supplied by the environment. The recursive call is a proof, and proofs are erased at runtime, so the checker does not run it: its borrow argument is returned unchanged.

For comparison, here is the same theorem about the pure wrapper:

```
AddZero(x : Nat) : Id Nat (Add(x, 0)) x :=
  match x { Z => refl | S p => cong S (AddZero(p)) }
```

`Add(x, 0)` writes nothing outside itself, so its observation is just its result, and the goal is again `Eq Nat N(σ) σ`, the very proposition `AddMZero`'s statement computed to. The induction hypothesis `AddZero(p)` is about a fresh copy of the predecessor, so the successor must be added by hand. In Ochr the in-place proof is the shorter one. The two theorems are also interchangeable: `AddZero(x) := AddMZero(&x)` type-checks, because both statements normalise to the same proposition.

== Returning a borrow

A more idiomatic in-place addition first finds the final node and then writes through it:

```
TailM(x : &Nat) : &Nat := match *x { Z => x | S p => TailM(&p) }
AddM'(x : &Nat, y : Nat) : Unit := let t = TailM(x); *t := y
```

`TailM` returns a borrow into its argument. When it is stuck on `σ`, the place it borrowed cannot be given its final content yet, because that depends on what the caller will later write through the returned borrow. Closing off such a call returns a borrow of a fresh `k` and fills the argument's loan with a sealed program that has a _hole_ `loan_k` for the returned borrow's final content:

```
{ c ↦ loan₀ } ⊢ TailM(borrow₀ σ)
   ⟶  { c ↦ ⌈let c = σ; let r = TailM(&c); *r := loan_k; c⌉ } ⊢ borrow_k ⌈let c = σ; let r = TailM(&c); *r⌉
```

In `AddM'`, the caller writes `y` through `t` and drops it; ending `borrow_k` substitutes the final content `y` for the hole. What remains in `c` is #seal(`let c = σ; let r = TailM(&c); *r := y; c`): the effect of `AddM'`, as a program. The hole is the neutral form of an Aeneas region abstraction, and of a RustHorn prophecy @rusthorn: it records only the _final_ value written through the returned borrow.

The equivalence of the two additions is proved by the same bare recursion:

```
AddMEq(x : &Nat, y : Nat) : Id Unit (AddM(x, y)) (AddM'(x, y)) :=
  match *x { Z => refl | S p => AddMEq(&p, y) }
```

In the successor branch, re-running `AddM'`'s sealed program on `S σ'` unfolds `TailM` once, closes off its inner call with a fresh hole, and the pending write `*r := y` then fills that hole; on the other side the recursive call's statement, evaluated at the call site, performs the same steps through the caller's borrow. Both sides arrive at `Eq Nat (S A(σ', y)) (S B(σ', y))`, where `A` and `B` are the sealed programs for the two additions on the predecessor. The theorem for an owned number follows by lending it: `AddMEqOwned(x : Nat) : Id Unit (AddM(&x, 0)) (AddM'(&x, 0)) := AddMEq(&x, 0)`.

== Proofs about the current state

Dependent types are not only for stating theorems after the fact. A function can demand, as an argument, a proof about the _current_ contents of a borrow. Here is in-place subtraction, which is total only when the subtrahend is no larger than the number:

```
Le(a : Nat, b : Nat) : Prop by a :=
  match a { Z => ⊤ | S a' => match b { Z => Eq Nat Z (S Z) | S b' => Le(a', b') } }

SubM(x : &Nat, y : Nat, h : Le(y, *x)) : Unit by y :=
  match y { Z => () | S q => match *x { Z => () | S p => *x := p; SubM(x, q, h) } }
```

The type of `h` mentions `*x`, the content of the borrow at the moment of the call. Inside `SubM`, after `*x := p` has overwritten that content, the recursive call needs a proof of `Le(q, *x)` about the _new_ content; the old hypothesis `h`, of type `Le(S q, S p)`, provides it, because that type was formed when `h` was bound and normalises to `Le(q, p)`.

Now a caller that first adds and then subtracts:

```
LeAdd(n : Nat, m : Nat) : Le(n, Add(n, m)) by n := match n { Z => refl | S n' => LeAdd(n', m) }

AddSub(x : &Nat, y : Nat) : Unit := let old = *x; AddM(&*x, y); SubM(x, old, LeAdd(old, y))
```

At the call to `SubM`, `*x` has just been mutated in place by `AddM`, so on symbolic input it holds the sealed program `N(σ, y) = ⌈let c = σ; AddM(&c, y); c⌉`, and `SubM` demands a proof of `Le(σ, N(σ, y))`. The lemma `LeAdd` is about the _pure_ `Add` of the snapshot `old`, and its type is `Le(σ, Add(σ, y))`. The two meet because `Add(σ, y)` normalises to the very same sealed program: the in-place computation and the pure one are the same program to the type checker. A proof about the pure function is accepted where a proof about the mutated state is required, with no bridging lemma. Using the snapshot after further mutation, `…; AddM(&*x, y); *x := Z; SubM(x, old, LeAdd(old, y))`, is rejected, since the requirement then mentions `Z`.

Finally, a theorem about the whole: adding `y` and then subtracting the old value leaves exactly `y`.

```
AddSubId(x : &Nat, y : Nat) : Id Unit (AddSub(x, y)) (*x := y) by x :=
  match *x { Z => refl | S p => let c = p; AddSubId(&c, y) }
```

Here the successor case copies the predecessor into a fresh place `c` instead of borrowing it in place. Borrowing would supply the surrounding `S` to the induction hypothesis, as in `AddMZero`, and the goal has no `S` to match: `AddSub` peels the successor off. Borrowing supplies the congruence and copying withholds it, and the programmer chooses.

== Branching

A `match` on an abstract value in the middle of a function cannot pick an arm. Each arm is checked separately, and the rest of the function is then checked once, from the state in which the match itself has been closed off like a call. This covers borrows whose origin depends on the branch:

```
AddToOne(b : Nat, x₁ : &Nat, x₂ : &Nat, y : Nat) : Unit :=
  let r = match b { Z => x₁ | S _ => x₂ }; AddM(r, y)
```

The closed-off match returns a borrow with a hole that appears in the sealed programs for both `x₁`'s and `x₂`'s places; whichever the match would have chosen receives the final content. A proof about `AddToOne` splits on `b`, after which the sealed programs run and the goal becomes a statement about `AddM` alone.
