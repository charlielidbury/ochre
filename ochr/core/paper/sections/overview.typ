#import "../style.typ": *

This section introduces Ochr through its running examples. Everything is informal here; @sec-calculus onwards makes it precise.

== Imperative code is evaluated inside types

Ochr programs are made of definitions with parameters and a body. Borrow types `&T` are Rust's mutable references; places are variables `x`, dereferences `*p` and the predecessor field `p.1` of a number. A `match` on a place binds its pattern variable to a _sub-place_, not a copy, so in `match *x { Z => …, S p => … }` the name `p` stands for the field `(*x).1` and `&p` reborrows it.

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

Write `N(σ)` for #seal(`let c = σ; AddM(&c, 0); c`). It is a neutral value, like a stuck `Nat.rec` in Lean, and it is literally the body of `Add(σ, 0)`: the sealed program _is_ the pure wrapper, generated on demand. It computes what Aeneas's backward function for `AddM` computes @aeneas, without leaving the source language (@sec-eval says for which fragment). When a later case split refines `σ` to `S σ'`, `N(S σ')` runs again, now makes progress through one successor, closes off the inner recursive call, and normalises to `S N(σ')`.

== Equality between computations

The type `Id Unit (AddM(x, 0)) ()` compares two computations. It is evaluated at the environment where it is formed. Each side runs on its own copy of that environment; the result and the final contents of the places the side may write form its _observation_; and `Id` computes to ordinary equality between the two observations. For a definition taking `x : &Nat`, the checker works at the definition's _generic call_ `AddMZero(&c)` from `{ c ↦ σ }`, so the place that may be written is `c`, the owner of `x`'s loan:

```
⟦AddM(x, 0)⟧  =  ((), N(σ))          // the call is stuck, so c receives the sealed program
⟦()⟧          =  ((), σ)             // nothing happens; ending x's borrow returns σ to c

Id Unit (AddM(x, 0)) ()  ≡  Eq Unit () () ∧ Eq Nat N(σ) σ  ≡  Eq Nat N(σ) σ
```

`Id` is a conjunction of equations, one between the results and one for each place written; a reflexive equation is `⊤`, and `⊤` is a unit for `∧`. Here `⊤` and `∧` are not primitives: they are `True` and `And`, ordinary inductive declarations in `Prop`, and `refl` is `True`'s constructor. The statement "running `AddM(x, 0)` has no effect" has become the ordinary proposition that `N(σ)` equals `σ`.

== Induction hypotheses at the call site

Now the proof:

```
AddMZero(x : &Nat) : Id Unit (AddM(x, 0)) () by x :=
  match *x { Z => refl, S p => AddMZero(&p) }
```

The match on `*x` splits on `σ`. In the `Z` branch the goal is `Eq Nat N(Z) Z`; `N(Z)` runs to `Z`, the equation is reflexive and so `⊤`, and `refl` proves it. In the `S` branch the goal is `Eq Nat N(S σ') (S σ')`, which normalises to `Eq Nat (S N(σ')) (S σ')`, and then, since `Eq` takes apart two successors, to `Eq Nat N(σ') σ'`.

The recursive call is checked by the same rule that produced the goal: the callee's statement is evaluated at the call site, with its parameter bound to the argument. At the call site the environment is

```
{ c ↦ loan₀ | x ↦ borrow₀ (S loan₁) }   and the argument is   borrow₁ σ'
```

because matching `S p` through the borrow and taking `&p` leaves the successor in place, around a loan for the predecessor. The owner of the argument's loan is found by following it outwards: `loan₁` sits inside `x`'s borrow, whose loan sits in `c`. So the recursive call's statement observes `c`, and running `AddM` on the argument fills `loan₁` with `N(σ')`, after which `c` holds `S N(σ')`:

```
⟦AddM(x', 0)⟧ at the call site  =  ((), S N(σ'))
⟦()⟧          at the call site  =  ((), S σ')
AddMZero(&p) : Eq Nat (S N(σ')) (S σ')  ≡  Eq Nat N(σ') σ'
```

This is the goal. The callee's statement is about the place it borrowed; evaluated at the call site, it is about the caller's number, successor included. Relating the two is the frame argument that a proof about a translated program makes by hand, and here it was done by evaluation. The recursive call is a proof, and proofs are erased at runtime, so the checker does not run it: its borrow argument is returned unchanged.

The same theorem about the pure wrapper, `AddZero(x : Nat) : Id Nat (Add(x, 0)) x`, has the same goal, since `Add(x, 0)` writes nothing outside itself. It is proved by lending the predecessor field of the owned `x` to the in-place lemma, or by recursion on a copy of it; indeed `AddZero(x) := AddMZero(&x)` type-checks, because both statements normalise to the same proposition. Neither proof mentions a model of `AddM`: the statement is about the program itself.

== Returning a borrow

A more idiomatic in-place addition first finds the final node and then writes through it:

```
TailM(x : &Nat) : &Nat by x := match *x { Z => x, S p => TailM(&p) }
AddM'(x : &Nat, y : Nat) : Unit := let t = TailM(x); *t := y
```

`TailM` returns a borrow into its argument. When it is stuck on `σ`, the place it borrowed cannot be given its final content yet, because that depends on what the caller will later write through the returned borrow. Closing off such a call returns a borrow of a fresh `k` and fills the argument's loan with a sealed program that has a _hole_ `loan_k` for the returned borrow's final content:

```
{ c ↦ loan₀ } ⊢ TailM(borrow₀ σ)
   ⟶  { c ↦ ⌈let c = σ; let r = TailM(&c); *r := loan_k; c⌉ }
      ⊢ borrow_k ⌈let c = σ; let r = TailM(&c); *r⌉
```

In `AddM'`, the caller writes `y` through `t` and drops it; ending `borrow_k` substitutes the final content `y` for the hole. What remains in `c` is #seal(`let c = σ; let r = TailM(&c); *r := y; c`): the effect of `AddM'`, as a program. The hole plays the role of Aeneas's region abstraction for this one call: it records only the _final_ value written through the returned borrow.

The equivalence of the two additions is proved by the same bare recursion:

```
AddMEq(x : &Nat, y : Nat) : Id Unit (AddM(x, y)) (AddM'(x, y)) by x :=
  match *x { Z => refl, S p => AddMEq(&p, y) }
```

In the successor branch, re-running `AddM'`'s sealed program on `S σ'` unfolds `TailM` once, closes off its inner call with a fresh hole, and the pending write `*r := y` then fills that hole; on the other side the recursive call's statement, evaluated at the call site, performs the same steps through the caller's borrow. Both sides arrive at `Eq Nat (S A(σ', y)) (S B(σ', y))`, where `A` and `B` are the sealed programs for the two additions on the predecessor. The theorem for an owned number follows by lending it: `AddMEqOwned(x : Nat) : Id Unit (AddM(&x, 0)) (AddM'(&x, 0)) := AddMEq(&x, 0)`.

== Proofs about the current state

Dependent types are not only for stating theorems after the fact. A function can demand, as an argument, a proof about the _current_ contents of a borrow. Here is in-place subtraction, which is total only when the subtrahend is no larger than the number:

```
Le(a : Nat, b : Nat) : Prop by a :=
  match a { Z => True, S a' => match b { Z => False, S b' => Le(a', b') } }

SubM(x : &Nat, y : Nat, h : Le(y, *x)) : Unit by y :=
  match y { Z => (), S q => match *x { Z => match h {}, S p => *x := p; SubM(x, q, h) } }
```

The type of `h` mentions `*x`, the content of the borrow at the moment of the call. Where `*x` is `Z` but `y` is not, `h` has type `Le(S q, Z)`, which computes to `False`: the case cannot arise, and the match with no arms, `match h {}`, says so. Inside `SubM`, after `*x := p` has overwritten that content, the recursive call needs a proof of `Le(q, *x)` about the _new_ content; the old hypothesis `h`, of type `Le(S q, S p)`, provides it, because that type was formed when `h` was bound and normalises to `Le(q, p)`.

Now a caller that first adds and then subtracts:

```
LeAdd(n : Nat, m : Nat) : Le(n, Add(n, m)) by n := match n { Z => refl, S n' => LeAdd(n', m) }

AddSub(x : &Nat, y : Nat) : Unit := let old = *x; AddM(&*x, y); SubM(x, old, LeAdd(old, y))
```

At the call to `SubM`, `*x` has just been mutated in place by `AddM`, so on symbolic input it holds the sealed program `N(σ, y) = ⌈let c = σ; AddM(&c, y); c⌉`, and `SubM` demands a proof of `Le(σ, N(σ, y))`. The lemma `LeAdd` is about the _pure_ `Add` of the snapshot `old`, and its type is `Le(σ, Add(σ, y))`. The two meet because `Add(σ, y)` normalises to the very same sealed program: the in-place computation and the pure one are the same program to the type checker. A proof about the pure function is accepted where a proof about the mutated state is required, with no bridging lemma. Using the snapshot after further mutation, `…; AddM(&*x, y); *x := Z; SubM(x, old, LeAdd(old, y))`, is rejected, since the requirement then mentions `Z`.

== Trees

Nothing above is specific to numbers. With several constructors and several fields, a pattern variable names a field place, and the environment keeps every field that a recursive call does not touch. In-place insertion into a binary search tree recurses into the left or the right subtree according to a comparison, so which place is mutated depends on a value. Its pure version is not written separately; like `Add`, it runs the in-place one on a copy:

```
InsertM(t : &Tree, k : Nat) : Unit by t :=
  match *t { Leaf          => *t := Node(Leaf, k, Leaf),
             Node(l, v, r) => let b = Lt(k, v);
                              match b { true => InsertM(&l, k), false => InsertM(&r, k) } }
Insert(t : Tree, k : Nat) : Tree := InsertM(&t, k); t
```

A property of the in-place code is then stated and proved directly: insertion adds one node.

```
SizeInsert(t : Tree, k : Nat) : Id Nat (S (Size(t))) (Size(Insert(t, k))) by t :=
  match t { Leaf => refl,
            Node(l, v, r) => let b = Lt(k, v); match b {
              true  => J(Nat, S (Size(l)), Size(Insert(l, k)),
                         λ(z : Nat) : Prop => Id Nat (S (S (Add(Size(l), Size(r))))) (S (Add(z, Size(r)))),
                         SizeInsert(l, k), refl),
              false => J(Nat, Add(Size(l), S (Size(r))), S (Add(Size(l), Size(r))),
                         λ(z : Nat) : Prop => Id Nat (S z) (S (Add(Size(l), Size(Insert(r, k))))),
                         AddS(Size(l), Size(r)),
                         J(Nat, S (Size(r)), Size(Insert(r, k)),
                           λ(z : Nat) : Prop => Id Nat (S (Add(Size(l), S (Size(r))))) (S (Add(Size(l), z))),
                           SizeInsert(r, k), refl)) } }
```

The comparison `Lt(σ_k, σ_v)` is stuck, so the split on `b` is a split on a sealed program: the checker names its value by a fresh abstract value, and replaces every derivation of the same closed program by it, including those produced later when the goal's sealed programs run again. In each arm, `Insert`'s sealed program runs one step and leaves the other subtree and the key in place, carried by the environment. The proof is not bare recursion: without rewriting tactics, each arm rewrites with the induction hypothesis by `J` with a hand-written motive, and the `false` arm needs an arithmetic lemma, `AddS : x + S y = S (x + y)`, proved in place by bare recursion and transferred to `Add` by lending, as `AddZero` was. This is the honest cost of a property that is not an equation between two recursions of the same shape.

== Branching

A `match` on an abstract value in the middle of a function is closed off like a call: each arm is checked separately, and the rest of the function once. This covers borrows whose origin depends on the branch, as in `AddToOne(b : Nat, x₁ : &Nat, x₂ : &Nat, y : Nat) : Unit := let r = match b { Z => x₁, S _ => x₂ }; AddM(r, y)`, whose closed-off match returns a borrow with a hole in the sealed programs of both `x₁`'s and `x₂`'s owners.
