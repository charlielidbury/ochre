# 01 · Closing off: how an effectful definition unfolds inside a type

Read `00-idea.md` first. This document resolves its `???` and records the design principles the resolution forces. Throughout, the emphasis is on why each choice is the only one that works, not just what the choice is.

## 0. The answer, then the argument

The hole is `cong S (AddZero px)`. The whole proof is

```
let AddZero = λx: Nat. match x {
    Z    => Refl,
    S px => cong S (AddZero px),
};
```

which is the proof one would write for a pure `Add`. Every trace of the mutation has been absorbed into definitional equality by a single new reduction rule, *closing off*, which fires when the normalizer reaches a call whose body it cannot run to completion:

```
        Ω[loan_i] ⊢ f (borrow_i v) w              the body of f gets stuck on v
CLOSE  ─────────────────────────────────────────────────────────────────────────
        Ω[(f♯ v w).back] ⊢ (f♯ v w).ret
```

`f♯ v w` is a neutral term: a stuck call, written on the *values* of its arguments rather than on the borrows. Its two projections are the call's return value and the final content of the place it borrowed. The rest of this document explains why this rule is the one, why the alternatives fail, and what it costs.

Notation beyond `00-idea.md`: `|` separates frames in Ω; `Ω[·]` marks one position inside Ω, possibly under constructors; `⟨Ω, e⟩ ⇓ v` is evaluation to a value; `≡` is definitional equality; `f♯` is the neutral head for a closed-off call to `f`.

## 1. Evaluation, not rewriting

`00-idea.md` says the language "has β-reduction with side effects". Taken literally this is unworkable, and seeing why fixes the shape of everything that follows.

β-reduction in a pure calculus is a rewrite system: any redex anywhere may fire, in any order, and confluence guarantees the answer does not depend on the order. Definitional equality is "same normal form", which is a definition only because normal forms are unique. Side effects destroy confluence at once. Take `(λy. x := 2; y) (x := 1)`. Evaluating the argument first leaves `x` at 2; substituting first, as rewriting anywhere permits, runs the writes in the other order and leaves it at 1. Two answers, so "same normal form" no longer names a relation, and no care with typing rules brings it back.

What restores uniqueness is fixing the order. The operational semantics of Ochr is a deterministic call-by-value machine, the Ω interpreter of `00-idea.md`. Run it on a closed term and it produces a value. Run it on an open term, with the free variables bound to abstract values σ, and it produces a value or gets stuck at a point where it must inspect a σ. Definitional equality is then: two terms are equal when the machine sends them to the same thing. The standard name for this is normalization by evaluation. Instead of defining normal forms by a rewrite relation and proving them unique, one defines them as the outputs of an evaluator run on symbolic inputs, and uniqueness is inherited from the evaluator being a function. There is no confluence to prove because there is only one order.

So the normalizer of Ochr *is* the abstract interpreter, and the whole design question becomes: what does the machine do when it gets stuck, and what term stands for the stuck state?

## 2. Places and values

Before answering that, one principle that settles most of the small questions at once.

Ω maps variables to values. Inside a type, a free variable does not mean the place; it means the value Ω currently holds for it. In `Id Nat x 5` with `x ↦ σ`, the `x` means `σ`, a mathematical object that never changes. Mutation does not change σ; it replaces the content of the place `x` with a different value.

There is no other choice, because proofs outlive the states they were made in:

```
λx: Nat. (
    let p : Id Nat x x := Refl;   // elaborates to Id Nat σ σ
    x := S x;                     // Ω now has x ↦ S σ
    p                             // still Id Nat σ σ
)
```

If `x` in a type meant the place, the type of `p` would change on the second line while `p` did not. A term's type would fail to be stable under evaluation at every write, which is to say subject reduction would fail. The only semantics in which a proof is a value with a stable type is the one in which types mention values, and it is where every system that combines specification with state ends up: `old(x)` in Hoare logic, snapshots in Creusot, σ in Aeneas.

Three consequences follow with no further design work.

**Assignment to an ambient variable inside a type is ill-formed.** `Id Unit (x := 1) ()` is rejected with "x is a value here, not a place", for the same reason `5 := 1` is. Assignment and `&mut` need a place, and the only places a type-level term can name are the ones it creates itself, by `let` or as parameters of a function the normalizer unfolds into a fresh frame. So a type-level term cannot have effects on the ambient environment at all, and this needs no separate check; it is a consequence of what variables mean. Local mutation inside a type is unrestricted:

```
Id Nat (let y := x; y := S y; y) (S x)     ⇓     Id Nat (S σ) (S σ)      // Refl
```

To talk *about* the effect of a computation, own its state and return it. The type `Π v: Nat. Id (Nat × Unit) (let x := v; x := 1; (x, ())) (let x := v; (x, ()))` normalizes to an equation between `(1, ())` and `(σ_v, ())`, which is unprovable, as it should be. `Add` is exactly this encoding of `AddM`.

**The type level is not linear.** `Id Nat (Add x 0) x` uses `x` twice, and so does `Πx: Nat. Id Nat (Add x 0) x`. A linear or affine type level could not state the theorem. Runtime terms stay affine; terms mentioned in types are not. This is the zero multiplicity of quantitative type theory, and Idris 2 is the reference for how the two layers coexist. Borrows appear in Ω while the normalizer runs, but never in a normal form.

**Places are made by evaluation, values by typing.** `λx: Nat. body` at term level makes `x` a place in `body`; when the normalizer unfolds an application of that λ it opens a frame with a fresh place holding the argument's value. `Πx: Nat. T` makes `x` a value in `T`. The two never conflict, because the normalizer's frames are its own and the ambient context only ever contributes values.

## 3. Where the machine gets stuck

The machine gets stuck at a `match` whose scrutinee, looking through any borrow, is an abstract σ or a neutral term. What happens next depends on where that match is.

If the match is in the term being checked, the checker case-splits. For each branch it refines Ω (`x ↦ Z`, or `x ↦ S σ_px` with `px ↦ σ_px`), substitutes the refinement into every type in scope, and checks the branch. This is ordinary dependent pattern matching; the match in `AddZero` is of this kind.

If the match is reached while unfolding a definition during conversion, case-splitting is not available: conversion must return one answer, not one per branch. The machine must instead produce a neutral term, a piece of syntax standing for "this computation, whose result is unknown until σ is". Which term is the subject of the next section.

Unfolding itself is not optional. `Refl : Id Nat (Add Z 0) Z` type-checks only if the checker runs `Add Z 0` to `Z`, which means unfolding `Add`, unfolding `AddM`, and performing the write. A checker that treated calls as opaque, as Aeneas's symbolic execution does for modularity, would make nothing definitionally equal to anything, and every equation would have to be proven from a specification of `AddM`: exactly the pure-model-plus-equivalence-proof workflow the language exists to avoid. But unfolding cannot be unconditional either. In CIC a fixpoint unfolds only when its recursive argument is a constructor; applied to a variable it is itself a neutral, and this guard is what makes conversion decidable and terminating. Ochr inherits the guard, reading through the borrow: `AddM (borrow (S σ)) 0` unfolds and `AddM (borrow σ) 0` does not. Section 5 gives the rule in its general form, where it is semantic rather than syntactic.

## 4. Reification: what term stands for a stuck computation

Normalization by evaluation has two halves. *Evaluate* runs the machine. *Reify* reads a stuck machine state back into a term, so that it can be stored in a type, substituted into when σ is later refined, and compared for equality. The design question is what term to write down, and there are two candidates: freeze the innermost stuck `match`, with the frame's values substituted in, or freeze the innermost enclosing *call*, on the values of its arguments.

Lean reifies at the match: a stuck recursor application `Nat.rec … x` is a normal form, and it is what appears in a goal after an over-eager `unfold`. It is harmless there, because a stuck `Nat.rec` on a variable is a closed pure term. Here it is not harmless. Run `Add (S σ_px) 0` until the inner `AddM` is stuck:

```
Ω = { z ↦ loan_0  |  x ↦ borrow_0 (S loan_1)  |  x' ↦ borrow_1 σ_px, y' ↦ 0 }
stuck at:  match x' { Z => *x' := y',  S px' => AddM px' y' }
```

Frozen at the match, the neutral is `match (borrow_1 σ_px) { Z => *x' := 0, S px' => AddM px' 0 }`. It contains `borrow_1`, a reference to a location in Ω, so it means nothing except relative to this Ω, and it has a pending effect on `loan_1`. Now continue the caller: pop the frame of `AddM`, end `borrow_0`, read `z`. Ending `borrow_0` requires `loan_1` to have been ended, which requires knowing what the stuck match did to it. Nothing knows. The stuckness propagates outward, frame by frame, until the whole block freezes as a residual program, schematically:

```
Add (S σ_px) 0   ⇓   let z := S σ_px; match (&mut (&mut z).pred) { Z => …, S _ => … }; z
Add σ_px 0       ⇓   let z := σ_px;   match (&mut z)              { Z => …, S _ => … }; z
```

These are closed, so they are legitimate normal forms. They are useless. The induction hypothesis has the second as a subterm; the goal is the first; `cong S (AddZero px)` needs the goal to be `S` applied to the second, and syntactically it is not. Making them equal would require the conversion checker to prove a program equivalence: running a stuck computation on a reborrow of the tail of `z` and then reading `z` equals `S` of running it on a fresh copy of the tail. That equivalence is the frame rule. The machine had already performed it when it wrote `x ↦ borrow_0 (S loan_1)`: the `S` is sitting in Ω, outside the stuck call. Reifying at the match freezes the frame mid-step, throws that work away, and asks a syntactic comparison to rediscover it, which it cannot.

A smarter freeze-at-match that noticed the effect is confined to `loan_1` and gave its final content a name would be exactly the other candidate. So: reify at the call.

## 5. Closing off

When the body of a call gets stuck, the machine restores Ω to its state at the call and replaces the call by a neutral term on the values of its arguments, filling each loan the call held with a projection of that neutral:

```
        Ω[loan_i] ⊢ f (borrow_i v) w              the body of f gets stuck on v
CLOSE  ─────────────────────────────────────────────────────────────────────────
        Ω[(f♯ v w).back] ⊢ (f♯ v w).ret
```

The projections are not new primitives. They are the canonical forms of source programs that own their state:

```
(f♯ v w).back   is the normal form of   let z := v; f (&mut z) w; z
(f♯ v w).ret    is the normal form of   let z := v; f (&mut z) w
```

Those programs normalize to those projections by CLOSE itself, so the two equations are consequences of the rule rather than axioms. The projections are two runs of `f`; they agree because the machine is deterministic and, by the termination checker, total.

**Why the neutral is written on values rather than the borrow.** A borrow contains a loan identifier and means nothing outside its Ω; a value is closed. The neutral must be closed because it will be substituted into. The goal `Id Nat (Add x 0) x` is elaborated once, with `x ↦ σ_x`, to `Id Nat (AddM♯ σ_x 0).back σ_x`. In the `S px` branch the refinement `σ_x := S σ_px` is substituted, and the neutral must then be run again, since `AddM♯ (S σ_px) 0` now unfolds. A neutral is therefore a stuck call carrying everything needed to run it: the function and the values of its arguments. This is also why Aeneas's backward functions take values.

**Why the rule is sound, and what it demands of the language.** The rule asserts that the effect of a call on its caller's environment is a function of the call's argument values. That is the frame rule of separation logic, and here it holds by construction rather than by proof, because a function can reach only what it was passed, by move or by borrow. The borrow discipline is what makes a stuck effectful call a *function*, and thereby something a term can name. The assertion is false the moment a function can reach state by any other route, so the language must have no globals, no interior mutability, and no unsafe code. These are not simplifications; they are the hypothesis of the one rule the design rests on.

**Why closing off is semantic, at the innermost call, rather than a syntactic guard.** A function may get stuck on a match that is not on its recursive argument, for instance `f (x: &mut Nat) (b: Bool) = match b { … }` called with `b ↦ σ_b`. No syntactic guard predicts this in general. The semantic rule, unfold every call and if the body gets stuck restore Ω to the call and close it off, handles every case uniformly, and for a structurally recursive function whose only match is on its recursive argument it coincides with the CIC guard. The restoration discards effects the partial run had already performed; nothing is lost, because `.back` denotes the whole run and the discarded prefix is part of it.

**A stuck match outside any call.** A match written directly in a type-level block, such as `Id Nat (match x { Z => Z, S _ => Z }) Z`, has no call to close off. It is reified together with the smallest enclosing closed subterm, which at type level is the block itself, since a block owns every place it can name. Such neutrals are the ordinary stuck case analyses of CIC. In general the unit of closing off is any subterm whose footprint is known: a call's is given by its signature, a block's by an analysis of the places it mentions. This document uses calls.

## 6. The example, end to end

Unfolding a function opens a frame whose parameters are fresh places holding the argument values.

```
⟨{ x ↦ S σ_px }, Add x 0⟩
⟨{ z ↦ S σ_px }, AddM (&mut z) 0; z⟩                                           // unfold Add
⟨{ z ↦ loan_0 }, AddM (borrow_0 (S σ_px)) 0; z⟩                                 // borrow z
⟨{ z ↦ loan_0 | x ↦ borrow_0 (S σ_px), y ↦ 0 }, match x {…}; z⟩                 // unfold AddM
⟨{ z ↦ loan_0 | x ↦ borrow_0 (S loan_1), px ↦ borrow_1 σ_px, y ↦ 0 }, AddM px y; z⟩   // S case; the match reborrows the field
⟨{ z ↦ loan_0 | x ↦ borrow_0 (S loan_1) }, AddM (borrow_1 σ_px) 0; z⟩           // px, y move into the call
                                                                                // AddM's body is stuck on σ_px: CLOSE with N := AddM♯ σ_px 0
⟨{ z ↦ loan_0 | x ↦ borrow_0 (S N.back) }, N.ret; z⟩
⟨{ z ↦ S N.back }, z⟩                                                           // AddM's frame ends; x is dropped, borrow_0 ends into loan_0
⟨∅, S (AddM♯ σ_px 0).back⟩
```

The induction hypothesis, by the same rule and nothing else:

```
⟨{ x ↦ σ_px }, Add x 0⟩
⟨{ z ↦ loan_0 }, AddM (borrow_0 σ_px) 0; z⟩         // unfold Add, borrow z; AddM's body is stuck at once: CLOSE
⟨{ z ↦ N.back }, N.ret; z⟩
⟨∅, (AddM♯ σ_px 0).back⟩
```

The base case runs to completion with no neutral at all:

```
⟨{ x ↦ Z }, Add x 0⟩   ⇓   ⟨∅, Z⟩            // the Z case writes y into *x; the write is local to the block
```

Now check `AddZero`. In the `S px` branch, Ω = `{ x ↦ S σ_px, px ↦ σ_px }`. The expected type, with values substituted and normalized, is `Id Nat (S (AddM♯ σ_px 0).back) (S σ_px)`. The term `AddZero px` has type `Id Nat (Add px 0) px`, which normalizes to `Id Nat (AddM♯ σ_px 0).back σ_px`, and `cong S` of it is the expected type, symbol for symbol. The `Z` branch is `Refl : Id Nat Z Z`.

Two things to notice. The `S` in the answer was never computed by anything resembling `cong`. It was sitting in Ω as `borrow_0 (S loan_1)`, between the outer loan and the inner one, put there by the rule for matching through a reference. The borrow bookkeeping *is* the congruence. And the proof term makes no reference to mutation, states, or frames: the theorem about the in-place function is proven exactly as it would be about a pure one.

Compare the state monad, the obvious alternative encoding. There `AddM y : State Nat ()` and `Add x y = runState (AddM y) x`. The state is one opaque blob, and `Add (S x) 0 = S (Add x 0)` is a theorem, proven by unfolding the monadic code and reasoning about the whole blob. Here it is definitional, because places have structure and a reborrow of the tail leaves the head in Ω untouched. Places give a definitional frame rule; monads do not. That is the argument for building on borrows rather than on a monad.

## 7. What this is

The mathematics is not new, and it is worth being exact about where it comes from and what is different.

`(f♯ v w).back` is Aeneas's backward function `f_back v w`. Aeneas's symbolic execution, on reaching a call, ends a region abstraction by introducing a fresh symbolic value for each loan given back and emitting `let σ' := f_back … in` into the pure translation. CLOSE does the same with the term itself as the name. The difference is where and when. Aeneas performs the translation once, eagerly, for a whole function, and reasons about the translated artifact. Ochr performs it lazily, inside conversion, only as far as a particular equality needs, and the source term is the thing reasoned about. Aeneas never unfolds a callee, which is what makes it modular; Ochr must, because unfolding definitions is what conversion is, and the guard of section 5 is what keeps that decidable.

The same object appears in RustHornBelt and Creusot as a *prophecy*: a mutable borrow is modelled as its current value paired with a logic variable `^x` for its final value, resolved when the borrow ends. `loan_i ↦ (f♯ v w).back` is a prophecy with a name, and CLOSE is its resolution. It appears in a state-monad library as `runState`. One idea at three levels: a logic variable, a pure function, a neutral term.

Hoare type theory and Ynot combine dependent types with effects by keeping the effects propositional: a computation has a type `{P} T {Q}`, and one proves `Add x 0 = x` from a specification of `AddM`. The `⟨Ω, e⟩` pairs of `00-idea.md` are Hoare triples in spirit. CLOSE is what turns them into computation, so that the unfolding is definitional and the specification is the code.

What is gained is ergonomic, and real: no translated artifact, no separately written pure model, and a proof that is the pure proof. What is inherited is the whole metatheory of the symbolic semantics, which Aeneas argues for a fragment and Ochr must have in full.

## 8. What must be proven

The obligations split by what they protect.

**Consistency**, meaning no closed proof of `Id Nat Z (S Z)`, needs the standard three: every well-typed closed-off term has a normal form; that normal form is unique; and closed normal forms of type `Nat` are numerals, so that `Refl`, whose endpoints must be convertible, cannot inhabit that type. The effects enter through uniqueness. The machine is deterministic on closed inputs by construction, but on symbolic inputs a choice remains: the order in which loans are ended when several are outstanding. Aeneas leaves the order nondeterministic and argues informally that the translation is the same up to equivalence. Ochr cannot leave it open, because two normal forms for one term plus `Refl` is a proof that they are equal, and if they differ that is a proof of False. The strategy of `00-idea.md`, end a loan only when a read of its place demands it, is deterministic; what remains is to prove that independent loan endings commute, so that the strategy's answer is canonical. This is the most important theorem in the design.

**Adequacy**, meaning that what is proven about `Add` is true of the compiled `Add`, needs the symbolic machine to refine the concrete one: for every instantiation of the abstract values, concrete evaluation of the instantiated term yields the instantiated normal form. This is Aeneas's soundness theorem. It is the theorem CLOSE's frame assumption rests on, and it is where the prohibitions of section 5 and the correctness of the borrow checker enter. Consistency does not depend on it. A type theory whose reduction was consistent but mismatched the runtime would prove true things about the wrong program.

**Termination of the source functions** is assumed by both. Its checker must measure the value at entry, not the current value. In `*x := S *x; match x { S px => f px }` the recursive argument is a strict sub-value of the current content but equal to the entry value, and the function never terminates. The borrow checker supplies part of the guarantee: a live reborrow of a field forbids writing the parent, so at the recursive call the argument is a strict sub-value of the parent as it then is. Writes before the match are the gap, and the symbolic execution, which sees both the entry value and the argument value in Ω, is the natural place to close it.

**Subject reduction** for the machine, in the usual form: evaluation preserves the type, where the type is read against the values in Ω.

## 9. What the example hides

The example is chosen so that the borrowed argument is consumed entirely inside the call and the return type carries no borrow. Relaxing either exposes the general shape of the rule.

*Returning a borrow.* Write `AddM` iteratively as `*(last_mut x) := y` with `last_mut : &mut Nat → &mut Nat`. Closing off `last_mut (borrow_1 σ)` must return a borrow whose loan lives inside the neutral, and the caller's `loan_1` cannot be filled until the caller has finished writing through the returned borrow. So `loan_1` receives a function awaiting that final value, `λfinal. (last_mut♯ σ).back final`, applied when the returned borrow ends. That is a region abstraction of Aeneas written as a neutral term. It should be the second worked example, because it tests whether normal forms with λ-valued loan fills still let `cong S` go through.

*Argument values containing borrows.* If `v` itself contains a borrow of some other place, the call can write through it, so CLOSE must fill every loan reachable from the arguments, one `.back_j` each. The signature says which.

*Specifications on borrowed arguments.* Nothing here lets a type mention the post-state of a `&mut` argument directly; one speaks about `AddM` only through `Add`. Creusot's `^x` is the obvious syntax to add, and its meaning is already present as `.back`. Deferred.

*Equality at borrow types.* `Id (&mut Nat) a b` is forbidden for now. The sane reading, when it is wanted, is that a borrow is transparent at the type level and denotes its current content.

*Definitional equalities lost.* Reifying at the call rather than the match means two functions with identical bodies are not convertible when stuck, and no partial evaluation of a stuck call is exposed. Lean's structural recursion via `brecOn` would identify them; Lean's well-founded recursion, being irreducible, would not. The loss is of that second kind and is accepted.

## 10. Rule sheet

Principles.

- P1. Definitional equality is sameness of normal form, where normal forms are the outputs of the deterministic Ω machine on symbolic inputs. Evaluation, not rewriting.
- P2. A free variable in a type denotes a value, never a place. Places exist only in frames the machine opens.
- P3. Terms in types are not linear. Runtime terms are affine.
- P4. A stuck computation is reified at the innermost enclosing subterm with a known footprint, normally a call, never at a bare match.
- P5. The effect of a call is a function of its argument values. Guaranteed by borrows and by the absence of globals, interior mutability, and unsafe code.

Rules.

- R1, match in a checked term: case-split; refine Ω per branch; substitute the refinement into every type in scope.
- R2, unfold: every call is unfolded into a fresh frame whose parameters are places holding the argument values.
- R3, CLOSE: if the body gets stuck, restore Ω to the call, replace the call by `f♯ v̄`, fill each loan it held with the matching `.back` projection, and return `.ret`. The projections are the normal forms of the state-owning programs of section 5.
- R4, ending a borrow: a live borrow ends when its holder is dropped or when a read of its loaned place demands it; the place receives the borrow's current content.
- R5, conversion: syntactic equality of normal forms, up to α for λ-valued fills.

Obligations, in order of importance: canonicity of the ending strategy (independent endings commute); refinement of the concrete semantics by the symbolic one; entry-value termination; subject reduction.
