#import "../style.typ": *

Typing is the machine run on abstract inputs, with case splitting where the checked program itself inspects an abstract value. The judgement `Ω ⊢ t ⇓ v : A ⊣ Ω'` says that from `Ω` the term `t` runs to the value `v` of type `A`, leaving `Ω'`. It returns the value, not just the type, because later types may depend on it: after `let z = (let y = &x; *y := 2; x)`, the type `Id Nat z 2` holds by `refl` only because the checker knows that `z` is `2`. The rules for the basic forms are the evident ones, each the corresponding machine rule annotated with types, and we omit them. @fig-typing gives the rules that are particular to Ochr.

#figure(kind: image, supplement: [Figure],
  block(width: 100%)[
    *[Call-type]* At the point where the arguments of `f(ā)` have been evaluated, with `f : Π(x̄ : Ā). B`: push a frame binding each `xᵢ` to `aᵢ`'s value, evaluate `B` there on a private copy of the environment, and pop. The result is the type of the call. Each `aᵢ` must have type `Aᵢ`, evaluated with the earlier parameters bound.

    *[Def]* `fix f (x̄ : Ā) : B by xⱼ := b` is checked at its _generic call_: from an environment with a fresh owned place `cᵢ ↦ σᵢ` for each borrow parameter `xᵢ : &Tᵢ`, the call `f(ā)` with `aᵢ = &cᵢ` for borrow parameters and `aᵢ = σᵢ` otherwise. The goal is the [Call-type] of this call. The body runs in the pushed frame, which is then dropped; its result's type must be convertible to the goal, as refined by the splits on the way.

    *[Split]* When the checked program matches on a place whose content has an abstract head `σ`, each arm is checked with the refinement `σ := Z`, respectively `σ := S σ'` for fresh `σ'`, applied to the environment, the goal and every stored type. If the head is a sealed program, every occurrence of it is first replaced by a fresh `σ`. If the match is followed by more code, that code is checked once, from the state in which the match has been closed off as a stuck block.

    *[Rec]* In the body of `fix f … by xⱼ`, `f` occurs only as the head of a call, and each recursive call passes in position `j` a value, or a borrow of a value, that is a strict subterm of `xⱼ`'s entry value `σⱼ` as refined so far.

    *[Proof]* In a term whose type is a proposition, every write, borrow or move of a place that outlives the term is an argument of a call whose result type is a proposition.
  ],
  caption: [The typing rules particular to Ochr.],
) <fig-typing>

== One rule for goals and induction hypotheses

A definition is checked by running it at its most general call [Def]. For `AddMZero(x : &Nat)` that is `AddMZero(&c)` from `{ c ↦ σ }`: the parameter becomes a borrow of a fresh owned place, which stands for whatever the real caller lends. The goal is then computed by [Call-type], the rule that types every call.

The same rule types the recursive call in the successor case, at a different environment. There the argument `&p` borrows the predecessor field of `c`'s content, so evaluating the callee's statement at the call site observes `c` through the successor that surrounds the field. This is how the induction hypothesis arrives already wrapped in `S`. The generic call and the recursive call are two instances of one rule, which is why the goal and the hypothesis meet without a congruence step. That the callee's statement, proved at its generic call, remains true at every call site is the frame property of @sec-meta: a call affects only what it is passed, so the caller's observation is the callee's, placed in a context.

== Types are formed once

A type is evaluated once, when it is formed, on a private copy of the environment, and becomes a closed statement about values. Later mutation cannot change it. This includes the codomain of a Π-type, which is a closure over the values of the variables it mentions; only its parameters are bound later, at each call. The goal of a definition is formed at its generic call, before the body runs, so a body that mutates its argument and then proves something about the new contents does not prove the goal: `λ(x : &Nat). (*x := 5; refl)` does not have type `Π(x : &Nat). Id Nat (*x) 5`.

== Case splitting and joins

A `match` in the checked program on an abstract value cannot pick an arm, so each arm is checked with the abstract value refined [Split]. What follows the match is checked once, from a state in which the match itself has been closed off as a stuck block. The closed-off match is precise: its sealed programs contain the match, and they reduce as soon as a later split decides it. There is no join of environments and no loss of information, and a borrow whose origin depends on the branch is handled like any other returned borrow. `AddToOne` of @sec-overview is accepted, and so is any function whose body is split into a helper at a match: a match and a call to a function containing it are treated alike. Errors in the code after a match are reported once, at the line where they occur, not once per arm.

== Proofs do not act

A call whose result type is a proposition is erased at runtime, and the machine skips it. For this to be sound, skipping a proof must be indistinguishable from running it, and [Proof] ensures that it is: a proof may mutate places it creates itself, and may hand outside places to other proofs, but may not write, borrow or move an outside place on its own account. `AddMZero`'s successor case borrows the field `p` only to pass it to the proof `AddMZero`, and is accepted.

This is a restriction on proofs, which are erased, and not on programs. Nothing in a program is marked pure, and any program may appear in a statement.

== Why each condition is there

Each side condition above was added in response to a concrete false proof or run-time error found while designing the calculus. We list them because together they delimit the design, and because each is a regression test for the implementation (@sec-impl).

- *Π-types capture values.* If the codomain of a hypothesis `h : Π(_ : Unit). Id Nat x Z` were re-evaluated at each call, then `x := S x; h(())` would produce a proof of `Id Nat (S Z) Z` from `h`, which was proved when `x` was `Z`.
- *Recursion on entry values.* A syntactic structural check accepts `f(x : &Nat) := *x := S *x; match *x { S p => f(&p) }`, whose recursive argument is the parameter's original value, and with it a proof of `Π(n : Nat). ⊥`. The recursive function must also never escape as a value, or the check can be bypassed through a higher-order call.
- *Proofs do not act.* Proof irrelevance at a Π-type over a borrow identifies `λx. ⋆` with `λx. (*x := 7; ⋆)`; if calls to these were run, transport along that identification proves `⊥`. Stipulating only that proof _calls_ are skipped is not enough: a proof block that writes, closed off by [Split] and then refined, would be skipped, but run directly it would not, and a closed proof of `Id Nat (S Z) Z` results. [Proof] makes skipping a consequence rather than a stipulation.
- *All owners are observed.* A function returning a borrow into one of two arguments leaves its hole in both. A footprint that observed only one owner lets [Call-type] prove `Id Nat (S Z) Z`.
- *Access is exclusive and closing off needs loan-free arguments.* Moving a borrow whose content still holds a live loan into a call, and closing that call off, copies the loan into a sealed program; after refinement the sealed program disagrees with running the call, and the compiled program writes through an ended borrow.
