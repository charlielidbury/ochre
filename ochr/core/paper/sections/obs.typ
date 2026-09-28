#import "../style.typ": *

`Id A t u` states that the computations `t` and `u`, both of result type `A`, are indistinguishable from where the statement is made: run from the current environment, they return equal values and leave equal contents in every place either of them may write. This section defines that notion precisely and shows that it reduces to ordinary propositional equality.

== Footprints and observations

A computation affects the world only through the places it names. The places a term may *write* are read off its syntax: they are the free places that appear under `&_` or on the left of `:=`, and the borrow variables it mentions, since a borrow grants write access to someone else's place. Each of these is traced back to the owned place that will receive the write. For a place rooted at an owned variable `x`, that is `x`. For a borrow variable holding `borrow_ℓ v`, it is the set of _owners_ of `ℓ`:

$ "owners"(ell) = union.big_("occurrences of" "loan"_ell) cases("owners"(m) & "if the occurrence lies inside the content of" "borrow"_m, {x} & "if it lies inside the owned binding" x) $

Following loans outward through enclosing borrows is what connects a reborrow with the place it ultimately writes. In the successor case of `AddMZero`, the argument `borrow₁ σ'` has its loan inside the content of `x`'s `borrow₀`, whose loan is in the generic caller's `c`; so the owner of the recursive call's argument is `c`, the same place the goal observes. The owners form a set because a hole left by a returned borrow can occur in several sealed programs at once. Observing only one of them would be unsound: a call that returns a borrow into one of two arguments could then be proved to leave the other unchanged whichever it picked.

The _footprint_ `W(t, u)` is the union of the owners of the places `t` or `u` may write. It is syntactic, so it does not change when a later case split refines an abstract value, and it does not depend on unrelated places in the environment.

The _observation_ of `t` at `Ω` on footprint `W` runs `t` on a private copy of `Ω`, ends every borrow that remains, and reads off the result and the contents of the footprint:

$ ⟦t⟧_Omega^W = (v, Omega'(k)_(k in W)) quad "where" cfg(Omega, t) arrow.b.double cfg(Omega'', v) "and" Omega'' arrow.squiggly^* Omega' "with no borrows left" $

If `t` is itself stuck outside any call, it is first closed off as a stuck block, so an observation always exists. Ending every remaining borrow makes the observation independent of which borrows happened to be live when `t` finished; that the order in which they are ended does not matter is a theorem (@sec-meta).

== `Id` is equality of observations

#figure(kind: image, supplement: [Figure],
  block[
    $ "Id" A space t space u quad equiv quad "Eq" (A times T_W) space ⟦t⟧_Omega^W space ⟦u⟧_Omega^W quad quad W = W(t, u), "both sides run from" Omega "on independent copies" $
    #v(4pt)
    $ "Eq" (A times B) (a, b) (a', b') equiv "Eq" A space a space a' and "Eq" B space b space b' quad quad "Eq" A space a space b equiv top "  if " a equiv b quad quad top and P equiv P equiv P and top $
  ],
  caption: [`Id` computes to `Eq` between observations (`T_W` is the product of the types of the places in `W`; for empty `W` the pair is just `A`), and `Eq` computes on pairs and on reflexive instances. `refl : ⊤`.],
) <fig-id>

@fig-id is the whole of `Id`. Both sides run from the same environment, each on its own copy; sharing one copy and running the sides in sequence would let the first side's effects change what the second observes. The result type `A` must be borrow-free: a borrow has no meaning once the computation that produced it has finished.

The equality `Eq` on the right is Lean's, living in the proof-irrelevant universe `Prop`. We add three conversion rules in the style of observational type theory @ott @ott-now-for-good: equality at a product is a conjunction, a reflexive equation is `⊤`, and `⊤` is a unit for `∧`. Their only role is to strip away the parts of an observation that no side changed, so that `Id Unit (AddM(x, 0)) ()` computes to the single interesting equation

$ "Eq" (sans("Unit") times sans("Nat")) ((), N(sigma)) ((), sigma) equiv top and "Eq" sans("Nat") space N(sigma) space sigma equiv "Eq" sans("Nat") space N(sigma) space sigma. $

Each rule identifies two propositions with the same truth value, so all three hold in the proof-irrelevant set model of Lean's type theory @theory-of-lean. Accordingly `refl` proves `⊤`, and by conversion every reflexive equation. Transport `J(A, a, b, P, h, t)` takes its endpoints explicitly, since a reflexive `Eq A a a` computes to `⊤` and no longer records them.

Three consequences are worth drawing out.

*Effects are outputs.* The observation turns every write to a place in the footprint into an extra component of the result. This is the sense in which Ochr has no pure/impure divide: a computation's effects are part of its value as seen by `Id`, and the programmer never declares them.

*Owned locals are observed.* The footprint includes places the current function owns, not only the places behind its borrow parameters. This is forced. A context such as `(□; x)`, which reads `x` afterwards, distinguishes `x := 6` from `()`; if `Id` ignored owned locals it would equate them, and transport along that equation would prove `Eq Nat 6 5`.

*Unobserved moves are harmless.* Reading a borrow variable moves it, so the two sides of an `Id` may consume different borrow variables. Borrow variables are never in the footprint (their owners are), and ending the remaining borrows puts every borrowed content back in its owner, so what one side consumed and the other did not makes no difference to the comparison.
