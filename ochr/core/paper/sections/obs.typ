#import "../style.typ": *

`Id A t u` states that the computations `t` and `u`, both of result type `A`, are indistinguishable from where the statement is made: run from the current environment, they return equal values and leave equal contents in every place either of them may write. This section defines that notion precisely and shows that it reduces to ordinary propositional equality.

== Footprints and observations

A computation affects the world only through the places it names. The places a term may *write* are read off its syntax: they are the free places that appear under `&_` or on the left of `:=`, and the borrow variables it mentions, since a borrow grants write access to someone else's place. Each of these is traced back to the owned place that will receive the write. For a place rooted at an owned variable `x`, that is `x`. For a borrow variable holding `borrow_ℓ v`, it is the set of _owners_ of `ℓ`:

$ "owners"(ell) = union.big_("occurrences of" "loan"_ell) cases("owners"(m) & "if the occurrence lies inside the content of" "borrow"_m, {x} & "if it lies inside the owned binding" x) $

Following loans outward through enclosing borrows is what connects a reborrow with the place it ultimately writes. In the successor case of `AddMZero`, the argument `borrow₁ σ'` has its loan inside the content of `x`'s `borrow₀`, whose loan is in the generic caller's `c`; so the owner of the recursive call's argument is `c`, the same place the goal observes. The owners form a set because a hole left by a returned borrow can occur in several sealed programs at once, and all of them must be observed (@fig-why).

The _footprint_ `W(t, u)` is the union of the owners of the places `t` or `u` may write. The places are read off the syntax, so the footprint does not depend on unrelated places in the environment; their owners are found by following loans, so a later refinement can shrink an owner set, removing a component both sides agree on.

The _observation_ of `t` at `Ω` on footprint `W` runs `t` on a private copy of `Ω`, ends every borrow that remains, and reads off the result and the contents of the footprint:

$ ⟦t⟧_Omega^W = (v, Omega'(k)_(k in W)) quad "where" cfg(Omega, t) arrow.b.double cfg(Omega'', v) "and" Omega'' arrow.squiggly^* Omega' "with no borrows left" $

If `t` is itself stuck outside any call, it is first closed off as a stuck block, so an observation always exists. Ending every remaining borrow makes the observation independent of which borrows happened to be live when `t` finished; that the order in which they are ended does not matter is a conjecture, proved for two endings (@sec-meta).

== `Id` is equality of observations

#figure(kind: image, supplement: [Figure],
  block[
    $ "Id" A space t space u quad equiv quad "Eq" A space r space r' and "Eq" T_1 space w_1 space w'_1 and dots and "Eq" T_k space w_k space w'_k quad quad "where" ⟦t⟧_Omega^W = (r, overline(w)), space ⟦u⟧_Omega^W = (r', overline(w')), space W = W(t, u) $
    #v(4pt)
    $ "Eq" ty("D")(overline(a)) space ty("C")(overline(v)) space ty("C")(overline(w)) equiv "Eq" B_1 space v_1 space w_1 and dots and "Eq" B_k space v_k space w_k quad quad "Eq" ty("D")(overline(a)) space ty("C")(overline(v)) space ty("C")'(overline(w)) equiv ty("False") "  if " ty("C") != ty("C")' $
    $ "Eq" A space a space b equiv top "  if " a equiv b quad quad top and P equiv P equiv P and top $
  ],
  caption: [`Id` computes to a conjunction of equations between the two observations, both run from Ω on independent copies ($T_i$ is the type of the $i$-th place of $W$). `Eq` computes on constructor values by structure ($B_j$ are the fields' types; no fields gives `⊤`) and on reflexive instances. `⊤`, `∧` and `False` are the library inductives of @fig-syntax, and `refl : ⊤`.],
) <fig-id>

@fig-id is the whole of `Id`. Both sides run from the same environment, each on its own copy; sharing one copy and running the sides in sequence would let the first side's effects change what the second observes. The result type `A` must be borrow-free: a borrow has no meaning once the computation that produced it has finished. An observation is a tuple of the machine, not a pair value, so `A` may be any borrow-free type, a proposition or a universe included.

The equality `Eq` is Lean's, living in the proof-irrelevant universe `Prop`, and it computes on constructor values by structure, in the style of observational type theory @ott @ott-now-for-good. Two values built by the same constructor are equal when their fields are (injectivity), two built by different constructors are not (disjointness), a reflexive equation is `⊤`, and `⊤` is a unit for `∧`. The rules produce the library inductives `And`, `True` and `False`, so these three are known to the conversion checker, the one point where the library declarations are special. The unit laws are conversion rules, not a rewriting of stored types: a hypothesis of type `⊤ ∧ P` keeps its `And` and can still be taken apart by a match. Together the rules strip away what no side changed, as in the `AddM` example of @sec-overview. Disjointness lets an observation that differs in a constructor reach `False` directly: at a definition taking `x : &Nat`, the statement `Id Unit (*x := 0) (*x := 1)` computes to `False`, so a hypothesis of that type is eliminated by `match e {}`. An `Id` over several places computes to a conjunction, which `match h { Intro(l, r) => … }` takes apart. `refl` proves `⊤`, and so, by conversion, every reflexive equation. Transport `J(A, a, b, P, h, t)` takes its endpoints explicitly, since a reflexive `Eq A a a` computes to `⊤` and no longer records them, and it computes to `t` only when `a ≡ b`, as Lean's `Eq.rec` does. Under a hypothesis that equates unequal values a cast stays stuck, so there is no equality reflection and no value of the wrong type.

Two consequences are worth drawing out.

*Owned locals are observed.* The footprint includes places the current function owns, not only the places behind its borrow parameters. This is forced. A context such as `(□; x)`, which reads `x` afterwards, distinguishes `x := 6` from `()`; if `Id` ignored owned locals it would equate them, and transport along that equation would prove `Eq Nat 6 5`.

*Unobserved moves are harmless.* The two sides of an `Id` may consume different borrow variables, but borrow variables are never in the footprint, their owners are, and ending the remaining borrows puts every borrowed content back in its owner.
