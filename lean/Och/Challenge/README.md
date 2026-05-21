# The Och Challenge

*A minimal dependently-typed calculus. Your task: build a sound constructive type checker for it.*

## Background

**Och** is a work-in-progress core calculus for the Ochre programming language. Its defining feature is that **terms and types share a single syntactic category** — there is no separate "type" grammar. A value, a type, and a proposition are all the same kind of thing. A type checker for Och is therefore simultaneously doing (partial) evaluation, term comparison, and subtype inference.

This challenge is the Och core stripped to its minimum: five term forms plus `μ`. It is intentionally small so that the interesting question is not "how many rules" but "how do you even *formulate* the algorithm and its correctness".

## The language

Syntax (shown with named variables for readability; the Lean formalisation uses de Bruijn indices).

**Notation convention used throughout this README:**
- `E, F, A, T, B, D, R, …` (capital) — arbitrary expressions, possibly unevaluated.
- `e, f, a, v, …` (lowercase) — values, i.e. results of `⇓`.
- `x, y, z, b, …` (lowercase) — variable names bound by `λ` and `μ`.

```
E, T  ::=  x                 — variable
       |   λx:T. E           — lambda with domain annotation
       |   E E               — application
       |   (E : T)           — ascription
       |   ⊤                 — "top" (compatible with every term)
       |   μx. E             — fixpoint (x is a self-reference bound in the body)
```

Some quick examples:

- `λx:⊤. x` — the polymorphic identity. Also its own type (`⊤ → ⊤`, modulo subtyping).
- `(⊤ : ⊤)` — `⊤` ascribed to itself. Ascription is how you attach a type to a term.
- `μt. t → ⊤` — a recursive "type of functions that take themselves and return ⊤".
- **Church `Bool`**: `μb. ⊤ → b → b → b` — the `μ` is what makes it dependent, because the body of the type refers back to the whole type through `b`.

**On `⊤`:** it doubles as the unit type and the subtype-lattice top — a trivially-inhabited 0-byte value in the sense of `True : Prop`, and simultaneously the type every other type is a subtype of. The two readings coincide because Och fuses kinds: there is no syntactic distinction between "types" and "values", so the unit type and the top type collapse into one symbol.

## Concrete interpretation `E ⇓ v`

[`Eval.lean`] A fuel-based call-by-value evaluator of type `Expr → Except String Expr`. It is **partial**: the head of an application must reduce to a literal lambda, otherwise evaluation errors. The rules (read conclusion first, premises indented):

```
[E-Top]
⊤ ⇓ ⊤

[E-Lam]
λx:T. B ⇓ λx:T. B // lambdas are values, domain kept

[E-Asc]
(E : T) ⇓ v // ascriptions are erased at runtime
  E ⇓ v

[E-App]
F A ⇓ v // CBV: evaluate the argument before substituting
  F ⇓ λx:D. B
  A ⇓ a
  B[x := a] ⇓ v

[E-Mu]
μx. B ⇓ v // μ is not a value; it always unfolds
  B[x := μx. B] ⇓ v
```

There are **only two values**: `⊤` and `λx:T. B` (lambdas — their insides `T` and `B` are still unevaluated syntax). Everything else either reduces or errors. In particular:

- A free variable at the top level is an error — it means a substitution was never performed, which breaks the "everything is closed by the time we run" contract.
- `F A` where `F` does not reduce to a literal lambda is an error — the head might be a variable, `⊤`, or another stuck form; none of these can be applied.

A correct `synth`/`check` must ensure these error cases never arise on accepted programs. "Progress" is not a vacuous theorem here: it is literally the statement that `eval` returns `ok` on closed, well-typed inputs — though it may exhaust fuel, because `μ` gives us general recursion and infinite loops are a programmer's prerogative, not a type error.

This is **genuine CBV**, not CBV-with-lazy-μ: evaluating `(λx:⊤. ⊤) (μy. y y)` diverges, just like `(lambda x: 0)(while True: pass)` hangs in Python. If you wanted terms like `μy. y y` to be silently tolerated when unused, you'd need lazy semantics, and this calculus deliberately does not have them. The only fixed design decision `eval` embeds is that `μ` is *not* a value: it always unfolds, plugging itself in for its own self-variable.

## The challenge

You must define one partial judgment:

```
Γ ⊢ E ⇝ T // "in Γ, the expression E has normal-form type T"
```

It is **partial**: on failure it returns a human-readable error message explaining why it could not make progress. Silent failure (`none`, `false`) is forbidden — debugging a type checker with no diagnostics is a misery you should not inflict on your future self.

The input is an arbitrary expression. The output is a normal form (or an error). What counts as "normal form" is part of your design: the scaffold starts with `NFExpr` as a synonym for `Expr` — meaning "normal form is whatever shape you promise to maintain" — but you are free to strengthen it into its own type whose constructors rule out un-normalised shapes at definition time.

`⇝` is the **entire public interface** of your type checker. Whatever else you introduce — subtyping relations, normalization passes, bidirectional modes, seen-sets, logical relations — is internal to your implementation and lives wherever is convenient for your proofs. The outside world only ever calls `⇝`.

Your solution must:

1. Make the tests pass. Tests are phrased entirely in terms of `⇝` — a subtyping claim `A ⊑ B` is encoded as "`⇝ [] (A : B)` succeeds", because ascription exists precisely to assert compatibility claims.
2. Satisfy a notion of soundness you yourself articulate and prove, relating `⇝` to concrete eval.

## What "sound" might mean

We deliberately do *not* provide a reference declarative relation for `⇝` to decide. That would bake in a particular design. Instead, here are some notions of soundness you might commit to:

- **Progress.** If `⋅ ⊢ E ⇝ T` (empty context), then `E ⇓ v` succeeds — either producing a value or diverging via `μ`, but never erroring out. No notion of compatibility needed; this is pure reachability.
- **Preservation up to solver-defined compatibility.** If `⋅ ⊢ E ⇝ T` and `E ⇓ v`, then `⋅ ⊢ v ⇝ T'` for some `T'` that you show is compatible with `T` under whatever relation you care to define internally. The "compatibility" relation here is *private* to your proof — you might call it `⊑`, or anything else, but it is not part of the public interface.
- **Logical relation / Kripke semantics.** Define a meaning function `⟦T⟧` that assigns each normal-form type a set of expressions, and show `Γ ⊢ E ⇝ T` implies every closing instance of `E` lies in `⟦T⟧`. No external notion of compatibility at all.
- **Observational / test-based.** The tests encode the minimum bar; the soundness file records whatever stronger claims you are willing to back up.

Whichever you pick, the soundness file should contain it as a stated-and-proved theorem, with no holes remaining.

## Hints (not requirements)

These are architectural sketches that have worked, partially worked, or almost worked in prior experiments on related calculi. None of them are mandatory — a totally different architecture is perfectly welcome, and in fact encouraged. They are collected here so you are not starting from a blank page if you would rather not.

- **Bidirectional split.** Internally distinguish a "synth" mode (infer a type from an expression) from a "check" mode (verify an expression against an expected type). Most bidirectional designs handle `μ` in check-mode by extending the context with the expected type as the self-variable's type, then verifying the body at that same type.
- **Subtyping as the workhorse.** Define an internal relation `Γ ⊢ A ⊑ B` that both compares two types and checks an expression against a type (they are the same operation in a kindless calculus). The existing Och/Simple branch in this repo takes this approach and is fully proven up to self-types.
- **Annotated μ.** Extend the syntax with `μx:T. body` where the annotation fixes the self-variable's type up front. Makes `μ` trivially checkable against its annotation, at the cost of a new syntactic form.
- **Seen-set / coinductive cycle detection.** Lazily unfold `μ` as you go and remember the pairs you have already started comparing; when you revisit a pair, close the cycle. This is the only approach known to handle the aspirational self-type tests, but soundness for it requires coinductive or step-indexed reasoning.
- **Logical relations.** Skip inductive subtyping entirely. Define a semantic interpretation `⟦T⟧ : Expr → Prop` by recursion on the type, and show directly that `⇝`'s output correctly describes the evaluation behaviour of the input. Heavy machinery but sidesteps the transitivity headaches.
- **Normalization + structural compare.** Normalize both sides to some canonical form via a separate reduction judgment, then do plain structural equality. Avoids most of the subtleties of subtyping but moves them into the normalization procedure.

Different approaches close different test categories. A bidirectional + inductive-subtyping solution will comfortably handle the first ~80% of the tests but hit a wall on self-types; a seen-set solution can clear the self-type tests but needs nontrivial soundness machinery. Budget accordingly.

## Suggested progression

1. **μ-free first.** Pretend `μ` does not exist in the language. Build `⇝` for the other five forms and pass the μ-free tests. This is already non-trivial: ascription, `⊤`-widening in application, and the existential nature of "the type of `F A`" are all live issues.
2. **Pick a notion of soundness and prove it** for the μ-free fragment.
3. **Add `μ` back.** Decide how `μ` should be abstractly interpreted — the hints above are starting points.
4. **Attempt the aspirational self-type tests** (`true_ ⊑ DBool`, the dependent Church-Bool introduction, etc.). These are genuinely hard — do not start here.

## Pitfalls and tips

- **Termination.** Lean wants total functions. Options: `(a)` an explicit `fuel : Nat` parameter (easiest, most honest), `(b)` `partial def` (forfeits provable termination — soundness theorems become unreachable), `(c)` a cleverly-chosen `termination_by` measure (hard — many obvious measures fail). Most solvers will want fuel.
- **Normal form is slippery.** `NFExpr` as a synonym for `Expr` is a fine starting point — "normal form" is then a convention you maintain, not a type-level guarantee. Strengthening it into an inductive with its own grammar helps you avoid bugs at the cost of more plumbing.
- **Self-types are productive cycles.** `true_ ⊑ DBool` unfolds to a subgoal that structurally contains *itself*. Plain inductive reasoning cannot close this. Coinductive, step-indexed, and seen-set approaches all work in principle.
- **Ascriptions are the sneaky case.** `(E : T)` on the left means "trust me, `E` has type `T`". On the right it means "check that `E` and your candidate agree, **and** that `T` is actually a valid type for it". Half-formed checkers usually get one direction wrong.
- **`⊤` is not a universe.** It is the top of the subtype lattice and doubles as the unit type — every expression is compatible with `⊤`. There is no `⊤ : ⊤` paradox because `⊤` is not a type *universe*, just a maximal element.

## Layout

```
lean/Och/Challenge/
  README.md         — this file
  Syntax.lean       — syntax with μ                  (KNOWN)
  Eval.lean         — concrete interpretation        (KNOWN)
  Synth.lean        — the ⇝ signature                (YOURS — body is sorry)
  Soundness.lean    — your soundness statement+proof (YOURS — everything is sorry)
  Tests.lean        — failing tests you must pass    (sorry'd until ⇝ works)
```

## How to take the challenge

1. Fork / branch.
2. Replace every `sorry` in `Check.lean`, `Soundness.lean`, and `Tests.lean` with real code/proofs.
3. `lake build` must pass with zero `sorry`s and zero `axiom`s beyond Lean's standard ones.
4. Write a short `SOLUTION.md` explaining the design decisions — especially *what soundness means* in your version.

Good luck.
