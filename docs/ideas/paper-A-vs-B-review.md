# Paper A (typed eval) vs Paper B (pure eval): Comparative Review

A neutral comparison of two architectural variants of the Och formalization. Both
specify the same source language; they differ in how `⇒` (eval), `⊑` (subtype),
and the typing layer are factored.

The two source documents:

- `/home/charlielidbury/repos/ochre/agda/paper-A-typed-eval.md`
- `/home/charlielidbury/repos/ochre/agda/paper-B-pure-eval.md`

---

## 1. Restatement of each variant

### Variant A — typed eval

`⇒` is partial: `Γ ⊢ e ⇒ v` only relates when `e` is well-typed in `Γ`. Every
canonical-head rule has well-formedness premises on its annotations
(`E-Lam` requires `Γ ⊢ A ⇒ A_v`), and `E-AppBeta` / `E-AppNeutral` / `E-Asc`
fire `⊑` checks on domains and ascriptions inline. The result is that the
existence of an `⇒`-derivation is itself a typing certificate: a `Value`
produced by `⇒` is well-typed by construction.

`⇒` and `⊑` are **mutually recursive**: `⇒` calls `⊑` for domain checks, and
`⊑` calls `⇒` (via `S-Neutral`'s argument WHNF and via `S-Ascent`/`ascent`)
for sub-term reduction. Top-level typing (`Γ ⊢ e : τ`) is a thin wrapper that
composes `⇒` and `⊑`.

There is also an `ascent(Γ, n)` partial function that walks neutral spines,
looks up the head's declared type in Γ, and substitutes argument values
through codomains; this is where `S-Ascent` fires and where `E-AppNeutral`
gets the function type to domain-check against. `ascent` itself calls `⊑`.

### Variant B — pure eval + bidirectional checker

`⇒` is purely computational. It β-reduces, fix-unfolds, projects ι (deferred
to eval), erases ascription, all without typing checks. Values may be
ill-typed garbage; `⇒` doesn't care. It is total modulo fuel.

A separate **bidirectional type-checking layer** (`infer ⇒t` and `check ⇐`)
walks the AST, calling `⇒` (for whnf) and `⊑` (for value comparison) but
neither calls back into the checker. The dependency graph is strictly
one-way: `infer/check → ⊑ → ⇒`.

`⊑` is structural on values, identical in structure to A's `⊑` except for
two specific differences in `S-Neutral` (no eval call on arguments — premise
on raw Syntax) and the absence of `S-Ascent` / `ascent`.

Top-level typing is just sugar for `⇐`.

---

## 2. Technical differences (concise)

| Aspect                       | Variant A                                                | Variant B                                                |
|------------------------------|----------------------------------------------------------|----------------------------------------------------------|
| `⇒` purpose                  | Partial: eval ∧ well-typedness                          | Total (mod fuel): eval only                              |
| `⇒` premises                 | Domain, annotation, ascription checks inline            | None                                                     |
| Dependency graph             | Cycle: `⇒ ↔ ⊑` (also via `ascent`)                       | DAG: `infer/check → ⊑ → ⇒`                                |
| Well-typedness witness       | The `⇒` derivation itself                                | The `infer/check` derivation                             |
| `S-Neutral` arg premise      | `Γ ⊢ a_v ⊑ a'_v` (with eval premises producing `a_v`)    | `Γ ⊢ a ⊑ a'` on raw Syntax (deferred)                    |
| `S-Ascent` rule              | Present (`n ⊑ τ` via `ascent(Γ, n) ⊑ τ`)                  | Absent                                                   |
| `ascent(Γ, n)`               | Defined; partial relation calling `⊑`                    | Not present                                              |
| `E-AppNeutral` output        | `stuck(n_v, a_v)` after domain check via `ascent`        | `stuck(n_v, a)`; arg unevaluated                         |
| `E-AppBeta` arg eval         | Eagerly eval'd, domain-checked, then substituted        | Substituted as Syntax, no check                          |
| `E-Asc`                      | Eval `e`, eval `T`, check `e_v ⊑ T_v`                    | Eval `e`, drop `T` entirely                              |
| Bidirectional check layer    | None — typing ≡ `⇒` + final `⊑`                          | Yes (`⇐`/`⇒t` mutually rec.), with `[I-*]` rules         |
| Inferred type at App         | Implicit via `ascent` on the resulting neutral           | Explicit in `[I-App]`: `f a ⇒t B[a/x]`                   |
| Subsumption                  | Implicit at top level (`Γ ⊢ v_e ⊑ v_τ`)                  | Explicit `[C-Sub]` (only checking rule)                  |
| What `[I-Iota]` infers       | N/A (no infer)                                           | `top` — interesting design choice (loses self info)      |

A few of B's `[I-*]` rules deserve separate attention because they aren't
just "the inverse of A":

- **`[I-Bot]`** says `bot ⇒t top`, not `bot ⇒t bot`. Reasonable
  (`bot ⊑ top` so this is sound), but A simply has `[E-Bot] bot ⇒ bot`
  and lets the lattice work itself out via `S-BotL`. B has chosen a
  specific inferred type where A leaves it implicit.
- **`[I-Lam]`** infers `λx:A. B` where `B` is the inferred body type.
  In Och, lambdas are their own types (the dependent function type
  `λx:A. B` literally is the type of `λx:A. b` when `b ⇒t B`). This
  is consistent with Och's "terms-are-types" philosophy.
- **`[I-Iota]`** infers `top`. This is *suspicious*. ι is meant to
  carry self-type information; saying `ι x:T. b` infers `top` throws
  that away and forces all uses of ι to be checked, never inferred.
  A's design avoids this: there's no inference in A, but in
  practice `ι x:T. b ⇒ ι x:T. b` and `S-IotaIntro` provides
  contextual unfolding.

---

## 3. Per-criterion evaluation

### 3.1 Soundness ergonomics

**A:** Soundness statements collapse into a single relation. "`Γ ⊢ e : τ`"
literally means "the `⇒` and `⊑` derivations exist". Substitution lemmas
need to be stated for the joint relation; you cannot prove preservation
for `⇒` independently of `⊑` because they call each other. The current
soundness blocker — eval-preservation in the [App] case (per
`MEMORY.md`'s "Eval preservation status") — likely *mirrors* the
mutual-recursion structure: lambda inversion in `⊑` requires a typed
lambda, which requires `⇒` to have produced it, which requires
`⊑` again on the domain. This is the Zwanenburg circularity warning
made flesh.

A's saving grace for soundness: there's no separate "well-typed values"
predicate to maintain as an invariant. The relation *is* the invariant.

**B:** Each layer can be reasoned about separately:

1. `⇒` is a **partial function** modulo fuel. Confluence and progress can
   be stated as pure rewriting properties — no typing in sight.
2. `⊑` is a **purely structural relation** on values. Reflexivity,
   transitivity (admissibility), antisymmetry — pure structural induction.
3. `infer/check` is **the soundness theorem**: "if `⇐` succeeds then `⇒`
   produces a value `v_e` with `v_e ⊑ τ_v` (after both are eval'd)".

This is the standard PCUIC / Lean / Agda decomposition. The standard
metatheory toolbox applies. Each lemma is smaller; the proofs compose.

The cost in B: you have to prove "`⊑` is sound for arbitrary values" —
including ones that are in fact ill-typed. This is harder to *state*
informally but cleaner formally because there's no implicit
well-typedness assumption.

**Verdict on this criterion: B is meaningfully easier for soundness.**
The mutual cycle in A is exactly the structure that makes Zwanenburg-style
proofs hard, and the fact that the project is currently stuck on the App
case is consistent with this. B doesn't have that cycle.

### 3.2 Implementation feasibility (Agda)

**A:** Agda's positivity and termination checkers will find the mutual
recursion `⇒ ↔ ⊑` annoying. Specifically:

- The relations are mutually inductively defined. That works. But
  proofs by induction on `⇒`-derivations will need to recurse into
  `⊑`-derivations, which need to recurse into `⇒`-derivations again.
  This is **fine in principle** but requires a well-founded measure on
  pairs.
- `S-Ascent` and `E-AppNeutral` go through `ascent`, which is itself
  a partial relation calling `⊑`. That's *three* mutually defined
  things, not two.
- The current `Och/Typed.agda` uses induction-induction for
  `Term ↔ Ctx ↔ ∈`. Adding `⇒ ↔ ⊑ ↔ ascent` makes it
  induction-induction-induction-induction-induction. Agda can do this,
  but the boilerplate compounds.

**B:** The DAG `infer/check → ⊑ → ⇒` maps onto Agda layered modules
trivially: define `⇒` first as its own inductive, then `⊑` as a separate
inductive that may *use* `⇒` (e.g. eval premises in subtype rules can
reference an already-defined `⇒`), then `infer/check` on top. No mutual
recursion between layers means no induction-induction across them.

Within `⊑` itself there's still the issue of `S-Lam`'s body comparison
needing to compose with eval, and `S-IotaIntro`'s `b[v/x]` substitution
producing Syntax that needs eval before recursive `⊑`. Both papers
note this as TBD; B's strict layering makes the resolution natural
("define `⊑_Syntax` as the composition", well-founded by structural
size of values).

**Verdict: B is much easier to implement in Agda.** The strict layering
is a real Agda ergonomic win.

### 3.3 Performance / algorithmic complexity

This matters only when we eventually generate an executable kernel.

**A:** Inline checks in `⇒` mean every β-reduction triggers a domain
subtype check. If a function is applied many times, the same domain
check fires repeatedly. Without memoization, this is asymptotically
worse than B.

`E-AppNeutral` calls `ascent`, which itself does typing work, on every
neutral application. For a deep neutral spine `f a₁ a₂ … aₙ`, ascent is
quadratic in the spine length (each step substitutes through the
codomain, which contains earlier substitutions). With domain checks
firing at each level, this compounds.

**B:** `⇒` is just reduction. Bidirectional type checking is *one pass*
over the AST. Subtype calls happen at `[C-Sub]` and at `[I-App]`'s
domain check; the WHNFs are computed lazily.

This matches the "lazy delta" pattern that all production kernels use.

**Verdict: B has clearly better algorithmic structure for an
implementation.** A could be made performant via memoization, but B
naturally avoids the redundant work.

### 3.4 Conceptual cleanliness

This is the most subjective axis, and where A has its strongest case.

**A's claim:** "`⇒` is a single relation that captures both *what e
reduces to* and *that e is well-typed*. There's only one thing to talk
about." This is genuinely appealing. The Yang-Oliveira λI≤ ambition is
the same: collapse the typing/conversion duality into one relation.

**B's claim:** "Each judgment has a single, distinct purpose. `⇒` is
reduction. `⊑` is structural type comparison. `infer/check` is the type
system. Composing them gives the typing relation." This is the
mainstream PCUIC/Lean/Agda partition.

The deeper question: **what does Och's "terms-are-types" philosophy
actually want from these judgments?**

Och's stated philosophy (from `docs/what-is-och.md`): "Types are sets of
values. The most precise type of a term is the term itself. Typing is
abstract interpretation. Subtyping is set inclusion."

This philosophy says **typing IS evaluation under a wider semantic
interpretation**. The natural reading is: there's one operational story
(eval), and a separate semantic story (subset / subtype) that explains
when one piece of code is more approximate than another.

Both A and B can express this. But:

- A's `⇒` is *not* abstract interpretation — it's normal eval *plus
  bookkeeping*. Mixing the bookkeeping into the same relation conflates
  two different things.
- B's `⇒` is the operational story; `⊑` is the inclusion-style relation;
  `infer/check` is "compute the abstract interpretation" — which in Och
  is "compute the most precise type via subsumption". This actually maps
  better onto the philosophy.

That said, A has one conceptual win B doesn't: in A, **`Value` =
"output of `⇒`" = "well-typed canonical form"**. There's no "garbage
values" concept. Both papers explicitly note that a `Value` is a
syntactic shape and may be ill-typed; A's `⇒` then admits only the
well-typed subset, but A's *value grammar* still includes garbage. So
this win is partial — it shows up in informal descriptions ("a Value
produced by `⇒` is well-typed") but the value grammar admits the same
ill-typed garbage as B.

**Verdict on cleanliness: roughly a wash.** A is cleaner in the
"single relation" sense; B is cleaner in the "single concern per
relation" sense. Och's stated philosophy is *slightly* better matched
by B because the philosophy distinguishes operational eval from
semantic inclusion.

### 3.5 Decidability / termination

**A:** Mutual recursion makes a fuel scheme have to budget *across*
both relations. If `⇒` calls `⊑` calls `⇒` calls `⊑`, when does
fuel decrement? You need a fuel counter that's shared, and you need
to argue that progress happens somewhere. Doable, but more careful.

`ascent(Γ, n)` is also problematic: it walks the neutral and looks up
context types. If the context contains arbitrary terms (which it does —
contexts in dependent type theory contain types-as-terms), `ascent`
can recursively trigger `⊑` on context contents, which recurses into
`⇒` on context contents, etc.

**B:** `⇒` is the only place reduction happens. Fuel goes there.
`⊑` recurses on value structure (no eval premises *directly*, except
the deferred Syntax-vs-Value question on `S-Neutral` arguments —
which the paper flags as TBD). `infer/check` is structural on the
AST and terminates trivially.

The total termination story is: `⇒` is fuel-bounded; everything else is
structural. This is *exactly* the Lean 4 kernel story.

**Verdict: B has cleaner termination/decidability bounds.**

### 3.6 Extensibility

Suppose Och later adds a feature — say, dependent pairs (`Σx:A. B`)
with projections, or refinement types `{x:A | P x}`, or a primitive
match construct.

**A:** Each new constructor needs:
- An `⇒` rule (with well-formedness premises).
- Possibly an `⊑` rule.
- Possibly modifications to `ascent`.
- Soundness arguments must be redone over the joint relation.

For a feature like match, where elimination triggers reduction *and*
needs scrutinee-type inference, you need to weave both into `⇒` while
preserving the mutual-recursion invariants. This is exactly the work
PCUIC's authors had to do for cumulativity-with-inductives (Timany &
Sozeau FSCD 2018, cited in the survey).

**B:** Each new constructor needs:
- An `⇒` rule (just reduction).
- Possibly an `⊑` rule.
- An `[I-*]` and/or `[C-*]` rule.

Each layer can be extended independently. Adding match: extend `⇒`
with case-reduction; extend `[I-*]` with `[I-Match]` that infers a type
from branches; the existing `[C-Sub]` handles subsumption.

**Verdict: B extends cleaner.** This is actually the *strongest*
practical argument against A — Och is a research calculus that *will*
gain features, and refactoring across a mutual relation each time is
costly.

### 3.7 Match with Och's stated philosophy

Both Och papers cite the kernel-conversion-survey approvingly. The
survey is unambiguous about what mainstream kernels do (B-style), but
the user's prompt explicitly cautions against treating "matches the
mainstream" as a reason to prefer something.

So let's check Och's philosophy directly:

1. **"Types are sets of values."** Both variants accommodate this; the
   subtype relation expresses set inclusion. Equally well in A and B.

2. **"The most precise type of a term is the term itself."** This is
   `[S-Refl]: v ⊑ v`. Both have it. Equally well.

3. **"Typing is abstract interpretation."** This is the deepest one.
   Abstract interpretation has a *concrete* semantics and an *abstract*
   semantics; the abstract one over-approximates the concrete one. The
   natural mapping is:
   - Concrete = `⇒` (eval, what the program does).
   - Abstract = `⇒t` or "the type of `e`".
   - Soundness = "concrete ⊑ abstract".

   B's bidirectional `⇒t` *literally* implements this. A doesn't have
   a separate "type-of" computation; it folds well-typedness into eval
   itself.

   **Variant B more directly realizes "typing is abstract interpretation".**

4. **"Type annotations only lose information."** Both express this via
   ascription. B has `[I-Asc]: (e:T) ⇒t T` — the ascription becomes the
   inferred type, *widening* away from `e`'s natural type. A has
   `E-Asc` which checks `e_v ⊑ T_v` and erases the annotation. Both
   work; B's is closer to "the annotation widens" because it explicitly
   produces `T` as the inferred type.

5. **Subsumption-based.** Both have it. Equally well.

**Verdict: B's bidirectional layer is a better fit for "typing is
abstract interpretation" because abstract interpretation needs a
distinct abstract semantics.** The user said don't pick "matches
mainstream" as a tie-breaker; the philosophy match here isn't about
matching mainstream, it's about Och's *own* stated framing.

---

## 4. Honest weaknesses

### Weaknesses of Variant A

1. **Mutual recursion is the existing soundness blocker.** Per
   `MEMORY.md`: "[App] case is last soundness blocker; needs lambda
   inversion or logical relation." Lambda inversion in `⊑` requires
   the lambda to be well-typed, which is a fact about `⇒`, which
   requires the inversion property of `⊑`. A's design *causes* this
   cycle.

2. **`ascent` is a third mutually-recursive relation.** Not just `⇒` and
   `⊑` — `ascent` calls `⊑` and is called by both. The metatheoretic
   complexity is at least cubic.

3. **`E-AppBeta`'s domain check duplicates work.** Every β-reduction
   re-checks the domain even though the function was presumably already
   well-typed when constructed. (Implementation: memoization can fix
   this; metatheory: the rule still has the premise.)

4. **The `Value` grammar still admits ill-typed garbage** despite the
   prose claiming "Value produced by `⇒` is well-typed by construction".
   Both papers admit `Value` doesn't mean well-typed. So A's
   conceptual win — "Values are well-typed" — only holds for *images
   of `⇒`*, not for the `Value` type itself. The Agda type system
   can't enforce the distinction without re-introducing `Term Γ τ`-style
   intrinsic typing.

5. **No inference, only checking + composition.** A's top-level typing
   is `e ⇒ v_e`, `τ ⇒ v_τ`, `v_e ⊑ v_τ`. There's no way to ask "what's
   the type of `e`?" without already having a candidate τ. For an
   abstract-interpretation language whose whole pitch is "compute the
   most precise type from the term", this is a step backward.

6. **Coinduction story is muddier.** `S-FixCoind` is coinductive; `⇒`
   has fix unfolding, which can also be coinductive. The mutual
   recursion makes the coinductive/inductive split harder to manage —
   are `⇒`-derivations inductive and `⊑`-derivations coinductive?
   What does that mean for the joint induction principle?

### Weaknesses of Variant B

1. **`[I-Iota]` is weak.** It infers `top`, throwing away the self-type
   information that ι is supposed to carry. To use ι you must always
   *check* against an expected type. For a feature whose entire point
   is to express things you couldn't otherwise — Cedille-style
   self-types are non-trivial to encode — this is a real loss. (Could
   be fixed: `[I-Iota] ι x:T. b ⇒t ι x:T. b` would mirror `[I-Lam]`.
   The paper as written is just an early draft.)

2. **Two relations to keep in sync.** When you change `⇒`'s rules,
   you may need to update `infer/check`'s rules to match. With A,
   one change covers it. (Practical impact: small if `⇒` is stable.)

3. **`[C-Sub]` is overly general.** Falling back to `⇒t` + `⊑` for
   every checking goal misses opportunities for type-directed
   elaboration. E.g., checking `λ` against a known function type
   should drive elaboration of the body in the *expected* codomain
   context. A doesn't have this issue (no checking phase), but a
   refined B should specialize `[C-Sub]` for specific shapes. (The
   paper acknowledges this.)

4. **`S-Neutral` argument premise on raw Syntax is unresolved.** Both
   papers note this; B punts harder because it doesn't have the
   eval-on-the-fly machinery A wires into the relation. B will need
   to either lift `⊑` to Syntax (extending the dependency chain) or
   eval first then compare (a third meta-level relation).

5. **Equirecursion with B's pure eval is subtle.** When comparing
   `fix x:A. b ⊑ T` for non-fix `T`, B's eval would need to unfold
   `fix` to make the structural comparison work. The paper notes this
   ("eval can be made to produce maximally-unfolded values when
   comparing against a fix") but doesn't pin it down. A's typed
   eval has the same problem; both punt.

6. **B doesn't currently enable Och's vision of "the most precise
   type is the term itself" cleanly.** `[I-Lam]` infers a function
   *type* (`λx:A. B`), not the function term itself. To make the
   "term-is-its-own-most-precise-type" view work, you'd want
   `[I-X] e ⇒t e` for canonical forms (or close to it). B's
   `[I-*]` rules as written reduce inferred types to "type-shaped"
   terms in a way that loses precision. **This is a real philosophy
   match issue** — A's `[E-Lam] λx:A. b ⇒ λx:A. b` is more faithful
   to "the term is its own type". *(See section 3.7 and the
   recommendation below — this is the crux.)*

---

## 5. Recommendation

**Recommend Variant B as the metatheory baseline, with one significant
modification: change inference rules so canonical forms infer
themselves.**

The reasoning, in order of importance:

### Primary reasons to choose B

1. **The current soundness blocker (App-case lambda inversion) is
   structurally caused by A's mutual recursion.** B doesn't have
   that cycle. The most efficient way to unblock soundness is to
   eliminate the cause, not to keep proving harder lemmas about it.
   This dominates other considerations.

2. **Agda implementation feasibility.** The DAG `infer/check → ⊑ → ⇒`
   maps onto Agda modules with no induction-induction across layers.
   A's three-way mutual recursion (`⇒ ↔ ⊑ ↔ ascent`) on top of the
   existing `Term ↔ Ctx ↔ ∈` indinction-indinction is a real
   complexity bomb.

3. **Extensibility.** Och will gain features (μ, dependent pairs,
   match, unions, atoms — see `what-is-och.md`'s staging table).
   Each addition requires re-doing soundness arguments in A's joint
   relation; in B, each layer extends independently.

4. **Termination/decidability story is cleaner.** Fuel lives in `⇒`;
   `⊑` is structural; `infer/check` is on AST size. Lean 4's kernel
   has the same architecture and admits non-termination — exactly
   what Och wants.

### The crucial fix to B before adopting

`[I-Iota]: ι x:T. b ⇒t top` and `[I-Lam]: λx:A. b ⇒t λx:A. B` (where
B is the inferred body type) **violate Och's "term is its own most
precise type" philosophy**. They project to type-shaped terms instead
of preserving the term itself.

The fix is straightforward: make canonical forms infer themselves:

```
[I-Lam']
Γ ⊢ λx:A. b ⇒t λx:A. b                  // self-inference

[I-Iota']
Γ ⊢ ι x:T. b ⇒t ι x:T. b                // self-inference

[I-Fix']
Γ ⊢ fix x:A. b ⇒t fix x:A. b
```

with all the well-formedness premises preserved. This is consistent
with Och's `[S-Refl]` (every term is at least its own subtype) and is
exactly what A's `[E-Lam]`, `[E-Iota]`, `[E-Fix]` do for `⇒`.

`[I-App]` then needs adjustment: instead of inferring `B[a/x]` (which
assumes `f`'s type is a function-shape), it should infer the
application of the inferred types: `f a ⇒t f' a` where `f ⇒t f'` and
`a ⇒t a'`. Subsumption handles converting these into "real" types
when needed.

This is the abstract-interpretation reading made concrete: `⇒t` is
"abstract eval" — it produces the maximally-precise type by tracking
the term itself, only widening when forced (by subsumption rules
like `[S-Top]`).

**With this fix, B becomes much closer to A's "types are terms" vision
while keeping the layered architecture.**

### Reasons not to choose B (and why they don't dominate)

- *"A is more faithful to Och's 'one relation' philosophy."* If
  Och's vision *is* one unified relation, then A is more direct.
  But Och's actual stated philosophy (`what-is-och.md`) is "typing
  is abstract interpretation", which wants two semantic levels —
  that's B. Yang & Oliveira's λI≤ unifies declaratively but
  *the algorithm* falls back to the standard layered approach
  anyway. There's no working algorithmic precedent for the unified
  approach in dependent settings (per the survey).

- *"A makes 'well-typed values' a derivable property."* True, but
  only on values produced by `⇒`. The `Value` grammar still admits
  garbage in both. The win is rhetorical, not structural.

- *"B requires writing more rules."* Yes — but each rule is smaller
  and independent.

### When you might prefer A

- If you discover that B's `⊑` requires nontrivial type information
  about its arguments to make some rule decidable (currently nothing
  in either paper requires this — `⊑` is structural in both — but if
  a future feature needed it, you'd be back to A's coupling).

- If you specifically want to prove a *very general* metatheorem
  about Och in the Yang-Oliveira style and don't care about the
  algorithm. (For Och, where the algorithm is the point — Ochre
  is a programming language, not a paper-only calculus — this isn't
  the situation.)

- If the soundness work in A is *almost done* and you'd lose
  considerable proof investment by switching. Per `MEMORY.md`'s
  status this doesn't appear to be the case — App is the last
  blocker and it's been blocking.

---

## 6. Summary

| Criterion                    | A wins                          | B wins                                | Tie |
|------------------------------|---------------------------------|---------------------------------------|-----|
| Soundness ergonomics         |                                 | Layered proofs; no cycle              |     |
| Agda implementation          |                                 | DAG > 3-way mutual rec                |     |
| Performance                  |                                 | Lazy WHNF; no redundant checks        |     |
| Conceptual cleanliness       | Single relation                 | Single concern per layer              | ~   |
| Decidability/termination     |                                 | Fuel localized to `⇒`                 |     |
| Extensibility                |                                 | Layer-independent additions            |     |
| Och philosophy match         | "types are terms" via self-eval | "abstract interpretation" via `⇒t`    | ~   |

A wins on *unification rhetoric*; B wins on *every practical axis*.
Och's philosophy is mixed — A's `⇒` keeps canonical forms as themselves
(matching "term is its own type"); B has a separate type-inference
relation (matching "typing is abstract interpretation"). The
"infer-self" fix to B captures both.

**Recommendation: Variant B with self-inferring canonical forms.**

---

## 7. Notes for execution if B is chosen

- The Agda layering should be: `Eval.agda` (`⇒` only) → `Sub.agda`
  (`⊑` referencing `⇒` for sub-term whnf) → `Infer.agda`
  (`⇒t`, `⇐` referencing both).
- Resolve `S-Neutral`'s "argument is Syntax" issue by lifting `⊑` to
  Syntax via `⇒` — or by always eval'ing arguments first inside
  `S-Neutral`. Either is fine; the paper currently punts.
- Fix `[I-Iota]`. As written, it loses information.
- Consider: is `[C-Sub]` the *only* checking rule, or do you want
  `[C-Lam]` (check λ against a function type, drives body
  elaboration)? For Och as currently spec'd, `[C-Sub]` is enough,
  but adding shape-driven checking rules will help diagnostics.
- The current soundness blocker (App-case eval-preservation) should
  be revisited under B's setting: the statement becomes "if
  `Γ ⊢ e ⇐ τ` then `Γ ⊢ e ⇒ v` and `Γ ⊢ v ⊑ τ_v`", and the
  proof goes by induction on `⇐` derivations, with no cycle
  through `⊑`.
