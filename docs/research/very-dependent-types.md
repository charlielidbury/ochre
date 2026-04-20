# Very Dependent Types

A research report on Jason Hickey's **very dependent types** (VDTs): what
they achieve, how they are typed, and how they relate to Och's existing
`fix` system and its proposed `iota` (self-type) extension.

Much of the interest here is that VDTs occupy an unusual point in the
design space — they are older than modern self types, predate Cedille by
two decades, and yet capture a self-reference pattern that neither `fix`
nor `iota` captures cleanly on its own. For a project like Och, where
"fix and iota might be the same thing" is an open question (see
`docs/ideas/merge-fix-iota.md`), VDTs are a useful third data point.

---

## Part 1: What Very Dependent Types Are

### 1.1 Origin

VDTs were introduced by **Jason Hickey** in his 1996 MIT thesis
*"Formal Objects in Type Theory Using Very Dependent Types"* and
developed inside the **Nuprl / MetaPRL** constructive type theory
tradition. Hickey's motivating problem was encoding **objects and
records with inter-field dependencies** — specifically, a record where
the type of a later field may depend on the *values* of earlier fields
— inside a type theory that natively has only Π and Σ types.

The idea, one sentence:

> A very dependent function type `{f | x:A → B(f, x)}` is the type of
> functions `f : A → …` such that for every `x : A`, `f x` inhabits
> `B(f, x)` — the codomain is allowed to mention `f` itself.

That single generalisation — letting the codomain refer to the function
being typed — turns out to subsume records, streams, and several
induction-like patterns.

### 1.2 The one-line comparison

| Type former                | Codomain depends on…          |
| -------------------------- | ----------------------------- |
| `A → B`                    | nothing                       |
| `(x : A) → B(x)`           | the argument `x`              |
| `{f \| x : A → B(f, x)}`   | the argument `x` AND `f` itself |

A value of the very dependent type is literally a function. The VDT
only changes what it means to say "this function is well-typed" — the
type checker now sees not just the argument but the function being
defined, so it can express "the type of `f x` may refer to the
behaviour of `f` on other inputs."

### 1.3 What it lets you write

Four canonical examples make the expressiveness concrete.

**Dependent records.** A record with fields `f₁, …, fₙ` where `fₖ`'s
type depends on the values of `f₁, …, f_{k-1}` can be encoded as a
function `f : Fin n → …` where `f k` returns the k-th field. The type
of `f k` is allowed to mention `f 0, …, f (k-1)` — exactly what VDTs
permit. Hickey's original motivation.

**Dependent streams.** A stream where `stream n`'s type may refer to
`stream 0, …, stream (n-1)` — e.g. "element n+1 is a proof that
element n is sorted" — is a VDT with `A = ℕ`.

**Self-typed functions.** If `B(f, x) = P (f x)` where `P` is some
predicate, the VDT says "for every `x`, `f x` satisfies a predicate
that mentions `f x` itself." This is very close to self types.

**Iteration with accumulating types.** A function `f` where the *type*
of `f (n+1)` is some function of the type of `f n` — inductive-
recursive definitions live in this neighbourhood.

What VDTs do **not** give you directly is general recursion on the
*value* level. A VDT says the function *has* a certain (self-referential)
type; it does not say "run this function by unfolding." Value-level
recursion is orthogonal — in Nuprl it is provided separately via `fix`
or `Y`.

---

## Part 2: How They Are Typed

### 2.1 The regularity / well-foundedness condition

The obvious objection to `{f | x:A → B(f, x)}` is circularity: if
`B(f, x)` can say anything about `f`, why is this well-defined?
Couldn't `B(f, x) = ¬(f x ∈ f x)` produce a paradox?

Hickey's answer is a **well-foundedness condition**: there must be a
well-founded order `≺` on `A` such that `B(f, x)` only inspects `f y`
for `y ≺ x`. Formally, `B` is required to be **monotone** with respect
to a certain partial approximation order on `f` — equivalently,
`B(f, x)` is determined by the restriction of `f` to `{ y | y ≺ x }`.

With this, the type is built up inductively: for the ≺-minimal `x`,
`B(f, x)` does not mention `f` at all, so it is a plain type. For the
next level, `B(f, x)` can mention `f` on minimal elements, which are
already defined. And so on. The fixed-point exists and is unique
because each "slice" of `f` is determined by strictly earlier slices —
this is exactly the same pattern as well-founded recursion on `A`,
lifted one level to act on the *type* of `f` rather than its *value*.

**Practical consequence:** not every specification of the shape
`B(f, x)` is a legal VDT. The type checker (or the author) must
discharge a well-foundedness obligation. In Nuprl this is done by
providing the order `≺` explicitly; in more recent expositions it is
usually implicit, with the body syntactically restricted (e.g. `f` may
only be applied to variables proved smaller than `x`).

### 2.2 Formation, introduction, elimination

Writing `{f | x:A → B}` for the VDT (`B` may mention both `f` and `x`):

**Formation.**
```
    Γ, f : (x:A → ⊤), x : A ⊢ B : Type
    (+ well-foundedness of B w.r.t. some ≺ on A)
    ─────────────────────────────────────────
    Γ ⊢ {f | x:A → B} : Type
```
`B` is checked as a type under the assumption that `f` is *some*
function on `A` (the particular function being defined is not yet
available — hence `⊤` codomain as a placeholder). The well-foundedness
side-condition is what makes the definition stratified.

**Introduction.**
```
    Γ, x : A ⊢ t(x) : B[f := (λy. t(y)), x := x]
    ────────────────────────────────────────────
    Γ ⊢ (λx. t(x)) : {f | x:A → B}
```
To inhabit the VDT with `λx. t(x)`, show that for each `x`, `t(x)`
inhabits `B` with `f` instantiated to the very function being defined.
This is the "tie the knot" step — you substitute the closed function
back into its own codomain specification.

Note the structural similarity to Fu–Stump `selfIntro`:
```
    Γ ⊢ t : T[x := t]
    ─────────────────
    Γ ⊢ t : ι x. T
```
Both rules substitute the term being defined into its own type, and
both rely on some well-foundedness / positivity condition to avoid
circularity. The difference is that the VDT rule does this once per
application of `f`, not once per use of the term.

**Elimination.** Two equivalent forms:

1. *Applicative:* if `f : {g | x:A → B}` then `f a : B[g := f, x := a]`.
2. *View / subsumption:* `{g | x:A → B}` is a subtype of `(x : A) →
   B[g := f, x := x]` once `f` is a known specific element of the VDT.

Most presentations fold (2) into (1) — the only way a VDT is used is by
application, and each application produces a term whose type is `B`
with `g` instantiated to the very `f` you applied.

### 2.3 Relation to Π and Σ

VDTs are **not** strictly more expressive than the Π+Σ+inductive-types
fragment of CIC — you can encode many VDTs as Σ-types (a dependent
record *is* a dependent pair, iterated). What VDTs buy is **a
presentation that is a function, not a tuple**. You get to write

```
get : Fin n → (k : Fin n) → Field k
```

and apply it, rather than projecting out of a nested Σ. For object
encodings, method dispatch, and records with many fields, this is a
substantial syntactic win, and it composes cleanly with higher-order
code that treats records as functions.

### 2.4 Where the metatheory lives

Nuprl's metatheory is **extensional and untyped-at-the-bottom**: types
are inductively defined families of partial equivalence relations
(PERs) on untyped terms. VDTs fit this framework naturally — the PER
for `{f | x:A → B}` is defined by induction along the well-founded
order `≺`, exactly mirroring the stratified construction in §2.1.

In more modern, intensional, definitional-equality-driven settings
(Coq, Lean, Agda), VDTs have no direct implementation. The closest
analogue is **induction–recursion** (Dybjer) or **induction–induction**,
which allow a type family and a function into it to be defined
simultaneously. Induction–recursion is arguably the direct descendant
of VDTs in the intensional tradition; it keeps the "function's codomain
depends on earlier values of the function" pattern but requires the
function and type to be declared as a combined schema rather than as an
anonymous type former.

---

## Part 3: Relation to Och's `fix`

### 3.1 What Och's `fix` actually does

Currently in Och:

```
fix : (T → T) → T    -- schematic; in the implementation, with annotation
```

with two evaluation rules:

- **Concrete:** unroll. `concEval (fix (lam f : T. body)) =
  concEval (body[f := fix …])`. May diverge; that is intended.
- **Abstract:** stop at the annotation. `absEval (fix (lam f : T. body))
  = T`. Termination anchor.

The annotation `T` is load-bearing: it lets abstract evaluation
describe the function without entering the body.

### 3.2 What `fix` shares with VDTs

**Both are self-referential constructs where a name refers to the thing
being defined.** In `fix (lam f : T. body)`, `f` in the body is the
whole `fix` expression. In `{f | x:A → B(f, x)}`, `f` in `B` is the
whole VDT (or, equivalently, the particular function being typed).

**Both need a finite summary to reason about without unfolding.** For
`fix`, the summary is the annotation `T`. For VDTs, the summary is the
well-founded order `≺` plus the constraint that `B(f, x)` only reads
`f` on ≺-predecessors. Different mechanisms, same underlying problem:
"I need to talk about this self-referential thing without chasing the
loop."

### 3.3 Where they diverge

**`fix` is value-level; VDTs are type-level.** `fix` produces a term
whose *value* is defined by unrolling. VDTs describe a *type*
inhabited by terms whose *codomain behaviour* is recursively specified.
You can have a VDT whose inhabitants are not themselves recursive
functions at all — every inhabitant is just some ordinary function that
happens to satisfy the self-referential spec.

**`fix` is unrestricted; VDTs are well-founded.** Och's `fix` has no
termination or well-foundedness obligation — it is fine with divergent
functions; concrete evaluation just loops. VDTs require a well-founded
order up front; without it, the type is not well-formed.

**The dual-evaluation split does different work.** For `fix`, concrete
and abstract evaluation do structurally different things (unroll vs.
return annotation). For a VDT, there is nothing for concrete evaluation
to "do" — the VDT is a type; its inhabitants are plain functions whose
concrete behaviour is unchanged by the VDT wrapper. The VDT's
stratification lives entirely in the type checker.

So `fix` and VDTs are **siblings, not variants**: both exploit
self-reference, but at different layers (values vs. types) and with
different termination contracts (none vs. well-founded).

---

## Part 4: Relation to Och's `iota` (Self Types)

Och's `iota` — proposed but not implemented; see
`docs/research/self-types-for-och.md` — is much closer to VDTs than
`fix` is. Here the comparison is fine-grained.

### 4.1 Syntactic distance

Side by side:

```
iota x. T              -- self type (Fu–Stump / Cedille)
{f | x:A → B(f, x)}    -- very dependent type (Hickey / Nuprl)
```

Rewriting the VDT as a binder:

```
ι_fn f. (x:A) → B(f, x)
```

In this form, the only syntactic difference is that VDTs wrap a Π, and
self types wrap an arbitrary `T`. A VDT is *essentially* a self type
whose body is a dependent function — except the binder `f` ranges over
functions only, not over arbitrary inhabitants.

### 4.2 Semantic distance

The semantic difference is more interesting.

**Self types bind "the term itself":** `t : iota x. T` means `t`
satisfies `T[x := t]`. The self-reference is to the whole inhabitant as
a single object. This is what lets a Church numeral carry its own
induction principle: `n : iota n. (P : Nat → Type) → … → P n`.

**VDTs bind "the function itself, at every point":** `f : {g | x:A →
B(g, x)}` means that for every `x : A`, `f x` satisfies `B(f, x)`. The
self-reference is to the function viewed pointwise, with a stratified
dependency structure. This is what lets you say "`f 5`'s type depends
on `f 4`'s value."

**Neither subsumes the other cleanly.** A self type over a function
type, `iota f. (x:A) → B`, can refer to `f` in `B`, and if Hickey's
well-foundedness is imposed externally, this is *exactly* a VDT. So in
a permissive enough self-type system with a well-foundedness check,
VDTs are a definable fragment. Conversely, a VDT whose `A` is `Unit`
(or any singleton) collapses to a self type `iota x. B(⟨⟩, x)` up to
trivial currying — so self types are also approximately "VDTs with no
domain." They overlap heavily; they are not the same.

### 4.3 The annotation question

Victor Maia's termination fix for Kind2 (annotating the self binder
with its type: `$(self : T). …`) is striking when compared to Hickey's
well-foundedness condition. Both are ways to attach a **finite
termination anchor** to a self-referential type so that the checker
does not diverge. Maia's annotation is an arbitrary upper-bound type;
Hickey's `≺` is a strict well-founded order. They solve the same
problem with different tools: Maia gets decidability of equality
checking via a syntactic similarity check on the annotation; Hickey
gets a semantic proof of well-foundedness via the stratified
construction.

For Och, this suggests a design axis that is not about "self types vs.
VDTs" but about **how the termination anchor is provided**: as a type
annotation (Kind2), as a well-founded order (Nuprl), as a domain
annotation on a fix binder (Och today), or implicitly via a termination
checker (Agda).

### 4.4 What VDTs buy over `iota`, if anything

For the specific workloads that motivate iota in Och (dependent
elimination of Church encodings, typing `appendArrays`), VDTs offer no
obvious win — iota is sufficient, and is already the well-studied tool.

For workloads that iota handles *awkwardly* — records with many fields,
streams with element-wise dependencies, object encodings — VDTs offer a
more direct presentation. Hickey-style `{f | x:A → B(f, x)}` lets you
write the thing you want directly, whereas iota-encoding the same
record forces you through a Church encoding of tuples that carries its
own induction principle. For Och's current goals this is academic;
if/when Ochre wants first-class records with dependent fields, VDTs
become relevant.

---

## Part 5: Relation to the Proposed `mu` Unification

`docs/ideas/merge-fix-iota.md` proposes that `fix` and `iota` are the
same primitive — a single `mu (x : T). body` distinguished only by the
evaluation mode (concrete unrolls, abstract normalises under the
binder). Where do VDTs sit in that picture?

**VDTs are not a third thing in the mu worldview — they are a pattern
you can express in it.** If `mu` subsumes both `fix`-style term
self-reference and `iota`-style type self-reference, then a VDT is just
`mu (f : (x:A) → …). (x:A) → B(f, x)` — a `mu` binder at a function
type, used in type position, where the body references `f` under a
well-foundedness obligation.

This reframing clarifies two things:

1. **Och's annotation on `mu` plays the role of Hickey's `≺`
   *partially*.** It gives the checker something finite to compare
   (Victor's trick), but it does not by itself enforce that `B(f, x)`
   only reads `f` on smaller `x`. If Och ever cares about *decidability*
   of VDT-like patterns (not just termination of the equality check),
   a separate well-foundedness obligation would need to be reintroduced
   — or accepted as undecidable, which Och currently accepts anyway.

2. **The "stuck application of an abstract self-typed value" question
   in the iota work is exactly the VDT elimination question.** When
   `f` has abstract type `iota f. (x:A) → B(f, x)` and we encounter
   `app f a`, the type of the result is `B[f := f, x := a]`. Hickey's
   VDT elimination rule is precisely "substitute the function into its
   own codomain at each application site." Och's open question about
   how absEval should handle this application — whether it needs
   type-directed evaluation, a stuck-term type tag, or something else —
   is not a new problem invented by self types; it is the same problem
   Nuprl solved via its PER semantics thirty years ago.

Whether the Nuprl-style solution ports to Och's abstract-interpretation
semantics is an open question. PER semantics is extensional and
untyped-at-the-bottom; Och is intensional and type-directed. The
well-founded construction of the VDT's PER does not obviously translate
into a terminating abstract evaluator. But the *shape* of the problem
and the *shape* of Nuprl's answer are close enough that the Nuprl
literature is worth mining.

---

## Part 6: Takeaways for Och

The point of this report is not to argue for adding VDTs to Och — the
self-type / `mu` direction already covers the motivating use cases and
is closer to Och's existing design. But VDTs are a useful third
reference point for three reasons:

**They pre-date and motivate much of the self-types literature.** Any
claim that a self-type / `mu` feature is "novel" should be checked
against Hickey. The object-encoding use case in particular is
essentially what VDTs were built for.

**They separate self-reference from termination more cleanly than
anything in the fix/iota/mu discussion.** `fix` couples self-reference
with "divergence is fine"; `iota` couples it with "trust the author to
write a well-founded spec"; VDTs couple it with "prove well-foundedness
up front via a ≺." The latter is the strictest contract, and it is
worth asking whether Och's abstract-evaluator termination story is
closer to "trust the author" or "prove ≺" — the answer is currently
closer to the former, with the `mu` annotation as a hedge.

**They suggest that the right framing for Och may be "self-reference
plus a termination anchor," with the anchor as an orthogonal
parameter.** The anchor can be a domain annotation (`fix`), a self
binder annotation (Kind2), a well-founded order (Hickey), or implicit
(Agda's termination checker). The choice is independent of whether the
self-reference lives on terms, types, or (via `mu`) both. Och's current
design uses option 1 for `fix` and is reaching for option 2 for `iota`
via the `mu` proposal. Option 3 (explicit well-foundedness) is the
heaviest but also the only one that gives decidability guarantees.

---

## References

- Hickey, J. (1996). *Formal Objects in Type Theory Using Very
  Dependent Types.* Foundations of Object-Oriented Languages (FOOL 3).
  https://www.cs.caltech.edu/~jyh/papers/fool3/default.html
- Hickey, J. (2001). *The MetaPRL Logical Programming Environment.*
  Cornell PhD thesis. Chapters on VDTs in the Nuprl type theory.
- Allen, S., Bickford, M., Constable, R., Eaton, R., Kreitz, C.,
  Lorigo, L., Moran, E. (2006). *Innovations in computational type
  theory using Nuprl.* J. Applied Logic. Contains the Nuprl VDT rules.
- Fu, P. & Stump, A. (2014). *Self Types for Dependently Typed Lambda
  Encodings.* RTA-TLCA 2014. For comparison with `iota`.
- Dybjer, P. (2000). *A general formulation of simultaneous inductive-
  recursive definitions in type theory.* JSL. The intensional
  descendant of VDTs.
- Internal: `docs/research/self-types-for-och.md`,
  `docs/ideas/merge-fix-iota.md` — Och's existing treatment of
  self-reference.
