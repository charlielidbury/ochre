# Och formalization

Companion to the Agda track in `agda/Och/`. Builds up the declarative
metatheory in natural-deduction style. Notation follows
`../docs/notation.md` — indented derivation trees, conclusion first.

This document uses **named variables** for readability. The Agda
implementation uses de Bruijn indices; the correspondence is
standard (α-equivalence at the named level).

---

## Phase 1 — Syntax and well-formedness

### Syntax

Terms and types share one syntactic category.

```
e, τ ::=
  | x            // variable
  | top          // top of subtype lattice (also the Type universe)
  | bot          // bottom of subtype lattice (empty type)
  | λx:A. b      // lambda; A annotates the domain
  | f a          // application
  | (e : T)      // ascription
  | ι x:A. b     // iota / self-type binder (Cedille-style)
                 //   x in b refers to the value being typed
  | fix x:A. b   // recursive binder
                 //   x in b refers to the recursion
```

Metavariables: `x, y, z` range over variables; `e, b, f, a` over
arbitrary terms; `A, B, T, τ, σ` over terms used as types (all
the same syntactic category).

### Contexts

A context `Γ` is a list of typed bindings:

```
Γ ::=
  | ∅            // empty
  | Γ, x:T       // extend with binding x of type T
```

We assume bindings have distinct names (Barendregt convention).
Context lookup: `x : T ∈ Γ` reads "x is bound to T somewhere in Γ".

### Well-formedness

Judgment `Γ ⊢ e` reads "e is well-formed in context Γ". Just
well-scopedness with structural well-formedness of every sub-term
— no subtyping, no type-checking yet. Subsumption / typing
relation comes in Phase 2.

```
[WF-Var]
Γ ⊢ x
  x : T ∈ Γ        // for some T

[WF-Top]
Γ ⊢ top

[WF-Bot]
Γ ⊢ bot

[WF-Lam]
Γ ⊢ λx:A. b
  Γ ⊢ A
  Γ, x:A ⊢ b

[WF-App]
Γ ⊢ f a
  Γ ⊢ f
  Γ ⊢ a

[WF-Asc]
Γ ⊢ (e : T)
  Γ ⊢ e
  Γ ⊢ T

[WF-Iota]
Γ ⊢ ι x:A. b
  Γ ⊢ A
  Γ, x:A ⊢ b

[WF-Fix]
Γ ⊢ fix x:A. b
  Γ ⊢ A
  Γ, x:A ⊢ b
```

Note: `WF-Lam`, `WF-Iota`, `WF-Fix` have identical shape — each
binds one variable whose type is the annotation. The structural
similarity may factor into a single rule once we identify what
distinguishes them at the typing level.

---

## Phase 2 — Values

The subtype relation operates on **values**, not raw `Syntax`.
This separates two concerns that the previous draft conflated:

* **Reduction** (β, fix unfolding, iota projection) — happens
  during evaluation, before subtyping.
* **Subtyping** — purely structural comparison, no reduction
  inside the relation.

This matches how mainstream dependent type theory implementations
structure their kernels (Coq, Lean, Agda — see
`docs/ideas/kernel-conversion-survey.md` for citations).

### Grammar

Values are `Syntax` whose head is in **weak head normal form**
(WHNF): a canonical constructor, or a stuck "neutral".

```
v, w ::=                                     // values (WHNF)
  | top
  | bot
  | λx:A. b                                  // canonical lambda
  | ι x:A. b                                 // canonical iota
  | fix x:A. b                               // canonical fix
  | n                                        // neutral

n ::=                                        // neutrals (stuck)
  | x                                        // free variable
  | n a                                      // application of neutral
```

Sub-terms inside binders (`A`, `b`) and stuck-app args (`a`) are
arbitrary `Syntax`, not values — eval reduces only to WHNF, not
under binders.

### What `Value` means here

Pinning this down explicitly because it matters:

`Value` is **purely a structural property** — "the head is in
WHNF". A `Value` is a syntactic shape, not a typing claim.

Specifically, `Value` does **not** mean:

* Well-typed in some context.
* The result of eval'ing a well-formed term.
* Closed (free of free variables — neutrals headed by free vars
  are values).
* Bvars in scope.

`Value` *only* means: the head can't β-reduce, fix-unfold, or
iota-eliminate any further. It's the input format the subtype
relation expects.

Well-typedness in Och is **a property of the subtype relation**,
not of values. A value `v` is "well-typed at τ" iff `Γ ⊢ v ⊑ τ`
is derivable. There's no separate well-typedness predicate to
satisfy *before* you can talk about subtyping. By [S-Refl], every
value is at least well-typed at itself.

This is the same convention every kernel uses: the value
representation admits ill-typed garbage; the typing system is
what carves out the well-typed sub-language.

### Why values matter

The point of values: subtype rules become **structural** —
no β, no unfold, no projection rules inside the relation. Each
constructor of the relation matches a value-grammar shape and
recurses into sub-components.

The previous draft had `S-AppBetaL/R`, `S-FixUnfoldL/R`,
`S-IotaElim-AnnL/BodyL` — all *reduction* rules. With reduction
moved into eval (Phase 3), those disappear from the subtype
relation entirely. What's left is small.

---

## Phase 2 (continued) — Subtyping on values

Judgment `Γ ⊢ v ⊑ w` reads "in context Γ, value v is a subtype
of value w". Single turnstile throughout.

The relation is defined on `Value × Value` only. Top-level typing
on `Syntax` (which would compose eval and this relation) is not
yet formalized — that's a later phase.

### Structural rules

```
[S-Refl]
Γ ⊢ v ⊑ v

[S-Trans]                                    // conjectured admissible
Γ ⊢ v ⊑ w
  Γ ⊢ v ⊑ u
  Γ ⊢ u ⊑ w

[S-Top]
Γ ⊢ v ⊑ top

[S-BotL]
Γ ⊢ bot ⊑ v
```

Note on `S-Trans`: in this design — subtype on values, no internal
reduction — `S-Trans` is **conjectured admissible** by structural
induction (no rule increases value size on the cut). The previous
draft had it as a primitive constructor because reduction rules
inside subtype broke the size measure; that's no longer the case.
We keep it as a rule for now and check admissibility later.

### Variables (neutral heads)

```
[S-Var]
Γ ⊢ x ⊑ T
  x : T ∈ Γ                                  // for the declared T

[S-Neutral]                                  // structural on neutral spines
Γ ⊢ n a ⊑ n' a'
  Γ ⊢ n ⊑ n'
  Γ ⊢ a ⊑ a'                                 // (a, a' are Syntax — see note)
```

Note: `S-Neutral`'s `a ⊑ a'` premise is on raw `Syntax`. Either
we extend the relation to Syntax (composing eval + value-subtype),
or we eval `a` and `a'` to values first. Resolved when we add eval.

### Lambda

Pierce-style. Contra on domain, co on body, with the body
recursing under the *narrower* declared domain.

```
[S-Lam]
Γ ⊢ λx:A. b ⊑ λx:A'. b'
  Γ ⊢ A' ⊑ A                                 // contra on domain
  Γ, x:A' ⊢ b ⊑ b'                           // co on body
```

Same caveat as `S-Neutral`: `b`, `b'` are `Syntax`, not values.
The body comparison composes with eval once we add it.

### Iota (self-types)

The intro rule constructs an ι-witness. There are no elim rules
in this version — what would have been `S-IotaElim-AnnL` /
`-BodyL` is now eval's job: an `ι` value can be "projected" by
eval (yielding either the annotation or the self-substituted
body, depending on what the consumer asks for), and the result
is a value the subtype relation handles via other rules.

```
[S-IotaIntro]
Γ ⊢ v ⊑ ι x:T. b
  Γ ⊢ v ⊑ T                                  // satisfies annotation
  Γ ⊢ v ⊑ b[v/x]                             // satisfies self-typed body
```

The substituted body `b[v/x]` is `Syntax`; its WHNF is what the
recursive subtype check sees — to be made precise once eval is
defined.

### Fix (recursive types)

Equirecursive subtyping. Two fix values are subtypes when their
unfoldings are subtypes — coinductively.

```
[S-FixCoind]
Γ ⊢ fix x:A. b ⊑ fix x:A'. b'
  Γ, x:A' ⊢ b ⊑ b'                           // assume goal coinductively, recurse on bodies
```

This is the Brandt–Henglein equirecursive subtype rule. The
algorithmic version uses a seen-set to detect cycles; the
declarative version is coinductive.

What about asymmetric fix (one side fix, other side not)? In a
`Value × Value` setting, that situation arises when eval has
already unfolded one side and not the other. We'd handle it via
eval, not via a subtype rule — eval can be made to produce
maximally-unfolded values when comparing against a fix.

### Ascription — gone

Ascription doesn't appear in the value grammar. That's because
eval erases it: `(e : T)` reduces to whatever `e` reduces to,
threading the ascription as a typing constraint at eval time
(the analogue of `S-AscR`'s "and `e ⊑ T`" premise becomes a
side condition on eval's input).

This matches Coq / Lean kernel behavior where ascription is a
purely syntactic / pre-elaboration concern, invisible to the
internal value representation.

---

## Phase 3 — TODO

Evaluation `Γ ⊢ e ⇓ v` — relation reducing `Syntax` to `Value`.
Substitution machinery. Once defined, the subtype rules' Syntax
premises (`a ⊑ a'`, `b ⊑ b'`) get cleaned up: either by composing
with eval inline, or by lifting subtype to a `Syntax × Syntax`
relation defined as "eval both sides, then `Value × Value`
subtype".

Then: top-level typing on `Syntax`, soundness.
