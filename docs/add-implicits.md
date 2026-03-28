# Och Extension: Implicit Arguments

## Prerequisites

This extension builds on the core Och calculus defined in och-spec.md. It adds
implicit argument syntax and an elaboration pass that resolves implicit arguments
into explicit ones before the core typing rules are applied.

---

## 1. Motivation

Church encodings require many type arguments that are inferrable from context.
For example, constructing a pair:

```
pair Nat Bool 10 true
```

The type arguments `Nat` and `Bool` are determined by the value arguments `10`
and `true`. Requiring them to be written explicitly adds significant syntactic
noise, especially in deeply nested expressions like:

```
consArray Nat 2 30 (consArray Nat 1 40 (consArray Nat 0 50 (emptyArray Nat)))
```

vs:

```
consArray 30 (consArray 40 (consArray 50 emptyArray))
```

---

## 2. Syntax Extension

Add two new syntactic forms:

```
e ::= ...
  | λ[x: τ]. e                -- lambda with implicit parameter
  | e [e]                     -- explicit application of implicit argument
  | λ[x: τ₁]. τ₂              -- lambda with implicit parameter (also serves as implicit function type)
```

Square brackets `[ ]` distinguish implicit from explicit arguments.

---

## 3. Elaboration

Implicit arguments are resolved by an **elaboration pass** that transforms the
surface syntax into the core calculus (which has only explicit arguments). This
pass runs before typing.

### 3.1 Rules

1. **Definition site:** `λ[x: τ]. e` elaborates to `λ(x: τ). e`. The bracket
   annotation is recorded in the function's signature metadata but does not
   change the core term.

2. **Call site (implicit):** When `f` expects an implicit argument and the caller
   writes `f a` (without brackets), the elaborator inserts a metavariable:
   `f ?M a`, where `?M` is solved by unification with the types of subsequent
   arguments.

3. **Call site (explicit override):** `f [τ] a` provides the implicit argument
   explicitly. No inference needed.

4. **Unification:** The elaborator solves metavariables by unifying expected and
   actual types. For example, if `pair : λ[A: Type]. λ[B: Type]. A → B → Pair A B`
   and the call is `pair 10 true`, the elaborator unifies:
   - `A` with the type of `10` → `A = Nat` (or the precise type `10`, depending
     on the desired precision level)
   - `B` with the type of `true` → `B = Bool` (or `true`)

### 3.2 Precision and Implicit Arguments

A subtle question: when inferring `A` from a value argument `10`, should `A` be
inferred as `Nat` (the annotated parameter type) or `10` (the most precise type)?

In the terms-as-types system, the most precise type of `10` is `10` itself. If
the implicit parameter is annotated `[A: Type]`, the elaborator should infer `A`
as the type annotation on the corresponding explicit parameter, not the precise
type of the value. For example:

```
id = λ[T: Type]. λ(x: T). x;
id 3
```

Here `T` should be inferred from the annotation `(x: T)` and the argument `3`.
Since `3 ⊑ Nat ⊑ Type`, the question is whether `T = 3` or `T = Nat`.

Proposed rule: the elaborator infers the **most precise** type that satisfies all
constraints. If the only constraint is `3 ⊑ T`, then `T = 3`. If the function
is later applied in a context requiring `T = Nat`, the caller can write `id [Nat] 3`.

### 3.3 Complete Elaboration Example

Surface syntax:
```
consArray 30 (consArray 40 (consArray 50 emptyArray))
```

After elaboration (assuming definitions use `[T: Type]` and `[n: Nat]`):
```
consArray Nat 2 30 (consArray Nat 1 40 (consArray Nat 0 50 (emptyArray Nat)))
```

The type `Nat` is inferred from the value arguments. The lengths `2, 1, 0` are
inferred from the types of the rest arguments.

---

## 4. Typing

Since elaboration produces core calculus terms, no new typing rules are needed.
The typing rules from och-spec.md apply to the elaborated output.

The correctness obligation is: **elaboration preserves types.** If the surface
program is intended to have type `τ`, the elaborated core program should have
type `τ` under the existing rules.

---

## 5. Properties

### 5.1 Conservative Extension

Every core calculus program is a valid surface program (just don't use `[ ]`).
Elaboration is the identity on programs without implicit arguments.

### 5.2 Coherence

If there are multiple valid solutions for an implicit argument, the elaborator
must be deterministic — it always picks the same solution. The "most precise"
rule (§3.2) provides this determinism.

### 5.3 Preservation of Core Properties

Since elaboration produces core terms, soundness, monotonicity, ascription
soundness, and transparency preservation follow from the core proofs.

---

## 6. Interaction with Other Extensions

### 6.1 With CPS Bind (`?`)

Implicit arguments and `?` interact at elaboration time. When `v?` is used and
`v` expects an implicit type argument (the `X` in `λ[X: Type]. λ(_: T → X). X`),
the elaborator must infer `X` from the expected return type of the enclosing block.

The desugaring of `?` should happen after implicit argument elaboration, or the
two passes need to cooperate on inferring `X`.

### 6.2 With Ascription

Ascription `(e : τ)` can provide type information that helps resolve implicit
arguments. For example:

```
(id 3 : Nat)
```

The ascription tells the elaborator that the result should be `Nat`, which could
influence the inference of `T` in `id [T] 3`.

---

## 7. Open Questions

### 7.1 Inference Algorithm

The unification-based approach described above is standard, but in a dependently
typed setting with terms-as-types, unification must handle arbitrary term equality.
This is undecidable in general. Practical approaches include pattern unification
(Miller's fragment) or best-effort inference with explicit fallback.

### 7.2 Multiple Valid Inferences

When `3 ⊑ Nat ⊑ Type`, inferring `T = 3` vs `T = Nat` changes the downstream
types. The "most precise" rule is one choice; another is "use the declared
parameter bound." This needs a definitive design decision.

### 7.3 Error Messages

When implicit argument inference fails, the error message should clearly indicate
which argument could not be inferred and why, rather than presenting a confusing
unification failure on the elaborated core term.