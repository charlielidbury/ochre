# Why Och Matters for Ochre

This document explains the precise relationship between Och and Ochre, and what
constraints Ochre places on Och's design. It is written for anyone working on Och
who needs to understand what they're building toward.

## The Short Version

Ochre's type checker is an abstract interpreter. Och isolates that abstract
interpreter in a pure setting. Every rule in Och — evaluation, subtyping,
ascription — appears as a sub-component of Ochre's type system. If these rules
are wrong in Och, they are wrong in Ochre. If they are right in Och but too
weak, Ochre cannot express the properties it needs.

## The Precise Dependencies

### 1. Och's abstract evaluation IS Ochre's type-level computation

In Ochre, dependent types like `Array n T` require evaluating expressions at the
type level. When the type checker encounters `Array n T`, it must compute what
this reduces to — e.g., `Array 2 T = Pair T (Pair T Unit)`. This computation
follows exactly the rules of Och's abstract evaluation: beta-reduction,
substitution, ascription handling.

If Och's abstract evaluation is wrong, Ochre's type-level computation is wrong.
There is no separate mechanism.

### 2. Och's subtyping rules are embedded in Ochre's

Ochre's subtyping includes everything Och has — function subtyping (contravariant
domains, covariant bodies checked pointwise), Type as top, singleton subtyping —
plus additional rules for references and ownership. The Och rules appear as-is in
Ochre. If function subtyping is unsound in the pure fragment, it is unsound in
the full language.

### 3. Monotonicity IS what makes strong mutation sound

This is the deepest connection and the most important to understand.

Ochre's signature feature is **strong mutation**: after `x = 5`, the type of `x`
becomes the singleton `5`, not just `Nat`. This is implemented by **narrowing the
typing environment** — replacing `x: Nat` with `x: 5` and re-evaluating
dependent expressions.

Monotonicity says: narrowing the environment narrows (or preserves) the result.
This is exactly the property that makes strong mutation safe. If you have verified
that some expression `e` has type `τ` when `x: Nat`, and then `x` is mutated to
`5` (narrowing `x`'s type from `Nat` to `5`), monotonicity guarantees that `e`
still has a type that is a subtype of `τ`. Without this, mutation could silently
invalidate previously-checked typing judgments.

**The known counterexample (Proposition 5.2.9) is exactly a failure of this.**
Narrowing `B: Bool` to `B: true` broke a subtyping judgment. This is not a
mutation-specific bug — it happens in the pure fragment. But it is a bug that
*would manifest as unsound mutation* in Ochre. Fixing it in Och directly fixes
the path to strong mutation.

### 4. Transparency enables verification across function boundaries

Ochre's value proposition is that programmers can prove properties of real code.
This requires the type checker to see through function bodies — if `f` is defined
transparently, a caller of `f` gets precise information about what `f` returns.

In Och, this is the default: function bodies are visible unless explicitly
ascribed. This transparency is what allows `succ 2` to have precise type `3`
rather than just `Nat`. In Ochre, the same mechanism allows the type checker to
verify properties like "this function preserves an invariant" by actually
evaluating the function body abstractly.

If Och achieves soundness by making functions opaque, Ochre loses its ability to
verify anything interesting.

### 5. Ascription is where runtime and compile-time diverge

This is perhaps the most unusual and important aspect of Och's design.

In Och, `(e : τ)` has two interpretations depending on the mode of evaluation:
- **Runtime (concrete evaluation):** takes the left-hand side `e`, discards `τ`.
  The ascription is erased; the program runs normally.
- **Compile-time (abstract evaluation):** takes the right-hand side `τ`, discards
  `e`. The type checker sees only the declared type, not the implementation.

This means **compiling an Och program is just running it in imprecise mode.**
There is no separate compilation semantics — the same evaluator, when it
encounters `(e : τ)`, simply chooses the right-hand side instead of the left.
The "compiled" (erased, abstract) program and the "interpreted" (concrete)
program are the same program executed under different ascription semantics.

This is a very unusual concept, and it might be unsound. A key goal of Och is to
determine whether this dual-interpretation of ascription can be made correct —
specifically, whether the soundness theorem (concrete evaluation refines abstract
evaluation) holds when the only point of divergence between the two modes is
which side of `:` they take.

In Ochre, this same mechanism would serve multiple roles:
- **Module boundaries and APIs:** ascribing an implementation to an interface
  type hides internals from callers (compile-time takes the rhs).
- **Compilation itself:** erasing type information for code generation is just
  the concrete evaluator ignoring the rhs.
- **The distinction between proof and program:** proof terms exist at compile
  time (rhs) but are erased at runtime (lhs takes over).

The rules for ascription must be:
- Sound (the lhs must actually be in the set denoted by the rhs)
- Actually lossy in abstract mode (the rhs must genuinely hide information,
  otherwise there's no way to write stable APIs or erase proofs)
- Compatible with monotonicity (ascribing a function shouldn't create
  anti-monotone behavior in callers)
- Consistent between modes (the two interpretations must agree on
  well-formedness — if `(e : τ)` is accepted, both modes must be safe)

### 6. Church encodings stand in for algebraic data types

Och uses Church encodings for all data. This is not just a simplification — Ochre's
algebraic data types would desugar to something with the same typing behavior.
If Och's type system cannot verify that `true ⊑ Bool` or that `isZero` correctly
distinguishes `0` from `succ k`, then Ochre cannot type-check pattern matching
on user-defined data types.

The partitioning mechanism (§4.2.5 of the spec) — where the abstract interpreter
splits on a Church-encoded eliminator — is a prototype of Ochre's match/pattern
matching. Getting this right in Och is a prerequisite for getting it right in Ochre.

## Design Constraints Ochre Places on Och

These are properties Och **must** have for Ochre to work. An Och design that
violates any of these is a dead end, even if it is internally sound.

### Must: Precision by default

The abstract interpreter must compute the most precise type it can, absent
ascription. For closed terms, this means singleton types. For open terms, this
means propagating whatever is known.

**Why:** Ochre's strong mutation and dependent types only work if the type system
tracks precise information. If Och defaults to imprecise types, Ochre cannot
express properties like "this array has exactly n elements."

**Test:** `succ 2` must have precise type `3`, not just `Nat`. The §6 test suite
encodes many such precision requirements.

### Must: Transparent function bodies

Callers of a non-ascribed function must be able to see (and type-check through)
the function body.

**Why:** This is what allows Ochre to verify properties that span function
boundaries. An opaque-by-default system would require the programmer to
separately state and prove every property of every function, which is the
ergonomic disaster Ochre is trying to avoid.

**Test:** `id Nat 3` must have precise type `3`, where `id = λ(T: Type). λ(x: T). x`.

### Must: Non-trivial subtyping

The subtyping relation must be rich enough to express: `3 ⊑ Nat`, `true ⊑ Bool`,
`succ ⊑ λ(_: Nat). Nat`, function subtyping with contravariant domains.

**Why:** Ochre needs semantic subtyping for refinement types, for checking that
implementations match interfaces, and for the basic property that a precise type
can be used where a less precise one is expected.

**Test:** The §6 test suite requires all of these. If any are dropped, Ochre
cannot express the properties it needs.

### Must: Monotonicity of abstract evaluation

If `Γ₂ ⊑ Γ₁` then the abstract result under `Γ₂` must be ⊑ the result under `Γ₁`.

**Why:** See §3 above. This is what makes strong mutation and modular type
checking sound. Without it, Ochre cannot narrow variable types after assignment
without rechecking everything from scratch.

**Test:** This is a universal property, not a single test case. It must be proven,
not just tested. The counterexample from Proposition 5.2.9 is a specific case
where earlier attempts failed.

### Must: Ascription actually loses information

`(e : τ)` must produce type `τ`, not something more precise.

**Why:** Ochre needs stable interfaces. If the type checker can see through
ascription, there is no way to hide implementation details, and every change to a
function body is a breaking API change. More fundamentally, if the abstract
evaluator doesn't actually take the rhs, then there is no compile-time/runtime
distinction and no way to erase proofs.

### Must: The dual-interpretation of ascription must be sound

The central research question: can `(e : τ)` safely mean "take `e` at runtime,
take `τ` at compile time"? Soundness requires that anything the compile-time
mode accepts, the runtime mode doesn't violate. This is not a standard property
— it is specific to Och's design and must be carefully validated.

### Must not: Require annotations for precision

The system should not require the programmer to write type annotations to get
precise types. Annotations should only be needed to *lose* precision.

**Why:** This is a core ergonomic property of Ochre. Code without annotations
should "just work" with maximal precision. Forcing annotations everywhere defeats
the purpose of having a precise type system.

## What "Success" Looks Like

A successful Och design is one where:

1. Soundness and monotonicity are provable (mechanically, in Lean or similar)
2. The §6 test suite passes
3. All the "Must" constraints above are satisfied
4. Looking at the rules, there is a clear path to adding ownership (Ochr) and
   then mutable references (Ochre) without fundamentally changing the core

Point 4 is a judgment call, not a mechanical check. But if the rules for
evaluation, subtyping, and ascription are clean and compositional, extending
them with ownership should be a matter of adding rules, not rewriting existing
ones.

## What "Failure" Looks Like

These are signs that an Och design is going off track:

- **Soundness achieved by restricting expressiveness.** If `3 ⊑ Nat` no longer
  holds, or `succ 2` doesn't have type `3`, the system is too weak for Ochre.
- **Monotonicity achieved by making everything opaque.** If function bodies are
  hidden by default, Ochre loses its verification power.
- **Subtyping only works for syntactic equality.** If the system can only check
  `e ⊑ e` and not `3 ⊑ Nat`, it's not semantic subtyping.
- **Proofs require ad-hoc side conditions.** If soundness needs "this only works
  when the term doesn't contain X," the rule is probably wrong and will cause
  worse problems in Ochre.
- **The rules are not compositional.** If adding a new feature requires modifying
  existing rules rather than adding new ones, the design will not scale to Ochre.
