# Fix Exploration: Monotonicity-Compatible Rules

The monotonicity failure is caused by dependent domains + contravariant
function subtyping. This document explores concrete rule modifications
that might resolve it.

## The Goal

Find rules such that:
1. `true ⊑ Bool`, `false ⊑ Bool`, `3 ⊑ Nat`, `true ⋢ Nat` (basic subtyping)
2. `succ 2 ⇝ 3` (transparency, precision)
3. `(x : T) ⇝ T` (ascription loses information)
4. Monotonicity: narrower Γ → narrower τ (or at least: narrower Γ doesn't WIDEN τ)
5. Soundness: concrete value ⊑ abstract type

---

## Idea A: Widen Domains on Substitution

The problem: substituting a narrow value for `A` in `λ(x:A).body` narrows
the domain, widening the function type. What if we DON'T narrow the domain?

**Modified App rule:** When substituting `a'` for `x` in `body`, and `body`
contains a lambda `λ(y:D).e` where `x ∈ FV(D)`, replace `D[x:=a']` with
`D[x:=A]` (the DOMAIN of x, not the value of x).

That is: domain annotations are substituted with the WIDEST type for the
variable, not the actual value.

Example: `f = λ(A:Type). λ(x:A). x`

`f Nat`: body = `λ(x:A).x`. Instead of substituting `A:=Nat` into the
domain, we substitute `A:=Type` (the domain of A). Result: `λ(x:Type).x`.

Under `A:Type`: `f A ⇝ λ(x:Type).x`. Same as before.
Under `A:Nat`: `f A ⇝ λ(x:Type).x`. Domain stays wide!

Now `λ(x:Type).x ⊑ λ(x:Type).x` by Refl. Monotonicity holds. ✓

### Does this break precision?

`f Nat ⇝ λ(x:Type).x` instead of `λ(x:Nat).x`. This is LESS precise.
The function appears to accept all types, not just Nat.

But is it SOUND? `f Nat` concretely evaluates to `λ(x:Nat).x`. We need
`λ(x:Nat).x ⊑ λ(x:Type).x`. By S-Lam: `Type ⊑ Nat`? NO.

By Lam-PW-Partial or by the semantic argument: the concrete function
(only works on Nat) IS in the set `λ(x:Type).x` (works on everything)?
No — `λ(x:Nat).x` doesn't work on non-Nat inputs, so it's NOT in the
set `λ(x:Type).x`.

Wait, actually: `λ(x:Nat).x` DOES work on everything at runtime — the
domain annotation is erased! At runtime, `(λ(x:Nat).x) "hello" = "hello"`.
The domain annotation is only a COMPILE-TIME restriction.

Hmm, but soundness says: concrete value ⊑ abstract type. If the abstract
type is `λ(x:Type).x` (identity on everything), and the concrete value is
`λ(x:Nat).x` (identity on Nat), is the concrete value in the abstract set?

Semantically: `λ(x:Type).x` = {f | ∀v. f v ⊑ v}. At runtime, `λ(x:Nat).x`
applied to anything returns it (since domain annotations are erased). So
`λ(x:Nat).x` IS in the set — it just happens to have a narrower static
domain annotation.

But in Och's subtyping: `λ(x:Nat).x ⊑ λ(x:Type).x` requires `Type ⊑ Nat`
by S-Lam. This fails. So the subtyping rules DON'T reflect the runtime
semantics here.

**The subtyping rules are too strict.** At runtime, domain annotations are
erased. But the subtyping rules treat domains as meaningful. This creates
a gap: the runtime function works on everything, but subtyping says it only
works on Nat.

### Key Insight: Domain Erasure and Subtyping

At runtime, `λ(x:A).body` and `λ(x:B).body` are identical — domain
annotations are erased. So at runtime, `λ(x:Nat).x = λ(x:Type).x = λ(x:_).x`.

For soundness, we need: concrete value ⊑ abstract type. The concrete value
is the domain-erased function. If the abstract type has a wider domain, the
concrete function (which works on everything) is in the abstract set.

This suggests we need a subtyping rule that reflects domain erasure:

```
[Lam-Erased]
Γ ⊢ λ(x:A₁).B₁ ⊑ λ(x:A₂).B₂
  Γ, x:A₂ ⊢ B₁ ⊑ B₂
  -- NO domain check on A₁ vs A₂!
```

But we showed earlier that dropping the domain check makes `true ⊑ Nat`
hold, which is wrong. Let's recheck.

`true ⊑ Nat` with Lam-Erased:
```
λ(X:Type).λ(t:X).λ(f:X).t  ⊑  λ(X:Type).λ(z:X).λ(s:λ(_:X).X).X
```

Lam-Erased (outer, X:Type): body check:
```
λ(t:X).λ(f:X).t  ⊑  λ(z:X).λ(s:λ(_:X).X).X
```

Lam-Erased (middle, α-rename to `a:X`): body check under `a:X`:
```
λ(f:X).a  ⊑  λ(s:λ(_:X).X).X
```

Lam-Erased (inner, use supertype's domain `s:λ(_:X).X`): body check under
`X:Type, a:X, s:λ(_:X).X`:
```
a ⊑ X
```

`a : X` in context, so `a ⊑ X` by Var. ✓

So `true ⊑ Nat` holds. **But it should fail!**

The problem: `true` selects its second argument (like zero does), but `true`
expects its third argument to have type `X`, while a natural number's third
argument should have type `X → X`. Without the domain check, we can't
distinguish them.

But semantically, at RUNTIME, true and zero are the same function! Both take
three arguments and return the second one. `true X z s = z = 0 X z s` for
any X, z, s.

Wait... are true and 0 really the same? Let me check:

```
true = λ(X:Type).λ(t:X).λ(f:X).t
0    = λ(X:Type).λ(z:X).λ(s:λ(_:X).X).z
```

At runtime (domains erased):
```
true = λ(X).λ(t).λ(f).t
0    = λ(X).λ(z).λ(s).z
```

Yes, they're identical! `true` and `0` are the SAME runtime value!

So `true ⊑ Nat` is actually CORRECT from a runtime perspective: the runtime
value of `true` IS a natural number (it's zero). The distinction between
`true` and `0` is purely in their domain annotations, which are erased.

**This means: if we erase domains for subtyping (Lam-Erased), then
`true ⊑ Nat` is correct, and `true ⋢ Nat` is an INCORRECT requirement!**

Or rather: the spec says `true ⋢ Nat`, and this is a design choice about
whether domain annotations matter for type identity. If domains are erased,
`true = 0` and `Bool ∩ Nat ≠ ∅`. If domains are kept, `true ≠ 0` and
`Bool ∩ Nat = ∅`.

### The Design Choice

**Option 1: Domains matter for identity (current).**
- `true ≠ 0` (different domain annotations)
- `Bool ∩ Nat = ∅` (no value is both a boolean and a natural)
- Subtyping uses S-Lam with contravariant domains
- Monotonicity FAILS

**Option 2: Domains are erased for identity.**
- `true = 0` (same runtime behavior)
- `true ⊑ Nat` and `0 ⊑ Bool` (both select the second argument)
- Subtyping uses Lam-Erased (no domain check)
- Monotonicity HOLDS (for the function type comparison)
- But: `Bool` and `Nat` are no longer disjoint. `true : Bool ∩ Nat`.

### Consequences of Option 2

If `true ⊑ Nat`, what goes wrong?

Consider: `isZero true`. `isZero = λ(n:Nat). n Bool true (λ(_:Bool).false)`.

With `true ⊑ Nat`, the call typechecks. At runtime:
`isZero true = true Bool true (λ(_:Bool).false) = true`. Correct! true selects
the "zero" branch, and `isZero true = true`, same as `isZero 0`.

Consider: `succ true`. `succ = λ(n:Nat). λ(X:Type).λ(z:X).λ(s:λ(_:X).X). s(n X z s)`.

With `true ⊑ Nat`:
`succ true = λ(X:Type).λ(z:X).λ(s:λ(_:X).X). s(true X z s) = λ...s(z) = 1`.

`succ true = 1`. Is this correct? Operationally yes: since `true` and `0`
are the same runtime value, `succ true = succ 0 = 1`.

Actually, everything works out consistently because `true` and `0` ARE the
same function. The Church encoding doesn't distinguish them at runtime.

So Option 2 is semantically consistent. But it changes the language's type
system: `Bool` and `Nat` overlap, and you can pass booleans where naturals
are expected (and vice versa, where the encoding happens to match).

For Ochre (the full language with algebraic data types), this would be
problematic: you'd want `True` and `Zero` to be genuinely different
constructors. But in Church-encoded Och, the distinction is artificial.

### Option 2 with Explicit Tags

To recover disjointness of `Bool` and `Nat`, you could Church-encode with
explicit tag parameters:

```
Bool = λ(X:Type). λ(tag: BoolTag). λ(t:X). λ(f:X). X
Nat  = λ(X:Type). λ(tag: NatTag). λ(z:X). λ(s:X→X). X
```

Where `BoolTag` and `NatTag` are distinct types. This adds an extra parameter
that distinguishes booleans from naturals even after domain erasure.

But this is an encoding change, not a rule change. The current Church
encoding is the standard one and doesn't include tags.

---

## Idea B: Make Domains Part of the Context, Not the Lambda

Instead of `λ(x:A).body`, use `λ(x).body` with domain annotations stored
separately in the environment:

```
Γ, x:A ⊢ body : τ
─────────────────────
Γ ⊢ (λx.body, domain=A) : (x:A) → τ
```

The domain `A` is metadata on the binding, not part of the lambda syntax.
Subtyping compares lambda BODIES only:

```
Γ ⊢ λx.B₁ ⊑ λx.B₂   iff   for all v, B₁[x:=v] ⊑ B₂[x:=v]
```

But the domain is used to determine WHICH values are valid inputs.

This is essentially untyped lambda calculus with external type annotations.
It avoids the domain comparison issue but loses the syntactic distinction
between functions with different domains.

---

## Idea C: Monotonicity via Semantic (Denotational) Subtyping

Instead of the syntactic S-Lam rule, define subtyping denotationally:

```
τ₁ ⊑ τ₂  iff  ⟦τ₁⟧ ⊆ ⟦τ₂⟧
```

where `⟦τ⟧` is the set of runtime values that "behave as" τ. Since domains
are erased at runtime, `⟦λ(x:A).body⟧` depends only on `body`, not `A`.

Under this definition:
- `⟦λ(x:Nat).x⟧` = {the identity function} (one runtime behavior)
- `⟦λ(x:Type).x⟧` = {the identity function} (same!)

So `λ(x:Nat).x ⊑ λ(x:Type).x` AND `λ(x:Type).x ⊑ λ(x:Nat).x`. They're
equivalent!

This makes monotonicity trivially hold for function types: if the set
doesn't depend on the domain annotation, narrowing the domain changes
nothing.

But this loses the ability to distinguish `Bool` from `Nat` (same issue as
Option 2 above).

---

## Idea D: Two-Level Subtyping

Have TWO subtyping relations:

1. **Static subtyping** (`⊑ₛ`): includes domain checks (current S-Lam).
   Used for ascription checks and user-facing type errors.

2. **Semantic subtyping** (`⊑ᵣ`): no domain checks (Lam-Erased).
   Used for the soundness proof and monotonicity.

Monotonicity holds for `⊑ᵣ`. Soundness uses `⊑ᵣ`. The user sees `⊑ₛ`.

Since `⊑ₛ ⊆ ⊑ᵣ` (stricter static check implies the semantic one), any
program accepted by static checking is also semantically sound.

The split is:
- **Wellformedness/typechecking** uses `⊑ₛ` (with domain checks)
- **Soundness theorem** uses `⊑ᵣ` (without domain checks)
- **Monotonicity theorem** uses `⊑ᵣ` (without domain checks)

Theorem: If Γ ⊢ e ⇝ τ (using ⊑ₛ in all checks), and γ ⊨ₛ Γ, and eγ ⇓ v,
then v ⊑ᵣ τγ.

Note: the CONCLUSION uses ⊑ᵣ (semantic), not ⊑ₛ (static). This is weaker
than saying `v ⊑ₛ τγ`, but it's what soundness needs: the runtime value is
semantically compatible with the declared type.

### Does this work?

Monotonicity with ⊑ᵣ:
Under A:Type: `f A ⇝ λ(x:Type).x`.
Under A:Nat: `f A ⇝ λ(x:Nat).x`.

`λ(x:Nat).x ⊑ᵣ λ(x:Type).x`? By Lam-Erased: body check under `x:Type`:
`x ⊑ᵣ x`. ✓

So monotonicity holds for ⊑ᵣ. ✓

Soundness: concrete `v = λ(x:Nat).x` (domains erased at runtime, so really
just `λx.x`), abstract type `τ = λ(x:Type).x`.

`λx.x ⊑ᵣ λ(x:Type).x`? Need to check body: for all v ⊑ᵣ Type, x ⊑ᵣ x. ✓

But wait — concrete values DON'T have domain annotations (they're erased).
So `v` is `λx.x`, and `τ` is `λ(x:Type).x`. Comparing them with ⊑ᵣ
(which ignores domains) gives `λx.x ⊑ᵣ λ(x:Type).x`. ✓

Static checks still use ⊑ₛ: `true ⋢ₛ Nat`. ✓ (domain check fails).

### This seems promising!

The two-level approach separates concerns:
- **User-facing type system** (⊑ₛ): strict, distinguishes Bool from Nat
- **Soundness/metatheory** (⊑ᵣ): permissive, based on runtime behavior

The static system is an OVERAPPROXIMATION of what's needed for soundness.
Programs that pass static checking are sound, and we can prove it using
the more relaxed semantic subtyping.

### What about the Prop 5.2.9 example?

```
g = λ(B:Bool). (Not B : B)
```

Static check (⊑ₛ):
Under B:Bool: `Not Bool ⊑ₛ Bool`. `Bool ⊑ₛ Bool`. ✓
Under B:true: `Not true ⊑ₛ true`. `false ⊑ₛ true`. ✗

Static check fails for narrowed context. This is the original bug.

But with two-level: does `g` type-check at all? Under B:Bool, it does.
The monotonicity question is: under B:true, does the body STILL type-check?

With static checking: NO. The ascription check `Not B ⊑ₛ B` fails for
B:true. So the Lam well-formedness check ALSO needs to be reconsidered.

The Lam rule's well-formedness check uses ⊑ₛ. If we check with B:Bool and
it passes, we'd like to conclude that it passes for all B ⊑ Bool. But it
doesn't — the check can fail for narrower B.

The two-level approach doesn't directly fix this unless the well-formedness
check uses ⊑ᵣ instead of ⊑ₛ. If the Lam check uses ⊑ᵣ:

Under B:Bool: `Not Bool ⊑ᵣ Bool`. Does this hold? `Not Bool =β Bool`.
`Bool ⊑ᵣ Bool`. ✓

Under B:true: `Not true ⊑ᵣ true`. `false ⊑ᵣ true`.
`λ(X:Type).λ(t:X).λ(f:X).f ⊑ᵣ λ(X:Type).λ(t:X).λ(f:X).t`

By Lam-Erased (three levels), body check under X:Type, t:X, f:X:
`f ⊑ᵣ t`? f:X, t:X. Need `f ⊑ᵣ t`.

Hmm, `f ⊑ᵣ t` — both are variables of type X. By Var, `f ⊑ᵣ X` and
`t ⊑ᵣ X`. But `f ⊑ᵣ t`? There's no rule for this. `f` and `t` are
different variables. ✗

So `false ⊑ᵣ true` still fails. The issue isn't about domain comparison —
it's about `f` vs `t` in the body.

Actually, this is correct! `false` and `true` are genuinely different
runtime values — they select different arguments. `false X z s = s` while
`true X z s = z`. No domain-erasure trick makes them equal.

So the Prop 5.2.9 issue is NOT resolved by two-level subtyping. It's a
different kind of anti-monotonicity: the BODY (not the domain) produces
anti-monotone results.

### Wait — reconsidering the Prop 5.2.9 example

The issue is:
```
g = λ(B:Bool). (Not B : B)
```

`Not B` abstractly evaluates to:
- Under B:Bool: `Not Bool =β Bool`
- Under B:true: `Not true =β false`

And `B` is:
- Under B:Bool: `Bool`
- Under B:true: `true`

The check `Not B ⊑ B`:
- Bool ⊑ Bool ✓
- false ⊑ true ✗

The anti-monotonicity is in `Not`: narrowing B from Bool to true changes
`Not B` from `Bool` to `false`. Meanwhile B itself goes from `Bool` to `true`.
These move in opposite directions.

This is NOT a domain-annotation issue. It's a body-computation issue. `Not`
is genuinely anti-monotone: narrower input → wider output (true→false is
a "jump", not a narrowing).

The two-level approach helps with the domain counterexample but NOT with the
body counterexample. These are two separate sources of anti-monotonicity.

---

## Summary of Fix Exploration

| Fix | Domain CE fixed? | Body CE (5.2.9) fixed? | Breaks `true ⋢ Nat`? |
|-----|-----------------|----------------------|---------------------|
| A (widen domains) | ✓ but unsound | N/A | N/A |
| B (untyped lambdas) | ✓ | ✗ | Yes |
| C (denotational sub) | ✓ | ✗ | Yes |
| D (two-level) | ✓ | ✗ | No (static ⊑ₛ) |

**None of the fixes resolve the Prop 5.2.9 counterexample**, because that
involves body-level anti-monotonicity, not domain-level anti-monotonicity.

The domain counterexample (`λ(A:Type).λ(x:A).x` under A:Nat) is fixable
by domain erasure / two-level subtyping. But the body counterexample
(`Not B : B` under B:true) requires addressing how ascription interacts
with anti-monotone functions.

---

## The Two Sources of Anti-Monotonicity

1. **Domain anti-monotonicity**: Narrowing a context variable that appears
   in a lambda domain narrows the domain, widening the function set.
   FIXABLE by ignoring domains in the metatheory (two-level subtyping).

2. **Body anti-monotonicity**: Some functions (like `Not`) produce outputs
   that go in the opposite direction from their inputs. When such a function's
   output is used in a subtyping check against a context variable, narrowing
   the context can break the check. NOT FIXABLE by any subtyping rule change
   — it's a property of the FUNCTION being applied.

For body anti-monotonicity, the issue is that `Not` is anti-monotone: it maps
`true → false` and `false → true`. When used in ascription `(Not B : B)`,
the check requires `Not B ⊑ B`. For B:Bool, this holds vacuously (both are
Bool). For B:true, it fails (false ⋢ true).

### Can body anti-monotonicity be restricted?

The Prop 5.2.9 example requires:
1. An anti-monotone function (Not)
2. An ascription where the LHS uses the anti-monotone function and the RHS
   is the same variable

If we restrict ascription to only use monotone expressions on the LHS, the
problem disappears. But this is extremely restrictive — it essentially
forbids ascribing with dependent types.

Alternatively: the ascription check `σ ⊑ τ` could be done ONCE (at the
widest context) and not re-checked under narrowing. This is the current
Lam rule behavior: the well-formedness check passes under the declared
domain. The issue is that monotonicity expects the check to ALSO pass under
narrower domains.

**If we accept that well-formedness is checked once (at the declared domain)
and NOT guaranteed to hold under narrowing, then monotonicity as traditionally
stated fails. But a WEAKER property might hold:**

"If the well-formedness check passes at the declared domain, then CONCRETE
evaluation under any narrower domain is still safe (soundness holds)."

This is soundness WITHOUT monotonicity. The idea: we don't need the
ABSTRACT result to be monotone. We just need the CONCRETE result to be
⊑ the abstract type checked at the widest domain.

This is essentially: "type-check once, run safely everywhere."

The formal version would be:
If `Γ ⊢ e ⇝ τ` (checked at Γ), and `γ ⊨ Γ` (γ is a concrete env
consistent with Γ), and `eγ ⇓ v`, then `v ⊑ τγ`.

Note: this does NOT require `Γ' ⊢ e ⇝ τ'` with `τ' ⊑ τ` for narrower Γ'.
It only requires soundness of the ORIGINAL check at Γ for ALL consistent
concrete environments γ.

**This IS the standard soundness theorem.** It doesn't need monotonicity!
Monotonicity is a separate property (useful for modular type checking and
strong mutation, but not required for basic soundness).

### Revisiting soundness without monotonicity

Can we prove `v ⊑ τγ` without showing that abstract evaluation is monotone?

Going back to the App case:
- `Γ ⊢ f a ⇝ body[x:=a']`, with `f ⇝ λ(x:A).body`, `a ⇝ a'`, `a' ⊑ A`.
- Concrete: `fγ ⇓ λ(x:D).body_c`, `aγ ⇓ v_a`, `body_c[x:=v_a] ⇓ v`.

IH on f: `λ(x:D).body_c ⊑ (λ(x:A).body)γ = λ(x:Aγ).bodyγ`.
S-Lam: for y ⊑ Aγ: `body_c[x:=y] ⊑ bodyγ[x:=y]`.

IH on a: `v_a ⊑ a'γ ⊑ Aγ`.

Instantiate: `body_c[x:=v_a] ⊑ bodyγ[x:=v_a]`.

Need: `v ⊑ (body[x:=a'])γ = bodyγ[x:=a'γ]`.

We have `body_c[x:=v_a] ⇓ v`. Recursively apply soundness to this sub-
evaluation. But what is the "typing judgment" for `body_c[x:=v_a]`?

**This is the key: we need a typing judgment for the concrete body applied
to the concrete argument.** We don't have one from the original derivation
(which types `body[x:=a']` in context Γ, not `body_c[x:=v_a]` in the
empty context).

To construct one: `body_c[x:=v_a]` is a closed term. Its abstract evaluation
is `absEval(body_c[x:=v_a])`. By the IH (soundness for the sub-evaluation):
`v ⊑ absEval(body_c[x:=v_a])`.

Now: `body_c[x:=v_a] ⊑ bodyγ[x:=v_a]` (from the pointwise condition).
If absEval preserves subtyping (term monotonicity):
`absEval(body_c[x:=v_a]) ⊑ absEval(bodyγ[x:=v_a])`.

And `absEval(bodyγ[x:=v_a])`: this evaluates the abstract body with the
concrete argument. Compare to `absEval(bodyγ[x:=a'γ])`: abstract body
with the abstract argument. The gap is again v_a vs a'γ.

**We're going in circles.** Every formulation eventually needs to bridge
from `v_a` to `a'γ` inside some body, which requires monotonicity.

### The Real Question

Is there a proof of soundness that doesn't require bridging from concrete
to abstract argument values?

What if we strengthen the IH to carry the bridge? Something like:

**Theorem (Soundness, strong form).** If `Γ ⊢ e ⇝ τ` and `γ ⊨ Γ` and
`eγ ⇓ v`, then there exist closed terms `τ_c, τ_a` such that:
- `v ⊑ τ_c`
- `τ_c ⊑ τ_a`
- `τ_a ⊑ τγ`

with each ⊑ established by a different argument (IH, pointwise, direct).

The App case would then have:
1. `v ⊑ absEval(body_c[x:=v_a])` — IH on sub-evaluation
2. `absEval(body_c[x:=v_a]) ⊑ absEval(bodyγ[x:=v_a])` — term mono from pointwise
3. `absEval(bodyγ[x:=v_a]) ⊑ bodyγ[x:=a'γ]` — env monotonicity (FAILS)

Step 3 is the problem. Without it, we can get `v ⊑ absEval(bodyγ[x:=v_a])`
but not `v ⊑ bodyγ[x:=a'γ]`.

**Unless** `bodyγ[x:=v_a]` and `bodyγ[x:=a'γ]` evaluate to the same thing.
This happens when body doesn't actually depend on x (the variable doesn't
appear in the body). Or when the dependency is through an ascription that
discards the precise value.

In the test cases: most function bodies either don't mention their argument
in a position that creates anti-monotonicity, or the argument appears only
inside ascriptions (which fix the output type). So the practical impact is
limited.

**Conclusion: soundness without monotonicity seems to require either:**
1. A restriction on which programs are accepted (no anti-monotone bodies)
2. A modified abstract evaluation that avoids the monotonicity gap
3. A fundamentally different proof technique

Option 2 is the most promising: if the App rule's result is formulated so
that the proof doesn't need to bridge from v_a to a'γ, the gap disappears.
But every formulation I've tried still creates this gap.
