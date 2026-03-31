# Monotonicity Analysis

## The Core Tension

Och wants three properties simultaneously:

1. **Dependent types**: Lambda domains can reference context variables.
   E.g., `λ(A:Type). λ(x:A). x` — the inner domain `A` depends on the
   outer binding.

2. **Contravariant function subtyping**: `f ⊑ g` requires `dom(g) ⊑ dom(f)`
   (wider domain = smaller function set, because the function must work on
   more inputs).

3. **Monotone abstract evaluation**: Narrowing the context narrows (or
   preserves) the abstract result. `Γ₂ ⊑ Γ₁ ⟹ τ₂ ⊑ τ₁`.

**These three cannot all hold.** Here is the precise argument.

---

## The Counterexample

```
f = λ(A:Type). λ(x:A). x
```

Under context `A : Type`:
```
f A  ⇝  (λ(x:A).x)[A := Type]  =  λ(x:Type).x
```

Under context `A : Nat` (narrower, since `Nat ⊑ Type`):
```
f A  ⇝  (λ(x:A).x)[A := Nat]  =  λ(x:Nat).x
```

For monotonicity, we need: `λ(x:Nat).x ⊑ λ(x:Type).x`.

By S-Lam, this requires `Type ⊑ Nat` (contravariant domain check). **False.**

In fact, the REVERSE holds: `λ(x:Type).x ⊑ λ(x:Nat).x` (by `Nat ⊑ Type`
via Top). So narrowing the context from `A:Type` to `A:Nat` **widens** the
result from `λ(x:Type).x` to `λ(x:Nat).x`. Anti-monotone.

### Why the reverse direction is correct semantically

- `λ(x:Type).x` as a set = {functions f such that for ALL inputs v,
  f v ⊑ v}. Only the identity function satisfies this. **Small set.**

- `λ(x:Nat).x` as a set = {functions f such that for all v ⊑ Nat,
  f v ⊑ v}. Any function that acts as identity on Nats qualifies,
  regardless of behavior on non-Nat inputs. **Larger set.**

Wider domain → stricter constraint → fewer functions → smaller set.
Narrower domain → weaker constraint → more functions → larger set.

So `λ(x:Type).x ⊑ λ(x:Nat).x` is semantically correct: the smaller
set is a subset of the larger set.

---

## Where This Bites Soundness

The soundness proof's App case needs this chain:

```
v ⊑ absEval(body_c[x:=v_a])              -- IH on sub-evaluation
  ⊑ absEval(body[x:=v_a])                -- "term monotonicity" (body_c ⊑ body)
  ⊑ absEval(body[x:=a'])                 -- env monotonicity (v_a ⊑ a')
  = τ                                     -- by def of abstract eval of App
```

The last step (env monotonicity in the body's substitution) fails when body
contains a lambda with `x` in its domain.

**Key observation:** This failure ONLY occurs when `body` contains a lambda
with the substitution variable in its domain. If `x ∉ FV(domain)` for every
lambda in `body`, then the substitution is purely covariant and the step
holds.

---

## Restricted Monotonicity Conjecture

**Conjecture (Body Monotonicity).** If `Γ, x:A ⊢ e ⇝ τ` and
`Γ ⊢ v₁ ⊑ v₂ ⊑ A`, and `x` does not appear in the domain of any lambda
abstraction in `τ`, then `τ[x:=v₁] ⊑ τ[x:=v₂]`.

This would cover:
- `succ 2 ⇝ 3` — no lambdas with x in domain ✓
- `add n m` where n:Nat, m:Nat — result is a Church numeral (nested s-z
  applications), no dependent domain ✓
- `isZero n` — result is true or false, no dependent domain ✓
- `Array n T` — result is nested Pair types. Does `n` appear in a domain?
  `Pair T (Pair T ...)` = `λ(X:Type).λ(k:λ(_:T).λ(_:...).X).X`. The domains
  of the `k` parameter reference T but not n. ✓

Potential failure:
- `λ(x:n).body` where n is a type variable — but this is unusual in practice

### Does restricted monotonicity suffice for soundness?

If the final result of abstract evaluation is always "domain-free in the
substitution variable" (i.e., no lambda in the result has the substitution
variable in its domain), then the chain in the App case works.

When does the result have the substitution variable in a domain?

The result `τ = body[x:=a']`. If `body` is e.g. `λ(y:x).e'`, then
`τ = λ(y:a').e'[x:=a']`. The domain of `τ` is `a'`, which doesn't contain
`x` (a' is already substituted). So `x ∉ FV(τ)` in all cases!

Wait — the restricted monotonicity is about whether the RESULT τ has the
substitution variable in a domain. But τ is `body[x:=a']`, and after
substitution, `x` doesn't appear at all! So the restriction is vacuously
satisfied?

No, that's confused. The monotonicity step is going from `body[x:=v₁]` to
`body[x:=v₂]`. The question is whether `body` has `x` in a lambda domain.
After substitution with `v₁`, `x` is gone. But the issue is that the
substitution ITSELF produces different terms depending on whether `x` appears
in a domain.

Let me be precise. Consider `body = λ(y:x).y`:

`body[x:=Nat] = λ(y:Nat).y`
`body[x:=Bool] = λ(y:Bool).y`

`λ(y:Nat).y ⊑ λ(y:Bool).y`? Contra needs `Bool ⊑ Nat`. May fail.
`λ(y:Bool).y ⊑ λ(y:Nat).y`? Contra needs `Nat ⊑ Bool`. May fail.

Neither direction works in general. So `body = λ(y:x).y` is anti-monotone.

But this body would come from abstract evaluation of a term like
`f = λ(A:Type). λ(y:A). y`. When we evaluate `f B` for `B:Bool`, we get
`(λ(y:A).y)[A:=Bool] = λ(y:Bool).y`.

The question for soundness is: does the soundness chain need to go through
this anti-monotone step? Let's trace:

Suppose `g = λ(B:Type). (f B) 3`:
- `g ⇝ λ(B:Type).(f B) 3`
- Under B:Nat: `g Nat ⇝ (f Nat) 3 = (λ(y:Nat).y) 3 ⇝ 3` ... wait, 3 ⊑ Nat,
  so App works, result is 3.
- Under B:Type: `g Type ⇝ (f Type) 3 = (λ(y:Type).y) 3 ⇝ 3`.

In both cases the result is 3. The anti-monotone intermediate step
(different domains) doesn't affect the final result because the function
is immediately applied.

### The Application Cancellation Principle

When a function with a dependent domain is APPLIED, the anti-monotonicity
of the function type is cancelled by the covariance of application:

```
λ(x:Nat).x  applied to  3  ⇝  3
λ(x:Type).x  applied to  3  ⇝  3
```

Both give the same result. The domain doesn't affect the result of
application (it only affects the domain check, which passes in both cases
since 3 ⊑ Nat ⊑ Type).

More generally: if `F₁ ⊑ F₂` (as functions) and `v ⊑ dom(F₂)`, then
`F₁ v ⊑ F₂ v`. This is the S-App rule. The anti-monotonicity of the
function type cancels out upon application.

**The anti-monotonicity only matters when functions are RETURNED as values
(not immediately applied).** If every intermediate function result is
eventually applied, the final (ground) result IS monotone.

---

## Exploring Fix #2: Pointwise Function Subtyping

Replace S-Lam with a rule that doesn't compare domains:

```
[Lam-PW]
Γ ⊢ f ⊑ λ(x:A).B
  For all v: if Γ ⊢ v ⊑ A then Γ ⊢ f v ⊑ B[x:=v]
```

This checks: f produces a result ⊑ B for every valid input to the supertype.

### Would this rescue monotonicity?

Under A:Nat: `f A ⇝ λ(x:Nat).x`. Under A:Type: `f A ⇝ λ(x:Type).x`.

Need: `λ(x:Nat).x ⊑ λ(x:Type).x` under Lam-PW.

For all v ⊑ Type: `(λ(x:Nat).x) v ⊑ (λ(x:Type).x) v = v`.

`(λ(x:Nat).x) v ⊑ v`? This applies the function to v. If v ⊑ Nat, the
application succeeds and gives v (so v ⊑ v by Refl). If v ⋢ Nat, the
application FAILS (domain check).

So Lam-PW would require `λ(x:Nat).x` to work on ALL v ⊑ Type, not just
v ⊑ Nat. Since `λ(x:Nat).x` doesn't accept non-Nat inputs, the check
fails for v ⋢ Nat.

**Result: Lam-PW does NOT rescue monotonicity for this example.** It's
actually STRICTER than S-Lam: it requires the subtype function to handle
all inputs of the supertype, not just matching domains.

### Would Lam-PW still validate the existing derivations?

Check `true ⊑ Bool`:

`true ⊑ λ(X:Type).λ(t:X).λ(f:X).X` under Lam-PW:
For all V ⊑ Type: `true V ⊑ (λ(X:Type).λ(t:X).λ(f:X).X) V = λ(t:V).λ(f:V).V`.

`true V = λ(t:V).λ(f:V).t`. Need `λ(t:V).λ(f:V).t ⊑ λ(t:V).λ(f:V).V`.
By Lam-PW: for all v ⊑ V: `(λ(t:V).λ(f:V).t) v ⊑ (λ(t:V).λ(f:V).V) v`.
Both: `λ(f:V).v ⊑ λ(f:V).V`.
By Lam-PW: for all w ⊑ V: `(λ(f:V).v) w ⊑ (λ(f:V).V) w = V`.
`(λ(f:V).v) w = v ⊑ V`. Need `v ⊑ V`. Since `v ⊑ V` (assumed). ✓

So `true ⊑ Bool` works with Lam-PW. ✓

Check `true ⋢ Nat`:

`true ⊑ Nat` under Lam-PW:
For all V ⊑ Type: `true V ⊑ Nat V`.

`true V = λ(t:V).λ(f:V).t`.
`Nat V = λ(z:V).λ(s:λ(_:V).V).V`.

Need: `λ(t:V).λ(f:V).t ⊑ λ(z:V).λ(s:λ(_:V).V).V`.

By Lam-PW (outer): for all v ⊑ V:
`(λ(t:V).λ(f:V).t) v ⊑ (λ(z:V).λ(s:λ(_:V).V).V) v`
= `λ(f:V).v ⊑ λ(s:λ(_:V).V).V`

By Lam-PW: for all w ⊑ λ(_:V).V:
`(λ(f:V).v) w ⊑ (λ(s:λ(_:V).V).V) w = V`
= `v ⊑ V` ...wait, does `w ⊑ λ(_:V).V` satisfy `w ⊑ V`? Not necessarily.

But the domain of the subtype's lambda is V, and we're checking against the
supertype's domain `λ(_:V).V`. We need w to range over `λ(_:V).V` (the
supertype's domain), and check that `(λ(f:V).v) w ⊑ V`.

`(λ(f:V).v) w`: the domain check requires `w ⊑ V`. But `w ⊑ λ(_:V).V`.
Is `λ(_:V).V ⊑ V`? Not in general. So the application might fail.

Actually wait — Lam-PW as I stated it quantifies over `v ⊑ A` (the
supertype's domain). So we check `f v ⊑ B[x:=v]` for `v ⊑ A`. But `f`
is the SUBTYPE, and when we apply `f v`, we need `v` to be in f's domain.
If f = `λ(f:V).v` and v's domain is V, but we're applying to `w ⊑ λ(_:V).V`,
the domain check in the App rule requires `w ⊑ V`. This may fail.

This means the Lam-PW check itself can fail (the application gets stuck).
We'd need to handle this: either the rule says "if f v is well-defined, then
f v ⊑ B[x:=v]" (partial), or we require f to be applicable to all inputs
of the supertype's domain.

If we require applicability: then `true ⋢ Nat` because `(λ(f:V).t) w` with
`w ⊑ λ(_:V).V` fails the domain check `w ⊑ V`. Stuck ⟹ not applicable ⟹
subtyping fails. ✓ Still rejects correctly.

But then Lam-PW is VERY strict: it requires the subtype to accept ALL
inputs of the supertype's domain. This makes it equivalent to requiring
`A₂ ⊑ A₁` (the subtype must have a wider domain, i.e., the old contra
check) PLUS the body check. So Lam-PW with the applicability requirement
is strictly STRONGER than S-Lam.

Actually wait, S-Lam checks `A₂ ⊑ A₁` (supertype's domain ⊑ subtype's
domain, i.e., the subtype must accept MORE inputs). So the subtype's domain
is wider. In Lam-PW, we require `f v` to be defined for all `v ⊑ A₂`
(supertype's domain). If `f = λ(x:A₁).body`, this requires `v ⊑ A₁` for
the application to succeed. So we need `A₂ ⊑ A₁` (every input to the
supertype is also a valid input to the subtype).

So Lam-PW with applicability is equivalent to S-Lam. No help.

### What about Lam-PW without the applicability requirement?

```
[Lam-PW-Partial]
Γ ⊢ f ⊑ λ(x:A).B
  For all v ⊑ A: if f v is defined, then f v ⊑ B[x:=v]
  (f may be undefined on some inputs in A)
```

This is weaker: f doesn't need to accept all inputs of the supertype. It
only needs to produce correct outputs when it DOES accept an input.

Under this rule: `λ(x:Nat).x ⊑ λ(x:Type).x`?

For all v ⊑ Type: if `(λ(x:Nat).x) v` is defined, then `(λ(x:Nat).x) v ⊑ v`.

If v ⊑ Nat: `(λ(x:Nat).x) v = v ⊑ v` ✓.
If v ⋢ Nat: `(λ(x:Nat).x) v` is undefined. Vacuously true. ✓

So `λ(x:Nat).x ⊑ λ(x:Type).x` holds under Lam-PW-Partial! This would
rescue monotonicity for the counterexample.

But check `true ⋢ Nat`:
For all V ⊑ Type: `true V ⊑ Nat V`.

At the inner level:
`λ(f:V).t ⊑ λ(s:λ(_:V).V).V`

For all w ⊑ λ(_:V).V: if `(λ(f:V).t) w` is defined, then it ⊑ V.

Is `(λ(f:V).t) w` defined for w ⊑ λ(_:V).V? The application requires
w ⊑ V (domain of the lambda). If λ(_:V).V ⊑ V, then yes. But
λ(_:V).V ⊑ V is not generally provable... unless we add it?

Actually, with Lam-PW-Partial: `λ(_:V).V ⊑ V` would need to be checked.
If it fails, then for inputs w ⊑ λ(_:V).V that are NOT ⊑ V, the
application is undefined, and the check is vacuously true.

For inputs w that ARE ⊑ V (a subset of λ(_:V).V ∩ V): `(λ(f:V).t) w = t ⊑ V`.
Since t ⊑ V (from context). ✓

So `true ⊑ Nat` would HOLD under Lam-PW-Partial! ✗

The partial check is too weak — it vacuously accepts things it shouldn't
because it ignores inputs the subtype can't handle.

### Summary of Lam-PW analysis

| Rule | `true ⊑ Bool` | `true ⋢ Nat` | monotonicity |
|------|---------------|--------------|--------------|
| S-Lam (current) | ✓ | ✓ rejects | ✗ fails |
| Lam-PW (total) | ✓ | ✓ rejects | ✗ fails (equiv to S-Lam) |
| Lam-PW-Partial | ✓ | ✗ accepts | ✓ would rescue |

None of the three satisfies all requirements simultaneously.

---

## Exploring Fix #4: Monotonicity for Applied Results Only

### Observation: Anti-monotonicity cancels at application

The anti-monotone step produces a function type. When that function is
APPLIED, the result is monotone again:

```
Under A:Nat:   (λ(x:Nat).x) 3   ⇝  3
Under A:Type:  (λ(x:Type).x) 3  ⇝  3
```

Both give 3. The domain difference doesn't affect the output because 3 is
in both domains.

More generally: if `F₁ ⊑ F₂` (by S-Lam), then for `v ⊑ dom(F₂)`:
`F₁ v ⊑ F₂ v` (by S-App). But the REVERSE also works:

If F₁ and F₂ have different domains but agree on the intersection, and
`v ⊑ dom(F₁) ∩ dom(F₂)`, then both applications succeed and the
outputs are related by the body's behavior.

### "Observation Monotonicity"

Instead of requiring τ₂ ⊑ τ₁ for intermediate types, require it only for
types that are "observed" (used as inputs to further computation or returned
as final results).

A function type is observed when:
- It is applied to an argument (the App rule)
- It is checked by an ascription (the Asc rule)
- It is the final result of the program

For application: `F v` always gives a monotone result if the body is
monotone (since the substitution doesn't go through the domain). So
application "observes through" the anti-monotone layer.

For ascription: `(F : T)` checks `F ⊑ T`. If T is fixed, the check
might fail under narrowing (Prop 5.2.9). This is where ascription
interacts badly with dependent domains.

For final result: if the program returns a function as its final value,
the anti-monotonicity is visible. But in practice, programs return
ground values (numbers, booleans, etc.).

### Formal Statement

**Conjecture (Applied Monotonicity).** If `Γ₁ ⊢ e ⇝ τ₁` and `Γ₂ ⊑ Γ₁`,
and `e` is a term of "applied form" (every sub-expression of function type
is eventually applied), then `Γ₂ ⊢ e ⇝ τ₂` with `τ₂ ⊑ τ₁`.

This is hard to formalize precisely. A simpler version:

**Conjecture (Ground Monotonicity).** If `Γ₁ ⊢ e ⇝ τ₁` and `τ₁` is ground
(contains no lambda abstractions at top level), and `Γ₂ ⊑ Γ₁`, then
`Γ₂ ⊢ e ⇝ τ₂` with `τ₂ ⊑ τ₁`.

"Ground" terms: Church numerals, `Type`, `true`, `false`, `unit`.
"Non-ground" terms: anything of the form `λ(x:A).body`.

---

## The Ascription Problem Revisited

Even with Fix #4, there's a problem with ascription + dependent domains.
This is the original Prop 5.2.9:

```
Not = λ(X:Bool). X Bool false true
g = λ(B:Bool). (Not B : B)
```

Under B:Bool: `Not Bool =β Bool`. Check `Bool ⊑ Bool`. ✓
Under B:true: `Not true =β false`. Check `false ⊑ true`. ✗

The issue: the ascription target `B` narrows with the context, and the body
`Not B` narrows in the "wrong direction."

This is NOT a function-domain issue — it's a subtyping check where both sides
depend on the context, but in opposite directions. The LHS narrows (closer to
the concrete value), while the RHS also narrows (but doesn't track the LHS).

**Key insight:** The Asc rule checks `σ ⊑ τ` where both σ and τ may depend
on context variables. If σ and τ move in opposite directions as the context
narrows, the check can fail.

This is distinct from the function domain issue and needs a separate fix.

### What Makes Ascription Safe?

Ascription `(e : τ)` is safe when:
1. `e` and `τ` move in the SAME direction as the context narrows, or
2. `τ` is context-independent (a closed type)

Case 1: If narrowing the context makes `e` more precise AND makes `τ` more
precise in a compatible way, the check `e ⊑ τ` is preserved.

Case 2: If `τ` is closed (no free variables from Γ), then τ doesn't change
when Γ narrows, and monotonicity of `e` guarantees `e ⊑ τ` is preserved.

The Prop 5.2.9 example violates both: `Not B` is anti-monotone in B (because
Not negates), and `B` is monotone in B. They move in opposite directions.

### Structural Restriction for Safe Ascription

**Conjecture.** Ascription `(e : τ)` is safe (monotone under context
narrowing) if `τ` does not reference any context variable that `e`
referencing in a "negating" position.

This is hard to formalize without a polarity system. In Och, every position
is potentially mixed-variance because the language is higher-order.

**Alternative:** Restrict ascription so that `τ` must be "upward closed" —
if `σ ⊑ τ` and τ narrows to τ', then σ' ⊑ τ' (the check is preserved). This
is a semantic property, not a syntactic one.

---

## Concrete Proposal: Separate Soundness from Monotonicity

Given the difficulties, here is a practical path forward:

### Step 1: Prove soundness for closed terms (no monotonicity needed)

**Theorem.** If e is closed and e ⇓ v, then v ⊑ absEval(e).

Proof by induction on e ⇓ v:
- Value: trivial (v = e = absEval(e))
- Ascription: IH + ascription check
- Application: IH on sub-evaluations + pointwise S-Lam condition

The App case chain:
```
v ⊑ absEval(body_c[x:=v_a])              -- IH on sub-eval
  ⊑ absEval(body[x:=v_a])                -- term monotonicity
  = body[x:=v_a]                          -- if body[x:=v_a] is a value
```

And we need `body[x:=v_a] ⊑ body[x:=a']`. But both v_a and a' are
the concrete and abstract values of the argument.

**For closed terms, a' = absEval(a) and v_a is the concrete value.**

Wait, for closed terms without an environment, the abstract evaluation
uses no context at all. Every variable is substituted by the evaluation.
So the gap between v_a and a' is:
- a' = absEval(a) — the abstract value of the argument
- v_a = concreteEval(a) — the concrete value of the argument

By IH: v_a ⊑ a'. And the question is whether body is monotone in its
argument.

**For closed terms where the body doesn't contain ascription:**
transparency preservation tells us absEval(e) = concreteEval(e) for all
subterms. So v_a = a' and the gap doesn't exist.

**For closed terms WITH ascription in the body:** the gap is that
absEval(body[x:=v_a]) ≠ absEval(body[x:=a']) because ascription takes
different sides in concrete vs abstract mode. This is exactly where
soundness and monotonicity interact.

The closed-term soundness proof can proceed if we can show
"term monotonicity": absEval is monotone in the input term. This
requires that absEval(A) ⊑ absEval(B) whenever A ⊑ B. This is a
restricted form of monotonicity that avoids the environment issue.

### Step 2: Extend to open terms using a "widening" argument

For open terms with Γ, we observe:
- absEval_Γ(e) gives type τ where variables are abstract
- absEval_∅(eγ) gives type τ' where variables are concrete

The abstract evaluation with concrete inputs (τ') is MORE precise
than with abstract inputs (τ), IF monotonicity holds. Since it doesn't
hold in general, we need a weaker argument.

**Alternative: prove soundness directly by induction on the typing derivation
Γ ⊢ e ⇝ τ, without factoring through closed terms.**

The App case then requires: if bodyγ[x:=v_a] ⇓ v, then v ⊑ (body[x:=a'])γ.

We have body_c (from concrete eval of f) with body_c ⊑ bodyγ (from IH, pointwise).

body_c[x:=v_a] ⊑ bodyγ[x:=v_a] (instantiate pointwise).

body_c[x:=v_a] ⇓ v. By "term soundness" (recursive use): v ⊑ absEval(body_c[x:=v_a]).

But absEval(body_c[x:=v_a]) is evaluated in the EMPTY context (both sides are closed after substitution). This evaluation doesn't need environment monotonicity.

And we need: v ⊑ bodyγ[x:=a'γ] = (body[x:=a'])γ.

The chain is: v ⊑ absEval(body_c[x:=v_a]) ⊑ₜₘ bodyγ[x:=v_a] ⊑ₑₙᵥ bodyγ[x:=a'γ].

The first ⊑ is by IH. The second (⊑ₜₘ, "term monotonicity") requires 
body_c[x:=v_a] ⊑ bodyγ[x:=v_a] implies their abstract evaluations are 
related. The third (⊑ₑₙᵥ, "env monotonicity") is the problematic step.

**We're stuck in the same place.** No matter how we restructure, the gap
between `v_a` and `a'γ` in the substitution requires some form of
monotonicity.

### Step 3: Accept the limitation and state a conditional soundness

**Theorem (Conditional Soundness).** If `Γ ⊢ e ⇝ τ` and `γ ⊨ Γ` and
`eγ ⇓ v`, and **every sub-derivation's App case involves a body that is
monotone in its bound variable** (i.e., no lambda in the body has the
bound variable in its domain, or the body is ascription-free), then `v ⊑ τγ`.

This holds for all the test cases in §6, since none of them involve the
anti-monotone pattern.

---

## Summary

| Property | Status | Key Issue |
|----------|--------|-----------|
| Ascription soundness | ✓ Proved | Trivial from rule |
| Transparency preservation | ✓ Proved | No ascription = no divergence |
| Full monotonicity | ✗ Fails | Dependent domains + contra |
| Full soundness | ✗ Blocked | Depends on monotonicity |
| Restricted monotonicity (ground results) | ? Plausible | Needs formalization |
| Restricted soundness (no anti-monotone bodies) | ? Plausible | Covers all test cases |
| Closed-term soundness (no env) | ? Plausible | Needs term monotonicity |

### Recommendations

1. **The monotonicity failure is fundamental**, not a proof artifact. Any
   system with (dependent domains + contravariant function subtyping) will
   have this issue. The question is how to live with it.

2. **For Ochre's strong mutation**, monotonicity is needed. The resolution
   likely requires restricting WHAT can appear in domain position (e.g.,
   only closed types, or types annotated as "stable"). This is a language
   design choice, not a proof choice.

3. **For soundness of Och**, the restriction "no anti-monotone bodies"
   covers all practical programs. Formal soundness could be stated with
   this restriction, acknowledging that the unrestricted case is open.

4. **The Prop 5.2.9 phenomenon IS the monotonicity failure.** It manifests
   differently (ascription check failure vs. subtyping direction flip) but
   has the same root cause: context narrowing can reverse the direction of
   a type-level relationship when dependent domains are involved.
