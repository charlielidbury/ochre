# The Domain Erasure Insight

## The Observation

At runtime, domain annotations in lambdas are erased (§4.1). This means:

```
true = λ(X:Type).λ(t:X).λ(f:X).t
0    = λ(X:Type).λ(z:X).λ(s:λ(_:X).X).z
```

Are the SAME runtime value: `λ_.λa.λ_.a` (select second argument).

Similarly:
```
false = λ(X:Type).λ(t:X).λ(f:X).f
```

And there is no Church numeral with the same behavior as `false` — `false`
selects the THIRD argument, while every Church numeral `n` applies `s` n
times to `z`. For n=0, it selects the second argument (= true). For n≥1,
it returns `s(...(s z)...)` which selects the third argument only if `s` is
the identity.

Wait, let me reconsider:
```
1 = λ(X:Type).λ(z:X).λ(s:λ(_:X).X). s z
```

At runtime: `λ_.λz.λs. s z`. This is NOT `false = λ_.λt.λf.f`. Because
`1` applies `s` to `z`, while `false` just returns `f`. These are different:
`1 X z s = s z` while `false X t f = f`. If `s = id` and `z = t = 42` and
`f = 99`, then `1 X 42 id = 42` but `false X 42 99 = 99`.

So `false ≠ 1` even at runtime. ✓ Good — only `true = 0`.

### Full Collapsing Analysis

Which Church-encoded values coincide at runtime (after domain erasure)?

- `true = 0` — both are `λ_.λa.λ_. a`
- `unit` vs `true`/`0`: `unit = λ(X:Type).λ(x:X).x = λ_.λa.a` (2-arg).
  `true = λ_.λa.λ_.a` (3-arg). Different arities? Not really — in untyped
  lambda calculus, `λ_.λa.a` applied to three args gives: `(λa.a) arg2 arg3`.
  First: `λa.a` applied to arg2 = arg2. Then arg2 applied to arg3. So
  `unit X t f = t f`, while `true X t f = t`. Different! (unless t doesn't
  use its argument).
  
  Actually, `unit = λ(X:Type).λ(x:X).x`. Applied to Type, then t, then f:
  `unit Type t f = (λ(x:Type).x) t f = t f`. Because unit is the identity,
  it passes f through to t.
  
  `true Type t f = t`. Just returns t.
  
  So `unit ≠ true` at runtime when t uses its argument. ✓

- `id = λ(T:Type).λ(x:T).x` = unit (same thing). ✓

So the only "unexpected" collapse is `true = 0`.

## Implications for the Type System

### Semantic Subtyping Should Reflect Runtime

If `true` and `0` are the same runtime value, then any sound type system
must assign them compatible types. Specifically:

- If `0 : Nat`, and `true = 0` at runtime, then `true : Nat` should hold
  for runtime soundness.
- Similarly, if `true : Bool`, then `0 : Bool` should hold.

The current rules say `true ⋢ Nat` and `0 ⋢ Bool`. This is STRICTER than
necessary for soundness — it's a design choice to treat domain annotations
as meaningful for type identity.

### When Does the Distinction Matter?

The distinction between `true` and `0` (via their domain annotations) matters
for:

1. **Error messages**: If someone passes `true` where a `Nat` is expected,
   the type error is helpful.
2. **Partitioning**: `isZero` partitions Nat into `{0, succ k}`. If `true`
   is also in Nat, partitioning needs to account for it (but `true` behaves
   like `0`, so it's fine).
3. **Extensional behavior under Church elimination**: `true X z s = z` and
   `0 X z s = z` — same behavior. So they're indistinguishable by any
   Church-encoded operation.

The distinction does NOT matter for soundness, correctness, or behavior.

### Connection to Monotonicity

The domain-level anti-monotonicity counterexample:
```
Under A:Type: f A ⇝ λ(x:Type).x
Under A:Nat:  f A ⇝ λ(x:Nat).x
```

At runtime, both are the same function (`λ_.λx.x` — identity). The subtyping
failure `λ(x:Nat).x ⋢ λ(x:Type).x` is an artifact of treating domains as
meaningful in subtyping. If we acknowledge that these are the same runtime
value, the "failure" evaporates.

### Formal Two-Level Framework

Define:
- **Syntactic type** (`σ`): An Och term, including domain annotations
- **Runtime type** (`ρ`): An Och term with all domain annotations replaced by `Type`
- **Erasure** (`⌊·⌋`): `⌊λ(x:A).body⌋ = λ(x:Type).⌊body⌋`. All other
  forms are unchanged (variables, Type, applications, ascriptions).

Define runtime subtyping: `ρ₁ ⊑ᵣ ρ₂ iff ⌊ρ₁⌋ ⊑ ⌊ρ₂⌋` using the
standard subtyping rules.

Note: `⌊λ(x:Nat).x⌋ = λ(x:Type).x = ⌊λ(x:Type).x⌋`. So
`λ(x:Nat).x ⊑ᵣ λ(x:Type).x` iff `λ(x:Type).x ⊑ λ(x:Type).x` = Refl. ✓

**Theorem (Runtime Monotonicity).** If `Γ₁ ⊢ e ⇝ τ₁` and `Γ₂ ⊑ Γ₁`, then
`Γ₂ ⊢ e ⇝ τ₂` with `⌊τ₂⌋ ⊑ ⌊τ₁⌋`.

This says: monotonicity holds up to domain erasure.

**Proof sketch.**

The only case where full monotonicity fails is when `τ` contains a lambda
with a context variable in the domain. After erasure, all domains become
Type, so the domain difference disappears.

Case App: `τ₁ = body[x:=a'₁]`, `τ₂ = body[x:=a'₂]` with `a'₂ ⊑ a'₁`.

`⌊τ₂⌋ = ⌊body[x:=a'₂]⌋` and `⌊τ₁⌋ = ⌊body[x:=a'₁]⌋`.

After erasure, any lambda `λ(y:D).e` in body becomes `λ(y:Type).⌊e⌋`.
The variable `x` may appear in `D`, but after erasure, `D` is replaced by
Type, so the substitution `x:=a'₂` vs `x:=a'₁` doesn't affect the domain.

The body part `⌊e⌋` still has `x` (if x appears in e), and the substitution
does affect it. But body subtyping is covariant, so `⌊e[x:=a'₂]⌋ ⊑ ⌊e[x:=a'₁]⌋`
follows from `a'₂ ⊑ a'₁` and body covariance.

Wait — does body covariance hold after erasure? The body could contain
nested lambdas, whose domains are erased. After erasure, the nested
lambdas all have domain Type. The body check under the ERASED domain
(Type) is just checking that the bodies are related.

Let me verify with the counterexample:

`body = λ(x:A).x`. After erasure: `⌊λ(x:A).x⌋ = λ(x:Type).x`.
`body[A:=Nat] = λ(x:Nat).x`. `⌊·⌋ = λ(x:Type).x`.
`body[A:=Type] = λ(x:Type).x`. `⌊·⌋ = λ(x:Type).x`.

Both give the same erased form! ✓ No monotonicity issue.

For the BODY of the lambda (the `x` part): `x` doesn't depend on A, so
it's the same after both substitutions. ✓

For a more complex case: `body = λ(x:A). f x` where `f : A → Nat`.
After erasure: `⌊λ(x:A). f x⌋ = λ(x:Type). ⌊f x⌋ = λ(x:Type). f x`.
(f x is an application, unchanged by erasure.)

`body[A:=Nat] = λ(x:Nat). f x`. Erased: `λ(x:Type). f x`.
`body[A:=Type] = λ(x:Type). f x`. Erased: `λ(x:Type). f x`.

Same. ✓

Now, `f` might also be affected by the substitution (if f mentions A).
But f's domain annotation is erased, so any lambda in f's definition also
gets domain-erased. The covariant body parts of f are handled recursively.

**This argument works because erasure eliminates ALL domains, so the only
part of the term that changes under substitution is the body parts, which
are covariant.**

### Soundness with Runtime Subtyping

**Theorem (Soundness).** If `Γ ⊢ e ⇝ τ` and `γ ⊨ Γ` and `eγ ⇓ v`, then
`v ⊑ᵣ τγ` (i.e., `⌊v⌋ ⊑ ⌊τγ⌋`).

Note: `v` is a concrete value (domains already erased by runtime), so
`⌊v⌋ = v` (or more precisely, `v` already has `Type` in all domain
positions since it came from concrete evaluation).

Actually wait — concrete evaluation doesn't erase domain annotations from
lambdas! Looking at §4.1:

```
(λ(x: τ). e) v  ⟶  e[x := v]            -- β-reduction
(e : τ)          ⟶  e                     -- ascription erased at runtime
```

The lambda's domain annotation τ is preserved syntactically — it's just not
checked at runtime. So `(λ(x:Nat).x) 3 ⟶ 3`, and the resulting value is
`3`, which is `λ(X:Type).λ(z:X).λ(s:λ(_:X).X).s(s(s z))`. The domain
annotations are still there!

Hmm, but the domain annotations in the VALUE come from the original source
code, not from the evaluation. So the value `λ(x:D).body` has whatever
domain D was written by the programmer.

For soundness, we need `v ⊑ₛ τγ` (standard subtyping, including domain
checks). If monotonicity fails for standard subtyping, soundness might too.

OR we state soundness with runtime subtyping:

`v ⊑ᵣ τγ` — the runtime value is semantically compatible with the abstract
type, up to domain erasure.

This is a WEAKER soundness statement but still useful: it says the runtime
behavior of the program is consistent with the abstract type's behavioral
specification (ignoring domain annotations).

### What Does Runtime Soundness Buy You?

If `v ⊑ᵣ τ`, then for any context C[] that observes v through Church
elimination (applying v to arguments):
- If C[v] terminates, C[τ] terminates with a result that is ⊑ᵣ.
- The observed behavior of v is consistent with τ's specification.

This is "behavioral" or "observational" soundness. It's weaker than full
syntactic soundness but arguably what you actually want for a programming
language: the runtime behavior matches the type specification.

The gap (v ⊑ᵣ τ but not v ⊑ₛ τ) only arises when v and τ differ in domain
annotations. Since domain annotations are erased at runtime, this gap
has no runtime consequence.

---

## Summary

1. **Domain annotations are erased at runtime.** This is by design (§4.1).

2. **Erased values can be members of multiple types.** `true` and `0` are
   the same runtime value, so both can be in Bool and Nat.

3. **Standard (syntactic) subtyping is stricter than necessary.** It uses
   domain annotations to distinguish types, creating anti-monotonicity when
   domains depend on context variables.

4. **Runtime subtyping (domain-erased) is monotone.** After erasure, the
   domain-based anti-monotonicity disappears because all domains become Type.

5. **Soundness can be stated with runtime subtyping.** This gives a
   behavioral guarantee: runtime values behave consistently with their
   abstract types, ignoring domain annotations.

6. **The Prop 5.2.9 counterexample involves body anti-monotonicity, not
   domain anti-monotonicity.** This is a separate issue that domain erasure
   does not fix. `Not` is genuinely anti-monotone in its body behavior.

### Open Question

Can soundness with FULL (syntactic) subtyping be proved? This requires
monotonicity of abstract evaluation with respect to syntactic subtyping,
which fails for the domain counterexample.

Two possible paths:
- Prove that the domain counterexample never arises in the App case of
  the soundness proof (because v_a and a' have the same domain structure)
- Accept runtime soundness as sufficient and prove monotonicity only for
  runtime subtyping
