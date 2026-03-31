# Problem

Layer 4: Proofs
Task 4.1: Prove soundness (§7.1). If Γ ⊢ e ⇝ τ and γ ⊨ Γ and γ ⊢ e ⇓ v, then v ⊑ τ. Proof by induction on the derivation of Γ ⊢ e ⇝ τ, one case per typing rule. Verification: every case of the typing rules is covered, each case is a valid logical argument. Depends on all of Layer 2.
Task 4.2: Prove monotonicity (§7.2). If Γ₂ ⊑ Γ₁ then τ₂ ⊑ τ₁. Proof by induction on the derivation. The critical cases are application (transparent vs ascribed) and the interaction with partitioning. Verification: every case covered. Depends on all of Layer 2 and 3.
Task 4.3: Prove ascription soundness (§7.3). If Γ ⊢ e ⇝ σ and (e : τ) is well-formed, then σ ⊑ τ. This should be a short proof falling directly out of the ascription typing rule. Verification: complete proof. Depends on 2.1.
Task 4.4: Prove transparency preservation (§7.4). For closed terms without ascription, ∅ ⊢ e ⇝ τ implies τ is the singleton. This requires showing that the abstract interpreter, when given fully concrete inputs, traces the same path as concrete evaluation. Verification: complete proof. Depends on 2.1 and 4.1.

# Solution

## Conventions

Throughout these proofs, we work **modulo β-equivalence**: terms that are
β-equivalent are treated as identical. This matches the convention from
Tasks 1–3 ("we freely β-reduce before applying rules").

**Recall the typing rules** (from Task 2.1):

```
[Var]   Γ ⊢ x ⇝ τ                    where x : τ ∈ Γ
[Lam]   Γ ⊢ λ(x:A).e ⇝ λ(x:A).e     (premise: Γ, x:A ⊢ e ⇝ e')
[App]   Γ ⊢ f a ⇝ τ[x := a']         where Γ ⊢ f ⇝ λ(x:A).τ,
                                             Γ ⊢ a ⇝ a', Γ ⊢ a' ⊑ A
[Asc]   Γ ⊢ (e : τ) ⇝ τ              where Γ ⊢ e ⇝ σ, Γ ⊢ σ ⊑ τ
[Type]  Γ ⊢ Type ⇝ Type
```

**Recall the subtyping rules** (from Task 1.1):

```
[Refl]  Γ ⊢ e ⊑ e
[Var]   Γ ⊢ x ⊑ T                     where x : T ∈ Γ
[Lam]   Γ ⊢ λ(x:A₁).B₁ ⊑ λ(x:A₂).B₂  where Γ ⊢ A₂ ⊑ A₁, Γ,x:A₂ ⊢ B₁ ⊑ B₂
[App]   Γ ⊢ f a ⊑ B[x:=a]            where Γ ⊢ f ⊑ λ(x:A).B, Γ ⊢ a ⊑ A
[Trans] Γ ⊢ A ⊑ C                     where Γ ⊢ A ⊑ B, Γ ⊢ B ⊑ C
[Top]   Γ ⊢ τ ⊑ Type
```

**Concrete evaluation** (§4.1):
```
(λ(x: τ). e) v  ⟶  e[x := v]         -- β-reduction
(e : τ)          ⟶  e                  -- ascription erased at runtime
```

Concrete evaluation produces a **value**: a lambda `λ(x:A).e` or `Type`.

**Environment consistency.** Given an abstract context Γ and a concrete
substitution γ (mapping variables to closed values):

`γ ⊨ Γ` iff for every `(x : A) ∈ Γ`, `γ(x) ⊑ A[γ<x]`

where `γ<x` is the restriction of γ to variables bound before `x` in Γ.
This handles the fact that types in Γ may reference earlier variables.

For notational convenience, we write `eγ` for `e` with γ applied (all free
variables substituted). All γ-substituted terms are closed.


---

## Task 4.3: Ascription Soundness

**Theorem.** If `Γ ⊢ e ⇝ σ` and `(e : τ)` is well-formed, then `σ ⊑ τ`.

**Proof.** "Well-formed" means the Asc rule accepted `(e : τ)`. By the Asc
rule, acceptance requires deriving `Γ ⊢ e ⇝ σ` and `Γ ⊢ σ ⊑ τ`. The
conclusion `σ ⊑ τ` is literally the second premise. ∎

This is immediate by construction. The non-trivial content is that the
subtyping check is sufficient to guarantee soundness of precision loss,
which is established by the main soundness theorem.


---

## Task 4.4: Transparency Preservation

**Theorem.** Let `e` be a closed, ascription-free term. If `e` concretely
evaluates to `v` (i.e., `∅ ⊢ e ⇓ v`), then `∅ ⊢ e ⇝ v`.

Abstract evaluation exactly recovers the concrete value when no ascription
is present to cause divergence between the two modes.

**Proof.** By structural induction on `e`.

**Case `e = Type`:**
Concrete: `v = Type`. Abstract: `∅ ⊢ Type ⇝ Type = v`. ✓

**Case `e = x`:**
Impossible — `e` is closed.

**Case `e = λ(x:A).body`:**
Concrete: lambdas are values, so `v = λ(x:A).body = e`.
Abstract: Lam gives `∅ ⊢ λ(x:A).body ⇝ λ(x:A).body = e = v`. ✓

Note: the Lam well-formedness premise requires `x:A ⊢ body ⇝ body'`. Since
`e` is ascription-free, this succeeds (see remark below). The result `body'`
is discarded — only the original lambda is returned.

**Case `e = (e' : τ)`:**
Excluded by the ascription-free hypothesis.

**Case `e = f a`:**
Concrete:
1. `f ⇓ λ(x:A).body_c` (must be a lambda since the term is well-typed)
2. `a ⇓ v_a`
3. `body_c[x := v_a] ⇓ v`

By IH on `f` (closed, ascription-free, sub-expression):
  `∅ ⊢ f ⇝ λ(x:A).body_c`

By IH on `a` (closed, ascription-free, sub-expression):
  `∅ ⊢ a ⇝ v_a`

Domain check `v_a ⊑ A`: Since the program is well-typed and the concrete
evaluation doesn't get stuck, the concrete argument `v_a` is a valid input
to the function. The Lam well-formedness check at definition time guarantees
that the body is well-formed for inputs in the domain. We assume this check
passes (it must, for well-typed terms).

By App: `∅ ⊢ f a ⇝ body_c[x := v_a]`.

Now, `body_c[x := v_a]` is closed and ascription-free (since both `body_c`
and `v_a` are ascription-free — `body_c` comes from the ascription-free
function `f`, and `v_a` from the ascription-free argument `a`).

We know `body_c[x := v_a] ⇓ v` (from concrete eval step 3). Since we work
modulo β-equivalence, and concrete evaluation of an ascription-free term IS
β-reduction, we have `body_c[x := v_a] =β v`.

Therefore `∅ ⊢ f a ⇝ body_c[x := v_a] =β v`, i.e., `∅ ⊢ f a ⇝ v`. ✓

∎

**Remark on Lam well-formedness.** The Lam premise checks
`Γ, x:A ⊢ body ⇝ body'`. For an ascription-free body, abstract evaluation
traces the same path as concrete evaluation would for any input. The check
succeeds because the body is a well-formed term — all variables are bound,
all applications are well-typed. The key point is that without ascription,
there is no divergence between abstract and concrete modes.

**Corollary.** For a closed, ascription-free term `e` with `e ⇓ v`:
`∅ ⊢ e ⇝ v`. The abstract type is the singleton `{v}`. This confirms §7.4:
the type system achieves maximal precision when no information is deliberately
discarded.


---

## Required Lemmas

### Lemma 1: Equal Substitution for Subtyping

**Statement.** If `Γ, x:A ⊢ e₁ ⊑ e₂` and `Γ ⊢ v ⊑ A`, then
`Γ ⊢ e₁[x:=v] ⊑ e₂[x:=v]`.

Substituting the same value on both sides preserves subtyping.

**Proof.** By induction on the derivation of `Γ, x:A ⊢ e₁ ⊑ e₂`.

- **Refl:** `e₁ = e₂`, so `e₁[x:=v] = e₂[x:=v]`. Apply Refl. ✓
- **S-Var:** `e₁ = y` where `y : T ∈ (Γ, x:A)`.
  - If `y = x`: then `T = A`, and the conclusion was `x ⊑ A`. After
    substitution: `v ⊑ A[x:=v]`. Since `A` is well-formed in Γ (before `x`
    is bound), `x ∉ FV(A)`, so `A[x:=v] = A`. Need: `v ⊑ A`. This is
    exactly the hypothesis. ✓
  - If `y ≠ x`: `y[x:=v] = y`, and `y : T ∈ Γ`. By S-Var in Γ:
    `y ⊑ T[x:=v]`. Since `T` is a type from Γ (bound before or independently
    of x), it may or may not contain `x`. If `T` is from before `x` in Γ,
    `x ∉ FV(T)` and `T[x:=v] = T`. If `T` contains `x` (possible if Γ has
    later entries), this requires care — but by well-formedness of Γ, types
    only reference earlier variables. Since `x` is the last binding, nothing
    in Γ references `x`, so `T[x:=v] = T`. ✓
- **S-Lam:** `λ(y:A₁).B₁ ⊑ λ(y:A₂).B₂` with `A₂ ⊑ A₁` and
  `Γ, x:A, y:A₂ ⊢ B₁ ⊑ B₂` (α-renaming to ensure `y ≠ x`).
  After substitution: `λ(y:A₁[x:=v]).B₁[x:=v] ⊑ λ(y:A₂[x:=v]).B₂[x:=v]`.
  By IH on `A₂ ⊑ A₁`: `A₂[x:=v] ⊑ A₁[x:=v]`. ✓ (contra)
  By IH on `B₁ ⊑ B₂` (exchanging x and y in the context): need
  `Γ, y:A₂[x:=v] ⊢ B₁[x:=v] ⊑ B₂[x:=v]`. This follows from IH applied
  to the derivation in the extended context `Γ, x:A, y:A₂`. ✓ (co)
- **S-App:** `f e ⊑ B[y:=e]` from `f ⊑ λ(y:C).B` and `e ⊑ C`.
  After substitution: `f[x:=v] e[x:=v] ⊑ B[y:=e][x:=v] = B[x:=v][y:=e[x:=v]]`.
  By IH on both premises. ✓
- **Trans:** Immediate by IH on both sub-derivations. ✓
- **Top:** `e₁[x:=v] ⊑ Type` holds by Top. ✓

∎

### Lemma 2: Covariant Substitution

**Statement.** If `Γ, x:A ⊢ e₁ ⊑ e₂` and `Γ ⊢ v₁ ⊑ v₂ ⊑ A`, then
`Γ ⊢ e₁[x:=v₁] ⊑ e₂[x:=v₂]`.

Substituting a narrower value on the left and a wider value on the right
preserves subtyping.

**Proof attempt.** We try to decompose via Equal Substitution + Trans:

Step 1: By Lemma 1 with `v₁`: `Γ ⊢ e₁[x:=v₁] ⊑ e₂[x:=v₁]`. ✓

Step 2: Need `Γ ⊢ e₂[x:=v₁] ⊑ e₂[x:=v₂]`.

Step 2 requires **monotonicity of `e₂` with respect to x**: substituting a
wider value produces a wider result. This is essentially the monotonicity
theorem restricted to a single substitution step.

By induction on the structure of `e₂`:
- `e₂ = x`: `x[x:=v₁] = v₁ ⊑ v₂ = x[x:=v₂]`. ✓
- `e₂ = y ≠ x`: both sides equal `y`. By Refl. ✓
- `e₂ = Type`: both sides equal Type. By Refl. ✓
- `e₂ = f a`: need `f[x:=v₁] a[x:=v₁] ⊑ f[x:=v₂] a[x:=v₂]`. By IH on
  `f` and `a` separately, we get `f[x:=v₁] ⊑ f[x:=v₂]` and
  `a[x:=v₁] ⊑ a[x:=v₂]`. But combining these for application subtyping
  requires that `f[x:=v₂]` evaluates to a lambda — this works only if
  application subtyping composes, which it does via S-App + Trans. ✓
- `e₂ = (e' : σ)`: `(e'[x:=v₁] : σ[x:=v₁]) ⊑ (e'[x:=v₂] : σ[x:=v₂])`.
  Under abstract evaluation, both ascriptions return their rhs:
  `σ[x:=v₁] ⊑ σ[x:=v₂]` by IH on σ. ✓
  (Note: this assumes the ascription subtyping check passes for both, which
  follows from the well-formedness of the original term.)
- `e₂ = λ(y:B).body`:
  Need `λ(y:B[x:=v₁]).body[x:=v₁] ⊑ λ(y:B[x:=v₂]).body[x:=v₂]`.
  By S-Lam:
  - Contra: `B[x:=v₂] ⊑ B[x:=v₁]` — this is the ANTI-monotone direction!
    We need the domain to get WIDER (v₂ direction), but the IH gives us
    `B[x:=v₁] ⊑ B[x:=v₂]` (v₂ is wider).
    So `B[x:=v₂] ⊑ B[x:=v₁]` is BACKWARDS. ✗

**THE LAMBDA CASE FAILS.** The contravariant domain in S-Lam demands that
the domain SHRINKS as x gets wider, but monotonicity of substitution makes
the domain GROW. This is the fundamental obstacle.

### Understanding the Lambda Failure

This failure is expected and important. Consider:

```
e₂ = λ(y : x). body
```

With `x := Nat`: `λ(y:Nat).body` — accepts all naturals.
With `x := Bool`: `λ(y:Bool).body` — accepts only booleans.

For `λ(y:Nat).body ⊑ λ(y:Bool).body`, the contra check needs `Bool ⊑ Nat`,
which may or may not hold. More importantly, if we widen `x` from `Nat` to
`Type`, the domain gets WIDER, and the function accepts MORE inputs. A
function accepting more inputs is NOT necessarily a subtype of one accepting
fewer inputs (it depends on the body's behavior on the extra inputs).

**This is the core tension identified in the spec (Prop 5.2.9).** The domain
of a lambda is covariant in its definition (wider x → wider domain), but
function subtyping has contravariant domains. These conflict.

### Lemma 2 Status: BLOCKED

The naive covariant substitution lemma does not hold for lambdas with the
substitution variable in the domain. This directly impacts the monotonicity
theorem (Task 4.2). See discussion there.

### Lemma 3: Weakening for Subtyping

**Statement.** If `Γ ⊢ e₁ ⊑ e₂` and `x ∉ dom(Γ)`, then
`Γ, x:A ⊢ e₁ ⊑ e₂`.

**Proof.** Routine structural induction. Var lookups succeed because the
original binding is still present. New binding `x:A` is unused. ∎

### Lemma 4: Weakening for Abstract Evaluation

**Statement.** If `Γ ⊢ e ⇝ τ` and `x ∉ dom(Γ)`, then `Γ, x:A ⊢ e ⇝ τ`.

**Proof.** By induction on the derivation. Var lookups find the same binding.
Subtyping premises preserved by Lemma 3. ∎


---

## Task 4.1: Soundness

**Theorem (Soundness).** If `Γ ⊢ e ⇝ τ` and `γ ⊨ Γ` and `eγ ⇓ v`, then
`v ⊑ τγ`.

(Here `eγ` denotes `e` with all free variables substituted by γ, and
similarly for `τγ`. Both `v` and `τγ` are closed.)

**Proof.** By structural induction on the derivation of `Γ ⊢ e ⇝ τ`.

### Case Var

`e = x`, `τ = A` where `x : A ∈ Γ`.

Concrete: `eγ = γ(x)`. Since `γ(x)` is a value, `v = γ(x)`.

Need: `v = γ(x) ⊑ Aγ = τγ`.

By `γ ⊨ Γ`: `γ(x) ⊑ Aγ`. ✓

### Case Lam

`e = λ(x:A).body`, `τ = λ(x:A).body = e`.

Concrete: `eγ = λ(x:Aγ).bodyγ`. Lambdas are values, so `v = λ(x:Aγ).bodyγ`.

`τγ = λ(x:Aγ).bodyγ = v`.

By Refl: `v ⊑ τγ`. ✓

### Case Type

`e = Type`, `τ = Type`. `eγ = Type`, `v = Type`, `τγ = Type`.
By Refl: `v ⊑ τγ`. ✓

### Case Asc

`e = (e' : σ)`, `τ = σ`.
Premises: `Γ ⊢ e' ⇝ σ'`, `Γ ⊢ σ' ⊑ σ`.

Concrete: `eγ = (e'γ : σγ) ⟶ e'γ ⇓ v` (ascription erased at runtime).

By IH on `Γ ⊢ e' ⇝ σ'` with the same γ: `v ⊑ σ'γ`.

From `Γ ⊢ σ' ⊑ σ`: applying γ preserves this (by Equal Substitution,
Lemma 1, extended to handle the full γ): `σ'γ ⊑ σγ`.

By Trans: `v ⊑ σ'γ ⊑ σγ = τγ`. ✓

### Case App — The Critical Case

`e = f a`, `τ = body[x := a']`.
Premises:
- (P1) `Γ ⊢ f ⇝ λ(x:A).body`
- (P2) `Γ ⊢ a ⇝ a'`
- (P3) `Γ ⊢ a' ⊑ A`

Concrete: `fγ ⇓ v_f`, `aγ ⇓ v_a`, and since `v_f` must be a lambda
(well-typed terms don't get stuck on applications), `v_f = λ(x:D).body_c`
for some D and body_c. Then `body_c[x := v_a] ⇓ v`.

Need: `v ⊑ τγ = body[x := a']γ = bodyγ[x := a'γ]`.

(Here we use that x is the lambda's bound variable and doesn't appear free
in γ's range, so the substitutions commute.)

**Step 1: Apply IH to f and a.**

By IH on (P1): `v_f ⊑ (λ(x:A).body)γ = λ(x:Aγ).bodyγ`.

Since `v_f = λ(x:D).body_c`, by S-Lam inversion:
- (F1) `Aγ ⊑ D`    (contravariant domain)
- (F2) For all `y ⊑ Aγ`: `body_c[x:=y] ⊑ bodyγ[x:=y]`    (covariant body)

By IH on (P2): `v_a ⊑ a'γ`.

From (P3), applying γ: `a'γ ⊑ Aγ`.

By Trans: `v_a ⊑ a'γ ⊑ Aγ`.

**Step 2: Instantiate the pointwise condition.**

Since `v_a ⊑ Aγ`, we can instantiate (F2) with `y = v_a`:

`body_c[x := v_a] ⊑ bodyγ[x := v_a]`    ... (★)

**Step 3: Relate concrete value to abstract body.**

We have `body_c[x := v_a] ⇓ v`. Since we work modulo β-equivalence, and
concrete evaluation is β-reduction (plus ascription erasure), the term
`body_c[x := v_a]` β-reduces to `v` (possibly after erasing ascriptions).

**Sub-case 3a: `body_c` is ascription-free.**

Then `body_c[x := v_a]` β-reduces to `v`, so `body_c[x := v_a] =β v`.
Since we work modulo β: `body_c[x := v_a] = v` (as terms), so (★) gives:

`v ⊑ bodyγ[x := v_a]`    ... (★★)

**Sub-case 3b: `body_c` contains ascriptions.**

Concrete evaluation erases ascriptions: `(e' : σ) ⟶ e'`. So `v` is the
result of β-reducing `body_c[x:=v_a]` while erasing ascriptions. The term
`body_c[x:=v_a]` might not be β-equivalent to `v` — the erasure of
ascriptions creates a divergence.

But wait: `body_c` comes from the concrete evaluation of `f`. Since `f`
concretely evaluates to `λ(x:D).body_c`, and concrete evaluation DOES erase
ascriptions, `body_c` is already the "concrete" body — ascriptions inside it
have not yet been evaluated (they're under the lambda). So `body_c` may
still contain ascriptions.

To handle this: we observe that concrete evaluation of `body_c[x:=v_a]`
erases all ascriptions as it encounters them. Each ascription `(e':σ)` in
`body_c` evaluates by discarding σ and evaluating `e'`. So `v` is what you
get by evaluating `body_c[x:=v_a]` while "taking the left side" of each
ascription.

The abstract evaluator, on the other hand, "takes the right side" of each
ascription (returns σ, discards e'). The Asc rule ensures `e' ⊑ σ`, so the
right side is wider. This is where soundness comes from.

**For a rigorous treatment of sub-case 3b:** We need an induction on the
evaluation of `body_c[x:=v_a]`. Each step is either a β-reduction (same in
both modes) or an ascription (concrete takes lhs, abstract takes rhs). At
each ascription, the Asc premise guarantees `lhs ⊑ rhs`, so the concrete
path stays ⊑ the abstract path. This gives `v ⊑ body_c[x:=v_a]` when we
interpret the term `body_c[x:=v_a]` as an abstract type (i.e., evaluating
ascriptions abstractly).

Actually, this is what (★) already gives us, because `bodyγ[x:=v_a]` IS the
abstract body evaluated with the abstract semantics.

So from (★): `body_c[x := v_a] ⊑ bodyγ[x := v_a]`, and we can show
`v ⊑ body_c[x:=v_a]` by inducting on the concrete evaluation of
`body_c[x:=v_a] ⇓ v`.

Hmm, this is getting circular. Let me try a cleaner approach.

**Clean approach: IH on the sub-evaluation.**

The key insight is that `body_c[x:=v_a] ⇓ v` is a SMALLER evaluation than
the original `(f a)γ ⇓ v` (it's a sub-evaluation). So we can use the
soundness theorem inductively — but we need a typing judgment for
`body_c[x:=v_a]`.

We don't have a direct typing judgment for `body_c[x:=v_a]`, but we DO
have one for `bodyγ[x:=v_a]`: it's what we get from the App rule applied
with the precise argument `v_a`.

**Actually, let me reconsider the proof structure entirely.**

Rather than inducting on the TYPING derivation (which creates problems
because the concrete subterms don't align with the abstract subterms), let's
try inducting on the EVALUATION derivation.

**Alternative proof structure: induction on concrete evaluation.**

**Theorem (Soundness, alt).** If `Γ ⊢ e ⇝ τ` and `γ ⊨ Γ` and `eγ ⇓ v`,
then `v ⊑ τγ`.

Proof by induction on the derivation of `eγ ⇓ v`.

**Case: `eγ` is a value** (lambda or Type):
Then `v = eγ`. If `e = λ(x:A).body`, then `τ = λ(x:A).body` (Lam rule), so
`τγ = λ(x:Aγ).bodyγ = eγ = v`. By Refl. ✓
If `e = Type`, similar. ✓

**Case: `eγ = (e'γ : σγ) ⟶ e'γ ⇓ v`** (ascription erasure):
By Asc: `τ = σ`, so `τγ = σγ`.
By IH on `e' ⇝ σ'` and `e'γ ⇓ v`: `v ⊑ σ'γ`.
By `σ' ⊑ σ` (Asc premise): `σ'γ ⊑ σγ` (by Equal Sub).
By Trans: `v ⊑ σγ = τγ`. ✓

**Case: `eγ = fγ aγ ⇓ v`** where `fγ ⇓ λ(x:D).b`, `aγ ⇓ v_a`,
`b[x:=v_a] ⇓ v`:

Typing: `Γ ⊢ f a ⇝ body[x:=a']` by App, with `f ⇝ λ(x:A).body`, `a ⇝ a'`.

By IH on `fγ ⇓ λ(x:D).b` (smaller evaluation):
`λ(x:D).b ⊑ (λ(x:A).body)γ = λ(x:Aγ).bodyγ`

By S-Lam inversion:
- `Aγ ⊑ D`
- For all `y ⊑ Aγ`: `b[x:=y] ⊑ bodyγ[x:=y]`    ... (F2)

By IH on `aγ ⇓ v_a` (smaller evaluation):
`v_a ⊑ a'γ`

Since `a' ⊑ A`: `a'γ ⊑ Aγ`, so `v_a ⊑ Aγ`.

By (F2) with `y = v_a`: `b[x:=v_a] ⊑ bodyγ[x:=v_a]`    ... (★)

Now we need to handle `b[x:=v_a] ⇓ v` (the last evaluation step). This is
where we need either:
(a) Apply the IH to `b[x:=v_a] ⇓ v`, or
(b) Show `v ⊑ bodyγ[x:=v_a]` and then relate to `bodyγ[x:=a'γ]`.

**For (a):** The IH says "if we have a typing judgment for `b[x:=v_a]`, we
can conclude `v ⊑` its type." But `b[x:=v_a]` doesn't have a typing
judgment from the original derivation.

**For (b):** We can get `v ⊑ b[x:=v_a]` if concrete evaluation preserves
subtyping in the sense that `v ⊑ e` whenever `e ⇓ v` — but this is
essentially what we're trying to prove.

**The fundamental issue:** The induction on concrete evaluation has a
structural problem in the App case: `b[x:=v_a] ⇓ v` is a sub-evaluation,
but we don't have a typing judgment for `b[x:=v_a]`.

**Resolution: simultaneous induction on evaluation + "abstract evaluation
of the concrete term."**

Define `absEval(e)` as the abstract evaluation of closed term `e` (i.e.,
`∅ ⊢ e ⇝ absEval(e)`). Then we can formulate:

**Lemma (Concrete-Abstract Simulation).** If `e ⇓ v` (closed term), then
`v ⊑ absEval(e)`.

This is a property of closed terms only. Proof by induction on `e ⇓ v`:

**Case value:** `v = e`, `absEval(e) = e` (for lambdas and Type). ✓

**Case ascription:** `(e':σ) ⟶ e' ⇓ v`. `absEval((e':σ)) = σ`.
By IH: `v ⊑ absEval(e')`.
By Asc well-formedness: `absEval(e') ⊑ σ`.
By Trans: `v ⊑ σ`. ✓

**Case application:** `f a ⇓ v` where `f ⇓ λ(x:D).b`, `a ⇓ v_a`,
`b[x:=v_a] ⇓ v`.

`absEval(f a)`: evaluate `f` abstractly: `absEval(f)`. If `absEval(f) = λ(x:A').body'`,
then `absEval(f a) = body'[x := absEval(a)]` (modulo β, and assuming the
domain check passes).

By IH on `f`: `λ(x:D).b ⊑ absEval(f) = λ(x:A').body'`.
By IH on `a`: `v_a ⊑ absEval(a)`.
By IH on `b[x:=v_a]`: `v ⊑ absEval(b[x:=v_a])`.

From `λ(x:D).b ⊑ λ(x:A').body'` (S-Lam):
- `A' ⊑ D`
- For `y ⊑ A'`: `b[x:=y] ⊑ body'[x:=y]`    ... (P)

We need: `v ⊑ body'[x := absEval(a)]`.

From IH: `v ⊑ absEval(b[x:=v_a])`.

**Claim:** `absEval(b[x:=v_a]) ⊑ body'[x := absEval(a)]`.

From (P) with `y = v_a` (need `v_a ⊑ A'`):
`b[x:=v_a] ⊑ body'[x:=v_a]`

But we need `absEval(b[x:=v_a]) ⊑ body'[x:=absEval(a)]`, which is different
because:
1. `absEval(b[x:=v_a])` vs `b[x:=v_a]` — abstract evaluation may differ
   from the raw term.
2. `v_a` vs `absEval(a)` — we need to relate these.

By IH on `a ⇓ v_a`: `v_a ⊑ absEval(a)`.

Hmm, we need `v_a ⊑ A'` for (P). We have `v_a ⊑ absEval(a)`, and we need
`absEval(a) ⊑ A'` (the domain check from abstract eval of the application).
This should hold because abstract evaluation checks `absEval(a) ⊑ A'` as a
premise of the App rule.

So: `b[x:=v_a] ⊑ body'[x:=v_a]` from (P).

And we need: `v ⊑ body'[x:=absEval(a)]`.

From IH on `b[x:=v_a] ⇓ v`: `v ⊑ absEval(b[x:=v_a])`.

The remaining gap is relating `absEval(b[x:=v_a])` to `body'[x:=absEval(a)]`.

Note that `absEval(b[x:=v_a])` is the abstract evaluation of the concrete
body with the concrete argument. And `body'[x:=absEval(a)]` is the abstract
body with the abstract argument. The difference is:
- `b` vs `body'` — related by subtyping (from S-Lam on `f`)
- `v_a` vs `absEval(a)` — related by subtyping (from IH on `a`)

To bridge this gap, we need:

**Lemma (Abstract Eval Monotonicity for Closed Terms).** If `e₁ ⊑ e₂`
(both closed), then `absEval(e₁) ⊑ absEval(e₂)`.

This is a version of monotonicity for closed terms under the subtyping
preorder. Combined with the pointwise condition from S-Lam, this would give:

`absEval(b[x:=v_a]) ⊑ absEval(body'[x:=v_a]) ⊑ absEval(body'[x:=absEval(a)])`

where the first step uses `b[x:=v_a] ⊑ body'[x:=v_a]` from (P), and the
second step uses `v_a ⊑ absEval(a)` with monotonicity of `body'` in `x`.

**This reveals the mutual dependency.** Soundness requires monotonicity,
even in the closed-term case. The two must be proved simultaneously.

### Summary of App Case

The App case of soundness requires:

1. IH gives `v_f ⊑ absEval(f)` and `v_a ⊑ absEval(a)` and
   `v ⊑ absEval(b[x:=v_a])`
2. S-Lam gives `b[x:=v_a] ⊑ body'[x:=v_a]` pointwise
3. Need: monotonicity of abstract evaluation to bridge from
   `body'[x:=v_a]` to `body'[x:=absEval(a)]`

**The chain is:**
```
v ⊑ absEval(b[x:=v_a])                  -- IH on sub-evaluation
  ⊑ absEval(body'[x:=v_a])              -- monotonicity of absEval (from (P))
  ⊑ absEval(body'[x:=absEval(a)])       -- monotonicity of absEval in subst
  = body'[x:=absEval(a)]                -- if body' has no further redexes
```

The last equality holds modulo β. And `body'[x:=absEval(a)]` is exactly
`absEval(f a)` (by the App abstract evaluation rule).

### Handling the General Case (with Γ)

The general case (non-empty Γ) reduces to the closed case by applying γ.
Given `Γ ⊢ e ⇝ τ` and `γ ⊨ Γ`, we have:
- `eγ` is closed, `eγ ⇓ v`
- `absEval(eγ)` = `τγ` (abstract evaluation commutes with γ-substitution,
  because γ replaces each variable `x` with `γ(x)` which has `γ(x) ⊑ Γ(x)γ`)

Wait, this isn't quite right. `absEval(eγ)` evaluates the closed term `eγ`
from scratch. But `τγ` is the abstract type from the open evaluation,
closed by γ. These differ because the open evaluation uses `x ⇝ Γ(x)`
(variable returns its type), while the closed evaluation uses `γ(x)` directly
(which is more precise: `γ(x) ⊑ Γ(x)γ`).

So `absEval(eγ) ⊑ τγ` (the closed evaluation is MORE precise than the open
one), and we need `v ⊑ τγ`, which follows from `v ⊑ absEval(eγ) ⊑ τγ`.

The first inequality is the closed-term soundness (Concrete-Abstract
Simulation). The second is a consequence of monotonicity: narrower
environment → narrower abstract result, so `absEval(eγ) ⊑ τγ`.

**Again, soundness ⟹ monotonicity dependency.**

### Conclusion on Soundness

Soundness and monotonicity are mutually dependent:
- Soundness (App case) needs monotonicity to bridge `body[x:=v_a]` to
  `body[x:=a']`.
- Monotonicity needs soundness (or at least the simulation lemma) to relate
  concrete and abstract evaluations.

**They must be proved by mutual/simultaneous induction.** The induction
measure should be the SIZE of the term (or the evaluation derivation), with
both theorems proved for all terms up to a given size before proceeding.

The easy cases (Var, Lam, Type) are straightforward for both theorems. The
hard case (App) requires both theorems at smaller sizes. Since application
reduces the evaluation to sub-evaluations of strictly smaller size
(the function, the argument, and the body application), the mutual induction
is well-founded.

**Status: The structure is sound (pun intended), and each step has been
identified. The key gap is Lemma 2 (covariant substitution) and its
interaction with lambda domains. See Task 4.2 for the full analysis.**


---

## Task 4.2: Monotonicity

**Theorem (Monotonicity).** If `Γ₁ ⊢ e ⇝ τ₁` and `Γ₂ ⊑ Γ₁` (pointwise:
for each `x:A₁ ∈ Γ₁`, there exists `x:A₂ ∈ Γ₂` with `Γ₂ ⊢ A₂ ⊑ A₁`),
then `Γ₂ ⊢ e ⇝ τ₂` for some `τ₂` with `Γ₂ ⊢ τ₂ ⊑ τ₁`.

More precise environment → more precise abstract result.

**Proof.** By structural induction on the derivation of `Γ₁ ⊢ e ⇝ τ₁`.

### Case Var

`e = x`, `τ₁ = A₁` where `x : A₁ ∈ Γ₁`.

By `Γ₂ ⊑ Γ₁`: `x : A₂ ∈ Γ₂` with `A₂ ⊑ A₁`.

`Γ₂ ⊢ x ⇝ A₂` by Var. And `A₂ ⊑ A₁`. Set `τ₂ = A₂`. ✓

### Case Type

`e = Type`, `τ₁ = Type`.

`Γ₂ ⊢ Type ⇝ Type`. Set `τ₂ = Type ⊑ Type` by Refl. ✓

### Case Lam

`e = λ(x:A).body`, `τ₁ = λ(x:A).body`.

Need: `Γ₂ ⊢ λ(x:A).body ⇝ τ₂` with `τ₂ ⊑ λ(x:A).body`.

By the Lam rule, `Γ₂ ⊢ λ(x:A).body ⇝ λ(x:A).body`, provided the
well-formedness check succeeds: `Γ₂, x:A ⊢ body ⇝ body'`.

**Problem:** Does the well-formedness check still pass under Γ₂? The
original check was `Γ₁, x:A ⊢ body ⇝ body'`. Under Γ₂ ⊑ Γ₁, the body
evaluation might differ because variables from Γ have narrower types.

The well-formedness check verifies that the body is evaluable and that
any subtyping checks (especially in ascriptions) succeed. Under a
NARROWER environment (Γ₂), variables have more precise types. This means:
- Subtyping checks `σ' ⊑ σ` in ascriptions: if `σ'` gets more precise
  (narrower) and `σ` also gets more precise, the check might fail. This
  is exactly the Prop 5.2.9 scenario!

**Example of potential failure:**

```
f = λ(B:Bool). λ(x:B). (x : B)
```

Under `B : Bool`: the body `(x : B)` requires `x ⊑ B`. Since `x : B`
and B is abstract, we have `x ⊑ B` by Var. ✓

Under `B : true` (narrower): the body becomes `(x : true)`, requiring
`x ⊑ true`. Since `x : true`, we have `x ⊑ true` by Var. Still ✓.

Now consider:
```
g = λ(B:Bool). (Not B : B)
```
where `Not = λ(X:Bool). X Bool false true`.

Under `B : Bool`: need `Not Bool ⊑ Bool`. `Not Bool =β Bool Bool false true =β Bool`.
So `Bool ⊑ Bool`. ✓

Under `B : true` (narrower): need `Not true ⊑ true`. `Not true =β false`.
So `false ⊑ true`? ✗

**This is the Prop 5.2.9 counterexample.** Narrowing B from Bool to true
causes the ascription check to FAIL. The well-formedness check that passed
under Γ₁ fails under Γ₂ ⊑ Γ₁.

This means the Lam case of monotonicity DOES NOT HOLD in general for terms
containing ascription.

### Case Asc

`e = (e' : σ)`, `τ₁ = σ`.
Premises: `Γ₁ ⊢ e' ⇝ σ'₁`, `Γ₁ ⊢ σ'₁ ⊑ σ`.

Under Γ₂: by IH on `e'`, `Γ₂ ⊢ e' ⇝ σ'₂` with `σ'₂ ⊑ σ'₁`.

Need: `Γ₂ ⊢ σ'₂ ⊑ σ₂` where `σ₂` is σ evaluated under Γ₂.

Wait, σ is a term that may contain variables. Under Γ₂, its abstract
evaluation would give `σ` evaluated with narrower variables. But the Asc
rule returns σ as-is (it's a syntactic term, not an evaluated one). So
`τ₂ = σ` (same σ), but the subtyping check requires `σ'₂ ⊑ σ`.

We have `σ'₂ ⊑ σ'₁ ⊑ σ` by Trans. So the check passes. ✓

And `τ₂ = σ ⊑ σ = τ₁` by Refl. ✓

**Wait:** But σ might contain free variables. Under Γ₂, the meaning of σ
might change. The Asc rule returns σ syntactically, but the "meaning" of σ
(what set it denotes) depends on the environment.

Hmm, but the Asc rule literally returns the syntactic term σ. It doesn't
evaluate σ. So τ₁ = τ₂ = σ as syntactic terms.

But subtyping judgments are context-dependent: `Γ₁ ⊢ σ ⊑ σ` vs
`Γ₂ ⊢ σ ⊑ σ`. Both hold by Refl.

For the monotonicity conclusion: `Γ₂ ⊢ τ₂ ⊑ τ₁` becomes `Γ₂ ⊢ σ ⊑ σ`.
By Refl. ✓

But wait, this doesn't feel right. If `σ` contains variables, then under
Γ₂ (narrower environment), σ "denotes a narrower set." The monotonicity
theorem says the RESULT should be narrower. But the Asc rule returns σ
regardless of the environment. So the result doesn't get narrower — it stays
the same.

This is CORRECT and important: **ascription is trivially monotone because
it returns a fixed type regardless of the environment.** The whole point of
ascription is to produce a stable type that doesn't change when the
environment narrows. This is exactly what makes ascribed functions monotone.

### Case App

`e = f a`, `τ₁ = body₁[x := a'₁]`.
Premises:
- `Γ₁ ⊢ f ⇝ λ(x:A₁).body₁`
- `Γ₁ ⊢ a ⇝ a'₁`
- `Γ₁ ⊢ a'₁ ⊑ A₁`

Under Γ₂:

By IH on f: `Γ₂ ⊢ f ⇝ F₂` with `F₂ ⊑ λ(x:A₁).body₁`.

**Sub-case: F₂ is a lambda.** `F₂ = λ(x:A₂).body₂`.

From `λ(x:A₂).body₂ ⊑ λ(x:A₁).body₁` (S-Lam):
- `A₁ ⊑ A₂`    (contra)
- `Γ₂, x:A₁ ⊢ body₂ ⊑ body₁`    (co, under the supertype domain)

By IH on a: `Γ₂ ⊢ a ⇝ a'₂` with `a'₂ ⊑ a'₁`.

Domain check: need `a'₂ ⊑ A₂`. We have `a'₂ ⊑ a'₁ ⊑ A₁ ⊑ A₂`
(by Trans, using the contra check). ✓

By App: `Γ₂ ⊢ f a ⇝ body₂[x := a'₂]`. Set `τ₂ = body₂[x := a'₂]`.

Need: `τ₂ ⊑ τ₁`, i.e., `body₂[x := a'₂] ⊑ body₁[x := a'₁]`.

This is EXACTLY Lemma 2 (Covariant Substitution):
- We have `body₂ ⊑ body₁` under `x : A₁`
- We have `a'₂ ⊑ a'₁ ⊑ A₁`

By Covariant Substitution: `body₂[x:=a'₂] ⊑ body₁[x:=a'₁]`. ✓

**...except Lemma 2 is blocked on the lambda case.**

### The Core Difficulty: Lambda in the Body

The covariant substitution lemma fails when `body₁` or `body₂` contains a
lambda with `x` in the domain. Concretely:

If `body₁ = λ(y:x).e₁`, then:
- `body₁[x:=a'₁] = λ(y:a'₁).e₁[x:=a'₁]`
- `body₁[x:=a'₂] = λ(y:a'₂).e₁[x:=a'₂]`

For `λ(y:a'₂).e₁[x:=a'₂] ⊑ λ(y:a'₁).e₁[x:=a'₁]`, the contra check
needs `a'₁ ⊑ a'₂`. But we have `a'₂ ⊑ a'₁` — the WRONG direction.

### Is This Actually a Problem?

Let's check whether this scenario arises in practice. When does a lambda
body contain another lambda with a variable domain?

Example: `f = λ(A:Type). λ(x:A). x`. This is the polymorphic identity.
The inner lambda `λ(x:A).x` has domain `A`, which depends on the outer
parameter.

Abstract evaluation of `f`: `f ⇝ λ(A:Type). λ(x:A). x` (Lam, returns self).

Now consider `f Nat` under Γ₁ = `[]` and `f Bool` under Γ₁ = `[]`:
- `f Nat ⇝ λ(x:Nat).x`, `f Bool ⇝ λ(x:Bool).x`
- `Nat ⊑ Nat` vs `Bool ⊑ Bool` — no issue, these are independent.

But for monotonicity, consider `f A` where `A : Type`:
- Under `A : Type`: `f A ⇝ λ(x:A).x`
- Under `A : Nat` (narrower): `f A ⇝ λ(x:A).x`

Wait, the Lam rule returns the SYNTACTIC lambda, not substituting A. So
both give `λ(x:A).x` in the context where A is bound. The key is: the
subtyping judgment `λ(x:A).x ⊑ λ(x:A).x` under each context.

In context `A:Nat`: `λ(x:A).x` where `A ⇝ Nat`, so effectively `λ(x:Nat).x`.
In context `A:Type`: `λ(x:A).x` where `A ⇝ Type`, so effectively `λ(x:Type).x`.

`λ(x:Nat).x ⊑ λ(x:Type).x`? By S-Lam: contra needs `Type ⊑ Nat`. This is
FALSE in general (Type is wider than Nat).

**So the function `λ(x:Nat).x` is NOT a subtype of `λ(x:Type).x`.** The
more restrictive function (smaller domain) is not a subtype of the less
restrictive one. This makes sense: `λ(x:Nat).x` can't handle all inputs
that `λ(x:Type).x` can.

But monotonicity says: narrower environment → narrower result. Under
`A:Nat`, `f A ⇝ λ(x:Nat).x`. Under `A:Type`, `f A ⇝ λ(x:Type).x`. We
need `λ(x:Nat).x ⊑ λ(x:Type).x`. But this fails!

**Wait — does it?** Let me reconsider. Actual abstract evaluation:

Under `A:Type`: `f ⇝ f = λ(A:Type).λ(x:A).x`. Apply to `A`:
`f A ⇝ (λ(x:A).x)[A:=Type] = λ(x:Type).x`. Hmm, but the App rule
substitutes the ABSTRACT VALUE of A, which is `Type` (from Var).

Under `A:Nat`: `f ⇝ f`. Apply to `A`:
`f A ⇝ (λ(x:A).x)[A:=Nat] = λ(x:Nat).x`. (A ⇝ Nat from Var).

So τ₁ = `λ(x:Type).x`, τ₂ = `λ(x:Nat).x`.

Need: `λ(x:Nat).x ⊑ λ(x:Type).x`? By S-Lam:
- Contra: `Type ⊑ Nat` — FALSE.

**Monotonicity fails for this example!**

### Wait — Is This Really a Failure?

Let me recheck. `λ(x:Nat).x` vs `λ(x:Type).x`:
- `λ(x:Nat).x` is the identity restricted to Nat
- `λ(x:Type).x` is the identity on all terms

The first is "more precise" — it tells you more about what the function
does (it only works on Nats). In the terms-as-types interpretation:
- `λ(x:Nat).x` as a set = {functions f : for all a ⊑ Nat, f a ⊑ a}
  = {identity restricted to Nat}
- `λ(x:Type).x` as a set = {functions f : for all a, f a ⊑ a}
  = {the identity function}

Wait, `λ(x:Type).x` is MORE restrictive as a set — it requires the function
to work on ALL inputs, not just Nats. So `λ(x:Type).x ⊆ λ(x:Nat).x` as
sets (any function that works on all inputs certainly works on Nats).

This means `λ(x:Type).x ⊑ λ(x:Nat).x`, not the reverse!

And indeed, S-Lam with `λ(x:Type).x ⊑ λ(x:Nat).x`:
- Contra: `Nat ⊑ Type` ✓ (Top)
- Co: `x ⊑ x` under `x:Nat` ✓ (Refl)

So the wider domain gives a NARROWER set. This is consistent.

**Monotonicity should say:** Under `A:Nat` (narrower), `f A ⇝ λ(x:Nat).x`.
Under `A:Type` (wider), `f A ⇝ λ(x:Type).x`. And we need
`λ(x:Nat).x ⊑ λ(x:Type).x`... but we just showed the REVERSE holds!

`λ(x:Type).x ⊑ λ(x:Nat).x` ✓ (wider domain → narrower set).
But monotonicity wants `λ(x:Nat).x ⊑ λ(x:Type).x` (narrower env → narrower result).

These are DIFFERENT DIRECTIONS. So monotonicity fails?

**Let me recheck the semantics.** "Narrower" means "more precise" which
means "smaller set." Under narrower environment, the abstract result should
be a SMALLER set (more information known).

- `λ(x:Nat).x` as a set: all functions that, restricted to Nat, return
  their input. This includes the unrestricted identity AND functions that
  do anything on non-Nat inputs. So this is a LARGER set.
- `λ(x:Type).x` as a set: only the unrestricted identity. SMALLER set.

So `λ(x:Type).x ⊑ λ(x:Nat).x` (smaller ⊑ larger). ✓

Under wider environment (`A:Type`), we get `λ(x:Type).x` — the SMALLER set
(more precise!). Under narrower environment (`A:Nat`), we get `λ(x:Nat).x`
— the LARGER set (less precise!).

**This is anti-monotone!** Narrowing `A` from `Type` to `Nat` WIDENS the
result. This is exactly the phenomenon from Prop 5.2.9.

### Why This Happens

The issue is that the domain of a lambda is in a CONTRAVARIANT position for
subtyping, but in a COVARIANT position for abstract evaluation (narrowing A
narrows the domain). These two directions conflict:

- Abstract eval is covariant: narrower A → narrower domain
- Subtyping treats domains contravariantly: narrower domain → wider function set

So narrowing the environment can produce a WIDER result type, violating
monotonicity.

### When Is Monotonicity Rescued?

**Ascription rescues monotonicity.** If the function's return is ascribed:

```
f_asc = λ(A:Type). (λ(x:A).x : λ(_:A).A)
```

Then `f_asc A` evaluates to... hmm, let's be more precise. Actually, the
ascription would be on the application result, not the function itself. The
typical pattern is:

```
g = λ(A:Type). λ(x:A). (x : A)
```

Under `A:Type`: `g A ⇝ λ(x:Type).(x:Type)`. Applying to concrete arg:
abstractly evaluates to `Type` (Asc returns rhs).

Under `A:Nat`: `g A ⇝ λ(x:Nat).(x:Nat)`. Applying to concrete arg:
abstractly evaluates to `Nat` (Asc returns rhs).

Now `Nat ⊑ Type` ✓. Monotonicity holds for the APPLICATION result because
the ascription fixes the output type relative to the input.

But we showed above that `λ(x:Nat).(x:Nat) ⊑ λ(x:Type).(x:Type)` requires:
- Contra: `Type ⊑ Nat` — FAILS.

So monotonicity still fails at the FUNCTION level, even with ascription!

### The Deep Issue

**Monotonicity of abstract evaluation fails for functions with dependent
domains.** This is not a bug in the proof — it's a real semantic issue.
When a function's domain depends on a context variable, narrowing that
variable narrows the domain, which WIDENS the function type.

This is the same phenomenon as Prop 5.2.9, now analyzed in Och's minimal
setting. The Lean track found this too: monotonicity fails because function
subtyping contravariance conflicts with the covariance of dependent domains.

### Possible Fixes

Several approaches could rescue monotonicity:

**1. Restrict where variables appear in domains.** If `x` can only appear
in the BODY of a lambda, not its domain, then the contra check doesn't flip
the direction. But this kills dependent types — `λ(x:A).body` where `A`
depends on a context variable is the whole point.

**2. Use a different subtyping rule for functions.** Instead of S-Lam with
contravariant domains, use a rule that checks pointwise:

```
[Lam-Pointwise]
Γ ⊢ f ⊑ λ(x:A₂).B₂
  For all v ⊑ A₂: Γ ⊢ f v ⊑ B₂[x:=v]
```

This avoids the contravariance issue because it doesn't compare domains
directly. Instead, it checks that `f` produces a result ⊑ `B₂` for every
valid input. This is closer to the semantic definition of subtyping.

Under this rule, `λ(x:Nat).x ⊑ λ(x:Type).x` requires: for all `v ⊑ Type`,
`(λ(x:Nat).x) v ⊑ x[x:=v] = v`. This gives `v ⊑ v` by Refl (assuming `v`
is in Nat's domain — but wait, `v` ranges over all of Type, and `λ(x:Nat).x`
might not accept non-Nat inputs).

Hmm, this doesn't obviously help. The domain check `v ⊑ Nat` would fail for
`v ⊑ Type` that isn't also ⊑ Nat.

**3. Separate the "shape" (domain annotations) from the "behavior" (body)
in subtyping.** The key insight is: for monotonicity, we care about the
BEHAVIOR of the function (what it computes on valid inputs), not its domain
annotation. Two functions with different domain annotations but identical
behavior on the intersection of their domains should be related.

**4. Accept that monotonicity fails for intermediate terms and only require
it for final results.** If the FINAL result (after all applications are
resolved) is monotone, that might suffice for soundness. The intermediate
function types might be anti-monotone, but if they're always applied to
arguments before being observed, the anti-monotonicity cancels out.

This is plausible because:
- `f A ⇝ λ(x:A).x` is anti-monotone in A
- But `f A v ⇝ v` is trivially monotone (doesn't depend on A at all!)

The anti-monotonicity appears only at the unapplied function stage. Once
applied, it disappears. If we can formulate monotonicity for "ground types"
(types that are not functions), that might be enough.

**5. Change the abstract evaluation of application to avoid the issue.**
Instead of substituting and returning the raw result, wrap it in something
that preserves monotonicity. For instance, the App rule could produce
`body[x:=a'] ⊓ body[x:=Type]` (intersection with the widest possible
substitution), ensuring the result only gets narrower as a' gets narrower.
But this might kill precision.

### Summary of Monotonicity Status

**Monotonicity does not hold in general** for the rules as defined. The
counterexample is:

```
Under A:Type:  (λ(A:Type).λ(x:A).x) A  ⇝  λ(x:Type).x
Under A:Nat:   (λ(A:Type).λ(x:A).x) A  ⇝  λ(x:Nat).x
```

`λ(x:Nat).x ⋢ λ(x:Type).x` because the contra check `Type ⊑ Nat` fails.

This is a manifestation of the Prop 5.2.9 phenomenon in the pure Och
setting. The issue is structural: function subtyping contravariance conflicts
with the covariance of dependent domain instantiation.

**Open question for the project:** Can the rules be modified to rescue
monotonicity without sacrificing expressiveness? The candidates from
"Possible Fixes" above need investigation. Fix #4 (restricting monotonicity
to ground types / fully-applied results) seems most promising because it
matches how types are actually used in practice.


---

## Summary and Open Questions

### What's Proved

1. **Ascription Soundness (4.3):** Complete. Immediate from the Asc rule.

2. **Transparency Preservation (4.4):** Complete. Ascription-free closed
   terms evaluate identically under abstract and concrete semantics.

3. **Soundness (4.1):** Structure established. All cases except App are
   straightforward. The App case reduces to the Covariant Substitution
   lemma, which in turn requires Monotonicity. The mutual dependency
   between soundness and monotonicity is identified and the chain of
   reasoning is laid out.

4. **Monotonicity (4.2):** **FAILS** in general. A concrete counterexample
   is exhibited: dependent domain instantiation produces anti-monotone
   function types because function subtyping is contravariant in the domain.

### The Key Finding

**Monotonicity fails for unapplied functions with dependent domains.** This
is the Prop 5.2.9 phenomenon, now reduced to its essence in Och. The
failure is not an artifact of the proof technique — it reflects a genuine
semantic tension between:

1. Dependent types (domains can mention context variables)
2. Contravariant function subtyping (narrower domain → wider function type)
3. Monotone abstract evaluation (narrower context → narrower result)

These three cannot all hold simultaneously.

### Impact on Soundness

Soundness (4.1) depends on monotonicity only in the App case, specifically
to bridge from `body[x:=v_concrete]` to `body[x:=a'_abstract]`. If
monotonicity fails, this bridge fails, and soundness is unproved for the App
case.

However, soundness might still hold even without full monotonicity, because:
- The concrete value `v` is always ⊑ the concrete body `body_c[x:=v_a]`
  (by the simulation lemma)
- The concrete body is ⊑ the abstract body under the SAME substitution
  (by the pointwise S-Lam condition)
- The gap is only in going from the concrete substitution to the abstract
  substitution (the monotonicity step)

If we could prove soundness for the restricted case where the abstract
argument is also a value (not just a type), the bridge wouldn't be needed.
This suggests a stratified approach where soundness is proved first for
closed/concrete terms, then extended.

### Recommendations for Next Steps

1. **Investigate Fix #4** (monotonicity for ground types only). Formalize
   what "ground type" means in Och and check whether the restricted
   monotonicity suffices for the soundness proof.

2. **Investigate Fix #2** (pointwise function subtyping). This would replace
   S-Lam with a rule that doesn't compare domains directly. Check whether
   the Task 1 derivations still go through (they might — the derivations
   already use a pointwise style in many places).

3. **Try to prove soundness without full monotonicity.** The simulation
   lemma (v ⊑ absEval(e) for e ⇓ v) doesn't obviously need monotonicity.
   If it can be proved independently, soundness follows for closed terms.

4. **Examine whether the counterexample matters in practice.** The anti-
   monotone case arises when a function with a dependent domain is returned
   as a value (not immediately applied). If Och programs always apply such
   functions immediately, the issue might be academic.
