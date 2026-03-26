# Monotonicity — T-App Case

Proof of the T-App case of the monotonicity theorem for Och₀, as defined
in `docs/och.md`. This document also handles the T-App-Top sub-case where
M₁ refines from ⊤ to a function type.

## Theorem (Monotonicity)

If `Γ ⊢ M ⇒ A` and `Γ' ⊑ Γ` (pointwise), then `Γ' ⊢ M ⇒ A'` for some
A' with `Γ' ⊢ A' ⊑ A`.

**Proof method:** Mutual induction on the typing derivation with soundness
and narrowing-preserves-subtyping. IH: the theorem holds for all strict
sub-derivations.

---

## Case T-App

**Given:** `Γ ⊢ M₁ M₂ ⇒ R` via T-App, with premises:

```
(P1)  Γ ⊢ M₁ ⇒ (x: A) → B
(P2)  Γ ⊢ M₂ ⇒ N'
(P3)  Γ ⊢ N' ⊑ A
(P4)  Γ ⊢ B[x ≔ N'] ⇒ R
```

**Goal:** `Γ' ⊢ M₁ M₂ ⇒ R'` for some R' with `Γ' ⊢ R' ⊑ R`.

### Step 1: Apply IH to sub-derivations

By IH on (P1):

```
Γ' ⊢ M₁ ⇒ T₁  with  Γ' ⊢ T₁ ⊑ (x: A) → B         — (IH₁)
```

By IH on (P2):

```
Γ' ⊢ M₂ ⇒ N''  with  Γ' ⊢ N'' ⊑ N'                  — (IH₂)
```

### Step 2: Case split on T₁

**What forms can T₁ take?** We have `Γ' ⊢ T₁ ⊑ (x: A) → B`. Consider
what subtyping derivations can produce `T₁ ⊑ (x: A) → B`:

- If T₁ = ⊤: Need `⊤ ⊑ (x: A) → B`. The only rules with ⊤ on the left
  are S-Refl (giving ⊤ ⊑ ⊤) and S-Top (⊤ on the right, wrong direction).
  S-Eval on ⊤ gives ⊤ ⇒ ⊤ (by T-Top), so S-Eval yields ⊤ ⊑ ⊤ only.
  S-Trans with ⊤ ⊑ C ⊑ (x: A) → B requires ⊤ ⊑ C, which by the same
  argument forces C = ⊤, leading nowhere. **Impossible.**

- If T₁ = (x: C) → D: The interesting case. Handled below.

- If T₁ = y (a variable): Then `Γ' ⊢ y ⊑ (x: A) → B` could come from
  S-Var: `y: E ∈ Γ'` and `E ⊑ (x: A) → B`. This is possible but does
  not help us apply T-App (which needs M₁ to type to a function, not a
  variable). However, T₁ is the *result* of typing M₁, not M₁ itself.
  Typing results are always one of: ⊤ (from T-Top, T-App-Top), a type
  from Γ' (from T-Var), a function literal (from T-Fun), or a result of
  evaluating a substituted body (from T-App) or ascription target (from
  T-Asc). So T₁ could be a variable (from T-Var) if M₁ is a variable.

  If T₁ = y (a variable), we cannot directly apply T-App because T-App
  requires M₁ ⇒ (x: C) → D (a function type), not a variable. But we
  can observe: if `y ⊑ (x: A) → B`, can we "unfold" y? No — subtyping
  does not guarantee y evaluates to a function. We would need T₁ to be
  syntactically a function type.

  **However**, looking at the typing rules more carefully: T-App's first
  premise requires `Γ' ⊢ M₁ ⇒ (x: A') → B'` — the result must be
  *syntactically* a function type (a pi/lambda form). If T₁ is a variable,
  T-App does not apply. T-App-Top requires T₁ = ⊤, which it is not.
  So M₁ M₂ would be untypeable under Γ'.

  **But can T₁ actually be a variable?** T₁ is the type of M₁ under Γ'.
  Types in the environment Γ' can be variables (e.g., if `f: g ∈ Γ'`
  then `f ⇒ g`). So yes, T₁ can be a variable.

  This means there is a sub-case where T₁ is a variable that is a subtype
  of a function type, but M₁ M₂ is untypeable under Γ'. This is the same
  structural issue as T-App-Top sub-case 2 (see below).

  **We defer this sub-case and note it as a gap.** See "The Typeability
  Gap" section below for analysis.

**For the remainder of this case, assume T₁ = (x: C) → D.**

### Step 3: Extract information from S-Fun

From IH₁: `Γ' ⊢ (x: C) → D ⊑ (x: A) → B`.

**Inversion on function subtyping.** The derivation of
`(x: C) → D ⊑ (x: A) → B` must ultimately go through S-Fun (possibly
via S-Trans and S-Refl). We cannot do clean syntactic inversion because
S-Trans could interpose arbitrary intermediate types. However, we can
establish the following by a structural argument:

*Claim:* If `Γ' ⊢ (x: C) → D ⊑ (x: A) → B`, then `Γ' ⊢ A ⊑ C`
and `Γ', x: A ⊢ D ⊑ B`.

*Justification:* The only rules that produce `F₁ ⊑ F₂` where both sides
are function types are S-Refl (giving A = C, D = B) and S-Fun (giving
`A ⊑ C` and `x: A ⊢ D ⊑ B`). S-Eval with `(x: C) → D ⇒ (x: A) → B`
requires T-Fun, which gives `(x: C) → D ⇒ (x: C) → D`, only matching
if C = A and D = B. S-Trans with intermediate `(x: E) → F` gives
`(x: C) → D ⊑ (x: E) → F ⊑ (x: A) → B`, and by induction on each
piece we get `E ⊑ C` and `x: E ⊢ D ⊑ F`, plus `A ⊑ E` and
`x: A ⊢ F ⊑ B`. By S-Trans: `A ⊑ C` and (with weakening/narrowing
from `x: A` to `x: E` for the first piece) we can chain `D ⊑ F ⊑ B`
under `x: A`. S-Var cannot produce function ⊑ function (variable on
the left). S-Trans with non-function intermediate: ⊤ on the right
contradicts having a function on the right; a variable intermediate
would require variable ⊑ function (possible via S-Var + S-Trans chain
but ultimately grounded in S-Fun).

**For this proof, we assume this inversion principle holds:**

```
Γ' ⊢ A ⊑ C                    — (Inv₁)
Γ', x: A ⊢ D ⊑ B              — (Inv₂)
```

*Note:* The body comparison is under `x: A` (the wider domain, from the
supertype side), matching S-Fun's convention of comparing bodies under
the supertype's domain.

### Step 4: Establish T-App premises under Γ'

**Premise (1):** `Γ' ⊢ M₁ ⇒ (x: C) → D`. From IH₁. ✓

**Premise (2):** `Γ' ⊢ M₂ ⇒ N''`. From IH₂. ✓

**Premise (3):** `Γ' ⊢ N'' ⊑ C`.

```
N'' ⊑ N'     (from IH₂)
N' ⊑ A       (from P3, transported to Γ' by narrowing-preserves-subtyping)
A ⊑ C        (from Inv₁)
————————————
N'' ⊑ C      (by S-Trans, chaining all three)  ✓
```

*Detail on transporting P3:* Premise (P3) states `Γ ⊢ N' ⊑ A`. By
Lemma 3 (narrowing preserves subtyping, proved in `full-proof-attempt.md`)
with `Γ' ⊑ Γ`: `Γ' ⊢ N' ⊑ A`. Note that N' and A are closed terms
(they are the type of M₂ and the domain annotation, both of which are
syntax from the original term, not environment-dependent values). Even
if they contain free variables, narrowing-preserves-subtyping handles
that.

**Premise (4):** `Γ' ⊢ D[x ≔ N''] ⇒ R'` for some R', with `R' ⊑ R`.

**This is the hard part.** See Step 5.

### Step 5: The body evaluation — relating D[x ≔ N''] to B[x ≔ N']

We need to show:
- (a) `D[x ≔ N'']` is typeable under Γ', yielding some R'.
- (b) `Γ' ⊢ R' ⊑ R`.

**What we have:**

```
(P4)    Γ ⊢ B[x ≔ N'] ⇒ R
(IH₂)  Γ' ⊢ N'' ⊑ N'
(Inv₂)  Γ', x: A ⊢ D ⊑ B
```

And: `Γ' ⊢ N'' ⊑ N' ⊑ A` (the full chain from Step 4).

**Strategy: go through environments, then substitute.**

The idea is to avoid directly comparing `D[x ≔ N'']` and `B[x ≔ N']`
(which would require monotone substitution, which fails due to
contravariance). Instead, we work in extended environments and use
monotonicity to vary the environment.

#### Step 5a: Lift premise (P4) into an environment with x

**Substitution-Environment Equivalence (assumed lemma):**

> If `Γ ⊢ B[x ≔ V] ⇒ R`, then `Γ, x: V ⊢ B ⇒ R₀` where
> `R = R₀[x ≔ V]`.

*Intuition:* Typing a term after substitution is equivalent to typing the
pre-substitution term in an environment that binds x to V, up to
substituting the result. This holds because typing is syntax-directed
and substitution commutes with each typing rule.

Applying this to (P4): from `Γ ⊢ B[x ≔ N'] ⇒ R`, we get:

```
Γ, x: N' ⊢ B ⇒ R₀   where R = R₀[x ≔ N']       — (δ)
```

#### Step 5b: Apply monotonicity to the pre-substitution typing

We want to type B under `Γ', x: N''` (which is narrower than
`Γ, x: N'`).

Claim: `(Γ', x: N'') ⊑ (Γ, x: N')` pointwise.
- For variables y ≠ x in Γ: `y: A_y ∈ Γ` has `y: A'_y ∈ Γ'` with
  `Γ' ⊢ A'_y ⊑ A_y` (from `Γ' ⊑ Γ`). Strengthening to
  `(Γ', x: N'') ⊢ A'_y ⊑ A_y` by weakening (adding x: N''). ✓
- For x: `x: N'' ∈ (Γ', x: N'')` and `x: N' ∈ (Γ, x: N')`. Need
  `(Γ', x: N'') ⊢ N'' ⊑ N'`. We have `Γ' ⊢ N'' ⊑ N'` from IH₂.
  By weakening (adding x: N''): `Γ', x: N'' ⊢ N'' ⊑ N'`. ✓

  *Note:* This requires that N'' and N' do not mention x, which holds
  because they are typing results of M₂ under Γ' and Γ respectively,
  and x is the binder from the function type of M₁.

By monotonicity (IH, applied to the sub-derivation δ, which is
strictly smaller than the original T-App derivation — see well-foundedness
note below):

```
Γ', x: N'' ⊢ B ⇒ R₁   with  (Γ', x: N'') ⊢ R₁ ⊑ R₀    — (ε)
```

#### Step 5c: Substitute back

From (ε): `Γ', x: N'' ⊢ B ⇒ R₁`.

By the forward direction of the substitution-environment equivalence:

> If `Γ', x: V ⊢ B ⇒ R₁`, then `Γ' ⊢ B[x ≔ V] ⇒ R₁[x ≔ V]`.

*Note:* This forward direction is more subtle than the reverse. It says
that substituting V for x in the term B and then typing gives the same
result as typing B in the extended environment and then substituting in
the result. This holds when typing is syntax-directed: each rule
commutes with substitution because substitution distributes over the
term constructors and the environment lookup `x: V ∈ (Γ', x: V)` is
replaced by the substituted value V.

Applying this to (ε):

```
Γ' ⊢ B[x ≔ N''] ⇒ R₁[x ≔ N'']                            — (ζ)
```

#### Step 5d: Relate D[x ≔ N''] to B[x ≔ N'']

From (Inv₂): `Γ', x: A ⊢ D ⊑ B`.

We have `Γ' ⊢ N'' ⊑ A` (from Step 4). By equal substitution
(Lemma 2, see `lemma-equal-substitution.md`):

```
Γ' ⊢ D[x ≔ N''] ⊑ B[x ≔ N'']                              — (η)
```

#### Step 5e: Type D[x ≔ N'']

From (ζ): `Γ' ⊢ B[x ≔ N''] ⇒ R₁[x ≔ N'']`.
From (η): `Γ' ⊢ D[x ≔ N''] ⊑ B[x ≔ N'']`.

We need D[x ≔ N''] to be typeable. Since D[x ≔ N''] ⊑ B[x ≔ N'']
(by η), and B[x ≔ N''] is typeable (by ζ), we can type D[x ≔ N''].

Specifically, by S-Eval on (ζ):
`Γ' ⊢ B[x ≔ N''] ⊑ R₁[x ≔ N'']`.

But we need a *typing derivation* for D[x ≔ N''], not just a subtyping
relationship. The subtyping `D[x ≔ N''] ⊑ B[x ≔ N'']` does not
directly give us that D[x ≔ N''] is typeable.

**Alternative approach for D[x ≔ N'']:** Apply the same
substitution-environment strategy to D.

From (Inv₂) we know `Γ', x: A ⊢ D ⊑ B`, but we do not directly have a
typing derivation for D. However, we can construct one:

From IH₁, M₁ types to `(x: C) → D` under Γ'. This came from T-Fun
(since that's the only rule producing a function type as output). So
`(x: C) → D` is a syntactic sub-term of M₁ (or is M₁ itself). The body
D is a raw term — T-Fun does not evaluate it.

To type D under an environment with x, we need to assume D is typeable.
In fact, for T-App to be applicable at all, we need premise (4) to hold,
which requires `D[x ≔ N'']` to be typeable. Rather than proving this
from first principles, we can work directly:

**Revised strategy: apply monotonicity to (P4) directly.**

We have `Γ ⊢ B[x ≔ N'] ⇒ R` from (P4). We established
`Γ' ⊢ B[x ≔ N''] ⇒ R₁[x ≔ N'']` in (ζ). So B[x ≔ N''] is typeable.

Now, D[x ≔ N''] is a term such that `D[x ≔ N''] ⊑ B[x ≔ N'']` (by η).
We cannot conclude D[x ≔ N''] is typeable from this alone.

**This is a genuine difficulty.** Subtyping `D[x ≔ N''] ⊑ B[x ≔ N'']`
tells us D[x ≔ N''] is "at least as precise as" B[x ≔ N''], but
typeability is not upward-closed under ⊑. A more precise term can fail
to type-check (e.g., an ascription with a tighter target).

**However**, we can use a different path. Instead of going through B,
type D directly using the environment strategy:

From T-Fun applied to M₁ (which produced `(x: C) → D`), D is a raw
body term. Under `Γ', x: C`, D is typeable because it is a well-formed
sub-term (assuming well-formedness of the original program — every
sub-term that appears in a typing derivation must be processable by the
typing rules, though it may yield ⊤ at worst). More precisely:

**Lemma (Sub-term Typeability):** Every syntactically well-formed term
is typeable under any environment that binds all its free variables.

*Proof sketch:*
- ⊤: T-Top. ✓
- x (if x ∈ dom(Γ)): T-Var. ✓
- (x: A) → B: T-Fun (always, unconditionally). ✓
- M N: If M types to ⊤, T-App-Top. If M types to a function (x: A) → B,
  then we need N typeable (by IH) and N' ⊑ A and B[x ≔ N'] typeable (by IH
  on the substituted body). **This does NOT always hold** — the domain
  check N' ⊑ A can fail.
- (M : A): Requires M typeable, A typeable, and M' ⊑ A. The subtyping
  check can fail.

**So not every term is typeable.** Applications and ascriptions can fail.
D[x ≔ N''] might contain ascriptions or applications that fail.

**The way out:** We do not need D[x ≔ N''] to be typeable in isolation.
We need it to be typeable *and* to satisfy the T-App premise. Let us
check whether the proof can be restructured to avoid this obligation.

### Step 5 (Revised): Direct approach via environment monotonicity

Abandon the D vs B comparison. Instead, work entirely with B (from the
original function type) and use monotonicity on the environment.

#### Step 5a': Substitution-environment equivalence on (P4)

From `Γ ⊢ B[x ≔ N'] ⇒ R`:

```
Γ, x: N' ⊢ B ⇒ R₀   where R = R₀[x ≔ N']           — (δ)
```

#### Step 5b': Monotonicity into Γ', x: N''

`(Γ', x: N'') ⊑ (Γ, x: N')` (established in Step 5b above).

By IH on (δ):

```
Γ', x: N'' ⊢ B ⇒ R₁   with  R₁ ⊑ R₀                — (ε)
```

(The ⊑ is under `Γ', x: N''`.)

#### Step 5c': Substitute back to get typing of B[x ≔ N'']

```
Γ' ⊢ B[x ≔ N''] ⇒ R₁[x ≔ N'']                       — (ζ)
```

#### Step 5d': Now we need T-App with function (x: C) → D, not (x: A) → B

Here is the problem: T-App under Γ' uses the function type `(x: C) → D`
(from M₁'s type), and its premise (4) requires typing **D[x ≔ N'']**,
not B[x ≔ N'']. We have established typeability of B[x ≔ N''] (in ζ),
but T-App demands the body from the *actual* function type that M₁
evaluates to, which is D, not B.

**This is the crux.** Under Γ, M₁ typed to `(x: A) → B`. Under Γ'
(narrower), M₁ types to `(x: C) → D` with `(x: C) → D ⊑ (x: A) → B`.
T-App under Γ' uses body D. T-App under Γ used body B. They are
different raw terms (in general).

#### Step 5e': Type D[x ≔ N''] via the same environment strategy

We need `Γ' ⊢ D[x ≔ N''] ⇒ R'` for some R'.

**Apply the substitution-environment equivalence in reverse.** We need to
first establish `Γ', x: N'' ⊢ D ⇒ S` for some S.

**How to get a typing derivation for D under `Γ', x: N''`:**

M₁ types to `(x: C) → D` under Γ'. This means D is the raw body of a
function literal. T-Fun returns the function as-is without typing the
body. So we do not have a typing derivation for D from the T-App
premises. The body D is only typed after substitution (in T-App's
premise 4).

However, we know D is a well-formed term whose free variables are among
those in Γ' plus x. We need to type it under `Γ', x: N''`. Since
`N'' ⊑ C` (from Step 4), the environment `Γ', x: N''` is at least as
informative about x as `Γ', x: C` would be.

**But we have no typing derivation for D under any environment to serve
as the base case for a monotonicity argument.** We cannot invoke the IH
because there is no sub-derivation of the original T-App that types D.

#### Step 5f': The key insight — use T-App on (x: C) → D directly

We can *construct* a typing derivation for `((x: C) → D) N''` under Γ'
as follows. Recall:

- `Γ' ⊢ (x: C) → D ⇒ (x: C) → D` (by T-Fun)
- `Γ' ⊢ N'' ⇒ ?` — but wait, N'' is a typing result, not a raw term
  in the program. It is the type of M₂ under Γ'.

Actually, T-App applies to the application `M₁ M₂`, not to
`((x: C) → D) N''`. The body D comes from M₁'s type, and the argument
type N'' comes from typing M₂. T-App's premise (4) requires
`Γ' ⊢ D[x ≔ N''] ⇒ R'`. This is a typing judgment on the syntactic
term `D[x ≔ N'']`, which is well-defined. The question is whether it
has a derivation.

**The term D[x ≔ N''] is typeable if we can construct a derivation.**
Since D appears inside M₁ (as part of the function body), and M₁ is
part of the original well-typed program, D is built from the same syntax.
After substituting N'' for x, the result is a well-formed term. But
well-formedness does not guarantee typeability in Och₀ (ascriptions and
applications can fail).

**This is where the proof gets stuck in a new way**, distinct from the
monotone substitution issue. We need D[x ≔ N''] to be typeable under Γ',
but the only typing derivation we have for anything involving D is
indirect (through B via the S-Fun inversion).

---

## Summary of What Works and What's Stuck

### What works (premises 1–3 of T-App under Γ'):

| Premise | Status | How |
|---------|--------|-----|
| `Γ' ⊢ M₁ ⇒ (x: C) → D` | ✓ | IH on (P1) |
| `Γ' ⊢ M₂ ⇒ N''` | ✓ | IH on (P2) |
| `Γ' ⊢ N'' ⊑ C` | ✓ | Chain: N'' ⊑ N' (IH₂) ⊑ A (P3 + narrowing) ⊑ C (Inv₁) |

### What's stuck (premise 4):

We need `Γ' ⊢ D[x ≔ N''] ⇒ R'` with `Γ' ⊢ R' ⊑ R`.

**Two independent difficulties:**

**Difficulty 1: Typeability of D[x ≔ N''].**
We have no typing derivation for D under any environment. D is a raw
body from a function literal; T-Fun does not type it. We can type
B[x ≔ N''] (via the environment monotonicity strategy, yielding ζ),
but T-App needs D, not B.

If M₁ was already a function literal under both Γ and Γ' (the common
case), then the function type is identical: `(x: A) → B = (x: C) → D`
(since T-Fun returns the literal unchanged), so C = A and D = B. In
this case, D[x ≔ N''] = B[x ≔ N''], and (ζ) gives the typing
derivation directly. The difficulty only arises when M₁ is not a literal
and its type genuinely changes between Γ and Γ'.

**Difficulty 2: The result R' must satisfy R' ⊑ R (monotone substitution gap).**
Even when D = B (the easy case), we have:
```
Γ' ⊢ B[x ≔ N''] ⇒ R₁[x ≔ N'']     (from ζ)
```
And R = R₀[x ≔ N'] (from δ). So we need:
```
Γ' ⊢ R₁[x ≔ N''] ⊑ R₀[x ≔ N']
```

From (ε): `(Γ', x: N'') ⊢ R₁ ⊑ R₀`. By equal substitution with
`N'' ⊑ N''`:
```
Γ' ⊢ R₁[x ≔ N''] ⊑ R₀[x ≔ N'']
```

So it suffices to show:
```
Γ' ⊢ R₀[x ≔ N''] ⊑ R₀[x ≔ N']                         — (★)
```

This is **monotone substitution**: substituting a more precise value (N'')
for x in R₀ should yield a more precise result than substituting a less
precise value (N'). This fails in general due to contravariant positions
(x might appear in parameter annotations inside R₀).

**When (★) holds:** If x does not appear in R₀ (the common case for
non-dependent functions), then R₀[x ≔ N''] = R₀[x ≔ N'] = R₀ and (★)
holds by S-Refl. More generally, if x only appears in covariant
positions in R₀, monotone substitution holds.

**When (★) fails:** If R₀ contains x in a contravariant position (e.g.,
R₀ = (y: x) → y), then R₀[x ≔ N''] = (y: N'') → y and
R₀[x ≔ N'] = (y: N') → y. Subtyping requires N' ⊑ N'' in the domain
(contravariance), but we only have N'' ⊑ N' (the wrong direction).

---

## The Typeability Gap (T-App-Top Sub-case 2 and T-App Variable Case)

### Statement of the gap

When the original derivation types `M₁ M₂` via T-App-Top (M₁ ⇒ ⊤) or
via T-App where M₁ ⇒ (x: A) → B, but under Γ', M₁ types to a
*different* function type or (in the T-App-Top case) types to a function
type for the first time, then M₂ may not satisfy the domain check.

**Specifically, for T-App-Top sub-case 2:**

Under Γ: `Γ ⊢ M₁ ⇒ ⊤`, so `Γ ⊢ M₁ M₂ ⇒ ⊤` by T-App-Top. M₂ is
never typed.

Under Γ' ⊑ Γ: `Γ' ⊢ M₁ ⇒ (x: C) → D`. Now T-App-Top does not apply
(M₁ does not type to ⊤). T-App requires M₂ to be typeable with result
⊑ C, but M₂ was never checked and might contain failing ascriptions or
applications.

**Is M₂ always typeable?** No. Counterexample:

```
Let Γ = {f: ⊤, x: ⊤}
Let M₁ = f, M₂ = (x : ⊥)    — where ⊥ is some untypeable ascription

Under Γ:
  f ⇒ ⊤, so f M₂ ⇒ ⊤ by T-App-Top. M₂ is never typed. ✓

Under Γ' = {f: (x: ⊤) → ⊤, x: ⊤}:
  f ⇒ (x: ⊤) → ⊤. T-App requires M₂ typeable. But M₂ might not be.
```

In Och₀ specifically, `(x : ⊥)` is not syntax (no ⊥). But consider:

```
M₂ = (⊤ : (x: ⊤) → x)
```

T-Asc needs: `⊤ ⇒ ⊤`, check `⊤ ⊑ (x: ⊤) → x`. But `⊤ ⊑ (x: ⊤) → x`
fails (⊤ is not a subtype of a function type). So M₂ is untypeable.

Under `Γ = {f: ⊤}`: `f M₂ ⇒ ⊤` by T-App-Top. ✓
Under `Γ' = {f: (y: ⊤) → ⊤}`: `f M₂` requires M₂ typeable. It is not.

**This is a concrete failure of monotonicity as stated.** The term
`f ((⊤ : (x: ⊤) → x))` types to ⊤ under `{f: ⊤}` but is untypeable
under `{f: (y: ⊤) → ⊤}`.

### Possible resolutions for the typeability gap

1. **Weaken monotonicity to only require *typeability preservation*,
   not strict ⊑.** That is: if typeable under Γ and Γ' ⊑ Γ, then
   typeable under Γ' (but the result may be ⊤). This fails for the
   same reason: the term may not be typeable at all under Γ'.

2. **Add a rule T-App-Top-Fallback:** If `Γ ⊢ M ⇒ T` and `T ⊑ ⊤`
   (i.e., always), then `Γ ⊢ M N ⇒ ⊤`. This makes every application
   typeable (with result ⊤ in the worst case). Monotonicity would then
   always have the fallback of producing ⊤ ⊑ ⊤.

   *Risk:* This is a very permissive rule. It means `f x` always
   type-checks even when f is a function and x is incompatible with the
   domain. The type is ⊤ (no information), which is safe from a
   soundness perspective (need to verify), but it means more programs
   type-check than intended.

3. **Restrict monotonicity to well-typed sub-terms.** Require that all
   sub-terms of M are typeable under Γ (not just M itself). This rules
   out the counterexample because M₂ is untypeable under Γ too (it just
   was not checked). This is a natural "well-formedness" requirement on
   programs.

4. **Extend T-App-Top to not require M ⇒ ⊤ exactly.** For example:
   `Γ ⊢ M ⇒ A, Γ ⊢ A ⊑ ⊤ ⟹ Γ ⊢ M N ⇒ ⊤`. Since `A ⊑ ⊤` always
   holds (S-Top), this would make T-App-Top always applicable,
   equivalent to option 2.

**Recommended resolution: option 3.** Require that monotonicity applies
only to programs where all sub-terms are well-typed. This is the standard
approach in type theory — we prove properties of *well-typed* programs,
and well-typedness typically implies all sub-terms are also checkable.
Alternatively, option 2 (always-applicable T-App-Top) is clean and may
be worth considering for its simplicity.

---

## The Monotone Substitution Gap

The core difficulty in premise (4) is the obligation (★):

```
Γ' ⊢ R₀[x ≔ N''] ⊑ R₀[x ≔ N']
```

where N'' ⊑ N'. This is "monotone substitution": substituting a more
precise value should give a more precise result. It fails when x appears
in contravariant positions in R₀.

### Why it fails (concrete example)

Let R₀ = (y: x) → y. Then:
- R₀[x ≔ N''] = (y: N'') → y
- R₀[x ≔ N'] = (y: N') → y

By S-Fun: need N' ⊑ N'' (contra in domain) and y: N' ⊢ y ⊑ y (trivial).
But we only have N'' ⊑ N', not N' ⊑ N''.

### When does x appear contravariantly in R₀?

R₀ is the result of typing the raw body B under `Γ, x: N'`. For x to
appear in R₀, B must contain sub-terms that "pass through" x into the
result type. This happens with dependent function types:

```
B = (y: x) → y     — x appears in a parameter annotation
```

After typing: R₀ = (y: x) → y (T-Fun returns the literal).

### Possible resolutions for the monotone substitution gap

1. **Prove monotone substitution for a restricted class of terms.**
   If R₀ only has x in covariant positions, the result holds. This
   requires defining a polarity analysis and showing that typing
   outputs have the right polarity structure. This is significant
   metatheoretic work.

2. **Modify E-App/T-App to evaluate the body before reporting it.**
   If T-App evaluates B in the extended environment rather than
   substituting and then evaluating, i.e., if the rule were:
   ```
   Γ, x: N' ⊢ B ⇒ R₀
   Γ ⊢ R₀[x ≔ N'] ⇒ R
   ```
   then monotonicity on the first premise gives `R₁ ⊑ R₀`, and on
   the second premise (with the monotone substitution on R₀ still
   required for the final result) we still face the same issue. So
   this restructuring alone does not help.

3. **Accept the gap for dependent types.** The monotone substitution
   issue only arises when B uses x in parameter annotations (dependent
   types). For non-dependent function bodies (where x does not appear
   in any parameter annotation in B), R₀ does not contain x in
   contravariant positions, and (★) holds trivially (R₀ does not
   mention x at all, or mentions it only covariantly).

4. **Evaluation removes contravariant occurrences.** Observe that
   E-Fun erases parameter annotations to ⊤. So at runtime, the
   contravariant positions are erased. The question is whether
   *abstract* evaluation (typing) similarly neutralizes them. Since
   T-Fun does NOT evaluate the body, contravariant occurrences survive
   in types. This is the root tension.

### Connection to the soundness gap

This is the same obstacle identified in `full-proof-attempt.md` for
T-App soundness. Both soundness and monotonicity of T-App require
bridging a substitution gap where different values (V vs N', or N'' vs
N') are substituted into a body that may use the variable
contravariantly. The root cause is that T-Fun preserves parameter
annotations verbatim while E-Fun erases them, creating a mismatch
between the abstract and concrete treatment of contravariant positions.

---

## Well-Foundedness of the IH Application

In Step 5b, we apply the monotonicity IH to the derivation (δ):
`Γ, x: N' ⊢ B ⇒ R₀`. We need this to be strictly smaller than the
original T-App derivation `Γ ⊢ M₁ M₂ ⇒ R`.

The derivation (δ) comes from the substitution-environment equivalence
applied to (P4): `Γ ⊢ B[x ≔ N'] ⇒ R`. The derivation of (P4) is a
strict sub-derivation of the T-App derivation. The
substitution-environment equivalence produces a derivation for
`Γ, x: N' ⊢ B ⇒ R₀` that mirrors the structure of the (P4) derivation
(each typing rule maps to the same rule, with variable lookups adjusted).
This mirroring derivation has the same depth as (P4)'s derivation, which
is strictly smaller than the T-App derivation.

Therefore the IH application is well-founded. ✓

---

## Summary

| Component | Status | Blocker |
|-----------|--------|---------|
| T-App premise (1) under Γ' | ✓ Complete | — |
| T-App premise (2) under Γ' | ✓ Complete | — |
| T-App premise (3) under Γ' | ✓ Complete | — |
| T-App premise (4): typeability of D[x ≔ N''] | Partial | When D = B (M₁ is a literal or types identically), resolved via environment monotonicity. When D ≠ B, no typing derivation for D is available. |
| T-App premise (4): R' ⊑ R | **STUCK** | Monotone substitution (★) fails due to contravariant positions. Only resolved when x does not appear contravariantly in R₀. |
| T-App-Top sub-case 2 (⊤ refines to function) | **STUCK** | M₂ may be untypeable. Concrete counterexample exists. Resolvable by requiring all sub-terms well-typed, or by making T-App-Top always applicable. |

### The D = B simplification

In the common case where M₁ is a function literal `(x: A) → B`, T-Fun
gives the same type under both Γ and Γ' (T-Fun is environment-
independent), so C = A and D = B. The proof then only faces difficulty 2
(the monotone substitution gap).

Even when M₁ is not a literal (e.g., M₁ is a variable whose type
changes), the function type it receives is typically stored in the
environment, and the bodies are raw syntax. The D ≠ B case arises when
the environment stores different function types for the same variable.

### Path forward

The monotone substitution gap is shared with soundness of T-App
(see `full-proof-attempt.md`). Resolving it requires one of:
1. A polarity-aware substitution lemma.
2. Modifying the typing rules to evaluate away contravariant occurrences.
3. Restricting the theorem to non-dependent function bodies.

The typeability gap (T-App-Top sub-case 2) is independent and resolvable
by strengthening the well-typedness hypothesis or relaxing T-App-Top.
