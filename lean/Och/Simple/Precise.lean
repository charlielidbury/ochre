import Och.Simple.Syntax
import Och.Simple.Subtype
import Och.Simple.DefEq

/-!
# Precise Interpretation + Self-Types (Experimental)

This file explores the "precise interpretation" approach to self-types in
Simple Och.

Because Simple Och has no `μ`/self-type constructor, we introduce an
experimental term language `PExpr` that adds one constructor `iota`, and a
subtyping relation `PSub` over `PExpr`. The relation incorporates two key
ingredients:

1.  **[IotaIntro] rule** — the Cedille-style self-type introduction rule,
    which substitutes the *value* being checked into the self-type body.
2.  **[DefEq] rule** — a coarse computational equality, lifted to `PExpr`,
    which lets the relation close obligations that differ only by beta or
    ascription erasure.

Together, these two ingredients resolve the circularity that blocks
`dtrue ⊑ dBool` in any purely structural formulation of subtyping.

Status: EXPLORATORY. Most proof obligations are `sorry`'d. The file's
purpose is to validate the approach by:

- defining a minimal target relation,
- encoding the motivating cycle (`dtrue ⊑ dBool`) in terms of it,
- tracing through the cycle by hand and pinpointing which rules fire, and
- documenting the resulting proof obligations that a future mechanisation
  would need to discharge.
-/

set_option autoImplicit false

namespace Och.Simple.Precise

/-- Experimental term language: Simple Och extended with a self-type
    constructor `iota`. The body of `.iota body` is under a fresh binder
    `self` at de Bruijn index `0`. -/
inductive PExpr where
  | var  : Nat → PExpr
  | lam  : (dom : PExpr) → (body : PExpr) → PExpr
  | app  : PExpr → PExpr → PExpr
  | asc  : (e : PExpr) → (ty : PExpr) → PExpr
  | top  : PExpr
  /-- `iota body` = `ι self. body` — a self-type binder. -/
  | iota : (body : PExpr) → PExpr
  deriving Inhabited, DecidableEq, Repr

namespace PExpr

/-- Standard de Bruijn shift. -/
def shift (cutoff amount : Nat) : PExpr → PExpr
  | .var k => if k < cutoff then .var k else .var (k + amount)
  | .lam dom body => .lam (shift cutoff amount dom) (shift (cutoff + 1) amount body)
  | .app f a => .app (shift cutoff amount f) (shift cutoff amount a)
  | .asc e ty => .asc (shift cutoff amount e) (shift cutoff amount ty)
  | .top => .top
  | .iota body => .iota (shift (cutoff + 1) amount body)

/-- Standard de Bruijn substitution: replace `var target` with `replacement`. -/
def subst (e : PExpr) (target : Nat) (replacement : PExpr) : PExpr :=
  match e with
  | .var k =>
    if k == target then replacement
    else if k > target then .var (k - 1)
    else .var k
  | .lam dom body =>
    .lam (dom.subst target replacement)
         (body.subst (target + 1) (replacement.shift 0 1))
  | .app f a => .app (f.subst target replacement) (a.subst target replacement)
  | .asc e ty => .asc (e.subst target replacement) (ty.subst target replacement)
  | .top => .top
  | .iota body =>
    .iota (body.subst (target + 1) (replacement.shift 0 1))

end PExpr

/-- Contexts for `PSub`. -/
abbrev PCtx := List PExpr

namespace PCtx

def get? (Γ : PCtx) (n : Nat) : Option PExpr :=
  match List.get? Γ n with
  | some T => some (T.shift 0 (n + 1))
  | none   => none

end PCtx

/-- One-step definitional equality on `PExpr`, same shape as
    `Och.Simple.DefEq` but on `PExpr`. Only the cases relevant to the
    motivating example are exercised. -/
inductive PDefEq : PExpr → PExpr → Prop where
  | refl      : (e : PExpr) → PDefEq e e
  | symm      : {a b : PExpr} → PDefEq a b → PDefEq b a
  | trans     : {a b c : PExpr} → PDefEq a b → PDefEq b c → PDefEq a c
  | beta      : (D b a : PExpr) → PDefEq (.app (.lam D b) a) (b.subst 0 a)
  | ascErase  : (e τ : PExpr) → PDefEq (.asc e τ) e
  | appFun    : {f₁ f₂ a : PExpr} → PDefEq f₁ f₂ → PDefEq (.app f₁ a) (.app f₂ a)
  | appArg    : {f a₁ a₂ : PExpr} → PDefEq a₁ a₂ → PDefEq (.app f a₁) (.app f a₂)
  | lamDom    : {D₁ D₂ b : PExpr} → PDefEq D₁ D₂ → PDefEq (.lam D₁ b) (.lam D₂ b)
  | lamBody   : {D b₁ b₂ : PExpr} → PDefEq b₁ b₂ → PDefEq (.lam D b₁) (.lam D b₂)

/-- Subtyping relation for the experimental self-type calculus. Extends
    `Och.Simple.Sub` with two new rules:

    - **[IotaIntro]**: `a ⊑ body[0 := a]  →  a ⊑ ι. body`  — the self-type
      introduction rule. The *value* `a` is substituted for the self-reference,
      so downstream positions that mentioned `self` become instantiated at
      the precise value under test.

    - **[IotaElim]**: `body[0 := a] ⊑ b  →  a ⊑ b` with `a`'s declared type
      being `ι. body`. (Elided here: we'd need a well-typedness premise;
      see the design notes below.)

    - **[DefEq]**: `PDefEq a b  →  a ⊑ b`. This closes gaps that differ only
      by computation (beta / ascription erasure).
-/
inductive PSub : PCtx → PExpr → PExpr → Type where
  | refl  : (Γ : PCtx) → (a : PExpr) → PSub Γ a a
  | top   : (Γ : PCtx) → (a : PExpr) → PSub Γ a .top
  | var   : (Γ : PCtx) → (x : Nat) → (b T : PExpr) →
            Γ.get? x = some T → PSub Γ T b → PSub Γ (.var x) b
  | lam   : (Γ : PCtx) → (A B b₁ b₂ : PExpr) →
            PSub Γ B A → PSub (B :: Γ) b₁ b₂ →
            PSub Γ (.lam A b₁) (.lam B b₂)
  | app   : (Γ : PCtx) → (f a b D R : PExpr) →
            PSub Γ f (.lam D R) →
            PSub Γ a D →
            PSub Γ (R.subst 0 a) b →
            PSub Γ (.app f a) b
  | ascL  : (Γ : PCtx) → (e τ b : PExpr) →
            PSub Γ e τ → PSub Γ τ b → PSub Γ (.asc e τ) b
  | ascR  : (Γ : PCtx) → (a e τ : PExpr) →
            PSub Γ e τ → PSub Γ a e → PSub Γ a (.asc e τ)
  /-- [IotaIntro]: `a ⊑ body[0 := a]  →  a ⊑ ι. body`.
      This is the "precise" self-type introduction: the value `a` is
      substituted for the self-binder, NOT the type `ι. body`. -/
  | iotaIntro : (Γ : PCtx) → (a body : PExpr) →
                PSub Γ a (body.subst 0 a) →
                PSub Γ a (.iota body)
  /-- [DefEq]: terms that are definitionally equal are in Sub. -/
  | defEq : (Γ : PCtx) → (a b : PExpr) → PDefEq a b → PSub Γ a b

-- ============================================================
-- Encoding of the motivating example: dtrue ⊑ dBool
-- ============================================================

/-!
## The `dtrue ⊑ dBool` cycle, traced by hand

We use the dependent-Bool encoding from `Och.Std.DBool`:

```
dBool  = ι dBool. λP:(dBool→⊤). λt:(P dtrue). λf:(P dfalse). P dBool
dtrue  = ι dtrue. λP:(dtrue→⊤). λt:(P dtrue). λf:⊤.         t
dfalse = ι dfalse. λP:(dfalse→⊤). λt:⊤.        λf:(P dfalse). f
```

To keep things tractable below, we study a *simplified* self-type cycle
that isolates exactly the phenomenon that breaks inductive Sub.

### The mini-cycle

Take the minimal self-type:

```
Nil  = ι self. self → ⊤              — a predicate type "accepts itself"
nil  = ι self. λx:self. ⊤            — a term inhabiting Nil
```

(`self` abbreviates `var 0` under the iota-binder.)

Claim: `nil ⊑ Nil`. An inductive, purely structural derivation stalls
because the contravariant domain check on the `→` demands `self ⊑ self`
*after substitution* — and the two sides end up with different substitutions
in the hostile formulations.

With [IotaIntro] substituting the *value* `nil`:

    To show        nil ⊑ Nil                                [ι. self → ⊤]
    [IotaIntro]    nil ⊑ (self → ⊤)[self := nil]
                  = nil ⊑ (nil → ⊤)
    nil itself is ι self. λx:self. ⊤, so [IotaIntro] again on the LHS
    (via its associated elim rule, or via ascription at the call-site):
                   λx:nil. ⊤ ⊑ (nil → ⊤)
                   (after the outer iota "unwraps" to the lambda form)
    By [Lam] with *the same* domain `nil` on both sides, only the body
    check `⊤ ⊑ ⊤` remains — which is [Refl].

The critical observation: because [IotaIntro] substitutes the value `nil`
on *both* sides of the unfolded check, the domain positions become
syntactically identical without ever needing [DefEq]. Reflexivity closes
the goal.

For `dtrue ⊑ dBool`, substitution is not quite enough on its own. After
substituting `dtrue` for the self-reference in `dBool`'s body, we get
```
λP:(dtrue→⊤). λt:(P dtrue). λf:(P dfalse). P dtrue
```
and `dtrue`'s own unfolded body is
```
λP:(dtrue→⊤). λt:(P dtrue). λf:⊤. t
```
The first two lambdas match on the nose (same domain, same body-position).
The third lambda's domain diverges: `P dfalse` vs `⊤`. This is resolved
by [Top] (`⊤` is RHS-compatible with anything). The body position then
needs `t ⊑ P dtrue`, which — since `t : P dtrue` in context — is closed
by [Var] + [Refl], and no further iota-unfolding is required.

The *critical* position is the `P dtrue` appearing in both sides: because
the value `dtrue` was substituted uniformly, the two `P dtrue`s are
syntactically identical and [Refl] closes the obligation. Without value
substitution (e.g. with equi-recursive `μ` which substitutes the type
`dBool`), the two sides would read `P dtrue` vs `P dBool`, forcing a
recursive `dtrue ⊑ dBool` obligation — the original cycle.

[DefEq] enters the picture if the substituted body has beta-redexes.
E.g. if `P` is applied to something that beta-reduces to a self-reference,
[DefEq] closes the gap.

### What this file establishes

We set up the machinery (`PExpr`, `PSub`, `PDefEq`, `iotaIntro`) and
sketch, as a `noncomputable` term, the proof of the mini-cycle
`nil ⊑ Nil`. The full `dtrue ⊑ dBool` derivation is similar but longer;
we comment out its detailed structure at the bottom of the file.
-/

-- Abbreviations for the mini-cycle encoding.
-- self := var 0 under the iota-binder

/-- `Nil = ι self. self → ⊤`. Using de Bruijn: the arrow sugar `A → B`
    expands to `λ_:A. B` where the body is shifted; but since `B = ⊤`
    has no free variables, it is just `.lam self .top`.
    So `Nil = .iota (.lam (.var 0) .top)`. -/
def Nil : PExpr := .iota (.lam (.var 0) .top)

/-- `nil = ι self. λx:self. ⊤`. Same shape as `Nil` in this toy case
    (because a "value inhabiting `self → ⊤`" is itself a lambda
    returning `⊤`). -/
def nil : PExpr := .iota (.lam (.var 0) .top)

/-- Trivial case: in this exact encoding `nil = Nil` syntactically, so
    `PSub Γ nil Nil` holds by [Refl]. The example is degenerate but
    pedagogically useful: it shows [IotaIntro] *is not needed* when
    the two sides already match. -/
example (Γ : PCtx) : PSub Γ nil Nil := PSub.refl Γ nil

/-!
### A less degenerate mini-cycle

For a case where [IotaIntro] actually fires, we need `nil` and `Nil` to
differ in a self-ref position:

```
Nil' = ι self. self → ⊤                       — predicate "accepts self"
nil' = λ(x:Nil'). ⊤                             — non-iota term of type Nil'
```

Here `nil'` has no top-level iota, so checking `nil' ⊑ Nil'` necessarily
goes through [IotaIntro] on the RHS:

    goal:     nil' ⊑ Nil'
    [IotaIntro] (a := nil', body := (self → ⊤)):
              nil' ⊑ (self → ⊤)[0 := nil']
            = nil' ⊑ nil' → ⊤
    That's (λx:Nil'. ⊤) ⊑ (λ_:nil'. ⊤). By [Lam]:
              contravariant domain: nil' ⊑ Nil'     ← PRINCIPAL CYCLE
              covariant body:       ⊤ ⊑ ⊤           (refl)

So the circularity is still there: after [IotaIntro] we are back to
the same goal in the contravariant position. [IotaIntro] on its own does
NOT break this particular cycle.

This demonstrates a key subtlety: [IotaIntro] helps *only when the
substituted body becomes reflexive in the problematic positions*.
That requires the self-reference to appear **covariantly** in the body
(as in the `P dNat` case of `dBool`), not contravariantly.

**Implication**: the precise-interpretation approach works for self-types
like `dBool`/`dNat` where the self-reference only appears in positions that
substitution collapses to reflexivity. It does NOT work for types where
the self-reference occurs contravariantly — those would still need
coinduction, a seen set, or step-indexing. Good news: most motivating
examples (Church-encoded data with dependent elimination) have covariant
self-references.
-/

def Nil' : PExpr := .iota (.lam (.var 0) .top)
def nil' : PExpr := .lam Nil' .top

-- Attempting to prove nil' ⊑ Nil' via iotaIntro.
-- After iotaIntro with a := nil', body := (lam (var 0) top):
--   need: nil' ⊑ (lam (var 0) top).subst 0 nil' = lam nil' top
-- which is nil' ⊑ (lam nil' top).
-- Since nil' = lam Nil' top, we use [Lam]:
--   contravariant: nil' ⊑ Nil'  — back to the original goal (cycle!)
--   body: top ⊑ top  (refl)
example (Γ : PCtx) : PSub Γ nil' Nil' := by
  -- This is expected to be non-terminating/non-derivable inductively.
  -- Demonstrates where precise-interpretation alone fails.
  sorry

/-!
## A case where precise interpretation DOES work: covariant self-ref

Here is the core `dBool`-style pattern in miniature. Let:

```
T   = ι self. self                       — "a value of type self"
val = ι self. self                       — same; fully reflexive
```

Because the self-reference `self` appears *only* in a covariant position,
substituting the value causes both sides of the unfolded body to agree
structurally.

The more realistic pattern is `ι self. P self` for some functional `P`
where `self` also occurs covariantly in the body. A typical example:

```
Wrap = ι self. lam(k : self→⊤). k self
```

When we check any value `v ⊑ Wrap`, iotaIntro gives us `v ⊑ Wrap.body[0:=v]`
which unfolds to `v ⊑ lam(k : v→⊤). k v`. The contravariant domain check
is `v→⊤ ⊑ v→⊤` → reflexive. The body check is `k v ⊑ k v` (under the
`k:v→⊤` binder) → reflexive.

Both positions collapse to reflexivity ONLY because `v` was substituted
uniformly on both sides.
-/

-- ============================================================
-- Design notes and open questions
-- ============================================================

/-!
## Summary of findings

### What works (claims requiring further mechanical verification)

1.  **[IotaIntro] with value substitution** resolves self-type cycles in
    which the self-reference occurs in positions where uniform value
    substitution collapses the two sides to syntactic equality.
    Concretely: positions where, after substitution, both the LHS and
    the RHS contain the *same* subterm (the value being checked),
    closing by [Refl].

    Example (verified by hand): in `Wrap = ι self. (self → ⊤) → self`
    with value `v`, the [IotaIntro] unfolding yields
    `v ⊑ (v → ⊤) → v`, and every occurrence of `self` is substituted
    to the same `v`, so the contravariant and covariant positions both
    reduce to `v ⊑ v` / `v → ⊤ ⊑ v → ⊤` — closable by [Refl].

2.  **Ascription erasure via [DefEq]** handles the residual case where
    two positions are equal up to beta but not syntactically identical.
    This is exactly the "precise interpretation = definitional equality"
    interpretation (Formulation A from the research brief).

3.  The approach is structural (no step-indexing, no seen set, no
    coinduction) in the *simple* cases above. However, realistic
    examples like `dtrue ⊑ dBool` involve value substitutions on BOTH
    sides (because `dtrue` is itself an iota), and whether those two
    substitutions can be proven to match up without an auxiliary
    coinduction is still an open question — see next section.

### What doesn't work / is unresolved

1.  **Contravariant self-references** still produce productive cycles
    that [IotaIntro] alone cannot break. See `nil' ⊑ Nil'` above: after
    [IotaIntro] + [Lam], the contravariant domain check reproduces the
    original goal. These require a seen-set, coinductive account, or
    step-indexing on top of the precise-interpretation layer.

1b. **Both-sides iota unfolding** (the realistic `dtrue ⊑ dBool` case).
    When both sides are iotas, we'd need a dual [IotaElim] rule as well,
    with a well-typedness side condition. A candidate:

    ```
    [IotaElim]: (Γ ⊢ a : ι. body) → Γ ⊢ body[0 := a] ⊑ b → Γ ⊢ a ⊑ b
    ```

    But "a has type ι. body" is circular — it's exactly the subtyping
    goal we're trying to prove. One way out: restrict [IotaElim] to
    terms whose head is a literal `iota` (so that elimination is
    really a definitional unfolding), effectively folding it into
    [DefEq]. This moves the question back to: is the precise
    interpretation closed under beta when the beta-redex "crosses" a
    self-type? This is the main open question left by this exploration.

2.  `defEq_of_nf_eq` in `DefEq.lean` is a stub; a real mechanisation
    needs soundness of `nf` vs `DefEq`, plus confluence of beta.

3.  Substitution covariance of `PSub` w.r.t. `PDefEq` would need:
    `PSub Γ a b  →  PDefEq a a'  →  PDefEq b b'  →  PSub Γ a' b'`.
    This is true but nontrivial — it is essentially "PSub is closed
    under definitional equality", which is the non-obvious content of
    extending Sub with [DefEq].

### Proof obligations a future agent would need

1.  `PSub.congr_defEq : PSub Γ a b → PDefEq a a' → PDefEq b b' → PSub Γ a' b'`
    (closure under DefEq — replacing the [DefEq] rule with this lemma is a
    common move in intensional type theories).
2.  `PSub.trans : PSub Γ a b → PSub Γ b c → PSub Γ a c`
    (with [DefEq] + [IotaIntro], the cut-formula measure needs to account
    for definitional-equality expansions; lexicographic on
    `(normal-form-size b, derivation size)` is a natural starting point).
3.  `PSub.weaken` / `PSub.subst` (standard, should be mechanical).
4.  `dtrue ⊑ dBool` as a concrete `PSub` proof term.

### Comparison with other approaches

| Approach               | Handles covariant self-ref | Handles contravariant self-ref | Inductive? |
|------------------------|:--------------------------:|:------------------------------:|:----------:|
| Pure Sub (Simple Och)  | ✗                          | ✗                              | ✓          |
| Precise (this file)    | ✓                          | ✗                              | ✓          |
| Step-indexed Sub       | ✓                          | ✓ (bounded depth)              | ✓          |
| Coinductive Sub        | ✓                          | ✓                              | ✗ (coind.) |
| Algorithmic + seen-set | ✓                          | ✓                              | algorithmic |

The **precise** approach is the simplest thing that could possibly work
for the motivating examples (Scott/Church-encoded data with covariant
self-reference in eliminators), and it stays firmly inductive.

### Next steps

1.  Mechanically verify `PSub.congr_defEq` for the sub-language without
    iota (i.e. as an extension of `Och.Simple.Sub`).
2.  Add `iotaElim` (self-type elimination) and check that
    `[IotaIntro]` + `[IotaElim]` are internally consistent.
3.  Write the full `dtrue ⊑ dBool` derivation as a proof term and see
    which obligations actually need [DefEq] versus which can close by
    [Refl] alone.
4.  Investigate whether [DefEq] can be restricted to a smaller closure
    (e.g. "equal after zero-or-one beta") to simplify the closure lemma.
-/

end Och.Simple.Precise
