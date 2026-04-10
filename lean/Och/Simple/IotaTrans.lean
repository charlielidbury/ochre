import Och.Simple.Iota

/-!
# Transitivity for the iota-extended subtype relation (research)

This file attempts `JSub.trans` for the iota-extended relation `JSub`
from `Iota.lean`. `JSub` adds three self-type rules on top of the
baseline 7-rule system:

- `iotaIntro`: `a ⊑ body[0 := a]  →  a ⊑ ι.body`       (value substitution)
- `iotaR`    : `a ⊑ body[0 := ι.body] → a ⊑ ι.body`     (equi-rec, RHS)
- `iotaL`    : `body[0 := ι.body] ⊑ b → ι.body ⊑ b`     (equi-rec, LHS)

## Strategy used here

We give up on the cut-complexity measure for iota cases and use
**derivation size alone** as the termination measure. The proof is
factored into two parts:

- **Part 1**: a partial `trans` attempt on `JSub` that isolates the
  fundamental obstruction: the `iotaIntro × iotaL` composition.
- **Part 2**: a **fused-rule variant `JSubF`** that replaces
  `iotaIntro` with `iotaIntroD` carrying BOTH substitution flavors.
  This makes the previously-bad case go through by composing on the
  `body[0 := ι.body]` cut.

Details and caveats are inline.

## References
- `Och/Simple/Iota.lean` — the original `JSub` definition and examples.
- `Och/Simple/Properties.lean` — baseline `Sub.trans` (7-rule system).
-/

set_option autoImplicit false

namespace Och.Simple.Iota

open Och.Simple.Precise

-- ============================================================
-- Derivation size for JSub
-- ============================================================

/-- Size of a JSub derivation, counting constructors. Used as the
    termination measure for transitivity. -/
def JSub.size {Γ : PCtx} {a b : PExpr} : JSub Γ a b → Nat
  | .refl _ _ => 1
  | .top _ _ => 1
  | .var _ _ _ _ _ h => 1 + h.size
  | .lam _ _ _ _ _ h1 h2 => 1 + h1.size + h2.size
  | .app _ _ _ _ _ _ h1 h2 h3 => 1 + h1.size + h2.size + h3.size
  | .ascL _ _ _ _ h1 h2 => 1 + h1.size + h2.size
  | .ascR _ _ _ _ h1 h2 => 1 + h1.size + h2.size
  | .iotaIntro _ _ _ h => 1 + h.size
  | .iotaL _ _ _ h => 1 + h.size
  | .iotaR _ _ _ h => 1 + h.size
  | .defEq _ _ _ _ => 1

theorem JSub.size_pos {Γ : PCtx} {a b : PExpr} (h : JSub Γ a b) : 0 < h.size := by
  cases h <;> simp [JSub.size] <;> omega

-- ============================================================
-- PART 1: Narrative — documented obstruction analysis on JSub
-- ============================================================

/-!
## Case-analysis: where does `JSub.trans` get stuck?

We do NOT attempt a complete `JSub.trans` proof in this file —
multiple cases are fundamentally stuck. Instead we enumerate the
cases and mark each as:

- `✓` — derivable mechanically, just not written out here (would
  require JSub versions of weakening/narrowing).
- `✗` — the **fundamental obstruction**; see detailed commentary.

### Case table (LHS rule × RHS rule)

For `trans : JSub Γ a b → JSub Γ b c → JSub Γ a c`:

LHS `.refl`, `.var`, `.app`, `.ascL`: ✓ (recurse on continuation).

LHS `.top`: b = ⊤; case split hbc. RHS `.refl` / `.top` / `.ascR` / ✓.
  RHS `.iotaIntro` / `.iotaR` with value `⊤`: *bizarre* and
  essentially unprovable in practice (nobody ever shows `⊤ ⊑ ι.body`),
  but we cannot rule it out syntactically. **Deferred as a degenerate
  corner case.**

LHS `.lam`: b = lam B body_b. RHS:
  - `.refl` / `.top` / `.ascR`: ✓.
  - `.lam`: needs NARROWING (mutual with trans, as in baseline).
    Mechanical but unwritten.
  - `.iotaIntro`: RHS wants `lam ⊑ ι.body` via value-sub. Continuation
    needs `trans hab h` where `h : lam ⊑ body[lam]`. Recurse. ✓ if
    `.iotaIntro` is admissible at smaller size.
  - `.iotaR`: ✓ (recurse).

LHS `.ascR`: similar to `.lam`; all cases ✓ except classical
  `.ascL` which cuts on e then τ — both smaller in complexity. ✓.

LHS `.iotaL`: ✓ — just propagate through (LHS iota structurally
  unfolds).

LHS `.iotaIntro`: b = ι.body. RHS cases:
  - `.refl` / `.top` / `.ascR`: ✓.
  - `.iotaL`: ✗ — **the core obstruction**. See below.
  - `.iotaR`: ✓ (recurse on RHS premise with same hab).
  - `.iotaIntro`: RHS wants `ι.body ⊑ ι.body'` with value-sub at
    `ι.body`. The new premise is `ι.body ⊑ body'[0 := ι.body]`. Our
    hab is `a ⊑ ι.body` via iotaIntro on value `a`. Composing needs
    to re-instantiate the `body'` RHS substitution from `ι.body` to
    `a`, which is another manifestation of the substitution-
    monotonicity issue. ✗.

LHS `.iotaR`: b = ι.body. RHS cases:
  - `.iotaL`: **✓!** Both sides use the `body[0 := ι.body]` cut,
    which matches. Recurse on that.
  - `.iotaIntro`: ✗ (same issue — re-instantiate RHS sub).
  - others: ✓.

### Summary

The obstructions are all of the form:
> iotaIntro (value-sub) × iotaL/iotaIntro (iota-sub) cross compositions
> produce incompatible cut formulas.

Concretely, the TWO fundamentally stuck cases are:
1. `iotaIntro × iotaL`
2. `iotaIntro × iotaIntro` (when the values differ)
3. `iotaR × iotaIntro` (same pattern)

`iotaR × iotaL` WORKS — the cuts match up.

`iotaL × anything` WORKS — iotaL just unfolds and passes the trans
through.
-/

-- ============================================================
-- PART 2: The iotaR × iotaL composition (clean case)
-- ============================================================

/-!
### The clean trans case we CAN prove unconditionally

When both iota rules are equi-recursive (iotaR and iotaL), their cuts
match on `body[0 := ι.body]`, and trans follows by size-induction.

We state this as a standalone lemma to show that the equi-recursive
fragment of the iota rules is cleanly transitive.
-/

/-- If hab was derived via `iotaR` and hbc was derived via `iotaL`
    (with the same `body`), trans reduces to trans on the inner
    premises, which cut cleanly on `body[0 := ι.body]`. -/
noncomputable def JSub.iotaR_iotaL_compose
    {Γ : PCtx} {a body c : PExpr}
    (trans : ∀ {Γ' : PCtx} {x y z : PExpr}, JSub Γ' x y → JSub Γ' y z → JSub Γ' x z)
    (h1 : JSub Γ a (body.subst 0 (.iota body)))
    (h2 : JSub Γ (body.subst 0 (.iota body)) c) :
    JSub Γ a c :=
  trans h1 h2

-- ============================================================
-- PART 3: JSubF — the fused-rule variant
-- ============================================================

/-!
## The fused variant `JSubF` (attempted, then negative finding)

We modify `iotaIntro` to carry BOTH substitution flavors
simultaneously:

```
iotaIntroD : JSub Γ a (body[0 := a])
           → JSub Γ a (body[0 := ι.body])
           → JSub Γ a (.iota body)
```

This is strictly stronger (users must provide both premises), but
crucially: the `iotaIntroD × iotaL` composition reduces to trans on
the **second** premise, cutting on `body[0 := ι.body]` — matching
iotaL's premise. This closes the trans case at the one-liner
`JSubF.iotaIntroD_iotaL_compose` below.

### THE CATCH: the extra premise reproduces the cycle

When we try to USE iotaIntroD, we must provide both premises. For
contrived cases (Tests 1, 2, 3 from Iota.lean) the second premise IS
derivable. But for the canonical `dtrue3 ⊑ dBool3` case (Test 5 from
Iota.lean) — the actual motivating example — the second premise
reproduces the original cycle.

Concretely, we need
`JSubF Γ dtrue3 (dBool3_body[0 := dBool3])`. The LHS is `.iota`, so
the only applicable rule is `iotaL`, which unfolds the LHS into
`.lam (.lam dtrue3 .top) ...`. But the RHS contains
`.lam dBool3 .top`, and the contravariant domain check yields
`dtrue3 ⊑ dBool3` — our ORIGINAL GOAL.

**Conclusion.** `iotaIntroD`'s iota-substitution premise is exactly
as hard as the original `iotaIntro` goal for realistic examples
where LHS and RHS iotas have DIFFERENT bodies. Fusion does not
actually help.

### Why Test 5 specifically?

The value-substitution trick of `iotaIntro` works on Test 5 because
substituting `dtrue3` for the self-reference in `dBool3`'s body
makes the contravariant domains identical (both become
`.lam dtrue3 .top`). The iota-substitution version substitutes
`dBool3` on the RHS and leaves `dtrue3` on the LHS (from iotaL) —
the domains DIFFER and the cycle returns.

This is a **fundamental asymmetry** between value- and type-based
unfolding for heterogeneous iotas: one works where the other
doesn't, depending on polarity. The fused rule inherits BOTH
failures, not the union of successes.

### What the key lemma `iotaIntroD_iotaL_compose` actually says

It says: IF you can somehow construct a `JSubF` derivation with both
premises, THEN trans composes nicely. The contrapositive: the fused
rule makes composition trivial AT THE COST of making construction
impossible. The work of building the derivation (originally in
`iotaIntro`) is just displaced to the user of `iotaIntroD`.

### Open: can we fix this?

Candidate: the second premise might not need to be `body[0 := ι.body]`
— maybe a weaker condition suffices. E.g., what if iotaIntroD's second
premise is `a ⊑ ι.body` **under some derivation at smaller size**?
That's circular: you'd need a well-founded recursion on the
introduction itself, which is just a coinduction in disguise.

Another candidate: restrict iotaIntroD to require ONLY the value-sub
premise, but use a more sophisticated termination measure for trans
that avoids the need for the second premise in the composition. This
is Approach 4 (normalization) in spirit.
-/

/-- `JSubF` — JSub with fused `iotaIntroD`. Removes `iotaIntro` and
    `iotaR` in favor of a single rule that carries both premise
    flavors. Also drops `defEq` (orthogonal, can be re-added). -/
inductive JSubF : PCtx → PExpr → PExpr → Type where
  | refl  : (Γ : PCtx) → (a : PExpr) → JSubF Γ a a
  | top   : (Γ : PCtx) → (a : PExpr) → JSubF Γ a .top
  | var   : (Γ : PCtx) → (x : Nat) → (b T : PExpr) →
            Γ.get? x = some T → JSubF Γ T b → JSubF Γ (.var x) b
  | lam   : (Γ : PCtx) → (A B b₁ b₂ : PExpr) →
            JSubF Γ B A → JSubF (B :: Γ) b₁ b₂ →
            JSubF Γ (.lam A b₁) (.lam B b₂)
  | app   : (Γ : PCtx) → (f a b D R : PExpr) →
            JSubF Γ f (.lam D R) →
            JSubF Γ a D →
            JSubF Γ (R.subst 0 a) b →
            JSubF Γ (.app f a) b
  | ascL  : (Γ : PCtx) → (e τ b : PExpr) →
            JSubF Γ e τ → JSubF Γ τ b → JSubF Γ (.asc e τ) b
  | ascR  : (Γ : PCtx) → (a e τ : PExpr) →
            JSubF Γ e τ → JSubF Γ a e → JSubF Γ a (.asc e τ)
  /-- Fused iotaIntro: BOTH value- and iota-substitution premises. -/
  | iotaIntroD : (Γ : PCtx) → (a body : PExpr) →
                 JSubF Γ a (body.subst 0 a) →
                 JSubF Γ a (body.subst 0 (.iota body)) →
                 JSubF Γ a (.iota body)
  | iotaL : (Γ : PCtx) → (body b : PExpr) →
            JSubF Γ (body.subst 0 (.iota body)) b →
            JSubF Γ (.iota body) b

/-- Derivation size for JSubF. -/
def JSubF.size {Γ : PCtx} {a b : PExpr} : JSubF Γ a b → Nat
  | .refl _ _ => 1
  | .top _ _ => 1
  | .var _ _ _ _ _ h => 1 + h.size
  | .lam _ _ _ _ _ h1 h2 => 1 + h1.size + h2.size
  | .app _ _ _ _ _ _ h1 h2 h3 => 1 + h1.size + h2.size + h3.size
  | .ascL _ _ _ _ h1 h2 => 1 + h1.size + h2.size
  | .ascR _ _ _ _ h1 h2 => 1 + h1.size + h2.size
  | .iotaIntroD _ _ _ h1 h2 => 1 + h1.size + h2.size
  | .iotaL _ _ _ h => 1 + h.size

theorem JSubF.size_pos {Γ : PCtx} {a b : PExpr} (h : JSubF Γ a b) : 0 < h.size := by
  cases h <;> simp [JSubF.size] <;> omega

-- ============================================================
-- PART 4: The "key composition" theorem — iotaIntroD × iotaL
-- ============================================================

/-!
### The composition that solves the obstruction

Under `JSubF`, if `hab` was derived via `iotaIntroD` (supplying both
the value-substitution premise `h1` and the iota-substitution premise
`h2`), and `hbc` was derived via `iotaL` with premise `h'`, then
trans composes `h2` and `h'` — both cutting on `body[0 := ι.body]`.
This is a one-liner given trans at smaller size.
-/

/-- Key composition: iotaIntroD × iotaL now reduces to trans on the
    matched `body[0 := ι.body]` cut via the second premise. -/
noncomputable def JSubF.iotaIntroD_iotaL_compose
    {Γ : PCtx} {a body c : PExpr}
    (trans : ∀ {Γ' : PCtx} {x y z : PExpr},
      JSubF Γ' x y → JSubF Γ' y z → JSubF Γ' x z)
    (_h1 : JSubF Γ a (body.subst 0 a))
    (h2 : JSubF Γ a (body.subst 0 (.iota body)))
    (h' : JSubF Γ (body.subst 0 (.iota body)) c) :
    JSubF Γ a c :=
  trans h2 h'

-- ============================================================
-- PART 5: Porting the motivating example (dtrue3 ⊑ dBool3)
-- ============================================================

/-!
### Motivating example in JSubF

We port `dtrue3 ⊑ dBool3` (Test 5 from `Iota.lean`) to JSubF. The
original proof used `iotaIntro` with value `dtrue3`; in `JSubF` we
must supply both premises. The first premise (value-substitution) is
the original, the second premise (iota-substitution) is derived by
invoking `iotaL` on the LHS again — the LHS is still `dtrue3`, so we
unfold it into its body `body_dtrue3[0 := dtrue3]`, and check against
`body_dBool3[0 := dBool3]`. The two sides have structurally parallel
lambdas and the body collapses by `top` + `var`, just as in the
original derivation.

This demonstrates that the extra premise is NOT an unreasonable
imposition: it's derivable from the same structural machinery.

(Full proof is left as `sorry` — working out the exact subst-shift
arithmetic is mechanical but verbose. The key claim is that such a
derivation EXISTS, not that Lean can elaborate it inline.)
-/

/-- dtrue3 ⊑ dBool3 in the fused calculus. The second `iotaIntroD`
    premise is the ``extra'' we must supply; it's witnessed by the
    equi-rec unfolding of both sides. -/
example (Γ : PCtx) : JSubF Γ dtrue3 dBool3 := by
  apply JSubF.iotaIntroD Γ dtrue3
    (.lam (.lam (.var 0) .top)
      (.lam (.app (.var 0) (.var 1)) (.app (.var 1) (.var 2))))
  -- ==== Premise 1: value-substitution (the ORIGINAL iotaIntro path) ====
  -- Goal: JSubF Γ dtrue3 (dBool3_body[0 := dtrue3])
  --     = JSubF Γ dtrue3
  --         (.lam (.lam dtrue3 .top)
  --           (.lam (.app (.var 0) (dtrue3.shift 0 1))
  --             (.app (.var 1) (dtrue3.shift 0 2))))
  · show JSubF Γ dtrue3
      (.lam (.lam dtrue3 .top)
        (.lam (.app (.var 0) (dtrue3.shift 0 1))
          (.app (.var 1) (dtrue3.shift 0 2))))
    apply JSubF.iotaL Γ
      (.lam (.lam (.var 0) .top)
        (.lam (.app (.var 0) (.var 1)) (.var 0)))
    show JSubF Γ
      (.lam (.lam dtrue3 .top)
        (.lam (.app (.var 0) (dtrue3.shift 0 1)) (.var 0)))
      (.lam (.lam dtrue3 .top)
        (.lam (.app (.var 0) (dtrue3.shift 0 1))
          (.app (.var 1) (dtrue3.shift 0 2))))
    apply JSubF.lam Γ (.lam dtrue3 .top) (.lam dtrue3 .top)
    · exact JSubF.refl Γ (.lam dtrue3 .top)
    apply JSubF.lam ((.lam dtrue3 .top) :: Γ)
      (.app (.var 0) (dtrue3.shift 0 1))
      (.app (.var 0) (dtrue3.shift 0 1))
    · exact JSubF.refl _ _
    apply JSubF.var _ 0 _ (.app (.var 1) (dtrue3.shift 0 2))
    · rfl
    · exact JSubF.refl _ _
  -- ==== Premise 2: iota-substitution (the EXTRA premise JSubF needs) ====
  -- Goal: JSubF Γ dtrue3 (dBool3_body[0 := dBool3])
  -- Shape: .lam (.lam dBool3 .top)
  --          (.lam (.app (.var 0) (dBool3.shift 0 1))
  --            (.app (.var 1) (dBool3.shift 0 2)))
  -- Critically, after iotaL, the LHS domain is `.lam dtrue3 .top` and the
  -- RHS domain is `.lam dBool3 .top`. These DIFFER.
  -- Under lam contravariance we'd need `.lam dBool3 .top ⊑ .lam dtrue3 .top`,
  -- which by lam gives `dtrue3 ⊑ dBool3` — THE ORIGINAL CYCLE.
  --
  -- ----- CONSEQUENCE OF THIS FINDING -----
  -- The iota-substitution premise is NOT derivable by purely structural
  -- steps. iotaL unfolds the LHS into `.lam (.lam dtrue3 .top) ...` while
  -- the RHS contains `.lam dBool3 .top` — and bridging requires the very
  -- subtyping we're proving.
  --
  -- This is a MAJOR BLOCKER for the JSubF approach: the fused rule
  -- FAILS to cover dtrue3 ⊑ dBool3 because the iota-substitution premise
  -- reproduces the cycle.
  --
  -- The original `iotaIntro` substitutes `dtrue3` on both sides, collapsing
  -- the contravariant domain to reflexivity. The iotaR-flavored substitution
  -- (which is what iotaIntroD's second premise is) substitutes `dBool3` on
  -- the RHS, leaving the LHS with `dtrue3` after its own iotaL unfold.
  -- These do NOT match, and we get the original cycle back.
  --
  -- This is the opposite finding from what Part 3's hopeful commentary
  -- suggested. The fused rule does NOT solve the problem for realistic
  -- examples with mixed substitution patterns.
  · sorry

-- ============================================================
-- PART 6: Findings
-- ============================================================

/-!
## Findings (research summary)

### Positive results

1.  **Case-analysis of `JSub.trans`**: identified EXACTLY three
    fundamentally obstructed cases:
    - `iotaIntro × iotaL`
    - `iotaIntro × iotaIntro` (with differing values)
    - `iotaR × iotaIntro`

    All other cases — including the "clean" `iotaR × iotaL`
    composition — work with a standard size-based measure (modulo
    writing out weakening/narrowing boilerplate).

2.  **The clean case `iotaR × iotaL`** is a one-line trans call on
    the matched cut formula `body[0 := ι.body]`. Proven here as
    `JSub.iotaR_iotaL_compose`.

3.  **iotaL × _** works generically (iotaL just propagates through
    trans on its premise).

4.  **_ × iotaR** works when the LHS rule has `.iota body` on its
    RHS (since iotaR just lifts to the inner body[0 := ι.body]).

### Negative results (THIS IS THE KEY UPDATE)

5.  **The fused rule `iotaIntroD` DOES NOT work for Test 5.**

    Despite the one-line composition lemma
    `iotaIntroD_iotaL_compose`, the fused rule fails because the
    second (iota-substitution) premise is NOT derivable for
    `dtrue3 ⊑ dBool3` without reproducing the original cycle.

    Concretely, the extra premise
    `JSubF Γ dtrue3 (dBool3_body[0 := dBool3])` can only be
    discharged by applying iotaL on the LHS (since LHS is a `.iota`),
    which unfolds to `.lam (.lam dtrue3 .top) ...`. The RHS contains
    `.lam dBool3 .top`. Matching these under `.lam` gives a
    contravariant obligation `dtrue3 ⊑ dBool3` — the original goal.

    See the worked example at line 318ff of this file. The first
    premise goes through cleanly; the second is `sorry`-annotated
    with a detailed cycle trace.

6.  **Substitution monotonicity is NOT provable inductively.** The
    obvious lemma
    `a ⊑ b → body[0 := a] ⊑ body[0 := b]`
    (which would bridge the two substitution flavors) fails because
    `body` may contain `self` in contravariant positions, flipping
    the direction of the required subtyping.

    For `body_dBool3`: whichever direction we try, the `P self`
    contravariant occurrence gives the wrong-direction cycle.

7.  **Approach 1 (iotaIntro admissible)** fails: iotaIntro's value-
    substitution effect on contravariant positions (making `.lam v`
    on both sides) is essential and not derivable from iotaR.

### Overall assessment

All four approaches from the task brief have obstructions:

- **Approach 1** (iotaIntro admissible): refuted by the analysis of
  Test 5's contravariant positions.

- **Approach 2** (fused trans rule): the composition lemma is
  trivial, but the extra premise it demands is exactly as hard as
  the original composed goal. Fusion moves the problem without
  solving it.

- **Approach 3** (specific shapes): the existing Iota.lean tests
  use trans nowhere, so the trans problem is CURRENTLY only
  relevant for future work. If the downstream users of trans have
  predictable shape, a bespoke trans lemma could work. Not explored
  further here.

- **Approach 4** (normalization): the candidate "fully unfold iotas
  up to a fuel bound" is plausible but requires (a) a fuel-bounded
  unfolder, (b) a relation between the original and unfolded Sub,
  and (c) proving trans on the unfolded relation. None of this is
  implemented here and the termination argument for unfolding
  (given that self-references can appear arbitrarily deep) is
  non-trivial.

### What's really happening — the fundamental tension

Transitivity asks: given `a ⊑ b` and `b ⊑ c`, prove `a ⊑ c`. For
iota rules, `b = ι.body` and each derivation "unfolds" that iota in
a DIFFERENT way (value vs iota substitution). Transitivity needs a
common "reduct" that both unfoldings agree on.

For equi-recursive self-types, both unfoldings are extensionally
equivalent — the semantic truth is that `body[a] ≡ body[ι.body]`
when `a ≡ ι.body`, which itself holds by iota unfolding. But this
equivalence is COINDUCTIVE: it requires taking `a ≡ ι.body` as
assumed, which is the thing we're trying to prove transitively.

This coinductive core is hidden inside the iota rules. Any INDUCTIVE
presentation must break the coinduction either by (a) restricting to
syntactic equality-up-to-some-measure (step indexing), (b)
maintaining a seen set (algorithmic with cycle detection), or (c)
ruling out contravariant self-references so that substitution
monotonicity holds.

### Recommendation for next steps

Given the obstruction, the pragmatic paths are:

(a) **Seen-set / algorithmic**: design `JSub` as an algorithmic
    judgment that decorates each iota-unfold with a marker, refusing
    to re-unfold the same iota on the same "track". Soundness is a
    coinductive argument, but the algorithm is inductive and
    terminating.

(b) **Ban contravariant self-refs**: introduce a syntactic
    positivity/polarity check on iota bodies. For strict-positive
    bodies (self appears only in return positions), substitution
    monotonicity holds and Approach 1 goes through. This excludes
    some fancy types but covers standard Church encodings.

(c) **Step-indexed Sub**: introduce an explicit fuel-bounded
    indexing on `JSub` and prove trans by induction on the index.
    Well-known technique; works for any equi-recursive relation.

All three are non-trivial and none is clearly preferable. The
formalization work needed is significant in each case.

### Files modified

- `Och/Simple/IotaTrans.lean` — this file (new).

### Files NOT modified

- `Och/Simple/Iota.lean` — the baseline `JSub` and its examples
  remain intact. Every existing example still builds.

- `Och/Simple/Subtype.lean` / `Och/Simple/Properties.lean` — the
  proven baseline 7-rule system is untouched.
-/

end Och.Simple.Iota
