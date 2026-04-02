# Decision Log

Record significant design decisions here. Each entry should explain WHAT was
decided, WHY, and what alternatives were considered.

---

## 2026-04-02: Equi-recursive self-intro (substitute mu, not value)

**Decision:** Changed self-intro in `subCheckNF` from Cedille-style
(`a ⊑ body[x := a]`, substitutes the value) to equi-recursive
(`a ⊑ body[x := mu x ann body]`, substitutes the mu type itself).
Also added a coinductive `seen` set to prevent divergence from circular
unfolding.

**Why:** Variant B (MuNat) uses the self-variable `N` in a TYPE position
(domain of the successor function: `s : N → X → X`). Cedille-style self-intro
substitutes the VALUE (`zero_mu`) there, producing `s : zero_mu → X → X`.
The contravariant domain check then requires `MuNat ⊑ zero_mu` (type ⊑
value), which is false. Equi-recursive self-intro substitutes the mu TYPE,
keeping `s : MuNat → X → X`, so the domain comparison is `MuNat ⊑ MuNat`
(trivially true).

**Alternatives considered:**
1. **Cedille-style + equi-recursive caching only:** Caching alone doesn't
   fix the problem because the circularity produces `MuNat ⊑ zero_mu`
   (reverse direction), not the cached `zero_mu ⊑ MuNat`.
2. **Separate rules based on annotation:** Use Cedille-style when
   `ann ≠ Type` and equi-recursive when `ann = Type`. Rejected as
   unnecessary complexity — equi-recursive works for both cases.
3. **Keep Cedille-style, fix later with richer subtyping:** Would require
   equi-recursive subtyping anyway, just pushed to a different layer.

**Impact on dependent elimination:** None. Dependent elimination goes through
self-ELIM (which already substitutes the mu, unchanged). Self-intro is about
introducing a value INTO a mu type, not extracting dependent information.

**Impact on existing tests:** None. Variant A (SelfNat) has an unused
self-variable — both substitutions are no-ops. All M1-M4 tests still pass.

**Impact on soundness proof:** None. The soundness proof is about
`absEval`/`concEval`, not `subCheckNF`. The `Subtype'`/`SubtypeCore`
inductive relations are unchanged.

---

## 2026-04-01: Unify fix and iota into mu

**Decision:** Replace `fix` (recursion) and `iota` (self types) with a single
primitive `mu (x : ann). body` (self-reference).

**Why:** In Och's "terms and types are the same" framework, fix and iota
express the same operation (self-reference) at different precision levels.
Concrete eval unrolls (fix behavior). Abstract eval normalizes under binder
(iota behavior). The evaluation mode already provides the distinction — two
separate primitives are redundant.

The annotation `ann` is load-bearing: it prevents divergence in both absEval
(avoids entering the body of recursive functions) and subtype checking (enables
comparing mu types without unfolding bodies, per Victor Maia's Kind2 trick).

**Full analysis:** `docs/ideas/merge-fix-iota.md`

**Alternatives considered:**
- Keep fix and iota separate (the previous approach). Works but duplicates
  self-reference across two primitives with different evaluation strategies.
- Merge into unannotated `mu x. body`. Rejected — the annotation is needed
  for termination of both absEval and subtype checking.

---

## 2026-04-01: Normalize domains in subCheckNF

**Decision:** Added `normalizeDomain` helper in subCheckNF that normalizes
domain expressions (using absEval with context variables as neutrals) before
adding them to the inferType context.

**Why:** absEval deliberately does NOT normalize lambda domains (to preserve
monotonicity for proofs). But subCheckNF's `inferType` needs domains in normal
form to pattern-match on them. For example, `Vec' (var "T")` is stored as
`app (lam "T" ...) (var "T")` — an `.app`, not a `.lam`. Without normalization,
inferType can't recognize it as a function type, and type inference for stuck
applications like `(v1 (Vec T)) (lam ...)` fails.

This flipped M4a (`appendVec ⊑ T→Vec T→Vec T→Vec T`), completing Phase 1.

**Alternatives considered:**
- Normalize domains in absEval itself. Rejected — would break the
  monotonicity invariant that proofs depend on.
- Have inferType normalize types on lookup. Would work but is less clean —
  normalization at insertion is simpler and predictable.
- Enhance inferType to reduce beta-redexes inline. More complex, and
  normalizeDomain already handles all cases.

**Impact on proofs:** The monotonicity/soundness proofs are already sorry'd.
When they resume, they'll need to account for domain normalization in
subCheckNF. Since `normalizeDomain` only affects the subtype checker (not
absEval), the impact should be contained to subCheckNF-related lemmas.

---

## 2026-04-01: Mu soundness resolved via env change + self_intro

**Decision:** Changed absEval mu case to bind x to the mu value (not var x),
and added `self_intro` constructor to SubtypeTrans.

**The problem (previously documented):** EnvConsistent needed
`SubtypeTrans (mu x ann body) (var x)`, which has no constructor.

**Solution applied (combination of approaches a and c from prior analysis):**

1. **Changed absEval mu env binding:** `(x, var x)` → `(x, mu x ann body)`.
   This matches concEval's env, making EnvConsistent trivially satisfied.
   All tests pass — the change only affects how x-references in mu bodies
   are normalized, and current tests don't depend on the old behavior.

2. **Added self_intro to SubtypeTrans:** `SubtypeTrans a body' → SubtypeTrans a
   (mu x ann body')`. This bridges IH result (v ⊑ body') to soundness goal
   (v ⊑ mu x ann body'), since absEval wraps the result in mu.

**Trade-off (RESOLVED):** self_intro was originally only in SubtypeTrans,
which broke composability of congruence lemmas (lam_body, mu_body, app_cong).
This was resolved by moving self_intro to Subtype' and changing SubtypeTrans.self_intro
to take a Subtype' argument. See the 2026-04-01 "self_intro to Subtype'" entry below.

**Alternatives rejected:**
- (c) alone: transparent mu (no wrapping) breaks tests that expect mu in output
- Wrapping concEval too: breaks mu-app unrolling (mu wrapping prevents lam matching)

---

## 2026-04-01: Move self_intro to Subtype' to fix congruence composability

**Decision:** Added `self_intro` to `Subtype'` (not just SubtypeTrans),
and changed `SubtypeTrans.self_intro` to take a `Subtype'` argument instead
of `SubtypeTrans`.

**The problem:** With self_intro only in SubtypeTrans (taking a SubtypeTrans
argument), the congruence lemmas (lam_body, mu_body, app_cong_left,
app_cong_right) had sorry'd self_intro cases. The issue was circularity:
in the induction on SubtypeTrans for lam_body, the self_intro case
required calling lam_body on self_intro — the exact thing being proved.

**Solution:** Adding self_intro to Subtype' breaks the circularity. In
the self_intro case of `SubtypeTrans.lam_body`, we can now construct:
```
.trans (.step (.lam_body h'))
      (.step (.lam_body (.self_intro (.refl _))))
```
The first step uses the Subtype' sub-proof directly. The second uses
Subtype'.self_intro and Subtype'.refl — no recursive SubtypeTrans needed.

**Impact:**
- Eliminated all 5 sorry'd congruence cases in SubtypeTrans
- Subtyping.lean is now sorry-free
- mu_rhs_shape returns a disjunction (Or.inl mu / Or.inr self_intro)
- absEval_mono gained 5 sorry'd self_intro cases (unreachable from monotonicity theorem)
- soundness_gen gained 1 sorry'd Subtype'.self_intro case (unreachable from soundness theorem)
- Net: 9→5 declarations with sorry, Subtyping.lean fully clean

**Alternatives considered:**
- Transparent mu (no wrapping in absEval): would avoid needing self_intro
  entirely, but breaks annotation-based mu-app for abstract args (M1d fails)
- Restricting absEval_mono to a Subtype' subset without self_intro:
  too complex, would require duplicating the inductive definition
- Well-founded recursion instead of structural: doesn't help because the
  circular construction is NOT well-founded (can loop)

---

## 2026-04-01: Prove Subtype'.trans; rewrite soundness without SubtypeTrans

**Decision:** Proved that Subtype' is transitive, then rewrote soundness_gen
to use Subtype' directly instead of SubtypeTrans.

**Why:** SubtypeTrans existed solely because Subtype' wasn't known to be
transitive. The trans constructor in SubtypeTrans created an irresolvable
sorry in soundness_gen: the trans case needed the intermediate expression
to evaluate in both modes, which isn't generally possible.

**How Subtype'.trans is proved:** Structural induction on the second proof
(`induction q generalizing a`). Key insight: in every recursive call, the
second argument (q-position) is strictly smaller, and the first argument
(p-position) can be anything. So standard structural induction on q works —
no well-founded recursion needed.

Cases:
- refl/top: base cases
- lam_body: destruct p (must be refl or lam_body), recurse on bodies
- app_cong: destruct p (refl or app_cong), recurse on components
- mu_body: destruct p (refl, mu_body, or self_intro), recurse
- self_intro: recurse with same p and smaller h2

**Impact:** Eliminated 2 sorrys from soundness_gen (5→3):
- trans case: gone (not a constructor of Subtype')
- SubtypeTrans.self_intro cases: gone (SubtypeTrans no longer used)
New self_intro sorry exists for Subtype' but has a different root cause
(fuel mismatch) and is unreachable from the main theorem.

**SubtypeTrans status:** Still defined in Subtyping.lean (used by
CounterexampleTest.lean for counterexamples), but no longer used by
Soundness.lean. Could be removed entirely if counterexamples are reworked.

---

## 2026-04-01: absEval_evalFreeVars_general is FALSE for mu case

**Decision:** Removed `absEval_evalFreeVars_general`, `absEval_evalFreeVars_neutral`,
and all supporting definitions (`isNeutral`, `EnvEvalClosed'`,
`envEvalClosed'_extend_neutral`, `env_extend_neutral_or`, `env_extend_val`)
from Monotonicity.lean. All were unused.

**Why the theorem is false:** The mu case binds `(x, mu x ann body)` in the env.
The mu value's `evalFreeVars` include input variable NAMES from the body (minus x).
These names are not in P — P tracks which names appear in env values' evalFreeVars
(one level of indirection removed). E.g., Γ = [("y", var "z")] with P = {z}:
the mu value `mu "x" _ (app (var "y") (var "x"))` has evalFreeVars = ["y"],
but P("y") is false.

**Root cause:** The env change from `(x, var x)` to `(x, mu x ann body)` (needed
for soundness) made the theorem false. With `(x, var x)`, evalFreeVars = [x] which
trivially satisfies P ∨ (· = x). With `(x, mu ...)`, evalFreeVars = body's free
vars minus x, which are input-level names not necessarily in P.

**Impact:** Monotonicity.lean is now fully sorry-free. The overall sorry count
dropped from 2 declarations to 1.

**Counterexample:** CounterexampleTest.lean, native_decide verified.

---

## 2026-04-01: Switch soundness_gen to SubtypeCore to eliminate self_intro sorry

**Decision:** Changed soundness_gen to take and return `SubtypeCore` (Subtype'
without self_intro) instead of `Subtype'`. Changed EnvConsistent and WellTyped's
asc case to use SubtypeCore. The main `soundness` theorem converts via toSubtype'.

**The problem:** The self_intro case in soundness_gen had two fundamental
mismatches that couldn't be resolved within the current proof framework:
1. **Fuel mismatch:** absEval uses fuel n (after unwrapping mu), concEval uses
   fuel n+1. Fuel weakening (n+1→n) is FALSE for concEval because it normalizes
   under binders (more fuel = more normalization = different result).
2. **Env mismatch:** absEval uses ((x,mu)::Γ), concEval uses γ (no x binding).
   Can't extend γ with (x,mu) because e_c might reference x (self_intro allows
   Subtype' (var x) body), and concEval isn't env-monotone for shadowed bindings.

**Solution:** SubtypeCore doesn't have self_intro, so the case doesn't exist.
The IH only produces SubtypeCore values (refl, lam_body, mu_body, app_cong, top).
lam_rhs_shape on SubtypeCore gives SubtypeCore (no self_intro leaks through
recursive calls). SubtypeCore.trans proved for the asc case composition.

**Trade-off:** WellTyped's asc case uses SubtypeCore instead of Subtype'. Programs
with ascriptions like `(e : mu_type)` where the proof requires self_intro (e.g.,
e directly subtypes the mu body, not the whole mu) are not covered. In practice,
this is fine for current milestones. Strengthening requires step-indexed logical
relations (which are needed anyway for the mu-app sorrys).

**Impact:** 3→2 sorrys in soundness_gen. Self_intro case eliminated entirely.

**Alternatives considered:**
- Decoupled fuels (separate fuel_a, fuel_c). Solves fuel mismatch but NOT env
  mismatch. Would need env weakening/agreement lemmas that are hard to prove
  in a named variable representation.
- Strong induction on (fuel, sizeOf h_sub). Doesn't help with env mismatch.
- Restrict EnvConsistent to SubtypeCore. Works (this is the approach taken),
  but slightly weakens the soundness theorem.
- Step-indexed logical relations. Would solve everything but is a major
  multi-session effort. Still recommended for the mu-app sorrys.

---

## 2026-04-02: Annotation consistency in WellTyped for mu-app proof

**Decision:** Added annotation consistency condition to WellTyped's app case
for mu functions. When absEval returns a mu with a lambda annotation AND lambda
body, WellTyped requires: (1) matching binder names, (2) WellTyped for both
body result and annotation return body, (3) absEval of the body result
SubtypeCore's the absEval of the annotation return body.

**The problem:** absEval's mu-app uses the annotation (return type) while
concEval's mu-app uses the body (actual computation). These are fundamentally
different expressions. SubtypeCore (structural) can't bridge them. Previous
agents documented this as requiring step-indexed logical relations.

**Key insight:** We DON'T need logical relations for the annotation path. If
WellTyped asserts that the body "implements" the annotation (abstractly), the
proof can chain: concEval(body) ⊑ absEval(body) ⊑ absEval(annotation) = τ.
The first step uses the IH with SubtypeCore from lam_rhs_shape. The second
uses the annotation consistency from WellTyped.

**Why matching binder names are needed:** concEval binds the body's parameter
name, absEval binds the annotation's parameter name. For EnvConsistent (which
maps variables by name), both env extensions must use the same name. Without
alpha-equivalence or de Bruijn indices, we require syntactic name matching.

**Impact:** Proved the mu-app annotation path in soundness_gen (×2: refl and
app_cong). Body-unfold path (ann≠lam or body≠lam) remains sorry'd — 4 sorrys
total, but these are rare cases (iota-like mus used as functions, or mus whose
evaluated body is not a lambda).

**Caveat:** The matching binder name requirement means WellTyped is only
non-vacuously satisfiable for programs where mu annotation parameter names
match body parameter names. The test suite uses "_" in annotations and
meaningful names in bodies. To make the test programs satisfy WellTyped,
either change annotations to match, or switch to a representation without
binder name sensitivity (e.g., de Bruijn indices).

**Alternatives considered:**
- Step-indexed logical relations: would solve everything including body-unfold
  path, but is a major infrastructure change. Still recommended for the
  remaining body-unfold sorrys.
- Substitution-based renaming in the evaluator: avoids binder name matching
  requirement but introduces variable capture issues with the naive subst.
- De Bruijn indices: eliminates binder name issues entirely but requires
  rewriting the whole codebase.
- Using Subtype' instead of SubtypeCore for annotation consistency: SubtypeCore
  is too weak to relate the abstract body result to the annotation return type
  (they're semantically related but structurally different). The condition
  instead uses absEval (evaluation-based), which CAN relate them semantically.

---

## Historical decisions (pre-mu, from main branch)

The following decisions were made before the mu experiment. They describe the
architecture that mu is replacing. Kept for context, not as current guidance.

<details>
<summary>Click to expand historical decisions</summary>

### absEval_freeVars_covered is false (2026-04-01)
absEval does NOT evaluate domain annotations in lambdas, so free vars in
result aren't always covered by the env. Counterexample in CounterexampleTest.lean.

### absEval_succeeds_envsub is false (2026-04-01)
Needs a well-formedness precondition. Counterexample: env with unbound vars
in lambda values. See CounterexampleTest.lean.

### Add iota before proving remaining sorrys (2026-04-01)
Added iota early so all future proof work accounts for it. Chose Option B
(one constructor, implicit intro/elim). Self-type unfolding in app case
deferred — requires type-directed evaluation.

### Direct soundnessC approach (2026-04-01)
Bypassed the factored approach (soundnessC_abs + absEvalC_equiv). Direct
proof relates concEvalC to absEval. 1 sorry remaining (app case).

### absEval_normalize_stable is FALSE (2026-03-31)
Machine-verified counterexample. The LR approach in SoundnessS.lean is
a dead end. Closure-based approach (Closure.lean) supersedes it.

### Closure-based concrete evaluator (2026-03-31)
concEvalC captures definition-site envs in lambda values. Solves the
normalization-under-binders problem for recursive fix.

### Remove trans from Subtype' (2026-03-31)
Enables lambda inversion for monotonicity. SubtypeTrans is the transitive
closure, used in soundness.

### concEval wraps mu results (2026-04-01)

Changed concEval's mu case from unrolling (returning body directly) to wrapping
(returning `mu x ann body'`, like absEval). The app-mu case now matches on the
mu body directly instead of re-unrolling via `concEval fuel γ (.mu ...)`.

**Why:** The old approach made the soundness mu case require self_intro
(concEval unwraps → body value, absEval wraps → mu value). With wrapping, both
evaluators produce mu values, and the soundness case uses mu_body (structural
subtyping). This also corrected a false "unreachable" claim about the
self_intro sorry — the previous mu case was producing self_intro that flowed
through lam_body and appeared as input in recursive calls.

**Trade-off:** The app-mu case in concEval no longer re-evaluates the body
when a mu is in function position. Instead it matches the already-evaluated
body for a lambda. This is slightly more fuel-efficient but semantically
equivalent (the body in the mu value is already evaluated).

**Alternatives considered:**
- Keep unrolling, prove self_intro case. Blocked by fuel/env mismatch.
- Use SubtypeCore for h_sub (exclude self_intro). ACTUALLY WORKS — was
  adopted in the later "Switch soundness_gen to SubtypeCore" decision.
  The key insight was changing WellTyped's asc case to SubtypeCore too.
- Make concEval's app-mu use the annotation (like absEval). Wrong: `add 2 3`
  would evaluate to `Nat` instead of `5`.

### Normalize under binders in absEval (2026-03-31)
Required for `succ 2 = 3`. Domains NOT normalized (would break monotonicity).

### Env-based beta-reduction (2026-03-31)
Changed from substitution to env extension in app case. Makes soundness
proof a straightforward induction (same body, different envs).

### WellTyped precondition for soundness (2026-03-31)
Without it, `(true : Nat)` would be unsound. WellTyped ensures ascriptions
are valid.

</details>
