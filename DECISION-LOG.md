# Decision Log

Record significant design decisions here. Each entry should explain WHAT was
decided, WHY, and what alternatives were considered.

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

**Trade-off:** self_intro breaks composability of SubtypeTrans congruence
lemmas. The self_intro case in lam_body/mu_body/app_cong requires putting
a mu INSIDE a context wrapper (lam/app), which no constructor supports.
These are sorry'd but may not arise in practice.

**Alternatives rejected:**
- (c) alone: transparent mu (no wrapping) breaks tests that expect mu in output
- Wrapping concEval too: breaks mu-app unrolling (mu wrapping prevents lam matching)
- self_intro in Subtype': breaks mu_rhs_shape needed by monotonicity

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

### Normalize under binders in absEval (2026-03-31)
Required for `succ 2 = 3`. Domains NOT normalized (would break monotonicity).

### Env-based beta-reduction (2026-03-31)
Changed from substitution to env extension in app case. Makes soundness
proof a straightforward induction (same body, different envs).

### WellTyped precondition for soundness (2026-03-31)
Without it, `(true : Nat)` would be unsound. WellTyped ensures ascriptions
are valid.

</details>
