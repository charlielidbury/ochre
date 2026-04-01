# Decision Log

Record significant design decisions here. Each entry should explain WHAT was
decided, WHY, and what alternatives were considered.

---

## 2026-04-01 ochre-lean-20260401-120716: absEvalC_equiv — partial proof + key insight about readback envs

**What was done:**

1. Proved 5 of 6 cases of `absEvalC_equiv` (var, type, asc, fix, lam). The app case
   remains as sorry.

2. Added `absEval_fuel_mono` to Closure.lean (copied from SoundnessS.lean to avoid
   importing the stalled file). Used for the lam case where readbackA uses fuel n+1
   but absEval's lam case uses fuel n.

3. Added `readbackAEnv_lookup` lemma: if readbackAEnv Γ = some Γ' and Γ.lookup x = some a,
   then readbackA a gives the corresponding Γ'.lookup x value.

4. Reformulated `absEvalC_equiv` with separate `rb_fuel ≥ fuel` parameter to handle
   the fuel offset between sub-evaluations and readbackAEnv.

**Key insight: absEval_normalize_stable may hold for readback envs**

The counterexample in SoundnessS.lean (which proves absEval_normalize_stable FALSE)
relies on env values that are *reducible expressions* like `app (var "z") type`.
But readback envs (from readbackAEnv) contain ONLY lam/type/fix — never var, app, or asc.

More importantly, readback-produced lambda bodies have a crucial property: their only
free variables are bound lambda parameters. All other variables are resolved to constants
during readback (via absEval in the captured env). This means:

1. **Normalization is effectively a no-op** on readback env values (re-normalizing
   a readback result in the same env gives back the same result)
2. **Re-evaluating normalized bodies is env-irrelevant** for non-parameter variables
   (the body doesn't reference them)

This suggests absEval_normalize_stable IS true when restricted to readback envs.

**What's needed to finish the app case:**

1. A "closed body" lemma: absEval in a readback env produces expressions where the
   only free vars are bound lambda parameters
2. An "env irrelevance" lemma: absEval of such closed expressions gives the same
   result regardless of env (for non-referenced vars)
3. absEval_normalize_stable restricted to readback envs

These are well-motivated but non-trivial. Each is a separate proof by induction.

**Alternative considered: changing absEval to use closures**

If absEval used AVal (closures) instead of Expr, it would be structurally parallel
to absEvalC, making absEvalC_equiv trivial. But this would require rewriting ALL
existing proofs (soundness, monotonicity, tests), which is too large for one session.

**Also analyzed and rejected:**

- VR_abs subsumption for asc/fix cases of soundnessC_abs: fundamentally impossible
  with structural VR_abs (requires same body/name, but asc produces different closures)
- absEvalC_equiv at the original fuel (without rb_fuel): fuel mismatch between
  readbackAEnv at fuel n+1 and sub-evaluations at fuel n

---

## 2026-03-31 ochre-lean-20260331-233210: Closure-based concrete evaluator (concEvalC) — NEW APPROACH

**Decision:** Added `concEvalC` in `Och/Closure.lean` — a closure-based concrete
evaluator that captures the definition-site env in lambda values. This is a
fundamentally different approach to the concEvalS soundness problem.

**Why closures (not substitution or env-with-normalization):**

The three previous approaches all hit fundamental obstacles:
1. **concEval (env + normalization under binders):** Normalizes both branches of
   Church-encoded conditionals, causing recursive fix to diverge. UNSOUND for
   recursive programs.
2. **concEvalS (substitution, lambdas as values):** Correct CBV but uses
   substitution while absEval uses env extension. The bridge theorem
   `absEval_normalize_stable` is PROVABLY FALSE. The LR-based soundness proof
   has been stuck for 5+ sessions.
3. **concEvalE (env, lambdas as values, no closures):** Has the "closure problem" —
   returned lambdas lose their definition-site env bindings. `(λx. λy. x) 3 5`
   gives a stuck result because `var x` is not resolved.

Closures solve all three problems:
- Lambdas ARE values (no normalization under binders → fix works)
- Env extension for beta-reduction (structurally parallel to absEval)
- Captured env ensures correct scoping for higher-order functions

**Soundness proof strategy:**

The key insight: `readback` normalizes a closure's body using `absEval` in the
captured env. So relating readback to absEval is a MONOTONICITY question (same
expression, related envs), NOT a normalize-stability question. Monotonicity is
already proven!

Specifically, in the lam case:
- readback body = `absEval ((x, var x) :: readbackEnv γ) body`
- absEval body = `absEval ((x, var x) :: Γ) body`
- If `EnvSub (readbackEnv γ) Γ`, then monotonicity gives `Subtype' readback_body absEval_body`

**Remaining challenge:** CEnvConsistent (the env relationship from the IH) gives
SubtypeTrans (transitive closure), but monotonicity requires Subtype' (single step).
A generalized monotonicity theorem for SubtypeTrans envs would close this gap.

**Tests:** All existing tests pass, including recursive fix with thunked branches
(toZeroThunked, rebuildThunked, addThunked, compositions). Higher-order closure
tests also pass (e.g., `(λx. λy. x) 3 5 = 3`).

---

## 2026-03-31 ochre-lean-20260331-225410: absEval_normalize_stable is FALSE — the LR approach needs restructuring

**Discovery:** The `absEval_normalize_stable` theorem (the planned bridge between
normalized body' and original body in the lam case of fundamental) is **provably
false**. A machine-verified counterexample was added to SoundnessS.lean using
`native_decide`.

**What's false and why:**

The theorem claims: if normalization gives body', and re-evaluating body' gives τ',
then evaluating the original body at additive fuel also gives τ'. This fails for
the `var y ≠ x` case because:

1. Normalization looks up var y → gets raw env value v_y (containing sub-expressions)
2. Re-evaluation evaluates v_y deeply (resolving its internal references)
3. Direct evaluation looks up var y → returns raw v_y WITHOUT further evaluation

Steps 2 and 3 give different results when v_y contains reducible sub-expressions.

**Also discovered:** WellTyped is NEITHER fuel-monotone NOR fuel-anti-monotone.
Previous analysis claimed anti-monotonicity. Machine-verified that WellTyped 2 = True
but WellTyped 1 = False for `.asc .type .type`.

**Impact:** The entire normalize_stable approach to the lam case (pursued across
sessions 211841 and 220210) was a dead end. The 5 proved cases of normalize_stable
are correct, but the var y≠x and app cases are not just "hard" — they're impossible.

**Recommended next step:** See PROGRESS.md for Option B (env-based CBV evaluator
without normalization under binders) and Option C (accept current state).

---

## 2026-03-31 ochre-lean-20260331-160108: concEvalS — substitution-based concrete evaluator (IMPLEMENTED)

**Decision:** Added `concEvalS` as a second concrete evaluator alongside the existing
`concEval`. `concEvalS` uses substitution and treats lambdas as values (no normalization
under binders). It is the "real" runtime semantics per spec §4.1. `concEval` is kept
as a proof artifact for soundness.

**Why the previous proposal ("just stop normalizing in concEval") doesn't work:**

The env-based `concEval` REQUIRES normalization under binders. Here's why:

When `concEval env (lam x dom body)` returns the raw lambda, the body has
free variables (like `var "y"`) that were resolved through the environment.
Without normalization, these variables remain unresolved. When the lambda is
later applied in a DIFFERENT env context (e.g., after being returned from a
function), the free variables are looked up in the wrong env or not found at all.

Example: `(λy. λx. x + y) 5 3`
1. Evaluate `(λy. λx. x+y) 5`: app of lam, evaluate body `λx. x+y` with (y,5)::γ
2. Without normalization: return `lam x dom (x + y)` — var "y" is NOT resolved
3. Apply to 3: evaluate `x + y` with (x,3)::γ' — where is y? NOT in scope!

With normalization (current): step 2 evaluates body → `lam x dom (x + 5)` → y resolved.
With substitution (concEvalS): step 1 uses subst not env → body becomes `λx. x + 5` → y resolved.

So the three viable approaches are:
1. **Closures** — lambda values carry their environment. Requires changing Expr or
   adding a Value type. Major refactor of Subtype' and all proofs.
2. **Substitution** — beta-reduction uses `body.subst x arg` not env extension.
   Loses the "same body expression" property that makes soundness proof easy.
3. **Extensional soundness** — prove soundness as a logical relation (lambdas are
   related when applied to related args, not when compared syntactically).

Approach 2 was chosen as a stepping stone. `concEvalS` demonstrates that concrete
recursive fix WORKS. Proving its soundness is left for future sessions.

**Thunking convention for recursion:**
Even `concEvalS` is call-by-value: arguments are evaluated before being passed.
Church-encoded branching `(isZero n) R base_case recursive_case` evaluates BOTH
branches. The fix: wrap branches in thunks (lambdas that delay evaluation):
`(isZero n) (Unit→R) (λ_.base) (λ_.rec) unit`. The unused thunk is a value
(not evaluated). The selected thunk is applied to unit, triggering evaluation.

**Limitation:** `concEvalS` returns un-normalized lambdas, so `succ 2` is NOT
syntactically equal to `three'`. It's extensionally correct (applying to X,z,s
gives the same result) but structurally different. Tests should check behavior
(apply to args) not normal forms.

**What this unblocks:**
- Concrete recursive fix: `toZeroThunked 3 = 0` ✓ (Tests.lean)
- Composition: `toZeroThunked (add 2 1) = 0` ✓ (church numerals as args)
- Future: `appendArrays`, `mapArray`, any recursive function with thunked branches

**Soundness path forward:**
To prove `concEvalS` sound w.r.t. `absEval`, the most promising approach is a
logical-relations style proof. Define `Sound n v τ` as:
- For non-lam: `SubtypeTrans v τ`
- For lam-lam: when applied to Sound arguments, the results are Sound

This decouples the lam case (no need to compare bodies syntactically) while
preserving compositionality at application sites. Estimated effort: 200-300 lines,
primarily in defining the Sound relation and proving the app case.

---

## 2026-03-31 ochre-lean-20260331-140739: Stop normalizing under binders in concEval (SUPERSEDED)

**Status:** SUPERSEDED by the concEvalS decision above. The analysis below is
kept for historical reference but the approach was found to be incomplete.

**Original decision:** `concEval` should treat `λ(x: τ). e` as a value — return it as-is
without reducing the body. `absEval` should continue normalizing under binders
(needed for precision like `succ 2 = 3`).

**Why this doesn't work (discovered session ochre-lean-20260331-160108):**
The env-based evaluator requires normalization to resolve free variables. Without
it, lambda bodies have dangling variable references. See the entry above for the
full analysis.

**Original analysis (for reference):**
The current `concEval` normalizes lambda bodies eagerly. This breaks
Church-encoded branching: both branches are eagerly normalized, causing recursive
branches to diverge even when not taken. Demonstrated by `toZero 1 = none` in
Tests.lean.

**Alternatives considered (original):**
- Add laziness annotations to Church encodings. Ad-hoc, not compositional.
- Add a `thunk`/`delay` construct. Adds syntax for what should be default behavior.
- Keep normalizing but add fuel-aware recursion limits. Doesn't fix the
  fundamental problem (both branches are entered).

---

## 2026-03-31 och-agent-20260331-124544: Remove trans from Subtype' (IMPLEMENTED)

**Decision:** Removed `trans` from `Subtype'` and created `SubtypeTrans` as the
transitive closure.

**Why:** Lambda inversion (`Subtype' (lam x d b₂) (lam x d b₁) → Subtype' b₂ b₁`)
is needed for the app case of monotonicity. With `trans` in `Subtype'`, inversion
fails because `lam ⊑ lam` could go through any intermediate term. Without `trans`,
the only ways to prove `lam ⊑ lam` are `refl` and `lam_body`, both of which give
`body₂ ⊑ body₁`.

**Result:** The lam-lam app case of monotonicity is now proven! This was previously
impossible. The generalized `absEval_mono` takes `Subtype' e₂ e₁` (related exprs)
and `EnvSub Γ₂ Γ₁` (related envs), proving the result for both same-expression
and different-expression cases.

**Implications:**
- `SubtypeTrans` is used in soundness (asc case chains IH with well-typedness via trans)
- `Subtype'` is used in monotonicity (no trans = clean inversion)
- Lambda inversion lemmas `lam_inv` and `lam_rhs_shape` are proven in Subtyping.lean
- `SubtypeTrans.lam_body` lifts the body relation through the transitive closure

---

## 2026-03-31 och-agent-20260331-124544: Generalized monotonicity (absEval_mono)

**Decision:** Monotonicity is proven as a generalized theorem `absEval_mono` that
takes `Subtype' e₂ e₁` (related expressions) in addition to `EnvSub Γ₂ Γ₁`.
Standard monotonicity is the corollary with `Subtype'.refl`.

**Why:** In the app case, evaluating the same function `f` in different environments
produces different normalized lambdas `lam x dom body₁` and `lam x dom body₂` (body₁
is normalized under Γ₁, body₂ under Γ₂). The IH gives `Subtype' body₂ body₁` via
lambda inversion. The recursive call on the beta-reduced body then needs `Subtype' body₂ body₁`
as input — not just `Subtype'.refl`.

**Alternatives considered:**
- Standard monotonicity (same expr, different envs): insufficient because the
  recursive call in the app case involves different bodies.
- Substitution-based monotonicity: would need a substitution-Subtype interaction
  lemma, which is complex and doesn't fit the closure-based evaluator.

**Implications:** The proof is by induction on fuel, with `match` on the
`Subtype' e₂ e₁` proof at each step. Cases: refl (5 expression sub-cases),
top (trivial), lam_body (IH on bodies), app_cong (IH on subexpressions).

---

## 2026-03-31 och-agent-20260331-120514: Normalize under binders in absEval

**Decision:** absEval normalizes lambda bodies under the binder (with bound
variable as neutral), rather than returning the lambda as-is.

**Why:** This is necessary for `succ 2 = 3`. After substituting `two'` for `n`
in succ's body, the resulting lambda contains unreduced `two' X z s` inside.
Normalizing under binders (with X, z, s as neutral) reduces this to `s(s(s z))`,
yielding the precise Church numeral `three'`.

**Alternatives considered:**
- Return lambda as-is (spec §4.2 suggests this). Fails `succ 2 = 3` test.
- Only normalize at application time. Same effect for applied functions, but
  standalone lambdas would have un-normalized bodies.

**Implications:** Affects the monotonicity proof: the lambda case needs
`lam_body` rule and IH on the body with extended env. Currently works.

---

## 2026-03-31 och-agent-20260331-120514: Do NOT normalize domains in absEval

**Decision:** Lambda domains are kept as-is (not normalized) in absEval output.

**Why:** Normalizing domains would make them depend on the environment, breaking
monotonicity. If domain is `var T` and T maps to different types in Γ₁ vs Γ₂,
normalized domains would differ, and function subtyping's contravariant domain
check would fail even though the source code is identical.

**Alternatives considered:**
- Normalize domains. Simpler but breaks monotonicity structurally.

**Implications:** The lam_body Subtype' rule requires same domain in both sides.
Non-normalized domains ensure this invariant.

---

## 2026-03-31 och-agent-20260331-120514: Pointwise subCheck with inferType

**Decision:** subCheckNF works by entering lambda bodies pointwise (like function
subtyping: contravariant domains, covariant bodies) and uses inferType to handle
the leaf case where neutral terms need type comparison.

**Why:** This is what makes `true ⊑ Bool` and `3 ⊑ Nat` work. At the leaf,
`var "t" ⊑ var "X"` succeeds because t's declared type is X (from the lambda
domain annotation), and X ⊑ X by reflexivity.

**Alternatives considered:**
- Pure syntactic comparison (fails for non-trivial subtyping)
- Evaluation-based (normalize both and compare — doesn't handle the quantified
  "for all x ⊑ dom" check)

**Implications:** subCheckNF needs a typing context to track declared domains.
This context is local to subCheckNF (not threaded through absEval).

---

## 2026-03-31 och-agent-20260331-120514: Make concEval parallel to absEval

**Decision:** concEval now takes an environment and normalizes under binders,
making it structurally identical to absEval except at ascription (concEval takes
lhs, absEval takes rhs).

**Why:** This makes the soundness proof a straightforward induction. For all
cases except ascription, the proof structure is: both evaluators do the same
thing → use IH. For ascription, the WellTyped precondition provides the bridge.

**Alternatives considered:**
- Keep concEval as-is (no env, no normalization). Soundness statement would need
  a different formulation and couldn't handle open terms.
- Separate soundness for closed terms only. Limits usefulness.

**Implications:** Concrete eval tests need env argument (use neutral bindings for
free variables). The conceptual model is now: compilation = evaluation in abstract
mode, runtime = evaluation in concrete mode, same env structure.

---

## 2026-03-31 och-agent-20260331-120514: WellTyped precondition for soundness

**Decision:** Soundness requires a WellTyped precondition that all ascriptions
encountered during evaluation are valid (term's abstract type ⊑ annotation type).

**Why:** Without this, `(true : Nat)` would pass absEval (returns Nat) but
concEval returns true, and true ⊑ Nat is false. The spec (§4.2.4) says the
interpreter "must verify e ⊑ τ" — this precondition captures that.

**Alternatives considered:**
- Build the check into absEval. Requires threading a subcheck context through
  absEval (needs domain info for inferType). Significant refactor.
- Prove soundness without precondition. Impossible for the asc case.

**Implications:** The WellTyped predicate mirrors absEval's structure. For the
app case, it requires well-typedness of the beta-reduced body (recursive).
Future work could move the check into absEval itself.

---

## 2026-03-31 och-agent-20260331-120514: Closure-based evaluator (IMPLEMENTED)

**Decision:** Changed absEval and concEval app cases from substitution-based
(`absEval Γ (body.subst x aVal)`) to environment-based (`absEval ((x, aVal) :: Γ) body`).

**Why:** With substitution, the two sides of monotonicity/soundness proofs work
with DIFFERENT expressions (body₁.subst x v₁ vs body₂.subst x v₂), and the IH
requires the same expression. With env extension, both sides evaluate the same
`body` in different envs, making the IH applicable (after solving the inversion
issue — see next decision).

**Result:** All 25+ tests pass with the closure-based approach. The normalized
body has no free references to env variables (they were resolved during
normalization under binders), so only the `(x, aVal)` binding matters.

**Alternatives considered:** See previous entry.

**Implications:** The app case proof now only needs lambda inversion (extracting
body₂ ⊑ body₁ from lam ⊑ lam). This is blocked by trans in Subtype' — see
next decision.

---

## 2026-03-31 och-agent-20260331-120514: Remove trans from Subtype' (RECOMMENDED)

**Decision:** (NOT YET IMPLEMENTED) trans should be removed from the Subtype'
inductive and placed in a separate SubtypeTrans wrapper.

**Why:** Lambda inversion (`Subtype' (lam x dom b₂) (lam x dom b₁) → Subtype' b₂ b₁`)
is needed for the app case of monotonicity. With trans in Subtype', inversion fails
because `lam ⊑ lam` could be proved via `lam ⊑ mid ⊑ lam` where `mid` is any term.
Without trans, the only ways to prove `lam ⊑ lam` are `refl` and `lam_body`, both
of which give us `body₂ ⊑ body₁`.

**Implementation plan:**
1. Remove `trans` from `Subtype'`
2. Define `SubtypeTrans` as transitive closure of `Subtype'`
3. `EnvSub` and `EnvConsistent` can use either (choose based on proof needs)
4. Soundness uses `SubtypeTrans` (needs trans for asc case)
5. Monotonicity produces `Subtype'` (no trans, enables lambda inversion)
6. Generalize monotonicity to `absEval_mono`: takes `Subtype' e₂ e₁` + `EnvSub Γ₂ Γ₁`
   as inputs, produces `Subtype' τ₂ τ₁`. Standard monotonicity is the corollary
   with `Subtype'.refl`.

**Why this unblocks everything:**
The lam-lam app case of monotonicity becomes:
- IH gives: `lam x dom body₂ ⊑ lam x dom body₁` (Subtype', no trans)
- Invert: `body₂ ⊑ body₁` ✓
- Extended envs: `((x, a₂) :: Γ₂) ⊑ ((x, a₁) :: Γ₁)` ✓
- Generalized IH: `τ₂ ⊑ τ₁` ✓

**Alternatives considered:**
- Induction on Subtype' proof to prove inversion. Fails at trans case.
- Strong monotonicity with Subtype' (including trans). Trans case requires
  intermediate term to evaluate, which isn't guaranteed.
- Mutual induction with absEval_subtype_input lemma. Also circular at trans.

**Implications:** subCheck (the Bool decision procedure) doesn't use Subtype',
so tests are unaffected. Only the proof-level Subtype' changes.
