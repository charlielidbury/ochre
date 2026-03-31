# Decision Log

Record significant design decisions here. Each entry should explain WHAT was
decided, WHY, and what alternatives were considered.

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

## 2026-03-31 och-agent-20260331-120514: Closure-based evaluator recommended

**Decision:** (NOT YET IMPLEMENTED) The substitution-based evaluator should be
redesigned to use closures/environments for beta-reduction.

**Why:** The app case in both Soundness and Monotonicity is unprovable with the
current substitution-based approach. After beta-reduction, the two sides have
DIFFERENT expressions (body₁.subst x v₁ vs body₂.subst x v₂), and the IH
requires the SAME expression. A closure-based evaluator would extend the env
instead of substituting, keeping the same body expression in both sides.

**Alternatives considered:**
- Substitution monotonicity lemma. Hard to state and prove.
- Logical relations / step-indexed argument. Very complex.
- Beta-subtyping rules. Helps with mixed cases but not the core issue.

**Implications:** This is the most impactful change for future agents. Requires:
1. Change app case of absEval: `absEval ((x, aVal) :: Γ) body` instead of
   `absEval Γ (body.subst x aVal)`
2. Prove that the new evaluator gives equivalent results (tests still pass)
3. The monotonicity and soundness proofs should then go through for the app case
4. Need to handle the interaction between env-based eval and normalization
   under binders (body was already normalized, so re-evaluating in new env
   might produce different results)
