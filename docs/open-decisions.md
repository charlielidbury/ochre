# Open Decisions

Questions for the user when they're back. In the meantime, agents proceed with best judgment.

## Q5 (CRITICAL): How to handle the "principal type" obstruction?

**Status:** Multiple agents have confirmed this is a fundamental wall. ANY rule
that puts a substituted term on the RHS of subtyping (BetaR, AppR, Mu-R, IotaR)
breaks the cut-formula transitivity proof. The substituted body's complexity can
be arbitrarily larger than the original cut formula because var-0 can appear
multiple times in body, duplicating arg.

**The two architectural options:**

**Option A: Canonical synthesis for [App]**
Replace the existential `(D, R)` in [App] with a deterministic `principal(f)`
function that returns f's CANONICAL function type. For literal lambdas, this is
trivial: `principal(λD.body) = (D, body)`. For variables, look up Γ. For
applications, recurse.

The idea: with no existential, transitivity composes deterministically. The
"different paths pick different witnesses" problem disappears.

**Cost:** Requires re-proving everything for the new [App] rule. The principal
type might not exist for some terms (e.g., applications of variables of type ⊤).
Need to handle the partial case carefully.

**Option B: Semantic proof via logical relations**
Define a Kripke model where types are interpreted as sets of values, and prove
soundness via the semantic interpretation. Avoid the syntactic cut-elimination
proof entirely.

**Cost:** Substantial Lean machinery. Step-indexing or coinductive types needed
for self-types.

**Default decision (no user input):** Try Option A first because it's more
incremental. If it doesn't work, fall back to Option B.



## Q1: After [BetaR] lands, should it support variable-headed apps too?

[BetaR] (restricted) only fires when the function is a literal lambda. Variable-headed
apps like `t ⊑ P dBool` (where P is a parameter) on the RHS stay opaque.

This means self-types with variables in function position still don't work.

**Options:**
- A) Leave it. Variable-headed apps are rare in practice.
- B) Allow [Var]-style unfolding on the RHS (would need careful soundness check).
- C) Use the seen-set algorithm only for variable-headed apps.

**Default decision (no user input):** A. Leave it. Variable-headed RHS apps are
the same fundamental cycle problem we've been trying to solve.

## Q2: Should we keep MuTests, DBool, DNat from the old branch?

When we reset main to b5fcfa0, we removed μ-related test files. These had nice
test cases that document the self-type problem.

**Default decision:** Leave them removed. They were testing things the current
system doesn't support. Re-add when we have a working self-type solution.

## Q3: How do we handle the constructive checker's relationship to inductive Sub
when we add new rules?

Currently `subCheck_sound : check Γ a b = true → Sub Γ a b`. Adding [BetaR]
to Sub means we need to update subCheck to handle it AND prove the new soundness case.

**Default decision:** Update subCheck to handle [BetaR] explicitly. The soundness
case is straightforward — produce a Sub.betaR derivation.

## Q4: For the precise interpretation, which formulation should we commit to?

**Finding (research-precise agent):** The circularity breaker is VALUE SUBSTITUTION,
not definitional equality. Cedille-style `[IotaIntro]` substitutes the value being
checked into the self-type body, collapsing recursive goals to Refl.

**This handles COVARIANT self-types** (where self appears only in covariant positions).
**Contravariant self-references still produce productive cycles** (like dBool where
self is in the lambda domain `P : self → ⊤`).

**Status of dtrue ⊑ dBool:** Needs BOTH `[IotaIntro]` and `[IotaElim]`. The elim
rule has a circular well-typedness side condition that's the main open question.

**Files:** `Och/Simple/Precise.lean` and `Och/Simple/DefEq.lean` on research-precise
branch. 2 documented sorrys (one oracle, one open case).

**Default decision:** Pursue the IotaIntro approach for covariant self-types. The
contravariant case (dBool) is still open and might genuinely require coinduction.
Worth implementing IotaIntro fully for the cases it handles.
