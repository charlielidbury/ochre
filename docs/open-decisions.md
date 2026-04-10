# Open Decisions

Questions for the user when they're back. In the meantime, agents proceed with best judgment.

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

The research-precise agent is exploring multiple options. After it reports back,
we'll have a recommendation.

**Default decision (no user input):** Pick whichever works experimentally. Document
the others in the graveyard.
