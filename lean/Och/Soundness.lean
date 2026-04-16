import Och.Syntax
import Och.Eval
import Och.Subtyping

/-!
# Soundness (Phase 2 — intentionally empty)

The soundness proof is deferred to Phase 2 (see `AGENT_PROMPT.md`). Agents
in Phase 1 must not work on proving anything here; Phase 1 is about making
the abstract interpretation handle the test suite correctly.

The prior attempt (step-indexed value-type compatibility, `VCompat`) has
been removed. It grew a disjunct per term shape and per subtyping rule —
fragile under language changes, and each new constructor required
rewriting the relation. When Phase 2 begins, the first task is to choose
a proof architecture, not to extend what was here. See `SUGGESTIONS.md`
for some candidate approaches and the open questions they each raise.

Until then this file is intentionally empty so that agents do not
inherit a presumed target.
-/
