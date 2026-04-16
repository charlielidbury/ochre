# Progress

## Current state (2026-04-16)

Phase 1 active. Full Och was just restructured: the bundled `μ` binder has
been split into separate `ι` (self-type) and `fix` (recursive type)
constructors. `lake build` compiles. Simple Och (`lean/Och/Simple/`) is
untouched and remains the proven-sound metatheory reference.

`dtrue ⊑ dBool` does not currently pass under the new rule set. This is
expected — it's the central aspirational test. See AGENT_PROMPT.md for
rules of engagement.

## Open `TODO[mega-loop]` markers

Agents should run `grep -rn "TODO\[mega-loop\]" lean/` for the current list.
At time of writing there are 11 markers, spanning:

- Dependent-intro tests (`dtrue ⊑ dBool`, `dzero ⊑ dNat`, etc.)
- Negative-check re-verifications
- Array-over-DNat smoke tests
- Transitivity exhaustive checks

## Session log

Agents: append a brief session summary below. What you changed, what you
tried, what blocked you, what the next agent needs to know. Be specific —
file names, markers closed, definitions changed.

---

(no sessions yet under the new arc)
