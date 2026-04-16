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

### ochre-20260416-182337 (2026-04-16)

**Closed 18 DBool concEval markers via native_decide.**

Previous agent (175614) flagged these as defensively sorry'd after the
e08bce9 encoding switch but likely closable. Verified all pass:

- `dtrue P t f = t`, `dfalse P t f = f` (2)
- `dbcase dtrue/dfalse` (2)
- `dtrue/dfalse depMotive zero_ true_` (2)
- `not dtrue/dfalse` identities (2)
- `and` table (4)
- Negative `≠` checks: dtrue/dfalse selects right arg, not-involution,
  and-asymmetry (6)

Runtime reduction through `fix`/`ι` wrappers works correctly: fix unfolds
at head-of-app, ι unfolds its self-ref via body.subst 0 iota, then the
lambdas beta-reduce normally. concEval's implementation at Eval.lean
matches the whiteboard.

**Did NOT close DBool subtype markers (lines 145, 148, 154).** The
positive `dtrue ⊑ dBool` and `dfalse ⊑ dBool` DO close via native_decide
under the current algorithm, but via the SAME unsound seen-set cycle
that makes the negative `dBool ⊑ dtrue` spuriously return .ok true.
Closing the positives would hide that the algorithm cannot distinguish
them and suggest the wall is only about the negative case. Leaving all
three sorry'd keeps the picture honest.

Detailed cycle trace (for the next agent attempting the wall):

Both sides are `fix B:Type. ι self:B. body_X`. For either direction,
the algorithm:
1. `_, .fix` rule unfolds RHS → `a ⊑ ι self:(outer_fix). body_X_substd`.
2. `_, .iota` rule does iotaIntro → `a ⊑ body_X_substd[self := a]` which
   simplifies to a lam.
3. `.fix, _` on LHS: ann_path (Type ⊑ lam) fails, unfold_path produces
   `ι self:(LHS_fix). body_LHS_substd` ⊑ lam.
4. `.iota, _` on that iota widens to its ann (= LHS_fix), checks
   `LHS_fix ⊑ lam` — now `(LHS_fix, lam)` is in seen from step 3's seen'.
5. `.fix, _` on LHS_fix: ann_path again fails, unfold_path reproduces
   `ι self:(LHS_fix). body_LHS_substd` ⊑ lam.
6. Pattern `(ι_LHS_substd, lam)` was added to seen at step 4. Seen
   short-circuits → `.ok true`.

The cycle closure at step 6 happens REGARDLESS of whether the lambdas
would actually structurally match. If we could force structural lam
descent (iotaIntro-on-LHS, substituting LHS iota into its own body
before comparing to RHS lam), the negative case's `(P dfalse) ⊑ Type`
contravariant check on λf would fail (Type ⊑ neutral-app ≠ top), while
the positive case's `(P dfalse) ⊑ Type` is in the other direction via
`top` and succeeds. But LHS-iota-self-unfolding (`ι A. B ⊑ c ←
B[0 := ι A. B] ⊑ c`) is only sound when B is monotone in self, and
dBool's body has self in invariant position (`P self`).

Options for the next agent:
(a) Productivity-aware seen set: only close cycles when structural
    progress has occurred between encounters. Distinguishes "cycle via
    widening" from "cycle via structural descent."
(b) Eager structural descent when shapes are compatible: when `_, .iota`
    or `_, .fix` fires and LHS also has the matching outer shape,
    try structural iota_body/fix_body first before iotaIntro/unfold.
(c) A DBool encoding change that makes the negative case fail
    structurally (at a shallower depth than the unsound cycle closes).
(d) Coinductive Subtype' reformulation + algorithm restricted to GFP.

`lake build` passes. Marker count: TODO[mega-loop] comments 38 → 27.
Sorry count dropped by 18.

---

### ochre-20260416-175614 (2026-04-16)

**Removed unsound RHS `fix_ann` rule; closed 3 transitivity markers.**

The rule `a ⊑ fix A. body  ←  a ⊑ A` (ann_path in `_, .fix` case of
`subCheckNF`, constructor `fix_ann` in `Subtype'`) was unsound: `fix A. body`
is narrower than its annotation A (values must additionally unfold-match the
body), so A-membership doesn't imply fix-membership. Concrete counterexample
found by exhaustive search on smallExprs:

  a = λx:Type. λy:Type. y
  b = fix x:(Type→Type). λy:Type. y
  c = ι x:Type. λy:Type. y

Under the old rules: a⊑b via fix_ann (a⊑Type→Type by top-on-body),
b⊑c via unfoldFixR, but a⊑c correctly fails. **Transitivity violation.**
Three identical-shape triples existed in the smallExprs table; similar ones
in stdExprs/edgeExprs. After removal, all three `TODO[mega-loop]`
transitivity markers in `Och/Tests.lean` (lines 130, 150, 171) now close
via `native_decide`.

Files: `Och/Eval.lean` (subCheckNF RHS fix case simplified to unfold-only;
neutralType still handles ann-based widening without polluting the seen
memo), `Och/Subtyping.lean` (drop `fix_ann` constructor; unfold-only on RHS),
`Och/Tests.lean` (3 markers closed with native_decide, comments updated to
explain the fix).

**Did NOT fix the deeper DBool subtyping wall.** The negative test
`subCheck 50 dBool dtrue = .ok false` still spuriously returns `.ok true`.
Trace: unfold_fix_R + iotaIntro reduces the goal to `dBool ⊑ lam_t'`, which
cycles through `.iota, _` (LHS ann widening on dBool's iota) + `.fix, _`
(LHS unfold) back to the same pair and closes via seen memoization. This
same cycle is ALSO what makes the positive `dtrue ⊑ dBool` close, so
removing LHS ann-widening from the main flow (tested in this session)
breaks positive cases without fixing the negative. Distinguishing the two
requires either (a) a new semantic mechanism in the checker that doesn't
just rely on syntactic cycle detection, or (b) a change to the DBool
encoding so the negative case fails structurally. Both are research-level.
Matches graveyard: "Self-types (dtrue ⊑ dBool) are inherently circular —
need cycle detection OR coinductive Sub OR step-indexed LR".

**Incidental finding (not acted on):** the DBool concEval markers at
lines 116, 119, 126, 127, 134, 135, 161, 162, 165-168, 175-184 are all
closable via `native_decide` (they were defensively sorry'd by the
e08bce9 encoding switch, not genuinely obstructed). Left for a follow-up
to keep this commit focused on the substantive soundness fix.

`lake build` passes. Marker count: 41 → 38 (Tests.lean: 5 → 2).

---

### phase1-array-dnat-swap (2026-04-14)

**Encoding swap, not a marker close.** Replaced Church-Nat-indexed Array_
with dNat-indexed Array_. The transitional `Array_dnat` is gone; the name
`Array_` now refers to the dNat version. `Vec`, `mkVec`, `appendVec`,
`appendArrays` all moved to dNat indices. `Tests.lean` §6.2 abstract-vec
tests ported. Added `dadd` in Std/Array.lean (was no dNat addition before).

**Test disposition.** Most Vec/Array tests that previously passed via
`native_decide` under Church-Nat are now sorry'd with TODO[mega-loop]
markers. The root obstruction is consistent: the motive
`λn:dNat. λarr:(Array_ n Nat_). _` has a binder whose body
`Array_ n Nat_` evaluates by unfolding Array_'s outer `fix` and then
running DNat's eliminator on the bvar `n`, which is stuck. The old
Church-Nat version did the analogous stuck reduction but absEval silently
admitted it; under the new strict absEval those tests fail honestly.

**Specific flips of intent:**
- `appendArrays` type-check test flipped from `≠ .ok true` to `= .ok true`
  (sorry'd). Under Church-Nat the negative assertion was expressing the
  encoding's limitation; the whole point of dNat indexing is that the
  positive assertion should hold once the mega-loop is closed.
- `appendVec` type-check similarly flipped. `appendVec_wrong` stays as
  `≠ .ok true` — it's a negative assertion that survives the swap.

**Live tests kept:**
- concEval tests on `appendArrays [1,2] [3] = [1,2,3]` in Std/Array.lean.
- isZero-checks, disZero computation tests in Std/DNat.lean (unchanged).
- All non-Vec/Array integration tests in Tests.lean.

**Nothing was trivialised.** No test was swapped from a succ-case to a
zero-case to dodge the reduction (e.g. `Array_ done_ T` stayed as
`Array_ done_ T`, not `Array_ dzero T`).

**Nothing was deleted.** Every Church-Nat test has a dNat analogue at
parity.

**Sorry count added:** ~17 new TODO[mega-loop] markers
(6 in Std/Array.lean, 12 in Std/Vec.lean, 2 in Och/Tests.lean).

**Downstream fallout noticed:** none. `Std/Sigma.lean`, `Std/Pair.lean`
etc. don't reference Array_ or Vec. `Simple/` is untouched (directive).

**Next agent:** the central obstruction is DNat's Scott-style eliminator
on a neutral bvar. If the eliminator were Church-with-ι (per
`docs/research/self-types-for-och.md`), `Array_ n T` would normalize
under an abstract n binder via dependent elimination. That's a
structural DNat redesign — orthogonal to, but unblocking, this swap.
`lake build` passes.
