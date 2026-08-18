# Overnight campaign review guide — packed invariants under borrows

**For the morning review, 2026-08-18.** The mandate was `14-packed-borrows.md`: attack the GetMut wall on a branch, sub-agents doing the major work, review guide if something lands. Something landed — **two kernel fixes merged to main** (both soundness/capability class, under the session's objective-merge delegation), and the wall is reduced from "conversion cannot cross this" to **two pinned design questions with in-tree acceptance probes**. Nothing design-flavored merged; the flagship branches stay parked.

## What merged, in order (each an ff of a verified branch; revert = revert the range)

1. **`77feff6a..a4ea8d44` + `..99b59678` — opaque fill** (branch `opaque-fill`). When the exit audit re-types a payload containing an ESCAPING mutable borrow, the lent place is filled with a fresh σ at the *issued borrow's* owed type, instead of its current value — so the pack must type for *every* value the caller could later write. Three-line kernel change (`spliceInFlight` + the widened `issued` plumbing, Machine.lean), 651-line test module (`Tests/OpaqueFill.lean`). **It closes four live unsoundness holes that existed on main independent of the hashmap** — escaping borrows onto a hashed key cell, an array extent, a Σ0-pinned cell, and a cell a later runtime binder's type needs, each previously accepted and each exploitable (`escKeyExploit` is the end-to-end witness: a checked program whose runtime output provably fails its own declared type). One needle edit ledgered (`siblingBadWrite`, σ9→σ10).
2. **`99b59678..4b6d332e` — the audit folds rejoined carves** (branch `audit-fold-segments`). One site: `subsKnowledge` (Machine.lean:1519) now takes ¶1.3's ⇝ bridge (`arrFoldDeep`) before contributing a value to a dependent tail's typing context. Its fall-through comment had claimed state-holding nodes were unreachable there — true of `buildResult`, false of `checkFields`. Typing-time view only; the M32-R1 `§segs` refusal is untouched and asserted so. The counterfactual found the fix also silently protects `ArraySort`'s chain (three assertions co-depend on the exit-snapshot fold). Test module `Tests/AuditFold.lean`; perf-neutral with a fast path.
3. **`4b6d332e..ec87eece` — the corrected diagnosis and the nine-flip ledger** (branch `leading-slice-probe`, test-file only). The residual was mischaracterized twice ("leading opaque slice breaks the fold") and pinned correctly on the third measurement: the fill's σ is erased iff the invariant's fold *reduces past* the lent element, which needs every earlier element concrete. The refusal at carve-index ≥ 1 is **correct, not incomplete tooling** — nothing has told the checker the invariant ignores that cell.

## The one composition fact to internalize (`gmKey2`)

The two kernel fixes were independent in their diffs and **not independent in their consequences**: the fold fix alone would have made partially-carved packs re-typable *and thereby made an escaping KEY borrow into one of them type* — opening a fresh instance of exactly the hole the fill closes. Landing both, in either order, is sound; landing the fold alone would not have been. `OpaqueFill.lean`'s ledger pins it: seven flips the rule buys (each previously green and unsound), two it costs (escaping value borrows at carve index ≥ 1 — safe, refused, the measured price of conservatism).

## What to review, concretely

- `Machine.lean`: the `spliceInFlight` issued-arm mint (granularity comment cites `layer1Val` as what the wrong granularity does) and the `subsKnowledge` two-liner. Both carry their reasoning at the site.
- `Tests/OpaqueFill.lean` (50 assertions): §2 the four holes; §3 the exploit witness in three-part form; §7 the remaining walls, now the campaign's honest residue. The module docstring's counterfactuals have exact red-line counts.
- `Tests/AuditFold.lean` (§iii's two negative controls red for two *different* reasons is the part worth a careful read).
- The review question I'd ask of the fill: is "fresh σ at the issued borrow's owed type" the right universal quantifier, or should it eventually be the *pin* from `12-`'s design (which would also buy functional precision)? The landed rule is the safety floor; it forecloses nothing.

## The two remaining design questions (pinned, not attempted — they are yours)

1. **A fold that can begin at a symbolic prefix** (`OpaqueFill.lean` §7.5; probes `gmValMid`/`gmValLast` red, `gmVal2`/`gmVal3` green, `midSplit3` as the exact A/B). This is on the real `GetMut`'s critical path — the flagship's slot index is symbolic, so its carve is always mid-shaped. What's missing is a *theorem about `arrRec`* (an invariant insensitive to positions its fold hasn't reached), not a conversion: candidate shapes are a `SlotsFrom`-style fold-from-index in the spec layer, or the `12-` debts design giving the callee a place to *prove* invariant-survival across its carve.
2. **`endGroup`'s component-level re-mint** (§7.4; `layer1`/`layer1Val` red, `layer1Ctl` green). Passing a component of a packed container to any function by `&mut` orphans the packed proof at group end, escaping borrow or not. This is opacity doctrine territory (§6.2 is load-bearing for the carve reset), so it wants a design ruling, not a patch.

Both questions now have three live customers (the flagship's GetMut, the two-call fuel wall from the opus run, and these probes), and both point at `12-design-borrow-refounding.md` — which also still awaits your D-list review, with its stage 5 measured in advance by the audit-fix lane's findings.

## Method notes the campaign paid for (the probe lane's own words, kept because they generalize)

- The costliest failure mode was not missing data: it was **carrying a hypothesis past the point where one's own measurement had refuted it** — `midSplit3` sat in the lane's report proving the spine matched, and it took another agent's hint to make its author re-read it. The exclusion probes (`midCarveEscN`, `frontCarveEscN`) now pin the corrected mechanism in-tree so the refuted reading cannot be re-proposed.
- The `gmKey2` composition hole existed **only in the intersection of two lanes** — one suite had no escaping borrows, the other no partially-carved packs that typed — so neither lane could have found it alone. A cross-lane ledger run before merging two kernel changes is cheap and finds this class without anyone needing to think of it.
- Sha-ancestry after a rebase is not a merge test: `merge-base --is-ancestor <old-tip> main` answers NO for work that IS in main under a new sha. Verify by file contents (the assertion is byte-identical in main), not by ancestry.

## Not merged, awaiting you

The three flagship branches (`hm-flagship-opus` @ 9c288065, `-sonnet` @ 2dcfa82f, `-fable` @ 97be424a — fable's final executing build confirmed green, every box closed); the `12-` design doc (uncommitted in `dllbc/docs/`, with the overnight addendum); the fifth-invariant-clause spec amendment to `13-` (NodupB, forced by the fixed specs, matches Aeneas' `slot_t_inv` — recommend ratifying); and the natCase/listCase design item from the eager-evaluation lane (`09-nbe.md` §9 item 10). Timeline, verification transcripts, and per-lane reports are in this session's log; every branch named above is pushed.
