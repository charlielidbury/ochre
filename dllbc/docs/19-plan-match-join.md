# Plan v2: match environment unification — join always

**The user's request, in substance.** Match branches are checked with increased knowledge (in a `Cons` branch the scrutinee IS a Cons node — dependent elimination), but there is no join after a match, so code after a statement-position match is analysed once per path: N sequential matches cost 2^N walks. Measured: 1/2/3/6 sequential two-branch symbolic matches produce 3/5/9/65 paths and 27/64/138/1205 ms of checker time. **Constraints, from review of v1: the user experience must not get worse — no annotation may be required; no change to the `Term` datastructure; syntax stays the same; only the analysis differs.**

**The design, in one sentence.** *Every statement-position match is checked joined: the arms are checked terminally under their refinements as today, and the continuation is then checked ONCE from the pre-split environment, with slots on which the arms agree passed through losslessly and slots on which they disagree re-minted as fresh σs at conservatively synthesized types; where no such type exists the program is rejected with an error that names the disagreement — there is no fork.*

**Version history, so nobody re-litigates it.** v1 (branch `match-join` @ `a5e1b7e9`) gated the join behind a declared motive (`let x : τ = match …`), which required a `Term.matchE` motive field, new syntax rows, and an annotation — all three now ruled out. A "join-first, fork-on-failure" middle ground was considered and rejected: the fork's only job would be to accept programs whose continuation exploits the correlation between a match result and its scrutinee, that class has zero representatives in the corpus, and the language's existing idiom (return the evidence: `Pair(True, e)` with M23 branch equations; or restructure into one match) covers it. Aeneas is the precedent read both ways: its symbolic execution duplicates continuations, but the paper itself calls that *"a strong restriction"* adopted for scoping, names the fix — *"computing a join … the merge problem"* — and is *"confident that this can be addressed systematically and predictably"* (§4.3, p. 116:22; future work §7, p. 116:28). The fork was scaffolding there too. What Aeneas argues is load-bearing is the per-branch strong update itself (*"refining into a constructor value is important for soundness"*, T-Match-Symbolic, p. 116:22–23) — which this design keeps unchanged: arms are still checked refined; only the seam changes.

---

## 1. Where the fork lives today (unchanged from v1's survey)

* `pushContinuations` (`Machine.lean:3860`) duplicates the continuation of `let x = match s {…}; k` and `seq (match…) k` into every arm behind `@armScope`/`@popArmL` seam markers.
* `exploreD`/`exploreMatch`/`exploreSymBranches` (`Machine.lean:6797–6928`) fork one path per branch on a symbolic scrutinee; `reorgScrut` classifies the scrutinee; `symOwnedSetup`/`symBorrowSetup` refine (`refineSym σ := Ctor(σ_fields)`) and bind branch equations.
* `auditPathsD` (`Boundary.lean:32`) audits every path at fn return — the continuation, copied into each arm, is audited once per path.
* The only statement-position symbolic matches in the suite are two purpose-built hover tests (`HoverSpans` §11, `PointSpans` §P3); the whole real corpus is tail-form — the fork's relational power is essentially unused.

## 2. What changes: the seam, and nothing before it

**No `Term` change.** `matchE` keeps its shape. v1's motive field and syntax rows are REMOVED; the branch must end with `Term` construction byte-identical to `origin/main`'s (the `Sugar` goldens and a direct `==` against pre-branch desugarings are the canary).

**The spine keeps its continuations.** `pushContinuations` no longer pushes a statement-position match's continuation into the arms for the checking walk. (Executing mode is untouched semantically: `runProgram`/`readR` select one arm on a concrete scrutinee; whether that keeps the pushed shape or generalizes v1's fork-shape rewrite rows in `readR`/`readRTail` is the implementer's call — the invariant is that executing-mode environments are bit-identical to today's, asserted by the differential.)

**Checking a statement-position match** (`let x = match s {…}; k` or `seq`):

1. Fence, reorganize (`reorgScrut`), exhaustiveness — as today. Concrete scrutinee: select the arm, continue — as today.
2. Symbolic scrutinee: snapshot the pre-split state `St₀`. Check each arm TERMINALLY under its refinement, exactly as today (branch equations, arm scopes, seam pops all unchanged). Collect each arm's exit `(Val × St)`.
3. **The join.** Continue once from `St₀`:
   * **Result slot `x`** and every other Ω slot, by the same ladder:
     a. all arms' exit values CONVERT → pass the value through unchanged (lossless — a match whose arms agree costs nothing in knowledge);
     b. values differ, but a type is synthesizable and common across arms once un-refined (constructor table for ctor values, `sctx` for σs, owed type for borrow payloads under the SAME loan) → bind a fresh σ at that type;
     c. for pair/pack results whose later components' types mention earlier components' values: attempt the dependent abstraction (replace the earlier component's per-arm value by the pack binder) before comparing — this is what lets `Pair(True, e)` / `Pair(False, e)` join at `Σ (b : Bool). Id Bool b …` without any annotation, and it is a HEURISTIC: where it fails, (d) applies;
     d. otherwise → **reject**, with an error naming the slot, the two disagreeing arms, and the remedy ("the arms disagree at the join; make the match return the disagreement as data/evidence, or restructure into one match");
   * ⊥ in any arm → ⊥ (conditional move = moved after);
   * differing loan/carve/scope STRUCTURE (different loans in a slot, a carve in one arm only, an arm ending a pre-existing loan the other keeps) → reject as in (d) — loan-set borrows are out of scope;
   * the scrutinee: owned — var consumed (⊥), σ_s stays citable in `sctx` (names the pre-split value); borrow — loan structure restored, payload re-minted fresh iff arms wrote (ladder rule (a) covers the untouched case);
   * per-arm knowledge and branch equations die at the seam. Obligations carry from `St₀` (loan-keyed; re-mint changes payloads, not loan identity).
4. Check `k` once. The fn-level audit runs on the single joined path.

**Soundness direction.** Join-accept ⊆ fork-accept: every per-path environment is an instance of the joined one, and checking is stable under instantiation — the property the seal and call boundary already trust, exercised by the differential and `Tests/OpaqueFill`. So the change can only reject more, never accept more; there is no new unsoundness surface.

## 3. Acceptance changes, stated honestly

The correlation class flips from accepted to rejected. The pinned example:

```
let b = match n { Z => True, S(k) => False };
match b { True => { let h = (Refl : Id Nat n Z); () }, False => () }
```

Fork: `b` is concrete per path, the second match selects, `n ≡ Z` is in force — accepted. Join: `b` is `σ : Bool`, the second match splits blind — rejected, and the error message must say why and name the remedy. The corpus contains zero such programs. The two hover tests' pinned per-path comments (`HoverSpans` §11 "differs per path", `PointSpans` §P3 two-answer hover) describe fork behaviour and are updated to the joined single answers; per-path hover answers survive only INSIDE arms, where paths still genuinely exist.

Note what does NOT flip, because of ladder rule (a): arms that agree (`match n { Z => True, S(k) => True }` then `Refl : Id Bool b True`) still check — the value passes through. v1's always-mint (which rejected this) is corrected.

## 4. What ships (rework of branch `match-join`; commit + push per stage; no merge)

* **Stage R1 — remove the motive.** Strip the `matchE` motive field, both syntax rows, and the motive threading (~44 lib + 30 test sites); assert `Term`-level identity with `origin/main` desugarings. `MatchJoinProbe` updated or retired.
* **Stage R2 — the join driver, unconditional.** Rework `exploreJoin`/`joinSlots` to the §2 ladder (value pass-through first, synthesis second, dependent-pack heuristic third, reject last); wire it as THE `exploreD` handling of every statement-position symbolic match; delete the fork driver path (`exploreSymBranches` survives only as the arm-checking loop inside the join).
* **Stage R3 — tests** (`Tests/MatchJoin.lean`, accepted/rejected only): agreeing-arms pass-through accept; fresh-σ join accept (flag case, continuation uses `b` opaquely); the correlation rejection with its message pinned; structure-divergence rejection; borrow-mode join with arm writes + fn audit; dependent-pack heuristic accept (`Pair(True, e)`); executing differential unchanged; flip ledger (revert the join case, count reds, restore). Hover-test comments updated.
* **Stage R4 — measurement.** Sequential-match paths and wall-time, join vs the fork numbers recorded in v1's AS BUILT (3/5/9/65 paths, 27/64/138/1205 ms) — expect linear paths and flat per-match cost, with no annotation in the measured programs.
* **AS BUILT** appended here, including which ladder rule each test exercises and where the dependent-pack heuristic's edge sits.

## 5. Out of scope

Loan-set borrows (branch-divergent borrows stay rejections); joining differing carve shapes via fold/`endGroup` reassembly; any executing-mode change; any `Term` or syntax change (hard constraint, not preference); resurrecting the fork in any form.

---

## 6. AS BUILT (2026-08-21, branch `match-join`, v2 rework)

> **SHIPPED, R1–R4.** The join is unconditional, the carrier and syntax are byte-identical to `origin/main`, and the whole corpus is green with exactly two assertions changed. Three findings from contact, each recorded at its site.

**R1+R2 (one commit, `9c5f66fc`).** Syntax.lean/Uni.lean/FnMacro.lean and the six once-threaded test files are `git checkout origin/main` — identical, not re-edited — so Term construction is main's by construction; the `Sugar` goldens re-ran green as the canary. `pushContinuations` is DELETED, not disabled: `atBoundary` numbers seals and nothing else, and the seam shape is built lazily where a match is walked — `pushJoinArms`/`pushJoinArmsSeq` at `readR`/`readRTail`'s new statement-match rows (⇒ selects one arm, markers pop the arm scope, envs bit-identical — the executing-mode question §2 left to the implementer, answered: generalize the lazy rows, keep no pre-pass) and at `exploreD`'s concrete delegation.

**The driver.** `exploreD` routes both statement shapes to `exploreJoin`. Two single-path delegations before any join: a concrete scrutinee, and **the one-branch match** — fork ≡ join exactly at N=1, so `let Pair(a, b) = e` destructures keep field σs and knowledge losslessly, which is what spares the corpus's pervasive Σ idiom from the seam entirely. Genuinely branching symbolic matches join by the ladder (`joinVal`), rules as §2 with two contact corrections:

* **Rule 5 validates by `hasType`, not re-synthesis** — the first cut required every arm to synthesize the candidate type and wrongly refused `Nil` at `List Nat` (a parameter no value can invent). Found by the corpus (`S33Eager`, `PointSpans` P3) within minutes of the driver landing. Each arm's value is judged under that ARM's own exit `sctx`.
* **Rule (c) is a real anti-unifier, not an abstraction** — `Term.abstractInto` of the first component's value mangled the flagship's own case: `True`/`False` occur INSIDE the unfolded `Leb` spine, so blanket replacement rewrote each arm's candidate differently and nothing converged. `antiUnify` walks the candidates simultaneously: agreement stays, a position where each arm's subterm is that arm's own first-component value becomes σf, same-shaped nodes recurse, exotic heads fail closed to rule (d). With it, `Pair(True, e)`/`Pair(False, e)` joins at `Id Bool (Leb a b) σf` and the full roundtrip — destructure, re-split the flag, `LebTrueLe` on the refined evidence — checks end to end with zero annotation (`packEvidence`).

Also load-bearing: `symFreeIn` (an arm-minted σ may not cross the seam — two arms mint from the SAME counter, so one id can mean two different things; both arms of an `if` mint their branch equation at one id) and `collapseArmLoansFrom` (the arm's own loans are ended at its seam so a borrow payload is a VALUE the ladder can read; inherited loans are left for the continuation).

**Corpus fallout, complete list:** two assertions — `Traces`' `zeroHead` and `variantChange` `tailPaths`, the path-STRUCTURE canaries, now pinning ONE joined path each (`variantChange` is rule 4 live: both arms leave `Nil`, it passes through; `zeroHead` is rule 5: payloads disagree, fresh σ at `List Nat`). `Programs`' `S33Eager` trio and `PointSpans` P3 accept unchanged through rule 5. The hover comments (`HoverSpans` §11, `PointSpans` §P3) now describe the joined single answers; per-path answers survive only inside arms.

**R3 (`5bbb935b`), rule per test:** seqJoins (5), agreeArms (4 — v1's always-mint inversion, now accepting), correlClass (§3's pin, rejected "does not have its ascribed type"), divergentBorrows (7, the named-slot message), packEvidence (6, the flagship), borrowWrite (3→5), concreteJoin (selection + `progRunsTo`), joinNonExh (exhaustiveness), singleArm (N=1). **Flip ledger 4/4:** reverting the two `exploreD` join rows to the fork shape turns exactly `correlClass`, `divergentBorrows`, `zeroHead`, `variantChange` red — the four claims that ARE the joined semantics — and nothing else.

**R4, measured** (same annotation-free programs as the v1 fork baseline):

| N | fork paths | join paths | fork ×200 | join ×200 |
|---|---|---|---|---|
| 1 | 3 | 4 | 27 ms | 33 ms |
| 2 | 5 | 6 | 64 ms | 62 ms |
| 3 | 9 | 8 | 138 ms | 96 ms |
| 6 | 65 | 14 | 1205 ms | 214 ms |

Join paths are 2N+2 (each arm closes its own diagnostic sub-path — the seal carry's rule — plus one continuation path and the top level); wall-clock is linear at ~+30 ms per match against the fork's doubling, 5.6× ahead at N=6 and diverging. The measured programs carry no annotation — the user-experience constraint, held in the measurement itself.

**Where the heuristic's edge sits:** rule (c) fires only on `Pair`-shaped results; its candidates come from arm `sctx` (bare σs) and the closed constructor basis, so a snd whose type needs a parametrized head (`List`) or whose disagreement is not the fst value verbatim falls to (d); nesting recurses but each level abstracts only its own fst. The rejection message names the remedy, and `packEvidence` is the worked example the message points at.

**Residuals:** parametrized-head synthesis (a `Cons`-headed result with no owed source rejects — an inverse constructor-table would lift it); slot-level packs (rule (c) currently reaches only the result; a slot holding a written pack falls to rule 5/7); anti-unification under binders is name-sensitive (`pi`/`lam`/`sigmaT` require equal binder names — α-widening is mechanical if a case demands it); the `joinFreshTyped` σ carries no provenance for hovers ("joined from N arms" would earn its keep).

---

## 7. THE HOVER-SIMPLIFICATION SWEEP — a finding, not a deletion (2026-08-21)

The follow-up question was whether the join lets the multi-path hover/`show` rendering machinery (`renderPaths`' multi-answer listing with arm trails and the cap-at-three, `letIndex`'s `differs` flag and the `*(differs per path)*` suffix) be retired. The premise: post-seam points are one joined path, in-arm points are one arm's path, and shared-prefix points repeat with identical deltas — so genuinely divergent answers at one point should be unreachable. **The sweep refutes the premise.**

`Tests/MatchJoinSweep.lean` (not in build) replays every (statement-key × binder) point of thirteen corpus programs through the real ledger machinery and counts distinct rendered answers:

| program | paths | points | point-div | let-div |
|---|---|---|---|---|
| the six MatchJoin programs | 1–8 | 3–27 | **0** | **0** |
| S33Eager trio (statement-position borrow joins) | 5 | 26–34 | **0** | **0** |
| flagship (list quicksort) | 14 | 1822 | **56** | 7 |
| arrChain (array quicksort) | 14 | 3160 | **38** | 3 |
| hashmap s1Chain / s2CheckedCaller | 31 | ~24k | **448** each | 13 |

Every program whose matches the JOIN reaches renders one answer per point — the join's own half of the premise holds. The divergences all come from **tail-position matches, the corpus's dominant style, which the join deliberately leaves forked** (no continuation, one audited path per arm): a statement ABOVE a tail split appears in every one of that body's paths, and its σ-bearing state is NOT identical across them — per-path refinement sweeps the slots bound before the split, and per-path minting (a recursive call in each `if` branch) renumbers the σs, so the same binder legitimately renders `(σ₀ : List Nat)` on one path and `(σ₈ : List Nat)` on another. Samples: `Partition`'s `v`/`p`/`Hf` at the statements above its tail `if`, 56 points in the flagship alone.

**So the boundary sits exactly at the match's position.** Statement-position match → joined → one answer, and the machinery's dedup collapses the shared prefix. Tail-position match → forked (by design: fork ≡ join is FALSE there only in bookkeeping — semantically each arm ends the body, but the paths still mint and refine separately) → the multi-answer rendering is load-bearing. Nothing is deleted; the sweep harness stays as the evidence and as the regression canary for whenever a later change (e.g. canonicalizing σ display per path) makes the count drop.

What DID change under the join (from R2): the two purpose-built statement-position hover pins (`HoverSpans` §11, `PointSpans` §P3) are single-answer now, and their comments say so. `ShowSpans`' `#guard_msgs` suite — including upstream's S6 "a probe above a match sees the unnarrowed borrow" — passes verbatim, with the S6 claim STRENGTHENED: the pre-split state is literally the state the joined continuation resumes from.
