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
