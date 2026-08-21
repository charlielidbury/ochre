# Plan: match environment unification — the join is the seal, inline

**The user's request, in substance.** Match branches are checked with increased knowledge (in a `Cons` branch the scrutinee IS a Cons node — dependent elimination). But there is no way to unify environments after a match, so code after a statement-position match is analysed once per path: N sequential matches cost 2^N walks of everything below them. Measured: 1/2/3 sequential two-branch symbolic matches produce 3/5/9 paths (2^N + 1, the +1 being the top level) via `checkProgramHover`. Design a join.

**The design, in one sentence.** *A match may declare a motive — a result type, exactly as a `fn` declares a return type — and a motived match checks each arm against the motive under that arm's refinement, then continues ONCE from the pre-split environment with the result re-minted as a fresh σ at the motive: the same environment unification the call boundary already performs, made available without factoring the match into a helper function.*

The one-sentence justification for the shape: DLLBC already has exactly one place where N environments become one — a function return. Each path passes the exit audit against the declared return type, and the caller resumes once with the result minted as a fresh existential at that type (§5.3/§6.1 opacity) and lent state re-typed by the audit's opaque fill. Today that join is reachable only by factoring the match into a `fn`, and the corpus's universal tail-position match style is the friction made visible: every `Partition`/`Quicksort` arm builds the entire return pack itself because nothing else avoids the blowup. This plan offers the same seam inline. It is the structurally uniform endpoint — one join mechanism at both seams — not a second mechanism.

---

## 1. Where the fork lives today (the code this plan touches)

* `pushContinuations` (`Machine.lean:3860`) rewrites `let x = match s {…}; k` and `seq (match…) k` by DUPLICATING `k` into every arm, behind `@armScope`/`@popArmL` seam markers. Every statement-position match becomes terminal.
* `exploreD`/`exploreMatch`/`exploreSymBranches` (`Machine.lean:6797–6928`) walk the spine; a terminal match on a symbolic scrutinee forks one path per branch (`exploreSymBranches` concatenates the per-branch path lists). `reorgScrut` classifies the scrutinee into `Dispatch` (`ownedCtor`/`borrowCtor`/`ownedSym`/`borrowSym`); `symOwnedSetup`/`symBorrowSetup` perform the per-arm refinement (`refineSym σ := Ctor(σ_fields)` through all σ-bearing state) and bind the branch equation (M23).
* `auditPathsD` (`Boundary.lean:32`) audits every path at return against the fn's return type — the continuation, having been copied into each arm, is audited once per path.
* Diagnostics already cope with the duplication: `stmtKey` is keyed by the statement's TERM because one statement exists in N copies (`Machine.lean:396–399`); `trail` records which path failed; hovers render per-path answers (`HoverSpans` §11, `PointSpans` §P3).

The two purpose-built post-match tests (`HoverSpans.lean:143–148`, `PointSpans.lean:89–98`) are the ONLY statement-position symbolic matches in the suite; everything else is tail-form. So the fork's relational power is almost unused by the corpus, and the join's cost falls almost entirely on programs nobody has been able to write comfortably anyway.

## 2. Surface

```
let x : τ = match s { Ctor(...) => e1, ... };
future code
```

The type ascription on the `let` is the join marker AND the motive. Unannotated statement matches keep today's fork semantics unchanged — zero corpus churn, and the fork remains available where per-path checking is genuinely wanted. (The elaboration layer already has expression ascription `(e : τ)`; whether the row is literally `let x : τ = match` or reuses the ascription form is the implementer's call — the macro layer decides, the `Term` shape below is the contract.)

`τ` may mention any σ in scope, INCLUDING the scrutinee's σ_s — that is what makes it a real dependent motive. The arm-local equation binder (`match e : s`) composes with this and stays arm-local.

## 3. Semantics — the join, precisely

**Term shape.** `Term.matchE` currently has no continuation (arms swallow it). The motived form must KEEP its continuation out of the arms, so the term is `letIn x rhs rest` where the match carries its motive: extend `matchE` with an `Option Term` motive field (`.matchE s eqn motive branches`), `none` everywhere today. `pushContinuations` gets one new case: a motive-carrying match under `letIn` is NOT pushed into — the spine keeps `let x = matchM …; rest` intact. Everything else in the pre-pass is untouched.

**Checking a motived match** (new case in `exploreD` for `.letIn x (.matchE s eqn (some τ) bs) rest`):

1. Fence, reorganize, classify the scrutinee exactly as `exploreMatch` does (reuse `reorgScrut`). Exhaustiveness check as today (`checkExhaustive`).
2. Snapshot the pre-split state `St₀` (after reorganization, before any refinement).
3. For each arm: run `symOwnedSetup`/`symBorrowSetup` as today, then explore the arm body TERMINALLY — its final expression is read against **τ as the arm's refinement rewrote it** via `readResult`. No new motive-instantiation machinery: the declared τ mentions σ_s, `refineSym` substitutes through all σ-bearing state, and τ held in the checking state is σ-bearing state. The refinement machinery IS the motive instantiation. Each arm must also pass its seam obligations (arm scope pop, as today).
4. **The join.** Continue ONCE from `St₀` with:
   * the scrutinee: owned mode — the var is consumed (⊥), its σ_s survives in `sctx` for types to cite (it names the PRE-split value, `old`-like); borrow mode — the loan structure of `St₀` is restored and the payload is re-minted as a fresh σ'_s at the loan's owed type (the opaque-fill move, `Machine.lean:4148–4258`), because arms may have written through it;
   * every OTHER Ω slot: compare the arms' exit values slot-by-slot. All arms convertibly equal (and equal to `St₀` where untouched) → pass through unchanged. Differing pure values → re-mint fresh σ at the slot's type. Differing borrow payloads under the SAME loan → fresh σ at the owed type. ⊥ in any arm → ⊥ (moved-after-conditional-move, the Rust rule). **Differing loan/carve STRUCTURE — different loans in the same slot, a carve present in one arm only, a scope entry escaping one arm — is REJECTED** with an error naming the slot and the two disagreeing arms;
   * the result: `x ↦ sym σ_b` with `sctx[σ_b : τ]` — τ at the un-refined σ_s;
   * per-arm knowledge and branch equations die at the seam. Correlation that future code needs must ride in τ (a Σ-pack of value + evidence is the corpus's fluent idiom — `Partition`'s `%pret` is exactly this at the fn boundary).
5. The fn-level exit audit runs once on the joined path, as it would after a call.

**Concrete scrutinee** under a motive: selection as today (one arm), result still read against τ. Executing mode is untouched — the join is a checking-mode construct; the differential's concrete runs go through arm selection exactly as before.

**Soundness direction.** The join is pure weakening: every per-path environment is an instance of the joined one, so join-accepted ⊆ fork-accepted for the same arms. The trusted move (fresh σ at declared type) is the call boundary's own, already exercised by the differential and `Tests/OpaqueFill`. The risk is therefore completeness/expressivity, not soundness — the reject list in §5.

## 4. The hard questions, answered here

**Q: What does τ mean per-arm vs post-join?** Per-arm it is checked REFINED (`τ[σ_s := Ctor(σ_fields)]`, free via `refineSym`); post-join it stands at the neutral σ_s. A later re-match on something carrying σ_s re-refines, and τ(σ_s) recomputes — correlation recovered through the type, which is the dependent-elimination answer to boolean blindness. This is the whole reason the motive may be dependent.

**Q: What happens to obligations/loans across the seam?** `St₀`'s obligation table carries forward (loans opened before the match are still owed at fn exit); obligations are keyed by loan and survive the re-mint because the re-mint changes payloads, not loan identity. An arm that ENDS a pre-existing loan diverges structurally from an arm that doesn't → reject (structure rule above). Arms' own arm-local loans are closed by their seam pops as today.

**Q: Stuck-spine scrutinees (`if e : Leb x p`)?** `generalizeStuck` runs before the split as today; the join treats σ_b like any owned sym. The minted equation is arm-local as today. Nothing new.

**Q: Diagnostics?** The completed arms are recorded as sealed sub-paths — the seal carry already solved "N sub-paths complete, one continuation proceeds" for fn bodies checked mid-walk (`St` completed-sub-paths field, `Machine.lean:208`; commit 7b506d23 "the carry keeps PATHS SEPARATE"). Reuse it. Hover/point ledgers inside arms behave like sealed-body branches; the continuation is one path. `stmtKey`-by-term and `trail` are untouched (the fork still exists for unannotated matches).

**Q: Why not auto-join when all arms leave convertible environments (no annotation)?** It is acceptance-neutral and kills the trivial blowup, but it is also a silent behaviour change to path counts and diagnostics, and the flag-computing case (`let b = match … True/False`) does NOT convert anyway, so it buys less than it appears to. Listed as a follow-up, not in v1. The one auto-join this plan DOES take: nothing. Explicit motive or fork.

## 5. What RELIES on the fork (and what the join rejects, on purpose)

Three reliance classes, from the design discussion; each gets a pinned rejection test so the boundary is asserted, not implied:

1. **Path correlation without a motive.** `let b = match n {Z => True, S(k) => False}` then a later `match b` whose arms use knowledge about `n`. Fork: `b` is concrete per path, the second match selects, `n`-knowledge is in force. Join: σ_b is opaque, the second match splits blind. Fix by declaring the correlation in τ (`Σ0`-pack with an `Id`), or keep the fork form.
2. **Heterogeneous continuation typing** (large elimination across the seam): `let x = match b { True => 5, False => Nil }` — per-path `x` has different types (documented as intended in `HoverSpans` §11). No non-dependent join represents it; a dependent motive (`match b { True => Nat, False => List Nat }`) can. Without one: reject.
3. **Branch-divergent borrows.** `let r = if c { &m x } else { &m y }; *r := 5` — different loans per arm. A join needs loan-SET borrows (the region/NLL generalization). Out of scope; rejected by the structure rule with a message that names this as the reason. Tail-position `Choose` stays legal.

Plus one negative control pinning weakening: post-join `Refl : Id Nat n Z` (provable on the Z path under the fork when the continuation is otherwise path-uniform… it isn't — the fork checks the continuation on BOTH paths, so this already fails today; the honest control is instead: an arm-provable fact cited AFTER the seam rejects under join and under fork alike, and a τ-carried fact checks under both).

## 6. What ships (stages; commit + push per stage, branch `match-join`, no merge to main)

* **Stage 0 — viability probe, timeboxed.** The riskiest composition is §3.4: continuation-from-`St₀` with re-minted payloads while the fn-level audit stays coherent. Hand-build the smallest joined match through the machinery (Bool flag, unit continuation) before writing the general driver. If this walls, stop and report — the wall is the finding.
* **Stage 1 — carrier + surface.** `matchE` motive field (default `none`, all existing constructions unchanged — the corpus's `Term`-equality goldens in `Sugar` must stay green), the `let x : τ = match` row, `pushContinuations` leaving motived matches unpushed.
* **Stage 2 — the join driver.** New `exploreD` case per §3; slot-diff + re-mint; the reject list with named-slot errors.
* **Stage 3 — tests** (`Tests/MatchJoin.lean`, accepted/rejected only, per the E2E rule): sequential joined matches accept; dependent-motive accept (Σ-pack evidence used after the seam); the three §5 rejections; borrow-mode joined match with arm writes (payload re-minted, exit audit passes); concrete-scrutinee joined match; executing-mode differential unchanged on a joined program. Counterfactual flip ledger: revert the driver, count red assertions.
* **Stage 4 — measurement.** The 3/5/9 probe rewritten with motives → expect 3/4/5 (linear); checker wall-time on a synthetic N-match body, fork vs join. Not-in-build harness beside `PointCost`.
* **Docs.** AS BUILT section appended here, per house rule.

## 7. Out of scope, named so nobody trips on it

Loan-set borrows (region generalization) for §5.3-class conditional borrows; auto-join of convertible environments; joining differing array carve shapes via fold/`endGroup` reassembly (the packed-borrows residuals already pin fold-insensitivity at symbolic-prefix carves — do not couple this plan to that); any change to executing mode; retiring the fork (it remains the unannotated semantics).
