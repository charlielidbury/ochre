# The mu experiment

## Background: what happened and why we're here

Och previously had two separate self-reference primitives:
- `fix` — general recursion (recursive functions)
- `iota` — self types (dependent elimination)

We discovered these are the same thing. In Och's "terms and types are the
same thing" framework, both express self-reference. The only difference is
how *determined* the self-reference is — and that's already handled by the
concrete/abstract evaluation split. See `docs/ideas/merge-fix-iota.md` for
the full analysis (READ THIS FIRST — it is the design document for this
experiment).

The unified primitive is `mu`:

```lean
| mu : Name → (ann : Expr) → (body : Expr) → Expr
```

`mu (x : T). body` means "the thing being defined can refer to itself as x,
and its annotation is T."

- **Concrete eval:** unroll — `body[x := mu x T body]` (like fix)
- **Abstract eval:** normalize body under binder, return `mu x T' body'` (like iota)
- **Subtyping:** mu-mu compares bodies covariant; self-intro/elim unfold one level

## North Star: abstract appendVec

The goal is getting `appendVec` working end-to-end with **abstract** arguments
(`n : Nat, m : Nat`). Och is useless without this — a type system that can
only verify concrete computations adds nothing over an evaluator.

## Strategy: tests first, proofs last

Proofs are expensive and fragile — they break whenever definitions change.
The definitions are NOT yet stable (annotation semantics are unresolved,
the env type may need to change, subtyping rules may evolve). So the strategy
is:

1. **Get appendVec working as native_decide tests** — validate that the
   definitions are expressive enough by writing executable tests, not proofs.
   Every milestone below is a test that either passes or doesn't.
2. **Only then prove soundness/monotonicity** — once the tests pass and the
   definitions have stabilised, the proofs confirm what we already believe.

This brings risk forward: if the definitions can't express appendVec, we find
out in days (a failing test), not weeks (a stuck proof).

**Do not prioritise filling sorrys over getting tests to pass.** A system
with 10 sorrys and a passing appendVec test is in a far better position than
a system with 0 sorrys that can't express dependent elimination.

## Current state (as of 2026-04-02)

`lake build` passes with **2 sorrys** (`absEval_mono` + `soundness_gen`).
**All M1-M4 milestone tests pass.** 11 WellTyped witness tests pass.
**ValSub.lean is SORRY-FREE** — bridge proved via compose_r + mono.

### What's working

- mu replaces fix+iota throughout the codebase
- Concrete eval unrolls mu (like fix)
- Abstract eval normalizes body under binder (like iota)
- **Annotation-based mu-elim in absEval** — when a recursive mu is applied,
  absEval uses the annotation (if it's a lambda) to determine the return
  type, preventing divergence. Falls back to body unfolding for self-types.
- **Domain normalization in subCheckNF** — domains are normalized before
  adding to inferType's context, so `Vec' T` is recognized as a lambda.
- **Equi-recursive self-intro in subCheckNF** — self-intro substitutes the
  mu type itself (not the value), enabling Variant B (truly self-referential
  Nat). Coinductive `seen` set prevents divergence on circular unfolding.
- Self-intro and self-elim work in subCheckNF
- `inferType` in the subtype checker does mu-elim on stuck applications
- **All milestone tests pass:** M1a-d, M2a, M3a, M4a-c
- **Abstract `add` (non-recursive, Church-style) with SelfNat passes** (§9)
- **Recursive add (mu-as-fix) with both concrete and abstract args passes** (M1a-d)
- **appendVec as raw function AND applied to abstract args passes** (M4a-c)
- **Variant B passes:** `zero_mu ⊑ MuNat` and `add_mu ⊑ MuNat→MuNat→MuNat` (§10)
- **soundness_gen ~300 lines of proof reinstated** — all non-asc,
  non-annotation-path cases proved. 3 targeted sorrys remain.

## RESOLVED: WellTyped is now non-vacuous (Phase 5, Step 1 complete)

WellTyped was previously Prop-valued with SubtypeCore in the asc case.
SubtypeCore lacks self_intro, making WellTyped unsatisfiable for any
program with `(e : mu_type)` ascriptions — the soundness theorem was
vacuously true.

**Now fixed:** WellTyped is Bool-valued with `subCheckNF` in the asc case.
11 witness tests prove WellTyped is satisfiable for milestone programs.

**Architecture:** The intended user-facing type checker is
`WellTyped fuel [] e && subCheck fuel e τ`. `WellTyped` recursively checks
that all ascriptions are sound (e.g., rejects `(b : not b)` inside a
lambda). `subCheck` checks that the overall expression has the declared
type. Both are decidable (Bool-valued). Once Phase 4 proves soundness_gen,
the full guarantee is: if both return true, then `concEval(e) ⊑ absEval(τ)`.

**Key finding:** `(.asc unit' SelfNat)` is NOT a valid test — unit' (Church
unit) is not in SelfNat (Church Nat). Use `(.asc zero' SelfNat)` instead.
The ascription witness must actually inhabit the declared type.

## Known risks and open questions

These are observations, not certainties. Investigate before acting on them.

1. **The annotation field on mu is now load-bearing (RESOLVED).**
   absEval uses the annotation to determine return types for recursive mus:
   when `app (mu x ann body) aVal` and ann is a lambda, it beta-reduces
   ann with aVal instead of unfolding the body (which would diverge).
   For iota-like mus (ann = Type), it falls back to body unfolding.
   This resolved M1d, M4b, and M4c. The annotation is still NOT compared
   by subCheckNF's mu-mu rule or checked by WellTyped — these may need
   updating when proofs resume.

2. **The subtype checker compensates for the evaluator.** absEval does NOT
   do type-directed evaluation — stuck applications stay stuck. The subtype
   checker's `inferType` does mu-elim to recover type information, and
   `normalizeDomain` resolves beta-redexes in domains. This architecture
   works for all milestones through appendVec. Whether it scales to Phase 4
   (Scott encoding) is an open question.

3. **Variant B now works (RESOLVED).** Equi-recursive self-intro
   (substituting the mu type, not the value) resolved `zero_mu ⊑ MuNat`
   and `add_mu ⊑ MuNat→MuNat→MuNat`. The coinductive `seen` set prevents
   divergence. Phase 4 (Scott encoding) is now unblocked.

## Roadmap

Phases are in priority + dependency order. Do the first incomplete phase.

### Phase 1: Milestone tests ✓ COMPLETE

All M1-M4 milestones pass. Variant B passes. See git history for details.

### Phase 2: Non-vacuous WellTyped ✓ COMPLETE

WellTyped is now Bool-valued with `subCheckNF` (was Prop with SubtypeCore).
11 witness tests prove satisfiability.

### Phase 3: De Bruijn indices ✓ COMPLETE

**Why this is next:** Everything downstream needs substitution to be correct
and to have provable properties. The current `subst` in Syntax.lean is
explicitly not capture-avoiding ("WARNING: This naive implementation does
not handle capture"). This means:
- `subCheckNF` can give wrong answers on programs with shadowed variables
- Substitution lemmas (needed for Phase 4) are unprovable or false
- `concEvalS` soundness requires `ValSub a b → ValSub (e[x:=a]) (e[x:=b])`
  which needs correct substitution

De Bruijn indices fix all of these by construction:
- Substitution is correct (no variable names to capture)
- Alpha-equivalence is syntactic equality (no binder name issues)
- Substitution lemmas become provable
- The WellTyped binder name matching issue (y_ann == y_body) disappears

**Scope:** This is a mechanical refactor. Every file changes but the
semantics don't. Existing `native_decide` tests verify nothing breaks.

**Steps:**
1. Change `Expr` to use de Bruijn indices (indices instead of `Name` for
   bound variables; free variables can stay as names or also become indices)
2. Update `subst`, `Env.lookup`, `absEval`, `concEval`, `concEvalS`
3. Update `subCheckNF`, `inferType`, `normalizeDomain`
4. Update `Subtype'`, `SubtypeCore` and all lemmas
5. Rewrite Tests.lean (hardest part — all the test terms need rebuilding)
6. Verify `lake build` passes and all tests (including witness tests) pass

**Completed** in one session. All tests pass. Monotonicity and soundness
proofs sorry'd (need reproving with new env extension + subst patterns).

### Phase 3.5: Reprove env extend lemmas ✓ COMPLETE

Env extend lemmas proved for de Bruijn (4 sorrys eliminated):
- `SubtypeCore.shift_preserve` — SubtypeCore preserved under shifting
- `envSubCore_extend` / `envSubCore_extend_sub` (Monotonicity.lean)
- `envConsistent_extend` / `envConsistent_extend_sub` (Soundness.lean)

**absEval_mono is NOT reproved** — it requires a substitution lemma for
SubtypeCore (`SubtypeCore e₂ e₁ → SubtypeCore a₂ a₁ → SubtypeCore
(e₂.subst j a₂) (e₁.subst j a₁)`). This lemma doesn't hold for the
current SubtypeCore because `lam_body` requires equal domains — substituting
different values into a domain breaks equality. Fixing this requires adding
`lam_cong` (allowing different domains) to SubtypeCore, but Phase 4
replaces SubtypeCore entirely, making that work redundant.

### Phase 4: Step-indexed `ValSub` — the new soundness relation ← START HERE

**Depends on:** Phase 3 (substitution lemmas needed — now available via de Bruijn subst).

**The problem:** soundness_gen has sorrys. The fundamental blocker is that
SubtypeCore is too weak as the output relation — it lacks self_intro and
contra-domain lam_sub. See `docs/research/equi-recursive-subtyping-lit-review.md`.

#### Step 1: Syntactic ValSub + compose_r + bridge ✓ COMPLETE

File: `Och/ValSub.lean`. ValSub has 8 disjuncts:
- (1-7) Structural: top, refl, lam_sub, mu_body, app_cong, mu_r, mu_l
- (8) `compose_r`: right-compose with subCheckNF (algorithmic transitivity)

**What's proved (sorry-free):**
- ValSub definition + 10 intro lemmas (including compose_r)
- SubtypeCore embedding: `of_subtypeCore : SubtypeCore v τ → ∀n, ValSub n v τ`
- Downward closure: `mono : ValSub (n+1) v τ → ValSub n v τ`
- **Bridge lemma: `bridge : ValSub n v σ → subCheckNF σ τ = true → ValSub n v τ`**

**Critical finding: subst_congr is FALSE** (verified by native_decide).
This means generalized soundness via substitution congruence is blocked.
See ValSub.lean for the counterexample.

**Bridge design:** The bridge was previously blocked by domain composition
(contravariant domains need reverse bridge or transitivity). The compose_r
disjunct sidesteps this: instead of decomposing subCheckNF structurally,
it stores the subCheckNF result directly as evidence. The bridge proof
is then trivial: apply mono to get ValSub (n-1), then compose_r.

#### Step 2: SoundRel + concEvalE ✓ DONE (app-lam-beta PROVED)

**SoundRel** is now defined in Soundness.lean: like SubtypeCore but with
flexible domains on lam and flexible annotations on mu. This enables
`SoundRel.subst_congr` — the KEY lemma SubtypeCore can't prove.

**concEvalE** (env-based concrete evaluator) is now in Eval.lean. It is
structurally parallel to absEval (only differs at ascription: takes lhs
instead of rhs). Used as a proof auxiliary by `soundness_gen_sr`.

**soundness_gen_sr** (Soundness.lean): SoundRel-generalized soundness
theorem using concEvalE. Proved cases: bvar, type, lam, mu, top,
app-lam-beta, app-stuck, lam/mu/app_cong.

**Why concEvalE was needed:** The substitution-based `concEval` (lambdas
are values) creates a body/body' mismatch: concEval returns source body,
absEval returns normalized body. An env-subst equivalence lemma
(`SoundRel body (absEval body)`) is FALSE for mu-containing bodies — when
absEval enters a mu body, it puts `mu ann body` in the env, so `bvar 0`
resolves to the mu term (structurally different from bvar). The env-based
`concEvalE` normalizes under binders like absEval, so the IH relates
their outputs directly via the `EnvSoundRel` invariant.

#### Step 3: Resolve remaining sorrys in soundness_gen_sr ← DO THIS NEXT

**3 sorrys remaining (2 in soundness_gen_sr, 1 in soundness_app_case):**

1. **asc/refl case (Soundness.lean:~493):** concEvalE takes the term (lhs),
   absEval takes the type (rhs) — DIFFERENT subexpressions. The IH gives
   SoundRel for the term, but we need to connect it to the type via
   `subCheckNF`. Solution: change the output of soundness_gen_sr from
   `SoundRel` to an `OutputRel` that wraps `SoundRel ∨ compose_r` (like
   ValSub). Steps:
   - Define `OutputRel n v τ := SoundRel v τ ∨ ∃ mid, OutputRel (n-1) v mid ∧ subCheckNF mid τ`
   - Prove bridge: `OutputRel n v σ → subCheckNF σ τ → OutputRel n v τ`
   - Change soundness_gen_sr output from SoundRel to OutputRel
   - Non-asc cases: wrap SoundRel results in `OutputRel.embed`
   - Asc case: IH gives OutputRel for term, WellTyped gives subCheckNF,
     bridge composes them.
   **WARNING:** Changing the output to OutputRel is non-trivial because the
   app case uses `subst_congr` which needs SoundRel, not OutputRel, from
   the IH. OutputRel needs structural constructors (lam, mu, app_cong) so
   that IH results can be wrapped. Then the app case needs `OutputRel` inversion
   (lam_rhs_shape for OutputRel), which is blocked by compose_r — you can't
   extract body relationships from a subCheckNF chain without subCheckNF
   decomposition lemmas. Consider alternative approaches:
   - Prove a SoundRel bridge lemma for cases where self-intro doesn't apply
   - Add structural constructors to OutputRel + subCheckNF lam decomposition
   - Switch to a fully semantic approach (lam_sem in OutputRel)

2. **asc/SoundRel.asc case (Soundness.lean:~532):** Same issue, but the
   input has `SoundRel.asc h_term h_ty` relating different term/ty pairs.
   Same solution: OutputRel handles the subCheckNF composition.

3. **app-mu-annotation edge case (Soundness.lean:~358):** ✓ MOSTLY RESOLVED.
   The main case (ann_a = lam, body_a = lam) is PROVED via SoundRel.mu with
   annotation tracking + concEvalE mirroring absEval. The remaining sorry is
   a narrow edge case: ann_c = lam but ann_a ≠ lam (only via SoundRel.top,
   unreachable from .refl entry point). Can be eliminated by:
   - Restricting SoundRel.mu to require same-constructor annotations
   - Or proving the .refl entry point guarantees same annotations throughout

**The legacy `soundness_gen` (ValSub-based, uses substitution-based
concEval) is retained for compatibility.** Its 3 sorrys (lam, mu, app)
could be eliminated by proving a bridge between concEval and concEvalE,
but this is lower priority — the SoundRel-based proof is the main path.

**Note:** subst_congr (`ValSub n a b → ValSub n (e[i:=a]) (e[i:=b])`)
is FALSE for any relation with contravariant function domains. See
ValSub.lean for the verified counterexample. Do not attempt this.

### Phase 6: Scott encoding and recursive types

**Independent of Phases 3-5** (just tests, no proofs). Can be done any time.

- [ ] Type-level mu for recursive types
- [ ] Scott-encoded Nat (nested mus)
- [ ] Full induction via mu-as-fix
- [ ] Dependent elimination tests with abstract arguments

## Long-term proof strategy

See `docs/long-term-proof-strategy.md` for the full Och → Ochr → Ochre
proof roadmap and research references. Key takeaway: ownership-disciplined
mutation does not require separation logic — the `ValSub` relation from
Phase 4 extends naturally to Ochr and Ochre.

### Completed phases (for reference)

**Phase 1 (milestone tests):** All M1-M4 pass. Variant B passes.
Key techniques: annotation-based mu-elim, domain normalization,
equi-recursive self-intro + seen set.

**Phase 2 (non-vacuous WellTyped):** WellTyped is Bool-valued with
subCheckNF. 11 witness tests. soundness_gen mostly proved (3 targeted
sorrys in asc + annotation path).

**Previous Phase 3 (proofs):** absEval_mono and soundness_gen were
sorry-free, but soundness was vacuously true for mu programs (WellTyped
used SubtypeCore which is unsatisfiable for mu ascriptions). The sorry-free
proofs are preserved in git (commit f7c40a1) for reference but should not
be treated as "done" — the theorem statement was wrong.

## Design principles

- **Tests before proofs.** A failing test is more informative than a stuck
  proof. If you're choosing between "fill a sorry" and "write a test for the
  next milestone," write the test.

- **Definitions before proofs.** Getting the definitions right is more
  valuable than proving things about wrong definitions. If a proof isn't
  going through, consider whether the definition needs to change.

- **Never weaken preconditions without a witness test.** If you change
  WellTyped (or any theorem precondition) to make a proof go through,
  you MUST also add or maintain a `native_decide` test that the
  precondition is satisfiable for a real program. A sorry-free proof
  with an unsatisfiable precondition is worthless — it's vacuously true.
  This is how Phase 3 produced a "proven" soundness theorem that says
  nothing about mu programs. **Do not repeat this mistake.**

- **One primitive for self-reference.** If you find yourself wanting a second
  self-reference mechanism, stop and think about whether mu can do it.

- **Tests are sacred.** Existing tests pin expressiveness. Don't weaken them.
  Adding new tests is encouraged.

- **Sorry freely, compile always.** `lake build` must pass.

- **Read merge-fix-iota.md.** It is the design document. The worked example
  at the bottom shows what the typing rules need to look like.
