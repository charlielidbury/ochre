# Progress

## Current state (2026-04-21)

**MAJOR BREAKTHROUGH: `concEval_refines` and `concEval_preservation`
are now axiom-clean** (depend only on `propext`, `Quot.sound`). Verified
by `#print axioms`. Previously these transitively depended on `sorryAx`
via `Equiv.shift`'s nil-Γ case. The closedness-propagation chain built
this session (see below) eliminates that dependency.

`soundness` still has `sorryAx` — but only via the `typeCheck_sound`
branch (SubV/SubN/SynthN bridges), NOT via concEval anymore.

**Closedness-propagation chain (all fully proven this session):**
- `concEval_closedAt` (Eval.lean) — concEval preserves closedness.
- `Expr.shift_of_closedAt` (Syntax.lean, pre-existing) — shift is
  identity on closed expressions.
- `Equiv.subst_resp_closed` (SoundnessProof.lean) — closedness-carrying
  subst_resp that avoids Equiv.shift entirely.
- `Equiv.shift_of_closed` (SoundnessProof.lean) — trivial shift on
  closed endpoints.
- `Subtype'.shift_above_closed` / `shift_nil_closed` (Subtyping.lean)
  — trivial Subtype' shift on closed endpoints.
- `concEval_equiv_closed` (Soundness.lean) — all 8 cases proven using
  the chain above; no sorry.

`concEval_refines` / `concEval_preservation` / `soundness` now route
through `concEval_equiv_closed` (takes closedness).

**Phase 2 incremental structuring (earlier in session):**
- `QuotesCtx` strengthened with `Γ.size = Γe.length`, closing the
  `.hyp` case inside `SubN_to_Subtype'`.
- `SubV/SynthN_to_Subtype'` split from monolithic sorries into
  per-case `cases h` structure — the four SubV structural-guard
  cases (`hyp`, `refl`, `top`, `neutral_struct`) and the
  `SynthN.var` case close directly via the same handlers as
  `SubN_to_Subtype'`. Remaining closure-opening cases in each
  bridge still need tier-2 threading (realisability + quote_open_subst).
- `Subtype'.shift_above` — proven 12/23 cases including `.hyp`
  (was the supposed impossibility wall).

Per-case targets, post-refactor:
- SubV bridge (`SubV_to_Subtype'`): 4/15 cases closed; 11 sorry
  (binder/closure-opening + `neutral_ascent` quote-totality).
- SynthN bridge (`SynthN_to_Subtype'`): 1/6 cases closed; 5 sorry
  (all 5 non-`var` cases need `quote_open_subst`).
- SubN bridge (`SubN_to_Subtype'`): `.hyp` closed (was sorried
  awaiting `QuotesCtx.hlen`); remaining internal sorries mirror
  SubV's obligations.

## Historical state (2026-04-19)

**Phase 1 complete and verified** (f2ba74a). 41 → 0 markers; 0 sorries
in `Och/Std/` or `Och/Tests.lean`.

**Phase 2 (soundness) ~70%.** Nine audit findings A1–A9 in
`SoundnessAudit.lean`; six resolved (A1 covariant-app, A4 inductive
Subtype', A5 iotaIntro annotation, A7 fix-self productivity, A8 asc
transparency, A9 tyInfer-trusted-fix-annotation), one *deferred* (A6
lam-domain — pushing `domB` is more complete but causes seen-list
misses on dNat-style nested fixes; `domA` is sound, see DECISION-LOG
2026-04-18), two by-design (A2 type-in-type, A3 β-blind subCheck →
use typeCheck). Legacy `subCheckNF` retired; sweep is NbE-only
(refl/top/strict/A6-pinned). Algorithm is sound modulo type-in-type.

**Build: clean 71 s** (was 580 s before the `Val.beq` ptrEq fix +
legacy retirement; DECISION-LOG 2026-04-19). DBool/DNat constructors
use the very-dependent encoding (no per-constructor `fix B`).

Proof chain: `subCheckVal → SubV → Subtype' → semantic`.
  - `subCheckVal → SubV`: **fully proven** (axioms `propext`/
    `Quot.sound` only, verified PASS), all 15 match arms + all 4
    helper-function reflections in `SoundnessProof.lean`.
  - **All four target theorems wired** (Soundness.lean):
    `subCheckVal_sound = SubV_to_Subtype' ∘ subCheckVal_subV`;
    `typeCheck_sound = tyCheck_sound_closed ∘ subCheckVal_sound`;
    `concEval_preservation = .trans ∘ concEval_refines`;
    `soundness` composes the latter two. None of the four has a
    direct `sorry`. `concEval_equiv` 8/8 head-shapes leaf-sorry-free;
    `Equiv.iota_unfold` axiom-free.
  - **10 declaration sorries** (all in SoundnessProof.lean;
    Subtyping/Soundness/Eval sorry-free) at `67a202b`.
    **All three root obligations solved with proofs**:
      1. Depth-tagged `Seen` → `ctx_extend_at`/`narrow` proven;
         Subtyping.lean **0 sorries**.
      2. `R` env-exposure → `vapp_realises`/`R_mono`/
         `quote_open_subst`/`Equiv.subst_target` **proven**.
      3. `OpenCtx.hwf`/`hlen` → `tyInfer .bvar`,
         `letBinderType_sound_open` **proven**.
    `Subtype'.app_elim` derived rule added.
  - **Soundness assessment:** the metatheory holds. None of
    the 10 sorries represent open research questions; each
    has a documented engineering route in DECISION-LOG/
    SUGGESTIONS. Three are statement-precision issues, not
    soundness holes: `openNf_holds` (false-as-stated;
    `eval_quotes'` route ready), `tyInfer .fix/.iota` (A9
    annotation-trusted by design), `tyInfer .letE` (algorithm
    gap, fixable in TyCheck.lean).
  - **Remaining 10:**
    - `Equiv.shift` nil-Γ (1) — `Subtype'.shift_nil` ~60 lines
    - `eval_realises` base-conjuncts (3) — drop redundant `R`
      conjunct + quote-fuel-mutual `quoteClosure_realises`
    - `SubV/SubN/SynthN_to_Subtype'` (3) — `(hRa)/(hRb)`
      threading from `subCheckVal_sound_open` callers
    - `openNf_holds` (1) — `(hnfq)` threading via `eval_quotes'`
    - `whnfPi_sound_open` + `tyCheck/tyInfer_sound_open`
      assembly (2) — via proven `quote_open_subst`/`app_elim`

Two checkers: `NbE.subCheck` (Val-domain, the soundness target),
`NbE.typeCheck` (bidirectional). Legacy `subCheckNF` removed.

Simple Och (`lean/Och/Simple/`) remains the proven-sound reference.
Phase 1 path: coinductive seen-set → removed `[fix-ann]` →
neutral-head gate → NbE evaluator → subCheckVal → `fix N. ι self.`
dNat encoding → stuckRec structural arms → bidirectional `typeCheck`.
Phase 2 path: SoundnessAudit → A1/A5/A6/A7/A8 fixes → seen-indexed
Subtype' → SubV reflection → step-indexed `R` → fundamental lemma.

### Agent phase1-coinductive-seen, 2026-04-16

Picked: `dtrue ⊑ dBool` (the central marker).

Found that `subCheckNF` was already accepting it — but only because the
`[fix-ann]` RHS rule (`a ⊑ fix A. body ← a ⊑ A`) made *every* term a subtype
of *every* `fix Type. _`, including `Nat_ ⊑ dBool` and `dBool ⊑ dtrue`. The
annotation `A` is the *type* of the recursion variable, not an upper bound
on the fixpoint, so this rule was unsound and masked the real obstruction.

Removing it exposed the actual gap: the recursive `dtrue ⊑ dBool` subgoal
that reappears in contravariant domain position couldn't be discharged
because `lam`/`app` reset the coinductive assumption set to `[]`. The fix
is the standard Brandt-Henglein discipline:

  - `seen` is threaded through `lam`/`app` instead of reset.
  - Only *productive* steps (fix-unfold, ι-unfold, iotaIntro) extend `seen`.
  - Annotation-widening steps inherit `seen` but never extend it; the
    `.iota`/`.fix` arms in `neutralType` (which silently re-introduced
    ann-widening with the inherited `seen`) are removed.
  - A new `[unfoldIotaL]` arm peels `ι` on the left so `ι_dtrue ⊑ M`
    reduces to its body instead of dead-ending at the annotation.
  - Degenerate `ι A. self` / `fix A. self` (body = `bvar 0`) skip the
    unfold path so they don't close trivially via the assumption set.

After this, all 21 DBool examples close by `native_decide`, including the
negatives (`dBool ⊑ dtrue`, `dtrue ⊑ dfalse`, `dfalse ⊑ dtrue` all
`= .ok false`). `Nat_ ⊑ dBool` and `Type ⊑ dBool` are correctly rejected.

Next obvious target: `dzero ⊑ dNat` runs out of fuel at 200. The DNat
encoding has a Scott-style eliminator whose successor case applies the
predecessor, so unfolding generates much larger terms than DBool. Likely
needs either a sharing-aware `seen` lookup (current `==` is structural on
the unfolded terms) or a smarter unfold strategy that doesn't substitute
the full fixpoint into the successor branch.

### Agent phase1-abseval-museen, 2026-04-16

Picked: `dzero ⊑ dNat`.

Root cause was not subCheckNF at all: `absEvalVal dNat` itself diverged
at any fuel. The `muSeen` cycle check in absEval's app-of-fix/iota arms
compared `(term, arg)` pairs by `==`, but every recursive descent goes
under fresh binders, so both the recursive term and its argument pick up
de-Bruijn shifts and the comparison never fires. Replaced the syntactic
match with a length-based cutoff (one unfold then stuck); subCheckNF's
own L/R rules handle the structural recursion soundly from there.

After that, `dzero ⊑ dNat`, `true_ ⊑ dNat = false`, and the previously
mis-tracked `dzero ⊑ done_ = false` all close at fuel 200. The remaining
DNat tests (`done_/dtwo/dthree ⊑ dNat` and `dNat ⊑ dzero`) are now
*reachable* but blow up: iotaIntro substitutes the closed `dNat` term for
its own self-reference, so each iota-L unfold roughly squares the term
size. This is a representation problem (eager-substitution de Bruijn),
not a missing rule — the obvious fix is an NbE/closure-style evaluator
where substitution is delayed. Also added the missing `body == bvar 0`
guard to fix-R that the verifier flagged.

26 → 25 markers (3 examples closed, 1 negative test corrected from
spurious-true to correct-false).

### Agent phase1-trans-exhaustive, 2026-04-16

Picked: the three `checkTrans` exhaustive transitivity searches in
Tests.lean (smallExprs/stdExprs/edgeExprs). They were sorried after the
μ → ι/fix split because the rule set changed; under the seen-discipline
rework (loop above) all 9³ + 11³ + 11³ triples now satisfy
`a ⊑ b ∧ b ⊑ c → a ⊑ c` with no counterexample.

Also made absEval total on stuck recursive heads: when the muSeen
cutoff fires (or any neutral-spine head can't be typed as an arrow) the
catch-all now returns the stuck application with placeholder type
`Type` instead of erroring with "not callable". This doesn't yet unlock
`Array_ dzero T = Unit_` because the inner β domain check `dzero ⊑ dNat`
sees a *different* normal form of dNat (normalised at non-empty muSeen
inside the fix-Array unfold) than the standalone check does — absEval's
normal form is muSeen-dependent, so it isn't canonical. The Array/Vec
wall is therefore the same NbE/closure-representation problem already
flagged for `done_ ⊑ dNat`, just one indirection deeper.

25 → 22 markers (3 transitivity examples closed).

### Agent phase1-neutral-head-gate, 2026-04-16

Picked: `Array_ dzero Nat_ = Unit_` (Array.lean) and the `Vec Nat_`
normalisation tests, all of which cited "stuck DNat elim on abstract n"
— exactly the absEval recursive-head problem.

The previous depth-1 muSeen cutoff stopped *every* recursive-head
application after one unfold, which prevented `Array_` (a fix) from
unfolding and *then* its argument `dzero` (an ι) from unfolding in the
same chain. Bumping the depth bound made `dzero ⊑ dNat` blow up, so
that's not the lever.

The actual termination criterion is the *argument*, not the depth: a
recursive head applied to a *neutral* (bvar-headed spine) cannot make
progress — the eliminator is stuck on an abstract scrutinee — whereas
applied to a *value* it consumes one constructor layer per unfold and
terminates as long as the value is finite. Added
`Expr.hasNeutralHead` and gated the ι/fix-in-app unfold on
`!arg.hasNeutralHead` (with a high muSeen depth bound kept only for
the degenerate `(fix f. f) v` case).

After this `Array_ dzero Nat_` reduces to `Unit_` (the recursive
`Array_ pred T` in the successor branch stays stuck because `pred` is
a bvar), and `Vec Nat_` normalises (so its negative subtyping tests
close). Everything that uses `done_/dtwo` as a concrete index is still
blocked by the `done_ ⊑ dNat` domain-check blowup inside the β step.

22 → 19 markers (Array_ dzero = Unit, Vec Nat ⊄ Nat, Nat ⊄ Vec Nat).

### Agent phase1-drop-domain-check, 2026-04-16

Picked: the four remaining `Array_ done_/dtwo` markers (Array.lean) and
`dNat ⊄ dzero`.

Two absEval changes:

  1. β-reduce unconditionally. The `(λx:A. b) v` arm previously did a
     `subCheckNF v A` domain check before substituting, which forced
     `(λn:dNat. …) done_` (inside the Array_ unfold) to discharge
     `done_ ⊑ dNat` *during normalisation* — exactly the goal
     subCheckNF was being called to set up. β is type-blind and the
     subCheckNF caller only consumes the value, so dropping the check
     loses inferred-type precision but unblocks normalisation.

  2. Re-add the syntactic head-`==` muSeen check alongside the
     neutral-arg gate. After dropping the domain check, normalising
     `Array_ dtwo` exposes the `(dsucc m) → Type` self-reference in
     dsucc's body: m gets the *value* `done_NF`, the neutral-arg gate
     doesn't fire, and the depth-16 backstop alone makes the term grow
     ~16×. The closed top-level `dsucc` doesn't shift under binders,
     so head-`==` against muSeen fires after one unfold and stops it
     cleanly.

Closes Array.lean: testArr1 ⊑ Array_ done_ Nat, testArr2 ⊑ Array_ dtwo
Nat, unit_ ⊄ Array_ done_ Nat, the (Array_ (dsucc dzero) Nat).isOk
smoke test, plus two new positive `Array_ done_/dtwo` reduction
checks. Closes DNat.lean: dNat ⊄ dzero.

Known incompleteness introduced: `done_ ⊑ dNat` (and dtwo, dthree)
now return `.ok false` instead of timing out. The head-`==` cutoff
leaves a stuck `(dsucc dzero)` inside done_NF's type annotation,
while iotaIntro on the dNat side substitutes the *evaluated* done_NF
(an ι value) for `self`; the two non-canonical normal forms of the
same term then meet in contravariant position and subCheckNF can't
equate them. This is incompleteness (a valid subtype rejected), not
unsoundness. Documented in the in-file TODO; the obvious fix is
either canonical NbE normal forms or a subCheckNF rule that
re-evaluates a stuck recursive-head application before falling
through to neutralType.

19 → 14 markers (5 closed, 2 new positive Array_ tests added).

### Agent phase1-stuck-head-reeval, 2026-04-16

Picked: `testVec1 ⊑ Vec Nat` and the `appendArrays` typing assertion.

Added a stuck-recursive-head re-evaluation rule to subCheckNF: when
either side is `app f arg` with `f = .fix/.iota` (i.e. absEval's
muSeen cutoff left a recursive head un-unfolded — *not* a genuinely
neutral bvar-headed term), unfold it once and recurse with the
seen-set extended. This sits in two places: a dedicated `_, .app
(.fix/.iota …) _` arm right after `unfoldFixR` (so it fires before
the LHS `.fix/.iota` arms — needed for transitivity over edgeExprs),
and inside `neutralType`'s `.app` arm for the LHS direction. Without
this the type-widening fallback collapsed `(dsucc dzero)` to `dNat`
and `(Array_ pred T)` / `(dadd n m)` to `Type`, losing all index
information.

Closes:
  Vec.lean:    testVec1 ⊑ Vec Nat
  Array.lean:  appendArrays ⊑ (T → n → m → Array n T → Array m T
                                 → Array (dadd n m) T)
               — Array.lean now has zero `sorry`.

`done_ ⊑ dNat` is still open: the re-eval rule lets subCheckNF
explore further than before (`.ok false` at fuel ≤150, exponential
at 200) but iotaIntro on dNat still substitutes the closed `dNat`
term for every `:dNat` ascription, so the search fans out before
seen can close it. Same NbE/closure-representation fix as before.

14 → 12 markers.

### Agent phase1-appendvec-northstar, 2026-04-16

Picked: harvest the markers the stuck-head re-eval rule unblocked.

Closes (no checker changes — pure harvest from f04721c):
  Vec.lean:   appendVec ⊑ (T → Vec T → Vec T → Vec T)  — the
              "north star" abstract appendVec test
              concEval (disZero (unpack vecResult)) = false_
              unpack vec1 ≠ dtwo
  Tests.lean: rewrapped (testVec1 : Vec Nat) ⊑ Vec Nat

`appendVec_wrong` (Vec:135) is still accepted: the checker doesn't
yet distinguish `dadd n1 n1` from `dadd n1 n2` under abstract n1,n2
— both reduce to stuck applications of the same closed `dadd` head
and the structural `app, app` rule accepts `n1 ⊑ n2` when both are
bvars. That's a real precision gap (the test is the right
assertion); fixing it likely needs the `app, app` rule to demand
argument *equality* (not just LHS ⊑ RHS) when the head is opaque.

12 → 8 markers.

### Agent ochre-20260416-193340, 2026-04-16

Pure harvest — no checker changes. Once rebased onto
phase1-appendvec-northstar, two more Vec markers close at the same
fuel, via the same stuck-head re-eval mechanism:

  Vec.lean: testVec2 ⊑ Vec Nat  (Array_ dtwo Nat → Pair Nat (Pair Nat
                                 Unit), sigma lines up)
            unpack vec2 → length ≠ done_  (symmetric to unpack vec1
                                 ≠ dtwo)

Separately (earlier in the session, before fetching the remote
updates): probed the `muSeen.length >= 16` cap as a candidate lever
for `done_ ⊑ dNat`. Tried adding a `(fix_expr, arg) == muSeen[..]`
uniqueness check alongside the length cap. done_'s normal form
shrinks ~10× (21620 → 2285 chars) but `subCheck 200 done_ dNat`
returns .ok false at fuel 200 where it previously timed out. The
shorter normal form leaves `(dsucc dzero)` stuck in the λP ann,
iotaIntro substitutes a fuller `done_` on the dNat side, and the
contravariant domain check hits structurally-different shapes.
Reverted — same conclusion phase1-drop-domain-check reached with the
closed-head `==` variant: muSeen caps are tuned to "do enough unfolds
to make shapes line up under eager substitution", not to principled
cycle detection. Documented here so the next agent doesn't re-reach
for this particular lever.

8 → 6 markers.

### Agent phase1-testvec2, 2026-04-16

Same harvest as 193340 above (raced on testVec2). Used the loop to
catalogue the remaining six markers into three distinct obstacles
so the next agent has a map:

  1. `done_/dtwo/dthree ⊑ dNat` (DNat) plus `vecResult ⊑ Vec Nat`
     and `unpack vec2` (Vec) — iotaIntro on dNat substitutes the
     closed `dNat` term for every `:dNat` ascription and the
     search fans out. NbE/closure evaluator.

  2. `unpack vec1 = done_` (Vec:62), abstract unpack `= dNat`
     (Tests:69) — non-canonical normal
     forms: the unpacked length and the literal `done_`/`dNat`
     are computed at different muSeen depths so `==` doesn't fire.
     Tests:69 may also have a wrong expectation (the Sigma type's
     body is the motive `X`, so abstract unpack at motive `Nat_`
     gives `Nat_`, not `dNat`).

  3. `appendVec_wrong` (Vec:135) — accepted because absEval no
     longer does the β domain check (loop 5), so the ill-typed
     `appendArrays T n1 n1 arr1 arr2` (with `arr2 : Array_ n2 T`)
     β-reduces silently. Restoring the domain check would re-block
     all the Array_/appendVec wins; a targeted fix would re-check
     domains only in subCheckNF's goal positions, not during
     normalisation.

### Agent phase1-parallel-forks, 2026-04-16

Four parallel forks, one per remaining obstacle:

  obstacle2-tests69: Tests:69 was a porting error. The pre-c061a3b
    test asserted `= Nat_` (the motive) and passed; the dNat port
    changed it to `= dNat` (n's type) on the assumption that the
    abstract unpack should reveal the witness type. But ascription
    widens to `Vec Nat_ = λX. λk. X`, so applying the motive gives
    the motive back. Under Church-Nat the motive and n's type were
    both `Nat_`, masking the distinction. Restored to `= Nat_` and
    closed. Getting `dNat` here is a Sigma-encoding question
    (Sigma-as-a-type would need to apply k to abstract witnesses),
    not a checker gap.

  obstacle2-vec62: Vec:62/71 restated via concEval. The
    computational fact "unpack gives back the packed length" is a
    runtime property; concEval has no muSeen-path-dependence so
    both sides normalise identically. Bidirectional subCheck also
    works for vec1 but hangs for vec2. The previous absEvalVal
    phrasing was testing absEval's NF canonicity, which is the
    documented representation problem, not the computational fact.

  obstacle1-dnat: skipping ι/fix annotation normalisation in
    absEval is harmless (no regressions) but doesn't close
    `done_ ⊑ dNat`. The fan-out is in λ-domain positions
    (`λpred:self. …`) inside dNat's body, not only ι/fix
    annotations. Skipping λ-domain normalisation breaks Pair
    (its projections need the domain in normal form). Confirms
    NbE.

  obstacle3-domcheck: neutralType domain check fails on both
    correctness and performance. The ill-typed
    `appendArrays T n1 n1 arr1 arr2` is fully β-reduced during
    absEval (no β-site check since loop 5), so by the time
    neutralType sees the application the mismatch is erased — only
    the consistent-with-wrong-indices return type
    `Array_ (dadd n1 n1) T` survives. And the extra `arg ⊑ dom`
    check at every neutral spine is multiplicative in nesting
    depth (appendArrays/appendVec hang at fuel ≥100). The domain
    obligation has to be captured at the β site *before*
    substitution; either (a) absEval annotates each β with a
    deferred obligation subCheckNF collects later, or (b) restore
    the β-site check once obstacle 1 is fixed so `done_ ⊑ dNat`
    doesn't blow it up. (b) means obstacle 3 is sequenced after
    obstacle 1.

6 → 3 markers.

### Agent phase1-nbe-foundation, 2026-04-16

Implemented `lean/Och/NbE.lean`: a closure-based NbE evaluator
(`Val`/`Neutral`/`Closure`, `eval`/`vapp`/`quote`, `nf`/`nfIn`).
Recursive heads (fix/ι) unfold by environment extension instead
of term substitution; a neutral argument blocks the unfold (same
gate as absEval), and a small per-chain `unf` bound stops the
`(dsucc m)→Type` self-reference in done_'s annotation. `quote`
opens closures with a fresh neutral and re-evaluates at `unf=1`,
so the self-reference reads back as a single stuck application
rather than 32 nested ones.

`NbETests.lean` validates: `nf` terminates on `dNat/done_/dtwo/
dthree` (where `absEval` either fans out or produces non-canonical
forms), `Array_ dthree Nat_` reduces to `Pair Nat (Pair Nat (Pair
Nat Unit))` (where `absEval` hangs), and `nf done_ = nf (dsucc
dzero)` (canonicity). All by `native_decide`. No changes to
`absEval`/`subCheckNF`; purely additive.

Tried the naive integration (swap `subCheckNF`'s ~7 `absEval`
calls for `NbE.nfInE`/`nfSubstE`). Doesn't help: `subCheckNF`
works on `Expr`, so each NbE call has to *quote* the result back
to syntax, and the next call re-evaluates that quoted form. The
quote/eval round-trip defeats the sharing — a `Val` closure that
points at `done_val` once becomes an `Expr` with the full
`done_NF` term inlined at every position, and re-evaluating that
re-creates the recursion at a different `unf` depth so `==`
misses. It also makes Vec.lean's existing `native_decide` tests
slower (the quoted forms are larger than absEval's). Reverted.

The *right* integration is `subCheckVal : Val → Val → Bool` —
compare in the semantic domain so closures stay un-quoted.
`iotaIntro` becomes "open the RHS ι closure with the LHS Val in
the env"; `lam-lam` opens both closures with the same fresh
neutral; the seen-set holds `(Val × Val)` pairs (which need
`BEq Val`, derivable once `Closure` compares its `Expr` body and
`Env` structurally). `nfSubstE` is in `NbE.lean` as the entry
point that does env-extension instead of `body.subst 0 a`, ready
for whoever picks this up.

### Agent phase1-subcheckval, 2026-04-17

`done_ ⊑ dNat` is the *encoding*, not the checker. Trace under
subCheckVal (no fan-out, search completes):

  done_'s λs domain  = `λpred:dNat-closed. P (dsucc pred)`
  dNat[done_]'s λs   = `λpred:done_. P (dsucc'[done_] pred)`
                       (dNat's `λpred:bvar0` → `λpred:done_`)

  contra needs `dNat-closed ⊑ done_` — correctly false. And
  semantically: done_ calls `s dzero`, but a dNat[done_]-caller's
  `s` expects `pred:done_`, and `dzero ⊄ done_`. So done_ does
  not satisfy dNat's self-type under this encoding + standard
  function subtyping.

dBool (e08bce9) uses `fix B:Type. ι self:B. …` — B (fix) is the
*type* binder, stable under iotaIntro; self (ι) is the *value*
binder, substituted. dNat conflates them. The fix: wrap dNat in
`fix N:Type. ι self:N. …`, use `N` for all type ascriptions
(`λm:N`, `λpred:N`, `dsucc':(N→N)`), keep `self` only for the
final `P self`. Then iotaIntro substitutes self → done_ but the
λpred annotation stays `:N` (= dNat after fix-unfold), and the
contra `dNat ⊑ dNat` is reflexive.

This is an encoding change, not a checker change. Once dNat
matches dBool's pattern, `done_ ⊑ dNat` should close under the
*existing* subCheckNF (same path as `dtrue ⊑ dBool` in loop 1).
The earlier "NbE root cause" diagnosis below was the fan-out
*symptom*; subCheckVal removed the fan-out and exposed the
underlying encoding mismatch.

**Confirmed**: with `dNat = fix N:Type. ι self:N. …`,
`subCheck 200 done_ dNat = .ok true` under the existing
subCheckNF. All prior tests still pass (build green, no
regressions in DBool/Array/Vec/Tests/NbETests). `dtwo/dthree`
are now *correct* (the contra is reflexive) but subCheckNF
still fans out on them — that's the genuine NbE-integration
work, now decoupled from the encoding question. `vecResult`
(which uses dthree) and `appendVec_wrong` (β-domain-check)
likewise.

### subCheckVal stuckRec-stuckRec arm; dtwo/dthree closed (5862916f)

Probing `NbE.subCheck` on the new encoding revealed a
closure-canonicity gap: the let-bound `dsucc` inside dNat's
body (domain `N` resolved from env) and the top-level `dsucc`
(domain a closed `dNat` Expr) are non-`beq` Vals even though
they denote the same function. When both are stuck on a
neutral (`dsucc pred`), the existing arms re-vapp (no progress,
arg neutral) → `.ok false`.

Fix: a `.neutral (.stuckRec fA aA), .neutral (.stuckRec fB aB)`
arm in subCheckVal that compares structurally — heads via the
`.fix,.fix` η-open arm (which normalises the env difference by
opening both under a shared fresh), args covariantly. With
this, `NbE.subCheck` accepts dzero/done_/dtwo/dthree ⊑ dNat
and rejects dNat⊑dzero, dzero⊑done_.

DNat.lean's dtwo/dthree assertions switched to `NbE.subCheck`
(the Val-domain checker is the better algorithm for these;
subCheckNF still fans out on them and will be retired once
subCheckVal handles the full test surface). Added 4 extra
agreement examples (dzero/done_ positives + 2 negatives under
NbE.subCheck) to lock in semantic agreement with subCheckNF.

**Markers: 3 → 2. Std sorries: 4 → 2.** Remaining: Vec
appendVec_wrong (β-domain-check) and vecResult (dthree
cascade).

### vecResult closed via NbE.subCheck (5862916f)

`NbE.subCheck 400 vecResult (Vec Nat) = .ok true`. Same root
cause as dtwo/dthree (vecResult has length dthree); same fix.
Verified that NbE.subCheck *accepts* appendVec_wrong (it has
no domain check during β), so the last marker genuinely needs
the β-domain-check restored in the typing evaluator.

**Markers: 2 → 1. Std sorries: 2 → 1.** Last marker:
appendVec_wrong.

### TyCheck.lean: bidirectional pass; appendVec_wrong closed (5862916f)

Two separate experiments confirmed the β-domain-check cannot
live inside `absEval`/`subCheckNF`:

  1. **beta-restore worktree**: full-fuel lenient check hangs
     (every β through `Array_` triggers a `done_ ⊑ dNat`
     side-goal, which itself β's through `Array_`, …). At fuel
     ≤64 it returns spurious `.ok false` for legitimate `Array_
     done_` — 7 Array.lean regressions.
  2. **Targeted gate** (only on neutral-headed args): regresses
     `appendArrays` typing because `arr ⊑ Pair Type Type`
     ascends through the muSeen-gated `Array_ (dsucc pred) T`
     to `Type`, losing the `Pair T (Array_ pred T)` reduct.

Both fail for the same architectural reason: the domain check
calls `subCheckNF` which calls `absEval` which calls the domain
check. The standard escape is a *separate* bidirectional pass
that walks the syntactic term, doing one domain check per
`.app`, with NbE supplying conversion as a black box.

`Och/TyCheck.lean` implements this:
  - `tyInfer`/`tyCheck` mutual; `whnfPi` unfolds fix/iota to
    expose Π heads (substituting the inhabitant for ι-self).
  - `.fix`/`.iota` are black boxes of their annotation — the
    pass does not recurse into bodies, so the unprovable
    `Array_ (dsucc pred) T ⊑ Pair Type Type` cast inside
    `appendArrays` never surfaces.
  - β fast-path for `.app (.lam ..) a` and `.app (.letE ..) a`
    avoids the quote-codomain round-trip when the head is an
    inlined helper (`mkVec`, `dpair`).

Fixing this exposed two `subCheckVal` gaps:
  - `synthNeutral .stuckRec f arg` returned `f`'s annotation,
    not `(annotation of f) arg` — wrong arity. Fixed.
  - `subCheckNeutral` had no `.stuckRec, .stuckRec` arm, so
    `Array_ (dadd n1 n2) T` from two paths (appendArrays' return
    annotation vs mkVec's domain via the quote codomain) failed
    even though their `quote`s are *identical Exprs*. Same
    structural fix as the subCheckVal arm.

`typeCheck appendVec τ = .ok true`; `typeCheck appendVec_wrong τ
= .error "arg ⊄ dom at fix·5 (arg=?0)"` — rejected exactly at
the 5th argument of the inner `appendArrays` call.

**Markers: 1 → 0. Std sorries: 1 → 0. PHASE 1 COMPLETE.**

### Phase 2 begins: SoundnessAudit.lean (5862916f)

Three soundness gaps identified and recorded as executable
`native_decide` witnesses in `Och/SoundnessAudit.lean`:

  - **A1**: covariant neutral-app congruence (the `Pair a b ⊑
    Pair A B` mechanism) violates substitution. Witness:
    `Pair zero_ unit_ ⊑ Pair Nat_ Unit_` accepted; eliminating
    with `λn. λu. n→Unit_` gives `zero_→Unit_ ⊄ Nat_→Unit_`.
  - **A2**: type-in-type (`_ ⊑ Type`). Intentional, but admits
    Girard's paradox; the soundness theorem must work modulo
    this.
  - **A3**: subCheck β is type-blind (`(λn:Nat_. n) Bool ⊑
    Bool` accepted). `typeCheck` catches it.

A1 is the actionable one: fixing it requires reverting to
bidirectional neutral-arg comparison and re-encoding `Pair`
(and hence `Array_`) with a separate value constructor. The
DECISION-LOG entry sketches the path. The other arms of
`subCheckVal` (refl, seen, lam-lam, iotaIntro, fix-unfold,
neutralAscent) follow standard sound rules.

### A1 fixed: bidirectional neutral-app + new Pair encoding (5862916f)

`subCheckNeutral`/`subCheckVal`/`subCheckNF`'s neutral-app arms
now require argument *equivalence* (`a ⊑ b ∧ b ⊑ a`). The
closure-canonicity case (DNat dtwo/dthree) and the appendVec
return-type comparison both still pass — they were always
equivalences, not strict subtypes.

`Pair` re-encoded as `λA. λB. λX. λk:(A→B→X). X` (parametric
body); separate `pair_ A B a b = λX. λk. k a b` constructor.
`pair_ … ⊑ Pair A B` via type-ascent through `k` (synth
`k a b : X`). The new Pair is *soundly* covariant in A, B
(contra² on k's domain). All Pair/Array/Vec value-construction
sites updated to `pair_ A B a b`. fst_/snd_ stay monomorphic at
`Pair Type Type` (any Pair coerces via type-in-type).

Build green; markers/Std-sorries stay at 0. SoundnessAudit's
A1 section now records the fix as `a1_ruleFixed` /
`a1_substitutionHolds` / `a1_pairAscent`. Two open items
remain: A2 (type-in-type, accepted as model axiom) and A3
(β-blind subCheck, mitigated by `typeCheck`). The arms-by-arms
soundness proof can now begin.

Verifier (12 checks, 6 adversarial probes): PASS. The old
unsound encoding is rejected even if reverted; equivalent-
but-not-syntactic args still accepted; ~2.15× DNat slowdown
from bidirectional doubling but no fuel exhaustion.

### Subtype' context-indexed; first hand-derivations (5862916f)

`Subtype'` is now `Ctx → Expr → Expr → Prop` with a `.bvar`
rule (`Γ[k] = τ → Γ ⊢ bvar k ⊑ τ.shift (k+1) 0`) realising
type-ascent declaratively. `lam`/`iota_body`/`fix_body` push
the binder's domain onto Γ. `SubtypeCore.toSubtype'` now
quantifies over Γ.

Two hand-built derivations in Soundness.lean confirm the
constructors suffice: `Subtype' [] zero_ Nat_` and
`Subtype' [] unit_ Unit_`, both via three `lam_body` then one
`bvar` (the body `z ⊑ X` is exactly `Γ[1] = bvar 0` shifted).
This is the smallest end-to-end witness that the declarative
relation matches the algorithm.

The remaining gap (β-conversion rule) is documented inline.
Next: prove `subCheckVal_sound` arm-by-arm; the lam-lam,
fix-unfold, and bvar arms now have direct constructors.

### β-conversion + four hand-derivations + non-partial subCheckVal (5862916f)

`Subtype'` gained `beta_L/R`, `letE_L/R`, `asc_L/R`; derived
`app_head`, `beta_head`, `app_ascent`. Hand-derivations for
`(λx.x) zero_ ⊑ Nat_` and `one_ ⊑ Nat_` (via app_ascent).
`subCheckVal` & co. made non-partial (`termination_by fuel`).

### A4/A5 found; A5 fixed; NbE made non-partial (5862916f)

**A4**: inductive `Subtype'` is incomplete for equirecursion.
Tracing `dtrue ⊑ dBool` declaratively: after fix/iota unfolds
the lam-lam contravariant domain needs `dtrue ⊑ dBool` again.
The algorithm closes this via the seen-set; the inductive
relation cannot. Documented with three fix options
(seen-indexed / step-indexed / parameterised coinduction);
seen-indexed is closest to both the algorithm and Simple/'s
proof structure.

**A5**: both checkers' iotaIntro arm skipped the `a ⊑ ann`
premise, accepting `dtrue ⊑ ι self:Nat_. Type` despite
`dtrue ⊄ Nat_`. Fixed: both checkers now require `a ⊑ ann ∧
a ⊑ body[self:=a]`, with seen extended *before* the
annotation check so `fix B. ι self:B. …` closes coinductively.
Verified: constrained-ι rejected; dtrue⊑dBool, done_⊑dNat,
all DBool/DNat/Array/Vec/Tests still pass. The declarative
`Subtype'.iota_intro` already had both premises, so this
brings the algorithm in line with the relation.

**NbE termination**: eval/vapp/quote/quoteClosure/quoteNeutral
all made non-partial (`termination_by fuel`; quoteClosure
gained a fuel match). Full build green. Combined with
non-partial subCheckVal, the entire algorithmic stack now
unfolds in proofs.

**Phase-2 status**: 5 audit findings (A1, A5 fixed; A2 axiom;
A3 mitigated; A4 open). Algorithm sound modulo A2/A4. Declarative
relation has every constructor needed; the one remaining gap
(A4: coinductive encoding) is the last prerequisite for
`subCheckVal_sound`.

### A5 ι-ι gap closed; A4 seen-indexed Subtype' (5862916f)

Verifier FAIL on d1275ab: NbE.subCheck's `.iota,.iota`
structural arm has its own iotaIntro fallback that skipped
the annotation premise, so `(ι:Type.Type) ⊑ (ι:Nat_.Type)`
returned `.ok true` from NbE but `.ok false` from subCheckNF
— the two checkers diverged. Fixed: the ι-ι fallback now
checks `a ⊑ annB` first (same as the `_, .iota` arm).
Regression `a5_iotaIotaPath` locked into SoundnessAudit.

`Subtype'` is now seen-indexed: `Seen → Ctx → Expr → Expr →
Prop` with `.hyp : (a,b) ∈ S → Subtype' S Γ a b`. The four
productive rules (`iota_intro`, three `unfold_*`) extend `S`
before recursing; everything else threads it. `Subtype'.weaken`
proven (seen-monotone). The `dtrue ⊑ dBool` witness in
Soundness.lean has its annotation premise closed via
`.hyp (List.Mem.tail _ (List.Mem.head _))` — the cycle that
previously had no finite derivation now closes in one step.

**All five audit items resolved or accepted.** Algorithm sound
modulo type-in-type. Every arm maps to a declarative
constructor; the seen-set has a declarative counterpart;
the whole stack is non-partial. `subCheckVal_sound` is now a
matter of fuel induction with no architectural blockers.

### `subCheckVal_subV` guard arms proven; supporting lemmas closed (5862916f)

Three parallel worktree forks, all landed:

  1. **`Val.beq` non-partial + `LawfulBEq`** (81d7935): the
     `partial` came from `Closure.beq`'s
     `(e1.zip e2).all (Val.beq …)` hiding the recursion in a
     higher-order arg; replaced with explicit `Env.beq` in
     the same mutual block. `beq_eq`/`beq_refl` proven by
     mutual structural induction; `LawfulBEq Val` instance.

  2. **`eval`/`vapp` fuel monotonicity** (45277e3): combined
     Nat-induction proving both halves; `unf` held fixed
     (only decrements within a vapp chain, never across the
     n→m bridge). `Closure.open_fuel_mono` is a one-liner.

  3. **`dtrue ⊑ dBool` body premise fully closed** (d0b6070):
     the flagship coinductive derivation. `unfold_fix_R` →
     `iota_intro` (annotation via `.hyp`) → `unfold_fix_L` →
     `unfold_iota_L` → `lam`³, with the contravariant
     P-domain closing via `.hyp` at seen[3], the t-domain
     via `app_cong` with `dtrue ≡ ι_dtrue` (each direction
     one fix-unfold), the f-domain via `.top`, and the body
     `t ⊑ P dtrue` via `.bvar`. Every `Subtype'` constructor
     exercised; no sorry.

`SoundnessProof.lean`: the `SubV` Val-level relation +
`subCheckVal_subV` proof. Guard arms (refl via `eq_of_beq`,
hyp via `seen_any_mem`, top) closed by fuel induction at
`maxHeartbeats 4M` (the succ-body is too large for default
unfold; refactoring `subCheckVal` to factor out the match
is the cleaner long-term fix). The match arms remain
sorried (each is `ih` + constructor + `openω_of_open`).

**No axioms** in the proven path: `Val.beq_eq_ax` removed.
Build green; 0 markers, 0 Std/Tests sorries.

### subCheckVal factored; 8 match arms proven; pre-existing sorries swept (5862916f)

Two more parallel-fork landings plus mainline cleanup:

  - **`subCheckVal` refactor** (77ac3da): match arms factored
    into `subCheckValMatch` (lex `(fuel, tag)` termination).
    `subCheckVal_subV` now runs at *default* heartbeats —
    `set_option maxHeartbeats` removed.
  - **8 match arms closed** in `subCheckValMatch_subV`:
    lam-lam, `_,.iota`, `_,.fix`, `.fix,_`, `.iota,_`, plus
    three trivial leaves (`_,.neutral`/`.type,_`/`_,.type`).
    Pattern: `rcases` each sub-result before simping `h`,
    then `ih` + matching `SubV` constructor +
    `Closure.openω_of_open(Fresh)`. Added `hfuel : fuel ≤
    fuelω` premise for the lift.
  - **Pre-existing sorries swept**: `Syntax.lean` 4 → 0
    (the `.letE` cases of the four substitution lemmas; same
    binder pattern as the preceding `.fix` case). `Eval.lean`
    7 → 6 (`concEval_not_letE` added, mirroring
    `concEval_not_asc`).

**Sorry inventory** (excluding `Och/Simple/` and Std/Tests
which are at 0):

| File | Count | On critical path? |
|---|---|---|
| `Syntax.lean` | 0 | — |
| `Eval.lean` | 6 | no (legacy `subCheckNF` fuel-mono) |
| `Subtyping.lean` | 4 | no (legacy `subCheckNF` shape) |
| `SoundnessProof.lean` | 8 | yes (7 match arms + quote bridge) |
| `Soundness.lean` | 3 | yes (target theorems, compose above) |

The 7 remaining match arms are the disjunctive ones (ι-ι and
fix-fix structural-OR-fallback; three stuckRec re-vapp
variants; two neutral struct/ascent). Each maps to existing
`SubV` constructors but needs case-splits on which branch
the algorithm took. The quote bridge (`SubV_to_Subtype'`) is
the substantive remaining work.

### Mutual reflection block; subCheckNeutral/neutralAscent fully proven (5862916f)

`SoundnessProof.lean` restructured into a 5-theorem mutual
block (`subCheckVal_subV`, `subCheckValMatch_subV`,
`subCheckNeutral_subN`, `neutralAscent_subV`,
`synthNeutral_synthN`) with `(fuel, tag)` termination
mirroring the algorithm. Key technique: `split` after a
`do`-block desugars binds positionally NOT in source-pattern
order, so the pattern is `split` (no `next`) → `rename_i` on
bind results → `simp [bind, Except.bind, pure]` → repeat.

  - `subCheckNeutral_subN`: **4/4 arms proven**.
  - `neutralAscent_subV`: **3/3 arms proven** (`.app` via
    `cases` on synthesised type instead of `split` to avoid
    binding-order brittleness).
  - `synthNeutral_synthN`: 2/3 (`.var`, `.app`; `.stuckRec`
    sorried — two-level match on f/ann).
  - `subCheckValMatch_subV`: **12/15 arms proven**. The
    disjunctive `_,.stuckRec`/`.stuckRec,_`/two neutral arms
    closed; ι-ι/fix-fix/stuckRec² (structural-OR-fallback)
    sorried with per-branch decomposition documented.

`SubV` extended with `iota_struct`/`fix_struct`/
`stuckRec_struct`. Legacy `Eval.lean` fuel-mono scaffolded
as a combined 3-conjunct Nat-induction (zero case proven;
succ arms documented but sorried — off critical path).

**Sorry-bearing declarations: 15** (clean build count). On
the soundness critical path: 6 (3 SoundnessProof + 3 target
theorems). Off-path: 9 (5 Eval legacy + 4 Subtyping legacy).
The `subCheckVal → SubV` direction is ~80% done.

### `subCheckVal → SubV` complete (5862916f, ef386b3)

The 3 structural-OR-fallback arms (ι-ι, fix-fix, stuckRec²)
and `synthN.stuckRec` closed. ι-ι/fix-fix: `split` on the
outer `match structural with` exposes `hstruct` via
`rename_i`; structural side → `SubV.iota_struct`/`fix_struct`
via `ih` on annOk + openFresh + body; wildcard side reuses
the proven `_, .iota`/`_, .fix` fallback pattern. stuckRec²:
4 bidirectional checks → `stuckRec_struct`; fallback nests
two `vapp` + beq splits → `revapp_R`/`revapp_L`/`.ok false`-
contradiction. `synthN.stuckRec`: nested split on the
`match f with` or-pattern + `match ann with` → the four
`SynthN.stuckRec*` constructors.

**The mutual reflection block has zero sorry.** Every arm
of `subCheckVal`/`subCheckValMatch`/`subCheckNeutral`/
`neutralAscent`/`synthNeutral` reflects into a `SubV`/`SubN`/
`SynthN` constructor by fuel induction, with no axioms
beyond `propext`/`Quot.sound` (from `LawfulBEq Val`).

**Sorry-bearing declarations: 13.** Critical path: **4**
(`SubV_to_Subtype'` quote bridge + 3 target theorems).
Off-path: 9 (legacy `subCheckNF`).

Verified PASS: all five reflection theorems depend only on
`propext`/`Quot.sound`; no `sorryAx`, no `Classical.choice`,
no `ofReduceBool`. 258 native_decide tests; refactor is
semantics-preserving.

### Quote bridge: 3 non-recursive cases proven; NbE-correctness lemma stated (5862916f)

`SubV_to_Subtype'` is over a mutual inductive (`SubV`/`SubN`/
`SynthN`), so `induction` rejects it (multiple motives). For
now the three non-recursive constructors are dispatched by
`cases`: `.hyp` → `Subtype'.hyp` via `hS` + quote-uniqueness;
`.refl` → `.refl` (quote functional); `.top` → `.top`
(quote .type = .type). The 12 recursive cases each need the
mutual recursor plus two supporting lemmas, both stated:

  - `quote_open_subst` (the NbE correctness theorem):
    `quote (cl.openω v)` is `Subtype'`-β-equivalent to
    `(quoteClosure cl).subst 0 (quote v)`. This is the
    substantive remaining obligation; the standard proof
    is a logical relation between `Val` and `Expr` indexed
    by the eval environment.
  - `Subtype'.narrow` (Γ-monotonicity): `domB ⊑ domA →
    Subtype' S (domA::Γ) x y → Subtype' S (domB::Γ) x y`.
    Bridges the algorithm pushing `domA` vs `Subtype'.lam`
    pushing `domB`.

**Sorry-bearing declarations: 14** (+1 from stating
`quote_open_subst` explicitly). Critical path: **5** (2
SoundnessProof + 3 target theorems).

### A6/A7 + bughunt-lite findings; quote_fuel_mono (5862916f)

Three parallel probes (divergence-sweep, quote-open-attack,
bughunt-lite) ran concurrently and found:

  - **A6** (incomplete): NbE's lam-lam pushed `domA` (source)
    not `domB` (target), rejecting `(λx:Nat_. x) ⊑
    (λx:zero_. zero_)` while subCheckNF accepted. Fixed →
    push domB; both checkers agree. Also brings SubV.lam in
    line with Subtype'.lam (no Γ-narrowing needed for the
    bridge's `.lam` case).
  - **A7** (unsound): NbE's `.fix,_`/`.iota,_` arms accepted
    `(fix self. self) ⊑ X` for any X via the seen-cycle
    (body=bvar0 → open returns `a` → seen' fires).
    Productivity guard `a' == a → false` added; subCheckNF's
    R-side `body == .bvar 0 → false` flipped to `→ true`
    (`X ⊑ ⊤` is true). Both checkers agree on all 8 probes.
  - **Bughunt-lite (3 confirmed at 5-0)**: (1) SubV.revapp_R/L
    lacked `vappω` premise — `b'` could be `.type`, making
    SubV trivially inhabited. Premise added + threaded. (2)
    legacy absEval/neutralType `.fix` arms substituted the
    inhabitant instead of the type. (3) stale comment.

`SubV.unfold_fix_L`/`unfold_iota_L` gained the same
productivity premise as the algorithm (without it, body=
bvar0 + .hyp derived ⊤⊑c via the relation too).

`quote_fuel_mono`/`quoteClosure_fuel_mono`/
`quoteNeutral_fuel_mono` proven (NbE.lean). `eval_unf_equiv`
stated as the precise NbE-correctness obligation;
`quoteClosure_eq_quote_openω_fresh` proven conditional on it.

**SoundnessAudit: 7 findings (A1–A7), 5 resolved.** The
algorithm is sound modulo type-in-type. `subCheckVal → SubV`
remains fully proven (the SubV constructor changes were
absorbed by threading evidence the proof already had).

**Sorry-bearing declarations: 17** (+3 from stating
`narrow`/`shift_preserve`/`eval_unf_equiv` precisely).
Critical path: **6** (3 SoundnessProof + 3 target theorems).

Verified PASS (12 checks incl. β-reducible-self adversarial).
Divergence sweep: **0/576** (locked in as `divergenceSweep_zero`).

### Logical relation R; eval_unf_equiv derived; mutual bridge (5862916f)

Two parallel worktree forks landed and auto-merged:

  - **Step-indexed logical relation `R n d v e`** ("v
    realises e at step n, depth d"). Recurses on `n`; the
    `.lam` clause Kripke-quantifies over `n' ≤ n` (Appel-
    McAllester downward closure). `Equiv` (Subtype'-both-
    directions) defined with refl/symm/trans. `R_quote_equiv`
    *proven*: the base conjunct of `R` at nonzero index gives
    `quote v ≡ e`. **`eval_unf_equiv` is now derived** from
    the (sorried) fundamental lemma `eval_realises` — apply
    at unf₁ and unf₂, both realise the same `e.substEnv ρe`,
    compose via `Equiv.trans ∘ Equiv.symm`. No direct sorry.
  - **3-motive `@SubN.rec`** for the bridge. `SubN.var/app/
    stuckRec` and `SubV.neutral_struct/neutral_ascent` (most
    sub-cases) proven. New helpers: `quoteNeutral_app_shape`,
    `quoteNeutral_var_shape`, `quoteNeutral_stuckRec_shape`.
    The 10 closure-opening cases sorried with IHs visible
    (gated on `quote_open_subst`).

**The entire soundness chain reduces to `eval_realises`**
(the fundamental lemma of `R`). Everything else is either
proven or derived from it. Sorry-bearing declarations: 21
(+4 from stating `R_mono`/`eval_realises`/`REnv_id`/the
3-motive bridge block; `eval_unf_equiv` no longer counts).

### A8; eval_realises .lam/.app/.fix/.iota merged (5862916f)

**A8** (unsound vs concEval): both evaluators returned `τ`
for `.asc t τ`, accepting `Nat_ ⊑ (zero_:Nat_)`. But
`(zero_:Nat_)` computes to `zero_` (concEval, Subtype'.asc_*),
and `Nat_ ⊄ zero_` — subject reduction fails. Found by the
`.asc` case of `eval_realises`. Fix: both evaluators return
`t`. `Std/Id.lean`'s §6.4 "widening via asc" tests updated
(the widening *intent* lives in `typeCheck`'s annotation
handling, not the value evaluator). Divergence corpus
extended to 26×26=676 with `.asc` terms; still zero.

`eval_realises` two-fork merge:
  - **R stabilised**: ∀-form base (`∀ e', quote = e' →
    Equiv e' e`), `d`-depth lam-Kripke, `n'<n` fix/iota-Kripke.
  - **Closed**: `.type`, `.bvar`. `.lam` Kripke mostly closed
    (REnv_take + ihm at n'). `.app` split per fV (`.lam`/
    `.neutral` structured). `.fix`/`.iota` Kripke threaded.
  - **Proven helpers** (cumulative): `R_mono`, `REnv_id`,
    `R_quote_equiv`, `REnv_mono`, `REnv_cons`, `R_resp_Equiv`,
    `REnv_take`, `closedAt_bvarBound`, `Closure.mk'_body_closed`,
    `Equiv.lam`/`.app`/`.beta`, `quote_fuel_mono` family.
  - **Open helpers**: `substEnv_closedAt_irrel`,
    `R_depth_lift`, `REnv_lift`, `eval_env_take`.
  - **5 post-merge re-thread sorries**: cross-fork `ihm`
    signature mismatches (argument-order plumbing).

**8 audit findings (A1–A8), 6 resolved.**

**All three remaining markers reduce to the NbE
root cause:** `done_/dtwo/dthree ⊑ dNat` and `vecResult ⊑ Vec Nat`
are the dNat-self-substitution fan-out directly; `appendVec_wrong`
needs the β-site domain check restored, which is blocked on the
same fan-out. Once an NbE/closure evaluator (or any normaliser
whose NF is canonical and where substitution doesn't copy) lands,
the β-site domain check can come back, and all three should close
together.

### Agent phase1-bounded-domcheck-deadend, 2026-04-16

Tried obstacle (3) with a bounded-fuel domain check: run
`subCheckNF (min fuel 30) a' dom` at every β and reject only on
`.ok false` (`.ok true` and `.error` proceed). The hope was that
the simple `arr2 : Array_ n2 T ⊄ Array_ n1 T` mismatch would be
caught quickly while `done_ ⊑ dNat` would error (out of fuel) and
proceed. It doesn't work: subCheckNF returns `.ok false` for
legitimate deep checks before it errors (the appendArrays body
hits `bvar 0 ⊄ (λpair. pair Type Type)` at fuel 30 because the
type of bvar 0 needs more than 30 fuel to widen to the Pair-
projection shape). So the bounded check rejects valid β.
Documented in the Eval.lean comment so it isn't retried. The
right fix is probably to delay the domain obligation to where
subCheckNF actually *uses* the application's result type (i.e.
inside neutralType's `.app` arm), not at the β site.

### A6 reverted to `domA`; DNat build hang root-caused (5862916f, 2026-04-18)

Verifier FAIL on `cebb1b0`: clean `lake build` hung at
`Och.Std.DNat` (RSS frozen ~708 MB, >25 min). Bisected the
27 commits since the last clean DNat build (`047e59f`,
277 s); the `972db66` PASS verdict had been on cached oleans.
Three-way parallel bisect (`81d7935`/`77ac3da`/`f2684c9`) plus
revert-isolation (`revA6`/`revA7`/`revBoth`) pinned it to
`f2684c9` (A6: `tyCtx.push domA → domB`).

The mechanism: `dNat`'s inner `let dsucc = fix …` evaluates to
a `.fix` whose closure env (after `Closure.mk'`'s `.take`-trim)
is `[dzero, fresh_self@d, vNat]`. The body never references
env[1], but `.take (bvarBound − 1)` keeps it because `N` at
index 2 forces `take 3`. So each structural ι-open at depth
`d` yields a structurally-distinct `dsucc_local`. With `domB`
(taken from `dNat`'s side, hence referencing `dsucc_local`),
neutral-ascent synthesises types containing it; the seen-list
`==` never matches; `dtwo ⊑ dNat` goes exponential. With
`domA` (taken from the input `dtwo`, whose closures contain
no fresh vars) the seen-list works. `#eval NbE.subCheck 170
dtwo dNat`: instant at `domA`, >60 s at `domB`.

A6 was an *incompleteness* fix (`(λx:Nat_. x) ⊑ (λx:zero_.
zero_)`), not a soundness one — so reverting it leaves the
Phase-2 theorem statement unchanged. Reverted `domB → domA`
in `subCheckValMatch`; mirrored in `SubV.lam`; updated
SoundnessAudit A6 to DEFERRED with `a6_dtwoFastWithDomA`
regression; divergence sweep now whitelists the A6 pair and
asserts NbE only ever *under*-accepts. The bridge `SubV.lam →
Subtype'.lam` will need `Subtype'.narrow` (already stated,
sorried). DECISION-LOG entry added.

A worktree fork is implementing the principled fix —
mask unreferenced closure-env entries with a canonical
placeholder so `Val.beq` identifies `dsucc_local` across
fresh-opens — after which `domB` can come back.

### Three forks integrated; subCheckVal_sound wired (5862916f, 2026-04-18)

`70307d5` clean-builds in 580 s (fresh worktree, no oleans);
the DNat hang is gone. Cherry-picked two of the three forks
on top:

- `438931b` → `d45f2d9`: `Subtype'.narrow_at` (position-`k`
  context narrowing) proven for 18/19 constructor cases;
  `narrow` derives from it.
  The one open case is `ctx_extend` — pushing a binder past
  a seen-set entry; the entries' Exprs are closed so this is
  morally the identity, but stating that needs a closedness
  invariant on `S`.
- `fb8164a` → `b668959`: `eval_realises` `.app` head sub-cases
  threaded — `.lam` head closed (was already), `.type`/stuck
  heads closed (new), `.fix`/`.iota` heads down to four named
  obligations: `vapp_open_eq` (vapp of an unfolded fix is
  vapp of body[self↦fix]), `R_resp_iota_unfold`,
  `R_resp_fix_unfold`, and a recursion-shape fix
  (recommendation: ∀-`unf`-quantify `R`'s Kripke clause and
  add `m ≤ fuel` to `eval_realises` so the inner `vapp` call
  is in IH range).
- Closure-mask fork (`6a0d2bf`, tagged
  `a6-closure-mask-experiment`): NOT cherry-picked. Env
  masking makes `dtwo ⊑ dNat` fast under `domB` but not
  `dthree`; the residual mismatch is in closure *bodies*
  (inner-let `dsucc_local` body is `bvar 3`, top-level
  `dsucc` body is the closed `dNat` Expr), so `domB` would
  need quote-based canonicalisation. `domA` stands;
  DECISION-LOG updated.

`subCheckVal_sound` (`Och.Soundness`) is now a direct term:
`SubV_to_Subtype' ∘ subCheckVal_subV` with the empty-context
quote premises discharged vacuously and `quote_fuel_mono`
lifting the user-supplied fuel. Soundness.lean: 3 → 2 direct
sorries (`typeCheck_sound`, `concEval_preservation`).

Sorry-using declarations (clean build at d4b7259): Eval 5,
Subtyping 6, SoundnessProof 9, Soundness 2.

### Eval.lean dead-scaffold removal (5862916f, 2026-04-18)

The legacy-`subCheckNF` fuel-mono scaffold
(`absEval_subCheckNF_neutralType_fuel_mono` from `f82fbfc`)
and four `*_preserves_closedAt`/`*_ctx_irrelevant` lemmas
(`851b67b`) had zero callers and were sorried since
introduction. Removed; doc marker points back to `f82fbfc`.
Eval.lean: 5 → 0 sorries. Total: 22 → 17.

### Six-fork integration; A9 found and fixed (5862916f, 2026-04-18)

Six worktree forks integrated (one parked). Tags pushed at
each fork commit for traceability.

- **R-Kripke restate** (`r-kripke-restate-fork`): `R`'s
  Kripke clauses now ∀-`fuel'`/`unf'`-quantified; 4
  `eval_realises` leaf sorries closed.
- **TyCheck de-partialised** (`tycheck-departialise-fork`):
  `tyInfer`/`tyCheck`/`tyCheckFallback`/`whnfPi` now total
  via `(fuel, tag)` lex; `unfold tyCheck` works.
- **`tyCheck_sound_closed` structured**
  (`tycheck-sound-induct-fork`): mutual `(fuel, tag)`
  induction. `tyCheckFallback_sound_closed` and
  `tyCheck`'s `.asc`/catch-all arms **proven**;
  `quote_total_on_eval`/`whnfPi_sound`/
  `tyInfer_sound_closed` stated. Found A9.
- **`Subtype'` congruence constructors**
  (`subtype-cong-ctors-fork`): `.iota_cong`/`.fix_cong`/
  `.letE_cong` added (vary both ann and body).
  `Equiv.subst_resp` and `R_resp_Equiv` closed (no leaf
  `sorry`; both reduce to the pre-existing `Equiv.shift`);
  `Subtype'.subst_body` removed (subsumed). SoundnessProof
  11 → 8.
- **`ctx_extend_at` deepened** (`ctx-extend-fork`): 16/19
  cases proven; the 3 binder cases need depth-tagged seen
  entries (or `Subtype'`'s `.iota_intro`/`.unfold_*` to
  record closed pairs). 5 shift/subst lemmas added to
  Syntax.lean (all proven).
- **`SubtypeCore` removed**: 4 dead legacy-checker sorries.
  Subtyping 6 → 2.

**A9** (`tyInfer` trusted fix/ι annotation): `typeCheck
(.fix Nat_ unit_) Nat_` was `.ok true`. Fixed by a
`.fix`/`.iota` arm in `tyCheck` that does
`subCheckVal (eval e) expected` directly (bypasses the
annotation-trusting `tyInfer` path; sound via
`subCheckVal_sound`). Two earlier attempts (body-check
inside `tyInfer`; `.ok none` on body-check failure) both
regressed `appendVec` because nested-fix annotations are
opaque neutrals. `tyCheck_sound_closed`'s new arm is
proven; SoundnessAudit gains `a9_fixIotaBodyChecked`.

**Sorry counts at `c5914db`**: Eval 0, Subtyping 2,
SoundnessProof 8, Soundness 5. Total **15** (from 22 at
session start). All four target theorems
(`subCheckVal_sound`/`typeCheck_sound`/
`concEval_preservation`/`soundness`) wired through with no
direct sorry.

### unfold_iota_R; concEval_equiv 8/8; A9 leak paths closed (5862916f, 2026-04-18)

Verifier on `c5914db` found two more A9 leaks: `tyInfer`'s
own `.letE` arm and the `.app (.letE …) a` let-floating
arm both consult `tyInfer val` without verifying. Same fix
as `tyCheck`'s `.letE` (verify via `tyCheck val valTy`,
fall back to singleton). `appendVec` still accepts;
`a9_fixIotaBodyChecked` now five witness conjuncts.

Removed `Subtype'.shift_preserve` (wrongly-stated, subsumed
by `ctx_extend_at`, no callers): Subtyping 2 → 1.

Two more forks integrated:
- **equiv-shift** (`equiv-shift-fork`): `Equiv.shift`'s
  cons-Γ case wired through `Subtype'.ctx_extend [τ]` —
  consolidates `Equiv.shift` and `ctx_extend_at` into the
  same depth-tagged-seen root cause (DECISION-LOG route a).
- **soundness-bundle** (`soundness-bundle-fork`):
  `concEval_equiv` (both directions) proven 7/8 head
  shapes; `concEval_refines` and `quote_total_on_eval`
  derived from it and `eval_quotable` resp. Found: `match`
  on `Equiv`-typed goals eagerly instantiates implicits;
  use `cases` instead.

Added `Subtype'.unfold_iota_R` (symmetric to
`unfold_fix_R`; `iota_intro` is the strictly-stronger
algorithmic form). With it, `Equiv.iota_unfold` is a
one-liner; `concEval_equiv`'s `.app .iota` head closes
(now 8/8). Soundness 5 → 4.

**Sorry counts at `d19f092`**: Eval 0, Subtyping 1,
SoundnessProof 8, Soundness 4. Total **13**. Reduces to
four root obligations: depth-tagged seen-set
(`ctx_extend_at` + `Equiv.shift`); `eval_realises`
recursion-boundary leaves; `eval_quotable` Val-size
measure; open-Γ generalisation of `tyCheck`/`tyInfer`/
`whnfPi_sound`.

### Tech-debt sweep + perf root-cause (5862916f, 2026-04-19)

Six parallel forks. **Clean build: 580 s → 71 s** (8.2×).

- **Perf root-cause** (`perf-rootcause-fork`, +48 to
  SubCheckVal): `Val.beq` walks the value DAG as a *tree*.
  With `unfBound=32`, `dsucc`'s self-applying P-domain
  makes `vthree` a 15.6 M-node tree-walk (the DAG is 63
  nodes; eval is 3 ms). Fix: `unsafe Val.beqFast` with
  `ptrEq ||` prefix, `@[implemented_by]` so the proven
  `Val.beq` is unchanged (`subCheckVal_subV` axioms still
  `[propext, Quot.sound]`). `dthree ⊑ dNat` 322 s →
  0.3 s (1046×); `dfive` (previously untestable) flat
  ~330 ms. PerfProbe.lean carries the regression.
- **Legacy `subCheckNF` retired** (`retire-subchecknf-fork`,
  net −449 lines, Eval.lean 808→339): the Expr-domain
  checker existed for the divergence sweep, which had done
  its job (A1–A8). New SoundnessAudit sweep is NbE-only
  (`sweep_refl`/`top`/`strict`/`a6_pinned`). One test
  weakened: `appendArrays` at its declared type is an
  A6-family NbE incompleteness (legacy accepted via
  `neutralType` Type-widening); pinned in PerfProbe.lean.
- **DBool: very-dependent encoding** (`38d1031`):
  `dtrue`/`dfalse` are now `ι self:Type. λP:(self →
  Type). …` — no per-constructor `fix B` wrapper. The
  `e08bce9` workaround predated A4/A5/A7; the
  very-dependent form now goes through directly. The
  hand-built `dtrue ⊑ dBool` derivation is shorter
  (t-domain is `.refl`).
- **DNat: local-let `dzero` removed**
  (`dnat-simplify-fork`): top-level `dzero` is
  very-dependent, `dNat` references it directly.
  `dsucc_local` stays (genuinely needs `N`). DNat module
  305 s → 256 s pre-ptrEq → ~3 s post.
- **Macro sugar** (`macro-sugar-fork`, `ced372c`):
  `ι x. body`/`fix x. body`/`let x = v in body` desugar to
  the `:Type`-annotated forms (`rfl`-identical Exprs).
- **`letBinderType` helper** (`tycheck-helper-fork`, net
  −5): the three duplicated A9 verification blocks
  factored into one mutual-block function.
- **PropertyTests.lean** (`test-additions-fork`, +240, 33
  tests): open-Γ `subCheckVal` (10), negative subtyping
  (16), `nf` round-trip + refl/top sweeps (7). Two
  *findings* pinned: (a) `nf` is not syntactically
  idempotent (`nf (nf done_) ≠ nf done_` — the
  `eval_unf_equiv` gap; semantic idempotence holds);
  (b) open-Γ neutral-vs-concrete is rejected both ways
  (LHS-only ascent — A6 from a different angle).

13 sorries unchanged.

### Open-Γ generalisation; eval_quotable closed (5862916f, 2026-04-19)

Three soundness-engineering forks on root obligations #3
and #4. Sorry counts after integration: Subtyping 1 +
SoundnessProof 13 + Soundness 3 = **17** (temporarily up
from 13 — the previously-implicit open-Γ obligations are
now named lemmas; dedup of closed/open forms in flight).

- **`eval_quotable`** (`eval-quotable-fork`, root #3): the
  unconditional form is **genuinely false** — `eval 2 _ []
  (.lam .type huge)` succeeds at fuel 2, but `quoteClosure`
  re-evals `huge` (unbounded). Closed via `(nf fuelω
  e).isSome` side-condition; the `nf` witness *is* the
  quote, transported via `eval_fuel_mono`. Axiom-clean
  `[propext, Quot.sound]`. `quote_total_on_eval` and
  `nf_asc_term_isSome` proven; `hnfe`/`hnfτ` threaded
  through `tyCheck_sound_closed` chain. DECISION-LOG
  2026-04-19. Soundness 4→3.

- **Open-Γ skeleton** (`open-gamma-fork`, root #4):
  `OpenCtx Γ ρ Γe` bundles `QuotesCtx` + ρ-quotable +
  eval-quote≡source. `subCheckVal_sound_open`,
  `tyCheckFallback_sound_open`, and `tyCheck_sound_open`'s
  `.asc`/`.fix`/`.iota`/catch-all arms **proven** (`.asc`
  is *shorter* than the closed form — no source-τ
  round-trip). Closed corollary derives at `OpenCtx.empty`
  + `substEnv_nil`. SoundnessProof 8→16 (the +8 are the
  named obligations). **Design finding**: `OpenCtx`'s
  `hρeq` was too strong for let-bound entries.

- **`OpenCtx` ρe-threading** (`openctx-rhoe-fork`):
  `OpenCtx Γ ρ Γe ρe` carries the explicit Expr-level
  substitution. `OpenCtx.push_fresh`/`push_let` **closed**
  (reduce to `eval_realises` + `R_depth_lift` +
  `eval_quotable_open`). `QuotesCtx.push` proven
  axiom-clean. SoundnessProof 16→13.

A dedup fork is replacing the closed `tyCheck_sound_*`
mutual block in Soundness.lean with corollaries of the
open forms; target is Soundness 3→0, SoundnessProof ≤13.

### Soundness.lean sorry-free; root #3 done (5862916f, 2026-04-19)

Dedup landed (`dedup-closed-open-fork`). The closed
`whnfPi_sound`/`tyInfer_sound_closed`/
`tyCheckFallback_sound_closed`/`tyCheck_sound_closed` are
now four short corollaries of `*_open` at `OpenCtx.empty`
+ `substEnv_nil`. The ~225-line mutual block deleted.
`eval_quotable_open` proven axiom-clean (the previous
`hρ`-only statement was also false; the per-call-site
`hnfq` evidence is the new `openNf_holds` — same shape as
the threaded `hnfe`/`hnfτ`).

**`Soundness.lean` is sorry-free.** All four target
theorems plus all closed-context supporting lemmas wired
through. **14 sorries** (Subtyping 1, SoundnessProof 13).
Three root obligations remain (root #3 `eval_quotable` is
done axiom-clean):
  1. Depth-tagged seen → `ctx_extend_at` + `Equiv.shift`
  2. `eval_realises` recursion-boundary → cascades to
     `quote_open_subst` + `SubV_to_Subtype'` chain
  3. Open-Γ residuals: `whnfPi_sound_open`/
     `tyInfer_sound_open`/`tyCheck_sound_open` `.lam`/
     `.letE`/`letBinderType_sound_open`/`openNf_holds`

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
