# Decision Log

Record significant design decisions here. Each entry should explain WHAT was
decided, WHY, and what alternatives were considered.

## 2026-04-18 — A6 reverted to `domA` (algorithmic blowup)

`subCheckValMatch`'s `.lam,.lam` arm pushes the *source*
domain `domA` into `tyCtx`, not the target `domB`.

**Why**: `domB` is more *complete* (so `(λx:Nat_. x) ⊑
(λx:zero_. zero_)` would pass) and matches `Subtype'.lam`,
but it makes `dthree ⊑ dNat` non-terminating in practice.
The cause is upstream of A6: `Closure.mk'` trims env to
`[0 .. max-referenced-index]`, so `dNat`'s inner-`let`
`dsucc_local` keeps `[dzero, fresh_self@d, vNat]` even though
its body never references env[1]. Each structural ι-open at
depth `d` therefore gives a structurally-distinct
`dsucc_local`; with `domB` (which references it via `s`'s
domain) the seen-list `==` check never fires and the
algorithm goes exponential. With `domA` (taken from the
*input* lambda, whose closures don't contain fresh vars) the
seen-list works as intended.

The clean build at `f2684c9` (first `domB` commit) only
"passed" the verifier on cached oleans; a clean rebuild
hangs at `Och.Std.DNat`.

**Status**: `domA` is *sound* (just incomplete on the A6
witness), so the Phase-2 soundness theorem is unaffected.
`SubV.lam` mirrors the algorithm at `Γ.push domA`; the
`SubV → Subtype'` bridge will need `Subtype'.narrow` for
the lam case. `divergenceSweep` now whitelists the one A6
divergence and asserts NbE only ever *under*-accepts.

**Plan**: mask unreferenced closure-env entries with a
canonical placeholder (so `Val.beq` identifies
`dsucc_local` across fresh-opens), then re-enable `domB`.
A worktree fork is exploring this.

**Alternatives considered**: (a) per-index env trim — what
`Closure.mk'` already does; insufficient since it keeps
gaps. (b) Quote-then-compare for the seen check — would
work but is O(quote) per check and breaks `LawfulBEq`.
(c) Two type contexts (domA for LHS-ascent, domB for
RHS-ascent) — there is no RHS-ascent in the current
algorithm, so this degenerates to (status quo).

---

## 2026-04-16: Split bundled `μ` into separate `ι` and `fix`

**Agents:** a27af1e65ebbe752d (full Och rewrite), ae69c738316f74ee5 + a1acb27814dafabf2 (Simple Och exploration)

**What:** Full Och's `Expr.mu (ann : Expr) (body : Expr)` is replaced by two
constructors:
- `Expr.iota (ann : Expr) (body : Expr)` — self-type. Intro rule uses
  value-substitution (Cedille-style): `a ⊑ ι A. b` if `a ⊑ A` ∧ `a ⊑ b[x := a]`.
- `Expr.fix (ann : Expr) (body : Expr)` — recursive binder. Equi-recursive:
  `fix A. b` unfolds to `b[x := fix A. b]` on both sides of `⊑`.

**Why:** Bundled `μ` was doing two jobs (dependent-elim self-typing AND
recursive structure) with one rule set, and the overlap caused persistent
transitivity walls. The Simple Och exploration on `research-iota-fix-split`
showed the split is structurally clean: each binder gets a narrower, well-
understood rule set. The split does NOT resolve the `dtrue ⊑ dBool`
obstruction on its own (that needs a separate β-conversion / DefEq rule),
but it unblocks reasoning about the two concepts independently.

**Alternatives considered:**
- Keep bundled `μ`: proof walls persisted across every extension attempt
  (BetaR, AppR, Mu-R, IotaR) — all hit the same cut-formula inflation.
- Fixed-self ι: tried first, found to be semantically equivalent to the old
  `Sub.mu` — voided the usefulness. Rejected.
- Value-substitution ι only (no fix): doesn't express recursive types
  (List, Stream) which full Och needs.

---

## Historical decisions (VCompat era, pre-rewrite)

The entries below are from the pre-split VCompat / soundness-proof era
(April 2026). They describe decisions about a codebase that has since been
substantially restructured. **Do not treat these as current guidance** —
the definitions they reference (bundled `μ`, `lenient` mode, VCompat's
mu-* disjuncts, etc.) no longer exist. They are retained as history for
agents investigating why particular design choices were made before.

---

## 2026-04-05: Replace isConcreteVal with ConcNF in VCompat semantic lam

**Agent:** ochre-20260405-091658

**What:** Replaced the VCompat semantic lam guard from `match aV with | .lam _ _
| .type | .mu _ _ => True | _ => False` to `ConcNF aV`, where `ConcNF` is a new
inductive characterizing ALL concEval output shapes (lam/type/mu and neutral apps).

**Why:** concEval CAN produce neutral applications (e.g., `app type type` when
the function is not callable). The old guard rejected these. Concrete counter-
example: `app (lam Type (bvar 0)) (app (bvar 0) (bvar 1))` with γV = [type, type].
The argument evaluates to `app type type`, but absEval succeeds because bvar 0 is
callable via inferType.

**Alternatives considered:**
- Prove concEval never produces neutral apps when absEval succeeds: FALSE (the
  counterexample above disproves it)
- Remove the guard entirely: breaks the soundness_open lam case because
  FunEnvCompat needs the guard to ensure γV entries are stable under concEval
- Keep old guard, handle app case separately: would require a completely
  different proof strategy for the app-result case

---

## 2026-04-05: Mu body evaluation at definition site — TESTED, DOES NOT WORK

**Agent:** ochre-20260405-091658

**What:** Tested the suggestion (SUGGESTIONS.md Phase 0) to check mu bodies at
definition site by binding self to annotation type and absEval'ing the body.

**Why it fails:** absEval FAILS on the body for Church-encoded types. When self
is bound to the annotation type as a bvar, the body evaluation encounters domain
check failures because self is abstract (bvar), and applying abstract variables
to arguments fails domain checks. Even without the body' ⊑ ann' subcheck, the
body evaluation itself fails with "domain check failed" for appendArrays.
Specifically: `absEval 5000 [] [] appendArrays = .error "domain check failed..."`.
This confirms why the original absEval only validated the annotation.

**Key insight:** The body of a mu type is NOT well-typed in the traditional sense
when self is treated as an opaque type variable. Self's well-typedness depends on
its RECURSIVE structure (mu unfolding), not just its declared type. Standard
recursive type checking binds self to the annotation and checks the body, but this
works in systems where self's type is fully informative (e.g., isorecursive types).
In Och, the annotation is an approximation (e.g., Type), and the body's behavior
under abstract self-reference doesn't match the annotation.

---

## 2026-04-05: Move annotation normalization from absEval to subCheckNF

**Agent:** ochre-20260405-020120

**What:** Changed absEval's mu case to keep raw annotations (validate but don't
normalize), and moved annotation normalization to subCheckNF's self-elim
annotation path (normalize on demand before comparing).

**Why:** The annotation normalization mismatch between concEval (keeps raw) and
absEval (normalized) was blocking 5+ sorrys. The soundness mu case needed
VCompat(v, τ) where v = mu ann body (raw) and τ = mu ann'.val body (normalized).
This required proving "annotation normalization congruence" — a deep lemma.

By keeping raw annotations in absEval output, both evaluators produce the same
mu term, making soundness mu trivial by VCompat.refl.

**Impact:** 7 sorrys eliminated (24 → 17). Eliminated the entire "annotation
normalization congruence" blocker from absEval_preserves.

**Alternatives considered:**
- WellAnnotated precondition: would weaken the theorem unnecessarily
- Normalizing in concEval: concEval and absEval handle asc differently, so
  their normalizations would produce different results
- Adding a VCompat disjunct for "same expression with different annotations":
  too invasive, would require updating every VCompat case split

**Risk:** Raw annotations in absEval output mean subCheckNF's self-elim must
normalize on demand. This adds an absEval call to the self-elim annotation
path, changing fuel consumption. All tests pass including the north star
(appendVec). fuel_mono proof updated and fully proved.

---

## 2026-04-05: Fundamental theorem of logical relations as path forward

**Agent:** ochre-20260405-044743

**What:** After exhaustive analysis of all 20 remaining sorrys, identified that
~8 are blocked by the **dual-substitution problem** (the single biggest blocker),
~4 by **self-elim step-count**, ~4 by **annotation-trust**, and ~4 by various
interaction effects. Proposed the **fundamental theorem of the logical relation**
as the path forward for the dual-substitution problem.

**The dual-substitution problem (detailed analysis):**

absEval normalizes lambda bodies: absEval(lam dom body) = lam dom'.val body'.val.
When this lambda is applied:
- concEval beta-reduces: bodyV.subst 0 aV (raw body, concrete arg)
- absEval beta-reduces: bodyT.subst 0 aT.val (normalized body, abstract arg)

The soundness IH is for the SAME expression evaluated by both evaluators.
body.subst 0 aV ≠ body'.val.subst 0 aT, so the IH can't be applied.

**Approaches explored and REJECTED:**
1. Raw lam bodies in absEval: breaks ALL tests (agents 031505, 040204)
2. Single-expression semantic lam: body mismatch remains
3. Extracting semantic lam from VCompat: refl disjunct blocks
4. Ascription-based arguments: doesn't help after beta-reduce
5. Strong fuel induction: doesn't help (different expressions, not fuel)
6. Normalization-substitution commutation: the lemma
   "absEval(body.subst 0 arg) = absEval(body'.val.subst 0 arg)" is FALSE
   in general. Counterexample: body = asc (bvar 0) (lam Type Type),
   absEval(body) = ⟨lam Type Type⟩. Then body.subst 0 arg = asc arg (lam Type Type)
   which FAILS if arg's type doesn't subcheck against lam Type Type, while
   body'.val.subst 0 arg = lam Type Type which succeeds trivially.
   (When both succeed, the results may be the same by confluence, but the
   conditional version is complex to prove.)

**Why the fundamental theorem approach works:**

Standard logical relations prove soundness by induction on the TYPING DERIVATION
(or expression structure), not on fuel. The key difference:

- Current approach (fuel induction): IH gives soundness for THE SAME expression
  at lower fuel. Can't handle different expressions.
- Fundamental theorem (expression induction): IH gives soundness for SUB-TERMS
  with EXTENDED environments. The lam body is a sub-term, so the IH applies
  directly, with the lambda parameter added to the environment.

Specifically:

```
theorem soundness_open
    (fuel : Nat) (ctx : TyCtx) (e : Expr) (τ : NfExpr)
    (h_abs : absEval fuel ctx [] e = .ok τ)
    (n : Nat) (γV γT : List Expr)
    (h_env : ∀ i, i < ctx.length → VCompat n (γV[i]) (γT[i]))
    (v : Expr)
    (h_conc : concEval fuel (e.substEnv γV) = some v)
    : VCompat n v (τ.val.substEnv γT)
```

For the lam case (e = lam dom body):
1. absEval gives τ = ⟨lam dom'.val body'.val⟩
2. concEval gives v = lam (dom.substEnv γV) (body.substEnv (shift γV))
3. For the semantic lam, given VCompat(j, aV, aT):
   - Use IH on BODY (structurally smaller!) with extended env: aV :: γV, aT :: γT
   - body.substEnv (aV :: γV) and body'.val.substEnv (aT :: γT)
   - By IH: VCompat(j, concEval(body.substEnv (aV :: γV)), absEval result)
   - This works because BOTH sides use the SAME body sub-expression, just with
     different environments applied through substEnv.

**Required infrastructure:**
1. `substEnv`: simultaneous substitution by an environment (List Expr → Expr → Expr)
2. Substitution lemmas: substEnv composition with single subst, shifting, etc.
3. `EnvCompat`: environment compatibility definition
4. The fundamental theorem (soundness_open), proved by induction on expression
5. Original soundness as corollary (empty environments)

**Estimated effort:** 300-500 lines of new Lean code. The main challenge is
defining substEnv correctly for de Bruijn indices and proving the substitution
composition lemmas. The actual fundamental theorem proof should follow standard
logical relations patterns once the infrastructure is in place.

**Self-elim step-count issue (secondary blocker):**

The self-elim cases in adequacy_gen (σ = mu, τ ≠ mu) are blocked by VCompat's
mu-right disjunct costing one step. From VCompat(m+1, v, mu ann body):
- mu-right gives VCompat(m, v, body.subst) — lost one step
- After adequacy: VCompat(m, v, τ) — need VCompat(m+1, v, τ)

All sub-cases of the VCompat decomposition work for seen = [] (the common
case), but fail for non-empty seen due to the callback mismatch: the callback
provides VCompat for the original v, but the proof needs VCompat for the
transformed v' (body.subst for mu-left, ty for inferType, term for asc-left).

The standard fix: dual-budget VCompat (one budget for observations, one for
type unfoldings) or Löb induction. Both require significant VCompat restructuring.

**Circular dependency in absEval_preserves:**

The refl-asc sorry (line 437) needs adequacy_gen, but adequacy_gen uses
absEval_preserves. However, adequacy_gen's uses of absEval_preserves only
process types from inferType (which never produces asc at top level), so the
circular call never fires in practice. This could be resolved by:
- Proving specialized combined lemmas (bvar_inferType_preserves)
- Or accepting the sorry as non-critical (it doesn't arise at use sites)

---

## 2026-04-05: Raw lam body + on-demand normalization ALSO REJECTED

**Agent:** ochre-20260405-040204

**What:** Tested a variant of the raw lam body approach: keep raw body in absEval
AND normalize bodies on demand in subCheckNF's lam-lam case. This addresses the
domain-inside-body issue by normalizing bodies before structural comparison.

**What was changed:**
1. absEval lam: `let _ ← absEval fuel ctx seen body; .ok ⟨.lam dom'.val body⟩`
2. subCheckNF lam-lam: `match absEval fuel ... bodyA, absEval fuel ... bodyB with | .ok bodyA', .ok bodyB' => ...`

**Why it FAILED:** The fundamental issue is that absEval's output IS the normalized
form. Tests check `absEval 200 [] [] expr = Except.ok { val := expected }` via
`native_decide`. With raw bodies, even `succ_.app two_` gives a wrong result
because the intermediate lam has a raw body, and the test expects a normalized one.

**Key insight:** The mu annotation change worked because mu annotations are
"internal" — they flow only to subCheckNF's self-elim, not to absEval's observable
output in a way tests check. Lam bodies are "external" — they appear directly in
absEval's output and are checked by tests. There's no way to keep raw bodies
without changing the observable output, which breaks all computation tests.

**Conclusion:** All 3 variants of the raw body approach have been tested and
rejected. The dual-substitution problem must be solved at the proof level (not
the definition level). The remaining approaches are:
1. Generalized soundness for compatible expression pairs (substitution lemma)
2. Biorthogonality / observational VCompat

---

## 2026-04-05: Raw lam body approach REJECTED

**Agent:** ochre-20260405-031505

**What:** Attempted to apply the same "keep raw, normalize on demand" strategy
from mu annotations to lam bodies. Changed absEval's lam case to return
⟨lam dom body⟩ (raw) instead of ⟨lam dom'.val body'.val⟩ (normalized), and
updated subCheckNF's lam-lam case to normalize bodies on demand via absEval.

**Why it was attempted:** Would make soundness lam case trivial by VCompat.refl
(concEval and absEval both return the same raw lam). This is the same insight
that made soundness mu trivial.

**Why it FAILED:** Raw lam bodies contain raw DOMAINS in nested lams. When these
lams are applied later (in absEval's app case), the domain check
`subCheckNF fuel ctx seen a'.val dom` compares the argument against a raw domain
like `app (app Pair_ Nat_) Nat_` instead of the normalized Pair type. subCheckNF
can't handle this comparison.

The mu annotation change worked because annotations are only consumed by
subCheckNF (which was updated to normalize on demand), never by absEval's
direct domain check. For lams, the domain appears in TWO places: subCheckNF's
lam-lam comparison AND absEval's app-case domain check. Updating both would
require normalizing domains on demand inside the app case, adding significant
complexity.

**Variant tested:** Keep normalized domain but raw body (`.ok ⟨.lam dom'.val body⟩`).
This partially works but: (a) v ≠ τ.val (different domains), so refl doesn't apply,
and (b) the semantic lam still has the dual-substitution problem (aV vs aT).

**Impact on approach:** The "normalize on demand" strategy has reached its limit.
The remaining soundness blockers (lam/app) require a different approach — either
a generalized soundness theorem, a change to VCompat's semantic lam definition,
or an entirely new proof strategy.

---

## 2026-04-05: Fix self-elim to restore transitivity (two changes)

**Agent:** ochre-20260405-013043

**Decision:** Two changes to subCheckNF's self-elim case:

1. Body check uses original `seen` (not `seen'`):
```lean
| .ok u' => subCheckNF fuel ctx seen u'.val b   -- was: seen'
```

2. Annotation path guarded by `body != bvar 0`:
```lean
if body != .bvar 0 && subCheckNF fuel ctx seen' ann b then true
```

**Why (change 1):** The self-elim entry in seen' enabled circular reasoning.
Non-productive fixpoints like `mu Type (bvar 0)` unfold to themselves,
hit the seen entry, and succeed trivially.

**Why (change 2):** Even after change 1, `mu ann (bvar 0) ⊑ ann` succeeded
via the annotation path (ann ⊑ ann by equality). Since mu ann (bvar 0) is
universal (everything subtypes it via self-intro), this created a bridge for
transitivity violations: `a ⊑ mu ann (bvar 0) ⊑ ann` but `a ⋢ ann`.
Found via exhaustive testing on edge-case expressions.

**Why `body != bvar 0` specifically:** Only pure self-reference bodies are
non-productive. All standard library mus (dNat, dBool, Array, Vec) have
lambda bodies that expose constructor structure when unfolded. The guard
doesn't affect them.

**Alternatives considered:**
1. Validate annotations at mu creation (breaks Church-encoded types)
2. Remove annotation path entirely (breaks DNat/Vec body normalization)
3. Check post-normalization progress instead of syntactic guard
   (changes control flow, harder to maintain)

**Validation:** All tests pass. Added 3 exhaustive transitivity test suites
(~30 expressions × 3 triples each) covering Std types, nested mus, and
self-referential patterns.

**Impact on proofs:** Fuel_mono updated (handle Bool.and in annotation guard).
Self-elim body path in adequacy_gen unblocked from circular callback.

---

## 2026-04-05: Add asc-left disjunct to VCompat

**Agent:** ochre-20260405-003633

**Decision:** Added a 10th disjunct to VCompat:
```lean
∨ (∃ term tyAsc, v = .asc term tyAsc ∧ VCompat n term τ)
```

**Why:** `absEval_preserves` was FALSE without it. Counterexample:
v = e = `asc (lam Type (bvar 0)) (lam Type Type)`, n=2. VCompat(2, v, v) holds
via refl, but absEval(v) = ok ⟨lam Type Type⟩ and VCompat(2, asc(...), lam Type Type)
had no way to hold — no existing disjunct could handle asc on the value side.

**Semantics:** The disjunct is correct because concEval erases ascriptions —
`(e : τ)` at runtime behaves like `e`. The asc-left disjunct costs one step
(VCompat n+1 → VCompat n) to prevent infinite chains.

**Why it's needed:** mu-left unfolding in adequacy_gen introduces `body.subst 0 (mu ...)`
as the value, and body can contain asc nodes from let-bindings etc.

**Alternatives considered:**
1. Restricting absEval_preserves to v being a concEval output (too narrow —
   mu-left recursion in adequacy_gen passes non-value v's)
2. Adding IsNotAsc precondition (doesn't hold for mu-left unfolded values)
3. Avoiding absEval_preserves entirely (would need completely different proof strategy)

**Impact:** All existing proofs updated (VCompat.mono, bvar_inferType, adequacy_gen).
The asc-left case is always handled by recursion (IH or ih_n).

---

## 2026-04-04: Clear `seen` in structural subCheckNF recursive calls

**Agent:** ochre-20260404-224040

**Decision:** Changed subCheckNF's lam-lam and app-app structural cases to
use empty `seen` `[]` instead of propagating the outer seen set.

**Why:** The outer `seen` set contains equi-recursive assumptions like
(σ, mu ann body) with VCompat callbacks in adequacy_gen tied to the original
value `v`. When the proof needs to recurse into structural sub-components
(e.g., f1→f2 in app-app), the callback would need VCompat for the
*sub-component* (fV), not the original v. This mismatch was the fundamental
blocker for proving app-app structural congruence in adequacy_gen.

By clearing seen in structural recursive calls, the callback becomes vacuous
(empty seen = no callback), enabling the proof.

**Alternatives considered:**
1. Strengthen the seen callback to `∀ v, VCompat n v p.1 → VCompat n v p.2`
   (too strong — fails for from_type_sub_gen)
2. Prove `subCheckNF with seen → subCheckNF with []` (wrong direction — more
   seen pairs make subCheckNF succeed more, not less)
3. Keep the definition and accept the app-app case can't be proved (unacceptable
   — app-app is a core case)

**Validation:** All tests pass including the north star (appendVec). The
structural recursive calls don't benefit from equi-recursive assumptions
anyway — they compare structural sub-parts (domains, bodies, function/arg
components), not the mu types that the seen set tracks.

**Impact:** Enables the app-app structural congruence proof in adequacy_gen
(all 4 VCompat sub-cases). Also prepares the lam-lam case for future work.
Fuel_mono proof required minor update (changing `seen` to `[]` in `show`
clauses).

## 2026-04-16: Phase 2 soundness audit — three gaps identified

`lean/Och/SoundnessAudit.lean` records each as a `native_decide`
theorem about the *current* checker behaviour, paired with a
witness that the behaviour is wrong. Fixing a gap will make the
file fail to compile, prompting an update.

**A1 — covariant neutral-app congruence.** `subCheckNeutral`'s
`.app, .app` arm (and the `.stuckRec, .stuckRec` arms in both
`subCheckNeutral` and `subCheckVal`) accept `n a ⊑ n b` whenever
`a ⊑ b`. Sound only if `n` is covariant in its argument, which
isn't tracked. Concrete witness: `Pair zero_ unit_ ⊑ Pair Nat_
Unit_` is accepted, but eliminating both with `λn. λu. n → Unit_`
gives `zero_ → Unit_ ⊄ Nat_ → Unit_` — substitution-principle
violation. This is *by design* (Pair.lean's doc names "app
congruence" as the mechanism); the design is unsound. Fix:
restore bidirectional comparison; re-encode `Pair` with a
separate value constructor (like `dpair`/`Sigma`) so concrete
pairs inhabit `Pair A B` via type-ascent rather than congruence.
Affected tests: Pair.lean:56/59, Array.lean:86/88.

**A2 — type-in-type.** `_ ⊑ Type → true`. Admits Girard's
paradox. Almost certainly intentional (Pair.lean's `fst_`/`snd_`
rely on it). Fix is universe stratification (mechanical but
invasive) or accepting Type:Type as a model axiom. The Phase-2
theorem should be stated modulo this.

**A3 — β is type-blind.** `subCheckNF`/`NbE.subCheck` normalise
first, so `(λn:Nat_. n) Bool ⊑ Bool` is accepted. `NbE.typeCheck`
(TyCheck.lean) catches it. The Phase-2 theorem should target
`typeCheck`, not `subCheck`.

**Decision**: The Phase-2 soundness statement is

> `NbE.typeCheck fuel e τ = .ok true → ⟦e⟧ ∈ ⟦τ⟧`

with A1 fixed (bidirectional neutral args, Pair re-encoded) and
A2 taken as a model axiom (`⟦Type⟧ = universe of all values`).
The architecture follows `Och/Simple/CheckSoundness.lean`:
algorithmic → declarative `Subtype'` → semantic model.
