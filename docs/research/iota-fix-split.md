# Iota/Fix Split: Design, Prototype, and Honest Assessment

**Branch:** `research-iota-fix-split`
**Worktree:** `/home/charlielidbury/repos/ochre-iota-fix-split`
**Status:** Prototype complete. Split metatheory largely works. **Target
theorem `dtrue ⊑ Bool` is NOT closable** — obstruction is orthogonal to
the ι/fix split.

## Background

Historical Simple Och had one `μ self:A. body` constructor bundling two
distinct concepts:

1. **`fix`**: recursive reference — `body` may mention `self`
   recursively to define a recursive type (e.g., `List = μself. ⊤ +
   (Nat × self)`).
2. **`ι` (iota)**: self-typing — a value `v : ι x. T` has type `T[x :=
   v]`, enabling dependent elimination (e.g., Church-encoded Bool with a
   motive).

Prior research (`research-iota-impl`, `research-precise`) identified a
"contravariant wall" where every transitivity rule that substitutes into
a μ-body can inflate the cut formula, and contravariant self-occurrences
drive productive cycles.

The user's hypothesis: **splitting the concepts lets each binder get
narrower rules, and makes the "dependent Bool with `cBool`-domain
motive" case provably sound.**

## Design chosen

### Syntax

Two new constructors, each with an annotation:

```lean
Expr.iota (ann : Expr) (body : Expr)  -- ι A. b, body binds self = bvar 0
Expr.fix  (ann : Expr) (body : Expr)  -- fix A. b, body binds recref = bvar 0
```

Both participate in shift/subst identically (body shifted at cutoff + 1).

### Subtyping rules

Added **three** new rules on top of the 7-rule baseline:

1. **`iotaIntro`** (self-type intro, RHS):
   ```
   Γ ⊢ a ⊑ ι A. b   ←   Γ ⊢ a ⊑ A   ∧   Γ ⊢ a ⊑ b[0 := ι A. b]
   ```
   Uses the **fixed-self** substitution (the iota itself, not the value
   `a`). This is what `research-iota-impl` proved sound with zero sorrys
   in Properties.lean.

   The precise form (`b[0 := a]`) was considered and rejected: its
   transitivity proof fails in the iotaIntro × iotaIntro case, because
   the cut formula `ι A. b` has different substitutions in the two
   derivations. With fixed-self, the cut stays intact and induction on
   derivation size closes it.

2. **`fixAnn`** (recursive type annotation-only):
   ```
   Γ ⊢ a ⊑ fix A. b   ←   Γ ⊢ a ⊑ A
   ```
   A weak, annotation-only rule. The RHS `fix A. b` is treated as
   opaque; only the annotation `A` is checked. Trivially sound.

3. **`unfoldFixL`** (equi-recursive LHS unfolding):
   ```
   Γ ⊢ fix A. b ⊑ c   ←   Γ ⊢ b[0 := fix A. b] ⊑ c
   ```
   Unfolds a fix on the LHS. Cut formula `b[...]` may be LARGER than
   `fix A. b`, so this rule is **not cut-measure-safe** in general — see
   obstruction below.

### Rules deliberately NOT added

- **`iotaElim`** / **`unfoldIotaL`**: not needed for the target
  theorem. Adding them would mirror `unfoldFixL` and create the same
  cut-measure obstruction.
- **`fixFold`**: an RHS iso-recursive intro. Would require explicit
  fold/unfold terms in the language; not in scope.

## Metatheory analysis (rule by rule)

For each new rule, does the lex measure `(cut.complexity,
derivation_size_sum)` shrink?

### `iotaIntro`

Cases where `iotaIntro` appears as `hbc` (RHS):
- `refl × iotaIntro`, `top × iotaIntro`, `lam × iotaIntro`, `ascR ×
  iotaIntro`: rebuild via `iotaIntro` with the same cut formula.
  Sizes decrease. **Closes.**
- `iotaIntro × iotaIntro`: rebuild via iotaIntro; the cut formula
  `iota A_mu body_mu` is preserved across the two sub-calls (they
  retarget RHS to A' and body'). Size strictly decreases. **Closes.**

Cases where `iotaIntro` appears as `hab` (LHS, i.e., cut = iota):
- `iotaIntro × refl`: trivial.
- `iotaIntro × top`: return `Sub.top`.
- `iotaIntro × ascR`: standard peel.
- `iotaIntro × iotaIntro`: as above.
- `iotaIntro × fixAnn`: compose hab and hbc's premise.

All cases close cleanly. **ZERO sorrys for iotaIntro in Properties.**

### `fixAnn`

The premise is `Sub Γ a A` — no recursion into the body. Trivially
well-behaved for trans/narrow/subst.

- As `hbc`: same pattern as iotaIntro cases, always reconstructible.
- As `hab`: premise lifts to any `c` via trans with the cut.

All cases close **except** `fixAnn × unfoldFixL` (see below).

### `unfoldFixL`

- As `hab`: `hab: Sub Γ (fix A b) b0`; trans with `hbc: Sub Γ b0 c`
  gives `Sub Γ (body[fix]) c`, then lift back via `unfoldFixL`. This
  **closes** via size reduction on the premise.
- As `hbc`: only applies when cut `b = fix A body`. The only hab cases
  that produce a `fix` LHS are:
  - `refl × unfoldFixL`: trivial.
  - `fixAnn × unfoldFixL`: **obstruction**. See below.

### The `fixAnn × unfoldFixL` obstruction (SORRY)

```
hab: Sub Γ a (fix A_fix body_fix)       from habA: Sub Γ a A_fix
hbc: Sub Γ (fix A_fix body_fix) c       from hbcUnf: Sub Γ (body_fix.subst 0 (fix...)) c
goal: Sub Γ a c
```

We have `a ⊑ A_fix` and `body_fix[fix] ⊑ c`. But we need `a ⊑ c`, which
requires a bridge. Options:

1. Compose: `Sub Γ a (body_fix[fix])` via some rule, then trans with
   hbcUnf. But what rule produces that? None — `a` isn't necessarily a
   fix, and `A_fix` isn't necessarily related to `body_fix[fix]`.

2. Unfold `a` too. But `a` isn't a fix.

3. Use `fixAnn` on the goal: need `a ⊑ c` where `c = fix ..` if that
   shape persists. But c is whatever; could be anything.

**This is the canonical equi-recursive + annotation obstruction**:
`fixAnn` is too weak (only annotation), and `unfoldFixL` drops the fix
entirely. There's no way to bridge them without either:

- Adding a `fixUnfoldR` rule (equi-recursive on RHS too) — but then
  the cut-measure for the iotaIntro × fixUnfoldR case breaks (body[fix]
  can grow without bound).
- Requiring well-typedness invariants that ensure `A_fix` is compatible
  with `body_fix[fix]` — but "compatible" = Sub relation, circular.
- Using coinduction / step-indexing.

**Conclusion for `unfoldFixL`**: sound in isolation, but incompatible
with `fixAnn` in transitivity. For the target theorem we don't use
`unfoldFixL`, so this sorry doesn't block the whiteboard goal — but it
means the fix rules aren't a complete drop-in replacement for the
bundled μ.

## The whiteboard theorem: `dtrue ⊑ Bool`

```
cBool = λA:⊤. A → A → A
true  = λA:⊤. λt:A. λf:A. t
Bool  = ι self:cBool. λP:(cBool → ⊤). P true → P false → P self
dtrue = true
```

### What closes cleanly

- `cTrue ⊑ cBool`: standard Church-Bool argument. Proved in
  `Challenge.lean`.
- `cTrue ⊑ ι ⊤. cBool`: trivial iota where body doesn't use self.
  Proved in `Challenge.lean` via `iotaIntro`, annotation leg by
  `Sub.top`, body leg closes because `cBool.subst 0 (...)` = `cBool`
  (cBool is closed).

### What doesn't close: `dtrue ⊑ Bool`

The only entry for `Sub [] cTrue Bool` is `iotaIntro`. This produces
two sub-goals:

1. `cTrue ⊑ cBool` ✓ (proved).
2. `cTrue ⊑ body.subst 0 Bool`.

Sub-goal (2) unfolds to

```
cTrue ⊑ λP:(cBool→⊤). λt:(P cTrue_s). λf:(P cFalse_s). (P Bool_s)
```

(with subst replacing `self` by `Bool` shifted appropriately; or
by `cTrue` in the precise form — both have the same obstruction.)

[Lam] decomposition under `[cBool→⊤]` context then reaches, at the
second level, a contravariant domain check:

```
app (var 0) cTrue ⊑ (var 0)     -- where var 0 = cBool→⊤
```

Via [App]:
- `(var 0) ⊑ λD.R`: via [Var], `cBool→⊤ = λ_:cBool. ⊤ ⊑ λD.R`, forcing
  `D = cBool, R = ⊤`.
- `cTrue ⊑ cBool` ✓.
- `R[0 := cTrue] = ⊤ ⊑ (var 0) = cBool→⊤`. **FALSE.**

`⊤` is the top of the universe; it is not a subtype of a specific
function type.

### This is NOT a ι/fix problem

Every rule mentioned above — `[App]`, `[Var]`, `[Top]`, `[Refl]`,
`[Lam]` — is in the **baseline 7-rule Simple Och**. The obstruction
has NOTHING to do with ι, fix, self-types, or recursion.

The obstruction is: Simple Och has no `[BetaL]` or `[DefEq]` rule, so
it cannot reduce `(λ_:cBool. ⊤) cTrue → ⊤` syntactically. Even WITH
beta, the post-reduced check `⊤ ⊑ cBool→⊤` is still false — so the
Bool encoding with `P : cBool→⊤` fundamentally requires more than just
beta.

### What would unblock `dtrue ⊑ Bool`?

Not a ι/fix change. Candidate ingredients:

1. **Change the encoding.** E.g., `Bool = ι self. λP:⊤. P true → P
   false → P self` (P opaque). But `app ⊤ cTrue` isn't a sensible term
   either — you can't apply top. Every "natural" simplification runs
   into a similar wall.

2. **Add a weakening-away rule**: `a ⊑ b` when RHS is a lam-shape
   whose body position can absorb an ⊤. E.g., a widening rule like
   `⊤ ⊑ λ_:A. ⊤` for any A? This would be unsound (⊤ can't be viewed
   as a function).

3. **Add a proof-irrelevant universe** where `⊤` serves as a dummy type
   for predicate motives. Then `P : cBool→⊤` inhabitants really are
   type-families, and `(⊤ ⊑ cBool→⊤)` might hold in a universe-level
   subtyping sense. This is a deep change to the calculus.

4. **Full logical-relations / semantic soundness**. Escape syntax.

## Which rules need coinduction / step-indexing / seen-set?

- **`iotaIntro`** with **fixed-self** substitution: **no coinduction
  needed**. The iota-impl branch and this branch both prove trans
  inductively. Clean.
- **`iotaIntro`** with **precise** substitution: needs coinduction or
  seen-set for the iotaIntro × iotaIntro case (cut formula's body is
  substituted with different values on the two sides — they may not
  match).
- **`fixAnn`**: no coinduction needed.
- **`unfoldFixL`**: no coinduction needed IN ISOLATION, but the
  `fixAnn × unfoldFixL` trans case needs either a "bridge" rule (not
  obvious how to add without unsoundness) or a well-typedness premise
  (which is circular) — so in practice, needs either coinduction or a
  restricted form of fix (e.g., strictly positive, guarded).
- **Contravariant self-references** in ι-bodies (e.g., `ι self. self →
  ⊤`): productive cycles. Need seen-set or coind. Not relevant to the
  whiteboard (Bool has only covariant self-refs).

## Concrete recommendation: is this worth merging to main?

### Pros

- The split IS cleaner metatheorically. Each binder gets narrower
  rules.
- `iotaIntro` (fixed-self form) has a fully-proven trans/narrow/subst.
- Zero sorrys in the core metatheory for iota. Only 1 sorry for fix
  (`fixAnn × unfoldFixL`), which is a known obstruction.
- Evaluator extension is straightforward (iota is a value; fix unfolds).

### Cons

- Does NOT unlock `dtrue ⊑ Bool`. The obstruction is structural, not
  related to ι/fix.
- Adds two constructors + three rules + 3 sorrys in Soundness (eval
  preservation for iota/fix cases), which are fixable but take work.
- Without `dtrue ⊑ Bool` working, the motivation for the split is
  weakened. We're paying complexity cost without landing the theorem.

### Recommendation

**DO NOT merge to main as-is.** The split is a net complexity increase
without a payoff theorem. Main's 7-rule system is the provably-sound
maximum.

**DO keep the branch** as reference for:
- The clean `iotaIntro` pattern for future exploration.
- The honest finding that the whiteboard encoding's obstruction is in
  [App]'s `⊤ ⊑ arrow` wall, not in the ι/fix rules.

**Next experiment to unblock `dtrue ⊑ Bool`**: investigate adding
[BetaL] / [DefEq] independently of ι/fix. If that unblocks a simpler
self-typed theorem (perhaps `dtrue ⊑ (ι self. self)` or similar) in
combination with iotaIntro, the combined split + DefEq might be worth
merging.

## Files modified on this branch

- `lean/Och/Simple/Syntax.lean`: added `.iota` and `.fix` constructors,
  shift/subst extended, supporting lemmas (`shift_zero`,
  `subst_shift_cancel`) extended.
- `lean/Och/Simple/Subtype.lean`: added `Sub.iotaIntro`, `Sub.fixAnn`,
  `Sub.unfoldFixL`.
- `lean/Och/Simple/Properties.lean`: added iota/fix cases to all
  shift/subst/complexity/size lemmas; added iota/fix cases to
  `weaken_gen`, `transNarrowInner` (1 sorry: fixAnn × unfoldFixL), and
  `subst_gen_aux` (0 sorry).
- `lean/Och/Simple/Eval.lean`: iota is a value, fix unfolds on eval.
- `lean/Och/Simple/Soundness.lean`: added iota/fix cases to all eval
  helpers (eval_mono, eval_produces_value, eval_idempotent,
  eval_app_head_result, eval_result_sub_lam_not_app). Added 3 sorrys in
  `evalPreservation_aux` for the iota/fix/app-iota cases.
- `lean/Och/Simple/Check.lean`: iota/fix make the checker return false
  (checker doesn't support them; iotaIntro etc. are declarative-only).
- `lean/Och/Simple/Challenge.lean`: NEW file with the whiteboard target
  theorem attempt. Proves `cTrue ⊑ cBool` and `cTrue ⊑ ι ⊤. cBool`,
  sorries `dtrue ⊑ Bool` with detailed diagnosis of the obstruction.

## Sorry inventory on this branch

| File | Line | What | Why |
|------|------|------|-----|
| Properties.lean | ~641 | `fixAnn × unfoldFixL` trans | No bridge between annotation-only LHS and equi-recursive RHS |
| Soundness.lean | ~413 | `app` case where f = `.iota` | Needs lam-inversion for iota-on-LHS |
| Soundness.lean | ~425 | `iotaIntro` eval preservation | Needs LHS eval closure for iota-RHS |
| Soundness.lean | ~433 | `fixAnn` eval preservation | Needs fuel-monotone unfolding for fix |
| Challenge.lean | ~203 | `dtrue ⊑ Bool` target | Structural [App] obstruction (not ι/fix) |
| SubstLemmas.lean | pre-existing | - | not modified |

The **1 metatheory sorry** in Properties is the only one that's
fundamental to the split. The Soundness sorrys are fixable with work
(not attempted here due to scope). The Challenge sorry is the honest
finding: the target theorem is blocked on a different wall.

---

## Value-substitution attempt (follow-up)

After the initial fixed-self implementation above, we also tried the
Cedille-style **value-substitution** formulation:

```
iotaIntro:  a ⊑ ι A. b   ←   a ⊑ A   ∧   a ⊑ b[0 := a]
```

Rationale: the fixed-self rule substitutes the iota *type* into its own
body, which makes it effectively equi-recursive unfolding — not
self-typing. Only value-substitution yields `v : P v` style dependent
eliminations. `research-precise` proved value-sub closes inductively
for covariant self-occurrences, and Bool's self occurs covariantly in
`P self`, so on paper value-sub should work for the whiteboard Bool.

### What changed

* `Subtype.lean`: `iotaIntro`'s second premise changed from
  `Sub Γ a (b.subst 0 (.iota A b))` to `Sub Γ a (b.subst 0 a)`.
* `Properties.lean`:
  * `weaken_gen.iotaIntro`: shift-commutes on `b.subst 0 a` (simpler
    than the fixed-self form because there's no iota-reconstruction
    needed).
  * `narrow_gen.iotaIntro`: `body_mu.subst 0 a` instead of
    `body_mu.subst 0 (.iota ...)`.
  * `subst_gen_aux.iotaIntro`: uses `subst_subst` on `body_mu.subst 0 a'`
    to commute the two substitutions.
  * **6 transitivity cases for `iotaIntro` as RHS became sorrys**:
    all cases of trans with `hbc = iotaIntro(hbcA, hbcBody)` where
    `hbcBody : Sub Γ b_cut (body'.subst 0 b_cut)`. Composing with
    `hab : Sub Γ a b_cut` gives `Sub Γ a (body'.subst 0 b_cut)`, but
    the value-sub iotaIntro needs `Sub Γ a (body'.subst 0 a)`. The
    self-substitution value changes from `b_cut` to `a`, which has no
    inductive bridge.
* `Challenge.lean`: body leg of `dtrue ⊑ Bool` now unfolds to
  `dtrue ⊑ BoolBody.subst 0 dtrue` (value-sub form).

### Transitivity cut-measure analysis for value-sub

Goal of trans: given `hab : Sub Γ a b_cut` and `hbc : Sub Γ b_cut c`,
build `Sub Γ a c`. The lex measure is `(b_cut.complexity, sizes)`.

For `iotaIntro × iotaIntro`:
* `b_cut = ι A_mu. body_mu`, complexity `1 + A_mu.cplx + body_mu.cplx`.
* hab's body leg: `Sub Γ a (body_mu.subst 0 a)` — cut `body_mu.subst 0 a`
  has complexity `body_mu.cplx + k·a.cplx` where `k` = number of free
  self-refs in body_mu (shift-invariance of complexity). If `a` is
  complex and self occurs multiply, this cut can be much larger than
  `b_cut`.
* **Shrinkage requires `a.complexity · k < 1 + A_mu.complexity`**, i.e.
  the LHS value must be "smaller" than the iota's annotation. This is
  an **admissibility condition**, not a structural decrease.

For the whiteboard `dtrue ⊑ Bool`:
* `dtrue.complexity = cTrue.complexity = 4` (3 lams + 1 nested var).
* `cBool.complexity = 4` as well.
* `BoolBody` has **one** self-occurrence at the deepest position, so
  `k = 1`. Then `dtrue.cplx · 1 = 4 < 1 + cBool.cplx = 5`. ✓ Borderline!
  So the cut-measure **would shrink** for this specific case. But the
  general rule isn't structurally safe.

### Does the derivation close?

**No.** The obstruction is unchanged from fixed-self.

After `Sub.iotaIntro` the body leg is
`dtrue ⊑ BoolBody.subst 0 dtrue`. Computing:

```
BoolBody.subst 0 dtrue =
  .lam cBoolToTop
    (.lam (app (var 0) cTrue)
      (.lam (app (var 1) cFalse)
        (app (var 2) dtrue)))   -- was (var 3), self-ref → dtrue
```

Only the `var 3 = self` position at depth 3 is affected by the
value-sub. Every other position (`var 0`, `var 1` in the domain
annotations) refers to lambda binders, not self.

Second [Lam] decomposition reaches the contravariant domain check
`app (var 0) cTrue ⊑ var 0` in context `[cBoolToTop]`. Here `var 0`
looks up `cBoolToTop = cBool → ⊤`. Via [App] on the LHS:

```
(var 0) ⊑ λD. R    (via [Var]: D = cBool, R = ⊤)
cTrue ⊑ cBool      ✓
R[0 := cTrue] = ⊤ ⊑ var 0 = cBoolToTop   -- FALSE
```

**This is exactly the same wall the fixed-self attempt hit.** The
obstruction is not in any self-position; it is in the [App]
decomposition of `P cTrue` against `cBoolToTop`, which requires
showing `⊤ ⊑ cBool → ⊤` (top isn't a subtype of an arrow).

### Comparison to the prior (fixed-self) obstruction

| Aspect | Fixed-self | Value-sub |
|---|---|---|
| Trans metatheory | All closes, 0 sorrys (for iota) | 6 sorrys on `iotaIntro × iotaIntro` family |
| Cut-measure | Structurally safe (cut = iota preserved) | Conditional on `a.cplx < 1 + A.cplx` per self-ref |
| Whiteboard goal | Body leg forms `dtrue ⊑ BoolBody.subst 0 Bool`, same [App] wall | Body leg forms `dtrue ⊑ BoolBody.subst 0 dtrue`, **same** [App] wall |
| Self-typing semantics | Equi-recursive unfolding (no real dep elim) | True value substitution (`v : P v` derivable *in principle*) |

The obstruction is identical. Value-sub makes the body-leg substitution
"correct" semantically but does not reach the contravariant wall.

### What value-sub *would* close (counterfactual)

If we could somehow close the `⊤ ⊑ cBoolToTop` wall (e.g. via a
structural-eta rule or beta-reduction LHS), value-sub would then reach
the deepest body position `app (var 2) dtrue`. The LHS at that depth
would also be `var 1` (referring to `t` binder, dtrue is the first arg
of cTrue = `λA.λt.λf. t`). The RHS would be `app (var 2) dtrue`.
[Var] on the LHS gives type `(app (var 1) cTrue).shift 0 1 = app (var 2) cTrue`
in context `[app (var 1) cFalse, app (var 0) cTrue, cBoolToTop]`.

We'd then need `app (var 2) cTrue ⊑ app (var 2) dtrue`. By [App]:
* `var 2 ⊑ λD. R` — same domain/codomain.
* `cTrue ⊑ D` — ok.
* `R.subst 0 cTrue ⊑ app (var 2) dtrue` — requires knowing what R is.

So even at the deepest position, more machinery is needed. But this is
a DIFFERENT wall (dependent-app covariance) and was not reachable
under fixed-self either (fixed-self has its own `BoolBody.subst 0 Bool`
where the deepest position is `app (var 2) Bool` — distinct from
`app (var 2) cTrue` on the LHS).

### Verdict on value-sub

Value-sub is the **semantically correct** self-type rule but:

1. Its transitivity breaks inductively (6 sorrys) — needs coinduction
   or a seen-set, as `research-precise`'s analysis predicted.
2. It does not unblock `dtrue ⊑ Bool` because the structural [App]
   wall sits in front of any self-reference.

**Recommendation**: do NOT merge value-sub iotaIntro into main either.
The ι/fix split (fixed-self or value-sub) is orthogonal to the real
obstruction for the Bool whiteboard example. The next experiment
should focus on the [App] wall directly (e.g. a `[BetaL]` rule, a
codomain-equality rule, or a semantic logical-relation approach) and
see whether any of *those* unblock the domain check — then layer
iotaIntro (preferably value-sub for semantics) on top.

### Files modified in the value-sub pass

* `lean/Och/Simple/Subtype.lean`: iotaIntro premise changed.
* `lean/Och/Simple/Properties.lean`:
  * weaken/narrow/subst cases for iotaIntro adjusted.
  * 6 trans cases (iotaIntro as hbc) changed to sorrys.
* `lean/Och/Simple/Challenge.lean`:
  * `cTrue_sub_iota_trivial`: substitution formula updated, still closes.
  * `dtrue_sub_Bool`: body leg reduced via value-sub, derivation
    pushed to the exact obstruction point (second [Lam]'s contra
    domain check), then sorry.

### Sorry inventory (value-sub pass)

| File | Line | What | Why |
|------|------|------|-----|
| Properties.lean | ~641 (1 decl, 7 sorries inside) | `iotaIntro × iotaIntro` family (6 sorries) + `fixAnn × unfoldFixL` (1 sorry) | Value-sub cut substitutes different values on the two sides; generically unbridgeable |
| Soundness.lean | ~413, ~425, ~433 | iota/fix eval preservation cases | Unchanged from fixed-self pass |
| Challenge.lean | ~242, ~249 | `dtrue ⊑ Bool` partial derivation | [App] contravariant wall, not value-sub related |

Total Simple metatheory sorries: **7** (up from 1 in fixed-self pass)
plus 3 Soundness sorrys (same as before). The whiteboard goal is no
closer to provable.
