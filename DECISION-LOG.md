# Decision Log

Record significant design decisions here. Each entry should explain WHAT was
decided, WHY, and what alternatives were considered.

## 2026-04-21: Path A breakthrough — Equiv_c d sidesteps the nil-Γ obstruction

Added `Equiv_c d e₁ e₂ := ∀ {S Γ}, d ≤ |Γ| → Subtype' S Γ e₁ e₂ ∧ symm` as a
depth-parametrised variant of Equiv. Key new primitive **`Equiv_c.shift`**:

```lean
Equiv_c d e₁ e₂ → Equiv_c (d+1) (e₁.shift 1 0) (e₂.shift 1 0)
```

**Proven axiom-clean, no closedness side condition.** The nil-Γ obstruction
is avoided by paying with a tighter output quantifier (|Γ'| ≥ d+1 ≥ 1
excludes Γ'=[]). `Subtype'.ctx_extend` with Δ = [head] handles every
non-empty case uniformly.

`Equiv_c 0` coincides with `Equiv` (via `to_Equiv_zero`), so the top-level
soundness chain loses nothing. Coercion `Equiv → Equiv_c d` is free via
`of_Equiv`.

**Remaining work (Path A step 3):** refactor R's .lam/.iota/.fix/.type/
.neutral clauses to use `Equiv_c d` instead of `Equiv`. Cascading updates:
- R_resp_Equiv: compose Equiv input via of_Equiv + Equiv_c.trans.
- R_neutral_app: output as Equiv_c d.
- R_fresh_bvar0: use Equiv_c.refl.
- R_quote_equiv return type: Equiv_c d (was Equiv).
- All R_quote_equiv consumers: OpenCtx.eq, eval_quote_equiv_closed,
  vapp_realises stuckRec branches. Each uses Equiv_c d at Γe of length d,
  which satisfies |Γe| ≥ d.
- eval_realises construction sites (4 for .asc/.letE/.lam/.iota/.fix):
  wrap final Equiv in `Equiv_c.of_Equiv` to upgrade to Equiv_c d.

Estimated ~30 error sites in SoundnessProof.lean to fix. Attempted this
iteration, hit scope limit mid-refactor, reverted R def. Infrastructure
(Equiv_c + shift + basic combinators) landed in commit 826d2b1.

Once R uses Equiv_c d, R_depth_lift's 5 cases close:
- .type/.neutral: `Equiv_c.shift` on the base conjunct's Equiv_c d.
- .lam/.iota/.fix: depth-lift existentials (dome, ρe'), then
  `Equiv_c.shift` on heqL/I/F, plus a substEnv-shift commutation lemma
  `(body.substEnv (.bvar 0 :: ρe.map shift)).shift 1 1 =
   body.substEnv (.bvar 0 :: (ρe.map shift).map shift)`.

## 2026-04-21: Structural blocker confirmed — all 4 remaining declaration sorries reduce to nil-Γ Equiv.shift

After Agent A2's levelsBelow refactor landed (95f0022) and Agent E
added RList_depth_lift (f011754), the remaining 4 declaration
sorries were analysed. All four ultimately reduce to the same
obstruction:

**Blocker:** `Equiv.shift` at `Γ=[]` requires `shift 1 0` applied
to arbitrary (possibly open) expressions. Without closedness of
both endpoints, this is structurally unprovable because:
- At `Γ=[]`, `Subtype' S [] (e.shift 1 0) _` introduces free
  bvars that no `.bvar` rule can discharge.
- `ctx_extend_at` requires a non-empty Δ to extend into — at
  Γ'=[], there's nowhere to extend.
- `shift_of_closed` only works when `e.closedAt 0 = true`, which
  doesn't hold for ρe entries at intermediate depths (they have
  free bvars < d for d > 0).

**Sorry reductions:**

1. `R_depth_lift` (2130): needs `Equiv (e.shift 1 0) (e'.shift 1 0)`
   for the `.type`/`.neutral` and `.lam`/`.iota`/`.fix` (final
   Equiv conjunct) cases. Reduces to Equiv.shift.

2. `R_quote_equiv` closure cases (2467): each needs
   `Equiv body' bodyE` where `bodyE` has a shifted env. Reduces
   to `quoteClosure_realises` + mutual recursion on quote-fuel,
   and the env-shift step needs Equiv.shift.

3. `vapp_realises` iota/fix unfold (2594): needs `Equiv.subst_resp`
   (deleted) on `heqI : fe ≡ .iota anne bode`. The closedness-
   carrying `Equiv.subst_resp_closed` requires `fe.closedAt 0 ∧
   anne.closedAt 0`, which don't hold in open contexts. Reduces
   to: either thread closedness through REnv (refactor), or use
   Equiv.shift.

4. `tyInfer_sound_open` (3626): mutual block with internal
   `by sorry` for A9 (known issue: tyInfer returns bare .fix/.iota
   annotation, not sound) + other internal sorries threading
   through eval_quotes'. A9 is a calculus-design issue, not a
   proof blocker.

**Paths forward:**
- **(A) Closedness-tracking R:** add `e.closedAt d = true`
  invariant to R's .lam/.iota/.fix env-exposes clauses. Then
  R_depth_lift's shift at cutoff d becomes identity (via
  shift_of_closedAt at d = Γ.length). But requires proving
  closedness preservation through all R construction sites.
- **(B) Closedness-tracking Equiv:** refactor Equiv to carry
  closedness witnesses, making Equiv.shift provable directly.
  Invasive.
- **(C) Alternative subst_resp path:** prove subst_resp using
  unfold_iota_L/R rules + structural recursion without going
  through Equiv.shift. Unclear if feasible.

**Status:** Both Agent E (R_depth_lift) and Agent F (vapp iota/fix)
sub-agents stalled (stream watchdog timeout at 600s). Agent E
committed partial progress (RList_depth_lift). Agent F's worktree
branch `agent-vapp-iota-fix` was created but no work pushed.

Session net progress:
- Started: 10 declaration sorries.
- Ended: 4 declaration sorries (R_depth_lift, R_quote_equiv,
  vapp_realises, tyInfer_sound_open).
- Infrastructure added (proven, reusable): Val.shiftLvl,
  Val.levelsBelow, eval_shiftLvl, eval_levelsBelow,
  Closure.envShiftLvl, shiftLvl_of_levelsBelow,
  quote_quoteClosure_quoteNeutral_depth_shift cutoff-mutual,
  quote_depth_shift_of_levelsBelow, RList_depth_lift,
  OpenCtx.hρlvl + hΓ.levelsBelow invariants.

Further progress requires deciding between paths A/B/C.

## 2026-04-21: R refactor landed — base conjunct dropped for closures; R_quote_equiv closure cases left as residual sorry

**What:** Implemented the R restructure per the 2026-04-19 plan.
`R (n+1) d (.lam dV cl) e`, `.iota`, `.fix` now only carry the
env-exposes clause with the added **head R**: `∃ ρe' he,
R (n+1) d headV he ∧ RList (n+1) d cl.env ρe' ∧ closedAt ∧
Equiv e (.ctor he body.substEnv …)`. The `.type`/`.neutral` clauses
retain the base conjunct `∀ e' hq, Equiv e' e`. `R_mono`,
`R_resp_Equiv`, `RList_mono`, extractors (`R_lam_clause`,
`R_iota_clause`, `R_fix_clause`), and `eval_realises`'s ctor cases
all updated.

**Wins:**
- `eval_realises`'s 3 base-conjunct sorries (for `.lam`/`.iota`/
  `.fix` cases) are gone — the env-exposes branch just supplies
  the new head R from `ihf'` (fuel-IH).
- R extractors now return the head R as extra info.
- R_neutral_app simplified to take per-component `Equiv`
  witnesses instead of deriving from R bases (which no longer
  exist for closure cases).

**Residuals (sorries added):**
- `R_quote_equiv`'s `.lam`/`.iota`/`.fix` cases (3 sub-sorries,
  one declaration): needs mutual `quoteClosure_realises` on
  quote-fuel; each step would use env-exposes to build a REnv
  at `d+1` and call `eval_realises`. The cycle is
  `R_quote_equiv → quoteClosure_realises → eval_realises →
  (via R_neutral_app) → R_quote_equiv`. To close, either
  (a) put all four theorems in one giant mutual with a lex
  `(eval_fuel, quote_fuel, sizeOf v)` termination (eval_fuel
  decreases on most calls, quote-fuel on
  R_quote_equiv→quoteClosure, sizeOf on recursive R_quote_equiv
  sub-calls); or
  (b) add a closedness side condition (`e.closedAt d`) and let
  `subst_resp_closed` discharge inner substitutions.
- `vapp_realises` iota/fix unfold branches (2 sub-sorries, same
  mutual declaration): need `Equiv.subst_resp` on `fe ≡ .iota
  anne bode`. `subst_resp` was deleted 2026-04-21 (depended on
  nil-Γ `Equiv.shift`). `subst_resp_closed` is available but
  requires closedness of fe AND `.iota anne bode`. Closing
  requires either threading closedness through `vapp_realises`
  or resolving the nil-Γ `Equiv.shift` sorry.

**Net effect:** `eval_realises`'s mutual sorry reduces from 5
sub-sorries (3 base + 2 iota/fix unfold) to 2 (iota/fix unfold).
But R_quote_equiv gains 3 sub-sorries as one new declaration.
Overall declaration-sorry count: 3 → 4 (+1). The R structure
change is sound; the residuals are mechanical proof obligations
that close once the structural sorries above are resolved.

**Soundness axioms unchanged:** `concEval_refines`,
`concEval_preservation`, `concEval_equiv_closed` all still
depend only on `[propext, Quot.sound]` — the sorries are not
on the critical soundness path.

## 2026-04-21: R_quote_equiv closure + vapp iota/fix unfold — investigation (agent a516f9da)

**What:** Extended analysis of the two residual sorries. Attempted
routes (a) giant mutual and (b) closedness side condition. Both
routes hit infrastructure obstacles.

### Route (a) — giant mutual with `quoteClosure_realises`

Planned cycle:
`R_quote_equiv` (.lam/.iota/.fix on `sizeOf v`)
  → `quoteClosure_realises` (decreases quote-fuel)
  → `eval_realises` (same fuel-mutual as today)
  → `R_quote_equiv` (on sub-values — `sizeOf` decrease).

**Obstacle identified:** `quoteClosure_realises` needs `REnv (m+1)
(d+1) (.neutral (.var d) :: cl.env) (.bvar 0 :: ρe'.map (·.shift 1
0))` to call `eval_realises`. The head is `R_fresh_bvar0` ✓. The
tail requires `RList (m+1) (d+1) cl.env (ρe'.map (·.shift 1 0))`
— depth-lifted from `RList (m+1) d cl.env ρe'`.

`R_depth_lift` (in `depth_lift_bundle`) takes as a precondition
`quote fuelω d v = some qe`, i.e. **quotability of each env entry
at depth `d`**. This quotability is NOT provided by R nor by `hq :
quote fuelω d (.lam dV cl) = some e'` (quote on a closure doesn't
recurse through `cl.env`; it goes `quoteClosure → eval → quote` on
the inner eval result, bypassing the env entries).

**Options to supply quotability:**
1. Strengthen R's closure clauses to include `∀ k w, cl.env[k]? =
   some w → ∃ we, quote fuelω d w = some we`. Propagate through
   `eval_realises`'s .lam/.iota/.fix cases. Requires `eval ρ e =
   some v → env-quotable-of-ρ → v-env-quotable` as a new lemma.
   **Moderate-high complexity.**
2. Strengthen R with `v.levelsBelow d` instead. `v.levelsBelow d`
   is preserved through `eval_levelsBelow` (proven). But
   `R_depth_lift` still uses `quote fuelω d v = some qe`, not
   `v.levelsBelow d` — would need a new `R_depth_lift_levels`
   variant, which itself requires `quote_levelsBelow` (quote →
   levelsBelow, potentially provable but NOT existing today).

Attempted route (a) with option (2) analyzed; the `R_depth_lift_
levels`-style theorem for the `.type` case reduces to
`Subtype' Γ' .type (e.shift 1 0)` given `Subtype' Γ .type e`,
which is `Equiv.shift` (still sorried at nil-Γ).

**Net:** Route (a) is NOT closable without either (i) strengthening
R with quotability/levelsBelow invariants AND threading through
all R-producing theorems, OR (ii) closing the nil-Γ `Equiv.shift`
sorry. Both are substantial separate workstreams.

### Route (b) — closedness side condition

Add `e.closedAt d = true` (or `e.closedAt 0 = true`) as a hypothesis
to R_quote_equiv.

**Obstacle identified:** For the `.lam` case, we need `Equiv (.lam
dom' body') (.lam dome bodyE)` via `Equiv.lam`, which requires
`Equiv dom' dome` (recursive R_quote_equiv on dV) and `Equiv body'
bodyE`. Recursion on `dV` needs `dome.closedAt d`. The hypothesis
`e.closedAt d` does NOT give us `dome.closedAt d` because Equiv
doesn't preserve closedness (Equiv e (.lam dome bodyE) doesn't
imply `.lam dome bodyE` is closed).

Additionally, `OpenCtx.eq` has `hcl : e.closedAt ρe.length` (closed
under the env, not at 0). The closure-case substituends inside the
body are at arbitrary depth within open contexts — closedness at
0 doesn't hold.

**Net:** Route (b) requires either (i) enriching R itself with
closedness conjuncts (so `dome.closedAt d` is exposed), OR
(ii) extending `OpenCtx` invariants to carry ρe-entry closedness
and propagate to `e.substEnv ρe` closedness. Both touch many
call sites.

### vapp_realises iota/fix unfold — specific sorry analysis

Target: `Equiv (bode.subst 0 fe) fe` where `heqI : Equiv fe
(.iota anne bode)`.

Attempted alternative chains (NOT needing Equiv.subst_resp):
- Via `unfold_iota_R`: transforms `a ⊑ body.subst 0 (.iota ...)`
  into `a ⊑ .iota ...`. We need the REVERSE direction (inversion),
  which is NOT a rule — would require proof-level reasoning on
  Subtype' derivations.
- Via `iota_intro`: requires proving `bode.subst 0 fe ⊑ anne` AND
  `bode.subst 0 fe ⊑ bode.subst 0 (bode.subst 0 fe)` — both
  structurally deeper substitutions that don't simplify.
- Via `trans` with intermediate `.iota anne bode`: gives
  `bode.subst 0 fe ⊑ .iota anne bode → bode.subst 0 fe ⊑ fe` by
  `heqI.2`. The first hop `bode.subst 0 fe ⊑ .iota anne bode` via
  `unfold_iota_R` requires `bode.subst 0 fe ⊑ bode.subst 0 (.iota
  anne bode)` — back to subst-congruence.

**`subst_resp_closed` usability:** Requires `fe.closedAt 0` AND
`(.iota anne bode).closedAt 0`. In open contexts (used by
`OpenCtx.eq`), `fe = .iota annE (bExpr.substEnv (lift ρe))` which
is NOT closed at 0 when ρe has free variables.

**Net:** vapp iota/fix unfold sorries structurally require either
(a) the nil-Γ `Equiv.shift` sorry closed, OR (b) closedness
invariants threaded through REnv/OpenCtx/R.

### Conclusion

Both sorries (R_quote_equiv closures, vapp iota/fix unfold) are
blocked on the SAME underlying gap: the inability to shift Equiv
witnesses under binders without closedness (Equiv.shift nil-Γ sorry).

**Shortest path forward** (avoiding this dead end):
1. Close the nil-Γ `Equiv.shift` sorry (via closedness-tracking
   Equiv + `Subtype'.shift_nil_closed`), OR
2. Strengthen REnv/OpenCtx with `∀ k e_k, ρe[k]?.closedAt 0`
   invariants and propagate closedness through eval_realises.

Both are multi-session refactors. This session's sorries REMAIN
in place pending that work. Agent C's target (whatever it is)
is unblocked to the extent it doesn't depend on R_quote_equiv's
closure cases — which it may or may not.

## 2026-04-21: `depth_lift_bundle` — partial infrastructure; step 5 blocked by cutoff-mismatch (agent a800598a)

**What:** Attacked `depth_lift_bundle` (the last single-sorry bundle for
the quote depth-shift property). Proved 4 of 6 infrastructure steps
fully; the 5th (`quote_shiftLvl`) hit a subtle cutoff-mismatch wall
that needs a generalised mutual statement (sketched but not
completed).

**Proven infrastructure (SoundnessProof.lean, all axiom-free):**
- `Val.shiftLvl c v` + Neutral/Closure analogues (+ helper
  `Closure.envShiftLvl`): shift neutral-var levels `≥ c` up by 1.
  `Closure.envShiftLvl_eq_map` bridges to List.map.
- `Val.levelsBelow d v` + analogues: every neutral-var level is `< d`.
  Monotonicity (`levelsBelow_mono`); `envLevelsBelow_take` for
  `Closure.mk'`; `envLevelsBelow_getElem?` / `_of_getElem?` bridges.
- `Val.shiftLvl_of_levelsBelow`: `v.levelsBelow c → v.shiftLvl c = v`
  (no-op).
- `eval_shiftLvl`: `eval ρ e = some v →
  eval (ρ.map (·.shiftLvl c)) e = some (v.shiftLvl c)`. Full induction
  on fuel, including vapp iota/fix recursive-head branches (via
  `Val.shiftLvl_neutral_isNeutral` and `cases f` on the outer vapp).
- `eval_levelsBelow`: `eval ρ e = some v → envLevelsBelow d ρ →
  v.levelsBelow d`. Preserves level bound through all cases.

**Remaining obstacle (step 5):** In the closure case of a would-be
`quote_depth_shift_mutual`:

Given `quoteClosure d cl = some e`, unfold to:
  `eval (.var d :: cl.env) body = some v`, `quote (d+1) v = some e`.

Goal: `quoteClosure (d+1) cl = some (e.shift 1 1)`.

Via `eval_shiftLvl` (c := d) + `Closure.levelsBelow d cl` (input),
we correctly get `eval (.var (d+1) :: cl.env) body = some
(v.shiftLvl d)`.

But the IH gives `quote (d+2) v = some (e.shift 1 0)` — NOT
`quote (d+2) (v.shiftLvl d) = some (e.shift 1 1)`. The cutoff
mismatch reflects:
- `.var d` in v: quotes at `d+1` to `.bvar 0` (the binder).
- `.var (d+1)` in v.shiftLvl d: quotes at `d+2` to `.bvar 0` (same
  binder, unchanged).
- Other `.var j < d`: `.bvar (d-j)` → `.bvar (d+1-j)` at the deeper
  quote. Difference is `.shift 1 1` (bvar 0 preserved, others +1),
  NOT `.shift 1 0`.

**Sketched (but not written) resolution:** A generalised mutual with
a cutoff parameter:
```
∀ n d c v e, c ≤ d → Val.levelsBelow d v →
  quote n d v = some e →
  quote n (d+1) (v.shiftLvl (d-c)) = some (e.shift 1 c)
```
with similar forms for `quoteClosure`/`quoteNeutral`. At c=0 the
Val shift at cutoff d is a no-op (via shiftLvl_of_levelsBelow),
giving the outer form. At c=1 (closure body) it matches the
required `.shift 1 1`.

The closure case recurses with (c+1): so the outer IH at (c, d)
feeds the closure's body at (c+1, d+1), maintaining `c+1 ≤ d+1`.

The arithmetic works out; what needs care is:
- `Val.shiftLvl (d-c)` at various `c` values is monotone in `c`
  on values with `levelsBelow d`, but the exact shape needs
  threading.
- The `.bvar` case of `quoteNeutral` needs an explicit split on
  `j < d - c` to determine whether `.shiftLvl (d-c)` moves `j`.

Left as "[TODO]" in the `depth_lift_bundle` docstring with the full
plan; future agent can resume from here without re-doing steps 1-4, 6.

**State:** Declaration sorries unchanged (3 total). ~300 lines of
new axiom-free infrastructure.

## 2026-04-21: `Equiv.shift` nil-Γ: route (i) is genuinely harder than the docstring suggests

**What (reassessment of 2026-04-19 entry below):** Route (i) —
`Subtype'.shift_nil : Subtype' S [] a b → Subtype' S [] (a.shift n c)
(b.shift n c)` — is **not** a ~60-line structural induction. The
`.hyp` case at `Γ = []` is genuinely unsound *as stated* for
arbitrary `S`: from `Subtype' S [] a b` via `.hyp` with
`(0, x, y) ∈ S`, we have `a = x`, `b = y` (shift-by-0). We need
`Subtype' S [] (x.shift n 0) (y.shift n 0)`. If `x` has a free
bvar, `.hyp` on `(0, x, y)` doesn't give the shifted form — it
gives the unshifted — and no other constructor produces
`(x.shift n 0) ⊑ (y.shift n 0)` without a matching S entry.

The `.bvar` case being "vacuous at Γ=[]" is correct, but it's
the `.hyp` case that's the wall, not `.bvar`.

**Three ways forward, none 60 lines:**

1. **`Seen.wellClosed` invariant.** Track `∀ (d, x, y) ∈ S,
   x.closedAt d ∧ y.closedAt d`. Then `.hyp` case: `x`, `y` closed
   at d means `x.shift (|Γ|-d) 0` is closed at `|Γ|`, so shift at
   cutoff `|Γ|` is identity — conclusion = input. The invariant is
   preserved by every Subtype' constructor (productive rules add
   `(|Γ|, a, b)` at current depth; `a, b` live in `Γ`, closed at
   `|Γ|`). This makes `shift_nilS` provable at any `Γ`, but requires
   threading `wellClosed` through every user.

2. **`Ctx.wellFormed` invariant + `shift_in_place`.** At any `Γ`,
   shift by `n` at cutoff `|Γ|` (above the context). Needs `Γ`
   entries closed at their position (τ at index `k` closedAt
   `|Γ|-k-1`) to discharge the `.bvar` case. Again an invariant
   to thread.

3. **Restrict `Equiv` to non-empty `Γ`.** All callers of
   `Equiv.shift` (subst_resp's lam/iota/fix/letE branches; R_depth_lift
   base-conjunct) compose into larger `Equiv.lam` /
   `Equiv.iota_cong` / etc. forms whose `.2` access happens at
   `dom :: Γ` — always non-empty. But `concEval_refines` uses
   `(concEval_equiv hstep).1` at `Γ = []` for `concEval_preservation`,
   which would break unless concEval_equiv is re-derived without
   going through `Equiv.shift` at the top.

**Trace argument for route 3 (key insight):** Inside
`concEval_equiv`'s letE/app cases, `Equiv.subst_resp body heq 0`
is instantiated at `(S=[], Γ=[])`. `subst_resp` recurses on
`body`; at each binder level it wraps the inner Equiv in
`Equiv.lam`/`Equiv.iota_cong`/etc., whose `.1`/`.2` access the
body at `dom :: outerΓ`. At `bvar i` case, `subst_resp` returns
`heq` directly — so `heq` is accessed at `(S, Γ)` that `subst_resp`
was instantiated at, wrapped in the enclosing binders. The
*outermost* subst_resp is called at `Γ=[]`, but the `Equiv.shift
heq` inside is always one binder level deeper, hence non-empty.

So **Equiv.shift is never actually accessed at Γ=[] in any
current caller's usage pattern**. The sorryAx exists only because
Lean requires a total proof of `Equiv (e₁.shift 1 0) (e₂.shift 1 0)`
regardless of how its `.1` is used.

**Cleanest fix: route 3** — add `Γ ≠ []` hypothesis to
`Equiv.shift`, verify at each use site, and produce
`concEval_refines_closed : Subtype' [] [] e' e` as a separate
bespoke proof at Γ=[] (the only place it's needed). Not
trivially small: concEval_equiv's proof has ~60 lines of case
analysis that would need duplication for the closed variant.

**Decision:** NOT yet chosen. Route 1 is most general but
invasive; route 3 is local but duplicates proof. Both take a
day's work — neither is a ~60-line structural induction. The
prior entry below understates this.

## 2026-04-19: `R` base-conjunct is redundant; quote-fuel mutual recovers it

**What:** `R (n+1) d (.lam dV cl) e` carries both the new
env-exposes conjunct (`∃ ρe' he, RList … ∧ closedAt ∧ Equiv e
(.lam he (body.substEnv …))`) AND a legacy `quoteClosure`-based
base conjunct. The latter is unprovable inside `eval_realises`'s
fuel-IH (`quoteClosure` evaluates at `fuelω-1`, outside the IH).

**Resolution:** Drop the base conjunct from `R`'s definition; add
`R (n+1) d headV headE` to env-exposes (so the *head* annotation
is also realised). Recover `quoteClosure d cl ≡ body.substEnv
(lift ρe')` post-hoc via a `quoteClosure_realises` lemma mutual
with `R_quote_equiv` on **quote-fuel** (the `fuelω-1` recursion in
`quote`/`quoteClosure`), not eval-fuel. Each step uses env-exposes
to know `cl.env` is realised. Per tier-1 fork analysis (`e7b8beb`).

**Closes:** 3 `eval_realises` base-conjunct sorries (lines 1310,
1328, 1673 at `1df8063`).

## 2026-04-19: `Equiv.shift` nil-Γ via `Subtype'.shift_nil`

**What:** `Equiv.shift`'s cons-Γ case routes through `ctx_extend`
(now proven). The nil-Γ case can't (nothing to extend). Routes:
(i) `Subtype'.shift_nil : Subtype' S [] a b → Subtype' S []
(a.shift n c) (b.shift n c)` — ~60-line structural induction in
Subtyping.lean; the `.bvar` case is vacuous at `Γ=[]`. (ii) Restate
`Equiv` quantifying `Γ ≠ []` — verified all callers are at cons-Γ,
but the conclusion still needs `[]`. (iii) Add `(hcl : a.closedAt 0)`
hypothesis so `a.shift n c = a` — but `Equiv` doesn't track
closedness. **Route (i) chosen.**

## 2026-04-19: All three root obligations solved at the definition level

**What:** The three structural obstructions that gated soundness
since the open-Γ generalisation are each closed by a definition
change, integrated at `e0384f1`:
- Root #1 (`ctx_extend_at`): `Seen` depth-tagged → Subtyping.lean
  is **sorry-free**. `.hyp` self-shifts; `narrow`/`ctx_extend` drop
  `Seen.Closed`. Commits `8d86c69`+`e0384f1`.
- Root #2 (`vapp_realises`): `R`'s `.lam`/`.iota`/`.fix` clauses
  expose `∃ ρe' he, RList (n+1) d cl.env ρe' ∧ closedAt ∧ Equiv …`
  (well-founded on `(n, sizeOf v)` lex via mutual `RList`).
  `vapp_realises` proven by `REnv_cons henv' hRa` → mutual
  `eval_realises` → `R_resp_Equiv`. Commit `293dc13`.
- Root #3 (`tyInfer .bvar`): `OpenCtx` carries `hwf` (each `ρe[k]`
  has its declared type) and `hlen`. `push_fresh.hwf` via
  `Subtype'.bvar`; `push_let.hwf` via `(hval_le)` + `ctx_extend`.
  Commits `578ad37`+`94483f1`.

**Residual** (~13 declaration sorries): `R_mono.decreasing_by`
(termination reshuffle, ~10 min); 3 `eval_realises` base-conjuncts
(quoteClosure correspondence — closes via the new
`quoteClosure_equiv_openω_fresh`); `quote_open_subst` (4-step route
documented); `SubV_to_Subtype'` closure cases (need `(hRa)` from
new R-clause); `whnfPi_sound_open`; `tyInfer .lam/.app/.letE`;
`openNf_holds` (false; route-(a) `eval_quotes'` overload ready).
None require further definition changes — all are downstream
applications of the three solved roots.

**`tyInfer .letE` algorithm gap (noted, not fixed):** the inferred
type may reference the let-binder, so `quote_{Γ.size}` of it can
fail. `tyInfer .letE` should `eval`-substitute the binder value
into the body's inferred type before returning (TyCheck.lean
change). Per fork `a40bd0da` analysis.

## 2026-04-18: `Seen.Closed` (route b) ruled out for `ctx_extend_at`; route (a) required

**What:** The `Seen.Closed S` invariant cannot close `ctx_extend_at`'s
6 binder cases. Route (a) — `Seen := List (Nat × Expr × Expr)` with
`.hyp` shifting from recorded depth to `|Γ|` and the 5 seen-extender
constructors recording `|Γ|` — is required.

**Why:** `Seen.Closed` is not preserved through `.iota_intro` /
`.unfold_*`: those constructors add the *current goal pair* to `S`,
which references `Γ`-vars, so when `|Γ| > 0` the new entry is not
closed at `|Γpfx|`. Concrete: `.iota_intro` at `Γpfx₀ ++ Γ` adds `p`,
then `.lam` below it; the IH gives seen `p.shift_{c+1} :: S₀`, the
goal needs `p.shift_c :: S₀`, which differ when `p` has a var at
index `c`. Four non-invasive generalisations (per-entry depth-list,
∀-quantified `S'`, union-over-cutoffs, closed-up-to) all fail because
`.hyp` uses entries at *arbitrary deeper contexts* without shifting,
so the lifted seen-set needs each entry at every use-cutoff — a
`List` can't hold that. Detailed at Subtyping.lean's `ctx_extend_at`
docstring (commit 26cd686).

**Ripple:** `Subtype'` definition + ~15-30 SoundnessProof.lean sites
(`.hyp`/seen-extender uses, `QuotesSeen`, `subCheckVal_subV` bridge,
`Equiv.shift`). All callers pass `S = []` at the top level, so the
ripple is mechanical. **Deferred** until R-restructure (root #2)
lands so both definition changes go through SoundnessProof.lean once.

## 2026-04-18: `R` must expose closure environments (root #2 resolution route)

**What:** `R`'s `.lam`/`.iota`/`.fix` clauses change from a pure
Kripke quantification (`∀ va ea, R n d va ea → R n (d+1) (vapp …) …`)
to additionally expose the captured environment:
`∃ ρe', REnv n d cl.env ρe' ∧ Equiv e (.lam … (cl.body.substEnv …))`.
Termination shifts to `(n, sizeOf v)` lex so `REnv n d cl.env`
referencing `R n` at sub-Vals is well-founded.

**Why:** Both the "Ahmed-style `R(min m fuel)`" and the
mutual-`vapp_realises` routes lose exactly one step-index at the
`.app`/closure boundary (documented at SoundnessProof.lean:1495-1530
in 92a1bd4). The Kripke clause says "for any future arg, the body
realises" but discards which `ρ` produced the closure. `eval_realises`
needs to invoke its fuel-IH on the closure body at `(va :: cl.env)`,
which requires `REnv n d cl.env ρe'`. With the env exposed,
`.app .fix/.iota` heads close as `ihf' cl.body (REnv_cons henv' hRa)`
— no Kripke step, no index loss.

**Alternatives:** (a) Keep Kripke, drop a step-index at `.app`:
fails because `R 0` is vacuous so the conclusion is too weak.
(b) Mutual `vapp_realises` recursing on `(fuel, sizeOf)` lex: the
`vapp` call inside `.fix` unfold consumes one `unf` not one `fuel`,
so the measure doesn't decrease. (c) Expose `REnv` (chosen).

## 2026-04-18: `QuotesCtx` depth convention is `k`, not `k+1`

**What:** `QuotesCtx Γ Γe` says entry `k` of `Γ` quotes at depth `k`
(was `k+1`). Ripples: `QuotesCtx.push`, `OpenCtx.push_fresh/push_let`
all take `hqτ : quote Γ.size τ = some τe` (was `Γ.size+1`).

**Why:** `Γ[k]` was added when `Γ` had size `k`; its Val references
neutrals at levels `0..k-1`; the canonical depth is `k`. The `k+1`
convention forced `push_fresh` to produce `(τe.shift 1 0 :: Γe)`
where `Subtype'.lam`'s body context is `(τe :: Γe)` — an unprovable
shift bridge. With `k`, `push_fresh` gives `(τe :: Γe)` directly and
`tyCheck_sound_open .lam` builds `Subtype'.lam hcontra hIH` with no
shift gymnastics. Also unblocks `SynthN_to_Subtype'.var` (the `hΓ`
hypothesis now matches `Subtype'.bvar`'s shift count up to
`quote_depth_shift_n`).

## 2026-04-19 — `quote_total_on_eval` needs `(nf fuelω e).isSome`

The unconditional form `eval fuel _ [] e = some v →
∃ ve, quote fuelω 0 v = some ve` is **false**: `eval 2 _ []
(.lam .type huge) = some (.lam .type ⟨huge, []⟩)` succeeds
at fuel 2 (lambdas don't evaluate their body), but
`quoteClosure` opens the closure with a fresh neutral and
re-evaluates `huge`, which can need arbitrary fuel.

**Fix**: add `(hnf : (nf fuelω e).isSome)` as a side
condition. The `nf` witness *is* `quote (eval e)` at
`fuelω`; transport via `eval_fuel_mono`. Axiom-clean
(`[propext, Quot.sound]`). Threaded `hnfe`/`hnfτ` through
`tyCheckFallback_sound_closed`/`tyCheck_sound_closed`/
`typeCheck_sound`/`soundness`; for concrete inputs both
discharge by `native_decide`.

**Why not a Val-size measure**: the natural measure
`Val.qsize` would need to bound `quoteClosure cl`'s
`eval [fresh :: cl.env] cl.body` cost, which depends on
`cl.body` (an arbitrary `Expr`) — there's no useful bound
in terms of `cl`'s structure alone. The `nf.isSome`
condition is exactly "the term has a normal form within
budget", which is the right operational precondition.

The open-Γ form (`eval_quotable_open`, SoundnessProof)
should take the same shape; deferred until the
`OpenCtx`-ρe restructure lands.

## 2026-04-19 — `Val.beq` ptrEq fast-path; legacy `subCheckNF` retired

**Root cause of the ~5 min DNat build**: `Val.beq` walks
the value DAG as a *tree*. With `unfBound = 32`, `dsucc`'s
self-applying `(dsucc m)` P-domain creates a 32-deep `.lam`
tower whose closure envs each reference the predecessor
numeral, so DAG-as-tree size grows ~33× per level
(`vthree` = 15.6 M nodes; `vNat` = 63). The DAG itself is
tiny (eval ~3 ms); 488 `subCheckVal` calls × ~28 `Val.beq`
guards each tree-walk it. Call counts and seen-list length
are *constant* across `done_..dthree` — the blowup is
per-call cost, not call count. (`H1` confirmed; `H2..H4`
ruled out — see commit `60d4b6d`.)

**Fix**: `unsafe def Val.beqFast` (+ Neutral/Closure/Env
twins) prefixed with `ptrEq ||`, swapped via
`@[implemented_by]` so the proven `Val.beq` (and
`LawfulBEq`/`subCheckVal_subV`) are untouched. `dthree ⊑
dNat` 322 s → 0.3 s; `dfive` flat at ~330 ms (was
untestable). Combined with the legacy-checker retirement,
clean build 580 s → 71 s.

**Why ptrEq is sound here**: `Val` is an inductive (no
mutable cells), so pointer-equality implies structural
equality. `@[implemented_by]` is a trusted annotation; the
*proof* uses the structural `beq`, only `native_decide`/
`#eval` use the fast path. The risk is the usual one for
`implemented_by` (a future divergence between `beq` and
`beqFast` would not be caught by Lean); the `LawfulBEq`
instance and the `dfive` regression in `PerfProbe.lean`
are the guards.

**Alternatives considered**: (a) `Hashable Val` + `HashSet`
seen — would also work, more code, same trust boundary
(hash collisions). (b) Quote-then-`Expr.beq` for the seen
check — slower per check, identifies more pairs (the A6
closure-non-canonicality), but breaks `LawfulBEq`. (c)
Cap `unfBound` at e.g. 8 — workaround, not a fix.

**Legacy `subCheckNF`/`absEval` retired** in the same
batch (`6772061`, net −449 lines, Eval.lean 808→339). It
existed for the divergence sweep, which had found A1–A8
and was down to the one documented A6 incompleteness. The
new sweep is NbE-only (`sweep_refl`/`top`/`strict`/
`a6_pinned`). One test weakened: `appendArrays` at its
declared type is an A6-family NbE incompleteness; pinned
in `PerfProbe.lean`.

## 2026-04-19 — DBool/DNat: very-dependent encoding (no per-constructor `fix`)

`dtrue`/`dfalse`/`dzero` are now `ι self. λP:(self →
Type). …` — no `fix B:Type` wrapper, no forward-reference
to their type. `dBool`/`dNat` reference them directly.

The `e08bce9` per-constructor `fix B` was a workaround for
the contravariant motive-domain check not closing
coinductively. With A4 (seen-indexed `Subtype'`) + A5/A7,
the very-dependent form goes through directly: after
`unfold_fix_R` puts `(ctor, Type)` on the seen-list,
`unfold_iota_L` substitutes `self ↦ ctor` so the motive
domain becomes `(ctor → Type)`, and the contravariant
check `Type ⊑ ctor → ctor ⊑ dType` closes via `.hyp`. The
constructor's `:Type` annotation is a placeholder (the
motive uses `self`, not the annotation; `Type` makes the
structural ann-check fail fast so iotaIntro takes over).

`dsucc`'s `fix dsucc:(dNat → dNat)` stays — genuine
function recursion (`dsucc pred` in the `s`-branch). The
local-let `dsucc` inside `dNat` also stays
(closure-non-canonicality; A6).

`ι x.`/`fix x.`/`let x =` macro sugar (`rfl`-identical to
the `:Type` form) added to make this read naturally.

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

**Plan revised**: a worktree fork (`6a0d2bf`) implemented
closure-env masking (replace unreferenced env slots with
`.type`) and confirmed it makes `dtwo ⊑ dNat` fast under
`domB` — but **not** `dthree`. The residual cause: `dNat`'s
`s`-domain `λpred:N. P (dsucc_local pred)` references the
inner `let`-bound `dsucc_local` (closure body `bvar 3`,
env `[…, vNat]`), while the input numeral's `s`-domain
references the *top-level* `dsucc` (closure body = the
closed `dNat` Expr, env `[]`). These are semantically equal
but structurally distinct *bodies*, not envs; A1's
bidirectional `.app,.app` then recurses into `dsucc_local m
⊑⊒ dsucc m` at every numeral layer. Fixing this needs
quote-based closure canonicalisation (or a quote-based
seen-check), which is the option (b) we rejected for cost.
So `domA` stands; `domB` is a post-Phase-2 completeness
project. The masking work is parked on tag
`a6-closure-mask-experiment` (`6a0d2bf`).

Verifier note: `#eval NbE.subCheck 200 dthree dNat` still
times out under `domA`, and *also* at the `77ac3da`
pre-A6 baseline. So that is interpreter overhead (the
seen-list `Val.beq` walks the full numeral Expr at each
check), not a `domA`-vs-`domB` symptom; `native_decide` at
fuel 1600 handles it in the ~5 min DNat build.

## 2026-04-18 — `ctx_extend_at` binder cases need a `Subtype'`-seen redesign

`Subtype'.narrow_at` (and `Equiv.shift`, same shape) is
proven for 16/19 cases; the three open binder cases all
hit the same wall: the body IH gives the seen-set shifted
at cutoff `c+1`, the goal needs it at cutoff `c`, and these
only coincide when the seen entries are closed — but
`.iota_intro`/`.unfold_fix_*`/`.unfold_iota_L` extend the
seen-set with the *current* `(a, b)` pair, which lives at
depth `|Γ|`.

**Why this matters**: `narrow_head` is what bridges
`SubV.lam` (at `Γ.push domA`) to `Subtype'.lam` (at
`domB :: Γ`), so until it closes the `subCheckVal_sound`
chain has `sorryAx` from this one place.

**Three routes** (none yet committed to):

(a) **Depth-tag the seen-set**: change `Seen` from
`List (Expr × Expr)` to `List (Nat × Expr × Expr)`;
`.iota_intro` records `(|Γ|, a, b)`; `.hyp` shifts the
recorded depth back. Then `ctx_extend_at`'s shift on `S`
is per-entry at the entry's recorded cutoff. Invasive
(every seen-touching constructor changes), but the
algorithm already does this implicitly (its seen entries
are `Val × Val` with neutrals at known depths).

(b) **Closed-pair recording**: change `.iota_intro`/
`.unfold_*` to record `(a.subst…, b.subst…)` closed at
depth 0 (i.e., the entry as it would appear at the empty
context). Then `Seen.Closed S` is preserved through the
induction. Requires a "close at Γ" operation on Exprs and
proofs that the algorithm's `quote` produces the same
closed pairs.

(c) **Don't generalise — prove `narrow_head` directly**
without the cutoff-`c` generalisation. The induction on
`Subtype' S (A :: Γ) M N` keeps `S` fixed; the binder cases
recurse at `S` (unshifted) and a deeper `Γ`. The `.hyp`
case is then trivial (S unchanged). The `.bvar 0` case
needs `Subtype'.weaken` of `h_BA : Subtype' S Γ B A` to
`B :: Γ`, which is `ctx_extend_at` at cutoff 0 — so this
recurses into the same problem unless `weaken` is proven
separately for the head-only case.

(c) is closest to what the bridge actually needs and
avoids touching `Subtype'`. (a) is most principled.
Deferred until either an `Equiv.shift` fork or a fresh
look establishes which is least disruptive.

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
