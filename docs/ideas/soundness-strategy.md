# Och soundness — lemma dependency map (overnight Stage 1)

**Status:** mapping doc only, no proofs. Stage 1 of an overnight effort
to close the four sorried theorems in `lean/Och/Soundness.lean`.

**Read first:**

- `docs/what-is-och.md` — Och is a *proof instrument*, not a useful
  language. North-Star property: if `concEval(e) = v` (concrete) and
  abstract type evaluation gives `t`, then `v ∈ t`.
- `docs/ideas/sorry-closure-plan.md` — post-mortem of the previous
  (typed-NbE) substrate. Four subagent attempts walled. Read the
  "Execution outcome" section — most of the failure modes (Halting-
  problem-style obstacles around `fullyQuotable`, `Subtype'` UNSHIFT
  research-grade lemma) reappear here in a different form.
- `docs/ideas/engine-collapse.md` — explains why we now have substitution-
  based eval (`evalSubst`) plus a single public API
  (`Och.synth`/`Och.subCheck`).

**This doc is a map, not a climb.** Subsequent agents pick lemmas from
§3 / §5 to attempt. They should also read §4 — there are walls visible
from here that we should not waste agent budget on.

---

## 0. Invariants any honest reader should hold

1. The **soundness target** for Och is conditional preservation:
   `synth e = .ok v → concEval e = .ok e' → ∃ τ. e' ⊑ τ`.
   It is *not* progress (well-typed terms don't get stuck) and not
   normalization. See `docs/ideas/soundness-strengthen.md` for why
   progress is intentionally deferred.
2. The substrate is **substitution-based**. `evalSubst` (in
   `Och/EvalSubst.lean`) is `partial def` and has **zero proven
   lemmas**. `subCheckSubst` is also `partial def` mutual block with
   zero proven lemmas. This is the bulk of the work below.
3. `Subtype'` (in `Och/Subtyping.lean`) has `narrow_at`,
   `ctx_extend_at`, `weaken`, `app_elim`, `app_head`, `app_ascent`,
   `shift_above_closed`, `shift_nil_closed`. These are real assets.
   The UNSHIFT-at-cutoff-0 lemma is **not** present (only
   `unshift_trivial` at cutoff `Γ.length`); the doc-comment at line
   1058–1123 of `Subtyping.lean` is the past plan that walled.
4. The **Simple/** subdirectory (`Och/Simple/*.lean`) has a complete
   Sub-level soundness story for a much smaller calculus (no fix/iota,
   no seen-set, no substitution-with-large-bvar trick, single
   substitution lemma). It is the model agents should mentally
   compare against. Most of the structural plumbing in `Simple/`
   ports verbatim; the seen-set / fix-iota / level-bvar additions are
   what make the full Och version hard.

## 1. Theorem inventory (Och/Soundness.lean)

All four bodies are `sorry`. Statements verbatim:

### 1.1 `synth_sound`

```lean
theorem synth_sound
    {fuel : Nat} {e : Expr} {v : Och.WTValue}
    (h : Och.synth e fuel = .ok v) :
    ∃ τ, Subtype' [] [] e τ := sorry
```

**Informal:** if the structural walk in `Och.synth` accepts `e`, then
`e` has *some* declarative supertype.

**Och-identity link:** this is the typing-side of "terms are types".
The intended witness per the doc-comment is `e` itself: synth doesn't
infer a separate type, it walks `e` and produces `e`'s WHNF as a
type-via-Refl. So `τ = e.whnf` (or even `τ = e`) should always work.
The existential is essentially trivial *if* `Subtype'.refl` covers
`e ⊑ e` — which it does (the `refl` constructor is unconditional).

**Honest reading:** this theorem as stated is *very weak* — `Subtype'.refl _`
discharges `∃ τ. Subtype' [] [] e τ` for *any* `e`. Even an ill-formed
term would satisfy this; the existential is not informative. So the
theorem either (a) is misframed and should be strengthened to a
*meaningful* statement (e.g. `Subtype' [] [] e v.whnf` plus
something asserting `v.whnf` is a head-normal form derivable from `e`
under β), or (b) is intentionally a trivial scaffold and the work is
elsewhere. **Flag for user review** — see §6.

### 1.2 `subCheck_sound`

```lean
theorem subCheck_sound
    {fuel : Nat} {a b : Och.WTValue}
    (h : Och.subCheck a b fuel = .ok true) :
    Subtype' [] [] a.whnf b.whnf := sorry
```

**Informal:** the algorithmic check `subCheckSubst` (engine) accepts
`(a.whnf, b.whnf)` only when the declarative `Subtype' [] []` relation
holds.

**Och-identity link:** this *is* the soundness of the typing decision
procedure. Subtyping = set inclusion in Och's semantic story; `Subtype'`
is the declarative formalisation. If the algorithm accepts where the
declarative spec rejects, Och is unsound on its core claim.

**This is the hardest of the four.** The engine has 24 distinct shape-
arms (`subCheckSubstMatch`), uses a level-bvar encoding (`shiftL` /
`substL`) that is *not* the same as `Expr.shift`/`Expr.subst`, and
calls `evalSubst` between every shape-decision. Bridging the engine's
seen-set (`List (Expr × Expr)`, no depth tag) to `Subtype'`'s
depth-tagged `Seen` is non-trivial.

### 1.3 `concEval_preservation`

```lean
theorem concEval_preservation
    {fuel : Nat} {e e' τ : Expr}
    (hcl : e.closedAt 0 = true)
    (hty : Subtype' [] [] e τ)
    (hstep : concEval fuel e = .ok e') :
    Subtype' [] [] e' τ := sorry
```

**Informal:** standard preservation. If `e ⊑ τ` declaratively and `e`
β/ι/fix-reduces to `e'`, then `e' ⊑ τ`.

**Och-identity link:** this is preservation. `concEval` is closed-term
CBV with substitution semantics. `Subtype'` is closed under β
(constructors `beta_L`, `beta_R`, `letE_L`, `letE_R`, `asc_L`, `asc_R`),
under ι/fix unfold (`unfold_iota_*`, `unfold_fix_*`). So preservation
should reduce to:

> for every reduction step `e → e₁` that `concEval` makes,
> `Subtype' S Γ e τ → Subtype' S Γ e₁ τ`.

The Simple/ analog `evalPreservation` is **proven** (Simple/Soundness.lean
~line 496) for the small calculus. The full version has to handle ι,
fix, seen-set propagation, and `concEval`'s lazy-arg / non-CBV-arg quirks
under app.

**Tractability:** mechanical-to-medium. The hard work is the per-step
substitution lemma (1.5 below), not preservation itself.

### 1.4 `soundness`

```lean
theorem soundness
    {fuel : Nat} {e e' : Expr} {a b : Och.WTValue}
    (hcl : e.closedAt 0 = true)
    (hsynthA : Och.synth e fuel = .ok a)
    (hsynthB : Och.synth b.whnf fuel = .ok b)
    (hcheck : Och.subCheck a b fuel = .ok true)
    (hstep : concEval fuel e = .ok e') :
    Subtype' [] [] e' b.whnf := sorry
```

**Informal:** end-to-end. A well-checked `e ⊑ b` evaluates to a value
`e'` that is still `⊑ b.whnf`.

**Och-identity link:** the North Star. This is exactly the property
`docs/what-is-och.md §Key Properties to Prove (2)`.

**Tractability:** **trivial composition** of 1.1, 1.2, 1.3 *if* those
three close. Specifically:

1. `synth_sound hsynthA` gives `∃ τₐ. Subtype' [] [] e τₐ` (the type
   `a.whnf` plays the τₐ role).
2. `subCheck_sound hcheck` gives `Subtype' [] [] a.whnf b.whnf`.
3. Transitivity (`Subtype'.trans`) gives `Subtype' [] [] e b.whnf`.
4. `concEval_preservation hcl _ hstep` gives the result.

The composition is one Lean tactic block. No extra research lemmas.
**This means agents should not work on `soundness` directly** — work
on its components.

## 2. Core dependency graph

```
                   soundness
                  /    |    \
              synth_  sub-   concEval_
              sound   Check_ preservation
                      sound
                       |        |
              ┌────────┴────┐   |
              |             |   |
        engine→Subtype'   engine fuel-
        bridge per arm    monotonicity
              |
        ┌─────┴─────┬───────┬──────────┬──────────┐
        |           |       |          |          |
   evalSubst   substL  shiftL    seen-set    neutralAscent
   correctness lemmas  lemmas    bridge      soundness
    (vs concEval)
```

The bridges break into 5 layers (innermost to outermost):

### Layer 1: substitution arithmetic on `Expr`
*Already mostly present* in `Syntax.lean`. Key existing lemmas:
- `shift_subst_cancel`, `shift_subst_cancel_gen`
- `shift_shift`, `shift_shift_same`, `shift_shift_comm_gen`,
  `shift_shift_between`
- `subst_shift_swap`, `subst_shift_swap_gen`
- `shift_closedAt`, `subst_closedAt_gen`, `closedAt_mono`,
  `shift_of_closedAt`
- `substEnv_subst_comp`, `subst_substEnv_comm`, `substEnv_idEnv`

**Status:** rich, mature. Likely sufficient for everything else.

### Layer 2: `evalSubst` ≃ `concEval` (on closed terms)
The engine uses `substL` and `shiftL`, the level-bvar variants. The
declarative `Subtype'` and `concEval` use `Expr.subst` / `Expr.shift`.
On terms with no level-vars (i.e. real Och programs), the two coincide.
This needs to be **proved**.

| Lemma | Statement | Difficulty | Status |
|---|---|---|---|
| `substL_eq_subst_no_levelvars` | If `s` and `e` have no level-vars (≥ levelOffset), `substL e j s = e.subst j s` | mechanical | unstated |
| `shiftL_eq_shift_no_levelvars` | similar | mechanical | unstated |
| `evalSubst_concEval_agree` | `e.closedAt 0 → no-level-vars(e) → evalSubst f u e = .ok v ↔ concEval f' e = .ok v` (modulo fuel) | medium | unstated |
| `evalSubst_closedAt` | mirror of `concEval_closedAt` | mechanical | unstated |
| `evalSubst_fuel_mono` | mirror of `concEval_fuel_mono` | mechanical | unstated |
| `evalSubst_no_levelvars_preserved` | if input has none, output has none | mechanical | unstated |

These are mechanical but tedious — `evalSubst` is `partial def`, so
agents will need to use `evalSubst.eq_def` or unfold it manually rather
than `match_target`.

### Layer 3: `Subtype'` closed under reduction
This is the core preservation lemma.

| Lemma | Statement | Difficulty | Status |
|---|---|---|---|
| `Subtype'.subst_step_L` | `Subtype' S Γ (.app (.lam A b) a) τ → Subtype' S Γ (b.subst 0 a) τ` | mechanical (one `cases` on `beta_L`/refl/trans) | unstated |
| `Subtype'.iota_unfold_step_L` | `Subtype' S Γ (.iota A b) τ → Subtype' S Γ (b.subst 0 (.iota A b)) τ` | mechanical | unstated |
| `Subtype'.fix_unfold_step_L` | `Subtype' S Γ (.fix A b) τ → Subtype' S Γ (b.subst 0 (.fix A b)) τ` | mechanical | unstated |
| `Subtype'.let_step_L` | `Subtype' S Γ (.letE v b) τ → Subtype' S Γ (b.subst 0 v) τ` | mechanical | unstated |
| `Subtype'.asc_step_L` | `Subtype' S Γ (.asc e t) τ → Subtype' S Γ e τ` | mechanical | unstated |

These are NOT generally true as standalone lemmas — they hold "at the
top level" because `Subtype'` is closed under β (the `beta_L` etc
constructors), but the obvious *inversion* direction is not. The
honest formulation is more like:

> `Subtype' S Γ a τ → ∀ a'. step a a' → Subtype' S Γ a' τ`

where `step` is the (deterministic, head-) reduction relation that
`concEval` actually performs. Need to:

| Lemma | Statement | Difficulty | Status |
|---|---|---|---|
| `Subtype'.preserve_step` | `concEval`-style head step preserves `Subtype'` | medium-hard (24 cases × 7 step shapes) | unstated |

Better approach: define a small inductive `HeadStep : Expr → Expr →
Prop` mirroring `concEval`'s reduction rules, prove
`Subtype'.preserve_HeadStep`, prove `concEval _ e = .ok e' → ∃ steps,
HeadStep* e e'`. The Simple/ proof structures things this way (without
the inductive HeadStep — it inlines the case analysis).

### Layer 4: engine `subCheckSubst` ≃ `Subtype'` (the hard bridge)
This is where the previous typed-NbE pass walled (`docs/ideas/sorry-closure-plan.md`).
The new substrate has different walls but the same flavor.

| Lemma | Statement | Difficulty | Status |
|---|---|---|---|
| `subCheckSubst_sound_arm_lam_lam` | engine accepts `λ ⊑ λ` ⟹ `Subtype'` derivation via `.lam` | mechanical | unstated |
| `subCheckSubst_sound_arm_iota_iota` | same for ι ⊑ ι (structural arm + `iota_intro` fallback) | medium | unstated |
| `subCheckSubst_sound_arm_fix_fix` | same for fix ⊑ fix | medium | unstated |
| `subCheckSubst_sound_arm_iota_R` | engine `_ ⊑ ι` ⟹ `iota_intro` | medium | unstated |
| `subCheckSubst_sound_arm_fix_R` | engine `_ ⊑ fix` ⟹ `unfold_fix_R` | medium | unstated |
| `subCheckSubst_sound_arm_iota_L` | engine `ι ⊑ _` ⟹ `unfold_iota_L` | medium | unstated |
| `subCheckSubst_sound_arm_fix_L` | engine `fix ⊑ _` ⟹ `unfold_fix_L` | medium | unstated |
| `subCheckSubst_sound_arm_neutral` | spine compare ⟹ chain of `app_cong` + `bvar` | medium | unstated |
| `subCheckSubst_sound_arm_ascent` | `neutralAscent` ⟹ `bvar` chain + `trans` | medium-hard | unstated |
| `subCheckSubst_sound_arm_bot_L` | engine `bot ⊑ _` ⟹ `bot_L` | trivial | unstated |
| `subCheckSubst_sound_arm_top_R` | engine `_ ⊑ type` ⟹ `top` | trivial | unstated |
| `subCheckSubst_sound_seenBridge` | seen-list (no tag) → seen-Set (with tag) translation | medium-hard, may wall | unstated |
| `subCheckSubst_sound` | top theorem; mutual induction via `(fuel, sizeOf a + sizeOf b)` lex | hard | unstated |

Each "arm" lemma assumes the bridge holds inductively for sub-calls
(co-induction-via-strong-induction-on-fuel). They're not provable
independently — they all close in one big mutual block.

### Layer 5: `Och.synth` correctness
The `synth_sound` statement (§1.1) reduces to either:

(a) trivial `Subtype'.refl` — if the user accepts the existential as
trivial, no work needed.

(b) a **stronger** statement we should propose: e.g.
`synth_sound_strong : Och.synth e = .ok v → Subtype' [] [] e v.whnf
∧ ConcNF v.whnf` — saying synth's WHNF is a real type-witness for `e`,
and `e ↪* v.whnf` declaratively.

Either way, agents working on §1.1 need a verdict from the user on
which formulation is intended (see §6 wall-1). Until then, treat 1.1
as parked.

## 3. Prioritisation for follow-up agents

Order is dependency-driven. Agents go strictly down the list; each
must finish (or be flagged walled) before the next starts in earnest.

### Priority A — substrate hygiene (Agents 2–4, parallel-safe)

These are mechanical, parallelisable, and unblock everything else.
Agent failures here are diagnostic — if these wall, the substrate
choice itself is in question.

- **A1**: prove `evalSubst_fuel_mono`. Pattern: copy `concEval_fuel_mono`
  arm-for-arm. ~150 LOC.
- **A2**: prove `evalSubst_closedAt` (closedness preserved by eval).
  Pattern: copy `concEval_closedAt`. Will need
  `substL_closedAt` (mechanical, ~50 LOC pre-req).
- **A3**: prove `substL_eq_subst_no_levelvars` and
  `shiftL_eq_shift_no_levelvars`. Pattern: induction on `Expr`.
  Possibly need a `noLevelVars : Expr → Bool` predicate. ~100 LOC.

If all three close: the substrate is well-behaved on real Och programs.
Layer 2 done. Move to Priority B.

If A1 walls: `evalSubst`'s `partial def` shape is the cause. Possible
fix: re-derive `evalSubst` with explicit termination (it has a lex
measure already documented; just hasn't been written out). Tier-2
research effort. Agent should flag and stop.

### Priority B — preservation arm (Agents 5–7)

Build up to `concEval_preservation`. Each builds on its predecessor.

- **B1**: prove `Subtype'.preserve_betaStep`: if
  `Subtype' S Γ (.app (.lam A b) a) τ`, then `Subtype' S Γ (b.subst 0 a) τ`.
  Strategy: case split on the derivation of the LHS. The `beta_L`
  rule provides exactly the desired conclusion; `app_cong`/`refl`/`trans`/
  `top` cases compose. **Watch out:** `app_cong`'s direction —
  the LHS reduces, but the RHS may not. If derivation goes through
  `app_cong` from a non-redex shape `app f a ⊑ app (lam A b) a'`, you
  need a lemma that the LHS wasn't really a redex shape. This may
  force you to characterize WHNF.
- **B2**: prove the same for ι-unfold, fix-unfold, let-step,
  asc-step. Five short lemmas, all in the same shape. Mechanical
  if B1 closed.
- **B3**: prove `concEval_preservation` itself (= §1.3) by induction
  on fuel + case on `e`. Each step uses one of B1/B2 results plus
  inductive hypothesis. Pattern: copy structure from
  `concEval_closedAt`. ~300 LOC.

### Priority C — engine soundness arms (Agents 8–10, partly parallel)

Pre-req: A1–A3, B1–B3. The engine soundness proof is one big mutual
block, but individual arm lemmas can be drafted in isolation
(assuming the inductive hypothesis as an axiom for now) and then
linked.

Approach **incrementally**:

- **C0**: define a compatibility relation `seenList_to_seenSet :
  List (Expr × Expr) → Ctx → Seen` that lifts the engine seen-list
  (no depth tag) to the declarative seen-set (with depth tag = current
  Γ.length). Prove monotonicity: extending the engine list with
  `(a, b)` corresponds to extending the seen-set with
  `(Γ.length, a, b)`. ~50 LOC.
- **C1**: easy arms: `bot_L`, `top_R` (`b == .type`), refl
  (`a == b`). ~100 LOC.
- **C2**: λ ⊑ λ arm. ~150 LOC. Uses C0 for the seen-set, B1 etc are
  not needed (no β happens here, only structural).
- **C3**: ι ⊑ ι, fix ⊑ fix structural arms (no fallback). ~250 LOC.
- **C4**: ι ⊑ ι, fix ⊑ fix fallback arms (`iota_intro`, fix-unfold).
  ~300 LOC.
- **C5**: `_ ⊑ ι`, `_ ⊑ fix` arms. ~250 LOC.
- **C6**: `ι ⊑ _`, `fix ⊑ _` arms. ~250 LOC.
- **C7**: neutral spine + `neutralAscent` arm. The hardest. ~400 LOC.
  **Likely to wall** — see §4.
- **C8**: stitch the mutual block; `subCheckSubst_sound` (§1.2). ~200
  LOC, but only if all C-arms close.

Stop and ask if C7 walls — there's a Subtype'-substitution-or-shift
question that we know is research-grade (§4 wall-2).

### Priority D — composition

- **D1**: prove `soundness` (§1.4) by composing 1.1–1.3 (one tactic
  block). Trivially mechanical *iff* 1.1, 1.2, 1.3 close.

### Priority E — synth_sound disposition

- **E1**: ask user: do you want the trivial existential (close with
  `⟨e, .refl _⟩`) or a strengthened `synth_sound_strong`? Pick the
  strengthening if asked — see §6.

**Recommended overnight schedule:**
- Hour 1–2: Agent 2 attempts A1+A2 in parallel with Agent 3 on A3.
- Hour 2–4: Agent 4 attempts B1, Agent 5 attempts C0+C1.
- Hour 4–6: Agent 6 attempts B2+B3, Agent 7 attempts C2.
- Hour 6–8: Agents 8–9 attempt C3+C4.
- Hour 8–10: Agent 10 attempts C5+C6 if C3+C4 closed; otherwise reassess.
- Hour 10+: stop, write up state.

Most likely outcome: A1–A3 close cleanly, B1 closes, B2+B3 close,
C0–C2 close, **C7 walls** (the Subtype' UNSHIFT-style obstacle).
Soundness is then 80% built; the bridge remains research-grade.

## 4. Anticipated walls

### Wall 1 — `synth_sound` is trivially provable as stated

The existential `∃ τ. Subtype' [] [] e τ` closes with `Subtype'.refl _`
for *any* `e`, ill-typed or not. The theorem is vacuous. Either:

- **option A**: accept it as a trivial scaffold and use it that way.
  No real work.
- **option B**: strengthen to `Subtype' [] [] e v.whnf ∧ Subtype'.refl
  v.whnf` or similar. This makes synth_sound load-bearing.

**Recommendation:** ask the user before any agent starts work. Until
then `synth_sound` is parked.

### Wall 2 — `subCheckSubst` neutral-arm seen-set semantics

The engine's seen-list discards depth (`List (Expr × Expr)`). The
declarative `Subtype'` seen-set uses depth tags
(`List (Nat × Expr × Expr)`) and binds `.hyp` rule shifts to
`(Γ.length - d)`. The lift `engine list → declarative set` at the
*current* Γ-length works for shallow goals, but as the recursion
descends through binders the engine's list semantics start to diverge
from the declarative semantics — the engine never re-tags entries
when entering a binder, but the declarative `.hyp` rule auto-shifts.

This is precisely the same flavour of obstacle that walled
`Subtype'.unshift_head` (`Subtype'.lean` line 1058–1123, post-mortem
in `sorry-closure-plan.md`). The 300–500 LOC structural induction
with seen-set rewiring still applies. Tractable but research-engineering.

**Predicted outcome:** C7 will wall here unless we can establish a
"seen-set commutes with binder entry" lemma. There's a workaround:
*forbid* agents from descending under binders with non-empty seen-set
(this is what algorithmic seen-sets actually do via the productive-
unfold guard), but encoding that as a Lean invariant requires
threading a closedness side-condition through `subCheckSubst`.

### Wall 3 — `evalSubst` is `partial def`

The structural induction proofs (A1, A2) need `evalSubst.eq_def` (the
"unfolding theorem" Lean generates for partial defs). It exists but is
delicate to use — `partial def` doesn't reduce definitionally, only
propositionally via `eq_def`. Expect tactic complexity beyond the
Simple/ analog.

**Predicted outcome:** A1+A2 close but with ugly proofs and 2x more
LOC than the Simple/ analog. Consider de-partialising `evalSubst` first
(the docstring claims a lex measure on `(fuel, unf)` exists, just
unwritten).

### Wall 4 — `concEval` vs `evalSubst` divergence on level-bvars

`concEval` (`Eval.lean`) errors on `.bvar k` for *any* k. `evalSubst`
returns `.ok (.bvar k)` for `k ≥ levelOffset` (free level-vars are
neutral values). The two evaluators disagree on open terms. The
`evalSubst_concEval_agree` lemma (Layer 2) only holds on terms with
**no level-vars** — i.e. real source programs that haven't gone
through `openFreshTop`.

**Predicted outcome:** the soundness chain has to either:
(a) only use `concEval`, treating `evalSubst` as an internal engine
detail with its own correctness lemma against `Subtype'`, OR
(b) introduce a level-var-aware variant of `concEval` and prove
agreement.

(a) is simpler but means the engine soundness proof has to talk to
`Subtype'` directly without going through `concEval_preservation`.

### Wall 5 — fix-unfold is not productive in `evalSubst`

`evalSubst`'s `.app (.fix A b) a` arm checks `isNeutral a || unf == 0`
before unfolding. So `(fix A b) (lvl 5)` does NOT unfold (since `(lvl 5)`
is neutral). Whereas the declarative `unfold_fix_R` rule unconditionally
unfolds. This means the algorithm and the declarative spec **disagree**
on when to unfold fix at app — the algorithm is more conservative.

For soundness this is OK: the algorithm under-approximates
acceptance, so accepted ⟹ derivable. But the proof has to handle
this asymmetry: when proving "engine accepted X ⟹ X is derivable",
you can always insert *more* declarative unfolds in the witness.

**Predicted outcome:** survivable but adds case-bloat to C5/C6.

## 5. Sub-task templates for follow-up agents

Each is sized for one focused agent session (~2–4 hours).

### Template 1 — A1 `evalSubst_fuel_mono`

> **File:** `lean/Och/EvalSubst.lean` (or new file
> `lean/Och/EvalSubstLemmas.lean` if `partial def` is a problem).
>
> **Goal:** prove
> ```lean
> theorem evalSubst_fuel_mono {n unf : Nat} {e v : Expr}
>     (h : evalSubst n unf e = .ok v) :
>     evalSubst (n + 1) unf e = .ok v
> ```
>
> **Pattern:** mirror `concEval_fuel_mono` in `Och/Eval.lean` (lines
> 243–296). Uses `evalSubst.eq_def` to unfold the `partial def`.
> Take care: `evalSubst`'s match cases include β/let with internal
> recursive calls; those use the same fuel value — preservation under
> `n+1` is direct.
>
> **Pre-reqs:** none. **Estimate:** mechanical, 150 LOC. **Risk:**
> `partial def` unfolding may force tactic complexity beyond the
> non-partial analog. If it walls, propose de-partialising `evalSubst`
> first (the lex measure `(fuel, unf)` is documented; just write it).
>
> **Acceptance:** `lake build` green, theorem unfolds without `sorry`.

### Template 2 — A2 `evalSubst_closedAt`

> **File:** as A1.
>
> **Goal:**
> ```lean
> theorem evalSubst_closedAt {n unf : Nat} {e v : Expr}
>     (hcl : e.closedAt 0 = true)
>     (h : evalSubst n unf e = .ok v) : v.closedAt 0 = true
> ```
>
> **Pattern:** mirror `concEval_closedAt` (`Och/Eval.lean` lines 112–242).
> Pre-req: `substL_closedAt_gen` — a closedAt-preservation lemma for
> `substL` analogous to `subst_closedAt_gen`. ~80 LOC pre-req.
>
> **Subtle point:** level-vars ≥ levelOffset have huge indices; the
> standard `closedAt 0` predicate would reject them. You may need to
> work with `closedAt_modulo_levelvars` or restrict to
> "no-level-vars" inputs. Talk to user if this comes up.
>
> **Estimate:** mechanical+, 250 LOC including pre-req. **Risk:** the
> level-var question above. Flag and ask if unclear.

### Template 3 — B1 `Subtype'.preserve_betaStep`

> **File:** `lean/Och/Subtyping.lean` (add at end, before
> `Sub Σ`-related defs).
>
> **Goal:**
> ```lean
> theorem Subtype'.preserve_betaStep {S Γ A b a τ}
>     (h : Subtype' S Γ (.app (.lam A b) a) τ) :
>     Subtype' S Γ (b.subst 0 a) τ
> ```
>
> **Pattern:** induction on `h`. Most cases yield directly (`refl`,
> `top`, `trans`, `bvar` impossible by shape, etc.). The interesting
> cases are `app_cong` and `beta_R`. For `app_cong`: the LHS structure
> says `app f a' ⊑ app (lam A b) a` with `f ⊑ lam A b`, `a' ⊑ a`,
> `a ⊑ a'`. Need to show `b.subst 0 a' ⊑ ?` — but the IH on `f ⊑ lam A b`
> is *not* directly useful since `f` may not itself be a `lam`. This
> case forces: when does `Subtype' S Γ f (.lam A b)` give
> `Subtype' S Γ (.app f a) (b.subst 0 a)`? Answer: that's exactly
> `Subtype'.app_elim` (already proved!). So derive via `app_elim` from
> the LHS, then transitivity.
>
> **Estimate:** medium, ~80 LOC. **Risk:** the `app_cong` case may need
> substitution-respecting lemma `Subtype'.subst_resp` (covariant
> substitution), which is currently *not present* and is itself a
> medium-hard lemma. If so, escalate.

### Template 4 — B3 `concEval_preservation`

> **File:** `lean/Och/Soundness.lean` (replace `sorry` for
> `concEval_preservation`).
>
> **Goal:** as stated in §1.3.
>
> **Pattern:** induction on fuel. Take cases on `e`. Mirror
> `concEval_closedAt` (`Och/Eval.lean`) for the case structure. At each
> reduction point, apply the matching B1/B2 lemma to update the
> Subtype' derivation, then apply IH to the reduced term.
>
> **Pre-reqs:** all B1, B2 lemmas. **Estimate:** mechanical+, 300 LOC.
> **Risk:** `app`'s neutral-arm (where `f' = .bvar k` etc) — neutrals
> don't reduce, so `e' = .app f' a'` and the question is whether
> `Subtype' [] [] (.app f a) τ → Subtype' [] [] (.app f' a') τ` when
> the components stepped. Need: covariant congruence under `.app`.
> This is `Subtype'.app_head` (already exists!) plus arg-cong (need
> to prove or use `app_cong`).

### Template 5 — C0 seen-set bridge

> **File:** new `lean/Och/SubCheckSoundnessLemmas.lean` (or end of
> Soundness.lean for now).
>
> **Goal:** define
> ```lean
> def liftSeenList (Γlen : Nat) (seen : List (Expr × Expr)) : Seen :=
>   seen.map (fun (a, b) => (Γlen, a, b))
> ```
> and prove
> ```lean
> theorem liftSeenList_cons (Γlen) (seen) (a b) :
>     liftSeenList Γlen ((a, b) :: seen)
>     = (Γlen, a, b) :: liftSeenList Γlen seen := rfl
> ```
> plus the key compatibility:
> ```lean
> theorem liftSeenList_unchanged_at_same_depth
>     {Γ : Ctx} {seen : List (Expr × Expr)} {a b : Expr}
>     (h : (a, b) ∈ seen) :
>     (Γ.length, a, b) ∈ liftSeenList Γ.length seen
> ```
>
> **Pattern:** straightforward `List.mem_map`. **Estimate:** trivial,
> 50 LOC. **Risk:** none. The interesting question is what to do
> when descending through a binder — that's wall-2; this template
> is just the easy first step.

### Template 6 — C2 λ ⊑ λ arm soundness

> **File:** as C0.
>
> **Goal:** in a mutual block with the rest of `subCheckSubst_sound`,
> prove the lambda case:
> ```lean
> theorem subCheckSubst_sound_lam_lam
>     {fuel : Nat} {tyCtx : Array Expr} {seen : List (Expr × Expr)}
>     {domA bodyA domB bodyB : Expr}
>     (h : subCheckSubst fuel tyCtx seen
>           (.lam domA bodyA) (.lam domB bodyB) = .ok true) :
>     Subtype' (liftSeenList tyCtx.size seen) <Γ-from-tyCtx>
>       (.lam domA bodyA) (.lam domB bodyB)
> ```
>
> **Pattern:** unfold `subCheckSubst` (partial def), reach the
> `.lam, .lam` arm, extract the contravariant domain check
> `subCheckSubst _ _ _ domB domA = true` and the covariant body
> check `subCheckSubst _ (push domB) _ (openFresh bodyA) (openFresh bodyB)
> = true`. Apply IH to each. Use `Subtype'.lam` to conclude. The
> `openFresh` calls add level-vars; you need to translate
> `Subtype'` on opened bodies to `Subtype'` on closed bodies under
> `(domB :: Γ)` — pre-req lemma `openFresh_Subtype_close`.
>
> **Estimate:** medium, 150 LOC plus pre-req. **Risk:** the
> `openFresh`/`closeLevelVar` ↔ Subtype' translation may itself need
> non-trivial substitution arithmetic.

### Template 7 — strengthen synth_sound

> **File:** `lean/Och/Soundness.lean`.
>
> **Pre-req:** user verdict on §6 wall-1.
>
> **Goal (option B):** replace `synth_sound`'s statement with
> ```lean
> theorem synth_sound
>     {fuel : Nat} {e : Expr} {v : Och.WTValue}
>     (h : Och.synth e fuel = .ok v) :
>     Subtype' [] [] e v.whnf
> ```
> (no existential — concrete witness).
>
> **Strategy:** induction on the structure of `e`. At each arm, recover
> what `synthCore` did (domain checks, β/ι/fix-fold), translate each to
> a `Subtype'` derivation. Heavy lift: every `synthCore` arm has a
> `subCheckOpen` call whose `.ok true` result needs `subCheck_sound`
> applied. So this is really only doable AFTER §1.2 closes.
>
> **Estimate:** hard, ~500 LOC. Not Stage-1 work; agents should not
> attempt without C-priority complete.

### Template 8 — de-partialise `evalSubst` (escape hatch)

> **File:** `lean/Och/EvalSubst.lean`.
>
> **Use:** only if A1 walls due to `partial def` complexity.
>
> **Goal:** convert `evalSubst` from `partial def` to `def` with an
> explicit `decreasing_by` clause using lex measure `(fuel, unf)`.
> Keep the body identical.
>
> **Pattern:** add `termination_by fuel + unf` or a true lex
> `Prod.lex Nat.lt Nat.lt`. Most arms decrease `fuel`; the ι-unfold
> and fix-unfold arms hold `fuel` and decrease `unf`. The β/let arms
> decrease `fuel` and pass `unf` unchanged.
>
> **Estimate:** medium, ~50 LOC change. **Risk:** if Lean's lex prover
> rejects the measure, may need to manually weave fuel through harder.

### Template 9 — define `noLevelVars`

> **File:** `lean/Och/Syntax.lean` (or extension thereof).
>
> **Goal:**
> ```lean
> def Expr.noLevelVars (offset : Nat := 100_000_000) : Expr → Bool
>   | .bvar k => k < offset
>   | .lam d b => d.noLevelVars offset && b.noLevelVars offset
>   ...
> ```
> plus `theorem subst_noLevelVars`, `theorem shift_noLevelVars`.
>
> **Estimate:** trivial, 50 LOC. **Use:** Layer-2 lemmas (substL ≃
> subst restricted to no-level-vars terms).

### Template 10 — `Subtype'.subst_resp` (covariant substitution)

> **File:** `lean/Och/Subtyping.lean`.
>
> **Goal:**
> ```lean
> theorem Subtype'.subst_resp
>     {S Γ a a' b b' : Expr}
>     (ha : Subtype' S Γ a a')
>     (hb : Subtype' S (a' :: Γ) b b') :
>     Subtype' S Γ (b.subst 0 a) (b'.subst 0 a')
> ```
>
> **Pattern:** induction on `hb`. Constructors that don't bind handle
> directly; binder cases need `narrow_at` to adjust contexts.
> **CAVEAT:** this lemma may be subject to the same UNSHIFT obstacle
> as wall-2. The Simple/Properties.lean has `Sub.subst_lemma`
> (line 27 of file: "subst_gen ... [Var] sorry'd") — it's PARTIALLY
> SORRIED in Simple already. So this is research-grade.
>
> **Estimate:** **research**, multi-day. Prerequisite for B1 in
> some derivation paths. **Recommend:** skip unless B1 hits the
> wall and demands it.

## 6. Open questions / things to ask the user

1. **`synth_sound` framing** (wall-1, §4): trivial existential or
   strengthened concrete witness? Affects whether agents work on §1.1
   at all.

2. **Substrate divergence** (wall-4, §4): proof goes through `concEval`
   only, or both `concEval` and `evalSubst` with explicit agreement?
   Affects the shape of layer-2 lemmas.

3. **Acceptable axiomatisation:** is it OK to take some lemmas as
   `axiom` if they wall and are not on the critical path? E.g.
   `Subtype'.subst_resp` axiomatised would unblock B1 without the
   research effort. The user has previously preferred "ship dead-end
   commits with documented walls" — the same pragma may apply here.

4. **`partial def` policy:** is it acceptable to de-partialise
   `evalSubst` and `subCheckSubst` *first* before any soundness work?
   This is ~1 day of focused work and would make all subsequent
   proofs significantly easier.

## 7. Honest scoping summary

| Theorem | True difficulty | Most likely overnight outcome |
|---|---|---|
| §1.1 `synth_sound` | **trivial as stated** (existential discharged by `refl`); **hard** if strengthened | parked pending user decision |
| §1.2 `subCheck_sound` | **research-grade** (engine bridge, seen-set, level-vars) | partial — easy arms close, hard arms wall |
| §1.3 `concEval_preservation` | **medium-mechanical** | likely closes overnight |
| §1.4 `soundness` | **trivial** if 1.1–1.3 close | follows automatically |

**Most realistic overnight target:** close §1.3 in full, close half of
§1.2's arms. §1.1 parked until user verdict. §1.4 closes
mechanically when its dependencies do.

**Total LOC budget:** ~3,000 LOC of new proof if everything closes.
~1,500 LOC realistic.

**Stop if:** any agent reports the seen-set bridge wall (wall-2).
That's a research problem, not a session problem.
