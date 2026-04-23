# Quote-witness feasibility: can Task 1 be closed without typing?

**Status:** research note, 2026-04-22.
**Scope:** determine whether the closure in `eval_vapp_preserves_fullyQuotable`'s
statement (`Val.fullyQuotable d v → ∃ q, quote fuelω d v = some q`) can be
closed under ANY proof-theoretic invariant strictly weaker than "well-typed".
**Companion to:** `docs/ideas/sorry-closure-plan.md` (Task 1),
`docs/ideas/soundness-strengthen.md` (Phase 2),
`DECISION-LOG.md` 2026-04-22 entry on Task 1.

## 1. Summary

**Headline finding: the implication is structurally false.** There exists
a concrete `v : Val` with `Val.fullyQuotable d v = True`, arising from
`eval` on a closed source expression, yet `quote fuelω d v = none`. The
counterexample is a direct semantic embedding of the Turing-complete
untyped λ-calculus Ω-combinator inside a closure's environment — the
outer `Val` itself has constant `sizeOf` and a fully-quotable env, but
invoking `quoteClosure` on it forces untyped β-reduction of `Ω`, which
does not terminate.

This rules out **all four** candidate invariants (fuel-parametric,
structural-size, step-indexed at the result, closed-at-zero). By the
standard reduction of termination of untyped λ-calculus to the Halting
Problem, any purely-structural predicate on `Val` that implies
`quoteClosure`-success would decide the Halting Problem, hence none
exists.

**Implication for Phase 1.** Task 1 as stated in `sorry-closure-plan.md`
is not closable without a typing invariant. The existing route —
threading `hnfq : ((eval fuelω unf ρ e).bind (quote fuelω d)).isSome`
per call site (`eval_quotable_open` / `OpenCtx.eval_quotes'`) — remains
the only route that does not require Phase 2 or intrinsic typing. The
`Val.fullyQuotable` predicate is still useful for closing `RList_depth_lift`
and downstream env-lifts, but it CANNOT discharge the quote-witness
obligation on its own. Tasks 2–4 should assume `∃ q, quote fuelω d v = some q`
is supplied from the caller (via `hnfq`), not derived from `fullyQuotable`.

**Implication for Phase 2.** Phase 2 as specified
(`docs/ideas/soundness-strengthen.md`) is about `concEval`, not `eval`
(NbE). It does NOT automatically close Task 1. Closing Task 1 in the
absence of typing invariants requires either adopting `hnfq`-threading
as permanent architecture, or a typed logical-relations refactor of the
NbE proof chain — neither of which the current Phase 2 scope addresses.

## 2. The core obstruction

### 2.1 The counterexample

We construct `v : Val` such that (a) `Val.fullyQuotable d v` holds, (b)
`v` arises from `eval n unf ρ e_src = some v` on a *closed source term*
`e_src` with small `n`, and (c) `quote fuelω d v = none`.

Let `B = body₀ := .app (.bvar 0) (.bvar 0)`. This is the term `x x` at
de Bruijn index 0 (used under one binder). Then:

```
ω : Val := .lam .type ⟨ B, [] ⟩                           -- the SK-Ω closure
envₒ    := [ω] : List Val
bodyₒ   := .app (.bvar 1) (.bvar 1)                        -- applies entry 1 of env to itself
v       := .lam .type ⟨ bodyₒ, envₒ ⟩
```

**Claim (a): `Val.fullyQuotable d v` holds for every `d`.**

Unfolding the definitions in `SoundnessProof.lean:1198–1223`:

- `Val.fullyQuotable d (.lam .type ⟨bodyₒ, envₒ⟩)` reduces to
  `Val.fullyQuotable d .type ∧ Closure.fullyQuotable d ⟨bodyₒ, envₒ⟩`.
- `Val.fullyQuotable d .type = True`.
- `Closure.fullyQuotable d ⟨bodyₒ, envₒ⟩` reduces to
  `bodyₒ.closedAt (envₒ.length + 1) = true ∧ Closure.envFullyQuotable d envₒ`.
  - `bodyₒ.closedAt 2 = (.bvar 1).closedAt 2 && (.bvar 1).closedAt 2
    = (1 < 2) && (1 < 2) = true`. ✓
  - `Closure.envFullyQuotable d [ω]` reduces to
    `(Val.fullyQuotable d ω ∧ ∃ qe, quote fuelω d ω = some qe) ∧
     Closure.envFullyQuotable d []`.
    - `Val.fullyQuotable d ω`: identical reasoning with `body₀ =
      .app (.bvar 0) (.bvar 0)`, `env_ω = []`. `body₀.closedAt 1 =
      true`. `envFullyQuotable d [] = True`. ✓
    - `∃ qe, quote fuelω d ω = some qe`: direct computation.
      `quote fuelω d ω = quote _ d (.lam .type cl_ω)` reduces to
      `.lam (quote _ d .type) (quoteClosure _ d cl_ω)`. The inner
      `quoteClosure fuelω d ⟨body₀, []⟩` does:
      ```
      let bv := .neutral (.var d)
      eval fuelω 1 [bv] (.app (.bvar 0) (.bvar 0))
         = vapp fuelω 1 bv bv
         = some (.neutral (.app (.var d) bv))           -- neutrals absorb
      quote fuelω (d+1) (.neutral (.app (.var d) bv))   -- terminates
      ```
      So `ω` quotes cleanly. ✓
    - `envFullyQuotable d []` = True. ✓

All bullets discharged; `Val.fullyQuotable d v = True`.

**Claim (b): `v` arises from `eval` on a closed source term.**

Let
```
e_src := (λf. λg. .app (.bvar 0) (.bvar 0))  (λx. .app (.bvar 0) (.bvar 0))
```
At the Expr level (de Bruijn):
```
e_src = .app
          (.lam .type                                    -- binds f
             (.lam .type (.app (.bvar 1) (.bvar 1))))   -- binds g; body = g g ... wait, bvar 1 = f here
          (.lam .type (.app (.bvar 0) (.bvar 0)))
```
This is `(λf. λg. f f) (λx. x x)` — a β-redex taking `Ω = λx.x x` as
argument. Evaluating:
1. `eval n unf [] e_src` reduces the outer `.app`:
   - f-side evaluates to `.lam .type ⟨λg. f f, []⟩` (call it `F`)
   - a-side evaluates to `.lam .type ⟨x x, []⟩ = ω`
   - `vapp n unf F ω` reduces the `.lam` head: `eval n unf (ω :: [])
     (.lam .type (.app (.bvar 1) (.bvar 1)))`
   - This matches the `.lam` case: evaluates `.type` (trivial), then
     constructs `.lam .type (Closure.mk' (.app (.bvar 1) (.bvar 1))
     [ω])`. `bvarBound (.app (.bvar 1) (.bvar 1)) = 2`, so `mk'`
     takes `take (2-1) = 1` of `[ω]`, giving `envₒ = [ω]`. ✓
2. Result: `v = .lam .type ⟨bodyₒ, envₒ⟩`. ✓

The source term `e_src` is closed (all bvar indices are bound within
the visible binders), and `eval` needs only ~5 fuel to produce `v`.

**Claim (c): `quote fuelω d v = none`.**

```
quote fuelω d v = quote fuelω d (.lam .type ⟨bodyₒ, envₒ⟩)
```
The `.lam` arm requires `quoteClosure fuelω d ⟨bodyₒ, envₒ⟩`:
```
let bv := .neutral (.var d)
eval fuelω 1 (bv :: envₒ) bodyₒ
  = eval fuelω 1 [bv, ω] (.app (.bvar 1) (.bvar 1))
  = do let f ← eval fuelω' 1 [bv, ω] (.bvar 1)        -- f = ω
       let a ← eval fuelω' 1 [bv, ω] (.bvar 1)        -- a = ω
       vapp fuelω' 1 ω ω
```
Now `vapp _ 1 ω ω` hits the `.lam` branch of `vapp` (since ω is a
lambda):
```
eval fuelω' 1 (ω :: env_ω) body₀
  = eval fuelω' 1 [ω] (.app (.bvar 0) (.bvar 0))
  = do let f ← eval fuelω'' 1 [ω] (.bvar 0)           -- f = ω
       let a ← eval fuelω'' 1 [ω] (.bvar 0)           -- a = ω
       vapp fuelω'' 1 ω ω                             -- LOOP
```
Each recursive `vapp _ 1 ω ω` decrements the outer `fuel` by exactly 1
(NOT `unf` — lambda reduction in `NbE.vapp` does not decrement `unf`,
only iota/fix do). After `fuelω = 100000` steps, `eval` returns `none`,
so `quoteClosure` returns `none`, so `quote fuelω d v = none`. ✓

### 2.2 Why this blocks Task 1

Task 1's target theorem (in `eval_vapp_preserves_fullyQuotable`) needs
to prove, for the `.app` case of eval:

> given `eval (k+1) unf ρ (.app f a) = some v`, `Val.fullyQuotable d v`.

The body of the proof needs to extract `f'` and `a'` from the eval,
then invoke `vapp_preserves_fullyQuotable` with hypotheses
`Val.fullyQuotable d f'`, `Val.fullyQuotable d a'`, `∃ qf', quote _ d f'
= some qf'`, `∃ qa', quote _ d a' = some qa'`. The first two come
from the outer IH; the last two do NOT. They must be produced from the
`fullyQuotable` hypotheses, which is precisely the implication
`fullyQuotable_has_quote : Val.fullyQuotable d v → ∃ q, quote fuelω d v
= some q`. By the counterexample, this implication is false.

The same obstruction recurs in the `.letE` case (line 2541) and in the
`.iota`/`.fix` unfold branches of `vapp` (lines 2597, 2608).

## 3. Candidates explored

### 3.1 Candidate 1 — Fuel-parametric

**Statement (informal):** `∀ k n ρ e v fuel, eval n unf ρ e = some v →
quote (k·n + c) d v = some q` for some polynomial `k·n + c` in the
eval fuel.

**Attempted direction.** The intuition is that a small `eval` output
must be "cheap" to quote.

**Outcome: FALSE.** The counterexample in §2.1 is produced by `eval`
with `n ≈ 5` fuel. Any polynomial `k·5 + c` is a constant, yet
`quote` requires unbounded fuel to terminate on `v`, which it doesn't.

More fundamentally: `eval` can build a large semantic tower of closures
with small fuel (one fuel unit per syntactic lam/app node), but the
closures encode unbounded reduction sequences. Eval fuel measures
syntactic traversal; quote fuel measures operational unfold depth.
These are uncoupled in untyped λ-calculus.

**Verdict: reject.**

### 3.2 Candidate 2 — Structural size

**Statement:** `∀ v d N, Val.fullyQuotable d v ∧ Val.sizeOf v ≤ N →
∃ q, quote (f(N)) d v = some q` for some function `f`.

**Attempted direction.** If `Val` is bounded structurally, maybe the
unfold depth is bounded.

**Outcome: FALSE.** The counterexample has constant `sizeOf`:

- `ω = .lam .type ⟨B, []⟩` — `sizeOf ω = 1 + 1 + sizeOf B + 1`
  (constants only, since `B` is a small fixed expression).
- `v = .lam .type ⟨bodyₒ, [ω]⟩` — `sizeOf v = 1 + 1 + sizeOf bodyₒ +
  1 + sizeOf ω`. All of bounded size.

`sizeOf` counts tree nodes of the semantic Val; it does not count
operational reduction steps. Closures share structure (the env is a
list, not an inlined substitution), so a single closure can "unfold"
into an unbounded reduction tree at quoteClosure time.

**Verdict: reject.**

### 3.3 Candidate 3 — Step-indexed fullyQuotable

**Statement:** redefine `Val.fullyQuotable` indexed by a step-index
`n`, such that `fullyQuotable_n d v → ∃ q, quote n d v = some q` and
the implication threads through eval (i.e., step-index decreases along
eval's recursion).

**Attempted direction (a) — tautological form.** Define
`fullyQuotable_n d v ≡ ∃ q, quote n d v = some q`. Then the implication
is trivial. But as a hypothesis in eval-preservation, it forces
`vapp_preserves_fullyQuotable` to receive a hypothesis saying "the
result already quotes", which the caller can't provide without
circular reasoning — eval produces the result, so claiming quote-at-n
before the production means doing quote in parallel with eval. This is
functionally equivalent to the `hnfq` threading already in use (see
`eval_quotes'`); it's not an invariant, it's a carried witness.

**Attempted direction (b) — Kripke / coinductive.** Define
`fullyQuotable_ω d v` as "for every substitution of env under any
fresh neutral, the body's eval terminates". This is a statement about
operational reduction closure. **But this predicate is undecidable:**

*Reduction to Halting.* Given a Turing machine `M` and input `x`,
encode `(M, x)` as an untyped λ-term `e_M` in the standard way (every
TM has a λ-calculus encoding). Then `e_M` terminates iff `M` halts on
`x`. Construct closure `cl = ⟨e_M, []⟩`. `fullyQuotable_ω d
(.lam .type cl)` iff `eval ω 1 [bv] e_M` terminates iff `M` halts on
`x`. A proof of this predicate preserving under eval (`eval-preserves-
fullyQuotable`) would require structural (hence computable) case
analysis, which contradicts the undecidability of halting.

More formally: any **first-order inductive predicate** `P` on `Val`
with the property `P v → ∃ q, quote fuelω d v = some q` (for a fixed
fuelω) induces a decidable approximation of halting. If `P` were
structurally recursive on `Val`, then deciding `P v` is decidable
(finite tree). But then `P v` could be used to decide whether
`quoteClosure fuelω d cl` returns `some _` or `none` — which by
construction is a halting problem for the λ-calculus fragment.
Contradiction unless `P` admits semantic/coinductive content (i.e., is
not structurally-recursive).

**Verdict (a): trivial reformulation, not an improvement.**
**Verdict (b): inherently non-structural; cannot be proved inductively
on Val.**

### 3.4 Candidate 4 — Closed-at-0 restriction

**Statement:** `e.closedAt 0 = true ∧ eval fuel unf [] e = some v →
∃ q, quote fuelω d v = some q`.

**Attempted direction.** Closed source terms might have simpler
quote behaviour.

**Outcome: FALSE.** The source term `e_src = (λf. λg. f f)
(λx. x x)` in §2.1 is `closedAt 0 = true` (verify: the only bvars are
`0` inside `λx. x x` which is bound by `λx`, and `1` inside `λg. f f`
which is bound by the outer `λf`). Yet the adversarial `v` is its
eval-result. Closedness of the source is insufficient.

**Deeper reason.** Closedness bounds *scope* but not *reduction
length*. The untyped λ-calculus has closed Ω-style terms that diverge;
closedness is orthogonal to termination.

**Verdict: reject.**

### 3.5 Candidate 5 — ConcNF on Val (structural)

**Statement:** define `ValConcNF d v` inductively to mean "`v`'s env
entries are themselves ValConcNF, closure bodies don't contain
self-application patterns" or similar.

**Attempted direction.** Exclude specific syntactic patterns that
cause looping.

**Outcome: FALSE.** Untyped λ-calculus has no "syntactic" signal of
divergence. The pattern `.app (.bvar k) (.bvar k)` is innocuous by
itself (it could be `neutral_var_k neutral_var_k`, which terminates).
Only when `.bvar k` is substituted by a *lambda* does it diverge, and
this depends on the env, not the body. The env is an arbitrary
`List Val` — there's no syntactic pattern one can exclude without
losing the λ-calculus's expressive power.

More specifically: for ANY purported syntactic predicate `Q` on
`(body, env)` pairs with `Q (body, env) → quoteClosure-terminates`,
the Böhm-style encoding of arbitrary computation means `Q` must exclude
either all self-applications (too restrictive — disallows identity
applications like `(λx. x) (λx. x)`, which are valid Och programs
after erasure) or refer to semantic properties of env entries
(non-structural, already handled in Candidate 3).

**Verdict: reject.**

### 3.6 Candidate 6 — Typed fullyQuotable

**Statement:** require `Val.fullyQuotable` to additionally carry a
typing hypothesis `∃ Γ τ, Subtype' [] Γ (quote v) τ` (or
equivalent in the Val-level SubV relation).

**Attempted direction.** Types classically rule out Ω. The adversarial
`v` is not typable (the term `(λx. x x)` requires `X = X → Y`, which
is not inhabited in pure system with positivity).

**Outcome: PROVABLE in principle, but not without Phase 2 / intrinsic
typing.**

The standard NbE fundamental lemma says: *if `e` is well-typed at `τ`
in `Γ`, and `ρ` realises `Γ` at `d`, then `eval fuel unf ρ e = some v`
for sufficiently large fuel, and `quote fuelω d v` terminates.*
Formalising this requires:

1. A Val-level logical relation `⟦τ⟧_d` that saturates reducibility
   candidates at each type (standard for NbE).
2. The fundamental lemma's induction on `e`, quantifying over all
   realising environments.
3. A bridge from `typeCheck` to "well-typed at τ in some derivation
   tree".

This is the *typed NbE* proof architecture, and it is NOT what Och's
current `SoundnessProof.lean` implements. The current architecture
uses a *syntactic* `R` relation (step-indexed, Equiv_c on quote
output) that sidesteps reducibility candidates; but as a consequence,
it cannot extract quote-termination from the `R`-relation alone —
which is why `hnfq` must be threaded.

**Verdict: provable with intrinsic typing (e.g., the Phase-2 refactor
or a typed-eval refactor). Not provable in the current scope.**

## 4. Implications

### 4.1 For Option 1 (Phase 1 only)

Option 1 — closing Task 1's 4 declaration-sorries + 16 internal
sub-sorries under the preservation-only metatheory — is **not closable
as specified in `sorry-closure-plan.md`**. The plan assumed that
strengthening the conclusion of `eval_vapp_preserves_fullyQuotable` to
carry `∃ q, quote fuelω d v = some q` would be derivable from a
suitably extended `Val.fullyQuotable`. That derivation does not exist.

**Salvage route (A): hnfq-threading as permanent architecture.** The
existing `eval_quotes' / eval_quotable_open` already threads `hnfq`
per call site (see `SoundnessProof.lean:4827, 5019, 5618`). The
`Val.fullyQuotable` predicate continues to be useful for:

- `RList_depth_lift`'s recursion into env entries.
- `quote_depth_shift_n`'s levelsBelow prerequisite.
- `Closure.fullyQuotable`'s `body.closedAt (env.length+1)` conjunct.

But `∃ q, quote fuelω d v = some q` must always come from a caller's
`hnfq` hypothesis, never from `fullyQuotable` alone.

**Consequence for Tasks 2, 3, 4.** Each needs review:

- **Task 2 (`vapp_realises`)** already specifies 6 new hypotheses
  including `hqvf`, `hqva`. These can be supplied by the caller via
  `eval_quotes'`, provided the caller has an `hnfq` witness. This is
  doable — caller sites already thread `hnfq`. Task 2 remains
  feasible.
- **Task 3 (`quoteClosure_realises`)** is a forward-reference
  structural issue, unrelated to quote-witness circularity. Still
  feasible.
- **Task 4 Category A** (sub-sorries at 5243, 5303, 5305, 5306) —
  these were slated to be closed by the "strengthened
  `eval_preserves_fullyQuotable`". Under the salvage: they need their
  own `hnfq` witnesses threaded through `tyInfer_sound_open`. Requires
  a mechanical restatement: `tyInfer_sound_open` gets an `hnfq`
  argument, which cascades down to the `Val.fullyQuotable`-consuming
  call sites. Feasible but more invasive than the original plan.

**Salvage route (B): accept that `eval_vapp_preserves_fullyQuotable`
remains a declaration-level sorry.** Proceed with Tasks 2, 3, 4; note
that `fullyQuotable`'s preservation is not closed but is not strictly
needed on the critical path to `typeCheck_sound` if the `hnfq` route is
adopted universally. This leaves 1 declaration-level sorry permanent
in Phase 1.

### 4.2 For Option 2 / Phase 2

Phase 2's `progress_mod_fuel` refactor, as specified in
`soundness-strengthen.md`, concerns `concEval` (substitution-based),
**not** `eval` (NbE). It does NOT automatically close Task 1's NbE
sorries. The `.app` case of `progress_mod_fuel` needs to reason about
`concEval`'s behaviour, which is operational (β via substitution) and
doesn't carry closures-with-envs. So the Ω-style divergence in `eval`
persists into `concEval` (at the `.app .type a` stuck arm, not at
closure-quote divergence), but the obstruction is different: in
`concEval` the issue is "stuck on Type-applied-to-arg", in `eval +
quote` it's "unbounded reduction inside a closure".

**Phase 2 does not subsume Task 1.** If Task 1 is to be closed without
typing, it needs an orthogonal effort: either `hnfq`-threading (Option
1 salvage), or a typed-eval refactor (not in any current plan).

### 4.3 Intermediate options

**Option 1.5 (hybrid)**: adopt the `hnfq`-threading salvage for Task 1,
leave `eval_vapp_preserves_fullyQuotable` sorried, close Tasks 2–4
under the assumption that each `hnfq` call site either receives a
threaded witness (closed case) or sorries locally. This gives a
partial Phase-1 outcome: 1 declaration-level sorry + a handful of
local `by sorry` at `hctx.eval_quotes'` call sites (already present at
lines 5243, 5355, 5439, 5560, 5589).

**Option 1.75 (typed NbE)**: instead of `fullyQuotable`, prove the
typed-NbE fundamental lemma: `typeCheck n e τ = .ok true → ∃ v, eval _
_ [] e = some v ∧ quote fuelω 0 v = some _`. This is the classical
NbE soundness-and-completeness theorem in Abel's "NbE: Dependent
Types and Impredicativity" (2013). Requires:

- Val-level reducibility candidates indexed by Val-level types (or
  Expr-level types via `eval`).
- A bridge from `typeCheck`'s algorithmic output to the reducibility
  relation.
- Probably 1000–2000 LOC of new infrastructure.

This would subsume both Task 1 AND Phase 2 — a proper "progress" theorem
for the NbE evaluator. It's a larger investment than Phase 2 but gives
a stronger result.

## 5. Recommendation

**Prefer Option 1 salvage route (A): treat `hnfq`-threading as
architecture, not scaffold.**

Rationale:

1. The current codebase already threads `hnfq` at all `eval_quotes'`
   call sites. Formalising this as the permanent route costs nothing
   beyond what's already done.
2. The `Val.fullyQuotable` predicate retains its role in
   `RList_depth_lift` and `quote_depth_shift`. Only the
   `fullyQuotable_has_quote` direction is abandoned.
3. Task 2 (`vapp_realises`) remains feasible with the 6 hypotheses
   as originally specified — the caller (`eval_realises`'s `.app`
   case) supplies `hqvf`/`hqva` by invoking `eval_quotes'` with its
   own threaded `hnfq`. This is slightly more plumbing but not new
   theorems.
4. Task 3 (`quoteClosure_realises`) is orthogonal (forward-reference
   issue).
5. Task 4 Category A becomes Category B-equivalent (non-trivial but
   mechanical): thread `hnfq` through `tyInfer_sound_open`'s 4 sub-
   sorries. Category B and C are unchanged.

**Concrete path forward:**

1. **Document** this finding in `DECISION-LOG.md` (2026-04-22 entry
   supplement) and update `sorry-closure-plan.md` Task 1 to note that
   the strengthened-conclusion approach is abandoned.
2. **Restate Task 1's acceptance criterion**: close the 4 sub-sorries
   at 2536, 2541, 2597, 2608 by *dropping* the output-quote-witness
   obligation from `eval_vapp_preserves_fullyQuotable`, and instead
   weakening the return to just `Val.fullyQuotable d v`. Remove the
   need for these sub-sorries by routing their callers through
   `eval_quotes'` + threaded `hnfq`.
3. **If `eval_vapp_preserves_fullyQuotable` itself cannot be
   salvaged without quote witnesses** (because vapp's `.iota`/`.fix`
   unfold branches need `∃ qf, quote fuelω d f = some qf` to extend
   the env under `envFullyQuotable`, per DECISION-LOG 2026-04-22's
   "vapp iota/fix UNFOLD" note):
   - Add an explicit `hnfq_on_f : ∃ qf, quote fuelω d f = some qf`
     hypothesis to the vapp side of the mutual. The caller (vapp's
     `.app` case in eval, or `eval_realises`'s `.app` case) threads
     this from its own `hnfq`.
4. **Re-examine Tasks 2, 3, 4** under the new architecture. Most
   should still be mechanical; Task 4 Category A becomes slightly
   more invasive.
5. **Do NOT attempt Phase 2 as a remedy.** Phase 2 is orthogonal
   and does not subsume this.

**If Option 1 salvage is judged too invasive**, the alternative is
Option 1.75 (typed NbE). That's a 2–4 week research project, not a
2–4 hour engineering task. Do NOT confuse it with Phase 2.

## 6. Appendix: formal statement of the impossibility

**Theorem (informal):** There exists no decidable predicate `P : Val →
Prop` satisfying:

1. `P v → ∃ q, quote fuelω 0 v = some q` (quote-termination implied).
2. `P` is preserved by `eval`: `eval fuel unf ρ e = some v ∧
   (∀ v' ∈ ρ, P v') ∧ e.closedAt ρ.length = true → P v`.
3. `P` does NOT reference `typeCheck` or any typing predicate.

**Proof sketch.** Suppose such a `P` exists. Then the function

```
halt? : Expr → Bool
halt? e_body :=
  let cl := ⟨e_body, []⟩
  let v  := .lam .type cl
  decide (P v)  -- decidable by assumption
```

decides whether `quoteClosure fuelω 0 cl` terminates (by Condition 1
and the reverse direction — if it terminates, P v holds by backward
reasoning from the quote witness). By the standard encoding of Turing
machines in untyped λ-calculus (fix any Church/Kleene/Böhm encoding),
termination of `quoteClosure fuelω 0 cl` for `cl = ⟨e_body, []⟩` is
equivalent to termination of the untyped-λ β-reduction of `e_body`
under a fresh neutral input, which is Turing-equivalent to the Halting
Problem. Contradiction.

**Caveat.** The "fresh neutral" is a *free* variable, so the halting
reduction is on an *open* term. However, the standard observation is
that any non-terminating closed term `M` gives a non-terminating open
term `λx. M x` (or just `M` applied to a neutral, since the neutral
is absorbed). The Ω-counterexample in §2.1 demonstrates this
concretely without needing an encoded TM.

**Consequence.** Any `P` satisfying (1) and (2) but not (3) must refer
to typing or semantic properties not expressible as a first-order
structural predicate on `Val`. This rules out all five Candidates
(3.1–3.5). Candidate 6 (typed fullyQuotable) escapes the theorem by
failing condition (3); it is the intended route but requires the
typed-NbE infrastructure not present in the current codebase.

## 7. References

- `docs/ideas/sorry-closure-plan.md` — Phase 1 plan (Task 1's original
  statement).
- `docs/ideas/soundness-strengthen.md` — Phase 2 plan (does NOT
  subsume Task 1).
- `docs/ideas/bottom.md` — Primitive Bot (orthogonal).
- `DECISION-LOG.md` 2026-04-22 — Task 1 blocked (this doc provides
  the deeper analysis).
- `lean/Och/SoundnessProof.lean:1198–1223` — `Val.fullyQuotable`
  definitions.
- `lean/Och/SoundnessProof.lean:2463–2608` — the target theorem.
- `lean/Och/SoundnessProof.lean:4801–4832` — `eval_quotable_open` /
  `OpenCtx.eval_quotes'` (the existing `hnfq` threading).
- `lean/Och/SoundnessProof.lean:4819–4826` — existing documentation
  of the `openNf_holds` counterexample (closely analogous to
  §2.1's construction).
- `lean/Och/NbE.lean:292–307` — `quoteClosure` definition (the
  looping call `eval fuel 1 (bv :: cl.env) cl.body`).
- Abel, "NbE: Dependent Types and Impredicativity" (2013) — the
  typed-NbE architecture needed for Option 1.75.
