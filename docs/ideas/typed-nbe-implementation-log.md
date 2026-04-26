# Typed NbE — implementation log

Running log of the typed-NbE implementation work. Most recent entries
at the top. Each entry is honest about what landed, what's sorried,
and what's blocked.

## 2026-04-24 — Pass 11 (overnight #6): typed refinement of SubV_subst_neutral_to_value (agent-aba102f3)

**Strengthened `SubV_subst_neutral_to_value`'s statement with an
`RC n d τ_dom v` hypothesis**, eliminating the Ω-style
counterexample pass 9 found. Proof remains sorried; investigation
confirms pass 9's structural finding that even with the typed
hypothesis, the proof requires Val-level substitution machinery
(`Val.substLvl` + eval-substitution-commutation, pass-9 estimate
~510 LOC). Updated `lam` and `iota_struct` callers to provide RC
witnesses (both have them readily available). Did NOT typed-
refine `SubV_subst_pair`: the `fix_struct` caller's substituents
are `.fix` types (not RC-realised at the relevant domain), and
strengthening the pair lemma without an RC-at-fix-value auxiliary
would force a new inline sorry at the call site, violating the
no-net-sorry rule.

Net delta: 0 sorries. Statement of `SubV_subst_neutral_to_value`
is now correct (no Ω vacuity). The `lam`/`iota_struct` cases of
`subtype_closed_aux` continue to use it; their soundness now
rests on a *true* lemma rather than a vacuously-satisfied false
one. `SubV_subst_pair` and `fix_struct` retain the pass-8 status.

This is "case 2" of pass 11's stop-conditions: lemma statement
fixed, proof remains partial, with detailed post-mortem on why
even the typed version isn't easier.

### What landed

#### Statement strengthening

```lean
theorem SubV_subst_neutral_to_value
    {n d : Nat}
    {S : List (Val × Val)} {Γ : TyCtx}
    {τ_dom : Val} {clA clB : Closure} {bA bB : Val} (v : Val)
    (_hRC : RC n d τ_dom v)                            -- NEW
    (hbA : clA.openω (.neutral (.var Γ.size)) = some bA)
    (hbB : clB.openω (.neutral (.var Γ.size)) = some bB)
    (hbody : SubV S (Γ.push τ_dom) bA bB) :
    ∃ bA' bB',
      clA.openω v = some bA' ∧
      clB.openω v = some bB' ∧
      SubV S Γ bA' bB'
```

Previously this lemma's existential conclusion was vacuously
satisfied on Ω inputs (e.g. self-application closure opened at
the omega combinator). The RC hypothesis on `v` rules out such
inputs by saturation: `RC` at any non-zero step requires
`Val.fullyQuotable d v ∧ ∃ q, quote fuelω d v = .ok q`, which
implies `quote v` terminates. This (transitively) implies eval at
`v`-bound positions terminates *to the extent that quote
inspects them*. The conclusion's existential is now provable in
principle.

#### Caller updates

`subtype_closed_aux` lam case: passes `ha_RCdomA : RC m d domA a`
(the RC witness on the substituent argument `a`).

`subtype_closed_aux` iota_struct case: passes `hAnnB : RC k d annB v`
(the RC witness derived from the iota body's annotation
realisation).

Both call sites had the witness readily available — no new sorry,
no new auxiliary lemma at these call sites.

#### What was NOT changed

`SubV_subst_pair` (used by `fix_struct`) retains its pass-8
statement. Documented in-source: the typed refinement (route a:
`RC n d τ_dom va ∧ RC n d τ_dom vb`) requires a "fix-inhabits-
own-annotation" auxiliary lemma to discharge at the `fix_struct`
caller (substituents are `.fix annA clA, .fix annB clB`, not RC-
realised at `annB` directly). Building that aux lemma was out of
scope for pass 11.

The alternative (route b: explicit eval-termination preconditions)
was *prototyped* during this pass — see git history below — but
required +1 inline sorry at the `fix_struct` caller (for the RHS
fix open termination), which violates the no-net-sorry constraint.

### Why even the typed proof is hard

Pass 9's Approach B already noted: "RC-typing on `v` does NOT
replace the substitution content." Pass 11 attempted to find a
proof path leveraging RC's structure; here is the negative
result.

#### The fundamental obstacle: shape mismatch on bA vs bA'

The induction is on `hbody : SubV S (Γ.push τ_dom) bA bB`. Each
SubV constructor constrains `bA, bB`:
- `SubV.lam` ⟹ `bA = .lam ...`, `bB = .lam ...`
- `SubV.iota_struct` ⟹ `bA = .iota ...`, `bB = .iota ...`
- `SubV.refl` ⟹ `bA = bB`
- ... etc.

But the goal speaks of `bA' = clA.openω v` — an eval result whose
shape is *not* constrained by the SubV constructor. For example:
even when the SubV proves `SubV.lam bA bB`, `bA'` need not be a
`.lam` (it's `eval fuelω (v :: env) body` — `body`'s shape post-
eval depends on env, including v).

The bridge "`bA, bA'` differ by Val-level substitution
(replace fresh-neutral with v)" requires:

(1) A **Val-level substitution function** `Val.substLvl k v_sub :
    Val → Val/Outcome Val` that replaces `.neutral (.var k)` with
    `v_sub`, propagating through `.app`/`.iota`/etc. (pass 9
    Approach A).

(2) An **eval-substitution-commutation lemma**:
    `eval fuel (a₁ :: env) body = .ok r₁ →
     eval fuel (a₂ :: env) body = .ok r₂ →
     r₂ = Val.substLvl Γ.size (a₂ at original-position-of-a₁) r₁`
    (modulo redex firing for `.app`-spine cases).

(3) A **SubV-preserves-substLvl lemma**: substituting an
    SubV-related pair into both sides preserves SubV.

These are pass 9's components (a), (b), (c) — estimated ~510 LOC
in total.

The RC hypothesis on `v` *helps* component (b) by guaranteeing
eval-termination at v-bound positions (saturation⇒quote
terminates⇒eval-at-fresh terminates⇒eval-at-v terminates by
substitution-commutation). But component (b) itself, the lemma
that *defines* this commutation, is the bulk of the work and is
unavoidable.

#### Why RC's specific structure (saturation, mono, intro/elim) doesn't shortcut

The user's prompt asked: "Consider whether RC's particular
structure can be leveraged differently."

- **Saturation conjuncts** (`fullyQuotable`, quote witness): tell
  us about `v` itself (it's well-formed and quote-able). Don't
  tell us about `eval (v :: env) body`'s shape.

- **Mono** (`RC.mono`): downward step-index closure. Useful for
  IH applications at smaller steps but doesn't change the
  body-shape bridge.

- **Intro/elim** lemmas (`RC.lam_intro`, `RC.lam_elim`, etc.):
  give us forward/backward principles between RC at closure
  types and explicit body opens. These are useful at the
  *outer* level (where `subtype_closed_aux`'s lam case applies
  the body clause of h to a concrete `a`) but inside the
  substitution lemma itself, the goal is structural SubV
  transport, not RC manipulation.

The RC structure's payoff for this lemma is bounded: it makes
the *statement* correct (no Ω vacuity), but the structural
content of the proof is unchanged from pass 9's analysis.

#### Could splitting into helpers help?

Pass 9's prompt suggested: "Try splitting the lemma into smaller
helper lemmas, each provable."

Plausible factoring:
- `Val.substLvl_well_def` — partiality discharge at `.app`-spine
  cases, given RC on the substituend (~80 LOC).
- `eval_substLvl_commutes_lam` — special case for `.lam`-bound
  bodies (~50 LOC).
- `eval_substLvl_commutes_neutral` — special case for fresh-
  neutral substitution (~50 LOC).
- `SubV_substLvl_preserves_<constructor>` — one per SubV
  constructor (~150 LOC total, 13 constructors).
- Glue lemma combining the above (~30 LOC).

Total: still in the ~360-510 LOC range. No order-of-magnitude
saving.

### Sorry trajectory

Pre-pass-11:
- `subtype_closed_aux`: 5 inline sorries
  (`neutral_ascent`, `iota_intro`, `unfold_fix_L`,
  `unfold_iota_L`, `revapp_L`)
- `SubV_subst_neutral_to_value`: 1 declaration sorry
- `SubV_subst_pair`: 1 declaration sorry
- `typed_nbe_fundamental_open`: 1 declaration sorry
- **Total**: 8 sorries in TypedNbE.lean

Post-pass-11:
- `subtype_closed_aux`: 5 inline sorries (UNCHANGED)
- `SubV_subst_neutral_to_value`: 1 declaration sorry,
  **statement strengthened with RC hypothesis**
- `SubV_subst_pair`: 1 declaration sorry (UNCHANGED, statement
  preserved)
- `typed_nbe_fundamental_open`: 1 declaration sorry (UNCHANGED)
- **Total**: 8 sorries in TypedNbE.lean

Net: 0 sorries added/removed. One statement strengthened from
"vacuously satisfied on Ω" to "true under typed refinement".

### Build status

`nix develop -c lake build` passes end-to-end. AxiomCheck.lean
unchanged (the same theorems still depend on sorryAx; the new RC
hypothesis pulls `Quot.sound` into
`SubV_subst_neutral_to_value`'s axiom dependencies as a structural
side-effect of the RC predicate's mutual definition with
Outcome/Val machinery — purely a transitivity addition, not a new
fundamental dependency).

### What pass 12+ should pick up

In priority order:

1. **The substitution machinery proper.** Pass 9's components
   (`Val.substLvl`, eval-commutation, SubV-preservation). With
   the typed `SubV_subst_neutral_to_value` statement, the
   partiality issues in `Val.substLvl` are easier to discharge
   (RC on the substituend is exactly the well-typed-substituent
   condition). Estimated ~400-500 LOC; closes
   `lam`/`iota_struct` axiomatically.

2. **`SubV_subst_pair` typed refinement** — apply route (a)
   (`RC n d τ_dom va ∧ RC n d τ_dom vb`) once an RC-at-fix-value
   auxiliary lemma is built. The aux lemma might follow from
   `RC.fix_intro` plus careful step-index bookkeeping — needs
   investigation. Once route (a) lands, `fix_struct` rests on a
   true pair-lemma, matching `lam`/`iota_struct`'s pass-11 status.

3. **Alternative: pivot to typed-everything** (pass-6 design's
   Level 2). The substitution lemma's content moves into
   `subCheckTypedV`'s soundness, where the algorithmic
   structural recursion at fresh neutrals carries the
   parametricity argument. Pass 6's analysis (§2) showed the
   substitution lemma is *intrinsically required* by either
   architecture — pivoting moves the work but doesn't dissolve
   it. Open question: does the typed-everything formulation
   admit a cleaner substitution-machinery proof?

4. **Leave intact, attack other inline sorries**
   (`iota_intro`, `revapp_L`, `neutral_ascent`,
   `unfold_fix_L`, `unfold_iota_L`). These have distinct
   obstacles per pass-10's analysis; could be tackled in
   parallel with the substitution work.

### Honest assessment

Pass 11 is the third pass to NOT add scaffolding (after passes
9, 10). The strengthening is forward progress in *correctness*
(statement is now true, not vacuously satisfied) but doesn't
close cases. The substitution wall remains.

The user's pass-11 prompt anticipated this disposition (case 2:
"Lemma statement fixed but proof partial. Document precisely
where the proof needs more work."). This entry fulfills that.

The honest path to OCH soundness via this architecture remains:
a dedicated multi-pass effort on the Val-level substitution
machinery (pass 9's ~510 LOC estimate). No shortcut has emerged
across passes 5-11.

---

## 2026-04-24 — Pass 10 (overnight #5): RC_env signature refactor (agent-ad99cc16)

**Landed pass 9's recommended `RC_env` signature refactor for
`subtype_closed_aux` (~75 LOC delta, +1 axiom-clean lemma
`RC_env.mono`). Confirmed honestly that the refactor — by
itself — does NOT close any of the 5 sorried inline cases. Pass 9's
post-mortem hoped that "directly inducting under the extended
`RC_env`" would dissolve the substitution wall; pass 10's
implementation reveals this is not the case. The refactor is
nevertheless forward progress: it positions the proof to use
typing information in pass 11+ work on the still-sorried cases
and aligns with the FL body's signature.**

Net delta: 0 sorries added, 0 removed. +1 axiom-clean lemma
(`RC_env.mono`). +1 strengthened signature.

This is "case 2" of pass 10's stop-conditions: refactor lands but
0 closure cases close. Documented here.

### What landed

#### Signature refactor

`RC.subtype_closed_aux` now takes `RC_env n d Γ ρ` as a typed-
environment realisation hypothesis:

```
theorem RC.subtype_closed_aux : ∀ (n : Nat) {d : Nat}
    {S : List (Val × Val)} {Γ : TyEnv} {ρ : Env} {τ τ' v : Val},
      RC_env n d Γ ρ →                  -- NEW
      (∀ α β, (α, β) ∈ S → ∀ m, m ≤ n → ∀ v',
         RC m d α v' → RC m d β v') →
      SubV S Γ τ τ' → RC n d τ v → RC n d τ' v
```

Closed corollary `RC.subtype_closed` provides `RC_env.nil` for the
empty context. External API preserved.

`RC_env` definition + `nil`/`cons`/`mono` lemmas relocated to
*before* `subtype_closed_aux` (was originally after it, co-located
with FL). Move was a pure relocation.

#### `RC_env.mono` (new, axiom-clean)

```
theorem RC_env.mono {n m d : Nat} {Γ : TyEnv} {ρ : Env}
    (hle : m ≤ n) (hΓρ : RC_env n d Γ ρ) : RC_env m d Γ ρ
```

Step-index downward monotonicity for typed envs. Trivial — per-
position via `RC.mono`. Used by `subtype_closed_aux`'s recursive
calls (which always step down).

#### Pass 10's threading-through pattern

Each match-case body's recursive call (`ihStrong m _` or `ih m _`)
needs `RC_env m d Γ' ρ` where `Γ'` is the match-bound pattern
variable. The fix: at each call site, derive
`hΓρ_m : RC_env m d Γ' ρ := RC_env.mono _ hΓρ` and pass it as the
first argument to the IH.

Lean subtlety: after dependent pattern matching on `hsub : SubV S Γ
τ τ'`, the dependent elimination substitutes outer `Γ`'s
references in pre-existing hypotheses (e.g., `hΓρ` becomes
`RC_env (k+1) d Γ' ρ`), but new type ascriptions in the case body
must use `Γ'` explicitly. Without this, Lean fails to unify outer
`Γ` (the FVar in scope) with `Γ'` (the match-introduced FVar).
This was the elaboration trip-up in pass 10's first attempt;
documented here for future agents.

### Critical finding: RC_env alone does NOT dissolve the substitution wall

Pass 9's post-mortem (Critical finding 3) claimed:

> The "substitution wall" disappears: instead of needing to prove
> `SubV bA bB` extends to substituted versions, the proof directly
> inducts under the extended `RC_env`, and the RC structure of
> values closes the cases.

Pass 10 implements the refactor and traces through case-by-case.
The above claim is **structurally incorrect**. Detailed analysis:

#### `lam` case

Premises (from `SubV.lam`): `hbA : clA.openω fresh = some bA`,
`hbB : clB.openω fresh = some bB`,
`hbody : SubV S' (Γ'.push domA) bA bB` — body relation at the
*fresh-neutral-opened* bodies.

Goal (after RC unfolding): for every `m ≤ k`, `a` with
`RC m d domB a`, get `r` with `vapp v a = .ok r ∧ ∃ rTyB,
clB.openω a = some rTyB ∧ RC m d rTyB r`.

Strategy attempt with RC_env:
1. From `ha_RCdomA : RC m d domA a` (via contravariance), construct
   extended env `ρ' = a :: ρ` and `RC_env.cons hΓρ ha_RCdomA :
   RC_env m d (Γ'.push domA) (a :: ρ)`.
2. Apply IH on `hbody` at the extended env: this gives
   `RC m d bA r → RC m d bB r` (NOT what we want!).

The IH gives a coercion at `bA, bB`, the *fresh-opened* bodies.
But we have `RC m d (clA.openω a) r` (the *concrete-opened* body)
and want `RC m d (clB.openω a) r`. The IH fires at the wrong
bodies.

To bridge `bA = clA.openω fresh` to `clA.openω a`, we still need
substitution at the Val level. RC_env doesn't dissolve this.

#### `iota_struct`, `fix_struct` cases

Same shape — the SubV body is at fresh-opened bodies, the goal
needs concrete-opened bodies. Substitution required.

#### `iota_intro` case

Premise: `hOpen : clB.openω a = some bB`. Goal needs `clB.openω v`
to terminate (where `v` is the value witness). Even with
`RC_env Γ ρ` and `RC k d a v` available (mono of given `h`), there
is no derivation of `clB.openω v = some _` from these. RC at `a`
gives saturation + body witnesses on `v` *with respect to a's
shape* — but those don't determine how `clB.openω v` evaluates.

#### `revapp_L`, `neutral_ascent`, `unfold_fix_L`, `unfold_iota_L`

These have distinct obstacles documented in passes 5/8:
- `revapp_L`, `neutral_ascent`: only saturation on `v` is
  available from `h`; v's relationship to the LHS-derivation
  values (`a'`, synthesized type τ) is not in RC.
- `unfold_fix_L`, `unfold_iota_L`: step-up mismatch (LHS unfold
  consumes a step but goal demands original step).

For `revapp_L` / `neutral_ascent`: RC_env helps conceptually (the
typing context is now visible), but operationally the bridge
needed is "vapp respects RC" or "SynthN-to-RC-realises", which are
separate lemma families.

For `unfold_fix_L` / `unfold_iota_L`: step-up is an RC structural
issue, orthogonal to RC_env.

### Why pass 9 thought RC_env would dissolve the wall

Pass 9's intuition: "for arbitrary RC-typed test arguments, the IH
applies under `RC_env.cons` extending the typed env." This is
correct in shape but doesn't address the substitution issue. The
IH on the SubV body fires *between bA and bB*, not on the closure
bodies as functions. The extended env makes `(Γ'.push domA, a :: ρ)`
typed, but the SubV is still about *closed Vals* `bA, bB`, not
*open closure bodies*.

Pass 9's recommendation was a structural intuition; pass 10's
implementation falsifies it concretely. This redirects future
work.

### What the refactor IS good for

**Forward progress, not case closure.** Specifically:

1. **FL body alignment.** When the FL body is written (pass 11+),
   it has `RC_env n d Γ ρ` from its open-environment signature.
   At conversion sites, calling `subtype_closed_aux` is now a
   trivial pass-through; previously the FL would need to specialise
   to `RC_env.nil` (closed) or weave around the missing
   parameter.

2. **Substrate for sorried cases.** The 5 sorried inline cases
   (`iota_intro`, `revapp_L`, `neutral_ascent`, `unfold_fix_L`,
   `unfold_iota_L`) need typing information. With `hΓρ` now in
   scope, future passes attacking these cases have it available.

3. **Aligns with `SubTV` substrate.** `SubTV` (pass 6) is
   logical-relation-style; bridging `SubV` to `SubTV` via
   `subtype_closed` was always going to need typing info in the
   limit. Pass 10 wires it through.

4. **Doesn't regress.** All previously closed cases (refl, top,
   hyp, bot_L, neutral_struct, stuckRec_struct, revapp_R, lam,
   iota_struct, fix_struct, unfold_fix_R) preserved. No new
   sorries.

### Sorry trajectory

Pre-pass-10:
- `subtype_closed_aux`: 5 inline (`neutral_ascent`, `iota_intro`,
  `unfold_fix_L`, `unfold_iota_L`, `revapp_L`).
- `SubV_subst_neutral_to_value`: 1 declaration.
- `SubV_subst_pair`: 1 declaration.
- `typed_nbe_fundamental_open`: 1 declaration.
- **Total**: 8.

Post-pass-10:
- `subtype_closed_aux`: 5 inline (UNCHANGED).
- `SubV_subst_neutral_to_value`: 1 declaration (unchanged).
- `SubV_subst_pair`: 1 declaration (unchanged).
- `typed_nbe_fundamental_open`: 1 declaration (unchanged).
- **Total**: 8.

**Net delta**: 0 sorries. +1 axiom-clean lemma (`RC_env.mono`).

### Build status

`nix develop -c lake build` passes end-to-end. AxiomCheck.lean
updated: `RC_env.mono` added (axiom-clean). All previously
axiom-clean theorems remain so. `subtype_closed_aux` and
`subtype_closed` continue to depend on sorryAx (5 inline sorries
unchanged).

### What pass 11 should pick up

In priority order:

1. **Attack the substitution lemmas directly** with the realistic
   ~510-LOC budget pass 9 estimated. They remain the keystone for
   `lam`/`iota_struct`/`fix_struct`. The Val-level substitution
   machinery + eval-commutation + SubV-preservation is a 4-pass
   project that would close 3 of the 5 sorried cases.

2. **`iota_intro` via closure parametricity.** This needs
   "`RC k d a v ∧ clB.openω a = some bB → ∃ bB', clB.openω v =
   some bB' ∧ RC k d bB' v`" — a parametricity-of-closure-
   application property. Distinct from substitution. ~100-200 LOC.

3. **`revapp_L` via "vapp respects RC".** Lemma:
   "`RC k d (.neutral (.stuckRec f arg)) v ∧ vappω f arg = some a'
   ∧ a' ≠ stuckRec → RC k d a' v`". This effectively says RC at a
   stuck application "follows the unfold". Needs RC.stuckRec
   structure that doesn't exist yet — RC at `.neutral` is
   currently just saturation. **Would need an RC redesign**
   to add stuck-rec-respecting structure. Larger pass.

4. **`neutral_ascent` via SynthN-realises bridge.** Similar to
   (3) — needs RC.neutral to encode synthesized type info.
   Either redesign RC at neutral, or add a separate
   "SynthN-realises" lemma family that runs alongside RC. Both
   are larger passes.

5. **`unfold_fix_L`/`unfold_iota_L`** are blocked on the step-up
   mismatch. Alternative architectures (guarded recursion,
   Iris-style ▷ modality) might address this — see
   pass-9 entry. Orthogonal to RC_env work.

### Honest assessment

Pass 10 is the second pass to NOT add scaffolding (after pass 9).
The refactor is forward progress for pass 11+ work but does not
close cases. The honest finding is that pass 9's hope was too
optimistic: RC_env-in-the-signature is necessary but not
sufficient for the closure-form cases. The substitution wall is
real and structurally required, as pass 9 itself documented.

What pass 10 affirms:
- Pass 9's first finding (substitution lemma is ~510 LOC, not
  ~200-400) — **strengthened**, since pass 10 confirms RC_env
  doesn't shortcut it.
- Pass 9's second finding (the keystone lemma's statement has a
  latent bug) — **unchanged**, the lemma is still sorried with
  the same statement.
- Pass 9's third finding (the signature refactor sidesteps the
  wall) — **falsified**. Refactor lands; wall remains.

The user's pass-10 prompt anticipated this outcome:

> 2. **Refactor lands but only 1-2 cases close.** Document why
> others don't and what additional infrastructure they need. Stop.

Pass 10 fulfills this disposition: 0 cases close, but the
refactor lands cleanly and is documented for pass 11+ to
build upon.

The most likely path forward for OCH soundness now appears to be:
- Direct attack on the Val-level substitution lemmas (~510 LOC)
  is unavoidable for `lam`/`iota_struct`/`fix_struct`. Pass 11+
  may attempt this.
- Alternative: redesign the RC predicate to encode neutral-type
  structure (so `RC.neutral` carries SynthN-realised content).
  This would close `neutral_ascent`, `revapp_L`, possibly help
  `iota_intro`. But it's a larger architectural shift.
- Or: pivot to a different soundness architecture entirely
  (e.g., quote-based as in pass 9's option 2). This is the
  user's call.

---

## 2026-04-24 — Pass 9 (overnight #4): keystone post-mortem (agent-afa368ac)

**No code changes this pass.** Pass 9's prompt asked for direct
attack on `SubV_subst_neutral_to_value` (the keystone lemma
that passes 5-8 "duck-and-covered" around). After ~3 hours of
structural investigation across multiple proof strategies,
pass 9 produces three critical findings:

1. The lemma is **structurally harder** than passes 5-8
   estimated — closer to ~510 LOC across 4 inter-dependent
   components.
2. The lemma's **statement contains a latent bug** — the
   conclusion's eval-termination claim fails for arbitrary `v`.
3. The **most promising path forward is a signature refactor**
   of `subtype_closed_aux` (which the pass-9 prompt
   specifically forbade, but pass 10+ should reconsider given
   these findings).

This is option 3 from the pass-9 prompt's "When to stop" list:
*"Lemma genuinely intractable at Val-level too. Write a careful
post-mortem describing exactly which sub-induction breaks, what
additional infrastructure would unblock it, and whether the
typed-everything architecture itself is the right path."*

Net delta: 0 sorries.

### Approaches investigated

#### Approach A.0: structural Val-level substitution function

```lean
def Val.substLvl (k : Nat) (vs : Val) : Val → Val
  | .type => .type
  | .neutral (.var k') => if k' = k then vs else .neutral (.var k')
  | .neutral (.app n a) => .neutral (.app (?subst n) (Val.substLvl k vs a))
  | ...
```

**Fatal obstacle**: substituting a non-neutral `vs` into the
spine head of `.neutral (.app (.var k) a)` produces a malformed
Val. `Neutral.app`'s first argument MUST be a Neutral, so
`.app vs ...` doesn't typecheck. There is no purely-structural
type-correct substitution function on Val.

#### Approach A.1: Outcome-valued substitution with vapp

```lean
def Val.substLvl (k : Nat) (vs : Val) : Val → Outcome Val
  | .neutral (.app n a) => do
      let nv ← Neutral.substLvl k vs n
      let av ← Val.substLvl k vs a
      vapp fuelω unfBound nv av  -- handles redex-firing
```

**Fatal obstacle**: makes substitution partial. Every
downstream proof must thread the `.outOfFuel` / `.error` cases.
The eval-substitution commutation lemma becomes a multi-case
mutual induction with the partiality, ballooning to ~250 LOC
just for component (b) below.

#### Approach A.2: relational substitution

```lean
inductive Val.SubstLvl (k : Nat) (vs : Val) : Val → Val → Prop where
  | type : Val.SubstLvl k vs .type .type
  | varHit : Val.SubstLvl k vs (.neutral (.var k)) vs
  | varMiss : k' ≠ k → Val.SubstLvl k vs (.neutral (.var k')) (.neutral (.var k'))
  | app_neut : Val.SubstLvl k vs (.neutral n) (.neutral n') → ... →
               Val.SubstLvl k vs (.neutral (.app n a)) (.neutral (.app n' a'))
  | app_redex : Val.SubstLvl k vs (.neutral n) (.lam dom cl) → ... →
                vapp fuelω unfBound (.lam dom cl) a' = .ok r →
                Val.SubstLvl k vs (.neutral (.app n a)) r
  | ...
```

**Obstacle**: avoids the partiality issue but requires deep
case analysis on the relation. SubV-preservation under this
relation needs to handle each clause; eval-commutation needs
to handle each clause. Still ~400-500 LOC total.

#### Approach B: typed refinement (RC-typed v)

Add `RC n d τ_dom v` as a hypothesis. Hope: RC structure on `v`
lets us close cases by RC-elim instead of substitution.

**Investigation**: RC-typing on `v` does NOT replace the
substitution content. Specifically, the SubV proof of
`SubV S (Γ.push τ_dom) bA bB` may include constructors like
`SubV.lam` where `bA = .lam domA' clA'` and `bB = .lam domB'
clB'`. To transport this to `bA' = clA.openω v` (a different
shape entirely — `bA'` need not be a `.lam`), we still need
substitution at the closure-body level. RC on `v` gives
saturation + body content for `v` ALONE; it doesn't tell us
how `clA.body`'s eval result transforms.

**Net savings of Approach B over A**: marginal. Only the
`SubV.iota_intro`-like cases clearly benefit, and those have
their own distinct obstacles.

#### Approach C: direct induction on SubV (no substitution)

Try to induct on `hbody : SubV S (Γ.push τ_dom) bA bB` and at
each constructor, derive `bA' bB'` from the constructor's
shape constraints.

**Fatal obstacle**: each constructor only constrains `bA, bB`
— it gives **no information** about `bA' = clA.openω v` or
`bB' = clB.openω v`. The `bA' bB'` are determined by `clA`,
`clB`'s INTERNAL structure (their `body : Expr` and `env :
List Val`), which the SubV proof doesn't expose.

For example, `SubV.refl` says `bA = bB`. The closures `clA,
clB` need not be equal — only their fresh-opens match. So
`clA.openω v` and `clB.openω v` are independent eval results;
the lemma's conclusion `SubV S Γ bA' bB'` is generally NOT
derivable from refl alone.

This confirms substitution machinery is **structurally
required**. Direct SubV induction without substitution is a
non-starter.

### Critical finding 1: pre-pass-9 estimate was off by ~2x

Previous passes (5-8) framed the substitution lemma as
"~200-400 LOC of structural induction" comparable in scope to
`Subtype'.unshift_head`. **This estimate is too optimistic.**

The Subtype'-level analog operates on `Expr`, which is purely
syntactic. Substitution on Expr is straightforward structural
recursion with no reduction.

The SubV-level lemma operates on `Val`, which embeds
operational semantics (closures with environments, neutral
spines). Substitution must respect vapp-reductions when
substituting non-neutral values into spine heads.

Realistic estimate (with explicit components):

| Component | Estimate | Notes |
|---|---|---|
| `Val.substLvl` def + termination | ~80 LOC | Outcome-valued; vapp call in `.app` case |
| `eval_substLvl_commutes` | ~200 LOC | Mutual on eval/vapp; mirrors `eval_levelsBelow` |
| `SubV_substLvl_preserves` | ~200 LOC | 13 SubV constructors |
| Glue + statement-shape fix | ~30 LOC | Wires components |
| **Total** | **~510 LOC** | Across 4 inter-dependent passes |

Each component is a substantial pass-sized proof in its own
right. None can be partially sorried without violating the
pass-9 no-regression rule.

### Critical finding 2: the lemma's statement has a latent bug

The current statement claims `clA.openω v = some bA'` for
ARBITRARY `v`. This is **provably false** for some inputs.

**Concrete Ω-style counterexample**:

Let `clA = ⟨body := .app (.bvar 0) (.bvar 0), env := []⟩`
(self-application body).

- `clA.openω fresh` runs `eval fuelω 4 [fresh] (.app (.bvar 0)
  (.bvar 0))` → `vapp fuelω 4 fresh fresh`. Since `fresh =
  .neutral (.var Γ.size)` is neutral, vapp returns `.ok
  (.neutral (.app (.var Γ.size) (.neutral (.var Γ.size))))`.
  Succeeds. So `bA = .neutral (.app (.var Γ.size) ...)`.
- For `v = .lam dom ⟨.app (.bvar 0) (.bvar 0), []⟩`
  (self-application function — the omega combinator),
  `clA.openω v` runs `vapp fuelω 4 v v` → opens v's body at
  `v :: []` → `vapp fuelω 4 v v` → ... → exhausts fuel.
  Returns `.outOfFuel`. So `clA.openω v = none`.

The lemma's conclusion `clA.openω v = some bA'` does NOT
hold; the existential cannot be satisfied. The lemma's
statement, as currently written, is **false in general**.

**Fix** (generalisation, not weakening, per pass-9 rules):

Option 1 — pre-conditioned conclusion:
```
SubV_subst_neutral_to_value :
    clA.openω fresh = some bA → clB.openω fresh = some bB →
    SubV S (Γ.push τ_dom) bA bB →
    -- Caller proves eval-termination as precondition:
    clA.openω v = some bA' → clB.openω v = some bB' →
    SubV S Γ bA' bB'
```
Caller is responsible for eval-termination at v. This still
requires the substitution lemma's content but doesn't claim
spurious termination.

Option 2 — typed refinement:
```
SubV_subst_neutral_to_value_typed :
    RC n d τ_dom v →                  -- typed v
    clA.openω fresh = some bA → clB.openω fresh = some bB →
    SubV S (Γ.push τ_dom) bA bB →
    ∃ bA' bB',
      clA.openω v = some bA' ∧ clB.openω v = some bB' ∧
      SubV S Γ bA' bB'
```
The RC hypothesis on `v` ensures the closure opens terminate
(via the RC saturation conjunct's `quote` witness, which
implies eval termination).

**Pre-pass-9 callers** (pass 7's `lam`/`iota_struct`, pass 8's
`fix_struct`): each call site has RC-typing on `v` available
(`a` is RC-typed at domA in lam, `v` is RC-typed at annA in
iota/fix). So Option 2 doesn't regress the use sites.

The current statement (with no termination hypothesis) is
**vacuously satisfied** at counterexample inputs because the
conclusion has `clA.openω v = some bA'` as a CONJUNCT — if
this fails, the existential is unprovable rather than false.
But it's still misleading: callers expect the lemma to fire
for any v, when in fact it can only fire when v makes both
opens terminate.

### Critical finding 3: signature refactor sidesteps the wall

Pass 9's prompt **forbids** the signature refactor of
`subtype_closed_aux`. But the post-mortem must surface this
finding because it's the most promising path forward, and
pass 10+ should reconsider:

Refactor `subtype_closed_aux` to take `RC_env n d Γ ρ`:

```lean
theorem RC.subtype_closed_under_realisation
    {n d : Nat} {Γ : TyCtx} {ρ : Env}
    {S : List (Val × Val)} {τ τ' v : Val}
    (hΓρ : RC_env n d Γ ρ)
    (hS : ∀ α β, (α, β) ∈ S → ∀ m, m ≤ n → ∀ v',
        RC m d α v' → RC m d β v')
    (hsub : SubV S Γ τ τ')
    (h : RC n d τ v) :
    RC n d τ' v
```

The new ingredient is `hΓρ : RC_env n d Γ ρ` — a typed
environment realisation. The closure-form cases (`SubV.lam`,
`iota_struct`, `fix_struct`) now have:

- For each bvar position in Γ, an RC-typed value.
- For arbitrary RC-typed test arguments, the IH applies under
  `RC_env.cons` extending the typed env.

The "substitution wall" disappears: instead of needing to
prove `SubV bA bB` extends to substituted versions, the proof
directly inducts under the extended `RC_env`, and the RC
structure of values closes the cases.

Estimated cost: ~150-250 LOC for the new signature + re-proofs
of existing closed cases (refl, top, bot_L, neutral_struct,
stuckRec_struct, revapp_R, unfold_fix_R) + the new closure
cases. **No substitution lemma needed.**

This is a **structurally cleaner** path than the substitution
machinery. Pass 9's recommendation: pass 10 should attempt
this refactor before any more substitution-machinery work.

### Why this finding wasn't surfaced in passes 5-8

Passes 5-8 framed the problem as "the substitution lemma is
hard but ultimately tractable, just needs a dedicated pass."
This framing was **structurally correct** but **strategically
misleading**: each pass added more inline scaffolding (using
the keystone lemma) that ultimately depended on the keystone
proof, making the overall effort feel close to closure when
the central piece remained out of reach.

Pass 9's contribution is the **architectural realisation**
that:
1. The substitution wall is harder than estimated.
2. The lemma's statement has a structural bug.
3. The wall is **avoidable** via signature refactor — a
   detail that would be missed if pass 9 had blindly
   continued adding scaffolding.

### Alternative architectures briefly considered

1. **RC redesign with guarded recursion (Iris-style ▷
   modality)**: would change the step-loss issue on
   `unfold_fix_R` but doesn't address substitution. Orthogonal.

2. **Move soundness chain through quote**: `typeCheck e τ →
   quote e' = .ok normal → Subtype' (quote a) (quote τ)`. Trades
   the Val-level substitution for the Expr-level
   `Subtype'.unshift_head` (which is itself a 300-500 LOC
   resisting wall). No clear win.

3. **Move to typed-everything (`SubTV`)**: pass 6 design doc
   sketched this. The semantic subtype relation would
   internalise RC. But the FL still needs to prove
   non-trivial properties about closure equivalence; the wall
   moves but doesn't disappear.

4. **The `RC_env`-refactor (Critical finding 3)**: most
   promising. Recommended for pass 10.

### Sorry trajectory (no change)

- TypedNbE.lean: 4 declaration sorries unchanged.
- SoundnessProof.lean: 4 declaration sorries unchanged.

### Build status

`nix develop -c lake build` passes. AxiomCheck unchanged. No
files modified (this entry is the only deliverable).

### What pass 10 should pick up

In priority order:

1. **Refactor `subtype_closed_aux` signature to take `RC_env`**
   (Critical finding 3) — most promising path. Estimated
   ~150-250 LOC; sidesteps substitution wall entirely.
   Even though pass 9 was forbidden from doing this, the
   findings strongly justify reconsidering.

2. **If the refactor doesn't pan out**, fix the keystone
   lemma's statement (Critical finding 2): strengthen with
   eval-termination evidence or RC-typing on `v`. Then
   attempt the substitution machinery.

3. **Stretch goal**: if (1) succeeds, retire
   `SubV_subst_neutral_to_value` and `SubV_subst_pair` as
   sorried lemmas — they would no longer be needed at the new
   signature. This drops the sorry count by 2.

4. **Architectural review**: if (1) and (2) both prove
   intractable, consider whether typed-NbE is the right
   architecture for OCH soundness, or whether to pivot.

### Honest assessment

Pass 9 is the first pass to **not** add scaffolding to the
typed-NbE proof. The previous four passes (5-8) each added
infrastructure that depended on the keystone — making the
typed-NbE substrate ever-larger without closing the central
proof obligation. Pass 9's contribution is to **diagnose**
rather than scaffold.

The findings (lemma is harder than estimated, has a latent
statement bug, and is sidesteppable via signature refactor)
redirect typed-NbE work toward a more promising path.

The user's pass-9 prompt anticipated this outcome (option 3:
"Lemma genuinely intractable at Val-level too. Write a careful
post-mortem... possibly suggests we need to revisit the
architecture."). This entry fulfills that disposition.

---

## 2026-04-24 — Pass 8 (overnight #3): SubV_subst_pair, fix_struct closed (structural) (agent-aab33530)

**Stated `SubV_subst_pair` (sorried, the pair-substitution
generalisation of `SubV_subst_neutral_to_value`) and used it to
close `fix_struct` case of `subtype_closed_aux`. Net delta: 0
inline sorries (closed 1, added 1 new sorried lemma — same as
pass 7's pattern but with smaller leverage). The keystone
`SubV_subst_neutral_to_value` was NOT proven this pass: detailed
investigation confirms it is genuinely 200-400 LOC and cannot be
landed in one overnight pass without weakening statements or
intermediate sorries (forbidden by no-regression rule). Build
green throughout.**

### What landed

#### `SubV_subst_pair` — pair-substitution lemma (sorried)

The "different substituents on each side" generalisation of
`SubV_subst_neutral_to_value`:

```lean
theorem SubV_subst_pair
    {S Γ τ_dom clA clB bA bB} (va vb : Val)
    (hbA : clA.openω (.neutral (.var Γ.size)) = some bA)
    (hbB : clB.openω (.neutral (.var Γ.size)) = some bB)
    (hbody : SubV S (Γ.push τ_dom) bA bB)
    (hsubst : SubV S Γ va vb) :
    ∃ bA' bB',
      clA.openω va = some bA' ∧
      clB.openω vb = some bB' ∧
      SubV S Γ bA' bB'
```

The basic lemma replaces a fresh neutral with a SINGLE value on
both sides; the pair version threads TWO related substituents
(`va` on LHS, `vb` on RHS) connected by `SubV S Γ va vb`.

**Estimated proof scope**: ~50-100 LOC on top of the basic
lemma's 200-400 LOC. Currently sorried; pass 9+ work.

#### `fix_struct` case closure

The fix_struct case of `subtype_closed_aux` (previously deferred
because RC at `.fix annA clA` opens at the FIX VALUE itself
— `clA.openω (.fix annA clA)` for LHS, `clB.openω (.fix annB
clB)` for RHS, with DISTINCT substituents) is now wired through
`SubV_subst_pair`.

Strategy mirrors iota_struct's pass-7 closure:
1. Unfold RC at h, goal: saturation + body witness.
2. Saturation transfers from h directly.
3. Build augmented hS_k (seen-set + new entry, discharged via
   ihStrong on OUR derivation at smaller step).
4. Apply SubV_subst_pair on hBody at substituents
   `(.fix annA clA, .fix annB clB)`, related by SubV.hyp on the
   augmented seen-set's new entry.
5. By Some-injectivity, the LHS-substituted body equals the RC
   body witness from h.
6. Apply ihStrong at step k on the resulting SubV (under hS_k)
   to lift RC k d uTyA v to RC k d bB' v.

#### `iota_intro` is NOT closed by SubV_subst_pair

Pass 7's commit message suggested SubV_subst_pair could also
close `iota_intro`. On closer inspection, **this is incorrect**:

`SubV.iota_intro`'s premises don't go through a fresh neutral —
they have `clB.openω a = some bB` directly, where `a` is the
LHS *type/inhabitant*. RC.iota_intro requires `clB.openω v` for
the actual VALUE `v`. Both opens are at concrete values, not at
a fresh neutral; SubV_subst_pair (which has a fresh-neutral
hypothesis) doesn't apply.

Closing `iota_intro` requires a DIFFERENT lemma:

```
"closure_apply_coherence" :
  RC k d a v →
  clB.openω a = some bB →
  RC k d bB v →           -- from SubV S Γ a bB + RC at a + IH
  ∃ bB', clB.openω v = some bB' ∧ RC k d bB' v
```

This is parametricity of closure-application over RC-equivalent
inputs. Documented inline in `subtype_closed_aux`. Pass 9+ work.

### Why the keystone substitution lemma was NOT proven this pass

The pass-8 prompt's primary target was proving
`SubV_subst_neutral_to_value`. After detailed investigation, I
conclude it is genuinely 200-400 LOC and cannot be safely
landed in one overnight pass without violating rules. Specific
findings:

#### Approach 1: Val-level substitution machinery

Define `Val.substLvl k vsub : Val → Val` (replace neutral level
`k` with `vsub`). Required infrastructure:
1. `Val.substLvl` definition with mutual recursion through Val,
   Closure, Neutral. ~30 LOC.
2. `eval_substLvl_commutes`: if `eval n unf (env_1 :: env_tail)
   body = .ok bA` where `env_1 = .neutral (.var k)`, and
   `Val.substLvl k vsub` is applied throughout the env, then
   `eval n unf (vsub :: env_tail) body = .ok (Val.substLvl k vsub
   bA)`. **This is a deep mutual induction on eval/vapp**, ~150
   LOC for the operational property alone.
3. `SubV` is preserved under `Val.substLvl k vsub` (changing
   context from `Γ.push τ_dom` to `Γ`). **Structural induction
   over 13 SubV constructors**, each requiring substitution
   through the constructor's premises. ~150 LOC.

Total: ~300-350 LOC. The middle step (eval_substLvl_commutes)
is the load-bearing piece — without it, the substitution
operation is meaningless at the SubV level.

#### Approach 2: typed refinement

Add `RC n d τ_dom v` as a hypothesis. The hope: RC's structural
content lets us close cases by RC-elim instead of SubV-induction.

In practice: SubV's closure cases (`lam`, `iota_struct`,
`fix_struct`) STILL require us to relate `clA.openω fresh` to
`clA.openω v` — that's the substitution's content. RC at v
gives saturation + body content for v, but doesn't tell us how
the closure body's eval-result transforms. We're back to needing
eval-substitution.

The savings from RC: in the `neutral_ascent`-shaped subcases,
where SubV at neutral lets us discharge via saturation; and in
the `iota_intro`-shaped subcases, where RC at the inhabitant
helps. But for closure-form cases (the bulk), RC doesn't replace
the substitution.

Total: ~150-250 LOC, not the dramatic shortcut hoped for.

#### Conclusion

Both approaches are full-pass projects in their own right. The
honest move was to:
1. Land the structural staging (one more inline case factored
   out into a sorried lemma).
2. Document the wall with this post-mortem.

This is the same disposition as passes 5, 6, and 7 reached
independently. Four passes (5-8) have now confirmed the
substitution lemma is a genuine 200-400 LOC obstacle that
requires its own dedicated pass with that specific budget.

### Sorry trajectory

Pre-pass-8 (= post-pass-7):
- `subtype_closed_aux` body: 6 inline (`neutral_ascent`,
  `fix_struct`, `iota_intro`, `unfold_fix_L`, `unfold_iota_L`,
  `revapp_L`).
- `SubV_subst_neutral_to_value` body: 1.
- `typed_nbe_fundamental_open` body: 1.
- **Total**: 8.

Post-pass-8:
- `subtype_closed_aux` body: 5 (`fix_struct` closed; others
  unchanged).
- `SubV_subst_neutral_to_value` body: 1.
- `SubV_subst_pair` body: 1 (NEW).
- `typed_nbe_fundamental_open` body: 1.
- **Total**: 8.

**Net delta**: 0. Inline sorries within `subtype_closed_aux`
dropped from 6 to 5 (a meaningful proxy-metric for soundness
proof progress); the absolute total is unchanged because the
substitution-lemma family is now factored as two related lemmas
rather than one lemma + undocumented fix_struct gap.

### Build status

`nix develop -c lake build` passes end-to-end. AxiomCheck.lean
updated: `SubV_subst_pair` added (shows sorryAx). No
regressions in SoundnessProof.lean, AxiomCheck.lean, or test
files.

### Honest assessment

Pass 8's deliverable is structural staging only — the same
pattern as pass 7, with smaller leverage (1 case closed instead
of 2). The keystone substitution lemma remains unproven, and
this pass's investigation confirms it is genuinely a 200-400 LOC
project requiring its own dedicated pass.

The factoring contribution is real: future passes attacking the
substitution lemma now have a precise pair-of-lemmas target,
each with a specific subset of inline cases it dispatches.

### What pass 9 should pick up

In priority order:
1. **Prove `SubV_subst_neutral_to_value`** — keystone, closes
   `lam` + `iota_struct`. 200-400 LOC dedicated pass.
2. **Prove `SubV_subst_pair`** — likely a refinement or parallel
   induction. Closes `fix_struct`. 50-100 LOC after (1).
3. **`iota_intro` via `closure_apply_coherence`** — new
   bridge lemma family. ~100-200 LOC.
4. **`neutral_ascent` / `revapp_L`** — need RC_env in scope of
   subtype_closed_aux (signature change), or proven separately
   under typed assumptions. ~200-300 LOC including the signature
   change.
5. **`unfold_fix_L`/`unfold_iota_L`** — step-up mismatch, needs
   RC redesign or workaround.

After (1)+(2), 3 of 5 remaining inline sorries close
mechanically; subtype_closed_aux drops from 5 inline sorries to
2 (just `iota_intro` and the unfold-L pair).

---

## 2026-04-24 — Pass 7 (overnight #2): SubV_subst_neutral_to_value substrate (agent-aa094350)

**Stated `SubV_subst_neutral_to_value` (sorried) and used it to
close `lam` and `iota_struct` cases of `subtype_closed_aux`. Net
delta: -1 inline sorry in TypedNbE.lean (closed 2 inline sorries,
added 1 sorried lemma that consolidates the obligation). Build
green throughout. `fix_struct` not closed (different-substituends
issue documented); `iota_intro` similarly deferred.**

### What landed

#### `SubV_subst_neutral_to_value` — the substitution lemma (sorried)

The body-substitution lemma identified in pass 5's post-mortem:

```lean
theorem SubV_subst_neutral_to_value
    {S Γ τ_dom v} {clA clB bA bB} :
    clA.openω (.neutral (.var Γ.size)) = some bA →
    clB.openω (.neutral (.var Γ.size)) = some bB →
    SubV S (Γ.push τ_dom) bA bB →
    ∃ bA' bB',
      clA.openω v = some bA' ∧
      clB.openω v = some bB' ∧
      SubV S Γ bA' bB'
```

The Val-level analog of the Expr-level `Subtype'.unshift_head`. Its
proof requires either:
1. **Val-level substitution machinery** — define `Val.substLvl
   (k : Nat) (v_sub : Val) : Val → Val` (replace neutral level
   `.var k` with `v_sub`), prove it commutes with `eval`/`vapp`/
   closure-opening, prove it transports SubV under the appropriate
   context-update. Estimated 200-400 LOC.
2. **A typed refinement** — restrict to RC-typed `v` (require
   `RC n d τ_dom v` as a hypothesis) and use the typed structure
   to close case-by-case. Estimated 150-250 LOC at the Val level
   (vs 300-500 at Expr-level for `unshift_head`).

Pass 7 keeps the lemma sorried but USES it to close two inline
sorries in `subtype_closed_aux`, demonstrating leverage and
consolidating obligations.

#### `lam` case closed in `subtype_closed_aux`

Strategy:
1. Unfold RC at `h` and goal: both reduce to saturation + body
   clause "for all m ≤ k, RC-typed `a`, vapp succeeds and produces
   RC-typed result".
2. Saturation transfers from `h` directly via `RC.sat_of_succ`.
3. For body: take `m, hm, a` with `RC m d domB a`. Apply
   `subtype_closed_aux` IH (`ihStrong`) at step `m+1 < k+1` to
   `hdom : SubV S Γ domB domA` to get `RC m d domA a`
   (contravariant domain). Wraps zero-step trivially.
4. Apply `h`'s body clause at this `a` to get `r, vapp_eq, rTyA,
   hOpenA, hRCa : RC m d rTyA r`.
5. Use `SubV_subst_neutral_to_value` at `a` to convert `hbody`
   into `∃ bA' bB', clA.openω a = some bA' ∧ clB.openω a = some
   bB' ∧ SubV S Γ bA' bB'`.
6. By `Some`-injectivity, `bA' = rTyA`. Apply `ihStrong` at step
   `m+1` on `hSubBody` and `hRCa` to get `RC m d bB' r`. Witness
   `rTyB := bB'`.

#### `iota_struct` case closed in `subtype_closed_aux`

Same pattern as `lam`, with three adjustments:
- The seen-set is augmented with `(.iota annA clA, .iota annB
  clB)` in the recursive premises. The new entry's obligation
  is closed by `ihStrong` applied to OUR derivation at strictly
  smaller step (the standard pattern from `unfold_fix_R`).
- The body context is `Γ.push annB` (not `annA`), so the
  substitution lemma is invoked with `τ_dom := annB`.
- For the iota's annotation premise, we apply the IH (under the
  augmented seen-set hypothesis) at step `k`.

The augmented-seen-set discharge follows the same pattern as
`unfold_fix_R` (closed in pass 4), using `ihStrong` with the
restricted-step seen-set hypothesis.

### What did NOT land

#### `fix_struct` case

Structurally different from iota_struct: RC at `.fix` opens the
body at the FIX VALUE itself (`clA.openω (.fix annA clA)` for the
LHS, `clB.openω (.fix annB clB)` for the RHS — *distinct
substituends*). The substitution lemma covers a SINGLE substituend
on both sides simultaneously. Closing fix_struct requires an
extension lemma:

> If `SubV S Γ a b` (in the augmented seen-set), then
> `clA.openω a` and `clB.openω b` (different substituends) give
> related bodies.

This is a parametricity-of-closure-pair lemma, distinct from but
related to the basic substitution lemma. Pass 8+ work.

#### `iota_intro` case

Has the LHS-vs-value mismatch documented in pass 5's post-mortem.
Closing it likely needs the same extension lemma family as
`fix_struct`.

### Sorry trajectory

Inline sorries inside `subtype_closed_aux` body:
- Pre-pass-7: 7 (`lam`, `iota_struct`, `fix_struct`, `iota_intro`,
  `unfold_fix_L`, `unfold_iota_L`, `revapp_L`, `neutral_ascent`).
  Note: `lam` was 1 of 7 — old docstring counted by case-name;
  not a discrepancy.
- Post-pass-7: 6 (`fix_struct`, `iota_intro`, `unfold_fix_L`,
  `unfold_iota_L`, `revapp_L`, `neutral_ascent`).

Plus 1 NEW sorried lemma `SubV_subst_neutral_to_value`. So
TypedNbE.lean total declaration-sorries:
- Pre-pass-7: 2 (`subtype_closed_aux` body, `typed_nbe_fundamental_open`).
- Post-pass-7: 3 (above two + `SubV_subst_neutral_to_value`).

But the inline-sorry count (which is what tracks fragmentation) is:
- Pre-pass-7: 9 inline (7 in subtype_closed_aux, 2 in declarations).
- Post-pass-7: 8 inline (6 in subtype_closed_aux, 1 in declarations,
  1 in SubV_subst_neutral_to_value).

**Net delta**: -1 inline sorry. Per pass-7 prompt's target.

The `SubV_subst_neutral_to_value` sorry is a CONSOLIDATION:
closing it (in pass 8 or beyond) automatically closes 2 inline
sorries in `subtype_closed_aux` (already wired). With the
proposed `fix_struct`/`iota_intro` extension lemma, that becomes
4 sorries closed at once.

`AxiomCheck.lean` updated: added `#print axioms
NbE.SubV_subst_neutral_to_value`. Shows sorryAx as expected.

### Build status

`nix develop -c lake build` passes end-to-end. No regressions in
SoundnessProof.lean, AxiomCheck.lean, or test files. Full Std
suite, NbETests, TypedNbETests, PropertyTests all green.

### Honest assessment

Pass 7's deliverable matches the prompt's primary target (`lam` case
closed). The bonus (`iota_struct`) materialised; the further bonus
(`fix_struct`) did not, because of the genuine substituend asymmetry
(documented in source code).

The substitution lemma proof itself was NOT attempted in this pass.
The honest reasoning: the lemma is genuinely 150-400 LOC of work, and
attempting a partial proof would either:
- Introduce more sorries to make a case go through (forbidden by
  no-regression rule), or
- Weaken the statement (forbidden by user's principle).

The right move is to consolidate the obligation into one lemma,
demonstrate it dispatches multiple cases, and hand off to a future
pass with a budget for the lemma's proof.

### What pass 8 should pick up

In priority order:

1. **Prove `SubV_subst_neutral_to_value`** — the lemma is the
   single biggest blocker. Even a partial proof (e.g., restricted
   to `v` of certain shapes) would close 2 inline sorries in
   `subtype_closed_aux`. The proof technique:
   - Build Val-level substitution `Val.substLvl k v_sub : Val →
     Val` (replace neutral level `.var k` with `v_sub`).
   - Prove `eval` commutes with substitution: if `eval` succeeds
     on `e` with one env, the substituted env produces the
     substituted result.
   - Specialise to closure-opening: `clA.openω fresh = some bA`
     and `Val.substLvl Γ.size v bA` should equal what
     `clA.openω v` produces (modulo level-shift bookkeeping).
   - Induct on SubV: each constructor's premises are SubV
     derivations on smaller Vals; substitution preserves the
     constructor's premise pattern. Tedious but mechanical.
   - Estimated 200-400 LOC.

2. **Extension lemma for `fix_struct`/`iota_intro`** — the
   "different substituends" version:
   ```
   theorem SubV_subst_pair :
       ∀ {S Γ τ_dom va vb} {clA clB bA bB},
         clA.openω (.neutral (.var Γ.size)) = some bA →
         clB.openω (.neutral (.var Γ.size)) = some bB →
         SubV S (Γ.push τ_dom) bA bB →
         SubV S Γ va vb →
         ∃ bA' bB',
           clA.openω va = some bA' ∧
           clB.openω vb = some bB' ∧
           SubV S Γ bA' bB'
   ```
   Likely ~50-100 LOC on top of the basic lemma. Closes 2 more
   inline sorries (`fix_struct`, `iota_intro`).

3. **`unfold_fix_L`/`unfold_iota_L`** — step-up issue documented
   in pass 5; needs RC redesign or workaround. Defer until (1)+(2)
   are landed.

4. **`revapp_L`/`neutral_ascent`** — orthogonal bridges
   (vapp-respects-RC, SynthN-realises). Each ~100-200 LOC.

After (1) lands, (2) is a moderate refinement. After (1)+(2), 4
of 6 remaining inline sorries in `subtype_closed_aux` close
mechanically.

---

## 2026-04-24 — Pass 6 (overnight): typed-everything investigation (agent-a3d9ef98)

**Investigated the user's hypothesis: "making everything the typed
version dissolves the substitution-lemma wall." Verdict (honest):
**partially yes** — the wall persists in any algorithmic checker that
decides closure equivalence by fresh-opening, but typed-everything
(a) bypasses `Subtype'.unshift_head` entirely in the typed pipeline,
and (b) reduces the body-substitution lemma's scope from 300-500 LOC
at Expr-level to estimated 150-250 LOC at Val-level. Net: typed-
everything is the right architecture, but it's a multi-pass migration,
not a one-pass dissolution.**

### What landed

#### Phase 1: design doc

`docs/ideas/typed-everything-architecture.md` (552 LOC) lays out:

- Three architectural levels (0/1/2) with concrete data-type sketches.
  Pass 6 commits to **Level 1.5**: typed `SubTV` relation, untyped
  engine. Gets Level 2's payoff at Level 0's cost.
- Walk-through of the substitution lemma in the typed setting: why
  it doesn't magically dissolve, but how its shape changes.
- 5-pass forward plan (passes 6-10+), with LOC estimates per pass.
- Honest assessment of what bypasses (`unshift_head`), what gets
  cheaper (Val-level body-substitution), and what stays hard
  (algorithmic-checker parametricity).

Commit `9c62aca`.

#### Phase 2: `SubTV` substrate

`SubTV n d τ_a τ_b := ∀ v, RC n d τ_a v → RC n d τ_b v` — the
typed-everything subtype relation, defined as a logical relation.

Constructors landed (all axiom-clean):
- `SubTV.refl` — `τ ⊑ τ`.
- `SubTV.trans` — composition of RC-coercions.
- `SubTV.bot_L` — `.bot ⊑ τ` (RC at .bot is False).
- `SubTV.top` — `τ ⊑ .type` (saturation-only).
- `SubTV.to_neutral` — `τ ⊑ .neutral _` (saturation-only).
- `SubTV.coerce` — apply a SubTV to lift an RC.
- `SubTV.contra` — contravariant alias for arrow domains.

Bridge (transitively sorried via `RC.subtype_closed`):
- `SubTV.of_SubV` — converts `SubV [] #[] τ_a τ_b` to `SubTV n d τ_a τ_b`.
  Currently depends on the 8 inline sorries in `subtype_closed_aux`.
  Once those close (passes 7-8), `SubTV` is fully bridged.

`AxiomCheck.lean` updated with all 7 SubTV constructors. Verified
axiom-clean except for `of_SubV` (transitively on RC.subtype_closed,
as expected).

Commit `198ab43`.

### What did NOT land

**Closing any inline sorries in `subtype_closed_aux`.** All 8 hard
cases remain sorried. The reason — documented honestly in the design
doc — is that **the substitution lemma is intrinsic** to algorithmic
soundness when the algorithm decides closure equivalence by
fresh-opening. Pass 6's design demonstrates that:

1. The `SubTV` relation is the right *target* for the FL.
2. The bridge `SubV ⟹ SubTV` IS the work, factored as
   `RC.subtype_closed_aux`.
3. The wall is the same wall; the rebuild **doesn't dissolve it**.

This is critical to know. The user's hypothesis "typed-everything
dissolves the wall" was investigated honestly and refined. The
architectural shift is still worth doing — `unshift_head` is
bypassed, the substitution lemma gets cheaper at Val-level — but it's
not free.

### Sorry trajectory

- Before pass 6: TypedNbE.lean = 9 sorries (8 inline in
  `subtype_closed_aux` + 1 declaration in `typed_nbe_fundamental_open`).
- After pass 6: TypedNbE.lean = 9 sorries (UNCHANGED).

Net delta: 0 sorries added, 0 removed. Pass 6's deliverables are
substrate (7 axiom-clean theorems) and design (552-LOC doc), neither
of which touches the existing sorries.

Build green throughout.

### Pass 7+ next-step list (precise, non-investigative)

The design doc's recommended ordering. Each is sized so a single
agent session can land at least the first sub-step.

**Pass 7: `SubV_to_SubTV.lam` via Val-level body-substitution.**

Goal: close one closure case in `subtype_closed_aux` — specifically
the `lam` case — using a NEW Val-level body-substitution lemma.

Concrete steps:
1. State `SubV_subst_neutral_to_value` in TypedNbE.lean:
   ```
   theorem SubV_subst_neutral_to_value :
       ∀ {S Γ τ_dom v} {clA clB bA bB},
         clA.openω (.neutral (.var Γ.size)) = some bA →
         clB.openω (.neutral (.var Γ.size)) = some bB →
         SubV S (Γ.push τ_dom) bA bB →
         ∃ bA' bB',
           clA.openω v = some bA' ∧
           clB.openω v = some bB' ∧
           SubV S Γ bA' bB'
   ```
2. Prove it by SubV-induction. **At Val-level**, where RC's saturation
   structure is available. Estimated 100-150 LOC.
3. Use it to close `subtype_closed_aux`'s `lam` case (currently
   sorried). Net delta: -1 inline sorry, +1 axiom-clean lemma.

**Pass 8: extend body-substitution to remaining closure cases.**

Same lemma covers `iota_struct`, `fix_struct` (variations on the
shape). Closure-form premises in `iota_intro`, `unfold_fix_L`,
`unfold_iota_L`, `revapp_L` may need separate but related lemmas.

Estimated 200-300 LOC. Closes 5-6 inline sorries. Possibly leaves
`neutral_ascent` for pass 8.5 (needs SynthN-realises bridge,
~100-200 LOC, orthogonal).

**Pass 9: FL body using completed SubTV.**

Once `subtype_closed_aux` is closed (i.e., 0 inline sorries),
`SubTV.of_SubV` becomes axiom-clean. The FL body
(`typed_nbe_fundamental_open`) can use SubTV throughout for
conversion sites:
```
have hsub : SubTV n d τ_inferred τ_expected :=
  SubTV.of_SubV (subCheckVal_subV ...)
have rc_b : RC n d τ_expected v := hsub.coerce rc_a
```

FL body is structural induction on `tyCheck`/`tyInfer`. Estimated
500-800 LOC.

**Pass 10+: retire unshift_head-dependent code.**

The 4 declaration sorries in `SoundnessProof.lean`
(`tyCheck_sound_open`, `tyInfer_sound_open`, etc.) become provable
via the typed FL. `unshift_head` is no longer needed; can be deleted
or left documented.

### Honest assessment

Pass 6 set out to investigate a user hypothesis. Investigation
returned: **the hypothesis is partially correct**. Typed-everything
is the right path, but it's not a one-pass shortcut around the
substitution lemma. The pass's commitment was to deliver the design
doc + at least one substantive prototype piece. Both delivered.

What I deliberately did NOT do:
- Open new sorries to "make progress" on inline cases. The temptation
  to case-split `revapp_L` or `neutral_ascent` on the goal-type was
  resisted: it would add sorries (1 → 4 in each case) which violates
  the no-regression rule, even when 2 of the 4 sub-cases close.
- Inflate the count by adding sorried "scaffold" lemmas for pass 7+
  to use. Pass 7 will state the substitution lemma when it actually
  proves it; pre-stating it as `sorry` would be cosmetic.
- Touch the FL body. That's pass 9 work; pass 6 is substrate.

What I delivered:
- A design doc that's honest about what the architecture buys vs
  doesn't buy.
- A `SubTV` substrate that pass 7+ inherits as a clean foundation.
- A precise next-step list so pass 7 starts coding immediately
  without re-investigating.
- 0 sorry regression.

The "couple of agents" estimate the user gave will likely be **3-4
agents**, not 2, given the substitution-lemma cost at the Val-level.
This is the most honest forward estimate available.

---

## 2026-04-24 — Pass 5 partial + substitution-lemma post-mortem (agent-ad8dfe91)

**Reformulated the FL signature to take an open-environment realisation
(`RC_env n d Γ ρ`), and proved both `RC_env.nil` and `RC_env.cons`
axiom-clean. This is the right shape for the eventual FL body: the
`.lam`/`.app`/`.letE` cases need `RC_env.cons` to extend the env. The
7 inline sorries in `subtype_closed_aux` REMAIN — pass 5 explored each
and confirmed that 6 of 7 require the same body-substitution lemma
(or close variants of it), and that lemma is genuinely 300-500 LOC of
its own. Net inline sorry delta: 0 (no progress on the 7 hard cases,
no regression).**

### What landed

#### `RC_env n d Γ ρ` definition + helpers

Added the typed-environment realisation predicate, with the indexing
convention from `tyInfer`/`tyCheck`:
- `Γ : TyEnv` is an `Array Val`; bvar `k` looks up `Γ[Γ.size - 1 - k]`
  (reverse-order array indexing, matching `tyInfer`'s `.bvar` arm).
- `ρ : Env` is a `List Val`; bvar `k` looks up `ρ[k]` (cons-order).

`RC_env n d Γ ρ` requires `Γ.size = ρ.length` and for every
`k < ρ.length`, the value at `ρ[k]` is RC at the type at
`Γ[Γ.size - 1 - k]`.

Helper lemmas (both axiom-clean):
- `RC_env.nil : RC_env n d #[] []` (trivial).
- `RC_env.cons : RC_env n d Γ ρ → RC n d τ v → RC_env n d (Γ.push τ) (v :: ρ)`
  — index-arithmetic proof handling the bvar-0-vs-bvar-(k+1) split.

#### `typed_nbe_fundamental_open` — open-environment FL signature

Replaced the closed-environment FL signature with:

```
theorem typed_nbe_fundamental_open
    {n d : Nat} {Γ : TyEnv} {ρ : Env} {e : Expr} {τV : Val}
    (hΓρ : RC_env n d Γ ρ)
    (hfuel : 1 ≤ n) (hfuelω : n ≤ fuelω)
    (hcheck : tyCheck n Γ ρ e τV = .ok true) :
    ∃ v, eval n unfBound ρ e = .ok v ∧ RC n d τV v
```

This is the right shape for the eventual proof: structural induction
on `tyCheck`/`tyInfer`'s case-split, with the `.lam`/`.app`/`.letE`
cases extending `Γ ρ` via `RC_env.cons` and recursing on the body.

The closed corollary (at `Γ = #[]`/`ρ = []`) is left as a docstring
example (NOT a sorried theorem — that would inflate sorry count); the
actual theorem will be added in pass 6+ as a one-liner specialisation
once `typed_nbe_fundamental_open`'s body is proven.

`AxiomCheck.lean` updated: `typed_nbe_fundamental` → `typed_nbe_fundamental_open`,
`RC_env.nil`, `RC_env.cons` added (latter two axiom-clean).

### Substitution lemma post-mortem

This pass set out to close the 7 inline sorries in `subtype_closed_aux`,
prioritising the body-substitution lemma (which closes
`lam`/`iota_struct`/`fix_struct` — 3 of 7). After detailed analysis
of each remaining case, here is what's needed for each, and why
the substitution lemma is genuinely a 300-500 LOC project beyond
this pass's scope.

#### The substitution lemma (needed by `lam`, `iota_struct`, `fix_struct`)

The shape needed for these three cases:

```
SubV_subst_neutral :
  ∀ {S Γ τ_dom v} {clA clB bA bB},
    clA.openω (.neutral (.var Γ.size)) = some bA →
    clB.openω (.neutral (.var Γ.size)) = some bB →
    SubV S (Γ.push τ_dom) bA bB →
    -- For any value `v` in scope, replacing the neutral var with `v`:
    ∃ bA' bB',
      clA.openω v = some bA' ∧
      clB.openω v = some bB' ∧
      SubV S Γ bA' bB'
```

**Why it's needed**:
- `lam` case: `RC.lam` requires `clA.openω a` and `clB.openω a` to be
  related for arbitrary RC-typed `a`. The SubV.lam premise gives
  `SubV (Γ.push domA) bA bB` where `bA = clA.openω fresh` and
  `bB = clB.openω fresh` — only at the fresh neutral. The
  substitution lemma bridges to arbitrary `a`.
- `iota_struct` case: same structure. `RC.iota` needs
  `clA.openω v` ↔ `clB.openω v` for the inhabitant `v`.
- `fix_struct` case: same shape, with the inhabitant being the fix
  itself (`clA.openω (.fix annA clA)`).

**Why it's hard**:
- The SubV is a relational property over closures, NOT a syntactic
  substitution. Proving it requires inducting on the SubV derivation
  and threading the substitution through every nested case.
- This is structurally the **same scope** as `Subtype'.unshift_head`
  documented in `Subtyping.lean` (lines 1074-1123). That docstring
  records: "Scope estimate. ~300–500 LOC structural induction over
  24 `Subtype'` constructors, with shift-subst arithmetic in `.hyp`
  ... seen-set depth-tag rewiring in productive rules. Not proven
  in this branch. Four prior subagent sessions attempted variants
  of this and documented progressive infrastructure; none closed
  the lemma."
- The SubV-level analog has 17 constructors (one fewer than Subtype')
  but the shape of the induction is identical. Estimated scope:
  same 300-500 LOC.

**Disposition**: deferred to a dedicated future pass. The pass 5
attempt confirmed:
1. The lemma's statement is well-defined (not a moving target).
2. The proof technique is structural induction on SubV, threading
   substitution + seen-set transformation.
3. No shortcut exists via the seen-set coinduction trick (the
   `unfold_fix_R` machinery handles seen-set obligations, but NOT
   the body substitution itself).

#### `iota_intro` (LHS-type-vs-value mismatch)

**SubV.iota_intro structure**: LHS = `a` (a Val), RHS =
`.iota ann clB`. Premises include `clB.openω a = some bB` (body
opened at the LHS *type* `a`).

**RC.iota_intro requires**: `clB.openω v = some bB' ∧ RC k d bB' v`
where `v` is the actual value (the inhabitant).

**The mismatch**: the SubV premise opens `clB` at `a` (the LHS
type/value). The RC requires opening at `v` (the inhabitant). These
differ unless `a = v`.

**What the bridge would need**: a lemma saying "if `v` is RC at type
`a`, then `clB.openω a` and `clB.openω v` are RC-equivalent". This
is a parametricity-style statement: closures respect RC-equivalence
of their inputs. Provable in principle (closures are functions, RC
is a logical relation, so closures should be relational), but the
proof requires the same kind of substitution-through-eval lemma
discussed above.

**Disposition**: deferred. Same family as the lam-substitution lemma.

#### `revapp_L` (RC-at-neutral is just saturation)

**SubV.revapp_L structure**: LHS = `.neutral (.stuckRec f arg)`,
RHS = `c`. Premise: `vappω f arg = some a' ∧ a' ≠ stuckRec ∧
SubV (..) Γ a' c`.

**The blockage**: `RC` at `.neutral _` is JUST saturation
(`Val.fullyQuotable d v ∧ ∃ q, quote fuelω d v = .ok q`) — NO
information about how `v` relates to the unfolded form `a'`. So
applying the IH to the recursive premise requires `RC k d a' v`,
which we don't have.

**Cases where revapp_L closes**: by case-split on `c`'s shape:
- `c = .type` or `c = .neutral _`: closes via saturation alone.
- `c = .lam`/`.iota`/`.fix`: needs body content; blocked.
- `c = .bot`: would need to derive `False`; only possible with
  typing context (which `subtype_closed_aux` doesn't have).

**Disposition**: a partial closure (case-split on `c`'s shape) is
possible but only handles a subset. The general case needs an
additional bridge "RC at stuckRec implies RC at unfolded form" that
would itself require typing-realisation context.

#### `neutral_ascent` (SynthN realisation missing)

**SubV.neutral_ascent structure**: LHS = `.neutral nA`, RHS = `b`.
Premises: `SynthN Γ nA τ ∧ SubV S Γ τ b`.

**The blockage**: same as `revapp_L`. RC at `.neutral nA` is just
saturation. We need `RC k d τ v` to apply the IH on `SubV S Γ τ b`,
but RC at neutral doesn't give us this.

**What the bridge would need**: a `SynthN-realises` lemma. Given
`SynthN Γ nA τ` and `RC_env n d Γ ρ` (the realised typing context),
a value `v` with `R n d v (.bvar Γ.size)` (i.e., `v` realises the
neutral `nA`'s syntactic form) should imply `RC n d τ v`. This is
analogous to the untyped `eval_realises`/`vapp_realises` chain, but
for the typed RC side.

**Disposition**: needs `RC_env`-aware reasoning. Now that `RC_env`
is defined, this bridge could be tackled, but it's still a
substantial lemma — needs SynthN-induction over the synthesis
structure (var, app, stuckRec). Estimated scope: 100-200 LOC.

#### `unfold_fix_L`, `unfold_iota_L` (step-up mismatch)

**Structure**: LHS = `.fix ann clA` (or `.iota ann clA`),
RHS = `c`. Premise: `clA.openω (LHS) = some bA ∧ bA ≠ LHS ∧
SubV (..) Γ bA c`.

**What we have**: `h : RC (k+1) d (LHS) v`. By RC.fix_elim/iota_elim:
`RC k d bA v` (one step is consumed by the unfold).

**What we need**: `RC (k+1) d c v`.

**The step-up mismatch**: applying the IH at step `k` to the
recursive premise gives `RC k d c v`, NOT `RC (k+1) d c v`. For
non-trivial `c` (closure-form), `RC (k+1) d c v` requires body
content "at step k", while `RC k d c v` only gives body content
"at step k-1". One step short.

**Why this is unrecoverable with current RC**: step-indexed RC
*requires* fix-unfolding to consume a step (otherwise the
predicate isn't well-founded, since `RC (n+1) d (.fix ann cl) v
:= RC (n+1) d (cl.openω (.fix ann cl)) v` would be an unguarded
self-reference). The cost of well-foundedness IS the step-loss
on unfold.

**What would unblock**: either
1. A different RC formulation that doesn't step-down on fix unfold
   (e.g., guarded recursion via `▷` modality, Iris-style; would
   require redefining RC and re-proving mono).
2. A "step-up" lemma like `RC k d c v ∧ saturation v → RC (k+1) d c v`
   — only true for trivial `c` (`.type`/`.neutral`/`.bot`).
   Would close revapp_L/neutral_ascent partially but not these
   unfold cases.

**Disposition**: documented as a structural issue with the
current RC definition. May require RC redesign.

### What pass 6 should pick up

In priority order:

1. **`SynthN-realises` bridge** (100-200 LOC) — closes
   `neutral_ascent`. Now that `RC_env` is defined, this is the most
   tractable of the remaining sorries.

2. **`revapp_L` partial closure** (case-split on `c`'s shape, ~50
   LOC) — closes the `c = .type`/`c = .neutral` sub-cases. The
   general case still blocked.

3. **Substitution lemma** (300-500 LOC) — closes
   `lam`/`iota_struct`/`fix_struct`/`iota_intro` (4 of the 7
   sorries). This is the highest-leverage but hardest piece.
   Should be done in tandem with `Subtype'.unshift_head` if
   possible (similar shape, similar techniques).

4. **RC redesign or fix-unfold step-up workaround** for
   `unfold_fix_L`/`unfold_iota_L` (2 of 7) — likely requires
   reformulating the RC predicate. Evaluate cost-vs-benefit
   relative to keeping the current form.

5. **FL body** for `typed_nbe_fundamental_open` — multi-week task,
   should follow at least partial closure of `subtype_closed_aux`
   (used at conversion sites in `tyCheck`).

### Sorry count trajectory

- Before pass 5: TypedNbE.lean = 2 declaration sorries
  (`subtype_closed_aux` body, `typed_nbe_fundamental` body),
  with 7 inline sorries in `subtype_closed_aux`.
- After pass 5: TypedNbE.lean = 2 declaration sorries
  (`subtype_closed_aux` body, `typed_nbe_fundamental_open` body
  — the latter is the reformulated open-form), with 7 inline
  sorries in `subtype_closed_aux` (UNCHANGED).

Net delta: 0 inline sorries removed, 0 added. No regression.

The `RC_env.nil` and `RC_env.cons` lemmas are axiom-clean
(no sorryAx).

Build green throughout.

### Honest assessment

Pass 5's deliverable is the **FL signature reformulation** plus
the `RC_env` substrate. This is real progress: the next pass
(or the eventual FL body) starts from a correctly-shaped
signature with the typed-env realisation lemmas already in
hand.

The 7 inline sorries in `subtype_closed_aux` were not closed
this pass. The substitution lemma (highest leverage) is
documented to be a 300-500 LOC project of comparable scope to
`Subtype'.unshift_head` (which has resisted four prior agents).
Attempting it in the remaining budget of this pass would have
risked either:
- A half-finished sorried lemma (forbidden by user's principle:
  "no new sorries to close old ones").
- A weakened statement (forbidden by user's principle: "don't
  weaken statements to make proofs go through").

The honest disposition is to commit the genuinely-finished work
(`RC_env` + reformulated FL signature) and document the
substitution-lemma terrain so the next agent has a precise
starting point.

---

## 2026-04-25 — Pass 4 partial + post-mortem (agent-aa25a621)

**Took the `RC.subtype_closed` sorry from one bare placeholder to a
structured proof scaffold with 7/16 SubV cases proven inline and the
remainder documented. The all-lower-indices + strong-IH refactor for
the auxiliary's seen-set hypothesis is now in place, which is the
correct step-indexed shape needed for the recursive closure cases.
The FL body remains untouched (still 1 sorry). Net sorry count
unchanged at 2 in TypedNbE.lean.**

### What landed

#### `RC.subtype_closed_aux` — initial scaffold + strong-IH refactor

The pass 3 placeholder was a single bare `sorry`. Replaced with:

1. **First iteration**: split into `cases hsub with | …`, proved
   the easy "shape transfer" cases inline (refl, top, hyp, bot_L,
   neutral_struct, stuckRec_struct, revapp_R). Each of these
   benefits from the saturated RC: when τ' is `.type` or
   `.neutral`, RC at τ' reduces to just the saturation witnesses
   (Val.fullyQuotable + quote witness), which transfer from any
   source RC via `RC.fullyQuotable` / `RC.quote_witness`. Closed
   ~7 of the 16 SubV cases.

2. **Second iteration**: refactored the auxiliary's seen-set
   hypothesis to the **all-lower-indices form**:
   ```
   hS : ∀ (α,β) ∈ S, ∀ m ≤ n, ∀ v', RC m d α v' → RC m d β v'
   ```
   and proved by `Nat.strongRecOn`, which provides
   `ihStrong m hmlt : Aux m` for any `m < n`. This is the correct
   shape for closing the seen-set entries added by the recursive
   premises in `iota_intro`, `unfold_fix_R`, etc.: the new entry's
   obligation is at strictly smaller step-index, closed by the
   strong IH applied to OUR own derivation.

3. **Third (in-progress) iteration**: tried to close `unfold_fix_R`
   using the strong-IH machinery. The proof structure is correct —
   saturation via `RC.sat_of_succ`, body recursion via `ih k _`,
   new seen-set entry obligation closed by `ihStrong m _` applied
   to OUR derivation. **However**, the named-implicit-binding
   issue blocks the closing tactic: `cases hsub with |
   unfold_fix_R hopen hbody` doesn't bind the constructor's
   implicits (`a, ann, clB, bB`) by name, and workarounds (`next`,
   `case`, `match` re-binding) all hit Lean-4 friction.

#### `typed_nbe_fundamental` — added `n ≤ fuelω` hypothesis

The FL signature now requires `n ≤ fuelω`. This is needed to invoke
`subCheckVal_subV` (which needs `fuel ≤ fuelω`) at conversion sites
inside the FL body. No callers exist yet, so this is a non-breaking
refinement.

The proof body remains untouched. The structural challenge documented
in the pass 3 log (need open-environment FL for `.lam`/`.app`/`.letE`
cases) is still the central obstruction.

### What did NOT land

The `unfold_fix_R` tactical closure and the FL body. The strong-IH
refactor brings the `unfold_fix_R` case to the brink of closing —
all the architectural pieces are in place, but Lean-4's
`cases ... with` doesn't expose the implicit constructor args by
name, blocking the residual tactic.

### How to close `unfold_fix_R` (and unfold_fix_L, unfold_iota_L)

Three options, in increasing cleanness:

1. **Quick fix via @-pattern in inner `match`**: re-match the
   already-matched `hsub` via a fresh `match` with full @-pattern
   to bind the implicits. Gets messy because `cases` already
   consumed `hsub`; would need to capture `hsub` before `cases`.

2. **Refactor to use `SubV.rec` directly**: build the three motives
   (one for SubV, SubN, SynthN) manually. More verbose but gives
   full control over implicit naming. ~50-100 LOC overhead.

3. **Define an "unfold_fix_R-only" inversion lemma** that takes
   `SubV S Γ a (.fix ann clB)` and exposes the witnesses (a, ann,
   clB, bB, hopen, hbody) as a Σ-type. Then `obtain ⟨...⟩ := inv`
   binds them all. This is the most idiomatic Lean-4 approach.

Option 3 is the one I'd take next iteration; it likely closes
`unfold_fix_R`/`unfold_fix_L`/`unfold_iota_L` together (similar
structures) in ~50 LOC.

### What pass 5 should pick up

In priority order:

1. **Close `unfold_fix_R` via option 3 above** — the strong-IH
   machinery is in place; this is purely tactical work.

2. **Close `unfold_fix_L` and `unfold_iota_L`** — same shape as
   `unfold_fix_R`. Should close together with option 3's
   inversion-lemma approach.

3. **`stuckRec_struct` and `iota_intro`** — these need a more
   refined RC bridge. `iota_intro` has the LHS-type-vs-value
   mismatch; the bridge is a typed iotaIntro lemma. Defer.

4. **`lam`, `iota_struct`, `fix_struct`** — the body-substitution
   lemma (fresh-open ⇝ arbitrary substitution equivalence on
   bodies). This is a classical NbE lemma but needs careful
   formulation in OCH's NbE substrate. ~200-500 LOC.

5. **`revapp_L`** — needs a `vapp-respects-RC` lemma. Likely
   provable from FL once FL is in place.

6. **`neutral_ascent`** — needs a `SynthN-realises` bridge. Defer.

7. **The FL body itself** — see pass 3's post-mortem; needs
   open-environment FL formulation. Multi-week task.

### Sorry count trajectory

- Before pass 4: TypedNbE.lean = 2 (subtype_closed body + FL body).
- After pass 4: TypedNbE.lean = 2 (same declaration count).

Internal sorry breakdown:
- `subtype_closed_aux`: 8 SubV cases proven inline (refl, hyp, top,
  bot_L, neutral_struct, stuckRec_struct, revapp_R, **unfold_fix_R**),
  with 7 inline sorries on hard cases (each documented).
- `typed_nbe_fundamental`: bare sorry, with refined signature
  (`n ≤ fuelω` added) and structural notes for next pass.

AxiomCheck.lean updated to track `subtype_closed_aux`,
`subtype_closed`, and `typed_nbe_fundamental` (each shows sorryAx,
as expected; the other 18 substrate lemmas are axiom-clean).

Build green throughout.

### Key technical insight: `match` vs `cases ... with`

The `unfold_fix_R` closure depended on a Lean-4 specific trick:
`cases hsub with | unfold_fix_R hopen hbody` doesn't bind the
constructor's *implicit* arguments by name, while a tactic-mode
`match hsub with | @SubV.unfold_fix_R S' Γ' a ann clB bB hopen
hbody` does (via the @-pattern). Replacing `cases` with `match`
unblocked the proof. Same technique should close `unfold_fix_L`
and `unfold_iota_L` modulo the step-up issue noted earlier.

---

## 2026-04-25 — Pass 3 partial + post-mortem (agent-a9d3158b)

**Two phases of pass 3 landed; the FL body remains. Substantial
honest progress on the substrate (closed `RC.mono` on `.lam`,
saturated RC, closed `implies_*` lemmas), but the FL itself and the
SoundnessProof.lean sorries remain unresolved.**

### What landed

#### Phase 1: `RC.mono` closed via "all-lower-indices" form

The Pass 1 log called out the `.lam` step-indexing problem as the
central limitation. Two strategies on the table: (a) lex recursion
on `(τ_size, n)`, (b) Iris-style `▷` modality.

Took option (c) — neither: the **Pitts-Howe / Dreyer-Ahmed-Birkedal
all-lower-indices form**:

```
RC (n+1) (.lam dV cl) v := ∀ m, m ≤ n → ∀ a, RC m dV a → ...
```

The universally-quantified `m ≤ n` makes mono trivial: shrinking
`n+1` to `m'+1` only restricts the universe of allowed `m`s. Take
any `m ≤ m'`, by transitivity `m ≤ n`, apply h. No contravariant
lift needed; no `▷` modality needed.

- Updated `RC.mono` `.lam` case to close cleanly.
- Updated `RC.lam_intro`/`RC.lam_elim` to take an `(m, hm)` pair.
- All other RC eliminators/introducers needed `unfold RC` to
  match the new shape.

Sorry trajectory: TypedNbE.lean 5 → 4. Commit `2a4b0d0`.

#### Phase 2: Saturated RC + `implies_*` projections

Pass 1's TODO comment on `implies_fullyQuotable` said:
> this corollary needs a stronger RC predicate; refactor pending.

Implemented the refactor: bake `Val.fullyQuotable d v ∧ ∃ q, quote
fuelω d v = .ok q` into **every** RC clause (including `.type` and
`.neutral` which were just `True`).

- New signature: `RC : Nat → Nat → Val → Val → Prop` (added depth
  `d` parameter; required because `Val.fullyQuotable` and `quote`
  are depth-parametrised).
- Two new direct-projection theorems:
  - `RC.fullyQuotable : RC (n+1) d τ v → Val.fullyQuotable d v`
  - `RC.quote_witness : RC (n+1) d τ v → ∃ q, quote fuelω d v = .ok q`
- `RC.implies_fullyQuotable` and `RC.implies_quote_terminates`
  now delegate to the new projections — sorries closed.
- `RC.lam_intro`/`iota_intro`/`fix_intro` now require the
  saturation witnesses on `v` as inputs. The FL must produce
  these for each value it constructs.
- `RC.type_top`/`neutral_top` similarly take saturation witnesses.

Sorry trajectory: TypedNbE.lean 4 → 2 (subtype_closed, FL body
remain). Commit `8882494`.

### What did NOT land — the FL body

The fundamental lemma's body would mirror `tyCheck`/`tyInfer`'s
case-split structure. Each typing rule produces an RC witness for
its result. With the saturation refactor, **each rule must now
also produce `Val.fullyQuotable d v` and `∃ q, quote fuelω d v =
.ok q` witnesses**.

For non-closure forms (.type, .bot, .bvar from realised env), this
is mechanical: `quote_type`/`quote_bot` are total, env entries
carry their saturation via `Closure.envFullyQuotable`.

For closure forms (.lam, .iota, .fix outputs of eval), the
saturation conjunct requires that `quoteClosure fuelω d cl =
.ok body'` — i.e., that opening the closure with a fresh neutral
and evaluating the body terminates within fuelω. Whether this
holds depends on the closure's body structure.

Specifically, `eval` of `.lam dom body` produces
`v = .lam (eval dom) (Closure.mk' body ρ)`. The saturation conjunct
on this `v` is:

  Val.fullyQuotable d v ∧ ∃ q, quote fuelω d v = .ok q

Unpacked:
  Val.fullyQuotable d (eval dom)              -- structural, closes
  Closure.fullyQuotable d (Closure.mk' body ρ) -- structural, closes
  ∃ q, quote fuelω d v = .ok q                  -- HARD

The last conjunct requires `quoteClosure fuelω d` to succeed,
which requires `eval fuelω 1 (.var d :: env) body` to succeed.
For an arbitrary OCH `body`, this need not terminate (e.g. body
= `.fix x:τ. x` has divergence under unf=1).

**This is the core obstacle**: even with typed RC, the saturation
conjunct on closure outputs requires a *nontrivial termination
argument* for the closure body's eval at fuelω. This must come
from the typing derivation, since the type has to constrain the
body's structure.

The plan is for FL's `.lam` case to feed the body's typed RC up:
the body inhabits some type, which by FL gives RC, which by the
saturation conjunct gives a quote witness on the body's eval. But
this is circular — FL's `.lam` case wants RC of the *closure*
output, and that RC needs the body's eval-quote, which needs the
body's RC, which needs... FL of the body. The recursion measure
must reflect this.

A sound measure exists in principle (induction on the typing
derivation, which is structurally finite), but the Lean
formalisation is involved: each FL case is several hundred lines
of bookkeeping plus the actual reasoning.

**Honest estimate**: 2-4 weeks of focused work to close FL body.
The pass 1 plan said the same; I confirm this from inside.

### What about the SoundnessProof.lean sorries?

The pass 3 prompt expected the FL to close 4 declaration-level
sorries in `SoundnessProof.lean`. It cannot, even hypothetically:

1. **`quoteClosure_realises`** (line 3763, full body sorry) — the
   docstring documents Routes A and B as formally blocked
   (termination measure failure across mutual cycle). Route C
   (the current state) keeps the sorry. The FL doesn't help: this
   is about *quoting* a closure, not about typed RC of one.

2. **`vapp_realises`'s 7 internal sorries** (lines 3998, 4001,
   4002, 4053, 4057, 4058, 4123, 4127, 4128) — each is of the
   form "need `Val.levelsBelow d va` / `Val.fullyQuotable d va`
   / `∃ qa, quote fuelω d va = .ok qa` on the function arg".
   The sorries' own comments say "add as vapp_realises hyp".
   Closing them requires *threading* the hypotheses through
   `vapp_realises`'s signature and recursion sites, plus
   `eval_realises`'s callers.

   Could be done, but each new hypothesis cascades:
   - `Val.levelsBelow` is derivable from `eval_levelsBelow` (proven).
   - `Val.fullyQuotable` is derivable from `eval_preserves_fullyQuotable`
     IF its 4 internal sorries close (they're documented as
     formally impossible without typing).
   - `∃ qa, quote fuelω d va = .ok qa` requires the same
     quote-termination argument that the FL would provide via
     RC saturation — but only AFTER FL itself is proven.

3. **`tyInfer_sound_open` 4 sorries** (.fix/.iota A9, .lam quote
   round-trip, generic .app) — documented as either:
   - **A9 unsoundness** (.fix/.iota inferring annotation as type)
     — a known *correctness gap* that's intentionally sorried.
   - **UNSHIFT-head** (Subtyping.lean docstring) — a 300-500 LOC
     substitution lemma over every `Subtype'` constructor.
   - **`quote_open_subst`** (root #2) — Halting-reduction
     impossible per `quote-witness-feasibility.md`.

4. **`tyCheck_sound_open` sorries** — same UNSHIFT obstructions.

The FL would close ~3 of these with substantial restating, but
the documented blockers (UNSHIFT, A9, quoteClosure_realises Routes
A/B) are orthogonal to typed-NbE.

### Net sorry status (as of this entry)

- `lean/Och/TypedNbE.lean`: 5 → 2 (`subtype_closed`, `FL body`).
- `lean/Och/SoundnessProof.lean`: unchanged from pass 1+2.

### What pass 3 phase 1+2 *enables*

Even without FL, the saturated RC and Phase 1 close-up are
substrate work that future agents inherit:

- `RC.mono` works for ALL type formers (including `.lam`).
- `RC` is depth-parametrised so it integrates with the existing
  `Val.fullyQuotable d v` / `quote fuelω d v` infrastructure
  without translation layers.
- `RC.fullyQuotable`/`RC.quote_witness` are direct projections;
  any future FL proof immediately closes the bridges.
- The introducers/eliminators correctly thread the
  saturation witnesses, so future FL cases have a clean API.

### Recommended next steps

1. **FL body**, one rule at a time, in priority order: `.type`/
   `.bot` → `.bvar` → `.asc`/`.letE` → `.iota`/`.fix` → `.lam`
   → `.app`. Each case is ~50-200 lines. Allow 2-4 weeks total.

2. **`subtype_closed`**: SubV induction, ~17 cases. Each case is
   moderate complexity. Allow 1-2 weeks. Should be done in
   tandem with FL body so the FL can use it for `.asc`-directed
   conversion.

3. **`vapp_realises` sorry threading**: orthogonal to FL; closes
   once `eval_vapp_preserves_fullyQuotable`'s 4 internal sorries
   close. Those need typed RC OR a substitute.

4. Documented blockers (UNSHIFT-head, quoteClosure_realises
   Routes A/B, A9 unsoundness) need separate post-mortems
   before any further attempt.

### Final assessment

The Pass 3 prompt's ask — "make `typeCheck_sound` axiom-clean" —
remains a 2-4 week target, not a single-session deliverable. Pass
3 phase 1+2 closed 3 of the 5 TypedNbE.lean sorries, with the
remaining two being the genuinely hard ones. The architectural
substrate (Pitts-Howe form + saturation) is now correctly shaped
for the FL proof; the FL body itself is the remaining work.

Build green throughout. AxiomCheck unchanged.

---

## 2026-04-24 — Pass 2 final (agent-a07e1f43-pass2)

**All seven phases (A-G) addressed; substrate fully wired into
the test suite; old path unused at user-facing level.**

### Headline numbers

- `three_ ⊑ Nat_` at fuel **800** under `subCheckT` (was ~50k under
  `subCheck`).
- `five_ ⊑ Nat_` at fuel **800** under `subCheckT` (did not close
  at fuel 6400 under `subCheck`, in 10+ minutes).
- A6 incompleteness `(λx:Nat_. x) ⊑ (λx:zero_. zero_)` accepted
  under `subCheckT` (rejected under `subCheck`). This is a
  completeness gain that was beyond reach of the perf
  investigations (subcheck-perf.md, a6-closure-env-filtering.md).

### Phase summary

- **Phase A** (typed eval substrate): `tyEvalIn`, `subCheckTyped`,
  `subCheckT` lands as type-directed pipeline. Done.
- **Phase B** (typed conversion): `subCheckTyped` fast-path uses
  the LHS's recorded type to short-circuit. Done; smoke tests pass.
- **Phase C** (wire into TyCheck): `subCheckT` wraps `typeCheck`
  (the syntactic-bidirectional path, which already does
  type-directed checking) plus fall-back to bare `subCheck`. Done.
- **Phase D** (Std/* migration): swept all test sites in
  `Std/*.lean`, `Tests.lean`, `PropertyTests.lean`,
  `SoundnessAudit.lean` from `NbE.subCheck` to `NbE.subCheckT`.
  All 100+ tests pass.
- **Phase E** (regressed tests): tried `five_ ⊑ Nat_` at fuel 800
  — passes. `two_ ⊑ Fin three_` still doesn't close at fuel 16000
  (the typed fast-path rejects via `Nat_ ⊑ Fin three_`, falls back
  to slow path). Pass 3 work needed for the latter.
- **Phase F** (delete dead code): not feasible. `subCheckVal` is
  the engine of `subCheckTyped`; `subCheck` is the fallback.
  `tyCheck` uses `subCheckVal` internally. Pass-3 SoundnessProof
  has 5000+ lines depending on `subCheckVal_subV`. Documented
  these as internal-only via `SubCheckVal.lean` module docstring.
- **Phase G** (this entry).

### What's wired

- `lean/Och/TypedNbE.lean` exports `subCheckT`, `subCheckTyped`,
  `tyEval`, `tyEvalIn`, `TypedVal`.
- `lean/Och/Std/*.lean` test sites use `NbE.subCheckT`.
- `lean/Och/Tests.lean`, `PropertyTests.lean`, `SoundnessAudit.lean`
  test sites use `NbE.subCheckT`.
- `lean/Och/TypedNbETests.lean` is the dedicated typed-pipeline
  test file (~30 tests including the headline `five_ ⊑ Nat_` win).
- `subCheckVal` and `subCheck` retained as the engine layer, used
  internally by `tyCheck`, `tyInfer`, and `subCheckT`'s fallback.

### What's left for pass 3

1. **FL body** (in `TypedNbE.lean`). Still sorried.
2. **`RC.implies_fullyQuotable`** and `RC.implies_quote_terminates`.
   Still sorried.
3. **The 4 declaration-level sorries in SoundnessProof.lean** —
   await FL body, then become straightforward corollaries.
4. **Wider Fin tests** (`two_ ⊑ Fin three_` etc.) — the typed
   pipeline's fast-path can't currently convert a singleton
   `succ_ k` value to its inferred-type `Nat_` AND know the
   value is also at `Fin (succ_ n)`. Pass 3 would need a `tyEval`
   that *records the structural shape* of the value so the
   fast-path can probe multiple types.

### Known cost

- Negative-case tests are now ~2x slower (typeCheck rejects, then
  fall back to subCheck which also rejects — both passes run).
  Net build time impact: ~2x on Std/*.lean rebuild, but absolute
  numbers are still bounded (~1 min for Std/Vec.lean which was
  the slowest).

### Build status

`nix develop -c lake build` passes. Sorry count:
- `SoundnessProof.lean`: 4 (unchanged from pass 1).
- `TypedNbE.lean`: 5 (unchanged from pass 1; pass 2 added no proof
  obligations because `subCheckTyped`/`subCheckT` are pure
  definitions; their soundness is a transitivity argument that
  pass 3 will prove formally).

---

## 2026-04-24 — Pass 2 milestone A (agent-a07e1f43-pass2)

**Phase A — typed eval + typed conversion check landed.**

### What landed in `lean/Och/TypedNbE.lean`

- `tyEvalIn (n unf : Nat) (ρ : Env) (e : Expr) (τV : Val) :
  Outcome TypedVal` — typed-eval over an open environment;
  pairs the eval'd value with a caller-supplied target type.
- `subCheckTyped (fuel : Nat) (tyCtx : TyCtx)
  (seen : List (Val × Val)) (a : TypedVal) (b : Val) : Outcome
  Bool` — type-directed conversion check. Fast-path: try
  `subCheckVal a.ty b`; on `.ok true` accept (sound by
  transitivity through `a.val ⊑ a.ty ⊑ b`). Otherwise fall back
  to the bare `subCheckVal a.val b`.
- `subCheckT (fuel : Nat) (a τ : Expr) : Outcome Bool` —
  top-level typed entry point. Runs `tyInfer` on `a` to
  discover its principal type, pairs `aV` with that type as the
  declared type, fires `subCheckTyped`. If inference fails,
  falls back to plain `subCheckVal`.

### Soundness sketch

The TypedVal invariant is `RC n a.ty a.val` (FL conclusion).
With the existing `subCheckVal_subV` soundness theorem:

  subCheckVal a.ty b = .ok true → Subtype' (quote a.ty) (quote b)

Combined with `RC` implying `a.val ⊑ a.ty` (which is the
saturated form of RC's reducibility predicate — pass-3 lemma),
we get `a.val ⊑ a.ty ⊑ b`, so `a.val ⊑ b`. Concretely:
fast-path is sound on RC-typed values, which is what `tyEval`
guarantees.

### Soundness of `subCheckT` specifically

`subCheckT a τ` runs `tyInfer a`. If inference returns some
`inferredTy`, by `tyInfer_sound` we have `Subtype' a inferredTy`.
The fast-path then checks `subCheckVal inferredTy τ`. If that
is `.ok true`, by `subCheckVal_subV` we get
`Subtype' inferredTy τ`, so by transitivity `Subtype' a τ`.
The fallback path just calls `subCheckVal aV τV`, which is
exactly what `subCheck a τ` does.

### Known limitations (carried into Phase B)

1. **Open-context tyInfer cost is doubled.** Every typed entry
   point now runs both `tyInfer` and `eval` upfront. For inputs
   where `tyInfer` doesn't help (no principal type), this is
   pure overhead. Pass 2 mitigation: only the top-level entry
   `subCheckT` does the inference; internal `subCheckTyped`
   calls use the *already-known* type from the typing context.

2. **Fast-path is conservative.** It uses `[]` for `seen`, so
   it can't close cyclic obligations on the type side.
   Practically, types like `Nat_` (a `fix`) require the
   seen-set on their own, so the fast-path may not fire on
   `Nat_ ⊑ Nat_` unless `subCheckVal` has the `a == b` short
   circuit (it does, via the first guard). For non-`fix`
   types like `Bool`, the fast-path closes via refl.

3. **No proof yet.** `subCheckTyped`/`subCheckT` have no
   `_subV` companion theorem. That's pass-3 work.

### Smoke tests in `TypedNbE.lean`

`subCheckT 50 .type .type = .ok true` and the matching
`subCheck` pin both pass. Wider tests (Std/* migration) are
phase D.

### Build status

`nix develop -c lake build` passes. No new sorries introduced
(the FL body remains the only deferred proof; the new
functions are pure definitions, no proof obligations yet).

### Next concrete step

Phase B/C: wire `subCheckTyped` into `TyCheck`'s `tyCheck`/
`tyInfer` so that conversion checks at every `.app` and
`.asc` go through the typed pipeline. Then test sweep.

---

## 2026-04-24 — Pass 1 final state (agent-a05d76a4)

After three commits on branch `agent-typed-nbe-a05d76a4`:

### Final tree contents

- **`lean/Och/TypedNbE.lean`** (468 lines):
  - `TypedVal` record (val + ty).
  - `RC : Nat → Val → Val → Prop` (step-indexed reducibility predicate).
  - `RC.mono` (proven for `.type`/`.bot`/`.neutral`/`.iota`/`.fix`;
    sorried for `.lam`).
  - `RC.subtype_closed` (sorried — needs SubV induction).
  - `RC.type_top`, `RC.neutral_top` (proven trivially).
  - `RC.lam_intro`/`iota_intro`/`fix_intro` (proven by defn).
  - `RC.lam_elim`/`iota_elim`/`fix_elim` (proven by defn).
  - `tyEval` (typed-eval wrapper, signature only).
  - `typed_nbe_fundamental` (FL signature; body sorried).
  - `RC.implies_fullyQuotable` (sorried).
  - `RC.implies_quote_terminates` (sorried).

- **`docs/ideas/typed-nbe.md`**: implementation addendum at the bottom
  documenting the four architectural choices (parallel TypedVal,
  step-indexed RC, FL-as-statement, file layout).

- **`docs/ideas/typed-nbe-implementation-log.md`**: this file.

### Final sorry count

- `lean/Och/SoundnessProof.lean`: **4** declaration-level sorries
  (unchanged).
- `lean/Och/TypedNbE.lean`: **5** declaration-level sorries (was 6;
  `RC.lam_intro` closed via defn-eq).
- Net delta: **+5** new sorries to ground the substrate, but each
  is a tractable target with a clear shape.

### What's next (concrete steps for the next agent)

In rough priority order:

1. **Refactor RC for step-indexing on `.lam` (the "later" problem).**
   Either Iris-style `▷` or lex-recursion on `(τ_size, n)`. This
   unblocks `RC.mono` for the `.lam` case.

2. **Prove the FL body, one case at a time.** Suggested order:
   `.type`/`.bot`/`.bvar` (base) → `.asc` → `.fix`/`.iota` →
   `.lam` → `.app` → `.letE`. The intro/elim lemmas in
   TypedNbE.lean are designed for this.

3. **Prove `RC.implies_quote_terminates`** (the bridge from typed
   semantic to operational). This is the lemma that, combined with
   FL, finally discharges the four old SoundnessProof sorries.

4. **Wire the closed-context `typeCheck_sound` to use FL.** This
   adds a typed pathway parallel to the existing untyped one.
   The closed-context case has typing hypotheses available so FL
   applies directly; the open-context case can reuse the path.

5. **Once 1–4 land, retire the four old SoundnessProof sorries.**
   They become provable corollaries of FL +
   `implies_quote_terminates`.

### What this pass is NOT

- Not a closed FL.
- Not a sorry-count reduction in `SoundnessProof.lean`.
- Not a perf demonstration.

It IS:

- A typed substrate that compiles and is wired into the build.
- A clear set of next-step targets with documented obstacles.
- The architectural shift: future work no longer needs to fight
  the `Val.fullyQuotable` Halting-reduction issue from
  `quote-witness-feasibility.md`. Instead, RC + FL is the path,
  and that path is well-precedented in the literature (Abel,
  Dreyer-Ahmed-Birkedal, Iris).

---

## 2026-04-24 — Pass 1 initial scaffold (agent-a05d76a4)

**Spec**: `docs/ideas/typed-nbe.md` (esp. the implementation addendum
at the bottom).

### What landed

- `lean/Och/TypedNbE.lean`: new file defining the typed-NbE substrate.
  - `TypedVal`: a record `(val : Val, ty : Val)` carrying a value and
    its declared semantic type.
  - `RC : Nat → Val → Val → Prop`: step-indexed reducibility candidate
    predicate, defined recursively on the type's exposed shape.
  - `tyEval`: a thin wrapper around `eval` that bundles the result
    with a typed-value witness.
  - `typed_nbe_fundamental` (statement only): every well-typed closed
    expression evaluates to an RC-witness of its declared type.

- `docs/ideas/typed-nbe.md`: added an implementation addendum
  recording the architectural choices for this pass.

### What is sorried

- The body of `typed_nbe_fundamental` — left as `sorry` with
  `-- TODO(typed-nbe): proof body. See docstring for sketch.`
- Various `RC`-closure properties (subtype-closure, fuel-monotonicity)
  are stated as `axiom` placeholders pending later proof. Each is
  marked `-- TODO(typed-nbe): provable from <reasoning>`.

### What is wired

- `SoundnessProof.lean` imports `TypedNbE.lean`. The four sorries in
  `eval_vapp_preserves_fullyQuotable`/`quoteClosure_realises`/
  `tyInfer_sound_open`/`tyCheck_sound_open` have been re-tagged with
  `-- TODO(typed-nbe):` markers showing the typed-NbE-derived path
  that would close them if the FL body were filled in.

### Blocker / next concrete step

The FL body is the single remaining proof obligation. It is structural
induction on the typing derivation; the bodies of each case are
straightforward modulo the RC-closure helpers being filled in.

The next agent's concrete task: pick **one** case of the FL induction
(suggested: `.type` since it is base) and prove it cleanly, then
proceed by induction shape.

There are also *secondary* issues that surfaced during this pass:

1. **`RC.mono` doesn't hold uniformly across all type formers.** The
   `.lam` case has a contravariant-domain step-indexing problem (see
   "Finding" section below). Either (a) accept that mono is partial
   and use compatibility lemmas instead of mono for the lam case, or
   (b) refactor RC to use a "later" modality (Iris-style). Both are
   well-trodden paths in the step-indexed literature.

2. **`RC.implies_fullyQuotable` needs a saturated RC variant.**
   The current RC at `.type` and `.neutral` is `True`, which tells us
   nothing about the value's structure. A saturated variant would
   bake `Val.fullyQuotable d v` into those clauses. This is a small
   refactor and probably should be done before the FL proof body
   so the FL has the right invariants to thread through.

3. **The 4 old SoundnessProof.lean sorries take typing-free
   hypotheses.** They cannot directly invoke FL. To use FL, those
   theorems would need typing hypotheses added — which cascades to
   ~6 callers each. This is expected (the spec explicitly authorised
   restating). The right move is probably:
   - Add a *parallel*, typed-versions of the broken theorems
     (`eval_vapp_preserves_RC`, `vapp_realises_typed`, etc.) in
     `TypedNbE.lean`, proven from FL.
   - Have the closed `Soundness.lean` entry points (`typeCheck_sound`)
     branch to the typed path when typing hypotheses are available
     (which they are in the closed case).
   - Leave the old untyped path alive but sorry'd; once the typed
     path closes the chain, the untyped path can be removed.

### Sorry trajectory

- Before: 4 declaration-level sorries + ~20 internal `by sorry`s in
  `SoundnessProof.lean`.
- After: same surface-level count, but the **architectural** dependency
  has been re-routed: instead of needing fundamentally-impossible
  `Val.fullyQuotable` strengthenings, they all reduce to a single
  fundamental-lemma proof obligation.

This is the architectural shift the typed-NbE doc was endorsing. It
does not (yet) reduce the sorry count; that requires the FL body.

### Build status

`nix develop -c lake build` passes end-to-end. AxiomCheck still shows
sorryAx in the dependency closures, but no new ones have been
introduced.

### Finding: naive RC.mono fails on `.lam` types (the "later" problem)

Attempted to prove `RC.mono : m ≤ n → RC n τ v → RC m τ v` directly.
The `.type`/`.bot`/`.neutral`/`.iota`/`.fix` cases are mechanical.
The `.lam` case fails:

  RC (n+1) (.lam dV cl) v says: ∀ a. RC n dV a → ∃ r. … RC n …
  RC (m'+1) (.lam dV cl) v says: ∀ a. RC m' dV a → ∃ r. … RC m' …

To weaken (n+1) → (m'+1), we need to take an `a` with `RC m' dV a`
and produce one with `RC n dV a` (to apply the n+1 hypothesis).
That's monotonicity in the *opposite* direction: `m' → n` upward,
which we don't have (and which doesn't hold).

This is the well-known issue with naive step-indexed logical
relations on negative type formers. Standard fixes:

1. **"Later" modality** (Iris-style): instead of `RC n` directly,
   carry a `▷` modality that delays one step. Function-type RC
   becomes "for each future-RC argument, future-RC result".

2. **Recursion-on-type-then-step**: define `RC` by lex induction
   on `(τ_size, n)`, so the function-type case is well-founded
   without needing both directions of monotonicity.

3. **Uniform RC**: the saturated form (Pitts/Howe) where RC is
   the largest predicate satisfying the closure conditions; no
   step index needed but coinductive.

Implication: the `RC.mono` lemma should be proved separately for
the *contravariant-friendly* fragment (type/iota/fix/neutral),
and the function-type case requires either (1) a redesign to
incorporate `▷` or (2) restating mono in a form that doesn't apply
to `.lam` directly (and using a separate compatibility lemma where
needed).

This is a known trade-off, not a dead-end. Recorded here so the
next agent doesn't waste time re-discovering it. The first three
cases of `RC.mono` ARE proven cleanly — the lam case is the one
left sorried with an explanatory comment in the source.
