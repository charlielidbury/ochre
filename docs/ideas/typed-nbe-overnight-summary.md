# Typed NbE — overnight summary (2026-04-25 → 2026-04-26)

## What you authorised

Autonomous overnight work toward "sound and consistent Och" via typed-everything. You said: "It will probably only take a couple of agents", "DO NOT WAIT FOR INPUT, just work towards our end goal as much as possible", "do things properly over quick wins".

## What happened

**12 overnight passes (6 through 17). Sorry count: 9 → 8 (net -1).**

The "couple of agents" estimate turned out conservative by ~10×. The architecture has fundamental structural limits we did not foresee, and each pass spent agent-time mapping where those limits are. We now have a precise map.

## Five critical findings (the walls)

Each finding is a confirmed obstruction with concrete evidence, not a maybe.

### 1. Pass 9 — keystone substitution lemma was *wrong as stated*

Concrete Ω-style counterexample: `clA.openω v` for arbitrary `v` exhausts fuel, making the existential unprovable. Pass 11 fixed the statement by adding RC-typing on `v`.

### 2. Pass 10 — `RC_env` signature refactor doesn't dissolve substitution requirement

We refactored `subtype_closed_aux` to carry `RC_env n d Γ ρ`. The closure cases (`lam`, `iota_struct`, `fix_struct`) still structurally need Val-level substitution because SubV body premises are at fresh-neutral-opened bodies while goals need concrete-value-opened bodies. `RC_env` doesn't bridge that gap.

### 3. Pass 14 — RC-threaded eval-commutation hits a wall

Three concrete sub-walls in the substitution path: fuel/unf alignment, `RC.lam_elim` shape constraint, recursive RC threading through vapp. Each is its own multi-pass project. Pass 12+13 landed ~570 LOC of supporting infrastructure (Val.substLvl data, WellFormed predicates, identity-on-closed, env helpers — all axiom-clean), but the eval-commutation lemma itself remains unproven.

### 4. Pass 15 + 16 — `neutral_ascent` and `revapp_L` are not provable as stated (same finding)

RC at `.neutral` is defined as plain saturation (syntactic). The conclusion needs RC at arbitrary closure-form τ_b (semantic). Verified counterexamples in both passes. They are the same architectural problem under different SubV constructors.

### 5. Pass 17 — the RC-at-.neutral redesign that fix #4 pointed to also fails

The "Option A" lower-step realisation conjunct hits two structural problems:
- **Off-by-one barrier**: well-founded lower-step realisation can't close closure-form sub-cases due to step-indexing arithmetic; same-step realisation is needed but Lean's structural recursion rejects it.
- **Cascading regression**: the redesign breaks existing axiom-clean lemmas (`SubV.neutral_struct`, `SubTV.to_neutral`).

UPred-style infrastructure (~500-1000 LOC) is the theoretical workaround but is heavy.

## What landed (axiom-clean infrastructure, ~700+ LOC)

- **`SubTV` substrate** (pass 6): typed-everything subtype relation as logical relation, 7 constructors.
- **`RC_env` (pass 5) + `RC_env.cons`/`.nil`/`.mono`** (pass 10): typed-environment realisation predicate.
- **`Val.substLvl` data layer** (pass 12): mutual definitions for `Val`/`Neutral`/`Closure`/`Closure.envSubstLvl`.
- **`WellFormed` predicate family** (pass 13): captures the invariant that closure-form heads have `.isNeutral` arguments.
- **Identity-on-closed lemmas** (pass 13): `substLvl_of_levelsBelow` for all four data types.
- **`Closure.envSubstLvl` commutation** (pass 13): `_cons`, `_cons_inv`, `_length`, `_getElem?`, `_take`.
- **`Val.eval_substLvl_identity`** (pass 14): combines identity-on-closed with eval_levelsBelow.

All 18+ substrate lemmas axiom-clean. The substrate is correctly shaped for any future approach.

## What did NOT land

The five inline sorries in `subtype_closed_aux` (`iota_intro`, `revapp_L`, `neutral_ascent`, `unfold_fix_L`, `unfold_iota_L`) all remain. Plus three declaration-level sorries (`SubV_subst_neutral_to_value`, `SubV_subst_pair`, `typed_nbe_fundamental_open`). The 4 declaration-level sorries in `SoundnessProof.lean` are unchanged.

## Strategic options when you wake up

In rough order of "ambitiousness":

### A. Continue grinding the substitution lemma chain (passes 12-14 trajectory)

Build the rest of the substitution machinery: RC-threaded eval-commutation, then SubV-preservation, then combine. Estimated 3-4 more passes (~500-700 LOC total) to close `lam`/`iota_struct`/`fix_struct` cases. Doesn't address the `neutral_ascent`/`revapp_L` walls.

### B. Bite the UPred-style infrastructure for RC-at-`.neutral`

~500-1000 LOC. Closes `neutral_ascent` and `revapp_L` simultaneously. Significant new infrastructure but is the theoretically-clean fix. Doesn't address the substitution lemma chain.

### C. Drop `SubV.neutral_ascent` from the algorithm

Instead of fighting it, restructure the algorithmic subtype check so it doesn't use `neutral_ascent`. This is an algorithmic-side change rather than a proof-side one. Trade-off: may break the algorithm's completeness on cases that currently route through `neutral_ascent`. Test impact would need careful audit.

### D. Pivot to alternative soundness architecture

Possibilities:
- **Quote-based**: prove soundness via the existing `Val.fullyQuotable` machinery without typed RC. Tried previously and shown impossible (Halting reduction in `quote-witness-feasibility.md`) — but the architectural lessons may be useful.
- **Guarded recursion / step-indexing infrastructure**: a Lean 4 port of Iris-style logical relations. Heavy.
- **Restructure FL to fragment-based**: prove FL on a fragment of well-typed Och that excludes the problematic shapes.

### E. Accept the boundary

The substrate is in good shape. The typed pipeline is integrated and produces real wins (`five_ ⊑ Nat_` at fuel 800). The four `SoundnessProof.lean` sorries map to documented limitations of OCH's non-total design (per `paper.md` §7.2). Document the typed-NbE state, ship what we have, revisit when better tools are available.

## My honest take

If "sound" must mean axiom-clean `typeCheck_sound`, then **B + A combined** is needed and is genuinely 5-10 more focused passes. Most realistic path to actually closing all sorries.

If "sound" can mean "soundness story is documented and the boundary is honest", then **E** is the truthful position. The investigation has produced enough evidence that the four remaining `SoundnessProof.lean` sorries are not closeable without significant new infrastructure.

If you want to keep autonomous agents running on this, **B** is the highest-leverage single move (closes 2 of 5 inline sorries, paves the way for the substitution-dependent ones). But it's heavy.

The path that's *not* worthwhile: more "try a small fix" passes. The space has been mapped. The remaining work is significant infrastructure, not incremental fixes.

## Trajectory summary

| Pass | What happened | Sorry count |
|------|--------------|-------------|
| 6 | Typed-everything design + SubTV substrate | 9 |
| 7 | `lam`/`iota_struct` closed via sorried keystone | 8 |
| 8 | `fix_struct` closed via sorried `SubV_subst_pair` | 8 |
| 9 | Critical finding #1: keystone wrong (Ω) | 8 |
| 10 | RC_env refactor; finding #2: doesn't dissolve walls | 8 |
| 11 | Keystone statement fixed (RC-typed) | 8 |
| 12 | Val.substLvl data layer (axiom-clean) | 8 |
| 13 | WellFormed + env helpers (axiom-clean) | 8 |
| 14 | Finding #3: eval-commutation walled | 8 |
| 15 | Finding #4: neutral_ascent unprovable | 8 |
| 16 | Finding #5 = #4: revapp_L unprovable (same root) | 8 |
| 17 | RC redesign breaks structural recursion | 8 |

12 passes. ~700 LOC axiom-clean infrastructure. Net -1 sorry. Comprehensive map of the architecture's structural limits.

The agents performed honestly throughout. Each pass either landed infrastructure or surfaced a precise wall. The "diminishing returns" pattern in sorry count reflects the *space being mapped*, not bad work.

## Files for review

- `lean/Och/TypedNbE.lean` — the main work, ~1100 LOC including all infrastructure and walled sorries
- `docs/ideas/typed-nbe-implementation-log.md` — full pass-by-pass log with each post-mortem
- `docs/ideas/typed-everything-architecture.md` — pass 6's design doc
- `lean/Och/AxiomCheck.lean` — verifies which lemmas are axiom-clean

Build is green throughout. Test suite passes (~100 tests on typed pipeline including `five_ ⊑ Nat_`).
