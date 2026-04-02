# Deep Dive: Amin-Rompf POPL 2017 and Och's Transitivity Problem

## Context

Och's soundness proof has a `sorry` in the **ascription case**:

```
v = concEval(term)    -- concrete runtime value
sigma = absEval(term) -- abstract type of the term
tau' = absEval(ty)    -- declared type annotation
```

We have `SubtypeCore v sigma` (from IH) and `subCheckNF sigma tau' = true` (from
WellTyped). We need `SubtypeCore v tau'`. This is a transitivity problem:
`v <= sigma` and `sigma <= tau'` implies `v <= tau'`.

The lit review recommended the Amin-Rompf approach. This document examines whether
it truly fits.

---

## 1. What Does "Transitivity Only For Runtime Objects" Actually Mean?

### The DOT "Bad Bounds" Problem (Amin-Rompf's Motivation)

The Amin-Rompf insight was developed for DOT (Dependent Object Types), Scala's core
calculus. DOT has **type members** where an object can declare `type A: S..U`, meaning
"I have an abstract type A that is a supertype of S and a subtype of U." By
transitivity, this implies `S <: U`.

The "bad bounds" problem: a programmer can write `type A: Int..String`, which would
imply `Int <: String`. In general, DOT's type system **cannot** prevent bad bounds at
the syntactic/type-checking level because:

1. **Narrowing breaks good bounds.** Both `{A: Bot..Bot}` and `{A: Top..Top}` have
   "good" bounds. But narrowing their intersection gives `{A: Bot..Bot} & {A: Top..Top}`,
   which implies `Top <: x.A <: Bot` -- bad bounds emerge from combining good ones.

2. **Transitivity + narrowing are mutually dependent** and DOT cannot have both in
   full generality at the type-checking level.

### The Key Insight: Values Have Good Bounds By Construction

The resolution: **at runtime, every object that actually exists was created with a
concrete type assignment.** If an object has `type A = T` (a concrete type member),
then its bounds are `{A: T..T}` -- trivially good. Bad bounds only arise in
**hypothetical/dead code paths** where a variable has a declared type with bad
bounds, but no actual runtime object can witness those bounds.

Therefore: **transitivity of subtyping only needs to hold when the intermediate type
is the type of an actual runtime value (not an arbitrary type hypothesis).**

### Mechanism in the Coq Development

In the Coq code (github.com/TiarkRompf/minidot, `popl17/` directory), this manifests
as follows:

1. **`val_type env v T`** -- a predicate relating runtime values to types. Each
   constructor embeds an `stp2 true env ... [] n` witness. The `[]` (empty abstract
   environment) is crucial: it means no hypothetical type variables are involved.

2. **`valtp_widen`** -- the transitivity-for-values lemma:
   ```coq
   Lemma valtp_widen: forall vf H1 H2 T1 T2,
     val_type H1 vf (bind_tm T1) ->
     stpd2 true H1 T1 H2 T2 [] ->
     val_type H2 vf (bind_tm T2).
   ```
   By inverting `val_type`, we extract an `stp2` witness. Then `stpd2_untrans`
   chains two `stpd2 true` judgments together. This works because the abstract
   environment is empty `[]` -- no bad bounds can interfere.

3. **`stp_trans`** (static transitivity) is proved by induction on `tsize T2`
   (the size of the intermediate type). This is about ~40 lines.

4. **`stp2_trans_aux`** (dynamic transitivity) is proved with derivation bounds.
   The full transitivity infrastructure spans ~450 lines across several lemmas
   (`stp2_narrow_aux`, `stp2_substitute_aux`, etc.).

### What Property Do Values Have That Arbitrary Types Don't?

Precisely: **values are canonical forms with bounded structure.** When you invert
`val_type v T`, you learn that `v` is one of finitely many shapes (bool, closure,
type tag, object), each carrying a concrete `stp2` witness at empty abstract
context. The empty context eliminates:

- Bad bounds (no hypothetical type members)
- Narrowing complications (no abstract variables to narrow)
- Infinite transitivity chains (derivation sizes are bounded)

In contrast, arbitrary types can mention abstract type variables with unconstrained
bounds, making transitivity unprovable in general.

---

## 2. How Does Amin-Rompf State Their Soundness Theorem?

The soundness theorem is `full_safety`:

```coq
Theorem full_safety : forall n e tenv venv res T,
  teval n venv e = Some res -> has_type tenv e T ->
  wf_env venv tenv -> res_type venv res T.
```

Where `res_type` is:
- `res = Some v` implies `val_type venv v T` (semantic style -- the result is in
  the value set of the type)
- `res = None` means stuck (which the theorem rules out for well-typed terms)

**This is style (b): "if evaluation succeeds, the result is in the value set of the
type."** It is NOT progress+preservation; there is no step relation. The fuel-bounded
evaluator returns a value directly.

### Comparison to Och's Soundness

Och's soundness is:
```lean
theorem soundness : absEval fuel G e = some tau ->
  concEval fuel gamma e = some v ->
  EnvConsistent gamma G ->
  WellTyped fuel G e = true ->
  Subtype' v tau
```

This is very similar to Amin-Rompf's statement, but with a critical difference:
**Och has TWO evaluators** (concrete and abstract), whereas Amin-Rompf has one
evaluator and a separate typing judgment (`has_type`). In Och, the abstract
evaluator serves as both the typing judgment AND the type computation.

The structural parallel is:
| Amin-Rompf | Och |
|---|---|
| `has_type tenv e T` | `absEval fuel G e = some tau` |
| `teval n venv e = Some (Some v)` | `concEval fuel gamma e = some v` |
| `wf_env venv tenv` | `EnvConsistent gamma G` |
| (none) | `WellTyped fuel G e = true` |
| `val_type venv v T` | `Subtype' v tau` |

Och's `WellTyped` plays the role of "the ascription checks pass" -- it ensures that
every ascription encountered during evaluation has `subCheckNF sigma tau' = true`.
Amin-Rompf does not need this because they have a separate typing judgment that
already ensures type safety.

---

## 3. Does Amin-Rompf Use a Separate Subtyping Relation?

**Yes -- they use TWO separate subtyping relations:**

1. **`stp G GH T1 T2`** -- static/syntactic subtyping. Used in the typing judgment
   `has_type`. This is a standard inductive relation with rules for reflexivity,
   transitivity, function subtyping, etc.

2. **`stp2 m G1 T1 G2 T2 GH n`** -- dynamic/semantic subtyping. Used in `val_type`.
   This has a boolean flag `m` controlling whether the last rule can be transitivity,
   and a derivation bound `n`.

The key bridge lemma is `stp_to_stp2`: static well-typedness converts to dynamic
subtyping when environments are well-formed.

**Och does NOT have this separation.** Och uses `subCheckNF` (a Bool-valued
algorithmic checker) as the subtyping notion in `WellTyped`, and `SubtypeCore`/
`Subtype'` (inductive Prop relations) in the soundness output. The gap between these
is exactly the transitivity problem.

---

## 4. The `seen` Set Problem

### How Och's seen Set Works

Och's `subCheckNF` maintains a `seen : List (Expr * Expr)` that tracks which
`(a, b)` pairs have already been visited. When encountering a mu type:

- **Self-intro**: `a <= mu x body` adds `(a, mu)` to seen, then checks
  `a <= body[x := mu]`
- **Self-elim**: `mu x body <= b` adds `(mu, b)` to seen, then checks
  `body[x := mu] <= b`

If a pair is already in `seen`, the check succeeds immediately (coinductive
hypothesis).

### The Transitivity-of-Seen-Sets Problem

For checker transitivity, we need:
```
subCheckNF fuel ctx seen1 v sigma = true
subCheckNF fuel ctx seen2 sigma tau' = true
=> subCheckNF fuel ctx ??? v tau' = true
```

The problem: what `seen` set do we use for the composed check? The two input checks
may have accumulated different seen sets during their recursive descent. The composed
check needs to handle recursive type unfoldings that combine patterns from both
inputs.

### What the Literature Says

**Amin-Rompf:** Does NOT address this problem. Their system has no equi-recursive mu
types with a seen set. The DOT `TBind` type uses a different mechanism (fuel-indexed
`val_type` with `v_pack`). Transitivity in their system goes through `stp2`, which
tracks derivation size bounds, not seen sets.

**Zhou-Oliveira-Zhao (OOPSLA 2020):** Their transitivity proof is on the
**declarative** `Sub` relation, NOT on an algorithmic checker with a seen set.

Their declarative `Sub` relation uses the Amber-like rule:
```coq
| SA_rec: forall L A1 A2 E,
    (forall n X, X \notin L ->
        Sub ((X ~ bind_sub) ++ E) (unfoldT A1 X n) (unfoldT A2 X n)) ->
    Sub E (typ_mu A1) (typ_mu A2).
```

The `forall n` quantifies over ALL unfolding depths -- this is what gives
transitivity. The `trans_aux` lemma is proved by induction on `WFS E B`
(well-formedness of the intermediate type), and the mu case works because `WFS`
requires all unfoldings to be well-formed. The proof is clean: ~37 lines.

Their algorithmic `sub` uses **locally nameless** representation with fresh variables
(not an explicit seen set). The mu rule requires checking at BOTH one unfolding AND
two unfoldings (the "double unfolding" rule):
```coq
| sa_rec: forall L A1 A2 E,
    (forall X, X \notin L ->
        sub (X ~ bind_sub ++ E) (open A1 X) (open A2 X)) ->
    (forall X, X \notin L ->
        sub (X ~ bind_sub ++ E) (open A1 (open A1 X)) (open A2 (open A2 X))) ->
    sub E (typ_mu A1) (typ_mu A2).
```

This is for **iso-recursive** types (with explicit fold/unfold). They avoid a seen
set entirely by using locally nameless + fresh variables, which naturally prevents
revisiting the same pair.

**Brandt-Henglein (1998):** Their fixpoint/coinduction principle requires
**contractivity** -- making progress through at least one type constructor before
revisiting a pair. This is analogous to Och's seen set but formulated differently.
They do not address algorithmic transitivity with explicit seen sets.

**Danielsson-Altenkirch (2010):** Mixed induction/coinduction. Transitivity is an
inductive rule (finitely many uses), structural rules are coinductive (infinite
unfolding). This avoids seen sets by using Agda's native coinduction. Not directly
applicable to an algorithmic checker.

**Jones-Pearce (2016):** Prove the algorithmic checker sound w.r.t. a coinductive
tree relation. Transitivity is trivial on the tree relation (simulation is
transitive). The seen set only appears in the algorithmic checker, and soundness
w.r.t. the tree relation absorbs the seen-set complexity. This is the closest
existing approach to handling seen-set transitivity, but it requires defining the
coinductive tree relation as an intermediate layer.

### Assessment: No One Has Proved Seen-Set Transitivity Directly

No mechanized proof in the literature directly proves transitivity of an algorithmic
checker that uses an explicit seen set for equi-recursive types. The existing
approaches are:

1. **Prove transitivity of a declarative/semantic relation, prove the checker sound
   w.r.t. it** (Zhou-Oliveira-Zhao, Jones-Pearce).
2. **Avoid seen sets** by using locally nameless + fresh variables (Zhou-Oliveira-Zhao
   algorithmic formulation).
3. **Use fuel/derivation bounds** instead of seen sets, getting transitivity from
   bound composition (Amin-Rompf).
4. **Use coinduction natively** (Danielsson-Altenkirch, Brandt-Henglein).

---

## 5. Proof Size Metrics

### Amin-Rompf POPL 2017 Coq Development

Repository: github.com/TiarkRompf/minidot, `popl17/` directory.

| File | Lines | Contents |
|------|-------|----------|
| stlc.v | ~400 | STLC baseline (no subtyping) |
| fsub.v | ~1500 | System F<: (the paper's main contribution) |
| fsub_equiv.v | ~? | F<: with small-step equivalence |
| fsub_mut.v | ~? | F<: with mutable references |
| dot.v | ~2100 | DOT (dependent object types) with TBind |

Transitivity-related code in `fsub.v` (~450 lines):
- `stp_trans_aux` + `stp_trans`: ~40 lines (static transitivity)
- `stp_narrow_aux` + `stp_narrow`: ~50 lines
- `stp2_narrow_aux`: ~120 lines
- `stp2_substitute_aux`: ~200 lines (two-environment substitution)
- `valtp_widen`: ~5 lines (the key bridge lemma)

The `valtp_widen` lemma itself is trivial (~5 lines) because all the work is in
building the `stp2` infrastructure. The system-specific infrastructure (stp2 rules,
narrowing, substitution) is NOT reusable -- it is tied to F<:'s specific type
structure.

### Zhou-Oliveira-Zhao OOPSLA 2020 Coq Development

Repository: github.com/juda/Iso-Recursive-Subtyping, `OOPSLA/src/` directory.

| File | Contents |
|------|----------|
| definition.v | Type syntax, subtyping (declarative + algorithmic), typing, reduction |
| infra.v | Infrastructure lemmas |
| subtyping.v | Declarative subtyping properties (reflexivity, transitivity) |
| subtyping2.v | Algorithmic subtyping properties |
| subtyping3.v | Soundness/completeness of algorithmic w.r.t. declarative |
| decidability.v | Decidability proof |
| typesafety.v | Type safety |

Declarative transitivity (`trans_aux`): ~37 lines. Clean and short because the
declarative relation with `forall n` in the mu rule makes the induction
straightforward.

---

## 6. Does Amin-Rompf Truly Fit Och's Problem?

### Similarities

| Feature | Amin-Rompf | Och |
|---------|-----------|-----|
| Fuel-bounded evaluator | Yes (Coq `Fixpoint` on `nat`) | Yes (Lean `def` on `Nat`) |
| Soundness = "eval gives value, value has type" | Yes | Yes |
| Induction on fuel | Yes | Yes |
| Need transitivity at ascription/subsumption | Yes (typing_sub rule) | Yes (asc case) |

### Critical Differences

| Feature | Amin-Rompf | Och |
|---------|-----------|-----|
| Recursive types | TBind (simple) in DOT only | mu x ann body (equi-recursive, central) |
| Subtyping termination | Derivation bounds on `stp2` | Seen set in `subCheckNF` |
| Two evaluators | No (one eval + has_type) | Yes (concEval + absEval) |
| Subtyping relation | Two relations (stp, stp2) | SubtypeCore (too weak) + subCheckNF (Bool) |
| Self-intro / self-elim | Not applicable (TBind uses v_pack) | Core feature of subCheckNF |
| Contravariant domains | Standard (in stp rules) | In subCheckNF but not in SubtypeCore |

### The Core Mismatch

Amin-Rompf's key technique is: define `val_type` to embed `stp2` witnesses at empty
abstract context, then `valtp_widen` is trivial because it just composes `stp2`
derivations.

**Och cannot directly replicate this because:**

1. **Och's algorithmic checker (`subCheckNF`) is the ONLY subtyping notion that
   handles mu types correctly.** There is no separate declarative relation with
   transitivity. `SubtypeCore` lacks self-intro and contravariant domains.

2. **Och's seen set is incompatible with derivation bounds.** Amin-Rompf's `stp2`
   uses a natural number derivation bound `n` that composes naturally
   (`S (n1 + n2)`). Och's seen set does not compose -- two different checks
   accumulate different seen sets.

3. **Och has equi-recursive types as a central feature.** Amin-Rompf's DOT handles
   `TBind` via `v_pack` (a value-level existential), not via equi-recursive
   unfolding. The recursion in DOT is controlled by `val_type`'s fuel index, not by a
   seen set.

### The Amin-Rompf Insight IS Applicable, But Not the Mechanism

The insight "transitivity only for runtime values" IS relevant to Och:

- In the asc case, `v` is a concrete value (output of `concEval`), not an arbitrary
  expression.
- Values in Och have restricted shapes: `lam`, `type`, `mu` (wrapping a value body).
  They cannot be `var` or `app` (these would be stuck/neutral).
- This means `subCheckNF v sigma` has limited recursion patterns compared to
  arbitrary `subCheckNF a b`.

However, the **mechanism** (defining `val_type` with embedded `stp2` witnesses)
requires having a composable subtyping relation. Och would need to either:

(a) **Define a new semantic subtyping relation** (replacing SubtypeCore) that handles
    mu types and contravariant domains, prove it transitive, and prove subCheckNF
    sound w.r.t. it.

(b) **Prove checker transitivity directly** for `subCheckNF`, restricted to the case
    where the LHS is a value. The value restriction limits the shapes that can appear,
    potentially making the proof tractable.

(c) **Reformulate soundness output** to use `subCheckNF` directly:
    `subCheckNF fuel ctx [] v tau = true`. Then the asc case becomes: compose
    `subCheckNF v sigma` and `subCheckNF sigma tau'` into `subCheckNF v tau'`. This is
    still the seen-set transitivity problem, but now everything is in the same
    framework.

---

## 7. Recommended Path Forward

### Option B (Semantic Relation) Seems Most Viable

Based on this analysis, the most promising approach is:

1. **Define a fuel-indexed semantic subtyping relation** `ValSub (n : Nat) (v : Expr)
   (T : Expr) : Prop` that:
   - Handles equi-recursive mu unfolding (self-intro and self-elim)
   - Handles contravariant function domains
   - Is defined by well-founded recursion on fuel (not coinduction)
   - Only applies to values (not arbitrary expressions)

2. **Prove `ValSub` is transitive** (or more precisely: `ValSub n v T1 -> subCheckNF
   T1 T2 = true -> ValSub n v T2`). This is the Amin-Rompf `valtp_widen` pattern.

3. **Prove `subCheckNF` sound w.r.t. `ValSub`**: if `subCheckNF v T = true` and `v`
   is a value, then `ValSub n v T` for some `n`.

4. **Restate soundness** in terms of `ValSub` instead of `SubtypeCore`/`Subtype'`.

This approach:
- Follows the Amin-Rompf architecture (fuel-indexed value-type relation)
- Handles equi-recursive types via the fuel index (each unfolding consumes fuel)
- Avoids seen-set composition (the semantic relation doesn't use a seen set)
- Is natural in Lean 4 (well-founded recursion on Nat)

### Alternative: Direct Checker Transitivity for Values (Option B-lite)

A lighter-weight approach: prove a restricted transitivity lemma directly:

```lean
theorem subCheckNF_trans_val (fuel : Nat) (ctx : Env) (v sigma tau : Expr)
    (hv : IsValue v)
    (h1 : subCheckNF fuel ctx [] v sigma = true)
    (h2 : subCheckNF fuel ctx [] sigma tau = true)
    : subCheckNF fuel ctx [] v tau = true
```

This avoids defining a new semantic relation but requires proving that the seen-set
problem doesn't arise when the LHS is a value (because values have limited shapes,
the recursion patterns are constrained).

**Risk:** Even with the value restriction, the seen-set composition problem may still
be hard. When `sigma` is a mu type, `h1` may have accumulated seen pairs involving
`v` and unfoldings of `sigma`, while `h2` has seen pairs involving `sigma` and
unfoldings of `tau`. The composed check needs different seen pairs.

---

## Sources

- [Amin & Rompf, POPL 2017 paper](https://www.cs.purdue.edu/homes/rompf/papers/amin-popl17a.pdf)
- [Amin & Rompf, arXiv extended version](https://arxiv.org/abs/1510.05216)
- [Amin & Rompf, Coq development](https://github.com/TiarkRompf/minidot/tree/master/popl17)
- [Rompf & Amin, DOT Soundness OOPSLA 2016](https://www.cs.purdue.edu/homes/rompf/papers/rompf-oopsla16.pdf)
- [Zhou, Oliveira & Zhao, OOPSLA 2020](https://dl.acm.org/doi/10.1145/3428291)
- [Zhou, Oliveira & Zhao, TOPLAS 2022 extended](https://i.cs.hku.hk/~bruno/papers/toplas2022.pdf)
- [Zhou, Oliveira & Zhao, Coq development](https://github.com/juda/Iso-Recursive-Subtyping)
- [Danielsson & Altenkirch, MPC 2010](https://www.cse.chalmers.se/~nad/publications/danielsson-altenkirch-subtyping.pdf)
- [Jones & Pearce, FTfJP 2016](https://homepages.ecs.vuw.ac.nz/~tim/publications/ftfjp16-mechanical-subtyping.pdf)
- [Brandt & Henglein, 1998](https://journals.sagepub.com/doi/10.3233/FI-1998-33401)
