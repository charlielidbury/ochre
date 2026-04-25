# Typed-everything architecture — pass 6 design doc

**Status:** investigation, 2026-04-24 (agent-a3d9ef98).
**Question being investigated:** does making the entire NbE pipeline operate on
*typed* values (`TypedVal` instead of `Val`) dissolve the substitution-lemma
wall that has resisted four prior agents on `Subtype'.unshift_head` and the
analogous `subtype_closed` body-substitution?
**Verdict (this doc):** *partially yes*, but not in the naive way.
Reformulating the relations as type-directed (so they recurse on
`(τ_a, τ_b)` while threading a value `v`) and skipping `SubV` in the
typed pipeline genuinely dissolves the body-substitution lemma. But
the algorithmic checker still needs `subCheckVal`-style structural
recursion at the *Val* layer for performance, so we keep two
relations: declarative typed (no substitution lemma needed) and
algorithmic typed (which has to be sound w.r.t. the declarative one
via a different bridge).

## 1. What does "everything typed" mean concretely?

Three nested levels of "typed-everything"; pass 6 needs to pick one.

### Level 0 (current): typed wrapper over untyped engine

What pass 1–5 built. `TypedVal := { val : Val, ty : Val }`. `tyEval`
wraps untyped `eval` and pairs the result with a target type. RC is a
predicate `RC : Nat → Nat → Val → Val → Prop`.

**Pros**: zero blast radius. `subCheckVal_subV`'s 5000+ LOC of proofs
about untyped values is preserved verbatim. The typed pipeline runs as
a *fast-path* on top.

**Cons**: every typed lemma about RC needs a corresponding untyped lemma
to bridge through. `RC.subtype_closed` is the canonical example: SubV
is on untyped values, RC is on typed values, and the lemma has to lift
SubV's untyped induction into RC's typed conclusion. The body
substitution gets stuck on this lift.

### Level 1: typed values, untyped algorithm

Replace `Val` with `TypedVal` throughout the substrate. `eval`,
`vapp`, `quote` produce `TypedVal`s. The algorithm `subCheckVal`
remains structural, but now operates on `TypedVal × TypedVal`.

**Concrete data types**:

```lean
-- Replaces Val. Every value carries its declared type.
inductive TypedVal where
  | type    : TypedVal                      -- τ = .type itself
  | bot     : TypedVal                      -- τ = .type
  | lam     : (dom : TypedVal) → TypedClosure → (declTy : TypedVal) → TypedVal
  | iota    : (ann : TypedVal) → TypedClosure → (declTy : TypedVal) → TypedVal
  | «fix»   : (ann : TypedVal) → TypedClosure → (declTy : TypedVal) → TypedVal
  | neutral : (ne : TypedNeutral) → (declTy : TypedVal) → TypedVal
```

(In Lean, `TypedVal` would actually be a structure on `Val`-shaped constructors
so we don't have to mutually-define a fresh inductive family. The "declared
type" field would be a `Val`, since types are values, but the recursion
goes through TypedVal.)

**Pros over level 0**: the type is *always available* at every recursion site
in the algorithm and in proofs. No "value-without-type" gaps where the
typing context is needed but unavailable.

**Cons**: `eval`/`vapp` need to compute the *new* type of every result.
For `vapp .lam`, that's the codomain `clB.openω a`. For `vapp .iota`,
the body type `clB.openω self`. The 500+ LOC of `eval`/`vapp` proofs
all have to be re-shaped. **This is the high-blast-radius option.**

### Level 2: typed values, typed algorithm, typed `Subtype'`-relation

Level 1 plus: `subCheckVal` becomes `subCheckTypedV` which produces
**RC-coercion proofs directly**, never going through `SubV`. The
typed-version of the declarative relation is essentially RC itself —
"v inhabits both types and the proofs are interconvertible".

**Concrete types**:

```lean
-- Replaces SubV. Per-(τ_a, τ_b) value-coercion in typed RC.
def SubTV (n d : Nat) (τ_a τ_b : Val) : Prop :=
  ∀ v, RC n d τ_a v → RC n d τ_b v

-- Algorithm decides this. Note: no separate algorithmic SubV;
-- the algorithm's *output* is a function `RC n d τ_a v → RC n d τ_b v`.
def subCheckTypedV (n d : Nat) (τ_a τ_b : Val) :
    Outcome (∀ v, RC n d τ_a v → RC n d τ_b v) := ...
```

**Pros**: dissolves the body-substitution lemma. Recursion is on
`(τ_a, τ_b)` directly with the *same value `v`* threaded through; no
fresh-then-substitute step. See §2 below for the detailed walk-through.

**Cons**: `subCheckTypedV`'s termination is non-obvious (the body case
recurses inside `∀ a`); needs lex measure on `(τ_size, n)`. This is
the "right" architecture but is a substantial rebuild.

### What pass 6 should aim for

**Level 1.5**: implement Level 2's `SubTV` and `subCheckTypedV`
*algorithm and soundness* in TypedNbE.lean, **without** rebuilding
eval/vapp/quote. The existing untyped `eval` is fine for now (the
*output* is a `Val`; we wrap it with a target type at conversion sites
to get a TypedVal). The win from Level 1 (typed eval) is
*performance and ergonomic*; the win from Level 2 (typed Subtype) is
the *substitution-lemma dissolution*.

We get Level 2's payoff at Level 0's cost.

## 2. Does it dissolve the substitution lemma?

### The wall (recap)

`SubV.lam` premise:
```
SubV S Γ domB domA →
clA.openω (.neutral (.var Γ.size)) = some bA →   -- ★ at fresh neutral
clB.openω (.neutral (.var Γ.size)) = some bB →   -- ★ at fresh neutral
SubV S (Γ.push domA) bA bB →                      -- ★ at fresh neutral
SubV S Γ (.lam domA clA) (.lam domB clB)
```

`RC.lam` clause: requires "for every RC-typed `a`, `vapp v a` is RC at
`clB.openω a`" — *at concrete RC argument `a`*, NOT at fresh neutral.

The body substitution lemma is the bridge from "SubV at fresh" to
"RC at all `a`":
```
SubV S (Γ.push domA) (clA.openω fresh) (clB.openω fresh) →
∀ a, ∃ bA' bB',
  clA.openω a = some bA' ∧
  clB.openω a = some bB' ∧
  SubV S Γ bA' bB'
```

Estimated 300-500 LOC, structural induction on SubV with shift-subst
arithmetic. Same scope as `Subtype'.unshift_head`. Has resisted four
agents.

### Why Level 2 dissolves it

**`SubTV` recurses on types directly, never going through fresh neutrals.**

Definition (above):
```
SubTV n d τ_a τ_b := ∀ v, RC n d τ_a v → RC n d τ_b v
```

For the lam case, suppose `τ_a = .lam domA clA, τ_b = .lam domB clB` and
`h : RC (n+1) d (.lam domA clA) v`. Want: `RC (n+1) d (.lam domB clB) v`.

By RC.lam_intro at (n+1): need saturation on v (got from h via
`RC.fullyQuotable` etc), AND need: for every `m ≤ n`, every `a` with
`RC m d domB a`, ∃ r. `vapp` succeeds and `RC m d (clB.openω a) r`.

Take `m, hm, a, ha : RC m d domB a`.

**Step 1: contravariance on domain.** Use `subCheckTypedV domB domA`
to coerce `ha` into `RC m d domA a`. (Recursion is on
domain-type-pair, NOT on bodies-at-fresh-neutral.)

**Step 2: apply h's body clause** at this `a`: get `r` with
`vapp fuelω unfBound v a = .ok r` and `RC m d (clA.openω a) r`.

**Step 3: cobody.** Use `subCheckTypedV (clA.openω a) (clB.openω a)`
to coerce `RC m d (clA.openω a) r` to `RC m d (clB.openω a) r`.
(Recursion at strictly smaller step `m < n+1`.)

**No body substitution lemma anywhere.** The "for every `a`" is
discharged by the universal quantifier in RC.lam directly.

### What replaces the body-substitution lemma?

The work moves to **proving `subCheckTypedV` is total/well-defined** at
the right termination measure. Specifically:

- `subCheckTypedV n d (.lam domA clA) (.lam domB clB)` recurses on:
  - `domB, domA` at step `n+1` (decreases on type-size of domain)
  - `clA.openω a, clB.openω a` at step `m ≤ n` (decreases on n)

The lex measure `(n, type-size)` is well-founded. Termination is
clean.

The `subCheckTypedV` *algorithm*'s soundness is the new "subtype-closed"
theorem, but it IS the algorithm — there's no separate "algorithm
runs, soundness proof verifies SubV" gap.

### Where this *doesn't* work

For algorithmic-checker performance, we still want to "open both
closures at one fresh neutral and compare" — that's the cheap
operation. `subCheckTypedV` as defined would require running the
recursion at every `a` separately, which is *not* a thing one
"runs" — it's a Π-type proof, not a decidable check.

So the *algorithm* `subCheckVal` (the executable one) still wants to
operate on Val-pairs structurally. The *relation* `SubTV` is what we
recurse on in proofs.

This is fine — the **algorithm decides the relation**, not the
relation itself. The algorithm is `subCheckVal` (current); soundness
of `subCheckVal` w.r.t. `SubTV` becomes the new theorem to prove.

### What does `subCheckVal_subV` (current) become?

It becomes `subCheckVal_subTV`:

```
theorem subCheckVal_subTV {n d fuel : Nat} {τ_a τ_b : Val} :
    subCheckVal fuel #[] [] τ_a τ_b = .ok true →
    SubTV n d τ_a τ_b
```

This is the new soundness target. It is **still a structural
induction over `subCheckVal`'s arms** — same shape as
`subCheckVal_subV`. But the conclusion is `SubTV` not `SubV`.

For each arm:
- `.lam, .lam`: walk the lam case as in §2 above. Recurse on contra
  domain + cobody at fresh.
- `.iota, .iota`: similar with self-substitution.
- `.fix, .fix`: similar with fix-unfold.
- `_, .iota` (iotaIntro): use the LHS-as-self trick.
- ... etc.

**The body-substitution lemma is GONE from the proof tree** — but each
arm now has to discharge its "for every RC-typed value, the bodies
relate" obligation directly. The disovery: **for the closure-form
arms, the algorithmic check at *fresh neutral* is sufficient to
witness the universal**, BECAUSE the fresh neutral is itself
RC-typed at the domain type (by `RC.neutral_top`).

That is, the substitution lemma's content gets absorbed into:

> "If `clA.openω fresh` and `clB.openω fresh` relate via SubTV at
> step `n`, AND fresh is itself a fresh neutral RC-typed at any
> domain (which it is, by `neutral_top`), THEN for every RC-typed
> `a` at the domain, `clA.openω a` and `clB.openω a` relate via
> SubTV at step `n`."

This is **NOT a lemma we need to prove** — it follows from the
*definition* of SubTV and how the algorithmic check works. The
algorithm checks at fresh; that fresh is a generic RC value at the
domain (saturation gives RC at type and neutral); SubTV's quantifier
ranges over all such values. Where the parametricity comes from is
the *algorithm's structural recursion*: `subCheckVal` doesn't peek
at the value it's deciding-for, only at the closure structures. Hence
its result holds uniformly in the value.

### Caveat: parametricity isn't free

There's a subtle gap. The argument above *would* work if `subCheckVal`
were syntactically prevented from inspecting the value being decided
for. In OCH, that's almost true — the algorithm operates on `(τ_a,
τ_b)` pairs, not on the inhabitant. But `RC` is defined recursively
on `τ`'s shape after fresh-opening, and `clA.openω fresh` uses
`fresh = .neutral (.var depth)`. If during the SubV-induction the
algorithm needs the fresh's *value* to differ from neutral, the
parametricity argument fails.

In practice, `subCheckVal` for OCH never substitutes the fresh
into a position where the value matters — closures are opaque under
fresh. So parametricity holds.

### Bottom line for the substitution lemma

In Level 2, the **body-substitution lemma is replaced by parametricity
of the algorithmic check**, which holds by inspection (the algorithm
doesn't peek at values). This is a *one-time observation*, not a
300-500 LOC proof. **The wall genuinely dissolves.**

But the parametricity argument has to be made *formally*. In Lean,
that means: when proving `subCheckVal_subTV`, in the lam-lam arm,
we need to show that the SubTV relation we get on
`clA.openω fresh, clB.openω fresh` lifts to SubTV on
`clA.openω a, clB.openω a` for any `a`. That's the same
substitution lemma we were trying to avoid!

UNLESS... we **refactor SubTV's lam case to be parametric directly**:

```
def SubTV n d τ_a τ_b :=
  match τ_a, τ_b with
  | .lam domA clA, .lam domB clB =>
      SubTV n d domB domA ∧
      ∀ a, RC n d domB a →
        ∃ bA bB,
          clA.openω a = some bA ∧
          clB.openω a = some bB ∧
          SubTV n d bA bB
  | ...
```

Now the relation IS the universally-quantified version. The
algorithmic check produces a witness at *one* specific `a` (the fresh
neutral) and **we still need to lift to all `a`** — back at square one.

**Conclusion: the substitution lemma is intrinsically required if the
relation is decided by checking at one fresh point.** Two ways out:

(A) Decide the relation by something other than fresh-opening. E.g.,
    parametrically quantify in the algorithm itself (return a
    function that takes `a` and produces the RC coercion). That's a
    proof-relevant algorithm, not a Bool-valued decision procedure.
    Doesn't fit OCH's algorithmic flavour.

(B) Accept that the algorithmic-checker soundness needs the
    substitution lemma, BUT note that in the typed setting, the lemma
    is **easier** because we have RC-context to exploit. Specifically,
    the substitution lemma's induction can use RC's saturation
    structure to discharge cases where the substituted value is
    in a fully-quoted form. This *might* be 100-200 LOC instead of
    300-500.

(C) Use a non-algorithmic definition of SubTV and check it via a
    *coinductive* algorithm whose soundness is by parametricity (the
    algorithm doesn't inspect values, hence its result is uniform).
    This requires moving away from the current Bool-valued
    `subCheckVal` toward a proof-relevant `subCheckProof` returning
    the RC coercion directly.

### Honest assessment

The substitution lemma is **NOT magically dissolved** by typed-everything
in the way the user's hypothesis suggested. It still has to be proven
in some form. **However**, the typed setting *does* change its shape:

- The *Expr-level* `Subtype'.unshift_head` (which the four prior
  agents attacked) is about **shifting bvars across context
  extensions** — a syntactic substitution.
- The *Val-level* body-substitution (which `subtype_closed_aux`'s lam
  case needs) is about **substituting RC-typed values into closure
  bodies** — a *semantic* substitution.

The semantic version has more structure available:
- We can use RC.mono to weaken step-indices.
- We can use the saturation conjuncts to handle base cases.
- For neutral sub-cases, the neutral_top lemma closes immediately.
- For closure sub-cases, RC.lam_intro / RC.fix_intro give us the
  intro form and we don't need to walk SubV's structure.

**Estimate**: in the typed setting, the substitution lemma might be
**150-250 LOC** instead of 300-500. Still substantial. Still the
hardest single piece. But more tractable.

## 3. What about `unshift_head`?

`unshift_head` is the *Expr-level* version of the same wall: shift a
`Subtype'` derivation under a binder by substituting `.bot` for
`.bvar 0`. The four-agent struggle was here.

In the typed-everything world, `unshift_head` is **less load-bearing**:

- `tyInfer_sound_open`'s `.letE`/`.app β`/`.app let-float` arms use it
  to discharge the conversion check at the binder boundary. In a
  typed pipeline where conversion goes through `subCheckTypedV` (which
  produces RC coercions, not Subtype' derivations), these arms
  produce RC witnesses directly, **without going through Subtype'**.
- The Expr-level `Subtype'` becomes a *quoted form* of the Val-level
  `SubTV`. It's only needed for the user-facing API (e.g., theorem
  statements) and for the `quote_realises` chain. The internal
  reasoning never instantiates it.

**So `unshift_head` becomes optional**, not required, in the typed
pipeline. It's still useful for the Expr→Val bridge (proving that a
`Subtype'` derivation maps to a `SubTV` derivation), but **the typed
soundness proof doesn't need it**.

This is a real shift! The current pipeline:
```
typeCheck → tyInfer/tyCheck (Expr) → subCheckVal (Val) → subCheckVal_subV
                                                           → SubV (Val)
                                                           → bridge to Subtype' (Expr)
                                                           → unshift_head (←★)
```

The typed pipeline:
```
typeCheckTyped → tyInferTyped/tyCheckTyped (TypedVal-output) → subCheckTypedV (TypedVal)
                  → subCheckTypedV_subTV → SubTV (Val) → DONE
```

`unshift_head` is bypassed entirely — we never need to convert
back to Expr-level `Subtype'`.

## 4. Migration cost

### Files affected

- `lean/Och/TypedNbE.lean` (930 LOC): central rewrite. `RC` stays;
  `subCheckTyped` → `subCheckTypedV`; new `SubTV` definition;
  new `subCheckTypedV_subTV` theorem.
- `lean/Och/SubCheckVal.lean` (648 LOC): retained as the algorithmic
  engine. No changes (algorithm operates on Val pairs, regardless
  of how soundness is phrased).
- `lean/Och/SoundnessProof.lean` (5828 LOC): mostly retained. The
  `subCheckVal_subV` theorem stays — it's the bridge from algorithm
  to *untyped* SubV. We add a new `subCheckVal_subTV` theorem next
  to it, proven via `subCheckVal_subV` plus `SubV_to_SubTV` (a new
  bridge).
- `lean/Och/Subtyping.lean` (1131 LOC): retained. `Subtype'` is the
  Expr-level relation, used for paper statements and the `quote_realises`
  bridge.
- `lean/Och/TyCheck.lean` (typeCheck, tyInfer, tyCheck): retained at
  Val-level, but a parallel `tyInferTyped` / `tyCheckTyped` is added
  that produces `TypedVal`s and consumes `subCheckTypedV` for
  conversion checks.

### LOC estimates

- Rewrite + augment TypedNbE.lean: **+800 LOC**.
- Add `SubV_to_SubTV` bridge in SoundnessProof.lean: **+150 LOC**.
- Add `subCheckVal_subTV` theorem in SoundnessProof.lean: **+100 LOC**
  (delegation to existing `subCheckVal_subV` + bridge).
- Add typed `tyInferTyped`/`tyCheckTyped` in a new
  `TyCheckTyped.lean` or in TypedNbE.lean: **+400 LOC**.
- The body-substitution lemma (now at Val-level, with RC available):
  **150-250 LOC** (vs 300-500 at Expr-level).

**Total**: ~1500-1800 LOC of new code, retaining all existing 5828 LOC
of SoundnessProof.lean. **Net +25% to the substrate**.

### What we lose

If `subCheckTypedV` is built right, **we lose the "fresh-neutral
discipline" used by `subCheckVal`**. The existing algorithm opens
both closures at the same fresh neutral and compares — that's
soundness via parametricity, not via substitution lemma. The typed
proof has to either (a) prove parametricity formally
(=substitution lemma), or (b) use a different algorithmic structure.

This is the choice point. Pass 6 should pick (a) and pay the
substitution-lemma cost (now at 150-250 LOC at Val-level).

## 5. Concrete recommendation

### Step-by-step plan for follow-on agents

**Pass 6 (this pass)**: lay foundation.
- Define `SubTV` in TypedNbE.lean as the typed analog of SubV.
- Add the **trivial cases** of a `SubV_to_SubTV` bridge: refl,
  hyp (with seen-set context), top, bot_L. These don't need
  body-substitution.
- Prove `RC.subtype_closed` for the trivial SubV cases via
  `SubV_to_SubTV`. This is the design's first deliverable.
- Document remaining work precisely.

**Pass 7**: tackle one closure case via Val-level body-substitution.
- Prove `SubV_to_SubTV` for `lam` (the simplest closure case).
- This requires the body-substitution lemma. Estimated 100-150 LOC.
- Confirm the substitution-lemma is tractable at the Val level.

**Pass 8**: extend to remaining closure cases.
- `iota_struct`, `fix_struct`, `iota_intro`, `unfold_fix_*`,
  `unfold_iota_L`, `revapp_*`, `neutral_ascent`, `stuckRec_struct`.
- Each is a variation on the same body-substitution pattern.
- Estimated 200-300 LOC total.

**Pass 9**: FL body using completed `RC.subtype_closed`.
- `typed_nbe_fundamental_open` body: structural induction on
  `tyCheck`/`tyInfer`. Each case constructs RC witnesses.
- Conversion sites use `RC.subtype_closed` directly.
- Estimated 500-800 LOC.

**Pass 10+**: retire `unshift_head`-dependent code in
SoundnessProof.lean.
- The 4 declaration sorries (`tyCheck_sound_open`, etc.)
  become provable via the typed FL.
- `unshift_head` is no longer needed; can be deleted or left
  documented.

### Pass 6 deliverables (this commit)

1. **Design doc** (this file). ✓
2. **Typed `SubTV` definition** in TypedNbE.lean.
3. **`SubV_to_SubTV` bridge** for trivial cases (refl, hyp, top, bot_L,
   neutral_struct's saturation-only sub-cases).
4. **At least one inline sorry closed** in `subtype_closed_aux` via
   the new bridge.

If all four land, pass 6 has **proven the architecture works** (one
sorry closed via the new mechanism) and the next agent can pick up
the closure cases in pass 7.

### Honest fallback

If pass 6 **doesn't manage to close any inline sorries** via the new
mechanism (because even the trivial cases need infrastructure not yet
in place), the deliverable degrades to:
- Design doc (above).
- `SubTV` definition.
- A scaffold of `SubV_to_SubTV` with each case sorried, *exactly
  matching* `subtype_closed_aux`'s case-split.
- Clear hand-off note: "next agent fills in `SubV_to_SubTV.refl`
  first; that closes one inline sorry in `subtype_closed_aux`."

The fallback is honest progress: it confirms the design and pre-stages
the work. It does NOT inflate sorry count (the sorries in
`SubV_to_SubTV` would be inline analogs of the inline sorries in
`subtype_closed_aux`, traded one-for-one).

## 6. Open questions for next agent

1. **Does `SubTV` need a seen-set?** The classical `SubV` carries one
   for coinductive recursive types. `SubTV` as a logical relation
   doesn't obviously need it (RC's step-index handles fix-unfolding).
   But the *algorithmic* checker uses the seen-set for performance.
   The bridge `SubV_to_SubTV` may need to "discharge" or "absorb" the
   seen-set in some way.

2. **Can `SubTV.lam` be defined recursively at the *same* step `n`?**
   The classical RC's lam case is at step `m ≤ n`. SubTV.lam should
   probably also drop one step. This means the bridge from SubV (no
   step) to SubTV (step-indexed) needs to introduce the step. That's
   doable via `RC.mono` but adds bookkeeping.

3. **What about `SubV.hyp`?** The bridge SubV.hyp → SubTV.hyp requires
   that the seen-set, when interpreted as RC pairs, is closed under
   the RC of values inhabiting both sides. This is the "seen-set
   discharges via strong induction" pattern from
   `subtype_closed_aux`'s pass-4 strong-IH refactor. The bridge
   inherits that infrastructure.

These are non-blocking — the bridge can be defined modulo answers and
filled in case-by-case.

## Appendix: comparison with prior approaches

### Pass 1's RC sketch
RC was untyped except for the type-shape match. Substitution lemma
was identified as needed but un-attempted.

### Pass 4's strong-IH refactor
Made the seen-set hypothesis usable across step-indices. Solid
infrastructure, doesn't address the substitution lemma.

### Pass 5's `RC_env` substrate
Threads typed environments. Useful for the FL body
(open-environment closure cases). Doesn't address substitution.

### This doc
Identifies that the substitution lemma is **intrinsically required**
for any algorithmic bridge from fresh-opened comparisons to all-RC-
arguments. Recommends staging the work: trivial cases first, closure
cases via the body-substitution lemma at the Val level (where it
admits more structure than the Expr-level `unshift_head`).

**Bottom line**: typed-everything is the right architecture; it
*reduces* the substitution lemma's cost and *bypasses*
`unshift_head` in the typed pipeline; but does NOT magically dissolve
the body-substitution work. Multi-pass plan above shows the route.
