# Strengthening Och's soundness: from preservation-only to `progress_mod_fuel`

**Status:** design proposal, not yet implemented.
**Scope:** metatheory only — no change to the declarative subtyping relation, the
typing rules, or the surface language. The goal is to **state and prove** a
property that is currently aspirational in `lean/Och/paper.md §7.1`.

## 1. Motivation

Och's current end-to-end theorem is
[`Och.Soundness.soundness`](../../lean/Och/Soundness.lean#L437):

```lean
theorem soundness {fuel : Nat} {e e' τ : Expr}
    (hfuel : fuel ≤ fuelω)
    (hcle : e.closedAt 0 = true) (hclτ : τ.closedAt 0 = true)
    (hnfe : (nf fuelω e).isSome) (hnfτ : (nf fuelω τ).isSome)
    (hcheck : typeCheck fuel e τ = .ok true)
    (hstep : concEval fuel e = some e') :
    Subtype' [] [] e' τ
```

This is **preservation-only**: it assumes `concEval` produced a value and
concludes the value subtypes `τ`. It says nothing about *whether*
`concEval` produces a value. Looking at the signature
`concEval : Nat → Expr → Option Expr`, a reader might assume `none` means
"out of fuel." In fact [`concEval`](../../lean/Och/Eval.lean#L62) uses `none`
for three distinct outcomes:

1. **Fuel exhaustion** (`fuel = 0`): benign — the programmer retries with
   more fuel.
2. **Free de Bruijn index** (`.bvar _`): genuinely stuck; the evaluator
   expects closed terms and has nothing to do with an unbound variable.
3. **Application of a non-function value** (`.type` applied to an
   argument; and, once `Bot` lands per `docs/ideas/bottom.md`, `Bot`
   applied too): genuinely stuck; the `| _, _ => none` catch-all in
   the `.app` arm fires.

[`paper.md §7.1`](../../lean/Och/paper.md) already diagnoses this:

> `progress_mod_fuel` (aspirational):
> `typeCheck n e τ = ok true ∧ e, τ closed ⟹ ∀ n'. concEval n' e ∈ { some v,
> none-due-to-fuel }` — i.e. the only reason `concEval n' e` returns `none` on
> a typed closed term is fuel exhaustion, never "the evaluator hit an arm it
> couldn't handle."
>
> `soundness` today is a preservation-only theorem … It does not claim
> evaluation runs without stuck arms.

**Why the conflation matters.** A practical programmer looking at the
Och API reads "typeCheck accepts ⟹ safe to evaluate." Under the current
theorem that inference is unjustified: a well-typed `e` whose evaluator
returns `none` could be out of fuel (re-run with more) or permanently
stuck (re-running cannot help). The preservation theorem is **vacuously
true** for both cases — the hypothesis `concEval n e = some e'` is
simply false — so the type system has made no promise that well-typed
programs don't silently fail.

This is the gap we want to close. The hard part is **not** the refactor;
it is working out what the refactor cascades into across
[`Soundness.lean`](../../lean/Och/Soundness.lean),
[`SoundnessProof.lean`](../../lean/Och/SoundnessProof.lean), and the
ten outstanding sorries.

## 2. The proposed refactor

### 2.1 The new evaluation result

Replace `Option Expr` with a three-way result that distinguishes
success, fuel exhaustion, and genuine stuckness:

```lean
inductive StuckReason where
  /-- `concEval` hit `.app f a` where `f` reduced to a value that is not
      a lambda, iota, or fix. Currently: `.type`. Once `Bot` lands: also
      `Bot`. -/
  | appliedToNonLambda (f : Expr) (a : Expr) : StuckReason
  /-- `concEval` encountered `.bvar k` at the top level, which means the
      input term was not closed. -/
  | unboundBvar (k : Nat) : StuckReason
  /-- Escape hatch for future additions that don't fit the above.
      Having it from the start means `progress_mod_fuel`'s statement
      does not need to be rewritten every time a new arm is added;
      only the list of cases the proof must discharge grows. -/
  | other (msg : String) : StuckReason

inductive EvalResult where
  | ok : Expr → EvalResult
  | outOfFuel : EvalResult
  | stuck : StuckReason → EvalResult
```

### 2.2 The rewritten `concEval`

```lean
def concEval (fuel : Nat) (e : Expr) : EvalResult :=
  match fuel with
  | 0 => .outOfFuel
  | fuel + 1 =>
    match e with
    | .bvar k => .stuck (.unboundBvar k)
    | .lam _ _ => .ok e
    | .type    => .ok .type
    | .iota _ _ => .ok e
    | .fix _ _  => .ok e
    | .asc term _ => concEval fuel term
    | .letE val body =>
        match concEval fuel val with
        | .ok v => concEval fuel (body.subst 0 v)
        | r     => r                       -- outOfFuel / stuck propagate
    | .app f a =>
        match concEval fuel f with
        | .outOfFuel => .outOfFuel
        | .stuck r   => .stuck r
        | .ok fVal   =>
          match concEval fuel a with
          | .outOfFuel => .outOfFuel
          | .stuck r   => .stuck r
          | .ok aVal =>
            match fVal with
            | .lam _ body       => concEval fuel (body.subst 0 aVal)
            | .iota ann body    => concEval fuel (.app (body.subst 0 (.iota ann body)) aVal)
            | .fix ann body     => concEval fuel (.app (body.subst 0 (.fix ann body)) aVal)
            | .bvar _ | .asc _ _ | .letE _ _ =>
                -- Impossible by concEval_not_bvar / _not_asc / _not_letE.
                -- We emit `.stuck .other` rather than relying on the
                -- impossibility lemmas here; the cleanest shape is to
                -- keep the arm total and discharge the impossibility
                -- inside `progress_mod_fuel`.
                .stuck (.other "neutral head: bvar/asc/letE")
            | .app _ _ => .ok (.app fVal aVal)  -- neutral spine
            | .type    => .stuck (.appliedToNonLambda .type aVal)
```

Two small design choices here:

- **Why `.stuck` is fatal and the match is total.** With `Option` the
  `| _, _ => none` catch-all did double duty. Making every arm total
  surfaces exactly which shapes can appear; the `.bvar/.asc/.letE`
  arms are *unreachable* on closed inputs — the existing
  [`concEval_not_bvar`](../../lean/Och/Eval.lean#L272),
  `concEval_not_asc`, `concEval_not_letE` lemmas already prove this.
  We re-use those lemmas inside `progress_mod_fuel`'s proof rather
  than inside `concEval` itself, because keeping `concEval`
  dependency-free keeps `native_decide` cheap.
- **`.other` as insurance.** If a future refactor introduces a new
  stuck shape (e.g. a genuine Bot primitive), the statement of
  `progress_mod_fuel` can be left unchanged and only the proof grows a
  case. Without `.other` each addition would need a statement update.

### 2.3 The new theorem statements

Split the single `soundness` into two independent theorems:

```lean
/-- Preservation (same meaning as today, with the sharper type). -/
theorem preservation
    (hcheck : typeCheck n e τ = .ok true)
    (hstep  : concEval n e = .ok e') :
    ∅ ; ∅ ⊢ e' ⊑ τ

/-- Progress modulo fuel: typed closed programs never stuck. -/
theorem progress_mod_fuel
    (hcheck : typeCheck n e τ = .ok true)
    (hcle   : e.closedAt 0 = true)
    (hclτ   : τ.closedAt 0 = true)
    {n' : Nat} :
    ∀ r, concEval n' e = .stuck r → False
```

Equivalently, `progress_mod_fuel` can be stated positively:

```lean
theorem progress_mod_fuel
    (hcheck : typeCheck n e τ = .ok true)
    (hcle : e.closedAt 0 = true) (hclτ : τ.closedAt 0 = true)
    {n'} :
    concEval n' e = .outOfFuel  ∨  ∃ v, concEval n' e = .ok v
```

The negative form is more convenient for proof (every stuck
constructor becomes a `False` goal via `cases` on `StuckReason`); the
positive form is what programmers cite.

The composed `soundness` then means:

```lean
theorem soundness
    (hcheck : typeCheck n e τ = .ok true)
    (hcle : e.closedAt 0 = true) (hclτ : τ.closedAt 0 = true) :
    ∀ n', (∃ v, concEval n' e = .ok v ∧ ∅ ; ∅ ⊢ v ⊑ τ)
        ∨ concEval n' e = .outOfFuel
```

— for every fuel `n'`, the evaluator either produces a declaratively-typed
result or signals fuel exhaustion. **Never** stuck. This is the actual
guarantee a programmer wants from "typeCheck accepts."

## 3. Proof consequences (the hard part)

Breaking this down by file / theorem / sorry.

### 3.1 `Eval.lean` internal lemmas

The following lemmas need signature updates but the proof bodies
survive almost verbatim:

- [`concEval_closedAt`](../../lean/Och/Eval.lean#L103): re-index on
  `concEval n e = .ok v` (was `= some v`). The case-split on the
  `match` in `.app` gets a new arm — `.stuck`/`.outOfFuel` for the
  head / argument — which is a trivial `rcases`. Preserves its
  length (~100 lines).
- [`concEval_fuel_mono`](../../lean/Och/Eval.lean#L219): the
  statement is currently "`some v` survives +1 fuel." The new form
  is "`ok v` survives." A reasonable strengthening worth
  considering at the same time: *fuel monotonicity of the non-bad
  outcome* —

  ```lean
  theorem concEval_fuel_mono_ok : concEval n e = .ok v → concEval (n+1) e = .ok v
  theorem concEval_stuck_stable : concEval n e = .stuck r → concEval (n+1) e = .stuck r
  ```

  The `.stuck` stability is new (under `Option`, stuck and
  out-of-fuel were indistinguishable so monotonicity was vacuous on
  `none`). It says: once you've hit a genuine stuck state, adding
  fuel won't rescue you. This is precisely what lets
  `progress_mod_fuel` range over *all* `n'` from a single check at
  some fixed fuel.

  Proof: the same induction on fuel as the current
  `concEval_fuel_mono`; each arm now has three outcomes but the
  structural recursion is the same.
- [`concEval_not_bvar`](../../lean/Och/Eval.lean#L272),
  `_not_asc`, `_not_letE`: these become part of the
  "never-happen" arguments inside `progress_mod_fuel`. The
  statements are unchanged modulo `some v → ok v`.
- [`concEval_ConcNF`](../../lean/Och/Eval.lean#L378): unchanged
  modulo the renaming.

**Estimated disruption:** ~150 LOC touched, zero proof-level ingenuity
required.

### 3.2 `Soundness.lean` — `concEval_equiv_closed`

The flagship proof here is
[`concEval_equiv_closed`](../../lean/Och/Soundness.lean#L262). Its
hypothesis is `concEval fuel e = some e'`; every single match arm
destructures that hypothesis. Under the refactor, each arm now splits
on `.ok/.stuck/.outOfFuel`; only `.ok` proceeds, so each arm gets an
extra two no-op cases (`.stuck` and `.outOfFuel` directly contradict
the hypothesis of `= .ok _`).

The logical structure is *unchanged* — the `Equiv` / `Subtype'`
derivations are identical once inside the `.ok` branch. Preserving the
proof is mechanical `rcases`/`match` surgery.

Downstream callers —
[`concEval_refines`](../../lean/Och/Soundness.lean#L418),
[`concEval_preservation`](../../lean/Och/Soundness.lean#L428),
[`soundness`](../../lean/Och/Soundness.lean#L437) — are single-line
wrappers; they pick up the new `.ok` pattern at no cost.

**Estimated disruption:** ~200 LOC in `Soundness.lean`, mostly pattern
renames. No new lemmas needed.

### 3.3 `Subtyping.lean`

**Unchanged.** The declarative subtyping relation does not mention
`concEval`. This is by design (§7 of the paper: the declarative world
is `Subtype'`, the algorithmic world is `concEval`/`typeCheck`, and
the soundness arrows cross between them).

### 3.4 `TyCheck.lean`

**Unchanged.** `typeCheck`'s output is an `Except String Bool`; its
internal shape does not refer to `concEval` at all. The only change
would be if we decide to add a kinding pass at the boundary (see §3.7
below); that is an additional design question and can be deferred.

### 3.5 The 10 existing sorries — impact assessment

Per [`PROGRESS.md`](../../PROGRESS.md), the outstanding sorries in
`SoundnessProof.lean` at 2026-04-22 reduce to roughly these categories:

| # | Sorry                                               | Current purpose                                                      | Impact of refactor                                               |
|---|-----------------------------------------------------|----------------------------------------------------------------------|------------------------------------------------------------------|
| 1 | `Equiv.shift` nil-Γ (L788–811)                      | Missing shift lemma; only used in `Equiv.subst_resp`                 | **None** — does not mention `concEval`. Orthogonal.              |
| 2 | `eval_realises` base-conjuncts (L3838/41/42 etc.)   | NbE fundamental lemma closure cases (level/quote witnesses)          | **None** — NbE is about `eval`, not `concEval`. Orthogonal.      |
| 3 | `quoteClosure_realises` (L3597)                     | Consolidated NbE closure-readback sorry                              | **None** — NbE internals. Orthogonal.                            |
| 4 | `SubV_to_Subtype'` binder cases                     | Bridges the Val-level `SubV` relation to `Subtype'`                  | **None** — pre-normalization argument. Orthogonal.               |
| 5 | `tyInfer_sound_open` A9 holes (L5157/58)            | `tyInfer` returns bare annotation for fix/ι — unsound in isolation   | **See §3.6** — this is the A9 question. Mostly orthogonal.       |
| 6 | `tyInfer_sound_open` .lam (L5170)                   | Needs `quote_open_subst` to recover quoted body                      | **None** — pre-normalization. Orthogonal.                        |
| 7 | `tyInfer_sound_open` .app fast-path (L5180)         | Relates `.app (.lam ..) a` via `Subtype'.beta_L`                     | **None** — does not depend on `concEval`. Orthogonal.            |
| 8 | `tyInfer_sound_open` .app let-float (L5186)         | Relates `.app (.letE ..) a` via `Subtype'.letE_L`                    | **None.** Orthogonal.                                            |
| 9 | `tyInfer_sound_open` .app generic (L5192)           | `whnfPi` + codomain recovery                                         | **None.** Orthogonal.                                            |
| 10| Various `by sorry` in push_let/eval_quotes'        | Closedness/quote plumbing                                            | **None** — pre-normalization. Orthogonal.                        |

**The refactor is almost totally orthogonal to the 10 existing
sorries.** Not a single one of them mentions `concEval`; they all
live on the algorithmic-typing side of the diagram in §7 of the
paper. The two worlds meet only at `Subtype'`, which is unchanged.

The one sorry that looks adjacent — A9 — is discussed in §3.6; the
punchline is that `progress_mod_fuel` does **not** transitively
require closing A9.

### 3.6 The A9 question

**Is A9 a prerequisite for `progress_mod_fuel`?** Let me reason
through this carefully.

A9, per `SoundnessAudit.lean` and
[`DECISION-LOG.md 2026-04-22`](../../DECISION-LOG.md#L6): `tyInfer`
on `.fix`/`.iota` returns the *bare annotation* without checking the
body against it. So `tyInfer` on `fix(x:Nat). unit_` claims `Nat`
even though the body is `unit_`. At the algorithm level this is
neutralised because every *soundness-critical consumer* of `tyInfer`
re-verifies via `subCheckVal` or routes through `tyCheck`'s dedicated
`.fix`/`.iota` arm (which calls `subCheckVal (eval e) expected`).

**What `progress_mod_fuel` needs:** starting from
`typeCheck n e τ = .ok true`, show that the `.app` arm of `concEval`
never applies `.type` (or, in future, `.bvar`, `.asc`, `.letE`, or
`Bot`) to an argument. The argument has two legs:

- **Leg A (closedness preserved):** `.bvar`/`.asc`/`.letE` stuck arms
  are unreachable for *any* input `e` that reaches the `.app` head —
  the existing `concEval_not_bvar`/`_asc`/`_letE` lemmas prove this
  irrespective of types. No typing invariant needed; this leg is
  pure operational reasoning and already proven.

- **Leg B (kinding):** `.type`-in-function-position is ruled out by
  the typing discipline. Suppose `.app f a` appears in `e`;
  `typeCheck` accepted. What we need: the value `fVal` that `f`
  reduces to is a `.lam`, `.iota`, `.fix`, or neutral — never
  `.type`. This is where the kinding discipline matters.

For Leg B, notice that `tyCheck` on `.app f a` always routes through
`tyInfer f` (either the β fast-path, the let-float arm, or the
generic `.app` arm), and in every case the algorithm either (i)
matches `.lam dom body` on `f` directly and proceeds with the domain
check, or (ii) runs `whnfPi fuel fV fTy` on the inferred type and
matches `.lam dom cl`. Case (i) *syntactically* rules out `f` being
`.type` (it would be matched against `.lam` and fail). Case (ii) is
where A9 could bite: `whnfPi` works on the *type* of `f`, not `f`
itself, and A9 says `tyInfer` can return a wrong type for fix/ι heads.

**But** for Leg B we need to argue about `f`'s *operational
behaviour*, not about the type `tyInfer` claims for it. The critical
observation:

- `concEval` evaluates `f` structurally: its result is `.lam`,
  `.iota`, `.fix`, `.type`, or a neutral (`.app`) — this is
  `ConcNF`. The only bad case for Leg B is `f ⇓ .type`.
- `.type`'s only reduction path to another term is via `concEval
  .type = .ok .type` (self-evaluating), so `f ⇓ .type` iff every
  reduction of `f` terminates at `.type`.
- For the well-typed program to end with `f` reducing to `.type`, the
  `.app f a` must have been accepted by `tyCheck`. `tyCheck`'s
  `.app` arms all require a Π-head on `f`'s type. `.type` has type
  `.type` (the universe); `whnfPi` on `.type` with inhabitant
  `.type` returns `.type` unchanged (no `.lam` head) — **the `.app`
  arm rejects** (`| _ => .ok none` in `tyInfer`, then fallback
  fails in `subCheckVal`).

So even **without closing A9**, Leg B can be argued from the shape of
`tyCheck` on `.app`: if `typeCheck` accepted, then at every `.app f a`
in the derivation tree, `tyInfer f` returned a type whose `whnfPi`
unfolds to a `.lam` head. That type might be *wrong* (A9) but it is
*shaped* like a function type, which is exactly what Leg B needs.

**More precisely, the progress argument for the `.app` case goes:**

1. Suppose `typeCheck n e τ = .ok true` and `e` contains `.app f a`.
   By structural traversal of `tyCheck`, we know `tyInfer f`
   returned some type `fTy` that `whnfPi` unfolded to `.lam dom cl`.
2. By induction on the subterm `f`, `concEval n' f` terminates at
   some `ConcNF` value `fVal`.
3. We need `fVal` to be `.lam`, `.iota`, `.fix`, or a neutral — in
   particular, not `.type`.
4. Claim: if `fVal = .type`, then `typeCheck` could not have
   accepted `.app f a`. This is where we use the fact that
   `concEval` refines `Subtype'` (the preservation result): if
   `f ⇓ .type`, then `f ⊑ .type` declaratively, and `.app .type a`
   is subtype-rejected by the `[S-Top]` / `[S-App-Cong]` shape
   mismatch.

Step 4 is the only delicate part. It's essentially a shape lemma:
*`Subtype'` admits no derivation concluding `.type ⊑ .lam dom body`*
(the algorithm's `.type` is subtype-maximal; no lambda-headed type
subtypes it in the *reverse* direction). With the `.lam`
congruence, `[S-Top]` going the wrong way doesn't exist.

This is a **shape / canonicity argument**, completely separate from
A9. It holds whether or not A9 is closed.

**Conclusion: A9 is NOT a prerequisite for `progress_mod_fuel`.**
The progress theorem can be stated and proved today modulo A9's
status. A9 concerns `tyInfer`'s *returned type* being wrong; progress
concerns `concEval`'s *operational behaviour* being correct. These
are different questions.

*Caveat.* If Leg B is formalised via a logical relation that
consumes A9-level well-typedness invariants (e.g. "`fV` came from
`eval` on a syntactically-typed subterm, so `fV` has a Π-type shape
at the value level"), then A9 matters. But the most direct route —
routing progress through the existing `concEval_refines`
(`concEval e = .ok e' ⟹ e' ⊑ e` declaratively) and then using
subtype-shape lemmas — sidesteps A9 entirely.

### 3.7 Additional typing-discipline invariants

Even with the refactor, `progress_mod_fuel`'s proof benefits from
making the following invariants explicit:

- **I1** *Every `Γ`-stored type has kind `Type`* — currently **not
  enforced**. `tyCheck`/`tyInfer` evaluate domain annotations without
  checking `A : Type` first ([TyCheck.lean:110–113, 184–186,
  203–204](../../lean/Och/TyCheck.lean#L110)). Paper.md §7.1 calls
  this out:
  > `tyCheck` on `λ(x : A). b` evaluates `A` before checking that
  > `A : Type`.
  Without I1, a pathological input like
  `λ(x : some_non_type). x` type-checks (since `subCheckVal` only
  compares against the expected type, which could be anything).
  Strengthening to enforce I1 is a **precondition** for progress in
  the strict sense. Without it, progress still holds but relies on
  the shape-canonicity argument of §3.6 rather than a clean
  kinding-based induction.

- **I2** *`whnfPi` never produces `.type` or `.bvar` at the head.* —
  derivable from (I1). If every stored type has kind `Type`, then
  `whnfPi`'s output is either a `.lam`-headed Π, or a stuck recursive
  (`.iota`/`.fix`), or a neutral. Never `.type`. This makes the `.app`
  arm's progress proof a direct case-analysis on `whnfPi`'s result.

- **I3** *`concEval` never produces `.bvar`, `.asc`, `.letE` on
  closed input.* — already proven
  (`concEval_not_bvar`/`_asc`/`_letE`). Re-used unchanged.

- **I4** *Subtype' admits no derivation `.type ⊑ .lam …`*. This is
  a statement about the declarative relation; it follows from the
  absence of a `[S-Type-L]` rule. Formalising it requires an
  induction on `Subtype'` derivations; straightforward but
  previously unneeded.

**What the refactor forces**: I3. Everything else is optional — but
without I1+I2, progress's proof for `.app` must go via (I4) plus
preservation plus shape, which is longer but doable.

### 3.8 What induction does `progress_mod_fuel` use?

`concEval`'s induction principle is **lexicographic on (fuel, term
size)**, but actually only fuel appears as the termination measure in
the Lean definition (`match fuel with | 0 => … | fuel + 1 => match e
with …`). So naively, `progress_mod_fuel`'s proof does fuel
induction with inner case-analysis on `e`.

However, **fuel induction alone is not enough.** Consider the `.app`
arm: we recurse on `f`, then on `a`, then on the substituted body
`body.subst 0 aVal`. The body's size is unrelated to `f`'s size;
fuel induction covers this (`concEval fuel` recurses with `fuel` —
same fuel — and the termination of the Lean definition uses
structural recursion via the fact that each sub-call passes a smaller
term *or* the same fuel-index decrement).

Actually re-reading `concEval`: every recursive call passes `fuel` as
the decrement. So the proof is pure **fuel induction**:

```lean
theorem progress_mod_fuel
    (hcheck : typeCheck n e τ = .ok true)
    (hcle : e.closedAt 0 = true)
    (hclτ : τ.closedAt 0 = true) :
    ∀ n' r, concEval n' e = .stuck r → False := by
  intro n'
  induction n' generalizing e τ n with
  | zero => intros r h; simp [concEval] at h  -- .outOfFuel, not .stuck
  | succ k ih =>
    cases e with
    | bvar _ =>
        -- closedAt 0 ⟹ bvar case impossible.
        simp [Expr.closedAt] at hcle
    | type | lam | iota | fix =>
        -- .ok arm fires; no .stuck.
        intros r h; simp [concEval] at h
    | asc t _ =>
        -- unfolds to ih on t.
        ...
    | letE val body =>
        -- case-split on concEval fuel val.
        ...
    | app f a =>
        -- THE interesting case. See §3.6 Leg A + Leg B.
        ...
```

The `.app` case is the heart of the proof. Its structure:

1. Case-split on `concEval k f`:
   - `.stuck r`: IH on `f` (which must be well-typed since `.app f a`
     was well-typed) — `False`.
   - `.outOfFuel`: the whole `concEval` returns `.outOfFuel`, not
     `.stuck` — contradiction with the hypothesis.
   - `.ok fVal`: continue.
2. Symmetric case-split on `concEval k a`.
3. Case-split on `fVal`:
   - `.lam`, `.iota`, `.fix`: the β/iota/fix unfold arms; recurse via
     IH on the substituted body (which is well-typed at the codomain
     by the preservation direction).
   - `.app _ _` (neutral): the `.ok (.app fVal aVal)` arm fires; no
     `.stuck`.
   - `.type`: **forbidden by the shape-canonicity argument of §3.6
     Leg B**. This is the only arm that requires a typing-level
     contradiction.
   - `.bvar`, `.asc`, `.letE`: forbidden by `concEval_not_bvar`/
     `_not_asc`/`_not_letE` applied to the `.ok fVal` hypothesis.

The IH steps on β/iota/fix unfolds need `.app (body.subst 0 vVal) aVal`
to be well-typed; this is the preservation direction applied
pointwise. So `preservation` and `progress_mod_fuel` are most
naturally proved **together as a mutual induction**, not as two
independent theorems. This is the standard "progress + preservation"
mutual in textbook treatments, with the twist that Och's `Subtype'`
is pre-normalized (carries β, let, asc conversion rules) so the
"after one step the type is preserved" half is already
[`concEval_preservation`](../../lean/Och/Soundness.lean#L428).

**Practical consequence.** The cleanest formalization is:

```lean
theorem progress_and_preservation
    (hcheck : typeCheck n e τ = .ok true)
    (hcle : e.closedAt 0 = true) (hclτ : τ.closedAt 0 = true) :
    (∀ n' r, concEval n' e = .stuck r → False)
    ∧ (∀ n' e', concEval n' e = .ok e' → Subtype' [] [] e' τ)
```

with the existing `concEval_preservation` providing the second
conjunct and the new work focused on the first.

## 4. Migration plan

Ordered steps with dependencies noted:

1. **Define `EvalResult` + `StuckReason`** (in `Eval.lean` or a new
   `EvalResult.lean`). Add `DecidableEq`, `BEq`, `Repr` instances
   (mirroring the current `Except` instances at L36–52).
   *Dependencies:* none.

2. **Rewrite `concEval`** to return `EvalResult`. Update the `.app`
   match to be total (no `_, _` catch-all).
   *Dependencies:* step 1.

3. **Port internal lemmas in `Eval.lean`**:
   `concEval_closedAt`, `concEval_fuel_mono`, `concEval_not_bvar`,
   `_not_asc`, `_not_letE`, `concEval_ConcNF`. Add the new
   `concEval_stuck_stable` (fuel-mono for `.stuck`).
   *Dependencies:* step 2.

4. **Port `Soundness.lean`**: `concEval_equiv_closed`,
   `concEval_refines`, `concEval_preservation`. These are mechanical
   pattern renames.
   *Dependencies:* step 3.

5. **State `progress_mod_fuel`** (as a target theorem with `sorry`,
   so downstream reasoning and `#print axioms` can inspect it).
   *Dependencies:* step 4.

6. **Prove `progress_mod_fuel`** via the mutual recursion with
   `concEval_preservation`:
   - 6a. Base cases (`.type`, `.lam`, `.iota`, `.fix`): trivial.
   - 6b. `.bvar`: closedness rules it out.
   - 6c. `.asc`, `.letE`: IH on the subterm.
   - 6d. `.app`: the hard case. Requires the shape-canonicity
     lemma (I4) plus existing `ConcNF` infrastructure.
   *Dependencies:* step 5, plus (I4) as a new lemma in
   `Subtyping.lean` or `SoundnessProof.lean`.

7. **Wire the new `soundness`** that composes
   `progress_mod_fuel` and `concEval_preservation` into the "either
   well-typed value or fuel exhaustion" form.
   *Dependencies:* step 6.

8. **Update `paper.md §7.1`**: remove the "aspirational" caveat;
   update the "What holds and what doesn't" table; note the
   remaining `sorry` status (still tied to the existing 10, via
   `typeCheck_sound`'s dependency on the SubV bridge).
   *Dependencies:* step 7.

### 4.1 Dependencies on the A9 hole

Per §3.6, **none of steps 1–7 require closing A9.** Step 6d's
shape-canonicity argument goes through the preservation direction
(already proven, modulo the existing 10 sorries, none of which are
A9-specific) and a new shape-canonicity lemma on `Subtype'`.

The A9 hole lives entirely in `tyInfer_sound_open`'s `.fix`/`.iota`
arms; the progress argument does not traverse `tyInfer_sound_open` on
those shapes (it goes through `tyCheck_sound_open`, which for
`.fix`/`.iota` routes through `subCheckVal` directly — the "A9 is
resolved" path in the DECISION-LOG).

### 4.2 Dependencies on the existing 10 sorries

The composed `soundness` still transitively depends on `typeCheck_sound`,
which has `sorryAx` (via the SubV/SubN/SynthN bridges, per PROGRESS.md
at 2026-04-21). `progress_mod_fuel` itself does **not** need
`typeCheck_sound` in full generality — it needs only weaker invariants
extractable from "`typeCheck` accepted" (specifically, every `.app f a`
has a Π-shape type for `f`). This is actually a *pure syntactic
invariant* of the `tyCheck` function — provable by structural induction
on `e` and case-analysis on the algorithm, with no reference to
`Subtype'`. So `progress_mod_fuel` can be sorry-clean even while
`typeCheck_sound` is not.

Concretely, define:

```lean
/-- The syntactic obligation discharged by tyCheck. If tyCheck
    accepts `.app f a`, then `tyInfer f` returned a type whose whnfPi
    unfolds to a `.lam`-headed value, and the argument was accepted
    against that domain. Derivable by case-analysis on `tyCheck`. -/
theorem tyCheck_app_exposes_pi
    (h : tyCheck n Γ ρ (.app f a) τV = .ok true) :
    ∃ dom cl, (exists fTy, tyInfer n Γ ρ f = .ok (some fTy) ∧
               whnfPi n (some fV) fTy = some (.lam dom cl))
            ∨ …  -- β fast-path / let-float
```

This is **proof-engineering orthogonal to the 10 sorries**. It is
pure algorithm-reflection, similar to `subCheckVal_subV`'s guard
arms.

## 5. Out of scope

- **Closing A9.** Per §3.6 and the 2026-04-22 DECISION-LOG entry, A9
  is a separate concern. The refactor does not close it; neither
  does it require closing it.
- **Changing the declarative subtyping relation `Subtype'`.** One
  new lemma (I4: no `.type ⊑ .lam` derivation) is required, but the
  relation itself is unchanged. We use the same `Subtype'` from
  [`Subtyping.lean`](../../lean/Och/Subtyping.lean#L77).
- **Changing the typing rules.** §§6.1–6.3 of `paper.md` stand as
  written. The kinding discipline (I1) would be a separate
  strengthening; we discuss it in §3.7 but do not propose it as part
  of this refactor.
- **Adding new features.** `Bot` (per `docs/ideas/bottom.md`) is
  deliberately out of scope; when it lands, it will add one
  `StuckReason` arm (`appliedToBot`) which slots into the
  `.appliedToNonLambda` case or, if desired, gets its own
  constructor. The `StuckReason.other` escape hatch makes this a
  non-event for the statement of `progress_mod_fuel`.
- **Proving termination.** §7.1 is explicit: Och does not aim to
  prove termination. This refactor is strictly about progress, not
  totality.
- **Closing the remaining 10 sorries in `SoundnessProof.lean`.**
  Orthogonal per §3.5.

## 6. Risks and honest caveats

### 6.1 Where the refactor could bite

- **`native_decide` performance.** `concEval` is the workhorse for
  `Tests.lean` and `Std/` evaluations via `#reduce` / `by
  native_decide`. Changing the return type forces Lean to
  re-elaborate all those sites. In principle the new `EvalResult`
  has the same cardinality of branches as `Option`; in practice
  `native_decide` is sensitive to inductive-type layout. Expect a
  CI round of fixing `by native_decide` tests that break because
  the pattern `= some v` no longer matches; replace with `= .ok v`.

  **Mitigation:** provide a convenience function
  `EvalResult.toOption : EvalResult → Option Expr` that drops the
  distinction (for test sites that don't care); add `instance :
  Coe EvalResult (Option Expr)`. Keeps old test sites working.

- **Existing `concEval_equiv_closed` proof** (211 lines, eight
  head-shape cases). Each case destructures `hstep : concEval … =
  some e'` and derives an `Equiv`. Adding three new arms per case
  (one each for `.outOfFuel`, `.stuck`, the catch-all) is
  mechanically straightforward but tedious. Budget: ~2 days of
  careful find-and-replace. No proof-level ingenuity at risk.

### 6.2 Stuck states we haven't enumerated

The `StuckReason.other` escape hatch is insurance against this, but
worth enumerating what we currently know can go wrong:

- `.app .type a` — known.
- `.app (.bvar k) a` — unreachable on closed input
  (`concEval_not_bvar`); we emit `.stuck .other` as a defensive
  measure.
- `.app (.asc ..) a`, `.app (.letE ..) a` — unreachable
  (`concEval_not_asc`/`_letE`); same.
- `.bvar _` at top level — unreachable on closed input
  (`closedAt 0`).
- **Not-yet-existing:** `.app Bot a` — will exist once `Bot` lands;
  gets its own `StuckReason.appliedToNonLambda` arm (or a dedicated
  `appliedToBot` arm, TBD).
- **Not-yet-existing:** hypothetical `Expr.prop`, `Expr.literal`,
  etc. from future extensions.

The escape hatch ensures the **statement** of `progress_mod_fuel`
(`concEval n' e = .stuck r → False`) holds regardless of how many
new shapes are added, so long as none of them are reachable for
well-typed closed inputs.

### 6.3 Does the refactor re-open closed proofs?

Main risk: the 10 existing sorries in `SoundnessProof.lean`. As
analyzed in §3.5, they are orthogonal — they concern the algorithmic
typing side (`tyCheck_sound_open`, `SubV_to_Subtype'`, etc.) and
touch neither `concEval` nor the theorems that reference it. So the
refactor does not re-open any of them.

One secondary concern: **axiom hygiene**. The `concEval`-chain
(`concEval_refines`, `concEval_preservation`, `concEval_equiv_closed`)
is currently axiom-clean (`propext`, `Quot.sound` only — PROGRESS.md
at 2026-04-21 records this as a "MAJOR BREAKTHROUGH"). Moving to
the new `EvalResult` must preserve this. The risk is that a
careless `rcases` on `EvalResult` could pull in `Classical.choice`
or similar. Solution: prefer `match` over `rcases` for case-analysis
on `EvalResult` (it is computable), and verify with `#print axioms`
at each migration step.

### 6.4 Blowup in proof size

Rough estimate of proof-size impact:

- `concEval_equiv_closed`: ~220 lines → ~260 lines (three extra
  no-op cases per of 8 head shapes; call it +40).
- `concEval_closedAt`: ~120 lines → ~140 lines (same reasoning).
- `concEval_fuel_mono`: ~45 lines → ~55 lines.
- `concEval_not_bvar` + `_not_asc` + `_not_letE`: ~30 lines each
  → essentially unchanged.
- `concEval_ConcNF`: ~35 lines → ~40 lines.
- **New: `concEval_stuck_stable`**: ~45 lines.
- **New: `progress_mod_fuel`**: estimated 250–400 lines. The main
  work is in the `.app` case's shape-canonicity argument (~150
  lines), the IH plumbing for preservation-in-parallel (~80
  lines), and the I4 lemma on `Subtype'` (~50 lines).
- **New: `tyCheck_app_exposes_pi`** (syntactic reflection of the
  `.app` arm): ~100 lines.

**Rough total:** +500–700 lines of new proof, +100 lines of
mechanical adjustments. Well within the budget of a 2–3 week task
for one agent.

### 6.5 What could still go wrong

The shape-canonicity argument (I4) relies on `Subtype'` not admitting
`.type ⊑ .lam dom body`. Let me sanity-check this by eyeballing the
constructors of [`Subtype'`](../../lean/Och/Subtyping.lean#L77):

- `refl e`: needs `.type = .lam dom body` — impossible.
- `top e`: concludes `e ⊑ .type`, not `.type ⊑ _`.
- `trans a → b → c`: would need an intermediate `.type ⊑ b ⊑ .lam
  dom body`. Inductive: if neither sub-proof proves a shape like
  `.type ⊑ .lam …` and the relation composes only such forbidden
  shapes, then the composition is also forbidden. Careful, though
  — `trans` could go via a `.fix`/`.iota` fixpoint, and those admit
  unfolds. Need to check: does any unfold rule produce a `.lam`
  head? `unfold_iota_L`: `.iota ann body ⊑ c` from `body.subst 0
  (.iota …) ⊑ c`. If `body` is `.lam …`, then `body.subst …` is
  `.lam …`, and we'd need `.type ⊑ .lam …` on the RHS from some
  prior step. Circular — the induction closes.
- `bvar`, `lam`, `app_cong`, `iota_body`, `fix_body`,
  `iota_cong`, `fix_cong`, `letE_cong`, `iota_intro`,
  `unfold_iota_L/R`, `unfold_fix_L/R`: each fixes a head constructor
  on at least one side; case-analysis rules them out.
- `beta_L/R`, `letE_L/R`, `asc_L/R`: conversion rules; the head
  after reduction determines the goal. Possible landmines — e.g.
  `beta_R: a ⊑ body.subst 0 arg` concludes with `.app (.lam …) arg`
  on the right; if `a = .type` and `body.subst = .lam …`, this
  derives `.type ⊑ .lam …`. Hmm. But **preservation** tells us
  `body.subst 0 arg = .lam …` as a raw term doesn't appear after a
  `.type` head; we'd need the earlier stage to derive it. Inductive
  closure on depth.

So I4 is **probably true but not trivial**. Worth formalising as a
separate lemma with its own careful induction. Budget ~50 LOC as
estimated.

**The risk:** I4 turns out to be harder than expected, or actually
false in some corner case (e.g. some conversion rule admits a `.type
⊑ .lam …` derivation through a pathological term we haven't
considered). Fallback: restrict I4 to *closed* terms, or add a kinding
hypothesis.

### 6.6 Dependence on `Bot` landing

If `Bot` is added during or before this refactor, we need one more
`StuckReason` arm plus one more `.app` case (`Bot · a → .stuck
(.appliedToBot)`). The shape-canonicity argument (I4) extends to
`Bot`: the subtyping rule for `Bot` in `docs/ideas/bottom.md` is
`Bot ⊑ _` (bottom is the least element), not `_ ⊑ .lam …`. So
`.app Bot a` is rejected by `tyCheck`'s `.app` arm (the Π-head check
fails). No additional work for progress beyond adding the arm.

## 7. Summary

- The refactor (swap `Option Expr` → `EvalResult`) is mechanical and
  touches ~500 LOC across `Eval.lean` and `Soundness.lean`.
- The new theorem `progress_mod_fuel` costs an additional ~250–400
  LOC of proof, centered on the `.app` case and a new shape
  lemma I4.
- **Orthogonal to the 10 existing sorries** in `SoundnessProof.lean`;
  none of them mention `concEval`.
- **Orthogonal to the A9 hole.** Progress goes through operational
  + shape-canonicity reasoning, not through `tyInfer`'s claimed
  types.
- **Axiom hygiene preserved.** The `concEval`-chain is currently
  axiom-clean; careful use of `match`/`cases` preserves that.
- **Main risks:** I4 being harder than estimated, test-site
  migration, and `native_decide` performance regressions. All
  mitigable.

Once `progress_mod_fuel` is proved, `paper.md §7.1`'s aspirational
row in the "What holds and what doesn't" table becomes
machine-checked, and `soundness` upgrades from a preservation-only
promise to the actual programmer contract the type system aims to
provide.
