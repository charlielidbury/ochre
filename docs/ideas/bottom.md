# Native `Bot`: a primitive bottom type

## Motivation

Och has `Type` as a primitive top with the subtyping rule
`_ ⊑ Type ⇒ true`. It does **not** have a primitive bottom. Without
one, any "bottom" is encoded as a term, and structural subtyping on
encodings collides with other terms that happen to share the same
shape.

The concrete case is `Std/Fin.lean`. With the singleton-encoded Scott
numerals in `Std/Nat.lean` (each numeral's `s`-domain is the
predecessor value), `Fin n` subtyping becomes expressible —
`Fin n ⊑ Nat`, `Fin m ⊑ Fin n` for `m ≤ n`, specific numerals flowing
in and out — but the `Fin zero` branch needs a "bottom" type. The
current encoding is

```lean
def Bot := och{ fix B. λX:Type. λz:X. λs:(B → X). s B }
```

This works — the full truth table is correct — but it's fragile. The
body `s B` was tuned to structurally differ from `zero_`; an earlier
version with body `z` caused `zero_ ⊑ Bot` to close (structural
collision with the singleton `zero_`) and cascaded into the
`n_ ⊑ Fin n_` diagonal passing wrongly. Future changes to Scott
numerals or to the subtype algorithm could re-introduce the collision
elsewhere. Hack, not a primitive.

Research: every mainstream type system with subtyping (DOT, Scala 3,
TypeScript, Kotlin, Ceylon) makes bottom primitive. Cedille avoids
the question by having no subtyping. Systems with Scott encodings
*plus* subtyping are essentially unexplored — we're the first case,
and the collision we hit is the predictable one. Primitive Bot
aligns Och with the DOT consensus: one constructor, one subtyping
rule, no structural entanglement.

## Proposal at a glance

Add `Expr.bot` as a term constructor with these properties:

1. **Syntax.** `Bot` as a keyword in `och{…}`. Parses to `Expr.bot`.

2. **Evaluation.** A new `Val.bot`, self-evaluating (like `Val.type`).
   **Application onto Bot is stuck** — no vapp rule matches, so
   `concEval (Bot a) = none`, parallel to `concEval (Type a) = none`.

3. **Subtyping — one new declarative rule:**

   ```
   [S-BotL]
   S ; Γ ⊢ Bot ⊑ e
   ```

   Algorithmically: one match arm in `subCheckVal`:

   ```lean
   | .bot, _ => .ok true
   ```

   No companion `_, .bot => .ok false` arm. Rejection emerges from
   fall-through, matching the declarative "positive rules only"
   style. For structural matching concerns, see the existing
   `.type` treatment below.

4. **Typing restriction — bidirectional mode as a proxy for
   term/type distinction.** Bot can only appear in positions where
   the checker is asking "is this a type?" — specifically:

   - `tyInfer .bot` fails. Bot does not synthesise a type.
   - `tyCheck .bot τ` succeeds **only when `τ = Val.type`** — i.e.,
     Bot is acceptable when the surrounding context is already asking
     for a type-level expression.

   This piggybacks on Och's existing bidirectional mode without
   introducing a separate term/type stratum. See
   [Bidirectional mode as proxy](#bidirectional-mode-as-proxy) for
   how this translates to type-in-type semantics and where the proxy
   leaks.

5. **No introduction form for Bot**, and no separate elimination
   form. Bot values can't be constructed; subsumption via `[S-BotL]`
   gives ex-falso directly (DOT-style, not Coq-style).

## Bidirectional mode as proxy

Och doesn't syntactically distinguish types from terms; both are
`Expr`. The bidirectional type checker has two operational modes:

- **Synthesis** (`tyInfer`): given a term, produce its type.
- **Checking** (`tyCheck`): given a term and an expected type,
  produce a boolean.

The proxy we use: **checking at `Val.type` ≈ "used as a type,"
checking at anything else ≈ "used as a value."**

The restriction `tyInfer .bot = error, tyCheck .bot τ = ok true iff
τ = Val.type` exploits this proxy. It does not create a new
term/type separation — it uses the mode the checker already
maintains.

**Where the proxy leaks**: in type-in-type, `(λX:Type. X) Bot`
evaluates to `Val.bot` at type `Type` — Bot-as-value living at
type-Type. This is benign because:

- Val.bot at type Type cannot be further ascribed at a non-Type
  type (tyCheck rejects at the ascription's fallback).
- Val.bot at type Type cannot be passed to a non-Type-expecting
  function (tyCheck rejects the argument-against-domain check).
- Val.bot at type Type can be used as an annotation elsewhere
  (e.g., `λy:(thing-evaluating-to-Bot). body`), but that's just
  "writing `λy:Bot. body`" via indirection, and it's fine.

What this rules out: Val.bot ever flowing into a value position at
a specific non-Type type. This is the invariant that matters for
runtime safety — it is stated below as a soundness obligation.

## Application onto Bot is stuck

Matching the existing treatment of `Type`: there's no vapp rule for
`.bot` in function position, so `vapp .bot a = none`, and
`concEval (Bot a) = none`. Attempting to apply Bot causes evaluation
to give up.

This is intentional. Applying an argument to a type makes no sense;
Bot is a type, so it's not applicable. Reading "Bot ⊑ everything" as
a *static* subtyping fact (which is what DOT / Rust `!` / Scala
Nothing do) rather than as a runtime reduction rule is the
semantically correct design.

**An earlier draft of this spec proposed `vapp .bot a = some .bot`
("Bot absorbs"). That was wrong.** Other languages don't have such
a rule — they ensure Bot is uninhabited at runtime, and the question
of "what does it mean to apply a Bot value" doesn't arise. The
absorbing rule was a runtime hack to paper over the real issue:
under the existing preservation-only soundness, absorbing hides
stuckness inside a formally-valid value, which is wrong in spirit
even when technically preservation-consistent. The correct approach
is to leave Bot-application unhandled (stuck) and rely on the
typing discipline to ensure well-typed programs never reach that
state.

## Soundness: Phase 1 and Phase 2

Soundness here has two levels, and this proposal is scoped to
Phase 1. Phase 2 is acknowledged but deferred.

### Phase 1 (this proposal): preservation-preserving addition

Paper.md §7's `soundness` theorem is preservation-only:

> `typeCheck n e τ = ok true ∧ concEval n e = some e' ⟹ ∅ ; ∅ ⊢ e' ⊑ τ`

Under this theorem, Bot-application's stuckness (returning `none`)
makes the hypothesis `concEval n e = some e'` false, so the theorem
is **vacuously satisfied**. That is: adding Bot as specified here
doesn't weaken or break the existing soundness.

Proof obligations for Phase 1:

1. **Extension of `Subtype'` with `[S-BotL]`.** One constructor.
2. **Extension of `SubV`**, matching `[S-BotL]`. Trivial.
3. **Soundness of the new algorithm arm**:
   `subCheckVal (.bot) v = ok true → Subtype' .bot v`. Proof:
   `exact .bot_L`.
4. **Extension of `eval_realises`** and kin with the `.bot` case.
   `.bot` is self-evaluating, self-quoting, refl under every
   structural predicate.
5. **Extension of `whnfPi`** with `.bot => none`. `.bot` is not
   a Π-head.
6. **No re-opening of existing sorries.** All 10 existing sorries
   remain open for their own reasons; adding Bot adds one trivial
   case to each without changing the structural argument.

Everything is mechanical.

### Phase 2 (separate follow-up): progress-mod-fuel

The stronger guarantee programmers actually want is:

> `typeCheck n e τ = ok true ⟹ concEval n e is *either* a
> well-typed value *or* out of fuel — never silently stuck`.

This is paper.md §7.1's `progress_mod_fuel`, which is noted as "not
stated, not proven." The obstacle is structural: `concEval` currently
returns `Option Expr`, conflating fuel exhaustion with stuckness
(applying to Type, applying to Bot, stumbling on a free variable).
Distinguishing these requires refactoring `concEval`'s return type,
restating the theorem, and re-doing the surrounding proofs.

See `docs/ideas/soundness-strengthen.md` for the separate proposal
on this refactor. It is NOT part of Phase 1.

**What Phase 1 doesn't claim**: Phase 1 adds Bot as a first-class
primitive and extends the existing preservation story to cover it.
It does NOT claim that well-typed programs cannot stuck on
Bot-application at runtime (a progress-style claim). Under the
bidirectional restriction, such stuckness should not happen in
practice for any program that doesn't deliberately exploit A9 —
but a formal no-stuckness theorem requires Phase 2's refactor.

## Concrete implementation checklist

### `lean/Och/Syntax.lean`

- Add `| bot : Expr` constructor.
- `pretty`: `.bot => "Bot"`.
- `bvarBound`, `shift`, `subst`, and any other structural traversal:
  `.bot => …` case (closed constructor, no subterms).
- `DecidableEq`/`Inhabited` derivations auto-extend.

### `lean/Och/Macro.lean`

- Add `Bot` as a keyword in `och{…}`, parsing to `Expr.bot`. Same
  shape as the existing `Type` keyword.

### `lean/Och/Eval.lean` (concEval)

- `Expr.bot ⇓ Expr.bot` (self-evaluating, parallel to `Expr.type`).
- **No `E-App-Bot` rule.** Application onto `Expr.bot` has no rule,
  so `concEval (Bot a) = none` — stuck, same as `concEval (Type a)`.

### `lean/Och/NbE.lean`

- Add `| bot : Val` to `inductive Val`.
- `eval`: `| .bot => some .bot`.
- **`vapp` has no arm for `.bot` in function position.** Parallel
  to `.type`. If exhaustiveness requires it, add `| .bot, _ => none`.
- `quote`: `| .bot => some .bot`.
- `bvarBound`, `Val.isNeutral`, `Val.beq`, `Val.beqFast`, and the
  `Val.beq_eq` / `beq_refl` theorems: add the `.bot` case.

### `lean/Och/SubCheckVal.lean`

- Add one arm:

  ```lean
  | .bot, _ => .ok true
  ```

  placed at high priority — before fix/ι/stuckRec/neutral arms. If
  exhaustiveness requires one, add a single catch-all
  `_, _ => .ok false` at the end. Do not add per-shape `_, .bot`
  rejection arms.

- Update `subCheckVal_subV` proof to handle the new arm.

### `lean/Och/TyCheck.lean`

- `tyInfer`: `| .bot => .error "Bot has no synthesized type; use as annotation"`.
- `tyCheck`: add a special case matching `.bot` expression against
  `Val.type` expected type, returning `.ok true`. Other cases
  fall through to the existing fallback (which will reject via the
  errored `tyInfer`).
- `whnfPi`: add `.bot => none` case.

### `lean/Och/Subtyping.lean` (declarative relation)

- Add `| bot_L : Subtype' s Γ .bot e` constructor.
- Update inversion lemmas / structural traversals for the new case.

### `lean/Och/Soundness.lean` / `SoundnessProof.lean`

- Extend `SubV` with the matching constructor, `SubV_to_Subtype'`
  with the case (trivial).
- `eval_realises`: `.bot` case — self-evaluating, realiser satisfies
  trivially.
- `openNf_holds` and related normalization: `.bot` is self-NF.
- `whnfPi_sound`: `.bot => none` is trivially sound (no claim when
  result is `none`).

### `lean/Och/paper.md`

Paper updates are part of this change.

- **§1 (Syntax).** Add `Bot` to the term grammar beside `Type`.
- **§2 (Concrete semantics).** Note that `Bot` is a value (like
  `Type`), self-evaluating. Application onto `Bot` has no reduction
  rule — stuck, parallel to `Type`. Users should read this as a
  soundness discharge: the typing discipline must ensure well-typed
  programs don't reach it.
- **§3 (Declarative subtyping), §3.1.** Add `[S-BotL]` below
  `[S-Top]`. Update the taxonomy table's Structural row.
- **§3 note**: subsumption via `[S-BotL]` gives ex-falso directly;
  no dedicated absurd eliminator exists (worth mentioning for
  readers expecting Coq-style elimination).
- **§5 (Algorithmic subtyping).** Describe the `.bot` arm. Contrast
  with `.type`: both primitive lattice extrema.
- **§6 (Algorithmic typing).** Describe `tyInfer .bot = error` and
  `tyCheck .bot Type = ok true`. Explain the bidirectional-mode
  proxy for "Bot is a type, not a value."
- **§7 (Metatheory).** Note Phase 1 vs Phase 2 (with reference to
  soundness-strengthen.md for Phase 2).

### Tests in `lean/Och/Std/Fin.lean`

1. Replace the definable `Bot`:

   ```lean
   def Bot := och{ fix B. λX:Type. λz:X. λs:(B → X). s B }
   ```

   with `def Bot := och{ Bot }` using the primitive keyword.

2. Re-run the existing test battery. All these should still hold:

   ```
   YES: two_ ⊑ Nat
   YES: two_ ⊑ Fin four_
   NO:  two_ ⊑ Fin one_
   YES: Fin three_ ⊑ Nat
   NO:  Nat ⊑ Fin three_
   NO:  one_ ⊑ Fin zero_
   NO:  zero_ ⊑ Fin zero_
   NO:  one_  ⊑ Fin one_
   NO:  two_  ⊑ Fin two_
   ```

3. Add a dedicated Bot test block:

   ```lean
   -- Bot ⊑ everything (S-BotL)
   example : NbE.subCheck 200 Bot Nat_                   = .ok true
   example : NbE.subCheck 200 Bot Std.Bool               = .ok true
   example : NbE.subCheck 200 Bot (och{ Fin three_ })    = .ok true
   example : NbE.subCheck 200 Bot Expr.type              = .ok true
   -- Refl
   example : NbE.subCheck 200 Bot Bot                    = .ok true
   -- Only Bot ⊑ Bot on the RHS
   example : NbE.subCheck 200 Nat_   Bot                 = .ok false
   example : NbE.subCheck 200 zero_  Bot                 = .ok false
   example : NbE.subCheck 200 Expr.type Bot              = .ok false
   ```

4. Add stuckness test for Bot-application (parallel to Type):

   ```lean
   -- Applying an argument to Bot is stuck, just like Type
   example : concEval 200 (och{ Bot zero_ }) = none       -- stuck
   example : concEval 200 (och{ Type zero_ }) = none      -- stuck (existing)
   ```

5. Bidirectional restriction tests:

   ```lean
   -- tyInfer rejects Bot as a value
   example : NbE.tyInfer 200 #[] [] (och{ Bot }) |>.isOk
           = false   -- modulo the "via annotation" path

   -- tyCheck accepts Bot at type Type
   example : NbE.typeCheck 200 (och{ Bot }) Expr.type = .ok true

   -- tyCheck rejects Bot at a non-Type type
   example : NbE.typeCheck 200 (och{ Bot }) Nat_ = .ok false

   -- The user's problematic scenario is now rejected:
   example : (NbE.typeCheck 200
               (och{ (λT:Type. λx:T. x) Nat_ Bot }) Nat_).isOk
           = false
   ```

## Why Fin.lean is the load-bearing test case

The definable `Bot` + singleton Scott encoding in `Std.Fin` tests
the property the primitive should preserve: `Bot ⊑ X` for every `X`
that appears in the contra chain of `Fin n ⊑ Nat`. If primitive Bot
breaks that, the Fin tests will regress immediately. Conversely, if
the Fin tests all hold, the algorithm has been correctly extended.

## Scope — explicitly not in this proposal

- No change to `zero_`'s or `Nat_`'s encoding. Primitive Bot
  replaces the definable one in `Fin.lean`; `Std.Nat` is untouched.
- No introduction or elimination form for Bot (subsumption already
  provides ex-falso).
- No change to the existing `Type` top treatment.
- No closure of the A9 hole — Bot doesn't make A9 worse and A9's
  closure is orthogonal.
- **No progress_mod_fuel / no concEval refactor.** These are
  Phase 2, covered separately in `soundness-strengthen.md`.

## Deliverables

1. `Expr.bot` constructor with all structural traversals updated.
2. `Val.bot` with eval / vapp (stuck) / quote / beq coverage.
3. `.bot, _ => .ok true` arm in `subCheckVal`.
4. `Bot` keyword in `och{…}`.
5. `tyInfer .bot = error`; `tyCheck .bot Val.type = ok true`;
   `whnfPi .bot = none`.
6. `[S-BotL]` in `Subtype'`; matching constructor in `SubV`; bridge
   updated.
7. `Std/Fin.lean` switched to primitive Bot. All tests still green,
   plus new Bot-specific block and stuckness tests.
8. `paper.md` updated per the list above.
9. Axiom set of `subCheckVal_sound` / `typeCheck_sound` /
   `concEval_equiv` / `soundness` unchanged.

All existing tests in `lean/Och/Std/` continue to pass; no file
outside the listed set should require changes.
