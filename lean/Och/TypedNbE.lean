import Och.NbE
import Och.SubCheckVal
import Och.TyCheck
import Och.SoundnessProof

/-!
# Typed NbE — the architectural substrate

**Status:** scaffold. Pass 1 lands datatype + RC predicate definition
+ fundamental-lemma signature. Bodies are `sorry`'d.

See `docs/ideas/typed-nbe.md` (especially the implementation addendum)
for the architectural motivation. See
`docs/ideas/typed-nbe-implementation-log.md` for the running log.

## What this file provides

1. `TypedVal`: a record bundling a `Val` with its declared semantic
   type. The type is itself a `Val` — types are values in OCH.

2. `RC : Nat → Val → Val → Prop`: step-indexed reducibility candidate.
   `RC n τ v` reads "v is in the reducibility candidate of type τ at
   step-index n". The classical predicate from Tait/Girard/Abel,
   adapted for OCH's `Type:Type` non-stratified setting via step-
   indexing.

3. `tyEval`: a thin wrapper around `eval` that, when supplied with a
   typing precondition, produces a `TypedVal` together with a proof
   that the value is RC at its declared type.

4. `typed_nbe_fundamental` (signature only — body is `sorry`):
   "well-typed expression evaluates to RC of its declared type".

## What this file deliberately does NOT do

- Modify `Val`. The untyped `Val` is keep-stable; `TypedVal` is a
  parallel layer. Rationale: minimise blast radius and preserve the
  ~6000 lines of existing proofs in `SoundnessProof.lean`.

- Replace `subCheckVal`. The typed conversion check `subCheckTyped`
  is a follow-up step — when typed values are available at the
  call sites, switching the algorithm is a separate refactor.

- Prove the fundamental lemma. The body is `sorry`. The *statement*
  matters most for unblocking the four declaration-level sorries
  in `SoundnessProof.lean`; future agents fill in the body.

## Step-indexing convention

Following Dreyer-Ahmed-Birkedal "Logical step-indexed logical
relations". `RC n τ v` is monotone-down in `n` (`n ≤ m → RC m → RC n`)
and approximates "v is fully reducible at τ" as `n → ∞`. The
fundamental lemma takes a step-budget `n` aligned with the eval/quote
fuel budgets — well-typed `e` evaluates to a value satisfying `RC n
τV` for the same `n` that drove evaluation.

The classical proof discharges `n` by induction on the type complexity;
in OCH with `fix` and `ι`, the step-index protects against Ω-style
divergence (a `fix x:A. x` value passes `RC 0 _` trivially but not
`RC (n+1) _` unless its body terminates). This is the explicit
step-indexed analogue of the "well-typed implies terminates" theorem
the spec deliberately weakens.
-/

namespace NbE

/-! ## TypedVal

A typed semantic value: a `Val` with its declared type (also a `Val`).

In the classical NbE phrasing, this is `Σ τ. RC τ v`. We split the
data (`val × ty`) from the proof (`RC n ty val`) so the data layer
remains purely computational and the proposition can be carried
separately when needed.
-/

/-- A semantic value paired with its declared semantic type. The type
is itself a `Val` (OCH has type-in-type). -/
structure TypedVal where
  val : Val
  ty  : Val
  deriving Inhabited

/-! ## The reducibility-candidate predicate

`RC n τ v` is defined recursively on `n`, branching on the *exposed
shape* of the type `τ`. The shape exposure is best-effort: if `τ` is
a closure-form (`.lam`/`.iota`/`.fix`) it dictates the reducibility
condition for `v`; if `τ` is a neutral or `.type`, we accept any `v`
(the type is opaque to RC).

The cases:

- `RC 0 _ _ := True` — step-zero: trivially RC. Useful for the IH
  base where we don't yet have any constraint.

- `RC (n+1) .type v := True` — `Type` is the universe; everything
  inhabits it.

- `RC (n+1) .bot v := False` — `Bot` is empty; nothing inhabits it.
  (This excludes diverging values from being typed at `Bot`, which
  is the empty type.)

- `RC (n+1) (.lam dV cl) v` — `v` is at function type. For every
  argument `a` of type `dV` with `RC n dV a`, applying `v` to `a`
  must succeed and produce a value `r` with `RC n (cl.openω a) r`.

- `RC (n+1) (.iota aV cl) v` — `v` is at self-type. Then `v : aV`
  (`RC n aV v`) AND `v : cl[self:=v]` (`RC n (cl.openω v) v`). This
  matches the iotaIntro rule of `Subtype'`.

- `RC (n+1) (.fix _ cl) v` — `v` is at recursive type. Unfold once
  and require `RC n (cl.openω (.fix _ cl)) v`. The unfold
  budget at `n+1` permits one `fix`-unfold.

- `RC (n+1) (.neutral _) _ := True` — neutral types are opaque
  (their content depends on a free variable). RC defers to the
  caller, which will discharge via the neutral's surrounding
  context.

This is *one* possible RC definition. The classical Tait
"reducibility candidates" carry more closure structure (closed
under reduction; closed under variable injection); the spec's
recommendation is to start with the minimal version and lift to
the saturated form (Girard's "neutral terms are reducible") only
when needed by a particular fundamental-lemma case.

Termination: the recursion on `n` is structural (each clause goes
to `n` from `n+1`). The recursion on `τ`'s shape is structural in
the head constructor; we never recurse on `τ`'s sub-`Val` directly
(closure opens are taken at face value, returning a fresh `Val`
that the *next* `n`-step bounds).
-/

/-- Step-indexed reducibility candidate predicate.
`RC n τ v` reads: "v is in the RC of type τ at step-index n".

Defined by recursion on `n` first, then case on `τ`. The `fix` case
is the main subtlety: we unfold once and recurse at smaller `n`,
which is why step-indexing buys us well-foundedness without needing
to inspect the closure body's structure. -/
def RC : Nat → Val → Val → Prop
  | 0, _, _ => True
  | _+1, .type, _ => True
  | _+1, .bot, _ => False
  | n+1, .lam dV cl, v =>
      ∀ a, RC n dV a →
        ∃ r, vapp fuelω unfBound v a = .ok r
           ∧ ∃ rTy, cl.openω a = some rTy ∧ RC n rTy r
  | n+1, .iota aV cl, v =>
      RC n aV v ∧ ∃ vTy, cl.openω v = some vTy ∧ RC n vTy v
  | n+1, .fix annV cl, v =>
      ∃ uTy, cl.openω (.fix annV cl) = some uTy ∧ RC n uTy v
  | _+1, .neutral _, _ => True

/-! ## RC-closure properties

These are the structural lemmas that follow from `RC`'s definition.
Most are straightforward inductions on `n`. We state them and leave
their proof bodies as `sorry` for now — the *statements* are what
matter for the fundamental-lemma sketch. Future agents fill in
proofs.
-/

/-- Step-index downward monotonicity: more fuel → more RC; less fuel
also yields RC (RC weakens). This is the classical "monotone in n" of
step-indexed logical relations. -/
theorem RC.mono {n m : Nat} {τ v : Val} (hle : m ≤ n) (h : RC n τ v) :
    RC m τ v := by
  -- TODO(typed-nbe): proof body. Standard step-indexed induction.
  -- Each case of RC at n+1 weakens to the same case at m+1 with
  -- the IH at m ≤ n.
  sorry

/-- RC is preserved under declarative subtyping (algorithmic SubV
form). The intuition: if `τ ⊑ τ'` and `v` inhabits `RC τ`, then
`v` also inhabits `RC τ'` because every "obligation" of `RC τ'` is
a relaxation of one in `RC τ`. -/
theorem RC.subtype_closed {n : Nat} {τ τ' v : Val}
    (_hsub : SubV [] #[] τ τ')   -- assumes empty seen/Γ for now
    (h : RC n τ v) : RC n τ' v := by
  -- TODO(typed-nbe): proof body. Induction on SubV; each
  -- constructor of SubV maps to the corresponding "weakening" of RC.
  -- The hyp/refl/top cases are immediate; the lam case is
  -- contravariant on the domain (the hypothesis on the new domain
  -- discharges via the old via SubV's contra direction).
  sorry

/-- RC at the universe `.type` is the entire `Val` space. -/
theorem RC.type_top {n : Nat} {v : Val} : RC (n+1) .type v := by
  show True; trivial

/-- RC at `.neutral` is opaque (always holds). The caller discharges
the obligation via the surrounding context. -/
theorem RC.neutral_top {n : Nat} {ne : Neutral} {v : Val} :
    RC (n+1) (.neutral ne) v := by
  show True; trivial

/-- A concrete construction useful for `eval`'s `.lam` case: if `v`
is itself a lambda, RC at a `.lam` type reduces to checking the body
under the closure. This is provable by case analysis on `vapp`. -/
theorem RC.lam_intro {n : Nat} {dV : Val} {cl clBody : Closure} {v : Val}
    (_hbody : ∀ a r,
      RC n dV a →
      cl.openω a = some r →
      ∃ rB, clBody.openω a = some rB ∧ RC n r rB) :
    RC (n+1) (.lam dV cl) v := by
  -- TODO(typed-nbe): proof body. Carefully unwind the `.lam` clause
  -- of `RC` and discharge each instance via `_hbody`. The shape is
  -- constructive (forall arg → exists r), so the body builds the
  -- vapp witness from `cl`'s structure.
  sorry

/-! ## Typed eval

`tyEval n e τ` evaluates `e` and produces a `TypedVal` paired with
a proof that the value is RC at the given type.

This is the bridge between the term layer (`Expr`) and the typed
semantic layer (`TypedVal + RC`). It is *defined* in terms of
`eval` and the fundamental lemma; if the FL holds, `tyEval` is
total on well-typed inputs. -/

/-- A typed eval result: a `TypedVal` plus an RC proof. -/
structure TypedEvalResult (n : Nat) where
  tv : TypedVal
  rc : RC n tv.ty tv.val

/-- Typed eval on closed expressions. Returns a `TypedVal` paired
with an RC witness when:
  1. `e` evaluates to some value `v` at fuel `n`.
  2. `τ` evaluates to some `τV` at fuel `n`.
  3. The fundamental lemma applies (typed_nbe_fundamental).

This is sound by construction (RC follows from FL); we leave the
proof body as `sorry` because the FL itself is sorried below.
-/
def tyEval (n : Nat) (e τ : Expr) : Outcome TypedVal := do
  let τV ← eval n unfBound [] τ
  let v ← eval n unfBound [] e
  pure ⟨v, τV⟩

/-! ## The fundamental lemma

The classical NbE soundness theorem, adapted to OCH's setting.

Statement (informal): if `typeCheck n e τ = .ok true` then `eval n e`
produces a value that satisfies `RC n τV v` for some step-index `n'`
that depends on `n`.

Statement (formal): see `typed_nbe_fundamental` below.

Proof (sketch, *not* in this commit): structural induction on the
typing-derivation shape (i.e., follow the tyCheck/tyInfer cases).
Each case of tyCheck constructs an RC witness from the IHs:

- `.type` / `.bot`: base cases — `.type` is in `RC _ .type` directly;
  `.bot` doesn't occur as a value at non-Bot type, so the case is
  vacuous unless `τ = .type`.
- `.bvar k`: env-lookup; `RC` follows from the env-realization
  hypothesis (typed env: every entry is RC at its declared type).
- `.lam dom body`: the function case. To show `RC (n+1) (.lam dom cl)
  (.lam domV cl)`, we need that for every RC argument, vapp produces
  RC at the body type. This is the IH on the body, instantiated under
  the typed env extended with the argument.
- `.app f a`: from `RC` of `f` at `.lam domV cl` and `RC` of `a` at
  `domV`, the `.lam` clause of `RC` gives `RC` at `cl.openω a`.
- `.iota` / `.fix`: similar, using the corresponding `RC` clauses.
- `.asc t τ`: ascription is computationally transparent; `RC` follows
  from the IH on `t` at `τ`.
- `.letE val body`: extend the typed env with the typed value of
  `val`, recurse on body.

Each case requires: the FL's IHs, the RC-closure lemmas (`RC.mono`,
`RC.subtype_closed`), and the standard NbE realization lemmas
(`eval_realises`, `vapp_realises`).
-/

/-- **Fundamental lemma**: well-typed closed expressions evaluate to
RC-witnessed values of their declared type.

This is the typed-NbE analogue of `eval_realises` (the untyped
realization theorem in `SoundnessProof.lean`). The relationship:

  eval_realises    :  R relates v with e — untyped, syntactic.
  typed_nbe_fundamental :  RC relates v with τ — typed, semantic.

Both flow from `typeCheck` accepting; `eval_realises` gives
quote-equivalence, `typed_nbe_fundamental` gives reducibility-at-type.

The conclusion bundles three things:

  ∃ τV v. eval n unfBound [] τ = .ok τV
        ∧ eval n unfBound [] e = .ok v
        ∧ RC n τV v

The first two ensure that `eval` succeeds at the given fuel (this is
NOT derivable in general from `typeCheck` — see the
`docs/ideas/quote-witness-feasibility.md` Ω-counterexample — but for
the *RC-witnessed* fragment, it is). The third gives the typed-RC
witness.

**Proof status**: `sorry`. See `typed-nbe-implementation-log.md`. -/
theorem typed_nbe_fundamental
    {n : Nat} {e τ : Expr}
    (_hcle : e.closedAt 0 = true) (_hclτ : τ.closedAt 0 = true)
    (_hfuel : 1 ≤ n)
    (_hcheck : typeCheck n e τ = .ok true) :
    ∃ τV v, eval n unfBound [] τ = .ok τV
          ∧ eval n unfBound [] e = .ok v
          ∧ RC n τV v := by
  -- TODO(typed-nbe): proof body. See module docstring's sketch.
  sorry

/-! ## Bridge corollaries: from FL to old-soundness sorries

These corollaries discharge the four declaration-level sorries in
`SoundnessProof.lean` once the FL body is filled in. Currently
sorried because they invoke the FL.

The pattern: each old sorry has the shape "I need quote-termination
on a Val produced by eval". The FL gives RC; RC gives quote-
termination via `RC.implies_fullyQuotable` (sorried below) and the
existing structural lemmas about quote.
-/

/-- RC implies `Val.fullyQuotable`: if a value is RC at some type,
it has a fully-quotable representation. This is the bridge from the
typed-RC predicate to the (weaker) untyped fullyQuotable predicate
that `SoundnessProof.lean` already uses. -/
theorem RC.implies_fullyQuotable
    {n : Nat} {τ v : Val} {d : Nat} (_h : RC (n+1) τ v) :
    Val.fullyQuotable d v := by
  -- TODO(typed-nbe): proof body. Case-split on τ's shape.
  -- - .type/.neutral/.bot: trivial (the v can be anything, but
  --   fullyQuotable is structural; need v's *shape* hypothesis,
  --   which RC's neutral/type cases don't give. So this corollary
  --   needs a stronger RC predicate: instead of "RC .type _ := True",
  --   define "RC .type v := Val.fullyQuotable v" baked in. This is
  --   the *saturated* RC; refactor pending.
  -- - .lam: vapp at fresh-neutral terminates (RC.lam clause), and
  --   the result fullyQuotable by IH on the result-type.
  -- - .iota/.fix: open the closure with v / itself; the result
  --   fullyQuotable by IH.
  sorry

/-- RC implies quote-termination: if `v` is RC at any type, `quote
fuelω d v` succeeds with some output. This is the missing direction
from `quote-witness-feasibility.md` — provable under the typed-RC
hypothesis, impossible under the bare `Val.fullyQuotable`. -/
theorem RC.implies_quote_terminates
    {n : Nat} {τ v : Val} {d : Nat} (_h : RC (n+1) τ v) :
    ∃ q, quote fuelω d v = .ok q := by
  -- TODO(typed-nbe): proof body. Same case-split as
  -- implies_fullyQuotable, but extracting the actual quote witness
  -- from RC's productivity content (vapp/openω termination).
  -- Combined with `quote_total_on_eval` (in Soundness.lean) gives
  -- the full chain.
  sorry

end NbE
