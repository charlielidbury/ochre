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

/-- Step-indexed reducibility candidate predicate, **saturated form**
(2026-04-25 refactor for pass 3).

`RC n d τ v` reads: "v is in the RC of type τ at step-index n,
depth d". Defined by recursion on `n` first, then case on `τ`.

The depth `d` parameter records how many binders have been opened
on the way to this point. It threads through closure types so the
quote witnesses live at the correct depth.

**Saturation**: the base cases (`.type`/`.neutral`) and *every*
recursive case bake in `Val.fullyQuotable d v ∧ ∃ q, quote fuelω d v
= .ok q`. This is the "saturated" or "Girard-style" RC: instead of
a separate `RC.implies_fullyQuotable`/`RC.implies_quote_terminates`
lemma (which can't recover the witnesses for `.type`/`.neutral`
where the unsaturated RC was just `True`), the witness is *carried
inside RC* as part of the predicate.

Trade-off: more bookkeeping in the FL body (each rule must produce
fullyQuotable + quote witnesses), but `implies_*` lemmas become
trivial projections. Without saturation, those lemmas are
unprovable for the trivial RC clauses — and the soundness chain
to `fullyQuotable` / `quote-witness` from FL collapses.

The `fix` case is the main subtlety: we unfold once and recurse at
smaller `n`, which is why step-indexing buys us well-foundedness
without needing to inspect the closure body's structure. -/
def RC : Nat → Nat → Val → Val → Prop
  | 0, _, _, _ => True
  | _+1, d, .type, v =>
      Val.fullyQuotable d v ∧ ∃ q, quote fuelω d v = .ok q
  | _+1, _, .bot, _ => False
  | n+1, d, .lam dV cl, v =>
      -- "All lower indices" form (Dreyer-Ahmed-Birkedal /
      -- Pitts-Howe). Mono is trivial because shrinking `n+1` only
      -- restricts the universally-quantified `m`. Without this
      -- quantifier, mono on `.lam` fails (the contravariant-domain
      -- issue: RC m' dV a doesn't lift to RC k dV a).
      (Val.fullyQuotable d v ∧ ∃ q, quote fuelω d v = .ok q) ∧
      ∀ m, m ≤ n → ∀ a, RC m d dV a →
        ∃ r, vapp fuelω unfBound v a = .ok r
           ∧ ∃ rTy, cl.openω a = some rTy ∧ RC m d rTy r
  | n+1, d, .iota aV cl, v =>
      (Val.fullyQuotable d v ∧ ∃ q, quote fuelω d v = .ok q) ∧
      RC n d aV v ∧ ∃ vTy, cl.openω v = some vTy ∧ RC n d vTy v
  | n+1, d, .fix annV cl, v =>
      (Val.fullyQuotable d v ∧ ∃ q, quote fuelω d v = .ok q) ∧
      ∃ uTy, cl.openω (.fix annV cl) = some uTy ∧ RC n d uTy v
  | _+1, d, .neutral _, v =>
      Val.fullyQuotable d v ∧ ∃ q, quote fuelω d v = .ok q

/-! ## RC-closure properties

These are the structural lemmas that follow from `RC`'s definition.
Most are straightforward inductions on `n`. We state them and leave
their proof bodies as `sorry` for now — the *statements* are what
matter for the fundamental-lemma sketch. Future agents fill in
proofs.
-/

/-- Step-index downward monotonicity: more fuel → less constrained.
A value reducible at step `n` is also reducible at any `m ≤ n`.
This is the classical "monotone in n" of step-indexed logical
relations.

Strong induction on `n` with case-split on `τ`. The base `m = 0` is
trivial. The inductive case uses the IH at `n` to weaken inner `RC n`
hypotheses to `RC m`.
-/
theorem RC.mono : ∀ (n : Nat) {m d : Nat} {τ v : Val},
    m ≤ n → RC n d τ v → RC m d τ v := by
  intro n
  induction n with
  | zero =>
    intro m d τ v hle _h
    have hm : m = 0 := Nat.eq_zero_of_le_zero hle
    subst hm
    unfold RC; trivial
  | succ k ih =>
    intro m d τ v hle h
    cases m with
    | zero => unfold RC; trivial
    | succ m' =>
      have hle' : m' ≤ k := Nat.le_of_succ_le_succ hle
      cases τ with
      | type => unfold RC at h ⊢; exact h
      | bot =>
        unfold RC at h ⊢; exact h
      | neutral _ => unfold RC at h ⊢; exact h
      | lam dV cl =>
        unfold RC at h ⊢
        obtain ⟨hSat, hbody⟩ := h
        refine ⟨hSat, ?_⟩
        intro m hmle a hRCa
        exact hbody m (Nat.le_trans hmle hle') a hRCa
      | iota aV cl =>
        unfold RC at h ⊢
        obtain ⟨hSat, hRCa, vTy, hopen, hRCv⟩ := h
        refine ⟨hSat, ih hle' hRCa, vTy, hopen, ih hle' hRCv⟩
      | «fix» annV cl =>
        unfold RC at h ⊢
        obtain ⟨hSat, uTy, hopen, hRC⟩ := h
        refine ⟨hSat, uTy, hopen, ih hle' hRC⟩

/-- RC is preserved under declarative subtyping (algorithmic SubV
form). The intuition: if `τ ⊑ τ'` and `v` inhabits `RC τ`, then
`v` also inhabits `RC τ'` because every "obligation" of `RC τ'` is
a relaxation of one in `RC τ`. -/
theorem RC.subtype_closed {n d : Nat} {τ τ' v : Val}
    (_hsub : SubV [] #[] τ τ')   -- assumes empty seen/Γ for now
    (h : RC n d τ v) : RC n d τ' v := by
  -- TODO(typed-nbe): proof body. Induction on SubV; each
  -- constructor of SubV maps to the corresponding "weakening" of RC.
  -- The hyp/refl/top cases are immediate; the lam case is
  -- contravariant on the domain (the hypothesis on the new domain
  -- discharges via the old via SubV's contra direction).
  sorry

/-- RC at the universe `.type` requires `v` is fully quotable AND
has a concrete quote witness at depth `d`. (Saturated form.) -/
theorem RC.type_top {n d : Nat} {v : Val}
    (hfq : Val.fullyQuotable d v) (hq : ∃ q, quote fuelω d v = .ok q) :
    RC (n+1) d .type v := by
  unfold RC; exact ⟨hfq, hq⟩

/-- RC at `.neutral` is also saturated: requires fullyQuotable + quote
witness on `v`. -/
theorem RC.neutral_top {n d : Nat} {ne : Neutral} {v : Val}
    (hfq : Val.fullyQuotable d v) (hq : ∃ q, quote fuelω d v = .ok q) :
    RC (n+1) d (.neutral ne) v := by
  unfold RC; exact ⟨hfq, hq⟩

/-- An RC-introduction lemma for closure-form values at a `.lam` type.
Given that `v` is itself a lambda `.lam dV' clV` and that for every
RC-typed argument `a`, `vapp` of `v` with `a` produces an RC result,
we conclude `RC` at the `.lam dV cl` type.

Now requires the saturation witnesses on `v` (fullyQuotable + quote)
to populate the `.lam` clause. -/
theorem RC.lam_intro {n d : Nat} {dV : Val} {cl : Closure} {v : Val}
    (hfq : Val.fullyQuotable d v) (hq : ∃ q, quote fuelω d v = .ok q)
    (hbody : ∀ m, m ≤ n → ∀ a, RC m d dV a →
              ∃ r, vapp fuelω unfBound v a = .ok r
                 ∧ ∃ rTy, cl.openω a = some rTy ∧ RC m d rTy r) :
    RC (n+1) d (.lam dV cl) v := by
  unfold RC; exact ⟨⟨hfq, hq⟩, hbody⟩

/-- RC-introduction at an `.iota` type. -/
theorem RC.iota_intro {n d : Nat} {aV : Val} {cl : Closure} {v : Val}
    (hfq : Val.fullyQuotable d v) (hq : ∃ q, quote fuelω d v = .ok q)
    (hann : RC n d aV v)
    (hbody : ∃ vTy, cl.openω v = some vTy ∧ RC n d vTy v) :
    RC (n+1) d (.iota aV cl) v := by
  unfold RC; exact ⟨⟨hfq, hq⟩, hann, hbody⟩

/-- RC-introduction at a `.fix` type. -/
theorem RC.fix_intro {n d : Nat} {annV : Val} {cl : Closure} {v : Val}
    (hfq : Val.fullyQuotable d v) (hq : ∃ q, quote fuelω d v = .ok q)
    (huy : ∃ uTy, cl.openω (.fix annV cl) = some uTy ∧ RC n d uTy v) :
    RC (n+1) d (.fix annV cl) v := by
  unfold RC; exact ⟨⟨hfq, hq⟩, huy⟩

/-- RC-elimination at `.lam`: extract the application-output witness. -/
theorem RC.lam_elim {n m d : Nat} {dV : Val} {cl : Closure} {v a : Val}
    (h : RC (n+1) d (.lam dV cl) v) (hm : m ≤ n) (ha : RC m d dV a) :
    ∃ r, vapp fuelω unfBound v a = .ok r
       ∧ ∃ rTy, cl.openω a = some rTy ∧ RC m d rTy r := by
  unfold RC at h
  exact h.2 m hm a ha

/-- RC-elimination at `.iota`: split into the annotation and self-body
witnesses. -/
theorem RC.iota_elim {n d : Nat} {aV : Val} {cl : Closure} {v : Val}
    (h : RC (n+1) d (.iota aV cl) v) :
    RC n d aV v ∧ ∃ vTy, cl.openω v = some vTy ∧ RC n d vTy v := by
  unfold RC at h; exact h.2

/-- RC-elimination at `.fix`: extract the unfolded-type witness. -/
theorem RC.fix_elim {n d : Nat} {annV : Val} {cl : Closure} {v : Val}
    (h : RC (n+1) d (.fix annV cl) v) :
    ∃ uTy, cl.openω (.fix annV cl) = some uTy ∧ RC n d uTy v := by
  unfold RC at h; exact h.2

/-- **Saturation projection**: every non-zero RC carries a fullyQuotable
witness on `v`. This is what was previously the `RC.implies_fullyQuotable`
lemma — now provable directly from RC's definition because the witness
is baked in. -/
theorem RC.fullyQuotable {n d : Nat} {τ v : Val} (h : RC (n+1) d τ v) :
    Val.fullyQuotable d v := by
  unfold RC at h
  cases τ with
  | type => exact h.1
  | bot => exact False.elim h
  | neutral _ => exact h.1
  | lam _ _ => exact h.1.1
  | iota _ _ => exact h.1.1
  | «fix» _ _ => exact h.1.1

/-- **Saturation projection**: every non-zero RC carries a quote
witness at the recorded depth. Was `RC.implies_quote_terminates`. -/
theorem RC.quote_witness {n d : Nat} {τ v : Val} (h : RC (n+1) d τ v) :
    ∃ q, quote fuelω d v = .ok q := by
  unfold RC at h
  cases τ with
  | type => exact h.2
  | bot => exact False.elim h
  | neutral _ => exact h.2
  | lam _ _ => exact h.1.2
  | iota _ _ => exact h.1.2
  | «fix» _ _ => exact h.1.2

/-! ## Typed eval — pass 2 integration layer

`tyEval n e τ` evaluates `e` and produces a `TypedVal` paired with
a proof that the value is RC at the given type.

This is the bridge between the term layer (`Expr`) and the typed
semantic layer (`TypedVal + RC`). It is *defined* in terms of
`eval` and the fundamental lemma; if the FL holds, `tyEval` is
total on well-typed inputs.

In pass 2 we treat `tyEval` as a *bookkeeping* layer: it runs
the existing untyped `eval` and pairs the result with the
target type `τV`. The RC proof is deferred to pass 3 (the FL
body). Externally, callers receive a TypedVal that they can
*structurally* reason about: type-directed conversion, type-
directed normalisation, etc. -/

/-- A typed eval result: a `TypedVal` plus an RC proof. -/
structure TypedEvalResult (n d : Nat) where
  tv : TypedVal
  rc : RC n d tv.ty tv.val

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

/-- `tyEvalIn` — typed eval over an open environment. Used by
the typed `tyCheckTyped` pipeline below. The caller supplies the
expected type as an already-evaluated `Val` so we can skip the
inner `eval` of `τ`. -/
def tyEvalIn (n unf : Nat) (ρ : Env) (e : Expr) (τV : Val) :
    Outcome TypedVal := do
  let v ← eval n unf ρ e
  pure ⟨v, τV⟩

/-! ## Typed conversion check (`subCheckTyped`)

`subCheckTyped` is the type-directed analogue of `subCheckVal`.
It takes a `TypedVal` as the LHS and a `Val` as the RHS-target,
and uses the recorded type on the LHS as a fast-path:

```
  a : TypedVal,  b : Val
  if subCheckVal Γ [] a.ty b = .ok true then accept
  else fall back to subCheckVal Γ seen a.val b
```

**Soundness**. If `a.val ⊑ a.ty` (the typing invariant on a
`TypedVal`) and `subCheckVal` is sound and transitive, then
`a.ty ⊑ b ⟹ a.val ⊑ b`. So the fast-path is sound whenever
the typing invariant on `TypedVal` holds — which is exactly
what `RC n a.ty a.val` (the fundamental lemma's conclusion)
gives us.

**Where the win comes from**. For singleton-encoded constants
like `zero_`, `one_`, `two_` (in OCH's nested-fix Nat_), the
*declared* type is `Nat_`. The expensive subtype obligation
`zero_ ⊑ Nat_` reduces under the typed pipeline to the trivial
`Nat_ ⊑ Nat_` (refl). Subsequent uses don't re-derive the
singleton structure.

**Why we don't trust `.ok false` from the fast-path**. The
recorded type may not be the *tightest* type: e.g.,
`succ_ zero_` has recorded type `Nat_` but is also at type
`Fin two_`. The fast-path would say `Nat_ ⊑ Fin two_` is
false (correctly), but the slow path can still derive
`succ_ zero_ ⊑ Fin two_` directly via the Option F encoding.
So `.ok false` only triggers fallback, not rejection.

**Cost vs. benefit**. The fast-path adds one extra
`subCheckVal` call to every typed check. For cases where it
fires, this is a huge win (50k → ~50 fuel for `three_ ⊑ Nat_`).
For cases where it fails, we pay the fast-path cost on top of
the slow path — usually ~2x slowdown for the failing branch.
The overall impact should be net positive for the test suite,
which has heavy positive-subtyping workloads.

The fast-path is non-recursive — we don't invoke `subCheckTyped`
in the fast-path. That means proof obligations carry through
cleanly: `subCheckTyped_subV` will reduce to `subCheckVal_subV`
applied at two points (the fast-path and the fallback).
-/

/-- Top-level typed subtype check. The LHS is a `TypedVal`
carrying its declared type; the RHS is a bare `Val` (the target
type). -/
def subCheckTyped (fuel : Nat) (tyCtx : TyCtx)
    (seen : List (Val × Val)) (a : TypedVal) (b : Val)
    : Outcome Bool :=
  -- Fast path: try to discharge via the recorded type.
  -- If `a.ty ⊑ b`, then `a.val ⊑ a.ty ⊑ b`, so accept.
  -- Note: we use a fresh seen-set on the fast-path. The seen
  -- entries (a.val, _) don't apply to (a.ty, _) — they were
  -- collected for value-vs-value coinduction, not type-vs-type.
  match subCheckVal fuel tyCtx [] a.ty b with
  | .ok true => .ok true
  | _ => subCheckVal fuel tyCtx seen a.val b

/-- Top-level typed entry point. Like `subCheck`, but goes
through the typed pipeline.

**Architecture**. Two strategies, in order:

1. **Bidirectional path** — `typeCheck a τ`. This is the
   syntactic-bidirectional checker: walks `a`'s structure, at
   every `.app` checks the argument against the function's
   domain syntactically (no value-level subtype check on the
   *whole* term). For ascribed/inferable terms, this terminates
   in O(|a|) subCheckVal calls each of which is small (e.g.
   `Nat_ ⊑ Nat_` = refl). For ill-typed terms or terms that
   typeCheck can't process, returns `.ok false` /
   `.outOfFuel` / `.error`.

2. **Conversion fallback** — `subCheckVal aV τV`. The bare
   value-level subtype check, which is what `subCheck` does.
   This is necessary for cases where `typeCheck` rejects
   (e.g. `Type ⊑ Nat_` is `.ok false` from typeCheck since
   `.type` has principal type `.type` and `Type ⊑ Nat_` is
   false; but at the value layer, `subCheck Type Nat_` is
   *also* `.ok false` so it doesn't matter — yet the
   bidirectional path is the one that gives the *win*).

The win comes from (1): `typeCheck three_ Nat_` is fast
because each layer of `succ_ ...` is checked locally. Without
typing, `subCheckVal three_ Nat_` is forced to expand the
singleton-encoded structure of `Nat_`'s ι-body and verify it
matches `three_`'s structure — that's the ~50k fuel cost.

For positive cases where (1) accepts: O(|a|) subCheckVal
calls, each cheap (refl on inferred type).

For positive cases where (1) rejects but the term is still
declaratively a subtype (e.g. when the inferred type isn't
the tightest, or when typeCheck has incompletenesses), (2)
is the safety net — same cost as bare `subCheck`.

For negative cases where the term is genuinely ill-typed:
(1) rejects fast, (2) rejects, total cost is sum of both.
That's a 2x slowdown for negatives compared to bare
`subCheck` — acceptable given the test corpus is mostly
positive subtyping.
-/
def subCheckT (fuel : Nat) (a τ : Expr) : Outcome Bool :=
  match typeCheck fuel a τ with
  | .ok true => .ok true
  | _ => subCheck fuel a τ

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
          ∧ RC n 0 τV v := by
  -- TODO(typed-nbe): proof body. See module docstring's sketch.
  sorry

/-! ## Bridge corollaries: from FL to old-soundness sorries

After the saturation refactor (2026-04-25), `RC.implies_fullyQuotable`
and `RC.implies_quote_terminates` are now **trivial projections** of
`RC.fullyQuotable` and `RC.quote_witness` (proven above). They are
kept as named API for backward-compat with the Pass 1 plan, but
delegate to the projections.
-/

/-- RC implies `Val.fullyQuotable`. Direct delegation to the
saturation projection. -/
theorem RC.implies_fullyQuotable
    {n d : Nat} {τ v : Val} (h : RC (n+1) d τ v) :
    Val.fullyQuotable d v :=
  RC.fullyQuotable h

/-- RC implies quote-termination. Direct delegation to the
saturation projection. -/
theorem RC.implies_quote_terminates
    {n d : Nat} {τ v : Val} (h : RC (n+1) d τ v) :
    ∃ q, quote fuelω d v = .ok q :=
  RC.quote_witness h

end NbE
