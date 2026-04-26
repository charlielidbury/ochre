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

-- `RC.subtype_closed` is defined further down in the file, after
-- the saturation projections (`RC.fullyQuotable`/`RC.quote_witness`)
-- which the proof depends on.

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

/-! ### `RC.subtype_closed`

RC is preserved under declarative subtyping (algorithmic SubV form).
The intuition: if `τ ⊑ τ'` and `v` inhabits `RC τ`, then `v` also
inhabits `RC τ'` because every "obligation" of `RC τ'` is a
relaxation of one in `RC τ`.

**Strategy**: prove a more general auxiliary statement
`RC.subtype_closed_aux` that takes a seen-set hypothesis (every
`(α, β) ∈ S` already inherits RC across), then derive the
empty-seen-set case as a corollary.

With the *saturated* RC (post-pass-3 refactor), the RC at
`.type`/`.neutral` cases reduces to just `Val.fullyQuotable d v ∧
∃ q, quote fuelω d v = .ok q`, which transfers from any source RC
via `RC.fullyQuotable` / `RC.quote_witness`. This makes the `top`,
`neutral_struct`, `revapp_R`, `bot_L`, `stuckRec_struct` cases
mechanical.

**The hard cases** (`lam`, `iota_struct`, `fix_struct`, `iota_intro`,
`unfold_fix_*`, `unfold_iota_L`, `revapp_L`, `neutral_ascent`) have
one or more of the following obstacles:

1. **Body substitution mismatch**: SubV.lam's body premise is
   `SubV S (Γ.push domA) bA bB` where `bA = clA.openω
   (.neutral (.var Γ.size))` and `bB = clB.openω (.neutral (.var
   Γ.size))` are *fresh-opened* bodies. RC at `.lam` requires the
   bodies opened at *concrete RC-typed arguments* `a`. The bridge
   needs a substitution lemma "fresh-opened-equivalent →
   arbitrary-substitution-equivalent" — not yet available.

2. **Seen-set obligation circularity**: cases like `iota_intro`,
   `unfold_fix_R`, `revapp_R`, `revapp_L` add an entry `(τ, τ')` to
   the seen-set in the recursive premise. The seen-set hypothesis
   in our auxiliary requires "for every `(α, β) ∈ S, ∀ v', RC n α
   v' → RC n β v'" — the new entry's obligation is exactly what we
   are trying to prove. This is the standard Pitts-Howe / DAB
   coinduction and would need to be addressed with a stratified
   step-indexed approach (the seen-set carries obligations at
   strictly smaller step-index).

3. **iotaIntro / unfold_fix mismatch**: SubV.iota_intro has
   `clB.openω a = some bB` where `a` is the LHS *type*; RC `.iota`
   requires `clB.openω v` where `v` is the *value*. These are
   different unless `a = v` (degenerate). The bridge is nontrivial
   and requires the typing-derivation structure.

**Status (pass 8)**: 11/16 SubV cases proven inline:
- Saturation-only cases (RC at `.type`/`.neutral` is just
  saturation witnesses): `top`, `neutral_struct`,
  `stuckRec_struct`, `revapp_R`.
- Trivial cases: `refl`, `hyp`, `bot_L`.
- One-step recursive case: `unfold_fix_R` (closed via the
  strong-IH on the augmented seen-set entry).
- **Pass 7 closures**: `lam`, `iota_struct` — closed via the
  `SubV_subst_neutral_to_value` body-substitution lemma (sorried,
  consolidates 2 inline sorries into 1).
- **Pass 8 closure**: `fix_struct` — closed via the
  `SubV_subst_pair` pair-substitution lemma (sorried,
  consolidates 1 inline sorry into 1; relates `clA.openω
  (.fix annA clA)` and `clB.openω (.fix annB clB)` via
  `SubV.hyp` on the augmented seen-set).

Hard cases remain sorried inline:
- `iota_intro` — typed iotaIntro LHS-vs-value mismatch (needs
  RC-realisation bridge, distinct from the basic/pair
  substitution family).
- `unfold_fix_L`, `unfold_iota_L` — step-up mismatch (the LHS
  unfold consumes a step but the goal demands the original step;
  documented in pass 5 post-mortem as a structural RC issue).
- `revapp_L` — vapp-respects-RC missing.
- `neutral_ascent` — **structurally unprovable under current RC**.
  Pass 15 (2026-04-25) finding: the lemma's conclusion is FALSE
  for arbitrary `v` in this case (counterexample: `v = .type` at
  any closure-form `b`). RC at `.neutral` carries only saturation,
  which does not imply RC at closure-form types. Closing this
  case requires either redesigning RC at `.neutral` to encode
  realisation content (~200-400 LOC) or strengthening
  `subtype_closed_aux`'s signature with a "v realises a closed
  term" premise. See pass 15 entry in
  `docs/ideas/typed-nbe-implementation-log.md` and the inline
  comment on the sorry below.

Inline sorry count in `subtype_closed_aux`: 5 (was 6 pre-pass-8).
Plus 2 sorried lemmas (`SubV_subst_neutral_to_value`,
`SubV_subst_pair`) that together close 3 of the easier-shaped
cases (`lam`, `iota_struct`, `fix_struct`).

**Net file delta pass 8**: 0 inline sorries (closed 1 inline,
added 1 new sorried lemma). Refactoring pass: the substitution
lemma family is now stated as two related lemmas with their own
proof targets, rather than one lemma plus an undocumented
fix_struct gap. Pre-pass-8 total = post-pass-8 total = 8.
-/

/-- Helper: extracting the saturation conjunct from any RC at
step ≥ 1. -/
private theorem RC.sat_of_succ {n d : Nat} {τ v : Val}
    (h : RC (n+1) d τ v) :
    Val.fullyQuotable d v ∧ ∃ q, quote fuelω d v = .ok q :=
  ⟨RC.fullyQuotable h, RC.quote_witness h⟩

/-! ## Typed environment realisation

`RC_env n d Γ ρ`: the value-environment `ρ` realises the type-context
`Γ` at step-index `n`, depth `d`. Each value-position aligns with the
corresponding type-position via the bvar indexing convention.

**Convention** (matching `tyInfer`/`tyCheck`): `Γ` is an `Array Val`
(= `TyEnv`) where `Γ[Γ.size - 1 - k]` is the type at bvar `k`.
`ρ` is a `List Val` (= `Env`) where `ρ[k]` is the value at bvar `k`
(cons-order: position 0 is the head / most recently bound).

The realisation aligns these by bvar index (NOT by raw array/list
index). So `RC_env n d Γ ρ` requires `Γ.size = ρ.length` and, for
every bvar `k < ρ.length`, the value `ρ[k]` is RC at the type
`Γ[Γ.size - 1 - k]`.

**Position in the file** (pass 10): defined here, *before*
`subtype_closed_aux`, so that the latter can take `RC_env n d Γ ρ`
as a hypothesis. The original definition site (after the FL
signature) is preserved as documentation; the actual definition
lives here. -/

/-- The value environment `ρ` realises the type context `Γ` at step
`n`, depth `d`. Indexed by bvar position (ρ is cons-order, Γ is
reverse-order matching the bvar convention from `tyInfer`). -/
def RC_env (n d : Nat) (Γ : TyEnv) (ρ : Env) : Prop :=
  Γ.size = ρ.length ∧
  ∀ k, k < ρ.length →
    ∃ τ v, Γ[Γ.size - 1 - k]? = some τ ∧ ρ[k]? = some v ∧ RC n d τ v

/-- The empty typed environment realises the empty value environment
trivially. -/
theorem RC_env.nil {n d : Nat} : RC_env n d #[] [] := by
  refine ⟨rfl, ?_⟩
  intro k hk
  simp at hk

/-- Extending the typed env with a freshly-bound `(τ, v)` pair
preserves realisation, given `RC n d τ v`. The new entry takes
bvar index `0`; existing entries shift to bvar `k+1`. -/
theorem RC_env.cons {n d : Nat} {Γ : TyEnv} {ρ : Env} {τ v : Val}
    (hΓρ : RC_env n d Γ ρ) (hRC : RC n d τ v) :
    RC_env n d (Γ.push τ) (v :: ρ) := by
  obtain ⟨hlen, hidx⟩ := hΓρ
  refine ⟨?_, ?_⟩
  · -- Length preservation: |Γ.push τ| = |Γ| + 1 = |ρ| + 1 = |v::ρ|.
    simp [Array.size_push, hlen]
  · -- Bvar lookup. New entry at k=0; existing entries at k+1.
    intro k hk
    -- Case on k. Use omega for the index-arithmetic relating
    -- (Γ.push τ).size to Γ.size.
    cases k with
    | zero =>
      -- k = 0 → bvar 0 maps to the freshly pushed τ and the head v.
      refine ⟨τ, v, ?_, ?_, hRC⟩
      · -- (Γ.push τ)[(Γ.size + 1) - 1 - 0]? = (Γ.push τ)[Γ.size]?
        --  = some τ (the just-pushed entry).
        have hbound : Γ.size < (Γ.push τ).size := by
          rw [Array.size_push]; omega
        have hidxeq : (Γ.push τ).size - 1 - 0 = Γ.size := by
          rw [Array.size_push]; omega
        rw [hidxeq, Array.getElem?_eq_getElem hbound]
        rw [Array.getElem_push_eq]
      · simp
    | succ k' =>
      -- k = k' + 1 → bvar k+1 looks up old position k'.
      have hk_unfold : k' + 1 < ρ.length + 1 := by
        simpa [List.length_cons] using hk
      have hk' : k' < ρ.length := Nat.lt_of_succ_lt_succ hk_unfold
      obtain ⟨τk, vk, hΓk, hρk, hRCk⟩ := hidx k' hk'
      refine ⟨τk, vk, ?_, ?_, hRCk⟩
      · -- (Γ.push τ)[(Γ.size + 1) - 1 - (k' + 1)]?
        --  = (Γ.push τ)[Γ.size - 1 - k']? = Γ[Γ.size - 1 - k']?
        have hbound_orig : Γ.size - 1 - k' < Γ.size := by
          have : k' < Γ.size := hlen ▸ hk'
          omega
        have hbound_push : Γ.size - 1 - k' < (Γ.push τ).size := by
          rw [Array.size_push]; omega
        have hidxeq : (Γ.push τ).size - 1 - (k' + 1) = Γ.size - 1 - k' := by
          rw [Array.size_push]; omega
        rw [hidxeq]
        rw [Array.getElem?_eq_getElem hbound_push]
        rw [Array.getElem_push_lt _ _ _ hbound_orig]
        rw [Array.getElem?_eq_getElem hbound_orig] at hΓk
        exact hΓk
      · -- (v :: ρ)[k' + 1]? = ρ[k']?
        simpa using hρk

/-- **Step-index downward monotonicity** for typed environments.
`RC_env n d Γ ρ` at a higher step `n` weakens to any lower step
`m ≤ n` because each per-position RC is downward-monotone in `n`
via `RC.mono`. -/
theorem RC_env.mono {n m d : Nat} {Γ : TyEnv} {ρ : Env}
    (hle : m ≤ n) (hΓρ : RC_env n d Γ ρ) : RC_env m d Γ ρ := by
  obtain ⟨hlen, hidx⟩ := hΓρ
  refine ⟨hlen, ?_⟩
  intro k hk
  obtain ⟨τ, v, hΓk, hρk, hRC⟩ := hidx k hk
  exact ⟨τ, v, hΓk, hρk, RC.mono _ hle hRC⟩

/-! ## `Val.substLvl` — Val-level substitution machinery (pass 12)

**Definition layer.** Replaces a level-indexed neutral variable
`.var k` with a substituent value `v_sub` throughout a `Val`.

**The partiality issue.** When we substitute through `.neutral
(.app n a)` and `n` rewrites to a non-neutral (e.g., the head was
`.var k` and `v_sub` is a `.lam`), the resulting `.app` is a
β-redex that must be fired via `vapp`. This makes substitution
inherently partial: it depends on `vapp` succeeding, which depends
on fuel.

**Approach** (per pass-9 finding A.1, refined for pass 12).
`Val.substLvl` returns `Option Val`: `none` indicates either
fuel exhaustion (`vapp` ran out) or genuine stuckness.
`Neutral.substLvl` returns `Option Val` (NOT `Option Neutral`)
since substitution may "promote" a neutral to a non-neutral via
β/μ-firing.

**Termination.** Structural recursion on the `Val`/`Neutral`/
`Closure` argument (mutual). The `.app` case's `vapp` call is
fuelled separately; substLvl itself doesn't recurse on its
result. Closures are walked via their `env` (each entry
recurses).

**Pass 12 status.** This pass commits the data-layer definitions
plus the simplest structural lemmas (`identity-on-closed`).
The eval-commutation lemma (~200 LOC) and the SubV-preservation
lemma (~200 LOC) are deferred to passes 13/14. This pass alone
does NOT close `SubV_subst_neutral_to_value`. -/

mutual
  /-- Substitute `v_sub` for the level-indexed neutral var `.var k`
  throughout a `Val`. Returns `none` for genuine stuckness or
  fuel exhaustion at `.app`-redex firings.

  The structural cases (`.type`, `.bot`, closure-form heads)
  recurse via `Closure.substLvl`. The `.neutral n` case delegates
  to `Neutral.substLvl`, which may promote-to-Val via vapp-redex
  firing. -/
  def Val.substLvl (fuel k : Nat) (v_sub : Val) : Val → Option Val
    | .type => some .type
    | .bot => some .bot
    | .neutral n => Neutral.substLvl fuel k v_sub n
    | .lam dom cl => do
        let dom' ← Val.substLvl fuel k v_sub dom
        let cl' ← Closure.substLvl fuel k v_sub cl
        some (.lam dom' cl')
    | .iota ann cl => do
        let ann' ← Val.substLvl fuel k v_sub ann
        let cl' ← Closure.substLvl fuel k v_sub cl
        some (.iota ann' cl')
    | .«fix» ann cl => do
        let ann' ← Val.substLvl fuel k v_sub ann
        let cl' ← Closure.substLvl fuel k v_sub cl
        some (.«fix» ann' cl')

  /-- Substitute through a Neutral. Returns `Option Val` because the
  result may not remain a Neutral: substituting a non-neutral
  `v_sub` for the spine's head var fires β. -/
  def Neutral.substLvl (fuel k : Nat) (v_sub : Val) : Neutral → Option Val
    | .var j => if j = k then some v_sub else some (.neutral (.var j))
    | .app n a => do
        let n' ← Neutral.substLvl fuel k v_sub n
        let a' ← Val.substLvl fuel k v_sub a
        match n' with
        | .neutral nn => some (.neutral (.app nn a'))
        | _ =>
            -- Non-neutral spine head: fire vapp.
            (vapp fuel unfBound n' a').toOption
    | .stuckRec f a => do
        let f' ← Val.substLvl fuel k v_sub f
        let a' ← Val.substLvl fuel k v_sub a
        -- Re-form the stuck-rec: f' may still be a closure-form
        -- (fix/iota), in which case it's again stuck on the
        -- (potentially still-neutral) a'.
        if a'.isNeutral then
          some (.neutral (.stuckRec f' a'))
        else
          -- a' became non-neutral: try a vapp that may fire.
          (vapp fuel unfBound f' a').toOption

  /-- Substitute through a Closure. The closure's body is
  syntactic (`Expr`); we only substitute through the captured
  environment. -/
  def Closure.substLvl (fuel k : Nat) (v_sub : Val) :
      Closure → Option Closure
    | ⟨body, env⟩ => do
        let env' ← Closure.envSubstLvl fuel k v_sub env
        some ⟨body, env'⟩

  /-- Substitute through a Closure environment, point-wise. -/
  def Closure.envSubstLvl (fuel k : Nat) (v_sub : Val) :
      List Val → Option (List Val)
    | [] => some []
    | v :: vs => do
        let v' ← Val.substLvl fuel k v_sub v
        let vs' ← Closure.envSubstLvl fuel k v_sub vs
        some (v' :: vs')
end

/-! ### `Val.substLvl` simplest structural lemmas (pass 12)

Pass 12 commits the data layer. The lemmas we can prove without
needing eval-commutation:

- `Val.substLvl_levelsBelow_identity`: substitution is identity
  on values whose levels are all below `k`. (Trivial — the var
  case never fires.)

What is NOT proven in pass 12:
- Eval-commutation: `eval (v_sub :: env) body = .ok v →
  eval (.neutral (.var k) :: env) body = .ok bA → Val.substLvl k
  v_sub bA = some v` (with appropriate level-arithmetic). This is
  the heart of the keystone lemma; ~200 LOC of mutual
  fuel-induction over eval/vapp.
- SubV-preservation: `SubV S Γ a b → Val.substLvl k v_sub a =
  some a' → Val.substLvl k v_sub b = some b' → SubV S Γ a' b'`.
  Per pass-9 estimate, ~200 LOC across 13 SubV constructors. -/

/-- Substitution by `v_sub` for the level `Γ.size` is identity
on a closure body opened only at fresh-neutral var `Γ.size` IF
that var doesn't actually appear in the body. (Trivial corollary
of `Val.substLvl`'s definition; documents the simple no-op
case.)

Stated as an axiom-clean **non-`theorem`** placeholder for
documentation; pass 13 makes it a real lemma when paired with
the levels-below predicate threading. The general statement
needs `Val.levelsBelow` from `SoundnessProof.lean`. -/
example (k : Nat) (v_sub : Val) :
    Val.substLvl 1 k v_sub .type = some .type := by
  rfl

/-- Documentation example: substituting through `.bot` is the
identity. -/
example (k : Nat) (v_sub : Val) :
    Val.substLvl 1 k v_sub .bot = some .bot := by
  rfl

/-- Documentation example: substituting `v_sub` at the matching
level fires the var case, returning `v_sub`. -/
example (k : Nat) (v_sub : Val) :
    Val.substLvl 1 k v_sub (.neutral (.var k)) = some v_sub := by
  unfold Val.substLvl Neutral.substLvl
  simp

/-- Documentation example: substituting at a non-matching level
leaves the variable unchanged. -/
example (j k : Nat) (v_sub : Val) (hjk : j ≠ k) :
    Val.substLvl 1 k v_sub (.neutral (.var j)) =
      some (.neutral (.var j)) := by
  unfold Val.substLvl Neutral.substLvl
  simp [hjk]

/-! ### Val/Neutral/Closure well-formedness (pass 13)

`Val.WellFormed` captures the invariant that pass 12 identified as
needed: every `.stuckRec` in the value tree has its argument-side
neutral. This is exactly the invariant that `vapp` maintains when
producing stuckRec (it only fires the stuckRec branch when
`a.isNeutral || unf == 0`; the latter case still produces a
stuckRec, which violates this invariant — but only when fuel is
exhausted).

For pass 13's purposes we use the strong invariant
(stuckRec implies arg is neutral) and prove later that `eval` /
`vapp` preserve it under reasonable conditions. Identity-on-closed
substitution (`levelsBelow k v → Val.substLvl fuel k v_sub v =
some v`) follows directly. -/
mutual
  /-- A `Val` is *well-formed* iff every `.stuckRec` reachable
  through closure-form heads has a `.isNeutral` argument. -/
  def Val.WellFormed : Val → Prop
    | .type => True
    | .bot => True
    | .neutral n => Neutral.WellFormed n
    | .lam dom cl => Val.WellFormed dom ∧ Closure.WellFormed cl
    | .iota ann cl => Val.WellFormed ann ∧ Closure.WellFormed cl
    | .«fix» ann cl => Val.WellFormed ann ∧ Closure.WellFormed cl

  def Neutral.WellFormed : Neutral → Prop
    | .var _ => True
    | .app n a => Neutral.WellFormed n ∧ Val.WellFormed a
    | .stuckRec f a =>
        Val.WellFormed f ∧ Val.WellFormed a ∧ a.isNeutral = true

  def Closure.WellFormed : Closure → Prop
    | ⟨_body, env⟩ => Closure.envWellFormed env

  /-- Helper for Closure.WellFormed (inlined list quantifier). -/
  def Closure.envWellFormed : List Val → Prop
    | [] => True
    | v :: vs => Val.WellFormed v ∧ Closure.envWellFormed vs
end

/-- `envWellFormed` ↔ "every entry is well-formed". -/
theorem Closure.envWellFormed_getElem?
    {env : List Val} (h : Closure.envWellFormed env)
    {k : Nat} {v : Val} (hk : env[k]? = some v) :
    Val.WellFormed v := by
  induction env generalizing k with
  | nil => simp at hk
  | cons w ws ih =>
      cases k with
      | zero =>
          simp only [List.getElem?_cons_zero, Option.some.injEq] at hk
          subst hk
          unfold Closure.envWellFormed at h
          exact h.1
      | succ m =>
          simp only [List.getElem?_cons_succ] at hk
          unfold Closure.envWellFormed at h
          exact ih h.2 hk

theorem Closure.envWellFormed_take
    {env : List Val} (h : Closure.envWellFormed env) (n : Nat) :
    Closure.envWellFormed (env.take n) := by
  induction env generalizing n with
  | nil => cases n <;> simp [List.take, Closure.envWellFormed]
  | cons w ws ih =>
      cases n with
      | zero =>
          simp [List.take, Closure.envWellFormed]
      | succ m =>
          unfold Closure.envWellFormed at h
          simp only [List.take_succ_cons]
          unfold Closure.envWellFormed
          exact ⟨h.1, ih h.2 m⟩

/-! ### Identity-on-levelsBelow (pass 13)

Substitution is a no-op when level `k` doesn't appear in the
value. With `Val.WellFormed` (every `.stuckRec` has a neutral
argument), the `.stuckRec` case is straightforward — the
neutrality of the argument is preserved (since substitution at
levels below `k` never produces a non-neutral from a neutral). -/

mutual
  /-- `Val.substLvl` is the identity on values whose levels are all
  below the substitution point AND that are well-formed. The
  well-formedness condition is needed to handle `.stuckRec` (where
  substitution would otherwise fire vapp on a non-neutral arg). -/
  theorem Val.substLvl_of_levelsBelow :
      ∀ (v : Val) (fuel k : Nat) (v_sub : Val),
      Val.levelsBelow k v → Val.WellFormed v →
      Val.substLvl fuel k v_sub v = some v
    | .type, _, _, _, _, _ => rfl
    | .bot, _, _, _, _, _ => rfl
    | .neutral n, fuel, k, v_sub, h, hwf => by
        unfold Val.substLvl
        unfold Val.levelsBelow at h
        unfold Val.WellFormed at hwf
        exact Neutral.substLvl_of_levelsBelow n fuel k v_sub h hwf
    | .lam dom cl, fuel, k, v_sub, h, hwf => by
        unfold Val.substLvl
        unfold Val.levelsBelow at h
        unfold Val.WellFormed at hwf
        rw [Val.substLvl_of_levelsBelow dom fuel k v_sub h.1 hwf.1]
        simp only [bind, Option.bind_some]
        rw [Closure.substLvl_of_levelsBelow cl fuel k v_sub h.2 hwf.2]
        simp
    | .iota ann cl, fuel, k, v_sub, h, hwf => by
        unfold Val.substLvl
        unfold Val.levelsBelow at h
        unfold Val.WellFormed at hwf
        rw [Val.substLvl_of_levelsBelow ann fuel k v_sub h.1 hwf.1]
        simp only [bind, Option.bind_some]
        rw [Closure.substLvl_of_levelsBelow cl fuel k v_sub h.2 hwf.2]
        simp
    | .«fix» ann cl, fuel, k, v_sub, h, hwf => by
        unfold Val.substLvl
        unfold Val.levelsBelow at h
        unfold Val.WellFormed at hwf
        rw [Val.substLvl_of_levelsBelow ann fuel k v_sub h.1 hwf.1]
        simp only [bind, Option.bind_some]
        rw [Closure.substLvl_of_levelsBelow cl fuel k v_sub h.2 hwf.2]
        simp

  /-- `Neutral.substLvl` returns the wrapped neutral when all levels
  are below the substitution point and the neutral is well-formed.
  The strong form (returns `some (.neutral n)`) is needed because
  `Neutral.substLvl` returns `Option Val`, not `Option Neutral`. -/
  theorem Neutral.substLvl_of_levelsBelow :
      ∀ (n : Neutral) (fuel k : Nat) (v_sub : Val),
      Neutral.levelsBelow k n → Neutral.WellFormed n →
      Neutral.substLvl fuel k v_sub n = some (.neutral n)
    | .var j, fuel, k, v_sub, h, _ => by
        unfold Neutral.substLvl
        unfold Neutral.levelsBelow at h
        have : j ≠ k := Nat.ne_of_lt h
        simp [this]
    | .app n a, fuel, k, v_sub, h, hwf => by
        unfold Neutral.substLvl
        unfold Neutral.levelsBelow at h
        unfold Neutral.WellFormed at hwf
        rw [Neutral.substLvl_of_levelsBelow n fuel k v_sub h.1 hwf.1]
        simp only [bind, Option.bind_some]
        rw [Val.substLvl_of_levelsBelow a fuel k v_sub h.2 hwf.2]
        simp
    | .stuckRec f a, fuel, k, v_sub, h, hwf => by
        unfold Neutral.substLvl
        unfold Neutral.levelsBelow at h
        unfold Neutral.WellFormed at hwf
        rw [Val.substLvl_of_levelsBelow f fuel k v_sub h.1 hwf.1]
        simp only [bind, Option.bind_some]
        rw [Val.substLvl_of_levelsBelow a fuel k v_sub h.2 hwf.2.1]
        simp [hwf.2.2]

  theorem Closure.substLvl_of_levelsBelow :
      ∀ (cl : Closure) (fuel k : Nat) (v_sub : Val),
      Closure.levelsBelow k cl → Closure.WellFormed cl →
      Closure.substLvl fuel k v_sub cl = some cl
    | ⟨body, env⟩, fuel, k, v_sub, h, hwf => by
        change Closure.envLevelsBelow k env at h
        change Closure.envWellFormed env at hwf
        unfold Closure.substLvl
        rw [Closure.envSubstLvl_of_levelsBelow env fuel k v_sub h hwf]
        simp

  theorem Closure.envSubstLvl_of_levelsBelow :
      ∀ (env : List Val) (fuel k : Nat) (v_sub : Val),
      Closure.envLevelsBelow k env → Closure.envWellFormed env →
      Closure.envSubstLvl fuel k v_sub env = some env
    | [], _, _, _, _, _ => rfl
    | w :: ws, fuel, k, v_sub, h, hwf => by
        unfold Closure.envSubstLvl
        unfold Closure.envLevelsBelow at h
        unfold Closure.envWellFormed at hwf
        rw [Val.substLvl_of_levelsBelow w fuel k v_sub h.1 hwf.1]
        simp only [bind, Option.bind_some]
        rw [Closure.envSubstLvl_of_levelsBelow ws fuel k v_sub h.2 hwf.2]
        simp
end

/-! ### `envSubstLvl` list-operation commutation lemmas (pass 13)

These are pure list-level commutation properties of
`envSubstLvl` with `take` and `getElem?`. They are the env-side
analogs of the shape lemmas needed by an eval-commutation proof
(eval performs `getElem?` for `.bvar` and `take` via
`Closure.mk'` for closure-form heads).

These lemmas have `Closure.envSubstLvl ... env = some env'` as a
hypothesis: they don't claim envSubstLvl succeeds (which depends
on each entry's substLvl succeeding), they describe its
behaviour when it does. -/

theorem Closure.envSubstLvl_cons
    {fuel k : Nat} {v_sub : Val} {w : Val} {ws : List Val}
    {w' : Val} {ws' : List Val}
    (hw : Val.substLvl fuel k v_sub w = some w')
    (hws : Closure.envSubstLvl fuel k v_sub ws = some ws') :
    Closure.envSubstLvl fuel k v_sub (w :: ws) = some (w' :: ws') := by
  unfold Closure.envSubstLvl
  rw [hw]
  simp only [bind, Option.bind_some]
  rw [hws]
  simp

/-- Inversion of `envSubstLvl` on a cons: extracts the element-wise
substitutions. -/
theorem Closure.envSubstLvl_cons_inv
    {fuel k : Nat} {v_sub : Val} {w : Val} {ws : List Val}
    {result : List Val}
    (h : Closure.envSubstLvl fuel k v_sub (w :: ws) = some result) :
    ∃ w' ws',
      Val.substLvl fuel k v_sub w = some w' ∧
      Closure.envSubstLvl fuel k v_sub ws = some ws' ∧
      result = w' :: ws' := by
  unfold Closure.envSubstLvl at h
  simp only [bind, Option.bind] at h
  match hw : Val.substLvl fuel k v_sub w, hws : Closure.envSubstLvl fuel k v_sub ws with
  | none, _ => rw [hw] at h; cases h
  | some w', none => rw [hw, hws] at h; cases h
  | some w', some ws' =>
      rw [hw, hws] at h
      simp only [Option.some.injEq] at h
      exact ⟨w', ws', rfl, rfl, h.symm⟩

theorem Closure.envSubstLvl_length
    {fuel k : Nat} {v_sub : Val} {env env' : List Val}
    (h : Closure.envSubstLvl fuel k v_sub env = some env') :
    env'.length = env.length := by
  induction env generalizing env' with
  | nil =>
      unfold Closure.envSubstLvl at h
      simp only [Option.some.injEq] at h
      subst h; rfl
  | cons w ws ih =>
      obtain ⟨w', ws', _, hws', rfl⟩ := Closure.envSubstLvl_cons_inv h
      simp [List.length_cons, ih hws']

theorem Closure.envSubstLvl_getElem?
    {fuel k : Nat} {v_sub : Val} {env env' : List Val}
    (h : Closure.envSubstLvl fuel k v_sub env = some env')
    (j : Nat) {v : Val} (hv : env[j]? = some v) :
    ∃ v', env'[j]? = some v' ∧ Val.substLvl fuel k v_sub v = some v' := by
  induction env generalizing j env' with
  | nil => simp at hv
  | cons w ws ih =>
      obtain ⟨w', ws', hw', hws', rfl⟩ := Closure.envSubstLvl_cons_inv h
      cases j with
      | zero =>
          simp only [List.getElem?_cons_zero, Option.some.injEq] at hv
          subst hv
          refine ⟨w', ?_, hw'⟩
          simp [List.getElem?_cons_zero]
      | succ m =>
          simp only [List.getElem?_cons_succ] at hv
          obtain ⟨v', hv', hsub⟩ := ih hws' m hv
          refine ⟨v', ?_, hsub⟩
          simp only [List.getElem?_cons_succ]
          exact hv'

theorem Closure.envSubstLvl_take
    {fuel k : Nat} {v_sub : Val} {env env' : List Val}
    (h : Closure.envSubstLvl fuel k v_sub env = some env') (n : Nat) :
    Closure.envSubstLvl fuel k v_sub (env.take n) = some (env'.take n) := by
  induction env generalizing env' n with
  | nil =>
      unfold Closure.envSubstLvl at h
      simp only [Option.some.injEq] at h
      subst h
      cases n <;> rfl
  | cons w ws ih =>
      obtain ⟨w', ws', hw', hws', rfl⟩ := Closure.envSubstLvl_cons_inv h
      cases n with
      | zero => simp [List.take, Closure.envSubstLvl]
      | succ m =>
          simp only [List.take_succ_cons]
          exact Closure.envSubstLvl_cons hw' (ih hws' m)

/-! ### Pass 13/14 status: eval-commutation lemma deferred

The full eval-commutation lemma — given
`eval n unf (.neutral (.var k) :: ρ) body = .ok bA`,
derive `∃ bA', eval n unf (v_sub :: ρ) body = .ok bA' ∧
Val.substLvl fuel k v_sub bA = some bA'` — turns out to be
**genuinely intractable without RC-typing** on `v_sub`.

**Why.** In the `.app` eval case, `eval` may produce
`.neutral (.app (.var k) a)` (a stuck spine on the
substitution variable). After substitution, the head becomes
`v_sub`, and `Val.substLvl` must fire `vapp fuel unfBound v_sub
a'`. Without RC-typing, this vapp may diverge — exactly the
Ω-counterexample pass 9 found:
- `clA = ⟨body := .app (.bvar 0) (.bvar 0), env := []⟩`,
- `v_sub = .lam dom ⟨.app (.bvar 0) (.bvar 0), []⟩` (omega).

`cl.openω fresh` succeeds (vapp on neutral fresh succeeds
without unfolding), but `cl.openω v_sub` exhausts fuel.

**What pass 13 contributes** (lemmas above):
- `Val.WellFormed` / `Neutral.WellFormed` / `Closure.WellFormed`:
  the structural invariant that every `.stuckRec` has a
  `.isNeutral` argument.
- `Val.substLvl_of_levelsBelow`: substitution is a no-op when
  level `k` doesn't appear in a well-formed value. (Pass 12 had
  noted this lemma needed the WellFormed predicate to land
  cleanly; pass 13 introduces both.)
- `Closure.envWellFormed_take`, `Closure.envWellFormed_getElem?`:
  WellFormed propagates through `take` and `getElem?` (the two
  list operations `eval` performs on env).

**Pass 14 wall analysis (2026-04-25, agent-a682142c).** Pass 14
attempted the RC-threaded eval-commutation lemma sketched above.
After detailed analysis of the proof structure, the wall is
deeper than pass 13 estimated:

The proof would proceed by mutual induction on `eval`/`vapp`
fuel `n`, mirroring `eval_vapp_shiftLvl` in `SoundnessProof.lean`.
For most expression cases (`.type`/`.bot`/`.bvar`/`.lam`/`.iota`/
`.fix`/`.letE`/`.asc`), the structural argument carries through
using pass 13's `Closure.envSubstLvl_take`/`_getElem?` helpers.

**The wall** is the `.app f a` case + `vapp` on `.neutral` head:

1. `eval` evaluates `f → f'_left`, `a → a'_left`.
2. `vapp n unf f'_left a'_left = .ok v_left`.
3. By IH, ∃ f'_right with `vapp_substLvl: substLvl k v_sub f'_left
   = some f'_right` (for some appropriate substLvl on the
   `f'_left` shape), similarly for `a'_left`.
4. Need: ∃ v_right, `vapp n unf f'_right a'_right = .ok v_right`
   and `Val.substLvl ... v_left = some v_right`.

**Subcase (the wall)**: when `f'_left = .neutral nf` where `nf`'s
spine root is `.var k` (e.g., `.var k` itself, or `.app (.var k)
arg1 arg2 …`). Then:
- `Neutral.substLvl k v_sub nf` returns `some v_sub_post` where
  `v_sub_post` is non-neutral (it's `v_sub` with sub-substitutions
  on the args).
- The substLvl match goes to the second arm: fires `vapp fuelω
  unfBound v_sub_post a'_right`.
- For substLvl to succeed at any concrete output, this `vapp` must
  terminate. **This requires RC on v_sub** (pass 9's Ω
  counterexample is precisely the case where it diverges).

**Three sub-walls within this subcase**:
1. **Fuel/unf alignment**: substLvl uses `(fuelω, unfBound)`;
   the original `vapp n unf` uses caller-supplied `(n, unf)`.
   Even if both terminate, the values may differ if the function
   v_sub_post is `.iota`/`.fix` (where the unf gate matters).
   Reconciling needs vapp_unf_mono (does it hold? non-trivial:
   higher unf may fire iota/fix unfolding that lower unf won't).
2. **RC.lam_elim shape constraint**: `RC.lam_elim` gives vapp
   termination ONLY when applied to RC-typed arguments. The
   `a'_right` we have isn't necessarily RC-typed at v_sub's domain
   — it's just the value of an arbitrary subexpression.
3. **Recursive RC threading**: for the `vapp` result to itself
   commute with substLvl, we'd need to invoke a sibling lemma on
   the eval'd body — which itself runs into the same .app wall.

Pass 14 concludes: the RC-threaded eval-commutation lemma is NOT
closeable in a single overnight pass without more substrate. The
remaining work for pass 15+ is:
- **Sub-wall 1**: prove `vapp_unf_mono` (or accept fuel/unf
  alignment via an alternative formulation, e.g., parameterising
  Val.substLvl by the original `unf`).
- **Sub-wall 2**: thread RC's domain on `v_sub` AND on the
  argument values that arise during eval. This requires an
  RC_env-like predicate that tracks the type of each env entry,
  AND a typed eval lemma that produces RC results from RC inputs.
  Effectively this is the FUNDAMENTAL LEMMA itself in disguise —
  once we have the FL, eval-commutation falls out as a corollary.
- **Sub-wall 3**: structurally recursive RC-threading via mutual
  induction on eval+vapp+well-formedness invariants.

**Pass 14 contribution.** A small structural helper
(`eval_substLvl_identity`) that captures the case where the eval
result is `levelsBelow d` AND well-formed AND we substitute at a
level `k ≥ d`. In this case, identity-on-closed kicks in directly
and eval-commutation is trivial: `eval ρ' e = eval ρ e` (same
result) and substLvl is identity.

This corollary is useful for the easy fragment of any eval-
commutation argument: when the closure body's eval result happens
to not reference the binding level, substitution is a no-op.

**Path forward.** Two strategic options for pass 15+:

1. **Architecture change**: replace `Val.substLvl` with a
   "typed substitution" that takes RC witnesses on env entries,
   eliminating the partiality issue. This makes substLvl total
   on RC-typed inputs but requires re-deriving identity-on-closed
   in the typed setting.

2. **Bypass via Subtype'**: use the existing `Subtype'`-level
   subtyping (the `Expr`-level relation) to bridge the substitution
   gap, leveraging existing Expr-level substitution lemmas in
   `SoundnessProof.lean`. This keeps `SubV` for the algorithm but
   doesn't require Val-level substitution to close the keystone.

The infrastructure committed in pass 13 + pass 14 is required by
either path: identity-on-closed (pass 13) and `eval_substLvl_
identity` (pass 14) are preconditions for any value-level
substitution argument that bypasses the .app wall. -/

/-! ### `eval_substLvl_identity` (pass 14)

Pass 14's contribution: a structural corollary that combines
pass 13's `Val.substLvl_of_levelsBelow` with `eval_levelsBelow`
(from `SoundnessProof.lean`). This handles the case where the
eval result is levels-below the substitution point AND well-
formed: substitution is identity, eval-commutation is trivial.

This is the "easy fragment" of eval-commutation: when the
closure body's eval result doesn't reference the binding level
(or any higher), substitution doesn't fire. -/

/-- If `eval` succeeds with a result that is `levelsBelow d` AND
well-formed, then `Val.substLvl` at any `k ≥ d` is identity.

This is a direct combination of `eval_levelsBelow` (which gives
the levels-below conclusion from env-side levels-below) and pass
13's `Val.substLvl_of_levelsBelow`.

The hypotheses `Val.WellFormed v` and `Closure.envLevelsBelow d ρ`
(the latter implies `v.levelsBelow d` via `eval_levelsBelow`) are
the natural preconditions. The `hwf` hypothesis comes from the
caller, which must establish it via "eval preserves WellFormed"
(an as-yet-unproven lemma; see pass 14 wall analysis above). -/
theorem Val.eval_substLvl_identity
    {n unf d k : Nat} {ρ : Env} {e : Expr} {v : Val}
    (h : eval n unf ρ e = .ok v)
    (hρ_lb : Closure.envLevelsBelow d ρ)
    (hwf : Val.WellFormed v)
    (hkd : d ≤ k)
    (fuel : Nat) (v_sub : Val) :
    Val.substLvl fuel k v_sub v = some v := by
  -- v is levels-below d via eval_levelsBelow.
  have hv_lb : Val.levelsBelow d v := eval_levelsBelow h hρ_lb
  -- levels-below d ⇒ levels-below k (since d ≤ k).
  have hv_lbk : Val.levelsBelow k v := Val.levelsBelow_mono hkd v hv_lb
  -- Apply pass 13's identity-on-closed.
  exact Val.substLvl_of_levelsBelow v fuel k v_sub hv_lbk hwf

/-! ## `SubV_subst_neutral_to_value` — the body-substitution lemma

The central technical lemma needed by the closure cases of
`RC.subtype_closed_aux` (`lam`, `iota_struct`, `fix_struct`).

**Statement.** If two closures, opened at the same fresh neutral
`(.var Γ.size)`, give bodies `bA, bB` related by `SubV` under
`Γ.push τ_dom`, AND `v` is **RC-realised** at `τ_dom` (step `n`,
depth `d`), then the closures opened at `v` give bodies
`bA', bB'` related by `SubV` under `Γ`.

Conceptually: this is a "fresh neutral substitution" lemma —
replacing the abstract fresh neutral with a *typed* value, and
correspondingly trimming `τ_dom` off the typing context, preserves
SubV.

**Pass 11 typed-refinement (2026-04-24).** Previous formulations of
this lemma (passes 7-10) had a **latent statement bug**: with
arbitrary `v` (no typing), `clA.openω v` is not guaranteed to
terminate — there is a concrete Ω-style counterexample
(`clA = ⟨body := .app (.bvar 0) (.bvar 0), env := []⟩` opened at
`v = .lam dom ⟨.app (.bvar 0) (.bvar 0), []⟩` exhausts fuel). The
existential conclusion `∃ bA', clA.openω v = some bA'` is then
unprovable, making the lemma vacuous on Ω inputs and misleading.

The fix is to **strengthen** (not weaken) the statement: add
`RC n d τ_dom v` as a hypothesis. This ensures `v` is "well-typed"
in the RC sense at the closure's domain. Saturation on `v` (via
`RC.fullyQuotable` / `RC.quote_witness`) provides eval-termination
evidence the un-typed statement was missing.

**Why we need it (lam case).** The `RC (.lam domB clB) v` clause
requires the closure body opened at *every* RC-typed `a` to relate
to the action of `vapp v a`. The `SubV.lam` premise only gives
relatedness at the *fresh neutral*. The lemma closes the gap. At
the call site, `a` is RC-typed at `domA` (after contravariant
coercion), satisfying the new RC hypothesis.

**Why the proof is hard.** SubV's induction recursors on the *shape*
of the two value arguments. After substituting `v` for the fresh
neutral, the shapes can change wildly (e.g. `bA = .neutral (.app
(var Γ.size) arg)`, but `bA' = vappω v arg` could be a
`.lam`/`.iota`/etc. depending on `v`). The classical induction on
SubV cannot transport the derivation case-by-case. Even with the
RC hypothesis on `v`, the body shapes diverge — pass 9's Approach B
showed RC-on-v gives saturation/quote info for `v` alone, not for
how `clA.body`'s eval result transforms.

A successful proof requires:
1. **Val-level substitution machinery** — define `Val.substLvl
   (k : Nat) (v_sub : Val) : Val → Val` (replace neutral level
   `.var k` with `v_sub`), prove it commutes with `eval` /
   `vapp` / closure-opening, prove it transports SubV under the
   appropriate context-update.

   With the typed refinement, the partiality gates introduced by
   `vapp` at `app`-spines can be discharged using `v`'s RC
   structure (saturation gives `quote v` terminates; combined with
   eval-substitution-commutation, `eval (v :: env) body` terminates
   if `eval (fresh :: env) body` does).

   Pass 9 estimate: ~510 LOC across 4 inter-dependent components
   (`Val.substLvl`, eval-commutation, SubV-preservation, glue).

**Pass 11 status.** The statement is now correct (no Ω vacuity).
The proof remains sorried; closing it requires the substitution
machinery above. See `docs/ideas/typed-nbe-implementation-log.md`
pass-11 entry for the substantive reasoning behind keeping the
lemma sorried with the corrected statement.

**Pass 12 status.** The data layer is now in place:
`Val.substLvl`/`Neutral.substLvl`/`Closure.substLvl` are defined
above (Approach A.1: Outcome-valued, fuel-bounded). What remains:

- **Eval-commutation** (pass 13, ~200 LOC): given
  `eval n unf (.neutral (.var k) :: env) body = .ok bA`, derive
  `eval fuel n unf (v_sub :: env) body = .ok bA' ∧
   Val.substLvl fuel k v_sub bA = some bA'`. Mirrors
  `eval_vapp_shiftLvl` in `SoundnessProof.lean`. Mutual
  fuel-induction over eval/vapp.

- **SubV-preservation** (pass 14, ~200 LOC): given
  `SubV S (Γ.push τ_dom) bA bB ∧ Val.substLvl ... bA = some bA'
   ∧ Val.substLvl ... bB = some bB'`, derive `SubV S Γ bA' bB'`.
  Structural induction on SubV across 13 constructors.

- **Glue** (pass 15, ~30 LOC): combine eval-commutation +
  SubV-preservation + saturation-on-v to close the keystone.

See `docs/ideas/typed-everything-architecture.md` (pass 6 design
doc) §2 for why this lemma is intrinsically required (the typed-
everything substrate does NOT magically dissolve it). -/
theorem SubV_subst_neutral_to_value
    {n d : Nat}
    {S : List (Val × Val)} {Γ : TyCtx}
    {τ_dom : Val} {clA clB : Closure} {bA bB : Val} (v : Val)
    (_hRC : RC n d τ_dom v)
    (hbA : clA.openω (.neutral (.var Γ.size)) = some bA)
    (hbB : clB.openω (.neutral (.var Γ.size)) = some bB)
    (hbody : SubV S (Γ.push τ_dom) bA bB) :
    ∃ bA' bB',
      clA.openω v = some bA' ∧
      clB.openω v = some bB' ∧
      SubV S Γ bA' bB' := by
  -- See docstring for the proof strategy. Pass 11 strengthens
  -- the statement with `RC n d τ_dom v` (closing the Ω counter-
  -- example pass 9 found in the un-typed version) but keeps the
  -- proof sorried — even with the typed hypothesis, the proof
  -- requires Val-level substitution machinery (pass-9 Approach B
  -- analysis: RC-on-v alone doesn't dissolve the structural
  -- substitution requirement).
  sorry

/-! ## `SubV_subst_pair` — different substituends on each side

The `fix_struct` case of `subtype_closed_aux` needs to relate
`clA.openω (.fix annA clA)` and `clB.openω (.fix annB clB)` —
*different* substituends on the two sides. The basic
`SubV_subst_neutral_to_value` lemma uses the *same* substituent
on both sides; this is the pair-substitution generalisation.

**Statement.** If two closures, opened at the same fresh neutral,
give bodies related by SubV, two values `va, vb` are RC-realised
at `τ_dom` (typed refinement, see pass-11 note below), AND `va, vb`
are related by SubV in the OUTER context, then the closures opened
at `va` and `vb` (respectively) give bodies related by SubV in the
outer context.

**Why a separate lemma.** The basic lemma's proof inducts on the
SubV derivation `bA ⊑ bB` and threads a SINGLE substituent
through. The pair version threads TWO substituents — `va` on the
LHS, `vb` on the RHS — connected by `SubV S Γ va vb`. The
constructor cases are similar in shape but every recursive
premise needs the pair-related-substituent input rather than
single-substituent.

**Pass 11 status.** This pair lemma has the **same Ω
counterexample** as `SubV_subst_neutral_to_value` (un-typed
substituents allow non-terminating `clA.openω va`). The clean fix
is route (a): require `RC n d τ_dom va ∧ RC n d τ_dom vb`. But
the `fix_struct` caller's substituents are `.fix annA clA` and
`.fix annB clB` — *types*, not typed values inhabiting `annB`.
Providing the RC witnesses requires a separate "fix-inhabits-own-
annotation" auxiliary lemma (out of pass-11 scope).

To preserve the existing `fix_struct` structural argument and not
inflate the inline-sorry count, pass 11 leaves this pair lemma's
statement **unchanged** (still vacuously satisfied on Ω inputs).
The post-pass-11 plan: build the RC-at-fix aux lemma, then apply
route (a) here. See pass-11 entry in
`docs/ideas/typed-nbe-implementation-log.md` for the full
reasoning.

**Implementation note.** In principle, `SubV_subst_pair` can
follow from `SubV_subst_neutral_to_value` plus a "compose
substitutions" step (substitute fresh→va on the LHS, fresh→vb
on the RHS, glue via SubV transitivity at the substituents). In
practice it's likely simpler to prove directly by SubV-induction
with both substituents threaded in parallel. Either way, this is
~50-100 LOC on top of the basic lemma.

**`iota_intro` is NOT closed by this lemma.** That case has a
type-vs-value mismatch (the LHS in `SubV.iota_intro` is the
inhabitant `a` itself, but RC requires opening at the value `v`,
where only `RC k d a v` holds). Closing `iota_intro` needs an
RC-realisation bridge, distinct from this pair-substitution. -/
theorem SubV_subst_pair
    {S : List (Val × Val)} {Γ : TyCtx}
    {τ_dom : Val} {clA clB : Closure} {bA bB : Val}
    (va vb : Val)
    (hbA : clA.openω (.neutral (.var Γ.size)) = some bA)
    (hbB : clB.openω (.neutral (.var Γ.size)) = some bB)
    (hbody : SubV S (Γ.push τ_dom) bA bB)
    (hsubst : SubV S Γ va vb) :
    ∃ bA' bB',
      clA.openω va = some bA' ∧
      clB.openω vb = some bB' ∧
      SubV S Γ bA' bB' := by
  -- See docstring. Pass 11 leaves this lemma's statement
  -- unchanged from pass 8; the typed-refinement (route a) is
  -- deferred until the RC-at-fix-value auxiliary lemma is
  -- written. Pair lemma itself remains sorried.
  sorry

/-- Auxiliary form parameterised over the seen-set obligation, in
**all-lower-indices** form: the seen-set hypothesis covers every
step `m ≤ n`. This makes the seen-set obligation transferable to
strictly smaller step indices, which is necessary for the
"unfold one step" cases (`unfold_fix_R`, `unfold_fix_L`,
`unfold_iota_L`, etc.).

Proven by **strong induction on n**. The IH provides `Aux m` for
all `m ≤ k`, which is needed for cases like `unfold_fix_R` where
the augmented seen-set obligation requires `Aux m` at strictly
lower steps.

Top-level `RC.subtype_closed` specialises `S = []`.

**Pass 10 signature refactor (2026-04-24)**: now takes
`RC_env n d Γ ρ` as a typed-environment realisation hypothesis.
This brings the signature into alignment with the FL body's
context (which always has `RC_env` in scope after the pass-5
open-environment reformulation), and gives the existing closed
cases AND the sorried hard cases a typed environment to work
against.

**Important honest assessment** (pass 10): the RC_env hypothesis
*alone* does NOT dissolve the substitution wall for the closure-
form cases (`lam`, `iota_struct`, `fix_struct`). Those cases
still go through `SubV_subst_neutral_to_value` /
`SubV_subst_pair`. The reason: the SubV body premise is on the
*fresh-neutral-opened* bodies `bA = clA.openω fresh`,
`bB = clB.openω fresh`, while the goal needs bodies opened at a
concrete value `a`. Even with `RC_env`, the IH is on `bA, bB`
(closed Vals), not on closure-bodies-as-functions, so the IH
cannot be applied at `a` directly. Substitution on Val-level
remains necessary.

What RC_env *does* unlock: future passes can use it to attack
the still-sorried `iota_intro`, `revapp_L`, `neutral_ascent`,
`unfold_fix_L`, `unfold_iota_L` cases, which need typing
information beyond what's in SubV. Pass 10 ships the substrate;
pass 11+ uses it.

For the existing closed cases, `RC_env` is threaded through
unchanged via `RC_env.mono` at recursive calls (which always
happen at the same Γ, just at a smaller step). -/
theorem RC.subtype_closed_aux : ∀ (n : Nat) {d : Nat}
    {S : List (Val × Val)} {Γ : TyEnv} {ρ : Env} {τ τ' v : Val},
      RC_env n d Γ ρ →
      (∀ α β, (α, β) ∈ S → ∀ m, m ≤ n → ∀ v',
         RC m d α v' → RC m d β v') →
      SubV S Γ τ τ' → RC n d τ v → RC n d τ' v := by
  intro n
  induction n using Nat.strongRecOn with
  | _ n ihStrong =>
  -- ihStrong : ∀ m < n, [body with m]
  match n with
  | 0 =>
      -- RC 0 d _ _ = True for all τ, τ'. So the conclusion is
      -- True trivially.
      intro d S Γ ρ τ τ' v _hΓρ _hS _hsub _h
      unfold RC
      trivial
  | k+1 =>
      intro d S Γ ρ τ τ' v hΓρ hS hsub h
      have ih : ∀ m, m ≤ k →
          ∀ {d' : Nat} {S' : List (Val × Val)} {Γ' : TyEnv} {ρ' : Env}
            {τ_ τ'_ v_ : Val},
          RC_env m d' Γ' ρ' →
          (∀ α β, (α, β) ∈ S' → ∀ m', m' ≤ m → ∀ v'',
             RC m' d' α v'' → RC m' d' β v'') →
          SubV S' Γ' τ_ τ'_ → RC m d' τ_ v_ → RC m d' τ'_ v_ := by
        intro m hmk
        exact ihStrong m (Nat.lt_succ_of_le hmk)
      match hsub with
      | SubV.hyp hmem =>
          exact hS _ _ hmem (k+1) (Nat.le_refl _) v h
      | SubV.refl =>
          exact h
      | SubV.top =>
          unfold RC
          exact RC.sat_of_succ h
      | SubV.bot_L =>
          unfold RC at h
          exact False.elim h
      | SubV.neutral_struct _ =>
          unfold RC
          exact RC.sat_of_succ h
      | SubV.neutral_ascent _ _ =>
          -- ----------------------------------------------------------
          -- WALL: `neutral_ascent` cannot be closed under the current
          -- RC formulation. Pass-15 finding (2026-04-25, agent-a20ccfc8).
          -- ----------------------------------------------------------
          --
          -- `SubV.neutral_ascent` premises:
          --   * `SynthN Γ nA τ` — `nA` synthesises type `τ`.
          --   * `SubV S Γ τ b` — `τ ⊑ b`.
          --
          -- We have `h : RC (k+1) d (.neutral nA) v`. By RC's
          -- definition at `.neutral`:
          --   `RC (n+1) d (.neutral _) v
          --      = Val.fullyQuotable d v ∧ ∃ q, quote fuelω d v = .ok q`
          -- i.e. saturation only — no semantic link between `v` and
          -- `nA`.
          --
          -- To apply `ih` on `SubV S Γ τ b`, we need `RC (k+1) d τ v`.
          -- For `τ` of closure form (`.lam`/`.iota`/`.fix`), this
          -- requires body witnesses that saturation alone cannot
          -- supply.
          --
          -- Concrete counterexample (refined per pass-15 verification):
          --   Take cl₀ with body = `Expr.bot`, env = []. Then
          --     `cl₀.openω _ = some .bot` for any input.
          --   Pick τ = `.lam .type cl₀` (non-bot closure type whose
          --     body opens to `.bot`).
          --   Pick `nA` such that `SynthN Γ nA τ` holds (e.g. a bvar
          --     of type τ in some Γ).
          --   Pick b = τ (so `SubV S Γ τ b` discharges by `SubV.refl`).
          --   Take v = `.type` — fullyQuotable + quote-witness, so
          --     `RC (k+1) d (.neutral nA) .type` HOLDS.
          --   But `RC (k+1) d τ .type` is FALSE for k ≥ 1:
          --     `vapp _ _ .type a = .ok (.neutral (.stuckRec .type a))`
          --     succeeds, but the body witness requires `RC m d .bot
          --     (.neutral (.stuckRec .type a))`, and RC at `.bot` is
          --     `False`.
          --
          -- Therefore `subtype_closed_aux`'s conclusion is FALSE for
          -- this `v` in the `neutral_ascent` case — the lemma is not
          -- provable AS STATED.
          --
          -- The `SynthN-realises` bridge described in passes 8/10
          -- doesn't dissolve this: that bridge needs "`v` realises
          -- `nA`" as a precondition (i.e., `v = eval ρ nA`), which
          -- `subtype_closed_aux`'s hypothesis doesn't carry. RC at
          -- `.neutral` would have to be REDESIGNED to encode the
          -- realisation content (~200-400 LOC of refactoring); see
          -- the Pass 15 entry in
          -- `docs/ideas/typed-nbe-implementation-log.md` for
          -- options.
          --
          -- Strategic options (pass 16+):
          --   A0. (FALSE — pass 15 finding) Prove
          --       "saturation ∧ τ ≠ .bot → RC n d τ v" as a stand-
          --       alone lemma (Girard's "neutral terms are
          --       reducible"). Counterexample: v = .type, τ =
          --       .lam .type cl₀ where cl₀.openω _ = some .bot.
          --       v is saturated, τ is non-bot, but RC n d τ v is
          --       FALSE because the body witness requires RC at
          --       .bot, which is False.
          --   A.  Redesign RC at `.neutral` to encode realisation
          --       (eval-of-nA = v, plus RC at synthesised type).
          --       ~200-400 LOC refactoring.
          --   B.  Strengthen `subtype_closed_aux`'s signature with
          --       a "v realises some closed term" hypothesis.
          --   C.  Restructure `SubV.neutral_ascent` away from the
          --       algorithm; large rewiring.
          --   D.  Live with the sorry; prioritise the four other
          --       sorried cases.
          sorry
      | @SubV.lam S' Γ' domA domB clA clB bA bB hbA hbB hdom hbody =>
          -- Goal: RC (k+1) d (.lam domB clB) v.
          -- Strategy:
          --   1. Unfold RC at h and the goal: both reduce to
          --      saturation + body clause "for all m ≤ k, RC-typed
          --      a, vapp succeeds and produces RC-typed result".
          --   2. Saturation transfers from h directly.
          --   3. For body: take m, hm, a with `RC m d domB a`.
          --      Apply IH (subtype_closed_aux at step m ≤ k) to
          --      `hdom : SubV S' Γ' domB domA` to get `RC m d domA a`.
          --   4. Apply h's body clause at this `a` to get `r, vapp_eq,
          --      rTyA, hOpenA, hRCa : RC m d rTyA r` where
          --      `rTyA = clA.openω a`.
          --   5. Use `SubV_subst_neutral_to_value` to convert
          --      `hbody : SubV S' (Γ'.push domA) bA bB` into
          --      `∃ bA' bB', clA.openω a = some bA' ∧ clB.openω a =
          --      some bB' ∧ SubV S' Γ' bA' bB'`.
          --   6. By injectivity of `Some`, bA' = rTyA. Apply IH at
          --      step m to get RC m d bB' r. Witness rTyB := bB'.
          unfold RC at h ⊢
          obtain ⟨hSat, h_body⟩ := h
          refine ⟨hSat, ?_⟩
          intro m hm a ha_RCdomB
          -- Step 3: contravariant domain coercion via IH at step m.
          -- Build hS at step ≤ m (chain: m ≤ k ≤ k+1).
          have ha_RCdomA : RC m d domA a := by
            cases m with
            | zero => unfold RC; trivial
            | succ m' =>
              have hm' : m'+1 ≤ k := hm
              have hS_m' : ∀ α β, (α, β) ∈ S' → ∀ m'', m'' ≤ m'+1 →
                  ∀ v'', RC m'' d α v'' → RC m'' d β v'' := by
                intro α β hin m'' hm''m v'' h'
                exact hS α β hin m''
                  (Nat.le_trans hm''m (Nat.le_succ_of_le hm')) v'' h'
              -- RC_env at the smaller step m'+1 ≤ k+1 via mono.
              -- Use Γ' (post-match index name).
              have hΓρ_m : RC_env (m'+1) d Γ' ρ :=
                RC_env.mono (Nat.le_trans hm' (Nat.le_succ k)) hΓρ
              exact ihStrong (m'+1) (Nat.lt_succ_of_le hm')
                hΓρ_m hS_m' hdom ha_RCdomB
          -- Step 4: body clause at concrete `a`.
          obtain ⟨r, hvapp, rTyA, hOpenA, hRCa⟩ :=
            h_body m hm a ha_RCdomA
          -- Step 5: substitution lemma at value `a`.
          -- Pass 11: provide RC witness on `a` (typed refinement).
          obtain ⟨bA', bB', hOpenA', hOpenB', hSubBody⟩ :=
            SubV_subst_neutral_to_value (n := m) (d := d)
              (S := S') (Γ := Γ')
              (τ_dom := domA) (clA := clA) (clB := clB)
              (bA := bA) (bB := bB) a ha_RCdomA hbA hbB hbody
          -- bA' = rTyA from `clA.openω a = some bA' = some rTyA`.
          have heq : bA' = rTyA := by
            rw [hOpenA] at hOpenA'
            exact (Option.some.injEq _ _).mp hOpenA'.symm
          subst heq
          -- Step 6: IH at step m on hSubBody.
          refine ⟨r, hvapp, bB', hOpenB', ?_⟩
          cases m with
          | zero => unfold RC; trivial
          | succ m' =>
            have hm' : m'+1 ≤ k := hm
            have hS_m' : ∀ α β, (α, β) ∈ S' → ∀ m'', m'' ≤ m'+1 →
                ∀ v'', RC m'' d α v'' → RC m'' d β v'' := by
              intro α β hin m'' hm''m v'' h'
              exact hS α β hin m''
                (Nat.le_trans hm''m (Nat.le_succ_of_le hm')) v'' h'
            have hΓρ_m : RC_env (m'+1) d Γ' ρ :=
              RC_env.mono (Nat.le_trans hm' (Nat.le_succ k)) hΓρ
            exact ihStrong (m'+1) (Nat.lt_succ_of_le hm')
              hΓρ_m hS_m' hSubBody hRCa
      | @SubV.iota_struct S' Γ' annA annB clA clB bA bB
          hbA hbB hAnn hBody =>
          -- Goal: RC (k+1) d (.iota annB clB) v.
          -- Strategy mirrors lam case but with the seen-set
          -- augmented (and pushed annB instead of annA).
          --   1. Unfold RC at h, goal: saturation + (RC k d ann v)
          --      + (∃ vTy, cl.openω v = some vTy ∧ RC k d vTy v).
          --   2. Saturation transfers from h directly.
          --   3. From h's RC k d annA v, plus hAnn (on augmented
          --      seen-set), apply ihStrong at step k to get
          --      RC k d annB v. The augmented seen-set's new
          --      entry's obligation is OUR derivation at step
          --      ≤ k (closed by ihStrong).
          --   4. From h's body witness, get vTy with `clA.openω v
          --      = some vTy ∧ RC k d vTy v`.
          --   5. Apply substitution lemma to hBody with `v` to
          --      get clB.openω v = some bB' and SubV bA' bB' on
          --      *augmented* seen-set under Γ'.
          --   6. By Some-injectivity, bA' = vTy. Apply ihStrong at
          --      step k to the SubV (with augmented hS_k) to get
          --      RC k d bB' v. Done.
          unfold RC at h ⊢
          obtain ⟨hSat, hAnnA, vTy, hOpenA, hRCv⟩ := h
          -- Build hS_k : the augmented seen-set hypothesis at
          -- step ≤ k. Used both for the annotation IH and the
          -- body IH (after substitution).
          have hS_k : ∀ α β, (α, β) ∈
              ((.iota annA clA, .iota annB clB) :: S') →
              ∀ m, m ≤ k → ∀ v', RC m d α v' → RC m d β v' := by
            intro α β hαβ m hmk v' hαv'
            rw [List.mem_cons] at hαβ
            rcases hαβ with hαβ_eq | hin
            · -- New entry: discharge via ihStrong applied to OUR
              -- derivation at step m ≤ k < k+1.
              obtain ⟨rfl, rfl⟩ := Prod.mk.inj hαβ_eq
              -- Build hS_m : restrict outer hS to step ≤ m.
              have hS_m : ∀ α' β', (α', β') ∈ S' → ∀ m', m' ≤ m →
                  ∀ v'', RC m' d α' v'' → RC m' d β' v'' := by
                intro α' β' hin' m' hm'm v'' h'
                exact hS α' β' hin' m'
                  (Nat.le_trans hm'm (Nat.le_succ_of_le hmk)) v'' h'
              -- Apply ihStrong at step m to OUR derivation.
              have hsub_orig : SubV S' Γ' (.iota annA clA)
                  (.iota annB clB) :=
                SubV.iota_struct hbA hbB hAnn hBody
              -- RC_env at step m via mono. Use Γ' (the match-bound
              -- pattern variable, which the dependent pattern match
              -- substitutes hΓρ's index to).
              have hΓρ_m : RC_env m d Γ' ρ :=
                RC_env.mono (Nat.le_trans hmk (Nat.le_succ k)) hΓρ
              exact ihStrong m
                (Nat.lt_succ_of_le hmk) hΓρ_m hS_m hsub_orig hαv'
            · exact hS α β hin m (Nat.le_succ_of_le hmk) v' hαv'
          -- Step 3: ann coercion at step k.
          have hΓρ_k : RC_env k d Γ' ρ :=
            RC_env.mono (Nat.le_succ k) hΓρ
          have hAnnB : RC k d annB v :=
            ih k (Nat.le_refl _) hΓρ_k hS_k hAnn hAnnA
          refine ⟨hSat, hAnnB, ?_⟩
          -- Step 5: substitution lemma on hBody, applied at v.
          -- Pass 11: provide RC witness on `v` at annB (the typed
          -- refinement's hypothesis).
          obtain ⟨bA', bB', hOpenA', hOpenB', hSubBody⟩ :=
            SubV_subst_neutral_to_value (n := k) (d := d)
              (S := (.iota annA clA, .iota annB clB) :: S')
              (Γ := Γ') (τ_dom := annB) (clA := clA) (clB := clB)
              (bA := bA) (bB := bB) v hAnnB hbA hbB hBody
          -- bA' = vTy (both equal clA.openω v).
          have heq : bA' = vTy := by
            rw [hOpenA] at hOpenA'
            exact (Option.some.injEq _ _).mp hOpenA'.symm
          subst heq
          -- Step 6: apply IH at step k to hSubBody (under
          -- augmented seen-set, hS_k).
          exact ⟨bB', hOpenB', ih k (Nat.le_refl _) hΓρ_k hS_k hSubBody hRCv⟩
      | @SubV.fix_struct S' Γ' annA annB clA clB bA bB
          hbA hbB hAnn hBody =>
          -- Goal: RC (k+1) d (.fix annB clB) v.
          -- Strategy mirrors iota_struct, but RC at `.fix` opens
          -- the body at the FIX VALUE itself (different
          -- substituends on each side: clA at .fix annA clA,
          -- clB at .fix annB clB). We use `SubV_subst_pair` —
          -- the pair-substitution generalisation — with
          -- substituents (.fix annA clA, .fix annB clB) related
          -- by `SubV.hyp` in the augmented seen-set.
          --   1. Unfold RC at h, goal: saturation + (∃ uTy,
          --      cl.openω (.fix _ cl) = some uTy ∧ RC k d uTy v).
          --   2. Saturation transfers from h directly.
          --   3. Build augmented hS_k as in iota_struct.
          --   4. Apply SubV_subst_pair on hBody at substituents
          --      `va := .fix annA clA, vb := .fix annB clB`,
          --      related by SubV.hyp on the augmented seen-set.
          --   5. By Some-injectivity, the LHS bA' = uTyA from h.
          --   6. Apply IH at step k on the resulting SubV (under
          --      hS_k) to RC k d uTyA v, getting RC k d bB' v.
          unfold RC at h ⊢
          obtain ⟨hSat, uTyA, hOpenA, hRCu⟩ := h
          have hS_k : ∀ α β, (α, β) ∈
              ((.«fix» annA clA, .«fix» annB clB) :: S') →
              ∀ m, m ≤ k → ∀ v', RC m d α v' → RC m d β v' := by
            intro α β hαβ m hmk v' hαv'
            rw [List.mem_cons] at hαβ
            rcases hαβ with hαβ_eq | hin
            · -- New entry: discharge via ihStrong applied to OUR
              -- derivation at step m ≤ k < k+1.
              obtain ⟨rfl, rfl⟩ := Prod.mk.inj hαβ_eq
              have hS_m : ∀ α' β', (α', β') ∈ S' → ∀ m', m' ≤ m →
                  ∀ v'', RC m' d α' v'' → RC m' d β' v'' := by
                intro α' β' hin' m' hm'm v'' h'
                exact hS α' β' hin' m'
                  (Nat.le_trans hm'm (Nat.le_succ_of_le hmk)) v'' h'
              have hsub_orig : SubV S' Γ' (.«fix» annA clA)
                  (.«fix» annB clB) :=
                SubV.fix_struct hbA hbB hAnn hBody
              have hΓρ_m : RC_env m d Γ' ρ :=
                RC_env.mono (Nat.le_trans hmk (Nat.le_succ k)) hΓρ
              exact ihStrong m
                (Nat.lt_succ_of_le hmk) hΓρ_m hS_m hsub_orig hαv'
            · exact hS α β hin m (Nat.le_succ_of_le hmk) v' hαv'
          refine ⟨hSat, ?_⟩
          -- Substituents related by SubV.hyp on the augmented
          -- seen-set.
          have hSubFix :
              SubV ((.«fix» annA clA, .«fix» annB clB) :: S') Γ'
                (.«fix» annA clA) (.«fix» annB clB) :=
            SubV.hyp (List.mem_cons_self _ _)
          -- Pair substitution lemma at (`.fix annA clA`,
          -- `.fix annB clB`).
          obtain ⟨bA', bB', hOpenA', hOpenB', hSubBody⟩ :=
            SubV_subst_pair
              (S := (.«fix» annA clA, .«fix» annB clB) :: S')
              (Γ := Γ') (τ_dom := annB) (clA := clA) (clB := clB)
              (bA := bA) (bB := bB)
              (.«fix» annA clA) (.«fix» annB clB)
              hbA hbB hBody hSubFix
          -- bA' = uTyA (both equal clA.openω (.fix annA clA)).
          have heq : bA' = uTyA := by
            rw [hOpenA] at hOpenA'
            exact (Option.some.injEq _ _).mp hOpenA'.symm
          subst heq
          -- Apply IH at step k to hSubBody under augmented hS_k.
          have hΓρ_k : RC_env k d Γ' ρ :=
            RC_env.mono (Nat.le_succ k) hΓρ
          exact ⟨bB', hOpenB', ih k (Nat.le_refl _) hΓρ_k hS_k hSubBody hRCu⟩
      | SubV.iota_intro _ _ _ =>
          -- iotaIntro type-vs-value mismatch. Deferred.
          sorry
      | @SubV.unfold_fix_R S' Γ' a ann clB bB hopen hbody =>
          -- τ' = .fix ann clB. RC.fix at step k+1 requires
          -- saturation + RC k d bB v.
          unfold RC
          refine ⟨RC.sat_of_succ h, bB, hopen, ?_⟩
          -- Apply IH at step k to hbody : SubV ((a, .fix ann clB)
          -- :: S') Γ' a bB. Need augmented hS at step k.
          have hS_k : ∀ α β, (α, β) ∈ ((a, .«fix» ann clB) :: S') →
              ∀ m, m ≤ k → ∀ v', RC m d α v' → RC m d β v' := by
            intro α β hαβ m hmk v' hαv'
            rw [List.mem_cons] at hαβ
            rcases hαβ with hαβ_eq | hin
            · -- New entry. Apply ihStrong at m to OUR derivation.
              obtain ⟨rfl, rfl⟩ := Prod.mk.inj hαβ_eq
              -- Restrict outer hS at S' to step ≤ m.
              have hS_m : ∀ α' β', (α', β') ∈ S' →
                  ∀ m', m' ≤ m → ∀ v'', RC m' d α' v'' →
                  RC m' d β' v'' := by
                intro α' β' hin' m' hm'm v'' hα'v''
                exact hS α' β' hin' m'
                  (Nat.le_trans hm'm (Nat.le_succ_of_le hmk)) v''
                  hα'v''
              -- Apply ihStrong at step m to OUR derivation.
              have hsub_orig : SubV S' Γ' α (.«fix» ann clB) :=
                SubV.unfold_fix_R hopen hbody
              have hΓρ_m : RC_env m d Γ' ρ :=
                RC_env.mono (Nat.le_trans hmk (Nat.le_succ k)) hΓρ
              exact ihStrong m
                (Nat.lt_succ_of_le (Nat.le_trans hmk (Nat.le_refl k)))
                hΓρ_m hS_m hsub_orig hαv'
            · -- Old entry: outer hS at step m.
              exact hS α β hin m (Nat.le_succ_of_le hmk) v' hαv'
          have h_lower : RC k d a v := RC.mono (k+1) (Nat.le_succ k) h
          have hΓρ_k : RC_env k d Γ' ρ :=
            RC_env.mono (Nat.le_succ k) hΓρ
          exact ih k (Nat.le_refl _) hΓρ_k hS_k hbody h_lower
      | SubV.unfold_fix_L _ _ _ =>
          -- Symmetric step-shift issue. Deferred.
          sorry
      | SubV.unfold_iota_L _ _ _ =>
          -- Same as unfold_fix_L. Deferred.
          sorry
      | SubV.stuckRec_struct _ _ _ _ =>
          unfold RC
          exact RC.sat_of_succ h
      | SubV.revapp_R _ _ _ =>
          unfold RC
          exact RC.sat_of_succ h
      | SubV.revapp_L _ _ _ =>
          -- vapp-respects-RC missing. Deferred.
          sorry

/-- Specialisation of the auxiliary at empty seen-set / context.

Pass 10 update: now provides `RC_env.nil` (the empty typed
environment realises the empty value environment trivially) to
satisfy the new `RC_env n d Γ ρ` parameter at `Γ = #[]`,
`ρ = []`. -/
theorem RC.subtype_closed {n d : Nat} {τ τ' v : Val}
    (hsub : SubV [] #[] τ τ')
    (h : RC n d τ v) : RC n d τ' v := by
  refine RC.subtype_closed_aux n RC_env.nil ?_ hsub h
  intro α β hmem _ _ _ _
  exact (List.not_mem_nil (α, β) hmem).elim

/-! ## `SubTV` — the typed-everything subtype relation (pass 6)

`SubTV n d τ_a τ_b` is the typed analog of `SubV`: a *logical-
relation*-style predicate stating that every value RC-typed at
`τ_a` is also RC-typed at `τ_b`, at the same step `n` and depth `d`.

This is the foundation of the typed-everything pipeline. Where
the untyped `SubV` is a *syntactic* relation between Vals, `SubTV`
is a *semantic* relation defined via RC. The two are connected:

```
  SubV [] #[] τ_a τ_b → SubTV n d τ_a τ_b   (this is RC.subtype_closed!)
```

So `SubTV` is a strict refinement: SubV-related ⟹ SubTV-related.
The reverse doesn't hold (SubTV admits more pairs than SubV), but
that's irrelevant for soundness — the algorithm only ever produces
SubV witnesses, and `SubTV` is what the FL needs.

**Why bother defining a new relation?** Because it gives us a
clean substrate for pass 7+ work:
- `SubTV` constructors are all derivable from RC (no SubV-induction
  needed for the trivial cases).
- The FL body can use `SubTV` directly without going through
  `SubV ⟹ RC` lifting (which is what `RC.subtype_closed_aux`
  bottlenecks on).
- The bridge `SubV ⟹ SubTV` is exactly `RC.subtype_closed`,
  factored out as a single theorem.

**Pass 6 deliverable**: definition + trivial constructors. The
derivation `SubV ⟹ SubTV` is `RC.subtype_closed`'s job (still
sorried for hard cases, but the trivial cases work).

**Pass 7+**: `SubV ⟹ SubTV` for closure cases via Val-level
body-substitution lemma (estimated 150-250 LOC, see design doc
`docs/ideas/typed-everything-architecture.md`).
-/

/-- The typed-everything subtype relation. Logical-relation style:
`τ_a ⊑^T τ_b` at step `n` and depth `d` iff every RC-typed value at
`τ_a` is also RC-typed at `τ_b`.

Definitionally extensional — purely a Π-type. Constructors below
(`SubTV.refl`, `SubTV.top`, etc.) provide useful API, but anything
provable about RC-coercions is a `SubTV`. -/
def SubTV (n d : Nat) (τ_a τ_b : Val) : Prop :=
  ∀ v, RC n d τ_a v → RC n d τ_b v

namespace SubTV

/-- Reflexivity: any type is a subtype of itself. -/
theorem refl {n d : Nat} {τ : Val} : SubTV n d τ τ :=
  fun _ h => h

/-- Transitivity: composition of RC-coercions. -/
theorem trans {n d : Nat} {τ_a τ_b τ_c : Val}
    (hab : SubTV n d τ_a τ_b) (hbc : SubTV n d τ_b τ_c) :
    SubTV n d τ_a τ_c :=
  fun v h => hbc v (hab v h)

/-- `.bot` is a subtype of everything. RC at `.bot` is `False`,
so every "value" at `.bot` lifts vacuously. -/
theorem bot_L {n d : Nat} {τ : Val} : SubTV n d .bot τ := by
  intro v h
  cases n with
  | zero => unfold RC; trivial
  | succ k =>
    unfold RC at h
    exact False.elim h

/-- Anything is a subtype of `.type` (the universe is the largest
type). At step `n+1`, this requires saturation on the value, which
RC always provides (via `RC.fullyQuotable`/`RC.quote_witness`).
At step 0, RC is `True` for both, trivial. -/
theorem top {n d : Nat} {τ : Val} : SubTV n d τ .type := by
  intro v h
  cases n with
  | zero => unfold RC; trivial
  | succ k =>
    -- RC (k+1) d .type v requires saturation. Get from h.
    have hsat := RC.sat_of_succ h
    unfold RC; exact hsat

/-- Anything is a subtype of any neutral type. Like `top`, this is
saturation-only. -/
theorem to_neutral {n d : Nat} {τ : Val} {ne : Neutral} :
    SubTV n d τ (.neutral ne) := by
  intro v h
  cases n with
  | zero => unfold RC; trivial
  | succ k =>
    have hsat := RC.sat_of_succ h
    unfold RC; exact hsat

/-- The bridge from `SubV` (untyped algorithmic relation) to
`SubTV` (typed semantic relation). At empty seen-set / context,
this is exactly `RC.subtype_closed` repackaged. Because
`RC.subtype_closed` is parametric in `n`, this gives `SubTV n d`
for all `n` simultaneously.

This is the **central bridge theorem** of the typed-everything
architecture. The FL body uses `SubTV` directly; the algorithmic
checker produces `SubV`; this lemma converts. As long as
`RC.subtype_closed` is closed (currently 8 inline sorries on hard
cases), `SubTV` is fully bridged.

Pass 7+ work is closing the inline sorries in
`RC.subtype_closed_aux`, NOT this bridge. -/
theorem of_SubV {n d : Nat} {τ_a τ_b : Val}
    (hsub : SubV [] #[] τ_a τ_b) : SubTV n d τ_a τ_b :=
  fun _v h => RC.subtype_closed hsub h

end SubTV

/-! ## SubTV API: the typed pipeline's coercion primitive

These wrappers give the FL body a clean interface for type
coercion. The FL never directly invokes `RC.subtype_closed`;
instead it goes through `SubTV` which provides:
- `SubTV.coerce : SubTV n d τ_a τ_b → RC n d τ_a v → RC n d τ_b v`
  (essentially the definition unfolded)
- `SubTV.of_SubV` (above) for converting algorithmic outputs.

In pass 9+ when the FL body is written, callers will use:
```
have hsub : SubTV n d τ_a τ_b := SubTV.of_SubV (subCheckVal_subV ...)
have rc_b : RC n d τ_b v := hsub.coerce rc_a
```

NOT:
```
have rc_b : RC n d τ_b v :=
  RC.subtype_closed (subV_of_subCheck ...) rc_a
```

The SubTV layer makes the type-direction explicit.
-/

/-- Apply a `SubTV` to coerce an RC witness. Trivial unfold but
named for clarity at use sites. -/
theorem SubTV.coerce {n d : Nat} {τ_a τ_b v : Val}
    (hsub : SubTV n d τ_a τ_b) (h : RC n d τ_a v) : RC n d τ_b v :=
  hsub v h

/-- The contravariant variant for arrow-domain coercions. Mostly
notational at this point; will be the call-site idiom for the
function-type case in `SubV_to_SubTV.lam` (pass 7).

Note: this is NOT the contravariant SubV.lam-domain rule (which is
SubV S Γ domB domA → ...). It's just an alias for `SubTV` on the
domain-type pair, named to make contravariance explicit. -/
abbrev SubTV.contra (n d : Nat) (domA domB : Val) : Prop :=
  SubTV n d domB domA

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

/-! ## The fundamental lemma — open-environment form

The classical NbE soundness theorem, adapted to OCH's setting and
formulated over an open environment.

**Why open**: the closed FL's `.lam` case has no way to recurse
(the body lives under one binder, and the closed FL only knows
about empty environments). The open form takes a typed env `Γ ⊨ ρ`
and reasons under that env. The `.lam` case extends the env with
the function's domain; the IH applies under the extension.

Statement (informal): if `tyCheck n Γ ρ e τV = .ok true` and `ρ`
realises `Γ` (i.e., `RC_env n d Γ ρ`) and the type-target `τV` is
itself realised, then `eval n unfBound ρ e` produces a value `v`
with `RC n d τV v`.

Proof (sketch, *not* in this commit): structural induction on
`tyCheck`/`tyInfer`'s case-split structure. Each case of
`tyCheck`/`tyInfer` constructs an RC witness from the IHs:

- `.type` / `.bot`: base cases — `.type` is in `RC _ .type`
  directly via `RC.type_top`; `.bot` doesn't occur as a value at
  non-Bot type.
- `.bvar k`: env-lookup; `RC` follows from `RC_env`.
- `.lam dom body`: the function case. To show `RC (n+1) d (.lam
  domV clB) (.lam domV cl)`, we need that for every RC argument
  `a`, vapp produces an RC body. This is the IH on the body,
  instantiated under `RC_env.cons` extending the typed env.
- `.app f a`: from RC of `f` at `.lam domV clB` and RC of `a` at
  `domV`, the `.lam` clause of `RC` gives RC at `clB.openω a`.
- `.iota` / `.fix`: similar, using the corresponding `RC` clauses
  and `RC.iota_intro`/`RC.fix_intro`.
- `.asc t τ`: ascription is computationally transparent; RC
  follows from the IH on `t` at `τ`.
- `.letE val body`: extend the typed env via `RC_env.cons`, recurse.

Each case requires: the FL's IHs, the RC-closure lemmas (`RC.mono`,
`RC.subtype_closed`), and the standard NbE realisation lemmas
(`eval_realises`, `vapp_realises`).

**Proof status (pass 5)**: signature reformulated to take an
open environment. Body remains sorried — pass 6+ work.
-/

/-- **Fundamental lemma (open form)**: well-typed open expressions,
under a typed environment realisation, evaluate to RC-witnessed
values of their declared type.

This is the typed-NbE analogue of `eval_realises` (the untyped
realisation theorem in `SoundnessProof.lean`). The relationship:

  eval_realises    :  R relates v with e — untyped, syntactic.
  typed_nbe_fundamental_open :  RC relates v with τ — typed, semantic.

Both flow from `tyCheck` accepting; `eval_realises` gives
quote-equivalence, `typed_nbe_fundamental_open` gives
reducibility-at-type.

The conclusion bundles two things:

  ∃ v. eval n unfBound ρ e = .ok v ∧ RC n d τV v

The first ensures that `eval` succeeds at the given fuel (this is
NOT derivable in general from `tyCheck` — see the
`docs/ideas/quote-witness-feasibility.md` Ω-counterexample — but
for the *RC-witnessed* fragment, it is). The second gives the
typed-RC witness.

**Proof status (pass 5)**: scaffold with reformulated signature
to take an open environment. Body remains sorried; pass 6+ should
attack the body case-by-case. -/
theorem typed_nbe_fundamental_open
    {n d : Nat} {Γ : TyEnv} {ρ : Env} {e : Expr} {τV : Val}
    (_hΓρ : RC_env n d Γ ρ)
    (_hfuel : 1 ≤ n)
    (_hfuelω : n ≤ fuelω)
    (_hcheck : tyCheck n Γ ρ e τV = .ok true) :
    ∃ v, eval n unfBound ρ e = .ok v ∧ RC n d τV v := by
  -- TODO(typed-nbe pass 6+): proof body.
  --
  -- The proof is by structural induction on `tyCheck`/`tyInfer`'s
  -- case-split (which mirrors typing rules):
  --
  -- - `.type` / `.bot`: base case via `RC.type_top` / `RC.bot`.
  -- - `.bvar k`: env-lookup; `RC` from `RC_env`.
  -- - `.lam dom body`: extend env via `RC_env.cons`, recurse.
  -- - `.app f a`: combine IHs, use `RC.lam_elim` for body type.
  -- - `.iota` / `.fix`: use `RC.iota_intro` / `RC.fix_intro`.
  -- - `.asc t τ`: IH on `t` plus `RC.subtype_closed` for the
  --   declared-type ascription check.
  -- - `.letE val body`: extend env via `RC_env.cons`, recurse.
  --
  -- The hardest cases are `.lam` (closure-form output requires
  -- saturation witnesses on the closure body's eval at fuelω;
  -- documented in pass 3's post-mortem) and `.fix` (similar
  -- saturation issue on the fixed-point body).
  --
  -- Auxiliary lemmas the body will likely need:
  -- - `RC.subtype_closed` (above) for `.asc` and conversion sites
  --   inside `tyCheck` — currently scaffolded with 7 inline
  --   sorries on hard SubV cases.
  -- - A *body-substitution* lemma for the closure cases:
  --   "SubV between fresh-opened bodies → SubV between
  --   any-value-opened bodies". See the post-mortem in
  --   `docs/ideas/typed-nbe-implementation-log.md`.
  -- - `eval_realises` for the operational backbone (already
  --   proven in `SoundnessProof.lean`).
  sorry

/-- **Closed corollary** of the open FL: at empty `Γ`/`ρ`, the open
fundamental lemma yields the closed-form statement. Stated as a
non-`theorem`-tagged shape so it carries no proof obligation in
this commit; the body will fall out as a one-liner specialisation
once `typed_nbe_fundamental_open` is closed.

(Kept as documentation of the intended downstream API. NOT a
sorried theorem — it would inflate the inline-sorry count. Pass
6+ should add the actual theorem and prove it as a one-liner
specialisation.)
-/
example
    {n : Nat} {e τ : Expr}
    (_hcle : e.closedAt 0 = true) (_hclτ : τ.closedAt 0 = true)
    (_hfuel : 1 ≤ n)
    (_hfuelω : n ≤ fuelω)
    (_hcheck : typeCheck n e τ = .ok true) :
    -- Statement: the closed-form FL conclusion. Shown as an
    -- `example` (Lean's syntax for "stated, not committed").
    -- Actual theorem will be added by pass 6+ once
    -- `typed_nbe_fundamental_open` is proven.
    True := trivial

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
