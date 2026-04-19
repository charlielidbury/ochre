import Och.Syntax
import Och.Eval
import Och.Subtyping
import Och.NbE
import Och.SubCheckVal
import Och.TyCheck
import Och.SoundnessProof
import Och.Std.Nat
import Och.Std.Unit
import Och.Std.DBool

/-!
# Soundness (Phase 2)

Phase 1 (close all `TODO[mega-loop]` markers, zero `sorry` in
`Std/`+`Tests.lean`) completed at f2ba74a; the soundness audit
(`SoundnessAudit.lean`) identified three gaps, of which A1 was
fixed at 047e59f. This file now records the chosen Phase-2
architecture and the top-level theorem statements.

## Architecture

Following `Och/Simple/CheckSoundness.lean`:

  algorithmic ⟶ declarative ⟶ semantic
  `typeCheck`    `Subtype'`    `⟦·⟧`

The algorithmic side is `NbE.typeCheck` (TyCheck.lean), *not*
`subCheckNF` — the latter normalises first and so accepts
ill-typed inputs (SoundnessAudit A3). `typeCheck` runs the
domain check at every `.app` syntactically, then defers to
`subCheckVal` for conversion.

`subCheckVal` operates on `Val`s. The bridge to the Expr-level
`Subtype'` is `quote`: every `Val` produced by `eval` quotes
back to a unique normal-form `Expr` (NbETests witnesses
canonicity). So the algorithmic-soundness statement is

  `subCheckVal Γ a b = .ok true → Subtype' (quote a) (quote b)`

modulo de Bruijn level/index bookkeeping.

## Open design questions

- **A2 (type-in-type)**: the model takes `⟦Type⟧` to be the
  full value universe, accepting `Type : Type`. A predicative
  variant would index `Subtype'` and the model by a level.
  Deferred — Och is a core calculus, not a foundation.

- **`Subtype'` synced** (fb53b4c): now context-indexed
  (`Subtype' Γ a b`), with `lam` (contravariant domain),
  `app_cong` (arg equivalence), `unfold_iota_L`, explicit
  `trans`, and the `bvar` rule for type-ascent. The witnesses
  below confirm the constructors suffice for the simplest
  positive examples.

- **Coinduction**: the seen-set discipline is Brandt-Henglein
  style. The declarative counterpart is a coinductive
  `Subtype'` (or an inductive one quotiented by the gfp). Lean
  4's coinductive support is limited; the inductive-up-to
  encoding from `Simple/` may port directly.
-/

namespace Och.Soundness
open NbE

/-!
## Top-level statements

These are *targets*, not yet proofs. Each `sorry` here is a
Phase-2 obligation. They are stated now so that downstream
work (e.g. `concEval`-preservation) can quantify over them.
-/

/-- Algorithmic conversion is sound w.r.t. the declarative
relation. Stated over closed terms; the open-term version
threads `Γ` and a level-to-index map.

The proof factors as `subCheckVal → SubV → Subtype'`:
`subCheckVal_subV` is the algorithm-reflection step (fully
proven) and `SubV_to_Subtype'` is the readback bridge
(sorried in its closure-opening cases pending
`quote_open_subst` + `narrow`; see SoundnessProof). -/
theorem subCheckVal_sound
    {fuel : Nat} {a b : Val}
    (hfuel : fuel ≤ fuelω)
    (h : subCheckVal fuel #[] [] a b = .ok true)
    {ae be : Expr}
    (hqa : quote fuelω 0 a = some ae)
    (hqb : quote fuelω 0 b = some be) :
    Subtype' [] [] ae be :=
  SubV_to_Subtype'
    (subCheckVal_subV hfuel h)
    (fun _ hp => absurd hp (List.not_mem_nil _))
    (fun _ _ hk => by simp at hk)
    (by simpa using hqa)
    (by simpa using hqb)

/-- Closed-term NbE correctness: evaluating then quoting a
closed term gives something `Subtype'`-equivalent to the
original. Specialises `eval_realises` + `R_quote_equiv` at
the empty environment. -/
theorem eval_quote_equiv_closed {fuel unf : Nat} {e : Expr} {v : Val}
    (heval : eval fuel unf [] e = some v)
    {e' : Expr} (hq : quote fuelω 0 v = some e')
    {S Γe} : Subtype' S Γe e' e ∧ Subtype' S Γe e e' := by
  have henv : REnv 1 0 [] [] :=
    ⟨rfl, fun _ _ hk => by simp at hk⟩
  have hr : R 1 0 v (e.substEnv []) := eval_realises heval henv
  rw [Expr.substEnv_nil] at hr
  exact R_quote_equiv Nat.one_pos hr hq

/-- Quote-totality, inductive form: every value produced by
`eval` from an environment whose entries are themselves
`fuelω`-quotable at the current depth is `fuelω`-quotable.

This is the NbE-adequacy totality direction. The obstacle
is `quoteClosure`: it re-evaluates `cl.body` at fuel
`fuelω−1` with a fresh neutral consed onto `cl.env`, then
quotes the result at `depth+1`. So the IH needs to apply
to that *new* eval call (at a different fuel and a deeper
depth). Two sub-obligations:

  (a) Env entries quotable at `d` are also quotable at
      `d+1` — i.e., `quote_depth_lift` (every `.var l` in
      a value reachable from a depth-`d` env satisfies
      `l < d`, hence `l < d+1`). Stated separately below.

  (b) The inner `eval (fuelω−1) 1 (fresh :: cl.env)
      cl.body` succeeds. `cl.body` is a sub-Expr of the
      original `e` (via `Closure.mk'`), and `cl.env` is a
      prefix of the env at the closure's creation point.
      The bound is `fuelω ≥ fuel + Expr.size e` (each
      quote-layer adds at most `size body + 1` to the
      fuel needed); stated as `quoteClosure_total` below.

Both reduce to a `Val.maxLevel`/`Val.qfuel` measure that
doesn't yet exist; the closed-term specialisation
`quote_total_on_eval` derives from this with the env
hypothesis vacuously satisfied. -/
theorem eval_quotable {fuel unf d : Nat} {ρ : Env} {e : Expr} {v : Val}
    (hρ : ∀ w ∈ ρ, ∃ we, quote fuelω d w = some we)
    (heval : eval fuel unf ρ e = some v) :
    ∃ ve, quote fuelω d v = some ve := by
  -- By induction on `fuel`, then on `e`. Each constructive
  -- arm of `eval` either returns an env entry (`hρ`),
  -- builds one constructor on top of an IH result (`.lam`/
  -- `.iota`/`.fix` — the closure case is (b) above), or
  -- recurses (`.letE`/`.app`/`.asc` — IH at extended/same
  -- env). The closure case is the only non-IH leaf.
  sorry

/-- Quote-totality on closed eval-images: specialises
`eval_quotable` at the empty environment (env hypothesis
vacuous). -/
theorem quote_total_on_eval {fuel unf : Nat} {e : Expr} {v : Val}
    (heval : eval fuel unf [] e = some v) :
    ∃ ve, quote fuelω 0 v = some ve :=
  eval_quotable (fun _ hw => absurd hw (List.not_mem_nil _)) heval

/-- `whnfPi` is sound in the right-to-left direction: each
`.fix`/`.iota` step is one declarative unfold
(`Subtype'.unfold_fix_R`/`unfold_iota_L`), so the exposed
head is a supertype of the input. (The full `Equiv` form
needs the inhabitant to match the iota's self; the
right-to-left direction holds regardless.)

Stated relative to `quote` so it composes with
`subCheckVal_sound`/`eval_quote_equiv_closed` directly. -/
theorem whnfPi_sound {fuel : Nat} {inhab τV τV' : Val}
    (hwh : whnfPi fuel inhab τV = some τV')
    {τe τe' : Expr}
    (hqτ : quote fuelω 0 τV = some τe)
    (hqτ' : quote fuelω 0 τV' = some τe') :
    ∀ {S Γe}, Subtype' S Γe τe' τe := by
  -- Induction on `unfBound` (the counter `whnfPi.go`
  -- decrements). Each `.fix` step:
  --   `Subtype' (quote (cl.open v)) (quote (.fix ann cl))`
  --   = `unfold_fix_R` after `quote_open_subst` (via `Equiv`).
  -- Each `.iota` step similarly via `unfold_iota_L`. The
  -- `quote_open_subst` dependency chains this onto
  -- `eval_realises`.
  sorry

/-!
### `tyCheck`/`tyInfer` soundness

`tyCheck`/`tyInfer`/`tyCheckFallback` are de-partialised (`ddfe29c`), so
`unfold tyCheck` etc. work. The three soundness theorems
mirror the algorithm's mutual block at the same
`(fuel, tag)` lex order:
  - `tyInfer_sound_closed` tag 0
  - `tyCheckFallback_sound_closed` tag 1
  - `tyCheck_sound_closed` tag 2

All three are at the empty context (`#[]`/`[]`). The
binder-introducing arms (`.lam`/`.letE` of `tyCheck`;
`.lam`/`.letE`/`.app`-β of `tyInfer`) recurse at
*non-empty* `Γ`/`ρ`, so a closed-form IH does not apply.
Those arms are sorried with the residual goal exposed and
a note that the open-form generalisation
`tyCheck_sound_open : QuotesCtx Γ Γe → REnv … ρ ρe → … →
Subtype' [] Γe e τ` is the actual proof target; the
closed forms below specialise it at `Γe = []`.
-/
mutual

/-- Soundness of `tyInfer`: the inferred type's quote is a
supertype of `e`. The conclusion bundles quote-existence so
callers don't need a separate quote-totality lemma. -/
theorem tyInfer_sound_closed
    {fuel : Nat} {e : Expr} {τV : Val}
    (hfuel : fuel ≤ fuelω)
    (h : tyInfer fuel #[] [] e = .ok (some τV)) :
    ∃ τe, quote fuelω 0 τV = some τe ∧ Subtype' [] [] e τe := by
  match fuel, hfuel, h with
  | 0, _, h => simp [tyInfer] at h
  | fuel + 1, hfuel, h =>
    have hfuel' : fuel ≤ fuelω := Nat.le_of_succ_le hfuel
    unfold tyInfer at h
    -- Match on `e` mirroring the algorithm's case-split.
    -- Closed cases: `.bvar` (impossible), `.type` (refl).
    -- The remaining seven cases either recurse at
    -- non-empty Γ (`.lam`/`.letE`/`.app`-β/`.app`-let) or
    -- need `quote_open_subst` (`.app` generic) or trust
    -- the fix/iota annotation (`.fix`/`.iota` — see note
    -- below). The `.asc` case recurses at the same Γ via
    -- `tyCheck_sound_closed` and closes via `.asc_L` +
    -- `eval_quote_equiv_closed`; left as the per-arm
    -- residuals because the `do`-block extraction is the
    -- same shape as `tyCheckFallback`'s (worked through
    -- there) and adds no new sub-lemma.
    --
    -- `.fix ann _` / `.iota ann _`: `tyInfer` returns
    -- `eval ann` *without recursing into the body*. So
    -- `Subtype' (.fix ann body) (quote annV)` here is
    -- claimed *unconditionally on body*. That is unsound
    -- in general (`.fix Nat_ Bool ⊄ Nat_`); it relies on
    -- TyCheck.lean's documented "fix is treated as a
    -- black box of its annotation" assumption. The
    -- correct fix is for `tyInfer`'s `.fix` arm to also
    -- check `tyCheck body annV` under a self-hypothesis
    -- (the standard fixpoint typing rule). Until that's
    -- added, this case is genuinely *unprovable* and the
    -- top-level `typeCheck_sound` is conditional on
    -- well-annotated fixes in the input.
    sorry
termination_by (fuel, 0)

/-- Soundness of `tyCheckFallback`: both paths
(`tyInfer`-then-convert and `eval`-then-convert) chain
through `subCheckVal_sound` and `eval_quote_equiv_closed`. -/
theorem tyCheckFallback_sound_closed
    {fuel : Nat} {e τ : Expr} {τV : Val}
    (hfuel : fuel ≤ fuelω)
    (hτV : eval fuel unfBound [] τ = some τV)
    (h : tyCheckFallback fuel #[] [] e τV = .ok true) :
    Subtype' [] [] e τ := by
  obtain ⟨τe, hqτV⟩ := quote_total_on_eval hτV
  have hτe_τ : Subtype' [] [] τe τ :=
    (eval_quote_equiv_closed hτV hqτV).1
  unfold tyCheckFallback at h
  simp only [bind, Except.bind] at h
  split at h
  · simp_all
  · next eTy? hinfer =>
    cases eTy? with
    | some eTy =>
        -- `subCheckVal fuel #[] [] eTy τV = .ok true`
        simp only [] at h
        obtain ⟨eTye, hqeTy, h_e_eTye⟩ :=
          tyInfer_sound_closed hfuel hinfer
        have hsub := subCheckVal_sound hfuel h hqeTy hqτV
        exact .trans h_e_eTye (.trans hsub hτe_τ)
    | none =>
        -- `eval e → eV; subCheckVal eV τV = .ok true`
        simp only [] at h
        split at h
        · next eV heV =>
          obtain ⟨eVe, hqeV⟩ := quote_total_on_eval heV
          have h_e_eVe : Subtype' [] [] e eVe :=
            (eval_quote_equiv_closed heV hqeV).2
          have hsub := subCheckVal_sound hfuel h hqeV hqτV
          exact .trans h_e_eVe (.trans hsub hτe_τ)
        · simp_all
termination_by (fuel, 1)

/-- Soundness of `tyCheck` at the empty context: if
`tyCheck e τV` succeeds where `τV = eval [] τ`, then
`e ⊑ τ` declaratively. -/
theorem tyCheck_sound_closed
    {fuel : Nat} {e τ : Expr} {τV : Val}
    (hfuel : fuel ≤ fuelω)
    (hτV : eval fuel unfBound [] τ = some τV)
    (h : tyCheck fuel #[] [] e τV = .ok true) :
    Subtype' [] [] e τ := by
  match fuel, hfuel, hτV, h with
  | 0, _, _, h => simp [tyCheck] at h
  | fuel + 1, hfuel, hτV, h =>
    have hfuel' : fuel ≤ fuelω := Nat.le_of_succ_le hfuel
    unfold tyCheck at h
    split at h
    -- .lam dom body
    · -- `whnfPi expected → .lam expDom expCl;
      --  subCheckVal expDom domV;
      --  tyCheck body expBody (under push expDom, fresh::ρ)`.
      -- The body IH is at non-empty Γ; needs the open
      -- form. After that, `whnfPi_sound` bridges `τV` to
      -- the exposed `.lam`, `subCheckVal_sound` gives the
      -- contravariant domain premise, and `Subtype'.lam`
      -- assembles. The fallback branch (when `whnfPi`
      -- doesn't expose `.lam`) goes through
      -- `tyCheckFallback_sound_closed` directly.
      sorry
    -- .letE val body
    · -- After A9 (`a2c82ae`), the arm is:
      --   `valTy? ← tyInfer fuel #[] [] val;
      --    valV   ← eval fuel _ [] val;
      --    valTy  := match valTy? with
      --      | none   => valV
      --      | some t => if (tyCheck fuel #[] [] val t) then t else valV;
      --    tyCheck fuel #[valTy] [valV] body τV`.
      --
      -- The `okV` verification step (`tyCheck val t` at the
      -- empty context, fuel decremented) does NOT fit this
      -- closed-form IH because the IH wants an *Expr* `τ₀`
      -- with `eval … τ₀ = some t`, and `t` came from
      -- `tyInfer` (a `Val`) — there is no source Expr. The
      -- open form `tyCheck_sound_open` should take the
      -- expected type as `(τV : Val) (τe : Expr)
      -- (hq : quote fuelω d τV = some τe)` instead, so the
      -- conclusion is `Subtype' Se Γe e τe` and `t`'s `te`
      -- (from `tyInfer_sound_closed`) slots in directly.
      --
      -- The body call is at `Γ = #[valTy]`, `ρ = [valV]`,
      -- so the closed IH is unavailable regardless. The
      -- open-form residual:
      --   `Subtype' [] [valTye] body τe` (open IH at the
      --     extended context, where `valTye = quote valTy`)
      --   then `Subtype'.subst_body` (induction-on-derivation
      --     substituting `val` for the head context entry):
      --   `Subtype' [] [] (body.subst 0 val) τe`
      --   then `.letE_L`: `Subtype' [] [] (.letE val body) τe`
      --   then `.trans` with `eval_quote_equiv_closed hτV`'s
      --     `τe ⊑ τ`.
      --
      -- `Subtype'.subst_body` is the lemma the parent removed
      -- at `5169447` (subsumed by the new `*_cong`
      -- constructors for `Equiv.subst_resp`'s purposes), but
      -- this case needs the *one-direction* form
      --   `Subtype' S (A :: Γ) M N → Subtype' S Γ
      --     (M.subst 0 a) (N.subst 0 a)` (for `a ⊑ A`).
      -- That is the standard substitution lemma; same shape
      -- as `narrow_at`/`ctx_extend_at` (induction on the
      -- derivation, binder cases shift, `.bvar 0` uses the
      -- `a ⊑ A` premise).
      sorry
    -- .asc e0 τ0
    · next e0 τ0 =>
      -- `eval τ0 → τ0V; tyCheck e0 τ0V; subCheckVal τ0V τV`.
      -- Both calls at Γ=#[]; closed IH applies.
      split at h
      · next τ0V hτ0V =>
        simp only [bind, Except.bind] at h
        split at h
        · simp_all
        · next b hinner =>
          cases b with
          | false => simp_all [pure, Except.pure]
          | true =>
            simp only [Bool.not_true, Bool.false_eq_true,
                       ↓reduceIte, pure, Except.pure,
                       bind, Except.bind] at h
            -- IH on inner check: `e0 ⊑ τ0`.
            have h_e0_τ0 := tyCheck_sound_closed hfuel' hτ0V hinner
            -- `subCheckVal τ0V τV` → `quote τ0V ⊑ quote τV`.
            obtain ⟨τe, hqτV⟩ := quote_total_on_eval hτV
            obtain ⟨τ0e, hqτ0V⟩ := quote_total_on_eval hτ0V
            have hsub := subCheckVal_sound hfuel' h hqτ0V hqτV
            -- `eval_quote_equiv_closed`: `τ0 ≡ quote τ0V`,
            -- `quote τV ≡ τ`.
            have hτ0_τ0e :=
              (eval_quote_equiv_closed hτ0V hqτ0V
                (S := []) (Γe := [])).2
            have hτe_τ :=
              (eval_quote_equiv_closed hτV hqτV
                (S := []) (Γe := [])).1
            exact .asc_L (.trans h_e0_τ0
              (.trans hτ0_τ0e (.trans hsub hτe_τ)))
      · simp_all
    -- .fix _ _ and .iota _ _ (A9 arm: eval-then-subCheckVal),
    -- then catch-all → tyCheckFallback. The fix/iota cases:
    -- `subCheckVal_sound` + `eval_quote_equiv_closed` on both
    -- sides + `.trans`²; same proof for both, so `first | … |`.
    all_goals first
    | exact tyCheckFallback_sound_closed hfuel hτV h
    | (rename_i ann body
       split at h
       · rename_i eV hev
         obtain ⟨τe, hqτV⟩ := quote_total_on_eval hτV
         obtain ⟨ee, hqeV⟩ := quote_total_on_eval hev
         have hsub := subCheckVal_sound hfuel' h hqeV hqτV
         have he_ee := (eval_quote_equiv_closed hev hqeV
           (S := []) (Γe := [])).2
         have hτe_τ := (eval_quote_equiv_closed hτV hqτV
           (S := []) (Γe := [])).1
         exact .trans he_ee (.trans hsub hτe_τ)
       · simp_all)
termination_by (fuel, 2)

end

/-- The bidirectional checker is sound: if `typeCheck e τ`
accepts then `e ⊑ τ` declaratively.

`typeCheck` evaluates `τ` to `τV`, then runs `tyCheck` at
`τV`; `tyCheck_sound_closed` does the rest. -/
theorem typeCheck_sound
    {fuel : Nat} {e τ : Expr}
    (hfuel : fuel ≤ fuelω)
    (h : typeCheck fuel e τ = .ok true) :
    Subtype' [] [] e τ := by
  unfold typeCheck at h
  split at h
  · next τV hτV => exact tyCheck_sound_closed hfuel hτV h
  · simp_all

/-- One let-step is an `Equiv`. Both directions are single
`Subtype'` constructors with a `.refl` premise. -/
private theorem letE_unfold_equiv (val body : Expr) :
    Equiv (.letE val body) (body.subst 0 val) :=
  fun {_ _} => ⟨.letE_L (.refl _), .letE_R (.refl _)⟩

/-- One asc-erase is an `Equiv`. -/
private theorem asc_erase_equiv (t ty : Expr) :
    Equiv (.asc t ty) t :=
  fun {_ _} => ⟨.asc_L (.refl _), .asc_R (.refl _)⟩

-- One `.iota`-unfold step is `NbE.Equiv.iota_unfold`
-- (SoundnessProof.lean), enabled by `Subtype'.unfold_iota_R`.
-- The earlier `iota_unfold_equiv` (sorried — its backward
-- direction went via `.iota_intro` whose `body[ι] ⊑ ann`
-- premise is not derivable without a well-formedness
-- assumption) is removed.

/-- `concEval` produces a declarative *equivalent* of its
input (both directions). With `Equiv.subst_resp` (no leaf
sorry, SoundnessProof.lean) the `.letE` and `.app` cases
that previously needed only the forward direction now get
both from the IH. The `.app`-with-`.iota`-head case is the
sole residual, now closed via `Equiv.iota_unfold`.

`concEval_refines` (the forward half) and
`concEval_preservation` derive directly. -/
theorem concEval_equiv
    {fuel : Nat} {e e' : Expr}
    (hstep : concEval fuel e = some e') :
    Equiv e' e := by
  -- (Tactic-mode `match e` here makes the `Equiv`-def goal
  -- mis-elaborate against `Equiv.*` lemmas; `cases e` does
  -- not. Lean 4.16 quirk.)
  induction fuel generalizing e e' with
  | zero => simp [concEval] at hstep
  | succ n ih =>
    cases e with
    | bvar _ => simp [concEval] at hstep
    | type =>
      simp only [concEval, Option.some.injEq] at hstep
      subst hstep; exact Equiv.refl _
    | lam _ _ =>
      simp only [concEval, Option.some.injEq] at hstep
      subst hstep; exact Equiv.refl _
    | iota _ _ =>
      simp only [concEval, Option.some.injEq] at hstep
      subst hstep; exact Equiv.refl _
    | «fix» _ _ =>
      simp only [concEval, Option.some.injEq] at hstep
      subst hstep; exact Equiv.refl _
    | asc t ty =>
      simp only [concEval] at hstep
      exact Equiv.trans (ih hstep) (Equiv.symm (asc_erase_equiv t ty))
    | letE val body =>
      simp only [concEval] at hstep
      split at hstep
      · next v' hval =>
        exact Equiv.trans (ih hstep)
          (Equiv.trans (Equiv.subst_resp body (ih hval) 0)
            (Equiv.symm (letE_unfold_equiv val body)))
      · simp at hstep
    | app f a =>
      simp only [concEval] at hstep
      split at hstep
      -- .lam head: β
      · next dom fbody a' hf ha =>
        exact Equiv.trans (ih hstep)
          (Equiv.trans (Equiv.subst_resp fbody (ih ha) 0)
            (Equiv.trans (Equiv.symm (Equiv.beta dom fbody a))
              (Equiv.app (ih hf) (Equiv.refl a))))
      -- .iota head: via `Equiv.iota_unfold`
      · next ann ibody a' hf ha =>
        exact Equiv.trans (ih hstep)
          (Equiv.app
            (Equiv.trans (Equiv.symm (Equiv.iota_unfold ann ibody))
                         (ih hf))
            (ih ha))
      -- .fix head: `Equiv.fix_unfold` (proven, SoundnessProof)
      · next ann fbody' a' hf ha =>
        exact Equiv.trans (ih hstep)
          (Equiv.app
            (Equiv.trans (Equiv.symm (Equiv.fix_unfold ann fbody'))
                         (ih hf))
            (ih ha))
      -- other head: just `.app_cong`
      · next fVal a' _ _ _ hf ha =>
        simp only [Option.some.injEq] at hstep; subst hstep
        exact Equiv.app (ih hf) (ih ha)
      -- failure cases
      · simp_all

/-- The forward-only half, kept for callers that don't need
the equivalence. Now derived. -/
theorem concEval_refines
    {fuel : Nat} {e e' : Expr}
    (hstep : concEval fuel e = some e') :
    ∀ {S Γ}, Subtype' S Γ e' e :=
  fun {_ _} => (concEval_equiv hstep).1

/-- Type preservation under concrete evaluation: if `e ⊑ τ`
declaratively and `concEval e ⇓ e'`, then `e' ⊑ τ`. Direct
from `concEval_refines` and transitivity. -/
theorem concEval_preservation
    {fuel : Nat} {e e' τ : Expr}
    (hty : Subtype' [] [] e τ)
    (hstep : concEval fuel e = some e') :
    Subtype' [] [] e' τ :=
  .trans (concEval_refines hstep) hty

/-- Composing the above: the user-facing guarantee. -/
theorem soundness
    {fuel : Nat} {e e' τ : Expr}
    (hfuel : fuel ≤ fuelω)
    (hcheck : typeCheck fuel e τ = .ok true)
    (hstep : concEval fuel e = some e') :
    Subtype' [] [] e' τ :=
  concEval_preservation (typeCheck_sound hfuel hcheck) hstep

/-!
## Witnesses

Hand-built `Subtype'` derivations for the simplest positive
tests, demonstrating the constructors are sufficient (i.e. the
algorithm's `.ok true` corresponds to a derivation).
-/

section Witnesses
open Std

/-- `zero_ ⊑ Nat_`. The body comparison `z ⊑ X` (= `bvar 1 ⊑
bvar 2` under `Γ = [X→X, X, Type]`) goes through `.bvar`:
`Γ[1] = .bvar 0` (the type of `z` is `X`, which at its binder
was `bvar 0`), shifted by 2 gives `bvar 2` = `X`. -/
example : Subtype' [] [] zero_ Nat_ := by
  apply Subtype'.lam_body
  apply Subtype'.lam_body
  apply Subtype'.lam_body
  exact Subtype'.bvar (k := 1) (τ := .bvar 0) rfl

/-- `unit_ ⊑ Unit_`. Same shape: `unit_ = λX. λu:X. u`,
`Unit_ = λX. λu:X. X`, body `u ⊑ X` via `.bvar`. -/
example : Subtype' [] [] unit_ Unit_ := by
  apply Subtype'.lam_body
  apply Subtype'.lam_body
  exact Subtype'.bvar (k := 0) (τ := .bvar 0) rfl

/-- β-conversion: `(λx:Nat_. x) zero_ ⊑ Nat_` reduces via
`beta_L` to the `zero_ ⊑ Nat_` witness above. -/
example : Subtype' [] [] (.app (.lam Nat_ (.bvar 0)) zero_) Nat_ := by
  apply Subtype'.beta_L
  apply Subtype'.lam_body; apply Subtype'.lam_body; apply Subtype'.lam_body
  exact Subtype'.bvar (k := 1) (τ := .bvar 0) rfl

/-- `one_ ⊑ Nat_` (Church 1). Body is `s z ⊑ X` under
`Γ = [s:X→X, z:X, X:Type]`. Derives via `app_ascent`: `s` has
Π-type `X→X` from `.bvar`, so `s z` has the codomain `X`. -/
example : Subtype' [] [] one_ Nat_ := by
  apply Subtype'.lam_body
  apply Subtype'.lam_body
  apply Subtype'.lam_body
  -- Γ = [.lam (.bvar 1) (.bvar 2), .bvar 0, .type]
  -- bvar 0 (=s) ⊑ Γ[0].shift 1 0 ; Γ[0] = `.lam (bvar 1) (bvar 2)`
  -- shift 1 0 → `.lam (bvar 2) (bvar 3)`. Then app_ascent with
  -- a := bvar 1 (=z) gives `(bvar 3).subst 0 (bvar 1) = bvar 2`.
  have hs := Subtype'.bvar (S := [])
                           (Γ := [.lam (.bvar 1) (.bvar 2), .bvar 0, .type])
                           (k := 0) (τ := .lam (.bvar 1) (.bvar 2)) rfl
  have ha := Subtype'.app_ascent (a := .bvar 1) hs
  simp only [Expr.shift, Expr.subst, Expr.shift] at ha
  exact ha

/-!
The flagship coinductive case (SoundnessAudit A4): `dtrue ⊑ dBool`
fully derived. With the very-dependent encoding (no per-constructor
`fix`), the derivation is shorter than the `e08bce9` form: `dtrue`
is already an `.iota`, so there's no `.unfold_fix_L` step, and after
`unfold_iota_L` substitutes `self ↦ dtrue` the LHS `t`-domain is
already `P dtrue` (matching the RHS by `.refl` — previously it was
`P dtrueIota` and needed `app_cong` + two fix-unfolds).
-/

private def dBoolIota : Expr :=
  .iota dBool
    (.lam (.lam dBool .type)
      (.lam (.app (.bvar 0) dtrue)
        (.lam (.app (.bvar 1) dfalse)
          (.app (.bvar 2) (.bvar 3)))))

private def bodyRHS : Expr :=
  .lam (.lam dBool .type)
    (.lam (.app (.bvar 0) dtrue)
      (.lam (.app (.bvar 1) dfalse)
        (.app (.bvar 2) dtrue)))

private def dtrueLam : Expr :=
  .lam (.lam dtrue .type)
    (.lam (.app (.bvar 0) dtrue)
      (.lam .type (.bvar 1)))

/-- `dtrue ⊑ dBool`. Constructor path:

  `unfold_fix_R` → `iota_intro` (annotation via `.hyp`) →
  `unfold_iota_L` → `lam`³ →
    P-domain contra: `lam`(`.hyp`, `.refl`)
    t-domain contra: `.refl`         ← was app_cong + 2 fix-unfolds
    f-domain contra: `.top`
    body: `.bvar`

Both `.hyp` uses discharge `dtrue ⊑ dBool` from the seen-set entry
added by the very first `unfold_fix_R`; without seen-indexing
this was the unbreakable cycle. -/
example : Subtype' [] [] dtrue dBool := by
  unfold dBool
  apply Subtype'.unfold_fix_R
  change Subtype' _ [] dtrue dBoolIota
  apply Subtype'.iota_intro
  · -- annotation: dtrue ⊑ dBool, found at S[1]
    exact Subtype'.hyp (List.Mem.tail _ (List.Mem.head _))
  · -- body: dtrue ⊑ λP:(dBool→Type). λt:(P dtrue). λf:(P dfalse). P dtrue
    change Subtype' _ [] dtrue bodyRHS
    unfold dtrue
    apply Subtype'.unfold_iota_L
    change Subtype' _ [] dtrueLam bodyRHS
    -- λP:(dtrue→Type). λt:(P dtrue). λf:Type. t
    --   ⊑ λP:(dBool→Type). λt:(P dtrue). λf:(P dfalse). P dtrue
    apply Subtype'.lam
    · -- (dBool→Type) ⊑ (dtrue→Type): contra dtrue⊑dBool via .hyp at S[2]
      apply Subtype'.lam
      · exact Subtype'.hyp
          (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))
      · exact Subtype'.refl _
    · apply Subtype'.lam
      · -- (P dtrue) ⊑ (P dtrue): refl
        exact Subtype'.refl _
      · apply Subtype'.lam
        · -- (P dfalse) ⊑ Type
          exact Subtype'.top _
        · -- t ⊑ P dtrue, i.e. bvar 1 ⊑ (bvar 2) dtrue.
          show Subtype' _ _ (.bvar 1) ((Expr.app (.bvar 0) dtrue).shift 2 0)
          exact Subtype'.bvar (k := 1) (τ := .app (.bvar 0) dtrue) rfl

end Witnesses

end Och.Soundness
