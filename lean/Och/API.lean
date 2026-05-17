import Och.Syntax
import Och.Outcome
import Och.EvalSubst

/-!
# Och public typing/subtyping API

The single user-facing surface for Och's type-checking and
subtype-checking pipeline.

## Surface

```
structure Och.WTValue where
  private mk ::
  whnf : Expr      -- well-typed value (in WHNF) by construction

def Och.synth (e : Expr) (fuel : Nat := 5000) : Outcome WTValue
def Och.subCheck (a b : WTValue) (fuel : Nat := 5000) : Outcome Bool
def Och.subCheckE (fuel : Nat) (e τ : Expr) : Outcome Bool
```

## Design (synth = structural walk + the engine for typing questions)

`synth Γ e` is a structural walk that returns `e`'s WHNF (which
is its most-precise type via `Subtype'.refl`), validating
well-typedness at every node. All "is X well-typed at Y?"
questions are delegated to the existing complete structural
engine `SubstEval.subCheckOpen`.

In the pure de Bruijn regime, descending under a binder does NOT
substitute — we recurse on the raw body with the context extended.
`bvar 0` in the body naturally refers to the new innermost binder.

## Intrinsic typing

`synthCore` returns `Outcome (Σ v : Expr, Subtype' [] Γ e v)` —
both the synthesized WHNF AND a derivation that `e ⊑ v`. This
makes synth-soundness trivial: just extract the derivation from
the Sigma.
-/

namespace Och

open SubstEval

/-- A well-typed value: `whnf` is an `Expr` in head-normal form
that has been validated by the structural walk in `synth`. The
`mk` constructor is `private`; the only public way to obtain a
`WTValue` is via `synth`. -/
structure WTValue where
  private mk ::
  /-- The validated expression in head-normal form. -/
  whnf : Expr
  deriving Repr

/-- Type context for `synth`: stores the types of free variables.
`Γ[Γ.length - 1 - k]` is the type of `bvar k`. Push to the end
when entering a binder.

Public so soundness lemmas can mention `Γ`'s type when stating
per-arm helper lemmas. -/
abbrev TyEnv := List Expr

/-! ## Synth core (intrinsic)

The walk takes an explicit type-environment `Γ` and threads
fuel through. Each node validates its sub-terms recursively and
calls `subCheckOpen` for the one typing question that arm asks
(domain check at app, ascription consistency at asc).

Returns both the WHNF value AND a `Subtype' [] Γ e v` derivation.

Termination is fuel-bounded. -/

/-- Synth helper: produce e's WHNF as a type-witness, validating
each node. Returns both the WHNF value AND a proof that `e ⊑ v`.

For canonical forms (lam, iota, fix, type, bot) the result is `e`
itself with `.refl`. For `.app`, it's the WHNF of the β-reduced
result with a composed derivation chain. For `.asc`, it's the
inner value's result with `.asc_L`.

**Visibility.** Public so that soundness proofs can name it.

**Termination.** Non-`partial`: `fuel` strictly decreases at every
recursive call. -/
def synthCore (fuel : Nat) (Γ : TyEnv) (e : Expr) :
    Outcome (Σ v : Expr, Subtype' [] Γ e v) :=
  match fuel with
  | 0 => .outOfFuel
  | fuel + 1 =>
    match e with
    | .type => .ok ⟨.type, .refl _⟩
    | .bot  => .ok ⟨.bot, .refl _⟩
    | .bvar k =>
        -- Pure de Bruijn: bvar k is valid if k < Γ.length.
        if _h : k < Γ.length then
          .ok ⟨.bvar k, .refl _⟩
        else
          .error s!"synth: unbound bvar {k} (|Γ|={Γ.length})"
    | .lam dom body =>
        match subCheckOpen fuel Γ dom .type with
        | .ok true =>
          match evalSubst fuel SubstEval.unfBound dom with
          | .ok domV =>
            match synthCore fuel (domV :: Γ) body with
            | .ok ⟨_, _⟩ =>
              -- Canonical: a lambda is its own most-precise type.
              -- evalSubst on .lam returns .ok (.lam dom body) immediately.
              match hev : evalSubst fuel SubstEval.unfBound (.lam dom body) with
              | .ok v => .ok ⟨v, (evalSubst_equiv_open' [] Γ hev).2⟩
              | .outOfFuel => .outOfFuel
              | .error msg => .error msg
            | .outOfFuel => .outOfFuel
            | .error msg => .error msg
          | .outOfFuel => .outOfFuel
          | .error msg => .error msg
        | .ok false => .error s!"synth: lam domain annotation is not a type"
        | .outOfFuel => .outOfFuel
        | .error msg => .error msg
    | .iota ann body =>
        match subCheckOpen fuel Γ ann .type with
        | .ok true =>
          match evalSubst fuel SubstEval.unfBound ann with
          | .ok annV =>
            match synthCore fuel (annV :: Γ) body with
            | .ok ⟨_, _⟩ =>
              match hev : evalSubst fuel SubstEval.unfBound (.iota ann body) with
              | .ok v => .ok ⟨v, (evalSubst_equiv_open' [] Γ hev).2⟩
              | .outOfFuel => .outOfFuel
              | .error msg => .error msg
            | .outOfFuel => .outOfFuel
            | .error msg => .error msg
          | .outOfFuel => .outOfFuel
          | .error msg => .error msg
        | .ok false => .error s!"synth: iota annotation is not a type"
        | .outOfFuel => .outOfFuel
        | .error msg => .error msg
    | .fix ann body =>
        match subCheckOpen fuel Γ ann .type with
        | .ok true =>
          match evalSubst fuel SubstEval.unfBound ann with
          | .ok annV =>
            match synthCore fuel (annV :: Γ) body with
            | .ok ⟨_, _⟩ =>
              match hev : evalSubst fuel SubstEval.unfBound (.fix ann body) with
              | .ok v => .ok ⟨v, (evalSubst_equiv_open' [] Γ hev).2⟩
              | .outOfFuel => .outOfFuel
              | .error msg => .error msg
            | .outOfFuel => .outOfFuel
            | .error msg => .error msg
          | .outOfFuel => .outOfFuel
          | .error msg => .error msg
        | .ok false => .error s!"synth: fix annotation is not a type"
        | .outOfFuel => .outOfFuel
        | .error msg => .error msg
    | .asc inner τ =>
        match subCheckOpen fuel Γ τ .type with
        | .ok true =>
          match evalSubst fuel SubstEval.unfBound τ with
          | .ok τV =>
            match synthCore fuel Γ inner with
            | .ok ⟨vInner, pInner⟩ =>
              -- The single typing question: vInner ⊑ τV.
              match subCheckOpen fuel Γ vInner τV with
              | .ok true => .ok ⟨vInner, .asc_L pInner⟩
              | .ok false =>
                  .error s!"synth: ascription rejected (term ⊄ annotation)"
              | .outOfFuel => .outOfFuel
              | .error msg => .error msg
            | .outOfFuel => .outOfFuel
            | .error msg => .error msg
          | .outOfFuel => .outOfFuel
          | .error msg => .error msg
        | .ok false => .error s!"synth: ascription type is not a type"
        | .outOfFuel => .outOfFuel
        | .error msg => .error msg
    | .letE val body =>
        match synthCore fuel Γ val with
        | .ok ⟨valV, _⟩ =>
          match synthCore fuel (valV :: Γ) body with
          | .ok ⟨_, _⟩ =>
            -- The whole `let` β-reduces; return its WHNF via evalSubst.
            match hev : evalSubst fuel SubstEval.unfBound (.letE val body) with
            | .ok v => .ok ⟨v, (evalSubst_equiv_open' [] Γ hev).2⟩
            | .outOfFuel => .outOfFuel
            | .error msg => .error msg
          | .outOfFuel => .outOfFuel
          | .error msg => .error msg
        | .outOfFuel => .outOfFuel
        | .error msg => .error msg
    | .app f a =>
        match synthCore fuel Γ f with
        | .ok ⟨vF, pF⟩ =>
          match synthCore fuel Γ a with
          | .ok ⟨_vA, _pA⟩ =>
            match haV : evalSubst fuel SubstEval.unfBound a with
            | .ok aV =>
              match hfV : evalSubst fuel SubstEval.unfBound f with
              | .ok fV =>
                -- Build derivation ingredients
                let ha_aV := (evalSubst_equiv_open' [] Γ haV).2   -- a ⊑ aV
                let haV_a := (evalSubst_equiv_open' [] Γ haV).1   -- aV ⊑ a
                let hf_fV := (evalSubst_equiv_open' [] Γ hfV).2   -- f ⊑ fV
                let hfV_f := (evalSubst_equiv_open' [] Γ hfV).1   -- fV ⊑ f
                -- fV ⊑ vF via: fV ⊑ f ⊑ vF
                let hfV_vF : Subtype' [] Γ fV vF := .trans hfV_f pF
                -- Step 1: (.app f a) ⊑ (.app fV aV)
                let step1 : Subtype' [] Γ (.app f a) (.app fV aV) :=
                  .app_cong hf_fV ha_aV haV_a
                -- Try primary path: whnfPi directly on vF
                -- Use exposePi (= whnfPi) which has computable derivation
                match hwp : exposePi fuel fV vF with
                | some (.lam piDom piBody) =>
                    -- fV ⊑ piExpr via exposePi_deriv
                    let hfV_pi := exposePi_deriv [] Γ hfV_vF hwp
                    let step2 : Subtype' [] Γ (.app fV aV) (.app (.lam piDom piBody) aV) :=
                      .app_cong hfV_pi (.refl _) (.refl _)
                    -- Domain check
                    match subCheckOpen fuel Γ aV piDom with
                    | .ok true =>
                      match hev : evalSubst fuel SubstEval.unfBound
                          (.app (.lam piDom piBody) aV) with
                      | .ok v =>
                          let step3 := (evalSubst_equiv_open' [] Γ hev).2
                          .ok ⟨v, .trans step1 (.trans step2 step3)⟩
                      | .outOfFuel => .outOfFuel
                      | .error msg => .error msg
                    | .ok false =>
                      -- Arg direct check failed, try neutral ascent on arg
                      match synthNeutralWithDeriv fuel Γ [] aV with
                      | .ok (some ⟨aTy, _⟩) =>
                        match subCheckOpen fuel Γ aTy piDom with
                        | .ok true =>
                          match hev : evalSubst fuel SubstEval.unfBound
                              (.app (.lam piDom piBody) aV) with
                          | .ok v =>
                              let step3 := (evalSubst_equiv_open' [] Γ hev).2
                              .ok ⟨v, .trans step1 (.trans step2 step3)⟩
                          | .outOfFuel => .outOfFuel
                          | .error msg => .error msg
                        | .ok false => .error s!"synth: arg ⊄ dom at .app"
                        | .outOfFuel => .outOfFuel
                        | .error msg => .error msg
                      | .ok none => .error s!"synth: arg ⊄ dom at .app (no ascent)"
                      | .outOfFuel => .outOfFuel
                      | .error msg => .error msg
                    | .outOfFuel => .outOfFuel
                    | .error msg => .error msg
                | _ =>
                  -- Primary path failed, try neutralType on vF
                  match synthNeutralWithDeriv fuel Γ [] vF with
                  | .ok (some ⟨tyF, hvF_tyF⟩) =>
                    -- fV ⊑ tyF via: fV ⊑ vF ⊑ tyF
                    let hfV_tyF : Subtype' [] Γ fV tyF := .trans hfV_vF hvF_tyF
                    match hwp2 : exposePi fuel fV tyF with
                    | some (.lam piDom piBody) =>
                      let hfV_pi := exposePi_deriv [] Γ hfV_tyF hwp2
                      let step2 : Subtype' [] Γ (.app fV aV) (.app (.lam piDom piBody) aV) :=
                        .app_cong hfV_pi (.refl _) (.refl _)
                      -- Domain check
                      match subCheckOpen fuel Γ aV piDom with
                      | .ok true =>
                        match hev : evalSubst fuel SubstEval.unfBound
                            (.app (.lam piDom piBody) aV) with
                        | .ok v =>
                            let step3 := (evalSubst_equiv_open' [] Γ hev).2
                            .ok ⟨v, .trans step1 (.trans step2 step3)⟩
                        | .outOfFuel => .outOfFuel
                        | .error msg => .error msg
                      | .ok false =>
                        -- Arg check failed, try neutral ascent
                        match synthNeutralWithDeriv fuel Γ [] aV with
                        | .ok (some ⟨aTy, _⟩) =>
                          match subCheckOpen fuel Γ aTy piDom with
                          | .ok true =>
                            match hev : evalSubst fuel SubstEval.unfBound
                                (.app (.lam piDom piBody) aV) with
                            | .ok v =>
                                let step3 := (evalSubst_equiv_open' [] Γ hev).2
                                .ok ⟨v, .trans step1 (.trans step2 step3)⟩
                            | .outOfFuel => .outOfFuel
                            | .error msg => .error msg
                          | .ok false => .error s!"synth: arg ⊄ dom at .app"
                          | .outOfFuel => .outOfFuel
                          | .error msg => .error msg
                        | .ok none => .error s!"synth: arg ⊄ dom at .app (no ascent)"
                        | .outOfFuel => .outOfFuel
                        | .error msg => .error msg
                      | .outOfFuel => .outOfFuel
                      | .error msg => .error msg
                    | _ => .error s!"synth: applied non-Π head (ascended to non-Π)"
                  | .ok none => .error s!"synth: applied non-Π head (no ascent type)"
                  | .outOfFuel => .outOfFuel
                  | .error msg => .error msg
              | .outOfFuel => .outOfFuel
              | .error msg => .error msg
            | .outOfFuel => .outOfFuel
            | .error msg => .error msg
          | .outOfFuel => .outOfFuel
          | .error msg => .error msg
        | .outOfFuel => .outOfFuel
        | .error msg => .error msg
  termination_by fuel
  decreasing_by all_goals first | (simp_wf; omega) | omega | simp_wf

/-! ## Public surface -/

/-- Produce a `WTValue` for `e`. Validates well-typedness via a
structural walk that delegates each typing question to the
complete structural engine `SubstEval.subCheckOpen`. -/
def synth (e : Expr) (fuel : Nat := 5000) : Outcome WTValue := do
  if !e.closedAt 0 then
    .error s!"synth: input contains unbound bvars (not closed)"
  else
    let ⟨v, _⟩ ← synthCore fuel [] e
    pure ⟨v⟩

/-- Structural subtype check on already-typed values. -/
def subCheck (a b : WTValue) (fuel : Nat := 5000) : Outcome Bool :=
  SubstEval.subCheck fuel a.whnf b.whnf

/-- Convenience: run `synth` on both inputs, then `subCheck`. -/
def subCheckE (fuel : Nat) (e τ : Expr) : Outcome Bool := do
  let a ← synth e fuel
  let b ← synth τ fuel
  subCheck a b fuel

end Och
