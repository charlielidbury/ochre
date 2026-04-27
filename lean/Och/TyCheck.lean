import Och.EvalSubst

/-!
# Bidirectional type inference (substitution-based pipeline)

The bidirectional type-checker walks the unevaluated `Expr` and at
each `.app f a` checks the argument against the function's domain.
This is the standard "infer for elimination forms, check for
introduction forms" architecture, with `SubstEval.evalSubst` supplying
WHNF-evaluation and `SubstEval.subCheckOpen` supplying conversion.

## Why a separate pass

`evalSubst`'s β arm substitutes unconditionally, so a structural
subtype check (`subCheck`) alone can't reject `appendVec_wrong`
(`appendArrays T n1 n1 arr1 arr2` with `arr2 : Array_ n2 T` where
`Array_ n1 T` is expected). The syntactic walk in `tyCheck` catches
the mismatch *before* β fires.

The pass is *not* mutually recursive with normalisation: it calls
`evalSubst` and `subCheckOpen` as black boxes, so conversion runs
on already-evaluated `Expr`s with their own bounded `unf` budget,
independent of the outer term's β path.

A `.fix`/`.iota` is treated as a black box of its annotation; the
pass does *not* recurse into the body. So `appendArrays` (a fix)
exposes only its declared signature, and the unprovable
`Array_ (dsucc pred) T ⊑ Pair Type Type` cast inside its body —
which holds operationally but not via type-ascent — never surfaces.
Recursing into fix bodies is future work (it needs the body checked
against the annotation under a self-hypothesis, i.e. the standard
fixpoint typing rule).

## Substrate

This file used to live on the env-NbE substrate (`NbE.eval`,
`NbE.Val`, `subCheckVal`). The 2026-04-27 engine-collapse refactor
migrated it to the substitution substrate; the data shape is now:

  - Types are `Expr` (with free variables encoded as level-vars,
    matching `EvalSubst`'s convention: `bvar (levelOffset + k)` is
    the level-`k` free variable).
  - Open binders are entered via `SubstEval.openFreshTop`, which
    substitutes `bvar 0` with a fresh level-var.
  - The synthesised type of a lambda is rebuilt by closing the
    fresh level-var (`SubstEval.closeLevelVar`) so the result is a
    regular Π in standard de Bruijn form.

`tyInfer` / `tyCheck` return `Outcome α`. The three constructors
(`.ok` / `.outOfFuel` / `.error`) carry distinct information:
`.ok` = verdict, `.outOfFuel` = fuel exhaustion (recoverable),
`.error` = genuine type error.
-/

namespace TyCheck

open SubstEval

/-- Type context: `Γ[k]` is the type of `freshLevelVar k`. Mirrors
    NbE's `TyEnv`. -/
abbrev TyEnv := Array Expr

/-- Compact diagnostic: spine head constructor + arity. -/
private def spineSummary : Expr → Nat → String
  | .app f _, n => spineSummary f (n+1)
  | .lam .., n => s!"lam·{n}"
  | .fix .., n => s!"fix·{n}"
  | .iota .., n => s!"iota·{n}"
  | .bvar k, n => s!"?{k}·{n}"
  | .letE .., n => s!"let·{n}"
  | .asc .., n => s!"asc·{n}"
  | .type, n => s!"Type·{n}"
  | .bot, n => s!"Bot·{n}"

/-- Unfold a fix/iota wrapper to expose a Π head.

For `.fix ann cl`, the self is the fix itself (μ-unfold). For
`.iota ann cl`, the self is the *inhabitant* `inhab` whose type
we're computing — `n : ι self. B` means `n : B[self:=n]`.

Returns `Option Expr`: `none` means "no Π exposed" (either the
body isn't structurally a Π after unfolding, or evaluation
failed). Callers treat any failure as "no Π" and fall through to
the next strategy. -/
private def whnfPi (fuel : Nat) (inhab : Expr) (ty : Expr) : Option Expr :=
  -- Force `ty` to HNF first; then unfold fix/iota wrappers.
  match evalSubst fuel SubstEval.unfBound ty with
  | .ok ty' => go SubstEval.unfBound ty'
  | _ => none
where
  go : Nat → Expr → Option Expr
  | 0, e => some e
  | _+1, e@(.lam ..) => some e
  | n+1, e@(.fix _ann body) =>
      -- Unfold self with the fix itself, then re-evaluate.
      -- Use a small unf budget (4, mirroring NbE's `Closure.open`)
      -- so self-referential annotations like `(succ_ m)→Type`
      -- in `done_`'s body terminate after a few rounds.
      match evalSubst fuel 4 (substTop body e) with
      | .ok e' => go n e'
      | _ => none
  | n+1, .iota _ann body =>
      -- Unfold self with the inhabitant, then re-evaluate.
      match evalSubst fuel 4 (substTop body inhab) with
      | .ok e' => go n e'
      | _ => none
  -- Bot is not a Π head (it's non-applicable). Return `none` so
  -- callers treat it as "no Π exposed" — see `docs/ideas/bottom.md`.
  | _, .bot => none
  | _, e => some e

mutual
  /-- Synthesise the type of `e`.

  - `.error msg` — `e` is ill-typed (a domain check failed).
  - `.outOfFuel` — fuel exhausted; recoverable by re-running with
    more fuel.
  - `.ok none` — `e` is well-typed but no principal type was
    found (the caller falls back to value-level conversion).
  - `.ok (some τ)` — `e : τ`. -/
  def tyInfer (fuel : Nat) (Γ : TyEnv) (e : Expr) :
      Outcome (Option Expr) :=
    match fuel with
    | 0 => .outOfFuel
    | fuel + 1 =>
      match e with
      | .bvar _ =>
          match asLevelVar e with
          | some lvl =>
              if h : lvl < Γ.size then
                .ok (some Γ[lvl])
              else .error s!"tyInfer: unbound level-var {lvl} (|Γ|={Γ.size})"
          | none =>
              -- A bound bvar at this point is a stuck term — the
              -- caller should have opened it with a level-var.
              .error s!"tyInfer: unbound bvar (closed-form input expected)"
      | .type => .ok (some .type)
      | .bot =>
          -- Bot has no synthesized type. It can only appear in checking
          -- mode against `Type`. See `docs/ideas/bottom.md`.
          .error "tyInfer: Bot has no synthesized type; use as annotation"
      | .asc e' τ => do
          let τV ← evalSubst fuel SubstEval.unfBound τ
          let okInner ← tyCheck fuel Γ e' τV
          if !okInner then
            .error s!"tyInfer: ascription {repr τ} rejected"
          else .ok (some τV)
      | .fix ann _ | .iota ann _ => do
          -- A9: the annotation is the *claimed* type, returned
          -- so `.app`-chains with fix heads (`dadd n m`,
          -- `appendArrays …`) can infer through. It is *not*
          -- sound on its own — `(fix x:Nat. unit_)` yields `Nat`
          -- here even though the body has type `Unit`. Callers
          -- that need a verified type must go through
          -- `tyCheck`'s `.fix`/`.iota` arm (which checks
          -- `subCheck (eval e) expected`); the `.letE` arm of
          -- `tyCheck` does exactly that after consulting
          -- `tyInfer val`. SoundnessAudit A9.
          let annV ← evalSubst fuel SubstEval.unfBound ann
          .ok (some annV)
      | .lam dom body => do
          let domV ← evalSubst fuel SubstEval.unfBound dom
          let depth := Γ.size
          -- Open the body under a fresh level-var so its type can
          -- be synthesised in an extended Γ.
          let bodyOpen := openFreshTop body depth
          let bodyTy? ← tyInfer fuel (Γ.push domV) bodyOpen
          match bodyTy? with
          | none => .ok none
          | some bodyTy =>
            -- Close the fresh level-var back to `bvar 0` so the
            -- resulting Π-type is a regular `.lam`.
            let bodyTyClosed := closeLevelVar depth bodyTy
            .ok (some (.lam domV bodyTyClosed))
      | .app (.lam dom body) a => do
          -- β fast-path: an immediately-applied lambda. Och has
          -- no top-level definitions, so every reference to a
          -- helper like `mkVec`/`dpair` is inlined as a `.lam`
          -- chain at the use site. Going through the generic
          -- `.app` arm below would `tyInfer` the `.lam` head and
          -- return its synthesised Π-type, only to immediately
          -- substitute the argument back in — an avoidable
          -- round-trip. Instead just check the argument against
          -- the domain and recurse into the body with the
          -- argument substituted.
          let domV ← evalSubst fuel SubstEval.unfBound dom
          let okArg ← tyCheck fuel Γ a domV
          if !okArg then
            .error s!"tyInfer: β arg ⊄ dom at {spineSummary e 0} (arg={spineSummary a 0}, |Γ|={Γ.size})"
          else do
            let aV ← evalSubst fuel SubstEval.unfBound a
            tyInfer fuel Γ (substTop body aV)
      | .app (.letE val fbody) a => do
          -- Let-headed application: bind `val`, then continue
          -- with `.app fbody-opened a`. We push `valTy` to Γ
          -- (NOT `valV`) and open `fbody` under a fresh level-var,
          -- mirroring NbE's `tyInfer fuel (Γ.push valTy)
          -- (valV :: ρ) (.app fbody (a.shift 1 0))`.
          --
          -- Crucial for A9: when `letBinderType` fails to verify
          -- the binder, it returns `valTy = valV` (singleton-style).
          -- Looking up the level-var in Γ then yields the value
          -- itself, which `whnfPi` unfolds — exactly the path
          -- that catches an ill-typed `.fix` whose annotation
          -- is wider than its body.
          let (_valV, valTy) ← letBinderType fuel Γ val
          let depth := Γ.size
          let fbodyOpen := openFreshTop fbody depth
          tyInfer fuel (Γ.push valTy) (.app fbodyOpen a)
      | .app f a => do
          let fTy? ← tyInfer fuel Γ f
          match fTy? with
          | none => .ok none
          | some fTy => do
              let fV ← evalSubst fuel SubstEval.unfBound f
              match whnfPi fuel fV fTy with
              | some (.lam dom cl) => do
                  -- Domain check: the whole point of the pass.
                  let okArg ← tyCheck fuel Γ a dom
                  if !okArg then
                    .error s!"tyInfer: arg ⊄ dom at {spineSummary e 0} (arg={spineSummary a 0}, |Γ|={Γ.size})"
                  else do
                    let aV ← evalSubst fuel SubstEval.unfBound a
                    -- Apply the codomain to the argument. Use a small
                    -- unf budget (4, mirroring NbE's `Closure.open`)
                    -- so codomain bodies with self-referential
                    -- annotations don't blow the fuel.
                    let retTy ← evalSubst fuel 4 (substTop cl aV)
                    .ok (some retTy)
              | _ => .ok none
      | .letE val body => do
          let (valV, valTy) ← letBinderType fuel Γ val
          -- Push valTy into Γ, open body with the level-var.
          let depth := Γ.size
          let bodyOpen := openFreshTop body depth
          tyInfer fuel (Γ.push valTy) bodyOpen
            >>= fun bodyTy? => do
              -- Close the level-var: convert any reference to
              -- the let-bound name back into a `bvar 0` … but
              -- we want to substitute `valV` instead (since
              -- the whole `let` is going away). Equivalent move:
              -- substitute `valV` for the level-var.
              match bodyTy? with
              | none => .ok none
              | some bodyTy =>
                  let bodyTy' := substTop (closeLevelVar depth bodyTy) valV
                  .ok (some bodyTy')
  termination_by (fuel, 0)

  /-- Check `e` against `expected`. -/
  def tyCheck (fuel : Nat) (Γ : TyEnv) (e : Expr) (expected : Expr) :
      Outcome Bool :=
    match fuel with
    | 0 => .outOfFuel
    | fuel + 1 =>
      match e with
      | .lam dom body => do
          let domV ← evalSubst fuel SubstEval.unfBound dom
          -- Try to expose a Π head on the expected type. The
          -- inhabitant for ι-unfold is a fresh level-var at
          -- depth `Γ.size`.
          let depth := Γ.size
          let fresh := freshLevelVar depth
          match whnfPi fuel fresh expected with
          | some (.lam expDom expBody) => do
              let okDom ← subCheckOpen fuel Γ expDom domV
              if !okDom then return false
              -- Open both bodies with the same fresh.
              let bodyOpen := openFreshTop body depth
              let expBodyOpen := substTop expBody fresh
              tyCheck fuel (Γ.push expDom) bodyOpen expBodyOpen
          | _ => tyCheckFallback (fuel + 1) Γ e expected
      | .letE val body => do
          let (_valV, valTy) ← letBinderType fuel Γ val
          let depth := Γ.size
          let bodyOpen := openFreshTop body depth
          tyCheck fuel (Γ.push valTy) bodyOpen expected
      | .asc e' τ => do
          let τV ← evalSubst fuel SubstEval.unfBound τ
          let okInner ← tyCheck fuel Γ e' τV
          if !okInner then return false
          subCheckOpen fuel Γ τV expected
      | .fix _ _ | .iota _ _ => do
          -- A9: bypass `tyCheckFallback`'s tyInfer path here
          -- because `tyInfer` returns the *annotation* for
          -- fix/ι (which is what `.app`-chains need), but the
          -- annotation alone is not the term's type unless the
          -- body is well-formed. Checking `eval e ⊑ expected`
          -- via `subCheckOpen` unfolds the fix/ι and exposes
          -- the body, so `(fix x:Nat. unit_) ⊑ Nat` correctly
          -- fails (`unit_ ⊑ Nat_body` is false).
          -- SoundnessAudit A9.
          let eV ← evalSubst fuel SubstEval.unfBound e
          subCheckOpen fuel Γ eV expected
      | .bot =>
          -- Bot is acceptable only at `.type` — the bidirectional
          -- proxy for "used as a type, not a value". Other shapes
          -- fall through to the fallback, which goes via tyInfer,
          -- which errors — so the check rejects. See
          -- `docs/ideas/bottom.md`.
          match expected with
          | .type => .ok true
          | _ => tyCheckFallback (fuel + 1) Γ e expected
      | _ => tyCheckFallback (fuel + 1) Γ e expected
  termination_by (fuel, 2)

  /-- Fallback path of `tyCheck`: infer a type for `e` and
  compare against `expected` via `subCheckOpen`; if no
  principal type, evaluate `e` itself and compare as a
  value. Lifted into the mutual block (was a `where`
  helper) so the `tyCheck (n+1) → tyCheckFallback (n+1) →
  tyInfer (n+1)` chain is visible to the termination
  checker (decreases tag at each step). -/
  def tyCheckFallback (fuel : Nat) (Γ : TyEnv) (e : Expr) (expected : Expr) :
      Outcome Bool := do
    let eTy? ← tyInfer fuel Γ e
    match eTy? with
    | some eTy => subCheckOpen fuel Γ eTy expected
    | none => do
        -- No principal type: fall back to evaluating the term
        -- itself and comparing as a value (handles `.type` and
        -- forms whose type isn't locally determined). This is
        -- what the structural `subCheck` does, so it is at least
        -- as permissive on well-typed inputs.
        let eV ← evalSubst fuel SubstEval.unfBound e
        subCheckOpen fuel Γ eV expected
  termination_by (fuel, 1)

  /-- Compute the binder type and value for a `let val in …`.
  Returns `(valV, valTy)` where `valV` is the evaluated value
  (substituted into the body) and `valTy` is the verified
  binder type (pushed onto `Γ`).

  If `tyInfer val` produces a type, it is *verified* via
  `tyCheck val t` before being trusted (A9: `tyInfer`'s fix/ι
  arm returns the bare annotation, which is only sound if the
  body is well-formed; the `tyCheck` round-trip routes fix/ι
  through the eval-then-`subCheck` arm). On verification
  failure or when no type is inferred, the value itself is
  used as the binder type (singleton-style — Och lets types
  be values; in practice the only un-annotated let-bindings
  in Std are type aliases like `let N = dNat in …`, where
  this is exactly right). -/
  def letBinderType (fuel : Nat) (Γ : TyEnv) (val : Expr) :
      Outcome (Expr × Expr) := do
    let valTy? ← tyInfer fuel Γ val
    let valV ← evalSubst fuel SubstEval.unfBound val
    match valTy? with
    | none => pure (valV, valV)
    | some t => do
      let okV ← tyCheck fuel Γ val t
      pure (valV, if okV then t else valV)
  termination_by (fuel, 3)
end

/-- Top-level entry: type-check closed `e` against closed `τ`.

Marked `private` after the engine-collapse refactor — the public
typing surface is `Och.synth` + `Och.subCheck` (`Och/API.lean`).
This stays around for `Och.API.synth`'s internal call to
`tyInfer` (which is part of the same mutual block) and for the
remaining `tyInfer.isError` audit pins. -/
private def typeCheck (fuel : Nat) (e τ : Expr) : Outcome Bool := do
  let τV ← evalSubst fuel SubstEval.unfBound τ
  tyCheck fuel #[] e τV

-- De-partialised: confirm `unfold` works on each.
example : tyCheck 1 #[] .type .type
        = tyCheck 1 #[] .type .type := by
  unfold tyCheck; rfl
example : tyInfer 1 #[] .type
        = tyInfer 1 #[] .type := by
  unfold tyInfer; rfl
example : whnfPi 1 .type .type = whnfPi 1 .type .type := by
  unfold whnfPi whnfPi.go; rfl

end TyCheck
