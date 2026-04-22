import Och.NbE
import Och.SubCheckVal

/-!
# Bidirectional type inference over the NbE domain

NbE evaluation (`NbE.eval`) is type-blind at β: dropping the domain
check was necessary to avoid self-reference (`Array_ done_` would
otherwise need to discharge `done_ ⊑ dNat` *during* the
normalisation that sets up that very goal). The cost is that
ill-typed inner applications β through silently, so `subCheckVal`
alone can't reject `appendVec_wrong` (`appendArrays T n1 n1 arr1
arr2` with `arr2 : Array_ n2 T` where `Array_ n1 T` is expected).

This file provides a separate **syntactic** pass that walks the
unevaluated term and at each `.app f a` checks the argument against
the function's domain. It is the standard bidirectional architecture
(infer for elimination forms, check for introduction forms), with
NbE supplying normalisation and `subCheckVal` supplying conversion.

The pass is *not* mutually recursive with normalisation: it calls
`NbE.eval` and `subCheckVal` as black boxes, so `subCheckVal aTy dom`
runs on already-evaluated `Val`s with their own bounded `unf` budget,
independent of the outer term's β path.

A `.fix`/`.iota` is treated as a black box of its annotation; the
pass does *not* recurse into the body. So `appendArrays` (a fix)
exposes only its declared signature, and the unprovable
`Array_ (dsucc pred) T ⊑ Pair Type Type` cast inside its body —
which holds operationally but not via type-ascent — never surfaces.
Recursing into fix bodies is future work (it needs the body checked
against the annotation under a self-hypothesis, i.e. the standard
fixpoint typing rule).
-/

namespace NbE

abbrev TyEnv := Array Val

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

/-- Unfold a fix/iota wrapper to expose a `.lam` head.

For `.fix ann cl`, the self is the fix itself (μ-unfold). For
`.iota ann cl`, the self is the *inhabitant* `inhab` whose type
we're computing — `n : ι self. B` means `n : B[self:=n]`. -/
def whnfPi (fuel : Nat) (inhab : Val) (ty : Val) : Option Val :=
  go unfBound ty
where
  go : Nat → Val → Option Val
  | 0, v => some v
  | _+1, v@(.lam ..) => some v
  | n+1, v@(.fix _ cl) => do
      let v' ← cl.open fuel v
      go n v'
  | n+1, .iota _ cl => do
      let v' ← cl.open fuel inhab
      go n v'
  -- Bot is not a Π head (it's non-applicable). Return `none` so
  -- callers treat it as "no Π exposed" — see `docs/ideas/bottom.md`.
  | _, .bot => none
  | _, v => some v

mutual
  /-- Synthesise the type of `e`.

  - `.error msg` — `e` is ill-typed (a domain check failed).
  - `.ok none` — `e` is well-typed but no principal type was
    found (the caller falls back to value-level conversion).
  - `.ok (some τ)` — `e : τ`. -/
  def tyInfer (fuel : Nat) (Γ : TyEnv) (ρ : Env)
      (e : Expr) : Except String (Option Val) :=
    match fuel with
    | 0 => .error "tyInfer: out of fuel"
    | fuel + 1 =>
      match e with
      | .bvar k =>
          if h : Γ.size - 1 - k < Γ.size then
            .ok (some Γ[Γ.size - 1 - k])
          else
            .error s!"tyInfer: unbound bvar {k}"
      | .type => .ok (some .type)
      | .bot =>
          -- Bot has no synthesized type. It can only appear in checking
          -- mode against `Type`. See `docs/ideas/bottom.md`.
          .error "tyInfer: Bot has no synthesized type; use as annotation"
      | .asc e' τ => do
          let some τV := eval fuel unfBound ρ τ
            | .error "tyInfer: asc τ eval"
          let okInner ← tyCheck fuel Γ ρ e' τV
          if !okInner then
            .error s!"tyInfer: ascription {repr τ} rejected"
          else .ok (some τV)
      | .fix ann _ | .iota ann _ =>
          -- A9: the annotation is the *claimed* type, returned
          -- so `.app`-chains with fix heads (`dadd n m`,
          -- `appendArrays …`) can infer through. It is *not*
          -- sound on its own — `(fix x:Nat. unit_)` yields `Nat`
          -- here even though the body has type `Unit`. Callers
          -- that need a verified type must go through
          -- `tyCheck`'s `.fix`/`.iota` arm (which checks
          -- `subCheckVal (eval e) expected`); the `.letE` arm
          -- of `tyCheck` does exactly that after consulting
          -- `tyInfer val`. SoundnessAudit A9.
          match eval fuel unfBound ρ ann with
          | none => .error "tyInfer: fix/iota ann eval"
          | some annV => .ok (some annV)
      | .lam dom body => do
          let some domV := eval fuel unfBound ρ dom
            | .error "tyInfer: lam dom eval"
          let fresh := Val.neutral (.var Γ.size)
          let bodyTy? ← tyInfer fuel (Γ.push domV) (fresh :: ρ) body
          match bodyTy? with
          | none => .ok none
          | some bodyTy =>
            -- Reify the codomain so the resulting Π-type can be
            -- re-opened with a concrete argument later. Quote at
            -- depth `Γ.size + 1` so the fresh binder becomes bvar 0
            -- and outer levels line up with `ρ`.
            match quote fuel (Γ.size + 1) bodyTy with
            | none => .ok none
            | some bodyTyE =>
                .ok (some (.lam domV (Closure.mk' bodyTyE ρ)))
      | .app (.lam dom body) a => do
          -- β fast-path: an immediately-applied lambda. Och has
          -- no top-level definitions, so every reference to a
          -- helper like `mkVec`/`dpair` is inlined as a `.lam`
          -- chain at the use site. Going through the generic
          -- `.app` arm below would `tyInfer` the `.lam` head and
          -- reify its codomain via `quote`, only to immediately
          -- re-evaluate it under the argument — an avoidable
          -- round-trip that also defeats `subCheckVal`'s seen-set
          -- (the reified closure isn't `beq` to the source one).
          -- Instead just check the argument against the domain
          -- and recurse into the body with the argument bound.
          let some domV := eval fuel unfBound ρ dom
            | .error "tyInfer: β dom eval"
          let okArg ← tyCheck fuel Γ ρ a domV
          if !okArg then
            .error s!"tyInfer: β arg ⊄ dom at {spineSummary e 0} (arg={spineSummary a 0}, |Γ|={Γ.size})"
          else
            let some aV := eval fuel unfBound ρ a
              | .error "tyInfer: β arg eval"
            tyInfer fuel (Γ.push domV) (aV :: ρ) body
      | .app (.letE val fbody) a => do
          -- Let-headed application: float the `let` out so the
          -- arm above (or the generic one) can see the head.
          let (valV, valTy) ← letBinderType fuel Γ ρ val
          tyInfer fuel (Γ.push valTy) (valV :: ρ) (.app fbody (a.shift 1 0))
      | .app f a => do
          let fTy? ← tyInfer fuel Γ ρ f
          match fTy? with
          | none => .ok none
          | some fTy =>
              let some fV := eval fuel unfBound ρ f
                | .error "tyInfer: app head eval"
              match whnfPi fuel fV fTy with
              | some (.lam dom cl) => do
                  -- Domain check: the whole point of the pass.
                  let okArg ← tyCheck fuel Γ ρ a dom
                  if !okArg then
                    .error s!"tyInfer: arg ⊄ dom at {spineSummary e 0} (arg={spineSummary a 0}, |Γ|={Γ.size})"
                  else
                    let some aV := eval fuel unfBound ρ a
                      | .error "tyInfer: arg eval"
                    match cl.open fuel aV with
                    | none => .error "tyInfer: codomain open"
                    | some retTy => .ok (some retTy)
              | _ => .ok none
      | .letE val body => do
          let (valV, valTy) ← letBinderType fuel Γ ρ val
          tyInfer fuel (Γ.push valTy) (valV :: ρ) body
  termination_by (fuel, 0)

  /-- Check `e` against `expected`. -/
  def tyCheck (fuel : Nat) (Γ : TyEnv) (ρ : Env)
      (e : Expr) (expected : Val) : Except String Bool :=
    match fuel with
    | 0 => .error "tyCheck: out of fuel"
    | fuel + 1 =>
      match e with
      | .lam dom body => do
          let some domV := eval fuel unfBound ρ dom
            | .error "tyCheck: lam dom eval"
          -- Try to expose a Π head on the expected type. The
          -- inhabitant for ι-unfold is a fresh neutral of type
          -- `expected` (we're checking the term against it).
          let fresh := Val.neutral (.var Γ.size)
          match whnfPi fuel fresh expected with
          | some (.lam expDom expCl) => do
              let okDom ← subCheckVal fuel Γ [] expDom domV
              if !okDom then return false
              match expCl.open fuel fresh with
              | none => .error "tyCheck: expected codomain open"
              | some expBody =>
                  tyCheck fuel (Γ.push expDom) (fresh :: ρ) body expBody
          | _ => tyCheckFallback (fuel + 1) Γ ρ e expected
      | .letE val body => do
          let (valV, valTy) ← letBinderType fuel Γ ρ val
          tyCheck fuel (Γ.push valTy) (valV :: ρ) body expected
      | .asc e' τ => do
          let some τV := eval fuel unfBound ρ τ
            | .error "tyCheck: asc τ eval"
          let okInner ← tyCheck fuel Γ ρ e' τV
          if !okInner then return false
          subCheckVal fuel Γ [] τV expected
      | .fix _ _ | .iota _ _ => do
          -- A9: bypass `tyCheckFallback`'s tyInfer path here
          -- because `tyInfer` returns the *annotation* for
          -- fix/ι (which is what `.app`-chains need), but the
          -- annotation alone is not the term's type unless the
          -- body is well-formed. Checking `eval e ⊑ expected`
          -- via `subCheckVal` unfolds the fix/ι and exposes the
          -- body, so `(fix x:Nat. unit_) ⊑ Nat` correctly fails
          -- (`unit_ ⊑ Nat_body` is false). Sound by
          -- `subCheckVal_sound`. SoundnessAudit A9.
          let some eV := eval fuel unfBound ρ e
            | .error "tyCheck: fix/iota eval"
          subCheckVal fuel Γ [] eV expected
      | .bot =>
          -- Bot is acceptable only at `Val.type` — the bidirectional
          -- proxy for "used as a type, not a value". Other shapes
          -- fall through to the fallback, which goes via tyInfer,
          -- which errors — so the check rejects. See
          -- `docs/ideas/bottom.md`.
          match expected with
          | .type => .ok true
          | _ => tyCheckFallback (fuel + 1) Γ ρ e expected
      | _ => tyCheckFallback (fuel + 1) Γ ρ e expected
  termination_by (fuel, 2)

  /-- Fallback path of `tyCheck`: infer a type for `e` and
  compare against `expected` via `subCheckVal`; if no
  principal type, evaluate `e` itself and compare as a
  value. Lifted into the mutual block (was a `where`
  helper) so the `tyCheck (n+1) → tyCheckFallback (n+1) →
  tyInfer (n+1)` chain is visible to the termination
  checker (decreases tag at each step). -/
  def tyCheckFallback (fuel : Nat) (Γ : TyEnv) (ρ : Env)
      (e : Expr) (expected : Val) : Except String Bool := do
    let eTy? ← tyInfer fuel Γ ρ e
    match eTy? with
    | some eTy => subCheckVal fuel Γ [] eTy expected
    | none =>
        -- No principal type: fall back to evaluating the term
        -- itself and comparing as a value (handles `.type` and
        -- forms whose type isn't locally determined). This is
        -- what `NbE.subCheck` does, so it is at least as
        -- permissive on well-typed inputs.
        let some eV := eval fuel unfBound ρ e
          | .error "tyCheck: fallback eval"
        subCheckVal fuel Γ [] eV expected
  termination_by (fuel, 1)

  /-- Compute the binder type and value for a `let val in …`.
  Returns `(valV, valTy)` where `valV` is the evaluated value
  (pushed onto `ρ`) and `valTy` is the verified binder type
  (pushed onto `Γ`).

  If `tyInfer val` produces a type, it is *verified* via
  `tyCheck val t` before being trusted (A9: `tyInfer`'s fix/ι
  arm returns the bare annotation, which is only sound if the
  body is well-formed; the `tyCheck` round-trip routes fix/ι
  through the eval-then-`subCheckVal` arm). On verification
  failure or when no type is inferred, the value itself is
  used as the binder type (singleton-style — Och lets types
  be values; in practice the only un-annotated let-bindings
  in Std are type aliases like `let N = dNat in …`, where
  this is exactly right).

  Tag 3: called from `tyInfer (fuel+1)` [tag 0] and `tyCheck
  (fuel+1)` [tag 2] at the *decremented* fuel; calls back into
  `tyInfer fuel`/`tyCheck fuel` at the same fuel, decreasing
  on tag. -/
  def letBinderType (fuel : Nat) (Γ : TyEnv) (ρ : Env)
      (val : Expr) : Except String (Val × Val) := do
    let valTy? ← tyInfer fuel Γ ρ val
    let some valV := eval fuel unfBound ρ val
      | .error "letBinderType: val eval"
    match valTy? with
    | none => pure (valV, valV)
    | some t => do
      let okV ← tyCheck fuel Γ ρ val t
      pure (valV, if okV then t else valV)
  termination_by (fuel, 3)
end

/-- Top-level entry: type-check closed `e` against closed `τ`. -/
def typeCheck (fuel : Nat) (e τ : Expr) : Except String Bool := do
  let some τV := eval fuel unfBound [] τ
    | .error "typeCheck: τ eval"
  tyCheck fuel #[] [] e τV

-- De-partialised: confirm `unfold` works on each (was
-- `partial def`, so unfold previously failed and
-- `tyCheck_sound_closed` could not proceed).
example : tyCheck 1 #[] [] .type .type
        = tyCheck 1 #[] [] .type .type := by
  unfold tyCheck; rfl
example : tyInfer 1 #[] [] .type
        = tyInfer 1 #[] [] .type := by
  unfold tyInfer; rfl
example : whnfPi 1 .type .type = whnfPi 1 .type .type := by
  unfold whnfPi whnfPi.go; rfl

end NbE
