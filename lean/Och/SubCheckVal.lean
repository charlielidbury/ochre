import Och.NbE

/-!
# Subtype checking on NbE values

`subCheckNF` in `Eval.lean` works on `Expr` and calls `absEval` to
normalise after each substitution, which copies the substituend.
Swapping `absEval` for `NbE.nfInE` doesn't help because each call
quotes back to `Expr` and the next call re-evaluates the quoted
form, defeating the closure sharing.

`subCheckVal` works directly on `NbE.Val`. iotaIntro opens the RHS
ι closure with the *LHS Val* in the environment — one pointer, no
copy. lam-lam opens both closures with the same fresh neutral. The
seen-set holds `(Val × Val)` pairs.
-/

namespace NbE

mutual
  def Val.beq : Val → Val → Bool
    | .type, .type => true
    | .lam d1 c1, .lam d2 c2 => d1.beq d2 && c1.beq c2
    | .iota a1 c1, .iota a2 c2 => a1.beq a2 && c1.beq c2
    | .fix a1 c1, .fix a2 c2 => a1.beq a2 && c1.beq c2
    | .neutral n1, .neutral n2 => n1.beq n2
    | _, _ => false

  def Neutral.beq : Neutral → Neutral → Bool
    | .var l1, .var l2 => l1 == l2
    | .app n1 v1, .app n2 v2 => n1.beq n2 && v1.beq v2
    | .stuckRec f1 a1, .stuckRec f2 a2 => f1.beq f2 && a1.beq a2
    | _, _ => false

  def Closure.beq : Closure → Closure → Bool
    | ⟨b1, e1⟩, ⟨b2, e2⟩ =>
        b1 == b2 && Env.beq e1 e2

  def Env.beq : List Val → List Val → Bool
    | [], [] => true
    | v1 :: r1, v2 :: r2 => v1.beq v2 && Env.beq r1 r2
    | _, _ => false
end

instance : BEq Val := ⟨Val.beq⟩

@[simp] theorem Val.beq_def (a b : Val) : (a == b) = Val.beq a b := rfl

mutual
  theorem Val.beq_eq : ∀ (a b : Val), Val.beq a b = true → a = b
    | .type, b, h => by
        cases b <;> simp_all [Val.beq]
    | .lam d1 c1, b, h => by
        cases b <;> simp_all [Val.beq]
        exact ⟨Val.beq_eq _ _ h.1, Closure.beq_eq _ _ h.2⟩
    | .iota a1 c1, b, h => by
        cases b <;> simp_all [Val.beq]
        exact ⟨Val.beq_eq _ _ h.1, Closure.beq_eq _ _ h.2⟩
    | .«fix» a1 c1, b, h => by
        cases b <;> simp_all [Val.beq]
        exact ⟨Val.beq_eq _ _ h.1, Closure.beq_eq _ _ h.2⟩
    | .neutral n1, b, h => by
        cases b <;> simp_all [Val.beq]
        exact Neutral.beq_eq _ _ h

  theorem Neutral.beq_eq : ∀ (a b : Neutral), Neutral.beq a b = true → a = b
    | .var l1, b, h => by
        cases b <;> simp_all [Neutral.beq]
    | .app n1 v1, b, h => by
        cases b <;> simp_all [Neutral.beq]
        exact ⟨Neutral.beq_eq _ _ h.1, Val.beq_eq _ _ h.2⟩
    | .stuckRec f1 a1, b, h => by
        cases b <;> simp_all [Neutral.beq]
        exact ⟨Val.beq_eq _ _ h.1, Val.beq_eq _ _ h.2⟩

  theorem Closure.beq_eq : ∀ (a b : Closure), Closure.beq a b = true → a = b
    | ⟨b1, e1⟩, ⟨b2, e2⟩, h => by
        simp only [Closure.beq, Bool.and_eq_true] at h
        obtain ⟨hb, he⟩ := h
        rw [eq_of_beq hb, Env.beq_eq _ _ he]

  theorem Env.beq_eq : ∀ (a b : List Val), Env.beq a b = true → a = b
    | [], b, h => by
        cases b <;> simp_all [Env.beq]
    | v1 :: r1, b, h => by
        cases b <;> simp_all [Env.beq]
        exact ⟨Val.beq_eq _ _ h.1, Env.beq_eq _ _ h.2⟩
end

mutual
  theorem Val.beq_refl : ∀ (a : Val), Val.beq a a = true
    | .type => by simp only [Val.beq]
    | .lam d c => by
        simp only [Val.beq, Bool.and_eq_true]
        exact ⟨Val.beq_refl d, Closure.beq_refl c⟩
    | .iota a c => by
        simp only [Val.beq, Bool.and_eq_true]
        exact ⟨Val.beq_refl a, Closure.beq_refl c⟩
    | .«fix» a c => by
        simp only [Val.beq, Bool.and_eq_true]
        exact ⟨Val.beq_refl a, Closure.beq_refl c⟩
    | .neutral n => by
        simp only [Val.beq]; exact Neutral.beq_refl n

  theorem Neutral.beq_refl : ∀ (a : Neutral), Neutral.beq a a = true
    | .var l => by simp only [Neutral.beq]; exact beq_self_eq_true l
    | .app n v => by
        simp only [Neutral.beq, Bool.and_eq_true]
        exact ⟨Neutral.beq_refl n, Val.beq_refl v⟩
    | .stuckRec f a => by
        simp only [Neutral.beq, Bool.and_eq_true]
        exact ⟨Val.beq_refl f, Val.beq_refl a⟩

  theorem Closure.beq_refl : ∀ (a : Closure), Closure.beq a a = true
    | ⟨b, e⟩ => by
        simp only [Closure.beq, Bool.and_eq_true]
        exact ⟨beq_self_eq_true b, Env.beq_refl e⟩

  theorem Env.beq_refl : ∀ (a : List Val), Env.beq a a = true
    | [] => by simp only [Env.beq]
    | v :: r => by
        simp only [Env.beq, Bool.and_eq_true]
        exact ⟨Val.beq_refl v, Env.beq_refl r⟩
end

instance : LawfulBEq Val where
  eq_of_beq := Val.beq_eq _ _
  rfl := Val.beq_refl _

/-- Open a closure with the given value bound at index 0. The
    `unf` bound is small: under a binder the only fix/ι chains
    that need unfolding are short (e.g. `Array_ done_` → 3
    layers); the self-referential `(dsucc m)→Type` annotation in
    done_'s body would otherwise unfold `unfBound` times and
    exhaust subCheckVal's fuel. -/
def Closure.open (fuel : Nat) (cl : Closure) (v : Val) : Option Val :=
  eval fuel 4 (v :: cl.env) cl.body

/-- Open a closure with a fresh neutral at de Bruijn level `depth`. -/
def Closure.openFresh (fuel depth : Nat) (cl : Closure) : Option Val :=
  cl.open fuel (.neutral (.var depth))

/-- Fuel monotonicity for closure opening: if `open` succeeds
at fuel `n`, it succeeds with the same result at any `m ≥ n`.
Direct consequence of `eval_fuel_mono`. Used by
`subCheckVal_subV` to lift each arm's `cl.open fuel` result
to the fuel-erased `cl.openω`. -/
theorem Closure.open_fuel_mono {cl : Closure} {v r : Val} {n m : Nat}
    (hle : n ≤ m) (h : cl.open n v = some r) :
    cl.open m v = some r :=
  eval_fuel_mono hle h

theorem Closure.openFresh_fuel_mono {cl : Closure} {r : Val}
    {n m depth : Nat}
    (hle : n ≤ m) (h : cl.openFresh n depth = some r) :
    cl.openFresh m depth = some r :=
  Closure.open_fuel_mono hle h

/-- Type context indexed by de Bruijn *level*: `tyCtx[k]` is the
    type of the fresh neutral `.var k`. -/
abbrev TyCtx := Array Val

mutual
  /-- Subtype check in the Val domain. `tyCtx[k]` is the type of
      `.var k` (de Bruijn level). `seen` is the coinductive
      assumption set.

      Factored: the three guards live here; the per-shape
      match lives in `subCheckValMatch` so soundness proofs
      can unfold `subCheckVal` at default heartbeats. -/
  def subCheckVal (fuel : Nat) (tyCtx : TyCtx)
      (seen : List (Val × Val)) (a b : Val) : Except String Bool :=
    match fuel with
    | 0 => .error "subCheckVal: out of fuel"
    | fuel + 1 =>
      if a == b then .ok true
      else if seen.any (fun (a', b') => a == a' && b == b') then .ok true
      else if b == .type then .ok true
      else subCheckValMatch fuel tyCtx seen a b
  termination_by (fuel, 0)

  /-- The per-shape match arms of `subCheckVal`, factored out
  so each can be reasoned about in isolation. Called with the
  *post-decrement* fuel; recursive `subCheckVal fuel` calls
  here are at the same fuel (subCheckVal will decrement
  again). Termination is `(fuel, 1)` lex `(fuel, 0)`. -/
  def subCheckValMatch (fuel : Nat) (tyCtx : TyCtx)
      (seen : List (Val × Val)) (a b : Val) : Except String Bool :=
    let depth := tyCtx.size
        match a, b with
        | .lam domA clA, .lam domB clB => do
            let contra ← subCheckVal fuel tyCtx seen domB domA
            if !contra then return false
            let bodyA ← match clA.openFresh fuel depth with
              | some v => .ok v | none => .error "subCheckVal: open A"
            let bodyB ← match clB.openFresh fuel depth with
              | some v => .ok v | none => .error "subCheckVal: open B"
            -- Push the *target* domain (domB), not domA: the
            -- fresh variable's ascent type must be the smaller
            -- one so subterms in bodyB that need `fresh : domB`
            -- can ascend reflexively. Pushing domA made
            -- `(λx:Nat_. x) ⊑ (λx:zero_. zero_)` fail
            -- (SoundnessAudit A6) and diverge from subCheckNF.
            subCheckVal fuel (tyCtx.push domB) seen bodyA bodyB
        | .iota annA clA, .iota annB clB =>
            -- Try the structural path first: open both with the same
            -- fresh neutral and compare bodies. This lets two ι-values
            -- whose bodies coincide but whose *annotations* differ
            -- (e.g. dNat's let-bound `dsucc'` with `:done_` after
            -- iotaIntro vs the top-level `dsucc` with `:dNat`) line
            -- up. Falls back to iotaIntro if the structural path
            -- says no.
            let seen' := (a, b) :: seen
            let structural := do
              let annOk ← subCheckVal fuel tyCtx seen' annA annB
              if !annOk then return false
              let bodyA ← match clA.openFresh fuel depth with
                | some v => .ok v | none => .error "iota struct A"
              let bodyB ← match clB.openFresh fuel depth with
                | some v => .ok v | none => .error "iota struct B"
              subCheckVal fuel (tyCtx.push annB) seen' bodyA bodyB
            match structural with
            | .ok true => .ok true
            | _ => do
              -- iotaIntro fallback: BOTH premises (A5). Without
              -- this the ι-ι path bypassed the annotation check
              -- that the `_, .iota` arm enforces, so the two
              -- checkers diverged on `ι:Type.Type ⊑ ι:Nat_.Type`.
              let okAnn ← subCheckVal fuel tyCtx seen' a annB
              if !okAnn then .ok false
              else match clB.open fuel a with
              | none => .error "subCheckVal: iotaIntro open"
              | some bodyB' => subCheckVal fuel tyCtx seen' a bodyB'
        | .fix annA clA, .fix annB clB =>
            let seen' := (a, b) :: seen
            let structural := do
              let annOk ← subCheckVal fuel tyCtx seen' annA annB
              if !annOk then return false
              let bodyA ← match clA.openFresh fuel depth with
                | some v => .ok v | none => .error "fix struct A"
              let bodyB ← match clB.openFresh fuel depth with
                | some v => .ok v | none => .error "fix struct B"
              subCheckVal fuel (tyCtx.push annB) seen' bodyA bodyB
            match structural with
            | .ok true => .ok true
            | _ =>
              match clB.open fuel b with
              | none => .error "subCheckVal: fixR open"
              | some b' => subCheckVal fuel tyCtx seen' a b'
        | _, .iota ann clB => do
            -- iotaIntro: a ⊑ ι self:A. body ← a ⊑ A ∧ a ⊑
            -- body[self:=a]. BOTH premises (SoundnessAudit A5:
            -- skipping `a ⊑ A` accepted `dtrue ⊑ ι self:Nat_.
            -- Type` despite `dtrue ⊄ Nat_`). seen' is extended
            -- first so the annotation check closes
            -- coinductively when A is the enclosing recursive
            -- type (`fix B. ι self:B. …`). Opening the body
            -- with `a` as `self` is the key sharing step — `a`
            -- is bound by reference, not copied into every
            -- `:self` slot.
            let seen' := (a, b) :: seen
            let okAnn ← subCheckVal fuel tyCtx seen' a ann
            if !okAnn then .ok false
            else match clB.open fuel a with
            | none => .error "subCheckVal: iotaIntro open"
            | some bodyB' => subCheckVal fuel tyCtx seen' a bodyB'
        | _, .fix _ann clB =>
            -- unfoldFixR: open the RHS fix with itself as `self`.
            let seen' := (a, b) :: seen
            match clB.open fuel b with
            | none => .error "subCheckVal: fixR open"
            | some b' => subCheckVal fuel tyCtx seen' a b'
        | .neutral (.stuckRec fA aA), .neutral (.stuckRec fB aB) =>
            -- Both sides are recursive heads stuck on a neutral
            -- argument. The same recursive function can appear via
            -- two non-`beq` closures (e.g. the let-bound `dsucc`
            -- inside dNat's body — domain `N` resolved from env —
            -- vs the top-level `dsucc` — domain a closed `dNat`
            -- Expr). Re-vapp can't progress (both args neutral), so
            -- compare structurally: heads via the `.fix,.fix` arm
            -- (which η-opens with a shared fresh, normalising the
            -- closure-canonicity gap), args covariantly.
            let seen' := (a, b) :: seen
            let structural := do
              -- Heads and args must each be *equivalent* (A1):
              -- the recursive head may use its argument at any
              -- variance.
              let hd ← subCheckVal fuel tyCtx seen' fA fB
              if !hd then return false
              let hd' ← subCheckVal fuel tyCtx seen' fB fA
              if !hd' then return false
              let arg ← subCheckVal fuel tyCtx seen' aA aB
              if !arg then return false
              subCheckVal fuel tyCtx seen' aB aA
            match structural with
            | .ok true => .ok true
            | _ =>
              -- One side may still unfold (e.g. arg is a stuckRec
              -- that itself progresses).
              match vapp fuel 4 fB aB with
              | none => .error "subCheckVal: stuckRec R"
              | some b' =>
                if b' == b then
                  match vapp fuel 4 fA aA with
                  | none => .error "subCheckVal: stuckRec L"
                  | some a' =>
                    if a' == a then .ok false
                    else subCheckVal fuel tyCtx seen' a' b
                else subCheckVal fuel tyCtx seen' a b'
        | _, .neutral (.stuckRec f arg) =>
            -- RHS is a stuck recursive head: re-apply at full unf so
            -- the canonical NF is compared.
            let seen' := (a, b) :: seen
            match vapp fuel 4 f arg with
            | none => .error "subCheckVal: stuckRec R"
            | some b' =>
                if b' == b then .ok false
                else subCheckVal fuel tyCtx seen' a b'
        | .fix _ann clA, _ =>
            let seen' := (a, b) :: seen
            match clA.open fuel a with
            | none => .error "subCheckVal: fixL open"
            | some a' => subCheckVal fuel tyCtx seen' a' b
        | .iota _ann clA, _ =>
            let seen' := (a, b) :: seen
            match clA.open fuel a with
            | none => .error "subCheckVal: iotaL open"
            | some a' => subCheckVal fuel tyCtx seen' a' b
        | .neutral (.stuckRec f arg), _ =>
            let seen' := (a, b) :: seen
            match vapp fuel 4 f arg with
            | none => .error "subCheckVal: stuckRec L"
            | some a' =>
                if a' == a then .ok false
                else subCheckVal fuel tyCtx seen' a' b
        | .neutral nA, .neutral nB => do
            -- Try structural first; if that fails, fall through to
            -- type-ascent on the LHS.
            match subCheckNeutral fuel tyCtx seen nA nB with
            | .ok true => .ok true
            | _ => neutralAscent fuel tyCtx seen nA b
        | .neutral nA, _ => neutralAscent fuel tyCtx seen nA b
        | _, .neutral _ => .ok false
        | .type, _ => .ok false
        | _, .type => .ok true
  termination_by (fuel, 1)

  /-- Compare two neutral spines structurally: same head variable
      and pointwise-equal arguments (both directions, since an
      opaque head isn't known to be monotone). -/
  def subCheckNeutral (fuel : Nat) (tyCtx : TyCtx)
      (seen : List (Val × Val)) (a b : Neutral) : Except String Bool :=
    match fuel with
    | 0 => .error "subCheckNeutral: out of fuel"
    | fuel + 1 =>
      match a, b with
      | .var l1, .var l2 => .ok (l1 == l2)
      | .app n1 v1, .app n2 v2 => do
          -- Covariant on arguments to match subCheckNF's `.app, .app`
          -- arm. Bidirectional (`v1 ≡ v2`) would be sound for opaque
          -- heads but is too strict for Phase 1 — it rejects
          -- `Pair zero_ unit_ ⊑ Pair Nat_ Unit_` because
          -- `Unit_ ⊄ unit_`. The soundness audit (Phase 2) should
          -- revisit this with a type-directed monotonicity check.
          let hd ← subCheckNeutral fuel tyCtx seen n1 n2
          if !hd then return false
          -- Arguments must be *equivalent*, not merely sub-
          -- related: a neutral head can use its argument at any
          -- variance (SoundnessAudit A1). This is the standard
          -- congruence rule for stuck applications.
          let fwd ← subCheckVal fuel tyCtx seen v1 v2
          if !fwd then return false
          subCheckVal fuel tyCtx seen v2 v1
      | .stuckRec fA aA, .stuckRec fB aB => do
          -- Closure-canonicity normalisation, exposed here so it
          -- composes under `.app, .app` (e.g. comparing
          -- `Array_ (dadd n1 n2) T` against itself when the two
          -- `dadd`/`Array_` closures came via different paths).
          -- Heads and args must each be *equivalent*; a recursive
          -- type can use its index at any variance (A1).
          let hd ← subCheckVal fuel tyCtx seen fA fB
          if !hd then return false
          let hd' ← subCheckVal fuel tyCtx seen fB fA
          if !hd' then return false
          let arg ← subCheckVal fuel tyCtx seen aA aB
          if !arg then return false
          subCheckVal fuel tyCtx seen aB aA
      | _, _ => .ok false
  termination_by (fuel, 0)

  /-- Type ascent for a neutral on the LHS: synthesise its type
      from `tyCtx` and check `type ⊑ b`. Sound because every value
      `v : T` satisfies `{v} ⊑ T`. -/
  def neutralAscent (fuel : Nat) (tyCtx : TyCtx)
      (seen : List (Val × Val)) (a : Neutral) (b : Val)
      : Except String Bool :=
    match fuel with
    | 0 => .error "neutralAscent: out of fuel"
    | fuel + 1 =>
      match a with
      | .var lvl =>
          match tyCtx[lvl]? with
          | some ty => subCheckVal fuel tyCtx seen ty b
          | none => .ok false
      | .app n arg => do
          -- Type of `n arg`: synthesise type of `n`, must be an
          -- arrow `λx:_. retTy`; result type is retTy with x ↦ arg.
          match (← synthNeutral fuel tyCtx n) with
          | some (.lam _dom cl) =>
              match cl.open fuel arg with
              | some retTy => subCheckVal fuel tyCtx seen retTy b
              | none => .error "neutralAscent: retTy open"
          | _ => .ok false
      | .stuckRec f arg =>
          let seen' := (Val.neutral a, b) :: seen
          match vapp fuel 4 f arg with
          | none => .ok false
          | some a' =>
              if a' == .neutral a then .ok false
              else subCheckVal fuel tyCtx seen' a' b
  termination_by (fuel, 0)

  /-- Synthesise the type of a neutral. -/
  def synthNeutral (fuel : Nat) (tyCtx : TyCtx)
      (n : Neutral) : Except String (Option Val) :=
    match fuel with
    | 0 => .error "synthNeutral: out of fuel"
    | fuel + 1 =>
      match n with
      | .var lvl => .ok tyCtx[lvl]?
      | .app n' arg => do
          match (← synthNeutral fuel tyCtx n') with
          | some (.lam _dom cl) => .ok (cl.open fuel arg)
          | _ => .ok none
      | .stuckRec f arg =>
          -- `stuckRec f arg` denotes `f arg`; its type is `f`'s
          -- annotation applied to `arg` (one Π-elim), not the bare
          -- annotation.
          match f with
          | .fix ann _ | .iota ann _ =>
              match ann with
              | .lam _dom cl => .ok (cl.open fuel arg)
              | _ => .ok (some ann)
          | _ => .ok none
  termination_by (fuel, 0)
end

/-- Top-level entry: evaluate both sides to Vals, then compare. -/
def subCheck (fuel : Nat) (a b : Expr) : Except String Bool :=
  match eval fuel unfBound [] a, eval fuel unfBound [] b with
  | some a', some b' => subCheckVal fuel #[] [] a' b'
  | none, _ => .error "subCheck lhs: NbE out of fuel"
  | _, none => .error "subCheck rhs: NbE out of fuel"

/-!
## Status

Working:
  - DBool (`dtrue ⊑ dBool`, `dfalse ⊑ dBool`, `dBool ⊄ dtrue`,
    `dtrue ⊄ dfalse`)
  - Church Nat (`zero_ ⊑ Nat_`, `Nat_ ⊄ zero_`)
  - DNat (`dzero/done_/dtwo/dthree ⊑ dNat`, `dNat ⊄ dzero`,
    `dzero ⊄ done_`) — see DNat.lean
  - Array_ (`Pair zero_ unit_ ⊑ Array_ done_ Nat_`,
    `unit_ ⊄ Array_ done_ Nat_`)

The earlier `done_ ⊑ dNat → .ok false` failure was an artefact
of the *encoding*: the original `ι dNat:Type. … λpred:bvar0 …`
form let iotaIntro specialise the `pred` binder's type, forcing
an unsatisfiable `dNat ⊑ done_` in contravariant position. With
dNat re-encoded as `fix N:Type. ι self:N. …` (commit a58f476),
the type binder `N` is fix-bound and stable under iotaIntro.

That exposed a residual closure-canonicity gap: the let-bound
`dsucc` inside dNat's body and the top-level `dsucc` denote the
same function but live in non-`beq` closures (one resolves `N`
from env, the other from a closed Expr). The stuckRec-stuckRec
structural arm resolves this by recursing through `.fix,.fix`,
which η-opens both with a shared fresh and so normalises away
the env difference.

Open:
  - Vec/Sigma (`vecResult ⊑ Vec Nat`) — untested under this
    checker. The Sigma encoding goes through ι, so iotaIntro
    should fire; whether type-ascent through `unpack` works is
    the question.
-/

end NbE
