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
  partial def Val.beq : Val → Val → Bool
    | .type, .type => true
    | .lam d1 c1, .lam d2 c2 => d1.beq d2 && c1.beq c2
    | .iota a1 c1, .iota a2 c2 => a1.beq a2 && c1.beq c2
    | .fix a1 c1, .fix a2 c2 => a1.beq a2 && c1.beq c2
    | .neutral n1, .neutral n2 => n1.beq n2
    | _, _ => false

  partial def Neutral.beq : Neutral → Neutral → Bool
    | .var l1, .var l2 => l1 == l2
    | .app n1 v1, .app n2 v2 => n1.beq n2 && v1.beq v2
    | .stuckRec f1 a1, .stuckRec f2 a2 => f1.beq f2 && a1.beq a2
    | _, _ => false

  partial def Closure.beq : Closure → Closure → Bool
    | ⟨b1, e1⟩, ⟨b2, e2⟩ =>
        b1 == b2 && e1.length == e2.length
        && (e1.zip e2).all (fun (v1, v2) => v1.beq v2)
end

instance : BEq Val := ⟨Val.beq⟩

/-- Open a closure with the given value bound at index 0. -/
def Closure.open (fuel : Nat) (cl : Closure) (v : Val) : Option Val :=
  eval fuel unfBound (v :: cl.env) cl.body

/-- Open a closure with a fresh neutral at de Bruijn level `depth`. -/
def Closure.openFresh (fuel depth : Nat) (cl : Closure) : Option Val :=
  cl.open fuel (.neutral (.var depth))

/-- Type context indexed by de Bruijn *level*: `tyCtx[k]` is the
    type of the fresh neutral `.var k`. -/
abbrev TyCtx := Array Val

mutual
  /-- Subtype check in the Val domain. `tyCtx[k]` is the type of
      `.var k` (de Bruijn level). `seen` is the coinductive
      assumption set. -/
  partial def subCheckVal (fuel : Nat) (tyCtx : TyCtx)
      (seen : List (Val × Val)) (a b : Val) : Except String Bool :=
    let depth := tyCtx.size
    match fuel with
    | 0 => .error "subCheckVal: out of fuel"
    | fuel + 1 =>
      if a == b then .ok true
      else if seen.any (fun (a', b') => a == a' && b == b') then .ok true
      else if b == .type then .ok true
      else
        match a, b with
        | .lam domA clA, .lam domB clB => do
            let contra ← subCheckVal fuel tyCtx seen domB domA
            if !contra then return false
            let bodyA ← match clA.openFresh fuel depth with
              | some v => .ok v | none => .error "subCheckVal: open A"
            let bodyB ← match clB.openFresh fuel depth with
              | some v => .ok v | none => .error "subCheckVal: open B"
            subCheckVal fuel (tyCtx.push domB) seen bodyA bodyB
        | _, .iota _ann clB =>
            -- iotaIntro: open the RHS ι with the LHS value as `self`.
            -- This is the key sharing step — `a` is bound by reference
            -- in the environment, not copied into every `:self` slot.
            let seen' := (a, b) :: seen
            match clB.open fuel a with
            | none => .error "subCheckVal: iotaIntro open"
            | some bodyB' => subCheckVal fuel tyCtx seen' a bodyB'
        | _, .fix _ann clB =>
            -- unfoldFixR: open the RHS fix with itself as `self`.
            let seen' := (a, b) :: seen
            match clB.open fuel b with
            | none => .error "subCheckVal: fixR open"
            | some b' => subCheckVal fuel tyCtx seen' a b'
        | _, .neutral (.stuckRec f arg) =>
            -- RHS is a stuck recursive head: re-apply at full unf so
            -- the canonical NF is compared.
            let seen' := (a, b) :: seen
            match vapp fuel unfBound f arg with
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
            match vapp fuel unfBound f arg with
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

  /-- Compare two neutral spines structurally: same head variable
      and pointwise-equal arguments (both directions, since an
      opaque head isn't known to be monotone). -/
  partial def subCheckNeutral (fuel : Nat) (tyCtx : TyCtx)
      (seen : List (Val × Val)) (a b : Neutral) : Except String Bool :=
    match fuel with
    | 0 => .error "subCheckNeutral: out of fuel"
    | fuel + 1 =>
      match a, b with
      | .var l1, .var l2 => .ok (l1 == l2)
      | .app n1 v1, .app n2 v2 => do
          let hd ← subCheckNeutral fuel tyCtx seen n1 n2
          if !hd then return false
          let fwd ← subCheckVal fuel tyCtx seen v1 v2
          let bwd ← subCheckVal fuel tyCtx seen v2 v1
          return (fwd && bwd)
      | _, _ => .ok false

  /-- Type ascent for a neutral on the LHS: synthesise its type
      from `tyCtx` and check `type ⊑ b`. Sound because every value
      `v : T` satisfies `{v} ⊑ T`. -/
  partial def neutralAscent (fuel : Nat) (tyCtx : TyCtx)
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
          match vapp fuel unfBound f arg with
          | none => .ok false
          | some a' =>
              if a' == .neutral a then .ok false
              else subCheckVal fuel tyCtx seen' a' b

  /-- Synthesise the type of a neutral. -/
  partial def synthNeutral (fuel : Nat) (tyCtx : TyCtx)
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
      | .stuckRec f _arg =>
          -- A recursive head's type is its annotation.
          match f with
          | .fix ann _ | .iota ann _ => .ok (some ann)
          | _ => .ok none
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
  - DNat positives via iotaIntro (`dzero ⊑ dNat`)
  - DNat negatives (`dNat ⊄ dzero`)

Open (next loop iteration):
  - `done_/dtwo/dthree ⊑ dNat` → `.error "stuckRec L"`. The
    stuckRec re-eval `vapp fuel unfBound f arg` returns `none`
    somewhere in the chain. Likely a fuel/unf interaction:
    `Closure.open` uses `unfBound=32`, so the `(dsucc dzero)`
    self-reference inside done_'s λP annotation unfolds 32 times
    during the iota-L open, each evaluating the dNat annotation,
    exhausting fuel. Try `Closure.open` at unf=1 (matching
    `quoteClosure`).
  - `Pair zero_ unit_ ⊑ Array_ done_ Nat_` → `.ok false`. NbE
    reduces both sides correctly (per NbETests), so the issue
    is in the comparison. Probably the `subCheckNeutral`
    bidirectional arg check is too strict for the Pair body
    (it demands `zero_ ≡ Nat_` instead of `zero_ ⊑ Nat_`). The
    head there is a *parametric* lambda, not an opaque bvar, so
    monotonicity holds and one direction suffices — but
    distinguishing parametric from opaque heads needs the head's
    type.
-/

end NbE
