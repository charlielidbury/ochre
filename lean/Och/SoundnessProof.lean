import Och.NbE
import Och.SubCheckVal
import Och.Subtyping

/-!
# `subCheckVal_sound`: the arm-by-arm proof

`Soundness.lean` states the target theorems; this file builds
the proof of the algorithmic-→-declarative direction. The
strategy is fuel induction on `subCheckVal` (now non-partial),
with one case per match arm.

The bridge between the `Val` domain (algorithm) and the `Expr`
domain (`Subtype'`) is `quote`. Rather than thread `quote`
through every IH, we work with a *Val-level relation* `SubV`
that mirrors `subCheckVal` arm-for-arm; the algorithm-→-`SubV`
direction is then a direct fuel induction with no
representation change. Relating `SubV` to the Expr-level
`Subtype'` (the quote bridge) is a separate lemma, factored
out so it can be attacked independently.

  subCheckVal ──(this file)──▶ SubV ──(quote bridge)──▶ Subtype'

This file currently proves the *guard arms* (refl, top, hyp)
of `subCheckVal_subV` and records exactly which supporting
lemmas the remaining arms need.
-/

namespace NbE

/-!
## Fuel-erased helpers

`SubV` is stated without a fuel parameter; the fuelled
algorithm's `cl.open fuel` results are lifted to a large
fixed budget. The eventual quote-bridge lemma needs
fuel-monotonicity for `eval` (recorded below as a sorried
lemma) so this is sound.
-/

def fuelω : Nat := 100000

def Closure.openω (cl : Closure) (v : Val) : Option Val :=
  cl.open fuelω v

def vappω (f a : Val) : Option Val :=
  vapp fuelω 4 f a

/-!
## The Val-level relation
-/

mutual
  /-- Val-level declarative subtyping. One constructor per
  `subCheckVal` arm that can return `.ok true`. -/
  inductive SubV : List (Val × Val) → TyCtx → Val → Val → Prop where
    | hyp {S Γ a b} : (a, b) ∈ S → SubV S Γ a b
    | refl {S Γ a} : SubV S Γ a a
    | top {S Γ a} : SubV S Γ a .type
    | lam {S Γ domA domB clA clB bA bB} :
        clA.openω (.neutral (.var Γ.size)) = some bA →
        clB.openω (.neutral (.var Γ.size)) = some bB →
        SubV S Γ domB domA →
        -- The algorithm pushes `domA` (LHS domain) — see
        -- SubCheckVal.lean:82. `Subtype'.lam` pushes the
        -- *target* domain `domB`. The discrepancy is bridged
        -- in `SubV_to_Subtype'` via `Subtype'.weaken`-on-Γ
        -- (a Γ-monotonicity lemma, not yet stated).
        SubV S (Γ.push domA) bA bB →
        SubV S Γ (.lam domA clA) (.lam domB clB)
    | iota_intro {S Γ a ann clB bB} :
        clB.openω a = some bB →
        SubV ((a, .iota ann clB) :: S) Γ a ann →
        SubV ((a, .iota ann clB) :: S) Γ a bB →
        SubV S Γ a (.iota ann clB)
    | unfold_fix_R {S Γ a ann clB bB} :
        clB.openω (.«fix» ann clB) = some bB →
        SubV ((a, .«fix» ann clB) :: S) Γ a bB →
        SubV S Γ a (.«fix» ann clB)
    | unfold_fix_L {S Γ ann clA bA c} :
        clA.openω (.«fix» ann clA) = some bA →
        SubV ((.«fix» ann clA, c) :: S) Γ bA c →
        SubV S Γ (.«fix» ann clA) c
    | unfold_iota_L {S Γ ann clA bA c} :
        clA.openω (.iota ann clA) = some bA →
        SubV ((.iota ann clA, c) :: S) Γ bA c →
        SubV S Γ (.iota ann clA) c
    | neutral_struct {S Γ nA nB} :
        SubN S Γ nA nB →
        SubV S Γ (.neutral nA) (.neutral nB)
    | neutral_ascent {S Γ nA τ b} :
        SynthN Γ nA τ →
        SubV S Γ τ b →
        SubV S Γ (.neutral nA) b
    | revapp_R {S Γ a b b'} :
        b' ≠ b →
        SubV ((a, b) :: S) Γ a b' →
        SubV S Γ a b
    | revapp_L {S Γ a a' c} :
        a' ≠ a →
        SubV ((a, c) :: S) Γ a' c →
        SubV S Γ a c

  /-- Val-level neutral congruence (mirrors `subCheckNeutral`). -/
  inductive SubN : List (Val × Val) → TyCtx → Neutral → Neutral → Prop where
    | var {S Γ k} : SubN S Γ (.var k) (.var k)
    | app {S Γ n1 n2 v1 v2} :
        SubN S Γ n1 n2 → SubV S Γ v1 v2 → SubV S Γ v2 v1 →
        SubN S Γ (.app n1 v1) (.app n2 v2)
    | stuckRec {S Γ fA aA fB aB} :
        SubV S Γ fA fB → SubV S Γ fB fA →
        SubV S Γ aA aB → SubV S Γ aB aA →
        SubN S Γ (.stuckRec fA aA) (.stuckRec fB aB)

  /-- Type synthesis for neutrals (mirrors `synthNeutral`). -/
  inductive SynthN : TyCtx → Neutral → Val → Prop where
    | var {Γ k τ} : Γ[k]? = some τ → SynthN Γ (.var k) τ
    | app {Γ n v dom cl τ} :
        SynthN Γ n (.lam dom cl) → cl.openω v = some τ →
        SynthN Γ (.app n v) τ
    | stuckRecFix {Γ ann cl arg dom cl' τ} :
        ann = .lam dom cl' → cl'.openω arg = some τ →
        SynthN Γ (.stuckRec (.«fix» ann cl) arg) τ
    | stuckRecIota {Γ ann cl arg dom cl' τ} :
        ann = .lam dom cl' → cl'.openω arg = some τ →
        SynthN Γ (.stuckRec (.iota ann cl) arg) τ
end

/-!
## Algorithm → `SubV`: the guard arms

The first three guards in `subCheckVal` (`a == b`, `b == .type`,
`(a,b) ∈ seen`) map directly to `.refl`/`.top`/`.hyp`. These are
proved here; the match arms (lam-lam, iota, fix, neutral) are
sorried with the supporting-lemma they need recorded below.
-/

/-- `Val.beq` is at least sound: equal `Val`s yield the same
`SubV`-class. We don't need full `beq → Eq` (which would
require closure-env canonicity); it suffices that beq-equal
values are inter-substitutable in `SubV`, which `.refl` gives
once we know `a = b` *up to* `SubV`. For the guard-arm proof
we take the stronger `beq → Eq` as a working assumption;
weakening it is future work. -/
axiom Val.beq_eq_ax {a b : Val} : (a == b) = true → a = b

/-- Membership decision: the `seen.any` guard. The algorithm
checks `a == a' && b == b'` (line 71); reflect into `∈`. -/
theorem seen_any_mem {S : List (Val × Val)} {a b : Val}
    (h : (S.any fun (a', b') => a == a' && b == b') = true) :
    (a, b) ∈ S := by
  rw [List.any_eq_true] at h
  obtain ⟨⟨x, y⟩, hmem, heq⟩ := h
  simp only [Bool.and_eq_true] at heq
  obtain ⟨hx, hy⟩ := heq
  cases Val.beq_eq_ax hx
  cases Val.beq_eq_ax hy
  exact hmem

set_option maxHeartbeats 4000000

/-- The succ-body of `subCheckVal` is large enough that
unfolding needs ~2-4M heartbeats. Refactoring `subCheckVal`
to factor out the match arms into a separate
`subCheckValMatch` would let it unfold at default heartbeats
(and is the cleaner long-term fix), but is deferred to avoid
conflicting with the val-beq-nonpartial worktree fork.

Guard order (from the source): `a == b`, then `seen.any`,
then `b == .type`, then the match. -/
theorem subCheckVal_subV
    {fuel : Nat} {Γ : TyCtx} {S : List (Val × Val)} {a b : Val}
    (h : subCheckVal fuel Γ S a b = .ok true) :
    SubV S Γ a b := by
  induction fuel generalizing Γ S a b with
  | zero => unfold subCheckVal at h; simp at h
  | succ fuel ih =>
    unfold subCheckVal at h
    simp only [] at h
    -- Guard 1: `a == b`
    split at h
    · next hab => exact (Val.beq_eq_ax hab) ▸ SubV.refl
    -- Guard 2: `seen.any`
    split at h
    · next hseen => exact SubV.hyp (seen_any_mem hseen)
    -- Guard 3: `b == .type`
    split at h
    · next hbt => exact (Val.beq_eq_ax hbt) ▸ SubV.top
    -- Match arms: each returns `.ok true` only via recursive
    -- `subCheckVal` calls; `ih` gives `SubV` for those, and
    -- the matching constructor combines them. ~12 cases.
    sorry

set_option maxHeartbeats 200000

/-!
## Supporting lemmas the match arms need

Each is mechanical given the right induction; recorded so
the next session can attack them in isolation.
-/

/-- Fuel monotonicity for `eval`/`vapp`: if a closure opens at
fuel `n`, it opens with the same result at any `m ≥ n`. Needed
so each match arm's `cl.open fuel` can be lifted to `cl.openω`.
The proof is a straightforward mutual induction on `eval`/
`vapp` (both now non-partial, so this is structural). -/
theorem Closure.open_fuel_mono {cl : Closure} {v r : Val} {n m : Nat}
    (hle : n ≤ m) (h : cl.open n v = some r) :
    cl.open m v = some r := by
  sorry

/-- Bridge to the Expr-level relation. Each `SubV` constructor
maps to a `Subtype'` constructor on the quoted forms; the
substantive content is that `quote` commutes with closure
opening (`quote (cl.openω v) = (quote-cl-body).subst 0
(quote v)` modulo de Bruijn level/index conversion). -/
theorem SubV_to_Subtype'
    {S Γ a b} (h : SubV S Γ a b)
    {Se : List (Expr × Expr)} {Γe : Ctx} {ae be : Expr}
    (hS : ∀ p ∈ S, ∃ pe ∈ Se,
            quote fuelω Γ.size p.1 = some pe.1 ∧
            quote fuelω Γ.size p.2 = some pe.2)
    (hΓ : ∀ k τ, Γ[k]? = some τ →
            ∃ τe, Γe.get? (Γ.size - 1 - k) = some τe ∧
                  quote fuelω (k+1) τ = some τe)
    (ha : quote fuelω Γ.size a = some ae)
    (hb : quote fuelω Γ.size b = some be) :
    Subtype' Se Γe ae be := by
  sorry

end NbE
