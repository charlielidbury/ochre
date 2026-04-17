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

/-- Membership decision: the `seen.any` guard. The algorithm
checks `a == a' && b == b'` (line 71); reflect into `∈` via
the `LawfulBEq Val` instance. -/
theorem seen_any_mem {S : List (Val × Val)} {a b : Val}
    (h : (S.any fun (a', b') => a == a' && b == b') = true) :
    (a, b) ∈ S := by
  rw [List.any_eq_true] at h
  obtain ⟨⟨x, y⟩, hmem, heq⟩ := h
  simp only [Bool.and_eq_true] at heq
  obtain ⟨hx, hy⟩ := heq
  cases eq_of_beq hx
  cases eq_of_beq hy
  exact hmem

/-- Lift a fuelled closure opening to the large fixed budget.
`Closure.open_fuel_mono` is now proven in SubCheckVal.lean. -/
theorem Closure.openω_of_open {cl : Closure} {v r : Val} {n : Nat}
    (hn : n ≤ fuelω) (h : cl.open n v = some r) :
    cl.openω v = some r :=
  Closure.open_fuel_mono hn h

theorem Closure.openω_of_openFresh {cl : Closure} {r : Val}
    {n depth : Nat} (hn : n ≤ fuelω)
    (h : cl.openFresh n depth = some r) :
    cl.openω (.neutral (.var depth)) = some r :=
  Closure.openω_of_open hn h

/-- Per-arm proof for `subCheckValMatch`. Takes the IH for
`subCheckVal` at `fuel` (the post-decrement value) as a
hypothesis. -/
theorem subCheckValMatch_subV
    {fuel : Nat} {Γ : TyCtx} {S : List (Val × Val)} {a b : Val}
    (hfuel : fuel ≤ fuelω)
    (ih : ∀ {Γ' S' a' b'},
            subCheckVal fuel Γ' S' a' b' = .ok true → SubV S' Γ' a' b')
    (h : subCheckValMatch fuel Γ S a b = .ok true) :
    SubV S Γ a b := by
  unfold subCheckValMatch at h
  simp only [] at h
  split at h
  -- lam-lam
  · next domA clA domB clB =>
    -- Case on each sub-computation BEFORE simping `h`, so `h`
    -- reduces to the final recursive call directly.
    rcases hcontra : subCheckVal fuel Γ S domB domA with _ | contra
    · simp_all [bind, Except.bind]
    cases contra with
    | false => simp_all [bind, Except.bind, pure, Except.pure]
    | true =>
    rcases hbA : clA.openFresh fuel Γ.size with _ | bA
    · simp_all [bind, Except.bind, pure, Except.pure]
    rcases hbB : clB.openFresh fuel Γ.size with _ | bB
    · simp_all [bind, Except.bind, pure, Except.pure]
    simp only [hcontra, hbA, hbB, bind, Except.bind, pure,
               Except.pure, Bool.not_true, Bool.false_eq_true,
               ↓reduceIte] at h
    exact SubV.lam
      (Closure.openω_of_openFresh hfuel hbA)
      (Closure.openω_of_openFresh hfuel hbB)
      (ih hcontra) (ih h)
  -- iota-iota: structural OR iotaIntro fallback
  · sorry
  -- fix-fix: structural OR unfoldFixR fallback
  · sorry
  -- _, .iota
  · next a' ann clB hNotIota =>
    simp only [bind, Except.bind] at h
    split at h
    · next _ => simp at h
    next okAnn hokAnn =>
    cases hc : okAnn with
    | false => rw [hc] at h; simp at h
    | true =>
    rw [hc] at h hokAnn; simp only [Bool.not_true, Bool.false_eq_true,
      ↓reduceIte] at h
    split at h
    · next _ => simp at h
    next bodyB' hopen =>
    exact SubV.iota_intro
      (Closure.openω_of_open hfuel hopen)
      (ih hokAnn) (ih h)
  -- _, .fix
  · next a' ann clB hNotFix =>
    split at h
    · next _ => simp at h
    next b' hopen =>
    exact SubV.unfold_fix_R
      (Closure.openω_of_open hfuel hopen)
      (ih h)
  -- stuckRec, stuckRec
  · sorry
  -- _, .neutral .stuckRec
  · sorry
  -- .fix, _
  · next ann clA c hNotR =>
    split at h
    · next _ => simp at h
    next a' hopen =>
    exact SubV.unfold_fix_L
      (Closure.openω_of_open hfuel hopen)
      (ih h)
  -- .iota, _
  · next ann clA c hNotR =>
    split at h
    · next _ => simp at h
    next a' hopen =>
    exact SubV.unfold_iota_L
      (Closure.openω_of_open hfuel hopen)
      (ih h)
  -- .neutral .stuckRec, _
  · sorry
  -- .neutral, .neutral
  · sorry
  -- .neutral, _
  · sorry
  -- _, .neutral _
  · simp at h
  -- .type, _
  · simp at h
  -- _, .type
  · exact SubV.top

/-- After factoring into `subCheckValMatch`, the guards
unfold at default heartbeats and the match arms are handled
by `subCheckValMatch_subV`. -/
theorem subCheckVal_subV
    {fuel : Nat} {Γ : TyCtx} {S : List (Val × Val)} {a b : Val}
    (hfuel : fuel ≤ fuelω)
    (h : subCheckVal fuel Γ S a b = .ok true) :
    SubV S Γ a b := by
  induction fuel generalizing Γ S a b with
  | zero => unfold subCheckVal at h; simp at h
  | succ fuel ih =>
    have hfuel' : fuel ≤ fuelω := Nat.le_of_succ_le hfuel
    unfold subCheckVal at h
    simp only [] at h
    -- Guard 1: `a == b`
    split at h
    · next hab => exact (eq_of_beq hab) ▸ SubV.refl
    -- Guard 2: `seen.any`
    split at h
    · next hseen => exact SubV.hyp (seen_any_mem hseen)
    -- Guard 3: `b == .type`
    split at h
    · next hbt => exact (eq_of_beq hbt) ▸ SubV.top
    -- Match arms
    exact subCheckValMatch_subV hfuel' (fun hr => ih hfuel' hr) h

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
