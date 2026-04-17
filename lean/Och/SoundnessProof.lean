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
    | iota_struct {S Γ annA annB clA clB bA bB} :
        clA.openω (.neutral (.var Γ.size)) = some bA →
        clB.openω (.neutral (.var Γ.size)) = some bB →
        SubV ((.iota annA clA, .iota annB clB) :: S) Γ annA annB →
        SubV ((.iota annA clA, .iota annB clB) :: S) (Γ.push annB) bA bB →
        SubV S Γ (.iota annA clA) (.iota annB clB)
    | fix_struct {S Γ annA annB clA clB bA bB} :
        clA.openω (.neutral (.var Γ.size)) = some bA →
        clB.openω (.neutral (.var Γ.size)) = some bB →
        SubV ((.«fix» annA clA, .«fix» annB clB) :: S) Γ annA annB →
        SubV ((.«fix» annA clA, .«fix» annB clB) :: S) (Γ.push annB) bA bB →
        SubV S Γ (.«fix» annA clA) (.«fix» annB clB)
    | stuckRec_struct {S Γ fA aA fB aB} :
        SubV ((.neutral (.stuckRec fA aA),
               .neutral (.stuckRec fB aB)) :: S) Γ fA fB →
        SubV ((.neutral (.stuckRec fA aA),
               .neutral (.stuckRec fB aB)) :: S) Γ fB fA →
        SubV ((.neutral (.stuckRec fA aA),
               .neutral (.stuckRec fB aB)) :: S) Γ aA aB →
        SubV ((.neutral (.stuckRec fA aA),
               .neutral (.stuckRec fB aB)) :: S) Γ aB aA →
        SubV S Γ (.neutral (.stuckRec fA aA))
                  (.neutral (.stuckRec fB aB))
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
    /-- When the recursive head's annotation is not a Π, the
    algorithm returns the bare annotation. -/
    | stuckRecFixAnn {Γ ann cl arg} :
        (∀ d c, ann ≠ .lam d c) →
        SynthN Γ (.stuckRec (.«fix» ann cl) arg) ann
    | stuckRecIotaAnn {Γ ann cl arg} :
        (∀ d c, ann ≠ .lam d c) →
        SynthN Γ (.stuckRec (.iota ann cl) arg) ann
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

/-- BEq-disequality reflection (needed for the re-vapp arms'
`if b' == b then .ok false else …` discrimination). -/
theorem Val.ne_of_beq_false {a b : Val} (h : (a == b) = false) :
    a ≠ b := fun heq => by simp [heq] at h

/-!
## Algorithm → `SubV`: the mutual reflection

The five algorithmic functions in the mutual block reflect
into the five corresponding propositions. Each theorem's
`termination_by` mirrors the algorithm's exactly, so Lean's
checker accepts the recursive calls at the same positions
the algorithm makes them.
-/

mutual

theorem subCheckVal_subV
    {fuel : Nat} {Γ : TyCtx} {S : List (Val × Val)} {a b : Val}
    (hfuel : fuel ≤ fuelω)
    (h : subCheckVal fuel Γ S a b = .ok true) :
    SubV S Γ a b := by
  match fuel, hfuel, h with
  | 0, _, h => unfold subCheckVal at h; simp at h
  | fuel + 1, hfuel, h =>
    have hfuel' : fuel ≤ fuelω := Nat.le_of_succ_le hfuel
    unfold subCheckVal at h
    simp only [] at h
    split at h
    · next hab => exact (eq_of_beq hab) ▸ SubV.refl
    split at h
    · next hseen => exact SubV.hyp (seen_any_mem hseen)
    split at h
    · next hbt => exact (eq_of_beq hbt) ▸ SubV.top
    exact subCheckValMatch_subV hfuel' h
termination_by (fuel, 0)

theorem subCheckValMatch_subV
    {fuel : Nat} {Γ : TyCtx} {S : List (Val × Val)} {a b : Val}
    (hfuel : fuel ≤ fuelω)
    (h : subCheckValMatch fuel Γ S a b = .ok true) :
    SubV S Γ a b := by
  have ih : ∀ {Γ' S' a' b'},
      subCheckVal fuel Γ' S' a' b' = .ok true → SubV S' Γ' a' b' :=
    fun hr => subCheckVal_subV hfuel hr
  unfold subCheckValMatch at h
  simp only [] at h
  split at h
  -- lam-lam
  · next domA clA domB clB =>
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
  -- iota-iota: structural OR iotaIntro fallback. Both branches
  -- map to SubV constructors (iota_struct / iota_intro), but
  -- the do-block decomposition is doubled (one for structural,
  -- one for fallback). Defer to a helper:
  · sorry
  -- fix-fix: structural OR unfoldFixR fallback (same shape)
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
  -- stuckRec, stuckRec: structural OR re-vapp on either side
  · sorry
  -- _, .neutral .stuckRec: re-vapp R
  · split at h
    · simp at h
    rename_i b' hvapp
    split at h
    · simp at h
    rename_i hbeq
    exact SubV.revapp_R
      (Val.ne_of_beq_false (by simpa using hbeq))
      (ih h)
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
  -- .neutral .stuckRec, _ : re-vapp L
  · split at h
    · simp at h
    rename_i a' hvapp
    -- The stuckRec components are auto-named by split; extract
    -- via the structure of `hvapp : vapp fuel 4 ?f ?arg = some a'`.
    split at h
    · simp at h
    rename_i hbeq
    exact SubV.revapp_L
      (Val.ne_of_beq_false (by simpa using hbeq))
      (ih h)
  -- .neutral, .neutral: subCheckNeutral OR neutralAscent
  · split at h
    · rename_i hN
      exact SubV.neutral_struct (subCheckNeutral_subN hfuel hN)
    · exact neutralAscent_subV hfuel h
  -- .neutral, _ : neutralAscent
  · exact neutralAscent_subV hfuel h
  -- _, .neutral _
  · simp at h
  -- .type, _
  · simp at h
  -- _, .type
  · exact SubV.top
termination_by (fuel, 1)

theorem subCheckNeutral_subN
    {fuel : Nat} {Γ : TyCtx} {S : List (Val × Val)} {nA nB : Neutral}
    (hfuel : fuel ≤ fuelω)
    (h : subCheckNeutral fuel Γ S nA nB = .ok true) :
    SubN S Γ nA nB := by
  match fuel, hfuel, h with
  | 0, _, h => unfold subCheckNeutral at h; simp at h
  | fuel + 1, hfuel, h =>
    have hfuel' : fuel ≤ fuelω := Nat.le_of_succ_le hfuel
    have _ihV : ∀ {Γ' S' a' b'},
        subCheckVal fuel Γ' S' a' b' = .ok true → SubV S' Γ' a' b' :=
      fun hr => subCheckVal_subV hfuel' hr
    have _ihN : ∀ {Γ' S' nA' nB'},
        subCheckNeutral fuel Γ' S' nA' nB' = .ok true → SubN S' Γ' nA' nB' :=
      fun hr => subCheckNeutral_subN hfuel' hr
    unfold subCheckNeutral at h
    simp only [] at h
    split at h
    -- .var, .var
    next l1 l2 =>
      simp only [Except.ok.injEq] at h
      exact (eq_of_beq h) ▸ SubN.var
    -- .app, .app: don't bind pattern vars; `split` through the
    -- do-block instead. Each `split` on a `bind` introduces the
    -- intermediate result; the impossible branches close by
    -- `simp_all`.
    next =>
      simp only [bind, Except.bind, pure, Except.pure] at h
      split at h
      · simp at h
      rename_i hd hhd
      cases hd with
      | false => simp at h
      | true =>
      simp only [Bool.not_true, Bool.false_eq_true,
                 ↓reduceIte, bind, Except.bind, pure,
                 Except.pure] at h
      split at h
      · simp at h
      rename_i fwd hfwd
      cases fwd with
      | false => simp at h
      | true =>
      simp only [Bool.not_true, Bool.false_eq_true,
                 ↓reduceIte] at h
      exact SubN.app (_ihN hhd) (_ihV hfwd) (_ihV h)
    -- .stuckRec, .stuckRec
    next =>
      simp only [bind, Except.bind, pure, Except.pure] at h
      split at h
      · simp at h
      rename_i r1 h1
      cases r1 with
      | false => simp at h
      | true =>
      simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte,
                 bind, Except.bind, pure, Except.pure] at h
      split at h
      · simp at h
      rename_i r2 h2
      cases r2 with
      | false => simp at h
      | true =>
      simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte,
                 bind, Except.bind, pure, Except.pure] at h
      split at h
      · simp at h
      rename_i r3 h3
      cases r3 with
      | false => simp at h
      | true =>
      simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h
      exact SubN.stuckRec (_ihV h1) (_ihV h2) (_ihV h3) (_ihV h)
    -- _, _ → false
    next => exfalso; injection h with h; exact Bool.noConfusion h
termination_by (fuel, 0)

theorem neutralAscent_subV
    {fuel : Nat} {Γ : TyCtx} {S : List (Val × Val)} {nA : Neutral} {b : Val}
    (hfuel : fuel ≤ fuelω)
    (h : neutralAscent fuel Γ S nA b = .ok true) :
    SubV S Γ (.neutral nA) b := by
  match fuel, hfuel, h with
  | 0, _, h => unfold neutralAscent at h; simp at h
  | fuel + 1, hfuel, h =>
    have hfuel' : fuel ≤ fuelω := Nat.le_of_succ_le hfuel
    have _ihV : ∀ {Γ' S' a' b'},
        subCheckVal fuel Γ' S' a' b' = .ok true → SubV S' Γ' a' b' :=
      fun hr => subCheckVal_subV hfuel' hr
    have _ihS : ∀ {Γ' nA' τ'},
        synthNeutral fuel Γ' nA' = .ok (some τ') → SynthN Γ' nA' τ' :=
      fun hr => synthNeutral_synthN hfuel' hr
    unfold neutralAscent at h
    simp only [] at h
    split at h
    -- .var lvl
    next lvl =>
      split at h
      next ty hty =>
        exact SubV.neutral_ascent (.var hty) (_ihV h)
      next => simp at h
    -- .app n arg
    next =>
      simp only [bind, Except.bind] at h
      split at h
      · simp at h
      rename_i n'ty hn'ty
      cases hn'ty' : n'ty with
      | none => simp [hn'ty'] at h
      | some n'tyV =>
      cases hn'tyV : n'tyV with
      | lam dom cl =>
        simp only [hn'ty', hn'tyV] at h
        split at h
        next retTy hopen =>
          exact SubV.neutral_ascent
            (.app (_ihS (by rw [hn'ty, hn'ty', hn'tyV]))
                  (Closure.openω_of_open hfuel' hopen))
            (_ihV h)
        next => simp at h
      | _ => simp [hn'ty', hn'tyV] at h
    -- .stuckRec f arg
    next =>
      split at h
      · simp at h
      rename_i a' hvapp
      split at h
      · simp at h
      rename_i hbeq
      exact SubV.revapp_L
        (Val.ne_of_beq_false (by simpa using hbeq))
        (_ihV h)
termination_by (fuel, 0)

theorem synthNeutral_synthN
    {fuel : Nat} {Γ : TyCtx} {nA : Neutral} {τ : Val}
    (hfuel : fuel ≤ fuelω)
    (h : synthNeutral fuel Γ nA = .ok (some τ)) :
    SynthN Γ nA τ := by
  match fuel, hfuel, h with
  | 0, _, h => unfold synthNeutral at h; simp at h
  | fuel + 1, hfuel, h =>
    have hfuel' : fuel ≤ fuelω := Nat.le_of_succ_le hfuel
    have _ihS : ∀ {Γ' nA' τ'},
        synthNeutral fuel Γ' nA' = .ok (some τ') → SynthN Γ' nA' τ' :=
      fun hr => synthNeutral_synthN hfuel' hr
    unfold synthNeutral at h
    simp only [] at h
    split at h
    -- .var lvl
    next lvl =>
      simp only [Except.ok.injEq] at h
      exact SynthN.var h
    -- .app n' arg
    next =>
      simp only [bind, Except.bind] at h
      split at h
      · simp at h
      rename_i n'ty hn'ty
      cases hn'ty' : n'ty with
      | none => simp [hn'ty'] at h
      | some n'tyV =>
      cases hn'tyV : n'tyV with
      | lam dom cl =>
        simp only [hn'ty', hn'tyV, Except.ok.injEq] at h
        exact SynthN.app
          (_ihS (by rw [hn'ty, hn'ty', hn'tyV]))
          (Closure.openω_of_open hfuel' h)
      | _ => simp [hn'ty', hn'tyV] at h
    -- .stuckRec f arg
    next =>
      -- Two layers: match on f (fix/iota/other), then on ann
      -- (lam/other). Each path leads to a SynthN constructor.
      sorry
termination_by (fuel, 0)

end

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
