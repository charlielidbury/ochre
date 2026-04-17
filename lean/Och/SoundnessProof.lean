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
        -- Push the *target* domain (domB), matching both the
        -- algorithm (SubCheckVal.lean lam-lam arm, after the
        -- A6 fix) and `Subtype'.lam`.
        SubV S (Γ.push domB) bA bB →
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
        -- Productivity (A7): without this, body = `.bvar 0`
        -- gives `bA = a` and the recursive premise closes by
        -- `.hyp`, deriving `(fix self. self) ⊑ c` for every c
        -- — unsound (`⊤ ⊄ c` for c ≠ ⊤). The R-side
        -- `unfold_fix_R` needs no guard (`a ⊑ ⊤` is true).
        bA ≠ .«fix» ann clA →
        SubV ((.«fix» ann clA, c) :: S) Γ bA c →
        SubV S Γ (.«fix» ann clA) c
    | unfold_iota_L {S Γ ann clA bA c} :
        clA.openω (.iota ann clA) = some bA →
        bA ≠ .iota ann clA →
        SubV ((.iota ann clA, c) :: S) Γ bA c →
        SubV S Γ (.iota ann clA) c
    | neutral_struct {S Γ nA nB} :
        SubN S Γ nA nB →
        SubV S Γ (.neutral nA) (.neutral nB)
    | neutral_ascent {S Γ nA τ b} :
        SynthN Γ nA τ →
        SubV S Γ τ b →
        SubV S Γ (.neutral nA) b
    | revapp_R {S Γ a f arg b'} :
        -- The algorithm only reaches re-application when the
        -- RHS is a stuck recursive head; `b'` is the result
        -- of forcing one more unfold via `vappω`. WITHOUT this
        -- premise (just `b' ≠ b → … → SubV S Γ a b`) the
        -- constructor lets `b'` be arbitrary — instantiating
        -- `b' := .type` and discharging the recursive premise
        -- by `.top` made `SubV S Γ a b` hold for *every* a, b
        -- (bughunt-lite, 5-0). The `vappω` premise ties `b'`
        -- to `f arg`'s one-step unfold, matching exactly what
        -- the proof at `subCheckValMatch_subV`'s stuckRec arms
        -- already binds as `hvapp` and discards.
        vappω f arg = some b' →
        b' ≠ .neutral (.stuckRec f arg) →
        SubV ((a, .neutral (.stuckRec f arg)) :: S) Γ a b' →
        SubV S Γ a (.neutral (.stuckRec f arg))
    | revapp_L {S Γ f arg a' c} :
        vappω f arg = some a' →
        a' ≠ .neutral (.stuckRec f arg) →
        SubV ((.neutral (.stuckRec f arg), c) :: S) Γ a' c →
        SubV S Γ (.neutral (.stuckRec f arg)) c

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

/-- Lift a fuelled re-application to the large fixed budget. -/
theorem vappω_of_vapp {f arg r : Val} {n : Nat}
    (hn : n ≤ fuelω) (h : vapp n 4 f arg = some r) :
    vappω f arg = some r :=
  vapp_fuel_mono hn h

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
  -- iota-iota: structural OR iotaIntro fallback.
  · next annA clA annB clB =>
    -- Outer `match structural with | .ok true => … | _ => …`
    split at h
    · -- structural = .ok true → SubV.iota_struct
      rename_i hstruct
      rcases hannOk :
          subCheckVal fuel Γ
            ((.iota annA clA, .iota annB clB) :: S) annA annB
        with _ | annOk
      · simp_all [bind, Except.bind]
      cases annOk with
      | false => simp_all [bind, Except.bind, pure, Except.pure]
      | true =>
      rcases hbA : clA.openFresh fuel Γ.size with _ | bA
      · simp_all [bind, Except.bind, pure, Except.pure]
      rcases hbB : clB.openFresh fuel Γ.size with _ | bB
      · simp_all [bind, Except.bind, pure, Except.pure]
      simp only [hannOk, hbA, hbB, bind, Except.bind, pure,
                 Except.pure, Bool.not_true, Bool.false_eq_true,
                 ↓reduceIte] at hstruct
      exact SubV.iota_struct
        (Closure.openω_of_openFresh hfuel hbA)
        (Closure.openω_of_openFresh hfuel hbB)
        (ih hannOk) (ih hstruct)
    · -- fallback fired → SubV.iota_intro (same as `_, .iota`)
      simp only [bind, Except.bind] at h
      split at h
      · simp at h
      rename_i okAnn hokAnn
      cases hc : okAnn with
      | false => rw [hc] at h; simp at h
      | true =>
      rw [hc] at h hokAnn
      simp only [Bool.not_true, Bool.false_eq_true,
                 ↓reduceIte] at h
      split at h
      · simp at h
      rename_i bodyB' hopen
      exact SubV.iota_intro
        (Closure.openω_of_open hfuel hopen)
        (ih hokAnn) (ih h)
  -- fix-fix: structural OR unfoldFixR fallback (same shape).
  · next annA clA annB clB =>
    split at h
    · -- structural = .ok true → SubV.fix_struct
      rename_i hstruct
      rcases hannOk :
          subCheckVal fuel Γ
            ((.«fix» annA clA, .«fix» annB clB) :: S) annA annB
        with _ | annOk
      · simp_all [bind, Except.bind]
      cases annOk with
      | false => simp_all [bind, Except.bind, pure, Except.pure]
      | true =>
      rcases hbA : clA.openFresh fuel Γ.size with _ | bA
      · simp_all [bind, Except.bind, pure, Except.pure]
      rcases hbB : clB.openFresh fuel Γ.size with _ | bB
      · simp_all [bind, Except.bind, pure, Except.pure]
      simp only [hannOk, hbA, hbB, bind, Except.bind, pure,
                 Except.pure, Bool.not_true, Bool.false_eq_true,
                 ↓reduceIte] at hstruct
      exact SubV.fix_struct
        (Closure.openω_of_openFresh hfuel hbA)
        (Closure.openω_of_openFresh hfuel hbB)
        (ih hannOk) (ih hstruct)
    · -- fallback fired → SubV.unfold_fix_R (same as `_, .fix`)
      split at h
      · simp at h
      rename_i b' hopen
      exact SubV.unfold_fix_R
        (Closure.openω_of_open hfuel hopen)
        (ih h)
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
  · next fA aA fB aB =>
    split at h
    · -- structural = .ok true → SubV.stuckRec_struct
      rename_i hstruct
      rcases h1 : subCheckVal fuel Γ
          ((.neutral (.stuckRec fA aA),
            .neutral (.stuckRec fB aB)) :: S) fA fB with _ | r1
      · simp_all [bind, Except.bind]
      cases r1 with
      | false => simp_all [bind, Except.bind, pure, Except.pure]
      | true =>
      rcases h2 : subCheckVal fuel Γ
          ((.neutral (.stuckRec fA aA),
            .neutral (.stuckRec fB aB)) :: S) fB fA with _ | r2
      · simp_all [bind, Except.bind, pure, Except.pure]
      cases r2 with
      | false => simp_all [bind, Except.bind, pure, Except.pure]
      | true =>
      rcases h3 : subCheckVal fuel Γ
          ((.neutral (.stuckRec fA aA),
            .neutral (.stuckRec fB aB)) :: S) aA aB with _ | r3
      · simp_all [bind, Except.bind, pure, Except.pure]
      cases r3 with
      | false => simp_all [bind, Except.bind, pure, Except.pure]
      | true =>
      simp only [h1, h2, h3, bind, Except.bind, pure,
                 Except.pure, Bool.not_true, Bool.false_eq_true,
                 ↓reduceIte] at hstruct
      exact SubV.stuckRec_struct (ih h1) (ih h2) (ih h3) (ih hstruct)
    · -- fallback: re-vapp RHS, then maybe LHS
      split at h
      · simp at h  -- vapp fB aB = none → .error
      rename_i b' hvappR
      split at h
      · -- b' == b: try LHS
        rename_i hbeqR
        split at h
        · simp at h  -- vapp fA aA = none → .error
        rename_i a' hvappL
        split at h
        · simp at h  -- a' == a → .ok false
        rename_i hbeqL
        exact SubV.revapp_L
          (vappω_of_vapp hfuel hvappL)
          (Val.ne_of_beq_false (by simpa using hbeqL))
          (ih h)
      · -- b' ≠ b: revapp_R
        rename_i hbeqR
        exact SubV.revapp_R
          (vappω_of_vapp hfuel hvappR)
          (Val.ne_of_beq_false (by simpa using hbeqR))
          (ih h)
  -- _, .neutral .stuckRec: re-vapp R
  · split at h
    · simp at h
    rename_i b' hvapp
    split at h
    · simp at h
    rename_i hbeq
    exact SubV.revapp_R
      (vappω_of_vapp hfuel hvapp)
      (Val.ne_of_beq_false (by simpa using hbeq))
      (ih h)
  -- .fix, _
  · next ann clA c hNotR =>
    split at h
    · next _ => simp at h
    next a' hopen =>
    split at h
    · simp at h
    next hbeq =>
    exact SubV.unfold_fix_L
      (Closure.openω_of_open hfuel hopen)
      (Val.ne_of_beq_false (by simpa using hbeq))
      (ih h)
  -- .iota, _
  · next ann clA c hNotR =>
    split at h
    · next _ => simp at h
    next a' hopen =>
    split at h
    · simp at h
    next hbeq =>
    exact SubV.unfold_iota_L
      (Closure.openω_of_open hfuel hopen)
      (Val.ne_of_beq_false (by simpa using hbeq))
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
      (vappω_of_vapp hfuel hvapp)
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
        (vappω_of_vapp hfuel' hvapp)
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
      -- Outer match on `f`: the or-pattern `.fix ann _ | .iota
      -- ann _` produces two split cases plus the `_` catch-all.
      split at h
      · -- f = .fix ann cl; inner match on ann
        rename_i ann cl
        split at h
        · -- ann = .lam dom cl'; result = .ok (cl'.open fuel arg)
          rename_i dom cl'
          simp only [Except.ok.injEq] at h
          exact SynthN.stuckRecFix rfl (Closure.openω_of_open hfuel' h)
        · -- ann ≠ .lam; result = .ok (some ann); so τ = ann
          rename_i hnotlam
          simp only [Except.ok.injEq, Option.some.injEq] at h
          exact h ▸ SynthN.stuckRecFixAnn
            (fun d c heq => hnotlam d c heq)
      · -- f = .iota ann cl; same shape
        rename_i ann cl
        split at h
        · rename_i dom cl'
          simp only [Except.ok.injEq] at h
          exact SynthN.stuckRecIota rfl (Closure.openω_of_open hfuel' h)
        · rename_i hnotlam
          simp only [Except.ok.injEq, Option.some.injEq] at h
          exact h ▸ SynthN.stuckRecIotaAnn
            (fun d c heq => hnotlam d c heq)
      · -- f = other; result = .ok none; impossible since h : … = some τ
        simp at h
termination_by (fuel, 0)

end

/-!
## The quote bridge

`SubV` is over `Val`s; `Subtype'` is over `Expr`s. The bridge
quotes each piece. Three lemmas factor the work:

  - `quote_lam`/`quote_iota`/`quote_fix` (shape lemmas):
    `quote (.lam d c) = some e → ∃ de be, e = .lam de be ∧ …`
  - `quote_open` (NbE correctness): the quoted body of a
    closure opened with `v` is β-related to the substituted
    quote. This is the substantive lemma; everything else
    is bookkeeping.
  - Context/seen quoting respects extension (for the IH at
    `Γ.push`/`(p :: S)`).
-/

/-!
### The unf-mismatch blocker

`Closure.openω cl v = eval fuelω 4 (v :: cl.env) cl.body`
(unf = **4**), but `quoteClosure (n+1) d cl` evaluates the
body at unf = **1** before quoting. So even when `v` is the
fresh neutral `.var d`, the two evaluations can differ
whenever `cl.body` contains a *closed* recursive
application (e.g. `Array_ done_` captured in the env): at
unf=4 it unfolds three times, at unf=1 once. Hence
`quote (d+1) (cl.openω fresh) ≠ quoteClosure d cl` in
general — the directive's hoped-for `rfl` does not hold.

What does hold is that the two `eval` results are related
by repeated fix/iota unfolds, which `Subtype'.unfold_fix_*`
/`unfold_iota_L` capture. The precise sub-lemma:
-/

/-- **Unf-irrelevance modulo `Subtype'`**: evaluating the
same expression at the same fuel/env but different `unf`
budgets gives values whose quotes are `Subtype'`-equivalent.
This is the *core* of NbE correctness for Och: the only
non-determinism in `eval` is how many fix/ι layers unfold,
and each unfold is a `Subtype'.unfold_*` step.

Proof sketch: mutual induction on `n` over `eval`/`vapp`.
Every arm preserves the relation except `vapp`'s `.fix`/
`.iota` cases, which at `unf₁ > 0 = unf₂` produce an
unfolded body vs. a `.stuckRec`. Their quotes differ by
exactly one `unfold_fix_L/R` step, so are
`Subtype'`-equivalent. The hard part is threading the
relation through the recursive `eval` of the unfolded body
— that's where a logical relation `R d v e` (indexed by
depth and env) is needed instead of plain equivalence on
quotes. -/
theorem eval_unf_equiv {n unf₁ unf₂ ρ e v₁ v₂ depth e₁ e₂}
    (h₁ : eval n unf₁ ρ e = some v₁)
    (h₂ : eval n unf₂ ρ e = some v₂)
    (hq₁ : quote n depth v₁ = some e₁)
    (hq₂ : quote n depth v₂ = some e₂) :
    ∀ {S Γe}, Subtype' S Γe e₁ e₂ ∧ Subtype' S Γe e₂ e₁ := by
  sorry

/-- **Fresh-case correspondence, conditional on unf-
agreement.** When the unf=1 and unf=4 evaluations of the
closure body under a fresh variable agree (which holds
whenever the body has no closed recursive applications in
scope — in particular for every Std encoding that puts the
recursive call under a binder), `quoteClosure` and
`quote ∘ openω` give *equal* results modulo fuel.

This is the `SubV.lam` bridge case's exact need; the
unconditional version follows from `eval_unf_equiv`. -/
theorem quoteClosure_eq_quote_openω_fresh {cl : Closure}
    {depth : Nat} {r : Val} {bodye : Expr}
    (hopen : cl.openω (.neutral (.var depth)) = some r)
    (hqcl : quoteClosure fuelω depth cl = some bodye)
    -- The unf-agreement hypothesis. Discharged by
    -- `eval_unf_equiv` once that's proven; for now callers
    -- supply it (or sorry it) per closure.
    (hunf : eval (fuelω - 1) 1
              (.neutral (.var depth) :: cl.env) cl.body
            = eval fuelω 4
              (.neutral (.var depth) :: cl.env) cl.body) :
    quote fuelω (depth + 1) r = some bodye := by
  -- `cl.openω fresh = eval fuelω 4 (fresh :: env) body = some r`
  unfold Closure.openω Closure.open at hopen
  -- `quoteClosure fuelω d cl`: at fuelω = (fuelω-1)+1, the
  -- body is `do v ← eval (fuelω-1) 1 …; quote (fuelω-1) (d+1) v`.
  have hfω : fuelω = (fuelω - 1) + 1 := rfl
  rw [hfω] at hqcl; unfold quoteClosure at hqcl
  simp only [Option.bind_eq_bind, Option.bind_eq_some] at hqcl
  obtain ⟨v', hev', hq'⟩ := hqcl
  -- By the unf-agreement hypothesis, the unf=1 eval (giving
  -- v') equals the unf=4 eval (giving r). So v' = r.
  rw [hunf] at hev'
  rw [hev'] at hopen; cases hopen
  -- Now hq' : quote (fuelω-1) (d+1) r = some bodye. Lift to
  -- fuelω via `quote_fuel_mono`.
  exact quote_fuel_mono (Nat.sub_le _ _) hq'

/-- Quoting commutes with closure-opening up to `Subtype'`'s
β-conversion: opening `cl` with `v` and quoting gives an Expr
β-equivalent to substituting `quote v` into the closure's
quoted body. This is the standard NbE correctness theorem
(soundness direction), specialised to one closure-open.

Reduces to `eval_unf_equiv` (for the unf=1↔4 mismatch
between `quoteClosure` and `Closure.openω`) plus a
substitution lemma `quote (eval (v::ρ) body) ≡β
(quote (eval (fresh::ρ) body)).subst 0 (quote v)` — the
classic NbE soundness statement. Both halves need the same
logical relation; recorded as one obligation. -/
theorem quote_open_subst {cl : Closure} {v r : Val}
    {depth : Nat} {ve re bodye : Expr}
    (hopen : cl.openω v = some r)
    (hqv : quote fuelω depth v = some ve)
    (hqbody : quoteClosure fuelω depth cl = some bodye)
    (hqr : quote fuelω depth r = some re) :
    ∀ {S Γe}, Subtype' S Γe re (bodye.subst 0 ve) ∧
              Subtype' S Γe (bodye.subst 0 ve) re := by
  sorry

/-- Bridge to the Expr-level relation. Each `SubV` constructor
maps to a `Subtype'` constructor on the quoted forms.

`hS` says every seen-pair quotes into `Se`; `hΓ` says every
context entry quotes into `Γe` at the right de Bruijn index;
`ha`/`hb` quote the goal's endpoints. The induction is on
the `SubV` derivation; the closure-opening cases use
`quote_open_subst`. -/
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
  -- `SubV` is mutually inductive with `SubN`/`SynthN`, so
  -- `induction` rejects it (multiple motives). The full
  -- proof needs a *mutual* bridge — `SubV_to_Subtype'`,
  -- `SubN_to_Subtype'`, `SynthN_to_Subtype'_bvar` — using
  -- the joint recursor `SubV.rec`. For now, the three
  -- non-recursive constructors are dispatched by `cases`;
  -- the recursive ones need the mutual structure plus
  -- `quote_open_subst` and are sorried with the per-case
  -- plan documented.
  cases h with
  | hyp hin =>
      -- (a, b) ∈ S; hS gives a quoted pair in Se whose
      -- components are ae, be (by uniqueness of quote).
      obtain ⟨⟨pe1, pe2⟩, hpe, hq1, hq2⟩ := hS _ hin
      simp only at hq1 hq2
      rw [ha] at hq1; rw [hb] at hq2
      cases hq1; cases hq2
      exact .hyp hpe
  | refl =>
      rw [ha] at hb; cases hb
      exact .refl ae
  | top =>
      -- b = .type; quote .type = some .type at any depth.
      have : be = .type := by
        have hf : fuelω = fuelω.pred + 1 := rfl
        rw [hf] at hb; unfold quote at hb
        injection hb with hb; exact hb.symm
      exact this ▸ .top ae
  | lam hoA hoB hd hbody =>
      -- ae = .lam domAe bodyAe, be = .lam domBe bodyBe via
      -- quote-shape. IH on hd → `domBe ⊑ domAe`; IH on hbody
      -- (at Γ.push domB, depth+1) → `bodyAe ⊑ bodyBe` under
      -- `domBe :: Γe`. Subtype'.lam matches directly (after
      -- the A6 fix both push `domB`). The body
      -- correspondence needs `quote_open_subst` to relate
      -- `quote (cl.openω fresh)` to `quoteClosure cl` —
      -- but for fresh = .var Γ.size, opening with fresh and
      -- quoting at depth+1 *is* `quoteClosure` (by
      -- definition), so this case may close without the
      -- general lemma.
      sorry
  | iota_intro hoB hann hbody =>
      -- Subtype'.iota_intro needs `ae ⊑ anne` and
      -- `ae ⊑ bodye.subst 0 ae`. IH on hbody (at S') gives
      -- `ae ⊑ re` where re = quote(opened body);
      -- `quote_open_subst` bridges `re ↔ bodye.subst 0 ae`.
      sorry
  | unfold_fix_R hoB hbody => sorry
  | unfold_fix_L hoA hne hbody => sorry
  | unfold_iota_L hoA hne hbody => sorry
  | iota_struct hoA hoB hann hbody => sorry
  | fix_struct hoA hoB hann hbody => sorry
  | stuckRec_struct h1 h2 h3 h4 => sorry
  | neutral_struct hN =>
      -- `SubN_to_Subtype'`: the quoted neutral spines are
      -- `app_cong`-related with arg equivalence.
      sorry
  | neutral_ascent hsynth hsub =>
      -- `SynthN_to_Subtype'_bvar`: synthN.var → Subtype'.bvar
      -- at the right index; .app/.stuckRec → app_ascent.
      sorry
  | revapp_R hvapp hne hbody =>
      -- b' = vappω f arg (one forced unfold of the stuck
      -- recursive head). quote b' relates to quote b
      -- (= `.app (quote f) (quote arg)`) by exactly one
      -- `Subtype'.unfold_*` step (since vapp at unf>0
      -- unfolds the fix/iota once). Then `Subtype'.trans`
      -- with IH on hbody.
      sorry
  | revapp_L hvapp hne hbody => sorry

end NbE
