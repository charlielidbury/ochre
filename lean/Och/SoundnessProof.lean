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

/-!
### Logical relation for NbE correctness

The standard NbE soundness proof factors through a
*realisability* relation between semantic values and source
expressions. We use a step-indexed version (the `.lam`
clause quantifies over smaller indices, so the definition
terminates by recursion on the step count).
-/

/-- `Subtype'`-equivalence: both directions, in every
seen/context. This is the equational theory the bridge
targets. -/
def Equiv (e₁ e₂ : Expr) : Prop :=
  ∀ {S : Seen} {Γe : Ctx}, Subtype' S Γe e₁ e₂ ∧ Subtype' S Γe e₂ e₁

namespace Equiv
  theorem refl (e : Expr) : Equiv e e := fun {_ _} => ⟨.refl e, .refl e⟩
  theorem symm {e₁ e₂} (h : Equiv e₁ e₂) : Equiv e₂ e₁ :=
    fun {_ _} => ⟨h.2, h.1⟩
  theorem trans {e₁ e₂ e₃} (h₁ : Equiv e₁ e₂) (h₂ : Equiv e₂ e₃) :
      Equiv e₁ e₃ :=
    fun {_ _} => ⟨.trans h₁.1 h₂.1, .trans h₂.2 h₁.2⟩
end Equiv

/-- Step-indexed logical relation: `R n d v e` means "at step
index `n` and depth `d`, the value `v` realises the
expression `e`".

The base conjunct (`v` quotes to something `Equiv e`) is
what `R_quote_equiv` extracts. The constructor-specific
conjunct is what the fundamental lemma's `.app`/`.fix`/
`.iota` cases consume: a `.lam` is realised iff applying it
to any (smaller-index-)realised argument gives a realised
result; a `.fix`/`.iota` iff its one-step unfold is realised.

Downward closure (`R (n+1) → R n`) holds because the binder
clauses quantify over *all* `n' ≤ n`, not just `n` exactly;
this is the standard step-indexed setup (Appel-McAllester).
The whole definition recurses on the first argument. -/
def R : Nat → Nat → Val → Expr → Prop
  | 0, _, _, _ => True
  | n+1, d, v, e =>
      (∃ e', quote fuelω d v = some e' ∧ Equiv e' e) ∧
      (match v with
        | .lam _dV cl =>
            ∀ n', n' ≤ n → ∀ v' e', R n' d v' e' →
              ∀ r, cl.openω v' = some r →
                ∃ dom body, Equiv e (.lam dom body) ∧
                  R n' (d + 1) r (body.subst 0 e')
        | .iota _aV cl =>
            ∀ n', n' ≤ n →
              ∀ r, cl.openω (.iota _aV cl) = some r →
                r ≠ .iota _aV cl →
                ∃ ann body, Equiv e (.iota ann body) ∧
                  R n' d r (body.subst 0 e)
        | .«fix» _aV cl =>
            ∀ n', n' ≤ n →
              ∀ r, cl.openω (.«fix» _aV cl) = some r →
                r ≠ .«fix» _aV cl →
                ∃ ann body, Equiv e (.fix ann body) ∧
                  R n' d r (body.subst 0 (.fix ann body))
        | .type | .neutral _ => True)

/-- An environment `ρ` realises an expression-environment
`ρe` at index `n`, depth `d`. -/
def REnv (n d : Nat) (ρ : Env) (ρe : List Expr) : Prop :=
  ρ.length = ρe.length ∧
  ∀ k v, ρ[k]? = some v → ∃ e, ρe.get? k = some e ∧ R n d v e

/-- Downward closure: realisation at a larger step index
implies realisation at every smaller one. By induction on
`n`; the binder clauses are already `∀ n' ≤ n`-quantified so
restricting to `n' ≤ m ≤ n` is direct. -/
theorem R_mono {n m d v e} (hle : m ≤ n) (h : R n d v e) :
    R m d v e := by
  induction m generalizing n d v e with
  | zero => unfold R; trivial
  | succ k ih =>
    -- m = k+1 ≤ n, so n = n'+1 with k ≤ n'.
    match n, hle with
    | n'+1, hle =>
      have hk : k ≤ n' := Nat.le_of_succ_le_succ hle
      unfold R at h ⊢
      refine ⟨h.1, ?_⟩
      -- The constructor conjunct: each `∀ n'' ≤ k` instance
      -- discharges via h.2 at `n'' ≤ n'` (since k ≤ n').
      match v, h with
      | .lam _dV cl, ⟨_, hlam⟩ =>
          intro n'' hn'' v' e' hR r hopen
          exact hlam n'' (Nat.le_trans hn'' hk) v' e' hR r hopen
      | .iota _aV cl, ⟨_, hiota⟩ =>
          intro n'' hn'' r hopen hne
          exact hiota n'' (Nat.le_trans hn'' hk) r hopen hne
      | .«fix» _aV cl, ⟨_, hfix⟩ =>
          intro n'' hn'' r hopen hne
          exact hfix n'' (Nat.le_trans hn'' hk) r hopen hne
      | .type, _ => trivial
      | .neutral _, _ => trivial

theorem REnv_mono {n m d ρ ρe} (hle : m ≤ n) (h : REnv n d ρ ρe) :
    REnv m d ρ ρe := by
  refine ⟨h.1, ?_⟩
  intro k v hk
  obtain ⟨e, he, hR⟩ := h.2 k v hk
  exact ⟨e, he, R_mono hle hR⟩

/-- **Fundamental lemma** (NbE soundness, eval direction).
Evaluating `body` under a realised environment, at *any*
`unf` budget, gives a value realising `body.substEnv ρe`.
The `unf`-independence is the whole point: `vapp`'s
`.fix`/`.iota` arms either unfold (using one `unf`) or
return `.stuckRec`; both realise the same source expression
(the unfolded body via the `.fix`/`.iota` clause of `R`; the
stuckRec via the `.neutral` clause + `quote .stuckRec =
.app (quote f) (quote a)` which is `Equiv` to the unfolded
form by `Subtype'.unfold_*`).

Proof: induction on the step index `m`, with inner
case-split on `body`. The `.app` case uses the `.lam`/
`.fix`/`.iota` clauses of `R` on the head's IH (at index
`m`) instantiated with the argument's IH (at index `m' ≤ m`
via `R_mono`). The `.lam`/`.iota`/`.fix` cases of `body`
build the constructor clause directly (the closure body is
the original `body` Expr, so `cl.openω v'` re-evaluates it
under the extended env — apply IH at the smaller index). -/
theorem eval_realises {fuel unf : Nat} {ρ : Env} {body : Expr} {v : Val}
    (heval : eval fuel unf ρ body = some v)
    {m d : Nat} {ρe : List Expr}
    (henv : REnv m d ρ ρe) :
    R m d v (body.substEnv ρe) := by
  sorry

/-- The base conjunct of `R` at any nonzero index. -/
theorem R_quote_equiv {n d v e}
    (hn : 0 < n) (h : R n d v e)
    {e' : Expr} (hq : quote fuelω d v = some e') :
    Equiv e' e := by
  cases n with
  | zero => omega
  | succ m =>
      unfold R at h
      obtain ⟨⟨e'', hq'', heqv⟩, _⟩ := h
      rw [hq] at hq''; cases hq''; exact heqv

/-- A fresh neutral at level `lvl < d` quotes to `bvar
(d-1-lvl)`. Forward direction; the inversion is
`quoteNeutral_var` below. -/
private theorem quote_neutral_var_fwd {d lvl : Nat} (hlt : lvl < d) :
    quote fuelω d (.neutral (.var lvl)) = some (.bvar (d - 1 - lvl)) := by
  -- fuelω = 100000 = 99999 + 1; fuelω - 1 = 99999 = 99998 + 1
  show quote (99999 + 1) d (.neutral (.var lvl)) = _
  unfold quote
  show quoteNeutral (99998 + 1) d (.var lvl) = _
  unfold quoteNeutral
  simp [hlt]

theorem R_zero {d v e} : R 0 d v e := by unfold R; trivial

/-- A fresh neutral variable realises the corresponding
de-Bruijn-indexed bvar at every step index. -/
theorem R_neutral_var {m d lvl : Nat} (hlt : lvl < d) :
    R m d (.neutral (.var lvl)) (.bvar (d - 1 - lvl)) := by
  cases m with
  | zero => exact R_zero
  | succ m' =>
      unfold R
      exact ⟨⟨.bvar (d - 1 - lvl), quote_neutral_var_fwd hlt,
              Equiv.refl _⟩, trivial⟩

/-- The identity environment realises itself: each `ρ[k]` is
`.neutral (.var (d-1-k))` which quotes to `.bvar k`, and
`ρe[k] = .bvar k`. -/
theorem REnv_id (m d : Nat) :
    REnv m d
      ((List.range d).reverse.map (fun lvl => Val.neutral (.var lvl)))
      ((List.range d).map .bvar) := by
  constructor
  · simp only [List.length_map, List.length_reverse, List.length_range]
  · intro k v hk
    simp only [List.get?_eq_getElem?] at *
    rw [List.getElem?_map] at hk
    -- k < d, so reverse[k]? = some (d-1-k).
    rcases Nat.lt_or_ge k d with hkd | hkd
    · have hrev : (List.range d).reverse[k]? = some (d - 1 - k) := by
        rw [List.getElem?_reverse
              (by simp only [List.length_range]; exact hkd),
            List.length_range,
            List.getElem?_range (by omega)]
      rw [hrev] at hk
      simp only [Option.map_some', Option.some.injEq] at hk
      refine ⟨.bvar k, ?_, ?_⟩
      · simp only [List.get?_eq_getElem?, List.getElem?_map,
                   List.getElem?_range hkd, Option.map_some']
      · subst hk
        have hdk : d - 1 - k < d := Nat.lt_of_le_of_lt (Nat.sub_le _ _)
          (Nat.sub_lt (Nat.lt_of_le_of_lt (Nat.zero_le k) hkd) Nat.one_pos)
        have hr := R_neutral_var (m := m) (d := d) (lvl := d - 1 - k) hdk
        have heq : d - 1 - (d - 1 - k) = k := by omega
        simp only [heq] at hr
        exact hr
    · -- k ≥ d: ρ[k]? = none, contradiction.
      exfalso
      have : (List.range d).reverse[k]? = none := by
        apply List.getElem?_eq_none
        simp only [List.length_reverse, List.length_range]; omega
      rw [this] at hk; simp at hk

/-- **Unf-irrelevance modulo `Subtype'`**: evaluating the
same expression at the same fuel/env but different `unf`
budgets gives values whose quotes are `Subtype'`-equivalent.

Now derived from the fundamental lemma: both evaluations
realise the *same* source expression `e.substEnv ρe`
(`eval_realises` is `unf`-independent), so both quotes are
`Equiv` to it (`R_quote_equiv`), hence `Equiv` to each other
(`Equiv.trans` ∘ `Equiv.symm`). The remaining obligation is
`eval_realises` itself.

The `hρe` hypothesis says the evaluation environment is
realisable at the given depth (each `ρ[k]` quotes). The
bridge always supplies such an environment (built from
fresh neutrals via the `hΓ` correspondence). -/
theorem eval_unf_equiv {n unf₁ unf₂ ρ e v₁ v₂ depth e₁ e₂}
    (hn : n ≤ fuelω)
    {ρe : List Expr} (hρe : REnv 1 depth ρ ρe)
    (h₁ : eval n unf₁ ρ e = some v₁)
    (h₂ : eval n unf₂ ρ e = some v₂)
    (hq₁ : quote n depth v₁ = some e₁)
    (hq₂ : quote n depth v₂ = some e₂) :
    ∀ {S Γe}, Subtype' S Γe e₁ e₂ ∧ Subtype' S Γe e₂ e₁ := by
  have hq₁' := quote_fuel_mono hn hq₁
  have hq₂' := quote_fuel_mono hn hq₂
  -- Both evaluations realise `e.substEnv ρe` at step index 1
  -- (the fundamental lemma is `unf`-agnostic).
  have r₁ := eval_realises h₁ (m := 1) (d := depth) hρe
  have r₂ := eval_realises h₂ (m := 1) (d := depth) hρe
  -- Both quotes are `Equiv` to that common target.
  have eq₁ : Equiv e₁ (e.substEnv ρe) := R_quote_equiv Nat.one_pos r₁ hq₁'
  have eq₂ : Equiv e₂ (e.substEnv ρe) := R_quote_equiv Nat.one_pos r₂ hq₂'
  -- Compose: e₁ ≡ target ≡ e₂.
  intro S Γe
  exact ⟨.trans (eq₁.1) (eq₂.2), .trans (eq₂.1) (eq₁.2)⟩

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

/-!
### Quote shape lemmas

Inversion lemmas for `quote`/`quoteNeutral` on each Val/Neutral
constructor. These let the bridge proof extract the quoted
sub-components when matching on a `SubV`/`SubN` constructor.
-/

private theorem fuelω_succ : fuelω = (fuelω - 1) + 1 := rfl

theorem quote_type {d : Nat} : quote fuelω d .type = some .type := by
  rw [fuelω_succ, quote.eq_2]

theorem quote_neutral {d : Nat} {n : Neutral} {e : Expr}
    (h : quote fuelω d (.neutral n) = some e) :
    quoteNeutral (fuelω - 1) d n = some e := by
  rw [fuelω_succ, quote.eq_3] at h; exact h

theorem quoteNeutral_var {d k : Nat} {e : Expr}
    (h : quoteNeutral fuelω d (.var k) = some e) :
    k < d ∧ e = .bvar (d - 1 - k) := by
  rw [fuelω_succ, quoteNeutral.eq_2] at h
  split at h
  · next hlt => exact ⟨hlt, (Option.some.injEq .. ▸ h).symm⟩
  · exact absurd h (by simp)

theorem quoteNeutral_app {d : Nat} {n : Neutral} {v : Val} {e : Expr}
    (h : quoteNeutral fuelω d (.app n v) = some e) :
    ∃ ne ve, quoteNeutral (fuelω - 1) d n = some ne ∧
             quote (fuelω - 1) d v = some ve ∧
             e = .app ne ve := by
  rw [fuelω_succ, quoteNeutral.eq_3] at h
  simp only [Option.bind_eq_bind, Option.bind_eq_some,
             Option.some.injEq] at h
  obtain ⟨ne, hne, ve, hve, heq⟩ := h
  exact ⟨ne, ve, hne, hve, heq.symm⟩

theorem quoteNeutral_stuckRec {d : Nat} {f a : Val} {e : Expr}
    (h : quoteNeutral fuelω d (.stuckRec f a) = some e) :
    ∃ fe ae, quote (fuelω - 1) d f = some fe ∧
             quote (fuelω - 1) d a = some ae ∧
             e = .app fe ae := by
  rw [fuelω_succ, quoteNeutral.eq_4] at h
  simp only [Option.bind_eq_bind, Option.bind_eq_some,
             Option.some.injEq] at h
  obtain ⟨fe, hfe, ae, hae, heq⟩ := h
  exact ⟨fe, ae, hfe, hae, heq.symm⟩

/-- Lift `quoteNeutral` from `fuelω - 1` to `fuelω`. -/
theorem quoteNeutralω {d : Nat} {n : Neutral} {e : Expr}
    (h : quoteNeutral (fuelω - 1) d n = some e) :
    quoteNeutral fuelω d n = some e :=
  quoteNeutral_fuel_mono (Nat.sub_le _ _) h

/-- Lift `quote` from `fuelω - 1` to `fuelω`. -/
theorem quoteω {d : Nat} {v : Val} {e : Expr}
    (h : quote (fuelω - 1) d v = some e) :
    quote fuelω d v = some e :=
  quote_fuel_mono (Nat.sub_le _ _) h

/-!
### Hypothesis bundles
-/

/-- The seen-set quotes into `Se`. -/
abbrev QuotesSeen (S : List (Val × Val)) (Γ : TyCtx) (Se : Seen) : Prop :=
  ∀ p ∈ S, ∃ pe ∈ Se,
    quote fuelω Γ.size p.1 = some pe.1 ∧
    quote fuelω Γ.size p.2 = some pe.2

/-- The type context quotes into `Γe` at matching de Bruijn
indices. `Γ` is level-indexed (`Γ[k]` = type of `.var k`);
`Γe` is index-indexed (`Γe[i]` = type of `.bvar i`). -/
abbrev QuotesCtx (Γ : TyCtx) (Γe : Ctx) : Prop :=
  ∀ k τ, Γ[k]? = some τ →
    ∃ τe, Γe.get? (Γ.size - 1 - k) = some τe ∧
          quote fuelω (k + 1) τ = some τe

/-!
### The mutual bridge

Three theorems proven by simultaneous structural recursion
on `SubV`/`SubN`/`SynthN`, using the joint recursor
`SubV.rec`. Each motive packages the quote hypotheses; the
recursor supplies one IH per recursive premise.
-/

/-- `SubN`'s bridge: quoted neutral spines are
`Subtype'`-related via `.refl` (var) or `.app_cong` (app /
stuckRec, with arg equivalence). -/
theorem SubN_to_Subtype'
    {S Γ nA nB} (h : SubN S Γ nA nB)
    {Se Γe ae be}
    (hS : QuotesSeen S Γ Se) (hΓ : QuotesCtx Γ Γe)
    (ha : quoteNeutral fuelω Γ.size nA = some ae)
    (hb : quoteNeutral fuelω Γ.size nB = some be) :
    Subtype' Se Γe ae be := by
  -- The motives for the joint recursor.
  let MV := fun S Γ a b (_ : SubV S Γ a b) =>
    ∀ {Se Γe ae be}, QuotesSeen S Γ Se → QuotesCtx Γ Γe →
      quote fuelω Γ.size a = some ae →
      quote fuelω Γ.size b = some be →
      Subtype' Se Γe ae be
  let MN := fun S Γ nA nB (_ : SubN S Γ nA nB) =>
    ∀ {Se Γe ae be}, QuotesSeen S Γ Se → QuotesCtx Γ Γe →
      quoteNeutral fuelω Γ.size nA = some ae →
      quoteNeutral fuelω Γ.size nB = some be →
      Subtype' Se Γe ae be
  let MS := fun Γ n τ (_ : SynthN Γ n τ) =>
    ∀ {Se Γe ne τe}, QuotesCtx Γ Γe →
      quoteNeutral fuelω Γ.size n = some ne →
      quote fuelω Γ.size τ = some τe →
      Subtype' Se Γe ne τe
  refine (@SubN.rec MV MN MS
    -- ===== SubV cases =====
    -- hyp
    (fun {S Γ a b} hin {Se Γe ae be} hS _hΓ ha hb => by
      obtain ⟨⟨pe1, pe2⟩, hpe, hq1, hq2⟩ := hS _ hin
      simp only at hq1 hq2
      rw [ha] at hq1; rw [hb] at hq2
      cases hq1; cases hq2; exact .hyp hpe)
    -- refl
    (fun {S Γ a} {Se Γe ae be} _hS _hΓ ha hb => by
      rw [ha] at hb; cases hb; exact .refl ae)
    -- top
    (fun {S Γ a} {Se Γe ae be} _hS _hΓ _ha hb => by
      rw [quote_type] at hb; cases hb; exact .top ae)
    -- lam — needs eval_unf_equiv for the unf=1↔4 mismatch.
    -- IHs `ihD` (dom) and `ihB` (body at Γ.push domB) are
    -- now available; once `quoteClosure_eq_quote_openω_fresh`
    -- becomes unconditional this case closes via
    -- `Subtype'.lam (ihD …) (ihB …)`.
    (fun _ _ _ _ _ihD _ihB {_ _ _ _} _ _ _ _ => by sorry)
    -- iota_struct — same shape as lam (open with fresh).
    (fun _ _ _ _ _ihA _ihB {_ _ _ _} _ _ _ _ => by sorry)
    -- fix_struct
    (fun _ _ _ _ _ihA _ihB {_ _ _ _} _ _ _ _ => by sorry)
    -- stuckRec_struct — IHs ih1..ih4 give bidirectional
    -- equivalence on heads/args; quoted as `.app fe ae` on
    -- both sides → `.app_cong`. Needs `quote_open_subst` for
    -- the head if f is a closure-bearing Val (it isn't —
    -- stuckRec heads are .fix/.iota, quoted via quoteClosure
    -- which hits the unf mismatch).
    (fun _ _ _ _ _ih1 _ih2 _ih3 _ih4 {_ _ _ _} _ _ _ _ => by sorry)
    -- iota_intro — needs quote_open_subst.
    (fun _ _ _ _ihA _ihB {_ _ _ _} _ _ _ _ => by sorry)
    -- unfold_fix_R — needs quote_open_subst.
    (fun _ _ _ihB {_ _ _ _} _ _ _ _ => by sorry)
    -- unfold_fix_L — needs quote_open_subst.
    (fun _ _ _ _ihB {_ _ _ _} _ _ _ _ => by sorry)
    -- unfold_iota_L
    (fun _ _ _ _ihB {_ _ _ _} _ _ _ _ => by sorry)
    -- neutral_struct: hand off to MN's IH directly.
    (fun {S Γ nA nB} _hN ihN {Se Γe ae be} hS hΓ ha hb => by
      exact ihN hS hΓ (quoteNeutralω (quote_neutral ha))
                      (quoteNeutralω (quote_neutral hb)))
    -- neutral_ascent: SynthN gives `ne ⊑ τe` (via MS's IH);
    -- SubV gives `τe ⊑ be` (via MV's IH); compose by `.trans`.
    (fun {S Γ nA τ b} _hsynth _hsub ihS ihV
         {Se Γe ae be} hS hΓ ha hb => by
      -- Quote τ at depth Γ.size; if it fails the chain
      -- can't proceed — but synthN guarantees τ is a Val
      -- in scope, and quote at fuelω is total on
      -- well-scoped Vals. We don't have that totality
      -- lemma yet, so case on the option.
      rcases hτ : quote fuelω Γ.size τ with _ | τe
      · -- quote τ = none. The MS IH still requires a τe;
        -- without quote-totality this branch is stuck.
        sorry
      · exact .trans
          (ihS hΓ (quoteNeutralω (quote_neutral ha)) hτ)
          (ihV hS hΓ hτ hb))
    -- revapp_R — needs eval_unf_equiv (vappω is one forced
    -- unfold; quoted b' relates to quoted b by one
    -- `unfold_*` step).
    (fun _ _ _ _ihB {_ _ _ _} _ _ _ _ => by sorry)
    -- revapp_L
    (fun _ _ _ _ihB {_ _ _ _} _ _ _ _ => by sorry)
    -- ===== SubN cases =====
    -- var: both quote to `.bvar (d-1-k)`; refl.
    (fun {S Γ k} {Se Γe ae be} _hS _hΓ ha hb => by
      obtain ⟨_, heqA⟩ := quoteNeutral_var ha
      obtain ⟨_, heqB⟩ := quoteNeutral_var hb
      subst heqA heqB; exact .refl _)
    -- app: IH on heads (MN) + IHs on args both ways (MV)
    -- → `.app_cong`.
    (fun {S Γ n1 n2 v1 v2} _hn _hv1 _hv2 ihN ihV1 ihV2
         {Se Γe ae be} hS hΓ ha hb => by
      obtain ⟨n1e, v1e, hn1, hv1, heqA⟩ := quoteNeutral_app ha
      obtain ⟨n2e, v2e, hn2, hv2, heqB⟩ := quoteNeutral_app hb
      subst heqA heqB
      exact .app_cong
        (ihN hS hΓ (quoteNeutralω hn1) (quoteNeutralω hn2))
        (ihV1 hS hΓ (quoteω hv1) (quoteω hv2))
        (ihV2 hS hΓ (quoteω hv2) (quoteω hv1)))
    -- stuckRec: both quote to `.app fe ae`. IHs on f, a
    -- (both directions, MV) → `.app_cong` with the head
    -- itself by `.app_cong` again (since `quote (.fix..)`
    -- is an Expr, comparing two of them via the V-IH).
    (fun {S Γ fA aA fB aB} _h1 _h2 _h3 _h4 ih1 _ih2 ih3 ih4
         {Se Γe ae be} hS hΓ ha hb => by
      obtain ⟨fAe, aAe, hfA, haA, heqA⟩ := quoteNeutral_stuckRec ha
      obtain ⟨fBe, aBe, hfB, haB, heqB⟩ := quoteNeutral_stuckRec hb
      subst heqA heqB
      -- `.stuckRec f a` quotes to `.app fe ae` (one app
      -- node). So `.app fAe aAe ⊑ .app fBe aBe` via one
      -- `app_cong`: head `fAe ⊑ fBe` (ih1) + arg equiv
      -- `aAe ⊑ aBe ∧ aBe ⊑ aAe` (ih3, ih4).
      exact .app_cong
        (ih1 hS hΓ (quoteω hfA) (quoteω hfB))
        (ih3 hS hΓ (quoteω haA) (quoteω haB))
        (ih4 hS hΓ (quoteω haB) (quoteω haA)))
    -- ===== SynthN cases =====
    -- var: Γ[k] = τ. quoteNeutral .var k = .bvar (d-1-k).
    -- hΓ gives Γe[d-1-k] = τe with quote τ at depth k+1.
    -- Need Subtype' .. (.bvar (d-1-k)) τe. By `.bvar` rule
    -- with shift… but `Subtype'.bvar` gives `bvar i ⊑
    -- (Γe[i]).shift (i+1) 0`, and we want `bvar i ⊑ τe`
    -- where τe was quoted at depth k+1 ≠ d. Depth mismatch:
    -- `hΓ` quotes τ at depth `k+1` but the goal needs it at
    -- depth `d = Γ.size`. This is the level↔index
    -- bookkeeping; needs a quote-shift lemma.
    (fun {Γ k τ} _hk {Se Γe ne τe} _hΓ _hn _hτ => by sorry)
    -- app: IH gives ne' ⊑ (.lam dome cle)e; need
    -- `.app ne' ve ⊑ τe` where τe = quote(cl.openω v).
    -- `app_ascent` + `quote_open_subst`.
    (fun _ _ _ihS {_ _ _ _} _ _ _ => by sorry)
    -- stuckRecFix / stuckRecIota / *Ann: same shape as app.
    (fun _ _ {_ _ _ _} _ _ _ => by sorry)
    (fun _ _ {_ _ _ _} _ _ _ => by sorry)
    (fun _ {_ _ _ _} _ _ _ => by sorry)
    (fun _ {_ _ _ _} _ _ _ => by sorry)
    S Γ nA nB h) hS hΓ ha hb

/-- `SynthN`'s bridge: a neutral inhabits its synthesised
type. Same recursor application; this entry just projects
the `MS` motive. -/
theorem SynthN_to_Subtype'
    {Γ n τ} (h : SynthN Γ n τ)
    {Se Γe ne τe}
    (hΓ : QuotesCtx Γ Γe)
    (hn : quoteNeutral fuelω Γ.size n = some ne)
    (hτ : quote fuelω Γ.size τ = some τe) :
    Subtype' Se Γe ne τe := by
  -- Reuse the SubN bridge's recursor application by going
  -- through a trivial SubN derivation isn't possible; just
  -- call the recursor directly here too. For now, sorried —
  -- it's the same 24 cases as above with the MS motive
  -- projected. Once `SubN_to_Subtype'` is fully closed, this
  -- becomes a copy with `@SynthN.rec` instead of `@SubN.rec`.
  sorry

/-- Bridge to the Expr-level relation. Each `SubV` constructor
maps to a `Subtype'` constructor on the quoted forms.

`hS` says every seen-pair quotes into `Se`; `hΓ` says every
context entry quotes into `Γe` at the right de Bruijn index;
`ha`/`hb` quote the goal's endpoints. -/
theorem SubV_to_Subtype'
    {S Γ a b} (h : SubV S Γ a b)
    {Se : List (Expr × Expr)} {Γe : Ctx} {ae be : Expr}
    (hS : QuotesSeen S Γ Se)
    (hΓ : QuotesCtx Γ Γe)
    (ha : quote fuelω Γ.size a = some ae)
    (hb : quote fuelω Γ.size b = some be) :
    Subtype' Se Γe ae be := by
  -- Same recursor application as `SubN_to_Subtype'`, but
  -- projecting the `MV` motive at the end (`@SubV.rec`
  -- instead of `@SubN.rec`). The 24 case-handlers are
  -- identical; rather than duplicate ~150 lines, this
  -- delegates to a single shared application once the
  -- closure-opening cases close. Until then, sorried with
  -- the per-case status mirroring `SubN_to_Subtype'`:
  --   PROVEN: hyp, refl, top, neutral_struct (full), SubN.var,
  --           SubN.app, SubN.stuckRec, neutral_ascent (mod
  --           quote-totality)
  --   GATED on eval_unf_equiv: lam, iota_struct, fix_struct,
  --           stuckRec_struct, iota_intro, unfold_fix_R/L,
  --           unfold_iota_L, revapp_R/L, SynthN.app/stuckRec*
  --   GATED on quote-shift: SynthN.var
  sorry

end NbE
