import Och.NbE
import Och.SubCheckVal
import Och.Subtyping
import Och.TyCheck

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
        -- Push `domA`, matching the algorithm (SubCheckVal.lean
        -- lam-lam arm). `Subtype'.lam` pushes `domB`; the
        -- `SubV → Subtype'` bridge will need `Subtype'.narrow`
        -- here. A6 / DECISION-LOG: `domB` is more complete but
        -- causes seen-list misses on dNat-style nested fixes.
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

  theorem lam {dom₁ dom₂ body₁ body₂ : Expr}
      (hd : Equiv dom₁ dom₂) (hb : Equiv body₁ body₂) :
      Equiv (.lam dom₁ body₁) (.lam dom₂ body₂) := by
    intro S Γe
    exact ⟨.lam hd.2 hb.1, .lam hd.1 hb.2⟩

  /-- `Equiv` is a congruence under `.app` (both arguments
  must be equivalent — A1). -/
  theorem app {f₁ f₂ a₁ a₂ : Expr}
      (hf : Equiv f₁ f₂) (ha : Equiv a₁ a₂) :
      Equiv (.app f₁ a₁) (.app f₂ a₂) := by
    intro S Γe
    exact ⟨.app_cong hf.1 ha.1 ha.2, .app_cong hf.2 ha.2 ha.1⟩

  -- `Equiv.shift` (non-closedness form) deleted 2026-04-21.
  -- The nil-Γ case was unprovable without tracking closedness.
  -- Former callers (Equiv.subst_resp; R_depth_lift base case)
  -- are both now sorried inline or deleted. Use
  -- `Equiv.shift_of_closed` below when closedness is available.

  /-- A closedness-carrying form of `Equiv.shift`: if both
  endpoints are closed at 0, then the shifted pair is
  equivalent trivially (shift is the identity on closed
  expressions). This is the ENABLING lemma for closing the
  nil-Γ sorry in `Equiv.shift` above — any caller that can
  supply closedness of `e₁, e₂` avoids the sorry entirely.

  In `Equiv.subst_resp`'s uses, the substituends `a, b` come
  from `concEval` results (closed terms). Threading their
  closedness through `subst_resp`'s recursion is the pragmatic
  path. -/
  theorem shift_of_closed {e₁ e₂ : Expr}
      (h₁ : e₁.closedAt 0 = true) (h₂ : e₂.closedAt 0 = true)
      (h : Equiv e₁ e₂) :
      Equiv (e₁.shift 1 0) (e₂.shift 1 0) := by
    rw [Expr.shift_of_closedAt h₁ 1 (Nat.le_refl _),
        Expr.shift_of_closedAt h₂ 1 (Nat.le_refl _)]
    exact h

  /-- A closedness-carrying `subst_resp`: when substituends are
  closed at 0, the shift under binders is the identity and the
  proof avoids `Equiv.shift` (still sorried at nil-Γ) entirely.

  In practice, this is ALL the uses. `concEval_equiv`
  substituends come from `concEval` results (closed by
  construction). So this closedness-carrying form is the
  usable version; the general `subst_resp` below remains for
  full generality but depends on the nil-Γ sorry.

  The critical insight: `body.subst (i+1) (a.shift 1 0) =
  body.subst (i+1) a` when `a.closedAt 0`. So the recursive
  body call doesn't need the shifted substituend's Equiv — it
  uses the original `heq` directly, avoiding `Equiv.shift`. -/
  theorem subst_resp_closed :
      ∀ (e : Expr) {a b : Expr},
      a.closedAt 0 = true → b.closedAt 0 = true →
      Equiv a b → ∀ (i : Nat),
      Equiv (e.subst i a) (e.subst i b) := by
    intro e
    induction e with
    | bvar k =>
      intro a b _ha _hb heq i
      simp only [Expr.subst]
      split
      · exact heq
      · split <;> exact Equiv.refl _
    | type =>
      intro _ _ _ _ _ _
      simp only [Expr.subst]; exact Equiv.refl _
    | lam dom body ihD ihB =>
      intro a b ha hb heq i
      simp only [Expr.subst]
      -- Key trick: since a, b closedAt 0, their shift is identity.
      rw [Expr.shift_of_closedAt ha 1 (Nat.zero_le _),
          Expr.shift_of_closedAt hb 1 (Nat.zero_le _)]
      exact Equiv.lam (ihD ha hb heq i) (ihB ha hb heq (i+1))
    | app f x ihF ihX =>
      intro a b ha hb heq i
      simp only [Expr.subst]
      exact Equiv.app (ihF ha hb heq i) (ihX ha hb heq i)
    | asc t ty ihT _ =>
      intro a b ha hb heq i
      simp only [Expr.subst]
      exact fun {S Γ} =>
        ⟨.asc_L (.asc_R (ihT ha hb heq i).1),
         .asc_L (.asc_R (ihT ha hb heq i).2)⟩
    | iota ann body ihA ihB =>
      intro a b ha hb heq i
      simp only [Expr.subst]
      rw [Expr.shift_of_closedAt ha 1 (Nat.zero_le _),
          Expr.shift_of_closedAt hb 1 (Nat.zero_le _)]
      intro S Γ
      exact ⟨.iota_cong (ihA ha hb heq i).1 (ihB ha hb heq (i+1)).1,
             .iota_cong (ihA ha hb heq i).2 (ihB ha hb heq (i+1)).2⟩
    | «fix» ann body ihA ihB =>
      intro a b ha hb heq i
      simp only [Expr.subst]
      rw [Expr.shift_of_closedAt ha 1 (Nat.zero_le _),
          Expr.shift_of_closedAt hb 1 (Nat.zero_le _)]
      intro S Γ
      exact ⟨.fix_cong (ihA ha hb heq i).1 (ihB ha hb heq (i+1)).1,
             .fix_cong (ihA ha hb heq i).2 (ihB ha hb heq (i+1)).2⟩
    | letE val body ihV ihB =>
      intro a b ha hb heq i
      simp only [Expr.subst]
      rw [Expr.shift_of_closedAt ha 1 (Nat.zero_le _),
          Expr.shift_of_closedAt hb 1 (Nat.zero_le _)]
      intro S Γ
      exact ⟨.letE_cong (ihV ha hb heq i).1 (ihB ha hb heq (i+1)).1,
             .letE_cong (ihV ha hb heq i).2 (ihB ha hb heq (i+1)).2⟩

-- `Equiv.subst_resp` (non-closedness form) deleted 2026-04-21.
-- Its only callers were in vapp_realises; those call sites are
-- now sorried inline. Use `Equiv.subst_resp_closed` above for
-- the closedness-carrying version.
end Equiv

/-! ### Depth-parametrised Equiv (`Equiv_c`)

`Equiv_c d e₁ e₂` says `e₁ ⊑ e₂` and `e₂ ⊑ e₁` at every
context `Γ` of length **at least** `d`. This is strictly
weaker than `Equiv` (which requires `|Γ| ≥ 0` = all `Γ`,
including `[]`).

**Why it exists:** `Equiv.shift` at `Γ = []` is unprovable
without closedness of both endpoints (the structural blocker
documented in DECISION-LOG 2026-04-21). But at `Γ ≠ []`, the
shift follows from `Subtype'.ctx_extend`, which is already
proven. `Equiv_c d` excludes `Γ = []` for `d ≥ 1`, restoring
provability of shift without any closedness side condition.

`Equiv_c 0` coincides with `Equiv` (both quantify over all
`Γ`), so at the top-level soundness chain (`Γe = []`, closed
terms) no information is lost. For internal uses (R's closure
clauses at depth `d ≥ 1`), `Equiv_c d` is enough because
all downstream consumers use it at a `Γe` of length `d`. -/
@[reducible]
def Equiv_c (d : Nat) (e₁ e₂ : Expr) : Prop :=
  ∀ {S : Seen} {Γe : Ctx}, d ≤ Γe.length →
    Subtype' S Γe e₁ e₂ ∧ Subtype' S Γe e₂ e₁

namespace Equiv_c
  theorem refl (d : Nat) (e : Expr) : Equiv_c d e e :=
    fun {_ _} _ => ⟨.refl e, .refl e⟩

  theorem symm {d e₁ e₂} (h : Equiv_c d e₁ e₂) : Equiv_c d e₂ e₁ :=
    fun {_ _} hd => ⟨(h hd).2, (h hd).1⟩

  theorem trans {d e₁ e₂ e₃}
      (h₁ : Equiv_c d e₁ e₂) (h₂ : Equiv_c d e₂ e₃) :
      Equiv_c d e₁ e₃ :=
    fun {_ _} hd => ⟨.trans (h₁ hd).1 (h₂ hd).1,
                     .trans (h₂ hd).2 (h₁ hd).2⟩

  /-- `Equiv` coerces to `Equiv_c d` for any `d`. Since `Equiv`
  quantifies over all `Γ` and `Equiv_c d` only over those with
  `|Γ| ≥ d`, the coercion is immediate. -/
  theorem of_Equiv {d e₁ e₂} (h : Equiv e₁ e₂) : Equiv_c d e₁ e₂ :=
    fun {_ _} _ => h

  /-- `Equiv_c` is monotone in `d`: a smaller `d` yields a stronger
  statement (quantifies over more `Γ`), so `Equiv_c d → Equiv_c d'`
  for `d ≤ d'`. -/
  theorem mono {d d' e₁ e₂} (hle : d ≤ d')
      (h : Equiv_c d e₁ e₂) : Equiv_c d' e₁ e₂ :=
    fun {_ _} hd' => h (Nat.le_trans hle hd')

  /-- `.lam` congruence: contravariant domain, covariant body under
  depth-lifted environment. -/
  theorem lam_cong {d domA domB bodyA bodyB}
      (hd : Equiv_c d domA domB) (hb : Equiv_c (d+1) bodyA bodyB) :
      Equiv_c d (.lam domA bodyA) (.lam domB bodyB) := by
    intro S Γ hd_le
    have hd_le1 : d+1 ≤ (domB :: Γ).length := by
      simp only [List.length_cons]; omega
    have hd_le1' : d+1 ≤ (domA :: Γ).length := by
      simp only [List.length_cons]; omega
    obtain ⟨hd12, hd21⟩ := hd hd_le
    obtain ⟨hb12, _⟩ := hb hd_le1
    obtain ⟨_, hb21'⟩ := hb hd_le1'
    exact ⟨.lam hd21 hb12, .lam hd12 hb21'⟩

  /-- `.iota` congruence: covariant annotation, covariant body. -/
  theorem iota_cong {d ann₁ ann₂ body₁ body₂}
      (ha : Equiv_c d ann₁ ann₂)
      (hb : Equiv_c (d+1) body₁ body₂) :
      Equiv_c d (.iota ann₁ body₁) (.iota ann₂ body₂) := by
    intro S Γ hd_le
    have hd_le1 : d+1 ≤ (ann₂ :: Γ).length := by
      simp only [List.length_cons]; omega
    have hd_le1' : d+1 ≤ (ann₁ :: Γ).length := by
      simp only [List.length_cons]; omega
    obtain ⟨ha12, ha21⟩ := ha hd_le
    obtain ⟨hb12, _⟩ := hb hd_le1
    obtain ⟨_, hb21'⟩ := hb hd_le1'
    exact ⟨.iota_cong ha12 hb12, .iota_cong ha21 hb21'⟩

  /-- `.fix` congruence: covariant annotation, covariant body. -/
  theorem fix_cong {d ann₁ ann₂ body₁ body₂}
      (ha : Equiv_c d ann₁ ann₂)
      (hb : Equiv_c (d+1) body₁ body₂) :
      Equiv_c d (.fix ann₁ body₁) (.fix ann₂ body₂) := by
    intro S Γ hd_le
    have hd_le1 : d+1 ≤ (ann₂ :: Γ).length := by
      simp only [List.length_cons]; omega
    have hd_le1' : d+1 ≤ (ann₁ :: Γ).length := by
      simp only [List.length_cons]; omega
    obtain ⟨ha12, ha21⟩ := ha hd_le
    obtain ⟨hb12, _⟩ := hb hd_le1
    obtain ⟨_, hb21'⟩ := hb hd_le1'
    exact ⟨.fix_cong ha12 hb12, .fix_cong ha21 hb21'⟩

  /-- `.app` congruence. -/
  theorem app_cong {d f₁ f₂ a₁ a₂}
      (hf : Equiv_c d f₁ f₂) (ha : Equiv_c d a₁ a₂) :
      Equiv_c d (.app f₁ a₁) (.app f₂ a₂) := by
    intro S Γ hd_le
    obtain ⟨hf12, hf21⟩ := hf hd_le
    obtain ⟨ha12, ha21⟩ := ha hd_le
    exact ⟨.app_cong hf12 ha12 ha21, .app_cong hf21 ha21 ha12⟩

  /-- At `d = 0`, `Equiv_c 0` coincides with `Equiv`. -/
  theorem to_Equiv_zero {e₁ e₂} (h : Equiv_c 0 e₁ e₂) : Equiv e₁ e₂ :=
    fun {_ _} => h (Nat.zero_le _)

  /-- **Key shift lemma** — the whole point of `Equiv_c`. At
  output depth `d+1`, the shifted equivalence holds at every
  `Γ` of length `≥ d+1` (which excludes `Γ = []` for `d ≥ 0`).

  Proof: for `Γ` with `|Γ| ≥ d+1 ≥ 1`, decompose `Γ = head :: tail`
  with `|tail| ≥ d`. Apply the input `Equiv_c d` at `tail` to
  get `Subtype' S tail e₁ e₂`, then lift via `Subtype'.ctx_extend`
  with `Δ = [head]` to get the shifted pair at `[head] ++ tail = Γ`.

  No closedness side condition — the shift is paid for by
  restricting the output quantifier to non-empty-Γ cases. -/
  theorem shift {d e₁ e₂} (h : Equiv_c d e₁ e₂) :
      Equiv_c (d+1) (e₁.shift 1 0) (e₂.shift 1 0) := by
    intro S Γ hd
    -- |Γ| ≥ d+1, so Γ ≠ [].
    match Γ, hd with
    | head :: tail, hd =>
      have htail_len : d ≤ tail.length := by
        simp only [List.length_cons] at hd; omega
      have ⟨h12, h21⟩ := h (S := []) (Γe := tail) htail_len
      have h12' := Subtype'.ctx_extend (S := []) [head] h12
      have h21' := Subtype'.ctx_extend (S := []) [head] h21
      -- ctx_extend output context = [head] ++ tail = head :: tail.
      simp only [List.length_cons, List.length_nil, Nat.zero_add,
                 List.nil_append, List.cons_append] at h12' h21'
      -- S is mapped via Seen.extendEntry 1 tail.length. For
      -- our uses with S = [], this is fine; for general S we
      -- weaken from [] to S.
      refine ⟨Subtype'.weaken ?_ h12', Subtype'.weaken ?_ h21'⟩
      all_goals (intro _ hmem; simp [List.map_nil] at hmem)

  /-- **Equiv_c.subst_resp**: substitution congruence for `Equiv_c`.
  Given `Equiv_c d a b`, for any `body` and position `i`,
  `Equiv_c d (body.subst i a) (body.subst i b)`.

  The key insight: when descending under a binder (.lam/.iota/.fix/.letE),
  the inner call substitutes `a.shift 1 0` vs `b.shift 1 0` at position
  `i+1`. By `Equiv_c.shift`, these are `Equiv_c (d+1)` — exactly what's
  needed at the extended context.

  Proof: structural induction on body. No closedness side condition —
  `Equiv_c.shift` paid for the shift at binder crossings. -/
  theorem subst_resp (body : Expr) {d a b}
      (heq : Equiv_c d a b) (i : Nat) :
      Equiv_c d (body.subst i a) (body.subst i b) := by
    induction body generalizing d a b i with
    | bvar k =>
      unfold Expr.subst
      split
      · -- k = i: subst gives a / b.
        exact heq
      · split
        · -- k > i after adjustment: subst gives .bvar (k-1).
          exact Equiv_c.refl _ _
        · -- k ≠ i: subst gives .bvar k.
          exact Equiv_c.refl _ _
    | type =>
      unfold Expr.subst
      exact Equiv_c.refl _ _
    | lam dom body ihD ihB =>
      unfold Expr.subst
      intro S Γ hd
      obtain ⟨hd12, hd21⟩ := ihD heq i hd
      -- Under the .lam binder, we're at (dom_b.subst i b :: Γ), length ≥ d+1.
      -- Apply ihB with substituend (a.shift 1 0) vs (b.shift 1 0), position i+1,
      -- at depth d+1.
      have heq' : Equiv_c (d+1) (a.shift 1 0) (b.shift 1 0) := Equiv_c.shift heq
      have hle : d+1 ≤ (dom.subst i b :: Γ).length := by
        simp only [List.length_cons]; omega
      obtain ⟨hb12, hb21⟩ := ihB heq' (i+1) hle
      have hle' : d+1 ≤ (dom.subst i a :: Γ).length := by
        simp only [List.length_cons]; omega
      obtain ⟨hb12', hb21'⟩ := ihB heq' (i+1) hle'
      refine ⟨.lam hd21 hb12, .lam hd12 hb21'⟩
    | app f x ihF ihX =>
      unfold Expr.subst
      intro S Γ hd
      obtain ⟨hf12, hf21⟩ := ihF heq i hd
      obtain ⟨hx12, hx21⟩ := ihX heq i hd
      refine ⟨.app_cong hf12 hx12 hx21, .app_cong hf21 hx21 hx12⟩
    | asc t ty ihT _ihTy =>
      unfold Expr.subst
      intro S Γ hd
      obtain ⟨ht12, ht21⟩ := ihT heq i hd
      refine ⟨.asc_L (.asc_R ht12), .asc_L (.asc_R ht21)⟩
    | iota ann body ihA ihB =>
      unfold Expr.subst
      intro S Γ hd
      obtain ⟨ha12, ha21⟩ := ihA heq i hd
      have heq' : Equiv_c (d+1) (a.shift 1 0) (b.shift 1 0) := Equiv_c.shift heq
      have hle : d+1 ≤ (ann.subst i b :: Γ).length := by
        simp only [List.length_cons]; omega
      obtain ⟨hb12, _hb21⟩ := ihB heq' (i+1) hle
      have hle' : d+1 ≤ (ann.subst i a :: Γ).length := by
        simp only [List.length_cons]; omega
      obtain ⟨_hb12', hb21'⟩ := ihB heq' (i+1) hle'
      refine ⟨.iota_cong ha12 hb12, .iota_cong ha21 hb21'⟩
    | «fix» ann body ihA ihB =>
      unfold Expr.subst
      intro S Γ hd
      obtain ⟨ha12, ha21⟩ := ihA heq i hd
      have heq' : Equiv_c (d+1) (a.shift 1 0) (b.shift 1 0) := Equiv_c.shift heq
      have hle : d+1 ≤ (ann.subst i b :: Γ).length := by
        simp only [List.length_cons]; omega
      obtain ⟨hb12, _hb21⟩ := ihB heq' (i+1) hle
      have hle' : d+1 ≤ (ann.subst i a :: Γ).length := by
        simp only [List.length_cons]; omega
      obtain ⟨_hb12', hb21'⟩ := ihB heq' (i+1) hle'
      refine ⟨.fix_cong ha12 hb12, .fix_cong ha21 hb21'⟩
    | letE val body ihV ihB =>
      unfold Expr.subst
      intro S Γ hd
      obtain ⟨hv12, hv21⟩ := ihV heq i hd
      have heq' : Equiv_c (d+1) (a.shift 1 0) (b.shift 1 0) := Equiv_c.shift heq
      have hle : d+1 ≤ (val.subst i b :: Γ).length := by
        simp only [List.length_cons]; omega
      obtain ⟨hb12, _hb21⟩ := ihB heq' (i+1) hle
      have hle' : d+1 ≤ (val.subst i a :: Γ).length := by
        simp only [List.length_cons]; omega
      obtain ⟨_hb12', hb21'⟩ := ihB heq' (i+1) hle'
      refine ⟨.letE_cong hv12 hb12, .letE_cong hv21 hb21'⟩

end Equiv_c

/-! ## Step-indexed logical relation

`R n d v e` means "at step index `n` and depth `d`, the
value `v` realises the expression `e`".

The constructor-specific conjunct for `.lam`/`.iota`/`.fix`
**exposes the closure's environment AND the head annotation**
as realised at the *same* step index `n+1`: `∃ ρe' he,
R (n+1) d headV he ∧ RList (n+1) d cl.env ρe' ∧ …
∧ Equiv e (.lam he (body.substEnv (lift ρe')))`. This lets
`vapp_realises`'s `.lam`-head case build
`REnv (n+1) d (a :: cl.env) (ae :: ρe')` and call
`eval_realises`'s fuel-IH directly — no Kripke step-loss.

The former *base conjunct* (`∀ e', quote fuelω d v = some e'
→ Equiv e' e`) was dropped 2026-04-21: it's unprovable inside
`eval_realises`'s fuel-IH (`quoteClosure`'s inner eval is at
`fuelω-1`, outside the IH). Recovered post-hoc as the
external `R_quote_equiv` via mutual recursion with
`quoteClosure_realises` on **quote-fuel** — see DECISION-LOG
2026-04-19.

The previous Kripke design (`∀ n' ≤ n, … → R n' d r …`) lost
one step-index at every `.app`-head boundary, leaving
`vapp_realises` unprovable (see the docstring there for the
detailed analysis of why both `(fuel,unf)`-lex and Ahmed-style
indexing also fail by exactly 1).

Termination: `R`/`RList` are mutual on `(n, sizeOf v)` lex.
The same-index recursion `R (n+1) d w …` for `w ∈ cl.env` and
for the head annotation is well-founded because
`sizeOf w < sizeOf cl.env < sizeOf cl < sizeOf (.lam _ cl)`,
and `sizeOf headV < sizeOf (.lam headV cl)`. -/

-- Val.levelsBelow / Val.fullyQuotable: defined here (before R)
-- so R's closure clauses can reference envLevelsBelow /
-- envFullyQuotable as invariants. Moved up 2026-04-22 as
-- prep for quoteClosure_realises refactor.
mutual
  /-- `Val.levelsBelow d v` iff every neutral-var level in `v` is
  `< d`. -/
  def Val.levelsBelow (d : Nat) : Val → Prop
    | .type => True
    | .neutral n => Neutral.levelsBelow d n
    | .lam dom cl => Val.levelsBelow d dom ∧ Closure.levelsBelow d cl
    | .iota ann cl => Val.levelsBelow d ann ∧ Closure.levelsBelow d cl
    | .«fix» ann cl => Val.levelsBelow d ann ∧ Closure.levelsBelow d cl

  def Neutral.levelsBelow (d : Nat) : Neutral → Prop
    | .var k => k < d
    | .app n v => Neutral.levelsBelow d n ∧ Val.levelsBelow d v
    | .stuckRec f a => Val.levelsBelow d f ∧ Val.levelsBelow d a

  def Closure.levelsBelow (d : Nat) : Closure → Prop
    | ⟨_body, env⟩ => Closure.envLevelsBelow d env

  /-- Helper for Closure.levelsBelow (inlined list quantifier). -/
  def Closure.envLevelsBelow (d : Nat) : List Val → Prop
    | [] => True
    | v :: vs => Val.levelsBelow d v ∧ Closure.envLevelsBelow d vs
end

/-! ### `Val.fullyQuotable`: recursive quotability through closure envs.

`Val.fullyQuotable d v` says: `v` is quotable at depth `d` AND every
Val reachable via `v`'s transitive closure-environments is quotable
at depth `d`. This is the invariant needed by R_depth_lift's closure
cases: when RList_depth_lift recurses into each `cl.env` entry, it
needs a quote witness for that entry, and if the entry is itself a
closure, quote witnesses for ITS env, and so on. -/
mutual
  def Val.fullyQuotable (d : Nat) : Val → Prop
    | .type => True
    | .neutral n => Neutral.fullyQuotable d n
    | .lam dom cl => Val.fullyQuotable d dom ∧ Closure.fullyQuotable d cl
    | .iota ann cl => Val.fullyQuotable d ann ∧ Closure.fullyQuotable d cl
    | .«fix» ann cl => Val.fullyQuotable d ann ∧ Closure.fullyQuotable d cl

  def Neutral.fullyQuotable (d : Nat) : Neutral → Prop
    | .var k => k < d
    | .app n v => Neutral.fullyQuotable d n ∧ Val.fullyQuotable d v
    | .stuckRec f a => Val.fullyQuotable d f ∧ Val.fullyQuotable d a

  def Closure.fullyQuotable (d : Nat) : Closure → Prop
    | ⟨body, env⟩ =>
        body.closedAt (env.length + 1) = true ∧ Closure.envFullyQuotable d env

  /-- Each env entry is fully quotable AND has a concrete quote
  witness at `d`. The quote witness is what RList_depth_lift's
  recursive R_depth_lift call needs. -/
  def Closure.envFullyQuotable (d : Nat) : List Val → Prop
    | [] => True
    | v :: vs =>
      (Val.fullyQuotable d v ∧ (∃ qe, quote fuelω d v = some qe)) ∧
      Closure.envFullyQuotable d vs
end

mutual
/-- See the `Step-indexed logical relation` section above. -/
def R : Nat → Nat → Val → Expr → Prop
  | 0, _, _, _ => True
  | n+1, d, v, e =>
      match v with
        | .lam dV cl =>
            -- Env-exposes only — no base conjunct for
            -- `.lam`/`.iota`/`.fix` (DECISION-LOG 2026-04-19).
            -- Recovered post-hoc by `R_quote_equiv` + mutual
            -- `quoteClosure_realises` on quote-fuel.
            ∃ ρe' dome,
              R (n+1) d dV dome ∧
              RList (n+1) d cl.env ρe' ∧
              cl.body.closedAt (ρe'.length + 1) = true ∧
              Equiv_c d e (.lam dome
                (cl.body.substEnv (.bvar 0 :: ρe'.map (·.shift 1 0))))
        | .iota aV cl =>
            ∃ ρe' anne,
              R (n+1) d aV anne ∧
              RList (n+1) d cl.env ρe' ∧
              cl.body.closedAt (ρe'.length + 1) = true ∧
              Equiv_c d e (.iota anne
                (cl.body.substEnv (.bvar 0 :: ρe'.map (·.shift 1 0))))
        | .«fix» aV cl =>
            ∃ ρe' anne,
              R (n+1) d aV anne ∧
              RList (n+1) d cl.env ρe' ∧
              cl.body.closedAt (ρe'.length + 1) = true ∧
              Equiv_c d e (.fix anne
                (cl.body.substEnv (.bvar 0 :: ρe'.map (·.shift 1 0))))
        -- `.type`/`.neutral` keep the base conjunct: quoting
        -- them doesn't recurse into environments, so the
        -- correspondence is provable inside `eval_realises`'s
        -- fuel-IH directly. Uses Equiv_c d (depth-parametrised
        -- Equiv) so R_depth_lift can close via Equiv_c.shift.
        | .type => ∀ e', quote fuelω d v = some e' → Equiv_c d e' e
        | .neutral _ => ∀ e', quote fuelω d v = some e' → Equiv_c d e' e
termination_by _ _ v _ => sizeOf v
decreasing_by
  all_goals simp_wf
  all_goals first
    | omega
    | (rename Closure => cl; cases cl; simp; omega)

/-- Pointwise list realisation, mutual with `R` so the
`.lam`/`.iota`/`.fix` clauses can reference it at the *same*
step-index (well-founded by `sizeOf`). Equivalent to the
indexed `REnv` form (see `REnv_iff_RList`). -/
def RList : Nat → Nat → List Val → List Expr → Prop
  | _, _, [], [] => True
  | n, d, v :: ρ, e :: ρe => R n d v e ∧ RList n d ρ ρe
  | _, _, [], _ :: _ => False
  | _, _, _ :: _, [] => False
termination_by _ _ ρ _ => sizeOf ρ
decreasing_by all_goals (simp_wf; omega)
end

/-- An environment `ρ` realises an expression-environment
`ρe` at index `n`, depth `d`. Indexed form, equivalent to the
mutual `RList` (see `REnv_iff_RList`). All env-level lemmas
are stated on `REnv`; conversion happens at `R`'s clause
boundary. -/
def REnv (n d : Nat) (ρ : Env) (ρe : List Expr) : Prop :=
  ρ.length = ρe.length ∧
  ∀ k v, ρ[k]? = some v → ∃ e, ρe.get? k = some e ∧ R n d v e

theorem RList_length {n d ρ ρe} (h : RList n d ρ ρe) :
    ρ.length = ρe.length := by
  induction ρ generalizing ρe with
  | nil => cases ρe with
    | nil => rfl
    | cons => unfold RList at h; exact h.elim
  | cons v ρ ih => cases ρe with
    | nil => unfold RList at h; exact h.elim
    | cons e ρe =>
        unfold RList at h
        simp only [List.length_cons, Nat.succ.injEq]
        exact ih h.2

theorem REnv_iff_RList {n d ρ ρe} : REnv n d ρ ρe ↔ RList n d ρ ρe := by
  constructor
  · intro ⟨hlen, hidx⟩
    induction ρ generalizing ρe with
    | nil =>
        cases ρe with
        | nil => unfold RList; trivial
        | cons => simp at hlen
    | cons v ρ ih =>
        cases ρe with
        | nil => simp at hlen
        | cons e ρe =>
            unfold RList
            have h0 := hidx 0 v (by simp)
            obtain ⟨e0, he0, hR0⟩ := h0
            simp only [List.get?_eq_getElem?,
                       List.getElem?_cons_zero, Option.some.injEq] at he0
            refine ⟨he0 ▸ hR0, ih (by simpa using hlen) ?_⟩
            intro k w hk
            have := hidx (k+1) w (by simpa using hk)
            simpa [List.get?_eq_getElem?] using this
  · intro h
    refine ⟨RList_length h, ?_⟩
    intro k v hk
    induction ρ generalizing ρe k with
    | nil => simp at hk
    | cons w ρ ih =>
        cases ρe with
        | nil => unfold RList at h; exact h.elim
        | cons e ρe =>
            unfold RList at h
            cases k with
            | zero =>
                simp only [List.getElem?_cons_zero,
                           Option.some.injEq] at hk
                exact ⟨e, by simp, hk ▸ h.1⟩
            | succ j =>
                simp only [List.getElem?_cons_succ] at hk
                obtain ⟨e', he', hR'⟩ := ih (ρe := ρe) (k := j) h.2 hk
                exact ⟨e', by simpa using he', hR'⟩

theorem RList_of_REnv {n d ρ ρe} (h : REnv n d ρ ρe) :
    RList n d ρ ρe := REnv_iff_RList.mp h
theorem REnv_of_RList {n d ρ ρe} (h : RList n d ρ ρe) :
    REnv n d ρ ρe := REnv_iff_RList.mpr h

mutual
/-- Downward closure: realisation at a larger step index
implies realisation at every smaller one. The constructor
clauses' `RList (n+1)` lowers via mutual `RList_mono`, and
the head annotation's `R (n+1)` via `R_mono` at `sizeOf
headV < sizeOf (.lam headV cl)`. -/
theorem R_mono {n m d v e} (hle : m ≤ n) (h : R n d v e) :
    R m d v e := by
  -- Match on `v` at the top level (alongside `m`/`n`) so the
  -- termination machinery sees the substituted constructor
  -- when proving `sizeOf cl.env < sizeOf v` for the
  -- `RList_mono` cross-calls.
  match m, n, v, hle, h with
  | 0, _, _, _, _ => unfold R; trivial
  | _+1, _+1, .type, _, h => unfold R at h ⊢; exact h
  | _+1, _+1, .neutral _, _, h => unfold R at h ⊢; exact h
  | _+1, _+1, .lam dV cl, hle, h =>
      unfold R at h ⊢
      obtain ⟨ρe', dome, hRd, hRL, hclb, heqL⟩ := h
      exact ⟨ρe', dome, R_mono hle hRd, RList_mono hle hRL, hclb, heqL⟩
  | _+1, _+1, .iota aV cl, hle, h =>
      unfold R at h ⊢
      obtain ⟨ρe', anne, hRa, hRL, hclb, heqI⟩ := h
      exact ⟨ρe', anne, R_mono hle hRa, RList_mono hle hRL, hclb, heqI⟩
  | _+1, _+1, .«fix» aV cl, hle, h =>
      unfold R at h ⊢
      obtain ⟨ρe', anne, hRa, hRL, hclb, heqF⟩ := h
      exact ⟨ρe', anne, R_mono hle hRa, RList_mono hle hRL, hclb, heqF⟩
termination_by sizeOf v
decreasing_by
  all_goals simp_wf
  all_goals first
    | omega
    | (rename Closure => cl; cases cl; simp; omega)

theorem RList_mono {n m d ρ ρe} (hle : m ≤ n)
    (h : RList n d ρ ρe) : RList m d ρ ρe := by
  match ρ, ρe with
  | [], [] => unfold RList; trivial
  | [], _ :: _ => unfold RList at h; exact h.elim
  | _ :: _, [] => unfold RList at h; exact h.elim
  | v :: ρ, e :: ρe =>
      unfold RList at h ⊢
      exact ⟨R_mono hle h.1, RList_mono hle h.2⟩
termination_by sizeOf ρ
decreasing_by all_goals (simp_wf; omega)
end

theorem REnv_mono {n m d ρ ρe} (hle : m ≤ n) (h : REnv n d ρ ρe) :
    REnv m d ρ ρe := by
  refine ⟨h.1, ?_⟩
  intro k v hk
  obtain ⟨e, he, hR⟩ := h.2 k v hk
  exact ⟨e, he, R_mono hle hR⟩

/-- `R` respects `Equiv` on the Expr side. With the
env-exposes clause, `e` appears only in the constructor
clause's `Equiv e (.ctor …)` — rewrites by `Equiv.trans`.
**No recursion** (neither `RList` nor the head `R (n+1) d
headV he` clause mentions `e`). -/
theorem R_resp_Equiv {n d v e e'}
    (heq : Equiv e e') (h : R n d v e) : R n d v e' := by
  match n, h with
  | 0, _ => unfold R; trivial
  | _+1, h =>
    unfold R at h ⊢
    cases v with
    | type => exact fun qe hq =>
        Equiv_c.trans (h qe hq) (Equiv_c.of_Equiv heq)
    | neutral _ => exact fun qe hq =>
        Equiv_c.trans (h qe hq) (Equiv_c.of_Equiv heq)
    | lam dV cl =>
        obtain ⟨ρe', dome, hRd, hRL, hclb, heqL⟩ := h
        exact ⟨ρe', dome, hRd, hRL, hclb,
          Equiv_c.trans (Equiv_c.of_Equiv (Equiv.symm heq)) heqL⟩
    | iota aV cl =>
        obtain ⟨ρe', anne, hRa, hRL, hclb, heqI⟩ := h
        exact ⟨ρe', anne, hRa, hRL, hclb,
          Equiv_c.trans (Equiv_c.of_Equiv (Equiv.symm heq)) heqI⟩
    | «fix» aV cl =>
        obtain ⟨ρe', anne, hRa, hRL, hclb, heqF⟩ := h
        exact ⟨ρe', anne, hRa, hRL, hclb,
          Equiv_c.trans (Equiv_c.of_Equiv (Equiv.symm heq)) heqF⟩

/-- Depth-parametrised variant of `R_resp_Equiv`: accepts
`Equiv_c d` (weaker, but sufficient for R at depth `d`).
Used in `vapp_realises`'s `.lam`/`.iota`/`.fix` head cases
where the rewriting Equiv is derived from R's own clause
(which now carries `Equiv_c d`). -/
theorem R_resp_Equiv_c {n d v e e'}
    (heq : Equiv_c d e e') (h : R n d v e) : R n d v e' := by
  match n, h with
  | 0, _ => unfold R; trivial
  | _+1, h =>
    unfold R at h ⊢
    cases v with
    | type => exact fun qe hq =>
        Equiv_c.trans (h qe hq) heq
    | neutral _ => exact fun qe hq =>
        Equiv_c.trans (h qe hq) heq
    | lam dV cl =>
        obtain ⟨ρe', dome, hRd, hRL, hclb, heqL⟩ := h
        exact ⟨ρe', dome, hRd, hRL, hclb,
          Equiv_c.trans (Equiv_c.symm heq) heqL⟩
    | iota aV cl =>
        obtain ⟨ρe', anne, hRa, hRL, hclb, heqI⟩ := h
        exact ⟨ρe', anne, hRa, hRL, hclb,
          Equiv_c.trans (Equiv_c.symm heq) heqI⟩
    | «fix» aV cl =>
        obtain ⟨ρe', anne, hRa, hRL, hclb, heqF⟩ := h
        exact ⟨ρe', anne, hRa, hRL, hclb,
          Equiv_c.trans (Equiv_c.symm heq) heqF⟩

/-- A prefix of a realised environment is realised (used for
`Closure.mk'`'s env-trimming, which keeps only the first
`bvarBound body - 1` entries). -/
theorem REnv_take {n d ρ ρe} (j : Nat) (h : REnv n d ρ ρe) :
    REnv n d (ρ.take j) (ρe.take j) := by
  refine ⟨by simp [List.length_take, h.1], ?_⟩
  intro k v hk
  rw [List.getElem?_take] at hk
  split at hk
  · obtain ⟨e, he, hR⟩ := h.2 k v hk
    exact ⟨e, by rw [List.get?_eq_getElem?, List.getElem?_take]; simp_all, hR⟩
  · simp at hk

/-- `bvarBound` is the *least* `j` such that `closedAt j e` —
in particular `e.closedAt (bvarBound e)`. -/
theorem closedAt_bvarBound (e : Expr) : e.closedAt (bvarBound e) = true := by
  induction e with
  | bvar k => simp [Expr.closedAt, bvarBound]
  | type => simp [Expr.closedAt, bvarBound]
  | lam dom body ihd ihb =>
      simp only [Expr.closedAt, bvarBound, Bool.and_eq_true]
      exact ⟨Expr.closedAt_mono ihd (Nat.le_max_left _ _),
             Expr.closedAt_mono ihb (by omega)⟩
  | iota ann body iha ihb =>
      simp only [Expr.closedAt, bvarBound, Bool.and_eq_true]
      exact ⟨Expr.closedAt_mono iha (Nat.le_max_left _ _),
             Expr.closedAt_mono ihb (by omega)⟩
  | «fix» ann body iha ihb =>
      simp only [Expr.closedAt, bvarBound, Bool.and_eq_true]
      exact ⟨Expr.closedAt_mono iha (Nat.le_max_left _ _),
             Expr.closedAt_mono ihb (by omega)⟩
  | letE val body ihv ihb =>
      simp only [Expr.closedAt, bvarBound, Bool.and_eq_true]
      exact ⟨Expr.closedAt_mono ihv (Nat.le_max_left _ _),
             Expr.closedAt_mono ihb (by omega)⟩
  | app f a ihf iha =>
      simp only [Expr.closedAt, bvarBound, Bool.and_eq_true]
      exact ⟨Expr.closedAt_mono ihf (Nat.le_max_left _ _),
             Expr.closedAt_mono iha (Nat.le_max_right _ _)⟩
  | asc t ty iht ihy =>
      simp only [Expr.closedAt, bvarBound, Bool.and_eq_true]
      exact ⟨Expr.closedAt_mono iht (Nat.le_max_left _ _),
             Expr.closedAt_mono ihy (Nat.le_max_right _ _)⟩

/-- Converse of `closedAt_bvarBound`: if `e` is closed at `n`,
its bvar bound is at most `n`. -/
theorem bvarBound_le_of_closedAt {e : Expr} {n : Nat}
    (h : e.closedAt n = true) : bvarBound e ≤ n := by
  induction e generalizing n with
  | bvar k => simp only [Expr.closedAt, decide_eq_true_eq] at h
              simp only [bvarBound]; omega
  | type => simp [bvarBound]
  | lam d b ihd ihb | iota d b ihd ihb | «fix» d b ihd ihb
  | letE d b ihd ihb =>
      simp only [Expr.closedAt, Bool.and_eq_true] at h
      simp only [bvarBound, Nat.max_le]
      exact ⟨ihd h.1, by have := ihb h.2; omega⟩
  | app f a ihf iha | asc f a ihf iha =>
      simp only [Expr.closedAt, Bool.and_eq_true] at h
      simp only [bvarBound, Nat.max_le]
      exact ⟨ihf h.1, iha h.2⟩

/-- For a `Closure.mk'`-built closure, the body is closed at
`cl.env.length + 1` (trimming guarantees this exactly). -/
theorem Closure.mk'_body_closed (body : Expr) (ρ : Env)
    (hρ : bvarBound body ≤ ρ.length + 1) :
    body.closedAt ((Closure.mk' body ρ).env.length + 1) = true := by
  unfold Closure.mk'
  simp only [List.length_take]
  exact Expr.closedAt_mono (closedAt_bvarBound body) (by omega)

private theorem substEnv_bvar_eq (γ : List Expr) (k : Nat) :
    Expr.substEnv γ (.bvar k) = (γ[k]?).getD (.bvar k) := by
  simp only [Expr.substEnv]
  by_cases h : k < γ.length
  · rw [if_pos h, List.getElem?_eq_getElem h, Option.getD_some]
    exact List.getElem!_of_getElem? (List.getElem?_eq_getElem h)
  · rw [if_neg h, List.getElem?_eq_none (Nat.le_of_not_lt h),
        Option.getD_none]

/-- General env-irrelevance for `substEnv`: if `e.closedAt j`
and the two environments agree on indices `< j`, the
substitution results agree. -/
theorem substEnv_agree {e : Expr} :
    ∀ {j : Nat}, e.closedAt j = true →
    ∀ {γ₁ γ₂ : List Expr}, (∀ k, k < j → γ₁[k]? = γ₂[k]?) →
    e.substEnv γ₁ = e.substEnv γ₂ := by
  induction e with
  | bvar k =>
    intro j hcl γ₁ γ₂ hagree
    simp only [Expr.closedAt, decide_eq_true_eq] at hcl
    rw [substEnv_bvar_eq, substEnv_bvar_eq, hagree k hcl]
  | type => intros; rfl
  | lam dom body ihd ihb =>
    intro j hcl γ₁ γ₂ hagree
    simp only [Expr.closedAt, Bool.and_eq_true] at hcl
    simp only [Expr.substEnv]
    congr 1
    · exact ihd hcl.1 hagree
    · refine ihb hcl.2 ?_
      intro k hk
      cases k with
      | zero => simp
      | succ m =>
        simp only [List.getElem?_cons_succ, List.getElem?_map]
        rw [hagree m (by omega)]
  | iota ann body iha ihb =>
    intro j hcl γ₁ γ₂ hagree
    simp only [Expr.closedAt, Bool.and_eq_true] at hcl
    simp only [Expr.substEnv]
    congr 1
    · exact iha hcl.1 hagree
    · refine ihb hcl.2 ?_
      intro k hk
      cases k with
      | zero => simp
      | succ m =>
        simp only [List.getElem?_cons_succ, List.getElem?_map]
        rw [hagree m (by omega)]
  | fix ann body iha ihb =>
    intro j hcl γ₁ γ₂ hagree
    simp only [Expr.closedAt, Bool.and_eq_true] at hcl
    simp only [Expr.substEnv]
    congr 1
    · exact iha hcl.1 hagree
    · refine ihb hcl.2 ?_
      intro k hk
      cases k with
      | zero => simp
      | succ m =>
        simp only [List.getElem?_cons_succ, List.getElem?_map]
        rw [hagree m (by omega)]
  | letE val body ihv ihb =>
    intro j hcl γ₁ γ₂ hagree
    simp only [Expr.closedAt, Bool.and_eq_true] at hcl
    simp only [Expr.substEnv]
    congr 1
    · exact ihv hcl.1 hagree
    · refine ihb hcl.2 ?_
      intro k hk
      cases k with
      | zero => simp
      | succ m =>
        simp only [List.getElem?_cons_succ, List.getElem?_map]
        rw [hagree m (by omega)]
  | app f a ihf iha =>
    intro j hcl γ₁ γ₂ hagree
    simp only [Expr.closedAt, Bool.and_eq_true] at hcl
    simp only [Expr.substEnv]
    congr 1
    · exact ihf hcl.1 hagree
    · exact iha hcl.2 hagree
  | asc t ty iht ihy =>
    intro j hcl γ₁ γ₂ hagree
    simp only [Expr.closedAt, Bool.and_eq_true] at hcl
    simp only [Expr.substEnv]
    congr 1
    · exact iht hcl.1 hagree
    · exact ihy hcl.2 hagree

/-- **substEnv preserves closedness.** If `e.closedAt ρe.length`
and every `ρe[k]` is `closedAt n`, then `e.substEnv ρe` is
`closedAt n`.

Proof: structural induction on `e`. `.bvar k` case uses the
hypothesis on `ρe[k]`; `.lam/.iota/.fix/.letE` cases extend
the env with `.bvar 0 :: ρe.map (·.shift 1 0)` and recurse at
`n+1` (each shifted ρe entry preserves closedAt via
`shift_closedAt`; the new `.bvar 0` is closedAt 1 ≤ n+1). -/
theorem substEnv_closedAt {e : Expr} {n : Nat} {ρe : List Expr}
    (hbound : e.closedAt ρe.length = true)
    (hρecl : ∀ (k : Nat) (e' : Expr), ρe[k]? = some e' →
             e'.closedAt n = true) :
    (e.substEnv ρe).closedAt n = true := by
  induction e generalizing n ρe with
  | bvar k =>
    simp only [Expr.closedAt, decide_eq_true_eq] at hbound
    unfold Expr.substEnv
    simp only [hbound, ↓reduceIte]
    have hget : ρe[k]? = some ρe[k]! := by
      rw [List.getElem!_eq_getElem?_getD]
      simp [List.getElem?_eq_getElem hbound]
    exact hρecl k ρe[k]! hget
  | type => simp [Expr.substEnv, Expr.closedAt]
  | lam dom body ihD ihB =>
    simp only [Expr.closedAt, Bool.and_eq_true] at hbound
    unfold Expr.substEnv
    simp only [Expr.closedAt, Bool.and_eq_true]
    refine ⟨ihD hbound.1 hρecl, ?_⟩
    apply ihB
    · simp [List.length_map, hbound.2]
    · intro k e' hk
      cases k with
      | zero =>
        simp only [List.getElem?_cons_zero, Option.some.injEq] at hk
        subst hk
        simp [Expr.closedAt]
      | succ m =>
        simp only [List.getElem?_cons_succ, List.getElem?_map,
                   Option.map_eq_some'] at hk
        obtain ⟨e'', he'', heq⟩ := hk
        subst heq
        exact Expr.shift_closedAt e'' n 1 0 (Nat.zero_le _) (hρecl m e'' he'')
  | app f a ihF ihA =>
    simp only [Expr.closedAt, Bool.and_eq_true] at hbound
    unfold Expr.substEnv
    simp only [Expr.closedAt, Bool.and_eq_true]
    exact ⟨ihF hbound.1 hρecl, ihA hbound.2 hρecl⟩
  | asc t ty ihT ihTy =>
    simp only [Expr.closedAt, Bool.and_eq_true] at hbound
    unfold Expr.substEnv
    simp only [Expr.closedAt, Bool.and_eq_true]
    exact ⟨ihT hbound.1 hρecl, ihTy hbound.2 hρecl⟩
  | iota ann body ihA ihB =>
    simp only [Expr.closedAt, Bool.and_eq_true] at hbound
    unfold Expr.substEnv
    simp only [Expr.closedAt, Bool.and_eq_true]
    refine ⟨ihA hbound.1 hρecl, ?_⟩
    apply ihB
    · simp [List.length_map, hbound.2]
    · intro k e' hk
      cases k with
      | zero =>
        simp only [List.getElem?_cons_zero, Option.some.injEq] at hk
        subst hk
        simp [Expr.closedAt]
      | succ m =>
        simp only [List.getElem?_cons_succ, List.getElem?_map,
                   Option.map_eq_some'] at hk
        obtain ⟨e'', he'', heq⟩ := hk
        subst heq
        exact Expr.shift_closedAt e'' n 1 0 (Nat.zero_le _) (hρecl m e'' he'')
  | «fix» ann body ihA ihB =>
    simp only [Expr.closedAt, Bool.and_eq_true] at hbound
    unfold Expr.substEnv
    simp only [Expr.closedAt, Bool.and_eq_true]
    refine ⟨ihA hbound.1 hρecl, ?_⟩
    apply ihB
    · simp [List.length_map, hbound.2]
    · intro k e' hk
      cases k with
      | zero =>
        simp only [List.getElem?_cons_zero, Option.some.injEq] at hk
        subst hk
        simp [Expr.closedAt]
      | succ m =>
        simp only [List.getElem?_cons_succ, List.getElem?_map,
                   Option.map_eq_some'] at hk
        obtain ⟨e'', he'', heq⟩ := hk
        subst heq
        exact Expr.shift_closedAt e'' n 1 0 (Nat.zero_le _) (hρecl m e'' he'')
  | letE val body ihV ihB =>
    simp only [Expr.closedAt, Bool.and_eq_true] at hbound
    unfold Expr.substEnv
    simp only [Expr.closedAt, Bool.and_eq_true]
    refine ⟨ihV hbound.1 hρecl, ?_⟩
    apply ihB
    · simp [List.length_map, hbound.2]
    · intro k e' hk
      cases k with
      | zero =>
        simp only [List.getElem?_cons_zero, Option.some.injEq] at hk
        subst hk
        simp [Expr.closedAt]
      | succ m =>
        simp only [List.getElem?_cons_succ, List.getElem?_map,
                   Option.map_eq_some'] at hk
        obtain ⟨e'', he'', heq⟩ := hk
        subst heq
        exact Expr.shift_closedAt e'' n 1 0 (Nat.zero_le _) (hρecl m e'' he'')

/-- `substEnv` only depends on the prefix of the environment
that the term can reach. With `e.closedAt (j+1)` and
`ρe.take j = ρe'`, substituting under `x :: ρe'` gives the
same result as under `x :: ρe`. Corollary of
`substEnv_agree`. -/
theorem substEnv_closedAt_irrel {e : Expr} {j : Nat}
    (hcl : e.closedAt (j+1) = true)
    {x : Expr} {ρe ρe' : List Expr}
    (hpfx : ρe' = ρe.take j) :
    e.substEnv (x :: ρe') = e.substEnv (x :: ρe) := by
  refine substEnv_agree hcl ?_
  intro k hk
  cases k with
  | zero => simp
  | succ m =>
    simp only [List.getElem?_cons_succ]
    subst hpfx
    rw [List.getElem?_take, if_pos (by omega : m < j)]

/-- **substEnv-shift commutation**:
`(substEnv γ body).shift 1 c = substEnv (γ.map (·.shift 1 c)) body`
when `body.closedAt γ.length = true`.

Proof: structural induction on body. Binder cases (.lam/.iota/.fix/.letE)
recurse at `c+1` with γ extended by `.bvar 0 :: γ.map (·.shift 1 0)`.
The inductive step requires `shift_shift_comm_gen` to line up the
env-shift forms through the binder transition. -/
theorem substEnv_shift_comm : ∀ (body : Expr) (γ : List Expr) (c : Nat),
    body.closedAt γ.length = true →
    (Expr.substEnv γ body).shift 1 c
      = Expr.substEnv (γ.map (·.shift 1 c)) body := by
  intro body
  induction body with
  | bvar k =>
    intro γ c hcl
    simp only [Expr.closedAt, decide_eq_true_eq] at hcl
    simp only [Expr.substEnv, List.length_map, hcl, ↓reduceIte]
    rw [List.getElem!_eq_getElem?_getD, List.getElem!_eq_getElem?_getD,
        List.getElem?_eq_getElem hcl,
        List.getElem?_map, List.getElem?_eq_getElem hcl]
    simp
  | type =>
    intro γ c _hcl
    simp only [Expr.substEnv, Expr.shift]
  | lam dom body ihD ihB =>
    intro γ c hcl
    simp only [Expr.closedAt, Bool.and_eq_true] at hcl
    have hcl_body : body.closedAt ((.bvar 0 :: γ.map (·.shift 1 0)).length) = true := by
      simpa [List.length_map] using hcl.2
    have hD := ihD γ c hcl.1
    have hB := ihB (.bvar 0 :: γ.map (·.shift 1 0)) (c+1) hcl_body
    simp only [Expr.substEnv, Expr.shift]
    rw [hD, hB]
    -- Goal now: .lam _ (substEnv LHS-env body) = .lam _ (substEnv RHS-env body).
    congr 1
    -- Goal: substEnv LHS-env body = substEnv RHS-env body.
    congr 1
    -- Goal: LHS-env = RHS-env where both are .bvar 0 :: ...
    simp only [List.map_cons, Expr.shift, decide_eq_true_eq,
               show (0 : Nat) < c + 1 from Nat.succ_pos _, ↓reduceIte]
    rw [List.map_map, List.map_map]
    -- Goal: .bvar 0 :: γ.map (f ∘ g) = .bvar 0 :: γ.map (g' ∘ f')
    refine congrArg (List.cons (Expr.bvar 0)) ?_
    apply List.map_congr_left
    intro e _he
    simp only [Function.comp]
    exact Expr.shift_shift_comm_gen e 1 c 1
  | app f a ihF ihA =>
    intro γ c hcl
    simp only [Expr.closedAt, Bool.and_eq_true] at hcl
    simp only [Expr.substEnv, Expr.shift]
    rw [ihF γ c hcl.1, ihA γ c hcl.2]
  | asc t ty ihT ihTy =>
    intro γ c hcl
    simp only [Expr.closedAt, Bool.and_eq_true] at hcl
    simp only [Expr.substEnv, Expr.shift]
    rw [ihT γ c hcl.1, ihTy γ c hcl.2]
  | iota ann body ihA ihB =>
    intro γ c hcl
    simp only [Expr.closedAt, Bool.and_eq_true] at hcl
    have hcl_body : body.closedAt ((.bvar 0 :: γ.map (·.shift 1 0)).length) = true := by
      simpa [List.length_map] using hcl.2
    have hA := ihA γ c hcl.1
    have hB := ihB (.bvar 0 :: γ.map (·.shift 1 0)) (c+1) hcl_body
    simp only [Expr.substEnv, Expr.shift]
    rw [hA, hB]
    congr 1
    congr 1
    simp only [List.map_cons, Expr.shift, decide_eq_true_eq,
               show (0 : Nat) < c + 1 from Nat.succ_pos _, ↓reduceIte]
    rw [List.map_map, List.map_map]
    refine congrArg (List.cons (Expr.bvar 0)) ?_
    apply List.map_congr_left
    intro e _he
    simp only [Function.comp]
    exact Expr.shift_shift_comm_gen e 1 c 1
  | «fix» ann body ihA ihB =>
    intro γ c hcl
    simp only [Expr.closedAt, Bool.and_eq_true] at hcl
    have hcl_body : body.closedAt ((.bvar 0 :: γ.map (·.shift 1 0)).length) = true := by
      simpa [List.length_map] using hcl.2
    have hA := ihA γ c hcl.1
    have hB := ihB (.bvar 0 :: γ.map (·.shift 1 0)) (c+1) hcl_body
    simp only [Expr.substEnv, Expr.shift]
    rw [hA, hB]
    congr 1
    congr 1
    simp only [List.map_cons, Expr.shift, decide_eq_true_eq,
               show (0 : Nat) < c + 1 from Nat.succ_pos _, ↓reduceIte]
    rw [List.map_map, List.map_map]
    refine congrArg (List.cons (Expr.bvar 0)) ?_
    apply List.map_congr_left
    intro e _he
    simp only [Function.comp]
    exact Expr.shift_shift_comm_gen e 1 c 1
  | letE val body ihV ihB =>
    intro γ c hcl
    simp only [Expr.closedAt, Bool.and_eq_true] at hcl
    have hcl_body : body.closedAt ((.bvar 0 :: γ.map (·.shift 1 0)).length) = true := by
      simpa [List.length_map] using hcl.2
    have hV := ihV γ c hcl.1
    have hB := ihB (.bvar 0 :: γ.map (·.shift 1 0)) (c+1) hcl_body
    simp only [Expr.substEnv, Expr.shift]
    rw [hV, hB]
    congr 1
    congr 1
    simp only [List.map_cons, Expr.shift, decide_eq_true_eq,
               show (0 : Nat) < c + 1 from Nat.succ_pos _, ↓reduceIte]
    rw [List.map_map, List.map_map]
    refine congrArg (List.cons (Expr.bvar 0)) ?_
    apply List.map_congr_left
    intro e _he
    simp only [Function.comp]
    exact Expr.shift_shift_comm_gen e 1 c 1

/-!
### Semantic level shift (`Val.shiftLvl`) and `Val.levelsBelow`

`Val.shiftLvl c v` shifts every neutral-var level `k ≥ c` up by 1.
`Val.levelsBelow d v` says every level in `v` is `< d`. These are
the building blocks for `quote_depth_shift`'s closure case
(depth_lift_bundle.1). Full proof plan in the docstring of
`depth_lift_bundle` below. -/

mutual
  /-- Shift every neutral-var level `≥ c` up by 1. -/
  def Val.shiftLvl (c : Nat) : Val → Val
    | .type => .type
    | .neutral n => .neutral (Neutral.shiftLvl c n)
    | .lam dom cl => .lam (Val.shiftLvl c dom) (Closure.shiftLvl c cl)
    | .iota ann cl => .iota (Val.shiftLvl c ann) (Closure.shiftLvl c cl)
    | .«fix» ann cl => .«fix» (Val.shiftLvl c ann) (Closure.shiftLvl c cl)

  def Neutral.shiftLvl (c : Nat) : Neutral → Neutral
    | .var k => .var (if k < c then k else k + 1)
    | .app n v => .app (Neutral.shiftLvl c n) (Val.shiftLvl c v)
    | .stuckRec f a => .stuckRec (Val.shiftLvl c f) (Val.shiftLvl c a)

  def Closure.shiftLvl (c : Nat) : Closure → Closure
    | ⟨body, env⟩ => ⟨body, Closure.envShiftLvl c env⟩

  /-- Helper for Closure.shiftLvl (inlined `List.map`) so Lean's
  termination checker sees the recursive call into Val.shiftLvl. -/
  def Closure.envShiftLvl (c : Nat) : List Val → List Val
    | [] => []
    | v :: vs => Val.shiftLvl c v :: Closure.envShiftLvl c vs
end

theorem Val.shiftLvl_neutral_isNeutral (c : Nat) (v : Val) :
    (Val.shiftLvl c v).isNeutral = v.isNeutral := by
  cases v <;> unfold Val.shiftLvl <;> rfl

theorem Closure.envShiftLvl_eq_map (c : Nat) (env : List Val) :
    Closure.envShiftLvl c env = env.map (Val.shiftLvl c) := by
  induction env with
  | nil => rfl
  | cons v vs ih => simp [Closure.envShiftLvl, ih]

/-- `envLevelsBelow` ↔ "every entry has `levelsBelow`". -/
theorem Closure.envLevelsBelow_getElem?
    {d : Nat} {env : List Val}
    (h : Closure.envLevelsBelow d env)
    {k : Nat} {v : Val} (hk : env[k]? = some v) :
    Val.levelsBelow d v := by
  induction env generalizing k with
  | nil => simp at hk
  | cons w ws ih =>
      cases k with
      | zero =>
          simp only [List.getElem?_cons_zero, Option.some.injEq] at hk
          subst hk
          unfold Closure.envLevelsBelow at h
          exact h.1
      | succ m =>
          simp only [List.getElem?_cons_succ] at hk
          unfold Closure.envLevelsBelow at h
          exact ih h.2 hk

theorem Closure.envLevelsBelow_of_getElem?
    {d : Nat} {env : List Val}
    (h : ∀ (k : Nat) (v : Val),
      List.get? env k = some v → Val.levelsBelow d v) :
    Closure.envLevelsBelow d env := by
  induction env with
  | nil => unfold Closure.envLevelsBelow; trivial
  | cons w ws ih =>
      unfold Closure.envLevelsBelow
      refine ⟨h 0 w rfl, ih ?_⟩
      intro k v hk
      have := h (k+1) v
      simp only [List.get?_cons_succ] at this
      exact this hk

mutual
/-- Shift is a no-op when levels are already below the cutoff.
Joint mutual theorem on Val / Neutral / Closure, proved by
structural recursion on sizeOf. -/
theorem Val.shiftLvl_of_levelsBelow :
    ∀ (v : Val) (c : Nat),
    Val.levelsBelow c v → Val.shiftLvl c v = v
  | .type, _, _ => rfl
  | .neutral n, c, h => by
      unfold Val.shiftLvl Val.levelsBelow at *
      exact congrArg _ (Neutral.shiftLvl_of_levelsBelow n c h)
  | .lam dom cl, c, h => by
      unfold Val.shiftLvl Val.levelsBelow at *
      exact congr (congrArg _ (Val.shiftLvl_of_levelsBelow dom c h.1))
                  (Closure.shiftLvl_of_levelsBelow cl c h.2)
  | .iota ann cl, c, h => by
      unfold Val.shiftLvl Val.levelsBelow at *
      exact congr (congrArg _ (Val.shiftLvl_of_levelsBelow ann c h.1))
                  (Closure.shiftLvl_of_levelsBelow cl c h.2)
  | .«fix» ann cl, c, h => by
      unfold Val.shiftLvl Val.levelsBelow at *
      exact congr (congrArg _ (Val.shiftLvl_of_levelsBelow ann c h.1))
                  (Closure.shiftLvl_of_levelsBelow cl c h.2)

theorem Neutral.shiftLvl_of_levelsBelow :
    ∀ (n : Neutral) (c : Nat),
    Neutral.levelsBelow c n → Neutral.shiftLvl c n = n
  | .var _, _, h => by
      unfold Neutral.shiftLvl Neutral.levelsBelow at *
      simp [h]
  | .app n' v, c, h => by
      unfold Neutral.shiftLvl Neutral.levelsBelow at *
      exact congr (congrArg _ (Neutral.shiftLvl_of_levelsBelow n' c h.1))
                  (Val.shiftLvl_of_levelsBelow v c h.2)
  | .stuckRec f a, c, h => by
      unfold Neutral.shiftLvl Neutral.levelsBelow at *
      exact congr (congrArg _ (Val.shiftLvl_of_levelsBelow f c h.1))
                  (Val.shiftLvl_of_levelsBelow a c h.2)

theorem Closure.shiftLvl_of_levelsBelow :
    ∀ (cl : Closure) (c : Nat),
    Closure.levelsBelow c cl → Closure.shiftLvl c cl = cl
  | ⟨body, env⟩, c, h => by
      change Closure.envLevelsBelow c env at h
      show (⟨body, Closure.envShiftLvl c env⟩ : Closure) = ⟨body, env⟩
      congr 1
      exact Closure.envShiftLvl_of_envLevelsBelow env c h

theorem Closure.envShiftLvl_of_envLevelsBelow :
    ∀ (env : List Val) (c : Nat),
    Closure.envLevelsBelow c env → Closure.envShiftLvl c env = env
  | [], _, _ => rfl
  | w :: ws, c, h => by
      unfold Closure.envShiftLvl Closure.envLevelsBelow at *
      exact congr
        (congrArg _ (Val.shiftLvl_of_levelsBelow w c h.1))
        (Closure.envShiftLvl_of_envLevelsBelow ws c h.2)
end

/-!
### `eval` commutes with `Val.shiftLvl`

`eval fuel unf ρ e = some v` ⇒
`eval fuel unf (ρ.map (Val.shiftLvl c)) e = some (v.shiftLvl c)`.

Proved by combined induction on fuel over `eval` and `vapp`. The
vapp-iota/fix branches case-split on `a`-shape (to evaluate
`Val.shiftLvl c a`.isNeutral) and on the `isNeutral || unf==0`
gate. -/

theorem eval_vapp_shiftLvl :
    ∀ n,
    (∀ {unf c ρ e v}, eval n unf ρ e = some v →
      eval n unf (ρ.map (Val.shiftLvl c)) e = some (v.shiftLvl c)) ∧
    (∀ {unf c f a v}, vapp n unf f a = some v →
      vapp n unf (f.shiftLvl c) (a.shiftLvl c) = some (v.shiftLvl c)) := by
  intro n
  induction n with
  | zero =>
    refine ⟨?_, ?_⟩
    · intros _ _ _ _ _ h; rw [eval_zero] at h; cases h
    · intros _ _ _ _ _ h; rw [vapp_zero] at h; cases h
  | succ k ih =>
    obtain ⟨ihe, ihv⟩ := ih
    refine ⟨?_, ?_⟩
    -- eval (k+1)
    · intro unf c ρ e v h
      unfold eval at h ⊢
      match e, h with
      | .type, h =>
          simp only [Option.some.injEq] at h
          subst h; rfl
      | .bvar j, h =>
          simp only [] at h ⊢
          rw [List.getElem?_map]
          cases hk : ρ[j]? with
          | none => rw [hk] at h; cases h
          | some w =>
              rw [hk] at h
              simp only [Option.some.injEq] at h
              subst h
              simp only [Option.map_some']
      | .lam dom body, h =>
          simp only [Option.bind_eq_bind, Option.bind_eq_some] at h ⊢
          obtain ⟨dom', hdom, hv⟩ := h
          simp only [Option.some.injEq] at hv
          subst hv
          refine ⟨dom'.shiftLvl c, ihe hdom, ?_⟩
          simp only [Option.some.injEq]
          show Val.lam (Val.shiftLvl c dom') (Closure.mk' body (ρ.map (Val.shiftLvl c))) =
               Val.lam (Val.shiftLvl c dom')
                 (Closure.shiftLvl c (Closure.mk' body ρ))
          congr 1
          -- Closure.mk' body (ρ.map ...) = Closure.shiftLvl c (Closure.mk' body ρ)
          show Closure.mk' body (ρ.map (Val.shiftLvl c))
             = Closure.shiftLvl c (Closure.mk' body ρ)
          unfold Closure.mk' Closure.shiftLvl
          rw [Closure.envShiftLvl_eq_map]
          congr 1
          simp [List.map_take]
      | .iota ann body, h =>
          simp only [Option.bind_eq_bind, Option.bind_eq_some] at h ⊢
          obtain ⟨ann', hann, hv⟩ := h
          simp only [Option.some.injEq] at hv
          subst hv
          refine ⟨ann'.shiftLvl c, ihe hann, ?_⟩
          simp only [Option.some.injEq]
          show Val.iota (Val.shiftLvl c ann') (Closure.mk' body (ρ.map (Val.shiftLvl c))) =
               Val.iota (Val.shiftLvl c ann')
                 (Closure.shiftLvl c (Closure.mk' body ρ))
          congr 1
          show Closure.mk' body (ρ.map (Val.shiftLvl c))
             = Closure.shiftLvl c (Closure.mk' body ρ)
          unfold Closure.mk' Closure.shiftLvl
          rw [Closure.envShiftLvl_eq_map]
          congr 1
          simp [List.map_take]
      | .«fix» ann body, h =>
          simp only [Option.bind_eq_bind, Option.bind_eq_some] at h ⊢
          obtain ⟨ann', hann, hv⟩ := h
          simp only [Option.some.injEq] at hv
          subst hv
          refine ⟨ann'.shiftLvl c, ihe hann, ?_⟩
          simp only [Option.some.injEq]
          show Val.«fix» (Val.shiftLvl c ann') (Closure.mk' body (ρ.map (Val.shiftLvl c))) =
               Val.«fix» (Val.shiftLvl c ann')
                 (Closure.shiftLvl c (Closure.mk' body ρ))
          congr 1
          show Closure.mk' body (ρ.map (Val.shiftLvl c))
             = Closure.shiftLvl c (Closure.mk' body ρ)
          unfold Closure.mk' Closure.shiftLvl
          rw [Closure.envShiftLvl_eq_map]
          congr 1
          simp [List.map_take]
      | .app f a, h =>
          simp only [Option.bind_eq_bind, Option.bind_eq_some] at h ⊢
          obtain ⟨f', hf, a', ha, hv⟩ := h
          exact ⟨f'.shiftLvl c, ihe hf, a'.shiftLvl c, ihe ha, ihv hv⟩
      | .letE val body, h =>
          simp only [Option.bind_eq_bind, Option.bind_eq_some] at h ⊢
          obtain ⟨v', hv', hb⟩ := h
          refine ⟨v'.shiftLvl c, ihe hv', ?_⟩
          have := ihe (unf := unf) (c := c) (ρ := v' :: ρ) (e := body)
                      (v := v) hb
          simpa using this
      | .asc t _, h =>
          simp only [] at h ⊢
          exact ihe h
    -- vapp (k+1)
    · intro unf c f a v h
      unfold vapp at h ⊢
      cases f with
      | neutral nf =>
          simp only [Option.some.injEq] at h
          subst h
          rfl
      | type =>
          simp only [Option.some.injEq] at h
          subst h
          rfl
      | lam dom cl =>
          obtain ⟨body, env⟩ := cl
          simp only at h
          -- Target: eval on (shifted a :: Closure.envShiftLvl c env) body
          show eval k unf (Val.shiftLvl c a :: Closure.envShiftLvl c env) body =
               some (Val.shiftLvl c v)
          rw [Closure.envShiftLvl_eq_map]
          have := ihe (unf := unf) (c := c) (ρ := a :: env) (e := body)
                      (v := v) h
          simpa using this
      | iota ann cl =>
          obtain ⟨body, env⟩ := cl
          simp only at h
          -- After `cases f`, the goal has the iota arm of Val.shiftLvl
          -- unfolded. Use `show` to pin the goal structure.
          change (if ((Val.shiftLvl c a).isNeutral || unf == 0) = true
                  then some (Val.neutral (.stuckRec
                              (Val.iota (Val.shiftLvl c ann)
                                ⟨body, Closure.envShiftLvl c env⟩)
                              (Val.shiftLvl c a)))
                  else
                    (eval k (unf - 1)
                      (Val.iota (Val.shiftLvl c ann)
                        ⟨body, Closure.envShiftLvl c env⟩
                       :: Closure.envShiftLvl c env) body).bind
                      (fun f' => vapp k (unf - 1) f' (Val.shiftLvl c a)))
                 = some (Val.shiftLvl c v)
          have hge : (Val.shiftLvl c a).isNeutral = a.isNeutral :=
            Val.shiftLvl_neutral_isNeutral c a
          rw [hge]
          by_cases hg : (a.isNeutral || unf == 0) = true
          · simp only [hg, ↓reduceIte] at h ⊢
            simp only [Option.some.injEq] at h
            subst h
            rfl
          · simp only [Bool.not_eq_true] at hg
            simp only [hg, Bool.false_eq_true, ↓reduceIte,
                       Option.bind_eq_bind, Option.bind_eq_some] at h ⊢
            obtain ⟨f', hf, hv⟩ := h
            refine ⟨f'.shiftLvl c, ?_, ihv hv⟩
            have hhead : Val.shiftLvl c (Val.iota ann ⟨body, env⟩) =
                         Val.iota (Val.shiftLvl c ann) ⟨body, Closure.envShiftLvl c env⟩ := rfl
            have := ihe (unf := unf - 1) (c := c)
                        (ρ := Val.iota ann ⟨body, env⟩ :: env) (e := body)
                        (v := f') hf
            simp only [List.map_cons, hhead,
                       ← Closure.envShiftLvl_eq_map] at this
            exact this
      | fix ann cl =>
          obtain ⟨body, env⟩ := cl
          simp only at h
          change (if ((Val.shiftLvl c a).isNeutral || unf == 0) = true
                  then some (Val.neutral (.stuckRec
                              (Val.«fix» (Val.shiftLvl c ann)
                                ⟨body, Closure.envShiftLvl c env⟩)
                              (Val.shiftLvl c a)))
                  else
                    (eval k (unf - 1)
                      (Val.«fix» (Val.shiftLvl c ann)
                        ⟨body, Closure.envShiftLvl c env⟩
                       :: Closure.envShiftLvl c env) body).bind
                      (fun f' => vapp k (unf - 1) f' (Val.shiftLvl c a)))
                 = some (Val.shiftLvl c v)
          have hge : (Val.shiftLvl c a).isNeutral = a.isNeutral :=
            Val.shiftLvl_neutral_isNeutral c a
          rw [hge]
          by_cases hg : (a.isNeutral || unf == 0) = true
          · simp only [hg, ↓reduceIte] at h ⊢
            simp only [Option.some.injEq] at h
            subst h
            rfl
          · simp only [Bool.not_eq_true] at hg
            simp only [hg, Bool.false_eq_true, ↓reduceIte,
                       Option.bind_eq_bind, Option.bind_eq_some] at h ⊢
            obtain ⟨f', hf, hv⟩ := h
            refine ⟨f'.shiftLvl c, ?_, ihv hv⟩
            have hhead : Val.shiftLvl c (Val.«fix» ann ⟨body, env⟩) =
                         Val.«fix» (Val.shiftLvl c ann) ⟨body, Closure.envShiftLvl c env⟩ := rfl
            have := ihe (unf := unf - 1) (c := c)
                        (ρ := Val.«fix» ann ⟨body, env⟩ :: env) (e := body)
                        (v := f') hf
            simp only [List.map_cons, hhead,
                       ← Closure.envShiftLvl_eq_map] at this
            exact this

theorem eval_shiftLvl {n unf c ρ e v}
    (h : eval n unf ρ e = some v) :
    eval n unf (ρ.map (Val.shiftLvl c)) e = some (v.shiftLvl c) :=
  (eval_vapp_shiftLvl n).1 h

theorem vapp_shiftLvl {n unf c f a v}
    (h : vapp n unf f a = some v) :
    vapp n unf (f.shiftLvl c) (a.shiftLvl c) = some (v.shiftLvl c) :=
  (eval_vapp_shiftLvl n).2 h

/-!
### `eval` preserves `Val.levelsBelow`

If every entry of ρ has `levelsBelow d`, then `eval ρ e = some v`
implies `v.levelsBelow d`. Proved by induction on fuel.
-/

/-- Taking a prefix preserves envLevelsBelow. -/
theorem Closure.envLevelsBelow_take
    {d : Nat} {env : List Val} (h : Closure.envLevelsBelow d env) (n : Nat) :
    Closure.envLevelsBelow d (env.take n) := by
  induction env generalizing n with
  | nil => cases n <;> unfold Closure.envLevelsBelow <;> trivial
  | cons w ws ih =>
      cases n with
      | zero => unfold Closure.envLevelsBelow; trivial
      | succ m =>
          unfold Closure.envLevelsBelow at h
          simp only [List.take_succ_cons]
          unfold Closure.envLevelsBelow
          exact ⟨h.1, ih h.2 m⟩

/-- `envFullyQuotable` is preserved by `List.take`. -/
theorem Closure.envFullyQuotable_take
    {d : Nat} {env : List Val} (h : Closure.envFullyQuotable d env) (n : Nat) :
    Closure.envFullyQuotable d (env.take n) := by
  induction env generalizing n with
  | nil => cases n <;> unfold Closure.envFullyQuotable <;> trivial
  | cons w ws ih =>
      cases n with
      | zero => unfold Closure.envFullyQuotable; trivial
      | succ m =>
          unfold Closure.envFullyQuotable at h
          simp only [List.take_succ_cons]
          unfold Closure.envFullyQuotable
          exact ⟨h.1, ih h.2 m⟩

/-- From `envFullyQuotable`, get fullyQuotable + quote witness for a
specific entry. -/
theorem Closure.envFullyQuotable_getElem?
    {d : Nat} {env : List Val} (h : Closure.envFullyQuotable d env)
    {k : Nat} {v : Val} (hk : env[k]? = some v) :
    Val.fullyQuotable d v ∧ ∃ qe, quote fuelω d v = some qe := by
  induction env generalizing k with
  | nil => simp at hk
  | cons w ws ih =>
      unfold Closure.envFullyQuotable at h
      cases k with
      | zero =>
          simp only [List.getElem?_cons_zero, Option.some.injEq] at hk
          subst hk
          exact h.1
      | succ m =>
          simp only [List.getElem?_cons_succ] at hk
          exact ih h.2 hk

theorem eval_vapp_levelsBelow :
    ∀ n,
    (∀ {unf d ρ e v}, eval n unf ρ e = some v →
      Closure.envLevelsBelow d ρ → Val.levelsBelow d v) ∧
    (∀ {unf d f a v}, vapp n unf f a = some v →
      Val.levelsBelow d f → Val.levelsBelow d a → Val.levelsBelow d v) := by
  intro n
  induction n with
  | zero =>
    refine ⟨?_, ?_⟩
    · intros _ _ _ _ _ h; rw [eval_zero] at h; cases h
    · intros _ _ _ _ _ h; rw [vapp_zero] at h; cases h
  | succ k ih =>
    obtain ⟨ihe, ihv⟩ := ih
    refine ⟨?_, ?_⟩
    -- eval (k+1)
    · intro unf d ρ e v h hρ
      unfold eval at h
      cases e with
      | type =>
          simp only [Option.some.injEq] at h
          subst h
          unfold Val.levelsBelow; trivial
      | bvar j =>
          simp only [] at h
          exact Closure.envLevelsBelow_getElem? hρ h
      | lam dom body =>
          simp only [Option.bind_eq_bind, Option.bind_eq_some] at h
          obtain ⟨dom', hdom, hv⟩ := h
          simp only [Option.some.injEq] at hv
          subst hv
          unfold Val.levelsBelow
          refine ⟨ihe hdom hρ, ?_⟩
          unfold Closure.levelsBelow Closure.mk'
          exact Closure.envLevelsBelow_take hρ _
      | iota ann body =>
          simp only [Option.bind_eq_bind, Option.bind_eq_some] at h
          obtain ⟨ann', hann, hv⟩ := h
          simp only [Option.some.injEq] at hv
          subst hv
          unfold Val.levelsBelow
          refine ⟨ihe hann hρ, ?_⟩
          unfold Closure.levelsBelow Closure.mk'
          exact Closure.envLevelsBelow_take hρ _
      | «fix» ann body =>
          simp only [Option.bind_eq_bind, Option.bind_eq_some] at h
          obtain ⟨ann', hann, hv⟩ := h
          simp only [Option.some.injEq] at hv
          subst hv
          unfold Val.levelsBelow
          refine ⟨ihe hann hρ, ?_⟩
          unfold Closure.levelsBelow Closure.mk'
          exact Closure.envLevelsBelow_take hρ _
      | app f a =>
          simp only [Option.bind_eq_bind, Option.bind_eq_some] at h
          obtain ⟨f', hf, a', ha, hv⟩ := h
          exact ihv hv (ihe hf hρ) (ihe ha hρ)
      | letE val body =>
          simp only [Option.bind_eq_bind, Option.bind_eq_some] at h
          obtain ⟨v', hv', hb⟩ := h
          have hρ' : Closure.envLevelsBelow d (v' :: ρ) := by
            unfold Closure.envLevelsBelow
            exact ⟨ihe hv' hρ, hρ⟩
          exact ihe hb hρ'
      | asc t _ =>
          simp only [] at h
          exact ihe h hρ
    -- vapp (k+1)
    · intro unf d f a v h hf ha
      unfold vapp at h
      cases hfeq : f with
      | neutral nf =>
          subst hfeq
          simp only [Option.some.injEq] at h
          subst h
          unfold Val.levelsBelow Neutral.levelsBelow
          exact ⟨hf, ha⟩
      | type =>
          subst hfeq
          simp only [Option.some.injEq] at h
          subst h
          unfold Val.levelsBelow Neutral.levelsBelow
          exact ⟨hf, ha⟩
      | lam dom cl =>
          subst hfeq
          obtain ⟨body, env⟩ := cl
          simp only at h
          unfold Val.levelsBelow Closure.levelsBelow at hf
          have hρ' : Closure.envLevelsBelow d (a :: env) := by
            unfold Closure.envLevelsBelow
            exact ⟨ha, hf.2⟩
          exact ihe h hρ'
      | iota ann cl =>
          subst hfeq
          obtain ⟨body, env⟩ := cl
          simp only at h
          by_cases hg : (a.isNeutral || unf == 0) = true
          · simp only [hg, ↓reduceIte, Option.some.injEq] at h
            subst h
            unfold Val.levelsBelow Neutral.levelsBelow
            exact ⟨hf, ha⟩
          · simp only [hg, Bool.false_eq_true, ↓reduceIte,
                       Option.bind_eq_bind, Option.bind_eq_some] at h
            obtain ⟨f', hfe, hv⟩ := h
            unfold Val.levelsBelow Closure.levelsBelow at hf
            have hρ' : Closure.envLevelsBelow d
                (Val.iota ann ⟨body, env⟩ :: env) := by
              unfold Closure.envLevelsBelow
              refine ⟨?_, hf.2⟩
              unfold Val.levelsBelow
              exact ⟨hf.1, hf.2⟩
            exact ihv hv (ihe hfe hρ') ha
      | fix ann cl =>
          subst hfeq
          obtain ⟨body, env⟩ := cl
          simp only at h
          by_cases hg : (a.isNeutral || unf == 0) = true
          · simp only [hg, ↓reduceIte, Option.some.injEq] at h
            subst h
            unfold Val.levelsBelow Neutral.levelsBelow
            exact ⟨hf, ha⟩
          · simp only [hg, Bool.false_eq_true, ↓reduceIte,
                       Option.bind_eq_bind, Option.bind_eq_some] at h
            obtain ⟨f', hfe, hv⟩ := h
            unfold Val.levelsBelow Closure.levelsBelow at hf
            have hρ' : Closure.envLevelsBelow d
                (Val.«fix» ann ⟨body, env⟩ :: env) := by
              unfold Closure.envLevelsBelow
              refine ⟨?_, hf.2⟩
              unfold Val.levelsBelow
              exact ⟨hf.1, hf.2⟩
            exact ihv hv (ihe hfe hρ') ha

theorem eval_levelsBelow {n unf d ρ e v}
    (h : eval n unf ρ e = some v) (hρ : Closure.envLevelsBelow d ρ) :
    Val.levelsBelow d v :=
  (eval_vapp_levelsBelow n).1 h hρ

/-- **eval + vapp preserve Val.fullyQuotable**: mutual statement.
Takes quote witnesses for input `a` (for vapp's `.lam` head) and on
`f` (for `.iota`/`.fix` unfold). These quote witnesses are
supplied from the caller's chain via `eval_quotable_open`. -/
theorem eval_vapp_preserves_fullyQuotable :
    ∀ n,
    (∀ {unf d ρ e v}, eval n unf ρ e = some v →
      Closure.envFullyQuotable d ρ →
      e.closedAt ρ.length = true →
      Val.fullyQuotable d v) ∧
    (∀ {unf d f a v}, vapp n unf f a = some v →
      Val.fullyQuotable d f → Val.fullyQuotable d a →
      (∃ qf, quote fuelω d f = some qf) →
      (∃ qa, quote fuelω d a = some qa) →
      Val.fullyQuotable d v) := by
  intro n
  induction n with
  | zero =>
    refine ⟨?_, ?_⟩
    · intros _ _ _ _ _ h; rw [eval_zero] at h; cases h
    · intros _ _ _ _ _ h; rw [vapp_zero] at h; cases h
  | succ k ih =>
    obtain ⟨ihe, ihv⟩ := ih
    refine ⟨?_, ?_⟩
    · intro unf d ρ e v h hρ hcl
      unfold eval at h
      cases e with
      | type =>
          simp only [Option.some.injEq] at h
          subst h
          unfold Val.fullyQuotable; trivial
      | bvar j =>
          simp only [] at h
          have := Closure.envFullyQuotable_getElem? hρ h
          exact this.1
      | lam dom body =>
          simp only [Option.bind_eq_bind, Option.bind_eq_some] at h
          obtain ⟨dom', hdom, hv⟩ := h
          simp only [Option.some.injEq] at hv
          subst hv
          simp only [Expr.closedAt, Bool.and_eq_true] at hcl
          unfold Val.fullyQuotable
          refine ⟨ihe hdom hρ hcl.1, ?_⟩
          refine ⟨Closure.mk'_body_closed body ρ
                    (bvarBound_le_of_closedAt hcl.2), ?_⟩
          exact Closure.envFullyQuotable_take hρ _
      | iota ann body =>
          simp only [Option.bind_eq_bind, Option.bind_eq_some] at h
          obtain ⟨ann', hann, hv⟩ := h
          simp only [Option.some.injEq] at hv
          subst hv
          simp only [Expr.closedAt, Bool.and_eq_true] at hcl
          unfold Val.fullyQuotable
          refine ⟨ihe hann hρ hcl.1, ?_⟩
          refine ⟨Closure.mk'_body_closed body ρ
                    (bvarBound_le_of_closedAt hcl.2), ?_⟩
          exact Closure.envFullyQuotable_take hρ _
      | «fix» ann body =>
          simp only [Option.bind_eq_bind, Option.bind_eq_some] at h
          obtain ⟨ann', hann, hv⟩ := h
          simp only [Option.some.injEq] at hv
          subst hv
          simp only [Expr.closedAt, Bool.and_eq_true] at hcl
          unfold Val.fullyQuotable
          refine ⟨ihe hann hρ hcl.1, ?_⟩
          refine ⟨Closure.mk'_body_closed body ρ
                    (bvarBound_le_of_closedAt hcl.2), ?_⟩
          exact Closure.envFullyQuotable_take hρ _
      | app f a =>
          -- vapp case: need quote witnesses on f, a. Not derivable
          -- from envFullyQuotable alone. DEFERRED — requires threading
          -- hnfq hypothesis to obtain quote witnesses on intermediate
          -- vals.
          sorry
      | letE val body =>
          -- letE extends env: need (eval val) to have fullyQuotable
          -- AND quote witness. Fullyquotable from ihe, but quote witness
          -- not directly available. Same issue as .app.
          sorry
      | asc t _ =>
          simp only [] at h
          simp only [Expr.closedAt, Bool.and_eq_true] at hcl
          exact ihe h hρ hcl.1
    · intro unf d f a v h hf ha hqf hqa
      -- vapp cases
      unfold vapp at h
      cases hfeq : f with
      | neutral nf =>
          subst hfeq
          simp only [Option.some.injEq] at h
          subst h
          unfold Val.fullyQuotable Neutral.fullyQuotable
          exact ⟨hf, ha⟩
      | type =>
          subst hfeq
          simp only [Option.some.injEq] at h
          subst h
          unfold Val.fullyQuotable Neutral.fullyQuotable
          exact ⟨hf, ha⟩
      | lam dom cl =>
          subst hfeq
          have hf' := hf
          unfold Val.fullyQuotable at hf'
          obtain ⟨_hfdom, hfcl⟩ := hf'
          -- Unwrap the Closure structure to expose body/env.
          cases hcleq : cl with
          | mk body env =>
            subst hcleq
            unfold Closure.fullyQuotable at hfcl
            obtain ⟨hfbody, hfenv⟩ := hfcl
            -- vapp = eval k unf (a :: env) body
            have hρ' : Closure.envFullyQuotable d (a :: env) := by
              unfold Closure.envFullyQuotable
              exact ⟨⟨ha, hqa⟩, hfenv⟩
            have hcl' : body.closedAt ((a :: env).length) = true := by
              simp only [List.length_cons]; exact hfbody
            exact ihe h hρ' hcl'
      | iota ann cl =>
          subst hfeq
          cases hcleq : cl with
          | mk body env =>
            subst hcleq
            by_cases hng : a.isNeutral || unf == 0
            · simp only [hng, ↓reduceIte, Option.some.injEq] at h
              subst h
              unfold Val.fullyQuotable Neutral.fullyQuotable
              exact ⟨hf, ha⟩
            · -- Unfold branch: recursive vapp on eval-produced `f'`
              -- requires quote witness on `f'` (not available from
              -- eval alone). Deferred.
              sorry
      | fix ann cl =>
          subst hfeq
          cases hcleq : cl with
          | mk body env =>
            subst hcleq
            by_cases hng : a.isNeutral || unf == 0
            · simp only [hng, ↓reduceIte, Option.some.injEq] at h
              subst h
              unfold Val.fullyQuotable Neutral.fullyQuotable
              exact ⟨hf, ha⟩
            · sorry

/-- Specialisation for push_let: given hρ's envFullyQuotable, eval
preserves fullyQuotable on val result. -/
theorem eval_preserves_fullyQuotable {n unf d ρ e v}
    (heval : eval n unf ρ e = some v)
    (hρ : Closure.envFullyQuotable d ρ)
    (hcl : e.closedAt ρ.length = true) :
    Val.fullyQuotable d v :=
  (eval_vapp_preserves_fullyQuotable n).1 heval hρ hcl

/-- Convert per-entry `hρq` + `hρfq` hypotheses into `envFullyQuotable`. -/
theorem Closure.envFullyQuotable_of_getElem? {d : Nat} {ρ : List Val}
    (hρq : ∀ (k : Nat) (v : Val), ρ[k]? = some v →
           ∃ qe, quote fuelω d v = some qe)
    (hρfq : ∀ (k : Nat) (v : Val), ρ[k]? = some v →
            Val.fullyQuotable d v) :
    Closure.envFullyQuotable d ρ := by
  induction ρ with
  | nil => unfold Closure.envFullyQuotable; trivial
  | cons v vs ih =>
    unfold Closure.envFullyQuotable
    refine ⟨⟨hρfq 0 v ?_, hρq 0 v ?_⟩, ih ?_ ?_⟩
    · simp
    · simp
    · intro k w hk; exact hρq (k+1) w (by simpa using hk)
    · intro k w hk; exact hρfq (k+1) w (by simpa using hk)

mutual
/-- Monotonicity of levelsBelow/envLevelsBelow. -/
theorem Val.levelsBelow_mono {d d' : Nat} (hle : d ≤ d') :
    ∀ v, Val.levelsBelow d v → Val.levelsBelow d' v
  | .type, _ => by unfold Val.levelsBelow; trivial
  | .neutral n, h => by
      unfold Val.levelsBelow at h ⊢
      exact Neutral.levelsBelow_mono hle n h
  | .lam dom cl, h => by
      unfold Val.levelsBelow at h ⊢
      refine ⟨Val.levelsBelow_mono hle dom h.1, ?_⟩
      exact Closure.levelsBelow_mono hle cl h.2
  | .iota ann cl, h => by
      unfold Val.levelsBelow at h ⊢
      refine ⟨Val.levelsBelow_mono hle ann h.1, ?_⟩
      exact Closure.levelsBelow_mono hle cl h.2
  | .«fix» ann cl, h => by
      unfold Val.levelsBelow at h ⊢
      refine ⟨Val.levelsBelow_mono hle ann h.1, ?_⟩
      exact Closure.levelsBelow_mono hle cl h.2

theorem Neutral.levelsBelow_mono {d d' : Nat} (hle : d ≤ d') :
    ∀ n, Neutral.levelsBelow d n → Neutral.levelsBelow d' n
  | .var k, h => by
      unfold Neutral.levelsBelow at h ⊢
      omega
  | .app n' v, h => by
      unfold Neutral.levelsBelow at h ⊢
      exact ⟨Neutral.levelsBelow_mono hle n' h.1,
             Val.levelsBelow_mono hle v h.2⟩
  | .stuckRec f a, h => by
      unfold Neutral.levelsBelow at h ⊢
      exact ⟨Val.levelsBelow_mono hle f h.1,
             Val.levelsBelow_mono hle a h.2⟩

theorem Closure.levelsBelow_mono {d d' : Nat} (hle : d ≤ d') :
    ∀ cl, Closure.levelsBelow d cl → Closure.levelsBelow d' cl
  | ⟨_body, env⟩, h => by
      unfold Closure.levelsBelow at h ⊢
      exact Closure.envLevelsBelow_mono hle env h

theorem Closure.envLevelsBelow_mono {d d' : Nat} (hle : d ≤ d') :
    ∀ env, Closure.envLevelsBelow d env →
           Closure.envLevelsBelow d' env
  | [], _ => by unfold Closure.envLevelsBelow; trivial
  | w :: ws, h => by
      unfold Closure.envLevelsBelow at h ⊢
      exact ⟨Val.levelsBelow_mono hle w h.1,
             Closure.envLevelsBelow_mono hle ws h.2⟩
end

/-!
### Cutoff-parametrised depth shift for `quote`

A one-step quote-depth-shift, but generalised with a cutoff `c`
on the expression-level shift so the closure case's body
(recursing one binder deeper) can cleanly pass a larger cutoff.

At `c = 0`: the Val shift `v.shiftLvl (d-0) = v.shiftLvl d` is a
no-op whenever `v.levelsBelow d` holds (true for any `v` coming
out of a successful `quote n d v = some _`), so the shape reduces
to `quote (d+1) v = some (e.shift 1 0)` — the existing
`quote_depth_shift`.

At `c+1` (used inside the closure body, one binder deeper): the
recursive IH supplies `quote (d+2) (v.shiftLvl (d-c)) =
some (e.shift 1 (c+1))`, exactly matching the post-`eval_shiftLvl`
body state.

Proof is by induction on fuel, combined over the three quote
families. -/
theorem quote_quoteClosure_quoteNeutral_depth_shift :
    ∀ n,
    (∀ {c d v e}, c ≤ d → quote n d v = some e →
        quote n (d+1) (v.shiftLvl (d-c)) = some (e.shift 1 c)) ∧
    (∀ {c d cl e}, c ≤ d → quoteClosure n d cl = some e →
        quoteClosure n (d+1) (cl.shiftLvl (d-c))
          = some (e.shift 1 (c+1))) ∧
    (∀ {c d ne e}, c ≤ d → quoteNeutral n d ne = some e →
        quoteNeutral n (d+1) (ne.shiftLvl (d-c))
          = some (e.shift 1 c)) := by
  intro n
  induction n with
  | zero =>
    refine ⟨?_, ?_, ?_⟩
    · intro _ _ _ _ _ h; rw [quote_zero] at h; cases h
    · intro _ _ _ _ _ h; rw [quoteClosure_zero] at h; cases h
    · intro _ _ _ _ _ h; rw [quoteNeutral_zero] at h; cases h
  | succ n ih =>
    obtain ⟨ihq, ihc, ihne⟩ := ih
    refine ⟨?_, ?_, ?_⟩
    -- quote
    · intro c d v e hle h
      unfold quote at h
      cases v with
      | type =>
          simp only [Option.some.injEq] at h
          subst h
          unfold Val.shiftLvl quote
          rfl
      | neutral ne =>
          unfold Val.shiftLvl quote
          exact ihne hle h
      | lam dom cl =>
          simp only [Option.bind_eq_bind, Option.bind_eq_some,
                     Option.some.injEq] at h
          obtain ⟨dom', hdom, body', hbody, he⟩ := h
          subst he
          unfold Val.shiftLvl quote
          simp only [Option.bind_eq_bind, Option.bind_eq_some,
                     Option.some.injEq]
          refine ⟨dom'.shift 1 c, ihq hle hdom,
                  body'.shift 1 (c+1), ihc hle hbody, ?_⟩
          rfl
      | iota ann cl =>
          simp only [Option.bind_eq_bind, Option.bind_eq_some,
                     Option.some.injEq] at h
          obtain ⟨ann', hann, body', hbody, he⟩ := h
          subst he
          unfold Val.shiftLvl quote
          simp only [Option.bind_eq_bind, Option.bind_eq_some,
                     Option.some.injEq]
          refine ⟨ann'.shift 1 c, ihq hle hann,
                  body'.shift 1 (c+1), ihc hle hbody, ?_⟩
          rfl
      | «fix» ann cl =>
          simp only [Option.bind_eq_bind, Option.bind_eq_some,
                     Option.some.injEq] at h
          obtain ⟨ann', hann, body', hbody, he⟩ := h
          subst he
          unfold Val.shiftLvl quote
          simp only [Option.bind_eq_bind, Option.bind_eq_some,
                     Option.some.injEq]
          refine ⟨ann'.shift 1 c, ihq hle hann,
                  body'.shift 1 (c+1), ihc hle hbody, ?_⟩
          rfl
    -- quoteClosure
    · intro c d cl e hle h
      -- unfold quoteClosure; get eval + inner quote
      unfold quoteClosure at h
      simp only [Option.bind_eq_bind, Option.bind_eq_some] at h
      obtain ⟨v, hev, hq⟩ := h
      -- Apply eval_shiftLvl with cutoff (d - c)
      have hev' :
          eval n 1
            ((Val.neutral (.var d) :: cl.env).map
              (Val.shiftLvl (d - c)))
            cl.body = some (v.shiftLvl (d - c)) :=
        eval_shiftLvl hev
      -- Rewrite the mapped env into the shifted closure env
      -- plus the shifted fresh head `.var (d+1)`.
      have hfresh : (Val.neutral (.var d)).shiftLvl (d - c) =
                    Val.neutral (.var (d + 1)) := by
        unfold Val.shiftLvl Neutral.shiftLvl
        have : ¬ d < d - c := by omega
        simp [this]
      have henvmap :
          cl.env.map (Val.shiftLvl (d - c))
            = (cl.shiftLvl (d - c)).env := by
        obtain ⟨body, env⟩ := cl
        unfold Closure.shiftLvl
        simp [Closure.envShiftLvl_eq_map]
      -- body of shifted closure equals original body
      have hbody : (cl.shiftLvl (d - c)).body = cl.body := by
        obtain ⟨body, env⟩ := cl; unfold Closure.shiftLvl; rfl
      -- Assemble the new quoteClosure at depth d+1
      unfold quoteClosure
      simp only [Option.bind_eq_bind, Option.bind_eq_some]
      refine ⟨v.shiftLvl (d - c), ?_, ?_⟩
      · -- eval: rewrite to the shifted closure's env + fresh (d+1)
        have heq :
            (Val.neutral (.var d) :: cl.env).map
              (Val.shiftLvl (d - c))
            = Val.neutral (.var (d+1))
                :: (cl.shiftLvl (d-c)).env := by
          rw [List.map_cons, hfresh, henvmap]
        rw [heq] at hev'
        rw [hbody]
        exact hev'
      · -- quote at depth (d+1)+1 = d+2, cutoff (c+1)
        have hle' : c + 1 ≤ d + 1 := Nat.succ_le_succ hle
        have hsub : (d + 1) - (c + 1) = d - c := by omega
        have := ihq (c := c + 1) (d := d + 1) hle' hq
        rw [hsub] at this
        exact this
    -- quoteNeutral
    · intro c d ne e hle h
      unfold quoteNeutral at h
      cases ne with
      | var k =>
          simp only [] at h
          split at h
          · next hk =>
              simp only [Option.some.injEq] at h
              subst h
              -- Case: k < d → e = .bvar (d-1-k)
              unfold Neutral.shiftLvl quoteNeutral
              by_cases hkc : k < d - c
              · -- k < d - c: .var k unchanged;
                -- bvar (d-1-k) ≥ c so shift adds 1.
                simp only [hkc, if_true]
                have hklt : k < d + 1 := Nat.lt_succ_of_lt hk
                simp only [hklt, if_true]
                -- Goal: some (.bvar (d+1-1-k)) = some ((.bvar (d-1-k)).shift 1 c)
                -- (.bvar (d-1-k)).shift 1 c: since d-1-k ≥ c, → .bvar (d-k).
                show some (Expr.bvar (d + 1 - 1 - k))
                   = some ((Expr.bvar (d - 1 - k)).shift 1 c)
                have hge : ¬ d - 1 - k < c := by omega
                show some (Expr.bvar (d + 1 - 1 - k))
                   = some (if d - 1 - k < c then Expr.bvar (d - 1 - k)
                           else Expr.bvar (d - 1 - k + 1))
                rw [if_neg hge]
                congr 2; omega
              · -- k ≥ d - c: .var k → .var (k+1);
                -- bvar (d-1-k) < c so shift unchanged.
                simp only [hkc, if_false]
                have hklt : k + 1 < d + 1 := Nat.succ_lt_succ hk
                simp only [hklt, if_true]
                show some (Expr.bvar (d + 1 - 1 - (k + 1)))
                   = some ((Expr.bvar (d - 1 - k)).shift 1 c)
                have hlt : d - 1 - k < c := by omega
                show some (Expr.bvar (d + 1 - 1 - (k + 1)))
                   = some (if d - 1 - k < c then Expr.bvar (d - 1 - k)
                           else Expr.bvar (d - 1 - k + 1))
                rw [if_pos hlt]
                congr 2; omega
          · cases h
      | app n' v =>
          simp only [Option.bind_eq_bind, Option.bind_eq_some,
                     Option.some.injEq] at h
          obtain ⟨f', hf, a', ha, he⟩ := h
          subst he
          unfold Neutral.shiftLvl quoteNeutral
          simp only [Option.bind_eq_bind, Option.bind_eq_some,
                     Option.some.injEq]
          refine ⟨f'.shift 1 c, ihne hle hf,
                  a'.shift 1 c, ihq hle ha, ?_⟩
          rfl
      | stuckRec f a =>
          simp only [Option.bind_eq_bind, Option.bind_eq_some,
                     Option.some.injEq] at h
          obtain ⟨f', hf, a', ha, he⟩ := h
          subst he
          unfold Neutral.shiftLvl quoteNeutral
          simp only [Option.bind_eq_bind, Option.bind_eq_some,
                     Option.some.injEq]
          refine ⟨f'.shift 1 c, ihq hle hf,
                  a'.shift 1 c, ihq hle ha, ?_⟩
          rfl

/-- One-step `quote_depth_shift` (cutoff c = 0), specialised to
take `Val.levelsBelow d v` as a side condition so the Val shift
collapses to the identity. The side condition is discharged by
callers via `eval_levelsBelow`. -/
theorem quote_depth_shift_of_levelsBelow {fuel d v e}
    (hlvl : Val.levelsBelow d v)
    (hq : quote fuel d v = some e) :
    quote fuel (d+1) v = some (e.shift 1 0) := by
  have hle : (0 : Nat) ≤ d := Nat.zero_le _
  have hsub : d - 0 = d := Nat.sub_zero d
  have hgen :=
    (quote_quoteClosure_quoteNeutral_depth_shift fuel).1 hle hq
  rw [hsub] at hgen
  rwa [Val.shiftLvl_of_levelsBelow v d hlvl] at hgen

/-- **Closed form** of `quote_depth_shift`: with a
`Val.levelsBelow d v` witness, quoting at deeper depth `d+1`
produces the shifted expression. The levelsBelow witness is
discharged at callers via the `OpenCtx.hρlvl` invariant (which
is in turn maintained across `push_*` via `eval_levelsBelow`).

Delegates to `quote_depth_shift_of_levelsBelow`. -/
theorem quote_depth_shift {d v e}
    (hlvl : Val.levelsBelow d v)
    (hq : quote fuelω d v = some e) :
    quote fuelω (d + 1) v = some (e.shift 1 0) :=
  quote_depth_shift_of_levelsBelow hlvl hq

/-- N-step depth shift: `quote fuelω d v = e` and `d ≤ d'` gives
`quote fuelω d' v = e.shift (d'-d) 0`. By induction on `d'-d`,
each step applying `quote_depth_shift` at the intermediate depth.
Used in `OpenCtx.hρq_lift` + `Subtype'.bvar` bridge: relates
`QuotesCtx`'s per-entry depth `k` to the goal's outer depth
`Γ.size`, where the gap is exactly the `Subtype'.bvar`
shift amount. Moved here 2026-04-22 for Tier 0 refactor. -/
theorem quote_depth_shift_n {k d v e}
    (hlvl : Val.levelsBelow k v)
    (hle : k ≤ d) (hq : quote fuelω k v = some e) :
    quote fuelω d v = some (e.shift (d - k) 0) := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le hle
  simp only [Nat.add_sub_cancel_left]
  clear hle
  induction n with
  | zero => simp only [Nat.add_zero, Expr.shift_zero]; exact hq
  | succ m ih =>
      have hlvl_m : Val.levelsBelow (k + m) v :=
        Val.levelsBelow_mono (by omega) v hlvl
      have h1 := quote_depth_shift hlvl_m ih
      rw [Expr.shift_shift_same, Nat.add_comm 1 m] at h1
      exact h1

-- `Val.levelsBelow_of_fullyQuotable`: fullyQuotable implies
-- levelsBelow at the same depth. Moved here (before R_depth_lift)
-- 2026-04-22 for Tier 0 refactor.
mutual
theorem Val.levelsBelow_of_fullyQuotable : ∀ (d : Nat) (v : Val),
    Val.fullyQuotable d v → Val.levelsBelow d v
  | _, .type, _ => by unfold Val.levelsBelow; trivial
  | d, .neutral n, h => by
      unfold Val.fullyQuotable at h
      unfold Val.levelsBelow
      exact Neutral.levelsBelow_of_fullyQuotable d n h
  | d, .lam dom cl, h => by
      unfold Val.fullyQuotable at h
      unfold Val.levelsBelow
      exact ⟨Val.levelsBelow_of_fullyQuotable d dom h.1,
             Closure.levelsBelow_of_fullyQuotable d cl h.2⟩
  | d, .iota ann cl, h => by
      unfold Val.fullyQuotable at h
      unfold Val.levelsBelow
      exact ⟨Val.levelsBelow_of_fullyQuotable d ann h.1,
             Closure.levelsBelow_of_fullyQuotable d cl h.2⟩
  | d, .«fix» ann cl, h => by
      unfold Val.fullyQuotable at h
      unfold Val.levelsBelow
      exact ⟨Val.levelsBelow_of_fullyQuotable d ann h.1,
             Closure.levelsBelow_of_fullyQuotable d cl h.2⟩

theorem Neutral.levelsBelow_of_fullyQuotable : ∀ (d : Nat) (n : Neutral),
    Neutral.fullyQuotable d n → Neutral.levelsBelow d n
  | _, .var _, h => by unfold Neutral.fullyQuotable at h; unfold Neutral.levelsBelow; exact h
  | d, .app n v, h => by
      unfold Neutral.fullyQuotable at h; unfold Neutral.levelsBelow
      exact ⟨Neutral.levelsBelow_of_fullyQuotable d n h.1,
             Val.levelsBelow_of_fullyQuotable d v h.2⟩
  | d, .stuckRec f a, h => by
      unfold Neutral.fullyQuotable at h; unfold Neutral.levelsBelow
      exact ⟨Val.levelsBelow_of_fullyQuotable d f h.1,
             Val.levelsBelow_of_fullyQuotable d a h.2⟩

theorem Closure.levelsBelow_of_fullyQuotable : ∀ (d : Nat) (cl : Closure),
    Closure.fullyQuotable d cl → Closure.levelsBelow d cl
  | d, ⟨_body, env⟩, h => by
      unfold Closure.fullyQuotable at h; unfold Closure.levelsBelow
      exact Closure.envLevelsBelow_of_envFullyQuotable d env h.2

theorem Closure.envLevelsBelow_of_envFullyQuotable : ∀ (d : Nat) (env : List Val),
    Closure.envFullyQuotable d env → Closure.envLevelsBelow d env
  | _, [], _ => by unfold Closure.envLevelsBelow; trivial
  | d, v :: vs, h => by
      unfold Closure.envFullyQuotable at h; unfold Closure.envLevelsBelow
      exact ⟨Val.levelsBelow_of_fullyQuotable d v h.1.1,
             Closure.envLevelsBelow_of_envFullyQuotable d vs h.2⟩
end

-- Monotonicity of fullyQuotable in depth: a Val fully-quotable at d
-- is also fully-quotable at any d' ≥ d. Quote witnesses at d' are
-- derived from witnesses at d via quote_depth_shift_n. Moved here
-- (before R_depth_lift) 2026-04-22 for Tier 0 refactor.
mutual
theorem Val.fullyQuotable_mono : ∀ {d d' : Nat}, d ≤ d' →
    ∀ (v : Val), Val.fullyQuotable d v → Val.fullyQuotable d' v
  | _, _, _, .type, _ => by unfold Val.fullyQuotable; trivial
  | _, _, hle, .neutral n, h => by
      unfold Val.fullyQuotable at h ⊢
      exact Neutral.fullyQuotable_mono hle n h
  | _, _, hle, .lam dom cl, h => by
      unfold Val.fullyQuotable at h ⊢
      exact ⟨Val.fullyQuotable_mono hle dom h.1,
             Closure.fullyQuotable_mono hle cl h.2⟩
  | _, _, hle, .iota ann cl, h => by
      unfold Val.fullyQuotable at h ⊢
      exact ⟨Val.fullyQuotable_mono hle ann h.1,
             Closure.fullyQuotable_mono hle cl h.2⟩
  | _, _, hle, .«fix» ann cl, h => by
      unfold Val.fullyQuotable at h ⊢
      exact ⟨Val.fullyQuotable_mono hle ann h.1,
             Closure.fullyQuotable_mono hle cl h.2⟩

theorem Neutral.fullyQuotable_mono : ∀ {d d' : Nat}, d ≤ d' →
    ∀ (n : Neutral), Neutral.fullyQuotable d n → Neutral.fullyQuotable d' n
  | _, _, hle, .var k, h => by
      unfold Neutral.fullyQuotable at h ⊢; omega
  | _, _, hle, .app n v, h => by
      unfold Neutral.fullyQuotable at h ⊢
      exact ⟨Neutral.fullyQuotable_mono hle n h.1,
             Val.fullyQuotable_mono hle v h.2⟩
  | _, _, hle, .stuckRec f a, h => by
      unfold Neutral.fullyQuotable at h ⊢
      exact ⟨Val.fullyQuotable_mono hle f h.1,
             Val.fullyQuotable_mono hle a h.2⟩

theorem Closure.fullyQuotable_mono : ∀ {d d' : Nat}, d ≤ d' →
    ∀ (cl : Closure), Closure.fullyQuotable d cl → Closure.fullyQuotable d' cl
  | _, _, hle, ⟨_body, env⟩, h => by
      unfold Closure.fullyQuotable at h ⊢
      exact ⟨h.1, Closure.envFullyQuotable_mono hle env h.2⟩

theorem Closure.envFullyQuotable_mono : ∀ {d d' : Nat}, d ≤ d' →
    ∀ (env : List Val), Closure.envFullyQuotable d env →
      Closure.envFullyQuotable d' env
  | _, _, _, [], _ => by unfold Closure.envFullyQuotable; trivial
  | d, d', hle, v :: vs, h => by
      unfold Closure.envFullyQuotable at h ⊢
      obtain ⟨⟨hvfq, qe, hqe⟩, htail⟩ := h
      refine ⟨⟨Val.fullyQuotable_mono hle v hvfq, ?_⟩,
              Closure.envFullyQuotable_mono hle vs htail⟩
      have hlvl : Val.levelsBelow d v :=
        Val.levelsBelow_of_fullyQuotable d v hvfq
      exact ⟨qe.shift (d' - d) 0, quote_depth_shift_n (d := d') hlvl hle hqe⟩
end

mutual

/-- **Depth-lift of R** with `Val.levelsBelow d v` side
condition. After the R/Equiv_c refactor (commit b5f0fd8), R's
clauses carry `Equiv_c d`, which admits a `shift` to `Equiv_c (d+1)`
without any closedness assumption.

Cases:
- `.type`/`.neutral`: base conjunct `∀ qe' hq', Equiv_c d qe' e`.
  At d+1, quote produces `qe'.shift 1 0` via `quote_depth_shift`,
  and `Equiv_c.shift` lifts `Equiv_c d qe' e` to
  `Equiv_c (d+1) (qe'.shift 1 0) (e.shift 1 0)`.
- `.lam`/`.iota`/`.fix`: env-exposes existentials lift via recursion
  on the head `R` (smaller `sizeOf v`), `RList_depth_lift` for the
  body env, and `Equiv_c.shift` for the final conjunct — modulo
  a substEnv-shift commutation lemma to match the target shape
  (currently still sorry for closure cases; see helper below). -/
theorem R_depth_lift {n d v e}
    {qe : Expr} (hlvl : Val.levelsBelow d v)
    (hfq : Val.fullyQuotable d v)
    (hq : quote fuelω d v = some qe)
    (h : R n d v e) :
    R n (d + 1) v (e.shift 1 0) := by
  match n, v, hlvl, hfq, hq, h with
  | 0, _, _, _, _, _ => unfold R; trivial
  | k+1, .type, _, _, _, h =>
      unfold R at h ⊢
      intro qe'' hq''
      have hqt : quote fuelω (d+1) Val.type = some Expr.type := by
        have hf : fuelω = (fuelω - 1) + 1 := rfl
        rw [hf]; unfold quote; rfl
      have hqd : quote fuelω d Val.type = some Expr.type := by
        have hf : fuelω = (fuelω - 1) + 1 := rfl
        rw [hf]; unfold quote; rfl
      rw [hqt] at hq''
      cases hq''
      have h' : Equiv_c d Expr.type e := h Expr.type hqd
      intro S Γe hd
      obtain ⟨hab, hba⟩ := Equiv_c.shift h' hd
      exact ⟨hab, hba⟩
  | k+1, .neutral nN, hlvl, _, hq, h =>
      unfold R at h ⊢
      intro qe'' hq''
      have hshifted := quote_depth_shift_of_levelsBelow hlvl hq
      have heq : qe'' = qe.shift 1 0 := by
        rw [hshifted] at hq''
        exact Option.some.inj hq''.symm
      subst heq
      have h' : Equiv_c d qe e := h qe hq
      intro S Γe hd
      obtain ⟨hab, hba⟩ := Equiv_c.shift h' hd
      exact ⟨hab, hba⟩
  | k+1, .lam dV cl, hlvl, hfq, hq, h =>
      have hfq_dV : Val.fullyQuotable d dV := by
        unfold Val.fullyQuotable at hfq; exact hfq.1
      have hfq_cl : Closure.envFullyQuotable d cl.env := by
        unfold Val.fullyQuotable Closure.fullyQuotable at hfq
        obtain ⟨_, hfq2⟩ := hfq
        cases cl with | _ => exact hfq2.2
      have hlvl_dV : Val.levelsBelow d dV := by
        unfold Val.levelsBelow at hlvl; exact hlvl.1
      have hlvl_cl : Closure.envLevelsBelow d cl.env := by
        unfold Val.levelsBelow at hlvl
        obtain ⟨_, hlvl2⟩ := hlvl
        cases cl with | _ => exact hlvl2
      unfold R at h
      obtain ⟨ρe', dome, hRd, hRL, hclb, heqL⟩ := h
      have hfω_eq : fuelω = (fuelω - 1) + 1 := rfl
      rw [hfω_eq] at hq
      unfold quote at hq
      simp only [Option.bind_eq_bind, Option.bind_eq_some,
                 Option.some.injEq] at hq
      obtain ⟨dom', hdom', _body', _hbody', _⟩ := hq
      have hdom'_ω : quote fuelω d dV = some dom' :=
        quote_fuel_mono (by omega) hdom'
      have hRd' : R (k+1) (d+1) dV (dome.shift 1 0) :=
        R_depth_lift hlvl_dV hfq_dV hdom'_ω hRd
      have hRL' : RList (k+1) (d+1) cl.env (ρe'.map (·.shift 1 0)) :=
        RList_depth_lift hlvl_cl hfq_cl hRL
      have hclb' :
          cl.body.closedAt ((ρe'.map (·.shift 1 0)).length + 1) = true := by
        rw [List.length_map]; exact hclb
      have heqL' : Equiv_c (d+1) (e.shift 1 0)
          ((Expr.lam dome
            (cl.body.substEnv (.bvar 0 :: ρe'.map (·.shift 1 0)))).shift 1 0) :=
        Equiv_c.shift heqL
      have hsubst_comm :
          (cl.body.substEnv (.bvar 0 :: ρe'.map (·.shift 1 0))).shift 1 1
          = cl.body.substEnv
              ((.bvar 0 :: ρe'.map (·.shift 1 0)).map (·.shift 1 1)) := by
        apply substEnv_shift_comm
        simp [List.length_map]; exact hclb
      have htail_eq : (.bvar 0 :: ρe'.map (·.shift 1 0)).map (·.shift 1 1)
          = .bvar 0 :: (ρe'.map (·.shift 1 0)).map (·.shift 1 0) := by
        simp only [List.map_cons, Expr.shift, decide_eq_true_eq, Nat.lt_one_iff,
                   ↓reduceIte]
        congr 1
        rw [List.map_map, List.map_map]
        apply List.map_congr_left
        intro e _he
        simp only [Function.comp]
        have := Expr.shift_shift_comm_gen e 1 0 1
        simpa using this
      unfold R
      refine ⟨ρe'.map (·.shift 1 0), dome.shift 1 0,
              hRd', hRL', hclb', ?_⟩
      have target_rewrite :
          (Expr.lam dome
            (cl.body.substEnv (.bvar 0 :: ρe'.map (·.shift 1 0)))).shift 1 0
          = Expr.lam (dome.shift 1 0)
              (cl.body.substEnv
                (.bvar 0 :: (ρe'.map (·.shift 1 0)).map (·.shift 1 0))) := by
        show Expr.lam (dome.shift 1 0)
            ((cl.body.substEnv (.bvar 0 :: ρe'.map (·.shift 1 0))).shift 1 1)
          = Expr.lam (dome.shift 1 0) _
        congr 1
        rw [hsubst_comm, htail_eq]
      rw [target_rewrite] at heqL'
      intro S Γ hd
      exact heqL' hd
  | k+1, .iota aV cl, hlvl, hfq, hq, h =>
      have hfq_aV : Val.fullyQuotable d aV := by
        unfold Val.fullyQuotable at hfq; exact hfq.1
      have hfq_cl : Closure.envFullyQuotable d cl.env := by
        unfold Val.fullyQuotable Closure.fullyQuotable at hfq
        obtain ⟨_, hfq2⟩ := hfq
        cases cl with | _ => exact hfq2.2
      have hlvl_aV : Val.levelsBelow d aV := by
        unfold Val.levelsBelow at hlvl; exact hlvl.1
      have hlvl_cl : Closure.envLevelsBelow d cl.env := by
        unfold Val.levelsBelow at hlvl
        obtain ⟨_, hlvl2⟩ := hlvl
        cases cl with | _ => exact hlvl2
      unfold R at h
      obtain ⟨ρe', anne, hRa, hRL, hclb, heqI⟩ := h
      have hfω_eq : fuelω = (fuelω - 1) + 1 := rfl
      rw [hfω_eq] at hq
      unfold quote at hq
      simp only [Option.bind_eq_bind, Option.bind_eq_some,
                 Option.some.injEq] at hq
      obtain ⟨ann', hann', _body', _hbody', _⟩ := hq
      have hann'_ω : quote fuelω d aV = some ann' :=
        quote_fuel_mono (by omega) hann'
      have hRa' : R (k+1) (d+1) aV (anne.shift 1 0) :=
        R_depth_lift hlvl_aV hfq_aV hann'_ω hRa
      have hRL' : RList (k+1) (d+1) cl.env (ρe'.map (·.shift 1 0)) :=
        RList_depth_lift hlvl_cl hfq_cl hRL
      have hclb' :
          cl.body.closedAt ((ρe'.map (·.shift 1 0)).length + 1) = true := by
        rw [List.length_map]; exact hclb
      have heqI' : Equiv_c (d+1) (e.shift 1 0)
          ((Expr.iota anne
            (cl.body.substEnv (.bvar 0 :: ρe'.map (·.shift 1 0)))).shift 1 0) :=
        Equiv_c.shift heqI
      have hsubst_comm :
          (cl.body.substEnv (.bvar 0 :: ρe'.map (·.shift 1 0))).shift 1 1
          = cl.body.substEnv
              ((.bvar 0 :: ρe'.map (·.shift 1 0)).map (·.shift 1 1)) := by
        apply substEnv_shift_comm
        simp [List.length_map]; exact hclb
      have htail_eq : (.bvar 0 :: ρe'.map (·.shift 1 0)).map (·.shift 1 1)
          = .bvar 0 :: (ρe'.map (·.shift 1 0)).map (·.shift 1 0) := by
        simp only [List.map_cons, Expr.shift, decide_eq_true_eq, Nat.lt_one_iff,
                   ↓reduceIte]
        congr 1
        rw [List.map_map, List.map_map]
        apply List.map_congr_left
        intro e _he
        simp only [Function.comp]
        have := Expr.shift_shift_comm_gen e 1 0 1
        simpa using this
      unfold R
      refine ⟨ρe'.map (·.shift 1 0), anne.shift 1 0,
              hRa', hRL', hclb', ?_⟩
      have target_rewrite :
          (Expr.iota anne
            (cl.body.substEnv (.bvar 0 :: ρe'.map (·.shift 1 0)))).shift 1 0
          = Expr.iota (anne.shift 1 0)
              (cl.body.substEnv
                (.bvar 0 :: (ρe'.map (·.shift 1 0)).map (·.shift 1 0))) := by
        show Expr.iota (anne.shift 1 0) _ = Expr.iota (anne.shift 1 0) _
        congr 1
        rw [hsubst_comm, htail_eq]
      rw [target_rewrite] at heqI'
      intro S Γ hd
      exact heqI' hd
  | k+1, .«fix» aV cl, hlvl, hfq, hq, h =>
      have hfq_aV : Val.fullyQuotable d aV := by
        unfold Val.fullyQuotable at hfq; exact hfq.1
      have hfq_cl : Closure.envFullyQuotable d cl.env := by
        unfold Val.fullyQuotable Closure.fullyQuotable at hfq
        obtain ⟨_, hfq2⟩ := hfq
        cases cl with | _ => exact hfq2.2
      have hlvl_aV : Val.levelsBelow d aV := by
        unfold Val.levelsBelow at hlvl; exact hlvl.1
      have hlvl_cl : Closure.envLevelsBelow d cl.env := by
        unfold Val.levelsBelow at hlvl
        obtain ⟨_, hlvl2⟩ := hlvl
        cases cl with | _ => exact hlvl2
      unfold R at h
      obtain ⟨ρe', anne, hRa, hRL, hclb, heqF⟩ := h
      have hfω_eq : fuelω = (fuelω - 1) + 1 := rfl
      rw [hfω_eq] at hq
      unfold quote at hq
      simp only [Option.bind_eq_bind, Option.bind_eq_some,
                 Option.some.injEq] at hq
      obtain ⟨ann', hann', _body', _hbody', _⟩ := hq
      have hann'_ω : quote fuelω d aV = some ann' :=
        quote_fuel_mono (by omega) hann'
      have hRa' : R (k+1) (d+1) aV (anne.shift 1 0) :=
        R_depth_lift hlvl_aV hfq_aV hann'_ω hRa
      have hRL' : RList (k+1) (d+1) cl.env (ρe'.map (·.shift 1 0)) :=
        RList_depth_lift hlvl_cl hfq_cl hRL
      have hclb' :
          cl.body.closedAt ((ρe'.map (·.shift 1 0)).length + 1) = true := by
        rw [List.length_map]; exact hclb
      have heqF' : Equiv_c (d+1) (e.shift 1 0)
          ((Expr.fix anne
            (cl.body.substEnv (.bvar 0 :: ρe'.map (·.shift 1 0)))).shift 1 0) :=
        Equiv_c.shift heqF
      have hsubst_comm :
          (cl.body.substEnv (.bvar 0 :: ρe'.map (·.shift 1 0))).shift 1 1
          = cl.body.substEnv
              ((.bvar 0 :: ρe'.map (·.shift 1 0)).map (·.shift 1 1)) := by
        apply substEnv_shift_comm
        simp [List.length_map]; exact hclb
      have htail_eq : (.bvar 0 :: ρe'.map (·.shift 1 0)).map (·.shift 1 1)
          = .bvar 0 :: (ρe'.map (·.shift 1 0)).map (·.shift 1 0) := by
        simp only [List.map_cons, Expr.shift, decide_eq_true_eq, Nat.lt_one_iff,
                   ↓reduceIte]
        congr 1
        rw [List.map_map, List.map_map]
        apply List.map_congr_left
        intro e _he
        simp only [Function.comp]
        have := Expr.shift_shift_comm_gen e 1 0 1
        simpa using this
      unfold R
      refine ⟨ρe'.map (·.shift 1 0), anne.shift 1 0,
              hRa', hRL', hclb', ?_⟩
      have target_rewrite :
          (Expr.fix anne
            (cl.body.substEnv (.bvar 0 :: ρe'.map (·.shift 1 0)))).shift 1 0
          = Expr.fix (anne.shift 1 0)
              (cl.body.substEnv
                (.bvar 0 :: (ρe'.map (·.shift 1 0)).map (·.shift 1 0))) := by
        show Expr.fix (anne.shift 1 0) _ = Expr.fix (anne.shift 1 0) _
        congr 1
        rw [hsubst_comm, htail_eq]
      rw [target_rewrite] at heqF'
      intro S Γ hd
      exact heqF' hd
termination_by sizeOf v
decreasing_by
  all_goals simp_wf
  all_goals first
    | omega
    | (rename Closure => cl; cases cl; simp; omega)

/-- Pointwise depth-lift of `RList`. Uses `Closure.envFullyQuotable`
which provides both quote witnesses and levelsBelow recursively. -/
theorem RList_depth_lift {n d ρ ρe}
    (hlvl : Closure.envLevelsBelow d ρ)
    (hfq : Closure.envFullyQuotable d ρ)
    (h : RList n d ρ ρe) :
    RList n (d + 1) ρ (ρe.map (·.shift 1 0)) := by
  match ρ, ρe, hlvl, hfq, h with
  | [], [], _, _, _ => unfold RList; trivial
  | [], _ :: _, _, _, h => unfold RList at h; exact h.elim
  | _ :: _, [], _, _, h => unfold RList at h; exact h.elim
  | v :: ρ', e :: ρe', hlvl, hfq, h =>
      unfold RList at h
      unfold Closure.envLevelsBelow at hlvl
      unfold Closure.envFullyQuotable at hfq
      simp only [List.map_cons]
      unfold RList
      refine ⟨?_, ?_⟩
      · obtain ⟨qe, hqe⟩ := hfq.1.2
        exact R_depth_lift hlvl.1 hfq.1.1 hqe h.1
      · exact RList_depth_lift hlvl.2 hfq.2 h.2
termination_by sizeOf ρ

end

/-- A fresh `.var d` realises `.bvar 0` at depth `d+1`. -/
theorem R_fresh_bvar0 (n d : Nat) :
    R n (d + 1) (.neutral (.var d)) (.bvar 0) := by
  cases n with
  | zero => simp only [R]
  | succ k =>
    unfold R
    intro e' hq
    have heq : e' = .bvar 0 := by
      have hf : fuelω = (fuelω - 1) + 1 := rfl
      rw [hf] at hq
      unfold quote at hq
      simp only [] at hq
      have hf' : fuelω - 1 = (fuelω - 2) + 1 := rfl
      rw [hf'] at hq
      unfold quoteNeutral at hq
      simp only [Nat.lt_succ_self, if_true, Nat.add_sub_cancel,
                 Nat.sub_self, Option.some.injEq] at hq
      exact hq.symm
    subst heq
    exact fun {_ _} _ => ⟨.refl _, .refl _⟩

/-- Depth-lifting a realised environment (no head push):
each entry's realiser shifts up by one. Used by
`REnv_lift` (which then conses a fresh) and by
`OpenCtx.push_let` (which conses a concrete value).

Now carries a `levelsBelow d` hypothesis on each ρ entry (for
`R_depth_lift`). Callers discharge via `OpenCtx.hρlvl`. -/
theorem REnv_depth_lift {n d ρ ρe}
    (henv : REnv n d ρ ρe)
    (hquotes : ∀ (k : Nat) (v : Val),
        ρ[k]? = some v → ∃ qe, quote fuelω d v = some qe)
    (hρlvl : ∀ (k : Nat) (v : Val),
        ρ[k]? = some v → Val.levelsBelow d v)
    (hρfq : ∀ (k : Nat) (v : Val),
        ρ[k]? = some v → Val.fullyQuotable d v) :
    REnv n (d + 1) ρ (ρe.map (·.shift 1 0)) := by
  refine ⟨by simp [henv.1], ?_⟩
  intro m v hk
  obtain ⟨e, he, hR⟩ := henv.2 m v hk
  obtain ⟨qe, hqe⟩ := hquotes m v hk
  refine ⟨e.shift 1 0, ?_, R_depth_lift (hρlvl m v hk) (hρfq m v hk) hqe hR⟩
  have he' : ρe[m]? = some e := by
    rw [← List.get?_eq_getElem?]; exact he
  simp [List.getElem?_map, he']

/-- Lifting a realised environment under one binder: a
fresh `.var d` realises `.bvar 0` at the head; the tail
depth-lifts via `REnv_depth_lift`. -/
theorem REnv_lift {n d ρ ρe}
    (henv : REnv n d ρ ρe)
    (hquotes : ∀ (k : Nat) (v : Val),
        ρ[k]? = some v → ∃ qe, quote fuelω d v = some qe)
    (hρlvl : ∀ (k : Nat) (v : Val),
        ρ[k]? = some v → Val.levelsBelow d v)
    (hρfq : ∀ (k : Nat) (v : Val),
        ρ[k]? = some v → Val.fullyQuotable d v) :
    REnv n (d + 1)
      (Val.neutral (.var d) :: ρ)
      (.bvar 0 :: ρe.map (·.shift 1 0)) := by
  have htail := REnv_depth_lift henv hquotes hρlvl hρfq
  refine ⟨by simp [htail.1], ?_⟩
  intro k v hk
  cases k with
  | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hk
      exact ⟨.bvar 0, by simp, hk ▸ R_fresh_bvar0 n d⟩
  | succ m =>
      simp only [List.getElem?_cons_succ] at hk
      obtain ⟨e, he, hR⟩ := htail.2 m v hk
      exact ⟨e, by simpa using he, hR⟩

/-- Two lists agreeing on indices `< j` have equal `take j`. -/
private theorem List.take_eq_of_agree {α} {ρ₁ ρ₂ : List α} {j : Nat}
    (hagree : ∀ k, k < j → ρ₁[k]? = ρ₂[k]?) :
    ρ₁.take j = ρ₂.take j := by
  apply List.ext_getElem?
  intro k
  rw [List.getElem?_take, List.getElem?_take]
  by_cases hk : k < j
  · rw [if_pos hk, if_pos hk, hagree k hk]
  · rw [if_neg hk, if_neg hk]

/-- General env-irrelevance for `eval`: if the two
environments agree on every index the body can reach
(`< bvarBound body`), evaluation gives the same result.

By induction on `fuel` (eval's recursion), generalising the
body and both envs. The `.lam`/`.iota`/`.fix` cases use
`Closure.mk'`'s trimming together with `take_eq_of_agree`;
`.letE` extends both envs with the same value and recurses
at `bvarBound body ≤ bvarBound (.letE …) + 1`. -/
theorem eval_env_agree :
    ∀ {fuel unf : Nat} {body : Expr} {ρ₁ ρ₂ : Env},
      (∀ k, k < bvarBound body → ρ₁[k]? = ρ₂[k]?) →
      eval fuel unf ρ₁ body = eval fuel unf ρ₂ body := by
  intro fuel
  induction fuel with
  | zero => intros; simp [eval_zero]
  | succ n ih =>
    intro unf body ρ₁ ρ₂ hagree
    unfold eval
    cases body with
    | type => rfl
    | bvar k =>
        simp only []
        exact hagree k (by simp [bvarBound])
    | lam dom bdy =>
        simp only [bvarBound] at hagree
        simp only [Option.bind_eq_bind]
        have hd := ih (body := dom) (unf := unf) (ρ₁ := ρ₁) (ρ₂ := ρ₂)
              (fun k hk => hagree k (Nat.lt_of_lt_of_le hk (Nat.le_max_left _ _)))
        rw [hd]
        have hcl : Closure.mk' bdy ρ₁ = Closure.mk' bdy ρ₂ := by
          simp only [Closure.mk']
          congr 1
          exact List.take_eq_of_agree
            (fun k hk => hagree k
              (Nat.lt_of_lt_of_le hk (Nat.le_max_right _ _)))
        rw [hcl]
    | iota ann bdy =>
        simp only [bvarBound] at hagree
        simp only [Option.bind_eq_bind]
        have hd := ih (body := ann) (unf := unf) (ρ₁ := ρ₁) (ρ₂ := ρ₂)
              (fun k hk => hagree k (Nat.lt_of_lt_of_le hk (Nat.le_max_left _ _)))
        rw [hd]
        have hcl : Closure.mk' bdy ρ₁ = Closure.mk' bdy ρ₂ := by
          simp only [Closure.mk']
          congr 1
          exact List.take_eq_of_agree
            (fun k hk => hagree k
              (Nat.lt_of_lt_of_le hk (Nat.le_max_right _ _)))
        rw [hcl]
    | «fix» ann bdy =>
        simp only [bvarBound] at hagree
        simp only [Option.bind_eq_bind]
        have hd := ih (body := ann) (unf := unf) (ρ₁ := ρ₁) (ρ₂ := ρ₂)
              (fun k hk => hagree k (Nat.lt_of_lt_of_le hk (Nat.le_max_left _ _)))
        rw [hd]
        have hcl : Closure.mk' bdy ρ₁ = Closure.mk' bdy ρ₂ := by
          simp only [Closure.mk']
          congr 1
          exact List.take_eq_of_agree
            (fun k hk => hagree k
              (Nat.lt_of_lt_of_le hk (Nat.le_max_right _ _)))
        rw [hcl]
    | app f a =>
        simp only [bvarBound] at hagree
        simp only [Option.bind_eq_bind]
        have hf := ih (body := f) (unf := unf) (ρ₁ := ρ₁) (ρ₂ := ρ₂)
              (fun k hk => hagree k (Nat.lt_of_lt_of_le hk (Nat.le_max_left _ _)))
        have ha := ih (body := a) (unf := unf) (ρ₁ := ρ₁) (ρ₂ := ρ₂)
              (fun k hk => hagree k (Nat.lt_of_lt_of_le hk (Nat.le_max_right _ _)))
        rw [hf, ha]
    | letE v bdy =>
        simp only [bvarBound] at hagree
        simp only [Option.bind_eq_bind]
        have hv' := ih (body := v) (unf := unf) (ρ₁ := ρ₁) (ρ₂ := ρ₂)
              (fun k hk => hagree k (Nat.lt_of_lt_of_le hk (Nat.le_max_left _ _)))
        rw [hv']
        match hv : eval n unf ρ₂ v with
        | none => simp [hv]
        | some vV =>
            simp only [hv, Option.some_bind]
            apply ih
            intro k hk
            cases k with
            | zero => simp
            | succ m =>
                simp only [List.getElem?_cons_succ]
                exact hagree m (by omega)
    | asc t _ty =>
        simp only [bvarBound] at hagree
        simp only []
        exact ih (body := t)
          (fun k hk => hagree k (Nat.lt_of_lt_of_le hk (Nat.le_max_left _ _)))

/-- `eval` is insensitive to env entries beyond
`bvarBound body`: trimming `ρ` to that prefix gives the
same result. Corollary of `eval_env_agree`. (Holds without
`bvarBound body ≤ ρ.length`: when `ρ` is shorter, `take` is
the identity.) -/
theorem eval_env_take {fuel unf : Nat} {ρ : Env} {body : Expr} :
    eval fuel unf (ρ.take (bvarBound body)) body
      = eval fuel unf ρ body := by
  apply eval_env_agree
  intro k hk
  rw [List.getElem?_take, if_pos hk]

/-- One β-step is an `Equiv`. -/
theorem Equiv.beta (dom body arg : Expr) :
    Equiv (.app (.lam dom body) arg) (body.subst 0 arg) :=
  fun {_ _} => ⟨.beta_L (.refl _), .beta_R (.refl _)⟩

/-- One `.fix`-unfold step is an `Equiv`: both directions are
single `Subtype'` constructors with a `.refl` premise (the
unfolded body is compared with itself under the extended
seen-set). -/
theorem Equiv.fix_unfold (ann body : Expr) :
    Equiv (.fix ann body) (body.subst 0 (.fix ann body)) :=
  fun {_ _} => ⟨.unfold_fix_L (.refl _), .unfold_fix_R (.refl _)⟩

/-- The ι fixpoint equation, both directions. Symmetric to
`fix_unfold` now that `Subtype'.unfold_iota_R` exists. -/
theorem Equiv.iota_unfold (ann body : Expr) :
    Equiv (.iota ann body) (body.subst 0 (.iota ann body)) :=
  fun {_ _} => ⟨.unfold_iota_L (.refl _), .unfold_iota_R (.refl _)⟩

/-- Extending a realised environment with a realised pair. -/
theorem REnv_cons {n d ρ ρe v e}
    (henv : REnv n d ρ ρe) (hv : R n d v e) :
    REnv n d (v :: ρ) (e :: ρe) := by
  refine ⟨by simp [henv.1], ?_⟩
  intro k w hk
  cases k with
  | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hk
      exact ⟨e, by simp, hk ▸ hv⟩
  | succ j =>
      simp only [List.getElem?_cons_succ] at hk
      obtain ⟨e', he', hR⟩ := henv.2 j w hk
      exact ⟨e', by simpa using he', hR⟩

/-- The closure-clause witness packaged by `eval_realises`'s
`.lam`/`.iota`/`.fix` body cases. Pulled out so the three
near-identical cases share one proof; `j := bvarBound bExpr
− 1` and `cl := Closure.mk' bExpr ρ`. -/
private theorem closure_clause_witness {k d ρ ρe} {bExpr : Expr}
    (henv : REnv (k+1) d ρ ρe)
    (hclb_full : bExpr.closedAt (ρe.length + 1) = true) :
    let j := bvarBound bExpr - 1
    let ρe' := ρe.take j
    RList (k+1) d (ρ.take j) ρe' ∧
    bExpr.closedAt (ρe'.length + 1) = true ∧
    bExpr.substEnv (.bvar 0 :: ρe'.map (·.shift 1 0))
      = bExpr.substEnv (.bvar 0 :: ρe.map (·.shift 1 0)) := by
  intro j ρe'
  have hbb : bvarBound bExpr ≤ ρe.length + 1 :=
    bvarBound_le_of_closedAt hclb_full
  have hjle : j ≤ ρe.length := by omega
  have hρe'_len : ρe'.length = j := by
    simp only [ρe', List.length_take]; omega
  refine ⟨?_, ?_, ?_⟩
  · exact RList_of_REnv (REnv_take j henv)
  · rw [hρe'_len]
    exact Expr.closedAt_mono (closedAt_bvarBound bExpr) (by omega)
  · -- (ρe.take j).map shift = (ρe.map shift).take j, then
    -- substEnv_closedAt_irrel with bExpr.closedAt (j+1).
    have hmap_take : ρe'.map (·.shift 1 0)
                   = (ρe.map (·.shift 1 0)).take j := by
      simp only [ρe', List.map_take]
    rw [hmap_take]
    exact substEnv_closedAt_irrel
      (j := j) (ρe := ρe.map (·.shift 1 0))
      (Expr.closedAt_mono (closedAt_bvarBound bExpr) (by omega))
      rfl

/-- Helper for `vapp_realises`'s `.neutral`/`.type`/stuck
cases: assembles the `R (k+1) d (.neutral N) (.app fe ae)`
conclusion from per-component Equiv-witnesses. Callers supply
`hfEq`/`haEq` directly. -/
private theorem R_neutral_app {k d N fe ae}
    (hdecomp : ∀ e', quote fuelω d (.neutral N) = some e' →
       ∃ ne ve, e' = .app ne ve ∧
         Equiv_c d ne fe ∧ Equiv_c d ve ae) :
    R (k+1) d (Val.neutral N) (.app fe ae) := by
  unfold R
  intro e' hq
  obtain ⟨ne, ve, heq, hfEq, haEq⟩ := hdecomp e' hq
  subst heq
  -- Build Equiv_c d (.app ne ve) (.app fe ae) from hfEq : Equiv_c d ne fe
  -- and haEq : Equiv_c d ve ae via pointwise Subtype' .app_cong.
  intro S Γe hd
  obtain ⟨hf12, hf21⟩ := hfEq hd
  obtain ⟨ha12, ha21⟩ := haEq hd
  exact ⟨.app_cong hf12 ha12 ha21, .app_cong hf21 ha21 ha12⟩

/-- **quoteClosure-realisation**: when `quoteClosure fuel d cl`
succeeds with result `body'`, and the closure's env is realised
by `ρe'` via `RList`, and the closure body is closed at
`ρe'.length + 1`, then `body'` is equivalent at depth `d+1` to
`cl.body.substEnv (.bvar 0 :: ρe'.map (·.shift 1 0))`.

This is the consolidated sorry factored out from R_quote_equiv's
.lam/.iota/.fix closure cases (now proven modulo this helper).
Closing this single sorry discharges all three closure cases of
R_quote_equiv in one go.

**Blocker**: body-level Equiv is the NbE fundamental correspondence
on closures — body' = quote (d+1) (eval v_body), bodyE = substEnv
cl.body. These are equivalent via eval_realises + R_quote_equiv at
d+1 (mutual), but REnv at d+1 requires R_depth_lift on cl.env
entries, circularly blocked on the recursive `Val.fullyQuotable`
invariant (see DECISION-LOG). -/
theorem quoteClosure_realises {d : Nat} {cl : Closure} {body' : Expr}
    {m : Nat} {ρe' : List Expr}
    (_hq : quoteClosure fuelω d cl = some body')
    (_hRL : RList m d cl.env ρe')
    (_hclb : cl.body.closedAt (ρe'.length + 1) = true) :
    Equiv_c (d+1) body'
      (cl.body.substEnv (.bvar 0 :: ρe'.map (·.shift 1 0))) :=
  sorry

/-- Extract an `Equiv_c d`-witness between a `Val`'s quote and
the source `Expr` it realises. For `.type`/`.neutral`, this is
the base conjunct of `R` directly. For `.lam`/`.iota`/`.fix`,
closure cases delegate to `quoteClosure_realises` (consolidated
sorry; see that theorem's docstring).

Defined BEFORE the `eval_realises`/`vapp_realises` mutual so
`vapp_realises`'s `.stuckRec` branches can reference it in the
`R_neutral_app`-derived witness construction.

All callers in the current codebase:
- `Soundness.lean:eval_quote_equiv_closed` (closed context).
- `SoundnessProof.lean:OpenCtx.eq` (open context).
- `SoundnessProof.lean:vapp_realises` stuckRec branches. -/
theorem R_quote_equiv {n d v e}
    (hn : 0 < n) (h : R n d v e)
    {e' : Expr} (hq : quote fuelω d v = some e') :
    Equiv_c d e' e := by
  cases n with
  | zero => omega
  | succ m =>
      cases v with
      | type =>
          unfold R at h
          exact h e' hq
      | neutral _ =>
          unfold R at h
          exact h e' hq
      | lam dV cl =>
          have hfω : fuelω = (fuelω - 1) + 1 := rfl
          rw [hfω] at hq
          unfold quote at hq
          simp only [Option.bind_eq_bind, Option.bind_eq_some,
                     Option.some.injEq] at hq
          obtain ⟨dom', hdom', body', hbody', heq'⟩ := hq
          subst heq'
          unfold R at h
          obtain ⟨ρe', dome, hRd, hRL, hclb, heqL⟩ := h
          have hdom'_ω : quote fuelω d dV = some dom' :=
            quote_fuel_mono (by omega) hdom'
          have hbody'_ω : quoteClosure fuelω d cl = some body' :=
            quoteClosure_fuel_mono (by omega) hbody'
          have hEd : Equiv_c d dom' dome :=
            R_quote_equiv (Nat.succ_pos _) hRd hdom'_ω
          have hEb : Equiv_c (d+1) body'
              (cl.body.substEnv (.bvar 0 :: ρe'.map (·.shift 1 0))) :=
            quoteClosure_realises hbody'_ω hRL hclb
          -- Goal: Equiv_c d (.lam dom' body') e. Chain via lam_cong + heqL.
          have step1 : Equiv_c d (.lam dom' body')
              (.lam dome (cl.body.substEnv (.bvar 0 :: ρe'.map (·.shift 1 0)))) :=
            Equiv_c.lam_cong hEd hEb
          have step2 : Equiv_c d
              (.lam dome (cl.body.substEnv (.bvar 0 :: ρe'.map (·.shift 1 0)))) e :=
            Equiv_c.symm heqL
          intro S Γe hd
          obtain ⟨h12, h21⟩ := step1 hd
          obtain ⟨h34, h43⟩ := step2 hd
          exact ⟨.trans h12 h34, .trans h43 h21⟩
      | iota aV cl =>
          have hfω : fuelω = (fuelω - 1) + 1 := rfl
          rw [hfω] at hq
          unfold quote at hq
          simp only [Option.bind_eq_bind, Option.bind_eq_some,
                     Option.some.injEq] at hq
          obtain ⟨ann', hann', body', hbody', heq'⟩ := hq
          subst heq'
          unfold R at h
          obtain ⟨ρe', anne, hRa, hRL, hclb, heqI⟩ := h
          have hann'_ω : quote fuelω d aV = some ann' :=
            quote_fuel_mono (by omega) hann'
          have hbody'_ω : quoteClosure fuelω d cl = some body' :=
            quoteClosure_fuel_mono (by omega) hbody'
          have hEa : Equiv_c d ann' anne :=
            R_quote_equiv (Nat.succ_pos _) hRa hann'_ω
          have hEb : Equiv_c (d+1) body'
              (cl.body.substEnv (.bvar 0 :: ρe'.map (·.shift 1 0))) :=
            quoteClosure_realises hbody'_ω hRL hclb
          have step1 : Equiv_c d (.iota ann' body')
              (.iota anne (cl.body.substEnv (.bvar 0 :: ρe'.map (·.shift 1 0)))) :=
            Equiv_c.iota_cong hEa hEb
          have step2 : Equiv_c d
              (.iota anne (cl.body.substEnv (.bvar 0 :: ρe'.map (·.shift 1 0)))) e :=
            Equiv_c.symm heqI
          intro S Γe hd
          obtain ⟨h12, h21⟩ := step1 hd
          obtain ⟨h34, h43⟩ := step2 hd
          exact ⟨.trans h12 h34, .trans h43 h21⟩
      | «fix» aV cl =>
          have hfω : fuelω = (fuelω - 1) + 1 := rfl
          rw [hfω] at hq
          unfold quote at hq
          simp only [Option.bind_eq_bind, Option.bind_eq_some,
                     Option.some.injEq] at hq
          obtain ⟨ann', hann', body', hbody', heq'⟩ := hq
          subst heq'
          unfold R at h
          obtain ⟨ρe', anne, hRa, hRL, hclb, heqF⟩ := h
          have hann'_ω : quote fuelω d aV = some ann' :=
            quote_fuel_mono (by omega) hann'
          have hbody'_ω : quoteClosure fuelω d cl = some body' :=
            quoteClosure_fuel_mono (by omega) hbody'
          have hEa : Equiv_c d ann' anne :=
            R_quote_equiv (Nat.succ_pos _) hRa hann'_ω
          have hEb : Equiv_c (d+1) body'
              (cl.body.substEnv (.bvar 0 :: ρe'.map (·.shift 1 0))) :=
            quoteClosure_realises hbody'_ω hRL hclb
          have step1 : Equiv_c d (.fix ann' body')
              (.fix anne (cl.body.substEnv (.bvar 0 :: ρe'.map (·.shift 1 0)))) :=
            Equiv_c.fix_cong hEa hEb
          have step2 : Equiv_c d
              (.fix anne (cl.body.substEnv (.bvar 0 :: ρe'.map (·.shift 1 0)))) e :=
            Equiv_c.symm heqF
          intro S Γe hd
          obtain ⟨h12, h21⟩ := step1 hd
          obtain ⟨h34, h43⟩ := step2 hd
          exact ⟨.trans h12 h34, .trans h43 h21⟩

/-- Quote of `.neutral (.stuckRec vf va)` decomposes as
`.app (quote vf) (quote va)` (after fuel-mono lifting). -/
private theorem quote_stuckRec_decomp {d vf va} (e' : Expr)
    (hq : quote fuelω d (.neutral (.stuckRec vf va)) = some e') :
    ∃ ne ve, e' = .app ne ve ∧
      quote fuelω d vf = some ne ∧ quote fuelω d va = some ve := by
  have hfω : fuelω = (fuelω - 1) + 1 := rfl
  rw [hfω] at hq; unfold quote at hq
  have hfω' : fuelω - 1 = (fuelω - 2) + 1 := rfl
  rw [hfω'] at hq; unfold quoteNeutral at hq
  simp only [Option.bind_eq_bind, Option.bind_eq_some,
             Option.some.injEq] at hq
  obtain ⟨ne, hne, ve, hve, heq⟩ := hq
  exact ⟨ne, ve, heq.symm,
         quote_fuel_mono (by omega) hne,
         quote_fuel_mono (by omega) hve⟩

mutual
/-- Realisation through `vapp`. Mutual with `eval_realises`
on `fuel`; both stay at the *same* step-index `m`
throughout (the env-exposes `R` clause makes the Kripke
step-loss disappear — see `R`'s docstring).

`.neutral`/`.type`/stuck heads: `r` is `.neutral …`; base
via `Equiv.app` on the inputs' base conjuncts.

`.lam` head: `r = eval fuel (va :: cl.env) cl.body`. From
`hRf`'s clause obtain `RList m d cl.env ρe'`, cons `hRa` to
get `REnv m d (va :: cl.env) (ae :: ρe')`, apply
`eval_realises` (mutual, fuel `< fuel+1`), then
`R_resp_Equiv` along `.app fe ae ≡ bode.subst 0 ae` (via
`Equiv.beta` after `heqL`) `= cl.body.substEnv (ae :: ρe')`
(via `substEnv_subst_comp`).

`.iota`/`.fix` head, unfold branch: first
`f' = eval fuel (vf :: cl.env) cl.body`, then
`r = vapp fuel f' va`. From `hRf`'s clause + `REnv_cons hRf`
(self-binding) + `eval_realises` (mutual): `R m d f'
(cl.body.substEnv (fe :: ρe')) = bode.subst 0 fe`. Then
`R_resp_Equiv` along `bode.subst 0 fe ≡ fe` (via
`Equiv.subst_resp heqI` + `Equiv.iota_unfold` + `heqI⁻¹`)
gives `R m d f' fe`. Recurse `vapp_realises` (mutual,
fuel `< fuel+1`).

The `bode.subst 0 fe ≡ fe` step requires `Equiv.subst_resp`
on `fe ≡ .iota/.fix anne bode`, which was deleted
2026-04-21 (it depended on `Equiv.shift`'s nil-Γ sorry).
The closedness-carrying `Equiv.subst_resp_closed` is
available but needs `fe.closedAt 0 ∧ anne.closedAt 0`,
which don't hold in open contexts. Hence these two unfold
sub-sorries remain — they close once either (a) a general
closedness invariant is threaded through `vapp_realises`,
or (b) the nil-Γ `Equiv.shift` sorry is closed (e.g. via
`Subtype'.shift_nil` with `Seen.wellClosed`). -/
theorem vapp_realises {fuel unf vf va r m d fe ae}
    (hvapp : vapp fuel unf vf va = some r)
    (hRf : R m d vf fe) (hRa : R m d va ae) :
    R m d r (.app fe ae) := by
  match m with
  | 0 => unfold R; trivial
  | k+1 =>
    match fuel, hvapp with
    | 0, hvapp => simp [vapp_zero] at hvapp
    | fuel+1, hvapp =>
      unfold vapp at hvapp
      match hvfeq : vf, hvapp with
      | .neutral nf, hvapp =>
          simp only [Option.some.injEq] at hvapp
          -- (match already reduced for .neutral)
          subst hvapp
          have hRfN : R (k+1) d (.neutral nf) fe := hvfeq ▸ hRf
          refine R_neutral_app (N := .app nf va) (fe := fe) (ae := ae) ?_
          intro e' hq
          -- Decompose: quote (.neutral (.app nf va)) = .app (quoteNeutral nf) (quote va).
          have hfω : fuelω = (fuelω - 1) + 1 := rfl
          rw [hfω] at hq; unfold quote at hq
          have hfω' : fuelω - 1 = (fuelω - 2) + 1 := rfl
          rw [hfω'] at hq; unfold quoteNeutral at hq
          simp only [Option.bind_eq_bind, Option.bind_eq_some,
                     Option.some.injEq] at hq
          obtain ⟨ne, hne, ve, hve, heq⟩ := hq
          refine ⟨ne, ve, heq.symm, ?_, ?_⟩
          · -- Equiv ne fe. Use R base conjunct on .neutral nf.
            unfold R at hRfN
            apply hRfN
            rw [hfω]; unfold quote
            exact quoteNeutral_fuel_mono (by omega) hne
          · -- Equiv ve ae. Use R_quote_equiv on hRa.
            exact R_quote_equiv (Nat.succ_pos _) hRa
              (quote_fuel_mono (by omega) hve)
      | .type, hvapp =>
          simp only [Option.some.injEq] at hvapp
          subst hvapp
          have hRfT : R (k+1) d .type fe := hvfeq ▸ hRf
          refine R_neutral_app (N := .stuckRec .type va) (fe := fe) (ae := ae) ?_
          intro e' hq
          obtain ⟨ne, ve, heq, hqf, hqa⟩ :=
            quote_stuckRec_decomp (vf := .type) (va := va) e' hq
          refine ⟨ne, ve, heq, ?_, ?_⟩
          · unfold R at hRfT; exact hRfT ne hqf
          · exact R_quote_equiv (Nat.succ_pos _) hRa hqa
      | .lam dV ⟨lbody, lenv⟩, hvapp =>
          simp only [] at hvapp
          -- hvapp : eval fuel unf (va :: lenv) lbody = some r
          have hRf' : R (k+1) d (.lam dV ⟨lbody, lenv⟩) fe := hvfeq ▸ hRf
          unfold R at hRf'
          obtain ⟨ρe', dome, _hRd, hRL, hclb, heqL⟩ := hRf'
          have henv' := REnv_of_RList hRL
          have henv_ext := REnv_cons henv' hRa
          have hclb' : lbody.closedAt (ae :: ρe').length = true := by
            simpa using hclb
          have hRr := eval_realises hvapp henv_ext hclb'
          -- hRr : R (k+1) d r (lbody.substEnv (ae :: ρe'))
          refine R_resp_Equiv_c ?_ hRr
          have hcomp :
              Expr.subst (lbody.substEnv
                  (.bvar 0 :: ρe'.map (·.shift 1 0))) 0 ae
              = lbody.substEnv (ae :: ρe') :=
            Expr.substEnv_subst_comp lbody ρe' ae hclb
          rw [← hcomp]
          -- `bode.subst 0 ae ≡ .app fe ae` via
          --   .app fe ae ≡ .app (.lam dome bode) ae [heqL]
          --   ≡ bode.subst 0 ae [β]
          -- heqL is Equiv_c d; we undo the refine R_resp_Equiv by
          -- using R_resp_Equiv_c instead (above this match).
          intro S Γe hd
          obtain ⟨heq12, heq21⟩ := heqL hd
          refine ⟨.trans (.beta_R (dom := dome) (.refl _)) ?_,
                  .trans ?_ (.beta_L (dom := dome) (.refl _))⟩
          · exact .app_cong heq21 (.refl ae) (.refl ae)
          · exact .app_cong heq12 (.refl ae) (.refl ae)
      | .iota annV ⟨lbody, lenv⟩, hvapp =>
          simp only [] at hvapp
          have hRf' : R (k+1) d (.iota annV ⟨lbody, lenv⟩) fe := hvfeq ▸ hRf
          by_cases hcond : (va.isNeutral || unf == 0) = true
          · simp only [hcond, ↓reduceIte, Option.some.injEq] at hvapp
            subst hvapp
            refine R_neutral_app
              (N := .stuckRec (.iota annV ⟨lbody, lenv⟩) va)
              (fe := fe) (ae := ae) ?_
            intro e' hq
            obtain ⟨ne, ve, heq, hqf, hqa⟩ :=
              quote_stuckRec_decomp
                (vf := .iota annV ⟨lbody, lenv⟩) (va := va) e' hq
            refine ⟨ne, ve, heq, ?_, ?_⟩
            · exact R_quote_equiv (Nat.succ_pos _) hRf' hqf
            · exact R_quote_equiv (Nat.succ_pos _) hRa hqa
          · -- Unfold branch.
            simp only [hcond, Bool.false_eq_true, ↓reduceIte,
                       Option.bind_eq_bind, Option.bind_eq_some] at hvapp
            obtain ⟨f', hf', hvapp'⟩ := hvapp
            have hRf'' := hRf'  -- preserve for self-binding
            unfold R at hRf'
            obtain ⟨ρe', anne, _hRa_head, hRL, hclb, heqI⟩ := hRf'
            have henv' := REnv_of_RList hRL
            have henv_ext := REnv_cons henv' hRf''
            have hclb' : lbody.closedAt (fe :: ρe').length = true := by
              simpa using hclb
            -- eval_realises on the unfold's body eval (mutual,
            -- fuel < fuel+1).
            have hRf3 := eval_realises hf' henv_ext hclb'
            -- hRf3 : R (k+1) d f' (lbody.substEnv (fe :: ρe'))
            -- Rewrite via hcomp, then `R_resp_Equiv` with the
            -- iota-unfold Equiv chain:
            --   bode.subst 0 fe ≡ .iota anne bode ≡ fe
            -- The subst-respect step uses Subtype' rules directly
            -- (unfold_iota_L/R) — see helper below.
            have hcomp :
                Expr.subst (lbody.substEnv
                    (.bvar 0 :: ρe'.map (·.shift 1 0))) 0 fe
                = lbody.substEnv (fe :: ρe') :=
              Expr.substEnv_subst_comp lbody ρe' fe hclb
            have hRf4 : R (k+1) d f' fe := by
              -- Chain: bode.subst 0 fe ≡ bode.subst 0 (.iota anne bode)
              --                     [via Equiv_c.subst_resp on heqI]
              --        ≡ .iota anne bode  [via Equiv.iota_unfold reversed]
              --        ≡ fe               [via heqI reversed]
              let bode := lbody.substEnv (.bvar 0 :: ρe'.map (·.shift 1 0))
              have step1 : Equiv_c d (bode.subst 0 fe)
                  (bode.subst 0 (.iota anne bode)) :=
                Equiv_c.subst_resp bode heqI 0
              have step2 : Equiv_c d (bode.subst 0 (.iota anne bode))
                  (.iota anne bode) :=
                Equiv_c.of_Equiv (Equiv.symm (Equiv.iota_unfold anne bode))
              have step3 : Equiv_c d (.iota anne bode) fe :=
                Equiv_c.symm heqI
              have hEq : Equiv_c d (bode.subst 0 fe) fe :=
                Equiv_c.trans (Equiv_c.trans step1 step2) step3
              -- hRf3 : R (k+1) d f' (lbody.substEnv (fe :: ρe'))
              --     = R (k+1) d f' (bode.subst 0 fe) via hcomp reversed.
              rw [← hcomp] at hRf3
              exact R_resp_Equiv_c hEq hRf3
            exact vapp_realises hvapp' hRf4 hRa
      | .«fix» annV ⟨lbody, lenv⟩, hvapp =>
          simp only [] at hvapp
          have hRf' : R (k+1) d (.«fix» annV ⟨lbody, lenv⟩) fe := hvfeq ▸ hRf
          by_cases hcond : (va.isNeutral || unf == 0) = true
          · simp only [hcond, ↓reduceIte, Option.some.injEq] at hvapp
            subst hvapp
            refine R_neutral_app
              (N := .stuckRec (.«fix» annV ⟨lbody, lenv⟩) va)
              (fe := fe) (ae := ae) ?_
            intro e' hq
            obtain ⟨ne, ve, heq, hqf, hqa⟩ :=
              quote_stuckRec_decomp
                (vf := .«fix» annV ⟨lbody, lenv⟩) (va := va) e' hq
            refine ⟨ne, ve, heq, ?_, ?_⟩
            · exact R_quote_equiv (Nat.succ_pos _) hRf' hqf
            · exact R_quote_equiv (Nat.succ_pos _) hRa hqa
          · simp only [hcond, Bool.false_eq_true, ↓reduceIte,
                       Option.bind_eq_bind, Option.bind_eq_some] at hvapp
            obtain ⟨f', hf', hvapp'⟩ := hvapp
            have hRf'' := hRf'
            unfold R at hRf'
            obtain ⟨ρe', anne, _hRa_head, hRL, hclb, heqF⟩ := hRf'
            have henv' := REnv_of_RList hRL
            have henv_ext := REnv_cons henv' hRf''
            have hclb' : lbody.closedAt (fe :: ρe').length = true := by
              simpa using hclb
            have hRf3 := eval_realises hf' henv_ext hclb'
            have hcomp :
                Expr.subst (lbody.substEnv
                    (.bvar 0 :: ρe'.map (·.shift 1 0))) 0 fe
                = lbody.substEnv (fe :: ρe') :=
              Expr.substEnv_subst_comp lbody ρe' fe hclb
            have hRf4 : R (k+1) d f' fe := by
              -- Same chain as .iota, with .fix_unfold instead of .iota_unfold.
              let bode := lbody.substEnv (.bvar 0 :: ρe'.map (·.shift 1 0))
              have step1 : Equiv_c d (bode.subst 0 fe)
                  (bode.subst 0 (.fix anne bode)) :=
                Equiv_c.subst_resp bode heqF 0
              have step2 : Equiv_c d (bode.subst 0 (.fix anne bode))
                  (.fix anne bode) :=
                Equiv_c.of_Equiv (Equiv.symm (Equiv.fix_unfold anne bode))
              have step3 : Equiv_c d (.fix anne bode) fe :=
                Equiv_c.symm heqF
              have hEq : Equiv_c d (bode.subst 0 fe) fe :=
                Equiv_c.trans (Equiv_c.trans step1 step2) step3
              rw [← hcomp] at hRf3
              exact R_resp_Equiv_c hEq hRf3
            exact vapp_realises hvapp' hRf4 hRa
termination_by fuel

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
    (henv : REnv m d ρ ρe)
    (hcl : body.closedAt ρe.length = true) :
    R m d v (body.substEnv ρe) := by
  -- Mutual with `vapp_realises` on `fuel`. The step-index
  -- `m` is fixed throughout — the env-exposes `R` clause
  -- means no Kripke step is ever taken, so no outer
  -- `m`-induction is needed.
  match m with
  | 0 => unfold R; trivial
  | k + 1 =>
    match fuel, heval with
    | 0, heval => simp [eval_zero] at heval
    | fuel + 1, heval =>
      -- `ihf'`: mutual self-call at `fuel < fuel+1`, same
      -- step-index `k+1`. Generalises over the depth so
      -- the (currently sorried) base-conjunct cases that
      -- need `d+1` could share it.
      have ihf' : ∀ {unf' ρ' body' v' d' ρe'},
          eval fuel unf' ρ' body' = some v' →
          REnv (k+1) d' ρ' ρe' →
          body'.closedAt ρe'.length = true →
          R (k+1) d' v' (body'.substEnv ρe') :=
        fun he hr hc => eval_realises he hr hc
      cases body with
      | type =>
          -- eval .type → .type; substEnv .type = .type.
          unfold eval at heval; simp only [] at heval
          cases heval
          show R (k+1) d .type (Expr.substEnv ρe .type)
          unfold Expr.substEnv R
          intro e' hq
          have hqt : quote fuelω d .type = some .type := by
            have hf : fuelω = (fuelω - 1) + 1 := rfl
            rw [hf]; unfold quote; rfl
          rw [hqt] at hq; cases hq
          exact fun {_ _} _ => ⟨.refl _, .refl _⟩
      | bvar j =>
          -- eval (.bvar j) = ρ[j]?. REnv gives R (k+1) d ρ[j] ρe[j].
          unfold eval at heval; simp only [] at heval
          obtain ⟨e', he', hR⟩ := henv.2 j v heval
          -- substEnv (.bvar j) = ρe[j]! (when j < ρe.length).
          show R (k+1) d v (Expr.substEnv ρe (.bvar j))
          unfold Expr.substEnv
          have he'' : ρe[j]? = some e' := by
            simpa [List.get?_eq_getElem?] using he'
          have hlen : j < ρe.length :=
            (List.getElem?_eq_some_iff.mp he'').1
          simp only [hlen, ↓reduceIte]
          have heq : ρe[j]! = e' := by
            simp [List.getElem!_eq_getElem?_getD, he'']
          exact heq ▸ hR
      | asc t ty =>
          -- Post-A8, eval (.asc t ty) = eval t (the *term*;
          -- ascription is computationally transparent). The
          -- earlier comment here was stale (it described the
          -- pre-A8 `eval ty` arm).
          simp only [Expr.closedAt, Bool.and_eq_true] at hcl
          unfold eval at heval; simp only [] at heval
          have hRt := ihf' heval henv hcl.1
          unfold Expr.substEnv
          -- Goal: R (k+1) d v (.asc te tye); have R (k+1) d v te.
          -- `te ≡ .asc te tye` by `.asc_R`/`.asc_L (refl)`.
          exact R_resp_Equiv
            (fun {_ _} => ⟨.asc_R (.refl _), .asc_L (.refl _)⟩) hRt
      | letE val bExpr =>
          -- eval (.letE val bExpr): eval val → vV;
          -- eval (vV :: ρ) bExpr → v.
          simp only [Expr.closedAt, Bool.and_eq_true] at hcl
          unfold eval at heval
          simp only [Option.bind_eq_bind, Option.bind_eq_some] at heval
          obtain ⟨vV, hvV, hbody⟩ := heval
          -- IH_fuel on val: R (k+1) d vV (val.substEnv ρe).
          have hRvV := ihf' hvV henv hcl.1
          -- Extended env realises (val.substEnv ρe :: ρe).
          have henv' := REnv_cons henv hRvV
          -- IH_fuel on bExpr at the extended env:
          --   R (k+1) d v (bExpr.substEnv (val.substEnv ρe :: ρe)).
          have hRbody := ihf' hbody henv' (by simpa using hcl.2)
          -- substEnv .letE = .letE (val.substEnv ρe)
          --   (bExpr.substEnv (lift ρe)). And by
          -- substEnv_subst_comp, `(bExpr.substEnv (lift ρe))
          --   .subst 0 (val.substEnv ρe)` =
          --   `bExpr.substEnv (val.substEnv ρe :: ρe)`.
          -- So the goal `R (k+1) d v (.letE ve be_lifted)` and
          -- `hRbody : R (k+1) d v (be_lifted.subst 0 ve)` are
          -- related by `Subtype'.letE_L/R` (one let-β step).
          show R (k+1) d v (Expr.substEnv ρe (.letE val bExpr))
          unfold Expr.substEnv
          -- Goal: R (k+1) d v (.letE (val.substEnv ρe)
          --                          (bExpr.substEnv (lift ρe)))
          refine R_resp_Equiv ?_ hRbody
          -- Equiv (bExpr.substEnv (ve :: ρe)) (.letE ve be_lifted):
          -- via letE_L/R after substEnv_subst_comp rewrites
          -- be_lifted.subst 0 ve = bExpr.substEnv (ve :: ρe).
          -- substEnv_subst_comp needs `bExpr.closedAt
          -- (ρe.length + 1)`; threading a closedness
          -- invariant through REnv (or relaxing
          -- substEnv_subst_comp) is the eventual fix.
          have hcomp : Expr.subst
                          (Expr.substEnv ((.bvar 0) :: ρe.map (·.shift 1 0)) bExpr)
                          0 (Expr.substEnv ρe val)
                     = Expr.substEnv (Expr.substEnv ρe val :: ρe) bExpr :=
            Expr.substEnv_subst_comp bExpr ρe (Expr.substEnv ρe val) hcl.2
          intro S Γe
          refine ⟨?_, ?_⟩
          · rw [← hcomp]; exact .letE_R (.refl _)
          · rw [← hcomp]; exact .letE_L (.refl _)
      | lam dom bExpr =>
          -- eval (fuel+1) ρ (.lam dom bExpr) =
          --   .lam (eval fuel ρ dom) (Closure.mk' bExpr ρ).
          simp only [Expr.closedAt, Bool.and_eq_true] at hcl
          unfold eval at heval
          simp only [Option.bind_eq_bind, Option.bind_eq_some] at heval
          obtain ⟨domV, hdomV, hv⟩ := heval
          simp only [Option.some.injEq] at hv
          subst hv
          -- v = .lam domV (Closure.mk' bExpr ρ)
          -- Closure.mk' bExpr ρ = ⟨bExpr, ρ.take (bvarBound bExpr - 1)⟩
          unfold Expr.substEnv
          unfold R
          -- Env-exposes clause: `∃ ρe' dome, R headAnn ∧ RList … ∧
          -- closed ∧ Equiv`. With `cl = Closure.mk' bExpr ρ
          -- = ⟨bExpr, ρ.take j⟩`, take `ρe' := ρe.take j`
          -- and `dome := dom.substEnv ρe`. The head-R comes from
          -- `ihf' hdomV henv hcl.1`. `Equiv` is `refl` after
          -- `substEnv_closedAt_irrel`.
          simp only [Closure.mk']
          have hRdom := ihf' hdomV henv hcl.1
          obtain ⟨hRL, hclb', hbody_eq⟩ :=
            closure_clause_witness henv hcl.2
          exact ⟨ρe.take (bvarBound bExpr - 1), dom.substEnv ρe,
                 hRdom, hRL, hclb', hbody_eq ▸ Equiv_c.refl _ _⟩
      | app f a =>
          -- eval (fuel+1) ρ (.app f a) = vapp fuel
          --   (eval fuel f) (eval fuel a). Delegate to
          -- `vapp_realises` (mutual, fuel < fuel+1).
          simp only [Expr.closedAt, Bool.and_eq_true] at hcl
          unfold eval at heval
          simp only [Option.bind_eq_bind, Option.bind_eq_some] at heval
          obtain ⟨fV, hfV, aV, haV, hvapp⟩ := heval
          have hRfV := ihf' hfV henv hcl.1
          have hRaV := ihf' haV henv hcl.2
          show R (k+1) d v
            (.app (f.substEnv ρe) (a.substEnv ρe))
          exact vapp_realises hvapp hRfV hRaV
      | iota ann bExpr =>
          -- eval (.iota ann bExpr): eval ann → annV;
          -- v = .iota annV (Closure.mk' bExpr ρ).
          simp only [Expr.closedAt, Bool.and_eq_true] at hcl
          have hbb : bvarBound bExpr ≤ ρe.length + 1 :=
            bvarBound_le_of_closedAt hcl.2
          unfold eval at heval
          simp only [Option.bind_eq_bind, Option.bind_eq_some] at heval
          obtain ⟨annV, hann, hv⟩ := heval
          cases hv
          let cl := Closure.mk' bExpr ρ
          let anne := Expr.substEnv ρe ann
          let lifted := (Expr.bvar 0) :: ρe.map (·.shift 1 0)
          let bode := Expr.substEnv lifted bExpr
          show R (k+1) d (.iota annV cl) (Expr.substEnv ρe (.iota ann bExpr))
          have hsubst : Expr.substEnv ρe (.iota ann bExpr)
                      = .iota anne bode := by
            unfold Expr.substEnv; rfl
          rw [hsubst]
          unfold R
          -- Env-exposes clause (same shape as `.lam`).
          simp only [cl, Closure.mk']
          have hRann := ihf' hann henv hcl.1
          obtain ⟨hRL, hclb', hbody_eq⟩ :=
            closure_clause_witness henv hcl.2
          exact ⟨ρe.take (bvarBound bExpr - 1), anne,
                 hRann, hRL, hclb', by rw [hbody_eq]; exact Equiv_c.refl _ _⟩
      | fix ann bExpr =>
          -- Identical structure to .iota above.
          simp only [Expr.closedAt, Bool.and_eq_true] at hcl
          have hbb : bvarBound bExpr ≤ ρe.length + 1 :=
            bvarBound_le_of_closedAt hcl.2
          unfold eval at heval
          simp only [Option.bind_eq_bind, Option.bind_eq_some] at heval
          obtain ⟨annV, hann, hv⟩ := heval
          cases hv
          let cl := Closure.mk' bExpr ρ
          let anne := Expr.substEnv ρe ann
          let lifted := (Expr.bvar 0) :: ρe.map (·.shift 1 0)
          let bode := Expr.substEnv lifted bExpr
          show R (k+1) d (.«fix» annV cl) (Expr.substEnv ρe (.fix ann bExpr))
          have hsubst : Expr.substEnv ρe (.fix ann bExpr)
                      = .fix anne bode := by
            unfold Expr.substEnv; rfl
          rw [hsubst]
          unfold R
          simp only [cl, Closure.mk']
          have hRann := ihf' hann henv hcl.1
          obtain ⟨hRL, hclb', hbody_eq⟩ :=
            closure_clause_witness henv hcl.2
          exact ⟨ρe.take (bvarBound bExpr - 1), anne,
                 hRann, hRL, hclb', by rw [hbody_eq]; exact Equiv_c.refl _ _⟩
termination_by fuel
end

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

-- `R_zero` and `R_neutral_var` deleted 2026-04-21: unused.

-- `REnv_id`, `eval_unf_equiv`, `quoteClosure_eq_quote_openω_fresh`,
-- `quoteClosure_equiv_openω_fresh` all deleted 2026-04-21:
-- unused dead code (only mentioned in comments). Latter three
-- depended transitively on eval_realises' sorried base conjuncts,
-- so deletion also shrinks sorryAx-dependent code.

/-- Extract the env-realisation from `R`'s `.lam` clause.
At step-index `n+1` and `v = .lam dom cl`, this unfolds
directly. Now also returns `R (n+1) d dom dome` for the head
annotation (2026-04-21 R refactor). -/
theorem R_lam_clause {n d dom cl ea}
    (hR : R (n+1) d (.lam dom cl) ea) :
    ∃ ρe' dome,
      R (n+1) d dom dome ∧
      RList (n+1) d cl.env ρe' ∧
      cl.body.closedAt (ρe'.length + 1) = true ∧
      Equiv_c d ea (.lam dome
        (cl.body.substEnv (.bvar 0 :: ρe'.map (·.shift 1 0)))) := by
  unfold R at hR; exact hR

/-- Extract the env-realisation from `R`'s `.iota` clause. -/
theorem R_iota_clause {n d ann cl ea}
    (hR : R (n+1) d (.iota ann cl) ea) :
    ∃ ρe' anne,
      R (n+1) d ann anne ∧
      RList (n+1) d cl.env ρe' ∧
      cl.body.closedAt (ρe'.length + 1) = true ∧
      Equiv_c d ea (.iota anne
        (cl.body.substEnv (.bvar 0 :: ρe'.map (·.shift 1 0)))) := by
  unfold R at hR; exact hR

/-- Extract the env-realisation from `R`'s `.fix` clause. -/
theorem R_fix_clause {n d ann cl ea}
    (hR : R (n+1) d (.«fix» ann cl) ea) :
    ∃ ρe' anne,
      R (n+1) d ann anne ∧
      RList (n+1) d cl.env ρe' ∧
      cl.body.closedAt (ρe'.length + 1) = true ∧
      Equiv_c d ea (.fix anne
        (cl.body.substEnv (.bvar 0 :: ρe'.map (·.shift 1 0)))) := by
  unfold R at hR; exact hR

-- `Equiv.subst_target` and `quote_open_subst` deleted 2026-04-21:
-- both unused after whnfPi_fix_unfold_equiv was deleted. They
-- were deep infrastructure for the closure-quoting chain that
-- depended transitively on eval_realises' sorried base conjuncts.
-- If future work re-introduces the chain, they can be re-derived.

-- `quote_depth_shift_n` moved earlier (before R_depth_lift) 2026-04-22.

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

/-- Lift `quoteClosure` from `fuelω - 1` to `fuelω`. -/
theorem quoteClosureω {d : Nat} {cl : Closure} {e : Expr}
    (h : quoteClosure (fuelω - 1) d cl = some e) :
    quoteClosure fuelω d cl = some e :=
  quoteClosure_fuel_mono (Nat.sub_le _ _) h

/-- **Quoted expressions are closedAt their depth.** Combined mutual
induction on fuel. Every output of `quote d v` / `quoteClosure d cl`
/ `quoteNeutral d n` has free bvars bounded by `d` (or `d+1` for
closure bodies, which are quoted under one fresh binder).

This is a structural property of quote that gives us free
closedness witnesses everywhere quote succeeds — useful for
downstream closedness-carrying lemmas. -/
theorem quote_quoteClosure_quoteNeutral_closedAt :
    ∀ n,
    (∀ {d v e}, quote n d v = some e → e.closedAt d = true) ∧
    (∀ {d cl e}, quoteClosure n d cl = some e → e.closedAt (d+1) = true) ∧
    (∀ {d ne e}, quoteNeutral n d ne = some e → e.closedAt d = true) := by
  intro n
  induction n with
  | zero =>
    refine ⟨?_, ?_, ?_⟩ <;> intro <;> intro h <;> simp_all [quote_zero, quoteClosure_zero, quoteNeutral_zero]
  | succ n ih =>
    obtain ⟨ihq, ihc, ihn⟩ := ih
    refine ⟨?_, ?_, ?_⟩
    · intro d v e h
      unfold quote at h
      match v, h with
      | .type, h =>
        simp only [Option.some.injEq] at h; subst h
        simp [Expr.closedAt]
      | .neutral nne, h =>
        simp only [] at h
        exact ihn h
      | .lam dom cl, h =>
        simp only [Option.bind_eq_bind, Option.bind_eq_some,
                   Option.some.injEq] at h
        obtain ⟨dome, hdome, bodye, hbodye, heq⟩ := h
        subst heq
        simp only [Expr.closedAt, Bool.and_eq_true]
        exact ⟨ihq hdome, ihc hbodye⟩
      | .iota ann cl, h =>
        simp only [Option.bind_eq_bind, Option.bind_eq_some,
                   Option.some.injEq] at h
        obtain ⟨anne, hanne, bodye, hbodye, heq⟩ := h
        subst heq
        simp only [Expr.closedAt, Bool.and_eq_true]
        exact ⟨ihq hanne, ihc hbodye⟩
      | .«fix» ann cl, h =>
        simp only [Option.bind_eq_bind, Option.bind_eq_some,
                   Option.some.injEq] at h
        obtain ⟨anne, hanne, bodye, hbodye, heq⟩ := h
        subst heq
        simp only [Expr.closedAt, Bool.and_eq_true]
        exact ⟨ihq hanne, ihc hbodye⟩
    · intro d cl e h
      unfold quoteClosure at h
      simp only [Option.bind_eq_bind, Option.bind_eq_some] at h
      obtain ⟨v, _, hq⟩ := h
      exact ihq hq
    · intro d ne e h
      unfold quoteNeutral at h
      match ne, h with
      | .var k, h =>
        simp only [] at h
        split at h
        · next hlt =>
          simp only [Option.some.injEq] at h; subst h
          simp only [Expr.closedAt, decide_eq_true_eq]; omega
        · simp at h
      | .app n' v, h =>
        simp only [Option.bind_eq_bind, Option.bind_eq_some,
                   Option.some.injEq] at h
        obtain ⟨f, hf, a, ha, heq⟩ := h
        subst heq
        simp only [Expr.closedAt, Bool.and_eq_true]
        exact ⟨ihn hf, ihq ha⟩
      | .stuckRec f a, h =>
        simp only [Option.bind_eq_bind, Option.bind_eq_some,
                   Option.some.injEq] at h
        obtain ⟨fe, hfe, ae, hae, heq⟩ := h
        subst heq
        simp only [Expr.closedAt, Bool.and_eq_true]
        exact ⟨ihq hfe, ihq hae⟩

/-- Specialisation: `quote` output is `closedAt d`. -/
theorem quote_closedAt {fuel d v e} (h : quote fuel d v = some e) :
    e.closedAt d = true :=
  (quote_quoteClosure_quoteNeutral_closedAt fuel).1 h

/-- Specialisation: `quoteClosure` body output is `closedAt (d+1)`. -/
theorem quoteClosure_closedAt {fuel d cl e}
    (h : quoteClosure fuel d cl = some e) :
    e.closedAt (d+1) = true :=
  (quote_quoteClosure_quoteNeutral_closedAt fuel).2.1 h

/-- Specialisation: `quoteNeutral` output is `closedAt d`. -/
theorem quoteNeutral_closedAt {fuel d ne e}
    (h : quoteNeutral fuel d ne = some e) :
    e.closedAt d = true :=
  (quote_quoteClosure_quoteNeutral_closedAt fuel).2.2 h

-- `fullyQuotable` implies `levelsBelow` structurally (the .var
-- clause of both requires `k < d`; recursive cases mirror each other).
-- `Val.levelsBelow_of_fullyQuotable` + related — moved earlier
-- (before R_depth_lift) 2026-04-22 for Tier 0 refactor.

-- `Val.fullyQuotable_mono` + related — moved earlier (before
-- R_depth_lift) 2026-04-22 for Tier 0 refactor.

theorem quote_lam {d : Nat} {dom : Val} {cl : Closure} {e : Expr}
    (h : quote fuelω d (.lam dom cl) = some e) :
    ∃ dome bodye,
      quote (fuelω - 1) d dom = some dome ∧
      quoteClosure (fuelω - 1) d cl = some bodye ∧
      e = .lam dome bodye := by
  rw [fuelω_succ] at h; unfold quote at h
  simp only [Option.bind_eq_bind, Option.bind_eq_some,
             Option.some.injEq] at h
  obtain ⟨de, hde, be, hbe, heq⟩ := h
  exact ⟨de, be, hde, hbe, heq.symm⟩

theorem quote_iota {d : Nat} {ann : Val} {cl : Closure} {e : Expr}
    (h : quote fuelω d (.iota ann cl) = some e) :
    ∃ anne bodye,
      quote (fuelω - 1) d ann = some anne ∧
      quoteClosure (fuelω - 1) d cl = some bodye ∧
      e = .iota anne bodye := by
  rw [fuelω_succ] at h; unfold quote at h
  simp only [Option.bind_eq_bind, Option.bind_eq_some,
             Option.some.injEq] at h
  obtain ⟨de, hde, be, hbe, heq⟩ := h
  exact ⟨de, be, hde, hbe, heq.symm⟩

theorem quote_fix {d : Nat} {ann : Val} {cl : Closure} {e : Expr}
    (h : quote fuelω d (.«fix» ann cl) = some e) :
    ∃ anne bodye,
      quote (fuelω - 1) d ann = some anne ∧
      quoteClosure (fuelω - 1) d cl = some bodye ∧
      e = .«fix» anne bodye := by
  rw [fuelω_succ] at h; unfold quote at h
  simp only [Option.bind_eq_bind, Option.bind_eq_some,
             Option.some.injEq] at h
  obtain ⟨de, hde, be, hbe, heq⟩ := h
  exact ⟨de, be, hde, hbe, heq.symm⟩

/-!
### Hypothesis bundles
-/

/-- The seen-set quotes into `Se`. With depth-tagged `Seen`,
each Val-pair `(a,b) ∈ S` corresponds to an entry
`(d, ae, be) ∈ Se` where `d ≤ Γ.size` (entries recorded at the
current depth or shallower) and `quote_d a = ae`, `quote_d b
= be`. The bridge's `.hyp` case uses `Subtype'.hyp` with
`d ≤ Γe.length` and `quote_depth_shift_n` to bridge `quote_d`
to `quote_{Γ.size}`. -/
abbrev QuotesSeen (S : List (Val × Val)) (Γ : TyCtx) (Se : Seen) : Prop :=
  ∀ p ∈ S, ∃ pe ∈ Se,
    pe.1 ≤ Γ.size ∧
    quote fuelω pe.1 p.1 = some pe.2.1 ∧
    quote fuelω pe.1 p.2 = some pe.2.2

/-- The type context quotes into `Γe` at matching de Bruijn
indices. `Γ` is level-indexed (`Γ[k]` = type of `.var k`);
`Γe` is index-indexed (`Γe[i]` = type of `.bvar i`). The
quote depth is `k`: entry `k` was *added* when `Γ` had size
`k`, so its Val's neutrals reference levels `0..k-1` and
should quote at depth `k` (not `k+1`) to land in the right
`Γe`-relative slot. (`tyCheck_sound_open`'s `.lam` arm is
the witness — `Subtype'.lam` extends `Γe` with `domB` at
index 0, and `domB` is `quote |Γ| domV`.)

The `Γ.size = Γe.length` conjunct is the length invariant
that `OpenCtx.hlen` maintains at the top level. Making it
explicit in `QuotesCtx` lets the `.hyp` case of
`SubN_to_Subtype'` rewrite between the motive's `Γ.size`
shift amount and `Subtype'.hyp`'s `Γe.length` shift amount. -/
abbrev QuotesCtx (Γ : TyCtx) (Γe : Ctx) : Prop :=
  Γ.size = Γe.length ∧
  (∀ k τ, Γ[k]? = some τ →
    ∃ τe, Γe.get? (Γ.size - 1 - k) = some τe ∧
          quote fuelω k τ = some τe) ∧
  (∀ k τ, Γ[k]? = some τ → Val.levelsBelow k τ)

/-!
### The mutual bridge

Three theorems proven by simultaneous structural recursion
on `SubV`/`SubN`/`SynthN`, using the joint recursor
`SubV.rec`. Each motive packages the quote hypotheses; the
recursor supplies one IH per recursive premise.
-/

-- `SubN_to_Subtype'` and `SynthN_to_Subtype'` deleted
-- 2026-04-21. Both were sorry-ridden (each case of their
-- joint-recursor application required tier-2 realisability
-- threading that's not yet built); their only external
-- consumer (`SubV_to_Subtype'.neutral_struct`) now sorries
-- inline. Future work: re-derive via a proper `MR`-augmented
-- motive that carries realisability + quote-totality
-- hypotheses.

-- `SubV_to_Subtype'` deleted 2026-04-21: 11/15 cases were sorried
-- (closure-opening + neutral_ascent). Its only caller
-- (`subCheckVal_sound_open`) also deleted; downstream callers
-- (tyCheck_sound_open etc.) now sorry the subtype derivation
-- directly. Future work: re-derive via `MR`-augmented motive
-- carrying realisability hypotheses.

/-!
## Open-context `tyCheck`/`tyInfer` soundness

`tyCheck_sound_closed` (Soundness.lean) is at `Γ = #[]`/`ρ = []`/
`Γe = []`. Its `.lam`/`.letE` arms recurse at non-empty `Γ`,
which the closed IH cannot reach. The open generalisation
here threads a context-bundle `OpenCtx Γ ρ Γe` through the
mutual induction; the closed forms in `Soundness.lean`
specialise it at `OpenCtx.empty`.

**Statement shape.** The expected type comes as `(τV : Val)`
plus its quote `(τe, hqτ)`, *not* a source `(τ : Expr)` with
`eval τ = τV`. This is because the recursive cases (`.letE`'s
binder type from `letBinderType`; `tyInfer`'s result) supply
a `Val` directly with no source `Expr` to point at. The
closed wrapper does `eval [] τ → τV` then bridges `τe ≡ τ`
via `eval_quote_equiv_closed`.

**Conclusion.** `Subtype' [] Γe e τe` — the source `e` (open,
with bvars into `Γe`) is below the *quoted* expected type at
the declarative context. The seen-set is always `[]` since
`tyCheck`'s `subCheckVal` calls start at empty seen.
-/

-- `subCheckVal_sound_open` deleted 2026-04-21 along with
-- `SubV_to_Subtype'`. Callers (in tyCheck_sound_open's mutual)
-- now sorry the derivation directly — a net declaration-sorry
-- reduction since SubV_to_Subtype's warning disappears.

/-- The open-context invariant for `tyCheck`/`tyInfer`
soundness. Carries an explicit Expr-level substitution
`ρe` realised by the runtime `ρ` (via `REnv`), so the
conclusion can be stated as `Subtype' [] Γe (e.substEnv
ρe) τe` — which is *correct* for both fresh-neutral and
let-bound `ρ` entries (the previous `Equiv e' e at Γe`
form was false for the latter; see `push_let`).

  - `hΓ` for `subCheckVal_sound_open`;
  - `hρq` for `REnv_depth_lift` and `R_depth_lift` (each
    `ρ` entry quotes at the current depth);
  - `henv` (replacing the ad-hoc `hρeq`) packages the
    realisation; the eval-quote-equiv property is
    *derived* below as `OpenCtx.eq`. -/
structure OpenCtx (Γ : TyCtx) (ρ : Env) (Γe : Ctx)
    (ρe : List Expr) : Prop where
  hΓ : QuotesCtx Γ Γe
  hρq : ∀ (k : Nat) (v : Val), ρ[k]? = some v →
        ∃ we, quote fuelω Γ.size v = some we
  /-- Levelbound invariant: every entry of `ρ` has neutral-var
  levels `< Γ.size`. Maintained by `push_fresh` (new head
  `.var Γ.size` has level `Γ.size < Γ.size+1`) and by
  `push_let` (new head `valV` from `eval ρ val` has levels
  `< Γ.size` by `eval_levelsBelow`, then `< Γ.size+1` by mono).
  Used by `quote_depth_shift` at call sites (via
  `hρlvl_lift`). -/
  hρlvl : ∀ (k : Nat) (v : Val), ρ[k]? = some v →
          Val.levelsBelow Γ.size v
  /-- Closedness of substituted-environment entries. Each
  `ρe[k]` is `closedAt Γ.size` — it has no free bvars beyond
  the current depth. Maintained by `empty` (vacuous), `push_fresh`
  (head `.bvar 0` closedAt 1 ≤ Γ.size+1; tail entries shift
  `closedAt Γ.size → closedAt Γ.size+1`), and `push_let` (head
  `val.substEnv ρe` closedAt Γ.size from `val.closedAt ρe.length`
  + tail entries closedAt Γ.size; then shift to Γ.size+1).
  This invariant is Path A's enabler: with it, shifts of ρe
  entries at cutoff 0 lift to closedAt Γ.size+1, and downstream
  closedness-carrying Equiv.shift variants can fire. -/
  hρecl : ∀ (k : Nat) (e : Expr), ρe[k]? = some e →
          e.closedAt Γ.size = true
  /-- Recursive full quotability for each ρ entry. -/
  hρfq : ∀ (k : Nat) (v : Val), ρ[k]? = some v →
         Val.fullyQuotable Γ.size v
  henv : REnv 1 Γ.size ρ ρe
  /-- All four contexts grow in lockstep (`empty` starts at
  0; both `push_*` add 1 to each). `tyInfer_sound_open .bvar`
  needs this to turn `hcl : k < ρe.length` into `k < Γ.size`
  for the level↔index arithmetic. -/
  hlen : Γ.size = ρe.length
  /-- Each substituted entry has its declared context type:
  `ρe[k] ⊑ Γe[k].shift (k+1) 0`. This is `Subtype'.bvar`'s
  conclusion, generalised from `.bvar k` to whatever `ρe[k]`
  realises it. `tyInfer_sound_open .bvar` reads this
  directly. `push_fresh` discharges `k=0` via `Subtype'.bvar`
  (the head IS `.bvar 0`); `push_let` via the caller's
  `hval_le` (the let-bound value's typing). The `k>0` tail
  lifts via `ctx_extend [head]`. -/
  hwf : ∀ k w τe, ρe[k]? = some w → Γe.get? k = some τe →
        Subtype' [] Γe w (τe.shift (k+1) 0)

/-- Derived eval-quote-equiv: evaluating `e` under `ρ` and
quoting gives something `Equiv` to `e.substEnv ρe`. This
is the open form of `eval_quote_equiv_closed`. -/
theorem OpenCtx.eq {Γ ρ Γe ρe} (hctx : OpenCtx Γ ρ Γe ρe)
    {fuel unf e v} (heval : eval fuel unf ρ e = some v)
    (hcl : e.closedAt ρe.length = true)
    {e'} (hq : quote fuelω Γ.size v = some e') :
    Subtype' [] Γe e' (e.substEnv ρe) ∧
    Subtype' [] Γe (e.substEnv ρe) e' := by
  have heq : Equiv_c Γ.size e' (e.substEnv ρe) :=
    R_quote_equiv Nat.one_pos (eval_realises heval hctx.henv hcl) hq
  exact heq (Nat.le_of_eq hctx.hΓ.1)

/-- The empty context is trivially open. `ρe = []`. -/
theorem OpenCtx.empty : OpenCtx #[] [] [] [] where
  hΓ := ⟨rfl, fun _ _ hk => by simp at hk, fun _ _ hk => by simp at hk⟩
  hρq := fun _ _ hk => by simp at hk
  hρlvl := fun _ _ hk => by simp at hk
  hρecl := fun _ _ hk => by simp at hk
  hρfq := fun _ _ hk => by simp at hk
  henv := ⟨rfl, fun _ _ hk => by simp at hk⟩
  hlen := rfl
  hwf := fun _ _ _ hk => by simp at hk

/-- Open `eval_quotable`, with the `hnfq` side condition
that makes it provable. The previous `hρ`-only form is
**false** (DECISION-LOG 2026-04-19): `hρ` is vacuous at
empty `ρ`, and `eval 2 _ [] (.lam .type huge)` succeeds at
fuel 2 while `quoteClosure` re-evals `huge` unboundedly.
With `hnfq` the proof is `eval_fuel_mono`-transport, same
as `quote_total_on_eval`. -/
theorem eval_quotable_open {fuel unf d : Nat} {ρ : Env}
    {e : Expr} {v : Val}
    (hfuel : fuel ≤ fuelω)
    (hnfq : ((eval fuelω unf ρ e).bind (quote fuelω d)).isSome)
    (heval : eval fuel unf ρ e = some v) :
    ∃ ve, quote fuelω d v = some ve := by
  rw [eval_fuel_mono hfuel heval] at hnfq
  simp only [Option.some_bind] at hnfq
  exact Option.isSome_iff_exists.mp hnfq

/-- Sorry-free quote-totality wrapper: caller supplies the
`(hnfq)` witness directly (route (a) — per-call hypothesis).

At `OpenCtx.empty`, this is the closed-form `(hnf)` the
`Soundness.lean` wrappers already thread; under `push_fresh`
/`push_let`, derive it via one `quoteClosure`/`bind`-step
from the enclosing call's `(hnfq)`.

The original `openNf_holds` + `OpenCtx.eval_quotes`
(non-primed) were deleted 2026-04-21. `openNf_holds` was
false as stated (`eval 2 _ [] (.lam .type huge)` counterexample:
eval succeeds at fuel 2 regardless of `huge`'s size, but
`quoteClosure` re-evals `huge` unboundedly). All call sites
now use `eval_quotes'` with the witness either threaded from
the top-level `hnfe` / `hnfτ` or supplied via `by sorry` at
sites inside already-sorried theorems. -/
theorem OpenCtx.eval_quotes' {Γ ρ Γe ρe} (_hctx : OpenCtx Γ ρ Γe ρe)
    {fuel unf e v} (hfuel : fuel ≤ fuelω)
    (hnfq : ((eval fuelω unf ρ e).bind (quote fuelω Γ.size)).isSome)
    (heval : eval fuel unf ρ e = some v) :
    ∃ ve, quote fuelω Γ.size v = some ve :=
  eval_quotable_open hfuel hnfq heval

/-- Lifts an `OpenCtx.hwf` tail through one context
extension. Shared by `push_fresh`/`push_let` for the `k>0`
case: `ρe[m]` shifts to `ρe[m].shift 1 0`, the goal type
`Γe[m].shift (m+2) 0 = (Γe[m].shift (m+1) 0).shift 1 0` by
`shift_succ`, and `ctx_extend [head]` lifts the inner
derivation. -/
private theorem hwf_lift_tail {Γe : Ctx} {ρe : List Expr}
    (hwf : ∀ k w τe, ρe[k]? = some w → Γe.get? k = some τe →
           Subtype' [] Γe w (τe.shift (k+1) 0))
    (head : Expr) :
    ∀ m w τe,
      (ρe.map (·.shift 1 0))[m]? = some w →
      Γe.get? m = some τe →
      Subtype' [] (head :: Γe) w (τe.shift (m+2) 0) := by
  intro m w τe hw hτe
  rw [List.getElem?_map] at hw
  obtain ⟨w0, hw0, rfl⟩ := Option.map_eq_some'.mp hw
  have hinner := hwf m w0 τe hw0 hτe
  have hext := Subtype'.ctx_extend (S := []) [head] hinner
  simpa [Expr.shift_succ, List.map_nil,
         List.singleton_append] using hext

/-- Lift each `ρ`-entry's quote-witness to depth `d+1`. -/
private theorem hρq_lift {d : Nat} {ρ : Env}
    (hρq : ∀ (k : Nat) (v : Val), ρ[k]? = some v →
           ∃ we, quote fuelω d v = some we)
    (hρlvl : ∀ (k : Nat) (v : Val), ρ[k]? = some v →
             Val.levelsBelow d v) :
    ∀ (k : Nat) (v : Val), ρ[k]? = some v →
    ∃ we, quote fuelω (d + 1) v = some we := by
  intro k v hk
  obtain ⟨we, hwe⟩ := hρq k v hk
  exact ⟨we.shift 1 0, quote_depth_shift (hρlvl k v hk) hwe⟩

/-- `hρlvl`-lift companion: lift each ρ-entry's `levelsBelow d`
to `levelsBelow (d+1)` (by monotonicity). -/
private theorem hρlvl_lift {d : Nat} {ρ : Env}
    (hρlvl : ∀ (k : Nat) (v : Val), ρ[k]? = some v →
             Val.levelsBelow d v) :
    ∀ (k : Nat) (v : Val), ρ[k]? = some v →
    Val.levelsBelow (d + 1) v := by
  intro k v hk
  exact Val.levelsBelow_mono (Nat.le_succ _) v (hρlvl k v hk)

/-- `QuotesCtx` extension under `Γ.push`. The new head
`Γ'[d] = τ` quotes at `d+1` to `Γe'[0] = τe` (given). Each
old `Γ[k]` quotes at `k+1` (unchanged — `QuotesCtx`'s quote
depth is per-entry, not the outer `Γ.size`); only the
*lookup index* into `Γe'` shifts by one (`Γe'[i+1] =
Γe[i]`). -/
theorem QuotesCtx.push {Γ : TyCtx} {Γe : Ctx}
    (hΓ : QuotesCtx Γ Γe)
    {τ : Val} {τe : Expr}
    (hqτ : quote fuelω Γ.size τ = some τe)
    (hτlvl : Val.levelsBelow Γ.size τ) :
    QuotesCtx (Γ.push τ) (τe :: Γe) := by
  refine ⟨?hlen, ?hquote, ?hlvl⟩
  case hlen => simp [Array.size_push, hΓ.1]
  case hquote =>
    intro k τ' hk
    rw [Array.getElem?_push] at hk
    split at hk
    · -- k = Γ.size: new head.
      rename_i hk_eq
      cases hk
      refine ⟨τe, ?_, hk_eq ▸ hqτ⟩
      have : (Γ.push τ).size - 1 - k = 0 := by
        simp only [Array.size_push]; omega
      rw [this]; rfl
    · -- k ≠ Γ.size: old entry, Γ[k]? = some τ'.
      rename_i hk_ne
      obtain ⟨τe', hτe', hqτ'⟩ := hΓ.2.1 k τ' hk
      refine ⟨τe', ?_, hqτ'⟩
      have hk_lt : k < Γ.size :=
        (Array.getElem?_eq_some_iff.mp hk).1
      have hidx : (Γ.push τ).size - 1 - k
                = (Γ.size - 1 - k) + 1 := by
        simp only [Array.size_push]; omega
      rw [hidx]; simpa using hτe'
  case hlvl =>
    intro k τ' hk
    rw [Array.getElem?_push] at hk
    split at hk
    · rename_i hk_eq
      cases hk
      exact hk_eq ▸ hτlvl
    · rename_i hk_ne
      exact hΓ.2.2 k τ' hk

/-- Pushing a fresh neutral preserves the invariant.
`ρe' = .bvar 0 :: ρe.map shift` — the standard de-Bruijn
lift. Closes via `REnv_lift` (which packages
`R_fresh_bvar0` for the head and `REnv_depth_lift` for the
tail) and `QuotesCtx.push`. -/
theorem OpenCtx.push_fresh {Γ ρ Γe ρe} (hctx : OpenCtx Γ ρ Γe ρe)
    {τ : Val} {τe : Expr}
    (hqτ : quote fuelω Γ.size τ = some τe)
    (hτlvl : Val.levelsBelow Γ.size τ) :
    OpenCtx (Γ.push τ) (.neutral (.var Γ.size) :: ρ)
            (τe :: Γe) (.bvar 0 :: ρe.map (·.shift 1 0)) where
  hΓ := QuotesCtx.push hctx.hΓ hqτ hτlvl
  hρq := by
    intro k v hk
    cases k with
    | zero =>
        simp only [List.getElem?_cons_zero, Option.some.injEq] at hk
        subst hk
        exact ⟨.bvar 0,
          by simpa [Array.size_push] using
             quote_neutral_var_fwd (lvl := Γ.size)
               (Nat.lt_succ_self _)⟩
    | succ m =>
        simp only [List.getElem?_cons_succ] at hk
        have h := hρq_lift (d := Γ.size) hctx.hρq hctx.hρlvl m v hk
        simpa [Array.size_push] using h
  hρlvl := by
    intro k v hk
    cases k with
    | zero =>
        simp only [List.getElem?_cons_zero, Option.some.injEq] at hk
        subst hk
        -- .neutral (.var Γ.size) has level Γ.size < Γ.size+1
        simp only [Array.size_push]
        unfold Val.levelsBelow Neutral.levelsBelow
        exact Nat.lt_succ_self _
    | succ m =>
        simp only [List.getElem?_cons_succ] at hk
        have h := hρlvl_lift (d := Γ.size) hctx.hρlvl m v hk
        simpa [Array.size_push] using h
  hρecl := by
    intro k e hk
    cases k with
    | zero =>
        simp only [List.getElem?_cons_zero, Option.some.injEq] at hk
        subst hk
        simp only [Array.size_push, Expr.closedAt, decide_eq_true_eq]
        omega
    | succ m =>
        simp only [List.getElem?_cons_succ] at hk
        simp only [Array.size_push]
        simp only [List.getElem?_map, Option.map_eq_some'] at hk
        obtain ⟨e', he', heq⟩ := hk
        subst heq
        have hcl := hctx.hρecl m e' he'
        exact Expr.shift_closedAt e' _ 1 0 (Nat.zero_le _) hcl
  hρfq := by
    intro k v hk
    cases k with
    | zero =>
        simp only [List.getElem?_cons_zero, Option.some.injEq] at hk
        subst hk
        simp only [Array.size_push, Val.fullyQuotable, Neutral.fullyQuotable]
        omega
    | succ m =>
        simp only [List.getElem?_cons_succ] at hk
        simp only [Array.size_push]
        exact Val.fullyQuotable_mono (Nat.le_succ _) v (hctx.hρfq m v hk)
  henv := by
    simpa [Array.size_push] using
      REnv_lift hctx.henv hctx.hρq hctx.hρlvl hctx.hρfq
  hlen := by simp [Array.size_push, List.length_map, hctx.hlen]
  hwf := by
    intro k w τe' hw hτe'
    cases k with
    | zero =>
        simp only [List.getElem?_cons_zero, List.get?_cons_zero,
                   Option.some.injEq] at hw hτe'
        subst hw hτe'
        exact Subtype'.bvar (Γ := τe :: Γe) (k := 0) rfl
    | succ m =>
        simp only [List.getElem?_cons_succ,
                   List.get?_cons_succ] at hw hτe'
        exact hwf_lift_tail hctx.hwf τe m w τe' hw hτe'

/-- Pushing a `letBinderType`-result preserves the
invariant. `ρe' = (val.substEnv ρe).shift 1 0 :: ρe.map
shift` — the let-bound *source* (substituted at the outer
`ρe`) realises `valV`, depth-lifted to `d+1`. **Closes**
via `eval_realises` (giving `R 1 d valV (val.substEnv
ρe)`), `R_depth_lift` (lifting to `d+1`), `REnv_depth_lift`
(lifting the tail), and `REnv_cons` (assembling). -/
theorem OpenCtx.push_let {Γ ρ Γe ρe} (hctx : OpenCtx Γ ρ Γe ρe)
    {fuel unf : Nat} (hfuel : fuel ≤ fuelω)
    {val : Expr} {valV valTy : Val} {valTye : Expr}
    (hev : eval fuel unf ρ val = some valV)
    (hnfq : ((eval fuelω unf ρ val).bind (quote fuelω Γ.size)).isSome)
    (hclv : val.closedAt ρe.length = true)
    (hqτ : quote fuelω Γ.size valTy = some valTye)
    (hτlvl : Val.levelsBelow Γ.size valTy)
    (hval_le : Subtype' [] Γe (val.substEnv ρe) valTye) :
    OpenCtx (Γ.push valTy) (valV :: ρ)
            (valTye :: Γe)
            ((val.substEnv ρe).shift 1 0
              :: ρe.map (·.shift 1 0)) where
  hΓ := QuotesCtx.push hctx.hΓ hqτ hτlvl
  hρq := by
    intro k v hk
    cases k with
    | zero =>
        simp only [List.getElem?_cons_zero, Option.some.injEq] at hk
        subst hk
        obtain ⟨qe, hqe⟩ := hctx.eval_quotes' hfuel hnfq hev
        -- Derive levelsBelow Γ.size for valV from eval_levelsBelow:
        have henvLvl : Closure.envLevelsBelow Γ.size ρ :=
          Closure.envLevelsBelow_of_getElem? (fun k v hk =>
            hctx.hρlvl k v (by rw [List.get?_eq_getElem?] at hk; exact hk))
        have hevω := eval_fuel_mono hfuel hev
        have hvlvl : Val.levelsBelow Γ.size valV :=
          eval_levelsBelow hevω henvLvl
        exact ⟨qe.shift 1 0,
          by simpa [Array.size_push] using
             quote_depth_shift hvlvl hqe⟩
    | succ m =>
        simp only [List.getElem?_cons_succ] at hk
        have h := hρq_lift (d := Γ.size) hctx.hρq hctx.hρlvl m v hk
        simpa [Array.size_push] using h
  hρlvl := by
    intro k v hk
    cases k with
    | zero =>
        simp only [List.getElem?_cons_zero, Option.some.injEq] at hk
        subst hk
        have henvLvl : Closure.envLevelsBelow Γ.size ρ :=
          Closure.envLevelsBelow_of_getElem? (fun k v hk =>
            hctx.hρlvl k v (by rw [List.get?_eq_getElem?] at hk; exact hk))
        have hevω := eval_fuel_mono hfuel hev
        have hvlvl : Val.levelsBelow Γ.size valV :=
          eval_levelsBelow hevω henvLvl
        simpa [Array.size_push] using
          Val.levelsBelow_mono (Nat.le_succ _) valV hvlvl
    | succ m =>
        simp only [List.getElem?_cons_succ] at hk
        have h := hρlvl_lift (d := Γ.size) hctx.hρlvl m v hk
        simpa [Array.size_push] using h
  hρecl := by
    intro k e hk
    cases k with
    | zero =>
        simp only [List.getElem?_cons_zero, Option.some.injEq] at hk
        subst hk
        -- Head entry: (val.substEnv ρe).shift 1 0
        -- val.closedAt ρe.length = Γ.size; every ρe[j] closedAt Γ.size;
        -- so val.substEnv ρe closedAt Γ.size, then shift bumps to Γ.size+1.
        simp only [Array.size_push]
        have hvcl : (val.substEnv ρe).closedAt Γ.size = true :=
          substEnv_closedAt (n := Γ.size) (hbound := hctx.hlen ▸ hclv)
            hctx.hρecl
        exact Expr.shift_closedAt (val.substEnv ρe) Γ.size 1 0
          (Nat.zero_le _) hvcl
    | succ m =>
        simp only [List.getElem?_cons_succ] at hk
        simp only [Array.size_push]
        simp only [List.getElem?_map, Option.map_eq_some'] at hk
        obtain ⟨e', he', heq⟩ := hk
        subst heq
        have hcl := hctx.hρecl m e' he'
        exact Expr.shift_closedAt e' _ 1 0 (Nat.zero_le _) hcl
  hρfq := by
    intro k v hk
    cases k with
    | zero =>
        simp only [List.getElem?_cons_zero, Option.some.injEq] at hk
        subst hk
        simp only [Array.size_push]
        -- Head valV: use eval_preserves_fullyQuotable.
        have hρenv : Closure.envFullyQuotable Γ.size ρ :=
          Closure.envFullyQuotable_of_getElem?
            (fun k v hk => hctx.hρq k v hk)
            (fun k v hk => hctx.hρfq k v hk)
        have hlen_eq : ρ.length = ρe.length := hctx.henv.1
        have hclv' : val.closedAt ρ.length = true := hlen_eq ▸ hclv
        have hvfq : Val.fullyQuotable Γ.size valV :=
          eval_preserves_fullyQuotable hev hρenv hclv'
        exact Val.fullyQuotable_mono (Nat.le_succ _) valV hvfq
    | succ m =>
        simp only [List.getElem?_cons_succ] at hk
        simp only [Array.size_push]
        exact Val.fullyQuotable_mono (Nat.le_succ _) v (hctx.hρfq m v hk)
  henv := by
    have hRval := eval_realises hev hctx.henv hclv
    obtain ⟨qe, hqe⟩ := hctx.eval_quotes' hfuel hnfq hev
    -- Derive levelsBelow Γ.size for valV (for R_depth_lift):
    have henvLvl : Closure.envLevelsBelow Γ.size ρ :=
      Closure.envLevelsBelow_of_getElem? (fun k v hk =>
        hctx.hρlvl k v (by rw [List.get?_eq_getElem?] at hk; exact hk))
    have hevω := eval_fuel_mono hfuel hev
    have hvlvl : Val.levelsBelow Γ.size valV :=
      eval_levelsBelow hevω henvLvl
    -- fullyQuotable on valV via eval_preserves_fullyQuotable.
    have hρenv : Closure.envFullyQuotable Γ.size ρ :=
      Closure.envFullyQuotable_of_getElem?
        (fun k v hk => hctx.hρq k v hk)
        (fun k v hk => hctx.hρfq k v hk)
    have hlen_eq : ρ.length = ρe.length := hctx.henv.1
    have hclv' : val.closedAt ρ.length = true := hlen_eq ▸ hclv
    have hvfq : Val.fullyQuotable Γ.size valV :=
      eval_preserves_fullyQuotable hev hρenv hclv'
    have hRval' := R_depth_lift hvlvl hvfq hqe hRval
    have htail := REnv_depth_lift hctx.henv hctx.hρq hctx.hρlvl hctx.hρfq
    simpa [Array.size_push] using REnv_cons htail hRval'
  hlen := by simp [Array.size_push, List.length_map, hctx.hlen]
  hwf := by
    intro k w τe' hw hτe'
    cases k with
    | zero =>
        simp only [List.getElem?_cons_zero, List.get?_cons_zero,
                   Option.some.injEq] at hw hτe'
        subst hw hτe'
        have := Subtype'.ctx_extend (S := []) [valTye] hval_le
        simpa using this
    | succ m =>
        simp only [List.getElem?_cons_succ,
                   List.get?_cons_succ] at hw hτe'
        exact hwf_lift_tail hctx.hwf valTye m w τe' hw hτe'

-- whnfPi_fix_unfold_equiv, whnfPi_go_sound_open,
-- whnfPi_sound_open, whnfPi_sound (in Soundness.lean) all
-- deleted 2026-04-21. The fix_unfold_equiv building block
-- transitively depended on quote_open_subst's sorry chain
-- (via eval_realises); nothing in the current proof chain uses
-- it, and if future work needs it it can be re-derived with
-- fewer sorries once eval_realises is closed.

mutual

/-- Open-context `tyInfer` soundness. The conclusion bundles
quote-existence so callers (the `tyCheckFallback` arm) don't
need a separate quote-totality side-lemma.

**Note on `.fix`/`.iota` (A9)**: `tyInfer` returns the bare
annotation, which is *not* sound (`(.fix Nat_ unit_) ⋢
Nat_`). This case is therefore unprovable as stated. The
mitigation: every *caller* of `tyInfer` that needs a
verified type goes through `tyCheck`'s `.fix`/`.iota` arm or
`letBinderType` (both of which verify); `tyCheckFallback`'s
`some`-path is the only direct consumer of an unverified
`tyInfer` result, and *that* path is exactly the residual
A9 hole the verifier-on-`c5914db` flagged for `.app`-chains
with bad-fix heads. So `tyInfer_sound_open` below carries
an additional hypothesis `(hwf : <e contains no ill-formed
fix/ι>)` *or* the `.fix`/`.iota` arm is sorried with this
note — taking the latter for now. -/
theorem tyInfer_sound_open
    {fuel : Nat} (hfuel : fuel ≤ fuelω)
    {Γ : TyCtx} {ρ : Env} {Γe : Ctx} {ρe : List Expr}
    (hctx : OpenCtx Γ ρ Γe ρe)
    {e : Expr} {τV : Val}
    (hcl : e.closedAt ρe.length = true)
    (h : tyInfer fuel Γ ρ e = .ok (some τV)) :
    ∃ τe, quote fuelω Γ.size τV = some τe ∧
          Subtype' [] Γe (e.substEnv ρe) τe := by
  match fuel, hfuel, h with
  | 0, _, h => simp [tyInfer] at h
  | fuel + 1, hfuel, h =>
    have hfuel' : fuel ≤ fuelω := Nat.le_of_succ_le hfuel
    unfold tyInfer at h
    split at h
    -- .bvar k
    · rename_i _e' k _h'
      simp only [Expr.closedAt, decide_eq_true_eq] at hcl
      have hlen := hctx.hlen
      have hk_lt : k < Γ.size := by omega
      split at h
      case isFalse => simp_all
      case isTrue hidx_lt =>
      simp only [Except.ok.injEq, Option.some.injEq] at h
      subst h
      -- τV = Γ[Γ.size-1-k]. From `hctx.hΓ` get its quote
      -- at depth `Γ.size-1-k` and the matching `Γe[k]`.
      have hΓk : Γ[Γ.size - 1 - k]? = some Γ[Γ.size - 1 - k] := by
        simp [Array.getElem?_eq_getElem, hidx_lt]
      obtain ⟨τe0, hΓe, hqτe0⟩ := hctx.hΓ.2.1 _ _ hΓk
      have hτlvl : Val.levelsBelow (Γ.size - 1 - k) _ :=
        hctx.hΓ.2.2 _ _ hΓk
      have hidx : Γ.size - 1 - (Γ.size - 1 - k) = k := by omega
      rw [hidx] at hΓe
      -- Lift the quote from depth `Γ.size-1-k` to `Γ.size`:
      have hqτe := quote_depth_shift_n (d := Γ.size) hτlvl
        (show Γ.size - 1 - k ≤ Γ.size by omega) hqτe0
      have hshamt : Γ.size - (Γ.size - 1 - k) = k + 1 := by omega
      rw [hshamt] at hqτe
      -- The substituted bvar `(.bvar k).substEnv ρe = ρe[k]`
      -- has its declared type by `hctx.hwf`:
      refine ⟨τe0.shift (k+1) 0, hqτe, ?_⟩
      simp only [Expr.substEnv, hcl, ↓reduceIte,
                 getElem!_pos ρe k hcl]
      exact hctx.hwf k _ τe0 (List.getElem?_eq_getElem hcl) hΓe
    -- .type
    · simp only [Except.ok.injEq, Option.some.injEq] at h
      subst h
      exact ⟨.type, quote_type,
        by simpa [Expr.substEnv] using Subtype'.refl Expr.type⟩
    -- .asc e' τ
    · rename_i e' τ
      simp only [Expr.closedAt, Bool.and_eq_true] at hcl
      simp only [bind, Except.bind] at h
      split at h
      case h_2 => simp_all
      case h_1 τV0 hτV0 =>
      split at h
      · simp_all
      next okI hokI =>
      cases okI with
      | false => simp_all
      | true =>
        simp only [Bool.not_true, Bool.false_eq_true,
                   ↓reduceIte, Except.ok.injEq,
                   Option.some.injEq] at h
        subst h
        obtain ⟨τe, hqτV⟩ := hctx.eval_quotes' hfuel' (by sorry) hτV0
        have hsub := tyCheck_sound_open hfuel' hctx
          hcl.1 hqτV hokI
        exact ⟨τe, hqτV,
          by simpa [Expr.substEnv] using Subtype'.asc_L hsub⟩
    -- .fix ann _ and .iota ann _ — the A9 unsoundness.
    -- `tyInfer` returns `eval ann`, but `(.fix ann body) ⋢
    -- ann` in general (the body need not inhabit `ann`).
    -- All callers that need a sound type route through
    -- `tyCheck`'s `.fix`/`.iota` arm or `letBinderType`
    -- (both verify); only `tyCheckFallback`'s `some`-path
    -- consumes this raw — that residual is the documented
    -- A9 hole. See SoundnessAudit A9.
    · sorry
    · sorry
    -- .lam dom body
    · -- `tyInfer` recurses at `push_fresh`, then *quotes*
      -- the body type and re-wraps as
      -- `.lam domV (Closure.mk' bodyTyE ρ)`. The conclusion
      -- needs `quote_{Γ.size}` of that closure — i.e.,
      -- `quoteClosure_{Γ.size} (Closure.mk' bodyTyE ρ)`,
      -- which re-evaluates `bodyTyE` under `fresh::ρ`.
      -- That round-trip (`quote ∘ eval ∘ quote ∘ eval`) is
      -- `quote_open_subst` territory — root #2. The
      -- `Subtype'` half would be `Subtype'.lam (.refl _)
      -- hIH` after the IH at `push_fresh`.
      sorry
    -- .app (.lam dom body) a — β fast-path.
    · -- `tyInfer` checks `a` against `domV`, then recurses
      -- on `body` under `(aV :: ρ)`. The IH applies at
      -- `hctx.push_let hev_a hcl_a hqdomV` (a let-style
      -- push, since `aV` is concrete not fresh). Goal then
      -- needs `Subtype'.beta_L` to relate `(.app (.lam …)
      -- a).substEnv ρe` to `body.substEnv (aV-realiser ::
      -- ρe')`. Same `.letE`-arm shift obstruction as
      -- `tyCheck_sound_open`.
      sorry
    -- .app (.letE val fbody) a — let-float.
    · -- `tyInfer` floats the let out and recurses on
      -- `(.app fbody (a.shift 1 0))` under `push_let`.
      -- IH at the floated form; relate back via
      -- `Subtype'.letE_L` + `app_cong`.
      sorry
    -- .app f a — generic.
    · -- IH on `f` gives `fTy` + quote witness; `whnfPi`
      -- exposes `.lam dom cl`; `tyCheck` IH on `a`; result
      -- is `cl.open aV`. Quoting `cl.open aV` is
      -- `quote_open_subst` — root #2.
      sorry
    -- .letE val body
    · rename_i _e' val body _h'
      simp only [Expr.closedAt, Bool.and_eq_true] at hcl
      obtain ⟨hcl_val, hcl_body⟩ := hcl
      simp only [bind, Except.bind] at h
      split at h
      · simp_all
      next valpair hletB =>
      obtain ⟨valV, valTy⟩ := valpair
      -- Mirror of `tyCheck_sound_open`'s `.letE`:
      have ⟨hev, valTye, hqValTy, hval_le⟩ :=
        letBinderType_sound_open hfuel' hctx (by sorry) hcl_val hletB
      have hctx' :=
        hctx.push_let (val := val) hfuel' hev (by sorry) hcl_val
          hqValTy (by sorry) hval_le
      have hIH :=
        tyInfer_sound_open hfuel' hctx'
          (by simpa [List.length_map] using hcl_body)
          h
      obtain ⟨τe', hqτe', hsub'⟩ := hIH
      -- `hqτe' : quote_{Γ.size+1} τV = some τe'` and
      -- `hsub' : (body.substEnv ρe') ⊑ τe'` at
      -- `(valTye :: Γe)`. Goal needs `quote_{Γ.size} τV` —
      -- but `τV`'s neutrals reference only levels `<
      -- Γ.size` (the let-bound entry is concrete `valV`,
      -- not fresh). So `τe'` should be the shift of some
      -- `τe` at depth `Γ.size`. Recovering that requires a
      -- "no-fresh-neutral" side-condition or downshift
      -- lemma — same `.letE` shift obstruction as
      -- `tyCheck_sound_open .letE` (route (a) unshift via
      -- `ctx_extend` inverse). With `τe` in hand, conclude
      -- via `Subtype'.letE_L` after relating `body.substEnv
      -- ρe'` to `(.letE val body).substEnv ρe`'s body.
      sorry
termination_by (fuel, 0)

/-- Open-context `tyCheckFallback` soundness. Both paths
chain through `subCheckVal_sound_open` and `OpenCtx.eq`. -/
theorem tyCheckFallback_sound_open
    {fuel : Nat} (hfuel : fuel ≤ fuelω)
    {Γ : TyCtx} {ρ : Env} {Γe : Ctx} {ρe : List Expr}
    (hctx : OpenCtx Γ ρ Γe ρe)
    {e : Expr} {τV : Val} {τe : Expr}
    (hcl : e.closedAt ρe.length = true)
    (hqτ : quote fuelω Γ.size τV = some τe)
    (h : tyCheckFallback fuel Γ ρ e τV = .ok true) :
    Subtype' [] Γe (e.substEnv ρe) τe := by
  unfold tyCheckFallback at h
  simp only [bind, Except.bind] at h
  split at h
  · simp_all
  · next eTy? hinfer =>
    cases eTy? with
    | some eTy =>
        simp only [] at h
        obtain ⟨eTye, hqeTy, h_e_eTye⟩ :=
          tyInfer_sound_open hfuel hctx hcl hinfer
        have hsub : Subtype' [] Γe eTye τe := by sorry
        exact .trans h_e_eTye hsub
    | none =>
        simp only [] at h
        split at h
        · next eV heV =>
          obtain ⟨eVe, hqeV⟩ := hctx.eval_quotes' hfuel (by sorry) heV
          have h_e_eVe := (hctx.eq heV hcl hqeV).2
          have hsub : Subtype' [] Γe eVe τe := by sorry
          exact .trans h_e_eVe hsub
        · simp_all
termination_by (fuel, 1)

/-- Open-context `tyCheck` soundness. Conclusion is at
`e.substEnv ρe` — the source with the explicit substitution
applied. At the closed corollary `ρe = []` and
`substEnv_nil` recovers `e`. -/
theorem tyCheck_sound_open
    {fuel : Nat} (hfuel : fuel ≤ fuelω)
    {Γ : TyCtx} {ρ : Env} {Γe : Ctx} {ρe : List Expr}
    (hctx : OpenCtx Γ ρ Γe ρe)
    {e : Expr} {τV : Val} {τe : Expr}
    (hcl : e.closedAt ρe.length = true)
    (hqτ : quote fuelω Γ.size τV = some τe)
    (h : tyCheck fuel Γ ρ e τV = .ok true) :
    Subtype' [] Γe (e.substEnv ρe) τe := by
  match fuel, hfuel, h with
  | 0, _, h => simp [tyCheck] at h
  | fuel + 1, hfuel, h =>
    have hfuel' : fuel ≤ fuelω := Nat.le_of_succ_le hfuel
    unfold tyCheck at h
    split at h
    -- .lam dom body
    · rename_i _e' dom body _h'
      simp only [Expr.closedAt, Bool.and_eq_true] at hcl
      obtain ⟨hcl_dom, hcl_body⟩ := hcl
      split at h
      case h_2 => simp_all
      case h_1 domV hdomV =>
      simp only [] at h  -- inline `let fresh := …`
      split at h
      case h_2 _ _ =>
        exact tyCheckFallback_sound_open hfuel hctx
          (by simpa [Expr.closedAt] using ⟨hcl_dom, hcl_body⟩)
          hqτ h
      case h_1 expDom expCl hwhnf =>
      simp only [bind, Except.bind] at h
      split at h
      · simp_all
      rename_i okDom hokDom
      cases okDom with
      | false => simp_all [pure, Except.pure]
      | true =>
      simp only [Bool.not_true, Bool.false_eq_true,
                 ↓reduceIte, pure, Except.pure] at h
      split at h
      case h_1 => simp_all
      case h_2 expBody hopen =>
      -- All algorithm splits done.
      -- (a) Quote witnesses for the exposed Π-head.
      --     `expDom` lives at depth `Γ.size` (same context
      --     as the `.lam` head); `expBody` at `Γ.size + 1`
      --     (the body's extended context). Both reachable
      --     from `τV` via `whnfPi`'s .fix/.iota unfolds +
      --     one closure-open; quote-totality on these is
      --     exactly what `whnfPi_sound_open` already needs
      --     (`quote_open_subst` per unfold step). Same
      --     dependency as obstruction (a) below.
      have h_lamQuote : ∃ expDome expBodye,
          quote fuelω Γ.size expDom = some expDome ∧
          quote fuelω (Γ.size + 1) expBody = some expBodye := by
        sorry
      obtain ⟨expDome, expBodye, hqDom, hqBody'⟩ := h_lamQuote
      -- (b) Extended context. With the `QuotesCtx` depth-`k`
      --     convention, `push_fresh hqDom` gives
      --     `Γe' = expDome :: Γe` — directly the head
      --     `Subtype'.lam` expects.
      have hctx' := hctx.push_fresh (τ := expDom) hqDom (by sorry)
      -- (c) Body IH at the extended context. The `ρe'` from
      --     `push_fresh` is `.bvar 0 :: ρe.map shift` —
      --     **identical** to `(.lam dom body).substEnv ρe`'s
      --     body environment. So the IH's `e.substEnv ρe'`
      --     IS the body of the goal's `.lam`. ✓
      have hIH : Subtype' [] (expDome :: Γe)
          (body.substEnv (.bvar 0 :: ρe.map (·.shift 1 0)))
          expBodye :=
        tyCheck_sound_open hfuel' hctx'
          (by simpa [List.length_map] using hcl_body)
          (by simpa [Array.size_push] using hqBody') h
      -- (d) Contravariant domain at the *outer* depth:
      obtain ⟨dome, hqdomV⟩ := hctx.eval_quotes' hfuel' (by sorry) hdomV
      have hcontra : Subtype' [] Γe expDome (dom.substEnv ρe) := by sorry
      -- (e) Assemble. With (a)-(d) in scope:
      --   hIH    : body[ρe'] ⊑ expBodye  at (expDome :: Γe)
      --   hcontra: expDome ⊑ dom[ρe]     at Γe
      -- so `Subtype'.lam hcontra hIH` gives
      --   (.lam dom body)[ρe] ⊑ .lam expDome expBodye  at Γe.
      -- **Two obstructions remain** for the final `.trans`
      -- to `τe`:
      --
      -- (a) `whnfPi_quotes`: relating `expBodye =
      --     quote_{Γ.size+1} expBody` to the *closure* quote
      --     `quoteClosure_{Γ.size} expCl` (via
      --     `quoteClosure_eq_quote_openω_fresh` ←
      --     `eval_unf_equiv` ← root #2). Without it,
      --     `h_lamQuote` above stays sorried and the
      --     `.lam expDome expBodye` we built is not
      --     definitionally `quote_{Γ.size} (.lam expDom
      --     expCl)`.
      -- (c) `whnfPi_sound_open` (sorried at line ~2924) for
      --     `quote_{Γ.size} (.lam expDom expCl) ⊑ τe`.
      --
      -- Once (a)+(c) land, this is
      -- `(Subtype'.lam hcontra hIH).trans hwhnf_equiv`.
      have hpre : Subtype' [] Γe ((Expr.lam dom body).substEnv ρe)
          (.lam expDome expBodye) := by
        simpa [Expr.substEnv] using Subtype'.lam hcontra hIH
      sorry
    -- .letE val body
    · -- `next` would mis-bind (the outer `h✝`/`e✝` shadowing
      -- pollutes the inaccessible stack); rename all 4.
      rename_i _e' val body _h'
      simp only [Expr.closedAt, Bool.and_eq_true] at hcl
      obtain ⟨hcl_val, hcl_body⟩ := hcl
      simp only [bind, Except.bind] at h
      split at h
      · simp_all
      next valpair hletB =>
      obtain ⟨valV, valTy⟩ := valpair
      -- In scope:
      --   hletB : letBinderType fuel Γ ρ val = .ok (valV, valTy)
      --   h     : tyCheck fuel (Γ.push valTy) (valV :: ρ)
      --             body τV = .ok true
      -- `letBinderType_sound_open` (mutual, tag 3 — proven
      -- below) gives the binder's eval + a quoted upper
      -- bound on its type:
      have ⟨hev, valTye, hqValTy, hval_le⟩ :=
        letBinderType_sound_open hfuel' hctx (by sorry) hcl_val hletB
      -- Extended context (push_let is proven; with the
      -- `QuotesCtx` depth-`k` convention, `valTye` at depth
      -- `Γ.size` is exactly the head we cons):
      have hctx' :=
        hctx.push_let (val := val) hfuel' hev (by sorry) hcl_val
          hqValTy (by sorry) hval_le
      -- IH: body at hctx', expected τV at depth Γ.size+1.
      have hIH :=
        tyCheck_sound_open hfuel' hctx'
          (by simpa [List.length_map] using hcl_body)
          (by
            -- Inside already-sorried section; levelsBelow of τV
            -- would be threaded via hctx-invariant from caller.
            simpa [Array.size_push] using
              quote_depth_shift (by sorry : Val.levelsBelow Γ.size τV) hqτ)
          h
      -- Goal: Subtype' [] Γe
      --   (.letE (val.substEnv ρe)
      --     (body.substEnv (.bvar 0 :: ρe.map shift))) τe.
      --
      -- ── Obstruction: ──────────────────────────────────
      -- The IH is at `(valTye.shift :: Γe)` with both sides
      -- shifted (`body.substEnv ρe' = body.substEnv ((vale
      -- :: ρe).map shift)` and RHS `τe.shift`). Need to
      -- bring it back to `Γe` (un-shift). Two routes:
      --
      -- (a) **Unshift lemma**: `Subtype' S (X.shift::Γ)
      --     (a.shift) (b.shift) → Subtype' S (X::Γ) a b`.
      --     This is the *inverse* of `ctx_extend_at` at
      --     `Δ = [X]` — i.e., `ctx_extend_at` gives the
      --     forward direction; the backward needs shift to
      --     be injective on `Subtype'` (it is, since
      --     `unshift ∘ shift = id` on closed-at-d terms).
      --     Then `body.substEnv ((vale::ρe).map shift) =
      --     (body.substEnv (vale::ρe)).shift` by
      --     `substEnv_map_shift`, and after unshift the IH
      --     becomes `body.substEnv (vale::ρe) ⊑ τe` at
      --     `(valTye :: Γe)`. Then `narrow` to `(vale ::
      --     Γe)` via `hval_le`, then `.letE_L` via
      --     `substEnv_subst_comp_gen` at c=0.
      --
      -- (b) **Avoid the shift** by changing `push_let`'s
      --     `ρe'` to `vale :: ρe` (NOT shifted) and the
      --     extended `Γe'` to `valTye :: Γe` (NOT shifted) —
      --     i.e., let-bound entries DON'T extend the typing
      --     context depth (the body has the same de Bruijn
      --     depth, with `bvar 0` substituted by `vale`).
      --     This is conceptually right (`let` is just sugar
      --     for substitution), but means `OpenCtx`'s
      --     `Γ.size` no longer equals `|Γe|` after a
      --     `push_let`, breaking the `QuotesCtx` indexing.
      --
      -- Route (a)'s `unshift` lemma is the same `ctx_extend
      -- _at`-family obligation as the `.lam` arm's
      -- obstruction (b) — both stem from the `QuotesCtx`
      -- (k+1) depth convention. So both arms reduce to the
      -- SAME design fix.
      sorry
    -- .asc e0 τ0
    · next e0 τ0 =>
      split at h
      · next τ0V hτ0V =>
        simp only [bind, Except.bind] at h
        split at h
        · simp_all
        · next b hinner =>
          cases b with
          | false => simp_all [pure, Except.pure]
          | true =>
            simp only [Bool.not_true, Bool.false_eq_true,
                       ↓reduceIte, pure, Except.pure,
                       bind, Except.bind] at h
            simp only [Expr.closedAt, Bool.and_eq_true] at hcl
            obtain ⟨τ0e, hqτ0V⟩ := hctx.eval_quotes' hfuel' (by sorry) hτ0V
            -- IH (same Γ/ρ): `(e0.substEnv ρe) ⊑ τ0e`.
            have h_e0_τ0e :=
              tyCheck_sound_open hfuel' hctx hcl.1 hqτ0V hinner
            have hsub : Subtype' [] Γe τ0e τe := by sorry
            -- `(.asc e0 τ0).substEnv ρe = .asc
            --  (e0.substEnv ρe) (τ0.substEnv ρe)`.
            simp only [Expr.substEnv]
            exact .asc_L (.trans h_e0_τ0e hsub)
      · simp_all
    -- .fix _ _ and .iota _ _ (A9 arm) then catch-all.
    all_goals first
    | exact tyCheckFallback_sound_open hfuel hctx hcl hqτ h
    | (rename_i ann body
       split at h
       · rename_i eV hev
         obtain ⟨ee, hqeV⟩ := hctx.eval_quotes' hfuel' (by sorry) hev
         have hsub : Subtype' [] Γe ee τe := by sorry
         have he_ee := (hctx.eq hev hcl hqeV).2
         exact .trans he_ee hsub
       · simp_all)
termination_by (fuel, 2)

/-- Soundness of `letBinderType`: it returns `(valV, valTy)`
where `valV = eval ρ val` and `valTy` quotes to *some* upper
bound on `val.substEnv ρe`.

The `none` and `okV = false` branches: `valTy = valV`, the
upper bound is `quote valV` and `(val.substEnv ρe) ⊑
(quote valV)` is the forward direction of `hctx.eq`. The
`okV = true` branch: `valTy = t` from `tyInfer`, and
`tyInfer_sound_open` gives both the quote witness and the
upper bound. (That call inherits the A9 sorry for `.fix`/
`.iota`-headed `val`; the algorithm guards this at runtime
via the `tyCheck` round-trip, but the proof routes through
`tyInfer_sound_open` which carries the residual.)

Tag 3: called from `tyCheck_sound_open` at `(fuel+1, 2)` →
`(fuel, 3)`; calls `tyInfer_sound_open` at `(fuel, 0)` and
`tyCheck_sound_open` at `(fuel, 2)` (unused). -/
theorem letBinderType_sound_open
    {fuel : Nat} (hfuel : fuel ≤ fuelω)
    {Γ : TyCtx} {ρ : Env} {Γe : Ctx} {ρe : List Expr}
    (hctx : OpenCtx Γ ρ Γe ρe)
    {val : Expr} {valV valTy : Val}
    (hnfq : ((eval fuelω unfBound ρ val).bind (quote fuelω Γ.size)).isSome)
    (hcl : val.closedAt ρe.length = true)
    (h : letBinderType fuel Γ ρ val = .ok (valV, valTy)) :
    eval fuel unfBound ρ val = some valV ∧
    ∃ valTye, quote fuelω Γ.size valTy = some valTye ∧
              Subtype' [] Γe (val.substEnv ρe) valTye := by
  unfold letBinderType at h
  simp only [bind, Except.bind] at h
  split at h
  · simp_all
  next valTy? hinfer =>
  split at h
  case h_2 => simp_all
  case h_1 valV0 hev =>
  -- The "fall back to valV" branch (shared by `none` and
  -- `okV = false`):
  have hself : eval fuel unfBound ρ val = some valV0 ∧
      ∃ valTye, quote fuelω Γ.size valV0 = some valTye ∧
                Subtype' [] Γe (val.substEnv ρe) valTye := by
    obtain ⟨valVe, hqvalV⟩ := hctx.eval_quotes' hfuel hnfq hev
    exact ⟨hev, valVe, hqvalV, (hctx.eq hev hcl hqvalV).2⟩
  cases valTy? with
  | none =>
      simp only [pure, Except.pure, Except.ok.injEq,
                 Prod.mk.injEq] at h
      obtain ⟨h1, h2⟩ := h; subst h1 h2; exact hself
  | some t =>
      simp only [bind, Except.bind] at h
      split at h
      · simp_all
      next okV hokV =>
      simp only [pure, Except.pure, Except.ok.injEq,
                 Prod.mk.injEq] at h
      obtain ⟨h1, h2⟩ := h; subst h1
      split at h2
      · -- okV = true branch: valTy = t
        subst h2
        exact ⟨hev, tyInfer_sound_open hfuel hctx hcl hinfer⟩
      · -- okV = false branch: valTy = valV0
        subst h2; exact hself
termination_by (fuel, 3)

end

/-- The closed forms in `Soundness.lean` derive from the
open ones at the empty context (`ρe = []`,
`substEnv_nil`). The `hcl0` precondition is the
well-scopedness of `e`. -/
example {fuel : Nat} (hfuel : fuel ≤ fuelω)
    {e : Expr} {τV : Val} {τe : Expr}
    (hcl0 : e.closedAt 0 = true)
    (hqτ : quote fuelω 0 τV = some τe)
    (h : tyCheck fuel #[] [] e τV = .ok true) :
    Subtype' [] [] e τe := by
  have := tyCheck_sound_open hfuel OpenCtx.empty
    (by simpa using hcl0) (by simpa using hqτ) h
  simpa [Expr.substEnv_nil] using this

end NbE
