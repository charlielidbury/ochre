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

  /-- `Equiv` respects `shift`.

  For any *nonempty* target context `τ :: Γ₀`, instantiate
  `h` at `([], Γ₀)`, lift via `Subtype'.ctx_extend [τ]` (the
  empty seen-set is trivially `Closed`), and `weaken` to the
  caller's `S`. This routes `Equiv.shift` through
  `ctx_extend_at` — so its `sorryAx` is exactly the six
  binder-case sorries there (the seen-cutoff obstruction;
  DECISION-LOG 2026-04-18), shared with `Subtype'.narrow`.

  The empty-context case (`Γ' = []`) is the irreducible
  residual: `ctx_extend` can only *extend* a context, never
  produce `[]`. A direct induction on the derivation at
  `Subtype' [] [] e₁ e₂` hits the same wall — `.iota_intro`
  inside extends the seen-set with a depth-0 pair, and a
  `.lam` body under that needs the pair shifted at two
  different cutoffs. None of routes (a)/(b)/(c) avoid this
  without touching `Subtype'`. -/
  theorem shift {e₁ e₂ : Expr} (h : Equiv e₁ e₂) :
      Equiv (e₁.shift 1 0) (e₂.shift 1 0) := by
    intro S' Γ'
    have hSc : Seen.Closed ([] : Seen) := by
      intro p hp; cases hp
    have lift : ∀ (τ : Expr) (Γ₀ : Ctx),
        Subtype' S' (τ :: Γ₀) (e₁.shift 1 0) (e₂.shift 1 0) ∧
        Subtype' S' (τ :: Γ₀) (e₂.shift 1 0) (e₁.shift 1 0) := by
      intro τ Γ₀
      have h₁ := (h (S := []) (Γe := Γ₀)).1
      have h₂ := (h (S := []) (Γe := Γ₀)).2
      have l₁ := Subtype'.ctx_extend (Γ := Γ₀) [τ] hSc h₁
      have l₂ := Subtype'.ctx_extend (Γ := Γ₀) [τ] hSc h₂
      simp only [List.length_singleton, List.singleton_append]
        at l₁ l₂
      exact ⟨l₁.weaken (fun _ hp => absurd hp (List.not_mem_nil _)),
             l₂.weaken (fun _ hp => absurd hp (List.not_mem_nil _))⟩
    cases Γ' with
    | cons τ Γ₀ => exact lift τ Γ₀
    | nil =>
      -- At `Γ' = []` there is no smaller context to lift
      -- *from*; this is the same seen-cutoff residual as
      -- `ctx_extend_at`'s six binder cases (Subtyping.lean
      -- 308). All call sites of `Equiv.shift` are inside
      -- `subst_resp`'s binder arms, which then feed the
      -- result to `Equiv.lam`/`.iota_cong`/`.fix_cong`/
      -- `.letE_cong` — each of which instantiates the body
      -- premise at a *cons* context. So this branch is
      -- believed unreachable from the proof chain; a
      -- `Subtype'` redesign (DECISION-LOG routes a/b) would
      -- close it together with `ctx_extend_at`.
      sorry

  /-- Substitution respects declarative equivalence: if
  `a ≡ b` then `e[i ↦ a] ≡ e[i ↦ b]` for any `e`. Needed at
  `R_resp_Equiv` (`.iota` arm), `eval_realises`
  (`.letE`/`.app`-Kripke threads), and `concEval_refines`
  (`.letE`/`.app` cases).

  By induction on `e`, generalising over the substituted
  pair (the binder cases shift it). All eight constructors
  close via the corresponding `Subtype'` congruence (`.lam`/
  `.app_cong`/`.iota_cong`/`.fix_cong`/`.letE_cong`/`.asc_*`).
  Inherits `sorryAx` only from `Equiv.shift`. -/
  theorem subst_resp :
      ∀ (e : Expr) {a b : Expr}, Equiv a b → ∀ (i : Nat),
      Equiv (e.subst i a) (e.subst i b) := by
    intro e
    induction e with
    | bvar k =>
      intro a b heq i
      simp only [Expr.subst]
      split
      · exact heq
      · split <;> exact Equiv.refl _
    | type =>
      intro _ _ _ _
      simp only [Expr.subst]; exact Equiv.refl _
    | lam dom body ihD ihB =>
      intro a b heq i
      simp only [Expr.subst]
      exact Equiv.lam (ihD heq i)
        (ihB (Equiv.shift heq) (i + 1))
    | app f x ihF ihX =>
      intro a b heq i
      simp only [Expr.subst]
      exact Equiv.app (ihF heq i) (ihX heq i)
    | asc t ty ihT _ =>
      intro a b heq i
      simp only [Expr.subst]
      exact fun {S Γ} =>
        ⟨.asc_L (.asc_R (ihT heq i).1),
         .asc_L (.asc_R (ihT heq i).2)⟩
    | iota ann body ihA ihB =>
      intro a b heq i
      simp only [Expr.subst]
      intro S Γ
      exact ⟨.iota_cong (ihA heq i).1 (ihB (Equiv.shift heq) (i + 1)).1,
             .iota_cong (ihA heq i).2 (ihB (Equiv.shift heq) (i + 1)).2⟩
    | «fix» ann body ihA ihB =>
      intro a b heq i
      simp only [Expr.subst]
      intro S Γ
      exact ⟨.fix_cong (ihA heq i).1 (ihB (Equiv.shift heq) (i + 1)).1,
             .fix_cong (ihA heq i).2 (ihB (Equiv.shift heq) (i + 1)).2⟩
    | letE val body ihV ihB =>
      intro a b heq i
      simp only [Expr.subst]
      intro S Γ
      exact ⟨.letE_cong (ihV heq i).1 (ihB (Equiv.shift heq) (i + 1)).1,
             .letE_cong (ihV heq i).2 (ihB (Equiv.shift heq) (i + 1)).2⟩
end Equiv

/-! ## Step-indexed logical relation

`R n d v e` means "at step index `n` and depth `d`, the
value `v` realises the expression `e`".

The base conjunct (`v` quotes to something `Equiv e`) is
what `R_quote_equiv` extracts.

The constructor-specific conjunct for `.lam`/`.iota`/`.fix`
**exposes the closure's environment** as realised at the
*same* step index `n+1`: `∃ ρe', RList (n+1) d cl.env ρe' ∧ …
∧ Equiv e (.lam … (cl.body.substEnv (lift ρe')))`. This lets
`vapp_realises`'s `.lam`-head case build
`REnv (n+1) d (a :: cl.env) (ae :: ρe')` and call
`eval_realises`'s fuel-IH directly — no Kripke step-loss.

The previous Kripke design (`∀ n' ≤ n, … → R n' d r …`) lost
one step-index at every `.app`-head boundary, leaving
`vapp_realises` unprovable (see the docstring there for the
detailed analysis of why both `(fuel,unf)`-lex and Ahmed-style
indexing also fail by exactly 1).

Termination: `R`/`RList` are mutual on `(n, sizeOf v)` lex.
The same-index recursion `R (n+1) d w …` for `w ∈ cl.env` is
well-founded because `sizeOf w < sizeOf cl.env < sizeOf cl <
sizeOf (.lam _ cl)`. -/

mutual
/-- See the `Step-indexed logical relation` section above. -/
def R : Nat → Nat → Val → Expr → Prop
  | 0, _, _, _ => True
  | n+1, d, v, e =>
      -- Base conjunct: *if* `v` quotes (it might not — fuel
      -- exhaustion, scope error), the quote is `Equiv e`. The
      -- universal form avoids a totality obligation in
      -- `eval_realises`'s `.lam`/`.fix`/`.iota` cases.
      (∀ e', quote fuelω d v = some e' → Equiv e' e) ∧
      (match v with
        | .lam _dV cl =>
            ∃ ρe' dome,
              RList (n+1) d cl.env ρe' ∧
              cl.body.closedAt (ρe'.length + 1) = true ∧
              Equiv e (.lam dome
                (cl.body.substEnv (.bvar 0 :: ρe'.map (·.shift 1 0))))
        | .iota _aV cl =>
            ∃ ρe' anne,
              RList (n+1) d cl.env ρe' ∧
              cl.body.closedAt (ρe'.length + 1) = true ∧
              Equiv e (.iota anne
                (cl.body.substEnv (.bvar 0 :: ρe'.map (·.shift 1 0))))
        | .«fix» _aV cl =>
            ∃ ρe' anne,
              RList (n+1) d cl.env ρe' ∧
              cl.body.closedAt (ρe'.length + 1) = true ∧
              Equiv e (.fix anne
                (cl.body.substEnv (.bvar 0 :: ρe'.map (·.shift 1 0))))
        | .type => True
        | .neutral _ => True)
termination_by n _ v _ => sizeOf v
decreasing_by
  all_goals simp_wf
  all_goals (rename Closure => cl; cases cl; simp; omega)

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
clauses' `RList (n+1)` lowers via mutual `RList_mono`;
recursion is on `sizeOf v`/`sizeOf ρ` (the step-index does
not change inside the constructor clauses). -/
theorem R_mono {n m d v e} (hle : m ≤ n) (h : R n d v e) :
    R m d v e := by
  match m, n, hle with
  | 0, _, _ => unfold R; trivial
  | _+1, _+1, hle =>
    unfold R at h ⊢
    refine ⟨h.1, ?_⟩
    match v, h.2 with
    | .type, hcl => exact hcl
    | .neutral _, hcl => exact hcl
    | .lam dV cl, ⟨ρe', dome, hRL, hclb, heqL⟩ =>
        exact ⟨ρe', dome, RList_mono hle hRL, hclb, heqL⟩
    | .iota aV cl, ⟨ρe', anne, hRL, hclb, heqI⟩ =>
        exact ⟨ρe', anne, RList_mono hle hRL, hclb, heqI⟩
    | .«fix» aV cl, ⟨ρe', anne, hRL, hclb, heqF⟩ =>
        exact ⟨ρe', anne, RList_mono hle hRL, hclb, heqF⟩
termination_by sizeOf v
decreasing_by
  all_goals simp_wf
  -- Mutual-termination encoding: the goal compares
  -- `RList_mono`'s `sizeOf cl.env` against this call's
  -- `sizeOf v`, but `v` (the implicit binder) is NOT
  -- substituted by the inner `match v` — the well-founded
  -- machinery sees the original `v`, not `.lam dV cl`. The
  -- actual obligation `sizeOf cl.env < sizeOf (.lam dV cl)`
  -- holds by `Closure.mk.sizeOf_spec`; what's needed is
  -- either (a) restating `R_mono` with `v` as an explicit
  -- *positional* arg matched at the top level (so the
  -- termination machinery sees the constructor), or (b) a
  -- non-mutual proof via strong induction on `sizeOf v`.
  -- Either is a 10-minute reshuffle; deferred per the ≤2-
  -- build-cycle ripple budget.
  all_goals sorry

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
env-exposes clause, `e` appears only in the base conjunct's
`Equiv e' e` and the constructor clause's `Equiv e (.ctor …)`
— both rewrite by `Equiv.trans`. **No recursion** (the
`RList` part doesn't mention `e`). -/
theorem R_resp_Equiv {n d v e e'}
    (heq : Equiv e e') (h : R n d v e) : R n d v e' := by
  match n, h with
  | 0, _ => unfold R; trivial
  | _+1, h =>
    unfold R at h ⊢
    refine ⟨fun qe hq => Equiv.trans (h.1 qe hq) heq, ?_⟩
    cases v with
    | type => exact h.2
    | neutral _ => exact h.2
    | lam dV cl =>
        obtain ⟨ρe', dome, hRL, hclb, heqL⟩ := h.2
        exact ⟨ρe', dome, hRL, hclb, Equiv.trans (Equiv.symm heq) heqL⟩
    | iota aV cl =>
        obtain ⟨ρe', anne, hRL, hclb, heqI⟩ := h.2
        exact ⟨ρe', anne, hRL, hclb, Equiv.trans (Equiv.symm heq) heqI⟩
    | «fix» aV cl =>
        obtain ⟨ρe', anne, hRL, hclb, heqF⟩ := h.2
        exact ⟨ρe', anne, hRL, hclb, Equiv.trans (Equiv.symm heq) heqF⟩

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

/-- Quoting a value at the next depth shifts the result by
one — provided quoting at the current depth already
succeeds (which guarantees every `.var k` neutral has
`k < d`, so re-quoting at `d+1` maps `k ↦ d-k` instead of
`d-1-k`, i.e. each bvar index increments).

By mutual induction on `quote`/`quoteClosure`/
`quoteNeutral` over `fuelω`. The `.var k` case:
`quoteNeutral d (.var k) = some (.bvar (d-1-k))` requires
`k < d`; at `d+1` it's `.bvar (d-k)` = `.bvar ((d-1-k)+1)`
= `(.bvar (d-1-k)).shift 1 0`. Closure cases recurse via
`quoteClosure` at `depth+1` (so the inner depth shift
threads). Sorried — the mutual recursion makes this a
~50-line case analysis; recorded as the precise obligation
`R_depth_lift` reduces to. -/
theorem quote_depth_shift {d v e}
    (hq : quote fuelω d v = some e) :
    quote fuelω (d + 1) v = some (e.shift 1 0) := by
  sorry

/-- Realisation lifts to the next depth, given the value
already quotes at the current depth (which is the implicit
"all `.var` levels `< d`" side-condition). Combines
`quote_depth_shift` (for the base conjunct) with the
constructor clauses recursing at `d+1`.

`R`'s constructor clauses (`.lam`/`.fix`/`.iota`) all
quantify over results of `cl.openω`, which are values at
the *same* depth `d`; so the IH applies uniformly. The
side-condition `hq` for the recursive value `r` follows
from `quote_depth_shift` on the *closure body*'s quote (the
opened value's quote at `d` is determined by the body
under `fresh d`). -/
theorem R_depth_lift {n d v e}
    {qe : Expr} (hq : quote fuelω d v = some qe)
    (h : R n d v e) :
    R n (d + 1) v (e.shift 1 0) := by
  induction n generalizing d v e qe with
  | zero => simp only [R]
  | succ k ihk =>
    unfold R at h ⊢
    refine ⟨?base, ?ctor⟩
    case base =>
      intro e' hq'
      rw [quote_depth_shift hq] at hq'
      cases hq'
      exact Equiv.shift (h.1 qe hq)
    case ctor =>
      -- With the env-exposes clause, the constructor case
      -- needs:
      --   `RList (k+1) d cl.env ρe' →
      --      RList (k+1) (d+1) cl.env (ρe'.map (·.shift 1 0))`
      -- (mutual `RList_depth_lift`, recursing on `sizeOf`),
      -- plus `Equiv (e.shift 1 0) (.ctor (dome.shift 1 0)
      -- (bode.shift 1 1))` from `Equiv.shift heqL`, plus a
      -- `substEnv`/`shift` commutation
      --   `(cl.body.substEnv (lift ρe')).shift 1 1
      --      = cl.body.substEnv (lift (ρe'.map shift))`.
      -- The first two are mechanical; the commutation lemma
      -- is the same shift/substEnv obligation as before
      -- (orthogonal to the Kripke→env-exposes change). The
      -- per-entry `R_depth_lift` recursion additionally
      -- needs each entry's quote-success — supplied by an
      -- `RList_quotes` side-condition or threaded via
      -- `henv'`. Sorried; structure clear.
      sorry

/-- A fresh `.var d` realises `.bvar 0` at depth `d+1`. -/
theorem R_fresh_bvar0 (n d : Nat) :
    R n (d + 1) (.neutral (.var d)) (.bvar 0) := by
  cases n with
  | zero => simp only [R]
  | succ k =>
    unfold R
    refine ⟨?_, True.intro⟩
    intro e' hq
    -- quote (d+1) (.neutral (.var d)) = quoteNeutral … =
    -- if d < d+1 then some (.bvar (d+1-1-d)) = some (.bvar 0)
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
    exact fun {_ _} => ⟨.refl _, .refl _⟩

/-- Depth-lifting a realised environment (no head push):
each entry's realiser shifts up by one. Used by
`REnv_lift` (which then conses a fresh) and by
`OpenCtx.push_let` (which conses a concrete value). -/
theorem REnv_depth_lift {n d ρ ρe}
    (henv : REnv n d ρ ρe)
    (hquotes : ∀ (k : Nat) (v : Val),
        ρ[k]? = some v → ∃ qe, quote fuelω d v = some qe) :
    REnv n (d + 1) ρ (ρe.map (·.shift 1 0)) := by
  refine ⟨by simp [henv.1], ?_⟩
  intro m v hk
  obtain ⟨e, he, hR⟩ := henv.2 m v hk
  obtain ⟨qe, hqe⟩ := hquotes m v hk
  refine ⟨e.shift 1 0, ?_, R_depth_lift hqe hR⟩
  have he' : ρe[m]? = some e := by
    rw [← List.get?_eq_getElem?]; exact he
  simp [List.getElem?_map, he']

/-- Lifting a realised environment under one binder: a
fresh `.var d` realises `.bvar 0` at the head; the tail
depth-lifts via `REnv_depth_lift`. -/
theorem REnv_lift {n d ρ ρe}
    (henv : REnv n d ρ ρe)
    (hquotes : ∀ (k : Nat) (v : Val),
        ρ[k]? = some v → ∃ qe, quote fuelω d v = some qe) :
    REnv n (d + 1)
      (Val.neutral (.var d) :: ρ)
      (.bvar 0 :: ρe.map (·.shift 1 0)) := by
  have htail := REnv_depth_lift henv hquotes
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
cases: when `r` is a neutral whose quote decomposes as
`.app (quote vf) (quote va)`, the base conjuncts of
`hRf`/`hRa` assemble via `Equiv.app`. -/
private theorem R_neutral_app {k d N vf va fe ae}
    (hRf : R (k+1) d vf fe) (hRa : R (k+1) d va ae)
    (hdecomp : ∀ e', quote fuelω d (.neutral N) = some e' →
       ∃ ne ve, e' = .app ne ve ∧
         quote fuelω d vf = some ne ∧ quote fuelω d va = some ve) :
    R (k+1) d (Val.neutral N) (.app fe ae) := by
  unfold R
  refine ⟨?_, trivial⟩
  intro e' hq
  obtain ⟨ne, ve, heq, hqf, hqa⟩ := hdecomp e' hq
  subst heq
  unfold R at hRf hRa
  exact Equiv.app (hRf.1 ne hqf) (hRa.1 ve hqa)

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
fuel `< fuel+1`). -/
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
          refine R_neutral_app (vf := .neutral nf) (hvfeq ▸ hRf) hRa ?_
          intro e' hq
          have hfω : fuelω = (fuelω - 1) + 1 := rfl
          rw [hfω] at hq; unfold quote at hq
          have hfω' : fuelω - 1 = (fuelω - 2) + 1 := rfl
          rw [hfω'] at hq; unfold quoteNeutral at hq
          simp only [Option.bind_eq_bind, Option.bind_eq_some,
                     Option.some.injEq] at hq
          obtain ⟨ne, hne, ve, hve, heq⟩ := hq
          refine ⟨ne, ve, heq.symm, ?_, quote_fuel_mono (by omega) hve⟩
          rw [hfω]; unfold quote
          exact quoteNeutral_fuel_mono (by omega) hne
      | .type, hvapp =>
          simp only [Option.some.injEq] at hvapp
          subst hvapp
          exact R_neutral_app (vf := .type) (hvfeq ▸ hRf) hRa
            (quote_stuckRec_decomp (vf := .type) (va := va))
      | .lam dV ⟨lbody, lenv⟩, hvapp =>
          simp only [] at hvapp
          -- hvapp : eval fuel unf (va :: lenv) lbody = some r
          have hRf' : R (k+1) d (.lam dV ⟨lbody, lenv⟩) fe := hvfeq ▸ hRf
          unfold R at hRf'
          obtain ⟨_, ρe', dome, hRL, hclb, heqL⟩ := hRf'
          have henv' := REnv_of_RList hRL
          have henv_ext := REnv_cons henv' hRa
          have hclb' : lbody.closedAt (ae :: ρe').length = true := by
            simpa using hclb
          have hRr := eval_realises hvapp henv_ext hclb'
          -- hRr : R (k+1) d r (lbody.substEnv (ae :: ρe'))
          refine R_resp_Equiv ?_ hRr
          have hcomp :
              Expr.subst (lbody.substEnv
                  (.bvar 0 :: ρe'.map (·.shift 1 0))) 0 ae
              = lbody.substEnv (ae :: ρe') :=
            Expr.substEnv_subst_comp lbody ρe' ae hclb
          rw [← hcomp]
          -- `bode.subst 0 ae ≡ .app fe ae` via
          --   .app fe ae ≡ .app (.lam dome bode) ae [heqL]
          --   ≡ bode.subst 0 ae [β]
          intro S Γe
          refine ⟨.trans (.beta_R (dom := dome) (.refl _)) ?_,
                  .trans ?_ (.beta_L (dom := dome) (.refl _))⟩
          · exact .app_cong heqL.2 (.refl ae) (.refl ae)
          · exact .app_cong heqL.1 (.refl ae) (.refl ae)
      | .iota annV ⟨lbody, lenv⟩, hvapp =>
          simp only [] at hvapp
          have hRf' : R (k+1) d (.iota annV ⟨lbody, lenv⟩) fe := hvfeq ▸ hRf
          by_cases hcond : (va.isNeutral || unf == 0) = true
          · simp only [hcond, ↓reduceIte, Option.some.injEq] at hvapp
            subst hvapp
            exact R_neutral_app (vf := .iota annV ⟨lbody, lenv⟩) hRf' hRa
              (quote_stuckRec_decomp (vf := .iota annV ⟨lbody, lenv⟩) (va := va))
          · -- Unfold branch.
            simp only [hcond, Bool.false_eq_true, ↓reduceIte,
                       Option.bind_eq_bind, Option.bind_eq_some] at hvapp
            obtain ⟨f', hf', hvapp'⟩ := hvapp
            have hRf'' := hRf'  -- preserve for self-binding
            unfold R at hRf'
            obtain ⟨_, ρe', anne, hRL, hclb, heqI⟩ := hRf'
            have henv' := REnv_of_RList hRL
            have henv_ext := REnv_cons henv' hRf''
            have hclb' : lbody.closedAt (fe :: ρe').length = true := by
              simpa using hclb
            -- eval_realises on the unfold's body eval (mutual,
            -- fuel < fuel+1).
            have hRf3 := eval_realises hf' henv_ext hclb'
            -- hRf3 : R (k+1) d f' (lbody.substEnv (fe :: ρe'))
            -- = bode.subst 0 fe.   Equiv-chain to fe:
            --   bode.subst 0 fe
            --     ≡ bode.subst 0 (.iota anne bode)  [subst_resp heqI]
            --     ≡ .iota anne bode                 [iota_unfold⁻¹]
            --     ≡ fe                              [heqI⁻¹]
            have hcomp :
                Expr.subst (lbody.substEnv
                    (.bvar 0 :: ρe'.map (·.shift 1 0))) 0 fe
                = lbody.substEnv (fe :: ρe') :=
              Expr.substEnv_subst_comp lbody ρe' fe hclb
            have hRf4 : R (k+1) d f' fe := by
              refine R_resp_Equiv ?_ hRf3
              rw [← hcomp]
              refine Equiv.trans (Equiv.subst_resp _ heqI 0)
                       (Equiv.trans ?_ (Equiv.symm heqI))
              exact Equiv.symm (Equiv.iota_unfold anne _)
            -- Inner vapp at fuel < fuel+1.
            exact vapp_realises hvapp' hRf4 hRa
      | .«fix» annV ⟨lbody, lenv⟩, hvapp =>
          simp only [] at hvapp
          have hRf' : R (k+1) d (.«fix» annV ⟨lbody, lenv⟩) fe := hvfeq ▸ hRf
          by_cases hcond : (va.isNeutral || unf == 0) = true
          · simp only [hcond, ↓reduceIte, Option.some.injEq] at hvapp
            subst hvapp
            exact R_neutral_app (vf := .«fix» annV ⟨lbody, lenv⟩) hRf' hRa
              (quote_stuckRec_decomp (vf := .«fix» annV ⟨lbody, lenv⟩) (va := va))
          · simp only [hcond, Bool.false_eq_true, ↓reduceIte,
                       Option.bind_eq_bind, Option.bind_eq_some] at hvapp
            obtain ⟨f', hf', hvapp'⟩ := hvapp
            have hRf'' := hRf'
            unfold R at hRf'
            obtain ⟨_, ρe', anne, hRL, hclb, heqF⟩ := hRf'
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
              refine R_resp_Equiv ?_ hRf3
              rw [← hcomp]
              refine Equiv.trans (Equiv.subst_resp _ heqF 0)
                       (Equiv.trans ?_ (Equiv.symm heqF))
              exact Equiv.symm (Equiv.fix_unfold anne _)
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
          refine ⟨fun e' hq => ?_, trivial⟩
          have hqt : quote fuelω d .type = some .type := by
            have hf : fuelω = (fuelω - 1) + 1 := rfl
            rw [hf]; unfold quote; rfl
          rw [hqt] at hq; cases hq
          exact fun {_ _} => ⟨.refl _, .refl _⟩
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
          refine ⟨?_, ?_⟩
          · -- Base conjunct: `quote d (.lam domV cl) ≡ .lam
            -- dome bodye`. `quote (.lam domV cl) = .lam
            -- (quote d domV) (quoteClosure d cl)`. The dom
            -- part: `R (k+1) d domV dome` from `ihf'`, then
            -- `R_quote_equiv` extracts `quote domV ≡ dome`.
            -- The body part: `quoteClosure d cl` opens with
            -- fresh `.var d` at unf=1 and quotes at d+1; the
            -- result realises `bExpr.substEnv (.bvar 0 ::
            -- (ρe.take j).map shift)` (via `ihm` at any
            -- m' ≤ k with `REnv_lift ∘ REnv_take`). After
            -- `substEnv`-take normalisation that equals
            -- `bodye`, so `Equiv.lam` assembles. The
            -- quote-totality (`∃ e', quote … = some e'`) is
            -- the residual obligation: `quote` succeeds
            -- whenever its argument is "well-leveled" (all
            -- free .var < d), which holds for any value
            -- produced by `eval` from a depth-d env.
            sorry
          · -- Env-exposes clause: `∃ ρe' dome, RList … ∧
            -- closed ∧ Equiv`. With `cl = Closure.mk' bExpr ρ
            -- = ⟨bExpr, ρ.take j⟩`, take `ρe' := ρe.take j`
            -- and `dome := dom.substEnv ρe`. The `Equiv` is
            -- by `refl` after `substEnv_closedAt_irrel`.
            simp only [Closure.mk']
            obtain ⟨hRL, hclb', hbody_eq⟩ :=
              closure_clause_witness henv hcl.2
            exact ⟨ρe.take (bvarBound bExpr - 1), dom.substEnv ρe,
                   hRL, hclb', hbody_eq ▸ Equiv.refl _⟩
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
          refine ⟨?_, ?_⟩
          · -- BASE conjunct: ∀ e', quote (.iota annV cl) = some e'
            -- → Equiv e' (.iota anne bode). Decomposing
            -- `quote (.iota …)` gives `.iota qann qcl`; the
            -- ann-Equiv comes from `IH_fuel hann` +
            -- `R_quote_equiv`; the body-Equiv `qcl ≡ bode` is
            -- the *body-correspondence* (quoteClosure of cl
            -- ≡ bExpr.substEnv lifted) — same blocker as
            -- `.lam`'s base, gated on a `eval_realises` call
            -- on `bExpr` at fuel `fuelω-2` which IH_fuel
            -- doesn't reach. Resolved once the parallel
            -- `.lam` fork lands a `quoteClosure_realises`
            -- helper (or once closedness is threaded so
            -- `IH_m` at the fresh-extended env applies).
            sorry
          · -- Env-exposes clause (same shape as `.lam`).
            simp only [cl, Closure.mk']
            obtain ⟨hRL, hclb', hbody_eq⟩ :=
              closure_clause_witness henv hcl.2
            exact ⟨ρe.take (bvarBound bExpr - 1), anne,
                   hRL, hclb', by rw [hbody_eq]; exact Equiv.refl _⟩
      | fix ann bExpr =>
          -- Identical structure to .iota above (R's `.fix`
          -- clause has `body.subst 0 (.fix ann body)` instead
          -- of `body.subst 0 e`, but `e` here IS the .fix).
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
          refine ⟨?_, ?_⟩
          · -- BASE conjunct: same body-correspondence blocker
            -- as `.iota`/`.lam`.
            sorry
          · -- Env-exposes clause (same shape as `.lam`).
            simp only [cl, Closure.mk']
            obtain ⟨hRL, hclb', hbody_eq⟩ :=
              closure_clause_witness henv hcl.2
            exact ⟨ρe.take (bvarBound bExpr - 1), anne,
                   hRL, hclb', by rw [hbody_eq]; exact Equiv.refl _⟩
termination_by fuel
end

/-- The base conjunct of `R` at any nonzero index. -/
theorem R_quote_equiv {n d v e}
    (hn : 0 < n) (h : R n d v e)
    {e' : Expr} (hq : quote fuelω d v = some e') :
    Equiv e' e := by
  cases n with
  | zero => omega
  | succ m =>
      unfold R at h
      exact h.1 e' hq

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
      refine ⟨fun e' hq => ?_, trivial⟩
      rw [quote_neutral_var_fwd hlt] at hq
      cases hq; exact Equiv.refl _

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
    (hcl : e.closedAt ρe.length = true)
    (h₁ : eval n unf₁ ρ e = some v₁)
    (h₂ : eval n unf₂ ρ e = some v₂)
    (hq₁ : quote n depth v₁ = some e₁)
    (hq₂ : quote n depth v₂ = some e₂) :
    ∀ {S Γe}, Subtype' S Γe e₁ e₂ ∧ Subtype' S Γe e₂ e₁ := by
  have hq₁' := quote_fuel_mono hn hq₁
  have hq₂' := quote_fuel_mono hn hq₂
  -- Both evaluations realise `e.substEnv ρe` at step index 1
  -- (the fundamental lemma is `unf`-agnostic).
  have r₁ := eval_realises h₁ (m := 1) (d := depth) hρe hcl
  have r₂ := eval_realises h₂ (m := 1) (d := depth) hρe hcl
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

/-- **Unconditional** fresh-open correspondence: opening `cl`
with the fresh neutral and quoting gives an Expr `Equiv` to
`quoteClosure cl`. Replaces the `(hunf)`-conditional lemma
above by going through `eval_unf_equiv` (proven, mod
`eval_realises`).

The `(hρe')` hypothesis is what root #2 (R-restructure)
exposes: once `R`'s `.lam`/`.iota`/`.fix` clause carries
`∃ ρe', REnv n d cl.env ρe'`, every `SubV_to_Subtype'`
closure case has it (the bridge gains `(hRa)/(hRb)`
realisability hypotheses, supplied by `eval_realises` at
`subCheckVal_sound_open`'s call site). -/
theorem quoteClosure_equiv_openω_fresh
    {cl : Closure} {depth : Nat} {r : Val} {bodye re : Expr}
    {ρe' : List Expr}
    (hopen : cl.openω (.neutral (.var depth)) = some r)
    (hqcl : quoteClosure fuelω depth cl = some bodye)
    (hqr : quote fuelω (depth + 1) r = some re)
    (hρe' : REnv 1 (depth + 1)
              (.neutral (.var depth) :: cl.env) ρe')
    (hclb : cl.body.closedAt ρe'.length = true) :
    Equiv bodye re := by
  unfold Closure.openω Closure.open at hopen
  have hfω : fuelω = (fuelω - 1) + 1 := rfl
  rw [hfω] at hqcl; unfold quoteClosure at hqcl
  simp only [Option.bind_eq_bind, Option.bind_eq_some] at hqcl
  obtain ⟨v', hev', hq'⟩ := hqcl
  have hev'ω := eval_fuel_mono (Nat.sub_le _ _) hev'
  have hq'ω := quote_fuel_mono (Nat.sub_le _ _) hq'
  intro S Γe
  exact eval_unf_equiv (Nat.le_refl fuelω) hρe' hclb hev'ω hopen hq'ω hqr

/-- Quoting commutes with closure-opening up to `Subtype'`'s
β-conversion: opening `cl` with `v` and quoting gives an Expr
β-equivalent to substituting `quote v` into the closure's
quoted body. The general-`v` form of
`quoteClosure_equiv_openω_fresh`.

Once root #2 lands, this derives by:
  (1) `eval_realises` on `cl.openω v` (i.e., `eval (v::cl.env)
      cl.body`) gives `R 1 d r (cl.body.substEnv (ve::ρe'))`
      where `ρe'` realises `cl.env` (from the new R-clause).
  (2) `eval_realises` on the `quoteClosure` eval gives
      `bodye ≡ cl.body.substEnv (.bvar 0 :: ρe'.shift)`.
  (3) `(cl.body.substEnv (.bvar 0 :: ρe'.shift)).subst 0 ve
       = cl.body.substEnv (ve :: ρe')` by `substEnv_subst_comp`.
  (4) `R_quote_equiv` on (1) + (2) + (3). -/
theorem quote_open_subst {cl : Closure} {v r : Val}
    {depth : Nat} {ve re bodye : Expr}
    (hopen : cl.openω v = some r)
    (hqv : quote fuelω depth v = some ve)
    (hqbody : quoteClosure fuelω depth cl = some bodye)
    (hqr : quote fuelω depth r = some re) :
    ∀ {S Γe}, Subtype' S Γe re (bodye.subst 0 ve) ∧
              Subtype' S Γe (bodye.subst 0 ve) re := by
  sorry

/-- Multi-step `quote_depth_shift`: quoting at any deeper
depth `d ≥ k` shifts the result by `d - k`. Iterates the
one-step lemma; `shift_shift_same` collapses the iterated
shifts. Used by `SynthN_to_Subtype'.var` to bridge
`QuotesCtx`'s per-entry depth `k` to the goal's outer depth
`Γ.size`, where the gap is exactly the `Subtype'.bvar`
shift amount. -/
theorem quote_depth_shift_n {k d v e}
    (hle : k ≤ d) (hq : quote fuelω k v = some e) :
    quote fuelω d v = some (e.shift (d - k) 0) := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le hle
  simp only [Nat.add_sub_cancel_left]
  clear hle
  induction n with
  | zero => simp only [Nat.add_zero, Expr.shift_zero]; exact hq
  | succ m ih =>
      have h1 := quote_depth_shift ih
      rw [Expr.shift_shift_same, Nat.add_comm 1 m] at h1
      exact h1

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

/-- The seen-set quotes into `Se`. -/
abbrev QuotesSeen (S : List (Val × Val)) (Γ : TyCtx) (Se : Seen) : Prop :=
  ∀ p ∈ S, ∃ pe ∈ Se,
    quote fuelω Γ.size p.1 = some pe.1 ∧
    quote fuelω Γ.size p.2 = some pe.2

/-- The type context quotes into `Γe` at matching de Bruijn
indices. `Γ` is level-indexed (`Γ[k]` = type of `.var k`);
`Γe` is index-indexed (`Γe[i]` = type of `.bvar i`). The
quote depth is `k`: entry `k` was *added* when `Γ` had size
`k`, so its Val's neutrals reference levels `0..k-1` and
should quote at depth `k` (not `k+1`) to land in the right
`Γe`-relative slot. (`tyCheck_sound_open`'s `.lam` arm is
the witness — `Subtype'.lam` extends `Γe` with `domB` at
index 0, and `domB` is `quote |Γ| domV`.) -/
abbrev QuotesCtx (Γ : TyCtx) (Γe : Ctx) : Prop :=
  ∀ k τ, Γ[k]? = some τ →
    ∃ τe, Γe.get? (Γ.size - 1 - k) = some τe ∧
          quote fuelω k τ = some τe

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
    -- lam: decompose via `quote_lam`; domain via `ihD`;
    -- body via `ihB` at `Γ.push domA` then `Subtype'.narrow`
    -- to `(domBe :: Γe)`. Three residual obstructions in the
    -- body sub-goal (see inline).
    (fun {S Γ domA domB clA clB bA bB}
         hopenA hopenB _hD _hB ihD ihB
         {Se Γe ae be} hS hΓ ha hb => by
      obtain ⟨domAe, bodyAe, hdomAe, hclA, haeq⟩ := quote_lam ha
      obtain ⟨domBe, bodyBe, hdomBe, hclB, hbeq⟩ := quote_lam hb
      subst haeq hbeq
      have hcontra : Subtype' Se Γe domBe domAe :=
        ihD hS hΓ (quoteω hdomBe) (quoteω hdomAe)
      refine .lam hcontra ?_
      -- Goal: Subtype' Se (domBe :: Γe) bodyAe bodyBe.
      -- Plan: ihB at QuotesSeen/QuotesCtx for `Γ.push domA`,
      -- with body quotes from `quoteClosure_eq_quote_openω_fresh`,
      -- giving `Subtype' Se' (domAe::Γe) bodyAe bodyBe`; then
      -- `Subtype'.narrow hSc hcontra` to `(domBe::Γe)`.
      -- Obstructions:
      --  (a) `QuotesSeen S (Γ.push domA) Se`: depth changes
      --      d→d+1, so each pe must shift. With
      --      `Seen.Closed Se` (root #1), `pe.shift = pe`
      --      (`Seen.Closed.shift_map_eq`). All callers pass
      --      `Se = []`; adding `(hSc : Seen.Closed Se)` to
      --      the bridge signatures is the clean fix.
      --  (b) `quote_{d+1} bA = bodyAe`: from
      --      `quoteClosure_eq_quote_openω_fresh hopenA
      --       (quoteClosureω hclA) hunfA` where `hunfA` is the
      --      unf=1↔4 *equality* on this closure (root #2,
      --      stronger than `eval_unf_equiv`'s ≡). The ≡ form
      --      suffices via `.trans` if we let `bodyAe` and
      --      `quote_{d+1} bA` differ.
      --  (c) `Subtype'.narrow` (root #1, `ctx_extend_at`'s
      --      sorry) for `(domAe::Γe) → (domBe::Γe)`.
      -- Once (a)–(c) are available:
      --   have hΓ' := QuotesCtx.push hΓ (quoteω hdomAe)
      --   have hbA := quoteClosure_eq_quote_openω_fresh
      --                 hopenA (quoteClosureω hclA) hunfA
      --   have hbB := … hopenB (quoteClosureω hclB) hunfB
      --   exact Subtype'.narrow hSc hcontra
      --     (ihB hS' hΓ' (by simpa [Array.size_push] using hbA)
      --                  (by simpa [Array.size_push] using hbB))
      sorry)
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
    -- `QuotesCtx` (depth-k convention) gives Γe[d-1-k] = τe'
    -- with quote_k τ = τe'. `Subtype'.bvar` gives
    -- `bvar i ⊑ (Γe[i]).shift (i+1) 0` where i = d-1-k, so
    -- the shift amount is `d-k`. The goal's `τe = quote_d τ`,
    -- which by `quote_depth_shift_n` equals
    -- `τe'.shift (d-k) 0` — exactly the `.bvar` conclusion.
    (fun {Γ k τ} hk {Se Γe ne τe} hΓ hn hτ => by
      obtain ⟨hkd, hne⟩ := quoteNeutral_var hn
      subst hne
      obtain ⟨τe', hget, hqk⟩ := hΓ k τ hk
      have hqd := quote_depth_shift_n (Nat.le_of_lt hkd) hqk
      rw [hτ] at hqd; injection hqd with heq
      rw [heq, show Γ.size - k = Γ.size - 1 - k + 1 from by omega]
      exact .bvar hget)
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

/-- Open-context `subCheckVal_sound`: direct from
`SubV_to_Subtype'` at general `Γ` (closed wrapper in
Soundness.lean specialises at `Γ = #[]`). -/
theorem subCheckVal_sound_open
    {fuel : Nat} (hfuel : fuel ≤ fuelω)
    {Γ : TyCtx} {Γe : Ctx} (hΓ : QuotesCtx Γ Γe)
    {a b : Val}
    (h : subCheckVal fuel Γ [] a b = .ok true)
    {ae be : Expr}
    (hqa : quote fuelω Γ.size a = some ae)
    (hqb : quote fuelω Γ.size b = some be) :
    Subtype' [] Γe ae be :=
  SubV_to_Subtype'
    (subCheckVal_subV hfuel h)
    (fun _ hp => absurd hp (List.not_mem_nil _))
    hΓ hqa hqb

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
    Subtype' [] Γe (e.substEnv ρe) e' :=
  R_quote_equiv Nat.one_pos (eval_realises heval hctx.henv hcl) hq

/-- The empty context is trivially open. `ρe = []`. -/
theorem OpenCtx.empty : OpenCtx #[] [] [] [] where
  hΓ := fun _ _ hk => by simp at hk
  hρq := fun _ _ hk => by simp at hk
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

/-- The `hnfq` evidence each `OpenCtx.eval_quotes` call site
needs. This is the open-Γ analogue of the `(nf fuelω
e).isSome` side condition in `quote_total_on_eval`
(Soundness.lean) — i.e., "evaluating `e` under `ρ` and
quoting at depth `Γ.size` succeeds within `fuelω`". It is
**not** derivable from `OpenCtx` alone (the
closure-body-fuel counterexample applies at every `Γ`/`ρ`,
not just the empty one — `eval 2 unf ρ (.lam .type huge)`
succeeds at fuel 2 while `quoteClosure` re-evals `huge`
unboundedly).

**This statement is false.** The intended use-pattern was:
at `OpenCtx.empty`, derive from caller's `hnfe`; under
`push_fresh`, derive from caller's evidence for the
enclosing `.lam` (one `quoteClosure` step). But neither
the caller's `hnfe` nor the enclosing-lam evidence is in
scope here. The right shape is one of:

  (a) **Per-call hypothesis**: change every `*_sound_open`
      to take `(hnfq : ((eval fuelω unfBound ρ
      e).bind (quote fuelω Γ.size)).isSome)` for its own
      `e`, and discharge the recursive call's hypothesis by
      one `quote`/`quoteClosure`-step from it. The closed
      wrappers in `Soundness.lean` already pass `hnfe`/
      `hnfτ` at the top, so this is "thread it through".
      Each binder case (`.lam`/`.letE`) needs `hnfq_body`
      derived from `hnfq_lam` via the `quoteClosure`-step;
      `.asc` needs `hnfq_τ0` derived from … nothing (the
      ascription type is not a sub-eval of `e` — same
      `.asc`-residual the closed `tyCheck_sound_closed`
      already has).

  (b) **`OpenNf`-bundle in `OpenCtx`**: add `hnfρ : ∀ k v,
      ρ[k]? = some v → quote fuelω Γ.size v ≠ none` to the
      structure (almost what `hρq` already says — could
      strengthen `hρq` and drop this).

Route (a) is the same shape as `quote_total_on_eval`'s
`hnf` threading; cleanest. Until then, this `sorry` stands
for "all `OpenCtx.eval_quotes` call sites have evidence
the caller could have threaded". -/
theorem openNf_holds {Γ ρ Γe ρe} (_hctx : OpenCtx Γ ρ Γe ρe)
    {fuel unf e v} (_hfuel : fuel ≤ fuelω)
    (_heval : eval fuel unf ρ e = some v) :
    ((eval fuelω unf ρ e).bind (quote fuelω Γ.size)).isSome := by
  -- False as stated; see docstring. The route-(a) restructure
  -- replaces this with a per-call hypothesis.
  sorry

/-- Convenience wrapper: every `eval`-result under an
`OpenCtx` quotes (modulo `openNf_holds`). DEPRECATED: callers
should switch to `eval_quotes'` and supply `(hnfq)` directly,
then delete this and `openNf_holds`. -/
theorem OpenCtx.eval_quotes {Γ ρ Γe ρe} (hctx : OpenCtx Γ ρ Γe ρe)
    {fuel unf e v} (hfuel : fuel ≤ fuelω)
    (heval : eval fuel unf ρ e = some v) :
    ∃ ve, quote fuelω Γ.size v = some ve :=
  eval_quotable_open hfuel (openNf_holds hctx hfuel heval) heval

/-- Sorry-free replacement for `eval_quotes`: caller supplies
the `(hnfq)` evidence directly (route (a) of the `openNf_holds`
docstring). At `OpenCtx.empty` this is the closed-form `(hnf)`
the `Soundness.lean` wrappers already thread; under `push_fresh`
/`push_let`, derive it via one `quoteClosure`/`bind`-step from
the enclosing call's `(hnfq)`. -/
theorem OpenCtx.eval_quotes' {Γ ρ Γe ρe} (_hctx : OpenCtx Γ ρ Γe ρe)
    {fuel unf e v} (hfuel : fuel ≤ fuelω)
    (hnfq : ((eval fuelω unf ρ e).bind (quote fuelω Γ.size)).isSome)
    (heval : eval fuel unf ρ e = some v) :
    ∃ ve, quote fuelω Γ.size v = some ve :=
  eval_quotable_open hfuel hnfq heval

/-- `Seen.Closed []` is vacuous. -/
private theorem seen_closed_nil : Seen.Closed [] :=
  fun _ hp => absurd hp (List.not_mem_nil _)

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
  have hext := Subtype'.ctx_extend [head] seen_closed_nil hinner
  simpa [Expr.shift_succ] using hext

/-- Lift each `ρ`-entry's quote-witness to depth `d+1`. -/
private theorem hρq_lift {d : Nat} {ρ : Env}
    (hρq : ∀ (k : Nat) (v : Val), ρ[k]? = some v →
           ∃ we, quote fuelω d v = some we) :
    ∀ (k : Nat) (v : Val), ρ[k]? = some v →
    ∃ we, quote fuelω (d + 1) v = some we := by
  intro k v hk
  obtain ⟨we, hwe⟩ := hρq k v hk
  exact ⟨we.shift 1 0, quote_depth_shift hwe⟩

/-- `QuotesCtx` extension under `Γ.push`. The new head
`Γ'[d] = τ` quotes at `d+1` to `Γe'[0] = τe` (given). Each
old `Γ[k]` quotes at `k+1` (unchanged — `QuotesCtx`'s quote
depth is per-entry, not the outer `Γ.size`); only the
*lookup index* into `Γe'` shifts by one (`Γe'[i+1] =
Γe[i]`). -/
theorem QuotesCtx.push {Γ : TyCtx} {Γe : Ctx}
    (hΓ : QuotesCtx Γ Γe)
    {τ : Val} {τe : Expr}
    (hqτ : quote fuelω Γ.size τ = some τe) :
    QuotesCtx (Γ.push τ) (τe :: Γe) := by
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
    obtain ⟨τe', hτe', hqτ'⟩ := hΓ k τ' hk
    refine ⟨τe', ?_, hqτ'⟩
    have hk_lt : k < Γ.size :=
      (Array.getElem?_eq_some_iff.mp hk).1
    have hidx : (Γ.push τ).size - 1 - k
              = (Γ.size - 1 - k) + 1 := by
      simp only [Array.size_push]; omega
    rw [hidx]; simpa using hτe'

/-- Pushing a fresh neutral preserves the invariant.
`ρe' = .bvar 0 :: ρe.map shift` — the standard de-Bruijn
lift. Closes via `REnv_lift` (which packages
`R_fresh_bvar0` for the head and `REnv_depth_lift` for the
tail) and `QuotesCtx.push`. -/
theorem OpenCtx.push_fresh {Γ ρ Γe ρe} (hctx : OpenCtx Γ ρ Γe ρe)
    {τ : Val} {τe : Expr}
    (hqτ : quote fuelω Γ.size τ = some τe) :
    OpenCtx (Γ.push τ) (.neutral (.var Γ.size) :: ρ)
            (τe :: Γe) (.bvar 0 :: ρe.map (·.shift 1 0)) where
  hΓ := QuotesCtx.push hctx.hΓ hqτ
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
        have h := hρq_lift (d := Γ.size) hctx.hρq m v hk
        simpa [Array.size_push] using h
  henv := by
    simpa [Array.size_push] using REnv_lift hctx.henv hctx.hρq
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
    (hclv : val.closedAt ρe.length = true)
    (hqτ : quote fuelω Γ.size valTy = some valTye)
    (hval_le : Subtype' [] Γe (val.substEnv ρe) valTye) :
    OpenCtx (Γ.push valTy) (valV :: ρ)
            (valTye :: Γe)
            ((val.substEnv ρe).shift 1 0
              :: ρe.map (·.shift 1 0)) where
  hΓ := QuotesCtx.push hctx.hΓ hqτ
  hρq := by
    intro k v hk
    cases k with
    | zero =>
        simp only [List.getElem?_cons_zero, Option.some.injEq] at hk
        subst hk
        obtain ⟨qe, hqe⟩ := hctx.eval_quotes hfuel hev
        exact ⟨qe.shift 1 0,
          by simpa [Array.size_push] using quote_depth_shift hqe⟩
    | succ m =>
        simp only [List.getElem?_cons_succ] at hk
        have h := hρq_lift (d := Γ.size) hctx.hρq m v hk
        simpa [Array.size_push] using h
  henv := by
    have hRval := eval_realises hev hctx.henv hclv
    obtain ⟨qe, hqe⟩ := hctx.eval_quotes hfuel hev
    have hRval' := R_depth_lift hqe hRval
    have htail := REnv_depth_lift hctx.henv hctx.hρq
    simpa [Array.size_push] using REnv_cons htail hRval'
  hlen := by simp [Array.size_push, List.length_map, hctx.hlen]
  hwf := by
    intro k w τe' hw hτe'
    cases k with
    | zero =>
        simp only [List.getElem?_cons_zero, List.get?_cons_zero,
                   Option.some.injEq] at hw hτe'
        subst hw hτe'
        exact Subtype'.ctx_extend [valTye] seen_closed_nil hval_le
    | succ m =>
        simp only [List.getElem?_cons_succ,
                   List.get?_cons_succ] at hw hτe'
        exact hwf_lift_tail hctx.hwf valTye m w τe' hw hτe'

/-- Open-context `whnfPi_sound`: each unfold step is one
declarative `.unfold_fix_R`/`.unfold_iota_R`, so the exposed
head is `≡` the input. Same shape as `whnfPi_sound`
(Soundness.lean) but at general `Γ`/`Γe`. -/
theorem whnfPi_sound_open {fuel : Nat}
    {Γ : TyCtx} {Γe : Ctx} (hΓ : QuotesCtx Γ Γe)
    {inhab τV τV' : Val}
    (hwh : whnfPi fuel inhab τV = some τV')
    {τe τe' : Expr}
    (hqτ : quote fuelω Γ.size τV = some τe)
    (hqτ' : quote fuelω Γ.size τV' = some τe') :
    Equiv τe' τe := by
  -- Induction on `unfBound`; each `.fix`/`.iota` step is
  -- `Equiv.fix_unfold`/`Equiv.iota_unfold` after
  -- `quote_open_subst`. Same dependency chain as the
  -- closed form.
  sorry

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
      obtain ⟨τe0, hΓe, hqτe0⟩ := hctx.hΓ _ _ hΓk
      have hidx : Γ.size - 1 - (Γ.size - 1 - k) = k := by omega
      rw [hidx] at hΓe
      -- Lift the quote from depth `Γ.size-1-k` to `Γ.size`:
      have hqτe := quote_depth_shift_n (d := Γ.size)
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
        obtain ⟨τe, hqτV⟩ := hctx.eval_quotes hfuel' hτV0
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
        letBinderType_sound_open hfuel' hctx hcl_val hletB
      have hctx' :=
        hctx.push_let (val := val) hfuel' hev hcl_val hqValTy hval_le
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
        have hsub :=
          subCheckVal_sound_open hfuel hctx.hΓ h hqeTy hqτ
        exact .trans h_e_eTye hsub
    | none =>
        simp only [] at h
        split at h
        · next eV heV =>
          obtain ⟨eVe, hqeV⟩ := hctx.eval_quotes hfuel heV
          have h_e_eVe := (hctx.eq heV hcl hqeV).2
          have hsub :=
            subCheckVal_sound_open hfuel hctx.hΓ h hqeV hqτ
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
      have hctx' := hctx.push_fresh (τ := expDom) hqDom
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
      obtain ⟨dome, hqdomV⟩ := hctx.eval_quotes hfuel' hdomV
      have hcontra : Subtype' [] Γe expDome (dom.substEnv ρe) :=
        .trans
          (subCheckVal_sound_open hfuel' hctx.hΓ hokDom hqDom hqdomV)
          (hctx.eq hdomV hcl_dom hqdomV).1
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
        letBinderType_sound_open hfuel' hctx hcl_val hletB
      -- Extended context (push_let is proven; with the
      -- `QuotesCtx` depth-`k` convention, `valTye` at depth
      -- `Γ.size` is exactly the head we cons):
      have hctx' :=
        hctx.push_let (val := val) hfuel' hev hcl_val hqValTy hval_le
      -- IH: body at hctx', expected τV at depth Γ.size+1.
      have hIH :=
        tyCheck_sound_open hfuel' hctx'
          (by simpa [List.length_map] using hcl_body)
          (by simpa [Array.size_push] using quote_depth_shift hqτ)
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
            obtain ⟨τ0e, hqτ0V⟩ := hctx.eval_quotes hfuel' hτ0V
            -- IH (same Γ/ρ): `(e0.substEnv ρe) ⊑ τ0e`.
            have h_e0_τ0e :=
              tyCheck_sound_open hfuel' hctx hcl.1 hqτ0V hinner
            have hsub :=
              subCheckVal_sound_open hfuel' hctx.hΓ h hqτ0V hqτ
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
         obtain ⟨ee, hqeV⟩ := hctx.eval_quotes hfuel' hev
         have hsub :=
           subCheckVal_sound_open hfuel' hctx.hΓ h hqeV hqτ
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
    obtain ⟨valVe, hqvalV⟩ := hctx.eval_quotes hfuel hev
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
