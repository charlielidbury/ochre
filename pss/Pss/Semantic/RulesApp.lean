import Pss.Semantic.Model
import Pss.Semantic.ModelLemmas
import Pss.Semantic.Conversion

/-!
# Per-rule soundness: the application rules

§6 of `pss/docs/03-revised-proof.md`, W-APP and DS-APP — the cases with
exact step/depth accounting (`j = j₁ + 1 + j₂` paying for tier depth
`k − j₁ − 1`; doc §9 calls the off-by-ones here the likeliest mechanical
bug, and `converges_app_factor` / `converges_app_beta` in
`WeakHead.lean` fix the arithmetic once).

Hypotheses match the `Instrumented` constructors under the fundamental
theorem's motives. `SubI.app` carries its endpoints' W-APP
instrumentations *unpacked* as four `WellSubI` premises; their motive
images are the four `And`-triples below, passed verbatim by
`Fundamental.lean` — every component is available, none may be dropped.

**Note for the implementer of `sound_app_le` — the bound-conversion
chain (c).** The doc's chain `S =β A =β A′ =β S′` connects the bounds of
the two independent W-APP instrumentations through (a) the unprimed
head's converged bound, (b) the `MATCH_∀(w_T, w_{T′})` bound clause, and
(a′) the primed head's converged bound. It has no clean γ-free
standalone statement: every link lives under the local convergence
analysis of `T(U)`'s member (the factorization witnesses `A`, `A′` are
existentially produced inside the case). Build it as an explicit `have`
chain inside the proof, per the §9 watchpoint, rather than as a lemma.
-/

namespace Pss.Semantic

/-- **W-APP** (doc §6): a converging member of `⟦T(U)⟧` factors through
`T ⇓ w_T` (`converges_app_factor`); `w_T` is a λ with bound `=β S` by
the `t ≤ λx≤s.Top` premise's (m3) (*were it `Top`, the member side of
MATCH would fail — the progress-critical step*); `U` is good at every
depth from the `u ≤ s` premise's membership and **inclusion** halves;
the head's self-MATCH tier at `j′ = k − j₁ − 1` self-describes the
contractum, and `⟦T(U)⟧ₖ = ⟦[x↦U]B⟧ₖ` by Lemma 4.3. Matches `WfI.app`
(premise triples projected by `Fundamental.lean`). -/
theorem sound_wapp {Γ : Ctx} {t u s : Term}
    (h₁ : SemLe Γ t (.lam s .top)) (h₂ : SemLe Γ u s)
    (hwt : SemWf Γ t) (hwu : SemWf Γ u) :
    SemWf Γ (.app t u) := by
  intro k γ hγ
  rw [Mem_unfold]
  intro j v hj hconv
  obtain ⟨j₁, w, hj₁le, hconvT, hcase⟩ := converges_app_factor hconv
  -- (1) The head's value is a λ whose bound is β-convertible to `S`, by the
  -- `t ≤ λx≤s.Top` premise at index `j₁ + 1 ≤ k` — were it `Top`, the member
  -- side of (m3) would fail: the progress-critical step.
  have hlam : ∃ A B, w = .lam A B ∧ Beta A (s.subst γ) := by
    have hmem : Mem (j₁ + 1) (t.subst γ) ((Term.lam s .top).subst γ) :=
      (h₁ (j₁ + 1) γ (semCtx_antitone (by omega) hγ)).1
    rw [Mem_unfold] at hmem
    obtain ⟨-, w', hw'conv, -, hmatch⟩ := hmem j₁ w (by omega) hconvT
    obtain ⟨i', hw'c⟩ := hw'conv
    have hself : Converges 0 ((Term.lam s .top).subst γ) ((Term.lam s .top).subst γ) :=
      ⟨.refl, whNormal_of_value (.lam _ _)⟩
    obtain ⟨-, rfl⟩ := Converges.deterministic hw'c hself
    rw [Match_unfold] at hmatch
    rcases hmatch with htop | ⟨a, b, α, β, hweq, hveq, hβ, -⟩
    · exact Term.noConfusion htop
    · injection hweq with ha hb
      exact ⟨α, β, hveq, ha ▸ hβ⟩
  rcases hcase with ⟨A, B, rfl, j₂, hjeq, hconvB⟩ | ⟨hnotlam, -, -⟩
  · -- λ branch: `j = j₁ + 1 + j₂`, `Converges j₂ ([U]B) v`.
    obtain ⟨A', B', heq, hAS⟩ := hlam
    injection heq with hA hB
    subst hA; subst hB
    -- (2) Self-MATCH of the head's value at the ambient index `k`, from `hwt`.
    have hmemTT : Mem k (t.subst γ) (t.subst γ) := hwt k γ hγ
    rw [Mem_unfold] at hmemTT
    obtain ⟨-, w'', hw''conv, -, hmatchTT⟩ := hmemTT j₁ (.lam A B) (by omega) hconvT
    obtain ⟨i'', hw''c⟩ := hw''conv
    obtain ⟨-, rfl⟩ := Converges.deterministic hw''c hconvT
    rw [Match_unfold] at hmatchTT
    rcases hmatchTT with htop | ⟨a, b, α, β, hweq, hveq, -, htier⟩
    · exact Term.noConfusion htop
    · injection hweq with ha hb
      subst ha; subst hb
      injection hveq with hα hβ
      subst hα; subst hβ
      -- (3) `U` is a good argument of `A` at depth `k - j₁ - 1`: memberships
      -- and inclusions from the `u ≤ s` premise (indices ≤ k), transported
      -- across `Beta A S` by Lemma 4.4.
      have hgood : Good (k - j₁ - 1) A (u.subst γ) := by
        rw [Good_unfold]
        refine ⟨?_, ?_, ?_⟩
        · exact (mem_beta_type hAS).mpr
            (h₂ (k - j₁ - 1) γ (semCtx_antitone (by omega) hγ)).1
        · exact hwu (k - j₁ - 1) γ (semCtx_antitone (by omega) hγ)
        · intro i s' hi hmem
          exact (mem_beta_type hAS).mpr
            ((h₂ i γ (semCtx_antitone (by omega) hγ)).2 s' hmem)
      -- (4) The tier at depth `j' = k - j₁ - 1` self-describes the contractum.
      have hmemB := (htier (k - j₁ - 1) (u.subst γ) (by omega) hgood).1
      -- (5) Run the contractum's membership on `[U]B ⇓^{j₂} v`; its (m3) value
      -- is `v` itself by determinism, and `(k-j₁-1) - j₂ = k - j` exactly.
      rw [Mem_unfold] at hmemB
      obtain ⟨hvval, w₃, hw₃conv, -, hmatchv⟩ := hmemB j₂ v (by omega) hconvB
      obtain ⟨i₃, hw₃c⟩ := hw₃conv
      obtain ⟨-, rfl⟩ := Converges.deterministic hconvB hw₃c
      refine ⟨hvval, v, ⟨j, hconv⟩, hvval, ?_⟩
      have harith : k - j₁ - 1 - j₂ = k - j := by omega
      rwa [harith] at hmatchv
  · -- Stuck branch refuted: the head's value is a λ by (1).
    obtain ⟨A, B, heq, -⟩ := hlam
    exact absurd heq (hnotlam A B)

/-! ## The definable-observer kit (research phase, sem/impl-rulesapp)

Private, fully proven. `Ω := (λx≤⊤.x x)(λx≤⊤.x x)` weak-head loops, so
`λx≤A.Ω` is a *universal probe* for λ-shaped types: it matches every λ-value
with bound `=β A` at **every** index (its tiers are vacuous by divergence),
and `⊤` probes exactly the ⊤-valued types. Pushed through the **inclusion
halves** of the DS-APP hypotheses — which fire at *member* steps, not type
steps — these probes extract the primed head's convergence, λ-shape, and the
full bound chain `A =β A′ =β S′` at index 1, with **no budget condition on
`j₁`/`j₁′`** (`primed_head` below). This closes the (a′) sub-gap of the wall
report and reduces the remaining gap to the deep tier content alone. -/

/-- The looping combinator's half: `λx≤⊤. x x`. -/
private def OmegaArg : Term := .lam .top (.app (.var 0) (.var 0))

/-- `Ω := (λx≤⊤. x x)(λx≤⊤. x x)` (weak-head loops in one step). -/
private def Omega : Term := .app OmegaArg OmegaArg

/-- `Ω` is closed: substitution fixes it (definitional). -/
private theorem omega_subst (σ : Nat → Term) : Omega.subst σ = Omega := rfl

private theorem omega_whStep : WHStep Omega Omega := WHStep.beta

private theorem evals_omega {j : Nat} {u : Term} (h : Evals j Omega u) :
    u = Omega := by
  induction j generalizing u with
  | zero => cases h; rfl
  | succ j ih =>
    cases h with
    | step hs h' =>
      rw [hs.deterministic omega_whStep] at h'
      exact ih h'

/-- `Ω ⇑`: no weak-head normal form. -/
private theorem omega_diverges : Diverges Omega := by
  rintro w ⟨j, he, hn⟩
  rw [evals_omega he] at hn
  exact hn Omega omega_whStep

/-- A term with no weak-head normal form is in every extension. -/
private theorem mem_of_diverges {k : Nat} {s T : Term} (h : Diverges s) :
    Mem k s T := by
  rw [Mem_unfold]
  intro j v _ hc
  exact absurd ⟨j, hc⟩ (h v)

/-- Members of `⟦Ω⟧` are divergent, hence members of everything. -/
private theorem mem_of_mem_omega {k : Nat} {s T : Term}
    (h : Mem k s Omega) : Mem k s T := by
  rw [Mem_unfold] at h ⊢
  intro j v hj hc
  obtain ⟨-, w, hw, -, -⟩ := h j v hj hc
  exact absurd hw (omega_diverges w)

/-- **Probe introduction**: `λx≤A.Ω ∈ ⟦X⟧ₖ` for every `k`, as soon as `X`
converges to `⊤` or to a λ whose bound is `=β A`. The tiers are vacuous:
`Ω[c] = Ω` diverges. -/
private theorem lamOmega_mem_intro {k : Nat} {A X w : Term}
    (hX : ConvergesTo X w) (hval : Term.Value w)
    (hshape : w = .top ∨ ∃ a b, w = .lam a b ∧ Beta A a) :
    Mem k (.lam A Omega) X := by
  rw [Mem_unfold]
  intro j v hj hc
  obtain ⟨-, rfl⟩ := Converges.deterministic hc
    ⟨.refl, whNormal_of_value (.lam _ _)⟩
  refine ⟨.lam _ _, w, hX, hval, ?_⟩
  rw [Match_unfold]
  rcases hshape with rfl | ⟨a, b, rfl, hba⟩
  · exact .inl rfl
  · refine .inr ⟨a, b, A, Omega, rfl, rfl, hba, ?_⟩
    intro j' c _ _
    have hΩ : Omega.subst1 c = Omega := omega_subst _
    rw [hΩ]
    exact ⟨mem_of_diverges omega_diverges,
           fun s' hs' => mem_of_mem_omega hs'⟩

/-- **Probe elimination**: a membership of `λx≤A.Ω` at any positive index
yields the type's weak-head value together with its shape/bound link. -/
private theorem lamOmega_mem_elim {k : Nat} {A X : Term} (hk : 1 ≤ k)
    (h : Mem k (.lam A Omega) X) :
    ∃ w, ConvergesTo X w ∧ Term.Value w ∧
      (w = .top ∨ ∃ a b, w = .lam a b ∧ Beta A a) := by
  rw [Mem_unfold] at h
  obtain ⟨-, w, hw, hval, hmatch⟩ :=
    h 0 (.lam A Omega) hk ⟨.refl, whNormal_of_value (.lam _ _)⟩
  refine ⟨w, hw, hval, ?_⟩
  rw [Match_unfold] at hmatch
  rcases hmatch with htop | ⟨a, b, α, β, hweq, hveq, hβ, -⟩
  · exact .inl htop
  · injection hveq with h1 _
    exact .inr ⟨a, b, hweq, h1 ▸ hβ⟩

/-- **⊤-probe introduction**: `⊤ ∈ ⟦X⟧ₖ` whenever `X ⇓ ⊤`. -/
private theorem top_mem_intro {k : Nat} {X : Term}
    (hX : ConvergesTo X .top) : Mem k .top X := by
  rw [Mem_unfold]
  intro j v hj hc
  obtain ⟨-, rfl⟩ := Converges.deterministic hc ⟨.refl, whNormal_of_value .top⟩
  refine ⟨.top, .top, hX, .top, ?_⟩
  rw [Match_unfold]
  exact .inl rfl

/-- **⊤-probe elimination**: `⊤`'s membership at a positive index forces the
type's weak-head value to be `⊤` (the member side of a λ-MATCH must be a λ). -/
private theorem top_mem_elim {k : Nat} {X : Term} (hk : 1 ≤ k)
    (h : Mem k .top X) : ∃ w, ConvergesTo X w ∧ w = .top := by
  rw [Mem_unfold] at h
  obtain ⟨-, w, hw, -, hmatch⟩ := h 0 .top hk ⟨.refl, whNormal_of_value .top⟩
  refine ⟨w, hw, ?_⟩
  rw [Match_unfold] at hmatch
  rcases hmatch with htop | ⟨a, b, α, β, -, hveq, -, -⟩
  · exact htop
  · exact Term.noConfusion hveq

/-- **(P1), budget-free primed head** (research phase): under DS-APP's
hypotheses, if the unprimed head converges to `λA.B` — at *any* evaluation
length `j₁`, in or out of budget — then the primed head converges to a value
`λA′.B′` with the full bound chain `Beta A S`, `Beta A A′`, `Beta A′ S′`.

Proof = the observer argument: `λx≤A.Ω ∈ ⟦T⟧₁` (probe introduction on `T`'s
own convergence, which is a type-side, unbudgeted fact); the inclusion halves
of `h₁`/`hle₁`/`hle₃` at index `1 ≤ k` transport the probe; elimination reads
off shape and bounds. `w_{T′} = ⊤` is refuted by transporting the ⊤-probe
into `⟦λx≤S′.⊤⟧₁`. This discharges the wall report's (a′) and the chain (c)
with no appeal to memberships above the budget. -/
private theorem primed_head {Γ : Ctx} {t t' s s' : Term} {k j₁ : Nat}
    {γ : Nat → Term} {A B : Term}
    (h₁ : SemLe Γ t t') (hle₁ : SemLe Γ t (.lam s .top))
    (hle₃ : SemLe Γ t' (.lam s' .top))
    (hγ : SemCtx k Γ γ) (hk : 1 ≤ k)
    (hT : Converges j₁ (t.subst γ) (.lam A B)) :
    Beta A (s.subst γ) ∧
    ∃ A' B', ConvergesTo (t'.subst γ) (.lam A' B') ∧
      Beta A A' ∧ Beta A' (s'.subst γ) := by
  have hγ1 : SemCtx 1 Γ γ := semCtx_antitone hk hγ
  -- The probe is in ⟦T⟧₁ by T's own convergence (type side, unbudgeted).
  have hprobeT : Mem 1 (.lam A Omega) (t.subst γ) :=
    lamOmega_mem_intro ⟨j₁, hT⟩ (.lam A B) (.inr ⟨A, B, rfl, Beta.refl A⟩)
  -- (c) unprimed link: transport the probe into ⟦λx≤S.⊤⟧₁ and eliminate.
  have hAS : Beta A (s.subst γ) := by
    have hmem : Mem 1 (.lam A Omega) ((Term.lam s .top).subst γ) :=
      (hle₁ 1 γ hγ1).2 _ hprobeT
    obtain ⟨w, hw, -, hshape⟩ := lamOmega_mem_elim (Nat.le_refl 1) hmem
    obtain ⟨-, rfl⟩ := Converges.deterministic hw.choose_spec
      ⟨.refl, whNormal_of_value (.lam _ _)⟩
    rcases hshape with htop | ⟨a, b, heq, hba⟩
    · exact Term.noConfusion htop
    · injection heq with ha _
      exact ha ▸ hba
  -- Transport the probe into ⟦T′⟧₁: T′ converges to a value.
  have hprobeT' : Mem 1 (.lam A Omega) (t'.subst γ) :=
    (h₁ 1 γ hγ1).2 _ hprobeT
  obtain ⟨w', hw', hval', hshape'⟩ := lamOmega_mem_elim (Nat.le_refl 1) hprobeT'
  -- (c) primed link, for any probe bound β-convertible to A.
  have hS' : ∀ {A₀ : Term}, Mem 1 (.lam A₀ Omega) (t'.subst γ) →
      Beta A₀ (s'.subst γ) := by
    intro A₀ hmem
    have hmem' : Mem 1 (.lam A₀ Omega) ((Term.lam s' .top).subst γ) :=
      (hle₃ 1 γ hγ1).2 _ hmem
    obtain ⟨w, hw, -, hshape⟩ := lamOmega_mem_elim (Nat.le_refl 1) hmem'
    obtain ⟨-, rfl⟩ := Converges.deterministic hw.choose_spec
      ⟨.refl, whNormal_of_value (.lam _ _)⟩
    rcases hshape with htop | ⟨a, b, heq, hba⟩
    · exact Term.noConfusion htop
    · injection heq with ha _
      exact ha ▸ hba
  rcases hshape' with rfl | ⟨a', b', rfl, hAa'⟩
  · -- w′ = ⊤ is refuted by the ⊤-probe through hle₃'s inclusion.
    exfalso
    have htop : Mem 1 (Term.top) (t'.subst γ) := top_mem_intro hw'
    have htop' : Mem 1 (Term.top) ((Term.lam s' .top).subst γ) :=
      (hle₃ 1 γ hγ1).2 _ htop
    obtain ⟨w, hw, hweq⟩ := top_mem_elim (Nat.le_refl 1) htop'
    obtain ⟨-, rfl⟩ := Converges.deterministic hw.choose_spec
      ⟨.refl, whNormal_of_value (.lam _ _)⟩
    exact Term.noConfusion hweq
  · -- w′ = λA′.B′ with Beta A A′; close the chain with Beta A′ S′.
    have hAS' : Beta A (s'.subst γ) := hS' hprobeT'
    exact ⟨hAS, a', b', hw', hAa', (Beta.symm hAa').trans hAS'⟩

/-- **DS-APP, ≤-form** (doc §6, steps (a)–(g)): both applications
weak-head factor (4.3), the function values MATCH at every index, `U` is
∀-good at `A′` via member conversion (4.5, ∀-index available) and the
bound chain (c), the strengthened tier at `c = U` gives the inclusion at
`k`, and primed conversion (substitutivity + 4.4) closes the chain
`⟦T(U)⟧ₖ = ⟦[x↦U]B⟧ₖ ⊆ ⟦[x↦U]B′⟧ₖ = ⟦[x↦U′]B′⟧ₖ = ⟦T′(U′)⟧ₖ`.
Membership half via Lemma 3.3 from the unprimed instrumentation's wf
(`sound_wapp` on `hi₁`/`hi₂`). Matches `SubI.app` at `r = .le`; the four
triples are the motive images of its four `WellSubI` premises. -/
theorem sound_app_le {Γ : Ctx} {t t' u u' s s' : Term}
    (h₁ : SemLe Γ t t') (h₂ : SemEq Γ u u')
    (hi₁ : SemWf Γ t ∧ SemWf Γ (.lam s .top) ∧ SemLe Γ t (.lam s .top))
    (hi₂ : SemWf Γ u ∧ SemWf Γ s ∧ SemLe Γ u s)
    (hi₃ : SemWf Γ t' ∧ SemWf Γ (.lam s' .top) ∧ SemLe Γ t' (.lam s' .top))
    (hi₄ : SemWf Γ u' ∧ SemWf Γ s' ∧ SemLe Γ u' s') :
    SemLe Γ (.app t u) (.app t' u') := by
  /- IMPLEMENTER WALL REPORT (sem/impl-rulesapp), rev. 2 after the research
  phase. The doc's §6 DS-APP proof has a quantifier-budget gap for nonempty
  `Γ`: Definition 3.2 binds the index and `γ ∈ ⟦Γ⟧ₖ` jointly, antitonicity is
  downward-only, and §6 instantiates premises at indices up to `k+j₁+1` —
  the preamble's "at ∀-index via the ∀ in Definition 3.2" is false for the
  fixed `γ`. Status of the doc's steps after this session:

  CLOSED IN BUDGET (kernel-checked above, no `j₁`/`j₂′` conditions):
  · (a′) + chain (c): `primed_head` — the `λx≤A.Ω`/`⊤` probes pushed through
    the INCLUSION halves (which fire at member steps, never type steps)
    force `T′ ⇓ λA′.B′` and `S =β A =β A′ =β S′` at index 1.
  · (d): needs no 4.5 — `U ∈ ⟦A′⟧ᵢ` follows from hi₂'s wf + inclusion halves
    and `mem_beta_type` (4.4, now fully proven) along the chain (c).
  · `[U]B′ ⇓ value` + shape/bound link: the same probes through the
    function-pair tier (t2) at `j′ = 1` — needs only `j₁ ≤ k−2`.

  THE RESIDUAL (the precise open core): the goal's deep tier content.
  Elementwise at `σ ⇓ʲ v`, `j < k`, the goal `Match (k−j) v w″` composes σ's
  own MATCH with pair facts on the contracta; every derivable pair fact caps
  at tier depth `(k−j₁−1) − j₂′`, and `j` is independent of `j₁+1+j₂′`, so
  fast members of slow types need depths the budget cannot reach. The same
  self-MATCH wall recurs at every level of the descent (`Match m w w` above
  `k − (steps of w's source)` is underivable). This is the same root cause
  as Conversion.lean's `TierTransport` residual (4.5, doc §4 tier (t1)) —
  one joint invariant would close both.

  TRUTH: conjectured TRUE, open. The countermodel constraint system is
  near-exhaustively closed: closed pairs die at ∀-good substitutions;
  context-manufactured pairs (`x₂ ≤ x₁`) hand the conclusion over via
  `Good`'s own inclusion components at full `k`; padding the heads
  (`t := I^N t₀`) strips memberships but inclusions and the goal are
  4.3-invariant; divergence cannot be capped (divergent bodies are good at
  every bound, so caps require reachable defects, and evaluation cannot
  distinguish capped towers from their ⊤-completions without sticking).
  What is missing in both directions is a quantitative lemma linking
  goodness depth, evaluation length, and value self-description — beyond
  transcription of the doc. See the commit history of this file for the
  full constraint-system analysis and the erratum draft for doc §6. -/
  sorry

/-- **DS-APP, ≡-form** (doc §6): conversion by congruence, wf of both
applications from their W-APP instrumentations. Matches `SubI.app` at
`r = .eq`. -/
theorem sound_app_eq {Γ : Ctx} {t t' u u' s s' : Term}
    (h₁ : SemEq Γ t t') (h₂ : SemEq Γ u u')
    (hi₁ : SemWf Γ t ∧ SemWf Γ (.lam s .top) ∧ SemLe Γ t (.lam s .top))
    (hi₂ : SemWf Γ u ∧ SemWf Γ s ∧ SemLe Γ u s)
    (hi₃ : SemWf Γ t' ∧ SemWf Γ (.lam s' .top) ∧ SemLe Γ t' (.lam s' .top))
    (hi₄ : SemWf Γ u' ∧ SemWf Γ s' ∧ SemLe Γ u' s') :
    SemEq Γ (.app t u) (.app t' u') :=
  ⟨Beta.app h₁.1 h₂.1,
   sound_wapp hi₁.2.2 hi₂.2.2 hi₁.1 hi₂.1,
   sound_wapp hi₃.2.2 hi₄.2.2 hi₃.1 hi₄.1⟩

end Pss.Semantic
