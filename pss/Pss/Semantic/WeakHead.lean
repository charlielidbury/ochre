import Pss.Syntax
import Pss.Star
import Pss.Reduction

/-!
# Weak-head reduction for System λ⊲

§1 of `pss/docs/03-revised-proof.md`: weak-head reduction `↦` (the unique
redex contracted is the head one), exact-step evaluation `t ↦ʲ w`,
convergence `t ⇓ʲ w` / `t ⇓ w` / divergence `t ⇑`, spines
`Top(d₁)…(dₙ)`, Fact 1.1 (classification of closed weak-head normal
forms), and the head-factorization of `⇓` through application (the doc's
§9 watchpoint: the step arithmetic `j = j₁ + 1 + j₂` is stated exactly).

Everything lives in `namespace Pss.Semantic`; no existing file is touched.
-/

namespace Pss.Semantic

open Term (Value ClosedUnder)

/-- Weak-head reduction `t ↦ t'` (doc §1): contract the head redex only —
no reduction under λ, in bounds, or in argument position. -/
inductive WHStep : Term → Term → Prop where
  /-- `(λx ≤ a. b)(c) ↦ [x ↦ c]b` (head β). -/
  | beta {t u s : Term} : WHStep (.app (.lam t u) s) (u.subst1 s)
  /-- `t ↦ t' ⟹ t(u) ↦ t'(u)` (head closure). -/
  | head {t t' : Term} (u : Term) : WHStep t t' → WHStep (.app t u) (.app t' u)

/-- `t ↦ʲ u` — exactly `j` weak-head steps (doc §1). -/
inductive Evals : Nat → Term → Term → Prop where
  | refl {t : Term} : Evals 0 t t
  | step {j : Nat} {t t' u : Term} : WHStep t t' → Evals j t' u → Evals (j + 1) t u

/-- `t` is weak-head normal: no `↦`-step from `t` (doc §1). -/
def WHNormal (t : Term) : Prop := ∀ t', ¬ WHStep t t'

/-- `t` is `⟶`-normal: no full-reduction step from `t` (Fact 1.1). -/
def StepNormal (t : Term) : Prop := ∀ t', ¬ Step t t'

/-- `t ⇓ʲ w` — `t ↦ʲ w` with `w` weak-head normal (doc §1). -/
def Converges (j : Nat) (t w : Term) : Prop := Evals j t w ∧ WHNormal w

/-- `t ⇓ w` — `t ⇓ʲ w` for some `j` (doc §1). -/
def ConvergesTo (t w : Term) : Prop := ∃ j, Converges j t w

/-- `t ⇑` — `t` weak-head diverges: no weak-head normal form (doc §1). -/
def Diverges (t : Term) : Prop := ∀ w, ¬ ConvergesTo t w

/-! ## Determinism and basic facts about `↦` -/

/-- `↦ ⊆ ⟶`: a weak-head step is a full-reduction step (doc §1). -/
theorem WHStep.toStep {t t' : Term} (h : WHStep t t') : Step t t' := by
  induction h with
  | beta => exact .eapp
  | head u _ ih => exact ih.appL u

/-- `↦` is deterministic (doc §1). -/
theorem WHStep.deterministic {t t₁ t₂ : Term}
    (h₁ : WHStep t t₁) (h₂ : WHStep t t₂) : t₁ = t₂ := by
  induction h₁ generalizing t₂ with
  | beta =>
    cases h₂ with
    | beta => rfl
    | head u h => cases h
  | head u h ih =>
    cases h₂ with
    | beta => cases h
    | head u h₂ => rw [ih h₂]

/-- Values are weak-head normal (doc §1: `Top` and λs are answers). -/
theorem whNormal_of_value {v : Term} (h : Value v) : WHNormal v := by
  intro v' hs
  cases h with
  | top => cases hs
  | lam t u => cases hs

/-- Inverting weak-head normality at an application: the head is
weak-head normal and is not a λ (else `WHStep.head` / `WHStep.beta`
would fire). The engine of Fact 1.1's induction. -/
theorem whNormal_app_inv {t u : Term} (h : WHNormal (.app t u)) :
    WHNormal t ∧ ∀ a b, t ≠ .lam a b := by
  refine ⟨?_, ?_⟩
  · intro t' hs
    exact h (.app t' u) (.head u hs)
  · intro a b heq
    subst heq
    exact h (b.subst1 u) .beta

/-! ## Step arithmetic for `↦ʲ` and `⇓ʲ`

The doc's §9 singles out step accounting (`j = j₁ + 1 + j₂` paying for
tier depth `k − j₁ − 1` in W-APP) as the likeliest mechanical bug; these
helpers fix the arithmetic once.
-/

/-- Composition of exact-step evaluations. -/
theorem Evals.trans {j₁ j₂ : Nat} {t u v : Term}
    (h₁ : Evals j₁ t u) (h₂ : Evals j₂ u v) : Evals (j₁ + j₂) t v := by
  induction h₁ with
  | refl => simpa using h₂
  | step hs _ ih =>
    rename_i j _ _ _ _
    have := Evals.step hs (ih h₂)
    simpa [Nat.add_right_comm, Nat.add_assoc] using this

/-- Extend an evaluation by one step at the end. -/
theorem Evals.tail {j : Nat} {t u v : Term}
    (h : Evals j t u) (hs : WHStep u v) : Evals (j + 1) t v :=
  h.trans (.step hs .refl)

/-- Decomposition of an evaluation at an additive split of its length. -/
theorem Evals.add_inv {j₁ j₂ : Nat} {t v : Term}
    (h : Evals (j₁ + j₂) t v) : ∃ u, Evals j₁ t u ∧ Evals j₂ u v := by
  induction j₁ generalizing t with
  | zero => exact ⟨t, .refl, by simpa using h⟩
  | succ j₁ ih =>
    rw [Nat.succ_add] at h
    cases h with
    | step hs h' =>
      obtain ⟨u, h1, h2⟩ := ih h'
      exact ⟨u, .step hs h1, h2⟩

/-- Evaluation of the same length is deterministic. -/
theorem Evals.deterministic {j : Nat} {t u₁ u₂ : Term}
    (h₁ : Evals j t u₁) (h₂ : Evals j t u₂) : u₁ = u₂ := by
  induction h₁ with
  | refl => cases h₂; rfl
  | step hs _ ih =>
    cases h₂ with
    | step hs₂ h₂' =>
      rw [hs.deterministic hs₂] at *
      exact ih h₂'

/-- `↦ʲ ⊆ ⟶*` (each weak-head step is a full step). -/
theorem Evals.toSteps {j : Nat} {t u : Term} (h : Evals j t u) :
    Steps t u := by
  induction h with
  | refl => exact .refl
  | step hs _ ih => exact .head hs.toStep ih

/-- Head closure lifts through exact-step evaluation:
`t ↦ʲ t' ⟹ t(u) ↦ʲ t'(u)`. -/
theorem Evals.appL {j : Nat} {t t' : Term} (u : Term)
    (h : Evals j t t') : Evals j (.app t u) (.app t' u) := by
  induction h with
  | refl => exact .refl
  | step hs _ ih => exact .step (.head u hs) ih

/-- Convergence extends backwards along a weak-head step
(one half of the engine of doc Lemma 4.2). -/
theorem Converges.of_whStep {j : Nat} {t t' w : Term}
    (hs : WHStep t t') (h : Converges j t' w) : Converges (j + 1) t w :=
  ⟨.step hs h.1, h.2⟩

/-- Convergence factors forwards through a weak-head step, by determinism
(the other half of the engine of doc Lemma 4.2). -/
theorem Converges.whStep_inv {j : Nat} {t t' w : Term}
    (hs : WHStep t t') (h : Converges (j + 1) t w) : Converges j t' w := by
  obtain ⟨he, hn⟩ := h
  cases he with
  | step hs' he' =>
    rw [hs.deterministic hs'] at *
    exact ⟨he', hn⟩

/-- Convergence is unique, in both the step count and the result
(doc §1: `↦` is deterministic). -/
theorem Converges.deterministic {j₁ j₂ : Nat} {t w₁ w₂ : Term}
    (h₁ : Converges j₁ t w₁) (h₂ : Converges j₂ t w₂) :
    j₁ = j₂ ∧ w₁ = w₂ := by
  obtain ⟨he₁, hn₁⟩ := h₁
  obtain ⟨he₂, hn₂⟩ := h₂
  induction he₁ generalizing j₂ with
  | refl =>
    cases he₂ with
    | refl => exact ⟨rfl, rfl⟩
    | step hs₂ _ => exact absurd hs₂ (hn₁ _)
  | step hs₁ he₁' ih =>
    cases he₂ with
    | refl => exact absurd hs₁ (hn₂ _)
    | step hs₂ he₂' =>
      rw [hs₁.deterministic hs₂] at *
      obtain ⟨hj, hw⟩ := ih hn₁ he₂'
      exact ⟨by omega, hw⟩

/-! ## Spines

Fact 1.1's stuck states: `Top(d₁)…(dₙ)`, `n ≥ 1`. `SpineArgs t ds`
carries the argument list **outermost-first** (`ds = [dₙ, …, d₁]`), so
peeling the outer application conses its argument — the order is shared
with the standardization statements, which match argument lists
positionally. -/

/-- `SpineArgs t ds`: `t = Top(d₁)…(dₙ)` with `n ≥ 1` and
`ds = [dₙ, …, d₁]` (outermost argument first). -/
inductive SpineArgs : Term → List Term → Prop where
  /-- `Top(d)` — the minimal spine. -/
  | head {d : Term} : SpineArgs (.app .top d) [d]
  /-- Apply a spine to one more argument. -/
  | app {t d : Term} {ds : List Term} :
      SpineArgs t ds → SpineArgs (.app t d) (d :: ds)

/-- `t` is a spine `Top(d₁)…(dₙ)`, `n ≥ 1` (Fact 1.1, doc §1). -/
def Spine (t : Term) : Prop := ∃ ds, SpineArgs t ds

/-- Pointwise lifting of a relation to equal-length lists (used for the
componentwise spine clauses of doc Lemma 2.2). -/
inductive Forall2 {α β : Type _} (R : α → β → Prop) : List α → List β → Prop where
  | nil : Forall2 R [] []
  | cons {a : α} {b : β} {l₁ : List α} {l₂ : List β} :
      R a b → Forall2 R l₁ l₂ → Forall2 R (a :: l₁) (b :: l₂)

/-- Spines are not values — "going wrong" (doc §1). -/
theorem Spine.not_value {t : Term} (h : Spine t) : ¬ Value t := by
  obtain ⟨ds, hsp⟩ := h
  intro hv
  cases hsp <;> cases hv

/-- Spines are weak-head normal (the head `Top` is rigid). -/
theorem Spine.whNormal {t : Term} (h : Spine t) : WHNormal t := by
  obtain ⟨ds, hsp⟩ := h
  induction hsp with
  | head =>
    intro t' hs
    cases hs with
    | head u hs => exact (whNormal_of_value .top) _ hs
  | @app t d ds h' ih =>
    intro t' hs
    cases hs with
    | beta => cases h'
    | head u hs => exact ih _ hs

/-- **Fact 1.1** (doc §1), weak-head form: a closed weak-head normal term
is a value (`Top` or a λ) or a spine. -/
theorem fact_1_1 {t : Term} (hc : ClosedUnder 0 t) (hn : WHNormal t) :
    Value t ∨ Spine t := by
  induction t with
  | var x => cases hc; omega
  | top => exact .inl .top
  | lam a b => exact .inl (.lam a b)
  | app f u ihf _ =>
    obtain ⟨hnf, hf_not_lam⟩ := whNormal_app_inv hn
    cases hc with
    | app hcf _ =>
      rcases ihf hcf hnf with hv | ⟨ds, hsp⟩
      · -- Value f, not a λ, so f = .top: spine Top(u)
        cases hv with
        | top => exact .inr ⟨[u], .head⟩
        | lam a b => exact absurd rfl (hf_not_lam a b)
      · -- f is a spine: f(u) is a spine
        exact .inr ⟨u :: ds, .app hsp⟩

/-- Inverting `⟶`-normality at an application: head and argument are
`⟶`-normal, and the head is not a λ (else `Step.eapp` fires). -/
private theorem stepNormal_app_inv {f u : Term} (h : StepNormal (.app f u)) :
    StepNormal f ∧ StepNormal u ∧ ∀ a b, f ≠ .lam a b := by
  refine ⟨?_, ?_, ?_⟩
  · intro f' hs; exact h _ (hs.appL u)
  · intro u' hs; exact h _ (Step.appR f hs)
  · intro a b heq; subst heq; exact h (b.subst1 u) .eapp

/-- **Fact 1.1** (doc §1), full-reduction form: a closed `⟶`-normal
non-value is a spine with `⟶`-normal arguments. -/
theorem fact_1_1_step_normal {t : Term} (hc : ClosedUnder 0 t)
    (hn : StepNormal t) (hv : ¬ Value t) :
    ∃ ds, SpineArgs t ds ∧ ∀ d ∈ ds, StepNormal d := by
  induction t with
  | var x => cases hc; omega
  | top => exact absurd .top hv
  | lam a b => exact absurd (.lam a b) hv
  | app f u ihf _ =>
    obtain ⟨hnf, hnu, hf_not_lam⟩ := stepNormal_app_inv hn
    cases hc with
    | app hcf _ =>
      by_cases hfv : Value f
      · -- f is a value but not a λ, so f = .top: spine Top(u)
        cases hfv with
        | top =>
          refine ⟨[u], .head, ?_⟩
          intro d hd; simp only [List.mem_singleton] at hd; subst hd; exact hnu
        | lam a b => exact absurd rfl (hf_not_lam a b)
      · -- f is a non-value spine: prepend u
        obtain ⟨ds, hsp, hds⟩ := ihf hcf hnf hfv
        refine ⟨u :: ds, .app hsp, ?_⟩
        intro d hd
        rcases List.mem_cons.mp hd with h | h
        · subst h; exact hnu
        · exact hds d h

/-! ## Head factorization of `⇓` through application

Doc §9 watchpoint: "Prove the head-factorization of `⇓` through
application as a standalone lemma first. Off-by-ones here are the
likeliest mechanical bug of the whole development." The arithmetic is
`j = j₁ + 1 + j₂`: `j₁` head steps in the function, one β-step, `j₂`
steps in the contractum.
-/

/-- **Head factorization** (doc §6 W-APP / §9): a converging application
factors through the convergence of its head. Either the head converges
to a λ and the evaluation continues through the β-contractum with
`j = j₁ + 1 + j₂` exactly, or the head converges to a non-λ and the
application is already weak-head normal with `j = j₁`. -/
theorem converges_app_factor {j : Nat} {T U v : Term}
    (h : Converges j (.app T U) v) :
    ∃ j₁ w, j₁ ≤ j ∧ Converges j₁ T w ∧
      ((∃ A B, w = .lam A B ∧
          ∃ j₂, j = j₁ + 1 + j₂ ∧ Converges j₂ (B.subst1 U) v) ∨
       ((∀ A B, w ≠ .lam A B) ∧ v = .app w U ∧ j = j₁)) := by
  obtain ⟨he, hn⟩ := h
  induction j generalizing T with
  | zero =>
    -- app T U is already weak-head normal; T converges to itself, not a λ
    cases he with
    | refl =>
      obtain ⟨hnT, hT_not_lam⟩ := whNormal_app_inv hn
      refine ⟨0, T, Nat.le_refl _, ⟨.refl, hnT⟩, .inr ⟨?_, rfl, rfl⟩⟩
      intro A B heq; exact hT_not_lam A B heq
  | succ j ih =>
    cases he with
    | step hs he' =>
      cases hs with
      | beta =>
        -- T = lam A B fires immediately: j₁ = 0
        rename_i A B
        refine ⟨0, .lam A B, Nat.zero_le _,
          ⟨.refl, whNormal_of_value (.lam A B)⟩, .inl ⟨A, B, rfl, j, by omega, he', hn⟩⟩
      | head u hs' =>
        -- T ↦ T'; recurse on the head, prepend the step
        rename_i T'
        obtain ⟨j₁, w, hle, ⟨heT', hnw⟩, hcase⟩ := ih he'
        refine ⟨j₁ + 1, w, by omega, ⟨.step hs' heT', hnw⟩, ?_⟩
        rcases hcase with ⟨A, B, hwlam, j₂, hjeq, hconv⟩ | ⟨hnotlam, hveq, hjeq⟩
        · exact .inl ⟨A, B, hwlam, j₂, by omega, hconv⟩
        · exact .inr ⟨hnotlam, hveq, by omega⟩

/-- Composition direction of head factorization: rebuild the evaluation
of an application from its head's evaluation to a λ and the contractum's
convergence — with the exact arithmetic `j₁ + 1 + j₂`. -/
theorem converges_app_beta {j₁ j₂ : Nat} {T A B U v : Term}
    (hT : Evals j₁ T (.lam A B)) (hv : Converges j₂ (B.subst1 U) v) :
    Converges (j₁ + 1 + j₂) (.app T U) v := by
  refine ⟨?_, hv.2⟩
  have step1 : Evals j₁ (.app T U) (.app (.lam A B) U) := hT.appL U
  have step2 : Evals (j₁ + 1) (.app T U) (B.subst1 U) := step1.tail .beta
  exact step2.trans hv.1

/-! ## Closedness

The model (doc §3) lives on closed terms; these are the doc-level
closedness facts (§9: "expect a small lemma kit relating `subst`,
closedness, and `γ[x↦c]`" — the kit's `subst1` corollary and the
preservation facts live here, private auxiliaries belong to the
implementer).
-/

/-- Closedness is monotone in the bound. -/
theorem closedUnder_mono {n m : Nat} {t : Term} (hnm : n ≤ m)
    (h : ClosedUnder n t) : ClosedUnder m t := by
  induction h generalizing m with
  | var hx => exact .var (by omega)
  | top => exact .top
  | lam _ _ iht ihu => exact .lam (iht hnm) (ihu (by omega))
  | app _ _ iht ihu => exact .app (iht hnm) (ihu hnm)

/-- A renaming that maps indices `< m` into `< n` preserves closedness:
`ClosedUnder m t → ClosedUnder n (t.rename ρ)`. -/
private theorem closedUnder_rename {m n : Nat} {ρ : Nat → Nat} {t : Term}
    (hρ : ∀ x, x < m → ρ x < n) (h : ClosedUnder m t) :
    ClosedUnder n (t.rename ρ) := by
  induction h generalizing n ρ with
  | var hx => exact .var (hρ _ hx)
  | top => exact .top
  | @lam m a b _ _ iha ihb =>
    refine .lam (iha hρ) (ihb ?_)
    intro x hx
    cases x with
    | zero => simp [Term.liftRen]
    | succ x => exact Nat.succ_lt_succ (hρ x (by omega))
  | app _ _ iha ihb => exact .app (iha hρ) (ihb hρ)

/-- A substitution closed pointwise below `m` (each `σ x` for `x < m` is
closed under `n`) sends `m`-closed terms to `n`-closed terms. -/
private theorem closedUnder_subst {m n : Nat} {σ : Nat → Term} {t : Term}
    (hσ : ∀ x, x < m → ClosedUnder n (σ x)) (h : ClosedUnder m t) :
    ClosedUnder n (t.subst σ) := by
  induction h generalizing n σ with
  | var hx => exact hσ _ hx
  | top => exact .top
  | @lam m a b _ _ iha ihb =>
    refine .lam (iha hσ) (ihb ?_)
    intro x hx
    cases x with
    | zero => exact .var (by omega)
    | succ x =>
      show ClosedUnder (n + 1) ((σ x).rename (· + 1))
      exact closedUnder_rename (fun y _ => by omega) (hσ x (by omega))
  | app _ _ iha ihb => exact .app (iha hσ) (ihb hσ)

/-- `subst1` preserves closedness: `[x ↦ s]u` is closed under `n` when
`u` is closed under `n + 1` and `s` under `n`. -/
theorem closedUnder_subst1 {n : Nat} {u s : Term}
    (hu : ClosedUnder (n + 1) u) (hs : ClosedUnder n s) :
    ClosedUnder n (u.subst1 s) := by
  apply closedUnder_subst _ hu
  intro x hx
  cases x with
  | zero => exact hs
  | succ x => exact .var (by omega)

/-- Full reduction preserves closedness. -/
theorem closedUnder_step {n : Nat} {t t' : Term}
    (hc : ClosedUnder n t) (h : Step t t') : ClosedUnder n t' := by
  rw [Step.step_iff_compat] at h
  induction h generalizing n with
  | @eapp a b s =>
    cases hc with
    | app hlam hs =>
      cases hlam with
      | lam ha hb => exact closedUnder_subst1 hb hs
  | appL u _ ih =>
    cases hc with
    | app ht hu => exact .app (ih ht) hu
  | appR t _ ih =>
    cases hc with
    | app ht hu => exact .app ht (ih hu)
  | lamBound u _ ih =>
    cases hc with
    | lam ht hu => exact .lam (ih ht) hu
  | lamBody t _ ih =>
    cases hc with
    | lam ht hu => exact .lam ht (ih hu)

/-- Weak-head reduction preserves closedness. -/
theorem closedUnder_whStep {n : Nat} {t t' : Term}
    (hc : ClosedUnder n t) (h : WHStep t t') : ClosedUnder n t' :=
  closedUnder_step hc h.toStep

/-- Multi-step reduction preserves closedness. -/
theorem closedUnder_steps {n : Nat} {t t' : Term}
    (hc : ClosedUnder n t) (h : Steps t t') : ClosedUnder n t' := by
  induction h with
  | refl => exact hc
  | head hs _ ih => exact ih (closedUnder_step hc hs)

/-- Exact-step weak-head evaluation preserves closedness. -/
theorem closedUnder_evals {n j : Nat} {t t' : Term}
    (hc : ClosedUnder n t) (h : Evals j t t') : ClosedUnder n t' :=
  closedUnder_steps hc h.toSteps

end Pss.Semantic
