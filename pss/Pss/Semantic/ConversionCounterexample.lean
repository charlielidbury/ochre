import Pss.Semantic.Model
import Pss.Semantic.Standardization

/-!
# Lemma 4.5 (member conversion) is FALSE in this model

A closed-term countermodel to `mem_of_beta_all` (doc §4, Lemma 4.5) and
to its isolated residual `TierTransport` (Conversion.lean). The doc's
proof was already known to have a quantifier gap at tier (t1) (commit
e944b707); this file shows the gap is **unfixable**: the statement
itself fails.

## The countermodel

With `K⊤ := λz≤⊤.⊤` and `I := λx≤⊤.x`:

- the bound `c := λy≤K⊤. y(⊤)(⊤)` is a perfectly good *value* whose
  **body is spine-typed on good arguments**: for good `c₃`, the type
  `c₃(⊤)(⊤)` weak-head evaluates toward the stuck spine `⊤(⊤)`, so by
  (m2) *any* convergence of a member of `⟦c₃(⊤)(⊤)⟧` is fatal — good
  arguments of `c` are capped at depth 2 (`Good 2 c c` holds, nothing
  above);
- the junk probe `⊤` short-circuits applications in **zero** steps
  (`⊤(d)` is already weak-head normal), while good arguments resolve
  in ≥ 1 step — so the member body `q := y(⊤)` reaches the stuck spine
  `⊤(⊤)(⊤)` after just **one** step at the capped argument `c` itself:
  `q[c] = c(⊤) ⇓¹ ⊤(⊤)(⊤)`, killing `Mem 2 (q[c]) ⊤` at (m1);
- the padded conversion partner `β′ := I(I(q))` satisfies **every**
  tier of `∀m, Match m (λy≤c.β′) (λy≤c.⊤)`: its only sub-cap firings
  would need a good `c′` whose body resolves with the junk probe `⊤`
  to a non-value strictly faster than with `K⊤` — impossible by the
  **lockstep lemma** (`step_reflect`/`shape_resolve`): ⊤-instantiation
  reflects weak-head steps (⊤ creates no redexes), and a ⊤-instance
  weak-head normal form that is not a value resolves under `K⊤` within
  one extra step, after which (m2) against the spine-type contradicts
  the goodness of `c′`.

Embedding the failing tier at `s := λy≤c.q`, `s′ := λy≤c.β′`,
`T := λy≤c.⊤`, `k := 4` — **all terms closed** — refutes Lemma 4.5
outright (`mem_of_beta_all_refuted`), for the doc's closed-term model
as well as the mechanized all-terms one.

Consequences: the `TierTransport` residual is false (`tierTransport_false`),
so `mem_of_beta_all`'s sorry can never be closed and the statement must
be retired by the orchestrator; the model (Definition 3.1) genuinely
distinguishes `=β`-equal members, so any DS-APP/FT closure must come
from derivability of the hypotheses or a model change, not from a
model-level conversion invariant. (Lemma 4.4 — type-side conversion —
is unaffected: it is proven and true; here the *member* changes.)
-/

namespace Pss.Semantic

open Term (Value)

namespace Cx45

/-- `I := λx≤⊤.x`, the one-step padding combinator. -/
def iTop : Term := .lam .top (.var 0)

/-- `K⊤ := λz≤⊤.⊤` — the constant-`⊤` value, used both as the inner
bound and as the "good prober" of the lockstep lemma. -/
def kTop : Term := .lam .top .top

/-- `c`'s body `y(⊤)(⊤)` (free `y` = de Bruijn 0). -/
def cBody : Term := .app (.app (.var 0) .top) .top

/-- The capped bound `c := λy≤K⊤. y(⊤)(⊤)`. -/
def cEx : Term := .lam kTop cBody

/-- The member body `q := y(⊤)`. -/
def qEx : Term := .app (.var 0) .top

/-- The padded conversion partner `β′ := I(I(q))`. -/
def betaEx : Term := .app iTop (.app iTop qEx)

/-- The stuck witness `⊤(⊤)(⊤) = q[c]`'s weak-head normal form. -/
def spine3 : Term := .app (.app .top .top) .top

/-! ## Weak-head basics for the concrete terms -/

/-- Variables are weak-head normal. -/
theorem whnf_var (i : Nat) : WHNormal (.var i) := fun _ h => nomatch h

/-- `⊤`-headed applications are weak-head normal (spines). -/
theorem whnf_top_app (X : Term) : WHNormal (.app .top X) := by
  intro t' h
  cases h with
  | head _ hs => exact nomatch hs

/-- An application with a weak-head-normal non-λ head is weak-head
normal (converse of `whNormal_app_inv`). -/
theorem whNormal_app_intro' {f : Term} (hf : WHNormal f)
    (hnl : ∀ a b, f ≠ Term.lam a b) : ∀ u, WHNormal (.app f u) := by
  intro u t' hs
  cases hs with
  | beta => exact hnl _ _ rfl
  | head _ hs' => exact hf _ hs'

/-- `⊤(⊤)(⊤)` is weak-head normal. -/
theorem whnf_spine3 : WHNormal spine3 := by
  intro t' h
  cases h with
  | head _ hs => exact whnf_top_app .top _ hs

/-- A weak-head normal term's convergences are trivial. -/
theorem converges_whnf_fix {j : Nat} {t v : Term} (hn : WHNormal t)
    (h : Converges j t v) : j = 0 ∧ v = t := by
  obtain ⟨hj, hv⟩ := Converges.deterministic h ⟨Evals.refl, hn⟩
  exact ⟨hj, hv⟩

/-- Pinning a type-side weak-head value: a whnf converges only to
itself. -/
theorem convergesTo_whnf_eq {t w : Term} (hn : WHNormal t)
    (h : ConvergesTo t w) : w = t := by
  obtain ⟨j, hj⟩ := h
  exact (converges_whnf_fix hn hj).2

/-- `Mem 0` is universal. -/
theorem mem_zero (s T : Term) : Mem 0 s T :=
  Mem_unfold.mpr (fun j _ hj _ => absurd hj (Nat.not_lt_zero j))

/-- `MATCH` against `⊤` holds unconditionally. -/
theorem match_vs_top {m : Nat} {v : Term} : Match m v .top :=
  Match_unfold.mpr (.inl rfl)

/-- Membership in `⟦⊤⟧ₖ` is exactly (m1): all sub-`k` convergences are
values. -/
theorem mem_top_intro {k : Nat} {x : Term}
    (h : ∀ j v, j < k → Converges j x v → Value v) : Mem k x .top := by
  rw [Mem_unfold]
  intro j v hj hconv
  exact ⟨h j v hj hconv, .top, ⟨0, Evals.refl, whNormal_of_value .top⟩,
    .top, match_vs_top⟩

/-- Everything below any type is below `⊤` (its own (m1) supplies the
value). -/
theorem mem_top_of_mem {k : Nat} {x X : Term} (h : Mem k x X) :
    Mem k x .top := by
  rw [Mem_unfold] at h
  refine mem_top_intro (fun j v hj hconv => ?_)
  exact (h j v hj hconv).1

/-- The padding step: `I(X) ↦ X`. -/
theorem iTop_step (X : Term) : WHStep (.app iTop X) X := WHStep.beta

/-! ## `K⊤` is a good argument of itself at every depth -/

/-- `⊤ ∈ ⟦⊤⟧ₖ` at every `k`. -/
theorem mem_top_top (k : Nat) : Mem k .top .top :=
  mem_top_intro fun j v _ hconv => by
    obtain ⟨-, rfl⟩ := converges_whnf_fix (whNormal_of_value .top) hconv
    exact .top

/-- `MATCHₘ(K⊤, K⊤)` at every `m`: the body tiers are `⊤ ∈ ⟦⊤⟧`. -/
theorem match_kTop_kTop (m : Nat) : Match m kTop kTop := by
  rw [Match_unfold]
  refine .inr ⟨.top, .top, .top, .top, rfl, rfl, Beta.refl .top, ?_⟩
  intro j' c₄ _ _
  exact ⟨mem_top_top j', fun _ h => h⟩

/-- `K⊤ ∈ ⟦K⊤⟧ₖ` at every `k`. -/
theorem mem_kTop_kTop (k : Nat) : Mem k kTop kTop := by
  rw [Mem_unfold]
  intro j v hj hconv
  obtain ⟨rfl, rfl⟩ :=
    converges_whnf_fix (whNormal_of_value (.lam .top .top)) hconv
  exact ⟨.lam _ _, kTop, ⟨0, Evals.refl, whNormal_of_value (.lam _ _)⟩,
    .lam _ _, match_kTop_kTop _⟩

/-- `K⊤ ∈ ⟨K⊤⟩ⱼ` at **every** depth — the good prober exists at every
index. -/
theorem good_kTop_kTop (j : Nat) : Good j kTop kTop := by
  rw [Good_unfold]
  exact ⟨mem_kTop_kTop j, mem_kTop_kTop j, fun i s' _ h => h⟩

/-! ## `Good 2 c c`: the capped bound is good at depth 2 -/

/-- The depth-1 tier of `c`'s self-MATCH is vacuous: for `c₃` good at 1,
`c₃(⊤)(⊤)` is never weak-head normal (good whnf arguments of `K⊤` are
λs, which redex; non-whnf arguments keep stepping). -/
theorem mem_one_cBody (c₃ : Term) (hgood : Good 1 kTop c₃) :
    Mem 1 (cBody.subst1 c₃) (cBody.subst1 c₃) := by
  rw [Mem_unfold]
  intro j v hj hconv
  have hj0 : j = 0 := by omega
  subst hj0
  obtain ⟨he, hn⟩ := hconv
  cases he
  -- hn : WHNormal (c₃(⊤)(⊤)); derive a contradiction from goodness
  exfalso
  obtain ⟨hn₁, -⟩ := whNormal_app_inv hn
  obtain ⟨hnc₃, hc₃_not_lam⟩ := whNormal_app_inv hn₁
  -- fire `Mem 1 c₃ K⊤` at (0, c₃)
  rw [Good_unfold] at hgood
  obtain ⟨hval, w, hTw, -, hmatch⟩ :=
    Mem_unfold.mp hgood.1 0 c₃ Nat.one_pos ⟨Evals.refl, hnc₃⟩
  -- c₃ is a value that is not a λ: c₃ = ⊤
  cases hval with
  | top =>
    -- Match 1 ⊤ K⊤ is impossible: the member side must be a λ
    obtain rfl : w = kTop :=
      convergesTo_whnf_eq (whNormal_of_value (.lam .top .top)) hTw
    rcases Match_unfold.mp hmatch with htop | ⟨a₀, b₀, α₀, β₀, hw, hv', -, -⟩
    · exact nomatch htop
    · exact nomatch hv'
  | lam a b => exact hc₃_not_lam a b rfl

/-- `MATCH₂(c, c)`: tier 0 is trivial, tier 1 is `mem_one_cBody`. -/
theorem match_two_cEx : Match 2 cEx cEx := by
  rw [Match_unfold]
  refine .inr ⟨kTop, cBody, kTop, cBody, rfl, rfl, Beta.refl kTop, ?_⟩
  intro j' c₃ hj' hgood
  match j', hj' with
  | 0, _ => exact ⟨mem_zero _ _, fun _ h => h⟩
  | 1, _ => exact ⟨mem_one_cBody c₃ hgood, fun _ h => h⟩

/-- `c ∈ ⟦c⟧₂`. -/
theorem mem_two_cEx : Mem 2 cEx cEx := by
  rw [Mem_unfold]
  intro j v hj hconv
  obtain ⟨rfl, rfl⟩ :=
    converges_whnf_fix (whNormal_of_value (.lam kTop cBody)) hconv
  exact ⟨.lam _ _, cEx, ⟨0, Evals.refl, whNormal_of_value (.lam kTop cBody)⟩,
    .lam _ _, match_two_cEx⟩

/-- **`Good 2 c c`**: the goal tier of the countermodel is genuinely
inhabited. -/
theorem good_two_cEx : Good 2 cEx cEx := by
  rw [Good_unfold]
  exact ⟨mem_two_cEx, mem_two_cEx, fun i s' _ h => h⟩

/-! ## The lockstep simulation

The quantitative "cap anatomy" — landing on the **falsity** side: a
body's evaluation under the junk probe `⊤` is *reflected* by the body
itself (⊤ creates no redexes), so the `K⊤`-instance runs in lockstep
and resolves within **one** extra step once the ⊤-instance reaches a
non-value weak-head normal form. Hypothesis tiers (which only see good
arguments, all of whose convergences are banned by (m2) against the
spine-type) therefore contradict any non-value firing of the padded
member — while the *goal*'s junk path stays one step ahead of the cap. -/

/-- ⊤-instantiation **reflects** weak-head steps: a head step of
`M[x↦⊤]` is the instance of a head step of `M` (substituted `⊤`s create
no redexes). -/
theorem step_reflect : ∀ (M : Term) {X' : Term},
    WHStep (M.subst1 .top) X' →
    ∃ M', WHStep M M' ∧ X' = M'.subst1 .top := by
  intro M
  induction M with
  | var i =>
    intro X' h
    cases i with
    | zero => exact nomatch h
    | succ i => exact nomatch h
  | top => exact fun h => nomatch h
  | lam A B => exact fun h => nomatch h
  | app M₁ M₂ ih₁ _ =>
    intro X' h
    cases M₁ with
    | var i =>
      cases i with
      | zero =>
        -- (⊤)(M₂[⊤]): weak-head normal, no step
        cases h with
        | head _ hs => exact nomatch hs
      | succ i =>
        cases h with
        | head _ hs => exact nomatch hs
    | top =>
      cases h with
      | head _ hs => exact nomatch hs
    | lam A₀ B₀ =>
      cases h with
      | beta =>
        exact ⟨B₀.subst1 M₂, WHStep.beta, (Term.subst_subst1 _ B₀ M₂).symm⟩
      | head _ hs => exact absurd hs (whNormal_of_value (.lam _ _) _)
    | app N₁ N₂ =>
      cases h with
      | head _ hs =>
        obtain ⟨M₁', hstep, rfl⟩ := ih₁ hs
        exact ⟨.app M₁' M₂, .head _ hstep, rfl⟩

/-- Lockstep along evaluations: the ⊤-instance's whole evaluation is an
instance of an evaluation of `M` itself, which the `K⊤`-instance
mirrors step for step. -/
theorem evals_reflect {f : Nat} {X N : Term} (h : Evals f X N) :
    ∀ M : Term, X = M.subst1 .top →
    ∃ M_f : Term, N = M_f.subst1 .top ∧
      Evals f (M.subst1 kTop) (M_f.subst1 kTop) := by
  induction h with
  | refl => exact fun M hM => ⟨M, hM, .refl⟩
  | step hs _ ih =>
    intro M hM
    subst hM
    obtain ⟨M', hstep, rfl⟩ := step_reflect M hs
    obtain ⟨M_f, hN, hev⟩ := ih M' rfl
    exact ⟨M_f, hN,
      .step (Standardization.whStep_subst (Term.scons kTop Term.var) hstep) hev⟩

/-- Shape resolution: if `M[x↦⊤]` is weak-head normal but **not a
value**, then `M[x↦K⊤]` converges within one step, to a non-λ. (The
only divergence between the instances is a head occurrence of the
variable: `⊤` freezes the spine, `K⊤` resolves it to `⊤` in one step.) -/
theorem shape_resolve : ∀ M : Term, WHNormal (M.subst1 .top) →
    ¬ Value (M.subst1 .top) →
    ∃ g w, g ≤ 1 ∧ Converges g (M.subst1 kTop) w ∧
      (∀ A B, w ≠ Term.lam A B) := by
  intro M
  induction M with
  | var i =>
    intro _ hv
    cases i with
    | zero => exact absurd .top hv
    | succ i =>
      exact ⟨0, .var i, by omega, ⟨Evals.refl, whnf_var i⟩,
        fun A B h => nomatch h⟩
  | top => exact fun _ hv => absurd .top hv
  | lam A B => exact fun _ hv => absurd (.lam _ _) hv
  | app M₁ M₂ ih₁ _ =>
    intro hn _
    obtain ⟨hn₁, hnl₁⟩ := whNormal_app_inv hn
    cases M₁ with
    | var i =>
      cases i with
      | zero =>
        -- M[K⊤] = K⊤(M₂[K⊤]) ↦ ⊤
        refine ⟨1, .top, by omega,
          ⟨.step WHStep.beta Evals.refl, whNormal_of_value .top⟩,
          fun A B h => nomatch h⟩
      | succ i =>
        exact ⟨0, .app (.var i) (M₂.subst1 kTop), by omega,
          ⟨Evals.refl, whNormal_app_intro' (whnf_var i)
            (fun _ _ h => nomatch h) _⟩,
          fun A B h => nomatch h⟩
    | top =>
      exact ⟨0, .app .top (M₂.subst1 kTop), by omega,
        ⟨Evals.refl, whnf_top_app _⟩, fun A B h => nomatch h⟩
    | lam A₀ B₀ => exact absurd rfl (hnl₁ _ _)
    | app N₁ N₂ =>
      have hv₁ : ¬ Value ((Term.app N₁ N₂).subst1 .top) := fun h => nomatch h
      obtain ⟨g, w₁, hg, hconv₁, hnl⟩ := ih₁ hn₁ hv₁
      refine ⟨g, .app w₁ (M₂.subst1 kTop), hg,
        ⟨Evals.appL _ hconv₁.1, whNormal_app_intro' hconv₁.2 hnl _⟩,
        fun A B h => nomatch h⟩

/-- **The lockstep lemma**: a ⊤-instance converging to a non-value
forces the `K⊤`-instance to converge, within one extra step. -/
theorem lockstep {f : Nat} {M v : Term}
    (hconv : Converges f (M.subst1 .top) v) (hv : ¬ Value v) :
    ∃ g w, g ≤ f + 1 ∧ Converges g (M.subst1 kTop) w := by
  obtain ⟨M_f, rfl, hev⟩ := evals_reflect hconv.1 M rfl
  obtain ⟨g', w, hg', hconv', -⟩ := shape_resolve M_f hconv.2 hv
  exact ⟨f + g', w, by omega, ⟨hev.trans hconv'.1, hconv'.2⟩⟩

/-! ## The spine-type kills convergent members -/

/-- `c`'s body at the good prober — the type `K⊤(⊤)(⊤) ⇓¹ ⊤(⊤)`, a
spine — admits **no** convergent member: (m2) demands a type-side value
that does not exist. -/
theorem mem_cBody_kTop_no_conv {j : Nat} {x : Term}
    (h : Mem j x (cBody.subst1 kTop)) {g : Nat} {v : Term}
    (hg : g < j) (hc : Converges g x v) : False := by
  obtain ⟨-, w, hTw, hwval, -⟩ := Mem_unfold.mp h g v hg hc
  have hconv1 : Converges 1 (cBody.subst1 kTop) (.app .top .top) :=
    ⟨.step (.head _ WHStep.beta) .refl, whnf_top_app .top⟩
  obtain ⟨jw, hjw⟩ := hTw
  obtain ⟨-, rfl⟩ := Converges.deterministic hjw hconv1
  exact nomatch hwval

/-! ## The dagger: every tier of the ∀-MATCH holds for `β′` -/

/-- **(†)**: for every good argument `c′` of `c` at every depth `j′`,
`β′[c′] ∈ ⟦⊤⟧_{j′}` — i.e. all sub-`j′` convergences of the padded
member body are values. A non-value firing would need the junk path
(`⊤`) to outrun the good path (`K⊤`) by more than the lockstep slack,
contradicting `c′`'s goodness via (m2) against the spine-type. -/
theorem dagger (j' : Nat) (c' : Term) (hgood : Good j' cEx c') :
    Mem j' (betaEx.subst1 c') .top := by
  refine mem_top_intro (fun j'' v hlt hconv => ?_)
  rcases j'' with - | - | j₃
  · -- the outer pad is a redex: no 0-step convergence
    obtain ⟨hev, hn⟩ := hconv
    cases hev
    exact absurd (iTop_step _) (hn _)
  · -- the inner pad is a redex: no 1-step convergence
    obtain ⟨hev, hn⟩ := Converges.whStep_inv (iTop_step _) hconv
    cases hev
    exact absurd (iTop_step _) (hn _)
  · -- peel both pads, then factor through `c′`'s own convergence
    have h2 : Converges j₃ (.app c' .top) v :=
      Converges.whStep_inv (iTop_step _) (Converges.whStep_inv (iTop_step _) hconv)
    obtain ⟨j₁', w_c, hle, hconv_c, hcase⟩ := converges_app_factor h2
    rw [Good_unfold] at hgood
    rcases hcase with ⟨A, B, rfl, j₂'', hjeq, hconvB⟩ | ⟨hnotlam, rfl, hjeq⟩
    · -- c′ ⇓ λA.B and v = whnf of B[⊤]: suppose v were a non-value
      refine Classical.byContradiction fun hv => ?_
      obtain ⟨g, w₂, hg, hconv₂⟩ := lockstep hconvB hv
      have hj₁' : j₁' < j' := by omega
      obtain ⟨-, wc₂, hTw, -, hmatch⟩ :=
        Mem_unfold.mp hgood.1 j₁' _ hj₁' hconv_c
      obtain rfl : wc₂ = cEx :=
        convergesTo_whnf_eq (whNormal_of_value (.lam kTop cBody)) hTw
      rcases Match_unfold.mp hmatch with
        htop | ⟨a₀, b₀, α₀, β₀, hw, hv', -, htier⟩
      · exact nomatch htop
      · injection hw with hw1 hw2
        injection hv' with hv1 hv2
        subst hw1; subst hw2; subst hv1; subst hv2
        have htk : j' - j₁' - 1 < j' - j₁' := by omega
        obtain ⟨ht1, -⟩ := htier (j' - j₁' - 1) kTop htk (good_kTop_kTop _)
        exact mem_cBody_kTop_no_conv ht1 (by omega) hconv₂
    · -- c′ converges to a non-λ: contradicts the MATCH shape clause
      exfalso
      have hj₁' : j₁' < j' := by omega
      obtain ⟨-, wc₂, hTw, -, hmatch⟩ :=
        Mem_unfold.mp hgood.1 j₁' _ hj₁' hconv_c
      obtain rfl : wc₂ = cEx :=
        convergesTo_whnf_eq (whNormal_of_value (.lam kTop cBody)) hTw
      rcases Match_unfold.mp hmatch with
        htop | ⟨a₀, b₀, α₀, β₀, hw, hv', -, -⟩
      · exact nomatch htop
      · exact absurd hv' (hnotlam _ _)

/-! ## The refutations -/

/-- The full ∀-index MATCH of the conversion pair against `λy≤c.⊤`. -/
theorem match_all (m : Nat) : Match m (.lam cEx betaEx) (.lam cEx .top) := by
  rw [Match_unfold]
  refine .inr ⟨cEx, .top, cEx, betaEx, rfl, rfl, Beta.refl cEx, ?_⟩
  intro j' c' _ hgood
  exact ⟨dagger j' c' hgood, fun x hx => mem_top_of_mem hx⟩

/-- `s′ := λy≤c.β′` inhabits `⟦λy≤c.⊤⟧` at **every** index. -/
theorem mem_all_sPrime (k : Nat) : Mem k (.lam cEx betaEx) (.lam cEx .top) := by
  rw [Mem_unfold]
  intro j v hj hconv
  obtain ⟨rfl, rfl⟩ :=
    converges_whnf_fix (whNormal_of_value (.lam cEx betaEx)) hconv
  exact ⟨.lam _ _, .lam cEx .top,
    ⟨0, Evals.refl, whNormal_of_value (.lam cEx .top)⟩, .lam _ _, match_all _⟩

/-- `q =β β′` (two padding steps). -/
theorem beta_q_betaEx : Beta qEx betaEx := by
  have h1 : Step betaEx (.app iTop qEx) := Step.eapp
  have h2 : Step (.app iTop qEx) qEx := Step.eapp
  exact (Beta.of_steps (Star.head h1 (Star.head h2 Star.refl))).symm

/-- The failing tier: `q[c] = c(⊤) ⇓¹ ⊤(⊤)(⊤)`, a stuck spine, so
`q[c] ∉ ⟦⊤⟧₂` — (m1) fails strictly inside the budget. -/
theorem qEx_cEx_fails : ¬ Mem 2 (qEx.subst1 cEx) .top := by
  intro h
  have hconv : Converges 1 (qEx.subst1 cEx) spine3 :=
    ⟨.step WHStep.beta .refl, whnf_spine3⟩
  obtain ⟨hval, -⟩ := Mem_unfold.mp h 1 spine3 (by omega) hconv
  exact nomatch hval

/-- **`TierTransport` is FALSE** — the residual of `mem_of_beta_all`
(Conversion.lean), restated verbatim, is refuted at
`j₁ := 2, α' := c, β' := I(I(y(⊤))), a := c, b := ⊤, q := y(⊤), c := c`. -/
theorem tierTransport_false :
    ¬ (∀ (j₁ : Nat) (α' β' a b q c : Term), Beta q β' →
        (∀ n, Match (n + 1) (.lam α' β') (.lam a b)) →
        Good j₁ a c → Mem j₁ (q.subst1 c) (b.subst1 c)) := by
  intro H
  exact qEx_cEx_fails
    (H 2 cEx betaEx cEx .top qEx cEx beta_q_betaEx
      (fun n => match_all (n + 1)) good_two_cEx)

/-- **Lemma 4.5 (doc §4) is FALSE**: member conversion fails in this
model, on closed terms — `s := λy≤c.y(⊤)`, `s′ := λy≤c.I(I(y(⊤)))`,
`T := λy≤c.⊤`, `k := 4`. The sorried `mem_of_beta_all` in
`Conversion.lean` is unprovable and must be retired. -/
theorem mem_of_beta_all_refuted :
    ¬ (∀ (k : Nat) (s s' T : Term), Beta s s' → (∀ k', Mem k' s' T) →
        Mem k s T) := by
  intro H
  have h4 : Mem 4 (.lam cEx qEx) (.lam cEx .top) :=
    H 4 (.lam cEx qEx) (.lam cEx betaEx) (.lam cEx .top)
      (Beta.lam (Beta.refl cEx) beta_q_betaEx) (fun k' => mem_all_sPrime k')
  obtain ⟨-, w, hTw, -, hmatch⟩ := Mem_unfold.mp h4 0 (.lam cEx qEx)
    (by omega) ⟨Evals.refl, whNormal_of_value (.lam cEx qEx)⟩
  obtain rfl : w = .lam cEx .top :=
    convergesTo_whnf_eq (whNormal_of_value (.lam cEx .top)) hTw
  rcases Match_unfold.mp hmatch with
    htop | ⟨a₀, b₀, α₀, β₀, hw, hv', -, htier⟩
  · exact nomatch htop
  · injection hw with hw1 hw2
    injection hv' with hv1 hv2
    subst hw1; subst hw2; subst hv1; subst hv2
    exact qEx_cEx_fails (htier 2 cEx (by omega) good_two_cEx).1

end Cx45

end Pss.Semantic
