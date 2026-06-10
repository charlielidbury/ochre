import Pss.Semantic.Model
import Pss.Semantic.ModelLemmas
import Pss.Semantic.Standardization

/-!
# Conversion invariance of the model

§4 of `pss/docs/03-revised-proof.md`, Lemmas 4.4 and 4.5. The asymmetry
between them is principled (doc §4): the type side is unbudgeted, so
type conversion holds at each fixed index (4.4); the member side counts
steps, and conversion changes step counts, so member conversion needs
the hypothesis at **every** index (4.5). Every use of 4.5 in the
fundamental theorem has ∀-index facts available, because semantic
judgements are ∀-quantified.

Proof route (doc §4): strong induction on the index; Corollary 2.3
(`beta_lam_converges`/`beta_top_converges`) supplies the converging
value of the converted side; `Beta.subst1` transports tier bodies;
(t2) components ride the IH's set *equalities*— the §9 watchpoint warns
they must not be forgotten in the case analysis.
-/

namespace Pss.Semantic

/-! ### Private machinery for Lemma 4.4

The master lemma `conv_master` proves both directions-at-once forms of
4.4 (`Mem`-conversion, then `Good`-conversion, in that order inside the
step — goodness at `k` consumes membership conversion at indices `≤ k`,
including `k` itself) by strong induction on the index. `Beta` is
symmetric, so one-directional implications suffice; the public ↔s
follow by `Beta.symm`. -/

/-- `MATCH` against a `Top` type side holds unconditionally. -/
private theorem match_top {m : Nat} {v : Term} : Match m v .top := by
  rw [Match_unfold]
  exact .inl rfl

/-- Transport `Match m v ·` across a componentwise `=β` change of the
type-side λ (doc Lemma 4.4's MATCH-transport): the bound clause composes
conversions; tier domains transport by `Good`-conversion below `m`;
(t1) transports by `Mem`-conversion below `m` along `Beta.subst1`; (t2)
rides the same set equality (the §9 watchpoint 2 component). -/
private theorem match_lam_transport {m : Nat} {v a b a' b' : Term}
    (ha : Beta a a') (hb : Beta b b')
    (ihmem : ∀ j', j' < m → ∀ s T T', Beta T T' → Mem j' s T → Mem j' s T')
    (ihgood : ∀ j', j' < m → ∀ x x' c, Beta x x' → Good j' x c → Good j' x' c)
    (h : Match m v (.lam a b)) : Match m v (.lam a' b') := by
  rw [Match_unfold] at h ⊢
  rcases h with htop | ⟨a₀, b₀, α, β, hw, hv, hα, htier⟩
  · cases htop
  · injection hw with h1 h2
    subst h1; subst h2
    refine .inr ⟨a', b', α, β, rfl, hv, hα.trans ha, ?_⟩
    intro j' c hj' hc'
    have hc : Good j' a c := ihgood j' hj' a' a c (Beta.symm ha) hc'
    obtain ⟨ht1, ht2⟩ := htier j' c hj' hc
    have hbc : Beta (b.subst1 c) (b'.subst1 c) := Beta.subst1 hb (Beta.refl c)
    exact ⟨ihmem j' hj' _ _ _ hbc ht1,
      fun s' hs' => ihmem j' hj' _ _ _ hbc (ht2 s' hs')⟩

/-- The master strong induction for Lemma 4.4: at every index, type
conversion preserves membership, and bound conversion preserves
goodness. Membership at `k` uses both claims strictly below `k` (tiers
of `MATCH_{k−j}` sit at `j' < k − j ≤ k`); goodness at `k` uses
membership at indices `≤ k` — including `k` itself, which is why
membership is established first inside the step. -/
private theorem conv_master (k : Nat) :
    (∀ s T T', Beta T T' → Mem k s T → Mem k s T') ∧
    (∀ a a' c, Beta a a' → Good k a c → Good k a' c) := by
  have IH : ∀ m, m < k →
      (∀ s T T', Beta T T' → Mem m s T → Mem m s T') ∧
      (∀ a a' c, Beta a a' → Good m a c → Good m a' c) :=
    fun m hm => conv_master m
  have memk : ∀ s T T', Beta T T' → Mem k s T → Mem k s T' := by
    intro s T T' hT h
    rw [Mem_unfold] at h ⊢
    intro j v hj hconv
    obtain ⟨hv, w, hTw, hwval, hmatch⟩ := h j v hj hconv
    refine ⟨hv, ?_⟩
    obtain ⟨jT, hTconv⟩ := hTw
    have hT'w : Beta T' w :=
      (Beta.symm hT).trans (Beta.of_steps hTconv.1.toSteps)
    cases hwval with
    | top =>
      obtain ⟨j', hconv'⟩ := beta_top_converges hT'w
      exact ⟨.top, ⟨j', hconv'⟩, .top, match_top⟩
    | lam a b =>
      obtain ⟨j', a', b', hconv', ha', hb'⟩ := beta_lam_converges hT'w
      refine ⟨.lam a' b', ⟨j', hconv'⟩, .lam a' b', ?_⟩
      exact match_lam_transport (Beta.symm ha') (Beta.symm hb')
        (fun j₁ hj₁ => (IH j₁ (Nat.lt_of_lt_of_le hj₁ (Nat.sub_le k j))).1)
        (fun j₁ hj₁ => (IH j₁ (Nat.lt_of_lt_of_le hj₁ (Nat.sub_le k j))).2)
        hmatch
  refine ⟨memk, ?_⟩
  intro a a' c ha h
  rw [Good_unfold] at h ⊢
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨memk c a a' ha h1, h2, ?_⟩
  intro i s' hi hmem
  have hma : Mem i s' a := h3 i s' hi hmem
  rcases Nat.lt_or_ge i k with hlt | hge
  · exact (IH i hlt).1 s' a a' ha hma
  · have hik : i = k := Nat.le_antisymm hi hge
    subst hik
    exact memk s' a a' ha hma
termination_by k
decreasing_by exact hm

/-- **Lemma 4.4 (type conversion invariance)**: `T =β T′` gives the set
*equality* `⟦T⟧ₖ = ⟦T′⟧ₖ`, at every fixed index. -/
theorem mem_beta_type {k : Nat} {s T T' : Term}
    (hT : Beta T T') : Mem k s T ↔ Mem k s T' := by
  exact ⟨(conv_master k).1 s T T' hT, (conv_master k).1 s T' T (Beta.symm hT)⟩

/-- **Lemma 4.4**, goodness: `a =β a′` gives `⟨a⟩ⱼ = ⟨a′⟩ⱼ` (memberships
directly, inclusions because `⟦a⟧ᵢ = ⟦a′⟧ᵢ` as sets). -/
theorem good_beta_bound {j : Nat} {a a' c : Term}
    (ha : Beta a a') : Good j a c ↔ Good j a' c := by
  exact ⟨(conv_master j).2 a a' c ha, (conv_master j).2 a' a c (Beta.symm ha)⟩

/-! ### Private machinery for Lemma 4.5

Standardization glue beyond Corollary 2.3: the converted member `s'` is
`=β` a weak-head normal form `v` that is *not yet known to be a value*
(its value-ness comes from the ∀-index hypothesis only after `s'` is
known to converge), so convergence of `s'` must be transferred along
`=β` to an arbitrary-shape whnf target — `St`-inversion at a whnf, plus
preservation of weak-head normality under full reduction. -/

/-- An application with a weak-head-normal non-λ head is weak-head
normal (converse of `whNormal_app_inv`). -/
private theorem whNormal_app_intro {f : Term} (u : Term) (hf : WHNormal f)
    (hnl : ∀ a b, f ≠ .lam a b) : WHNormal (.app f u) := by
  intro t' hs
  cases hs with
  | beta => exact hnl _ _ rfl
  | head _ hs' => exact hf _ hs'

/-- A full-reduction step preserves weak-head normality, and preserves
whether the term is a λ (a whnf's rigid head cannot change). -/
private theorem whNormal_step {v e : Term} (h : Step v e) :
    WHNormal v →
    WHNormal e ∧ ((∃ a b, v = Term.lam a b) ↔ (∃ a b, e = Term.lam a b)) := by
  rw [Step.step_iff_compat] at h
  induction h with
  | @eapp a b s =>
    intro hn
    exact absurd WHStep.beta (hn _)
  | appL u _ ih =>
    intro hn
    obtain ⟨hnt, hnl⟩ := whNormal_app_inv hn
    obtain ⟨hnt', hiff⟩ := ih hnt
    refine ⟨whNormal_app_intro u hnt' ?_, ?_⟩
    · intro a b heq
      obtain ⟨a', b', heq'⟩ := hiff.mpr ⟨a, b, heq⟩
      exact hnl a' b' heq'
    · exact ⟨fun ⟨a, b, h⟩ => (nomatch h), fun ⟨a, b, h⟩ => (nomatch h)⟩
  | appR t _ ih =>
    intro hn
    obtain ⟨hnt, hnl⟩ := whNormal_app_inv hn
    exact ⟨whNormal_app_intro _ hnt hnl,
      fun ⟨a, b, h⟩ => (nomatch h), fun ⟨a, b, h⟩ => (nomatch h)⟩
  | lamBound u _ _ =>
    intro _
    exact ⟨whNormal_of_value (.lam _ _),
      fun _ => ⟨_, _, rfl⟩, fun _ => ⟨_, _, rfl⟩⟩
  | lamBody t _ _ =>
    intro _
    exact ⟨whNormal_of_value (.lam _ _),
      fun _ => ⟨_, _, rfl⟩, fun _ => ⟨_, _, rfl⟩⟩

/-- Full reduction preserves weak-head normality (rigid heads stay
rigid: a whnf's reducts are whnf). -/
private theorem whNormal_steps {v e : Term} (h : Steps v e) :
    WHNormal v → WHNormal e := by
  induction h with
  | refl => exact id
  | head hab _ ih => exact fun hn => ih (whNormal_step hab hn).1

/-- `St`-inversion at a weak-head-normal target of *any* shape (the
var-headed generalization of Lemma 2.2's value cases): the source
converges, to a whnf that is a λ only if the target is. -/
private theorem st_whnf_converges {t e : Term} (hst : Standardization.St t e) :
    WHNormal e →
    ∃ i u, Converges i t u ∧
      ((∃ a b, u = Term.lam a b) → (∃ a b, e = Term.lam a b)) := by
  induction hst with
  | @var t x hap =>
    intro _
    obtain ⟨i, hi⟩ := Standardization.starWH_evals hap
    exact ⟨i, .var x, ⟨hi, fun t' hs => nomatch hs⟩, fun ⟨a, b, h⟩ => nomatch h⟩
  | top hap =>
    intro _
    obtain ⟨i, hi⟩ := Standardization.starWH_evals hap
    exact ⟨i, .top, ⟨hi, whNormal_of_value .top⟩, fun ⟨a, b, h⟩ => nomatch h⟩
  | @lam t a b a' b' hap _ _ _ _ =>
    intro _
    obtain ⟨i, hi⟩ := Standardization.starWH_evals hap
    exact ⟨i, .lam a b, ⟨hi, whNormal_of_value (.lam a b)⟩,
      fun _ => ⟨a', b', rfl⟩⟩
  | @app t t₁ t₂ u₁ u₂ hap _ _ ih₁ _ =>
    intro hn
    obtain ⟨hnu₁, hnl⟩ := whNormal_app_inv hn
    obtain ⟨i₁, w₁, ⟨hev₁, hnw₁⟩, himp⟩ := ih₁ hnu₁
    have hw₁nl : ∀ a b, w₁ ≠ .lam a b := by
      intro a b heq
      obtain ⟨a', b', heq'⟩ := himp ⟨a, b, heq⟩
      exact hnl a' b' heq'
    obtain ⟨i₀, hi₀⟩ := Standardization.starWH_evals hap
    exact ⟨i₀ + i₁, .app w₁ t₂,
      ⟨hi₀.trans (Evals.appL t₂ hev₁), whNormal_app_intro t₂ hnw₁ hw₁nl⟩,
      fun ⟨a, b, h⟩ => nomatch h⟩

/-- Convergence transfers along `=β` to a weak-head-normal partner of
any shape (Corollary 2.3 without the value assumption — needed because
the converted member's value-ness is only available *after* its
convergence is established). -/
private theorem beta_whnf_converges {t v : Term} (h : Beta t v)
    (hn : WHNormal v) : ∃ i u, Converges i t u := by
  obtain ⟨e, hte, hve⟩ := beta_iff_common_reduct.mp h
  obtain ⟨i, u, hc, -⟩ :=
    st_whnf_converges (Standardization.st_of_steps hte) (whNormal_steps hve hn)
  exact ⟨i, u, hc⟩

/-- Shape transfer onto an already-normal term: a whnf `=β` a value is
that value's constructor with `=β` components (Corollary 2.3 plus
determinism of `↦`). -/
private theorem value_beta_whnf {v u : Term} (hvu : Beta v u)
    (hu : Term.Value u) (hn : WHNormal v) :
    (v = .top ∧ u = .top) ∨
    ∃ p q α' β', v = .lam p q ∧ u = .lam α' β' ∧ Beta p α' ∧ Beta q β' := by
  cases hu with
  | top =>
    obtain ⟨j₃, hconv⟩ := beta_top_converges hvu
    obtain ⟨-, hveq⟩ := Converges.deterministic ⟨Evals.refl, hn⟩ hconv
    exact .inl ⟨hveq, rfl⟩
  | lam α' β' =>
    obtain ⟨j₃, p, q, hconv, hp, hq⟩ := beta_lam_converges hvu
    obtain ⟨-, hveq⟩ := Converges.deterministic ⟨Evals.refl, hn⟩ hconv
    exact .inr ⟨p, q, α', β', hveq, rfl, hp, hq⟩

/-- The **residual of doc Lemma 4.5's proof**, isolated: transport of a
tier's membership component (t1) across a `=β` change of the member-side
body. The doc §4 argument for this step does not go through as written:
from `MATCH` at every index, `Mem i (β'[c]) (b[c])` is extractable only
at `i ≤ j₁` (the tier's `Good j₁ a c` is downward-closed *only*, Def 3.1
remark (v) — instantiating a deeper tier needs `Good` at the deeper
index), while the index-induction IH needs it at *every* index.
Everything else in Lemma 4.5 is proven, conditional on exactly this
statement (`mem_of_beta_all_of_tier`). -/
private def TierTransport : Prop :=
  ∀ (j₁ : Nat) (α' β' a b q c : Term), Beta q β' →
    (∀ n, Match (n + 1) (.lam α' β') (.lam a b)) →
    Good j₁ a c →
    Mem j₁ (q.subst1 c) (b.subst1 c)

/-- `Match`-transport across a `=β`-componentwise change of the
**member-side** λ, given matches at every index — conditional on the
(t1) residual. The bound clause and (t2) are unconditional: (t2)
composes Lemma 4.4's set equality `⟦q[c]⟧ⱼ₁ = ⟦β'[c]⟧ⱼ₁` with the
supplied tier's inclusion at exactly `j₁`, the doc's argument verbatim. -/
private theorem match_transport_of_tier (gap : TierTransport)
    {m : Nat} {p q α' β' w : Term}
    (hp : Beta p α') (hq : Beta q β') (hwval : Term.Value w)
    (hAll : ∀ n, Match (n + 1) (.lam α' β') w) :
    Match m (.lam p q) w := by
  cases hwval with
  | top => exact match_top
  | lam a b =>
    rcases Match_unfold.mp (hAll 0) with htop | ⟨a₀, b₀, α₀, β₀, hw, hv, hα, -⟩
    · cases htop
    · injection hw with hw1 hw2
      injection hv with hv1 hv2
      subst hw1; subst hw2; subst hv1; subst hv2
      rw [Match_unfold]
      refine .inr ⟨a, b, p, q, rfl, rfl, hp.trans hα, ?_⟩
      intro j₁ c hj₁ hc
      refine ⟨gap j₁ α' β' a b q c hq hAll hc, ?_⟩
      intro s' hs'
      have hs'' : Mem j₁ s' (β'.subst1 c) :=
        (mem_beta_type (Beta.subst1 hq (Beta.refl c))).mp hs'
      rcases Match_unfold.mp (hAll j₁) with htop2 |
        ⟨a₁, b₁, α₁, β₁, hw2, hv2, -, htier⟩
      · cases htop2
      · injection hw2 with hw21 hw22
        injection hv2 with hv21 hv22
        subst hw21; subst hw22; subst hv21; subst hv22
        exact (htier j₁ c (Nat.lt_succ_self j₁) hc).2 s' hs''

/-- **Lemma 4.5, conditional form**: the full doc §4 proof of
`mem_of_beta_all` — standardization transfer of the converted member's
convergence (`beta_whnf_converges`; `i′` unrelated to `k`), value
transfer by determinism of `↦`, ∀-index `MATCH` extraction with the type
side identified by `Converges.deterministic`, and the member-side
`Match` transport — kernel-checked, with the (t1) residual as a
hypothesis. No induction on the index remains: the residual was the
proof's *only* recursive step. -/
private theorem mem_of_beta_all_of_tier (gap : TierTransport)
    {k : Nat} {s s' T : Term}
    (hs : Beta s s') (h : ∀ k', Mem k' s' T) : Mem k s T := by
  rw [Mem_unfold]
  intro j v hj hconv
  have hsv : Beta s v := Beta.of_steps hconv.1.toSteps
  obtain ⟨i', u, huconv⟩ :=
    beta_whnf_converges ((Beta.symm hs).trans hsv) hconv.2
  obtain ⟨huval, w, hTw, hwval, -⟩ :=
    Mem_unfold.mp (h (i' + 1)) i' u (Nat.lt_succ_self i') huconv
  have hAll : ∀ n, Match (n + 1) u w := by
    intro n
    obtain ⟨-, w₂, hTw₂, -, hm⟩ :=
      Mem_unfold.mp (h (i' + 1 + n)) i' u (by omega) huconv
    obtain ⟨jT, hjT⟩ := hTw
    obtain ⟨jT₂, hjT₂⟩ := hTw₂
    obtain ⟨-, hww⟩ := Converges.deterministic hjT₂ hjT
    rw [hww, show i' + 1 + n - i' = n + 1 from by omega] at hm
    exact hm
  have hvu : Beta v u :=
    (Beta.symm hsv).trans (hs.trans (Beta.of_steps huconv.1.toSteps))
  rcases value_beta_whnf hvu huval hconv.2 with ⟨rfl, rfl⟩ |
    ⟨p, q, α', β', rfl, rfl, hp, hq⟩
  · refine ⟨.top, w, hTw, hwval, ?_⟩
    have hm := hAll (k - j - 1)
    rw [show k - j - 1 + 1 = k - j from by omega] at hm
    exact hm
  · exact ⟨.lam p q, w, hTw, hwval,
      match_transport_of_tier gap hp hq hwval hAll⟩

/-- **Lemma 4.5 (member conversion)**: ∀-index hypothesis, single-index
conclusion — `i′` (the converted member's evaluation length) is
unrelated to `k`, which is why the hypothesis must be ∀-quantified
(doc §4). -/
theorem mem_of_beta_all {k : Nat} {s s' T : Term}
    (hs : Beta s s') (h : ∀ k', Mem k' s' T) : Mem k s T := by
  -- UNPROVEN: doc §4's proof of Lemma 4.5 has a quantifier gap at the
  -- tier's (t1) component. `mem_of_beta_all_of_tier` above is the whole
  -- doc proof, kernel-checked, conditional on exactly the residual
  -- `TierTransport`; the doc's justification for that residual ("[c]β′ ∈
  -- ⟦[c]b⟧ at every index, from MATCH at every index") needs `Good i a c`
  -- at every `i`, but the tier supplies it only at `i ≤ j₁` (goodness is
  -- downward-closed only). Counterexample attempts against the statement
  -- itself fail systematically (divergent arguments are good at every
  -- depth, forcing ∀-index tier facts; goodness's self-membership
  -- component caps exactly compensate member-side padding), so the
  -- statement is conjectured true — but a proof needs an argument beyond
  -- the doc's. See the commit message for the full analysis, and note
  -- the FT's only planned use site (`sound_app_le`, doc §6 step (d)) can
  -- be closed without 4.5: `U ∈ ⟦U⟧ᵢ ⊆ ⟦S⟧ᵢ = ⟦S′⟧ᵢ = ⟦A′⟧ᵢ` via IH(1),
  -- the unprimed inclusion, and 4.4 along the bound chain (c).
  exact mem_of_beta_all_of_tier (fun j₁ α' β' a b q c hq hAll hc => by
    sorry) hs h

end Pss.Semantic
