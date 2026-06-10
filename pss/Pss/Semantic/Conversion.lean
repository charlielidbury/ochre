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

/-- **Lemma 4.5 (member conversion)**: ∀-index hypothesis, single-index
conclusion — `i′` (the converted member's evaluation length) is
unrelated to `k`, which is why the hypothesis must be ∀-quantified
(doc §4). -/
theorem mem_of_beta_all {k : Nat} {s s' T : Term}
    (hs : Beta s s') (h : ∀ k', Mem k' s' T) : Mem k s T := by
  sorry

end Pss.Semantic
