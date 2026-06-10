import Pss.Semantic.Model

/-!
# Structural lemmas of the model

§4 of `pss/docs/03-revised-proof.md`: Lemma 4.1 (antitonicity), Lemma 4.2
(step shift), Lemma 4.3 (type evaluation invariance). All statements are
consumed through `Mem_unfold`/`Match_unfold`/`Good_unfold`.

The doc's §4 discipline box, binding for every consumer: extension
*inclusions* `⟦t⟧ₖ ⊆ ⟦u⟧ₖ` are **not** antitone in `k` — only
memberships are. Goodness is antitone because its inclusion components
are downward-closed by fiat (`i ≤ j` in `Good`).
-/

namespace Pss.Semantic

/-- Private engine for `match_antitone` (placed before `mem_antitone`,
which consumes it). The `top` disjunct is index-free; the `lam` disjunct's
tier quantifier domain `j' < m₁ ⊆ j' < m₂` shrinks. No recursion. -/
private theorem match_antitone_aux {m₁ m₂ : Nat} {v w : Term} (hm : m₁ ≤ m₂)
    (h : Match m₂ v w) : Match m₁ v w := by
  rw [Match_unfold] at h ⊢
  rcases h with htop | ⟨a, b, α, β, hw, hv, hbound, htier⟩
  · exact .inl htop
  · refine .inr ⟨a, b, α, β, hw, hv, hbound, ?_⟩
    intro j' c hj' hgood
    exact htier j' c (Nat.lt_of_lt_of_le hj' hm) hgood

/-- **Lemma 4.1 (antitonicity)**, membership: a larger index imposes a
superset of obligations. -/
theorem mem_antitone {j k : Nat} {s T : Term} (hjk : j ≤ k)
    (h : Mem k s T) : Mem j s T := by
  rw [Mem_unfold] at h ⊢
  intro j' v hj' hconv
  obtain ⟨hv, w, hTw, hvw, hmatch⟩ := h j' v (Nat.lt_of_lt_of_le hj' hjk) hconv
  exact ⟨hv, w, hTw, hvw, match_antitone_aux (by omega) hmatch⟩

/-- **Lemma 4.1**, MATCH tiers: antitone in the tier index. -/
theorem match_antitone {m₁ m₂ : Nat} {v w : Term} (hm : m₁ ≤ m₂)
    (h : Match m₂ v w) : Match m₁ v w :=
  match_antitone_aux hm h

/-- **Lemma 4.1**, goodness: membership components by `mem_antitone`,
inclusion components by their explicit `i ≤ j` downward closure. -/
theorem good_antitone {j k : Nat} {a c : Term} (hjk : j ≤ k)
    (h : Good k a c) : Good j a c := by
  rw [Good_unfold] at h ⊢
  obtain ⟨hca, hcc, hincl⟩ := h
  refine ⟨mem_antitone hjk hca, mem_antitone hjk hcc, ?_⟩
  intro i s' hij hmem
  exact hincl i s' (Nat.le_trans hij hjk) hmem

/-- **Lemma 4.1**, contexts: `⟦Γ⟧ₖ ⊆ ⟦Γ⟧ⱼ`. -/
theorem semCtx_antitone {j k : Nat} {Γ : Ctx} {γ : Nat → Term}
    (hjk : j ≤ k) (h : SemCtx k Γ γ) : SemCtx j Γ γ := by
  intro x t hbound
  exact good_antitone hjk (h x t hbound)

/-- **Lemma 4.2 (step shift)**, backwards: a member's predecessor along
`↦` is a member one index up (`s ⇓^{j+1} v ⟺ s₁ ⇓ʲ v`). -/
theorem mem_whStep_intro {k : Nat} {s s₁ T : Term}
    (hs : WHStep s s₁) (h : Mem k s₁ T) : Mem (k + 1) s T := by
  rw [Mem_unfold] at h ⊢
  intro j v hj hconv
  cases j with
  | zero =>
    -- `Converges 0 s v` forces `s` weak-head normal, contradicting `s ↦ s₁`.
    obtain ⟨he, hn⟩ := hconv
    cases he
    exact absurd hs (hn s₁)
  | succ j' =>
    have hconv' : Converges j' s₁ v := Converges.whStep_inv hs hconv
    obtain ⟨hv, w, hTw, hvw, hmatch⟩ := h j' v (by omega) hconv'
    refine ⟨hv, w, hTw, hvw, ?_⟩
    have : k + 1 - (j' + 1) = k - j' := by omega
    rw [this]
    exact hmatch

/-- **Lemma 4.2 (step shift)**, forwards: stepping a member costs one
index (determinism of `↦`). -/
theorem mem_whStep_elim {k : Nat} {s s₁ T : Term}
    (hs : WHStep s s₁) (h : Mem (k + 1) s T) : Mem k s₁ T := by
  rw [Mem_unfold] at h ⊢
  intro j v hj hconv
  have hconv' : Converges (j + 1) s v := Converges.of_whStep hs hconv
  obtain ⟨hv, w, hTw, hvw, hmatch⟩ := h (j + 1) v (by omega) hconv'
  refine ⟨hv, w, hTw, hvw, ?_⟩
  have : k + 1 - (j + 1) = k - j := by omega
  rw [this] at hmatch
  exact hmatch

/-- **Lemma 4.3 (type evaluation invariance)**: the clause inspects only
the type's weak-head value, so a weak-head step of the type changes
nothing — at the *same* index. Presupposes the step exists (doc: uses
establish the type's convergence first, typically from (m2) of a
converging member). -/
theorem mem_type_whStep {k : Nat} {s T T' : Term}
    (hT : WHStep T T') : Mem k s T ↔ Mem k s T' := by
  sorry

/-- **Lemma 4.3**, iterated: `⟦T⟧ₖ = ⟦T′⟧ₖ` along any weak-head
evaluation of the type. -/
theorem mem_type_evals {k j : Nat} {s T T' : Term}
    (hT : Evals j T T') : Mem k s T ↔ Mem k s T' := by
  sorry

end Pss.Semantic
