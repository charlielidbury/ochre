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

/-- **Lemma 4.4 (type conversion invariance)**: `T =β T′` gives the set
*equality* `⟦T⟧ₖ = ⟦T′⟧ₖ`, at every fixed index. -/
theorem mem_beta_type {k : Nat} {s T T' : Term}
    (hT : Beta T T') : Mem k s T ↔ Mem k s T' := by
  sorry

/-- **Lemma 4.4**, goodness: `a =β a′` gives `⟨a⟩ⱼ = ⟨a′⟩ⱼ` (memberships
directly, inclusions because `⟦a⟧ᵢ = ⟦a′⟧ᵢ` as sets). -/
theorem good_beta_bound {j : Nat} {a a' c : Term}
    (ha : Beta a a') : Good j a c ↔ Good j a' c := by
  sorry

/-- **Lemma 4.5 (member conversion)**: ∀-index hypothesis, single-index
conclusion — `i′` (the converted member's evaluation length) is
unrelated to `k`, which is why the hypothesis must be ∀-quantified
(doc §4). -/
theorem mem_of_beta_all {k : Nat} {s s' T : Term}
    (hs : Beta s s') (h : ∀ k', Mem k' s' T) : Mem k s T := by
  sorry

end Pss.Semantic
