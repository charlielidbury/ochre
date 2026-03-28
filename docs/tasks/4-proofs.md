# Problem

Layer 4: Proofs
Task 4.1: Prove soundness (§7.1). If Γ ⊢ e ⇝ τ and γ ⊨ Γ and γ ⊢ e ⇓ v, then v ⊑ τ. Proof by induction on the derivation of Γ ⊢ e ⇝ τ, one case per typing rule. Verification: every case of the typing rules is covered, each case is a valid logical argument. Depends on all of Layer 2.
Task 4.2: Prove monotonicity (§7.2). If Γ₂ ⊑ Γ₁ then τ₂ ⊑ τ₁. Proof by induction on the derivation. The critical cases are application (transparent vs ascribed) and the interaction with partitioning. Verification: every case covered. Depends on all of Layer 2 and 3.
Task 4.3: Prove ascription soundness (§7.3). If Γ ⊢ e ⇝ σ and (e : τ) is well-formed, then σ ⊑ τ. This should be a short proof falling directly out of the ascription typing rule. Verification: complete proof. Depends on 2.1.
Task 4.4: Prove transparency preservation (§7.4). For closed terms without ascription, ∅ ⊢ e ⇝ τ implies τ is the singleton. This requires showing that the abstract interpreter, when given fully concrete inputs, traces the same path as concrete evaluation. Verification: complete proof. Depends on 2.1 and 4.1.

# Solution
// put your answer here