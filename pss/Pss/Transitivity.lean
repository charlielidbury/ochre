import Pss.Basic

/-!
# §6 Transitivity elimination (Hutchins, *Pure Subtype Systems*, POPL 2010)

The paper's headline development: transitivity is admissible in the
algorithmic system provided the underlying reductions are confluent /
commute (§6.3). This file states the three §6.3–§6.6 properties

* `EqConfluent` — Theorem 6.1's property (`≡→` is confluent),
* `Commutes` — Conjecture 6.2's property (`≡→` commutes with `≤→`),
* `LocallyCommutes` — Lemma 6.4's property (local commutation, with a
  *transitive subtyping judgment* on the completing edge),

and proves **Lemma 6.3** (commutativity implies transitivity): from
`EqConfluent` and `Commutes`, the transitive-subtyping judgment `⊲*`
collapses into plain algorithmic subtyping `⊲`.
-/

namespace Pss

/-- **Theorem 6.1's property** (`≡→` is confluent, p. 295):

> If `Γ ⊢A t₀ ≡→* t₁, t₀ ≡→* t₂`, then there exists a `t₃`, such that
> `Γ ⊢A t₁ ≡→* t₃, t₂ ≡→* t₃`. -/
def EqConfluent : Prop :=
  ∀ Γ t0 t1 t2, RedStar Γ t0 .eq t1 → RedStar Γ t0 .eq t2 →
    ∃ t3, RedStar Γ t1 .eq t3 ∧ RedStar Γ t2 .eq t3

/-- **Conjecture 6.2's property** (`≡→` commutes with `≤→`, p. 295):

> If `Γ ⊢A t₀ ≡→* t₁, t₀ ≤→* t₂` then there exists a `t₃`, such that
> `Γ ⊢A t₂ ≡→* t₃, t₁ ≤→* t₃`.

The spanning edges are the premises; the completing edges are the
conclusion, exactly as in the paper's diagram. -/
def Commutes : Prop :=
  ∀ Γ t0 t1 t2, RedStar Γ t0 .eq t1 → RedStar Γ t0 .le t2 →
    ∃ t3, RedStar Γ t2 .eq t3 ∧ RedStar Γ t1 .le t3

/-- **Lemma 6.4's property** (`≤→` and `≡→` commute locally, p. 296):

> If `Γ ⊢A t₀ ≡→ t₁, t₀ ≤→ t₂`, then there exists a `t₃`, such that
> `Γ ⊢A t₂ ≡→⁽⁼⁾ t₃, and Γ ⊢A t₁ ≤* t₃`, where `≡→⁽⁼⁾` is the reflexive
> closure of `≡→`.

Note the asymmetry (§6.6): the top completing edge is (at most) *one*
`≡`-step, but the right completing edge is a transitive subtyping
*judgment* `≤*`, not a reduction sequence — "which would prove
commutativity". -/
def LocallyCommutes : Prop :=
  ∀ Γ t0 t1 t2, Red Γ t0 .eq t1 → Red Γ t0 .le t2 →
    ∃ t3, (t2 = t3 ∨ Red Γ t2 .eq t3) ∧ ATSub Γ t1 .le t3

namespace Statements

/-- **Conjecture 6.2 (`≡→` commutes with `≤→`), p. 295 — OPEN.**

Open problem in the paper (§6.6: "we have thus far been unable to show
that they commute globally"; §7 presents it as an open problem for the
rewriting community). Stated as a `Prop`, never an axiom. By
`lemma_6_3`, together with Theorem 6.1 it implies transitivity
elimination, and by §5 (Theorem 5.6) type safety of System λ⊲. -/
def conjecture_6_2 : Prop := Commutes

end Statements

/-! ## Lemma 6.3 (commutativity implies transitivity), p. 295

> If `≡→` commutes with `≤→`, then transitivity is admissible.

The proof composes the two joins given by `ASub.to_join` through the
commutativity (for `≤`) or confluence (for `≡`) diagram, exactly as in
the paper's diagram: from `s ⊲→* a *←≡ t` and `t ⊲→* b *←≡ u`, the
spanning peak at `t` is completed by some `c` with `a ⊲→* c` and
`b ≡→* c`, whence `s ⊲→* c *←≡ u`. -/

/-- **Lemma 6.3 (commutativity implies transitivity).** Given confluence
of `≡→` (Theorem 6.1's property) and commutation of `≡→` with `≤→`
(Conjecture 6.2's property), algorithmic subtyping is transitive. -/
theorem lemma_6_3 (hconf : EqConfluent) (hcomm : Commutes) :
    ∀ Γ s t u r, ASub Γ s r t → ASub Γ t r u → ASub Γ s r u := by
  intro Γ s t u r h1 h2
  obtain ⟨a, hsa, hta⟩ := h1.to_join
  obtain ⟨b, htb, hub⟩ := h2.to_join
  cases r with
  | le =>
    -- Peak at `t`: `a *←≡ t ≤→* b`; commute to get `b ≡→* c`, `a ≤→* c`.
    obtain ⟨c, hbc, hac⟩ := hcomm Γ t a b hta htb
    exact ASub.of_join h1.prevalid (hsa.trans hac) (hub.trans hbc)
  | eq =>
    -- Peak at `t`: `a *←≡ t ≡→* b`; confluence gives the common reduct.
    obtain ⟨c, hac, hbc⟩ := hconf Γ t a b hta htb
    exact ASub.of_join h1.prevalid (hsa.trans hac) (hub.trans hbc)

/-- Corollary of Lemma 6.3: under the same hypotheses the *transitive*
subtyping judgment `⊲*` (AST-SUB/AST-TRANS) collapses into plain
algorithmic subtyping `⊲` — transitivity elimination for the
algorithmic system. By induction on the `⊲*` derivation. -/
theorem atsub_to_asub (hconf : EqConfluent) (hcomm : Commutes)
    {Γ : Ctx} {s u : Term} {r : Rel} (h : ATSub Γ s r u) : ASub Γ s r u :=
  h.induct
    (motR := fun _ _ _ _ => True)
    (motA := fun Γ t r u => ASub Γ t r u)
    (motT := fun Γ t r u => ASub Γ t r u)
    (red_prom := fun _ _ => trivial)
    (red_rtop := fun _ => trivial)
    (red_beta := fun _ _ => trivial)
    (red_topApp := fun _ => trivial)
    (red_cong := fun _ _ _ => trivial)
    (red_fn := fun _ _ => trivial)
    (red_eq := fun _ _ => trivial)
    (asub_refl := fun h => .refl h)
    (asub_left := fun hred h _ _ => .left hred h)
    (asub_right := fun hred h _ _ => .right hred h)
    (atsub_sub := fun _ ih => ih)
    (atsub_trans := fun _ _ ih1 ih2 => lemma_6_3 hconf hcomm _ _ _ _ _ ih1 ih2)

/-- Wire-up: the transitivity-elimination conclusion, conditional on the
two §6 reduction properties (Theorem 6.1 + Conjecture 6.2). -/
theorem transitivity_admissible_of (h1 : EqConfluent) (h2 : Commutes)
    {Γ : Ctx} {s t u : Term} {r : Rel}
    (hst : ASub Γ s r t) (htu : ASub Γ t r u) : ASub Γ s r u :=
  lemma_6_3 h1 h2 Γ s t u r hst htu

end Pss
