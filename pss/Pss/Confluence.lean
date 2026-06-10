import Pss.Transitivity
import Pss.AlgWeakening

/-!
# §6.5–§6.6: confluence of `≡→` and local commutation (Lemma 6.4)

* **Lemma 6.4** (`lemma_6_4`): `≤→` and `≡→` commute locally, with the
  reflexive closure of one `≡`-step on top and a transitive subtyping
  *judgment* on the right. Proved — see the docstring for why the
  literal statement admits a short proof, and `lemma_6_4_top_case` /
  `lemma_6_4_prom_case` for the paper's §6.6.1 showcase diagrams with
  their *intended* (reduction-derived) completions.
* **Theorem 6.1** (`Statements.thm_6_1`): confluence of `≡→`, attacked
  via Takahashi-style parallel reduction (`Par`, §6.5) adapted to the
  conditional rewrite system; the embedding `≡→ ⊆ Par ⊆ ≡→*` is proved.
-/

namespace Pss

/-! ## Lemma 6.4 (`≤→` and `≡→` commute locally), p. 296

> If `Γ ⊢A t₀ ≡→ t₁, t₀ ≤→ t₂`, then there exists a `t₃`, such that
> `Γ ⊢A t₂ ≡→⁽⁼⁾ t₃`, and `Γ ⊢A t₁ ≤* t₃`.

**Why this is provable directly.** The paper stresses (§6.6) that "the
completing edge of the diagram on the right-hand side is not a subtype
reduction (which would prove commutativity) but a transitive subtyping
judgement". Subtyping judgments may fold reductions *backwards*:
AS-RIGHT gives `t₁ ⊲ t₀` from the spanning edge `t₀ ≡→ t₁` itself, and
AS-LEFT gives `t₀ ⊲ t₂` from the spanning edge `t₀ ≤→ t₂`, so
`t₁ ≤* t₀ ≤* t₂` by AST-TRANS and the diagram closes degenerately at
`t₃ = t₂` with a reflexive top edge.

This makes the literal Lemma 6.4 true, but the degenerate completion is
useless for the paper's §6.6.2 decreasing-diagrams program: there the
completing judgment must have *strictly smaller index* than the
spanning edges, whereas this completion contains them. The substantive
§6.6.1 case analysis (thesis [19]) produces completions whose right
edges are built from *new* reductions — the two key cases are proved
below as `lemma_6_4_top_case` and `lemma_6_4_prom_case`. What remains
genuinely open is global commutativity (`Statements.conjecture_6_2`).
-/

/-- **Lemma 6.4** (p. 296): local commutation of `≤→` and `≡→`, with a
transitive subtyping judgment as the right completing edge. -/
theorem lemma_6_4 : LocallyCommutes := by
  intro Γ t0 t1 t2 he hl
  exact ⟨t2, .inl rfl, .trans (.sub (.of_red_rev .le he)) (.of_red hl)⟩

/-! ## §6.6.1: the two showcase diagrams, with the paper's completions -/

/-- §6.6.1 case (1): the term `Top(c)`.

```
   Top(c) ⋯⋯≡⋯⋯▸ Top
     ▴              ▴
   ≤ │              ⋮ ≤*
 (λx ≤ a. b)(c) ─≡─▸ [x ↦ c]b
```

The `≤`-edge promotes the function to `Top` (SRS-TOP under `E≤`); the
`≡`-edge β-fires (SRE-APP, guarded by `c ≤* a`). The completing top
edge is SRE-TOPAPP — "the term `Top(c)` is not well-formed, but we must
handle it because algorithmic subtyping is defined over all terms" —
and the completing right edge is promotion to `Top`. -/
theorem lemma_6_4_top_case {Γ : Ctx} {a b c : Term}
    (hc : ATSub Γ c .le a) :
    -- spanning edges
    Red Γ (.app (.lam a b) c) .eq (b.subst1 c)
    ∧ Red Γ (.app (.lam a b) c) .le (.app .top c)
    -- completing edges, meeting at t₃ = Top
    ∧ Red Γ (.app .top c) .eq .top
    ∧ ATSub Γ (b.subst1 c) .le .top :=
  have hΓ : Prevalid Γ := hc.prevalid
  ⟨.beta hc, .cong (ECtx.appL .hole c) (.rtop hΓ),
   .topApp hΓ, .of_red (.rtop hΓ)⟩

/-- §6.6.1 case (2): promotion of the bound variable inside a redex.

```
 (λx ≤ a. C≤[a])(c) ─≡─▸ [x ↦ c]C≤[a]
     ▴                        ⋮
   ≤ │                        ⋮ ≤*
 (λx ≤ a. C≤[x])(c) ─≡─▸ [x ↦ c]C≤[x]
```

The `≤`-edge promotes the bound variable `x` (= de Bruijn index 0, so
its bound is `a.shift 1` inside the body) in a positive position `C≤`
of the body (SRS-PROM under SR-CONG under SR-FUN); the `≡`-edge β-fires
guarded by `c ≤* a`. The top completing edge β-fires the promoted
redex; the right completing edge is "the only case which requires `≤*`
as the completing edge": `[x ↦ c]C≤[x] = C≤'[c] ≤* C≤'[a] = [x ↦ c]C≤[a]`
by `E≤`-congruence of `≤*` applied to the SRE-APP premise `c ≤* a` —
"a simple promotion on the left-hand side becomes a full subtyping
judgement on the right-hand side." -/
theorem lemma_6_4_prom_case {Γ : Ctx} {a c : Term} (E : ECtx .le)
    (hc : ATSub Γ c .le a) (ha : Term.ClosedUnder Γ.length a) :
    -- spanning edges
    Red Γ (.app (.lam a (E.fill (.var 0))) c) .eq
      ((E.fill (.var 0)).subst1 c)
    ∧ Red Γ (.app (.lam a (E.fill (.var 0))) c) .le
      (.app (.lam a (E.fill (a.shift 1))) c)
    -- completing edges
    ∧ Red Γ (.app (.lam a (E.fill (a.shift 1))) c) .eq
      ((E.fill (a.shift 1)).subst1 c)
    ∧ ATSub Γ ((E.fill (.var 0)).subst1 c) .le
      ((E.fill (a.shift 1)).subst1 c) := by
  have hΓa : Prevalid (a :: Γ) := .cons hc.prevalid ha
  refine ⟨.beta hc,
    .cong (ECtx.appL .hole c) (.fn (.cong E (.prom hΓa .here))),
    .beta hc, ?_⟩
  -- Right edge: `[x ↦ c]` turns `C≤[x]` into `C≤'[c]` and `C≤[↑a]`
  -- into `C≤'[a]`, and `c ≤* a` lifts through `C≤'` by congruence.
  have key : (a.shift 1).subst (Term.scons c Term.var) = a :=
    Term.shift_subst1 a c
  show ATSub Γ ((E.fill (.var 0)).subst (Term.scons c .var)) .le
    ((E.fill (a.shift 1)).subst (Term.scons c .var))
  rw [ECtx.fill_subst, ECtx.fill_subst, key]
  exact hc.cong _

end Pss
