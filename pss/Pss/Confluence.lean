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

/-! ## §6.5: parallel reduction for `≡→`

> "Our proof is an adaptation of Takahashi's proof of confluence for
> the untyped λ-calculus [29] [6], which shows that simultaneous
> reduction has the diamond property. Full details can be found in [19]."

`Par Γ t t'` simultaneously contracts any set of non-overlapping
`≡`-redexes of `t`: β-redexes (SRE-APP, *with its `≤*` guard* — this is
how the conditional rewrite system rides through the development) and
`Top`-applications (SRE-TOPAPP), congruently in every `≡`-position
(arguments, bounds via `E≡`, bodies via SR-FUN's context extension). -/

/-- Takahashi-style simultaneous `≡`-reduction, adapted to the
conditional system of Figure 2. -/
inductive Par : Ctx → Term → Term → Prop where
  | var {Γ : Ctx} {x : Nat} : Par Γ (.var x) (.var x)
  | top {Γ : Ctx} : Par Γ .top .top
  | lam {Γ : Ctx} {a a' u u' : Term} :
      Par Γ a a' → Par (a :: Γ) u u' → Par Γ (.lam a u) (.lam a' u')
  | app {Γ : Ctx} {t t' u u' : Term} :
      Par Γ t t' → Par Γ u u' → Par Γ (.app t u) (.app t' u')
  /-- SRE-APP, parallel form: contract the redex and reduce inside the
  body and argument simultaneously. The guard is the SRE-APP premise. -/
  | beta {Γ : Ctx} {a b b' s s' : Term} :
      ATSub Γ s .le a → Par (a :: Γ) b b' → Par Γ s s' →
      Par Γ (.app (.lam a b) s) (b'.subst1 s')
  /-- SRE-TOPAPP, parallel form. -/
  | topApp {Γ : Ctx} {t : Term} : Prevalid Γ → Par Γ (.app .top t) .top

/-- Parallel reduction is reflexive (the empty redex set). -/
theorem Par.refl : ∀ (t : Term) (Γ : Ctx), Par Γ t t
  | .var _, _ => .var
  | .top, _ => .top
  | .lam a u, Γ => .lam (Par.refl a Γ) (Par.refl u (a :: Γ))
  | .app t u, Γ => .app (Par.refl t Γ) (Par.refl u Γ)

/-- Variables only parallel-reduce to themselves. -/
theorem Par.var_inv {Γ : Ctx} {x : Nat} {t' : Term}
    (h : Par Γ (.var x) t') : t' = .var x := by
  cases h; rfl

/-- `Top` only parallel-reduces to itself. -/
theorem Par.top_inv {Γ : Ctx} {t' : Term}
    (h : Par Γ .top t') : t' = .top := by
  cases h; rfl

/-- Parallel reduction is closed under `E≡` contexts (fill the rest of
the context with reflexivity). -/
theorem Par.fill {Γ : Ctx} : (E : ECtx .eq) → ∀ {t t' : Term},
    Par Γ t t' → Par Γ (E.fill t) (E.fill t')
  | .hole, _, _, h => h
  | .appL E u, _, _, h => .app (Par.fill E h) (Par.refl u Γ)
  | .appR u E, _, _, h => .app (Par.refl u Γ) (Par.fill E h)
  | .lamBound E u, _, _, h => .lam (Par.fill E h) (Par.refl u _)

/-- **`≡→ ⊆ Par`**: every single equivalence-reduction step is a
parallel step. -/
theorem Par.of_red {Γ : Ctx} {t t' : Term} (h : Red Γ t .eq t') :
    Par Γ t t' := by
  refine h.induct
    (motR := fun Γ t r t' => r = .eq → Par Γ t t')
    (motA := fun _ _ _ _ => True)
    (motT := fun _ _ _ _ => True)
    (red_prom := fun _ _ h => nomatch h)
    (red_rtop := fun _ h => nomatch h)
    (red_beta := fun hts _ _ => .beta hts (Par.refl _ _) (Par.refl _ _))
    (red_topApp := fun h _ => .topApp h)
    (red_cong := fun {_ _ _ r} E _ ih heq => by
      subst heq
      exact Par.fill E (ih rfl))
    (red_fn := fun {_ _ _ _ r} _ ih heq => by
      subst heq
      exact .lam (Par.refl _ _) (ih rfl))
    (red_eq := fun _ _ h => nomatch h)
    (asub_refl := fun _ => trivial)
    (asub_left := fun _ _ _ _ => trivial)
    (asub_right := fun _ _ _ _ => trivial)
    (atsub_sub := fun _ _ => trivial)
    (atsub_trans := fun _ _ _ _ => trivial)
    rfl

/-- Guard transport: the SRE-APP premise `s ≤* a` survives `≡`-reduction
of the argument `s ≡→* s'` — fold the sequence backwards with AS-RIGHT
and chain with AST-TRANS. This is how the condition "rides through" the
parallel-reduction development (§6.5). -/
theorem ATSub.guard_left {Γ : Ctx} {s s' a : Term}
    (hred : RedStar Γ s .eq s') (hg : ATSub Γ s .le a) :
    ATSub Γ s' .le a :=
  .trans (.sub (ASub.of_join hg.prevalid .refl hred)) hg

/-- `≡→*` congruence in function position (`E≡ = [](u)`). -/
theorem RedStar.appL {Γ : Ctx} {t t' : Term} (u : Term)
    (h : RedStar Γ t .eq t') : RedStar Γ (.app t u) .eq (.app t' u) :=
  h.map (fun x => Term.app x u) fun hs => .cong (ECtx.appL .hole u) hs

/-- `≡→*` congruence in argument position (`E≡ = t([])`). -/
theorem RedStar.appR {Γ : Ctx} (t : Term) {u u' : Term}
    (h : RedStar Γ u .eq u') : RedStar Γ (.app t u) .eq (.app t u') :=
  h.map (Term.app t) fun hs => .cong (ECtx.appR t .hole) hs

/-- `≡→*` congruence in bound position (`E≡ = λx ≤ []. u`). -/
theorem RedStar.lamBound {Γ : Ctx} (u : Term) {a a' : Term}
    (h : RedStar Γ a .eq a') : RedStar Γ (.lam a u) .eq (.lam a' u) :=
  h.map (fun x => Term.lam x u) fun hs => .cong (ECtx.lamBound .hole u) hs

/-- **`Par ⊆ ≡→*`**: a parallel step sequentializes into equivalence
reduction. The β-case fires SRE-APP *after* reducing body and argument,
with the guard transported by `ATSub.guard_left`. -/
theorem Par.to_redStar {Γ : Ctx} {t t' : Term} (h : Par Γ t t') :
    RedStar Γ t .eq t' := by
  induction h with
  | var => exact .refl
  | top => exact .refl
  | lam _ _ iha ihu => exact (RedStar.fn ihu).trans (RedStar.lamBound _ iha)
  | app _ _ iht ihu => exact (RedStar.appL _ iht).trans (RedStar.appR _ ihu)
  | beta hg _ _ ihb ihs =>
    exact (((RedStar.appL _ (RedStar.fn ihb)).trans
      (RedStar.appR _ ihs)).tail (.beta (ATSub.guard_left ihs hg)))
  | topApp h => exact Star.single (.topApp h)

/-- `≡→*` sequences are `Par`-sequences. -/
theorem parStar_of_redStar {Γ : Ctx} {t t' : Term}
    (h : RedStar Γ t .eq t') : Star (Par Γ) t t' :=
  h.mono fun hs => Par.of_red hs

/-- `Par`-sequences are `≡→*` sequences. -/
theorem redStar_of_parStar {Γ : Ctx} {t t' : Term}
    (h : Star (Par Γ) t t') : RedStar Γ t .eq t' := by
  induction h with
  | refl => exact .refl
  | head hab _ ih => exact (Par.to_redStar hab).trans ih

/-! ## The diamond property and Theorem 6.1 -/

/-- The diamond property for parallel reduction — the §6.5 crux. -/
def ParDiamond : Prop :=
  ∀ Γ t t1 t2, Par Γ t t1 → Par Γ t t2 →
    ∃ t3, Par Γ t1 t3 ∧ Par Γ t2 t3

/-- Strip lemma: one parallel step against a `Par`-sequence. -/
theorem parStrip (hd : ParDiamond) {Γ : Ctx} {t t1 t2 : Term}
    (h1 : Par Γ t t1) (h2 : Star (Par Γ) t t2) :
    ∃ t3, Star (Par Γ) t1 t3 ∧ Par Γ t2 t3 := by
  induction h2 generalizing t1 with
  | refl => exact ⟨t1, .refl, h1⟩
  | head hab _ ih =>
    obtain ⟨c, hc1, hc2⟩ := hd _ _ _ _ h1 hab
    obtain ⟨t3, h31, h32⟩ := ih hc2
    exact ⟨t3, .head hc1 h31, h32⟩

/-- The diamond property tiles to confluence of `Par`-sequences. -/
theorem parStar_confluent (hd : ParDiamond) {Γ : Ctx} {t t1 t2 : Term}
    (h1 : Star (Par Γ) t t1) (h2 : Star (Par Γ) t t2) :
    ∃ t3, Star (Par Γ) t1 t3 ∧ Star (Par Γ) t2 t3 := by
  induction h1 generalizing t2 with
  | refl => exact ⟨t2, h2, .refl⟩
  | head hab _ ih =>
    obtain ⟨c, hc1, hc2⟩ := parStrip hd hab h2
    obtain ⟨t3, h31, h32⟩ := ih hc1
    exact ⟨t3, h31, .head hc2 h32⟩

/-- **Theorem 6.1, reduced to the diamond property**: if `Par` has the
diamond property, then `≡→` is confluent (sandwich `≡→ ⊆ Par ⊆ ≡→*`
through `parStar_confluent`). -/
theorem eqConfluent_of_parDiamond (hd : ParDiamond) : EqConfluent := by
  intro Γ t0 t1 t2 h1 h2
  obtain ⟨t3, h31, h32⟩ :=
    parStar_confluent hd (parStar_of_redStar h1) (parStar_of_redStar h2)
  exact ⟨t3, redStar_of_parStar h31, redStar_of_parStar h32⟩

/-- A closed diamond case: the SRE-TOPAPP redex `Top(t)` against any
parallel step (`Top` is rigid, so the overlap is harmless). -/
theorem parDiamond_topApp_case {Γ : Ctx} {t t2 : Term}
    (hΓ : Prevalid Γ) (h2 : Par Γ (.app .top t) t2) :
    ∃ t3, Par Γ .top t3 ∧ Par Γ t2 t3 := by
  cases h2 with
  | app hf ht =>
    have := Par.top_inv hf
    subst this
    exact ⟨.top, .top, .topApp hΓ⟩
  | topApp _ => exact ⟨.top, .top, .top⟩

namespace Statements

/-- **Theorem 6.1 (`≡→` is confluent), p. 295 — STATED.**

> If `Γ ⊢A t₀ ≡→* t₁, t₀ ≡→* t₂`, then there exists a `t₃`, such that
> `Γ ⊢A t₁ ≡→* t₃, t₂ ≡→* t₃`.

The paper proves this by adapting Takahashi's parallel-reduction
technique (§6.5), deferring "full details" to the author's thesis [19].

**Status of the mechanization** (`Pss/Confluence.lean`):
* `Par` — Takahashi simultaneous reduction for the conditional system,
  with the SRE-APP guard `s ≤* a` carried in the `Par.beta` rule;
* proved: `Par.of_red` (`≡→ ⊆ Par`), `Par.to_redStar` (`Par ⊆ ≡→*`,
  guard transported along argument reduction by `ATSub.guard_left`),
  `Par.refl`, `Par.fill`, inversions for rigid terms;
* proved: `eqConfluent_of_parDiamond` — the diamond property of `Par`
  (`ParDiamond`) implies this statement, via the strip lemma
  (`parStrip`) and tiling (`parStar_confluent`);
* proved: the `Top(t)`-overlap diamond case (`parDiamond_topApp_case`);
* **open here**: `ParDiamond` itself. Its β/β and β/congruence overlaps
  need a parallel-substitution lemma (`Par` under `[x ↦ s]`-instantiation,
  for which the `≤*`-valued substitution `Pss.alg_subst` supplies the
  guard transport) and a parallel-narrowing lemma; both involve
  closedness side conditions on binder bounds (over the *all-terms*
  algorithmic system, function bodies with ill-scoped bounds admit no
  reductions, so the narrowing escape hatch is a `Par`-is-identity-or-
  context-prevalid dichotomy). Stated as a `Prop`, never an axiom. -/
def thm_6_1 : Prop := EqConfluent

end Statements

end Pss
