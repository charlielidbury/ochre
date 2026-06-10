import Pss.Semantic.Model
import Pss.Semantic.ModelLemmas
import Pss.Semantic.Conversion

/-!
# Per-rule soundness: the easy rules

§6 of `pss/docs/03-revised-proof.md` (Theorem 6.2's case analysis),
non-binder rules. Each `sound_*` lemma's hypotheses are **exactly** what
the corresponding `Instrumented` constructor's premises yield under the
fundamental theorem's motives —

- `CtxWfI Γ ↦ True` (dropped),
- `WfI Γ t ↦ SemWf Γ t`,
- `WellSubI Γ t r u ↦ SemWf Γ t ∧ SemWf Γ u ∧ SemRel r Γ t u`,
- `SubI Γ t r u ↦ SemRel r Γ t u`,

with syntactic side conditions (`x < Γ.length`, `Ctx.Bound Γ x t`)
passing through as themselves. `Fundamental.lean` applies these
verbatim; do not change a hypothesis without checking the constructor.

Several lemmas are already proven here (they are one-line compositions
of Model.lean's proven glue and phase-A statements); the sorried ones
are the genuine model arguments.
-/

namespace Pss.Semantic

open Term (Value)

/-- Every in-range index is bound: `x < |Γ| ⟹ ∃ t, Ctx.Bound Γ x t`.
Induction on `Γ` with cases on `x` (cf. `Ctx.Bound`'s `here`/`there`). -/
private theorem exists_bound {Γ : Ctx} {x : Nat} (hx : x < Γ.length) :
    ∃ t, Ctx.Bound Γ x t := by
  induction Γ generalizing x with
  | nil => exact absurd hx (by simp)
  | cons a Γ' ih =>
    cases x with
    | zero => exact ⟨a.shift 1, .here⟩
    | succ n =>
      obtain ⟨t', hb⟩ := ih (by simpa using Nat.lt_of_succ_lt_succ hx)
      exact ⟨t'.shift 1, .there hb⟩

/-- **W-VAR** (doc §6): `γx ∈ ⟦γx⟧ₖ` is the self-membership component of
the goodness of `γx` — a `Ctx.Bound` witness exists for every
`x < Γ.length`. Matches `WfI.var` (its `CtxWfI` premise is dropped). -/
theorem sound_wvar {Γ : Ctx} {x : Nat} (hx : x < Γ.length) :
    SemWf Γ (.var x) := by
  intro k γ hγ
  -- `(.var x).subst γ = γ x`; goal is `Mem k (γ x) (γ x)`.
  show Mem k (γ x) (γ x)
  -- Some `t` binds `x`; `SemCtx` at that bound gives `Good k (γt) (γx)`,
  -- whose self-membership component (second conjunct) is the goal.
  obtain ⟨t, hb⟩ := exists_bound hx
  have hg := hγ x t hb
  rw [Good_unfold] at hg
  exact hg.2.1

/-- **W-TOP** (doc §6): `Top ⇓⁰ Top`, `MATCH(Top, Top)`. Matches
`WfI.top`. -/
theorem sound_wtop {Γ : Ctx} : SemWf Γ .top := by
  intro k γ _
  -- `.top.subst γ = .top`; show `Mem k .top .top`.
  show Mem k .top .top
  rw [Mem_unfold]
  intro j v hj hconv
  -- `.top` is whnf, so the only convergence is `Converges 0 .top .top`.
  have htop : Converges 0 .top .top := ⟨.refl, whNormal_of_value .top⟩
  obtain ⟨hjeq, hveq⟩ := Converges.deterministic hconv htop
  subst hjeq; subst hveq
  refine ⟨.top, .top, ⟨0, htop⟩, .top, ?_⟩
  -- (m3) `Match k .top .top` is the left disjunct of `Match_unfold`.
  rw [Match_unfold]
  exact Or.inl rfl

/-- **DS-VAR** (doc §6): reflexivity at a variable. Matches `SubI.var`. -/
theorem sound_var {Γ : Ctx} {x : Nat} (hx : x < Γ.length) :
    SemEq Γ (.var x) (.var x) :=
  ⟨Beta.refl _, sound_wvar hx, sound_wvar hx⟩

/-- **DS-TOP** (doc §6): reflexivity at `Top`. Matches `SubI.top`. -/
theorem sound_top {Γ : Ctx} : SemEq Γ .top .top :=
  ⟨Beta.refl _, sound_wtop, sound_wtop⟩

/-- **DS-ETOP** (doc §6): everything's extension is included in `Top`'s
— a member's own (m1) makes its value a value, and `MATCH(v, Top)` is
free. Matches `SubI.etop` (the wf premise feeds Lemma 3.3). -/
theorem sound_etop {Γ : Ctx} {t : Term} (hwf : SemWf Γ t) :
    SemLe Γ t .top := by
  -- Lemma 3.3: the membership half follows from the inclusion half, which
  -- is `Mem k s .top` for any `s ∈ ⟦γt⟧ₖ` (doc §6 DS-ETOP).
  refine semLe_of_inclusion hwf (fun k γ _ s hs => ?_)
  show Mem k s .top
  rw [Mem_unfold]
  intro j v hj hconv
  -- (m1) `v` is a value, read off `s`'s own membership in `⟦γt⟧ₖ`.
  have hv : Value v := ((Mem_unfold.mp hs) j v hj hconv).1
  -- (m2) `.top ⇓⁰ .top`; (m3) `Match (k−j) v .top` = left disjunct.
  refine ⟨hv, .top, ⟨0, .refl, whNormal_of_value .top⟩, .top, ?_⟩
  rw [Match_unfold]
  exact Or.inl rfl

/-- **DS-EQ** (doc §6): conversion gives the set *equality* of
extensions (Lemma 4.4 after `Beta.subst`), hence both halves via
Lemma 3.3. Matches `SubI.eq`. -/
theorem sound_eq {Γ : Ctx} {t u : Term} (h : SemEq Γ t u) :
    SemLe Γ t u :=
  semLe_of_inclusion h.2.1 fun _ γ _ _ hs =>
    (mem_beta_type (Beta.subst γ h.1)).mp hs

/-- **DS-SYM** (doc §6): symmetric in `=β` and wf. Matches `SubI.symm`. -/
theorem sound_sym {Γ : Ctx} {t u : Term} (h : SemEq Γ u t) :
    SemEq Γ t u :=
  SemEq.symm h

/-- **DS-TRANS, ≡-form** (doc §6): `=β` and wf both compose. The ≤-form
is Theorem 5.1 (`SemLe.trans`), proven in `Model.lean`. Matches
`SubI.trans` at `r = .eq` (the middle's wf premise is dropped — doc:
"not even needed semantically"). -/
theorem sound_trans_eq {Γ : Ctx} {s t u : Term}
    (h₁ : SemEq Γ s t) (h₂ : SemEq Γ t u) : SemEq Γ s u :=
  SemEq.trans h₁ h₂

/-- **DS-EAPP** (doc §6): one β-step; both endpoints' wf are the
instrumented premises. Matches `SubI.eapp`. -/
theorem sound_eapp {Γ : Ctx} {t u s : Term}
    (h₁ : SemWf Γ (.app (.lam t u) s)) (h₂ : SemWf Γ (u.subst1 s)) :
    SemEq Γ (.app (.lam t u) s) (u.subst1 s) :=
  ⟨Beta.of_step .eapp, h₁, h₂⟩

/-- **DS-EVAR** (doc §6): both halves are read directly off the goodness
of `γx` — membership is its first component, the inclusion is its
third at `i = k`. *This is precisely where storing inclusions in
goodness breaks the circularity* (doc: deriving the inclusion from the
membership would itself be a transitivity argument). Matches
`SubI.evar` (its `CtxWfI` premise is dropped). -/
theorem sound_evar {Γ : Ctx} {x : Nat} {t : Term}
    (hb : Ctx.Bound Γ x t) : SemLe Γ (.var x) t := by
  intro k γ hγ
  have hg := hγ x t hb
  rw [Good_unfold] at hg
  exact ⟨hg.1, fun s hs => hg.2.2 k s (Nat.le_refl k) hs⟩

end Pss.Semantic
