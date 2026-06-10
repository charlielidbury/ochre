import Pss.Reduction
import Pss.Declarative
import Pss.Induction
import Pss.Basic
import Pss.Weakening
import Pss.Substitution

/-!
# Type safety for System λ⊲ (§5, p. 293)

Statements 5.1–5.6 of Hutchins, *Pure Subtype Systems* (POPL 2010).

* Conjecture 5.1 (transitivity elimination) — stated as a `Prop`
  (`TransitivityElimination`), **not** assumed.
* Lemma 5.2 (inversion of subtyping, declarative version) — proved from 5.1.
* Lemma 5.3 (reduction implies equivalence) — proved outright.
* Theorem 5.5 (progress) and Theorem 5.6 (preservation) — proved from 5.1,
  exactly as in the paper ("System λ⊲ is type-safe so long as subtyping has
  the transitivity elimination property").
-/

namespace Pss

/-! ## Conjecture 5.1 — transitivity elimination -/

/-- **Conjecture 5.1 (Transitivity elimination)**, p. 293:

> If `Γ ⊢ v ≤wf w`, then there exists a proof of `Γ ⊢ v ≤ w` that ends in
> either (DS-FUN) or (DS-ETOP).

A derivation ending in (DS-ETOP) forces `w = Top`; one ending in (DS-FUN)
forces both sides to be λ-abstractions and exposes the rule's premises
`Γ ⊢ t ≡ t'` and `Γ, x ≤ t ⊢ u ≤ u'`. (`v`, `w` range over *values*, the
only well-formed normal forms relevant for safety.)

This is an **open problem** — the paper's §6 program (confluence of `≡→`
plus commutativity of `≤→` and `≡→`, Lemma 6.3) targets it but is itself
incomplete (§6.6). We therefore state it as a definition of type `Prop`
and thread it as an explicit hypothesis through Lemma 5.2, Theorem 5.5 and
Theorem 5.6, never as an axiom. -/
def TransitivityElimination : Prop :=
  ∀ Γ (v w : Term), Term.Value v → Term.Value w → WellSub Γ v .le w →
    w = .top ∨
    ∃ t u t' u', v = .lam t u ∧ w = .lam t' u' ∧
      Sub Γ t .eq t' ∧ Sub (t :: Γ) u .le u'

/-! ## Lemma 5.2 — inversion of subtyping (declarative version) -/

/-- **Lemma 5.2 (Inversion of subtyping — declarative version)**, p. 293:

> If `Γ ⊢ (λx ≤ t. u) ≤wf (λx ≤ t'. u')` then `Γ ⊢ t ≡ t'`.

Proved from Conjecture 5.1 (transitivity elimination), exactly as in the
paper: a λ-abstraction is a value, and `λx ≤ t'. u' ≠ Top` rules out the
(DS-ETOP) disjunct, so the derivation ends in (DS-FUN) whose first premise
is the conclusion. -/
theorem Sub.inversion (te : TransitivityElimination) {Γ : Ctx}
    {t u t' u' : Term} (h : WellSub Γ (.lam t u) .le (.lam t' u')) :
    Sub Γ t .eq t' := by
  rcases te Γ _ _ (.lam t u) (.lam t' u') h with htop | ⟨a, b, a', b', hv, hw, h1, _⟩
  · cases htop
  · cases hv; cases hw; exact h1

/-! ## Lemma 5.3 — reduction implies equivalence -/

/-- **Lemma 5.3 (Reduction implies equivalence)**, p. 293:

> If `t ⟶ t'`, then `Γ ⊢ t ≡ t'`.

By induction on the derivation of `t ⟶ t'` (via the compatible-closure
presentation `Step.Compat`): the base case is rule (DS-EAPP); the
congruence cases are (DS-APP) and (DS-FUN) with reflexivity
(`Sub.refl_eq`) on the unchanged side. -/
theorem Step.to_sub_eq {t t' : Term} (h : Step t t') :
    ∀ Γ : Ctx, Sub Γ t .eq t' := by
  have h' := Step.step_iff_compat.mp h
  clear h
  induction h' with
  | eapp => exact fun Γ => .eapp
  | appL u _ ih => exact fun Γ => .app (ih Γ) (Sub.refl_eq u Γ)
  | appR t _ ih => exact fun Γ => .app (Sub.refl_eq t Γ) (ih Γ)
  | lamBound u _ ih => exact fun Γ => .fn (ih Γ) (Sub.refl_eq u _)
  | lamBody t _ ih => exact fun Γ => .fn (Sub.refl_eq t Γ) (ih _)

/-! ## Theorem 5.5 — progress -/

/-- **Theorem 5.5 (Progress)**, p. 293:

> If `∅ ⊢ t wf` then either `t = v` for some `v` (i.e. `t` is a value), or
> there exists a `t'` such that `t ⟶ t'`.

By induction on the derivation of `t wf`. The hypothesis
`TransitivityElimination` (Conjecture 5.1) is needed in exactly one place:
in the application case `t(u)`, when the function part is the value `Top`,
the well-formedness premise `∅ ⊢ Top ≤wf λx ≤ s. Top` must be refuted —
transitivity elimination forces such a derivation to end in (DS-ETOP)
(impossible: `λx ≤ s. Top ≠ Top`) or (DS-FUN) (impossible: `Top` is not a
λ-abstraction). Without 5.1, a derivation built from DS-TRANS chains cannot
be ruled out and `Top(u)` would be stuck. When the function part is a
λ-abstraction, (E-APP) fires unconditionally (no value or typing condition
on the argument). -/
theorem progress (te : TransitivityElimination) {t : Term}
    (h : Wf [] t) : Term.Value t ∨ ∃ t', Step t t' := by
  have H := decl_induction
    (motC := fun _ => True)
    (motW := fun Γ u => Γ = [] → Term.Value u ∨ ∃ u', Step u u')
    (motWS := fun Γ u _ _ => Γ = [] → Term.Value u ∨ ∃ u', Step u u')
    (motS := fun _ _ _ _ => True)
    (ctx_nil := trivial)
    (ctx_cons := fun _ _ _ _ => trivial)
    (wf_var := fun _ hx _ hΓ => by subst hΓ; simp at hx)
    (wf_top := fun _ _ _ => .inl .top)
    (wf_fn := fun _ _ _ => .inl (.lam _ _))
    (wf_app := fun {Γ a u s} h1 _ ih1 _ hΓ => by
      subst hΓ
      rcases ih1 rfl with hv | ⟨a2, hstep⟩
      · cases hv with
        | top =>
          rcases te [] .top (.lam s .top) .top (.lam s .top) h1 with
            htop | ⟨w1, w2, w3, w4, hveq, _, _, _⟩
          · cases htop
          · cases hveq
        | lam c d => exact .inr ⟨d.subst1 u, .eapp⟩
      · exact .inr ⟨.app a2 u, Step.appL u hstep⟩)
    (wsub_sub := fun _ _ _ ihW _ _ => ihW)
    (sub_trans := fun _ _ _ _ _ _ => trivial)
    (sub_symm := fun _ _ => trivial)
    (sub_eq := fun _ _ => trivial)
    (sub_var := trivial)
    (sub_top := trivial)
    (sub_fn := fun _ _ _ _ => trivial)
    (sub_app := fun _ _ _ _ => trivial)
    (sub_eapp := trivial)
    (sub_etop := trivial)
    (sub_evar := fun _ => trivial)
  exact H.2.1 [] t h rfl

/-! ## Theorem 5.6 — preservation

The paper's proof has two parts: (1) subject reduction for the subtyping
half, which follows from Lemma 5.3 and DS-TRANS; (2) preservation of
well-formedness, by induction on the well-formedness derivation with case
analysis on where the step occurred. -/

/-! ### Step and well-formedness inversions -/

theorem Step.not_var {x : Nat} {t' : Term} (h : Step (.var x) t') : False := by
  cases Step.step_iff_compat.mp h

theorem Step.not_top {t' : Term} (h : Step .top t') : False := by
  cases Step.step_iff_compat.mp h

/-- A step from `λx ≤ a. b` is a step in the bound or in the body. -/
theorem Step.lam_inv {a b c : Term} (h : Step (.lam a b) c) :
    (∃ a', c = .lam a' b ∧ Step a a') ∨ (∃ b', c = .lam a b' ∧ Step b b') := by
  cases Step.step_iff_compat.mp h with
  | lamBound u hc => exact .inl ⟨_, rfl, Step.step_iff_compat.mpr hc⟩
  | lamBody t hc => exact .inr ⟨_, rfl, Step.step_iff_compat.mpr hc⟩

/-- A step from `f(u)` is the β-redex or a step in either component. -/
theorem Step.app_inv {f u c : Term} (h : Step (.app f u) c) :
    (∃ a b, f = .lam a b ∧ c = b.subst1 u)
    ∨ (∃ f', c = .app f' u ∧ Step f f')
    ∨ (∃ u', c = .app f u' ∧ Step u u') := by
  cases Step.step_iff_compat.mp h with
  | eapp => exact .inl ⟨_, _, rfl, rfl⟩
  | appL u hc => exact .inr (.inl ⟨_, rfl, Step.step_iff_compat.mpr hc⟩)
  | appR t hc => exact .inr (.inr ⟨_, rfl, Step.step_iff_compat.mpr hc⟩)

/-- Inversion of W-FUN. -/
theorem Wf.lam_inv {Γ : Ctx} {a b : Term} (h : Wf Γ (.lam a b)) :
    Wf (a :: Γ) b := by
  cases h with | fn h => exact h

/-- Inversion of W-APP. -/
theorem Wf.app_inv {Γ : Ctx} {f u : Term} (h : Wf Γ (.app f u)) :
    ∃ s, WellSub Γ f .le (.lam s .top) ∧ WellSub Γ u .le s := by
  cases h with | app h1 h2 => exact ⟨_, h1, h2⟩

/-- The left-hand side of a well-subtyping is well-formed (W-SUB inversion). -/
theorem WellSub.wf_left {Γ : Ctx} {t u : Term} {r : Rel}
    (h : WellSub Γ t r u) : Wf Γ t := by
  cases h with | sub h _ _ => exact h

/-- The right-hand side of a well-subtyping is well-formed (W-SUB inversion). -/
theorem WellSub.wf_right {Γ : Ctx} {t u : Term} {r : Rel}
    (h : WellSub Γ t r u) : Wf Γ u := by
  cases h with | sub _ h _ => exact h

/-- The subtyping component of a well-subtyping (W-SUB inversion). -/
theorem WellSub.to_sub {Γ : Ctx} {t u : Term} {r : Rel}
    (h : WellSub Γ t r u) : Sub Γ t r u := by
  cases h with | sub _ _ h => exact h

/-! ### Part 1: subject reduction for well-subtyping -/

/-- **Theorem 5.6, part 1**: if `Γ ⊢ t ⊲wf u` and `t ⟶ t'` then
`Γ ⊢ t' ⊲wf u`, *given* preservation of well-formedness (part 2, proved
conditionally below). Exactly the paper's argument: by Lemma 5.3
(reduction implies equivalence) `t ≡ t'`, hence `t' ⊲ t` by DS-SYM (and
DS-EQ at `≤`), and `t' ⊲ u` follows by DS-TRANS — whose middle-term
well-formedness premise `Γ ⊢ t wf` is the hypothesis's own left
well-formedness. -/
theorem WellSub.preservation_of_wf_preservation
    (hwf : ∀ (Γ : Ctx) (a a' : Term), Wf Γ a → Step a a' → Wf Γ a')
    {Γ : Ctx} {t t' u : Term} {r : Rel}
    (h : WellSub Γ t r u) (hs : Step t t') : WellSub Γ t' r u := by
  cases h with
  | sub hW1 hW2 hSub =>
    have heq : Sub Γ t' .eq t := (hs.to_sub_eq Γ).symm
    exact .sub (hwf Γ t t' hW1 hs) hW2 (.trans (heq.of_eq r) hSub hW1)

/-! ### Part 2: preservation of well-formedness -/

namespace Statements

/-- **Context conversion (narrowing)**, used by the paper's Theorem 5.6 in
the bound-step case `λx ≤ a. b` with `a ⟶ a'`: a judgment under `x ≤ a`
transports to `x ≤ a'` when `Γ ⊢ a' ≡ a` and `a'` is well-formed.

**Status: open**, blocked by the same obstruction as Lemma 5.4
(`Statements.SubstitutionLemma`): at a DS-EVAR leaf for the converted
variable one must weaken `Γ ⊢ a' ≤ a` and the middle-term well-formedness
of a DS-TRANS into the local context, but DS-FUN extends contexts with
arbitrary, possibly ill-formed bounds, into which neither `Sub` nor `Wf`
weakening is derivable by rule induction. -/
def Narrowing : Prop :=
  ∀ (Γ : Ctx) (a a' u : Term), Sub Γ a' .eq a → Wf Γ a' →
    Wf (a :: Γ) u → Wf (a' :: Γ) u

end Statements

/-- **Theorem 5.6, redex case**: the paper's "most interesting case".
If `(λx ≤ a. b)(c)` is well-formed then so is `[x ↦ c]b`. The two premises
of well-formedness are `λx ≤ a. b ≤wf λx ≤ a'. Top` and `c ≤wf a'`; Lemma
5.2 (inversion, from Conjecture 5.1) gives `a ≡ a'`, DS-TRANS gives
`c ≤wf a`, and the substitution transport (`subst_transport`, the proved
content of Lemma 5.4) finishes — its hypothesis family discharged by
`SubShiftWeakening`. -/
theorem wf_redex (te : TransitivityElimination) (hw : SubShiftWeakening)
    {Γ : Ctx} {a b u : Term} (h : Wf Γ (.app (.lam a b) u)) :
    Wf Γ (b.subst1 u) := by
  obtain ⟨s, h1, h2⟩ := h.app_inv
  have hb : Wf (a :: Γ) b := h1.wf_left.lam_inv
  have hinv : Sub Γ a .eq s := Sub.inversion te h1
  have hua : Sub Γ u .le a := .trans h2.to_sub (Sub.eq hinv.symm) h2.wf_right
  exact (subst_transport h2.wf_left (fun Ξ' => hw Γ u a Ξ' hua)).2.1
    (a :: Γ) b hb [] rfl

/-- **Theorem 5.6, part 2** (preservation of well-formedness), conditional
on the two open structural lemmas: if `Γ ⊢ t wf` and `t ⟶ t'` then
`Γ ⊢ t' wf`. By induction on the term with case analysis on where the step
occurred: the redex case is `wf_redex` (Lemma 5.2 + Lemma 5.4); a step in a
λ-bound needs `Narrowing`; all congruence cases re-derive the W-APP
premises via Lemma 5.3 + DS-TRANS. -/
theorem wf_preservation_of (te : TransitivityElimination)
    (hw : SubShiftWeakening) (hnar : Statements.Narrowing) :
    ∀ (t : Term) {Γ : Ctx} {t' : Term}, Wf Γ t → Step t t' → Wf Γ t' := by
  intro t
  induction t with
  | var x => intro Γ t' _ hs; exact hs.not_var.elim
  | top => intro Γ t' _ hs; exact hs.not_top.elim
  | lam a b iha ihb =>
    intro Γ t' hW hs
    have hb : Wf (a :: Γ) b := hW.lam_inv
    rcases hs.lam_inv with ⟨a', rfl, hsa⟩ | ⟨b', rfl, hsb⟩
    · have ha' : Wf Γ a' := iha hb.ctxWf.head_wf hsa
      exact .fn (hnar Γ a a' b (hsa.to_sub_eq Γ).symm ha' hb)
    · exact .fn (ihb hb hsb)
  | app f u ihf ihu =>
    intro Γ t' hW hs
    obtain ⟨s, h1, h2⟩ := hW.app_inv
    rcases hs.app_inv with ⟨a, b, rfl, rfl⟩ | ⟨f', rfl, hsf⟩ | ⟨u', rfl, hsu⟩
    · exact wf_redex te hw hW
    · have h1' : WellSub Γ f' .le (.lam s .top) :=
        .sub (ihf h1.wf_left hsf) h1.wf_right
          (.trans ((hsf.to_sub_eq Γ).symm.of_eq .le) h1.to_sub h1.wf_left)
      exact .app h1' h2
    · have h2' : WellSub Γ u' .le s :=
        .sub (ihu h2.wf_left hsu) h2.wf_right
          (.trans ((hsu.to_sub_eq Γ).symm.of_eq .le) h2.to_sub h2.wf_left)
      exact .app h1 h2'

namespace Statements

/-- **Theorem 5.6 (Preservation)**, p. 293:

> If `Γ ⊢ t ≤wf u` and `t ⟶ t'` then `Γ ⊢ t' ≤wf u`.

(`⊲` generalized over both relations, with the well-formedness half — the
paper's part 2 — alongside, since the proof needs them jointly.) Stated
under Conjecture 5.1, as the whole of §5 is.

**Status: partially proved.** Part 1 is fully proved relative to part 2
(`WellSub.preservation_of_wf_preservation` — Lemma 5.3 + DS-SYM/DS-EQ +
DS-TRANS, with the middle well-formedness from the hypothesis). Part 2 is
proved (`wf_preservation_of`, including the paper's "most interesting"
redex case via `wf_redex`) conditional on the two open structural lemmas:
`SubShiftWeakening` (the isolated gap of Lemma 5.4, used in the redex
case) and `Narrowing` (used when the step is inside a λ-bound). So
`preservation_of_assumptions` below reduces this statement to those two
assumptions; neither is derivable by rule induction from Figure 1 (see
their docstrings), and Conjecture 5.1 (values only) does not supply them. -/
def Preservation : Prop :=
  TransitivityElimination →
    ∀ (Γ : Ctx) (t t' u : Term) (r : Rel),
      (WellSub Γ t r u → Step t t' → WellSub Γ t' r u)
      ∧ (Wf Γ t → Step t t' → Wf Γ t')

end Statements

/-- Theorem 5.6 holds given the two open structural lemmas: shift
weakening of `≤` into arbitrary extensions (the Lemma 5.4 gap) and
narrowing. Both halves of the paper's statement. -/
theorem preservation_of_assumptions (hw : SubShiftWeakening)
    (hnar : Statements.Narrowing) : Statements.Preservation := by
  intro te Γ t t' u r
  refine ⟨fun h hs => ?_, fun h hs => wf_preservation_of te hw hnar t h hs⟩
  exact h.preservation_of_wf_preservation
    (fun Γ a a' hW hsa => wf_preservation_of te hw hnar a hW hsa) hs

end Pss
