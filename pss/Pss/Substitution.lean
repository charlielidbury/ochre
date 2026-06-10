import Pss.Declarative
import Pss.Induction
import Pss.Basic
import Pss.Weakening

/-!
# Substitution for the declarative system (§5, Lemma 5.4)

De Bruijn rendering of the paper's `[x ↦ t']` acting at position `|Ξ|`:
`sigmaAt n t'` substitutes `t'` for variable `n` (suitably shifted) and
lowers all higher variables by one; `Ctx.substAt` applies it pointwise to a
context suffix. The transport theorem and the Lemma 5.4 statement follow in
the second half of this file.
-/

namespace Pss

/-! ## The single-variable substitution at depth `n` -/

/-- `sigmaAt n t'` is the paper's `[x ↦ t']` for the variable at de Bruijn
index `n`: variables `< n` are untouched, variable `n` becomes `t'.shift n`,
and variables `> n` are lowered by one. `sigmaAt 0 t'` is `Term.subst1`'s
substitution. -/
def sigmaAt : Nat → Term → Nat → Term
  | 0, t' => Term.scons t' Term.var
  | n + 1, t' => Term.liftSubst (sigmaAt n t')

theorem sigmaAt_lt {n x : Nat} (t' : Term) (h : x < n) :
    sigmaAt n t' x = .var x := by
  induction n generalizing x with
  | zero => omega
  | succ n ih =>
    cases x with
    | zero => rfl
    | succ x =>
      show (sigmaAt n t' x).rename _ = _
      rw [ih (by omega)]
      rfl

theorem sigmaAt_self (n : Nat) (t' : Term) :
    sigmaAt n t' n = t'.shift n := by
  induction n with
  | zero => exact (Term.shift_zero t').symm
  | succ n ih =>
    show (sigmaAt n t' n).rename _ = _
    rw [ih]
    exact Term.shift_shift t' n

theorem sigmaAt_gt {n y : Nat} (t' : Term) (h : n ≤ y) :
    sigmaAt n t' (y + 1) = .var y := by
  induction n generalizing y with
  | zero => rfl
  | succ n ih =>
    cases y with
    | zero => omega
    | succ y =>
      show (sigmaAt n t' (y + 1)).rename _ = _
      rw [ih (by omega)]
      rfl

/-- Substituting under one shift skips the shifted binder:
`(↑b).subst (⇑σ) = ↑(b.subst σ)`. -/
theorem Term.shift_subst_lift (σ : Nat → Term) (b : Term) :
    (b.shift 1).subst (Term.liftSubst σ) = (b.subst σ).shift 1 := by
  show (b.rename _).subst _ = (b.subst _).rename _
  rw [Term.subst_rename, Term.rename_subst]
  congr 1

/-- A term shifted past the substituted variable is merely unshifted by one:
`(b.shift (n+1)).subst (sigmaAt n t') = b.shift n`. -/
theorem subst_sigmaAt_shift (b t' : Term) (n : Nat) :
    (b.shift (n + 1)).subst (sigmaAt n t') = b.shift n := by
  show (b.rename _).subst _ = b.rename _
  rw [Term.subst_rename, Term.rename_eq_subst]
  congr 1
  funext x
  show sigmaAt n t' (x + (n + 1)) = .var (x + n)
  have h : x + (n + 1) = (x + n) + 1 := by omega
  rw [h, sigmaAt_gt t' (by omega)]

/-! ## Pointwise substitution in a context suffix -/

/-- `[x ↦ t']Γ'` (Lemma 5.4): substitute pointwise in the context suffix
inside the binding being eliminated. Entry `u` at depth `|Ξ|` from the
binding is scoped in its own tail, so it is substituted at that depth. -/
def Ctx.substAt (t' : Term) : Ctx → Ctx
  | [] => []
  | u :: Ξ => u.subst (sigmaAt Ξ.length t') :: Ctx.substAt t' Ξ

@[simp] theorem Ctx.substAt_length (t' : Term) (Ξ : Ctx) :
    (Ctx.substAt t' Ξ).length = Ξ.length := by
  induction Ξ with
  | nil => rfl
  | cons u Ξ ih => simp [Ctx.substAt, ih]

/-! ## Bound transport along `substAt` -/

/-- The bound of the variable being substituted is the marker entry itself:
`|Ξ| ≤ t ∈ Ξ ++ t :: Γ₀`, shifted into whole-context scope. -/
theorem Ctx.bound_at_split {Ξ Γ₀ : Ctx} {t b : Term}
    (h : Ctx.Bound (Ξ ++ t :: Γ₀) Ξ.length b) : b = t.shift (Ξ.length + 1) := by
  induction Ξ generalizing b with
  | nil => cases h with | here => rfl
  | cons s Ξ ih =>
    cases h with
    | there h' =>
      rw [ih h', Term.shift_shift]
      rfl

/-- Bounds of variables inside `Ξ` transport pointwise. -/
theorem Ctx.bound_substAt_lt {Ξ Γ₀ : Ctx} {t b t' : Term} {x : Nat}
    (h : Ctx.Bound (Ξ ++ t :: Γ₀) x b) (hx : x < Ξ.length) :
    Ctx.Bound (Ctx.substAt t' Ξ ++ Γ₀) x (b.subst (sigmaAt Ξ.length t')) := by
  induction Ξ generalizing x b with
  | nil => simp at hx
  | cons s Ξ ih =>
    cases h with
    | here =>
      show Ctx.Bound _ 0 ((s.shift 1).subst (Term.liftSubst _))
      rw [Term.shift_subst_lift]
      exact .here
    | there h' =>
      rename_i b' x'
      show Ctx.Bound _ (x' + 1) ((b'.shift 1).subst (Term.liftSubst _))
      rw [Term.shift_subst_lift]
      exact .there (ih h' (by simp at hx; omega))

/-- Bounds of variables outside the binding lower by one. -/
theorem Ctx.bound_substAt_gt {Ξ Γ₀ : Ctx} {t b t' : Term} {y : Nat}
    (h : Ctx.Bound (Ξ ++ t :: Γ₀) (y + 1) b) (hy : Ξ.length ≤ y) :
    Ctx.Bound (Ctx.substAt t' Ξ ++ Γ₀) y (b.subst (sigmaAt Ξ.length t')) := by
  induction Ξ generalizing y b with
  | nil =>
    cases h with
    | there h' =>
      rename_i b'
      show Ctx.Bound Γ₀ y ((b'.shift 1).subst1 t')
      rw [Term.shift_subst1 b' t']
      exact h'
  | cons s Ξ ih =>
    cases y with
    | zero => simp at hy
    | succ y =>
      cases h with
      | there h' =>
        rename_i b'
        show Ctx.Bound _ (y + 1) ((b'.shift 1).subst (Term.liftSubst _))
        rw [Term.shift_subst_lift]
        exact .there (ih h' (by simp at hy; omega))

/-! ## The substitution transport theorem

The inductive content of Lemma 5.4, proved relative to a *shift-transport
family* for the hypothesis `t' ≤ t`: rule DS-FUN extends contexts with
arbitrary (possibly ill-formed) bounds, and weakening `Γ₀ ⊢ t' ≤ t` into
such extensions is exactly the obligation that cannot be discharged from
Figure 1 alone (see `Pss.Statements.SubstitutionLemma`). Everything else —
all four judgments, all seventeen rules — goes through. -/

theorem subst_transport {Γ₀ : Ctx} {t t' : Term}
    (hWt' : Wf Γ₀ t')
    (HS : ∀ Ξ' : Ctx, Sub (Ξ' ++ Γ₀) (t'.shift Ξ'.length) .le (t.shift Ξ'.length)) :
    (∀ Γ', CtxWf Γ' → ∀ Ξ, Γ' = Ξ ++ t :: Γ₀ →
      CtxWf (Ctx.substAt t' Ξ ++ Γ₀))
    ∧ (∀ Γ' u, Wf Γ' u → ∀ Ξ, Γ' = Ξ ++ t :: Γ₀ →
      Wf (Ctx.substAt t' Ξ ++ Γ₀) (u.subst (sigmaAt Ξ.length t')))
    ∧ (∀ Γ' u r v, WellSub Γ' u r v → ∀ Ξ, Γ' = Ξ ++ t :: Γ₀ →
      WellSub (Ctx.substAt t' Ξ ++ Γ₀) (u.subst (sigmaAt Ξ.length t')) r
        (v.subst (sigmaAt Ξ.length t')))
    ∧ (∀ Γ' u r v, Sub Γ' u r v → ∀ Ξ, Γ' = Ξ ++ t :: Γ₀ →
      Sub (Ctx.substAt t' Ξ ++ Γ₀) (u.subst (sigmaAt Ξ.length t')) r
        (v.subst (sigmaAt Ξ.length t'))) :=
  decl_induction
    (motC := fun Γ' => ∀ Ξ, Γ' = Ξ ++ t :: Γ₀ →
      CtxWf (Ctx.substAt t' Ξ ++ Γ₀))
    (motW := fun Γ' u => ∀ Ξ, Γ' = Ξ ++ t :: Γ₀ →
      Wf (Ctx.substAt t' Ξ ++ Γ₀) (u.subst (sigmaAt Ξ.length t')))
    (motWS := fun Γ' u r v => ∀ Ξ, Γ' = Ξ ++ t :: Γ₀ →
      WellSub (Ctx.substAt t' Ξ ++ Γ₀) (u.subst (sigmaAt Ξ.length t')) r
        (v.subst (sigmaAt Ξ.length t')))
    (motS := fun Γ' u r v => ∀ Ξ, Γ' = Ξ ++ t :: Γ₀ →
      Sub (Ctx.substAt t' Ξ ++ Γ₀) (u.subst (sigmaAt Ξ.length t')) r
        (v.subst (sigmaAt Ξ.length t')))
    (ctx_nil := fun Ξ hEq => by cases Ξ <;> cases hEq)
    (ctx_cons := fun hC hW ihC ihW Ξ hEq => by
      cases Ξ with
      | nil => cases hEq; exact hC
      | cons s Ξ => cases hEq; exact .cons (ihC Ξ rfl) (ihW Ξ rfl))
    (wf_var := fun {Γ' x} hC hx ihC Ξ hEq => by
      subst hEq
      have hlen : (Ctx.substAt t' Ξ ++ Γ₀).length = Ξ.length + Γ₀.length := by
        simp
      have hx' : x < Ξ.length + (Γ₀.length + 1) := by simpa using hx
      show Wf _ (sigmaAt Ξ.length t' x)
      by_cases h1 : x < Ξ.length
      · rw [sigmaAt_lt t' h1]
        exact .var (ihC Ξ rfl) (by omega)
      · by_cases h2 : x = Ξ.length
        · subst h2
          rw [sigmaAt_self]
          have h := Wf.weaken_append (Ctx.substAt t' Ξ) (ihC Ξ rfl) hWt'
          rwa [Ctx.substAt_length] at h
        · obtain ⟨y, rfl⟩ : ∃ y, x = y + 1 := ⟨x - 1, by omega⟩
          rw [sigmaAt_gt t' (by omega)]
          exact .var (ihC Ξ rfl) (by omega))
    (wf_top := fun hC ihC Ξ hEq => by
      subst hEq; exact .top (ihC Ξ rfl))
    (wf_fn := fun {Γ' a u} _ ihW Ξ hEq => by
      subst hEq
      exact Wf.fn (ihW (a :: Ξ) rfl))
    (wf_app := fun _ _ ihWS1 ihWS2 Ξ hEq => by
      subst hEq
      exact .app (ihWS1 Ξ rfl) (ihWS2 Ξ rfl))
    (wsub_sub := fun _ _ _ ihW1 ihW2 ihS Ξ hEq => by
      subst hEq
      exact .sub (ihW1 Ξ rfl) (ihW2 Ξ rfl) (ihS Ξ rfl))
    (sub_trans := fun _ _ _ ih1 ih2 ihW Ξ hEq => by
      subst hEq
      exact .trans (ih1 Ξ rfl) (ih2 Ξ rfl) (ihW Ξ rfl))
    (sub_symm := fun _ ih Ξ hEq => .symm (ih Ξ hEq))
    (sub_eq := fun _ ih Ξ hEq => .eq (ih Ξ hEq))
    (sub_var := fun Ξ hEq => Sub.refl_eq _ _)
    (sub_top := fun Ξ hEq => .top)
    (sub_fn := fun {Γ' a a' u u' r} _ _ ih1 ih2 Ξ hEq => by
      subst hEq
      exact Sub.fn (ih1 Ξ rfl) (ih2 (a :: Ξ) rfl))
    (sub_app := fun _ _ ih1 ih2 Ξ hEq => by
      subst hEq
      exact .app (ih1 Ξ rfl) (ih2 Ξ rfl))
    (sub_eapp := fun Ξ hEq => by
      subst hEq
      rw [Term.subst_subst1]
      exact .eapp)
    (sub_etop := fun Ξ hEq => .etop)
    (sub_evar := fun {Γ' x b} hb Ξ hEq => by
      subst hEq
      show Sub _ (sigmaAt Ξ.length t' x) .le _
      by_cases h1 : x < Ξ.length
      · rw [sigmaAt_lt t' h1]
        exact .evar (Ctx.bound_substAt_lt hb h1)
      · by_cases h2 : x = Ξ.length
        · subst h2
          rw [sigmaAt_self, Ctx.bound_at_split hb, subst_sigmaAt_shift]
          have h := HS (Ctx.substAt t' Ξ)
          rwa [Ctx.substAt_length] at h
        · obtain ⟨y, rfl⟩ : ∃ y, x = y + 1 := ⟨x - 1, by omega⟩
          rw [sigmaAt_gt t' (by omega)]
          exact .evar (Ctx.bound_substAt_gt hb (by omega)))

/-! ## Lemma 5.4 -/

/-- Shift-transport for declarative `≤` along *arbitrary* context
extensions: the missing ingredient between `subst_transport` and Lemma 5.4.
For well-formed extensions this is `weakening_insertAt` (iterated); the
general form cannot be proved by rule induction because DS-TRANS's premise
`Γ ⊢ t wf` does not transport into ill-formed extensions (any `Wf Γ' m`
forces `CtxWf Γ'` — `Wf.ctxWf`). It would follow from transitivity
elimination for arbitrary terms, which is strictly stronger than
Conjecture 5.1 (stated for values only). -/
def SubShiftWeakening : Prop :=
  ∀ (Γ : Ctx) (s u : Term) (Ξ : Ctx), Sub Γ s .le u →
    Sub (Ξ ++ Γ) (s.shift Ξ.length) .le (u.shift Ξ.length)

namespace Statements

/-- **Lemma 5.4 (Substitution)**, p. 293:

> If `Γ, x ≤ t, Γ' ⊢ u ⊲wf s` and `Γ ⊢ t' ≤wf t`
> then `Γ, [x ↦ t']Γ' ⊢ [x ↦ t']u ⊲wf [x ↦ t']s`.

De Bruijn rendering: the suffix `Γ'` is `Ξ`, substitution acts at index
`|Ξ|` in the terms (`sigmaAt`) and pointwise in the suffix (`Ctx.substAt`).

**Status: open.** The entire rule-by-rule content is proved
(`subst_transport`): every `x wf` leaf becomes `t' wf`
(via `Wf.weaken_append`), every `x ≤ t` leaf (DS-EVAR) becomes the
transported hypothesis `t' ≤ t`, and DS-TRANS's `Wf` premise rides the
mutual induction, exactly as the paper's proof sketch says. The single gap
is the transport of the hypothesis `Γ ⊢ t' ≤ t` into the contexts at which
DS-EVAR fires: DS-FUN extends contexts with arbitrary — possibly
ill-formed — bounds, and weakening a `Sub` derivation into an ill-formed
extension cannot be proved by rule induction (DS-TRANS's well-formedness
premise does not transport; see `SubShiftWeakening`). The paper's proof
sketch silently assumes this weakening. `substitution_of_subShiftWeakening`
closes the lemma from that single assumption. -/
def SubstitutionLemma : Prop :=
  ∀ (Γ : Ctx) (t t' : Term) (Ξ : Ctx) (u s : Term) (r : Rel),
    WellSub (Ξ ++ t :: Γ) u r s →
    WellSub Γ t' .le t →
    WellSub (Ctx.substAt t' Ξ ++ Γ) (u.subst (sigmaAt Ξ.length t')) r
      (s.subst (sigmaAt Ξ.length t'))

end Statements

/-- Lemma 5.4 follows from shift weakening of `≤` into arbitrary
extensions; all other content is `subst_transport`. -/
theorem substitution_of_subShiftWeakening (hw : SubShiftWeakening) :
    Statements.SubstitutionLemma := by
  intro Γ t t' Ξ u s r h ht'
  cases ht' with
  | sub hWt' _ hSub =>
    exact (subst_transport hWt' (fun Ξ' => hw Γ t' t Ξ' hSub)).2.2.1
      _ u r s h Ξ rfl

/-- **Lemma 5.4, unconditionally, for `Top`-bounded binders**: when the
eliminated binding is `x ≤ Top`, the hypothesis family of
`subst_transport` is discharged outright by DS-ETOP (`t'.shift ≤ Top` in
*any* context, well-formed or not), so this instance of the substitution
lemma needs no assumption at all. -/
theorem substitution_top {Γ : Ctx} {t' : Term} {Ξ : Ctx} {u s : Term}
    {r : Rel} (h : WellSub (Ξ ++ .top :: Γ) u r s)
    (ht' : WellSub Γ t' .le .top) :
    WellSub (Ctx.substAt t' Ξ ++ Γ) (u.subst (sigmaAt Ξ.length t')) r
      (s.subst (sigmaAt Ξ.length t')) := by
  cases ht' with
  | sub hWt' _ _ =>
    exact (subst_transport hWt' (fun Ξ' => .etop)).2.2.1 _ u r s h Ξ rfl

end Pss
