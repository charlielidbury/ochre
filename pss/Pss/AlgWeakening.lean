import Pss.Basic

/-!
# Structural lemmas for the algorithmic system (Figure 2)

Renaming (hence weakening), substitution, and narrowing for `Red` /
`ASub` / `ATSub`, plus congruence of the judgments under the evaluation
contexts `E⊲`.

§6.2 of the paper explains the key design point mechanized here:
substitution and narrowing for the *algorithmic* system map a single
`≤→`-step (e.g. a variable promotion SRS-PROM whose variable is being
substituted away) to a transitive subtyping *judgment* `≤*`, not to a
reduction sequence — and `≤*` is transitive by definition (AST-TRANS),
which is exactly why SRE-APP's premise uses `≤*` rather than `≤`.
`≡→`-steps, by contrast, are preserved as single `≡→`-steps.
-/

namespace Pss

/-! ## Closedness transport -/

namespace Term

/-- Renaming maps `fv ⊆ dom(Γ)` to `fv ⊆ dom(Δ)` along a domain map. -/
theorem ClosedUnder.rename {n m : Nat} {ρ : Nat → Nat} {t : Term}
    (h : ClosedUnder n t) (hρ : ∀ x, x < n → ρ x < m) :
    ClosedUnder m (t.rename ρ) := by
  induction h generalizing m ρ with
  | var hx => exact .var (hρ _ hx)
  | top => exact .top
  | lam _ _ iht ihu =>
    refine .lam (iht hρ) (ihu fun x hx => ?_)
    cases x with
    | zero => exact Nat.zero_lt_succ _
    | succ x => exact Nat.succ_lt_succ (hρ x (Nat.lt_of_succ_lt_succ hx))
  | app _ _ iht ihu => exact .app (iht hρ) (ihu hρ)

/-- Substitution maps `fv ⊆ dom(Γ)` to `fv ⊆ dom(Δ)` when every image
variable is `Δ`-closed. -/
theorem ClosedUnder.subst {n m : Nat} {σ : Nat → Term} {t : Term}
    (h : ClosedUnder n t) (hσ : ∀ x, x < n → ClosedUnder m (σ x)) :
    ClosedUnder m (t.subst σ) := by
  induction h generalizing m σ with
  | var hx => exact hσ _ hx
  | top => exact .top
  | lam _ _ iht ihu =>
    refine .lam (iht hσ) (ihu fun x hx => ?_)
    cases x with
    | zero => exact .var (Nat.zero_lt_succ _)
    | succ x =>
      exact (hσ x (Nat.lt_of_succ_lt_succ hx)).rename
        fun y hy => Nat.succ_lt_succ hy
  | app _ _ iht ihu => exact .app (iht hσ) (ihu hσ)

/-- Shifting commutes with lifted renaming: `(↑t)⟨⇑ρ⟩ = ↑(t⟨ρ⟩)`. -/
theorem shift_rename (ρ : Nat → Nat) (t : Term) :
    (t.shift 1).rename (liftRen ρ) = (t.rename ρ).shift 1 := by
  show (t.rename (· + 1)).rename (liftRen ρ)
      = (t.rename ρ).rename (· + 1)
  rw [rename_rename, rename_rename]
  rfl

/-- Shifting commutes with lifted substitution: `(↑t)[⇑σ] = ↑(t[σ])`. -/
theorem shift_subst_lift (σ : Nat → Term) (t : Term) :
    (t.shift 1).subst (liftSubst σ) = (t.subst σ).shift 1 := by
  show (t.rename (· + 1)).subst (liftSubst σ)
      = (t.subst σ).rename (· + 1)
  rw [subst_rename, rename_subst]
  rfl

end Term

/-- The first entry of a prevalid context is closed under the rest. -/
theorem Prevalid.head {Γ : Ctx} {t : Term} (h : Prevalid (t :: Γ)) :
    Term.ClosedUnder Γ.length t := by
  cases h with
  | cons _ ht => exact ht

/-! ## Evaluation-context transport

`E≤` is a sub-grammar of `E≡` (`ECtx.toEq`), and both are closed under
renaming and substitution (the body stored under `lamBound` lives under
the binder, so it is lifted). -/

/-- Every positive context `E≤` is also an `E≡` context. -/
def ECtx.toEq : ECtx .le → ECtx .eq
  | .hole => .hole
  | .appL E t => .appL E.toEq t

@[simp] theorem ECtx.fill_toEq : (E : ECtx .le) → ∀ s : Term,
    E.toEq.fill s = E.fill s
  | .hole, _ => by simp [ECtx.toEq, ECtx.fill]
  | .appL E t, s => by simp [ECtx.toEq, ECtx.fill, fill_toEq E]

/-- An `≡→`-step may be lifted through an `E⊲` context of *either*
polarity (for `E≤` via `ECtx.toEq`). -/
theorem Red.cong_eq {Γ : Ctx} {u u' : Term} {r : Rel} (E : ECtx r)
    (h : Red Γ u .eq u') : Red Γ (E.fill u) .eq (E.fill u') := by
  cases r with
  | eq => exact .cong E h
  | le =>
    rw [← ECtx.fill_toEq, ← ECtx.fill_toEq]
    exact .cong E.toEq h

/-- Rename the term parts of an `E⊲` context. The body stored under
`lamBound` is under the binder, so its renaming is lifted. -/
def ECtx.rename (ρ : Nat → Nat) : {r : Rel} → ECtx r → ECtx r
  | _, .hole => .hole
  | _, .appL E t => .appL (E.rename ρ) (t.rename ρ)
  | _, .appR t E => .appR (t.rename ρ) (E.rename ρ)
  | _, .lamBound E t => .lamBound (E.rename ρ) (t.rename (Term.liftRen ρ))

theorem ECtx.fill_rename (ρ : Nat → Nat) :
    {r : Rel} → (E : ECtx r) → ∀ s : Term,
    (E.fill s).rename ρ = (E.rename ρ).fill (s.rename ρ)
  | _, .hole, _ => rfl
  | _, .appL E t, s => by
    show Term.app ((E.fill s).rename ρ) (t.rename ρ) = _
    rw [fill_rename ρ E s]; rfl
  | _, .appR t E, s => by
    show Term.app (t.rename ρ) ((E.fill s).rename ρ) = _
    rw [fill_rename ρ E s]; rfl
  | _, .lamBound E t, s => by
    show Term.lam ((E.fill s).rename ρ) (t.rename (Term.liftRen ρ)) = _
    rw [fill_rename ρ E s]; rfl

/-- Substitute into the term parts of an `E⊲` context (lifted under the
`lamBound` body). -/
def ECtx.subst (σ : Nat → Term) : {r : Rel} → ECtx r → ECtx r
  | _, .hole => .hole
  | _, .appL E t => .appL (E.subst σ) (t.subst σ)
  | _, .appR t E => .appR (t.subst σ) (E.subst σ)
  | _, .lamBound E t => .lamBound (E.subst σ) (t.subst (Term.liftSubst σ))

theorem ECtx.fill_subst (σ : Nat → Term) :
    {r : Rel} → (E : ECtx r) → ∀ s : Term,
    (E.fill s).subst σ = (E.subst σ).fill (s.subst σ)
  | _, .hole, _ => rfl
  | _, .appL E t, s => by
    show Term.app ((E.fill s).subst σ) (t.subst σ) = _
    rw [fill_subst σ E s]; rfl
  | _, .appR t E, s => by
    show Term.app (t.subst σ) ((E.fill s).subst σ) = _
    rw [fill_subst σ E s]; rfl
  | _, .lamBound E t, s => by
    show Term.lam ((E.fill s).subst σ) (t.subst (Term.liftSubst σ)) = _
    rw [fill_subst σ E s]; rfl

/-! ## Renaming (context morphisms)

A renaming `ρ` is a *morphism* from `Γ` to `Δ` when it maps `dom(Γ)`
into `dom(Δ)` and transports every bound `x ≤ t ∈ Γ` to
`ρ x ≤ t⟨ρ⟩ ∈ Δ`. Weakening is the instance `ρ = (· + 1)`,
`Δ = a :: Γ`. -/

/-- Context morphism for renamings. -/
structure RenMorph (ρ : Nat → Nat) (Γ Δ : Ctx) : Prop where
  prevalid : Prevalid Δ
  dom : ∀ {x : Nat}, x < Γ.length → ρ x < Δ.length
  bound : ∀ {x : Nat} {t : Term},
    Ctx.Bound Γ x t → Ctx.Bound Δ (ρ x) (t.rename ρ)

/-- Push a renaming morphism under one binder. -/
theorem RenMorph.lift {ρ : Nat → Nat} {Γ Δ : Ctx} {t : Term}
    (hm : RenMorph ρ Γ Δ) (ht : Term.ClosedUnder Γ.length t) :
    RenMorph (Term.liftRen ρ) (t :: Γ) (t.rename ρ :: Δ) where
  prevalid := .cons hm.prevalid (ht.rename fun _ hx => hm.dom hx)
  dom := by
    intro x hx
    cases x with
    | zero => exact Nat.zero_lt_succ _
    | succ x =>
      exact Nat.succ_lt_succ (hm.dom (Nat.lt_of_succ_lt_succ hx))
  bound := by
    intro x s hb
    cases hb with
    | here =>
      rw [Term.shift_rename]
      exact .here
    | there hb =>
      rw [Term.shift_rename]
      exact .there (hm.bound hb)

/-- The weakening morphism `(· + 1) : Γ → (a :: Γ)`. -/
theorem RenMorph.shift {Γ : Ctx} {a : Term}
    (ha : Prevalid (a :: Γ)) : RenMorph (· + 1) Γ (a :: Γ) where
  prevalid := ha
  dom := fun hx => Nat.succ_lt_succ hx
  bound := fun hb => .there hb

/-- **Renaming for the algorithmic block**: all three judgments transport
along renaming context morphisms. Single steps stay single steps. -/
theorem alg_rename :
    (∀ Γ t r t', Red Γ t r t' → ∀ Δ ρ, RenMorph ρ Γ Δ →
      Red Δ (t.rename ρ) r (t'.rename ρ))
    ∧ (∀ Γ t r u, ASub Γ t r u → ∀ Δ ρ, RenMorph ρ Γ Δ →
      ASub Δ (t.rename ρ) r (u.rename ρ))
    ∧ (∀ Γ t r u, ATSub Γ t r u → ∀ Δ ρ, RenMorph ρ Γ Δ →
      ATSub Δ (t.rename ρ) r (u.rename ρ)) :=
  alg_induction
    (motR := fun Γ t r t' => ∀ Δ ρ, RenMorph ρ Γ Δ →
      Red Δ (t.rename ρ) r (t'.rename ρ))
    (motA := fun Γ t r u => ∀ Δ ρ, RenMorph ρ Γ Δ →
      ASub Δ (t.rename ρ) r (u.rename ρ))
    (motT := fun Γ t r u => ∀ Δ ρ, RenMorph ρ Γ Δ →
      ATSub Δ (t.rename ρ) r (u.rename ρ))
    (red_prom := fun _ hb _ _ hm => .prom hm.prevalid (hm.bound hb))
    (red_rtop := fun _ _ _ hm => .rtop hm.prevalid)
    (red_beta := fun _ ih Δ ρ hm => by
      rw [Term.rename_subst1]
      exact .beta (ih Δ ρ hm))
    (red_topApp := fun _ _ _ hm => .topApp hm.prevalid)
    (red_cong := fun E _ ih Δ ρ hm => by
      rw [ECtx.fill_rename, ECtx.fill_rename]
      exact .cong (E.rename ρ) (ih Δ ρ hm))
    (red_fn := fun h ih Δ ρ hm =>
      .fn (ih _ _ (hm.lift h.prevalid.head)))
    (red_eq := fun _ ih Δ ρ hm => .eq (ih Δ ρ hm))
    (asub_refl := fun _ _ _ hm => .refl hm.prevalid)
    (asub_left := fun _ _ ihred ih Δ ρ hm =>
      .left (ihred Δ ρ hm) (ih Δ ρ hm))
    (asub_right := fun _ _ ihred ih Δ ρ hm =>
      .right (ihred Δ ρ hm) (ih Δ ρ hm))
    (atsub_sub := fun _ ih Δ ρ hm => .sub (ih Δ ρ hm))
    (atsub_trans := fun _ _ ih1 ih2 Δ ρ hm =>
      .trans (ih1 Δ ρ hm) (ih2 Δ ρ hm))

/-- Renaming for `⊲→` steps. -/
theorem Red.rename {Γ Δ : Ctx} {t t' : Term} {r : Rel} {ρ : Nat → Nat}
    (h : Red Γ t r t') (hm : RenMorph ρ Γ Δ) :
    Red Δ (t.rename ρ) r (t'.rename ρ) :=
  alg_rename.1 Γ t r t' h Δ ρ hm

/-- Renaming for `⊲`. -/
theorem ASub.rename {Γ Δ : Ctx} {t u : Term} {r : Rel} {ρ : Nat → Nat}
    (h : ASub Γ t r u) (hm : RenMorph ρ Γ Δ) :
    ASub Δ (t.rename ρ) r (u.rename ρ) :=
  alg_rename.2.1 Γ t r u h Δ ρ hm

/-- Renaming for `⊲*`. -/
theorem ATSub.rename {Γ Δ : Ctx} {t u : Term} {r : Rel} {ρ : Nat → Nat}
    (h : ATSub Γ t r u) (hm : RenMorph ρ Γ Δ) :
    ATSub Δ (t.rename ρ) r (u.rename ρ) :=
  alg_rename.2.2 Γ t r u h Δ ρ hm

/-! ### Weakening (the `(· + 1)` instance) -/

/-- Weakening for `⊲→` steps: `Γ ⊢A t ⊲→ t'` and `fv(a) ⊆ dom(Γ)` give
`Γ, x ≤ a ⊢A ↑t ⊲→ ↑t'`. -/
theorem Red.weaken {Γ : Ctx} {t t' a : Term} {r : Rel}
    (h : Red Γ t r t') (ha : Term.ClosedUnder Γ.length a) :
    Red (a :: Γ) (t.shift 1) r (t'.shift 1) :=
  h.rename (RenMorph.shift (.cons h.prevalid ha))

/-- Weakening for `⊲`. -/
theorem ASub.weaken {Γ : Ctx} {t u a : Term} {r : Rel}
    (h : ASub Γ t r u) (ha : Term.ClosedUnder Γ.length a) :
    ASub (a :: Γ) (t.shift 1) r (u.shift 1) :=
  h.rename (RenMorph.shift (.cons h.prevalid ha))

/-- Weakening for `⊲*`. -/
theorem ATSub.weaken {Γ : Ctx} {t u a : Term} {r : Rel}
    (h : ATSub Γ t r u) (ha : Term.ClosedUnder Γ.length a) :
    ATSub (a :: Γ) (t.shift 1) r (u.shift 1) :=
  h.rename (RenMorph.shift (.cons h.prevalid ha))

/-! ## Single steps and reduction sequences as judgments -/

/-- A single `⊲→` step is a `⊲` judgment (AS-LEFT into AS-REFL). -/
theorem ASub.of_red {Γ : Ctx} {t t' : Term} {r : Rel}
    (h : Red Γ t r t') : ASub Γ t r t' :=
  .left h (.refl h.prevalid)

/-- A single backwards `≡→` step is a `⊲` judgment at *either* relation
(AS-RIGHT into AS-REFL): if `u ≡→ u'` then `u' ⊲ u`. -/
theorem ASub.of_red_rev {Γ : Ctx} {u u' : Term} (r : Rel)
    (h : Red Γ u .eq u') : ASub Γ u' r u :=
  .right h (.refl h.prevalid)

/-- A `⊲→*` sequence is a `⊲` judgment. -/
theorem ASub.of_redStar {Γ : Ctx} {t t' : Term} {r : Rel}
    (hΓ : Prevalid Γ) (h : RedStar Γ t r t') : ASub Γ t r t' :=
  ASub.of_join hΓ h .refl

/-- A single `⊲→` step is a `⊲*` judgment. -/
theorem ATSub.of_red {Γ : Ctx} {t t' : Term} {r : Rel}
    (h : Red Γ t r t') : ATSub Γ t r t' :=
  .sub (.of_red h)

/-- A `⊲→*` sequence is a `⊲*` judgment. -/
theorem ATSub.of_redStar {Γ : Ctx} {t t' : Term} {r : Rel}
    (hΓ : Prevalid Γ) (h : RedStar Γ t r t') : ATSub Γ t r t' :=
  .sub (.of_redStar hΓ h)

/-! ## Congruence of the judgments under `E⊲` and λ-bodies

These are the judgment-level forms of SR-CONG / SR-FUN: e.g. from
`c ≤* a`, conclude `E≤[c] ≤* E≤[a]` — exactly the completing-edge
construction of §6.6.1 case (2). -/

/-- `⊲` is a congruence with respect to `E⊲` contexts. -/
theorem ASub.cong {Γ : Ctx} {t u : Term} {r : Rel} (E : ECtx r)
    (h : ASub Γ t r u) : ASub Γ (E.fill t) r (E.fill u) :=
  h.induct
    (motR := fun _ _ _ _ => True)
    (motA := fun Γ t r u => ∀ E : ECtx r, ASub Γ (E.fill t) r (E.fill u))
    (motT := fun _ _ _ _ => True)
    (red_prom := fun _ _ => trivial)
    (red_rtop := fun _ => trivial)
    (red_beta := fun _ _ => trivial)
    (red_topApp := fun _ => trivial)
    (red_cong := fun _ _ _ => trivial)
    (red_fn := fun _ _ => trivial)
    (red_eq := fun _ _ => trivial)
    (asub_refl := fun h _ => .refl h)
    (asub_left := fun hred _ _ ih E => .left (.cong E hred) (ih E))
    (asub_right := fun hred _ _ ih E => .right (Red.cong_eq E hred) (ih E))
    (atsub_sub := fun _ _ => trivial)
    (atsub_trans := fun _ _ _ _ => trivial)
    E

/-- `⊲*` is a congruence with respect to `E⊲` contexts. -/
theorem ATSub.cong {Γ : Ctx} {t u : Term} {r : Rel} (E : ECtx r)
    (h : ATSub Γ t r u) : ATSub Γ (E.fill t) r (E.fill u) :=
  h.induct
    (motR := fun _ _ _ _ => True)
    (motA := fun Γ t r u => ASub Γ t r u)
    (motT := fun Γ t r u => ∀ E : ECtx r, ATSub Γ (E.fill t) r (E.fill u))
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
    (atsub_sub := fun _ ih E => .sub (ih.cong E))
    (atsub_trans := fun _ _ ih1 ih2 E => .trans (ih1 E) (ih2 E))
    E

/-- `⊲` is a congruence with respect to λ-bodies (judgment-level SR-FUN). -/
theorem ASub.fn {Γ : Ctx} {a u u' : Term} {r : Rel}
    (h : ASub (a :: Γ) u r u') :
    ASub Γ (.lam a u) r (.lam a u') :=
  have ⟨_, h1, h2⟩ := h.to_join
  ASub.of_join h.prevalid.tail (RedStar.fn h1) (RedStar.fn h2)

/-- `⊲*` is a congruence with respect to λ-bodies. -/
theorem ATSub.fn {Γ : Ctx} {a u u' : Term} {r : Rel}
    (h : ATSub (a :: Γ) u r u') :
    ATSub Γ (.lam a u) r (.lam a u') :=
  h.induct
    (motR := fun _ _ _ _ => True)
    (motA := fun Δ t r t' => ASub Δ t r t')
    (motT := fun Δ t r t' => ∀ Γ a u u', Δ = a :: Γ → t = u → t' = u' →
      ATSub Γ (.lam a u) r (.lam a u'))
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
    (atsub_sub := fun _ ih _ _ _ _ hΔ ht ht' => by
      subst hΔ; subst ht; subst ht'; exact .sub ih.fn)
    (atsub_trans := fun _ _ ih1 ih2 _ _ _ _ hΔ ht ht' => by
      subst hΔ; subst ht; subst ht'
      exact .trans (ih1 _ _ _ _ rfl rfl rfl) (ih2 _ _ _ _ rfl rfl rfl))
    Γ a u u' rfl rfl rfl

/-! ## Substitution (context morphisms)

This is the §6.2 lemma shape: a substitution maps each variable `x` with
`x ≤ t ∈ Γ` to a term `σ x` that is `≤*`-below `t[σ]`. Transporting a
single `≤→`-step (a promotion of a substituted variable) then yields a
transitive subtyping *judgment* `≤*` rather than a reduction — "both of
these lemmas require transitivity. ... This potential circularity is
eliminated by using `≤*`, which is transitive by definition." (§6.2). -/

/-- Result of transporting one `⊲→` step along a substitution morphism:
`≡`-steps stay single steps, `≤`-steps become `≤*` judgments. -/
def SubstRed (Δ : Ctx) (t : Term) : Rel → Term → Prop
  | .eq, t' => Red Δ t .eq t'
  | .le, t' => ATSub Δ t .le t'

/-- Either way, the transported step is a `⊲*` judgment. -/
theorem SubstRed.toATSub {Δ : Ctx} {t t' : Term} :
    {r : Rel} → SubstRed Δ t r t' → ATSub Δ t r t'
  | .eq, h => .of_red h
  | .le, h => h

/-- Context morphism for substitutions. -/
structure SubstMorph (σ : Nat → Term) (Γ Δ : Ctx) : Prop where
  prevalid : Prevalid Δ
  closed : ∀ {x : Nat}, x < Γ.length → Term.ClosedUnder Δ.length (σ x)
  bound : ∀ {x : Nat} {t : Term},
    Ctx.Bound Γ x t → ATSub Δ (σ x) .le (t.subst σ)

/-- Push a substitution morphism under one binder. -/
theorem SubstMorph.lift {σ : Nat → Term} {Γ Δ : Ctx} {a : Term}
    (hm : SubstMorph σ Γ Δ) (ha : Term.ClosedUnder Γ.length a) :
    SubstMorph (Term.liftSubst σ) (a :: Γ) (a.subst σ :: Δ) where
  prevalid := .cons hm.prevalid (ha.subst fun _ hx => hm.closed hx)
  closed := by
    intro x hx
    cases x with
    | zero => exact .var (Nat.zero_lt_succ _)
    | succ x =>
      exact (hm.closed (Nat.lt_of_succ_lt_succ hx)).rename
        fun _ hy => Nat.succ_lt_succ hy
  bound := by
    intro x t hb
    cases hb with
    | here =>
      rw [Term.shift_subst_lift]
      exact .of_red (.prom
        (.cons hm.prevalid (ha.subst fun _ hx => hm.closed hx)) .here)
    | there hb =>
      rw [Term.shift_subst_lift]
      exact (hm.bound hb).weaken (ha.subst fun _ hx => hm.closed hx)

/-- **Substitution for the algorithmic block** (§6.2): `≡→`-steps are
preserved as single steps; `≤→`-steps and both judgments become `⊲*`
judgments. -/
theorem alg_subst :
    (∀ Γ t r t', Red Γ t r t' → ∀ Δ σ, SubstMorph σ Γ Δ →
      SubstRed Δ (t.subst σ) r (t'.subst σ))
    ∧ (∀ Γ t r u, ASub Γ t r u → ∀ Δ σ, SubstMorph σ Γ Δ →
      ATSub Δ (t.subst σ) r (u.subst σ))
    ∧ (∀ Γ t r u, ATSub Γ t r u → ∀ Δ σ, SubstMorph σ Γ Δ →
      ATSub Δ (t.subst σ) r (u.subst σ)) :=
  alg_induction
    (motR := fun Γ t r t' => ∀ Δ σ, SubstMorph σ Γ Δ →
      SubstRed Δ (t.subst σ) r (t'.subst σ))
    (motA := fun Γ t r u => ∀ Δ σ, SubstMorph σ Γ Δ →
      ATSub Δ (t.subst σ) r (u.subst σ))
    (motT := fun Γ t r u => ∀ Δ σ, SubstMorph σ Γ Δ →
      ATSub Δ (t.subst σ) r (u.subst σ))
    (red_prom := fun _ hb _ _ hm => hm.bound hb)
    (red_rtop := fun _ _ _ hm => ATSub.of_red (.rtop hm.prevalid))
    (red_beta := fun _ ih Δ σ hm => by
      show Red Δ _ .eq _
      rw [Term.subst_subst1]
      exact .beta (ih Δ σ hm))
    (red_topApp := fun _ _ _ hm => by
      show Red _ _ .eq _
      exact .topApp hm.prevalid)
    (red_cong := fun {_ _ _ r} E _ ih Δ σ hm => by
      cases r with
      | eq =>
        show Red Δ _ .eq _
        rw [ECtx.fill_subst, ECtx.fill_subst]
        exact .cong (E.subst σ) (ih Δ σ hm)
      | le =>
        show ATSub Δ _ .le _
        rw [ECtx.fill_subst, ECtx.fill_subst]
        exact (ih Δ σ hm).cong (E.subst σ))
    (red_fn := fun {_ t _ _ r} h ih Δ σ hm => by
      have ih' := ih (t.subst σ :: Δ) _ (hm.lift h.prevalid.head)
      cases r with
      | eq => exact Red.fn ih'
      | le => exact ATSub.fn ih')
    (red_eq := fun _ ih Δ σ hm => ATSub.of_red (.eq (ih Δ σ hm)))
    (asub_refl := fun _ _ _ hm => .sub (.refl hm.prevalid))
    (asub_left := fun _ _ ihred ih Δ σ hm =>
      ((ihred Δ σ hm).toATSub).trans (ih Δ σ hm))
    (asub_right := fun {_ _ _ _ r} _ _ ihred ih Δ σ hm =>
      (ih Δ σ hm).trans (.sub (ASub.of_red_rev r (ihred Δ σ hm))))
    (atsub_sub := fun _ ih => ih)
    (atsub_trans := fun _ _ ih1 ih2 Δ σ hm =>
      .trans (ih1 Δ σ hm) (ih2 Δ σ hm))

/-! ### Single-variable substitution (the SRE-APP / β instance)

Substituting `c` for the outermost variable of `a :: Γ` is a morphism
into `Γ` provided `c ≤* a` — exactly the situation at a β-redex
`(λx ≤ a. b)(c)` whose SRE-APP premise gives `c ≤* a`. -/

/-- `[x ↦ c] : (a :: Γ) → Γ` is a substitution morphism when `c ≤* a`. -/
theorem SubstMorph.subst1 {Γ : Ctx} {a c : Term}
    (hc : ATSub Γ c .le a) (hcc : Term.ClosedUnder Γ.length c) :
    SubstMorph (Term.scons c Term.var) (a :: Γ) Γ where
  prevalid := hc.prevalid
  closed := by
    intro x hx
    cases x with
    | zero => exact hcc
    | succ x => exact .var (Nat.lt_of_succ_lt_succ hx)
  bound := by
    intro x t hb
    cases hb with
    | here =>
      show ATSub Γ c .le ((a.shift 1).subst1 c)
      rw [Term.shift_subst1]
      exact hc
    | there hb =>
      show ATSub Γ (.var _) .le ((_root_.Pss.Term.shift _ 1).subst1 c)
      rw [Term.shift_subst1]
      exact .of_red (.prom hc.prevalid hb)

/-- Substitution for `⊲*`: instantiating the bound variable by `c ≤* a`. -/
theorem ATSub.subst1 {Γ : Ctx} {a c u v : Term} {r : Rel}
    (h : ATSub (a :: Γ) u r v) (hc : ATSub Γ c .le a)
    (hcc : Term.ClosedUnder Γ.length c) :
    ATSub Γ (u.subst1 c) r (v.subst1 c) :=
  alg_subst.2.2 _ _ _ _ h Γ _ (SubstMorph.subst1 hc hcc)

/-- Substitution for `⊲`: the result is a `⊲*` judgment (§6.2). -/
theorem ASub.subst1 {Γ : Ctx} {a c u v : Term} {r : Rel}
    (h : ASub (a :: Γ) u r v) (hc : ATSub Γ c .le a)
    (hcc : Term.ClosedUnder Γ.length c) :
    ATSub Γ (u.subst1 c) r (v.subst1 c) :=
  alg_subst.2.1 _ _ _ _ h Γ _ (SubstMorph.subst1 hc hcc)

/-- Substitution for `≡→` steps: single steps are preserved. -/
theorem Red.subst1_eq {Γ : Ctx} {a c u u' : Term}
    (h : Red (a :: Γ) u .eq u') (hc : ATSub Γ c .le a)
    (hcc : Term.ClosedUnder Γ.length c) :
    Red Γ (u.subst1 c) .eq (u'.subst1 c) :=
  alg_subst.1 _ _ _ _ h Γ _ (SubstMorph.subst1 hc hcc)

/-- Substitution for `≤→` steps: a promoted occurrence of the
substituted variable turns the step into a `≤*` judgment (§6.2). -/
theorem Red.subst1_le {Γ : Ctx} {a c u u' : Term}
    (h : Red (a :: Γ) u .le u') (hc : ATSub Γ c .le a)
    (hcc : Term.ClosedUnder Γ.length c) :
    ATSub Γ (u.subst1 c) .le (u'.subst1 c) :=
  alg_subst.1 _ _ _ _ h Γ _ (SubstMorph.subst1 hc hcc)

/-! ### Narrowing

Replacing a context bound by a `≤*`-smaller one is the substitution
morphism along the identity substitution. -/

/-- The narrowing morphism `(a :: Γ) → (a' :: Γ)` for `a' ≤* a`. -/
theorem SubstMorph.narrow {Γ : Ctx} {a a' : Term}
    (hsub : ATSub Γ a' .le a) (ha' : Term.ClosedUnder Γ.length a') :
    SubstMorph Term.var (a :: Γ) (a' :: Γ) where
  prevalid := .cons hsub.prevalid ha'
  closed := fun hx => .var hx
  bound := by
    intro x t hb
    cases hb with
    | here =>
      rw [Term.subst_var]
      exact .trans
        (.of_red (.prom (.cons hsub.prevalid ha') .here))
        (hsub.weaken ha')
    | there hb =>
      rw [Term.subst_var]
      exact .of_red (.prom (.cons hsub.prevalid ha') (.there hb))

/-- Narrowing for `⊲*`: a bound may be replaced by a `≤*`-smaller one. -/
theorem ATSub.narrow {Γ : Ctx} {a a' u v : Term} {r : Rel}
    (h : ATSub (a :: Γ) u r v) (hsub : ATSub Γ a' .le a)
    (ha' : Term.ClosedUnder Γ.length a') :
    ATSub (a' :: Γ) u r v := by
  have := alg_subst.2.2 _ _ _ _ h (a' :: Γ) _ (SubstMorph.narrow hsub ha')
  rwa [Term.subst_var, Term.subst_var] at this

/-- Narrowing for `⊲`: the result is a `⊲*` judgment. -/
theorem ASub.narrow {Γ : Ctx} {a a' u v : Term} {r : Rel}
    (h : ASub (a :: Γ) u r v) (hsub : ATSub Γ a' .le a)
    (ha' : Term.ClosedUnder Γ.length a') :
    ATSub (a' :: Γ) u r v := by
  have := alg_subst.2.1 _ _ _ _ h (a' :: Γ) _ (SubstMorph.narrow hsub ha')
  rwa [Term.subst_var, Term.subst_var] at this

/-- Narrowing for `≡→` steps: single steps are preserved. -/
theorem Red.narrow_eq {Γ : Ctx} {a a' u u' : Term}
    (h : Red (a :: Γ) u .eq u') (hsub : ATSub Γ a' .le a)
    (ha' : Term.ClosedUnder Γ.length a') :
    Red (a' :: Γ) u .eq u' := by
  have := alg_subst.1 _ _ _ _ h (a' :: Γ) _ (SubstMorph.narrow hsub ha')
  rwa [Term.subst_var, Term.subst_var] at this

/-- Narrowing for `≤→` steps: a promotion of the narrowed variable
turns the step into a `≤*` judgment. -/
theorem Red.narrow_le {Γ : Ctx} {a a' u u' : Term}
    (h : Red (a :: Γ) u .le u') (hsub : ATSub Γ a' .le a)
    (ha' : Term.ClosedUnder Γ.length a') :
    ATSub (a' :: Γ) u .le u' := by
  have := alg_subst.1 _ _ _ _ h (a' :: Γ) _ (SubstMorph.narrow hsub ha')
  rwa [Term.subst_var, Term.subst_var] at this

end Pss

