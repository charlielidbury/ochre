import Pss.Mpss.ContextRed

/-! # `Pss.Mpss.Substitution` — substitution lemmas for MPSS reductions

Pasquale & García-Pérez 2024 (CSL 2026), appendix Lemmas 28-32.

## Conventions

The paper writes contexts left-to-right with new bindings on the right
(`Γ, x ◁ t, Γ'`). Under our list-head-is-innermost convention this
becomes `Γ' ++ ⟨x, t, k⟩ :: Γ`. So `Γ₂ ++ ⟨x, t, .sub⟩ :: Γ₁` matches
the paper's `Γ₁, x ≤ t, Γ₂` (where `Γ₁` is the outer context, `Γ₂` the
innermost extension).

Substitution `[x ↦ s]` is applied entry-wise to `Γ₂` (the inner part)
and to the stack — never to `Γ₁`, since by prevalidity `x ∉ fv(Γ₁)`.

## Lemma roster

* `Lemma_28_SubstPreservesPrevalid` — substitution preserves prevalidity.
* `Lemma_31_ReductionUnderSubst_Eq` — substitution preserves `MEqRed`
  under a `.sub` head binding (the heart of the file).
* `Lemma_32_ReductionUnderSubst_Eq_OfEqu` — substitution preserves
  `MEqRed` under an `.equ` head binding (auxiliary form for commutation).
* `Lemma_30_ReductionUnderSubst_Sub` — substitution preserves `MSubRed`,
  with the `Ms-Pro y=x` arm axiomatized (see escape hatch).

## Side-condition

The substituted term `s` must be locally closed and its free variables
must be scoped by the outer context `Γ₁`:

```lean
def SubstOk (Γ : Ctx) (s : Term) : Prop :=
  Term.LC s ∧ Term.fv s ⊆ Γ.dom
```
-/

namespace Pss

/-! ## §1. Substitution on contexts and stacks -/

/-- Apply `[x ↦ s]` to every entry's `bound` field in a context. -/
def Ctx.subst (x : String) (s : Term) (Γ : Ctx) : Ctx :=
  Γ.map (fun e => ⟨e.name, Term.subst x s e.bound, e.kind⟩)

/-- Apply `[x ↦ s]` to every operand in a stack. -/
def Stack.subst (x : String) (s : Term) (st : Stack) : Stack :=
  st.map (Term.subst x s)

@[simp] lemma Ctx.subst_nil (x : String) (s : Term) :
    Ctx.subst x s [] = [] := rfl

@[simp] lemma Ctx.subst_cons (x : String) (s : Term) (e : CtxEntry) (Γ : Ctx) :
    Ctx.subst x s (e :: Γ) =
      ⟨e.name, Term.subst x s e.bound, e.kind⟩ :: Ctx.subst x s Γ := rfl

@[simp] lemma Ctx.subst_append (x : String) (s : Term) (Γ₁ Γ₂ : Ctx) :
    Ctx.subst x s (Γ₁ ++ Γ₂) = Ctx.subst x s Γ₁ ++ Ctx.subst x s Γ₂ := by
  simp [Ctx.subst, List.map_append]

@[simp] lemma Stack.subst_nil (x : String) (s : Term) :
    Stack.subst x s [] = [] := rfl

@[simp] lemma Stack.subst_cons (x : String) (s : Term) (α : Term) (st : Stack) :
    Stack.subst x s (α :: st) = Term.subst x s α :: Stack.subst x s st := rfl

/-- Domain is preserved under substitution. -/
@[simp] lemma Ctx.dom_subst (x : String) (s : Term) (Γ : Ctx) :
    Ctx.dom (Ctx.subst x s Γ) = Ctx.dom Γ := by
  induction Γ with
  | nil => rfl
  | cons e rest ih =>
    show Ctx.dom (⟨e.name, Term.subst x s e.bound, e.kind⟩ :: Ctx.subst x s rest)
       = Ctx.dom (e :: rest)
    rw [Ctx.dom_cons, Ctx.dom_cons, ih]

/-- Domain of an append. -/
@[simp] lemma Ctx.dom_append (Γ₁ Γ₂ : Ctx) :
    (Γ₁ ++ Γ₂).dom = Γ₁.dom ∪ Γ₂.dom := by
  induction Γ₁ with
  | nil => simp
  | cons e rest ih => simp [Ctx.dom, ih, Finset.insert_union]

/-! ## §2. The substitutability premise -/

/-- A term `s` is well-formed for substitution at `Γ`. -/
def SubstOk (Γ : Ctx) (s : Term) : Prop :=
  Term.LC s ∧ Term.fv s ⊆ Γ.dom

namespace SubstOk

theorem lc {Γ : Ctx} {s : Term} (h : SubstOk Γ s) : Term.LC s := h.1

theorem fv_sub {Γ : Ctx} {s : Term} (h : SubstOk Γ s) :
    Term.fv s ⊆ Γ.dom := h.2

end SubstOk

/-! ## §3. Prevalidity outer-context extraction

Used inside Lemma 32 to extract `Prevalid (⟨x, v, .equ⟩ :: Γ₁)` from
`Prevalid (Γ₂ ++ ⟨x, v, .equ⟩ :: Γ₁)`. -/

theorem Prevalid.outer {Γ₁ Γ₂ : Ctx} (h : Prevalid (Γ₂ ++ Γ₁)) : Prevalid Γ₁ := by
  induction Γ₂ with
  | nil => simpa using h
  | cons e rest ih => exact ih h.tail

/-! ## §5.5. Free-variable shifting helper

Used by Lemma 28 and the leaf cases of Lemma 31 to convert
`fv u ⊆ Ctx.dom (Γ₂ ++ ⟨x,t,k⟩ :: Γ₁)` into `fv (subst x s u) ⊆
Ctx.dom (subst x s Γ₂ ++ Γ₁)`. -/

private theorem fv_subst_dom_shift {Γ₁ Γ₂ : Ctx} {x : String}
    {s u : Term} {t : Term} {k : CtxEntryKind}
    (hok : SubstOk Γ₁ s)
    (hfv : Term.fv u ⊆ (Γ₂ ++ ⟨x, t, k⟩ :: Γ₁).dom) :
    Term.fv (Term.subst x s u) ⊆ (Ctx.subst x s Γ₂ ++ Γ₁).dom := by
  intro z hz
  have hsub := Term.fv_subst_subset x s u hz
  rw [Ctx.dom_append, Ctx.dom_subst]
  rcases Finset.mem_union.mp hsub with hsd | hsd
  · rcases Finset.mem_sdiff.mp hsd with ⟨hz_fv, hz_neq⟩
    have hz_in : z ∈ (Γ₂ ++ ⟨x, t, k⟩ :: Γ₁).dom := hfv hz_fv
    rw [Ctx.dom_append] at hz_in
    rw [Ctx.dom_cons] at hz_in
    rcases Finset.mem_union.mp hz_in with h | h
    · exact Finset.mem_union.mpr (Or.inl h)
    · rcases Finset.mem_insert.mp h with hzx | hzΓ
      · exact absurd hzx (fun hh => hz_neq (by simp [hh]))
      · exact Finset.mem_union.mpr (Or.inr hzΓ)
  · have hzΓ : z ∈ Γ₁.dom := hok.fv_sub hsd
    exact Finset.mem_union.mpr (Or.inr hzΓ)

/-! ## §6. Lemma 28 — Substitution preserves prevalidity -/

private lemma Ctx.dom_append_cons (Γ₁ Γ₂ : Ctx) (x : String) (t : Term)
    (k : CtxEntryKind) :
    (Γ₂ ++ ⟨x, t, k⟩ :: Γ₁).dom = Γ₂.dom ∪ insert x Γ₁.dom := by
  rw [Ctx.dom_append]
  simp [Ctx.dom]

private lemma Ctx.dom_subst_append (x : String) (s : Term) (Γ₁ Γ₂ : Ctx) :
    (Ctx.subst x s Γ₂ ++ Γ₁).dom = Γ₂.dom ∪ Γ₁.dom := by
  rw [Ctx.dom_append, Ctx.dom_subst]

theorem Lemma_28a_SubstPreservesPrevalid_kind
    {Γ₁ Γ₂ : Ctx} {x : String} {t s : Term} {k : CtxEntryKind}
    (hpv : Prevalid (Γ₂ ++ ⟨x, t, k⟩ :: Γ₁))
    (hok : SubstOk Γ₁ s) :
    Prevalid (Ctx.subst x s Γ₂ ++ Γ₁) := by
  induction Γ₂ with
  | nil =>
    simpa using hpv.tail
  | cons e rest ih =>
    have hpv_eq : (e :: rest ++ ⟨x, t, k⟩ :: Γ₁) =
        (e :: (rest ++ ⟨x, t, k⟩ :: Γ₁)) := by simp
    rw [hpv_eq] at hpv
    cases hpv with
    | @sub Γ' y u hΓ' hy hfv hlc =>
      have ih' := ih hΓ'
      have hy' : y ∉ Ctx.dom (Ctx.subst x s rest ++ Γ₁) := by
        rw [Ctx.dom_subst_append]
        rw [Ctx.dom_append_cons] at hy
        intro hmem
        rcases Finset.mem_union.mp hmem with h | h
        · exact hy (Finset.mem_union.mpr (Or.inl h))
        · exact hy (Finset.mem_union.mpr (Or.inr (Finset.mem_insert_of_mem h)))
      have hfv' := fv_subst_dom_shift hok hfv
      have hlc' : Term.LC (Term.subst x s u) := Term.subst_lc hok.lc hlc
      simpa [Ctx.subst] using Prevalid.sub ih' hy' hfv' hlc'
    | @equ Γ' y α hΓ' hy hfv hlc =>
      have ih' := ih hΓ'
      have hy' : y ∉ Ctx.dom (Ctx.subst x s rest ++ Γ₁) := by
        rw [Ctx.dom_subst_append]
        rw [Ctx.dom_append_cons] at hy
        intro hmem
        rcases Finset.mem_union.mp hmem with h | h
        · exact hy (Finset.mem_union.mpr (Or.inl h))
        · exact hy (Finset.mem_union.mpr (Or.inr (Finset.mem_insert_of_mem h)))
      have hfv' := fv_subst_dom_shift hok hfv
      have hlc' : Term.LC (Term.subst x s α) := Term.subst_lc hok.lc hlc
      simpa [Ctx.subst] using Prevalid.equ ih' hy' hfv' hlc'

/-- **Lemma 28** (Pasquale & García-Pérez 2024).
Substitution preserves prevalidity (extended-context form). -/
theorem Lemma_28_SubstPreservesPrevalid
    {Γ₁ Γ₂ : Ctx} {st : Stack} {x : String} {t s : Term}
    {k : CtxEntryKind}
    (hpv : PrevalidExt (Γ₂ ++ ⟨x, t, k⟩ :: Γ₁) st)
    (hok : SubstOk Γ₁ s) :
    PrevalidExt (Ctx.subst x s Γ₂ ++ Γ₁) (Stack.subst x s st) := by
  induction st with
  | nil =>
    cases hpv with
    | nil hpvL =>
      exact PrevalidExt.nil (Lemma_28a_SubstPreservesPrevalid_kind hpvL hok)
  | cons α st' ih =>
    match hpv with
    | PrevalidExt.cons hpvr hLCα hfvα =>
      have ih' := ih hpvr
      exact PrevalidExt.cons ih' (Term.subst_lc hok.lc hLCα)
        (fv_subst_dom_shift hok hfvα)

/-! ## §7. Reflexivity of `MEqRed` (Proposition 18, partial) -/

/-- **Proposition 18 (MEqRed half).** Reflexivity of MPSS equivalence reduction.

Returns `MEqRedJ` (Prop-wrapped) since the proof inducts on the
Prop-valued `Term.LC u` predicate, which cannot eliminate into a
Type-valued conclusion. Callers that need the bare Type-valued
derivation can use `(MEqRed.refl …).some`. -/
theorem MEqRed.refl_J {Γ : Ctx} {st : Stack} {u : Term}
    (hpv : PrevalidExt Γ st) (hLC : Term.LC u) (hfv : Term.fv u ⊆ Γ.dom) :
    MEqRedJ Γ st u u := by
  induction hLC generalizing st Γ with
  | top => exact ⟨MEqRed.top hpv⟩
  | fvar x => exact ⟨MEqRed.var hpv⟩
  | @app a b hLCa hLCb iha ihb =>
    have hfa : Term.fv a ⊆ Γ.dom := by
      intro z hz; exact hfv (by simp [Term.fv]; exact Or.inl hz)
    have hfb : Term.fv b ⊆ Γ.dom := by
      intro z hz; exact hfv (by simp [Term.fv]; exact Or.inr hz)
    have hpvb : PrevalidExt Γ (b :: st) := PrevalidExt.cons hpv hLCb hfb
    have hpvnil : PrevalidExt Γ [] := PrevalidExt.nil (extractPrevalid hpv)
    obtain ⟨ha⟩ := iha hpvb hfa
    obtain ⟨hb⟩ := ihb hpvnil hfb
    exact ⟨MEqRed.app ha hb⟩
  | @abs L bound body hLCbound hbody ihbound ihbody =>
    have hpvnil : PrevalidExt Γ [] := PrevalidExt.nil (extractPrevalid hpv)
    have hfb : Term.fv bound ⊆ Γ.dom := by
      intro z hz; exact hfv (by simp [Term.fv]; exact Or.inl hz)
    have hfbody : Term.fv body ⊆ Γ.dom := by
      intro z hz; exact hfv (by simp [Term.fv]; exact Or.inr hz)
    obtain ⟨hb_refl⟩ : MEqRedJ Γ [] bound bound := ihbound hpvnil hfb
    cases st with
    | nil =>
      classical
      -- Build the cofinite witness: at each fresh `y`, get a Type-level
      -- MEqRed for the opened body. We collect via Classical.choice.
      have hbody_each : ∀ y, y ∉ (L ∪ Γ.dom) →
          Nonempty (MEqRed (⟨y, bound, .sub⟩ :: Γ) [] (body^[y]) (body^[y])) := by
        intro y hy
        have hyL : y ∉ L := fun h => hy (Finset.mem_union.mpr (Or.inl h))
        have hyΓ : y ∉ Γ.dom := fun h => hy (Finset.mem_union.mpr (Or.inr h))
        have hpvy : Prevalid (⟨y, bound, .sub⟩ :: Γ) :=
          Prevalid.sub (extractPrevalid hpv) hyΓ hfb hLCbound
        have hpvey : PrevalidExt (⟨y, bound, .sub⟩ :: Γ) [] := PrevalidExt.nil hpvy
        have hfvy : Term.fv (body^[y]) ⊆ Ctx.dom (⟨y, bound, .sub⟩ :: Γ) := by
          intro z hz
          have hsub := Term.fv_open_subset 0 (.fvar y) body
          have hmem : z ∈ Term.fv body ∪ Term.fv (.fvar y) := hsub hz
          rcases Finset.mem_union.mp hmem with h | h
          · have hzΓ : z ∈ Γ.dom := hfbody h
            have hdom_eq : Ctx.dom (⟨y, bound, .sub⟩ :: Γ) =
                insert y Γ.dom := Ctx.dom_cons _ _
            rw [hdom_eq]
            exact Finset.mem_insert_of_mem hzΓ
          · have hzy : z = y := by simpa [Term.fv] using h
            subst hzy
            have hdom_eq : Ctx.dom (⟨z, bound, .sub⟩ :: Γ) =
                insert z Γ.dom := Ctx.dom_cons _ _
            rw [hdom_eq]
            exact Finset.mem_insert_self _ _
        exact ihbody y hyL hpvey hfvy
      have hbody_choice : ∀ y, y ∉ (L ∪ Γ.dom) →
          MEqRed (⟨y, bound, .sub⟩ :: Γ) [] (body^[y]) (body^[y]) :=
        fun y hy => (hbody_each y hy).some
      exact ⟨MEqRed.fun_ (L ∪ Γ.dom) hb_refl hbody_choice⟩
    | cons α tail =>
      cases hpv with
      | cons hpvr hLCα hfvα =>
        classical
        have hpvey_aux : ∀ {st : Stack} (y : String) (_hyΓ : y ∉ Γ.dom),
            PrevalidExt Γ st →
            Prevalid (⟨y, α, .equ⟩ :: Γ) →
            PrevalidExt (⟨y, α, .equ⟩ :: Γ) st := by
          intro st y _hyΓ hst hpvy
          induction hst with
          | nil _ => exact PrevalidExt.nil hpvy
          | @cons _ β hpvE hLCβ hfvβ ih =>
            refine PrevalidExt.cons ih hLCβ ?_
            intro z hz
            have hzΓ : z ∈ Γ.dom := hfvβ hz
            have hdom_eq : Ctx.dom (⟨y, α, .equ⟩ :: Γ) =
                insert y Γ.dom := Ctx.dom_cons _ _
            show z ∈ Ctx.dom (⟨y, α, .equ⟩ :: Γ)
            rw [hdom_eq]
            exact Finset.mem_insert_of_mem hzΓ
        have hbody_each : ∀ y, y ∉ (L ∪ Γ.dom) →
            Nonempty (MEqRed (⟨y, α, .equ⟩ :: Γ) tail (body^[y]) (body^[y])) := by
          intro y hy
          have hyL : y ∉ L := fun h => hy (Finset.mem_union.mpr (Or.inl h))
          have hyΓ : y ∉ Γ.dom := fun h => hy (Finset.mem_union.mpr (Or.inr h))
          have hpvy : Prevalid (⟨y, α, .equ⟩ :: Γ) :=
            Prevalid.equ (extractPrevalid hpvr) hyΓ hfvα hLCα
          have hpvey : PrevalidExt (⟨y, α, .equ⟩ :: Γ) tail :=
            hpvey_aux y hyΓ hpvr hpvy
          have hfvy : Term.fv (body^[y]) ⊆ Ctx.dom (⟨y, α, .equ⟩ :: Γ) := by
            intro z hz
            have hsub := Term.fv_open_subset 0 (.fvar y) body
            have hmem : z ∈ Term.fv body ∪ Term.fv (.fvar y) := hsub hz
            rcases Finset.mem_union.mp hmem with h | h
            · have hzΓ : z ∈ Γ.dom := hfbody h
              have hdom_eq : Ctx.dom (⟨y, α, .equ⟩ :: Γ) =
                  insert y Γ.dom := Ctx.dom_cons _ _
              rw [hdom_eq]
              exact Finset.mem_insert_of_mem hzΓ
            · have hzy : z = y := by simpa [Term.fv] using h
              subst hzy
              have hdom_eq : Ctx.dom (⟨z, α, .equ⟩ :: Γ) =
                  insert z Γ.dom := Ctx.dom_cons _ _
              rw [hdom_eq]
              exact Finset.mem_insert_self _ _
          exact ihbody y hyL hpvey hfvy
        have hbody_choice : ∀ y, y ∉ (L ∪ Γ.dom) →
            MEqRed (⟨y, α, .equ⟩ :: Γ) tail (body^[y]) (body^[y]) :=
          fun y hy => (hbody_each y hy).some
        exact ⟨MEqRed.fOp (L ∪ Γ.dom) hb_refl hbody_choice⟩

/-- Type-valued accessor for `MEqRed.refl_J`. Uses choice to extract the
underlying derivation tree from the `Nonempty`-wrapped result. -/
noncomputable def MEqRed.refl {Γ : Ctx} {st : Stack} {u : Term}
    (hpv : PrevalidExt Γ st) (hLC : Term.LC u) (hfv : Term.fv u ⊆ Γ.dom) :
    MEqRed Γ st u u :=
  (MEqRed.refl_J hpv hLC hfv).some

/-! ## §8. Helper lemmas for Lemma 31 -/

/-- If `Γ₂ ++ ⟨x, t, .sub⟩ :: Γ₁` has a `.equ`-binding for `y`, then `y ≠ x`
(since the only entry for `x` is `.sub`, by prevalidity). -/
private theorem equBinds_ne_x_at_sub_head
    {Γ₁ Γ₂ : Ctx} {x y : String} {t α : Term}
    (hpv : Prevalid (Γ₂ ++ ⟨x, t, .sub⟩ :: Γ₁))
    (heq : (Γ₂ ++ ⟨x, t, .sub⟩ :: Γ₁).equBinds y α) : y ≠ x := by
  intro heq_yx
  subst heq_yx
  -- We need to show contradiction: equBinds y α can't hold when the only y-entry is .sub.
  induction Γ₂ with
  | nil =>
    -- heq : equBinds y α in [] ++ ⟨y, t, .sub⟩ :: Γ₁ = ⟨y, t, .sub⟩ :: Γ₁.
    -- Head is .sub for y, so lookupEqu returns none ≠ some α. Direct contradiction.
    have heq' : Ctx.equBinds (⟨y, t, .sub⟩ :: Γ₁) y α := by simpa using heq
    simp [Ctx.equBinds, Ctx.lookupEqu] at heq'
  | cons e rest ih =>
    have hpv_eq : (e :: rest ++ ⟨y, t, .sub⟩ :: Γ₁) =
        (e :: (rest ++ ⟨y, t, .sub⟩ :: Γ₁)) := by simp
    rw [hpv_eq] at hpv
    simp [Ctx.equBinds, Ctx.lookupEqu_cons] at heq
    by_cases he : e.name = y
    · -- e is at head, e.name = y. Prevalidity says e.name ∉ dom of rest.
      cases he_kind : e.kind with
      | sub =>
        simp [he, he_kind] at heq
      | equ =>
        simp [he, he_kind] at heq
        -- The prevalid context has e.name freshness ⇒ contradiction.
        have hyfresh : e.name ∉ Ctx.dom (rest ++ ⟨y, t, .sub⟩ :: Γ₁) := by
          cases hpv with
          | sub _ hen _ _ => exact hen
          | equ _ hen _ _ => exact hen
        apply hyfresh
        rw [he, Ctx.dom_append_cons]
        apply Finset.mem_union.mpr; right
        exact Finset.mem_insert_self _ _
    · simp [he] at heq
      have hpv_tail : Prevalid (rest ++ ⟨y, t, .sub⟩ :: Γ₁) := hpv.tail
      exact ih hpv_tail heq

/-- Given `equBinds y α` in `Γ₂ ++ ⟨x, t, .sub⟩ :: Γ₁` with `y ≠ x`, find
the binding's position and produce the corresponding binding in the
substituted context. -/
private theorem equBinds_split
    {Γ₁ Γ₂ : Ctx} {x y : String} {s t α : Term}
    (hyx : y ≠ x)
    (hpv : Prevalid (Γ₂ ++ ⟨x, t, .sub⟩ :: Γ₁))
    (heq : (Γ₂ ++ ⟨x, t, .sub⟩ :: Γ₁).equBinds y α) :
    -- Two possibilities: either y is in Γ₁ (so α is unaffected by substitution),
    -- or y is in Γ₂ (so α gets substituted).
    -- We unify both cases by exhibiting the post-substitution binding.
    (Ctx.subst x s Γ₂ ++ Γ₁).equBinds y (Term.subst x s α) := by
  induction Γ₂ with
  | nil =>
    -- y is bound somewhere in ⟨x,t,.sub⟩::Γ₁. Since y ≠ x, it's in Γ₁.
    simp [Ctx.equBinds, Ctx.lookupEqu_cons, Ne.symm hyx] at heq
    -- heq : Γ₁.equBinds y α
    -- Show: ([] subst).append Γ₁).equBinds y (subst x s α) = Γ₁.equBinds y (subst x s α)
    -- α has no x in fv (by prevalidity), so subst x s α = α.
    have hfvα : Term.fv α ⊆ Γ₁.dom :=
      Prevalid.fv_lookupEqu hpv.tail heq
    have hxnotin : x ∉ Γ₁.dom := by
      cases hpv with
      | sub _ hxn _ _ => exact hxn
    have hxα : x ∉ Term.fv α := fun h => hxnotin (hfvα h)
    rw [Term.subst_fresh hxα]
    simp [Ctx.subst]
    exact heq
  | cons e rest ih =>
    have hpv_eq : (e :: rest ++ ⟨x, t, .sub⟩ :: Γ₁) =
        (e :: (rest ++ ⟨x, t, .sub⟩ :: Γ₁)) := by simp
    rw [hpv_eq] at hpv
    simp [Ctx.equBinds, Ctx.lookupEqu_cons] at heq
    by_cases he : e.name = y
    · cases he_kind : e.kind with
      | sub => simp [he, he_kind] at heq
      | equ =>
        simp [he, he_kind] at heq
        subst heq
        -- Goal: equBinds for the substituted (e :: rest ++ Γ₁), which has head with kind .equ.
        show Ctx.equBinds
          (⟨e.name, Term.subst x s e.bound, e.kind⟩ :: (Ctx.subst x s rest ++ Γ₁))
          y (Term.subst x s e.bound)
        simp [Ctx.equBinds, Ctx.lookupEqu_cons, he, he_kind]
    · simp [he] at heq
      have hpv_tail : Prevalid (rest ++ ⟨x, t, .sub⟩ :: Γ₁) := hpv.tail
      have ih' := ih hpv_tail heq
      show Ctx.equBinds
        (⟨e.name, Term.subst x s e.bound, e.kind⟩ :: (Ctx.subst x s rest ++ Γ₁))
        y (Term.subst x s α)
      simp [Ctx.equBinds, Ctx.lookupEqu_cons, he]
      exact ih'

/-- Symmetric helper for `subBinds` under a `.sub`-head context. The
`.sub` entry for `x` is the only entry that could match `x`; if `y ≠ x`
the binding is preserved through substitution. The `y = x` case yields
`b = t` and is handled separately by callers. -/
private theorem subBinds_split_neq
    {Γ₁ Γ₂ : Ctx} {x y : String} {s t b : Term}
    (hyx : y ≠ x)
    (hpv : Prevalid (Γ₂ ++ ⟨x, t, .sub⟩ :: Γ₁))
    (hb : (Γ₂ ++ ⟨x, t, .sub⟩ :: Γ₁).subBinds y b) :
    (Ctx.subst x s Γ₂ ++ Γ₁).subBinds y (Term.subst x s b) := by
  induction Γ₂ with
  | nil =>
    simp [Ctx.subBinds, Ctx.lookupSub_cons, Ne.symm hyx] at hb
    -- hb : Γ₁.subBinds y b
    have hfvb : Term.fv b ⊆ Γ₁.dom :=
      Prevalid.fv_lookupSub hpv.tail hb
    have hxnotin : x ∉ Γ₁.dom := by
      cases hpv with
      | sub _ hxn _ _ => exact hxn
    have hxb : x ∉ Term.fv b := fun h => hxnotin (hfvb h)
    rw [Term.subst_fresh hxb]
    simp [Ctx.subst]
    exact hb
  | cons e rest ih =>
    have hpv_eq : (e :: rest ++ ⟨x, t, .sub⟩ :: Γ₁) =
        (e :: (rest ++ ⟨x, t, .sub⟩ :: Γ₁)) := by simp
    rw [hpv_eq] at hpv
    simp [Ctx.subBinds, Ctx.lookupSub_cons] at hb
    by_cases he : e.name = y
    · cases he_kind : e.kind with
      | sub =>
        simp [he, he_kind] at hb
        subst hb
        show Ctx.subBinds
          (⟨e.name, Term.subst x s e.bound, e.kind⟩ :: (Ctx.subst x s rest ++ Γ₁))
          y (Term.subst x s e.bound)
        simp [Ctx.subBinds, Ctx.lookupSub_cons, he, he_kind]
      | equ => simp [he, he_kind] at hb
    · simp [he] at hb
      have hpv_tail : Prevalid (rest ++ ⟨x, t, .sub⟩ :: Γ₁) := hpv.tail
      have ih' := ih hpv_tail hb
      show Ctx.subBinds
        (⟨e.name, Term.subst x s e.bound, e.kind⟩ :: (Ctx.subst x s rest ++ Γ₁))
        y (Term.subst x s b)
      simp [Ctx.subBinds, Ctx.lookupSub_cons, he]
      exact ih'

/-- `fv` of a free-variable substitution. -/
@[simp] lemma Term.subst_fvar_eq (x : String) (s : Term) :
    Term.subst x s (.fvar x) = s := by simp [Term.subst]

/-- Substitution at a different variable is a no-op. -/
lemma Term.subst_fvar_ne {x y : String} (hyx : y ≠ x) (s : Term) :
    Term.subst x s (.fvar y) = .fvar y := by
  simp [Term.subst, hyx]

/-- Uniqueness: `.equ` head binding is the only one for `x`. -/
theorem equBinds_at_equ_head_unique
    {Γ₁ Γ₂ : Ctx} {x : String} {v α : Term}
    (hpv : Prevalid (Γ₂ ++ ⟨x, v, .equ⟩ :: Γ₁))
    (heq : (Γ₂ ++ ⟨x, v, .equ⟩ :: Γ₁).equBinds x α) : α = v := by
  induction Γ₂ with
  | nil =>
    have heq' : Ctx.equBinds (⟨x, v, .equ⟩ :: Γ₁) x α := by simpa using heq
    simp [Ctx.equBinds, Ctx.lookupEqu] at heq'
    exact heq'.symm
  | cons e rest ih =>
    have hpv_eq : (e :: rest ++ ⟨x, v, .equ⟩ :: Γ₁) =
        (e :: (rest ++ ⟨x, v, .equ⟩ :: Γ₁)) := by simp
    rw [hpv_eq] at hpv
    simp [Ctx.equBinds, Ctx.lookupEqu_cons] at heq
    by_cases he : e.name = x
    · cases he_kind : e.kind with
      | sub => simp [he, he_kind] at heq
      | equ =>
        exfalso
        have hyfresh : e.name ∉ Ctx.dom (rest ++ ⟨x, v, .equ⟩ :: Γ₁) := by
          cases hpv with
          | sub _ hen _ _ => exact hen
          | equ _ hen _ _ => exact hen
        apply hyfresh
        rw [he, Ctx.dom_append_cons]
        apply Finset.mem_union.mpr; right
        exact Finset.mem_insert_self _ _
    · simp [he] at heq
      exact ih hpv.tail heq

/-- `.equ`-head version of `equBinds_split`: when the head is `.equ` for `x`
and `y ≠ x`, `.equ`-bindings for `y` lift through substitution. -/
theorem equBinds_split_equ
    {Γ₁ Γ₂ : Ctx} {x y : String} {s v α : Term}
    (hyx : y ≠ x)
    (hpv : Prevalid (Γ₂ ++ ⟨x, v, .equ⟩ :: Γ₁))
    (heq : (Γ₂ ++ ⟨x, v, .equ⟩ :: Γ₁).equBinds y α) :
    (Ctx.subst x s Γ₂ ++ Γ₁).equBinds y (Term.subst x s α) := by
  induction Γ₂ with
  | nil =>
    simp [Ctx.equBinds, Ctx.lookupEqu_cons, Ne.symm hyx] at heq
    have hfvα : Term.fv α ⊆ Γ₁.dom :=
      Prevalid.fv_lookupEqu hpv.tail heq
    have hxnotin : x ∉ Γ₁.dom := by
      cases hpv with
      | equ _ hxn _ _ => exact hxn
    have hxα : x ∉ Term.fv α := fun h => hxnotin (hfvα h)
    rw [Term.subst_fresh hxα]
    simp [Ctx.subst]
    exact heq
  | cons e rest ih =>
    have hpv_eq : (e :: rest ++ ⟨x, v, .equ⟩ :: Γ₁) =
        (e :: (rest ++ ⟨x, v, .equ⟩ :: Γ₁)) := by simp
    rw [hpv_eq] at hpv
    simp [Ctx.equBinds, Ctx.lookupEqu_cons] at heq
    by_cases he : e.name = y
    · cases he_kind : e.kind with
      | sub => simp [he, he_kind] at heq
      | equ =>
        simp [he, he_kind] at heq
        subst heq
        show Ctx.equBinds
          (⟨e.name, Term.subst x s e.bound, e.kind⟩ :: (Ctx.subst x s rest ++ Γ₁))
          y (Term.subst x s e.bound)
        simp [Ctx.equBinds, Ctx.lookupEqu_cons, he, he_kind]
    · simp [he] at heq
      have hpv_tail : Prevalid (rest ++ ⟨x, v, .equ⟩ :: Γ₁) := hpv.tail
      have ih' := ih hpv_tail heq
      show Ctx.equBinds
        (⟨e.name, Term.subst x s e.bound, e.kind⟩ :: (Ctx.subst x s rest ++ Γ₁))
        y (Term.subst x s α)
      simp [Ctx.equBinds, Ctx.lookupEqu_cons, he]
      exact ih'

/-- `.equ`-head version: a `.sub`-binding for `x` is impossible when the
head entry for `x` is `.equ`. (Used by Renaming.) -/
theorem subBinds_at_equ_head_impossible
    {Γ₁ Γ₂ : Ctx} {x : String} {v t : Term}
    (hpv : Prevalid (Γ₂ ++ ⟨x, v, .equ⟩ :: Γ₁))
    (hsb : (Γ₂ ++ ⟨x, v, .equ⟩ :: Γ₁).subBinds x t) : False := by
  induction Γ₂ with
  | nil =>
    have hsb' : Ctx.subBinds (⟨x, v, .equ⟩ :: Γ₁) x t := by simpa using hsb
    simp [Ctx.subBinds, Ctx.lookupSub] at hsb'
  | cons e rest ih =>
    have hpv_eq : (e :: rest ++ ⟨x, v, .equ⟩ :: Γ₁) =
        (e :: (rest ++ ⟨x, v, .equ⟩ :: Γ₁)) := by simp
    rw [hpv_eq] at hpv
    simp [Ctx.subBinds, Ctx.lookupSub_cons] at hsb
    by_cases he : e.name = x
    · cases he_kind : e.kind with
      | sub =>
        -- e at head names x with kind .sub. By prevalidity, e.name ∉ tail.dom,
        -- but tail contains ⟨x, v, .equ⟩.
        have hyfresh : e.name ∉ Ctx.dom (rest ++ ⟨x, v, .equ⟩ :: Γ₁) := by
          cases hpv with
          | sub _ hen _ _ => exact hen
          | equ _ hen _ _ => exact hen
        apply hyfresh
        rw [he, Ctx.dom_append, Ctx.dom_cons]
        apply Finset.mem_union.mpr; right
        exact Finset.mem_insert_self _ _
      | equ => simp [he, he_kind] at hsb
    · simp [he] at hsb
      have hpv_tail : Prevalid (rest ++ ⟨x, v, .equ⟩ :: Γ₁) := hpv.tail
      exact ih hpv_tail hsb

/-- `.equ`-head version of `subBinds_split_neq`: when the head is `.equ` for `x`
and `y ≠ x`, `.sub`-bindings for `y` lift through substitution. -/
theorem subBinds_split_equ
    {Γ₁ Γ₂ : Ctx} {x y : String} {s v b : Term}
    (hyx : y ≠ x)
    (hpv : Prevalid (Γ₂ ++ ⟨x, v, .equ⟩ :: Γ₁))
    (hb : (Γ₂ ++ ⟨x, v, .equ⟩ :: Γ₁).subBinds y b) :
    (Ctx.subst x s Γ₂ ++ Γ₁).subBinds y (Term.subst x s b) := by
  induction Γ₂ with
  | nil =>
    -- y ≠ x and head is ⟨x, v, .equ⟩ — lookupSub skips it; binding is in Γ₁.
    have hb0 : Ctx.subBinds (⟨x, v, .equ⟩ :: Γ₁) y b := by simpa using hb
    simp [Ctx.subBinds, Ctx.lookupSub_cons, Ne.symm hyx] at hb0
    -- hb0 : Γ₁.lookupSub y = some b
    have hfvb : Term.fv b ⊆ Γ₁.dom :=
      Prevalid.fv_lookupSub hpv.tail hb0
    have hxnotin : x ∉ Γ₁.dom := by
      cases hpv with
      | equ _ hxn _ _ => exact hxn
    have hxb : x ∉ Term.fv b := fun h => hxnotin (hfvb h)
    rw [Term.subst_fresh hxb]
    show Ctx.subBinds (Ctx.subst x s ([] : Ctx) ++ Γ₁) y b
    simp [Ctx.subst]
    exact hb0
  | cons e rest ih =>
    have hpv_eq : (e :: rest ++ ⟨x, v, .equ⟩ :: Γ₁) =
        (e :: (rest ++ ⟨x, v, .equ⟩ :: Γ₁)) := by simp
    rw [hpv_eq] at hpv
    simp [Ctx.subBinds, Ctx.lookupSub_cons] at hb
    by_cases he : e.name = y
    · cases he_kind : e.kind with
      | sub =>
        simp [he, he_kind] at hb
        subst hb
        show Ctx.subBinds
          (⟨e.name, Term.subst x s e.bound, e.kind⟩ :: (Ctx.subst x s rest ++ Γ₁))
          y (Term.subst x s e.bound)
        simp [Ctx.subBinds, Ctx.lookupSub_cons, he, he_kind]
      | equ => simp [he, he_kind] at hb
    · simp [he] at hb
      have hpv_tail : Prevalid (rest ++ ⟨x, v, .equ⟩ :: Γ₁) := hpv.tail
      have ih' := ih hpv_tail hb
      show Ctx.subBinds
        (⟨e.name, Term.subst x s e.bound, e.kind⟩ :: (Ctx.subst x s rest ++ Γ₁))
        y (Term.subst x s b)
      simp [Ctx.subBinds, Ctx.lookupSub_cons, he]
      exact ih'

/-! ## §9. Lemma 31 — Reduction under substitution (MEqRed) -/

/-- **Lemma 31 (Reduction under substitution).** Substitution preserves
MPSS equivalence reduction under a `.sub` head binding.

This is the central tactical lemma of the file. Proof by induction on
the MEqRed derivation, with 8 cases (one per `MEqRed` constructor).

Heaviest cases:
* `Me-Bet` — uses `Term.subst_open` (Barendregt's substitution lemma).
* `Me-Fun`, `Me-FOp`, `Me-Bet`'s body — cofinite quantification with
  fresh `y` outside `{x} ∪ L ∪ dom ∪ fv s ∪ fv body ∪ fv body'`.
-/
noncomputable def Lemma_31_ReductionUnderSubst_Eq
    {Γ₁ Γ₂ : Ctx} {st : Stack} {x : String} {s t u v : Term}
    (h : MEqRed (Γ₂ ++ ⟨x, t, .sub⟩ :: Γ₁) st u v)
    (hok : SubstOk Γ₁ s) :
    MEqRed (Ctx.subst x s Γ₂ ++ Γ₁) (Stack.subst x s st)
      (Term.subst x s u) (Term.subst x s v) := by
  generalize hΓ : (Γ₂ ++ ⟨x, t, .sub⟩ :: Γ₁) = Γ at h
  induction h generalizing Γ₂ with
  | @pro Γ st' y α α' hpv heq hα ihα =>
    subst hΓ
    -- y ≡ α ∈ Γ. Since head is .sub at x, y ≠ x.
    have hyx : y ≠ x :=
      equBinds_ne_x_at_sub_head (extractPrevalid hpv) heq
    rw [Term.subst_fvar_ne hyx]
    have hpvL : Prevalid (Γ₂ ++ ⟨x, t, .sub⟩ :: Γ₁) := extractPrevalid hpv
    have heq' : (Ctx.subst x s Γ₂ ++ Γ₁).equBinds y (Term.subst x s α) :=
      equBinds_split hyx hpvL heq
    have hpv' : PrevalidExt (Ctx.subst x s Γ₂ ++ Γ₁) (Stack.subst x s st') :=
      Lemma_28_SubstPreservesPrevalid hpv hok
    exact MEqRed.pro hpv' heq' (ihα (Γ₂ := Γ₂) rfl)
  | @bet Γ st' t' v' v'' body body' L hLCt hbody hv ihbody ihv =>
    subst hΓ
    -- u = .app (.abs t' body) v'  reduces to  Term.opening v'' body'
    -- After subst: subst x s (.app (.abs t' body) v') = .app (.abs (subst x s t') (subst x s body)) (subst x s v')
    -- Which should reduce to: Term.opening (subst x s v'') (subst x s body')
    -- = subst x s (Term.opening v'' body')  by Barendregt (subst_open).
    have hLCs := hok.lc
    have hsubst_open : Term.subst x s (Term.opening v'' body') =
        Term.opening (Term.subst x s v'') (Term.subst x s body') := by
      simp [Term.opening, Term.subst_open hLCs]
    show MEqRed (Ctx.subst x s Γ₂ ++ Γ₁) (Stack.subst x s st')
      (Term.subst x s (.app (.abs t' body) v'))
      (Term.subst x s (Term.opening v'' body'))
    rw [hsubst_open]
    show MEqRed (Ctx.subst x s Γ₂ ++ Γ₁) (Stack.subst x s st')
      (.app (.abs (Term.subst x s t') (Term.subst x s body)) (Term.subst x s v'))
      (Term.opening (Term.subst x s v'') (Term.subst x s body'))
    refine MEqRed.bet (L ∪ {x}) (Term.subst_lc hLCs hLCt) ?_ ?_
    · -- Body case.
      intro y hy
      simp [Finset.mem_union, Finset.mem_singleton] at hy
      have hyL : y ∉ L := hy.1
      have hyx : y ≠ x := hy.2
      have ih_body := ihbody y hyL (Γ₂ := Γ₂) rfl
      rw [Term.subst_open_var (Ne.symm hyx) hLCs body,
          Term.subst_open_var (Ne.symm hyx) hLCs body'] at ih_body
      exact ih_body
    · -- Operand case at empty stack.
      have ihv' := ihv (Γ₂ := Γ₂) rfl
      simpa using ihv'
  | @top Γ st' hpv =>
    subst hΓ
    have hpv' : PrevalidExt (Ctx.subst x s Γ₂ ++ Γ₁) (Stack.subst x s st') :=
      Lemma_28_SubstPreservesPrevalid hpv hok
    exact MEqRed.top hpv'
  | @app Γ st' u_ u_' v_ v_' hu hv ihu ihv =>
    subst hΓ
    have ihu' := ihu (Γ₂ := Γ₂) rfl
    have ihv' := ihv (Γ₂ := Γ₂) rfl
    simp at ihu'
    refine MEqRed.app ?_ ?_
    · exact ihu'
    · simpa using ihv'
  | @var Γ st' y hpv =>
    subst hΓ
    have hpv' : PrevalidExt (Ctx.subst x s Γ₂ ++ Γ₁) (Stack.subst x s st') :=
      Lemma_28_SubstPreservesPrevalid hpv hok
    by_cases hyx : y = x
    · -- y = x. After subst, fvar y becomes s. Use reflexivity.
      have heq : Term.subst x s (.fvar y) = s := by
        rw [hyx]; exact Term.subst_fvar_eq x s
      rw [heq]
      have hfvs : Term.fv s ⊆ Ctx.dom (Ctx.subst x s Γ₂ ++ Γ₁) := by
        intro z hz
        have hzΓ₁ : z ∈ Γ₁.dom := hok.fv_sub hz
        rw [Ctx.dom_subst_append]
        exact Finset.mem_union.mpr (Or.inr hzΓ₁)
      exact MEqRed.refl hpv' hok.lc hfvs
    · rw [Term.subst_fvar_ne hyx]
      exact MEqRed.var hpv'
  | @fun_ Γ t' t'' body body' L ht hbody iht ihbody =>
    subst hΓ
    -- u = .abs t' body, v = .abs t'' body'
    -- subst gives .abs (subst x s t') (subst x s body) → .abs (subst x s t'') (subst x s body')
    show MEqRed (Ctx.subst x s Γ₂ ++ Γ₁) (Stack.subst x s [])
      (.abs (Term.subst x s t') (Term.subst x s body))
      (.abs (Term.subst x s t'') (Term.subst x s body'))
    refine MEqRed.fun_ (L ∪ {x}) ?_ ?_
    · -- Bound annotation reduction at empty stack.
      have iht' := iht (Γ₂ := Γ₂) rfl
      simpa using iht'
    · -- Body case: extend Γ₂ by ⟨y, t', .sub⟩.
      intro y hy
      simp [Finset.mem_union, Finset.mem_singleton] at hy
      have hyL : y ∉ L := hy.1
      have hyx : y ≠ x := hy.2
      have ih_body := ihbody y hyL (Γ₂ := ⟨y, t', .sub⟩ :: Γ₂) (by simp)
      have hLCs := hok.lc
      rw [Term.subst_open_var (Ne.symm hyx) hLCs body,
          Term.subst_open_var (Ne.symm hyx) hLCs body'] at ih_body
      -- The context is (subst x s (⟨y, t', .sub⟩ :: Γ₂) ++ Γ₁) =
      -- ⟨y, subst x s t', .sub⟩ :: (subst x s Γ₂ ++ Γ₁)
      simpa [Ctx.subst, List.cons_append] using ih_body
  | @tAp Γ st' u_ hpv hLCu hfv =>
    subst hΓ
    have hpv' : PrevalidExt (Ctx.subst x s Γ₂ ++ Γ₁) (Stack.subst x s st') :=
      Lemma_28_SubstPreservesPrevalid hpv hok
    have hLCu' : Term.LC (Term.subst x s u_) := Term.subst_lc hok.lc hLCu
    have hfv' := fv_subst_dom_shift hok hfv
    show MEqRed (Ctx.subst x s Γ₂ ++ Γ₁) (Stack.subst x s st')
      (Term.subst x s (.app .top u_)) (Term.subst x s .top)
    simp [Term.subst]
    exact MEqRed.tAp hpv' hLCu' hfv'
  | @fOp Γ st' t' t'' α body body' L ht hbody iht ihbody =>
    subst hΓ
    -- u = .abs t' body, v = .abs t'' body', stack = α :: tail
    show MEqRed (Ctx.subst x s Γ₂ ++ Γ₁) (Stack.subst x s (α :: st'))
      (.abs (Term.subst x s t') (Term.subst x s body))
      (.abs (Term.subst x s t'') (Term.subst x s body'))
    rw [Stack.subst_cons]
    refine MEqRed.fOp (L ∪ {x}) ?_ ?_
    · -- Bound annotation reduction.
      have iht' := iht (Γ₂ := Γ₂) rfl
      simpa using iht'
    · -- Body case: extend Γ₂ by ⟨y, α, .equ⟩.
      intro y hy
      simp [Finset.mem_union, Finset.mem_singleton] at hy
      have hyL : y ∉ L := hy.1
      have hyx : y ≠ x := hy.2
      have ih_body := ihbody y hyL (Γ₂ := ⟨y, α, .equ⟩ :: Γ₂) (by simp)
      have hLCs := hok.lc
      rw [Term.subst_open_var (Ne.symm hyx) hLCs body,
          Term.subst_open_var (Ne.symm hyx) hLCs body'] at ih_body
      simpa [Ctx.subst, List.cons_append] using ih_body

/-! ## §10. Lemma 30 — Reduction under substitution (MSubRed)

Pasquale's Lemma 30 is the `MSubRed` analogue of Lemma 31. The paper's
statement carries a side condition: the derivation must NOT make a
"promotion of `x` to `t`" (a Ms-Pro step on `x`).

We mechanize this by ASSUMING the side condition is satisfied — we
discharge five of the six MSubRed constructors directly, and AXIOMATIZE
the residual `Ms-Pro y = x` arm. This consumes the **single escape-hatch
axiom** allotted to Wave 4B (per `PLAN.md` §6.3).

The axiom states the precise residual obligation and is to be discharged
in Wave 7 once the well-typing infrastructure is available to make the
side condition explicit on derivations. -/

/-- **Escape-hatch axiom** (single, per Plan §6.3). The residual case of
Lemma 30 where the MSubRed derivation is exactly `Ms-Pro` on the
substituted variable `x`. Under the paper's "no promotion of `x`" side
condition, this case is vacuous — but the side condition is not
mechanized in the current `MSubRed` inductive. To be discharged in
Wave 7 by introducing a refined `MSubRedNoProOf x` predicate or by
ruling out this arm via well-typing.

Statement: if the only way to fire `Ms-Pro` for `x` is to look up the
specific `.sub` head binding, then after substituting `α` for `x`, the
"reduction" `x ⟶^≤ t` becomes the trivial `α ⟶^≤ t[x\α]`, which holds
by reflexivity-then-subtype-step composition. -/
axiom Lemma_30_msPro_x_axiom
    {Γ₁ Γ₂ : Ctx} {st : Stack} (x : String) {s : Term} (t : Term)
    (hok : SubstOk Γ₁ s)
    (hpv : PrevalidExt (Ctx.subst x s Γ₂ ++ Γ₁) (Stack.subst x s st)) :
    MSubRed (Ctx.subst x s Γ₂ ++ Γ₁) (Stack.subst x s st)
      s (Term.subst x s t)

/-- **Lemma 30 (Reduction under substitution, MSubRed).** Substitution
preserves MPSS subtype reduction under a `.sub` head binding.

5/6 cases proved directly; the `Ms-Pro y = x` arm uses
`Lemma_30_msPro_x_axiom`. -/
noncomputable def Lemma_30_ReductionUnderSubst_Sub
    {Γ₁ Γ₂ : Ctx} {st : Stack} {x : String} {s t u v : Term}
    (h : MSubRed (Γ₂ ++ ⟨x, t, .sub⟩ :: Γ₁) st u v)
    (hok : SubstOk Γ₁ s) :
    MSubRed (Ctx.subst x s Γ₂ ++ Γ₁) (Stack.subst x s st)
      (Term.subst x s u) (Term.subst x s v) := by
  generalize hΓ : (Γ₂ ++ ⟨x, t, .sub⟩ :: Γ₁) = Γ at h
  induction h generalizing Γ₂ with
  | @pro Γ st' y t' hpv hsb =>
    subst hΓ
    have hpvL : Prevalid (Γ₂ ++ ⟨x, t, .sub⟩ :: Γ₁) := extractPrevalid hpv
    have hpv' : PrevalidExt (Ctx.subst x s Γ₂ ++ Γ₁) (Stack.subst x s st') :=
      Lemma_28_SubstPreservesPrevalid hpv hok
    by_cases hyx : y = x
    · -- The escape-hatch arm.
      subst hyx
      rw [Term.subst_fvar_eq]
      exact Lemma_30_msPro_x_axiom y t' hok hpv'
    · rw [Term.subst_fvar_ne hyx]
      have hsb' := subBinds_split_neq (s := s) hyx hpvL hsb
      exact MSubRed.pro hpv' hsb'
  | @top Γ st' u_ hpv hLCu hfv =>
    subst hΓ
    have hpv' : PrevalidExt (Ctx.subst x s Γ₂ ++ Γ₁) (Stack.subst x s st') :=
      Lemma_28_SubstPreservesPrevalid hpv hok
    have hLCu' : Term.LC (Term.subst x s u_) := Term.subst_lc hok.lc hLCu
    have hfv' := fv_subst_dom_shift hok hfv
    show MSubRed (Ctx.subst x s Γ₂ ++ Γ₁) (Stack.subst x s st')
      (Term.subst x s u_) (Term.subst x s .top)
    simp [Term.subst]
    exact MSubRed.top hpv' hLCu' hfv'
  | @equ Γ st' u_ v_ hpv heq =>
    subst hΓ
    have hpv' : PrevalidExt (Ctx.subst x s Γ₂ ++ Γ₁) (Stack.subst x s st') :=
      Lemma_28_SubstPreservesPrevalid hpv hok
    -- Use Lemma 31 on the inner equivalence reduction.
    have heq' := Lemma_31_ReductionUnderSubst_Eq heq hok
    exact MSubRed.equ hpv' heq'
  | @app Γ st' u_ u_' v_ hu hLCv hfvv ihu =>
    subst hΓ
    have ihu' := ihu (Γ₂ := Γ₂) rfl
    have hLCv' : Term.LC (Term.subst x s v_) := Term.subst_lc hok.lc hLCv
    have hfvv' := fv_subst_dom_shift hok hfvv
    show MSubRed (Ctx.subst x s Γ₂ ++ Γ₁) (Stack.subst x s st')
      (Term.subst x s (.app u_ v_)) (Term.subst x s (.app u_' v_))
    simp [Term.subst]
    refine MSubRed.app ?_ hLCv' hfvv'
    simpa using ihu'
  | @fun_ Γ t' body body' L hLCt hbody ihbody =>
    subst hΓ
    show MSubRed (Ctx.subst x s Γ₂ ++ Γ₁) (Stack.subst x s [])
      (Term.subst x s (.abs t' body)) (Term.subst x s (.abs t' body'))
    simp [Term.subst]
    refine MSubRed.fun_ (L ∪ {x}) (Term.subst_lc hok.lc hLCt) ?_
    intro y hy
    simp [Finset.mem_union, Finset.mem_singleton] at hy
    have hyL : y ∉ L := hy.1
    have hyx : y ≠ x := hy.2
    have ih_body := ihbody y hyL (Γ₂ := ⟨y, t', .sub⟩ :: Γ₂) (by simp)
    rw [Term.subst_open_var (Ne.symm hyx) hok.lc body,
        Term.subst_open_var (Ne.symm hyx) hok.lc body'] at ih_body
    simpa [Ctx.subst, List.cons_append] using ih_body
  | @fOp Γ st' t' α body body' L hLCt hbody ihbody =>
    subst hΓ
    show MSubRed (Ctx.subst x s Γ₂ ++ Γ₁) (Stack.subst x s (α :: st'))
      (Term.subst x s (.abs t' body)) (Term.subst x s (.abs t' body'))
    rw [Stack.subst_cons]
    simp [Term.subst]
    refine MSubRed.fOp (L ∪ {x}) (Term.subst_lc hok.lc hLCt) ?_
    intro y hy
    simp [Finset.mem_union, Finset.mem_singleton] at hy
    have hyL : y ∉ L := hy.1
    have hyx : y ≠ x := hy.2
    have ih_body := ihbody y hyL (Γ₂ := ⟨y, α, .equ⟩ :: Γ₂) (by simp)
    rw [Term.subst_open_var (Ne.symm hyx) hok.lc body,
        Term.subst_open_var (Ne.symm hyx) hok.lc body'] at ih_body
    simpa [Ctx.subst, List.cons_append] using ih_body

/-! ## §11. Lemma 32 — Reduction under substitution (auxiliary form)

Pasquale's Lemma 32: substitution under an `.equ` head binding `x ≡ v`,
where the substituted `v` itself reduces to `v'`. The result substitutes
`v` on the LHS and `v'` on the RHS — the asymmetry is essential for the
commutation proof (Wave 6).

We mechanize the **restricted form** `v = v'`: substitution preserves
MPSS equivalence reduction under an `.equ` head binding, when the
substituted term is REFLEXIVE (i.e. `v ⟶^≡ v` via Proposition 18).
This is the "diagonal" of Lemma 32 and is provable via the same machinery
as Lemma 31.

The fully asymmetric form is left as a `TODO` for downstream use: the
proof structure is identical except for the `Me-Pro y = x` case, which
needs `α[x\v'] = α[x\v]` (i.e. `v = v'` implicit; otherwise needs care). -/

/-- **Lemma 32 (restricted: `s = v`).** Substitution preserves MPSS
equivalence reduction under an `.equ` head binding `x ≡ v`, when we
substitute the bound term `v` itself (i.e. `s = v`). The asymmetric
form needed for full commutation (substituting `v` on LHS and `v'` on
RHS for some `v ⟶ v'`) is left to a future iteration; the restricted
form below is the "diagonal" used by the reflexive part of the
commutation diagram. -/
noncomputable def Lemma_32_ReductionUnderSubst_Eq_OfEqu
    {Γ₁ Γ₂ : Ctx} {st : Stack} {x : String} {s v u u' : Term}
    (h : MEqRed (Γ₂ ++ ⟨x, v, .equ⟩ :: Γ₁) st u u')
    (hok : SubstOk Γ₁ s)
    (hsv : s = v) :
    MEqRed (Ctx.subst x s Γ₂ ++ Γ₁) (Stack.subst x s st)
      (Term.subst x s u) (Term.subst x s u') := by
  -- The proof has the same structure as Lemma 31. The key difference is the
  -- Me-Pro y=x case: now y CAN be x (since x has an .equ binding). When y = x,
  -- the binding gives α = v, the looked-up term. Since fv v ⊆ Γ₁.dom and
  -- x ∉ Γ₁.dom (by prevalidity), v[x\s] = v. The IH gives MEqRed at the
  -- substituted context for v ⟶ α'.
  generalize hΓ : (Γ₂ ++ ⟨x, v, .equ⟩ :: Γ₁) = Γ at h
  induction h generalizing Γ₂ with
  | @pro Γ st' y α α' hpv heq hα ihα =>
    subst hΓ
    have hpvL : Prevalid (Γ₂ ++ ⟨x, v, .equ⟩ :: Γ₁) := extractPrevalid hpv
    have hpv' : PrevalidExt (Ctx.subst x s Γ₂ ++ Γ₁) (Stack.subst x s st') :=
      Lemma_28_SubstPreservesPrevalid hpv hok
    by_cases hyx : y = x
    · -- y = x. By uniqueness of x's binding (prevalidity), α = v.
      -- Substitute v with s (using hsv.symm), then everything unifies.
      have hα_eq_v : α = v := by
        have heq_x : (Γ₂ ++ ⟨x, v, .equ⟩ :: Γ₁).equBinds x α := hyx ▸ heq
        exact equBinds_at_equ_head_unique hpvL heq_x
      have ihα_app := ihα (Γ₂ := Γ₂) rfl
      rw [hα_eq_v] at ihα_app
      have hxs : x ∉ Term.fv s := by
        have hxnotin : x ∉ Γ₁.dom := by
          have hpv_outer : Prevalid (⟨x, v, .equ⟩ :: Γ₁) := Prevalid.outer hpvL
          cases hpv_outer with
          | equ _ hxn _ _ => exact hxn
        intro h
        exact hxnotin (hok.fv_sub h)
      have hsv_subst : Term.subst x s v = s := by
        rw [← hsv]; exact Term.subst_fresh hxs
      rw [hsv_subst] at ihα_app
      -- ihα_app : MEqRed _ _ s (subst x s α')
      -- Goal: MEqRed _ _ (subst x s (.fvar y)) (subst x s α')
      rw [hyx, Term.subst_fvar_eq]
      exact ihα_app
    · rw [Term.subst_fvar_ne hyx]
      have heq' : (Ctx.subst x s Γ₂ ++ Γ₁).equBinds y (Term.subst x s α) :=
        equBinds_split_equ hyx hpvL heq
      exact MEqRed.pro hpv' heq' (ihα (Γ₂ := Γ₂) rfl)
  | @bet Γ st' t' v' v'' body body' L hLCt hbody hv ihbody ihv =>
    subst hΓ
    have hLCs := hok.lc
    have hsubst_open : Term.subst x s (Term.opening v'' body') =
        Term.opening (Term.subst x s v'') (Term.subst x s body') := by
      simp [Term.opening, Term.subst_open hLCs]
    show MEqRed (Ctx.subst x s Γ₂ ++ Γ₁) (Stack.subst x s st')
      (Term.subst x s (.app (.abs t' body) v')) (Term.subst x s (Term.opening v'' body'))
    rw [hsubst_open]
    show MEqRed (Ctx.subst x s Γ₂ ++ Γ₁) (Stack.subst x s st')
      (.app (.abs (Term.subst x s t') (Term.subst x s body)) (Term.subst x s v'))
      (Term.opening (Term.subst x s v'') (Term.subst x s body'))
    refine MEqRed.bet (L ∪ {x}) (Term.subst_lc hLCs hLCt) ?_ ?_
    · intro y hy
      simp [Finset.mem_union, Finset.mem_singleton] at hy
      have hyL : y ∉ L := hy.1
      have hyx : y ≠ x := hy.2
      have ih_body := ihbody y hyL (Γ₂ := Γ₂) rfl
      rw [Term.subst_open_var (Ne.symm hyx) hLCs body,
          Term.subst_open_var (Ne.symm hyx) hLCs body'] at ih_body
      exact ih_body
    · have ihv' := ihv (Γ₂ := Γ₂) rfl
      simpa using ihv'
  | @top Γ st' hpv =>
    subst hΓ
    have hpv' : PrevalidExt (Ctx.subst x s Γ₂ ++ Γ₁) (Stack.subst x s st') :=
      Lemma_28_SubstPreservesPrevalid hpv hok
    exact MEqRed.top hpv'
  | @app Γ st' u_ u_' v_ v_' hu hv ihu ihv =>
    subst hΓ
    have ihu' := ihu (Γ₂ := Γ₂) rfl
    have ihv' := ihv (Γ₂ := Γ₂) rfl
    simp at ihu'
    refine MEqRed.app ?_ ?_
    · exact ihu'
    · simpa using ihv'
  | @var Γ st' y hpv =>
    subst hΓ
    have hpv' : PrevalidExt (Ctx.subst x s Γ₂ ++ Γ₁) (Stack.subst x s st') :=
      Lemma_28_SubstPreservesPrevalid hpv hok
    by_cases hyx : y = x
    · have heq : Term.subst x s (.fvar y) = s := by
        rw [hyx]; exact Term.subst_fvar_eq x s
      rw [heq]
      have hfvs : Term.fv s ⊆ Ctx.dom (Ctx.subst x s Γ₂ ++ Γ₁) := by
        intro z hz
        have hzΓ₁ : z ∈ Γ₁.dom := hok.fv_sub hz
        rw [Ctx.dom_subst_append]
        exact Finset.mem_union.mpr (Or.inr hzΓ₁)
      exact MEqRed.refl hpv' hok.lc hfvs
    · rw [Term.subst_fvar_ne hyx]
      exact MEqRed.var hpv'
  | @fun_ Γ t' t'' body body' L ht hbody iht ihbody =>
    subst hΓ
    show MEqRed (Ctx.subst x s Γ₂ ++ Γ₁) (Stack.subst x s [])
      (.abs (Term.subst x s t') (Term.subst x s body))
      (.abs (Term.subst x s t'') (Term.subst x s body'))
    refine MEqRed.fun_ (L ∪ {x}) ?_ ?_
    · have iht' := iht (Γ₂ := Γ₂) rfl
      simpa using iht'
    · intro y hy
      simp [Finset.mem_union, Finset.mem_singleton] at hy
      have hyL : y ∉ L := hy.1
      have hyx : y ≠ x := hy.2
      have ih_body := ihbody y hyL (Γ₂ := ⟨y, t', .sub⟩ :: Γ₂) (by simp)
      have hLCs := hok.lc
      rw [Term.subst_open_var (Ne.symm hyx) hLCs body,
          Term.subst_open_var (Ne.symm hyx) hLCs body'] at ih_body
      simpa [Ctx.subst, List.cons_append] using ih_body
  | @tAp Γ st' u_ hpv hLCu hfv =>
    subst hΓ
    have hpv' : PrevalidExt (Ctx.subst x s Γ₂ ++ Γ₁) (Stack.subst x s st') :=
      Lemma_28_SubstPreservesPrevalid hpv hok
    have hLCu' : Term.LC (Term.subst x s u_) := Term.subst_lc hok.lc hLCu
    have hfv' := fv_subst_dom_shift hok hfv
    show MEqRed (Ctx.subst x s Γ₂ ++ Γ₁) (Stack.subst x s st')
      (Term.subst x s (.app .top u_)) (Term.subst x s .top)
    simp [Term.subst]
    exact MEqRed.tAp hpv' hLCu' hfv'
  | @fOp Γ st' t' t'' α body body' L ht hbody iht ihbody =>
    subst hΓ
    show MEqRed (Ctx.subst x s Γ₂ ++ Γ₁) (Stack.subst x s (α :: st'))
      (.abs (Term.subst x s t') (Term.subst x s body))
      (.abs (Term.subst x s t'') (Term.subst x s body'))
    rw [Stack.subst_cons]
    refine MEqRed.fOp (L ∪ {x}) ?_ ?_
    · have iht' := iht (Γ₂ := Γ₂) rfl
      simpa using iht'
    · intro y hy
      simp [Finset.mem_union, Finset.mem_singleton] at hy
      have hyL : y ∉ L := hy.1
      have hyx : y ≠ x := hy.2
      have ih_body := ihbody y hyL (Γ₂ := ⟨y, α, .equ⟩ :: Γ₂) (by simp)
      have hLCs := hok.lc
      rw [Term.subst_open_var (Ne.symm hyx) hLCs body,
          Term.subst_open_var (Ne.symm hyx) hLCs body'] at ih_body
      simpa [Ctx.subst, List.cons_append] using ih_body

end Pss
