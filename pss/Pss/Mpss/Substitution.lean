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
theorem equBinds_ne_x_at_sub_head
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
theorem equBinds_split
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
theorem subBinds_split_neq
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

/-- Uniqueness: the `.sub` head binding for `x` is the only one. Mirrors
`equBinds_at_equ_head_unique`. Used by Renaming for the `Ms-Pro y = x` arm. -/
theorem subBinds_at_sub_head_unique
    {Γ₁ Γ₂ : Ctx} {x : String} {t b : Term}
    (hpv : Prevalid (Γ₂ ++ ⟨x, t, .sub⟩ :: Γ₁))
    (hb : (Γ₂ ++ ⟨x, t, .sub⟩ :: Γ₁).subBinds x b) : b = t := by
  induction Γ₂ with
  | nil =>
    have hb' : Ctx.subBinds (⟨x, t, .sub⟩ :: Γ₁) x b := by simpa using hb
    simp [Ctx.subBinds, Ctx.lookupSub] at hb'
    exact hb'.symm
  | cons e rest ih =>
    have hpv_eq : (e :: rest ++ ⟨x, t, .sub⟩ :: Γ₁) =
        (e :: (rest ++ ⟨x, t, .sub⟩ :: Γ₁)) := by simp
    rw [hpv_eq] at hpv
    simp [Ctx.subBinds, Ctx.lookupSub_cons] at hb
    by_cases he : e.name = x
    · cases he_kind : e.kind with
      | sub =>
        exfalso
        have hyfresh : e.name ∉ Ctx.dom (rest ++ ⟨x, t, .sub⟩ :: Γ₁) := by
          cases hpv with
          | sub _ hen _ _ => exact hen
          | equ _ hen _ _ => exact hen
        apply hyfresh
        rw [he, Ctx.dom_append, Ctx.dom_cons]
        apply Finset.mem_union.mpr; right
        exact Finset.mem_insert_self _ _
      | equ => simp [he, he_kind] at hb
    · simp [he] at hb
      exact ih hpv.tail hb

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
by reflexivity-then-subtype-step composition.

## Status (2026-04-29)

Commit `172b6b6` introduced `Lemma_30_msPro_x` (in `AvoidsPro.lean`):
a leaf-level theorem that takes an `msAvoidsPro h x = true` witness on
the `pro` derivation and discharges the residual obligation by
`False.elim` (the witness immediately contradicts `y = x`).

Wiring `Lemma_30_msPro_x` here in place of `Lemma_30_msPro_x_axiom`
requires threading an `msAvoidsPro h x = true` premise through the
WHOLE `Lemma_30_ReductionUnderSubst_Sub` proof (not just the leaf):

* The axiom is invoked at the `pro y = x` arm of the induction on
  `h : MSubRed (...) st u v`. To replace it with `Lemma_30_msPro_x`,
  the leaf needs the `msAvoidsPro` witness on the SPECIFIC `MSubRed.pro
  hpv hsb` step in scope. That witness must come from a top-level
  `havoid : msAvoidsPro h x = true` premise added to the function.
* The `app` arm requires `msAvoidsPro hu x = true` on the operator
  derivation (immediately discharged by `msAvoidsPro_app`).
* The cofinite arms (`fun_`, `fOp`) need to thread the avoidance
  through to the body IH at an arbitrary fresh `y ∉ L`. The current
  `msAvoidsPro` definition reduces the cofinite cases by sampling
  `pickFresh L` (a single canonical fresh name); to recover the
  avoidance witness at an arbitrary `y ∉ L`, an alpha-equivariance
  lemma `msAvoidsPro (hbody y₁ _) x = msAvoidsPro (hbody y₂ _) x` is
  needed. That is the residual work to fully replace the axiom here.

The blocker for **removing the axiom from Theorem 5's dep list** is
NOT the leaf discharge — `Lemma_30_msPro_x` already exists. The blocker
is the SOLE caller `Pss.Mpss.TypeSafety._S_lf2` (in `Lemma_7_*`'s
`WSubM.lf2` arm), which calls `Lemma_30_ReductionUnderSubst_Sub hred
hok` without an avoidance witness. Adding the `havoid` premise here
breaks that call site; the call site cannot independently produce an
`msAvoidsPro hred xout = true` because the `WSubM.lf2` constructor
carries no such side condition. The fix has to land in TypeSafety
(propagating the avoidance through the `_S_motive_sub` motive) before
the axiom can be removed here.

For the present revision the axiom remains; `Lemma_30_msPro_x`
documents the exact leaf-level discharge that becomes available once
the avoidance premise is threaded.

**Cross-ref:** see `AXIOMS.md` axiom #4 for status / paper / discharge
plan; this is currently in the `#print axioms` closure of Theorem 5
only. -/
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

/-! ## §12. No-context-extension substitution lemma

The substitution lemmas above (Lemmas 30/31/32) all require the substituted
variable `x` to be context-bound (via `Γ₂ ++ ⟨x, _, _⟩ :: Γ₁`). The
`Bet × *` cases of `Lemma_2_DiamondMEqRed_core` need a different shape:
the substituted variable `y` is bound by a λ in the term, NOT by the
context. So we need a `MEqRed.subst` that substitutes for a FRESH name `y`
not in `Γ.dom`.

Since `y ∉ Γ.dom`:
* `Me-Pro` lookups produce names in `Γ.dom`, so the looked-up variable
  is `≠ y`.
* The looked-up bound `α` has `fv α ⊆ Γ.dom`, so substitution by `y`
  is a no-op on `α`.

The single non-trivial leaf is `Me-Var x` with `x = y`: `.fvar y` becomes
`w` and we close via `MEqRed.refl`. -/

/-- Helper: a `.equ` binding implies the bound name is in the context's
domain. -/
private theorem dom_of_equBinds {Γ : Ctx} {x : String} {α : Term}
    (hb : Γ.equBinds x α) : x ∈ Γ.dom := by
  induction Γ with
  | nil => simp [Ctx.equBinds, Ctx.lookupEqu] at hb
  | cons e rest ih =>
    rw [Ctx.dom_cons]
    by_cases he : e.name = x
    · rw [he]; exact Finset.mem_insert_self _ _
    · have hb' : Ctx.equBinds rest x α := by
        simp [Ctx.equBinds, Ctx.lookupEqu_cons, he] at hb
        exact hb
      exact Finset.mem_insert_of_mem (ih hb')

/-- Helper: a `.sub` binding implies the bound name is in the context's
domain. -/
private theorem dom_of_subBinds {Γ : Ctx} {x : String} {t : Term}
    (hb : Γ.subBinds x t) : x ∈ Γ.dom := by
  induction Γ with
  | nil => simp [Ctx.subBinds, Ctx.lookupSub] at hb
  | cons e rest ih =>
    rw [Ctx.dom_cons]
    by_cases he : e.name = x
    · rw [he]; exact Finset.mem_insert_self _ _
    · have hb' : Ctx.subBinds rest x t := by
        simp [Ctx.subBinds, Ctx.lookupSub_cons, he] at hb
        exact hb
      exact Finset.mem_insert_of_mem (ih hb')

/-- Helper: lift `PrevalidExt Γ s` over a `cons` extension by checking
each stack entry remains scoped under the larger domain. Just monotonicity
of subset for `Finset` membership. -/
private theorem PrevalidExt.weaken_cons {Γ : Ctx} {e : CtxEntry}
    (hpvE : Prevalid (e :: Γ)) {s : Stack} (hpv : PrevalidExt Γ s) :
    PrevalidExt (e :: Γ) s := by
  induction s with
  | nil => exact PrevalidExt.nil hpvE
  | cons α tail ih =>
    cases hpv with
    | cons hpvr hLCα hfvα =>
      refine PrevalidExt.cons (ih hpvr) hLCα ?_
      intro z hz
      rw [Ctx.dom_cons]
      exact Finset.mem_insert_of_mem (hfvα hz)

/-- Helper: descend `PrevalidExt (e :: Γ) s` to `PrevalidExt Γ s`, given
that no stack entry mentions `e.name`. (Used in the helper that extracts
`PrevalidExt Γ s` from an `MEqRed Γ s u v` derivation, in the `fOp`
case where the body has been opened with a fresh name we control.) -/
private theorem PrevalidExt.descend_cons {Γ : Ctx} {s : Stack} {e : CtxEntry}
    (hpvΓ : Prevalid Γ)
    (hpv : PrevalidExt (e :: Γ) s)
    (hfresh : ∀ α ∈ s, e.name ∉ Term.fv α) :
    PrevalidExt Γ s := by
  induction s with
  | nil => exact PrevalidExt.nil hpvΓ
  | cons α tail ih =>
    cases hpv with
    | cons hpvr hLCα hfvα =>
      have hfresh_tail : ∀ β ∈ tail, e.name ∉ Term.fv β :=
        fun β hβ => hfresh β (List.mem_cons_of_mem α hβ)
      have hfresh_head : e.name ∉ Term.fv α := hfresh α (List.mem_cons_self _ _)
      have ih' := ih hpvr hfresh_tail
      have hfvα' : Term.fv α ⊆ Γ.dom := by
        intro z hz
        have hzext : z ∈ Ctx.dom (e :: Γ) := hfvα hz
        rw [Ctx.dom_cons] at hzext
        rcases Finset.mem_insert.mp hzext with hzn | hzΓ
        · exact absurd hz (hzn ▸ hfresh_head)
        · exact hzΓ
      exact PrevalidExt.cons ih' hLCα hfvα'

/-- Helper: extract `Prevalid Γ` from any `MEqRed Γ s u v`. -/
private theorem MEqRed.prevalid {Γ : Ctx} {s : Stack} {u v : Term}
    (h : MEqRed Γ s u v) : Prevalid Γ := by
  induction h with
  | @pro Γ st x α α' hpv _ _ _ => exact extractPrevalid hpv
  | @bet Γ s t v v' body body' L _ _ _ _ ihv => exact ihv
  | @top Γ s hpv => exact extractPrevalid hpv
  | @app Γ s u u' v v' _ _ _ ihv => exact ihv
  | @var Γ s x hpv => exact extractPrevalid hpv
  | @fun_ Γ t t' body body' L _ _ iht _ => exact iht
  | @tAp Γ s u hpv _ _ => exact extractPrevalid hpv
  | @fOp Γ s t t' α body body' L _ _ iht _ => exact iht

/-- Pop the head of a non-empty `PrevalidExt`. -/
private theorem PrevalidExt.tail {Γ : Ctx} {s : Stack} {α : Term}
    (h : PrevalidExt Γ (α :: s)) : PrevalidExt Γ s := by
  cases h with
  | cons hpvr _ _ => exact hpvr

/-- Sum of `fv` over a stack. -/
private def Stack.fvAll : Stack → Finset String
  | [] => ∅
  | α :: tail => Term.fv α ∪ Stack.fvAll tail

private lemma Stack.mem_fvAll {st : Stack} {α : Term} (hα : α ∈ st)
    {z : String} (hz : z ∈ Term.fv α) : z ∈ Stack.fvAll st := by
  induction st with
  | nil => exact (List.not_mem_nil _ hα).elim
  | cons β tail ih =>
    show z ∈ Term.fv β ∪ Stack.fvAll tail
    rcases List.mem_cons.mp hα with heq | hα'
    · subst heq
      exact Finset.mem_union.mpr (Or.inl hz)
    · exact Finset.mem_union.mpr (Or.inr (ih hα'))

/-- Extract `PrevalidExt Γ s` from `MEqRed Γ s u v`. The `fOp` case
picks a cofinite-fresh `x` outside `L ∪ Γ.dom ∪ Stack.fvAll s` so the body
IH's stack remains valid after descending past the new entry. -/
private theorem MEqRed.prevalidExt {Γ : Ctx} {s : Stack} {u v : Term}
    (h : MEqRed Γ s u v) : PrevalidExt Γ s := by
  induction h with
  | @pro Γ s x α α' hpv _ _ _ => exact hpv
  | @bet Γ s t v0 v0' body body' L _ _ _ ihbody _ =>
    classical
    obtain ⟨x, hx⟩ := Term.exists_fresh L
    exact ihbody x hx
  | @app Γ s u u' v v' _ _ ihu _ =>
    exact PrevalidExt.tail ihu
  | top hpv => exact hpv
  | var hpv => exact hpv
  | @fun_ Γ t t' body body' L _ _ iht _ => exact iht
  | tAp hpv _ _ => exact hpv
  | @fOp Γ s t t' α body body' L _ _ iht ihbody =>
    classical
    obtain ⟨x, hx⟩ := Term.exists_fresh (L ∪ Γ.dom ∪ Stack.fvAll s)
    have hxL : x ∉ L := fun h' => hx (by
      apply Finset.mem_union.mpr; left
      apply Finset.mem_union.mpr; left; exact h')
    have hxΓ : x ∉ Γ.dom := fun h' => hx (by
      apply Finset.mem_union.mpr; left
      apply Finset.mem_union.mpr; right; exact h')
    have hxFV : x ∉ Stack.fvAll s := fun h' => hx (by
      apply Finset.mem_union.mpr; right; exact h')
    have hpvExt : PrevalidExt (⟨x, α, .equ⟩ :: Γ) s := ihbody x hxL
    have hfreshAll : ∀ β ∈ s, x ∉ Term.fv β := by
      intro β hβ hzfv
      exact hxFV (Stack.mem_fvAll hβ hzfv)
    have hpvΓ : Prevalid Γ := extractPrevalid iht
    have hpvS : PrevalidExt Γ s :=
      PrevalidExt.descend_cons hpvΓ hpvExt hfreshAll
    have hpvExtBare : Prevalid (⟨x, α, .equ⟩ :: Γ) := extractPrevalid hpvExt
    cases hpvExtBare with
    | equ _ _ hfvα hLCα =>
      exact PrevalidExt.cons hpvS hLCα hfvα

/-- **Substitution where the variable is FREE (not context-bound).**

Substitute `w` for free occurrences of `y` in both sides of the
derivation. Since `y ∉ Γ.dom`:
* No lookup hits `y` (lookups produce names in `Γ.dom`).
* All lookup results have `fv ⊆ Γ.dom` so are unaffected by `subst y w`.

The single non-trivial leaf is `Me-Var x` with `x = y`: `.fvar y`
becomes `w`, closed via `MEqRed.refl`. -/
noncomputable def MEqRed.subst {Γ : Ctx} {s : Stack} {u v : Term}
    (y : String) (w : Term)
    (hy_not_dom : y ∉ Γ.dom)
    (hw_lc : Term.LC w) (hw_fv : Term.fv w ⊆ Γ.dom)
    (h : MEqRed Γ s u v) :
    MEqRed Γ s (Term.subst y w u) (Term.subst y w v) := by
  induction h with
  | @pro Γ st x α α' hpv heq hα ihα =>
    have hxdom : x ∈ Γ.dom := dom_of_equBinds heq
    have hxy : x ≠ y := fun heqxy => hy_not_dom (heqxy ▸ hxdom)
    have hfvα : Term.fv α ⊆ Γ.dom :=
      Prevalid.fv_lookupEqu (extractPrevalid hpv) heq
    have hyα : y ∉ Term.fv α := fun h' => hy_not_dom (hfvα h')
    have hα_fix : Term.subst y w α = α := Term.subst_fresh hyα
    have ihα' := ihα hy_not_dom hw_fv
    rw [hα_fix] at ihα'
    rw [Term.subst_fvar_ne hxy]
    exact MEqRed.pro hpv heq ihα'
  | @bet Γ st t v0 v0' body body' L hLCt hbody hv ihbody ihv =>
    have hsubst_open : Term.subst y w (Term.opening v0' body') =
        Term.opening (Term.subst y w v0') (Term.subst y w body') := by
      simp [Term.opening, Term.subst_open hw_lc]
    show MEqRed Γ st
      (Term.subst y w (.app (.abs t body) v0))
      (Term.subst y w (Term.opening v0' body'))
    rw [hsubst_open]
    show MEqRed Γ st
      (.app (.abs (Term.subst y w t) (Term.subst y w body)) (Term.subst y w v0))
      (Term.opening (Term.subst y w v0') (Term.subst y w body'))
    refine MEqRed.bet (L ∪ {y}) (Term.subst_lc hw_lc hLCt) ?_ ?_
    · intro x hx
      simp [Finset.mem_union, Finset.mem_singleton] at hx
      have hxL : x ∉ L := hx.1
      have hxy : x ≠ y := hx.2
      have ihb := ihbody x hxL hy_not_dom hw_fv
      rw [Term.subst_open_var (Ne.symm hxy) hw_lc body,
          Term.subst_open_var (Ne.symm hxy) hw_lc body'] at ihb
      exact ihb
    · exact ihv hy_not_dom hw_fv
  | @top Γ st hpv =>
    exact MEqRed.top hpv
  | @app Γ st u_ u_' v_ v_' hu hv ihu ihv =>
    show MEqRed Γ st (Term.subst y w (.app u_ v_)) (Term.subst y w (.app u_' v_'))
    simp only [Term.subst]
    -- ihu : MEqRed Γ (v_::st) (subst y w u_) (subst y w u_').
    -- Need MEqRed Γ ((subst y w v_)::st) ...; rewrite using subst y w v_ = v_.
    have hpv_u : PrevalidExt Γ (v_ :: st) := MEqRed.prevalidExt hu
    have hfv_v : Term.fv v_ ⊆ Γ.dom := by
      cases hpv_u with
      | cons _ _ hfvv => exact hfvv
    have hyv : y ∉ Term.fv v_ := fun h' => hy_not_dom (hfv_v h')
    have hv_fix : Term.subst y w v_ = v_ := Term.subst_fresh hyv
    have ihu' := ihu hy_not_dom hw_fv
    rw [← hv_fix] at ihu'
    exact MEqRed.app ihu' (ihv hy_not_dom hw_fv)
  | @var Γ st x hpv =>
    by_cases hxy : x = y
    · have heq : Term.subst y w (.fvar x) = w := by
        rw [hxy]; exact Term.subst_fvar_eq y w
      rw [heq]
      exact MEqRed.refl hpv hw_lc hw_fv
    · rw [Term.subst_fvar_ne hxy]
      exact MEqRed.var hpv
  | @fun_ Γ t' t'' body body' L ht hbody iht ihbody =>
    show MEqRed Γ []
      (.abs (Term.subst y w t') (Term.subst y w body))
      (.abs (Term.subst y w t'') (Term.subst y w body'))
    -- For Me-Fun, the body context entry uses (subst y w t'), so we need to convert
    -- ihbody's context entry from t' to subst y w t'. They are equal since
    -- y ∉ fv t' (from fv t' ⊆ Γ.dom, extractable via MEqRed.prevalidExt of iht's
    -- inner derivation — but iht is the IH, not the original. Use ht instead.)
    have hpv_t : PrevalidExt Γ [] := MEqRed.prevalidExt ht
    have hpv_t_bare : Prevalid Γ := extractPrevalid hpv_t
    -- From ht : MEqRed Γ [] t' t'', extract a leaf with PrevalidExt Γ []. This gives
    -- Prevalid Γ but not fv t' ⊆ Γ.dom directly. Use AvoidsPro lemmas? No, simpler:
    -- the body derivation hbody x hx is at ⟨x, t', .sub⟩ :: Γ; extracting Prevalid
    -- gives fv t' ⊆ Γ.dom.
    classical
    let x0 : String := Classical.choose (Term.exists_fresh L)
    have hx0 : x0 ∉ L := Classical.choose_spec (Term.exists_fresh L)
    have hbody_x0 : MEqRed (⟨x0, t', .sub⟩ :: Γ) [] (body^[x0]) (body'^[x0]) :=
      hbody x0 hx0
    have hpv_b : Prevalid (⟨x0, t', .sub⟩ :: Γ) :=
      MEqRed.prevalid hbody_x0
    have hfv_t' : Term.fv t' ⊆ Γ.dom := by
      cases hpv_b with
      | sub _ _ hfv _ => exact hfv
    have hyt' : y ∉ Term.fv t' := fun h' => hy_not_dom (hfv_t' h')
    have ht'_fix : Term.subst y w t' = t' := Term.subst_fresh hyt'
    refine MEqRed.fun_ (L ∪ {y} ∪ Γ.dom) ?_ ?_
    · exact iht hy_not_dom hw_fv
    · intro x hx
      simp only [Finset.mem_union, Finset.mem_singleton] at hx
      have hxL : x ∉ L := fun h' => hx (Or.inl (Or.inl h'))
      have hxy : x ≠ y := fun h' => hx (Or.inl (Or.inr (by simp [h'])))
      have hxΓ : x ∉ Γ.dom := fun h' => hx (Or.inr h')
      have hy_not_dom_ext : y ∉ Ctx.dom (⟨x, t', .sub⟩ :: Γ) := by
        rw [Ctx.dom_cons]
        intro hin
        rcases Finset.mem_insert.mp hin with hyx | hyΓ
        · exact hxy.symm hyx
        · exact hy_not_dom hyΓ
      have hw_fv_ext : Term.fv w ⊆ Ctx.dom (⟨x, t', .sub⟩ :: Γ) := by
        intro z hz
        rw [Ctx.dom_cons]
        exact Finset.mem_insert_of_mem (hw_fv hz)
      have ihb := ihbody x hxL hy_not_dom_ext hw_fv_ext
      rw [Term.subst_open_var (Ne.symm hxy) hw_lc body,
          Term.subst_open_var (Ne.symm hxy) hw_lc body'] at ihb
      -- Convert ihb's context entry t' to subst y w t' (no-op).
      rw [ht'_fix.symm] at ihb
      exact ihb
  | @tAp Γ st u_ hpv hLCu hfv =>
    have hLCu' : Term.LC (Term.subst y w u_) := Term.subst_lc hw_lc hLCu
    have hfv' : Term.fv (Term.subst y w u_) ⊆ Γ.dom := by
      intro z hz
      have hsub := Term.fv_subst_subset y w u_ hz
      rcases Finset.mem_union.mp hsub with hsd | hsd
      · exact hfv (Finset.mem_sdiff.mp hsd).1
      · exact hw_fv hsd
    show MEqRed Γ st (Term.subst y w (.app .top u_)) (Term.subst y w .top)
    simp [Term.subst]
    exact MEqRed.tAp hpv hLCu' hfv'
  | @fOp Γ st t' t'' α body body' L ht hbody iht ihbody =>
    show MEqRed Γ (α :: st)
      (.abs (Term.subst y w t') (Term.subst y w body))
      (.abs (Term.subst y w t'') (Term.subst y w body'))
    refine MEqRed.fOp (L ∪ {y} ∪ Γ.dom) ?_ ?_
    · exact iht hy_not_dom hw_fv
    · intro x hx
      simp only [Finset.mem_union, Finset.mem_singleton] at hx
      have hxL : x ∉ L := fun h' => hx (Or.inl (Or.inl h'))
      have hxy : x ≠ y := fun h' => hx (Or.inl (Or.inr (by simp [h'])))
      have hxΓ : x ∉ Γ.dom := fun h' => hx (Or.inr h')
      have hy_not_dom_ext : y ∉ Ctx.dom (⟨x, α, .equ⟩ :: Γ) := by
        rw [Ctx.dom_cons]
        intro hin
        rcases Finset.mem_insert.mp hin with hyx | hyΓ
        · exact hxy.symm hyx
        · exact hy_not_dom hyΓ
      have hw_fv_ext : Term.fv w ⊆ Ctx.dom (⟨x, α, .equ⟩ :: Γ) := by
        intro z hz
        rw [Ctx.dom_cons]
        exact Finset.mem_insert_of_mem (hw_fv hz)
      have ihb := ihbody x hxL hy_not_dom_ext hw_fv_ext
      rw [Term.subst_open_var (Ne.symm hxy) hw_lc body,
          Term.subst_open_var (Ne.symm hxy) hw_lc body'] at ihb
      exact ihb

/-- **Bet-friendly substitution.** Re-expression of `MEqRed.subst` via
`subst_intro`: a derivation at `body^[y]` becomes a derivation at
`Term.opening v body`.

Used in the `Bet × *` cases of `Lemma_2_DiamondMEqRed_core` to commute
β-substitution past closing reductions. -/
noncomputable def Lemma_31_NoExt {Γ : Ctx} {s : Stack} {v body body' : Term}
    (y : String)
    (hy_not_dom : y ∉ Γ.dom)
    (hy_not_fv_body : y ∉ Term.fv body)
    (hy_not_fv_body' : y ∉ Term.fv body')
    (hv : Term.LC v) (hv_fv : Term.fv v ⊆ Γ.dom)
    (hbody : MEqRed Γ s (body^[y]) (body'^[y])) :
    MEqRed Γ s (Term.opening v body) (Term.opening v body') := by
  -- subst_intro: opening v body = subst y v (body^[y]), and similarly for body'.
  rw [Term.subst_intro hy_not_fv_body hv,
      Term.subst_intro hy_not_fv_body' hv]
  exact MEqRed.subst y v hy_not_dom hv hv_fv hbody

end Pss
