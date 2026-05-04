import Pss.Context.DeBruijn
import Mathlib.Logic.Relation

/-! # `Pss.Mpss.DeBruijnReductions` — de Bruijn MPSS reductions

This is the first reduction-side artifact for the de Bruijn refactor. It is
standalone under `Pss.DeBruijn` and does not modify the locally-nameless MPSS
relations.

The important shape change is in binder rules: the locally-nameless cofinite
premises become single derivations under an extended nameless context.
-/

namespace Pss
namespace DeBruijn

/-- MPSS equivalence reduction in de Bruijn form. -/
inductive MEqRed : Ctx → Stack → Term → Term → Type where
  /-- **Me-Pro**: promote a variable through an equivalence binding. -/
  | pro {Γ : Ctx} {s : Stack} {i : Nat} {α α' : Term} :
      PrevalidExt Γ s →
      Γ.equBinds i α →
      MEqRed Γ s α α' →
      MEqRed Γ s (.bvar i) α'

  /-- **Me-Bet**: β-step. The body derivation is a single proof under the
  context extended by the abstraction bound. -/
  | bet {Γ : Ctx} {s : Stack} {t v v' body body' : Term} :
      Term.Scoped Γ.depth t →
      MEqRed ({ bound := t, kind := .sub } :: Γ) (Stack.shift 0 s) body body' →
      MEqRed Γ [] v v' →
      MEqRed Γ s (.app (.abs t body) v) (Term.instantiate 0 v' body')

  /-- **Me-Top**. -/
  | top {Γ : Ctx} {s : Stack} :
      PrevalidExt Γ s →
      MEqRed Γ s .top .top

  /-- **Me-App**. -/
  | app {Γ : Ctx} {s : Stack} {u u' v v' : Term} :
      MEqRed Γ (v :: s) u u' →
      MEqRed Γ [] v v' →
      MEqRed Γ s (.app u v) (.app u' v')

  /-- **Me-Var**: an in-scope variable reduces to itself. -/
  | var {Γ : Ctx} {s : Stack} {i : Nat} :
      PrevalidExt Γ s →
      i < Γ.depth →
      MEqRed Γ s (.bvar i) (.bvar i)

  /-- **Me-Fun**: descend under an unapplied abstraction. -/
  | fun_ {Γ : Ctx} {t t' body body' : Term} :
      MEqRed Γ [] t t' →
      MEqRed ({ bound := t, kind := .sub } :: Γ) [] body body' →
      MEqRed Γ [] (.abs t body) (.abs t' body')

  /-- **Me-TAp**: `Top` applied to a scoped argument reduces to `Top`. -/
  | tAp {Γ : Ctx} {s : Stack} {u : Term} :
      PrevalidExt Γ s →
      Term.Scoped Γ.depth u →
      MEqRed Γ s (.app .top u) .top

  /-- **Me-FOp**: function step with an operand popped into an equivalence
  binding for the body derivation. -/
  | fOp {Γ : Ctx} {s : Stack} {t t' α body body' : Term} :
      MEqRed Γ [] t t' →
      Term.Scoped Γ.depth α →
      MEqRed ({ bound := α, kind := .equ } :: Γ) (Stack.shift 0 s) body body' →
      MEqRed Γ (α :: s) (.abs t body) (.abs t' body')

/-- MPSS subtype reduction in de Bruijn form. -/
inductive MSubRed : Ctx → Stack → Term → Term → Type where
  /-- **Ms-Pro**: promote a variable through a subtype binding. -/
  | pro {Γ : Ctx} {s : Stack} {i : Nat} {t : Term} :
      PrevalidExt Γ s →
      Γ.subBinds i t →
      MSubRed Γ s (.bvar i) t

  /-- **Ms-Top**. -/
  | top {Γ : Ctx} {s : Stack} {u : Term} :
      PrevalidExt Γ s →
      Term.Scoped Γ.depth u →
      MSubRed Γ s u .top

  /-- **Ms-Equ**. -/
  | equ {Γ : Ctx} {s : Stack} {u v : Term} :
      PrevalidExt Γ s →
      MEqRed Γ s u v →
      MSubRed Γ s u v

  /-- **Ms-App**. -/
  | app {Γ : Ctx} {s : Stack} {u u' v : Term} :
      MSubRed Γ (v :: s) u u' →
      Term.Scoped Γ.depth v →
      MSubRed Γ s (.app u v) (.app u' v)

  /-- **Ms-Fun**. -/
  | fun_ {Γ : Ctx} {t t' body body' : Term} :
      Term.Scoped Γ.depth t →
      MEqRed Γ [] t t' →
      MSubRed ({ bound := t, kind := .sub } :: Γ) [] body body' →
      MSubRed Γ [] (.abs t body) (.abs t' body')

  /-- **Ms-FOp**. -/
  | fOp {Γ : Ctx} {s : Stack} {t α body body' : Term} :
      Term.Scoped Γ.depth t →
      Term.Scoped Γ.depth α →
      MSubRed ({ bound := α, kind := .equ } :: Γ) (Stack.shift 0 s) body body' →
      MSubRed Γ (α :: s) (.abs t body) (.abs t body')

/-- Prop wrapper for equivalence reduction, matching the existing LN API. -/
def MEqRedJ (Γ : Ctx) (s : Stack) (u v : Term) : Prop :=
  Nonempty (MEqRed Γ s u v)

/-- Prop wrapper for subtype reduction, matching the existing LN API. -/
def MSubRedJ (Γ : Ctx) (s : Stack) (u v : Term) : Prop :=
  Nonempty (MSubRed Γ s u v)

/-- Reflexive-transitive closure of de Bruijn equivalence reduction. -/
abbrev MEqRedStar (Γ : Ctx) (s : Stack) : Term → Term → Prop :=
  Relation.ReflTransGen (MEqRedJ Γ s)

/-- Reflexive-transitive closure of de Bruijn subtype reduction. -/
abbrev MSubRedStar (Γ : Ctx) (s : Stack) : Term → Term → Prop :=
  Relation.ReflTransGen (MSubRedJ Γ s)

/-! ## Basic scoping invariants -/

/-- Equivalence reduction relates terms scoped in the current de Bruijn
context. -/
noncomputable def MEqRed.scoped_pair {Γ : Ctx} {s : Stack} {u v : Term}
    (h : MEqRed Γ s u v) : Term.Scoped Γ.depth u × Term.Scoped Γ.depth v := by
  induction h with
  | pro hpv hb _ ih =>
    exact ⟨Term.Scoped.bvar (Ctx.equBinds_lt hb), ih.2⟩
  | bet ht _ _ ih_body ih_arg =>
    exact ⟨
      Term.Scoped.app (Term.Scoped.abs ht ih_body.1) ih_arg.1,
      Term.instantiate_scoped 0 _ _ _ (Nat.zero_le _) ih_arg.2 ih_body.2⟩
  | top _ =>
    exact ⟨Term.Scoped.top, Term.Scoped.top⟩
  | app _ _ ih_fn ih_arg =>
    exact ⟨Term.Scoped.app ih_fn.1 ih_arg.1, Term.Scoped.app ih_fn.2 ih_arg.2⟩
  | var _ hi =>
    exact ⟨Term.Scoped.bvar hi, Term.Scoped.bvar hi⟩
  | fun_ _ _ ih_t ih_body =>
    exact ⟨Term.Scoped.abs ih_t.1 ih_body.1, Term.Scoped.abs ih_t.2 ih_body.2⟩
  | tAp _ hu =>
    exact ⟨Term.Scoped.app Term.Scoped.top hu, Term.Scoped.top⟩
  | fOp _ _ _ ih_t ih_body =>
    exact ⟨Term.Scoped.abs ih_t.1 ih_body.1, Term.Scoped.abs ih_t.2 ih_body.2⟩

/-- Left projection of `MEqRed.scoped_pair`. -/
noncomputable def MEqRed.scoped_left {Γ : Ctx} {s : Stack} {u v : Term}
    (h : MEqRed Γ s u v) : Term.Scoped Γ.depth u :=
  h.scoped_pair.1

/-- Right projection of `MEqRed.scoped_pair`. -/
noncomputable def MEqRed.scoped_right {Γ : Ctx} {s : Stack} {u v : Term}
    (h : MEqRed Γ s u v) : Term.Scoped Γ.depth v :=
  h.scoped_pair.2

/-- Subtype reduction relates terms scoped in the current de Bruijn context. -/
noncomputable def MSubRed.scoped_pair {Γ : Ctx} {s : Stack} {u v : Term}
    (h : MSubRed Γ s u v) : Term.Scoped Γ.depth u × Term.Scoped Γ.depth v := by
  induction h with
  | pro hpv hb =>
    exact ⟨
      Term.Scoped.bvar (Ctx.subBinds_lt hb),
      Prevalid.scoped_lookupSub (PrevalidExt.ctx hpv) hb⟩
  | top _ hu =>
    exact ⟨hu, Term.Scoped.top⟩
  | equ _ heq =>
    exact heq.scoped_pair
  | app _ hv ih =>
    exact ⟨Term.Scoped.app ih.1 hv, Term.Scoped.app ih.2 hv⟩
  | fun_ ht heq _ ih_body =>
    exact ⟨Term.Scoped.abs ht ih_body.1, Term.Scoped.abs heq.scoped_pair.2 ih_body.2⟩
  | fOp ht _ _ ih_body =>
    exact ⟨Term.Scoped.abs ht ih_body.1, Term.Scoped.abs ht ih_body.2⟩

/-- Left projection of `MSubRed.scoped_pair`. -/
noncomputable def MSubRed.scoped_left {Γ : Ctx} {s : Stack} {u v : Term}
    (h : MSubRed Γ s u v) : Term.Scoped Γ.depth u :=
  h.scoped_pair.1

/-- Right projection of `MSubRed.scoped_pair`. -/
noncomputable def MSubRed.scoped_right {Γ : Ctx} {s : Stack} {u v : Term}
    (h : MSubRed Γ s u v) : Term.Scoped Γ.depth v :=
  h.scoped_pair.2

/-! ## Prop-wrapper and closure scoping invariants -/

/-- Prop-wrapper equivalence reduction relates scoped de Bruijn terms. -/
noncomputable def MEqRedJ.scoped_pair {Γ : Ctx} {s : Stack} {u v : Term}
    (h : MEqRedJ Γ s u v) : Term.Scoped Γ.depth u × Term.Scoped Γ.depth v :=
  h.some.scoped_pair

/-- Left projection of `MEqRedJ.scoped_pair`. -/
noncomputable def MEqRedJ.scoped_left {Γ : Ctx} {s : Stack} {u v : Term}
    (h : MEqRedJ Γ s u v) : Term.Scoped Γ.depth u :=
  h.scoped_pair.1

/-- Right projection of `MEqRedJ.scoped_pair`. -/
noncomputable def MEqRedJ.scoped_right {Γ : Ctx} {s : Stack} {u v : Term}
    (h : MEqRedJ Γ s u v) : Term.Scoped Γ.depth v :=
  h.scoped_pair.2

/-- Prop-wrapper subtype reduction relates scoped de Bruijn terms. -/
noncomputable def MSubRedJ.scoped_pair {Γ : Ctx} {s : Stack} {u v : Term}
    (h : MSubRedJ Γ s u v) : Term.Scoped Γ.depth u × Term.Scoped Γ.depth v :=
  h.some.scoped_pair

/-- Left projection of `MSubRedJ.scoped_pair`. -/
noncomputable def MSubRedJ.scoped_left {Γ : Ctx} {s : Stack} {u v : Term}
    (h : MSubRedJ Γ s u v) : Term.Scoped Γ.depth u :=
  h.scoped_pair.1

/-- Right projection of `MSubRedJ.scoped_pair`. -/
noncomputable def MSubRedJ.scoped_right {Γ : Ctx} {s : Stack} {u v : Term}
    (h : MSubRedJ Γ s u v) : Term.Scoped Γ.depth v :=
  h.scoped_pair.2

/-- A de Bruijn equivalence-reduction chain preserves target scoping from
source scoping. -/
noncomputable def MEqRedStar.scoped_right {Γ : Ctx} {s : Stack} {u v : Term}
    (h : MEqRedStar Γ s u v) :
    Term.Scoped Γ.depth u → Term.Scoped Γ.depth v := by
  suffices key : ∀ {a : Term} (h : MEqRedStar Γ s a v),
      Nonempty (Term.Scoped Γ.depth a → Term.Scoped Γ.depth v) from
    (key h).some
  intro a h
  refine Relation.ReflTransGen.head_induction_on (b := v)
    (P := fun a _ => Nonempty (Term.Scoped Γ.depth a → Term.Scoped Γ.depth v))
    h ?_ ?_
  · exact ⟨fun hu => hu⟩
  · intro _ _ hHead _ ih
    exact ⟨fun hu => ih.some hHead.scoped_right⟩

/-- A de Bruijn equivalence-reduction chain relates scoped endpoints when its
source is scoped. -/
noncomputable def MEqRedStar.scoped_pair {Γ : Ctx} {s : Stack} {u v : Term}
    (h : MEqRedStar Γ s u v) (hu : Term.Scoped Γ.depth u) :
    Term.Scoped Γ.depth u × Term.Scoped Γ.depth v :=
  ⟨hu, h.scoped_right hu⟩

/-- A de Bruijn equivalence-reduction chain provides source scoping in
`Prop` form when its target is scoped. This `Nonempty` shape avoids
eliminating the Prop-valued star into a Type-valued conclusion. -/
theorem MEqRedStar.scoped_left_nonempty {Γ : Ctx} {s : Stack} {u v : Term}
    (h : MEqRedStar Γ s u v) (hv : Term.Scoped Γ.depth v) :
    Nonempty (Term.Scoped Γ.depth u) := by
  induction h with
  | refl =>
    exact ⟨hv⟩
  | tail hStar hStep ih =>
    exact ih hStep.scoped_left

/-- A de Bruijn equivalence-reduction chain relates scoped endpoints in
`Prop` form when its target is scoped. -/
theorem MEqRedStar.scoped_pair_from_right_nonempty {Γ : Ctx} {s : Stack}
    {u v : Term} (h : MEqRedStar Γ s u v) (hv : Term.Scoped Γ.depth v) :
    Nonempty (Term.Scoped Γ.depth u × Term.Scoped Γ.depth v) :=
  ⟨⟨(h.scoped_left_nonempty hv).some, hv⟩⟩

/-- A de Bruijn subtype-reduction chain preserves target scoping from source
scoping. -/
noncomputable def MSubRedStar.scoped_right {Γ : Ctx} {s : Stack} {u v : Term}
    (h : MSubRedStar Γ s u v) :
    Term.Scoped Γ.depth u → Term.Scoped Γ.depth v := by
  suffices key : ∀ {a : Term} (h : MSubRedStar Γ s a v),
      Nonempty (Term.Scoped Γ.depth a → Term.Scoped Γ.depth v) from
    (key h).some
  intro a h
  refine Relation.ReflTransGen.head_induction_on (b := v)
    (P := fun a _ => Nonempty (Term.Scoped Γ.depth a → Term.Scoped Γ.depth v))
    h ?_ ?_
  · exact ⟨fun hu => hu⟩
  · intro _ _ hHead _ ih
    exact ⟨fun hu => ih.some hHead.scoped_right⟩

/-- A de Bruijn subtype-reduction chain relates scoped endpoints when its
source is scoped. -/
noncomputable def MSubRedStar.scoped_pair {Γ : Ctx} {s : Stack} {u v : Term}
    (h : MSubRedStar Γ s u v) (hu : Term.Scoped Γ.depth u) :
    Term.Scoped Γ.depth u × Term.Scoped Γ.depth v :=
  ⟨hu, h.scoped_right hu⟩

/-- A de Bruijn subtype-reduction chain provides source scoping in `Prop`
form when its target is scoped. -/
theorem MSubRedStar.scoped_left_nonempty {Γ : Ctx} {s : Stack} {u v : Term}
    (h : MSubRedStar Γ s u v) (hv : Term.Scoped Γ.depth v) :
    Nonempty (Term.Scoped Γ.depth u) := by
  induction h with
  | refl =>
    exact ⟨hv⟩
  | tail hStar hStep ih =>
    exact ih hStep.scoped_left

/-- A de Bruijn subtype-reduction chain relates scoped endpoints in `Prop`
form when its target is scoped. -/
theorem MSubRedStar.scoped_pair_from_right_nonempty {Γ : Ctx} {s : Stack}
    {u v : Term} (h : MSubRedStar Γ s u v) (hv : Term.Scoped Γ.depth v) :
    Nonempty (Term.Scoped Γ.depth u × Term.Scoped Γ.depth v) :=
  ⟨⟨(h.scoped_left_nonempty hv).some, hv⟩⟩

/-! ## Closure constructors -/

/-- A single de Bruijn equivalence-reduction step embeds into its reflexive
transitive closure. -/
theorem MEqRedStar.single {Γ : Ctx} {s : Stack} {u v : Term}
    (h : MEqRed Γ s u v) : MEqRedStar Γ s u v :=
  Relation.ReflTransGen.single ⟨h⟩

/-- A single de Bruijn subtype-reduction step embeds into its reflexive
transitive closure. -/
theorem MSubRedStar.single {Γ : Ctx} {s : Stack} {u v : Term}
    (h : MSubRed Γ s u v) : MSubRedStar Γ s u v :=
  Relation.ReflTransGen.single ⟨h⟩

/-- Star-on-star transitivity for de Bruijn equivalence reduction. -/
theorem MEqRedStar.trans {Γ : Ctx} {s : Stack} {u v w : Term}
    (h₁ : MEqRedStar Γ s u v) (h₂ : MEqRedStar Γ s v w) :
    MEqRedStar Γ s u w :=
  Relation.ReflTransGen.trans h₁ h₂

/-- Star-on-star transitivity for de Bruijn subtype reduction. -/
theorem MSubRedStar.trans {Γ : Ctx} {s : Stack} {u v w : Term}
    (h₁ : MSubRedStar Γ s u v) (h₂ : MSubRedStar Γ s v w) :
    MSubRedStar Γ s u w :=
  Relation.ReflTransGen.trans h₁ h₂

/-- An equivalence-reduction chain embeds into subtype reduction when the
extended context is prevalid, by wrapping each equivalence step in `Ms-Equ`. -/
theorem MSubRedStar.of_MEqRedStar {Γ : Ctx} {s : Stack} {u v : Term}
    (hpv : PrevalidExt Γ s) (h : MEqRedStar Γ s u v) :
    MSubRedStar Γ s u v := by
  induction h with
  | refl =>
    exact Relation.ReflTransGen.refl
  | @tail y z hStar hStep ih =>
    exact Relation.ReflTransGen.trans ih
      (MSubRedStar.single (MSubRed.equ hpv hStep.some))

/-! ## Prevalidity invariants -/

/-- Context prevalidity from de Bruijn equivalence reduction. -/
noncomputable def MEqRed.prevalid {Γ : Ctx} {s : Stack} {u v : Term}
    (h : MEqRed Γ s u v) : Prevalid Γ := by
  induction h with
  | pro hpv _ _ _ =>
    exact PrevalidExt.ctx hpv
  | bet _ _ _ _ ihArg =>
    exact ihArg
  | top hpv =>
    exact PrevalidExt.ctx hpv
  | app _ _ _ ihArg =>
    exact ihArg
  | var hpv _ =>
    exact PrevalidExt.ctx hpv
  | fun_ _ _ ihBound _ =>
    exact ihBound
  | tAp hpv _ =>
    exact PrevalidExt.ctx hpv
  | fOp _ _ _ ihBound _ =>
    exact ihBound

/-- Context prevalidity from de Bruijn subtype reduction. -/
noncomputable def MSubRed.prevalid {Γ : Ctx} {s : Stack} {u v : Term}
    (h : MSubRed Γ s u v) : Prevalid Γ := by
  induction h with
  | pro hpv _ =>
    exact PrevalidExt.ctx hpv
  | top hpv _ =>
    exact PrevalidExt.ctx hpv
  | equ hpv _ =>
    exact PrevalidExt.ctx hpv
  | app _ _ ih =>
    exact ih
  | fun_ _ heq _ _ =>
    exact heq.prevalid
  | fOp _ _ _ ih =>
    exact Prevalid.tail ih

/-! ## Insertion weakening scaffolding -/

/-- Weakening helper for the de Bruijn equivalence variable case under
`Ctx.insertAt`. -/
noncomputable def MEqRed.var_insertAt {Γ : Ctx} {s : Stack} {cutoff i : Nat}
    {newEntry : CtxEntry}
    (hcut : cutoff ≤ Γ.depth)
    (hpv : PrevalidExt (Ctx.insertAt cutoff newEntry Γ) (Stack.shift cutoff s))
    (hi : i < Γ.depth) :
    MEqRed (Ctx.insertAt cutoff newEntry Γ) (Stack.shift cutoff s)
      (Term.shift cutoff (.bvar i)) (Term.shift cutoff (.bvar i)) := by
  rw [Ctx.shift_bvar_insertAtIndex]
  exact MEqRed.var hpv (Ctx.insertAtIndex_lt_depth hcut hi)

/-- Weakening helper for the de Bruijn equivalence promotion case under
`Ctx.insertAt`. The recursive premise is supplied explicitly; this lemma only
packages the index and binding transport. -/
noncomputable def MEqRed.pro_insertAt {Γ : Ctx} {s : Stack} {cutoff i : Nat}
    {newEntry : CtxEntry} {α α' : Term}
    (hpv : PrevalidExt (Ctx.insertAt cutoff newEntry Γ) (Stack.shift cutoff s))
    (hb : Γ.equBinds i α)
    (hrec : MEqRed (Ctx.insertAt cutoff newEntry Γ) (Stack.shift cutoff s)
      (Term.shift cutoff α) (Term.shift cutoff α')) :
    MEqRed (Ctx.insertAt cutoff newEntry Γ) (Stack.shift cutoff s)
      (Term.shift cutoff (.bvar i)) (Term.shift cutoff α') := by
  rw [Ctx.shift_bvar_insertAtIndex]
  exact MEqRed.pro hpv (Ctx.equBinds_insertAt hb) hrec

/-- Weakening helper for `Me-Top` under `Ctx.insertAt`. -/
noncomputable def MEqRed.top_insertAt {Γ : Ctx} {s : Stack} {cutoff : Nat}
    {newEntry : CtxEntry}
    (hpv : PrevalidExt (Ctx.insertAt cutoff newEntry Γ) (Stack.shift cutoff s)) :
    MEqRed (Ctx.insertAt cutoff newEntry Γ) (Stack.shift cutoff s)
      (Term.shift cutoff .top) (Term.shift cutoff .top) := by
  exact MEqRed.top hpv

/-- Weakening helper for `Me-TAp` under `Ctx.insertAt`. -/
noncomputable def MEqRed.tAp_insertAt {Γ : Ctx} {s : Stack} {cutoff : Nat}
    {newEntry : CtxEntry} {u : Term}
    (hcut : cutoff ≤ Γ.depth)
    (hpv : PrevalidExt (Ctx.insertAt cutoff newEntry Γ) (Stack.shift cutoff s))
    (hu : Term.Scoped Γ.depth u) :
    MEqRed (Ctx.insertAt cutoff newEntry Γ) (Stack.shift cutoff s)
      (Term.shift cutoff (.app .top u)) (Term.shift cutoff .top) := by
  have hu' : Term.Scoped (Γ.depth + 1) (Term.shift cutoff u) :=
    Term.shift_scoped cutoff Γ.depth _ hcut hu
  have hdepth : (Ctx.insertAt cutoff newEntry Γ).depth = Γ.depth + 1 :=
    Ctx.depth_insertAt_of_le hcut
  simpa using MEqRed.tAp hpv (by simpa [hdepth] using hu')

/-- Weakening helper for `Me-App` under `Ctx.insertAt`; recursive premises are
supplied explicitly. -/
noncomputable def MEqRed.app_insertAt {Γ : Ctx} {s : Stack} {cutoff : Nat}
    {newEntry : CtxEntry} {u u' v v' : Term}
    (hfn : MEqRed (Ctx.insertAt cutoff newEntry Γ)
      (Term.shift cutoff v :: Stack.shift cutoff s)
      (Term.shift cutoff u) (Term.shift cutoff u'))
    (harg : MEqRed (Ctx.insertAt cutoff newEntry Γ) []
      (Term.shift cutoff v) (Term.shift cutoff v')) :
    MEqRed (Ctx.insertAt cutoff newEntry Γ) (Stack.shift cutoff s)
      (Term.shift cutoff (.app u v)) (Term.shift cutoff (.app u' v')) := by
  exact MEqRed.app hfn harg

/-- Weakening helper for `Me-Fun` under `Ctx.insertAt`; recursive premises are
supplied explicitly. The body premise uses insertion below the abstraction
head, i.e. cutoff `cutoff + 1`. -/
noncomputable def MEqRed.fun_insertAt {Γ : Ctx} {cutoff : Nat}
    {newEntry : CtxEntry} {t t' body body' : Term}
    (hbound : MEqRed (Ctx.insertAt cutoff newEntry Γ) []
      (Term.shift cutoff t) (Term.shift cutoff t'))
    (hbody : MEqRed (Ctx.insertAt (cutoff + 1) newEntry
      ({ bound := t, kind := .sub } :: Γ)) []
      (Term.shift (cutoff + 1) body) (Term.shift (cutoff + 1) body')) :
    MEqRed (Ctx.insertAt cutoff newEntry Γ) []
      (Term.shift cutoff (.abs t body)) (Term.shift cutoff (.abs t' body')) := by
  exact MEqRed.fun_ hbound hbody

/-- Weakening helper for `Me-Bet` under `Ctx.insertAt`; recursive premises are
supplied explicitly. -/
noncomputable def MEqRed.bet_insertAt {Γ : Ctx} {s : Stack} {cutoff : Nat}
    {newEntry : CtxEntry} {t v v' body body' : Term}
    (hcut : cutoff ≤ Γ.depth)
    (ht : Term.Scoped Γ.depth t)
    (hbody : MEqRed (Ctx.insertAt (cutoff + 1) newEntry
      ({ bound := t, kind := .sub } :: Γ)) (Stack.shift 0 (Stack.shift cutoff s))
      (Term.shift (cutoff + 1) body) (Term.shift (cutoff + 1) body'))
    (harg : MEqRed (Ctx.insertAt cutoff newEntry Γ) []
      (Term.shift cutoff v) (Term.shift cutoff v')) :
    MEqRed (Ctx.insertAt cutoff newEntry Γ) (Stack.shift cutoff s)
      (Term.shift cutoff (.app (.abs t body) v))
      (Term.shift cutoff (Term.instantiate 0 v' body')) := by
  have ht' : Term.Scoped (Γ.depth + 1) (Term.shift cutoff t) :=
    Term.shift_scoped cutoff Γ.depth _ hcut ht
  have hdepth : (Ctx.insertAt cutoff newEntry Γ).depth = Γ.depth + 1 :=
    Ctx.depth_insertAt_of_le hcut
  have hbet := MEqRed.bet (by simpa [hdepth] using ht') hbody harg
  simpa [Term.shift_instantiate_zero cutoff v' body'] using hbet

/-- Weakening helper for `Me-FOp` under `Ctx.insertAt`; recursive premises are
supplied explicitly. -/
noncomputable def MEqRed.fOp_insertAt {Γ : Ctx} {s : Stack} {cutoff : Nat}
    {newEntry : CtxEntry} {t t' α body body' : Term}
    (hcut : cutoff ≤ Γ.depth)
    (hbound : MEqRed (Ctx.insertAt cutoff newEntry Γ) []
      (Term.shift cutoff t) (Term.shift cutoff t'))
    (hα : Term.Scoped Γ.depth α)
    (hbody : MEqRed (Ctx.insertAt (cutoff + 1) newEntry
      ({ bound := α, kind := .equ } :: Γ)) (Stack.shift 0 (Stack.shift cutoff s))
      (Term.shift (cutoff + 1) body) (Term.shift (cutoff + 1) body')) :
    MEqRed (Ctx.insertAt cutoff newEntry Γ) (Stack.shift cutoff (α :: s))
      (Term.shift cutoff (.abs t body)) (Term.shift cutoff (.abs t' body')) := by
  have hα' : Term.Scoped (Γ.depth + 1) (Term.shift cutoff α) :=
    Term.shift_scoped cutoff Γ.depth _ hcut hα
  have hdepth : (Ctx.insertAt cutoff newEntry Γ).depth = Γ.depth + 1 :=
    Ctx.depth_insertAt_of_le hcut
  exact MEqRed.fOp hbound (by simpa [hdepth] using hα') hbody

/-- Weakening helper for the de Bruijn subtype promotion case under
`Ctx.insertAt`. -/
noncomputable def MSubRed.pro_insertAt {Γ : Ctx} {s : Stack} {cutoff i : Nat}
    {newEntry : CtxEntry} {t : Term}
    (hpv : PrevalidExt (Ctx.insertAt cutoff newEntry Γ) (Stack.shift cutoff s))
    (hb : Γ.subBinds i t) :
    MSubRed (Ctx.insertAt cutoff newEntry Γ) (Stack.shift cutoff s)
      (Term.shift cutoff (.bvar i)) (Term.shift cutoff t) := by
  rw [Ctx.shift_bvar_insertAtIndex]
  exact MSubRed.pro hpv (Ctx.subBinds_insertAt hb)

/-- Weakening helper for `Ms-Top` under `Ctx.insertAt`. -/
noncomputable def MSubRed.top_insertAt {Γ : Ctx} {s : Stack} {cutoff : Nat}
    {newEntry : CtxEntry} {u : Term}
    (hcut : cutoff ≤ Γ.depth)
    (hpv : PrevalidExt (Ctx.insertAt cutoff newEntry Γ) (Stack.shift cutoff s))
    (hu : Term.Scoped Γ.depth u) :
    MSubRed (Ctx.insertAt cutoff newEntry Γ) (Stack.shift cutoff s)
      (Term.shift cutoff u) (Term.shift cutoff .top) := by
  have hu' : Term.Scoped (Γ.depth + 1) (Term.shift cutoff u) :=
    Term.shift_scoped cutoff Γ.depth _ hcut hu
  have hdepth : (Ctx.insertAt cutoff newEntry Γ).depth = Γ.depth + 1 :=
    Ctx.depth_insertAt_of_le hcut
  exact MSubRed.top hpv (by simpa [hdepth] using hu')

/-- Weakening helper for `Ms-Equ` under `Ctx.insertAt`. -/
noncomputable def MSubRed.equ_insertAt {Γ : Ctx} {s : Stack} {cutoff : Nat}
    {newEntry : CtxEntry} {u v : Term}
    (hpv : PrevalidExt (Ctx.insertAt cutoff newEntry Γ) (Stack.shift cutoff s))
    (heq : MEqRed (Ctx.insertAt cutoff newEntry Γ) (Stack.shift cutoff s)
      (Term.shift cutoff u) (Term.shift cutoff v)) :
    MSubRed (Ctx.insertAt cutoff newEntry Γ) (Stack.shift cutoff s)
      (Term.shift cutoff u) (Term.shift cutoff v) :=
  MSubRed.equ hpv heq

/-- Weakening helper for `Ms-App` under `Ctx.insertAt`; the recursive premise
is supplied explicitly. -/
noncomputable def MSubRed.app_insertAt {Γ : Ctx} {s : Stack} {cutoff : Nat}
    {newEntry : CtxEntry} {u u' v : Term}
    (hcut : cutoff ≤ Γ.depth)
    (hfn : MSubRed (Ctx.insertAt cutoff newEntry Γ)
      (Term.shift cutoff v :: Stack.shift cutoff s)
      (Term.shift cutoff u) (Term.shift cutoff u'))
    (hv : Term.Scoped Γ.depth v) :
    MSubRed (Ctx.insertAt cutoff newEntry Γ) (Stack.shift cutoff s)
      (Term.shift cutoff (.app u v)) (Term.shift cutoff (.app u' v)) := by
  have hv' : Term.Scoped (Γ.depth + 1) (Term.shift cutoff v) :=
    Term.shift_scoped cutoff Γ.depth _ hcut hv
  have hdepth : (Ctx.insertAt cutoff newEntry Γ).depth = Γ.depth + 1 :=
    Ctx.depth_insertAt_of_le hcut
  exact MSubRed.app hfn (by simpa [hdepth] using hv')

/-- Weakening helper for `Ms-Fun` under `Ctx.insertAt`; recursive premises are
supplied explicitly. -/
noncomputable def MSubRed.fun_insertAt {Γ : Ctx} {cutoff : Nat}
    {newEntry : CtxEntry} {t t' body body' : Term}
    (hcut : cutoff ≤ Γ.depth)
    (ht : Term.Scoped Γ.depth t)
    (hbound : MEqRed (Ctx.insertAt cutoff newEntry Γ) []
      (Term.shift cutoff t) (Term.shift cutoff t'))
    (hbody : MSubRed (Ctx.insertAt (cutoff + 1) newEntry
      ({ bound := t, kind := .sub } :: Γ)) []
      (Term.shift (cutoff + 1) body) (Term.shift (cutoff + 1) body')) :
    MSubRed (Ctx.insertAt cutoff newEntry Γ) []
      (Term.shift cutoff (.abs t body)) (Term.shift cutoff (.abs t' body')) := by
  have ht' : Term.Scoped (Γ.depth + 1) (Term.shift cutoff t) :=
    Term.shift_scoped cutoff Γ.depth _ hcut ht
  have hdepth : (Ctx.insertAt cutoff newEntry Γ).depth = Γ.depth + 1 :=
    Ctx.depth_insertAt_of_le hcut
  exact MSubRed.fun_ (by simpa [hdepth] using ht') hbound hbody

/-- Weakening helper for `Ms-FOp` under `Ctx.insertAt`; recursive premises are
supplied explicitly. -/
noncomputable def MSubRed.fOp_insertAt {Γ : Ctx} {s : Stack} {cutoff : Nat}
    {newEntry : CtxEntry} {t α body body' : Term}
    (hcut : cutoff ≤ Γ.depth)
    (ht : Term.Scoped Γ.depth t)
    (hα : Term.Scoped Γ.depth α)
    (hbody : MSubRed (Ctx.insertAt (cutoff + 1) newEntry
      ({ bound := α, kind := .equ } :: Γ)) (Stack.shift 0 (Stack.shift cutoff s))
      (Term.shift (cutoff + 1) body) (Term.shift (cutoff + 1) body')) :
    MSubRed (Ctx.insertAt cutoff newEntry Γ) (Stack.shift cutoff (α :: s))
      (Term.shift cutoff (.abs t body)) (Term.shift cutoff (.abs t body')) := by
  have ht' : Term.Scoped (Γ.depth + 1) (Term.shift cutoff t) :=
    Term.shift_scoped cutoff Γ.depth _ hcut ht
  have hα' : Term.Scoped (Γ.depth + 1) (Term.shift cutoff α) :=
    Term.shift_scoped cutoff Γ.depth _ hcut hα
  have hdepth : (Ctx.insertAt cutoff newEntry Γ).depth = Γ.depth + 1 :=
    Ctx.depth_insertAt_of_le hcut
  exact MSubRed.fOp (by simpa [hdepth] using ht') (by simpa [hdepth] using hα') hbody

/-- General insertion weakening for de Bruijn equivalence reduction. -/
noncomputable def MEqRed.insertAt {Γ : Ctx} {s : Stack} {u v : Term}
    (h : MEqRed Γ s u v) {cutoff : Nat} {newEntry : CtxEntry}
    (hcut : cutoff ≤ Γ.depth)
    (hNew : Prevalid (newEntry :: List.drop cutoff Γ))
    (hpv : PrevalidExt Γ s) :
    MEqRed (Ctx.insertAt cutoff newEntry Γ) (Stack.shift cutoff s)
      (Term.shift cutoff u) (Term.shift cutoff v) := by
  induction h generalizing cutoff newEntry with
  | @pro Γp sp i α α' hpv0 hb hred ih =>
    have hpv' : PrevalidExt (Ctx.insertAt cutoff newEntry Γp) (Stack.shift cutoff sp) :=
      PrevalidExt.insertAt (Γ := Γp) (s := sp) (cutoff := cutoff)
        (newEntry := newEntry) hcut hpv
        (Prevalid.insertAt (Γ := Γp) (cutoff := cutoff) (newEntry := newEntry)
          hcut (PrevalidExt.ctx hpv) hNew)
    exact MEqRed.pro_insertAt hpv' hb (ih hcut hNew hpv)
  | @bet Γp sp t x x' body body' ht hbody harg ih_body ih_arg =>
    have hpvBodyCtx : Prevalid ({ bound := t, kind := .sub } :: Γp) :=
      Prevalid.sub (PrevalidExt.ctx hpv) ht
    have hpvBody : PrevalidExt ({ bound := t, kind := .sub } :: Γp) (Stack.shift 0 sp) :=
      PrevalidExt.weaken_head hpv hpvBodyCtx
    have hcutBody : cutoff + 1 ≤ Ctx.depth ({ bound := t, kind := .sub } :: Γp) := by
      simpa [Ctx.depth, Nat.add_comm] using Nat.succ_le_succ hcut
    have hNewBody :
        Prevalid (newEntry :: List.drop (cutoff + 1) ({ bound := t, kind := .sub } :: Γp)) := by
      simpa using hNew
    have hbody' :
        MEqRed (Ctx.insertAt (cutoff + 1) newEntry ({ bound := t, kind := .sub } :: Γp))
          (Stack.shift 0 (Stack.shift cutoff sp))
          (Term.shift (cutoff + 1) body) (Term.shift (cutoff + 1) body') := by
      have hb := ih_body hcutBody hNewBody hpvBody
      simpa [Stack.shift_shift_zero cutoff sp] using hb
    have hpvNil : PrevalidExt Γp [] := PrevalidExt.nil (PrevalidExt.ctx hpv)
    exact MEqRed.bet_insertAt hcut ht hbody' (ih_arg hcut hNew hpvNil)
  | @top Γp sp hpv0 =>
    have hpv' : PrevalidExt (Ctx.insertAt cutoff newEntry Γp) (Stack.shift cutoff sp) :=
      PrevalidExt.insertAt (Γ := Γp) (s := sp) (cutoff := cutoff)
        (newEntry := newEntry) hcut hpv
        (Prevalid.insertAt (Γ := Γp) (cutoff := cutoff) (newEntry := newEntry)
          hcut (PrevalidExt.ctx hpv) hNew)
    exact MEqRed.top_insertAt hpv'
  | @app Γp sp u₀ u₁ x x' hfn harg ih_fn ih_arg =>
    have hx : Term.Scoped Γp.depth x := harg.scoped_left
    have hpvFn : PrevalidExt Γp (x :: sp) := PrevalidExt.cons hpv hx
    have hfn' := ih_fn hcut hNew hpvFn
    have hpvNil : PrevalidExt Γp [] := PrevalidExt.nil (PrevalidExt.ctx hpv)
    exact MEqRed.app_insertAt hfn' (ih_arg hcut hNew hpvNil)
  | @var Γp sp i hpv0 hi =>
    have hpv' : PrevalidExt (Ctx.insertAt cutoff newEntry Γp) (Stack.shift cutoff sp) :=
      PrevalidExt.insertAt (Γ := Γp) (s := sp) (cutoff := cutoff)
        (newEntry := newEntry) hcut hpv
        (Prevalid.insertAt (Γ := Γp) (cutoff := cutoff) (newEntry := newEntry)
          hcut (PrevalidExt.ctx hpv) hNew)
    exact MEqRed.var_insertAt hcut hpv' hi
  | @fun_ Γp t t' body body' hbound hbody ih_bound ih_body =>
    have hpvNil : PrevalidExt Γp [] := PrevalidExt.nil (PrevalidExt.ctx hpv)
    have ht : Term.Scoped Γp.depth t := hbound.scoped_left
    have hpvBodyCtx : Prevalid ({ bound := t, kind := .sub } :: Γp) :=
      Prevalid.sub (PrevalidExt.ctx hpv) ht
    have hpvBody : PrevalidExt ({ bound := t, kind := .sub } :: Γp) [] :=
      PrevalidExt.nil hpvBodyCtx
    have hcutBody : cutoff + 1 ≤ Ctx.depth ({ bound := t, kind := .sub } :: Γp) := by
      simpa [Ctx.depth, Nat.add_comm] using Nat.succ_le_succ hcut
    have hNewBody :
        Prevalid (newEntry :: List.drop (cutoff + 1) ({ bound := t, kind := .sub } :: Γp)) := by
      simpa using hNew
    exact MEqRed.fun_insertAt
      (ih_bound hcut hNew hpvNil)
      (ih_body hcutBody hNewBody hpvBody)
  | @tAp Γp sp x hpv0 hx =>
    have hpv' : PrevalidExt (Ctx.insertAt cutoff newEntry Γp) (Stack.shift cutoff sp) :=
      PrevalidExt.insertAt (Γ := Γp) (s := sp) (cutoff := cutoff)
        (newEntry := newEntry) hcut hpv
        (Prevalid.insertAt (Γ := Γp) (cutoff := cutoff) (newEntry := newEntry)
          hcut (PrevalidExt.ctx hpv) hNew)
    exact MEqRed.tAp_insertAt hcut hpv' hx
  | @fOp Γp sp t t' α body body' hbound hα hbody ih_bound ih_body =>
    have hpvTail : PrevalidExt Γp sp := PrevalidExt.tail hpv
    have hpvNil : PrevalidExt Γp [] := PrevalidExt.nil (PrevalidExt.ctx hpv)
    have hpvBodyCtx : Prevalid ({ bound := α, kind := .equ } :: Γp) :=
      Prevalid.equ (PrevalidExt.ctx hpv) hα
    have hpvBody : PrevalidExt ({ bound := α, kind := .equ } :: Γp) (Stack.shift 0 sp) :=
      PrevalidExt.weaken_head hpvTail hpvBodyCtx
    have hcutBody : cutoff + 1 ≤ Ctx.depth ({ bound := α, kind := .equ } :: Γp) := by
      simpa [Ctx.depth, Nat.add_comm] using Nat.succ_le_succ hcut
    have hNewBody :
        Prevalid (newEntry :: List.drop (cutoff + 1) ({ bound := α, kind := .equ } :: Γp)) := by
      simpa using hNew
    have hbody' :
        MEqRed (Ctx.insertAt (cutoff + 1) newEntry ({ bound := α, kind := .equ } :: Γp))
          (Stack.shift 0 (Stack.shift cutoff sp))
          (Term.shift (cutoff + 1) body) (Term.shift (cutoff + 1) body') := by
      have hb := ih_body hcutBody hNewBody hpvBody
      simpa [Stack.shift_shift_zero cutoff sp] using hb
    exact MEqRed.fOp_insertAt hcut (ih_bound hcut hNew hpvNil) hα hbody'

/-- General insertion weakening for de Bruijn subtype reduction. -/
noncomputable def MSubRed.insertAt {Γ : Ctx} {s : Stack} {u v : Term}
    (h : MSubRed Γ s u v) {cutoff : Nat} {newEntry : CtxEntry}
    (hcut : cutoff ≤ Γ.depth)
    (hNew : Prevalid (newEntry :: List.drop cutoff Γ))
    (hpv : PrevalidExt Γ s) :
    MSubRed (Ctx.insertAt cutoff newEntry Γ) (Stack.shift cutoff s)
      (Term.shift cutoff u) (Term.shift cutoff v) := by
  induction h generalizing cutoff newEntry with
  | @pro Γp sp i t hpv0 hb =>
    have hpv' : PrevalidExt (Ctx.insertAt cutoff newEntry Γp) (Stack.shift cutoff sp) :=
      PrevalidExt.insertAt (Γ := Γp) (s := sp) (cutoff := cutoff)
        (newEntry := newEntry) hcut hpv
        (Prevalid.insertAt (Γ := Γp) (cutoff := cutoff) (newEntry := newEntry)
          hcut (PrevalidExt.ctx hpv) hNew)
    exact MSubRed.pro_insertAt hpv' hb
  | @top Γp sp u hpv0 hu =>
    have hpv' : PrevalidExt (Ctx.insertAt cutoff newEntry Γp) (Stack.shift cutoff sp) :=
      PrevalidExt.insertAt (Γ := Γp) (s := sp) (cutoff := cutoff)
        (newEntry := newEntry) hcut hpv
        (Prevalid.insertAt (Γ := Γp) (cutoff := cutoff) (newEntry := newEntry)
          hcut (PrevalidExt.ctx hpv) hNew)
    exact MSubRed.top_insertAt hcut hpv' hu
  | @equ Γp sp u v hpv0 heq =>
    have hpv' : PrevalidExt (Ctx.insertAt cutoff newEntry Γp) (Stack.shift cutoff sp) :=
      PrevalidExt.insertAt (Γ := Γp) (s := sp) (cutoff := cutoff)
        (newEntry := newEntry) hcut hpv
        (Prevalid.insertAt (Γ := Γp) (cutoff := cutoff) (newEntry := newEntry)
          hcut (PrevalidExt.ctx hpv) hNew)
    exact MSubRed.equ_insertAt hpv' (heq.insertAt hcut hNew hpv)
  | @app Γp sp u u' x hfn hx ih =>
    have hpvFn : PrevalidExt Γp (x :: sp) := PrevalidExt.cons hpv hx
    exact MSubRed.app_insertAt hcut (ih hcut hNew hpvFn) hx
  | @fun_ Γp t t' body body' ht heq hbody ih_body =>
    have hpvNil : PrevalidExt Γp [] := PrevalidExt.nil (PrevalidExt.ctx hpv)
    have hpvBodyCtx : Prevalid ({ bound := t, kind := .sub } :: Γp) :=
      Prevalid.sub (PrevalidExt.ctx hpv) ht
    have hpvBody : PrevalidExt ({ bound := t, kind := .sub } :: Γp) [] :=
      PrevalidExt.nil hpvBodyCtx
    have hcutBody : cutoff + 1 ≤ Ctx.depth ({ bound := t, kind := .sub } :: Γp) := by
      simpa [Ctx.depth, Nat.add_comm] using Nat.succ_le_succ hcut
    have hNewBody :
        Prevalid (newEntry :: List.drop (cutoff + 1) ({ bound := t, kind := .sub } :: Γp)) := by
      simpa using hNew
    exact MSubRed.fun_insertAt hcut ht
      (heq.insertAt hcut hNew hpvNil)
      (ih_body hcutBody hNewBody hpvBody)
  | @fOp Γp sp t α body body' ht hα hbody ih_body =>
    have hpvTail : PrevalidExt Γp sp := PrevalidExt.tail hpv
    have hpvBodyCtx : Prevalid ({ bound := α, kind := .equ } :: Γp) :=
      Prevalid.equ (PrevalidExt.ctx hpv) hα
    have hpvBody : PrevalidExt ({ bound := α, kind := .equ } :: Γp) (Stack.shift 0 sp) :=
      PrevalidExt.weaken_head hpvTail hpvBodyCtx
    have hcutBody : cutoff + 1 ≤ Ctx.depth ({ bound := α, kind := .equ } :: Γp) := by
      simpa [Ctx.depth, Nat.add_comm] using Nat.succ_le_succ hcut
    have hNewBody :
        Prevalid (newEntry :: List.drop (cutoff + 1) ({ bound := α, kind := .equ } :: Γp)) := by
      simpa using hNew
    have hbody' :
        MSubRed (Ctx.insertAt (cutoff + 1) newEntry ({ bound := α, kind := .equ } :: Γp))
          (Stack.shift 0 (Stack.shift cutoff sp))
          (Term.shift (cutoff + 1) body) (Term.shift (cutoff + 1) body') := by
      have hb := ih_body hcutBody hNewBody hpvBody
      simpa [Stack.shift_shift_zero cutoff sp] using hb
    exact MSubRed.fOp_insertAt hcut ht hα hbody'

/-- Head-extension weakening for de Bruijn equivalence reduction. -/
noncomputable def MEqRed.weaken_head {Γ : Ctx} {s : Stack} {u v : Term}
    {newEntry : CtxEntry}
    (h : MEqRed Γ s u v)
    (hpv : PrevalidExt Γ s)
    (hNew : Prevalid (newEntry :: Γ)) :
    MEqRed (newEntry :: Γ) (Stack.shift 0 s) (Term.shift 0 u) (Term.shift 0 v) := by
  simpa using h.insertAt (cutoff := 0) (newEntry := newEntry)
    (Nat.zero_le Γ.depth) hNew hpv

/-- Head-extension weakening for de Bruijn subtype reduction. -/
noncomputable def MSubRed.weaken_head {Γ : Ctx} {s : Stack} {u v : Term}
    {newEntry : CtxEntry}
    (h : MSubRed Γ s u v)
    (hpv : PrevalidExt Γ s)
    (hNew : Prevalid (newEntry :: Γ)) :
    MSubRed (newEntry :: Γ) (Stack.shift 0 s) (Term.shift 0 u) (Term.shift 0 v) := by
  simpa using h.insertAt (cutoff := 0) (newEntry := newEntry)
    (Nat.zero_le Γ.depth) hNew hpv

/-- Weakening under one existing head binder for de Bruijn equivalence
reduction. The head remains innermost; the new entry is inserted below it. -/
noncomputable def MEqRed.weaken_tail_head {Γ : Ctx} {s : Stack} {u v : Term}
    {head newHead : CtxEntry}
    (h : MEqRed (head :: Γ) s u v)
    (hpv : PrevalidExt (head :: Γ) s)
    (hNew : Prevalid (head.shift 0 :: newHead :: Γ)) :
    MEqRed (head.shift 0 :: newHead :: Γ) (Stack.shift 1 s)
      (Term.shift 1 u) (Term.shift 1 v) := by
  simpa using h.insertAt (cutoff := 1) (newEntry := newHead)
    (by simp [Ctx.depth]) (Prevalid.tail hNew) hpv

/-- Weakening under one existing head binder for de Bruijn subtype reduction. -/
noncomputable def MSubRed.weaken_tail_head {Γ : Ctx} {s : Stack} {u v : Term}
    {head newHead : CtxEntry}
    (h : MSubRed (head :: Γ) s u v)
    (hpv : PrevalidExt (head :: Γ) s)
    (hNew : Prevalid (head.shift 0 :: newHead :: Γ)) :
    MSubRed (head.shift 0 :: newHead :: Γ) (Stack.shift 1 s)
      (Term.shift 1 u) (Term.shift 1 v) := by
  simpa using h.insertAt (cutoff := 1) (newEntry := newHead)
    (by simp [Ctx.depth]) (Prevalid.tail hNew) hpv

/-- Prop-wrapper insertion weakening for de Bruijn equivalence reduction. -/
theorem MEqRedJ.insertAt {Γ : Ctx} {s : Stack} {u v : Term}
    {cutoff : Nat} {newEntry : CtxEntry}
    (hcut : cutoff ≤ Γ.depth)
    (hNew : Prevalid (newEntry :: List.drop cutoff Γ))
    (hpv : PrevalidExt Γ s) :
    MEqRedJ Γ s u v →
    MEqRedJ (Ctx.insertAt cutoff newEntry Γ) (Stack.shift cutoff s)
      (Term.shift cutoff u) (Term.shift cutoff v) := by
  rintro ⟨h⟩
  exact ⟨h.insertAt hcut hNew hpv⟩

/-- Prop-wrapper head-extension weakening for de Bruijn equivalence
reduction. -/
theorem MEqRedJ.weaken_head {Γ : Ctx} {s : Stack} {u v : Term}
    {newEntry : CtxEntry}
    (hpv : PrevalidExt Γ s)
    (hNew : Prevalid (newEntry :: Γ)) :
    MEqRedJ Γ s u v →
    MEqRedJ (newEntry :: Γ) (Stack.shift 0 s) (Term.shift 0 u) (Term.shift 0 v) := by
  simpa using MEqRedJ.insertAt (Γ := Γ) (s := s) (u := u) (v := v)
    (cutoff := 0) (newEntry := newEntry) (Nat.zero_le Γ.depth) hNew hpv

/-- Prop-wrapper weakening under one existing head binder for de Bruijn
equivalence reduction. -/
theorem MEqRedJ.weaken_tail_head {Γ : Ctx} {s : Stack} {u v : Term}
    {head newHead : CtxEntry}
    (hpv : PrevalidExt (head :: Γ) s)
    (hNew : Prevalid (head.shift 0 :: newHead :: Γ)) :
    MEqRedJ (head :: Γ) s u v →
    MEqRedJ (head.shift 0 :: newHead :: Γ) (Stack.shift 1 s)
      (Term.shift 1 u) (Term.shift 1 v) := by
  simpa using MEqRedJ.insertAt (Γ := head :: Γ) (s := s) (u := u) (v := v)
    (cutoff := 1) (newEntry := newHead) (by simp [Ctx.depth])
    (Prevalid.tail hNew) hpv

/-- Prop-wrapper insertion weakening for de Bruijn subtype reduction. -/
theorem MSubRedJ.insertAt {Γ : Ctx} {s : Stack} {u v : Term}
    {cutoff : Nat} {newEntry : CtxEntry}
    (hcut : cutoff ≤ Γ.depth)
    (hNew : Prevalid (newEntry :: List.drop cutoff Γ))
    (hpv : PrevalidExt Γ s) :
    MSubRedJ Γ s u v →
    MSubRedJ (Ctx.insertAt cutoff newEntry Γ) (Stack.shift cutoff s)
      (Term.shift cutoff u) (Term.shift cutoff v) := by
  rintro ⟨h⟩
  exact ⟨h.insertAt hcut hNew hpv⟩

/-- Prop-wrapper head-extension weakening for de Bruijn subtype reduction. -/
theorem MSubRedJ.weaken_head {Γ : Ctx} {s : Stack} {u v : Term}
    {newEntry : CtxEntry}
    (hpv : PrevalidExt Γ s)
    (hNew : Prevalid (newEntry :: Γ)) :
    MSubRedJ Γ s u v →
    MSubRedJ (newEntry :: Γ) (Stack.shift 0 s) (Term.shift 0 u) (Term.shift 0 v) := by
  simpa using MSubRedJ.insertAt (Γ := Γ) (s := s) (u := u) (v := v)
    (cutoff := 0) (newEntry := newEntry) (Nat.zero_le Γ.depth) hNew hpv

/-- Prop-wrapper weakening under one existing head binder for de Bruijn subtype
reduction. -/
theorem MSubRedJ.weaken_tail_head {Γ : Ctx} {s : Stack} {u v : Term}
    {head newHead : CtxEntry}
    (hpv : PrevalidExt (head :: Γ) s)
    (hNew : Prevalid (head.shift 0 :: newHead :: Γ)) :
    MSubRedJ (head :: Γ) s u v →
    MSubRedJ (head.shift 0 :: newHead :: Γ) (Stack.shift 1 s)
      (Term.shift 1 u) (Term.shift 1 v) := by
  simpa using MSubRedJ.insertAt (Γ := head :: Γ) (s := s) (u := u) (v := v)
    (cutoff := 1) (newEntry := newHead) (by simp [Ctx.depth])
    (Prevalid.tail hNew) hpv

/-- Reflexive-transitive closure insertion weakening for de Bruijn equivalence
reduction. -/
theorem MEqRedStar.insertAt {Γ : Ctx} {s : Stack} {u v : Term}
    {cutoff : Nat} {newEntry : CtxEntry}
    (hcut : cutoff ≤ Γ.depth)
    (hNew : Prevalid (newEntry :: List.drop cutoff Γ))
    (hpv : PrevalidExt Γ s) :
    MEqRedStar Γ s u v →
    MEqRedStar (Ctx.insertAt cutoff newEntry Γ) (Stack.shift cutoff s)
      (Term.shift cutoff u) (Term.shift cutoff v) := by
  intro h
  refine Relation.ReflTransGen.head_induction_on (b := v)
    (P := fun a _ =>
      MEqRedStar (Ctx.insertAt cutoff newEntry Γ) (Stack.shift cutoff s)
        (Term.shift cutoff a) (Term.shift cutoff v)) h ?_ ?_
  · exact Relation.ReflTransGen.refl
  · intro a b hHead _ ih
    exact Relation.ReflTransGen.head (MEqRedJ.insertAt hcut hNew hpv hHead) ih

/-- Reflexive-transitive closure head-extension weakening for de Bruijn
equivalence reduction. -/
theorem MEqRedStar.weaken_head {Γ : Ctx} {s : Stack} {u v : Term}
    {newEntry : CtxEntry}
    (hpv : PrevalidExt Γ s)
    (hNew : Prevalid (newEntry :: Γ)) :
    MEqRedStar Γ s u v →
    MEqRedStar (newEntry :: Γ) (Stack.shift 0 s) (Term.shift 0 u) (Term.shift 0 v) := by
  simpa using MEqRedStar.insertAt (Γ := Γ) (s := s) (u := u) (v := v)
    (cutoff := 0) (newEntry := newEntry) (Nat.zero_le Γ.depth) hNew hpv

/-- Reflexive-transitive closure weakening under one existing head binder for
de Bruijn equivalence reduction. -/
theorem MEqRedStar.weaken_tail_head {Γ : Ctx} {s : Stack} {u v : Term}
    {head newHead : CtxEntry}
    (hpv : PrevalidExt (head :: Γ) s)
    (hNew : Prevalid (head.shift 0 :: newHead :: Γ)) :
    MEqRedStar (head :: Γ) s u v →
    MEqRedStar (head.shift 0 :: newHead :: Γ) (Stack.shift 1 s)
      (Term.shift 1 u) (Term.shift 1 v) := by
  simpa using MEqRedStar.insertAt (Γ := head :: Γ) (s := s) (u := u) (v := v)
    (cutoff := 1) (newEntry := newHead) (by simp [Ctx.depth])
    (Prevalid.tail hNew) hpv

/-- Reflexive-transitive closure insertion weakening for de Bruijn subtype
reduction. -/
theorem MSubRedStar.insertAt {Γ : Ctx} {s : Stack} {u v : Term}
    {cutoff : Nat} {newEntry : CtxEntry}
    (hcut : cutoff ≤ Γ.depth)
    (hNew : Prevalid (newEntry :: List.drop cutoff Γ))
    (hpv : PrevalidExt Γ s) :
    MSubRedStar Γ s u v →
    MSubRedStar (Ctx.insertAt cutoff newEntry Γ) (Stack.shift cutoff s)
      (Term.shift cutoff u) (Term.shift cutoff v) := by
  intro h
  refine Relation.ReflTransGen.head_induction_on (b := v)
    (P := fun a _ =>
      MSubRedStar (Ctx.insertAt cutoff newEntry Γ) (Stack.shift cutoff s)
        (Term.shift cutoff a) (Term.shift cutoff v)) h ?_ ?_
  · exact Relation.ReflTransGen.refl
  · intro a b hHead _ ih
    exact Relation.ReflTransGen.head (MSubRedJ.insertAt hcut hNew hpv hHead) ih

/-- Reflexive-transitive closure head-extension weakening for de Bruijn subtype
reduction. -/
theorem MSubRedStar.weaken_head {Γ : Ctx} {s : Stack} {u v : Term}
    {newEntry : CtxEntry}
    (hpv : PrevalidExt Γ s)
    (hNew : Prevalid (newEntry :: Γ)) :
    MSubRedStar Γ s u v →
    MSubRedStar (newEntry :: Γ) (Stack.shift 0 s) (Term.shift 0 u) (Term.shift 0 v) := by
  simpa using MSubRedStar.insertAt (Γ := Γ) (s := s) (u := u) (v := v)
    (cutoff := 0) (newEntry := newEntry) (Nat.zero_le Γ.depth) hNew hpv

/-- Reflexive-transitive closure weakening under one existing head binder for
de Bruijn subtype reduction. -/
theorem MSubRedStar.weaken_tail_head {Γ : Ctx} {s : Stack} {u v : Term}
    {head newHead : CtxEntry}
    (hpv : PrevalidExt (head :: Γ) s)
    (hNew : Prevalid (head.shift 0 :: newHead :: Γ)) :
    MSubRedStar (head :: Γ) s u v →
    MSubRedStar (head.shift 0 :: newHead :: Γ) (Stack.shift 1 s)
      (Term.shift 1 u) (Term.shift 1 v) := by
  simpa using MSubRedStar.insertAt (Γ := head :: Γ) (s := s) (u := u) (v := v)
    (cutoff := 1) (newEntry := newHead) (by simp [Ctx.depth])
    (Prevalid.tail hNew) hpv

/-! ## Equ-head replacement leaf constructors -/

/-- `Me-Top` is stable when the bound stored in an innermost `.equ` head is
replaced. -/
noncomputable def MEqRed.top_equ_head_replace {Γ : Ctx} {s : Stack} {old new : Term}
    (hpv : PrevalidExt ({ bound := old, kind := .equ } :: Γ) s)
    (hnew : Term.Scoped Γ.depth new) :
    MEqRed ({ bound := new, kind := .equ } :: Γ) s .top .top :=
  MEqRed.top (PrevalidExt.equ_head_replace hpv hnew)

/-- `Me-Var` is stable when the bound stored in an innermost `.equ` head is
replaced; the context depth is unchanged. -/
noncomputable def MEqRed.var_equ_head_replace {Γ : Ctx} {s : Stack} {old new : Term}
    {i : Nat}
    (hpv : PrevalidExt ({ bound := old, kind := .equ } :: Γ) s)
    (hnew : Term.Scoped Γ.depth new)
    (hi : i < Ctx.depth ({ bound := old, kind := .equ } :: Γ)) :
    MEqRed ({ bound := new, kind := .equ } :: Γ) s (.bvar i) (.bvar i) := by
  exact MEqRed.var (PrevalidExt.equ_head_replace hpv hnew) (by
    simpa [Ctx.depth] using hi)

/-- `Me-TAp` is stable when the bound stored in an innermost `.equ` head is
replaced. -/
noncomputable def MEqRed.tAp_equ_head_replace {Γ : Ctx} {s : Stack} {old new u : Term}
    (hpv : PrevalidExt ({ bound := old, kind := .equ } :: Γ) s)
    (hnew : Term.Scoped Γ.depth new)
    (hu : Term.Scoped (Ctx.depth ({ bound := old, kind := .equ } :: Γ)) u) :
    MEqRed ({ bound := new, kind := .equ } :: Γ) s (.app .top u) .top := by
  exact MEqRed.tAp (PrevalidExt.equ_head_replace hpv hnew) (by
    simpa [Ctx.depth] using hu)

/-- Non-head `Me-Pro` is stable across an innermost `.equ` head replacement,
given the recursively replaced reduction of the looked-up bound. The index is
written as `i + 1` to rule out the changed head binding. -/
noncomputable def MEqRed.pro_equ_head_replace_succ {Γ : Ctx} {s : Stack}
    {old new : Term} {i : Nat} {α α' : Term}
    (hpv : PrevalidExt ({ bound := old, kind := .equ } :: Γ) s)
    (hnew : Term.Scoped Γ.depth new)
    (hb : Ctx.equBinds ({ bound := old, kind := .equ } :: Γ) (i + 1) α)
    (hα : MEqRed ({ bound := new, kind := .equ } :: Γ) s α α') :
    MEqRed ({ bound := new, kind := .equ } :: Γ) s (.bvar (i + 1)) α' :=
  MEqRed.pro (PrevalidExt.equ_head_replace hpv hnew)
    (Ctx.equBinds_equ_head_replace_succ hb) hα

/-- `Ms-Pro` is stable when the bound stored in an innermost `.equ` head is
replaced, because subtype lookup ignores `.equ` heads. -/
noncomputable def MSubRed.pro_equ_head_replace {Γ : Ctx} {s : Stack} {old new : Term}
    {i : Nat} {t : Term}
    (hpv : PrevalidExt ({ bound := old, kind := .equ } :: Γ) s)
    (hnew : Term.Scoped Γ.depth new)
    (hb : Ctx.subBinds ({ bound := old, kind := .equ } :: Γ) i t) :
    MSubRed ({ bound := new, kind := .equ } :: Γ) s (.bvar i) t :=
  MSubRed.pro (PrevalidExt.equ_head_replace hpv hnew)
    (Ctx.subBinds_equ_head_replace hb)

/-- `Ms-Top` is stable when the bound stored in an innermost `.equ` head is
replaced. -/
noncomputable def MSubRed.top_equ_head_replace {Γ : Ctx} {s : Stack} {old new u : Term}
    (hpv : PrevalidExt ({ bound := old, kind := .equ } :: Γ) s)
    (hnew : Term.Scoped Γ.depth new)
    (hu : Term.Scoped (Ctx.depth ({ bound := old, kind := .equ } :: Γ)) u) :
    MSubRed ({ bound := new, kind := .equ } :: Γ) s u .top := by
  exact MSubRed.top (PrevalidExt.equ_head_replace hpv hnew) (by
    simpa [Ctx.depth] using hu)

/-! ## Shape inversions -/

/-- A de Bruijn equivalence-reduction step from `Top` can only target `Top`. -/
theorem MEqRed.top_inv {Γ : Ctx} {s : Stack} {v : Term}
    (h : MEqRed Γ s .top v) : v = .top := by
  cases h with
  | top _ => rfl

/-- A de Bruijn subtype-reduction step from `Top` can only target `Top`. -/
theorem MSubRed.top_inv {Γ : Ctx} {s : Stack} {v : Term}
    (h : MSubRed Γ s .top v) : v = .top := by
  cases h with
  | top _ _ => rfl
  | equ _ heq => exact heq.top_inv

/-- A de Bruijn equivalence-reduction chain from `Top` can only target `Top`. -/
theorem MEqRedStar.top_inv {Γ : Ctx} {s : Stack} {v : Term}
    (h : MEqRedStar Γ s .top v) : v = .top := by
  induction h with
  | refl => rfl
  | tail _ hStep ih =>
      subst ih
      exact hStep.some.top_inv

/-- A de Bruijn subtype-reduction chain from `Top` can only target `Top`. -/
theorem MSubRedStar.top_inv {Γ : Ctx} {s : Stack} {v : Term}
    (h : MSubRedStar Γ s .top v) : v = .top := by
  induction h with
  | refl => rfl
  | tail _ hStep ih =>
      subst ih
      exact hStep.some.top_inv

/-- A de Bruijn equivalence-reduction step from an abstraction can only target
an abstraction. -/
theorem MEqRed.abs_inv {Γ : Ctx} {s : Stack} {bound body v : Term}
    (h : MEqRed Γ s (.abs bound body) v) :
    ∃ bound' body', v = .abs bound' body' := by
  cases h with
  | fun_ _ _ => exact ⟨_, _, rfl⟩
  | fOp _ _ _ => exact ⟨_, _, rfl⟩

/-- Detail-preserving one-step equivalence inversion from an abstraction,
separating the unapplied-function rule from the operand-stack rule. -/
theorem MEqRed.abs_inv_detail {Γ : Ctx} {s : Stack} {bound body v : Term}
    (h : MEqRed Γ s (.abs bound body) v) :
    (∃ bound' body',
      MEqRedJ Γ [] bound bound' ∧
        MEqRedJ ({ bound := bound, kind := .sub } :: Γ) [] body body' ∧
        v = .abs bound' body') ∨
      ∃ bound' α rest body',
        MEqRedJ Γ [] bound bound' ∧
          Nonempty (Term.Scoped Γ.depth α) ∧
          s = α :: rest ∧
          MEqRedJ ({ bound := α, kind := .equ } :: Γ)
            (Stack.shift 0 rest) body body' ∧
          v = .abs bound' body' := by
  cases h with
  | fun_ hBound hBody =>
    exact Or.inl ⟨_, _, ⟨hBound⟩, ⟨hBody⟩, rfl⟩
  | fOp hBound hα hBody =>
    exact Or.inr ⟨_, _, _, _, ⟨hBound⟩, ⟨hα⟩, rfl, ⟨hBody⟩, rfl⟩

/-- A de Bruijn equivalence-reduction chain from an abstraction can only target
an abstraction. -/
theorem MEqRedStar.abs_inv {Γ : Ctx} {s : Stack} {bound body v : Term}
    (h : MEqRedStar Γ s (.abs bound body) v) :
    ∃ bound' body', v = .abs bound' body' := by
  induction h with
  | refl => exact ⟨bound, body, rfl⟩
  | tail _ hStep ih =>
      obtain ⟨bound', body', hEq⟩ := ih
      subst hEq
      exact hStep.some.abs_inv

/-- A de Bruijn subtype-reduction step from an abstraction can only target
`Top` or another abstraction. -/
theorem MSubRed.abs_inv {Γ : Ctx} {s : Stack} {bound body v : Term}
    (h : MSubRed Γ s (.abs bound body) v) :
    v = .top ∨ ∃ bound' body', v = .abs bound' body' := by
  cases h with
  | top _ _ =>
    exact Or.inl rfl
  | equ _ heq =>
    exact Or.inr heq.abs_inv
  | fun_ _ _ _ =>
    exact Or.inr ⟨_, _, rfl⟩
  | fOp _ _ _ =>
    exact Or.inr ⟨_, _, rfl⟩

/-- Detail-preserving one-step subtype inversion from an abstraction. This
keeps constructor evidence for the equivalence-derived abstraction branches,
direct `Ms-Fun`, and direct `Ms-FOp`. -/
theorem MSubRed.abs_inv_detail {Γ : Ctx} {s : Stack} {bound body v : Term}
    (h : MSubRed Γ s (.abs bound body) v) :
    v = .top ∨
      (∃ bound' body',
        MEqRedJ Γ [] bound bound' ∧
          MEqRedJ ({ bound := bound, kind := .sub } :: Γ) [] body body' ∧
          v = .abs bound' body') ∨
      (∃ bound' α rest body',
        MEqRedJ Γ [] bound bound' ∧
          Nonempty (Term.Scoped Γ.depth α) ∧
          s = α :: rest ∧
          MEqRedJ ({ bound := α, kind := .equ } :: Γ)
            (Stack.shift 0 rest) body body' ∧
          v = .abs bound' body') ∨
      (∃ bound' body',
        Nonempty (Term.Scoped Γ.depth bound) ∧
          MEqRedJ Γ [] bound bound' ∧
          MSubRedJ ({ bound := bound, kind := .sub } :: Γ) [] body body' ∧
          v = .abs bound' body') ∨
      ∃ α rest body',
        Nonempty (Term.Scoped Γ.depth bound) ∧
          Nonempty (Term.Scoped Γ.depth α) ∧
          s = α :: rest ∧
          MSubRedJ ({ bound := α, kind := .equ } :: Γ)
            (Stack.shift 0 rest) body body' ∧
          v = .abs bound body' := by
  cases h with
  | top _ _ =>
    exact Or.inl rfl
  | equ _ heq =>
    cases heq.abs_inv_detail with
    | inl hFun =>
      exact Or.inr (Or.inl hFun)
    | inr hFOp =>
      exact Or.inr (Or.inr (Or.inl hFOp))
  | fun_ ht hBound hBody =>
    exact Or.inr (Or.inr (Or.inr (Or.inl
      ⟨_, _, ⟨ht⟩, ⟨hBound⟩, ⟨hBody⟩, rfl⟩)))
  | fOp ht hα hBody =>
    exact Or.inr (Or.inr (Or.inr (Or.inr
      ⟨_, _, _, ⟨ht⟩, ⟨hα⟩, rfl, ⟨hBody⟩, rfl⟩)))

/-- A de Bruijn subtype-reduction chain from an abstraction can only target
`Top` or another abstraction. -/
theorem MSubRedStar.abs_inv {Γ : Ctx} {s : Stack} {bound body v : Term}
    (h : MSubRedStar Γ s (.abs bound body) v) :
    v = .top ∨ ∃ bound' body', v = .abs bound' body' := by
  induction h with
  | refl =>
    exact Or.inr ⟨bound, body, rfl⟩
  | tail _ hStep ih =>
    cases ih with
    | inl hTop =>
      subst hTop
      exact Or.inl hStep.some.top_inv
    | inr hAbs =>
      obtain ⟨bound', body', hEq⟩ := hAbs
      subst hEq
      exact hStep.some.abs_inv

/-- A one-step equivalence reduction from a `Top`-headed application can only
target either `Top` or another `Top`-headed application. -/
theorem MEqRed.app_top_inv {Γ : Ctx} {s : Stack} {arg v : Term}
    (h : MEqRed Γ s (.app .top arg) v) :
    v = .top ∨ ∃ arg', v = .app .top arg' := by
  cases h with
  | app hOp _ =>
    have hTop := MEqRed.top_inv hOp
    subst hTop
    exact Or.inr ⟨_, rfl⟩
  | tAp _ _ =>
    exact Or.inl rfl

/-- A one-step subtype reduction from a `Top`-headed application can only
target either `Top` or another `Top`-headed application. -/
theorem MSubRed.app_top_inv {Γ : Ctx} {s : Stack} {arg v : Term}
    (h : MSubRed Γ s (.app .top arg) v) :
    v = .top ∨ ∃ arg', v = .app .top arg' := by
  cases h with
  | top _ _ =>
    exact Or.inl rfl
  | equ _ heq =>
    exact heq.app_top_inv
  | app hOp _ =>
    have hTop := MSubRed.top_inv hOp
    subst hTop
    exact Or.inr ⟨arg, rfl⟩

/-- A de Bruijn equivalence-reduction chain from a `Top`-headed application
can only target either `Top` or another `Top`-headed application. -/
theorem MEqRedStar.app_top_inv {Γ : Ctx} {s : Stack} {arg v : Term}
    (h : MEqRedStar Γ s (.app .top arg) v) :
    v = .top ∨ ∃ arg', v = .app .top arg' := by
  induction h with
  | refl =>
    exact Or.inr ⟨arg, rfl⟩
  | tail _ hStep ih =>
    cases ih with
    | inl hTop =>
      subst hTop
      exact Or.inl hStep.some.top_inv
    | inr hApp =>
      obtain ⟨arg', hEq⟩ := hApp
      subst hEq
      exact hStep.some.app_top_inv

/-- A de Bruijn subtype-reduction chain from a `Top`-headed application can
only target either `Top` or another `Top`-headed application. -/
theorem MSubRedStar.app_top_inv {Γ : Ctx} {s : Stack} {arg v : Term}
    (h : MSubRedStar Γ s (.app .top arg) v) :
    v = .top ∨ ∃ arg', v = .app .top arg' := by
  induction h with
  | refl =>
    exact Or.inr ⟨arg, rfl⟩
  | tail _ hStep ih =>
    cases ih with
    | inl hTop =>
      subst hTop
      exact Or.inl hStep.some.top_inv
    | inr hApp =>
      obtain ⟨arg', hEq⟩ := hApp
      subst hEq
      exact hStep.some.app_top_inv

/-- A one-step equivalence reduction from an abstraction-headed application
is either a β target or another abstraction-headed application. -/
theorem MEqRed.app_abs_inv {Γ : Ctx} {s : Stack}
    {bound body arg v : Term}
    (h : MEqRed Γ s (.app (.abs bound body) arg) v) :
    (∃ arg' body', v = Term.instantiate 0 arg' body') ∨
      ∃ bound' body' arg', v = .app (.abs bound' body') arg' := by
  cases h with
  | bet _ _ _ =>
    exact Or.inl ⟨_, _, rfl⟩
  | app hOp _ =>
    obtain ⟨bound', body', hEq⟩ := hOp.abs_inv
    subst hEq
    exact Or.inr ⟨bound', body', _, rfl⟩

/-- A detail-preserving one-step equivalence inversion from an
abstraction-headed application. The β branch keeps the body and argument
premises; the residual application branch keeps the operator and argument
steps. -/
theorem MEqRed.app_abs_inv_detail {Γ : Ctx} {s : Stack}
    {bound body arg v : Term}
    (h : MEqRed Γ s (.app (.abs bound body) arg) v) :
    (∃ body' arg',
      MEqRedJ ({ bound := bound, kind := .sub } :: Γ) (Stack.shift 0 s) body body' ∧
        MEqRedJ Γ [] arg arg' ∧
        v = Term.instantiate 0 arg' body') ∨
      ∃ bound' body' arg',
        MEqRedJ Γ (arg :: s) (.abs bound body) (.abs bound' body') ∧
          MEqRedJ Γ [] arg arg' ∧
          v = .app (.abs bound' body') arg' := by
  cases h with
  | bet _ hBody hArg =>
    exact Or.inl ⟨_, _, ⟨hBody⟩, ⟨hArg⟩, rfl⟩
  | app hOp hArg =>
    obtain ⟨bound', body', hEq⟩ := hOp.abs_inv
    subst hEq
    exact Or.inr ⟨bound', body', _, ⟨hOp⟩, ⟨hArg⟩, rfl⟩

/-- A one-step subtype reduction from an abstraction-headed application is
either `Top`, a β target inherited through `Ms-Equ`, a `Top`-headed
application, or another abstraction-headed application. -/
theorem MSubRed.app_abs_inv {Γ : Ctx} {s : Stack}
    {bound body arg v : Term}
    (h : MSubRed Γ s (.app (.abs bound body) arg) v) :
    v = .top ∨
      (∃ arg' body', v = Term.instantiate 0 arg' body') ∨
      (∃ arg', v = .app .top arg') ∨
      ∃ bound' body' arg', v = .app (.abs bound' body') arg' := by
  cases h with
  | top _ _ =>
    exact Or.inl rfl
  | equ _ heq =>
    cases heq.app_abs_inv with
    | inl hBet =>
      exact Or.inr (Or.inl hBet)
    | inr hApp =>
      exact Or.inr (Or.inr (Or.inr hApp))
  | app hOp _ =>
    cases hOp.abs_inv with
    | inl hTop =>
      subst hTop
      exact Or.inr (Or.inr (Or.inl ⟨arg, rfl⟩))
    | inr hAbs =>
      obtain ⟨bound', body', hEq⟩ := hAbs
      subst hEq
      exact Or.inr (Or.inr (Or.inr ⟨bound', body', arg, rfl⟩))

/-- A detail-preserving one-step subtype inversion from an
abstraction-headed application. Besides the immediate `Top` target, it
separates β targets inherited through `Ms-Equ`, residual applications
inherited through `Ms-Equ`, structural `Ms-App` targets whose operator reaches
`Top`, and structural `Ms-App` targets whose operator remains an abstraction. -/
theorem MSubRed.app_abs_inv_detail {Γ : Ctx} {s : Stack}
    {bound body arg v : Term}
    (h : MSubRed Γ s (.app (.abs bound body) arg) v) :
    v = .top ∨
      (∃ body' arg',
        MEqRedJ ({ bound := bound, kind := .sub } :: Γ) (Stack.shift 0 s) body body' ∧
          MEqRedJ Γ [] arg arg' ∧
          v = Term.instantiate 0 arg' body') ∨
      (∃ bound' body' arg',
        MEqRedJ Γ (arg :: s) (.abs bound body) (.abs bound' body') ∧
          MEqRedJ Γ [] arg arg' ∧
          v = .app (.abs bound' body') arg') ∨
      (∃ arg',
        MSubRedJ Γ (arg :: s) (.abs bound body) .top ∧
          v = .app .top arg') ∨
      ∃ bound' body',
        MSubRedJ Γ (arg :: s) (.abs bound body) (.abs bound' body') ∧
          v = .app (.abs bound' body') arg := by
  cases h with
  | top _ _ =>
    exact Or.inl rfl
  | equ _ heq =>
    cases heq.app_abs_inv_detail with
    | inl hBet =>
      exact Or.inr (Or.inl hBet)
    | inr hApp =>
      exact Or.inr (Or.inr (Or.inl hApp))
  | app hOp _ =>
    cases hOp.abs_inv with
    | inl hTop =>
      subst hTop
      exact Or.inr (Or.inr (Or.inr (Or.inl ⟨arg, ⟨hOp⟩, rfl⟩)))
    | inr hAbs =>
      obtain ⟨bound', body', hEq⟩ := hAbs
      subst hEq
      exact Or.inr (Or.inr (Or.inr (Or.inr ⟨bound', body', ⟨hOp⟩, rfl⟩)))

/-- A chain of equivalence reductions from an abstraction-headed application
either has already taken a β step, in which case the final target remains
reachable from that β target, or it is still abstraction-headed. -/
theorem MEqRedStar.app_abs_inv {Γ : Ctx} {s : Stack}
    {bound body arg v : Term}
    (h : MEqRedStar Γ s (.app (.abs bound body) arg) v) :
    (∃ arg' body', MEqRedStar Γ s (Term.instantiate 0 arg' body') v) ∨
      ∃ bound' body' arg', v = .app (.abs bound' body') arg' := by
  induction h with
  | refl =>
    exact Or.inr ⟨bound, body, arg, rfl⟩
  | tail _ hStep ih =>
    cases ih with
    | inl hBet =>
      obtain ⟨arg', body', hChain⟩ := hBet
      exact Or.inl ⟨arg', body', Relation.ReflTransGen.tail hChain hStep⟩
    | inr hApp =>
      obtain ⟨bound', body', arg', hEq⟩ := hApp
      subst hEq
      cases hStep.some.app_abs_inv with
      | inl hBet =>
        obtain ⟨arg'', body'', hEq⟩ := hBet
        subst hEq
        exact Or.inl ⟨arg'', body'', Relation.ReflTransGen.refl⟩
      | inr hApp =>
        exact Or.inr hApp

/-- A chain of subtype reductions from an abstraction-headed application
either reaches `Top`, has already taken a β step through `Ms-Equ`, is still
`Top`-headed, or is still abstraction-headed. The β branch is recorded as a
subtype chain from the β target to the final target. -/
theorem MSubRedStar.app_abs_inv {Γ : Ctx} {s : Stack}
    {bound body arg v : Term}
    (h : MSubRedStar Γ s (.app (.abs bound body) arg) v) :
    v = .top ∨
      (∃ arg' body', MSubRedStar Γ s (Term.instantiate 0 arg' body') v) ∨
      (∃ arg', v = .app .top arg') ∨
      ∃ bound' body' arg', v = .app (.abs bound' body') arg' := by
  induction h with
  | refl =>
    exact Or.inr (Or.inr (Or.inr ⟨bound, body, arg, rfl⟩))
  | tail _ hStep ih =>
    cases ih with
    | inl hTop =>
      subst hTop
      exact Or.inl hStep.some.top_inv
    | inr hRest =>
      cases hRest with
      | inl hBet =>
        obtain ⟨arg', body', hChain⟩ := hBet
        exact Or.inr (Or.inl ⟨arg', body', Relation.ReflTransGen.tail hChain hStep⟩)
      | inr hRest =>
        cases hRest with
        | inl hAppTop =>
          obtain ⟨arg', hEq⟩ := hAppTop
          subst hEq
          cases hStep.some.app_top_inv with
          | inl hTop =>
            exact Or.inl hTop
          | inr hAppTop =>
            exact Or.inr (Or.inr (Or.inl hAppTop))
        | inr hAppAbs =>
          obtain ⟨bound', body', arg', hEq⟩ := hAppAbs
          subst hEq
          cases hStep.some.app_abs_inv with
          | inl hTop =>
            exact Or.inl hTop
          | inr hRest =>
            cases hRest with
            | inl hBet =>
              obtain ⟨arg'', body'', hEq⟩ := hBet
              subst hEq
              exact Or.inr (Or.inl ⟨arg'', body'', Relation.ReflTransGen.refl⟩)
            | inr hRest =>
              cases hRest with
              | inl hAppTop =>
                exact Or.inr (Or.inr (Or.inl hAppTop))
              | inr hAppAbs =>
                exact Or.inr (Or.inr (Or.inr hAppAbs))

/-! ## Reflexivity -/

/-- Reflexivity of de Bruijn equivalence reduction.

This is direct recursion on Type-valued `Term.Scoped`, avoiding the
`Classical.choice` opacity that existed before the locally-nameless
`Term.LC` predicate was made proof-relevant. -/
noncomputable def MEqRed.refl {Γ : Ctx} {s : Stack} {u : Term}
    (hpv : PrevalidExt Γ s) (hu : Term.Scoped Γ.depth u) :
    MEqRed Γ s u u := by
  induction u generalizing Γ s with
  | bvar i =>
    exact MEqRed.var hpv hu.bvar_lt
  | top =>
    exact MEqRed.top hpv
  | app u v ihu ihv =>
    let hparts := Term.Scoped.app_inv hu
    have huOp : Term.Scoped Γ.depth u := hparts.1
    have hv : Term.Scoped Γ.depth v := hparts.2
    have hpvOp : PrevalidExt Γ (v :: s) := PrevalidExt.cons hpv hv
    have hpvNil : PrevalidExt Γ [] := PrevalidExt.nil (PrevalidExt.ctx hpv)
    exact MEqRed.app (ihu hpvOp huOp) (ihv hpvNil hv)
  | abs bound body ihBound ihBody =>
    let hparts := Term.Scoped.abs_inv hu
    have hBound : Term.Scoped Γ.depth bound := hparts.1
    have hBody : Term.Scoped (Γ.depth + 1) body := hparts.2
    have hpvNil : PrevalidExt Γ [] := PrevalidExt.nil (PrevalidExt.ctx hpv)
    have hBoundRefl : MEqRed Γ [] bound bound := ihBound hpvNil hBound
    cases s with
    | nil =>
      have hpvBodyCtx : Prevalid ({ bound := bound, kind := .sub } :: Γ) :=
        Prevalid.sub (PrevalidExt.ctx hpv) hBound
      have hpvBody : PrevalidExt ({ bound := bound, kind := .sub } :: Γ) [] :=
        PrevalidExt.nil hpvBodyCtx
      exact MEqRed.fun_ hBoundRefl (ihBody hpvBody hBody)
    | cons α s' =>
      have hα : Term.Scoped Γ.depth α := PrevalidExt.head_scoped hpv
      have hpvTail : PrevalidExt Γ s' := PrevalidExt.tail hpv
      have hpvBodyCtx : Prevalid ({ bound := α, kind := .equ } :: Γ) :=
        Prevalid.equ (PrevalidExt.ctx hpv) hα
      have hpvBody : PrevalidExt ({ bound := α, kind := .equ } :: Γ) (Stack.shift 0 s') :=
        PrevalidExt.weaken_head hpvTail hpvBodyCtx
      exact MEqRed.fOp hBoundRefl hα (ihBody hpvBody hBody)

/-- Reflexivity of de Bruijn subtype reduction, via `Ms-Equ`. -/
noncomputable def MSubRed.refl {Γ : Ctx} {s : Stack} {u : Term}
    (hpv : PrevalidExt Γ s) (hu : Term.Scoped Γ.depth u) :
    MSubRed Γ s u u :=
  MSubRed.equ hpv (MEqRed.refl hpv hu)


end DeBruijn
end Pss
