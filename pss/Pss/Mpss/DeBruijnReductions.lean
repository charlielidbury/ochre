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

/-- Type-valued reflexive-transitive closure of de Bruijn equivalence
reduction. This is used when later proofs need to construct Type-valued
evidence from a reduction chain. -/
inductive MEqRedChain (Γ : Ctx) (s : Stack) : Term → Term → Type where
  | refl {u : Term} : MEqRedChain Γ s u u
  | tail {u v w : Term} :
      MEqRedChain Γ s u v →
      MEqRed Γ s v w →
      MEqRedChain Γ s u w

/-- Type-valued reflexive-transitive closure of de Bruijn subtype
reduction. -/
inductive MSubRedChain (Γ : Ctx) (s : Stack) : Term → Term → Type where
  | refl {u : Term} : MSubRedChain Γ s u u
  | tail {u v w : Term} :
      MSubRedChain Γ s u v →
      MSubRed Γ s v w →
      MSubRedChain Γ s u w

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

/-- A single de Bruijn equivalence-reduction step embeds into the
Type-valued equivalence closure. -/
def MEqRedChain.single {Γ : Ctx} {s : Stack} {u v : Term}
    (h : MEqRed Γ s u v) : MEqRedChain Γ s u v :=
  MEqRedChain.tail MEqRedChain.refl h

/-- Type-valued equivalence-chain transitivity. -/
noncomputable def MEqRedChain.trans {Γ : Ctx} {s : Stack} {u v w : Term}
    (h₁ : MEqRedChain Γ s u v) (h₂ : MEqRedChain Γ s v w) :
    MEqRedChain Γ s u w := by
  induction h₂ with
  | refl =>
      exact h₁
  | tail hChain hStep ih =>
      exact MEqRedChain.tail ih hStep

/-- A single de Bruijn subtype-reduction step embeds into the Type-valued
subtype closure. -/
def MSubRedChain.single {Γ : Ctx} {s : Stack} {u v : Term}
    (h : MSubRed Γ s u v) : MSubRedChain Γ s u v :=
  MSubRedChain.tail MSubRedChain.refl h

/-- Type-valued subtype-chain transitivity. -/
noncomputable def MSubRedChain.trans {Γ : Ctx} {s : Stack} {u v w : Term}
    (h₁ : MSubRedChain Γ s u v) (h₂ : MSubRedChain Γ s v w) :
    MSubRedChain Γ s u w := by
  induction h₂ with
  | refl =>
      exact h₁
  | tail hChain hStep ih =>
      exact MSubRedChain.tail ih hStep

/-- Type-valued equivalence chains embed into the existing Prop-valued
closure. -/
theorem MEqRedChain.to_star {Γ : Ctx} {s : Stack} {u v : Term}
    (h : MEqRedChain Γ s u v) : MEqRedStar Γ s u v := by
  induction h with
  | refl =>
      exact Relation.ReflTransGen.refl
  | tail hChain hStep ih =>
      exact MEqRedStar.trans ih (MEqRedStar.single hStep)

/-- Type-valued subtype chains embed into the existing Prop-valued closure. -/
theorem MSubRedChain.to_star {Γ : Ctx} {s : Stack} {u v : Term}
    (h : MSubRedChain Γ s u v) : MSubRedStar Γ s u v := by
  induction h with
  | refl =>
      exact Relation.ReflTransGen.refl
  | tail hChain hStep ih =>
      exact MSubRedStar.trans ih (MSubRedStar.single hStep)

/-- Prop-valued equivalence closures contain a Type-valued chain witness.
This is kept as `Nonempty` so Prop eliminations stay in Prop. -/
theorem MEqRedChain.nonempty_of_star {Γ : Ctx} {s : Stack} {u v : Term}
    (h : MEqRedStar Γ s u v) : Nonempty (MEqRedChain Γ s u v) := by
  induction h with
  | refl =>
      exact ⟨MEqRedChain.refl⟩
  | tail hStar hStep ih =>
      exact ⟨MEqRedChain.tail ih.some hStep.some⟩

/-- Choose a Type-valued equivalence chain from the Prop-valued closure. -/
noncomputable def MEqRedChain.of_star {Γ : Ctx} {s : Stack} {u v : Term}
    (h : MEqRedStar Γ s u v) : MEqRedChain Γ s u v :=
  (MEqRedChain.nonempty_of_star h).some

/-- Prop-valued subtype closures contain a Type-valued chain witness. This is
kept as `Nonempty` so Prop eliminations stay in Prop. -/
theorem MSubRedChain.nonempty_of_star {Γ : Ctx} {s : Stack} {u v : Term}
    (h : MSubRedStar Γ s u v) : Nonempty (MSubRedChain Γ s u v) := by
  induction h with
  | refl =>
      exact ⟨MSubRedChain.refl⟩
  | tail hStar hStep ih =>
      exact ⟨MSubRedChain.tail ih.some hStep.some⟩

/-- Choose a Type-valued subtype chain from the Prop-valued closure. -/
noncomputable def MSubRedChain.of_star {Γ : Ctx} {s : Stack} {u v : Term}
    (h : MSubRedStar Γ s u v) : MSubRedChain Γ s u v :=
  (MSubRedChain.nonempty_of_star h).some

/-- Transport a subtype-reduction chain when each old step has a replacement
chain in the target context. -/
theorem MSubRedStar.replace_from_step_replacement {Γ Γ' : Ctx} {s : Stack}
    {u v : Term}
    (hStep : ∀ {x y : Term}, MSubRed Γ s x y → MSubRedStar Γ' s x y)
    (h : MSubRedStar Γ s u v) : MSubRedStar Γ' s u v := by
  induction h with
  | refl =>
      exact Relation.ReflTransGen.refl
  | tail hChain hLast ih =>
      exact MSubRedStar.trans ih (hStep hLast.some)

/-- Transport a subtype-reduction chain when each old step has a replacement
chain at the target stack. This is the stack-varying analogue of
`MSubRedStar.replace_from_step_replacement`; it is useful for reducing
changed-argument stack-head transports to one-step obligations. -/
theorem MSubRedStar.stack_replace_from_step_replacement {Γ Γ' : Ctx}
    {s s' : Stack} {u v : Term}
    (hStep : ∀ {x y : Term}, MSubRed Γ s x y → MSubRedStar Γ' s' x y)
    (h : MSubRedStar Γ s u v) : MSubRedStar Γ' s' u v := by
  induction h with
  | refl =>
      exact Relation.ReflTransGen.refl
  | tail hChain hLast ih =>
      exact MSubRedStar.trans ih (hStep hLast.some)

/-- Split a one-step subtype transport across a changed stack head. Stable
leaves (`Ms-Pro` and `Ms-Top`) are rebuilt directly at the new stack; the
recursive/equivalence cases are exposed as handlers. This is intentionally not
a blanket stack replacement theorem: `Ms-FOp` changes the operand head used in
the body context, and nested `Ms-App` changes the stack recursively. -/
theorem MSubRed.stack_head_replace_from_handlers {Γ : Ctx} {s : Stack}
    {old new u v : Term}
    (hpvNew : PrevalidExt Γ (new :: s))
    (hEq :
      ∀ {a b : Term},
        MEqRed Γ (old :: s) a b →
        MSubRedStar Γ (new :: s) a b)
    (hApp :
      ∀ {op op' arg : Term},
        MSubRed Γ (arg :: old :: s) op op' →
        Term.Scoped Γ.depth arg →
        MSubRedStar Γ (new :: s) (.app op arg) (.app op' arg))
    (hFOp :
      ∀ {bound body body' : Term},
        Term.Scoped Γ.depth bound →
        Term.Scoped Γ.depth old →
        MSubRed ({ bound := old, kind := .equ } :: Γ) (Stack.shift 0 s)
          body body' →
        MSubRedStar Γ (new :: s) (.abs bound body) (.abs bound body'))
    (h : MSubRed Γ (old :: s) u v) :
    MSubRedStar Γ (new :: s) u v := by
  cases h with
  | pro _ hb =>
      exact MSubRedStar.single (MSubRed.pro hpvNew hb)
  | top _ hu =>
      exact MSubRedStar.single (MSubRed.top hpvNew hu)
  | equ _ heq =>
      exact hEq heq
  | app hOp hArg =>
      exact hApp hOp hArg
  | fOp ht hArg hBody =>
      exact hFOp ht hArg hBody

/-- Split a one-step equivalence transport across a changed stack head,
preserving the equivalence conclusion. Stack-insensitive leaves are rebuilt
directly at the new stack; recursive and operand-consuming constructors are
exposed as handlers. This is the raw-equivalence analogue of
`MEqRed.stack_head_subtype_replace_from_handlers`, for body transports that
must remain `MEqRed` rather than being wrapped into subtype chains. -/
noncomputable def MEqRed.stack_head_replace_from_handlers {Γ : Ctx} {s : Stack}
    {old new u v : Term}
    (hpvNew : PrevalidExt Γ (new :: s))
    (hPro :
      ∀ {i : Nat} {α α' : Term},
        Γ.equBinds i α →
        MEqRed Γ (old :: s) α α' →
        MEqRed Γ (new :: s) (.bvar i) α')
    (hApp :
      ∀ {op op' arg arg' : Term},
        MEqRed Γ (arg :: old :: s) op op' →
        MEqRed Γ [] arg arg' →
        MEqRed Γ (new :: s) (.app op arg) (.app op' arg'))
    (hBet :
      ∀ {bound arg arg' body body' : Term},
        Term.Scoped Γ.depth bound →
        MEqRed ({ bound := bound, kind := .sub } :: Γ)
          (Stack.shift 0 (old :: s)) body body' →
        MEqRed Γ [] arg arg' →
        MEqRed Γ (new :: s) (.app (.abs bound body) arg)
          (Term.instantiate 0 arg' body'))
    (hFOp :
      ∀ {bound bound' body body' : Term},
        MEqRed Γ [] bound bound' →
        Term.Scoped Γ.depth old →
        MEqRed ({ bound := old, kind := .equ } :: Γ) (Stack.shift 0 s)
          body body' →
        MEqRed Γ (new :: s) (.abs bound body) (.abs bound' body'))
    (h : MEqRed Γ (old :: s) u v) :
    MEqRed Γ (new :: s) u v := by
  cases h with
  | top _ =>
      exact MEqRed.top hpvNew
  | var _ hi =>
      exact MEqRed.var hpvNew hi
  | pro _ hb hα =>
      exact hPro hb hα
  | app hOp hArg =>
      exact hApp hOp hArg
  | tAp _ hu =>
      exact MEqRed.tAp hpvNew hu
  | bet ht hBody hArg =>
      exact hBet ht hBody hArg
  | fOp hBound hOldScoped hBody =>
      exact hFOp hBound hOldScoped hBody

/-- Split an equivalence-origin one-step transport across a changed stack
head, producing a subtype chain at the new stack. Stack-insensitive leaves
(`Me-Top`, `Me-Var`, `Me-TAp`) are rebuilt internally via `Ms-Equ`; recursive
and operand-consuming constructors remain as explicit handlers. -/
theorem MEqRed.stack_head_subtype_replace_from_handlers {Γ : Ctx} {s : Stack}
    {old new u v : Term}
    (hpvNew : PrevalidExt Γ (new :: s))
    (hPro :
      ∀ {i : Nat} {α α' : Term},
        Γ.equBinds i α →
        MEqRed Γ (old :: s) α α' →
        MSubRedStar Γ (new :: s) (.bvar i) α')
    (hApp :
      ∀ {op op' arg arg' : Term},
        MEqRed Γ (arg :: old :: s) op op' →
        MEqRed Γ [] arg arg' →
        MSubRedStar Γ (new :: s) (.app op arg) (.app op' arg'))
    (hBet :
      ∀ {bound arg arg' body body' : Term},
        Term.Scoped Γ.depth bound →
        MEqRed ({ bound := bound, kind := .sub } :: Γ)
          (Stack.shift 0 (old :: s)) body body' →
        MEqRed Γ [] arg arg' →
        MSubRedStar Γ (new :: s) (.app (.abs bound body) arg)
          (Term.instantiate 0 arg' body'))
    (hFOp :
      ∀ {bound bound' body body' : Term},
        MEqRed Γ [] bound bound' →
        Term.Scoped Γ.depth old →
        MEqRed ({ bound := old, kind := .equ } :: Γ) (Stack.shift 0 s)
          body body' →
        MSubRedStar Γ (new :: s) (.abs bound body) (.abs bound' body'))
    (h : MEqRed Γ (old :: s) u v) :
    MSubRedStar Γ (new :: s) u v := by
  cases h with
  | top _ =>
      exact MSubRedStar.single (MSubRed.equ hpvNew (MEqRed.top hpvNew))
  | var _ hi =>
      exact MSubRedStar.single (MSubRed.equ hpvNew (MEqRed.var hpvNew hi))
  | pro _ hb hα =>
      exact hPro hb hα
  | app hOp hArg =>
      exact hApp hOp hArg
  | tAp _ hu =>
      exact MSubRedStar.single (MSubRed.equ hpvNew (MEqRed.tAp hpvNew hu))
  | bet ht hBody hArg =>
      exact hBet ht hBody hArg
  | fOp hBound hOldScoped hBody =>
      exact hFOp hBound hOldScoped hBody

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

/-- Lift an operator subtype-reduction chain under a fixed application
argument. -/
theorem MSubRedStar.app_fixed_arg {Γ : Ctx} {s : Stack}
    {arg u u' : Term} (hArgScoped : Term.Scoped Γ.depth arg)
    (h : MSubRedStar Γ (arg :: s) u u') :
    MSubRedStar Γ s (.app u arg) (.app u' arg) := by
  induction h with
  | refl =>
      exact Relation.ReflTransGen.refl
  | tail hChain hStep ih =>
      exact Relation.ReflTransGen.trans ih
        (MSubRedStar.single (MSubRed.app hStep.some hArgScoped))

/-- Lift a body subtype-reduction chain through `Ms-FOp` with fixed bound and
fixed operand. -/
theorem MSubRedStar.fOp_body_fixed {Γ : Ctx} {s : Stack}
    {t α body body' : Term}
    (ht : Term.Scoped Γ.depth t)
    (hα : Term.Scoped Γ.depth α)
    (h : MSubRedStar ({ bound := α, kind := .equ } :: Γ)
      (Stack.shift 0 s) body body') :
    MSubRedStar Γ (α :: s) (.abs t body) (.abs t body') := by
  induction h with
  | refl =>
      exact Relation.ReflTransGen.refl
  | tail hChain hStep ih =>
      exact Relation.ReflTransGen.trans ih
        (MSubRedStar.single (MSubRed.fOp ht hα hStep.some))

/-- Lift a body subtype-reduction chain through the reflexive-bound `Ms-Fun`
shape. This only handles the fixed-bound case; the general changing-bound
`Ms-Fun` replacement needs an additional endpoint bridge. -/
theorem MSubRedStar.fun_body_fixed {Γ : Ctx}
    {t body body' : Term}
    (ht : Term.Scoped Γ.depth t)
    (hEqT : MEqRed Γ [] t t)
    (h : MSubRedStar ({ bound := t, kind := .sub } :: Γ) [] body body') :
    MSubRedStar Γ [] (.abs t body) (.abs t body') := by
  induction h with
  | refl =>
      exact Relation.ReflTransGen.refl
  | tail hChain hStep ih =>
      exact Relation.ReflTransGen.trans ih
        (MSubRedStar.single (MSubRed.fun_ ht hEqT hStep.some))

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

/-- Extended-context prevalidity from de Bruijn equivalence reduction. This
recovers stack validity as well as logical-context validity. -/
noncomputable def MEqRed.prevalidExt {Γ : Ctx} {s : Stack} {u v : Term}
    (h : MEqRed Γ s u v) : PrevalidExt Γ s := by
  induction h with
  | pro hpv _ _ _ =>
    exact hpv
  | bet _ _ _ ihBody _ =>
    exact PrevalidExt.weaken_head_inv ihBody
  | top hpv =>
    exact hpv
  | app _ _ ihOp _ =>
    exact PrevalidExt.tail ihOp
  | var hpv _ =>
    exact hpv
  | fun_ hBound _ =>
    exact PrevalidExt.nil hBound.prevalid
  | tAp hpv _ =>
    exact hpv
  | fOp _ hα _ _ ihBody =>
    exact PrevalidExt.cons (PrevalidExt.weaken_head_inv ihBody) hα

/-- Extended-context prevalidity from de Bruijn subtype reduction. This
recovers stack validity as well as logical-context validity. -/
noncomputable def MSubRed.prevalidExt {Γ : Ctx} {s : Stack} {u v : Term}
    (h : MSubRed Γ s u v) : PrevalidExt Γ s := by
  induction h with
  | pro hpv _ =>
    exact hpv
  | top hpv _ =>
    exact hpv
  | equ hpv _ =>
    exact hpv
  | app _ _ ih =>
    exact PrevalidExt.tail ih
  | fun_ _ heq _ _ =>
    exact PrevalidExt.nil heq.prevalid
  | fOp _ hα _ ih =>
    exact PrevalidExt.cons (PrevalidExt.weaken_head_inv ih) hα

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

/-! ## Generic replacement lifts -/

/-- Lift an equivalence between the old and new annotations from the tail
below a replaced `.sub` entry through the replaced entry and every preserved
head above it. The endpoints are shifted by the number of heads crossed. -/
noncomputable def MEqRed.lift_replaceAt_sub_self {Γ : Ctx} {cutoff : Nat}
    {old new : Term}
    (hpvNew : Prevalid (Ctx.replaceAt cutoff { bound := new, kind := .sub } Γ))
    (hcut : cutoff < Ctx.depth Γ)
    (hOldNew : MEqRed (List.drop (cutoff + 1) Γ) [] old new) :
    MEqRed (Ctx.replaceAt cutoff { bound := new, kind := .sub } Γ) []
      (Term.shiftBy 0 (cutoff + 1) old) (Term.shiftBy 0 (cutoff + 1) new) := by
  induction Γ generalizing cutoff with
  | nil =>
      exact False.elim (Nat.not_lt_zero _ hcut)
  | cons head Γ ih =>
      cases cutoff with
      | zero =>
          simpa [Term.shift] using
            hOldNew.weaken_head (PrevalidExt.nil hOldNew.prevalid) hpvNew
      | succ cutoff =>
          have hpvTail : Prevalid (Ctx.replaceAt cutoff { bound := new, kind := .sub } Γ) :=
            Prevalid.tail hpvNew
          have hcutTail : cutoff < Ctx.depth Γ := by
            simpa [Ctx.depth] using hcut
          have hLiftTail :
              MEqRed (Ctx.replaceAt cutoff { bound := new, kind := .sub } Γ) []
                (Term.shiftBy 0 (cutoff + 1) old)
                (Term.shiftBy 0 (cutoff + 1) new) :=
            ih hpvTail hcutTail hOldNew
          have hLiftHead :
              MEqRed (head :: Ctx.replaceAt cutoff { bound := new, kind := .sub } Γ) []
                (Term.shift 0 (Term.shiftBy 0 (cutoff + 1) old))
                (Term.shift 0 (Term.shiftBy 0 (cutoff + 1) new)) :=
            hLiftTail.weaken_head (PrevalidExt.nil hLiftTail.prevalid) hpvNew
          have hOldShift :
              Term.shift 0 (Term.shiftBy 0 (cutoff + 1) old) =
                Term.shiftBy 0 (cutoff + 2) old := by
            simpa [Term.shift, Nat.add_assoc] using
              (Term.shiftBy_compose 0 (cutoff + 1) 1 old)
          have hNewShift :
              Term.shift 0 (Term.shiftBy 0 (cutoff + 1) new) =
                Term.shiftBy 0 (cutoff + 2) new := by
            simpa [Term.shift, Nat.add_assoc] using
              (Term.shiftBy_compose 0 (cutoff + 1) 1 new)
          simpa [Ctx.replaceAt, hOldShift, hNewShift] using hLiftHead

/-! ## Sub-head replacement constructors -/

/-- `Me-Top` is stable when the bound stored in an innermost `.sub` head is
replaced. -/
noncomputable def MEqRed.top_sub_head_replace {Γ : Ctx} {s : Stack} {old new : Term}
    (hpv : PrevalidExt ({ bound := old, kind := .sub } :: Γ) s)
    (hnew : Term.Scoped Γ.depth new) :
    MEqRed ({ bound := new, kind := .sub } :: Γ) s .top .top :=
  MEqRed.top (PrevalidExt.sub_head_replace hpv hnew)

/-- `Me-Var` is stable when replacing an innermost `.sub` head; the context
depth is unchanged. -/
noncomputable def MEqRed.var_sub_head_replace {Γ : Ctx} {s : Stack} {old new : Term}
    {i : Nat}
    (hpv : PrevalidExt ({ bound := old, kind := .sub } :: Γ) s)
    (hnew : Term.Scoped Γ.depth new)
    (hi : i < Ctx.depth ({ bound := old, kind := .sub } :: Γ)) :
    MEqRed ({ bound := new, kind := .sub } :: Γ) s (.bvar i) (.bvar i) := by
  exact MEqRed.var (PrevalidExt.sub_head_replace hpv hnew) (by
    simpa [Ctx.depth] using hi)

/-- `Me-TAp` is stable when replacing an innermost `.sub` head. -/
noncomputable def MEqRed.tAp_sub_head_replace {Γ : Ctx} {s : Stack} {old new u : Term}
    (hpv : PrevalidExt ({ bound := old, kind := .sub } :: Γ) s)
    (hnew : Term.Scoped Γ.depth new)
    (hu : Term.Scoped (Ctx.depth ({ bound := old, kind := .sub } :: Γ)) u) :
    MEqRed ({ bound := new, kind := .sub } :: Γ) s (.app .top u) .top := by
  exact MEqRed.tAp (PrevalidExt.sub_head_replace hpv hnew) (by
    simpa [Ctx.depth] using hu)

/-- `Me-Pro` is stable when replacing an innermost `.sub` head, because
equivalence lookup skips `.sub` heads. -/
noncomputable def MEqRed.pro_sub_head_replace {Γ : Ctx} {s : Stack}
    {old new : Term} {i : Nat} {α α' : Term}
    (hpv : PrevalidExt ({ bound := old, kind := .sub } :: Γ) s)
    (hnew : Term.Scoped Γ.depth new)
    (hb : Ctx.equBinds ({ bound := old, kind := .sub } :: Γ) i α)
    (hα : MEqRed ({ bound := new, kind := .sub } :: Γ) s α α') :
    MEqRed ({ bound := new, kind := .sub } :: Γ) s (.bvar i) α' :=
  MEqRed.pro (PrevalidExt.sub_head_replace hpv hnew)
    (Ctx.equBinds_sub_head_replace hb) hα

/-- Rebuild `Me-App` after replacing an innermost `.sub` head, assuming the
recursive premises have already been replaced. -/
noncomputable def MEqRed.app_sub_head_replace {Γ : Ctx} {s : Stack}
    {_old new u u' v v' : Term}
    (hOp : MEqRed ({ bound := new, kind := .sub } :: Γ) (v :: s) u u')
    (hArg : MEqRed ({ bound := new, kind := .sub } :: Γ) [] v v') :
    MEqRed ({ bound := new, kind := .sub } :: Γ) s (.app u v) (.app u' v') :=
  MEqRed.app hOp hArg

/-- Rebuild `Me-Fun` after replacing an innermost `.sub` head, assuming the
bound and preserved-head body premises have already been replaced. -/
noncomputable def MEqRed.fun_sub_head_replace {Γ : Ctx}
    {_old new t t' body body' : Term}
    (hBound : MEqRed ({ bound := new, kind := .sub } :: Γ) [] t t')
    (hBody : MEqRed ({ bound := t, kind := .sub } ::
        { bound := new, kind := .sub } :: Γ) [] body body') :
    MEqRed ({ bound := new, kind := .sub } :: Γ) []
      (.abs t body) (.abs t' body') :=
  MEqRed.fun_ hBound hBody

/-- Rebuild `Me-Bet` after replacing an innermost `.sub` head, assuming the
body and argument premises have already been replaced. -/
noncomputable def MEqRed.bet_sub_head_replace {Γ : Ctx} {s : Stack}
    {old new t v v' body body' : Term}
    (ht : Term.Scoped (Ctx.depth ({ bound := old, kind := .sub } :: Γ)) t)
    (hBody : MEqRed ({ bound := t, kind := .sub } ::
        { bound := new, kind := .sub } :: Γ) (Stack.shift 0 s) body body')
    (hArg : MEqRed ({ bound := new, kind := .sub } :: Γ) [] v v') :
    MEqRed ({ bound := new, kind := .sub } :: Γ) s
      (.app (.abs t body) v) (Term.instantiate 0 v' body') := by
  exact MEqRed.bet (by simpa [Ctx.depth] using ht) hBody hArg

/-- Rebuild `Me-FOp` after replacing an innermost `.sub` head, assuming the
bound and preserved-head body premises have already been replaced. -/
noncomputable def MEqRed.fOp_sub_head_replace {Γ : Ctx} {s : Stack}
    {old new t t' α body body' : Term}
    (hBound : MEqRed ({ bound := new, kind := .sub } :: Γ) [] t t')
    (hα : Term.Scoped (Ctx.depth ({ bound := old, kind := .sub } :: Γ)) α)
    (hBody : MEqRed ({ bound := α, kind := .equ } ::
        { bound := new, kind := .sub } :: Γ) (Stack.shift 0 s) body body') :
    MEqRed ({ bound := new, kind := .sub } :: Γ) (α :: s)
      (.abs t body) (.abs t' body') := by
  exact MEqRed.fOp hBound (by simpa [Ctx.depth] using hα) hBody

/-! ### Sub-head replacement under one preserved head -/

/-- `Me-Top` is stable when replacing a `.sub` entry immediately under a
preserved head. -/
noncomputable def MEqRed.top_sub_under_head_replace {Γ : Ctx} {s : Stack}
    {head : CtxEntry} {old new : Term}
    (hpv : PrevalidExt (head :: { bound := old, kind := .sub } :: Γ) s)
    (hnew : Term.Scoped Γ.depth new) :
    MEqRed (head :: { bound := new, kind := .sub } :: Γ) s .top .top :=
  MEqRed.top (PrevalidExt.sub_under_head_replace hpv hnew)

/-- `Me-Var` is stable when replacing a `.sub` entry immediately under a
preserved head. -/
noncomputable def MEqRed.var_sub_under_head_replace {Γ : Ctx} {s : Stack}
    {head : CtxEntry} {old new : Term} {i : Nat}
    (hpv : PrevalidExt (head :: { bound := old, kind := .sub } :: Γ) s)
    (hnew : Term.Scoped Γ.depth new)
    (hi : i < Ctx.depth (head :: { bound := old, kind := .sub } :: Γ)) :
    MEqRed (head :: { bound := new, kind := .sub } :: Γ) s
      (.bvar i) (.bvar i) := by
  exact MEqRed.var (PrevalidExt.sub_under_head_replace hpv hnew) (by
    simpa [Ctx.depth] using hi)

/-- `Me-TAp` is stable when replacing a `.sub` entry immediately under a
preserved head. -/
noncomputable def MEqRed.tAp_sub_under_head_replace {Γ : Ctx} {s : Stack}
    {head : CtxEntry} {old new u : Term}
    (hpv : PrevalidExt (head :: { bound := old, kind := .sub } :: Γ) s)
    (hnew : Term.Scoped Γ.depth new)
    (hu : Term.Scoped (Ctx.depth (head :: { bound := old, kind := .sub } :: Γ)) u) :
    MEqRed (head :: { bound := new, kind := .sub } :: Γ) s (.app .top u) .top := by
  exact MEqRed.tAp (PrevalidExt.sub_under_head_replace hpv hnew) (by
    simpa [Ctx.depth] using hu)

/-- `Me-Pro` is stable when replacing a `.sub` entry immediately under a
preserved head, because equivalence lookup skips `.sub` entries. -/
noncomputable def MEqRed.pro_sub_under_head_replace {Γ : Ctx} {s : Stack}
    {head : CtxEntry} {old new : Term} {i : Nat} {α α' : Term}
    (hpv : PrevalidExt (head :: { bound := old, kind := .sub } :: Γ) s)
    (hnew : Term.Scoped Γ.depth new)
    (hb : Ctx.equBinds (head :: { bound := old, kind := .sub } :: Γ) i α)
    (hα : MEqRed (head :: { bound := new, kind := .sub } :: Γ) s α α') :
    MEqRed (head :: { bound := new, kind := .sub } :: Γ) s (.bvar i) α' :=
  MEqRed.pro (PrevalidExt.sub_under_head_replace hpv hnew)
    (Ctx.equBinds_sub_under_head_replace hb) hα

/-- Rebuild `Me-App` after replacing an under-head `.sub` entry, assuming
recursive premises have already been replaced. -/
noncomputable def MEqRed.app_sub_under_head_replace {Γ : Ctx} {s : Stack}
    {head : CtxEntry} {_old new u u' v v' : Term}
    (hOp : MEqRed (head :: { bound := new, kind := .sub } :: Γ) (v :: s) u u')
    (hArg : MEqRed (head :: { bound := new, kind := .sub } :: Γ) [] v v') :
    MEqRed (head :: { bound := new, kind := .sub } :: Γ) s
      (.app u v) (.app u' v') :=
  MEqRed.app hOp hArg

/-- Rebuild `Me-Fun` after replacing an under-head `.sub` entry, assuming
the bound and body premises have already been replaced. -/
noncomputable def MEqRed.fun_sub_under_head_replace {Γ : Ctx}
    {head : CtxEntry} {_old new t t' body body' : Term}
    (hBound : MEqRed (head :: { bound := new, kind := .sub } :: Γ) [] t t')
    (hBody : MEqRed ({ bound := t, kind := .sub } :: head ::
        { bound := new, kind := .sub } :: Γ) [] body body') :
    MEqRed (head :: { bound := new, kind := .sub } :: Γ) []
      (.abs t body) (.abs t' body') :=
  MEqRed.fun_ hBound hBody

/-- Rebuild `Me-Bet` after replacing an under-head `.sub` entry, assuming
the body and argument premises have already been replaced. -/
noncomputable def MEqRed.bet_sub_under_head_replace {Γ : Ctx} {s : Stack}
    {head : CtxEntry} {old new t v v' body body' : Term}
    (ht : Term.Scoped (Ctx.depth (head :: { bound := old, kind := .sub } :: Γ)) t)
    (hBody : MEqRed ({ bound := t, kind := .sub } :: head ::
        { bound := new, kind := .sub } :: Γ) (Stack.shift 0 s) body body')
    (hArg : MEqRed (head :: { bound := new, kind := .sub } :: Γ) [] v v') :
    MEqRed (head :: { bound := new, kind := .sub } :: Γ) s
      (.app (.abs t body) v) (Term.instantiate 0 v' body') := by
  exact MEqRed.bet (by simpa [Ctx.depth] using ht) hBody hArg

/-- Rebuild `Me-FOp` after replacing an under-head `.sub` entry, assuming
the bound and body premises have already been replaced. -/
noncomputable def MEqRed.fOp_sub_under_head_replace {Γ : Ctx} {s : Stack}
    {head : CtxEntry} {old new t t' α body body' : Term}
    (hBound : MEqRed (head :: { bound := new, kind := .sub } :: Γ) [] t t')
    (hα : Term.Scoped (Ctx.depth (head :: { bound := old, kind := .sub } :: Γ)) α)
    (hBody : MEqRed ({ bound := α, kind := .equ } :: head ::
        { bound := new, kind := .sub } :: Γ) (Stack.shift 0 s) body body') :
    MEqRed (head :: { bound := new, kind := .sub } :: Γ) (α :: s)
      (.abs t body) (.abs t' body') := by
  exact MEqRed.fOp hBound (by simpa [Ctx.depth] using hα) hBody

/-! ### Subtype constructors stable across sub-head replacement -/

/-- Generic `Me-Top` transport across replacement of a `.sub` entry at any
context depth. -/
noncomputable def MEqRed.top_replaceAt_sub {Γ : Ctx} {s : Stack}
    {cutoff : Nat} {new : Term}
    (hpvNew : PrevalidExt (Ctx.replaceAt cutoff { bound := new, kind := .sub } Γ) s) :
    MEqRed (Ctx.replaceAt cutoff { bound := new, kind := .sub } Γ) s .top .top :=
  MEqRed.top hpvNew

/-- Generic `Me-Var` transport across replacement of a `.sub` entry at any
context depth. -/
noncomputable def MEqRed.var_replaceAt_sub {Γ : Ctx} {s : Stack}
    {cutoff i : Nat} {old new : Term}
    (hpvNew : PrevalidExt (Ctx.replaceAt cutoff { bound := new, kind := .sub } Γ) s)
    (hi : i < Ctx.depth (Ctx.replaceAt cutoff { bound := old, kind := .sub } Γ)) :
    MEqRed (Ctx.replaceAt cutoff { bound := new, kind := .sub } Γ) s
      (.bvar i) (.bvar i) :=
  MEqRed.var hpvNew (by simpa [Ctx.depth_replaceAt] using hi)

/-- Generic `Me-TAp` transport across replacement of a `.sub` entry at any
context depth. -/
noncomputable def MEqRed.tAp_replaceAt_sub {Γ : Ctx} {s : Stack}
    {cutoff : Nat} {old new u : Term}
    (hpvNew : PrevalidExt (Ctx.replaceAt cutoff { bound := new, kind := .sub } Γ) s)
    (hu : Term.Scoped (Ctx.depth (Ctx.replaceAt cutoff { bound := old, kind := .sub } Γ)) u) :
    MEqRed (Ctx.replaceAt cutoff { bound := new, kind := .sub } Γ) s
      (.app .top u) .top :=
  MEqRed.tAp hpvNew (by simpa [Ctx.depth_replaceAt] using hu)

/-- Generic `Me-Pro` transport across replacement of a `.sub` entry at any
context depth. Equivalence lookups are unaffected by the changed `.sub`
entry. -/
noncomputable def MEqRed.pro_replaceAt_sub {Γ : Ctx} {s : Stack}
    {cutoff i : Nat} {old new α α' : Term}
    (hpvNew : PrevalidExt (Ctx.replaceAt cutoff { bound := new, kind := .sub } Γ) s)
    (hb : Ctx.equBinds (Ctx.replaceAt cutoff { bound := old, kind := .sub } Γ) i α)
    (hα : MEqRed (Ctx.replaceAt cutoff { bound := new, kind := .sub } Γ) s α α') :
    MEqRed (Ctx.replaceAt cutoff { bound := new, kind := .sub } Γ) s
      (.bvar i) α' :=
  MEqRed.pro hpvNew (Ctx.equBinds_replaceAt_sub hb) hα

/-- Generic `Me-App` rebuilder after arbitrary-depth `.sub` replacement,
assuming both recursive premises have already been replaced. -/
noncomputable def MEqRed.app_replaceAt_sub {Γ : Ctx} {s : Stack}
    {cutoff : Nat} {new u u' v v' : Term}
    (hOp : MEqRed (Ctx.replaceAt cutoff { bound := new, kind := .sub } Γ)
      (v :: s) u u')
    (hArg : MEqRed (Ctx.replaceAt cutoff { bound := new, kind := .sub } Γ)
      [] v v') :
    MEqRed (Ctx.replaceAt cutoff { bound := new, kind := .sub } Γ) s
      (.app u v) (.app u' v') :=
  MEqRed.app hOp hArg

/-- Generic `Me-Fun` rebuilder after arbitrary-depth `.sub` replacement,
assuming the bound and body premises have already been replaced. -/
noncomputable def MEqRed.fun_replaceAt_sub {Γ : Ctx} {cutoff : Nat}
    {new t t' body body' : Term}
    (hBound : MEqRed (Ctx.replaceAt cutoff { bound := new, kind := .sub } Γ)
      [] t t')
    (hBody : MEqRed ({ bound := t, kind := .sub } ::
        Ctx.replaceAt cutoff { bound := new, kind := .sub } Γ) [] body body') :
    MEqRed (Ctx.replaceAt cutoff { bound := new, kind := .sub } Γ) []
      (.abs t body) (.abs t' body') :=
  MEqRed.fun_ hBound hBody

/-- Generic `Me-Bet` rebuilder after arbitrary-depth `.sub` replacement,
assuming body and argument premises have already been replaced. -/
noncomputable def MEqRed.bet_replaceAt_sub {Γ : Ctx} {s : Stack}
    {cutoff : Nat} {old new t v v' body body' : Term}
    (ht : Term.Scoped (Ctx.depth (Ctx.replaceAt cutoff { bound := old, kind := .sub } Γ)) t)
    (hBody : MEqRed ({ bound := t, kind := .sub } ::
        Ctx.replaceAt cutoff { bound := new, kind := .sub } Γ)
        (Stack.shift 0 s) body body')
    (hArg : MEqRed (Ctx.replaceAt cutoff { bound := new, kind := .sub } Γ)
      [] v v') :
    MEqRed (Ctx.replaceAt cutoff { bound := new, kind := .sub } Γ) s
      (.app (.abs t body) v) (Term.instantiate 0 v' body') :=
  MEqRed.bet (by simpa [Ctx.depth_replaceAt] using ht) hBody hArg

/-- Generic `Me-FOp` rebuilder after arbitrary-depth `.sub` replacement,
assuming bound and body premises have already been replaced. -/
noncomputable def MEqRed.fOp_replaceAt_sub {Γ : Ctx} {s : Stack}
    {cutoff : Nat} {old new t t' α body body' : Term}
    (hBound : MEqRed (Ctx.replaceAt cutoff { bound := new, kind := .sub } Γ)
      [] t t')
    (hα : Term.Scoped (Ctx.depth (Ctx.replaceAt cutoff { bound := old, kind := .sub } Γ)) α)
    (hBody : MEqRed ({ bound := α, kind := .equ } ::
        Ctx.replaceAt cutoff { bound := new, kind := .sub } Γ)
        (Stack.shift 0 s) body body') :
    MEqRed (Ctx.replaceAt cutoff { bound := new, kind := .sub } Γ) (α :: s)
      (.abs t body) (.abs t' body') :=
  MEqRed.fOp hBound (by simpa [Ctx.depth_replaceAt] using hα) hBody

/-- Generic `Ms-Top` transport across replacement of a `.sub` entry at any
context depth. -/
noncomputable def MSubRed.top_replaceAt_sub {Γ : Ctx} {s : Stack}
    {cutoff : Nat} {old new u : Term}
    (hpvNew : PrevalidExt (Ctx.replaceAt cutoff { bound := new, kind := .sub } Γ) s)
    (hu : Term.Scoped (Ctx.depth (Ctx.replaceAt cutoff { bound := old, kind := .sub } Γ)) u) :
    MSubRed (Ctx.replaceAt cutoff { bound := new, kind := .sub } Γ) s u .top :=
  MSubRed.top hpvNew (by simpa [Ctx.depth_replaceAt] using hu)

/-- Generic `Ms-Equ` rebuilder after arbitrary-depth `.sub` replacement,
assuming the equivalence premise has already been replaced. -/
noncomputable def MSubRed.equ_replaceAt_sub {Γ : Ctx} {s : Stack}
    {cutoff : Nat} {new u v : Term}
    (hpvNew : PrevalidExt (Ctx.replaceAt cutoff { bound := new, kind := .sub } Γ) s)
    (hEq : MEqRed (Ctx.replaceAt cutoff { bound := new, kind := .sub } Γ) s u v) :
    MSubRed (Ctx.replaceAt cutoff { bound := new, kind := .sub } Γ) s u v :=
  MSubRed.equ hpvNew hEq

/-- The changed innermost `.sub` entry reduces to the new shifted annotation
after replacement. This is the residual form of head-index `Ms-Pro`. -/
noncomputable def MSubRed.pro_sub_head_zero_residual {Γ : Ctx} {s : Stack}
    {old new : Term}
    (hpv : PrevalidExt ({ bound := old, kind := .sub } :: Γ) s)
    (hnew : Term.Scoped Γ.depth new) :
    MSubRed ({ bound := new, kind := .sub } :: Γ) s
      (.bvar 0) (Term.shift 0 new) :=
  MSubRed.pro (PrevalidExt.sub_head_replace hpv hnew) (by
    simp [Ctx.subBinds])

/-- Generic changed-slot `Ms-Pro` residual after replacing a `.sub` entry at
any context depth. -/
noncomputable def MSubRed.pro_replaceAt_sub_self {Γ : Ctx} {s : Stack}
    {cutoff : Nat} {new : Term}
    (hpv : PrevalidExt (Ctx.replaceAt cutoff { bound := new, kind := .sub } Γ) s)
    (hcut : cutoff < Ctx.depth Γ) :
    MSubRed (Ctx.replaceAt cutoff { bound := new, kind := .sub } Γ) s
      (.bvar cutoff) (Term.shiftBy 0 (cutoff + 1) new) :=
  MSubRed.pro hpv (Ctx.subBinds_replaceAt_sub_self hcut)

/-- Generic non-changed-slot `Ms-Pro` transport after replacing a `.sub`
entry at any context depth. -/
noncomputable def MSubRed.pro_replaceAt_sub_of_ne {Γ : Ctx} {s : Stack}
    {cutoff i : Nat} {old new t : Term}
    (hpv : PrevalidExt (Ctx.replaceAt cutoff { bound := new, kind := .sub } Γ) s)
    (hne : i ≠ cutoff)
    (hb : Ctx.subBinds (Ctx.replaceAt cutoff { bound := old, kind := .sub } Γ) i t) :
    MSubRed (Ctx.replaceAt cutoff { bound := new, kind := .sub } Γ) s
      (.bvar i) t :=
  MSubRed.pro hpv (Ctx.subBinds_replaceAt_sub_of_ne hne hb)

/-- Generic `Ms-App` rebuilder after arbitrary-depth `.sub` replacement,
assuming the operator premise has already been replaced. -/
noncomputable def MSubRed.app_replaceAt_sub {Γ : Ctx} {s : Stack}
    {cutoff : Nat} {old new u u' v : Term}
    (hOp : MSubRed (Ctx.replaceAt cutoff { bound := new, kind := .sub } Γ)
      (v :: s) u u')
    (hv : Term.Scoped (Ctx.depth (Ctx.replaceAt cutoff { bound := old, kind := .sub } Γ)) v) :
    MSubRed (Ctx.replaceAt cutoff { bound := new, kind := .sub } Γ) s
      (.app u v) (.app u' v) :=
  MSubRed.app hOp (by simpa [Ctx.depth_replaceAt] using hv)

/-- Generic `Ms-Fun` rebuilder after arbitrary-depth `.sub` replacement,
assuming the bound equivalence and body premises have already been replaced. -/
noncomputable def MSubRed.fun_replaceAt_sub {Γ : Ctx} {cutoff : Nat}
    {old new t t' body body' : Term}
    (ht : Term.Scoped (Ctx.depth (Ctx.replaceAt cutoff { bound := old, kind := .sub } Γ)) t)
    (hEq : MEqRed (Ctx.replaceAt cutoff { bound := new, kind := .sub } Γ) [] t t')
    (hBody : MSubRed ({ bound := t, kind := .sub } ::
        Ctx.replaceAt cutoff { bound := new, kind := .sub } Γ) [] body body') :
    MSubRed (Ctx.replaceAt cutoff { bound := new, kind := .sub } Γ) []
      (.abs t body) (.abs t' body') :=
  MSubRed.fun_ (by simpa [Ctx.depth_replaceAt] using ht) hEq hBody

/-- Generic `Ms-FOp` rebuilder after arbitrary-depth `.sub` replacement,
assuming the body premise has already been replaced. -/
noncomputable def MSubRed.fOp_replaceAt_sub {Γ : Ctx} {s : Stack}
    {cutoff : Nat} {old new t α body body' : Term}
    (ht : Term.Scoped (Ctx.depth (Ctx.replaceAt cutoff { bound := old, kind := .sub } Γ)) t)
    (hα : Term.Scoped (Ctx.depth (Ctx.replaceAt cutoff { bound := old, kind := .sub } Γ)) α)
    (hBody : MSubRed ({ bound := α, kind := .equ } ::
        Ctx.replaceAt cutoff { bound := new, kind := .sub } Γ)
        (Stack.shift 0 s) body body') :
    MSubRed (Ctx.replaceAt cutoff { bound := new, kind := .sub } Γ) (α :: s)
      (.abs t body) (.abs t body') :=
  MSubRed.fOp (by simpa [Ctx.depth_replaceAt] using ht)
    (by simpa [Ctx.depth_replaceAt] using hα) hBody

/-- Full equivalence-reduction transport across arbitrary-depth `.sub`
replacement. Since equivalence lookup ignores `.sub` entries, every
constructor is preserved exactly; recursive binder cases advance the
replacement index under the preserved binder. -/
noncomputable def MEqRed.replaceAt_sub_aux {Γold : Ctx} {s : Stack}
    {u v : Term} {old new : Term}
    (h : MEqRed Γold s u v) :
    ∀ {Γ : Ctx} {cutoff : Nat},
      Γold = Ctx.replaceAt cutoff { bound := old, kind := .sub } Γ →
      cutoff < Ctx.depth Γ →
      MEqRed (List.drop (cutoff + 1) Γ) [] old new →
      MEqRed (Ctx.replaceAt cutoff { bound := new, kind := .sub } Γ) s u v := by
  induction h with
  | pro hpv hb hα ih =>
      intro Γ cutoff hEq hcut hOldNew
      cases hEq
      have hnew : CtxEntry.ScopedIn (List.drop (cutoff + 1) Γ)
          { bound := new, kind := .sub } := by
        simpa [CtxEntry.ScopedIn, Ctx.depth] using hOldNew.scoped_right
      exact MEqRed.pro_replaceAt_sub
        (PrevalidExt.replaceAt_sub_same hpv hcut hnew)
        hb (ih rfl hcut hOldNew)
  | bet ht hBody hArg ihBody ihArg =>
      intro Γ cutoff hEq hcut hOldNew
      cases hEq
      exact MEqRed.bet_replaceAt_sub ht
        (by
          simpa [Ctx.replaceAt, Nat.add_assoc] using
            ihBody (Γ := { bound := _, kind := .sub } :: Γ)
              (cutoff := cutoff + 1) rfl
              (by simpa [Ctx.depth] using Nat.succ_lt_succ hcut)
              (by simpa [Nat.add_assoc] using hOldNew))
        (ihArg rfl hcut hOldNew)
  | top hpv =>
      intro Γ cutoff hEq hcut hOldNew
      cases hEq
      have hnew : CtxEntry.ScopedIn (List.drop (cutoff + 1) Γ)
          { bound := new, kind := .sub } := by
        simpa [CtxEntry.ScopedIn, Ctx.depth] using hOldNew.scoped_right
      exact MEqRed.top_replaceAt_sub
        (PrevalidExt.replaceAt_sub_same hpv hcut hnew)
  | app hOp hArg ihOp ihArg =>
      intro Γ cutoff hEq hcut hOldNew
      cases hEq
      exact MEqRed.app_replaceAt_sub (ihOp rfl hcut hOldNew) (ihArg rfl hcut hOldNew)
  | var hpv hi =>
      intro Γ cutoff hEq hcut hOldNew
      cases hEq
      have hnew : CtxEntry.ScopedIn (List.drop (cutoff + 1) Γ)
          { bound := new, kind := .sub } := by
        simpa [CtxEntry.ScopedIn, Ctx.depth] using hOldNew.scoped_right
      exact MEqRed.var_replaceAt_sub
        (PrevalidExt.replaceAt_sub_same hpv hcut hnew)
        hi
  | fun_ hBound hBody ihBound ihBody =>
      intro Γ cutoff hEq hcut hOldNew
      cases hEq
      exact MEqRed.fun_replaceAt_sub (ihBound rfl hcut hOldNew) (by
        simpa [Ctx.replaceAt, Nat.add_assoc] using
          ihBody (Γ := { bound := _, kind := .sub } :: Γ)
            (cutoff := cutoff + 1) rfl
            (by simpa [Ctx.depth] using Nat.succ_lt_succ hcut)
            (by simpa [Nat.add_assoc] using hOldNew))
  | tAp hpv hu =>
      intro Γ cutoff hEq hcut hOldNew
      cases hEq
      have hnew : CtxEntry.ScopedIn (List.drop (cutoff + 1) Γ)
          { bound := new, kind := .sub } := by
        simpa [CtxEntry.ScopedIn, Ctx.depth] using hOldNew.scoped_right
      exact MEqRed.tAp_replaceAt_sub
        (PrevalidExt.replaceAt_sub_same hpv hcut hnew)
        hu
  | fOp hBound hα hBody ihBound ihBody =>
      intro Γ cutoff hEq hcut hOldNew
      cases hEq
      exact MEqRed.fOp_replaceAt_sub (ihBound rfl hcut hOldNew) hα (by
        simpa [Ctx.replaceAt, Nat.add_assoc] using
          ihBody (Γ := { bound := _, kind := .equ } :: Γ)
            (cutoff := cutoff + 1) rfl
            (by simpa [Ctx.depth] using Nat.succ_lt_succ hcut)
            (by simpa [Nat.add_assoc] using hOldNew))

/-- Full equivalence-reduction transport across arbitrary-depth `.sub`
replacement. -/
noncomputable def MEqRed.replaceAt_sub {Γ : Ctx} {s : Stack} {u v : Term}
    {cutoff : Nat} {old new : Term}
    (h : MEqRed (Ctx.replaceAt cutoff { bound := old, kind := .sub } Γ) s u v)
    (hcut : cutoff < Ctx.depth Γ)
    (hOldNew : MEqRed (List.drop (cutoff + 1) Γ) [] old new) :
    MEqRed (Ctx.replaceAt cutoff { bound := new, kind := .sub } Γ) s u v :=
  h.replaceAt_sub_aux rfl hcut hOldNew

/-- Head specialization of `MEqRed.replaceAt_sub` for replacing the
innermost `.sub` binder by one equivalence step. -/
noncomputable def MEqRed.sub_head_replace {Γ : Ctx} {s : Stack} {u v : Term}
    {old new : Term}
    (h : MEqRed ({ bound := old, kind := .sub } :: Γ) s u v)
    (hOldNew : MEqRed Γ [] old new) :
    MEqRed ({ bound := new, kind := .sub } :: Γ) s u v := by
  have hcut : 0 < Ctx.depth ({ bound := old, kind := .sub } :: Γ) := by
    simp [Ctx.depth]
  simpa [Ctx.replaceAt] using
    (h.replaceAt_sub
      (Γ := { bound := old, kind := .sub } :: Γ) (cutoff := 0)
      (old := old) (new := new) hcut (by simpa using hOldNew))

/-- Two-step head replacement for equivalence reductions under an innermost
`.sub` binder. This packages the common changing-bound/body pattern: first
move from the original bound to one branch bound, then from that branch bound
to the joined bound. -/
noncomputable def MEqRed.sub_head_replace_two_step {Γ : Ctx} {s : Stack}
    {u v old mid new : Term}
    (h : MEqRed ({ bound := old, kind := .sub } :: Γ) s u v)
    (hOldMid : MEqRed Γ [] old mid)
    (hMidNew : MEqRed Γ [] mid new) :
    MEqRed ({ bound := new, kind := .sub } :: Γ) s u v :=
  (h.sub_head_replace hOldMid).sub_head_replace hMidNew

/-- Chain-level equivalence-reduction transport across arbitrary-depth `.sub`
replacement. -/
theorem MEqRedStar.replaceAt_sub {Γ : Ctx} {s : Stack} {u v : Term}
    {cutoff : Nat} {old new : Term}
    (h : MEqRedStar (Ctx.replaceAt cutoff { bound := old, kind := .sub } Γ) s u v)
    (hcut : cutoff < Ctx.depth Γ)
    (hOldNew : MEqRed (List.drop (cutoff + 1) Γ) [] old new) :
    MEqRedStar (Ctx.replaceAt cutoff { bound := new, kind := .sub } Γ) s u v := by
  induction h with
  | refl =>
      exact Relation.ReflTransGen.refl
  | tail hChain hStep ih =>
      exact Relation.ReflTransGen.tail ih
        ⟨hStep.some.replaceAt_sub hcut hOldNew⟩

/-- Head specialization of `MEqRedStar.replaceAt_sub` for replacing the
innermost `.sub` binder. -/
theorem MEqRedStar.sub_head_replace {Γ : Ctx} {s : Stack} {u v : Term}
    {old new : Term}
    (h : MEqRedStar ({ bound := old, kind := .sub } :: Γ) s u v)
    (hOldNew : MEqRed Γ [] old new) :
    MEqRedStar ({ bound := new, kind := .sub } :: Γ) s u v := by
  have hcut : 0 < Ctx.depth ({ bound := old, kind := .sub } :: Γ) := by
    simp [Ctx.depth]
  simpa [Ctx.replaceAt] using
    (MEqRedStar.replaceAt_sub
      (Γ := { bound := old, kind := .sub } :: Γ) (cutoff := 0)
      (old := old) (new := new) h hcut (by simpa using hOldNew))

/-- Chain-valued head replacement for equivalence reductions under an
innermost `.sub` binder whose bound itself moves by an equivalence chain. -/
theorem MEqRedStar.sub_head_replace_star {Γ : Ctx} {s : Stack} {u v : Term}
    {old new : Term}
    (h : MEqRedStar ({ bound := old, kind := .sub } :: Γ) s u v)
    (hOldNew : MEqRedStar Γ [] old new) :
    MEqRedStar ({ bound := new, kind := .sub } :: Γ) s u v := by
  induction hOldNew with
  | refl =>
      exact h
  | tail hChain hStep ih =>
      exact ih.sub_head_replace hStep.some

/-- Star-valued `Ms-Equ` replacement across arbitrary-depth `.sub`
replacement. -/
theorem MSubRedStar.equ_replaceAt_sub {Γ : Ctx} {s : Stack} {u v : Term}
    {cutoff : Nat} {old new : Term}
    (hpvNew : PrevalidExt (Ctx.replaceAt cutoff { bound := new, kind := .sub } Γ) s)
    (hEq : MEqRed (Ctx.replaceAt cutoff { bound := old, kind := .sub } Γ) s u v)
    (hcut : cutoff < Ctx.depth Γ)
    (hOldNew : MEqRed (List.drop (cutoff + 1) Γ) [] old new) :
    MSubRedStar (Ctx.replaceAt cutoff { bound := new, kind := .sub } Γ) s u v :=
  MSubRedStar.single
    (MSubRed.equ_replaceAt_sub hpvNew (hEq.replaceAt_sub hcut hOldNew))

/-- Head specialization of `MSubRedStar.equ_replaceAt_sub` for replacing the
innermost `.sub` binder in an `Ms-Equ` step. -/
theorem MSubRedStar.equ_sub_head_replace {Γ : Ctx} {s : Stack} {u v : Term}
    {old new : Term}
    (hpvNew : PrevalidExt ({ bound := new, kind := .sub } :: Γ) s)
    (hEq : MEqRed ({ bound := old, kind := .sub } :: Γ) s u v)
    (hOldNew : MEqRed Γ [] old new) :
    MSubRedStar ({ bound := new, kind := .sub } :: Γ) s u v := by
  have hcut : 0 < Ctx.depth ({ bound := old, kind := .sub } :: Γ) := by
    simp [Ctx.depth]
  simpa [Ctx.replaceAt] using
    (MSubRedStar.equ_replaceAt_sub
      (Γ := { bound := old, kind := .sub } :: Γ) (cutoff := 0)
      (old := old) (new := new) hpvNew hEq hcut (by simpa using hOldNew))

/-- Restricted subtype-chain head replacement for chains that originate from
equivalence. This avoids the false general `MSubRedStar` replacement shape:
arbitrary subtype steps may use `Ms-Pro` at the replaced `.sub` slot and
therefore change their target. -/
theorem MSubRedStar.of_meqStar_sub_head_replace_star {Γ : Ctx} {s : Stack}
    {u v old new : Term}
    (hpvNew : PrevalidExt ({ bound := new, kind := .sub } :: Γ) s)
    (hEq : MEqRedStar ({ bound := old, kind := .sub } :: Γ) s u v)
    (hOldNew : MEqRedStar Γ [] old new) :
    MSubRedStar ({ bound := new, kind := .sub } :: Γ) s u v :=
  MSubRedStar.of_MEqRedStar hpvNew (hEq.sub_head_replace_star hOldNew)

/-- Star-valued changed-slot `Ms-Pro` replacement residual. -/
theorem MSubRedStar.pro_replaceAt_sub_self {Γ : Ctx} {s : Stack}
    {cutoff : Nat} {new : Term}
    (hpvNew : PrevalidExt (Ctx.replaceAt cutoff { bound := new, kind := .sub } Γ) s)
    (hcut : cutoff < Ctx.depth Γ) :
    MSubRedStar (Ctx.replaceAt cutoff { bound := new, kind := .sub } Γ) s
      (.bvar cutoff) (Term.shiftBy 0 (cutoff + 1) new) :=
  MSubRedStar.single (MSubRed.pro_replaceAt_sub_self hpvNew hcut)

/-- Star-valued non-changed-slot `Ms-Pro` replacement. -/
theorem MSubRedStar.pro_replaceAt_sub_of_ne {Γ : Ctx} {s : Stack}
    {cutoff i : Nat} {old new t : Term}
    (hpvNew : PrevalidExt (Ctx.replaceAt cutoff { bound := new, kind := .sub } Γ) s)
    (hne : i ≠ cutoff)
    (hb : Ctx.subBinds (Ctx.replaceAt cutoff { bound := old, kind := .sub } Γ) i t) :
    MSubRedStar (Ctx.replaceAt cutoff { bound := new, kind := .sub } Γ) s
      (.bvar i) t :=
  MSubRedStar.single (MSubRed.pro_replaceAt_sub_of_ne hpvNew hne hb)

/-- Star-valued `Ms-Top` replacement. -/
theorem MSubRedStar.top_replaceAt_sub {Γ : Ctx} {s : Stack}
    {cutoff : Nat} {old new u : Term}
    (hpvNew : PrevalidExt (Ctx.replaceAt cutoff { bound := new, kind := .sub } Γ) s)
    (hu : Term.Scoped (Ctx.depth (Ctx.replaceAt cutoff { bound := old, kind := .sub } Γ)) u) :
    MSubRedStar (Ctx.replaceAt cutoff { bound := new, kind := .sub } Γ) s u .top :=
  MSubRedStar.single (MSubRed.top_replaceAt_sub hpvNew hu)

/-- Star-valued `Ms-App` replacement from an already-replaced operator
subtype chain. -/
theorem MSubRedStar.app_replaceAt_sub_from_operator {Γ : Ctx} {s : Stack}
    {cutoff : Nat} {old new u u' v : Term}
    (hOp : MSubRedStar (Ctx.replaceAt cutoff { bound := new, kind := .sub } Γ)
      (v :: s) u u')
    (hv : Term.Scoped (Ctx.depth (Ctx.replaceAt cutoff { bound := old, kind := .sub } Γ)) v) :
    MSubRedStar (Ctx.replaceAt cutoff { bound := new, kind := .sub } Γ) s
      (.app u v) (.app u' v) :=
  MSubRedStar.app_fixed_arg (by simpa [Ctx.depth_replaceAt] using hv) hOp

/-- Star-valued `Ms-FOp` replacement from an already-replaced body subtype
chain. -/
theorem MSubRedStar.fOp_replaceAt_sub_from_body {Γ : Ctx} {s : Stack}
    {cutoff : Nat} {old new t α body body' : Term}
    (ht : Term.Scoped (Ctx.depth (Ctx.replaceAt cutoff { bound := old, kind := .sub } Γ)) t)
    (hα : Term.Scoped (Ctx.depth (Ctx.replaceAt cutoff { bound := old, kind := .sub } Γ)) α)
    (hBody : MSubRedStar ({ bound := α, kind := .equ } ::
        Ctx.replaceAt cutoff { bound := new, kind := .sub } Γ)
        (Stack.shift 0 s) body body') :
    MSubRedStar (Ctx.replaceAt cutoff { bound := new, kind := .sub } Γ) (α :: s)
      (.abs t body) (.abs t body') :=
  MSubRedStar.fOp_body_fixed (by simpa [Ctx.depth_replaceAt] using ht)
    (by simpa [Ctx.depth_replaceAt] using hα) hBody

/-- Binder-recursive `Ms-FOp` chain replacement wrapper. Recursive body calls
under the `.equ` operand head naturally produce `replaceAt (cutoff + 1)`;
this packages the definitional fold back to the constructor context. -/
theorem MSubRedStar.fOp_replaceAt_sub_from_body_replaceAt {Γ : Ctx} {s : Stack}
    {cutoff : Nat} {old new t α body body' : Term}
    (ht : Term.Scoped (Ctx.depth (Ctx.replaceAt cutoff { bound := old, kind := .sub } Γ)) t)
    (hα : Term.Scoped (Ctx.depth (Ctx.replaceAt cutoff { bound := old, kind := .sub } Γ)) α)
    (hBody : MSubRedStar
        (Ctx.replaceAt (cutoff + 1) { bound := new, kind := .sub }
          ({ bound := α, kind := .equ } :: Γ))
        (Stack.shift 0 s) body body') :
    MSubRedStar (Ctx.replaceAt cutoff { bound := new, kind := .sub } Γ) (α :: s)
      (.abs t body) (.abs t body') :=
  MSubRedStar.fOp_replaceAt_sub_from_body (Γ := Γ) (s := s)
    (cutoff := cutoff) (old := old) (new := new)
    (t := t) (α := α) (body := body) (body' := body')
    ht hα (by simpa [Ctx.replaceAt] using hBody)

/-- Head specialization of `MSubRedStar.app_replaceAt_sub_from_operator`. -/
theorem MSubRedStar.app_sub_head_replace_from_operator {Γ : Ctx} {s : Stack}
    {old new u u' v : Term}
    (hOp : MSubRedStar ({ bound := new, kind := .sub } :: Γ)
      (v :: s) u u')
    (hv : Term.Scoped (Ctx.depth ({ bound := old, kind := .sub } :: Γ)) v) :
    MSubRedStar ({ bound := new, kind := .sub } :: Γ) s
      (.app u v) (.app u' v) := by
  simpa [Ctx.replaceAt] using
    (MSubRedStar.app_replaceAt_sub_from_operator
      (Γ := { bound := old, kind := .sub } :: Γ) (s := s)
      (cutoff := 0) (old := old) (new := new)
      (u := u) (u' := u') (v := v)
      (by simpa [Ctx.replaceAt] using hOp)
      (by simpa [Ctx.replaceAt] using hv))

/-- Head specialization of `MSubRedStar.fOp_replaceAt_sub_from_body`. -/
theorem MSubRedStar.fOp_sub_head_replace_from_body {Γ : Ctx} {s : Stack}
    {old new t α body body' : Term}
    (ht : Term.Scoped (Ctx.depth ({ bound := old, kind := .sub } :: Γ)) t)
    (hα : Term.Scoped (Ctx.depth ({ bound := old, kind := .sub } :: Γ)) α)
    (hBody : MSubRedStar ({ bound := α, kind := .equ } ::
        { bound := new, kind := .sub } :: Γ)
        (Stack.shift 0 s) body body') :
    MSubRedStar ({ bound := new, kind := .sub } :: Γ) (α :: s)
      (.abs t body) (.abs t body') := by
  simpa [Ctx.replaceAt] using
    (MSubRedStar.fOp_replaceAt_sub_from_body
      (Γ := { bound := old, kind := .sub } :: Γ) (s := s)
      (cutoff := 0) (old := old) (new := new)
      (t := t) (α := α) (body := body) (body' := body')
      (by simpa [Ctx.replaceAt] using ht)
      (by simpa [Ctx.replaceAt] using hα)
      (by simpa [Ctx.replaceAt] using hBody))

/-- Binder-recursive head specialization of
`MSubRedStar.fOp_replaceAt_sub_from_body_replaceAt`. -/
theorem MSubRedStar.fOp_sub_head_replace_from_body_replaceAt {Γ : Ctx} {s : Stack}
    {old new t α body body' : Term}
    (ht : Term.Scoped (Ctx.depth ({ bound := old, kind := .sub } :: Γ)) t)
    (hα : Term.Scoped (Ctx.depth ({ bound := old, kind := .sub } :: Γ)) α)
    (hBody : MSubRedStar
        (Ctx.replaceAt 1 { bound := new, kind := .sub }
          ({ bound := α, kind := .equ } :: { bound := old, kind := .sub } :: Γ))
        (Stack.shift 0 s) body body') :
    MSubRedStar ({ bound := new, kind := .sub } :: Γ) (α :: s)
      (.abs t body) (.abs t body') := by
  simpa [Ctx.replaceAt] using
    (MSubRedStar.fOp_sub_head_replace_from_body
      (Γ := Γ) (s := s) (old := old) (new := new)
      (t := t) (α := α) (body := body) (body' := body')
      ht hα (by simpa [Ctx.replaceAt] using hBody))

/-- Non-head `Ms-Pro` is stable when replacing an innermost `.sub` head.
The head index `0` is intentionally excluded because its target changes. -/
noncomputable def MSubRed.pro_sub_head_replace_succ {Γ : Ctx} {s : Stack}
    {old new : Term} {i : Nat} {t : Term}
    (hpv : PrevalidExt ({ bound := old, kind := .sub } :: Γ) s)
    (hnew : Term.Scoped Γ.depth new)
    (hb : Ctx.subBinds ({ bound := old, kind := .sub } :: Γ) (i + 1) t) :
    MSubRed ({ bound := new, kind := .sub } :: Γ) s (.bvar (i + 1)) t :=
  MSubRed.pro (PrevalidExt.sub_head_replace hpv hnew)
    (Ctx.subBinds_sub_head_replace_succ hb)

/-- `Ms-Top` is stable when replacing an innermost `.sub` head. -/
noncomputable def MSubRed.top_sub_head_replace {Γ : Ctx} {s : Stack}
    {old new u : Term}
    (hpv : PrevalidExt ({ bound := old, kind := .sub } :: Γ) s)
    (hnew : Term.Scoped Γ.depth new)
    (hu : Term.Scoped (Ctx.depth ({ bound := old, kind := .sub } :: Γ)) u) :
    MSubRed ({ bound := new, kind := .sub } :: Γ) s u .top := by
  exact MSubRed.top (PrevalidExt.sub_head_replace hpv hnew) (by
    simpa [Ctx.depth] using hu)

/-- `Ms-Equ` is stable when the equivalence premise has already been
transported across an innermost `.sub` head replacement. -/
noncomputable def MSubRed.equ_sub_head_replace {Γ : Ctx} {s : Stack}
    {old new u v : Term}
    (hpv : PrevalidExt ({ bound := old, kind := .sub } :: Γ) s)
    (hnew : Term.Scoped Γ.depth new)
    (hEq : MEqRed ({ bound := new, kind := .sub } :: Γ) s u v) :
    MSubRed ({ bound := new, kind := .sub } :: Γ) s u v :=
  MSubRed.equ (PrevalidExt.sub_head_replace hpv hnew) hEq

/-- Rebuild `Ms-App` after replacing an innermost `.sub` head, assuming the
operator premise has already been replaced. -/
noncomputable def MSubRed.app_sub_head_replace {Γ : Ctx} {s : Stack}
    {_old new u u' v : Term}
    (hOp : MSubRed ({ bound := new, kind := .sub } :: Γ) (v :: s) u u')
    (hv : Term.Scoped (Ctx.depth ({ bound := _old, kind := .sub } :: Γ)) v) :
    MSubRed ({ bound := new, kind := .sub } :: Γ) s (.app u v) (.app u' v) := by
  exact MSubRed.app hOp (by simpa [Ctx.depth] using hv)

/-- Rebuild `Ms-Fun` after replacing an innermost `.sub` head, assuming the
bound equivalence and preserved-head body premises have already been
replaced. -/
noncomputable def MSubRed.fun_sub_head_replace {Γ : Ctx}
    {old new t t' body body' : Term}
    (ht : Term.Scoped (Ctx.depth ({ bound := old, kind := .sub } :: Γ)) t)
    (hEq : MEqRed ({ bound := new, kind := .sub } :: Γ) [] t t')
    (hBody : MSubRed ({ bound := t, kind := .sub } ::
        { bound := new, kind := .sub } :: Γ) [] body body') :
    MSubRed ({ bound := new, kind := .sub } :: Γ) []
      (.abs t body) (.abs t' body') := by
  exact MSubRed.fun_ (by simpa [Ctx.depth] using ht) hEq hBody

/-- Rebuild `Ms-FOp` after replacing an innermost `.sub` head, assuming the
preserved-head body premise has already been replaced. -/
noncomputable def MSubRed.fOp_sub_head_replace {Γ : Ctx} {s : Stack}
    {old new t α body body' : Term}
    (ht : Term.Scoped (Ctx.depth ({ bound := old, kind := .sub } :: Γ)) t)
    (hα : Term.Scoped (Ctx.depth ({ bound := old, kind := .sub } :: Γ)) α)
    (hBody : MSubRed ({ bound := α, kind := .equ } ::
        { bound := new, kind := .sub } :: Γ) (Stack.shift 0 s) body body') :
    MSubRed ({ bound := new, kind := .sub } :: Γ) (α :: s)
      (.abs t body) (.abs t body') := by
  exact MSubRed.fOp (by simpa [Ctx.depth] using ht)
    (by simpa [Ctx.depth] using hα) hBody

/-- The changed under-head `.sub` entry reduces to the new doubly shifted
annotation after replacement. This is the residual form of index-`1`
`Ms-Pro`. -/
noncomputable def MSubRed.pro_sub_under_head_one_residual {Γ : Ctx} {s : Stack}
    {head : CtxEntry} {old new : Term}
    (hpv : PrevalidExt (head :: { bound := old, kind := .sub } :: Γ) s)
    (hnew : Term.Scoped Γ.depth new) :
    MSubRed (head :: { bound := new, kind := .sub } :: Γ) s
      (.bvar 1) (Term.shift 0 (Term.shift 0 new)) :=
  MSubRed.pro (PrevalidExt.sub_under_head_replace hpv hnew)
    (@Ctx.subBinds_sub_under_head_replace_one Γ head old new)

/-- `Ms-Pro` at the preserved head remains stable when replacing a `.sub`
entry immediately below it. -/
noncomputable def MSubRed.pro_sub_under_head_replace_zero {Γ : Ctx} {s : Stack}
    {head : CtxEntry} {old new t : Term}
    (hpv : PrevalidExt (head :: { bound := old, kind := .sub } :: Γ) s)
    (hnew : Term.Scoped Γ.depth new)
    (hb : Ctx.subBinds (head :: { bound := old, kind := .sub } :: Γ) 0 t) :
    MSubRed (head :: { bound := new, kind := .sub } :: Γ) s (.bvar 0) t :=
  MSubRed.pro (PrevalidExt.sub_under_head_replace hpv hnew)
    (Ctx.subBinds_sub_under_head_replace_zero hb)

/-- `Ms-Pro` strictly below the replaced `.sub` entry is stable. The changed
index `1` is intentionally excluded because its target changes. -/
noncomputable def MSubRed.pro_sub_under_head_replace_succ_succ {Γ : Ctx}
    {s : Stack} {head : CtxEntry} {old new : Term} {i : Nat} {t : Term}
    (hpv : PrevalidExt (head :: { bound := old, kind := .sub } :: Γ) s)
    (hnew : Term.Scoped Γ.depth new)
    (hb : Ctx.subBinds (head :: { bound := old, kind := .sub } :: Γ) (i + 2) t) :
    MSubRed (head :: { bound := new, kind := .sub } :: Γ) s (.bvar (i + 2)) t :=
  MSubRed.pro (PrevalidExt.sub_under_head_replace hpv hnew)
    (Ctx.subBinds_sub_under_head_replace_succ_succ hb)

/-- `Ms-Top` is stable when replacing a `.sub` entry immediately under a
preserved head. -/
noncomputable def MSubRed.top_sub_under_head_replace {Γ : Ctx} {s : Stack}
    {head : CtxEntry} {old new u : Term}
    (hpv : PrevalidExt (head :: { bound := old, kind := .sub } :: Γ) s)
    (hnew : Term.Scoped Γ.depth new)
    (hu : Term.Scoped (Ctx.depth (head :: { bound := old, kind := .sub } :: Γ)) u) :
    MSubRed (head :: { bound := new, kind := .sub } :: Γ) s u .top := by
  exact MSubRed.top (PrevalidExt.sub_under_head_replace hpv hnew) (by
    simpa [Ctx.depth] using hu)

/-- `Ms-Equ` is stable when the equivalence premise has already been
transported across an under-head `.sub` replacement. -/
noncomputable def MSubRed.equ_sub_under_head_replace {Γ : Ctx} {s : Stack}
    {head : CtxEntry} {old new u v : Term}
    (hpv : PrevalidExt (head :: { bound := old, kind := .sub } :: Γ) s)
    (hnew : Term.Scoped Γ.depth new)
    (hEq : MEqRed (head :: { bound := new, kind := .sub } :: Γ) s u v) :
    MSubRed (head :: { bound := new, kind := .sub } :: Γ) s u v :=
  MSubRed.equ (PrevalidExt.sub_under_head_replace hpv hnew) hEq

/-- Rebuild `Ms-App` after replacing an under-head `.sub` entry, assuming
the operator premise has already been replaced. -/
noncomputable def MSubRed.app_sub_under_head_replace {Γ : Ctx} {s : Stack}
    {head : CtxEntry} {_old new u u' v : Term}
    (hOp : MSubRed (head :: { bound := new, kind := .sub } :: Γ) (v :: s) u u')
    (hv : Term.Scoped (Ctx.depth (head :: { bound := _old, kind := .sub } :: Γ)) v) :
    MSubRed (head :: { bound := new, kind := .sub } :: Γ) s
      (.app u v) (.app u' v) := by
  exact MSubRed.app hOp (by simpa [Ctx.depth] using hv)

/-- Rebuild `Ms-Fun` after replacing an under-head `.sub` entry, assuming
the bound equivalence and body premises have already been replaced. -/
noncomputable def MSubRed.fun_sub_under_head_replace {Γ : Ctx}
    {head : CtxEntry} {old new t t' body body' : Term}
    (ht : Term.Scoped (Ctx.depth (head :: { bound := old, kind := .sub } :: Γ)) t)
    (hEq : MEqRed (head :: { bound := new, kind := .sub } :: Γ) [] t t')
    (hBody : MSubRed ({ bound := t, kind := .sub } :: head ::
        { bound := new, kind := .sub } :: Γ) [] body body') :
    MSubRed (head :: { bound := new, kind := .sub } :: Γ) []
      (.abs t body) (.abs t' body') := by
  exact MSubRed.fun_ (by simpa [Ctx.depth] using ht) hEq hBody

/-- Rebuild `Ms-FOp` after replacing an under-head `.sub` entry, assuming
the body premise has already been replaced. -/
noncomputable def MSubRed.fOp_sub_under_head_replace {Γ : Ctx} {s : Stack}
    {head : CtxEntry} {old new t α body body' : Term}
    (ht : Term.Scoped (Ctx.depth (head :: { bound := old, kind := .sub } :: Γ)) t)
    (hα : Term.Scoped (Ctx.depth (head :: { bound := old, kind := .sub } :: Γ)) α)
    (hBody : MSubRed ({ bound := α, kind := .equ } :: head ::
        { bound := new, kind := .sub } :: Γ) (Stack.shift 0 s) body body') :
    MSubRed (head :: { bound := new, kind := .sub } :: Γ) (α :: s)
      (.abs t body) (.abs t body') := by
  exact MSubRed.fOp (by simpa [Ctx.depth] using ht)
    (by simpa [Ctx.depth] using hα) hBody

/-- Star-valued residual for the changed under-head `.sub` lookup. -/
theorem MSubRedStar.pro_sub_under_head_one_residual {Γ : Ctx} {s : Stack}
    {head : CtxEntry} {old new : Term}
    (hpv : PrevalidExt (head :: { bound := old, kind := .sub } :: Γ) s)
    (hnew : Term.Scoped Γ.depth new) :
    MSubRedStar (head :: { bound := new, kind := .sub } :: Γ) s
      (.bvar 1) (Term.shift 0 (Term.shift 0 new)) :=
  MSubRedStar.single (MSubRed.pro_sub_under_head_one_residual hpv hnew)

/-- Star-valued stable `Ms-Pro` at the preserved head across under-head
`.sub` replacement. -/
theorem MSubRedStar.pro_sub_under_head_replace_zero {Γ : Ctx} {s : Stack}
    {head : CtxEntry} {old new t : Term}
    (hpv : PrevalidExt (head :: { bound := old, kind := .sub } :: Γ) s)
    (hnew : Term.Scoped Γ.depth new)
    (hb : Ctx.subBinds (head :: { bound := old, kind := .sub } :: Γ) 0 t) :
    MSubRedStar (head :: { bound := new, kind := .sub } :: Γ) s
      (.bvar 0) t :=
  MSubRedStar.single (MSubRed.pro_sub_under_head_replace_zero hpv hnew hb)

/-- Star-valued stable `Ms-Pro` strictly below the changed under-head `.sub`
entry. -/
theorem MSubRedStar.pro_sub_under_head_replace_succ_succ {Γ : Ctx}
    {s : Stack} {head : CtxEntry} {old new : Term} {i : Nat} {t : Term}
    (hpv : PrevalidExt (head :: { bound := old, kind := .sub } :: Γ) s)
    (hnew : Term.Scoped Γ.depth new)
    (hb : Ctx.subBinds (head :: { bound := old, kind := .sub } :: Γ) (i + 2) t) :
    MSubRedStar (head :: { bound := new, kind := .sub } :: Γ) s
      (.bvar (i + 2)) t :=
  MSubRedStar.single (MSubRed.pro_sub_under_head_replace_succ_succ hpv hnew hb)

/-- Star-valued `Ms-Top` under one preserved head across `.sub` replacement. -/
theorem MSubRedStar.top_sub_under_head_replace {Γ : Ctx} {s : Stack}
    {head : CtxEntry} {old new u : Term}
    (hpv : PrevalidExt (head :: { bound := old, kind := .sub } :: Γ) s)
    (hnew : Term.Scoped Γ.depth new)
    (hu : Term.Scoped (Ctx.depth (head :: { bound := old, kind := .sub } :: Γ)) u) :
    MSubRedStar (head :: { bound := new, kind := .sub } :: Γ) s u .top :=
  MSubRedStar.single (MSubRed.top_sub_under_head_replace hpv hnew hu)

/-- Star-valued `Ms-Equ` under one preserved head once the equivalence premise
has already been transported. -/
theorem MSubRedStar.equ_sub_under_head_replace {Γ : Ctx} {s : Stack}
    {head : CtxEntry} {old new u v : Term}
    (hpv : PrevalidExt (head :: { bound := old, kind := .sub } :: Γ) s)
    (hnew : Term.Scoped Γ.depth new)
    (hEq : MEqRed (head :: { bound := new, kind := .sub } :: Γ) s u v) :
    MSubRedStar (head :: { bound := new, kind := .sub } :: Γ) s u v :=
  MSubRedStar.single (MSubRed.equ_sub_under_head_replace hpv hnew hEq)

/-- Star-valued `Ms-App` under one preserved head from an already transported
operator subtype chain. -/
theorem MSubRedStar.app_sub_under_head_replace_from_operator {Γ : Ctx} {s : Stack}
    {head : CtxEntry} {old new u u' v : Term}
    (hOp : MSubRedStar (head :: { bound := new, kind := .sub } :: Γ)
      (v :: s) u u')
    (hv : Term.Scoped (Ctx.depth (head :: { bound := old, kind := .sub } :: Γ)) v) :
    MSubRedStar (head :: { bound := new, kind := .sub } :: Γ) s
      (.app u v) (.app u' v) :=
  MSubRedStar.app_fixed_arg (by simpa [Ctx.depth] using hv) hOp

/-- Star-valued `Ms-FOp` under one preserved head from an already transported
body subtype chain. -/
theorem MSubRedStar.fOp_sub_under_head_replace_from_body {Γ : Ctx} {s : Stack}
    {head : CtxEntry} {old new t α body body' : Term}
    (ht : Term.Scoped (Ctx.depth (head :: { bound := old, kind := .sub } :: Γ)) t)
    (hα : Term.Scoped (Ctx.depth (head :: { bound := old, kind := .sub } :: Γ)) α)
    (hBody : MSubRedStar ({ bound := α, kind := .equ } :: head ::
        { bound := new, kind := .sub } :: Γ) (Stack.shift 0 s) body body') :
    MSubRedStar (head :: { bound := new, kind := .sub } :: Γ) (α :: s)
      (.abs t body) (.abs t body') :=
  MSubRedStar.fOp_body_fixed (by simpa [Ctx.depth] using ht)
    (by simpa [Ctx.depth] using hα) hBody

/-- Star-valued fixed-bound `Ms-Fun` under one preserved head from an already
transported body subtype chain. -/
theorem MSubRedStar.fun_sub_under_head_replace_from_body_fixed_bound {Γ : Ctx}
    {head : CtxEntry} {old new t body body' : Term}
    (ht : Term.Scoped (Ctx.depth (head :: { bound := old, kind := .sub } :: Γ)) t)
    (hEqT : MEqRed (head :: { bound := new, kind := .sub } :: Γ) [] t t)
    (hBody : MSubRedStar ({ bound := t, kind := .sub } :: head ::
        { bound := new, kind := .sub } :: Γ) [] body body') :
    MSubRedStar (head :: { bound := new, kind := .sub } :: Γ) []
      (.abs t body) (.abs t body') :=
  MSubRedStar.fun_body_fixed (by simpa [Ctx.depth] using ht) hEqT hBody

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

/-- Head `Me-Pro` across an `.equ` head replacement is the one residual case:
the lookup observes the changed head, so the old derivation reduces from the
old head bound. -/
theorem MEqRed.pro_equ_head_zero_residual {Γ : Ctx} {s : Stack}
    {old α α' : Term}
    (hb : Ctx.equBinds ({ bound := old, kind := .equ } :: Γ) 0 α)
    (hα : MEqRed ({ bound := old, kind := .equ } :: Γ) s α α') :
    α = Term.shift 0 old ∧
      MEqRedJ ({ bound := old, kind := .equ } :: Γ) s (Term.shift 0 old) α' := by
  have hαeq : α = Term.shift 0 old := Ctx.equBinds_zero_equ_inv hb
  subst hαeq
  exact ⟨rfl, ⟨hα⟩⟩

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

/-! ### Equ-head replacement constructor rebuilders -/

/-- Rebuild `Me-App` after replacing an innermost `.equ` head, assuming the
recursive operator and argument premises have already been replaced. -/
noncomputable def MEqRed.app_equ_head_replace {Γ : Ctx} {s : Stack}
    {_old new u u' v v' : Term}
    (hOp : MEqRed ({ bound := new, kind := .equ } :: Γ) (v :: s) u u')
    (hArg : MEqRed ({ bound := new, kind := .equ } :: Γ) [] v v') :
    MEqRed ({ bound := new, kind := .equ } :: Γ) s (.app u v) (.app u' v') :=
  MEqRed.app hOp hArg

/-- Rebuild `Me-Fun` after replacing an innermost `.equ` head, assuming the
bound and preserved-head body premises have already been replaced. -/
noncomputable def MEqRed.fun_equ_head_replace {Γ : Ctx}
    {_old new t t' body body' : Term}
    (hBound : MEqRed ({ bound := new, kind := .equ } :: Γ) [] t t')
    (hBody : MEqRed ({ bound := t, kind := .sub } ::
        { bound := new, kind := .equ } :: Γ) [] body body') :
    MEqRed ({ bound := new, kind := .equ } :: Γ) []
      (.abs t body) (.abs t' body') :=
  MEqRed.fun_ hBound hBody

/-- Rebuild `Me-Bet` after replacing an innermost `.equ` head, assuming the
body and argument premises have already been replaced. -/
noncomputable def MEqRed.bet_equ_head_replace {Γ : Ctx} {s : Stack}
    {old new t v v' body body' : Term}
    (ht : Term.Scoped (Ctx.depth ({ bound := old, kind := .equ } :: Γ)) t)
    (hBody : MEqRed ({ bound := t, kind := .sub } ::
        { bound := new, kind := .equ } :: Γ) (Stack.shift 0 s) body body')
    (hArg : MEqRed ({ bound := new, kind := .equ } :: Γ) [] v v') :
    MEqRed ({ bound := new, kind := .equ } :: Γ) s
      (.app (.abs t body) v) (Term.instantiate 0 v' body') := by
  exact MEqRed.bet (by simpa [Ctx.depth] using ht) hBody hArg

/-- Rebuild `Me-FOp` after replacing an innermost `.equ` head, assuming the
bound and preserved-head body premises have already been replaced. -/
noncomputable def MEqRed.fOp_equ_head_replace {Γ : Ctx} {s : Stack}
    {old new t t' α body body' : Term}
    (hBound : MEqRed ({ bound := new, kind := .equ } :: Γ) [] t t')
    (hα : Term.Scoped (Ctx.depth ({ bound := old, kind := .equ } :: Γ)) α)
    (hBody : MEqRed ({ bound := α, kind := .equ } ::
        { bound := new, kind := .equ } :: Γ) (Stack.shift 0 s) body body') :
    MEqRed ({ bound := new, kind := .equ } :: Γ) (α :: s)
      (.abs t body) (.abs t' body') := by
  exact MEqRed.fOp hBound (by simpa [Ctx.depth] using hα) hBody

/-- Split a one-step equivalence replacement across an innermost changed
`.equ` head, preserving the raw equivalence conclusion. Stable leaves are
rebuilt directly; the head `Me-Pro` residual and recursive constructors are
exposed as handlers. This is the `MEqRed`-preserving counterpart to the
diagrammatic `meqRed_equ_head_replace_from_handlers` splitter. -/
noncomputable def MEqRed.equ_head_replace_from_handlers {Γ : Ctx} {s : Stack}
    {old new u v : Term}
    (hpv : PrevalidExt ({ bound := old, kind := .equ } :: Γ) s)
    (hnew : Term.Scoped Γ.depth new)
    (hProHead :
      ∀ {target : Term},
        MEqRed ({ bound := old, kind := .equ } :: Γ) s
          (Term.shift 0 old) target →
        MEqRed ({ bound := new, kind := .equ } :: Γ) s (.bvar 0) target)
    (hProTail :
      ∀ {i : Nat} {α α' : Term},
        Ctx.equBinds ({ bound := old, kind := .equ } :: Γ) (i + 1) α →
        MEqRed ({ bound := old, kind := .equ } :: Γ) s α α' →
        MEqRed ({ bound := new, kind := .equ } :: Γ) s (.bvar (i + 1)) α')
    (hApp :
      ∀ {op op' arg arg' : Term},
        MEqRed ({ bound := old, kind := .equ } :: Γ) (arg :: s) op op' →
        MEqRed ({ bound := old, kind := .equ } :: Γ) [] arg arg' →
        MEqRed ({ bound := new, kind := .equ } :: Γ) s
          (.app op arg) (.app op' arg'))
    (hFun :
      ∀ {bound bound' body body' : Term},
        MEqRed ({ bound := old, kind := .equ } :: Γ) [] bound bound' →
        MEqRed ({ bound := bound, kind := .sub } ::
          { bound := old, kind := .equ } :: Γ) [] body body' →
        MEqRed ({ bound := new, kind := .equ } :: Γ) []
          (.abs bound body) (.abs bound' body'))
    (hBet :
      ∀ {bound arg arg' body body' : Term},
        Term.Scoped (Ctx.depth ({ bound := old, kind := .equ } :: Γ)) bound →
        MEqRed ({ bound := bound, kind := .sub } ::
          { bound := old, kind := .equ } :: Γ) (Stack.shift 0 s) body body' →
        MEqRed ({ bound := old, kind := .equ } :: Γ) [] arg arg' →
        MEqRed ({ bound := new, kind := .equ } :: Γ) s
          (.app (.abs bound body) arg) (Term.instantiate 0 arg' body'))
    (hFOp :
      ∀ {bound bound' arg body body' : Term} {rest : Stack},
        MEqRed ({ bound := old, kind := .equ } :: Γ) [] bound bound' →
        Term.Scoped (Ctx.depth ({ bound := old, kind := .equ } :: Γ)) arg →
        s = arg :: rest →
        MEqRed ({ bound := arg, kind := .equ } ::
          { bound := old, kind := .equ } :: Γ) (Stack.shift 0 rest) body body' →
        MEqRed ({ bound := new, kind := .equ } :: Γ) s
          (.abs bound body) (.abs bound' body'))
    (h : MEqRed ({ bound := old, kind := .equ } :: Γ) s u v) :
    MEqRed ({ bound := new, kind := .equ } :: Γ) s u v := by
  cases h with
  | @pro Γp sp i α α' _ hb hα =>
      cases i with
      | zero =>
          obtain ⟨hαEq, hResidual⟩ := MEqRed.pro_equ_head_zero_residual hb hα
          subst hαEq
          exact hProHead hResidual.some
      | succ i =>
          exact hProTail hb hα
  | top _ =>
      exact MEqRed.top_equ_head_replace hpv hnew
  | app hOp hArg =>
      exact hApp hOp hArg
  | var _ hi =>
      exact MEqRed.var_equ_head_replace hpv hnew hi
  | fun_ hBound hBody =>
      exact hFun hBound hBody
  | tAp _ hu =>
      exact MEqRed.tAp_equ_head_replace hpv hnew hu
  | fOp hBound hArg hBody =>
      exact hFOp hBound hArg rfl hBody
  | bet ht hBody hArg =>
      exact hBet ht hBody hArg

/-- Rebuild `Ms-Equ` after replacing an innermost `.equ` head, assuming the
equivalence premise has already been replaced. -/
noncomputable def MSubRed.equ_equ_head_replace {Γ : Ctx} {s : Stack}
    {old new u v : Term}
    (hpv : PrevalidExt ({ bound := old, kind := .equ } :: Γ) s)
    (hnew : Term.Scoped Γ.depth new)
    (hEq : MEqRed ({ bound := new, kind := .equ } :: Γ) s u v) :
    MSubRed ({ bound := new, kind := .equ } :: Γ) s u v :=
  MSubRed.equ (PrevalidExt.equ_head_replace hpv hnew) hEq

/-- Rebuild `Ms-App` after replacing an innermost `.equ` head, assuming the
operator premise has already been replaced. -/
noncomputable def MSubRed.app_equ_head_replace {Γ : Ctx} {s : Stack}
    {old new u u' v : Term}
    (hOp : MSubRed ({ bound := new, kind := .equ } :: Γ) (v :: s) u u')
    (hv : Term.Scoped (Ctx.depth ({ bound := old, kind := .equ } :: Γ)) v) :
    MSubRed ({ bound := new, kind := .equ } :: Γ) s (.app u v) (.app u' v) := by
  exact MSubRed.app hOp (by simpa [Ctx.depth] using hv)

/-- Rebuild `Ms-Fun` after replacing an innermost `.equ` head, assuming the
bound and preserved-head body premises have already been replaced. -/
noncomputable def MSubRed.fun_equ_head_replace {Γ : Ctx}
    {old new t t' body body' : Term}
    (ht : Term.Scoped (Ctx.depth ({ bound := old, kind := .equ } :: Γ)) t)
    (hBound : MEqRed ({ bound := new, kind := .equ } :: Γ) [] t t')
    (hBody : MSubRed ({ bound := t, kind := .sub } ::
        { bound := new, kind := .equ } :: Γ) [] body body') :
    MSubRed ({ bound := new, kind := .equ } :: Γ) []
      (.abs t body) (.abs t' body') := by
  exact MSubRed.fun_ (by simpa [Ctx.depth] using ht) hBound hBody

/-- Rebuild `Ms-FOp` after replacing an innermost `.equ` head, assuming the
preserved-head body premise has already been replaced. -/
noncomputable def MSubRed.fOp_equ_head_replace {Γ : Ctx} {s : Stack}
    {old new t α body body' : Term}
    (ht : Term.Scoped (Ctx.depth ({ bound := old, kind := .equ } :: Γ)) t)
    (hα : Term.Scoped (Ctx.depth ({ bound := old, kind := .equ } :: Γ)) α)
    (hBody : MSubRed ({ bound := α, kind := .equ } ::
        { bound := new, kind := .equ } :: Γ) (Stack.shift 0 s) body body') :
    MSubRed ({ bound := new, kind := .equ } :: Γ) (α :: s)
      (.abs t body) (.abs t body') := by
  exact MSubRed.fOp (by simpa [Ctx.depth] using ht) (by simpa [Ctx.depth] using hα) hBody

/-- Split a one-step subtype replacement across an innermost changed `.equ`
head, preserving the raw subtype conclusion. Stable leaves are rebuilt
directly; constructor cases whose premises must be recursively replaced are
exposed as handlers. This is the raw-`MSubRed` counterpart to
`msubRed_equ_head_replace_from_handlers`. -/
noncomputable def MSubRed.equ_head_replace_from_handlers {Γ : Ctx} {s : Stack}
    {old new u v : Term}
    (hpv : PrevalidExt ({ bound := old, kind := .equ } :: Γ) s)
    (hnew : Term.Scoped Γ.depth new)
    (hEq :
      ∀ {u v : Term},
        MEqRed ({ bound := old, kind := .equ } :: Γ) s u v →
        MEqRed ({ bound := new, kind := .equ } :: Γ) s u v)
    (hApp :
      ∀ {op op' arg : Term},
        MSubRed ({ bound := old, kind := .equ } :: Γ) (arg :: s) op op' →
        Term.Scoped (Ctx.depth ({ bound := old, kind := .equ } :: Γ)) arg →
        MSubRed ({ bound := new, kind := .equ } :: Γ) s
          (.app op arg) (.app op' arg))
    (hFun :
      ∀ {bound bound' body body' : Term},
        Term.Scoped (Ctx.depth ({ bound := old, kind := .equ } :: Γ)) bound →
        MEqRed ({ bound := old, kind := .equ } :: Γ) [] bound bound' →
        MSubRed ({ bound := bound, kind := .sub } ::
          { bound := old, kind := .equ } :: Γ) [] body body' →
        MSubRed ({ bound := new, kind := .equ } :: Γ) []
          (.abs bound body) (.abs bound' body'))
    (hFOp :
      ∀ {bound arg body body' : Term} {rest : Stack},
        Term.Scoped (Ctx.depth ({ bound := old, kind := .equ } :: Γ)) bound →
        Term.Scoped (Ctx.depth ({ bound := old, kind := .equ } :: Γ)) arg →
        s = arg :: rest →
        MSubRed ({ bound := arg, kind := .equ } ::
          { bound := old, kind := .equ } :: Γ) (Stack.shift 0 rest) body body' →
        MSubRed ({ bound := new, kind := .equ } :: Γ) s
          (.abs bound body) (.abs bound body'))
    (h : MSubRed ({ bound := old, kind := .equ } :: Γ) s u v) :
    MSubRed ({ bound := new, kind := .equ } :: Γ) s u v := by
  cases h with
  | pro _ hb =>
      exact MSubRed.pro_equ_head_replace hpv hnew hb
  | top _ hu =>
      exact MSubRed.top_equ_head_replace hpv hnew hu
  | equ _ heq =>
      exact MSubRed.equ_equ_head_replace hpv hnew (hEq heq)
  | app hOp hArg =>
      exact hApp hOp hArg
  | fun_ ht hBound hBody =>
      exact hFun ht hBound hBody
  | fOp ht hArg hBody =>
      exact hFOp ht hArg rfl hBody

/-! ### Equ-head replacement under one preserved head -/

/-- `Me-Top` is stable when replacing an `.equ` entry immediately under a
preserved head. -/
noncomputable def MEqRed.top_equ_under_head_replace {Γ : Ctx} {s : Stack}
    {head : CtxEntry} {old new : Term}
    (hpv : PrevalidExt (head :: { bound := old, kind := .equ } :: Γ) s)
    (hnew : Term.Scoped Γ.depth new) :
    MEqRed (head :: { bound := new, kind := .equ } :: Γ) s .top .top :=
  MEqRed.top (PrevalidExt.equ_under_head_replace hpv hnew)

/-- `Me-Var` is stable when replacing an `.equ` entry immediately under a
preserved head; the context depth is unchanged. -/
noncomputable def MEqRed.var_equ_under_head_replace {Γ : Ctx} {s : Stack}
    {head : CtxEntry} {old new : Term} {i : Nat}
    (hpv : PrevalidExt (head :: { bound := old, kind := .equ } :: Γ) s)
    (hnew : Term.Scoped Γ.depth new)
    (hi : i < Ctx.depth (head :: { bound := old, kind := .equ } :: Γ)) :
    MEqRed (head :: { bound := new, kind := .equ } :: Γ) s
      (.bvar i) (.bvar i) := by
  exact MEqRed.var (PrevalidExt.equ_under_head_replace hpv hnew) (by
    simpa [Ctx.depth] using hi)

/-- `Me-TAp` is stable when replacing an `.equ` entry immediately under a
preserved head. -/
noncomputable def MEqRed.tAp_equ_under_head_replace {Γ : Ctx} {s : Stack}
    {head : CtxEntry} {old new u : Term}
    (hpv : PrevalidExt (head :: { bound := old, kind := .equ } :: Γ) s)
    (hnew : Term.Scoped Γ.depth new)
    (hu : Term.Scoped (Ctx.depth (head :: { bound := old, kind := .equ } :: Γ)) u) :
    MEqRed (head :: { bound := new, kind := .equ } :: Γ) s (.app .top u) .top := by
  exact MEqRed.tAp (PrevalidExt.equ_under_head_replace hpv hnew) (by
    simpa [Ctx.depth] using hu)

/-- Preserved-head `Me-Pro` is stable across under-head `.equ` replacement,
provided the looked-up bound reduction has already been replaced. -/
noncomputable def MEqRed.pro_equ_under_head_replace_zero {Γ : Ctx} {s : Stack}
    {head : CtxEntry} {old new : Term} {α α' : Term}
    (hpv : PrevalidExt (head :: { bound := old, kind := .equ } :: Γ) s)
    (hnew : Term.Scoped Γ.depth new)
    (hb : Ctx.equBinds (head :: { bound := old, kind := .equ } :: Γ) 0 α)
    (hα : MEqRed (head :: { bound := new, kind := .equ } :: Γ) s α α') :
    MEqRed (head :: { bound := new, kind := .equ } :: Γ) s (.bvar 0) α' :=
  MEqRed.pro (PrevalidExt.equ_under_head_replace hpv hnew)
    (Ctx.equBinds_equ_under_head_replace_zero hb) hα

/-- Non-residual `Me-Pro` past the replaced under-head `.equ` entry is stable.
The changed entry itself is index `1`; this helper covers indices `2+`. -/
noncomputable def MEqRed.pro_equ_under_head_replace_succ_succ {Γ : Ctx}
    {s : Stack} {head : CtxEntry} {old new : Term} {i : Nat} {α α' : Term}
    (hpv : PrevalidExt (head :: { bound := old, kind := .equ } :: Γ) s)
    (hnew : Term.Scoped Γ.depth new)
    (hb : Ctx.equBinds (head :: { bound := old, kind := .equ } :: Γ)
      ((i + 1) + 1) α)
    (hα : MEqRed (head :: { bound := new, kind := .equ } :: Γ) s α α') :
    MEqRed (head :: { bound := new, kind := .equ } :: Γ) s
      (.bvar ((i + 1) + 1)) α' :=
  MEqRed.pro (PrevalidExt.equ_under_head_replace hpv hnew)
    (Ctx.equBinds_equ_under_head_replace_succ_succ hb) hα

/-- The replaced under-head `.equ` entry is the residual `Me-Pro` case: from
the preserved head, it sits at index `1` and exposes the old bound shifted
through both heads. -/
theorem MEqRed.pro_equ_under_head_one_residual {Γ : Ctx} {s : Stack}
    {head : CtxEntry} {old α α' : Term}
    (hb : Ctx.equBinds (head :: { bound := old, kind := .equ } :: Γ) 1 α)
    (hα : MEqRed (head :: { bound := old, kind := .equ } :: Γ) s α α') :
    α = Term.shift 0 (Term.shift 0 old) ∧
      MEqRedJ (head :: { bound := old, kind := .equ } :: Γ) s
        (Term.shift 0 (Term.shift 0 old)) α' := by
  have hαeq : α = Term.shift 0 (Term.shift 0 old) := by
    have hraw : Term.shift 0 (Term.shift 0 old) = α := by
      simpa [Ctx.equBinds] using hb
    exact hraw.symm
  subst hαeq
  exact ⟨rfl, ⟨hα⟩⟩

/-- Rebuild `Me-App` after replacing an `.equ` entry immediately under a
preserved head, assuming recursive premises have already been replaced. -/
noncomputable def MEqRed.app_equ_under_head_replace {Γ : Ctx} {s : Stack}
    {head : CtxEntry} {_old new u u' v v' : Term}
    (hOp : MEqRed (head :: { bound := new, kind := .equ } :: Γ) (v :: s) u u')
    (hArg : MEqRed (head :: { bound := new, kind := .equ } :: Γ) [] v v') :
    MEqRed (head :: { bound := new, kind := .equ } :: Γ) s
      (.app u v) (.app u' v') :=
  MEqRed.app hOp hArg

/-- Rebuild `Me-Fun` after replacing an under-head `.equ` entry, assuming
the bound and body premises have already been replaced. -/
noncomputable def MEqRed.fun_equ_under_head_replace {Γ : Ctx}
    {head : CtxEntry} {_old new t t' body body' : Term}
    (hBound : MEqRed (head :: { bound := new, kind := .equ } :: Γ) [] t t')
    (hBody : MEqRed ({ bound := t, kind := .sub } :: head ::
        { bound := new, kind := .equ } :: Γ) [] body body') :
    MEqRed (head :: { bound := new, kind := .equ } :: Γ) []
      (.abs t body) (.abs t' body') :=
  MEqRed.fun_ hBound hBody

/-- Rebuild `Me-Bet` after replacing an under-head `.equ` entry, assuming
the body and argument premises have already been replaced. -/
noncomputable def MEqRed.bet_equ_under_head_replace {Γ : Ctx} {s : Stack}
    {head : CtxEntry} {old new t v v' body body' : Term}
    (ht : Term.Scoped (Ctx.depth (head :: { bound := old, kind := .equ } :: Γ)) t)
    (hBody : MEqRed ({ bound := t, kind := .sub } :: head ::
        { bound := new, kind := .equ } :: Γ) (Stack.shift 0 s) body body')
    (hArg : MEqRed (head :: { bound := new, kind := .equ } :: Γ) [] v v') :
    MEqRed (head :: { bound := new, kind := .equ } :: Γ) s
      (.app (.abs t body) v) (Term.instantiate 0 v' body') := by
  exact MEqRed.bet (by simpa [Ctx.depth] using ht) hBody hArg

/-- Rebuild `Me-FOp` after replacing an under-head `.equ` entry, assuming
the bound and body premises have already been replaced. -/
noncomputable def MEqRed.fOp_equ_under_head_replace {Γ : Ctx} {s : Stack}
    {head : CtxEntry} {old new t t' α body body' : Term}
    (hBound : MEqRed (head :: { bound := new, kind := .equ } :: Γ) [] t t')
    (hα : Term.Scoped (Ctx.depth (head :: { bound := old, kind := .equ } :: Γ)) α)
    (hBody : MEqRed ({ bound := α, kind := .equ } :: head ::
        { bound := new, kind := .equ } :: Γ) (Stack.shift 0 s) body body') :
    MEqRed (head :: { bound := new, kind := .equ } :: Γ) (α :: s)
      (.abs t body) (.abs t' body') := by
  exact MEqRed.fOp hBound (by simpa [Ctx.depth] using hα) hBody

/-- Split a one-step equivalence replacement across a changed `.equ` entry
under one preserved head, preserving the raw equivalence conclusion. Stable
leaves are rebuilt directly; lookup-sensitive `Me-Pro` cases and recursive
constructors are exposed as handlers. -/
noncomputable def MEqRed.equ_under_head_replace_from_handlers {Γ : Ctx} {s : Stack}
    {head : CtxEntry} {old new u v : Term}
    (hpv : PrevalidExt (head :: { bound := old, kind := .equ } :: Γ) s)
    (hnew : Term.Scoped Γ.depth new)
    (hProZero :
      ∀ {α α' : Term},
        Ctx.equBinds (head :: { bound := old, kind := .equ } :: Γ) 0 α →
        MEqRed (head :: { bound := old, kind := .equ } :: Γ) s α α' →
        MEqRed (head :: { bound := new, kind := .equ } :: Γ) s (.bvar 0) α')
    (hProOne :
      ∀ {target : Term},
        MEqRed (head :: { bound := old, kind := .equ } :: Γ) s
          (Term.shift 0 (Term.shift 0 old)) target →
        MEqRed (head :: { bound := new, kind := .equ } :: Γ) s (.bvar 1) target)
    (hProTail :
      ∀ {i : Nat} {α α' : Term},
        Ctx.equBinds (head :: { bound := old, kind := .equ } :: Γ) ((i + 1) + 1) α →
        MEqRed (head :: { bound := old, kind := .equ } :: Γ) s α α' →
        MEqRed (head :: { bound := new, kind := .equ } :: Γ) s
          (.bvar ((i + 1) + 1)) α')
    (hApp :
      ∀ {op op' arg arg' : Term},
        MEqRed (head :: { bound := old, kind := .equ } :: Γ) (arg :: s) op op' →
        MEqRed (head :: { bound := old, kind := .equ } :: Γ) [] arg arg' →
        MEqRed (head :: { bound := new, kind := .equ } :: Γ) s
          (.app op arg) (.app op' arg'))
    (hFun :
      ∀ {bound bound' body body' : Term},
        MEqRed (head :: { bound := old, kind := .equ } :: Γ) [] bound bound' →
        MEqRed ({ bound := bound, kind := .sub } :: head ::
          { bound := old, kind := .equ } :: Γ) [] body body' →
        MEqRed (head :: { bound := new, kind := .equ } :: Γ) []
          (.abs bound body) (.abs bound' body'))
    (hBet :
      ∀ {bound arg arg' body body' : Term},
        Term.Scoped (Ctx.depth (head :: { bound := old, kind := .equ } :: Γ)) bound →
        MEqRed ({ bound := bound, kind := .sub } :: head ::
          { bound := old, kind := .equ } :: Γ) (Stack.shift 0 s) body body' →
        MEqRed (head :: { bound := old, kind := .equ } :: Γ) [] arg arg' →
        MEqRed (head :: { bound := new, kind := .equ } :: Γ) s
          (.app (.abs bound body) arg) (Term.instantiate 0 arg' body'))
    (hFOp :
      ∀ {bound bound' arg body body' : Term} {rest : Stack},
        MEqRed (head :: { bound := old, kind := .equ } :: Γ) [] bound bound' →
        Term.Scoped (Ctx.depth (head :: { bound := old, kind := .equ } :: Γ)) arg →
        s = arg :: rest →
        MEqRed ({ bound := arg, kind := .equ } :: head ::
          { bound := old, kind := .equ } :: Γ) (Stack.shift 0 rest) body body' →
        MEqRed (head :: { bound := new, kind := .equ } :: Γ) s
          (.abs bound body) (.abs bound' body'))
    (h : MEqRed (head :: { bound := old, kind := .equ } :: Γ) s u v) :
    MEqRed (head :: { bound := new, kind := .equ } :: Γ) s u v := by
  cases h with
  | @pro Γp sp i α α' _ hb hα =>
      cases i with
      | zero =>
          exact hProZero hb hα
      | succ i =>
          cases i with
          | zero =>
              obtain ⟨hαEq, hResidual⟩ := MEqRed.pro_equ_under_head_one_residual hb hα
              subst hαEq
              exact hProOne hResidual.some
          | succ i =>
              exact hProTail hb hα
  | top _ =>
      exact MEqRed.top_equ_under_head_replace hpv hnew
  | app hOp hArg =>
      exact hApp hOp hArg
  | var _ hi =>
      exact MEqRed.var_equ_under_head_replace hpv hnew hi
  | fun_ hBound hBody =>
      exact hFun hBound hBody
  | tAp _ hu =>
      exact MEqRed.tAp_equ_under_head_replace hpv hnew hu
  | fOp hBound hArg hBody =>
      exact hFOp hBound hArg rfl hBody
  | bet ht hBody hArg =>
      exact hBet ht hBody hArg

/-- `Ms-Pro` is stable when replacing an `.equ` entry immediately under a
preserved head, because subtype lookup ignores `.equ` entries. -/
noncomputable def MSubRed.pro_equ_under_head_replace {Γ : Ctx} {s : Stack}
    {head : CtxEntry} {old new : Term} {i : Nat} {t : Term}
    (hpv : PrevalidExt (head :: { bound := old, kind := .equ } :: Γ) s)
    (hnew : Term.Scoped Γ.depth new)
    (hb : Ctx.subBinds (head :: { bound := old, kind := .equ } :: Γ) i t) :
    MSubRed (head :: { bound := new, kind := .equ } :: Γ) s (.bvar i) t :=
  MSubRed.pro (PrevalidExt.equ_under_head_replace hpv hnew)
    (Ctx.subBinds_equ_under_head_replace hb)

/-- `Ms-Top` is stable when replacing an `.equ` entry immediately under a
preserved head. -/
noncomputable def MSubRed.top_equ_under_head_replace {Γ : Ctx} {s : Stack}
    {head : CtxEntry} {old new u : Term}
    (hpv : PrevalidExt (head :: { bound := old, kind := .equ } :: Γ) s)
    (hnew : Term.Scoped Γ.depth new)
    (hu : Term.Scoped (Ctx.depth (head :: { bound := old, kind := .equ } :: Γ)) u) :
    MSubRed (head :: { bound := new, kind := .equ } :: Γ) s u .top := by
  exact MSubRed.top (PrevalidExt.equ_under_head_replace hpv hnew) (by
    simpa [Ctx.depth] using hu)

/-- Rebuild `Ms-Equ` after replacing an under-head `.equ` entry, assuming
the equivalence premise has already been replaced. -/
noncomputable def MSubRed.equ_equ_under_head_replace {Γ : Ctx} {s : Stack}
    {head : CtxEntry} {old new u v : Term}
    (hpv : PrevalidExt (head :: { bound := old, kind := .equ } :: Γ) s)
    (hnew : Term.Scoped Γ.depth new)
    (hEq : MEqRed (head :: { bound := new, kind := .equ } :: Γ) s u v) :
    MSubRed (head :: { bound := new, kind := .equ } :: Γ) s u v :=
  MSubRed.equ (PrevalidExt.equ_under_head_replace hpv hnew) hEq

/-- Rebuild `Ms-App` after replacing an under-head `.equ` entry, assuming
the operator premise has already been replaced. -/
noncomputable def MSubRed.app_equ_under_head_replace {Γ : Ctx} {s : Stack}
    {head : CtxEntry} {old new u u' v : Term}
    (hOp : MSubRed (head :: { bound := new, kind := .equ } :: Γ) (v :: s) u u')
    (hv : Term.Scoped (Ctx.depth (head :: { bound := old, kind := .equ } :: Γ)) v) :
    MSubRed (head :: { bound := new, kind := .equ } :: Γ) s
      (.app u v) (.app u' v) := by
  exact MSubRed.app hOp (by simpa [Ctx.depth] using hv)

/-- Rebuild `Ms-Fun` after replacing an under-head `.equ` entry, assuming
the bound and body premises have already been replaced. -/
noncomputable def MSubRed.fun_equ_under_head_replace {Γ : Ctx}
    {head : CtxEntry} {old new t t' body body' : Term}
    (ht : Term.Scoped (Ctx.depth (head :: { bound := old, kind := .equ } :: Γ)) t)
    (hBound : MEqRed (head :: { bound := new, kind := .equ } :: Γ) [] t t')
    (hBody : MSubRed ({ bound := t, kind := .sub } :: head ::
        { bound := new, kind := .equ } :: Γ) [] body body') :
    MSubRed (head :: { bound := new, kind := .equ } :: Γ) []
      (.abs t body) (.abs t' body') := by
  exact MSubRed.fun_ (by simpa [Ctx.depth] using ht) hBound hBody

/-- Rebuild `Ms-FOp` after replacing an under-head `.equ` entry, assuming
the body premise has already been replaced. -/
noncomputable def MSubRed.fOp_equ_under_head_replace {Γ : Ctx} {s : Stack}
    {head : CtxEntry} {old new t α body body' : Term}
    (ht : Term.Scoped (Ctx.depth (head :: { bound := old, kind := .equ } :: Γ)) t)
    (hα : Term.Scoped (Ctx.depth (head :: { bound := old, kind := .equ } :: Γ)) α)
    (hBody : MSubRed ({ bound := α, kind := .equ } :: head ::
        { bound := new, kind := .equ } :: Γ) (Stack.shift 0 s) body body') :
    MSubRed (head :: { bound := new, kind := .equ } :: Γ) (α :: s)
      (.abs t body) (.abs t body') := by
  exact MSubRed.fOp (by simpa [Ctx.depth] using ht) (by simpa [Ctx.depth] using hα) hBody

/-- Split a one-step subtype replacement across a changed `.equ` entry under
one preserved head, preserving the raw subtype conclusion. Stable leaves are
rebuilt directly; constructor cases whose premises must be recursively
replaced are exposed as handlers. -/
noncomputable def MSubRed.equ_under_head_replace_from_handlers {Γ : Ctx} {s : Stack}
    {head : CtxEntry} {old new u v : Term}
    (hpv : PrevalidExt (head :: { bound := old, kind := .equ } :: Γ) s)
    (hnew : Term.Scoped Γ.depth new)
    (hEq :
      ∀ {u v : Term},
        MEqRed (head :: { bound := old, kind := .equ } :: Γ) s u v →
        MEqRed (head :: { bound := new, kind := .equ } :: Γ) s u v)
    (hApp :
      ∀ {op op' arg : Term},
        MSubRed (head :: { bound := old, kind := .equ } :: Γ) (arg :: s) op op' →
        Term.Scoped (Ctx.depth (head :: { bound := old, kind := .equ } :: Γ)) arg →
        MSubRed (head :: { bound := new, kind := .equ } :: Γ) s
          (.app op arg) (.app op' arg))
    (hFun :
      ∀ {bound bound' body body' : Term},
        Term.Scoped (Ctx.depth (head :: { bound := old, kind := .equ } :: Γ)) bound →
        MEqRed (head :: { bound := old, kind := .equ } :: Γ) [] bound bound' →
        MSubRed ({ bound := bound, kind := .sub } :: head ::
          { bound := old, kind := .equ } :: Γ) [] body body' →
        MSubRed (head :: { bound := new, kind := .equ } :: Γ) []
          (.abs bound body) (.abs bound' body'))
    (hFOp :
      ∀ {bound arg body body' : Term} {rest : Stack},
        Term.Scoped (Ctx.depth (head :: { bound := old, kind := .equ } :: Γ)) bound →
        Term.Scoped (Ctx.depth (head :: { bound := old, kind := .equ } :: Γ)) arg →
        s = arg :: rest →
        MSubRed ({ bound := arg, kind := .equ } :: head ::
          { bound := old, kind := .equ } :: Γ) (Stack.shift 0 rest) body body' →
        MSubRed (head :: { bound := new, kind := .equ } :: Γ) s
          (.abs bound body) (.abs bound body'))
    (h : MSubRed (head :: { bound := old, kind := .equ } :: Γ) s u v) :
    MSubRed (head :: { bound := new, kind := .equ } :: Γ) s u v := by
  cases h with
  | pro _ hb =>
      exact MSubRed.pro_equ_under_head_replace hpv hnew hb
  | top _ hu =>
      exact MSubRed.top_equ_under_head_replace hpv hnew hu
  | equ _ heq =>
      exact MSubRed.equ_equ_under_head_replace hpv hnew (hEq heq)
  | app hOp hArg =>
      exact hApp hOp hArg
  | fun_ ht hBound hBody =>
      exact hFun ht hBound hBody
  | fOp ht hArg hBody =>
      exact hFOp ht hArg rfl hBody

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

/-- Detail-preserving one-step equivalence inversion from a de Bruijn
variable. -/
theorem MEqRed.bvar_inv_detail {Γ : Ctx} {s : Stack} {i : Nat} {v : Term}
    (h : MEqRed Γ s (.bvar i) v) :
    (Nonempty (PrevalidExt Γ s) ∧ i < Γ.depth ∧ v = .bvar i) ∨
      ∃ α α',
        Γ.equBinds i α ∧
          MEqRedJ Γ s α α' ∧
          v = α' := by
  cases h with
  | pro hpv hBind hRed =>
      exact Or.inr ⟨_, _, hBind, ⟨hRed⟩, rfl⟩
  | var hpv hi =>
      exact Or.inl ⟨⟨hpv⟩, hi, rfl⟩

/-- Detail-preserving one-step subtype inversion from a de Bruijn variable. -/
theorem MSubRed.bvar_inv_detail {Γ : Ctx} {s : Stack} {i : Nat} {v : Term}
    (h : MSubRed Γ s (.bvar i) v) :
    (∃ t, Γ.subBinds i t ∧ v = t) ∨
      (Nonempty (PrevalidExt Γ s) ∧
        Nonempty (Term.Scoped Γ.depth (.bvar i)) ∧
        v = .top) ∨
      ∃ t, MEqRedJ Γ s (.bvar i) t ∧ v = t := by
  cases h with
  | pro hpv hBind =>
      exact Or.inl ⟨_, hBind, rfl⟩
  | top hpv hScoped =>
      exact Or.inr (Or.inl ⟨⟨hpv⟩, ⟨hScoped⟩, rfl⟩)
  | equ hpv hEq =>
      exact Or.inr (Or.inr ⟨_, ⟨hEq⟩, rfl⟩)

/-- A de Bruijn equivalence-reduction step from an abstraction can only target
an abstraction. -/
theorem MEqRed.abs_inv {Γ : Ctx} {s : Stack} {bound body v : Term}
    (h : MEqRed Γ s (.abs bound body) v) :
    ∃ bound' body', v = .abs bound' body' := by
  cases h with
  | fun_ _ _ => exact ⟨_, _, rfl⟩
  | fOp _ _ _ => exact ⟨_, _, rfl⟩

/-- Type-valued abstraction inversion for one equivalence-reduction step.
Use this instead of `MEqRed.abs_inv` when the target proof constructs
Type-valued evidence. -/
def MEqRed.abs_inv_type {Γ : Ctx} {s : Stack} {bound body v : Term}
    (h : MEqRed Γ s (.abs bound body) v) :
    Sigma fun bound' => Sigma fun body' => PLift (v = .abs bound' body') := by
  cases h with
  | fun_ _ _ => exact ⟨_, _, ⟨rfl⟩⟩
  | fOp _ _ _ => exact ⟨_, _, ⟨rfl⟩⟩

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

/-- Bound projection for one empty-stack equivalence step between
abstractions. -/
def MEqRed.abs_bound_red {Γ : Ctx} {bound body result body' : Term}
    (h : MEqRed Γ [] (.abs bound body) (.abs result body')) :
    MEqRed Γ [] bound result := by
  cases h with
  | fun_ hBound _ =>
    exact hBound

/-- Type-valued bound projection for one empty-stack equivalence step between
abstractions. -/
def MEqRed.abs_bound_chain {Γ : Ctx} {bound body result body' : Term}
    (h : MEqRed Γ [] (.abs bound body) (.abs result body')) :
    MEqRedChain Γ [] bound result :=
  MEqRedChain.single h.abs_bound_red

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

/-- Type-valued abstraction inversion for Type-valued equivalence chains. -/
noncomputable def MEqRedChain.abs_inv_type {Γ : Ctx} {s : Stack} {bound body v : Term}
    (h : MEqRedChain Γ s (.abs bound body) v) :
    Sigma fun bound' => Sigma fun body' => PLift (v = .abs bound' body') := by
  induction h with
  | refl =>
      exact ⟨bound, body, ⟨rfl⟩⟩
  | tail _ hStep ih =>
      obtain ⟨bound', body', hEq⟩ := ih
      cases hEq with
      | up hEq =>
          subst hEq
          exact hStep.abs_inv_type

/-- Bound projection for an empty-stack equivalence chain between
abstractions. -/
theorem MEqRedStar.abs_bound_red {Γ : Ctx} {bound body result body' : Term}
    (h : MEqRedStar Γ [] (.abs bound body) (.abs result body')) :
    MEqRedStar Γ [] bound result := by
  suffices key : ∀ {target : Term},
      MEqRedStar Γ [] (.abs bound body) target →
        ∀ {result body' : Term}, target = .abs result body' →
          MEqRedStar Γ [] bound result from
    key h rfl
  intro target hChain
  induction hChain with
  | refl =>
      intro result body' hEq
      cases hEq
      exact Relation.ReflTransGen.refl
  | tail hStar hStep ih =>
      intro result body' hEq
      subst hEq
      obtain ⟨midBound, midBody, hMid⟩ := MEqRedStar.abs_inv hStar
      subst hMid
      exact MEqRedStar.trans (ih rfl)
        (MEqRedStar.single hStep.some.abs_bound_red)

/-- Type-valued bound projection for Type-valued empty-stack equivalence
chains between abstractions. -/
noncomputable def MEqRedChain.abs_bound_chain {Γ : Ctx}
    {bound body result body' : Term}
    (h : MEqRedChain Γ [] (.abs bound body) (.abs result body')) :
    MEqRedChain Γ [] bound result := by
  suffices key : ∀ {target : Term},
      MEqRedChain Γ [] (.abs bound body) target →
        ∀ {result body' : Term}, PLift (target = .abs result body') →
          MEqRedChain Γ [] bound result from
    key h ⟨rfl⟩
  intro target hChain
  induction hChain with
  | refl =>
      intro result body' hEq
      cases hEq with
      | up hEq =>
          cases hEq
          exact MEqRedChain.refl
  | tail hChain hStep ih =>
      intro result body' hEq
      cases hEq with
      | up hEq =>
          subst hEq
          obtain ⟨midBound, midBody, hMid⟩ := hChain.abs_inv_type
          cases hMid with
          | up hMid =>
              subst hMid
              exact MEqRedChain.trans (ih ⟨rfl⟩) hStep.abs_bound_chain

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

/-- Type-valued abstraction inversion for one subtype-reduction step. Use this
instead of `MSubRed.abs_inv` when the target proof constructs Type-valued
evidence. -/
def MSubRed.abs_inv_type {Γ : Ctx} {s : Stack} {bound body v : Term}
    (h : MSubRed Γ s (.abs bound body) v) :
    PLift (v = .top) ⊕
      (Sigma fun bound' => Sigma fun body' => PLift (v = .abs bound' body')) := by
  cases h with
  | top _ _ =>
    exact Sum.inl ⟨rfl⟩
  | equ _ heq =>
    obtain ⟨bound', body', hTarget⟩ := heq.abs_inv_type
    exact Sum.inr ⟨bound', body', hTarget⟩
  | fun_ _ _ _ =>
    exact Sum.inr ⟨_, _, ⟨rfl⟩⟩
  | fOp _ _ _ =>
    exact Sum.inr ⟨_, _, ⟨rfl⟩⟩

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

/-- Bound projection for one empty-stack subtype step between abstractions.
The bound changes only through an equivalence reduction; body-only function
operand steps keep it fixed. -/
theorem MSubRed.abs_bound_red {Γ : Ctx} {bound body result body' : Term}
    (h : MSubRed Γ [] (.abs bound body) (.abs result body')) :
    MEqRedStar Γ [] bound result := by
  cases h with
  | equ _ hEq =>
      exact MEqRedStar.single hEq.abs_bound_red
  | fun_ _ hBound _ =>
      exact MEqRedStar.single hBound

/-- Type-valued bound projection for one empty-stack subtype step between
abstractions. -/
def MSubRed.abs_bound_chain {Γ : Ctx} {bound body result body' : Term}
    (h : MSubRed Γ [] (.abs bound body) (.abs result body')) :
    MEqRedChain Γ [] bound result := by
  cases h with
  | equ _ hEq =>
      exact hEq.abs_bound_chain
  | fun_ _ hBound _ =>
      exact MEqRedChain.single hBound

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

/-- Type-valued abstraction inversion for Type-valued subtype chains. -/
noncomputable def MSubRedChain.abs_inv_type {Γ : Ctx} {s : Stack} {bound body v : Term}
    (h : MSubRedChain Γ s (.abs bound body) v) :
    PLift (v = .top) ⊕
      (Sigma fun bound' => Sigma fun body' => PLift (v = .abs bound' body')) := by
  induction h with
  | refl =>
      exact Sum.inr ⟨bound, body, ⟨rfl⟩⟩
  | tail _ hStep ih =>
      cases ih with
      | inl hTop =>
          cases hTop with
          | up hTop =>
              subst hTop
              exact Sum.inl ⟨hStep.top_inv⟩
      | inr hAbs =>
          obtain ⟨bound', body', hEq⟩ := hAbs
          cases hEq with
          | up hEq =>
              subst hEq
              exact hStep.abs_inv_type

/-- Bound projection for an empty-stack subtype chain between abstractions. -/
theorem MSubRedStar.abs_bound_red {Γ : Ctx} {bound body result body' : Term}
    (h : MSubRedStar Γ [] (.abs bound body) (.abs result body')) :
    MEqRedStar Γ [] bound result := by
  suffices key : ∀ {target : Term},
      MSubRedStar Γ [] (.abs bound body) target →
        ∀ {result body' : Term}, target = .abs result body' →
          MEqRedStar Γ [] bound result from
    key h rfl
  intro target hChain
  induction hChain with
  | refl =>
      intro result body' hEq
      cases hEq
      exact Relation.ReflTransGen.refl
  | tail hStar hStep ih =>
      intro result body' hEq
      subst hEq
      obtain ⟨midBound, midBody, hMid⟩ := (MSubRedStar.abs_inv hStar).resolve_left (by
        intro hTop
        subst hTop
        have hTargetTop : Term.abs result body' = Term.top :=
          MSubRed.top_inv (Nonempty.some hStep)
        cases hTargetTop)
      subst hMid
      exact MEqRedStar.trans (ih rfl) (MSubRed.abs_bound_red (Nonempty.some hStep))

/-- Type-valued bound projection for Type-valued empty-stack subtype chains
between abstractions. -/
noncomputable def MSubRedChain.abs_bound_chain {Γ : Ctx}
    {bound body result body' : Term}
    (h : MSubRedChain Γ [] (.abs bound body) (.abs result body')) :
    MEqRedChain Γ [] bound result := by
  suffices key : ∀ {target : Term},
      MSubRedChain Γ [] (.abs bound body) target →
        ∀ {result body' : Term}, PLift (target = .abs result body') →
          MEqRedChain Γ [] bound result from
    key h ⟨rfl⟩
  intro target hChain
  induction hChain with
  | refl =>
      intro result body' hEq
      cases hEq with
      | up hEq =>
          cases hEq
          exact MEqRedChain.refl
  | tail hChain hStep ih =>
      intro result body' hEq
      cases hEq with
      | up hEq =>
          subst hEq
          cases hChain.abs_inv_type with
          | inl hTop =>
              cases hTop with
              | up hTop =>
                  subst hTop
                  have hTargetTop : Term.abs result body' = Term.top :=
                    hStep.top_inv
                  cases hTargetTop
          | inr hAbs =>
              obtain ⟨midBound, midBody, hMid⟩ := hAbs
              cases hMid with
              | up hMid =>
                  subst hMid
                  exact MEqRedChain.trans (ih ⟨rfl⟩) hStep.abs_bound_chain

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

/-- Compose the changing-bound `Ms-Fun` step with a body subtype chain that
already lives under the changed bound. This isolates the endpoint composition
needed by the general `.sub` replacement abstraction case. -/
theorem MSubRedStar.fun_bound_then_body {Γ : Ctx}
    {t t' body body' : Term}
    (ht : Term.Scoped Γ.depth t)
    (hEq : MEqRed Γ [] t t')
    (hBodyScoped : Term.Scoped (Γ.depth + 1) body)
    (hBody : MSubRedStar ({ bound := t', kind := .sub } :: Γ) [] body body') :
    MSubRedStar Γ [] (.abs t body) (.abs t' body') := by
  have hpvΓ : Prevalid Γ := hEq.prevalid
  have ht' : Term.Scoped Γ.depth t' := hEq.scoped_right
  have hpvOldBodyCtx : Prevalid ({ bound := t, kind := .sub } :: Γ) :=
    Prevalid.sub hpvΓ ht
  have hBodyRefl : MSubRed ({ bound := t, kind := .sub } :: Γ) [] body body :=
    MSubRed.refl (PrevalidExt.nil hpvOldBodyCtx) (by
      simpa [Ctx.depth] using hBodyScoped)
  have hFirst : MSubRedStar Γ [] (.abs t body) (.abs t' body) :=
    MSubRedStar.single (MSubRed.fun_ ht hEq hBodyRefl)
  have hEqRefl : MEqRed Γ [] t' t' :=
    MEqRed.refl (PrevalidExt.nil hpvΓ) ht'
  have hTail : MSubRedStar Γ [] (.abs t' body) (.abs t' body') :=
    MSubRedStar.fun_body_fixed ht' hEqRefl hBody
  exact MSubRedStar.trans hFirst hTail

/-- Star-valued fixed-bound `Ms-Fun` replacement from an already-replaced body
subtype chain. -/
theorem MSubRedStar.fun_replaceAt_sub_from_body_fixed_bound {Γ : Ctx}
    {cutoff : Nat} {old new t body body' : Term}
    (ht : Term.Scoped (Ctx.depth (Ctx.replaceAt cutoff { bound := old, kind := .sub } Γ)) t)
    (hEqT : MEqRed (Ctx.replaceAt cutoff { bound := new, kind := .sub } Γ) [] t t)
    (hBody : MSubRedStar ({ bound := t, kind := .sub } ::
        Ctx.replaceAt cutoff { bound := new, kind := .sub } Γ) [] body body') :
    MSubRedStar (Ctx.replaceAt cutoff { bound := new, kind := .sub } Γ) []
      (.abs t body) (.abs t body') :=
  MSubRedStar.fun_body_fixed (by simpa [Ctx.depth_replaceAt] using ht)
    hEqT hBody

/-- Binder-recursive fixed-bound `Ms-Fun` chain replacement wrapper. -/
theorem MSubRedStar.fun_replaceAt_sub_from_body_fixed_bound_replaceAt {Γ : Ctx}
    {cutoff : Nat} {old new t body body' : Term}
    (ht : Term.Scoped (Ctx.depth (Ctx.replaceAt cutoff { bound := old, kind := .sub } Γ)) t)
    (hEqT : MEqRed (Ctx.replaceAt cutoff { bound := new, kind := .sub } Γ) [] t t)
    (hBody : MSubRedStar
        (Ctx.replaceAt (cutoff + 1) { bound := new, kind := .sub }
          ({ bound := t, kind := .sub } :: Γ)) [] body body') :
    MSubRedStar (Ctx.replaceAt cutoff { bound := new, kind := .sub } Γ) []
      (.abs t body) (.abs t body') :=
  MSubRedStar.fun_replaceAt_sub_from_body_fixed_bound
    (Γ := Γ) (cutoff := cutoff) (old := old) (new := new)
    (t := t) (body := body) (body' := body')
    ht hEqT (by simpa [Ctx.replaceAt] using hBody)

/-- Star-valued changing-bound `Ms-Fun` replacement once the body subtype chain
has already been transported under the changed bound. -/
theorem MSubRedStar.fun_replaceAt_sub_from_body_changed_bound {Γ : Ctx}
    {cutoff : Nat} {old new t t' body body' : Term}
    (ht : Term.Scoped (Ctx.depth (Ctx.replaceAt cutoff { bound := old, kind := .sub } Γ)) t)
    (hEq : MEqRed (Ctx.replaceAt cutoff { bound := new, kind := .sub } Γ) [] t t')
    (hBodyScoped : Term.Scoped
      (Ctx.depth (Ctx.replaceAt cutoff { bound := new, kind := .sub } Γ) + 1) body)
    (hBody : MSubRedStar ({ bound := t', kind := .sub } ::
        Ctx.replaceAt cutoff { bound := new, kind := .sub } Γ) [] body body') :
    MSubRedStar (Ctx.replaceAt cutoff { bound := new, kind := .sub } Γ) []
      (.abs t body) (.abs t' body') :=
  MSubRedStar.fun_bound_then_body (by simpa [Ctx.depth_replaceAt] using ht)
    hEq hBodyScoped hBody

/-- Binder-recursive changing-bound `Ms-Fun` chain replacement wrapper, once
the recursive body chain already lives under the changed abstraction bound. -/
theorem MSubRedStar.fun_replaceAt_sub_from_body_changed_bound_replaceAt {Γ : Ctx}
    {cutoff : Nat} {old new t t' body body' : Term}
    (ht : Term.Scoped (Ctx.depth (Ctx.replaceAt cutoff { bound := old, kind := .sub } Γ)) t)
    (hEq : MEqRed (Ctx.replaceAt cutoff { bound := new, kind := .sub } Γ) [] t t')
    (hBodyScoped : Term.Scoped
      (Ctx.depth (Ctx.replaceAt cutoff { bound := new, kind := .sub } Γ) + 1) body)
    (hBody : MSubRedStar
        (Ctx.replaceAt (cutoff + 1) { bound := new, kind := .sub }
          ({ bound := t', kind := .sub } :: Γ)) [] body body') :
    MSubRedStar (Ctx.replaceAt cutoff { bound := new, kind := .sub } Γ) []
      (.abs t body) (.abs t' body') :=
  MSubRedStar.fun_replaceAt_sub_from_body_changed_bound
    (Γ := Γ) (cutoff := cutoff) (old := old) (new := new)
    (t := t) (t' := t') (body := body) (body' := body')
    ht hEq hBodyScoped (by simpa [Ctx.replaceAt] using hBody)

/-- Star-valued changing-bound `Ms-Fun` under one preserved head once the body
chain already lives under the changed bound. -/
theorem MSubRedStar.fun_sub_under_head_replace_from_body_changed_bound {Γ : Ctx}
    {head : CtxEntry} {old new t t' body body' : Term}
    (ht : Term.Scoped (Ctx.depth (head :: { bound := old, kind := .sub } :: Γ)) t)
    (hEq : MEqRed (head :: { bound := new, kind := .sub } :: Γ) [] t t')
    (hBodyScoped : Term.Scoped
      (Ctx.depth (head :: { bound := new, kind := .sub } :: Γ) + 1) body)
    (hBody : MSubRedStar ({ bound := t', kind := .sub } :: head ::
        { bound := new, kind := .sub } :: Γ) [] body body') :
    MSubRedStar (head :: { bound := new, kind := .sub } :: Γ) []
      (.abs t body) (.abs t' body') :=
  MSubRedStar.fun_bound_then_body (by simpa [Ctx.depth] using ht)
    hEq hBodyScoped hBody


end DeBruijn
end Pss
