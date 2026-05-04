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
