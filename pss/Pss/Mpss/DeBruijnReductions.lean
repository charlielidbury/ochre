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
