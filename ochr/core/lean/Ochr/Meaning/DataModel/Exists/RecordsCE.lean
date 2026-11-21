import Ochr.Meaning.Consistency
import Ochr.Meaning.DataModel.Canonical.Layout

/-!
# `RecordsFaithful` has no instance at any non-empty `Γ` (kernel-checked)

So `Assembly.exists_dataModel` is false as stated wherever the checker accepts one declaration
(every accepted program: the library declares `Pair`, `False`, `True`, `And`): `DataFaithful` at a
prefix asks `CtxFaithful`, which asks `RecordsFaithful`.

The witness is a type in the model's `Type₀`: the RAW data code of a `Prop`-sorted declaration over
the model's own carrier, `X = .t0 (car E r) (.data E r (car E r))`. Its level is `1` (`Code0.level`
gives every data code `1`), so `.ty X` is a member of `Type₀` (`univ1` decodes `⟨A, c, _⟩` to
`.ty (.t0 A c)`). No shape means `X` except a leaf holding `X`'s code (a `.data E` entry gives a
`prf`, a proposition), and `LeafOk` forbids exactly that leaf. Two clauses then collide:
* `RecordsFaithful.types`, at the parameter list `[.ty X]` (`ParamsTyped` holds: a parameter may be
  any type value), forces the record's entry at `paramKey 0` to be that leaf;
* `RecordsFaithful.leafOk` reads every key of the form `[(c, i, es)]`, and `paramKey 0` is one
  (`c = 0`, `i = 0`, `es = [.other]`: the universal signature reads it as a field's kind).

The same type breaks faithfulness at a GENUINE field key, independently of how `types` and
`leafOk` are scoped: `Box (A : Type) := MkBox(x : A)` at `A := X` must read its field at `X`
(`FieldsFaithful`: the run reads the type parameter, a member of `Type₀`), which only the forbidden
leaf gives; and if the leaf is allowed, the run's `MkBox[A](x)` at `A := X` builds a tree whose
field (a tree of `E`, a member of `X` through the reading) does not fit the leaf (a leaf fits only
`el0`-tagged elements, `DataLib.encLeaf`), so the strict constructor fails where the checker
accepts. That second form is argued here, not kernel-checked.
-/

namespace Ochr.Meaning.DataModel.Exists.RecordsCE

open Ochr Ochr.Meaning Ochr.Meaning.DataLib Ochr.Meaning.Canonical

/-- A `Prop`-sorted declaration (no parameters, no constructors): any one will do. -/
def eD : IndDecl := { name := "E0", sort := 0 }

/-- **The witness type**: `eD`'s raw data code at the model's carrier, at any record. -/
noncomputable def xTy (r : Rec) : TyM := .t0 (ucar eD r) (.data eD r (ucar eD r))

/-- Since the ruling (M-a) it is a member of no universe: a `Prop`-sorted declaration's data code
has no level (`Code0.level`). Before it, `⟨⟨ucar eD r, .data eD r (ucar eD r), rfl⟩, rfl⟩` was a
proof that `.ty (xTy r)` is a member of `Type₀`. -/
theorem xTy_not_mem_univ (R : DataRead) (r : Rec) : ¬ (Sem.ty (xTy r)) ∈ₛ[R] TyM.univ 1 := by
  rintro ⟨⟨A, c, hc⟩, h⟩
  have h' : TyM.t0 A c = xTy r := Sem.ty.inj h
  unfold xTy at h'
  obtain ⟨hA, hh⟩ := TyM.t0_inj h'
  subst hA
  cases eq_of_heq hh
  simp [Code0.level, eD] at hc

/-- A proposition's code is not `xTy`. -/
theorem prop_ne_xTy (P : Prop) (r : Rec) : TyM.prop P ≠ xTy r := by
  intro h
  unfold TyM.prop xTy at h
  obtain ⟨hA, hh⟩ := TyM.t0_inj h
  revert hh
  generalize ucar eD r = B at *
  subst hA
  intro hh
  cases eq_of_heq hh

/-- The error type is not `xTy`. -/
theorem err_ne_xTy (r : Rec) : TyM.err ≠ xTy r := by
  intro h
  unfold TyM.err xTy at h
  obtain ⟨hA, hh⟩ := TyM.t0_inj h
  revert hh
  generalize ucar eD r = B at *
  subst hA
  intro hh
  cases eq_of_heq hh

/-- No data type's code is `xTy` (a data-sorted declaration's code names another declaration). -/
theorem tyR_ne_xTy (dm : DataModel) (d : IndDecl) (r' r : Rec) : dm.tyR d r' ≠ xTy r := by
  intro h
  unfold DataModel.tyR at h
  split at h
  · exact prop_ne_xTy _ r h
  · rename_i hs
    unfold xTy at h
    obtain ⟨hA, hh⟩ := TyM.t0_inj h
    obtain ⟨rfl, -⟩ := data_heq_inj hA hh
    exact hs (by decide)

/-- `projIdx` of a list of `.other`s is itself. -/
theorem projIdx_other (d : IndDecl) (c : Nat) : projIdx d c [.other] = [.other] := by
  simp only [projIdx, List.zipIdx_cons, List.zipIdx_nil, List.map_cons, List.map_nil]
  split <;> rfl

/-- **`RecordsFaithful` has no instance once `Γ` holds a declaration.** -/
theorem recordsFaithful_false (K : RunCtx) (d : IndDecl) (hd : d ∈ K.Γ) : ¬ RecordsFaithful K := by
  intro h
  let ps : List Sem := [.ty (xTy dummyRec)]
  have hpt : ParamsTyped K.dm d ps := fun j hj => .inr ⟨xTy dummyRec, by
    cases j with
    | zero => rfl
    | succ j => simp [ps] at hj⟩
  have ht := h.types d hd ps 0 _ _ hpt rfl
  have hl := h.leafOk d hd ps hpt 0 0 [.other]
  generalize hr : K.dm.recOf d ps = r at ht hl
  have hsh : K.dm.sig.shape d r 0 0 [.other] = uShape d r 0 0 [.other] := rfl
  rw [hsh] at hl
  unfold uShape at hl
  rw [projIdx_other] at hl
  have hk : kindKey 0 0 [.other] = paramKey 0 := rfl
  rw [hk] at hl
  unfold DataModel.paramTyOf at ht
  revert ht hl
  cases r (paramKey 0) with
  | none => intro ht; exact absurd ht (err_ne_xTy _)
  | small s => intro ht; exact absurd ht (err_ne_xTy _)
  | data d' => intro ht; exact absurd ht (tyR_ne_xTy _ _ _ _)
  | leaf B c =>
    intro ht hl
    obtain ⟨hA, hh⟩ := TyM.t0_inj ht
    subst hA
    cases eq_of_heq hh
    exact hl eD dummyRec rfl rfl

/-- Hence no data model is faithful to a non-empty `Γ`. -/
theorem ctxFaithful_false (K : RunCtx) (d : IndDecl) (hd : d ∈ K.Γ) : ¬ CtxFaithful K :=
  fun h => recordsFaithful_false K d hd (h (fun _ => .plain TyM.err) (fun _ => .err)).2.2

/-- And `DataFaithful` holds of a program state only if it declares nothing: the existence
statement's conclusion fails at every prefix holding a declaration. -/
theorem dataFaithful_false (dm : DataModel) (D : MState → Decisions) (P : ProgState) (d : IndDecl)
    (hd : d ∈ P.inds) : ¬ Assembly.DataFaithful dm D P := by
  intro h
  exact ctxFaithful_false _ d hd (h { globals := P.globals, inds := P.inds } rfl (List.prefix_refl _))

end Ochr.Meaning.DataModel.Exists.RecordsCE

