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

/-- `projIdx` of a list of `.other`s is itself: `paramKey 0` is the key the universal signature reads
for field `0` of constructor `0` with one earlier field, which is how `leafOk` came to read it before
(S) scoped `RecLeafOk` to genuine field keys. -/
theorem projIdx_other (d : IndDecl) (c : Nat) : projIdx d c [.other] = [.other] := by
  simp only [projIdx, List.zipIdx_cons, List.zipIdx_nil, List.map_cons, List.map_nil]
  split <;> rfl

theorem kindKey_paramKey : kindKey 0 0 [.other] = paramKey 0 := rfl

/-! The refutation itself (`recordsFaithful_false`: `RecordsFaithful K` false at every `K` with a
declaration in `Γ`; `ctxFaithful_false`; `dataFaithful_false`), against the statement as it stood,
is at 1765a998. It went through three things the rulings removed: `.ty (xTy r)` a member of
`Type₀` (now `xTy_not_mem_univ`), `ParamsTyped`'s "or any type value" disjunct (gone), and `leafOk`
reading `paramKey 0` (now `RecLeafOk` reads genuine field keys only). The restated bundle is
inhabited at the library's declarations: `PreludeModel.lean`. -/

end Ochr.Meaning.DataModel.Exists.RecordsCE

