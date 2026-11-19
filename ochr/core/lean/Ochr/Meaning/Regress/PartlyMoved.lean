import Ochr.Meaning.WF

/-!
# A partly moved constructor value was a member of no type (built)

docs/31 D24 (third lead, 2026-11-19). Membership of a possibly partly moved value, `pmem`, as
first stated: `s = moved ∨ ∃ t whole, s ⊑ t ∧ t ∈ T`, with `⊑` the order `Sem.le` (`moved` below
everything, a tuple below a tuple field by field, anything else only below itself).

A constructor value with a moved field means an untyped TUPLE (`ctorM_partly`; since D32 a `dat`
with no element), and a whole constructor value is never one: it has an element of its carrier. So nothing whole and typed
lies above a partly moved tuple in `Sem.le`, and `pmem` was false of every one
(`old_pmem_false`), whatever the type.

A match that moves a field out leaves its scrutinee partly moved: `match xs { Cons(h, t) => t }`
leaves `xs = Cons(h, ⊥)`. So `Membership`, and with it `Good`, failed at the state after every
such read, and every step statement, which assumes `Good` and concludes it, was false or vacuous
there. A fault of the model's definition, not of the checker.

Fixed: `DataModel.pmem` reads "some whole member of the type with parts moved out"
(`DataModel.MovedOf`: a tuple lies below a packed element of its carrier whose tag is its own and
whose fields lie above its fields). `pmem_partly` is the positive form: a packed element with any
of its fields moved out is a partly moved member of its type.
-/

namespace Ochr.Meaning.Regress.PartlyMoved
open Ochr Ochr.Meaning

/-- **`pmem` as first stated is false of every partly moved value**, at every type (since D32 a
partly moved value is a `dat` with no element, below only such values, and those are in no type). -/
theorem old_pmem_false (n : String) (ps : List Sem) (c : Nat) (fs : List Sem) (T : TyM) :
    ¬ (Sem.dat n ps c fs none = .moved ∨ ∃ t : Sem, t.whole ∧ Sem.dat n ps c fs none ⊑ t ∧ t ∈ₛ T) := by
  rintro (h | ⟨t, -, hle, hm⟩)
  · cases h
  · cases hle with
    | refl => cases T <;> exact hm
    | dat _ => cases T <;> exact hm

/-- A constructor value some field of which is not whole has no element. -/
theorem ctorM_partly (dm : DataModel) (d : IndDecl) (ps : List Sem) (c : Nat) (fs : List Sem)
    (h : ¬ ∀ f ∈ fs, f.whole) : dm.ctorM d ps c fs = .dat d.name ps c fs none := by
  unfold DataModel.ctorM
  rw [if_neg h]

/-- `moved` is not whole: a constructor value with a moved field is such a value. -/
theorem moved_not_whole : ¬ Sem.moved.whole := by simp [Sem.whole]

/-- **The positive form.** A whole member of a data type with some of its fields moved out is a
partly moved member of the type. -/
theorem pmem_partly (dm : DataModel) (Γ : List IndDecl) (d : IndDecl) (ps : List Sem) (x : dm.car d ps)
    (hs : (d.sort == 0) = false) (hw : ∀ f ∈ dm.fields x, f.whole) (fs : List Sem)
    (hfs : DataModel.MovedOfList Γ fs (dm.fields x)) :
    DataModel.pmem Γ (.dat d.name ps (dm.tag x) fs none) (dm.tyM d ps) := by
  refine .inr ⟨.dat d.name ps (dm.tag x) (dm.fields x) (some ⟨dm.car d ps, x⟩), by simpa [Sem.whole] using hw, .dat hfs, .inl ?_⟩
  unfold DataModel.tyM
  rw [hs]
  exact ⟨rfl, rfl, rfl, rfl⟩

end Ochr.Meaning.Regress.PartlyMoved
