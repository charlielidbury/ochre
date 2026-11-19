import Ochr.Meaning.WF

/-!
# A partly moved constructor value was a member of no type (built)

docs/31 D24 (third lead, 2026-11-19). Membership of a possibly partly moved value, `pmem`, as
first stated: `s = moved ∨ ∃ t whole, s ⊑ t ∧ t ∈ T`, with `⊑` the order `Sem.le` (`moved` below
everything, a tuple below a tuple field by field, anything else only below itself).

A constructor value with a moved field means an untyped TUPLE (`ctorM_partly`), and a whole
constructor value is never a tuple: it is an element of its carrier. So nothing whole and typed
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

/-- **`pmem` as first stated is false of every tuple**, at every type. -/
theorem old_pmem_false (ty : String) (c : Nat) (fs : List Sem) (T : TyM) :
    ¬ (Sem.ctor ty c fs = .moved ∨ ∃ t : Sem, t.whole ∧ Sem.ctor ty c fs ⊑ t ∧ t ∈ₛ T) := by
  rintro (h | ⟨t, -, hle, hm⟩)
  · cases h
  · cases hle with
    | refl => cases T <;> exact hm
    | ctor _ => cases T <;> exact hm

/-- A constructor value some field of which is not whole means a tuple. -/
theorem ctorM_partly (dm : DataModel) (d : IndDecl) (ps : List Sem) (c : Nat) (fs : List Sem)
    (h : ¬ ∀ f ∈ fs, f.whole) : dm.ctorM d ps c fs = .ctor d.name c fs := by
  unfold DataModel.ctorM
  rw [if_neg h]

/-- `moved` is not whole: a constructor value with a moved field is such a tuple. -/
theorem moved_not_whole : ¬ Sem.moved.whole := by simp [Sem.whole]

/-- **The positive form.** A packed element of a data type with some of its fields moved out is a
partly moved member of the type. -/
theorem pmem_partly (dm : DataModel) (Γ : List IndDecl) (d : IndDecl) (ps : List Sem) (x : dm.car d ps)
    (hd : d ∈ Γ) (hs : (d.sort == 0) = false) (fs : List Sem) (hfs : dm.MovedOfList Γ fs (dm.fields x)) :
    dm.pmem Γ (.ctor d.name (dm.tag x) fs) (dm.tyM d ps) := by
  refine .inr ⟨.el0 (dm.car d ps) x, by simp [Sem.whole], .ctor x hd rfl hfs, ?_⟩
  unfold DataModel.tyM
  rw [hs]
  exact rfl

end Ochr.Meaning.Regress.PartlyMoved
