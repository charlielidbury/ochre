import Ochr.Meaning.WF
import Ochr.Meaning.DataModel.Old
import Ochr.Meaning.DataModel.ReadMember

/-!
# A partly moved constructor value was a member of no type (built)

docs/31 D24 (third lead, 2026-11-19). Membership of a possibly partly moved value, `pmem`, as
first stated: `s = moved ∨ ∃ t whole, s ⊑ t ∧ t ∈ T`, with `⊑` the order `Sem.le` (`moved` below
everything, a tuple below a tuple field by field, anything else only below itself).

Under D32 a constructor value with a moved field meant an untyped TUPLE (a `dat` with no packed
element), and a whole constructor value was never one: it had an element of its carrier. So
nothing whole and typed lay above a partly moved tuple in `Sem.le`, and `pmem` was false of every
one (`old_pmem_false`, against the frozen copy of that layer, `DataModel/Old.lean`), whatever the
type. A match that moves a field out leaves its scrutinee partly moved: `match xs { Cons(h, t) => t }`
leaves `xs = Cons(h, ⊥)`, so `Membership`, and with it `Good`, failed after every such read.

Fixed then by `DataModel.pmem` ("some whole member of the type with parts moved out",
`DataModel.MovedOf`). Since docs/34's port a constructor value is a tree, whole or not, so the
first statement holds too: a whole member with fields moved out lies below the member in `Sem.le`
(`first_stated_holds`), and `pmem_partly` is the positive form.
-/

namespace Ochr.Meaning.Regress.PartlyMoved

/-- **`pmem` as first stated was false of every partly moved value**, at every type, before the
port (a partly moved value was a `dat` with no element, below only such values, and those were in
no type). -/
theorem old_pmem_false (R : Old.DataRead) (n : String) (ps : List Old.Sem) (c : Nat) (fs : List Old.Sem) (T : Old.TyM) :
    ¬ (Old.Sem.dat n ps c fs none = .moved ∨
      ∃ t : Old.Sem, t.whole ∧ Old.Sem.le (Old.Sem.dat n ps c fs none) t ∧ Old.Sem.mem R t T) := by
  rintro (h | ⟨t, -, hle, hm⟩)
  · cases h
  · cases hle with
    | refl => exact Old.Sem.not_mem_dat_none R n ps c fs T hm
    | dat _ => exact Old.Sem.not_mem_dat_none R n ps c _ T hm

open Ochr Ochr.Meaning

/-- `moved` is not whole: a constructor value with a moved field is such a value. -/
theorem moved_not_whole : ¬ Sem.moved.whole := by simp [Sem.whole]

/-- **The positive form.** A whole member of a data type with some of its fields moved out is an
open member of the type (`omem_of_below`). -/
theorem pmem_partly (dm : DataModel) (Γ : List IndDecl) (d : IndDecl) (r : Rec) (c : Nat) (fs gs : List Sem)
    (hs : (d.sort == 0) = false) (hm : dm.Mem d r (.dat d.name r c gs)) (hfs : DataModel.MovedOfList Γ fs gs) :
    DataModel.pmem dm Γ (.dat d.name r c fs) (dm.tyR d r) :=
  DataModel.omem_of_below (.dat hfs) (DataLib.mem_whole dm.sig d r _ hm) ((DataModel.mem_tyR dm d r hs _).2 hm)

/-- **`pmem` as first stated now holds**: `Cons(h, ⊥)`, left by `match xs { Cons(h, t) => t }`, is
below the whole member `Cons(h, t)` it came from. -/
theorem first_stated_holds (dm : DataModel) (d : IndDecl) (r : Rec) (hs : (d.sort == 0) = false)
    (h t : Sem) (hm : dm.Mem d r (.dat d.name r 1 [h, t])) :
    ∃ w : Sem, w.whole ∧ Sem.dat d.name r 1 [h, .moved] ⊑ w ∧ w ∈ₛ[dm.read] dm.tyR d r :=
  ⟨_, DataLib.mem_whole dm.sig d r _ hm, .dat (.cons (.refl _) (.cons (.moved _) .nil)),
    (DataModel.mem_tyR dm d r hs _).2 hm⟩

end Ochr.Meaning.Regress.PartlyMoved
