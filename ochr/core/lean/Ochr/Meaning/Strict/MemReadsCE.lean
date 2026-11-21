import Ochr.Meaning.Strict.Ops

/-!
# `MemReads` as stated holds in no data model (a finding, 2026-11-21)

`MemReads dm Γ` (`Strict/Ops.lean`, the context's `FundCtx.reads`) asks of EVERY type `T`: a whole
value a read path reaches in a member of `T` is a member of the type the read gives it. A read
types a field by the declaration it finds BY NAME in `Γ` (`contentTyS`); a data code of the model
for a declaration that `Γ` does not declare is still a type with members (the signature is
universal, `DataLib/Universal.lean`), and the read types its fields `err`. So for any `Γ` that
declares nothing named `Fresh`, the declaration `Fresh` with one `Nat` field at the record `rF`
(field `0` a `Nat` leaf) has the member `Fresh.C(5)`, whose field reads `5` at `err`: no member of
`err`, and data. `FundCtx K` is then uninhabited and `fund_all` holds vacuously.
-/

namespace Ochr.Meaning.Strict.MemReadsCE

open Ochr Ochr.Meaning

/-- A declaration the program does not declare: one constructor with one field. -/
def dF : IndDecl := { name := "Fresh", ctors := [("C", [("x", .nat)])] }

/-- A record giving that field the leaf `Nat`. -/
def rF : Rec
  | [(0, 0, [])] => .leaf Nat .nat
  | _ => .none

/-- The field, by name. -/
def g : FieldRef := { ty := "Fresh", ctor := 0, idx := 0, name := "x" }

/-- `Fresh.C(5)` is a member of `Fresh` at `rF`, in every data model. -/
theorem mem (dm : DataModel) : Sem.dat "Fresh" rF 0 [.el0 Nat 5] ∈ₛ[dm.read] dm.tyR dF rF := by
  refine (dm.mem_tyR dF rF rfl _).2 ((DataLib.mem_iff dm.sig dF rF _).2
    ⟨⟨0, by decide⟩, [.el0 Nat 5], rfl, ?_⟩)
  show ∃ f fs', [Sem.el0 Nat 5] = f :: fs' ∧ _ ∧ _
  refine ⟨.el0 Nat 5, [], rfl, ?_, rfl⟩
  show ∃ b, DataLib.encLeaf Code0.nat b = Sem.el0 Nat 5
  exact ⟨5, rfl⟩

/-- **`MemReads` is false** for every data model and every `Γ` declaring nothing named `Fresh`. -/
theorem not_memReads (dm : DataModel) (Γ : List IndDecl) (hΓ : ∀ d ∈ Γ, d.name ≠ "Fresh") :
    ¬ MemReads dm Γ := by
  intro h
  have hf : Γ.find? (·.name == "Fresh") = none := by
    rw [List.find?_eq_none]; intro d hd; simpa using hΓ d hd
  have hfol : Sem.follow dm Γ (.plain (dm.tyR dF rF)) (.dat "Fresh" rF 0 [.el0 Nat 5]) [.field g]
      = some (.el0 Nat 5, .plain TyM.err) := by
    simp [Sem.follow, Sem.step, Sem.stepField, g, contentTyS, hf]
  rcases h (.plain (dm.tyR dF rF)) _ _ (mem dm) (.refl _) [.field g] _ _ hfol (by simp [Sem.whole]) with
    ⟨a, _⟩ | ⟨-, ⟨T, hT⟩ | hT⟩
  · exact a.elim
  · cases hT
  · cases hT

end Ochr.Meaning.Strict.MemReadsCE
