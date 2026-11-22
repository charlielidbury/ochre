import Ochr.Meaning.Consistency

/-!
# The degenerate model no longer meets the existence statement (docs/34 §2.1; kernel-checked)

Before docs/34's port, `exists_dataModel` asked of a data model only that it cover the program's
declarations and read whole fields, and a model that ignores the program met it
(`Counterexamples.degenerate_meets`, against the frozen copy of that layer). The same model in
the ported layer, `degenerate` (every declaration covered, every record empty, so every field `err`), still covers
everything (`degenerate_covers`), but it is not faithful: at a declaration with a `Nat` field, the
reference run of the declared field type `Nat` gives `Nat`, not the model's `err`
(`degenerate_not_faithful`), so no program declaring one has it as a faithful model
(`degenerate_not_dataFaithful`).
-/

namespace Ochr.Meaning.DataModel.Degenerate

open Ochr Ochr.Meaning Ochr.Meaning.Assembly

/-- Every declaration covered, every field `err`, every record empty. -/
def degenerate : DataModel where
  covers _ := True
  recOf _ _ := natRec
  paramTy _ _ _ := TyM.err

/-- It covers every declaration of every program. -/
theorem degenerate_covers (P : ProgState) : P.Covered degenerate := fun _ _ => trivial

/-- `inductive NB := MkNB(n : Nat)`. -/
def nbD : IndDecl := { name := "NB", ctors := [("MkNB", [("n", .nat)])] }

theorem nat_ne_err : TyM.nat ≠ TyM.err := by
  intro h; have := congrArg TyM.level h; simp [TyM.level, TyM.nat, TyM.err, Code0.level] at this

/-- **The degenerate model is not faithful** to any run context declaring `NB`: the field type
`Nat` runs to `Nat`, and the model reads it `err`. -/
theorem degenerate_not_faithful (K : RunCtx) (hdm : K.dm = degenerate) (hΓ : nbD ∈ K.Γ) (ρ : Assignment) :
    ¬ FieldsFaithful K ρ := by
  intro h
  have hT := h nbD hΓ [] 0 0 [] .nat rfl (fun j hj => absurd hj (by simp))
    (fun i hi => absurd hi (by simp)) rfl rfl _ _ rfl
  rw [hdm] at hT
  exact nat_ne_err hT

/-- The same at the one declaration `NB` (`FieldsFaithfulAt`, what `DeclsFaithful` asks). -/
theorem degenerate_not_faithfulAt (K : RunCtx) (hdm : K.dm = degenerate) (ρ : Assignment) :
    ¬ FieldsFaithfulAt K ρ nbD := by
  intro h
  have hT := h [] 0 0 [] .nat rfl (fun j hj => absurd hj (by simp))
    (fun i hi => absurd hi (by simp)) rfl rfl _ _ rfl
  rw [hdm] at hT
  exact nat_ne_err hT

/-- **No program declaring `NB` has the degenerate model as a faithful model**: `DataFaithful`, the
existence statement's obligation, fails at the program's own state, at every whole-program list `Γ`
(docs/31 D174). -/
theorem degenerate_not_dataFaithful (D : MState → Decisions) (Γ : List IndDecl) (P : ProgState) (hΓ : nbD ∈ P.inds) :
    ¬ DataFaithful degenerate D Γ P := by
  intro h
  have hf := h { globals := P.globals, inds := P.inds } rfl (List.prefix_refl _)
  exact degenerate_not_faithfulAt _ rfl (fun _ => .err) (hf nbD hΓ (fun _ => .plain TyM.err) (fun _ => .err)).1

end Ochr.Meaning.DataModel.Degenerate
