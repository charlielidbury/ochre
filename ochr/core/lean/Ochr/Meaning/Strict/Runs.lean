import Ochr.Meaning.Strict.Fund
import Ochr.Meaning.DataModel.CtorMem
import Ochr.Meaning.BotWrite

/-!
# The motivating runs, on the strict run (kernel-checked)

1. `(0 : Unit)` has NO successful strict run, whatever the decisions say of it (`zero_unit_none`),
   and neither has the untyped `let x = (0 : Unit); x` (`let_zero_unit_none`). The reference as it
   stands runs the first to `0` typed `Unit` (`Regress/OpenFalse.run_ascribe_trusted` on spine-lead).
2. Honest programs run, and their results are members of their types:
   - `(S(Z) : Nat)` runs to `1` at `Nat` (`succ_nat_runs`);
   - `refl` (`True`'s constructor `I`), classed a proof, runs on its copy to `⋆` at `True`'s meaning,
     and `⋆` is a member: the proposition is true (`refl_runs`);
   - `(refl : Eq(Nat, Z, Z))`, classed a proof, runs to `⋆` at `0 = 0` (`refl_eq_runs`), and
     `(refl : Eq(Nat, Z, S(Z)))` has no successful run (`refl_neq_none`): the strict run of a proof
     term certifies its proposition.
-/

namespace Ochr.Meaning.Strict
open Ochr Ochr.Meaning

/-- `True`, declared as in the library: a proposition with one constructor and no field. -/
def trueD : IndDecl := { name := "True", sort := 0, ctors := [("I", [])] }

/-- The decisions: a constructor and an ascription are proofs (erased; C1 runs them on a copy),
nothing else is a statement or a proof. Otherwise `Attack.D₀`'s. -/
def Dpf : Decisions where
  flags _ t := match t with
    | .ctor .. | .ascribe .. => (false, true)
    | _ => (false, false)
  placeDecl _ _ := .other
  declOf _ _ := .other
  copy _ := false
  piSort _ _ := 1
  joinMoves _ _ _ := []
  rePointed _ _ := []
  typeDecl _ _ := .other

/-- A run context with `True` declared, at any data model. -/
def Kt (dm : DataModel) (D : Decisions) : RunCtx where
  dm := dm
  Γ := [trueD]
  C := { global := fun _ => (.err, .plain TyM.err), sealed := fun _ _ _ _ => .err, clo := fun _ _ _ _ _ => .err,
         pi := fun _ _ _ _ _ => TyM.err, paramTy := fun _ _ _ _ => .plain TyM.err }
  D := D

variable (K : RunCtx) (ρ : Assignment) (φ : Future)

theorem unit_ne_nat' : (Unit : Type) ≠ Nat := by
  intro h
  have : ∀ a b : Nat, a = b := fun a b => by
    have := Subsingleton.elim (cast h.symm a) (cast h.symm b)
    simpa using congrArg (cast h) this
  exact absurd (this 0 1) (by decide)

@[simp] theorem labTyOk_none (s : SState) (T : TyM) : labTyOk s none T := fun _ h => by cases h

theorem nat_not_unit (n : Nat) (R : DataRead) : ¬ (Sem.el0 Nat n ∈ₛ[R] TyM.unit) := by
  rintro ⟨a, ha⟩
  exact unit_ne_nat' (Sem.el0.inj ha).1

/-- **`(0 : Unit)` has no successful strict run**, whatever the decisions say of it: the strict
ascription fails (a statement or a proof runs the same clause, on a copy). -/
theorem zero_unit_none (tl : Bool) (h : TyS) (s : SState) :
    runS K ρ φ tl h (.ascribe (.val .zero) (.val .tUnit)) s = none := by
  have hn := nat_not_unit 0 K.dm.read
  rw [runS]
  show SM.erasedS (K.D.flags (scopeOf s) _) _ s = none
  generalize K.D.flags (scopeOf s) (.ascribe (.val .zero) (.val .tUnit)) = fl
  obtain ⟨b1, b2⟩ := fl
  cases b2 <;> cases b1 <;>
    simp [SM.erasedS, SM.stmtIf, SM.strictS, runS, SM.onCopy, bind, pure, meanS, Sem.asTy, strictVal, TyS.plain, hn]

/-- **The untyped `let x = (0 : Unit); x` has no successful strict run**: its binding's run fails. -/
theorem let_zero_unit_none (tl : Bool) (h : TyS) (x : Hint) (s : SState) :
    runS K ρ φ tl h (.letIn x (.ascribe (.val .zero) (.val .tUnit)) (.place (.var 0))) s = none := by
  rw [runS]
  show SM.erasedS (K.D.flags (scopeOf s) _) _ s = none
  generalize K.D.flags (scopeOf s) _ = fl
  obtain ⟨b1, b2⟩ := fl
  cases b2 <;> cases b1 <;> simp [SM.erasedS, SM.stmtIf, bind, zero_unit_none]

theorem one_mem_nat (R : DataRead) : Sem.el0 Nat 1 ∈ₛ[R] TyM.nat := ⟨1, rfl⟩

/-- **`(S(Z) : Nat)` runs to `1` at `Nat`**, a member (decisions that class nothing a statement or a
proof). -/
theorem succ_nat_runs (hfl : ∀ sc t, K.D.flags sc t = (false, false)) (tl : Bool) (h : TyS) (s : SState) :
    runS K ρ φ tl h (.ascribe (.succ .zero) .nat) s = some ((.el0 Nat 1, .plain TyM.nat), s) ∧
      Sem.el0 Nat 1 ∈ₛ[K.dm.read] TyM.nat := by
  refine ⟨?_, one_mem_nat _⟩
  have hm : Sem.el0 Nat 1 ∈ₛ[K.dm.read] TyM.nat := one_mem_nat K.dm.read
  simp [runS, hfl, SM.erasedS, SM.stmtIf, SM.strictS, SM.onCopy, bind, pure, Sem.succ_el0, Sem.asTy, hm, TyS.plain]
/-- **`Type₁` as a term runs, to a value that is no (partly moved) member of the type the run gives
it**: `sort 2 : sort 3`, and the bounded model has no `Type₂` (`TyM.univ 3 = err`). The term occurs in
accepted programs (a codomain `Type_1`, `Regress/CodeRuns`' `Pred`), so the fundamental lemma's
conclusion is "a partly moved member, OR the type is `err`" (`GoodRes`), not `pmem` alone; the same
holds of the run as it stands (`runT`). -/
theorem sort_two_runs (tl : Bool) (h : TyS) (s : SState) :
    runS K ρ φ tl h (.sort 2) s = some ((.ty (TyM.univ 2), .plain (TyM.univ 3)), s) ∧
      ¬ DataModel.pmem K.dm.read K.Γ (.ty (TyM.univ 2)) (TyM.univ 3) ∧ TyM.univ 3 = TyM.err := by
  refine ⟨by rw [runS]; rfl, ?_, rfl⟩
  rintro (h | ⟨t, _, hm, ht | ho⟩)
  · cases h
  · exact DataModel.err_mem_false _ _ ht
  · cases hm <;> exact ho

section
variable (dm : DataModel)

/-- `True`'s record, as the constructor clause computes it (no parameters). -/
abbrev trueR : Rec := dm.recOf trueD []

/-- **`refl` is true in the model**: `⋆` is a member of `True`'s meaning (its constructor `I` with no
field: `CtorMem.proof_mem_tyR`). -/
theorem proof_mem_trueD (hok : dm.RecLeafOk trueD (trueR dm)) : Sem.proof ∈ₛ[dm.read] dm.tyR trueD (trueR dm) :=
  dm.proof_mem_tyR trueD _ 0 [] rfl (by decide) rfl (fun _ _ h => by simp at h) hok

theorem tyR_true_level : (dm.tyR trueD (trueR dm)).level = some 0 := by
  simp [DataModel.tyR, trueD, TyM.prop, TyM.level, Code0.level]

/-- **`refl`, classed a proof, runs**: its constructor clause runs on a copy to `⋆` at `True`'s meaning,
of which `⋆` is a member (the strict test, `proof_mem_trueD`), and the erased term is `⋆` at
`prop True` (C1, decision 1). -/
theorem refl_runs (hok : dm.RecLeafOk trueD (trueR dm)) (tl : Bool) (h : TyS) (x : Hint) (s : SState) :
    runS (Kt dm Dpf) ρ φ tl h (.ctor "True" 0 x [] []) s = some ((.proof, .plain (TyM.prop True)), s) ∧
      Sem.proof ∈ₛ[dm.read] dm.tyR trueD (trueR dm) := by
  refine ⟨?_, proof_mem_trueD dm hok⟩
  have hm : Sem.proof ∈ₛ[dm.read] (TyS.plain (dm.tyR trueD (trueR dm))).m := proof_mem_trueD dm hok
  have hfind : [trueD].find? (·.name == "True") = some trueD := rfl
  have hsort : (trueD.sort == 0) = true := rfl
  have hpar : trueD.params.isEmpty = true := rfl
  simp [runS, Kt, Dpf, SM.erasedS, SM.strictS, runParamsS, runFieldsS, ctorOut, bind, pure, hfind, hsort,
    hpar, hm, Sem.isProof]

theorem proof_mem_prop {R : DataRead} {P : Prop} (hP : P) : Sem.proof ∈ₛ[R] TyM.prop P := ⟨⟨hP⟩, rfl⟩

theorem proof_not_mem_false {R : DataRead} : ¬ (Sem.proof ∈ₛ[R] TyM.prop False) := fun ⟨⟨h⟩, _⟩ => h

/-- **`(refl : Eq(Nat, Z, Z))`, classed a proof, runs** to `⋆` at the meaning of `Eq(Nat, Z, Z)`,
which it is a member of. -/
theorem refl_eq_runs (hok : dm.RecLeafOk trueD (trueR dm)) (tl : Bool) (h : TyS) (x : Hint) (s : SState) :
    runS (Kt dm Dpf) ρ φ tl h (.ascribe (.ctor "True" 0 x [] []) (.eq .nat .zero .zero)) s =
      some ((.proof, .plain (TyM.prop True)), s) := by
  have hr : ∀ h s, runS (Kt dm Dpf) ρ φ false h (.ctor "True" 0 x [] []) s =
      some ((.proof, .plain (TyM.prop True)), s) := fun h s => (refl_runs ρ φ dm hok false h x s).1
  have he : ∀ h s, runS (Kt dm Dpf) ρ φ false h (.eq .nat .zero .zero) s =
      some ((.ty (TyM.prop True), .plain (TyM.univ 0)), s) := by
    intro h s; simp [runS, SM.onCopy, bind, pure]
  have hm : Sem.proof ∈ₛ[(Kt dm Dpf).dm.read] TyM.prop True := proof_mem_prop trivial
  have hfl : ∀ sc, (Kt dm Dpf).D.flags sc (.ascribe (.ctor "True" 0 x [] []) (.eq .nat .zero .zero)) = (false, true) :=
    fun _ => rfl
  have hdm : (Kt dm Dpf).dm = dm := rfl
  rw [runS]
  simp [hfl, SM.erasedS, SM.strictS, SM.onCopy, bind, pure, hr, he, Sem.asTy, hm, Sem.isProof, TyS.plain]

/-- **`(refl : Eq(Nat, Z, S(Z)))` has no successful strict run**: the ascription's test is the
proposition `0 = 1`. -/
theorem refl_neq_none (hok : dm.RecLeafOk trueD (trueR dm)) (tl : Bool) (h : TyS) (x : Hint) (s : SState) :
    runS (Kt dm Dpf) ρ φ tl h (.ascribe (.ctor "True" 0 x [] []) (.eq .nat .zero (.succ .zero))) s = none := by
  have hr : ∀ h s, runS (Kt dm Dpf) ρ φ false h (.ctor "True" 0 x [] []) s =
      some ((.proof, .plain (TyM.prop True)), s) := fun h s => (refl_runs ρ φ dm hok false h x s).1
  have h1 : Sem.el0 Nat 1 ∈ₛ[dm.read] (TyS.plain TyM.nat).m := one_mem_nat _
  have he : ∀ h s, runS (Kt dm Dpf) ρ φ false h (.eq .nat .zero (.succ .zero)) s =
      some ((.ty (TyM.prop False), .plain (TyM.univ 0)), s) := by
    intro h s; simp [runS, Dpf, Kt, SM.erasedS, SM.stmtIf, SM.strictS, SM.onCopy, bind, pure, Sem.succ_el0, h1]
  have hn : ¬ Sem.proof ∈ₛ[(Kt dm Dpf).dm.read] TyM.prop False := proof_not_mem_false
  have hfl : ∀ sc, (Kt dm Dpf).D.flags sc (.ascribe (.ctor "True" 0 x [] []) (.eq .nat .zero (.succ .zero))) =
    (false, true) := fun _ => rfl
  have hdm : (Kt dm Dpf).dm = dm := rfl
  rw [runS]
  simp [hfl, SM.erasedS, SM.strictS, SM.onCopy, bind, pure, hr, he, Sem.asTy, hn, TyS.plain]

end

end Ochr.Meaning.Strict
