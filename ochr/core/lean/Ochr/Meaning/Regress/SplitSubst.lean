import Ochr.Meaning.Steps.Statements
import Ochr.Meaning.Regress.CodeRuns
import Ochr.Meaning.SubstAbs
import Ochr.Meaning.RunSubstAbs
import Ochr.Examples.Nat

/-!
# Replacing an unknown by its refinement, on concrete runs (docs/31 D76; area (f))

The substitution lemma for unknowns (`substEnv_abs_step_stmt`) checked on the checker's own states
(recorded at holes, before and inside the world of a split) and on the reference's meanings
(kernel-checked), before anything is assembled around it.

**(1) A stuck program re-run after the refinement.** `A1B`: `r` holds `⌈Pred2(σ0)⌉`. In the world
`σ0 := S(σ1)` (`A1S`) the re-run computes: `r` holds `σ1`. The reference (`refine_keeps_sealed`):
under an assignment meeting the world, the sealed program before, its text substituted
`⌈Pred2(S(σ1))⌉`, and `σ1` all mean the same. A program holding a hole stays sealed with its text
substituted (D97; `B1S`: the fills of `a` and `b` hold `loan_2` and read `PickP(S(σ3), …)`), while
the returned borrow's loan-free program re-runs to `σ2`; the re-runs issue labels nothing holds
(`nextLoan` 4 before, 16 in the world). A stored type rebuilt after the refinement converts two
functions (`C1S`: `Eq(Π(n : Nat). Nat, G, Choose(b))` at `b := S(σ3)` is `⊤`), which keeps an unknown:
the table grows by two in the world, the arm's field and the conversion's (`C1B` 3, `C1S` 5).

**(2) A refinement of an unknown that a record or a stored type mentions.** The generalisation
record `⌈Pred2(σ0)⌉ := σ1` (`E2B`) is NOT rewritten when `σ0` is refined later (`E2`): its program
still names `σ0`, and still holds, since it means the same refined (`refine_keeps_sealed`). Stored
types are rewritten (`D2S`: `y : Box(S(σ2))`, `r : &Box(S(σ2))`), and mean the same
(`refine_keeps_type`); the reference's record of the borrow's content type, a meaning taken when
the borrow was made, agrees with them.

**(3) A refinement under one world, then the join.** After the match (`W3`, closed off as a block)
no refinement, record or path condition of either arm remains (`refs`, `etaRefs`, `neutrals`
empty); the arm `S m`'s fresh unknown keeps its type and nothing names it; `n` is moved into the
block, whose program means the run of the match at the assignment (`closeBlock_step`). Not
kernel-checked here: the reference's run of the match selecting the arm.
-/

open Ochr.Test

#guard_msgs (drop warning) in
ochr SplitSubst uses Nats {
  inductive Box (k : Nat) := MkB(x : Nat)
  def F (n : Nat) : Nat := n
  def G (m : Nat) : Nat := m
  def Choose (b : Nat) : (Π(n : Nat). Nat) := match b { Z => G, S k => F }
  def Pred2 (n : Nat) : Nat := match n { Z => S(S(Z)), S m => m }
  def PickP (n : Nat) (x : &(Nat × Nat)) (y : &(Nat × Nat)) : &(Nat × Nat) := (match n { Z => x, S _ => y })
  def A1B (n : Nat) : Nat := (let r = Pred2(clone(n)); ?)
  def A1S (n : Nat) : Nat := (let r = Pred2(clone(n)); match n { Z => r, S m => ? })
  def B1B (n : Nat) (a : Nat × Nat) (b : Nat × Nat) : Nat := (let r = PickP(clone(n), &a, &b); ?)
  def B1S (n : Nat) (a : Nat × Nat) (b : Nat × Nat) : Nat := (let r = PickP(clone(n), &a, &b); match n { Z => Z, S m => ? })
  def C1B (b : Nat) (h : Eq(Π(n : Nat). Nat, G, Choose(b))) : Nat := ?
  def C1S (b : Nat) (h : Eq(Π(n : Nat). Nat, G, Choose(b))) : Nat := match b { Z => Z, S k => ? }
  def E2B (n : Nat) : Nat := (let r = Pred2(clone(n)); match r { Z => Z, S k => ? })
  def E2 (n : Nat) : Nat := (let r = Pred2(clone(n)); match r { Z => Z, S k => match n { Z => Z, S m => ? } })
  def D2S (n : Nat) (y : Box(n)) : Nat := (let r = &y; match n { Z => Z, S m => ? })
  def W3 (n : Nat) : Nat := (let r : Nat = (match n { Z => Z, S m => m }); ?)
}

namespace Ochr.Meaning.Regress.SplitSubst
open Ochr Ochr.Meaning

/-- The checker's state at the hole of `name` (the last located term entered: each hole is in the
last arm). -/
def stAt (name : String) : MState :=
  let r := Ochr.Test.runWith (some Prelude) "SplitSubst" SplitSubst { recordStates := true } (located := true)
  match r.rows.find? (·.name == name) with
  | some row => (row.trace.toList.filterMap fun
      | .state _ false _ st => some st | _ => none).getLast?.getD default
  | none => default

/-- The values and the stored types of the body's frame, printed. -/
def vals (n : String) : List String := ((stAt n).env.toList.getLast?.map fun fr => fr.binds.toList.map fun b => toString b.val).getD []
def tys (n : String) : List String := ((stAt n).env.toList.getLast?.map fun fr => fr.binds.toList.map fun b => (b.ty.map toString).getD "-").getD []

-- (1) a stuck program re-run after the refinement
#guard vals "A1B" == ["A1B", "σ0", "⌈Pred2(σ0)⌉"]
#guard vals "A1S" == ["A1S", "S(σ1)", "σ1"] && toString (stAt "A1S").refs == "[(0, S(σ1))]"
#guard (vals "B1S")[2]! == "⌈let c1 = σ1; let c2 = σ2; let r = PickP(S(σ3), &c1, &c2); *r := loan_2; c1⌉"
#guard (vals "B1S")[3]! == "⌈let c1 = σ1; let c2 = σ2; let r = PickP(S(σ3), &c1, &c2); *r := loan_2; c2⌉"
#guard (vals "B1S")[4]! == "borrow_2 σ2" && (stAt "B1B").nextLoan == 4 && (stAt "B1S").nextLoan == 16
#guard (tys "C1B")[2]! == "Eq(Π(n : Nat). Nat, G, ⌈Choose(σ0)⌉)" && (stAt "C1B").absTy.size == 3
#guard (tys "C1S")[2]! == "⊤" && (stAt "C1S").absTy.size == 5
-- (2) a record and a stored type that mention the refined unknown
#guard toString (stAt "E2B").neutrals == "[(⌈Pred2(σ0)⌉, 1)]"
#guard toString (stAt "E2").neutrals == "[(⌈Pred2(σ0)⌉, 1)]" && toString (stAt "E2").refs == "[(0, S(σ3)), (1, S(σ2))]"
#guard (tys "D2S")[2]! == "Box(S(σ2))" && (tys "D2S")[3]! == "&Box(S(σ2))"
-- (3) after the join: nothing of either world remains
#guard (stAt "W3").refs.isEmpty && (stAt "W3").etaRefs.isEmpty && (stAt "W3").neutrals.isEmpty &&
  (stAt "W3").absTy.size == 2 && (vals "W3")[1]! == "⊥"

end Ochr.Meaning.Regress.SplitSubst

namespace Ochr.Meaning.Regress.SplitSubstRef
open Ochr Ochr.Meaning Ochr.Meaning.Regress.CodeClosures Ochr.Meaning.Regress.CodeRuns

/-- `Pred2`'s body as a function on meanings: `Z ↦ 2`, `S m ↦ m`. -/
noncomputable def pred2Body (R : DataRead) : List Sem → Option BodyOut
  | [x] => match Code0.dec R .nat x with
    | some 0 => some ⟨.el0 Nat 2, [], none⟩
    | some (m + 1) => some ⟨.el0 Nat m, [], none⟩
    | none => none
  | _ => none

theorem pred2Body_nat (R : DataRead) (x : Nat) :
    pred2Body R [.el0 Nat x] = some ⟨.el0 Nat (match x with | 0 => 2 | m + 1 => m), [], none⟩ := by
  cases x <;> simp [pred2Body, dec_nat]

/-- `Pred2` as the `.fix` clause builds it, at `Π(n : Nat). Nat`'s code. -/
noncomputable def gPred2 (R : DataRead) : String → Sem × TyS :=
  fun _ => (closureL (lvl0 R) noFuture tNN (pred2Body R), .plain (piTyL (lvl0 R) tNN))

variable (dm : DataModel) (Γ : List IndDecl) (ρ : Assignment) (φ : Future)

/-- `Pred2(v)`, `v` a value meaning `k + 1` at every hint, runs to `k`, the state untouched. -/
theorem run_pred2 (v : Value) (k : Nat) (hv : ∀ T, meanV (Kp dm Γ (gPred2 dm.read)) ρ φ T v = .el0 Nat (k + 1))
    (hint : TyS) (s : SState) :
    run (Kp dm Γ (gPred2 dm.read)) ρ φ hint (.call (.const "Pred2") [.val v] true) s
      = some ((.el0 Nat k, .plain TyM.nat), s) := by
  rw [run_call]
  simp only [SM.headOf, bind, run_const]
  have ha : ∀ fT, runArgs (Kp dm Γ (gPred2 dm.read)) ρ φ false fT [] [.val v] s =
      some ([(.el0 Nat (k + 1), { valT (Kp dm Γ (gPred2 dm.read)) ρ φ (.plain (fT.domAfter dm.read [])) v with label := none })], s) := by
    intro fT
    simp only [runArgs, Bool.false_and]
    show (do let r ← run (Kp dm Γ (gPred2 dm.read)) ρ φ (.plain (fT.domAfter dm.read [])) (.val v); _) s = _
    simp only [bind, run_val_def, hv]
    rfl
  rw [ha]
  have hg2 : ∀ x : Nat, ∃ k' : Nat, pred2Body dm.read [.el0 Nat x] = some { result := .el0 Nat k', finals := [] } :=
    fun x => ⟨_, pred2Body_nat dm.read x⟩
  have happ := apply_strict (R := dm.read) noFuture (pred2Body dm.read) hg2 (k + 1) k (pred2Body_nat dm.read (k + 1))
  exact callOf_data0 dm tNN _ _ s _ _ (by simp [telRefsL, tNN, dec_nat]) happ
theorem succ_el0 (m : Nat) : (Sem.el0 Nat m).succ = .el0 Nat (m + 1) := by
  simp [Sem.succ, Sem.asNat, Sem.as]

/-- **(1) A stuck program re-run after a refinement keeps its meaning.** In the world `σ₀ := S(σ₁)`,
under an assignment meeting it (`ρ σ₀ = m + 1`, `ρ σ₁ = m`): the sealed program `⌈Pred2(σ₀)⌉` (as
the state held it before), its text substituted `⌈Pred2(S(σ₁))⌉` (as `substT` makes it, and as a
program holding a hole stays, D97) and the value its re-run computes, `σ₁` (as the checker's state
holds it in the world: `A1S`), all mean `m`. -/
theorem refine_keeps_sealed (m : Nat) (h0 : ρ 0 = .el0 Nat (m + 1)) (h1 : ρ 1 = .el0 Nat m) (hint : TyS) :
    meanV (Kp dm Γ (gPred2 dm.read)) ρ φ hint (.sealed (.call (.const "Pred2") [.val (.abs 0)] true)) = .el0 Nat m ∧
    meanV (Kp dm Γ (gPred2 dm.read)) ρ φ hint (.sealed (.call (.const "Pred2") [.val (.succ (.abs 1))] true)) = .el0 Nat m ∧
    meanV (Kp dm Γ (gPred2 dm.read)) ρ φ hint (.abs 1) = .el0 Nat m := by
  refine ⟨?_, ?_, ?_⟩
  · show (match run (Kp dm Γ (gPred2 dm.read)) ρ φ hint _ (emptyState 0) with
      | some ((v, _), _) => v | none => .err) = _
    rw [run_pred2 dm Γ ρ φ (.abs 0) m (fun _ => h0)]
  · show (match run (Kp dm Γ (gPred2 dm.read)) ρ φ hint _ (emptyState 0) with
      | some ((v, _), _) => v | none => .err) = _
    rw [run_pred2 dm Γ ρ φ (.succ (.abs 1)) m (fun _ => by
      show (meanV (Kp dm Γ (gPred2 dm.read)) ρ φ (.plain TyM.nat) (.abs 1)).succ = _
      show (ρ 1).succ = _
      rw [h1, succ_el0])]
  · exact h1

/-- **(2) A stored type that names the refined unknown means the same refined** (any run context):
`Box(σ₀)` and `Box(S(σ₁))` are one type where `ρ σ₀ = S(ρ σ₁)`. So the checker's substitution into
the stored types (`types = true`: `y : Box(σ₀)` becomes `y : Box(S(σ₁))`, and so does the type a
borrow of `y` holds, `D2S`) changes no meaning, and the reference's record of a borrow's content
type, a meaning taken when the borrow was made, still agrees. -/
theorem refine_keeps_type (K : RunCtx) (n : String) (m : Nat) (h0 : ρ 0 = .el0 Nat (m + 1)) (h1 : ρ 1 = .el0 Nat m)
    (hint : TyS) :
    meanV K ρ φ hint (.tInd n [.abs 0]) = meanV K ρ φ hint (.tInd n [.succ (.abs 1)]) := by
  have e : ∀ T : TyS, meanV K ρ φ T (.succ (.abs 1)) = meanV K ρ φ T (.abs 0) := by
    intro T
    show (ρ 1).succ = ρ 0
    rw [h0, h1, succ_el0]
  show (match K.Γ.find? (·.name == n) with
      | some d => Sem.ty (K.dm.tyM d (meanParams K ρ φ d 0 [] [.abs 0]))
      | none => .ty TyM.err) =
    (match K.Γ.find? (·.name == n) with
      | some d => Sem.ty (K.dm.tyM d (meanParams K ρ φ d 0 [] [.succ (.abs 1)]))
      | none => .ty TyM.err)
  cases K.Γ.find? (·.name == n) with
  | none => rfl
  | some d =>
    simp only [meanParams, e]

/-- **The substitution lemma for unknowns on the `SplitSubst` run** (`SubstAbs.lean`): the pure
substitution `σ₀ := S(σ₁)` makes `⌈Pred2(σ₀)⌉` into `⌈Pred2(S(σ₁))⌉`, and under an assignment meeting it
both the meanings and the whole runs agree, although the lemma's base-case hypothesis
(`AbsFillOK.shape`) fails there: the argument `S(σ₁)` is typed at the parameter's type and `σ₀` at
`Δ σ₀`, and a call reads its arguments' meanings only. -/
theorem pred2_instance (m : Nat) (h0 : ρ 0 = .el0 Nat (m + 1)) (h1 : ρ 1 = .el0 Nat m) (hint : TyS) (s : SState) :
    Value.substAbs 0 (.succ (.abs 1)) (.sealed (.call (.const "Pred2") [.val (.abs 0)] true))
        = .sealed (.call (.const "Pred2") [.val (.succ (.abs 1))] true) ∧
      meanV (Kp dm Γ (gPred2 dm.read)) ρ φ hint
          (Value.substAbs 0 (.succ (.abs 1)) (.sealed (.call (.const "Pred2") [.val (.abs 0)] true)))
        = meanV (Kp dm Γ (gPred2 dm.read)) ρ φ hint (.sealed (.call (.const "Pred2") [.val (.abs 0)] true)) ∧
      run (Kp dm Γ (gPred2 dm.read)) ρ φ hint (Term.substAbs 0 (.succ (.abs 1)) (.call (.const "Pred2") [.val (.abs 0)] true)) s
        = run (Kp dm Γ (gPred2 dm.read)) ρ φ hint (.call (.const "Pred2") [.val (.abs 0)] true) s := by
  obtain ⟨e0, e1, -⟩ := refine_keeps_sealed dm Γ ρ φ m h0 h1 hint
  refine ⟨rfl, ?_, ?_⟩
  · show meanV (Kp dm Γ (gPred2 dm.read)) ρ φ hint (.sealed (.call (.const "Pred2") [.val (.succ (.abs 1))] true)) = _
    rw [e0, e1]
  · show run (Kp dm Γ (gPred2 dm.read)) ρ φ hint (.call (.const "Pred2") [.val (.succ (.abs 1))] true) s = _
    rw [run_pred2 dm Γ ρ φ (.abs 0) m (fun _ => h0), run_pred2 dm Γ ρ φ (.succ (.abs 1)) m (fun _ => by
      show (ρ 1).succ = _
      rw [h1, succ_el0])]

/-- **The lemma's hypothesis holds on the `SplitSubst` run once `Δ` types the unknown at its stored
type** (`DeltaOk`: `σ₀ : Nat`): the filler `S(σ₁)` means `ρ σ₀`, the run types `.val S(σ₁)` at `Nat`
as it types `.val σ₀`, and the probes' decisions are constant. -/
theorem pred2_absFill (m : Nat) (h0 : ρ 0 = .el0 Nat (m + 1)) (h1 : ρ 1 = .el0 Nat m) :
    AbsFillOK { Kp dm Γ (gPred2 dm.read) with Δ := fun _ => .plain TyM.nat } ρ φ 0 (.succ (.abs 1)) where
  mean hint := by
    show (ρ 1).succ = ρ 0
    rw [h0, h1, succ_el0]
  shape hint s := by rw [run_val_def, run_val_def]; rfl
  dec := ⟨fun _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl, fun _ _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl,
    fun _ _ _ => rfl⟩

/-- **The substitution lemma for unknowns, applied on the `SplitSubst` run** (`run_substAbs`): the
substituted call runs as the call, as `pred2_instance` computed by hand. -/
theorem pred2_by_lemma (m : Nat) (h0 : ρ 0 = .el0 Nat (m + 1)) (h1 : ρ 1 = .el0 Nat m) (hint : TyS) (s : SState) :
    run { Kp dm Γ (gPred2 dm.read) with Δ := fun _ => .plain TyM.nat } ρ φ hint
        (Term.substAbs 0 (.succ (.abs 1)) (.call (.const "Pred2") [.val (.abs 0)] true)) s
      = run { Kp dm Γ (gPred2 dm.read) with Δ := fun _ => .plain TyM.nat } ρ φ hint
        (.call (.const "Pred2") [.val (.abs 0)] true) s := by
  show runT _ ρ φ false hint _ s = runT _ ρ φ false hint _ s
  rw [run_substAbs _ ρ φ 0 _ (pred2_absFill dm Γ ρ φ m h0 h1) false]

end Ochr.Meaning.Regress.SplitSubstRef
