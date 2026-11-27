import Ochr.Meaning.ClosureStage

/-!
# A stage closure is not an argument of a parameter of its function's declared type (lead37; docs/31 D232)

The knot of [Def] (`Consistency.step_member_fix`, `fix_split`'s step; docs/31 D213's first step) simulates a recursive
definition's check under the context `K_b`, where the definition means its stage-`b` closure typed at the WEAKENED
function type (the true codomain below the bound, `Unit` above; `MemBelow`, docs/34). The checker's check of
`MB0 (m : Nat) (n : Nat) : Nat by n := let r = match m { Z => Z, S p => match n { Z => Z, S k => MB0(p, k) } }; r`
(accepted; `Steps/RecDescAttack`) closes the non-tail match off as a stuck block that takes the function's own binding
as a PARAMETER at its declared type and is applied to the global itself:
`r ↦ ⌈(fix _ (MB0 : Π(m : Nat) (n : Nat). Nat) (m : Nat) (n : Nat) : Nat := match m { … MB0(m.0, n.0) … })(MB0, σ0, σ1)⌉`.
Under `K_b` the reference reads that sealed program by applying the block's closure (whose first parameter is the
declared type `Π(m : Nat) (n : Nat). Nat`) to the global's meaning, the stage closure.

Kernel-checked here, at bound `0` (the knot's first step, where `MB0`'s leaf is reached at every assignment with `n = 0`):
- `stage0_not_mem`: the stage-`0` closure of a function of type `Π(m : Nat) (n : Nat). Nat` is NOT a member of that type
  (the weakened carrier is a subsingleton, the declared one is not, so they are different types);
- `stage0_dec`: decoding it at the declared type's code fails;
- `callOf_stage0`: so every call of a level-0 function whose first parameter has the declared type fails at it.
So under `K_0` the meaning of `MB0`'s leaf value is `err`, while the reference's direct run of the body (which runs the
match, no block) gives `0`: the simulation's relation at `r` is false.
- `stage0_apply`: the stage-`0` closure, applied at any member arguments, gives `()` at `Unit` (what any repair that
  passes the stage closure to the block at its own type would meet: the block, a function of all values of its
  captures, calls it above its bound).
-/

namespace Ochr.Meaning.Steps.StageBlock

open Ochr Ochr.Meaning Ochr.Meaning.Steps

/-- `Nat` as the model reads it at a parameter (no borrow) and as a codomain. -/
def natDom : PiDom := ⟨false, fun _ => TyM.nat⟩
def natOut : PiCod := ⟨false, fun _ => TyM.nat⟩
/-- The domains of `Π(m : Nat) (n : Nat). Nat`. -/
def psMB : List PiDom := [natDom, natDom]

section
variable (R : DataRead)

/-- The declared type's carrier, `ℕ → ℕ → ℕ × PUnit`. -/
abbrev CT : Type := (telL (lvl0 R) psMB [] PUnit natOut).1

/-- The stage-`0` closure's carrier, at the weakened codomain (`Unit` everywhere at bound `0`). -/
abbrev CW (rk : List Sem → Nat) : Type := (telL (lvl0 R) psMB [] PUnit (weakCod 1 rk 0 natOut)).1

theorem unit_code_eq {X : TyM} (h : X = TyM.unit) (x y : (TyM.code0 X).1) : x = y := by
  subst h; cases x; cases y; rfl

/-- At bound `0` the weakened codomain is `Unit` at every argument tuple. -/
theorem weak0_cod (rk : List Sem → Nat) (acc : List Sem) : (weakCod 1 rk 0 natOut).cod acc = TyM.unit := by
  simp [weakCod, fillTy]

/-- The stage-`0` carrier is a subsingleton. -/
theorem cw_sub (rk : List Sem → Nat) (f g : CW R rk) : f = g := by
  funext a a'
  refine Prod.ext ?_ rfl
  apply unit_code_eq
  exact weak0_cod rk _

/-- The declared carrier is `ℕ → ℕ → ℕ × PUnit`. -/
theorem ct_eq : CT R = (Nat → Nat → Nat × PUnit) := rfl

/-- The declared carrier is not a subsingleton: two constant functions differ. -/
theorem ct_not_sub : ¬ ∀ f g : CT R, f = g := by
  intro h
  rw [ct_eq] at h
  have := congrArg (fun f : Nat → Nat → Nat × PUnit => (f 0 0).1)
    (h (fun _ _ => ((0 : Nat), PUnit.unit)) (fun _ _ => ((1 : Nat), PUnit.unit)))
  exact absurd this (by decide)

/-- **The two carriers are different types.** -/
theorem cw_ne_ct (rk : List Sem → Nat) : CW R rk ≠ CT R := by
  intro h
  apply ct_not_sub R
  rw [← h]
  exact cw_sub R rk

/-- The stage-`0` closure (of ANY function) is not the encoding of an element of the declared type. -/
theorem stage0_ne_enc (rk : List Sem → Nat) (φ : Future) (g : List Sem → Option BodyOut) (t : Tel Code0 PUnit (CT R))
    (a : CT R) : (Code0.pi (CT R) t).enc R a ≠ closureAt R 1 φ psMB (weakCod 1 rk 0 natOut) g := by
  show Sem.el0 (CT R) a ≠ closureL (lvl0 R) φ (telL (lvl0 R) psMB [] PUnit (weakCod 1 rk 0 natOut)).2 g
  unfold closureL
  split
  · intro h
    exact cw_ne_ct R rk (Sem.el0.inj h).1.symm
  · intro h; cases h

/-- **The stage-`0` closure is not a member of the function's declared type.** -/
theorem stage0_not_mem (rk : List Sem → Nat) (φ : Future) (g : List Sem → Option BodyOut) :
    ¬ (closureAt R 1 φ psMB (weakCod 1 rk 0 natOut) g ∈ₛ[R] piTyAt R 1 psMB natOut) := by
  rintro ⟨a, ha⟩
  exact stage0_ne_enc R rk φ g _ a ha

/-- **Decoding it at the declared type's code fails.** -/
theorem stage0_dec (rk : List Sem → Nat) (φ : Future) (g : List Sem → Option BodyOut) (t : Tel Code0 PUnit (CT R)) :
    Code0.dec R (Code0.pi (CT R) t) (closureAt R 1 φ psMB (weakCod 1 rk 0 natOut) g) = none := by
  unfold Code0.dec
  rw [dif_neg]
  rintro ⟨a, ha⟩
  exact stage0_ne_enc R rk φ g t a ha

/-- A parameter of the declared type `Π(m : Nat) (n : Nat). Nat` (the block's first parameter, `MB0 : Π(m : Nat) (n : Nat).
Nat`, as the reference reads its type term: a closed type, the same at every earlier argument). -/
noncomputable def mbDom (isRef : Bool) : PiDom := ⟨isRef, fun _ => piTyAt R 1 psMB natOut⟩

/-- **Every call of a level-0 function whose first parameter has the declared type fails at the stage-`0` closure**:
the argument does not decode at the parameter's code (`stage0_dec`). -/
theorem callOf_stage0 (rk : List Sem → Nat) (φ : Future) (g : List Sem → Option BodyOut) (isRef : Bool)
    (ps' : List PiDom) (out' : PiCod) (F : Sem) (T0 : TyS) (rest : List Res) (s : SState) :
    callOf R (F, .plain (piTyAt R 1 (mbDom R isRef :: ps') out'))
      ((closureAt R 1 φ psMB (weakCod 1 rk 0 natOut) g, T0) :: rest) s = none := by
  have hap : ∀ F' : (telL (lvl0 R) (mbDom R isRef :: ps') [] PUnit out').1,
      applyTelL (lvl0 R) (telL (lvl0 R) (mbDom R isRef :: ps') [] PUnit out').2 (fun _ => [])
        F' ((closureAt R 1 φ psMB (weakCod 1 rk 0 natOut) g) :: rest.map (·.1)) = none := by
    intro F'
    have hd : (lvl0 R).dec ((lvl0 R).codeOf ((mbDom R isRef).dom [])).snd
        (closureAt R 1 φ psMB (weakCod 1 rk 0 natOut) g) = none :=
      stage0_dec R rk φ g (telL (lvl0 R) psMB [] PUnit natOut).2
    erw [applyTelL.eq_3]
    rw [hd]
  show callOfL (lvl0 R) (telL (lvl0 R) (mbDom R isRef :: ps') [] PUnit out').2 F _ s = none
  unfold callOfL applyFnL
  dsimp only
  generalize Sem.as _ F = o
  cases o with
  | none => rfl
  | some F' => simp only [Option.bind_some, List.map_cons, hap F']

/-- **The stage-`0` closure, applied at ANY member arguments, gives `()` at `Unit`** (at its own, weakened, type): what a
block that received it at that type would get at every argument, where the block's own codomain is `Nat`. -/
theorem stage0_apply (rk : List Sem → Nat) (φ : Future) (g : List Sem → Option BodyOut) (args : List Res) (s : SState)
    (hm : DomMembers R psMB (args.map (·.1))) :
    ∃ s', callOf R (closureAt R 1 φ psMB (weakCod 1 rk 0 natOut) (stageFn 1 psMB rk 0 g),
        .plain (piTyAt R 1 psMB (weakCod 1 rk 0 natOut))) args s =
      some ((.el0 Unit (), .plain TyM.unit), s') := by
  have hnl : ∀ a : List Sem, ¬ rk a < 0 := fun a => Nat.not_lt_zero _
  have hfill : stageFn 1 psMB rk 0 g (args.map (·.1)) = some ⟨fillVal 1, refFinals psMB (args.map (·.1)), some 0⟩ := by
    simp [stageFn]
  obtain ⟨s', hs'⟩ := closure_apply' R 1 φ psMB (weakCod 1 rk 0 natOut) (stageFn 1 psMB rk 0 g) ⟨Nat.le_refl 1, by omega⟩ rfl
    (weakCod_fit 1 ⟨Nat.le_refl 1, by omega⟩ R psMB rk 0 natOut (fun a _ h => absurd h (hnl a)))
    (stageFn_good R 1 psMB rk 0 natOut g (fun a _ h => absurd h (hnl a))) args s _ hm
    (fun i d hd => by
      rcases i with _ | _ | i <;> simp [psMB, natDom] at hd <;> subst hd <;> exact Nat.le_refl 1)
    (by rw [weak0_cod]; trivial) hfill
  refine ⟨s', ?_⟩
  rw [hs', weak0_cod]
  rfl

end

/-! ## A block is checked only at its captured values (D232's ruling, attack (b))

`NTr (n : Nat) (m : Nat) : Nat := match n { Z => Z, S p => let r = match m { Z => clone(n), S q => clone(p) }; r }` is
accepted; its non-tail match closes off as `⌈(fix _ (n : Nat) (m : Nat) : Nat := match m { Z => clone(n), S _ =>
clone(n.0) })(S(σ2), σ1)⌉` (`Steps/RecDescAttack`): the block takes `n` whole and reads its predecessor, which exists at
the captured `S(σ2)` and at no `0`. The model reads a closure strictly, as an element of its function type, so it asks
the block's function at EVERY value of its parameters: at `(0, 1)` its run reads the predecessor of `0`, which is
undefined (`step_pred_zero`), and a closure whose function fails at one fitting argument is `err`
(`closureL_err_of_none`). So today the model reads `NTr`'s leaf as `err`, for a definition with no recursion at all. -/

section
variable {L : Lvl}

/-- **A closure whose function fails at one argument tuple that fits its code is `err`**: the carrier holds total
functions only. -/
theorem closureL_err_of_none (hL : L.Lawful) (φ : Future) {C : Type _} (t : Tel L.Code PUnit C)
    (g : List Sem → Option BodyOut) (args : List Sem) (hfit : ArgsFitL L t args) (hg : g args = none) :
    closureL L φ t g = .err := by
  unfold closureL
  split
  · rename_i F hF
    obtain ⟨o, -, hgo, -, -⟩ := applyTelL_mkTelL L hL φ g t [] _ (fun _ => []) F args finInv_start hF hfit
    rw [List.nil_append, hg] at hgo
    cases hgo
  · rfl

end

/-- The predecessor of `0` is undefined: a run that reads it fails. -/
theorem step_pred_zero (dm : DataModel) (Γ : List IndDecl) (T : TyS) :
    Sem.step dm Γ T (.proj 0) (.el0 Nat 0) = none := by
  have h : (Sem.el0 Nat 0).asNat = some 0 := by simp [Sem.asNat, Sem.as]
  simp [Sem.step, h]

end Ochr.Meaning.Steps.StageBlock
