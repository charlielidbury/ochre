import Ochr.Meaning.Steps.TopRLinks

/-!
# The acceptance test at `R`: what later checks read of `R` (`GlobGrowG`; lead46, docs/31 D259 on)

After `R`'s check, its entry must meet `GlobalsOk`'s clauses at the context of every later check. Tools here: `R`'s
closure at `Π(n : Nat). Nat` is determined by its function at the numbers (the closure applies it only at encoded
carrier elements, and a data codomain with no borrow parameter reads no future), and `R`'s function is `0` at every
number at every context whose table decides `R`'s code as the checker does.
-/

namespace Ochr.Meaning.Steps.Form.Top.RT

open Ochr Ochr.Meaning Ochr.Meaning.Steps Ochr.Meaning.Steps.Form Ochr.Meaning.Steps.Form.Master
open Ochr.Meaning.Steps.Form.ColumnR Ochr.Meaning.Steps.Form.FixEqDesc
open Ochr.Meaning.Steps.Form.ColumnI (psI outI)

/-- **A closure at `Π(n : Nat). Nat` is determined by its function at the numbers** (whose outputs have no finals): at
any two futures. -/
theorem closureAt_nat_congr (R : DataRead) (φ φ' : Future) (g g' : List Sem → Option BodyOut)
    (hg : ∀ m, g [.el0 Nat m] = g' [.el0 Nat m]) (hf : ∀ m o, g [.el0 Nat m] = some o → o.finals = []) :
    closureAt R 1 φ psI outI g = closureAt R 1 φ' psI outI g' := by
  unfold closureAt closureL
  have key : mkTelL (lvl0 R) φ (telL (lvl0 R) psI [] PUnit outI).2 [] (fun fs => some (PUnit.unit, fs)) g =
      mkTelL (lvl0 R) φ' (telL (lvl0 R) psI [] PUnit outI).2 [] (fun fs => some (PUnit.unit, fs)) g' := by
    simp only [psI, outI, telL, mkTelL, List.nil_append]
    refine dite_isSome_congr _ _ (funext fun x => ?_)
    have hx : Code0.enc R TyM.nat.code0.snd x = Sem.el0 Nat x := rfl
    rw [hx, ← hg x]
    rcases e : g [Sem.el0 Nat x] with _ | o
    · rfl
    · simp only [Option.bind_some]
      unfold mkLeafDataL
      rw [hf x o e]
      rfl
  rw [key]
  rfl


/-- **`R`'s function is `0` at every number** (PROVED at every context whose table decides `R`'s code as the checker
does: the fixpoint equation, `fixEqAt_R`, and the body's run, `fixBodyAt_R_anyK`, by induction on the number). -/
theorem GG_R (K : RunCtx) (hd : DecR K.D) (ρ : Assignment) (φ : Future) (m : Nat) :
    GG K ρ φ [⟨"n"⟩] [.nat] .nat (some 0) bodyR [.el0 Nat m] = some ⟨.el0 Nat 0, [], none⟩ := by
  have hfg := fnGoodAt_R (φ := φ) K ρ hd
  unfold FnGoodAt at hfg
  rw [psG_R K ρ hd, outG_R K ρ, lG_R K hd] at hfg
  have hX : SelfR K.dm outI (GG K ρ φ [⟨"n"⟩] [.nat] .nat (some 0) bodyR) := ⟨rfl, fun a ha => hfg.1.2 a ha trivial, hfg.2⟩
  have hsel : selfG K ρ φ [⟨"n"⟩] [.nat] .nat (some 0) bodyR =
      closureAt K.dm.read 1 φ psI outI (GG K ρ φ [⟨"n"⟩] [.nat] .nat (some 0) bodyR) := by
    unfold selfG; rw [psG_R K ρ hd, outG_R K ρ, lG_R K hd]
  have hpiT : piTG K ρ φ [⟨"n"⟩] [.nat] .nat = piTyAt K.dm.read 1 psI outI := by
    unfold piTG; rw [psG_R K ρ hd, outG_R K ρ, lG_R K hd]
  have hT := fixBodyAt_R_anyK (φ := φ) K hd.1 ρ (fbG K ρ φ [.nat] .nat) (fbG_R1 K ρ hd) (fbG_R2 K ρ hd)
    (closureAt K.dm.read 1 φ psI outI (GG K ρ φ [⟨"n"⟩] [.nat] .nat (some 0) bodyR), .plain (piTyAt K.dm.read 1 psI outI))
    rfl hX.whole (SelfR.movedIn outI _) hX.mem
  have heq : ∀ k, GG K ρ φ [⟨"n"⟩] [.nat] .nat (some 0) bodyR [.el0 Nat k] =
      fixBodyAt K ρ φ (fbG K ρ φ [.nat] .nat) (emptyState 0) psI outI (piTyAt K.dm.read 1 psI outI) 0 bodyR
        (closureAt K.dm.read 1 φ psI outI (GG K ρ φ [⟨"n"⟩] [.nat] .nat (some 0) bodyR)) [.el0 Nat k] := by
    intro k
    have h := fixEqAt_R (φ := φ) K ρ hd [.el0 Nat k] (by rw [psG_R K ρ hd]; exact domMembers_nat _ k)
    rw [h, psG_R K ρ hd, outG_R K ρ, hpiT, hsel]
    rfl
  induction m with
  | zero => rw [heq]; exact hT.1
  | succ m ih =>
    rw [heq]
    exact hT.2 m (.el0 Nat 0) _ rfl (fun s => SelfR.apply (φ := φ) hX m ih s)

end Ochr.Meaning.Steps.Form.Top.RT
