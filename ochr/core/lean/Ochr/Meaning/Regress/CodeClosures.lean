import Ochr.Meaning.Apply1

/-!
# Closures are members of their types' codes (docs/31 D59, D60; built, kernel-checked)

The concrete check the lead asked for before the re-proof: a recursive function, a function
returning a function, a function taking a function parameter, and a polymorphic function applied
to a function type, each built along its type's code exactly as the reference run's `.fix` clause
builds it (`telL`, `closureL`, and the recursion's stages with `closureFillL`), each a member of its
type's code, and each applied by `applyFnL` as a call applies it. The bodies are written as
functions on meanings (what the `.fix` clause's `bodyAt` computes for these terms); the terms'
own runs need a concrete instance of the decisions under `run` (docs/31, the open check per term
form) and are not run here.

Found on the way (docs/31 D60): with the stages' closures built strictly, as the `.fix` clause
did, every recursive closure meant `err` (`Old.closure_err`): a stage is defined only below its
rank, the carrier holds total functions only, so every stage's closure was `err`, and so every
recursive call failed.
-/

namespace Ochr.Meaning.Regress.CodeClosures
open Ochr Ochr.Meaning

/-- `Π(n : Nat). Nat` at `Type₀`: its carrier, and its telescope code. -/
abbrev NN : Type := (n : Nat) → Nat × PUnit

def tNN : Tel lvl0.Code PUnit NN := .param PUnit false Nat .nat (fun _ => Nat × PUnit) fun _ => .dat PUnit Nat .nat

/-- It is the code the reference run builds from the description (each domain and the codomain
`Nat`). -/
theorem tNN_telL : telL lvl0 [⟨false, fun _ => TyM.nat⟩] [] PUnit ⟨false, fun _ => TyM.nat⟩ = ⟨NN, tNN⟩ := rfl

theorem dec_nat (n : Nat) : Code0.dec .nat (.el0 Nat n) = some n := Code0.dec_enc .nat n

/-- The element built along `tNN`, where the body gives a number at every number. -/
theorem mk_some (φ : Future) (g : List Sem → Option BodyOut)
    (hg : ∀ x, ∃ k, g [.el0 Nat x] = some ⟨.el0 Nat k, [], none⟩) :
    ∃ F, mkTelL lvl0 φ tNN [] (fun fs => some (PUnit.unit, fs)) g = some F ∧
      ∀ x k, g [.el0 Nat x] = some ⟨.el0 Nat k, [], none⟩ → F x = (k, PUnit.unit) := by
  have hleaf : ∀ x k, g [.el0 Nat x] = some ⟨.el0 Nat k, [], none⟩ →
      (g ([] ++ [lvl0.enc Code0.nat x])).bind (mkLeafDataL lvl0 φ (extFin false PUnit Nat)
        (extMkL false PUnit Nat (fun fs => some (PUnit.unit, fs)) (lvl0.dec Code0.nat)) Code0.nat)
        = some (k, PUnit.unit) := by
    intro x k h
    show (g [.el0 Nat x]).bind _ = _
    rw [h]
    simp [mkLeafDataL, extMkL, dec_nat]
  have hall : ∀ x : Nat, (mkTelL lvl0 φ (Tel.dat PUnit Nat .nat) ([] ++ [lvl0.enc Code0.nat x])
      (extMkL false PUnit Nat (fun fs => some (PUnit.unit, fs)) (lvl0.dec Code0.nat)) g).isSome := by
    intro x
    obtain ⟨k, hk⟩ := hg x
    rw [mkTelL.eq_1, hleaf x k hk]; rfl
  refine ⟨fun x => (mkTelL lvl0 φ (Tel.dat PUnit Nat .nat) ([] ++ [lvl0.enc Code0.nat x])
      (extMkL false PUnit Nat (fun fs => some (PUnit.unit, fs)) (lvl0.dec Code0.nat)) g).get (hall x), ?_, ?_⟩
  · unfold tNN
    rw [mkTelL.eq_3, dif_pos hall]
  · intro x k hk
    have e : mkTelL lvl0 φ (Tel.dat PUnit Nat .nat) ([] ++ [lvl0.enc Code0.nat x])
        (extMkL false PUnit Nat (fun fs => some (PUnit.unit, fs)) (lvl0.dec Code0.nat)) g = some (k, PUnit.unit) := by
      rw [mkTelL.eq_1, hleaf x k hk]
    simp only [e, Option.get_some]

/-- A closure along `tNN` is `err` where its body is undefined at some number. -/
theorem closure_err (φ : Future) (g : List Sem → Option BodyOut) (x : Nat) (hx : g [.el0 Nat x] = none) :
    closureL lvl0 φ tNN g = .err := by
  unfold closureL
  split
  · rename_i F hF
    exfalso
    unfold tNN at hF
    rw [mkTelL.eq_3] at hF
    split at hF
    · rename_i h
      have := h x
      rw [mkTelL.eq_1] at this
      simp [Code0.enc, hx] at this
    · cases hF
  · rfl

/-- Applying `err` fails. -/
theorem apply_err (args : List Sem) : applyFnL lvl0 tNN .err args = none := rfl

/-- A closure along `tNN`, applied at `n` where its body gives `k`, gives `k`, at `Nat`. -/
theorem apply_strict (φ : Future) (g : List Sem → Option BodyOut) (hg : ∀ x, ∃ k, g [.el0 Nat x] = some ⟨.el0 Nat k, [], none⟩)
    (n k : Nat) (hn : g [.el0 Nat n] = some ⟨.el0 Nat k, [], none⟩) :
    applyFnL lvl0 tNN (closureL lvl0 φ tNN g) [.el0 Nat n] = some (.data (.el0 Nat k) TyM.nat []) := by
  obtain ⟨F, hF, hFx⟩ := mk_some φ g hg
  unfold closureL
  rw [hF]
  show (Sem.as NN (.el0 NN F)).bind (fun F => applyTelL lvl0 tNN (fun _ => []) F [.el0 Nat n]) = _
  rw [show Sem.as NN (.el0 NN F) = some F from lvl0_lawful.unpack_pack NN F, Option.bind_some]
  simp only [tNN, applyTelL, lvl0, dec_nat, hFx n k hn]
  rfl

/-- The element a recursion stage's closure is built from along `tNN`: filled where the stage is
undefined (`Nat × PUnit` is inhabited, so never `err`), and the body's number where it is defined. -/
theorem fill_some (φ : Future) (g : List Sem → Option BodyOut) :
    ∃ F, mkTelFillL lvl0 φ tNN [] (fun fs => some (PUnit.unit, fs)) g = some F ∧
      ∀ x k, g [.el0 Nat x] = some ⟨.el0 Nat k, [], none⟩ → F x = (k, PUnit.unit) := by
  have hleaf : ∀ x, ∃ r, mkTelFillL lvl0 φ (Tel.dat PUnit Nat .nat) ([] ++ [lvl0.enc Code0.nat x])
      (extMkL false PUnit Nat (fun fs => some (PUnit.unit, fs)) (lvl0.dec Code0.nat)) g = some r ∧
      ∀ k, g [.el0 Nat x] = some ⟨.el0 Nat k, [], none⟩ → r = (k, PUnit.unit) := by
    intro x
    rw [mkTelFillL.eq_1]
    cases hgx : g [.el0 Nat x] with
    | none =>
      have : (g ([] ++ [lvl0.enc Code0.nat x])) = none := hgx
      simp only [this, Option.bind_none]
      exact ⟨_, dif_pos ⟨(0, PUnit.unit)⟩, fun k h => by cases h⟩
    | some o =>
      have : (g ([] ++ [lvl0.enc Code0.nat x])) = some o := hgx
      simp only [this, Option.bind_some]
      cases hl : mkLeafDataL lvl0 φ (extFin false PUnit Nat)
          (extMkL false PUnit Nat (fun fs => some (PUnit.unit, fs)) (lvl0.dec Code0.nat)) Code0.nat o with
      | some r =>
        refine ⟨r, rfl, fun k hk => ?_⟩
        cases hk
        simp [mkLeafDataL, extMkL, dec_nat] at hl
        exact hl.symm
      | none =>
        refine ⟨_, dif_pos ⟨(0, PUnit.unit)⟩, fun k hk => ?_⟩
        cases hk
        simp [mkLeafDataL, extMkL, dec_nat] at hl
  have hall : ∀ x : Nat, (mkTelFillL lvl0 φ (Tel.dat PUnit Nat .nat) ([] ++ [lvl0.enc Code0.nat x])
      (extMkL false PUnit Nat (fun fs => some (PUnit.unit, fs)) (lvl0.dec Code0.nat)) g).isSome := by
    intro x
    obtain ⟨r, hr, -⟩ := hleaf x
    rw [hr]; rfl
  refine ⟨fun x => (mkTelFillL lvl0 φ (Tel.dat PUnit Nat .nat) ([] ++ [lvl0.enc Code0.nat x])
      (extMkL false PUnit Nat (fun fs => some (PUnit.unit, fs)) (lvl0.dec Code0.nat)) g).get (hall x), ?_, ?_⟩
  · unfold tNN
    rw [mkTelFillL.eq_3, dif_pos hall]
  · intro x k hk
    obtain ⟨r, hr, hrk⟩ := hleaf x
    simp only [hr, Option.get_some, hrk k hk]

/-- A recursion stage's closure along `tNN`, applied at `n` where the stage gives `k`, gives `k`. -/
theorem apply_fill (φ : Future) (g : List Sem → Option BodyOut) (n k : Nat)
    (hn : g [.el0 Nat n] = some ⟨.el0 Nat k, [], none⟩) :
    applyFnL lvl0 tNN (closureFillL lvl0 φ tNN g) [.el0 Nat n] = some (.data (.el0 Nat k) TyM.nat []) := by
  obtain ⟨F, hF, hFx⟩ := fill_some φ g
  unfold closureFillL
  rw [hF]
  show (Sem.as NN (.el0 NN F)).bind (fun F => applyTelL lvl0 tNN (fun _ => []) F [.el0 Nat n]) = _
  rw [show Sem.as NN (.el0 NN F) = some F from lvl0_lawful.unpack_pack NN F, Option.bind_some]
  simp only [tNN, applyTelL, lvl0, dec_nat, hFx n k hn]
  rfl

/-! ## A recursive function: `double (n : Nat) : Nat by n := match n { Z => Z, S m => S(S(double(m))) }`

The `.fix` clause's construction, with `bodyAt self` written as the function on meanings the body
computes (`dblBody`): a call through `self` applies it along `tNN`. -/

noncomputable def dblBody (self : Sem) : List Sem → Option BodyOut
  | [x] => match Code0.dec .nat x with
    | some 0 => some ⟨.el0 Nat 0, [], none⟩
    | some (m + 1) => match applyFnL lvl0 tNN self [.el0 Nat m] with
      | some (.data r _ _) => (Code0.dec .nat r).map fun k => ⟨.el0 Nat (k + 2), [], none⟩
      | _ => none
    | none => none
  | _ => none

/-- The stages, each binding `self` to the closure `mk` builds of the stage below (the `.fix`
clause's `stage`). -/
noncomputable def stage (mk : (List Sem → Option BodyOut) → Sem) (k : Nat) : List Sem → Option BodyOut :=
  Nat.rec (motive := fun _ => List Sem → Option BodyOut) (fun _ => none) (fun _ gk => dblBody (mk gk)) k

noncomputable def rankOf : List Sem → Nat
  | [x] => (Code0.dec .nat x).getD 0
  | _ => 0

/-- The function at arguments of rank `r` is stage `r + 1` (the `.fix` clause's `g`). -/
noncomputable def gOf (mk : (List Sem → Option BodyOut) → Sem) : List Sem → Option BodyOut :=
  fun args => stage mk (rankOf args + 1) args

theorem rankOf_nat (n : Nat) : rankOf [.el0 Nat n] = n := by simp [rankOf, dec_nat]

theorem dblBody_zero (self : Sem) : dblBody self [.el0 Nat 0] = some ⟨.el0 Nat 0, [], none⟩ := by
  simp [dblBody, dec_nat]

theorem dblBody_succ (self : Sem) (m : Nat) :
    dblBody self [.el0 Nat (m + 1)] = match applyFnL lvl0 tNN self [.el0 Nat m] with
      | some (.data r _ _) => (Code0.dec .nat r).map fun k => ⟨.el0 Nat (k + 2), [], none⟩
      | _ => none := by
  simp [dblBody, dec_nat]

namespace Old

/-- **As the `.fix` clause built it before D60, the recursive closure is `err`**: each stage's
closure was built strictly, so it was `err` (a stage is undefined above its rank), and every
recursive call through it failed. -/
theorem closure_err (φ : Future) : closureL lvl0 φ tNN (gOf (closureL lvl0 φ tNN)) = .err := by
  have h0 : closureL lvl0 φ tNN (stage (closureL lvl0 φ tNN) 0) = .err :=
    CodeClosures.closure_err φ _ 0 rfl
  have h1 : stage (closureL lvl0 φ tNN) 1 [.el0 Nat 1] = none := by
    show dblBody (closureL lvl0 φ tNN (stage (closureL lvl0 φ tNN) 0)) [.el0 Nat (0 + 1)] = none
    rw [dblBody_succ, h0, apply_err]
  have h1' : closureL lvl0 φ tNN (stage (closureL lvl0 φ tNN) 1) = .err :=
    CodeClosures.closure_err φ _ 1 h1
  apply CodeClosures.closure_err φ _ 1
  show stage (closureL lvl0 φ tNN) (rankOf [.el0 Nat 1] + 1) [.el0 Nat 1] = none
  rw [rankOf_nat]
  show dblBody (closureL lvl0 φ tNN (stage (closureL lvl0 φ tNN) 1)) [.el0 Nat (0 + 1)] = none
  rw [dblBody_succ, h1', apply_err]

end Old

/-- With the stages' closures filled (D60), stage `n + 1` doubles `n`. -/
theorem stage_val (φ : Future) : ∀ n : Nat,
    stage (closureFillL lvl0 φ tNN) (n + 1) [.el0 Nat n] = some ⟨.el0 Nat (2 * n), [], none⟩
  | 0 => dblBody_zero _
  | m + 1 => by
    show dblBody (closureFillL lvl0 φ tNN (stage (closureFillL lvl0 φ tNN) (m + 1))) [.el0 Nat (m + 1)] = _
    rw [dblBody_succ, apply_fill φ _ m (2 * m) (stage_val φ m)]
    simp only [Option.map, dec_nat]
    congr 3

/-- **The recursive closure is a member of its type's code**, and `double(3)` is `6`. -/
theorem double_member (φ : Future) :
    closureL lvl0 φ tNN (gOf (closureFillL lvl0 φ tNN)) ∈ₛ piTyL lvl0 tNN ∧
      closureL lvl0 φ tNN (gOf (closureFillL lvl0 φ tNN)) ≠ .err ∧
      applyFnL lvl0 tNN (closureL lvl0 φ tNN (gOf (closureFillL lvl0 φ tNN))) [.el0 Nat 3]
        = some (.data (.el0 Nat 6) TyM.nat []) := by
  have hg : ∀ x, gOf (closureFillL lvl0 φ tNN) [.el0 Nat x] = some ⟨.el0 Nat (2 * x), [], none⟩ := by
    intro x
    show stage _ (rankOf [.el0 Nat x] + 1) [.el0 Nat x] = _
    rw [rankOf_nat]; exact stage_val φ x
  obtain ⟨F, hF, -⟩ := mk_some φ _ fun x => ⟨_, hg x⟩
  have hc : closureL lvl0 φ tNN (gOf (closureFillL lvl0 φ tNN)) = .el0 NN F := by
    unfold closureL; rw [hF]
  refine ⟨?_, ?_, apply_strict φ _ (fun x => ⟨_, hg x⟩) 3 6 (hg 3)⟩
  · rw [hc]; exact ⟨F, rfl⟩
  · rw [hc]; exact fun h => by cases h

/-! ## A function returning a function: `Adder (n : Nat) : Π(m : Nat). Nat` (`UseAdder`)

Its codomain's code is `tNN`'s, so the call's result is typed at it and can be called. -/

/-- `Π(n : Nat). Π(m : Nat). Nat`: the codomain is a function type's code. -/
def tAdd : Tel lvl0.Code PUnit ((n : Nat) → NN × PUnit) :=
  .param PUnit false Nat .nat (fun _ => NN × PUnit) fun _ => .dat PUnit NN (.pi NN tNN)

/-- The inner closure's body: `n + m`. -/
noncomputable def addBody (n : Nat) : List Sem → Option BodyOut
  | [x] => (Code0.dec .nat x).map fun m => ⟨.el0 Nat (n + m), [], none⟩
  | _ => none

/-- The outer body returns the inner closure. -/
noncomputable def adderBody (φ : Future) : List Sem → Option BodyOut
  | [x] => (Code0.dec .nat x).map fun n => ⟨closureL lvl0 φ tNN (addBody n), [], none⟩
  | _ => none

theorem addBody_nat (n m : Nat) : addBody n [.el0 Nat m] = some ⟨.el0 Nat (n + m), [], none⟩ := by
  simp [addBody, dec_nat]

theorem inner_eq (φ : Future) (n : Nat) : ∃ F : NN, closureL lvl0 φ tNN (addBody n) = .el0 NN F := by
  obtain ⟨F, hF, -⟩ := mk_some φ (addBody n) fun x => ⟨_, addBody_nat n x⟩
  exact ⟨F, by unfold closureL; rw [hF]⟩

/-- **`Adder` is a member of its type's code, and `Adder(2)` is a function typed at the code of
`Π(m : Nat). Nat`, which applied to `3` gives `5`.** -/
theorem adder_call (φ : Future) :
    ∃ F : (n : Nat) → NN × PUnit, closureL lvl0 φ tAdd (adderBody φ) = .el0 _ F ∧
      closureL lvl0 φ tAdd (adderBody φ) ∈ₛ piTyL lvl0 tAdd ∧
      applyFnL lvl0 tAdd (closureL lvl0 φ tAdd (adderBody φ)) [.el0 Nat 2]
        = some (.data (closureL lvl0 φ tNN (addBody 2)) (piTyL lvl0 tNN) []) ∧
      applyFnL lvl0 tNN (closureL lvl0 φ tNN (addBody 2)) [.el0 Nat 3] = some (.data (.el0 Nat 5) TyM.nat []) := by
  -- the leaf at each `n` decodes the inner closure at the codomain's code
  have hleaf : ∀ n, mkTelL lvl0 φ (Tel.dat PUnit NN (.pi NN tNN)) ([] ++ [lvl0.enc Code0.nat n])
      (extMkL false PUnit Nat (fun fs => some (PUnit.unit, fs)) (lvl0.dec Code0.nat)) (adderBody φ)
      = some (Classical.choose (inner_eq φ n), PUnit.unit) := by
    intro n
    rw [mkTelL.eq_1]
    have e := Classical.choose_spec (inner_eq φ n)
    have hb : adderBody φ ([] ++ [lvl0.enc Code0.nat n]) = some ⟨closureL lvl0 φ tNN (addBody n), [], none⟩ := by
      show adderBody φ [.el0 Nat n] = _
      simp only [adderBody, dec_nat, Option.map_some]
    rw [hb, Option.bind_some]
    have hd : (Code0.pi NN tNN).dec (closureL lvl0 φ tNN (addBody n)) = some (Classical.choose (inner_eq φ n)) := by
      conv => lhs; rw [e]
      exact Code0.dec_enc (Code0.pi NN tNN) _
    unfold mkLeafDataL
    simp only
    rw [hd]
    rfl
  have hall : ∀ n : Nat, (mkTelL lvl0 φ (Tel.dat PUnit NN (.pi NN tNN)) ([] ++ [lvl0.enc Code0.nat n])
      (extMkL false PUnit Nat (fun fs => some (PUnit.unit, fs)) (lvl0.dec Code0.nat)) (adderBody φ)).isSome := by
    intro n; rw [hleaf n]; rfl
  have hmk : mkTelL lvl0 φ tAdd [] (fun fs => some (PUnit.unit, fs)) (adderBody φ)
      = some fun n => (Classical.choose (inner_eq φ n), PUnit.unit) := by
    unfold tAdd
    rw [mkTelL.eq_3, dif_pos hall]
    congr 1
    funext n
    simp only [hleaf n, Option.get_some]
  have hc : closureL lvl0 φ tAdd (adderBody φ) = .el0 _ fun n => (Classical.choose (inner_eq φ n), PUnit.unit) := by
    unfold closureL; rw [hmk]; rfl
  refine ⟨_, hc, by rw [hc]; exact ⟨_, rfl⟩, ?_, ?_⟩
  · rw [hc]
    show (Sem.as _ (.el0 _ _)).bind (fun F => applyTelL lvl0 tAdd (fun _ => []) F [.el0 Nat 2]) = _
    rw [show Sem.as ((n : Nat) → NN × PUnit) (.el0 _ fun n => (Classical.choose (inner_eq φ n), PUnit.unit))
      = some fun n => (Classical.choose (inner_eq φ n), PUnit.unit) from lvl0_lawful.unpack_pack _ _, Option.bind_some]
    simp only [tAdd, applyTelL, lvl0, dec_nat]
    simp only [Option.some.injEq, AppResultL.data.injEq]
    exact ⟨(Classical.choose_spec (inner_eq φ 2)).symm, rfl, rfl⟩
  · exact apply_strict φ (addBody 2) (fun x => ⟨_, addBody_nat 2 x⟩) 3 5 (addBody_nat 2 3)

/-! ## A function taking a function parameter: `App (f : Π(x : Nat). Nat) (n : Nat) : Nat := f(n)`

The parameter's code is `tNN`'s, so the body calls `f` along it, for every element of the
carrier (every Lean function, not only closures). -/

def tApp : Tel lvl0.Code PUnit ((f : NN) → (n : Nat) → Nat × PUnit) :=
  .param PUnit false NN (.pi NN tNN) (fun _ => (n : Nat) → Nat × PUnit) fun _ =>
    .param PUnit false Nat .nat (fun _ => Nat × PUnit) fun _ => .dat PUnit Nat .nat

/-- The body: the call `f(n)`, along `f`'s parameter code. -/
noncomputable def appBody : List Sem → Option BodyOut
  | [f, x] => match applyFnL lvl0 tNN f [x] with
    | some (.data r _ _) => some ⟨r, [], none⟩
    | _ => none
  | _ => none

theorem apply_any (f : NN) (n : Nat) :
    applyFnL lvl0 tNN (.el0 NN f) [.el0 Nat n] = some (.data (.el0 Nat (f n).1) TyM.nat []) := by
  show (Sem.as NN (.el0 NN f)).bind (fun F => applyTelL lvl0 tNN (fun _ => []) F [.el0 Nat n]) = _
  rw [show Sem.as NN (.el0 NN f) = some f from lvl0_lawful.unpack_pack NN f, Option.bind_some]
  simp only [tNN, applyTelL, lvl0, dec_nat]
  rfl

/-- **`App` is a member of its type's code, and `App(λx. x + 1, 3)` is `4`.** -/
theorem app_call (φ : Future) :
    closureL lvl0 φ tApp appBody ∈ₛ piTyL lvl0 tApp ∧ closureL lvl0 φ tApp appBody ≠ .err ∧
      applyFnL lvl0 tApp (closureL lvl0 φ tApp appBody) [closureL lvl0 φ tNN (addBody 1), .el0 Nat 3]
        = some (.data (.el0 Nat 4) TyM.nat []) := by
  have hb : ∀ (f : NN) (n : Nat), appBody [.el0 NN f, .el0 Nat n] = some ⟨.el0 Nat (f n).1, [], none⟩ := by
    intro f n; simp only [appBody, apply_any]
  have hleaf : ∀ (f : NN) (n : Nat), mkTelL lvl0 φ (Tel.dat PUnit Nat .nat)
      ([] ++ [lvl0.enc (Code0.pi NN tNN) f] ++ [lvl0.enc Code0.nat n])
      (extMkL false PUnit Nat (extMkL false PUnit NN (fun fs => some (PUnit.unit, fs)) (lvl0.dec (Code0.pi NN tNN)))
        (lvl0.dec Code0.nat)) appBody = some (f n) := by
    intro f n
    rw [mkTelL.eq_1]
    show (appBody [.el0 NN f, .el0 Nat n]).bind _ = _
    rw [hb, Option.bind_some]
    simp [mkLeafDataL, extMkL, dec_nat]
  have hin : ∀ f : NN, (mkTelL lvl0 φ (Tel.param PUnit false Nat .nat (fun _ => Nat × PUnit) fun _ => .dat PUnit Nat .nat)
      ([] ++ [lvl0.enc (Code0.pi NN tNN) f])
      (extMkL false PUnit NN (fun fs => some (PUnit.unit, fs)) (lvl0.dec (Code0.pi NN tNN))) appBody) = some f := by
    intro f
    rw [mkTelL.eq_3, dif_pos fun n => by rw [hleaf f n]; rfl]
    congr 1
    funext n
    simp only [hleaf f n, Option.get_some]
  have hmk : mkTelL lvl0 φ tApp [] (fun fs => some (PUnit.unit, fs)) appBody = some fun f => f := by
    unfold tApp
    rw [mkTelL.eq_3, dif_pos fun f => by rw [hin f]; rfl]
    congr 1
    funext f
    simp only [hin f, Option.get_some]
  have hc : closureL lvl0 φ tApp appBody = .el0 ((f : NN) → (n : Nat) → Nat × PUnit) fun f => f := by
    unfold closureL; rw [hmk]
  obtain ⟨G, hG⟩ := inner_eq φ 1
  rw [hc]
  refine ⟨⟨_, rfl⟩, fun h => (by cases h), ?_⟩
  rw [hG]
  show (Sem.as ((f : NN) → (n : Nat) → Nat × PUnit) (.el0 _ fun f => f)).bind
    (fun F => applyTelL lvl0 tApp (fun _ => []) F [.el0 NN G, .el0 Nat 3]) = _
  rw [show Sem.as ((f : NN) → (n : Nat) → Nat × PUnit) (.el0 _ fun f => f) = some fun f => f
    from lvl0_lawful.unpack_pack _ _, Option.bind_some]
  have hdG : (Code0.pi NN tNN).dec (.el0 NN G) = some G := Code0.dec_enc (Code0.pi NN tNN) G
  simp only [tApp, applyTelL, lvl0, dec_nat]
  rw [hdG]
  -- `G` is the closure of `addBody 1`: at `3` it gives `4`
  have h3 := apply_strict φ (addBody 1) (fun x => ⟨_, addBody_nat 1 x⟩) 3 4 (addBody_nat 1 3)
  rw [hG] at h3
  rw [apply_any] at h3
  simp only [Option.some.injEq, AppResultL.data.injEq, Sem.el0.injEq, heq_eq_eq, true_and] at h3
  show some (AppResultL.data (Sem.el0 Nat (G 3).1) TyM.nat []) = _
  rw [h3.1]

/-! ## A polymorphic function at a function type: `let g = id(Nat → Nat, f); g(Z)`

`id (A : Type) (x : A) : A` is in `Type₁`: its first parameter ranges over the codes of `Type₀`
types (`univ1`), so the argument `Nat → Nat` keeps its code, and the result is typed at it. -/

abbrev Ty0 : Type 1 := (A : Type) × {c : Code0 A // c.level = some 1}

abbrev IdCar : Type 1 := (p : Ty0) → ULift.{1} p.1 → ULift.{1} p.1 × PUnit.{2}

def tId : Tel lvl1.Code PUnit.{2} IdCar :=
  .param PUnit.{2} false Ty0 .univ1 (fun p => ULift.{1} p.1 → ULift.{1} p.1 × PUnit.{2}) fun p =>
    .param PUnit.{2} false (ULift.{1} p.1) (.lift p.1 p.2.1) (fun _ => ULift.{1} p.1 × PUnit.{2}) fun _ =>
      .dat PUnit.{2} (ULift.{1} p.1) (.lift p.1 p.2.1)

/-- The identity's body: its second argument. -/
def idBody : List Sem → Option BodyOut
  | [_, x] => some ⟨x, [], none⟩
  | _ => none

/-- **`id` is a member of its type's code, and `id(Nat → Nat, f)` is `f` at the code of
`Nat → Nat`**: the call's result is typed at the argument's own code, so it can be called. -/
theorem id_call (φ : Future) (G : NN) :
    closureL lvl1 φ tId idBody ∈ₛ piTyL lvl1 tId ∧
      applyFnL lvl1 tId (closureL lvl1 φ tId idBody) [.ty (piTyL lvl0 tNN), .el0 NN G]
        = some (.data (.el0 NN G) (piTyL lvl0 tNN) []) ∧
      applyFnL lvl0 tNN (.el0 NN G) [.el0 Nat 0] = some (.data (.el0 Nat (G 0).1) TyM.nat []) := by
  have hleaf : ∀ (p : Ty0) (x : ULift.{1} p.1), mkTelL lvl1 φ (Tel.dat PUnit.{2} (ULift.{1} p.1) (.lift p.1 p.2.1))
      ([] ++ [lvl1.enc Code1.univ1 p] ++ [lvl1.enc (Code1.lift p.1 p.2.1) x])
      (extMkL false PUnit.{2} (ULift.{1} p.1)
        (extMkL false PUnit.{2} Ty0 (fun fs => some (PUnit.unit, fs)) (lvl1.dec Code1.univ1)) (lvl1.dec (Code1.lift p.1 p.2.1)))
      idBody = some (x, PUnit.unit) := by
    intro p x
    rw [mkTelL.eq_1]
    show (some ⟨lvl1.enc (Code1.lift p.1 p.2.1) x, [], none⟩ : Option BodyOut).bind _ = _
    rw [Option.bind_some]
    unfold mkLeafDataL
    simp only
    rw [show (Code1.lift p.1 p.2.1).dec ((Code1.lift p.1 p.2.1).enc x) = some x from Code1.dec_enc _ x]
    rfl
  have hin : ∀ p : Ty0, mkTelL lvl1 φ (Tel.param PUnit.{2} false (ULift.{1} p.1) (.lift p.1 p.2.1)
      (fun _ => ULift.{1} p.1 × PUnit.{2}) fun _ => .dat PUnit.{2} (ULift.{1} p.1) (.lift p.1 p.2.1))
      ([] ++ [lvl1.enc Code1.univ1 p])
      (extMkL false PUnit.{2} Ty0 (fun fs => some (PUnit.unit, fs)) (lvl1.dec Code1.univ1)) idBody
      = some fun x => (x, PUnit.unit) := by
    intro p
    rw [mkTelL.eq_3, dif_pos fun x => by rw [hleaf p x]; rfl]
    congr 1
    funext x
    simp only [hleaf p x, Option.get_some]
  have hmk : mkTelL lvl1 φ tId [] (fun fs => some (PUnit.unit, fs)) idBody = some fun _ x => (x, PUnit.unit) := by
    unfold tId
    rw [mkTelL.eq_3, dif_pos fun p => by rw [hin p]; rfl]
    congr 1
    funext p
    simp only [hin p, Option.get_some]
  have hc : closureL lvl1 φ tId idBody = .el1 IdCar fun _ x => (x, PUnit.unit) := by
    unfold closureL; rw [hmk]
  refine ⟨by rw [hc]; exact ⟨_, rfl⟩, ?_, apply_any G 0⟩
  rw [hc]
  show (Sem.as1 _ (.el1 _ _)).bind (fun F => applyTelL lvl1 tId (fun _ => []) F [.ty (piTyL lvl0 tNN), .el0 NN G]) = _
  rw [show Sem.as1 IdCar (.el1 _ fun _ x => (x, PUnit.unit))
    = some fun _ x => (x, PUnit.unit) from lvl1_lawful.unpack_pack _ _, Option.bind_some]
  have hA : Code1.univ1.dec (.ty (piTyL lvl0 tNN)) = some ⟨NN, ⟨Code0.pi NN tNN, rfl⟩⟩ :=
    Code1.dec_enc Code1.univ1 ⟨NN, ⟨Code0.pi NN tNN, rfl⟩⟩
  have hx : (Code1.lift NN (Code0.pi NN tNN)).dec (.el0 NN G) = some ⟨G⟩ :=
    Code1.dec_enc (Code1.lift NN (Code0.pi NN tNN)) ⟨G⟩
  simp only [tId, applyTelL, lvl1]
  rw [hA]
  simp only
  rw [hx]
  rfl

end Ochr.Meaning.Regress.CodeClosures
