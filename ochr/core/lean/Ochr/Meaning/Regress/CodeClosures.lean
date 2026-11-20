import Ochr.Meaning.Apply1
import Ochr.Meaning.ClosureStage

/-!
# Closures are members of their types' codes (docs/31 D59, D60; built, kernel-checked)

The concrete check the lead asked for before the re-proof: a recursive function, a function
returning a function, a function taking a function parameter, and a polymorphic function applied
to a function type, each built along its type's code exactly as the reference run's `.fix` clause
builds it (`telL`, `closureL`, and the recursion's stages at the weakened type), each a member of its
type's code, and each applied by `applyFnL` as a call applies it. The bodies are written as
functions on meanings (what the `.fix` clause's `bodyAt` computes for these terms); the terms'
own runs need a concrete instance of the decisions under `run` (docs/31, the open check per term
form) and are not run here.

Found on the way (docs/31 D60): with the stages' closures built strictly, as the `.fix` clause
did, every recursive closure meant `err` (`Old.closure_err`): a stage R is defined only below its
rank, the carrier holds total functions only, so every stage's closure was `err`, and so every
recursive call failed. D60 then filled each stage's closure where the stage was undefined; the
stages are now closures at a weakened function type instead (docs/34), and `double` is built that
way here.
-/

namespace Ochr.Meaning.Regress.CodeClosures
open Ochr Ochr.Meaning

variable {R : DataRead}

/-- `Π(n : Nat). Nat` at `Type₀`: its carrier, and its telescope code. -/
abbrev NN : Type := (n : Nat) → Nat × PUnit

def tNN : Tel Code0 PUnit NN := .param PUnit false Nat .nat (fun _ => Nat × PUnit) fun _ => .dat PUnit Nat .nat

/-- It is the code the reference run builds from the description (each domain and the codomain
`Nat`). -/
theorem tNN_telL : telL (lvl0 R) [⟨false, fun _ => TyM.nat⟩] [] PUnit ⟨false, fun _ => TyM.nat⟩ = ⟨NN, tNN⟩ := rfl

theorem dec_nat (n : Nat) : Code0.dec R .nat (.el0 Nat n) = some n := Code0.dec_enc R .nat n

/-- The element built along `tNN`, where the body gives a number at every number. -/
theorem mk_some (φ : Future) (g : List Sem → Option BodyOut)
    (hg : ∀ x, ∃ k, g [.el0 Nat x] = some ⟨.el0 Nat k, [], none⟩) :
    ∃ F, mkTelL (lvl0 R) φ tNN [] (fun fs => some (PUnit.unit, fs)) g = some F ∧
      ∀ x k, g [.el0 Nat x] = some ⟨.el0 Nat k, [], none⟩ → F x = (k, PUnit.unit) := by
  have hleaf : ∀ x k, g [.el0 Nat x] = some ⟨.el0 Nat k, [], none⟩ →
      (g ([] ++ [(lvl0 R).enc Code0.nat x])).bind (mkLeafDataL (lvl0 R) φ (extFin false PUnit Nat)
        (extMkL false PUnit Nat (fun fs => some (PUnit.unit, fs)) ((lvl0 R).dec Code0.nat)) Code0.nat)
        = some (k, PUnit.unit) := by
    intro x k h
    show (g [.el0 Nat x]).bind _ = _
    rw [h]
    simp [mkLeafDataL, extMkL, dec_nat]
  have hall : ∀ x : Nat, (mkTelL (lvl0 R) φ (Tel.dat PUnit Nat .nat) ([] ++ [(lvl0 R).enc Code0.nat x])
      (extMkL false PUnit Nat (fun fs => some (PUnit.unit, fs)) ((lvl0 R).dec Code0.nat)) g).isSome := by
    intro x
    obtain ⟨k, hk⟩ := hg x
    rw [mkTelL.eq_1, hleaf x k hk]; rfl
  refine ⟨fun x => (mkTelL (lvl0 R) φ (Tel.dat PUnit Nat .nat) ([] ++ [(lvl0 R).enc Code0.nat x])
      (extMkL false PUnit Nat (fun fs => some (PUnit.unit, fs)) ((lvl0 R).dec Code0.nat)) g).get (hall x), ?_, ?_⟩
  · unfold tNN
    rw [mkTelL.eq_3, dif_pos hall]
  · intro x k hk
    have e : mkTelL (lvl0 R) φ (Tel.dat PUnit Nat .nat) ([] ++ [(lvl0 R).enc Code0.nat x])
        (extMkL false PUnit Nat (fun fs => some (PUnit.unit, fs)) ((lvl0 R).dec Code0.nat)) g = some (k, PUnit.unit) := by
      rw [mkTelL.eq_1, hleaf x k hk]
    simp only [e, Option.get_some]

/-- A closure along `tNN` is `err` where its body is undefined at some number. -/
theorem closure_err (φ : Future) (g : List Sem → Option BodyOut) (x : Nat) (hx : g [.el0 Nat x] = none) :
    closureL (lvl0 R) φ tNN g = .err := by
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
theorem apply_err (args : List Sem) : applyFnL (lvl0 R) tNN .err args = none := rfl

/-- A closure along `tNN`, applied at `n` where its body gives `k`, gives `k`, at `Nat`. -/
theorem apply_strict (φ : Future) (g : List Sem → Option BodyOut) (hg : ∀ x, ∃ k, g [.el0 Nat x] = some ⟨.el0 Nat k, [], none⟩)
    (n k : Nat) (hn : g [.el0 Nat n] = some ⟨.el0 Nat k, [], none⟩) :
    applyFnL (lvl0 R) tNN (closureL (lvl0 R) φ tNN g) [.el0 Nat n] = some (.data (.el0 Nat k) TyM.nat []) := by
  obtain ⟨F, hF, hFx⟩ := mk_some φ g hg
  unfold closureL
  rw [hF]
  show (Sem.as NN (.el0 NN F)).bind (fun F => applyTelL (lvl0 R) tNN (fun _ => []) F [.el0 Nat n]) = _
  rw [show Sem.as NN (.el0 NN F) = some F from (lvl0_lawful R).unpack_pack NN F, Option.bind_some]
  simp only [tNN, applyTelL, lvl0, dec_nat, hFx n k hn]
  rfl

/-! ## A recursive function: `double (n : Nat) : Nat by n := match n { Z => Z, S m => S(S(double(m))) }`

The `.fix` clause's construction (docs/34), with `bodyAt self` written as the function on meanings
the body computes (`dblBody R`): stage `k + 1` binds `self` to stage `k`'s closure at the weakened
function type (`Nat` below rank `k`, `Unit` above, `selfAt`), and a call through `self` is
`callOf` at that type. -/

/-- `Π(n : Nat). Nat`'s description, as the `.fix` clause reads it. -/
def dsNN : List PiDom := [⟨false, fun _ => TyM.nat⟩]

def outNN : PiCod := ⟨false, fun _ => TyM.nat⟩

noncomputable def dblBody (R : DataRead) (self : Res) : List Sem → Option BodyOut
  | [x] => match Code0.dec R .nat x with
    | some 0 => some ⟨.el0 Nat 0, [], none⟩
    | some (m + 1) => match callOf R self [(.el0 Nat m, .plain TyM.nat)] (emptyState 0) with
      | some ((r, _), _) => (Code0.dec R .nat r).map fun k => ⟨.el0 Nat (k + 2), [], none⟩
      | none => none
    | none => none
  | _ => none

noncomputable def rankOf (R : DataRead) : List Sem → Nat
  | [x] => (Code0.dec R .nat x).getD 0
  | _ => 0

/-- Stage `k`'s closure, the `self` of stage `k + 1`, at the weakened function type. -/
noncomputable def selfAt (R : DataRead) (φ : Future) (k : Nat) (gk : List Sem → Option BodyOut) : Res :=
  (closureAt R 1 φ dsNN (weakCod 1 (rankOf R) k outNN) (stageFn 1 dsNN (rankOf R) k gk),
    .plain (piTyAt R 1 dsNN (weakCod 1 (rankOf R) k outNN)))

/-- The stages (the `.fix` clause's `stage`). -/
noncomputable def stage (R : DataRead) (φ : Future) (k : Nat) : List Sem → Option BodyOut :=
  Nat.rec (motive := fun _ => List Sem → Option BodyOut) (fun _ => none) (fun k gk => dblBody R (selfAt R φ k gk)) k

/-- The function at arguments of rank `r` is stage `r + 1` (the `.fix` clause's `g`). -/
noncomputable def gOf (R : DataRead) (φ : Future) : List Sem → Option BodyOut :=
  fun args => stage R φ (rankOf R args + 1) args

theorem rankOf_nat (n : Nat) : rankOf R [.el0 Nat n] = n := by simp [rankOf, dec_nat]

theorem natArgs_of_members {a : List Sem} (h : Steps.DomMembers R dsNN a) : ∃ n, a = [.el0 Nat n] := by
  obtain ⟨hl, hm⟩ := h
  match a, hl with
  | [x], _ =>
    obtain ⟨n, hn⟩ := hm 0 x _ rfl rfl
    exact ⟨n, by rw [← hn]; rfl⟩

theorem dblBody_zero (self : Res) : dblBody R self [.el0 Nat 0] = some ⟨.el0 Nat 0, [], none⟩ := by
  simp [dblBody, dec_nat]

theorem dblBody_succ (self : Res) (m : Nat) :
    dblBody R self [.el0 Nat (m + 1)] = match callOf R self [(.el0 Nat m, .plain TyM.nat)] (emptyState 0) with
      | some ((r, _), _) => (Code0.dec R .nat r).map fun k => ⟨.el0 Nat (k + 2), [], none⟩
      | none => none := by
  simp [dblBody, dec_nat]

/-- **A stage is good below its bound**: stage `n` doubles every `x < n` (the call at `m < x` reads
stage `n - 1`'s closure below its bound, `ClosureStage.stage_apply`). -/
theorem stage_val (φ : Future) : ∀ n x : Nat, x < n → stage R φ n [.el0 Nat x] = some ⟨.el0 Nat (2 * x), [], none⟩
  | 0, _, h => absurd h (Nat.not_lt_zero _)
  | n + 1, 0, _ => dblBody_zero _
  | n + 1, m + 1, h => by
    show dblBody R (selfAt R φ n (stage R φ n)) [.el0 Nat (m + 1)] = _
    have hgood : ∀ args, Steps.DomMembers R dsNN args → rankOf R args < n →
        ∃ o, stage R φ n args = some o ∧ Steps.OutGood R dsNN outNN args o ∧
          o.finals.length = (dsNN.filter (·.isRef)).length := by
      intro args ha hr
      obtain ⟨y, rfl⟩ := natArgs_of_members ha
      rw [rankOf_nat] at hr
      refine ⟨_, stage_val φ n y hr, ⟨⟨2 * y, rfl⟩, fun i d hd hr' => ?_⟩, rfl⟩
      rcases i with _ | i
      · simp only [dsNN, List.getElem?_cons_zero, Option.some.injEq] at hd
        subst hd; cases hr'
      · simp [dsNN] at hd
    have hmem : Steps.DomMembers R dsNN [Sem.el0 Nat m] := ⟨rfl, fun i a d ha hd => by
      rcases i with _ | i
      · simp only [List.getElem?_cons_zero, Option.some.injEq] at ha
        simp only [dsNN, List.getElem?_cons_zero, Option.some.injEq] at hd
        subst ha; subst hd; exact ⟨m, rfl⟩
      · simp at ha⟩
    obtain ⟨s', hs⟩ := stage_apply R 1 φ dsNN outNN (rankOf R) n (stage R φ n) ⟨Nat.le_refl 1, by omega⟩ rfl
      (fun _ _ _ => by simp [LevelFit, outNN, TyM.nat]) hgood [(.el0 Nat m, .plain TyM.nat)] (emptyState 0)
      ⟨.el0 Nat (2 * m), [], none⟩ hmem
      (fun i d hd => by
        rcases i with _ | i
        · simp only [dsNN, List.getElem?_cons_zero, Option.some.injEq] at hd
          subst hd; simp [LevelFit, TyM.nat]
        · simp [dsNN] at hd)
      (by show rankOf R [.el0 Nat m] < n; rw [rankOf_nat]; omega) trivial (stage_val φ n m (by omega))
    rw [dblBody_succ]
    unfold selfAt
    rw [hs]
    simp only [Option.map, dec_nat]
    rfl

namespace Old

/-- The body as it read `self` before the weakened stages: applied along the true code `tNN`. -/
noncomputable def dblBody (R : DataRead) (self : Sem) : List Sem → Option BodyOut
  | [x] => match Code0.dec R .nat x with
    | some 0 => some ⟨.el0 Nat 0, [], none⟩
    | some (m + 1) => match applyFnL (lvl0 R) tNN self [.el0 Nat m] with
      | some (.data r _ _) => (Code0.dec R .nat r).map fun k => ⟨.el0 Nat (k + 2), [], none⟩
      | _ => none
    | none => none
  | _ => none

noncomputable def stage (R : DataRead) (mk : (List Sem → Option BodyOut) → Sem) (k : Nat) : List Sem → Option BodyOut :=
  Nat.rec (motive := fun _ => List Sem → Option BodyOut) (fun _ => none) (fun _ gk => dblBody R (mk gk)) k

noncomputable def gOf (R : DataRead) (mk : (List Sem → Option BodyOut) → Sem) : List Sem → Option BodyOut :=
  fun args => stage R mk (rankOf R args + 1) args

theorem dblBody_succ (self : Sem) (m : Nat) :
    dblBody R self [.el0 Nat (m + 1)] = match applyFnL (lvl0 R) tNN self [.el0 Nat m] with
      | some (.data r _ _) => (Code0.dec R .nat r).map fun k => ⟨.el0 Nat (k + 2), [], none⟩
      | _ => none := by
  simp [dblBody, dec_nat]

/-- **As the `.fix` clause built it before D60, the recursive closure is `err`**: each stage's
closure was built strictly at the TRUE type, so it was `err` (a stage R is undefined above its
rank), and every recursive call through it failed. -/
theorem closure_err (φ : Future) : closureL (lvl0 R) φ tNN (gOf R (closureL (lvl0 R) φ tNN)) = .err := by
  have h0 : closureL (lvl0 R) φ tNN (stage R (closureL (lvl0 R) φ tNN) 0) = .err :=
    CodeClosures.closure_err φ _ 0 rfl
  have h1 : stage R (closureL (lvl0 R) φ tNN) 1 [.el0 Nat 1] = none := by
    show dblBody R (closureL (lvl0 R) φ tNN (stage R (closureL (lvl0 R) φ tNN) 0)) [.el0 Nat (0 + 1)] = none
    rw [dblBody_succ, h0, apply_err]
  have h1' : closureL (lvl0 R) φ tNN (stage R (closureL (lvl0 R) φ tNN) 1) = .err :=
    CodeClosures.closure_err φ _ 1 h1
  apply CodeClosures.closure_err φ _ 1
  show stage R (closureL (lvl0 R) φ tNN) (rankOf R [.el0 Nat 1] + 1) [.el0 Nat 1] = none
  rw [rankOf_nat]
  show dblBody R (closureL (lvl0 R) φ tNN (stage R (closureL (lvl0 R) φ tNN) 1)) [.el0 Nat (0 + 1)] = none
  rw [dblBody_succ, h1', apply_err]

end Old

/-- **The recursive closure is a member of its type's code**, and `double(3)` is `6`. -/
theorem double_member (φ : Future) :
    closureL (lvl0 R) φ tNN (gOf R φ) ∈ₛ[R] piTyL (lvl0 R) tNN ∧
      closureL (lvl0 R) φ tNN (gOf R φ) ≠ .err ∧
      applyFnL (lvl0 R) tNN (closureL (lvl0 R) φ tNN (gOf R φ)) [.el0 Nat 3]
        = some (.data (.el0 Nat 6) TyM.nat []) := by
  have hg : ∀ x, gOf R φ [.el0 Nat x] = some ⟨.el0 Nat (2 * x), [], none⟩ := by
    intro x
    show stage R φ (rankOf R [.el0 Nat x] + 1) [.el0 Nat x] = _
    rw [rankOf_nat]; exact stage_val φ (x + 1) x (Nat.lt_succ_self x)
  obtain ⟨F, hF, -⟩ := mk_some φ _ fun x => ⟨_, hg x⟩
  have hc : closureL (lvl0 R) φ tNN (gOf R φ) = .el0 NN F := by
    unfold closureL; rw [hF]
  refine ⟨?_, ?_, apply_strict φ _ (fun x => ⟨_, hg x⟩) 3 6 (hg 3)⟩
  · rw [hc]; exact ⟨F, rfl⟩
  · rw [hc]; exact fun h => by cases h

/-! ## A function returning a function: `Adder (n : Nat) : Π(m : Nat). Nat` (`UseAdder`)

Its codomain's code is `tNN`'s, so the call's result is typed at it and can be called. -/

/-- `Π(n : Nat). Π(m : Nat). Nat`: the codomain is a function type's code. -/
def tAdd : Tel Code0 PUnit ((n : Nat) → NN × PUnit) :=
  .param PUnit false Nat .nat (fun _ => NN × PUnit) fun _ => .dat PUnit NN (.pi NN tNN)

/-- The inner closure's body: `n + m`. -/
noncomputable def addBody (R : DataRead) (n : Nat) : List Sem → Option BodyOut
  | [x] => (Code0.dec R .nat x).map fun m => ⟨.el0 Nat (n + m), [], none⟩
  | _ => none

/-- The outer body returns the inner closure. -/
noncomputable def adderBody (R : DataRead) (φ : Future) : List Sem → Option BodyOut
  | [x] => (Code0.dec R .nat x).map fun n => ⟨closureL (lvl0 R) φ tNN (addBody R n), [], none⟩
  | _ => none

theorem addBody_nat (n m : Nat) : addBody R n [.el0 Nat m] = some ⟨.el0 Nat (n + m), [], none⟩ := by
  simp [addBody, dec_nat]

theorem inner_eq (φ : Future) (n : Nat) : ∃ F : NN, closureL (lvl0 R) φ tNN (addBody R n) = .el0 NN F := by
  obtain ⟨F, hF, -⟩ := mk_some φ (addBody R n) fun x => ⟨_, addBody_nat n x⟩
  exact ⟨F, by unfold closureL; rw [hF]⟩

/-- **`Adder` is a member of its type's code, and `Adder(2)` is a function typed at the code of
`Π(m : Nat). Nat`, which applied to `3` gives `5`.** -/
theorem adder_call (φ : Future) :
    ∃ F : (n : Nat) → NN × PUnit, closureL (lvl0 R) φ tAdd (adderBody R φ) = .el0 _ F ∧
      closureL (lvl0 R) φ tAdd (adderBody R φ) ∈ₛ[R] piTyL (lvl0 R) tAdd ∧
      applyFnL (lvl0 R) tAdd (closureL (lvl0 R) φ tAdd (adderBody R φ)) [.el0 Nat 2]
        = some (.data (closureL (lvl0 R) φ tNN (addBody R 2)) (piTyL (lvl0 R) tNN) []) ∧
      applyFnL (lvl0 R) tNN (closureL (lvl0 R) φ tNN (addBody R 2)) [.el0 Nat 3] = some (.data (.el0 Nat 5) TyM.nat []) := by
  -- the leaf at each `n` decodes the inner closure at the codomain's code
  have hleaf : ∀ n, mkTelL (lvl0 R) φ (Tel.dat PUnit NN (.pi NN tNN)) ([] ++ [(lvl0 R).enc Code0.nat n])
      (extMkL false PUnit Nat (fun fs => some (PUnit.unit, fs)) ((lvl0 R).dec Code0.nat)) (adderBody R φ)
      = some (Classical.choose (inner_eq (R := R) φ n), PUnit.unit) := by
    intro n
    rw [mkTelL.eq_1]
    have e := Classical.choose_spec (inner_eq (R := R) φ n)
    have hb : adderBody R φ ([] ++ [(lvl0 R).enc Code0.nat n]) = some ⟨closureL (lvl0 R) φ tNN (addBody R n), [], none⟩ := by
      show adderBody R φ [.el0 Nat n] = _
      simp only [adderBody, dec_nat, Option.map_some]
    rw [hb, Option.bind_some]
    have hd : (Code0.pi NN tNN).dec R (closureL (lvl0 R) φ tNN (addBody R n)) = some (Classical.choose (inner_eq (R := R) φ n)) := by
      conv => lhs; rw [e]
      exact Code0.dec_enc R (Code0.pi NN tNN) _
    unfold mkLeafDataL
    simp only
    rw [hd]
    rfl
  have hall : ∀ n : Nat, (mkTelL (lvl0 R) φ (Tel.dat PUnit NN (.pi NN tNN)) ([] ++ [(lvl0 R).enc Code0.nat n])
      (extMkL false PUnit Nat (fun fs => some (PUnit.unit, fs)) ((lvl0 R).dec Code0.nat)) (adderBody R φ)).isSome := by
    intro n; rw [hleaf n]; rfl
  have hmk : mkTelL (lvl0 R) φ tAdd [] (fun fs => some (PUnit.unit, fs)) (adderBody R φ)
      = some fun n => (Classical.choose (inner_eq (R := R) φ n), PUnit.unit) := by
    unfold tAdd
    rw [mkTelL.eq_3, dif_pos hall]
    congr 1
    funext n
    simp only [hleaf n, Option.get_some]
  have hc : closureL (lvl0 R) φ tAdd (adderBody R φ) = .el0 _ fun n => (Classical.choose (inner_eq (R := R) φ n), PUnit.unit) := by
    unfold closureL; rw [hmk]; rfl
  refine ⟨_, hc, by rw [hc]; exact ⟨_, rfl⟩, ?_, ?_⟩
  · rw [hc]
    show (Sem.as _ (.el0 _ _)).bind (fun F => applyTelL (lvl0 R) tAdd (fun _ => []) F [.el0 Nat 2]) = _
    rw [show Sem.as ((n : Nat) → NN × PUnit) (.el0 _ fun n => (Classical.choose (inner_eq (R := R) φ n), PUnit.unit))
      = some fun n => (Classical.choose (inner_eq (R := R) φ n), PUnit.unit) from (lvl0_lawful R).unpack_pack _ _, Option.bind_some]
    simp only [tAdd, applyTelL, lvl0, dec_nat]
    simp only [Option.some.injEq, AppResultL.data.injEq]
    exact ⟨(Classical.choose_spec (inner_eq φ 2)).symm, rfl, rfl⟩
  · exact apply_strict φ (addBody R 2) (fun x => ⟨_, addBody_nat 2 x⟩) 3 5 (addBody_nat 2 3)

/-! ## A function taking a function parameter: `App (f : Π(x : Nat). Nat) (n : Nat) : Nat := f(n)`

The parameter's code is `tNN`'s, so the body calls `f` along it, for every element of the
carrier (every Lean function, not only closures). -/

def tApp : Tel Code0 PUnit ((f : NN) → (n : Nat) → Nat × PUnit) :=
  .param PUnit false NN (.pi NN tNN) (fun _ => (n : Nat) → Nat × PUnit) fun _ =>
    .param PUnit false Nat .nat (fun _ => Nat × PUnit) fun _ => .dat PUnit Nat .nat

/-- The body: the call `f(n)`, along `f`'s parameter code. -/
noncomputable def appBody (R : DataRead) : List Sem → Option BodyOut
  | [f, x] => match applyFnL (lvl0 R) tNN f [x] with
    | some (.data r _ _) => some ⟨r, [], none⟩
    | _ => none
  | _ => none

theorem apply_any (f : NN) (n : Nat) :
    applyFnL (lvl0 R) tNN (.el0 NN f) [.el0 Nat n] = some (.data (.el0 Nat (f n).1) TyM.nat []) := by
  show (Sem.as NN (.el0 NN f)).bind (fun F => applyTelL (lvl0 R) tNN (fun _ => []) F [.el0 Nat n]) = _
  rw [show Sem.as NN (.el0 NN f) = some f from (lvl0_lawful R).unpack_pack NN f, Option.bind_some]
  simp only [tNN, applyTelL, lvl0, dec_nat]
  rfl

/-- **`App` is a member of its type's code, and `App(λx. x + 1, 3)` is `4`.** -/
theorem app_call (φ : Future) :
    closureL (lvl0 R) φ tApp (appBody R) ∈ₛ[R] piTyL (lvl0 R) tApp ∧ closureL (lvl0 R) φ tApp (appBody R) ≠ .err ∧
      applyFnL (lvl0 R) tApp (closureL (lvl0 R) φ tApp (appBody R)) [closureL (lvl0 R) φ tNN (addBody R 1), .el0 Nat 3]
        = some (.data (.el0 Nat 4) TyM.nat []) := by
  have hb : ∀ (f : NN) (n : Nat), (appBody R) [.el0 NN f, .el0 Nat n] = some ⟨.el0 Nat (f n).1, [], none⟩ := by
    intro f n; simp only [appBody, apply_any]
  have hleaf : ∀ (f : NN) (n : Nat), mkTelL (lvl0 R) φ (Tel.dat PUnit Nat .nat)
      ([] ++ [(lvl0 R).enc (Code0.pi NN tNN) f] ++ [(lvl0 R).enc Code0.nat n])
      (extMkL false PUnit Nat (extMkL false PUnit NN (fun fs => some (PUnit.unit, fs)) ((lvl0 R).dec (Code0.pi NN tNN)))
        ((lvl0 R).dec Code0.nat)) (appBody R) = some (f n) := by
    intro f n
    rw [mkTelL.eq_1]
    show ((appBody R) [.el0 NN f, .el0 Nat n]).bind _ = _
    rw [hb, Option.bind_some]
    simp [mkLeafDataL, extMkL, dec_nat]
  have hin : ∀ f : NN, (mkTelL (lvl0 R) φ (Tel.param PUnit false Nat .nat (fun _ => Nat × PUnit) fun _ => .dat PUnit Nat .nat)
      ([] ++ [(lvl0 R).enc (Code0.pi NN tNN) f])
      (extMkL false PUnit NN (fun fs => some (PUnit.unit, fs)) ((lvl0 R).dec (Code0.pi NN tNN))) (appBody R)) = some f := by
    intro f
    rw [mkTelL.eq_3, dif_pos fun n => by rw [hleaf f n]; rfl]
    congr 1
    funext n
    simp only [hleaf f n, Option.get_some]
  have hmk : mkTelL (lvl0 R) φ tApp [] (fun fs => some (PUnit.unit, fs)) (appBody R) = some fun f => f := by
    unfold tApp
    rw [mkTelL.eq_3, dif_pos fun f => by rw [hin f]; rfl]
    congr 1
    funext f
    simp only [hin f, Option.get_some]
  have hc : closureL (lvl0 R) φ tApp (appBody R) = .el0 ((f : NN) → (n : Nat) → Nat × PUnit) fun f => f := by
    unfold closureL; rw [hmk]
  obtain ⟨G, hG⟩ := inner_eq φ 1
  rw [hc]
  refine ⟨⟨_, rfl⟩, fun h => (by cases h), ?_⟩
  rw [hG]
  show (Sem.as ((f : NN) → (n : Nat) → Nat × PUnit) (.el0 _ fun f => f)).bind
    (fun F => applyTelL (lvl0 R) tApp (fun _ => []) F [.el0 NN G, .el0 Nat 3]) = _
  rw [show Sem.as ((f : NN) → (n : Nat) → Nat × PUnit) (.el0 _ fun f => f) = some fun f => f
    from (lvl0_lawful R).unpack_pack _ _, Option.bind_some]
  have hdG : (Code0.pi NN tNN).dec R (.el0 NN G) = some G := Code0.dec_enc R (Code0.pi NN tNN) G
  simp only [tApp, applyTelL, lvl0, dec_nat]
  rw [hdG]
  -- `G` is the closure of `addBody R 1`: at `3` it gives `4`
  have h3 := apply_strict (R := R) φ (addBody R 1) (fun x => ⟨_, addBody_nat 1 x⟩) 3 4 (addBody_nat 1 3)
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

def tId : Tel Code1 PUnit.{2} IdCar :=
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
    closureL (lvl1 R) φ tId idBody ∈ₛ[R] piTyL (lvl1 R) tId ∧
      applyFnL (lvl1 R) tId (closureL (lvl1 R) φ tId idBody) [.ty (piTyL (lvl0 R) tNN), .el0 NN G]
        = some (.data (.el0 NN G) (piTyL (lvl0 R) tNN) []) ∧
      applyFnL (lvl0 R) tNN (.el0 NN G) [.el0 Nat 0] = some (.data (.el0 Nat (G 0).1) TyM.nat []) := by
  have hleaf : ∀ (p : Ty0) (x : ULift.{1} p.1), mkTelL (lvl1 R) φ (Tel.dat PUnit.{2} (ULift.{1} p.1) (.lift p.1 p.2.1))
      ([] ++ [(lvl1 R).enc Code1.univ1 p] ++ [(lvl1 R).enc (Code1.lift p.1 p.2.1) x])
      (extMkL false PUnit.{2} (ULift.{1} p.1)
        (extMkL false PUnit.{2} Ty0 (fun fs => some (PUnit.unit, fs)) ((lvl1 R).dec Code1.univ1)) ((lvl1 R).dec (Code1.lift p.1 p.2.1)))
      idBody = some (x, PUnit.unit) := by
    intro p x
    rw [mkTelL.eq_1]
    show (some ⟨(lvl1 R).enc (Code1.lift p.1 p.2.1) x, [], none⟩ : Option BodyOut).bind _ = _
    rw [Option.bind_some]
    unfold mkLeafDataL
    simp only
    rw [show (Code1.lift p.1 p.2.1).dec R ((Code1.lift p.1 p.2.1).enc R x) = some x from Code1.dec_enc R _ x]
    rfl
  have hin : ∀ p : Ty0, mkTelL (lvl1 R) φ (Tel.param PUnit.{2} false (ULift.{1} p.1) (.lift p.1 p.2.1)
      (fun _ => ULift.{1} p.1 × PUnit.{2}) fun _ => .dat PUnit.{2} (ULift.{1} p.1) (.lift p.1 p.2.1))
      ([] ++ [(lvl1 R).enc Code1.univ1 p])
      (extMkL false PUnit.{2} Ty0 (fun fs => some (PUnit.unit, fs)) ((lvl1 R).dec Code1.univ1)) idBody
      = some fun x => (x, PUnit.unit) := by
    intro p
    rw [mkTelL.eq_3, dif_pos fun x => by rw [hleaf p x]; rfl]
    congr 1
    funext x
    simp only [hleaf p x, Option.get_some]
  have hmk : mkTelL (lvl1 R) φ tId [] (fun fs => some (PUnit.unit, fs)) idBody = some fun _ x => (x, PUnit.unit) := by
    unfold tId
    rw [mkTelL.eq_3, dif_pos fun p => by rw [hin p]; rfl]
    congr 1
    funext p
    simp only [hin p, Option.get_some]
  have hc : closureL (lvl1 R) φ tId idBody = .el1 IdCar fun _ x => (x, PUnit.unit) := by
    unfold closureL; rw [hmk]
  refine ⟨by rw [hc]; exact ⟨_, rfl⟩, ?_, apply_any G 0⟩
  rw [hc]
  show (Sem.as1 _ (.el1 _ _)).bind (fun F => applyTelL (lvl1 R) tId (fun _ => []) F [.ty (piTyL (lvl0 R) tNN), .el0 NN G]) = _
  rw [show Sem.as1 IdCar (.el1 _ fun _ x => (x, PUnit.unit))
    = some fun _ x => (x, PUnit.unit) from (lvl1_lawful R).unpack_pack _ _, Option.bind_some]
  have hA : Code1.univ1.dec R (.ty (piTyL (lvl0 R) tNN)) = some ⟨NN, ⟨Code0.pi NN tNN, rfl⟩⟩ :=
    Code1.dec_enc R Code1.univ1 ⟨NN, ⟨Code0.pi NN tNN, rfl⟩⟩
  have hx : (Code1.lift NN (Code0.pi NN tNN)).dec R (.el0 NN G) = some ⟨G⟩ :=
    Code1.dec_enc R (Code1.lift NN (Code0.pi NN tNN)) ⟨G⟩
  simp only [tId, applyTelL, lvl1]
  rw [hA]
  simp only
  rw [hx]
  rfl

end Ochr.Meaning.Regress.CodeClosures
