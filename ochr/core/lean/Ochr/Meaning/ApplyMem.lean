import Ochr.Meaning.Closure

/-!
# Function application lands in the result type (Π-elimination in the model; the lead's `app_mem`)

A member of a function type's code is an element of the code's carrier (the type's meaning is
`L.toTy (L.pi C t)`, whose members are the packed elements), whatever built it: a closure the
`.fix` clause made, an unknown's assigned element, a global. Applied along the code (`applyFnL`, as a
call reads it, `callOf`) at arguments that reach the codomain (`codAt?`: each decodes at its
parameter's code, as many as there are parameters), it gives the element's result, ENCODED at the
codomain's code, so a member of the codomain; the borrow parameters' final contents are encoded at
their parameters' codes, so members of their content types.

* `applyTelL_mem`: along a telescope, at any level.
* `app_mem`: the lead's statement (`Steps/EvalMem.lean` on `spine-lead`), at a data codomain; its
  hypothesis `hargs` is not needed (reaching the codomain already decodes every argument).
* `app_mem_ref`: the same at a returned borrow (the forward value a member of the content type).
* `app_mem_finals`: the borrow parameters' final contents, at the application.
* `unit_mem_eq`, `app_mem_unit`: `Unit` has one member, so a result at `Unit` is `()` (η at `Unit`).
-/

namespace Ochr.Meaning

open Ochr Ochr.Meaning.Steps

universe u

/-- **A level encodes into its codes' types**: an encoded element is a member of the code read as a
type. -/
def Lvl.EncMem (L : Lvl.{u}) : Prop :=
  ∀ {A : Type u} (c : L.Code A) (x : A), L.enc c x ∈ₛ[L.read] L.toTy c

theorem lvl0_encMem (R : DataRead) : (lvl0 R).EncMem := fun _ x => ⟨x, rfl⟩

theorem lvl1_encMem (R : DataRead) : (lvl1 R).EncMem := by
  intro A c x
  cases c with
  | lift B c => exact ⟨x.down, rfl⟩
  | univ0 => exact ⟨x, rfl⟩
  | univ1 => exact ⟨x, rfl⟩
  | pi C t => exact ⟨x, rfl⟩

theorem lvl2_encMem (R : DataRead) : (lvl2 R).EncMem := by
  intro A c x
  cases c with
  | lift B c =>
    cases c with
    | lift B' c' => exact ⟨x.down.down, rfl⟩
    | univ0 => exact ⟨x.down, rfl⟩
    | univ1 => exact ⟨x.down, rfl⟩
    | pi C t => exact ⟨x.down, rfl⟩
  | univ2 => exact ⟨x, rfl⟩
  | pi C t => exact ⟨x, rfl⟩

/-- Meanings, each a member of its type, in order. -/
inductive MemList (R : DataRead) : List Sem → List TyM → Prop
  | nil : MemList R [] []
  | cons {f : Sem} {T : TyM} {fs : List Sem} {Ts : List TyM} : f ∈ₛ[R] T → MemList R fs Ts →
      MemList R (f :: fs) (T :: Ts)

theorem MemList.append {R : DataRead} : ∀ {fs Ts gs Us}, MemList R fs Ts → MemList R gs Us →
    MemList R (fs ++ gs) (Ts ++ Us)
  | _, _, _, _, .nil, h => h
  | _, _, _, _, .cons hf hs, h => .cons hf (MemList.append hs h)

section
variable (L : Lvl.{u})

/-- The content types of the borrow parameters a telescope code reaches at the arguments, in order
(`[]` past an argument that does not decode). -/
noncomputable def telRefTysL : {Fin C : Type u} → Tel L.Code Fin C → List Sem → List TyM
  | _, _, .param _ isRef _ c _ k, a :: as =>
    match L.dec c a with
    | some x => (if isRef then [L.toTy c] else []) ++ telRefTysL (k x) as
    | none => []
  | _, _, _, _ => []

/-- **Application along a telescope lands in the codomain**: where the arguments reach a data
codomain `B` (`telCodL`), applying any element gives a result that is a member of `B`, and final
contents that are members of the borrow parameters' content types (those `readFin` already holds,
then those the arguments reach). -/
theorem applyTelL_mem (hE : L.EncMem) :
    ∀ {Fin C : Type u} (t : Tel L.Code Fin C) (readFin : Fin → List Sem) (tys : List TyM)
      (hread : ∀ fin, MemList L.read (readFin fin) tys)
      (F : C) (args : List Sem) (B : TyM), telCodL L t args = some (false, B) →
      ∃ r fins, applyTelL L t readFin F args = some (.data r B fins) ∧ r ∈ₛ[L.read] B ∧
        MemList L.read fins (tys ++ telRefTysL L t args)
  | _, _, .dat Fin B' c, readFin, tys, hread, F, [], B, h => by
    simp only [telCodL, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨-, rfl⟩ := h
    refine ⟨_, _, rfl, hE c F.1, ?_⟩
    simpa [telRefTysL] using hread F.2
  | _, _, .ref Fin U c, readFin, tys, hread, F, [], B, h => by
    simp [telCodL] at h
  | _, _, .param Fin isRef A c C' k, readFin, tys, hread, F, a :: as, B, h => by
    simp only [telCodL] at h
    cases hx : L.dec c a with
    | none => rw [hx] at h; cases h
    | some x =>
      rw [hx] at h
      dsimp only at h
      have hread' : ∀ fin, MemList L.read
          (extReadL isRef Fin A readFin (L.enc c) fin) (tys ++ if isRef then [L.toTy c] else []) := by
        intro fin
        cases isRef with
        | false => simpa [extReadL] using hread fin
        | true =>
          simp only [extReadL, if_true]
          exact MemList.append (hread fin.1) (.cons (hE c fin.2) .nil)
      obtain ⟨r, fins, hap, hr, hfins⟩ := applyTelL_mem hE (k x) _ _ hread' (F x) as B h
      refine ⟨r, fins, ?_, hr, ?_⟩
      · simp only [applyTelL, hx]; exact hap
      · simp only [telRefTysL, hx]
        simpa [List.append_assoc] using hfins
  | _, _, .dat .., _, _, _, _, _ :: _, _, h => by simp [telCodL] at h
  | _, _, .ref .., _, _, _, _, _ :: _, _, h => by simp [telCodL] at h
  | _, _, .param .., _, _, _, _, [], _, h => by simp [telCodL] at h

end

section
variable (L : Lvl.{u})

/-- Where the arguments reach a returned borrow `&U`, application gives a borrow at a code whose type
is `U`. -/
theorem applyTelL_ref :
    ∀ {Fin C : Type u} (t : Tel L.Code Fin C) (readFin : Fin → List Sem) (F : C) (args : List Sem) (U : TyM),
      telCodL L t args = some (true, U) →
      ∃ (U' : Type u) (c : L.Code U') (fwd : U') (back : U' → List Sem),
        applyTelL L t readFin F args = some (.ref U' c fwd back) ∧ L.toTy c = U
  | _, _, .dat .., _, _, [], U, h => by simp [telCodL] at h
  | _, _, .ref Fin U' c, readFin, F, [], U, h => by
    simp only [telCodL, Option.some.injEq, Prod.mk.injEq] at h
    exact ⟨_, c, _, _, rfl, h.2⟩
  | _, _, .param Fin isRef A c C' k, readFin, F, a :: as, U, h => by
    simp only [telCodL] at h
    cases hx : L.dec c a with
    | none => rw [hx] at h; cases h
    | some x =>
      rw [hx] at h
      obtain ⟨U', c', fwd, back, hap, hU⟩ := applyTelL_ref (k x) _ (F x) as U h
      exact ⟨U', c', fwd, back, by simp only [applyTelL, hx]; exact hap, hU⟩
  | _, _, .dat .., _, _, _ :: _, _, h => by simp [telCodL] at h
  | _, _, .ref .., _, _, _ :: _, _, h => by simp [telCodL] at h
  | _, _, .param .., _, _, [], _, h => by simp [telCodL] at h

/-- **A member of a function type, applied where the arguments reach a data codomain `B`**, gives a
member of `B` and final contents that are members of the borrow parameters' content types (what
`callOfL` fixes the borrow arguments' labels to). -/
theorem app_mem_finals (hL : L.Lawful) (hE : L.EncMem) {C : Type u} (t : Tel L.Code PUnit C) (fv : Sem)
    (hf : fv ∈ₛ[L.read] L.toTy (L.pi C t)) (args : List Sem) (B : TyM)
    (hcod : telCodL L t args = some (false, B)) :
    ∃ r fins, applyFnL L t fv args = some (.data r B fins) ∧ r ∈ₛ[L.read] B ∧
      MemList L.read fins (telRefTysL L t args) := by
  obtain ⟨F, hF⟩ := (hL.mem_pi C t fv).1 hf
  rw [hL.enc_pi] at hF
  subst hF
  obtain ⟨r, fins, hap, hr, hfins⟩ := applyTelL_mem L hE t (fun _ => []) [] (fun _ => .nil) F args B hcod
  refine ⟨r, fins, ?_, hr, by simpa using hfins⟩
  unfold applyFnL
  rw [hL.unpack_pack, Option.bind_some]
  exact hap

/-- The call (`callOfL`): the result is a member of `B`, typed at `B`. -/
theorem callOfL_mem (hL : L.Lawful) (hE : L.EncMem) {C : Type u} (t : Tel L.Code PUnit C) (fv : Sem)
    (hf : fv ∈ₛ[L.read] L.toTy (L.pi C t)) (args : List Res) (s : SState) (B : TyM)
    (hcod : telCodL L t (args.map (·.1)) = some (false, B)) :
    ∃ r s', callOfL L t fv args s = some (r, s') ∧ r.1 ∈ₛ[L.read] B ∧ r.2 = .plain B := by
  obtain ⟨r, fins, hap, hr, -⟩ := app_mem_finals L hL hE t fv hf _ B hcod
  unfold callOfL
  simp only [hap]
  exact ⟨_, _, rfl, hr, rfl⟩

/-- The call at a returned borrow `&U`: the result (the forward value) is a member of `U`, typed at
`U` under a fresh label. -/
theorem callOfL_mem_ref (hL : L.Lawful) (hE : L.EncMem) {C : Type u} (t : Tel L.Code PUnit C) (fv : Sem)
    (hf : fv ∈ₛ[L.read] L.toTy (L.pi C t)) (args : List Res) (s : SState) (U : TyM)
    (hcod : telCodL L t (args.map (·.1)) = some (true, U)) :
    ∃ r s', callOfL L t fv args s = some (r, s') ∧ r.1 ∈ₛ[L.read] U ∧ r.2.m = U := by
  obtain ⟨F, hF⟩ := (hL.mem_pi C t fv).1 hf
  rw [hL.enc_pi] at hF
  subst hF
  obtain ⟨U', c, fwd, back, hap, hU⟩ := applyTelL_ref L t (fun _ => []) F _ U hcod
  have happ : applyFnL L t (L.pack C F) (args.map (·.1)) = some (.ref U' c fwd back) := by
    unfold applyFnL
    rw [hL.unpack_pack, Option.bind_some]
    exact hap
  unfold callOfL
  simp only [happ]
  exact ⟨_, _, rfl, hU ▸ hE c fwd, hU⟩

end

/-! ## At a function type's meaning, as a call reads it -/

/-- **Π-elimination, as a call reads it** (the lead's `app_mem` without its `hargs`, which reaching
the codomain implies): a member of a function type, applied where the arguments reach a data
codomain `B`, gives a member of `B`, typed at `B`. Any member: a closure, an unknown's element, a
global. -/
theorem app_mem' (R : DataRead) (f : Res) (args : List Res) (s : SState) (B : TyM)
    (hf : f.1 ∈ₛ[R] f.2.m) (hcod : f.2.m.codAt? R (args.map (·.1)) = some (false, B)) :
    ∃ r s', callOf R f args s = some (r, s') ∧ r.1 ∈ₛ[R] B ∧ r.2 = .plain B := by
  rcases f with ⟨fv, ⟨T, lab⟩⟩
  cases T with
  | t0 A c =>
    cases c with
    | pi C t => exact callOfL_mem (lvl0 R) (lvl0_lawful R) (lvl0_encMem R) t fv hf args s B hcod
    | _ => simp [TyM.codAt?] at hcod
  | t1 A c =>
    cases c with
    | pi C t => exact callOfL_mem (lvl1 R) (lvl1_lawful R) (lvl1_encMem R) t fv hf args s B hcod
    | _ => simp [TyM.codAt?] at hcod
  | t2 A c =>
    cases c with
    | pi C t => exact callOfL_mem (lvl2 R) (lvl2_lawful R) (lvl2_encMem R) t fv hf args s B hcod
    | _ => simp [TyM.codAt?] at hcod

/-- **The lead's statement** (`Steps/EvalMem.app_mem` on `spine-lead`), proved. -/
theorem app_mem (R : DataRead) (f : Res) (args : List Res) (s : SState) (B : TyM)
    (hf : f.1 ∈ₛ[R] f.2.m) (_hargs : ArgsMember R f.2.m args)
    (hcod : f.2.m.codAt? R (args.map (·.1)) = some (false, B)) :
    ∃ r s', callOf R f args s = some (r, s') ∧ r.1 ∈ₛ[R] B := by
  obtain ⟨r, s', h, hr, -⟩ := app_mem' R f args s B hf hcod
  exact ⟨r, s', h, hr⟩

/-- **At a returned borrow `&U`**: the call's result is a member of `U`, typed at `U`. -/
theorem app_mem_ref (R : DataRead) (f : Res) (args : List Res) (s : SState) (U : TyM)
    (hf : f.1 ∈ₛ[R] f.2.m) (hcod : f.2.m.codAt? R (args.map (·.1)) = some (true, U)) :
    ∃ r s', callOf R f args s = some (r, s') ∧ r.1 ∈ₛ[R] U ∧ r.2.m = U := by
  rcases f with ⟨fv, ⟨T, lab⟩⟩
  cases T with
  | t0 A c =>
    cases c with
    | pi C t => exact callOfL_mem_ref (lvl0 R) (lvl0_lawful R) (lvl0_encMem R) t fv hf args s U hcod
    | _ => simp [TyM.codAt?] at hcod
  | t1 A c =>
    cases c with
    | pi C t => exact callOfL_mem_ref (lvl1 R) (lvl1_lawful R) (lvl1_encMem R) t fv hf args s U hcod
    | _ => simp [TyM.codAt?] at hcod
  | t2 A c =>
    cases c with
    | pi C t => exact callOfL_mem_ref (lvl2 R) (lvl2_lawful R) (lvl2_encMem R) t fv hf args s U hcod
    | _ => simp [TyM.codAt?] at hcod

/-- `Unit` has one member, `()`. -/
theorem unit_mem_eq (R : DataRead) (s : Sem) (h : s ∈ₛ[R] TyM.unit) : s = .el0 Unit () := by
  obtain ⟨⟨⟩, rfl⟩ := h
  rfl

/-- **η at `Unit` on a call's result**: where the arguments reach the codomain `Unit`, the call's
result is `()` (so η at `Unit` is the identity on it). -/
theorem app_mem_unit (R : DataRead) (f : Res) (args : List Res) (s : SState)
    (hf : f.1 ∈ₛ[R] f.2.m) (hcod : f.2.m.codAt? R (args.map (·.1)) = some (false, TyM.unit)) :
    ∃ r s', callOf R f args s = some (r, s') ∧ r.1 = .el0 Unit () ∧ r.2 = .plain TyM.unit := by
  obtain ⟨r, s', h, hr, hT⟩ := app_mem' R f args s TyM.unit hf hcod
  exact ⟨r, s', h, unit_mem_eq R _ hr, hT⟩

end Ochr.Meaning
