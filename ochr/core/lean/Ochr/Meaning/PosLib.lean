import Ochr.Meaning.Steps.Statements

/-!
# The position library: the checker's state operations as the step lemmas see them

Every prover meets the same three things (the pilot's finding, docs/31 item 5): the checker's
primitive state operations as runs (`Runs (setAt p v) st fuel () st'` fixes `st'`), the
environment's positions and values after them, and the bridge from a checker state to the
semantic state it means (`MState.sstate`, `MState.mean`). This file collects them.

* Part A: `Runs` of the primitives (`modify`, `setAt`, `pushTemp`, `pushBind`, `modifyFrame`), each
  the one state it reaches, by `rfl` on `runMachine`; determinism (`Runs.unique`).
* Part B: the environment after them (`allPos`, `valAt`, `Env.mean`, `Env.shape`, `Env.hintAt`).
* Part C: the bridge (`sstate`'s `valAt`, `tyAt`, `shape`, `positions` against `Env.mean`,
  `Env.hintAt`, `Env.shape`, `allPos`).
-/

namespace Ochr.Meaning.Steps

open Ochr

/-! ## Part A: runs of the primitives -/

/-- A run is deterministic: `runMachine` is a function. -/
theorem Runs.unique {α : Type} {x : M α} {st : MState} {fuel : Nat} {a b : α} {st' st'' : MState}
    (h₁ : Runs x st fuel a st') (h₂ : Runs x st fuel b st'') : a = b ∧ st' = st'' := by
  obtain ⟨l₁, g₁, e₁⟩ := h₁
  obtain ⟨l₂, g₂, e₂⟩ := h₂
  rw [e₁] at e₂
  simp only [Prod.mk.injEq] at e₂
  cases e₂.1
  exact ⟨rfl, rfl⟩

theorem runs_modify (g : MState → MState) (st : MState) (fuel : Nat) :
    Runs (modify g : M Unit) st fuel () (g st) := ⟨fuel, #[], rfl⟩

theorem runs_modifyFrame (f : Nat) (g : Frame → Frame) (st : MState) (fuel : Nat) :
    Runs (Ochr.modifyFrame f g) st fuel () { st with env := st.env.modify f g } := ⟨fuel, #[], rfl⟩

/-- The environment after `setAt`. -/
def Env.setAtE (env : Env) : Pos → Value → Env
  | .bind f i, v => env.modify f fun fr => { fr with binds := fr.binds.modify i ({ · with val := v }) }
  | .temp f i, v => env.modify f fun fr => { fr with temps := fr.temps.set! i v }

theorem runs_setAt (p : Pos) (v : Value) (st : MState) (fuel : Nat) :
    Runs (Ochr.setAt p v) st fuel () { st with env := Env.setAtE st.env p v } := by
  cases p <;> exact ⟨fuel, #[], rfl⟩

/-- The environment after `pushTemp` (a temporary of the top frame). -/
def Env.pushTempE (env : Env) (v : Value) : Env :=
  env.modify (env.size - 1) fun fr => { fr with temps := fr.temps.push v }

theorem runs_pushTemp (v : Value) (st : MState) (fuel : Nat) :
    Runs (Ochr.pushTemp v) st fuel () { st with env := Env.pushTempE st.env v } := ⟨fuel, #[], rfl⟩

/-- The environment after `pushBind`. -/
def Env.pushBindE (env : Env) (h : Hint) (ty : Option Value) (v : Value) (proof : Bool) (decl : DeclInfo) : Env :=
  env.modify (env.size - 1) fun fr => { fr with binds := fr.binds.push { hint := h, ty, val := v, proof, decl } }

theorem runs_pushBind (h : Hint) (ty : Option Value) (v : Value) (proof : Bool) (decl : DeclInfo)
    (st : MState) (fuel : Nat) :
    Runs (Ochr.pushBind h ty v proof decl) st fuel () { st with env := Env.pushBindE st.env h ty v proof decl } :=
  ⟨fuel, #[], rfl⟩

/-- `withTemp` is `pushTemp`'s environment. -/
theorem withTemp_eq (st : MState) (v : Value) : st.withTemp v = { st with env := Env.pushTempE st.env v } := rfl

/-! ## Part B: the environment's positions -/

/-- The positions of a checker frame, bindings then temporaries. -/
def frameAllPos (f : Nat) (fr : Frame) : List Pos :=
  (List.range fr.binds.size).map (Pos.bind f) ++ (List.range fr.temps.size).map (Pos.temp f)

/-- `allPos` as a list expression (the checker's `Id.run` loops unfolded; `SState.positions_eq`'s
twin). -/
theorem allPos_eq (env : Env) :
    allPos env = (List.range env.size).flatMap fun f => (env[f]?.map (frameAllPos f)).getD [] := by
  simp [allPos]
  rw [foldl_push_toList]
  simp only [List.nil_append]
  have key : ∀ (l : List Nat) (hl : ∀ x ∈ l, x < env.size),
      (l.attach.flatMap fun x => List.map (Pos.bind x.val) (List.range' 0 (env[x.val]'(hl x.val x.property)).binds.size) ++
          List.map (Pos.temp x.val) (List.range' 0 (env[x.val]'(hl x.val x.property)).temps.size))
        = l.flatMap fun f => (Option.map (frameAllPos f) env[f]?).getD [] := by
    intro l hl
    induction l with
    | nil => simp
    | cons a l ih =>
      simp only [List.attach_cons, List.flatMap_cons, List.flatMap_map]
      rw [show env[a]? = some (env[a]'(hl a (List.mem_cons_self ..))) from Array.getElem?_eq_getElem _]
      simp only [Option.map_some, Option.getD_some, frameAllPos, List.range_eq_range']
      congr 1
      exact ih fun x hx => hl x (List.mem_cons_of_mem _ hx)
  rw [List.range_eq_range']
  exact key (List.range' 0 env.size) (fun x hx => by simp [List.mem_range'] at hx; omega)

/-- `setAt` keeps the frames' sizes, so the positions. -/
theorem allPos_setAtE (env : Env) (p : Pos) (v : Value) : allPos (Env.setAtE env p v) = allPos env := by
  rw [allPos_eq, allPos_eq]
  cases p with
  | bind f i =>
    simp only [Env.setAtE, Array.size_modify]
    congr 1; funext f'
    by_cases hff : f = f'
    · subst hff
      rw [Array.getElem?_modify]; simp only [if_true]
      cases env[f]? with
      | none => rfl
      | some fr => simp [frameAllPos, Array.size_modify]
    · rw [Array.getElem?_modify]; simp only [hff, if_false]
  | temp f i =>
    simp only [Env.setAtE, Array.size_modify]
    congr 1; funext f'
    by_cases hff : f = f'
    · subst hff
      rw [Array.getElem?_modify]; simp only [if_true]
      cases env[f]? with
      | none => rfl
      | some fr => simp [frameAllPos, Array.size_set!]
    · rw [Array.getElem?_modify]; simp only [hff, if_false]

theorem flatMap_congr_mem {α β : Type _} {f g : α → List β} :
    ∀ (l : List α), (∀ x ∈ l, f x = g x) → l.flatMap f = l.flatMap g
  | [], _ => rfl
  | x :: l, h => by
    simp only [List.flatMap_cons]
    rw [h x (List.mem_cons_self ..), flatMap_congr_mem l fun y hy => h y (List.mem_cons_of_mem _ hy)]

/-- `pushTemp` adds one position, the new temporary of the top frame, after the others. -/
theorem allPos_pushTempE (env : Env) (v : Value) (fr : Frame) (hfr : env[env.size - 1]? = some fr)
    (hne : 0 < env.size) :
    allPos (Env.pushTempE env v) = allPos env ++ [.temp (env.size - 1) fr.temps.size] := by
  rw [allPos_eq, allPos_eq]
  simp only [Env.pushTempE, Array.size_modify]
  generalize hm : env.size - 1 = m at hfr ⊢
  have hsz : env.size = m + 1 := by omega
  rw [hsz, List.range_succ, List.flatMap_append, List.flatMap_append, List.flatMap_singleton,
    List.flatMap_singleton, List.append_assoc]
  congr 1
  · apply flatMap_congr_mem
    intro f' hf'
    have : m ≠ f' := by simp [List.mem_range] at hf'; omega
    rw [Array.getElem?_modify]; simp only [this, if_false]
  · rw [Array.getElem?_modify]; simp only [if_true, hfr, Option.map_some, Option.getD_some]
    simp only [frameAllPos, Array.size_push, List.range_succ, List.map_append, List.map_cons, List.map_nil,
      List.append_assoc]

/-- A stored type is untouched by `setAt`. -/
theorem hintAt_setAtE (dm : DataModel) (C : CodeMeaning) (Γ : List IndDecl) (ρ : Assignment)
    (env : Env) (p q : Pos) (v : Value) :
    Env.hintAt dm C Γ ρ (Env.setAtE env p v) q = Env.hintAt dm C Γ ρ env q := by
  cases q with
  | temp _ _ => rfl
  | bind f' i' =>
    cases p with
    | bind f i =>
      simp only [Env.hintAt, Env.setAtE]
      by_cases hff : f = f'
      · subst hff
        rw [Array.getElem?_modify]; simp only [if_true]
        cases env[f]? with
        | none => rfl
        | some fr =>
          simp only [Option.map_some, Option.bind_some]
          by_cases hii : i = i'
          · subst hii
            rw [Array.getElem?_modify]; simp only [if_true]
            cases fr.binds[i]? <;> rfl
          · rw [Array.getElem?_modify]; simp only [hii, if_false]
      · rw [Array.getElem?_modify]; simp only [hff, if_false]
    | temp f i =>
      simp only [Env.hintAt, Env.setAtE]
      by_cases hff : f = f'
      · subst hff
        rw [Array.getElem?_modify]; simp only [if_true]
        cases env[f]? <;> rfl
      · rw [Array.getElem?_modify]; simp only [hff, if_false]

section
variable (dm : DataModel) (C : CodeMeaning) (Γ : List IndDecl) (ρ : Assignment)

/-- Another position's meaning is untouched by `setAt`. -/
theorem mean_setAtE_other (env : Env) (p q : Pos) (v : Value) (φ : Future) (hne : q ≠ p) :
    Env.mean dm C Γ ρ φ (Env.setAtE env p v) q = Env.mean dm C Γ ρ φ env q := by
  cases q with
  | bind f' i' =>
    simp only [Env.mean, hintAt_setAtE]
    cases p with
    | bind f i =>
      simp only [Env.setAtE]
      by_cases hff : f = f'
      · subst hff
        rw [Array.getElem?_modify]; simp only [if_true]
        cases env[f]? with
        | none => rfl
        | some fr =>
          simp only [Option.map_some, Option.bind_some]
          have hii : i ≠ i' := fun h => hne (by subst h; rfl)
          rw [Array.getElem?_modify]; simp only [hii, if_false]
      · rw [Array.getElem?_modify]; simp only [hff, if_false]
    | temp f i =>
      simp only [Env.setAtE]
      by_cases hff : f = f'
      · subst hff
        rw [Array.getElem?_modify]; simp only [if_true]
        cases env[f]? <;> rfl
      · rw [Array.getElem?_modify]; simp only [hff, if_false]
  | temp f' i' =>
    simp only [Env.mean, hintAt_setAtE]
    cases p with
    | bind f i =>
      simp only [Env.setAtE]
      by_cases hff : f = f'
      · subst hff
        rw [Array.getElem?_modify]; simp only [if_true]
        cases env[f]? <;> rfl
      · rw [Array.getElem?_modify]; simp only [hff, if_false]
    | temp f i =>
      simp only [Env.setAtE]
      by_cases hff : f = f'
      · subst hff
        rw [Array.getElem?_modify]; simp only [if_true]
        cases env[f]? with
        | none => rfl
        | some fr =>
          simp only [Option.map_some, Option.bind_some]
          have hii : i ≠ i' := fun h => hne (by subst h; rfl)
          first
            | (rw [Array.set!, Array.getElem?_setIfInBounds]; simp only [hii, if_false])
            | (simp [Array.set!, Array.getElem?_setIfInBounds, hii])
      · rw [Array.getElem?_modify]; simp only [hff, if_false]

/-- The written binding means the written value at the binding's hint. -/
theorem mean_setAtE_bind (env : Env) (f i : Nat) (v : Value) (φ : Future) (fr : Frame) (b : Binding)
    (hf : env[f]? = some fr) (hi : fr.binds[i]? = some b) :
    Env.mean dm C Γ ρ φ (Env.setAtE env (.bind f i) v) (.bind f i)
      = Value.mean dm C Γ ρ φ (Env.hintAt dm C Γ ρ env (.bind f i)) v := by
  rw [Env.mean, hintAt_setAtE]
  simp only [Env.setAtE]
  rw [Array.getElem?_modify]; simp only [if_true, hf, Option.map_some, Option.bind_some]
  rw [Array.getElem?_modify]; simp only [if_true, hi, Option.map_some]

/-- The written temporary means the written value (at the untyped hint). -/
theorem mean_setAtE_temp (env : Env) (f i : Nat) (v : Value) (φ : Future) (fr : Frame)
    (hf : env[f]? = some fr) (hi : i < fr.temps.size) :
    Env.mean dm C Γ ρ φ (Env.setAtE env (.temp f i) v) (.temp f i)
      = Value.mean dm C Γ ρ φ (.plain .err) v := by
  rw [Env.mean]
  simp only [Env.setAtE]
  rw [Array.getElem?_modify]; simp only [if_true, hf, Option.map_some, Option.bind_some]
  first
    | (rw [Array.set!, Array.getElem?_setIfInBounds]; simp [hi, Env.hintAt])
    | (simp [Array.set!, Array.getElem?_setIfInBounds, hi, Env.hintAt])

end

section
variable (dm : DataModel) (C : CodeMeaning) (Γ : List IndDecl) (ρ : Assignment)

/-- A stored type is untouched by `pushTemp`. -/
theorem hintAt_pushTempE (env : Env) (v : Value) (q : Pos) :
    Env.hintAt dm C Γ ρ (Env.pushTempE env v) q = Env.hintAt dm C Γ ρ env q := by
  cases q with
  | temp _ _ => rfl
  | bind f' i' =>
    simp only [Env.hintAt, Env.pushTempE]
    by_cases hff : env.size - 1 = f'
    · rw [Array.getElem?_modify]; simp only [hff, if_true]
      cases env[f']? <;> rfl
    · rw [Array.getElem?_modify]; simp only [hff, if_false]

/-- Every position but the new temporary means the same after `pushTemp`. -/
theorem mean_pushTempE_other (env : Env) (v : Value) (fr : Frame) (hfr : env[env.size - 1]? = some fr)
    (q : Pos) (φ : Future) (hq : q ≠ .temp (env.size - 1) fr.temps.size) :
    Env.mean dm C Γ ρ φ (Env.pushTempE env v) q = Env.mean dm C Γ ρ φ env q := by
  cases q with
  | bind f' i' =>
    simp only [Env.mean]
    rw [hintAt_pushTempE]
    simp only [Env.pushTempE]
    by_cases hff : env.size - 1 = f'
    · rw [Array.getElem?_modify]; simp only [hff, if_true]
      cases env[f']? <;> rfl
    · rw [Array.getElem?_modify]; simp only [hff, if_false]
  | temp f' i' =>
    simp only [Env.mean]
    rw [hintAt_pushTempE]
    simp only [Env.pushTempE]
    by_cases hff : env.size - 1 = f'
    · subst hff
      rw [Array.getElem?_modify]; simp only [if_true, hfr, Option.map_some, Option.bind_some]
      have hii : i' ≠ fr.temps.size := fun h => hq (by subst h; rfl)
      rw [Array.getElem?_push]; simp only [hii, if_false]
    · rw [Array.getElem?_modify]; simp only [hff, if_false]

/-- The new temporary means the pushed value (at the untyped hint). -/
theorem mean_pushTempE_new (env : Env) (v : Value) (fr : Frame) (hfr : env[env.size - 1]? = some fr)
    (φ : Future) :
    Env.mean dm C Γ ρ φ (Env.pushTempE env v) (.temp (env.size - 1) fr.temps.size)
      = Value.mean dm C Γ ρ φ (.plain .err) v := by
  simp only [Env.mean, Env.pushTempE]
  rw [Array.getElem?_modify]; simp only [if_true, hfr, Option.map_some, Option.bind_some]
  rw [Array.getElem?_push]; simp [Env.hintAt]

end

/-- `valAt` through the total lookups. -/
theorem valAt_bind_eq (env : Env) (f i : Nat) :
    valAt env (.bind f i) = (((env[f]?).getD default).binds[i]?.getD default).val := by
  first
    | (simp only [valAt, Array.getElem!_eq_getD, Array.getD_eq_getD_getElem?])
    | (simp [valAt, Array.getElem!_eq_getD, Array.getD_eq_getD_getElem?])

theorem valAt_temp_eq (env : Env) (f i : Nat) :
    valAt env (.temp f i) = ((env[f]?).getD default).temps[i]?.getD default := by
  first
    | (simp only [valAt, Array.getElem!_eq_getD, Array.getD_eq_getD_getElem?])
    | (simp [valAt, Array.getElem!_eq_getD, Array.getD_eq_getD_getElem?])

/-- The shape a value gives its position. -/
def shapeOf : Value → Option Nat
  | .borrow l _ => some l
  | _ => none

theorem shape_eq_shapeOf (env : Env) (q : Pos) : Env.shape env q = shapeOf (valAt env q) := by
  simp only [Env.shape, shapeOf]
  generalize valAt env q = w
  cases w <;> rfl

/-- Another position's value is untouched by `setAt`. -/
theorem valAt_setAtE_other (env : Env) (p q : Pos) (v : Value) (hne : q ≠ p) :
    valAt (Env.setAtE env p v) q = valAt env q := by
  cases q with
  | bind f' i' =>
    rw [valAt_bind_eq, valAt_bind_eq]
    cases p with
    | bind f i =>
      simp only [Env.setAtE]
      by_cases hff : f = f'
      · subst hff
        rw [Array.getElem?_modify]; simp only [if_true]
        cases env[f]? with
        | none => rfl
        | some fr =>
          simp only [Option.map_some, Option.getD_some]
          have hii : i ≠ i' := fun h => hne (by subst h; rfl)
          rw [Array.getElem?_modify]; simp only [hii, if_false]
      · rw [Array.getElem?_modify]; simp only [hff, if_false]
    | temp f i =>
      simp only [Env.setAtE]
      by_cases hff : f = f'
      · subst hff
        rw [Array.getElem?_modify]; simp only [if_true]
        cases env[f]? <;> rfl
      · rw [Array.getElem?_modify]; simp only [hff, if_false]
  | temp f' i' =>
    rw [valAt_temp_eq, valAt_temp_eq]
    cases p with
    | bind f i =>
      simp only [Env.setAtE]
      by_cases hff : f = f'
      · subst hff
        rw [Array.getElem?_modify]; simp only [if_true]
        cases env[f]? <;> rfl
      · rw [Array.getElem?_modify]; simp only [hff, if_false]
    | temp f i =>
      simp only [Env.setAtE]
      by_cases hff : f = f'
      · subst hff
        rw [Array.getElem?_modify]; simp only [if_true]
        cases env[f]? with
        | none => rfl
        | some fr =>
          simp only [Option.map_some, Option.getD_some]
          have hii : i ≠ i' := fun h => hne (by subst h; rfl)
          rw [Array.set!, Array.getElem?_setIfInBounds]; simp only [hii, if_false]
      · rw [Array.getElem?_modify]; simp only [hff, if_false]

/-- Another position's shape is untouched by `setAt`. -/
theorem shape_setAtE_other (env : Env) (p q : Pos) (v : Value) (hne : q ≠ p) :
    Env.shape (Env.setAtE env p v) q = Env.shape env q := by
  rw [shape_eq_shapeOf, shape_eq_shapeOf, valAt_setAtE_other env p q v hne]

/-- The written binding's shape is the written value's. -/
theorem shape_setAtE_bind (env : Env) (f i : Nat) (v : Value) (fr : Frame) (b : Binding)
    (hf : env[f]? = some fr) (hi : fr.binds[i]? = some b) :
    Env.shape (Env.setAtE env (.bind f i) v) (.bind f i) = shapeOf v := by
  rw [shape_eq_shapeOf, valAt_bind_eq]
  simp only [Env.setAtE]
  rw [Array.getElem?_modify]; simp only [if_true, hf, Option.map_some, Option.getD_some]
  rw [Array.getElem?_modify]; simp only [if_true, hi, Option.map_some, Option.getD_some]

/-- The written temporary's shape is the written value's. -/
theorem shape_setAtE_temp (env : Env) (f i : Nat) (v : Value) (fr : Frame)
    (hf : env[f]? = some fr) (hi : i < fr.temps.size) :
    Env.shape (Env.setAtE env (.temp f i) v) (.temp f i) = shapeOf v := by
  rw [shape_eq_shapeOf, valAt_temp_eq]
  simp only [Env.setAtE]
  rw [Array.getElem?_modify]; simp only [if_true, hf, Option.map_some, Option.getD_some]
  rw [Array.set!, Array.getElem?_setIfInBounds]; simp [hi]

/-- A flat map of distinct, pairwise disjoint lists is distinct. -/
theorem nodup_flatMap_of {α β : Type _} (F : α → List β) :
    ∀ (l : List α), l.Nodup → (∀ x ∈ l, (F x).Nodup) →
      (∀ x ∈ l, ∀ y ∈ l, x ≠ y → ∀ a ∈ F x, a ∉ F y) → (l.flatMap F).Nodup
  | [], _, _, _ => List.nodup_nil
  | x :: l, hnd, hF, hdisj => by
    show (F x ++ l.flatMap F).Nodup
    have hnd' := List.nodup_cons.mp hnd
    rw [List.nodup_append]
    refine ⟨hF x (List.mem_cons_self ..), nodup_flatMap_of F l hnd'.2
      (fun y hy => hF y (List.mem_cons_of_mem _ hy))
      (fun y hy z hz => hdisj y (List.mem_cons_of_mem _ hy) z (List.mem_cons_of_mem _ hz)), ?_⟩
    intro a ha b hb hab
    subst hab
    simp only [List.mem_flatMap] at hb
    obtain ⟨y, hy, hay⟩ := hb
    have hxy : x ≠ y := fun h => hnd'.1 (h ▸ hy)
    exact hdisj x (List.mem_cons_self ..) y (List.mem_cons_of_mem _ hy) hxy a ha hay

theorem nodup_map_of_inj {α β : Type _} (g : α → β) (hg : ∀ a b, g a = g b → a = b) :
    ∀ (l : List α), l.Nodup → (l.map g).Nodup
  | [], _ => List.nodup_nil
  | x :: l, hnd => by
    have hnd' := List.nodup_cons.mp hnd
    simp only [List.map_cons]
    rw [List.nodup_cons]
    refine ⟨fun h => ?_, nodup_map_of_inj g hg l hnd'.2⟩
    simp only [List.mem_map] at h
    obtain ⟨y, hy, hxy⟩ := h
    exact hnd'.1 (hg _ _ hxy ▸ hy)

/-- The frame of a position. -/
def Pos.frame : Pos → Nat
  | .bind f _ => f
  | .temp f _ => f

/-- The positions of a frame are distinct. -/
theorem frameAllPos_nodup (f : Nat) (fr : Frame) : (frameAllPos f fr).Nodup := by
  simp only [frameAllPos]
  rw [List.nodup_append]
  refine ⟨nodup_map_of_inj _ (fun a b h => by cases h; rfl) _ List.nodup_range,
    nodup_map_of_inj _ (fun a b h => by cases h; rfl) _ List.nodup_range, ?_⟩
  intro a ha b hb hab
  subst hab
  simp only [List.mem_map, List.mem_range] at ha hb
  obtain ⟨i, _, rfl⟩ := ha
  obtain ⟨j, _, hj⟩ := hb
  cases hj

/-- A position of frame `f`'s list is in frame `f`. -/
theorem frame_of_mem_frameAllPos (f : Nat) (fr : Frame) (p : Pos) (hp : p ∈ frameAllPos f fr) :
    Pos.frame p = f := by
  simp only [frameAllPos, List.mem_append, List.mem_map, List.mem_range] at hp
  rcases hp with ⟨i, _, rfl⟩ | ⟨i, _, rfl⟩ <;> rfl

/-- The environment's positions are distinct. -/
theorem allPos_nodup (env : Env) : (allPos env).Nodup := by
  rw [allPos_eq]
  apply nodup_flatMap_of _ _ List.nodup_range
  · intro f _
    cases env[f]? with
    | none => exact List.nodup_nil
    | some fr => exact frameAllPos_nodup f fr
  · intro f _ g _ hfg a ha hb
    cases hf : env[f]? with
    | none => simp [hf] at ha
    | some fr =>
      cases hg : env[g]? with
      | none => simp [hg] at hb
      | some gr =>
        simp only [hf, hg, Option.map_some, Option.getD_some] at ha hb
        have h1 := frame_of_mem_frameAllPos f fr a ha
        have h2 := frame_of_mem_frameAllPos g gr a hb
        exact hfg (h1.symm.trans h2)

/-! ## Part C: the bridge -/

section
variable (dm : DataModel) (C : CodeMeaning) (Γ : List IndDecl) (ρ : Assignment)

theorem sstate_shape (st : MState) : (MState.sstate dm C Γ ρ st).shape = Env.shape st.env := rfl
theorem sstate_nextLoan (st : MState) : (MState.sstate dm C Γ ρ st).nextLoan = st.nextLoan := rfl

/-- A position's meaning in the semantic state is the environment's, at every position
(outside the environment both are `err`). -/
theorem sstate_valAt (st : MState) (p : Pos) (φ : Future) :
    (MState.sstate dm C Γ ρ st).valAt p φ = Env.mean dm C Γ ρ φ st.env p := by
  cases p with
  | bind f i =>
    simp only [SState.valAt, MState.sstate, Env.mean, List.getElem?_map, List.getElem?_zipIdx,
      Array.getElem?_toList, Option.map_map, Option.bind_map]
    cases hf : st.env[f]? with
    | none => rfl
    | some fr =>
      simp only [Option.map_some, Option.bind_some, Function.comp, List.getElem?_map, List.getElem?_zipIdx,
        Array.getElem?_toList]
      cases hi : fr.binds[i]? with
      | none => rfl
      | some b => simp [Nat.zero_add, hf, hi, Env.mean]
  | temp f i =>
    simp only [SState.valAt, MState.sstate, Env.mean, List.getElem?_map, List.getElem?_zipIdx,
      Array.getElem?_toList, Option.map_map, Option.bind_map]
    cases hf : st.env[f]? with
    | none => rfl
    | some fr =>
      simp only [Option.map_some, Option.bind_some, Function.comp, List.getElem?_map, List.getElem?_zipIdx,
        Array.getElem?_toList]
      cases hi : fr.temps[i]? with
      | none => rfl
      | some v => simp [Nat.zero_add, hf, hi, Env.mean]

/-- A binding's type in the semantic state is its hint. -/
theorem sstate_tyAt (st : MState) (p : Pos) :
    (MState.sstate dm C Γ ρ st).tyAt p = Env.hintAt dm C Γ ρ st.env p := by
  cases p with
  | bind f i =>
    simp only [SState.tyAt, MState.sstate, List.getElem?_map, List.getElem?_zipIdx,
      Array.getElem?_toList, Option.map_map, Option.bind_map]
    cases hf : st.env[f]? with
    | none => simp [Env.hintAt, hf]
    | some fr =>
      simp only [Option.map_some, Option.bind_some, Function.comp, List.getElem?_map, List.getElem?_zipIdx,
        Array.getElem?_toList]
      cases hi : fr.binds[i]? with
      | none => simp [Env.hintAt, hf, hi]
      | some b => simp [Nat.zero_add]
  | temp f i => rfl

/-- The semantic state's positions are the environment's. -/
theorem sstate_positions (st : MState) : (MState.sstate dm C Γ ρ st).positions = allPos st.env := by
  rw [SState.positions_eq, allPos_eq]
  simp only [MState.sstate, List.length_map, List.length_zipIdx, Array.length_toList]
  congr 1
  funext f
  simp only [List.getElem?_map, List.getElem?_zipIdx, Array.getElem?_toList]
  cases hf : st.env[f]? with
  | none => rfl
  | some fr => simp [framePos, frameAllPos, Nat.zero_add]

end

end Ochr.Meaning.Steps
