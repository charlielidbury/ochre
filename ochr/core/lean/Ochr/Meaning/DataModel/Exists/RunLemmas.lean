import Ochr.Meaning.DataModel.Faithful
import Ochr.Meaning.Attack.RunEqs

/-!
# Piece 3's run lemmas: what the reference run gives a field-type or parameter-type term

Faithfulness (`DataModel/Faithful.lean`) is conditional: WHERE the run of a declared type term is
defined, its result is the model's. So each lemma here says what the result is when the run is
defined, for one term form, in the frames faithfulness runs in (`teleFrame`, `paramFrame`: one
frame, no live borrow), under EVERY run context (decisions included): a lemma about the run of a
term form, not about a program.

* `runT_var_frame`: a variable reads its binding's value (whatever the decisions say about erasure
  and copying: an erased read that is not `•` fails, `SM.erasedIf`);
* `runT_sort`: `Sort l` is `Type_l`'s code.
-/

namespace Ochr.Meaning.DataModel.Exists.RunLemmas

open Ochr Ochr.Meaning

/-- A one-frame, shape-free state: what `stateOf` builds. -/
theorem stateOf_shape (n : Nat) (bs : List SBinding) : (stateOf n bs).shape = fun _ => none := rfl

/-- In such a state, variable `j` is binding `bs.length - 1 - j` (the last binding is `var 0`). -/
theorem varPos_stateOf (n : Nat) (bs : List SBinding) (j : Nat) (hj : j < bs.length) :
    (stateOf n bs).varPos j = some (.bind 0 (bs.length - 1 - j)) := by
  simp [SState.varPos, stateOf, SState.topIdx, hj]

/-- Its value there, at any future, when the binding's value is constant. -/
theorem valAt_stateOf (n : Nat) (bs : List SBinding) (k : Nat) (hk : k < bs.length) (ψ : Future) :
    (stateOf n bs).valAt (.bind 0 k) ψ = bs[k].val ψ := by
  simp [SState.valAt, stateOf, hk]

/-- **A variable's run reads its binding's value**: in a shape-free state, if the run of `var j` is
defined, its result is the value at `var j`'s position, at the typed future (which a shape-free state
does not move). Whatever the decisions: copy or move, statement or not, and a proof read only when the
value is `•`. -/
theorem runT_var (K : RunCtx) (ρ : Assignment) (φ : Future) (tl : Bool) (h : TyS) (j : Nat) (s : SState)
    (hs : s.shape = fun _ => none) (pos : Pos) (hpos : s.varPos j = some pos)
    {r : Res} {s' : SState} (hr : runT K ρ φ tl h (.place (.var j)) s = some (r, s')) :
    r.1 = s.valAt pos φ := by
  have hacc : ∀ hit, s.access pos hit = s := fun hit => Attack.access_noShape s hs pos hit
  have htf : s.typedFuture φ = φ := by
    have h0 : ∀ l : List Pos, List.filterMap (fun _ : Pos => (none : Option Nat)) l = [] := by
      intro l; induction l with
      | nil => rfl
      | cons _ _ ih => simpa [List.filterMap_cons] using ih
    funext l; simp [SState.typedFuture, SState.liveLabels, hs, h0]
  have hc : contentOf K φ (.var j) s = some ((s.valAt pos φ, s.tyAt pos, pos, []), s) := by
    simp only [contentOf, resolve, Place.steps, hpos, Option.map_some, hacc, htf, Sem.follow]
    rfl
  -- the read: whatever it does to the state, its value is the content's
  have hrd : ∀ copy r' s'', readPlace K φ (.var j) copy s = some (r', s'') → r'.1 = s.valAt pos φ := by
    intro copy r' s'' h'
    simp only [readPlace, hc, bind, Option.bind] at h'
    split at h'
    · cases h'
    · split at h'
      · cases h'
      · split at h'
        · cases h'; rfl
        · revert h'
          generalize setContent K φ pos [] Sem.moved s = sc
          intro h'
          cases sc with
          | none => cases h'
          | some p =>
            obtain ⟨⟨⟩, s₁⟩ := p
            simp only at h'
            split at h' <;> (cases h'; rfl)
  -- the read is guarded (the STRICT END test, ruling (A)); the guard changes no value
  have hg : ∀ copy r' s'', SM.guarded (ContentOk K φ (.var j)) (readPlace K φ (.var j) copy) s = some (r', s'') →
      r'.1 = s.valAt pos φ := fun copy r' s'' h' => hrd copy r' s'' (SM.guarded_some h').2
  simp only [runT] at hr
  unfold SM.erasedIf at hr
  split at hr
  · split at hr
    · rename_i r₀ T₀ s₀ hx
      cases hr
      exact (hg _ _ _ hx).symm ▸ rfl
    · cases hr
    · cases hr
  · unfold SM.stmtIf at hr
    split at hr
    · revert hr
      cases hx : SM.guarded (ContentOk K φ (.var j)) (readPlace K φ (.var j) _) s with
      | none => intro hr; cases hr
      | some x =>
        intro hr
        simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at hr
        obtain ⟨rfl, -⟩ := hr
        exact hg _ x.1 x.2 hx
    · exact hg _ _ _ hr

/-- **`Sort l` runs to `Type_l`'s code.** -/
theorem runT_sort (K : RunCtx) (ρ : Assignment) (φ : Future) (tl : Bool) (h : TyS) (l : Nat) (s : SState) :
    runT K ρ φ tl h (.sort l) s = some ((.ty (TyM.univ l), .plain (TyM.univ (sortSucc l))), s) := by
  simp [runT, pure]

/-! ## The frame a field type runs in -/

/-- `teleFrame`'s bindings: the constructor's fields (the earlier ones, then `moved`), then the
parameters. -/
theorem teleFrame_eq (dm : DataModel) (D : Decisions) (d : IndDecl) (ps : List Sem) (c : Nat) (e : List Sem) :
    ∃ fbs : List SBinding, fbs.length = (e ++ List.replicate (DataLib.arity d c - e.length) Sem.moved).length ∧
      teleFrame dm D d ps c e = stateOf 0 (fbs ++ ps.zipIdx.map (fun vj => faithBind (dm.paramTy d vj.2 (ps.take vj.2)) vj.1
        ((paramDecls D d (DataLib.arity d c)).getD vj.2 .other))) :=
  ⟨_, by simp [DataLib.arity], rfl⟩

/-- **A parameter read in a field type is the parameter**: in `teleFrame`, at a field below the
constructor's arity, variable `ps.length - 1 - j` reads parameter `j` (the checker numbers the
parameters first, the last one `var 0`), so where its run is defined it gives `ps[j]`. -/
theorem runT_teleFrame_param (K : RunCtx) (ρ : Assignment) (φ : Future) (tl : Bool) (h : TyS)
    (dm : DataModel) (D : Decisions) (d : IndDecl) (ps : List Sem) (c : Nat) (e : List Sem)
    (he : e.length ≤ DataLib.arity d c) (j : Nat) (hj : j < ps.length) {v : Nat} (hvj : v = ps.length - 1 - j)
    {r : Res} {s' : SState}
    (hr : runT K ρ φ tl h (.place (.var v)) (teleFrame dm D d ps c e) = some (r, s')) :
    r.1 = ps[j] := by
  subst hvj
  obtain ⟨fbs, hl, heq⟩ := teleFrame_eq dm D d ps c e
  rw [heq] at hr
  have hlen : fbs.length = DataLib.arity d c := by
    simp only [List.length_append, List.length_replicate] at hl; omega
  generalize hL : ps.zipIdx.map (fun vj => faithBind (dm.paramTy d vj.2 (ps.take vj.2)) vj.1
        ((paramDecls D d (DataLib.arity d c)).getD vj.2 .other)) = L at hr
  have hLl : L.length = ps.length := by rw [← hL]; simp
  have hv : ps.length - 1 - j < (fbs ++ L).length := by simp [hLl]; omega
  have h1 := runT_var K ρ φ tl h _ _ (stateOf_shape 0 _) _ (varPos_stateOf 0 _ _ hv) hr
  rw [h1]
  have hk : (fbs ++ L).length - 1 - (ps.length - 1 - j) = fbs.length + j := by simp [hLl]; omega
  have hget : (fbs ++ L)[fbs.length + j]? = some (faithBind (dm.paramTy d j (ps.take j)) ps[j]
      ((paramDecls D d (DataLib.arity d c)).getD j .other)) := by
    rw [List.getElem?_append_right (Nat.le_add_right _ _), Nat.add_sub_cancel_left, ← hL]
    simp [List.getElem?_map, hj]
  rw [hk]
  have hlt : fbs.length + j < (fbs ++ L).length := by simp [hLl]; omega
  rw [valAt_stateOf 0 _ _ hlt]
  rw [List.getElem?_eq_getElem hlt, Option.some.injEq] at hget
  rw [hget]
  rfl

/-! ## An applied declaration: `D(ā)` -/

/-- **An erased term's result is its run's**: whatever the flags, a defined `SM.erasedIf` returns the
value its inner run returned (an erased proof only when that value is `•`). -/
theorem erasedIf_val {fl : Bool × Bool} {x : SM Res} {s s' : SState} {r : Res}
    (h : SM.erasedIf fl x s = some (r, s')) : ∃ r₀ s₀, x s = some (r₀, s₀) ∧ r.1 = r₀.1 := by
  unfold SM.erasedIf at h
  split at h
  · split at h
    · rename_i r₀ T₀ s₀ hx
      cases h
      exact ⟨_, _, hx, rfl⟩
    · cases h
    · cases h
  · unfold SM.stmtIf at h
    split at h
    · revert h
      cases hx : x s with
      | none => intro h; cases h
      | some p =>
        intro h
        simp only [Option.map_some, Option.some.injEq] at h
        obtain ⟨rfl, -⟩ := Prod.mk.inj h
        exact ⟨p.1, p.2, rfl, rfl⟩
    · exact ⟨r, s', h, rfl⟩

/-- `runParams` runs each argument on a copy of the state it starts from, at its parameter's type at
the earlier ones; it leaves the state as it was. -/
theorem runParams_spec (K : RunCtx) (ρ : Assignment) (φ : Future) (d : IndDecl) :
    ∀ (as : List Term) (i : Nat) (earlier : List Sem) (s s' : SState) (vs : List Sem),
      runParams K ρ φ d i earlier as s = some (vs, s') →
      s' = s ∧ vs.length = as.length ∧
      ∀ (k : Nat) (a : Term) (v : Sem), as[k]? = some a → vs[k]? = some v →
        ∃ T s₁, runT K ρ φ false (.plain (K.dm.paramTy d (i + k) (earlier ++ vs.take k))) a s = some ((v, T), s₁)
  | [], i, earlier, s, s', vs, h => by
    simp only [runParams, pure] at h
    cases h
    exact ⟨rfl, rfl, fun k a v ha => by simp at ha⟩
  | a :: as, i, earlier, s, s', vs, h => by
    simp only [runParams, bind, SM.onCopy] at h
    revert h
    cases ha : runT K ρ φ false (.plain (K.dm.paramTy d i earlier)) a s with
    | none => intro h; simp at h
    | some p =>
      obtain ⟨⟨v, T⟩, s₁⟩ := p
      simp only [Option.map_some]
      cases hr : runParams K ρ φ d (i + 1) (earlier ++ [v]) as s with
      | none => intro h; simp [hr] at h
      | some q =>
        obtain ⟨rest, s₂⟩ := q
        intro h
        simp only [hr, pure, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        obtain ⟨hs, hl, hk⟩ := runParams_spec K ρ φ d as (i + 1) (earlier ++ [v]) s s₂ rest hr
        subst hs
        refine ⟨rfl, by simp [hl], fun k a' v' ha' hv' => ?_⟩
        rcases k with _ | k
        · simp only [List.getElem?_cons_zero, Option.some.injEq] at ha' hv'
          subst ha' hv'
          exact ⟨T, s₁, by simpa using ha⟩
        · simp only [List.getElem?_cons_succ] at ha' hv'
          obtain ⟨T', s₃, h3⟩ := hk k a' v' ha' hv'
          refine ⟨T', s₃, ?_⟩
          have : i + 1 + k = i + (k + 1) := by omega
          rw [this, List.append_assoc] at h3
          simpa using h3

/-- **`D(ā)` runs to `D`'s code at its arguments' meanings** (when it runs): the declaration is the
first of its name in `Γ`, the arguments are each run on a copy at its parameter's type, they are
members of their parameters' types (`paramsOk`, the strict former), and the result is
`tyM d psM`; the state is unchanged. -/
theorem runT_tind (K : RunCtx) (ρ : Assignment) (φ : Future) (tl : Bool) (h : TyS) (n : String) (args : List Term)
    (s : SState) {r : Res} {s' : SState} (hr : runT K ρ φ tl h (.tind n args) s = some (r, s')) :
    ∃ d psM, K.Γ.find? (·.name == n) = some d ∧ runParams K ρ φ d 0 [] args s = some (psM, s) ∧
      paramsOk K.dm d psM ∧ r = (.ty (K.dm.tyM d psM), .plain (TyM.univ d.sort)) ∧ s' = s := by
  simp only [runT] at hr
  revert hr
  cases hd : List.find? (fun x => x.name == n) K.Γ with
  | none => intro hr; cases hr
  | some d =>
    intro hr
    simp only [bind] at hr
    revert hr
    cases hp : runParams K ρ φ d 0 [] args s with
    | none => intro hr; cases hr
    | some p =>
      obtain ⟨psM, s₁⟩ := p
      obtain ⟨rfl, -, -⟩ := runParams_spec K ρ φ d args 0 [] s s₁ psM hp
      intro hr
      simp only at hr
      split at hr
      · cases hr
        exact ⟨d, psM, rfl, hp, by assumption, rfl, rfl⟩
      · cases hr

/-! ## An equation, and a call of a global -/

/-- **`Eq(A, a, b)` runs to the proposition that its sides' meanings are equal** (when it runs): `A`
runs to a type of some level, each side runs at it from the state `A`'s run left, each side is `⊥`
or a member (`EqOk`, the strict former); all on a copy, the state unchanged. -/
theorem runT_eq (K : RunCtx) (ρ : Assignment) (φ : Future) (tl : Bool) (h : TyS) (A a b : Term)
    (s : SState) {r : Res} {s' : SState} (hr : runT K ρ φ tl h (.eq A a b) s = some (r, s')) :
    ∃ (TA va vb : Sem) (s₁ : SState), (∃ RA, runT K ρ φ false (.plain TyM.err) A s = some ((TA, RA), s₁)) ∧
      (∃ Ra sa, runT K ρ φ false (.plain TA.asTy) a s₁ = some ((va, Ra), sa)) ∧
      (∃ Rb sb, runT K ρ φ false (.plain TA.asTy) b s₁ = some ((vb, Rb), sb)) ∧
      EqOk K.dm.read TA va vb ∧ r.1 = .ty (TyM.prop (va = vb)) ∧ s' = s := by
  simp only [runT, SM.onCopy, bind] at hr
  revert hr
  cases hA : runT K ρ φ false (.plain TyM.err) A s with
  | none => intro hr; simp at hr
  | some p =>
    obtain ⟨⟨TA, RA⟩, s₁⟩ := p
    cases ha : runT K ρ φ false (.plain TA.asTy) a s₁ with
    | none => intro hr; simp [ha] at hr
    | some q =>
      obtain ⟨⟨va, Ra⟩, sa⟩ := q
      cases hb : runT K ρ φ false (.plain TA.asTy) b s₁ with
      | none => intro hr; simp [ha, hb] at hr
      | some w =>
        obtain ⟨⟨vb, Rb⟩, sb⟩ := w
        intro hr
        simp only [ha, hb, Option.map_some] at hr
        split at hr
        · simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at hr
          obtain ⟨rfl, rfl⟩ := hr
          exact ⟨TA, va, vb, s₁, ⟨RA, rfl⟩, ⟨Ra, sa, by first | rfl | exact ha⟩, ⟨Rb, sb, by first | rfl | exact hb⟩, by assumption, rfl, rfl⟩
        · simp at hr

/-- **A call of a global runs its arguments and applies the global's meaning** (when it runs): the
arguments by `runArgs` at the global's type, then `callOf` at the global's meaning; the result's value
is `callOf`'s (an erased call's too: a proof call returns `•` only when `callOf` does). -/
theorem runT_call_const (K : RunCtx) (ρ : Assignment) (φ : Future) (tl : Bool) (h : TyS) (g : String)
    (args : List Term) (hd : Bool) (s : SState) {r : Res} {s' : SState}
    (hr : runT K ρ φ tl h (.call (.const g) args hd) s = some (r, s')) :
    ∃ (as : List Res) (s₁ : SState) (r' : Res) (s₂ : SState),
      runArgs K ρ φ (K.D.flags (scopeOf s) (.call (.const g) args hd)).1 (K.C.global g).2.m [] args s = some (as, s₁) ∧
      callOf K.dm.read (K.C.global g) as s₁ = some (r', s₂) ∧ r.1 = r'.1 := by
  simp only [runT] at hr
  obtain ⟨r₀, s₀, hx, hv⟩ := erasedIf_val hr
  simp only [bind, SM.headOf, pure] at hx
  revert hx
  cases ha : runArgs K ρ φ (K.D.flags (scopeOf s) (.call (.const g) args hd)).1 (K.C.global g).2.m [] args s with
  | none => intro hx; cases hx
  | some p =>
    obtain ⟨as, s₁⟩ := p
    intro hx
    simp only at hx
    split at hx
    · exact ⟨as, s₁, r₀, s₀, rfl, hx, hv⟩
    · cases hx

/-- `teleFrame` split: the field bindings (as many as the constructor's arity, the first `e.length`
holding the earlier fields), then the parameter bindings. -/
theorem teleFrame_split (dm : DataModel) (D : Decisions) (d : IndDecl) (ps : List Sem) (c : Nat) (e : List Sem)
    (he : e.length ≤ DataLib.arity d c) :
    ∃ F L : List SBinding, F.length = DataLib.arity d c ∧ L.length = ps.length ∧
      (∀ j (hj : j < e.length), ∃ b, F[j]? = some b ∧ ∀ ψ, b.val ψ = e[j]) ∧
      teleFrame dm D d ps c e = stateOf 0 (F ++ L) := by
  refine ⟨_, _, ?_, ?_, ?_, rfl⟩
  · simp [DataLib.arity] at he ⊢; omega
  · simp
  · intro j hj
    refine ⟨faithBind (dm.fieldTy d ps c j (e.take j)) e[j]
      (if j < e.length && fieldProof D d c j then .prop else .other), ?_, fun ψ => rfl⟩
    simp [List.getElem?_map, List.getElem?_append_left hj, hj]

/-- **An earlier field read in a field type is the field**: in `teleFrame`, variable
`arity + ps.length - 1 - j` reads field `j` (the fields are bound before the parameters, the first
outermost), so where its run is defined it gives `e[j]`. -/
theorem runT_teleFrame_field (K : RunCtx) (ρ : Assignment) (φ : Future) (tl : Bool) (h : TyS)
    (dm : DataModel) (D : Decisions) (d : IndDecl) (ps : List Sem) (c : Nat) (e : List Sem)
    (he : e.length ≤ DataLib.arity d c) (j : Nat) (hj : j < e.length) {v : Nat}
    (hvj : v = DataLib.arity d c + ps.length - 1 - j) {r : Res} {s' : SState}
    (hr : runT K ρ φ tl h (.place (.var v)) (teleFrame dm D d ps c e) = some (r, s')) :
    r.1 = e[j] := by
  subst hvj
  obtain ⟨F, L, hFl, hLl, hFv, heq⟩ := teleFrame_split dm D d ps c e he
  rw [heq] at hr
  have hv : DataLib.arity d c + ps.length - 1 - j < (F ++ L).length := by simp [hFl, hLl]; omega
  have h1 := runT_var K ρ φ tl h _ _ (stateOf_shape 0 _) _ (varPos_stateOf 0 _ _ hv) hr
  rw [h1]
  have hk : (F ++ L).length - 1 - (DataLib.arity d c + ps.length - 1 - j) = j := by simp [hFl, hLl]; omega
  rw [hk]
  have hlt : j < (F ++ L).length := by simp [hFl, hLl]; omega
  rw [valAt_stateOf 0 _ _ hlt]
  have hjF : j < F.length := by omega
  rw [List.getElem_append_left hjF]
  obtain ⟨b, hb, hbv⟩ := hFv j hj
  rw [List.getElem?_eq_getElem hjF, Option.some.injEq] at hb
  rw [hb, hbv]

/-! ## The leaves, and `D(ā)` at zero, one and two arguments -/

theorem runT_nat (K : RunCtx) (ρ : Assignment) (φ : Future) (tl : Bool) (h : TyS) (s : SState) :
    runT K ρ φ tl h .nat s = some ((.ty TyM.nat, .plain (TyM.univ 1)), s) := by
  simp [runT, pure]

theorem runT_zero (K : RunCtx) (ρ : Assignment) (φ : Future) (tl : Bool) (h : TyS) (s : SState) :
    runT K ρ φ tl h .zero s = some ((.el0 Nat 0, .plain TyM.nat), s) := by
  simp [runT, pure]

theorem runT_tind0 (K : RunCtx) (ρ : Assignment) (φ : Future) (tl : Bool) (h : TyS) (n : String) (s : SState)
    {r : Res} {s' : SState} (hr : runT K ρ φ tl h (.tind n []) s = some (r, s')) :
    ∃ d, K.Γ.find? (·.name == n) = some d ∧ r.1 = .ty (K.dm.tyM d []) := by
  obtain ⟨d, psM, hd, hp, -, hr', -⟩ := runT_tind K ρ φ tl h n [] s hr
  obtain ⟨-, hl, -⟩ := runParams_spec K ρ φ d [] 0 [] s s psM hp
  have : psM = [] := List.eq_nil_of_length_eq_zero (by simpa using hl)
  subst this
  exact ⟨d, hd, by rw [hr']⟩

theorem runT_tind1 (K : RunCtx) (ρ : Assignment) (φ : Future) (tl : Bool) (h : TyS) (n : String) (a : Term)
    (s : SState) {r : Res} {s' : SState} (hr : runT K ρ φ tl h (.tind n [a]) s = some (r, s')) :
    ∃ d v T s₁, K.Γ.find? (·.name == n) = some d ∧
      runT K ρ φ false (.plain (K.dm.paramTy d 0 [])) a s = some ((v, T), s₁) ∧ r.1 = .ty (K.dm.tyM d [v]) := by
  obtain ⟨d, psM, hd, hp, -, hr', -⟩ := runT_tind K ρ φ tl h n [a] s hr
  obtain ⟨-, hl, hk⟩ := runParams_spec K ρ φ d [a] 0 [] s s psM hp
  obtain ⟨v, rfl⟩ : ∃ v, psM = [v] := by
    rcases psM with _ | ⟨v, _ | _⟩ <;> simp at hl
    exact ⟨v, rfl⟩
  obtain ⟨T, s₁, h1⟩ := hk 0 a v rfl rfl
  exact ⟨d, v, T, s₁, hd, by simpa using h1, by rw [hr']⟩

theorem runT_tind2 (K : RunCtx) (ρ : Assignment) (φ : Future) (tl : Bool) (h : TyS) (n : String) (a b : Term)
    (s : SState) {r : Res} {s' : SState} (hr : runT K ρ φ tl h (.tind n [a, b]) s = some (r, s')) :
    ∃ d v w T U s₁ s₂, K.Γ.find? (·.name == n) = some d ∧
      runT K ρ φ false (.plain (K.dm.paramTy d 0 [])) a s = some ((v, T), s₁) ∧
      runT K ρ φ false (.plain (K.dm.paramTy d 1 [v])) b s = some ((w, U), s₂) ∧
      r.1 = .ty (K.dm.tyM d [v, w]) := by
  obtain ⟨d, psM, hd, hp, -, hr', -⟩ := runT_tind K ρ φ tl h n [a, b] s hr
  obtain ⟨-, hl, hk⟩ := runParams_spec K ρ φ d [a, b] 0 [] s s psM hp
  obtain ⟨v, w, rfl⟩ : ∃ v w, psM = [v, w] := by
    rcases psM with _ | ⟨v, _ | ⟨w, _ | _⟩⟩ <;> simp at hl
    exact ⟨v, w, rfl⟩
  obtain ⟨T, s₁, h1⟩ := hk 0 a v rfl rfl
  obtain ⟨U, s₂, h2⟩ := hk 1 b w rfl rfl
  exact ⟨d, v, w, T, U, s₁, s₂, hd, by simpa using h1, by simpa using h2, by rw [hr']⟩

/-! ## A call's value depends on the callee and the argument values only -/

theorem callOfL_val.{u} (L : Lvl.{u}) {C : Type u} (t : Tel L.Code PUnit C) (fv : Sem) (args args' : List Res)
    (s s₂ : SState) {r : Res} {s' : SState} (h : callOfL L t fv args s = some (r, s'))
    (hv : args.map (·.1) = args'.map (·.1)) :
    ∃ r₂ s₃, callOfL L t fv args' s₂ = some (r₂, s₃) ∧ r₂.1 = r.1 := by
  unfold callOfL at h ⊢
  dsimp only at h ⊢
  rw [← hv]
  split at h
  · rename_i r0 T finals happ
    simp only [Option.some.injEq] at h
    obtain ⟨rfl, -⟩ := Prod.mk.inj h
    exact ⟨_, _, rfl, rfl⟩
  · rename_i U c fwd back happ
    simp only [Option.some.injEq] at h
    obtain ⟨rfl, -⟩ := Prod.mk.inj h
    exact ⟨_, _, rfl, rfl⟩
  · cases h

/-- **A call's value depends only on the callee and the argument values**: not on the state, the
arguments' types or their labels. -/
theorem callOf_val (R : DataRead) (fv : Res) (args args' : List Res) (s s₂ : SState) {r : Res} {s' : SState}
    (h : callOf R fv args s = some (r, s')) (hv : args.map (·.1) = args'.map (·.1)) :
    ∃ r₂ s₃, callOf R fv args' s₂ = some (r₂, s₃) ∧ r₂.1 = r.1 := by
  unfold callOf at h ⊢
  split at h
  · exact callOfL_val _ _ _ _ _ _ _ h hv
  · exact callOfL_val _ _ _ _ _ _ _ h hv
  · exact callOfL_val _ _ _ _ _ _ _ h hv
  · cases h

/-- `runArgs` at one argument: the argument's run (in place or on a copy), at the callee's first domain. -/
theorem runArgs_one (K : RunCtx) (ρ : Assignment) (φ : Future) (stmt : Bool) (fT : TyM) (a : Term) (s : SState)
    {as : List Res} {s' : SState} (h : runArgs K ρ φ stmt fT [] [a] s = some (as, s')) :
    ∃ v T s₁, runT K ρ φ false (if a.argHinted then .plain (fT.domAfter K.dm.read []) else .plain TyM.err) a s =
      some ((v, T), s₁) ∧ as.map (·.1) = [v] := by
  simp only [runArgs, bind] at h
  revert h
  generalize hb : (stmt && !(K.D.declOf (scopeOf s) a matches .ref _)) = b
  cases hst : SM.stmtIf b (runT K ρ φ false (if a.argHinted then .plain (fT.domAfter K.dm.read []) else .plain TyM.err) a) s with
  | none => intro h; simp [hst] at h
  | some p =>
    obtain ⟨r, s₁⟩ := p
    intro h
    simp only [hst, runArgs, pure, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    rcases SM.stmtIf_some hst with ⟨-, hx⟩ | ⟨-, -, -, r₀, s₀, hx, rfl⟩
    · exact ⟨r.1, r.2, s₁, hx, rfl⟩
    · exact ⟨r₀.1, r₀.2, s₀, hx, rfl⟩

end Ochr.Meaning.DataModel.Exists.RunLemmas
