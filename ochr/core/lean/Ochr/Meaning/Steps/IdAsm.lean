import Ochr.Meaning.Steps.IH
import Ochr.Meaning.FrameProp

/-!
# `Id` computes, assembled from named obligations (docs/31 D74; area (d))

`Machine.idType` evaluates the type, checks [Id-typestate] (both sides leave the same type-state),
makes one fresh unknown per borrow binding both sides re-point ([Obs-ref]), observes each side on a
private copy (`observe`: the side run, a fresh value written through each re-pointed binding, every
borrow ended, the result and the footprint's owners read), and returns the conjunction of the
equalities of the two observations. The reference's `Id` (`run`'s `.id` clause) is the proposition
that the two sides' observations of EVERY position are equal, for every typed written value.

The assembly (`idType_step_asm`): the two observations by `observe_step`, every position outside the
footprint by `footprint_coverage` (the type-states agree), the conjunction's meaning by the split
(`idType_split`, `mkEqM_step` inside it), the reference's run by `id_run`, and the written values by
`fresh_realize`; the list reasoning (`obs_eq_iff`) is proved.
-/

namespace Ochr.Meaning.Steps

open Ochr Ochr.Meaning

/-- Two observations of the same length are equal exactly when their heads are and their tails are at
every index a predicate marks; where it does not, they are equal anyway. -/
theorem obs_eq_iff (o₁ o₂ : List Sem) (n : Nat) (h₁ : o₁.length = n + 1) (h₂ : o₂.length = n + 1)
    (mark : Nat → Prop) (hout : ∀ j, j < n → ¬ mark j → o₁.tail[j]? = o₂.tail[j]?) :
    o₁ = o₂ ↔ o₁[0]? = o₂[0]? ∧ ∀ j, j < n → mark j → o₁.tail[j]? = o₂.tail[j]? := by
  constructor
  · rintro rfl; exact ⟨rfl, fun _ _ _ => rfl⟩
  · rintro ⟨h0, hm⟩
    match o₁, o₂, h₁, h₂ with
    | x :: xs, y :: ys, h₁, h₂ =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at h0
      subst h0
      simp only [List.length_cons, Nat.add_right_cancel_iff] at h₁ h₂
      simp only [List.tail_cons] at hm hout
      congr 1
      apply List.ext_getElem?
      intro j
      by_cases hj : j < n
      · by_cases hmj : mark j
        · exact hm j hj hmj
        · exact hout j hj hmj
      · rw [List.getElem?_eq_none (by omega), List.getElem?_eq_none (by omega)]

section
variable (K : RunCtx) (ρ : Assignment) (φ : Future)

/-- A reference observation has the result first, then one meaning per position the side started
with. -/
theorem refObs_length {reps : List Place} {ws : List Sem} {hint : TyS} {t : Term} {s : SState} {o : List Sem}
    (h : refObs K ρ φ reps ws hint t s = some o) : o.length = s.positions.length + 1 := by
  unfold refObs at h
  cases hr : run K ρ φ hint t s with
  | none => rw [hr] at h; cases h
  | some x =>
    rw [hr] at h
    simp only [Option.map_some, Option.some.injEq] at h
    subst h
    simp [observation]

/-- **`Id` taken apart** (leaf): `Machine.idType` evaluates the type (`A'`), checks [Id-typestate] (the
two type-states agree, as `footprint_coverage` takes them), makes the fresh values written through
the re-pointed bindings (`refs`, at the places the aligned decision `rePointed` names), observes
each side over the footprint (`observe`, the second from the state the first leaves), and returns
the conjunction of the components' equalities (`mkEqM_step`): its meaning, under every typed
extension, is that the results and each owner's two observed values mean the same. The states it
passes through are good for every typed extension; typed at the end, an extension is typed at
each of them. -/
theorem idType_split (fuel : Nat) (st st' : MState) (typed : Bool) (A t u : Term) (P : Value)
    (hg : Good K.dm K.M K.Γ ρ st) (hctx : CtxOk K ρ st) (s : SState) (π : Nat → Nat) (hs : Rel K ρ φ π st s)
    (hD : DecTab K.D st') (bh : Nat) (h : Runs (Ochr.idType (fuel + 1) typed A t u) st bh P st') :
    ∃ (A' : Value) (tsT tsU : TypeState) (stT stU stR st₁ st₂ : MState) (bT bU b₁ b₂ : Nat)
      (refs : List (Place × Value)) (a b : Value) (as bs : List Value),
      Runs (withLive true (Ochr.typeState fuel t)) st bT tsT stT ∧ Runs (withLive true (Ochr.typeState fuel u)) st bU tsU stU ∧
      (jdMissing tsT.moved tsU.moved = none ∧ jdMissing tsU.moved tsT.moved = none) ∧
      (jdMissing tsT.consumed tsU.consumed = none ∧ jdMissing tsU.consumed tsT.consumed = none) ∧
      (jdMissing tsT.repointed tsU.repointed = none ∧ jdMissing tsU.repointed tsT.repointed = none) ∧
      (jdMissing tsT.leftOpen tsU.leftOpen = none ∧ jdMissing tsU.leftOpen tsT.leftOpen = none) ∧
      refs.map (·.1) = K.D.rePointed (scopeOf s) t ∧
      stR.env = st.env ∧ st.absTy.size ≤ stR.absTy.size ∧
      Runs (Ochr.observe fuel true t A' (footprint st.env [t, u]) refs) stR b₁ (a, as) st₁ ∧
      Runs (Ochr.observe fuel true u A' (footprint st.env [t, u]) refs) st₁ b₂ (b, bs) st₂ ∧
      TablesGrow st₂ st' ∧ st'.env = st.env ∧ st.absTy.size ≤ st'.absTy.size ∧ st.nextLoan ≤ st'.nextLoan ∧
      ∀ (ρ' : Assignment) (Δ' : Nat → TyS), (∀ σ, σ < st.absTy.size → ρ' σ = ρ σ ∧ Δ' σ = K.Δ σ) →
        TypedAssignment K.dm ({ K with Δ := Δ' } : RunCtx).M K.Γ ρ' st' →
        -- typed at the end, typed at each state before, and the states good
        TypedAssignment K.dm ({ K with Δ := Δ' } : RunCtx).M K.Γ ρ' st₁ ∧
        TypedAssignment K.dm ({ K with Δ := Δ' } : RunCtx).M K.Γ ρ' st₂ ∧
        Good K.dm ({ K with Δ := Δ' } : RunCtx).M K.Γ ρ' stR ∧ CtxOk { K with Δ := Δ' } ρ' stR ∧
        Rel { K with Δ := Δ' } ρ' φ π stR s ∧
        CtxOk { K with Δ := Δ' } ρ' st' ∧ Rel { K with Δ := Δ' } ρ' φ π (st'.withTemp P) s ∧
        GoodF K.dm ({ K with Δ := Δ' } : RunCtx).M K.Γ ρ' (st'.withTemp P) [] ∧
        -- the conjunction's meaning
        (propOf { K with Δ := Δ' } ρ' (fun l => φ (π l)) P ↔
          (meanV { K with Δ := Δ' } ρ' (fun l => φ (π l)) (Value.tyS K.dm ({ K with Δ := Δ' } : RunCtx).M K.Γ ρ' A') a =
            meanV { K with Δ := Δ' } ρ' (fun l => φ (π l)) (Value.tyS K.dm ({ K with Δ := Δ' } : RunCtx).M K.Γ ρ' A') b ∧
          ∀ (i : Nat) (p : Pos) (x y : Value), (footprint st.env [t, u])[i]? = some p → as[i]? = some x →
            bs[i]? = some y →
            meanV { K with Δ := Δ' } ρ' (fun l => φ (π l)) (Env.hintAt K.dm ({ K with Δ := Δ' } : RunCtx).M K.Γ ρ' st.env p) x =
              meanV { K with Δ := Δ' } ρ' (fun l => φ (π l)) (Env.hintAt K.dm ({ K with Δ := Δ' } : RunCtx).M K.Γ ρ' st.env p) y)) := by
  sorry

/-- **The reference's `Id`** (leaf): `run`'s `.id` clause from the related state: its result, a
proposition, is true exactly when for every typed written value the two sides' observations (at the
places the decision `rePointed` names, at the type the evaluated `A'` reads as) are equal; and an
observation is the same under every extension of the assignment and the context at new unknowns (the
sides name none of them). -/
theorem id_run (st : MState) (A t u : Term) (A' : Value) (s : SState) (π : Nat → Nat)
    (hg : Good K.dm K.M K.Γ ρ st) (hs : Rel K ρ φ π st s) :
    ∃ r, run K ρ φ (.plain .err) (.id A t u) s = some (r, s) ∧
      ∀ (ρ' : Assignment) (Δ' : Nat → TyS), (∀ σ, σ < st.absTy.size → ρ' σ = ρ σ ∧ Δ' σ = K.Δ σ) →
        ((r.1.asTy).true ↔ ∀ ws, obsTyped K.dm.read (K.D.rePointed (scopeOf s) t) ws s →
          refObs { K with Δ := Δ' } ρ' φ (K.D.rePointed (scopeOf s) t) ws
              (Value.tyS K.dm ({ K with Δ := Δ' } : RunCtx).M K.Γ ρ' A') t s =
            refObs { K with Δ := Δ' } ρ' φ (K.D.rePointed (scopeOf s) t) ws
              (Value.tyS K.dm ({ K with Δ := Δ' } : RunCtx).M K.Γ ρ' A') u s) ∧
        ∀ (ρ'' : Assignment) (Δ'' : Nat → TyS), (∀ σ, σ < st.absTy.size → ρ'' σ = ρ σ ∧ Δ'' σ = K.Δ σ) →
          ∀ ws v, refObs { K with Δ := Δ' } ρ' φ (K.D.rePointed (scopeOf s) t) ws
              (Value.tyS K.dm ({ K with Δ := Δ' } : RunCtx).M K.Γ ρ' A') v s =
            refObs { K with Δ := Δ'' } ρ'' φ (K.D.rePointed (scopeOf s) t) ws
              (Value.tyS K.dm ({ K with Δ := Δ'' } : RunCtx).M K.Γ ρ'' A') v s := by
  sorry

/-- **The written values** (leaf, [Obs-ref]): under a typed extension the fresh values `idType` wrote
mean typed values of the re-pointed bindings' content types; every such list of typed values is so
written under some typed extension; and some typed extension exists (each content type has the
binding's current content). -/
theorem fresh_realize (st st' : MState) (t : Term) (s : SState) (refs : List (Place × Value))
    (hrefs : refs.map (·.1) = K.D.rePointed (scopeOf s) t) :
    (∀ (ρ' : Assignment) (Δ' : Nat → TyS), (∀ σ, σ < st.absTy.size → ρ' σ = ρ σ ∧ Δ' σ = K.Δ σ) →
      TypedAssignment K.dm ({ K with Δ := Δ' } : RunCtx).M K.Γ ρ' st' →
      obsTyped K.dm.read (K.D.rePointed (scopeOf s) t)
        (refs.map fun x => meanV { K with Δ := Δ' } ρ' noFuture (.plain .err) x.2) s) ∧
    (∀ ws, obsTyped K.dm.read (K.D.rePointed (scopeOf s) t) ws s →
      ∃ (ρ' : Assignment) (Δ' : Nat → TyS), (∀ σ, σ < st.absTy.size → ρ' σ = ρ σ ∧ Δ' σ = K.Δ σ) ∧
        TypedAssignment K.dm ({ K with Δ := Δ' } : RunCtx).M K.Γ ρ' st' ∧
        refs.map (fun x => meanV { K with Δ := Δ' } ρ' noFuture (.plain .err) x.2) = ws) ∧
    ∃ (ρ' : Assignment) (Δ' : Nat → TyS), (∀ σ, σ < st.absTy.size → ρ' σ = ρ σ ∧ Δ' σ = K.Δ σ) ∧
        TypedAssignment K.dm ({ K with Δ := Δ' } : RunCtx).M K.Γ ρ' st' := by
  sorry

/-- (leaf) The footprint's owners are positions of the related reference state. -/
theorem footprint_positions (st : MState) (s : SState) (π : Nat → Nat) (hs : Rel K ρ φ π st s) (ts : List Term) :
    ∀ (i : Nat) (p : Pos), (footprint st.env ts)[i]? = some p → ∃ j : Nat, s.positions[j]? = some p := by
  sorry

/-! ### `Id` computes: the assembly -/

/-- **`Id` computes** (`idType_step_stmt`), assembled: under a typed extension the checker's
conjunction holds exactly when the two reference observations at the written values are equal
(`observe_step` twice, `footprint_coverage` off the footprint, `obs_eq_iff`, the conjunction's meaning
from `idType_split`); the reference's `Id` is that for every typed written value (`id_run`), each of
which some typed extension writes (`fresh_realize`). -/
theorem idType_step_asm (fuel : Nat) (ih : StepsIHBelow fuel) : idType_step_stmt K ρ φ (fuel + 1) := by
  intro st st' typed A t u P hg hctx s π hs hD bh h
  obtain ⟨A', tsT, tsU, stT, stU, stR, st₁, st₂, bT, bU, b₁, b₂, refs, a, b, as, bs, htT, htU, hmv, hcs, hrp, hlo,
    hrefs, hRenv, -, hob₁, hob₂, hpost, henv, habs, hnl, hafter⟩ :=
    idType_split K ρ φ fuel st st' typed A t u P hg hctx s π hs hD bh h
  have hD₂ : DecTab K.D st₂ := hD.back hpost
  have hD₁ : DecTab K.D st₁ := hD₂.back (hob₂.grows (grows_observe _ _ _ _ _ _))
  obtain ⟨r, hrun, hr⟩ := id_run K ρ φ st A t u A' s π hg hs
  obtain ⟨hfr₁, hfr₂, hfr₃⟩ := fresh_realize K ρ st st' t s refs hrefs
  -- the written values' meanings under an extension
  let wsOf (Δ' : Nat → TyS) (ρ' : Assignment) : List Sem :=
    refs.map fun x => meanV { K with Δ := Δ' } ρ' noFuture (.plain .err) x.2
  let W := footprint st.env [t, u]
  let reps := K.D.rePointed (scopeOf s) t
  let ob (Δ' : Nat → TyS) (ρ' : Assignment) (ws : List Sem) (v : Term) : Option (List Sem) :=
    refObs { K with Δ := Δ' } ρ' φ reps ws (Value.tyS K.dm ({ K with Δ := Δ' } : RunCtx).M K.Γ ρ' A') v s
  -- the key: under a typed extension the conjunction is the equality of the two observations
  have key : ∀ (ρ' : Assignment) (Δ' : Nat → TyS), (∀ σ, σ < st.absTy.size → ρ' σ = ρ σ ∧ Δ' σ = K.Δ σ) →
      TypedAssignment K.dm ({ K with Δ := Δ' } : RunCtx).M K.Γ ρ' st' →
      (propOf { K with Δ := Δ' } ρ' (fun l => φ (π l)) P ↔ ob Δ' ρ' (wsOf Δ' ρ') t = ob Δ' ρ' (wsOf Δ' ρ') u) := by
    intro ρ' Δ' he hty
    obtain ⟨hty₁, hty₂, hgR, hctxR, hsR, -, -, -, hP⟩ := hafter ρ' Δ' he hty
    obtain ⟨henv₁, -, -, hob1⟩ := (ih.at { K with Δ := Δ' } ρ' φ).observe_step stR st₁ true t A' W refs a as hgR hctxR s π hsR
      hD₁ b₁ hob₁
    obtain ⟨⟨hg₁, hctx₁, hs₁⟩, o₁, ho₁, ho₁0, ho₁t⟩ := hob1 ρ' Δ' (fun _ _ => ⟨rfl, rfl⟩) hty₁
    obtain ⟨-, -, -, hob2⟩ := (ih.at { K with Δ := Δ' } ρ' φ).observe_step st₁ st₂ true u A' W refs b bs hg₁ hctx₁ s π hs₁
      hD₂ b₂ hob₂
    obtain ⟨-, o₂, ho₂, ho₂0, ho₂t⟩ := hob2 ρ' Δ' (fun _ _ => ⟨rfl, rfl⟩) hty₂
    rw [hrefs] at ho₁ ho₂
    rw [henv₁, hRenv] at ho₂t
    rw [hRenv] at ho₁t
    have hl₁ := refObs_length _ _ _ ho₁
    have hl₂ := refObs_length _ _ _ ho₂
    -- off the footprint the two observations agree (`footprint_coverage`, at the starting context)
    have hindep := ((hr ρ' Δ' he).2 ρ K.Δ (fun _ _ => ⟨rfl, rfl⟩))
    have hb₁ : refObs K ρ φ reps (wsOf Δ' ρ') (Value.tyS K.dm ({ K with Δ := K.Δ } : RunCtx).M K.Γ ρ A') t s = some o₁ := by
      rw [← hindep]; exact ho₁
    have hb₂ : refObs K ρ φ reps (wsOf Δ' ρ') (Value.tyS K.dm ({ K with Δ := K.Δ } : RunCtx).M K.Γ ρ A') u s = some o₂ := by
      rw [← hindep]; exact ho₂
    have hout : ∀ j, j < s.positions.length → ¬ (∃ p, s.positions[j]? = some p ∧ p ∈ W) →
        o₁.tail[j]? = o₂.tail[j]? := by
      intro j hj hm
      have hpj : s.positions[j]? = some s.positions[j] := List.getElem?_eq_getElem hj
      have hp : s.positions[j] ∉ W := fun hW => hm ⟨_, hpj, hW⟩
      exact (ih.at K ρ φ).footprint_coverage st stT stU A t u s.positions[j] o₁ o₂ j reps (wsOf Δ' ρ') _ tsT tsU hg hctx
        s π hs bT htT bU htU hmv hcs hrp hlo hp hpj hb₁ hb₂
    have e1 : ob Δ' ρ' (wsOf Δ' ρ') t = some o₁ := ho₁
    have e2 : ob Δ' ρ' (wsOf Δ' ρ') u = some o₂ := ho₂
    rw [e1, e2, Option.some.injEq, obs_eq_iff o₁ o₂ s.positions.length hl₁ hl₂ _ hout, hP, ho₁0, ho₂0, Option.some.injEq]
    apply and_congr_right
    intro _
    constructor
    · intro hc j hj ⟨p, hpj, hpW⟩
      obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp hpW
      have e₁ := ho₁t i j p hi hpj
      have e₂ := ho₂t i j p hi hpj
      have ht₁ : (o₁.tail[j]?).isSome := by
        rw [List.getElem?_eq_getElem (by simp [List.length_tail, hl₁]; omega)]; rfl
      have ht₂ : (o₂.tail[j]?).isSome := by
        rw [List.getElem?_eq_getElem (by simp [List.length_tail, hl₂]; omega)]; rfl
      rw [← e₁] at ht₁ ⊢; rw [← e₂] at ht₂ ⊢
      cases hx : as[i]? with
      | none => rw [hx] at ht₁; cases ht₁
      | some x =>
        cases hy : bs[i]? with
        | none => rw [hy] at ht₂; cases ht₂
        | some y => simp only [Option.map_some, Option.some.injEq]; exact hc i p x y hi hx hy
    · intro ht i p x y hi hx hy
      obtain ⟨j, hpj⟩ := footprint_positions K ρ φ st s π hs [t, u] i p hi
      have hj : j < s.positions.length := by
        rcases Nat.lt_or_ge j s.positions.length with h | h
        · exact h
        · rw [List.getElem?_eq_none h] at hpj; cases hpj
      have e := ht j hj ⟨p, hpj, List.mem_of_getElem? hi⟩
      rw [← ho₁t i j p hi hpj, ← ho₂t i j p hi hpj, hx, hy] at e
      simpa using e
  -- the reference's `Id` is the equality at every typed written value
  refine ⟨henv, habs, hnl, r, hrun, ?_, fun hrt ρ' Δ' he hty =>
    (key ρ' Δ' he hty).mpr ((hr ρ' Δ' he).1.mp hrt _ (hfr₁ ρ' Δ' he hty))⟩
  by_cases hrt : (r.1.asTy).true
  · obtain ⟨ρ', Δ', he, hty⟩ := hfr₃
    obtain ⟨-, -, -, -, -, hctx', hrel', hgf', -⟩ := hafter ρ' Δ' he hty
    exact ⟨ρ', Δ', he, hctx', hrel', hgf', fun _ => hrt,
      fun _ => (key ρ' Δ' he hty).mpr ((hr ρ' Δ' he).1.mp hrt _ (hfr₁ ρ' Δ' he hty))⟩
  · have hnot : ¬ ∀ ws, obsTyped K.dm.read reps ws s → ob K.Δ ρ ws t = ob K.Δ ρ ws u :=
      fun hall => hrt ((hr ρ K.Δ (fun _ _ => ⟨rfl, rfl⟩)).1.mpr hall)
    obtain ⟨ws, hws⟩ := Classical.not_forall.mp hnot
    obtain ⟨hobs, hne⟩ := Classical.not_imp.mp hws
    obtain ⟨ρ', Δ', he, hty, hwsEq⟩ := hfr₂ ws hobs
    obtain ⟨-, -, -, -, -, hctx', hrel', hgf', -⟩ := hafter ρ' Δ' he hty
    refine ⟨ρ', Δ', he, hctx', hrel', hgf', fun hP => ?_, fun hr' => absurd hr' hrt⟩
    exfalso
    have heq := (key ρ' Δ' he hty).mp hP
    have hws' : wsOf Δ' ρ' = ws := hwsEq
    rw [hws'] at heq
    have hi := ((hr ρ' Δ' he).2 ρ K.Δ (fun _ _ => ⟨rfl, rfl⟩))
    exact hne ((hi ws t).symm.trans (heq.trans (hi ws u)))

/-! ### The bridge to the frame property's `Id` case (docs/31 D70, D74) -/

/-- **The checker's observation gives the frame property's `Id` hypotheses** (leaf). Inside a
callee's body run in place, related to the checker's run (`Rel`) and to the closure's run
(`FrameRel`), a side of an `Id` that the checker observed (`observe` accepted it: its final ends are
over whole contents, main's D98, and the body is typed) leaves, in the closure's run, cells holding
whole members of the parameters' content types at the observation (`CellsAtObs`), and the caller's
places tell such members apart (`CellsDetermined`: each borrow argument is lent where its final
content is read directly, or through an earlier call's backward function, injective on members).
What `FrameProp.run_frame_obs` asks, and so what `Call.callOf_inPlace_rel` needs for a body with an
`Id` and a borrow parameter. -/
theorem cells_of_observe (fuel : Nat) (st st' : MState) (t : Term) (A : Value) (W : List Pos)
    (refs : List (Place × Value)) (r : Value) (ws : List Value)
    (hg : Good K.dm K.M K.Γ ρ st) (hctx : CtxOk K ρ st) (s : SState) (π : Nat → Nat) (hs : Rel K ρ φ π st s)
    (bh : Nat) (h : Runs (Ochr.observe fuel true t A W refs) st bh (r, ws) st')
    (σ : Nat → Nat) (s₀ : SState) (ks : List Nat) (hs₀ : FrameStart s₀ ks) (sc : SState) (hfr : FrameRel σ s₀ ks s sc)
    (Ts : List TyM) (hTs : ∀ (i : Nat) (k : Nat), ks[i]? = some k → Ts[i]? = some (s₀.heldTy k))
    (r' : Res) (sc' : SState) (hside : runT K ρ φ false (Value.tyS K.dm K.M K.Γ ρ A) t sc = some (r', sc')) :
    CellsAtObs K φ Ts sc' ∧ CellsDetermined K s₀ ks Ts := by
  sorry

end

end Ochr.Meaning.Steps
