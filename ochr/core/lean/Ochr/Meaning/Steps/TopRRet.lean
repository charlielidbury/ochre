import Ochr.Meaning.Steps.TopRGlob
import Ochr.Meaning.Steps.MatchModel
import Ochr.Meaning.Closure
import Ochr.Meaning.LocalityRun

/-!
# `RetKindR` PROVED: `R`'s function, formed at any state, returns an unlabelled result (lead48; docs/31 D292)

`RetKindR` (`Steps/TopRGlob.lean`) is the clause `RetKindG` of `GlobalsOk` at `R`'s code: the function `fixG` builds for
`R` at ANY forming state returns a result carrying no label, its codomain `Nat` being data. The route (lead47's handoff,
item 3): the result label of `fixG` is the body run's (`fixBodyAt`); the body `match n { Z => Z, S m => R(m) }` returns
one arm's result with its label (`runT`'s `.matchNat`: the join's drop and the lending touch only the state); the arm `Z`
is unlabelled; the arm `S` is a call whose head is the function's own binding, read in place at its stored type, the
stage's Π-type at a data codomain, where `callOf` takes the data row (`applyTelL_telL_data`), which carries no label.
The binding is found at `#1` of the body's start at any forming state: the closure's frame is the forming state's top
frame with `self` and `n` pushed (`SState.under`, `fixStep`), and the tag's [Access] keeps where places resolve and their
types (`resolve_access`, `tyAt_access`).
-/

namespace Ochr.Meaning.Steps.Form.Top.RT

open Ochr Ochr.Meaning Ochr.Meaning.Steps Ochr.Meaning.Steps.Form Ochr.Meaning.Steps.Form.Master
open Ochr.Meaning.Steps.Form.ColumnR Ochr.Meaning.Steps.Form.FixEqDesc
open Ochr.Consistency Ochr.Surface Ochr.Meaning.Assembly

/-- Along `telL` at a data codomain, a call takes the data row: its result carries no label. -/
theorem callOfL_telL_data_label.{u} {L : Lvl.{u}} (hL : L.Lawful) (out : PiCod) (hd : out.isRef = false)
    (ps : List PiDom) (fv : Sem) (args : List Res) {s s' : SState} {r : Res}
    (h : callOfL L (telL L ps [] PUnit out).2 fv args s = some (r, s')) : r.2.label = none := by
  unfold callOfL at h
  dsimp only at h
  split at h
  · simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    rfl
  · rename_i U c fwd back happ
    exfalso
    unfold applyFnL at happ
    cases hu : L.unpack _ fv with
    | none => rw [hu] at happ; cases happ
    | some F =>
      rw [hu] at happ
      obtain ⟨res, fins, he⟩ := applyTelL_telL_data L hL out hd ps [] PUnit (fun _ => []) F _ _ happ
      cases he
  · cases h

/-- **A call at a Π-type of data codomain returns no label** (at every level: `Prop` and above the bounded levels the
call does not apply). -/
theorem callOf_piTyAt_data (R : DataRead) (l : Nat) (ps : List PiDom) (out : PiCod) (hd : out.isRef = false)
    {fv : Res} (hfv : fv.2.m = piTyAt R l ps out) {as : List Res} {s s' : SState} {r : Res}
    (h : callOf R fv as s = some (r, s')) : r.2.label = none := by
  unfold callOf at h
  rw [hfv] at h
  match l, h with
  | 0, h => simp [piTyAt, TyM.prop] at h
  | 1, h => exact callOfL_telL_data_label (lvl0_lawful R) out hd ps fv.1 as h
  | 2, h => exact callOfL_telL_data_label (lvl1_lawful R) out hd ps fv.1 as h
  | 3, h => exact callOfL_telL_data_label (lvl2_lawful R) out hd ps fv.1 as h
  | _ + 4, h => simp [piTyAt, TyM.err] at h

/-! ## The body's run returns an unlabelled result -/

section
variable {K : RunCtx} {ρ : Assignment} {φ : Future}

/-- The type `contentOf` gives at a whole variable is the one stored where it resolves. -/
theorem contentOf_ty {p : Place} {s s₁ : SState} {v : Sem} {T : TyS} {pos : Pos} {steps : List Step} {q : Pos}
    (hres : resolve s p = some (q, [])) (h : contentOf K φ p s = some ((v, T, pos, steps), s₁)) :
    T.m = (s.tyAt q).m := by
  unfold contentOf at h
  rw [hres] at h
  dsimp only at h
  split at h
  · simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨⟨-, rfl, -, -⟩, -⟩ := h
    simp only [List.isEmpty_nil, if_true]
    rw [Strict.tyAt_access]
  · cases h

/-- A place read in place (a call's head) gives the type stored where the place resolves, with no label. -/
theorem readPlace_copy_ty {p : Place} {s s' : SState} {fv : Res} {q : Pos} (hres : resolve s p = some (q, []))
    (h : readPlace K φ p true s = some (fv, s')) : fv.2.m = (s.tyAt q).m := by
  unfold readPlace at h
  cases hc : contentOf K φ p s with
  | none => rw [hc] at h; cases h
  | some x =>
    obtain ⟨⟨v, T, pos, steps⟩, s₁⟩ := x
    have hT := contentOf_ty hres hc
    rw [hc] at h
    simp only [bind, Option.bind] at h
    by_cases h1 : v.whole
    · by_cases h2 : ReadGood K.dm.read T.m v
      · simp only [h1, h2, not_true_eq_false, if_false, if_true, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, -⟩ := h
        exact hT
      · simp [h1, h2] at h
    · simp [h1] at h

/-- **The call `R(n.0)` returns no label** where `#1` resolves to a binding whose stored type is one at which every call
returns no label. -/
theorem runT_callR_label {tl : Bool} {h : TyS} {s s' : SState} {r : Res} {q : Pos} {T : TyM}
    (hres : resolve s (.var 1) = some (q, [])) (hty : (s.tyAt q).m = T)
    (hcall : ∀ (fv : Res) (as : List Res) (s₀ s₁ : SState) (r₀ : Res), fv.2.m = T →
      callOf K.dm.read fv as s₀ = some (r₀, s₁) → r₀.2.label = none)
    (hrun : runT K ρ φ tl h ColumnR.callR s = some (r, s')) : r.2.label = none := by
  unfold ColumnR.callR at hrun
  rw [runT] at hrun
  rcases SM.erasedIf_some hrun with hx | ⟨-, hl⟩
  · obtain ⟨fv, s₁, hfv, hx⟩ := SM.bind_some hx
    obtain ⟨as, s₂, -, hx⟩ := SM.bind_some hx
    simp only [SM.headOf] at hfv
    unfold SM.guarded at hfv
    split at hfv
    · have hm := readPlace_copy_ty hres hfv
      split at hx
      · exact hcall fv as s₂ s' r (hm.trans hty) hx
      · cases hx
    · cases hfv
  · exact hl

/-- **`R`'s body returns no label** at a state where `#1` resolves to a binding whose stored type is one at which every
call returns no label: the arm `Z` is unlabelled, the arm `S` is the call, and the match returns its arm's result. -/
theorem runT_bodyR_label {h : TyS} {s s' : SState} {r : Res} {q : Pos} {T : TyM}
    (hres : resolve s (.var 1) = some (q, [])) (hty : (s.tyAt q).m = T)
    (hcall : ∀ (fv : Res) (as : List Res) (s₀ s₁ : SState) (r₀ : Res), fv.2.m = T →
      callOf K.dm.read fv as s₀ = some (r₀, s₁) → r₀.2.label = none)
    (hrun : runT K ρ φ true h ColumnR.bodyR s = some (r, s')) : r.2.label = none := by
  unfold ColumnR.bodyR at hrun
  rw [runT] at hrun
  rcases SM.erasedIf_some hrun with hx | ⟨-, hl⟩
  · cases hg : SM.guarded (TagOk K φ (.var 0)) (tagOf K φ (.var 0) natTag) s with
    | none => rw [hg] at hx; cases hx
    | some x =>
      obtain ⟨tg, s₁⟩ := x
      -- the tag's state: an [Access] of the scrutinee's position
      have hacc : ∃ p hit, s₁ = s.access p hit := by
        unfold SM.guarded at hg
        split at hg
        · unfold tagOf at hg
          split at hg
          · simp only [Option.some.injEq, Prod.mk.injEq] at hg
            exact ⟨_, _, hg.2.symm⟩
          · cases hg
        · cases hg
      obtain ⟨p, hit, rfl⟩ := hacc
      have hres₁ : resolve (s.access p hit) (.var 1) = some (q, []) := by
        rw [Master.resolve_access]; exact hres
      have hty₁ : ((s.access p hit).tyAt q).m = T := by rw [Strict.tyAt_access]; exact hty
      rw [hg] at hx
      simp only [bind, Option.bind] at hx
      -- the entry is the identity in tail position
      have hme : ∀ t, (matchEntry K φ (!true) t (s.access p hit)).fst = s.access p hit := fun _ => rfl
      simp only [hme] at hx
      split at hx
      · cases hx
      · split at hx
        · -- the arm `Z`: unlabelled
          split at hx
          · cases hx
          · rename_i hz
            dsimp only at hx
            split at hx
            · cases hx
            · simp only [Option.some.injEq, Prod.mk.injEq] at hx
              obtain ⟨rfl, -⟩ := hx
              rw [runT] at hz
              simp only [Pure.pure, Option.some.injEq, Prod.mk.injEq] at hz
              obtain ⟨⟨-, rfl⟩, -⟩ := hz
              rfl
        · -- the arm `S`: the call
          split at hx
          · cases hx
          · rename_i hc
            dsimp only at hx
            split at hx
            · cases hx
            · simp only [Option.some.injEq, Prod.mk.injEq] at hx
              obtain ⟨rfl, -⟩ := hx
              exact runT_callR_label hres₁ hty₁ hcall hc
        · cases hx
  · exact hl

end

/-! ## The body's start: `#1` is the function's own binding -/

/-- Two bindings pushed on a state with a frame: `#1` is the first of them, at its type. -/
theorem varPos_tyAt_push2 (t : SState) (b1 b2 : SBinding) (hne : t.env ≠ []) :
    ∃ q, resolve ((t.pushBind b1).pushBind b2) (.var 1) = some (q, []) ∧
      ((t.pushBind b1).pushBind b2).tyAt q = b1.ty := by
  obtain ⟨fr, hfr⟩ : ∃ fr, t.env.getLast? = some fr := by
    cases h : t.env.getLast? with
    | none => exact absurd (List.getLast?_eq_none_iff.mp h) hne
    | some fr => exact ⟨fr, rfl⟩
  have hlast : ((t.pushBind b1).pushBind b2).env.getLast? =
      some { fr with binds := fr.binds ++ [b1] ++ [b2] } := by
    rw [SState.pushBind_getLast, SState.pushBind_getLast, hfr]; rfl
  refine ⟨.bind ((t.pushBind b1).pushBind b2).topIdx fr.binds.length, ?_, ?_⟩
  · unfold resolve SState.varPos
    rw [hlast]
    simp only [Place.steps, List.length_append, List.length_singleton]
    rw [if_pos (by omega)]
    simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq, Pos.bind.injEq, and_true, true_and]
    omega
  · have he : ((t.pushBind b1).pushBind b2).env[((t.pushBind b1).pushBind b2).topIdx]? =
        some { fr with binds := fr.binds ++ [b1] ++ [b2] } := by
      rw [← hlast, List.getLast?_eq_getElem?]; rfl
    unfold SState.tyAt
    dsimp only
    rw [he]
    simp

/-- **`RetKindR` PROVED** (docs/31 D292; assumes nothing): `R`'s function, formed at ANY state with `DecR`, returns an
unlabelled result, its codomain `Nat` being data. -/
theorem retKindR : RetKindR := by
  intro K _ ρ φ s piT args o ha h
  -- the codomain is data
  have hcod : (codOf K ρ φ s (bindsOf K ρ φ s [.nat]) ([Term.nat].map Term.isRefTy) .nat).isRef = false := rfl
  rw [hcod]
  -- one parameter, not a borrow
  obtain ⟨d, hd, hdr⟩ : ∃ d, runDoms K ρ φ s [.nat] = [d] ∧ d.isRef = false := ⟨_, rfl, rfl⟩
  have hlen := ha.1
  rw [hd] at hlen
  obtain ⟨a, rfl⟩ : ∃ a, args = [a] := by
    match args, hlen with
    | [a], _ => exact ⟨a, rfl⟩
  -- the stage the function's run is at, and its body's run
  unfold fixG fixStage at h
  replace h : fixBodyAt K ρ φ _ s _ _ _ _ _ _ [a] = some o := h
  unfold fixBodyAt at h
  rw [hd] at h
  simp only [List.zip_cons_cons, List.zip_nil_right, List.foldl_cons, List.foldl_nil] at h
  unfold fixStep at h
  simp only [hdr, Bool.false_eq_true, if_false] at h
  split at h
  · rename_i r R s₃ hrun
    rw [Option.ite_none_right_eq_some] at h
    obtain ⟨-, h⟩ := h
    injection h with h
    subst h
    -- main's D142: the run itself, or (an erased function) the run's result label-free at the start's state
    obtain ⟨rr, ss, hrun₀, hcase⟩ := SM.bodyRun_some hrun
    rcases hcase with ⟨-, hr, -⟩ | ⟨-, -, hr⟩
    · subst hr
      obtain ⟨q, hres, hty⟩ := varPos_tyAt_push2 s.under _ _ (by simp [SState.under])
      have hl := runT_bodyR_label hres (congrArg TyS.m hty) (fun fv as s₀ s₁ r₀ hfv hc =>
        callOf_piTyAt_data K.dm.read _ _ _ rfl hfv hc) hrun₀
      simp only at hl ⊢
      rw [hl]; rfl
    · rw [(Prod.mk.inj hr).2]; rfl
  · cases h

/-- **The links of the top at `R`'s program, from ONE fact** (`hlinks_R` with `RetKindR` proved): `KeepsTabFixR`
(whole-machine, the machine lane's: `checkFix`'s continuation keeps the tables' invariant). -/
theorem hlinks_R1 (hkt : KeepsTabFixR) : ∀ items, ResolvesTo pq F items →
    ∀ dm, (∀ d' ∈ indsOf {} F items, dm.covers d') →
      (∀ k, k ≤ items.length → DataFaithful dm (chainDecisions F) (indsOf {} F items)
        (progMeaning dm (chainDecisions F) (indsOf {} F items) (fun _ => .err) {} F (items.take k))) →
      TopLinks dm (chainDecisions F) (indsOf {} F items) F items :=
  hlinks_R hkt retKindR

end Ochr.Meaning.Steps.Form.Top.RT
