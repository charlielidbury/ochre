import Ochr.Meaning.AssignCongr
import Ochr.Meaning.DataModel.Exists.Knot.Grammar

/-!
# The knot, part 4: the model congruence (exists6)

A term that avoids the declaration `d` (`Avoids`: no `d(…)`, constructor or match of `d`, no
embedded value) runs the same under a model and under the same model with `d`'s records replaced
(`runT_congrR`). The run reads a model's records only at a declaration it finds by a name in the term
(`.tind`, `.ctor`, and `meanV` of an embedded value); the carriers, the members, the reading, the field
and parameter types at a record are the universal signature's, the same for every model
(definitionally: `DataModel.sig` ignores the model). The one place a model enters a strict test other
than through its reading is open membership (`OMem`, read by `StateOk` through `lentOk`); open
membership does not depend on the model at all (`omem_indep`).

Attacked before it was proved (docs/34 §18.8): the strict tests read whole states, but only through
the reading and open membership, the same under both models; values carry records, but a member's
test reads the record it carries, not the model's; a type function's result may mention `d` without
naming it, but a call applies the global's meaning (`K.C`), which neither model changes, and the
result is a code carrying its own record. The one gap was in `Avoids` as first written: an embedded
sealed program naming `d` in its term (`avoidsOld_gap`).

The proof follows `AssignCongr.runT_congrA` clause by clause.
-/

namespace Ochr.Meaning.DataModel.Exists.Knot

open Ochr Ochr.Meaning
open Classical

/-- **The gap in `Avoids` as first written** (kernel-checked): the embedded sealed program
`⌈D()⌉` names no `D` in the old sense (no `D(…)` node outside embedded values, no embedded value that
is `D`'s type or one of its constructor values), yet its meaning runs `D()`, which reads `D`'s record.
It does not avoid `D` in the new sense. -/
theorem avoidsOld_gap :
    (Term.val (.sealed (.tind "D" []))).mentionsType "D" = false ∧
      (Term.val (.sealed (.tind "D" []))).anyAtom
        (fun | .tInd m _ => m == "D" | .ind m .. => m == "D" | _ => false) = false ∧
      ¬ Avoids "D" (Term.val (.sealed (.tind "D" []))) := by
  refine ⟨rfl, by decide, fun h => ?_⟩
  have := h.2
  simp [Term.anyAtom, Value.anyAtom] at this

/-! ## Open membership does not depend on the model -/

section
variable {dm dm' : DataModel} {Γ : List IndDecl}

mutual
theorem omem_indep : ∀ {T : TyM} {s : Sem}, dm.OMem Γ T s → dm'.OMem Γ T s
  | _, _, .moved T => .moved T
  | _, _, .mem h => .mem h
  | _, _, .succ n h h' => .succ n h (omem_indep h')
  | _, _, .dat h1 h2 h3 h4 => .dat h1 h2 h3 (ofields_indep h4)

theorem ofields_indep : ∀ {d : IndDecl} {r : Rec} {c i : Nat} {e fs : List Sem},
    dm.OFields Γ d r c i e fs → dm'.OFields Γ d r c i e fs
  | _, _, _, _, _, _, .nil => .nil
  | _, _, _, _, _, _, .cons h hs => .cons (ofield_indep h) (ofields_indep hs)

theorem ofield_indep : ∀ {d : IndDecl} {r : Rec} {c i : Nat} {e : List Sem} {f : Sem},
    dm.OField Γ d r c i e f → dm'.OField Γ d r c i e f
  | _, _, _, _, _, _, .moved => .moved
  | _, _, _, _, _, _, .fits e' t h1 h2 h3 h4 => .fits e' t h1 h2 h3 h4
  | _, _, _, _, _, _, .at e' U h1 h2 h3 => .at e' U h1 h2 (omem_indep h3)
end

end

/-- **Open membership is the same at every model.** -/
theorem pmem_indep (dm dm' : DataModel) : dm.pmem = dm'.pmem := by
  funext Γ s T
  exact propext ⟨omem_indep, omem_indep⟩

/-! ## The context with `d`'s records replaced -/

/-- `K` with `d`'s records replaced by `R`. -/
noncomputable abbrev KR (K : RunCtx) (d : IndDecl) (R : List Sem → Rec) : RunCtx := { K with dm := setRec K.dm d R }

theorem lentOk_R (K : RunCtx) (d : IndDecl) (R : List Sem → Rec) (φ : Future) :
    lentOk (KR K d R) φ = lentOk K φ := by
  funext p s
  unfold lentOk StateOk
  rw [pmem_indep (KR K d R).dm K.dm]
  rfl

theorem recOf_R {K : RunCtx} {d M : IndDecl} (R : List Sem → Rec) (h : M ≠ d) :
    (KR K d R).dm.recOf M = K.dm.recOf M := setRec_other K.dm R h

theorem fieldTy_R {K : RunCtx} {d M : IndDecl} (R : List Sem → Rec) (h : M ≠ d) :
    (KR K d R).dm.fieldTy M = K.dm.fieldTy M := by
  funext ps c i e
  unfold DataModel.fieldTy
  rw [recOf_R R h]
  rfl

/-- A list of terms each avoiding `n`. -/
theorem avoids_of_list {n : String} : ∀ {ts : List Term}, Term.mentionsTypeList n ts = false →
    Term.anyAtomList (fun _ => true) ts = false → ∀ t ∈ ts, Avoids n t
  | [], _, _, t, h => absurd h List.not_mem_nil
  | a :: as, h1, h2, t, h => by
    simp only [Term.mentionsTypeList, Term.anyAtomList, Bool.or_eq_false_iff] at h1 h2
    rcases List.mem_cons.1 h with rfl | h
    · exact ⟨h1.1, h2.1⟩
    · exact avoids_of_list h1.2 h2.2 t h

theorem avoids_of_arms {n : String} : ∀ {as : List (Hint × Term)}, Term.mentionsTypeArms n as = false →
    Term.anyAtomArms (fun _ => true) as = false → ∀ p ∈ as, Avoids n p.2
  | [], _, _, p, h => absurd h List.not_mem_nil
  | a :: as, h1, h2, p, h => by
    simp only [Term.mentionsTypeArms, Term.anyAtomArms, Bool.or_eq_false_iff] at h1 h2
    rcases List.mem_cons.1 h with rfl | h
    · exact ⟨h1.1, h2.1⟩
    · exact avoids_of_arms h1.2 h2.2 p h

/-- The subterms of a term avoiding `n` avoid it. -/
macro "avd" : tactic => `(tactic| (constructor <;>
  simp_all [Avoids, Term.mentionsType, Term.mentionsTypeList, Term.mentionsTypeArms, Term.anyAtom,
    Term.anyAtomList, Term.anyAtomArms]))

theorem find_name' {Γ : List IndDecl} {n : String} {M : IndDecl} (h : Γ.find? (·.name == n) = some M) :
    M.name = n := by
  have := List.find?_some h
  simpa using this

/-! ## The run's helpers that navigate values: the same at every model

`Sem.follow` and `Sem.updAt` take the model but read only its signature; they recurse on the path, so
two models give definitionally equal steps but not definitionally equal recursions. -/

theorem follow_indep (dm dm' : DataModel) (Γ : List IndDecl) : Sem.follow dm Γ = Sem.follow dm' Γ := by
  funext T s steps
  induction steps generalizing T s with
  | nil => rfl
  | cons st sts ih =>
    show (Sem.step dm Γ T st s).bind _ = (Sem.step dm' Γ T st s).bind _
    rw [show Sem.step dm Γ T st s = Sem.step dm' Γ T st s from rfl]
    cases Sem.step dm' Γ T st s with
    | none => rfl
    | some p => obtain ⟨a, b⟩ := p; exact ih b a

theorem updAt_indep (dm dm' : DataModel) (Γ : List IndDecl) : Sem.updAt dm Γ = Sem.updAt dm' Γ := by
  funext T f steps s
  induction steps generalizing T s with
  | nil => rfl
  | cons st sts ih =>
    cases st with
    | deref => rw [Sem.updAt.eq_def, Sem.updAt.eq_def]; dsimp only; exact ih T s
    | proj i => rw [Sem.updAt.eq_def, Sem.updAt.eq_def]; dsimp only; simp only [ih]; rfl
    | field g => rw [Sem.updAt.eq_def, Sem.updAt.eq_def]; dsimp only; simp only [ih]; rfl

theorem unifyTyS_indep (dm dm' : DataModel) (np : Nat) (t : Term) (R : TyS) (sol : List (Option Sem)) :
    unifyTyS dm np t R sol = unifyTyS dm' np t R sol := by
  induction t, R, sol using unifyTyS.induct dm np
    (motive_2 := fun r k as sol => unifyArgsTyS dm np r k as sol = unifyArgsTyS dm' np r k as sol) with
  | case1 j R sol h => simp [unifyTyS, h]
  | case2 j R sol h => simp [unifyTyS, h]
  | case3 m as R sol h => simp [unifyTyS, h]
  | case4 as R sol h m' r hd ih => simp [unifyTyS, h, hd, ih]
  | case5 m as R sol h m' r hd hne => simp [unifyTyS, h, hd, hne]
  | case6 m as R sol h hd => simp [unifyTyS, h, hd]
  | case7 t R sol h1 h2 =>
    rw [unifyTyS.eq_def, unifyTyS.eq_def]
    split
    · rename_i j; exact absurd rfl (h1 j)
    · rename_i m as; exact absurd rfl (h2 m as)
    · rfl
  | case8 r k sol => rfl
  | case9 r k a as sol ih1 ih2 =>
    rw [unifyArgsTyS, unifyArgsTyS, ih2]
    congr 1
    cases h : r (paramKey k) with
    | none => rfl
    | small sv => rfl
    | _ => exact ih1

section
variable (K : RunCtx) (d : IndDecl) (R : List Sem → Rec) (φ : Future)

theorem obsAt_R : obsAt (KR K d R) = obsAt K := by
  funext T steps ob x; unfold obsAt; rw [follow_indep (KR K d R).dm K.dm] <;> rfl

theorem contentOf_R : contentOf (KR K d R) φ = contentOf K φ := by
  funext p s; unfold contentOf; rw [follow_indep (KR K d R).dm K.dm] <;> rfl

theorem setContent_R : setContent (KR K d R) φ = setContent K φ := by
  funext pos steps v s; unfold setContent; rw [updAt_indep (KR K d R).dm K.dm] <;> rfl

theorem borrowPlace_R : borrowPlace (KR K d R) φ = borrowPlace K φ := by
  funext p s; unfold borrowPlace; rw [contentOf_R, updAt_indep (KR K d R).dm K.dm] <;> rfl

theorem dropAt_R : dropAt (KR K d R) φ = dropAt K φ := by
  funext q pos steps s; unfold dropAt; rw [updAt_indep (KR K d R).dm K.dm] <;> rfl

theorem DropOk_R : DropOk (KR K d R) φ = DropOk K φ := by
  funext q pos steps s; unfold DropOk; rw [updAt_indep (KR K d R).dm K.dm] <;> rfl

theorem tagOf_R : tagOf (KR K d R) φ = tagOf K φ := by
  funext p tag s; unfold tagOf; rw [obsAt_R] <;> rfl

theorem assignAt_R : assignAt (KR K d R) φ = assignAt K φ := by
  funext p v lab s; unfold assignAt; rw [setContent_R] <;> rfl

theorem readPlace_R : readPlace (KR K d R) φ = readPlace K φ := by
  funext p copy s; unfold readPlace; rw [contentOf_R, setContent_R] <;> rfl

theorem invalidateOne_R : invalidateOne (KR K d R) φ = invalidateOne K φ := by
  funext s q; unfold invalidateOne; rw [setContent_R] <;> rfl

theorem invalidate_R : invalidate (KR K d R) φ = invalidate K φ := by
  funext p s; unfold invalidate; rw [invalidateOne_R] <;> rfl

theorem InvalidateOk_R : InvalidateOk (KR K d R) φ = InvalidateOk K φ := by
  funext p s; unfold InvalidateOk; rw [invalidateOne_R] <;> rfl

theorem placeTy_R : placeTy (KR K d R) φ = placeTy K φ := by
  funext p s; unfold placeTy; rw [contentOf_R] <;> rfl

theorem entryCap_R : entryCap (KR K d R) φ = entryCap K φ := by
  funext s qk; unfold entryCap; rw [invalidate_R] <;> rfl

theorem entryAccess_R : entryAccess (KR K d R) φ = entryAccess K φ := by
  funext bc s; unfold entryAccess; rw [entryCap_R] <;> rfl

theorem matchEntry_R : matchEntry (KR K d R) φ = matchEntry K φ := by
  funext ent mt s; unfold matchEntry; rw [entryAccess_R] <;> rfl

theorem EntryCapOk_R : EntryCapOk (KR K d R) φ = EntryCapOk K φ := by
  funext s qk; unfold EntryCapOk; rw [InvalidateOk_R] <;> rfl

theorem EntryAccessOk_R : EntryAccessOk (KR K d R) φ = EntryAccessOk K φ := by
  funext bc s; unfold EntryAccessOk; rw [entryCap_R, EntryCapOk_R] <;> rfl

theorem MatchEntryOk_R : MatchEntryOk (KR K d R) φ = MatchEntryOk K φ := by
  funext ent mt s; unfold MatchEntryOk; rw [EntryAccessOk_R] <;> rfl

theorem joinDrop_R : joinDrop (KR K d R) φ = joinDrop K φ := by
  funext entry t s; unfold joinDrop; rw [dropAt_R] <;> rfl

theorem JoinStepOk_R : JoinStepOk (KR K d R) φ = JoinStepOk K φ := by
  funext s q; unfold JoinStepOk; rw [DropOk_R] <;> rfl

theorem JoinDropOk_R : JoinDropOk (KR K d R) φ = JoinDropOk K φ := by
  funext entry t s; unfold JoinDropOk; rw [JoinStepOk_R, dropAt_R] <;> rfl

end

/-! ## The `.fix` clause's pieces -/

section
variable (K : RunCtx) (d : IndDecl) (R : List Sem → Rec) (ρ : Assignment) (φ : Future)

theorem fixBodyAt_congrR {body : Term} {fb : List PBind × PBind}
    (hb : ∀ hint s₂, runT K ρ φ true hint body s₂ = runT (KR K d R) ρ φ true hint body s₂)
    (s : SState) (ps : List PiDom) (out : PiCod) (piT : TyM) (start : Nat) (selfM : Sem) (args : List Sem) :
    fixBodyAt K ρ φ fb s ps out piT start body selfM args = fixBodyAt (KR K d R) ρ φ fb s ps out piT start body selfM args := by
  unfold fixBodyAt
  dsimp only
  generalize (args.zip ps).foldl (fixStep fb) (s.under.pushBind { ty := .plain piT, val := fun _ => selfM, decl := .pi fb.2.2 }, [], []) = F
  obtain ⟨s₂, acc, cells⟩ := F
  dsimp only
  rw [hb]
  rfl

theorem fixStage_congrR {body : Term} {fb : List PBind × PBind}
    (hb : ∀ hint s₂, runT K ρ φ true hint body s₂ = runT (KR K d R) ρ φ true hint body s₂)
    (l : Nat) (s : SState) (ps : List PiDom) (out : PiCod) (dec : Option Nat) (start : Nat) :
    ∀ k, fixStage K ρ φ fb l s ps out dec start body k = fixStage (KR K d R) ρ φ fb l s ps out dec start body k
  | 0 => rfl
  | k + 1 => by
    show fixBodyAt K ρ φ fb s ps out _ start body
        (closureAt K.dm.read l φ ps _ (stageFn l ps (fixRank dec) k (fixStage K ρ φ fb l s ps out dec start body k)))
      = fixBodyAt (KR K d R) ρ φ fb s ps out _ start body
        (closureAt K.dm.read l φ ps _ (stageFn l ps (fixRank dec) k (fixStage (KR K d R) ρ φ fb l s ps out dec start body k)))
    rw [fixStage_congrR hb l s ps out dec start k]
    funext args
    exact fixBodyAt_congrR K d R ρ φ hb s ps out _ start _ args

theorem fixG_congrR {body : Term} {fb : List PBind × PBind}
    (hb : ∀ hint s₂, runT K ρ φ true hint body s₂ = runT (KR K d R) ρ φ true hint body s₂)
    (l : Nat) (s : SState) (ps : List PiDom) (out : PiCod) (piT : TyM) (start : Nat) (dec : Option Nat) :
    fixG K ρ φ fb l s ps out piT start dec body = fixG (KR K d R) ρ φ fb l s ps out piT start dec body := by
  funext args
  show fixStage K ρ φ fb l s ps out dec start body (fixRank dec args + 1) args
    = fixStage (KR K d R) ρ φ fb l s ps out dec start body (fixRank dec args + 1) args
  rw [fixStage_congrR K d R ρ φ hb]

end

/-! ## The congruence -/

section
variable (K : RunCtx) (d : IndDecl) (R : List Sem → Rec) (ρ : Assignment) (φ : Future)

mutual
/-- **The model congruence**: a term avoiding `d` runs the same under `K` and under `K` with `d`'s
records replaced. -/
theorem runT_congrR : ∀ (tl : Bool) (t : Term) (hint : TyS) (s : SState), Avoids d.name t →
    runT K ρ φ tl hint t s = runT (KR K d R) ρ φ tl hint t s
  | tl, .place p, hint, s, ha => by rw [runT, runT, readPlace_R]; rfl
  | tl, .borrow p, hint, s, ha => by
    rw [runT, runT, lentOk_R K d R φ, borrowPlace_R, invalidate_R, InvalidateOk_R]; rfl
  | tl, .seq u w, hint, s, ha => by
    rw [runT, runT]
    refine SM.erasedIf_congr ?_
    apply SM.bind_congr (runT_congrR false u _ s (by avd))
    intro a s₁ _
    apply SM.bind_congr rfl
    intro _ s₂ _
    exact runT_congrR tl w (tailHint tl hint) _ (by avd)
  | tl, .succ u, hint, s, ha => by
    rw [runT, runT]
    refine SM.erasedIf_congr ?_
    refine SM.strictS_congr ?_
    apply SM.bind_congr (runT_congrR false u _ s (by avd))
    intro a s₁ _; rfl
  | tl, .ref A, hint, s, ha => by
    rw [runT, runT]
    refine SM.erasedIf_congr ?_
    refine SM.strictS_congr ?_
    apply SM.bind_congr (runT_congrR false A _ s (by avd))
    intro a s₁ _; rfl
  | tl, .const n, hint, s, ha => by rw [runT, runT]
  | tl, .sort l, hint, s, ha => by rw [runT, runT]
  | tl, .nat, hint, s, ha => by rw [runT, runT]
  | tl, .unit, hint, s, ha => by rw [runT, runT]
  | tl, .zero, hint, s, ha => by rw [runT, runT]
  | tl, .tt, hint, s, ha => by rw [runT, runT]
  | tl, .cong f g, hint, s, ha => by
    rw [runT, runT]
    have hg : ∀ s, runT K ρ φ false (.plain .err) g s = runT (KR K d R) ρ φ false (.plain .err) g s :=
      fun s => runT_congrR false g _ s (by avd)
    exact SM.onCopy_congr (premises_congr_all [g] (fun y hy => by rw [List.mem_singleton.mp hy]; exact hg) s)
  | tl, .val v, hint, s, ha => absurd ha.2 (by cases v <;> simp [Term.anyAtom, Value.anyAtom])
  | tl, .ascribe u A, hint, s, ha => by
    rw [runT, runT]
    refine SM.erasedIf_congr ?_
    refine SM.strictS_congr ?_
    apply SM.bind_congr (SM.onCopy_congr (runT_congrR false A _ s (by avd)))
    rintro ⟨TA, _⟩ s₁ h1
    have e := SM.onCopy_state h1
    subst e
    apply SM.bind_congr (runT_congrR false u _ _ (by avd))
    intro _ _ _; rfl
  | tl, .eq A a b, hint, s, ha => by
    rw [runT, runT]
    apply SM.onCopy_congr
    apply SM.bind_congr (runT_congrR false A _ s (by avd))
    rintro ⟨TA, _⟩ s₁ _
    apply SM.bind_congr (SM.onCopy_congr (runT_congrR false a _ s₁ (by avd)))
    rintro ⟨va, _⟩ s₂ h2
    have e := SM.onCopy_state h2
    subst e
    apply SM.bind_congr (SM.onCopy_congr (runT_congrR false b _ _ (by avd)))
    intro _ _ _; rfl
  | tl, .id A t u, hint, s, ha => by
    rw [runT, runT]
    apply Option.bind_congr' (SM.onCopy_congr (runT_congrR false A _ s (by avd)))
    rintro ⟨⟨TA, _⟩, s₁⟩ _
    apply Option.bind_congr' (runT_congrR false t _ s (by avd))
    rintro ⟨r₁, s₁'⟩ _
    apply Option.bind_congr' (runT_congrR false u _ s (by avd))
    rintro ⟨r₂, s₂'⟩ _
    rfl
  | tl, .tind n args, hint, s, ha => by
    rw [runT, runT]
    cases hM : K.Γ.find? (·.name == n) with
    | none => rfl
    | some M =>
      have hMd : M ≠ d := fun e => by
        have h1 := find_name' hM
        have h2 := ha.1
        subst e
        simp [Term.mentionsType, h1] at h2
      apply SM.bind_congr (runParams_congrR M args 0 [] s
        (avoids_of_list (by simp_all [Avoids, Term.mentionsType]) (by simp_all [Avoids, Term.anyAtom])))
      intro _ _ _
      rw [DataModel.tyM, DataModel.tyM, recOf_R R hMd]
      rfl
  | tl, .call f args hd, hint, s, ha => by
    rw [runT, runT]
    dsimp only
    refine SM.erasedIf_congr ?_
    have hhead : SM.headOf f (fun p => SM.guarded (ContentOk K φ p) (readPlace K φ p true)) (runT K ρ φ false (.plain .err) f) s
        = SM.headOf f (fun p => SM.guarded (ContentOk (KR K d R) φ p) (readPlace (KR K d R) φ p true))
          (runT (KR K d R) ρ φ false (.plain .err) f) s :=
      SM.headOf_congr (fun p => by rw [readPlace_R]; rfl) (runT_congrR false f _ s (by avd))
    apply SM.bind_congr hhead
    intro fv s₁ _
    apply SM.bind_congr (runArgs_congrR _ _ args [] s₁
      (avoids_of_list (by simp_all [Avoids, Term.mentionsType]) (by simp_all [Avoids, Term.anyAtom])))
    intro _ _ _; rfl
  | tl, .matchNat p z u, hint, s, ha => by
    rw [runT, runT, tagOf_R, joinDrop_R, JoinDropOk_R, matchEntry_R, MatchEntryOk_R]
    refine SM.erasedIf_congr ?_
    dsimp only
    apply Option.bind_congr' rfl
    rintro ⟨tg, s₀⟩ _
    dsimp only
    apply Option.bind_congr' rfl
    intro _ _
    generalize matchEntry K φ (!tl) (.matchNat p z u) s₀ = me
    obtain ⟨s₁, lend⟩ := me
    dsimp only
    split
    · apply Option.bind_congr' (runT_congrR tl z (tailHint tl hint) s₁ (by avd))
      intro _ _; rfl
    · apply Option.bind_congr' (runT_congrR tl u (tailHint tl hint) s₁ (by avd))
      intro _ _; rfl
    · rfl
  | tl, .matchInd p n arms, hint, s, ha => by
    rw [runT, runT, tagOf_R, joinDrop_R, JoinDropOk_R, matchEntry_R, MatchEntryOk_R]
    refine SM.erasedIf_congr ?_
    dsimp only
    apply Option.bind_congr' rfl
    rintro ⟨tg, s₀⟩ _
    dsimp only
    apply Option.bind_congr' rfl
    intro _ _
    generalize matchEntry K φ (!tl && !tg.isProof && !oneCtor K.Γ n) (.matchInd p n arms) s₀ = me
    obtain ⟨s₁, lend⟩ := me
    dsimp only
    have harms := avoids_of_arms (n := d.name) (as := arms) (by simp_all [Avoids, Term.mentionsType])
      (by simp_all [Avoids, Term.anyAtom])
    split
    · rename_i c _
      apply Option.bind_congr' (runArm_congrR tl arms (tailHint tl hint) c s₁ harms)
      intro _ _; rfl
    · split
      · exact SM.anyArm_congr fun c => runArm_congrR tl arms (tailHint tl hint) c s₁ harms
      · rfl
  | tl, .letIn x u w, hint, s, ha => by
    rw [runT, runT]
    refine SM.erasedIf_congr ?_
    apply Option.bind_congr' (runT_congrR false u _ s (by avd))
    rintro ⟨⟨v, T⟩, s₁⟩ _
    dsimp only
    apply Option.bind_congr' (runT_congrR tl w (tailHint tl hint) _ (by avd))
    intro _ _; rfl
  | tl, .assign p u, hint, s, ha => by
    rw [runT, runT, lentOk_R K d R φ, contentOf_R, placeTy_R, assignAt_R, invalidate_R, InvalidateOk_R]
    refine SM.erasedIf_congr ?_
    dsimp only
    apply Option.bind_congr' (runT_congrR false u _ _ (by avd))
    intro _ _; rfl
  | tl, .pi hs ds c, hint, s, ha => by
    rw [runT, runT]
    have hbs := runBinds_congrR s (K.D.paramDecls (scopeOf s) ds) ds [] []
      (avoids_of_list (by simp_all [Avoids, Term.mentionsType]) (by simp_all [Avoids, Term.anyAtom]))
    have hc : ∀ bs rs acc, runT K ρ φ false (.plain .err) c (extendBy s bs rs acc) = runT (KR K d R) ρ φ false (.plain .err) c (extendBy s bs rs acc) :=
      fun bs rs acc => runT_congrR false c _ _ (by avd)
    dsimp only
    rw [hbs]
    cases c with
    | ref U =>
      have hU : ∀ bs rs acc, runT K ρ φ false (.plain .err) U (extendBy s bs rs acc) = runT (KR K d R) ρ φ false (.plain .err) U (extendBy s bs rs acc) :=
        fun bs rs acc => runT_congrR false U _ _ (by avd)
      simp only [hU]
      rfl
    | _ => simp only [hc]; rfl
  | tl, .ctor ty c hh ps args, hint, s, ha => by
    rw [runT, runT]
    refine SM.erasedIf_congr ?_
    cases hM : K.Γ.find? (·.name == ty) with
    | none => rfl
    | some M =>
      have hMd : M ≠ d := fun e => by
        have h1 := find_name' hM
        have h2 := ha.1
        subst e
        simp [Term.mentionsType, h1] at h2
      apply SM.bind_congr (runParams_congrR M ps 0 [] s
        (avoids_of_list (by simp_all [Avoids, Term.mentionsType]) (by simp_all [Avoids, Term.anyAtom])))
      intro psM s₁ h1
      have e := runParams_state K ρ φ M ps 0 [] s s₁ psM h1
      subst e
      dsimp only
      rw [recOf_R R hMd]
      exact SM.bind_congr (runFields_congrR _ M hMd c args 0 _ _ [] s₁
        (avoids_of_list (by simp_all [Avoids, Term.mentionsType]) (by simp_all [Avoids, Term.anyAtom])))
        (fun _ _ _ => rfl)
  | tl, .prim n args, hint, s, ha => by
    have havl := avoids_of_list (ts := args) (n := d.name) (by simp_all [Avoids, Term.mentionsType])
      (by simp_all [Avoids, Term.anyAtom])
    have hallT : ∀ t ∈ args, ∀ (tl' : Bool) (hint : TyS) (s : SState),
        runT K ρ φ tl' hint t s = runT (KR K d R) ρ φ tl' hint t s := fun t hm tl' hint s =>
      runAll_congrR args t hm tl' hint s (havl t hm)
    have hall : ∀ t ∈ args, ∀ (hint : TyS) (s : SState),
        run K ρ φ hint t s = run (KR K d R) ρ φ hint t s := fun t hm hint s => hallT t hm false hint s
    have hprem : ∀ xs : List Term, (∀ x ∈ xs, x ∈ args) →
        SM.onCopy (xs.foldr (fun t k => runT K ρ φ false (.plain TyM.err) t >>= fun _ => k)
          (pure ((.proof, .plain (TyM.prop True)) : Res))) s =
        SM.onCopy (xs.foldr (fun t k => runT (KR K d R) ρ φ false (.plain TyM.err) t >>= fun _ => k)
          (pure ((.proof, .plain (TyM.prop True)) : Res))) s := fun xs hxs =>
      SM.onCopy_congr (premises_congr_all xs (fun x hx s' => hall x (hxs x hx) _ s') s)
    by_cases e1 : ∃ h, n = "symm" ∧ args = [h]
    · obtain ⟨h0, rfl, hargs⟩ := e1; subst hargs; rw [runT, runT]; exact hprem [h0] (by simp)
    by_cases e2 : ∃ h k, n = "trans" ∧ args = [h, k]
    · obtain ⟨h0, k0, rfl, hargs⟩ := e2; subst hargs; rw [runT, runT]; exact hprem [h0, k0] (by simp)
    by_cases e3 : ∃ h u, n = "rewrite" ∧ args = [h, u]
    · obtain ⟨h0, u0, rfl, hargs⟩ := e3; subst hargs; rw [runT, runT]; exact hprem [h0, u0] (by simp)
    by_cases e4 : ∃ h u, n = "rewriteR" ∧ args = [h, u]
    · obtain ⟨h0, u0, rfl, hargs⟩ := e4; subst hargs; rw [runT, runT]; exact hprem [h0, u0] (by simp)
    by_cases hJ : ∃ A a b P h t, n = "J" ∧ args = [A, a, b, P, h, t]
    · obtain ⟨A, a, b, P, h', t, rfl, hargs⟩ := hJ
      have hm : ∀ x, x ∈ [A, a, b, P, h', t] → x ∈ args := fun x hx => by rw [hargs]; exact hx
      rw [hargs, runT, runT, matchEntry_R, MatchEntryOk_R, joinDrop_R, JoinDropOk_R]
      refine SM.erasedIf_congr ?_
      apply SM.bind_congr (SM.onCopy_congr (hall A (hm A (by simp)) _ s))
      intro _ s₁ e1; have e := SM.onCopy_state e1; subst e
      apply SM.bind_congr (SM.onCopy_congr (hall a (hm a (by simp)) _ _))
      intro _ s₂ e2; have e := SM.onCopy_state e2; subst e
      apply SM.bind_congr (SM.onCopy_congr (hall b (hm b (by simp)) _ _))
      intro _ s₃ e3; have e := SM.onCopy_state e3; subst e
      apply SM.bind_congr (SM.onCopy_congr (hall P (hm P (by simp)) _ _))
      intro _ s₄ e4; have e := SM.onCopy_state e4; subst e
      apply SM.bind_congr (SM.onCopy_congr (hall h' (hm h' (by simp)) _ _))
      intro _ s₅ e5; have e := SM.onCopy_state e5; subst e
      apply SM.bind_congr rfl
      intro _ s₆ e6; have e := SM.onCopy_state e6; subst e
      dsimp only
      rw [show ∀ (hh : TyS) s₀, runT K ρ φ false hh t s₀ = runT (KR K d R) ρ φ false hh t s₀ from
        fun hh s₀ => hall t (hm t (by simp)) hh s₀]
    by_cases hc : ∃ u, (n = "clone" ∨ n = "peek" ∨ n = "inplace") ∧ args = [u]
    · obtain ⟨u, hn, hargs⟩ := hc
      have hu : u ∈ args := by rw [hargs]; simp
      rcases hn with rfl | rfl | rfl <;>
        (rw [hargs, runT, runT]
         exact SM.erasedIf_congr (SM.headOf_congr (fun p => by rw [readPlace_R]; rfl) (hall u hu _ _)))
    by_cases hsp : ∃ f u, n = "split" ∧ args = [.const f, u]
    · obtain ⟨f, u, rfl, hargs⟩ := hsp
      have hu : u ∈ args := by rw [hargs]; simp
      rw [hargs, runT, runT]
      exact SM.erasedIf_congr (hallT u hu tl hint s)
    have hs' : ∀ f u, n = "split" → args = [.const f, u] → False := fun f u e1 e2 => hsp ⟨f, u, e1, e2⟩
    have hJ' : ∀ (A a b P h t : Term), n = "J" → args = [A, a, b, P, h, t] → False :=
      fun A a b P h t e1 e2 => hJ ⟨A, a, b, P, h, t, e1, e2⟩
    have hc1 : ∀ u, n = "clone" → args = [u] → False := fun u e1 e2 => hc ⟨u, .inl e1, e2⟩
    have hc2 : ∀ u, n = "peek" → args = [u] → False := fun u e1 e2 => hc ⟨u, .inr (.inl e1), e2⟩
    have hc3 : ∀ u, n = "inplace" → args = [u] → False := fun u e1 e2 => hc ⟨u, .inr (.inr e1), e2⟩
    have f1 : ∀ h, n = "symm" → args = [h] → False := fun h0 a b => e1 ⟨h0, a, b⟩
    have f2 : ∀ h k, n = "trans" → args = [h, k] → False := fun h0 k0 a b => e2 ⟨h0, k0, a, b⟩
    have f3 : ∀ h u, n = "rewrite" → args = [h, u] → False := fun h0 u0 a b => e3 ⟨h0, u0, a, b⟩
    have f4 : ∀ h u, n = "rewriteR" → args = [h, u] → False := fun h0 u0 a b => e4 ⟨h0, u0, a, b⟩
    rw [runT, runT]
    all_goals first | rfl | exact f1 | exact f2 | exact f3 | exact f4 | exact hJ' | exact hc1 | exact hc2 | exact hc3 | exact hs'
  | tl, .fix self hs ds c dec body, hint, s, ha => by
    have hbs : bindsOf K ρ φ s ds = bindsOf (KR K d R) ρ φ s ds :=
      runBinds_congrR s (K.D.paramDecls (scopeOf s) ds) ds [] []
        (avoids_of_list (by simp_all [Avoids, Term.mentionsType]) (by simp_all [Avoids, Term.anyAtom]))
    have hds : runDoms K ρ φ s ds = runDoms (KR K d R) ρ φ s ds := by unfold runDoms; rw [hbs]
    have hc : ∀ bs rs acc, runT K ρ φ false (.plain .err) c (extendBy s bs rs acc) = runT (KR K d R) ρ φ false (.plain .err) c (extendBy s bs rs acc) :=
      fun bs rs acc => runT_congrR false c _ _ (by avd)
    have hb : ∀ (hint : TyS) (s₂ : SState), runT K ρ φ true hint body s₂ = runT (KR K d R) ρ φ true hint body s₂ :=
      fun hint s₂ => runT_congrR true body hint s₂ (by avd)
    have hout : ∀ bs rs, codOf K ρ φ s bs rs c = codOf (KR K d R) ρ φ s bs rs c := by
      intro bs rs
      cases c with
      | ref U =>
        have hU : ∀ bs rs acc, runT K ρ φ false (.plain .err) U (extendBy s bs rs acc) = runT (KR K d R) ρ φ false (.plain .err) U (extendBy s bs rs acc) :=
          fun bs rs acc => runT_congrR false U _ _ (by avd)
        simp only [codOf, hU]
      | _ => simp only [codOf, hc]
    have hcod : ∀ bs rs, fixCod K ρ φ s bs rs c = fixCod (KR K d R) ρ φ s bs rs c := fun bs rs => by unfold fixCod; rw [hout]
    rw [run_fix_def, run_fix_def, hds, hbs, hout, hcod]
    rw [fixG_congrR K d R ρ φ hb]
    rfl

theorem runAll_congrR : ∀ (ts : List Term) (t : Term), t ∈ ts → ∀ (tl : Bool) (hint : TyS) (s : SState),
    Avoids d.name t → runT K ρ φ tl hint t s = runT (KR K d R) ρ φ tl hint t s
  | [], t, h, _, _, _, _ => absurd h List.not_mem_nil
  | a :: as, t, h, tl, hint, s, ha => by
    rw [List.mem_cons] at h
    rcases h with e | h
    · rw [e] at ha ⊢; exact runT_congrR tl a hint s ha
    · exact runAll_congrR as t h tl hint s ha

theorem runBinds_congrR (s : SState) (dcs : List DeclInfo) : ∀ (ds : List Term) (pre : List PBind) (rs : List Bool),
    (∀ a ∈ ds, Avoids d.name a) →
    runBinds K ρ φ s dcs pre rs ds = runBinds (KR K d R) ρ φ s dcs pre rs ds
  | [], _, _, _ => rfl
  | x :: ds, pre, rs, ha => by
    have hds := fun pre' rs' => runBinds_congrR s dcs ds pre' rs' (fun a h => ha a (List.mem_cons_of_mem _ h))
    have hx := ha x (List.mem_cons_self ..)
    have hd : (fun acc => runT K ρ φ false (.plain .err) x (extendBy s pre rs acc))
        = (fun acc => runT (KR K d R) ρ φ false (.plain .err) x (extendBy s pre rs acc)) :=
      funext fun acc => runT_congrR false x _ _ hx
    cases x with
    | ref A =>
      have hA : (fun acc => runT K ρ φ false (.plain .err) A (extendBy s pre rs acc))
          = (fun acc => runT (KR K d R) ρ φ false (.plain .err) A (extendBy s pre rs acc)) :=
        funext fun acc => runT_congrR false A _ _
          ⟨by simpa [Term.mentionsType] using hx.1, by simpa [Term.anyAtom] using hx.2⟩
      simp only [runBinds, hA, hds]
    | _ => simp only [runBinds, hd, hds]

theorem runArgs_congrR (stmt : Bool) (fT : TyM) :
    ∀ (args : List Term) (earlier : List Sem) (s : SState), (∀ a ∈ args, Avoids d.name a) →
    runArgs K ρ φ stmt fT earlier args s = runArgs (KR K d R) ρ φ stmt fT earlier args s
  | [], _, _, _ => rfl
  | a :: as, earlier, s, ha => by
    simp only [runArgs]
    apply SM.bind_congr (SM.stmtIf_congr (runT_congrR false a _ s (ha a (List.mem_cons_self ..))))
    intro r s₁ _
    apply SM.bind_congr (runArgs_congrR stmt fT as _ s₁ (fun b h => ha b (List.mem_cons_of_mem _ h)))
    intro _ _ _; rfl

theorem runFields_congrR (stmt : Bool) (M : IndDecl) (hMd : M ≠ d) (c : Nat) :
    ∀ (args : List Term) (i : Nat) (rh : Option Rec) (sol : List (Option Sem)) (earlier : List Sem) (s : SState),
    (∀ a ∈ args, Avoids d.name a) →
    runFields K ρ φ stmt M c i rh sol earlier args s = runFields (KR K d R) ρ φ stmt M c i rh sol earlier args s
  | [], _, _, _, _, _, _ => rfl
  | a :: as, i, rh, sol, earlier, s, ha => by
    simp only [runFields]
    rw [fieldTy_R R hMd]
    apply SM.bind_congr (SM.stmtIf_congr (runT_congrR false a _ s (ha a (List.mem_cons_self ..))))
    intro r s₁ _
    simp only [unifyTyS_indep (setRec K.dm d R) K.dm]
    apply SM.bind_congr (runFields_congrR stmt M hMd c as _ _ _ _ s₁ (fun b h => ha b (List.mem_cons_of_mem _ h)))
    intro _ _ _; rfl

theorem runParams_congrR (M : IndDecl) :
    ∀ (args : List Term) (i : Nat) (earlier : List Sem) (s : SState), (∀ a ∈ args, Avoids d.name a) →
    runParams K ρ φ M i earlier args s = runParams (KR K d R) ρ φ M i earlier args s
  | [], _, _, _, _ => rfl
  | a :: as, i, earlier, s, ha => by
    simp only [runParams]
    apply SM.bind_congr (SM.onCopy_congr (runT_congrR false a _ s (ha a (List.mem_cons_self ..))))
    intro r s₁ h1
    have e := SM.onCopy_state h1
    subst e
    apply SM.bind_congr (runParams_congrR M as _ _ _ (fun b h => ha b (List.mem_cons_of_mem _ h)))
    intro _ _ _; rfl

theorem runArm_congrR : ∀ (tl : Bool) (arms : List (Hint × Term)) (hint : TyS) (c : Nat) (s : SState),
    (∀ p ∈ arms, Avoids d.name p.2) →
    runArm K ρ φ tl hint c arms s = runArm (KR K d R) ρ φ tl hint c arms s
  | _, [], _, _, _, _ => rfl
  | tl, (h, t) :: rest, hint, c, s, ha => by
    simp only [runArm]
    split
    · exact runT_congrR tl t hint s (ha (h, t) (List.mem_cons_self ..))
    · exact runArm_congrR tl rest hint (c - 1) s (fun p hp => ha p (List.mem_cons_of_mem _ hp))
end

/-- `runT_congrR` the other way round, at a position that is not a tail. -/
theorem run_congrR (t : Term) (hint : TyS) (s : SState) (ha : Avoids d.name t) :
    runT (KR K d R) ρ φ false hint t s = runT K ρ φ false hint t s :=
  (runT_congrR K d R ρ φ false t hint s ha).symm

end

end Ochr.Meaning.DataModel.Exists.Knot
