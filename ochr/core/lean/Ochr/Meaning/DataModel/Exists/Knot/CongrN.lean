import Ochr.Meaning.DataModel.Exists.Knot.Congr

/-!
# The run's congruence in the model and the globals, at the names a term mentions (exists9)

`Congr.runT_congrR` changes ONE declaration's records and needs the term to avoid that declaration
and to hold no embedded value. The assembly needs more (docs/34 §18.13, points 2 (a) and (b)):
* a later declaration's PARAMETER TYPES change between stages, not only its records;
* the models of two stages differ at every later declaration at once, and at declarations off the
  program's list (a model is a function on all declarations);
* the globals differ: a later stage has more of them;
* the program meaning's congruence runs a definition's body and reads its stored type (`globalTyS`,
  a `Value`), which holds embedded closures, Π-types and constructor values.

So the congruence here compares `K` with `KN K dm' C'` (another model and other globals, the same
declaration list, decisions, Δ, Λ) on a term whose names pass three tests (`NameOk`):
* `ty`: the names of its applied types (`.tind`, a value `.tInd`). At the declaration such a name
  finds, the two models must agree on parameter types, and on records only at parameter lists that
  pass `paramsOk` (the run reads `tyM` only after that test): this lets the assembly compare a
  declaration's records with their canonical form, which differs only off the typed lists;
* `rc`: the names of its constructors (`.ctor`, a value `.ind`): the models agree on records and
  parameter types (a bare constructor's record is read at parameters solved from small readings);
* `gl`: its globals (`.const`, a value `.gfn`): the two `global` tables agree.
A match reads only the declaration list (`oneCtor`), so its declaration's name is not tested.

The proof follows `Congr.runT_congrR` clause by clause, with `AssignCongr.runT_congrA`'s clauses for
embedded values. The helpers that navigate values read the model only through its signature
(`follow_indep`, `updAt_indep`, `pmem_indep`) and never read the globals.
-/

namespace Ochr.Meaning.DataModel.Exists.Knot

open Ochr Ochr.Meaning
open Classical

/-- The three name tests (see the module docstring). -/
structure NameOk where
  ty : String → Bool
  rc : String → Bool
  gl : String → Bool

mutual
/-- Every name the term mentions passes its test, inside embedded values included. -/
def Term.nok (N : NameOk) : Term → Bool
  | .tind m as => N.ty m && Term.nokList N as
  | .ctor t _ _ ps as => N.rc t && Term.nokList N ps && Term.nokList N as
  | .const g => N.gl g
  | .val v => Value.nok N v
  | .assign _ t | .succ t | .ref t => Term.nok N t
  | .letIn _ t u | .seq t u | .cong t u | .ascribe t u => Term.nok N t && Term.nok N u
  | .matchNat _ z s => Term.nok N z && Term.nok N s
  | .pi _ ds c => Term.nokList N ds && Term.nok N c
  | .fix _ _ ds c _ b => Term.nokList N ds && Term.nok N c && Term.nok N b
  | .call f as _ => Term.nok N f && Term.nokList N as
  | .eq a b c | .id a b c => Term.nok N a && Term.nok N b && Term.nok N c
  | .prim _ as => Term.nokList N as
  | .matchInd _ _ as => Term.nokArms N as
  | _ => true
termination_by structural t => t

def Term.nokList (N : NameOk) : List Term → Bool
  | [] => true
  | t :: ts => Term.nok N t && Term.nokList N ts
termination_by structural ts => ts

def Term.nokArms (N : NameOk) : List (Hint × Term) → Bool
  | [] => true
  | (_, t) :: ts => Term.nok N t && Term.nokArms N ts
termination_by structural ts => ts

def Value.nok (N : NameOk) : Value → Bool
  | .gfn n => N.gl n
  | .succ w | .tRef w | .borrow _ w | .gloan _ w => Value.nok N w
  | .tEq A a b => Value.nok N A && Value.nok N a && Value.nok N b
  | .clo cs t rd | .tPi cs t rd => Value.nokList N cs && Term.nok N t && Value.nokRd N rd
  | .sealed t => Term.nok N t
  | .ind ty _ _ ps fs => N.rc ty && Value.nokList N ps && Value.nokList N fs
  | .tInd n fs => N.ty n && Value.nokList N fs
  | _ => true
termination_by structural v => v

def Value.nokList (N : NameOk) : List Value → Bool
  | [] => true
  | v :: vs => Value.nok N v && Value.nokList N vs
termination_by structural vs => vs

def Value.nokRd (N : NameOk) : List (DeclInfo × Value) → Bool
  | [] => true
  | (_, v) :: vs => Value.nok N v && Value.nokRd N vs
termination_by structural vs => vs
end

/-- `K` with another model and other globals. -/
noncomputable abbrev KN (K : RunCtx) (dm' : DataModel) (C' : CodeMeaning) : RunCtx := { K with dm := dm', C := C' }

/-- **What the two contexts must agree on**, at the declarations the names find in `K.Γ`. -/
structure AgreeN (K : RunCtx) (dm' : DataModel) (C' : CodeMeaning) (N : NameOk) : Prop where
  ty : ∀ n M, N.ty n = true → K.Γ.find? (·.name == n) = some M →
    dm'.paramTy M = K.dm.paramTy M ∧ ∀ ps, paramsOk K.dm M ps → dm'.recOf M ps = K.dm.recOf M ps
  rc : ∀ n M, N.rc n = true → K.Γ.find? (·.name == n) = some M →
    dm'.recOf M = K.dm.recOf M ∧ dm'.paramTy M = K.dm.paramTy M
  gl : ∀ n, N.gl n = true → C'.global n = K.C.global n

theorem paramsOk_congr {dm dm' : DataModel} {M : IndDecl} (h : dm'.paramTy M = dm.paramTy M) (ps : List Sem) :
    paramsOk dm' M ps = paramsOk dm M ps := by
  unfold paramsOk; rw [h]; rfl

section
variable (K : RunCtx) (dm' : DataModel) (C' : CodeMeaning) (φ : Future)

theorem lentOk_N : lentOk (KN K dm' C') φ = lentOk K φ := by
  funext p s; unfold lentOk StateOk; rw [pmem_indep (KN K dm' C').dm K.dm]; rfl

theorem obsAt_N : obsAt (KN K dm' C') = obsAt K := by
  funext T steps ob x; unfold obsAt; rw [follow_indep (KN K dm' C').dm K.dm] <;> rfl

theorem contentOf_N : contentOf (KN K dm' C') φ = contentOf K φ := by
  funext p s; unfold contentOf; rw [follow_indep (KN K dm' C').dm K.dm] <;> rfl

theorem setContent_N : setContent (KN K dm' C') φ = setContent K φ := by
  funext pos steps v s; unfold setContent; rw [updAt_indep (KN K dm' C').dm K.dm] <;> rfl

theorem borrowPlace_N : borrowPlace (KN K dm' C') φ = borrowPlace K φ := by
  funext p s; unfold borrowPlace; rw [contentOf_N, updAt_indep (KN K dm' C').dm K.dm] <;> rfl

theorem dropAt_N : dropAt (KN K dm' C') φ = dropAt K φ := by
  funext q pos steps s; unfold dropAt; rw [updAt_indep (KN K dm' C').dm K.dm] <;> rfl

theorem DropOk_N : DropOk (KN K dm' C') φ = DropOk K φ := by
  funext q pos steps s; unfold DropOk; rw [updAt_indep (KN K dm' C').dm K.dm] <;> rfl

theorem tagOf_N : tagOf (KN K dm' C') φ = tagOf K φ := by
  funext p tag s; unfold tagOf; rw [obsAt_N] <;> rfl

theorem assignAt_N : assignAt (KN K dm' C') φ = assignAt K φ := by
  funext p v lab s; unfold assignAt; rw [setContent_N] <;> rfl

theorem readPlace_N : readPlace (KN K dm' C') φ = readPlace K φ := by
  funext p copy s; unfold readPlace; rw [contentOf_N, setContent_N] <;> rfl

theorem invalidateOne_N : invalidateOne (KN K dm' C') φ = invalidateOne K φ := by
  funext s q; unfold invalidateOne; rw [setContent_N] <;> rfl

theorem invalidate_N : invalidate (KN K dm' C') φ = invalidate K φ := by
  funext p s; unfold invalidate; rw [invalidateOne_N] <;> rfl

theorem InvalidateOk_N : InvalidateOk (KN K dm' C') φ = InvalidateOk K φ := by
  funext p s; unfold InvalidateOk; rw [invalidateOne_N] <;> rfl

theorem placeTy_N : placeTy (KN K dm' C') φ = placeTy K φ := by
  funext p s; unfold placeTy; rw [contentOf_N] <;> rfl

theorem entryCap_N : entryCap (KN K dm' C') φ = entryCap K φ := by
  funext s qk; unfold entryCap; rw [invalidate_N] <;> rfl

theorem entryAccess_N : entryAccess (KN K dm' C') φ = entryAccess K φ := by
  funext bc s; unfold entryAccess; rw [entryCap_N] <;> rfl

theorem matchEntry_N : matchEntry (KN K dm' C') φ = matchEntry K φ := by
  funext ent mt s; unfold matchEntry; rw [entryAccess_N] <;> rfl

theorem EntryCapOk_N : EntryCapOk (KN K dm' C') φ = EntryCapOk K φ := by
  funext s qk; unfold EntryCapOk; rw [InvalidateOk_N] <;> rfl

theorem EntryAccessOk_N : EntryAccessOk (KN K dm' C') φ = EntryAccessOk K φ := by
  funext bc s; unfold EntryAccessOk; rw [entryCap_N, EntryCapOk_N] <;> rfl

theorem MatchEntryOk_N : MatchEntryOk (KN K dm' C') φ = MatchEntryOk K φ := by
  funext ent mt s; unfold MatchEntryOk; rw [EntryAccessOk_N] <;> rfl

theorem joinDrop_N : joinDrop (KN K dm' C') φ = joinDrop K φ := by
  funext entry t s; unfold joinDrop; rw [dropAt_N] <;> rfl

theorem JoinStepOk_N : JoinStepOk (KN K dm' C') φ = JoinStepOk K φ := by
  funext s q; unfold JoinStepOk; rw [DropOk_N] <;> rfl

theorem JoinDropOk_N : JoinDropOk (KN K dm' C') φ = JoinDropOk K φ := by
  funext entry t s; unfold JoinDropOk; rw [JoinStepOk_N, dropAt_N] <;> rfl

end

/-! ## The `.fix` clause's pieces -/

section
variable (K : RunCtx) (dm' : DataModel) (C' : CodeMeaning) (ρ : Assignment) (φ : Future)

theorem fixBodyAt_congrN {body : Term} {fb : List PBind × PBind}
    (hb : ∀ hint s₂, runT K ρ φ true hint body s₂ = runT (KN K dm' C') ρ φ true hint body s₂)
    (s : SState) (ps : List PiDom) (out : PiCod) (piT : TyM) (start : Nat) (selfM : Sem) (args : List Sem) :
    fixBodyAt K ρ φ fb s ps out piT start body selfM args = fixBodyAt (KN K dm' C') ρ φ fb s ps out piT start body selfM args := by
  unfold fixBodyAt
  dsimp only
  generalize (args.zip ps).foldl (fixStep fb) (s.under.pushBind { ty := .plain piT, val := fun _ => selfM, decl := .pi fb.2.2 }, [], []) = F
  obtain ⟨s₂, acc, cells⟩ := F
  dsimp only
  rw [hb]
  rfl

theorem fixStage_congrN {body : Term} {fb : List PBind × PBind}
    (hb : ∀ hint s₂, runT K ρ φ true hint body s₂ = runT (KN K dm' C') ρ φ true hint body s₂)
    (l : Nat) (s : SState) (ps : List PiDom) (out : PiCod) (dec : Option Nat) (start : Nat) :
    ∀ k, fixStage K ρ φ fb l s ps out dec start body k = fixStage (KN K dm' C') ρ φ fb l s ps out dec start body k
  | 0 => rfl
  | k + 1 => by
    show fixBodyAt K ρ φ fb s ps out _ start body
        (closureAt K.dm.read l φ ps _ (stageFn l ps (fixRank dec) k (fixStage K ρ φ fb l s ps out dec start body k)))
      = fixBodyAt (KN K dm' C') ρ φ fb s ps out _ start body
        (closureAt K.dm.read l φ ps _ (stageFn l ps (fixRank dec) k (fixStage (KN K dm' C') ρ φ fb l s ps out dec start body k)))
    rw [fixStage_congrN hb l s ps out dec start k]
    funext args
    exact fixBodyAt_congrN K dm' C' ρ φ hb s ps out _ start _ args

theorem fixG_congrN {body : Term} {fb : List PBind × PBind}
    (hb : ∀ hint s₂, runT K ρ φ true hint body s₂ = runT (KN K dm' C') ρ φ true hint body s₂)
    (l : Nat) (s : SState) (ps : List PiDom) (out : PiCod) (piT : TyM) (start : Nat) (dec : Option Nat) :
    fixG K ρ φ fb l s ps out piT start dec body = fixG (KN K dm' C') ρ φ fb l s ps out piT start dec body := by
  funext args
  show fixStage K ρ φ fb l s ps out dec start body (fixRank dec args + 1) args
    = fixStage (KN K dm' C') ρ φ fb l s ps out dec start body (fixRank dec args + 1) args
  rw [fixStage_congrN K dm' C' ρ φ hb]

end

/-! ## Names of sub-terms -/

theorem nok_of_list {N : NameOk} : ∀ {ts : List Term}, Term.nokList N ts = true → ∀ t ∈ ts, Term.nok N t = true
  | [], _, t, h => absurd h List.not_mem_nil
  | a :: as, h1, t, h => by
    simp only [Term.nokList, Bool.and_eq_true] at h1
    rcases List.mem_cons.1 h with rfl | h
    · exact h1.1
    · exact nok_of_list h1.2 t h

theorem nok_of_arms {N : NameOk} : ∀ {as : List (Hint × Term)}, Term.nokArms N as = true → ∀ p ∈ as, Term.nok N p.2 = true
  | [], _, p, h => absurd h List.not_mem_nil
  | a :: as, h1, p, h => by
    simp only [Term.nokArms, Bool.and_eq_true] at h1
    rcases List.mem_cons.1 h with rfl | h
    · exact h1.1
    · exact nok_of_arms h1.2 p h

set_option hygiene false in
/-- The names of a sub-term pass when the term's do (`ha` names the term's test). -/
macro "nk" : tactic => `(tactic| (simp only [Term.nok, Term.nokList, Term.nokArms, Value.nok, Value.nokList,
  Value.nokRd, Bool.and_eq_true] at ha ⊢; simp only [ha]))

set_option hygiene false in
/-- The same for a value (`hv`). -/
macro "nkv" : tactic => `(tactic| (simp only [Term.nok, Term.nokList, Term.nokArms, Value.nok, Value.nokList,
  Value.nokRd, Bool.and_eq_true] at hv ⊢; simp only [hv]))

/-! ## The congruence -/

section
variable (K : RunCtx) (dm' : DataModel) (C' : CodeMeaning) (N : NameOk) (ρ : Assignment) (φ : Future)
set_option linter.unusedSectionVars false
variable (hA : AgreeN K dm' C' N)
include hA

mutual
/-- **The run's congruence at the names a term mentions**: a term whose names pass `N` runs the same
under `K` and under `K` with another model and other globals that agree with `K`'s at those names
(`AgreeN`). -/
theorem runT_congrN : ∀ (tl : Bool) (t : Term) (hint : TyS) (s : SState), Term.nok N t = true →
    runT K ρ φ tl hint t s = runT (KN K dm' C') ρ φ tl hint t s
  | tl, .place p, hint, s, ha => by rw [runT, runT, readPlace_N K dm' C' φ]; rfl
  | tl, .borrow p, hint, s, ha => by
    rw [runT, runT, lentOk_N K dm' C' φ, borrowPlace_N K dm' C' φ, invalidate_N K dm' C' φ, InvalidateOk_N K dm' C' φ]; rfl
  | tl, .seq u w, hint, s, ha => by
    rw [runT, runT]
    refine SM.erasedIf_congr ?_
    apply SM.bind_congr (runT_congrN false u _ s (by nk))
    intro a s₁ _
    apply SM.bind_congr rfl
    intro _ s₂ _
    exact runT_congrN tl w (tailHint tl hint) _ (by nk)
  | tl, .succ u, hint, s, ha => by
    rw [runT, runT]
    refine SM.erasedIf_congr ?_
    refine SM.strictS_congr ?_
    apply SM.bind_congr (runT_congrN false u _ s (by nk))
    intro a s₁ _; rfl
  | tl, .ref A, hint, s, ha => by
    rw [runT, runT]
    refine SM.erasedIf_congr ?_
    refine SM.strictS_congr ?_
    apply SM.bind_congr (runT_congrN false A _ s (by nk))
    intro a s₁ _; rfl
  | tl, .const n, hint, s, ha => by
    rw [runT, runT]
    have hg := hA.gl n (by simpa [Term.nok] using ha)
    show some (K.C.global n, s) = some (C'.global n, s)
    rw [hg]
  | tl, .sort l, hint, s, ha => by rw [runT, runT]
  | tl, .nat, hint, s, ha => by rw [runT, runT]
  | tl, .unit, hint, s, ha => by rw [runT, runT]
  | tl, .zero, hint, s, ha => by rw [runT, runT]
  | tl, .tt, hint, s, ha => by rw [runT, runT]
  | tl, .cong f g, hint, s, ha => by
    rw [runT, runT]
    have hg : ∀ s, runT K ρ φ false (.plain .err) g s = runT (KN K dm' C') ρ φ false (.plain .err) g s :=
      fun s => runT_congrN false g _ s (by nk)
    exact SM.onCopy_congr (premises_congr_all [g] (fun y hy => by rw [List.mem_singleton.mp hy]; exact hg) s)
  | tl, .val v, hint, s, ha => by
    have hv : Value.nok N v = true := by simpa [Term.nok] using ha
    rw [runT_val_def, runT_val_def, meanV_congrN v hint hv]
    cases v with
    | clo caps t rd =>
      simp only [valT]
      rw [capsVals_congrN caps (by nkv), capsTys_congrN rd (by nkv), runT_congrN false t _ _ (by nkv)]
      rfl
    | sealed t =>
      simp only [valT]
      rw [runT_congrN false t hint _ (by nkv)]
      rfl
    | gfn n =>
      simp only [valT]
      rw [hA.gl n (by simpa [Value.nok] using hv)]
      rfl
    | ind ty c h ps fs =>
      simp only [valT]
      cases hM : K.Γ.find? (·.name == ty) with
      | none => rfl
      | some M =>
        obtain ⟨hr, hp⟩ := hA.rc ty M (by simp only [Value.nok, Bool.and_eq_true] at hv; exact hv.1.1) hM
        have hP := meanParams_congrN M hp ps 0 [] (by simp only [Value.nok, Bool.and_eq_true] at hv; exact hv.1.2)
        simp only [hP, hr]
        rfl
    | _ => rfl
  | tl, .ascribe u A, hint, s, ha => by
    rw [runT, runT]
    refine SM.erasedIf_congr ?_
    refine SM.strictS_congr ?_
    apply SM.bind_congr (SM.onCopy_congr (runT_congrN false A _ s (by nk)))
    rintro ⟨TA, _⟩ s₁ h1
    have e := SM.onCopy_state h1
    subst e
    apply SM.bind_congr (runT_congrN false u _ _ (by nk))
    intro _ _ _; rfl
  | tl, .eq A a b, hint, s, ha => by
    rw [runT, runT]
    apply SM.onCopy_congr
    apply SM.bind_congr (runT_congrN false A _ s (by nk))
    rintro ⟨TA, _⟩ s₁ _
    apply SM.bind_congr (SM.onCopy_congr (runT_congrN false a _ s₁ (by nk)))
    rintro ⟨va, _⟩ s₂ h2
    have e := SM.onCopy_state h2
    subst e
    apply SM.bind_congr (SM.onCopy_congr (runT_congrN false b _ _ (by nk)))
    intro _ _ _; rfl
  | tl, .id A t u, hint, s, ha => by
    rw [runT, runT]
    apply Option.bind_congr' (SM.onCopy_congr (runT_congrN false A _ s (by nk)))
    rintro ⟨⟨TA, _⟩, s₁⟩ _
    apply Option.bind_congr' (runT_congrN false t _ s (by nk))
    rintro ⟨r₁, s₁'⟩ _
    apply Option.bind_congr' (runT_congrN false u _ s (by nk))
    rintro ⟨r₂, s₂'⟩ _
    rfl
  | tl, .tind n args, hint, s, ha => by
    rw [runT, runT]
    cases hM : K.Γ.find? (·.name == n) with
    | none => rfl
    | some M =>
      obtain ⟨hp, hr⟩ := hA.ty n M (by simp only [Term.nok, Bool.and_eq_true] at ha; exact ha.1) hM
      have hp' : (KN K dm' C').dm.paramTy M = K.dm.paramTy M := hp
      apply SM.bind_congr (runParams_congrN M args 0 [] s
        (nok_of_list (by simp only [Term.nok, Bool.and_eq_true] at ha; exact ha.2)))
      intro psM s₁ _
      simp only [paramsOk_congr hp']
      by_cases hok : paramsOk K.dm M psM
      · have hr' : dm'.recOf M psM = K.dm.recOf M psM := hr psM hok
        simp only [hok, if_true, DataModel.tyM, hr']
        rfl
      · simp only [hok, if_false]
  | tl, .call f args hd, hint, s, ha => by
    rw [runT, runT]
    dsimp only
    refine SM.erasedIf_congr ?_
    have hhead : SM.headOf f (fun p => SM.guarded (ContentOk K φ p) (readPlace K φ p true)) (runT K ρ φ false (.plain .err) f) s
        = SM.headOf f (fun p => SM.guarded (ContentOk (KN K dm' C') φ p) (readPlace (KN K dm' C') φ p true))
          (runT (KN K dm' C') ρ φ false (.plain .err) f) s :=
      SM.headOf_congr (fun p => by rw [readPlace_N K dm' C' φ]; rfl) (runT_congrN false f _ s (by nk))
    apply SM.bind_congr hhead
    intro fv s₁ _
    apply SM.bind_congr (runArgs_congrN _ _ args [] s₁
      (nok_of_list (by simp only [Term.nok, Bool.and_eq_true] at ha; exact ha.2)))
    intro _ _ _; rfl
  | tl, .matchNat p z u, hint, s, ha => by
    rw [runT, runT, tagOf_N K dm' C' φ, joinDrop_N K dm' C' φ, JoinDropOk_N K dm' C' φ, matchEntry_N K dm' C' φ, MatchEntryOk_N K dm' C' φ]
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
    · apply Option.bind_congr' (runT_congrN tl z (tailHint tl hint) s₁ (by nk))
      intro _ _; rfl
    · apply Option.bind_congr' (runT_congrN tl u (tailHint tl hint) s₁ (by nk))
      intro _ _; rfl
    · rfl
  | tl, .matchInd p n arms, hint, s, ha => by
    rw [runT, runT, tagOf_N K dm' C' φ, joinDrop_N K dm' C' φ, JoinDropOk_N K dm' C' φ, matchEntry_N K dm' C' φ, MatchEntryOk_N K dm' C' φ]
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
    have harms := nok_of_arms (N := N) (as := arms) (by simpa [Term.nok] using ha)
    split
    · rename_i c _
      apply Option.bind_congr' (runArm_congrN tl arms (tailHint tl hint) c s₁ harms)
      intro _ _; rfl
    · split
      · exact SM.anyArm_congr fun c => runArm_congrN tl arms (tailHint tl hint) c s₁ harms
      · rfl
  | tl, .letIn x u w, hint, s, ha => by
    rw [runT, runT]
    refine SM.erasedIf_congr ?_
    apply Option.bind_congr' (runT_congrN false u _ s (by nk))
    rintro ⟨⟨v, T⟩, s₁⟩ _
    dsimp only
    apply Option.bind_congr' (runT_congrN tl w (tailHint tl hint) _ (by nk))
    intro _ _; rfl
  | tl, .assign p u, hint, s, ha => by
    rw [runT, runT, lentOk_N K dm' C' φ, contentOf_N K dm' C' φ, placeTy_N K dm' C' φ, assignAt_N K dm' C' φ, invalidate_N K dm' C' φ, InvalidateOk_N K dm' C' φ]
    refine SM.erasedIf_congr ?_
    dsimp only
    apply Option.bind_congr' (runT_congrN false u _ _ (by nk))
    intro _ _; rfl
  | tl, .pi hs ds c, hint, s, ha => by
    rw [runT, runT]
    have hbs := runBinds_congrN s (K.D.paramDecls (scopeOf s) ds) ds [] []
      (nok_of_list (by simp only [Term.nok, Bool.and_eq_true] at ha; exact ha.1))
    have hc : ∀ bs rs acc, runT K ρ φ false (.plain .err) c (extendBy s bs rs acc) = runT (KN K dm' C') ρ φ false (.plain .err) c (extendBy s bs rs acc) :=
      fun bs rs acc => runT_congrN false c _ _ (by nk)
    dsimp only
    rw [hbs]
    cases c with
    | ref U =>
      have hU : ∀ bs rs acc, runT K ρ φ false (.plain .err) U (extendBy s bs rs acc) = runT (KN K dm' C') ρ φ false (.plain .err) U (extendBy s bs rs acc) :=
        fun bs rs acc => runT_congrN false U _ _ (by nk)
      simp only [hU]
      rfl
    | _ => simp only [hc]; rfl
  | tl, .ctor ty c hh ps args, hint, s, ha => by
    rw [runT, runT]
    refine SM.erasedIf_congr ?_
    cases hM : K.Γ.find? (·.name == ty) with
    | none => rfl
    | some M =>
      obtain ⟨hr, hp⟩ := hA.rc ty M (by simp only [Term.nok, Bool.and_eq_true] at ha; exact ha.1.1) hM
      have hr' : (KN K dm' C').dm.recOf M = K.dm.recOf M := hr
      have hp' : (KN K dm' C').dm.paramTy M = K.dm.paramTy M := hp
      apply SM.bind_congr (runParams_congrN M ps 0 [] s
        (nok_of_list (by simp only [Term.nok, Bool.and_eq_true] at ha; exact ha.1.2)))
      intro psM s₁ h1
      have e := runParams_state K ρ φ M ps 0 [] s s₁ psM h1
      subst e
      dsimp only
      rw [hr']
      exact SM.bind_congr (runFields_congrN _ M hr' c args 0 _ _ [] s₁
        (nok_of_list (by simp only [Term.nok, Bool.and_eq_true] at ha; exact ha.2)))
        (fun _ _ _ => by simp only [paramsOk_congr hp']; rfl)
  | tl, .prim n args, hint, s, ha => by
    have havl := nok_of_list (ts := args) (N := N) (by simpa [Term.nok] using ha)
    have hallT : ∀ t ∈ args, ∀ (tl' : Bool) (hint : TyS) (s : SState),
        runT K ρ φ tl' hint t s = runT (KN K dm' C') ρ φ tl' hint t s := fun t hm tl' hint s =>
      runAll_congrN args t hm tl' hint s (havl t hm)
    have hall : ∀ t ∈ args, ∀ (hint : TyS) (s : SState),
        run K ρ φ hint t s = run (KN K dm' C') ρ φ hint t s := fun t hm hint s => hallT t hm false hint s
    have hprem : ∀ xs : List Term, (∀ x ∈ xs, x ∈ args) →
        SM.onCopy (xs.foldr (fun t k => runT K ρ φ false (.plain TyM.err) t >>= fun _ => k)
          (pure ((.proof, .plain (TyM.prop True)) : Res))) s =
        SM.onCopy (xs.foldr (fun t k => runT (KN K dm' C') ρ φ false (.plain TyM.err) t >>= fun _ => k)
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
      rw [hargs, runT, runT, matchEntry_N K dm' C' φ, MatchEntryOk_N K dm' C' φ, joinDrop_N K dm' C' φ, JoinDropOk_N K dm' C' φ]
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
      rw [show ∀ (hh : TyS) s₀, runT K ρ φ false hh t s₀ = runT (KN K dm' C') ρ φ false hh t s₀ from
        fun hh s₀ => hall t (hm t (by simp)) hh s₀]
    by_cases hc : ∃ u, (n = "clone" ∨ n = "peek" ∨ n = "inplace") ∧ args = [u]
    · obtain ⟨u, hn, hargs⟩ := hc
      have hu : u ∈ args := by rw [hargs]; simp
      rcases hn with rfl | rfl | rfl <;>
        (rw [hargs, runT, runT]
         exact SM.erasedIf_congr (SM.headOf_congr (fun p => by rw [readPlace_N K dm' C' φ]; rfl) (hall u hu _ _)))
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
    have hds0 := nok_of_list (by simp only [Term.nok, Bool.and_eq_true] at ha; exact ha.1.1)
    have hbs : bindsOf K ρ φ s ds = bindsOf (KN K dm' C') ρ φ s ds :=
      runBinds_congrN s (K.D.paramDecls (scopeOf s) ds) ds [] [] hds0
    have hds : runDoms K ρ φ s ds = runDoms (KN K dm' C') ρ φ s ds := by unfold runDoms; rw [hbs]
    have hc : ∀ bs rs acc, runT K ρ φ false (.plain .err) c (extendBy s bs rs acc) = runT (KN K dm' C') ρ φ false (.plain .err) c (extendBy s bs rs acc) :=
      fun bs rs acc => runT_congrN false c _ _ (by nk)
    have hb : ∀ (hint : TyS) (s₂ : SState), runT K ρ φ true hint body s₂ = runT (KN K dm' C') ρ φ true hint body s₂ :=
      fun hint s₂ => runT_congrN true body hint s₂ (by nk)
    have hout : ∀ bs rs, codOf K ρ φ s bs rs c = codOf (KN K dm' C') ρ φ s bs rs c := by
      intro bs rs
      cases c with
      | ref U =>
        have hU : ∀ bs rs acc, runT K ρ φ false (.plain .err) U (extendBy s bs rs acc) = runT (KN K dm' C') ρ φ false (.plain .err) U (extendBy s bs rs acc) :=
          fun bs rs acc => runT_congrN false U _ _ (by nk)
        simp only [codOf, hU]
      | _ => simp only [codOf, hc]
    have hcod : ∀ bs rs, fixCod K ρ φ s bs rs c = fixCod (KN K dm' C') ρ φ s bs rs c := fun bs rs => by unfold fixCod; rw [hout]
    rw [run_fix_def, run_fix_def, hds, hbs, hout, hcod]
    rw [fixG_congrN K dm' C' ρ φ hb]
    rfl

theorem runAll_congrN : ∀ (ts : List Term) (t : Term), t ∈ ts → ∀ (tl : Bool) (hint : TyS) (s : SState),
    Term.nok N t = true → runT K ρ φ tl hint t s = runT (KN K dm' C') ρ φ tl hint t s
  | [], t, h, _, _, _, _ => absurd h List.not_mem_nil
  | a :: as, t, h, tl, hint, s, ha => by
    rw [List.mem_cons] at h
    rcases h with e | h
    · rw [e] at ha ⊢; exact runT_congrN tl a hint s ha
    · exact runAll_congrN as t h tl hint s ha

theorem runBinds_congrN (s : SState) (dcs : List DeclInfo) : ∀ (ds : List Term) (pre : List PBind) (rs : List Bool),
    (∀ a ∈ ds, Term.nok N a = true) →
    runBinds K ρ φ s dcs pre rs ds = runBinds (KN K dm' C') ρ φ s dcs pre rs ds
  | [], _, _, _ => rfl
  | x :: ds, pre, rs, hds => by
    have hds' := fun pre' rs' => runBinds_congrN s dcs ds pre' rs' (fun a h => hds a (List.mem_cons_of_mem _ h))
    have ha := hds x (List.mem_cons_self ..)
    have hd : (fun acc => runT K ρ φ false (.plain .err) x (extendBy s pre rs acc))
        = (fun acc => runT (KN K dm' C') ρ φ false (.plain .err) x (extendBy s pre rs acc)) :=
      funext fun acc => runT_congrN false x _ _ ha
    cases x with
    | ref A =>
      have hA' : (fun acc => runT K ρ φ false (.plain .err) A (extendBy s pre rs acc))
          = (fun acc => runT (KN K dm' C') ρ φ false (.plain .err) A (extendBy s pre rs acc)) :=
        funext fun acc => runT_congrN false A _ _ (by nk)
      simp only [runBinds, hA', hds']
    | _ => simp only [runBinds, hd, hds']

theorem runArgs_congrN (stmt : Bool) (fT : TyM) :
    ∀ (args : List Term) (earlier : List Sem) (s : SState), (∀ a ∈ args, Term.nok N a = true) →
    runArgs K ρ φ stmt fT earlier args s = runArgs (KN K dm' C') ρ φ stmt fT earlier args s
  | [], _, _, _ => rfl
  | a :: as, earlier, s, ha => by
    simp only [runArgs]
    apply SM.bind_congr (SM.stmtIf_congr (runT_congrN false a _ s (ha a (List.mem_cons_self ..))))
    intro r s₁ _
    apply SM.bind_congr (runArgs_congrN stmt fT as _ s₁ (fun b h => ha b (List.mem_cons_of_mem _ h)))
    intro _ _ _; rfl

theorem runFields_congrN (stmt : Bool) (M : IndDecl) (hr : (KN K dm' C').dm.recOf M = K.dm.recOf M) (c : Nat) :
    ∀ (args : List Term) (i : Nat) (rh : Option Rec) (sol : List (Option Sem)) (earlier : List Sem) (s : SState),
    (∀ a ∈ args, Term.nok N a = true) →
    runFields K ρ φ stmt M c i rh sol earlier args s = runFields (KN K dm' C') ρ φ stmt M c i rh sol earlier args s
  | [], _, _, _, _, _, _ => rfl
  | a :: as, i, rh, sol, earlier, s, ha => by
    have hF : (KN K dm' C').dm.fieldTy M = K.dm.fieldTy M := by
      funext ps c i e; unfold DataModel.fieldTy; rw [hr]; rfl
    simp only [runFields]
    rw [hF]
    apply SM.bind_congr (SM.stmtIf_congr (runT_congrN false a _ s (ha a (List.mem_cons_self ..))))
    intro r s₁ _
    simp only [unifyTyS_indep (KN K dm' C').dm K.dm]
    apply SM.bind_congr (runFields_congrN stmt M hr c as _ _ _ _ s₁ (fun b h => ha b (List.mem_cons_of_mem _ h)))
    intro _ _ _; rfl

theorem runParams_congrN (M : IndDecl) :
    ∀ (args : List Term) (i : Nat) (earlier : List Sem) (s : SState), (∀ a ∈ args, Term.nok N a = true) →
    runParams K ρ φ M i earlier args s = runParams (KN K dm' C') ρ φ M i earlier args s
  | [], _, _, _, _ => rfl
  | a :: as, i, earlier, s, ha => by
    simp only [runParams]
    apply SM.bind_congr (SM.onCopy_congr (runT_congrN false a _ s (ha a (List.mem_cons_self ..))))
    intro r s₁ h1
    have e := SM.onCopy_state h1
    subst e
    apply SM.bind_congr (runParams_congrN M as _ _ _ (fun b h => ha b (List.mem_cons_of_mem _ h)))
    intro _ _ _; rfl

theorem runArm_congrN : ∀ (tl : Bool) (arms : List (Hint × Term)) (hint : TyS) (c : Nat) (s : SState),
    (∀ p ∈ arms, Term.nok N p.2 = true) →
    runArm K ρ φ tl hint c arms s = runArm (KN K dm' C') ρ φ tl hint c arms s
  | _, [], _, _, _, _ => rfl
  | tl, (h, t) :: rest, hint, c, s, ha => by
    simp only [runArm]
    split
    · exact runT_congrN tl t hint s (ha (h, t) (List.mem_cons_self ..))
    · exact runArm_congrN tl rest hint (c - 1) s (fun p hp => ha p (List.mem_cons_of_mem _ hp))

theorem meanV_congrN : ∀ (v : Value) (hint : TyS), Value.nok N v = true →
    meanV K ρ φ hint v = meanV (KN K dm' C') ρ φ hint v
  | .abs σ, hint, hv => rfl
  | .gfn n, hint, hv => by
    show (K.C.global n).1 = (C'.global n).1
    rw [hA.gl n (by simpa [Value.nok] using hv)]
  | .succ w, hint, hv => by
    show (meanV K ρ φ _ w).succ = (meanV (KN K dm' C') ρ φ _ w).succ
    rw [meanV_congrN w _ (by nkv)]
  | .borrow _ w, hint, hv => by
    show meanV K ρ φ hint w = meanV (KN K dm' C') ρ φ hint w
    exact meanV_congrN w hint (by nkv)
  | .gloan _ w, hint, hv => by
    show meanV K ρ φ hint w = meanV (KN K dm' C') ρ φ hint w
    exact meanV_congrN w hint (by nkv)
  | .tRef A, hint, hv => by
    show meanV K ρ φ _ A = meanV (KN K dm' C') ρ φ _ A
    exact meanV_congrN A _ (by nkv)
  | .tEq A a b, hint, hv => by
    rw [meanV, meanV]
    rw [meanV_congrN A _ (by nkv), meanV_congrN a _ (by nkv), meanV_congrN b _ (by nkv)]
    rfl
  | .clo caps t rd, hint, hv => by
    rw [meanV, meanV]
    rw [capsVals_congrN caps (by nkv), capsTys_congrN rd (by nkv), runT_congrN false t _ _ (by nkv)]
    rfl
  | .tPi caps t rd, hint, hv => by
    rw [meanV, meanV]
    rw [capsVals_congrN caps (by nkv), capsTys_congrN rd (by nkv), runT_congrN false t _ _ (by nkv)]
    rfl
  | .sealed t, hint, hv => by
    rw [meanV, meanV]
    rw [runT_congrN false t _ _ (by nkv)]
  | .ind ty c h ps fs, hint, hv => by
    rw [meanV, meanV]
    dsimp only
    cases hM : K.Γ.find? (·.name == ty) with
    | none => rfl
    | some M =>
      obtain ⟨hr, hp⟩ := hA.rc ty M (by simp only [Value.nok, Bool.and_eq_true] at hv; exact hv.1.1) hM
      dsimp only
      rw [meanParams_congrN M hp ps _ _ (by simp only [Value.nok, Bool.and_eq_true] at hv; exact hv.1.2), hr]
      split
      · rename_i r' _
        rw [meanFields_congrN M r' c fs _ _ (by simp only [Value.nok, Bool.and_eq_true] at hv; exact hv.2)]
      · rfl
  | .tInd n args, hint, hv => by
    rw [meanV, meanV]
    dsimp only
    cases hM : K.Γ.find? (·.name == n) with
    | none => rfl
    | some M =>
      obtain ⟨hp, hr⟩ := hA.ty n M (by simp only [Value.nok, Bool.and_eq_true] at hv; exact hv.1) hM
      dsimp only
      rw [meanParams_congrN M hp args _ _ (by simp only [Value.nok, Bool.and_eq_true] at hv; exact hv.2)]
      simp only [paramsOk_congr hp]
      by_cases hok : paramsOk K.dm M (meanParams (KN K dm' C') ρ φ M 0 [] args)
      · have hr' : dm'.recOf M (meanParams (KN K dm' C') ρ φ M 0 [] args)
            = K.dm.recOf M (meanParams (KN K dm' C') ρ φ M 0 [] args) := hr _ hok
        simp only [hok, if_true, DataModel.tyM, hr']
        rfl
      · simp only [hok, if_false]
  | .zero, _, _ => rfl
  | .unit, _, _ => rfl
  | .bot, _, _ => rfl
  | .loan _, _, _ => rfl
  | .proof, _, _ => rfl
  | .tNat, _, _ => rfl
  | .tUnit, _, _ => rfl
  | .sort _, _, _ => rfl

theorem capsVals_congrN : ∀ (vs : List Value), Value.nokList N vs = true →
    capsVals K ρ φ vs = capsVals (KN K dm' C') ρ φ vs
  | [], _ => rfl
  | v :: vs, hv => by
    simp only [capsVals]
    rw [meanV_congrN v _ (by nkv), capsVals_congrN vs (by nkv)]

theorem capsTys_congrN : ∀ (rd : List (DeclInfo × Value)), Value.nokRd N rd = true →
    capsTys K ρ φ rd = capsTys (KN K dm' C') ρ φ rd
  | [], _ => rfl
  | (d, T) :: rest, hv => by
    simp only [capsTys]
    rw [meanV_congrN T _ (by nkv), capsTys_congrN rest (by nkv)]

theorem meanFields_congrN (d : IndDecl) (r : Rec) (c : Nat) :
    ∀ (vs : List Value) (i : Nat) (earlier : List Sem), Value.nokList N vs = true →
    meanFields K ρ φ d r c i earlier vs = meanFields (KN K dm' C') ρ φ d r c i earlier vs
  | [], _, _, _ => rfl
  | v :: vs, i, earlier, hv => by
    simp only [meanFields]
    rw [meanV_congrN v _ (by nkv), meanFields_congrN d r c vs _ _ (by nkv)]
    rfl

theorem meanParams_congrN (d : IndDecl) (hp : dm'.paramTy d = K.dm.paramTy d) :
    ∀ (vs : List Value) (i : Nat) (earlier : List Sem), Value.nokList N vs = true →
    meanParams K ρ φ d i earlier vs = meanParams (KN K dm' C') ρ φ d i earlier vs
  | [], _, _, _ => rfl
  | v :: vs, i, earlier, hv => by
    have hp' : (KN K dm' C').dm.paramTy d = K.dm.paramTy d := hp
    simp only [meanParams]
    rw [hp', meanV_congrN v _ (by nkv), meanParams_congrN d hp vs _ _ (by nkv)]
end

/-- `runT_congrN` at a position that is not a tail. -/
theorem run_congrN (t : Term) (hint : TyS) (s : SState) (ht : Term.nok N t = true) :
    run K ρ φ hint t s = run (KN K dm' C') ρ φ hint t s :=
  runT_congrN K dm' C' N ρ φ hA false t hint s ht

end

end Ochr.Meaning.DataModel.Exists.Knot
