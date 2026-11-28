import Ochr.Meaning.Steps.MasterMatch
import Ochr.Meaning.AccessAbsorb
import Ochr.Meaning.RunEnv
import Ochr.Meaning.Steps.JoinDropLib
import Ochr.Meaning.Strict.Good

/-!
# The split's facts about the model alone, proved (lead42, 2026-11-28; docs/31 D251)

`MatchReaccessM` and `MatchReaccessE` (the reference's match from the state after its own tag access is the match from
the start) and `ValsCongrA` (the embedded values' condition moves to an extension that agrees at the term's unknowns),
each a theorem with no hypothesis of its own.

The core of the first two is that the tag's access is IDEMPOTENT (`tagOf_again`): after `SState.access` nothing it
reaches is live (`access_post`: each round ends every reached live label and never makes one live, so the rounds settle
within the number of live labels), so the second access is the identity (`access_access`) and its strict test is vacuous
(`accessOk_post`); the access keeps the positions, so the place resolves alike (`resolve_access`), and it keeps the
types at positions (`tyAt_access`) and the readings (`scopeOf_access`).
-/

namespace Ochr.Meaning.Steps.Form.Master

open Ochr Ochr.Meaning Ochr.Meaning.Steps Ochr.Meaning.Steps.Form

/-! ## The access keeps what a match reads before it -/

/-- A state whose frames keep their bindings resolves variables alike. -/
theorem varPos_of_envLe' {s t : SState} (h : EnvLe s t) : t.varPos = s.varPos := by
  funext i
  unfold SState.varPos
  rw [List.getLast?_eq_getElem?, List.getLast?_eq_getElem?, h.1]
  have htop : t.topIdx = s.topIdx := by simp [SState.topIdx, h.1]
  rw [htop]
  cases hs : s.env[s.env.length - 1]? with
  | none =>
    have : t.env[s.env.length - 1]? = none := by
      have := h.1
      rw [List.getElem?_eq_none_iff] at hs ⊢; omega
    rw [this]
  | some fr =>
    obtain ⟨fr', h1, h2, -⟩ := h.2 _ fr hs
    rw [h1]; simp [h2, SState.topIdx]

/-- [Access] keeps where a place resolves. -/
theorem resolve_access (s : SState) (p : Pos) (hit : List Step → Bool) (q : Place) :
    resolve (s.access p hit) q = resolve s q := by
  simp only [resolve, varPos_of_envLe' (envLe_access s p hit)]

/-- [Access] keeps the top frame's readings. -/
theorem scopeOf_access (s : SState) (p : Pos) (hit : List Step → Bool) : scopeOf (s.access p hit) = scopeOf s :=
  scopeOf_of_declsOf (declsOf_access s p hit)

/-- After [Access] of `p`, a second [Access] of `p` makes no end: its strict test holds. -/
theorem accessOk_post (K : RunCtx) (φ : Future) (s : SState) (p : Pos) (hit : List Step → Bool) :
    AccessOk K φ (s.access p hit) p hit := by
  have hnil : ((s.access p hit).liveLabels.filter ((s.access p hit).reached p hit)) = [] :=
    List.filter_eq_nil_iff.mpr fun l hl => by
      simp [SState.access_post s p hit l hl]
  have hround : accRound p hit (s.access p hit) = s.access p hit := by
    unfold accRound; rw [hnil]; rfl
  have hk : ∀ k, (List.range k).foldl (fun t _ => accRound p hit t) (s.access p hit) = s.access p hit := by
    intro k
    induction k with
    | zero => rfl
    | succ k ih => rw [List.range_succ, List.foldl_append, ih]; exact hround
  intro k _
  rw [hk k, hnil]
  trivial

/-- **The tag's access is idempotent**: from the state after a match's access for its tag, the strict test holds and
the tag is read again, the same, leaving the same state. -/
theorem tagOf_again {K : RunCtx} {φ : Future} {p : Place} {tag : Sem → TyS → Sem} {s sA : SState} {tg : Sem}
    (htag : tagOf K φ p tag s = some (tg, sA)) : TagOk K φ p sA ∧ tagOf K φ p tag sA = some (tg, sA) := by
  unfold tagOf at htag
  cases hr : resolve s p with
  | none => rw [hr] at htag; cases htag
  | some ps =>
    obtain ⟨pos, steps⟩ := ps
    rw [hr] at htag
    simp only [Option.some.injEq, Prod.mk.injEq] at htag
    obtain ⟨rfl, rfl⟩ := htag
    have hr' : resolve (s.access pos (tagHit steps)) p = some (pos, steps) := by rw [resolve_access]; exact hr
    refine ⟨?_, ?_⟩
    · unfold TagOk; rw [hr']; exact accessOk_post K φ s pos (tagHit steps)
    · unfold tagOf; rw [hr']
      simp only [SState.access_access, Strict.tyAt_access]

/-- The tag's access keeps the readings. -/
theorem scopeOf_tagOf {K : RunCtx} {φ : Future} {p : Place} {tag : Sem → TyS → Sem} {s sA : SState} {tg : Sem}
    (htag : tagOf K φ p tag s = some (tg, sA)) : scopeOf sA = scopeOf s := by
  unfold tagOf at htag
  cases hr : resolve s p with
  | none => rw [hr] at htag; cases htag
  | some ps =>
    obtain ⟨pos, steps⟩ := ps
    rw [hr] at htag
    simp only [Option.some.injEq, Prod.mk.injEq] at htag
    obtain ⟨-, rfl⟩ := htag
    exact scopeOf_access s pos (tagHit steps)

/-! ## `MatchReaccessM`, `MatchReaccessE`: PROVED -/

/-- **`MatchReaccessM`, proved** (a fact about the model alone; no hypothesis): where the table does not erase the match,
the reference's match from the state after its own tag access is the match from the start. -/
theorem matchReaccessM : MatchReaccessM := by
  intro K ρ φ tl hint p z u s sA tg hfl hT htag
  obtain ⟨hTA, htagA⟩ := tagOf_again htag
  have hsc := scopeOf_tagOf htag
  rw [runT]
  simp only [hsc, hfl, SM.erasedIf, SM.stmtIf, Bool.false_eq_true, if_false]
  rw [SM.guarded_of hTA, SM.guarded_of hT, htagA, htag]

/-- **`MatchReaccessE`, proved** (a fact about the model alone; no hypothesis): the reference's match from the state
after its own tag access gives the result of the match from the start, whether or not the table erases it (an erased
match restores the state it started from, so only the results agree). -/
theorem matchReaccessE : MatchReaccessE := by
  intro K ρ φ tl hint p z u s sA tg hT htag
  obtain ⟨hTA, htagA⟩ := tagOf_again htag
  have hsc := scopeOf_tagOf htag
  rw [runT]
  simp only [hsc]
  generalize K.D.flags (scopeOf s) (.matchNat p z u) = fl
  simp only [SM.erasedIf, SM.stmtIf]
  rw [SM.guarded_of hTA, SM.guarded_of hT, htagA, htag]
  rcases fl with ⟨a, b⟩
  cases b
  · cases a <;> simp only [Bool.false_eq_true, if_false, if_true, Option.map_map] <;> rfl
  · simp only [if_true]
    split <;> simp_all

/-! ## `ValsCongrA`: PROVED -/

section
variable {P Q : Value → Prop} {A : Nat → Prop}

/-- Abbreviation: the atoms of `t` are among those `A` holds at. -/
private abbrev AOn (A : Nat → Prop) (t : Term) : Prop := ∀ σ, t.anyAtom (· == .abs σ) = true → A σ

mutual
/-- `valsOk` moves from `P` to `Q` when, at each embedded value whose unknowns `A` holds at, `P` gives `Q`. -/
theorem valsOk_imp (hPQ : ∀ v, P v → (∀ σ, v.anyAtom (· == .abs σ) = true → A σ) → Q v) :
    ∀ (t : Term), AOn A t → t.valsOk P → t.valsOk Q
  | .place _, _, _ => by simp [Term.valsOk]
  | .borrow _, _, _ => by simp [Term.valsOk]
  | .const _, _, _ => by simp [Term.valsOk]
  | .sort _, _, _ => by simp [Term.valsOk]
  | .nat, _, _ => by simp [Term.valsOk]
  | .zero, _, _ => by simp [Term.valsOk]
  | .unit, _, _ => by simp [Term.valsOk]
  | .tt, _, _ => by simp [Term.valsOk]
  | .val v, hA, h => by
    simp only [Term.valsOk] at h ⊢
    exact hPQ v h fun σ hσ => hA σ (by simp [Term.anyAtom, hσ])
  | .assign _ t, hA, h => by
    simp only [Term.valsOk] at h ⊢
    exact valsOk_imp hPQ t (fun σ hσ => hA σ (by simp [Term.anyAtom, hσ])) h
  | .succ t, hA, h => by
    simp only [Term.valsOk] at h ⊢
    exact valsOk_imp hPQ t (fun σ hσ => hA σ (by simp [Term.anyAtom, hσ])) h
  | .ref t, hA, h => by
    simp only [Term.valsOk] at h ⊢
    exact valsOk_imp hPQ t (fun σ hσ => hA σ (by simp [Term.anyAtom, hσ])) h
  | .letIn _ t u, hA, h => by
    simp only [Term.valsOk] at h ⊢
    exact ⟨valsOk_imp hPQ t (fun σ hσ => hA σ (by simp [Term.anyAtom, hσ])) h.1,
      valsOk_imp hPQ u (fun σ hσ => hA σ (by simp [Term.anyAtom, hσ])) h.2⟩
  | .seq t u, hA, h => by
    simp only [Term.valsOk] at h ⊢
    exact ⟨valsOk_imp hPQ t (fun σ hσ => hA σ (by simp [Term.anyAtom, hσ])) h.1,
      valsOk_imp hPQ u (fun σ hσ => hA σ (by simp [Term.anyAtom, hσ])) h.2⟩
  | .cong t u, hA, h => by
    simp only [Term.valsOk] at h ⊢
    exact ⟨valsOk_imp hPQ t (fun σ hσ => hA σ (by simp [Term.anyAtom, hσ])) h.1,
      valsOk_imp hPQ u (fun σ hσ => hA σ (by simp [Term.anyAtom, hσ])) h.2⟩
  | .ascribe t u, hA, h => by
    simp only [Term.valsOk] at h ⊢
    exact ⟨valsOk_imp hPQ t (fun σ hσ => hA σ (by simp [Term.anyAtom, hσ])) h.1,
      valsOk_imp hPQ u (fun σ hσ => hA σ (by simp [Term.anyAtom, hσ])) h.2⟩
  | .matchNat _ t u, hA, h => by
    simp only [Term.valsOk] at h ⊢
    exact ⟨valsOk_imp hPQ t (fun σ hσ => hA σ (by simp [Term.anyAtom, hσ])) h.1,
      valsOk_imp hPQ u (fun σ hσ => hA σ (by simp [Term.anyAtom, hσ])) h.2⟩
  | .eq a b c, hA, h => by
    simp only [Term.valsOk] at h ⊢
    exact ⟨valsOk_imp hPQ a (fun σ hσ => hA σ (by simp [Term.anyAtom, hσ])) h.1,
      valsOk_imp hPQ b (fun σ hσ => hA σ (by simp [Term.anyAtom, hσ])) h.2.1,
      valsOk_imp hPQ c (fun σ hσ => hA σ (by simp [Term.anyAtom, hσ])) h.2.2⟩
  | .id a b c, hA, h => by
    simp only [Term.valsOk] at h ⊢
    exact ⟨valsOk_imp hPQ a (fun σ hσ => hA σ (by simp [Term.anyAtom, hσ])) h.1,
      valsOk_imp hPQ b (fun σ hσ => hA σ (by simp [Term.anyAtom, hσ])) h.2.1,
      valsOk_imp hPQ c (fun σ hσ => hA σ (by simp [Term.anyAtom, hσ])) h.2.2⟩
  | .pi _ ds c, hA, h => by
    simp only [Term.valsOk] at h ⊢
    exact ⟨valsOkList_imp hPQ ds (fun σ hσ => hA σ (by simp [Term.anyAtom, hσ])) h.1,
      valsOk_imp hPQ c (fun σ hσ => hA σ (by simp [Term.anyAtom, hσ])) h.2⟩
  | .fix _ _ ds c _ b, hA, h => by
    simp only [Term.valsOk] at h ⊢
    exact ⟨valsOkList_imp hPQ ds (fun σ hσ => hA σ (by simp [Term.anyAtom, hσ])) h.1,
      valsOk_imp hPQ c (fun σ hσ => hA σ (by simp [Term.anyAtom, hσ])) h.2.1,
      valsOk_imp hPQ b (fun σ hσ => hA σ (by simp [Term.anyAtom, hσ])) h.2.2⟩
  | .call f as _, hA, h => by
    simp only [Term.valsOk] at h ⊢
    exact ⟨valsOk_imp hPQ f (fun σ hσ => hA σ (by simp [Term.anyAtom, hσ])) h.1,
      valsOkList_imp hPQ as (fun σ hσ => hA σ (by simp [Term.anyAtom, hσ])) h.2⟩
  | .prim _ as, hA, h => by
    simp only [Term.valsOk] at h ⊢
    exact valsOkList_imp hPQ as (fun σ hσ => hA σ (by simp [Term.anyAtom, hσ])) h
  | .tind _ as, hA, h => by
    simp only [Term.valsOk] at h ⊢
    exact valsOkList_imp hPQ as (fun σ hσ => hA σ (by simp [Term.anyAtom, hσ])) h
  | .ctor _ _ _ ps as, hA, h => by
    simp only [Term.valsOk] at h ⊢
    exact ⟨valsOkList_imp hPQ ps (fun σ hσ => hA σ (by simp [Term.anyAtom, hσ])) h.1,
      valsOkList_imp hPQ as (fun σ hσ => hA σ (by simp [Term.anyAtom, hσ])) h.2⟩
  | .matchInd _ _ arms, hA, h => by
    simp only [Term.valsOk] at h ⊢
    exact valsOkArms_imp hPQ arms (fun σ hσ => hA σ (by simp [Term.anyAtom, hσ])) h
termination_by structural t => t

theorem valsOkList_imp (hPQ : ∀ v, P v → (∀ σ, v.anyAtom (· == .abs σ) = true → A σ) → Q v) :
    ∀ (ts : List Term), (∀ σ, Term.anyAtomList (· == .abs σ) ts = true → A σ) →
      Term.valsOkList P ts → Term.valsOkList Q ts
  | [], _, _ => by simp [Term.valsOkList]
  | t :: ts, hA, h => by
    simp only [Term.valsOkList] at h ⊢
    exact ⟨valsOk_imp hPQ t (fun σ hσ => hA σ (by simp [Term.anyAtomList, hσ])) h.1,
      valsOkList_imp hPQ ts (fun σ hσ => hA σ (by simp [Term.anyAtomList, hσ])) h.2⟩
termination_by structural ts => ts

theorem valsOkArms_imp (hPQ : ∀ v, P v → (∀ σ, v.anyAtom (· == .abs σ) = true → A σ) → Q v) :
    ∀ (ts : List (Hint × Term)), (∀ σ, Term.anyAtomArms (· == .abs σ) ts = true → A σ) →
      Term.valsOkArms P ts → Term.valsOkArms Q ts
  | [], _, _ => by simp [Term.valsOkArms]
  | (_, t) :: ts, hA, h => by
    simp only [Term.valsOkArms] at h ⊢
    exact ⟨valsOk_imp hPQ t (fun σ hσ => hA σ (by simp [Term.anyAtomArms, hσ])) h.1,
      valsOkArms_imp hPQ ts (fun σ hσ => hA σ (by simp [Term.anyAtomArms, hσ])) h.2⟩
termination_by structural ts => ts
end

end

/-- **`ValsCongrA`, proved** (a fact about the model alone; no hypothesis): at each embedded value the reference's run
reads only the unknowns the value holds (`runT_congrA`), and the fundamental lemma's form (`FundAt`) reads only the data
model, the declarations and the future, which the extension keeps. -/
theorem valsCongrA : ValsCongrA := by
  intro K Δ' ρ ρ' φ t hA h
  refine valsOk_imp (A := AgreeA K Δ' ρ ρ') (fun v hv hav => ?_) t hA h
  intro tl hint
  have e : runT (KA K Δ') ρ' φ tl hint (.val v) = runT K ρ φ tl hint (.val v) :=
    funext fun s => (runT_congrA K Δ' ρ ρ' φ tl (.val v) hint s fun σ hσ => hav σ hσ).symm
  show Strict.FundAt K.dm K.Γ φ (runT (KA K Δ') ρ' φ tl hint (.val v))
  rw [e]
  exact hv tl hint

/-! ## The split at the end of a body, with the model facts proved -/

/-- **`TStepMatchNat` in general, with its three model facts proved** (`matchReaccessM`, `matchReaccessE`,
`valsCongrA`): ASSUMES 9 facts: `TailMatchNatInv`, `JoinContInv` (checker); `MatchFlagsT`, `ProofJoinG` (table; the
latter also the checker's `joinCont`); `MatchTagG`, `WorldRefineG`, `JoinContG`, `GenTailG` (mixed); `ProofArmM`
(model, at the instance's table); and `Strict.FundCtx K`. -/
theorem tStepMatchNat_from {K : RunCtx} {φ : Future} (hInv : TailMatchNatInv) (hJI : JoinContInv)
    (hMF : MatchFlagsT K.D) (hPJ : ProofJoinG K.D) (hTag : MatchTagG) (hW : WorldRefineG) (hJ : JoinContG)
    (hG : GenTailG) (hPA : ProofArmM K) (hc : Strict.FundCtx K) : TStepMatchNat K φ :=
  tStepMatchNat_of hInv hJI hMF hPJ hTag hW hJ hG matchReaccessM matchReaccessE hPA valsCongrA hc

end Ochr.Meaning.Steps.Form.Master
