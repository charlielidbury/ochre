import Ochr.Meaning.Steps.Machine.FragRuns
import Ochr.Meaning.Steps.Machine.FragFacts

/-!
# The end of one borrow in a fragment environment (machine lane)

`endBorrow l` and `endTopLoan l` where the environment holds fragment values, `loan_l` at `px` only
and `borrow_l c` (`c` a number) at `ph` only (`FEnd`): the result is `endE` (`ph ↦ ⊥`, `px ↦ c`).
The general form of `VarEndInv.lean`'s two-binding lemmas: `mapState` walked over any list of
positions (`runs_mapState_fold`), the fold computed where the map is the identity but at one
position (`setAtE_valAt_self`). The shared core of `VarLentInv`, `BorrowLentInv`, `DropBorrowInv`,
`AssignVarInv`, `SeqBorInv`.
-/

namespace Ochr.Meaning.Steps.Machine

open Ochr Ochr.Meaning Ochr.Meaning.Steps Ochr.Meaning.DecideScope Ochr.Meaning.Steps.Slice
open Ochr.Meaning.Steps.Form

theorem setAtE_valAt_self {E : Env} {p : Pos} (hp : p ∈ allPos E) : Env.setAtE E p (valAt E p) = E := by
  cases p with
  | bind f i =>
    obtain ⟨fr, b, hf, hb⟩ := mem_allPos_bind E f i hp
    have hv : valAt E (.bind f i) = b.val := by
      show (E[f]!).binds[i]!.val = _; rw [binds_get! (by rw [hf]; exact hb)]
    rw [hv]
    apply Array.ext_getElem?
    intro k
    simp only [Env.setAtE, Array.getElem?_modify]
    split
    · subst_vars; rw [hf]; simp only [Option.map_some, Option.some.injEq]
      congr 1
      apply Array.ext_getElem?
      intro m
      simp only [Array.getElem?_modify]
      split
      · subst_vars; rw [hb]; rfl
      · rfl
    · rfl
  | temp f i =>
    obtain ⟨fr, hf, hi⟩ := mem_allPos_temp E f i hp
    have hv : valAt E (.temp f i) = fr.temps[i] := by
      rw [valAt_temp_eq]; simp [hf, Array.getElem?_eq_getElem hi]
    rw [hv]
    apply Array.ext_getElem?
    intro k
    simp only [Env.setAtE, Array.getElem?_modify]
    split
    · subst_vars; rw [hf]; simp only [Option.map_some, Option.some.injEq]
      congr 1
      simp [Array.set!, hi, Array.setIfInBounds, Array.set_getElem_self]
    · rfl

/-- A fold of writes that each write a position's own value back is the identity. -/
theorem foldl_setAtE_id {φ : Value → Value} :
    ∀ (L : List Pos) (E : Env), (∀ q ∈ L, q ∈ allPos E) → (∀ q ∈ L, φ (valAt E q) = valAt E q) →
      L.foldl (fun E p => Env.setAtE E p (φ (valAt E p))) E = E
  | [], _, _, _ => rfl
  | q :: L, E, hm, hφ => by
    rw [List.foldl_cons, hφ q (.head _), setAtE_valAt_self (hm q (.head _))]
    exact foldl_setAtE_id L E (fun q' h => hm q' (.tail _ h)) (fun q' h => hφ q' (.tail _ h))

/-- The fold over the positions where the map moves only `px`'s value. -/
theorem foldl_setAtE_one {φ : Value → Value} {E : Env} {px : Pos} (hpx : px ∈ allPos E)
    (hφ : ∀ q ∈ allPos E, q ≠ px → φ (valAt E q) = valAt E q)
    (hφx : ∀ q ∈ allPos E, q ≠ px → φ (valAt (Env.setAtE E px (φ (valAt E px))) q) = valAt (Env.setAtE E px (φ (valAt E px))) q) :
    (allPos E).foldl (fun E p => Env.setAtE E p (φ (valAt E p))) E = Env.setAtE E px (φ (valAt E px)) := by
  obtain ⟨L1, L2, hsplit⟩ := List.append_of_mem hpx
  have hnd := allPos_nodup E
  rw [hsplit] at hnd
  have hnd' := List.nodup_append.mp hnd
  have h1 : px ∉ L1 := fun h => by
    have := hnd'.2.2 px h px (.head _); exact this rfl
  have h2 : px ∉ L2 := (List.nodup_cons.mp hnd'.2.1).1
  rw [hsplit, List.foldl_append, List.foldl_cons]
  rw [foldl_setAtE_id L1 E (fun q h => by rw [hsplit]; exact List.mem_append_left _ h)
    (fun q h => hφ q (by rw [hsplit]; exact List.mem_append_left _ h) (fun e => h1 (e ▸ h)))]
  refine foldl_setAtE_id L2 _ (fun q h => ?_) (fun q h => hφx q (by rw [hsplit]; exact List.mem_append_right _ (.tail _ h)) (fun e => h2 (e ▸ h)))
  rw [allPos_setAtE, hsplit]; exact List.mem_append_right _ (.tail _ h)

/-- A `for` loop over positions whose body sets each position to `φ` of its value. -/
theorem runs_forIn_fold {body : Pos → PUnit → M (ForInStep PUnit)} {φ : Value → Value} {P : Value → Prop}
    (hP : ∀ v, P v → P (φ v))
    (hbody : ∀ p (s s' : MState) b r, p ∈ allPos s.env → (∀ q ∈ allPos s.env, P (valAt s.env q)) →
      Runs (body p PUnit.unit) s b r s' → r = .yield PUnit.unit ∧ s' = { s with env := Env.setAtE s.env p (φ (valAt s.env p)) }) :
    ∀ (L : List Pos) (s s' : MState) (b : Nat) (u : PUnit), (∀ q ∈ allPos s.env, P (valAt s.env q)) → (∀ q ∈ L, q ∈ allPos s.env) →
      Runs (forIn L PUnit.unit body) s b u s' → s' = { s with env := L.foldl (fun E p => Env.setAtE E p (φ (valAt E p))) s.env }
  | [], s, s', b, u, _, _, h => by
    simp only [List.forIn_nil] at h
    obtain ⟨-, rfl⟩ := runs_pure_inv h
    rfl
  | p :: L, s, s', b, u, hs, hm, h => by
    simp only [List.forIn_cons] at h
    obtain ⟨x, s₁, b₁, h1, hrest⟩ := Runs.bind_inv h
    obtain ⟨rfl, rfl⟩ := hbody p s s₁ b x (hm p (.head _)) hs h1
    simp only at hrest
    have hs' : ∀ q ∈ allPos (Env.setAtE s.env p (φ (valAt s.env p))), P (valAt (Env.setAtE s.env p (φ (valAt s.env p))) q) := by
      intro q hq
      rw [allPos_setAtE] at hq
      by_cases e : q = p
      · subst e; rw [Ochr.Meaning.Steps.valAt_setAtE_self _ hq]; exact hP _ (hs q hq)
      · rw [valAt_setAtE_other _ _ _ _ e]; exact hs q hq
    rw [runs_forIn_fold hP hbody L _ s' b₁ u hs'
      (fun q h => by show q ∈ allPos (Env.setAtE _ _ _); rw [allPos_setAtE]; exact hm q (.tail _ h)) hrest, List.foldl_cons]

/-- **`mapState f false`** where `f` acts as the pure map `φ` on every value it meets (values in `P`,
which `φ` keeps): each position in turn set to `φ` of its value. -/
theorem runs_mapState_fold {f : Value → M Value} {φ : Value → Value} {P : Value → Prop}
    (hf : ∀ v, P v → ∀ st b r st', Runs (f v) st b r st' → r = φ v ∧ st' = st) (hP : ∀ v, P v → P (φ v))
    {s s' : MState} {b : Nat} (hs : ∀ q ∈ allPos s.env, P (valAt s.env q))
    (h : Runs (Ochr.mapState f false) s b () s') :
    s' = { s with env := (allPos s.env).foldl (fun E p => Env.setAtE E p (φ (valAt E p))) s.env } := by
  unfold Ochr.mapState at h
  peel h
  obtain ⟨_, s₀, b₀, hfor, htail⟩ := Runs.bind_inv h
  obtain ⟨-, e9⟩ := runs_pure_inv htail
  rw [e9]
  clear h htail e9
  simp only [Bool.false_eq_true, ↓reduceIte] at hfor
  refine runs_forIn_fold hP (fun p s₁ s₂ b₁ r hp hs₁ h1 => ?_) _ s s₀ b _ hs (fun _ h => h) hfor
  obtain ⟨v₁, s₃, b₃, hg, h1⟩ := Runs.bind_inv h1
  obtain ⟨e1, e2⟩ := runs_getAt_inv hg
  subst e1; have e2' := e2.symm; subst e2'
  obtain ⟨r₁, s₄, b₄, hfr, h1⟩ := Runs.bind_inv h1
  obtain ⟨e3, e4⟩ := hf _ (hs₁ p hp) _ _ _ _ hfr
  subst e3; have e4' := e4.symm; subst e4'
  obtain ⟨_, s₅, b₅, hst, h1⟩ := Runs.bind_inv h1
  have e5 := runs_setAt_inv hst; subst e5
  obtain ⟨e6, e7⟩ := runs_pure_inv h1
  exact ⟨e6, e7⟩

end Ochr.Meaning.Steps.Machine
