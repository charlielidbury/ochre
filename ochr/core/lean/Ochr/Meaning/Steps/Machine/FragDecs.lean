import Ochr.Meaning.Steps.Machine.FragAssign
import Ochr.Meaning.Steps.Machine.PlaceLocalFF
import Ochr.Meaning.Steps.Frag

/-!
# `FragDec`: the fuel-free table at the fragment's terms (machine lane, machine6)

`declOf` (unchecked, `chk = false`) of a fragment term runs as a pure computation at every fuel above
the term's depth, reading only the readings of its number variables (`.other`), and answers the term's
type's reading `A.rd`; `preFlags` of a non-call read `.other`, `.unit` or `.ref .other` is
`(false, false)`. So the fuel-free table, whose answer is any succeeding run's, reads the same.
-/

namespace Ochr.Meaning.Steps.Machine

open Ochr Ochr.Meaning Ochr.Meaning.Steps Ochr.Meaning.DecideScope Ochr.Meaning.Steps.Slice
open Ochr.Meaning.Steps.Form

theorem runAll_pure' {α : Type} (a : α) (s : MState) (f : Fuel) (l : Array LogEntry) :
    runAll (pure a : M α) s f l = ((.ok (.ok (a, s)), f), l) := rfl

/-- The reading of variable `i` under the local scope `sc`, then the live scope of `S`. -/
def readingAt (S : MState) (sc : List DeclInfo) (i : Nat) : DeclInfo :=
  if h : i < sc.length then sc[i] else liveVal S (i - sc.length)

theorem runAll_placeDecl_var (k : Nat) (sc : List DeclInfo) (i : Nat) (S : MState) (hl : S.liveScope = true)
    (f : Fuel) (l : Array LogEntry) :
    runAll (Ochr.placeDecl (k + 1) sc (.var i)) S f l = ((.ok (.ok (readingAt S sc i, S)), f), l) := by
  rw [Ochr.placeDecl]
  unfold readingAt
  by_cases h : i < sc.length
  · simp only [dif_pos h]; rfl
  · simp only [dif_neg h]
    show runAll (get >>= fun s => if s.liveScope = true then liveDecl (i - sc.length) else pure .other) S f l = _
    rw [runAll_get_bind', hl, if_pos rfl]
    rfl

/-- **`declOf` of a fragment term** (unchecked): a pure computation at every fuel above the term's
depth, answering its type's reading, where every number variable reads `.other`. -/
theorem declOf_frag {Γ : List Form.FT} {t : Term} {A : Form.FT} (hty : FTy Γ t A) :
    ∀ (sc : List DeclInfo) (ns : List String) (S : MState), S.liveScope = true →
      (∀ i, Γ[i]? = some .nat → readingAt S sc i = .other) →
      ∃ N, ∀ k, N ≤ k → ∀ f l, runAll (Ochr.declOf k false sc ns t) S f l = ((.ok (.ok (A.rd, S)), f), l) := by
  induction hty with
  | zero Γ =>
    intro sc ns S _ _
    refine ⟨1, fun k hk f l => ?_⟩
    obtain ⟨k, rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
    rw [Ochr.declOf]; rfl
  | succ Γ u _ _ =>
    intro sc ns S _ _
    refine ⟨1, fun k hk f l => ?_⟩
    obtain ⟨k, rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
    rw [Ochr.declOf]; rfl
  | var Γ i hi =>
    intro sc ns S hl hr
    refine ⟨2, fun k hk f l => ?_⟩
    obtain ⟨k, rfl⟩ : ∃ k', k = k' + 2 := ⟨k - 2, by omega⟩
    rw [Ochr.declOf]
    show runAll (Ochr.placeDecl (k + 1) sc (.var i)) S f l = _
    rw [runAll_placeDecl_var _ _ _ _ hl, hr i hi]; rfl
  | bor Γ i hi =>
    intro sc ns S hl hr
    refine ⟨2, fun k hk f l => ?_⟩
    obtain ⟨k, rfl⟩ : ∃ k', k = k' + 2 := ⟨k - 2, by omega⟩
    rw [Ochr.declOf]
    show runAll (Ochr.placeDecl (k + 1) sc (.var i) >>= fun d => pure (DeclInfo.ref d)) S f l = _
    rw [runAll_bind, runAll_placeDecl_var _ _ _ _ hl, hr i hi]; rfl
  | asg Γ i u _ _ _ =>
    intro sc ns S _ _
    refine ⟨1, fun k hk f l => ?_⟩
    obtain ⟨k, rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
    rw [Ochr.declOf]; rfl
  | asgD Γ i u _ _ _ =>
    intro sc ns S _ _
    refine ⟨1, fun k hk f l => ?_⟩
    obtain ⟨k, rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
    rw [Ochr.declOf]; rfl
  | letIn Γ x u w A B hu hw ihu ihw =>
    intro sc ns S hl hr
    obtain ⟨Nu, hNu⟩ := ihu sc ns S hl hr
    obtain ⟨Nw, hNw⟩ := ihw (A.rd :: sc) (x.name :: ns) S hl (fun i hi => by
      cases i with
      | zero =>
        simp only [List.getElem?_cons_zero, Option.some.injEq] at hi
        subst hi
        simp [readingAt, Form.FT.rd]
      | succ i =>
        simp only [List.getElem?_cons_succ] at hi
        have := hr i hi
        unfold readingAt at this ⊢
        simp only [List.length_cons, Nat.add_lt_add_iff_right, List.getElem_cons_succ, Nat.add_sub_add_right]
        exact this)
    refine ⟨max Nu Nw + 1, fun k hk f l => ?_⟩
    obtain ⟨k, rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
    rw [Ochr.declOf]
    show runAll (Ochr.declOf k false sc ns u >>= fun d => Ochr.declOf k false (d :: sc) (x.name :: ns) w) S f l = _
    rw [runAll_bind, hNu k (by omega)]
    exact hNw k (by omega) f l
  | seq Γ u w A B hu hw ihu ihw =>
    intro sc ns S hl hr
    obtain ⟨Nw, hNw⟩ := ihw sc ns S hl hr
    refine ⟨Nw + 1, fun k hk f l => ?_⟩
    obtain ⟨k, rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
    rw [Ochr.declOf]
    show runAll ((pure () : M Unit) >>= fun _ => Ochr.declOf k false sc ns w) S f l = _
    rw [runAll_bind]
    exact hNw k (by omega) f l

/-- `withLive b` around a computation that runs purely with the mode set to `b`. -/
theorem runAll_withLive_pure {α : Type} {b : Bool} {x : M α} {s : MState} {f : Fuel} {l : Array LogEntry} {a : α}
    (h : runAll x { s with liveScope := b } f l = ((.ok (.ok (a, { s with liveScope := b })), f), l)) :
    runAll (withLive b x) s f l = ((.ok (.ok (a, s)), f), l) := by
  unfold withLive
  rw [runAll_get_bind']
  simp only [runAll_bind, runAll_modify]
  rw [runAll_onFail_of_ok h]
  rfl

/-- `preFlags` of a fragment term at its type's reading: not erased, not a proof. -/
theorem runAll_preFlags_frag {Γ : List Form.FT} {t : Term} {A : Form.FT} (hty : FTy Γ t A) (s : MState) (f : Fuel)
    (l : Array LogEntry) : runAll (Ochr.preFlags t A.rd) s f l = ((.ok (.ok (some (false, false), s)), f), l) := by
  cases A <;> cases hty <;> rfl

/-- **`FragDec` at the fuel-free table.** -/
theorem fragDec (st' : MState) (bc : List DeclInfo → List Place → Term → List Place × List (Place × Nat)) :
    FragDec (checkerDecisionsFF st' bc) := by
  intro Γ t A st hty hF
  have hr : ∀ i, Γ[i]? = some .nat →
      readingAt { scopeState st' (topReadings st) with liveScope := true } [] i = .other := by
    intro i hi
    obtain ⟨f, j, b, hck, hb, -, hrd, -⟩ := hF.top i .nat hi
    unfold readingAt
    simp only [List.length_nil, Nat.not_lt_zero, dite_false, Nat.sub_zero]
    rw [show liveVal { scopeState st' (topReadings st) with liveScope := true } i =
      liveVal (scopeState st' (topReadings st)) i from rfl, liveVal_scopeState, topReadings_getD_of_ckVarPos hck hb, hrd]
    rfl
  obtain ⟨N, hN⟩ := declOf_frag hty [] [] { scopeState st' (topReadings st) with liveScope := true } rfl hr
  have hd : ∀ f l, runAll (declOfD t N) (scopeState st' (topReadings st)) f l =
      ((.ok (.ok (A.rd, scopeState st' (topReadings st))), f), l) :=
    fun f l => runAll_withLive_pure (hN N (Nat.le_refl _) f l)
  have hfl : runAll (flagsD t N) (scopeState st' (topReadings st)) ⟨0⟩ #[] =
      ((.ok (.ok ((false, false), scopeState st' (topReadings st))), ⟨0⟩), #[]) := by
    show runAll (declOfD t N >>= fun d => Ochr.preFlags t d >>= fun o => pure (o.getD (false, false))) _ _ _ = _
    rw [runAll_bind, hd]
    simp only
    rw [runAll_bind, runAll_preFlags_frag hty]
    rfl
  have hdr := hd ⟨0⟩ #[]
  refine ⟨?_, ?_⟩
  · exact readDecisionFF_of_runs ((decide_fuel_agree' _).1 t) (runs_of_runAll hfl)
  · exact readDecisionFF_of_runs ((decide_fuel_agree' _).2.2.1 t) (runs_of_runAll hdr)

#print axioms fragDec

end Ochr.Meaning.Steps.Machine
