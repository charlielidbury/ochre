import Ochr.Meaning.Steps.FormMachine

/-!
# A place's reading is local to its root (machine lane; proposed for `FormMachine.lean`)

`Inv D Γ` takes an arbitrary `D`, and `ShapeFacts.fits` reads `D.placeDecl` at the state's top
readings. A change that pushes or pops a binding moves the readings and the de Bruijn indices, and a
change that writes a number where the old content was a loan or absent meets readings the old `Inv`
never constrained (machine3's review, 2026-11-21: six of the ten `InvSteps` false as stated). What
the fuel-free table has, and what those lemmas need of `D`: a place's reading depends only on its
root variable's reading and its steps (`Decide.placeDecl` reads the frame only at the root,
through `liveDecl`), and under a root read `.other` or `.ref .other` no place reads an inductive.
-/

namespace Ochr.Meaning.Steps.Machine

open Ochr Ochr.Meaning Ochr.Meaning.Steps Ochr.Meaning.DecideScope
open Ochr.Meaning.Steps.Form

/-- A place's reading depends only on its root variable's reading and its steps, and under a root
read `.other` or `.ref .other` no place reads an inductive. -/
structure PlaceLocal (D : Decisions) : Prop where
  root : ∀ (sc sc' : List DeclInfo) (p p' : Place), p.steps.2 = p'.steps.2 →
    sc.getD p.steps.1 .other = sc'.getD p'.steps.1 .other → D.placeDecl sc p = D.placeDecl sc' p'
  other : ∀ p n args, D.placeDecl [.other] p ≠ .ind n args
  ref : ∀ p n args, D.placeDecl [.ref .other] p ≠ .ind n args

/-- The place with its root renamed to `var 0`. -/
def _root_.Ochr.Place.toRoot0 (p : Place) : Place := p.mapRoot fun _ => .var 0

theorem _root_.Ochr.Place.steps_toRoot0 : ∀ p : Place, p.toRoot0.steps = (0, p.steps.2)
  | .var _ => rfl
  | .deref q => by
    have ih := Place.steps_toRoot0 q
    simp only [Place.toRoot0, Place.mapRoot, Place.steps] at ih ⊢; rw [ih]
  | .proj _ q => by
    have ih := Place.steps_toRoot0 q
    simp only [Place.toRoot0, Place.mapRoot, Place.steps] at ih ⊢; rw [ih]
  | .field _ q => by
    have ih := Place.steps_toRoot0 q
    simp only [Place.toRoot0, Place.mapRoot, Place.steps] at ih ⊢; rw [ih]

/-- The top readings at a variable `ckVarPos` finds: its binding's reading. -/
theorem topReadings_getD_of_ckVarPos {st : MState} {i f j : Nat} (h : ckVarPos st.env i = some (.bind f j))
    {b : Binding} (hb : st.env[f]?.bind (fun fr : Frame => fr.binds[j]?) = some b) :
    (topReadings st).getD i .other = b.decl := by
  unfold ckVarPos at h
  split at h
  · rename_i hi
    cases h
    have hne : 0 < st.env.size := by
      rcases Nat.eq_zero_or_pos st.env.size with e | e
      · simp [e] at hb
      · exact e
    have hfr : st.env[st.env.size - 1]? = some st.env[st.env.size - 1]! := by
      rw [getElem!_pos st.env (st.env.size - 1) (by omega)]; exact Array.getElem?_eq_getElem _
    rw [hfr, Option.bind_some] at hb
    unfold topReadings
    simp only [Array.back?, hfr, Option.map_some, Option.getD_some]
    rw [List.getD_eq_getElem?_getD, List.getElem?_reverse (by simpa using hi)]
    simp only [List.length_map, Array.length_toList, List.getElem?_map, Array.getElem?_toList]
    rw [show st.env[st.env.size - 1]!.binds.size - 1 - i = st.env[st.env.size - 1]!.binds.size - 1 - i from rfl, hb]
    rfl
  · cases h

/-- Under `PlaceLocal`, a place rooted at a binding of the top frame read `r` reads as at `[r]`. -/
theorem PlaceLocal.at_binding {D : Decisions} (hL : PlaceLocal D) {st : MState} {p : Place} {f j : Nat}
    (h : ckVarPos st.env p.steps.1 = some (.bind f j)) {b : Binding}
    (hb : st.env[f]?.bind (fun fr : Frame => fr.binds[j]?) = some b) :
    D.placeDecl (topReadings st) p = D.placeDecl [b.decl] p.toRoot0 :=
  hL.root _ _ _ _ (by rw [Place.steps_toRoot0]) (by rw [Place.steps_toRoot0, topReadings_getD_of_ckVarPos h hb]; rfl)

/-- The place with its root renamed to `var r`. -/
def _root_.Ochr.Place.reroot (p : Place) (r : Nat) : Place := p.mapRoot fun _ => .var r

theorem _root_.Ochr.Place.steps_reroot (r : Nat) : ∀ p : Place, (p.reroot r).steps = (r, p.steps.2)
  | .var _ => rfl
  | .deref q => by
    have ih := Place.steps_reroot r q
    simp only [Place.reroot, Place.mapRoot, Place.steps] at ih ⊢; rw [ih]
  | .proj _ q => by
    have ih := Place.steps_reroot r q
    simp only [Place.reroot, Place.mapRoot, Place.steps] at ih ⊢; rw [ih]
  | .field _ q => by
    have ih := Place.steps_reroot r q
    simp only [Place.reroot, Place.mapRoot, Place.steps] at ih ⊢; rw [ih]

/-- **The readings' two clauses across a change of the top frame's variables** (a push or a pop of a
binding): `b`'s variables from `k` on are `a`'s variables `ρ i`, at the same positions, read the same,
holding the same values; `b`'s variables below `k` (new) hold contents that are no proof and read no
inductive. Under `PlaceLocal` the readings follow the variables. -/
theorem readClauses_reroot {D : Decisions} {Γ : List IndDecl} {a b : MState} (hi : Inv D Γ a) (hL : PlaceLocal D)
    (k : Nat) (ρ : Nat → Nat)
    (hpos : ∀ i, k ≤ i → ckVarPos b.env i = ckVarPos a.env (ρ i))
    (hR : ∀ i, k ≤ i → (topReadings b).getD i .other = (topReadings a).getD (ρ i) .other)
    (hval : ∀ i pos, k ≤ i → ckVarPos a.env (ρ i) = some pos → valAt b.env pos = valAt a.env pos)
    (hnew : ∀ p x, p.steps.1 < k → ckContent b.env p = some x →
      x ≠ .proof ∧ ∀ n args, D.placeDecl (topReadings b) p ≠ .ind n args) :
    (∀ p v n args, ckContent b.env p = some v → D.placeDecl (topReadings b) p = .ind n args →
      (Γ.find? (·.name == n)).isSome → v.fitsInd n = true) ∧
    (∀ p, GrainOk D Γ (topReadings b) p → ckContent b.env p = some .proof →
      D.copy (D.placeDecl (topReadings b) p) = true) := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, sf, -⟩ := hi
  have hc : ∀ p, k ≤ p.steps.1 → ckContent b.env p = ckContent a.env (p.reroot (ρ p.steps.1)) := by
    intro p hk
    unfold ckContent
    rw [Place.steps_reroot, hpos _ hk]
    cases e : ckVarPos a.env (ρ p.steps.1) with
    | none => rfl
    | some pos => simp only [Option.bind_some]; rw [hval _ pos hk e]
  have hd : ∀ p, k ≤ p.steps.1 → D.placeDecl (topReadings b) p = D.placeDecl (topReadings a) (p.reroot (ρ p.steps.1)) :=
    fun p hk => hL.root _ _ _ _ (by rw [Place.steps_reroot]) (by rw [Place.steps_reroot]; exact hR _ hk)
  refine ⟨fun p v n args h e hn => ?_, fun p hg h => ?_⟩
  · by_cases hk : p.steps.1 < k
    · exact absurd e ((hnew p v hk h).2 n args)
    · have hk := Nat.le_of_not_lt hk
      rw [hc p hk] at h; rw [hd p hk] at e
      exact sf.fits _ v n args h e hn
  · by_cases hk : p.steps.1 < k
    · exact absurd rfl (hnew p _ hk h).1
    · have hk := Nat.le_of_not_lt hk
      rw [hc p hk] at h; rw [hd p hk]
      refine sf.proofCopy _ (fun q x rest hq hs => ?_) h
      rw [Place.steps_reroot] at hq hs
      have hq' : (q.reroot p.steps.1).steps.1 = p.steps.1 := by rw [Place.steps_reroot]
      have hs' : p.steps.2 = (q.reroot p.steps.1).steps.2 ++ x :: rest := by rw [Place.steps_reroot]; exact hs
      have := hg _ x rest hq' hs'
      rwa [hL.root (topReadings b) (topReadings a) (q.reroot p.steps.1) q (by rw [Place.steps_reroot])
        (by rw [Place.steps_reroot, hR _ hk, hq])] at this

end Ochr.Meaning.Steps.Machine
