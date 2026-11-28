import Ochr.Meaning.Steps.TopCtx
import Ochr.Meaning.Steps.TopGuards

/-!
# The top of the proof from `master` (lead43, 2026-11-28; docs/31 D253 on)

`consistency_of_master` (`Steps/TopAssembly.lean`): the project's consistency statement (`consistencyBounded`'s form)
from the 32 step statements (`AllSteps`, at every context meeting the fundamental lemma's condition), the data
model's theorem as it stands (`Assembly.exists_dataModel`, its facts `DataFacts`), the fundamental lemma
(`Strict.fund_all`, PROVED), and one NAMED fact per link not derived. This file: the contexts of the checks, the
invariant carried from item to item, and the program-level induction. Every link is a `def … : Prop` whose docstring
gives its class (checker / model / mixed) and status (proved / read true / unread / false until X).

**The invariant** (`StageOk`): the stage's meanings are members of their types with no label (the old chain's
`MeansMember`), and every global of the stage meets `GlobalsOk`'s clauses (D253's included: its fixpoint equation, its
meaning its own closure, its result's label kind) at the context of EVERY later check. The second is what the next
check's `Pre` consumes; the knot of each function supplies it (`Steps/TopFix.lean`), so the knot's output is consumed
only by LATER items: no circle (the check of item `k` reads of item `k` only its stage closure, `memBelow`).
-/

namespace Ochr.Meaning.Steps.Form.Top

open Ochr Ochr.Meaning Ochr.Meaning.Steps Ochr.Meaning.Steps.Form Ochr.Meaning.Steps.Form.Master
open Ochr.Meaning.Assembly

/-- A name with a meaning in the stage `P`. -/
def _root_.Ochr.Meaning.ProgState.isGlobal (P : ProgState) (n : String) : Bool := (P.means.find? (·.1 == n)).isSome

section
variable (dm : DataModel) (D : MState → Decisions) (Γ : List IndDecl) (fuel : Nat)

/-- **The context of a check at stage `P`**: the program meaning's (`ProgState.ctx`: the data model, the whole
program's declarations, the stage's globals), the decisions `Dd`, and the function under check `cu = some (f, b, G)`
(`K.cur = some (f, b)`, `K.C.global f = G`, its stage closure at bound `b`). With `cu = none` it is `P.ctx` itself
(`ctxAt_none`). -/
noncomputable def ctxAt (P : ProgState) (Dd : Decisions) (cu : Option (String × Nat × (Sem × TyS))) : RunCtx :=
  { dm, Γ, D := Dd, cur := cu.map fun x => (x.1, x.2.1),
    C := { P.baseC with global := fun n => match cu with
      | some (f, _, G) => if n = f then G else P.baseC.global n
      | none => P.baseC.global n } }

theorem ctxAt_none (P : ProgState) (st : MState) : ctxAt dm Γ P (D st) none = P.ctx dm D Γ st := rfl

/-- The decisions of a checker state at or after stage `P` (its Σ extends `P`'s). -/
def LaterDec (P : ProgState) (Dd : Decisions) : Prop :=
  ∃ st : MState, Dd = D st ∧ P.globals <+: st.globals ∧ P.inds <+: st.inds

/-- **The top's invariant at stage `P`.** -/
structure StageOk (P : ProgState) : Prop where
  /-- every accepted definition so far means a member of its type -/
  mem : MeansMember dm P
  /-- with no label -/
  lab : ∀ e ∈ P.means, e.2.2.label = none
  /-- every meaning is a global's of the stage's Σ (so an accepted definition's fresh name is no meaning's) -/
  names : ∀ e ∈ P.means, ∃ g ∈ P.globals, g.name = e.1
  /-- every global of the stage meets `GlobalsOk`'s clauses at the context of every later check (a function under
  check there being none of the stage's) -/
  glob : ∀ (Dd : Decisions) (cu : Option (String × Nat × (Sem × TyS))), LaterDec D P Dd →
    (∀ x ∈ cu, P.isGlobal x.1 = false) → GlobalsOk (ctxAt dm Γ P Dd cu) { globals := P.globals }

/-- At the empty stage `GlobalsOk` asks nothing. -/
theorem globalsOk_nil (K : RunCtx) : GlobalsOk K { globals := [] } :=
  ⟨fun _ _ h => (by simp at h), fun _ _ h => (by simp at h), fun _ _ _ h => (by simp at h),
    fun _ _ h => (by simp at h), fun _ _ _ h => (by simp at h), fun _ _ _ _ _ _ _ _ h => (by simp at h),
    fun _ _ _ _ _ _ _ _ h => (by simp at h), fun _ _ _ _ _ _ _ _ h => (by simp at h), fun _ _ _ h => (by simp at h)⟩

theorem stageOk_empty : StageOk dm D Γ {} :=
  ⟨fun _ _ _ h => (by simp at h), fun _ h => (by simp at h), fun _ h => (by simp at h), fun _ _ _ _ => globalsOk_nil _⟩

/-- **The `k`-th item of `items` at its own stage** (the program's stage `k`, the items before it): what every per-item
link is asserted of, never an arbitrary stage or definition (docs/31 D254). -/
def AtStage (items : List Item) (P : ProgState) (it : Item) : Prop :=
  ∃ k, items[k]? = some it ∧ P = progMeaning dm D Γ (fun _ => .err) {} fuel (items.take k)

/-- **One item keeps the invariant**: the per-item obligation the knot, the constant's link and the inductive
declaration's discharge (`Steps/TopFix.lean`, `Steps/TopConst.lean`), for an item of the program at its own stage. -/
def ItemStep (items : List Item) (Inv : ProgState → Prop) : Prop :=
  ∀ (P : ProgState) (it : Item), AtStage dm D Γ fuel items P it → Inv P → ItemAccepted fuel P it → P.inds <+: Γ →
    (ProgState.step dm D Γ (fun _ => .err) {} fuel P it).inds <+: Γ → DataFaithful dm D Γ P →
    Inv (ProgState.step dm D Γ (fun _ => .err) {} fuel P it)

/-- **The program-level induction** (the old `defn_member`'s, for any invariant). -/
theorem inv_all {Inv : ProgState → Prop} (items : List Item) (h0 : Inv {}) (hs : ItemStep dm D Γ fuel items Inv)
    (hacc : ∀ (i : Nat) (it : Item), items[i]? = some it →
      ItemAccepted fuel (progMeaning dm D Γ (fun _ => .err) {} fuel (items.take i)) it)
    (hΓ : ∀ k, k ≤ items.length → (progMeaning dm D Γ (fun _ => .err) {} fuel (items.take k)).inds <+: Γ)
    (hfaith : ∀ k, k ≤ items.length → DataFaithful dm D Γ (progMeaning dm D Γ (fun _ => .err) {} fuel (items.take k))) :
    Inv (progMeaning dm D Γ (fun _ => .err) {} fuel items) := by
  have key : ∀ k, k ≤ items.length → Inv (progMeaning dm D Γ (fun _ => .err) {} fuel (items.take k)) := by
    intro k
    induction k with
    | zero => intro _; simpa [progMeaning, progMeaningFrom] using h0
    | succ k ih =>
      intro hk
      have hk' : k < items.length := hk
      have htake : items.take (k + 1) = items.take k ++ [items[k]] := List.take_succ_eq_append_getElem hk'
      have hfold : progMeaning dm D Γ (fun _ => .err) {} fuel (items.take k ++ [items[k]]) =
          ProgState.step dm D Γ (fun _ => .err) {} fuel (progMeaning dm D Γ (fun _ => .err) {} fuel (items.take k)) items[k] := by
        unfold progMeaning progMeaningFrom; rw [List.foldl_append]; rfl
      have hc := hΓ (k + 1) hk
      rw [htake, hfold] at hc ⊢
      exact hs _ _ ⟨k, List.getElem?_eq_getElem hk', rfl⟩ (ih (Nat.le_of_lt hk')) (hacc k items[k] (List.getElem?_eq_getElem hk'))
        (hΓ k (Nat.le_of_lt hk')) hc
        (hfaith k (Nat.le_of_lt hk'))
  have := key items.length (Nat.le_refl _)
  rwa [List.take_length] at this

end

end Ochr.Meaning.Steps.Form.Top
