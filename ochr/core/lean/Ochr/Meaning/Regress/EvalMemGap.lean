import Ochr.Meaning.Regress.GenNeutralContent
import Ochr.Meaning.Steps.Sim

/-!
# No statement concludes that an evaluation returns a member of its type (sixth lead; kernel-checked)

The rules trial found (`origin/rules-trial`, `Rules/InFlight.lean`) that the step statements count
the value an evaluation returns as a temporary of the top frame (`MState.withTemp`), and a temporary
has no stored type (`MState.posTyM` at `.temp` is `none`), so `Membership` says nothing of it. Two
consequences, checked here.

1. **[Return]'s statement is false** (`bodyReturns_false`). `bodyReturns_sound_stmt` concludes that
   the returned value is a whole member of the type `T` it is checked at, from `GoodF` of the state
   with the value in flight. But `Machine.bodyReturns` checks only [Repack], which returns at once
   for a value holding no dependent constructor (`repackCheck`: `if !(← hasDependent v) then
   return`), and `GoodF` of the state with the value in flight says nothing about the value. From
   one empty frame with `0` in flight (good at every assignment, `good_S0T`), `bodyReturns` checks
   `0` at `Unit` and succeeds (`runs`, evaluated by the kernel), and `0` is no member of `Unit`
   (`zero_not_unit`). So the statement is false at every context that admits the empty frame. The
   chain's constant case (`Assembly.step_member_const`) takes its membership from it.

2. **A typed `let` cannot be assembled from the evaluation step** (`good_pushBind_mem`). A typed
   `let` pushes its right-hand side's value `v` as a binding at its type `T` (`Machine.evalCore`'s
   `.letIn`: `pushBind h T v p du'`), and the tail is run from that state, so its step needs `Good`
   there. `Good` there contains the membership of `v` at `T`: `Membership.pos` at the new binding.
   The evaluation step's conclusion does not contain it: its `GoodF` holds of a state with a
   non-member in flight (`good_S0T` with `0` and `Unit`; the conjuncts relating `v` to the
   reference's result `r` say what `v` means, not that `r` is a member of anything): with `0` bound
   at `Unit` the state is good at no assignment (`not_good_push`).

3. **The call statements are vacuous at a borrow argument** (`borrowArg_not_good`). The same root:
   a temporary types no label, so a borrow held by a temporary (an argument, pushed by `evalCall`)
   leaves its label free in every typed future, and its lender is then no member of its type. So
   `Good (st.withTemps (fv :: ws))`, the hypothesis of `callFn_step_stmt`, `runBody_step_stmt` and
   `closeCall_step_stmt`, is false whenever an argument borrows a typed place. (`GoodF`'s flight
   types the label of one returned value; arguments are several and the statements take `Good`.)
-/

namespace Ochr.Meaning.Regress.EvalMemGap
open Ochr Ochr.Meaning Ochr.Meaning.Steps
open Ochr.Meaning.Regress.GenNeutralContent (outSt outVal isOk runs_out)

/-- One empty frame. -/
def S0 : MState := { env := #[{}] }

/-- The empty frame with `0` in flight. -/
theorem S0T_eq : S0.withTemp .zero = ({ env := #[{ temps := #[.zero] }] } : MState) := rfl

/-- The only position of the state with `0` in flight is its temporary. -/
theorem allPos_S0T : allPos (S0.withTemp .zero).env = [.temp 0 0] := by decide +kernel

theorem values_S0T : Env.values (S0.withTemp .zero).env = [.zero] := by
  rw [Env.values, allPos_S0T]; rfl

theorem noBind_S0T (f i : Nat) (b : Binding) :
    (S0.withTemp .zero).env[f]?.bind (fun fr => fr.binds[i]?) ≠ some b := by
  rw [S0T_eq]; rcases f with _ | f <;> simp

/-- **The empty frame with `0` in flight is good at every assignment**: it has no binding, so no
position with a stored type, and the temporary is untyped. -/
theorem good_S0T (K : RunCtx) (ρ : Assignment) : Good K.dm K.M K.Γ ρ (S0.withTemp .zero) := by
  have hV := values_S0T
  have hA := allPos_S0T
  have h0 : valAt (S0.withTemp .zero).env (.temp 0 0) = .zero := rfl
  refine ⟨⟨fun σ _ h => by simp [S0T_eq] at h, fun n σ h => by simp [S0T_eq] at h, fun σ v h => by simp [S0T_eq] at h,
      fun σ r h => by simp [S0T_eq] at h⟩,
    ⟨?_, fun σ _ h => by simp [S0T_eq] at h, fun G h => by simp [MState.goalM, S0T_eq] at h⟩,
    ⟨?_, ?_⟩, ⟨?_, ?_⟩, ?_, ?_, ⟨?_, ?_, ?_, ?_, ?_⟩, ?_, ⟨?_, ?_, ?_, ?_⟩, ?_, ?_, ⟨?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · intro φ _ p T hp
    cases p with
    | temp f i => simp [MState.posTyM] at hp
    | bind f i =>
      simp only [MState.posTyM] at hp
      split at hp
      · rename_i b hb; exact absurd hb (noBind_S0T f i b)
      · cases hp
  · rw [hA]; intro p hp; simp at hp; subst hp; show ¬ (Value.zero.hasBorrow = true); decide
  · rw [hA]; intro p hp q hq _ _ _; simp at hp hq; rw [hp, hq]
  · rw [hV]; intro v hv l hl; simp at hv; subst hv; simp [Value.outerLoans] at hl
  · intro l; rw [hV]; simp [Value.outerLoans]
  · exact ⟨fun a => ⟨a, fun b ⟨p, hp, w, hw, _⟩ => by
      rw [hA] at hp; simp at hp; subst hp; rw [h0] at hw; cases hw⟩⟩
  · unfold WF4; rw [hV]; intro v hv; simp at hv; subst hv; decide
  · exact MState.refd_lt _ _
      (by rw [hV]; intro v hv σ h; simp at hv; subst hv; simp [Value.hasAbs, Value.anyAtom, BEq.beq, Value.beq] at h)
      (fun f i b T hb _ => absurd hb (noBind_S0T f i b))
      (fun f i b P ws j hb _ => absurd hb (noBind_S0T f i b))
      (fun G hG => by simp [S0T_eq] at hG) (fun m σ' h => by simp [S0T_eq] at h) (fun σ' v h => by simp [S0T_eq] at h)
      (fun σ' T h => by simp [S0T_eq] at h)
  · intro T hT; simp [S0T_eq] at hT
  · intro σ r h; simp [S0T_eq] at h
  · simp [S0T_eq]
  · rw [hV]; intro v hv l hl; simp at hv; subst hv; simp [Value.loans] at hl
  · intro p T _ f i b _ hb; exact absurd hb (noBind_S0T f i b)
  · rw [hV]; intro v hv; simp at hv; subst hv; decide
  · intro f i b hb; exact absurd hb (noBind_S0T f i b)
  · intro T hT; simp [S0T_eq] at hT
  · intro G hG; simp [S0T_eq] at hG
  · intro p hp hl; rw [hA] at hp; simp at hp; subst hp; rw [h0] at hl; simp [Value.outerLoans] at hl
  · intro v hv; rw [hV] at hv; simp at hv; subst hv; rfl
  · intro f i b hb; exact absurd hb (noBind_S0T f i b)
  · intro T hT; simp [S0T_eq] at hT
  · intro G hG; simp [S0T_eq] at hG
  · intro n σ h; simp [S0T_eq] at h
  · intro σ v h; simp [S0T_eq] at h
  · refine ⟨?_, ?_, ?_⟩
    · intro k l _ _ x hx
      simp [Env.sitesOf, hA, h0, Value.sitesOf] at hx
    · intro pos path _ l _ x hx
      simp [Env.sitesOf, hA, h0, Value.sitesOf] at hx
    · refine ⟨?_, ?_⟩
      · intro v hv l; rw [hV] at hv; simp at hv; subst hv; rfl
      · intro v hv; rw [hV] at hv; simp at hv; subst hv; rfl

/-! ## [Return] at `Unit` of `0` -/

/-- The checker's [Return] of `0` checked at `Unit`. -/
abbrev br : M Unit := Ochr.bodyReturns 10 "it" .zero .tUnit [] ""

theorem ok : isOk br S0 10 = true := by decide +kernel

/-- **`bodyReturns` accepts `0` at `Unit`**: [Repack] returns at once for a value with no dependent
constructor, so nothing is checked. -/
theorem runs : Runs br S0 10 () (outSt br S0 10) := runs_out br S0 10 ok

/-- `Unit` and `Nat` are different types (one has a single element, the other two). -/
theorem unit_ne_nat : (Unit : Type) ≠ Nat := by
  intro h
  have : ∀ a b : Nat, a = b := fun a b => by
    have := Subsingleton.elim (cast h.symm a) (cast h.symm b)
    simpa using congrArg (cast h) this
  exact absurd (this 0 1) (by decide)

/-- **`0` is not a member of `Unit`**, at any reading and hint. -/
theorem zero_not_unit (K : RunCtx) (ρ : Assignment) (φ : Future) (h : TyS) :
    ¬ (meanV K ρ φ h .zero ∈ₛ[K.dm.read] (meanV K ρ noFuture (.plain .err) .tUnit).asTy) := by
  rintro ⟨a, ha⟩
  have e : meanV K ρ φ h .zero = .el0 Nat 0 := rfl
  rw [e] at ha
  exact unit_ne_nat (Sem.el0.inj ha).1

/-- **`bodyReturns_sound_stmt` is false** (fuel 10, any `K` admitting the empty frame, any `ρ` and
`φ`): from the empty frame with `0` in flight, good at every assignment, [Return] checks `0` at
`Unit` and succeeds, and `0` is no member of `Unit`. The statement asks nothing of the value
beyond `GoodF` of the state with it in flight, and that says nothing of a temporary. -/
theorem bodyReturns_false (K : RunCtx) (ρ : Assignment) (φ : Future) (hctx : CtxOk K ρ S0) :
    ¬ bodyReturns_sound_stmt K ρ φ 10 := by
  intro hs
  -- every future is typed for it: it has no typed holder
  have hφ : TypedFutureF K.dm K.M K.Γ ρ (S0.withTemp .zero) [] φ :=
    (typedFutureF_nil ..).mpr fun p l _ T hT => by
      cases p with
      | temp => simp [MState.posTyM] at hT
      | bind f i =>
        simp only [MState.posTyM] at hT
        split at hT
        · rename_i b hb; exact absurd hb (noBind_S0T f i b)
        · cases hT
  have h := (hs S0 _ "it" .zero .tUnit [] "" [] ((goodF_nil ..).mpr (good_S0T K ρ)) hctx 10 runs hφ).1
  exact zero_not_unit K ρ φ _ h

/-! ## A typed `let` needs the right-hand side's membership -/

/-- The state with the binding `b` pushed on the top frame (`Env.pushBind`, as the `let` does). -/
def _root_.Ochr.MState.withBind (st : MState) (b : Binding) : MState :=
  { st with env := st.env.modify (st.env.size - 1) fun fr => { fr with binds := fr.binds.push b } }

theorem withBind_bind (st : MState) (b : Binding) (fr : Frame) (hfr : st.env[st.env.size - 1]? = some fr) :
    (st.withBind b).env[st.env.size - 1]?.bind (fun fr' => fr'.binds[fr.binds.size]?) = some b := by
  simp [MState.withBind, Array.getElem?_modify, hfr]

/-- **`Good` after a typed `let`'s push contains the membership of the pushed value** at its type,
under every typed future (the new binding's `Membership.pos`). So the step for `let`, whose tail is
run from that state, owes it, and only the step that produced the value can supply it. -/
theorem good_withBind_mem (dm : DataModel) (C : CodeMeaning) (Γ : List IndDecl) (ρ : Assignment)
    (st : MState) (b : Binding) (T : Value) (hT : b.ty = some T) (fr : Frame)
    (hfr : st.env[st.env.size - 1]? = some fr) (hg : Good dm C Γ ρ (st.withBind b)) :
    ∀ φ, TypedFuture dm C Γ ρ (st.withBind b) φ →
      DataModel.pmem dm.read Γ (Value.mean dm C Γ ρ φ (Value.tyS dm C Γ ρ T) b.val) (Value.tyM dm C Γ ρ (fun _ => .err) T) := by
  intro φ hφ
  have hb' := withBind_bind st b fr hfr
  have hp : MState.posTyM dm C Γ ρ (st.withBind b) (.bind (st.env.size - 1) fr.binds.size) =
      some (Value.tyM dm C Γ ρ (fun _ => .err) T) := by
    simp only [MState.posTyM, hb', hT]
  have hm := hg.2.1.pos φ hφ _ _ hp
  have e : Env.mean dm C Γ ρ φ (st.withBind b).env (.bind (st.env.size - 1) fr.binds.size) =
      Value.mean dm C Γ ρ φ (Value.tyS dm C Γ ρ T) b.val := by
    simp only [Env.mean, hb', Env.hintAt, hT]
  rwa [e] at hm

/-- `let x = u; …` with `u` returning `0` at `Unit`: the binding pushed. -/
def bx : Binding := { hint := ⟨"x"⟩, ty := some .tUnit, val := .zero }

/-- **What the evaluation step concludes does not make the `let`'s next state good.** The state
with `0` in flight is good at every assignment (`good_S0T`: everything `eval_step_stmt` says of the
state after, its `GoodF`, holds of it), and with `0` bound at `Unit` it is good at none. -/
theorem not_good_push (K : RunCtx) (ρ : Assignment) : ¬ Good K.dm K.M K.Γ ρ (S0.withBind bx) := by
  intro hg
  have hφ : TypedFuture K.dm K.M K.Γ ρ (S0.withBind bx) noFuture := fun p l hl T hT => by
    exfalso
    cases p with
    | temp f i => simp [MState.posTyM] at hT
    | bind f i =>
      rcases f with _ | f
      · rcases i with _ | i
        · simp [Env.shape, valAt, S0, MState.withBind, bx] at hl
        · simp [MState.posTyM, S0, MState.withBind] at hT
      · simp [MState.posTyM, S0, MState.withBind] at hT
  have hm := good_withBind_mem K.dm K.M K.Γ ρ S0 bx .tUnit rfl {} rfl hg noFuture hφ
  rcases hm with h | ⟨t, hw, hmo, hin⟩
  · cases h
  · cases hmo with
    | refl =>
      rcases hin with hin | hin
      · exact zero_not_unit K ρ noFuture (Value.tyS K.dm K.M K.Γ ρ Value.tUnit) hin
      · simp [Value.tyM, Value.mean, DataModel.OpenIn, TyM.unit, Sem.asTy] at hin

/-! ## A borrow argument in flight leaves its label untyped -/

/-- `f(&x)` with `x : Nat`, after the argument is evaluated and pushed (`Machine.evalCall`'s
`pushTemp w`): `x` lent to `0`, the borrow `borrow_0 0` a temporary. -/
def SB : MState :=
  { env := #[{ binds := #[{ hint := ⟨"x"⟩, ty := some .tNat, val := .loan 0 }], temps := #[.borrow 0 .zero] }] }

/-- **No state with a borrow argument in flight is good.** `TypedFuture` types a label only at a
holder with a stored type, a temporary has none, so a future may give the label `0` anything; the
lender `x`, which means the label's final content, is then no member of `Nat`. So `callFn_step_stmt`
(whose hypothesis is `Good (st.withTemps (fv :: ws))`), `runBody_step_stmt` and `closeCall_step_stmt`
hold vacuously of every call with a borrow argument of a typed place, and their caller cannot supply
the hypothesis. (`GoodF` repairs this for ONE value in flight, through `flightOf`; the arguments are
several, and the call statements take `Good`.) -/
theorem borrowArg_not_good (K : RunCtx) (ρ : Assignment) : ¬ Good K.dm K.M K.Γ ρ SB := by
  intro hg
  have hφ : TypedFuture K.dm K.M K.Γ ρ SB noFuture := fun p l hl T hT => by
    exfalso
    cases p with
    | temp f i => simp [MState.posTyM] at hT
    | bind f i =>
      rcases f with _ | f
      · rcases i with _ | i
        · simp [Env.shape, valAt, SB] at hl
        · simp [MState.posTyM, SB] at hT
      · simp [MState.posTyM, SB] at hT
  have hp : MState.posTyM K.dm K.M K.Γ ρ SB (.bind 0 0) = some (Value.tyM K.dm K.M K.Γ ρ (fun _ => .err) .tNat) := rfl
  have hm := hg.2.1.pos noFuture hφ _ _ hp
  have e : Env.mean K.dm K.M K.Γ ρ noFuture SB.env (.bind 0 0) = .err := rfl
  rw [e] at hm
  rcases hm with h | ⟨t, hw, hmo, -⟩
  · cases h
  · cases hmo with
    | refl => simp [Sem.whole] at hw

/-! ## [Repack]'s statement, the same way -/

/-- The checker's [Repack] of `0` at `Unit`. -/
abbrev rp : M Unit := Ochr.repackCheck 10 "it" .zero .tUnit

theorem okR : isOk rp (S0.withTemp .zero) 10 = true := by decide +kernel

/-- **`repackCheck_sound_stmt` is false** (fuel 10, any `K` admitting the empty frame with `0` in
flight): [Repack] returns at once for a value with no dependent constructor, so it accepts `0` at
`Unit`, and the statement concludes membership from nothing else. Its honest content is
conditional: a value that is a member while open (`pmem`'s `OpenIn`) and passes the check is a
member. -/
theorem repackCheck_false (K : RunCtx) (ρ : Assignment) (φ : Future) (hctx : CtxOk K ρ (S0.withTemp .zero)) :
    ¬ repackCheck_sound_stmt K ρ φ 10 := by
  intro hs
  have hφ : TypedFuture K.dm K.M K.Γ ρ (S0.withTemp .zero) φ := fun p l _ T hT => by
    cases p with
    | temp => simp [MState.posTyM] at hT
    | bind f i =>
      simp only [MState.posTyM] at hT
      split at hT
      · rename_i b hb; exact absurd hb (noBind_S0T f i b)
      · cases hT
  exact zero_not_unit K ρ φ _
    ((hs _ _ "it" .zero .tUnit (good_S0T K ρ) hctx 10 (runs_out rp _ 10 okR)).2 hφ)

end Ochr.Meaning.Regress.EvalMemGap
