import Ochr.Meaning.Steps.Statements
import Ochr.Meaning.ApplyMem

/-!
# Every evaluation returns a member of its type: the typed temporaries (sixth lead, docs/31 D81)

`Regress/EvalMemGap.lean` shows, kernel-checked, that no step statement concludes that the value an
evaluation returns is a member of its type: a temporary has no stored type, so `Membership` says
nothing of it. Three faults have that one root: [Return]'s and [Repack]'s statements are false, a
typed `let` cannot be assembled, and every state holding a borrow argument in a temporary is not
`Good`, so the call statements are vacuous at borrow arguments.

**The design (D81): a temporary has a stored type, as a binding has.** Every value the machine
holds carries the type the machine computed for it when it produced it (`none` where an untyped run
computed none). Then the invariant's existing clauses cover temporaries:
- `Membership.pos` at a typed temporary is the evaluation's membership, and every step that runs
  with values in flight below it must keep it, as it keeps a binding's: a call's earlier arguments
  while later ones run, a constructor's fields, a `let`'s result across the drop of its binding, an
  arm's result across the join, a body's result across its frame's pop;
- `TypedFuture` types the label of a borrow held by a typed temporary at the borrow's content type,
  which is the record the call statements lacked.
The alternative, a conjunct in `SimConclT` ("the returned value is a member"), says nothing once
the next step runs: every step that can run with a value in flight below it would need a further
conjunct keeping that value's membership, which is this clause assembled piece by piece, and the
labels would still be untyped.

Where the type lives: the proposal is a field of the checker's frame beside its temporaries
(`Frame.tempTys`), filled at each push with the type the machine has in hand (the push sites are
listed in docs/31 D81). Until that lands, this file states the clause with the temporaries' types
given separately (`TempTys`), which is the same predicate with its input abstracted: with the field,
`tt f i` is `st.env[f].tempTys[i]`.
-/

namespace Ochr.Meaning.Steps
open Ochr Ochr.Meaning

/-- The stored types of the temporaries, by frame and index (what `Frame.tempTys` would hold). -/
abbrev TempTys := Nat → Nat → Option Value

/-- No temporary typed. -/
def TempTys.none : TempTys := fun _ _ => Option.none

/-- `tt` with the temporary `(f, i)` typed `T?`. -/
def TempTys.set (tt : TempTys) (f i : Nat) (T? : Option Value) : TempTys :=
  fun f' i' => if f' = f ∧ i' = i then T? else tt f' i'

/-- The position `withTemp` pushes at: the next temporary of the top frame. -/
def _root_.Ochr.MState.nextTemp (st : MState) : Nat × Nat :=
  (st.env.size - 1, ((st.env[st.env.size - 1]?).map (·.temps.size)).getD 0)

/-- The temporaries' types after a value typed `T?` is pushed in flight (`MState.withTemp`). -/
def TempTys.push (tt : TempTys) (st : MState) (T? : Option Value) : TempTys :=
  tt.set st.nextTemp.1 st.nextTemp.2 T?

section
variable (dm : DataModel) (C : CodeMeaning) (Γ : List IndDecl)

/-- The stored type at a position, temporaries included: a binding's as before, a temporary's from
`tt` where the temporary exists. -/
noncomputable def _root_.Ochr.MState.posTyMT (ρ : Assignment) (st : MState) (tt : TempTys) : Pos → Option TyM
  | .bind f i => MState.posTyM dm C Γ ρ st (.bind f i)
  | .temp f i => match st.env[f]?.bind (·.temps[i]?) with
    | some _ => (tt f i).map (Value.tyM dm C Γ ρ (fun _ => .err))
    | none => none

/-- The type a position is read at, temporaries included. -/
noncomputable def _root_.Ochr.Env.hintAtT (ρ : Assignment) (env : Env) (tt : TempTys) : Pos → TyS
  | .bind f i => Env.hintAt dm C Γ ρ env (.bind f i)
  | .temp f i => match tt f i with
    | some T => Value.tyS dm C Γ ρ T
    | none => .plain TyM.err

/-- A position's meaning at its own type (for a binding, `Env.mean`'s). -/
noncomputable def _root_.Ochr.Env.meanT (ρ : Assignment) (φ : Future) (env : Env) (tt : TempTys) (p : Pos) : Sem :=
  match p with
  | .bind f i => Env.mean dm C Γ ρ φ env (.bind f i)
  | .temp f i => match env[f]?.bind (·.temps[i]?) with
    | some v => Value.mean dm C Γ ρ φ (Env.hintAtT dm C Γ ρ env tt (.temp f i)) v
    | none => .err

/-- A typed future: each live label held at a typed position, a temporary included, ends at a member
of its holder's content type. -/
def TypedFutureT (ρ : Assignment) (st : MState) (tt : TempTys) (φ : Future) : Prop :=
  ∀ p l, Env.shape st.env p = some l → ∀ T, MState.posTyMT dm C Γ ρ st tt p = some T → φ l ∈ₛ[dm.read] T

/-- Membership with the temporaries typed: every typed position, a temporary included, holds a
(partly moved) member of its stored type under every typed future; each stored type is a type. -/
structure MembershipT (ρ : Assignment) (st : MState) (tt : TempTys) : Prop where
  pos : ∀ φ, TypedFutureT dm C Γ ρ st tt φ →
    ∀ p T, MState.posTyMT dm C Γ ρ st tt p = some T → DataModel.pmem dm.read Γ (Env.meanT dm C Γ ρ φ st.env tt p) T
  absTy : ∀ σ, st.Refd σ → σ < st.absTy.size → (MState.absTyM dm C Γ ρ st σ).level.isSome
  goal : ∀ G, MState.goalM dm C Γ ρ st = some G → G.level.isSome
  /-- every stored type is a type (has a level): the premise conversion's soundness needs of the
  types it compares (with strict meanings, "well typed inside"; docs/35 Theme 1) -/
  tys : ∀ p T, MState.posTyMT dm C Γ ρ st tt p = some T → T.level.isSome

/-- `Good` with the temporaries typed. -/
def GoodT (ρ : Assignment) (st : MState) (tt : TempTys) : Prop :=
  TypedAssignment dm C Γ ρ st ∧ MembershipT dm C Γ ρ st tt ∧ WF dm C Γ ρ st

end

/-! ## The clause at the value in flight -/

section
variable (K : RunCtx) (ρ : Assignment) (φ : Future)

/-- **The typed temporary carries the evaluation's membership** (proved): with the value `v` pushed in
flight at its type `T` (`withTemp`, `TempTys.push`), `MembershipT` at that temporary is the membership
of `v` at `T`, under every future typed for the state with it in flight. So a statement concluding
`GoodT (st'.withTemp v) (tt.push st' (some T))` concludes what `Rules/InFlight.EvalMemConcl` asks. -/
theorem goodT_push_mem (st : MState) (tt : TempTys) (v T : Value) (fr : Frame)
    (hfr : st.env[st.env.size - 1]? = some fr)
    (hg : GoodT K.dm K.M K.Γ ρ (st.withTemp v) (tt.push st (some T))) :
    ∀ ψ, TypedFutureT K.dm K.M K.Γ ρ (st.withTemp v) (tt.push st (some T)) ψ →
      DataModel.pmem K.dm.read K.Γ (Value.mean K.dm K.M K.Γ ρ ψ (Value.tyS K.dm K.M K.Γ ρ T) v)
        (Value.tyM K.dm K.M K.Γ ρ (fun _ => .err) T) := by
  intro ψ hψ
  have htmp : (st.withTemp v).env[st.env.size - 1]?.bind (·.temps[fr.temps.size]?) = some v := by
    simp [MState.withTemp, Array.getElem?_modify, hfr]
  have htt : (tt.push st (some T)) (st.env.size - 1) fr.temps.size = some T := by
    simp [TempTys.push, TempTys.set, MState.nextTemp, hfr]
  have hp : MState.posTyMT K.dm K.M K.Γ ρ (st.withTemp v) (tt.push st (some T)) (.temp (st.env.size - 1) fr.temps.size) =
      some (Value.tyM K.dm K.M K.Γ ρ (fun _ => .err) T) := by
    simp only [MState.posTyMT, htmp, htt, Option.map_some]
  have hm := hg.2.1.pos ψ hψ _ _ hp
  simpa only [Env.meanT, htmp, Env.hintAtT, htt] using hm

/-- **The conclusion of a step that returns a value, with the temporaries typed** (the form `SimConclT`
takes under D81): as `SimConclT`, with `GoodT` of the state after with the value in flight at the type
the checker returned (`T?`; `none` for an untyped run, which owes nothing of the value), the
temporaries below keeping their types (`tt`). Its hypotheses take `GoodT st tt` in place of `Good st`. -/
def SimConclTT (π : Nat → Nat) (st st' : MState) (tt : TempTys) (s : SState) (x : Assignment → SM Res)
    (v : Value) (T? : Option Value) : Prop :=
  ∃ (ρ' : Assignment) (Δ' : Nat → TyS) (π' : Nat → Nat) (r : Res) (s' : SState), st.absTy.size ≤ st'.absTy.size ∧
    st.nextLoan ≤ st'.nextLoan ∧ (∀ σ, σ < st.absTy.size → ρ' σ = ρ σ ∧ Δ' σ = K.Δ σ) ∧ (∀ l, l < st.nextLoan → π' l = π l) ∧
    x ρ' s = some (r, s') ∧
    meanV { K with Δ := Δ' } ρ' (fun l => φ (π' l)) r.2 v = r.1 ∧
    (∀ T, T? = some T → StrAgree { K with Δ := Δ' } ρ' T r.2) ∧
    CtxOk { K with Δ := Δ' } ρ' st' ∧ Rel { K with Δ := Δ' } ρ' φ π' (st'.withTemp v) s' ∧
    GoodT K.dm ({ K with Δ := Δ' } : RunCtx).M K.Γ ρ' (st'.withTemp v) (tt.push st' T?)

set_option linter.unusedVariables false in
/-- **The evaluation step under D81** (the form `eval_step_stmt` takes): from a state good with its
temporaries typed, the value returned is in flight at the type returned. No `StrAgree` exception is
needed for the value's membership: a proof's value `⋆` sits at its proposition `T`, and its membership
there is the proposition's truth, which `proof_step` owes. -/
def eval_step_stmtT (fuel : Nat) : Prop :=
  ∀ (st st' : MState) (tt : TempTys) (typed : Bool) (t : Term) (hint : Option Value)
    (v : Value) (T? : Option Value)
    (hg : GoodT K.dm K.M K.Γ ρ st tt) (hctx : CtxOk K ρ st)
    (s : SState) (π : Nat → Nat) (hs : Rel K ρ φ π st s)
    (hok : typed = false → (runT K ρ φ st.tailNext (hintM K ρ hint) t s).isSome)
    (hD : DecTab K.D st')
    (bh : Nat) (h : Runs (Ochr.eval fuel typed t hint) st bh (v, T?) st'),
    SimConclTT K ρ φ π st st' tt s (fun ρ' => runT K ρ' φ st.tailNext (hintM K ρ hint) t) v
      (if typed then T? else Option.none)

end

/-! ## The return path: membership at the declared type

The checker establishes a body's (or a constant's) value at its declared type in three steps, and
[Return] is only the last: (1) the evaluation returns the value at a type `T`, a member of it (the
clause above); (2) `conv T G` succeeds against the goal `G`, and conversion is sound on types that
are well typed inside (`Rules/ComposeT.conv_sound_T` on `origin/rules-trial`, under its named
premises): `⟦T⟧ = ⟦G⟧`; (3) `wholeReturned` and [Return]'s [Repack]: a whole value that is a member
of `G` while open is a member (`RepackSound`). `bodyReturns_sound_stmt` claimed all of it from (3)
alone and is false (`Regress/EvalMemGap.bodyReturns_false`); so is `repackCheck_sound_stmt`
(`repackCheck_false`). -/

section
variable (dm : DataModel) (C : CodeMeaning) (Γ : List IndDecl) (ρ : Assignment)

/-- **[Return]'s and [Repack]'s honest content** (the restatement of `bodyReturns_sound_stmt` and
`repackCheck_sound_stmt`; a guess, not proved): a whole value that is a (possibly open) member of `T`
and passes [Repack] at `T` is a member. For a value with no dependent constructor the check does
nothing, so this says an open non-member never lacks one: `OpenIn` arises only at [Open]. -/
def RepackSound (fuel : Nat) : Prop :=
  ∀ (st st' : MState) (what : String) (v T : Value) (bh : Nat),
    Runs (Ochr.repackCheck fuel what v T) st bh () st' → ∀ ψ : Future,
    DataModel.pmem dm.read Γ (Value.mean dm C Γ ρ ψ (Value.tyS dm C Γ ρ T) v) (Value.tyM dm C Γ ρ (fun _ => .err) T) →
    (Value.mean dm C Γ ρ ψ (Value.tyS dm C Γ ρ T) v).whole →
    Value.mean dm C Γ ρ ψ (Value.tyS dm C Γ ρ T) v ∈ₛ[dm.read] Value.tyM dm C Γ ρ (fun _ => .err) T

/-- **The return path, composed** (proved): from the value's membership at the type the evaluation
returned, conversion's soundness at the two types (their meanings agree), wholeness, and [Repack]'s
content at the goal, the value is a whole member of the goal. -/
theorem return_member (v T G : Value) (F : Future → Prop)
    (hmem : ∀ ψ, F ψ → DataModel.pmem dm.read Γ (Value.mean dm C Γ ρ ψ (Value.tyS dm C Γ ρ T) v)
      (Value.tyM dm C Γ ρ (fun _ => .err) T))
    (hconv : Value.tyM dm C Γ ρ (fun _ => .err) T = Value.tyM dm C Γ ρ (fun _ => .err) G)
    (hwhole : ∀ ψ, F ψ → (Value.mean dm C Γ ρ ψ (Value.tyS dm C Γ ρ G) v).whole)
    (hrep : ∀ ψ, F ψ → DataModel.pmem dm.read Γ (Value.mean dm C Γ ρ ψ (Value.tyS dm C Γ ρ G) v)
      (Value.tyM dm C Γ ρ (fun _ => .err) G) → (Value.mean dm C Γ ρ ψ (Value.tyS dm C Γ ρ G) v).whole →
      Value.mean dm C Γ ρ ψ (Value.tyS dm C Γ ρ G) v ∈ₛ[dm.read] Value.tyM dm C Γ ρ (fun _ => .err) G) :
    ∀ ψ, F ψ → Value.mean dm C Γ ρ ψ (Value.tyS dm C Γ ρ G) v ∈ₛ[dm.read] Value.tyM dm C Γ ρ (fun _ => .err) G ∧
      (Value.mean dm C Γ ρ ψ (Value.tyS dm C Γ ρ G) v).whole := by
  intro ψ hψ
  have hS : Value.tyS dm C Γ ρ T = Value.tyS dm C Γ ρ G := by
    simp only [Value.tyS]; exact congrArg TyS.plain hconv
  have hm := hmem ψ hψ
  rw [hS, hconv] at hm
  exact ⟨hrep ψ hψ hm (hwhole ψ hψ), hwhole ψ hψ⟩

end

/-! ## Model facts the table of D81 names (beyond the checker's checks) -/

/-- A proposition is a member of `Prop` (proved): what `Eq` and `Id` return. -/
theorem prop_mem_univ0 (R : DataRead) (P : Prop) : Sem.ty (TyM.prop P) ∈ₛ[R] TyM.univ 0 :=
  ⟨ULift.up P, rfl⟩

/-- **Π-elimination**: a member of a function type's code, applied at arguments, gives a member of
the codomain at them (stated here; PROVED by the data layer, `ApplyMem.app_mem`, with the argument
hypothesis unused: reaching the codomain decodes every argument at its parameter's code). What a
call's result's membership rests on when the callee is a global, a function parameter or a variable;
η at `Unit` is `ApplyMem.app_mem_unit`. -/
theorem app_mem (R : DataRead) (f : Res) (args : List Res) (s : SState) (B : TyM)
    (hf : f.1 ∈ₛ[R] f.2.m) (hargs : ArgsMember R f.2.m args)
    (hcod : f.2.m.codAt? R (args.map (·.1)) = some (false, B)) :
    ∃ r s', callOf R f args s = some (r, s') ∧ r.1 ∈ₛ[R] B :=
  Ochr.Meaning.app_mem R f args s B hf hargs hcod

end Ochr.Meaning.Steps
