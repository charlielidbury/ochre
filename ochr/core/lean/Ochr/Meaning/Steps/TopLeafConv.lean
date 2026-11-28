import Ochr.Meaning.Steps.TopLeaf
import Ochr.Meaning.Conv.ComposeFO

/-!
# `LeafConvG` from its parts: the goal read after the pop, N3 at the leaf's type, N3's side conditions (lead48; docs/31 D291)

`Top.Leaf.LeafConvG` (the leaf's type and the goal mean the same type at every assignment meeting the leaf's state) is
DERIVED here from three named facts:
- `LeafGoalPopG` (CHECKER; read true, attacked in `Steps/LeafAttack.lean` (A)): the comparison `fixCont` makes is a
  successful `conv` of the leaf's type against the leaf's own goal, which is set and not a deferred hint;
- `N3Hyps` (the conversion lane's hypotheses of N3 for values that hold no code, `Conv.conv_sound_fo'`);
- `LeafSideG` (MIXED): what N3 asks of the two types beyond the comparison: no code in either (`FO`), no constructor value
  of a `Prop` declaration (`NoProp`, a checker invariant, D42), and the leaf's type has a level at the assignment. The
  goal's level is not asked: it is `Pre`'s (`Asg.goalLv`).
-/

namespace Ochr.Meaning.Steps.Form.Top.Leaf

open Ochr Ochr.Meaning Ochr.Meaning.Steps Ochr.Meaning.Steps.Form Ochr.Meaning.Steps.Form.Master
open Ochr.Meaning.Conv Ochr.Meaning.Strict

/-- **The goal `fixCont` compares the leaf's type with is the leaf's** (CHECKER; READ TRUE against `Machine.lean`:
`wholeReturned` checks, `bodyReturns` (`repackCheck`: `lentUnknown` makes fresh unknowns, `packedErr` compares by `conv`
and reads types by `valType?`, each restoring the state it started from but for names), `pushTempAt`, `popFrame` (its
drops' ends substitute with `types := false`, re-run sealed programs by `nfSealed`, which restores the goal, and mark by
`lendEnv`, `types := false`) and `popTemp` write no goal; the goal at the leaf is set (`checkFix` sets it before the body)
and is a type evaluated by `evalType`, refined by substitutions, never D124's deferred hint. ATTACKED on seven programs,
`LeafAtk` (A): an erased body writing its borrow parameter, `AddMZero`, a goal holding a sealed program refined by the
split, a returned borrow, a stuck call's fill re-run at the pop, a generalisation inside the goal at the end of the body,
a one-constructor parameter refined in place. On main, D142's `popBody` puts an erased function's environment back
before the pop and keeps "the goal as its splits refined it": the fact keeps its content, `fixCont` must be re-copied.) -/
def LeafGoalPopG : Prop :=
  ∀ (n : Nat) (name : String) (v T : Value) (stl stk : MState) (bk : Nat),
    Runs (fixCont n name v T) stl bk () stk →
    ∃ (g : Value) (st₂ st₃ : MState) (b : Nat), stl.goal = some g ∧ deferredHint? g = none ∧
      Runs (Ochr.conv n T g) st₂ b true st₃

/-- **N3's side conditions at the leaf** (MIXED): the leaf's type `T` and the goal `g` hold no code (`FO`: FALSE at a
function whose codomain is a function type or holds a closure, until N3 for code, the conversion lane's `CodeOk`), hold no
constructor value of a `Prop` declaration (`NoProp`, the checker's D42; read true), and `T` means a type with a level at
every assignment meeting the leaf's state (UNREAD; the reference's result type at a typed leaf, which `StrAgree` ties to
`T`, has a level where the result is a member; GoodRes's third case, a result typed `err`, is what this excludes). -/
def LeafSideG : Prop :=
  ∀ (n : Nat) (name : String) (v T : Value) (stl stk : MState) (bk : Nat),
    Runs (fixCont n name v T) stl bk () stk →
    ∀ (K : RunCtx) (ρ : Assignment), Pre K ρ (stl.withTempT v (some T)) → ∀ g, stl.goal = some g →
      FO T ∧ FO g ∧ NoProp K T ∧ NoProp K g ∧
      Fit K.dm.read TyM.err (meanV K ρ (fun _ => .err) (.plain TyM.err) T)

/-- **N3's own hypotheses**, at every context and assignment, at the constant future types are read under (the
conversion lane's, `Conv.conv_sound_fo'`: the function rules `PremFn`, open; the library's `True`/`False`/`And`
shapes `LibDecls` and `And`'s meaning `LibAnd`, read true). -/
def N3Hyps : Prop :=
  ∀ (K : RunCtx) (ρ : Assignment),
    (∀ st, PremFn K ρ (fun _ => .err) (machPremises st)) ∧ LibDecls K ∧ LibAnd K ρ (fun _ => .err)

/-- A meaning whose reading as a type has a level is a type: it fits the error type. -/
theorem fit_err_of_level {R : DataRead} {s : Sem} (h : s.asTy.level.isSome = true) : Fit R TyM.err s := by
  cases s with
  | ty X => exact .inr (.inr ⟨rfl, X, rfl, h⟩)
  | _ => simp [Sem.asTy] at h; cases h

/-- **`LeafConvG` from its parts** (PROVED from `LeafGoalPopG`, `LeafSideG`, `N3Hyps`; the goal's level from `Pre`). -/
theorem leafConvG_of (hp : LeafGoalPopG) (hs : LeafSideG) (hn : N3Hyps) : LeafConvG := by
  intro n name v T stl stk bk hk K ρ hpre
  obtain ⟨g, st₂, st₃, b, hg, hdh, hconv⟩ := hp n name v T stl stk bk hk
  obtain ⟨fT, fg, nT, ng, ftT⟩ := hs n name v T stl stk bk hk K ρ hpre g hg
  obtain ⟨hpf, hld, hla⟩ := hn K ρ
  -- the goal's level: `Pre`'s
  have hgl : (Value.tyM K.dm K.M K.Γ ρ (fun _ => .err) g).level.isSome = true :=
    hpre.asg.goalLv _ (show (stl.withTempT v (some T)).norm.goal.map _ = _ by
      show (stl.withTempT v (some T)).goal.map _ = _
      show stl.goal.map _ = _
      rw [hg]; rfl)
  have ftg : Fit K.dm.read TyM.err (meanV K ρ (fun _ => .err) (.plain TyM.err) g) := by
    apply fit_err_of_level
    rw [← meanV_eq_mean K ρ]; exact hgl
  obtain ⟨-, hal⟩ := conv_sound_fo' (hpf st₂) hld hla hconv fT fg
  have e := hal (.plain TyM.err) TyM.err nT ng ftT ftg
  rw [hg, hintM_of_none hdh]
  show (Value.mean K.dm (codeMeaning K) K.Γ ρ (fun _ => .err) (.plain TyM.err) T).asTy =
    (Value.mean K.dm (codeMeaning K) K.Γ ρ (fun _ => .err) (.plain TyM.err) g).asTy
  rw [meanV_eq_mean K ρ, meanV_eq_mean K ρ, e]

end Ochr.Meaning.Steps.Form.Top.Leaf
