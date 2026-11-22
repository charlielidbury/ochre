import Ochr.Meaning.Strict.WitnessHint
import Ochr.Meaning.Steps.ColumnPlumb
import Ochr.Meaning.Steps.MasterGuards

/-!
# Tail position hands the hint: the regression, on both sides (lead23, 2026-11-22; docs/31 D156)

The model change of docs/31 D151's ruling (d): in tail position the reference's `let`, `;` and the arms of both
matches hand their own hint to the tail or arm (`Run.tailHint`), as the checker's tail check (`checkTail`) hands
the goal down; out of tail position nothing changes.

**The checker** (`TailHintRegress`, every verdict guarded): with `inductive L (A : Type) := N | C(h : A, t : L(A))`,
`F (n : Nat) : L(Nat) := let x = n; N`, the match `F2`, the sequence `F3` are accepted, and so are the nested
cases a match inside the tail of a `let` in tail position (`G1`) and a `let` inside an arm of a tail match (`G2`);
the constant `H : L(Nat) := let x = Z; N` (a constant's body is run by `eval`, not in tail position), a `let`
whose binding is a `let` ending in `N` (`G3`: the binding is not in tail position) and `let x = N; x` (`G4`) are
rejected ("cannot infer the parameter A of N").

**The reference** (kernel-checked, at `Strict.Witness`'s `Opt(A) := None | Some(v : A)`, whose bare `None` is
`L`'s bare `N` for the reference: a declaration with a parameter, a constructor with no field): in tail position,
at a hint naming `Opt`'s record, `Z; None` and `let x = Z; None` run to `None`; out of tail position (a constant's
body) both fail, as `H` fails. A `let` whose binding is `let y = Z; None` fails in tail position too: the binding
runs out of tail position. The arms of a tail match: columns `P`, `R`, `Not` and `Box`, whose bodies end in a
match, run as before at every hint (their arms read none, or read it as their own type).
-/

open Ochr.Test

ochr TailHintRegress {
  inductive L (A : Type) := N | C(h : A, t : L(A))
  def F (n : Nat) : L(Nat) := let x = n; N
  def F2 (n : Nat) : L(Nat) := match n { Z => N, S(m) => N }
  def F3 (n : Nat) : L(Nat) := (n; N)
  reject def H : L(Nat) := let x = Z; N
  def G1 (n : Nat) : L(Nat) := let x = n; match x { Z => N, S(m) => N }
  def G2 (n : Nat) : L(Nat) := match n { Z => let y = Z; N, S(m) => N }
  reject def G3 (n : Nat) : L(Nat) := let x = (let y = n; N); x
  reject def G4 (n : Nat) : L(Nat) := let x = N; x
}

namespace Ochr.Meaning.Steps.Form.TailHintRegress

open Ochr Ochr.Meaning Ochr.Meaning.Strict Ochr.Meaning.Strict.Witness
open Classical

/-- The checker's verdict on one definition of `TailHintRegress`: `""` if accepted, else the message. -/
def verdict (nm : String) : String :=
  match ((Ochr.Test.runWith none "TailHintRegress" TailHintRegress {} (located := false)).rows.find? (·.name == nm)) with
  | some r => match r.verdict with
    | Ochr.Verdict.accepted => ""
    | Ochr.Verdict.rejected m _ => m
    | Ochr.Verdict.undecided _ => "?"
  | none => "?"

#guard (Ochr.Test.runWith none "TailHintRegress" TailHintRegress {} (located := false)).allAsExpected
#guard ["H", "G3", "G4"].all fun nm => (verdict nm).startsWith "cannot infer the parameter A of N"

section
variable (dm : DataModel) (r : Rec)

/-- **The bare `None` at a hint naming `Opt`'s record runs**, in or out of tail position (`run_noneT_hint`, at
every tail flag: the constructor's clause reads none). -/
theorem run_noneT_hintT (hok : dm.RecLeafOk optD r) (ρ : Assignment) (x : Hint) (tl : Bool) (T : TyS)
    (hT : T.m = dm.tyR optD r) (s : SState) :
    runT (KO dm) ρ φw tl T (noneT x) s = some ((DataModel.ctorR optD r 0 [], .plain (dm.tyR optD r)), s) := by
  rw [← run_noneT_hint dm r hok ρ x T hT s, noneT, runT, runT]

/-- `Z` runs to `0` at every hint and tail flag. -/
theorem run_zeroO (ρ : Assignment) (tl : Bool) (T : TyS) (s : SState) :
    runT (KO dm) ρ φw tl T .zero s = some ((.el0 Nat 0, .plain TyM.nat), s) := by
  rw [runT]; rfl

/-- **`Z; None` in tail position runs** at a hint naming `Opt`'s record (`F3`'s shape): the sequence hands its
tail its own hint. -/
theorem run_seqNone_tail (hok : dm.RecLeafOk optD r) (ρ : Assignment) (x : Hint) (T : TyS)
    (hT : T.m = dm.tyR optD r) (s : SState) :
    runT (KO dm) ρ φw true T (.seq .zero (noneT x)) s =
      some ((DataModel.ctorR optD r 0 [], .plain (dm.tyR optD r)), s) := by
  rw [runT]
  show SM.erasedIf (false, false) _ s = _
  simp only [SM.erasedIf, SM.stmtIf, Bool.false_eq_true, if_false]
  simp only [Bind.bind, run_zeroO, SM.guardMod, DiscardOk, discardEnd, tailHint_true]
  simp [TyS.plain, run_noneT_hintT dm r hok ρ x true T hT]

/-- **Out of tail position `Z; None` fails** (a constant's body, `H`'s shape): its tail gets no hint. -/
theorem run_seqNone_notail (ρ : Assignment) (x : Hint) (T : TyS) (s : SState) :
    runT (KO dm) ρ φw false T (.seq .zero (noneT x)) s = none := by
  rw [runT]
  show SM.erasedIf (false, false) _ s = _
  simp only [SM.erasedIf, SM.stmtIf, Bool.false_eq_true, if_false]
  simp only [Bind.bind, run_zeroO, SM.guardMod, DiscardOk, discardEnd, tailHint_false,
    runT_noneT_noHint (K := KO dm) (fun _ _ => rfl) rfl]
  simp [TyS.plain]

/-- One frame with no binding and no label. -/
def sO : SState := { env := [{ binds := [] }], shape := fun _ => none, nextLoan := 0 }

/-- **`let x = Z; None` in tail position runs** at a hint naming `Opt`'s record (`F`'s shape), from one frame
with nothing lent: the `let` hands its tail its own hint, and the drop of `x` ends nothing. -/
theorem run_letNone_tail (hok : dm.RecLeafOk optD r) (ρ : Assignment) (y x : Hint) (T : TyS)
    (hT : T.m = dm.tyR optD r) :
    ∃ s', runT (KO dm) ρ φw true T (.letIn y .zero (noneT x)) sO =
      some ((DataModel.ctorR optD r 0 [], .plain (dm.tyR optD r)), s') := by
  rw [runT]
  show ∃ s', SM.erasedIf (false, false) _ sO = _
  simp only [SM.erasedIf, SM.stmtIf, Bool.false_eq_true, if_false]
  simp only [Bind.bind, run_zeroO, Option.bind_some, tailHint_true, run_noneT_hintT dm r hok ρ x true T hT]
  -- after the push: one frame holding `y`, nothing shaped, so no label is live and the drop ends nothing
  have hS : ∀ b : SBinding, b.ty.label = none →
      pushBindShaped sO b = { sO with env := [{ binds := [b] }] } := fun b hb => by
    unfold pushBindShaped; rw [hb]; rfl
  rw [hS _ rfl]
  have hSl : ∀ b : SBinding, ({ sO with env := [{ binds := [b] }] } : SState).liveLabels = [] := fun _ => by
    unfold SState.liveLabels
    have e : ∀ (L : List Pos), L.filterMap (fun _ => (none : Option Nat)) = [] := fun L => by
      induction L with
      | nil => rfl
      | cons _ _ ih => simpa using ih
    simp only [sO, e]; exact List.mergeSort_nil
  refine ⟨_, if_pos ?_⟩
  exact accessOk_noSites fun l h => by rw [hSl] at h; cases h

/-- **A `let` whose binding is `let y = Z; None` fails in tail position** (`G3`'s shape): the binding runs out of
tail position, where its own tail gets no hint. -/
theorem run_letLetNone_tail (ρ : Assignment) (x y z : Hint) (T : TyS) (s : SState) :
    runT (KO dm) ρ φw true T (.letIn x (.letIn y .zero (noneT z)) (.place (.var 0))) s = none := by
  rw [runT]
  show SM.erasedIf (false, false) _ s = _
  simp only [SM.erasedIf, SM.stmtIf, Bool.false_eq_true, if_false]
  simp [tailNone_none (K := KO dm) (fun _ _ => rfl) rfl]

end

end Ochr.Meaning.Steps.Form.TailHintRegress
