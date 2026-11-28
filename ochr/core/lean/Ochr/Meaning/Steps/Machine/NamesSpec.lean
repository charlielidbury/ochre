import Ochr.Meaning.Steps.Machine.CheckIndSpec

/-!
# What an accepted item's check establishes of its names (exists13)

For `checkInd`, the runs of D118's two `undeclaredCheck`s (parameter types with the declaration's own name
excluded, D133; field types with it admitted), kept by the peel `runs_checkInd_undeclared`.

For `checkDef`, a peel as `runs_checkDef_tables` (`CheckItem.lean`) peels it, keeping what `NamesFact` needs:
the name was not a global before (`declared`), D118's `undeclaredCheck` passed on the parameter types, the
codomain and the body at the state the definition is checked from, and the global appended is named after the
definition, with the written Π-type `Π(x̄ : Ā). B` as its stored type when it has parameters (a constant's
stored type is its goal VALUE, evaluated: not read here).
-/

namespace Ochr.Meaning.Steps.Machine
open Ochr Ochr.Meaning Ochr.Meaning.Steps Ochr.Meaning.DecideScope Ochr.Meaning.Steps.Slice
open Ochr.Meaning.Steps.Form

set_option maxHeartbeats 8000000 in
/-- **An accepted definition's names** (exists13). -/
theorem runs_checkDef_names {d : Def} {st st' : MState} {b : Nat} (h : Runs (checkDef d) st b () st') :
    st.globals.any (·.name == d.name) = false ∧
    Term.undeclaredList (fun m => st.globals.any (·.name == m))
      (fun m => none == some m || (none != some m && st.inds.any (·.name == m))) (d.doms ++ [d.cod, d.body]) = none ∧
    ∃ g : GDef, st'.globals = st.globals ++ [g] ∧ g.name = d.name ∧
      (d.doms.isEmpty = false → g.ty = .tPi [] (.pi d.hs d.doms d.cod) []) := by
  have hET : ∀ (G : Tab) (f : Nat) (t : Term), GrowsIn G (Ochr.evalType f t) := fun G f => (machineGrows f).evalType
  have hEv : ∀ (G : Tab) (f : Nat) (typed : Bool) (t : Term) (hint : Option Value), GrowsIn G (Ochr.eval f typed t hint) :=
    fun G f => (machineGrows f).eval
  have hCv : ∀ (G : Tab) (f : Nat) (v w : Value), GrowsIn G (Ochr.conv f v w) := fun G f => (machineGrows f).conv
  have hBR : ∀ (G : Tab) (f : Nat) (what : String) (v T : Value) (lent : List Place) (lw : String),
      GrowsIn G (Ochr.bodyReturns f what v T lent lw) := fun G f => (machineGrows f).bodyReturns
  have hCF : ∀ (G : Tab) (f : Nat) (fv : Value) (cs : List Value) (t : Term) (capRec : Array (Option Nat))
      (rd : List (DeclInfo × Value)), GrowsIn G (Ochr.checkFix f fv cs t capRec rd) := fun G f => (machineGrows f).checkFix
  unfold checkDef at h
  dsimp (config := { proj := false }) only at h
  obtain ⟨c, s₁, b₁, hd, h⟩ := Runs.bind_inv h
  obtain ⟨hc, hs₁⟩ := runs_declared_inv hd
  subst hs₁
  clear hd
  cases c
  case true =>
    rw [if_pos rfl] at h
    obtain ⟨_, _, _, he, _⟩ := Runs.bind_inv h; exact (runs_err_false he).elim
  rw [if_neg Bool.false_ne_true] at h
  have hfresh : s₁.globals.any (·.name == d.name) = false := by
    cases e : s₁.globals.any (·.name == d.name)
    · rfl
    · rw [e, Bool.true_or] at hc; cases hc
  by_cases hm : (d.cod :: d.doms).any (Term.mentionsConst d.name) = true
  · rw [if_pos hm] at h
    obtain ⟨_, _, _, he, _⟩ := Runs.bind_inv h; exact (runs_err_false he).elim
  rw [if_neg hm] at h
  by_cases hr : (!((d.cod :: d.doms).all Term.refTopOk && d.body.refsOk)) = true
  · rw [if_pos hr] at h
    obtain ⟨_, _, _, he, _⟩ := Runs.bind_inv h; exact (runs_err_false he).elim
  rw [if_neg hr] at h
  obtain ⟨_, s₂, b₂, hg₂, h⟩ := Runs.grows_bind (fun G => by grows_goI) h
  obtain ⟨_, s₃, b₃, hg₃, h⟩ := Runs.grows_bind (fun G => by grows_goI) h
  obtain ⟨_, s₄, b₄, hg₄, hUD, h⟩ := Runs.grows_bind' (fun G => by grows_goI) h
  have hud := runs_undeclaredCheck_inv hUD
  have h₃ : TablesGrow s₁ s₃ := hg₂.trans hg₃
  rw [h₃.globals, h₃.inds] at hud
  have h₀ : TablesGrow s₁ s₄ := h₃.trans hg₄
  clear hg₂ hg₃ hg₄
  refine ⟨hfresh, hud, ?_⟩
  by_cases he : d.doms.isEmpty = true
  · rw [if_pos he, runs_modify_bind] at h
    obtain ⟨_, s₅, b₅, hg₅, h⟩ := Runs.grows_bind (fun G => by grows_goI) h
    obtain ⟨_, s₆, b₆, hg₆, h⟩ := Runs.grows_bind (fun G => by grows_goI) h
    obtain ⟨_, s₇, b₇, hg₇, h⟩ := Runs.grows_bind (fun G => by grows_goI) h
    obtain ⟨_, s₈, b₈, hg₈, h⟩ := Runs.grows_bind (fun G => by grows_goI) h
    obtain ⟨_, s₉, b₉, hg₉, h⟩ := Runs.grows_bind (fun G => by grows_goI) h
    obtain ⟨_, s₁₀, b₁₀, hg₁₀, h⟩ := Runs.grows_bind (fun G => by grows_goI) h
    obtain ⟨_, s₁₁, b₁₁, hg₁₁, h⟩ := Runs.grows_bind (fun G => by grows_goI) h
    obtain ⟨_, s₁₂, b₁₂, hg₁₂, h⟩ := Runs.grows_bind (fun G => by grows_goI) h
    obtain ⟨c, s₁₃, b₁₃, hg₁₃, h⟩ := Runs.grows_bind (fun G => by grows_goI) h
    have hT : TablesGrow s₁ s₁₃ := by
      refine h₀.trans (TablesGrow.trans ?_ ((((((((hg₅.trans hg₆).trans hg₇).trans hg₈).trans hg₉).trans hg₁₀).trans
        hg₁₁).trans hg₁₂).trans hg₁₃))
      exact ⟨rfl, rfl, Nat.le_refl _, fun _ _ => rfl, Nat.le_refl _, Nat.le_refl _⟩
    clear hg₅ hg₆ hg₇ hg₈ hg₉ hg₁₀ hg₁₁ hg₁₂ hg₁₃ h₀
    cases c
    all_goals first | rw [if_pos rfl] at h | rw [if_neg Bool.false_ne_true] at h
    all_goals
      rw [runs_pure_bind', runs_get_bind] at h
      obtain ⟨_, s₁₄, b₁₄, hg₁₄, h⟩ := Runs.grows_bind (fun G => by grows_goI) h
      have hst := runs_modify_inv h
      subst hst
      refine ⟨_, by rw [hg₁₄.globals, hT.globals], rfl, fun hne => ?_⟩
      rw [he] at hne; cases hne
  · rw [if_neg he] at h
    by_cases hi : d.implBy.isSome = true
    · rw [if_pos hi, runs_pure_bind', runs_modify_bind] at h
      have hT := Runs.grows (growsM_of_growsIn fun G => by grows_goI) h
      exact ⟨_, by rw [hT.globals]; show s₄.globals ++ _ = _; rw [h₀.globals], rfl, fun _ => rfl⟩
    · rw [if_neg hi] at h
      obtain ⟨_, s₅, b₅, hg₅, h⟩ := Runs.grows_bind (fun G => by grows_goI) h
      rw [runs_modify_bind] at h
      have hT := Runs.grows (growsM_of_growsIn fun G => by grows_goI) h
      exact ⟨_, by rw [hT.globals]; show s₅.globals ++ _ = _; rw [hg₅.globals, h₀.globals], rfl, fun _ => rfl⟩

set_option maxHeartbeats 8000000 in
/-- **An accepted inductive declaration's names** (exists13): D118's two checks passed, at the declarations
before it with its stub appended (`checkInd`'s first `modify`) and the globals it starts from. -/
theorem runs_checkInd_undeclared {d : IndDecl} {st st' : MState} {b : Nat} (h : Runs (checkInd d) st b () st') :
    Term.undeclaredList (fun m => st.globals.any (·.name == m))
      (fun m => none == some m || (some d.name != some m &&
        (st.inds ++ [{ d with ctors := [], nestable := [], declaring := true }]).any (·.name == m)))
      (d.params.map (·.2)) = none ∧
    Term.undeclaredList (fun m => st.globals.any (·.name == m))
      (fun m => some d.name == some m || (none != some m &&
        (st.inds ++ [{ d with ctors := [], nestable := [], declaring := true }]).any (·.name == m)))
      (d.ctors.flatMap (·.2.map (·.2))) = none := by
  have hET : ∀ (G : Tab) (f : Nat) (t : Term), GrowsIn G (Ochr.evalType f t) := fun G f => (machineGrows f).evalType
  have hFT : ∀ (G : Tab) (f : Nat) (d : IndDecl) (ps : List Value) (c : Nat) (val : Nat → Value → M Value),
      (∀ i v, GrowsIn G (val i v)) → ∀ upto, GrowsIn G (Ochr.fieldTele f d ps c val upto) :=
    fun G f => (machineGrows f).fieldTele
  unfold checkInd at h
  dsimp (config := { proj := false }) only at h
  obtain ⟨c, s₁, b₁, hd, h⟩ := Runs.bind_inv h
  obtain ⟨hc, hs₁⟩ := runs_declared_inv hd
  subst hs₁
  clear hd
  cases c
  case true =>
    rw [if_pos rfl] at h
    obtain ⟨_, _, _, he, _⟩ := Runs.bind_inv h; exact (runs_err_false he).elim
  rw [if_neg Bool.false_ne_true] at h
  obtain ⟨_, s₂, b₂, hg₂, h⟩ := Runs.grows_bind (fun G => by grows_goI) h
  by_cases hsort : d.sort > 1
  · rw [if_pos hsort] at h
    obtain ⟨_, _, _, he, _⟩ := Runs.bind_inv h; exact (runs_err_false he).elim
  rw [if_neg hsort] at h
  rw [runs_get_bind, runs_get_bind, runs_modify_bind] at h
  obtain ⟨_, s₃, b₃, hg₃, h⟩ := Runs.grows_bind (fun G => by grows_goI) h
  obtain ⟨_, s₄, b₄, hg₄, hL, h⟩ := Runs.grows_bind' (fun G => by grows_goI) h
  obtain ⟨_, s₅, b₅, hg₅, h⟩ := Runs.grows_bind (fun G => by grows_goI) h
  obtain ⟨x, s₆, b₆, hg₆, hTel, h⟩ := Runs.grows_bind' (fun G => by grows_goI) h
  obtain ⟨sc, ns, l⟩ := x
  obtain ⟨_, s₇a, b₇a, hg₇a, h128, h⟩ := Runs.grows_bind' (fun G => by grows_goI) h
  obtain ⟨_, s₇, b₇, hg₇, hTP, h⟩ := Runs.grows_bind' (fun G => by grows_goI) h
  obtain ⟨_, s₇b, b₇b, hg₇b, hUP, h⟩ := Runs.grows_bind' (fun G => by grows_goI) h
  obtain ⟨_, s₈, b₈, hg₈, hUF, h⟩ := Runs.grows_bind' (fun G => by grows_goI) h
  have hP := runs_undeclaredCheck_inv hUP
  have hF := runs_undeclaredCheck_inv hUF
  have hG7 : s₇.globals = s₁.globals := by
    rw [hg₇.globals, hg₇a.globals, hg₆.globals, hg₅.globals, hg₄.globals, hg₃.globals]
    exact hg₂.globals
  have hI7 : s₇.inds = s₁.inds ++ [{ d with ctors := [], nestable := [], declaring := true }] := by
    rw [hg₇.inds, hg₇a.inds, hg₆.inds, hg₅.inds, hg₄.inds, hg₃.inds]
    show s₂.inds ++ _ = _
    rw [hg₂.inds]
  rw [hG7, hI7] at hP
  rw [hg₇b.globals, hG7, hg₇b.inds, hI7] at hF
  exact ⟨hP, hF⟩

end Ochr.Meaning.Steps.Machine
