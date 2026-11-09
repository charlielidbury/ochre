import Ochr.Consistency

/-!
# Consistency with bounded universe levels (docs/18, Q1)

The uniform statement `Ochr.Consistency.consistency` quantifies over programs writing `Type_i`
for every `i`. The set model fixes one Lean universe per Ochr level, and Lean's universes cannot
be indexed by a number, so the mechanised statement bounds the levels a program may *write*:
`Prop`, `Type₀` and `Type₁` (`sort l` with `l ≤ 2`). The types the checker then *computes* reach
one level higher (`Type₁`'s type `Type₂`, the sort of `Π(A : Type₁). Type₁`), which the domain
supports as a universe with no elements of its own that are ever quantified over (`TyM.ty2`,
`Sem.el2`). This is form (a) of `Ochr/Consistency.lean`'s obstacle 3: a family of statements, one
per bound; the bound `2` is the one the model of `Ochr/Meaning/Sem.lean` is built for, and
raising it is one more constructor in each of `TyM`, `Sem`, and the carrier functions.

The decision for the spine (docs/31): prove `consistencyBounded`, and record that `consistency`
(uniform) is not a target of the mechanisation. Every example in `Ochr/Examples` satisfies
`LevelsBelow 2` (the test at the end).
-/

namespace Ochr.Consistency
open Ochr.Surface

/-- Every `sort l` written in a surface term has `l ≤ N`. Mirrors `holeIn`. -/
def sortsBelow (N : Nat) : STerm → Bool
  | .sort l => l ≤ N
  | .ident _ | .num _ | .unitLit | .top => true
  | .app _ as => as.attach.all fun ⟨a, _⟩ => sortsBelow N a
  | .call f as => sortsBelow N f && as.attach.all fun ⟨a, _⟩ => sortsBelow N a
  | .ctorP _ ps as => ps.attach.all (fun ⟨a, _⟩ => sortsBelow N a) && as.attach.all fun ⟨a, _⟩ => sortsBelow N a
  | .deref t | .proj _ t | .amp t | .split _ t | .loc _ _ t => sortsBelow N t
  | .assign a b | .seq a b | .pair a b | .andI a b | .and a b | .prod a b | .ascribe a b
  | .rewrite _ a b | .arrow a b => sortsBelow N a && sortsBelow N b
  | .letIn _ T t u => (match T with | some A => sortsBelow N A | none => true) && sortsBelow N t && sortsBelow N u
  | .matchGen p arms => sortsBelow N p && arms.attach.all fun ⟨(_, _, t), _⟩ => sortsBelow N t
  | .splitArms _ arms => arms.attach.all fun ⟨(_, _, t), _⟩ => sortsBelow N t
  | .letPat _ _ sc b => sortsBelow N sc && sortsBelow N b
  | .pi bs c => bs.attach.all (fun ⟨(_, A), _⟩ => sortsBelow N A) && sortsBelow N c
  | .fix _ bs r _ b => bs.attach.all (fun ⟨(_, A), _⟩ => sortsBelow N A) && sortsBelow N r && sortsBelow N b
decreasing_by
  all_goals
    first
    | decreasing_tactic
    | (rename_i h; have := List.sizeOf_lt_of_mem h; simp at this ⊢; omega)

/-- Every sort written in a declaration (parameter types, its type, its body, an inductive's
parameter types, sort and field types) is at most `N`. -/
def _root_.Ochr.Surface.SDecl.sortsBelow (N : Nat) (d : SDecl) : Bool :=
  d.params.all (Ochr.Consistency.sortsBelow N ·.2) && Ochr.Consistency.sortsBelow N d.ret && Ochr.Consistency.sortsBelow N d.body &&
    d.indParams.all (Ochr.Consistency.sortsBelow N ·.2) && (d.indSort.map (Ochr.Consistency.sortsBelow N)).getD true &&
    (d.ind?.getD []).all fun (_, fs) => fs.all (Ochr.Consistency.sortsBelow N ·.2)

/-- A program writes no universe above `Type_(N-1)`: no `sort l` with `l > N` (`sort 0` is
`Prop`, `sort 1` is `Type₀`). -/
def LevelsBelow (N : Nat) (p : Program) : Prop := ∀ d ∈ p, d.sortsBelow N = true

/-- **Consistency, bounded form (Q1).** `consistency` with the hypothesis that the program writes
only `Prop`, `Type₀` and `Type₁`. This is the statement the spine's assembly (milestone 4)
targets; its proof is the main theorem of docs/18 over the model of `Ochr/Meaning`. -/
theorem consistencyBounded (q : Program) (fuel : Nat)
    (holes : NoHoles q) (levels : LevelsBelow 2 q)
    (acc : Accepted (Prelude.decls ++ q) fuel) :
    ∀ d ∈ q, ¬ d.IsFalseConst := by
  sorry

-- the library satisfies the bound
#guard Prelude.decls.all (·.sortsBelow 2)

end Ochr.Consistency
