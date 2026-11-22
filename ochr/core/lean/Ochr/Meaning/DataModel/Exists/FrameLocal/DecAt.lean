import Ochr.Meaning.DataModel.Exists.FrameLocal.Setup
import Ochr.Meaning.DataModel.Exists.Step2

/-!
# Frame locality's obligation on the checker, node by node (exists4)

`DecLocal` (`Setup.lean`) asks locality of the decisions at EVERY term. The run consults the four
decisions it concerns only at four kinds of node, so the obligation is exactly `DecAt` at each node
of the term the run is asked about (and `DecLocal.inv`, a property of `invalidated` alone):

* a match (`.matchNat`, `.matchInd`): the join's drop (`joinMoves`, the checker's `Decide.jdMoves`)
  and [Entry]'s captures (`blockCaps`, `BlockCaps.staticBlockCaps`) name only places already moved
  or rooted at the match's free variables;
* `J` (`.prim "J" [A, a, b, P, h, t]`): the join's drop at the `J` term, [Entry]'s captures at `t`;
* `Id` (`.id A t u`): the re-pointed bindings (`rePointed`, `Decide.typeState`'s `repointed`) of the
  side `t` are rooted at `t`'s free variables;
* `invalidated` (at a borrow, an assignment, a match entry's re-pointed capture): the invalidated
  places share the written place's root (empty in the chain's decisions).

A term with none of the first three kinds of node (`hasDecNode = false`) asks nothing of the table
(`decAll_of_hasDecNode`). The field types and parameter types of `Step2.lean`'s declarations have
none (`#guard` below), so at them frame locality asks of the checker only `DecLocal.inv`.

`runT_qset` still assumes the global `DecLocal`; replacing it by `DecAll` at the term (threaded
through the induction) is the handoff's next item.
-/

namespace Ochr.Meaning.DataModel.Exists.FrameLocal

open Ochr Ochr.Meaning

/-- The join's drop at `t` is local. -/
def JoinLocal (D : Decisions) (t : Term) : Prop :=
  ∀ sc entry q, q ∈ D.joinMoves sc entry t → q ∈ entry ∨ q.root ∈ t.freeVars

/-- [Entry]'s captures at `t` are local. -/
def CapsLocal (D : Decisions) (t : Term) : Prop :=
  ∀ sc entry qk, qk ∈ (D.blockCaps sc entry t).2 → qk.1 ∈ entry ∨ qk.1.root ∈ t.freeVars

/-- The re-pointed bindings of `t` are rooted at its free variables. -/
def RepLocal (D : Decisions) (t : Term) : Prop :=
  ∀ sc q, q ∈ D.rePointed sc t → q.root ∈ t.freeVars

/-- **What the run asks of the decisions at one node** (the obligation, node by node). -/
def DecAt (D : Decisions) : Term → Prop
  | .matchNat p z u => JoinLocal D (.matchNat p z u) ∧ CapsLocal D (.matchNat p z u)
  | .matchInd p n arms => JoinLocal D (.matchInd p n arms) ∧ CapsLocal D (.matchInd p n arms)
  | .id _ t _ => RepLocal D t
  | .prim n args => ∀ A a b P h t, n = "J" → args = [A, a, b, P, h, t] → JoinLocal D (.prim n args) ∧ CapsLocal D t
  | _ => True

theorem DecLocal.decAt {D : Decisions} (hD : DecLocal D) (t : Term) : DecAt D t := by
  cases t <;> simp only [DecAt]
  all_goals first
    | exact ⟨fun sc e q h => hD.join sc e _ q h, fun sc e qk h => hD.caps sc e _ qk h⟩
    | exact fun sc q h => hD.rep sc _ q h
    | exact fun A a b P h t _ _ => ⟨fun sc e q hq => hD.join sc e _ q hq, fun sc e qk hq => hD.caps sc e t qk hq⟩
    | trivial

mutual
/-- Does a term contain a node at which the run consults `joinMoves`, `blockCaps` or `rePointed`? -/
def _root_.Ochr.Term.hasDecNode : Term → Bool
  | .matchNat .. => true
  | .matchInd .. => true
  | .id .. => true
  | .prim n as => n == "J" || Term.hasDecNodeList as
  | .assign _ t | .succ t | .ref t => t.hasDecNode
  | .letIn _ t u | .seq t u | .cong t u | .ascribe t u => t.hasDecNode || u.hasDecNode
  | .eq a b d => a.hasDecNode || b.hasDecNode || d.hasDecNode
  | .pi _ ds c => Term.hasDecNodeList ds || c.hasDecNode
  | .fix _ _ ds c _ b => Term.hasDecNodeList ds || c.hasDecNode || b.hasDecNode
  | .call g as _ => g.hasDecNode || Term.hasDecNodeList as
  | .ctor _ _ _ ps as => Term.hasDecNodeList ps || Term.hasDecNodeList as
  | .tind _ as => Term.hasDecNodeList as
  | _ => false
def _root_.Ochr.Term.hasDecNodeList : List Term → Bool
  | [] => false
  | t :: ts => t.hasDecNode || Term.hasDecNodeList ts
end

/-- At a node that is no match, `J` or `Id`, the run asks nothing of the table. -/
theorem decAt_of_hasDecNode {D : Decisions} {t : Term} (h : t.hasDecNode = false) : DecAt D t := by
  cases t <;> simp only [DecAt] <;> simp_all [Term.hasDecNode]

/-- The field and parameter types of a declaration have no decision node. -/
def IndDecl.noDecNodes (d : IndDecl) : Bool :=
  d.params.all (fun p => !p.2.hasDecNode) && d.ctors.all fun c => c.2.all fun f => !f.2.hasDecNode

/-- The chain's decisions invalidate nothing (`Decisions.invalidated`'s default), so `DecLocal.inv`
holds of them outright. -/
theorem chainDecisions_inv (fuel : Nat) (st : MState) :
    ∀ sc p q, q ∈ (chainDecisions fuel st).invalidated sc p → q.root = p.root := by
  intro sc p q h; simp [chainDecisions, checkerDecisionsFF] at h

/- `Step2.lean`'s declarations (the library, `Bool`, `List`, `Rose`, `TF`, `Ev`, `Q`): no field or
parameter type has a match, a `J` or an `Id`, so frame locality asks nothing of the decision table
there beyond `invalidated`'s root clause. -/
#guard Step2.step2Decls.all IndDecl.noDecNodes

end Ochr.Meaning.DataModel.Exists.FrameLocal
