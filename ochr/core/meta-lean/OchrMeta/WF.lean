import OchrMeta.Machine

/-! # Lemma 0 (invariance): every run preserves the well-formedness invariants

meta-model-v1 §2.1 lists W1 (unique holders), W2 (bound loans), W3 (acyclicity) and W4 (clean
crossings).  In this machine they read as follows, for a state with values `V` in flight
(results produced but not yet bound):

* `fresh`: every name is below the fresh-name counter;
* `shallowE`/`shallowV`: no borrows inside data (a value is a borrow of borrow-free content, or
  borrow-free);
* `uniq` (W1): each borrow has one holder (a binding or a value in flight);
* `live` (W2): every loan occurring in the environment is live: its borrow is held;
* `owned`: no dangling borrows: every held borrow's loan occurs in the environment;
* `clean` (W4): values in flight carry no loans;
* `acyc` (W3, as an order): loans inside a borrow's content are younger (larger) than it.
-/

namespace OchrMeta

/-- The borrow a value holds at its top, if any. -/
def Val.held : Val → List Nat
  | .borrow l _ => [l]
  | _ => []

/-- The held borrow with its content. -/
def Val.heldPairs : Val → List (Nat × Val)
  | .borrow l c => [(l, c)]
  | _ => []

/-- Borrows only at the top, with borrow-free content (RULES §1: no borrows inside data). -/
def Val.Shallow (v : Val) : Prop := v.nb = 0 ∨ ∃ l c, v = .borrow l c ∧ c.nb = 0

def Env.held (Ω : Env) : List Nat := Ω.flatten.flatMap fun b => b.2.held
def Env.heldPairs (Ω : Env) : List (Nat × Val) := Ω.flatten.flatMap fun b => b.2.heldPairs

/-- Lemma 0's invariant for a state `s` with the values `V` in flight. -/
structure WFv (s : St) (V : List Val) : Prop where
  fresh : ∀ l, (l ∈ s.env.names ∨ ∃ v ∈ V, l ∈ v.names) → l < s.next
  shallowE : ∀ F ∈ s.env, ∀ b ∈ F, b.2.Shallow
  shallowV : ∀ v ∈ V, v.Shallow
  uniq : (s.env.held ++ V.flatMap Val.held).Nodup
  live : ∀ l ∈ s.env.loans, l ∈ s.env.held ++ V.flatMap Val.held
  owned : ∀ l ∈ s.env.held ++ V.flatMap Val.held, l ∈ s.env.loans
  clean : ∀ v ∈ V, v.loans = []
  acyc : ∀ p ∈ s.env.heldPairs, ∀ m ∈ p.2.loans, p.1 < m

/-- A well-formed state (nothing in flight). -/
def WF (s : St) : Prop := WFv s []

/-- **Lemma 0.** A run from a well-formed state ends in a well-formed state with its result in
flight; the counter only grows; the number of frames is preserved. -/
theorem exec_wf (P : Prog) : ∀ (n : Nat) (s : St) (t : Term) (s' : St) (v : Val),
    WF s → exec P n s t = .ok s' v → WFv s' [v] ∧ s.next ≤ s'.next ∧ s'.env.length = s.env.length := by
  sorry

end OchrMeta
