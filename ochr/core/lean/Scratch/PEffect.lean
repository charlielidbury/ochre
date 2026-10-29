/-!
# Probe: (P) for free, when looking at an unknown is an effect

A machine whose only way to look at a value is to ask a heap (`view`), written as a reified
computation (`Prog`), runs the same under two heaps that agree on everything it asks about.
That is one lemma about `Prog`, proved once (`exec_agree`), and (P) for a machine written this
way is a corollary with no per-construct proof (`P_eval`).
-/

namespace PEffect

/-- A node: its constructor and its children's handles. -/
inductive Sh (α : Type) where
  | zero | succ (a : α) | pair (a b : α)
deriving DecidableEq

/-- A machine computation, reified: it returns, fails, asks what a handle is (`view`: `none` for
an unknown), or stores a new node (`alloc`). -/
inductive Prog (α β : Type) where
  | ret (b : β)
  | fail
  | view (h : α) (k : Option (Sh α) → Prog α β)
  | alloc (s : Sh α) (k : α → Prog α β)

def Prog.bind {α β γ : Type} : Prog α β → (β → Prog α γ) → Prog α γ
  | .ret b, f => f b
  | .fail, _ => .fail
  | .view h k, f => .view h fun o => (k o).bind f
  | .alloc s k, f => .alloc s fun a => (k a).bind f

instance {α : Type} : Monad (Prog α) where
  pure := .ret
  bind := Prog.bind

/-- The heap: what each handle is (`none`: an unknown), and the next fresh handle. -/
structure Heap where
  node : Nat → Option (Sh Nat)
  next : Nat

def Heap.alloc (H : Heap) (s : Sh Nat) : Heap :=
  { node := fun n => if n = H.next then some s else H.node n, next := H.next + 1 }

/-- Refine the handle `σ` to the node `s` (a case split, or an instantiation). -/
def Heap.set (H : Heap) (σ : Nat) (s : Sh Nat) : Heap :=
  { node := fun n => if n = σ then some s else H.node n, next := H.next }

/-- Run a computation against a heap: its result (`none`: it failed) and the final heap. -/
def exec {β : Type} : Prog Nat β → Heap → Option β × Heap
  | .ret b, H => (some b, H)
  | .fail, H => (none, H)
  | .view h k, H => exec (k (H.node h)) H
  | .alloc s k, H => exec (k H.next) (H.alloc s)

/-- The handles a run asks about. -/
def queries {β : Type} : Prog Nat β → Heap → List Nat
  | .ret _, _ | .fail, _ => []
  | .view h k, H => h :: queries (k (H.node h)) H
  | .alloc s k, H => queries (k H.next) (H.alloc s)

/-- **Runs agree when the heaps agree on what is asked.** Two heaps with the same fresh handle
that differ only on a set `D` of existing handles, a run that never asks about `D`: same result,
and final heaps that still differ only on `D`. One induction on `Prog`, for every machine. -/
theorem exec_agree {β : Type} (D : Nat → Prop) :
    ∀ (p : Prog Nat β) (H₁ H₂ : Heap), H₁.next = H₂.next → (∀ n, D n → n < H₁.next) →
    (∀ n, ¬ D n → H₁.node n = H₂.node n) → (∀ h ∈ queries p H₁, ¬ D h) →
    (exec p H₁).1 = (exec p H₂).1 ∧ (exec p H₁).2.next = (exec p H₂).2.next ∧
      ∀ n, ¬ D n → (exec p H₁).2.node n = (exec p H₂).2.node n
  | .ret _, _, _, hn, _, hD, _ => ⟨rfl, hn, hD⟩
  | .fail, _, _, hn, _, hD, _ => ⟨rfl, hn, hD⟩
  | .view h k, H₁, H₂, hn, hlt, hD, hq => by
    have hh : H₁.node h = H₂.node h := hD h (hq h (List.mem_cons_self ..))
    simp only [exec, ← hh]
    exact exec_agree D (k (H₁.node h)) H₁ H₂ hn hlt hD fun x hx => hq x (List.mem_cons_of_mem _ hx)
  | .alloc s k, H₁, H₂, hn, hlt, hD, hq => by
    simp only [exec, ← hn]
    refine exec_agree D (k H₁.next) (H₁.alloc s) (H₂.alloc s) (by simp [Heap.alloc, hn]) ?_ ?_ hq
    · intro n hd; have := hlt n hd; simp [Heap.alloc]; omega
    · intro n hd; simp only [Heap.alloc, hn]; split <;> simp_all

/-! ## A machine written against the effect -/

/-- A slice of terms: variables, constructors, a projection and a match (the two that look). -/
inductive Tm where
  | var (i : Nat) | zero | succ (t : Tm) | pair (a b : Tm) | fst (t : Tm)
  | letIn (u w : Tm) | ifz (t z s : Tm)

/-- The machine, for any type of handles: it cannot look at a handle except through `view`.
`some h` is a result; `none` is stuck (where Ochr closes off). -/
def eval {α : Type} : Nat → Tm → List α → Prog α (Option α)
  | 0, _, _ => .fail
  | _ + 1, .var i, ρ => match ρ[i]? with
    | some h => .ret (some h)
    | none => .fail
  | _ + 1, .zero, _ => .alloc .zero fun h => .ret (some h)
  | f + 1, .succ t, ρ => (eval f t ρ).bind fun
    | some a => .alloc (.succ a) fun h => .ret (some h)
    | none => .ret none
  | f + 1, .pair a b, ρ => (eval f a ρ).bind fun
    | some x => (eval f b ρ).bind fun
      | some y => .alloc (.pair x y) fun h => .ret (some h)
      | none => .ret none
    | none => .ret none
  | f + 1, .fst t, ρ => (eval f t ρ).bind fun
    | some a => .view a fun
      | some (.pair x _) => .ret (some x)
      | none => .ret none        -- an unknown: stuck
      | some _ => .fail
    | none => .ret none
  | f + 1, .letIn u w, ρ => (eval f u ρ).bind fun
    | some a => eval f w (a :: ρ)
    | none => .ret none
  | f + 1, .ifz t z s, ρ => (eval f t ρ).bind fun
    | some a => .view a fun
      | some .zero => eval f z ρ
      | some (.succ p) => eval f s (p :: ρ)
      | none => .ret none        -- an unknown: stuck (where [Split] or [Close] take over)
      | some _ => .fail
    | none => .ret none

/-- **(P) for the whole machine, for free.** A run that never asks about `σ` gives the same result
whatever `σ` is refined to, and leaves the same heap apart from `σ`. No case of `eval` is
inspected: this is `exec_agree` with `D = {σ}`. -/
theorem P_eval (f : Nat) (t : Tm) (ρ : List Nat) (H : Heap) (σ : Nat) (s : Sh Nat)
    (hσ : σ < H.next) (hq : σ ∉ queries (eval f t ρ) H) :
    (exec (eval f t ρ) (H.set σ s)).1 = (exec (eval f t ρ) H).1 := by
  have := exec_agree (· = σ) (eval f t ρ) H (H.set σ s) rfl (by intro n h; omega)
    (by intro n hn; simp [Heap.set, hn]) (by intro h hh e; exact hq (e ▸ hh))
  exact this.1.symm

end PEffect

namespace PEffect
/-- A heap with one unknown, `σ = 0`. -/
def H0 : Heap := { node := fun _ => none, next := 1 }
-- passing `σ` around never asks about it: (P) applies
example : queries (eval 5 (.pair (.var 0) .zero) [0]) H0 = [] := rfl
-- projecting out of `σ` asks about it: (P) does not apply, and the run is stuck there
example : queries (eval 5 (.fst (.var 0)) [0]) H0 = [0] := rfl
example : (exec (eval 5 (.fst (.var 0)) [0]) H0).1 = some none := rfl
end PEffect
#print axioms PEffect.P_eval
#print axioms PEffect.exec_agree
