import Ochr.Heap.Slice

/-!
# The frame property on the heap design (`notes/frame-model.md`)

The paper's property 2 (Assumption 11 (T2)): a run changes the state outside what it was given
only through the borrows it was given, and a call's effect is its isolated run plugged back
into the caller. On the heap design a borrow is a handle to the lender's cell, so this is
*locality*: a run touches only the handles reachable from the ones it holds, and fresh ones.

As for (P) (`exec_agree`), nothing here looks at a case of the evaluator. A computation runs with
capabilities (`execR`): it may view or write only a handle it holds, and store only nodes whose
children it holds; viewing a node grants its children, allocating grants the fresh handle, and
anything else is an error. Whenever a capability run succeeds, the run never asked about the
frame (`cap_queries`), so `exec_agree` gives the isolated run's result, and the frame is left as
it was (`untouched`): `frame`. One induction on `Prog` each, for every computation at once.
-/

namespace Ochr.Heap

/-- The handles the node at `h` points at (none for an unknown or an unallocated handle). -/
def Heap.kids (H : Heap) (h : Nat) : List Nat := ((H.node h).map Node.children).getD []

/-- Run a computation with capabilities `R`. Viewing or writing a handle not held, or storing a
node that points at one, is an error (`none`): a run cannot reach what it was not given. -/
def execR {β : Type} : Prog β → Heap → List Nat → Option (β × Heap × List Nat)
  | .ret b, H, R => some (b, H, R)
  | .view h k, H, R => if h ∈ R then execR (k (H.node h)) H (H.kids h ++ R) else none
  | .alloc n k, H, R =>
    if n.children.all (fun a => decide (a ∈ R)) then execR (k H.next) (H.alloc n) (H.next :: R)
    else none
  | .write h n k, H, R =>
    if h ∈ R ∧ n.children.all (fun a => decide (a ∈ R)) = true then execR k (H.write h n) R
    else none

/-- What a computation holding `R` can reach in `H`: `R`, and whatever a reachable node points at. -/
inductive Reach (H : Heap) (R : List Nat) : Nat → Prop
  | base {h : Nat} : h ∈ R → Reach H R h
  | step {h a : Nat} : Reach H R h → a ∈ H.kids h → Reach H R a

theorem kids_alloc (H : Heap) (n : Node) (h : Nat) :
    (H.alloc n).kids h = if h = H.next then n.children else H.kids h := by
  unfold Heap.kids Heap.alloc; split <;> simp_all

theorem kids_write (H : Heap) (w : Nat) (n : Node) (h : Nat) :
    (H.write w n).kids h = if h = w then n.children else H.kids h := by
  unfold Heap.kids Heap.write; split <;> simp_all

/-- Viewing a held node grants nothing new: its children were reachable already. -/
theorem reach_kids {H : Heap} {R : List Nat} {h m : Nat} (hR : h ∈ R) :
    Reach H (H.kids h ++ R) m → Reach H R m := by
  intro hr
  induction hr with
  | base hm =>
    rcases List.mem_append.mp hm with hk | hm'
    · exact .step (.base hR) hk
    · exact .base hm'
  | step _ hk ih => exact .step ih hk

/-- After an allocation whose children are held, what is reachable is the fresh handle and
what was reachable before. -/
theorem reach_alloc {H : Heap} {R : List Nat} {n : Node} {m : Nat}
    (hc : ∀ a ∈ n.children, a ∈ R) :
    Reach (H.alloc n) (H.next :: R) m → m = H.next ∨ Reach H R m := by
  intro hr
  induction hr with
  | base hm =>
    rcases List.mem_cons.mp hm with h | h
    · exact .inl h
    · exact .inr (.base h)
  | step _ hk ih =>
    rw [kids_alloc] at hk
    split at hk
    · exact .inr (.base (hc _ hk))
    · rcases ih with h1 | h1
      · contradiction
      · exact .inr (.step h1 hk)

/-- A write of a node whose children are held makes nothing new reachable. -/
theorem reach_write {H : Heap} {R : List Nat} {w : Nat} {n : Node} {m : Nat}
    (hc : ∀ a ∈ n.children, a ∈ R) :
    Reach (H.write w n) R m → Reach H R m := by
  intro hr
  induction hr with
  | base hm => exact .base hm
  | step _ hk ih =>
    rw [kids_write] at hk
    split at hk
    · exact .base (hc _ hk)
    · exact .step ih hk

theorem all_mem {R : List Nat} {l : List Nat} (h : l.all (fun a => decide (a ∈ R)) = true) :
    ∀ a ∈ l, a ∈ R := by
  intro a ha; simpa using List.all_eq_true.mp h a ha

/-- **Locality.** A successful capability run asks about (views or writes) only handles it could
reach when it started, and fresh ones. -/
theorem cap_queries {β : Type} : ∀ (p : Prog β) (H : Heap) (R : List Nat) (r : β × Heap × List Nat),
    execR p H R = some r → ∀ q ∈ queries p H, Reach H R q ∨ H.next ≤ q
  | .ret _, _, _, _, _, q, hq => by simp [queries] at hq
  | .view h k, H, R, r, hx, q, hq => by
    simp only [execR] at hx
    split at hx
    · rename_i hR
      simp only [queries, List.mem_cons] at hq
      rcases hq with rfl | hq
      · exact .inl (.base hR)
      · rcases cap_queries (k (H.node h)) H _ r hx q hq with h1 | h1
        · exact .inl (reach_kids hR h1)
        · exact .inr h1
    · simp at hx
  | .alloc n k, H, R, r, hx, q, hq => by
    simp only [execR] at hx
    split at hx
    · rename_i hc
      simp only [queries] at hq
      rcases cap_queries (k H.next) (H.alloc n) _ r hx q hq with h1 | h1
      · rcases reach_alloc (all_mem hc) h1 with h2 | h2
        · exact .inr (by omega)
        · exact .inl h2
      · exact .inr (by simp [Heap.alloc] at h1; omega)
    · simp at hx
  | .write h n k, H, R, r, hx, q, hq => by
    simp only [execR] at hx
    split at hx
    · rename_i hc
      obtain ⟨hR, hc⟩ := hc
      simp only [queries, List.mem_cons] at hq
      rcases hq with rfl | hq
      · exact .inl (.base hR)
      · rcases cap_queries k (H.write h n) R r hx q hq with h1 | h1
        · exact .inl (reach_write (all_mem hc) h1)
        · exact .inr (by simpa [Heap.write] using h1)
    · simp at hx

/-- A capability run that succeeds computes what the plain run does. -/
theorem execR_exec {β : Type} : ∀ (p : Prog β) (H : Heap) (R : List Nat) (b : β) (H' : Heap)
    (R' : List Nat), execR p H R = some (b, H', R') → exec p H = (b, H')
  | .ret _, _, _, _, _, _, hx => by
    simp only [execR, Option.some.injEq, Prod.mk.injEq] at hx
    obtain ⟨rfl, rfl, -⟩ := hx; rfl
  | .view h k, H, R, b, H', R', hx => by
    simp only [execR] at hx; split at hx
    · simp only [exec]; exact execR_exec _ _ _ _ _ _ hx
    · simp at hx
  | .alloc n k, H, R, b, H', R', hx => by
    simp only [execR] at hx; split at hx
    · simp only [exec]; exact execR_exec _ _ _ _ _ _ hx
    · simp at hx
  | .write h n k, H, R, b, H', R', hx => by
    simp only [execR] at hx; split at hx
    · simp only [exec]; exact execR_exec _ _ _ _ _ _ hx
    · simp at hx

/-- A handle a run never asks about keeps its node (writes are asks; allocation is fresh). -/
theorem untouched {β : Type} : ∀ (p : Prog β) (H : Heap) (m : Nat),
    m ∉ queries p H → m < H.next → (exec p H).2.node m = H.node m
  | .ret _, _, _, _, _ => rfl
  | .view h k, H, m, hq, hm => by
    simp only [queries, List.mem_cons, not_or] at hq
    simp only [exec]; exact untouched _ H m hq.2 hm
  | .alloc n k, H, m, hq, hm => by
    simp only [queries] at hq; simp only [exec]
    have hne : m ≠ H.next := by omega
    rw [untouched _ (H.alloc n) m hq (by simp only [Heap.alloc]; omega)]
    simp [Heap.alloc, hne]
  | .write h n k, H, m, hq, hm => by
    simp only [queries, List.mem_cons, not_or] at hq; simp only [exec]
    rw [untouched _ (H.write h n) m hq.2 (by simpa [Heap.write] using hm)]
    simp [Heap.write, hq.1]

open Classical

/-- The heap a run holding `R` sees in isolation: what it can reach, and the fresh handles; the
frame (the old handles it cannot reach) is empty. -/
noncomputable def Heap.isolate (H : Heap) (R : List Nat) : Heap :=
  { node := fun m => if Reach H R m ∨ H.next ≤ m then H.node m else none, next := H.next }

/-- **The frame property** (paper property 2, Assumption 11 (T2)), for every computation of the
heap design. If a run holding `R` succeeds, then its result is the result of its isolated run,
the part of the heap it could reach (and the fresh handles) ends as the isolated run leaves it,
and the frame is left exactly as it was: the run's effect is its isolated run, plugged back in. -/
theorem frame {β : Type} (p : Prog β) (H : Heap) (R : List Nat) (b : β) (H' : Heap)
    (R' : List Nat) (hx : execR p H R = some (b, H', R')) :
    (exec p (H.isolate R)).1 = b ∧ (exec p (H.isolate R)).2.next = H'.next ∧
    ∀ m, H'.node m =
      if Reach H R m ∨ H.next ≤ m then (exec p (H.isolate R)).2.node m else H.node m := by
  have hq := cap_queries p H R _ hx
  have he := execR_exec p H R b H' R' hx
  have ha := exec_agree (fun m => ¬ (Reach H R m ∨ H.next ≤ m)) p H (H.isolate R) rfl
    (by intro m hm; simp only [not_or, Nat.not_le] at hm; exact hm.2)
    (by intro m hm; simp only [Heap.isolate]; rw [if_pos (Classical.not_not.mp hm)])
    (by intro h hh hn; exact hn (hq h hh))
  rw [he] at ha
  refine ⟨ha.1.symm, ha.2.1.symm, fun m => ?_⟩
  split
  · rename_i hm; exact ha.2.2 m (Classical.not_not.mpr hm)
  · rename_i hm
    have hnq : m ∉ queries p H := fun h => hm (hq m h)
    have hlt : m < H.next := by simp only [not_or, Nat.not_le] at hm; exact hm.2
    have := untouched p H m hnq hlt
    rw [he] at this; exact this

/-- **A call's effect is its isolated run** (`call_effect`), for the slice evaluator: a callee runs
on fresh cells holding its arguments' handles `hs`, so it holds exactly `hs`, and through a
borrow argument (a handle to the caller's cell) it reaches that cell and nothing else of the
caller. An instance of `frame`; no case of `evalH` is looked at. -/
theorem call_effect (S : Sig) (f : Nat) (body : Term) (name : String) (hs : List Nat) (H : Heap)
    (r : Res) (H' : Heap) (R' : List Nat)
    (hx : execR ((allocCells hs).bind fun cs => evalH S f body (cs.reverse.map .cell ++ [.fn name]))
      H hs = some (r, H', R')) :
    let call := (allocCells hs).bind fun cs => evalH S f body (cs.reverse.map .cell ++ [.fn name])
    (exec call (H.isolate hs)).1 = r ∧
    ∀ m, H'.node m = if Reach H hs m ∨ H.next ≤ m then (exec call (H.isolate hs)).2.node m
      else H.node m :=
  let h := frame _ H hs r H' R' hx
  ⟨h.1, h.2.2⟩

end Ochr.Heap
