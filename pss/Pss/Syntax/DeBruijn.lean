import Mathlib.Tactic

/-! # `Pss.Syntax.DeBruijn` — raw de Bruijn syntax core for MPSS

This module starts the post-iter-32 de Bruijn refactor. It deliberately
lives beside the locally-nameless development until the downstream MPSS
judgments are ported in one branch.

The syntax has no free-variable constructor. Binding is represented by
plain indices: `bvar 0` is the variable bound by the nearest surrounding
abstraction body, `bvar 1` by the next surrounding abstraction, and so on.
-/

namespace Pss
namespace DeBruijn

/-- Raw MPSS terms with all variables represented by de Bruijn indices. -/
inductive Term where
  | bvar : Nat → Term
  | top  : Term
  | abs  : (bound : Term) → (body : Term) → Term
  | app  : Term → Term → Term
  deriving DecidableEq, Repr

namespace Term

/-! ## Size -/

/-- Syntactic size, used as a basic structural measure for later proofs. -/
def size : Term → Nat
  | .bvar _  => 1
  | .top     => 1
  | .abs t b => 1 + size t + size b
  | .app t u => 1 + size t + size u

@[simp] theorem size_bvar (i : Nat) : size (.bvar i) = 1 := rfl
@[simp] theorem size_top : size .top = 1 := rfl
@[simp] theorem size_abs (t b : Term) :
    size (.abs t b) = 1 + size t + size b := rfl
@[simp] theorem size_app (t u : Term) :
    size (.app t u) = 1 + size t + size u := rfl

/-! ## Shifting -/

/-- `shiftBy cutoff amount t` raises every index `i ≥ cutoff` in `t` by
`amount`. Descending into an abstraction body increments the cutoff because
`bvar 0` is captured by that abstraction. The bound annotation is not under
the new binder, matching the locally-nameless `abs` convention in this repo. -/
def shiftBy (cutoff amount : Nat) : Term → Term
  | .bvar i  => if cutoff ≤ i then .bvar (i + amount) else .bvar i
  | .top     => .top
  | .abs t b => .abs (shiftBy cutoff amount t) (shiftBy (cutoff + 1) amount b)
  | .app t u => .app (shiftBy cutoff amount t) (shiftBy cutoff amount u)

/-- One-step shift: raise every index `i ≥ cutoff` by one. -/
def shift (cutoff : Nat) : Term → Term := shiftBy cutoff 1

@[simp] theorem shiftBy_bvar (cutoff amount i : Nat) :
    shiftBy cutoff amount (.bvar i) =
      if cutoff ≤ i then .bvar (i + amount) else .bvar i := rfl
@[simp] theorem shiftBy_top (cutoff amount : Nat) :
    shiftBy cutoff amount .top = .top := rfl
@[simp] theorem shiftBy_abs (cutoff amount : Nat) (t b : Term) :
    shiftBy cutoff amount (.abs t b) =
      .abs (shiftBy cutoff amount t) (shiftBy (cutoff + 1) amount b) := rfl
@[simp] theorem shiftBy_app (cutoff amount : Nat) (t u : Term) :
    shiftBy cutoff amount (.app t u) =
      .app (shiftBy cutoff amount t) (shiftBy cutoff amount u) := rfl

@[simp] theorem shift_bvar (cutoff i : Nat) :
    shift cutoff (.bvar i) =
      if cutoff ≤ i then .bvar (i + 1) else .bvar i := rfl
@[simp] theorem shift_top (cutoff : Nat) : shift cutoff .top = .top := rfl
@[simp] theorem shift_abs (cutoff : Nat) (t b : Term) :
    shift cutoff (.abs t b) = .abs (shift cutoff t) (shift (cutoff + 1) b) := rfl
@[simp] theorem shift_app (cutoff : Nat) (t u : Term) :
    shift cutoff (.app t u) = .app (shift cutoff t) (shift cutoff u) := rfl

/-- Shifting by zero is the identity. -/
theorem shiftBy_zero_id (cutoff : Nat) (t : Term) :
    shiftBy cutoff 0 t = t := by
  induction t generalizing cutoff with
  | bvar i =>
    by_cases h : cutoff ≤ i
    · simp [shiftBy, h]
    · simp [shiftBy, h]
  | top => simp [shiftBy]
  | abs bound body ih_bound ih_body =>
    simp [shiftBy, ih_bound, ih_body]
  | app fn arg ih_fn ih_arg =>
    simp [shiftBy, ih_fn, ih_arg]

/-! ## Instantiation -/

/-- `instantiate k v t` substitutes `v` for `bvar k` in `t`. Indices above
`k` are decremented, as in standard de Bruijn substitution. Under an
abstraction body the target index increases, and the substituted term is
shifted to remain valid under the new binder. -/
def instantiate (k : Nat) (v : Term) : Term → Term
  | .bvar i =>
      if i < k then
        .bvar i
      else if i = k then
        v
      else
        .bvar (i - 1)
  | .top     => .top
  | .abs t b => .abs (instantiate k v t) (instantiate (k + 1) (shift 0 v) b)
  | .app t u => .app (instantiate k v t) (instantiate k v u)

@[simp] theorem instantiate_bvar (k : Nat) (v : Term) (i : Nat) :
    instantiate k v (.bvar i) =
      if i < k then .bvar i else if i = k then v else .bvar (i - 1) := rfl
@[simp] theorem instantiate_top (k : Nat) (v : Term) :
    instantiate k v .top = .top := rfl
@[simp] theorem instantiate_abs (k : Nat) (v t b : Term) :
    instantiate k v (.abs t b) =
      .abs (instantiate k v t) (instantiate (k + 1) (shift 0 v) b) := rfl
@[simp] theorem instantiate_app (k : Nat) (v t u : Term) :
    instantiate k v (.app t u) = .app (instantiate k v t) (instantiate k v u) := rfl

/-- Instantiation distributes over application. Kept as a named lemma because
later ports use the application case constantly. -/
theorem instantiate_distributes_over_app (k : Nat) (v t u : Term) :
    instantiate k v (.app t u) = .app (instantiate k v t) (instantiate k v u) := rfl

/-- Shifting distributes over application. -/
theorem shift_distributes_over_app (cutoff : Nat) (t u : Term) :
    shift cutoff (.app t u) = .app (shift cutoff t) (shift cutoff u) := rfl

/-- Instantiating immediately after raising the same cutoff restores the
original term. Internal `shiftBy` form used by the public one-step lemma. -/
theorem instantiate_shiftBy_one_id (cutoff : Nat) (v t : Term) :
    instantiate cutoff v (shiftBy cutoff 1 t) = t := by
  induction t generalizing cutoff v with
  | bvar i =>
    by_cases hlt : i < cutoff
    · have hnot : ¬ cutoff ≤ i := Nat.not_le_of_gt hlt
      simp [shift, shiftBy, instantiate, hnot, hlt]
    · have hle : cutoff ≤ i := Nat.le_of_not_gt hlt
      have hs : i + 1 ≠ cutoff := by omega
      have hnlt : ¬ i + 1 < cutoff := by omega
      have hpred : i + 1 - 1 = i := Nat.succ_sub_one i
      simp [shift, shiftBy, instantiate, hle, hnlt, hs, hpred]
  | top =>
    simp [shift, shiftBy, instantiate]
  | abs bound body ih_bound ih_body =>
    simp [shiftBy, instantiate, ih_bound, ih_body]
  | app fn arg ih_fn ih_arg =>
    simp [shiftBy, instantiate, ih_fn, ih_arg]

/-- Instantiating immediately after one-step shifting at the same cutoff
restores the original term. -/
theorem instantiate_shift_id (cutoff : Nat) (v t : Term) :
    instantiate cutoff v (shift cutoff t) = t := by
  exact instantiate_shiftBy_one_id cutoff v t

end Term
end DeBruijn
end Pss
