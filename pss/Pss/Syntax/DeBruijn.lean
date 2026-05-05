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

/-- Two shifts at the same cutoff compose by adding their amounts. -/
theorem shiftBy_compose (cutoff amount₁ amount₂ : Nat) (t : Term) :
    shiftBy cutoff amount₂ (shiftBy cutoff amount₁ t) =
      shiftBy cutoff (amount₁ + amount₂) t := by
  induction t generalizing cutoff with
  | bvar i =>
    by_cases h : cutoff ≤ i
    · have h' : cutoff ≤ i + amount₁ := by omega
      simp [shiftBy, h, h', Nat.add_assoc]
    · simp [shiftBy, h]
  | top => simp [shiftBy]
  | abs bound body ih_bound ih_body =>
    simp [shiftBy, ih_bound, ih_body]
  | app fn arg ih_fn ih_arg =>
    simp [shiftBy, ih_fn, ih_arg]

/-- A one-step lift at `base` commutes with a later shift at `cutoff`, provided
`base ≤ cutoff`. This is the shift arithmetic used when descending through
abstraction bodies. -/
theorem shiftBy_lift_comm (base cutoff amount : Nat) (t : Term)
    (hbase : base ≤ cutoff) :
    shiftBy (cutoff + 1) amount (shiftBy base 1 t) =
      shiftBy base 1 (shiftBy cutoff amount t) := by
  induction t generalizing base cutoff with
  | bvar i =>
    by_cases hb : base ≤ i
    · by_cases hc : cutoff ≤ i
      · have hc' : cutoff + 1 ≤ i + 1 := by omega
        have hb' : base ≤ i + amount := by omega
        have hb'' : base ≤ amount + i := by omega
        simp [shiftBy, hb, hc, hc', hb', hb'', Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
      · have hc' : ¬ cutoff + 1 ≤ i + 1 := by omega
        simp [shiftBy, hb, hc, hc']
    · have hc : ¬ cutoff ≤ i := by omega
      have hc' : ¬ cutoff + 1 ≤ i := by omega
      simp [shiftBy, hb, hc, hc']
  | top =>
    simp [shift, shiftBy]
  | abs bound body ih_bound ih_body =>
    simp [shiftBy, ih_bound base cutoff hbase, ih_body (base + 1) (cutoff + 1) (by omega)]
  | app fn arg ih_fn ih_arg =>
    simp [shiftBy, ih_fn base cutoff hbase, ih_arg base cutoff hbase]

/-- Shifting below one newly introduced binder commutes with the raw top-level
one-step lift. -/
theorem shiftBy_shiftBy_zero_one (cutoff amount : Nat) (t : Term) :
    shiftBy (cutoff + 1) amount (shiftBy 0 1 t) =
      shiftBy 0 1 (shiftBy cutoff amount t) :=
  shiftBy_lift_comm 0 cutoff amount t (Nat.zero_le cutoff)

/-- Shifting below one newly introduced binder commutes with `shift 0`. -/
theorem shiftBy_shift_zero (cutoff amount : Nat) (t : Term) :
    shiftBy (cutoff + 1) amount (shift 0 t) =
      shift 0 (shiftBy cutoff amount t) :=
  shiftBy_shiftBy_zero_one cutoff amount t

/-- One-step version of `shiftBy_shift_zero`. -/
theorem shift_shift_zero (cutoff : Nat) (t : Term) :
    shift (cutoff + 1) (shift 0 t) =
      shift 0 (shift cutoff t) :=
  shiftBy_shift_zero cutoff 1 t

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
original term after cancelling one unit of shift. -/
theorem instantiate_shiftBy_succ (cutoff amount : Nat) (v t : Term) :
    instantiate cutoff v (shiftBy cutoff (amount + 1) t) =
      shiftBy cutoff amount t := by
  induction t generalizing cutoff v with
  | bvar i =>
    by_cases hlt : i < cutoff
    · have hnot : ¬ cutoff ≤ i := Nat.not_le_of_gt hlt
      simp [shift, shiftBy, instantiate, hnot, hlt]
    · have hle : cutoff ≤ i := Nat.le_of_not_gt hlt
      have hnlt : ¬ i + (amount + 1) < cutoff := by omega
      have hne : i + (amount + 1) ≠ cutoff := by omega
      have hpred : i + (amount + 1) - 1 = i + amount := by omega
      simp [shift, shiftBy, instantiate, hle, hnlt, hne, hpred]
  | top =>
    simp [shift, shiftBy, instantiate]
  | abs bound body ih_bound ih_body =>
    simp [shiftBy, instantiate, ih_bound, ih_body]
  | app fn arg ih_fn ih_arg =>
    simp [shiftBy, instantiate, ih_fn, ih_arg]

/-- Instantiating immediately after raising the same cutoff restores the
original term. Internal `shiftBy` form used by the public one-step lemma. -/
theorem instantiate_shiftBy_one_id (cutoff : Nat) (v t : Term) :
    instantiate cutoff v (shiftBy cutoff 1 t) = t := by
  rw [instantiate_shiftBy_succ cutoff 0 v t, shiftBy_zero_id]

/-- Instantiating immediately after one-step shifting at the same cutoff
restores the original term. -/
theorem instantiate_shift_id (cutoff : Nat) (v t : Term) :
    instantiate cutoff v (shift cutoff t) = t := by
  exact instantiate_shiftBy_one_id cutoff v t

/-- Shifting commutes with instantiation when the shift cutoff is at or below
the instantiated index. The instantiated slot moves upward by the shift
amount, and the replacement term is shifted with the same cutoff. -/
theorem shiftBy_instantiate (cutoff amount k : Nat) (v t : Term)
    (hcut : cutoff ≤ k) :
    shiftBy cutoff amount (instantiate k v t) =
      instantiate (k + amount) (shiftBy cutoff amount v) (shiftBy cutoff amount t) := by
  induction t generalizing cutoff k v with
  | bvar i =>
    by_cases hlt : i < k
    · by_cases hci : cutoff ≤ i
      · have hlt' : i + amount < k + amount := by omega
        simp [instantiate, shiftBy, hlt, hci, hlt']
      · have hlt' : i < k + amount := by omega
        simp [instantiate, shiftBy, hlt, hci, hlt']
    · by_cases heq : i = k
      · have hci : cutoff ≤ i := by omega
        have hnlt : ¬ i + amount < k + amount := by omega
        have heq' : i + amount = k + amount := by omega
        simp [instantiate, shiftBy, hlt, heq, hci, hcut, hnlt, heq']
      · have hgt : k < i := by omega
        have hci : cutoff ≤ i := by omega
        have hpred_cut : cutoff ≤ i - 1 := by omega
        have hnlt : ¬ i + amount < k + amount := by omega
        have hne : i + amount ≠ k + amount := by omega
        have hpred : i + amount - 1 = i - 1 + amount := by omega
        simp [instantiate, shiftBy, hlt, heq, hci, hpred_cut, hnlt, hne, hpred]
  | top =>
    simp [instantiate, shiftBy]
  | abs bound body ih_bound ih_body =>
    simp only [instantiate_abs, shiftBy_abs]
    exact congrArg₂ Term.abs
      (ih_bound cutoff k v hcut)
      (by
        have hbody := ih_body (cutoff + 1) (k + 1) (shift 0 v) (by omega)
        have hidx : k + 1 + amount = k + amount + 1 := by omega
        simpa [hidx, shiftBy_shift_zero cutoff amount v] using hbody)
  | app fn arg ih_fn ih_arg =>
    simp only [instantiate_app, shiftBy_app]
    exact congrArg₂ Term.app (ih_fn cutoff k v hcut) (ih_arg cutoff k v hcut)

/-- Shifting above an instantiated slot commutes with instantiation. Since
instantiation removes slot `k`, a later shift at `cutoff` corresponds to
shifting the original term at `cutoff + 1`. -/
theorem shiftBy_instantiate_lt (cutoff amount k : Nat) (v t : Term)
    (hk : k < cutoff) :
    shiftBy cutoff amount (instantiate k v t) =
      instantiate k (shiftBy cutoff amount v) (shiftBy (cutoff + 1) amount t) := by
  induction t generalizing cutoff k v with
  | bvar i =>
    by_cases hlt : i < k
    · have hshift : ¬ cutoff ≤ i := by omega
      have hshift_rhs : ¬ cutoff + 1 ≤ i := by omega
      simp [instantiate, shiftBy, hlt, hshift, hshift_rhs]
    · by_cases heq : i = k
      · have hshift_rhs : ¬ cutoff + 1 ≤ i := by omega
        subst heq
        simp [instantiate, shiftBy, hshift_rhs]
      · have hgt : k < i := by omega
        by_cases hci : cutoff ≤ i - 1
        · have hshift_rhs : cutoff + 1 ≤ i := by omega
          have hnlt : ¬ i + amount < k := by omega
          have hne : i + amount ≠ k := by omega
          have hpred : i + amount - 1 = i - 1 + amount := by omega
          simp [instantiate, shiftBy, hlt, heq, hci, hshift_rhs, hnlt, hne, hpred]
        · have hshift_rhs : ¬ cutoff + 1 ≤ i := by omega
          have hshift_lhs : ¬ cutoff ≤ i - 1 := hci
          simp [instantiate, shiftBy, hlt, heq, hshift_lhs, hshift_rhs]
  | top =>
    simp [instantiate, shiftBy]
  | abs bound body ih_bound ih_body =>
    simp only [instantiate_abs, shiftBy_abs]
    exact congrArg₂ Term.abs
      (ih_bound cutoff k v hk)
      (by
        have hbody := ih_body (cutoff + 1) (k + 1) (shift 0 v) (by omega)
        have hshift :
            shiftBy (cutoff + 1) amount (shift 0 v) =
              shift 0 (shiftBy cutoff amount v) :=
          shiftBy_shift_zero cutoff amount v
        simpa [hshift, Nat.add_assoc] using hbody)
  | app fn arg ih_fn ih_arg =>
    simp only [instantiate_app, shiftBy_app]
    exact congrArg₂ Term.app (ih_fn cutoff k v hk) (ih_arg cutoff k v hk)

/-- One-step version of `shiftBy_instantiate_lt`. -/
theorem shift_instantiate_lt (cutoff k : Nat) (v t : Term)
    (hk : k < cutoff) :
    shift cutoff (instantiate k v t) =
      instantiate k (shift cutoff v) (shift (cutoff + 1) t) :=
  shiftBy_instantiate_lt cutoff 1 k v t hk

/-- Instantiation commutes with inserting a new binding immediately outside
the instantiated slot. -/
theorem instantiate_shift_succ (k : Nat) (v t : Term) :
    instantiate k (shift k v) (shift (k + 1) t) =
      shift k (instantiate k v t) := by
  induction t generalizing k v with
  | bvar i =>
    by_cases hlt : i < k
    · have hshift : ¬ k + 1 ≤ i := by omega
      have hshift_rhs : ¬ k ≤ i := by omega
      simp [instantiate, shift, shiftBy, hlt, hshift, hshift_rhs]
    · by_cases heq : i = k
      · have hshift : ¬ k + 1 ≤ i := by omega
        simp [instantiate, shift, shiftBy, hlt, heq, hshift]
      · have hgt : k < i := by omega
        have hshift : k + 1 ≤ i := by omega
        have hnlt : ¬ i + 1 < k := by omega
        have hne : i + 1 ≠ k := by omega
        have hpred_shift : k ≤ i - 1 := by omega
        have hpred_rhs : i - 1 + 1 = i := by omega
        simp [instantiate, shift, shiftBy, hlt, heq, hshift, hnlt, hne, hpred_shift, hpred_rhs]
  | top =>
    simp [instantiate, shift, shiftBy]
  | abs bound body ih_bound ih_body =>
    simp only [instantiate_abs, shift_abs]
    exact congrArg₂ Term.abs
      (ih_bound k v)
      (by
        have hbody := ih_body (k + 1) (shift 0 v)
        have hshift : shift (k + 1) (shift 0 v) = shift 0 (shift k v) := by
          exact shiftBy_lift_comm 0 k 1 v (Nat.zero_le k)
        simpa [hshift, Nat.add_assoc] using hbody)
  | app fn arg ih_fn ih_arg =>
    simp only [instantiate_app, shift_app]
    exact congrArg₂ Term.app (ih_fn k v) (ih_arg k v)

/-- Instantiation at the innermost binder commutes with inserting a new
outer binding. The body is shifted at cutoff `1`, preserving its binder at
index `0`, while the replacement term is shifted at cutoff `0` because it
lives outside that binder. -/
theorem instantiate_zero_shift_one (v t : Term) :
    instantiate 0 (shift 0 v) (shift 1 t) =
      shift 0 (instantiate 0 v t) := by
  simpa using instantiate_shift_succ 0 v t

/-- β-instantiation commutes with shifting the surrounding context. -/
theorem shift_instantiate_zero (cutoff : Nat) (v t : Term) :
    shift cutoff (instantiate 0 v t) =
      instantiate 0 (shift cutoff v) (shift (cutoff + 1) t) := by
  cases cutoff with
  | zero =>
    exact (instantiate_shift_succ 0 v t).symm
  | succ cutoff =>
    exact shift_instantiate_lt (cutoff + 1) 0 v t (Nat.succ_pos cutoff)

/-- Instantiating one slot below a newly added top-level binder commutes with
shifting the surrounding term. This names the general form behind the
one-head, two-head, and three-head stack arithmetic lemmas. -/
theorem instantiate_succ_shift_zero (k : Nat) (v t : Term) :
    instantiate (k + 1) (shift 0 v) (shift 0 t) =
      shift 0 (instantiate k v t) := by
  simpa [shift] using
    (shiftBy_instantiate 0 1 k v t (Nat.zero_le k)).symm

/-- Instantiation at index `2` through two preserved top-level bindings
commutes with instantiating at index `0` before adding those bindings. -/
theorem instantiate_two_shift_zero (v t : Term) :
    instantiate 2 (shift 0 (shift 0 v)) (shift 0 (shift 0 t)) =
      shift 0 (shift 0 (instantiate 0 v t)) := by
  have h := (shiftBy_instantiate 0 2 0 v t (Nat.zero_le 0)).symm
  simpa [shift, shiftBy_compose, Nat.add_assoc] using h

/-- Instantiation at index `3` through three preserved top-level bindings
commutes with instantiating at index `0` before adding those bindings. -/
theorem instantiate_three_shift_zero (v t : Term) :
    instantiate 3 (shift 0 (shift 0 (shift 0 v)))
        (shift 0 (shift 0 (shift 0 t))) =
      shift 0 (shift 0 (shift 0 (instantiate 0 v t))) := by
  have h := (shiftBy_instantiate 0 3 0 v t (Nat.zero_le 0)).symm
  simpa [shift, shiftBy_compose, Nat.add_assoc] using h

/-- Instantiation at index `4` through four preserved top-level bindings
commutes with instantiating at index `0` before adding those bindings. -/
theorem instantiate_four_shift_zero (v t : Term) :
    instantiate 4
        (shift 0 (shift 0 (shift 0 (shift 0 v))))
        (shift 0 (shift 0 (shift 0 (shift 0 t)))) =
      shift 0 (shift 0 (shift 0 (shift 0 (instantiate 0 v t)))) := by
  have h := (shiftBy_instantiate 0 4 0 v t (Nat.zero_le 0)).symm
  simpa [shift, shiftBy_compose, Nat.add_assoc] using h

/-- Instantiation at index `5` through five preserved top-level bindings
commutes with instantiating at index `0` before adding those bindings. -/
theorem instantiate_five_shift_zero (v t : Term) :
    instantiate 5
        (shift 0 (shift 0 (shift 0 (shift 0 (shift 0 v)))))
        (shift 0 (shift 0 (shift 0 (shift 0 (shift 0 t))))) =
      shift 0 (shift 0 (shift 0 (shift 0 (shift 0 (instantiate 0 v t))))) := by
  have h := (shiftBy_instantiate 0 5 0 v t (Nat.zero_le 0)).symm
  simpa [shift, shiftBy_compose, Nat.add_assoc] using h

/-- Instantiating index `2` through a term shifted under three top-level
bindings cancels the shift at the instantiated slot and preserves the two
outer bindings. -/
theorem instantiate_two_shift_zero_tail (v t : Term) :
    instantiate 2 (shift 0 (shift 0 v)) (shift 0 (shift 0 (shift 0 t))) =
      shift 0 (shift 0 t) := by
  have hshift_general :
      ∀ (cutoff : Nat) (u : Term),
        shift cutoff (shift cutoff (shift cutoff u)) =
          shift (cutoff + 2) (shift cutoff (shift cutoff u)) := by
    intro cutoff u
    induction u generalizing cutoff with
    | bvar i =>
        by_cases h : cutoff ≤ i
        · have h₁ : cutoff ≤ i + 1 := by omega
          have h₂ : cutoff ≤ i + 1 + 1 := by omega
          have h₃ : cutoff + 2 ≤ i + 1 + 1 := by omega
          simp [shift, shiftBy, h, h₁, h₂, h₃, Nat.add_assoc]
        · have h₃ : ¬ cutoff + 2 ≤ i := by omega
          simp [shift, shiftBy, h, h₃]
    | top =>
        simp [shift, shiftBy]
    | abs bound body ih_bound ih_body =>
        simp only [shift, shiftBy]
        exact congrArg₂ Term.abs
          (ih_bound cutoff)
          (by simpa [Nat.add_assoc] using ih_body (cutoff + 1))
    | app fn arg ih_fn ih_arg =>
        simp only [shift, shiftBy]
        exact congrArg₂ Term.app (ih_fn cutoff) (ih_arg cutoff)
  have hshift :
      shift 0 (shift 0 (shift 0 t)) = shift 2 (shift 0 (shift 0 t)) := by
    simpa using hshift_general 0 t
  rw [hshift]
  exact instantiate_shift_id 2 (shift 0 (shift 0 v)) (shift 0 (shift 0 t))

/-- Instantiating index `3` through a term shifted under four top-level
bindings cancels the shift at the instantiated slot and preserves the three
outer bindings. -/
theorem instantiate_three_shift_zero_tail (v t : Term) :
    instantiate 3 (shift 0 (shift 0 (shift 0 v)))
        (shift 0 (shift 0 (shift 0 (shift 0 t)))) =
      shift 0 (shift 0 (shift 0 t)) := by
  have hshift_general :
      ∀ (cutoff : Nat) (u : Term),
        shift cutoff (shift cutoff (shift cutoff (shift cutoff u))) =
          shift (cutoff + 3)
            (shift cutoff (shift cutoff (shift cutoff u))) := by
    intro cutoff u
    induction u generalizing cutoff with
    | bvar i =>
        by_cases h : cutoff ≤ i
        · have h₁ : cutoff ≤ i + 1 := by omega
          have h₂ : cutoff ≤ i + 1 + 1 := by omega
          have h₃ : cutoff ≤ i + 1 + 1 + 1 := by omega
          have h₄ : cutoff + 3 ≤ i + 1 + 1 + 1 := by omega
          simp [shift, shiftBy, h, h₁, h₂, h₃, h₄, Nat.add_assoc]
        · have h₄ : ¬ cutoff + 3 ≤ i := by omega
          simp [shift, shiftBy, h, h₄]
    | top =>
        simp [shift, shiftBy]
    | abs bound body ih_bound ih_body =>
        simp only [shift, shiftBy]
        exact congrArg₂ Term.abs
          (ih_bound cutoff)
          (by simpa [Nat.add_assoc] using ih_body (cutoff + 1))
    | app fn arg ih_fn ih_arg =>
        simp only [shift, shiftBy]
        exact congrArg₂ Term.app (ih_fn cutoff) (ih_arg cutoff)
  have hshift :
      shift 0 (shift 0 (shift 0 (shift 0 t))) =
        shift 3 (shift 0 (shift 0 (shift 0 t))) := by
    simpa using hshift_general 0 t
  rw [hshift]
  exact instantiate_shift_id 3 (shift 0 (shift 0 (shift 0 v)))
    (shift 0 (shift 0 (shift 0 t)))

/-- Shifting a term by `n` at some cutoff and then inserting one slot after
those `n` slots is the same as shifting the original term by `n + 1`. This is
the generalized arithmetic behind the fixed two-head and three-head tail
lemmas. -/
theorem shiftBy_tail (cutoff n : Nat) (t : Term) :
    shiftBy (cutoff + n) 1 (shiftBy cutoff n t) =
      shiftBy cutoff (n + 1) t := by
  induction t generalizing cutoff n with
  | bvar i =>
      by_cases hcut : cutoff ≤ i
      · have htail : cutoff + n ≤ i + n := by omega
        have hsum : i + n + 1 = i + (n + 1) := by omega
        simp [shiftBy, hcut, htail, hsum]
      · have htail : ¬ cutoff + n ≤ i := by omega
        simp [shiftBy, hcut, htail]
  | top =>
      simp [shiftBy]
  | abs bound body ih_bound ih_body =>
      simp only [shiftBy_abs]
      exact congrArg₂ Term.abs
        (ih_bound cutoff n)
        (by
          have hbody := ih_body (cutoff + 1) n
          simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hbody)
  | app fn arg ih_fn ih_arg =>
      simp only [shiftBy_app]
      exact congrArg₂ Term.app (ih_fn cutoff n) (ih_arg cutoff n)

/-- Top-level specialization of `Term.shiftBy_tail`. -/
theorem shiftBy_zero_tail (n : Nat) (t : Term) :
    shiftBy n 1 (shiftBy 0 n t) = shiftBy 0 (n + 1) t := by
  simpa using shiftBy_tail 0 n t

/-- General tail cancellation for instantiation below `n` preserved top-level
bindings. The fixed `instantiate_two_shift_zero_tail` and
`instantiate_three_shift_zero_tail` lemmas are special cases with nested
one-step shifts. -/
theorem instantiate_shiftBy_zero_tail (n : Nat) (v t : Term) :
    instantiate n (shiftBy 0 n v) (shiftBy 0 (n + 1) t) =
      shiftBy 0 n t := by
  rw [← shiftBy_zero_tail n t]
  exact instantiate_shift_id n (shiftBy 0 n v) (shiftBy 0 n t)

/-- Instantiating index `4` through a term shifted under five top-level
bindings cancels the shift at the instantiated slot and preserves the four
outer bindings. -/
theorem instantiate_four_shift_zero_tail (v t : Term) :
    instantiate 4 (shift 0 (shift 0 (shift 0 (shift 0 v))))
        (shift 0 (shift 0 (shift 0 (shift 0 (shift 0 t))))) =
      shift 0 (shift 0 (shift 0 (shift 0 t))) := by
  have h := instantiate_shiftBy_zero_tail 4 v t
  simpa [shift, shiftBy_compose, Nat.add_assoc] using h

/-- Substituting index `k` and then the next surviving slot is equivalent to
first substituting the corresponding original slot at `k + 2`, then
substituting index `k`. -/
theorem instantiate_succ_after (k : Nat) (a v t : Term) :
    instantiate (k + 1) a (instantiate k v t) =
      instantiate k (instantiate (k + 1) a v)
        (instantiate (k + 2) (shift k a) t) := by
  induction t generalizing k a v with
  | bvar i =>
      by_cases hlt : i < k
      · have hlt_succ : i < k + 1 := by omega
        have hlt_two : i < k + 2 := by omega
        simp [instantiate, hlt, hlt_succ, hlt_two]
      · by_cases heq : i = k
        · subst i
          have hnot_succ : ¬ k < k := by omega
          have hnot_two : ¬ k < k := by omega
          have hlt_two : k < k + 2 := by omega
          simp [instantiate, hnot_succ, hnot_two, hlt_two]
        · have hgt : k < i := by omega
          by_cases heq_succ : i = k + 1
          · subst heq_succ
            have hnot : ¬ k + 1 < k := by omega
            have hnot_succ : ¬ k < k := by omega
            have hlt_two : k + 1 < k + 2 := by omega
            have hpred : k + 1 - 1 = k := by omega
            simp [instantiate, hlt, hnot, hnot_succ, hlt_two, hpred]
          · have hgt_succ : k + 1 < i := by omega
            by_cases heq_two : i = k + 2
            · subst heq_two
              have hnlt_lhs₁ : ¬ k + 2 < k := by omega
              have hne_lhs₁ : k + 2 ≠ k := by omega
              have hpred_lhs₁ : k + 2 - 1 = k + 1 := by omega
              have hnlt_lhs₂ : ¬ k + 1 < k + 1 := by omega
              have hshift_id :
                  instantiate k (instantiate (k + 1) a v) (shift k a) = a := by
                exact instantiate_shift_id k (instantiate (k + 1) a v) a
              simp [instantiate, hnlt_lhs₁, hne_lhs₁, hpred_lhs₁,
                hnlt_lhs₂, hshift_id]
            · have hnlt_lhs₁ : ¬ i < k := by omega
              have hne_lhs₁ : i ≠ k := by omega
              have hpred_lhs₁ : k < i - 1 := by omega
              have hpred_nlt : ¬ i - 1 < k + 1 := by omega
              have hpred_ne : i - 1 ≠ k + 1 := by omega
              have hpred_pred : i - 1 - 1 = i - 2 := by omega
              have hnlt_rhs₁ : ¬ i < k + 2 := by omega
              have hne_rhs₁ : i ≠ k + 2 := by omega
              have hnlt_rhs₂ : ¬ i - 1 < k := by omega
              have hne_rhs₂ : i - 1 ≠ k := by omega
              have hpred_rhs : i - 1 - 1 = i - 2 := by omega
              simp [instantiate, hnlt_lhs₁, hne_lhs₁, hpred_lhs₁,
                hpred_nlt, hpred_ne, hpred_pred, hnlt_rhs₁, hne_rhs₁,
                hnlt_rhs₂, hne_rhs₂, hpred_rhs]
  | top =>
      simp [instantiate]
  | abs bound body ih_bound ih_body =>
      simp only [instantiate_abs]
      apply congrArg₂ Term.abs
      · exact ih_bound k a v
      · have hbody := ih_body (k + 1) (shift 0 a) (shift 0 v)
        have hshift :
            shift (k + 1) (shift 0 a) = shift 0 (shift k a) := by
          exact shift_shift_zero k a
        have hvShift :
            instantiate (k + 2) (shift 0 a) (shift 0 v) =
              shift 0 (instantiate (k + 1) a v) := by
          exact (shiftBy_instantiate 0 1 (k + 1) a v (Nat.zero_le _)).symm
        simpa [Nat.add_assoc, hshift, hvShift] using hbody
  | app fn arg ih_fn ih_arg =>
      simp only [instantiate_app]
      exact congrArg₂ Term.app (ih_fn k a v) (ih_arg k a v)

/-- Substituting index `k` after substituting through three preserved slots is
equivalent to first substituting index `k`, then substituting the surviving
slot at `k + 2`. -/
theorem instantiate_after_two (k : Nat) (a v t : Term) :
    instantiate k (instantiate (k + 2) a v)
        (instantiate (k + 3) (shift k a) t) =
      instantiate (k + 2) a (instantiate k v t) := by
  induction t generalizing k a v with
  | bvar i =>
      by_cases hlt : i < k
      · have hlt_three : i < k + 3 := by omega
        have hlt_two : i < k + 2 := by omega
        simp [instantiate, hlt, hlt_three, hlt_two]
      · by_cases heq : i = k
        · subst i
          have hnot_three : ¬ k < k := by omega
          have hlt_three : k < k + 3 := by omega
          simp [instantiate, hnot_three, hlt_three]
        · have hgt : k < i := by omega
          by_cases heq_one : i = k + 1
          · subst i
            have hlt_three : k + 1 < k + 3 := by omega
            have hnot : ¬ k + 1 < k := by omega
            have hpred : k + 1 - 1 = k := by omega
            simp [instantiate, hlt, hnot, hlt_three, hpred]
          · by_cases heq_two : i = k + 2
            · subst i
              have hlt_three : k + 2 < k + 3 := by omega
              have hnot : ¬ k + 2 < k := by omega
              have hpred : k + 2 - 1 = k + 1 := by omega
              have hlt_two : k + 1 < k + 2 := by omega
              simp [instantiate, hlt, hnot, hlt_three, hpred, hlt_two]
            · by_cases heq_three : i = k + 3
              · subst i
                have hnlt_lhs₁ : ¬ k + 3 < k + 3 := by omega
                have hnlt_lhs₂ : ¬ k < k := by omega
                have hnot_rhs₁ : ¬ k + 3 < k := by omega
                have hne_rhs₁ : k + 3 ≠ k := by omega
                have hpred_rhs₁ : k + 3 - 1 = k + 2 := by omega
                have hnlt_rhs₂ : ¬ k + 2 < k + 2 := by omega
                have hshift_id :
                    instantiate k (instantiate (k + 2) a v) (shift k a) = a := by
                  exact instantiate_shift_id k (instantiate (k + 2) a v) a
                simp [instantiate, hnlt_lhs₁, hnlt_lhs₂,
                  hnot_rhs₁, hne_rhs₁, hpred_rhs₁, hnlt_rhs₂, hshift_id]
              · have hgt_three : k + 3 < i := by omega
                have hnlt_lhs₁ : ¬ i < k + 3 := by omega
                have hne_lhs₁ : i ≠ k + 3 := by omega
                have hnlt_lhs₂ : ¬ i - 1 < k := by omega
                have hne_lhs₂ : i - 1 ≠ k := by omega
                have hpred_lhs : i - 1 - 1 = i - 2 := by omega
                have hnlt_rhs₁ : ¬ i < k := by omega
                have hne_rhs₁ : i ≠ k := by omega
                have hpred_rhs₁ : i - 1 = i - 1 := rfl
                have hnlt_rhs₂ : ¬ i - 1 < k + 2 := by omega
                have hne_rhs₂ : i - 1 ≠ k + 2 := by omega
                have hpred_rhs₂ : i - 1 - 1 = i - 2 := by omega
                simp [instantiate, hnlt_lhs₁, hne_lhs₁, hnlt_lhs₂,
                  hne_lhs₂, hpred_lhs, hnlt_rhs₁, hne_rhs₁, hpred_rhs₁,
                  hnlt_rhs₂, hne_rhs₂, hpred_rhs₂]
  | top =>
      rfl
  | abs bound body ih_bound ih_body =>
      simp only [instantiate_abs]
      apply congrArg₂ Term.abs
      · exact ih_bound k a v
      · have hbody := ih_body (k + 1) (shift 0 a) (shift 0 v)
        have hshift :
            shift (k + 1) (shift 0 a) = shift 0 (shift k a) := by
          exact shift_shift_zero k a
        have hvShift :
            instantiate (k + 3) (shift 0 a) (shift 0 v) =
              shift 0 (instantiate (k + 2) a v) := by
          exact (shiftBy_instantiate 0 1 (k + 2) a v (Nat.zero_le _)).symm
        simpa [Nat.add_assoc, hshift, hvShift] using hbody
  | app fn arg ih_fn ih_arg =>
      simp only [instantiate_app]
      exact congrArg₂ Term.app (ih_fn k a v) (ih_arg k a v)

/-- Zero-cutoff specialization of `Term.instantiate_after_two`. -/
theorem instantiate_zero_after_two (a v t : Term) :
    instantiate 0 (instantiate 2 a v) (instantiate 3 (shift 0 a) t) =
      instantiate 2 a (instantiate 0 v t) :=
  instantiate_after_two 0 a v t

/-- Substituting index `k` after substituting through four preserved slots is
equivalent to first substituting index `k`, then substituting the surviving
slot at `k + 3`. This is the three-preserved-head β-target composition law.
-/
theorem instantiate_after_three (k : Nat) (a v t : Term) :
    instantiate k (instantiate (k + 3) a v)
        (instantiate (k + 4) (shift k a) t) =
      instantiate (k + 3) a (instantiate k v t) := by
  induction t generalizing k a v with
  | bvar i =>
      by_cases hlt : i < k
      · have hlt_four : i < k + 4 := by omega
        have hlt_three : i < k + 3 := by omega
        simp [instantiate, hlt, hlt_four, hlt_three]
      · by_cases heq : i = k
        · subst i
          have hnot_four : ¬ k < k := by omega
          have hlt_four : k < k + 4 := by omega
          simp [instantiate, hnot_four, hlt_four]
        · have hgt : k < i := by omega
          by_cases heq_one : i = k + 1
          · subst i
            have hlt_four : k + 1 < k + 4 := by omega
            have hnot : ¬ k + 1 < k := by omega
            have hpred : k + 1 - 1 = k := by omega
            simp [instantiate, hlt, hnot, hlt_four, hpred]
          · by_cases heq_two : i = k + 2
            · subst i
              have hlt_four : k + 2 < k + 4 := by omega
              have hnot : ¬ k + 2 < k := by omega
              have hpred : k + 2 - 1 = k + 1 := by omega
              have hlt_three : k + 1 < k + 3 := by omega
              simp [instantiate, hlt, hnot, hlt_four, hpred, hlt_three]
            · by_cases heq_three : i = k + 3
              · subst i
                have hlt_four : k + 3 < k + 4 := by omega
                have hnot : ¬ k + 3 < k := by omega
                have hpred : k + 3 - 1 = k + 2 := by omega
                have hlt_three : k + 2 < k + 3 := by omega
                simp [instantiate, hlt, hnot, hlt_four, hpred, hlt_three]
              · by_cases heq_four : i = k + 4
                · subst i
                  have hnlt_lhs₁ : ¬ k + 4 < k + 4 := by omega
                  have hnlt_lhs₂ : ¬ k < k := by omega
                  have hnot_rhs₁ : ¬ k + 4 < k := by omega
                  have hne_rhs₁ : k + 4 ≠ k := by omega
                  have hpred_rhs₁ : k + 4 - 1 = k + 3 := by omega
                  have hnlt_rhs₂ : ¬ k + 3 < k + 3 := by omega
                  have hshift_id :
                      instantiate k (instantiate (k + 3) a v) (shift k a) = a := by
                    exact instantiate_shift_id k (instantiate (k + 3) a v) a
                  simp [instantiate, hnlt_lhs₁, hnlt_lhs₂, hnot_rhs₁,
                    hne_rhs₁, hpred_rhs₁, hnlt_rhs₂, hshift_id]
                · have hgt_four : k + 4 < i := by omega
                  have hnlt_lhs₁ : ¬ i < k + 4 := by omega
                  have hne_lhs₁ : i ≠ k + 4 := by omega
                  have hnlt_lhs₂ : ¬ i - 1 < k := by omega
                  have hne_lhs₂ : i - 1 ≠ k := by omega
                  have hpred_lhs : i - 1 - 1 = i - 2 := by omega
                  have hnlt_rhs₁ : ¬ i < k := by omega
                  have hne_rhs₁ : i ≠ k := by omega
                  have hnlt_rhs₂ : ¬ i - 1 < k + 3 := by omega
                  have hne_rhs₂ : i - 1 ≠ k + 3 := by omega
                  have hpred_rhs₂ : i - 1 - 1 = i - 2 := by omega
                  simp [instantiate, hnlt_lhs₁, hne_lhs₁, hnlt_lhs₂,
                    hne_lhs₂, hpred_lhs, hnlt_rhs₁, hne_rhs₁,
                    hnlt_rhs₂, hne_rhs₂, hpred_rhs₂]
  | top =>
      rfl
  | abs bound body ih_bound ih_body =>
      simp only [instantiate_abs]
      apply congrArg₂ Term.abs
      · exact ih_bound k a v
      · have hbody := ih_body (k + 1) (shift 0 a) (shift 0 v)
        have hshift :
            shift (k + 1) (shift 0 a) = shift 0 (shift k a) := by
          exact shift_shift_zero k a
        have hvShift :
            instantiate (k + 4) (shift 0 a) (shift 0 v) =
              shift 0 (instantiate (k + 3) a v) := by
          exact (shiftBy_instantiate 0 1 (k + 3) a v (Nat.zero_le _)).symm
        simpa [Nat.add_assoc, hshift, hvShift] using hbody
  | app fn arg ih_fn ih_arg =>
      simp only [instantiate_app]
      exact congrArg₂ Term.app (ih_fn k a v) (ih_arg k a v)

/-- Zero-cutoff specialization of `Term.instantiate_after_three`. -/
theorem instantiate_zero_after_three (a v t : Term) :
    instantiate 0 (instantiate 3 a v) (instantiate 4 (shift 0 a) t) =
      instantiate 3 a (instantiate 0 v t) :=
  instantiate_after_three 0 a v t

/-- Substituting index `k` after substituting through five preserved slots is
equivalent to first substituting index `k`, then substituting the surviving
slot at `k + 4`. This is the four-preserved-head β-target composition law. -/
theorem instantiate_after_four (k : Nat) (a v t : Term) :
    instantiate k (instantiate (k + 4) a v)
        (instantiate (k + 5) (shift k a) t) =
      instantiate (k + 4) a (instantiate k v t) := by
  induction t generalizing k a v with
  | bvar i =>
      by_cases hlt : i < k
      · have hlt_five : i < k + 5 := by omega
        have hlt_four : i < k + 4 := by omega
        simp [instantiate, hlt, hlt_five, hlt_four]
      · by_cases heq : i = k
        · subst i
          have hnot_five : ¬ k < k := by omega
          have hlt_five : k < k + 5 := by omega
          simp [instantiate, hnot_five, hlt_five]
        · have hgt : k < i := by omega
          by_cases heq_one : i = k + 1
          · subst i
            have hlt_five : k + 1 < k + 5 := by omega
            have hnot : ¬ k + 1 < k := by omega
            have hpred : k + 1 - 1 = k := by omega
            simp [instantiate, hlt, hnot, hlt_five, hpred]
          · by_cases heq_two : i = k + 2
            · subst i
              have hlt_five : k + 2 < k + 5 := by omega
              have hnot : ¬ k + 2 < k := by omega
              have hpred : k + 2 - 1 = k + 1 := by omega
              have hlt_four : k + 1 < k + 4 := by omega
              simp [instantiate, hlt, hnot, hlt_five, hpred, hlt_four]
            · by_cases heq_three : i = k + 3
              · subst i
                have hlt_five : k + 3 < k + 5 := by omega
                have hnot : ¬ k + 3 < k := by omega
                have hpred : k + 3 - 1 = k + 2 := by omega
                have hlt_four : k + 2 < k + 4 := by omega
                simp [instantiate, hlt, hnot, hlt_five, hpred, hlt_four]
              · by_cases heq_four : i = k + 4
                · subst i
                  have hlt_five : k + 4 < k + 5 := by omega
                  have hnot : ¬ k + 4 < k := by omega
                  have hpred : k + 4 - 1 = k + 3 := by omega
                  have hlt_four : k + 3 < k + 4 := by omega
                  simp [instantiate, hlt, hnot, hlt_five, hpred, hlt_four]
                · by_cases heq_five : i = k + 5
                  · subst i
                    have hnlt_lhs₁ : ¬ k + 5 < k + 5 := by omega
                    have hnlt_lhs₂ : ¬ k < k := by omega
                    have hnot_rhs₁ : ¬ k + 5 < k := by omega
                    have hne_rhs₁ : k + 5 ≠ k := by omega
                    have hpred_rhs₁ : k + 5 - 1 = k + 4 := by omega
                    have hnlt_rhs₂ : ¬ k + 4 < k + 4 := by omega
                    have hshift_id :
                        instantiate k (instantiate (k + 4) a v) (shift k a) = a := by
                      exact instantiate_shift_id k (instantiate (k + 4) a v) a
                    simp [instantiate, hnlt_lhs₁, hnlt_lhs₂, hnot_rhs₁,
                      hne_rhs₁, hpred_rhs₁, hnlt_rhs₂, hshift_id]
                  · have hgt_five : k + 5 < i := by omega
                    have hnlt_lhs₁ : ¬ i < k + 5 := by omega
                    have hne_lhs₁ : i ≠ k + 5 := by omega
                    have hnlt_lhs₂ : ¬ i - 1 < k := by omega
                    have hne_lhs₂ : i - 1 ≠ k := by omega
                    have hpred_lhs : i - 1 - 1 = i - 2 := by omega
                    have hnlt_rhs₁ : ¬ i < k := by omega
                    have hne_rhs₁ : i ≠ k := by omega
                    have hnlt_rhs₂ : ¬ i - 1 < k + 4 := by omega
                    have hne_rhs₂ : i - 1 ≠ k + 4 := by omega
                    have hpred_rhs₂ : i - 1 - 1 = i - 2 := by omega
                    simp [instantiate, hnlt_lhs₁, hne_lhs₁, hnlt_lhs₂,
                      hne_lhs₂, hpred_lhs, hnlt_rhs₁, hne_rhs₁,
                      hnlt_rhs₂, hne_rhs₂, hpred_rhs₂]
  | top =>
      rfl
  | abs bound body ih_bound ih_body =>
      simp only [instantiate_abs]
      apply congrArg₂ Term.abs
      · exact ih_bound k a v
      · have hbody := ih_body (k + 1) (shift 0 a) (shift 0 v)
        have hshift :
            shift (k + 1) (shift 0 a) = shift 0 (shift k a) := by
          exact shift_shift_zero k a
        have hvShift :
            instantiate (k + 5) (shift 0 a) (shift 0 v) =
              shift 0 (instantiate (k + 4) a v) := by
          exact (shiftBy_instantiate 0 1 (k + 4) a v (Nat.zero_le _)).symm
        simpa [Nat.add_assoc, hshift, hvShift] using hbody
  | app fn arg ih_fn ih_arg =>
      simp only [instantiate_app]
      exact congrArg₂ Term.app (ih_fn k a v) (ih_arg k a v)

/-- Zero-cutoff specialization of `Term.instantiate_after_four`. -/
theorem instantiate_zero_after_four (a v t : Term) :
    instantiate 0 (instantiate 4 a v) (instantiate 5 (shift 0 a) t) =
      instantiate 4 a (instantiate 0 v t) :=
  instantiate_after_four 0 a v t

/-! ## Scoping -/

/-- `Scoped depth t` means every index in `t` is bound within `depth`
surrounding binders. Closed terms are `Scoped 0`.

This is `Type`-valued, matching the post-Type-LC locally-nameless
development. The MPSS reductions are also `Type`-valued, so later
reflexivity constructions must be able to recurse on scoping evidence. -/
inductive Scoped : Nat → Term → Type
  | bvar {depth i : Nat} : i < depth → Scoped depth (.bvar i)
  | top {depth : Nat} : Scoped depth .top
  | abs {depth : Nat} {bound body : Term} :
      Scoped depth bound → Scoped (depth + 1) body → Scoped depth (.abs bound body)
  | app {depth : Nat} {t u : Term} :
      Scoped depth t → Scoped depth u → Scoped depth (.app t u)

/-- Closed de Bruijn terms have no free indices. -/
abbrev Closed (t : Term) : Type := Scoped 0 t

/-- Inversion for scoped variables. -/
def Scoped.bvar_lt {depth i : Nat} :
    Scoped depth (.bvar i) → i < depth := by
  intro h
  cases h with
  | bvar hi => exact hi

/-- Inversion for scoped abstractions. -/
def Scoped.abs_inv {depth : Nat} {bound body : Term} :
    Scoped depth (.abs bound body) →
      Scoped depth bound × Scoped (depth + 1) body := by
  intro h
  cases h with
  | abs h_bound h_body => exact ⟨h_bound, h_body⟩

/-- Inversion for scoped applications. -/
def Scoped.app_inv {depth : Nat} {t u : Term} :
    Scoped depth (.app t u) → Scoped depth t × Scoped depth u := by
  intro h
  cases h with
  | app h_t h_u => exact ⟨h_t, h_u⟩

def no_scoped_zero_bvar (i : Nat) :
    Scoped 0 (.bvar i) → False := by
  intro h
  exact Nat.not_lt_zero _ h.bvar_lt

/-- Constructor alias for closed `top`. -/
def closed_top : Closed .top := Scoped.top

/-- Constructor alias for closed abstractions. -/
def closed_abs {bound body : Term} :
    Closed bound → Scoped 1 body → Closed (.abs bound body) :=
  Scoped.abs

/-- Constructor alias for closed applications. -/
def closed_app {t u : Term} :
    Closed t → Closed u → Closed (.app t u) :=
  Scoped.app

/-- Inversion for closed abstractions. -/
def Closed.abs_inv {bound body : Term} :
    Closed (.abs bound body) → Closed bound × Scoped 1 body :=
  Scoped.abs_inv

/-- Inversion for closed applications. -/
def Closed.app_inv {t u : Term} :
    Closed (.app t u) → Closed t × Closed u :=
  Scoped.app_inv

/-- Scoping is monotone in the ambient depth. This is the raw de Bruijn
weakening lemma for syntax. -/
noncomputable def scoped_mono {depth depth' : Nat} {t : Term}
    (hdepth : depth ≤ depth') :
    Scoped depth t → Scoped depth' t := by
  intro h
  induction h generalizing depth' with
  | bvar hi =>
    exact Scoped.bvar (by omega)
  | top =>
    exact Scoped.top
  | abs h_bound h_body ih_bound ih_body =>
    exact Scoped.abs (ih_bound hdepth) (ih_body (by omega))
  | app h_t h_u ih_t ih_u =>
    exact Scoped.app (ih_t hdepth) (ih_u hdepth)

/-- Closed terms are scoped at every ambient depth. -/
noncomputable def Closed.scoped (depth : Nat) {t : Term} :
    Closed t → Scoped depth t :=
  scoped_mono (Nat.zero_le depth)

/-- One-step shifting preserves scoping, increasing the ambient depth by one. -/
noncomputable def shift_scoped (cutoff depth : Nat) (t : Term)
    (hcut : cutoff ≤ depth) :
    Scoped depth t → Scoped (depth + 1) (shift cutoff t) := by
  intro h
  induction h generalizing cutoff with
  | bvar hi =>
    simp [shift, shiftBy]
    split
    · exact Scoped.bvar (by omega)
    · exact Scoped.bvar (by omega)
  | top =>
    exact Scoped.top
  | abs h_bound h_body ih_bound ih_body =>
    simp only [shift, shiftBy_abs]
    exact Scoped.abs (ih_bound cutoff hcut) (ih_body (cutoff + 1) (by omega))
  | app h_fn h_arg ih_fn ih_arg =>
    simp only [shift, shiftBy_app]
    exact Scoped.app (ih_fn cutoff hcut) (ih_arg cutoff hcut)

/-- Invert one-step shifting under a scoped ambient context. If shifting at a
valid cutoff is scoped one level higher, the original term was scoped at the
original depth. -/
noncomputable def shift_scoped_inv (cutoff depth : Nat) (t : Term)
    (hcut : cutoff ≤ depth) :
    Scoped (depth + 1) (shift cutoff t) → Scoped depth t := by
  induction t generalizing cutoff depth with
  | bvar i =>
    intro h
    simp [shift, shiftBy] at h
    split at h
    · exact Scoped.bvar (by
        have hi := Scoped.bvar_lt h
        omega)
    · exact Scoped.bvar (by
        have hi := Scoped.bvar_lt h
        omega)
  | top =>
    intro _h
    exact Scoped.top
  | abs bound body ih_bound ih_body =>
    intro h
    simp only [shift, shiftBy_abs] at h
    exact Scoped.abs
      (ih_bound cutoff depth hcut (Scoped.abs_inv h).1)
      (ih_body (cutoff + 1) (depth + 1) (by omega) (Scoped.abs_inv h).2)
  | app fn arg ih_fn ih_arg =>
    intro h
    simp only [shift, shiftBy_app] at h
    exact Scoped.app
      (ih_fn cutoff depth hcut (Scoped.app_inv h).1)
      (ih_arg cutoff depth hcut (Scoped.app_inv h).2)

/-- General shifting preserves scoping, increasing the ambient depth by the
shift amount. -/
noncomputable def shiftBy_scoped (cutoff amount depth : Nat) (t : Term)
    (hcut : cutoff ≤ depth) :
    Scoped depth t → Scoped (depth + amount) (shiftBy cutoff amount t) := by
  intro h
  induction h generalizing cutoff with
  | bvar hi =>
    simp [shiftBy]
    split
    · exact Scoped.bvar (by omega)
    · exact Scoped.bvar (by omega)
  | top =>
    exact Scoped.top
  | abs h_bound h_body ih_bound ih_body =>
    simp only [shiftBy_abs]
    exact Scoped.abs (ih_bound cutoff hcut) (by
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        ih_body (cutoff + 1) (by omega))
  | app h_fn h_arg ih_fn ih_arg =>
    simp only [shiftBy_app]
    exact Scoped.app (ih_fn cutoff hcut) (ih_arg cutoff hcut)

/-- Shifting at or above the current scoping depth has no effect. -/
noncomputable def shiftBy_of_scoped_id (cutoff amount : Nat) (t : Term) :
    Scoped cutoff t → shiftBy cutoff amount t = t := by
  intro h
  induction t generalizing cutoff with
  | bvar i =>
    cases h with
    | bvar hi =>
    have hnot : ¬ cutoff ≤ i := by omega
    simp [shiftBy, hnot]
  | top =>
    simp [shiftBy]
  | abs bound body ih_bound ih_body =>
    cases h with
    | abs h_bound h_body =>
    simp [shiftBy, ih_bound cutoff h_bound, ih_body (cutoff + 1) h_body]
  | app fn arg ih_fn ih_arg =>
    cases h with
    | app h_fn h_arg =>
    simp [shiftBy, ih_fn cutoff h_fn, ih_arg cutoff h_arg]

/-- Closed terms are invariant under top-level shifting. -/
noncomputable def shiftBy_closed_id (amount : Nat) (t : Term) :
    Closed t → shiftBy 0 amount t = t :=
  shiftBy_of_scoped_id 0 amount t

/-- Closed terms are invariant under one-step top-level shifting. -/
noncomputable def shift_closed_id (t : Term) :
    Closed t → shift 0 t = t :=
  shiftBy_closed_id 1 t

/-- Instantiation preserves scoping and removes one available index from the
ambient depth. The premise `k ≤ depth` says the removed slot is among the
`depth + 1` slots available to the input term. -/
noncomputable def instantiate_scoped (k depth : Nat) (v t : Term)
    (hk : k ≤ depth) (hv : Scoped depth v) :
    Scoped (depth + 1) t → Scoped depth (instantiate k v t) := by
  intro h
  induction t generalizing k depth v with
  | bvar i =>
    cases h with
    | bvar hi =>
    simp [instantiate]
    split
    · exact Scoped.bvar (by omega)
    · split
      · exact hv
      · exact Scoped.bvar (by omega)
  | top =>
    exact Scoped.top
  | abs bound body ih_bound ih_body =>
    cases h with
    | abs h_bound h_body =>
    simp only [instantiate_abs]
    exact Scoped.abs
      (ih_bound k depth v hk hv h_bound)
      (ih_body (k + 1) (depth + 1) (shift 0 v) (by omega)
        (shift_scoped 0 depth v (by omega) hv) h_body)
  | app fn arg ih_fn ih_arg =>
    cases h with
    | app h_fn h_arg =>
    simp only [instantiate_app]
    exact Scoped.app (ih_fn k depth v hk hv h_fn) (ih_arg k depth v hk hv h_arg)

/-- Instantiating the outermost available index with a closed term produces a
closed term. This is the β-substitution shape used by MPSS reductions. -/
noncomputable def instantiate_closed (v t : Term) :
    Closed v → Scoped 1 t → Closed (instantiate 0 v t) := by
  intro hv ht
  exact instantiate_scoped 0 0 v t (by omega) hv ht

/-- Instantiating an index at or above the current scoping depth has no
effect. This is the de Bruijn freshness/no-op substitution lemma. -/
noncomputable def instantiate_of_scoped_id (k : Nat) (v t : Term) :
    Scoped k t → instantiate k v t = t := by
  intro h
  induction t generalizing k v with
  | bvar i =>
    cases h with
    | bvar hi =>
    have hlt : i < k := hi
    simp [instantiate, hlt]
  | top =>
    simp [instantiate]
  | abs bound body ih_bound ih_body =>
    cases h with
    | abs h_bound h_body =>
    simp [instantiate, ih_bound k v h_bound, ih_body (k + 1) (shift 0 v) h_body]
  | app fn arg ih_fn ih_arg =>
    cases h with
    | app h_fn h_arg =>
    simp [instantiate, ih_fn k v h_fn, ih_arg k v h_arg]

/-- Instantiating a closed term at top level is a no-op. -/
noncomputable def instantiate_closed_id (v t : Term) :
    Closed t → instantiate 0 v t = t :=
  instantiate_of_scoped_id 0 v t

end Term
end DeBruijn
end Pss
