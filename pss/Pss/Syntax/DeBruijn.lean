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

/-! ## Scoping -/

/-- `Scoped depth t` means every index in `t` is bound within `depth`
surrounding binders. Closed terms are `Scoped 0`. -/
inductive Scoped : Nat → Term → Prop
  | bvar {depth i : Nat} : i < depth → Scoped depth (.bvar i)
  | top {depth : Nat} : Scoped depth .top
  | abs {depth : Nat} {bound body : Term} :
      Scoped depth bound → Scoped (depth + 1) body → Scoped depth (.abs bound body)
  | app {depth : Nat} {t u : Term} :
      Scoped depth t → Scoped depth u → Scoped depth (.app t u)

/-- Closed de Bruijn terms have no free indices. -/
abbrev Closed (t : Term) : Prop := Scoped 0 t

@[simp] theorem scoped_bvar_iff (depth i : Nat) :
    Scoped depth (.bvar i) ↔ i < depth := by
  constructor
  · intro h
    cases h with
    | bvar hi => exact hi
  · exact Scoped.bvar

@[simp] theorem not_scoped_zero_bvar (i : Nat) :
    ¬ Scoped 0 (.bvar i) := by
  simp

@[simp] theorem scoped_top_iff (depth : Nat) :
    Scoped depth .top ↔ True := by
  constructor
  · intro _; trivial
  · intro _; exact Scoped.top

@[simp] theorem scoped_abs_iff (depth : Nat) (bound body : Term) :
    Scoped depth (.abs bound body) ↔
      Scoped depth bound ∧ Scoped (depth + 1) body := by
  constructor
  · intro h
    cases h with
    | abs h_bound h_body => exact ⟨h_bound, h_body⟩
  · intro h
    exact Scoped.abs h.1 h.2

@[simp] theorem scoped_app_iff (depth : Nat) (t u : Term) :
    Scoped depth (.app t u) ↔ Scoped depth t ∧ Scoped depth u := by
  constructor
  · intro h
    cases h with
    | app h_t h_u => exact ⟨h_t, h_u⟩
  · intro h
    exact Scoped.app h.1 h.2

@[simp] theorem closed_top : Closed .top := Scoped.top

@[simp] theorem closed_abs_iff (bound body : Term) :
    Closed (.abs bound body) ↔ Closed bound ∧ Scoped 1 body :=
  scoped_abs_iff 0 bound body

@[simp] theorem closed_app_iff (t u : Term) :
    Closed (.app t u) ↔ Closed t ∧ Closed u :=
  scoped_app_iff 0 t u

/-- Scoping is monotone in the ambient depth. This is the raw de Bruijn
weakening lemma for syntax. -/
theorem scoped_mono {depth depth' : Nat} {t : Term}
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
theorem Closed.scoped (depth : Nat) {t : Term} :
    Closed t → Scoped depth t :=
  scoped_mono (Nat.zero_le depth)

/-- One-step shifting preserves scoping, increasing the ambient depth by one. -/
theorem shift_scoped (cutoff depth : Nat) (t : Term)
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

/-- General shifting preserves scoping, increasing the ambient depth by the
shift amount. -/
theorem shiftBy_scoped (cutoff amount depth : Nat) (t : Term)
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
theorem shiftBy_of_scoped_id (cutoff amount : Nat) (t : Term) :
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
theorem shiftBy_closed_id (amount : Nat) (t : Term) :
    Closed t → shiftBy 0 amount t = t :=
  shiftBy_of_scoped_id 0 amount t

/-- Closed terms are invariant under one-step top-level shifting. -/
theorem shift_closed_id (t : Term) :
    Closed t → shift 0 t = t :=
  shiftBy_closed_id 1 t

/-- Instantiation preserves scoping and removes one available index from the
ambient depth. The premise `k ≤ depth` says the removed slot is among the
`depth + 1` slots available to the input term. -/
theorem instantiate_scoped (k depth : Nat) (v t : Term)
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
theorem instantiate_closed (v t : Term) :
    Closed v → Scoped 1 t → Closed (instantiate 0 v t) := by
  intro hv ht
  exact instantiate_scoped 0 0 v t (by omega) hv ht

/-- Instantiating an index at or above the current scoping depth has no
effect. This is the de Bruijn freshness/no-op substitution lemma. -/
theorem instantiate_of_scoped_id (k : Nat) (v t : Term) :
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
theorem instantiate_closed_id (v t : Term) :
    Closed t → instantiate 0 v t = t :=
  instantiate_of_scoped_id 0 v t

end Term
end DeBruijn
end Pss
