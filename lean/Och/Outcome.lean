/-!
# Outcome: unified result type for Ochre's evaluation pipeline

Introduced 2026-04-23 as part of the `Option`/`Except` unification.

`Outcome` distinguishes three possible results for the `eval`/`vapp`/
`quote`/`subCheckVal`/`tyInfer`/`tyCheck` functions:

- `.ok a` — computation succeeded with value `a`.
- `.outOfFuel` — ran out of fuel; benign, caller can retry with more.
- `.error msg` — hit a rule that doesn't apply or a type-check
  violation. `msg` carries diagnostic information for debugging.

The key semantic distinction: `.outOfFuel` is recoverable by
increasing fuel; `.error` is a genuine failure. The
`progress_mod_fuel` theorem (future work; see paper.md §7.1) will
prove that well-typed programs never return `.error` — only `.ok`
or `.outOfFuel`. Splitting the two in the return type is the
prerequisite.
-/

universe u v

/-- Unified result type for Ochre's evaluation and type-checking
pipeline. See module doc. -/
inductive Outcome (α : Type u) : Type u where
  | ok        : α → Outcome α
  | outOfFuel : Outcome α
  | error     : String → Outcome α
  deriving Inhabited, Repr

namespace Outcome

instance : Monad Outcome where
  pure := .ok
  bind x f := match x with
    | .ok a       => f a
    | .outOfFuel  => .outOfFuel
    | .error s    => .error s

theorem bind_def {α β : Type u} (x : Outcome α) (f : α → Outcome β) :
    (x >>= f) = match x with
      | .ok a => f a
      | .outOfFuel => .outOfFuel
      | .error s => .error s := rfl

instance : LawfulMonad Outcome := LawfulMonad.mk'
  (id_map := fun x => by cases x <;> rfl)
  (pure_bind := fun _ _ => rfl)
  (bind_assoc := fun x _ _ => by cases x <;> rfl)

/-- Lift an `Option` into an `Outcome`, treating `none` as an error
with the given message. -/
def ofOption {α : Type u} (msg : String) : Option α → Outcome α
  | some a => .ok a
  | none   => .error msg

/-- Lift from `Except String` (legacy interop during migration). -/
def ofExcept {α : Type u} : Except String α → Outcome α
  | .ok a    => .ok a
  | .error s => .error s

/-- Handle an error case with a recovery function. -/
def catchError {α : Type u} : Outcome α → (String → Outcome α) → Outcome α
  | .error s, f => f s
  | x, _        => x

/-- Check fuel and decrement before running body. If `fuel = 0`,
return `.outOfFuel`; otherwise, run `body` with `fuel - 1`. -/
def withFuel {α : Type u} (fuel : Nat) (body : Nat → Outcome α) : Outcome α :=
  match fuel with
  | 0 => .outOfFuel
  | n+1 => body n

/-- Whether an outcome is successful. -/
def isOk {α : Type u} : Outcome α → Bool
  | .ok _ => true
  | _ => false

/-- Whether an outcome represents a genuine error (not fuel). -/
def isError {α : Type u} : Outcome α → Bool
  | .error _ => true
  | _ => false

/-- Whether an outcome ran out of fuel. -/
def isOutOfFuel {α : Type u} : Outcome α → Bool
  | .outOfFuel => true
  | _ => false

/-- Extract the value, or a default if not ok. -/
def getD {α : Type u} (default : α) : Outcome α → α
  | .ok a => a
  | _ => default

/-- Extract the value; panics if not `.ok`. Used primarily in test
sites where failure means a bug in the test setup. -/
def get! {α : Type u} [Inhabited α] : Outcome α → α
  | .ok a => a
  | .outOfFuel => panic! "Outcome.get!: outOfFuel"
  | .error s => panic! s!"Outcome.get!: error: {s}"

/-- Map the error message. -/
def mapError {α : Type u} (f : String → String) : Outcome α → Outcome α
  | .error s => .error (f s)
  | x => x

/-- Convert to an `Option`, discarding the distinction between
`.outOfFuel` and `.error`. Handy for bridging legacy code. -/
def toOption {α : Type u} : Outcome α → Option α
  | .ok a => some a
  | _ => none

/-- Convert to an `Except String α`, discarding the distinction
between `.outOfFuel` and `.error`. `.outOfFuel` becomes
`.error "out of fuel"`. Used by the legacy-Except `subCheckVal`
family to consume `Outcome`-valued `eval`/`vapp`/`open` results. -/
def toExcept {α : Type u} (fuelMsg : String := "out of fuel") : Outcome α → Except String α
  | .ok a => .ok a
  | .outOfFuel => .error fuelMsg
  | .error s => .error s

/-- Decidable equality on outcomes with decidable payloads. -/
instance {α : Type u} [DecidableEq α] : DecidableEq (Outcome α) := fun a b =>
  match a, b with
  | .ok a, .ok b =>
      if h : a = b then isTrue (by rw [h]) else isFalse (fun h2 => by cases h2; exact h rfl)
  | .outOfFuel, .outOfFuel => isTrue rfl
  | .error a, .error b =>
      if h : a = b then isTrue (by rw [h]) else isFalse (fun h2 => by cases h2; exact h rfl)
  | .ok _, .outOfFuel => isFalse (fun h => by cases h)
  | .ok _, .error _ => isFalse (fun h => by cases h)
  | .outOfFuel, .ok _ => isFalse (fun h => by cases h)
  | .outOfFuel, .error _ => isFalse (fun h => by cases h)
  | .error _, .ok _ => isFalse (fun h => by cases h)
  | .error _, .outOfFuel => isFalse (fun h => by cases h)

instance {α : Type u} [BEq α] : BEq (Outcome α) where
  beq a b := match a, b with
    | .ok a, .ok b => a == b
    | .outOfFuel, .outOfFuel => true
    | .error a, .error b => a == b
    | _, _ => false

/-! ## Simp lemmas -/

@[simp] theorem ok_bind {α β : Type u} (a : α) (f : α → Outcome β) :
    (Outcome.ok a >>= f) = f a := rfl

@[simp] theorem outOfFuel_bind {α β : Type u} (f : α → Outcome β) :
    (Outcome.outOfFuel : Outcome α) >>= f = .outOfFuel := rfl

@[simp] theorem error_bind {α β : Type u} (s : String) (f : α → Outcome β) :
    (Outcome.error s : Outcome α) >>= f = .error s := rfl

@[simp] theorem pure_eq_ok {α : Type u} (a : α) : (pure a : Outcome α) = .ok a := rfl

/-- Bind-unfold: `x >>= f = .ok v` iff there's an intermediate
`a` with `x = .ok a` and `f a = .ok v`. Mirrors
`Option.bind_eq_some`. -/
@[simp] theorem bind_eq_ok {α β : Type u} (x : Outcome α)
    (f : α → Outcome β) (v : β) :
    (x >>= f) = .ok v ↔ ∃ a, x = .ok a ∧ f a = .ok v := by
  cases x <;> simp [bind, Monad.toBind]

end Outcome
