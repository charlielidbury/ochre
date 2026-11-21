import Ochr.Meaning.Steps.Slice.DecideKeep

/-!
# A run at one fuel is a run at more: the relation and its closure (the decisions' fuel facts)

`FuelLe x y`: every successful run of `x` is a successful run of `y`, with the same value and the
same final state, from the same state and ANY fuel budget and log. It is the relation between a
decision procedure at fuel `n` and at fuel `n + 1`: out of fuel is never caught (`ochr/core/CLAUDE.md`),
so a run that succeeds never met the bound, and with more fuel takes the same path. The decision
procedures never read or write the fuel budget or the log, which is why "any budget and log" holds.

The closure lemmas below relate two computations of the same shape, step for step.
-/

namespace Ochr.Meaning.Steps.Machine

open Ochr Ochr.Meaning Ochr.Meaning.DecideScope

/-- Every successful run of `x` is one of `y` (same value, same final state), from any budget and log. -/
def FuelLe {α : Type} (x y : M α) : Prop :=
  ∀ s f l a s' f' l' (g : Fuel) (l₂ : Array LogEntry), runAll x s f l = ((.ok (.ok (a, s')), f'), l') →
    ∃ g' l₂', runAll y s g l₂ = ((.ok (.ok (a, s')), g'), l₂')

theorem FuelLe.trans {α : Type} {x y z : M α} (h₁ : FuelLe x y) (h₂ : FuelLe y z) : FuelLe x z := by
  intro s f l a s' f' l' g l₂ e
  obtain ⟨g₁, l₁, e₁⟩ := h₁ s f l a s' f' l' g l₂ e
  exact h₂ s g l₂ a s' g₁ l₁ g l₂ e₁

theorem fuelLe_bind {α β : Type} {x x' : M α} {k k' : α → M β} (hx : FuelLe x x') (hk : ∀ a, FuelLe (k a) (k' a)) :
    FuelLe (x >>= k) (x' >>= k') := by
  intro s f l b s' f' l' g l₂ e
  rw [runAll_bind] at e
  revert e
  rcases e₀ : runAll x s f l with ⟨⟨e₁ | e₁ | ⟨a, s₁⟩, f₁⟩, l₁⟩
  · intro e; cases e
  · intro e; cases e
  · intro e
    obtain ⟨g₁, l₃, e₁⟩ := hx s f l a s₁ f₁ l₁ g l₂ e₀
    obtain ⟨g₂, l₄, e₂⟩ := hk a s₁ f₁ l₁ b s' f' l' g₁ l₃ e
    exact ⟨g₂, l₄, by rw [runAll_bind, e₁]; exact e₂⟩

theorem fuelLe_pure {α : Type} (a : α) : FuelLe (pure a : M α) (pure a) := by
  intro s f l b s' f' l' g l₂ e
  cases e; exact ⟨g, l₂, rfl⟩

theorem fuelLe_err {α : Type} (m : String) (y : M α) : FuelLe (err m : M α) y := by
  intro s f l b s' f' l' g l₂ e; cases e

theorem fuelLe_exhausted {α : Type} (m : String) (y : M α) : FuelLe (exhausted m : M α) y := by
  intro s f l b s' f' l' g l₂ e; cases e

theorem fuelLe_get_bind {α : Type} {k k' : MState → M α} (hk : ∀ s, FuelLe (k s) (k' s)) :
    FuelLe (get >>= k) (get >>= k') := by
  intro s f l b s' f' l' g l₂ e
  exact hk s s f l b s' f' l' g l₂ e

theorem fuelLe_modify_bind {α : Type} (h : MState → MState) {k k' : PUnit → M α} (hk : ∀ u, FuelLe (k u) (k' u)) :
    FuelLe (modify h >>= k) (modify h >>= k') := by
  intro s f l b s' f' l' g l₂ e
  exact hk () (h s) f l b s' f' l' g l₂ e

theorem fuelLe_modify (h : MState → MState) : FuelLe (modify h : M Unit) (modify h) := by
  intro s f l b s' f' l' g l₂ e
  cases e; exact ⟨g, l₂, rfl⟩

theorem fuelLe_ite {α : Type} {c : Prop} [Decidable c] {x x' y y' : M α} (hx : FuelLe x x') (hy : FuelLe y y') :
    FuelLe (if c then x else y) (if c then x' else y') := by
  split <;> assumption

theorem fuelLe_dite {α : Type} {c : Prop} [Decidable c] {x x' : c → M α} {y y' : ¬ c → M α}
    (hx : ∀ h, FuelLe (x h) (x' h)) (hy : ∀ h, FuelLe (y h) (y' h)) :
    FuelLe (if h : c then x h else y h) (if h : c then x' h else y' h) := by
  split
  · exact hx _
  · exact hy _

theorem fuelLe_map {α β : Type} (g : α → β) {x x' : M α} (hx : FuelLe x x') : FuelLe (g <$> x) (g <$> x') := by
  rw [map_eq_pure_bind, map_eq_pure_bind]
  exact fuelLe_bind hx fun a => fuelLe_pure _

theorem fuelLe_discard {α : Type} {x x' : M α} (hx : FuelLe x x') : FuelLe (discard x) (discard x') := by
  show FuelLe (Functor.mapConst PUnit.unit x) (Functor.mapConst PUnit.unit x')
  rw [LawfulFunctor.map_const]
  exact fuelLe_map _ hx

theorem fuelLe_forIn {α β : Type} (xs : List α) (b : β) {body body' : α → β → M (ForInStep β)}
    (hb : ∀ a b, FuelLe (body a b) (body' a b)) : FuelLe (forIn xs b body) (forIn xs b body') := by
  induction xs generalizing b with
  | nil => exact fuelLe_pure b
  | cons a as ih =>
    rw [List.forIn_cons, List.forIn_cons]
    exact fuelLe_bind (hb a b) fun r => by cases r with
      | done b' => exact fuelLe_pure b'
      | yield b' => exact ih b'

theorem fuelLe_mapM {α β : Type} (xs : List α) {f f' : α → M β} (hf : ∀ a, FuelLe (f a) (f' a)) :
    FuelLe (xs.mapM f) (xs.mapM f') := by
  induction xs with
  | nil => exact fuelLe_pure []
  | cons a as ih =>
    rw [List.mapM_cons, List.mapM_cons]
    exact fuelLe_bind (hf a) fun b => fuelLe_bind ih fun bs => fuelLe_pure _

theorem fuelLe_allM {α : Type} (xs : List α) {f f' : α → M Bool} (hf : ∀ a, FuelLe (f a) (f' a)) :
    FuelLe (xs.allM f) (xs.allM f') := by
  induction xs with
  | nil => exact fuelLe_pure _
  | cons a as ih =>
    unfold List.allM
    exact fuelLe_bind (hf a) fun b => by cases b <;> first | exact ih | exact fuelLe_pure _

theorem fuelLe_onFail {α : Type} {x x' : M α} {c c' : M Unit} (hx : FuelLe x x') :
    FuelLe (onFail x c) (onFail x' c') := by
  intro s f l b s' f' l' g l₂ e
  unfold onFail at e ⊢
  rw [runAll_tryCatch] at e ⊢
  revert e
  rcases e₀ : runAll x s f l with ⟨⟨e₁ | e₁ | ⟨a, s₁⟩, f₁⟩, l₁⟩
  · intro e; cases e
  · intro e
    exfalso
    revert e
    show runAll (do c; throw e₁ : M α) s f₁ l₁ ≠ _
    exact Slice.runAll_cleanup_throw c e₁ s f₁ l₁ b s' f' l'
  · intro e
    simp only [Prod.mk.injEq, Except.ok.injEq] at e
    obtain ⟨⟨⟨rfl, rfl⟩, rfl⟩, rfl⟩ := e
    obtain ⟨g₁, l₃, e₁⟩ := hx s f l a s₁ f₁ l₁ g l₂ e₀
    exact ⟨g₁, l₃, by rw [e₁]⟩

theorem fuelLe_withLive {α : Type} (b : Bool) {x x' : M α} (hx : FuelLe x x') : FuelLe (withLive b x) (withLive b x') := by
  unfold withLive
  exact fuelLe_get_bind fun s => fuelLe_modify_bind _ fun _ => fuelLe_bind (fuelLe_onFail hx) fun _ =>
    fuelLe_modify_bind _ fun _ => fuelLe_pure _

end Ochr.Meaning.Steps.Machine
