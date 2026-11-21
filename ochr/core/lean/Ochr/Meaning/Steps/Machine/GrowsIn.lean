import Ochr.Meaning.Steps.Machine.Defs
import Ochr.Meaning.Steps.Slice.DecideKeep

/-!
# `GrowsIn G x`: the tables only grow, from a state whose globals and declarations are `G`

The closure lemmas of the monad, stated on the raw run (`DecideScope.runAll`, as `Slice.DecideKeep`
does): every combinator the machine uses keeps the property. The globals and the declarations are
the same at every state of a run (a `TablesGrow` keeps them), so a state read by `get` has them,
and a private copy's exit to it (`restoreKeep`, `exitWorld`) keeps the tables.
-/

namespace Ochr.Meaning.Steps.Machine

open Ochr Ochr.Meaning Ochr.Meaning.DecideScope Ochr.Meaning.Steps

/-- The globals and the declarations of a run (fixed along it). -/
abbrev Tab := List GDef × List IndDecl

/-- `s` has the globals and the declarations `G`. -/
def OnTab (G : Tab) (s : MState) : Prop := s.globals = G.1 ∧ s.inds = G.2

theorem OnTab.of_grows {G : Tab} {s s' : MState} (h : OnTab G s) (hg : TablesGrow s s') : OnTab G s' :=
  ⟨hg.globals.trans h.1, hg.inds.trans h.2⟩

/-- Every successful run of `x` from a state with the tables `G` only extends the tables. -/
def GrowsIn (G : Tab) {α : Type} (x : M α) : Prop :=
  ∀ s f l a s' f' l', OnTab G s → runAll x s f l = ((.ok (.ok (a, s')), f'), l') → TablesGrow s s'

variable {G : Tab}

theorem growsIn_bind {α β : Type} {x : M α} {k : α → M β} (hx : GrowsIn G x) (hk : ∀ a, GrowsIn G (k a)) :
    GrowsIn G (x >>= k) := by
  intro s f l b s' f' l' hs h
  rw [runAll_bind] at h
  revert h
  rcases e : runAll x s f l with ⟨⟨e₁ | e₁ | ⟨a, s₁⟩, f₁⟩, l₁⟩
  · intro h; cases h
  · intro h; cases h
  · intro h
    have h1 := hx s f l a s₁ f₁ l₁ hs e
    exact h1.trans (hk a s₁ f₁ l₁ b s' f' l' (hs.of_grows h1) h)

theorem growsIn_pure {α : Type} (a : α) : GrowsIn G (pure a : M α) := by
  intro s f l b s' f' l' _ h
  simp only [runAll, pure, StateT.pure, ExceptT.pure, ExceptT.mk] at h
  cases h; exact TablesGrow.refl _

theorem growsIn_throw {α : Type} (e : Fail) : GrowsIn G (throw e : M α) := by
  intro s f l b s' f' l' _ h; cases h

theorem growsIn_throwThe {α : Type} (e : Fail) : GrowsIn G (throwThe Fail e : M α) := by
  intro s f l b s' f' l' _ h; cases h

theorem growsIn_err {α : Type} (m : String) : GrowsIn G (err m : M α) := by
  intro s f l b s' f' l' _ h; cases h

theorem growsIn_exhausted {α : Type} (m : String) : GrowsIn G (exhausted m : M α) := by
  intro s f l b s' f' l' _ h; cases h

theorem growsIn_stuckNow {α : Type} : GrowsIn G (stuckNow : M α) := by
  intro s f l b s' f' l' _ h; cases h

theorem growsIn_stuckOn {α : Type} (v : Value) : GrowsIn G (stuckOn v : M α) := by
  intro s f l b s' f' l' _ h; cases h

/-- A read of the state, which has the tables `G`. -/
theorem growsIn_get_bind {α : Type} {k : MState → M α} (hk : ∀ s, OnTab G s → GrowsIn G (k s)) :
    GrowsIn G (get >>= k) := by
  intro s f l b s' f' l' hs h
  exact hk s hs s f l b s' f' l' hs h

theorem growsIn_get : GrowsIn G (get : M MState) := by
  intro s f l b s' f' l' _ h
  cases h; exact TablesGrow.refl _

theorem growsIn_modify {g : MState → MState} (hg : ∀ s, TablesGrow s (g s)) : GrowsIn G (modify g : M Unit) := by
  intro s f l b s' f' l' _ h
  cases h; exact hg s

/-- A write of the state with one that has the current tables. -/
theorem growsIn_set {s₀ : MState} (h : ∀ s, OnTab G s → TablesGrow s s₀) : GrowsIn G (set s₀ : M Unit) := by
  intro s f l b s' f' l' hs h'
  cases h'; exact h s hs

theorem growsIn_ite {α : Type} {c : Prop} [Decidable c] {x y : M α} (hx : GrowsIn G x) (hy : GrowsIn G y) :
    GrowsIn G (if c then x else y) := by
  split <;> assumption

theorem growsIn_dite {α : Type} {c : Prop} [Decidable c] {x : c → M α} {y : ¬ c → M α}
    (hx : ∀ h, GrowsIn G (x h)) (hy : ∀ h, GrowsIn G (y h)) : GrowsIn G (if h : c then x h else y h) := by
  split
  · exact hx _
  · exact hy _

theorem growsIn_map {α β : Type} (g : α → β) {x : M α} (hx : GrowsIn G x) : GrowsIn G (g <$> x) := by
  rw [map_eq_pure_bind]
  exact growsIn_bind hx fun a => growsIn_pure _

theorem growsIn_discard {α : Type} {x : M α} (hx : GrowsIn G x) : GrowsIn G (discard x) := by
  show GrowsIn G (Functor.mapConst PUnit.unit x)
  rw [LawfulFunctor.map_const]
  exact growsIn_map _ hx

/-- A computation that keeps the state keeps the tables. -/
theorem growsIn_of_keep {α : Type} {x : M α} (h : Slice.Keep x) : GrowsIn G x := by
  intro s f l b s' f' l' _ e
  rw [h s f l b s' f' l' e]; exact TablesGrow.refl _

/-- A run (`Runs`) from a state with the tables `G` of a computation that grows from there. -/
theorem GrowsIn.runs {α : Type} {x : M α} (h : GrowsIn G x) {st st' : MState} {b : Nat} {a : α}
    (hs : OnTab G st) (hr : Runs x st b a st') : TablesGrow st st' := by
  obtain ⟨L, left, log, hr⟩ := hr
  have key : runMachineL x st b L = (match runAll x st ⟨b⟩ L with
      | ((r, fl), log) => ((match r with
        | .error e => Outcome.exhausted e.msg
        | .ok (.error f) => .fail f
        | .ok (.ok (a, st')) => .ok a st'), fl.left, log)) := rfl
  rw [key] at hr
  rcases e : runAll x st ⟨b⟩ L with ⟨⟨e₁ | e₁ | ⟨a', s₁⟩, f₁⟩, l₁⟩ <;> rw [e] at hr
  · simp at hr
  · simp at hr
  · simp only [Prod.mk.injEq, Outcome.ok.injEq] at hr
    obtain ⟨⟨-, rfl⟩, -⟩ := hr
    exact h st ⟨b⟩ L a' s₁ f₁ l₁ hs e

/-- `GrowsM` is `GrowsIn` at every table. -/
theorem growsM_of_growsIn {α : Type} {x : M α} (h : ∀ G, GrowsIn G x) : GrowsM x := by
  intro st b a st' hr
  obtain ⟨L, left, log, hr⟩ := hr
  have key : runMachineL x st b L = (match runAll x st ⟨b⟩ L with
      | ((r, fl), log) => ((match r with
        | .error e => Outcome.exhausted e.msg
        | .ok (.error f) => .fail f
        | .ok (.ok (a, st')) => .ok a st'), fl.left, log)) := rfl
  rw [key] at hr
  rcases e : runAll x st ⟨b⟩ L with ⟨⟨e₁ | e₁ | ⟨a', s₁⟩, f₁⟩, l₁⟩ <;> rw [e] at hr
  · simp at hr
  · simp at hr
  · simp only [Prod.mk.injEq, Outcome.ok.injEq] at hr
    obtain ⟨⟨-, rfl⟩, -⟩ := hr
    exact h (st.globals, st.inds) st ⟨b⟩ L a' s₁ f₁ l₁ ⟨rfl, rfl⟩ e

theorem growsIn_of_growsM {α : Type} {x : M α} (h : GrowsM x) : GrowsIn G x := by
  intro s f l a s' f' l' _ e
  refine h s f.left a s' ⟨l, f'.left, l', ?_⟩
  show (match runAll x s ⟨f.left⟩ l with
      | ((r, fl), log) => ((match r with
        | .error e => Outcome.exhausted e.msg
        | .ok (.error f) => .fail f
        | .ok (.ok (a, st')) => .ok a st'), fl.left, log)) = _
  have : (⟨f.left⟩ : Fuel) = f := rfl
  rw [this, e]

end Ochr.Meaning.Steps.Machine
