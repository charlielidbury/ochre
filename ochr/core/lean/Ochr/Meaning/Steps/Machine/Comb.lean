import Ochr.Meaning.Steps.Machine.GrowsIn

/-!
# `GrowsIn`: loops, handlers, and the brackets of `Env.lean`

Loops over lists, arrays and ranges, `mapM`, `anyM`, `foldlM`; the two handlers (`onFail`,
`catchStuck`); and the brackets that save and restore a flag, a private copy (`privately`,
`inStatement`) and a [Split] world (`enterWorld`, `inWorld`, `exitWorld`). A private copy's exit
keeps the counters and the frozen readings the copy made (`restoreKeep`), so it keeps the tables
when the saved state has the current globals and declarations (`OnTab`).
-/

namespace Ochr.Meaning.Steps.Machine

open Ochr Ochr.Meaning Ochr.Meaning.DecideScope Ochr.Meaning.Steps

variable {G : Tab}

/-- A write of the state that keeps the tables of the states with tables `G`. -/
theorem growsIn_modify' {g : MState → MState} (hg : ∀ s, OnTab G s → TablesGrow s (g s)) :
    GrowsIn G (modify g : M Unit) := by
  intro s f l b s' f' l' hs h
  cases h; exact hg s hs

/-! ## Loops -/

theorem growsIn_forIn_list {α β : Type} (xs : List α) (b : β) {body : α → β → M (ForInStep β)}
    (hb : ∀ a b, GrowsIn G (body a b)) : GrowsIn G (forIn xs b body) := by
  induction xs generalizing b with
  | nil => exact growsIn_pure b
  | cons a as ih =>
    rw [List.forIn_cons]
    exact growsIn_bind (hb a b) fun r => by cases r with
      | done b' => exact growsIn_pure b'
      | yield b' => exact ih b'

/-- A loop over a list, its body run only at the list's elements. -/
theorem growsIn_forIn_list_mem {α β : Type} (xs : List α) (b : β) {body : α → β → M (ForInStep β)}
    (hb : ∀ a ∈ xs, ∀ b, GrowsIn G (body a b)) : GrowsIn G (forIn xs b body) := by
  induction xs generalizing b with
  | nil => exact growsIn_pure b
  | cons a as ih =>
    rw [List.forIn_cons]
    exact growsIn_bind (hb a (List.mem_cons_self ..) b) fun r => by cases r with
      | done b' => exact growsIn_pure b'
      | yield b' => exact ih b' (fun a h => hb a (List.mem_cons_of_mem _ h))

theorem growsIn_mapM_list_mem {α β : Type} (xs : List α) {f : α → M β} (hf : ∀ a ∈ xs, GrowsIn G (f a)) :
    GrowsIn G (xs.mapM f) := by
  induction xs with
  | nil => exact growsIn_pure []
  | cons a as ih =>
    rw [List.mapM_cons]
    exact growsIn_bind (hf a (List.mem_cons_self ..)) fun b =>
      growsIn_bind (ih fun a h => hf a (List.mem_cons_of_mem _ h)) fun bs => growsIn_pure _

theorem growsIn_mapM_option {α β : Type} (o : Option α) {f : α → M β} (hf : ∀ a, GrowsIn G (f a)) :
    GrowsIn G (o.mapM f) := by
  cases o with
  | none => exact growsIn_pure _
  | some a => exact growsIn_bind (hf a) fun _ => growsIn_pure _

theorem growsIn_forIn_array {α β : Type} (xs : Array α) (b : β) {body : α → β → M (ForInStep β)}
    (hb : ∀ a b, GrowsIn G (body a b)) : GrowsIn G (forIn xs b body) := by
  rw [← Array.forIn_toList]
  exact growsIn_forIn_list _ _ hb

theorem growsIn_forIn_range {β : Type} (r : Std.Legacy.Range) (b : β) {body : Nat → β → M (ForInStep β)}
    (hb : ∀ a b, GrowsIn G (body a b)) : GrowsIn G (forIn r b body) := by
  rw [Std.Legacy.Range.forIn_eq_forIn_range']
  exact growsIn_forIn_list _ _ hb

theorem growsIn_mapM_list {α β : Type} (xs : List α) {f : α → M β} (hf : ∀ a, GrowsIn G (f a)) :
    GrowsIn G (xs.mapM f) := by
  induction xs with
  | nil => exact growsIn_pure []
  | cons a as ih =>
    rw [List.mapM_cons]
    exact growsIn_bind (hf a) fun b => growsIn_bind ih fun bs => growsIn_pure _

theorem growsIn_mapM_array {α β : Type} (xs : Array α) {f : α → M β} (hf : ∀ a, GrowsIn G (f a)) :
    GrowsIn G (xs.mapM f) := by
  rw [Array.mapM_eq_mapM_toList]
  exact growsIn_map _ (growsIn_mapM_list _ hf)

theorem growsIn_anyM_list {α : Type} (xs : List α) {f : α → M Bool} (hf : ∀ a, GrowsIn G (f a)) :
    GrowsIn G (xs.anyM f) := by
  induction xs with
  | nil => exact growsIn_pure _
  | cons a as ih =>
    unfold List.anyM
    exact growsIn_bind (hf a) fun b => by cases b <;> first | exact ih | exact growsIn_pure _

theorem growsIn_allM_list {α : Type} (xs : List α) {f : α → M Bool} (hf : ∀ a, GrowsIn G (f a)) :
    GrowsIn G (xs.allM f) := by
  induction xs with
  | nil => exact growsIn_pure _
  | cons a as ih =>
    unfold List.allM
    exact growsIn_bind (hf a) fun b => by cases b <;> first | exact ih | exact growsIn_pure _

theorem growsIn_foldlM_list {α β : Type} (xs : List α) (b : β) {f : β → α → M β}
    (hf : ∀ b a, GrowsIn G (f b a)) : GrowsIn G (xs.foldlM f b) := by
  induction xs generalizing b with
  | nil => exact growsIn_pure _
  | cons a as ih =>
    rw [List.foldlM_cons]
    exact growsIn_bind (hf b a) fun b' => ih b'

/-! ## Handlers -/

theorem growsIn_tryCatch {α : Type} {x : M α} {h : Fail → M α} (hx : GrowsIn G x) (hh : ∀ e, GrowsIn G (h e)) :
    GrowsIn G (tryCatch x h) := by
  intro s f l a s' f' l' hs e
  rw [runAll_tryCatch] at e
  revert e
  rcases e₀ : runAll x s f l with ⟨⟨e₁ | e₁ | ⟨b, s₁⟩, f₁⟩, l₁⟩
  · intro e; cases e
  · intro e; exact hh e₁ s f₁ l₁ a s' f' l' hs e
  · intro e
    simp only [Prod.mk.injEq, Except.ok.injEq] at e
    obtain ⟨⟨⟨rfl, rfl⟩, rfl⟩, rfl⟩ := e
    exact hx s f l _ _ _ _ hs e₀

theorem growsIn_tryCatchThe {α : Type} {x : M α} {h : Fail → M α} (hx : GrowsIn G x) (hh : ∀ e, GrowsIn G (h e)) :
    GrowsIn G (tryCatchThe Fail x h) :=
  growsIn_tryCatch hx hh

theorem growsIn_onFail {α : Type} {x : M α} {c : M Unit} (hx : GrowsIn G x) : GrowsIn G (onFail x c) := by
  unfold onFail
  refine growsIn_tryCatch hx fun e => ?_
  intro s f l a s' f' l' hs h
  rw [runAll_bind] at h
  revert h
  rcases runAll c s f l with ⟨⟨e₁ | e₁ | ⟨u, s₁⟩, f₁⟩, l₁⟩
  · intro h; cases h
  · intro h; cases h
  · intro h; cases h

theorem growsIn_catchStuck {α : Type} {x : M α} {h : Option Value → M α} (hx : GrowsIn G x)
    (hh : ∀ on, GrowsIn G (h on)) : GrowsIn G (catchStuck x h) := by
  unfold catchStuck
  refine growsIn_tryCatchThe hx fun e => ?_
  cases e with
  | stuck on => exact hh on
  | error m l => exact growsIn_throwThe _

theorem growsIn_locateErrors {α : Type} (l : Loc) {x : M α} (hx : GrowsIn G x) : GrowsIn G (locateErrors l x) := by
  unfold locateErrors
  refine growsIn_tryCatchThe hx fun e => ?_
  cases e with
  | stuck on => exact growsIn_throwThe _
  | error m at? => cases at? <;> exact growsIn_throwThe _

/-! ## The fuel and the log (below the state) -/

theorem runAll_tick (s : MState) (n : Nat) (l : Array LogEntry) :
    runAll tick s ⟨n⟩ l = (match n with
      | 0 => ((.error ⟨"out of fuel"⟩, ⟨0⟩), l)
      | k + 1 => ((.ok (.ok ((), s)), ⟨k⟩), l)) := by
  cases n <;> rfl

theorem growsIn_tick : GrowsIn G tick := by
  intro s ⟨n⟩ l a s' f' l' _ h
  rw [runAll_tick] at h
  cases n with
  | zero => cases h
  | succ k => cases h; exact TablesGrow.refl _

theorem growsIn_modifyThe_log (g : Array LogEntry → Array LogEntry) :
    GrowsIn G (modifyThe (Array LogEntry) g : M Unit) := by
  intro s f l a s' f' l' _ h
  cases h; exact TablesGrow.refl _

theorem growsIn_getThe_fuel : GrowsIn G (getThe Fuel : M Fuel) := by
  intro s f l a s' f' l' _ h
  cases h; exact TablesGrow.refl _

/-! ## Brackets that restore a flag -/

theorem growsIn_withLive {α : Type} (b : Bool) {x : M α} (hx : GrowsIn G x) : GrowsIn G (withLive b x) := by
  unfold withLive
  refine growsIn_get_bind fun _ _ => growsIn_bind (growsIn_modify fun s => ⟨rfl, rfl, Nat.le_refl _,
    fun _ _ => rfl, Nat.le_refl _, Nat.le_refl _⟩) fun _ => growsIn_bind (growsIn_onFail hx) fun _ =>
    growsIn_bind (growsIn_modify fun s => ⟨rfl, rfl, Nat.le_refl _, fun _ _ => rfl, Nat.le_refl _,
    Nat.le_refl _⟩) fun _ => growsIn_pure _

theorem growsIn_withErased {α : Type} {x : M α} (hx : GrowsIn G x) : GrowsIn G (withErased x) := by
  unfold withErased
  refine growsIn_bind (growsIn_modify fun s => ⟨rfl, rfl, Nat.le_refl _,
    fun _ _ => rfl, Nat.le_refl _, Nat.le_refl _⟩) fun _ => growsIn_bind (growsIn_onFail hx) fun _ =>
    growsIn_bind (growsIn_modify fun s => ⟨rfl, rfl, Nat.le_refl _, fun _ _ => rfl, Nat.le_refl _,
    Nat.le_refl _⟩) fun _ => growsIn_pure _

theorem growsIn_withErasedIf {α : Type} (b : Bool) {x : M α} (hx : GrowsIn G x) :
    GrowsIn G (withErasedIf b x) := by
  unfold withErasedIf
  split
  · exact growsIn_withErased hx
  · exact hx

theorem growsIn_withRuntime {α : Type} {x : M α} (hx : GrowsIn G x) : GrowsIn G (withRuntime x) := by
  unfold withRuntime
  refine growsIn_get_bind fun _ _ => growsIn_get_bind fun _ _ => growsIn_bind (growsIn_modify fun s => ⟨rfl, rfl, Nat.le_refl _,
    fun _ _ => rfl, Nat.le_refl _, Nat.le_refl _⟩) fun _ => growsIn_bind (growsIn_onFail hx) fun _ =>
    growsIn_bind (growsIn_modify fun s => ⟨rfl, rfl, Nat.le_refl _, fun _ _ => rfl, Nat.le_refl _,
    Nat.le_refl _⟩) fun _ => growsIn_pure _

theorem growsIn_withCopying {α : Type} {x : M α} (hx : GrowsIn G x) : GrowsIn G (withCopying x) := by
  unfold withCopying
  refine growsIn_get_bind fun _ _ => growsIn_bind (growsIn_modify fun s => ⟨rfl, rfl, Nat.le_refl _,
    fun _ _ => rfl, Nat.le_refl _, Nat.le_refl _⟩) fun _ => growsIn_bind (growsIn_onFail hx) fun _ =>
    growsIn_bind (growsIn_modify fun s => ⟨rfl, rfl, Nat.le_refl _, fun _ _ => rfl, Nat.le_refl _,
    Nat.le_refl _⟩) fun _ => growsIn_pure _

/-! ## Private copies and worlds: the exits keep the counters and the frozen readings -/

theorem growsIn_restoreKeep {saved : MState} (h : OnTab G saved) : GrowsIn G (restoreKeep saved) := by
  unfold restoreKeep
  exact growsIn_modify' fun s hs => ⟨h.1.trans hs.1.symm, h.2.trans hs.2.symm, Nat.le_refl _,
    fun _ _ => rfl, Nat.le_refl _, Nat.le_refl _⟩

/-- `restoreNames` (a comparison's exit, D103) to a state with the current globals and declarations
keeps the tables: it keeps the counters and the frozen readings the comparison made. -/
theorem growsIn_restoreNames {saved : MState} (h : OnTab G saved) : GrowsIn G (restoreNames saved) := by
  unfold restoreNames
  exact growsIn_modify' fun s hs => ⟨h.1.trans hs.1.symm, h.2.trans hs.2.symm, Nat.le_refl _,
    fun _ _ => rfl, Nat.le_refl _, Nat.le_refl _⟩

theorem growsIn_exitWorld {w : World} (h : OnTab G w.saved) : GrowsIn G (exitWorld w) := by
  unfold exitWorld
  exact growsIn_modify' fun s hs => ⟨h.1.trans hs.1.symm, h.2.trans hs.2.symm, Nat.le_refl _,
    fun _ _ => rfl, Nat.le_refl _, Nat.le_refl _⟩

theorem growsIn_inWorld {α : Type} {w : World} (h : OnTab G w.saved) {x : M α} (hx : GrowsIn G x) :
    GrowsIn G (inWorld w x) := by
  unfold inWorld
  exact growsIn_bind hx fun _ => growsIn_bind (growsIn_exitWorld h) fun _ => growsIn_pure _

/-- `enterWorld` reads the state, which has the tables `G`. -/
theorem growsIn_enterWorld_bind {α : Type} {k : World → M α} (hk : ∀ w, OnTab G w.saved → GrowsIn G (k w)) :
    GrowsIn G (enterWorld >>= k) := by
  intro s f l b s' f' l' hs h
  exact hk ⟨s⟩ hs s f l b s' f' l' hs h

theorem growsIn_privately {α : Type} {x : M α} (hx : GrowsIn G x) : GrowsIn G (privately x) := by
  have e : privately x = (do
      let saved ← get
      modify fun s => { s with privateDepth := s.privateDepth + 1 }
      let r ← onFail x (restoreKeep saved)
      restoreKeep saved
      pure r) := rfl
  rw [e]
  exact growsIn_get_bind fun saved hs => growsIn_bind (growsIn_modify fun s => ⟨rfl, rfl, Nat.le_refl _,
    fun _ _ => rfl, Nat.le_refl _, Nat.le_refl _⟩) fun _ => growsIn_bind (growsIn_onFail hx) fun _ =>
    growsIn_bind (growsIn_restoreKeep hs) fun _ => growsIn_pure _

theorem growsIn_inStatement {α : Type} {x : M α} (hx : GrowsIn G x) : GrowsIn G (inStatement x) :=
  growsIn_privately (growsIn_withErased hx)

/-! ## Fresh names -/

theorem growsIn_freshAbs (ty : Value) (d : DeclInfo) : GrowsIn G (freshAbs ty d) := by
  intro s f l a s' f' l' _ h
  have e : runAll (freshAbs ty d) s f l =
      ((.ok (.ok (s.nextAbs, { s with nextAbs := s.nextAbs + 1, absTy := s.absTy.push ty, absDecl := s.absDecl.push d })), f), l) := rfl
  rw [e] at h
  cases h
  refine ⟨rfl, rfl, ?_, fun σ hσ => ?_, Nat.le_succ _, Nat.le_refl _⟩
  · simp
  · simp [Array.getElem?_push, Nat.ne_of_lt hσ]

theorem growsIn_freshLoan : GrowsIn G freshLoan := by
  intro s f l a s' f' l' _ h
  have e : runAll freshLoan s f l = ((.ok (.ok (s.nextLoan, { s with nextLoan := s.nextLoan + 1 })), f), l) := rfl
  rw [e] at h
  cases h
  exact ⟨rfl, rfl, Nat.le_refl _, fun _ _ => rfl, Nat.le_refl _, Nat.le_succ _⟩

/-! ## A run from one known state (a read of the state, then a write of a state made from it) -/

/-- Every successful run of `y` from `s` only extends the tables. -/
def GrowsAt (s : MState) {α : Type} (y : M α) : Prop :=
  ∀ f l a s' f' l', runAll y s f l = ((.ok (.ok (a, s')), f'), l') → TablesGrow s s'

theorem growsIn_get_bind_at {α : Type} {k : MState → M α} (hk : ∀ s, OnTab G s → GrowsAt s (k s)) :
    GrowsIn G (get >>= k) := by
  intro s f l b s' f' l' hs h
  exact hk s hs f l b s' f' l' h

theorem growsAt_of_growsIn {α : Type} {s : MState} {y : M α} (hs : OnTab G s) (h : GrowsIn G y) : GrowsAt s y :=
  fun f l a s' f' l' e => h s f l a s' f' l' hs e

theorem growsAt_set_bind {α : Type} {s s₀ : MState} {k : PUnit → M α} (h₀ : TablesGrow s s₀) (hs : OnTab G s)
    (hk : ∀ u, GrowsIn G (k u)) : GrowsAt s (set s₀ >>= k) := by
  intro f l a s' f' l' e
  exact h₀.trans (hk _ s₀ f l a s' f' l' (hs.of_grows h₀) e)

theorem growsAt_keep_bind {α β : Type} {s : MState} {x : M α} {k : α → M β} (hx : Slice.Keep x)
    (hk : ∀ a, GrowsAt s (k a)) : GrowsAt s (x >>= k) := by
  intro f l b s' f' l' e
  rw [runAll_bind] at e
  revert e
  rcases e₀ : runAll x s f l with ⟨⟨e₁ | e₁ | ⟨a, s₁⟩, f₁⟩, l₁⟩
  · intro e; cases e
  · intro e; cases e
  · intro e
    have := hx s f l a s₁ f₁ l₁ e₀
    subst this
    exact hk a f₁ l₁ b s' f' l' e

/-- A read of the state `cur`, any computation, then a write of `cur` back: the tables are `cur`'s
again, whatever the computation did (`closeBlock`'s check at each arm's end state, `set e` …
`set cur`). -/
theorem growsIn_get_restore {α β : Type} {x : MState → M α} {k : MState → PUnit → M β}
    (hk : ∀ s, OnTab G s → ∀ u, GrowsIn G (k s u)) :
    GrowsIn G (get >>= fun cur => x cur >>= fun _ => set cur >>= k cur) := by
  refine growsIn_get_bind_at fun cur hs => ?_
  intro f l b s' f' l' e
  rw [runAll_bind] at e
  revert e
  rcases runAll (x cur) cur f l with ⟨⟨e₁ | e₁ | ⟨a, s₁⟩, f₁⟩, l₁⟩
  · intro e; cases e
  · intro e; cases e
  · intro e
    exact hk cur hs () cur f₁ l₁ b s' f' l' hs e

end Ochr.Meaning.Steps.Machine
