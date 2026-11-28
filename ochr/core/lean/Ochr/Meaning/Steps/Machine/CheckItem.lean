import Ochr.Meaning.Steps.Machine.ConstRunJ

/-!
# What `checkItem` does to the declarations and the globals (machine10)

The parts of the existence lane's `ItemFacts` (`DataModel/Exists/Assembly.lean`) that are plain reads of
`Check.lean` (step 1 read them TRUE; `ItemFacts` as a whole is false, see the lane report):

* `runs_checkInd_tables`: an accepted inductive declaration appends exactly one entry, `d` with the nestable set
  `nestableSet` computed from the declarations before it (D107), and leaves the globals;
* `runs_checkDef_tables`: an accepted definition leaves the declarations and appends one global;
* `runs_checkItem_ind`, `runs_checkItem_defn`: the same through `checkItem` (`seedHoles` first, which writes only
  the unknowns' tables).

The checks `checkInd` runs between its two writes of the declarations read the state and write nothing it
reads (`keep_firstOrderTerm`, `keep_nestViolation`, `keep_readViolation`, here; the rest are the machine's and
the decisions', `machineGrows` and the leaves), so the declarations between the two writes are the stub's.
-/

namespace Ochr.Meaning.Steps.Machine

open Ochr Ochr.Meaning Ochr.Meaning.Steps Ochr.Meaning.DecideScope Ochr.Meaning.Steps.Slice
open Ochr.Meaning.Steps.Form

/-- `Tactic.lean`'s `grows_go` under a name of its own: `MachineMono.lean` declares a `grows_go` macro too (for
`GrowsM`), and where both are imported the parser takes the macro. -/
elab "grows_goI" : tactic => growsGo none

theorem keep_lookupInd (n : String) : Keep (lookupInd n) := by unfold lookupInd; keep_go

theorem keep_firstOrder (nest : NestTable) (n : String) (np k : Nat) :
    (∀ t, Keep (firstOrderTerm nest n np k t)) ∧ (∀ as, Keep (firstOrderCallArgs nest n np k as)) ∧
      (∀ m dm i as, Keep (firstOrderArgs nest n np k m dm i as)) := by
  refine firstOrderTerm.mutual_induct n (fun t => Keep (firstOrderTerm nest n np k t))
    (fun as => Keep (firstOrderCallArgs nest n np k as)) (fun m dm i as => Keep (firstOrderArgs nest n np k m dm i as))
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  all_goals intros
  all_goals (first
    | (unfold firstOrderTerm; keep_go)
    | (unfold firstOrderCallArgs; keep_go)
    | (unfold firstOrderArgs; keep_go))
  all_goals first | solve_by_elim | (exfalso; solve_by_elim [rfl])

theorem keep_nestViolation (nest : NestTable) (st : SortTable) (d : IndDecl) (n : String) :
    (∀ t, Keep (nestViolation nest st d n t)) ∧ (∀ m dm i as, Keep (nestViolationArgs nest st d n m dm i as)) := by
  refine nestViolation.mutual_induct nest st d n (fun t => Keep (nestViolation nest st d n t))
    (fun m dm i as => Keep (nestViolationArgs nest st d n m dm i as)) ?_ ?_ ?_ ?_ ?_ ?_
  all_goals intros
  all_goals (first
    | (unfold nestViolation; keep_go)
    | (unfold nestViolationArgs; keep_go))
  all_goals first | solve_by_elim | (exfalso; solve_by_elim [rfl])

theorem keep_readViolation (reads : Term → Option Nat) :
    (∀ t, Keep (readViolation reads t)) ∧ (∀ m dm i as, Keep (readViolationArgs reads m dm i as)) := by
  refine readViolation.mutual_induct reads (fun t => Keep (readViolation reads t))
    (fun m dm i as => Keep (readViolationArgs reads m dm i as)) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  all_goals intros
  all_goals (first
    | (unfold readViolation; keep_go)
    | (unfold readViolationArgs; keep_go))
  all_goals first | solve_by_elim | (exfalso; solve_by_elim [rfl])

variable {G : Tab}

@[grows] theorem growsIn_declared (n : String) : GrowsIn G (declared n) := growsIn_of_keep (keep_declared n)
@[grows] theorem growsIn_undeclaredCheck (self : Option String) (ts : List Term) (own : Option String) :
    GrowsIn G (undeclaredCheck self ts own) := growsIn_of_keep (keep_undeclaredCheck self ts own)
@[grows] theorem growsIn_firstOrderTerm (nest : NestTable) (n : String) (np k : Nat) (t : Term) :
    GrowsIn G (firstOrderTerm nest n np k t) := growsIn_of_keep ((keep_firstOrder nest n np k).1 t)
@[grows] theorem growsIn_nestViolation (nest : NestTable) (st : SortTable) (d : IndDecl) (n : String) (t : Term) :
    GrowsIn G (nestViolation nest st d n t) := growsIn_of_keep ((keep_nestViolation nest st d n).1 t)
@[grows] theorem growsIn_readViolation (reads : Term → Option Nat) (t : Term) :
    GrowsIn G (readViolation reads t) := growsIn_of_keep ((keep_readViolation reads).1 t)

/-- A run of `x >>= k` with `x` only growing the tables. -/
theorem Runs.grows_bind {α β : Type} {x : M α} {k : α → M β} {s s' : MState} {b : Nat} {r : β}
    (hx : ∀ G, GrowsIn G x) (h : Runs (x >>= k) s b r s') : ∃ a s₁ b₁, TablesGrow s s₁ ∧ Runs (k a) s₁ b₁ r s' := by
  obtain ⟨a, s₁, b₁, h₁, h₂⟩ := Runs.bind_inv h
  exact ⟨a, s₁, b₁, Runs.grows (growsM_of_growsIn hx) h₁, h₂⟩

theorem runs_declared_inv {n : String} {st st' : MState} {b : Nat} {c : Bool} (h : Runs (declared n) st b c st') :
    c = (st.globals.any (·.name == n) || st.inds.any fun e => e.name == n || e.ctors.any (·.1 == n)) ∧ st' = st := by
  unfold declared at h
  rw [runs_get_bind] at h
  obtain ⟨rfl, rfl⟩ := runs_pure_inv h
  exact ⟨rfl, rfl⟩

set_option maxHeartbeats 8000000 in
/-- **An accepted inductive declaration appends one entry and leaves the globals.** -/
theorem runs_checkInd_tables {d : IndDecl} {st st' : MState} {b : Nat} (h : Runs (checkInd d) st b () st') :
    st'.globals = st.globals ∧
      st'.inds = st.inds ++ [{ d with nestable := nestableSet (nestTableOf st.inds) (sortTableOf st.inds d) d }] := by
  have hET : ∀ (G : Tab) (f : Nat) (t : Term), GrowsIn G (Ochr.evalType f t) := fun G f => (machineGrows f).evalType
  have hFT : ∀ (G : Tab) (f : Nat) (d : IndDecl) (ps : List Value) (c : Nat) (val : Nat → Value → M Value),
      (∀ i v, GrowsIn G (val i v)) → ∀ upto, GrowsIn G (Ochr.fieldTele f d ps c val upto) :=
    fun G f => (machineGrows f).fieldTele
  unfold checkInd at h
  dsimp (config := { proj := false }) only at h
  obtain ⟨c, s₁, b₁, hd, h⟩ := Runs.bind_inv h
  obtain ⟨hc, hs₁⟩ := runs_declared_inv hd
  subst hs₁
  clear hd
  cases c
  case true =>
    rw [if_pos rfl] at h
    obtain ⟨_, _, _, he, _⟩ := Runs.bind_inv h; exact (runs_err_false he).elim
  rw [if_neg Bool.false_ne_true] at h
  obtain ⟨_, s₂, b₂, hg₂, h⟩ := Runs.grows_bind (fun G => by grows_goI) h
  by_cases hsort : d.sort > 1
  · rw [if_pos hsort] at h
    obtain ⟨_, _, _, he, _⟩ := Runs.bind_inv h; exact (runs_err_false he).elim
  rw [if_neg hsort] at h
  rw [runs_get_bind, runs_get_bind, runs_modify_bind] at h
  obtain ⟨_, s₃, b₃, hg₃, h⟩ := Runs.grows_bind (fun G => by grows_goI) h
  obtain ⟨_, s₄, b₄, hg₄, h⟩ := Runs.grows_bind (fun G => by grows_goI) h
  obtain ⟨_, s₅, b₅, hg₅, h⟩ := Runs.grows_bind (fun G => by grows_goI) h
  obtain ⟨x, s₆, b₆, hg₆, h⟩ := Runs.grows_bind (fun G => by grows_goI) h
  obtain ⟨sc, ns, l⟩ := x
  -- main's D128 (the written-sort check on parameters) and D133 (`undeclaredCheck` split in two) add two steps
  obtain ⟨_, s₇a, b₇a, hg₇a, h⟩ := Runs.grows_bind (fun G => by grows_goI) h
  obtain ⟨_, s₇, b₇, hg₇, h⟩ := Runs.grows_bind (fun G => by grows_goI) h
  obtain ⟨_, s₇b, b₇b, hg₇b, h⟩ := Runs.grows_bind (fun G => by grows_goI) h
  obtain ⟨_, s₈, b₈, hg₈, h⟩ := Runs.grows_bind (fun G => by grows_goI) h
  -- main's D141 (a parameter reading "any" rejected) adds one step
  obtain ⟨_, s₈a, b₈a, hg₈a, h⟩ := Runs.grows_bind (fun G => by grows_goI) h
  -- main's D140 (the written heads of field types) adds one step
  obtain ⟨_, s₈b, b₈b, hg₈b, h⟩ := Runs.grows_bind (fun G => by grows_goI) h
  obtain ⟨ps, s₉, b₉, hg₉, h⟩ := Runs.grows_bind (fun G => by grows_goI) h
  obtain ⟨_, s₁₀, b₁₀, hg₁₀, h⟩ := Runs.grows_bind (fun G => by grows_goI) h
  have hst := runs_modify_inv h
  subst hst
  have hT := (((((((((((hg₃.trans hg₄).trans hg₅).trans hg₆).trans hg₇a).trans hg₇).trans hg₇b).trans hg₈).trans hg₈a).trans hg₈b).trans hg₉).trans hg₁₀)
  have hfresh : ∀ e ∈ s₁.inds, (e.name == d.name) = false := by
    intro e he
    have h2 : (s₁.inds.any fun e => e.name == d.name || e.ctors.any (·.1 == d.name)) = false := by
      cases h3 : (s₁.inds.any fun e => e.name == d.name || e.ctors.any (·.1 == d.name))
      · rfl
      · rw [h3, Bool.or_true] at hc; cases hc
    have := List.any_eq_false.1 h2 e he
    cases h4 : (e.name == d.name)
    · rfl
    · simp [h4] at this
  refine ⟨hT.globals.trans hg₂.globals, ?_⟩
  show List.map _ s₁₀.inds = _
  rw [hT.inds]
  show List.map _ (s₂.inds ++ _) = _
  rw [hg₂.inds, List.map_append]
  congr 1
  · conv => rhs; rw [← List.map_id s₁.inds]
    exact List.map_congr_left fun e he => by rw [hfresh e he]; rfl
  · simp

set_option maxHeartbeats 8000000 in
/-- **An accepted definition leaves the declarations and appends one global.** -/
theorem runs_checkDef_tables {d : Def} {st st' : MState} {b : Nat} (h : Runs (checkDef d) st b () st') :
    st'.inds = st.inds ∧ ∃ g, st'.globals = st.globals ++ [g] := by
  have hET : ∀ (G : Tab) (f : Nat) (t : Term), GrowsIn G (Ochr.evalType f t) := fun G f => (machineGrows f).evalType
  have hEv : ∀ (G : Tab) (f : Nat) (typed : Bool) (t : Term) (hint : Option Value), GrowsIn G (Ochr.eval f typed t hint) :=
    fun G f => (machineGrows f).eval
  have hCv : ∀ (G : Tab) (f : Nat) (v w : Value), GrowsIn G (Ochr.conv f v w) := fun G f => (machineGrows f).conv
  have hBR : ∀ (G : Tab) (f : Nat) (what : String) (v T : Value) (lent : List Place) (lw : String),
      GrowsIn G (Ochr.bodyReturns f what v T lent lw) := fun G f => (machineGrows f).bodyReturns
  have hCF : ∀ (G : Tab) (f : Nat) (fv : Value) (cs : List Value) (t : Term) (capRec : Array (Option Nat))
      (rd : List (DeclInfo × Value)), GrowsIn G (Ochr.checkFix f fv cs t capRec rd) := fun G f => (machineGrows f).checkFix
  unfold checkDef at h
  dsimp (config := { proj := false }) only at h
  obtain ⟨c, s₁, b₁, hd, h⟩ := Runs.bind_inv h
  obtain ⟨-, hs₁⟩ := runs_declared_inv hd
  subst hs₁
  clear hd
  cases c
  case true =>
    rw [if_pos rfl] at h
    obtain ⟨_, _, _, he, _⟩ := Runs.bind_inv h; exact (runs_err_false he).elim
  rw [if_neg Bool.false_ne_true] at h
  by_cases hm : (d.cod :: d.doms).any (Term.mentionsConst d.name) = true
  · rw [if_pos hm] at h
    obtain ⟨_, _, _, he, _⟩ := Runs.bind_inv h; exact (runs_err_false he).elim
  rw [if_neg hm] at h
  by_cases hr : (!((d.cod :: d.doms).all Term.refTopOk && d.body.refsOk)) = true
  · rw [if_pos hr] at h
    obtain ⟨_, _, _, he, _⟩ := Runs.bind_inv h; exact (runs_err_false he).elim
  rw [if_neg hr] at h
  obtain ⟨_, s₂, b₂, hg₂, h⟩ := Runs.grows_bind (fun G => by grows_goI) h
  obtain ⟨_, s₃, b₃, hg₃, h⟩ := Runs.grows_bind (fun G => by grows_goI) h
  obtain ⟨_, s₄, b₄, hg₄, h⟩ := Runs.grows_bind (fun G => by grows_goI) h
  have h₀ : TablesGrow s₁ s₄ := (hg₂.trans hg₃).trans hg₄
  clear hg₂ hg₃ hg₄
  by_cases he : d.doms.isEmpty = true
  · rw [if_pos he, runs_modify_bind] at h
    obtain ⟨_, s₅, b₅, hg₅, h⟩ := Runs.grows_bind (fun G => by grows_goI) h
    obtain ⟨_, s₆, b₆, hg₆, h⟩ := Runs.grows_bind (fun G => by grows_goI) h
    obtain ⟨_, s₇, b₇, hg₇, h⟩ := Runs.grows_bind (fun G => by grows_goI) h
    obtain ⟨_, s₈, b₈, hg₈, h⟩ := Runs.grows_bind (fun G => by grows_goI) h
    obtain ⟨_, s₉, b₉, hg₉, h⟩ := Runs.grows_bind (fun G => by grows_goI) h
    obtain ⟨_, s₁₀, b₁₀, hg₁₀, h⟩ := Runs.grows_bind (fun G => by grows_goI) h
    obtain ⟨_, s₁₁, b₁₁, hg₁₁, h⟩ := Runs.grows_bind (fun G => by grows_goI) h
    obtain ⟨_, s₁₂, b₁₂, hg₁₂, h⟩ := Runs.grows_bind (fun G => by grows_goI) h
    obtain ⟨c, s₁₃, b₁₃, hg₁₃, h⟩ := Runs.grows_bind (fun G => by grows_goI) h
    have hT : TablesGrow s₁ s₁₃ := by
      refine h₀.trans (TablesGrow.trans ?_ ((((((((hg₅.trans hg₆).trans hg₇).trans hg₈).trans hg₉).trans hg₁₀).trans
        hg₁₁).trans hg₁₂).trans hg₁₃))
      exact ⟨rfl, rfl, Nat.le_refl _, fun _ _ => rfl, Nat.le_refl _, Nat.le_refl _⟩
    clear hg₅ hg₆ hg₇ hg₈ hg₉ hg₁₀ hg₁₁ hg₁₂ hg₁₃ h₀
    cases c
    all_goals first | rw [if_pos rfl] at h | rw [if_neg Bool.false_ne_true] at h
    all_goals
      rw [runs_pure_bind', runs_get_bind] at h
      obtain ⟨_, s₁₄, b₁₄, hg₁₄, h⟩ := Runs.grows_bind (fun G => by grows_goI) h
      have hst := runs_modify_inv h
      subst hst
      exact ⟨hg₁₄.inds.trans hT.inds, _, by rw [hg₁₄.globals, hT.globals]⟩
  · rw [if_neg he] at h
    -- main's D147: the global is appended before the check with `by`, after it without (in each branch of the model
    -- flag, which the `do` block's continuation is copied into)
    by_cases hi : d.implBy.isSome = true
    · rw [if_pos hi, runs_pure_bind'] at h
      have h₅ : TablesGrow s₁ s₄ := h₀
      clear h₀
      by_cases hds : d.dec.isSome = true
      · rw [if_pos hds, runs_modify_bind] at h
        have hn : ¬ d.dec.isNone = true := by
            intro hn'; cases e : d.dec with | none => (rw [e] at hds; cases hds) | some _ => (rw [e] at hn'; cases hn')
        obtain ⟨_, s₆, b₆, hg₆, h⟩ := Runs.grows_bind (fun G => by grows_goI) h
        obtain ⟨_, s₇, b₇, hg₇, h⟩ := Runs.grows_bind (fun G => by grows_goI) h
        obtain ⟨_, s₈, b₈, hg₈, h⟩ := Runs.grows_bind (fun G => by grows_goI) h
        obtain ⟨_, s₉, b₉, hg₉, h⟩ := Runs.grows_bind (fun G => by grows_goI) h
        rw [if_neg hn] at h
        obtain ⟨_, rfl⟩ := runs_pure_inv h
        have hT := ((hg₆.trans hg₇).trans hg₈).trans hg₉
        exact ⟨hT.inds.trans h₅.inds, _, by rw [hT.globals]; show s₄.globals ++ _ = _; rw [h₅.globals]⟩
      · rw [if_neg hds] at h
        have hn : d.dec.isNone = true := by
            cases e : d.dec with | none => rfl | some _ => (rw [e] at hds; exact absurd rfl hds)
        obtain ⟨_, s₆, b₆, hg₆, h⟩ := Runs.grows_bind (fun G => by grows_goI) h
        obtain ⟨_, s₇, b₇, hg₇, h⟩ := Runs.grows_bind (fun G => by grows_goI) h
        obtain ⟨_, s₈, b₈, hg₈, h⟩ := Runs.grows_bind (fun G => by grows_goI) h
        obtain ⟨_, s₉, b₉, hg₉, h⟩ := Runs.grows_bind (fun G => by grows_goI) h
        rw [if_pos hn] at h
        have hst := runs_modify_inv h
        subst hst
        have hT := (((h₅.trans hg₆).trans hg₇).trans hg₈).trans hg₉
        exact ⟨hT.inds, _, by show s₉.globals ++ _ = _; rw [hT.globals]⟩
    · rw [if_neg hi] at h
      obtain ⟨model, s₅, b₅, hg₅, h⟩ := Runs.grows_bind (fun G => by grows_goI) h
      have h₅ : TablesGrow s₁ s₅ := h₀.trans hg₅
      clear hg₅ h₀
      cases model
      · by_cases hds : d.dec.isSome = true
        · rw [if_pos hds, runs_modify_bind] at h
          have hn : ¬ d.dec.isNone = true := by
            intro hn'; cases e : d.dec with | none => (rw [e] at hds; cases hds) | some _ => (rw [e] at hn'; cases hn')
          simp only [hn, Bool.false_eq_true, if_false, ↓reduceIte] at h
          have hT := Runs.grows (growsM_of_growsIn fun G => by grows_goI) h
          exact ⟨hT.inds.trans h₅.inds, _, by rw [hT.globals]; show s₅.globals ++ _ = _; rw [h₅.globals]⟩
        · rw [if_neg hds] at h
          have hn : d.dec.isNone = true := by
            cases e : d.dec with | none => rfl | some _ => (rw [e] at hds; exact absurd rfl hds)
          simp only [hn, Bool.false_eq_true, if_false, if_true, ↓reduceIte] at h
          obtain ⟨_, s₆, b₆, hg₆, h⟩ := Runs.grows_bind (fun G => by grows_goI) h
          obtain ⟨_, s₇, b₇, hg₇, h⟩ := Runs.grows_bind (fun G => by grows_goI) h
          have hst := runs_modify_inv h
          subst hst
          have hT := (h₅.trans hg₆).trans hg₇
          exact ⟨hT.inds, _, by show s₇.globals ++ _ = _; rw [hT.globals]⟩
      · by_cases hds : d.dec.isSome = true
        · rw [if_pos hds, runs_modify_bind] at h
          have hn : ¬ d.dec.isNone = true := by
            intro hn'; cases e : d.dec with | none => (rw [e] at hds; cases hds) | some _ => (rw [e] at hn'; cases hn')
          obtain ⟨_, s₆, b₆, hg₆, h⟩ := Runs.grows_bind (fun G => by grows_goI) h
          obtain ⟨_, s₇, b₇, hg₇, h⟩ := Runs.grows_bind (fun G => by grows_goI) h
          obtain ⟨_, s₈, b₈, hg₈, h⟩ := Runs.grows_bind (fun G => by grows_goI) h
          obtain ⟨_, s₉, b₉, hg₉, h⟩ := Runs.grows_bind (fun G => by grows_goI) h
          rw [if_neg hn] at h
          obtain ⟨_, rfl⟩ := runs_pure_inv h
          have hT := ((hg₆.trans hg₇).trans hg₈).trans hg₉
          exact ⟨hT.inds.trans h₅.inds, _, by rw [hT.globals]; show s₅.globals ++ _ = _; rw [h₅.globals]⟩
        · rw [if_neg hds] at h
          have hn : d.dec.isNone = true := by
            cases e : d.dec with | none => rfl | some _ => (rw [e] at hds; exact absurd rfl hds)
          obtain ⟨_, s₆, b₆, hg₆, h⟩ := Runs.grows_bind (fun G => by grows_goI) h
          obtain ⟨_, s₇, b₇, hg₇, h⟩ := Runs.grows_bind (fun G => by grows_goI) h
          obtain ⟨_, s₈, b₈, hg₈, h⟩ := Runs.grows_bind (fun G => by grows_goI) h
          obtain ⟨_, s₉, b₉, hg₉, h⟩ := Runs.grows_bind (fun G => by grows_goI) h
          rw [if_pos hn] at h
          have hst := runs_modify_inv h
          subst hst
          have hT := (((h₅.trans hg₆).trans hg₇).trans hg₈).trans hg₉
          exact ⟨hT.inds, _, by show s₉.globals ++ _ = _; rw [hT.globals]⟩

/-- `seedHoles` writes only the unknowns' tables. -/
theorem runs_seedHoles_tables {st st' : MState} {b : Nat} (h : Runs seedHoles st b () st') :
    st'.globals = st.globals ∧ st'.inds = st.inds := by
  unfold seedHoles at h
  rw [runs_get_bind] at h
  dsimp (config := { proj := false }) only at h
  by_cases hc : ((st.globals.flatMap (·.absTys)).isEmpty || st.nextAbs != 0) = true
  · rw [if_pos hc] at h
    obtain ⟨_, rfl⟩ := runs_pure_inv h
    exact ⟨rfl, rfl⟩
  · rw [if_neg hc] at h
    obtain ⟨_, s₁, b₁, h₁, h⟩ := Runs.bind_inv h
    have := runs_keep (by keep_go) h₁
    subst this
    obtain ⟨_, s₂, b₂, h₂, h⟩ := Runs.bind_inv h
    have := runs_keep (by keep_go) h₂
    subst this
    obtain ⟨L, left, log, h⟩ := h
    simp only [runMachineL_set, Prod.mk.injEq, Outcome.ok.injEq] at h
    rw [← h.1.2]
    exact ⟨rfl, rfl⟩

/-- A run of the top-level machine is a `Runs`. -/
theorem runs_of_runMachine_fst {α : Type} {f : M α} {st : MState} {fuel : Nat} {a : α} {st' : MState}
    (h : (runMachine f st fuel).1 = .ok a st') : Runs f st fuel a st' := by
  have e : runMachine f st fuel = ((runMachine f st fuel).1, (runMachine f st fuel).2.1, (runMachine f st fuel).2.2) := rfl
  rw [h] at e
  exact Runs.of_runMachine e

/-- **What an accepted item does to the declarations and the globals** (the parts of `ItemFacts` that read
`Check.lean` alone; PROVED): a declaration `d` appends `d` with the nestable set computed from the
declarations before it and leaves the globals; a definition leaves the declarations and appends one global. -/
theorem checkItem_tables (it : Item) (st st' : MState) (fuel : Nat) (h : (runMachine (checkItem it) st fuel).1 = .ok () st') :
    (∀ d, it = .ind d → st'.inds = st.inds ++ [{ d with nestable := nestableSet (nestTableOf st.inds) (sortTableOf st.inds d) d }] ∧
      st'.globals = st.globals) ∧
    (∀ d, it = .defn d → st'.inds = st.inds ∧ ∃ g, st'.globals = st.globals ++ [g]) := by
  have hr := runs_of_runMachine_fst h
  refine ⟨fun d hd => ?_, fun d hd => ?_⟩
  all_goals subst hd
  all_goals
    unfold checkItem at hr
    obtain ⟨_, s₁, b₁, h₁, h₂⟩ := Runs.bind_inv hr
    obtain ⟨hg, hi⟩ := runs_seedHoles_tables h₁
  · obtain ⟨hg', hi'⟩ := runs_checkInd_tables h₂
    rw [hi', hg', hi, hg]
    exact ⟨rfl, rfl⟩
  · obtain ⟨hi', g, hg'⟩ := runs_checkDef_tables h₂
    exact ⟨hi'.trans hi, g, by rw [hg', hg]⟩

/-- Along the items the declarations only grow at the end. -/
theorem sigAfterFrom_prefix (cfg : Config) (fuel : Nat) :
    ∀ (items : List Item) (start : List GDef × List IndDecl), start.2 <+: (sigAfterFrom cfg fuel start items).2
  | [], _ => List.prefix_refl _
  | it :: items, start => by
    unfold sigAfterFrom
    rw [List.foldl_cons]
    refine List.IsPrefix.trans ?_ (sigAfterFrom_prefix cfg fuel items _)
    split
    · rename_i st' hst
      obtain ⟨hI, hD⟩ := checkItem_tables it _ st' fuel hst
      cases it with
      | ind d => rw [(hI d rfl).1]; exact List.prefix_append _ _
      | defn d => rw [(hD d rfl).1]; exact List.prefix_refl _
    · exact List.prefix_refl _

/-- **The stage prefix fact** (`Consistency.inds_prefix`'s conclusion, with no hypothesis): every stage's
declarations are a prefix of the whole program's. -/
theorem indsOf_take_prefix (cfg : Config) (fuel : Nat) (items : List Item) (k : Nat) :
    indsOf cfg fuel (items.take k) <+: indsOf cfg fuel items := by
  unfold indsOf
  conv => rhs; rw [← List.take_append_drop k items]
  unfold sigAfterFrom
  rw [List.foldl_append]
  exact sigAfterFrom_prefix cfg fuel (items.drop k) _

end Ochr.Meaning.Steps.Machine
