import Ochr.Meaning.Steps.Machine.BorrowRead
import Ochr.Meaning.DataModel.Exists.FrameLocal.Setup
import Ochr.Meaning.DecisionsFF

/-!
# `DecLocal.join`, proved (machine11)

`FrameLocal.DecLocal.join` (`DataModel/Exists/FrameLocal/Setup.lean`): every place the decisions' join gives for a term
at an entry is in the entry or rooted at a free variable of the term. True since main's D129, which carries the
entry's places as they are (before it, `jdMatch` re-grained them, `FactsCE`'s historical note).

The invariant of `jdMoves`/`jdMovesList`/`jdMatch` (`jd_local`): at `n` binders crossed (`sc`, with the local borrows
`al` beside them), every place of the result is in the incoming `acc` or its root is `RootOk n al O`: the frame index
of a free occurrence in `O`, a set of occurrences containing the term's, or the root of a local borrow's place. Each
place the code adds is a free occurrence resolved (`jdResolve`), a capture variable (`fnOccs`), a borrow variable
(`blockOccs`), a whole place the match uses (`blockOccs`), or a prefix of one of these at the same root (`jdGrain`).
-/

namespace Ochr.Meaning.Steps.Machine

open Ochr Ochr.Meaning Ochr.Meaning.Steps

/-! ## Runs that return what a predicate says -/

theorem RetP.mono {α : Type} {P Q : α → Prop} {x : M α} (h : RetP P x) (hPQ : ∀ a, P a → Q a) : RetP Q x := by
  unfold RetP at h ⊢; intro st b a st' hr; exact hPQ _ (h _ _ _ _ hr)

theorem RetP.bind_of {α β : Type} {Q : α → Prop} {P : β → Prop} {x : M α} {f : α → M β} (hx : RetP Q x)
    (h : ∀ a, Q a → RetP P (f a)) : RetP P (x >>= f) := by
  unfold RetP; intro st b y st' hr
  obtain ⟨a, s₁, b₁, h₀, h₁⟩ := Runs.bind_inv hr
  exact (h a (hx.run h₀)).run h₁

theorem RetP.exhausted' {α : Type} {P : α → Prop} {m : String} : RetP P (exhausted m : M α) := by
  unfold RetP; intro st b a st' hr; simp only [runs_exhausted_iff] at hr

theorem RetP.onFail' {α : Type} {P : α → Prop} {x : M α} {c : M Unit} (h : RetP P x) : RetP P (onFail x c) := by
  unfold RetP; intro st b a st' hr; exact h.run (Runs.onFail_inv hr)

theorem RetP.forIn' {α β : Type} (I : β → Prop) {xs : List α} {init : β} {f : α → β → M (ForInStep β)}
    (h0 : I init) (hf : ∀ x ∈ xs, ∀ b, I b → RetP (fun r => I r.value) (f x b)) : RetP I (forIn xs init f) := by
  induction xs generalizing init with
  | nil => rw [List.forIn_nil]; exact RetP.pure' h0
  | cons a as ih =>
    rw [List.forIn_cons]
    refine RetP.bind_of (hf a (List.mem_cons_self ..) init h0) fun r hr => ?_
    cases r with
    | done b => exact RetP.pure' hr
    | yield b => exact ih hr fun x hx b hb => hf x (List.mem_cons_of_mem _ hx) b hb

/-- `withLive` runs its body (the live-scope flag set and restored around it). -/
theorem RetP.withLive' {α : Type} {P : α → Prop} {x : M α} {live : Bool} (h : RetP P x) : RetP P (withLive live x) := by
  unfold withLive
  refine RetP.bind' fun _ => RetP.bind' fun _ => RetP.bind_of (RetP.onFail' h) fun r hr => RetP.bind' fun _ => RetP.pure' hr

/-- The walk of a run's code, goal first (`BorrowRead.lean`'s): binds (the continuation at every value), `err`,
branches, `dsimp`; each `pure` is left for the caller. -/
macro "retp_walk" : tactic => `(tactic| repeat (any_goals first
    | (with_reducible apply RetP.err_bind)
    | (with_reducible apply RetP.err')
    | (with_reducible apply RetP.exhausted')
    | (with_reducible apply RetP.pure')
    | (apply RetP.ite' <;> intro _)
    | (apply RetP.dite' <;> intro _)
    | (with_reducible apply RetP.bind'; intro _)
    | (dsimp only)
    | (split)))

/-! ## The places the join adds -/

theorem root_jdExtend (q : Place) (ss : List Step) : (jdExtend q ss).root = q.root := by
  rw [← DataModel.Exists.FrameLocal.steps_fst, jdExtend_steps, DataModel.Exists.FrameLocal.steps_fst]

theorem mem_jdAdd {acc : List Place} {p q : Place} (h : q ∈ jdAdd acc p) : q ∈ acc ∨ q = p := by
  unfold jdAdd at h
  split at h
  · exact .inl h
  · rcases List.mem_append.mp h with h | h
    · exact .inl (List.mem_filter.mp h).1
    · exact .inr (List.mem_singleton.mp h)

theorem mem_jdRefill {acc : List Place} {p q : Place} (h : q ∈ jdRefill acc p) : q ∈ acc := by
  unfold jdRefill at h; exact (List.mem_filter.mp h).1

/-- **The grain of a move keeps its root**: `jdGrain` returns a prefix of the place, at its root. -/
theorem retP_jdGrain (n : Nat) (m : Place) : RetP (fun r : Place => r.root = m.root) (Ochr.jdGrain n m) := by
  cases n with
  | zero => unfold Ochr.jdGrain; exact RetP.exhausted'
  | succ n =>
  unfold Ochr.jdGrain
  dsimp only
  refine RetP.bind_of (RetP.forIn' (fun s : Option Place × Place => (∀ r, s.1 = some r → r.root = m.root) ∧
      s.2.root = m.root) ⟨fun r h => (by cases h), (by simp [Place.root, DataModel.Exists.FrameLocal.steps_fst])⟩ ?_)
    fun s hs => ?_
  · intro x _ s hs
    retp_walk
    all_goals simp_all [ForInStep.value, root_jdExtend]
  · retp_walk
    all_goals simp_all

/-! ## The occurrences the join reads are the term's -/

/-- An occurrence's depth and place. -/
def pk (x : Nat × Place × PKind) : Nat × Place := (x.1, x.2.1)

mutual
theorem blockOccs_pk : ∀ (t : Term) (inFn : Bool) (c : Nat), (t.blockOccs inFn c).map pk = (t.placeOccs c).map pk
  | t, inFn, c => by
    cases t with
    | place p => simp [Term.blockOccs, Term.placeOccs, pk]
    | borrow p => simp [Term.blockOccs, Term.placeOccs, pk]
    | assign p u => simp [Term.blockOccs, Term.placeOccs, blockOccs_pk u inFn c, pk]
    | letIn h u v => simp only [Term.blockOccs, Term.placeOccs, List.map_append, blockOccs_pk u inFn c, blockOccs_pk v inFn (c + 1)]
    | seq u v => simp only [Term.blockOccs, Term.placeOccs, List.map_append, blockOccs_pk u inFn c, blockOccs_pk v inFn c]
    | matchNat p z s => simp only [Term.blockOccs, Term.placeOccs, List.map_append, List.map_cons, blockOccs_pk z inFn c, blockOccs_pk s inFn c]
    | pi hs ds cod => simp only [Term.blockOccs, Term.placeOccs, List.map_append, blockOccsDoms_pk ds c, blockOccs_pk cod true (c + ds.length)]
    | «fix» f hs ds cod d b => simp only [Term.blockOccs, Term.placeOccs, List.map_append, blockOccsDoms_pk ds c, blockOccs_pk cod true (c + ds.length), blockOccs_pk b true (c + ds.length + 1)]
    | call g as h => simp only [Term.blockOccs, Term.placeOccs, List.map_append, blockOccs_pk g inFn c, blockOccsList_pk as inFn c]
    | succ u => simp only [Term.blockOccs, Term.placeOccs, blockOccs_pk u inFn c]
    | ref u => simp only [Term.blockOccs, Term.placeOccs, blockOccs_pk u inFn c]
    | cong a b => simp only [Term.blockOccs, Term.placeOccs, List.map_append, blockOccs_pk a inFn c, blockOccs_pk b inFn c]
    | ascribe a b => simp only [Term.blockOccs, Term.placeOccs, List.map_append, blockOccs_pk a inFn c, blockOccs_pk b inFn c]
    | eq a b d => simp only [Term.blockOccs, Term.placeOccs, List.map_append, blockOccs_pk a inFn c, blockOccs_pk b inFn c, blockOccs_pk d inFn c]
    | id a b d => simp only [Term.blockOccs, Term.placeOccs, List.map_append, blockOccs_pk a inFn c, blockOccs_pk b inFn c, blockOccs_pk d inFn c]
    | ctor ty k h ps as => simp only [Term.blockOccs, Term.placeOccs, List.map_append, blockOccsList_pk ps inFn c, blockOccsList_pk as inFn c]
    | prim nm as => simp only [Term.blockOccs, Term.placeOccs, blockOccsList_pk as inFn c]
    | tind nm as => simp only [Term.blockOccs, Term.placeOccs, blockOccsList_pk as inFn c]
    | matchInd p ty as => simp only [Term.blockOccs, Term.placeOccs, List.map_cons, blockOccsArms_pk as inFn c]
    | _ => simp [Term.blockOccs, Term.placeOccs]

theorem blockOccsList_pk : ∀ (ts : List Term) (inFn : Bool) (c : Nat),
    (Term.blockOccsList inFn c ts).map pk = (Term.placeOccsList c ts).map pk
  | [], _, _ => rfl
  | t :: ts, inFn, c => by
    simp only [Term.blockOccsList, Term.placeOccsList, List.map_append, blockOccs_pk t inFn c, blockOccsList_pk ts inFn c]

theorem blockOccsDoms_pk : ∀ (ts : List Term) (c : Nat),
    (Term.blockOccsDoms c ts).map pk = (Term.placeOccsDoms c ts).map pk
  | [], _ => rfl
  | t :: ts, c => by
    simp only [Term.blockOccsDoms, Term.placeOccsDoms, List.map_append, blockOccs_pk t true c, blockOccsDoms_pk ts (c + 1)]

theorem blockOccsArms_pk : ∀ (ts : List (Hint × Term)) (inFn : Bool) (c : Nat),
    (Term.blockOccsArms inFn c ts).map pk = (Term.placeOccsArms c ts).map pk
  | [], _, _ => rfl
  | (h, t) :: ts, inFn, c => by
    simp only [Term.blockOccsArms, Term.placeOccsArms, List.map_append, blockOccs_pk t inFn c, blockOccsArms_pk ts inFn c]
end

/-- A `blockOccs` occurrence is a `placeOccs` occurrence (its kind aside). -/
theorem blockOccs_sub {t : Term} {inFn : Bool} {c d : Nat} {p : Place} {k : PKind} (h : (d, p, k) ∈ t.blockOccs inFn c) :
    ∃ k', (d, p, k') ∈ t.placeOccs c := by
  have : (d, p) ∈ (t.placeOccs c).map pk := by rw [← blockOccs_pk]; exact List.mem_map.mpr ⟨_, h, rfl⟩
  obtain ⟨⟨d', p', k'⟩, hm, he⟩ := List.mem_map.mp this
  simp only [pk, Prod.mk.injEq] at he
  obtain ⟨rfl, rfl⟩ := he
  exact ⟨k', hm⟩

/-- What a capture occurrence is: a free occurrence of the term, at its frame index. -/
def FnOk (t : Term) (c o : Nat) (p : Place) : Prop := ∃ d k, (d, p, k) ∈ t.placeOccs c ∧ d ≤ p.root ∧ o = p.root - d

theorem fnOk_of_block {t : Term} {inFn : Bool} {c o d : Nat} {p : Place} {k : PKind}
    (h : (d, p, k) ∈ t.blockOccs inFn c) (hd : d ≤ p.root) (ho : o = p.root - d) : FnOk t c o p := by
  obtain ⟨k', hk⟩ := blockOccs_sub h
  exact ⟨d, k', hk, hd, ho⟩

theorem FnOk.mono {t u : Term} {c c' o : Nat} {p : Place} (h : FnOk t c o p)
    (hs : ∀ x, x ∈ t.placeOccs c → x ∈ u.placeOccs c') : FnOk u c' o p := by
  obtain ⟨d, k, hm, hd, he⟩ := h
  exact ⟨d, k, hs _ hm, hd, he⟩

/-- `FnOk` over a list of occurrences. -/
def FnOkL (L : List (Nat × Place × PKind)) (o : Nat) (p : Place) : Prop := ∃ d k, (d, p, k) ∈ L ∧ d ≤ p.root ∧ o = p.root - d

theorem FnOkL.mono {L : List (Nat × Place × PKind)} {u : Term} {c' o : Nat} {p : Place} (h : FnOkL L o p)
    (hs : ∀ x, x ∈ L → x ∈ u.placeOccs c') : FnOk u c' o p := by
  obtain ⟨d, k, hm, hd, he⟩ := h
  exact ⟨d, k, hs _ hm, hd, he⟩

mutual
theorem fnOccs_ok : ∀ (t : Term) (c o : Nat) (p : Place), (o, p) ∈ t.fnOccs c → FnOk t c o p
  | t, c, o, p, h => by
    cases t with
    | pi hs ds cod =>
      simp only [Term.fnOccs, List.mem_filterMap] at h
      obtain ⟨⟨d, q, k⟩, hm, he⟩ := h
      dsimp only at he
      split at he
      · cases he; exact fnOk_of_block hm (by omega) rfl
      · cases he
    | «fix» f hs ds cod dd b =>
      simp only [Term.fnOccs, List.mem_filterMap] at h
      obtain ⟨⟨d, q, k⟩, hm, he⟩ := h
      dsimp only at he
      split at he
      · cases he; exact fnOk_of_block hm (by omega) rfl
      · cases he
    | letIn h u v =>
      simp only [Term.fnOccs, List.mem_append] at h
      rcases h with h | h
      · exact (fnOccs_ok u c o p h).mono fun x hx => by simp [Term.placeOccs, hx]
      · exact (fnOccs_ok v (c + 1) o p h).mono fun x hx => by simp [Term.placeOccs, hx]
    | assign q u => exact (fnOccs_ok u c o p h).mono fun x hx => by simp [Term.placeOccs, hx]
    | succ u => exact (fnOccs_ok u c o p h).mono fun x hx => by simp [Term.placeOccs, hx]
    | ref u => exact (fnOccs_ok u c o p h).mono fun x hx => by simp [Term.placeOccs, hx]
    | seq u v =>
      simp only [Term.fnOccs, List.mem_append] at h
      rcases h with h | h
      · exact (fnOccs_ok u c o p h).mono fun x hx => by simp [Term.placeOccs, hx]
      · exact (fnOccs_ok v c o p h).mono fun x hx => by simp [Term.placeOccs, hx]
    | cong u v =>
      simp only [Term.fnOccs, List.mem_append] at h
      rcases h with h | h
      · exact (fnOccs_ok u c o p h).mono fun x hx => by simp [Term.placeOccs, hx]
      · exact (fnOccs_ok v c o p h).mono fun x hx => by simp [Term.placeOccs, hx]
    | ascribe u v =>
      simp only [Term.fnOccs, List.mem_append] at h
      rcases h with h | h
      · exact (fnOccs_ok u c o p h).mono fun x hx => by simp [Term.placeOccs, hx]
      · exact (fnOccs_ok v c o p h).mono fun x hx => by simp [Term.placeOccs, hx]
    | matchNat q u v =>
      simp only [Term.fnOccs, List.mem_append] at h
      rcases h with h | h
      · exact (fnOccs_ok u c o p h).mono fun x hx => by simp [Term.placeOccs, hx]
      · exact (fnOccs_ok v c o p h).mono fun x hx => by simp [Term.placeOccs, hx]
    | call g as hd =>
      simp only [Term.fnOccs, List.mem_append] at h
      rcases h with h | h
      · exact (fnOccs_ok g c o p h).mono fun x hx => by simp [Term.placeOccs, hx]
      · exact (fnOccsList_ok as c o p h).mono fun x hx => by simp [Term.placeOccs, hx]
    | eq a b d =>
      simp only [Term.fnOccs, List.mem_append] at h
      rcases h with (h | h) | h
      · exact (fnOccs_ok a c o p h).mono fun x hx => by simp [Term.placeOccs, hx]
      · exact (fnOccs_ok b c o p h).mono fun x hx => by simp [Term.placeOccs, hx]
      · exact (fnOccs_ok d c o p h).mono fun x hx => by simp [Term.placeOccs, hx]
    | id a b d =>
      simp only [Term.fnOccs, List.mem_append] at h
      rcases h with (h | h) | h
      · exact (fnOccs_ok a c o p h).mono fun x hx => by simp [Term.placeOccs, hx]
      · exact (fnOccs_ok b c o p h).mono fun x hx => by simp [Term.placeOccs, hx]
      · exact (fnOccs_ok d c o p h).mono fun x hx => by simp [Term.placeOccs, hx]
    | ctor ty k hh ps as =>
      simp only [Term.fnOccs, List.mem_append] at h
      rcases h with h | h
      · exact (fnOccsList_ok ps c o p h).mono fun x hx => by simp [Term.placeOccs, hx]
      · exact (fnOccsList_ok as c o p h).mono fun x hx => by simp [Term.placeOccs, hx]
    | prim nm as => exact (fnOccsList_ok as c o p h).mono fun x hx => by simp [Term.placeOccs, hx]
    | tind nm as => exact (fnOccsList_ok as c o p h).mono fun x hx => by simp [Term.placeOccs, hx]
    | matchInd q ty as => exact (fnOccsArms_ok as c o p h).mono fun x hx => by simp [Term.placeOccs, hx]
    | _ => simp [Term.fnOccs] at h

theorem fnOccsList_ok : ∀ (ts : List Term) (c o : Nat) (p : Place), (o, p) ∈ Term.fnOccsList c ts →
    FnOkL (Term.placeOccsList c ts) o p
  | [], _, _, _, h => by simp [Term.fnOccsList] at h
  | t :: ts, c, o, p, h => by
    simp only [Term.fnOccsList, List.mem_append] at h
    rcases h with h | h
    · obtain ⟨d, k, hm, hd, he⟩ := fnOccs_ok t c o p h
      exact ⟨d, k, by simp [Term.placeOccsList, hm], hd, he⟩
    · obtain ⟨d, k, hm, hd, he⟩ := fnOccsList_ok ts c o p h
      exact ⟨d, k, by simp [Term.placeOccsList, hm], hd, he⟩

theorem fnOccsArms_ok : ∀ (ts : List (Hint × Term)) (c o : Nat) (p : Place), (o, p) ∈ Term.fnOccsArms c ts →
    FnOkL (Term.placeOccsArms c ts) o p
  | [], _, _, _, h => by simp [Term.fnOccsArms] at h
  | (hh, t) :: ts, c, o, p, h => by
    simp only [Term.fnOccsArms, List.mem_append] at h
    rcases h with h | h
    · obtain ⟨d, k, hm, hd, he⟩ := fnOccs_ok t c o p h
      exact ⟨d, k, by simp [Term.placeOccsArms, hm], hd, he⟩
    · obtain ⟨d, k, hm, hd, he⟩ := fnOccsArms_ok ts c o p h
      exact ⟨d, k, by simp [Term.placeOccsArms, hm], hd, he⟩
end

/-! ## The invariant -/

/-- A root the join may add at `n` binders crossed: the frame index of a free occurrence in `O`, or the root of a
local borrow's place (`al`). -/
def RootOk (n : Nat) (al : List (Option Place)) (O : Nat → Place → Prop) (r : Nat) : Prop :=
  (∃ d p, O d p ∧ d + n ≤ p.root ∧ r = p.root - d - n) ∨ (∃ q, some q ∈ al ∧ q.root = r)

/-- `O` holds every occurrence of `t` (at depth 0). -/
def OccsIn (t : Term) (O : Nat → Place → Prop) : Prop := ∀ d p k, (d, p, k) ∈ t.placeOccs 0 → O d p

/-- Every place of `ms` is in `acc` or at an allowed root. -/
def JOk (n : Nat) (al : List (Option Place)) (O : Nat → Place → Prop) (acc ms : List Place) : Prop :=
  ∀ q ∈ ms, q ∈ acc ∨ RootOk n al O q.root

section
variable {n : Nat} {al : List (Option Place)} {O : Nat → Place → Prop}

theorem JOk.refl (acc : List Place) : JOk n al O acc acc := fun q h => .inl h

theorem JOk.trans {a b c : List Place} (h₁ : JOk n al O a b) (h₂ : JOk n al O b c) : JOk n al O a c := by
  intro q hq
  rcases h₂ q hq with h | h
  · exact h₁ q h
  · exact .inr h

theorem JOk.bind {acc : List Place} {x : M (List Place)} {g : List Place → M (List Place)}
    (hx : RetP (JOk n al O acc) x) (hg : ∀ a, JOk n al O acc a → RetP (JOk n al O a) (g a)) :
    RetP (JOk n al O acc) (x >>= g) :=
  RetP.bind_of hx fun a ha => (hg a ha).mono fun _ h => ha.trans h

theorem JOk.add {acc : List Place} {q : Place} (hq : RootOk n al O q.root) : JOk n al O acc (jdAdd acc q) := by
  intro x hx
  rcases mem_jdAdd hx with h | rfl
  · exact .inl h
  · exact .inr hq

theorem JOk.refill {acc : List Place} {q : Place} : JOk n al O acc (jdRefill acc q) := fun _ hx => .inl (mem_jdRefill hx)

theorem OccsIn.sub {t u : Term} (h : OccsIn t O) (hs : ∀ x, x ∈ u.placeOccs 0 → x ∈ t.placeOccs 0) : OccsIn u O :=
  fun d p k hm => h d p k (hs _ hm)

end

theorem jdResolve_ok {al : List (Option Place)} {p q : Place} {O : Nat → Place → Prop} (hO : O 0 p)
    (h : jdResolve al p = some q) : RootOk al.length al O q.root := by
  unfold jdResolve at h
  have hr := DataModel.Exists.FrameLocal.steps_fst p
  rcases hs : p.steps with ⟨r, ss⟩
  rw [hs] at hr h
  dsimp only at hr h
  split at h
  · cases h
    rw [root_jdExtend]
    exact .inl ⟨0, p, hO, by simp at *; omega, by simp [Place.root]; omega⟩
  · split at h
    · rename_i _ _ q' rest hq
      cases h
      rw [root_jdExtend]
      exact .inr ⟨q', List.mem_of_getElem? hq, rfl⟩
    · cases h

/-- **The capture variables `jdFns` adds are free occurrences.** -/
theorem retP_jdFns (f : Nat) (sc : List DeclInfo) (al : List (Option Place)) (t : Term) (acc : List Place)
    {O : Nat → Place → Prop} (hO : OccsIn t O) : RetP (JOk sc.length al O acc) (jdFns f sc t acc) := by
  cases f with
  | zero => unfold jdFns; exact RetP.exhausted'
  | succ f =>
  unfold jdFns
  dsimp only
  refine RetP.bind_of (RetP.forIn' (JOk sc.length al O acc) (JOk.refl acc) ?_) fun a ha => RetP.pure' ha
  intro x hx b hb
  obtain ⟨o, q⟩ := x
  obtain ⟨d, k, hm, hd, he⟩ := fnOccs_ok t 0 o q hx
  retp_walk
  all_goals first
    | exact hb
    | (refine hb.trans (JOk.add ?_)
       exact .inl ⟨d, q, hO d q k hm, by omega, by simp only [Place.root]; omega⟩)

/-! ## The join of a match -/

theorem JOk.add' {n : Nat} {al : List (Option Place)} {O : Nat → Place → Prop} {acc s : List Place} {q : Place}
    (hs : JOk n al O acc s) (hq : q ∈ acc ∨ RootOk n al O q.root) : JOk n al O acc (jdAdd s q) := by
  intro x hx
  rcases mem_jdAdd hx with h | rfl
  · exact hs x h
  · exact hq

theorem root_mapRoot (f : Nat → Place) : ∀ q : Place, (q.mapRoot f).root = (f q.root).root
  | .var _ => rfl
  | .deref q | .proj _ q | .field _ q => by simp only [Place.mapRoot, Place.root]; exact root_mapRoot f q

theorem Place.beq_refl : ∀ p : Place, Place.beq p p = true
  | .var i => by simp [Place.beq]
  | .deref p => by simp only [Place.beq]; exact Place.beq_refl p
  | .proj i p => by simp only [Place.beq, beq_self_eq_true, Bool.true_and]; exact Place.beq_refl p
  | .field g p => by
    simp only [Place.beq, Bool.and_eq_true]
    exact ⟨by simp [BEq.beq], Place.beq_refl p⟩

theorem contains_of_mem {acc : List Place} {m : Place} (h : m ∈ acc) : acc.contains m = true := by
  rw [List.contains_iff_exists_mem_beq]
  exact ⟨m, h, Place.beq_refl m⟩

/-- A fold that keeps its accumulator or picks the element. -/
theorem foldl_pick {L : List Place} {f : Option Place → Place → Option Place}
    (hf : ∀ b w, f b w = some w ∨ f b w = b) : ∀ (init : Option Place) (x : Place),
    L.foldl f init = some x → x ∈ L ∨ init = some x := by
  induction L with
  | nil => intro init x h; exact .inr h
  | cons a as ih =>
    intro init x h
    rw [List.foldl_cons] at h
    rcases ih _ x h with h' | h'
    · exact .inl (List.mem_cons_of_mem _ h')
    · rcases hf init a with e | e <;> rw [e] at h'
      · cases h'; exact .inl (List.mem_cons_self ..)
      · exact .inr h'

theorem retP_jdMatch_succ (f : Nat)
    (ihM : ∀ sc al t acc (O : Nat → Place → Prop), al.length = sc.length → OccsIn t O →
      RetP (JOk sc.length al O acc) (jdMoves f sc al t acc))
    (sc : List DeclInfo) (al : List (Option Place)) (t : Term) (arms : List Term) (acc : List Place)
    (O : Nat → Place → Prop) (hl : al.length = sc.length) (hO : OccsIn t O) (hA : ∀ a ∈ arms, OccsIn a O) :
    RetP (JOk sc.length al O acc) (jdMatch (f + 1) sc al t arms acc) := by
  unfold Ochr.jdMatch
  dsimp only
  refine RetP.bind_of (RetP.forIn' (JOk sc.length al O acc) (fun _ h => by cases h) ?_) fun u1 hu1 => ?_
  · intro a ha s hs
    refine RetP.bind_of (ihM sc al a acc O hl (hA a ha)) fun ms hms => ?_
    refine RetP.bind_of (RetP.forIn' (JOk sc.length al O acc) hs ?_) fun s' hs' => RetP.pure' hs'
    intro m hm s2 hs2
    exact RetP.pure' (JOk.add' hs2 (hms m hm))
  refine RetP.bind_of (retP_jdFns f sc al t u1 hO) fun u2 hu2 => ?_
  refine RetP.bind_of (RetP.forIn' (JOk sc.length al O acc) (hu1.trans hu2) ?_) fun u3 hu3 => ?_
  · intro x hx s hs
    obtain ⟨d, q, k⟩ := x
    obtain ⟨k', hk'⟩ := blockOccs_sub hx
    retp_walk
    all_goals first
      | exact hs
      | (refine JOk.add' hs (.inr (.inl ⟨d, _, hO d _ k' hk', ?_, ?_⟩)) <;> simp_all [Place.root] <;> omega)
  refine RetP.bind_of (RetP.forIn' (JOk sc.length al O acc) (fun _ h => by cases h) ?_) fun g hg => ?_
  · intro m hm s hs
    have hmG := hu3 m hm
    apply RetP.ite' <;> intro hc
    · exact RetP.bind_of (Q := fun x => x = m) (RetP.pure' rfl) fun x hx => RetP.pure' (by subst hx; exact JOk.add' hs hmG)
    · refine RetP.bind_of (retP_jdGrain f m) fun r hr => RetP.pure' (JOk.add' hs ?_)
      rcases hmG with h | h
      · exact absurd (contains_of_mem h) hc
      · exact .inr (hr ▸ h)
  refine RetP.bind_of (RetP.forIn' (fun W : List Place => ∀ w ∈ W, RootOk sc.length al O w.root)
    (fun _ h => by cases h) ?_) fun W hW => ?_
  · intro x hx s hs
    obtain ⟨d, q, k⟩ := x
    obtain ⟨k', hk'⟩ := blockOccs_sub hx
    apply RetP.ite' <;> intro hc
    · refine RetP.pure' ?_
      intro w hw
      rcases List.mem_append.mp hw with h | h
      · exact hs w h
      · rw [List.mem_singleton] at h
        subst h
        simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
        refine .inl ⟨d, q, hO d q k' hk', by omega, ?_⟩
        rw [root_mapRoot]; rfl
    · exact RetP.pure' hs
  refine RetP.bind_of (RetP.forIn' (JOk sc.length al O acc) (fun _ h => by cases h) ?_) fun out hout => RetP.pure' hout
  intro m hm s hs
  split
  · rename_i w hw
    refine RetP.pure' (JOk.add' hs (.inr ?_))
    rcases foldl_pick (fun b w => by cases b <;> simp only [] <;> (try split) <;> simp) none w hw with h | h
    · exact hW w (List.mem_filter.mp h).1
    · cases h
  · exact RetP.pure' (JOk.add' hs (hg m hm))

/-! ## The moves of a term -/

theorem mem_placeOccsList {ts : List Term} {a : Term} {c : Nat} {x : Nat × Place × PKind} (ha : a ∈ ts)
    (hx : x ∈ a.placeOccs c) : x ∈ Term.placeOccsList c ts := by
  induction ts with
  | nil => cases ha
  | cons t ts ih =>
    simp only [Term.placeOccsList, List.mem_append]
    rcases List.mem_cons.mp ha with rfl | h
    · exact .inl hx
    · exact .inr (ih h)

theorem mem_placeOccsArms {ts : List (Hint × Term)} {a : Term} {c : Nat} {x : Nat × Place × PKind}
    (ha : a ∈ ts.map (·.2)) (hx : x ∈ a.placeOccs c) : x ∈ Term.placeOccsArms c ts := by
  induction ts with
  | nil => cases ha
  | cons t ts ih =>
    obtain ⟨h, t⟩ := t
    simp only [Term.placeOccsArms, List.mem_append]
    rcases List.mem_cons.mp ha with rfl | h
    · exact .inl hx
    · exact .inr (ih h)

theorem OccsIn.letIn_body {O : Nat → Place → Prop} {h : Hint} {u w : Term} (hO : OccsIn (.letIn h u w) O) :
    OccsIn w (fun d p => O (d + 1) p) := by
  intro d p k hm
  refine hO (d + 1) p k ?_
  simp only [Term.placeOccs, List.mem_append]
  refine .inr ?_
  rw [show (1 : Nat) = 0 + 1 from rfl, DataModel.Exists.FrameLocal.placeOccs_add w 0 1]
  exact List.mem_map.mpr ⟨(d, p, k), hm, rfl⟩

theorem JOk.lift {n : Nat} {al : List (Option Place)} {O : Nat → Place → Prop} {a : Option Place}
    {acc ms : List Place} (ha : ∀ q, a = some q → RootOk n al O q.root)
    (h : JOk (n + 1) (a :: al) (fun d p => O (d + 1) p) acc ms) : JOk n al O acc ms := by
  intro q hq
  rcases h q hq with h | (⟨d, p, hp, hd, he⟩ | ⟨q', hq', he⟩)
  · exact .inl h
  · exact .inr (.inl ⟨d + 1, p, hp, by omega, by omega⟩)
  · rcases List.mem_cons.mp hq' with e | e
    · exact .inr (he ▸ ha q' e.symm)
    · exact .inr (.inr ⟨q', e, he⟩)

/-- The occurrences of a subterm are the term's. -/
macro "occs_tac" : tactic => `(tactic| focus first
  | (assumption)
  | (refine OccsIn.sub ‹_› fun x hx => ?_; simp [Term.placeOccs, Term.placeOccsList, hx]; done)
  | (intro a ha; refine OccsIn.sub ‹_› fun x hx => ?_; simp [Term.placeOccs, mem_placeOccsList ha hx]; done)
  | (intro a ha; refine OccsIn.sub ‹_› fun x hx => ?_; simp [Term.placeOccs, mem_placeOccsArms ha hx]; done)
  | (intro a ha; simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
     rcases ha with rfl | rfl <;> (refine OccsIn.sub ‹_› fun x hx => ?_; simp [Term.placeOccs, hx]) <;> done))

theorem jd_local (f : Nat) :
    (∀ sc al t acc (O : Nat → Place → Prop), al.length = sc.length → OccsIn t O →
      RetP (JOk sc.length al O acc) (jdMoves f sc al t acc)) ∧
    (∀ sc al ts acc (O : Nat → Place → Prop), al.length = sc.length → (∀ t ∈ ts, OccsIn t O) →
      RetP (JOk sc.length al O acc) (jdMovesList f sc al ts acc)) ∧
    (∀ sc al t arms acc (O : Nat → Place → Prop), al.length = sc.length → OccsIn t O → (∀ a ∈ arms, OccsIn a O) →
      RetP (JOk sc.length al O acc) (jdMatch f sc al t arms acc)) := by
  induction f with
  | zero =>
    refine ⟨fun sc al t acc O _ _ => ?_, fun sc al ts acc O _ _ => ?_, fun sc al t arms acc O _ _ _ => ?_⟩
    · unfold Ochr.jdMoves; exact RetP.exhausted'
    · cases ts with
      | nil => unfold Ochr.jdMovesList; exact RetP.pure' (JOk.refl _)
      | cons t ts => unfold Ochr.jdMovesList; exact RetP.exhausted'
    · unfold Ochr.jdMatch; exact RetP.exhausted'
  | succ f ih =>
    obtain ⟨ihM, ihL, ihA⟩ := ih
    refine ⟨fun sc al t acc O hl hO => ?_, fun sc al ts acc O hl hO => ?_,
      fun sc al t arms acc O hl hO hA => retP_jdMatch_succ f ihM sc al t arms acc O hl hO hA⟩
    · cases t
      all_goals (unfold Ochr.jdMoves; dsimp only)
      all_goals (repeat (any_goals first
        | (contradiction)
        | (exact RetP.pure' (JOk.refl _))
        | (refine ihM _ _ _ _ O hl ?_; occs_tac)
        | (refine ihL _ _ _ _ O hl ?_; occs_tac)
        | (refine ihA _ _ _ _ _ O hl hO ?_; occs_tac)
        | (exact retP_jdFns _ _ _ _ _ hO)
        | (refine JOk.bind (ihM _ _ _ _ O hl ?_) fun _ _ => ?_; occs_tac)
        | (refine JOk.bind (ihL _ _ _ _ O hl ?_) fun _ _ => ?_; occs_tac)
        | (refine (ihM (_ :: _) (_ :: _) _ _ (fun d p => O (d + 1) p) (by simp [hl]) (OccsIn.letIn_body hO)).mono
            fun _ hj => JOk.lift ?_ hj
           intro q hq
           split at hq
           · rw [← hl]; exact jdResolve_ok (hO 0 _ .borrow (by simp [Term.placeOccs])) hq
           · cases hq)
        | (refine RetP.pure' (JOk.add ?_); rw [← hl]; refine jdResolve_ok ?_ (by assumption)
           exact hO 0 _ .read (by simp [Term.placeOccs]))
        | (exact RetP.pure' JOk.refill)
        | (with_reducible apply RetP.err_bind)
        | (with_reducible apply RetP.err')
        | (with_reducible apply RetP.exhausted')
        | (apply RetP.ite' <;> intro _)
        | (apply RetP.dite' <;> intro _)
        | (with_reducible apply RetP.bind'; intro _)
        | (dsimp only)
        | (split <;> try (injections <;> subst_vars))))
      -- the match on a number: its arms `[z, s]`
      all_goals (refine ihA _ _ _ _ _ O hl hO ?_
                 intro a ha; simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
                 rcases ha with rfl | rfl <;> (refine OccsIn.sub hO fun x hx => ?_; simp [Term.placeOccs, hx]))
    · cases ts with
      | nil => unfold Ochr.jdMovesList; exact RetP.pure' (JOk.refl _)
      | cons t ts =>
        unfold Ochr.jdMovesList
        dsimp only
        exact JOk.bind (ihM sc al t acc O hl (hO t (List.mem_cons_self ..)))
          fun a _ => ihL sc al ts a O hl fun x hx => hO x (List.mem_cons_of_mem _ hx)

/-! ## `DecLocal.join` -/

/-- **The join's places are the entry's or at a free variable**, for every successful run of the checker's join. -/
theorem joinMoves_local {f : Nat} {entry : List Place} {t : Term} {st st' : MState} {b : Nat} {ms : List Place}
    (h : Runs (joinMovesD entry t f) st b ms st') : ∀ q ∈ ms, q ∈ entry ∨ q.root ∈ t.freeVars := by
  have hR := (RetP.withLive' (live := true) ((jd_local f).1 [] [] t entry (fun d p => ∃ k, (d, p, k) ∈ t.placeOccs 0)
    rfl fun d p k hm => ⟨k, hm⟩)).run h
  intro q hq
  rcases hR q hq with h | (⟨d, p, ⟨k, hm⟩, hd, he⟩ | ⟨q', hq', -⟩)
  · exact .inl h
  · exact .inr ((DataModel.Exists.FrameLocal.mem_freeVars t _).mpr ⟨d, p, k, hm, by simpa using hd, by simpa using he⟩)
  · cases hq'

/-- **`DecLocal.join` at the fuel-free decisions, PROVED** (since main's D129): the table's join is a successful run's
answer (then `joinMoves_local`) or the entry itself. -/
theorem decLocal_join_ff (st : MState) (bc : List DeclInfo → List Place → Term → List Place × List (Place × Nat)) :
    ∀ sc entry t q, q ∈ (checkerDecisionsFF st bc).joinMoves sc entry t → q ∈ entry ∨ q.root ∈ t.freeVars := by
  intro sc entry t q hq
  simp only [checkerDecisionsFF, readDecisionFF] at hq
  split at hq
  · rename_i hs
    obtain ⟨f, b, st', hr⟩ := hs.choose_spec
    exact joinMoves_local hr q hq
  · exact .inl hq

/-- **`DecLocal.join` at the chain's decisions, PROVED.** -/
theorem decLocal_join_chain (fuel : Nat) (st : MState) :
    ∀ sc entry t q, q ∈ (chainDecisions fuel st).joinMoves sc entry t → q ∈ entry ∨ q.root ∈ t.freeVars :=
  decLocal_join_ff st _

end Ochr.Meaning.Steps.Machine
