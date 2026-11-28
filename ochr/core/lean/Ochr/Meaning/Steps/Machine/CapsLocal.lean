import Ochr.Meaning.Steps.Machine.JoinLocal
import Ochr.Meaning.BlockCaps

/-!
# `DecLocal.caps`, proved (exists13)

The last of `FrameLocal.DecLocal`'s four parts at the chain's decisions: every capture a stuck block's [Entry]
takes (`Decisions.blockCaps`, at the chain `BlockCaps.staticBlockCaps`) is rooted at a free variable of the term.
Each step of `staticBlockCaps` keeps the root of what it is given, and each place it starts from is rooted at
a free variable:
* the join's net: a move of the join is in the entry or rooted at a free variable (`decLocal_join_ff`), and
  one in the entry is covered by itself (`jdCovers_self`), so the net drops it;
* the closures' captures (`fnOccs_ok`) and the block's occurrences (`freeOccsBlock`, `blockOccs_sub`): an
  occurrence at depth `c` of a place whose root is `c` or more names the free variable `root - c`
  (`FrameLocal.mem_freeVars`), and the place is re-rooted at that variable;
* `staticReroot` (a strict prefix or the place itself) and `splitLoop` (a place or its fields) keep the root;
* the sort: main's `blockCapOrder` is a permutation (`blockCapOrder_perm`). Before main's capture sort this
  step was `Array.qsort`, about which Lean's core states nothing (docs/34 §18.17).
-/

namespace Ochr.Meaning.Steps.Machine
open Ochr Ochr.Meaning

/-- A place rooted at a free variable of `t`. -/
def RootIn (t : Term) (q : Place) : Prop := q.root ∈ t.freeVars

theorem jdStepEq_self : ∀ a : Step, jdStepEq a a = true
  | .deref => rfl
  | .proj i => by
    show (i == i) = true
    exact beq_self_eq_true i
  | .field g => by
    show (g.ty == g.ty && g.ctor == g.ctor && g.idx == g.idx) = true
    simp

theorem zip_self_jdStepEq : ∀ l : List Step, ((l.zip l).all fun (x : Step × Step) => jdStepEq x.1 x.2) = true
  | [] => rfl
  | a :: l => by simp [List.zip_cons_cons, jdStepEq_self, zip_self_jdStepEq l]

theorem jdPrefix_self (q : Place) : jdPrefix q q = true := by
  unfold jdPrefix
  generalize q.steps = st
  obtain ⟨i, qs⟩ := st
  simpa using zip_self_jdStepEq qs

/-- A place is covered by itself (a move of `q` moves `q`). -/
theorem jdCovers_self (q : Place) : jdCovers q q = true := by
  unfold jdCovers
  rw [jdPrefix_self]
  simp

theorem root_stepPlace (q : Place) (a : Step) : (stepPlace q a).root = q.root := by
  cases a <;> rfl

theorem root_foldl_stepPlace : ∀ (l : List Step) (q : Place), (l.foldl stepPlace q).root = q.root
  | [], _ => rfl
  | a :: l, q => by rw [List.foldl_cons, root_foldl_stepPlace l, root_stepPlace]

/-- `staticReroot` keeps the root: it answers a strict prefix or the place itself. -/
theorem root_staticReroot (pd : Place → DeclInfo) (entry : List Place) (q : Place) :
    (BlockCaps.staticReroot pd entry q).root = q.root := by
  unfold BlockCaps.staticReroot
  split
  · rename_i p hp
    have hm := List.mem_of_find?_eq_some hp
    unfold BlockCaps.strictPrefixes at hm
    rw [← DataModel.Exists.FrameLocal.steps_fst q]
    revert hm
    generalize q.steps = st
    obtain ⟨r, ss⟩ := st
    intro hm
    simp only [List.mem_map] at hm
    obtain ⟨k, -, rfl⟩ := hm
    rw [root_foldl_stepPlace]
    rfl
  · rfl

theorem root_mapRoot_var (o : Nat) (p : Place) : (p.mapRoot fun _ => .var o).root = o := by
  rw [root_mapRoot]; rfl

/-- An occurrence `freeOccsBlock` lists names a free variable. -/
theorem freeOccsBlock_free {t : Term} {o : Nat} {p : Place} {k : PKind} (h : (o, p, k) ∈ t.freeOccsBlock) :
    o ∈ t.freeVars := by
  unfold Term.freeOccsBlock at h
  rw [List.mem_filterMap] at h
  obtain ⟨⟨c, p', k'⟩, hm, he⟩ := h
  dsimp only at he
  split at he
  · rename_i hc
    simp only [Option.some.injEq, Prod.mk.injEq] at he
    obtain ⟨rfl, rfl, rfl⟩ := he
    obtain ⟨k'', hk⟩ := blockOccs_sub hm
    exact (DataModel.Exists.FrameLocal.mem_freeVars t _).mpr ⟨c, p', k'', hk, hc, rfl⟩
  · cases he

/-- A closure's capture `fnOccs` lists names a free variable. -/
theorem fnOccs_free {t : Term} {o : Nat} {p : Place} (h : (o, p) ∈ t.fnOccs 0) : o ∈ t.freeVars := by
  obtain ⟨d, k, hm, hd, ho⟩ := fnOccs_ok t 0 o p h
  exact (DataModel.Exists.FrameLocal.mem_freeVars t _).mpr ⟨d, p, k, hm, hd, ho⟩

/-- A list invariant through a left fold. -/
theorem foldl_inv {α β : Type} (f : β → α → β) (P : β → Prop) :
    ∀ (l : List α) (b : β), P b → (∀ b a, a ∈ l → P b → P (f b a)) → P (l.foldl f b)
  | [], _, h0, _ => h0
  | a :: l, b, h0, hs => foldl_inv f P l (f b a) (hs b a (List.mem_cons_self ..) h0)
      fun b' a' ha' hb' => hs b' a' (List.mem_cons_of_mem _ ha') hb'

/-- The fields `oneCtorFields` answers are fields of the place. -/
theorem root_oneCtorFields {Γ : List IndDecl} {r : DeclInfo} {q : Place} {chs : List Place}
    (h : BlockCaps.oneCtorFields Γ r q = some chs) : ∀ ch ∈ chs, ch.root = q.root := by
  unfold BlockCaps.oneCtorFields at h
  split at h
  · split at h
    · split at h
      · simp only [Option.some.injEq] at h
        subst h
        intro ch hch
        simp only [List.mem_map] at hch
        obtain ⟨⟨⟨_, _⟩, _⟩, -, rfl⟩ := hch
        rfl
      · cases h
    · cases h
  · cases h

/-- `splitLoop` keeps a property of roots: its places are those it is given and their fields. -/
theorem splitLoop_root (S : Nat → Prop) (Γ : List IndDecl) (pd : Place → DeclInfo) (moved : List Place)
    (uses : List (Place × Nat)) (wholeUses : List (Place × PKind)) :
    ∀ (n : Nat) (todo out : List (Place × Nat)), (∀ x ∈ todo, S x.1.root) → (∀ x ∈ out, S x.1.root) →
      ∀ x ∈ BlockCaps.splitLoop Γ pd moved uses wholeUses n todo out, S x.1.root
  | 0, todo, out, ht, ho => by
    intro x hx
    unfold BlockCaps.splitLoop at hx
    rcases List.mem_append.1 hx with hx | hx
    · exact ho x hx
    · exact ht x hx
  | n + 1, [], out, _, ho => by
    intro x hx
    unfold BlockCaps.splitLoop at hx
    exact ho x hx
  | n + 1, (q, k) :: todo, out, ht, ho => by
    have hq : S q.root := ht (q, k) (List.mem_cons_self ..)
    have ht' : ∀ x ∈ todo, S x.1.root := fun x hx => ht x (List.mem_cons_of_mem _ hx)
    have hadd : ∀ k', ∀ x ∈ out ++ [(q, k')], S x.1.root := by
      intro k' x hx
      rcases List.mem_append.1 hx with hx | hx
      · exact ho x hx
      · rw [List.mem_singleton] at hx; subst hx; exact hq
    intro x hx
    unfold BlockCaps.splitLoop at hx
    dsimp only at hx
    split at hx
    · exact splitLoop_root S Γ pd moved uses wholeUses n todo _ ht' (hadd k) x hx
    · split at hx
      · exact splitLoop_root S Γ pd moved uses wholeUses n todo _ ht' (hadd 2) x hx
      · split at hx
        · exact splitLoop_root S Γ pd moved uses wholeUses n todo _ ht' (hadd 2) x hx
        · rename_i chs hchs
          refine splitLoop_root S Γ pd moved uses wholeUses n _ out ?_ ho x hx
          intro y hy
          rcases List.mem_append.1 hy with hy | hy
          · exact ht' y hy
          · rw [List.mem_filterMap] at hy
            obtain ⟨ch, hch, he⟩ := hy
            split at he
            · cases he
            · simp only [Option.some.injEq] at he
              subst he
              rw [root_oneCtorFields hchs ch hch]
              exact hq

theorem mem_map_fst {α β : Type} {f : α × β → α × β} (hf : ∀ y, (f y).1 = y.1) {l : List (α × β)} {x : α × β}
    (h : x ∈ l.map f) : ∃ y ∈ l, x.1 = y.1 := by
  obtain ⟨y, hy, rfl⟩ := List.mem_map.1 h
  exact ⟨y, hy, hf y⟩

/-- **The static captures are rooted at the term's free variables** (any decisions whose join is local). -/
theorem staticBlockCaps_root (D : Decisions) (Γ : List IndDecl) (fuel : Nat) (sc : List DeclInfo) (entry : List Place)
    (mt : Term) (hJ : ∀ q, q ∈ D.joinMoves sc entry mt → q ∈ entry ∨ q.root ∈ mt.freeVars) :
    ∀ qk ∈ (BlockCaps.staticBlockCaps D Γ fuel sc entry mt).2, qk.1.root ∈ mt.freeVars := by
  intro qk hqk
  unfold BlockCaps.staticBlockCaps at hqk
  simp only at hqk
  rw [(blockCapOrder_perm _).mem_iff, List.toList_toArray] at hqk
  refine splitLoop_root (· ∈ mt.freeVars) _ _ _ _ _ _ _ _ ?_ (fun x hx => absurd hx List.not_mem_nil) qk hqk
  -- the net: a move of the join, not covered by the entry
  have hnet : ∀ q ∈ (D.joinMoves sc entry mt).filter (fun q => !entry.any (jdCovers · q)), q.root ∈ mt.freeVars := by
    intro q hq
    rw [List.mem_filter] at hq
    rcases hJ q hq.1 with he | hr
    · have : entry.any (jdCovers · q) = true := List.any_eq_true.2 ⟨q, he, jdCovers_self q⟩
      simp [this] at hq
    · exact hr
  -- the captures K1(c)–(f): the moved places, re-rooted, and the block's occurrences
  intro x hx
  obtain ⟨y, hy, hxy⟩ := mem_map_fst (by intro y; split <;> (try split) <;> rfl) hx
  obtain ⟨z, hz, hyz⟩ := mem_map_fst (by intro y; split <;> (try split) <;> rfl) hy
  rw [hxy, hyz]
  refine (foldl_inv _ (fun b : List (Place × Nat) => ∀ x ∈ b, x.1.root ∈ mt.freeVars) _ _ ?_ ?_) z hz
  · -- K1(c): maximal places of the block's occurrences
    refine foldl_inv _ (fun b : List (Place × Nat) => ∀ x ∈ b, x.1.root ∈ mt.freeVars) _ _ (fun x hx => absurd hx List.not_mem_nil) ?_
    intro b u hu hb
    try dsimp only
    split
    · intro w hw
      rcases List.mem_append.1 hw with hw | hw
      · exact hb w hw
      · rw [List.mem_singleton] at hw
        subst hw
        obtain ⟨⟨o, p, k⟩, ho, rfl⟩ := List.mem_map.1 hu
        try dsimp only
        rw [root_mapRoot_var]
        exact freeOccsBlock_free ho
    · exact hb
  · -- K1(d): a moved place covering captures replaces them
    intro b m hm hb
    have hmr : m.root ∈ mt.freeVars := by
      refine (foldl_inv _ (fun b : List Place => ∀ q ∈ b, q.root ∈ mt.freeVars) _ _ (fun q hq => absurd hq List.not_mem_nil) ?_) m hm
      intro acc q hq hacc
      try dsimp only
      have hqr : q.root ∈ mt.freeVars := by
        refine (foldl_inv _ (fun b : List Place => ∀ q ∈ b, q.root ∈ mt.freeVars) _ _ hnet ?_) q hq
        intro mv op hop hmv
        try dsimp only
        split
        · exact hmv
        · split
          · exact hmv
          · intro q' hq'
            rcases List.mem_append.1 hq' with hq' | hq'
            · exact hmv q' hq'
            · rw [List.mem_singleton] at hq'
              subst hq'
              rw [root_mapRoot_var]
              exact fnOccs_free hop
      split
      · exact hacc
      · intro q' hq'
        rcases List.mem_append.1 hq' with hq' | hq'
        · exact hacc q' hq'
        · rw [List.mem_singleton] at hq'
          subst hq'
          rw [root_staticReroot]
          exact hqr
    try dsimp only
    split
    · intro w hw
      rcases List.mem_append.1 hw with hw | hw
      · exact hb w (List.mem_filter.1 hw).1
      · rw [List.mem_singleton] at hw; subst hw; exact hmr
    · exact hb

/-- **`DecLocal.caps` at the chain's decisions, PROVED** (exists13): every capture the chain's [Entry] takes is
rooted at a free variable of the term (`staticBlockCaps_root`, with the join's locality `decLocal_join_ff`). -/
theorem decLocal_caps_chain (fuel : Nat) (st : MState) :
    ∀ sc entry t qk, qk ∈ ((chainDecisions fuel st).blockCaps sc entry t).2 → qk.1 ∈ entry ∨ qk.1.root ∈ t.freeVars :=
  fun sc entry t qk h => .inr (staticBlockCaps_root (checkerDecisionsFF st) st.inds fuel sc entry t
    (decLocal_join_ff st _ sc entry t) qk h)

end Ochr.Meaning.Steps.Machine
