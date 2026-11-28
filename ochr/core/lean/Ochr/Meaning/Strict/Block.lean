import Ochr.Meaning.Strict.Clauses2

/-!
# The fundamental lemma at a sealed block's text (exp-block-text; spine-exp-block, lead38)

On the experimental checker a stuck match closes off as a sealed TEXT, `Term.block cs rd pf B m` (`Run.lean`'s clause:
the cells' terms run, each a member of its recorded type with its borrow held there and live, `CellsOk`; the cells bound
as nested `let`s around the match, `bindCells`; the match in tail position at `B`; the cells dropped as a `let` drops
its binding; a borrow result lent at the borrow cells' places; the result at `B`, strictly). Each piece is a lemma the
`let`, the ascription and the join already have: `sgood_pushBindShaped` (a cell bound: a member of its type, its label
recording that type and live), the inner match's lemma, `sgood_letDrop` (a cell dropped), `sgood_setLent` (the lend).
-/

namespace Ochr.Meaning.Strict
open Ochr.Meaning

section
variable {K : RunCtx} {ρ : Assignment} {φ : Future}

/-- A sealed block's cells' terms: their runs keep the invariant. -/
theorem fund_cells : ∀ (cs : List (Hint × Term)), (∀ a ∈ cs, Fund K ρ φ a.2) →
    StatePres K.dm K.Γ φ (runCells K ρ φ cs)
  | [], _ => fun s s' r hs h => by
    simp only [runCells] at h
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (SM.pure_some h)
    exact hs
  | (x, a) :: cs, ha => fun s s' r hs h => by
    simp only [runCells] at h
    obtain ⟨y, s₁, h1, h2⟩ := SM.bind_some h
    obtain ⟨z, s₂, h3, h4⟩ := SM.bind_some h2
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (SM.pure_some h4)
    exact fund_cells cs (fun b hb => ha b (List.mem_cons_of_mem _ hb)) _ _ _
      ((ha (x, a) List.mem_cons_self) false _ _ _ _ hs h1).2.2.2 h3

theorem heldTy_pushBindShaped (s : SState) (b : SBinding) : (pushBindShaped s b).heldTy = s.heldTy := by
  have h2 : ∀ l, (s.takeLabel l).heldTy = s.heldTy := by
    intro l; unfold SState.takeLabel
    split
    · exact heldTy_setAt _ _ _
    · rfl
  unfold pushBindShaped
  split
  · rename_i l _
    dsimp only
    split
    · exact h2 l
    · exact h2 l
  · rfl

/-- `CellsOk` survives a cell bound: the held types are kept, the later cells' borrows stay live. -/
theorem cellsOk_push {s : SState} (hs : SGood K.dm K.Γ φ s) (c : Res) (dT : DeclInfo × TyS) :
    ∀ {rs : List Res} {ts : List (DeclInfo × TyS)}, CellsOk K.dm.read s rs ts →
      CellsOk K.dm.read (pushBindShaped s (cellBind c dT)) rs ts
  | [], [], _ => trivial
  | [], _ :: _, h => h.elim
  | _ :: _, [], h => h.elim
  | r :: rs, dT' :: ts, ⟨⟨hm, ht, hl⟩, h⟩ => by
    refine ⟨⟨hm, fun l hl' => ?_, fun l hl' => ?_⟩, cellsOk_push hs c dT h⟩
    · rw [heldTy_pushBindShaped]; exact ht l hl'
    · by_cases hne : s.env = []
      · rw [pushBindShaped_nil _ _ hne]; exact hl l hl'
      · exact (live_pushBindShaped hs.acyc.2.2 (cellBind c dT) hne l).mpr (.inl (hl l hl'))

/-- **The cells bound around the match**: each bound as a `let` binds (`sgood_pushBindShaped`), the match's lemma
inside, each dropped as a `let` drops (`sgood_letDrop`). -/
theorem bindCells_fund {k : SM Res} (hk : FundAt K.dm K.Γ φ k) :
    ∀ (rs : List Res) (ts : List (DeclInfo × TyS)) (s s' : SState) (r : Res), SGood K.dm K.Γ φ s →
      CellsOk K.dm.read s rs ts → bindCells K φ k rs ts s = some (r, s') →
      GoodRes K.dm.read r ∧ LabOk K.dm s' r ∧ LoU s' r.2.label ∧ SGood K.dm K.Γ φ s'
  | [], [], s, s', r, hs, _, h => hk s s' r hs h
  | [], _ :: _, _, _, _, _, hok, _ => hok.elim
  | _ :: _, [], _, _, _, _, hok, _ => hok.elim
  | c :: rs, dT :: ts, s, s', r, hs, hok, h => by
    simp only [bindCells] at h
    split at h
    · rename_i x s₂ hb
      obtain ⟨hend, h⟩ := open Classical in ite_none_some h
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
      obtain ⟨⟨hm, ht, hl⟩, hrest⟩ := hok
      have hs₁ : SGood K.dm K.Γ φ (pushBindShaped s (cellBind c dT)) := by
        by_cases hne : s.env = []
        · rw [pushBindShaped_nil _ _ hne]; exact hs
        · refine sgood_pushBindShaped hs _ rfl (.inl hm) (fun l hl' => ⟨ht l hl', hs.held l (hl l hl')⟩)
            (fun l hl' => lou_live hs.acyc.2.2 (hl l hl')) hne
      obtain ⟨hg, hlab, hlou, hs₂⟩ := bindCells_fund hk rs ts _ s₂ x hs₁ (cellsOk_push hs c dT hrest) hb
      refine ⟨hg, hlab.of_held (heldSame_letDrop _ _), ?_, sgood_letDrop hs₂ hend⟩
      exact (letDrop_rinv (fun _ => True) hs₂.acyc hlou _ (heldTop_eq s₂)).2.1
    · cases h

/-- A block's lend (`entryLend` with no `&` captures) only adds sites. -/
theorem entryLend_nil (snap : List Site) (lab : Option Nat) (s : SState) :
    entryLend ([], []) snap lab s = s ∨ ∃ k xs, entryLend ([], []) snap lab s = s.setLent k xs := by
  unfold entryLend
  split
  · split
    · exact .inr ⟨_, _, rfl⟩
    · exact .inl rfl
  · exact .inl rfl

/-- **A sealed block's text** (exp-block-text). -/
theorem fund_block {cs : List (Hint × Term)} {rd : List (DeclInfo × Value)} {pf : List Bool} {B : Value} {m : Term}
    (hcs : ∀ a ∈ cs, Fund K ρ φ a.2) (hm : Fund K ρ φ m) : Fund K ρ φ (.block cs rd pf B m) := fun tl hint => by
  intro s s' r hs h
  rw [runT] at h
  refine fund_erasedS (fund_strictS ?_) s s' r hs h
  intro s₀ s₄ r₀ hs₀ h₀
  dsimp only at h₀
  split at h₀
  · rename_i rs s₁ hc1
    have hs₁ := fund_cells cs hcs _ _ _ hs₀ hc1
    obtain ⟨hok, h₀⟩ := open Classical in ite_none_some h₀
    split at h₀
    · rename_i r' R s₃ hb
      obtain ⟨ht, h₀⟩ := open Classical in ite_none_some h₀
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h₀)
      obtain ⟨-, hlab, hlou, hs₃⟩ := bindCells_fund (hm true _) rs _ s₁ s₃ (r', R) hs₁ hok hb
      generalize hS : (if isRefDecl (K.D.declOf (scopeOf s₀) (.block cs rd pf B m)) then
          entryLend ([], []) (cellSnapshot rs s₁) R.label s₃ else s₃) = S at ht ⊢
      have hSx : S = s₃ ∨ ∃ k xs, S = s₃.setLent k xs := by
        rw [← hS]; split
        · exact entryLend_nil _ _ _
        · exact .inl rfl
      rcases hSx with rfl | ⟨k, xs, rfl⟩
      · exact ⟨fun l hl => ⟨ht l hl, (hlab l hl).2⟩, hlou, hs₃⟩
      · exact ⟨fun l hl => ⟨ht l hl, (hlab l hl).2⟩, lou_setLent.mpr hlou, sgood_setLent hs₃ k xs⟩
    · cases h₀
  · cases h₀

end

end Ochr.Meaning.Strict
