import Ochr.Meaning.Steps.SplitP
import Ochr.Meaning.Steps.ColumnI
import Ochr.Meaning.Steps.BotWriteRel

/-!
# The column `P`: the reference's run of the body from a related state (lead16, 2026-11-21; docs/31 D131)

The reference does not split: `runT`'s `.matchNat` clause reads the tag of `n` (the number `ρ 0`), runs the one
arm it selects (in tail position no [Entry]), then drops at the join (`joinDrop`: the join's moves `[n]`, read
from the aligned table). Here it is computed from every reference state that reads like one related to `P`'s
start state (`RefP`: no live label; `n` the binding `(1, 1)` holding the number `ρ 0` at `Nat`; the function's
own binding `(1, 0)`; the top frame read `[.other, .pi .other]`), at a table that decides as the checker does
there (`ParDecP`):

- `ρ 0 = 0`: the result `0` at `Nat`, the state with `n` moved;
- `ρ 0 = a + 1`: the result `a` at `Nat`; the arm's read of `n.0` writes `moved` at the predecessor
  (`setContent` at `[.0]`), then the join writes `moved` at `n`.

The two writes are stated exactly as `botWrite_rel` takes them, so the relation follows the checker's state
through the arm's move and the join's drop.
-/

namespace Ochr.Meaning.Steps.Form.ColumnP

open Ochr Ochr.Meaning Ochr.Meaning.Steps Ochr.Meaning.Steps.Form
open Ochr.Meaning.Steps.Form.ColumnI (piNat nB psI outI selfTy selfSem)

/-- The top frame's readings at `P`'s body (`n`, then the function's own binding). -/
abbrev RI : List DeclInfo := [.other, .pi .other]

/-- The place the `S` arm reads: `n.0`. -/
abbrev pn0 : Place := .proj 0 (.var 0)

/-- **The decisions the reference's run of `P`'s body reads** (a table aligned with the checker at `stP` makes
them, `parDecP`): the body and the arm's read are neither statements nor proofs, `n` and `n.0` are moved (not
copied), and the join of the match with nothing moved at entry moves `n`. -/
def ParDecP (D : Decisions) : Prop :=
  D.flags RI bodyP = (false, false) ∧ D.flags RI (.place pn0) = (false, false) ∧
    D.copy (D.placeDecl RI pn0) = false ∧ D.copy (D.placeDecl RI (.var 0)) = false ∧
    D.joinMoves RI [] bodyP = [.var 0]

/-- **What the join of `P`'s match reads of a reference state**: no live label, nothing held, the top frame
read `RI`, `n` the binding `(1, 1)`. -/
structure RefJ (s : SState) : Prop where
  live : s.liveLabels = []
  shape : ∀ p, s.shape p = none
  scope : scopeOf s = RI
  resolve0 : resolve s (.var 0) = some (.bind 1 1, [])

/-- **What the reference's run of `P`'s body reads of its state**: `RefJ`; the top frame has two bindings, `n`
at `(1, 1)` holding `ρ 0` at `Nat` and the function's own at `(1, 0)` holding `g`. -/
structure RefP (ρ : Assignment) (φ : Future) (g : Sem) (s : SState) : Prop extends RefJ s where
  top : ∃ fr, s.env.getLast? = some fr ∧ fr.binds.length = 2
  topIdx : s.topIdx = 1
  valN : s.valAt (.bind 1 1) φ = ρ 0
  valSelf : s.valAt (.bind 1 0) φ = g
  tyN : (s.tyAt (.bind 1 1)).m = TyM.nat

section
variable {ρ : Assignment} {φ : Future} {g : Sem} {s : SState}

theorem RefJ.noSites (h : RefJ s) (pos : Pos) : ∀ l ∈ s.liveLabels, ∀ x ∈ s.lent l, x.pos ≠ pos := by
  rw [h.live]; intro l hl; cases hl

theorem RefJ.access (h : RefJ s) (pos : Pos) (hit : List Step → Bool) : s.access pos hit = s :=
  access_noSites (h.noSites pos)

theorem RefJ.accessOk (h : RefJ s) (K : RunCtx) (φ : Future) (pos : Pos) (hit : List Step → Bool) :
    AccessOk K φ s pos hit :=
  accessOk_noSites (h.noSites pos)

theorem RefJ.typedFuture (h : RefJ s) (φ : Future) : s.typedFuture φ = φ := by
  funext l; unfold SState.typedFuture; rw [h.live]; simp

theorem RefJ.lentFuture (h : RefJ s) (φ : Future) : s.lentFuture φ = φ := by
  funext l; unfold SState.lentFuture; rw [h.live]; simp

theorem RefJ.typedFut (h : RefJ s) (K : RunCtx) {ψ : Future} (hψ : TypedFut K φ s ψ) : ψ = φ := by
  funext l; exact hψ.1 l (by rw [h.live]; simp)

/-- A write at a binding keeps what the join reads. -/
theorem RefJ.setAt (h : RefJ s) (p : Pos) (w : SVal) : RefJ (s.setAt p w) where
  live := by rw [Strict.liveLabels_setAt]; exact h.live
  shape := fun q => by rw [SState.shape_setAt]; exact h.shape q
  scope := by rw [scopeOf_of_declsOf (declsOf_setAt s p w)]; exact h.scope
  resolve0 := by rw [resolve_setAt]; exact h.resolve0

theorem RefP.varPos0 (h : RefP ρ φ g s) : s.varPos 0 = some (.bind 1 1) := by
  obtain ⟨fr, hfr, hl⟩ := h.top
  unfold SState.varPos; rw [hfr]; dsimp only; rw [hl, h.topIdx]; rfl

theorem RefP.varPos1 (h : RefP ρ φ g s) : s.varPos 1 = some (.bind 1 0) := by
  obtain ⟨fr, hfr, hl⟩ := h.top
  unfold SState.varPos; rw [hfr]; dsimp only; rw [hl, h.topIdx]; rfl

theorem RefP.resolveN0 (h : RefP ρ φ g s) : resolve s pn0 = some (.bind 1 1, [.proj 0]) := by
  unfold resolve; rw [show pn0.steps = (0, [.proj 0]) from rfl]; simp [h.varPos0]

end

/-! ## The join -/

section
variable {K : RunCtx} {ρ : Assignment} {φ : Future} {s : SState}

/-- The write the join's drop of `n` makes (`dropAt` at the root, `botWrite_rel`'s form). -/
noncomputable def dropN (K : RunCtx) (s : SState) : SState :=
  s.setAt (.bind 1 1) fun φ' =>
    (Sem.updAt K.dm K.Γ (s.tyAt (.bind 1 1)) (fun _ => .moved) [] (s.valAt (.bind 1 1) φ')).getD .err

theorem lentPrefix_nil (s : SState) (pos : Pos) : lentPrefix s pos [] = none := rfl

theorem accessLentPrefix_nil (s : SState) (pos : Pos) : accessLentPrefix pos [] s = s := by
  unfold accessLentPrefix; rw [lentPrefix_nil]

/-- **The join's drop of `P`'s match**, from a state whose `n` holds no borrow: its ends are strict-OK and it
writes `moved` at `n`. -/
theorem joinP (hd : ParDecP K.D) (h : RefJ s) :
    JoinDropOk K φ [] bodyP s ∧ joinDrop K φ [] bodyP s = dropN K s := by
  have hjm : K.D.joinMoves (scopeOf s) [] bodyP = [.var 0] := by rw [h.scope]; exact hd.2.2.2.2
  have hcp : K.D.copy (K.D.placeDecl (scopeOf s) (.var 0)) = false := by rw [h.scope]; exact hd.2.2.2.1
  have hdrop : dropAt K φ (.var 0) (.bind 1 1) [] s = dropN K s := by
    unfold dropAt; rw [h.shape]; dsimp only
    rw [h.access, hcp, if_neg (by simp), if_pos (fun _ _ => by rw [Sem.updAt.eq_def]; rfl)]
    rfl
  refine ⟨?_, ?_⟩
  · unfold JoinDropOk; rw [hjm]
    refine ⟨?_, trivial⟩
    unfold JoinStepOk; rw [h.resolve0]; dsimp only
    refine ⟨by unfold LentPrefixOk; rw [lentPrefix_nil]; trivial, ?_⟩
    rw [accessLentPrefix_nil]
    unfold DropOk; rw [h.shape]; dsimp only
    intro _ _; exact h.accessOk K φ _ _
  · unfold joinDrop; rw [hjm]
    simp only [List.foldl_cons, List.foldl_nil, h.resolve0, accessLentPrefix_nil]
    exact hdrop

end

/-! ## The arms and the match -/

section
variable {K : RunCtx} {ρ : Assignment} {φ : Future} {g : Sem} {s : SState}

/-- The write the `S` arm's read of `n.0` makes (`setContent` at `[.0]`, `botWrite_rel`'s form). -/
noncomputable def setN0 (K : RunCtx) (s : SState) : SState :=
  s.setAt (.bind 1 1) fun φ' =>
    (Sem.updAt K.dm K.Γ (s.tyAt (.bind 1 1)) (fun _ => .moved) [.proj 0] (s.valAt (.bind 1 1) φ')).getD .err

/-- Nothing is moved in the top frame at the match's start: `n` holds a number, the function's own binding a
meaning with no moved part. -/
theorem RefP.movedPlaces (h : RefP ρ φ g s) {k : Nat} (hk : ρ 0 = .el0 Nat k) (hg : ∀ q, Sem.movedIn g q = []) :
    Ochr.Meaning.movedPlaces φ s = [] := by
  obtain ⟨fr, hfr, hl⟩ := h.top
  unfold Ochr.Meaning.movedPlaces; rw [hfr]; dsimp only; rw [hl]
  simp [List.range_succ, h.varPos0, h.varPos1, h.lentFuture, h.valN, h.valSelf, h.shape, hk, hg, Sem.movedIn]

/-- **The `S` arm**: the read of `n.0` on `n ↦ a + 1` gives `a` at `Nat` and writes `moved` at the predecessor. -/
theorem runArmS (hd : ParDecP K.D) (h : RefP ρ φ g s) {a : Nat} (h0 : ρ 0 = .el0 Nat (a + 1)) (tl : Bool) (hint : TyS) :
    runT K ρ φ tl hint (.place pn0) s = some ((.el0 Nat a, .plain TyM.nat), setN0 K s) := by
  have hfl : K.D.flags (scopeOf s) (.place pn0) = (false, false) := by rw [h.scope]; exact hd.2.1
  have hcp : K.D.copy (K.D.placeDecl (scopeOf s) pn0) = false := by rw [h.scope]; exact hd.2.2.1
  have hco : contentOf K φ pn0 s = some ((.el0 Nat a, .plain TyM.nat, .bind 1 1, [.proj 0]), s) := by
    unfold contentOf; rw [h.resolveN0]; dsimp only
    rw [h.access, h.typedFuture, h.valN, h0]
    simp [Sem.follow, Sem.step, Sem.asNat_el0, TyS.plain]
  have hset : setContent K φ (.bind 1 1) [.proj 0] .moved s = some (⟨⟩, setN0 K s) := by
    unfold setContent
    rw [if_pos]
    · rfl
    · intro ψ hψ
      rw [h.typedFut K hψ, h.valN, h0, Sem.updAt.eq_def]
      simp only [Sem.asNat_el0]
      rw [Sem.updAt.eq_def]; rfl
  rw [runT]
  show SM.erasedIf (K.D.flags (scopeOf s) (.place pn0))
    (SM.guarded (ContentOk K φ pn0) (readPlace K φ pn0 (K.D.copy (K.D.placeDecl (scopeOf s) pn0)))) s = _
  rw [hfl, hcp]
  simp only [SM.erasedIf, SM.stmtIf, Bool.false_eq_true, if_false]
  rw [SM.guarded_of (by unfold ContentOk; rw [h.resolveN0]; exact h.accessOk K φ _ _)]
  unfold readPlace
  rw [hco]
  have hwhole : (Sem.el0 Nat a).whole := by simp [Sem.whole]
  have hrg : ReadGood K.dm.read (TyS.plain TyM.nat).m (.el0 Nat a) := .inl ⟨a, rfl⟩
  simp only [bind, Option.bind, hwhole, hrg, not_true_eq_false, if_false, Bool.false_eq_true, List.isEmpty_cons, hset]
  rfl

/-- **The match, at both tags**: on `0` the arm `Z` and the join's drop of `n`; on `a + 1` the arm's read of
`n.0` (the predecessor `a`) and the join's drop of `n`. In tail position, at any hint. -/
theorem runP (hd : ParDecP K.D) (h : RefP ρ φ g s) (hg : ∀ q, Sem.movedIn g q = []) (hint : TyS) :
    (ρ 0 = .el0 Nat 0 → runT K ρ φ true hint bodyP s = some ((.el0 Nat 0, .plain TyM.nat), dropN K s)) ∧
    (∀ a, ρ 0 = .el0 Nat (a + 1) →
      runT K ρ φ true hint bodyP s = some ((.el0 Nat a, .plain TyM.nat), dropN K (setN0 K s))) := by
  have hfl : K.D.flags (scopeOf s) (.matchNat (.var 0) .zero (.place pn0)) = (false, false) := by
    rw [h.scope]; exact hd.1
  have htag : TagOk K φ (.var 0) s := by unfold TagOk; rw [h.resolve0]; exact h.accessOk K φ _ _
  have htg : ∀ k, ρ 0 = .el0 Nat k →
      SM.guarded (TagOk K φ (.var 0)) (tagOf K φ (.var 0) natTag) s = some (natTag (.el0 Nat k) (s.tyAt (.bind 1 1)), s) := by
    intro k hk
    rw [SM.guarded_of htag]; unfold tagOf; rw [h.resolve0]; dsimp only
    rw [h.access, h.typedFuture, h.valN, hk]; rfl
  have hme : ∀ t, optCheck (MatchEntryOk K φ (!true) t s) = some ⟨⟩ := fun t => by
    unfold optCheck; rw [if_pos]; intro e; cases e
  have hent : ∀ t, matchEntry K φ (!true) t s = (s, fun _ s₂ => s₂) := fun t => rfl
  have hj : ∀ s', RefJ s' → optCheck (JoinDropOk K φ [] (.matchNat (.var 0) .zero (.place pn0)) s') = some ⟨⟩ ∧
      joinDrop K φ [] (.matchNat (.var 0) .zero (.place pn0)) s' = dropN K s' := fun s' h' => by
    obtain ⟨hjok, hjd⟩ := joinP (φ := φ) hd h'
    exact ⟨by unfold optCheck; exact if_pos hjok, hjd⟩
  refine ⟨fun h0 => ?_, fun a h0 => ?_⟩
  · have hz : ∀ T, runT K ρ φ true T .zero s = some ((.el0 Nat 0, .plain TyM.nat), s) := by
      intro T; rw [runT]; rfl
    have hmv := h.movedPlaces h0 hg
    have hnt : natTag (.el0 Nat 0) (s.tyAt (.bind 1 1)) = .el0 Nat 0 := by simp [natTag, Sem.asNat_el0]
    show runT K ρ φ true hint (.matchNat (.var 0) .zero (.place pn0)) s = _
    rw [runT]
    simp only [SM.erasedIf, SM.stmtIf, hfl, Bool.false_eq_true, if_false]
    rw [htg 0 h0, hnt]
    simp only [bind, Option.bind, hent, Sem.asNat_el0, tailHint_true, hz, hmv]
    rw [hme, (hj s h.toRefJ).1, (hj s h.toRefJ).2]
  · have hmv := h.movedPlaces h0 hg
    have hnt : natTag (.el0 Nat (a + 1)) (s.tyAt (.bind 1 1)) = .el0 Nat 1 := by simp [natTag, Sem.asNat_el0]
    have harm := runArmS (K := K) hd h h0 true hint
    have hj₁ : RefJ (setN0 K s) := h.toRefJ.setAt _ _
    show runT K ρ φ true hint (.matchNat (.var 0) .zero (.place pn0)) s = _
    rw [runT]
    simp only [SM.erasedIf, SM.stmtIf, hfl, Bool.false_eq_true, if_false]
    rw [htg (a + 1) h0, hnt]
    simp only [bind, Option.bind, hent, Sem.asNat_el0, tailHint_true, harm, hmv]
    rw [hme, (hj _ hj₁).1, (hj _ hj₁).2]

end

end Ochr.Meaning.Steps.Form.ColumnP
