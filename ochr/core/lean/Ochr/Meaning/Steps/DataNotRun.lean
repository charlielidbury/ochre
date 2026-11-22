import Ochr.Meaning.Steps.DataNot
import Ochr.Meaning.Steps.ColumnPRun

/-!
# The column `Not`: the reference's run of the body from a related state (lead21, 2026-11-22; docs/31 D147)

The reference does not split: `runT`'s `.matchInd` clause reads the tag of `b` (its meaning, a tree of `B`, read
off the value: `indTag`), runs the one arm the tag selects (in tail position no [Entry]), then drops at the join
(the join's moves, read from the aligned table, are none: no arm moves anything). The arm is a constructor with no
field: `runT`'s `.ctor` clause gives the tree `.dat "B" r c []` at the declaration's record `r = dm.recOf B []`, at
`B`'s type there, after its strict test (the tree a member of that type: `B`'s constructors have no field, so this
holds in every data model). Computed from every reference state that reads like one related to `Not`'s start state
(`RefNot`), at a table deciding as the checker does (`ParDecNot`), in a context whose declarations are `[B]`.
-/

namespace Ochr.Meaning.Steps.Form.ColumnNot

open Ochr Ochr.Meaning Ochr.Meaning.Steps Ochr.Meaning.Steps.Form
open Ochr.Meaning.Steps.Form.ColumnP (RefJ lentPrefix_nil accessLentPrefix_nil)

/-- The top frame's readings at `Not`'s body (`b`, then the function's own binding). -/
abbrev RN : List DeclInfo := [.ind "B" [], .pi (.ind "B" [])]

/-- The arms. -/
abbrev ctorF : Term := .ctor "B" 1 ⟨"F"⟩ [] []
abbrev ctorT : Term := .ctor "B" 0 ⟨"T"⟩ [] []

/-- **The decisions the reference's run of `Not`'s body reads** (a table aligned with the checker at `stNot` makes
them): the body and the two arms are neither statements nor proofs, and the join of the match with nothing moved
at entry moves nothing. -/
def ParDecNot (D : Decisions) : Prop :=
  D.flags RN bodyNot = (false, false) ∧ D.flags RN ctorF = (false, false) ∧ D.flags RN ctorT = (false, false) ∧
    D.joinMoves RN [] bodyNot = []

/-- **The table's declared readings of `Not`'s two places** at the body's scope: the function's own binding `Π(b : B). B`,
the scrutinee `b : B`. The first is what `ShapeFacts`' (V) needs where the place is not a declaration; the second
where it is, at a declaration list longer than `[B]` (docs/31 D177: with `[B]` alone the name was forced by the list). -/
def DecNot (D : Decisions) : Prop :=
  D.placeDecl RN (.var 1) = .pi (.ind "B" []) ∧ D.placeDecl RN (.var 0) = .ind "B" []

/-- The record of `B` (no parameter). -/
def recB (dm : DataModel) : Rec := dm.recOf declB []

/-- The meaning of `B`'s constructor `c`. -/
def datB (dm : DataModel) (c : Nat) : Sem := .dat "B" (recB dm) c []

/-- The meaning of the type `B`. -/
def tyBM (dm : DataModel) : TyM := dm.tyR declB (recB dm)

/-- **What the reference's run of `Not`'s body reads of its state**: no live label, nothing held, the top frame
read `RN` with two bindings, `b` at `(1, 1)` holding `ρ 0`. -/
structure RefNot (ρ : Assignment) (φ : Future) (g : Sem) (s : SState) : Prop where
  live : s.liveLabels = []
  shape : ∀ p, s.shape p = none
  scope : scopeOf s = RN
  resolve0 : resolve s (.var 0) = some (.bind 1 1, [])
  top : ∃ fr, s.env.getLast? = some fr ∧ fr.binds.length = 2
  topIdx : s.topIdx = 1
  valB : s.valAt (.bind 1 1) φ = ρ 0
  valSelf : s.valAt (.bind 1 0) φ = g

/-! ## The constructors of `B` -/

/-- **Every constructor of `B` is a member of `B`**, in every data model: its constructors have no field. -/
theorem datB_mem (dm : DataModel) {c : Nat} (hc : c < 2) : datB dm c ∈ₛ[dm.read] tyBM dm := by
  unfold tyBM
  rw [DataModel.mem_tyR dm declB (recB dm) rfl]
  show DataLib.Mem dm.sig declB (recB dm) (datB dm c)
  rw [DataLib.mem_iff]
  refine ⟨⟨c, hc⟩, [], rfl, ?_⟩
  rcases c with _ | _ | c
  · rfl
  · rfl
  · omega

/-- **The members of `B` are its two constructors**, in every data model. -/
theorem mem_B (dm : DataModel) {v : Sem} (h : v ∈ₛ[dm.read] tyBM dm) : ∃ c, c < 2 ∧ v = datB dm c := by
  unfold tyBM at h
  rw [DataModel.mem_tyR dm declB (recB dm) rfl] at h
  obtain ⟨⟨c, hc⟩, fs, rfl, hf⟩ := (DataLib.mem_iff _ _ _ _).1 h
  have hfs : fs = [] := by
    have : DataLib.arity declB c = 0 := by
      rcases c with _ | _ | c
      · rfl
      · rfl
      · exact absurd hc (by simp [declB])
    rw [this] at hf; exact hf
  subst hfs
  exact ⟨c, hc, rfl⟩

section
variable {K : RunCtx} {ρ : Assignment} {φ : Future} {s : SState}

/-- **A constructor of `B` in an arm**: from any state, in a context whose declarations find `B`, at a table not
erasing it, the run gives the tree at `B`'s record and type and keeps the state. -/
theorem runCtorB (hΓ : K.Γ.find? (·.name == "B") = some declB) {c : Nat} (hc : c < 2) {h : Hint}
    (hfl : K.D.flags (scopeOf s) (.ctor "B" c h [] []) = (false, false)) (tl : Bool) (hint : TyS) :
    runT K ρ φ tl hint (.ctor "B" c h [] []) s = some ((datB K.dm c, .plain (tyBM K.dm)), s) := by
  rw [runT]
  simp only [SM.erasedIf, SM.stmtIf, hfl, Bool.false_eq_true, if_false]
  rw [hΓ]
  have hmem := datB_mem K.dm hc
  simp [runParams, runFields, ctorOut, SM.strictS, declB, bind, Option.bind, pure, datB, tyBM, recB,
    DataModel.ctorR] at hmem ⊢
  exact hmem

/-! ## The match -/

theorem RefNot.access {g : Sem} (h : RefNot ρ φ g s) (pos : Pos) (hit : List Step → Bool) : s.access pos hit = s :=
  access_noSites (fun l hl => by rw [h.live] at hl; cases hl)

theorem RefNot.accessOk {g : Sem} (h : RefNot ρ φ g s) (pos : Pos) (hit : List Step → Bool) : AccessOk K φ s pos hit :=
  accessOk_noSites (fun l hl => by rw [h.live] at hl; cases hl)

theorem RefNot.typedFuture {g : Sem} (h : RefNot ρ φ g s) : s.typedFuture φ = φ := by
  funext l; unfold SState.typedFuture; rw [h.live]; simp

theorem RefNot.lentFuture {g : Sem} (h : RefNot ρ φ g s) : s.lentFuture φ = φ := by
  funext l; unfold SState.lentFuture; rw [h.live]; simp

theorem RefNot.varPos0 {g : Sem} (h : RefNot ρ φ g s) : s.varPos 0 = some (.bind 1 1) := by
  obtain ⟨fr, hfr, hl⟩ := h.top
  unfold SState.varPos; rw [hfr]; dsimp only; rw [hl, h.topIdx]; rfl

theorem RefNot.varPos1 {g : Sem} (h : RefNot ρ φ g s) : s.varPos 1 = some (.bind 1 0) := by
  obtain ⟨fr, hfr, hl⟩ := h.top
  unfold SState.varPos; rw [hfr]; dsimp only; rw [hl, h.topIdx]; rfl

/-- Nothing is moved in the top frame at the match's start: `b` holds a constructor of `B`, the function's own
binding a meaning with no moved part. -/
theorem RefNot.movedPlaces {g : Sem} (h : RefNot ρ φ g s) {c : Nat} (h0 : ρ 0 = datB K.dm c)
    (hg : ∀ q, Sem.movedIn g q = []) : Ochr.Meaning.movedPlaces φ s = [] := by
  obtain ⟨fr, hfr, hl⟩ := h.top
  unfold Ochr.Meaning.movedPlaces; rw [hfr]; dsimp only; rw [hl]
  simp [List.range_succ, h.varPos0, h.varPos1, h.lentFuture, h.valB, h.valSelf, h.shape, h0, hg, datB, Sem.movedIn,
    Sem.movedInFields]

/-- **The match, at both tags**: on `T` the arm `F`, on `F` the arm `T`; nothing is dropped and the state is kept.
In tail position, at any hint. -/
theorem runNot (hd : ParDecNot K.D) (hΓ : K.Γ.find? (·.name == "B") = some declB) {g : Sem} (h : RefNot ρ φ g s)
    (hg : ∀ q, Sem.movedIn g q = []) (hint : TyS) {c : Nat} (hc : c < 2) (h0 : ρ 0 = datB K.dm c) :
    runT K ρ φ true hint bodyNot s = some ((datB K.dm (1 - c), .plain (tyBM K.dm)), s) := by
  have hfind : K.Γ.find? (·.name == "B") = some declB := hΓ
  have hfl : K.D.flags (scopeOf s) bodyNot = (false, false) := by rw [h.scope]; exact hd.1
  have htag : TagOk K φ (.var 0) s := by unfold TagOk; rw [h.resolve0]; exact h.accessOk _ _
  have hone : oneCtor K.Γ "B" = false := by unfold oneCtor; rw [hΓ]; rfl
  have hmv := h.movedPlaces h0 hg
  have hjm : K.D.joinMoves (scopeOf s) [] bodyNot = [] := by rw [h.scope]; exact hd.2.2.2
  have htg : SM.guarded (TagOk K φ (.var 0)) (tagOf K φ (.var 0) indTag) s = some (.el0 Nat c, s) := by
    rw [SM.guarded_of htag]; unfold tagOf; rw [h.resolve0]; dsimp only
    rw [h.access, h.typedFuture, h.valB, h0]; rfl
  have harm : runArm K ρ φ true hint c
      [(⟨"T"⟩, .ctor "B" 1 ⟨"F"⟩ [] []), (⟨"F"⟩, .ctor "B" 0 ⟨"T"⟩ [] [])] s =
      some ((datB K.dm (1 - c), .plain (tyBM K.dm)), s) := by
    rcases c with _ | _ | c
    · simp only [runArm, if_true]
      exact runCtorB hfind (by decide) (by rw [h.scope]; exact hd.2.1) _ _
    · simp only [runArm, if_true, Nat.add_one_ne_zero, if_false, Nat.add_sub_cancel]
      exact runCtorB hfind (by decide) (by rw [h.scope]; exact hd.2.2.1) _ _
    · omega
  show runT K ρ φ true hint (.matchInd (.var 0) "B" _) s = _
  rw [runT]
  simp only [SM.erasedIf, SM.stmtIf, ← show bodyNot = .matchInd (.var 0) "B" _ from rfl, hfl, Bool.false_eq_true,
    if_false]
  rw [htg]
  have hme : ∀ t, optCheck (MatchEntryOk K φ false t s) = some ⟨⟩ := fun t => by
    unfold optCheck; rw [if_pos]; intro h'; cases h'
  have hent : ∀ t, matchEntry K φ false t s = (s, fun _ s₂ => s₂) := fun _ => rfl
  have hjd : joinDrop K φ [] bodyNot s = s := by unfold joinDrop; rw [hjm]; rfl
  have hjok : optCheck ((Sem.el0 Nat c).isProof = true ∨ false = true ∨ JoinDropOk K φ [] bodyNot s) = some ⟨⟩ := by
    unfold optCheck; rw [if_pos]; right; right; unfold JoinDropOk; rw [hjm]; trivial
  simp only [bind, Option.bind, Bool.not_true, Bool.false_and, hme, hent, tailHint_true, harm, hmv, hone, hjok,
    hjd, Sem.asNat_el0]
  rw [hme, hjok]; rfl

end

end Ochr.Meaning.Steps.Form.ColumnNot
