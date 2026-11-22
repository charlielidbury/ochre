import Ochr.Meaning.Steps.DataBoxModel
import Ochr.Meaning.Steps.DataNotRun

/-!
# A data type with a field: the reference's runs of `Wrap`'s and `Unbox`'s bodies (lead21, 2026-11-22; docs/31 D148)

From every reference state that reads like one related to the body's start state, at a table deciding as the
checker does, in a context whose declarations are `[Box]` and whose record gives `Box`'s field the `Nat` leaf
(`shape_box`, from the data-model hypothesis):
- `runWrap`: `MkBox(#0)`: the field's read moves `n` (`setContent` at the root), the constructor clause builds the
  tree `MkBox(a)` at `Box`'s record and type after its strict test (`datBox_mem`); the result and the state with
  `n` moved;
- `runUnbox`: `match #0 { MkBox => #0.n }`: a one-constructor match has no entry and no join (D93, `oneCtor`); the
  arm reads the place `b.n` (the field step of `Sem.step`, at the type the record gives the field: `Nat`), which
  MOVES it: `setContent` at the path `[.n]` writes `moved` into the tree, the partial move the checker's
  `MkBox(⊥)` is.
-/

namespace Ochr.Meaning.Steps.Form.ColumnBox

open Ochr Ochr.Meaning Ochr.Meaning.Steps Ochr.Meaning.Steps.Form

/-- The top frames' readings. -/
abbrev RW : List DeclInfo := [.other, .pi (.ind "Box" [])]
abbrev RU : List DeclInfo := [.ind "Box" [], .pi .other]

/-- The place `b.n` and its read. -/
abbrev pbn : Place := .field fieldN (.var 0)

/-- **The decisions the reference's run of `Wrap`'s body reads.** -/
def ParDecWrap (D : Decisions) : Prop :=
  D.flags RW bodyWrap = (false, false) ∧ D.flags RW (.place (.var 0)) = (false, false) ∧
    D.copy (D.placeDecl RW (.var 0)) = false

/-- **The decisions the reference's run of `Unbox`'s body reads.** -/
def ParDecUnbox (D : Decisions) : Prop :=
  D.flags RU bodyUnbox = (false, false) ∧ D.flags RU (.place pbn) = (false, false) ∧
    D.copy (D.placeDecl RU pbn) = false

/-- **What the reference's runs read of their state**: no live label, nothing held, the top frame read `sc` with two
bindings, the parameter at `(1, 1)` holding `x` at the type `T`. -/
structure RefBox (sc : List DeclInfo) (φ : Future) (x : Sem) (T : TyM) (s : SState) : Prop where
  live : s.liveLabels = []
  shape : ∀ p, s.shape p = none
  scope : scopeOf s = sc
  top : ∃ fr, s.env.getLast? = some fr ∧ fr.binds.length = 2
  topIdx : s.topIdx = 1
  val : s.valAt (.bind 1 1) φ = x
  ty : (s.tyAt (.bind 1 1)).m = T

section
variable {sc : List DeclInfo} {φ : Future} {x : Sem} {T : TyM} {s : SState}

theorem RefBox.access (h : RefBox sc φ x T s) (pos : Pos) (hit : List Step → Bool) : s.access pos hit = s :=
  access_noSites (fun l hl => by rw [h.live] at hl; cases hl)

theorem RefBox.accessOk (h : RefBox sc φ x T s) (K : RunCtx) (pos : Pos) (hit : List Step → Bool) :
    AccessOk K φ s pos hit :=
  accessOk_noSites (fun l hl => by rw [h.live] at hl; cases hl)

theorem RefBox.typedFuture (h : RefBox sc φ x T s) : s.typedFuture φ = φ := by
  funext l; unfold SState.typedFuture; rw [h.live]; simp

theorem RefBox.typedFut (h : RefBox sc φ x T s) (K : RunCtx) {ψ : Future} (hψ : TypedFut K φ s ψ) : ψ = φ := by
  funext l; exact hψ.1 l (by rw [h.live]; simp)

theorem RefBox.varPos0 (h : RefBox sc φ x T s) : s.varPos 0 = some (.bind 1 1) := by
  obtain ⟨fr, hfr, hl⟩ := h.top
  unfold SState.varPos; rw [hfr]; dsimp only; rw [hl, h.topIdx]; rfl

theorem RefBox.resolve0 (h : RefBox sc φ x T s) : resolve s (.var 0) = some (.bind 1 1, []) := by
  unfold resolve; simp [Place.steps, h.varPos0]

theorem RefBox.resolveBn (h : RefBox sc φ x T s) : resolve s pbn = some (.bind 1 1, [.field fieldN]) := by
  unfold resolve; simp [Place.steps, h.varPos0]

end

section
variable {K : RunCtx} {ρ : Assignment} {φ : Future} {s : SState}

/-- The write a move of `n` makes. -/
noncomputable def moveRoot (K : RunCtx) (s : SState) : SState :=
  s.setAt (.bind 1 1) fun φ' =>
    (Sem.updAt K.dm K.Γ (s.tyAt (.bind 1 1)) (fun _ => .moved) [] (s.valAt (.bind 1 1) φ')).getD .err

/-- The write the arm's move of `b.n` makes. -/
noncomputable def moveBn (K : RunCtx) (s : SState) : SState :=
  s.setAt (.bind 1 1) fun φ' =>
    (Sem.updAt K.dm K.Γ (s.tyAt (.bind 1 1)) (fun _ => .moved) [.field fieldN] (s.valAt (.bind 1 1) φ')).getD .err

/-- **The read of `n` holding a number**, which moves it. -/
theorem runReadN {a : Nat} (h : RefBox RW φ (.el0 Nat a) TyM.nat s) (hfl : K.D.flags RW (.place (.var 0)) = (false, false))
    (hcp : K.D.copy (K.D.placeDecl RW (.var 0)) = false) (tl : Bool) (hint : TyS) :
    runT K ρ φ tl hint (.place (.var 0)) s = some ((.el0 Nat a, { s.tyAt (.bind 1 1) with label := none }), moveRoot K s) := by
  have hco : contentOf K φ (.var 0) s = some ((.el0 Nat a, s.tyAt (.bind 1 1), .bind 1 1, []), s) := by
    unfold contentOf; rw [h.resolve0]; dsimp only
    rw [h.access, h.typedFuture, h.val]; rfl
  have hset : setContent K φ (.bind 1 1) [] .moved s = some (⟨⟩, moveRoot K s) := by
    unfold setContent
    rw [if_pos]
    · rfl
    · intro ψ hψ
      rw [h.typedFut K hψ, h.val, Sem.updAt.eq_def]; rfl
  rw [runT]
  show SM.erasedIf (K.D.flags (scopeOf s) (.place (.var 0)))
    (SM.guarded (ContentOk K φ (.var 0)) (readPlace K φ (.var 0) (K.D.copy (K.D.placeDecl (scopeOf s) (.var 0))))) s = _
  rw [h.scope, hfl, hcp]
  simp only [SM.erasedIf, SM.stmtIf, Bool.false_eq_true, if_false]
  rw [SM.guarded_of (by unfold ContentOk; rw [h.resolve0]; exact h.accessOk K _ _)]
  unfold readPlace
  rw [hco]
  have hwhole : (Sem.el0 Nat a).whole := by simp [Sem.whole]
  have hrg : ReadGood K.dm.read (s.tyAt (.bind 1 1)).m (.el0 Nat a) := by rw [h.ty]; exact .inl ⟨a, rfl⟩
  simp only [bind, Option.bind, hwhole, hrg, not_true_eq_false, if_false, Bool.false_eq_true, List.isEmpty_nil,
    if_true, h.shape, hset]

/-- **`Wrap`'s body**: from `n ↦ a`, the tree `MkBox(a)` at `Box`'s record and type, `n` moved. -/
theorem runWrap (hd : ParDecWrap K.D) (hΓ : K.Γ = [declBox])
    (hsh : K.dm.sig.shape declBox (boxRec K.dm) 0 0 [] = .leaf Nat .nat) (hok : K.dm.RecLeafOk declBox (boxRec K.dm))
    {a : Nat} (h : RefBox RW φ (.el0 Nat a) TyM.nat s) (tl : Bool) (hint : TyS) :
    runT K ρ φ tl hint bodyWrap s = some ((datBox K.dm (.el0 Nat a), .plain (tyBoxM K.dm)), moveRoot K s) := by
  have hfl : K.D.flags (scopeOf s) bodyWrap = (false, false) := by rw [h.scope]; exact hd.1
  have hrd := runReadN (K := K) (ρ := ρ) h hd.2.1 hd.2.2 false (.plain TyM.err)
  have hmem := datBox_mem K.dm hsh hok a
  show runT K ρ φ tl hint (.ctor "Box" 0 ⟨"MkBox"⟩ [] [.place (.var 0)]) s = _
  rw [runT]
  simp only [SM.erasedIf, SM.stmtIf, ← show bodyWrap = .ctor "Box" 0 ⟨"MkBox"⟩ [] [.place (.var 0)] from rfl, hfl,
    Bool.false_eq_true, if_false]
  rw [show K.Γ.find? (·.name == "Box") = some declBox by rw [hΓ]; rfl]
  have hrf : ∀ (T : TyS) (rh : Option Rec), runFields K ρ φ false declBox 0 0 rh [] [] [.place (.var 0)] s =
      some (([.el0 Nat a], []), moveRoot K s) := by
    intro T rh
    simp only [runFields, SM.stmtIf, Bool.false_and, Bool.false_eq_true, if_false, bind, Option.bind]
    rw [runReadN (K := K) (ρ := ρ) h hd.2.1 hd.2.2 false]
    simp only [pure, fieldTerm_box]
    rfl
  have e1 : (declBox.sort == 0) = false := rfl
  have e2 : declBox.params.isEmpty = true := rfl
  have e3 : declBox.params.length = 0 := rfl
  simp only [runParams, pure, bind, Option.bind, List.isEmpty_nil, Bool.not_true, Bool.false_or, e1, e2, e3,
    List.replicate_zero, if_true, hrf (.plain TyM.err)]
  rw [show (if false = true then List.map some ([] : List Sem) else []) = ([] : List (Option Sem)) from rfl,
    hrf (.plain TyM.err)]
  simp only [true_or, if_true, Option.orElse, HOrElse.hOrElse, OrElse.orElse]
  unfold SM.strictS
  simp only [ctorOut, e1, Bool.false_eq_true, if_false, pure]
  exact if_pos hmem

theorem not_ownCarrier_nat (dm : DataModel) : ¬ dm.OwnCarrier Code0.nat := by
  rintro ⟨d, r, h, -⟩; cases h

theorem tyBoxM_dataCode (dm : DataModel) : (tyBoxM dm).dataCode? = some (declBox, boxRec dm) := rfl

/-- **The arm's read of `b.n`** on `b ↦ MkBox(m)`: the number `m` at `Nat`, and `moved` written into the tree. -/
theorem runReadBn (hd : ParDecUnbox K.D) (hΓ : K.Γ = [declBox])
    (hsh : K.dm.sig.shape declBox (boxRec K.dm) 0 0 [] = .leaf Nat .nat) {m : Nat}
    (h : RefBox RU φ (datBox K.dm (.el0 Nat m)) (tyBoxM K.dm) s) (tl : Bool) (hint : TyS) :
    runT K ρ φ tl hint (.place pbn) s = some ((.el0 Nat m, .plain TyM.nat), moveBn K s) := by
  have hfl : K.D.flags (scopeOf s) (.place pbn) = (false, false) := by rw [h.scope]; exact hd.2.1
  have hcp : K.D.copy (K.D.placeDecl (scopeOf s) pbn) = false := by rw [h.scope]; exact hd.2.2
  have hfol : Sem.follow K.dm K.Γ (s.tyAt (.bind 1 1)) (datBox K.dm (.el0 Nat m)) [.field fieldN] =
      some (.el0 Nat m, .plain TyM.nat) := by
    simp only [Sem.follow, Sem.step, datBox, fieldN]
    unfold Sem.stepField
    rw [h.ty, tyBoxM_dataCode]
    simp only [show (declBox.name = "Box" ∧ (0 : Nat) = 0) from ⟨rfl, rfl⟩, if_true, List.getElem?_cons_zero,
      List.take_zero]
    unfold DataModel.readTy
    simp only [List.map_nil]
    rw [hsh]
    simp only [DataModel.shapeReadTy, if_neg (not_ownCarrier_nat K.dm)]
    simp; rfl
  have hco : contentOf K φ pbn s =
      some ((.el0 Nat m, .plain TyM.nat, .bind 1 1, [.field fieldN]), s) := by
    unfold contentOf; rw [h.resolveBn]; dsimp only
    rw [h.access, h.typedFuture, h.val, hfol]; rfl
  have hset : setContent K φ (.bind 1 1) [.field fieldN] .moved s = some (⟨⟩, moveBn K s) := by
    unfold setContent
    rw [if_pos]
    · rfl
    · intro ψ hψ
      rw [h.typedFut K hψ, h.val, Sem.updAt.eq_def]
      simp only [datBox, fieldN]
      show (Option.map _ (Sem.updAt K.dm K.Γ _ _ [] (Sem.el0 Nat m))).isSome = true
      rw [Sem.updAt.eq_def]; rfl
  rw [runT]
  show SM.erasedIf (K.D.flags (scopeOf s) (.place pbn))
    (SM.guarded (ContentOk K φ pbn) (readPlace K φ pbn (K.D.copy (K.D.placeDecl (scopeOf s) pbn)))) s = _
  rw [hfl, hcp]
  simp only [SM.erasedIf, SM.stmtIf, Bool.false_eq_true, if_false]
  rw [SM.guarded_of (by unfold ContentOk; rw [h.resolveBn]; exact h.accessOk K _ _)]
  unfold readPlace
  rw [hco]
  have hwhole : (Sem.el0 Nat m).whole := by simp [Sem.whole]
  have hrg : ReadGood K.dm.read (TyS.plain TyM.nat).m (.el0 Nat m) := .inl ⟨m, rfl⟩
  simp only [bind, Option.bind, hwhole, hrg, not_true_eq_false, if_false, Bool.false_eq_true, List.isEmpty_cons,
    hset]
  rfl

/-- **`Unbox`'s body**: a one-constructor match, no entry and no join; the arm's read of `b.n` gives `m` and moves the
field. In tail position, at any hint. -/
theorem runUnbox (hd : ParDecUnbox K.D) (hΓ : K.Γ = [declBox])
    (hsh : K.dm.sig.shape declBox (boxRec K.dm) 0 0 [] = .leaf Nat .nat) {m : Nat}
    (h : RefBox RU φ (datBox K.dm (.el0 Nat m)) (tyBoxM K.dm) s) (hint : TyS) :
    runT K ρ φ true hint bodyUnbox s = some ((.el0 Nat m, .plain TyM.nat), moveBn K s) := by
  have hfl : K.D.flags (scopeOf s) bodyUnbox = (false, false) := by rw [h.scope]; exact hd.1
  have htag : TagOk K φ (.var 0) s := by unfold TagOk; rw [h.resolve0]; exact h.accessOk K _ _
  have hone : oneCtor K.Γ "Box" = true := by rw [hΓ]; rfl
  have htg : SM.guarded (TagOk K φ (.var 0)) (tagOf K φ (.var 0) indTag) s = some (.el0 Nat 0, s) := by
    rw [SM.guarded_of htag]; unfold tagOf; rw [h.resolve0]; dsimp only
    rw [h.access, h.typedFuture, h.val]; rfl
  have harm : runArm K ρ φ true hint 0 [(⟨"MkBox"⟩, .place pbn)] s =
      some ((.el0 Nat m, .plain TyM.nat), moveBn K s) := by
    simp only [runArm, if_true]; exact runReadBn hd hΓ hsh h true _
  have hme : ∀ t, optCheck (MatchEntryOk K φ false t s) = some ⟨⟩ := fun t => by
    unfold optCheck; rw [if_pos]; intro h'; cases h'
  have hent : ∀ t, matchEntry K φ false t s = (s, fun _ s₂ => s₂) := fun _ => rfl
  have hjok : ∀ e s', optCheck ((Sem.el0 Nat 0).isProof = true ∨ True ∨ JoinDropOk K φ e bodyUnbox s') =
      some ⟨⟩ := fun _ _ => by unfold optCheck; rw [if_pos (.inr (.inl trivial))]
  show runT K ρ φ true hint (.matchInd (.var 0) "Box" _) s = _
  rw [runT]
  simp only [SM.erasedIf, SM.stmtIf, ← show bodyUnbox = .matchInd (.var 0) "Box" _ from rfl, hfl,
    Bool.false_eq_true, if_false]
  rw [htg]
  simp only [bind, Option.bind, Bool.not_true, Bool.false_and, hent, tailHint_true, harm, hone, Sem.asNat_el0]
  rw [hjok, hme]; simp

end

end Ochr.Meaning.Steps.Form.ColumnBox
