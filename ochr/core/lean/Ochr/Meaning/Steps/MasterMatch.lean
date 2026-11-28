import Ochr.Meaning.Steps.MasterTail
import Ochr.Meaning.Steps.MasterLet
import Ochr.Meaning.Steps.MatchAttack
import Ochr.Meaning.HintM

/-!
# The general match step (lead41, 2026-11-28; docs/31 D248 on)

The steps of the master induction at a match, in the form `EvalAt`/`TailAt` have, with every fact each needs named
and classed: (C) about the checker alone, (M) about the model alone, (X) mixed, (T) about the decision table.

**The split at the end of a body** (`TStepMatchNat` at a match the table does not read as a proof; the paper's
[Tail-split], [Tail-gen], [Tail-match] with D119's join in each world; docs/18's principle "worlds are exclusive" and
case 4 "a split on an unknown, and the join"): `tStepMatchNat_data`, from the induction hypothesis at the arms and at the
match itself (after a generalisation), and the facts

* `TailMatchNatInv` (C): `checkTail` of a match on a number, inverted: the scrutinee's access, then by its content a
  known arm with the join's continuation, one world per constructor (the base state of each world, the refinement, the
  join's continuation, the arm's check), or the generalisation of a sealed scrutinee and the check again;
* `MatchTagG` (X): the checker's access for the scrutinee against the reference's `tagOf`, and the tag the reference
  reads against the checker's content;
* `WorldRefineG` (X): a world's start (an earlier world's exit, the refinement to the constructor the assignment
  selects) keeps `Pre` and the relation under the assignment extended at the fresh fields, the goal's meaning, the mode,
  the frames and the readings;
* `JoinContG` (X): the join's continuation (`joinCont`: the drops, then the continuation) against the reference's
  join (`joinDrop`, its strict test `JoinDropOk`);
* `GenTailG` (X): the generalisation of a sealed scrutinee keeps the relation (to the reference state after the tag)
  and the goal's meaning; `MatchReaccessM` (M): the reference's match from the state after its own tag access is the
  match from the start (the access is idempotent);
* `ValsCongrA` (M, as for the `let`).

At EVERY assignment the reference takes the arm of the constructor the assignment gives the unknown, and the checker's
world for that constructor ran (every world must succeed for the check to succeed): the leaf of that world is the
leaf the conclusion names.
-/

namespace Ochr.Meaning.Steps.Form.Master

open Ochr Ochr.Meaning Ochr.Meaning.Steps Ochr.Meaning.Steps.Form

/-! ## The reference's match in tail position, unfolded -/

/-- **The reference's match on a number in tail position, where the table does not erase it**: the tag's access, no
[Entry] (tail position), the arm the tag selects at the match's own hint, the join's drop at the places moved after the
access. -/
theorem runT_matchNat_tailData {K : RunCtx} {ρ : Assignment} {φ : Future} (hint : TyS) (p : Place) (z u : Term)
    {s sA s₁ : SState} {tg : Sem} {r : Res} {c : Nat}
    (hfl : K.D.flags (scopeOf s) (.matchNat p z u) = (false, false))
    (hT : TagOk K φ p s) (htag : tagOf K φ p natTag s = some (tg, sA)) (hc : tg.asNat = some c)
    (harm : runT K ρ φ true hint (if c = 0 then z else u) sA = some (r, s₁))
    (hj : JoinDropOk K φ (movedPlaces φ sA) (.matchNat p z u) s₁) :
    runT K ρ φ true hint (.matchNat p z u) s = some (r, joinDrop K φ (movedPlaces φ sA) (.matchNat p z u) s₁) := by
  have hme : optCheck (MatchEntryOk K φ (!true) (.matchNat p z u) sA) = some ⟨⟩ := by
    unfold optCheck; rw [if_pos]; intro e; cases e
  have hent : matchEntry K φ (!true) (.matchNat p z u) sA = (sA, fun _ s₂ => s₂) := rfl
  have hjo : optCheck (JoinDropOk K φ (movedPlaces φ sA) (.matchNat p z u) s₁) = some ⟨⟩ := by
    unfold optCheck; exact if_pos hj
  rw [runT]
  simp only [SM.erasedIf, SM.stmtIf, hfl, Bool.false_eq_true, if_false]
  rw [SM.guarded_of hT, htag]
  simp only [bind, Option.bind, hent, hc, tailHint_true]
  rw [hme]
  rcases c with _ | c
  · simp only [if_true] at harm
    simp only [harm]; rw [hjo]
  · simp only [Nat.add_one_ne_zero, if_false] at harm
    simp only [harm]; rw [hjo]

/-! ## The facts the split at the end of a body assumes -/

/-- The state a world of a split starts from, before its refinement: the snapshot (the first world), or what leaving an
earlier world restores of it (`exitWorld ⟨stA⟩`, whatever that world's arm left: the snapshot with the counters, the new
unknowns' types and readings and the [Rec] candidates kept). -/
def WorldBase (stA stB : MState) : Prop :=
  stB = stA ∨ ∃ cur bx, Runs (Ochr.exitWorld ⟨stA⟩) cur bx () stB

/-- The refinement of world `c` of a split on the number `σ` (`checkTailAt`'s `.matchNat` at `.abs σ`): `σ := Z`, or
`σ := S(σ')` with `σ'` fresh. -/
def refineNat (n σ : Nat) : Nat → M Unit
  | 0 => Ochr.refine n σ .zero
  | _ + 1 => do let σ' ← Ochr.freshAbsR n .tNat; Ochr.refine n σ (.succ (.abs σ'))

/-- **`checkTail` of a match on a number, inverted** (a fact about the checker alone, NEW, for the machine lane;
guarded in `MatchGuards` below): the type test and the access of the scrutinee (`natScrutinee`, `accessPath`,
`accessNeutralHead`), then by its content (never `⊥`: `matchContent` fails there; nothing else at a place of type `Nat`):
* a known constructor: the join's continuation (`joinCont`) and its arm checked with it;
* an unknown `σ`: for EACH world `c` (`Z`, `S`), its base state, its refinement, the join's continuation and its arm
  checked with it (every world runs: the check succeeds only if each does);
* a sealed program or an inert loan: generalised (`generalizeNeutral`), and the match checked again.
The tables at each sub-run's end are aligned where they are at the whole run's end (they only grow; `exitWorld` keeps
the readings). The fuel goes down by two (`checkTail`, `checkTailAt`). -/
def TailMatchNatInv : Prop :=
  ∀ (n : Nat) (p : Place) (z u : Term) (k : Value → Value → M Unit) (st st' : MState) (bh : Nat) (D : Decisions),
    DecTab D st' → Runs (Ochr.checkTail n (.matchNat p z u) k) st bh () st' →
    ∃ (m : Nat) (stA : MState) (bA : Nat), m + 2 ≤ n ∧
      Runs (do Ochr.natScrutinee m p; Ochr.accessPath m p; Ochr.accessNeutralHead m p) st bA () stA ∧ DecTab D stA ∧
      ((∃ c, (ckContent stA.env p = some .zero ∧ c = 0 ∨ (∃ w, ckContent stA.env p = some (.succ w)) ∧ c = 1) ∧
          ∃ (kc : Value → Value → M Unit) (stJ st₁ : MState) (bj b₁ : Nat),
            Runs (Ochr.joinCont m (.matchNat p z u) k) stA bj kc stJ ∧
            Runs (Ochr.checkTail m (if c = 0 then z else u) kc) stJ b₁ () st₁ ∧ DecTab D st₁) ∨
       (∃ σ, ckContent stA.env p = some (.abs σ) ∧ ∀ c, c < 2 →
          ∃ (stB stW stJ st₁ : MState) (kc : Value → Value → M Unit) (bw bj b₁ : Nat),
            WorldBase stA stB ∧ Runs (refineNat m σ c) stB bw () stW ∧ DecTab D stW ∧
            Runs (Ochr.joinCont m (.matchNat p z u) k) stW bj kc stJ ∧
            Runs (Ochr.checkTail m (if c = 0 then z else u) kc) stJ b₁ () st₁ ∧ DecTab D st₁) ∨
       (∃ (v : Value) (σ : Nat) (stG st₁ : MState) (bg b₁ : Nat),
          ((∃ t', v = .sealed t') ∨ (∃ l, v = .loan l)) ∧ ckContent stA.env p = some v ∧
          Runs (Ochr.generalizeNeutral m p v) stA bg σ stG ∧ DecTab D stG ∧
          Runs (Ochr.checkTail m (.matchNat p z u) k) stG b₁ () st₁ ∧ DecTab D st₁))

/-- **`joinCont` reads the state and builds a continuation that grows the tables where the given one does** (a fact
about the checker alone, NEW): the static join is computed on the side (`staticJoin` under `withLive`), so the kernel,
the mode and the tail flags are kept; the continuation drops (`movedPlace`, `dropAtJoin`: machine code) and then calls
the given one. -/
def JoinContInv : Prop :=
  ∀ (m : Nat) (t : Term) (k kc : Value → Value → M Unit) (stW stJ : MState) (bj : Nat),
    Runs (Ochr.joinCont m t k) stW bj kc stJ →
    Kern stW stJ ∧ ModeEq stW stJ ∧ stJ.tailNext = stW.tailNext ∧ stJ.tailDecl = stW.tailDecl ∧
      stJ.typing = stW.typing ∧ ((∀ v T, GrowsM (k v T)) → ∀ v T, GrowsM (kc v T))

/-- **The table reads a match as a proof exactly when it erases it, and its arms as proofs only if it** (a fact about the
table, NEW; read true of the checker's: `preFlags` erases a non-call exactly when it is a proof, and `declOf`'s join of
the arms' readings is a proof when they all are, a conflict when some are, `.any` arms aside, which the instance reads
`(false, false)`). -/
def MatchFlagsT (D : Decisions) : Prop :=
  ∀ (sc : List DeclInfo) (p : Place) (z u : Term),
    (D.flags sc (.matchNat p z u)).1 = (D.flags sc (.matchNat p z u)).2 ∧
    ((D.flags sc (.matchNat p z u)).2 = false → (D.flags sc z).2 = false ∧ (D.flags sc u).2 = false)

/-- **The scrutinee's access and its tag** (mixed, NEW): the checker's type test and access of `p` (`natScrutinee`,
`accessPath`, `accessNeutralHead`: on the path, at the place, inside a neutral at its head) against the reference's
`tagOf` (its access for the tag, `tagHit`; its strict test `TagOk`): the relation after, under an extension (an end's
[Repack] may make unknowns), what a run keeps, and the tag the reference reads against the checker's content: `Z` reads
`0`, `S(w)` reads `1`, an unknown a tag below two (the assignment's value's). Its parts: `AccessG`'s at the match's
grain (the matching ends of [Access]), and the content's meaning (`Rel.sim` at the scrutinee). -/
def MatchTagG : Prop :=
  ∀ (K : RunCtx) (ρ : Assignment) (φ : Future) (π : Nat → Nat) (st stA : MState) (s : SState) (p : Place) (m bA : Nat),
    ModeR st → 0 < st.env.size → Pre K ρ st → Rel K ρ φ π st s → Strict.SGood K.dm K.Γ φ s → DecTab K.D stA →
    Runs (do Ochr.natScrutinee m p; Ochr.accessPath m p; Ochr.accessNeutralHead m p) st bA () stA →
    TagOk K φ p s ∧ ∃ (tg : Sem) (sA : SState) (ρA : Assignment) (ΔA : Nat → TyS) (πA : Nat → Nat),
      tagOf K φ p natTag s = some (tg, sA) ∧ Ext K ρ π st stA ρA ΔA πA ∧ Kept st stA ∧
      stA.tailNext = st.tailNext ∧ stA.tailDecl = st.tailDecl ∧
      hintM { K with Δ := ΔA } ρA stA.goal = hintM K ρ st.goal ∧
      Pre { K with Δ := ΔA } ρA stA ∧ Rel { K with Δ := ΔA } ρA φ πA stA sA ∧
      (ckContent stA.env p = some .zero → tg.asNat = some 0) ∧
      (∀ w, ckContent stA.env p = some (.succ w) → tg.asNat = some 1) ∧
      (∀ σ, ckContent stA.env p = some (.abs σ) → ∃ c, tg.asNat = some c ∧ c < 2)

/-- **A world's start** (mixed, NEW; the paper's [Split] premise "Ω₁[σ := rᵢ]", docs/18's principle "worlds are
exclusive"): from the state after the scrutinee's access, related to the reference's after its tag, whose tag is `c`,
the checker's world `c` (its base, then its refinement `σ := Z` or `σ := S(σ')`) keeps `Pre` and the relation to the
SAME reference state under the assignment extended at the fresh field (the predecessor of the assignment's value), the
goal's meaning, the mode, the frames and the readings. Its parts: the refinement keeps every meaning (the old
`refine_step_stmt`, with the re-run of every sealed program that mentions `σ`, case 3's `SealRerunG`), the path
condition recorded is met by the extension, and an earlier world's exit restores the snapshot (`exitWorld_step_stmt`). -/
def WorldRefineG : Prop :=
  ∀ (K : RunCtx) (ρ : Assignment) (φ : Future) (π : Nat → Nat) (stA stB stW : MState) (s sA : SState) (p : Place)
    (σ c m bw : Nat) (tg : Sem),
    0 < stA.env.size → Pre K ρ stA → Rel K ρ φ π stA sA → Strict.SGood K.dm K.Γ φ sA →
    tagOf K φ p natTag s = some (tg, sA) → ckContent stA.env p = some (.abs σ) → tg.asNat = some c →
    WorldBase stA stB → DecTab K.D stW → Runs (refineNat m σ c) stB bw () stW →
    ∃ (ρW : Assignment) (ΔW : Nat → TyS), Ext K ρ π stA stW ρW ΔW π ∧ Kept stA stW ∧
      stW.tailNext = stA.tailNext ∧ stW.tailDecl = stA.tailDecl ∧
      hintM { K with Δ := ΔW } ρW stW.goal = hintM K ρ stA.goal ∧
      Pre { K with Δ := ΔW } ρW stW ∧ Rel { K with Δ := ΔW } ρW φ π stW sA

/-- **The join at the end of an arm** (mixed, NEW; the paper's [Join] in tail position, D119's `joinCont`; docs/18
case 4, "what survives the join"): from the world's start (`stW`, related to the reference's state after the tag, `sA`),
the continuation `joinCont` built there, run at the arm's leaf (where the arm's result `v : T` is related to the
reference's arm result, the states after related with `v` in flight), drops what the join says (each place re-rooted by
`movedPlace`, then `dropAtJoin`) and calls the given continuation; the reference's join (`joinDrop` at the places moved
after its tag, `movedPlaces φ sA`, its strict test `JoinDropOk`) is matched, the value keeping its meaning, type and
label, under an extension (`movedPlace` may η-refine or generalise). Its parts: the join's entry and list are the same on
both sides (`joinEntry_stmt`, `Decisions.joinMoves` aligned with `jdMoves`, the scope kept by the arm), one drop
(`dropOne_step_stmt` in this form), the drops' strict tests from the checker's (a drop that would end a borrow the
result holds is an error on both sides). -/
def JoinContG : Prop :=
  ∀ (K : RunCtx) (ρ : Assignment) (φ : Future) (π : Nat → Nat) (stW stJ : MState) (sA : SState) (t : Term)
    (k kc : Value → Value → M Unit) (m bj : Nat),
    0 < stW.env.size → Pre K ρ stW → Rel K ρ φ π stW sA → Runs (Ochr.joinCont m t k) stW bj kc stJ →
    ∀ (ρ₁ : Assignment) (Δ₁ : Nat → TyS) (π₁ : Nat → Nat) (stl stk : MState) (v T : Value) (r : Res) (s₁ : SState)
      (bk : Nat),
      Ext K ρ π stJ stl ρ₁ Δ₁ π₁ → Kept stJ stl →
      meanV { K with Δ := Δ₁ } ρ₁ (fun l => φ (π₁ l)) r.2 v = r.1 → StrAgree { K with Δ := Δ₁ } ρ₁ T r.2 →
      r.2.label = (Value.heldLabel v).map π₁ →
      Pre { K with Δ := Δ₁ } ρ₁ (stl.withTempT v (some T)) → Rel { K with Δ := Δ₁ } ρ₁ φ π₁ (stl.withTempT v (some T)) s₁ →
      Strict.SGood K.dm K.Γ φ s₁ → Runs (kc v T) stl bk () stk →
      JoinDropOk K φ (movedPlaces φ sA) t s₁ ∧
      ∃ (stl₂ : MState) (ρ₂ : Assignment) (Δ₂ : Nat → TyS) (π₂ : Nat → Nat),
        Ext { K with Δ := Δ₁ } ρ₁ π₁ stl stl₂ ρ₂ Δ₂ π₂ ∧ Kept stl stl₂ ∧
        meanV { K with Δ := Δ₂ } ρ₂ (fun l => φ (π₂ l)) r.2 v = r.1 ∧ StrAgree { K with Δ := Δ₂ } ρ₂ T r.2 ∧
        r.2.label = (Value.heldLabel v).map π₂ ∧
        Pre { K with Δ := Δ₂ } ρ₂ (stl₂.withTempT v (some T)) ∧
        Rel { K with Δ := Δ₂ } ρ₂ φ π₂ (stl₂.withTempT v (some T)) (joinDrop K φ (movedPlaces φ sA) t s₁) ∧
        ∃ bk' stk', Runs (k v T) stl₂ bk' () stk'

/-- **A sealed scrutinee generalised at the end of a body** (mixed, NEW; the paper's [Tail-gen], D34's record a path
condition): from the state after the scrutinee's access, holding a sealed program (or an inert loan) there, the
checker's `generalizeNeutral` keeps `Pre` and the relation to the SAME reference state under the assignment extended at
the fresh `σ` by the program's meaning (which the reference holds at the scrutinee: the meaning is a member, `SGood`),
the goal's meaning, the mode, the frames and the readings (the old `generalizeNeutral_step_stmt` in this form). -/
def GenTailG : Prop :=
  ∀ (K : RunCtx) (ρ : Assignment) (φ : Future) (π : Nat → Nat) (stA stG : MState) (sA : SState) (p : Place) (v : Value)
    (σ m bg : Nat),
    0 < stA.env.size → Pre K ρ stA → Rel K ρ φ π stA sA → Strict.SGood K.dm K.Γ φ sA →
    ckContent stA.env p = some v → ((∃ t', v = .sealed t') ∨ (∃ l, v = .loan l)) →
    DecTab K.D stG → Runs (Ochr.generalizeNeutral m p v) stA bg σ stG →
    ∃ (ρG : Assignment) (ΔG : Nat → TyS), Ext K ρ π stA stG ρG ΔG π ∧ Kept stA stG ∧
      stG.tailNext = stA.tailNext ∧ stG.tailDecl = stA.tailDecl ∧
      hintM { K with Δ := ΔG } ρG stG.goal = hintM K ρ stA.goal ∧
      Pre { K with Δ := ΔG } ρG stG ∧ Rel { K with Δ := ΔG } ρG φ π stG sA

/-- **The reference's match from the state after its own tag access is the match from the start** (a fact about the
model, NEW; read true: the access for the tag is idempotent, nothing is reached a second time, the scope is the same, and
where the table does not erase the match no state is restored). Used where the checker checks the match again after
generalising its scrutinee. -/
def MatchReaccessM : Prop :=
  ∀ (K : RunCtx) (ρ : Assignment) (φ : Future) (tl : Bool) (hint : TyS) (p : Place) (z u : Term) (s sA : SState)
    (tg : Sem),
    K.D.flags (scopeOf s) (.matchNat p z u) = (false, false) →
    TagOk K φ p s → tagOf K φ p natTag s = some (tg, sA) →
    runT K ρ φ tl hint (.matchNat p z u) sA = runT K ρ φ tl hint (.matchNat p z u) s

/-! ## The split at the end of a body, for a match the table does not read as a proof -/

section
variable {K : RunCtx} {φ : Future}

/-- **One world's arm, to the match's leaf**: from a world's start `stW` (related to the reference's state after the tag,
under an extension of the start's assignment), the arm's check with the join's continuation gives, by the induction
hypothesis at the arm and `JoinContG`, the match's leaf: the reference's match succeeds (its tag selecting this arm),
`Out` holds where the given continuation runs, and the run keeps what `Kept` asks. -/
theorem matchArm_leaf (hJI : JoinContInv) (hJ : JoinContG) (hVC : ValsCongrA) (hc : Strict.FundCtx K)
    {n m : Nat} (ih : IH K φ n) (hmn : m < n) {ρ : Assignment} {π : Nat → Nat} {st stW stJ st₁ : MState}
    {s sA : SState} {p : Place} {z u : Term} {k kc : Value → Value → M Unit} {tg : Sem} {c bj b₁ : Nat}
    {ρW : Assignment} {ΔW : Nat → TyS} {πW : Nat → Nat}
    (hfl : K.D.flags (scopeOf s) (.matchNat p z u) = (false, false))
    (harmfl : (K.D.flags (scopeOf sA) (if c = 0 then z else u)).2 = false)
    (hTok : TagOk K φ p s) (htag : tagOf K φ p natTag s = some (tg, sA)) (hcn : tg.asNat = some c)
    (hm : ModeR st) (hne : 0 < st.env.size) (hk : ∀ v T, GrowsM (k v T)) (hSA : Strict.SGood K.dm K.Γ φ sA)
    (hv : (Term.matchNat p z u).valsOk (Strict.ValsP K ρ φ)) (hab : (Term.matchNat p z u).absBelow st.absTy.size)
    (hnh : (Term.matchNat p z u).hasHolePrim = false)
    (heW : Ext K ρ π st stW ρW ΔW πW) (hKW : Kept st stW) (htnW : stW.tailNext = false) (htdW : stW.tailDecl = none)
    (hgW : hintM { K with Δ := ΔW } ρW stW.goal = hintM K ρ st.goal)
    (hpW : Pre { K with Δ := ΔW } ρW stW) (hrW : Rel { K with Δ := ΔW } ρW φ πW stW sA)
    (hjc : Runs (Ochr.joinCont m (.matchNat p z u) k) stW bj kc stJ)
    (hD₁ : DecTab K.D st₁) (harm : Runs (Ochr.checkTail m (if c = 0 then z else u) kc) stJ b₁ () st₁) :
    TailOutK K ρ φ π st s (runT K ρ φ true (hintM K ρ st.goal) (.matchNat p z u)) k := by
  obtain ⟨hkJ, hmJ, htnJ, htdJ, -, hgrow⟩ := hJI m _ k kc stW stJ bj hjc
  have hneW : 0 < stW.env.size := by rw [hKW.size]; exact hne
  -- the arm's entry conditions at the world's continuation state
  have hva : (if c = 0 then z else u).valsOk (Strict.ValsP K ρ φ) := by
    split
    · exact hv.1
    · exact hv.2
  have haba : (if c = 0 then z else u).absBelow st.absTy.size := fun σ hσ => hab σ (by
    split at hσ <;> simp [Term.anyAtom, hσ])
  have hnha : (if c = 0 then z else u).hasHolePrim = false := by
    simp only [Term.hasHolePrim, Bool.or_eq_false_iff] at hnh
    split
    · exact hnh.1
    · exact hnh.2
  have hagree : ∀ σ, (if c = 0 then z else u).anyAtom (· == .abs σ) = true → AgreeA K ΔW ρ ρW σ := fun σ hσ => by
    obtain ⟨a, d⟩ := heW.agree σ (haba σ hσ)
    exact ⟨a.symm, d.symm⟩
  have hO := (ih m hmn ΔW ρW).2 (if c = 0 then z else u) stJ kc sA πW b₁ st₁
    (hm.of_modeEq (hKW.mode.trans hmJ)) (htnJ.trans htnW) (by rw [← ColumnC.size_of_erase hkJ.env]; exact hneW)
    (htdJ.trans htdW) (hgrow hk) (hpW.of_kern hkJ) (hrW.of_kern hkJ) hSA (hVC K ΔW ρ ρW φ _ hagree hva)
    (absBelow_mono haba (by rw [← hkJ.absTy]; exact heW.abs)) hnha hD₁ harm
  obtain ⟨stl, v, T, ⟨bk, stk, hkr⟩, ⟨ρ₁, Δ₁, π₁, r, s₁, he₁, hx₁, hm₁, ha₁, hl₁, hp₁, hr₁⟩, hK₁⟩ := hO.1 harmfl
  -- the arm's reference run at the start's context and hint
  have hgJ : hintM { K with Δ := ΔW } ρW stJ.goal = hintM K ρ st.goal := by rw [← hkJ.goal]; exact hgW
  rw [hgJ] at hx₁
  have hx₁' : runT K ρ φ true (hintM K ρ st.goal) (if c = 0 then z else u) sA = some (r, s₁) := by
    rw [runT_congrA K ΔW ρ ρW φ true _ _ sA hagree]; exact hx₁
  obtain ⟨-, -, -, hS₁⟩ := Strict.fund_all hc _ hva true _ sA s₁ r hSA hx₁'
  -- the join, at the arm's leaf
  obtain ⟨hjok, stl₂, ρ₂, Δ₂, π₂, he₂, hK₂, hm₂, ha₂, hl₂, hp₂, hr₂, bk', stk', hk'⟩ :=
    hJ { K with Δ := ΔW } ρW φ πW stW stJ sA _ k kc m bj hneW hpW hrW hjc ρ₁ Δ₁ π₁ stl stk v T r s₁ bk he₁ hK₁
      hm₁ (ha₁ T rfl) hl₁ hp₁ hr₁ hS₁ hkr
  refine ⟨stl₂, v, T, ⟨bk', stk', hk'⟩, ⟨ρ₂, Δ₂, π₂, r, joinDrop K φ (movedPlaces φ sA) (.matchNat p z u) s₁,
    (heW.trans ((he₁.congr hkJ.absTy hkJ.nextLoan rfl rfl))).trans he₂, ?_, hm₂, fun T' e => by cases e; exact ha₂,
    hl₂, hp₂, hr₂⟩, ((hKW.trans (Kept.of_kern hkJ hmJ)).trans hK₁).trans hK₂⟩
  exact runT_matchNat_tailData _ p z u hfl hTok htag hcn hx₁' hjok

end

section
variable {K : RunCtx} {φ : Future}

/-- **The split at the end of a body, for a match on a number the table does not read as a proof, in general**
(`TStepMatchNat`'s full form, `TailOutK`): from the induction hypothesis at fuel `n` (at the arms in each world, and at
the match itself after a generalisation), at EVERY assignment. The reference takes the arm of the constructor the
assignment gives the scrutinee (its tag); the checker's world for that constructor ran (each world must succeed); its
leaf is the conclusion's. A known scrutinee is the one-world case; a sealed one is generalised and the match checked
again at less fuel. ASSUMES 8 facts: `TailMatchNatInv`, `JoinContInv` (checker), `MatchFlagsT` (table), `MatchTagG`,
`WorldRefineG`, `JoinContG`, `GenTailG` (mixed), `MatchReaccessM`, `ValsCongrA` (model); and `Strict.FundCtx K`. -/
theorem tStepMatchNat_data (hInv : TailMatchNatInv) (hJI : JoinContInv) (hMF : MatchFlagsT K.D) (hTag : MatchTagG)
    (hW : WorldRefineG) (hJ : JoinContG) (hG : GenTailG) (hRe : MatchReaccessM) (hVC : ValsCongrA)
    (hc : Strict.FundCtx K) {n : Nat} (ih : IH K φ n) (ρ : Assignment) (p : Place) (z u : Term)
    (st : MState) (k : Value → Value → M Unit) (s : SState) (π : Nat → Nat) (bh : Nat) (st' : MState)
    (hm : ModeR st) (htn : st.tailNext = false) (hne : 0 < st.env.size) (htd : st.tailDecl = none)
    (hk : ∀ v T, GrowsM (k v T)) (hp : Pre K ρ st) (hr : Rel K ρ φ π st s) (hS : Strict.SGood K.dm K.Γ φ s)
    (hv : (Term.matchNat p z u).valsOk (Strict.ValsP K ρ φ)) (hab : (Term.matchNat p z u).absBelow st.absTy.size)
    (hnh : (Term.matchNat p z u).hasHolePrim = false) (hD : DecTab K.D st')
    (hrun : Runs (Ochr.checkTail n (.matchNat p z u) k) st bh () st')
    (hfl2 : (K.D.flags (scopeOf s) (.matchNat p z u)).2 = false) :
    TailOutK K ρ φ π st s (runT K ρ φ true (hintM K ρ st.goal) (.matchNat p z u)) k := by
  have hfl : K.D.flags (scopeOf s) (.matchNat p z u) = (false, false) := by
    have h1 := (hMF (scopeOf s) p z u).1
    rw [hfl2] at h1
    exact Prod.ext h1 hfl2
  obtain ⟨m, stA, bA, hmn, hacc, hDA, hcases⟩ := hInv n p z u k st st' bh K.D hD hrun
  obtain ⟨hTok, tg, sA, ρA, ΔA, πA, htag, heA, hKA, htnA, htdA, hgA, hpA, hrA, hZ, hSu, hAb⟩ :=
    hTag K ρ φ π st stA s p m bA hm hne hp hr hS hDA hacc
  have hSA : Strict.SGood K.dm K.Γ φ sA := Strict.sgood_tagOf hS hTok htag
  have hsc : scopeOf sA = scopeOf s := by
    rw [scopeOf_rel hr, scopeOf_rel hrA, hKA.top]
  have harmfl : ∀ c, (K.D.flags (scopeOf sA) (if c = 0 then z else u)).2 = false := fun c => by
    rw [hsc]; obtain ⟨hz, hu⟩ := (hMF (scopeOf s) p z u).2 hfl2
    split
    · exact hz
    · exact hu
  have hneA : 0 < stA.env.size := by rw [hKA.size]; exact hne
  rcases hcases with ⟨c, hcon, kc, stJ, st₁, bj, b₁, hjc, harm, hD₁⟩ | ⟨σ, hσ, hworlds⟩ |
      ⟨v, σ, stG, st₁, bg, b₁, hvs, hcv, hgen, hDG, hre, hD₁⟩
  · -- a known constructor: one world, the access's state
    have hcn : tg.asNat = some c := by
      rcases hcon with ⟨h0, rfl⟩ | ⟨⟨w, h1⟩, rfl⟩
      · exact hZ h0
      · exact hSu w h1
    exact matchArm_leaf hJI hJ hVC hc ih (by omega) hfl (harmfl c) hTok htag hcn hm hne hk hSA hv hab hnh heA hKA
      (htnA.trans htn) (htdA.trans htd) hgA hpA hrA hjc hD₁ harm
  · -- an unknown: the world of the constructor the assignment gives it
    obtain ⟨c, hcn, hc2⟩ := hAb σ hσ
    obtain ⟨stB, stW, stJ, st₁, kc, bw, bj, b₁, hbase, href, hDW, hjc, harm, hD₁⟩ := hworlds c hc2
    obtain ⟨ρW, ΔW, heW, hKW, htnW, htdW, hgW, hpW, hrW⟩ :=
      hW { K with Δ := ΔA } ρA φ πA stA stB stW s sA p σ c m bw tg hneA hpA hrA hSA htag hσ hcn hbase hDW href
    exact matchArm_leaf hJI hJ hVC hc ih (by omega) hfl (harmfl c) hTok htag hcn hm hne hk hSA hv hab hnh
      (heA.trans heW) (hKA.trans hKW) ((htnW.trans htnA).trans htn) ((htdW.trans htdA).trans htd) (hgW.trans hgA)
      hpW hrW hjc hD₁ harm
  · -- a sealed scrutinee: generalised, then the match checked again at less fuel
    obtain ⟨ρG, ΔG, heG, hKG, htnG, htdG, hgG, hpG, hrG⟩ :=
      hG { K with Δ := ΔA } ρA φ πA stA stG sA p v σ m bg hneA hpA hrA hSA hcv hvs hDG hgen
    have habG : st.absTy.size ≤ stG.absTy.size := Nat.le_trans heA.abs heG.abs
    have hagree : ∀ σ', (Term.matchNat p z u).anyAtom (· == .abs σ') = true → AgreeA K ΔG ρ ρG σ' := fun σ' hσ' => by
      obtain ⟨a, d⟩ := (heA.trans heG).agree σ' (hab σ' hσ')
      exact ⟨a.symm, d.symm⟩
    have hO := (ih m (by omega) ΔG ρG).2 (.matchNat p z u) stG k sA πA b₁ st₁
      (hm.of_modeEq (hKA.trans hKG).mode) ((htnG.trans htnA).trans htn) (by rw [(hKA.trans hKG).size]; exact hne)
      ((htdG.trans htdA).trans htd) hk hpG hrG hSA (hVC K ΔG ρ ρG φ _ hagree hv) (absBelow_mono hab habG) hnh hD₁ hre
    obtain ⟨stl, v', T, hkr, ⟨ρ₁, Δ₁, π₁, r, s₁, he₁, hx₁, hm₁, ha₁, hl₁, hp₁, hr₁⟩, hK₁⟩ :=
      hO.1 (by rw [hsc]; exact hfl2)
    rw [hgG.trans hgA] at hx₁
    refine ⟨stl, v', T, hkr, ⟨ρ₁, Δ₁, π₁, r, s₁, (heA.trans heG).trans he₁, ?_, hm₁, ha₁, hl₁, hp₁, hr₁⟩,
      (hKA.trans hKG).trans hK₁⟩
    rw [← hRe K ρ φ true (hintM K ρ st.goal) p z u s sA tg hfl hTok htag,
      runT_congrA K ΔG ρ ρG φ true _ _ sA hagree]
    exact hx₁

end

/-! ## The split at the end of a body, for a match the table reads as a proof (the erased form, D248's ruling (P1)) -/

/-- **The join of a match read as a proof is empty** (table and checker, NEW; probed: `MatchAtk.L11`): its arms are
statements, which move nothing outside their copies (`Decide.jdMoves`), so the table's join list is empty, and the
checker's `joinCont`, at a state whose aligned table reads the match as a proof, returns the continuation itself. -/
def ProofJoinG : Prop :=
  ∀ (D : Decisions),
    (∀ (sc : List DeclInfo) (entry : List Place) (p : Place) (z u : Term),
      (D.flags sc (.matchNat p z u)).2 = true → D.joinMoves sc entry (.matchNat p z u) = []) ∧
    ∀ (m : Nat) (p : Place) (z u : Term) (k kc : Value → Value → M Unit) (stW stJ : MState) (bj : Nat),
      DecTab D stJ → (D.flags (DecideScope.topReadings stW) (.matchNat p z u)).2 = true →
      Runs (Ochr.joinCont m (.matchNat p z u) k) stW bj kc stJ → kc = k

/-- **An arm of a match read as a proof runs to a proof** (a fact about the model, NEW): a successful reference run of
an arm returns the proof token, at a type meaning the true proposition, and leaves the state it started from. Read: an
arm the table reads as a proof runs under `SM.erasedIf` (exactly `(•, prop True)`, the state restored); a proof constant
means `•` at its type, which (I) makes true (`propext`), and reads nothing; an arm read `.any` (a match with no arms)
has no successful run. -/
def ProofArmM : Prop :=
  ∀ (K : RunCtx) (ρ : Assignment) (φ : Future) (hint : TyS) (p : Place) (z u : Term) (s' s₁ : SState) (c : Nat)
    (r : Res),
    (K.D.flags (scopeOf s') (.matchNat p z u)).2 = true →
    runT K ρ φ true hint (if c = 0 then z else u) s' = some (r, s₁) → r.1 = .proof ∧ r.2.m = TyM.prop True ∧ s₁ = s'

/-- **The reference's match from the state after its own tag access gives the same result** (model, NEW; read true:
the access is idempotent; an erased match restores the state it started from, so only the results agree). -/
def MatchReaccessE : Prop :=
  ∀ (K : RunCtx) (ρ : Assignment) (φ : Future) (tl : Bool) (hint : TyS) (p : Place) (z u : Term) (s sA : SState)
    (tg : Sem),
    TagOk K φ p s → tagOf K φ p natTag s = some (tg, sA) →
    (runT K ρ φ tl hint (.matchNat p z u) sA).map Prod.fst = (runT K ρ φ tl hint (.matchNat p z u) s).map Prod.fst

/-- **The reference's match on a number in tail position, where the table reads it as a proof**: the tag's access, the
arm, the empty join, under `SM.erasedIf` (the proof token at `prop True`, the state the match started from). -/
theorem runT_matchNat_tailProof {K : RunCtx} {ρ : Assignment} {φ : Future} (hint : TyS) (p : Place) (z u : Term)
    {s sA s₁ : SState} {tg : Sem} {r : Res} {c : Nat}
    (hfl2 : (K.D.flags (scopeOf s) (.matchNat p z u)).2 = true)
    (hT : TagOk K φ p s) (htag : tagOf K φ p natTag s = some (tg, sA)) (hc : tg.asNat = some c)
    (harm : runT K ρ φ true hint (if c = 0 then z else u) sA = some (r, s₁)) (hr1 : r.1 = .proof)
    (hj : K.D.joinMoves (scopeOf s₁) (movedPlaces φ sA) (.matchNat p z u) = []) :
    runT K ρ φ true hint (.matchNat p z u) s = some ((.proof, .plain (TyM.prop True)), s) := by
  have hme : optCheck (MatchEntryOk K φ (!true) (.matchNat p z u) sA) = some ⟨⟩ := by
    unfold optCheck; rw [if_pos]; intro e; cases e
  have hent : matchEntry K φ (!true) (.matchNat p z u) sA = (sA, fun _ s₂ => s₂) := rfl
  have hjo : optCheck (JoinDropOk K φ (movedPlaces φ sA) (.matchNat p z u) s₁) = some ⟨⟩ := by
    unfold optCheck; rw [if_pos]; unfold JoinDropOk; rw [hj]; trivial
  obtain ⟨r1, r2⟩ := r
  simp only at hr1
  subst hr1
  rw [runT]
  simp only [SM.erasedIf, hfl2, if_true]
  rw [SM.guarded_of hT, htag]
  simp only [bind, Option.bind, hent, hc, tailHint_true]
  rw [hme]
  rcases c with _ | c
  · simp only [if_true] at harm
    simp only [harm]; rw [hjo]
  · simp only [Nat.add_one_ne_zero, if_false] at harm
    simp only [harm]; rw [hjo]

section
variable {K : RunCtx} {φ : Future}

/-- **One world's arm, to the match's leaf, for a match read as a proof** (the erased form): the join is empty, so the
checker's continuation is the given one, and the arm's leaf is the match's; the reference's match succeeds as the
erased run of its arm. -/
theorem matchArm_leafE (hJI : JoinContInv) (hPJ : ProofJoinG) (hPA : ProofArmM) (hVC : ValsCongrA)
    {n m : Nat} (ih : IH K φ n) (hmn : m < n) {ρ : Assignment} {π : Nat → Nat} {st stW stJ st₁ : MState}
    {s sA : SState} {p : Place} {z u : Term} {k kc : Value → Value → M Unit} {tg : Sem} {c bj b₁ : Nat}
    {ρW : Assignment} {ΔW : Nat → TyS} {πW : Nat → Nat}
    (hfl2 : (K.D.flags (scopeOf s) (.matchNat p z u)).2 = true) (hr : Rel K ρ φ π st s)
    (hTok : TagOk K φ p s) (htag : tagOf K φ p natTag s = some (tg, sA)) (hcn : tg.asNat = some c)
    (hsc : scopeOf sA = scopeOf s)
    (hm : ModeR st) (hne : 0 < st.env.size) (hk : ∀ v T, GrowsM (k v T)) (hSA : Strict.SGood K.dm K.Γ φ sA)
    (hv : (Term.matchNat p z u).valsOk (Strict.ValsP K ρ φ)) (hab : (Term.matchNat p z u).absBelow st.absTy.size)
    (hnh : (Term.matchNat p z u).hasHolePrim = false)
    (heW : Ext K ρ π st stW ρW ΔW πW) (hKW : Kept st stW) (htnW : stW.tailNext = false) (htdW : stW.tailDecl = none)
    (hgW : hintM { K with Δ := ΔW } ρW stW.goal = hintM K ρ st.goal)
    (hpW : Pre { K with Δ := ΔW } ρW stW) (hrW : Rel { K with Δ := ΔW } ρW φ πW stW sA) (hDW : DecTab K.D stW)
    (hjc : Runs (Ochr.joinCont m (.matchNat p z u) k) stW bj kc stJ)
    (hD₁ : DecTab K.D st₁) (harm : Runs (Ochr.checkTail m (if c = 0 then z else u) kc) stJ b₁ () st₁) :
    TailOutE K ρ φ π st s (runT K ρ φ true (hintM K ρ st.goal) (.matchNat p z u)) k := by
  obtain ⟨hkJ, hmJ, htnJ, htdJ, -, -⟩ := hJI m _ k kc stW stJ bj hjc
  have hkc : kc = k := (hPJ K.D).2 m p z u k kc stW stJ bj (DecTab.of_kern hkJ hDW)
    (by rw [hKW.top, ← scopeOf_rel hr]; exact hfl2) hjc
  subst hkc
  have hneW : 0 < stW.env.size := by rw [hKW.size]; exact hne
  have hva : (if c = 0 then z else u).valsOk (Strict.ValsP K ρ φ) := by
    split
    · exact hv.1
    · exact hv.2
  have haba : (if c = 0 then z else u).absBelow st.absTy.size := fun σ hσ => hab σ (by
    split at hσ <;> simp [Term.anyAtom, hσ])
  have hnha : (if c = 0 then z else u).hasHolePrim = false := by
    simp only [Term.hasHolePrim, Bool.or_eq_false_iff] at hnh
    split
    · exact hnh.1
    · exact hnh.2
  have hagree : ∀ σ, (if c = 0 then z else u).anyAtom (· == .abs σ) = true → AgreeA K ΔW ρ ρW σ := fun σ hσ => by
    obtain ⟨a, d⟩ := heW.agree σ (haba σ hσ)
    exact ⟨a.symm, d.symm⟩
  have hO := (ih m hmn ΔW ρW).2 (if c = 0 then z else u) stJ kc sA πW b₁ st₁
    (hm.of_modeEq (hKW.mode.trans hmJ)) (htnJ.trans htnW) (by rw [← ColumnC.size_of_erase hkJ.env]; exact hneW)
    (htdJ.trans htdW) hk (hpW.of_kern hkJ) (hrW.of_kern hkJ) hSA (hVC K ΔW ρ ρW φ _ hagree hva)
    (absBelow_mono haba (by rw [← hkJ.absTy]; exact heW.abs)) hnha hD₁ harm
  obtain ⟨stl, v, T, hkr, ⟨ρ₁, Δ₁, π₁, r, s₁, he₁, hx₁, hm₁, ha₁, hp₁⟩, hK₁⟩ := hO.2
  have hgJ : hintM { K with Δ := ΔW } ρW stJ.goal = hintM K ρ st.goal := by rw [← hkJ.goal]; exact hgW
  rw [hgJ] at hx₁
  have hx₁' : runT K ρ φ true (hintM K ρ st.goal) (if c = 0 then z else u) sA = some (r, s₁) := by
    rw [runT_congrA K ΔW ρ ρW φ true _ _ sA hagree]; exact hx₁
  obtain ⟨hr1, hr2, hs₁⟩ := hPA K ρ φ _ p z u sA s₁ c r (by rw [hsc]; exact hfl2) hx₁'
  refine ⟨stl, v, T, hkr, ⟨ρ₁, Δ₁, π₁, (.proof, .plain (TyM.prop True)), s,
    heW.trans (he₁.congr hkJ.absTy hkJ.nextLoan rfl rfl), ?_, ?_, ?_, hp₁⟩, (hKW.trans (Kept.of_kern hkJ hmJ)).trans hK₁⟩
  · exact runT_matchNat_tailProof _ p z u hfl2 hTok htag hcn hx₁' hr1
      ((hPJ K.D).1 _ _ p z u (by rw [hs₁, hsc]; exact hfl2))
  · show meanV _ _ _ (.plain (TyM.prop True)) v = .proof
    rw [Ochr.Meaning.meanV_hintM _ _ _ v (.plain (TyM.prop True)) r.2 hr2.symm, hm₁, hr1]
  · exact ha₁.trans hr2

/-- **The split at the end of a body, for a match on a number the table reads as a proof, in general** (the erased
form `TailOutE`, D248's ruling (P1); a lemma's body: `AddMZero`, `AddZH`): from the induction hypothesis, at EVERY
assignment, as for data (`tStepMatchNat_data`) with the join empty and no relation at the leaf. ASSUMES 9 facts:
`TailMatchNatInv`, `JoinContInv` (checker), `ProofJoinG` (table and checker), `MatchTagG`, `WorldRefineG`, `GenTailG`
(mixed), `ProofArmM`, `MatchReaccessE`, `ValsCongrA` (model). -/
theorem tStepMatchNat_proof (hInv : TailMatchNatInv) (hJI : JoinContInv) (hPJ : ProofJoinG) (hTag : MatchTagG)
    (hW : WorldRefineG) (hG : GenTailG) (hPA : ProofArmM) (hRe : MatchReaccessE) (hVC : ValsCongrA)
    {n : Nat} (ih : IH K φ n) (ρ : Assignment) (p : Place) (z u : Term)
    (st : MState) (k : Value → Value → M Unit) (s : SState) (π : Nat → Nat) (bh : Nat) (st' : MState)
    (hm : ModeR st) (htn : st.tailNext = false) (hne : 0 < st.env.size) (htd : st.tailDecl = none)
    (hk : ∀ v T, GrowsM (k v T)) (hp : Pre K ρ st) (hr : Rel K ρ φ π st s) (hS : Strict.SGood K.dm K.Γ φ s)
    (hv : (Term.matchNat p z u).valsOk (Strict.ValsP K ρ φ)) (hab : (Term.matchNat p z u).absBelow st.absTy.size)
    (hnh : (Term.matchNat p z u).hasHolePrim = false) (hD : DecTab K.D st')
    (hrun : Runs (Ochr.checkTail n (.matchNat p z u) k) st bh () st')
    (hfl2 : (K.D.flags (scopeOf s) (.matchNat p z u)).2 = true) :
    TailOutE K ρ φ π st s (runT K ρ φ true (hintM K ρ st.goal) (.matchNat p z u)) k := by
  obtain ⟨m, stA, bA, hmn, hacc, hDA, hcases⟩ := hInv n p z u k st st' bh K.D hD hrun
  obtain ⟨hTok, tg, sA, ρA, ΔA, πA, htag, heA, hKA, htnA, htdA, hgA, hpA, hrA, hZ, hSu, hAb⟩ :=
    hTag K ρ φ π st stA s p m bA hm hne hp hr hS hDA hacc
  have hSA : Strict.SGood K.dm K.Γ φ sA := Strict.sgood_tagOf hS hTok htag
  have hsc : scopeOf sA = scopeOf s := by rw [scopeOf_rel hr, scopeOf_rel hrA, hKA.top]
  have hneA : 0 < stA.env.size := by rw [hKA.size]; exact hne
  rcases hcases with ⟨c, hcon, kc, stJ, st₁, bj, b₁, hjc, harm, hD₁⟩ | ⟨σ, hσ, hworlds⟩ |
      ⟨v, σ, stG, st₁, bg, b₁, hvs, hcv, hgen, hDG, hre, hD₁⟩
  · have hcn : tg.asNat = some c := by
      rcases hcon with ⟨h0, rfl⟩ | ⟨⟨w, h1⟩, rfl⟩
      · exact hZ h0
      · exact hSu w h1
    exact matchArm_leafE hJI hPJ hPA hVC ih (by omega) hfl2 hr hTok htag hcn hsc hm hne hk hSA hv hab hnh heA hKA
      (htnA.trans htn) (htdA.trans htd) hgA hpA hrA hDA hjc hD₁ harm
  · obtain ⟨c, hcn, hc2⟩ := hAb σ hσ
    obtain ⟨stB, stW, stJ, st₁, kc, bw, bj, b₁, hbase, href, hDW, hjc, harm, hD₁⟩ := hworlds c hc2
    obtain ⟨ρW, ΔW, heW, hKW, htnW, htdW, hgW, hpW, hrW⟩ :=
      hW { K with Δ := ΔA } ρA φ πA stA stB stW s sA p σ c m bw tg hneA hpA hrA hSA htag hσ hcn hbase hDW href
    exact matchArm_leafE hJI hPJ hPA hVC ih (by omega) hfl2 hr hTok htag hcn hsc hm hne hk hSA hv hab hnh
      (heA.trans heW) (hKA.trans hKW) ((htnW.trans htnA).trans htn) ((htdW.trans htdA).trans htd) (hgW.trans hgA)
      hpW hrW hDW hjc hD₁ harm
  · obtain ⟨ρG, ΔG, heG, hKG, htnG, htdG, hgG, hpG, hrG⟩ :=
      hG { K with Δ := ΔA } ρA φ πA stA stG sA p v σ m bg hneA hpA hrA hSA hcv hvs hDG hgen
    have habG : st.absTy.size ≤ stG.absTy.size := Nat.le_trans heA.abs heG.abs
    have hagree : ∀ σ', (Term.matchNat p z u).anyAtom (· == .abs σ') = true → AgreeA K ΔG ρ ρG σ' := fun σ' hσ' => by
      obtain ⟨a, d⟩ := (heA.trans heG).agree σ' (hab σ' hσ')
      exact ⟨a.symm, d.symm⟩
    have hO := (ih m (by omega) ΔG ρG).2 (.matchNat p z u) stG k sA πA b₁ st₁
      (hm.of_modeEq (hKA.trans hKG).mode) ((htnG.trans htnA).trans htn) (by rw [(hKA.trans hKG).size]; exact hne)
      ((htdG.trans htdA).trans htd) hk hpG hrG hSA (hVC K ΔG ρ ρG φ _ hagree hv) (absBelow_mono hab habG) hnh hD₁ hre
    obtain ⟨stl, v', T, hkr, ⟨ρ₁, Δ₁, π₁, r, s₁, he₁, hx₁, hm₁, ha₁, hp₁⟩, hK₁⟩ := hO.2
    rw [hgG.trans hgA, ← runT_congrA K ΔG ρ ρG φ true _ _ sA hagree] at hx₁
    have hmap := hRe K ρ φ true (hintM K ρ st.goal) p z u s sA tg hTok htag
    rw [hx₁] at hmap
    obtain ⟨⟨r', s'⟩, hx', hr'⟩ := Option.map_eq_some_iff.mp hmap.symm
    simp only at hr'
    subst hr'
    exact ⟨stl, v', T, hkr, ⟨ρ₁, Δ₁, π₁, r', s', (heA.trans heG).trans he₁, hx', hm₁, ha₁, hp₁⟩,
      (hKA.trans hKG).trans hK₁⟩

end

/-! ## The step `TStepMatchNat`, assembled -/

/-- **`TStepMatchNat` in general** (a match on a number at the end of a body: the paper's [Tail-split], [Tail-gen],
[Tail-match]; docs/18's principle "worlds are exclusive" and case 4): the full form where the table does not read the
match as a proof (`tStepMatchNat_data`), the erased form where it does (`tStepMatchNat_proof`; D248's ruling (P1)).
ASSUMES 12 facts: `TailMatchNatInv`, `JoinContInv` (checker); `MatchFlagsT`, `ProofJoinG` (table; the latter also
the checker's `joinCont`); `MatchTagG`, `WorldRefineG`, `JoinContG`, `GenTailG` (mixed); `MatchReaccessM`,
`MatchReaccessE`, `ProofArmM`, `ValsCongrA` (model); and `Strict.FundCtx K`. -/
theorem tStepMatchNat_of {K : RunCtx} {φ : Future} (hInv : TailMatchNatInv) (hJI : JoinContInv)
    (hMF : MatchFlagsT K.D) (hPJ : ProofJoinG) (hTag : MatchTagG) (hW : WorldRefineG) (hJ : JoinContG)
    (hG : GenTailG) (hRe : MatchReaccessM) (hRE : MatchReaccessE) (hPA : ProofArmM) (hVC : ValsCongrA)
    (hc : Strict.FundCtx K) : TStepMatchNat K φ := by
  intro n ih Δ ρ p z u st k s π bh st' hm htn hne htd hk hp hr hS hv hab hnh hD hrun
  have ih' : IH { K with Δ := Δ } φ n := ih
  have hc' : Strict.FundCtx { K with Δ := Δ } := ⟨hc.globals, hc.sorts⟩
  refine ⟨fun h2 => tStepMatchNat_data (K := { K with Δ := Δ }) hInv hJI hMF hTag hW hJ hG hRe hVC hc' ih' ρ p z u st k s π bh st' hm htn hne htd
    hk hp hr hS hv hab hnh hD hrun h2, ?_⟩
  cases h2 : ({ K with Δ := Δ } : RunCtx).D.flags (scopeOf s) (.matchNat p z u) |>.2
  · exact (tStepMatchNat_data (K := { K with Δ := Δ }) hInv hJI hMF hTag hW hJ hG hRe hVC hc' ih' ρ p z u st k s π bh st' hm htn hne htd
      hk hp hr hS hv hab hnh hD hrun h2).toE
  · exact tStepMatchNat_proof (K := { K with Δ := Δ }) hInv hJI hPJ hTag hW hG hPA hRE hVC ih' ρ p z u st k s π bh st' hm htn hne htd
      hk hp hr hS hv hab hnh hD hrun h2

/-! ## The facts attacked on the real checker (`MatchAtk`'s programs) -/

namespace MatchGuards

open Ochr.Meaning.Regress.GenNeutralContent (isOk outSt outVal)

/-- A continuation that succeeds exactly where the top frame's bindings `is` all hold `⊥`. -/
def kBots (is : List Nat) : Value → Value → M Unit := fun _ _ => do
  let st ← get
  if is.all fun i => st.env[st.env.size - 1]!.binds[i]!.val == .bot then pure () else err "k"

/-- A continuation that succeeds exactly where the top frame's binding `i` holds `v`. -/
def kHolds (i : Nat) (v : Value) : Value → Value → M Unit := fun _ _ => do
  let st ← get
  if st.env[st.env.size - 1]!.binds[i]!.val == v then pure () else err "k"

-- `A1 (x y n : Nat) : Nat := match n { Z => x, S(m) => y }`: a split at the end of the body (`n ↦ σ`); in EACH world
-- the join drops what the other arm moves (`JoinContG`, `joinCont` around the continuation): at every leaf both `x`
-- and `y` hold `⊥` (the arm's own read moved one, the join the other); the scrutinee is left whole
#guard (Ochr.Meaning.Steps.MatchAtk.bodyOf "A1").pp [] == "match #0 { Z => #2, S _ => #1 }"
#guard (Ochr.Meaning.Steps.MatchAtk.entryOf "A1" 3).any fun st => isOk (Ochr.checkTail 1000 (Ochr.Meaning.Steps.MatchAtk.bodyOf "A1") (kBots [1, 2])) st 100000
#guard (Ochr.Meaning.Steps.MatchAtk.entryOf "A1" 3).any fun st => !isOk (Ochr.checkTail 1000 (Ochr.Meaning.Steps.MatchAtk.bodyOf "A1") (kBots [3])) st 100000
-- `TailMatchNatInv`'s access: after it the scrutinee holds the unknown, and the static join is `[x, y]`
def accA1 : M Value := do
  Ochr.natScrutinee 100 (.var 0); Ochr.accessPath 100 (.var 0); Ochr.accessNeutralHead 100 (.var 0)
  Ochr.matchContent (.var 0)
#guard (Ochr.Meaning.Steps.MatchAtk.entryOf "A1" 3).any fun st => outVal accA1 st 100000 == .abs 2
#guard (Ochr.Meaning.Steps.MatchAtk.entryOf "A1" 3).any fun st =>
  (outVal (Ochr.staticJoin 100 (Ochr.Meaning.Steps.MatchAtk.bodyOf "A1")) st 100000).1.length == 2
-- `A6`: in world `S` the hypothesis `h : Eq(Nat, S(σ'), Z)` is `False` and `match h {}` has no leaf: a continuation that
-- needs `n ↦ Z` succeeds, so no leaf of world `S` ran it (the assignments selecting it are excluded by goodness: the
-- reference's `h` would be a proof of a false proposition)
#guard (Ochr.Meaning.Steps.MatchAtk.entryOf "A6" 2).any fun st => isOk (Ochr.checkTail 1000 (Ochr.Meaning.Steps.MatchAtk.bodyOf "A6") (kHolds 1 .zero)) st 100000
-- `A12`: a sealed scrutinee (`b ↦ ⌈IsZ(σ0)⌉`) is generalised (`GenTailG`), then split
#guard (Ochr.Meaning.Steps.MatchAtk.bodyOf "A12").pp [] == "let b = IsZ(#0); match b { false => 1, true => 2 }"
-- (at each leaf, after the `let`'s drop: the generalisation's record and the world's refinement of its unknown)
#guard (Ochr.Meaning.Steps.MatchAtk.entryOf "A12" 1).any fun st =>
  isOk (Ochr.checkTail 1000 (Ochr.Meaning.Steps.MatchAtk.bodyOf "A12") (fun _ _ => do
    let st ← get
    if st.neutrals.length == 1 && st.refs.any (fun r => st.neutrals.any (·.2 == r.1)) then pure () else err "k")) st 100000
-- `A14`: the `S` arm moves `n.0` and refills it, so the join leaves `n` whole in world `S` (net of refills) and drops
-- nothing the arm does not move: at every leaf `y` holds `⊥` and `n` does not
#guard (Ochr.Meaning.Steps.MatchAtk.entryOf "A14" 2).any fun st => isOk (Ochr.checkTail 1000 (Ochr.Meaning.Steps.MatchAtk.bodyOf "A14") (kBots [2])) st 100000
#guard (Ochr.Meaning.Steps.MatchAtk.entryOf "A14" 2).any fun st => !isOk (Ochr.checkTail 1000 (Ochr.Meaning.Steps.MatchAtk.bodyOf "A14") (kBots [1])) st 100000

end MatchGuards

end Ochr.Meaning.Steps.Form.Master
