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

/-- The induction hypothesis at a lower fuel, at any `Δ`. -/
theorem IH.lower {K : RunCtx} {φ : Future} {n m : Nat} (ih : IH K φ n) (h : m ≤ n) (Δ : Nat → TyS) :
    IH { K with Δ := Δ } φ m :=
  fun m' hm' Δ' ρ => ih m' (Nat.lt_of_lt_of_le hm' h) Δ' ρ

/-- An extension from a state with the same kernel is one from this state. -/
theorem Ext.of_kern_left {K : RunCtx} {ρ : Assignment} {π : Nat → Nat} {st st₀ st' : MState} {ρ' : Assignment}
    {Δ' : Nat → TyS} {π' : Nat → Nat} (hk : Kern st st₀) (h : Ext K ρ π st₀ st' ρ' Δ' π') : Ext K ρ π st st' ρ' Δ' π' where
  abs := by rw [hk.absTy]; exact h.abs
  lab := by rw [hk.nextLoan]; exact h.lab
  agree := fun σ hσ => h.agree σ (by rw [← hk.absTy]; exact hσ)
  ren := fun l hl => h.ren l (by rw [← hk.nextLoan]; exact hl)

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
earlier world restores of it (`exitWorld ⟨stA⟩` from the state that world's arm ENDED in, `cur`: the snapshot with
`cur`'s counters, new unknowns' types and readings and [Rec] candidates kept). RESTATED (lead42, docs/31 D250): `cur`
grew from the snapshot and keeps the tables' invariant. As first stated `cur` was any state, and from one whose counter
is below the snapshot's the next world's fresh field reuses a name in use (`MatchRd.exitBase`), so `WorldRefineG` was
false. `TailMatchNatInv` supplies both: the world's run only grows the tables (`GrowsM`), and keeps their invariant, the
continuation's run at its leaf included (`KeepsTab`, now asked of every continuation by `TailAt`). -/
def WorldBase (stA stB : MState) : Prop :=
  stB = stA ∨ ∃ cur bx, TablesGrow stA cur ∧ TabInv cur ∧ Runs (Ochr.exitWorld ⟨stA⟩) cur bx () stB

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
the readings). The fuel goes down by two (`checkTail`, `checkTailAt`).
RESTATED (lead42, docs/31 D250), twice: (i) the chain starts from a state `st₀` with `st`'s kernel, mode, tail flags and
goal, not from `st`: `locatedTail` sets the editor's fields (`locs.here`, `locs.arm`) before the access where the
editor's table holds the match, and a continuation that reads them succeeds at the run's leaves and fails at the end of
every chain from `st` (`MatchRd.kHere`, `chainZ`; as `TailOtherInv` was, machine9); (ii) a later world's base is the exit
from a state that grew from the snapshot and keeps the tables' invariant (`WorldBase`), which needs that invariant at
`st` and of the continuation (`KeepsTab`), and that the continuation only grows the tables.
RESTATED at main's D145 (lead49): at a DIRECT scrutinee (`Place.Direct`: no positional projection `q.i`), where
`checkTailAt`'s new first step, `projIn`, finds no field step and reads nothing (`runs_projIn_direct`), so the chain
above is unchanged. A scrutinee with a positional projection is now named by the one-arm match on its parent first
(`projStep`, the run's step), so the check continues as `checkTail` of that match: that class is the named fact
`TailProjNatG` (before D145 the check failed there, "no such place", so the class had no successful run). -/
def TailMatchNatInv : Prop :=
  ∀ (n : Nat) (p : Place) (z u : Term) (k : Value → Value → M Unit) (st st' : MState) (bh : Nat) (D : Decisions),
    p.Direct → TabInv st → (∀ v T, GrowsM (k v T)) → (∀ v T, KeepsTab (k v T)) →
    DecTab D st' → Runs (Ochr.checkTail n (.matchNat p z u) k) st bh () st' →
    ∃ (m : Nat) (st₀ stA : MState) (bA : Nat), m + 2 ≤ n ∧ Kern st st₀ ∧ ModeEq st st₀ ∧
      st₀.tailNext = st.tailNext ∧ st₀.tailDecl = st.tailDecl ∧
      Runs (do Ochr.natScrutinee m p; Ochr.accessPath m p; Ochr.accessNeutralHead m p) st₀ bA () stA ∧ DecTab D stA ∧
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
the given one. It keeps the tables' invariant where the given one does (lead42, docs/31 D250: the drops are machine
code; `movedPlace`'s generalisation and η refinement name their unknowns by `freshAbsR`). -/
def JoinContInv : Prop :=
  ∀ (m : Nat) (t : Term) (k kc : Value → Value → M Unit) (stW stJ : MState) (bj : Nat),
    Runs (Ochr.joinCont m t k) stW bj kc stJ →
    Kern stW stJ ∧ ModeEq stW stJ ∧ stJ.tailNext = stW.tailNext ∧ stJ.tailDecl = stW.tailDecl ∧
      stJ.typing = stW.typing ∧ ((∀ v T, GrowsM (k v T)) → ∀ v T, GrowsM (kc v T)) ∧
      ((∀ v T, KeepsTab (k v T)) → ∀ v T, KeepsTab (kc v T))

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
grain (the matching ends of [Access]), and the content's meaning (`Rel.sim` at the scrutinee). It takes the induction
hypothesis below the access's fuel (lead42, docs/31 D250): an end fills the holes of sealed programs, which are then
run again (`nfSealed`; case 3's `SealRerunG`, which needs (II) at their runs). -/
def MatchTagG : Prop :=
  ∀ (K : RunCtx) (ρ : Assignment) (φ : Future) (π : Nat → Nat) (st stA : MState) (s : SState) (p : Place) (m bA : Nat),
    IH K φ m →
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
condition recorded is met by the extension, and an earlier world's exit restores the snapshot (`exitWorld_step_stmt`).
RESTATED (lead42, docs/31 D250): its `WorldBase` asks that the earlier world's end grew from the snapshot and keeps the
tables' invariant (as first stated, any state: FALSE, `MatchRd.exitBase`); and it takes the induction hypothesis below
the refinement's fuel, since a refinement re-runs every sealed program that mentions `σ` (`substEnv`'s normalisation,
`renormAll`; case 3's `SealRerunG`, which needs (II) at those runs). -/
def WorldRefineG : Prop :=
  ∀ (K : RunCtx) (ρ : Assignment) (φ : Future) (π : Nat → Nat) (stA stB stW : MState) (s sA : SState) (p : Place)
    (σ c m bw : Nat) (tg : Sem),
    IH K φ m → 0 < stA.env.size → Pre K ρ stA → Rel K ρ φ π stA sA → Strict.SGood K.dm K.Γ φ sA →
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
result holds is an error on both sides).
RESTATED (lead42, docs/31 D250): the continuation runs at the value the drops LEAVE, not the arm's own value: the arm's
result is a temporary while the drops run, and `movedPlace`'s generalisation and η refinement of a sealed program of a
one-constructor type substitute into it (`MatchRd.J4`: the arm returns `⌈G(σ0)⌉`, the continuation receives
`MkBox(σ3)`); its meaning, the type and the label are kept. As first stated (the continuation at the arm's value) it was
FALSE. It takes the induction hypothesis below the join's fuel (the drops' ends and substitutions re-run sealed
programs). It concludes the goal's meaning kept (the goal clause, lead48, docs/31 D290; READ TRUE: the drops' ends
substitute with `types := false` and leave the goal; `movedPlace`'s generalisation of a sealed program and its
η-refinement write it, `G[σ/n]` and `G[C(σ̄)/σ]`, under an extension giving `σ` the program's meaning, resp. naming the
fields of the value, so its meaning is the same, D288's rows). -/
def JoinContG : Prop :=
  ∀ (K : RunCtx) (ρ : Assignment) (φ : Future) (π : Nat → Nat) (stW stJ : MState) (sA : SState) (t : Term)
    (k kc : Value → Value → M Unit) (m bj : Nat),
    IH K φ m → 0 < stW.env.size → Pre K ρ stW → Rel K ρ φ π stW sA → Runs (Ochr.joinCont m t k) stW bj kc stJ →
    ∀ (ρ₁ : Assignment) (Δ₁ : Nat → TyS) (π₁ : Nat → Nat) (stl stk : MState) (v T : Value) (r : Res) (s₁ : SState)
      (bk : Nat),
      Ext K ρ π stJ stl ρ₁ Δ₁ π₁ → Kept stJ stl →
      meanV { K with Δ := Δ₁ } ρ₁ (fun l => φ (π₁ l)) r.2 v = r.1 → StrAgree { K with Δ := Δ₁ } ρ₁ T r.2 →
      r.2.label = (Value.heldLabel v).map π₁ →
      Pre { K with Δ := Δ₁ } ρ₁ (stl.withTempT v (some T)) → Rel { K with Δ := Δ₁ } ρ₁ φ π₁ (stl.withTempT v (some T)) s₁ →
      Strict.SGood K.dm K.Γ φ s₁ → Runs (kc v T) stl bk () stk →
      JoinDropOk K φ (movedPlaces φ sA) t s₁ ∧
      ∃ (stl₂ : MState) (v₂ : Value) (ρ₂ : Assignment) (Δ₂ : Nat → TyS) (π₂ : Nat → Nat),
        Ext { K with Δ := Δ₁ } ρ₁ π₁ stl stl₂ ρ₂ Δ₂ π₂ ∧ Kept stl stl₂ ∧
        meanV { K with Δ := Δ₂ } ρ₂ (fun l => φ (π₂ l)) r.2 v₂ = r.1 ∧ StrAgree { K with Δ := Δ₂ } ρ₂ T r.2 ∧
        r.2.label = (Value.heldLabel v₂).map π₂ ∧
        Pre { K with Δ := Δ₂ } ρ₂ (stl₂.withTempT v₂ (some T)) ∧
        Rel { K with Δ := Δ₂ } ρ₂ φ π₂ (stl₂.withTempT v₂ (some T)) (joinDrop K φ (movedPlaces φ sA) t s₁) ∧
        hintM { K with Δ := Δ₂ } ρ₂ stl₂.goal = hintM { K with Δ := Δ₁ } ρ₁ stl.goal ∧
        ∃ bk' stk', Runs (k v₂ T) stl₂ bk' () stk'

/-- **A sealed scrutinee generalised at the end of a body** (mixed, NEW; the paper's [Tail-gen], D34's record a path
condition): from the state after the scrutinee's access, holding a sealed program (or an inert loan) there, the
checker's `generalizeNeutral` keeps `Pre` and the relation to the SAME reference state under the assignment extended at
the fresh `σ` by the program's meaning (which the reference holds at the scrutinee: the meaning is a member, `SGood`),
the goal's meaning, the mode, the frames and the readings (the old `generalizeNeutral_step_stmt` in this form). It takes
the induction hypothesis below the generalisation's fuel (lead42, docs/31 D250): replacing the program by `σ` inside other
sealed programs re-runs them (`substEnv`'s normalisation). -/
def GenTailG : Prop :=
  ∀ (K : RunCtx) (ρ : Assignment) (φ : Future) (π : Nat → Nat) (stA stG : MState) (sA : SState) (p : Place) (v : Value)
    (σ m bg : Nat),
    IH K φ m → 0 < stA.env.size → Pre K ρ stA → Rel K ρ φ π stA sA → Strict.SGood K.dm K.Γ φ sA →
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
    (hm : ModeR st) (hne : 0 < st.env.size) (hk : ∀ v T, GrowsM (k v T)) (hkt : ∀ v T, KeepsTab (k v T))
    (hSA : Strict.SGood K.dm K.Γ φ sA)
    (hv : (Term.matchNat p z u).valsOk (Strict.ValsP K ρ φ)) (hab : (Term.matchNat p z u).absBelow st.absTy.size)
    (hnh : (Term.matchNat p z u).hasHolePrim = false)
    (heW : Ext K ρ π st stW ρW ΔW πW) (hKW : Kept st stW) (htnW : stW.tailNext = false) (htdW : stW.tailDecl = none)
    (hgW : hintM { K with Δ := ΔW } ρW stW.goal = hintM K ρ st.goal) (hrt : RecTie K ρ st)
    (hpW : Pre { K with Δ := ΔW } ρW stW) (hrW : Rel { K with Δ := ΔW } ρW φ πW stW sA)
    (hjc : Runs (Ochr.joinCont m (.matchNat p z u) k) stW bj kc stJ)
    (hD₁ : DecTab K.D st₁) (harm : Runs (Ochr.checkTail m (if c = 0 then z else u) kc) stJ b₁ () st₁) :
    TailOutK K ρ φ π st s (runT K ρ φ true (hintM K ρ st.goal) (.matchNat p z u)) k := by
  obtain ⟨hkJ, hmJ, htnJ, htdJ, -, hgrow, hktab⟩ := hJI m _ k kc stW stJ bj hjc
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
    (htdJ.trans htdW) (hgrow hk) (hktab hkt) (hpW.of_kern hkJ)
    (hrt.move (by rw [← hkJ.recStack]; exact hKW.stack) (by rw [← hkJ.absTy]; exact heW.abs)
      fun σ hσ => (heW.agree σ hσ).1) (hrW.of_kern hkJ) hSA (hVC K ΔW ρ ρW φ _ hagree hva)
    (absBelow_mono haba (by rw [← hkJ.absTy]; exact heW.abs)) hnha hD₁ harm
  obtain ⟨stl, v, T, ⟨bk, stk, hkr⟩, ⟨ρ₁, Δ₁, π₁, r, s₁, he₁, hx₁, hm₁, ha₁, hl₁, hp₁, hr₁, hg₁⟩, hK₁⟩ := hO.1 harmfl
  -- the arm's reference run at the start's context and hint
  have hgJ : hintM { K with Δ := ΔW } ρW stJ.goal = hintM K ρ st.goal := by rw [← hkJ.goal]; exact hgW
  rw [hgJ] at hx₁
  have hx₁' : runT K ρ φ true (hintM K ρ st.goal) (if c = 0 then z else u) sA = some (r, s₁) := by
    rw [runT_congrA K ΔW ρ ρW φ true _ _ sA hagree]; exact hx₁
  obtain ⟨-, -, -, hS₁⟩ := Strict.fund_all hc _ hva true _ sA s₁ r hSA hx₁'
  -- the join, at the arm's leaf
  obtain ⟨hjok, stl₂, v₂, ρ₂, Δ₂, π₂, he₂, hK₂, hm₂, ha₂, hl₂, hp₂, hr₂, hg₂, bk', stk', hk'⟩ :=
    hJ { K with Δ := ΔW } ρW φ πW stW stJ sA _ k kc m bj (ih.lower (Nat.le_of_lt hmn) ΔW) hneW hpW hrW hjc ρ₁ Δ₁ π₁
      stl stk v T r s₁ bk he₁ hK₁ hm₁ (ha₁ T rfl) hl₁ hp₁ hr₁ hS₁ hkr
  refine ⟨stl₂, v₂, T, ⟨bk', stk', hk'⟩, ⟨ρ₂, Δ₂, π₂, r, joinDrop K φ (movedPlaces φ sA) (.matchNat p z u) s₁,
    (heW.trans ((he₁.congr hkJ.absTy hkJ.nextLoan rfl rfl))).trans he₂, ?_, hm₂, fun T' e => by cases e; exact ha₂,
    hl₂, hp₂, hr₂, hg₂.trans (hg₁.trans hgJ)⟩, ((hKW.trans (Kept.of_kern hkJ hmJ)).trans hK₁).trans hK₂⟩
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
    (hk : ∀ v T, GrowsM (k v T)) (hkt : ∀ v T, KeepsTab (k v T)) (hp : Pre K ρ st) (hrt : RecTie K ρ st)
    (hr : Rel K ρ φ π st s) (hS : Strict.SGood K.dm K.Γ φ s)
    (hv : (Term.matchNat p z u).valsOk (Strict.ValsP K ρ φ)) (hab : (Term.matchNat p z u).absBelow st.absTy.size)
    (hnh : (Term.matchNat p z u).hasHolePrim = false) (hD : DecTab K.D st')
    (hrun : Runs (Ochr.checkTail n (.matchNat p z u) k) st bh () st') (hdir : p.Direct)
    (hfl2 : (K.D.flags (scopeOf s) (.matchNat p z u)).2 = false) :
    TailOutK K ρ φ π st s (runT K ρ φ true (hintM K ρ st.goal) (.matchNat p z u)) k := by
  have hfl : K.D.flags (scopeOf s) (.matchNat p z u) = (false, false) := by
    have h1 := (hMF (scopeOf s) p z u).1
    rw [hfl2] at h1
    exact Prod.ext h1 hfl2
  obtain ⟨m, st₀, stA, bA, hmn, hk₀, hme₀, htn₀, htd₀, hacc, hDA, hcases⟩ :=
    hInv n p z u k st st' bh K.D hdir (TabInv.of_pre hp) hk hkt hD hrun
  obtain ⟨hTok, tg, sA, ρA, ΔA, πA, htag, heA₀, hKA₀, htnA₀, htdA₀, hgA₀, hpA, hrA, hZ, hSu, hAb⟩ :=
    hTag K ρ φ π st₀ stA s p m bA (fun m' hm' => ih m' (by omega)) (hm.of_modeEq hme₀)
      (by rw [← ColumnC.size_of_erase hk₀.env]; exact hne) (hp.of_kern hk₀) (hr.of_kern hk₀) hS hDA hacc
  -- from the step's own start (the chain starts at a state with its kernel, `locatedTail` aside)
  have heA : Ext K ρ π st stA ρA ΔA πA := Ext.of_kern_left hk₀ heA₀
  have hKA : Kept st stA := (Kept.of_kern hk₀ hme₀).trans hKA₀
  have htnA : stA.tailNext = st.tailNext := htnA₀.trans htn₀
  have htdA : stA.tailDecl = st.tailDecl := htdA₀.trans htd₀
  have hgA : hintM { K with Δ := ΔA } ρA stA.goal = hintM K ρ st.goal := by rw [hgA₀, hk₀.goal]
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
    exact matchArm_leaf hJI hJ hVC hc ih (by omega) hfl (harmfl c) hTok htag hcn hm hne hk hkt hSA hv hab hnh heA hKA
      (htnA.trans htn) (htdA.trans htd) hgA hrt hpA hrA hjc hD₁ harm
  · -- an unknown: the world of the constructor the assignment gives it
    obtain ⟨c, hcn, hc2⟩ := hAb σ hσ
    obtain ⟨stB, stW, stJ, st₁, kc, bw, bj, b₁, hbase, href, hDW, hjc, harm, hD₁⟩ := hworlds c hc2
    obtain ⟨ρW, ΔW, heW, hKW, htnW, htdW, hgW, hpW, hrW⟩ :=
      hW { K with Δ := ΔA } ρA φ πA stA stB stW s sA p σ c m bw tg (ih.lower (by omega) ΔA) hneA hpA hrA hSA htag hσ hcn hbase hDW href
    exact matchArm_leaf hJI hJ hVC hc ih (by omega) hfl (harmfl c) hTok htag hcn hm hne hk hkt hSA hv hab hnh
      (heA.trans heW) (hKA.trans hKW) ((htnW.trans htnA).trans htn) ((htdW.trans htdA).trans htd) (hgW.trans hgA)
      hrt hpW hrW hjc hD₁ harm
  · -- a sealed scrutinee: generalised, then the match checked again at less fuel
    obtain ⟨ρG, ΔG, heG, hKG, htnG, htdG, hgG, hpG, hrG⟩ :=
      hG { K with Δ := ΔA } ρA φ πA stA stG sA p v σ m bg (ih.lower (by omega) ΔA) hneA hpA hrA hSA hcv hvs hDG hgen
    have habG : st.absTy.size ≤ stG.absTy.size := Nat.le_trans heA.abs heG.abs
    have hagree : ∀ σ', (Term.matchNat p z u).anyAtom (· == .abs σ') = true → AgreeA K ΔG ρ ρG σ' := fun σ' hσ' => by
      obtain ⟨a, d⟩ := (heA.trans heG).agree σ' (hab σ' hσ')
      exact ⟨a.symm, d.symm⟩
    have hO := (ih m (by omega) ΔG ρG).2 (.matchNat p z u) stG k sA πA b₁ st₁
      (hm.of_modeEq (hKA.trans hKG).mode) ((htnG.trans htnA).trans htn) (by rw [(hKA.trans hKG).size]; exact hne)
      ((htdG.trans htdA).trans htd) hk hkt hpG
      (hrt.move (hKA.trans hKG).stack habG fun σ hσ => ((heA.trans heG).agree σ hσ).1)
      hrG hSA (hVC K ΔG ρ ρG φ _ hagree hv) (absBelow_mono hab habG) hnh hD₁ hre
    obtain ⟨stl, v', T, hkr, ⟨ρ₁, Δ₁, π₁, r, s₁, he₁, hx₁, hm₁, ha₁, hl₁, hp₁, hr₁, hg₁⟩, hK₁⟩ :=
      hO.1 (by rw [hsc]; exact hfl2)
    rw [hgG.trans hgA] at hx₁
    refine ⟨stl, v', T, hkr, ⟨ρ₁, Δ₁, π₁, r, s₁, (heA.trans heG).trans he₁, ?_, hm₁, ha₁, hl₁, hp₁, hr₁,
      hg₁.trans (hgG.trans hgA)⟩, (hKA.trans hKG).trans hK₁⟩
    rw [← hRe K ρ φ true (hintM K ρ st.goal) p z u s sA tg hfl hTok htag,
      runT_congrA K ΔG ρ ρG φ true _ _ sA hagree]
    exact hx₁

end

/-! ## The split at the end of a body, for a match the table reads as a proof (the erased form, D248's ruling (P1)) -/

/-- **The join of a match read as a proof is empty** (table and checker, NEW; probed: `MatchAtk.L11`): its arms are
statements, which move nothing outside their copies (`Decide.jdMoves`), so the table's join list is empty, and the
checker's `joinCont`, at a state whose aligned table reads the match as a proof, returns the continuation itself.
RESTATED (lead42, docs/31 D251): about THE table `D` (as `MatchFlagsT` is), not every one: as first stated, for every
`D`, its first part was FALSE (a table reading a match as a proof and listing a place to drop). -/
def ProofJoinG (D : Decisions) : Prop :=
    (∀ (sc : List DeclInfo) (entry : List Place) (p : Place) (z u : Term),
      (D.flags sc (.matchNat p z u)).2 = true → D.joinMoves sc entry (.matchNat p z u) = []) ∧
    ∀ (m : Nat) (p : Place) (z u : Term) (k kc : Value → Value → M Unit) (stW stJ : MState) (bj : Nat),
      DecTab D stJ → (D.flags (DecideScope.topReadings stW) (.matchNat p z u)).2 = true →
      Runs (Ochr.joinCont m (.matchNat p z u) k) stW bj kc stJ → kc = k

/-- **An arm of a match read as a proof runs to a proof** (a fact about the model, NEW): a successful reference run of
an arm returns the proof token, at a type meaning the true proposition, and leaves the state it started from. Read: an
arm the table reads as a proof runs under `SM.erasedIf` (exactly `(•, prop True)`, the state restored); a proof constant
means `•` at its type, which (I) makes true (`propext`), and reads nothing; an arm read `.any` (a match with no arms)
has no successful run.
RESTATED (lead42, docs/31 D251): about the run's own context `K₀` at every `Δ` (its table aligned with the checker's,
its globals good), not every context: as first stated, for every `K`, it was FALSE (a table reading the match as a proof
and its arm `Z` as data: the reference's `.zero` runs to `0`, not `•`). Read true of the instance, by the arm's former: the
formers the reference erases as a whole (`SM.erasedIf`: a place, `&`, `:=`, `let`, `;`, the matches, a constructor, `fix`,
a call, `S`, `&A`, `J`) give `(•, prop True)` and the start's state; the proof rules (`cong`, `symm`, `trans`, `rewrite`)
run on a copy to `(•, prop True)`; a proof constant means its global, `•` at a true proposition (`FundCtx`), which is
`prop True` by `propext`; `split f in t` runs `t`; a match with no arms has no successful run. -/
def ProofArmM (K₀ : RunCtx) : Prop :=
  ∀ (Δ : Nat → TyS) (ρ : Assignment) (φ : Future) (hint : TyS) (p : Place) (z u : Term) (s' s₁ : SState) (c : Nat)
    (r : Res), let K := { K₀ with Δ := Δ }
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
theorem matchArm_leafE (hJI : JoinContInv) (hPJ : ProofJoinG K.D) (hPA : ProofArmM K) (hVC : ValsCongrA)
    {n m : Nat} (ih : IH K φ n) (hmn : m < n) {ρ : Assignment} {π : Nat → Nat} {st stW stJ st₁ : MState}
    {s sA : SState} {p : Place} {z u : Term} {k kc : Value → Value → M Unit} {tg : Sem} {c bj b₁ : Nat}
    {ρW : Assignment} {ΔW : Nat → TyS} {πW : Nat → Nat}
    (hfl2 : (K.D.flags (scopeOf s) (.matchNat p z u)).2 = true) (hr : Rel K ρ φ π st s)
    (hTok : TagOk K φ p s) (htag : tagOf K φ p natTag s = some (tg, sA)) (hcn : tg.asNat = some c)
    (hsc : scopeOf sA = scopeOf s)
    (hm : ModeR st) (hne : 0 < st.env.size) (hk : ∀ v T, GrowsM (k v T)) (hkt : ∀ v T, KeepsTab (k v T))
    (hSA : Strict.SGood K.dm K.Γ φ sA)
    (hv : (Term.matchNat p z u).valsOk (Strict.ValsP K ρ φ)) (hab : (Term.matchNat p z u).absBelow st.absTy.size)
    (hnh : (Term.matchNat p z u).hasHolePrim = false)
    (heW : Ext K ρ π st stW ρW ΔW πW) (hKW : Kept st stW) (htnW : stW.tailNext = false) (htdW : stW.tailDecl = none)
    (hgW : hintM { K with Δ := ΔW } ρW stW.goal = hintM K ρ st.goal) (hrt : RecTie K ρ st)
    (hpW : Pre { K with Δ := ΔW } ρW stW) (hrW : Rel { K with Δ := ΔW } ρW φ πW stW sA) (hDW : DecTab K.D stW)
    (hjc : Runs (Ochr.joinCont m (.matchNat p z u) k) stW bj kc stJ)
    (hD₁ : DecTab K.D st₁) (harm : Runs (Ochr.checkTail m (if c = 0 then z else u) kc) stJ b₁ () st₁) :
    TailOutE K ρ φ π st s (runT K ρ φ true (hintM K ρ st.goal) (.matchNat p z u)) k := by
  obtain ⟨hkJ, hmJ, htnJ, htdJ, -, -, -⟩ := hJI m _ k kc stW stJ bj hjc
  have hkc : kc = k := hPJ.2 m p z u k kc stW stJ bj (DecTab.of_kern hkJ hDW)
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
    (htdJ.trans htdW) hk hkt (hpW.of_kern hkJ)
    (hrt.move (by rw [← hkJ.recStack]; exact hKW.stack) (by rw [← hkJ.absTy]; exact heW.abs)
      fun σ hσ => (heW.agree σ hσ).1) (hrW.of_kern hkJ) hSA (hVC K ΔW ρ ρW φ _ hagree hva)
    (absBelow_mono haba (by rw [← hkJ.absTy]; exact heW.abs)) hnha hD₁ harm
  obtain ⟨stl, v, T, hkr, ⟨ρ₁, Δ₁, π₁, r, s₁, he₁, hx₁, hm₁, ha₁, hp₁, hg₁⟩, hK₁⟩ := hO.2
  have hgJ : hintM { K with Δ := ΔW } ρW stJ.goal = hintM K ρ st.goal := by rw [← hkJ.goal]; exact hgW
  rw [hgJ] at hx₁
  have hx₁' : runT K ρ φ true (hintM K ρ st.goal) (if c = 0 then z else u) sA = some (r, s₁) := by
    rw [runT_congrA K ΔW ρ ρW φ true _ _ sA hagree]; exact hx₁
  obtain ⟨hr1, hr2, hs₁⟩ := hPA K.Δ ρ φ _ p z u sA s₁ c r (by rw [hsc]; exact hfl2) hx₁'
  refine ⟨stl, v, T, hkr, ⟨ρ₁, Δ₁, π₁, (.proof, .plain (TyM.prop True)), s,
    heW.trans (he₁.congr hkJ.absTy hkJ.nextLoan rfl rfl), ?_, ?_, ?_, hp₁, hg₁.trans hgJ⟩,
    (hKW.trans (Kept.of_kern hkJ hmJ)).trans hK₁⟩
  · exact runT_matchNat_tailProof _ p z u hfl2 hTok htag hcn hx₁' hr1
      (hPJ.1 _ _ p z u (by rw [hs₁, hsc]; exact hfl2))
  · show meanV _ _ _ (.plain (TyM.prop True)) v = .proof
    rw [Ochr.Meaning.meanV_hintM _ _ _ v (.plain (TyM.prop True)) r.2 hr2.symm, hm₁, hr1]
  · exact ha₁.trans hr2

/-- **The split at the end of a body, for a match on a number the table reads as a proof, in general** (the erased
form `TailOutE`, D248's ruling (P1); a lemma's body: `AddMZero`, `AddZH`): from the induction hypothesis, at EVERY
assignment, as for data (`tStepMatchNat_data`) with the join empty and no relation at the leaf. ASSUMES 9 facts:
`TailMatchNatInv`, `JoinContInv` (checker), `ProofJoinG` (table and checker), `MatchTagG`, `WorldRefineG`, `GenTailG`
(mixed), `ProofArmM`, `MatchReaccessE`, `ValsCongrA` (model). -/
theorem tStepMatchNat_proof (hInv : TailMatchNatInv) (hJI : JoinContInv) (hPJ : ProofJoinG K.D) (hTag : MatchTagG)
    (hW : WorldRefineG) (hG : GenTailG) (hPA : ProofArmM K) (hRe : MatchReaccessE) (hVC : ValsCongrA)
    {n : Nat} (ih : IH K φ n) (ρ : Assignment) (p : Place) (z u : Term)
    (st : MState) (k : Value → Value → M Unit) (s : SState) (π : Nat → Nat) (bh : Nat) (st' : MState)
    (hm : ModeR st) (htn : st.tailNext = false) (hne : 0 < st.env.size) (htd : st.tailDecl = none)
    (hk : ∀ v T, GrowsM (k v T)) (hkt : ∀ v T, KeepsTab (k v T)) (hp : Pre K ρ st) (hrt : RecTie K ρ st)
    (hr : Rel K ρ φ π st s) (hS : Strict.SGood K.dm K.Γ φ s)
    (hv : (Term.matchNat p z u).valsOk (Strict.ValsP K ρ φ)) (hab : (Term.matchNat p z u).absBelow st.absTy.size)
    (hnh : (Term.matchNat p z u).hasHolePrim = false) (hD : DecTab K.D st')
    (hrun : Runs (Ochr.checkTail n (.matchNat p z u) k) st bh () st') (hdir : p.Direct)
    (hfl2 : (K.D.flags (scopeOf s) (.matchNat p z u)).2 = true) :
    TailOutE K ρ φ π st s (runT K ρ φ true (hintM K ρ st.goal) (.matchNat p z u)) k := by
  obtain ⟨m, st₀, stA, bA, hmn, hk₀, hme₀, htn₀, htd₀, hacc, hDA, hcases⟩ :=
    hInv n p z u k st st' bh K.D hdir (TabInv.of_pre hp) hk hkt hD hrun
  obtain ⟨hTok, tg, sA, ρA, ΔA, πA, htag, heA₀, hKA₀, htnA₀, htdA₀, hgA₀, hpA, hrA, hZ, hSu, hAb⟩ :=
    hTag K ρ φ π st₀ stA s p m bA (fun m' hm' => ih m' (by omega)) (hm.of_modeEq hme₀)
      (by rw [← ColumnC.size_of_erase hk₀.env]; exact hne) (hp.of_kern hk₀) (hr.of_kern hk₀) hS hDA hacc
  -- from the step's own start (the chain starts at a state with its kernel, `locatedTail` aside)
  have heA : Ext K ρ π st stA ρA ΔA πA := Ext.of_kern_left hk₀ heA₀
  have hKA : Kept st stA := (Kept.of_kern hk₀ hme₀).trans hKA₀
  have htnA : stA.tailNext = st.tailNext := htnA₀.trans htn₀
  have htdA : stA.tailDecl = st.tailDecl := htdA₀.trans htd₀
  have hgA : hintM { K with Δ := ΔA } ρA stA.goal = hintM K ρ st.goal := by rw [hgA₀, hk₀.goal]
  have hSA : Strict.SGood K.dm K.Γ φ sA := Strict.sgood_tagOf hS hTok htag
  have hsc : scopeOf sA = scopeOf s := by rw [scopeOf_rel hr, scopeOf_rel hrA, hKA.top]
  have hneA : 0 < stA.env.size := by rw [hKA.size]; exact hne
  rcases hcases with ⟨c, hcon, kc, stJ, st₁, bj, b₁, hjc, harm, hD₁⟩ | ⟨σ, hσ, hworlds⟩ |
      ⟨v, σ, stG, st₁, bg, b₁, hvs, hcv, hgen, hDG, hre, hD₁⟩
  · have hcn : tg.asNat = some c := by
      rcases hcon with ⟨h0, rfl⟩ | ⟨⟨w, h1⟩, rfl⟩
      · exact hZ h0
      · exact hSu w h1
    exact matchArm_leafE hJI hPJ hPA hVC ih (by omega) hfl2 hr hTok htag hcn hsc hm hne hk hkt hSA hv hab hnh heA hKA
      (htnA.trans htn) (htdA.trans htd) hgA hrt hpA hrA hDA hjc hD₁ harm
  · obtain ⟨c, hcn, hc2⟩ := hAb σ hσ
    obtain ⟨stB, stW, stJ, st₁, kc, bw, bj, b₁, hbase, href, hDW, hjc, harm, hD₁⟩ := hworlds c hc2
    obtain ⟨ρW, ΔW, heW, hKW, htnW, htdW, hgW, hpW, hrW⟩ :=
      hW { K with Δ := ΔA } ρA φ πA stA stB stW s sA p σ c m bw tg (ih.lower (by omega) ΔA) hneA hpA hrA hSA htag hσ hcn hbase hDW href
    exact matchArm_leafE hJI hPJ hPA hVC ih (by omega) hfl2 hr hTok htag hcn hsc hm hne hk hkt hSA hv hab hnh
      (heA.trans heW) (hKA.trans hKW) ((htnW.trans htnA).trans htn) ((htdW.trans htdA).trans htd) (hgW.trans hgA)
      hrt hpW hrW hDW hjc hD₁ harm
  · obtain ⟨ρG, ΔG, heG, hKG, htnG, htdG, hgG, hpG, hrG⟩ :=
      hG { K with Δ := ΔA } ρA φ πA stA stG sA p v σ m bg (ih.lower (by omega) ΔA) hneA hpA hrA hSA hcv hvs hDG hgen
    have habG : st.absTy.size ≤ stG.absTy.size := Nat.le_trans heA.abs heG.abs
    have hagree : ∀ σ', (Term.matchNat p z u).anyAtom (· == .abs σ') = true → AgreeA K ΔG ρ ρG σ' := fun σ' hσ' => by
      obtain ⟨a, d⟩ := (heA.trans heG).agree σ' (hab σ' hσ')
      exact ⟨a.symm, d.symm⟩
    have hO := (ih m (by omega) ΔG ρG).2 (.matchNat p z u) stG k sA πA b₁ st₁
      (hm.of_modeEq (hKA.trans hKG).mode) ((htnG.trans htnA).trans htn) (by rw [(hKA.trans hKG).size]; exact hne)
      ((htdG.trans htdA).trans htd) hk hkt hpG
      (hrt.move (hKA.trans hKG).stack habG fun σ hσ => ((heA.trans heG).agree σ hσ).1)
      hrG hSA (hVC K ΔG ρ ρG φ _ hagree hv) (absBelow_mono hab habG) hnh hD₁ hre
    obtain ⟨stl, v', T, hkr, ⟨ρ₁, Δ₁, π₁, r, s₁, he₁, hx₁, hm₁, ha₁, hp₁, hg₁⟩, hK₁⟩ := hO.2
    rw [hgG.trans hgA, ← runT_congrA K ΔG ρ ρG φ true _ _ sA hagree] at hx₁
    have hmap := hRe K ρ φ true (hintM K ρ st.goal) p z u s sA tg hTok htag
    rw [hx₁] at hmap
    obtain ⟨⟨r', s'⟩, hx', hr'⟩ := Option.map_eq_some_iff.mp hmap.symm
    simp only at hr'
    subst hr'
    exact ⟨stl, v', T, hkr, ⟨ρ₁, Δ₁, π₁, r', s', (heA.trans heG).trans he₁, hx', hm₁, ha₁, hp₁, hg₁.trans (hgG.trans hgA)⟩,
      (hKA.trans hKG).trans hK₁⟩

end

/-! ## The step `TStepMatchNat`, assembled -/

/-- **The step at the end of a body at a match on a number whose scrutinee has a positional projection** (MIXED; NEW at
main's D145, UNREAD; lead49): since D145 `checkTailAt` names a scrutinee with a field step `q.i` by the one-arm match on
its parent first (`projStep`, the run's step: the parent refined in place, D93, or matched by its type), then checks
that match; the reference's `.matchNat` reads the tag at the field place directly (`tagOf`). Before D145 the check
failed at such a scrutinee ("no such place"), so the class had no successful run. Its content: the checker's one-arm
match on the parent against the reference's direct read of the field, the [Proj] agreement the eval side's place read
also leaves open (`PlaceInvD` is at a direct place). -/
def TailProjNatG (K : RunCtx) (φ : Future) : Prop :=
  ∀ n, IH K φ n → ∀ Δ ρ p z u, ¬ p.Direct → TailAt { K with Δ := Δ } ρ φ n (.matchNat p z u)

/-- **`TStepMatchNat` in general** (a match on a number at the end of a body: the paper's [Tail-split], [Tail-gen],
[Tail-match]; docs/18's principle "worlds are exclusive" and case 4): the full form where the table does not read the
match as a proof (`tStepMatchNat_data`), the erased form where it does (`tStepMatchNat_proof`; D248's ruling (P1)).
ASSUMES 13 facts: `TailMatchNatInv`, `JoinContInv` (checker); `MatchFlagsT`, `ProofJoinG` (table; the latter also
the checker's `joinCont`); `MatchTagG`, `WorldRefineG`, `JoinContG`, `GenTailG`, `TailProjNatG` (mixed; the last NEW at
main's D145: a projected scrutinee); `MatchReaccessM`, `MatchReaccessE`, `ProofArmM`, `ValsCongrA` (model); and
`Strict.FundCtx K`. -/
theorem tStepMatchNat_of {K : RunCtx} {φ : Future} (hInv : TailMatchNatInv) (hJI : JoinContInv)
    (hMF : MatchFlagsT K.D) (hPJ : ProofJoinG K.D) (hTag : MatchTagG) (hW : WorldRefineG) (hJ : JoinContG)
    (hG : GenTailG) (hRe : MatchReaccessM) (hRE : MatchReaccessE) (hPA : ProofArmM K) (hVC : ValsCongrA)
    (hPj : TailProjNatG K φ) (hc : Strict.FundCtx K) : TStepMatchNat K φ := by
  intro n ih Δ ρ p z u
  refine (Classical.em p.Direct).elim (fun hdir => ?_) (fun hdir => hPj n ih Δ ρ p z u hdir)
  intro st k s π bh st' hm htn hne htd hk hkt hp hrt hr hS hv hab hnh hD hrun
  have ih' : IH { K with Δ := Δ } φ n := ih
  have hc' : Strict.FundCtx { K with Δ := Δ } := ⟨hc.globals, hc.sorts⟩
  refine ⟨fun h2 => tStepMatchNat_data (K := { K with Δ := Δ }) hInv hJI hMF hTag hW hJ hG hRe hVC hc' ih' ρ p z u st k s π bh st' hm htn hne htd
    hk hkt hp hrt hr hS hv hab hnh hD hrun hdir h2, ?_⟩
  cases h2 : ({ K with Δ := Δ } : RunCtx).D.flags (scopeOf s) (.matchNat p z u) |>.2
  · exact (tStepMatchNat_data (K := { K with Δ := Δ }) hInv hJI hMF hTag hW hJ hG hRe hVC hc' ih' ρ p z u st k s π bh st' hm htn hne htd
      hk hkt hp hrt hr hS hv hab hnh hD hrun hdir h2).toE
  · exact tStepMatchNat_proof (K := { K with Δ := Δ }) hInv hJI hPJ hTag hW hG hPA hRE hVC ih' ρ p z u st k s π bh st' hm htn hne htd
      hk hkt hp hrt hr hS hv hab hnh hD hrun hdir h2

/-! ## A match on a known constructor, not at the end of a body (`StepMatchNat`'s known case): STATED, not proved

`evalMatch` on a scrutinee whose content after the access is `Z` or `S(w)`: [Entry] (`joinEnds`, not in tail
position: `blockEntry`, the captures of the block the match would close off as, accessed in its order), the arm run with
no hint in a typed run (the match's hint in an untyped run at the end of a body), the join's drop with the arm's result
in flight (`joinDrop`), and, where the match's declared type is a borrow, the result lent what the block's would be
(`lendEnv` with a reserved label, D90). The reference: `tagOf`, `matchEntry` (`entryAccess` at `Decisions.blockCaps`,
`MatchEntryOk`), the arm at `tailHint`, `JoinDropOk` and `joinDrop`, `entryLend` (only a live label, D222). An unknown
scrutinee closes off as a stuck block in a typed run (out of scope: decision (b) pending) and is stuck in an untyped one
(no successful run). The facts the step needs, each classed: -/

/-- **[Entry] at a match on a known constructor** (mixed, NEW; D90's static ends, the paper's [Entry]): the checker's
`blockEntry` (the captures of the block the match would close off as, in `closeBlock`'s order, each accessed, a capture by
`&` invalidating, D112) against the reference's `matchEntry` (`Decisions.blockCaps` at the places moved after the tag,
`entryAccess`, its strict test `MatchEntryOk`): the relation after, under an extension, what a run keeps. Its parts: the
captures and modes the same on both sides (`blockCaps` aligned with `blockCaptures`, the moved places by `joinEntry_stmt`),
each access `AccessG`'s, the re-rootings `movedPlace`'s. With the goal's meaning kept (the goal clause, lead48, docs/31
D290; READ TRUE: the entry's η-refinement of a captured one-constructor prefix writes the goal, `G[C(σ̄)/σ]`, under an
extension naming the fields of `σ`'s value, D288; no consumer yet). -/
def MatchEntryG : Prop :=
  ∀ (K : RunCtx) (ρ : Assignment) (φ : Future) (π : Nat → Nat) (stA stE : MState) (sA : SState) (t : Term)
    (caps : Array (Place × Nat)) (m bE : Nat),
    0 < stA.env.size → Pre K ρ stA → Rel K ρ φ π stA sA → Strict.SGood K.dm K.Γ φ sA → DecTab K.D stE →
    Runs (Ochr.blockEntry m t) stA bE caps stE →
    MatchEntryOk K φ true t sA ∧ ∃ (ρE : Assignment) (ΔE : Nat → TyS) (πE : Nat → Nat),
      Ext K ρ π stA stE ρE ΔE πE ∧ Kept stA stE ∧
      Pre { K with Δ := ΔE } ρE stE ∧ Rel { K with Δ := ΔE } ρE φ πE stE (matchEntry K φ true t sA).1 ∧
      hintM { K with Δ := ΔE } ρE stE.goal = hintM K ρ stA.goal

/-- **The join's drop after an arm, with the arm's result in flight** (mixed, NEW; [Join], D84; the old
`joinDrop_step_stmt` in the master's form), at a match whose declared type is not a borrow: from the arm's end (its
result `v : T?` related to the reference's), the checker's drops (`joinDrop`'s loop after `staticJoin`, the result held
as a temporary) against the reference's `JoinDropOk` and `joinDrop` at the places moved after the entry: the value keeps
its meaning, type and label; the relation after, under an extension. As first written it took the lending as a FREE
parameter `lend : M Unit` after the drops (any action plugged in made it false; and `joinEnds` marks the by-move borrow
variables' lent places BEFORE the arm, so no action after the drops is the lending): the borrow-typed match's lending is
its own fact, `JoinLendG`, stated in prose below. With the goal's meaning kept (the goal clause, lead48, docs/31 D290;
READ TRUE as `JoinContG`'s; no consumer yet). -/
def JoinDropG : Prop :=
  ∀ (K : RunCtx) (ρ : Assignment) (φ : Future) (π : Nat → Nat) (st₁ st₂ : MState) (sE s₁ : SState) (t : Term)
    (v : Value) (T? : Option Value) (r : Res) (m b : Nat),
    isRefDecl (K.D.declOf (scopeOf sE) t) = false →
    Pre K ρ (st₁.withTempT v T?) → Rel K ρ φ π (st₁.withTempT v T?) s₁ → Strict.SGood K.dm K.Γ φ s₁ →
    meanV K ρ (fun l => φ (π l)) r.2 v = r.1 → (∀ T, T? = some T → StrAgree K ρ T r.2) →
    r.2.label = (Value.heldLabel v).map π →
    Runs (do let (drops, _) ← Ochr.staticJoin m t
             Ochr.pushTemp v T? "joinDrop"
             for q in drops do Ochr.dropAtJoin m (← Ochr.movedPlace m q)
             discard Ochr.popTemp) st₁ b () st₂ →
    JoinDropOk K φ (movedPlaces φ sE) t s₁ ∧ ∃ (ρ₂ : Assignment) (Δ₂ : Nat → TyS) (π₂ : Nat → Nat),
      Ext K ρ π st₁ st₂ ρ₂ Δ₂ π₂ ∧ Kept st₁ st₂ ∧
      meanV { K with Δ := Δ₂ } ρ₂ (fun l => φ (π₂ l)) r.2 v = r.1 ∧
      (∀ T, T? = some T → StrAgree { K with Δ := Δ₂ } ρ₂ T r.2) ∧ r.2.label = (Value.heldLabel v).map π₂ ∧
      Pre { K with Δ := Δ₂ } ρ₂ (st₂.withTempT v T?) ∧
      Rel { K with Δ := Δ₂ } ρ₂ φ π₂ (st₂.withTempT v T?) (joinDrop K φ (movedPlaces φ sE) t s₁) ∧
      hintM { K with Δ := Δ₂ } ρ₂ st₂.goal = hintM K ρ st₁.goal

/-! `JoinLendG` (mixed, NOT stated in Lean): at a match whose declared type is a borrow, `joinEnds`' lending, in two parts
around the arm (before: a label `g` reserved and the by-move borrow variables' lent places marked for it; after the
drops: the result's label `k` given `g`'s marks, the by-`&` captures' places lent to `k`), against the reference's
`entrySnapshot` (taken after the entry) and `entryLend` at the result's label, which lends only a live label (D222).
Attacked on `MatchAtk.A7` (accepted). -/

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
