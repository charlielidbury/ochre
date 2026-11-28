import Ochr.Meaning.Steps.MatchModel

/-!
# The split at the end of a body, on a data type (lead42, 2026-11-28; docs/31 D252)

`TStepMatchInd` (the paper's [Tail-split], [Tail-gen], [Tail-match] at a declared inductive, with D119's join, D93's
one-constructor match refined in place, D45's match on a proof by its type) in the form of `TStepMatchNat`
(`Steps/MasterMatch.lean`), with every fact named and classed. Shared with the number case: `JoinContInv`, `JoinContG`,
`GenTailG` (stated for any match), `ValsCongrA` (proved). New:

* `TailMatchIndInv` (C): `checkTail` of a match on a data type inverted (`checkTailAt`'s `.matchInd`): the match on a
  proof apart; the access; by the content a known constructor (its arm, with the join's continuation unless the type has
  one constructor), an unknown of a one-constructor type refined in place (`etaInPlace`) and the match checked again, an
  unknown of a type with several, one world per constructor (`ctorRefinement`: the fields fresh, each at its type
  computed from the earlier ones and the parameters), a sealed program generalised and the match checked again;
* `MatchIndTagG` (X): `MatchTagG` at the tag of a data value (`indTag`: the constructor's index);
* `WorldRefineIndG` (X): `WorldRefineG` at `ctorRefinement` (constructors with fields, dependent fields, parameters);
* `EtaTailG` (X): the refinement in place of an unknown of a one-constructor type (`etaInPlace`: an η record);
* `MatchIndFlagsT`, `ProofJoinIndG` (T), `ProofArmIndM` (M at the instance): the number case's at a data match;
* `ProofMatchTailG` (X): the match on a PROOF at the end of a body (D45, D229/D231's witness step), one fact.

**Was false as stated for every term** (D252): `checkTailAt` built a split's worlds by `zip`, so a constructor with no
arm got no world (`MatchRead`'s `ArmsP`-shaped probe in docs/31 D252), where the reference has no run; the resolver never
makes such a match. The step was derived at matches whose arms cover their type's constructors (`ArmsCover`, a hypothesis
of the step). Since main's D146 the core checks one arm per constructor (`ctorArms`), so the covering is a consequence of
the checker's run (`TailMatchIndInv`'s split branch concludes it) and the hypothesis is DELETED (lead49): the step is
`TStepMatchInd` itself (`tStepMatchInd_of`).
-/

open Ochr.Test

/-! The new facts' cases, attacked on the real checker (`MatchIndGuards` below): a parameter substituted into a fresh
field's type (`O1`), a dependent field's type refined by an inner split's pattern (`D1`), a one-constructor unknown
refined in place and the match checked again (`U1`), a match on a proof read by its type (`P1`). -/
#guard_msgs (drop warning) in
ochr MatchIndRd {
  inductive Bool := false | true
  inductive Opt (A : Type) := None | Some(x : A)
  inductive Box := MkBox(v : Nat)
  def Payload (b : Bool) : Type := match b { false => Nat, true => Unit, }
  inductive DP := MkDP(b : Bool, x : Payload(b))
  inductive Ex : Prop := Wit(w : Nat, h : Eq(Nat, w, w))
  def O1 (o : Opt(Nat)) (y : Nat) : Nat := match o { None => y, Some(v) => v, }
  def D1 (d : DP) : Nat := match d { MkDP(b, x) => match b { false => clone(x), true => 0, }, }
  def U1 (b : Box) : Nat := match b { MkBox(v) => v, }
  def P1 (e : Ex) : True := match e { Wit(w, h) => refl, }
}

namespace Ochr.Meaning.Steps.Form.Master

open Ochr Ochr.Meaning Ochr.Meaning.Steps Ochr.Meaning.Steps.Form

/-- **The step at the end of a body at a match on a data type whose scrutinee has a positional projection** (MIXED;
NEW at main's D145, UNREAD; lead49): as `TailProjNatG`, the checker's one-arm match on the parent (`projStep`) against the
reference's direct read of the field's tag. -/
def TailProjIndG (K : RunCtx) (φ : Future) : Prop :=
  ∀ n, IH K φ n → ∀ Δ ρ p ty arms, ¬ p.Direct → TailAt { K with Δ := Δ } ρ φ n (.matchInd p ty arms)


/-! ## The reference's match on a data type in tail position, unfolded -/

/-- The arm of index `c`. -/
theorem runArm_get {K : RunCtx} {ρ : Assignment} {φ : Future} {tl : Bool} {hint : TyS} :
    ∀ (arms : List (Hint × Term)) (c : Nat) (h : Hint) (a : Term), arms[c]? = some (h, a) →
      runArm K ρ φ tl hint c arms = runT K ρ φ tl hint a
  | [], _, _, _, e => by simp at e
  | (h', a') :: rest, c, h, a, e => by
    rw [runArm]
    cases c with
    | zero => simp only [List.getElem?_cons_zero, Option.some.injEq, Prod.mk.injEq] at e; obtain ⟨-, rfl⟩ := e; rfl
    | succ c => simp only [List.getElem?_cons_succ] at e; simp only [Nat.add_one_ne_zero, if_false, Nat.add_sub_cancel]
                exact runArm_get rest c h a e

/-- **The reference's match on a data type in tail position, where the table does not erase it**: the tag's access, no
[Entry] (tail position), the arm the tag selects at the match's own hint, and the join's drop unless the type has one
constructor (D93). -/
theorem runT_matchInd_tailData {K : RunCtx} {ρ : Assignment} {φ : Future} (hint : TyS) (p : Place) (n : String)
    (arms : List (Hint × Term)) {s sA s₁ : SState} {tg : Sem} {r : Res} {c : Nat}
    (hfl : K.D.flags (scopeOf s) (.matchInd p n arms) = (false, false))
    (hT : TagOk K φ p s) (htag : tagOf K φ p indTag s = some (tg, sA)) (hc : tg.asNat = some c)
    (hnp : tg ≠ .proof) (harm : runArm K ρ φ true hint c arms sA = some (r, s₁))
    (hj : oneCtor K.Γ n = true ∨ JoinDropOk K φ (movedPlaces φ sA) (.matchInd p n arms) s₁) :
    runT K ρ φ true hint (.matchInd p n arms) s =
      some (r, if oneCtor K.Γ n = true then s₁ else joinDrop K φ (movedPlaces φ sA) (.matchInd p n arms) s₁) := by
  have hip : tg.isProof = false := by cases tg <;> first | exact absurd rfl hnp | rfl
  have hme : optCheck (MatchEntryOk K φ (!true && !tg.isProof && !oneCtor K.Γ n) (.matchInd p n arms) sA) = some ⟨⟩ := by
    unfold optCheck; rw [if_pos]; intro e; simp at e
  have hent : matchEntry K φ (!true && !tg.isProof && !oneCtor K.Γ n) (.matchInd p n arms) sA = (sA, fun _ s₂ => s₂) := by
    simp [matchEntry]
  have hjo : optCheck (tg.isProof = true ∨ oneCtor K.Γ n = true ∨
      JoinDropOk K φ (movedPlaces φ sA) (.matchInd p n arms) s₁) = some ⟨⟩ := by
    unfold optCheck; rw [if_pos]; exact Or.inr hj
  rw [runT]
  simp only [SM.erasedIf, SM.stmtIf, hfl, Bool.false_eq_true, if_false]
  rw [SM.guarded_of hT, htag]
  simp only [bind, Option.bind, hent, tailHint_true]
  rw [hme]
  simp only [hc, harm]
  rw [hjo]

/-! ## The facts -/

/-- **`checkTail` of a match on a data type, inverted** (a fact about the checker alone, NEW, for the machine lane;
attacked in `MatchIndGuards`): `abstractMatchCheck`, then either the match is on a proof (`byTypeMatch`: its arms name
the constructors of a `Prop` declaration, or it has none; `ProofMatchTailG`), or the access (`accessPath`,
`accessNeutralHead`) and, by the content:
* a known constructor `c` of `ty`: `scrutType`, then its arm, with the continuation itself where the type has one
  constructor (D93: no join) and with the join's (`joinCont`) otherwise;
* an unknown `σ`: `scrutType` (`(d, ps)`), then, at one constructor, its refinement in place (`etaInPlace`) and the match
  checked again; at several, for EACH constructor `c` with an arm, a world: its base, `σ := C_c(σ̄)` (`ctorRefinement`:
  the fields fresh, each at its type from the parameters and the earlier fields), the join's continuation, the arm;
* a sealed program or an inert loan: generalised and the match checked again.
As `TailMatchNatInv`: from a state `st₀` with `st`'s kernel, mode, tail flags and goal (the editor's located mode), a later
world's base from a grown state keeping `TabInv`.
RESTATED at main's D145 (lead49), as `TailMatchNatInv`: at a DIRECT scrutinee, where `checkTailAt`'s new first step,
`projIn`, finds no field step; a projected scrutinee is now named by the one-arm match on its parent first (`projStep`),
the class of the named fact `TailProjIndG`. -/
def TailMatchIndInv : Prop :=
  ∀ (n : Nat) (p : Place) (ty : String) (arms : List (Hint × Term)) (k : Value → Value → M Unit) (st st' : MState)
    (bh : Nat) (D : Decisions),
    p.Direct → TabInv st → (∀ v T, GrowsM (k v T)) → (∀ v T, KeepsTab (k v T)) →
    DecTab D st' → Runs (Ochr.checkTail n (.matchInd p ty arms) k) st bh () st' →
    (∃ b, Runs (Ochr.byTypeMatch ty arms) st b true st) ∨
    ∃ (m : Nat) (st₀ stA : MState) (bA : Nat) (d : IndDecl), m + 2 ≤ n ∧ Kern st st₀ ∧ ModeEq st st₀ ∧
      st₀.tailNext = st.tailNext ∧ st₀.tailDecl = st.tailDecl ∧
      st.inds.find? (·.name == ty) = some d ∧ d.sort ≠ 0 ∧
      Runs (do Ochr.abstractMatchCheck p ty; Ochr.accessPath m p; Ochr.accessNeutralHead m p) st₀ bA () stA ∧
      DecTab D stA ∧
      ((∃ (c : Nat) (h : Hint) (ps fs : List Value) (x : Hint) (a : Term) (stS : MState) (bS : Nat) (dps : IndDecl × List Value),
          ckContent stA.env p = some (.ind ty c h ps fs) ∧ arms[c]? = some (x, a) ∧
          Runs (Ochr.scrutType m p ty) stA bS dps stS ∧ DecTab D stS ∧
          ((d.ctors.length = 1 ∧ ∃ st₁ b₁, Runs (Ochr.checkTail m a k) stS b₁ () st₁ ∧ DecTab D st₁) ∨
           (d.ctors.length ≠ 1 ∧ ∃ (kc : Value → Value → M Unit) (stJ st₁ : MState) (bj b₁ : Nat),
              Runs (Ochr.joinCont m (.matchInd p ty arms) k) stS bj kc stJ ∧
              Runs (Ochr.checkTail m a kc) stJ b₁ () st₁ ∧ DecTab D st₁))) ∨
       (∃ (σ : Nat) (ps : List Value) (stS : MState) (bS : Nat),
          ckContent stA.env p = some (.abs σ) ∧ Runs (Ochr.scrutType m p ty) stA bS (d, ps) stS ∧ DecTab D stS ∧
          ((d.ctors.length = 1 ∧ ∃ (r : Value) (stE st₁ : MState) (bE b₁ : Nat), Runs (Ochr.etaInPlace m σ d ps) stS bE r stE ∧
              DecTab D stE ∧ Runs (Ochr.checkTail m (.matchInd p ty arms) k) stE b₁ () st₁ ∧ DecTab D st₁) ∨
           (d.ctors.length ≠ 1 ∧ arms.length = d.ctors.length ∧ ∀ c x a, c < d.ctors.length → arms[c]? = some (x, a) →
              ∃ (stB stW stJ st₁ : MState) (r : Value) (kc : Value → Value → M Unit) (bw bj b₁ : Nat),
                WorldBase stS stB ∧
                Runs (do let r ← Ochr.ctorRefinement m d ps c; Ochr.refine m σ r; pure r) stB bw r stW ∧ DecTab D stW ∧
                Runs (Ochr.joinCont m (.matchInd p ty arms) k) stW bj kc stJ ∧
                Runs (Ochr.checkTail m a kc) stJ b₁ () st₁ ∧ DecTab D st₁))) ∨
       (∃ (v : Value) (σ : Nat) (stG st₁ : MState) (bg b₁ : Nat),
          ((∃ t', v = .sealed t') ∨ (∃ l, v = .loan l)) ∧ ckContent stA.env p = some v ∧
          Runs (Ochr.generalizeNeutral m p v) stA bg σ stG ∧ DecTab D stG ∧
          Runs (Ochr.checkTail m (.matchInd p ty arms) k) stG b₁ () st₁ ∧ DecTab D st₁))

/-- **The scrutinee's access and its tag, at a data type** (mixed, NEW; `MatchTagG` at `indTag`): the checker's access
against the reference's `tagOf … indTag`; the tag is a constructor's index (the scrutinee is data: `d.sort ≠ 0`), below
the number of constructors (a member of `ty`'s meaning), and a known constructor's own. Takes the induction hypothesis
(an end re-runs sealed programs). -/
def MatchIndTagG : Prop :=
  ∀ (K : RunCtx) (ρ : Assignment) (φ : Future) (π : Nat → Nat) (st stA : MState) (s : SState) (p : Place) (ty : String)
    (d : IndDecl) (m bA : Nat),
    IH K φ m → ModeR st → 0 < st.env.size → Pre K ρ st → Rel K ρ φ π st s → Strict.SGood K.dm K.Γ φ s →
    DecTab K.D stA → st.inds.find? (·.name == ty) = some d → d.sort ≠ 0 →
    Runs (do Ochr.abstractMatchCheck p ty; Ochr.accessPath m p; Ochr.accessNeutralHead m p) st bA () stA →
    TagOk K φ p s ∧ ∃ (tg : Sem) (sA : SState) (ρA : Assignment) (ΔA : Nat → TyS) (πA : Nat → Nat),
      tagOf K φ p indTag s = some (tg, sA) ∧ Ext K ρ π st stA ρA ΔA πA ∧ Kept st stA ∧
      stA.tailNext = st.tailNext ∧ stA.tailDecl = st.tailDecl ∧
      hintM { K with Δ := ΔA } ρA stA.goal = hintM K ρ st.goal ∧
      Pre { K with Δ := ΔA } ρA stA ∧ Rel { K with Δ := ΔA } ρA φ πA stA sA ∧
      tg ≠ .proof ∧ ∃ c, tg.asNat = some c ∧ c < d.ctors.length ∧
        ∀ c' h ps fs, ckContent stA.env p = some (.ind ty c' h ps fs) → c' = c

/-- **The scrutinee's type** (mixed, NEW): `scrutType` (`placeType`, `lookupInd`) only reads, but `placeType` may compute
a dependent field's type on a private copy, whose new unknowns' types survive it: `Pre` and the relation to the same
reference state are kept under an extension, with what a run keeps, the goal's meaning, and Ω itself. -/
def ScrutTypeG : Prop :=
  ∀ (K : RunCtx) (ρ : Assignment) (φ : Future) (π : Nat → Nat) (stA stS : MState) (sA : SState) (p : Place) (ty : String)
    (dps : IndDecl × List Value) (m bS : Nat),
    IH K φ m → 0 < stA.env.size → Pre K ρ stA → Rel K ρ φ π stA sA → Strict.SGood K.dm K.Γ φ sA → DecTab K.D stS →
    Runs (Ochr.scrutType m p ty) stA bS dps stS →
    ∃ (ρS : Assignment) (ΔS : Nat → TyS), Ext K ρ π stA stS ρS ΔS π ∧ Kept stA stS ∧ stS.env = stA.env ∧
      stS.tailNext = stA.tailNext ∧ stS.tailDecl = stA.tailDecl ∧
      hintM { K with Δ := ΔS } ρS stS.goal = hintM K ρ stA.goal ∧
      Pre { K with Δ := ΔS } ρS stS ∧ Rel { K with Δ := ΔS } ρS φ π stS sA

/-- **A world's start at a data type** (mixed, NEW; `WorldRefineG` at `ctorRefinement`): the base, then `σ := C_c(σ̄)`
with the fields fresh, each typed from the parameters and the EARLIER fields (D64), keeps `Pre` and the relation to the
same reference state under the assignment extended at the fresh fields by the assignment's value's fields (the tag `c`
is its constructor). -/
def WorldRefineIndG : Prop :=
  ∀ (K : RunCtx) (ρ : Assignment) (φ : Future) (π : Nat → Nat) (stS stB stW : MState) (s sA : SState) (p : Place)
    (d : IndDecl) (ps : List Value) (r : Value) (σ c m bw : Nat) (tg : Sem),
    IH K φ m → 0 < stS.env.size → Pre K ρ stS → Rel K ρ φ π stS sA → Strict.SGood K.dm K.Γ φ sA →
    tagOf K φ p indTag s = some (tg, sA) → ckContent stS.env p = some (.abs σ) → tg.asNat = some c →
    WorldBase stS stB → DecTab K.D stW →
    Runs (do let r ← Ochr.ctorRefinement m d ps c; Ochr.refine m σ r; pure r) stB bw r stW →
    ∃ (ρW : Assignment) (ΔW : Nat → TyS), Ext K ρ π stS stW ρW ΔW π ∧ Kept stS stW ∧
      stW.tailNext = stS.tailNext ∧ stW.tailDecl = stS.tailDecl ∧
      hintM { K with Δ := ΔW } ρW stW.goal = hintM K ρ stS.goal ∧
      Pre { K with Δ := ΔW } ρW stW ∧ Rel { K with Δ := ΔW } ρW φ π stW sA

/-- **An unknown of a one-constructor type refined in place** (mixed, NEW; D93, D68): `etaInPlace` (the η record, or a
fresh `C(σ̄)` recorded in `etaRefs`, then `σ := C(σ̄)`) keeps `Pre` and the relation to the same reference state under the
assignment extended at the fields by the value's fields (the record's path condition is met). -/
def EtaTailG : Prop :=
  ∀ (K : RunCtx) (ρ : Assignment) (φ : Future) (π : Nat → Nat) (stS stE : MState) (sA : SState) (p : Place)
    (d : IndDecl) (ps : List Value) (r : Value) (σ m bE : Nat),
    IH K φ m → 0 < stS.env.size → Pre K ρ stS → Rel K ρ φ π stS sA → Strict.SGood K.dm K.Γ φ sA →
    ckContent stS.env p = some (.abs σ) → d.ctors.length = 1 → DecTab K.D stE →
    Runs (Ochr.etaInPlace m σ d ps) stS bE r stE →
    ∃ (ρE : Assignment) (ΔE : Nat → TyS), Ext K ρ π stS stE ρE ΔE π ∧ Kept stS stE ∧
      stE.tailNext = stS.tailNext ∧ stE.tailDecl = stS.tailDecl ∧
      hintM { K with Δ := ΔE } ρE stE.goal = hintM K ρ stS.goal ∧
      Pre { K with Δ := ΔE } ρE stE ∧ Rel { K with Δ := ΔE } ρE φ π stE sA

/-- **The table at a data match** (NEW; `MatchFlagsT`'s at `.matchInd`; read true of the instance). -/
def MatchIndFlagsT (D : Decisions) : Prop :=
  ∀ (sc : List DeclInfo) (p : Place) (ty : String) (arms : List (Hint × Term)),
    (D.flags sc (.matchInd p ty arms)).1 = (D.flags sc (.matchInd p ty arms)).2 ∧
    ((D.flags sc (.matchInd p ty arms)).2 = false → ∀ x a, (x, a) ∈ arms → (D.flags sc a).2 = false)

/-- **The join of a data match read as a proof is empty** (table and checker, NEW; `ProofJoinG`'s at `.matchInd`). -/
def ProofJoinIndG (D : Decisions) : Prop :=
  (∀ (sc : List DeclInfo) (entry : List Place) (p : Place) (ty : String) (arms : List (Hint × Term)),
      (D.flags sc (.matchInd p ty arms)).2 = true → D.joinMoves sc entry (.matchInd p ty arms) = []) ∧
    ∀ (m : Nat) (p : Place) (ty : String) (arms : List (Hint × Term)) (k kc : Value → Value → M Unit) (stW stJ : MState)
      (bj : Nat), DecTab D stJ → (D.flags (DecideScope.topReadings stW) (.matchInd p ty arms)).2 = true →
      Runs (Ochr.joinCont m (.matchInd p ty arms) k) stW bj kc stJ → kc = k

/-- **An arm of a data match read as a proof runs to a proof** (the model at the instance, NEW; `ProofArmM`'s). -/
def ProofArmIndM (K₀ : RunCtx) : Prop :=
  ∀ (Δ : Nat → TyS) (ρ : Assignment) (φ : Future) (hint : TyS) (p : Place) (ty : String) (arms : List (Hint × Term))
    (s' s₁ : SState) (c : Nat) (r : Res), let K := { K₀ with Δ := Δ }
    (K.D.flags (scopeOf s') (.matchInd p ty arms)).2 = true →
    runArm K ρ φ true hint c arms s' = some (r, s₁) → r.1 = .proof ∧ r.2.m = TyM.prop True ∧ s₁ = s'

/-- **The match on a PROOF at the end of a body** (mixed, NEW, one fact; the paper's [Tail-prop], D45, D229/D231): where
`byTypeMatch` reads the match as one on a proof, the step's conclusion. Its content: each arm is checked in a world after
`bindDataFields` (a data field let-bound to a fresh unknown), and the continuation insists on a proof unless the type is
a subsingleton; the reference runs the one arm of a subsingleton with one constructor, and otherwise does not run the
match (`•` at `prop True`, D229); at every good state the scrutinee's type is a true proposition, so some constructor
has a witness, whose world's arm, at the assignment extended by the witness's data fields, gives the leaf (the type true
by (I)); a type with no constructors is false, so no good state reaches the match. NOT derived here. -/
def ProofMatchTailG (K₀ : RunCtx) (φ : Future) : Prop :=
  ∀ n, IH K₀ φ n → ∀ (Δ : Nat → TyS) (ρ : Assignment) (p : Place) (ty : String) (arms : List (Hint × Term)),
    let K := { K₀ with Δ := Δ }
    ∀ (st : MState) (k : Value → Value → M Unit) (s : SState) (π : Nat → Nat) (bh : Nat) (st' : MState) (b : Nat),
      Runs (Ochr.byTypeMatch ty arms) st b true st →
      ModeR st → st.tailNext = false → 0 < st.env.size → st.tailDecl = none → (∀ v T, GrowsM (k v T)) →
      (∀ v T, KeepsTab (k v T)) →
      Pre K ρ st → RecTie K ρ st → Rel K ρ φ π st s → Strict.SGood K.dm K.Γ φ s →
      (Term.matchInd p ty arms).valsOk (Strict.ValsP K ρ φ) → (Term.matchInd p ty arms).absBelow st.absTy.size →
      (Term.matchInd p ty arms).hasHolePrim = false → DecTab K.D st' →
      Runs (Ochr.checkTail n (.matchInd p ty arms) k) st bh () st' →
      TailConcl K ρ φ π st s (.matchInd p ty arms) (runT K ρ φ true (hintM K ρ st.goal) (.matchInd p ty arms)) k

/-! ## The reference's side: the erased match, the match again after the tag (proved) -/

/-- **The reference's data match in tail position, where the table reads it as a proof**: the arm runs to the proof
token, the join is empty; the match is `•` at `prop True`, at the state it started from. -/
theorem runT_matchInd_tailProof {K : RunCtx} {ρ : Assignment} {φ : Future} (hint : TyS) (p : Place) (n : String)
    (arms : List (Hint × Term)) {s sA s₁ : SState} {tg : Sem} {r : Res} {c : Nat}
    (hfl2 : (K.D.flags (scopeOf s) (.matchInd p n arms)).2 = true)
    (hT : TagOk K φ p s) (htag : tagOf K φ p indTag s = some (tg, sA)) (hc : tg.asNat = some c)
    (hnp : tg ≠ .proof) (harm : runArm K ρ φ true hint c arms sA = some (r, s₁)) (hr1 : r.1 = .proof)
    (hj : K.D.joinMoves (scopeOf s₁) (movedPlaces φ sA) (.matchInd p n arms) = []) :
    runT K ρ φ true hint (.matchInd p n arms) s = some ((.proof, .plain (TyM.prop True)), s) := by
  have hip : tg.isProof = false := by cases tg <;> first | exact absurd rfl hnp | rfl
  have hme : optCheck (MatchEntryOk K φ (!true && !tg.isProof && !oneCtor K.Γ n) (.matchInd p n arms) sA) = some ⟨⟩ := by
    unfold optCheck; rw [if_pos]; intro e; simp at e
  have hent : matchEntry K φ (!true && !tg.isProof && !oneCtor K.Γ n) (.matchInd p n arms) sA = (sA, fun _ s₂ => s₂) := by
    simp [matchEntry]
  have hjo : optCheck (tg.isProof = true ∨ oneCtor K.Γ n = true ∨
      JoinDropOk K φ (movedPlaces φ sA) (.matchInd p n arms) s₁) = some ⟨⟩ := by
    unfold optCheck; rw [if_pos]; right; right; unfold JoinDropOk; rw [hj]; trivial
  obtain ⟨r1, r2⟩ := r
  simp only at hr1
  subst hr1
  rw [runT]
  simp only [SM.erasedIf, hfl2, if_true]
  rw [SM.guarded_of hT, htag]
  simp only [bind, Option.bind, hent, tailHint_true]
  rw [hme]
  simp only [hc, harm]
  rw [hjo]

/-- **`MatchReaccessM` at a data match, proved**: where the table does not erase it, the reference's match from the
state after its own tag access is the match from the start. -/
theorem matchIndReaccessM {K : RunCtx} {ρ : Assignment} {φ : Future} {tl : Bool} {hint : TyS} {p : Place} {ty : String}
    {arms : List (Hint × Term)} {s sA : SState} {tg : Sem}
    (hfl : K.D.flags (scopeOf s) (.matchInd p ty arms) = (false, false))
    (hT : TagOk K φ p s) (htag : tagOf K φ p indTag s = some (tg, sA)) :
    runT K ρ φ tl hint (.matchInd p ty arms) sA = runT K ρ φ tl hint (.matchInd p ty arms) s := by
  obtain ⟨hTA, htagA⟩ := tagOf_again htag
  have hsc := scopeOf_tagOf htag
  rw [runT]
  simp only [hsc, hfl, SM.erasedIf, SM.stmtIf, Bool.false_eq_true, if_false]
  rw [SM.guarded_of hTA, SM.guarded_of hT, htagA, htag]

/-- **`MatchReaccessE` at a data match, proved**: the results agree whatever the table. -/
theorem matchIndReaccessE {K : RunCtx} {ρ : Assignment} {φ : Future} {tl : Bool} {hint : TyS} {p : Place} {ty : String}
    {arms : List (Hint × Term)} {s sA : SState} {tg : Sem}
    (hT : TagOk K φ p s) (htag : tagOf K φ p indTag s = some (tg, sA)) :
    (runT K ρ φ tl hint (.matchInd p ty arms) sA).map Prod.fst = (runT K ρ φ tl hint (.matchInd p ty arms) s).map Prod.fst := by
  obtain ⟨hTA, htagA⟩ := tagOf_again htag
  have hsc := scopeOf_tagOf htag
  rw [runT]
  simp only [hsc]
  generalize K.D.flags (scopeOf s) (.matchInd p ty arms) = fl
  simp only [SM.erasedIf, SM.stmtIf]
  rw [SM.guarded_of hTA, SM.guarded_of hT, htagA, htag]
  rcases fl with ⟨a, b⟩
  cases b
  · cases a <;> simp only [Bool.false_eq_true, if_false, if_true, Option.map_map] <;> rfl
  · simp only [if_true]
    split <;> simp_all

/-! ## An arm of a match -/

theorem arms_get_valsOk {P : Value → Prop} : ∀ {arms : List (Hint × Term)} {c : Nat} {x : Hint} {a : Term},
    arms[c]? = some (x, a) → Term.valsOkArms P arms → a.valsOk P
  | [], _, _, _, e, _ => by simp at e
  | (x', a') :: rest, c, x, a, e, h => by
    simp only [Term.valsOkArms] at h
    cases c with
    | zero => simp only [List.getElem?_cons_zero, Option.some.injEq, Prod.mk.injEq] at e; obtain ⟨-, rfl⟩ := e; exact h.1
    | succ c => simp only [List.getElem?_cons_succ] at e; exact arms_get_valsOk e h.2

theorem arms_get_anyAtom {f : Value → Bool} : ∀ {arms : List (Hint × Term)} {c : Nat} {x : Hint} {a : Term},
    arms[c]? = some (x, a) → a.anyAtom f = true → Term.anyAtomArms f arms = true
  | [], _, _, _, e, _ => by simp at e
  | (x', a') :: rest, c, x, a, e, h => by
    simp only [Term.anyAtomArms, Bool.or_eq_true]
    cases c with
    | zero => simp only [List.getElem?_cons_zero, Option.some.injEq, Prod.mk.injEq] at e; obtain ⟨-, rfl⟩ := e; exact .inl h
    | succ c => simp only [List.getElem?_cons_succ] at e; exact .inr (arms_get_anyAtom e h)

theorem arms_get_hole : ∀ {arms : List (Hint × Term)} {c : Nat} {x : Hint} {a : Term},
    arms[c]? = some (x, a) → Term.hasHolePrimArms arms = false → a.hasHolePrim = false
  | [], _, _, _, e, _ => by simp at e
  | (x', a') :: rest, c, x, a, e, h => by
    simp only [Term.hasHolePrimArms, Bool.or_eq_false_iff] at h
    cases c with
    | zero => simp only [List.getElem?_cons_zero, Option.some.injEq, Prod.mk.injEq] at e; obtain ⟨-, rfl⟩ := e; exact h.1
    | succ c => simp only [List.getElem?_cons_succ] at e; exact arms_get_hole e h.2

/-- A declaration the checker finds is the context's (its list is a prefix of the context's). -/
theorem find_of_prefix' {Γ₀ Γ : List IndDecl} (h : Γ₀ <+: Γ) {n : String} {d : IndDecl}
    (hd : Γ₀.find? (·.name == n) = some d) : Γ.find? (·.name == n) = some d := by
  obtain ⟨t, rfl⟩ := h
  rw [List.find?_append, hd]; rfl

/-! ## One arm, to the match's leaf (the full form) -/

section
variable {K : RunCtx} {φ : Future}

/-- **One arm of a data match with several constructors, to the match's leaf** (`matchArm_leaf` at `.matchInd`): from a
world's start (or the known constructor's state), the arm checked with the join's continuation. -/
theorem indArm_leafJ (hJI : JoinContInv) (hJ : JoinContG) (hVC : ValsCongrA) (hc : Strict.FundCtx K)
    {n m : Nat} (ih : IH K φ n) (hmn : m < n) {ρ : Assignment} {π : Nat → Nat} {st stW stJ st₁ : MState}
    {s sA : SState} {p : Place} {ty : String} {arms : List (Hint × Term)} {x : Hint} {a : Term}
    {k kc : Value → Value → M Unit} {tg : Sem} {c bj b₁ : Nat}
    {ρW : Assignment} {ΔW : Nat → TyS} {πW : Nat → Nat}
    (hfl : K.D.flags (scopeOf s) (.matchInd p ty arms) = (false, false))
    (harmfl : (K.D.flags (scopeOf sA) a).2 = false) (hget : arms[c]? = some (x, a)) (hone : oneCtor K.Γ ty = false)
    (hTok : TagOk K φ p s) (htag : tagOf K φ p indTag s = some (tg, sA)) (hcn : tg.asNat = some c) (hnp : tg ≠ .proof)
    (hm : ModeR st) (hne : 0 < st.env.size) (hk : ∀ v T, GrowsM (k v T)) (hkt : ∀ v T, KeepsTab (k v T))
    (hSA : Strict.SGood K.dm K.Γ φ sA)
    (hva : a.valsOk (Strict.ValsP K ρ φ)) (haba : a.absBelow st.absTy.size) (hnha : a.hasHolePrim = false)
    (heW : Ext K ρ π st stW ρW ΔW πW) (hKW : Kept st stW) (htnW : stW.tailNext = false) (htdW : stW.tailDecl = none)
    (hgW : hintM { K with Δ := ΔW } ρW stW.goal = hintM K ρ st.goal) (hrt : RecTie K ρ st)
    (hpW : Pre { K with Δ := ΔW } ρW stW) (hrW : Rel { K with Δ := ΔW } ρW φ πW stW sA)
    (hjc : Runs (Ochr.joinCont m (.matchInd p ty arms) k) stW bj kc stJ)
    (hD₁ : DecTab K.D st₁) (harm : Runs (Ochr.checkTail m a kc) stJ b₁ () st₁) :
    TailOutK K ρ φ π st s (runT K ρ φ true (hintM K ρ st.goal) (.matchInd p ty arms)) k := by
  obtain ⟨hkJ, hmJ, htnJ, htdJ, -, hgrow, hktab⟩ := hJI m _ k kc stW stJ bj hjc
  have hneW : 0 < stW.env.size := by rw [hKW.size]; exact hne
  have hagree : ∀ σ, a.anyAtom (· == .abs σ) = true → AgreeA K ΔW ρ ρW σ := fun σ hσ => by
    obtain ⟨a', d⟩ := heW.agree σ (haba σ hσ)
    exact ⟨a'.symm, d.symm⟩
  have hO := (ih m hmn ΔW ρW).2 a stJ kc sA πW b₁ st₁
    (hm.of_modeEq (hKW.mode.trans hmJ)) (htnJ.trans htnW) (by rw [← ColumnC.size_of_erase hkJ.env]; exact hneW)
    (htdJ.trans htdW) (hgrow hk) (hktab hkt) (hpW.of_kern hkJ)
    (hrt.move (by rw [← hkJ.recStack]; exact hKW.stack) (by rw [← hkJ.absTy]; exact heW.abs)
      fun σ hσ => (heW.agree σ hσ).1) (hrW.of_kern hkJ) hSA (hVC K ΔW ρ ρW φ _ hagree hva)
    (absBelow_mono haba (by rw [← hkJ.absTy]; exact heW.abs)) hnha hD₁ harm
  obtain ⟨stl, v, T, ⟨bk, stk, hkr⟩, ⟨ρ₁, Δ₁, π₁, r, s₁, he₁, hx₁, hm₁, ha₁, hl₁, hp₁, hr₁, hg₁⟩, hK₁⟩ := hO.1 harmfl
  have hgJ : hintM { K with Δ := ΔW } ρW stJ.goal = hintM K ρ st.goal := by rw [← hkJ.goal]; exact hgW
  rw [hgJ] at hx₁
  have hx₁' : runT K ρ φ true (hintM K ρ st.goal) a sA = some (r, s₁) := by
    rw [runT_congrA K ΔW ρ ρW φ true _ _ sA hagree]; exact hx₁
  obtain ⟨-, -, -, hS₁⟩ := Strict.fund_all hc _ hva true _ sA s₁ r hSA hx₁'
  obtain ⟨hjok, stl₂, v₂, ρ₂, Δ₂, π₂, he₂, hK₂, hm₂, ha₂, hl₂, hp₂, hr₂, hg₂, bk', stk', hk'⟩ :=
    hJ { K with Δ := ΔW } ρW φ πW stW stJ sA _ k kc m bj (ih.lower (Nat.le_of_lt hmn) ΔW) hneW hpW hrW hjc ρ₁ Δ₁ π₁
      stl stk v T r s₁ bk he₁ hK₁ hm₁ (ha₁ T rfl) hl₁ hp₁ hr₁ hS₁ hkr
  refine ⟨stl₂, v₂, T, ⟨bk', stk', hk'⟩, ⟨ρ₂, Δ₂, π₂, r, joinDrop K φ (movedPlaces φ sA) (.matchInd p ty arms) s₁,
    (heW.trans ((he₁.congr hkJ.absTy hkJ.nextLoan rfl rfl))).trans he₂, ?_, hm₂, fun T' e => by cases e; exact ha₂,
    hl₂, hp₂, hr₂, hg₂.trans (hg₁.trans hgJ)⟩, ((hKW.trans (Kept.of_kern hkJ hmJ)).trans hK₁).trans hK₂⟩
  have := runT_matchInd_tailData (K := K) (ρ := ρ) (φ := φ) (hintM K ρ st.goal) p ty arms hfl hTok htag hcn hnp
    (by rw [runArm_get arms c x a hget]; exact hx₁') (.inr hjok)
  rw [hone] at this
  exact this

/-- **The one arm of a data match with one constructor, to the match's leaf** (D93: no join): the arm checked with the
continuation itself. -/
theorem indArm_leaf1 (hVC : ValsCongrA)
    {n m : Nat} (ih : IH K φ n) (hmn : m < n) {ρ : Assignment} {π : Nat → Nat} {st stW st₁ : MState}
    {s sA : SState} {p : Place} {ty : String} {arms : List (Hint × Term)} {x : Hint} {a : Term}
    {k : Value → Value → M Unit} {tg : Sem} {c b₁ : Nat}
    {ρW : Assignment} {ΔW : Nat → TyS} {πW : Nat → Nat}
    (hfl : K.D.flags (scopeOf s) (.matchInd p ty arms) = (false, false))
    (harmfl : (K.D.flags (scopeOf sA) a).2 = false) (hget : arms[c]? = some (x, a)) (hone : oneCtor K.Γ ty = true)
    (hTok : TagOk K φ p s) (htag : tagOf K φ p indTag s = some (tg, sA)) (hcn : tg.asNat = some c) (hnp : tg ≠ .proof)
    (hm : ModeR st) (hne : 0 < st.env.size) (hk : ∀ v T, GrowsM (k v T)) (hkt : ∀ v T, KeepsTab (k v T))
    (hSA : Strict.SGood K.dm K.Γ φ sA)
    (hva : a.valsOk (Strict.ValsP K ρ φ)) (haba : a.absBelow st.absTy.size) (hnha : a.hasHolePrim = false)
    (heW : Ext K ρ π st stW ρW ΔW πW) (hKW : Kept st stW) (htnW : stW.tailNext = false) (htdW : stW.tailDecl = none)
    (hgW : hintM { K with Δ := ΔW } ρW stW.goal = hintM K ρ st.goal) (hrt : RecTie K ρ st)
    (hpW : Pre { K with Δ := ΔW } ρW stW) (hrW : Rel { K with Δ := ΔW } ρW φ πW stW sA)
    (hD₁ : DecTab K.D st₁) (harm : Runs (Ochr.checkTail m a k) stW b₁ () st₁) :
    TailOutK K ρ φ π st s (runT K ρ φ true (hintM K ρ st.goal) (.matchInd p ty arms)) k := by
  have hneW : 0 < stW.env.size := by rw [hKW.size]; exact hne
  have hagree : ∀ σ, a.anyAtom (· == .abs σ) = true → AgreeA K ΔW ρ ρW σ := fun σ hσ => by
    obtain ⟨a', d⟩ := heW.agree σ (haba σ hσ)
    exact ⟨a'.symm, d.symm⟩
  have hO := (ih m hmn ΔW ρW).2 a stW k sA πW b₁ st₁
    (hm.of_modeEq hKW.mode) htnW hneW htdW hk hkt hpW (hrt.move hKW.stack heW.abs fun σ hσ => (heW.agree σ hσ).1)
    hrW hSA (hVC K ΔW ρ ρW φ _ hagree hva)
    (absBelow_mono haba heW.abs) hnha hD₁ harm
  obtain ⟨stl, v, T, hkr, ⟨ρ₁, Δ₁, π₁, r, s₁, he₁, hx₁, hm₁, ha₁, hl₁, hp₁, hr₁, hg₁⟩, hK₁⟩ := hO.1 harmfl
  rw [hgW] at hx₁
  have hx₁' : runT K ρ φ true (hintM K ρ st.goal) a sA = some (r, s₁) := by
    rw [runT_congrA K ΔW ρ ρW φ true _ _ sA hagree]; exact hx₁
  refine ⟨stl, v, T, hkr, ⟨ρ₁, Δ₁, π₁, r, s₁, heW.trans he₁, ?_, hm₁, ha₁, hl₁, hp₁, hr₁, hg₁.trans hgW⟩, hKW.trans hK₁⟩
  have := runT_matchInd_tailData (K := K) (ρ := ρ) (φ := φ) (hintM K ρ st.goal) p ty arms hfl hTok htag hcn hnp
    (by rw [runArm_get arms c x a hget]; exact hx₁') (.inl hone)
  rw [hone] at this
  exact this

end

/-! ## The split at the end of a body, on a data type the table does not read as a proof -/

section
variable {K : RunCtx} {φ : Future}

/-- **The split at the end of a body on a data type, the match not read as a proof and not on a proof** (the full form,
`TailOutK`), at a direct scrutinee (the arms' covering of the constructors from the run, main's D146). ASSUMES `TailMatchIndInv`, `JoinContInv` (checker),
`MatchIndFlagsT` (table), `MatchIndTagG`, `ScrutTypeG`, `WorldRefineIndG`, `EtaTailG`, `JoinContG`, `GenTailG` (mixed),
`ValsCongrA` (model, proved), `Strict.FundCtx K`. -/
theorem tStepMatchInd_data (hInv : TailMatchIndInv) (hJI : JoinContInv) (hMF : MatchIndFlagsT K.D)
    (hTag : MatchIndTagG) (hST : ScrutTypeG) (hW : WorldRefineIndG) (hE : EtaTailG) (hJ : JoinContG) (hG : GenTailG)
    (hVC : ValsCongrA) (hc : Strict.FundCtx K) {n : Nat} (ih : IH K φ n) (ρ : Assignment) (p : Place) (ty : String)
    (arms : List (Hint × Term))
    (st : MState) (k : Value → Value → M Unit) (s : SState) (π : Nat → Nat) (bh : Nat) (st' : MState)
    (hm : ModeR st) (htn : st.tailNext = false) (hne : 0 < st.env.size) (htd : st.tailDecl = none)
    (hk : ∀ v T, GrowsM (k v T)) (hkt : ∀ v T, KeepsTab (k v T)) (hp : Pre K ρ st) (hrt : RecTie K ρ st)
    (hr : Rel K ρ φ π st s)
    (hS : Strict.SGood K.dm K.Γ φ s)
    (hv : (Term.matchInd p ty arms).valsOk (Strict.ValsP K ρ φ)) (hab : (Term.matchInd p ty arms).absBelow st.absTy.size)
    (hnh : (Term.matchInd p ty arms).hasHolePrim = false) (hD : DecTab K.D st')
    (hrun : Runs (Ochr.checkTail n (.matchInd p ty arms) k) st bh () st')
    (hdat : ¬ ∃ b, Runs (Ochr.byTypeMatch ty arms) st b true st) (hdir : p.Direct)
    (hfl2 : (K.D.flags (scopeOf s) (.matchInd p ty arms)).2 = false) :
    TailOutK K ρ φ π st s (runT K ρ φ true (hintM K ρ st.goal) (.matchInd p ty arms)) k := by
  have hfl : K.D.flags (scopeOf s) (.matchInd p ty arms) = (false, false) := by
    have h1 := (hMF (scopeOf s) p ty arms).1
    rw [hfl2] at h1
    exact Prod.ext h1 hfl2
  obtain ⟨m, st₀, stA, bA, d, hmn, hk₀, hme₀, htn₀, htd₀, hfind, hsort, hacc, hDA, hcases⟩ :=
    (hInv n p ty arms k st st' bh K.D hdir (TabInv.of_pre hp) hk hkt hD hrun).resolve_left hdat
  obtain ⟨hTok, tg, sA, ρA, ΔA, πA, htag, heA₀, hKA₀, htnA₀, htdA₀, hgA₀, hpA, hrA, hnp, cT, hcT, hcTlt, hcTk⟩ :=
    hTag K ρ φ π st₀ stA s p ty d m bA (fun m' hm' => ih m' (by omega)) (hm.of_modeEq hme₀)
      (by rw [← ColumnC.size_of_erase hk₀.env]; exact hne) (hp.of_kern hk₀) (hr.of_kern hk₀) hS hDA
      (by rw [← hk₀.inds]; exact hfind) hsort hacc
  have heA : Ext K ρ π st stA ρA ΔA πA := Ext.of_kern_left hk₀ heA₀
  have hKA : Kept st stA := (Kept.of_kern hk₀ hme₀).trans hKA₀
  have htnA : stA.tailNext = st.tailNext := htnA₀.trans htn₀
  have htdA : stA.tailDecl = st.tailDecl := htdA₀.trans htd₀
  have hgA : hintM { K with Δ := ΔA } ρA stA.goal = hintM K ρ st.goal := by rw [hgA₀, hk₀.goal]
  have hSA : Strict.SGood K.dm K.Γ φ sA := Strict.sgood_tagOf hS hTok htag
  have hsc : scopeOf sA = scopeOf s := by rw [scopeOf_rel hr, scopeOf_rel hrA, hKA.top]
  have hneA : 0 < stA.env.size := by rw [hKA.size]; exact hne
  have hΓ : K.Γ.find? (·.name == ty) = some d := find_of_prefix' hp.ctx.inds hfind
  have hone : oneCtor K.Γ ty = (d.ctors.length == 1) := by simp [oneCtor, hΓ]
  have hvA : Term.valsOkArms (Strict.ValsP K ρ φ) arms := by simpa [Term.valsOk] using hv
  have hnhA : Term.hasHolePrimArms arms = false := by simpa [Term.hasHolePrim] using hnh
  -- an arm's entry conditions
  have harm_ok : ∀ c x a, arms[c]? = some (x, a) →
      a.valsOk (Strict.ValsP K ρ φ) ∧ a.absBelow st.absTy.size ∧ a.hasHolePrim = false ∧
        (K.D.flags (scopeOf sA) a).2 = false := fun c x a hget =>
    ⟨arms_get_valsOk hget hvA, fun σ hσ => hab σ (by simp only [Term.anyAtom]; exact arms_get_anyAtom hget hσ),
      arms_get_hole hget hnhA,
      by rw [hsc]; exact (hMF (scopeOf s) p ty arms).2 hfl2 x a (List.mem_of_getElem? hget)⟩
  rcases hcases with ⟨c, h, ps, fs, x, a, stS, bS, dps, hcon, hget, hscr, hDS, hcase⟩ |
      ⟨σ, ps, stS, bS, hσ, hscr, hDS, hcase⟩ | ⟨v, σ, stG, st₁, bg, b₁, hvs, hcv, hgen, hDG, hre, hD₁⟩
  · -- a known constructor
    have hcn : tg.asNat = some c := by rw [hcTk c h ps fs hcon]; exact hcT
    obtain ⟨ρS, ΔS, heS, hKS, henv, htnS, htdS, hgS, hpS, hrS⟩ :=
      hST { K with Δ := ΔA } ρA φ πA stA stS sA p ty dps m bS (ih.lower (by omega) ΔA) hneA hpA hrA hSA hDS hscr
    obtain ⟨hva, haba, hnha, harmfl⟩ := harm_ok c x a hget
    rcases hcase with ⟨hlen, st₁, b₁, harm, hD₁⟩ | ⟨hlen, kc, stJ, st₁, bj, b₁, hjc, harm, hD₁⟩
    · exact indArm_leaf1 hVC ih (by omega) hfl harmfl hget (by rw [hone, hlen]; rfl) hTok htag hcn hnp hm hne hk hkt
        hSA hva haba hnha (heA.trans heS) (hKA.trans hKS) ((htnS.trans htnA).trans htn) ((htdS.trans htdA).trans htd)
        (hgS.trans hgA) hrt hpS hrS hD₁ harm
    · exact indArm_leafJ hJI hJ hVC hc ih (by omega) hfl harmfl hget (by rw [hone]; simp [hlen]) hTok htag hcn hnp hm
        hne hk hkt hSA hva haba hnha (heA.trans heS) (hKA.trans hKS) ((htnS.trans htnA).trans htn)
        ((htdS.trans htdA).trans htd) (hgS.trans hgA) hrt hpS hrS hjc hD₁ harm
  · -- an unknown
    obtain ⟨ρS, ΔS, heS, hKS, henv, htnS, htdS, hgS, hpS, hrS⟩ :=
      hST { K with Δ := ΔA } ρA φ πA stA stS sA p ty (d, ps) m bS (ih.lower (by omega) ΔA) hneA hpA hrA hSA hDS hscr
    have hσS : ckContent stS.env p = some (.abs σ) := by rw [henv]; exact hσ
    have hneS : 0 < stS.env.size := by rw [hKS.size]; exact hneA
    rcases hcase with ⟨hlen, r, stE, st₁, bE, b₁, heta, hDE, hre, hD₁⟩ | ⟨hlen, hlenA, hworlds⟩
    · -- one constructor: refined in place, then the match again
      obtain ⟨ρE, ΔE, heE, hKE, htnE, htdE, hgE, hpE, hrE⟩ :=
        hE { K with Δ := ΔS } ρS φ πA stS stE sA p d ps r σ m bE (ih.lower (by omega) ΔS) hneS hpS hrS hSA hσS hlen hDE
          heta
      have he : Ext K ρ π st stE ρE ΔE πA := (heA.trans heS).trans heE
      have hK' : Kept st stE := (hKA.trans hKS).trans hKE
      have hagree : ∀ σ', (Term.matchInd p ty arms).anyAtom (· == .abs σ') = true → AgreeA K ΔE ρ ρE σ' :=
        fun σ' hσ' => by obtain ⟨a', d'⟩ := he.agree σ' (hab σ' hσ'); exact ⟨a'.symm, d'.symm⟩
      have hO := (ih m (by omega) ΔE ρE).2 (.matchInd p ty arms) stE k sA πA b₁ st₁
        (hm.of_modeEq hK'.mode) (((htnE.trans htnS).trans htnA).trans htn) (by rw [hK'.size]; exact hne)
        (((htdE.trans htdS).trans htdA).trans htd) hk hkt hpE (hrt.move hK'.stack he.abs fun σ hσ => (he.agree σ hσ).1)
        hrE hSA (hVC K ΔE ρ ρE φ _ hagree hv)
        (absBelow_mono hab he.abs) hnh hD₁ hre
      obtain ⟨stl, v', T, hkr, ⟨ρ₁, Δ₁, π₁, r', s₁, he₁, hx₁, hm₁, ha₁, hl₁, hp₁, hr₁, hg₁⟩, hK₁⟩ :=
        hO.1 (by rw [hsc]; exact hfl2)
      rw [(hgE.trans hgS).trans hgA] at hx₁
      refine ⟨stl, v', T, hkr, ⟨ρ₁, Δ₁, π₁, r', s₁, he.trans he₁, ?_, hm₁, ha₁, hl₁, hp₁, hr₁,
        hg₁.trans ((hgE.trans hgS).trans hgA)⟩, hK'.trans hK₁⟩
      rw [← matchIndReaccessM hfl hTok htag, runT_congrA K ΔE ρ ρE φ true _ _ sA hagree]
      exact hx₁
    · -- several constructors: the world of the assignment's constructor
      have hcA : cT < arms.length := by rw [hlenA]; exact hcTlt
      have hget : arms[cT]? = some (arms[cT].1, arms[cT].2) := by rw [List.getElem?_eq_getElem hcA]
      obtain ⟨hva, haba, hnha, harmfl⟩ := harm_ok cT _ _ hget
      obtain ⟨stB, stW, stJ, st₁, r, kc, bw, bj, b₁, hbase, href, hDW, hjc, harm, hD₁⟩ :=
        hworlds cT _ _ hcTlt hget
      obtain ⟨ρW, ΔW, heW, hKW, htnW, htdW, hgW, hpW, hrW⟩ :=
        hW { K with Δ := ΔS } ρS φ πA stS stB stW s sA p d ps r σ cT m bw tg (ih.lower (by omega) ΔS) hneS hpS hrS
          hSA htag hσS hcT hbase hDW href
      exact indArm_leafJ hJI hJ hVC hc ih (by omega) hfl harmfl hget (by rw [hone]; simp [hlen]) hTok htag hcT hnp hm
        hne hk hkt hSA hva haba hnha ((heA.trans heS).trans heW) ((hKA.trans hKS).trans hKW)
        (((htnW.trans htnS).trans htnA).trans htn) (((htdW.trans htdS).trans htdA).trans htd)
        ((hgW.trans hgS).trans hgA) hrt hpW hrW hjc hD₁ harm
  · -- a sealed scrutinee: generalised, then the match again
    obtain ⟨ρG, ΔG, heG, hKG, htnG, htdG, hgG, hpG, hrG⟩ :=
      hG { K with Δ := ΔA } ρA φ πA stA stG sA p v σ m bg (ih.lower (by omega) ΔA) hneA hpA hrA hSA hcv hvs hDG hgen
    have he : Ext K ρ π st stG ρG ΔG πA := heA.trans heG
    have hagree : ∀ σ', (Term.matchInd p ty arms).anyAtom (· == .abs σ') = true → AgreeA K ΔG ρ ρG σ' :=
      fun σ' hσ' => by obtain ⟨a', d'⟩ := he.agree σ' (hab σ' hσ'); exact ⟨a'.symm, d'.symm⟩
    have hO := (ih m (by omega) ΔG ρG).2 (.matchInd p ty arms) stG k sA πA b₁ st₁
      (hm.of_modeEq (hKA.trans hKG).mode) ((htnG.trans htnA).trans htn) (by rw [(hKA.trans hKG).size]; exact hne)
      ((htdG.trans htdA).trans htd) hk hkt hpG (hrt.move (hKA.trans hKG).stack he.abs fun σ hσ => (he.agree σ hσ).1)
      hrG hSA (hVC K ΔG ρ ρG φ _ hagree hv) (absBelow_mono hab he.abs) hnh hD₁ hre
    obtain ⟨stl, v', T, hkr, ⟨ρ₁, Δ₁, π₁, r, s₁, he₁, hx₁, hm₁, ha₁, hl₁, hp₁, hr₁, hg₁⟩, hK₁⟩ :=
      hO.1 (by rw [hsc]; exact hfl2)
    rw [hgG.trans hgA] at hx₁
    refine ⟨stl, v', T, hkr, ⟨ρ₁, Δ₁, π₁, r, s₁, he.trans he₁, ?_, hm₁, ha₁, hl₁, hp₁, hr₁, hg₁.trans (hgG.trans hgA)⟩,
      (hKA.trans hKG).trans hK₁⟩
    rw [← matchIndReaccessM hfl hTok htag, runT_congrA K ΔG ρ ρG φ true _ _ sA hagree]
    exact hx₁

end

/-- An extension to a state is one to a state with the same kernel. -/
theorem Ext.of_kern_right {K : RunCtx} {ρ : Assignment} {π : Nat → Nat} {st st₁ st₂ : MState} {ρ' : Assignment}
    {Δ' : Nat → TyS} {π' : Nat → Nat} (h : Ext K ρ π st st₁ ρ' Δ' π') (hk : Kern st₁ st₂) : Ext K ρ π st st₂ ρ' Δ' π' where
  abs := by rw [← hk.absTy]; exact h.abs
  lab := by rw [← hk.nextLoan]; exact h.lab
  agree := h.agree
  ren := h.ren

/-! ## The split at the end of a body, on a data type the table reads as a proof (the erased form) -/

section
variable {K : RunCtx} {φ : Future}

/-- **One arm of a data match read as a proof, to the match's leaf** (the erased form): the arm checked with the
continuation itself (the join is empty), from a state related to the reference's after the tag. -/
theorem indArm_leafE (hPJ : ProofJoinIndG K.D) (hPA : ProofArmIndM K) (hVC : ValsCongrA)
    {n m : Nat} (ih : IH K φ n) (hmn : m < n) {ρ : Assignment} {π : Nat → Nat} {st stW st₁ : MState}
    {s sA : SState} {p : Place} {ty : String} {arms : List (Hint × Term)} {x : Hint} {a : Term}
    {k : Value → Value → M Unit} {tg : Sem} {c b₁ : Nat}
    {ρW : Assignment} {ΔW : Nat → TyS} {πW : Nat → Nat}
    (hfl2 : (K.D.flags (scopeOf s) (.matchInd p ty arms)).2 = true) (hget : arms[c]? = some (x, a))
    (hTok : TagOk K φ p s) (htag : tagOf K φ p indTag s = some (tg, sA)) (hcn : tg.asNat = some c) (hnp : tg ≠ .proof)
    (hsc : scopeOf sA = scopeOf s)
    (hm : ModeR st) (hne : 0 < st.env.size) (hk : ∀ v T, GrowsM (k v T)) (hkt : ∀ v T, KeepsTab (k v T))
    (hSA : Strict.SGood K.dm K.Γ φ sA)
    (hva : a.valsOk (Strict.ValsP K ρ φ)) (haba : a.absBelow st.absTy.size) (hnha : a.hasHolePrim = false)
    (heW : Ext K ρ π st stW ρW ΔW πW) (hKW : Kept st stW) (htnW : stW.tailNext = false) (htdW : stW.tailDecl = none)
    (hgW : hintM { K with Δ := ΔW } ρW stW.goal = hintM K ρ st.goal) (hrt : RecTie K ρ st)
    (hpW : Pre { K with Δ := ΔW } ρW stW) (hrW : Rel { K with Δ := ΔW } ρW φ πW stW sA)
    (hD₁ : DecTab K.D st₁) (harm : Runs (Ochr.checkTail m a k) stW b₁ () st₁) :
    TailOutE K ρ φ π st s (runT K ρ φ true (hintM K ρ st.goal) (.matchInd p ty arms)) k := by
  have hneW : 0 < stW.env.size := by rw [hKW.size]; exact hne
  have hagree : ∀ σ, a.anyAtom (· == .abs σ) = true → AgreeA K ΔW ρ ρW σ := fun σ hσ => by
    obtain ⟨a', d⟩ := heW.agree σ (haba σ hσ)
    exact ⟨a'.symm, d.symm⟩
  have hO := (ih m hmn ΔW ρW).2 a stW k sA πW b₁ st₁
    (hm.of_modeEq hKW.mode) htnW hneW htdW hk hkt hpW (hrt.move hKW.stack heW.abs fun σ hσ => (heW.agree σ hσ).1)
    hrW hSA (hVC K ΔW ρ ρW φ _ hagree hva)
    (absBelow_mono haba heW.abs) hnha hD₁ harm
  obtain ⟨stl, v, T, hkr, ⟨ρ₁, Δ₁, π₁, r, s₁, he₁, hx₁, hm₁, ha₁, hp₁, hg₁⟩, hK₁⟩ := hO.2
  rw [hgW] at hx₁
  have hx₁' : runT K ρ φ true (hintM K ρ st.goal) a sA = some (r, s₁) := by
    rw [runT_congrA K ΔW ρ ρW φ true _ _ sA hagree]; exact hx₁
  have hxa : runArm K ρ φ true (hintM K ρ st.goal) c arms sA = some (r, s₁) := by
    rw [runArm_get arms c x a hget]; exact hx₁'
  obtain ⟨hr1, hr2, hs₁⟩ := hPA K.Δ ρ φ _ p ty arms sA s₁ c r (by rw [hsc]; exact hfl2) hxa
  refine ⟨stl, v, T, hkr, ⟨ρ₁, Δ₁, π₁, (.proof, .plain (TyM.prop True)), s, heW.trans he₁, ?_, ?_, ?_, hp₁,
    hg₁.trans hgW⟩, hKW.trans hK₁⟩
  · exact runT_matchInd_tailProof _ p ty arms hfl2 hTok htag hcn hnp hxa hr1
      (hPJ.1 _ _ p ty arms (by rw [hs₁, hsc]; exact hfl2))
  · show meanV _ _ _ (.plain (TyM.prop True)) v = .proof
    rw [Ochr.Meaning.meanV_hintM _ _ _ v (.plain (TyM.prop True)) r.2 hr2.symm, hm₁, hr1]
  · exact ha₁.trans hr2

/-- **The split at the end of a body on a data type the table reads as a proof** (the erased form, `TailOutE`; a lemma's
body), at a direct scrutinee (the arms' covering from the run, main's D146). ASSUMES `TailMatchIndInv`, `JoinContInv` (checker),
`ProofJoinIndG` (table and checker), `MatchIndTagG`, `ScrutTypeG`, `WorldRefineIndG`, `EtaTailG`, `GenTailG` (mixed),
`ProofArmIndM` (model at the instance), `ValsCongrA` (proved). -/
theorem tStepMatchInd_proofRead (hInv : TailMatchIndInv) (hJI : JoinContInv) (hPJ : ProofJoinIndG K.D)
    (hTag : MatchIndTagG) (hST : ScrutTypeG) (hW : WorldRefineIndG) (hE : EtaTailG) (hG : GenTailG)
    (hPA : ProofArmIndM K) (hVC : ValsCongrA) {n : Nat} (ih : IH K φ n) (ρ : Assignment) (p : Place) (ty : String)
    (arms : List (Hint × Term))
    (st : MState) (k : Value → Value → M Unit) (s : SState) (π : Nat → Nat) (bh : Nat) (st' : MState)
    (hm : ModeR st) (htn : st.tailNext = false) (hne : 0 < st.env.size) (htd : st.tailDecl = none)
    (hk : ∀ v T, GrowsM (k v T)) (hkt : ∀ v T, KeepsTab (k v T)) (hp : Pre K ρ st) (hrt : RecTie K ρ st)
    (hr : Rel K ρ φ π st s)
    (hS : Strict.SGood K.dm K.Γ φ s)
    (hv : (Term.matchInd p ty arms).valsOk (Strict.ValsP K ρ φ)) (hab : (Term.matchInd p ty arms).absBelow st.absTy.size)
    (hnh : (Term.matchInd p ty arms).hasHolePrim = false) (hD : DecTab K.D st')
    (hrun : Runs (Ochr.checkTail n (.matchInd p ty arms) k) st bh () st')
    (hdat : ¬ ∃ b, Runs (Ochr.byTypeMatch ty arms) st b true st) (hdir : p.Direct)
    (hfl2 : (K.D.flags (scopeOf s) (.matchInd p ty arms)).2 = true) :
    TailOutE K ρ φ π st s (runT K ρ φ true (hintM K ρ st.goal) (.matchInd p ty arms)) k := by
  obtain ⟨m, st₀, stA, bA, d, hmn, hk₀, hme₀, htn₀, htd₀, hfind, hsort, hacc, hDA, hcases⟩ :=
    (hInv n p ty arms k st st' bh K.D hdir (TabInv.of_pre hp) hk hkt hD hrun).resolve_left hdat
  obtain ⟨hTok, tg, sA, ρA, ΔA, πA, htag, heA₀, hKA₀, htnA₀, htdA₀, hgA₀, hpA, hrA, hnp, cT, hcT, hcTlt, hcTk⟩ :=
    hTag K ρ φ π st₀ stA s p ty d m bA (fun m' hm' => ih m' (by omega)) (hm.of_modeEq hme₀)
      (by rw [← ColumnC.size_of_erase hk₀.env]; exact hne) (hp.of_kern hk₀) (hr.of_kern hk₀) hS hDA
      (by rw [← hk₀.inds]; exact hfind) hsort hacc
  have heA : Ext K ρ π st stA ρA ΔA πA := Ext.of_kern_left hk₀ heA₀
  have hKA : Kept st stA := (Kept.of_kern hk₀ hme₀).trans hKA₀
  have htnA : stA.tailNext = st.tailNext := htnA₀.trans htn₀
  have htdA : stA.tailDecl = st.tailDecl := htdA₀.trans htd₀
  have hgA : hintM { K with Δ := ΔA } ρA stA.goal = hintM K ρ st.goal := by rw [hgA₀, hk₀.goal]
  have hSA : Strict.SGood K.dm K.Γ φ sA := Strict.sgood_tagOf hS hTok htag
  have hsc : scopeOf sA = scopeOf s := by rw [scopeOf_rel hr, scopeOf_rel hrA, hKA.top]
  have hneA : 0 < stA.env.size := by rw [hKA.size]; exact hne
  have hΓ : K.Γ.find? (·.name == ty) = some d := find_of_prefix' hp.ctx.inds hfind
  have hvA : Term.valsOkArms (Strict.ValsP K ρ φ) arms := by simpa [Term.valsOk] using hv
  have hnhA : Term.hasHolePrimArms arms = false := by simpa [Term.hasHolePrim] using hnh
  have harm_ok : ∀ (c : Nat) (x : Hint) (a : Term), arms[c]? = some (x, a) →
      a.valsOk (Strict.ValsP K ρ φ) ∧ a.absBelow st.absTy.size ∧ a.hasHolePrim = false := fun c x a hget =>
    ⟨arms_get_valsOk hget hvA, fun σ hσ => hab σ (by simp only [Term.anyAtom]; exact arms_get_anyAtom hget hσ),
      arms_get_hole hget hnhA⟩
  -- the join's continuation is the continuation itself (the join of a match read as a proof is empty)
  have hjk : ∀ (stW stJ : MState) (kc : Value → Value → M Unit) (bj : Nat), Kept st stW → DecTab K.D stW →
      Runs (Ochr.joinCont m (.matchInd p ty arms) k) stW bj kc stJ →
      kc = k ∧ Kern stW stJ ∧ ModeEq stW stJ ∧ stJ.tailNext = stW.tailNext ∧ stJ.tailDecl = stW.tailDecl :=
    fun stW stJ kc bj hKW hDW hjc => by
      obtain ⟨hkJ, hmJ, htnJ, htdJ, -, -, -⟩ := hJI m _ k kc stW stJ bj hjc
      exact ⟨hPJ.2 m p ty arms k kc stW stJ bj (DecTab.of_kern hkJ hDW)
        (by rw [hKW.top, ← scopeOf_rel hr]; exact hfl2) hjc, hkJ, hmJ, htnJ, htdJ⟩
  rcases hcases with ⟨c, h, ps, fs, x, a, stS, bS, dps, hcon, hget, hscr, hDS, hcase⟩ |
      ⟨σ, ps, stS, bS, hσ, hscr, hDS, hcase⟩ | ⟨v, σ, stG, st₁, bg, b₁, hvs, hcv, hgen, hDG, hre, hD₁⟩
  · have hcn : tg.asNat = some c := by rw [hcTk c h ps fs hcon]; exact hcT
    obtain ⟨ρS, ΔS, heS, hKS, henv, htnS, htdS, hgS, hpS, hrS⟩ :=
      hST { K with Δ := ΔA } ρA φ πA stA stS sA p ty dps m bS (ih.lower (by omega) ΔA) hneA hpA hrA hSA hDS hscr
    obtain ⟨hva, haba, hnha⟩ := harm_ok c x a hget
    rcases hcase with ⟨-, st₁, b₁, harm, hD₁⟩ | ⟨-, kc, stJ, st₁, bj, b₁, hjc, harm, hD₁⟩
    · exact indArm_leafE hPJ hPA hVC ih (by omega) hfl2 hget hTok htag hcn hnp hsc hm hne hk hkt hSA hva haba hnha
        (heA.trans heS) (hKA.trans hKS) ((htnS.trans htnA).trans htn) ((htdS.trans htdA).trans htd) (hgS.trans hgA)
        hrt hpS hrS hD₁ harm
    · obtain ⟨rfl, hkJ, hmJ, htnJ, htdJ⟩ := hjk stS stJ kc bj (hKA.trans hKS) hDS hjc
      exact indArm_leafE hPJ hPA hVC ih (by omega) hfl2 hget hTok htag hcn hnp hsc hm hne hk hkt hSA hva haba hnha
        (Ext.of_kern_right (heA.trans heS) hkJ) ((hKA.trans hKS).trans (Kept.of_kern hkJ hmJ))
        (htnJ.trans ((htnS.trans htnA).trans htn)) (htdJ.trans ((htdS.trans htdA).trans htd))
        (by rw [← hkJ.goal]; exact hgS.trans hgA) hrt (hpS.of_kern hkJ) (hrS.of_kern hkJ) hD₁ harm
  · obtain ⟨ρS, ΔS, heS, hKS, henv, htnS, htdS, hgS, hpS, hrS⟩ :=
      hST { K with Δ := ΔA } ρA φ πA stA stS sA p ty (d, ps) m bS (ih.lower (by omega) ΔA) hneA hpA hrA hSA hDS hscr
    have hσS : ckContent stS.env p = some (.abs σ) := by rw [henv]; exact hσ
    have hneS : 0 < stS.env.size := by rw [hKS.size]; exact hneA
    rcases hcase with ⟨hlen, r, stE, st₁, bE, b₁, heta, hDE, hre, hD₁⟩ | ⟨hlen, hlenA, hworlds⟩
    · obtain ⟨ρE, ΔE, heE, hKE, htnE, htdE, hgE, hpE, hrE⟩ :=
        hE { K with Δ := ΔS } ρS φ πA stS stE sA p d ps r σ m bE (ih.lower (by omega) ΔS) hneS hpS hrS hSA hσS hlen hDE
          heta
      have he : Ext K ρ π st stE ρE ΔE πA := (heA.trans heS).trans heE
      have hK' : Kept st stE := (hKA.trans hKS).trans hKE
      have hagree : ∀ σ', (Term.matchInd p ty arms).anyAtom (· == .abs σ') = true → AgreeA K ΔE ρ ρE σ' :=
        fun σ' hσ' => by obtain ⟨a', d'⟩ := he.agree σ' (hab σ' hσ'); exact ⟨a'.symm, d'.symm⟩
      have hO := (ih m (by omega) ΔE ρE).2 (.matchInd p ty arms) stE k sA πA b₁ st₁
        (hm.of_modeEq hK'.mode) (((htnE.trans htnS).trans htnA).trans htn) (by rw [hK'.size]; exact hne)
        (((htdE.trans htdS).trans htdA).trans htd) hk hkt hpE (hrt.move hK'.stack he.abs fun σ hσ => (he.agree σ hσ).1)
        hrE hSA (hVC K ΔE ρ ρE φ _ hagree hv)
        (absBelow_mono hab he.abs) hnh hD₁ hre
      obtain ⟨stl, v', T, hkr, ⟨ρ₁, Δ₁, π₁, r', s₁, he₁, hx₁, hm₁, ha₁, hp₁, hg₁⟩, hK₁⟩ := hO.2
      rw [(hgE.trans hgS).trans hgA, ← runT_congrA K ΔE ρ ρE φ true _ _ sA hagree] at hx₁
      have hmap := matchIndReaccessE (K := K) (ρ := ρ) (φ := φ) (tl := true) (hint := hintM K ρ st.goal) (ty := ty)
        (arms := arms) hTok htag
      rw [hx₁] at hmap
      obtain ⟨⟨r'', s''⟩, hx', hr'⟩ := Option.map_eq_some_iff.mp hmap.symm
      simp only at hr'
      subst hr'
      exact ⟨stl, v', T, hkr, ⟨ρ₁, Δ₁, π₁, r'', s'', he.trans he₁, hx', hm₁, ha₁, hp₁,
        hg₁.trans ((hgE.trans hgS).trans hgA)⟩, hK'.trans hK₁⟩
    · have hcA : cT < arms.length := by rw [hlenA]; exact hcTlt
      have hget : arms[cT]? = some (arms[cT].1, arms[cT].2) := by rw [List.getElem?_eq_getElem hcA]
      obtain ⟨hva, haba, hnha⟩ := harm_ok cT _ _ hget
      obtain ⟨stB, stW, stJ, st₁, r, kc, bw, bj, b₁, hbase, href, hDW, hjc, harm, hD₁⟩ :=
        hworlds cT _ _ hcTlt hget
      obtain ⟨ρW, ΔW, heW, hKW, htnW, htdW, hgW, hpW, hrW⟩ :=
        hW { K with Δ := ΔS } ρS φ πA stS stB stW s sA p d ps r σ cT m bw tg (ih.lower (by omega) ΔS) hneS hpS hrS
          hSA htag hσS hcT hbase hDW href
      have hKW' : Kept st stW := ((hKA.trans hKS).trans hKW)
      obtain ⟨rfl, hkJ, hmJ, htnJ, htdJ⟩ := hjk stW stJ kc bj hKW' hDW hjc
      exact indArm_leafE hPJ hPA hVC ih (by omega) hfl2 hget hTok htag hcT hnp hsc hm hne hk hkt hSA hva haba hnha
        (Ext.of_kern_right ((heA.trans heS).trans heW) hkJ) (hKW'.trans (Kept.of_kern hkJ hmJ))
        (htnJ.trans (((htnW.trans htnS).trans htnA).trans htn)) (htdJ.trans (((htdW.trans htdS).trans htdA).trans htd))
        (by rw [← hkJ.goal]; exact (hgW.trans hgS).trans hgA) hrt (hpW.of_kern hkJ) (hrW.of_kern hkJ) hD₁ harm
  · obtain ⟨ρG, ΔG, heG, hKG, htnG, htdG, hgG, hpG, hrG⟩ :=
      hG { K with Δ := ΔA } ρA φ πA stA stG sA p v σ m bg (ih.lower (by omega) ΔA) hneA hpA hrA hSA hcv hvs hDG hgen
    have he : Ext K ρ π st stG ρG ΔG πA := heA.trans heG
    have hagree : ∀ σ', (Term.matchInd p ty arms).anyAtom (· == .abs σ') = true → AgreeA K ΔG ρ ρG σ' :=
      fun σ' hσ' => by obtain ⟨a', d'⟩ := he.agree σ' (hab σ' hσ'); exact ⟨a'.symm, d'.symm⟩
    have hO := (ih m (by omega) ΔG ρG).2 (.matchInd p ty arms) stG k sA πA b₁ st₁
      (hm.of_modeEq (hKA.trans hKG).mode) ((htnG.trans htnA).trans htn) (by rw [(hKA.trans hKG).size]; exact hne)
      ((htdG.trans htdA).trans htd) hk hkt hpG (hrt.move (hKA.trans hKG).stack he.abs fun σ hσ => (he.agree σ hσ).1)
      hrG hSA (hVC K ΔG ρ ρG φ _ hagree hv) (absBelow_mono hab he.abs) hnh hD₁ hre
    obtain ⟨stl, v', T, hkr, ⟨ρ₁, Δ₁, π₁, r, s₁, he₁, hx₁, hm₁, ha₁, hp₁, hg₁⟩, hK₁⟩ := hO.2
    rw [hgG.trans hgA, ← runT_congrA K ΔG ρ ρG φ true _ _ sA hagree] at hx₁
    have hmap := matchIndReaccessE (K := K) (ρ := ρ) (φ := φ) (tl := true) (hint := hintM K ρ st.goal) (ty := ty)
      (arms := arms) hTok htag
    rw [hx₁] at hmap
    obtain ⟨⟨r', s'⟩, hx', hr'⟩ := Option.map_eq_some_iff.mp hmap.symm
    simp only at hr'
    subst hr'
    exact ⟨stl, v', T, hkr, ⟨ρ₁, Δ₁, π₁, r', s', he.trans he₁, hx', hm₁, ha₁, hp₁, hg₁.trans (hgG.trans hgA)⟩,
      (hKA.trans hKG).trans hK₁⟩
end

/-! ## The step, assembled -/

/-- **`TStepMatchInd` in general** (since main's D146 the arms' covering of the constructors is the run's, lead49; the paper's [Tail-split],
[Tail-gen], [Tail-match] at a data type, [Tail-prop]; docs/18's principle "worlds are exclusive" and case 4): the match on
a proof by `ProofMatchTailG`; otherwise the full form where the table does not read the match as a proof
(`tStepMatchInd_data`) and the erased form where it does (`tStepMatchInd_proofRead`); a scrutinee with a positional
projection by `TailProjIndG` (NEW at main's D145). ASSUMES 13 facts:
`TailMatchIndInv`, `JoinContInv` (checker); `MatchIndFlagsT`, `ProofJoinIndG` (table); `MatchIndTagG`, `ScrutTypeG`,
`WorldRefineIndG`, `EtaTailG`, `JoinContG`, `GenTailG`, `ProofMatchTailG`, `TailProjIndG` (mixed); `ProofArmIndM` (model at the
instance); and `Strict.FundCtx K`. Model facts used and proved: `ValsCongrA`, the match again after its tag
(`matchIndReaccessM`, `matchIndReaccessE`). -/
theorem tStepMatchInd_of {K : RunCtx} {φ : Future} (hInv : TailMatchIndInv) (hJI : JoinContInv)
    (hMF : MatchIndFlagsT K.D) (hPJ : ProofJoinIndG K.D) (hTag : MatchIndTagG) (hST : ScrutTypeG)
    (hW : WorldRefineIndG) (hE : EtaTailG) (hJ : JoinContG) (hG : GenTailG) (hPA : ProofArmIndM K)
    (hPM : ProofMatchTailG K φ) (hPj : TailProjIndG K φ) (hc : Strict.FundCtx K) : TStepMatchInd K φ := by
  intro n ih Δ ρ p ty arms
  refine (Classical.em p.Direct).elim (fun hdir => ?_) (fun hdir => hPj n ih Δ ρ p ty arms hdir)
  intro st k s π bh st' hm htn hne htd hk hkt hp hrt hr hS hv hab hnh hD hrun
  have ih' : IH { K with Δ := Δ } φ n := ih
  have hc' : Strict.FundCtx { K with Δ := Δ } := ⟨hc.globals, hc.sorts⟩
  by_cases hb : ∃ b, Runs (Ochr.byTypeMatch ty arms) st b true st
  · obtain ⟨b, hb⟩ := hb
    exact hPM n ih Δ ρ p ty arms st k s π bh st' b hb hm htn hne htd hk hkt hp hrt hr hS hv hab hnh hD hrun
  · refine ⟨fun h2 => tStepMatchInd_data (K := { K with Δ := Δ }) hInv hJI hMF hTag hST hW hE hJ hG valsCongrA hc' ih'
      ρ p ty arms st k s π bh st' hm htn hne htd hk hkt hp hrt hr hS hv hab hnh hD hrun hb hdir h2, ?_⟩
    cases h2 : ({ K with Δ := Δ } : RunCtx).D.flags (scopeOf s) (.matchInd p ty arms) |>.2
    · exact (tStepMatchInd_data (K := { K with Δ := Δ }) hInv hJI hMF hTag hST hW hE hJ hG valsCongrA hc' ih'
        ρ p ty arms st k s π bh st' hm htn hne htd hk hkt hp hrt hr hS hv hab hnh hD hrun hb hdir h2).toE
    · exact tStepMatchInd_proofRead (K := { K with Δ := Δ }) hInv hJI hPJ hTag hST hW hE hG hPA valsCongrA ih'
        ρ p ty arms st k s π bh st' hm htn hne htd hk hkt hp hrt hr hS hv hab hnh hD hrun hb hdir h2

namespace MatchIndGuards

open Ochr.Meaning.Regress.GenNeutralContent (isOk outSt outVal)

def bodyOf (name : String) : Term :=
  match MatchIndRd.decls.find? (·.name == name) with
  | some d => match Ochr.Surface.runResolve MatchIndRd.decls d 100000 with
    | (.ok (.ok (.defn df)), _) => df.body
    | _ => .zero
  | none => .zero

def entryOf (nm : String) (np : Nat) : Option MState :=
  let r := Ochr.Test.runWith (some Prelude) "MatchIndRd" MatchIndRd { recordStates := true } (located := true)
  match r.rows.find? (·.name == nm) with
  | some row => (row.trace.toList.filterMap fun e => match e with
      | .state _ _ _ st => if st.env.size == 2 && st.env[1]!.binds.size == np + 1 then some st else none
      | _ => none).head?
  | none => none

/-- Succeeds where the value, if an unknown, has the type `Nat`. -/
def kAbsNat : Value → Value → M Unit := fun v _ => do
  match v with
  | .abs i => if (← get).absTy[i]? == some .tNat then pure () else err "k"
  | _ => pure ()

/-- Succeeds where the value is not an unknown. -/
def kNoAbs : Value → Value → M Unit := fun v _ => if v matches .abs _ then err "k" else pure ()

#guard ((Ochr.Test.runWith (some Prelude) "MatchIndRd" MatchIndRd {} (located := false)).allAsExpected)
-- `O1`: world `Some` refines `σ := Some(σ')` with `σ' : Nat`, the parameter substituted into the field's type `A`
#guard (bodyOf "O1").pp [] == "match #1 { None => #0, Some => #1.x }"
#guard (entryOf "O1" 2).any fun st => isOk (Ochr.checkTail 1000 (bodyOf "O1") kAbsNat) st 100000
#guard (entryOf "O1" 2).any fun st => !isOk (Ochr.checkTail 1000 (bodyOf "O1") kNoAbs) st 100000
-- `D1`: `d` is refined in place (`σx : Payload(σb)`), then the inner split's world `false` refines `x`'s type to `Nat`
#guard (entryOf "D1" 1).any fun st => isOk (Ochr.checkTail 1000 (bodyOf "D1") kAbsNat) st 100000
#guard (entryOf "D1" 1).any fun st => !isOk (Ochr.checkTail 1000 (bodyOf "D1") kNoAbs) st 100000
-- `U1`: one constructor: an η record, the field moved by the arm
#guard (entryOf "U1" 1).any fun st => isOk (Ochr.checkTail 1000 (bodyOf "U1") (fun _ _ => do
  let st ← get
  if st.etaRefs.length == 1 && st.env[st.env.size - 1]!.binds[1]!.val matches .ind _ _ _ _ [.bot] then pure () else err "k"))
  st 100000
-- `P1`: a match on a proof is read by its type (`ProofMatchTailG`'s branch)
#guard (bodyOf "P1").pp [] == "match #0 { Wit => refl }"
#guard (entryOf "P1" 1).any fun st => outVal (Ochr.byTypeMatch "Ex" [(⟨"w"⟩, .tt)]) st 1000

end MatchIndGuards

end Ochr.Meaning.Steps.Form.Master
