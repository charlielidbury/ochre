import Ochr.Meaning.Steps.Borrow

/-!
# The aligned decisions equal the checker's (milestone 3; docs/18 "Decisions, by kind",
*aligned*)

`Decisions` (`Places.lean`) is what the reference run reads from syntax. "Aligned" is discharged
by showing each field equals the checker's `Decide` function, run from a state holding the same
declarations: whether a term is a statement and a proof (`preFlags`), a place's and a term's
declared-type reading (`placeDecl`, `declOf`), copy-ness (`declCopy`), a Π-term's sort
(`sortOf`/`piSort`), and D84's join set (`jdMoves`, on branch `d84`; stated here against the
field only, to be tied to `Decide.jdMoves` when it lands). The instance itself,
`Decisions` built from `Decide.lean`, is `DecisionsInst.lean` (implementer prog-decisions);
these statements are about that instance.
-/

namespace Ochr.Meaning.Steps

open Ochr.Meaning

section
variable (K : RunCtx) (ρ : Assignment)

/-- The scope of readings the checker uses at `st`'s top frame is `scopeOf` of its semantic
state (each binding's `decl`, innermost first). -/
theorem scopeOf_sstate (st : MState) :
    scopeOf (SM' K ρ st) = ((st.env.back?.map (·.binds.toList.map (·.decl))).getD []).reverse := by
  sorry

/-- `Decisions.flags` is `Decide.preFlags` where the latter answers. -/
theorem flags_aligned (st st' : MState) (t : Term) (d : DeclInfo) (fl : Bool × Bool)
    (hg : Good K.dm K.C K.Γ ρ st)
    (h : Runs (Ochr.preFlags t d) st 2000000 (some fl) st') :
    K.D.flags (scopeOf (SM' K ρ st)) t = fl := by
  sorry

/-- `Decisions.placeDecl` is `Decide.placeDecl`. -/
theorem placeDecl_aligned (st st' : MState) (fuel : Nat) (p : Place) (d : DeclInfo)
    (hg : Good K.dm K.C K.Γ ρ st)
    (h : Runs (Ochr.placeDecl fuel (scopeOf (SM' K ρ st)) p) st fuel d st') :
    K.D.placeDecl (scopeOf (SM' K ρ st)) p = d := by
  sorry

/-- `Decisions.declOf` is `Decide.declOf` (unchecked mode). -/
theorem declOf_aligned (st st' : MState) (fuel : Nat) (t : Term) (d : DeclInfo)
    (hg : Good K.dm K.C K.Γ ρ st)
    (h : Runs (Ochr.declOf fuel false (scopeOf (SM' K ρ st)) [] t) st fuel d st') :
    K.D.declOf (scopeOf (SM' K ρ st)) t = d := by
  sorry

/-- `Decisions.copy` is `Decide.declCopy`. -/
theorem copy_aligned (st st' : MState) (fuel : Nat) (d : DeclInfo) (b : Bool)
    (hg : Good K.dm K.C K.Γ ρ st)
    (h : Runs (Ochr.declCopy fuel d) st fuel b st') :
    K.D.copy d = b := by
  sorry

/-- `Decisions.piSort` is `Decide.sortOf` of the Π-type value (D55: declared sort = computed). -/
theorem piSort_aligned' (st st' : MState) (fuel : Nat) (caps : List Value) (hs : List Hint)
    (ds : List Term) (c : Term) (rd : List (DeclInfo × Value)) (l : Nat)
    (hg : Good K.dm K.C K.Γ ρ st)
    (h : Runs (Ochr.sortOf fuel (.tPi caps (.pi hs ds c) rd)) st fuel l st') :
    K.D.piSort (scopeOf (SM' K ρ st)) (.pi hs ds c) = l := by
  sorry

/-- D84's join set is static: a function of the match term and the scope only. (To be stated
against `Decide.jdMoves` when branch `d84` lands.) -/
theorem joinMoves_static (sc : List DeclInfo) (t : Term) :
    ∀ sc', sc' = sc → K.D.joinMoves sc' t = K.D.joinMoves sc t := by
  intro sc' h; rw [h]

end

end Ochr.Meaning.Steps
