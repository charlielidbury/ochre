import Ochr.Meaning.Strict.WitnessHint
import Ochr.Meaning.Closure

/-!
# The `.fix` clause reduced to its body's run (toward the closure-form witnesses, item 4)

Every strict test should have an accepted program, in CLOSURE form, that passes it (the lead's rule;
`Strict/HANDOFF.md`, Next 1 and 4(c)). A closure-form witness is a strict `.fix` run that succeeds and
returns a member of its type. These two lemmas reduce such a witness, for a non-recursive closure with
no borrow parameter, to its BODY's run at every member argument, in the frame `bodyWith` builds (`()` at `Unit`
in the own-name slot since R-dec, docs/31 D296; then the parameters):

- `run_fix_of_mem`: no erasure, the captures' accesses strict-OK and the closure a member of its type
  ⇒ the `.fix` run returns it (after the captures' moves).
- `fixClo_mem_nonrec`: at a data sort, a data codomain fitting the level, and the body running to a
  good result at every member argument (`fixBodyU`: `()` in the slot, R-dec) ⇒ the closure is a member.

What remains per program (`SetFstOwned`, `SetFst`, `PartMove`): the domains' runs (`runDoms`, a
`.tind` at `Pair(Nat, Nat)`: a data model with `Pair`), and the body's run at a symbolic member
(`Strict/FrameCE.run_body_iff` is its shape for `x.0 := c`).
-/

namespace Ochr.Meaning.Strict.Witness

open Ochr Ochr.Meaning Ochr.Meaning.Strict
open Classical

section
variable {K : RunCtx} {ρ : Assignment} {φ : Future}

/-- The sort the `.fix` clause builds its closure at. -/
noncomputable def fixSort (K : RunCtx) (s : SState) (hs : List Hint) (ds : List Term) (c : Term) : Nat :=
  K.D.piSort (scopeOf s) (.pi hs ds c)

/-- The type the `.fix` clause builds its closure at. -/
noncomputable def fixTy (K : RunCtx) (ρ : Assignment) (φ : Future) (s : SState) (hs : List Hint) (ds : List Term)
    (c : Term) : TyM :=
  piTyAt K.dm.read (fixSort K s hs ds c) (runDoms K ρ φ s ds) (codOf K ρ φ s (bindsOf K ρ φ s ds) (ds.map Term.isRefTy) c)

/-- The closure the `.fix` clause builds. -/
noncomputable def fixClo (K : RunCtx) (ρ : Assignment) (φ : Future) (s : SState) (hs : List Hint) (ds : List Term)
    (c : Term) (dec : Option Nat) (body : Term) : Sem :=
  closureAt K.dm.read (fixSort K s hs ds c) φ (runDoms K ρ φ s ds) (codOf K ρ φ s (bindsOf K ρ φ s ds) (ds.map Term.isRefTy) c)
    (fixG K ρ φ (bindsOf K ρ φ s ds, fixCod K ρ φ s (bindsOf K ρ φ s ds) (ds.map Term.isRefTy) c, K.D.typeDecl (K.D.teleDecls (scopeOf s) ds) c)
      (fixSort K s hs ds c) s (runDoms K ρ φ s ds) (codOf K ρ φ s (bindsOf K ρ φ s ds) (ds.map Term.isRefTy) c)
      (fixTy K ρ φ s hs ds c) s.nextLoan dec body)

/-- **The `.fix` clause runs where its closure is a member.** -/
theorem run_fix_of_mem (tl : Bool) (hint : TyS) (self : Hint) (hs : List Hint) (ds : List Term) (c : Term)
    (dec : Option Nat) (body : Term) (s : SState)
    (hfl : K.D.flags (scopeOf s) (.fix self hs ds c dec body) = (false, false))
    (hcap : FoldOk (capStep K) (CapOk K φ) (capOrder (.fix self hs ds c dec body)) s)
    (hmem : fixClo K ρ φ s hs ds c dec body ∈ₛ[K.dm.read] fixTy K ρ φ s hs ds c) :
    runT K ρ φ tl hint (.fix self hs ds c dec body) s =
      some ((fixClo K ρ φ s hs ds c dec body, .plain (fixTy K ρ φ s hs ds c)), fixMoves K (.fix self hs ds c dec body) s) := by
  rw [run_fix_def, hfl]
  simp only [SM.erasedIf, SM.stmtIf, Bool.false_eq_true, if_false]
  rw [if_pos hcap]
  unfold SM.strictS
  dsimp only
  rw [if_pos (by exact hmem)]
  rfl

/-- **A non-recursive closure is a member** when its body runs to a good result at every member
argument, in the frame `bodyWith` builds without `by` (R-dec, docs/31 D296: `()` at `Unit` in the slot, no stage).
At a data sort and a data codomain fitting the level; no borrow parameter (`finals` empty). -/
theorem fixClo_mem_nonrec (fb : List PBind × PBind) (l : Nat) (s : SState) (ps : List PiDom) (out : PiCod)
    (piT : TyM) (start : Nat) (body : Term) (hl : 1 ≤ l ∧ l ≤ 3) (hdata : out.isRef = false)
    (hcod : ∀ args, Steps.DomMembers K.dm.read ps args → LevelFit l (out.cod args))
    (hbody : ∀ args, Steps.DomMembers K.dm.read ps args →
      ∃ o, fixBodyU K ρ φ fb s ps out start body args = some o ∧
        Steps.OutGood K.dm.read ps out args o ∧ o.finals.length = (ps.filter (·.isRef)).length) :
    closureAt K.dm.read l φ ps out (fixG K ρ φ fb l s ps out piT start none body) ∈ₛ[K.dm.read] piTyAt K.dm.read l ps out :=
  closure_mem_of_total' K.dm.read l φ ps out _ hl hdata hcod fun args hm => hbody args hm

end

end Ochr.Meaning.Strict.Witness
