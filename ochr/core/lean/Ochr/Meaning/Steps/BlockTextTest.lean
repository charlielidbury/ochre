import Ochr.Meaning.Steps.BlockTextNTr

/-!
# The test of the design, faults (b), (c), (d) (spine-exp-block, lead38; docs/31 D236)

EXPERIMENTAL (`spine-exp-block`, the checker of `exp-block-text`). Fault (a) is `BlockTextNTr.mean_vNTr`. Here:

**(b) `MB0r` under the stage contexts** (docs/31 D232). On main the block of `MB0 (m n : Nat) : Nat by n` took the
function's own binding as a parameter at its DECLARED type and was applied to the global; under the knot's context `K_b`
the global means its stage closure at the WEAKENED type, which is no member of the declared type (`StageBlockCE`), so
the leaf meant `err`. On the experiment the text is pinned exactly (`textMB0_pinned`): its cells hold `σ0`, `σ1` (no
function), and the global occurs ONLY as the head of the call `MB0(m.0, n.0)` (`.call (.val (.gfn "MB0")) …`). The
model's `.block` clause never forms a closure and never asks a membership of the global: at the head of the call the
`.val` clause reads the global's meaning, `K.C.global "MB0"`, the stage closure itself, and `callOf` applies it along
its own (weakened) type at the call's arguments. At `n = 0` (every assignment the knot's first step reaches) the text
never reaches the call; at `n = 1` it calls the stage closure at `(m - 1, 0)`, of rank `0`, below every bound `b ≥ 1`
that reaches it, where the weakened type is the true one (`FixEqDesc.stage_agree`'s regime). By reading; the run up to
the call is `mean_vNTr`'s clause by clause.

**(c) The re-run of a sealed block** (`SealRerunG`; docs/31 D233). On main the checker's re-run bound the block's own
closure as `self` (`runBodyCore`), whose meaning is `err`, so no good reference state was related to it. On the
experiment the re-run (`runBlock`) binds only the cells, each at its recorded type and reading, and the model's clause
binds the same cells at the same types and readings (`capsTys rd`); its states are good wherever `CellsOk` holds
(`Strict.bindCells_fund`, proved). Pinned here: the checker's re-run of `NT`'s text after each refinement of `σ1`
computes the number `mean_vNTr` gives (`S(σ2)` at `σ1 := Z`, `σ2` at `σ1 := S(σ3)`).

**(d) The substitution lemmas** (docs/31 D234's fourth place). `runT_substSame`, `runT_substAbsSame` take the `.block`
case by congruence alone (`RunSubst`, `RunSubstAbs`: ten lines each, no closure application equality, no lemma about a
block's own slot): a value substitution cannot make a `.block` term, and a block is read by its text, not by a
closure's code.
-/

namespace Ochr.Meaning.Steps.Form.BlockTextTest

open Ochr Ochr.Meaning Ochr.Meaning.Steps Ochr.Meaning.Steps.Form
open Ochr.Meaning.Regress.GenNeutralContent (isOk outVal)

/-! ## (b) `MB0`'s text names the function only as the head of a call -/

/-- `MB0`'s block's TEXT, as the experimental checker makes it: cells `m ↦ σ0`, `n ↦ σ1`; the match on `m`, then on `n`,
then the call of the GLOBAL `MB0` at the predecessors. -/
def textMB0 : Term :=
  .block [(⟨"m"⟩, .val (.abs 0)), (⟨"n"⟩, .val (.abs 1))] [(.other, .tNat), (.other, .tNat)] [false, false] .tNat
    (.matchNat (.var 1) .zero (.matchNat (.var 0) .zero
      (.call (.val (.gfn "MB0")) [.place (.proj 0 (.var 1)), .place (.proj 0 (.var 0))] false)))

/-- **Pinned**: the checker's value of `MB0`'s leaf `r` is `textMB0`. -/
def textMB0_pinned : Bool :=
  (RecDescAtk.holes "MB0").map (fun Ω => (Ω.reverse.find? (·.1 == "r")).map (·.2.2) == some (.sealed textMB0)) == [true]

#guard textMB0_pinned

/-! ## (c) The checker's re-run of a sealed block computes what the text means -/

/-- `NT`'s text with `σ1` refined to `t`. -/
def textNTrAt (w : Value) : Term :=
  .block [(⟨"n"⟩, .val (.succ (.abs 2))), (⟨"m"⟩, .val w)] [(.other, .tNat), (.other, .tNat)] [false, false] .tNat
    BlockTextNTr.mNTr

/-- A state holding four unknowns of type `Nat`. -/
def st4 : MState := { nextAbs := 4, absTy := #[.tNat, .tNat, .tNat, .tNat], absDecl := #[.other, .other, .other, .other] }

-- the re-run (`nfSealed`: an untyped run from one empty frame) at `σ1 := Z` gives `S(σ2)`, at `σ1 := S(σ3)` gives `σ2`;
-- with `σ1` unknown the match is stuck and the text stays sealed
#guard isOk (Ochr.nfSealed 1000 (textNTrAt .zero)) st4 100000
#guard (outVal (Ochr.nfSealed 1000 (textNTrAt .zero)) st4 100000) == .succ (.abs 2)
#guard (outVal (Ochr.nfSealed 1000 (textNTrAt (.succ (.abs 3)))) st4 100000) == .abs 2
#guard (outVal (Ochr.nfSealed 1000 (textNTrAt (.abs 1))) st4 100000) == .sealed BlockTextNTr.textNTr

end Ochr.Meaning.Steps.Form.BlockTextTest
