import Dllbc.DeclMacro
import Dllbc.Std
import Dllbc.StdLemmas

/-!
# `decl{ … }` — the crown: quicksort's signature, verified S19-free

THE CROWN is quicksort's telescope (the `hbnd` line) and backward spec — the
ugliness the macro exists to remove. Verifying it against the *imported*
`S19Partition.quicksort` is a CHEAP structural BEq in principle, but the import
forces a from-scratch re-elaboration of S19 — whose own
`example : checkFnOk quicksort := by native_decide` (S19Partition.lean:771) is a
~39-minute audit — because this worktree's pre-seeded `.lake` trace is
hash-rejected by lake (a worktree-cache artifact; `touch`ing mtimes does not
help, lake keys on content hashes). Per the brief's "report rather than eat the
cost repeatedly", this file does NOT import S19.

Instead it proves the macro produces the crown's telescope/retType/back
**identically to the corpus**, by comparing against the corpus's own constructors
transcribed verbatim from S19Partition.lean (the same `Std.LeT`/`Std.addFnT`/
`Std.lenT`/`StdLemmas.sortRangeL` helpers, the same positional `V i "…"` ids).
`expTele`/`expBack` below are *character-for-character* the corpus's expressions,
so these equalities are equivalent to `== S19.quicksort.{telescope,back}` — minus
the 39-minute import. The body-splice half of the crown (that `= %corpusBody`
round-trips a real proof-laden Decl) is proven by `nthS` in SDeclMacro.lean.

The full `decl{ … } == S19Partition.quicksort` assertion — cheap in any checkout
whose S19 cache lake accepts (e.g. the team-lead's main checkout, where S19 is
already built) — is recorded, ready to run, in the comment block at the end.
-/

open Dllbc
open Dllbc.StdLemmas (sortRangeL)

namespace Dllbc.Tests.SDeclMacroCrown

-- The corpus's own helpers (transcribed from S19Partition.lean), so the expected
-- Terms are the corpus's exact constructions.
def V (i : Nat) (n : String) : Term := .var ⟨i, n⟩
def natT : Term := .const "Nat"
def listNatT : Term := .app (.const "List") (.const "Nat")
def dv : Term := .deref (V 0 "v")
def LeT (a b : Term) : Term := Std.LeT a b
def lenT (l : Term) : Term := Std.lenT l
def addTmH (a b : Term) : Term := .app (.app Std.addFnT a) b
def sortRangeLT2 (fuel lo cnt l : Term) : Term :=
  .app (.app (.app (.app StdLemmas.sortRangeL fuel) lo) cnt) l

-- The surface quicksort. Body is a placeholder `()`; the real `= %corpusBody`
-- splice is round-trip-proven by nthS (SDeclMacro.lean). Everything ELSE — the
-- header, the `hbnd` telescope, and the backward spec — is the crown surface.
def quicksortSig : Decl :=
  decl{ fn quicksort (v : &mut List Nat, fuel : Nat, lo : Nat, cnt : Nat,
                      hbnd : Le (add lo cnt) (len *v)) -> Unit
        back = sortRangeL fuel lo cnt (*v)
        { () } }

-- The corpus's exact telescope and back (S19Partition.lean:710-711, 763).
def expTele : List (String × Term) :=
  [("v", .borrowT listNatT listNatT), ("fuel", natT), ("lo", natT), ("cnt", natT),
   ("hbnd", LeT (addTmH (V 2 "lo") (V 3 "cnt")) (lenT dv))]
def expBack : Term := sortRangeLT2 (V 1 "fuel") (V 2 "lo") (V 3 "cnt") dv

-- The crown, proven: the surface produces the corpus's telescope, retType, back.
example : (quicksortSig.telescope == expTele) = true := by native_decide
example : (quicksortSig.retType == Term.const "Unit") = true := by native_decide
example : (quicksortSig.back == some expBack) = true := by native_decide

/-
The full round-trip, ready to run wherever S19's cache is accepted (drop these
lines into a file that imports `Dllbc.Tests.S19Partition` and, for `BEq Decl`,
`Dllbc.Tests.SDeclMacro`):

  def quicksort' : Decl :=
    decl{ fn quicksort (v : &mut List Nat, fuel : Nat, lo : Nat, cnt : Nat,
                        hbnd : Le (add lo cnt) (len *v)) -> Unit
          back = sortRangeL fuel lo cnt (*v)
          = %(Dllbc.Tests.S19Partition.quicksort.body) }
  example : (quicksort' == Dllbc.Tests.S19Partition.quicksort) = true := by native_decide
-/

end Dllbc.Tests.SDeclMacroCrown
