import Ochr.Meaning.Regress.GenNeutralContent
import Ochr.Meaning.Steps.MovedPlace

/-!
# Step kinds against parent kinds: the checker's walk and the reference's drop agree at the grain

Every kind of step (`*`, a named field `.g`, a positional field `.i`, a number's predecessor `.0`)
against every kind of value its parent can hold, at the join's grain as restated with the checker's
D101 (a `*` step is through a place declared a borrow, `Steps.StepOk`; the checker's `jdGrain`
rejects a move through any other `*`). Each cell: the checker (`stepV`, then `movedPlace` and
`dropAtJoin`: drop, re-root and do nothing, access and retry, η or generalise and retry, reject) and
the reference (its lent-prefix access `accessLentPrefix`, then `Run.dropAt`: `Sem.updAt` of `moved`
along the path, nothing where it fails), and the clause that makes them agree. Kernel-checked below
where it computes: `stepV` for every cell (`ck_*`), `Sem.step` and the drop's write for every meaning
form (`md_*`, `wr_*`), `movedPlace` on concrete states where the place does not exist (`mp_*`), and
the reference's lent prefix at DP4's cell (`lp_dp4`). A rejection is no run ("vacuous").

| step | parent holds | checker | reference: lent prefix, then write | agree by |
|---|---|---|---|---|
| `*` | a borrow (a holder) | the place exists: access, drop | prefix access absorbed, write | `lentPrefix_absorbed_eq` |
| `*` | `⊥` (the borrow moved) | re-root to the holder, nothing | no prefix site; `moved` over `moved` | (WF14), `updAt_bot_self` |
| `*` | `⋆` | — | — | excluded: the parent is declared a borrow, no copy, so (C⋆) |
| `*` | anything else | reject (no borrow), or D101 at the grain | — | vacuous |
| `.g` | constructor of `g`'s | exists: access, drop | prefix access absorbed, write | grain, `followMean`, `lentPrefix_absorbed_eq` |
| `.g` | `⊥` | re-root, nothing | no prefix site ((WF14)); the write fails through `moved` | (WF14), `Slice.updAt_moved_none` |
| `.g` | `⋆` | exists, holds `⋆` | — | excluded: a copy ((C⋆)), the join drops none |
| `.g` | unknown / sealed, one constructor | η / generalise, retry | after the refinement as the row above | `refine_step`, `generalizeNeutral_step` |
| `.g` | a hole or a fill (`loan`, sealed over one) | access the parent, retry | the same prefix accessed | `fillPrefix_eq` |
| `.g` | other constructor, a borrow, a number, a closure; unknown or sealed of several | reject (D94) | — | vacuous |
| `.i` | constructor 0 | as `.g` | as `.g` | as `.g` |
| `.0` | `S(n)` | exists: drop | write (the predecessor) | `NatAlong` |
| `.0` | `Z` | reject | — | vacuous |
| any | under a mark (`lent_l v`) | walks through it, as `v` | the mark is a site: absorbed where the place exists; no mark above a `⊥` ((WF14)); none above a `⋆` reached by a non-copy place (the `*` row) | as `v`'s row |

The grain as it stood (a `*` step needed nothing) left one row unexcluded, `*` on `⋆`: there the
reference wrote `moved` through the `*` (DP1, `wr_deref_proof`) and its lent-prefix access ended a
borrow whose mark sat above the `⋆` (DP4, `mp_dp4_markKept`, `lp_dp4`), where the checker did
nothing; only an arm the run never takes could put a `*` on a non-borrow there.
`Regress/GrainDerefProof.lean` records the leaf `grain_deref_not_proof` false at that grain; at the
restated grain it is proved from (C⋆).
-/

namespace Ochr.Meaning.Regress.StepKindsTable
open Ochr Ochr.Meaning Ochr.Meaning.Steps

/-! ## The checker's `stepV`, every cell -/

def h0 : Hint := ⟨"T"⟩
def g : FieldRef := ⟨"T", 0, 0, "a"⟩
/-- A constructor value of `g`'s constructor, of another constructor, of another declaration. -/
def cT : Value := .ind "T" 0 h0 [] [.zero, .proof]
def cT1 : Value := .ind "T" 1 h0 [] [.zero]
def cU : Value := .ind "U" 0 h0 [] [.zero]
def sl : Value := .sealed (.val .zero)
def cl : Value := .clo [] (.val .zero) []

-- `*`
theorem ck_deref_borrow : stepV .deref (.borrow 0 .zero) = some .zero := rfl
theorem ck_deref_proof : stepV .deref .proof = none := rfl
theorem ck_deref_bot : stepV .deref .bot = none := rfl
theorem ck_deref_ctor : stepV .deref cT = none := rfl
theorem ck_deref_num : stepV .deref (.succ .zero) = none := rfl
theorem ck_deref_abs : stepV .deref (.abs 0) = none := rfl
theorem ck_deref_sealed : stepV .deref sl = none := rfl
theorem ck_deref_loan : stepV .deref (.loan 0) = none := rfl
theorem ck_deref_clo : stepV .deref cl = none := rfl
theorem ck_deref_mark : stepV .deref (.gloan 0 .proof) = stepV .deref .proof := rfl
-- `.g`
theorem ck_field_ctor : stepV (.field g) cT = some .zero := rfl
theorem ck_field_otherCtor : stepV (.field g) cT1 = none := rfl
theorem ck_field_otherDecl : stepV (.field g) cU = none := rfl
theorem ck_field_proof : stepV (.field g) .proof = some .proof := rfl
theorem ck_field_bot : stepV (.field g) .bot = none := rfl
theorem ck_field_borrow : stepV (.field g) (.borrow 0 cT) = none := rfl
theorem ck_field_num : stepV (.field g) (.succ .zero) = none := rfl
theorem ck_field_abs : stepV (.field g) (.abs 0) = none := rfl
theorem ck_field_sealed : stepV (.field g) sl = none := rfl
theorem ck_field_loan : stepV (.field g) (.loan 0) = none := rfl
theorem ck_field_clo : stepV (.field g) cl = none := rfl
theorem ck_field_mark : stepV (.field g) (.gloan 0 cT) = some .zero := rfl
-- `.i` and `.0`
theorem ck_proj_ctor0 : stepV (.proj 1) cT = some .proof := rfl
theorem ck_proj_ctor1 : stepV (.proj 0) cT1 = none := rfl
theorem ck_proj_succ : stepV (.proj 0) (.succ .zero) = some .zero := rfl
theorem ck_proj_zero : stepV (.proj 0) .zero = none := rfl
theorem ck_proj_proof : stepV (.proj 3) .proof = some .proof := rfl
theorem ck_proj_bot : stepV (.proj 0) .bot = none := rfl
theorem ck_proj_borrow : stepV (.proj 0) (.borrow 0 cT) = none := rfl
theorem ck_proj_abs : stepV (.proj 0) (.abs 0) = none := rfl
theorem ck_proj_loan : stepV (.proj 0) (.loan 0) = none := rfl

/-! ## The reference: `Sem.step` and the drop's write, every meaning form -/

section
variable (dm : DataModel) (Γ : List IndDecl) (T : TyS)

/-- `*` is the identity on every meaning (a holder means its content). -/
theorem md_deref (s : Sem) : Sem.step dm Γ T .deref s = some (s, T) := rfl
theorem md_field_proof : (Sem.step dm Γ T (.field g) .proof).map Prod.fst = some .proof := rfl
theorem md_field_moved : Sem.step dm Γ T (.field g) .moved = none := rfl
/-- At a type of `T`'s declaration where the field's read type is defined (route (c): a read is typed
by the type it starts at). -/
theorem md_field_dat (r r₀ : Rec) (a b : Sem) (d : IndDecl) (hT : T.m.dataCode? = some (d, r₀))
    (hd : d.name = "T") (hU : (dm.readTy d r 0 0 [] a).isSome) :
    (Sem.step dm Γ T (.field g) (.dat "T" r 0 [a, b])).map Prod.fst = some a := by
  obtain ⟨U, hU⟩ := Option.isSome_iff_exists.mp hU
  simp [Sem.step, Sem.stepField, g, hT, hd, hU]
theorem md_field_otherCtor (r : Rec) (a : Sem) : Sem.step dm Γ T (.field g) (.dat "T" r 1 [a]) = none := by
  simp only [Sem.step, Sem.stepField, g]
  split
  · split
    · exact if_neg (fun h => absurd h.2 (by decide))
    · rfl
  · rfl
theorem md_field_otherDecl (r : Rec) (a : Sem) : Sem.step dm Γ T (.field g) (.dat "U" r 0 [a]) = none := by
  simp [Sem.step, g]
theorem md_pred_succ : (Sem.step dm Γ T (.proj 0) (.el0 Nat 1)).map Prod.fst = some (.el0 Nat 0) := by
  simp [Sem.step, Sem.asNat, Sem.as]
theorem md_pred_zero : Sem.step dm Γ T (.proj 0) (.el0 Nat 0) = none := by
  simp [Sem.step, Sem.asNat, Sem.as]
theorem md_proj_moved : Sem.step dm Γ T (.proj 0) .moved = none := by
  simp only [Sem.step, show Sem.moved.asNat = none from rfl]
  split
  · rename_i heq; cases heq
  · rfl
theorem md_proj_proof : (Sem.step dm Γ T (.proj 2) .proof).map Prod.fst = some .proof := rfl

/-- The drop's write through `*` at `proof` is made (DP1's cell): `*` is the identity. -/
theorem wr_deref_proof : Sem.updAt dm Γ T (fun _ => .moved) [.deref] .proof = some .moved := rfl
/-- ... and at `moved`, `moved` over `moved`. -/
theorem wr_deref_moved : Sem.updAt dm Γ T (fun _ => .moved) [.deref] .moved = some .moved := rfl
/-- A field step through `moved` or `proof` cannot be written: nothing. -/
theorem wr_field_moved : Sem.updAt dm Γ T (fun _ => .moved) [.field g] .moved = none := rfl
theorem wr_field_proof : Sem.updAt dm Γ T (fun _ => .moved) [.field g] .proof = none := rfl
theorem wr_proj_moved : Sem.updAt dm Γ T (fun _ => .moved) [.proj 0] .moved = none := rfl

end

/-! ## The checker's `movedPlace` where the place does not exist -/

open Ochr.Meaning.Regress.GenNeutralContent (outVal outSt isOk)

def bnd (n : String) (v : Value) : Binding := { hint := ⟨n⟩, ty := none, val := v }
def st1 (vs : Array Binding) : MState := { env := #[{ binds := vs }] }

/-- `*h` with `h` holding `⋆` (DP1): re-rooted to `h`, nothing done. -/
theorem mp_derefProof :
    isOk (Ochr.movedPlace 10 (.deref (.var 0))) (st1 #[bnd "h" .proof]) 100 = true ∧
    (outVal (Ochr.movedPlace 10 (.deref (.var 0))) (st1 #[bnd "h" .proof]) 100).beq (.var 0) = true := by
  decide +kernel

/-- `*x` with `x` holding `⊥`: re-rooted to `x`. -/
theorem mp_derefBot :
    isOk (Ochr.movedPlace 10 (.deref (.var 0))) (st1 #[bnd "x" .bot]) 100 = true ∧
    (outVal (Ochr.movedPlace 10 (.deref (.var 0))) (st1 #[bnd "x" .bot]) 100).beq (.var 0) = true := by
  decide +kernel

/-- `x.g` with `x` holding `⊥`: re-rooted to `x`. -/
theorem mp_fieldBot :
    isOk (Ochr.movedPlace 10 (.field g (.var 0))) (st1 #[bnd "x" .bot]) 100 = true ∧
    (outVal (Ochr.movedPlace 10 (.field g (.var 0))) (st1 #[bnd "x" .bot]) 100).beq (.var 0) = true := by
  decide +kernel

/-- `*x` with `x` holding a number, and `x.g` with `x` of another constructor: rejected (D94). -/
theorem mp_derefNum : isOk (Ochr.movedPlace 10 (.deref (.var 0))) (st1 #[bnd "x" (.succ .zero)]) 100 = false := by
  decide +kernel
theorem mp_fieldOther : isOk (Ochr.movedPlace 10 (.field g (.var 0))) (st1 #[bnd "x" cT1]) 100 = false := by
  decide +kernel

/-- DP4's cell: `x ↦ lent_1 T(0, ⋆)` (a mark of the live borrow `1`, which `r` holds), and the place
`*(x.1)`. The checker reaches `x.1` through the mark, re-roots there (`⋆`) and does nothing: `x`
keeps its mark, label 1 stays live. -/
def g1 : FieldRef := ⟨"T", 0, 1, "h"⟩
def S4 : MState := st1 #[bnd "x" (.gloan 1 cT), bnd "r" (.borrow 1 .zero)]
theorem mp_dp4_markKept :
    isOk (Ochr.movedPlace 10 (.deref (.field g1 (.var 1)))) S4 100 = true ∧
    (outVal (Ochr.movedPlace 10 (.deref (.field g1 (.var 1)))) S4 100).beq (.field g1 (.var 1)) = true ∧
    (match ((outSt (Ochr.movedPlace 10 (.deref (.field g1 (.var 1)))) S4 100).env[0]!.binds[0]!).val with
      | .gloan 1 _ => true | _ => false) = true := by
  decide +kernel

/-- The reference at DP4's cell: label 1 (held at `r`, `.bind 0 1`) is lent at `x` whole (the mark,
a fill), so the shortest strict prefix of `x.1.*` with a live site is `x` itself: `accessLentPrefix`
accesses `x` whole (`dataHit` of the empty path reaches the site), which ends label 1, while the
checker keeps it (`mp_dp4_markKept`). -/
noncomputable def R4 : SState :=
  { env := [{ binds := [{ ty := .plain TyM.err, val := fun _ => .err }, { ty := .plain TyM.err, val := fun _ => .err }] }],
    shape := fun p => if p = .bind 0 1 then some 1 else none, nextLoan := 2,
    lent := fun m => if m = 1 then [⟨.bind 0 0, [], true⟩] else [] }
theorem lp_dp4 :
    (match lentPrefix R4 (.bind 0 0) [.field g1, .deref] with | some [] => true | _ => false) = true ∧
    R4.reached (.bind 0 0) (dataHit []) 1 = true := by
  decide +kernel

end Ochr.Meaning.Regress.StepKindsTable
