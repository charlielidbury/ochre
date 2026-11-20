import Ochr.Meaning.Steps.Machine.EnvLeaves

/-!
# `GrowsIn` for the decision procedures (`Decide.lean`)

The functions `Slice.decideKeep` covers keep the state, so they keep the tables. The others of
`Decide.lean`'s block the machine calls (`pushCaps` writes a frame; `freshAbsR`, `absOf`,
`absAt`, `genericValue` make unknowns) and the join's syntactic readers (`jdMoves`, `jdAssigns`)
are walked here, by induction on the fuel where they recur.
-/

namespace Ochr.Meaning.Steps.Machine

open Ochr Ochr.Meaning Ochr.Meaning.Steps Ochr.Meaning.Steps.Slice

variable {G : Tab}

section keep
variable (fuel : Nat)
@[grows] theorem growsIn_placeDecl sc p : GrowsIn G (placeDecl fuel sc p) := growsIn_of_keep ((decideKeep fuel).1 sc p)
@[grows] theorem growsIn_fieldAt r n c i : GrowsIn G (fieldAt fuel r n c i) :=
  growsIn_of_keep ((decideKeep fuel).2.1 r n c i)
@[grows] theorem growsIn_fieldDecl d args c i : GrowsIn G (fieldDecl fuel d args c i) :=
  growsIn_of_keep ((decideKeep fuel).2.2.1 d args c i)
@[grows] theorem growsIn_declCopy r : GrowsIn G (declCopy fuel r) := growsIn_of_keep ((decideKeep fuel).2.2.2.1 r)
@[grows] theorem growsIn_callDecl F as sc ns : GrowsIn G (callDecl fuel F as sc ns) :=
  growsIn_of_keep ((decideKeep fuel).2.2.2.2.1 F as sc ns)
@[grows] theorem growsIn_closedTypeDecl T : GrowsIn G (closedTypeDecl fuel T) :=
  growsIn_of_keep ((decideKeep fuel).2.2.2.2.2.1 T)
@[grows] theorem growsIn_sortOf T : GrowsIn G (sortOf fuel T) := growsIn_of_keep ((decideKeep fuel).2.2.2.2.2.2.1 T)
@[grows] theorem growsIn_declSort sc ns T : GrowsIn G (declSort fuel sc ns T) :=
  growsIn_of_keep ((decideKeep fuel).2.2.2.2.2.2.2.1 sc ns T)
@[grows] theorem growsIn_declOf chk sc ns t : GrowsIn G (declOf fuel chk sc ns t) :=
  growsIn_of_keep ((decideKeep fuel).2.2.2.2.2.2.2.2.1 chk sc ns t)
@[grows] theorem growsIn_typeDecl chk sc ns T vis tsc : GrowsIn G (typeDecl fuel chk sc ns T vis tsc) :=
  growsIn_of_keep ((decideKeep fuel).2.2.2.2.2.2.2.2.2.1 chk sc ns T vis tsc)
@[grows] theorem growsIn_typePos chk sc ns T : GrowsIn G (typePos fuel chk sc ns T) :=
  growsIn_of_keep ((decideKeep fuel).2.2.2.2.2.2.2.2.2.2.2.1 chk sc ns T)
@[grows] theorem growsIn_telescope chk sc ns hs ds : GrowsIn G (telescope fuel chk sc ns hs ds) :=
  growsIn_of_keep ((decideKeep fuel).2.2.2.2.2.2.2.2.2.2.2.2.1 chk sc ns hs ds)
@[grows] theorem growsIn_valueDecl v : GrowsIn G (valueDecl fuel v) :=
  growsIn_of_keep ((decideKeep fuel).2.2.2.2.2.2.2.2.2.2.2.2.2.1 v)
@[grows] theorem growsIn_valTypeDecl T : GrowsIn G (valTypeDecl fuel T) :=
  growsIn_of_keep ((decideKeep fuel).2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 T)
@[grows] theorem growsIn_isPropV T : GrowsIn G (isPropV fuel T) :=
  growsIn_of_keep ((decideKeep fuel).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 T)
@[grows] theorem growsIn_fnClass T : GrowsIn G (fnClass fuel T) :=
  growsIn_of_keep ((decideKeep fuel).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2 T)
end keep

@[grows] theorem growsIn_liveDecl i : GrowsIn G (liveDecl i) := growsIn_of_keep (keep_liveDecl i)
@[grows] theorem growsIn_absReading σ : GrowsIn G (absReading σ) := growsIn_of_keep (keep_absReading σ)
@[grows] theorem growsIn_capReadings cs rd : GrowsIn G (capReadings cs rd) := growsIn_of_keep (keep_capReadings cs rd)
@[grows] theorem growsIn_fieldTermIsProp d FT : GrowsIn G (fieldTermIsProp d FT) :=
  growsIn_of_keep (keep_fieldTermIsProp d FT)
@[grows] theorem growsIn_fieldIsProof g : GrowsIn G (fieldIsProof g) := growsIn_of_keep (keep_fieldIsProof g)
@[grows] theorem growsIn_ctorIsProof ty : GrowsIn G (ctorIsProof ty) := growsIn_of_keep (keep_ctorIsProof ty)
@[grows] theorem growsIn_preFlags t d : GrowsIn G (preFlags t d) := growsIn_of_keep (keep_preFlags t d)
@[grows] theorem growsIn_refineDecl d : GrowsIn G (refineDecl d) := growsIn_of_keep (keep_refineDecl d)
@[grows] theorem growsIn_sealedSort? t : GrowsIn G (sealedSort? t) := growsIn_of_keep (keep_sealedSort t)
@[grows] theorem growsIn_largeElim d : GrowsIn G (largeElim d) := by unfold largeElim; grows_go
@[grows] theorem growsIn_byTypeMatch ty arms : GrowsIn G (byTypeMatch ty arms) := by unfold byTypeMatch; grows_go

@[grows] theorem growsIn_sortOf? fuel T : GrowsIn G (sortOf? fuel T) := by
  cases fuel <;> (unfold sortOf?; grows_go)
@[grows] theorem growsIn_isBorrowable fuel T : GrowsIn G (isBorrowable fuel T) := by
  cases fuel <;> (unfold isBorrowable; grows_go)
@[grows] theorem growsIn_paramDecls fuel cs rd hs ds c : GrowsIn G (paramDecls fuel cs rd hs ds c) := by
  cases fuel <;> (unfold paramDecls; grows_go)
@[grows] theorem growsIn_stmtArgInPlace fuel a : GrowsIn G (stmtArgInPlace fuel a) := by
  unfold stmtArgInPlace; grows_go
@[grows] theorem growsIn_pushCaps fuel cs rd : GrowsIn G (pushCaps fuel cs rd) := by
  cases fuel <;> (unfold pushCaps; grows_go)
@[grows] theorem growsIn_paramFlags fuel cs rd ds : GrowsIn G (paramFlags fuel cs rd ds) := by
  cases fuel <;> (unfold paramFlags; grows_go)
@[grows] theorem growsIn_leafProof fuel t v : GrowsIn G (leafProof fuel t v) := by
  induction fuel generalizing t v with
  | zero => unfold leafProof; grows_go
  | succ n ih => unfold leafProof; grows_go
@[grows] theorem growsIn_typeClass fuel T : GrowsIn G (typeClass fuel T) := by
  cases fuel <;> (unfold typeClass; grows_go)
@[grows] theorem growsIn_jErased fuel P : GrowsIn G (jErased fuel P) := by
  cases fuel <;> (unfold jErased; grows_go)
@[grows] theorem growsIn_kindOf fuel B : GrowsIn G (kindOf fuel B) := by
  cases fuel <;> (unfold kindOf; grows_go)
@[grows] theorem growsIn_declKind fuel piTy : GrowsIn G (declKind fuel piTy) := by
  cases fuel <;> (unfold declKind; grows_go)
@[grows] theorem growsIn_freshAbsR fuel T : GrowsIn G (freshAbsR fuel T) := by
  cases fuel <;> (unfold freshAbsR; grows_go)
@[grows] theorem growsIn_absOf fuel T : GrowsIn G (absOf fuel T) := by
  cases fuel <;> (unfold absOf; grows_go)
@[grows] theorem growsIn_absAt fuel d T : GrowsIn G (absAt fuel d T) := by
  cases fuel <;> (unfold absAt; grows_go)
@[grows] theorem growsIn_genericValue fuel A d : GrowsIn G (genericValue fuel A d) := by
  cases fuel <;> (unfold genericValue; grows_go)
@[grows] theorem growsIn_jdGrain fuel m : GrowsIn G (jdGrain fuel m) := by
  cases fuel <;> (unfold jdGrain; grows_go)
@[grows] theorem growsIn_jdFns fuel sc t acc : GrowsIn G (jdFns fuel sc t acc) := by
  cases fuel <;> (unfold jdFns; grows_go)

/-- The join's syntactic readers, at one fuel. -/
structure JdGrows (G : Tab) (n : Nat) : Prop where
  jdMoves : ∀ sc al t acc, GrowsIn G (jdMoves n sc al t acc)
  jdMovesList : ∀ sc al ts acc, GrowsIn G (jdMovesList n sc al ts acc)
  jdMatch : ∀ sc al t arms acc, GrowsIn G (jdMatch n sc al t arms acc)
  jdAssigns : ∀ sc t acc, GrowsIn G (jdAssigns n sc t acc)
  jdAssignsList : ∀ sc ts acc, GrowsIn G (jdAssignsList n sc ts acc)

theorem jdGrows : ∀ n, JdGrows G n
  | 0 => by
    constructor <;> intros <;>
      first
      | (unfold Ochr.jdMoves; grows_go) | (unfold Ochr.jdMatch; grows_go) | (unfold Ochr.jdAssigns; grows_go)
      | (rename_i ts _; cases ts <;> (unfold Ochr.jdMovesList; grows_go))
      | (rename_i ts _; cases ts <;> (unfold Ochr.jdAssignsList; grows_go))
  | n + 1 => by
    have ih := jdGrows n
    constructor <;> intros <;>
      first
      | (unfold Ochr.jdMoves; grows_go ih) | (unfold Ochr.jdMatch; grows_go ih) | (unfold Ochr.jdAssigns; grows_go ih)
      | (rename_i ts _; cases ts <;> (unfold Ochr.jdMovesList; grows_go ih))
      | (rename_i ts _; cases ts <;> (unfold Ochr.jdAssignsList; grows_go ih))

@[grows] theorem growsIn_jdMoves fuel sc al t acc : GrowsIn G (jdMoves fuel sc al t acc) := (jdGrows fuel).jdMoves sc al t acc
@[grows] theorem growsIn_jdMovesList fuel sc al ts acc : GrowsIn G (jdMovesList fuel sc al ts acc) :=
  (jdGrows fuel).jdMovesList sc al ts acc
@[grows] theorem growsIn_jdMatch fuel sc al t arms acc : GrowsIn G (jdMatch fuel sc al t arms acc) :=
  (jdGrows fuel).jdMatch sc al t arms acc
@[grows] theorem growsIn_jdAssigns fuel sc t acc : GrowsIn G (jdAssigns fuel sc t acc) := (jdGrows fuel).jdAssigns sc t acc
@[grows] theorem growsIn_jdAssignsList fuel sc ts acc : GrowsIn G (jdAssignsList fuel sc ts acc) :=
  (jdGrows fuel).jdAssignsList sc ts acc

@[grows] theorem growsIn_typeState fuel t : GrowsIn G (typeState fuel t) := by
  cases fuel with
  | zero => unfold typeState; grows_go
  | succ n => have ih : JdGrows G n := jdGrows n; unfold typeState; grows_go ih

end Ochr.Meaning.Steps.Machine
