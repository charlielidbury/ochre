import Ochr.Meaning.Steps.Machine.Tactic

/-!
# `GrowsIn` for the state's own operations (`Env.lean`, `Rules.lean`, `Located.lean`)

Frames, bindings, temporaries, the flags, the log: none writes a table.
-/

namespace Ochr.Meaning.Steps.Machine

open Ochr Ochr.Meaning Ochr.Meaning.Steps Ochr.Meaning.DecideScope

variable {G : Tab}

@[grows] theorem growsIn_absType (σ : Nat) : GrowsIn G (absType σ) := by unfold absType; grows_go
@[grows] theorem growsIn_lookupInd (n : String) : GrowsIn G (lookupInd n) := by unfold lookupInd; grows_go
@[grows] theorem growsIn_lookupGlobal (n : String) : GrowsIn G (lookupGlobal n) := by unfold lookupGlobal; grows_go
@[grows] theorem growsIn_topIdx : GrowsIn G topIdx := by unfold topIdx; grows_go
@[grows] theorem growsIn_modifyFrame (f : Nat) (g : Frame → Frame) : GrowsIn G (modifyFrame f g) := by
  unfold modifyFrame; grows_go
@[grows] theorem growsIn_pushFrame (fr : Frame) : GrowsIn G (pushFrame fr) := by unfold pushFrame; grows_go
@[grows] theorem growsIn_pushBind (h : Hint) (ty : Option Value) (v : Value) (proof : Bool) (decl : DeclInfo) :
    GrowsIn G (pushBind h ty v proof decl) := by unfold pushBind; grows_go
@[grows] theorem growsIn_pushTemp (v : Value) : GrowsIn G (pushTemp v) := by unfold pushTemp; grows_go
@[grows] theorem growsIn_pushTempAt (f : Nat) (v : Value) : GrowsIn G (pushTempAt f v) := by unfold pushTempAt; grows_go
@[grows] theorem growsIn_popTemp : GrowsIn G popTemp := by unfold popTemp; grows_go
@[grows] theorem growsIn_varPos (i : Nat) : GrowsIn G (varPos i) := by unfold varPos; grows_go
@[grows] theorem growsIn_getAt (p : Pos) : GrowsIn G (getAt p) := by unfold getAt; grows_go
@[grows] theorem growsIn_setAt (p : Pos) (v : Value) : GrowsIn G (setAt p v) := by unfold setAt; grows_go
@[grows] theorem growsIn_tyAt (p : Pos) : GrowsIn G (tyAt p) := by unfold tyAt; grows_go
@[grows] theorem growsIn_demand (b : Bool) : GrowsIn G (demand b) := by unfold demand; grows_go
@[grows] theorem growsIn_wanted : GrowsIn G wanted := by unfold wanted; grows_go
@[grows] theorem growsIn_getFlags : GrowsIn G getFlags := by unfold getFlags; grows_go
@[grows] theorem growsIn_setFlags (f : Bool × Bool) : GrowsIn G (setFlags f) := by unfold setFlags; grows_go
@[grows] theorem growsIn_trace (msg : Unit → String) : GrowsIn G (trace msg) := by unfold trace; grows_go

@[grows] theorem growsIn_popFrameRaw : GrowsIn G popFrameRaw := by
  unfold popFrameRaw
  refine growsIn_get_bind_at fun s hs => ?_
  split
  · exact growsAt_set_bind (tablesGrow_of_eq rfl rfl rfl rfl rfl) hs fun _ => growsIn_pure _
  · exact growsAt_of_growsIn hs (growsIn_err _)
@[grows] theorem growsIn_popTemps (n : Nat) : GrowsIn G (popTemps n) := by unfold popTemps; grows_go
@[grows] theorem growsIn_mapState (f : Value → M Value) (types : Bool) (hf : ∀ v, GrowsIn G (f v)) :
    GrowsIn G (mapState f types) := by
  unfold mapState; grows_go
@[grows] theorem growsIn_fire (r : Rule) (msg : Unit → String) : GrowsIn G (fire r msg) := by unfold fire; grows_go
@[grows] theorem growsIn_fireExt (e : Ext) (msg : Unit → String) : GrowsIn G (fireExt e msg) := by
  unfold fireExt; grows_go
@[grows] theorem growsIn_atLoc {α : Type} (l : Option Loc) {x : M α} (hx : GrowsIn G x) : GrowsIn G (atLoc l x) := by
  unfold atLoc; grows_go
@[grows] theorem growsIn_unlocated {α : Type} {x : M α} (hx : GrowsIn G x) : GrowsIn G (unlocated x) := by
  unfold unlocated; grows_go
@[grows] theorem growsIn_noteLoc (l : Option Loc) (n : Note) : GrowsIn G (noteLoc l n) := by unfold noteLoc; grows_go
@[grows] theorem growsIn_noteAt (t : Term) (n : Note) : GrowsIn G (noteAt t n) := by unfold noteAt; grows_go
@[grows] theorem growsIn_noteValue (t : Term) {x : M (Value × Option Value)} (hx : GrowsIn G x) :
    GrowsIn G (noteValue t x) := by unfold noteValue; grows_go
@[grows] theorem growsIn_noteEnders (e : Array (Option Nat)) (ws : Array Value) : GrowsIn G (noteEnders e ws) := by
  unfold noteEnders; grows_go
@[grows] theorem growsIn_enderLoc (e : Array (Option Nat)) (ws : Array Value) : GrowsIn G (enderLoc e ws) := by
  unfold enderLoc; grows_go
@[grows] theorem growsIn_placeContent? (p : Place) : GrowsIn G (placeContent? p) := by unfold placeContent?; grows_go
@[grows] theorem growsIn_noteHole (t : Term) (g : Value) : GrowsIn G (noteHole t g) := by unfold noteHole; grows_go
@[grows] theorem growsIn_takeArgBorrow (w : Value) : GrowsIn G (takeArgBorrow w) := by
  unfold takeArgBorrow; grows_go
@[grows] theorem growsIn_relocate (o n : Term) : GrowsIn G (relocate o n) := by unfold relocate; grows_go

end Ochr.Meaning.Steps.Machine
