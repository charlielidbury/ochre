import Ochr.Meaning.Apply

/-!
# Places on meanings, and the decisions the reference run reads from syntax

## Places

A place `x | *p | p.i | p.g` is followed on a meaning by reading the meaning (docs/31 D32): `*` is
the identity (a borrow's holder means its content, docs/27 Def. 2), `.0` of a number is its
predecessor, and `.i` and `.g` take a field of a constructor value, which describes itself
(`Sem.dat`: name, record, constructor, fields). No declaration is consulted to find the
field; the type handed on (`DataModel.readTy`, from the type's declaration and the value's own
record, route (c)) is what a read's result is typed at. A
partly moved value projects like a whole one; `⊥` and `err` have no fields. Updating at a path
rebuilds the tree (`reDat`); whether it is a member is the data model's predicate on trees.

## Decisions (docs/18 §"Decisions, by kind", *aligned*)

Some of the checker's decisions change what a step means, and the model must make the same
choice: whether a term is a statement (run on a copy that is thrown away), a Π-type's sort, η at
`Unit` (D80), copy or move on a read (D80), and D84's drop at the join. The checker reads each
from syntax and declared types alone (`Decide.lean`, D77, D80), never from a run, so the
reference run can read the same. `Decisions` is that interface; the step lemmas prove its
fields equal to the checker's functions (`Decide.preFlags`, `piSort`, `etaUnit`/`declCopy`,
`jdMoves`), which is where "aligned" is discharged.
-/

namespace Ochr.Meaning

open Classical

/-- The readings the reference run takes from syntax, exactly as the checker does. `sc` is the
scope of declared-type readings (`Binding.decl`, innermost first), as `Decide.placeDecl` takes
it. -/
structure Decisions : Type where
  /-- Is this term a statement (erased: a type, a proof, a type-returning or proof-returning
  call), and is it a proof (`Decide.preFlags`)? -/
  flags : List DeclInfo → Term → Bool × Bool
  /-- A place's declared-type reading (`Decide.placeDecl`). -/
  placeDecl : List DeclInfo → Place → DeclInfo
  /-- A term's declared-type reading (`Decide.declOf`). -/
  declOf : List DeclInfo → Term → DeclInfo
  /-- Does a reading say "copy" (`Decide.declCopy`, D80)? -/
  copy : DeclInfo → Bool
  /-- The sort of a Π-term (`Machine.piSort` / `Decide.sortOf`): 0 for `Prop`, `l + 1` for `Type_l`. -/
  piSort : List DeclInfo → Term → Nat
  /-- D84: the places a match drops at its join (`Decide.jdMoves`), given the places already
  moved when the match starts (its `entry` argument). -/
  joinMoves : List DeclInfo → List Place → Term → List Place
  /-- D84 [Id-typestate]/[Obs-ref]: the borrow bindings a side re-points (assigns whole and does
  not consume), read from syntax and declared types (`Decide.typeState`'s `repointed`). -/
  rePointed : List DeclInfo → Term → List Place
  /-- The reading of a type term, as a type (`Decide.typeDecl`): what a binding declared at it
  reads (D19, R3: a parameter's reading is its domain term's, `Decide.paramDecls`). -/
  typeDecl : List DeclInfo → Term → DeclInfo
  /-- D90 [Entry] (static ends, rule 2): what the stuck block a match term (or `J`'s transported
  term) would close off as captures, given the places already moved at its start (`entry`), as
  `Machine.blockEntry` computes it: the places `movedPlace` re-roots while the captures are
  computed (K1(a), in order, before re-rooting), and the captures with their modes (`0` read in
  place, `1` by `&`, `2` by move), in the block's order (oldest binding first, then shorter
  paths). Its alignment with `Machine.blockCaptures` is D90's first obligation (docs/31 D37); the
  instance is `BlockCaps.staticBlockCaps`. -/
  blockCaps : List DeclInfo → List Place → Term → List Place × List (Place × Nat) := fun _ _ _ => ([], [])

/-- The scope after a telescope of parameter types: each parameter's reading, read in the scope
of the earlier ones, innermost first (`Decide.telescope`). -/
def Decisions.teleDecls (D : Decisions) (sc : List DeclInfo) : List Term → List DeclInfo
  | [] => sc
  | d :: ds => D.teleDecls (D.typeDecl sc d :: sc) ds

/-- The declared readings of a telescope's parameters, in order (`Decide.paramDecls`'s first
component): what a frame binds them at. -/
def Decisions.paramDecls (D : Decisions) (sc : List DeclInfo) (ds : List Term) : List DeclInfo :=
  ((D.teleDecls sc ds).take ds.length).reverse

/-- The declared readings of a function's parameters, in order, and of its codomain, read in the
scope `sc` where the function is formed (`Decide.paramDecls`): what the closure's frame binds its
parameters at, and (`.pi cd`) `self`. -/
def Decisions.fixDecls (D : Decisions) (sc : List DeclInfo) (ds : List Term) (c : Term) : List DeclInfo × DeclInfo :=
  (D.paramDecls sc ds, D.typeDecl (D.teleDecls sc ds) c)

mutual
/-- **The height of a meaning** (docs/34 §15): a constructor value one more than its fields, a
number its value, anything else `0`. -/
noncomputable def semHeight : Sem → Nat
  | .dat _ _ _ fs => semHeightList fs + 1
  | s => s.asNat.getD 0
noncomputable def semHeightList : List Sem → Nat
  | [] => 0
  | f :: fs => max (semHeight f) (semHeightList fs)
end

theorem semHeight_le_list : ∀ (fs : List Sem) (f : Sem), f ∈ fs → semHeight f ≤ semHeightList fs
  | [], _, h => by cases h
  | g :: gs, f, h => by
    simp only [semHeightList]
    rcases List.mem_cons.1 h with rfl | h
    · exact Nat.le_max_left _ _
    · exact Nat.le_trans (semHeight_le_list gs f h) (Nat.le_max_right _ _)

/-- **Every field of a constructor value has smaller height**, through every declaration and every
nesting, whole, partly moved or open (docs/34 §15). -/
theorem semHeight_field_lt (n : String) (r : Rec) (c : Nat) (fs : List Sem) (f : Sem) (h : f ∈ fs) :
    semHeight f < semHeight (.dat n r c fs) := by
  simp only [semHeight]
  exact Nat.lt_succ_of_le (semHeight_le_list fs f h)

/-- The rank of a meaning for guarded recursion ([Rec], docs/24): its height (docs/34 §15). -/
noncomputable def semRank (s : Sem) : Nat := semHeight s

/-- A constructor value rebuilt after one of its fields changed: the tree, by its own name and
record (docs/34: membership is the model's predicate on trees, so nothing is repacked). The data
model and declarations are not read (kept so that callers read alike). -/
def reDat (_dm : DataModel) (_Γ : List IndDecl) (n : String) (r : Rec) (c : Nat) (fs : List Sem) : Sem :=
  .dat n r c fs

section
variable (dm : DataModel) (Γ : List IndDecl)

/-- The type field `i` of constructor `c` of `d` at the record `r` is read at, given the earlier
fields: its declared type's code, the hint `Value.meanFields` reads the field at. -/
def fieldHint (d : IndDecl) (r : Rec) (c i : Nat) (earlier : List Sem) : TyS :=
  .plain (dm.fieldTyR d r c i earlier)

/-- Field `i` of constructor `c` of a constructor value read at the type `T` (route (c), D32): the
field and the type the read gives it (`DataModel.readTy`), from `T`'s declaration (a data code
carries it) and the value's own record; never a declaration looked up by name. The read fails where
`T` is no data code, where `T`'s declaration is not the value's (the names differ), and at a junk
leaf. A field of `⋆` is `⋆` at `err`. `Γ` is not read (kept so that callers read alike). -/
noncomputable def Sem.stepField (T : TyS) (c i : Nat) (s : Sem) : Option (Sem × TyS) :=
  match s with
  | .proof => some (.proof, .plain TyM.err)
  | .dat n r c' fs =>
    match T.m.dataCode? with
    | some (d, _) =>
      if d.name = n ∧ c' = c then
        match fs[i]? with
        | some f => (dm.readTy d r c i (fs.take i) f).map fun U => (f, .plain U)
        | none => none
      else none
    | none => none
  | _ => none

/-- One step on a meaning: the sub-meaning and its type, exactly where the checker's `stepV`
steps. A step `.0` into a number takes its predecessor (a partly moved number's at a type that is
no data code); a positional step `.i` reads constructor `0`'s field; a named step `.g` reads a field
of a constructor value of `g`'s declaration, never a number's; a field of `⋆` is `⋆`; `*` is the
identity (a borrow means its content). The type `T` is the type of `s`, handed on through `*`. -/
noncomputable def Sem.step (T : TyS) : Step → Sem → Option (Sem × TyS)
  -- `Γ` is not read (kept so that callers read alike; named here so the section includes it)
  | .deref, s => let _ := Γ; some (s, T)
  | .proj 0, s =>
    match s.asNat with
    | some (n + 1) => some (.el0 Nat n, .plain TyM.nat)
    | some 0 => none
    | none => match T.m.dataCode?, s with
      | none, .dat "Nat" _ 1 [w] => some (w, .plain TyM.nat)
      | _, _ => Sem.stepField dm T 0 0 s
  | .proj i, s => Sem.stepField dm T 0 i s
  -- a named field step reads only a constructor value of the declaration it names, as the
  -- checker's `stepV` reads only `.ind` values of `g.ty`; never a number (the checker's numbers are
  -- `zero`/`succ`, with no named field; no declaration is named `Nat`, (N))
  | .field g, s => match s with
    | .dat n _ _ _ => if n = g.ty ∧ n ≠ "Nat" then Sem.stepField dm T g.ctor g.idx s else none
    | s => Sem.stepField dm T g.ctor g.idx s

/-- Follow a path on a meaning of type `T`. -/
noncomputable def Sem.follow (T : TyS) (s : Sem) : List Step → Option (Sem × TyS)
  | [] => some (s, T)
  | st :: sts => (Sem.step dm Γ T st s).bind fun (s', T') => Sem.follow T' s' sts

/-- Update the sub-meaning at a path, reading the value only (docs/31 D32): a number's
predecessor through `.0`, a constructor value's field, rebuilt by its own declaration (`reDat`:
a field set to `moved` makes it a partly moved value). `T` is not consulted (kept so that callers
read alike). -/
noncomputable def Sem.updAt (T : TyS) (f : Sem → Sem) : List Step → Sem → Option Sem
  | [], s => some (f s)
  | .deref :: sts, s => Sem.updAt T f sts s
  | st :: sts, s =>
    match st, s.asNat with
    | .proj 0, some (n + 1) => (Sem.updAt (.plain TyM.nat) f sts (.el0 Nat n)).map Sem.succ
    | _, _ =>
      match s with
      | .dat "Nat" _ 1 [w] =>
        match st with
        | .proj 0 => (Sem.updAt (.plain TyM.nat) f sts w).map Sem.succ
        | _ => none
      | .dat n r c fs =>
        let i := match st with | .proj i => i | .field g => g.idx | .deref => 0
        match fs[i]? with
        | some fi => (Sem.updAt T f sts fi).map fun fi' => reDat dm Γ n r c (fs.set i fi')
        | none => none
      | _ => none

/-- The field a step names, as `Sem.updAt` reads it. -/
def _root_.Ochr.Step.fieldIdx : Step → Nat
  | .proj i => i
  | .field g => g.idx
  | .deref => 0

theorem _root_.Ochr.Step.fieldIdx_eq (st : Step) :
    (match st with | .proj i => i | .field g => g.idx | .deref => 0) = st.fieldIdx := by cases st <;> rfl

theorem Sem.asNat_dat (n : String) (r : Rec) (c : Nat) (fs : List Sem) :
    (Sem.dat n r c fs).asNat = none := rfl

/-- A write at a field of a constructor value rebuilds it by its own name (`reDat`). -/
theorem Sem.updAt_dat' (T : TyS) (f : Sem → Sem) (st : Step) (sts : List Step) {n : String} {r : Rec}
    {c : Nat} {fs : List Sem} {fi : Sem}
    (hst : st ≠ .deref) (hn : n ≠ "Nat") (hi : fs[st.fieldIdx]? = some fi) :
    Sem.updAt dm Γ T f (st :: sts) (.dat n r c fs) =
      (Sem.updAt dm Γ T f sts fi).map fun fi' => reDat dm Γ n r c (fs.set st.fieldIdx fi') := by
  cases st with
  | deref => exact absurd rfl hst
  | proj i =>
    rw [Sem.updAt.eq_def]
    simp only [Sem.asNat_dat]
    split
    · rename_i heq; simp only [Sem.dat.injEq] at heq; exact absurd heq.1 hn
    · rename_i heq
      simp only [Sem.dat.injEq] at heq
      obtain ⟨rfl, rfl, rfl, rfl⟩ := heq
      simp only [Step.fieldIdx] at hi ⊢
      rw [hi]
    · rename_i hne; exact absurd rfl (hne _ _ _ _)
  | field g =>
    rw [Sem.updAt.eq_def]
    simp only [Sem.asNat_dat]
    split
    · rename_i heq; simp only [Sem.dat.injEq] at heq; exact absurd heq.1 hn
    · rename_i heq
      simp only [Sem.dat.injEq] at heq
      obtain ⟨rfl, rfl, rfl, rfl⟩ := heq
      simp only [Step.fieldIdx] at hi ⊢
      rw [hi]
    · rename_i hne; exact absurd rfl (hne _ _ _ _)

/-- A constructor value is a `dat` of its declaration's name and record. -/
theorem ctorM_dat (d : IndDecl) (ps : List Sem) (c : Nat) (fs : List Sem) :
    dm.ctorM d ps c fs = .dat d.name (dm.recOf d ps) c fs := rfl

/-- Rebuilding by the name of a declaration is the constructor value at the record. -/
theorem reDat_eq (d : IndDecl) (r : Rec) (c : Nat) (fs : List Sem) :
    reDat dm Γ d.name r c fs = DataModel.ctorR d r c fs := rfl

/-- Rebuilding is the tree, with a moved field as with any other. -/
theorem reDat_moved (dm : DataModel) (Γ : List IndDecl) (n : String) (r : Rec) (c : Nat) (fs : List Sem) :
    reDat dm Γ n r c fs = .dat n r c fs := rfl

end

mutual
/-- The places under `q` whose content in the meaning `x` is `moved`: `Machine.botPlaces`, on
meanings. A partly moved constructor value is a tuple (`DataModel.ctorM`) and names its fields as
the checker does (a `FieldRef` is compared without its printing name); a partly moved number is
`S` of its predecessor, the step `.0`. A whole value holds no moved part. -/
def Sem.movedIn : Sem → Place → List Place
  | .moved, q => [q]
  | .dat t _ c fs, q => if t = "Nat" then Sem.movedInNat fs q else Sem.movedInFields t c q 0 fs
  | _, _ => []
termination_by structural x => x

def Sem.movedInFields (t : String) (c : Nat) (q : Place) : Nat → List Sem → List Place
  | _, [] => []
  | i, w :: ws => Sem.movedIn w (.field ⟨t, c, i, s!"f{i}"⟩ q) ++ Sem.movedInFields t c q (i + 1) ws
termination_by structural _ ws => ws

def Sem.movedInNat : List Sem → Place → List Place
  | [], _ => []
  | w :: _, q => Sem.movedIn w (.proj 0 q)
termination_by structural ws => ws
end

end Ochr.Meaning
