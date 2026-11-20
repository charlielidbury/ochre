import Ochr.Meaning.Apply

/-!
# Places on meanings, and the decisions the reference run reads from syntax

## Places

A place `x | *p | p.i | p.g` is followed on a meaning by reading the meaning (docs/31 D32): `*` is
the identity (a borrow's holder means its content, docs/27 Def. 2), `.0` of a number is its
predecessor, and `.i` and `.g` take a field of a constructor value, which describes itself
(`Sem.dat`: name, parameters, constructor, fields). No type, declaration or carrier is consulted
to find the field; the type handed on (`contentTyS`) is the field's own when it is a constructor
value, else its declared one, and is what a read's result is typed at. A partly moved value
projects like a whole one; `⊥` and `err` have no fields. Updating at a path rebuilds with
`DataModel.ctorM` by the value's own name (`reDat`), so a field set to `moved` leaves no element.

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

section
variable (dm : DataModel) (Γ : List IndDecl)

/-- The declaration and parameters a structured type names (docs/31 D31): the declaration of
`Γ` with its data's NAME, at its data's parameters. Since D32 no value is decoded through a type;
this names a declaration for a type's own use (a bare constructor's parameters, D8). -/
def TyS.dataDecl (T : TyS) : Option (IndDecl × List Sem) :=
  T.data.bind fun (n, ps) => (Γ.find? (·.name == n)).map (·, ps)

/-- The structured type field `i` of constructor `c` of `d` at `ps` is read at, given the earlier
fields: its declared type and data, the hint `Value.meanFields` reads the field at. -/
def fieldHint (d : IndDecl) (ps : List Sem) (c i : Nat) (earlier : List Sem) : TyS :=
  ⟨dm.fieldTy d ps c i earlier, none, none, dm.fieldData d ps c i earlier⟩

/-- The structured type of a constructor value of the declaration named `n` at the parameters `ps`
(docs/31 D32: a value read off a constructor value is typed by its content). -/
def dataTyS (n : String) (ps : List Sem) : TyS :=
  match Γ.find? (·.name == n) with
  | some d => ⟨dm.tyM d ps, none, none, some (n, ps)⟩
  | none => .plain .err

/-- The type a field read off a constructor value is read at: its own when it is a constructor
value (by content, as the checker types an open value's field), a number's when it is a partly
moved number, else the hint its declaration gives it at the earlier fields. -/
def contentTyS (n : String) (ps : List Sem) (c i : Nat) (earlier : List Sem) : Sem → TyS
  | .dat "Nat" _ _ _ _ => .plain (.ty0 Nat)
  | .dat n' ps' _ _ _ => dataTyS dm Γ n' ps'
  | _ => match Γ.find? (·.name == n) with
    | some d => fieldHint dm d ps c i earlier
    | none => .plain .err

/-- A constructor value rebuilt after one of its fields changed: packed again when whole and of
its type (`ctorM`), by its own declaration's name. -/
noncomputable def reDat (n : String) (ps : List Sem) (c : Nat) (fs : List Sem) : Sem :=
  match Γ.find? (·.name == n) with
  | some d => dm.ctorM d ps c fs
  | none => .dat n ps c fs none

/-- The rank of a meaning for guarded recursion ([Rec], docs/24): a constructor value's element's
rank, found by its own declaration's name (docs/31 D32: no declaration is guessed from a carrier),
or a number. -/
noncomputable def semRank : Sem → Nat
  | .dat n ps _ _ (some ⟨A, x⟩) =>
    match Γ.find? (·.name == n) with
    | some d => open Classical in if h : A = dm.car d ps then dm.rank (h ▸ x) else 0
    | none => 0
  | s => match s.asNat with | some n => n | none => 0

/-- Field `i` of constructor `c` of a constructor value, read off the value (docs/31 D32), with the
type it is read at (`contentTyS`). -/
noncomputable def Sem.stepField (c i : Nat) (s : Sem) : Option (Sem × TyS) :=
  match s with
  | .proof => some (.proof, .plain .err)
  | .dat n ps c' fs _ =>
    if c' = c then (fs[i]?).map fun f => (f, contentTyS dm Γ n ps c i (fs.take i) f) else none
  | _ => none

/-- One step on a meaning: the sub-meaning and its type. A step `.0` into a number takes its
predecessor; any other field step reads the constructor value; `*` is the identity (a borrow
means its content). The type `T` is the type of `s`, handed on through `*`. -/
noncomputable def Sem.step (T : TyS) : Step → Sem → Option (Sem × TyS)
  | .deref, s => some (s, T)
  | .proj 0, s =>
    match s.asNat with
    | some (n + 1) => some (.el0 Nat n, .plain (.ty0 Nat))
    | some 0 => none
    | none => match s with
      | .dat "Nat" _ 1 [w] _ => some (w, .plain (.ty0 Nat))
      | _ => Sem.stepField dm Γ 0 0 s
  | .proj i, s => Sem.stepField dm Γ 0 i s
  | .field g, s => Sem.stepField dm Γ g.ctor g.idx s

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
    | .proj 0, some (n + 1) => (Sem.updAt (.plain (.ty0 Nat)) f sts (.el0 Nat n)).map Sem.succ
    | _, _ =>
      match s with
      | .dat "Nat" _ 1 [w] _ =>
        match st with
        | .proj 0 => (Sem.updAt (.plain (.ty0 Nat)) f sts w).map Sem.succ
        | _ => none
      | .dat n ps c fs _ =>
        let i := match st with | .proj i => i | .field g => g.idx | .deref => 0
        match fs[i]? with
        | some fi => (Sem.updAt T f sts fi).map fun fi' => reDat dm Γ n ps c (fs.set i fi')
        | none => none
      | _ => none

/-- The field a step names, as `Sem.updAt` reads it. -/
def _root_.Ochr.Step.fieldIdx : Step → Nat
  | .proj i => i
  | .field g => g.idx
  | .deref => 0

theorem _root_.Ochr.Step.fieldIdx_eq (st : Step) :
    (match st with | .proj i => i | .field g => g.idx | .deref => 0) = st.fieldIdx := by cases st <;> rfl

theorem Sem.asNat_dat (n : String) (ps : List Sem) (c : Nat) (fs : List Sem) (el : Option ((A : Type) × A)) :
    (Sem.dat n ps c fs el).asNat = none := rfl

/-- A write at a field of a constructor value rebuilds it by its own name (`reDat`). -/
theorem Sem.updAt_dat' (T : TyS) (f : Sem → Sem) (st : Step) (sts : List Step) {n : String} {ps : List Sem}
    {c : Nat} {fs : List Sem} {el : Option ((A : Type) × A)} {fi : Sem}
    (hst : st ≠ .deref) (hn : n ≠ "Nat") (hi : fs[st.fieldIdx]? = some fi) :
    Sem.updAt dm Γ T f (st :: sts) (.dat n ps c fs el) =
      (Sem.updAt dm Γ T f sts fi).map fun fi' => reDat dm Γ n ps c (fs.set st.fieldIdx fi') := by
  cases st with
  | deref => exact absurd rfl hst
  | proj i =>
    rw [Sem.updAt.eq_def]
    simp only [Sem.asNat_dat]
    split
    · rename_i heq; simp only [Sem.dat.injEq] at heq; exact absurd heq.1 hn
    · rename_i heq
      simp only [Sem.dat.injEq] at heq
      obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := heq
      simp only [Step.fieldIdx] at hi ⊢
      rw [hi]
    · rename_i hne; exact absurd rfl (hne _ _ _ _ _)
  | field g =>
    rw [Sem.updAt.eq_def]
    simp only [Sem.asNat_dat]
    split
    · rename_i heq; simp only [Sem.dat.injEq] at heq; exact absurd heq.1 hn
    · rename_i heq
      simp only [Sem.dat.injEq] at heq
      obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := heq
      simp only [Step.fieldIdx] at hi ⊢
      rw [hi]
    · rename_i hne; exact absurd rfl (hne _ _ _ _ _)

/-- A packed constructor value is a `dat` of its declaration's name. -/
theorem ctorM_dat (d : IndDecl) (ps : List Sem) (c : Nat) (fs : List Sem) :
    ∃ el, dm.ctorM d ps c fs = .dat d.name ps c fs el := by
  unfold DataModel.ctorM
  split
  · split
    · exact ⟨_, rfl⟩
    · exact ⟨_, rfl⟩
  · exact ⟨_, rfl⟩

/-- Rebuilding by the name of a declaration found by that name is `ctorM`. -/
theorem reDat_eq {d : IndDecl} {ty : String} (hf : Γ.find? (·.name == ty) = some d) (ps : List Sem) (c : Nat)
    (fs : List Sem) : reDat dm Γ d.name ps c fs = dm.ctorM d ps c fs := by
  have hn : d.name = ty := by
    have := List.find?_some hf; simpa using this
  unfold reDat; rw [hn, hf]

/-- Rebuilding with a moved field gives a value with no element. -/
theorem reDat_moved (dm : DataModel) (Γ : List IndDecl) (n : String) (ps : List Sem) (c : Nat) (fs : List Sem)
    (h : Sem.moved ∈ fs) : reDat dm Γ n ps c fs = .dat n ps c fs none := by
  have hnw : ¬ ∀ f ∈ fs, f.whole := fun hw => by simpa [Sem.whole] using hw _ h
  unfold reDat
  split
  · rename_i d hd
    have hn : d.name = n := by have := List.find?_some hd; simpa using this
    simp only [DataModel.ctorM, if_neg hnw, hn]
  · rfl

end

mutual
/-- The places under `q` whose content in the meaning `x` is `moved`: `Machine.botPlaces`, on
meanings. A partly moved constructor value is a tuple (`DataModel.ctorM`) and names its fields as
the checker does (a `FieldRef` is compared without its printing name); a partly moved number is
`S` of its predecessor, the step `.0`. A whole value holds no moved part. -/
def Sem.movedIn : Sem → Place → List Place
  | .moved, q => [q]
  | .dat t _ c fs _, q => if t = "Nat" then Sem.movedInNat fs q else Sem.movedInFields t c q 0 fs
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
