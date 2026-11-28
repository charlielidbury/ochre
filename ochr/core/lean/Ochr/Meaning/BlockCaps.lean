import Ochr.Meaning.Places
import Ochr.Machine

/-!
# A stuck block's captures, read statically (D90 [Entry], obligation 1)

`Machine.blockEntry` (static ends, rule 2: a non-tail match on a known constructor, and `J`'s
transported term wherever `J` computes) accesses what the stuck block it would close off as
captures: `staticJoin`, then `blockCaptures` (K1), sorted oldest binding first, then
`entryAccess`. The reference run reads those captures as a decision (`Decisions.blockCaps`). This
file is its instance: K1 clause by clause, with each input that `blockCaptures` reads from a
value replaced by what the declarations say, as D90's census argues they agree.

Which inputs of `blockCaptures` are static, and which read values (D90's obligation 1):
* static (syntax and declared readings): the moved set (`staticJoin`, `Decide.jdMoves`, D84, at
  its grain), the closures' captures (`fnOccs`) and copy-ness (`copyRead`: `Decide.placeDecl`,
  `declCopy`, D80), the occurrence kinds (`freeOccsBlock`), the maximal places (K1(c)), the
  covering by moved places (K1(d), K1(e)), the sort order;
* read from a value, replaced here:
  - `movedPlace`'s re-rooting of a moved place (K1(a)): a place exists unless a strict prefix holds
    `⊥` or `⋆`, and then it is re-rooted to the shortest such prefix (`staticReroot`). Which places
    hold `⊥` is the match's entry set (`botPlaces`, D84's grain, the same on every path by (A3));
    which hold `⋆` is read off the declared reading (`.prop`). `movedPlace`'s other branches
    (an unknown or a sealed program of a one-constructor type, refined or generalised; a filled
    parent, accessed) leave the place existing, so they do not re-root; their accesses are the
    reference's `accessLentPrefix` (`Run.entryAccess`);
  - K1(b)'s "a borrow variable" (`b.val.isBorrow || b.ty is &_`): the declared reading `.ref _`
    (D90: the value disjunct is redundant beside the declared type);
  - K1(f)'s proof flag (`placeType?` then `isPropV`): the declared reading `.prop`;
  - K1(g)'s split of a capture into its fields (`content q`'s constructor): only a value of a
    one-constructor type is split (the grain), so its constructor is the declaration's only one,
    and its fields are the declaration's. A number's predecessor is never split (a number is a
    copy type, so no part of one is moved).
The equality of this function with `blockCaptures` at the checker's states is stated, not proved
(`blockCaps_aligned_stmt`, `Steps/Statements.lean`).
-/

namespace Ochr.Meaning

open Ochr

namespace BlockCaps

/-- The strict prefixes of a place, shortest first. -/
def strictPrefixes (q : Place) : List Place :=
  let (r, ss) := q.steps
  (List.range ss.length).map fun k => (ss.take k).foldl stepPlace (.var r)

/-- `movedPlace`'s re-rooting, statically: the shortest strict prefix that is moved at the
match's start or is a proof, else the place. -/
def staticReroot (placeDecl : Place → DeclInfo) (entry : List Place) (q : Place) : Place :=
  match (strictPrefixes q).find? (fun p => entry.any (placeEq · p) || (placeDecl p matches .prop)) with
  | some p => p
  | none => q

/-- The fields of a place of a one-constructor type, by its declaration (K1(g)). -/
def oneCtorFields (Γ : List IndDecl) (r : DeclInfo) (q : Place) : Option (List Place) :=
  match r with
  | .ind n _ =>
    match Γ.find? (·.name == n) with
    | some d =>
      match d.ctors with
      | [(_, fs)] => some (fs.zipIdx.map fun ((name, _), i) => Place.field ⟨n, 0, i, name⟩ q)
      | _ => none
    | none => none
  | _ => none

/-- K1(g)'s worklist, breadth first as `blockCaptures`' `while` loop. -/
def splitLoop (Γ : List IndDecl) (placeDecl : Place → DeclInfo) (moved : List Place)
    (uses : List (Place × Nat)) (wholeUses : List (Place × PKind)) :
    Nat → List (Place × Nat) → List (Place × Nat) → List (Place × Nat)
  | 0, todo, out => out ++ todo
  | _ + 1, [], out => out
  | n + 1, (q, k) :: todo, out =>
    let inner := moved.filter fun m => placePrefix q m && !(placeEq m q)
    if k == 2 || inner.isEmpty then splitLoop Γ placeDecl moved uses wholeUses n todo (out ++ [(q, k)])
    else if wholeUses.any (fun (p, pk) => placeEq p q && pk != .scrut) then
      splitLoop Γ placeDecl moved uses wholeUses n todo (out ++ [(q, 2)])
    else match oneCtorFields Γ (placeDecl q) q with
      | none => splitLoop Γ placeDecl moved uses wholeUses n todo (out ++ [(q, 2)])
      | some chs =>
        let new := chs.filterMap fun ch =>
          let under := uses.filter fun (p, _) => placePrefix ch p
          if under.isEmpty && !(moved.any fun m => placePrefix ch m) then none
          else some (ch, if moved.any (placeEq · ch) then 2 else under.foldl (fun m (_, k) => max m k) 0)
        splitLoop Γ placeDecl moved uses wholeUses n (todo ++ new) out

/-- **The captures, statically**: `blockEntry`'s `staticJoin`, `blockCaptures` (K1(a)–(g)) and
sort, with the value reads replaced as the module docstring lists. Returns the places
`movedPlace` is asked of (before re-rooting, in order) and the sorted captures with their modes. -/
def staticBlockCaps (D : Decisions) (Γ : List IndDecl) (fuel : Nat) (sc : List DeclInfo) (entry : List Place)
    (mt : Term) : List Place × List (Place × Nat) :=
  let pd := D.placeDecl sc
  -- `staticJoin`'s net: the join's moves not already moved
  let net := (D.joinMoves sc entry mt).filter fun q => !entry.any (jdCovers · q)
  -- K1(a): the closures' non-copy captures
  let mv := (mt.fnOccs 0).foldl (fun mv (o, p) =>
    let q := p.mapRoot fun _ => .var o
    if D.copy (pd q) then mv else if mv.any (placeEq · q) then mv else mv ++ [q]) net
  let moved := mv.foldl (fun acc q =>
    let q' := staticReroot pd entry q
    if acc.contains q' then acc else acc ++ [q']) []
  -- K1(b): modes by use
  let occs := mt.freeOccsBlock
  let uses : List (Place × Nat) := occs.map fun (o, p, k) =>
    let q := p.mapRoot fun _ => .var o
    let whole := q matches .var _
    let isBorrowVar := pd (.var o) matches .ref _
    (q, if whole && isBorrowVar && (k == .read || k == .assign) then 2
      else if whole && moved.any (· == .var o) then 2
      else if k == .borrow || k == .assign then 1
      else 0)
  let wholeUses : List (Place × PKind) := occs.map fun (o, p, k) => (p.mapRoot fun _ => .var o, k)
  -- K1(c): maximal places
  let caps₀ := uses.foldl (fun caps (q, _) =>
    let hasPrefix := uses.any fun (q', _) => placePrefix q' q && !(placeEq q' q)
    if !hasPrefix && !(caps.any fun (c, _) => placeEq c q) then
      caps ++ [(q, (uses.filter fun (p, _) => placePrefix q p).foldl (fun m (_, k) => max m k) 0)]
    else caps) []
  -- K1(d): a moved place that is a strict prefix of captures is captured whole, by move
  let caps₁ := moved.foldl (fun caps m =>
    if caps.any (fun (c, _) => placePrefix m c && !(placeEq m c)) then
      (caps.filter fun (c, _) => !placePrefix m c) ++ [(m, 2)]
    else caps) caps₀
  -- K1(e): a capture some arm moves out whole is moved
  let caps₂ := caps₁.map fun (q, k) => if moved.any (placeEq · q) then (q, 2) else (q, k)
  -- K1(f): a proof is never taken by `&`
  let caps₃ := caps₂.map fun (q, k) => if k != 1 then (q, k) else if pd q matches .prop then (q, 0) else (q, k)
  -- K1(g): granularity
  let out := splitLoop Γ pd moved uses wholeUses fuel caps₃ []
  -- `blockEntry`'s order (`blockCapOrder`, main's capture sort): oldest binding first, then shorter
  -- paths, then by path
  let sorted := (blockCapOrder out.toArray).toList
  (mv, sorted)

end BlockCaps

end Ochr.Meaning
