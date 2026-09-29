import Ochr.Fuzz.Gen

/-! # Fuzzer: the recursive term generator (see `Gen.lean` for the productions' purpose) -/

namespace Ochr.Fuzz
open Ochr.Surface

mutual
partial def gen (Γ : Ctx) (T : GTy) (f : Nat) : Gen STerm := do
  if f == 0 then return ← leaf Γ T
  let cs := (← calleesOf Γ).filter (·.ret == T)
  let ms ← matchPlaces Γ T
  let fls := (← proofVars Γ).filter fun (_, P) => P matches .fls
  let h := f / 2
  let specific : List (Nat × Gen STerm) := match T with
    | .nat => [(1, do pure (.app "S" [← gen Γ .nat (f - 1)]))]
    | .unit => [(4, genAssign Γ f)]
    | .ind n => [(2, genCtor Γ n f)]
    | .prop => [(2, do pure (.app "Id" [.ident "Nat", ← gen Γ .nat h, ← gen Γ .nat (f / 3)])),
                (1, do pure (.app "Id" [.ident "Unit", ← gen Γ .unit h, ← gen Γ .unit (f / 3)])),
                (2, do pure (.app "Eq" [.ident "Nat", ← gen Γ .nat h, ← gen Γ .nat h])),
                (3, do pure (.seq (← gen Γ .unit h) (← gen Γ .prop h))),
                (1, do pure (.and (← gen Γ .prop h) (← gen Γ .prop h))),
                (2, genIdEff Γ h)]
    | .pf _ => [(3, do pure (.seq (← gen Γ .unit h) (← gen Γ T h)))]
    | .fam _ => [(3, do pure (.seq (← gen Γ .unit h) (← gen Γ T h)))]
    | .fn ps r => [(4, genLambda Γ ps r h)]
    | .ref _ => []
  weighted ([(2, leaf Γ T), (3, genLet Γ T f), (3, genSeq Γ T f),
             (if ms.isEmpty then 0 else 5, genMatch Γ T f ms),
             (if cs.isEmpty then 0 else 4, genCall Γ f cs),
             -- v2.x: a match with no arms on a proof of False, at any type (annotated)
             (if fls.isEmpty then 0 else 2, do
                let (v, _) ← pick fls
                pure (.ascribe (.matchGen v.place []) T.surface))] ++ specific)

partial def leaf (Γ : Ctx) (T : GTy) : Gen STerm := do
  match T with
  | .nat => weighted [(3, do pure (natLit (← rand 3))),
                      (6, do pure ((← readPlace? Γ .nat).getD (natLit 0))),
                      (1, do pure (.app "S" [← leaf Γ .nat]))]
  | .unit => weighted [(2, pure .unitLit), (3, genAssign Γ 0)]
  | .ind n => do
    if ← chance 50 then
      if let some p ← readPlace? Γ (.ind n) then return p
    genCtor Γ n 0
  | .ref t => do
    match ← borrowOf? Γ t [] with
    | some (b, _) => pure b
    | none => pure (.amp (.ident "nowhere"))
  | .prop => weighted [(3, pure .top), (3, do pure (.app "Eq" [.ident "Nat", ← leaf Γ .nat, ← leaf Γ .nat])),
                       (1, do pure ((← readPlace? Γ .prop).getD .top)),
                       (1, pure (.ident "False")), (1, pure (.and .top .top)),
                       (if Γ.inds.contains "Or" then 1 else 0, pure (PT.or.surface)),
                       (if Γ.lib.any (·.name == "PropIf") then 1 else 0, do pure (.call (.ident "PropIf") [← leaf Γ .nat]))]
  | .pf P => do
    let vs := (← proofVars Γ).filter (·.2 == P)
    if !vs.isEmpty && (← chance 50) then
      let (v, _) ← pick vs
      return v.place
    leafPf Γ P
  | .fam a => pure (.call (.ident "V") [a])
  | .fn ps r => genLambda Γ ps r 0

/-- A proof of `P` built from constructors (v2.x: `refl` is `I`, `⟨h, k⟩` is `Intro`, and a
constructor of a Prop inductive is a proof, D42); `False` and an opaque statement only from
a variable (`refl` if there is none: the case is then ill-typed, and uninteresting). -/
partial def leafPf (Γ : Ctx) (P : PT) : Gen STerm := do
  match P with
  | .top => pure (.ident "refl")
  | .and a b => pure (.andI (← leaf Γ (.pf a)) (← leaf Γ (.pf b)))
  | .or => do
    let c ← pick ["Inl", "Inr"]
    pure (.ctorP c [.top, .top] [← leaf Γ .proof])
  | .ex => pure (.call (.ident "Wit") [← leaf Γ .nat, ← leaf Γ .proof])
  | _ =>
    let vs := (← proofVars Γ).filter (·.2 == P)
    if vs.isEmpty then return .ident "refl"
    pure (← pick vs).1.place

partial def genCtor (Γ : Ctx) (n : String) (f : Nat) : Gen STerm := do
  let cs := ctorsOf n
  if cs.isEmpty then return .ident "Z"
  let (c, fs) ← pick cs
  if fs.isEmpty then return .ident c
  let args ← fs.mapM fun (_, T) => if f == 0 then leaf Γ T else gen Γ T (f / 2)
  pure (.call (.ident c) args)

/-- `p := t`, the right-hand side first (it is evaluated first). -/
partial def genAssign (Γ : Ctx) (f : Nat) : Gen STerm := do
  let mut ts := []
  for T in [GTy.nat, .ind "L", .ind "Box", .ind "B2"] do
    if ← hasPlace Γ T then ts := ts ++ [T]
  if ts.isEmpty then return .unitLit
  let T ← pick ts
  let rhs ← if f == 0 then leaf Γ T else gen Γ T (f / 2)
  let ps ← placesOf Γ T
  if ps.isEmpty then return .unitLit
  let v ← pick ps
  touch Γ v.proot true
  pure (.assign v.place rhs)

partial def genSeq (Γ : Ctx) (T : GTy) (f : Nat) : Gen STerm := do
  let h := f / 2
  let eff ← weighted [(5, gen Γ .unit h),
    (3, do
      let cs ← calleesOf Γ
      let cs ← cs.filterM fun c => c.ps.allM fun p => canGen Γ p
      if cs.isEmpty then gen Γ .unit h else genCall Γ h cs)]
  pure (.seq eff (← gen Γ T h))

partial def genCall (Γ : Ctx) (f : Nat) (cs : List Callee) : Gen STerm := do
  let c ← pick cs
  let mut roots : List String := []
  let mut args : Array STerm := #[]
  for p in c.ps do
    if !(← canGen Γ p) && p.isProof then return ← leaf Γ c.ret
    match p with
    | .ref t =>
      match ← borrowOf? Γ t roots with
      | some (b, r) => roots := r :: roots; args := args.push b
      | none => return ← leaf Γ c.ret
    | .nat =>
      let a ← if f ≤ 1 then leaf Γ .nat else weighted [(3, leaf Γ .nat), (1, gen Γ .nat (f / 3))]
      args := args.push a
    | t => args := args.push (← gen Γ t (f / 3))
  pure (.call c.head args.toList)

partial def genLambda (Γ : Ctx) (ps : List GTy) (r : GTy) (f : Nat) : Gen STerm := do
  let Γl := lamCtx Γ
  let names ← ps.mapM fun _ => freshName "y"
  let Γl := (names.zip ps).foldl (fun Γ (y, p) => match p with
    | .ref _ => Γ.push { name := y, ty := p, kind := .bvar, root := y, param := true }
    | _ => Γ.push { name := y, ty := p, kind := .owned, root := y, param := true }) Γl
  let r ← match r with
    | .fam _ => pure (GTy.fam (← famArg Γl))
    | _ => pure r
  let d ← saveDead
  let body ← gen Γl r f
  setDead d
  pure (.fix "_" (names.zip (ps.map GTy.surface)) r.surface none body)

/-- `Id Unit (p := a) (p := b)`: an effect equation about one place (for a returned
borrow `*r`, the footprint is every owner of its hole: D18). -/
partial def genIdEff (Γ : Ctx) (f : Nat) : Gen STerm := do
  let all ← placesOf Γ .nat
  let ps := all.filter (·.kind == .bvar)
  let ps := if ps.isEmpty then all else ps
  if ps.isEmpty then return .top
  let v ← pick ps
  let a ← gen Γ .nat (f / 2)
  let b ← gen Γ .nat (f / 2)
  pure (.app "Id" [.ident "Unit", .assign v.place a, .assign v.place b])

partial def genLet (Γ : Ctx) (T : GTy) (f : Nat) : Gen STerm := do
  let h := f / 2
  let x ← freshName "a"
  let fam := Γ.lib.any (·.name == "V")
  let ind (n : String) : Nat := if Γ.inds.contains n then 1 else 0
  let fr ← pick ([GTy.unit, .nat, .prop, .proof, .pf (.and .top .top), .ref .nat] ++ (if fam then [GTy.fam (.num 0), .fam (.num 0)] else []))
  let T' ← weighted [(4, pure GTy.nat), (if ← hasPlace Γ .nat then 4 else 0, pure (GTy.ref .nat)),
    (ind "L", pure (GTy.ind "L")), (ind "B2", pure (GTy.ind "B2")), (ind "Box", pure (GTy.ind "Box")),
    (if (← hasPlace Γ (.ind "L")) then 1 else 0, pure (GTy.ref (.ind "L"))),
    (2, pure GTy.prop), (2, pure GTy.proof), (2, pure (GTy.fn [.ref .nat] fr)),
    (1, pure (GTy.fn [.nat, .pf (.and .top .top)] fr)), (2, pure (GTy.pf (.and .top .top))),
    (ind "Or", pure (GTy.pf .or)), (ind "ExN", pure (GTy.pf .ex)),
    (if fam then 1 else 0, pure (GTy.fam (.num 0)))]
  let e ← gen Γ T' h
  let annot ← match T' with
    | .nat | .prop | .ind _ | .pf _ => do pure (if ← chance 25 then some T'.surface else none)
    | _ => pure none
  let v : GVar := match T' with
    | .ref _ => { name := x, ty := T', kind := .bvar, root := borrowRoot Γ x e }
    | .fn .. => { name := x, ty := T', kind := .fnv, root := x }
    | _ => { name := x, ty := T', kind := .owned, root := x }
  pure (.letIn x annot e (← gen (Γ.push v) T h))

partial def genMatch (Γ : Ctx) (T : GTy) (f : Nat) (ms : List GVar) : Gen STerm := do
  let v ← pick ms
  touch Γ v.proot false
  let some D := v.placeTy | leaf Γ T
  let h := f / 2 + f % 2
  let d0 ← saveDead
  let mut dead := d0
  let mut arms : Array (String × List String × STerm) := #[]
  let shapes : List (String × List (String × GTy)) := match D with
    | .nat => [("Z", []), ("S", [("1", .nat)])]
    | .ind n => ctorsOf n
    | .pf P => pfShapes P     -- v2.x: a match on a proof is by its type (D45)
    | _ => []
  if shapes.isEmpty then
    -- no constructors (False, or an opaque statement): no arms, at any type, annotated
    return .ascribe (.matchGen v.place []) T.surface
  for (c, fs) in shapes do
    setDead d0
    let mut Γa := Γ
    let mut vs := #[]
    for (_, FT) in fs do
      if ← chance 20 then vs := vs.push "_"
      else
        let y ← freshName "p"
        vs := vs.push y
        Γa := Γa.push { name := y, ty := FT, kind := .alias, root := v.proot }
    let body ← gen Γa T h
    arms := arms.push (c, vs.toList, body)
    dead := dead ++ (← saveDead).filter (!dead.contains ·)
  setDead dead
  let m := STerm.matchGen v.place arms.toList
  match T with
  | .nat | .unit | .ind _ | .prop | .pf _ =>
    if ← chance 20 then
      let x ← freshName "a"
      return .letIn x (some T.surface) m (.ident x)
    pure m
  | _ => pure m
end

end Ochr.Fuzz
