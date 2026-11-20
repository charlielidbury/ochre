import Ochr.Meaning.SState

/-!
# Applying and building function meanings along their codes (docs/18 Def. "reference run":
every call applies the callee's meaning; docs/31 D59)

A function value means an element of its type's carrier, and its type's code is a telescope code
(`Tel`, `Sem.lean`). To apply a function the reference run walks the code: each argument is decoded
at its parameter's code, the function applied to it, and the rest of the telescope is the code `k`
gives at that element; the result is read at the code the telescope reaches, so a call's result
keeps its whole type. `mkTelL` builds a carrier element from a function on meanings (a body's run
at every argument), `none` where that function is undefined or ill-typed at some argument: the
carrier holds total good functions only, so a closure whose body goes wrong somewhere, or whose
backward function is not injective, means `err`.

## One construction, three levels (`Lvl`)

A function type at `Type₀` has its carrier in `Type`, one at `Type₁` in `Type 1`, one at `Type₂` in
`Type 2` (`Swap (V : Type) (a : &V) (b : &V) : Unit` is in `Type₁` and borrows). The construction
reads its level only through `Lvl`: the code family, its encoding and decoding, how a type is read
at the level (lower levels lifted), how a code is read back as a type, the function-type code, and
the tag of the level's elements. `lvl0`, `lvl1`, `lvl2` are the three levels the bounded model
supports (D2).
-/

namespace Ochr.Meaning

open Classical

universe u

/-- Read a meaning as an element of a level-1 Lean type, by its tag (as `Sem.as` at level 0). -/
noncomputable def Sem.as1 (A : Type 1) : Sem → Option A
  | .el1 B b => if h : B = A then some (h ▸ b) else none
  | _ => none

/-- Read a meaning as an element of a level-2 Lean type, by its tag. -/
noncomputable def Sem.as2 (A : Type 2) : Sem → Option A
  | .el2 B b => if h : B = A then some (h ▸ b) else none
  | _ => none

/-- A carrier level. -/
structure Lvl : Type (max 3 (u + 2)) where
  /-- How a data element is read (docs/31 D61): the data model's, which the encoding reads. -/
  read : DataRead
  Code : Type u → Type (u + 1)
  enc : {A : Type u} → Code A → A → Sem
  dec : {A : Type u} → Code A → Sem → Option A
  codeOf : TyM → (A : Type u) × Code A
  toTy : {A : Type u} → Code A → TyM
  pi : (C : Type u) → Tel Code PUnit C → Code C
  pack : (A : Type u) → A → Sem
  unpack : (A : Type u) → Sem → Option A

noncomputable abbrev lvl0 (R : DataRead) : Lvl.{0} :=
  ⟨R, Code0, Code0.enc R, Code0.dec R, TyM.code0, fun c => .t0 _ c, Code0.pi, .el0, Sem.as⟩

/-- Level 1: `Type₁`, the universes `Prop` and `Type₀`, lower levels lifted. -/
noncomputable abbrev lvl1 (R : DataRead) : Lvl.{1} :=
  ⟨R, Code1, Code1.enc R, Code1.dec R, TyM.code1, TyM.of1, Code1.pi, .el1, Sem.as1⟩

/-- Level 2: `Type₂`, the universe `Type₁`, lower levels lifted. -/
noncomputable abbrev lvl2 (R : DataRead) : Lvl.{2} :=
  ⟨R, Code2, Code2.enc R, Code2.dec R, TyM.code2, TyM.of2, Code2.pi, .el2, Sem.as2⟩

/-- A level is lawful: decoding inverts encoding both ways, a function-type code encodes its
elements by their tag, which unpacking reads back, and a function-type code read back as a type
has exactly those encodings as members. -/
structure Lvl.Lawful (L : Lvl.{u}) : Prop where
  enc_of_dec : ∀ {A : Type u} (c : L.Code A) {s : Sem} {a : A}, L.dec c s = some a → L.enc c a = s
  dec_enc : ∀ {A : Type u} (c : L.Code A) (a : A), L.dec c (L.enc c a) = some a
  enc_pi : ∀ (C : Type u) (t : Tel L.Code PUnit C) (f : C), L.enc (L.pi C t) f = L.pack C f
  unpack_pack : ∀ (A : Type u) (a : A), L.unpack A (L.pack A a) = some a
  mem_pi : ∀ (C : Type u) (t : Tel L.Code PUnit C) (s : Sem), (s ∈ₛ[L.read] L.toTy (L.pi C t)) ↔ ∃ f, L.enc (L.pi C t) f = s

theorem lvl0_lawful (R : DataRead) : (lvl0 R).Lawful where
  enc_of_dec c _ _ h := Code0.enc_of_dec R c h
  dec_enc c a := Code0.dec_enc R c a
  enc_pi _ _ _ := rfl
  unpack_pack A a := by
    show (if h : A = A then some (h ▸ a) else none) = some a
    rw [dif_pos rfl]
  mem_pi _ _ _ := Iff.rfl

theorem lvl1_lawful (R : DataRead) : (lvl1 R).Lawful where
  enc_of_dec c _ _ h := Code1.enc_of_dec R c h
  dec_enc c a := Code1.dec_enc R c a
  enc_pi _ _ _ := rfl
  unpack_pack A a := by
    show (if h : A = A then some (h ▸ a) else none) = some a
    rw [dif_pos rfl]
  mem_pi _ _ _ := Iff.rfl

theorem lvl2_lawful (R : DataRead) : (lvl2 R).Lawful where
  enc_of_dec c _ _ h := Code2.enc_of_dec R c h
  dec_enc c a := Code2.dec_enc R c a
  enc_pi _ _ _ := rfl
  unpack_pack A a := by
    show (if h : A = A then some (h ▸ a) else none) = some a
    rw [dif_pos rfl]
  mem_pi _ _ _ := Iff.rfl

/-- What a body's run gives at a tuple of arguments: the result (at the run's future), the final
contents of the borrow parameters as functions of the future (they may depend on a returned
borrow's label), and, for a returned borrow, its label (the future at that label is what the
caller leaves in it). -/
structure BodyOut : Type 3 where
  result : Sem
  finals : List SVal
  retLabel : Option Nat := none

/-- The constant future: what is read where nothing depends on the future. -/
def noFuture : Future := fun _ => .err

section
variable (L : Lvl.{u})

/-- Read the accumulated final contents as a list of meanings, in parameter order. -/
def extReadL (b : Bool) (Fin T : Type u) (readFin : Fin → List Sem) (enc : T → Sem) :
    extFin b Fin T → List Sem :=
  match b with
  | true => fun x => readFin x.1 ++ [enc x.2]
  | false => readFin

/-- Build the accumulated final contents from meanings in parameter order, consuming them from
the front; the rest of the list is returned. -/
def extMkL (b : Bool) (Fin T : Type u) (mkFin : List Sem → Option (Fin × List Sem)) (dec : Sem → Option T) :
    List Sem → Option (extFin b Fin T × List Sem) :=
  match b with
  | true => fun fs => do
    let (x, rest) ← mkFin fs
    match rest with
    | t :: rest' => (dec t).map fun y => ((x, y), rest')
    | [] => none
  | false => mkFin

/-- What a call gives back: for a data codomain the result, its type (the code the telescope
reached at the arguments), and the final contents of the borrow parameters in parameter order; for
a returned borrow `&U` its code, the forward value, and the backward function from the value the
caller leaves in it to the final contents. -/
inductive AppResultL : Type (max 3 (u + 1)) where
  | data (result : Sem) (T : TyM) (finals : List Sem)
  | ref (U : Type u) (c : L.Code U) (fwd : U) (back : U → List Sem)

/-- Apply an element of a telescope code's carrier to arguments, walking the code; `none` if an
argument is not of its parameter's type or their number is wrong. -/
noncomputable def applyTelL : {Fin C : Type u} → Tel L.Code Fin C → (Fin → List Sem) → C → List Sem →
    Option (AppResultL L)
  | _, _, .dat _ _ c, readFin, r, [] => some (.data (L.enc c r.1) (L.toTy c) (readFin r.2))
  | _, _, .ref _ U c, readFin, r, [] => some (.ref U c r.val.1 fun v => readFin (r.val.2 v))
  | _, _, .param Fin isRef A c _ k, readFin, f, a :: as =>
    match L.dec c a with
    | some x => applyTelL (k x) (extReadL isRef Fin A readFin (L.enc c)) (f x) as
    | none => none
  | _, _, .dat .., _, _, _ :: _ => none
  | _, _, .ref .., _, _, _ :: _ => none
  | _, _, .param .., _, _, [] => none

/-- The leaf of `mkTelL` for a data codomain: the result decoded at the codomain's code, the
final contents built from the body's finals, all read under the future `φ`. -/
noncomputable def mkLeafDataL (φ : Future) (Fin : Type u) (mkFin : List Sem → Option (Fin × List Sem))
    {B : Type u} (c : L.Code B) (o : BodyOut) : Option (B × Fin) :=
  match L.dec c o.result, mkFin (o.finals.map (· φ)) with
  | some r, some (fin, []) => some (r, fin)
  | _, _ => none

/-- The backward function of a borrow-returning body at the value `v` the caller leaves in the
returned borrow: the finals read in the future that fixes the returned label to `v`. -/
noncomputable def mkBackAtL (φ : Future) (Fin : Type u) (mkFin : List Sem → Option (Fin × List Sem))
    {U : Type u} (c : L.Code U) (o : BodyOut) (k : Nat) (v : U) : Option Fin :=
  match mkFin (o.finals.map (· (φ.upd k (L.enc c v)))) with
  | some (fin, []) => some fin
  | _ => none

/-- The leaf of `mkTelL` for a returned borrow: the forward value and the backward function,
which must be total and injective (`Back`). -/
noncomputable def mkLeafRefL (φ : Future) (Fin : Type u) (mkFin : List Sem → Option (Fin × List Sem))
    {U : Type u} (c : L.Code U) (o : BodyOut) : Option (Back Fin U) :=
  match o.retLabel, L.dec c o.result with
  | some k, some fwd =>
    if h : ∀ v, (mkBackAtL L φ Fin mkFin c o k v).isSome then
      let back := fun v => (mkBackAtL L φ Fin mkFin c o k v).get (h v)
      if hi : ∀ v w, back v = back w → v = w then some ⟨(fwd, back), hi⟩ else none
    else none
  | _, _ => none

/-- Build an element of a telescope code's carrier from a function on meanings (a body's run at
the arguments `acc` so far extended), walking the code and deciding classically at each argument;
`none` if the body is undefined somewhere, its result or a final content is not of its type, or
(a returned borrow) the backward function is not injective. -/
noncomputable def mkTelL (φ : Future) : {Fin C : Type u} → Tel L.Code Fin C → List Sem →
    (List Sem → Option (Fin × List Sem)) → (List Sem → Option BodyOut) → Option C
  | _, _, .dat Fin _ c, acc, mkFin, g => (g acc).bind (mkLeafDataL L φ Fin mkFin c)
  | _, _, .ref Fin _ c, acc, mkFin, g => (g acc).bind (mkLeafRefL L φ Fin mkFin c)
  | _, _, .param Fin isRef A c _ k, acc, mkFin, g =>
    if h : ∀ x : A, (mkTelL φ (k x) (acc ++ [L.enc c x]) (extMkL isRef Fin A mkFin (L.dec c)) g).isSome then
      some fun x => (mkTelL φ (k x) (acc ++ [L.enc c x]) (extMkL isRef Fin A mkFin (L.dec c)) g).get (h x)
    else none

/-- `mkTelL` for a stage of a recursion (`Run.lean`'s `.fix`): where the body is undefined, the
element is an arbitrary element of the leaf type, when it has one. A stage of a guarded recursion
is defined only below its rank, and the carrier holds total functions only, so built strictly every
stage would be `err` and so would every recursive closure (docs/31 D60); a call that decreases in
rank never reads a stage where it was filled. -/
noncomputable def mkTelFillL (φ : Future) : {Fin C : Type u} → Tel L.Code Fin C → List Sem →
    (List Sem → Option (Fin × List Sem)) → (List Sem → Option BodyOut) → Option C
  | _, _, .dat Fin B c, acc, mkFin, g =>
    match (g acc).bind (mkLeafDataL L φ Fin mkFin c) with
    | some r => some r
    | none => if h : Nonempty (B × Fin) then some (Classical.choice h) else none
  | _, _, .ref Fin U c, acc, mkFin, g =>
    match (g acc).bind (mkLeafRefL L φ Fin mkFin c) with
    | some r => some r
    | none => if h : Nonempty (Back Fin U) then some (Classical.choice h) else none
  | _, _, .param Fin isRef A c _ k, acc, mkFin, g =>
    if h : ∀ x : A, (mkTelFillL φ (k x) (acc ++ [L.enc c x]) (extMkL isRef Fin A mkFin (L.dec c)) g).isSome then
      some fun x => (mkTelFillL φ (k x) (acc ++ [L.enc c x]) (extMkL isRef Fin A mkFin (L.dec c)) g).get (h x)
    else none

/-- **The telescope code of a function type** from its description (the reference run's reading
of the term: each domain, and the codomain, at the arguments so far, `Pi.lean`): each parameter's
code is its domain's at the earlier arguments, read at the level, and the rest is built at each of
its elements, encoded as a meaning. -/
def telL : (ds : List PiDom) → (acc : List Sem) → (Fin : Type u) → (out : PiCod) →
    (C : Type u) × Tel L.Code Fin C
  | [], acc, Fin, out =>
    match out.isRef with
    | false => ⟨(L.codeOf (out.cod acc)).1 × Fin, .dat Fin _ (L.codeOf (out.cod acc)).2⟩
    | true => ⟨Back Fin (L.codeOf (out.cod acc)).1, .ref Fin _ (L.codeOf (out.cod acc)).2⟩
  | p :: ps, acc, Fin, out =>
    ⟨(a : (L.codeOf (p.dom acc)).1) →
        (telL ps (acc ++ [L.enc (L.codeOf (p.dom acc)).2 a]) (extFin p.isRef Fin (L.codeOf (p.dom acc)).1) out).1,
      .param Fin p.isRef _ (L.codeOf (p.dom acc)).2 _ fun a =>
        (telL ps (acc ++ [L.enc (L.codeOf (p.dom acc)).2 a]) (extFin p.isRef Fin (L.codeOf (p.dom acc)).1) out).2⟩

/-- The next parameter of a telescope code after the given arguments (decoded at their
parameters' codes): whether it is a borrow, and its (content) code; `none` past the end or at an
argument of the wrong type. -/
noncomputable def telParamL : {Fin C : Type u} → Tel L.Code Fin C → List Sem → Option (Bool × TyM)
  | _, _, .param _ isRef _ c _ _, [] => some (isRef, L.toTy c)
  | _, _, .param _ _ _ c _ k, a :: as =>
    match L.dec c a with
    | some x => telParamL (k x) as
    | none => none
  | _, _, .dat .., _ => none
  | _, _, .ref .., _ => none

/-- The codomain a telescope code reaches at the arguments: whether it is a returned borrow, and
its (content) code; `none` at the wrong number of arguments or an argument of the wrong type. -/
noncomputable def telCodL : {Fin C : Type u} → Tel L.Code Fin C → List Sem → Option (Bool × TyM)
  | _, _, .dat _ _ c, [] => some (false, L.toTy c)
  | _, _, .ref _ _ c, [] => some (true, L.toTy c)
  | _, _, .param _ _ _ c _ k, a :: as =>
    match L.dec c a with
    | some x => telCodL (k x) as
    | none => none
  | _, _, .dat .., _ :: _ => none
  | _, _, .ref .., _ :: _ => none
  | _, _, .param .., [] => none

/-- The meaning of a function type with telescope code `t`, at level `L`. -/
def piTyL {C : Type u} (t : Tel L.Code PUnit C) : TyM := L.toTy (L.pi C t)

/-- The meaning of a closure at level `L` from its body's run at every argument (`g`): the element
`mkTelL` builds along the type's code, tagged at the code's carrier; `err` where it fails. -/
noncomputable def closureL (φ : Future) {C : Type u} (t : Tel L.Code PUnit C) (g : List Sem → Option BodyOut) : Sem :=
  match mkTelL L φ t [] (fun fs => some (PUnit.unit, fs)) g with
  | some F => L.pack C F
  | none => .err

/-- The meaning of a recursion stage's closure: `mkTelFillL`'s element, tagged at the code's
carrier; `err` where even filling fails (an empty leaf type). -/
noncomputable def closureFillL (φ : Future) {C : Type u} (t : Tel L.Code PUnit C) (g : List Sem → Option BodyOut) : Sem :=
  match mkTelFillL L φ t [] (fun fs => some (PUnit.unit, fs)) g with
  | some F => L.pack C F
  | none => .err

/-- Apply a function meaning at level `L` along its type's telescope code: unpack it at the code's
carrier, then walk the code. -/
noncomputable def applyFnL {C : Type u} (t : Tel L.Code PUnit C) (F : Sem) (args : List Sem) :
    Option (AppResultL L) :=
  (L.unpack C F).bind fun F => applyTelL L t (fun _ => []) F args

/-- **A closure is a member of its own type, or `err`**: it is built in the carrier its type's code
is indexed by. -/
theorem closureL_mem (hL : L.Lawful) (φ : Future) {C : Type u} (t : Tel L.Code PUnit C)
    (g : List Sem → Option BodyOut) : (closureL L φ t g ∈ₛ[L.read] piTyL L t) ∨ closureL L φ t g = .err := by
  unfold closureL
  split
  · rename_i F _
    exact .inl ((hL.mem_pi C t _).2 ⟨F, hL.enc_pi C t F⟩)
  · exact .inr rfl

end

end Ochr.Meaning
