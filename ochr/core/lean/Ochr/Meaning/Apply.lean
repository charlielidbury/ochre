import Ochr.Meaning.SState

/-!
# Applying and building function meanings (docs/18 Def. "reference run": every call applies
the callee's meaning)

A function value means `el0` of a Π-carrier (`Pi.lean`). To apply it the reference run needs
the Π's shape: its parameters (`PiParam`) and output (`PiOut`), read off the callee's Π-type by
running its parameter types and codomain. `applyTele` walks the telescope, decoding each
argument at its parameter type, and returns the output; `mkTele` builds a carrier element from
a function on meanings (a body's run at every argument), `none` where that function is
undefined or ill-typed at some argument: the carrier holds total good functions only, so a
closure whose body goes wrong somewhere, or whose backward function is not injective, means
`err`. Decoding is classical, by the tag (`TyM.dec0`).
-/

namespace Ochr.Meaning

open Classical

/-- Decode a meaning as an element of a level-0 carrier. -/
noncomputable def TyM.dec0 : (T : TyM) → Sem → Option T.el0
  | .ty0 A, s => s.as A
  | .prop P, .proof => if h : P then some ⟨h⟩ else none
  | _, _ => none

theorem TyM.dec0_enc0 (T : TyM) (a : T.el0) : T.dec0 (T.enc0 a) = some a := by
  sorry

/-- Decode a meaning as an element of a level-1 carrier. -/
noncomputable def TyM.dec1 : (T : TyM) → Sem → Option T.el1
  | .ty1 A, .el1 B b => if h : B = A then some (h ▸ b) else none
  | .univ 0, .ty (.prop P) => some ⟨P⟩
  | .univ 1, .ty (.ty0 A) => some A
  | .ty0 A, s => (s.as A).map ULift.up
  | .prop P, s => ((TyM.prop P).dec0 s).map ULift.up
  | _, _ => none

/-- The type of accumulated final contents after a parameter (`piCar0`'s accumulator step). -/
abbrev extFin (b : Bool) (Fin T : Type) : Type := match b with | true => Fin × T | false => Fin

/-- Read the accumulated final contents as a list of meanings, in parameter order. -/
def extRead (b : Bool) (Fin T : Type) (readFin : Fin → List Sem) (enc : T → Sem) :
    extFin b Fin T → List Sem :=
  match b with
  | true => fun x => readFin x.1 ++ [enc x.2]
  | false => readFin

/-- Build the accumulated final contents from a list of meanings in parameter order, consuming
it from the front; the rest of the list is returned. -/
def extMk (b : Bool) (Fin T : Type) (mkFin : List Sem → Option (Fin × List Sem)) (dec : Sem → Option T) :
    List Sem → Option (extFin b Fin T × List Sem) :=
  match b with
  | true => fun fs => do
    let (x, rest) ← mkFin fs
    match rest with
    | t :: rest' => (dec t).map fun y => ((x, y), rest')
    | [] => none
  | false => mkFin

/-- The result of applying a level-0 Π: for a data codomain the result and the final contents
of the borrow parameters, in parameter order; for a returned borrow the forward value and the
backward function from the value the caller leaves in it to the final contents. -/
inductive AppResult : Type 3 where
  | data (result : Sem) (finals : List Sem)
  | ref (U : TyM) (fwd : U.el0) (back : U.el0 → List Sem)

/-- Apply a level-0 Π-carrier element to arguments, walking the telescope; `none` if an argument
is not of its parameter type or their number is wrong. -/
noncomputable def applyTele : (ps : List PiParam) → (acc : List Sem) → (Fin : Type) →
    (Fin → List Sem) → (out : PiOut) → piCar0 ps acc Fin out → List Sem → Option AppResult
  | [], acc, _, readFin, .data B, r, [] => some (.data ((B acc).enc0 r.1) (readFin r.2))
  | [], acc, _, readFin, .ref U, r, [] => some (.ref (U acc) r.val.1 fun v => readFin (r.val.2 v))
  | p :: ps, acc, Fin, readFin, out, f, a :: as =>
    match (p.dom acc).dec0 a with
    | some x =>
      applyTele ps (acc ++ [(p.dom acc).enc0 x]) (extFin p.isRef Fin (p.dom acc).el0)
        (extRead p.isRef Fin (p.dom acc).el0 readFin (p.dom acc).enc0) out (f x) as
    | none => none
  | _, _, _, _, _, _, _ => none

/-- What a body's run gives at a tuple of arguments: the result and the final contents of the
borrow parameters as functions of the future, and, for a returned borrow, its label (the future
at that label is what the caller leaves in it). -/
structure BodyOut : Type 3 where
  result : SVal
  finals : List SVal
  retLabel : Option Nat := none

/-- The constant future: what is read where nothing depends on the future. -/
def noFuture : Future := fun _ => .err

/-- The leaf of `mkTele` for a data codomain: the result decoded at `B acc`, the final contents
built from the body's finals, all read under the constant future (every borrow of the frame
has ended when the body returns). -/
noncomputable def mkLeafData (acc : List Sem) (Fin : Type) (mkFin : List Sem → Option (Fin × List Sem))
    (B : List Sem → TyM) (o : BodyOut) : Option ((B acc).el0 × Fin) :=
  match (B acc).dec0 (o.result noFuture), mkFin (o.finals.map (· noFuture)) with
  | some r, some (fin, []) => some (r, fin)
  | _, _ => none

/-- The backward function of a borrow-returning body at the value `v` the caller leaves in the
returned borrow: the finals read in the future that fixes the returned label to `v`. -/
noncomputable def mkBackAt (Fin : Type) (mkFin : List Sem → Option (Fin × List Sem)) (U : TyM)
    (o : BodyOut) (k : Nat) (v : U.el0) : Option Fin :=
  match mkFin (o.finals.map (· (noFuture.upd k (U.enc0 v)))) with
  | some (fin, []) => some fin
  | _ => none

/-- The leaf of `mkTele` for a returned borrow: the forward value and the backward function,
which must be total and injective (`Back`). -/
noncomputable def mkLeafRef (acc : List Sem) (Fin : Type) (mkFin : List Sem → Option (Fin × List Sem))
    (U : List Sem → TyM) (o : BodyOut) : Option (Back Fin (U acc).el0) :=
  match o.retLabel, (U acc).dec0 (o.result noFuture) with
  | some k, some fwd =>
    if h : ∀ v, (mkBackAt Fin mkFin (U acc) o k v).isSome then
      let back := fun v => (mkBackAt Fin mkFin (U acc) o k v).get (h v)
      if hi : ∀ v w, back v = back w → v = w then some ⟨(fwd, back), hi⟩ else none
    else none
  | _, _ => none

/-- Build a level-0 Π-carrier element from a function on meanings (a body's run), walking the
telescope and deciding classically at each argument; `none` if the body is undefined somewhere,
its result or a final content is not of its type, or (a returned borrow) the backward function
is not injective. -/
noncomputable def mkTele : (ps : List PiParam) → (acc : List Sem) → (Fin : Type) →
    (List Sem → Option (Fin × List Sem)) → (out : PiOut) → (List Sem → Option BodyOut) →
    Option (piCar0 ps acc Fin out)
  | [], acc, Fin, mkFin, .data B, g => (g acc).bind (mkLeafData acc Fin mkFin B)
  | [], acc, Fin, mkFin, .ref U, g => (g acc).bind (mkLeafRef acc Fin mkFin U)
  | p :: ps, acc, Fin, mkFin, out, g =>
    if h : ∀ x : (p.dom acc).el0,
        (mkTele ps (acc ++ [(p.dom acc).enc0 x]) (extFin p.isRef Fin (p.dom acc).el0)
          (extMk p.isRef Fin (p.dom acc).el0 mkFin (p.dom acc).dec0) out g).isSome then
      some fun x => (mkTele ps (acc ++ [(p.dom acc).enc0 x]) (extFin p.isRef Fin (p.dom acc).el0)
          (extMk p.isRef Fin (p.dom acc).el0 mkFin (p.dom acc).dec0) out g).get (h x)
    else none

end Ochr.Meaning
