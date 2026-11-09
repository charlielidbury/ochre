import Ochr.Meaning.Apply

/-!
# Function meanings at every level (docs/31 D12: closures at their declared sort)

`Apply.lean` applies and builds functions at level 0: a closure in `Type₀` means `el0` of
`piCar0`. A function whose Π-type is in `Type₁` or `Type₂` has a parameter or codomain in a
higher universe. The polymorphic identity `id (A : Type) (x : A) : A` is in `Type₁`, as is
`Swap (V : Type) (a : &V) (b : &V) : Unit` from the suite. It must mean `el1`/`el2` of a level-1/2
carrier, which D12 leaves as `err`. This file is the construction, written once for every level.

## One construction, three levels (`Lvl`)

The level-0 code reads its level only through the carrier `TyM.el0`, its encoding `enc0` and
decoding `dec0`, the type meaning of a carrier (`TyM.ty0`) and the tag of its elements
(`Sem.el0`). `Lvl` packages exactly those, and `lvl0`, `lvl1`, `lvl2` are the three levels the
bounded model supports (D2). `piCarL`, `applyTeleL` and `mkTeleL` are `Pi.lean`'s `piCar0` and
`Apply.lean`'s `applyTele`/`mkTele` with the level as a parameter, clause for clause. They have
the same error cases (an argument not of its parameter type or a wrong number of arguments; a
body undefined or ill-typed at some argument; a final content not of its type) and the same
injectivity requirement on a returned borrow's backward function (`Back`). `applyTele1`,
`mkTele1`, `applyTele2`, `mkTele2` are the instances. At level 0 the carrier is `piCar0`
(`piCarL_lvl0`).

## Why not `Pi.lean`'s `piCar1`/`piCar2`

`piCar1`/`piCar2` have no final contents and a plain codomain. Their docstring says a type-level
function borrows nothing, but a polymorphic function can borrow its value parameters:
`Swap (V : Type) (a : &V) (b : &V) : Unit` is in `Type₁` and has two borrow parameters (D66 only
asks `V : Type₀`). Its meaning needs the parameters' final contents, and a polymorphic function
returning `&V` needs `Back`, exactly as at level 0. So the level-1/2 carrier is `piCarL lvl1`/
`piCarL lvl2`, with the final contents and the `PiOut` of level 0, lifted. The `.pi` clause's
`ty1 (piCar1 …)`/`ty2 (piCar2 …)` must become `lvl1.ty (piCarL lvl1 ps [] PUnit out)` (and level
2 alike) for a closure to be a member of its own type (the proposed wiring, in the report to the
spine).

## What is proved (no `sorry`)

* Both round trips at levels 1 and 2 (`TyM.dec1_enc1`, `dec2_enc2`; `enc1_of_dec1`,
  `enc2_of_dec2`), and the second at level 0 (`enc0_of_dec0`; the first is `Apply.lean`'s
  `dec0_enc0`). So each level is lawful (`Lvl.EncDec`), and `pack`/`unpack` round-trip.
* **Calling a built function runs its body** (`applyTeleL_mkTeleL`, and `_ref` for a returned
  borrow), at every lawful level: applying what `mkTeleL` built from `g` to arguments that fit
  the telescope (`ArgsFit`) gives `g`'s result there and its final contents (a returned borrow:
  the forward value, and the backward function reading the finals at the future that fixes the
  returned label). `applyFnL_closureL` is the same for a closure's meaning. This is what the call
  step lemma needs (`Steps/Call.lean`).
* A closure at a data sort is a member of its Π-type at that sort, or `err` (`closureAt_mem`).
* Sanity (`Apply1Sanity`): the level-1 carriers of `id`, `Swap` and a level-2 `F` are what they
  should be (`rfl`); `mkTele1` builds the polymorphic identity (`id_built`); and `id(Nat, 5)`
  is `5` (`id_call`).

## What the reference run uses

`piTyAt l` and `closureAt l` are the meaning of a Π-type and of a closure at the declared sort
`l` (`Decisions.piSort`): `piProp` and `⋆` at `Prop` (D12), and the level `l - 1` construction
above. `applyFnL L` unpacks a callee at its level and applies it. The `.pi` and `.fix` clauses
both read `piTyAt`, so a closure lies in its own type, and `callOf` dispatches on the callee's tag
(`el0`/`el1`/`el2`). The proposed wiring into `Run.lean` is the spine's to make.

## A gap in `el2` (reported)

Elements of the universe `Type₁` (`univ 2`) are `.ty (.ty1 A)`, and also `Prop` and `Type₀`
themselves, which `Sem` writes `.ty (.univ 0)` and `.ty (.univ 1)` (both have level 2,
`sortSucc`). `TyM.el2 (.univ 2)` is `Type 1` and `TyM.enc2` encodes its elements as
`.ty (.ty1 A)`, so the decoder below decodes only those. A level-2 function such as
`F (A : Type₁) : Type₁` applied to `Type₀` decodes its argument to `none`, and the call is
undefined. Covering it needs a level-2 carrier for `univ 2` with codes for `Prop` and `Type₀`
(`Pi.lean`). Level 1 has no such gap: the elements of `univ 1` (`Type₀`) are exactly
`.ty (.ty0 A)`, and those of `univ 0` exactly `.ty (.prop P)`.
-/

namespace Ochr.Meaning

open Classical

universe u

/-- Decode a meaning as an element of a level-2 carrier: a level-2 element by its tag, a type
value of `Type₁` (`univ 2`) as its level-1 carrier (only `.ty (.ty1 A)`, the image of `enc2`: the
gap in the module docstring), and every lower level through `dec1`, lifted. -/
noncomputable def TyM.dec2 : (T : TyM) → Sem → Option T.el2
  | .ty2 A, .el2 B b => if h : B = A then some (h ▸ b) else none
  | .ty2 _, _ => none
  | .univ 2, .ty (.ty1 A) => some A
  | .univ 2, _ => none
  | .ty1 A, s => ((TyM.ty1 A).dec1 s).map ULift.up
  | .univ 0, s => ((TyM.univ 0).dec1 s).map ULift.up
  | .univ 1, s => ((TyM.univ 1).dec1 s).map ULift.up
  | .univ (_ + 3), _ => none
  | .ty0 A, s => ((TyM.ty0 A).dec1 s).map ULift.up
  | .prop P, s => ((TyM.prop P).dec1 s).map ULift.up
  | .err, _ => none

/-- Decoding an encoded level-1 element gives it back. -/
theorem TyM.dec1_enc1 (T : TyM) (a : T.el1) : T.dec1 (T.enc1 a) = some a := by
  cases T with
  | ty1 A =>
    show (if h : A = A then some (h ▸ a) else none) = some a
    rw [dif_pos rfl]
  | univ l =>
    match l, a with
    | 0, _ => rfl
    | 1, _ => rfl
    | _ + 2, a => exact a.down.elim
  | ty0 A =>
    show ((open Classical in if h : A = A then some (h ▸ a.down) else none).map ULift.up) = some a
    rw [dif_pos rfl]
    rfl
  | prop P =>
    show ((if h : P then some (⟨h⟩ : PLift P) else none).map ULift.up) = some a
    rw [dif_pos a.down.down]
    rfl
  | ty2 _ | err => exact a.down.elim

/-- Decoding an encoded level-2 element gives it back. -/
theorem TyM.dec2_enc2 (T : TyM) (a : T.el2) : T.dec2 (T.enc2 a) = some a := by
  cases T with
  | ty2 A =>
    show (if h : A = A then some (h ▸ a) else none) = some a
    rw [dif_pos rfl]
  | univ l =>
    match l, a with
    | 0, _ => rfl
    | 1, _ => rfl
    | 2, _ => rfl
    | _ + 3, a => exact a.down.down.elim
  | ty1 A =>
    show ((if h : A = A then some (h ▸ a.down) else none).map ULift.up) = some a
    rw [dif_pos rfl]
    rfl
  | ty0 A =>
    show (((open Classical in if h : A = A then some (h ▸ a.down.down) else none).map ULift.up).map ULift.up) = some a
    rw [dif_pos rfl]
    rfl
  | prop P =>
    show (((if h : P then some (⟨h⟩ : PLift P) else none).map ULift.up).map ULift.up) = some a
    rw [dif_pos a.down.down.down]
    rfl
  | err => exact a.down.down.elim

theorem map_up_eq_some.{v, w} {α : Type v} {x : Option α} {a : ULift.{w} α} (h : x.map ULift.up = some a) :
    x = some a.down := by
  cases x with
  | none => cases h
  | some y => cases h; rfl

/-- What decodes at level 0 is the encoding of what it decodes to (the other round trip). -/
theorem TyM.enc0_of_dec0 (T : TyM) (s : Sem) (a : T.el0) (h : T.dec0 s = some a) : T.enc0 a = s := by
  cases T with
  | ty0 A =>
    cases s with
    | el0 B b =>
      have h' : (open Classical in if h : B = A then some (h ▸ b) else none) = some a := h
      by_cases hb : B = A
      · subst hb; rw [dif_pos rfl] at h'; cases h'; rfl
      · rw [dif_neg hb] at h'; cases h'
    | _ => cases h
  | prop P =>
    cases s with
    | proof => rfl
    | _ => cases h
  | ty1 _ | ty2 _ | univ _ | err => exact a.elim

/-- What decodes at level 1 is the encoding of what it decodes to. -/
theorem TyM.enc1_of_dec1 (T : TyM) (s : Sem) (a : T.el1) (h : T.dec1 s = some a) : T.enc1 a = s := by
  cases T with
  | ty1 A =>
    cases s with
    | el1 B b =>
      have h' : (if h : B = A then some (h ▸ b) else none) = some a := h
      by_cases hb : B = A
      · subst hb; rw [dif_pos rfl] at h'; cases h'; rfl
      · rw [dif_neg hb] at h'; cases h'
    | _ => cases h
  | univ l =>
    match l with
    | 0 =>
      cases s with
      | ty T => cases T with
        | prop P => cases h; rfl
        | _ => cases h
      | _ => cases h
    | 1 =>
      cases s with
      | ty T => cases T with
        | ty0 A => cases h; rfl
        | _ => cases h
      | _ => cases h
    | _ + 2 => exact a.down.elim
  | ty0 A => exact TyM.enc0_of_dec0 (.ty0 A) s a.down (map_up_eq_some h)
  | prop P => exact TyM.enc0_of_dec0 (.prop P) s a.down (map_up_eq_some h)
  | ty2 _ | err => exact a.down.elim

/-- What decodes at level 2 is the encoding of what it decodes to. -/
theorem TyM.enc2_of_dec2 (T : TyM) (s : Sem) (a : T.el2) (h : T.dec2 s = some a) : T.enc2 a = s := by
  cases T with
  | ty2 A =>
    cases s with
    | el2 B b =>
      have h' : (if h : B = A then some (h ▸ b) else none) = some a := h
      by_cases hb : B = A
      · subst hb; rw [dif_pos rfl] at h'; cases h'; rfl
      · rw [dif_neg hb] at h'; cases h'
    | _ => cases h
  | univ l =>
    match l with
    | 0 => exact TyM.enc1_of_dec1 (.univ 0) s a.down (map_up_eq_some h)
    | 1 => exact TyM.enc1_of_dec1 (.univ 1) s a.down (map_up_eq_some h)
    | 2 =>
      cases s with
      | ty T => cases T with
        | ty1 A => cases h; rfl
        | _ => cases h
      | _ => cases h
    | _ + 3 => exact a.down.down.elim
  | ty1 A => exact TyM.enc1_of_dec1 (.ty1 A) s a.down (map_up_eq_some h)
  | ty0 A => exact TyM.enc1_of_dec1 (.ty0 A) s a.down (map_up_eq_some h)
  | prop P => exact TyM.enc1_of_dec1 (.prop P) s a.down (map_up_eq_some h)
  | err => exact a.down.down.elim

/-! ## Levels -/

/-- A level of the model's carriers: what the level-0 construction reads of its level. `el` is
the carrier of a type meaning at this level, `enc`/`dec` encode and decode its elements as
meanings, `ty` is a carrier at this level as a type meaning (`ty0`/`ty1`/`ty2`), and
`pack`/`unpack` tag an element of such a carrier as a meaning (`Sem.el0`/`el1`/`el2`) and read it
back. -/
structure Lvl : Type (max 3 (u + 1)) where
  el : TyM → Type u
  enc : (T : TyM) → el T → Sem
  dec : (T : TyM) → Sem → Option (el T)
  ty : Type u → TyM
  pack : (A : Type u) → A → Sem
  unpack : (A : Type u) → Sem → Option A

/-- Read a meaning as an element of a level-1 Lean type, by its tag (as `Sem.as` at level 0). -/
noncomputable def Sem.as1 (A : Type 1) : Sem → Option A
  | .el1 B b => if h : B = A then some (h ▸ b) else none
  | _ => none

/-- Read a meaning as an element of a level-2 Lean type, by its tag. -/
noncomputable def Sem.as2 (A : Type 2) : Sem → Option A
  | .el2 B b => if h : B = A then some (h ▸ b) else none
  | _ => none

/-- Level 0: `Type₀`, propositions (`Apply.lean`'s carriers). -/
noncomputable def lvl0 : Lvl.{0} := ⟨TyM.el0, TyM.enc0, TyM.dec0, .ty0, .el0, Sem.as⟩

/-- Level 1: `Type₁`, the universes `Prop` and `Type₀`, lower levels lifted. -/
noncomputable def lvl1 : Lvl.{1} := ⟨TyM.el1, TyM.enc1, TyM.dec1, .ty1, .el1, Sem.as1⟩

/-- Level 2: `Type₂`, the universe `Type₁`, lower levels lifted. -/
noncomputable def lvl2 : Lvl.{2} := ⟨TyM.el2, TyM.enc2, TyM.dec2, .ty2, .el2, Sem.as2⟩

theorem lvl1_dec_enc (T : TyM) (a : lvl1.el T) : lvl1.dec T (lvl1.enc T a) = some a := TyM.dec1_enc1 T a

theorem lvl2_dec_enc (T : TyM) (a : lvl2.el T) : lvl2.dec T (lvl2.enc T a) = some a := TyM.dec2_enc2 T a

theorem lvl0_unpack_pack (A : Type) (a : A) : lvl0.unpack A (lvl0.pack A a) = some a := by
  show (open Classical in if h : A = A then some (h ▸ a) else none) = some a
  rw [dif_pos rfl]

theorem lvl1_unpack_pack (A : Type 1) (a : A) : lvl1.unpack A (lvl1.pack A a) = some a := by
  show (if h : A = A then some (h ▸ a) else none) = some a
  rw [dif_pos rfl]

theorem lvl2_unpack_pack (A : Type 2) (a : A) : lvl2.unpack A (lvl2.pack A a) = some a := by
  show (if h : A = A then some (h ▸ a) else none) = some a
  rw [dif_pos rfl]

/-- Unpacking at a carrier is decoding at its type meaning, at every level. -/
theorem lvl0_unpack_dec (A : Type) (s : Sem) : lvl0.unpack A s = lvl0.dec (lvl0.ty A) s := rfl

theorem lvl1_unpack_dec (A : Type 1) (s : Sem) : lvl1.unpack A s = lvl1.dec (lvl1.ty A) s := by
  cases s <;> rfl

theorem lvl2_unpack_dec (A : Type 2) (s : Sem) : lvl2.unpack A s = lvl2.dec (lvl2.ty A) s := by
  cases s <;> rfl

/-- A packed element is a member of its carrier's type meaning, at every level. -/
theorem lvl0_pack_mem (A : Type) (a : A) : lvl0.pack A a ∈ₛ lvl0.ty A := rfl

theorem lvl1_pack_mem (A : Type 1) (a : A) : lvl1.pack A a ∈ₛ lvl1.ty A := rfl

theorem lvl2_pack_mem (A : Type 2) (a : A) : lvl2.pack A a ∈ₛ lvl2.ty A := rfl

/-- A lawful level: what decodes is the encoding of what it decodes to (with `dec_enc`, the two
round trips). The three levels are lawful. -/
def Lvl.EncDec (L : Lvl.{u}) : Prop := ∀ T s a, L.dec T s = some a → L.enc T a = s

theorem lvl0_encDec : lvl0.EncDec := TyM.enc0_of_dec0
theorem lvl1_encDec : lvl1.EncDec := TyM.enc1_of_dec1
theorem lvl2_encDec : lvl2.EncDec := TyM.enc2_of_dec2

/-! ## Carriers, application and construction at a level -/

section
variable (L : Lvl.{u})

/-- The output of a Π at level `L`, as a function of the prefix and of the final contents `Fin`:
`PiOut.car0` at the level. -/
def PiOut.carL : PiOut → List Sem → Type u → Type u
  | .data B, acc, Fin => L.el (B acc) × Fin
  | .ref U, acc, Fin => Back Fin (L.el (U acc))

/-- The final contents accumulated after a parameter at level `L` (`extFin`). -/
abbrev extFinL (b : Bool) (Fin T : Type u) : Type u := match b with | true => Fin × T | false => Fin

/-- The level-`L` carrier of a Π with the parameters `ps` after the prefix `acc`, with the final
contents accumulated so far in `Fin`: `piCar0` at the level. -/
def piCarL : List PiParam → List Sem → Type u → PiOut → Type u
  | [], acc, Fin, out => PiOut.carL L out acc Fin
  | p :: ps, acc, Fin, out =>
    (a : L.el (p.dom acc)) →
      piCarL ps (acc ++ [L.enc (p.dom acc) a]) (extFinL p.isRef Fin (L.el (p.dom acc))) out

/-- Read the accumulated final contents as meanings, in parameter order (`extRead`). -/
def extReadL (b : Bool) (Fin T : Type u) (readFin : Fin → List Sem) (enc : T → Sem) :
    extFinL b Fin T → List Sem :=
  match b with
  | true => fun x => readFin x.1 ++ [enc x.2]
  | false => readFin

/-- Build the accumulated final contents from meanings in parameter order, consuming them from
the front (`extMk`). -/
def extMkL (b : Bool) (Fin T : Type u) (mkFin : List Sem → Option (Fin × List Sem)) (dec : Sem → Option T) :
    List Sem → Option (extFinL b Fin T × List Sem) :=
  match b with
  | true => fun fs => do
    let (x, rest) ← mkFin fs
    match rest with
    | t :: rest' => (dec t).map fun y => ((x, y), rest')
    | [] => none
  | false => mkFin

/-- The result of applying a level-`L` Π (`AppResult`): for a data codomain the result and the
final contents of the borrow parameters, in parameter order; for a returned borrow the forward
value and the backward function. -/
inductive AppResultL : Type (max 3 u) where
  | data (result : Sem) (finals : List Sem)
  | ref (U : TyM) (fwd : L.el U) (back : L.el U → List Sem)

/-- Apply a level-`L` Π-carrier element to arguments, walking the telescope (`applyTele`); `none`
if an argument is not of its parameter type or their number is wrong. -/
noncomputable def applyTeleL : (ps : List PiParam) → (acc : List Sem) → (Fin : Type u) →
    (Fin → List Sem) → (out : PiOut) → piCarL L ps acc Fin out → List Sem → Option (AppResultL L)
  | [], acc, _, readFin, .data B, r, [] => some (.data (L.enc (B acc) r.1) (readFin r.2))
  | [], acc, _, readFin, .ref U, r, [] => some (.ref (U acc) r.val.1 fun v => readFin (r.val.2 v))
  | p :: ps, acc, Fin, readFin, out, f, a :: as =>
    match L.dec (p.dom acc) a with
    | some x =>
      applyTeleL ps (acc ++ [L.enc (p.dom acc) x]) (extFinL p.isRef Fin (L.el (p.dom acc)))
        (extReadL p.isRef Fin (L.el (p.dom acc)) readFin (L.enc (p.dom acc))) out (f x) as
    | none => none
  | _, _, _, _, _, _, _ => none

/-- The leaf of `mkTeleL` for a data codomain (`mkLeafData`): the result decoded at `B acc`, the
final contents built from the body's finals at the future `φ`. -/
noncomputable def mkLeafDataL (φ : Future) (acc : List Sem) (Fin : Type u)
    (mkFin : List Sem → Option (Fin × List Sem)) (B : List Sem → TyM) (o : BodyOut) :
    Option (L.el (B acc) × Fin) :=
  match L.dec (B acc) o.result, mkFin (o.finals.map (· φ)) with
  | some r, some (fin, []) => some (r, fin)
  | _, _ => none

/-- The backward function of a borrow-returning body at the value `v` the caller leaves in the
returned borrow (`mkBackAt`): the finals read in the future that fixes the returned label to `v`. -/
noncomputable def mkBackAtL (φ : Future) (Fin : Type u) (mkFin : List Sem → Option (Fin × List Sem))
    (U : TyM) (o : BodyOut) (k : Nat) (v : L.el U) : Option Fin :=
  match mkFin (o.finals.map (· (φ.upd k (L.enc U v)))) with
  | some (fin, []) => some fin
  | _ => none

/-- The leaf of `mkTeleL` for a returned borrow (`mkLeafRef`): the forward value and the backward
function, which must be total and injective (`Back`). -/
noncomputable def mkLeafRefL (φ : Future) (acc : List Sem) (Fin : Type u)
    (mkFin : List Sem → Option (Fin × List Sem)) (U : List Sem → TyM) (o : BodyOut) :
    Option (Back Fin (L.el (U acc))) :=
  match o.retLabel, L.dec (U acc) o.result with
  | some k, some fwd =>
    if h : ∀ v, (mkBackAtL L φ Fin mkFin (U acc) o k v).isSome then
      let back := fun v => (mkBackAtL L φ Fin mkFin (U acc) o k v).get (h v)
      if hi : ∀ v w, back v = back w → v = w then some ⟨(fwd, back), hi⟩ else none
    else none
  | _, _ => none

/-- Build a level-`L` Π-carrier element from a function on meanings (a body's run), walking the
telescope and deciding classically at each argument (`mkTele`); `none` if the body is undefined
somewhere, its result or a final content is not of its type, or (a returned borrow) the backward
function is not injective. -/
noncomputable def mkTeleL (φ : Future) : (ps : List PiParam) → (acc : List Sem) → (Fin : Type u) →
    (List Sem → Option (Fin × List Sem)) → (out : PiOut) → (List Sem → Option BodyOut) →
    Option (piCarL L ps acc Fin out)
  | [], acc, Fin, mkFin, .data B, g => (g acc).bind (mkLeafDataL L φ acc Fin mkFin B)
  | [], acc, Fin, mkFin, .ref U, g => (g acc).bind (mkLeafRefL L φ acc Fin mkFin U)
  | p :: ps, acc, Fin, mkFin, out, g =>
    if h : ∀ x : L.el (p.dom acc),
        (mkTeleL φ ps (acc ++ [L.enc (p.dom acc) x]) (extFinL p.isRef Fin (L.el (p.dom acc)))
          (extMkL p.isRef Fin (L.el (p.dom acc)) mkFin (L.dec (p.dom acc))) out g).isSome then
      some fun x => (mkTeleL φ ps (acc ++ [L.enc (p.dom acc) x]) (extFinL p.isRef Fin (L.el (p.dom acc)))
          (extMkL p.isRef Fin (L.el (p.dom acc)) mkFin (L.dec (p.dom acc))) out g).get (h x)
    else none

end

/-! ## Calling a built function runs its body (the β-laws) -/

section
variable (L : Lvl.{u})

/-- The arguments fit the telescope at level `L`: as many as the parameters, each decoding at its
parameter type at the earlier arguments. -/
def ArgsFit : List PiParam → List Sem → List Sem → Prop
  | [], _, [] => True
  | p :: ps, acc, a :: as => (L.dec (p.dom acc) a).isSome ∧ ArgsFit ps (acc ++ [a]) as
  | _, _, _ => False

/-- `readFin` inverts `mkFin` on what it consumes (the accumulated final contents). -/
def FinInv {Fin : Type u} (mkFin : List Sem → Option (Fin × List Sem)) (readFin : Fin → List Sem) : Prop :=
  ∀ fs fin rest, mkFin fs = some (fin, rest) → readFin fin ++ rest = fs

/-- The inverse is kept by each parameter's step (`extMkL`/`extReadL`), at a lawful level. -/
theorem finInv_ext (hL : L.EncDec) (b : Bool) (Fin : Type u) (T : TyM)
    (mkFin : List Sem → Option (Fin × List Sem)) (readFin : Fin → List Sem) (h : FinInv mkFin readFin) :
    FinInv (extMkL b Fin (L.el T) mkFin (L.dec T)) (extReadL b Fin (L.el T) readFin (L.enc T)) := by
  cases b with
  | false => exact h
  | true =>
    intro fs fin rest hm
    cases hmk : mkFin fs with
    | none => simp [extMkL, hmk] at hm
    | some p =>
      obtain ⟨x, r⟩ := p
      cases r with
      | nil => simp [extMkL, hmk] at hm
      | cons t r' =>
        cases hd : L.dec T t with
        | none => simp [extMkL, hmk, hd] at hm
        | some y =>
          simp [extMkL, hmk, hd] at hm
          obtain ⟨rfl, rfl⟩ := hm
          have := h fs x (t :: r') hmk
          simp only [extReadL, hL T t y hd, List.append_assoc, List.singleton_append]
          exact this

/-- **Calling a built function runs its body (data codomain).** At a lawful level, if `mkTeleL`
built `F` from the body's run `g`, then applying `F` to arguments that fit the telescope gives
the body's result at those arguments and its final contents at the future, in parameter order. -/
theorem applyTeleL_mkTeleL (hL : L.EncDec) (φ : Future) (B : List Sem → TyM) (g : List Sem → Option BodyOut) :
    ∀ (ps : List PiParam) (acc : List Sem) (Fin : Type u) (mkFin : List Sem → Option (Fin × List Sem))
      (readFin : Fin → List Sem) (F : piCarL L ps acc Fin (.data B)) (args : List Sem),
      FinInv mkFin readFin → mkTeleL L φ ps acc Fin mkFin (.data B) g = some F → ArgsFit L ps acc args →
      ∃ o, g (acc ++ args) = some o ∧
        applyTeleL L ps acc Fin readFin (.data B) F args = some (.data o.result (o.finals.map (· φ)))
  | [], acc, Fin, mkFin, readFin, F, [], hF, hmk, _ => by
    have hdef : mkTeleL L φ [] acc Fin mkFin (.data B) g = (g acc).bind (mkLeafDataL L φ acc Fin mkFin B) := rfl
    rw [hdef] at hmk
    cases hg : g acc with
    | none => rw [hg] at hmk; cases hmk
    | some o =>
      rw [hg] at hmk
      refine ⟨o, by simpa using hg, ?_⟩
      have hmk' : mkLeafDataL L φ acc Fin mkFin B o = some F := hmk
      unfold mkLeafDataL at hmk'
      cases hr : L.dec (B acc) o.result with
      | none => simp [hr] at hmk'
      | some r =>
        cases hm : mkFin (o.finals.map (· φ)) with
        | none => simp [hr, hm] at hmk'
        | some q =>
          obtain ⟨fin, rest⟩ := q
          cases rest with
          | cons _ _ => simp [hr, hm] at hmk'
          | nil =>
            simp only [hr, hm] at hmk'
            cases hmk'
            show some (AppResultL.data (L.enc (B acc) r) (readFin fin)) = _
            rw [hL _ _ _ hr, show readFin fin = o.finals.map (· φ) by simpa using hF _ _ _ hm]
  | [], _, _, _, _, _, _ :: _, _, _, hfit => hfit.elim
  | _ :: _, _, _, _, _, _, [], _, _, hfit => hfit.elim
  | p :: ps, acc, Fin, mkFin, readFin, F, a :: as, hF, hmk, ⟨hd, hfit⟩ => by
    obtain ⟨x, hx⟩ := Option.isSome_iff_exists.mp hd
    unfold mkTeleL at hmk
    split at hmk
    · rename_i hall
      cases hmk
      have hea : L.enc (p.dom acc) x = a := hL _ _ _ hx
      obtain ⟨o, hg, hap⟩ := applyTeleL_mkTeleL hL φ B g ps (acc ++ [L.enc (p.dom acc) x]) _ _ _ _ as
        (finInv_ext L hL p.isRef Fin (p.dom acc) mkFin readFin hF) (Option.some_get (hall x)).symm
        (by rw [hea]; exact hfit)
      refine ⟨o, by simpa [hea] using hg, ?_⟩
      simp only [applyTeleL, hx]
      exact hap
    · cases hmk
/-- **Calling a built function runs its body (returned borrow).** Applying `F` gives the body's
result as the forward value, at the codomain at the arguments, and as the backward function the
body's final contents read in the future that fixes the returned label to the value left in it. -/
theorem applyTeleL_mkTeleL_ref (hL : L.EncDec) (φ : Future) (U : List Sem → TyM) (g : List Sem → Option BodyOut) :
    ∀ (ps : List PiParam) (acc : List Sem) (Fin : Type u) (mkFin : List Sem → Option (Fin × List Sem))
      (readFin : Fin → List Sem) (F : piCarL L ps acc Fin (.ref U)) (args : List Sem),
      FinInv mkFin readFin → mkTeleL L φ ps acc Fin mkFin (.ref U) g = some F → ArgsFit L ps acc args →
      ∃ o k U' fwd back, g (acc ++ args) = some o ∧ o.retLabel = some k ∧
        applyTeleL L ps acc Fin readFin (.ref U) F args = some (.ref U' fwd back) ∧
        U' = U (acc ++ args) ∧ L.enc U' fwd = o.result ∧
        ∀ v, back v = o.finals.map (· (φ.upd k (L.enc U' v)))
  | [], acc, Fin, mkFin, readFin, F, [], hF, hmk, _ => by
    have hdef : mkTeleL L φ [] acc Fin mkFin (.ref U) g = (g acc).bind (mkLeafRefL L φ acc Fin mkFin U) := rfl
    rw [hdef] at hmk
    cases hg : g acc with
    | none => rw [hg] at hmk; cases hmk
    | some o =>
      rw [hg] at hmk
      have hmk' : mkLeafRefL L φ acc Fin mkFin U o = some F := hmk
      unfold mkLeafRefL at hmk'
      cases hk : o.retLabel with
      | none => simp [hk] at hmk'
      | some k =>
        cases hr : L.dec (U acc) o.result with
        | none => simp [hk, hr] at hmk'
        | some fwd =>
          simp only [hk, hr] at hmk'
          split at hmk'
          · rename_i htot
            split at hmk'
            · cases hmk'
              refine ⟨o, k, U acc, fwd, _, by simpa using hg, hk, rfl, by simp, hL _ _ _ hr, ?_⟩
              intro v
              obtain ⟨b, hb⟩ := Option.isSome_iff_exists.mp (htot v)
              have hget : (mkBackAtL L φ Fin mkFin (U acc) o k v).get (htot v) = b := by simp [hb]
              show readFin ((mkBackAtL L φ Fin mkFin (U acc) o k v).get (htot v)) = _
              rw [hget]
              unfold mkBackAtL at hb
              split at hb
              · rename_i fin heq
                cases hb
                simpa using hF _ _ _ heq
              · cases hb
            · cases hmk'
          · cases hmk'
  | [], _, _, _, _, _, _ :: _, _, _, hfit => hfit.elim
  | _ :: _, _, _, _, _, _, [], _, _, hfit => hfit.elim
  | p :: ps, acc, Fin, mkFin, readFin, F, a :: as, hF, hmk, ⟨hd, hfit⟩ => by
    obtain ⟨x, hx⟩ := Option.isSome_iff_exists.mp hd
    unfold mkTeleL at hmk
    split at hmk
    · rename_i hall
      cases hmk
      have hea : L.enc (p.dom acc) x = a := hL _ _ _ hx
      obtain ⟨o, k, U', fwd, back, hg, hk, hap, hU, he, hb⟩ :=
        applyTeleL_mkTeleL_ref hL φ U g ps (acc ++ [L.enc (p.dom acc) x]) _ _ _ _ as
          (finInv_ext L hL p.isRef Fin (p.dom acc) mkFin readFin hF) (Option.some_get (hall x)).symm
          (by rw [hea]; exact hfit)
      refine ⟨o, k, U', fwd, back, by simpa [hea] using hg, hk, ?_, by simpa [hea] using hU, he, hb⟩
      simp only [applyTeleL, hx]
      exact hap
    · cases hmk
/-- The starting accumulator (`PUnit`, nothing consumed) is inverted by reading nothing. -/
theorem finInv_start : FinInv (fun fs => some (PUnit.unit, fs)) (fun (_ : PUnit.{u + 1}) => ([] : List Sem)) := by
  intro fs fin rest h
  cases h
  rfl

end

/-! ## The instances, and what the reference run uses -/

/-- Level-1 application and construction (`Type₁`: polymorphic functions). -/
noncomputable abbrev applyTele1 := applyTeleL lvl1
noncomputable abbrev mkTele1 := mkTeleL lvl1

/-- Level-2 application and construction (`Type₂`: functions on `Type₁`). -/
noncomputable abbrev applyTele2 := applyTeleL lvl2
noncomputable abbrev mkTele2 := mkTeleL lvl2

section
variable (L : Lvl.{u})

/-- The meaning of a Π-type at level `L`: the carrier with no final contents yet. -/
def piTyL (ps : List PiParam) (out : PiOut) : TyM := L.ty (piCarL L ps [] PUnit out)

/-- The meaning of a closure at level `L` from its body's run at every argument (`g`): the
carrier element `mkTeleL` builds, tagged at its carrier; `err` where `mkTeleL` fails. -/
noncomputable def closureL (φ : Future) (ps : List PiParam) (out : PiOut) (g : List Sem → Option BodyOut) : Sem :=
  match mkTeleL L φ ps [] PUnit (fun fs => some (PUnit.unit, fs)) out g with
  | some F => L.pack _ F
  | none => .err

/-- Apply a function meaning at level `L` (the callee's tag says which level): unpack it at its
carrier, then walk the telescope. -/
noncomputable def applyFnL (ps : List PiParam) (out : PiOut) (F : Sem) (args : List Sem) :
    Option (AppResultL L) :=
  (L.unpack (piCarL L ps [] PUnit out) F).bind fun F => applyTeleL L ps [] PUnit (fun _ => []) out F args

/-- A closure is a member of its Π-type's meaning, or `err`: the two have one carrier. -/
theorem closureL_mem (φ : Future) (ps : List PiParam) (out : PiOut) (g : List Sem → Option BodyOut)
    (hpack : ∀ (A : Type u) (a : A), L.pack A a ∈ₛ L.ty A) :
    closureL L φ ps out g ∈ₛ piTyL L ps out ∨ closureL L φ ps out g = .err := by
  unfold closureL
  split
  · exact .inl (hpack _ _)
  · exact .inr rfl

/-- **Calling a closure runs its body**, at a lawful level: applying the meaning `closureL`
builds to arguments that fit its telescope gives the body's result at them, and its final
contents at the future. -/
theorem applyFnL_closureL (hL : L.EncDec) (hP : ∀ (A : Type u) (a : A), L.unpack A (L.pack A a) = some a)
    (φ : Future) (ps : List PiParam) (B : List Sem → TyM) (g : List Sem → Option BodyOut) (args : List Sem)
    (hs : (mkTeleL L φ ps [] PUnit (fun fs => some (PUnit.unit, fs)) (.data B) g).isSome)
    (hfit : ArgsFit L ps [] args) :
    ∃ o, g args = some o ∧
      applyFnL L ps (.data B) (closureL L φ ps (.data B) g) args = some (.data o.result (o.finals.map (· φ))) := by
  obtain ⟨F, hF⟩ := Option.isSome_iff_exists.mp hs
  obtain ⟨o, hg, hap⟩ := applyTeleL_mkTeleL L hL φ B g ps [] PUnit _ (fun _ => []) F args (finInv_start) hF hfit
  refine ⟨o, by simpa using hg, ?_⟩
  unfold closureL applyFnL
  rw [hF]
  simp only [hP, Option.bind_some]
  exact hap

end

/-- The meaning of a Π-type at its declared sort `l` (D55, `Decisions.piSort`): the proposition
`piProp` at `Prop`, the level-`l - 1` carrier at `Type_{l-1}` for the bounded levels, `err` above
(D2). The `.pi` and `.fix` clauses must both use it, so that a closure lies in its type. -/
noncomputable def piTyAt (l : Nat) (ps : List PiParam) (out : PiOut) : TyM :=
  match l with
  | 0 => .prop (piProp ps [] fun acc => match out with | .data B => (B acc).true | .ref _ => False)
  | 1 => piTyL lvl0 ps out
  | 2 => piTyL lvl1 ps out
  | 3 => piTyL lvl2 ps out
  | _ => .err

/-- The meaning of a closure at its declared sort `l`: `⋆` at `Prop` (D12: a proof-valued
function is a proof), the level-`l - 1` element otherwise, `err` above the bounded levels. -/
noncomputable def closureAt (l : Nat) (φ : Future) (ps : List PiParam) (out : PiOut)
    (g : List Sem → Option BodyOut) : Sem :=
  match l with
  | 0 => .proof
  | 1 => closureL lvl0 φ ps out g
  | 2 => closureL lvl1 φ ps out g
  | 3 => closureL lvl2 φ ps out g
  | _ => .err

/-- At a data sort, a closure is a member of its type at that sort, or `err` (D12's invariant
for `Type₀`, `Type₁`, `Type₂`). -/
theorem closureAt_mem (l : Nat) (hl : l = 1 ∨ l = 2 ∨ l = 3) (φ : Future) (ps : List PiParam)
    (out : PiOut) (g : List Sem → Option BodyOut) :
    closureAt l φ ps out g ∈ₛ piTyAt l ps out ∨ closureAt l φ ps out g = .err := by
  rcases hl with rfl | rfl | rfl
  · exact closureL_mem lvl0 φ ps out g lvl0_pack_mem
  · exact closureL_mem lvl1 φ ps out g lvl1_pack_mem
  · exact closureL_mem lvl2 φ ps out g lvl2_pack_mem

/-! ## Level 0 is `Pi.lean`'s, and the suite's shapes at level 1 -/

/-- At level 0 the generic carrier is `piCar0`. -/
theorem piCarL_lvl0 (ps : List PiParam) (acc : List Sem) (Fin : Type) (out : PiOut) :
    piCarL lvl0 ps acc Fin out = piCar0 ps acc Fin out := by
  induction ps generalizing acc Fin with
  | nil => cases out <;> rfl
  | cons p ps ih =>
    show ((a : (p.dom acc).el0) → piCarL lvl0 ps (acc ++ [(p.dom acc).enc0 a]) (extFinL p.isRef Fin (p.dom acc).el0) out)
      = ((a : (p.dom acc).el0) → piCar0 ps (acc ++ [(p.dom acc).enc0 a]) (extFinL p.isRef Fin (p.dom acc).el0) out)
    exact congrArg (fun β : (p.dom acc).el0 → Type => (a : (p.dom acc).el0) → β a) (funext fun a => ih _ _)

namespace Apply1Sanity

/-- The polymorphic identity's shape, `Π(A : Type₀). Π(x : A). A`. -/
def idShape : List PiParam × PiOut :=
  ([⟨false, fun _ => .univ 1⟩, ⟨false, fun acc => (acc.getD 0 .err).asTy⟩],
   .data fun acc => (acc.getD 0 .err).asTy)

/-- `id (A : Type) (x : A) : A` at level 1: from a type and an element of it to that element
(with no final contents). -/
example : piCarL lvl1 idShape.1 [] PUnit.{2} idShape.2 = ((A : Type) → (x : ULift.{1} A) → ULift.{1} A × PUnit.{2}) :=
  rfl

/-- `Swap (V : Type) (a : &V) (b : &V) : Unit` (the suite's `BorrowTypes.lean`) at level 1: the
two borrowed places' final contents, lifted, which `piCar1` cannot hold. -/
example : piCarL lvl1 [⟨false, fun _ => .univ 1⟩, ⟨true, fun acc => (acc.getD 0 .err).asTy⟩,
      ⟨true, fun acc => (acc.getD 0 .err).asTy⟩] [] PUnit.{2} (.data fun _ => .ty0 Unit)
    = ((V : Type) → (a : ULift.{1} V) → (b : ULift.{1} V) → ULift.{1} Unit × ((PUnit.{2} × ULift.{1} V) × ULift.{1} V)) :=
  rfl

/-- `F (A : Type₁) : Type₁` at level 2: from a level-1 type to one. -/
example : piCarL lvl2 [⟨false, fun _ => .univ 2⟩] [] PUnit.{3} (.data fun _ => .univ 2)
    = ((A : Type 1) → Type 1 × PUnit.{3}) :=
  rfl

/-- The identity's body as a function on meanings: it returns its second argument. -/
def idBody : List Sem → Option BodyOut := fun acc => some ⟨acc.getD 1 .err, [], none⟩

theorem dec1_el0 (A : Type) (a : A) : TyM.dec1 (.ty0 A) (.el0 A a) = some ⟨a⟩ := by
  show ((open Classical in if h : A = A then some (h ▸ a) else none).map ULift.up) = _
  rw [dif_pos rfl]; rfl

theorem id_leaf (φ : Future) (A : Type) (x : ULift.{1} A) :
    mkTeleL lvl1 φ [] [.ty (.ty0 A), .el0 A x.down] PUnit (fun fs => some (PUnit.unit, fs)) idShape.2 idBody
      = some (x, PUnit.unit) := by
  have h1 : mkTeleL lvl1 φ [] [.ty (.ty0 A), .el0 A x.down] PUnit (fun fs => some (PUnit.unit, fs)) idShape.2 idBody
      = mkLeafDataL lvl1 φ [.ty (.ty0 A), .el0 A x.down] PUnit (fun fs => some (PUnit.unit, fs))
          (fun acc => (acc.getD 0 .err).asTy) ⟨.el0 A x.down, [], none⟩ := rfl
  rw [h1]
  unfold mkLeafDataL
  have h2 : lvl1.dec ((fun acc => (acc.getD 0 Sem.err).asTy) [Sem.ty (TyM.ty0 A), Sem.el0 A x.down])
      (BodyOut.result ⟨.el0 A x.down, [], none⟩) = some x := dec1_el0 A x.down
  rw [h2]
  rfl

/-- `mkTele1` builds the polymorphic identity: its body is defined and well typed at every type
and every element of it. -/
theorem id_built (φ : Future) :
    (mkTele1 φ idShape.1 [] PUnit (fun fs => some (PUnit.unit, fs)) idShape.2 idBody).isSome := by
  unfold mkTele1 idShape
  unfold mkTeleL
  dsimp only
  rw [dif_pos]
  · rfl
  · intro A
    unfold mkTeleL
    dsimp only
    rw [dif_pos]
    · rfl
    · intro x
      exact (id_leaf φ A x) ▸ rfl

/-- `id(Nat, 5)` is `5`: the level-1 closure, applied, runs its body (`applyFnL_closureL`). -/
theorem id_call (φ : Future) :
    applyFnL lvl1 idShape.1 idShape.2 (closureL lvl1 φ idShape.1 idShape.2 idBody) [.ty (.ty0 Nat), .el0 Nat 5]
      = some (.data (.el0 Nat 5) []) := by
  have hfit : ArgsFit lvl1 idShape.1 [] [.ty (.ty0 Nat), .el0 Nat 5] := by
    refine ⟨rfl, ?_, trivial⟩
    show (TyM.dec1 (.ty0 Nat) (.el0 Nat 5)).isSome = true
    rw [dec1_el0]
    rfl
  obtain ⟨o, hg, hap⟩ := applyFnL_closureL lvl1 lvl1_encDec lvl1_unpack_pack φ idShape.1
    (fun acc => (acc.getD 0 .err).asTy) idBody _ (id_built φ) hfit
  cases hg
  exact hap

end Apply1Sanity

end Ochr.Meaning
