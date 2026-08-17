import Dllbc.Program
import Dllbc.Boundary
import Dllbc.ProgMacro
import Dllbc.Std
import Dllbc.StdLemmas
import Dllbc.Tests.Diff
import Dllbc.Tests.Direct

/-!
# The hashmap flagship — a verified, resizable, in-place hashmap

`docs/13-hashmap-flagship.md` is the problem statement; this is the artifact. The
shape mirrors the Aeneas ICFP'22 case study (`competitors/aeneas-hashmap/`) closely
enough that the two can be compared side by side: slots are an array of
association-list buckets, the hash is the identity, the slot is `Mod key cap`, the
load factor is 4/5, and a full table doubles its capacity and re-inserts everything.

**The invariant is packed in the type.** A `HashMap` value cannot exist broken, so
every operation's invariant-preservation proof is just returning a well-typed pack —
and, per `HmProbeGetmut`'s G5, it survives even the opaque group ends that lose every
functional fact, because §6.1 re-mints a caller's payload as a fresh σ AT THE DECLARED
TYPE and inhabiting the type IS the invariant.

The file reads bottom-up: the pure vocabulary the specs are written in, then the
invariant library, then the programs, then the twins and the executing differential.
-/

section

open Dllbc
open Dllbc.StdLemmas (LeRefl LeAdd LeAddL LeAddSucc LeTrans LeUpR LePredL LeRwL LeRwR
  LebTrueLe LebFalseGt AddSucc AddZero AddAssoc AddComm IdTrans IdCongr IdSym Znots SInj
  EqbRefl EqbGtFalse EqbLtFalse ModLtN ModLtNTy ModDec ModDecTy ModCLt ModCLtTy
  StepInv StepInvTy NatRw NatRwTy LeZeroEq LeZeroEqTy)

namespace Dllbc.Tests.HashMap

/-- Type-check a closed term against a closed type in the pure seed (as ArraySort's). -/
def chkL (tm ty : Term) : Bool :=
  match (do let v ← readC 8000 tm; let t ← readC 8000 ty; hasTypeT 8000 v t).run (seedPure [] []) with
  | .ok r _ => r
  | .error _ _ => false

/-- The same, keeping the message — for pinning a rejection while developing. -/
def chkLMsg (tm ty : Term) : String :=
  match (do let v ← readC 8000 tm; let t ← readC 8000 ty; hasTypeT 8000 v t).run (seedPure [] []) with
  | .ok r _ => s!"ok {r}"
  | .error e _ => s!"error {e}"

def pv (t : Term) : Term := Pure.nf 200000 t

def chkProg (t : Term) : String :=
  match checkProgram t prog{ Unit } with | .ok _ => "ACCEPTED" | .error e => "REJECTED: " ++ e

/-! ## 1. The `Option`, as `Σ (b : Bool). OptP b T`

    The kernel's constructor basis is fixed (Unit/Bool/Nat/List/Σ/Array/Id) and has no
    `Option`; `hm-option-kernel` is the parked road not taken. The encoding is a
    Bool-tagged pair whose PAYLOAD TYPE is computed from the tag by an ordinary
    type-valued `boolRec` — so `Pair(True, unit)` and `Pair(False, 5)` are both
    ill-typed, which is what makes it an Option rather than a pair with a flag.

    `Some`/`None`/`Opt` are comptime definitions, not constructors, and that is the
    whole ergonomic claim: a spec reads `Id (Opt Nat) (FindHM q hm) (Some v)`. -/

def OptP : Term := prog{
  λ (B : Bool). λ (T : Type). elim B return (λ (Bm : Bool). Type) {
    True => T,
    False => Unit } }

def Opt : Term := prog{ λ (T : Type). Σ (b : Bool). OptP b T }
def Some : Term := prog{ λ (T : Type). λ (V : T). Pair(True, V) }
def None : Term := prog{ λ (T : Type). Pair(False, unit) }

-- The tag really does control the payload's type, in both directions.
example : chkL prog{ Some Nat 5 } prog{ Opt Nat } = true := by native_decide
example : chkL prog{ None Nat } prog{ Opt Nat } = true := by native_decide
example : chkL prog{ Pair(True, unit) } prog{ Opt Nat } = false := by native_decide
example : chkL prog{ Pair(False, 5) } prog{ Opt Nat } = false := by native_decide

-- …and `Id` at the `Opt` type separates the three interesting cases.
example : chkL prog{ Refl } prog{ Id (Opt Nat) (Some Nat 5) (Some Nat 5) } = true := by
  native_decide
example : chkL prog{ Refl } prog{ Id (Opt Nat) (Some Nat 5) (Some Nat 6) } = false := by
  native_decide
example : chkL prog{ Refl } prog{ Id (Opt Nat) (Some Nat 5) (None Nat) } = false := by
  native_decide

-- The payload type is a parameter, so the encoding survives a hashmap generic in `V`.
example : chkL prog{ Some (List Nat) Cons(1, Nil) } prog{ Opt (List Nat) } = true := by
  native_decide

/-! ## 2. Entries and buckets

    An entry is `Σ (k : Nat). Nat` — a key beside its value — and a bucket is a list of
    them, which is `AList<T>` in the Rust and `list (usize × T)` in the F*.

    These are Lean-level `Term`s spliced by name into `prog{ … }`: `resolveName`'s raw
    fallthrough answers a Lean identifier for any name the surface does not otherwise
    know, so `Entry` and `Bucket` read as ordinary vocabulary at every use site while
    being written once here. -/

def Entry : Term := prog{ Σ (k : Nat). Nat }
def Bucket : Term := prog{ List (Σ (k : Nat). Nat) }

/-! ### The bucket layer, and the one elaborator change this file rests on

    Every function below recurses over a `List (Σ (k : Nat). Nat)`. Until this branch
    the SURFACE's `elim` wrote its list element type as the literal `Nat` in the three
    places `listRec` needs it, so an `elim` over a bucket checked only when the
    recursor spine was written out by hand — five lines instead of three, at every
    bucket function and every induction over one. `Uni.elabUElim` now reads the
    element type out of the motive's binder type, exactly as its `Pair` branch twenty
    lines below has always read `A`/`B` out of `Σ (y : A). B`. It is an ELABORATOR
    change, not a kernel one: the kernel's `listRec` rule took `A` and built `List A`
    from it all along, and whatever the sugar emits the kernel still checks. -/

/-- `LenE b` — a bucket's length. `Std.lenFn` is monomorphic at `List Nat`. -/
def LenE : Term := prog{
  λ (B : List (Σ (k : Nat). Nat)).
    elim B return (λ (Bm : List (Σ (k : Nat). Nat)). Nat) {
      Nil => Z,
      Cons (E) (T) Rec => S(Rec) } }

/-- `FindL q b` — look `q` up in one bucket. The association-list model, and the leaf
    of everything this file specifies. -/
def FindL : Term := prog{
  λ (Q : Nat). λ (B : List (Σ (k : Nat). Nat)).
    elim B return (λ (Bm : List (Σ (k : Nat). Nat)). Opt Nat) {
      Nil => None Nat,
      Cons (E) (T) Rec =>
        elim E return (λ (Em : Σ (k : Nat). Nat). Opt Nat) {
          Pair (K2) (V2) =>
            elim (Eqb Q K2) return (λ (Bz : Bool). Opt Nat) {
              True => Some Nat V2,
              False => Rec } } } }

/-- `InsL k v b` — the bucket model of `insert_in_list`: overwrite in place if the key
    is present, otherwise append a fresh entry at the END. The key test is written
    `Eqb K2 K` (entry key first) because that is the order the PROGRAM's `if e : Eqb
    *kk k` produces, and a spec whose test is the other way round would need a
    symmetry lemma at every site to say the same thing. -/
def InsL : Term := prog{
  λ (K : Nat). λ (V : Nat). λ (B : List (Σ (k : Nat). Nat)).
    elim B return (λ (Bm : List (Σ (k : Nat). Nat)). List (Σ (k : Nat). Nat)) {
      Nil => Cons(Pair(K, V), Nil),
      Cons (E) (T) Rec =>
        elim E return (λ (Em : Σ (k : Nat). Nat). List (Σ (k : Nat). Nat)) {
          Pair (K2) (V2) =>
            elim (Eqb K2 K) return (λ (Bz : Bool). List (Σ (k : Nat). Nat)) {
              True => Cons(Pair(K2, V), T),
              False => Cons(Pair(K2, V2), Rec) } } } }

/-- `RemL k b` — drop the first entry whose key is `k`. -/
def RemL : Term := prog{
  λ (K : Nat). λ (B : List (Σ (k : Nat). Nat)).
    elim B return (λ (Bm : List (Σ (k : Nat). Nat)). List (Σ (k : Nat). Nat)) {
      Nil => Nil,
      Cons (E) (T) Rec =>
        elim E return (λ (Em : Σ (k : Nat). Nat). List (Σ (k : Nat). Nat)) {
          Pair (K2) (V2) =>
            elim (Eqb K2 K) return (λ (Bz : Bool). List (Σ (k : Nat). Nat)) {
              True => T,
              False => Cons(Pair(K2, V2), Rec) } } } }

/-! ### They compute -/

def b0 : Term := prog{ Cons(Pair(1, 10), Cons(Pair(3, 30), Nil)) }

example : chkL b0 Bucket = true := by native_decide
example : (pv prog{ LenE %b0 }).natOf? == Option.some 2 := by native_decide
example : chkL prog{ Refl } prog{ Id (Opt Nat) (FindL 3 %b0) (Some Nat 30) } = true := by
  native_decide
example : chkL prog{ Refl } prog{ Id (Opt Nat) (FindL 9 %b0) (None Nat) } = true := by
  native_decide
example : chkL prog{ Refl } prog{ Id (Opt Nat) (FindL 3 %b0) (Some Nat 10) } = false := by
  native_decide

-- `InsL` overwrites in place (the key is present) …
example : chkL prog{ Refl }
  prog{ Id (List (Σ (k : Nat). Nat)) (InsL 3 99 %b0)
           Cons(Pair(1, 10), Cons(Pair(3, 99), Nil)) } = true := by native_decide
-- … and appends at the tail (the key is absent), which is `insert_in_list`'s own shape.
example : chkL prog{ Refl }
  prog{ Id (List (Σ (k : Nat). Nat)) (InsL 5 50 %b0)
           Cons(Pair(1, 10), Cons(Pair(3, 30), Cons(Pair(5, 50), Nil))) } = true := by
  native_decide
example : chkL prog{ Refl }
  prog{ Id (List (Σ (k : Nat). Nat)) (RemL 1 %b0) Cons(Pair(3, 30), Nil) } = true := by
  native_decide

end Dllbc.Tests.HashMap
end
