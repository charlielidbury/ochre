/-
  Ochr.Model.Slice: a Lean check of test 0 of `ochr/docs/23` (does the set model exist, on a
  slice of the calculus?). Standalone: imports Lean core only, is not imported by `Ochr.lean`,
  and is checked with `lake env lean Ochr/Model/Slice.lean` from `ochr/core/lean`.

  Encoding.
  * §1. A type means a `SemTy`: a carrier with its good elements, which is docs/18's injectivity
    relation R paired in. Type formers are combinators on `SemTy`. Ochr's `Type₀` means
    `SemTy.{0}` itself, every semantic type of level 0, as `V_κ₀` does in the set model, so there
    is no universe of codes and no induction-recursion.
  * §2. Sanity theorems on the combinators, and a finding about pairing.
  * §3. A raw syntax of the slice, interpreted by one structurally recursive function.
  * §4. A type function defined by recursion on `Nat` (`Cells`), interpreted by stages.
-/
set_option autoImplicit false

namespace Ochr.Model

universe u

/-- A semantic type: its carrier, and which of its elements are good (docs/18's R). -/
structure SemTy : Type (u+1) where
  car  : Type u
  good : car → Prop

namespace SemTy

/-- `Nat`: every numeral is good. -/
def nat : SemTy.{u} := ⟨ULift Nat, fun _ => True⟩
/-- `Unit`. -/
def unit : SemTy.{u} := ⟨PUnit, fun _ => True⟩
/-- What an ill-formed term means. No derivation reaches it. -/
def err : SemTy.{u} := ⟨PEmpty, fun _ => False⟩
/-- A proposition used as a type: at most one element, so proof irrelevance holds. -/
def ofProp (P : Prop) : SemTy.{u} := ⟨ULift (PLift P), fun _ => True⟩
/-- A pair: good when both components are. -/
def pair (A B : SemTy.{u}) : SemTy.{u} := ⟨A.car × B.car, fun p => A.good p.1 ∧ B.good p.2⟩
/-- Π with a data codomain: a good function sends good arguments to good results. -/
def pi (A : SemTy.{u}) (B : A.car → SemTy.{u}) : SemTy.{u} :=
  ⟨(a : A.car) → (B a).car, fun f => ∀ a, A.good a → (B a).good (f a)⟩
/-- Π into a proposition: the truth value "true at every good argument". It is a `Prop` however
large `A` is, which is impredicativity. -/
def piProp (A : SemTy.{u}) (P : A.car → Prop) : Prop := ∀ a, A.good a → P a
/-- `Π(x : &T). B`, with `B` borrow-free data: the result and the final content of `*x`. -/
def brw (T : SemTy.{u}) (B : T.car → SemTy.{u}) : SemTy.{u} :=
  ⟨(d : T.car) → (B d).car × T.car,
   fun F => ∀ d, T.good d → (B d).good (F d).1 ∧ T.good (F d).2⟩
/-- `Π(x : &T). &U`: what the returned borrow holds at return, and the backward function from the
value the caller leaves in it to the final content of `*x`. R asks that the backward function map
good values to good ones and be injective on them (docs/18, the injectivity relation). -/
def brwRet (T : SemTy.{u}) (U : T.car → SemTy.{u}) : SemTy.{u} :=
  ⟨(d : T.car) → (U d).car × ((U d).car → T.car),
   fun F => ∀ d, T.good d → (U d).good (F d).1 ∧
     (∀ v, (U d).good v → T.good ((F d).2 v)) ∧
     (∀ v w, (U d).good v → (U d).good w → (F d).2 v = (F d).2 w → v = w)⟩
/-- `Type₀`, a type of level 1: every semantic type of level 0, each good. -/
def univ : SemTy.{u+1} := ⟨SemTy.{u}, fun _ => True⟩
/-- `Prop`, a type of level 1 beside `Type₀`. -/
def prop : SemTy.{u+1} := ⟨ULift.{u+1} Prop, fun _ => True⟩
/-- A level-0 type seen at level 1 (neither Ochr nor Lean is cumulative, so this is explicit). -/
def lift (A : SemTy.{u}) : SemTy.{u+1} := ⟨ULift.{u+1} A.car, fun a => A.good a.down⟩

end SemTy

/-! ## §2. Sanity theorems on the combinators -/

/-- `False` used as a type has no elements. -/
theorem false_empty : ∀ _x : (SemTy.ofProp.{u} False).car, False := fun x => x.down.down

/-- The meaning of `TailM (x : &Nat) : &Nat`'s type (docs/18). -/
abbrev TailMTy : SemTy.{0} := SemTy.brwRet SemTy.nat fun _ => SemTy.nat

/-- `TailM` itself: started with `n` in `*x`, the returned borrow holds the final `Z`, and leaving
`v` in it makes `*x` finally `n + v`. -/
def tailM : TailMTy.car := fun n => (⟨0⟩, fun v => ⟨n.down + v.down⟩)

/-- `TailM` is good: its backward function is injective. -/
theorem tailM_good : TailMTy.good tailM := by
  intro d _
  refine ⟨trivial, fun _ _ => trivial, ?_⟩
  intro v w _ _ h
  have h' : d.down + v.down = d.down + w.down := congrArg ULift.down h
  exact congrArg ULift.up (Nat.add_left_cancel h')

/-- Π into a proposition over `Type₀` is a `Prop`, although it quantifies over `SemTy.{0}`,
which lives in `Type 1`. -/
example (P : SemTy.{0} → Prop) : Prop := SemTy.piProp SemTy.univ P

/-! ### A finding about pairing: R must reach equality, or carriers must hold only good elements

With R paired in as a predicate on a carrier, a carrier still holds ill-behaved elements, such as
a borrow-returning function with a constant backward function. Two good functions out of such a
type can agree on every good argument and still differ as elements of the carrier. Ochr's
conversion compares functions by their generic call, so an unknown argument ranges over the
domain's meaning, its good elements: it identifies `f0` and `f1` below. `⟦Eq⟧` must then compare
functions on good arguments only, which makes each type a carrier with a partial equivalence
relation and not just a predicate. Or carriers hold only good elements (the `…R` definitions after
the theorems), and then R is the meaning itself and needs no second component. -/

/-- An element of `TailMTy`'s carrier that is not good: its backward function is constant. -/
def junk : TailMTy.car := fun _ => (⟨0⟩, fun _ => ⟨0⟩)

theorem junk_not_good : ¬ TailMTy.good junk := by
  intro h
  have e := (h ⟨0⟩ trivial).2.2 ⟨0⟩ ⟨1⟩ trivial trivial rfl
  exact Nat.zero_ne_one (congrArg ULift.down e)

/-- Two functions out of `TailMTy`, both good, since every `Nat` is good. -/
def f0 : (SemTy.pi TailMTy fun _ => SemTy.nat).car := fun _ => ⟨0⟩
def f1 : (SemTy.pi TailMTy fun _ => SemTy.nat).car :=
  fun h => if ((h ⟨0⟩).2 ⟨0⟩).down = ((h ⟨0⟩).2 ⟨1⟩).down then ⟨1⟩ else ⟨0⟩

/-- `f0` and `f1` agree on every good argument. -/
theorem f0_f1_agree_on_good : ∀ h, TailMTy.good h → f0 h = f1 h := by
  intro h hg
  have hinj := (hg ⟨0⟩ trivial).2.2 ⟨0⟩ ⟨1⟩ trivial trivial
  unfold f0 f1
  by_cases heq : ((h ⟨0⟩).2 ⟨0⟩).down = ((h ⟨0⟩).2 ⟨1⟩).down
  · exact (Nat.zero_ne_one (congrArg ULift.down (hinj (congrArg ULift.up heq)))).elim
  · exact (if_neg heq).symm

/-- …but they are different elements of the carrier: they differ at `junk`. -/
theorem f0_ne_f1 : f0 ≠ f1 := by
  intro h
  have e := congrArg ULift.down (congrFun h junk)
  simp [f0, f1, junk] at e

/-- The alternative: the meaning of `Π(x : &Nat). &Nat` holds only the good functions, so R is
folded into the carrier. Functions out of it are then equal when they agree on every element,
by function extensionality. -/
def TailMTyR : Type := {F : Nat → Nat × (Nat → Nat) // ∀ d v w, (F d).2 v = (F d).2 w → v = w}

def tailMR : TailMTyR := ⟨fun n => (0, fun v => n + v), fun _ _ _ h => Nat.add_left_cancel h⟩

theorem funext_on_restricted (f g : TailMTyR → Nat) (h : ∀ x, f x = g x) : f = g := funext h
