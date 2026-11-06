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

/-! ## §3. A raw syntax of the slice, and its interpretation

One grammar for types and for the `Nat` terms that types mention, as in Ochr, with de Bruijn
indices. The interpretation `I` is a single function, structurally recursive on the term. It needs
no universe of codes, because the meaning of `Type₀` is `SemTy.{0}` itself. It is total, and an
ill-formed term means `err` (no derivation reaches one). -/

/-- The slice's terms. Π's class (returns data, returns a proof) and whether it returns a borrow
are read off syntax, as Ochr reads them off the codomain term. -/
inductive Tm where
  | var (i : Nat)
  | nat | unit | type0 | prop | false_
  | zero | succ (t : Tm)
  | eqN (a b : Tm)               -- Eq(Nat, a, b)
  | pair (a b : Tm)
  | pi (dom cod : Tm)            -- Π(x : dom). cod, cod data or a type
  | piP (dom cod : Tm)           -- Π(x : dom). cod, cod a proposition
  | brw (t cod : Tm)             -- Π(x : &t). cod, cod borrow-free data
  | brwRet (t cod : Tm)          -- Π(x : &t). &cod
  | caseN (n z s : Tm)           -- match n { Z => z, S(m) => s }, m bound in s
  | call (g : Nat) (a b : Tm)    -- g(a, b), a global type function (A : Type₀) (n : Nat) : Type₀
  | self (a b : Tm)              -- the recursive call, inside a type function's body
  deriving Inhabited

/-- What a variable stands for. The tag is the variable's declared sort, which Ochr reads off
syntax (sorts are syntactic). -/
inductive Entry : Type 2 where
  | ty (A : SemTy.{0})                 -- a type, a value of `Type₀`
  | nat (n : Nat)                      -- a numeral
  | prf (P : Prop)                     -- a proposition, a value of `Prop`
  | val (A : SemTy.{0}) (a : A.car)    -- a value of another level-0 type

/-- What a term means: a level-0 type, a level-1 type, a proposition, a numeral, or nothing. -/
inductive Den : Type 2 where
  | ty0 (A : SemTy.{0})
  | ty1 (A : SemTy.{1})
  | prop (P : Prop)
  | num (n : Nat)
  | none

namespace Den
/-- Read as a level-0 type; a proposition is a type with at most one element. -/
def asTy0 : Den → SemTy.{0}
  | ty0 A => A | prop P => SemTy.ofProp P | _ => SemTy.err
/-- Read as a level-1 type. -/
def asTy1 : Den → SemTy.{1}
  | ty1 A => A | ty0 A => SemTy.lift A | prop P => SemTy.ofProp P | _ => SemTy.err
/-- Read as a proposition. -/
def asProp : Den → Prop
  | prop P => P | _ => False
/-- Read as a numeral. -/
def asNum : Den → Nat
  | num n => n | _ => 0
end Den

/-- Whether a type term lives at level 1, read off syntax: a sort, or a Π over a sort or into a
level-1 type. -/
def Tm.isLevel1 : Tm → Bool
  | .type0 => true
  | .prop => true
  | .pi .type0 _ => true
  | .pi .prop _ => true
  | .pi _ c => c.isLevel1
  | _ => false

/-- The meanings of the earlier global type functions, applied to their arguments' entries. -/
abbrev Globals : Type 2 := List (List Entry → SemTy.{0})

/-- The interpretation. `G` gives the meanings of the earlier global type functions, and `S` the
meaning of the type function whose body is being read, at the arguments of a recursive call. -/
def I (G : Globals) (S : List Entry → SemTy.{0}) : Tm → List Entry → Den
  | .var i, env =>
    match env[i]? with
    | some (.ty A) => .ty0 A
    | some (.nat n) => .num n
    | some (.prf P) => .prop P
    | _ => .none
  | .nat, _ => .ty0 SemTy.nat
  | .unit, _ => .ty0 SemTy.unit
  | .type0, _ => .ty1 SemTy.univ
  | .prop, _ => .ty1 SemTy.prop
  | .false_, _ => .prop False
  | .zero, _ => .num 0
  | .succ t, env => .num ((I G S t env).asNum + 1)
  | .eqN a b, env => .prop ((I G S a env).asNum = (I G S b env).asNum)
  | .pair a b, env => .ty0 (SemTy.pair (I G S a env).asTy0 (I G S b env).asTy0)
  | .pi d c, env =>
    match d, c.isLevel1 with
    | .type0, _ => .ty1 (SemTy.pi SemTy.univ fun A => (I G S c (.ty A :: env)).asTy1)
    | .prop, _ => .ty1 (SemTy.pi SemTy.prop fun P => (I G S c (.prf P.down :: env)).asTy1)
    | .nat, true =>
      .ty1 (SemTy.pi (SemTy.lift SemTy.nat) fun n => (I G S c (.nat n.down.down :: env)).asTy1)
    | .nat, false =>
      .ty0 (SemTy.pi SemTy.nat fun n => (I G S c (.nat n.down :: env)).asTy0)
    | _, true =>
      let A := (I G S d env).asTy0
      .ty1 (SemTy.pi (SemTy.lift A) fun a => (I G S c (.val A a.down :: env)).asTy1)
    | _, false =>
      let A := (I G S d env).asTy0
      .ty0 (SemTy.pi A fun a => (I G S c (.val A a :: env)).asTy0)
  | .piP d c, env =>
    match d with
    | .type0 => .prop (∀ A : SemTy.{0}, (I G S c (.ty A :: env)).asProp)
    | .prop => .prop (∀ P : Prop, (I G S c (.prf P :: env)).asProp)
    | .nat => .prop (∀ n : Nat, (I G S c (.nat n :: env)).asProp)
    | _ =>
      let A := (I G S d env).asTy0
      .prop (SemTy.piProp A fun a => (I G S c (.val A a :: env)).asProp)
  | .brw t c, env =>
    match t with
    | .nat => .ty0 (SemTy.brw SemTy.nat fun n => (I G S c (.nat n.down :: env)).asTy0)
    | _ =>
      let T := (I G S t env).asTy0
      .ty0 (SemTy.brw T fun d => (I G S c (.val T d :: env)).asTy0)
  | .brwRet t c, env =>
    match t with
    | .nat => .ty0 (SemTy.brwRet SemTy.nat fun n => (I G S c (.nat n.down :: env)).asTy0)
    | _ =>
      let T := (I G S t env).asTy0
      .ty0 (SemTy.brwRet T fun d => (I G S c (.val T d :: env)).asTy0)
  | .caseN n z s, env =>
    match (I G S n env).asNum with
    | 0 => I G S z env
    | m + 1 => I G S s (.nat m :: env)
  | .call g a b, env =>
    match G[g]? with
    | some F => .ty0 (F [.nat (I G S b env).asNum, .ty (I G S a env).asTy0])
    | none => .none
  | .self a b, env => .ty0 (S [.nat (I G S b env).asNum, .ty (I G S a env).asTy0])

/-! ## §4. Type functions by recursion on `Nat`, by stages

A global type function `F (A : Type₀) (n : Nat) : Type₀ := body`, structural on `n`, means the
function whose value at `n` is stage `n + 1`. Stage `k + 1` reads the body with stage `k` answering
the recursive call. The definition needs nothing of the body, so it exists whatever the body is.
That it satisfies `F`'s defining equation, which is what a step that unfolds a call needs, holds
when every recursive call is at a smaller `n`. That is [Rec]'s obligation, and it is why "every
closure and global has passed [Rec]" is part of the well-formedness invariant (docs/23). -/

/-- Stage `k` of a type function with body `body`. Its arguments are `[.nat n, .ty A]`. -/
def stage (G : Globals) (body : Tm) : Nat → List Entry → SemTy.{0}
  | 0 => fun _ => SemTy.err
  | k + 1 => fun args => (I G (stage G body k) body args).asTy0

/-- The meaning of the type function: at `n`, stage `n + 1`. -/
def tfun (G : Globals) (body : Tm) (args : List Entry) : SemTy.{0} :=
  match args with
  | .nat n :: _ => stage G body (n + 1) args
  | _ => SemTy.err

/-- `Cells (E : Type₀) (n : Nat) : Type₀ := match n { Z => Unit, S(m) => Pair(E, Cells(E, m)) }`.
In the body `var 0` is `n` and `var 1` is `E`; in the `S` arm `var 0` is `m` and `var 2` is `E`. -/
def cellsBody : Tm := .caseN (.var 0) .unit (.pair (.var 2) (.self (.var 2) (.var 0)))

/-- `Cells`'s meaning, at `E` and `n`. -/
def cells (E : SemTy.{0}) (n : Nat) : SemTy.{0} := tfun [] cellsBody [.nat n, .ty E]

/-- `Cells(E, Z) = Unit`. -/
theorem cells_zero (E : SemTy.{0}) : cells E 0 = SemTy.unit := rfl

/-- `Cells(E, S(n)) = Pair(E, Cells(E, n))`: the staged meaning satisfies `Cells`'s defining
equation, since its one recursive call is at the predecessor. -/
theorem cells_succ (E : SemTy.{0}) (n : Nat) :
    cells E (n + 1) = SemTy.pair E (cells E n) := rfl

/-- A type whose codomain is computed by the type function: `Π(n : Nat). Cells(E, n)`, with `E` a
type variable, read with `Cells` as global 0. The codomain's meaning comes from `Cells`'s meaning at
each `n`, with no recursion on the codomain's syntax beyond the call. -/
theorem pi_cells (E : SemTy.{0}) :
    I [tfun [] cellsBody] (fun _ => SemTy.err) (.pi .nat (.call 0 (.var 1) (.var 0))) [.ty E]
      = .ty0 (SemTy.pi SemTy.nat fun n => cells E n.down) := rfl

/-! ## §5. Sanity theorems on the syntax -/

section
variable (G : Globals) (S : List Entry → SemTy.{0}) (env : List Entry)

/-- `False`, read as a type, has no elements. -/
theorem I_false_empty : ∀ _x : (I G S .false_ env).asTy0.car, False := fun x => x.down.down

/-- `TailM`'s type, `Π(x : &Nat). &Nat`, means `TailMTy`; so `tailM` is an element, and a good one. -/
theorem I_tailM : (I G S (.brwRet .nat .nat) env).asTy0 = TailMTy := rfl
example : (I G S (.brwRet .nat .nat) env).asTy0.good tailM := tailM_good

/-- R at a type variable is the variable's own component: nothing to recurse on is needed. -/
theorem I_tyvar_good (A : SemTy.{0}) : (I G S (.var 0) (.ty A :: env)).asTy0.good = A.good := rfl

/-- `Π(A : Type₀). P(A)`, with `P` a proposition, is a proposition: a `Prop` quantifying over
`SemTy.{0} : Type 1` (impredicativity). -/
theorem I_piP_type0 (c : Tm) :
    I G S (.piP .type0 c) env = .prop (∀ A : SemTy.{0}, (I G S c (.ty A :: env)).asProp) := rfl

/-- For instance `Π(A : Type₀). Eq(Nat, Z, Z)` is true. -/
example : (I G S (.piP .type0 (.eqN .zero .zero)) env).asProp := fun _ => rfl

/-- The same quantifier into data is not small: `Π(A : Type₀). Π(x : A). A` lives at level 1. -/
theorem I_poly_id_level1 :
    I G S (.pi .type0 (.pi (.var 0) (.var 1))) env
      = .ty1 (SemTy.pi SemTy.univ fun A => SemTy.lift (SemTy.pi A fun _ => A)) := rfl

/-- The polymorphic identity is a good element of it. -/
example : (SemTy.pi SemTy.univ.{0} fun A => SemTy.lift (SemTy.pi A fun _ => A)).good
    (fun _ => ⟨fun a => a⟩) := fun _ _ => fun _ ha => ha

/-- `Type₀ : Type₁` and `Prop : Type₁`: both mean level-1 types. -/
theorem I_type0 : I G S .type0 env = .ty1 SemTy.univ := rfl
theorem I_prop : I G S .prop env = .ty1 SemTy.prop := rfl
end

end Ochr.Model

#print axioms Ochr.Model.I
#print axioms Ochr.Model.tfun
#print axioms Ochr.Model.tailM_good
#print axioms Ochr.Model.f0_f1_agree_on_good
#print axioms Ochr.Model.f0_ne_f1
#print axioms Ochr.Model.cells_succ
#print axioms Ochr.Model.pi_cells
#print axioms Ochr.Model.I_false_empty
#print axioms Ochr.Model.I_tailM
#print axioms Ochr.Model.I_tyvar_good
#print axioms Ochr.Model.I_piP_type0
#print axioms Ochr.Model.I_poly_id_level1
