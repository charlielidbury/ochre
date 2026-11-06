/-
  Ochr.Model.Slice: a Lean check of test 0 of `ochr/docs/23` (does the set model exist, on a
  slice of the calculus?). Standalone: imports Lean core only, is not imported by `Ochr.lean`,
  and is checked with `lake env lean Ochr/Model/Slice.lean` from `ochr/core/lean`.

  Encoding.
  * §1. A type means a Lean type holding only its good elements: docs/18's injectivity relation R
    is folded into the carrier, so it is not a second component. The meaning of `Π(x : &T). &U`
    holds only functions whose backward function is injective. Ochr's `Type₀` means `Type`, every
    type of level 0, as `V_κ₀` does in the set model, so there is no universe of codes and no
    induction-recursion.
  * §2. Sanity theorems on the combinators, and extensionality, which conversion of functions
    ([Conv-fun]) needs.
  * §3. A raw syntax of the slice, interpreted by one structurally recursive function.
  * §4. Type functions defined by recursion on `Nat`, by stages; the general stabilisation lemma
    (the semantic form of [Rec]), checked on `Cells` (recursion at `n - 1`) and `Alt` (`n - 2`).
  * §5. Sanity theorems on the syntax.
  * §6. Why R is not paired in as a predicate: the counterexample.
-/
set_option autoImplicit false

namespace Ochr.Model

universe u

/-! ## §1. Meanings of types: carriers holding only good elements -/

namespace Sem

/-- `Nat`. -/
abbrev nat : Type u := ULift Nat
/-- `Unit`. -/
abbrev unit : Type u := PUnit
/-- What an ill-formed term means. No derivation reaches one. -/
abbrev err : Type u := PEmpty
/-- A proposition used as a type: at most one element, so proof irrelevance holds. -/
abbrev ofProp (P : Prop) : Type u := ULift (PLift P)
/-- A pair. -/
abbrev pair (A B : Type u) : Type u := A × B
/-- Π with a data codomain. -/
abbrev pi (A : Type u) (B : A → Type u) : Type u := (a : A) → B a
/-- Π into a proposition: a `Prop` however large `A` is (impredicativity). -/
abbrev piProp (A : Type u) (P : A → Prop) : Prop := ∀ a, P a
/-- `Π(x : &T). B`, with `B` borrow-free data: the result and the final content of `*x`. -/
abbrev brw (T : Type u) (B : T → Type u) : Type u := (d : T) → B d × T
/-- What a call returning `&U` from a borrow of `T` gives back: what the returned borrow holds at
return, and an injective backward function from the value the caller leaves in it to the final
content of the lent place. Injectivity is part of the carrier (docs/18's R). -/
abbrev Back (T U : Type u) : Type u := {p : U × (U → T) // ∀ v w, p.2 v = p.2 w → v = w}
/-- `Π(x : &T). &U`. -/
abbrev brwRet (T : Type u) (U : T → Type u) : Type u := (d : T) → Back T (U d)
/-- `Type₀`, a type of level 1: every type of level 0. -/
abbrev univ : Type (u+1) := Type u
/-- `Prop`, a type of level 1 beside `Type₀`. -/
abbrev prop : Type (u+1) := ULift.{u+1} Prop
/-- A level-0 type seen at level 1 (neither Ochr nor Lean is cumulative). -/
abbrev lift (A : Type u) : Type (u+1) := ULift.{u+1} A

end Sem

/-! ## §2. Sanity theorems on the combinators -/

/-- `False` used as a type has no elements. -/
theorem false_empty : ∀ _x : Sem.ofProp.{u} False, False := fun x => x.down.down

/-- The meaning of `TailM (x : &Nat) : &Nat`'s type (docs/18). -/
abbrev TailMTy : Type := Sem.brwRet Sem.nat fun _ => Sem.nat

/-- `TailM`: started with `n` in `*x`, the returned borrow holds the final `Z`, and leaving `v` in
it makes `*x` finally `n + v`. It is an element only because that backward function is injective. -/
def tailM : TailMTy := fun n =>
  ⟨(⟨0⟩, fun v => ⟨n.down + v.down⟩), fun _ _ h =>
    congrArg ULift.up (Nat.add_left_cancel (congrArg ULift.down h))⟩

/-- Junk is excluded by construction: no element of `TailM`'s type has a backward function that
sends `0` and `1` to the same final content, so the constant one is not there. -/
theorem tailMTy_no_junk (F : TailMTy) (d : Sem.nat) : (F d).val.2 ⟨0⟩ ≠ (F d).val.2 ⟨1⟩ :=
  fun h => Nat.zero_ne_one (congrArg ULift.down ((F d).property _ _ h))

/-- Extensionality for Π, with no side condition: two functions that agree at every argument are
equal. This is what conversion of functions by their generic call ([Conv-fun]) needs, since the
generic argument ranges over the whole domain, which is now exactly the domain's meaning. -/
theorem pi_ext {A : Type u} {B : A → Type u} (f g : Sem.pi A B) (h : ∀ a, f a = g a) : f = g :=
  funext h

/-- Extensionality for borrow-returning functions: equal outputs at every argument. -/
theorem brwRet_ext {T : Type u} {U : T → Type u} (F G : Sem.brwRet T U)
    (h : ∀ d, (F d).val = (G d).val) : F = G :=
  funext fun d => Subtype.ext (h d)

/-- Two functions out of `TailM`'s type: `f0` is constantly `0`; `f1` answers `1` when the backward
function at `0` sends `0` and `1` to the same content. With R as a predicate on a larger carrier
they differ at junk (§6); here they are equal. -/
def f0 : Sem.pi TailMTy fun _ => Sem.nat := fun _ => ⟨0⟩
def f1 : Sem.pi TailMTy fun _ => Sem.nat :=
  fun h => if ((h ⟨0⟩).val.2 ⟨0⟩).down = ((h ⟨0⟩).val.2 ⟨1⟩).down then ⟨1⟩ else ⟨0⟩

theorem f0_eq_f1 : f0 = f1 :=
  pi_ext f0 f1 fun h => by
    have hne : ¬ ((h ⟨0⟩).val.2 ⟨0⟩).down = ((h ⟨0⟩).val.2 ⟨1⟩).down :=
      fun e => tailMTy_no_junk h ⟨0⟩ (congrArg ULift.up e)
    exact (if_neg hne).symm

/-- `Π(A : Type₀). P(A)` is a `Prop` although it quantifies over `Type`, which lives in `Type 1`. -/
example (P : Type → Prop) : Prop := Sem.piProp Sem.univ P

/-! ## §3. A raw syntax of the slice, and its interpretation

One grammar for types and for the `Nat` terms that types mention, as in Ochr, with de Bruijn
indices. The interpretation `I` is a single function, structurally recursive on the term. It needs
no universe of codes, because the meaning of `Type₀` is `Type` itself. It is total, and an
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
inductive Entry : Type 1 where
  | ty (A : Type)                -- a type, a value of `Type₀`
  | nat (n : Nat)                -- a numeral
  | prf (P : Prop)               -- a proposition, a value of `Prop`
  | val (A : Type) (a : A)       -- a value of another level-0 type

/-- What a term means: a level-0 type, a level-1 type, a proposition, a numeral, or nothing. -/
inductive Den : Type 2 where
  | ty0 (A : Type)
  | ty1 (A : Type 1)
  | prop (P : Prop)
  | num (n : Nat)
  | none

namespace Den
/-- Read as a level-0 type; a proposition is a type with at most one element. -/
def asTy0 : Den → Type
  | ty0 A => A | prop P => Sem.ofProp P | _ => Sem.err
/-- Read as a level-1 type. -/
def asTy1 : Den → Type 1
  | ty1 A => A | ty0 A => Sem.lift A | prop P => Sem.ofProp P | _ => Sem.err
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
abbrev Globals : Type 1 := List (List Entry → Type)

/-- The interpretation. `G` gives the meanings of the earlier global type functions, and `S` the
meaning of the type function whose body is being read, at the arguments of a recursive call. -/
def I (G : Globals) (S : List Entry → Type) : Tm → List Entry → Den
  | .var i, env =>
    match env[i]? with
    | some (.ty A) => .ty0 A
    | some (.nat n) => .num n
    | some (.prf P) => .prop P
    | _ => .none
  | .nat, _ => .ty0 Sem.nat
  | .unit, _ => .ty0 Sem.unit
  | .type0, _ => .ty1 Sem.univ
  | .prop, _ => .ty1 Sem.prop
  | .false_, _ => .prop False
  | .zero, _ => .num 0
  | .succ t, env => .num ((I G S t env).asNum + 1)
  | .eqN a b, env => .prop ((I G S a env).asNum = (I G S b env).asNum)
  | .pair a b, env => .ty0 (Sem.pair (I G S a env).asTy0 (I G S b env).asTy0)
  | .pi d c, env =>
    match d, c.isLevel1 with
    | .type0, _ => .ty1 (Sem.pi Sem.univ fun A => (I G S c (.ty A :: env)).asTy1)
    | .prop, _ => .ty1 (Sem.pi Sem.prop fun P => (I G S c (.prf P.down :: env)).asTy1)
    | .nat, true =>
      .ty1 (Sem.pi (Sem.lift Sem.nat) fun n => (I G S c (.nat n.down.down :: env)).asTy1)
    | .nat, false => .ty0 (Sem.pi Sem.nat fun n => (I G S c (.nat n.down :: env)).asTy0)
    | _, true =>
      let A := (I G S d env).asTy0
      .ty1 (Sem.pi (Sem.lift A) fun a => (I G S c (.val A a.down :: env)).asTy1)
    | _, false =>
      let A := (I G S d env).asTy0
      .ty0 (Sem.pi A fun a => (I G S c (.val A a :: env)).asTy0)
  | .piP d c, env =>
    match d with
    | .type0 => .prop (∀ A : Type, (I G S c (.ty A :: env)).asProp)
    | .prop => .prop (∀ P : Prop, (I G S c (.prf P :: env)).asProp)
    | .nat => .prop (∀ n : Nat, (I G S c (.nat n :: env)).asProp)
    | _ =>
      let A := (I G S d env).asTy0
      .prop (Sem.piProp A fun a => (I G S c (.val A a :: env)).asProp)
  | .brw t c, env =>
    match t with
    | .nat => .ty0 (Sem.brw Sem.nat fun n => (I G S c (.nat n.down :: env)).asTy0)
    | _ =>
      let T := (I G S t env).asTy0
      .ty0 (Sem.brw T fun d => (I G S c (.val T d :: env)).asTy0)
  | .brwRet t c, env =>
    match t with
    | .nat => .ty0 (Sem.brwRet Sem.nat fun n => (I G S c (.nat n.down :: env)).asTy0)
    | _ =>
      let T := (I G S t env).asTy0
      .ty0 (Sem.brwRet T fun d => (I G S c (.val T d :: env)).asTy0)
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
It satisfies `F`'s defining equation when every recursive call is at a smaller `n`
(`Decreasing`, the semantic form of [Rec]): then stage `k` at `m` is the same for every `k > m`
(`stage_stable`), and the equation follows (`tfun_eq`). -/

/-- Stage `k` of a type function with body `body`. Its arguments are `[.nat n, .ty A]`. -/
def stage (G : Globals) (body : Tm) : Nat → List Entry → Type
  | 0 => fun _ => Sem.err
  | k + 1 => fun args => (I G (stage G body k) body args).asTy0

/-- The meaning of the type function: at `n`, stage `n + 1`. -/
def tfun (G : Globals) (body : Tm) (args : List Entry) : Type :=
  match args with
  | .nat n :: _ => stage G body (n + 1) args
  | _ => Sem.err

/-- The semantic form of [Rec]: reading `body` at `n` consults the recursive call only at
arguments whose `Nat` is below `n`. (Every recursive call `I` makes has arguments
`[.nat m, .ty B]`.) -/
def Decreasing (G : Globals) (body : Tm) : Prop :=
  ∀ (n : Nat) (A : Type) (S S' : List Entry → Type),
    (∀ m, m < n → ∀ B : Type, S [.nat m, .ty B] = S' [.nat m, .ty B]) →
    (I G S body [.nat n, .ty A]).asTy0 = (I G S' body [.nat n, .ty A]).asTy0

/-- Stabilisation: for a decreasing body, stage `k` at `m` is stage `m + 1` at `m`, for every
`k > m`. By strong induction on `m`. -/
theorem stage_stable {G : Globals} {body : Tm} (hd : Decreasing G body) :
    ∀ (m k : Nat) (B : Type), m < k →
      stage G body k [.nat m, .ty B] = stage G body (m + 1) [.nat m, .ty B] := by
  intro m
  induction m using Nat.strongRecOn with
  | _ m ih =>
    intro k B hk
    match k, hk with
    | j + 1, hk =>
      show (I G (stage G body j) body [.nat m, .ty B]).asTy0
        = (I G (stage G body m) body [.nat m, .ty B]).asTy0
      apply hd
      intro m' hm' B'
      rw [ih m' hm' j B' (by omega), ih m' hm' m B' hm']

/-- The defining equation: for a decreasing body, the type function's meaning at `n` is its body
read at `n` with the recursive call answered by the type function itself. -/
theorem tfun_eq {G : Globals} {body : Tm} (hd : Decreasing G body) (n : Nat) (A : Type) :
    tfun G body [.nat n, .ty A] = (I G (tfun G body) body [.nat n, .ty A]).asTy0 := by
  show (I G (stage G body n) body [.nat n, .ty A]).asTy0 = _
  apply hd
  intro m hm B
  exact stage_stable hd m n B hm

/-- `Cells (E : Type₀) (n : Nat) : Type₀ := match n { Z => Unit, S(m) => Pair(E, Cells(E, m)) }`.
In the body `var 0` is `n` and `var 1` is `E`; in the `S` arm `var 0` is `m` and `var 2` is `E`. -/
def cellsBody : Tm := .caseN (.var 0) .unit (.pair (.var 2) (.self (.var 2) (.var 0)))

/-- `Cells`'s meaning, at `E` and `n`. -/
def cells (E : Type) (n : Nat) : Type := tfun [] cellsBody [.nat n, .ty E]

/-- `Cells`'s one recursive call is at `n - 1`. -/
theorem cells_dec : Decreasing [] cellsBody := by
  intro n A S S' h
  cases n with
  | zero => rfl
  | succ m =>
    show Sem.pair A (S [.nat m, .ty A]) = Sem.pair A (S' [.nat m, .ty A])
    rw [h m (Nat.lt_succ_self m) A]

theorem cells_zero (E : Type) : cells E 0 = Sem.unit := rfl
/-- From the general lemma; it also holds by `rfl`, since the call is at the predecessor. -/
theorem cells_succ (E : Type) (n : Nat) : cells E (n + 1) = Sem.pair E (cells E n) :=
  (tfun_eq cells_dec (n + 1) E).trans rfl
example (E : Type) (n : Nat) : cells E (n + 1) = Sem.pair E (cells E n) := rfl

/-- `Alt (E : Type₀) (n : Nat) : Type₀ :=
  match n { Z => Unit, S(m) => match m { Z => E, S(k) => Pair(E, Alt(E, k)) } }`: the recursive
call is at `n - 2`. In the inner `S` arm `var 0` is `k` and `var 3` is `E`. -/
def altBody : Tm :=
  .caseN (.var 0) .unit (.caseN (.var 0) (.var 2) (.pair (.var 3) (.self (.var 3) (.var 0))))

def alt (E : Type) (n : Nat) : Type := tfun [] altBody [.nat n, .ty E]

theorem alt_dec : Decreasing [] altBody := by
  intro n A S S' h
  match n with
  | 0 => rfl
  | 1 => rfl
  | k + 2 =>
    show Sem.pair A (S [.nat k, .ty A]) = Sem.pair A (S' [.nat k, .ty A])
    rw [h k (by omega) A]

theorem alt_zero (E : Type) : alt E 0 = Sem.unit := rfl
theorem alt_one (E : Type) : alt E 1 = E := rfl
/-- Here `rfl` fails: stage `k + 3` answers the call with stage `k + 2` at `k`, while `alt E k` is
stage `k + 1` at `k`. Stabilisation identifies them. -/
theorem alt_succ_succ (E : Type) (k : Nat) : alt E (k + 2) = Sem.pair E (alt E k) :=
  (tfun_eq alt_dec (k + 2) E).trans rfl
example (E : Type) (k : Nat) : alt E (k + 2) = Sem.pair E (alt E k) := by
  fail_if_success rfl
  exact alt_succ_succ E k

/-- A type whose codomain is computed by a type function: `Π(n : Nat). Cells(E, n)`, with `E` a
type variable, read with `Cells` as global 0. -/
theorem pi_cells (E : Type) :
    I [tfun [] cellsBody] (fun _ => Sem.err) (.pi .nat (.call 0 (.var 1) (.var 0))) [.ty E]
      = .ty0 (Sem.pi Sem.nat fun n => cells E n.down) := rfl

/-! ## §5. Sanity theorems on the syntax -/

section
variable (G : Globals) (S : List Entry → Type) (env : List Entry)

/-- `False`, read as a type, has no elements. -/
theorem I_false_empty : ∀ _x : (I G S .false_ env).asTy0, False := fun x => x.down.down

/-- `TailM`'s type, `Π(x : &Nat). &Nat`, means `TailMTy`, of which `tailM` is an element. -/
theorem I_tailM : (I G S (.brwRet .nat .nat) env).asTy0 = TailMTy := rfl
example : (I G S (.brwRet .nat .nat) env).asTy0 := tailM

/-- A type variable means the type it stands for; there is no R to look up. -/
theorem I_tyvar (A : Type) : I G S (.var 0) (.ty A :: env) = .ty0 A := rfl

/-- `Π(A : Type₀). P(A)`, with `P` a proposition, is a proposition: a `Prop` quantifying over
`Type : Type 1` (impredicativity). -/
theorem I_piP_type0 (c : Tm) :
    I G S (.piP .type0 c) env = .prop (∀ A : Type, (I G S c (.ty A :: env)).asProp) := rfl

/-- For instance `Π(A : Type₀). Eq(Nat, Z, Z)` is true. -/
example : (I G S (.piP .type0 (.eqN .zero .zero)) env).asProp := fun _ => rfl

/-- The same quantifier into data is not small: `Π(A : Type₀). Π(x : A). A` lives at level 1… -/
theorem I_poly_id_level1 :
    I G S (.pi .type0 (.pi (.var 0) (.var 1))) env
      = .ty1 (Sem.pi Sem.univ fun A => Sem.lift (Sem.pi A fun _ => A)) := rfl

/-- …and the polymorphic identity is an element of it. -/
def polyId : Sem.pi Sem.univ.{0} fun A => Sem.lift (Sem.pi A fun _ => A) := fun _ => ⟨fun a => a⟩

/-- A function type taking a function that returns a borrow: `Π(g : Π(x : &Nat). &Nat). Nat`. Its
domain is `TailMTy`, which holds no junk (`tailMTy_no_junk`), so functions out of it are equal when
they agree at every argument (`f0_eq_f1`). -/
theorem I_takes_brwRet :
    I G S (.pi (.brwRet .nat .nat) .nat) env = .ty0 (Sem.pi TailMTy fun _ => Sem.nat) := rfl

/-- `Type₀ : Type₁` and `Prop : Type₁`: both mean level-1 types. -/
theorem I_type0 : I G S .type0 env = .ty1 Sem.univ := rfl
theorem I_prop : I G S .prop env = .ty1 Sem.prop := rfl
end

/-! ## §6. Why R is not paired in as a predicate

The first version of this file read a type as a carrier with a predicate of good elements. A
carrier then also holds ill-behaved elements, such as a borrow-returning function with a constant
backward function. Two good functions out of such a type can agree on every good argument and
still differ as elements of the carrier, so `⟦Eq⟧` at function types would have to compare on good
arguments only (a partial equivalence relation, not a predicate). With carriers holding only good
elements, as above, the same two functions are equal (`f0_eq_f1`). The counterexample: -/

namespace Paired

/-- A carrier with a predicate of good elements. -/
structure SemTy : Type 1 where
  car  : Type
  good : car → Prop

/-- `Π(x : &Nat). &Nat` with R as a predicate. -/
def tailMTy : SemTy :=
  ⟨Nat → Nat × (Nat → Nat), fun F => ∀ d v w, (F d).2 v = (F d).2 w → v = w⟩

/-- An element of the carrier that is not good: its backward function is constant. -/
def junk : tailMTy.car := fun _ => (0, fun _ => 0)

theorem junk_not_good : ¬ tailMTy.good junk := fun h => Nat.zero_ne_one (h 0 0 1 rfl)

def g0 : tailMTy.car → Nat := fun _ => 0
def g1 : tailMTy.car → Nat := fun h => if (h 0).2 0 = (h 0).2 1 then 1 else 0

/-- `g0` and `g1` agree on every good argument… -/
theorem agree_on_good : ∀ h, tailMTy.good h → g0 h = g1 h := fun h hg => by
  have hne : ¬ (h 0).2 0 = (h 0).2 1 := fun e => Nat.zero_ne_one (hg 0 0 1 e)
  exact (if_neg hne).symm

/-- …but differ as elements of the carrier, at `junk`. -/
theorem differ : g0 ≠ g1 := fun h => by
  have e := congrFun h junk
  simp [g0, g1, junk] at e

end Paired

end Ochr.Model

#print axioms Ochr.Model.I
#print axioms Ochr.Model.tailM
#print axioms Ochr.Model.tailMTy_no_junk
#print axioms Ochr.Model.pi_ext
#print axioms Ochr.Model.brwRet_ext
#print axioms Ochr.Model.f0_eq_f1
#print axioms Ochr.Model.stage_stable
#print axioms Ochr.Model.tfun_eq
#print axioms Ochr.Model.cells_succ
#print axioms Ochr.Model.alt_succ_succ
#print axioms Ochr.Model.pi_cells
#print axioms Ochr.Model.I_false_empty
#print axioms Ochr.Model.I_tailM
#print axioms Ochr.Model.I_tyvar
#print axioms Ochr.Model.I_piP_type0
#print axioms Ochr.Model.I_poly_id_level1
#print axioms Ochr.Model.I_takes_brwRet
#print axioms Ochr.Model.Paired.differ
