import Ochr.Machine

/-!
# The rules trial (docs/35 Theme 1): conversion and `Eq` as inductive relations (part R)

The paper's conversion (`appendix.typ`, "Conversion": [Conv-refl], [Conv-cong], [Conv-unit],
[Conv-pi], [Conv-fun]) and the computation of `Eq` ([Eq-refl], [Eq-inj], [Eq-disj], [Eq-stuck]),
one constructor per rule, each premise a check, never a search. The relations mention values, the
declarations (`Γ`, Σ's globals for a function's declared Π-type) and nothing of `MState`: no
tables, copies, flags, fuel or monad.

Three things are left abstract, as parameters (`Premises`), because each is a computation the
paper does not define by a rule of its own: the generic-call premise of [Conv-fun], the
generic-argument premise of [Conv-pi] (with its class and row conditions, which are decisions read
from the unknowns' frozen readings), and the field types [Eq-inj] takes the fields apart at. Part
A assumes their soundness (`Rules/Sound.lean`); part B instantiates them with "the machine's run of
exactly that sub-computation succeeded" (`Rules/Refine.lean`).

The two rules that the paper states without a type, and that the model can only validate at a
type, are parameterised (`Syn`): the syntactic equality [Conv-refl] uses, and where [Conv-unit]
may apply. The paper's (and the machine's) instance is `Syn.machine`: `==` (`Value.beq`), which
identifies values up to binder names AND ignores the parameters a constructor value records
("determined by its type", [Conv-cong]), and the unit laws everywhere. Part A is stated for any
instance whose two parts preserve meanings (`Rules/Sound.lean`), which the machine's does not at
ill-typed nested values (`Rules/ConvCE.lean`); so the instance part A can use differs from the one
part B produces, and the bridge is a typing fact about the values compared (part C).
-/

namespace Ochr.Meaning.Conv
open Ochr

/-- The untyped parts of conversion: the syntactic equality [Conv-refl] uses, on values and on
terms, and the values [Conv-unit] may rewrite. -/
structure Syn where
  v : Value → Value → Prop
  t : Term → Term → Prop
  unit : Value → Prop
  /-- [Conv-cong] on constructor values ignores the parameters they record -/
  ignoreParams : Bool

/-- The machine's: `Value.beq` and `Term.beq` (binder names and recorded parameters ignored), and
the unit laws at every value. -/
def Syn.machine : Syn := ⟨fun v w => (v == w) = true, fun t u => (t == u) = true, fun _ => True, true⟩

/-- Two Π-closures' or closures' recorded readings agree (`==` on `List (DeclInfo × Value)`, the
values by the syntactic equality). -/
def RdEq (E : Syn) : List (DeclInfo × Value) → List (DeclInfo × Value) → Prop
  | [], [] => True
  | (d, a) :: as, (e, b) :: bs => (d == e) = true ∧ E.v a b ∧ RdEq E as bs
  | _, _ => False

/-- The premises of the rules that the paper states about a computation it does not define by
rules: abstract here. -/
structure Premises where
  /-- [Conv-fun]: at the generic call of the first function's Π-type, with one generic state,
  arguments and owned places, the two observations are convertible -/
  fn : Value → Value → Prop
  /-- [Conv-pi]: same number of parameters, same class, both or neither returning a borrow, and at
  the generic arguments of the first the parameter types and the codomains pairwise convertible -/
  pi : Value → Value → Prop
  /-- [Eq-inj]: `Ts` are the field types of constructor `c` of `d` at the parameters `args`,
  computed from the fields `fs` (D64: a later field's type from the earlier fields) -/
  fieldTys : IndDecl → List Value → Nat → List Value → List Value → Prop

/-- A function value (`conv`'s `isFn`). -/
def isFnV : Value → Bool
  | .gfn _ | .clo _ _ _ => true
  | _ => false

/-- A function value's declared Π-type, read off the declarations or its own code (`funType` on a
function value: a global's stored type, a closure's `fix`). -/
def fnTyOf (gs : List GDef) : Value → Option Value
  | .gfn n => (gs.find? (·.name == n)).map (·.ty)
  | .clo cs (.fix _ hs ds c _ _) rd => some (.tPi cs (.pi hs ds c) rd)
  | _ => none

/-- A function value's captured values (none for a global). -/
def capsOf : Value → List Value
  | .clo cs _ _ => cs
  | _ => []

section
variable (E : Syn) (G : Premises) (gs : List GDef)

mutual
/-- **Conversion** `v ≡ w`: the least relation closed under the paper's rules. [Conv-refl] is
`E.v`; [Conv-unit] applies the unit laws at the head of both sides (`unitTop`), after which the
head rules (`ConvH`) compare them. -/
inductive ConvV : Value → Value → Prop
  /-- [Conv-refl] -/
  | refl {v w : Value} : E.v v w → ConvV v w
  /-- [Conv-unit]: convertible once the unit laws are applied to each side -/
  | unit {v w : Value} : E.unit v → E.unit w → ConvH (unitTop v) (unitTop w) → ConvV v w

/-- The head rules, on values after the unit laws. -/
inductive ConvH : Value → Value → Prop
  | refl {v w : Value} : E.v v w → ConvH v w
  /-- [Conv-cong], one constructor per former -/
  | succ {a b : Value} : ConvV a b → ConvH (.succ a) (.succ b)
  | tRef {a b : Value} : ConvV a b → ConvH (.tRef a) (.tRef b)
  | tInd {n : String} {as bs : List Value} : ConvL as bs → ConvH (.tInd n as) (.tInd n bs)
  | tEq {A a b B c d : Value} : ConvV A B → ConvV a c → ConvV b d → ConvH (.tEq A a b) (.tEq B c d)
  | borrow {l : Nat} {a b : Value} : ConvV a b → ConvH (.borrow l a) (.borrow l b)
  /-- a constructor value by its constructor and fields; the parameters it records are ignored
  (in the paper's and the machine's instance) -/
  | ind {t : String} {c : Nat} {h h' : Hint} {ps qs fs gs' : List Value} :
      (E.ignoreParams = false → ConvL ps qs) → ConvL fs gs' → ConvH (.ind t c h ps fs) (.ind t c h' qs gs')
  | sealed {t u : Term} : ConvT t u → ConvH (.sealed t) (.sealed u)
  /-- two Π-closures with convertible captures, read alike, and the same code -/
  | piCong {cs ds : List Value} {t u : Term} {r r' : List (DeclInfo × Value)} :
      RdEq E r r' → ConvL cs ds → ConvT t u → ConvH (.tPi cs t r) (.tPi ds u r')
  /-- [Conv-pi] -/
  | pi {cs ds : List Value} {t u : Term} {r r' : List (DeclInfo × Value)} :
      G.pi (.tPi cs t r) (.tPi ds u r') → ConvH (.tPi cs t r) (.tPi ds u r')
  /-- [Conv-fun]: convertible Π-types, convertible captures, and the generic-call premise -/
  | fn {f g pf pg : Value} : isFnV f = true → isFnV g = true → fnTyOf gs f = some pf →
      fnTyOf gs g = some pg → ConvV pf pg → ConvL (capsOf f) (capsOf g) → G.fn f g → ConvH f g

inductive ConvL : List Value → List Value → Prop
  | nil : ConvL [] []
  | cons {a b : Value} {as bs : List Value} : ConvV a b → ConvL as bs → ConvL (a :: as) (b :: bs)

/-- [Conv-cong] on the code of closures and the programs inside sealed programs: component by
component, embedded values compared by `≡`. -/
inductive ConvT : Term → Term → Prop
  | refl {t u : Term} : E.t t u → ConvT t u
  | val {v w : Value} : ConvV v w → ConvT (.val v) (.val w)
  | letIn {h h' : Hint} {a b c d : Term} : ConvT a c → ConvT b d → ConvT (.letIn h a b) (.letIn h' c d)
  | seq {a b c d : Term} : ConvT a c → ConvT b d → ConvT (.seq a b) (.seq c d)
  | cong {a b c d : Term} : ConvT a c → ConvT b d → ConvT (.cong a b) (.cong c d)
  | ascribe {a b c d : Term} : ConvT a c → ConvT b d → ConvT (.ascribe a b) (.ascribe c d)
  | assign {p q : Place} {a b : Term} : (p == q) = true → ConvT a b → ConvT (.assign p a) (.assign q b)
  | matchNat {p q : Place} {z s z' s' : Term} : (p == q) = true → ConvT z z' → ConvT s s' →
      ConvT (.matchNat p z s) (.matchNat q z' s')
  | call {f g : Term} {as bs : List Term} {h : Bool} : ConvT f g → ConvTL as bs → ConvT (.call f as h) (.call g bs h)
  | succ {a b : Term} : ConvT a b → ConvT (.succ a) (.succ b)
  | ref {a b : Term} : ConvT a b → ConvT (.ref a) (.ref b)
  | eq {a b c d e f : Term} : ConvT a d → ConvT b e → ConvT c f → ConvT (.eq a b c) (.eq d e f)
  | id {a b c d e f : Term} : ConvT a d → ConvT b e → ConvT c f → ConvT (.id a b c) (.id d e f)
  | pi {hs hs' : List Hint} {ds ds' : List Term} {c c' : Term} : ConvTL ds ds' → ConvT c c' →
      ConvT (.pi hs ds c) (.pi hs' ds' c')
  | fix {s s' : Hint} {hs hs' : List Hint} {ds ds' : List Term} {c c' b b' : Term} {d : Option Nat} :
      ConvTL ds ds' → ConvT c c' → ConvT b b' → ConvT (.fix s hs ds c d b) (.fix s' hs' ds' c' d b')
  | prim {n : String} {as bs : List Term} : ConvTL as bs → ConvT (.prim n as) (.prim n bs)
  | ctor {t : String} {c : Nat} {h h' : Hint} {ps qs as bs : List Term} : ConvTL ps qs → ConvTL as bs →
      ConvT (.ctor t c h ps as) (.ctor t c h' qs bs)
  | tind {n : String} {as bs : List Term} : ConvTL as bs → ConvT (.tind n as) (.tind n bs)
  | matchInd {p q : Place} {t : String} {as bs : List (Hint × Term)} : (p == q) = true →
      ConvTL (as.map (·.2)) (bs.map (·.2)) → ConvT (.matchInd p t as) (.matchInd q t bs)

inductive ConvTL : List Term → List Term → Prop
  | nil : ConvTL [] []
  | cons {a b : Term} {as bs : List Term} : ConvT a b → ConvTL as bs → ConvTL (a :: as) (b :: bs)
end

/-- The parameters [Eq-inj] reads the field types at: the equation's type `D(ā)`, else the
values' own records (`mkEqM`'s choice). -/
def eqArgs (A : Value) (t : String) (ps qs : List Value) : Option (List Value) :=
  let a? : Option (List Value) := match A with
    | .tInd n as => if n == t then some as else none
    | _ => none
  a?.orElse fun _ => if !ps.isEmpty then some ps else if !qs.isEmpty then some qs else none

variable (Γ : List IndDecl)

mutual
/-- **`Eq` computes**: `EqTo A a b P`, "`Eq(A, a, b)` computes to the proposition `P`" (appendix,
"`Eq` computes"). Nondeterministic where the paper's clauses are ordered: every rule is sound on
its own, and the machine's choice is one derivation ([Eq-stuck] needs no side condition). -/
inductive EqTo : Value → Value → Value → Value → Prop
  /-- [Eq-disj] at `⊥`: one side moved on every path, the other not -/
  | disjBot {A a b : Value} : (a == .bot) ≠ (b == .bot) → EqTo A a b vFalse
  /-- [Eq-refl] -/
  | refl {A a b : Value} : ConvV E G gs a b → EqTo A a b vTrue
  /-- [Eq-inj] at `S` (`Nat`'s constructor with one field) -/
  | succ {A a b P : Value} : EqTo .tNat a b P → EqTo A (.succ a) (.succ b) P
  /-- [Eq-inj]: the field equations at the field types; a dependent constructor only while its
  index fields are convertible (D64) -/
  | inj {A : Value} {t : String} {c : Nat} {h h' : Hint} {ps qs fs gs' args Ts Ps : List Value} {d : IndDecl} :
      eqArgs A t ps qs = some args → Γ.find? (·.name == t) = some d → fs.length = gs'.length →
      (d.dependent c = true → ∀ j ∈ d.indexFields c, ConvV E G gs (fs.getD j .bot) (gs'.getD j .bot)) →
      G.fieldTys d args c fs Ts → Ts.length = fs.length → EqL Ts fs gs' Ps →
      EqTo A (.ind t c h ps fs) (.ind t c h' qs gs') (andList Ps)
  /-- [Eq-disj]: distinct constructors of one inductive -/
  | disj {A a b : Value} : distinctCtors a b = true → EqTo A a b vFalse
  /-- [Eq-stuck] -/
  | stuck {A a b : Value} : EqTo A a b (.tEq A a b)

/-- The field equations, one per field. -/
inductive EqL : List Value → List Value → List Value → List Value → Prop
  | nil : EqL [] [] [] []
  | cons {T v w P : Value} {Ts vs ws Ps : List Value} : EqTo T v w P → EqL Ts vs ws Ps →
      EqL (T :: Ts) (v :: vs) (w :: ws) (P :: Ps)
end

end

end Ochr.Meaning.Conv
