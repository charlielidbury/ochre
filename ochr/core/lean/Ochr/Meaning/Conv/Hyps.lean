import Ochr.Meaning.Conv.Statement

/-!
# N3's named hypotheses, each classed and read against the checker (conv1, 2026-11-28)

Each is one of the old attempt's (`origin/rules-trial`, `Rules/SoundT.lean`, `SoundEq.lean`,
`RefineConv.lean`), restated on the proof line as it is today (the strict type formers, `HWT` at a
hint, D103's comparisons that keep only names). Its class: **C** about the checker alone, **M** about
the model alone, **X** mixed. Its status is in the report and in each docstring: read true / false
(with the instance) / true only at reached states (with the invariant clause it needs) / unread.
-/

namespace Ochr.Meaning.Conv
open Ochr Ochr.Meaning Ochr.Meaning.Strict Ochr.Meaning.Steps

/-- Code values: a closure, a Π-closure, a sealed program (their meaning is a run of their code). -/
def isCode : Value → Bool
  | .clo .. | .tPi .. | .sealed _ => true
  | _ => false

/-- A class of values closed under the parts conversion compares and under the unit laws. The
instances: no code at all (`FO`, `Sound.lean`); the values the checker holds (the [Close]-shape
invariant of the rules trial's sweep, `Rules/ShapeSweep.lean`: every sealed program has [Close]'s
shape, closure code holds values only as inlined proofs, a stuck block's binder types or a `J`
block's statements). -/
structure Closed (Q : Value → Prop) : Prop where
  succ : ∀ {a}, Q (.succ a) → Q a
  tRef : ∀ {a}, Q (.tRef a) → Q a
  borrow : ∀ {l a}, Q (.borrow l a) → Q a
  gloan : ∀ {l a}, Q (.gloan l a) → Q a
  tEq : ∀ {A a b}, Q (.tEq A a b) → Q A ∧ Q a ∧ Q b
  tInd : ∀ {n as}, Q (.tInd n as) → ∀ a ∈ as, Q a
  ind : ∀ {t c h ps fs}, Q (.ind t c h ps fs) → ∀ a ∈ fs, Q a
  unit : ∀ {v}, Q v → Q (unitTop v)

section
variable (K : RunCtx) (ρ : Assignment) (φ : Future)

/-- **(H1) [Conv-fun]'s premise is sound** (X; the old `PremSoundT.fn`). A successful comparison of
the two functions' generic calls (`convFnRun`, run from a state the comparison reached) makes them
alike. Its content is (V5) of `notes/conv-model.md`: a function's meaning at every member argument
tuple is its generic observation under the assignment that sends the generic arguments there. So it
is (II) for the untyped run of the generic call (`callFn`, from `convFnRun`'s fresh frame, its (E4)
from the function's membership), the call in place against the callee's meaning (C1, `FixEqG` for a
global, the `.fix` clause for a closure), and the completeness of the observation (result; cells;
for a returned borrow, its content and the cells after one fresh `σw` through it, D38). -/
def PremFn (G : Premises) : Prop := ∀ f g, G.fn f g → Alike K ρ φ f g

/-- **(H2) [Conv-pi]'s premise is sound** (X; the old `PremSoundT.pi`). A successful `convPi` makes
two Π-closures alike: their domains and codomains, evaluated at the first's generic arguments, are
pairwise convertible, so (by N3 at types under every extension of the assignment to the generic
unknowns) the model's telescopes agree at every tuple of member arguments, which is all a Π code
reads (`Tel.param`'s continuation is a function of the domain's ELEMENTS). It is (II) for `evalType`
at the generic state and the transfer between that state and the model's `extendBy` (docs/31 D210). -/
def PremPi (G : Premises) : Prop := ∀ P Q, G.pi P Q → Alike K ρ φ P Q

/-- **(H3) The unit laws keep meaning** (M; the old `UnitOk`, in the claim's form). `unitTop`
replaces `And(True, P)` by `P` (and `And(P, True)` by `P`) along a head of nested `And`s; on a value of
the class `Q` that fits a type at a hint, the result means the same there and holds no `Prop`
constructor value either. Its content: `LibOk` (the library's `And` and `True`), and a sealed
proposition's meaning not depending on the hint it is read at (`HintIndep`: true of [Close]'s
shapes, whose tails read no hint). -/
structure UnitOk (Q : Value → Prop) : Prop where
  keep : ∀ h T v, Q v → NoProp K v → Fit K.dm.read T (meanV K ρ φ h v) →
    NoProp K (unitTop v) ∧ meanV K ρ φ h (unitTop v) = meanV K ρ φ h v

/-- **(H4) The code cases** (X; the old `CodeOk`): [Conv-refl] on code (`==`: binder names and the
parameters constructor values record ignored), [Conv-cong] on sealed programs (the same text but for
convertible embedded values) and on Π-closures (convertible captures, the same readings, the same
code), on a class `Q` of values (the [Close]-shape invariant; not of every well-typed value). -/
structure CodeOk (Q : Value → Prop) (G : Premises) (gs : List GDef) : Prop where
  refl : ∀ v w, Q v → Q w → isCode v = true → (v == w) = true → Alike K ρ φ v w
  sealed : ∀ t u, Q (.sealed t) → Q (.sealed u) → ConvT Syn.machine G gs t u →
    Alike K ρ φ (.sealed t) (.sealed u)
  piCong : ∀ cs ds t u r r', Q (.tPi cs t r) → Q (.tPi ds u r') → RdEq Syn.machine r r' →
    ConvL Syn.machine G gs cs ds → ConvT Syn.machine G gs t u → Alike K ρ φ (.tPi cs t r) (.tPi ds u r')

/-- **(H5) The library's connectives** (M; the old `LibOkT`): `True`, `False` and `And` (the
`Prelude`'s, in front of every program the consistency theorem is about, `Consistency.lean`) mean
truth, falsity and conjunction at every hint, for arguments whose meanings do not depend on the hint. -/
structure LibOk : Prop where
  tru : ∀ hint, meanV K ρ φ hint vTrue = .ty (TyM.prop True)
  fls : ∀ hint, meanV K ρ φ hint vFalse = .ty (TyM.prop False)
  and : ∀ (P Q : Value) (p q : Prop), (∀ hint, meanV K ρ φ hint P = .ty (TyM.prop p)) →
    (∀ hint, meanV K ρ φ hint Q = .ty (TyM.prop q)) →
    ∀ hint, meanV K ρ φ hint (.tInd "And" [P, Q]) = .ty (TyM.prop (p ∧ q))

/-- **(H6) [Eq-inj]'s field types** (X; the old `FieldTysSound`): each field type `fieldTypesOf`
computes means the model's field type at the record of the parameters and the left side's earlier
fields. Its content is N1's faithfulness (the field type the reference run computes is the data
model's) and (II) for the typed runs of `fieldTele`. -/
def FieldTysSound (G : Premises) : Prop :=
  ∀ d args c fs Ts, G.fieldTys d args c fs Ts → ∀ j T, Ts[j]? = some T →
    (meanV K ρ φ (.plain TyM.err) T).asTy = K.dm.fieldTyR d (K.dm.recOf d (meanParams K ρ φ d 0 [] args)) c j
      ((meanFields K ρ φ d (K.dm.recOf d (meanParams K ρ φ d 0 [] args)) c 0 [] fs).take j)

/-- **(H7) A field's type reads only the index fields** (M; the old `FieldTyIdx`, D64). -/
def FieldTyIdx : Prop :=
  ∀ d r c j (e e' : List Sem), e.length = e'.length →
    (∀ k ∈ d.indexFields c, k < e.length → e[k]? = e'[k]?) →
    K.dm.fieldTyR d r c j e = K.dm.fieldTyR d r c j e'

/-- **(H8) An `Eq`'s side** (X; the old `SideMem`; supplied by each caller): `⊥`, or a whole member of
the equation's type (D84; the strict `Eq` asks the same, `Value.SideOk`). -/
def SideOkV (T : TyM) (a : Value) : Prop :=
  a = .bot ∨ meanV K ρ φ (.plain T) a ∈ₛ[K.dm.read] T

end

end Ochr.Meaning.Conv
