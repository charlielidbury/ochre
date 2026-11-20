import Ochr.Meaning.Rules.Conv

/-!
# The rules trial, part A: the rules are sound in the model

No `MState` in any statement here: values, the run context `K` (declarations, data model, globals,
decisions), an assignment `ρ` and a future `φ`.

**What A needs, found by writing it** (each is a hypothesis below, named):
- `SynSound`: the two untyped parts of conversion keep meanings at every hint. True of syntactic
  equality and of no unit law at all; false of the machine's instance at ill-typed nested values
  (`Rules/Counter.lean`: `And(True, Nat) ≡ Nat` inside an `Eq`). The paper's conversion is untyped
  and the model is typed, so either the rules carry types (a typed conversion) or the values
  compared carry a deep typing fact; neither is machine bookkeeping.
- `PremSound`: the abstract premises are sound. For [Conv-fun] and [Conv-pi] this is the whole
  semantic content of the rule (the generic call stands for every instance); A itself adds only
  the congruence around it.
- `runT_congr` (a lemma of A, open): the model's run of two programs that are convertible
  component by component agrees. It reads the decision table at terms (`K.D.paramDecls`,
  `K.D.flags`, ...), so it needs the decisions to agree on convertible terms: a guess.
- for `Eq`: the library's `True`, `False`, `And` mean what they say (`LibOk`); the two sides are
  partly moved members of the equation's type (the records [Eq-inj] reads are the type's); a side
  that is not `⊥` does not mean `moved` ([Eq-disj] at `⊥`); constructor values are of data
  declarations ([Eq-disj] on constructors of a `Prop` inductive would be unsound: both mean `⋆`).
-/

namespace Ochr.Meaning.Rules
open Ochr Ochr.Meaning Ochr.Meaning.Steps

section
variable (K : RunCtx) (ρ : Assignment) (φ : Future)

/-- Two values are alike in the model: embedded in a program they run alike (the same meaning at
every hint, the same type: `runT`'s `.val` clause). -/
def ValAlike (v w : Value) : Prop :=
  ∀ tail hint s, runT K ρ φ tail hint (.val v) s = runT K ρ φ tail hint (.val w) s

/-- Two programs run alike from every state. -/
def TermAlike (t u : Term) : Prop :=
  ∀ tail hint s, runT K ρ φ tail hint t s = runT K ρ φ tail hint u s

/-- An embedded value's run gives its meaning at the hint. -/
theorem runT_val_fst (tail : Bool) (hint : TyS) (s : SState) (v : Value) :
    (runT K ρ φ tail hint (.val v) s).map (·.1.1) = some (meanV K ρ φ hint v) := by
  cases v <;> rfl

/-- Alike values mean the same at every hint. -/
theorem ValAlike.mean {v w : Value} (h : ValAlike K ρ φ v w) (hint : TyS) :
    meanV K ρ φ hint v = meanV K ρ φ hint w := by
  have e := congrArg (Option.map (·.1.1)) (h false hint (emptyState 0))
  rw [runT_val_fst, runT_val_fst] at e
  exact Option.some.inj e

/-- The untyped parts of conversion keep meanings. -/
structure SynSound (E : Syn) : Prop where
  v : ∀ v w, E.v v w → ValAlike K ρ φ v w
  t : ∀ t u, E.t t u → TermAlike K ρ φ t u
  unit : ∀ v, E.unit v → ValAlike K ρ φ (unitTop v) v
  /-- recorded parameters are compared -/
  params : E.ignoreParams = false

/-- What A assumes of the abstract premises. -/
structure PremSound (G : Premises) : Prop where
  fn : ∀ f g, G.fn f g → ValAlike K ρ φ f g
  pi : ∀ P Q, G.pi P Q → ValAlike K ρ φ P Q
  /-- each computed field type means the model's field type at the record of the parameters and
  the meanings of the earlier fields -/
  fieldTys : ∀ d args c fs Ts, G.fieldTys d args c fs Ts → ∀ j T, Ts[j]? = some T →
    (meanV K ρ φ (.plain .err) T).asTy =
      K.dm.fieldTyR d (K.dm.recOf d (meanParams K ρ φ d 0 [] args)) c j
        ((meanFields K ρ φ d (K.dm.recOf d (meanParams K ρ φ d 0 [] args)) c 0 [] fs).take j)

/-- The library's propositions mean what they say (a fact about `K`: its declarations hold the
library's `True`, `False`, `And` and its data model is faithful to them). -/
structure LibOk : Prop where
  tru : ∀ hint, meanV K ρ φ hint vTrue = .ty (TyM.prop True)
  fls : ∀ hint, meanV K ρ φ hint vFalse = .ty (TyM.prop False)
  and : ∀ hint (P Q : Value) (p q : Prop), meanV K ρ φ (.plain .err) P = .ty (TyM.prop p) →
    meanV K ρ φ (.plain .err) Q = .ty (TyM.prop q) → meanV K ρ φ hint (.tInd "And" [P, Q]) = .ty (TyM.prop (p ∧ q))

variable {E : Syn} {G : Premises} {gs : List GDef}

/-- **(A) Conversion is sound**: convertible values run alike, hence mean the same at every hint.
By induction on the derivation (mutually with `convH_sound`, `convL_sound`, `convT_sound`). No
membership hypothesis: with sound untyped parts, conversion is sound at every hint. -/
theorem convV_sound (hs : SynSound K ρ φ E) (hp : PremSound K ρ φ G) {v w : Value}
    (h : ConvV E G gs v w) : ValAlike K ρ φ v w := by
  sorry

theorem convH_sound (hs : SynSound K ρ φ E) (hp : PremSound K ρ φ G) {v w : Value}
    (h : ConvH E G gs v w) : ValAlike K ρ φ v w := by
  sorry

/-- (A) Convertible programs run alike from every state. The congruence of the model's run: it
reads a program's decisions (`K.D`) at its terms, so this needs the decisions to agree on
convertible terms (a guess; not yet a hypothesis). -/
theorem convT_sound (hs : SynSound K ρ φ E) (hp : PremSound K ρ φ G) {t u : Term}
    (h : ConvT E G gs t u) : TermAlike K ρ φ t u := by
  sorry

/-- (A) The existing statement's shape: at a type. -/
theorem conv_sound_at (hs : SynSound K ρ φ E) (hp : PremSound K ρ φ G) {v w : Value}
    (h : ConvV E G gs v w) (T : TyM) : meanV K ρ φ (.plain T) v = meanV K ρ φ (.plain T) w :=
  (convV_sound K ρ φ hs hp h).mean K ρ φ _

/-- The meaning of the equation's type, as the sides are read at it. -/
noncomputable abbrev tyOf (A : Value) : TyM := (meanV K ρ φ (.plain .err) A).asTy

/-- **(A) `Eq` computes soundly**: the proposition computed means `⟦a⟧ = ⟦b⟧` at `A`. Hypotheses on
the sides, each needed by one rule: partly moved members of `A` ([Eq-inj] reads `A`'s record;
[Conv-refl] does not need it), not meaning `moved` unless `⊥` ([Eq-disj] at `⊥`), constructor
values of data declarations ([Eq-disj] and [Eq-inj] on a `Prop` inductive's values, which all
mean `⋆`). -/
theorem eqTo_sound (hs : SynSound K ρ φ E) (hp : PremSound K ρ φ G) (hl : LibOk K ρ φ)
    {A a b P : Value} (h : EqTo E G gs K.Γ A a b P)
    (ha : DataModel.pmem K.dm.read K.Γ (meanV K ρ φ (.plain (tyOf K ρ φ A)) a) (tyOf K ρ φ A))
    (hb : DataModel.pmem K.dm.read K.Γ (meanV K ρ φ (.plain (tyOf K ρ φ A)) b) (tyOf K ρ φ A))
    (hma : a ≠ .bot → meanV K ρ φ (.plain (tyOf K ρ φ A)) a ≠ .moved)
    (hmb : b ≠ .bot → meanV K ρ φ (.plain (tyOf K ρ φ A)) b ≠ .moved)
    (hda : a.anyAtom (dataCtorBad K.Γ) = false) (hdb : b.anyAtom (dataCtorBad K.Γ) = false) :
    ∀ hint, meanV K ρ φ hint P =
      .ty (TyM.prop (meanV K ρ φ (.plain (tyOf K ρ φ A)) a = meanV K ρ φ (.plain (tyOf K ρ φ A)) b)) := by
  sorry

end

end Ochr.Meaning.Rules
