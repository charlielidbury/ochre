import Ochr.Meaning.DataModel.Proto.Core

/-!
# Prototype (b2): carriers by stages, with their meanings built alongside

A signature (`Sig`) gives each field's shape from the declaration, the record and the earlier
fields read small: a leaf of a non-data type (its code), or a member of a data type (its
declaration and record: a recursive, nested or closed data field alike). Stage `k + 1` of `D` at
`r` is the `Σ` over constructors of the telescope of fields, data fields at stage `k`; each stage
comes with the meaning of its elements (`Lvl.mean`), so a later field's shape reads an earlier
field's meaning, which no stage changes. Nothing reads a carrier from outside.
-/

namespace Ochr.Meaning.DataModel.Proto

/-- A field's shape. -/
inductive Shape : Type 1
  | leaf (B : Type) (c : Code B)
  | sub (d : IndDecl) (r : Rec)

/-- A program's signature: field `i` of constructor `c` of `d` at record `r`, after the earlier
fields read small (`e`). -/
structure Sig where
  shape : IndDecl → Rec → Nat → Nat → List Small → Shape

/-- The meaning of a leaf (a data code as a leaf is junk the signature does not produce: tagged). -/
def encLeaf : {B : Type} → Code B → B → Val
  | _, .prop _, _ => .proof
  | _, .nat, n => .el0 Nat n
  | _, .unit, u => .el0 Unit u
  | _, .fn C, f => .el0 C f
  | _, .data _ _ A, a => .el0 A a
  | _, .err, x => nomatch x

theorem encLeaf_inj : ∀ {B : Type} (c : Code B) {a b : B}, encLeaf c a = encLeaf c b → a = b
  | _, .prop _, a, b, _ => by cases a; cases b; rfl
  | _, .nat, _, _, h => by simp only [encLeaf, Val.el0.injEq, heq_eq_eq, true_and] at h; exact h
  | _, .unit, a, b, _ => by cases a; cases b; rfl
  | _, .fn _, _, _, h => by simp only [encLeaf, Val.el0.injEq, heq_eq_eq, true_and] at h; exact h
  | _, .data _ _ _, _, _, h => by simp only [encLeaf, Val.el0.injEq, heq_eq_eq, true_and] at h; exact h
  | _, .err, a, _, _ => nomatch a

theorem encLeaf_whole : ∀ {B : Type} (c : Code B) (b : B), (encLeaf c b).whole
  | _, .prop _, _ => by simp [encLeaf, Val.whole]
  | _, .nat, _ => by simp [encLeaf, Val.whole]
  | _, .unit, _ => by simp [encLeaf, Val.whole]
  | _, .fn _, _ => by simp [encLeaf, Val.whole]
  | _, .data _ _ _, _ => by simp [encLeaf, Val.whole]
  | _, .err, x => nomatch x

/-- The number of fields of constructor `c`. -/
def arity (d : IndDecl) (c : Nat) : Nat := ((d.ctors[c]?).map (·.2.length)).getD 0

/-- A stage: a carrier for every declaration and record, with the meaning of its elements. -/
structure Lvl : Type 2 where
  C : IndDecl → Rec → Type
  mean : {d : IndDecl} → {r : Rec} → C d r → Val

variable (S : Sig)

/-- One field and the rest of the telescope, which reads its meaning small. -/
def StepT (L : Lvl) (s : Shape) (K : Val → Type) : Type :=
  match s with
  | .leaf B c => Σ b : B, K (encLeaf c b)
  | .sub d r => Σ y : L.C d r, K (L.mean y)

/-- Fields `i, …, i + n - 1` of constructor `c`, after the earlier fields `e`. -/
def Tele (L : Lvl) (d : IndDecl) (r : Rec) (c : Nat) : Nat → Nat → List Small → Type
  | _, 0, _ => PUnit
  | i, n + 1, e => StepT L (S.shape d r c i e) fun v => Tele L d r c (i + 1) n (e ++ [v.small])

def StepT.mean (L : Lvl) {K : Val → Type} (rest : ∀ v, K v → List Val) : (s : Shape) → StepT L s K → List Val
  | .leaf _ c, ⟨b, t⟩ => encLeaf c b :: rest _ t
  | .sub _ _, ⟨y, t⟩ => L.mean y :: rest _ t

def Tele.mean (L : Lvl) {d : IndDecl} {r : Rec} {c : Nat} :
    (i n : Nat) → (e : List Small) → Tele S L d r c i n e → List Val
  | _, 0, _, _ => []
  | i, n + 1, e, t => StepT.mean L (fun v t' => Tele.mean L (i + 1) n (e ++ [v.small]) t') _ t

/-- **The stages.** Stage `k + 1`: a constructor and its telescope, data fields at stage `k`; the
meaning of an element is its constructor value, recording the record. -/
def lvl : Nat → Lvl
  | 0 => ⟨fun _ _ => PEmpty, fun x => x.elim⟩
  | k + 1 => ⟨fun d r => Σ c : Fin d.ctors.length, Tele S (lvl k) d r c 0 (arity d c) [],
      fun {d r} x => .dat d.name r x.1 (Tele.mean S (lvl k) 0 (arity d x.1) [] x.2)⟩

/-! ## What a telescope's meanings are -/

/-- One field's meaning fits its shape at a stage. -/
def FitsOne (L : Lvl) : Shape → Val → Prop
  | .leaf _ c, f => ∃ b, encLeaf c b = f
  | .sub d r, f => ∃ y : L.C d r, L.mean y = f

/-- The meanings of a telescope's fields, each fitting its shape at the earlier ones. -/
def Fits (L : Lvl) (d : IndDecl) (r : Rec) (c : Nat) : Nat → Nat → List Small → List Val → Prop
  | _, 0, _, fs => fs = []
  | i, n + 1, e, fs => ∃ f fs', fs = f :: fs' ∧ FitsOne L (S.shape d r c i e) f ∧
      Fits L d r c (i + 1) n (e ++ [f.small]) fs'

theorem tele_image (L : Lvl) (d : IndDecl) (r : Rec) (c : Nat) :
    ∀ (i n : Nat) (e : List Small) (fs : List Val),
      (∃ t : Tele S L d r c i n e, Tele.mean S L i n e t = fs) ↔ Fits S L d r c i n e fs
  | _, 0, _, fs => by
    simp only [Tele.mean, Fits]
    exact ⟨fun ⟨_, h⟩ => h.symm, fun h => ⟨PUnit.unit, h.symm⟩⟩
  | i, n + 1, e, fs => by
    simp only [Fits]
    have ih := fun v => tele_image L d r c (i + 1) n (e ++ [Val.small v])
    show (∃ t : StepT L (S.shape d r c i e) (fun v => Tele S L d r c (i + 1) n (e ++ [v.small])),
        StepT.mean L (fun v t' => Tele.mean S L (i + 1) n (e ++ [v.small]) t') _ t = fs) ↔ _
    generalize S.shape d r c i e = s
    cases s with
    | leaf B cd =>
      constructor
      · rintro ⟨⟨b, t⟩, rfl⟩
        exact ⟨_, _, rfl, ⟨b, rfl⟩, (ih _ _).1 ⟨t, rfl⟩⟩
      · rintro ⟨f, fs', rfl, ⟨b, rfl⟩, hf⟩
        obtain ⟨t, ht⟩ := (ih _ _).2 hf
        exact ⟨⟨b, t⟩, by simp only [StepT.mean, ht]⟩
    | sub d' r' =>
      constructor
      · rintro ⟨⟨y, t⟩, rfl⟩
        exact ⟨_, _, rfl, ⟨y, rfl⟩, (ih _ _).1 ⟨t, rfl⟩⟩
      · rintro ⟨f, fs', rfl, ⟨y, rfl⟩, hf⟩
        obtain ⟨t, ht⟩ := (ih _ _).2 hf
        exact ⟨⟨y, t⟩, by simp only [StepT.mean, ht]⟩

end Ochr.Meaning.DataModel.Proto
