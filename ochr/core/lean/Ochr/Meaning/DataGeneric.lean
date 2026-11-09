import Ochr.Meaning.Data

/-!
# The generic data model, by stages (docs/31 D4)

Every accepted inductive declaration means, at each parameter tuple, the least fixed point of its
constructor operator (docs/18 Def. "meaning of types"). This file builds it without
induction-recursion, as `Ochr/Model/Slice.lean` §4 builds type functions:

* **Codes** (`PCode`). The spine's assembly reads each field's declared type into a code: a
  closed small type (`ext`, everything not mentioning the declaration or a nestable parameter,
  including equations, type-function fields and earlier inductives at fixed arguments), a
  nestable parameter (`par`), an occurrence of the declaration itself at arguments (`self`, any
  arguments: non-uniform recursion, D71), or an occurrence of an *earlier* declaration with the
  declaration or a nestable parameter at a nestable position (`nest`, docs/18 (I1)).
* **Stages** (`stage`). Stage `k + 1` at `ps` is the `Σ` over constructors of the telescope of
  field carriers, recursive occurrences read at stage `k`; it is defined for every parameter
  tuple at once, so non-uniform parameters cost nothing.
* **The carrier** (`car`) is the colimit of the stages, a `Quotient` of `Σ k, stage k ps` by
  equality of a stage-independent *raw* meaning (`rawStage`).

Nesting (`Rose(A) := Node(v : A, kids : List(Rose(A)))`) is read through the earlier
declaration's own carrier, `car List [Rose(A)]`, as the reference run reads the field type. That
needs the earlier carrier to be functorial in its nestable parameters and finitary (an element
over a colimit comes from a stage): the interface `NModel`, which this construction also
*produces* for every declaration, so the program's declarations are modelled in order. The
choice is recorded in docs/31, "data-generic: choices".

Parameters at nestable positions are *blanked* (`blank`) before the codes read them: a code sees
a nestable parameter only as `par j`, so the carrier is functorial in it. The parameters'
types themselves come in as a leaf environment `Z : Nat → TyM`; the data model reads it off the
parameters (`envOf`).
-/

namespace Ochr.Meaning
namespace DataGeneric
open DataModel

/-! ## Preliminaries -/

/-- The type a parameter meaning holds. -/
def tyOf : Sem → TyM
  | .ty T => T
  | _ => .err

/-- The leaf environment of a parameter tuple: parameter `j`'s type. -/
def envOf (ps : List Sem) : Nat → TyM := fun j => tyOf (ps.getD j .err)

/-- Maps, raw meanings and predicates on the leaves of a leaf environment. -/
abbrev LMap (Z Z' : Nat → TyM) := ∀ j, El (Z j) → El (Z' j)
abbrev LRaw (Z : Nat → TyM) := ∀ j, El (Z j) → Sem
abbrev LPred (Z : Nat → TyM) := ∀ j, El (Z j) → Prop

/-- Leaf raws related: equal raws under `r₁`, `r₂` stay equal under `r₁'`, `r₂'`. -/
def LRel {Z₁ Z₂ : Nat → TyM} (r₁ r₁' : LRaw Z₁) (r₂ r₂' : LRaw Z₂) : Prop :=
  ∀ j a b, r₁ j a = r₂ j b → r₁' j a = r₂' j b

/-- The canonical raw meaning of a leaf: its own meaning. -/
def canon (Z : Nat → TyM) : LRaw Z := fun j => enc (Z j)

theorem canon_inj (Z : Nat → TyM) (j : Nat) : Function.Injective (canon Z j) :=
  fun _ _ h => enc_inj h

/-- The type meaning of a family member: a carrier, or for a `Prop`-sorted declaration its
inhabitedness (docs/31 D4: the truncation of the same fixed point). -/
def tyB : Bool → Type → TyM
  | true, A => .prop (Nonempty A)
  | false, A => .ty0 A

def mapB : (b : Bool) → {A B : Type} → (A → B) → El (tyB b A) → El (tyB b B)
  | true, _, _, f, h => ⟨h.down.elim fun a => ⟨f a⟩⟩
  | false, _, _, f, a => f a

def rawB : (b : Bool) → {A : Type} → (A → Sem) → El (tyB b A) → Sem
  | true, _, _, _ => .proof
  | false, _, r, a => r a

/-- A predicate on the leaves of a member: of the element, or of some witness of a proposition. -/
def allLB : (b : Bool) → {A : Type} → (A → Prop) → El (tyB b A) → Prop
  | true, _, P, _ => ∃ a, P a
  | false, _, P, a => P a

theorem plift_eq {P : Prop} (x y : PLift P) : x = y := by cases x; cases y; rfl

theorem mapB_comp (b : Bool) {A B C : Type} (f : A → B) (g : B → C) (x : El (tyB b A)) :
    mapB b g (mapB b f x) = mapB b (g ∘ f) x := by
  cases b
  · rfl
  · exact plift_eq _ _

theorem mapB_id (b : Bool) {A : Type} (x : El (tyB b A)) : mapB b id x = x := by
  cases b
  · rfl
  · exact plift_eq _ _

theorem mapB_congr (b : Bool) {A B : Type} {f g : A → B} (h : ∀ a, f a = g a) (x : El (tyB b A)) :
    mapB b f x = mapB b g x := by
  rw [funext h]

theorem rawB_map (b : Bool) {A B : Type} (f : A → B) (r : B → Sem) (x : El (tyB b A)) :
    rawB b r (mapB b f x) = rawB b (r ∘ f) x := by
  cases b <;> rfl

theorem rawB_inj (b : Bool) {A : Type} (r : A → Sem) (hr : Function.Injective r)
    (x y : El (tyB b A)) (h : rawB b r x = rawB b r y) : x = y := by
  cases b
  · exact hr h
  · exact plift_eq _ _

theorem rawB_rel (b : Bool) {A B : Type} (r₁ r₁' : A → Sem) (r₂ r₂' : B → Sem)
    (hr : ∀ a b, r₁ a = r₂ b → r₁' a = r₂' b) (x : El (tyB b A)) (y : El (tyB b B))
    (h : rawB b r₁ x = rawB b r₂ y) : rawB b r₁' x = rawB b r₂' y := by
  cases b
  · exact hr _ _ h
  · rfl

theorem allLB_mono (b : Bool) {A : Type} (P Q : A → Prop) (hPQ : ∀ a, P a → Q a)
    (x : El (tyB b A)) (h : allLB b P x) : allLB b Q x := by
  cases b
  · exact hPQ _ h
  · obtain ⟨a, ha⟩ := h; exact ⟨a, hPQ _ ha⟩

theorem allLB_true (b : Bool) {A : Type} (P : A → Prop) (hP : ∀ a, P a) (x : El (tyB b A)) :
    allLB b P x := by
  cases b
  · exact hP _
  · exact x.down.elim fun a => ⟨a, hP a⟩

/-- Lifting through `mapB`: what lifts at the members lifts at the type. -/
theorem allLB_lift (b : Bool) {A B : Type} (f : A → B) (Q : B → Prop)
    (hQ : ∀ y, Q y → ∃ x, f x = y) (y : El (tyB b B)) (h : allLB b Q y) :
    ∃ x, mapB b f x = y := by
  cases b
  · exact hQ _ h
  · obtain ⟨a, ha⟩ := h
    obtain ⟨x, _⟩ := hQ a ha
    exact ⟨⟨⟨x⟩⟩, plift_eq _ _⟩

/-- Directedness through `allLB`. -/
theorem allLB_directed (b : Bool) {A : Type} (P : A → Prop) (Pk : Nat → A → Prop)
    (hP : ∀ a, P a → ∃ k, Pk k a) (x : El (tyB b A)) (h : allLB b P x) :
    ∃ k, allLB b (Pk k) x := by
  cases b
  · exact hP _ h
  · obtain ⟨a, ha⟩ := h
    obtain ⟨k, hk⟩ := hP a ha
    exact ⟨k, a, hk⟩

/-! ## Nestable models

What a declaration nested into must provide (docs/18 (I1)): its carrier as a function of the
fixed parameters and of the leaf environment, functorial in the leaves (`map`), with a raw
meaning relative to a raw meaning of the leaves (`raw`) and a predicate on its leaves (`allL`).
The laws are the ones the stage construction of a later declaration uses: the functor laws,
naturality and relational invariance of the raw meaning, its injectivity, and finitarity
(`lift`: an element whose leaves all lie in the image of a leaf map comes from one;
`directed`: an element whose leaves each satisfy some stage of a monotone family satisfies one
stage). The generic construction produces one for every declaration (`Gen.nmodel`). -/
structure NModel where
  isProp : Bool
  car : List Sem → (Nat → TyM) → Type
  map : ∀ {ps Z Z'}, LMap Z Z' → car ps Z → car ps Z'
  raw : ∀ {ps Z}, LRaw Z → car ps Z → Sem
  allL : ∀ {ps Z}, LPred Z → car ps Z → Prop
  map_id : ∀ {ps Z} (x : car ps Z), map (fun _ => id) x = x
  map_comp : ∀ {ps Z Z' Z''} (f : LMap Z Z') (g : LMap Z' Z'') (x : car ps Z),
    map g (map f x) = map (fun j => g j ∘ f j) x
  raw_map : ∀ {ps Z Z'} (f : LMap Z Z') (r : LRaw Z') (x : car ps Z),
    raw r (map f x) = raw (fun j => r j ∘ f j) x
  raw_rel : ∀ {ps Z₁ Z₂} (r₁ r₁' : LRaw Z₁) (r₂ r₂' : LRaw Z₂) (x₁ : car ps Z₁) (x₂ : car ps Z₂),
    LRel r₁ r₁' r₂ r₂' → raw r₁ x₁ = raw r₂ x₂ → raw r₁' x₁ = raw r₂' x₂
  raw_inj : ∀ {ps Z} (r : LRaw Z) (x y : car ps Z), (∀ j, Function.Injective (r j)) →
    raw r x = raw r y → x = y
  allL_mono : ∀ {ps Z} (P Q : LPred Z) (x : car ps Z), (∀ j a, P j a → Q j a) → allL P x → allL Q x
  allL_true : ∀ {ps Z} (x : car ps Z), allL (fun _ _ => True) x
  lift : ∀ {ps Z Z'} (f : LMap Z Z') (y : car ps Z'), allL (fun j b => ∃ a, f j a = b) y →
    ∃ x, map f x = y
  directed : ∀ {ps Z} (P : Nat → LPred Z) (x : car ps Z), (∀ k j a, P k j a → P (k + 1) j a) →
    allL (fun j a => ∃ k, P k j a) x → ∃ k, allL (P k) x

/-- The model of nothing (an out-of-range declaration index). -/
def NModel.empty : NModel where
  isProp := false
  car _ _ := PEmpty
  map _ x := x.elim
  raw _ x := x.elim
  allL _ _ := True
  map_id x := x.elim
  map_comp _ _ x := x.elim
  raw_map _ _ x := x.elim
  raw_rel _ _ _ _ x := x.elim
  raw_inj _ x := x.elim
  allL_mono _ _ x := x.elim
  allL_true x := x.elim
  lift _ y := y.elim
  directed _ x := x.elim

/-! ## Codes of field types -/

/-- The code of a field's declared type (docs/18 (I1)–(I5)): a closed small type `ext T`; the
nestable parameter `par j`; an occurrence `self fx tys` of the declaration itself, with fixed
parameters `fx` and, at each position, the type code `tys j` (read without the declaration,
docs/18 (I2), and used at the declaration's nestable positions); an occurrence `nest e fx tys`
of the earlier declaration `e`, whose positions take the type codes `tys j`, which may contain
the declaration (nesting). A position that takes a fixed parameter `s` takes the code
`ext (tyOf s)` as well. -/
inductive PCode : Type 3 where
  | ext (T : TyM)
  | par (j : Nat)
  | self (fx : List Sem) (tys : Nat → PCode)
  | nest (e : Nat) (fx : List Sem) (tys : Nat → PCode)

/-- A family of carriers indexed by parameters and leaf environment. -/
abbrev Fam := List Sem → (Nat → TyM) → Type

/-- The family with no members: the arguments of an occurrence never mention the declaration. -/
def X₀ : Fam := fun _ _ => PEmpty

section codes
variable (M : Nat → NModel) (b : Bool)

/-- The meaning of a code, with the declaration read as `X` and the leaves as `Z`. -/
def interp (X : Fam) (Z : Nat → TyM) : PCode → TyM
  | .ext T => T
  | .par j => Z j
  | .self fx tys => tyB b (X fx fun j => interp X₀ Z (tys j))
  | .nest e fx tys => tyB (M e).isProp ((M e).car fx fun j => interp X Z (tys j))

/-- What a later field's code sees of this field: a closed field's meaning, `err` otherwise. -/
def mask (X : Fam) (Z : Nat → TyM) : (τ : PCode) → El (interp M b X Z τ) → Sem
  | .ext T, v => enc T v
  | .par _, _ => .err
  | .self _ _, _ => .err
  | .nest _ _ _, _ => .err

/-- What a later field's code sees, from the field's meaning. -/
def maskSem : PCode → Sem → Sem
  | .ext _, s => s
  | _, _ => .err

theorem mask_eq (X : Fam) (Z : Nat → TyM) (τ : PCode) (v : El (interp M b X Z τ)) :
    mask M b X Z τ v = maskSem τ (enc _ v) := by
  cases τ <;> rfl

/-- Change the reading of the declaration, `X` to `Y`, at fixed leaves (a stage into the next,
or into the colimit). -/
def cmapX {X Y : Fam} (fX : ∀ {ps Z}, X ps Z → Y ps Z) {Z : Nat → TyM} :
    (τ : PCode) → El (interp M b X Z τ) → El (interp M b Y Z τ)
  | .ext _, v => v
  | .par _, v => v
  | .self _ _, v => mapB b fX v
  | .nest e _ tys, v => mapB (M e).isProp ((M e).map fun j => cmapX (X := X) (Y := Y) fX (tys j)) v

/-- Change the leaves, for a reading `X` of the declaration functorial in its leaves. -/
def cmapZ {X : Fam} (fX : ∀ {ps Z Z'}, LMap Z Z' → X ps Z → X ps Z') :
    (τ : PCode) → {Z Z' : Nat → TyM} → LMap Z Z' → El (interp M b X Z τ) → El (interp M b X Z' τ)
  | .ext _, _, _, _, v => v
  | .par j, _, _, f, v => f j v
  | .self _ tys, _, _, f, v =>
    mapB b (fX fun j => cmapZ (X := X₀) (fun _ y => y.elim) (tys j) f) v
  | .nest e _ tys, _, _, f, v => mapB (M e).isProp ((M e).map fun j => cmapZ (X := X) fX (tys j) f) v

/-- The raw meaning of a field, for a raw meaning of the declaration's members and of the
leaves. -/
def craw {X : Fam} (rX : ∀ {ps Z}, LRaw Z → X ps Z → Sem) :
    (τ : PCode) → {Z : Nat → TyM} → LRaw Z → El (interp M b X Z τ) → Sem
  | .ext T, _, _, v => enc T v
  | .par j, _, r, v => r j v
  | .self _ tys, _, r, v => rawB b (rX fun j => craw (X := X₀) (fun _ y => y.elim) (tys j) r) v
  | .nest e _ tys, _, r, v => rawB (M e).isProp ((M e).raw fun j => craw (X := X) rX (tys j) r) v

/-- A predicate on the leaves of a field. -/
def callL {X : Fam} (PX : ∀ {ps Z}, LPred Z → X ps Z → Prop) :
    (τ : PCode) → {Z : Nat → TyM} → LPred Z → El (interp M b X Z τ) → Prop
  | .ext _, _, _, _ => True
  | .par j, _, P, v => P j v
  | .self _ tys, _, P, v =>
    allLB b (PX fun j => callL (X := X₀) (fun _ y => y.elim) (tys j) P) v
  | .nest e _ tys, _, P, v => allLB (M e).isProp ((M e).allL fun j => callL (X := X) PX (tys j) P) v

end codes

/-! ## Laws of the code operations

Each is by induction on the code, for a reading of the declaration with the corresponding
property (a stage, by induction on stages, or the colimit). The arguments of an occurrence are
read with `X₀`, for which every property is vacuous. -/

section codeLaws
variable (M : Nat → NModel) (b : Bool)

theorem cmapX_comp {X Y W : Fam} (fX : ∀ {ps Z}, X ps Z → Y ps Z) (gX : ∀ {ps Z}, Y ps Z → W ps Z)
    {Z : Nat → TyM} (τ : PCode) (v : El (interp M b X Z τ)) :
    cmapX M b (X := Y) (Y := W) gX τ (cmapX M b (X := X) (Y := Y) fX τ v) =
      cmapX M b (X := X) (Y := W) (fun y => gX (fX y)) τ v := by
  induction τ with
  | ext _ | par _ => rfl
  | self _ _ => exact mapB_comp b _ _ v
  | nest e _ tys ih =>
    refine (mapB_comp _ _ _ _).trans (mapB_congr _ (fun x => ?_) _)
    simp only [Function.comp, (M e).map_comp]
    congr 1
    funext j a
    exact ih j a

theorem cmapX_congr {X Y : Fam} (fX gX : ∀ {ps Z}, X ps Z → Y ps Z)
    (h : ∀ ps Z (y : X ps Z), fX y = gX y) {Z : Nat → TyM} (τ : PCode) (v : El (interp M b X Z τ)) :
    cmapX M b (X := X) (Y := Y) fX τ v = cmapX M b (X := X) (Y := Y) gX τ v := by
  induction τ with
  | ext _ | par _ => rfl
  | self _ _ => exact mapB_congr b (fun y => h _ _ y) v
  | nest e _ tys ih =>
    simp only [cmapX]
    congr 2
    funext j a
    exact ih j a

theorem craw_cmapX {X Y : Fam} (fX : ∀ {ps Z}, X ps Z → Y ps Z) (rY : ∀ {ps Z}, LRaw Z → Y ps Z → Sem)
    {Z : Nat → TyM} (τ : PCode) (r : LRaw Z) (v : El (interp M b X Z τ)) :
    craw M b (X := Y) rY τ r (cmapX M b (X := X) (Y := Y) fX τ v) =
      craw M b (X := X) (fun r y => rY r (fX y)) τ r v := by
  induction τ with
  | ext _ | par _ => rfl
  | self _ _ => exact rawB_map b _ _ v
  | nest e _ tys ih =>
    refine (rawB_map _ _ _ _).trans (congrArg (fun F => rawB _ F v) (funext fun x => ?_))
    simp only [Function.comp]
    rw [(M e).raw_map]
    congr 1
    funext j a
    exact ih j a

theorem craw_inj {X : Fam} (rX : ∀ {ps Z}, LRaw Z → X ps Z → Sem)
    (hX : ∀ ps Z (r : LRaw Z), (∀ j, Function.Injective (r j)) → Function.Injective (rX (ps := ps) r))
    (τ : PCode) {Z : Nat → TyM} (r : LRaw Z) (hr : ∀ j, Function.Injective (r j)) :
    Function.Injective (craw M b (X := X) rX τ r) := by
  induction τ generalizing X with
  | ext T => exact fun _ _ h => enc_inj h
  | par j => exact hr j
  | self fx tys ih =>
    apply rawB_inj
    apply hX
    intro j
    exact ih j (X := X₀) (fun _ (y : PEmpty) => y.elim) (fun _ _ _ _ (y : PEmpty) => y.elim)
  | nest e fx tys ih =>
    apply rawB_inj
    intro x y h
    exact (M e).raw_inj _ x y (fun j => ih j rX hX) h

/-- Equal raw meanings of a field at two readings give the same masked meaning. -/
theorem mask_rel {X₁ X₂ : Fam} (rX₁ : ∀ {ps Z}, LRaw Z → X₁ ps Z → Sem)
    (rX₂ : ∀ {ps Z}, LRaw Z → X₂ ps Z → Sem) (τ : PCode) {Z₁ Z₂ : Nat → TyM}
    (r₁ : LRaw Z₁) (r₂ : LRaw Z₂) (v₁ : El (interp M b X₁ Z₁ τ)) (v₂ : El (interp M b X₂ Z₂ τ))
    (h : craw M b (X := X₁) rX₁ τ r₁ v₁ = craw M b (X := X₂) rX₂ τ r₂ v₂) :
    mask M b X₁ Z₁ τ v₁ = mask M b X₂ Z₂ τ v₂ := by
  cases τ with
  | ext T => exact h
  | _ => rfl

/-- Relational invariance of a field's raw meaning (two readings, two leaf environments). -/
theorem craw_rel {X₁ X₂ : Fam} (rX₁ : ∀ {ps Z}, LRaw Z → X₁ ps Z → Sem)
    (rX₂ : ∀ {ps Z}, LRaw Z → X₂ ps Z → Sem)
    (hX : ∀ ps Za Zb (ra ra' : LRaw Za) (rb rb' : LRaw Zb) (ya : X₁ ps Za) (yb : X₂ ps Zb),
      LRel ra ra' rb rb' → rX₁ ra ya = rX₂ rb yb → rX₁ ra' ya = rX₂ rb' yb)
    (τ : PCode) {Z₁ Z₂ : Nat → TyM} (r₁ r₁' : LRaw Z₁) (r₂ r₂' : LRaw Z₂)
    (hr : LRel r₁ r₁' r₂ r₂') (v₁ : El (interp M b X₁ Z₁ τ)) (v₂ : El (interp M b X₂ Z₂ τ))
    (h : craw M b (X := X₁) rX₁ τ r₁ v₁ = craw M b (X := X₂) rX₂ τ r₂ v₂) :
    craw M b (X := X₁) rX₁ τ r₁' v₁ = craw M b (X := X₂) rX₂ τ r₂' v₂ := by
  induction τ generalizing X₁ X₂ with
  | ext _ => exact h
  | par j => exact hr j _ _ h
  | self fx tys ih =>
    refine rawB_rel b _ _ _ _ (fun ya yb hy => hX _ _ _ _ _ _ _ ya yb ?_ hy) v₁ v₂ h
    intro j a a' ha
    exact ih j (X₁ := X₀) (X₂ := X₀) (fun _ (y : PEmpty) => y.elim) (fun _ (y : PEmpty) => y.elim)
      (fun _ _ _ _ _ _ _ (y : PEmpty) => y.elim) a a' ha
  | nest e fx tys ih =>
    refine rawB_rel _ _ _ _ _ (fun x₁ x₂ hx => (M e).raw_rel _ _ _ _ x₁ x₂ ?_ hx) v₁ v₂ h
    intro j a a' ha
    exact ih j rX₁ rX₂ hX a a' ha

theorem callL_mono {X : Fam} (PX : ∀ {ps Z}, LPred Z → X ps Z → Prop)
    (hX : ∀ ps Z (P Q : LPred Z) (y : X ps Z), (∀ j a, P j a → Q j a) → PX P y → PX Q y)
    (τ : PCode) {Z : Nat → TyM} (P Q : LPred Z) (hPQ : ∀ j a, P j a → Q j a)
    (v : El (interp M b X Z τ)) (h : callL M b (X := X) PX τ P v) : callL M b (X := X) PX τ Q v := by
  induction τ generalizing X with
  | ext _ => trivial
  | par j => exact hPQ j _ h
  | self fx tys ih =>
    refine allLB_mono b _ _ (fun y hy => hX _ _ _ _ y (fun j a ha => ?_) hy) v h
    exact ih j (X := X₀) (fun _ (y : PEmpty) => y.elim) (fun _ _ _ _ (y : PEmpty) => y.elim) a ha
  | nest e fx tys ih =>
    refine allLB_mono _ _ _ (fun x hx => (M e).allL_mono _ _ x (fun j a ha => ?_) hx) v h
    exact ih j PX hX a ha

theorem callL_true {X : Fam} (PX : ∀ {ps Z}, LPred Z → X ps Z → Prop)
    (hmono : ∀ ps Z (P Q : LPred Z) (y : X ps Z), (∀ j a, P j a → Q j a) → PX P y → PX Q y)
    (hX : ∀ ps Z (y : X ps Z), PX (fun _ _ => True) y)
    (τ : PCode) {Z : Nat → TyM} (v : El (interp M b X Z τ)) :
    callL M b (X := X) PX τ (fun _ _ => True) v := by
  induction τ generalizing X with
  | ext _ | par _ => trivial
  | self fx tys ih =>
    refine allLB_true b _ (fun y => hmono _ _ _ _ y (fun j a _ => ?_) (hX _ _ y)) v
    exact ih j (X := X₀) (fun _ (y : PEmpty) => y.elim) (fun _ _ _ _ (y : PEmpty) => y.elim)
      (fun _ _ (y : PEmpty) => y.elim) a
  | nest e fx tys ih =>
    refine allLB_true _ _ (fun x => (M e).allL_mono _ _ x (fun j a _ => ?_) ((M e).allL_true x)) v
    exact ih j PX hmono hX a

theorem cmapZ_id {X : Fam} (fXZ : ∀ {ps Z Z'}, LMap Z Z' → X ps Z → X ps Z')
    (hX : ∀ ps Z (f : LMap Z Z) (y : X ps Z), (∀ j a, f j a = a) → fXZ f y = y)
    (τ : PCode) {Z : Nat → TyM} (f : LMap Z Z) (hf : ∀ j a, f j a = a)
    (v : El (interp M b X Z τ)) : cmapZ M b (X := X) fXZ τ f v = v := by
  induction τ generalizing X with
  | ext _ => rfl
  | par j => exact hf j v
  | self fx tys ih =>
    refine (mapB_congr b (fun y => hX _ _ _ y (fun j a => ?_)) v).trans (mapB_id b v)
    exact ih j (X := X₀) (fun _ (y : PEmpty) => y.elim) (fun _ _ _ (y : PEmpty) => y.elim) a
  | nest e fx tys ih =>
    refine (mapB_congr _ (fun x => ?_) v).trans (mapB_id _ v)
    have : (fun j => cmapZ M b (X := X) fXZ (tys j) f) = fun _ => id :=
      funext fun j => funext fun a => ih j (X := X) @fXZ hX a
    simp only [this, (M e).map_id, id]

theorem cmapZ_comp {X : Fam} (fXZ : ∀ {ps Z Z'}, LMap Z Z' → X ps Z → X ps Z')
    (hX : ∀ ps Z Z' Z'' (f : LMap Z Z') (g : LMap Z' Z'') (y : X ps Z),
      fXZ g (fXZ f y) = fXZ (fun j => g j ∘ f j) y)
    (τ : PCode) {Z Z' Z'' : Nat → TyM} (f : LMap Z Z') (g : LMap Z' Z'')
    (v : El (interp M b X Z τ)) :
    cmapZ M b (X := X) fXZ τ g (cmapZ M b (X := X) fXZ τ f v) =
      cmapZ M b (X := X) fXZ τ (fun j => g j ∘ f j) v := by
  induction τ generalizing X with
  | ext _ | par _ => rfl
  | self fx tys ih =>
    refine (mapB_comp b _ _ v).trans (mapB_congr b (fun y => ?_) v)
    simp only [Function.comp]
    rw [hX]
    congr 1
    funext j a
    exact ih j (X := X₀) (fun _ (y : PEmpty) => y.elim) (fun _ _ _ _ _ _ (y : PEmpty) => y.elim) a
  | nest e fx tys ih =>
    refine (mapB_comp _ _ _ v).trans (mapB_congr _ (fun x => ?_) v)
    simp only [Function.comp]
    rw [(M e).map_comp]
    congr 1
    funext j a
    exact ih j (X := X) @fXZ hX a

theorem craw_cmapZ {X : Fam} (fXZ : ∀ {ps Z Z'}, LMap Z Z' → X ps Z → X ps Z')
    (rX : ∀ {ps Z}, LRaw Z → X ps Z → Sem)
    (hX : ∀ ps Z Z' (f : LMap Z Z') (r : LRaw Z') (y : X ps Z),
      rX r (fXZ f y) = rX (fun j => r j ∘ f j) y)
    (τ : PCode) {Z Z' : Nat → TyM} (f : LMap Z Z') (r : LRaw Z') (v : El (interp M b X Z τ)) :
    craw M b (X := X) rX τ r (cmapZ M b (X := X) fXZ τ f v) =
      craw M b (X := X) rX τ (fun j => r j ∘ f j) v := by
  induction τ generalizing X with
  | ext _ | par _ => rfl
  | self fx tys ih =>
    refine (rawB_map b _ _ v).trans (congrArg (fun F => rawB b F v) (funext fun y => ?_))
    simp only [Function.comp]
    rw [hX]
    congr 1
    funext j a
    exact ih j (X := X₀) (fun _ (y : PEmpty) => y.elim) (fun _ (y : PEmpty) => y.elim)
      (fun _ _ _ _ _ (y : PEmpty) => y.elim) a
  | nest e fx tys ih =>
    refine (rawB_map _ _ _ v).trans (congrArg (fun F => rawB _ F v) (funext fun x => ?_))
    simp only [Function.comp]
    rw [(M e).raw_map]
    congr 1
    funext j a
    exact ih j (X := X) @fXZ @rX hX a

theorem callL_lift {X : Fam} (fXZ : ∀ {ps Z Z'}, LMap Z Z' → X ps Z → X ps Z')
    (PX : ∀ {ps Z}, LPred Z → X ps Z → Prop)
    (hmono : ∀ ps Z (P Q : LPred Z) (y : X ps Z), (∀ j a, P j a → Q j a) → PX P y → PX Q y)
    (hX : ∀ ps Z Z' (f : LMap Z Z') (y : X ps Z'), PX (fun j b => ∃ a, f j a = b) y →
      ∃ x, fXZ f x = y)
    (τ : PCode) {Z Z' : Nat → TyM} (f : LMap Z Z') (v' : El (interp M b X Z' τ))
    (h : callL M b (X := X) PX τ (fun j b => ∃ a, f j a = b) v') :
    ∃ v, cmapZ M b (X := X) fXZ τ f v = v' := by
  induction τ generalizing X with
  | ext _ => exact ⟨v', rfl⟩
  | par j => exact h
  | self fx tys ih =>
    refine allLB_lift b _ _ (fun y hy => hX _ _ _ _ y (hmono _ _ _ _ y (fun j l hl => ?_) hy)) v' h
    exact ih j (X := X₀) (fun _ (y : PEmpty) => y.elim) (fun _ (y : PEmpty) => y.elim)
      (fun _ _ _ _ (y : PEmpty) => y.elim) (fun _ _ _ _ (y : PEmpty) => y.elim) l hl
  | nest e fx tys ih =>
    refine allLB_lift _ _ _ (fun y hy => (M e).lift _ y ((M e).allL_mono _ _ y
      (fun j l hl => ?_) hy)) v' h
    exact ih j (X := X) @fXZ @PX hmono hX l hl

theorem callL_directed {X : Fam} (PX : ∀ {ps Z}, LPred Z → X ps Z → Prop)
    (hmono : ∀ ps Z (P Q : LPred Z) (y : X ps Z), (∀ j a, P j a → Q j a) → PX P y → PX Q y)
    (hX : ∀ ps Z (P : Nat → LPred Z) (y : X ps Z), (∀ k j a, P k j a → P (k + 1) j a) →
      PX (fun j a => ∃ k, P k j a) y → ∃ k, PX (P k) y)
    (τ : PCode) {Z : Nat → TyM} (P : Nat → LPred Z) (hP : ∀ k j a, P k j a → P (k + 1) j a)
    (v : El (interp M b X Z τ)) (h : callL M b (X := X) PX τ (fun j a => ∃ k, P k j a) v) :
    ∃ k, callL M b (X := X) PX τ (P k) v := by
  induction τ generalizing X with
  | ext _ => exact ⟨0, trivial⟩
  | par j => exact h
  | self fx tys ih =>
    have m₀ := callL_mono M b (X := X₀) (fun _ (y : PEmpty) => y.elim)
      (fun _ _ _ _ (y : PEmpty) => y.elim)
    refine allLB_directed b _ _ (fun y hy => hX _ _ (fun k j l => callL M b (X := X₀)
      (fun _ (y : PEmpty) => y.elim) (tys j) (P k) l) y
      (fun k j l hl => m₀ (tys j) _ _ (hP k) l hl)
      (hmono _ _ _ _ y (fun j l hl => ?_) hy)) v h
    exact ih j (X := X₀) (fun _ (y : PEmpty) => y.elim) (fun _ _ _ _ (y : PEmpty) => y.elim)
      (fun _ _ _ (y : PEmpty) => y.elim) l hl
  | nest e fx tys ih =>
    refine allLB_directed _ _ _ (fun y hy => (M e).directed (fun k j l => callL M b (X := X) PX
      (tys j) (P k) l) y (fun k j l hl => callL_mono M b PX hmono (tys j) _ _ (hP k) l hl)
      ((M e).allL_mono _ _ y (fun j l hl => ?_) hy)) v h
    exact ih j (X := X) @PX hmono hX l hl

/-- Surjectivity through `mapB`, at some index of a family of maps. -/
theorem mapB_surjK (b : Bool) {A : Nat → Type} {B : Type} (f : ∀ k, A k → B)
    (hf : ∀ y, ∃ k x, f k x = y) (y : El (tyB b B)) : ∃ k x, mapB b (f k) x = y := by
  cases b
  · exact hf y
  · obtain ⟨a⟩ := y.down
    obtain ⟨k, x, _⟩ := hf a
    exact ⟨k, ⟨⟨x⟩⟩, plift_eq _ _⟩

/-- A field of the colimit of a directed system comes from some stage, if its members do. -/
theorem cmapX_surj {Xs : Nat → Fam} {Y : Fam} (ι : ∀ k {ps Z}, Xs k ps Z → Y ps Z)
    (emb : ∀ k {ps Z}, Xs k ps Z → Xs (k + 1) ps Z)
    (hcoh : ∀ k ps Z (y : Xs k ps Z), ι (k + 1) (emb k y) = ι k y)
    (hsurj : ∀ ps Z (y : Y ps Z), ∃ k y₀, ι k y₀ = y)
    (τ : PCode) {Z : Nat → TyM} (v : El (interp M b Y Z τ)) :
    ∃ k v₀, cmapX M b (X := Xs k) (Y := Y) (ι k) τ v₀ = v := by
  induction τ with
  | ext _ | par _ => exact ⟨0, v, rfl⟩
  | self fx tys _ => exact mapB_surjK b (fun k => ι k) (hsurj _ _) v
  | nest e fx tys ih =>
    refine mapB_surjK _ (fun k => (M e).map fun j => cmapX M b (ι k) (tys j)) (fun x => ?_) v
    have hup : ∀ k j (l : El (interp M b Y Z (tys j))),
        (∃ v₀, cmapX M b (X := Xs k) (Y := Y) (ι k) (tys j) v₀ = l) →
        ∃ v₀, cmapX M b (X := Xs (k + 1)) (Y := Y) (ι (k + 1)) (tys j) v₀ = l := by
      rintro k j l ⟨v₀, rfl⟩
      refine ⟨cmapX M b (emb k) (tys j) v₀, ?_⟩
      rw [cmapX_comp]
      exact cmapX_congr M b _ _ (fun _ _ y => hcoh k _ _ y) _ _
    obtain ⟨k, hk⟩ := (M e).directed _ x hup
      ((M e).allL_mono _ _ x (fun j l _ => ih j l) ((M e).allL_true x))
    obtain ⟨x₀, hx₀⟩ := (M e).lift _ x hk
    exact ⟨k, x₀, hx₀⟩

end codeLaws

/-! ## Signatures and stages -/

/-- What the assembly reads off a declaration (docs/18 (I1)–(I6)): its constructors' arities,
its sort, which parameters are nestable, and the code of field `i` of constructor `c` at the
(blanked) parameters and the masked meanings of the earlier fields (the telescope, D64: a field
type may read earlier closed fields; a recursive, nested or parameter-typed field is never read,
docs/18 (I2), (I5)). -/
structure Sig where
  ar : List Nat
  isProp : Bool
  nestable : Nat → Bool
  code : List Sem → Nat → Nat → List Sem → PCode

/-- The parameters with the nestable positions, from `j` on, replaced by `err`. -/
def blankFrom (nb : Nat → Bool) : Nat → List Sem → List Sem
  | _, [] => []
  | j, s :: ss => (if nb j then .err else s) :: blankFrom nb (j + 1) ss

section stages
variable (S : Sig) (M : Nat → NModel)

/-- The parameters as the codes see them. -/
def Sig.blank (ps : List Sem) : List Sem := blankFrom S.nestable 0 ps

/-- One field and the rest of the telescope, which sees the field's masked meaning. -/
def Step (X : Fam) (Z : Nat → TyM) (τ : PCode) (K : Sem → Type) : Type :=
  Σ v : El (interp M S.isProp X Z τ), K (mask M S.isProp X Z τ v)

/-- The telescope of fields `i, …, i + n - 1` of constructor `c`, after the masked fields `e`. -/
def Tele (X : Fam) (Z : Nat → TyM) (ps : List Sem) (c : Nat) : Nat → Nat → List Sem → Type
  | _, 0, _ => PUnit
  | i, n + 1, e => Step S M X Z (S.code (S.blank ps) c i e) fun s => Tele X Z ps c (i + 1) n (e ++ [s])

def Step.mapX {X Y : Fam} (fX : ∀ {ps Z}, X ps Z → Y ps Z) {Z : Nat → TyM} {K K' : Sem → Type}
    (g : ∀ s, K s → K' s) : (τ : PCode) → Step S M X Z τ K → Step S M Y Z τ K'
  | .ext _, ⟨v, t⟩ => ⟨v, g _ t⟩
  | .par _, ⟨v, t⟩ => ⟨v, g _ t⟩
  | .self fx tys, ⟨v, t⟩ => ⟨cmapX M S.isProp (X := X) (Y := Y) fX (.self fx tys) v, g _ t⟩
  | .nest e fx tys, ⟨v, t⟩ => ⟨cmapX M S.isProp (X := X) (Y := Y) fX (.nest e fx tys) v, g _ t⟩

def Tele.mapX {X Y : Fam} (fX : ∀ {ps Z}, X ps Z → Y ps Z) {Z : Nat → TyM} {ps : List Sem}
    {c : Nat} : (i n : Nat) → (e : List Sem) → Tele S M X Z ps c i n e → Tele S M Y Z ps c i n e
  | _, 0, _, t => t
  | i, n + 1, e, t => Step.mapX S M (X := X) (Y := Y) @fX
      (fun s => Tele.mapX (X := X) (Y := Y) @fX (i + 1) n (e ++ [s])) _ t

def Step.mapZ {X : Fam} (fX : ∀ {ps Z Z'}, LMap Z Z' → X ps Z → X ps Z') {Z Z' : Nat → TyM}
    (f : LMap Z Z') {K K' : Sem → Type} (g : ∀ s, K s → K' s) :
    (τ : PCode) → Step S M X Z τ K → Step S M X Z' τ K'
  | .ext _, ⟨v, t⟩ => ⟨v, g _ t⟩
  | .par j, ⟨v, t⟩ => ⟨f j v, g _ t⟩
  | .self fx tys, ⟨v, t⟩ => ⟨cmapZ M S.isProp (X := X) fX (.self fx tys) f v, g _ t⟩
  | .nest e fx tys, ⟨v, t⟩ => ⟨cmapZ M S.isProp (X := X) fX (.nest e fx tys) f v, g _ t⟩

def Tele.mapZ {X : Fam} (fX : ∀ {ps Z Z'}, LMap Z Z' → X ps Z → X ps Z') {Z Z' : Nat → TyM}
    (f : LMap Z Z') {ps : List Sem} {c : Nat} :
    (i n : Nat) → (e : List Sem) → Tele S M X Z ps c i n e → Tele S M X Z' ps c i n e
  | _, 0, _, t => t
  | i, n + 1, e, t => Step.mapZ S M (X := X) @fX f
      (fun s => Tele.mapZ (X := X) @fX f (i + 1) n (e ++ [s])) _ t

def Step.raw {X : Fam} (rX : ∀ {ps Z}, LRaw Z → X ps Z → Sem) {Z : Nat → TyM} (r : LRaw Z)
    {K : Sem → Type} (rest : ∀ s, K s → List Sem) (τ : PCode) : Step S M X Z τ K → List Sem
  | ⟨v, t⟩ => craw M S.isProp (X := X) @rX τ r v :: rest _ t

def Tele.raw {X : Fam} (rX : ∀ {ps Z}, LRaw Z → X ps Z → Sem) {Z : Nat → TyM} (r : LRaw Z)
    {ps : List Sem} {c : Nat} : (i n : Nat) → (e : List Sem) → Tele S M X Z ps c i n e → List Sem
  | _, 0, _, _ => []
  | i, n + 1, e, t => Step.raw S M (X := X) @rX r (fun s => Tele.raw (X := X) @rX r (i + 1) n (e ++ [s])) _ t

def Step.allL {X : Fam} (PX : ∀ {ps Z}, LPred Z → X ps Z → Prop) {Z : Nat → TyM} (P : LPred Z)
    {K : Sem → Type} (rest : ∀ s, K s → Prop) (τ : PCode) : Step S M X Z τ K → Prop
  | ⟨v, t⟩ => callL M S.isProp (X := X) @PX τ P v ∧ rest _ t

def Tele.allL {X : Fam} (PX : ∀ {ps Z}, LPred Z → X ps Z → Prop) {Z : Nat → TyM} (P : LPred Z)
    {ps : List Sem} {c : Nat} : (i n : Nat) → (e : List Sem) → Tele S M X Z ps c i n e → Prop
  | _, 0, _, _ => True
  | i, n + 1, e, t => Step.allL S M (X := X) @PX P (fun s => Tele.allL (X := X) @PX P (i + 1) n (e ++ [s])) _ t

/-- Stage `k`: members of depth below `k`. Stage `k + 1` at `ps` is the `Σ` over constructors
of the telescope with the declaration read as stage `k`, at every parameter tuple. -/
def stage : Nat → Fam
  | 0 => fun _ _ => PEmpty
  | k + 1 => fun ps Z => Σ c : Fin S.ar.length, Tele S M (stage k) Z ps c 0 S.ar[c] []

/-- Stage `k` into stage `k + 1`. -/
def emb : (k : Nat) → ∀ {ps Z}, stage S M k ps Z → stage S M (k + 1) ps Z
  | 0, _, _, y => y.elim
  | k + 1, _, _, ⟨c, t⟩ => ⟨c, Tele.mapX S M (X := stage S M k) (Y := stage S M (k + 1))
      (fun y => emb k y) _ _ _ t⟩

/-- A stage is functorial in the leaves. -/
def smap : (k : Nat) → ∀ {ps Z Z'}, LMap Z Z' → stage S M k ps Z → stage S M k ps Z'
  | 0, _, _, _, _, y => y.elim
  | k + 1, _, _, _, f, ⟨c, t⟩ => ⟨c, Tele.mapZ S M (X := stage S M k)
      (fun f y => smap k f y) f _ _ _ t⟩

/-- The raw meaning of a stage member: its constructor and its fields' raw meanings, the
leaves read by `r`. It does not depend on the stage. -/
def sraw : (k : Nat) → ∀ {ps Z}, LRaw Z → stage S M k ps Z → Sem
  | 0, _, _, _, y => y.elim
  | k + 1, _, _, r, ⟨c, t⟩ => .ctor "" c.val (Tele.raw S M (X := stage S M k)
      (fun r y => sraw k r y) r _ _ _ t)

/-- A predicate on the leaves of a stage member. -/
def sallL : (k : Nat) → ∀ {ps Z}, LPred Z → stage S M k ps Z → Prop
  | 0, _, _, _, y => y.elim
  | k + 1, _, _, P, ⟨_, t⟩ => Tele.allL S M (X := stage S M k) (fun P y => sallL k P y) P _ _ _ t

end stages

/-! ## Laws of telescopes

A field at a time (`Step`, by cases on the code), then by induction on the length. -/

theorem craw_congr (M : Nat → NModel) (b : Bool) {X : Fam} (rX rX' : ∀ {ps Z}, LRaw Z → X ps Z → Sem)
    (h : ∀ ps Z (r : LRaw Z) (y : X ps Z), rX r y = rX' r y) (τ : PCode) {Z : Nat → TyM}
    (r : LRaw Z) (v : El (interp M b X Z τ)) :
    craw M b (X := X) rX τ r v = craw M b (X := X) rX' τ r v := by
  induction τ with
  | ext _ | par _ => rfl
  | self fx tys _ =>
    exact congrArg (fun F => rawB b F v) (funext fun y => h _ _ _ y)
  | nest e fx tys ih =>
    refine congrArg (fun F => rawB _ F v) (funext fun x => ?_)
    exact congrArg (fun R => (M e).raw R x) (funext fun j => funext fun a => ih j a)

section teleLaws
variable (S : Sig) (M : Nat → NModel)

theorem Step.raw_congr {X : Fam} (rX rX' : ∀ {ps Z}, LRaw Z → X ps Z → Sem)
    (h : ∀ ps Z (r : LRaw Z) (y : X ps Z), rX r y = rX' r y) {Z : Nat → TyM} (r : LRaw Z)
    {K : Sem → Type} (rest rest' : ∀ s, K s → List Sem) (hr : ∀ s k, rest s k = rest' s k)
    (τ : PCode) (st : Step S M X Z τ K) :
    Step.raw S M (X := X) @rX r rest τ st = Step.raw S M (X := X) @rX' r rest' τ st := by
  obtain ⟨v, t⟩ := st
  simp only [Step.raw, hr, craw_congr M S.isProp @rX @rX' h]

theorem Tele.raw_congr {X : Fam} (rX rX' : ∀ {ps Z}, LRaw Z → X ps Z → Sem)
    (h : ∀ ps Z (r : LRaw Z) (y : X ps Z), rX r y = rX' r y) {Z : Nat → TyM} (r : LRaw Z)
    {ps : List Sem} {c : Nat} (i n : Nat) (e : List Sem) (t : Tele S M X Z ps c i n e) :
    Tele.raw S M (X := X) @rX r i n e t = Tele.raw S M (X := X) @rX' r i n e t := by
  induction n generalizing i e with
  | zero => rfl
  | succ n ih => exact Step.raw_congr S M @rX @rX' h r _ _ (fun s k => ih _ _ k) _ t

theorem Step.raw_mapX {X Y : Fam} (fX : ∀ {ps Z}, X ps Z → Y ps Z)
    (rY : ∀ {ps Z}, LRaw Z → Y ps Z → Sem) {Z : Nat → TyM} (r : LRaw Z) {K K' : Sem → Type}
    (g : ∀ s, K s → K' s) (rest : ∀ s, K' s → List Sem) (τ : PCode) (st : Step S M X Z τ K) :
    Step.raw S M (X := Y) @rY r rest τ (Step.mapX S M (X := X) (Y := Y) @fX g τ st) =
      Step.raw S M (X := X) (fun r y => rY r (fX y)) r (fun s k => rest s (g s k)) τ st := by
  obtain ⟨v, t⟩ := st
  cases τ <;> simp only [Step.mapX, Step.raw] <;>
    exact congrArg (· :: _) (craw_cmapX M S.isProp @fX @rY _ r v)

theorem Tele.raw_mapX {X Y : Fam} (fX : ∀ {ps Z}, X ps Z → Y ps Z)
    (rY : ∀ {ps Z}, LRaw Z → Y ps Z → Sem) {Z : Nat → TyM} (r : LRaw Z) {ps : List Sem} {c : Nat}
    (i n : Nat) (e : List Sem) (t : Tele S M X Z ps c i n e) :
    Tele.raw S M (X := Y) @rY r i n e (Tele.mapX S M (X := X) (Y := Y) @fX i n e t) =
      Tele.raw S M (X := X) (fun r y => rY r (fX y)) r i n e t := by
  induction n generalizing i e with
  | zero => rfl
  | succ n ih =>
    exact (Step.raw_mapX S M @fX @rY r _ _ _ t).trans
      (Step.raw_congr S M _ _ (fun _ _ _ _ => rfl) r _ _ (fun s k => ih _ _ k) _ t)

theorem Step.raw_mapZ {X : Fam} (fX : ∀ {ps Z Z'}, LMap Z Z' → X ps Z → X ps Z')
    (rX : ∀ {ps Z}, LRaw Z → X ps Z → Sem)
    (hX : ∀ ps Z Z' (f : LMap Z Z') (r : LRaw Z') (y : X ps Z),
      rX r (fX f y) = rX (fun j => r j ∘ f j) y)
    {Z Z' : Nat → TyM} (f : LMap Z Z') (r : LRaw Z') {K K' : Sem → Type}
    (g : ∀ s, K s → K' s) (rest : ∀ s, K' s → List Sem) (τ : PCode) (st : Step S M X Z τ K) :
    Step.raw S M (X := X) @rX r rest τ (Step.mapZ S M (X := X) @fX f g τ st) =
      Step.raw S M (X := X) @rX (fun j => r j ∘ f j) (fun s k => rest s (g s k)) τ st := by
  obtain ⟨v, t⟩ := st
  cases τ <;> simp only [Step.mapZ, Step.raw] <;>
    exact congrArg (· :: _) (craw_cmapZ M S.isProp @fX @rX hX _ f r v)

theorem Tele.raw_mapZ {X : Fam} (fX : ∀ {ps Z Z'}, LMap Z Z' → X ps Z → X ps Z')
    (rX : ∀ {ps Z}, LRaw Z → X ps Z → Sem)
    (hX : ∀ ps Z Z' (f : LMap Z Z') (r : LRaw Z') (y : X ps Z),
      rX r (fX f y) = rX (fun j => r j ∘ f j) y)
    {Z Z' : Nat → TyM} (f : LMap Z Z') (r : LRaw Z') {ps : List Sem} {c : Nat}
    (i n : Nat) (e : List Sem) (t : Tele S M X Z ps c i n e) :
    Tele.raw S M (X := X) @rX r i n e (Tele.mapZ S M (X := X) @fX f i n e t) =
      Tele.raw S M (X := X) @rX (fun j => r j ∘ f j) i n e t := by
  induction n generalizing i e with
  | zero => rfl
  | succ n ih =>
    exact (Step.raw_mapZ S M @fX @rX hX f r _ _ _ t).trans
      (Step.raw_congr S M _ _ (fun _ _ _ _ => rfl) _ _ _ (fun s k => ih _ _ k) _ t)

theorem Step.raw_rel {X₁ X₂ : Fam} (rX₁ : ∀ {ps Z}, LRaw Z → X₁ ps Z → Sem)
    (rX₂ : ∀ {ps Z}, LRaw Z → X₂ ps Z → Sem)
    (hX : ∀ ps Za Zb (ra ra' : LRaw Za) (rb rb' : LRaw Zb) (ya : X₁ ps Za) (yb : X₂ ps Zb),
      LRel ra ra' rb rb' → rX₁ ra ya = rX₂ rb yb → rX₁ ra' ya = rX₂ rb' yb)
    {Z₁ Z₂ : Nat → TyM} (r₁ r₁' : LRaw Z₁) (r₂ r₂' : LRaw Z₂) (hr : LRel r₁ r₁' r₂ r₂')
    {K₁ K₂ : Sem → Type} (rest₁ rest₁' : ∀ s, K₁ s → List Sem) (rest₂ rest₂' : ∀ s, K₂ s → List Sem)
    (hrest : ∀ s₁ s₂, s₁ = s₂ → ∀ (k₁ : K₁ s₁) (k₂ : K₂ s₂),
      rest₁ s₁ k₁ = rest₂ s₂ k₂ → rest₁' s₁ k₁ = rest₂' s₂ k₂)
    (τ : PCode) (st₁ : Step S M X₁ Z₁ τ K₁) (st₂ : Step S M X₂ Z₂ τ K₂)
    (h : Step.raw S M (X := X₁) @rX₁ r₁ rest₁ τ st₁ = Step.raw S M (X := X₂) @rX₂ r₂ rest₂ τ st₂) :
    Step.raw S M (X := X₁) @rX₁ r₁' rest₁' τ st₁ = Step.raw S M (X := X₂) @rX₂ r₂' rest₂' τ st₂ := by
  obtain ⟨v₁, k₁⟩ := st₁
  obtain ⟨v₂, k₂⟩ := st₂
  simp only [Step.raw, List.cons.injEq] at h ⊢
  exact ⟨craw_rel M S.isProp @rX₁ @rX₂ hX τ r₁ r₁' r₂ r₂' hr v₁ v₂ h.1,
    hrest _ _ (mask_rel M S.isProp @rX₁ @rX₂ τ r₁ r₂ v₁ v₂ h.1) k₁ k₂ h.2⟩

theorem Tele.raw_rel {X₁ X₂ : Fam} (rX₁ : ∀ {ps Z}, LRaw Z → X₁ ps Z → Sem)
    (rX₂ : ∀ {ps Z}, LRaw Z → X₂ ps Z → Sem)
    (hX : ∀ ps Za Zb (ra ra' : LRaw Za) (rb rb' : LRaw Zb) (ya : X₁ ps Za) (yb : X₂ ps Zb),
      LRel ra ra' rb rb' → rX₁ ra ya = rX₂ rb yb → rX₁ ra' ya = rX₂ rb' yb)
    {Z₁ Z₂ : Nat → TyM} (r₁ r₁' : LRaw Z₁) (r₂ r₂' : LRaw Z₂) (hr : LRel r₁ r₁' r₂ r₂')
    {ps : List Sem} {c : Nat} (i n : Nat) (e : List Sem)
    (t₁ : Tele S M X₁ Z₁ ps c i n e) (t₂ : Tele S M X₂ Z₂ ps c i n e)
    (h : Tele.raw S M (X := X₁) @rX₁ r₁ i n e t₁ = Tele.raw S M (X := X₂) @rX₂ r₂ i n e t₂) :
    Tele.raw S M (X := X₁) @rX₁ r₁' i n e t₁ = Tele.raw S M (X := X₂) @rX₂ r₂' i n e t₂ := by
  induction n generalizing i e with
  | zero => rfl
  | succ n ih =>
    refine Step.raw_rel S M @rX₁ @rX₂ hX r₁ r₁' r₂ r₂' hr _ _ _ _ ?_ _ t₁ t₂ h
    intro s₁ s₂ hs k₁ k₂ hk
    subst hs
    exact ih _ _ k₁ k₂ hk

theorem Tele.raw_inj {X : Fam} (rX : ∀ {ps Z}, LRaw Z → X ps Z → Sem)
    (hX : ∀ ps Z (r : LRaw Z), (∀ j, Function.Injective (r j)) → Function.Injective (rX (ps := ps) r))
    {Z : Nat → TyM} (r : LRaw Z) (hr : ∀ j, Function.Injective (r j)) {ps : List Sem} {c : Nat}
    (i n : Nat) (e : List Sem) (t t' : Tele S M X Z ps c i n e)
    (h : Tele.raw S M (X := X) @rX r i n e t = Tele.raw S M (X := X) @rX r i n e t') : t = t' := by
  induction n generalizing i e with
  | zero => rfl
  | succ n ih =>
    obtain ⟨v, k⟩ := t
    obtain ⟨v', k'⟩ := t'
    simp only [Tele.raw, Step.raw, List.cons.injEq] at h
    obtain rfl := craw_inj M S.isProp @rX hX _ r hr h.1
    obtain rfl := ih _ _ k k' h.2
    rfl

theorem Step.mapX_comp {X Y W : Fam} (fX : ∀ {ps Z}, X ps Z → Y ps Z)
    (gX : ∀ {ps Z}, Y ps Z → W ps Z) {Z : Nat → TyM} {K K' K'' : Sem → Type}
    (f : ∀ s, K s → K' s) (g : ∀ s, K' s → K'' s) (τ : PCode) (st : Step S M X Z τ K) :
    Step.mapX S M (X := Y) (Y := W) @gX g τ (Step.mapX S M (X := X) (Y := Y) @fX f τ st) =
      Step.mapX S M (X := X) (Y := W) (fun y => gX (fX y)) (fun s k => g s (f s k)) τ st := by
  obtain ⟨v, k⟩ := st
  cases τ
  case ext | par => rfl
  all_goals exact Sigma.ext (cmapX_comp M S.isProp @fX @gX _ v) HEq.rfl

theorem Tele.mapX_comp {X Y W : Fam} (fX : ∀ {ps Z}, X ps Z → Y ps Z)
    (gX : ∀ {ps Z}, Y ps Z → W ps Z) {Z : Nat → TyM} {ps : List Sem} {c : Nat}
    (i n : Nat) (e : List Sem) (t : Tele S M X Z ps c i n e) :
    Tele.mapX S M (X := Y) (Y := W) @gX i n e (Tele.mapX S M (X := X) (Y := Y) @fX i n e t) =
      Tele.mapX S M (X := X) (Y := W) (fun y => gX (fX y)) i n e t := by
  induction n generalizing i e with
  | zero => rfl
  | succ n ih =>
    refine (Step.mapX_comp S M @fX @gX _ _ _ t).trans ?_
    simp only [ih]
    rfl

theorem Tele.mapX_congr {X Y : Fam} (fX gX : ∀ {ps Z}, X ps Z → Y ps Z)
    (h : ∀ ps Z (y : X ps Z), fX y = gX y) {Z : Nat → TyM} {ps : List Sem} {c : Nat}
    (i n : Nat) (e : List Sem) (t : Tele S M X Z ps c i n e) :
    Tele.mapX S M (X := X) (Y := Y) @fX i n e t = Tele.mapX S M (X := X) (Y := Y) @gX i n e t := by
  have : (@fX) = (@gX) := by
    funext ps Z y
    exact h ps Z y
  rw [this]

theorem Step.mapZ_id {X : Fam} (fXZ : ∀ {ps Z Z'}, LMap Z Z' → X ps Z → X ps Z')
    (hX : ∀ ps Z (f : LMap Z Z) (y : X ps Z), (∀ j a, f j a = a) → fXZ f y = y)
    {Z : Nat → TyM} (f : LMap Z Z) (hf : ∀ j a, f j a = a) {K : Sem → Type}
    (g : ∀ s, K s → K s) (hg : ∀ s k, g s k = k) (τ : PCode) (st : Step S M X Z τ K) :
    Step.mapZ S M (X := X) @fXZ f g τ st = st := by
  obtain ⟨v, k⟩ := st
  cases τ
  case ext => exact Sigma.ext rfl (heq_of_eq (hg _ k))
  case par j => exact Sigma.ext (hf j v) (heq_of_eq (hg _ k))
  all_goals exact Sigma.ext (cmapZ_id M S.isProp @fXZ hX _ f hf v) (heq_of_eq (hg _ k))

theorem Tele.mapZ_id {X : Fam} (fXZ : ∀ {ps Z Z'}, LMap Z Z' → X ps Z → X ps Z')
    (hX : ∀ ps Z (f : LMap Z Z) (y : X ps Z), (∀ j a, f j a = a) → fXZ f y = y)
    {Z : Nat → TyM} (f : LMap Z Z) (hf : ∀ j a, f j a = a) {ps : List Sem} {c : Nat}
    (i n : Nat) (e : List Sem) (t : Tele S M X Z ps c i n e) :
    Tele.mapZ S M (X := X) @fXZ f i n e t = t := by
  induction n generalizing i e with
  | zero => rfl
  | succ n ih => exact Step.mapZ_id S M @fXZ hX f hf _ (fun s k => ih _ _ k) _ t

theorem Step.mapZ_comp {X : Fam} (fXZ : ∀ {ps Z Z'}, LMap Z Z' → X ps Z → X ps Z')
    (hX : ∀ ps Z Z' Z'' (f : LMap Z Z') (g : LMap Z' Z'') (y : X ps Z),
      fXZ g (fXZ f y) = fXZ (fun j => g j ∘ f j) y)
    {Z Z' Z'' : Nat → TyM} (f : LMap Z Z') (f' : LMap Z' Z'') {K K' K'' : Sem → Type}
    (g : ∀ s, K s → K' s) (g' : ∀ s, K' s → K'' s) (τ : PCode) (st : Step S M X Z τ K) :
    Step.mapZ S M (X := X) @fXZ f' g' τ (Step.mapZ S M (X := X) @fXZ f g τ st) =
      Step.mapZ S M (X := X) @fXZ (fun j => f' j ∘ f j) (fun s k => g' s (g s k)) τ st := by
  obtain ⟨v, k⟩ := st
  cases τ
  case ext | par => rfl
  all_goals exact Sigma.ext (cmapZ_comp M S.isProp @fXZ hX _ f f' v) HEq.rfl

theorem Tele.mapZ_comp {X : Fam} (fXZ : ∀ {ps Z Z'}, LMap Z Z' → X ps Z → X ps Z')
    (hX : ∀ ps Z Z' Z'' (f : LMap Z Z') (g : LMap Z' Z'') (y : X ps Z),
      fXZ g (fXZ f y) = fXZ (fun j => g j ∘ f j) y)
    {Z Z' Z'' : Nat → TyM} (f : LMap Z Z') (f' : LMap Z' Z'') {ps : List Sem} {c : Nat}
    (i n : Nat) (e : List Sem) (t : Tele S M X Z ps c i n e) :
    Tele.mapZ S M (X := X) @fXZ f' i n e (Tele.mapZ S M (X := X) @fXZ f i n e t) =
      Tele.mapZ S M (X := X) @fXZ (fun j => f' j ∘ f j) i n e t := by
  induction n generalizing i e with
  | zero => rfl
  | succ n ih =>
    refine (Step.mapZ_comp S M @fXZ hX f f' _ _ _ t).trans ?_
    simp only [ih]
    rfl

theorem Tele.allL_mono {X : Fam} (PX : ∀ {ps Z}, LPred Z → X ps Z → Prop)
    (hX : ∀ ps Z (P Q : LPred Z) (y : X ps Z), (∀ j a, P j a → Q j a) → PX P y → PX Q y)
    {Z : Nat → TyM} (P Q : LPred Z) (hPQ : ∀ j a, P j a → Q j a) {ps : List Sem} {c : Nat}
    (i n : Nat) (e : List Sem) (t : Tele S M X Z ps c i n e)
    (h : Tele.allL S M (X := X) @PX P i n e t) : Tele.allL S M (X := X) @PX Q i n e t := by
  induction n generalizing i e with
  | zero => trivial
  | succ n ih =>
    obtain ⟨v, k⟩ := t
    exact ⟨callL_mono M S.isProp @PX hX _ P Q hPQ v h.1, ih _ _ k h.2⟩

theorem Tele.allL_true {X : Fam} (PX : ∀ {ps Z}, LPred Z → X ps Z → Prop)
    (hmono : ∀ ps Z (P Q : LPred Z) (y : X ps Z), (∀ j a, P j a → Q j a) → PX P y → PX Q y)
    (hX : ∀ ps Z (y : X ps Z), PX (fun _ _ => True) y)
    {Z : Nat → TyM} {ps : List Sem} {c : Nat} (i n : Nat) (e : List Sem)
    (t : Tele S M X Z ps c i n e) : Tele.allL S M (X := X) @PX (fun _ _ => True) i n e t := by
  induction n generalizing i e with
  | zero => trivial
  | succ n ih =>
    obtain ⟨v, k⟩ := t
    exact ⟨callL_true M S.isProp @PX hmono hX _ v, ih _ _ k⟩

theorem Step.lift {X : Fam} (fXZ : ∀ {ps Z Z'}, LMap Z Z' → X ps Z → X ps Z')
    (PX : ∀ {ps Z}, LPred Z → X ps Z → Prop)
    (hmono : ∀ ps Z (P Q : LPred Z) (y : X ps Z), (∀ j a, P j a → Q j a) → PX P y → PX Q y)
    (hX : ∀ ps Z Z' (f : LMap Z Z') (y : X ps Z'), PX (fun j b => ∃ a, f j a = b) y →
      ∃ x, fXZ f x = y)
    {Z Z' : Nat → TyM} (f : LMap Z Z') {K K' : Sem → Type} (g : ∀ s, K s → K' s)
    (rest : ∀ s, K' s → Prop) (hrest : ∀ s k', rest s k' → ∃ k, g s k = k')
    (τ : PCode) (st' : Step S M X Z' τ K')
    (h : Step.allL S M (X := X) @PX (fun j b => ∃ a, f j a = b) rest τ st') :
    ∃ st, Step.mapZ S M (X := X) @fXZ f g τ st = st' := by
  obtain ⟨v', k'⟩ := st'
  obtain ⟨hv, hk⟩ := h
  cases τ
  case ext T =>
    obtain ⟨k, rfl⟩ := hrest _ k' hk
    exact ⟨⟨v', k⟩, rfl⟩
  case par j =>
    obtain ⟨a, rfl⟩ := hv
    obtain ⟨k, rfl⟩ := hrest _ k' hk
    exact ⟨⟨a, k⟩, rfl⟩
  all_goals
    obtain ⟨v, rfl⟩ := callL_lift M S.isProp @fXZ @PX hmono hX _ f v' hv
    obtain ⟨k, rfl⟩ := hrest _ k' hk
    exact ⟨⟨v, k⟩, rfl⟩

theorem Tele.lift {X : Fam} (fXZ : ∀ {ps Z Z'}, LMap Z Z' → X ps Z → X ps Z')
    (PX : ∀ {ps Z}, LPred Z → X ps Z → Prop)
    (hmono : ∀ ps Z (P Q : LPred Z) (y : X ps Z), (∀ j a, P j a → Q j a) → PX P y → PX Q y)
    (hX : ∀ ps Z Z' (f : LMap Z Z') (y : X ps Z'), PX (fun j b => ∃ a, f j a = b) y →
      ∃ x, fXZ f x = y)
    {Z Z' : Nat → TyM} (f : LMap Z Z') {ps : List Sem} {c : Nat} (i n : Nat) (e : List Sem)
    (t' : Tele S M X Z' ps c i n e) (h : Tele.allL S M (X := X) @PX (fun j b => ∃ a, f j a = b) i n e t') :
    ∃ t, Tele.mapZ S M (X := X) @fXZ f i n e t = t' := by
  induction n generalizing i e with
  | zero => exact ⟨PUnit.unit, rfl⟩
  | succ n ih =>
    exact Step.lift S M @fXZ @PX hmono hX f _ _ (fun s k' hk => ih _ _ k' hk) _ t' h

theorem le_family {α : Type _} {P : Nat → α → Prop} (hP : ∀ k x, P k x → P (k + 1) x) {a b : Nat}
    (hab : a ≤ b) (x : α) (h : P a x) : P b x := by
  induction hab with
  | refl => exact h
  | step _ ih => exact hP _ _ ih

theorem Tele.directed {X : Fam} (PX : ∀ {ps Z}, LPred Z → X ps Z → Prop)
    (hmono : ∀ ps Z (P Q : LPred Z) (y : X ps Z), (∀ j a, P j a → Q j a) → PX P y → PX Q y)
    (hX : ∀ ps Z (P : Nat → LPred Z) (y : X ps Z), (∀ k j a, P k j a → P (k + 1) j a) →
      PX (fun j a => ∃ k, P k j a) y → ∃ k, PX (P k) y)
    {Z : Nat → TyM} (P : Nat → LPred Z) (hP : ∀ k j a, P k j a → P (k + 1) j a)
    {ps : List Sem} {c : Nat} (i n : Nat) (e : List Sem) (t : Tele S M X Z ps c i n e)
    (h : Tele.allL S M (X := X) @PX (fun j a => ∃ k, P k j a) i n e t) :
    ∃ k, Tele.allL S M (X := X) @PX (P k) i n e t := by
  have hm : ∀ k (i n e) (t : Tele S M X Z ps c i n e), Tele.allL S M (X := X) @PX (P k) i n e t →
      Tele.allL S M (X := X) @PX (P (k + 1)) i n e t :=
    fun k i n e t => Tele.allL_mono S M @PX hmono _ _ (hP k) i n e t
  induction n generalizing i e with
  | zero => exact ⟨0, trivial⟩
  | succ n ih =>
    obtain ⟨v, k⟩ := t
    obtain ⟨hv, hk⟩ := h
    obtain ⟨k₁, h₁⟩ := callL_directed M S.isProp @PX hmono hX _ P hP v hv
    obtain ⟨k₂, h₂⟩ := ih _ _ k hk
    refine ⟨max k₁ k₂, ?_, ?_⟩
    · exact le_family (P := fun k v => callL M S.isProp (X := X) @PX _ (P k) v)
        (fun k v hv => callL_mono M S.isProp @PX hmono _ _ _ (hP k) v hv) (Nat.le_max_left _ _) v h₁
    · exact le_family (P := fun k t => Tele.allL S M (X := X) @PX (P k) _ n _ t)
        (fun k t ht => hm k _ n _ t ht) (Nat.le_max_right _ _) k h₂

end teleLaws
