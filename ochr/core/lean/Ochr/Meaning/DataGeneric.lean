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

## Choices (also docs/31, "data-generic: choices")

* **Input.** One signature per declaration in program order (`Sig`, `Prog`): arities, sort,
  nestable positions, and a code per field as a function of the parameters and the masked
  earlier fields. The assembly reads codes off the field-type terms and must show that a code
  read at the colimit (`interp`) is the run's reading. That needs docs/18 (I1)–(I6) and three
  well-formedness facts: type codes only at nestable positions, `ext (tyOf s)` at positions
  taking a fixed parameter `s`, and field types reading only earlier closed fields.
* **Masking.** A field's code sees an earlier field's meaning only if that field is closed
  (`mask`); a recursive, nested or parameter-typed field shows `err`. So the telescope is the
  same at every stage. It is sound because no accepted field type reads such a field ((I1),
  (I2), nestability).
* **Nesting** is read through the earlier declaration's own carrier, as the run reads
  `List(Rose(A))`, not translated to mutual recursion. A mutual translation yields an
  auxiliary type only isomorphic to `List`'s carrier at `Rose`'s, and identifying the two would
  mean recovering parameters from a carrier, which is D8's problem. This needs the earlier
  carrier to be functorial and finitary in its leaves: the interface `NModel`, which every
  declaration also produces (`nmodel`). Declarations are modelled in order (`progModel`,
  `progEnv`, `progEnv_car`).
* **Leaf environments and blanking.** The core carrier `car S M ps Z` is built at parameters as
  the codes see them and a leaf environment `Z` (the nestable parameters' types). The data
  model passes the parameters blanked at the nestable positions and `Z = envOf ps`, so a
  carrier depends on a nestable parameter only through its `par` leaves.
* **Equality in the colimit** is equality of raw meanings (`sraw`: constructor and fields'
  raw meanings), read relative to a raw meaning of the leaves. `sraw_rel` (relational
  invariance) makes this well defined on the quotient and coherent under nesting.
* **`Prop`-sorted declarations** are the same fixed point. Their occurrences store
  `PLift (Nonempty _)` (a field means `•`), and leaves of hidden witnesses are reached
  existentially (`allLB`).
* **Field types are cut to `small`** (`Type₀` carriers and propositions), so packing succeeds
  exactly on members. This agrees with the run under (I6).
* **The rank is the first stage** (`crank`). `crank_self` is the law on the core carrier;
  `gRank_lt` is the interface's, through `recArgs` (`gRecArgs`). `recArgs` is returned only
  when the interface carrier is literally the core one, and `gRecArgs_wf` shows that it is for
  a well-formed occurrence. Nested paths (`Rose` → `List` → `Rose`) are not covered.
* **`fieldData`, `paramData` and `paramTy`** (the structured hints' data, D8) are passed
  through from the signature; the construction does not use them.
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
  /-- The readings the construction does not use, passed through to the data model: a
  parameter's type at the earlier parameters, and the structured hints' data (docs/31 D8) of a
  field's type (at the parameters and earlier fields) and of a parameter's type. -/
  paramTy : Nat → List Sem → TyM := fun _ _ => .err
  fieldData : List Sem → Nat → Nat → List Sem → Option (String × List Sem) := fun _ _ _ _ => none
  paramData : Nat → List Sem → Option (String × List Sem) := fun _ _ => none

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
  | i, n + 1, e => Step S M X Z (S.code ps c i e) fun s => Tele X Z ps c (i + 1) n (e ++ [s])

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

/-! ## Laws of stages, by induction on the stage -/

section stageLaws
variable (S : Sig) (M : Nat → NModel)

theorem sraw_emb : ∀ (k : Nat) {ps : List Sem} {Z : Nat → TyM} (r : LRaw Z) (y : stage S M k ps Z),
    sraw S M (k + 1) r (emb S M k y) = sraw S M k r y
  | 0, _, _, _, y => y.elim
  | k + 1, _, _, r, ⟨c, t⟩ => by
    simp only [emb, sraw]
    congr 1
    refine (Tele.raw_mapX S M _ _ r _ _ _ t).trans ?_
    exact Tele.raw_congr S M _ _ (fun _ _ r y => sraw_emb k r y) r _ _ _ t

theorem sraw_rel : ∀ (k₁ k₂ : Nat) {ps : List Sem} {Z₁ Z₂ : Nat → TyM} (r₁ r₁' : LRaw Z₁)
    (r₂ r₂' : LRaw Z₂) (y₁ : stage S M k₁ ps Z₁) (y₂ : stage S M k₂ ps Z₂),
    LRel r₁ r₁' r₂ r₂' → sraw S M k₁ r₁ y₁ = sraw S M k₂ r₂ y₂ →
      sraw S M k₁ r₁' y₁ = sraw S M k₂ r₂' y₂
  | 0, _, _, _, _, _, _, _, _, y₁, _, _, _ => y₁.elim
  | _ + 1, 0, _, _, _, _, _, _, _, _, y₂, _, _ => y₂.elim
  | k₁ + 1, k₂ + 1, _, _, _, r₁, r₁', r₂, r₂', ⟨c₁, t₁⟩, ⟨c₂, t₂⟩, hr, h => by
    simp only [sraw, Sem.ctor.injEq, true_and] at h ⊢
    obtain ⟨hc, ht⟩ := h
    obtain rfl : c₁ = c₂ := Fin.ext hc
    refine ⟨rfl, Tele.raw_rel S M _ _ ?_ r₁ r₁' r₂ r₂' hr _ _ _ t₁ t₂ ht⟩
    intro ps Za Zb ra ra' rb rb' ya yb hab hy
    exact sraw_rel k₁ k₂ ra ra' rb rb' ya yb hab hy

theorem sraw_inj : ∀ (k : Nat) {ps : List Sem} {Z : Nat → TyM} (r : LRaw Z),
    (∀ j, Function.Injective (r j)) → Function.Injective (sraw S M k (ps := ps) r)
  | 0, _, _, _, _, y, _, _ => y.elim
  | k + 1, _, _, r, hr, ⟨c₁, t₁⟩, ⟨c₂, t₂⟩, h => by
    simp only [sraw, Sem.ctor.injEq, true_and] at h
    obtain ⟨hc, ht⟩ := h
    obtain rfl : c₁ = c₂ := Fin.ext hc
    obtain rfl := Tele.raw_inj S M (X := stage S M k) (fun r y => sraw S M k r y)
      (fun _ _ r hr => sraw_inj k r hr) r hr _ _ _ t₁ t₂ ht
    rfl

theorem sraw_smap : ∀ (k : Nat) {ps : List Sem} {Z Z' : Nat → TyM} (f : LMap Z Z') (r : LRaw Z')
    (y : stage S M k ps Z), sraw S M k r (smap S M k f y) = sraw S M k (fun j => r j ∘ f j) y
  | 0, _, _, _, _, _, y => y.elim
  | k + 1, _, _, _, f, r, ⟨c, t⟩ => by
    simp only [smap, sraw]
    congr 1
    exact Tele.raw_mapZ S M (X := stage S M k) (fun f y => smap S M k f y) (fun r y => sraw S M k r y)
      (fun _ _ _ f r y => sraw_smap k f r y) f r _ _ _ t

theorem smap_id : ∀ (k : Nat) {ps : List Sem} {Z : Nat → TyM} (f : LMap Z Z),
    (∀ j a, f j a = a) → ∀ y : stage S M k ps Z, smap S M k f y = y
  | 0, _, _, _, _, y => y.elim
  | k + 1, _, _, f, hf, ⟨c, t⟩ => by
    simp only [smap]
    congr 1
    exact Tele.mapZ_id S M (X := stage S M k) (fun f y => smap S M k f y)
      (fun _ _ f y hf => smap_id k f hf y) f hf _ _ _ t

theorem smap_comp : ∀ (k : Nat) {ps : List Sem} {Z Z' Z'' : Nat → TyM} (f : LMap Z Z')
    (g : LMap Z' Z'') (y : stage S M k ps Z),
    smap S M k g (smap S M k f y) = smap S M k (fun j => g j ∘ f j) y
  | 0, _, _, _, _, _, _, y => y.elim
  | k + 1, _, _, _, _, f, g, ⟨c, t⟩ => by
    simp only [smap]
    congr 1
    exact Tele.mapZ_comp S M (X := stage S M k) (fun f y => smap S M k f y)
      (fun _ _ _ _ f g y => smap_comp k f g y) f g _ _ _ t

theorem sallL_mono : ∀ (k : Nat) {ps : List Sem} {Z : Nat → TyM} (P Q : LPred Z)
    (y : stage S M k ps Z), (∀ j a, P j a → Q j a) → sallL S M k P y → sallL S M k Q y
  | 0, _, _, _, _, y, _, _ => y.elim
  | k + 1, _, _, P, Q, ⟨_, t⟩, hPQ, h =>
    Tele.allL_mono S M (X := stage S M k) (fun P y => sallL S M k P y)
      (fun _ _ P Q y hPQ => sallL_mono k P Q y hPQ) P Q hPQ _ _ _ t h

theorem sallL_true : ∀ (k : Nat) {ps : List Sem} {Z : Nat → TyM} (y : stage S M k ps Z),
    sallL S M k (fun _ _ => True) y
  | 0, _, _, y => y.elim
  | k + 1, _, _, ⟨_, t⟩ =>
    Tele.allL_true S M (X := stage S M k) (fun P y => sallL S M k P y)
      (fun _ _ P Q y hPQ => sallL_mono S M k P Q y hPQ) (fun _ _ y => sallL_true k y) _ _ _ t

theorem slift : ∀ (k : Nat) {ps : List Sem} {Z Z' : Nat → TyM} (f : LMap Z Z')
    (y : stage S M k ps Z'), sallL S M k (fun j b => ∃ a, f j a = b) y → ∃ x, smap S M k f x = y
  | 0, _, _, _, _, y, _ => y.elim
  | k + 1, _, _, _, f, ⟨c, t⟩, h => by
    obtain ⟨t₀, rfl⟩ := Tele.lift S M (X := stage S M k) (fun f y => smap S M k f y)
      (fun P y => sallL S M k P y) (fun _ _ P Q y hPQ => sallL_mono S M k P Q y hPQ)
      (fun _ _ _ f y hy => slift k f y hy) f _ _ _ t h
    exact ⟨⟨c, t₀⟩, rfl⟩

theorem sdirected : ∀ (k : Nat) {ps : List Sem} {Z : Nat → TyM} (P : Nat → LPred Z)
    (y : stage S M k ps Z), (∀ m j a, P m j a → P (m + 1) j a) →
    sallL S M k (fun j a => ∃ m, P m j a) y → ∃ m, sallL S M k (P m) y
  | 0, _, _, _, y, _, _ => y.elim
  | k + 1, _, _, P, ⟨_, t⟩, hP, h =>
    Tele.directed S M (X := stage S M k) (fun P y => sallL S M k P y)
      (fun _ _ P Q y hPQ => sallL_mono S M k P Q y hPQ)
      (fun _ _ P y hP hy => sdirected k P y hP hy) P hP _ _ _ t h

end stageLaws

/-! ## The colimit -/

section colimit
variable (S : Sig) (M : Nat → NModel)

/-- Two stage members are one member of the colimit when their raw meanings agree. -/
def rel (ps : List Sem) (Z : Nat → TyM) : Setoid (Σ k, stage S M k ps Z) where
  r a b := sraw S M a.1 (canon Z) a.2 = sraw S M b.1 (canon Z) b.2
  iseqv := ⟨fun _ => rfl, fun h => h.symm, fun h₁ h₂ => h₁.trans h₂⟩

/-- The carrier: the colimit of the stages. -/
def car (ps : List Sem) (Z : Nat → TyM) : Type := Quotient (rel S M ps Z)

/-- A stage member as a member of the colimit. -/
def ι (k : Nat) {ps : List Sem} {Z : Nat → TyM} (y : stage S M k ps Z) : car S M ps Z :=
  Quotient.mk _ ⟨k, y⟩

theorem canon_rel (Z : Nat → TyM) (r r' : LRaw Z) (hr : ∀ j, Function.Injective (r j)) :
    LRel r r' r r' := fun j _ _ h => by rw [hr j h]

theorem ι_emb (k : Nat) {ps : List Sem} {Z : Nat → TyM} (y : stage S M k ps Z) :
    ι S M (k + 1) (emb S M k y) = ι S M k y :=
  Quotient.sound (sraw_emb S M k (canon Z) y)

theorem ι_surj {ps : List Sem} {Z : Nat → TyM} (x : car S M ps Z) : ∃ k y, ι S M k y = x := by
  obtain ⟨⟨k, y⟩, h⟩ := Quotient.exists_rep x
  exact ⟨k, y, h⟩

/-- The raw meaning of a colimit member, the leaves read by `r`. -/
def cRaw {ps : List Sem} {Z : Nat → TyM} (r : LRaw Z) : car S M ps Z → Sem :=
  Quotient.lift (fun a => sraw S M a.1 r a.2) fun a b h =>
    sraw_rel S M a.1 b.1 (canon Z) r (canon Z) r a.2 b.2 (canon_rel Z _ r (canon_inj Z)) h

theorem cRaw_ι (k : Nat) {ps : List Sem} {Z : Nat → TyM} (r : LRaw Z) (y : stage S M k ps Z) :
    cRaw S M r (ι S M k y) = sraw S M k r y := rfl

theorem cRaw_inj {ps : List Sem} {Z : Nat → TyM} (r : LRaw Z) (hr : ∀ j, Function.Injective (r j)) :
    Function.Injective (cRaw S M (ps := ps) r) := by
  intro x x' h
  obtain ⟨k, y, rfl⟩ := ι_surj S M x
  obtain ⟨k', y', rfl⟩ := ι_surj S M x'
  exact Quotient.sound (sraw_rel S M k k' r (canon Z) r (canon Z) y y'
    (canon_rel Z r _ hr) h)

/-- The colimit is functorial in the leaves. -/
def cMap {ps : List Sem} {Z Z' : Nat → TyM} (f : LMap Z Z') : car S M ps Z → car S M ps Z' :=
  Quotient.lift (fun a => ι S M a.1 (smap S M a.1 f a.2)) fun a b h => by
    apply Quotient.sound
    show sraw S M a.1 (canon Z') (smap S M a.1 f a.2) = sraw S M b.1 (canon Z') (smap S M b.1 f b.2)
    rw [sraw_smap, sraw_smap]
    exact sraw_rel S M a.1 b.1 (canon Z) _ (canon Z) _ a.2 b.2 (canon_rel Z _ _ (canon_inj Z)) h

theorem cMap_ι (k : Nat) {ps : List Sem} {Z Z' : Nat → TyM} (f : LMap Z Z') (y : stage S M k ps Z) :
    cMap S M f (ι S M k y) = ι S M k (smap S M k f y) := rfl

/-- A predicate on the leaves of a colimit member: of some representative. -/
def cAllL {ps : List Sem} {Z : Nat → TyM} (P : LPred Z) (x : car S M ps Z) : Prop :=
  ∃ k y, ι S M k y = x ∧ sallL S M k P y

/-- The declaration's model, for later declarations to nest into. -/
def nmodel : NModel where
  isProp := S.isProp
  car := car S M
  map := cMap S M
  raw := cRaw S M
  allL := cAllL S M
  map_id x := by
    obtain ⟨k, y, rfl⟩ := ι_surj S M x
    exact congrArg (ι S M k) (smap_id S M k _ (fun _ _ => rfl) y)
  map_comp f g x := by
    obtain ⟨k, y, rfl⟩ := ι_surj S M x
    exact congrArg (ι S M k) (smap_comp S M k f g y)
  raw_map f r x := by
    obtain ⟨k, y, rfl⟩ := ι_surj S M x
    exact sraw_smap S M k f r y
  raw_rel r₁ r₁' r₂ r₂' x₁ x₂ hr h := by
    obtain ⟨k₁, y₁, rfl⟩ := ι_surj S M x₁
    obtain ⟨k₂, y₂, rfl⟩ := ι_surj S M x₂
    exact sraw_rel S M k₁ k₂ r₁ r₁' r₂ r₂' y₁ y₂ hr h
  raw_inj r x y hr h := cRaw_inj S M r hr h
  allL_mono P Q x hPQ h := by
    obtain ⟨k, y, rfl, hy⟩ := h
    exact ⟨k, y, rfl, sallL_mono S M k P Q y hPQ hy⟩
  allL_true x := by
    obtain ⟨k, y, rfl⟩ := ι_surj S M x
    exact ⟨k, y, rfl, sallL_true S M k y⟩
  lift f y h := by
    obtain ⟨k, y₀, rfl, hy⟩ := h
    obtain ⟨x, rfl⟩ := slift S M k f y₀ hy
    exact ⟨ι S M k x, rfl⟩
  directed P x hP h := by
    obtain ⟨k, y, rfl, hy⟩ := h
    obtain ⟨m, hm⟩ := sdirected S M k P y hP hy
    exact ⟨m, k, y, rfl, hm⟩

end colimit

/-! ## The colimit is a fixed point

A member of the colimit is a constructor with a telescope of fields read at the colimit
(`view`), and every such pair is one (`unview`): the fields of a colimit telescope each come
from some stage (`cmapX_surj`), so all of them from one. -/

section view
variable (S : Sig) (M : Nat → NModel)

/-- A constructor and its fields, read at the colimit. -/
abbrev Fix (ps : List Sem) (Z : Nat → TyM) : Type :=
  Σ c : Fin S.ar.length, Tele S M (car S M) Z ps c 0 S.ar[c] []

/-- A stage's telescope read at the colimit. -/
abbrev teleι (k : Nat) {Z : Nat → TyM} {ps : List Sem} {c : Nat} {i n : Nat} {e : List Sem}
    (t : Tele S M (stage S M k) Z ps c i n e) : Tele S M (car S M) Z ps c i n e :=
  Tele.mapX S M (X := stage S M k) (Y := car S M) (fun y => ι S M k y) i n e t

theorem sraw_succ (k : Nat) {ps : List Sem} {Z : Nat → TyM} (r : LRaw Z) (c : Fin S.ar.length)
    (t : Tele S M (stage S M k) Z ps c 0 S.ar[c] []) :
    sraw S M (k + 1) r ⟨c, t⟩ =
      .ctor "" c.val (Tele.raw S M (X := car S M) (fun r x => cRaw S M r x) r 0 _ [] (teleι S M k t)) := by
  simp only [sraw]
  congr 1
  exact (Tele.raw_mapX S M (X := stage S M k) (Y := car S M) (fun y => ι S M k y)
    (fun r x => cRaw S M r x) r _ _ _ t).symm

/-- The fields of a stage member, read at the colimit. -/
def viewS {ps : List Sem} {Z : Nat → TyM} : (Σ k, stage S M k ps Z) → Fix S M ps Z
  | ⟨0, y⟩ => y.elim
  | ⟨k + 1, ⟨c, t⟩⟩ => ⟨c, teleι S M k t⟩

theorem viewS_wd {ps : List Sem} {Z : Nat → TyM} (a b : Σ k, stage S M k ps Z)
    (h : sraw S M a.1 (canon Z) a.2 = sraw S M b.1 (canon Z) b.2) : viewS S M a = viewS S M b := by
  obtain ⟨_ | k₁, y₁⟩ := a
  · exact y₁.elim
  obtain ⟨_ | k₂, y₂⟩ := b
  · exact y₂.elim
  obtain ⟨c₁, t₁⟩ := y₁
  obtain ⟨c₂, t₂⟩ := y₂
  simp only [sraw_succ, Sem.ctor.injEq, true_and] at h
  obtain ⟨hc, ht⟩ := h
  obtain rfl : c₁ = c₂ := Fin.ext hc
  have := Tele.raw_inj S M (X := car S M) (fun r x => cRaw S M r x)
    (fun _ _ r hr => cRaw_inj S M r hr) (canon Z) (canon_inj Z) _ _ _ _ _ ht
  simp only [viewS, this]

/-- A member of the colimit as a constructor and its fields. -/
def view {ps : List Sem} {Z : Nat → TyM} : car S M ps Z → Fix S M ps Z :=
  Quotient.lift (viewS S M) (viewS_wd S M)

theorem view_ι (k : Nat) {ps : List Sem} {Z : Nat → TyM} (c : Fin S.ar.length)
    (t : Tele S M (stage S M k) Z ps c 0 S.ar[c] []) :
    view S M (ι S M (k + 1) ⟨c, t⟩) = ⟨c, teleι S M k t⟩ := rfl

theorem teleι_up (k : Nat) {Z : Nat → TyM} {ps : List Sem} {c i n : Nat} {e : List Sem}
    (t₀ : Tele S M (stage S M k) Z ps c i n e) :
    teleι S M (k + 1) (Tele.mapX S M (X := stage S M k) (Y := stage S M (k + 1))
      (fun y => emb S M k y) i n e t₀) = teleι S M k t₀ := by
  simp only [teleι]
  rw [Tele.mapX_comp]
  exact Tele.mapX_congr S M _ _ (fun _ _ y => ι_emb S M k y) _ _ _ t₀

theorem le_prop {Q : Nat → Prop} (hQ : ∀ k, Q k → Q (k + 1)) {a b : Nat} (hab : a ≤ b) (h : Q a) :
    Q b := le_family (P := fun k (_ : Unit) => Q k) (fun k _ => hQ k) hab () h

theorem cmapX_ι_up (k : Nat) {Z : Nat → TyM} (τ : PCode)
    (v₀ : El (interp M S.isProp (stage S M k) Z τ)) :
    cmapX M S.isProp (X := stage S M (k + 1)) (Y := car S M) (fun y => ι S M (k + 1) y) τ
      (cmapX M S.isProp (X := stage S M k) (Y := stage S M (k + 1)) (fun y => emb S M k y) τ v₀) =
    cmapX M S.isProp (X := stage S M k) (Y := car S M) (fun y => ι S M k y) τ v₀ := by
  rw [cmapX_comp]
  exact cmapX_congr M S.isProp _ _ (fun _ _ y => ι_emb S M k y) τ v₀

theorem Step.surjι {Z : Nat → TyM} {K : Nat → Sem → Type} {K' : Sem → Type}
    (g : ∀ k s, K k s → K' s) (hrest : ∀ s (t' : K' s), ∃ k t₀, g k s t₀ = t')
    (hmono : ∀ k s (t₀ : K k s), ∃ t₁, g (k + 1) s t₁ = g k s t₀)
    (τ : PCode) (st : Step S M (car S M) Z τ K') :
    ∃ k, ∃ st₀ : Step S M (stage S M k) Z τ (K k),
      Step.mapX S M (X := stage S M k) (Y := car S M) (fun y => ι S M k y) (g k) τ st₀ = st := by
  obtain ⟨v, t'⟩ := st
  have up : ∀ k₁ k (hk : k₁ ≤ k) (s : Sem) (t₀ : K k₁ s), ∃ t₁ : K k s, g k s t₁ = g k₁ s t₀ :=
    fun k₁ k hk s t₀ => le_prop (Q := fun k => ∃ t₁ : K k s, g k s t₁ = g k₁ s t₀)
      (fun k ⟨t₁, h₁⟩ => (hmono k s t₁).imp fun _ h => h.trans h₁) hk ⟨t₀, rfl⟩
  cases τ
  case ext =>
    obtain ⟨k, t₀, rfl⟩ := hrest _ t'
    exact ⟨k, ⟨v, t₀⟩, rfl⟩
  case par =>
    obtain ⟨k, t₀, rfl⟩ := hrest _ t'
    exact ⟨k, ⟨v, t₀⟩, rfl⟩
  all_goals
    obtain ⟨k₁, v₀, hv⟩ := cmapX_surj M S.isProp (Xs := stage S M) (Y := car S M)
      (fun k {_ _} y => ι S M k y) (fun k {_ _} y => emb S M k y) (fun k _ _ y => ι_emb S M k y)
      (fun _ _ y => ι_surj S M y) _ v
    obtain ⟨k₂, t₀, rfl⟩ := hrest _ t'
    obtain ⟨v₁, hv₁⟩ := le_prop (Q := fun k => ∃ v₁ : El (interp M S.isProp (stage S M k) Z _),
        cmapX M S.isProp (X := stage S M k) (Y := car S M) (fun y => ι S M k y) _ v₁ = v)
      (fun k ⟨v₁, h₁⟩ => ⟨_, (cmapX_ι_up S M k _ v₁).trans h₁⟩) (Nat.le_max_left k₁ k₂) ⟨v₀, hv⟩
    obtain ⟨t₁, ht₁⟩ := up k₂ (max k₁ k₂) (Nat.le_max_right _ _) _ t₀
    exact ⟨max k₁ k₂, ⟨v₁, t₁⟩, Sigma.ext hv₁ (heq_of_eq ht₁)⟩

theorem Tele.surjι {Z : Nat → TyM} {ps : List Sem} {c : Nat} :
    ∀ (n i : Nat) (e : List Sem) (t : Tele S M (car S M) Z ps c i n e),
      ∃ k, ∃ t₀ : Tele S M (stage S M k) Z ps c i n e, teleι S M k t₀ = t
  | 0, _, _, _ => ⟨0, PUnit.unit, rfl⟩
  | n + 1, i, e, t =>
    Step.surjι S M (K := fun k s => Tele S M (stage S M k) Z ps c (i + 1) n (e ++ [s]))
      (fun k _ t₀ => teleι S M k t₀) (fun s t' => Tele.surjι n (i + 1) (e ++ [s]) t')
      (fun k _ t₀ => ⟨_, teleι_up S M k t₀⟩) _ t

/-- A constructor and its fields as a member of the colimit (classically: the fields are
lifted to a common stage). -/
noncomputable def unview {ps : List Sem} {Z : Nat → TyM} (w : Fix S M ps Z) : car S M ps Z :=
  have h := Tele.surjι S M _ _ _ w.2
  ι S M (Classical.choose h + 1)
    (show stage S M (Classical.choose h + 1) ps Z from ⟨w.1, Classical.choose (Classical.choose_spec h)⟩)

theorem view_unview {ps : List Sem} {Z : Nat → TyM} (w : Fix S M ps Z) :
    view S M (unview S M w) = w := by
  obtain ⟨c, t⟩ := w
  have h := Tele.surjι S M _ _ _ t
  exact Sigma.ext rfl (heq_of_eq (Classical.choose_spec (Classical.choose_spec h)))

theorem unview_view {ps : List Sem} {Z : Nat → TyM} (x : car S M ps Z) :
    unview S M (view S M x) = x := by
  obtain ⟨_ | k, y, rfl⟩ := ι_surj S M x
  · exact y.elim
  obtain ⟨c, t⟩ := y
  have h := Tele.surjι S M _ _ _ (teleι S M k t)
  have hs := Classical.choose_spec (Classical.choose_spec h)
  apply Quotient.sound
  change sraw S M (Classical.choose h + 1) (canon Z) ⟨c, Classical.choose (Classical.choose_spec h)⟩ =
    sraw S M (k + 1) (canon Z) ⟨c, t⟩
  rw [sraw_succ, sraw_succ]
  exact congrArg _ (congrArg _ hs)

end view

/-! ## Fields and packing -/

section decode
variable (S : Sig) (M : Nat → NModel)

def Step.fields {X : Fam} {Z : Nat → TyM} {K : Sem → Type} (rest : ∀ s, K s → List Sem)
    (τ : PCode) : Step S M X Z τ K → List Sem
  | ⟨v, k⟩ => enc _ v :: rest _ k

/-- The meanings of a telescope's fields. -/
def Tele.fields {X : Fam} {Z : Nat → TyM} {ps : List Sem} {c : Nat} :
    (i n : Nat) → (e : List Sem) → Tele S M X Z ps c i n e → List Sem
  | _, 0, _, _ => []
  | i, n + 1, e, t => Step.fields S M (fun s => Tele.fields (i + 1) n (e ++ [s])) _ t

/-- Read a list of meanings as a telescope: each a member of its field type, read at the
masked meanings of the earlier ones. -/
noncomputable def Tele.decode {X : Fam} {Z : Nat → TyM} {ps : List Sem} {c : Nat} :
    (i n : Nat) → (e : List Sem) → List Sem → Option (Tele S M X Z ps c i n e)
  | _, 0, _, [] => some PUnit.unit
  | _, 0, _, _ :: _ => none
  | _, _ + 1, _, [] => none
  | i, n + 1, e, f :: fs => (dec _ f).bind fun v =>
    (Tele.decode (i + 1) n (e ++ [mask M S.isProp X Z _ v]) fs).map fun k => ⟨v, k⟩

theorem Tele.decode_fields {X : Fam} {Z : Nat → TyM} {ps : List Sem} {c : Nat} :
    ∀ (i n : Nat) (e : List Sem) (t : Tele S M X Z ps c i n e),
      Tele.decode S M i n e (Tele.fields S M i n e t) = some t
  | _, 0, _, _ => rfl
  | i, n + 1, e, ⟨v, k⟩ => by
    simp only [Tele.fields, Step.fields, Tele.decode, dec_enc, Option.bind_some, Tele.decode_fields]
    rfl

theorem Tele.fields_decode {X : Fam} {Z : Nat → TyM} {ps : List Sem} {c : Nat} :
    ∀ (i n : Nat) (e : List Sem) (fs : List Sem) (t : Tele S M X Z ps c i n e),
      Tele.decode S M i n e fs = some t → Tele.fields S M i n e t = fs
  | _, 0, _, [], _, _ => rfl
  | _, 0, _, _ :: _, _, h => by simp [Tele.decode] at h
  | _, _ + 1, _, [], _, h => by simp [Tele.decode] at h
  | i, n + 1, e, f :: fs, t, h => by
    simp only [Tele.decode] at h
    cases hv : dec _ f with
    | none => rw [hv] at h; cases h
    | some v =>
      rw [hv, Option.bind_some] at h
      cases hk : Tele.decode S M (i + 1) n (e ++ [mask M S.isProp X Z _ v]) fs with
      | none => rw [hk] at h; cases h
      | some k =>
        rw [hk] at h
        obtain rfl : (⟨v, k⟩ : Tele S M X Z ps c i (n + 1) e) = t := Option.some.inj h
        simp only [Tele.fields, Step.fields, enc_of_dec hv, Tele.fields_decode _ _ _ fs k hk]

/-- The masked meanings of a list of fields, after `e`, from field `i` on. -/
def Sig.maskList (ps : List Sem) (c : Nat) : Nat → List Sem → List Sem → List Sem
  | _, e, [] => e
  | i, e, f :: fs => Sig.maskList ps c (i + 1) (e ++ [maskSem (S.code ps c i e) f]) fs

theorem isSome_map_eq {α β : Type} (g : α → β) (o : Option α) : (o.map g).isSome = o.isSome := by
  cases o <;> rfl

theorem Tele.decode_isSome {X : Fam} {Z : Nat → TyM} {ps : List Sem} {c : Nat} :
    ∀ (n i : Nat) (e : List Sem) (fs : List Sem),
      (Tele.decode S M (X := X) (Z := Z) (ps := ps) (c := c) i n e fs).isSome ↔
        fs.length = n ∧ ∀ j (h : j < fs.length), fs[j] ∈ₛ
          small (interp M S.isProp X Z (S.code ps c (i + j) (Sig.maskList S ps c i e (fs.take j))))
  | 0, _, _, [] => by simp [Tele.decode]; rfl
  | 0, _, _, _ :: _ => by simp [Tele.decode]
  | n + 1, _, _, [] => by simp [Tele.decode]
  | n + 1, i, e, f :: fs => by
    simp only [Tele.decode, List.length_cons, Nat.add_right_cancel_iff]
    have hf := dec_isSome_iff (interp M S.isProp X Z (S.code ps c i e)) f
    cases hv : dec _ f with
    | none =>
      simp only [Option.bind_none, Option.isSome_none, Bool.false_eq_true, false_iff]
      rw [hv] at hf
      rintro ⟨_, h⟩
      exact absurd (hf.2 (h 0 (Nat.zero_lt_succ _))) (by simp)
    | some v =>
      rw [Option.bind_some]
      refine (iff_of_eq (congrArg (fun b => b = true) (isSome_map_eq _ _))).trans ?_
      have hm : mask M S.isProp X Z _ v = maskSem (S.code ps c i e) f := by
        rw [mask_eq, enc_of_dec hv]
      rw [hm, Tele.decode_isSome n (i + 1) _ fs]
      rw [hv] at hf
      have h0 := hf.1 rfl
      constructor
      · rintro ⟨hl, h⟩
        refine ⟨hl, fun j hj => ?_⟩
        cases j with
        | zero => exact h0
        | succ j =>
          have := h j (Nat.lt_of_succ_lt_succ hj)
          rw [show i + (j + 1) = i + 1 + j by omega]
          exact this
      · rintro ⟨hl, h⟩
        refine ⟨hl, fun j hj => ?_⟩
        have := h (j + 1) (Nat.succ_lt_succ hj)
        rw [show i + (j + 1) = i + 1 + j by omega] at this
        exact this

end decode

/-! ## One declaration's data model

At parameters `ps` and leaves `Z` (the data model takes `Z = envOf ps`): the tag and fields of a
member are those of its view, packing decodes the fields into a colimit telescope and unviews
it, and a field's type is its code read at the colimit, at the masked earlier fields. -/

section decl
variable (S : Sig) (M : Nat → NModel)

def fixTag {ps : List Sem} {Z : Nat → TyM} : Fix S M ps Z → Nat
  | ⟨c, _⟩ => c.val

def fixFields {ps : List Sem} {Z : Nat → TyM} : Fix S M ps Z → List Sem
  | ⟨_, t⟩ => Tele.fields S M 0 _ [] t

def gTag {ps : List Sem} {Z : Nat → TyM} (x : car S M ps Z) : Nat := fixTag S M (view S M x)

def gFields {ps : List Sem} {Z : Nat → TyM} (x : car S M ps Z) : List Sem :=
  fixFields S M (view S M x)

noncomputable def gPack (ps : List Sem) (Z : Nat → TyM) (c : Nat) (fs : List Sem) :
    Option (car S M ps Z) :=
  if h : c < S.ar.length then
    (Tele.decode S M (X := car S M) (Z := Z) (ps := ps) (c := c) 0 S.ar[c] [] fs).map
      fun t => unview S M ⟨⟨c, h⟩, t⟩
  else none

/-- The type of field `i` of constructor `c` at the meanings `earlier` of the fields before it. -/
def gFieldTy (ps : List Sem) (Z : Nat → TyM) (c i : Nat) (earlier : List Sem) : TyM :=
  small (interp M S.isProp (car S M) Z (S.code ps c i (Sig.maskList S ps c 0 [] earlier)))

theorem gPack_some {ps : List Sem} {Z : Nat → TyM} {c : Nat} {fs : List Sem} {x : car S M ps Z}
    (h : gPack S M ps Z c fs = some x) : ∃ (hc : c < S.ar.length)
      (t : Tele S M (car S M) Z ps c 0 S.ar[c] []),
      Tele.decode S M 0 S.ar[c] [] fs = some t ∧ x = unview S M ⟨⟨c, hc⟩, t⟩ := by
  unfold gPack at h
  split at h
  · rename_i hc
    cases ht : Tele.decode S M (X := car S M) (Z := Z) (ps := ps) (c := c) 0 S.ar[c] [] fs with
    | none => rw [ht] at h; cases h
    | some t =>
      rw [ht] at h
      exact ⟨hc, t, ht, (Option.some.inj h).symm⟩
  · cases h

theorem gTag_pack {ps : List Sem} {Z : Nat → TyM} {c : Nat} {fs : List Sem} (x : car S M ps Z)
    (h : gPack S M ps Z c fs = some x) : gTag S M x = c := by
  obtain ⟨hc, t, _, rfl⟩ := gPack_some S M h
  unfold gTag
  rw [view_unview]
  rfl

theorem gFields_pack {ps : List Sem} {Z : Nat → TyM} {c : Nat} {fs : List Sem} (x : car S M ps Z)
    (h : gPack S M ps Z c fs = some x) : gFields S M x = fs := by
  obtain ⟨hc, t, ht, rfl⟩ := gPack_some S M h
  unfold gFields
  rw [view_unview]
  exact Tele.fields_decode S M _ _ _ fs t ht

theorem gPack_fin {ps : List Sem} {Z : Nat → TyM} (c : Fin S.ar.length) (fs : List Sem) :
    gPack S M ps Z c.val fs =
      (Tele.decode S M (X := car S M) (Z := Z) (ps := ps) (c := c) 0 S.ar[c] [] fs).map
        fun t => unview S M ⟨c, t⟩ := by
  unfold gPack
  rw [dif_pos c.isLt]
  rfl

theorem gPack_fix {ps : List Sem} {Z : Nat → TyM} (w : Fix S M ps Z) :
    gPack S M ps Z (fixTag S M w) (fixFields S M w) = some (unview S M w) := by
  obtain ⟨c, t⟩ := w
  show gPack S M ps Z c.val (Tele.fields S M 0 _ [] t) = _
  rw [gPack_fin, Tele.decode_fields]
  rfl

theorem gPack_fields {ps : List Sem} {Z : Nat → TyM} (x : car S M ps Z) :
    gPack S M ps Z (gTag S M x) (gFields S M x) = some x := by
  unfold gTag gFields
  rw [gPack_fix, unview_view]

theorem gPack_isSome (ps : List Sem) (Z : Nat → TyM) (c : Nat) (fs : List Sem) :
    (gPack S M ps Z c fs).isSome ↔
      ∃ n, S.ar[c]? = some n ∧ fs.length = n ∧
        ∀ i (h : i < fs.length), fs[i] ∈ₛ gFieldTy S M ps Z c i (fs.take i) := by
  unfold gPack
  split
  · rename_i hc
    rw [isSome_map_eq, Tele.decode_isSome, List.getElem?_eq_getElem hc]
    simp only [Option.some.injEq, exists_eq_left', Nat.zero_add, gFieldTy]
  · rename_i hc
    rw [List.getElem?_eq_none (Nat.le_of_not_lt hc)]
    simp

end decl

/-! ## The program: declarations in order

Declaration `i` is modelled at the environment of the models of the declarations before it
(`progEnv`), so a `nest e` code of declaration `i` reads declaration `e < i`'s own model. -/

instance : Inhabited Sig where
  default :=
    { ar := []
      isProp := false
      nestable := fun _ => false
      code := fun _ _ _ _ => .ext .err }

/-- The model of declaration `i` of the program `sigs`. -/
def progModel (sigs : List Sig) (i : Nat) : NModel :=
  nmodel (sigs.getD i default) fun e => if e < i then progModel sigs e else NModel.empty
termination_by i
decreasing_by assumption

/-- The models declaration `i` may nest into. -/
def progEnv (sigs : List Sig) (i : Nat) : Nat → NModel :=
  fun e => if e < i then progModel sigs e else NModel.empty

theorem progModel_eq (sigs : List Sig) (i : Nat) :
    progModel sigs i = nmodel (sigs.getD i default) (progEnv sigs i) := by
  rw [progModel]
  rfl

/-- What a later declaration's `nest i` reads is declaration `i`'s own carrier. -/
theorem progEnv_car (sigs : List Sig) {i j : Nat} (h : i < j) :
    (progEnv sigs j i).car = car (sigs.getD i default) (progEnv sigs i) := by
  simp only [progEnv, h, if_true, progModel_eq]
  rfl

/-! ## The rank: the first stage

A member's rank is the first stage it appears at. A recursive field of a member of rank
`k + 1` is the image of a stage-`k` member, so it has a smaller rank (`crank_self`). -/

theorem exists_min (P : Nat → Prop) (h : ∃ n, P n) : ∃ n, P n ∧ ∀ m, P m → n ≤ m := by
  obtain ⟨n, hn⟩ := h
  induction n using Nat.strongRecOn with
  | _ n ih =>
    by_cases h' : ∃ m, m < n ∧ P m
    · obtain ⟨m, hm, hPm⟩ := h'
      exact ih m hm hPm
    · exact ⟨n, hn, fun m hm => Nat.le_of_not_lt fun hlt => h' ⟨m, hlt, hm⟩⟩

theorem enc_mapB_el0 (b : Bool) {A B : Type} (f : A → B) (v : El (tyB b A)) (y : B)
    (h : enc (tyB b B) (mapB b f v) = .el0 B y) : ∃ a, f a = y := by
  cases b
  · cases h; exact ⟨v, rfl⟩
  · cases h

section rank
variable (S : Sig) (M : Nat → NModel)

/-- The rank of a colimit member: the first stage it comes from. -/
noncomputable def crank {ps : List Sem} {Z : Nat → TyM} (x : car S M ps Z) : Nat :=
  Classical.choose (exists_min (fun k => ∃ y, ι S M k y = x) (let ⟨k, y, h⟩ := ι_surj S M x; ⟨k, y, h⟩))

theorem crank_spec {ps : List Sem} {Z : Nat → TyM} (x : car S M ps Z) :
    ∃ y, ι S M (crank S M x) y = x :=
  (Classical.choose_spec (exists_min (fun k => ∃ y, ι S M k y = x)
    (let ⟨k, y, h⟩ := ι_surj S M x; ⟨k, y, h⟩))).1

theorem crank_le {ps : List Sem} {Z : Nat → TyM} (x : car S M ps Z) (k : Nat)
    (y : stage S M k ps Z) (h : ι S M k y = x) : crank S M x ≤ k :=
  (Classical.choose_spec (exists_min (fun k => ∃ y, ι S M k y = x)
    (let ⟨k, y, h⟩ := ι_surj S M x; ⟨k, y, h⟩))).2 k ⟨y, h⟩

/-- The leaf environment of a recursive occurrence `self fx tys`, at the leaves `Z`. -/
abbrev occEnv (Z : Nat → TyM) (tys : Nat → PCode) : Nat → TyM :=
  fun j => interp M S.isProp X₀ Z (tys j)

theorem Step.fields_self_head (k : Nat) {Z : Nat → TyM} {K K' : Sem → Type} (g : ∀ s, K s → K' s)
    (rest : ∀ s, K' s → List Sem) (τ : PCode) (fx : List Sem) (tys : Nat → PCode)
    (hτ : τ = .self fx tys) (st₀ : Step S M (stage S M k) Z τ K) (y : car S M fx (occEnv S M Z tys))
    (h : (Step.fields S M rest τ (Step.mapX S M (X := stage S M k) (Y := car S M)
      (fun y => ι S M k y) g τ st₀))[0]? = some (.el0 _ y)) :
    ∃ y₀, ι S M k y₀ = y := by
  subst hτ
  obtain ⟨v₀, t⟩ := st₀
  simp only [Step.mapX, Step.fields, List.getElem?_cons_zero, Option.some.injEq] at h
  exact enc_mapB_el0 S.isProp _ v₀ y h

/-- A recursive field of a stage-`k` telescope read at the colimit is the image of a stage-`k`
member. -/
theorem Tele.fields_self (k : Nat) {Z : Nat → TyM} {ps : List Sem} {c : Nat} :
    ∀ (n i : Nat) (e : List Sem) (t₀ : Tele S M (stage S M k) Z ps c i n e) (j : Nat)
      (fx : List Sem) (tys : Nat → PCode) (y : car S M fx (occEnv S M Z tys)),
      S.code ps c (i + j) (Sig.maskList S ps c i e
        ((Tele.fields S M i n e (teleι S M k t₀)).take j)) = .self fx tys →
      (Tele.fields S M i n e (teleι S M k t₀))[j]? = some (.el0 _ y) →
      ∃ y₀, ι S M k y₀ = y
  | 0, _, _, _, _, _, _, _, _, h => by simp [Tele.fields] at h
  | n + 1, i, e, t₀, j, fx, tys, y, h₁, h₂ => by
    have key : ∀ (τ : PCode) (hτ : S.code ps c i e = τ)
        (st₀ : Step S M (stage S M k) Z τ fun s => Tele S M (stage S M k) Z ps c (i + 1) n (e ++ [s])),
        S.code ps c (i + j) (Sig.maskList S ps c i e ((Step.fields S M
          (fun s => Tele.fields S M (i + 1) n (e ++ [s])) τ (Step.mapX S M (X := stage S M k)
            (Y := car S M) (fun y => ι S M k y) (fun _ t => teleι S M k t) τ st₀)).take j)) =
          .self fx tys →
        (Step.fields S M (fun s => Tele.fields S M (i + 1) n (e ++ [s])) τ (Step.mapX S M
          (X := stage S M k) (Y := car S M) (fun y => ι S M k y) (fun _ t => teleι S M k t) τ
            st₀))[j]? = some (.el0 _ y) →
        ∃ y₀, ι S M k y₀ = y := by
      intro τ hτ st₀ h₁ h₂
      cases j with
      | zero => exact Step.fields_self_head S M k _ _ τ fx tys (hτ.symm.trans h₁) st₀ y h₂
      | succ j =>
        obtain ⟨v₀, t'⟩ := st₀
        rw [show i + (j + 1) = i + 1 + j by omega] at h₁
        cases τ <;>
          simp only [Step.mapX, Step.fields, List.take_succ_cons, List.getElem?_cons_succ,
            Sig.maskList, hτ, maskSem, mask] at h₁ h₂ <;>
          exact Tele.fields_self k n (i + 1) _ t' j fx tys y h₁ h₂
    exact key _ rfl t₀ h₁ h₂

/-- **The rank law, on the core carrier.** A field whose code is a recursive occurrence
`self fx tys`, read at that occurrence, has a smaller rank. -/
theorem crank_self {ps : List Sem} {Z : Nat → TyM} (x : car S M ps Z) (i : Nat)
    (fx : List Sem) (tys : Nat → PCode) (y : car S M fx (occEnv S M Z tys))
    (hcode : S.code ps (gTag S M x) i (Sig.maskList S ps (gTag S M x) 0 [] ((gFields S M x).take i)) =
      .self fx tys)
    (hy : (gFields S M x)[i]? = some (.el0 _ y)) : crank S M y < crank S M x := by
  obtain ⟨y₀, hx⟩ := crank_spec S M x
  revert y₀ hx
  generalize crank S M x = r
  intro y₀ hx
  subst hx
  obtain _ | k := r
  · exact y₀.elim
  obtain ⟨c, t₀⟩ := y₀
  simp only [gTag, gFields, view_ι, fixTag, fixFields] at hcode hy
  obtain ⟨y₁, rfl⟩ := Tele.fields_self S M k S.ar[c] 0 [] t₀ i fx tys y
    (by rw [Nat.zero_add]; exact hcode) hy
  exact Nat.lt_succ_of_le (crank_le S M _ k y₁ rfl)

end rank

/-! ## The data model

A declaration's data model at parameters `ps` is the core construction at the blanked
parameters and the parameters' leaf environment, `car (blank ps) (envOf ps)`. A recursive
field's parameters (`recArgs`) are the occurrence's fixed parameters with its type codes at the
nestable positions (`occParams`), returned when the interface carrier there is the core
carrier the field lives in; `gRecArgs_wf` says it is whenever the code is well formed, which
the assembly shows from the checker's [Ind-decl]. -/

/-- An occurrence's parameters: its fixed parameters, its leaf types at the nestable
positions. -/
def occFrom (nb : Nat → Bool) (Zo : Nat → TyM) : Nat → List Sem → List Sem
  | _, [] => []
  | j, s :: ss => (if nb j then .ty (Zo j) else s) :: occFrom nb Zo (j + 1) ss

section model
variable (S : Sig) (M : Nat → NModel)

noncomputable def gRecArgs (ps : List Sem) (c i : Nat) (earlier : List Sem) : Option (List Sem) :=
  match S.code (S.blank ps) c i (Sig.maskList S (S.blank ps) c 0 [] earlier) with
  | .self fx tys =>
    open Classical in
    if S.blank (occFrom S.nestable (occEnv S M (envOf ps) tys) 0 fx) = fx ∧
        envOf (occFrom S.nestable (occEnv S M (envOf ps) tys) 0 fx) = occEnv S M (envOf ps) tys then
      some (occFrom S.nestable (occEnv S M (envOf ps) tys) 0 fx)
    else none
  | _ => none

theorem crank_self' {ps : List Sem} {Z : Nat → TyM} (x : car S M ps Z) (i : Nat)
    (fx : List Sem) (tys : Nat → PCode)
    (hcode : S.code ps (gTag S M x) i (Sig.maskList S ps (gTag S M x) 0 [] ((gFields S M x).take i)) =
      .self fx tys)
    (bps : List Sem) (Z' : Nat → TyM) (hb : bps = fx) (hz : Z' = occEnv S M Z tys)
    (y : car S M bps Z') (hy : (gFields S M x)[i]? = some (.el0 (car S M bps Z') y)) :
    crank S M y < crank S M x := by
  subst hb hz
  exact crank_self S M x i _ tys y hcode hy

/-- The interface's rank law for one declaration. -/
theorem gRank_lt {ps ps' : List Sem} (x : car S M (S.blank ps) (envOf ps))
    (y : car S M (S.blank ps') (envOf ps')) (i : Nat)
    (h : gRecArgs S M ps (gTag S M x) i ((gFields S M x).take i) = some ps')
    (hy : (gFields S M x)[i]? = some (.el0 (car S M (S.blank ps') (envOf ps')) y)) :
    crank S M y < crank S M x := by
  unfold gRecArgs at h
  split at h
  · rename_i fx tys hcode
    split at h
    · rename_i hg
      obtain rfl := Option.some.inj h
      exact crank_self' S M x i fx tys hcode _ _ hg.1 hg.2 y hy
    · cases h
  · cases h

end model

theorem blankFrom_occFrom (nb : Nat → Bool) (Zo : Nat → TyM) :
    ∀ (j : Nat) (fx : List Sem), blankFrom nb j (occFrom nb Zo j fx) = blankFrom nb j fx
  | _, [] => rfl
  | j, s :: ss => by
    simp only [occFrom, blankFrom, blankFrom_occFrom nb Zo (j + 1) ss]
    cases nb j <;> rfl

theorem getD_occFrom (nb : Nat → Bool) (Zo : Nat → TyM) :
    ∀ (j : Nat) (fx : List Sem) (m : Nat), (occFrom nb Zo j fx).getD m .err =
      if h : m < fx.length then (if nb (j + m) then .ty (Zo (j + m)) else fx[m]) else .err
  | _, [], _ => rfl
  | j, s :: ss, 0 => by simp [occFrom]
  | j, s :: ss, m + 1 => by
    simp only [occFrom, List.getD_cons_succ, getD_occFrom nb Zo (j + 1) ss m, List.length_cons,
      Nat.add_lt_add_iff_right, List.getElem_cons_succ]
    rw [show j + 1 + m = j + (m + 1) by omega]

/-- **Bridge.** For a well-formed recursive occurrence (its fixed parameters blank at the
nestable positions, its type codes at the other positions those parameters' types), `recArgs`
is the occurrence's parameters, so the interface's rank law speaks of every recursive field. -/
theorem gRecArgs_wf (S : Sig) (M : Nat → NModel) (ps : List Sem) (c i : Nat) (earlier : List Sem)
    (fx : List Sem) (tys : Nat → PCode)
    (hcode : S.code (S.blank ps) c i (Sig.maskList S (S.blank ps) c 0 [] earlier) = .self fx tys)
    (hb : S.blank fx = fx)
    (hz : ∀ j, (S.nestable j = false ∨ fx.length ≤ j) →
      occEnv S M (envOf ps) tys j = tyOf (fx.getD j .err)) :
    gRecArgs S M ps c i earlier = some (occFrom S.nestable (occEnv S M (envOf ps) tys) 0 fx) := by
  have h₁ : S.blank (occFrom S.nestable (occEnv S M (envOf ps) tys) 0 fx) = fx := by
    rw [Sig.blank, blankFrom_occFrom]
    exact hb
  have h₂ : envOf (occFrom S.nestable (occEnv S M (envOf ps) tys) 0 fx) = occEnv S M (envOf ps) tys := by
    funext j
    simp only [envOf, getD_occFrom, Nat.zero_add]
    split
    · rename_i hj
      cases hn : S.nestable j
      · simp only [Bool.false_eq_true, if_false]
        rw [hz j (.inl hn), ← List.getElem_eq_getD]
      · rfl
    · rename_i hj
      rw [hz j (.inr (Nat.le_of_not_lt hj)), List.getD_eq_getElem?_getD,
        List.getElem?_eq_none (Nat.le_of_not_lt hj)]
      rfl
  unfold gRecArgs
  rw [hcode]
  exact if_pos ⟨h₁, h₂⟩

/-- One declaration's data model at every parameter tuple, with the laws of `DataModel`. -/
structure DM where
  car : List Sem → Type
  ar : List Nat
  fieldTy : List Sem → Nat → Nat → List Sem → TyM
  paramTy : Nat → List Sem → TyM
  fieldData : List Sem → Nat → Nat → List Sem → Option (String × List Sem)
  paramData : Nat → List Sem → Option (String × List Sem)
  recArgs : List Sem → Nat → Nat → List Sem → Option (List Sem)
  pack : (ps : List Sem) → Nat → List Sem → Option (car ps)
  tag : {ps : List Sem} → car ps → Nat
  fields : {ps : List Sem} → car ps → List Sem
  rank : {ps : List Sem} → car ps → Nat
  tag_pack : ∀ {ps c fs} (x : car ps), pack ps c fs = some x → tag x = c
  fields_pack : ∀ {ps c fs} (x : car ps), pack ps c fs = some x → fields x = fs
  pack_fields : ∀ {ps} (x : car ps), pack ps (tag x) (fields x) = some x
  pack_isSome : ∀ ps c fs, (pack ps c fs).isSome ↔
    ∃ n, ar[c]? = some n ∧ fs.length = n ∧ ∀ i (h : i < fs.length), fs[i] ∈ₛ fieldTy ps c i (fs.take i)
  rank_lt : ∀ {ps ps'} (x : car ps) (y : car ps') i, recArgs ps (tag x) i ((fields x).take i) = some ps' →
    (fields x)[i]? = some (.el0 (car ps') y) → rank y < rank x

/-- A declaration's data model: the core construction at the blanked parameters and their leaf
environment. -/
noncomputable def declDM (S : Sig) (M : Nat → NModel) : DM where
  car ps := car S M (S.blank ps) (envOf ps)
  ar := S.ar
  fieldTy ps := gFieldTy S M (S.blank ps) (envOf ps)
  paramTy := S.paramTy
  fieldData := S.fieldData
  paramData := S.paramData
  recArgs := gRecArgs S M
  pack ps := gPack S M (S.blank ps) (envOf ps)
  tag := gTag S M
  fields := gFields S M
  rank := crank S M
  tag_pack x h := gTag_pack S M x h
  fields_pack x h := gFields_pack S M x h
  pack_fields x := gPack_fields S M x
  pack_isSome ps := gPack_isSome S M (S.blank ps) (envOf ps)
  rank_lt x y i h hy := gRank_lt S M x y i h hy

/-- The model of an undeclared name. -/
def DM.empty : DM where
  car _ := PEmpty
  ar := []
  fieldTy _ _ _ _ := .err
  paramTy _ _ := .err
  fieldData _ _ _ _ := none
  paramData _ _ := none
  recArgs _ _ _ _ := none
  pack _ _ _ := none
  tag x := x.elim
  fields x := x.elim
  rank x := x.elim
  tag_pack x _ := x.elim
  fields_pack x _ := x.elim
  pack_fields x := x.elim
  pack_isSome _ _ _ := by simp
  rank_lt x _ _ _ _ := x.elim

/-- The program's declarations with their signatures, in order. -/
abbrev Prog := List (IndDecl × Sig)

/-- The index of a declaration in the program, by name. -/
def Prog.index (Γ : Prog) (d : IndDecl) : Option Nat := Γ.findIdx? fun p => p.1.name == d.name

/-- The data model of a declaration: its signature's, at the models of the declarations
before it. -/
noncomputable def Prog.dm (Γ : Prog) (d : IndDecl) : DM :=
  match Γ.index d with
  | some i => declDM ((Γ.map (·.2)).getD i default) (progEnv (Γ.map (·.2)) i)
  | none => DM.empty

/-- **The generic data model** of a program: every declaration by stages, in order. It covers a
declaration that is the program's declaration of its name, with the signature's arities and
sort. -/
noncomputable def genericModel (Γ : Prog) : DataModel where
  covers d := ∃ i, Γ.index d = some i ∧ (Γ[i]?).map (·.1) = some d ∧
    arities d = ((Γ.map (fun p : IndDecl × Sig => p.2)).getD i default).ar ∧
    (d.sort == 0) = ((Γ.map (fun p : IndDecl × Sig => p.2)).getD i default).isProp
  car d := (Γ.dm d).car
  fieldTy d := (Γ.dm d).fieldTy
  paramTy d := (Γ.dm d).paramTy
  fieldData d := (Γ.dm d).fieldData
  paramData d := (Γ.dm d).paramData
  recArgs d := (Γ.dm d).recArgs
  pack d := (Γ.dm d).pack
  tag := (Γ.dm _).tag
  fields := (Γ.dm _).fields
  rank := (Γ.dm _).rank
  tag_pack x _ h := (Γ.dm _).tag_pack x h
  fields_pack x _ h := (Γ.dm _).fields_pack x h
  pack_fields x _ := (Γ.dm _).pack_fields x
  pack_isSome {d ps c fs} hd := by
    obtain ⟨i, hi, _, har, _⟩ := hd
    rw [ctor_iff_arity d c (fun n => fs.length = n ∧ _), (Γ.dm d).pack_isSome]
    have : (Γ.dm d).ar = arities d := by simp only [Prog.dm, hi, har]; rfl
    rw [this]
  rank_lt x y _ i h hy := (Γ.dm _).rank_lt x y i h hy

/-! ## The assembly's obligation: codes are the run's reading of the field types

`FieldsFaithful dm d readTy readData` is what the assembly owes for a covered declaration `d`:
`readTy ps c i earlier` and `readData ps c i earlier` are the reference run's reading of field
`i`'s declared type term (its `TyS`'s `m` and `data`) at the parameters' and earlier fields'
meanings. Then `Value.meanFields` reads every field at the type and hint the run gives it.

Status (data-generic, 2026-11-10), by kind of field code:
* `ext T` (closed types, including type-function fields like `Cells`' `G(n, x)`): the run's
  reading is a function of the parameters' and earlier closed fields' meanings, so the type
  part holds when the assembly takes `T` to be that reading, and the data part holds with
  `Sig.fieldData` equal to the run's data (a function of the same meanings).
* `self` / `nest` (an inductive written at arguments, `Cell (R) := MkC(h : Nat, t : SliceOf(R))`):
  the data is the declaration's name and the arguments' meanings, a function of `ps`. It
  holds under the well-formedness of `gRecArgs_wf`.
* **`par j` (a field whose declared type is a parameter, `Pair`'s `fst : A`, `Box(A) :=
  MkBox(x : A)`): the type part holds (`libModel_fieldTy_pair`), the data part is
  unprovable.** At `A := List(Nat)` the run's hint for `x` carries `("List", [⟦Nat⟧])`, read
  off the *parameter's* structured type. But `fieldData d ps` sees only
  `ps = [ty (ty0 (car List [⟦Nat⟧]))]`, and recovering a declaration and parameters from a
  carrier is D8's problem: no choice is provably the run's. With two declarations of equal
  carrier the obligation fails outright, and Lean can neither prove nor refute such equalities.
  So `MkBox(Nil)` (or `(Nil, 0)` at `List(Nat) × Nat`), with `Nil` recording no parameters
  (an untyped run), means `err` in the field under any data model with a pass-through
  `fieldData`, and a well-typed value means junk. Fix (for the lead): parameters must carry
  their structured hint too. Either `TyS.data : Option (String × List TyS)`, so a parameter's
  own data travels, with `fieldData` at a `par j` field returning parameter `j`'s; or D8's
  option (c) (the checker records inferred parameters), which removes `ps = []` values.
-/

/-- The assembly's obligation for one covered declaration (see the section docstring). -/
def FieldsFaithful (dm : DataModel) (d : IndDecl)
    (readTy : List Sem → Nat → Nat → List Sem → TyM)
    (readData : List Sem → Nat → Nat → List Sem → Option (String × List Sem)) : Prop :=
  ∀ ps c i earlier, dm.fieldTy d ps c i earlier = small (readTy ps c i earlier) ∧
    dm.fieldData d ps c i earlier = readData ps c i earlier

/-- The library's type part: `Pair`'s fields have the parameters' types (cut to `small`), as
the run reads the field type terms `A` and `B`. -/
theorem libModel_fieldTy_pair (d : IndDecl) (h : DataModel.libKind d = .pair) (A B : TyM)
    (c i : Nat) (e : List Sem) :
    DataModel.libModel.fieldTy d [.ty A, .ty B] c i e = small (if i = 0 then A else B) := by
  show (DataModel.libKind d).fieldTy _ i = _
  rw [h]
  by_cases hi : i = 0 <;> simp [DataModel.LibKind.fieldTy, DataModel.libPar, hi, List.getD]

/-! ## Nested recursion (`Rose → List → Rose`): the statement the semantic [Rec] needs

`rank_lt` covers direct recursive fields only. For [Rec]'s path through a nested field
(`x : Rose(A)`, `x.kids : List(Rose(A))`, `h` a member of `kids`), the statement that holds by
construction is: **every leaf of a nested field of `x` at a position whose type code is a
recursive occurrence has a smaller rank than `x`**. In `NModel` terms, for a field `v` with code
`nest e fx tys` at the view of `x`, `(M e).allL (fun j l => tys j = .self … → crank l < crank x) v`.
It holds because `x` of first stage `k + 1` has its nested fields at `E`'s carrier over stage `k`
(`view_ι`), whose leaves are `ι k` of stage-`k` members (`crank_le`). The proof needs one more
`NModel` law, `allL_map : (∀ j a, P j a → Q j (f j a)) → allL P x → allL Q (map f x)`, which
holds for `nmodel` (by `sallL` along `smap`) but is not yet in the interface. On the
interface side the guard must then read ranks along the declared path: `List`'s `fields` at
`Rose`'s carrier give `Rose` members whose rank the statement bounds, so a semantic [Rec]
stated with "reachable through nested fields at declared types" is provable from it. Not
written here (out of time, 2026-11-10).
-/

end DataGeneric
end Ochr.Meaning
