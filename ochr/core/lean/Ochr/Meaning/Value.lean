import Ochr.Meaning.Data
import Ochr.Meaning.Future
import Ochr.Meaning.Pi

/-!
# The meaning of a value, `⟦v⟧_{ρ,φ}` (docs/18 Def. "meaning of a state", docs/27 Def. 2)

Under an assignment `ρ` of the abstract values and a future `φ` of the live borrows:
* `σ` means `ρ σ`; `⋆` means `•`; `⊥` means `moved`; `Z`, `S v`, `()` mean the numbers and the
  unit as elements of `Nat` and `Unit`;
* a constructor value means the tree recording its type's record (`DataModel.ctorR`; docs/34),
  whatever its fields hold;
* a type value means `ty T`: `Nat`, `Unit`, `sort l`, `D(ā)` by the data model, `Eq(A, a, b)` the
  proposition `⟦a⟧ = ⟦b⟧`, `&A` the content type `⟦A⟧` (a borrow is read as what it holds, so a
  borrow-typed place means its content). Strict (below): `Eq(A, a, b)` and `D(ā)` mean `ty err`
  unless their parts are typed (`EqOk`, `paramsOk`);
* `borrow_ℓ w` means `⟦w⟧`, its *current* content; `loan_ℓ` means `φ ℓ`, the *final* content
  of the borrow that took it (docs/27 §3);
* a global, a closure, a Π-closure and a sealed program mean what running code means, through
  `CodeMeaning`, which the reference run supplies (milestone 2).

## The type hint (docs/31 D8, revised)

A constructor value of a parameterised type may record no parameters (`ps = []`): an untyped
run (a sealed program's re-normalisation, a callee's body) records only the parameters written
in the source, and the checker reads such a value's type from its position (D49 (4),
`Machine.indValType?`). The typed model needs the parameters' meanings, so the meaning of a
value is read *at a type*, the `hint : TyS`, whose `data` component names the declaration and
its record (read off its code): the position's stored type, a field's type at the earlier fields
(`DataModel.fieldTy`), a parameter's type, an equation's type. Only a constructor value with
`ps = []` reads the hint, taking the record straight off `hint.data`; everything else ignores it. So
docs/18's V2 holds in this sense: what a constructor value means is determined by its type,
whether or not it records its parameters. `TyS.plain TyM.err` is "no hint".

The definition is total; an ill-formed value means `err`.
-/

namespace Ochr.Meaning

/-- What the meaning of a value needs from the meaning of code. The reference run (`Run.lean`)
defines these together with `Value.mean` in one recursion; here they are a parameter, so that
the first-order meaning is fixed and checkable on its own. -/
structure CodeMeaning where
  /-- The meaning of the global `gfn n` (a function) or of a constant, from the program so far,
  with its type as the run knows it (a function's Π-shape). -/
  global : String → Sem × TyS
  /-- The meaning of the sealed program `⌈t⌉` read at the type `hint`: `t` run from the empty
  state, its abstract values read from `ρ` and its loans (holes, inert loans) from `φ`. -/
  sealed : Assignment → Future → TyS → Term → Sem
  /-- The meaning of the closure `clo caps t rd`: a function on its annotated domain, read off the
  reference run of its body with the captures bound at their recorded types; a recursive closure
  by guarded recursion on the rank of its decreasing argument (docs/24 §4). -/
  clo : Assignment → Future → List Value → Term → List (DeclInfo × Value) → Sem
  /-- The meaning of the Π-closure `tPi caps t rd`: the dependent product of its parameter types
  and codomain, evaluated at every argument (`Pi.lean`). -/
  pi : Assignment → Future → List Value → Term → List (DeclInfo × Value) → TyM
  /-- The meaning of a deferred type (D82 `Binding.lazyTy`): parameter `i` of the Π-type `P` at
  the arguments `ws` as passed, or `P`'s codomain there for `i` the number of parameters. -/
  paramTy : Assignment → Value → List Value → Nat → TyS

/-- Read a meaning as an element of the Lean type `A` (classically, by the tag). -/
noncomputable def Sem.as (A : Type) : Sem → Option A
  | .el0 B b => open Classical in if h : B = A then some (h ▸ b) else none
  | _ => none

/-- Read a meaning as a number. -/
noncomputable def Sem.asNat (s : Sem) : Option Nat := s.as Nat

/-- `S` on meanings: the successor of a number, the partly moved tuple `S(⊥…)` of a
non-whole argument (D84), `err` otherwise. -/
noncomputable def Sem.succ (s : Sem) : Sem :=
  match s.asNat with
  | some n => .el0 Nat (n + 1)
  | none => open Classical in if s.whole then .err else .dat "Nat" natRec 1 [s]

/-! ## Strict type formers ("well typed inside", the orchestrator's decision of 2026-11-21)

The checker's comparison of values is untyped, and membership of a type value in a universe says
nothing about the values inside it (`Eq(A, a, b)` is a proposition whatever `a` and `b` are). So
the type formers mean `err` (and their clauses of the reference run fail) unless their parts are
typed: then "has a meaning" implies "well typed inside" (`Strict/Typed.lean`), and no typing
predicate is carried as an invariant. -/

/-- A side of an equation (`Eq`, `Id`): `moved` (D84: a side may be `⊥`) or a member of the
equation's type (whole, at the model's reading: `DataModel.read_wholeFields`; a partly moved member
is too weak, D84's sides are `⊥` or whole). -/
def SideOk (R : DataRead) (T : TyM) (v : Sem) : Prop := v = .moved ∨ v ∈ₛ[R] T

/-- An equation's type `TA` (the meaning of its type term) is a type with a level, and both sides
are `SideOk` at it. A level, not membership in a universe (the orchestrator, 2026-11-21, on the
trial's advice): the bounded model has no universe holding a level-3 type, and `Eq(Type₁, X, Y)`
would otherwise be excluded. -/
def EqOk (R : DataRead) (TA : Sem) (a b : Sem) : Prop :=
  TA.asTy.level.isSome = true ∧ SideOk R TA.asTy a ∧ SideOk R TA.asTy b

/-- Parameters are members of their declared types at the earlier ones (an inductive type
applied to arguments; written constructor parameters). -/
def paramsOk (dm : DataModel) (d : IndDecl) (ps : List Sem) : Prop :=
  ∀ i v, ps[i]? = some v → v ∈ₛ[dm.read] dm.paramTy d i (ps.take i)

@[simp] theorem paramsOk_nil (dm : DataModel) (d : IndDecl) : paramsOk dm d [] := by
  intro i v h; simp at h

section
variable (dm : DataModel) (C : CodeMeaning) (Γ : List IndDecl)

mutual
/-- The meaning of a value under `ρ` and `φ`, read at the type `hint`, with the declarations
`Γ` (`MState.inds`). -/
noncomputable def Value.mean (ρ : Assignment) (φ : Future) (hint : TyS) : Value → Sem
  | .zero => .el0 Nat 0
  | .succ v => (Value.mean ρ φ (.plain TyM.nat) v).succ
  | .unit => .el0 Unit ()
  | .gfn n => (C.global n).1
  | .clo caps t rd => C.clo ρ φ caps t rd
  | .borrow _ w => Value.mean ρ φ hint w
  -- `lent_k w` (static ends, D90): the mark has no meaning of its own (docs/31 D29)
  | .gloan _ w => Value.mean ρ φ hint w
  | .loan l => φ l
  | .bot => .moved
  | .abs σ => ρ σ
  | .sealed t => C.sealed ρ φ hint t
  | .proof => .proof
  | .tNat => .ty TyM.nat
  | .tUnit => .ty TyM.unit
  -- STRICT: `err` unless the type has a level and the sides are `⊥` or members of it (`EqOk`)
  | .tEq A a b =>
    let T := TyS.plain (Value.mean ρ φ (.plain TyM.err) A).asTy
    open Classical in
    if EqOk dm.read (Value.mean ρ φ (.plain TyM.err) A) (Value.mean ρ φ T a) (Value.mean ρ φ T b) then
      .ty (TyM.prop (Value.mean ρ φ T a = Value.mean ρ φ T b))
    else .ty TyM.err
  | .tRef A => Value.mean ρ φ (.plain TyM.err) A
  | .tPi caps t rd => .ty (C.pi ρ φ caps t rd)
  | .sort l => .ty (TyM.univ l)
  | .ind ty c _ ps fs =>
    match Γ.find? (·.name == ty) with
    | some d =>
      let r? : Option Rec := if ps.isEmpty && !d.params.isEmpty then
          (match hint.data with | some (n, r) => if n = ty then some r else none | none => none)
        else some (dm.recOf d (Value.meanParams ρ φ d 0 [] ps))
      match r? with
      | some r => if d.sort == 0 then .proof else DataModel.ctorR d r c (Value.meanFields ρ φ d r c 0 [] fs)
      | none => .err
    | none => .err
  -- STRICT: `err` unless each argument is a member of its parameter type (`paramsOk`)
  | .tInd n args =>
    match Γ.find? (·.name == n) with
    | some d =>
      open Classical in
      if paramsOk dm d (Value.meanParams ρ φ d 0 [] args) then .ty (dm.tyM d (Value.meanParams ρ φ d 0 [] args))
      else .ty TyM.err
    | none => .ty TyM.err
termination_by structural v => v

/-- The meanings of a constructor's fields, each read at its field type at the record and the
earlier ones. -/
noncomputable def Value.meanFields (ρ : Assignment) (φ : Future) (d : IndDecl) (r : Rec) (c i : Nat)
    (earlier : List Sem) : List Value → List Sem
  | [] => []
  | v :: vs =>
    let s := Value.mean ρ φ (.plain (dm.fieldTyR d r c i earlier)) v
    s :: Value.meanFields ρ φ d r c (i + 1) (earlier ++ [s]) vs
termination_by structural vs => vs

/-- The meanings of an inductive's parameters, each read at its parameter type. -/
noncomputable def Value.meanParams (ρ : Assignment) (φ : Future) (d : IndDecl) (i : Nat)
    (earlier : List Sem) : List Value → List Sem
  | [] => []
  | v :: vs =>
    let s := Value.mean ρ φ ⟨dm.paramTy d i earlier, none⟩ v
    s :: Value.meanParams ρ φ d (i + 1) (earlier ++ [s]) vs
termination_by structural vs => vs
end

/-- The meaning of a type value, as a type. -/
noncomputable def Value.tyM (ρ : Assignment) (φ : Future) (T : Value) : TyM :=
  (Value.mean dm C Γ ρ φ (.plain TyM.err) T).asTy

end


/-- A constructor value of a parameterised declaration with no parameters recorded (D88/D89:
the checker never builds one; its meaning would read the hint's data). -/
def _root_.Ochr.Value.bareCtor (Γ : List IndDecl) : Value → Bool
  | .ind ty _ _ [] _ => match Γ.find? (·.name == ty) with | some d => !d.params.isEmpty | none => false
  | _ => false

/-- A sealed program (its meaning is its run at the hint: hint-dependent by design, D89). -/
def _root_.Ochr.Value.isSealed : Value → Bool
  | .sealed _ => true
  | _ => false

/-- The loans a value's MEANING reads: `loan_l` anywhere inside it, sealed programs, closures and
recorded types included. Main's `Value.hasLoan` also counts a mark `lent_l` (static ends, D90),
which [Access] reads and a meaning does not (docs/31 D29: the mark has no meaning of its own), so
the congruence lemmas are stated with this one. -/
def _root_.Ochr.Value.hasLoanM (l : Nat) (v : Value) : Bool := v.anyAtom (· == .loan l)

mutual
theorem _root_.Ochr.Value.anyAtom_mono {P Q : Value → Bool} (h : ∀ a, P a = true → Q a = true) :
    ∀ (v : Value), v.anyAtom P = true → v.anyAtom Q = true
  | v, hv => by
    cases v with
    | succ w | tRef w | borrow _ w | gloan _ w | sealed w | tInd _ w =>
      simp only [Value.anyAtom, Bool.or_eq_true_iff] at hv ⊢
      rcases hv with hv | hv
      · exact .inl (h _ hv)
      · first
          | exact .inr (Value.anyAtom_mono h _ hv)
          | exact .inr (Term.anyAtom_mono h _ hv)
          | exact .inr (Value.anyAtomList_mono h _ hv)
    | tEq A a b =>
      simp only [Value.anyAtom, Bool.or_eq_true_iff] at hv ⊢
      rcases hv with hv | (hv | hv) | hv
      · exact .inl (h _ hv)
      · exact .inr (.inl (.inl (Value.anyAtom_mono h _ hv)))
      · exact .inr (.inl (.inr (Value.anyAtom_mono h _ hv)))
      · exact .inr (.inr (Value.anyAtom_mono h _ hv))
    | clo cs t rd | tPi cs t rd =>
      simp only [Value.anyAtom, Bool.or_eq_true_iff] at hv ⊢
      rcases hv with hv | (hv | hv) | hv
      · exact .inl (h _ hv)
      · exact .inr (.inl (.inl (Value.anyAtomList_mono h _ hv)))
      · exact .inr (.inl (.inr (Term.anyAtom_mono h _ hv)))
      · exact .inr (.inr (Value.anyAtomRd_mono h _ hv))
    | ind _ _ _ ps fs =>
      simp only [Value.anyAtom, Bool.or_eq_true_iff] at hv ⊢
      rcases hv with hv | hv | hv
      · exact .inl (h _ hv)
      · exact .inr (.inl (Value.anyAtomList_mono h _ hv))
      · exact .inr (.inr (Value.anyAtomList_mono h _ hv))
    | zero | unit | gfn _ | loan _ | bot | abs _ | proof | tNat | tUnit | sort _ =>
      simp only [Value.anyAtom, Bool.or_eq_true_iff, Bool.or_false] at hv ⊢
      first | exact h _ hv | exact .inl (h _ hv)

theorem _root_.Ochr.Value.anyAtomList_mono {P Q : Value → Bool} (h : ∀ a, P a = true → Q a = true) :
    ∀ (vs : List Value), Value.anyAtomList P vs = true → Value.anyAtomList Q vs = true
  | [], hv => by simp [Value.anyAtomList] at hv
  | v :: vs, hv => by
    simp only [Value.anyAtomList, Bool.or_eq_true_iff] at hv ⊢
    rcases hv with hv | hv
    · exact .inl (Value.anyAtom_mono h v hv)
    · exact .inr (Value.anyAtomList_mono h vs hv)

theorem _root_.Ochr.Value.anyAtomRd_mono {P Q : Value → Bool} (h : ∀ a, P a = true → Q a = true) :
    ∀ (rd : List (DeclInfo × Value)), Value.anyAtomRd P rd = true → Value.anyAtomRd Q rd = true
  | [], hv => by simp [Value.anyAtomRd] at hv
  | (_, v) :: rd, hv => by
    simp only [Value.anyAtomRd, Bool.or_eq_true_iff] at hv ⊢
    rcases hv with hv | hv
    · exact .inl (Value.anyAtom_mono h v hv)
    · exact .inr (Value.anyAtomRd_mono h rd hv)

theorem _root_.Ochr.Term.anyAtom_mono {P Q : Value → Bool} (h : ∀ a, P a = true → Q a = true) :
    ∀ (t : Term), t.anyAtom P = true → t.anyAtom Q = true
  | t, ht => by
    cases t <;> simp only [Term.anyAtom, Bool.or_eq_true_iff] at ht ⊢ <;> (try exact absurd ht Bool.false_ne_true)
    all_goals first
      | exact Value.anyAtom_mono h _ ht
      | exact Term.anyAtom_mono h _ ht
      | exact Term.anyAtomList_mono h _ ht
      | exact Term.anyAtomArms_mono h _ ht
      | (rcases ht with ht | ht
         · exact .inl (Term.anyAtom_mono h _ ht)
         · exact .inr (Term.anyAtom_mono h _ ht))
      | (rcases ht with ht | ht
         · exact .inl (Term.anyAtomList_mono h _ ht)
         · exact .inr (Term.anyAtom_mono h _ ht))
      | (rcases ht with ht | ht
         · exact .inl (Term.anyAtom_mono h _ ht)
         · exact .inr (Term.anyAtomList_mono h _ ht))
      | (rcases ht with ht | ht
         · exact .inl (Term.anyAtomList_mono h _ ht)
         · exact .inr (Term.anyAtomList_mono h _ ht))
      | (rcases ht with (ht | ht) | ht
         · exact .inl (.inl (Term.anyAtom_mono h _ ht))
         · exact .inl (.inr (Term.anyAtom_mono h _ ht))
         · exact .inr (Term.anyAtom_mono h _ ht))
      | (rcases ht with (ht | ht) | ht
         · exact .inl (.inl (Term.anyAtomList_mono h _ ht))
         · exact .inl (.inr (Term.anyAtom_mono h _ ht))
         · exact .inr (Term.anyAtom_mono h _ ht))

theorem _root_.Ochr.Term.anyAtomList_mono {P Q : Value → Bool} (h : ∀ a, P a = true → Q a = true) :
    ∀ (ts : List Term), Term.anyAtomList P ts = true → Term.anyAtomList Q ts = true
  | [], ht => by simp [Term.anyAtomList] at ht
  | t :: ts, ht => by
    simp only [Term.anyAtomList, Bool.or_eq_true_iff] at ht ⊢
    rcases ht with ht | ht
    · exact .inl (Term.anyAtom_mono h t ht)
    · exact .inr (Term.anyAtomList_mono h ts ht)

theorem _root_.Ochr.Term.anyAtomArms_mono {P Q : Value → Bool} (h : ∀ a, P a = true → Q a = true) :
    ∀ (as : List (Hint × Term)), Term.anyAtomArms P as = true → Term.anyAtomArms Q as = true
  | [], ht => by simp [Term.anyAtomArms] at ht
  | (_, t) :: as, ht => by
    simp only [Term.anyAtomArms, Bool.or_eq_true_iff] at ht ⊢
    rcases ht with ht | ht
    · exact .inl (Term.anyAtom_mono h t ht)
    · exact .inr (Term.anyAtomArms_mono h as ht)
end

/-- A loan the meaning reads is a loan main's `hasLoan` counts. -/
theorem _root_.Ochr.Value.hasLoan_of_hasLoanM {l : Nat} {v : Value} (h : v.hasLoanM l = true) :
    v.hasLoan l = true :=
  Value.anyAtom_mono (fun a ha => by
    cases a <;> simp_all [BEq.beq, Value.beq]) v h

/-! ## Hint-free tails (`HintIndep.lean` proves what they give; (WF16) asks them of Ω) -/

mutual
/-- No tail of the term reads the hint. -/
def _root_.Ochr.Term.tailHintFree (Γ : List IndDecl) : Term → Bool
  | .letIn _ _ w => Term.tailHintFree Γ w
  | .seq _ w => Term.tailHintFree Γ w
  | .matchNat _ z u => Term.tailHintFree Γ z && Term.tailHintFree Γ u
  | .matchInd _ _ arms => Term.armsHintFree Γ arms
  | .ctor ty _ _ ps _ =>
    !ps.isEmpty || (match Γ.find? (·.name == ty) with | some d => d.params.isEmpty | none => true)
  | .val v => Value.topHintFree Γ v
  -- a primitive is conservatively hint-reading, except the reads [Close] puts at its tails
  -- (`peek`/`clone` of a place); `J`'s transported term and `inplace` are not needed yet
  | .prim n [.place _] => n == "peek" || n == "clone"
  | .prim _ _ => false
  | _ => true
termination_by structural t => t

def _root_.Ochr.Term.armsHintFree (Γ : List IndDecl) : List (Hint × Term) → Bool
  | [] => true
  | (_, t) :: rest => Term.tailHintFree Γ t && Term.armsHintFree Γ rest
termination_by structural arms => arms

/-- The hint reaches the value's meaning through no bare constructor and no sealed program with a
hint-reading tail. -/
def _root_.Ochr.Value.topHintFree (Γ : List IndDecl) : Value → Bool
  | .borrow _ w => Value.topHintFree Γ w
  | .gloan _ w => Value.topHintFree Γ w
  | .sealed t => Term.tailHintFree Γ t
  | .ind ty _ _ [] _ => (match Γ.find? (·.name == ty) with | some d => d.params.isEmpty | none => true)
  | _ => true
termination_by structural v => v
end


end Ochr.Meaning
