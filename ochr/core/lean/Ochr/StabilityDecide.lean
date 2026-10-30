import Ochr.Stability

/-!
# Stability: the decisions that commute with refinement, proved

`Ochr/Stability.lean` states the paper's Conjecture 2 as `DecisionsCommute ∧ RunsCorrespond`.
This file proves the parts of `DecisionsCommute` that do not need `RunsCorrespond`, one lemma
per decision function, and names exactly what the rest assumes (`notes/stability.md` §9).
`StabilitySig.lean` proves that a refinement keeps the signature, so the decisions here that
read only the signature are the same at the refined state, and states the proved fields.

The tool is `step`, every layer of the machine monad `M` taken apart, with one lemma per
primitive (`step_bind`, `step_get`, …), so that a `do` block can be unfolded with `simp only`.
-/

namespace Ochr.Stability
open Ochr

/-- One run of `M`, every layer taken apart: the outcome (exhausted, failed, or a value and a
state), the fuel left, and the log. -/
abbrev Res (α : Type) := (Except Exhausted (Except Fail (α × MState)) × Fuel) × Array LogEntry

/-- Run `x` from a state, a fuel counter and a log. -/
@[inline] def step {α : Type} (x : M α) (Ω : MState) (fl : Fuel) (lg : Array LogEntry) : Res α :=
  ((((x.run Ω).run).run).run fl).run lg

/-- Continue a run with `f` when it succeeded. -/
@[inline] def cont {α β : Type} (r : Res α) (f : α → MState → Fuel → Array LogEntry → Res β) : Res β :=
  match r with
  | ((.ok (.ok (a, Ω)), fl), lg) => f a Ω fl lg
  | ((.ok (.error e), fl), lg) => ((.ok (.error e), fl), lg)
  | ((.error e, fl), lg) => ((.error e, fl), lg)

theorem step_pure {α} (a : α) Ω fl lg : step (pure a : M α) Ω fl lg = ((.ok (.ok (a, Ω)), fl), lg) := rfl

theorem step_bind {α β} (x : M α) (f : α → M β) Ω fl lg :
    step (x >>= f) Ω fl lg = cont (step x Ω fl lg) fun a Ω' fl' lg' => step (f a) Ω' fl' lg' := by
  simp only [step, cont, bind, StateT.bind, ExceptT.bind, ExceptT.mk, ExceptT.bindCont, StateT.run,
    ExceptT.run]
  rcases x Ω fl lg with ⟨⟨r, fl'⟩, lg'⟩; rcases r with e | (e | ⟨a, Ω'⟩) <;> rfl

theorem step_get Ω fl lg : step (get : M MState) Ω fl lg = ((.ok (.ok (Ω, Ω)), fl), lg) := rfl

theorem step_modify (g : MState → MState) Ω fl lg :
    step (modify g : M Unit) Ω fl lg = ((.ok (.ok ((), g Ω)), fl), lg) := rfl

theorem step_throwFail {α} (e : Fail) Ω fl lg :
    step (throw e : M α) Ω fl lg = ((.ok (.error e), fl), lg) := rfl

theorem step_err {α} (m : String) Ω fl lg :
    step (err m : M α) Ω fl lg = ((.ok (.error (.error m)), fl), lg) := rfl

theorem step_exhausted {α} (m : String) Ω fl lg :
    step (exhausted m : M α) Ω fl lg = ((.error ⟨m⟩, fl), lg) := rfl

/-- `run?` is the successful outcome of `step` from a fresh fuel counter and an empty log. -/
theorem run?_eq {α} (x : M α) (Ω : MState) (fuel : Nat) :
    run? x Ω fuel = match step x Ω ⟨fuel⟩ #[] with
      | ((.ok (.ok (a, Ω')), _), _) => some (a, Ω')
      | _ => none := by
  simp only [run?, runMachine, step]
  rcases (((((x.run Ω).run).run).run ⟨fuel⟩).run #[]) with ⟨⟨r, fl⟩, lg⟩
  rcases r with e | (e | ⟨a, Ω'⟩) <;> rfl

/-! ## Computations that read only the signature

A computation *reads only the signature* when its outcome is a function of the declared
inductive types and globals, and it changes nothing: not the state, not the fuel, not the
log. Every decision that reads only syntax and declarations is of this kind, so it gives the
same answer at any two states with the same signature. -/

/-- The outcome of a computation that reads only the signature: a failure, or a value. -/
abbrev SigOut (α : Type) := Except Fail α

/-- Turn a signature-determined outcome into a run from `Ω`, leaving everything as it was. -/
@[inline] def sigRes {α : Type} (o : SigOut α) (Ω : MState) (fl : Fuel) (lg : Array LogEntry) : Res α :=
  match o with
  | .ok a => ((.ok (.ok (a, Ω)), fl), lg)
  | .error e => ((.ok (.error e), fl), lg)

/-- `x` reads only the signature: its run from any state is `f` of that state's inductives and
globals, and changes nothing else. -/
def ReadsSig {α : Type} (x : M α) : Prop :=
  ∃ f : List IndDecl → List GDef → SigOut α, ∀ Ω fl lg, step x Ω fl lg = sigRes (f Ω.inds Ω.globals) Ω fl lg

theorem ReadsSig.pure {α} (a : α) : ReadsSig (pure a : M α) :=
  ⟨fun _ _ => .ok a, fun _ _ _ => rfl⟩

theorem ReadsSig.err {α} (m : String) : ReadsSig (err m : M α) :=
  ⟨fun _ _ => .error (.error m), fun _ _ _ => rfl⟩

theorem ReadsSig.bind {α β} {x : M α} {f : α → M β} (hx : ReadsSig x) (hf : ∀ a, ReadsSig (f a)) :
    ReadsSig (x >>= f) := by
  obtain ⟨g, hg⟩ := hx
  let h := fun a => Classical.choose (hf a)
  have hh : ∀ a Ω fl lg, step (f a) Ω fl lg = sigRes (h a Ω.inds Ω.globals) Ω fl lg :=
    fun a => Classical.choose_spec (hf a)
  refine ⟨fun is gs => match g is gs with
    | .ok a => h a is gs
    | .error e => .error e, fun Ω fl lg => ?_⟩
  rw [step_bind, hg]
  cases hgo : g Ω.inds Ω.globals with
  | error e => simp only [sigRes, cont, hgo]
  | ok a => simp only [sigRes, cont, hgo, hh]

theorem ReadsSig.ite {α} (c : Prop) [Decidable c] {x y : M α} (hx : ReadsSig x) (hy : ReadsSig y) :
    ReadsSig (if c then x else y) := by
  by_cases h : c <;> simp [h, hx, hy]

/-- Agreeing on the signature: the same inductive declarations and globals. -/
structure SigAgree (Ω Ω' : MState) : Prop where
  inds : Ω.inds = Ω'.inds
  globals : Ω.globals = Ω'.globals

/-- A computation that reads only the signature gives the same answer at two states with the
same signature (its value; it changes neither state). -/
theorem ReadsSig.agree {α} {x : M α} (hx : ReadsSig x) {Ω Ω' : MState} (h : SigAgree Ω Ω') (fuel : Nat) :
    (run? x Ω fuel).map (·.1) = (run? x Ω' fuel).map (·.1) := by
  obtain ⟨f, hf⟩ := hx
  rw [run?_eq, run?_eq, hf, hf, h.inds, h.globals]
  cases f Ω'.inds Ω'.globals <;> rfl

/-- It changes no state: a successful run ends where it began. -/
theorem ReadsSig.state {α} {x : M α} (hx : ReadsSig x) {Ω : MState} {fuel : Nat} {a : α} {Ω' : MState}
    (h : run? x Ω fuel = some (a, Ω')) : Ω' = Ω := by
  obtain ⟨f, hf⟩ := hx
  rw [run?_eq, hf] at h
  cases hfo : f Ω.inds Ω.globals with
  | error e => simp [sigRes, hfo] at h
  | ok b => simp [sigRes, hfo] at h; exact h.2.symm

theorem readsSig_lookupInd (n : String) : ReadsSig (lookupInd n) :=
  ⟨fun is _ => match is.find? (·.name == n) with
    | some d => .ok d
    | none => .error (.error s!"unknown inductive type {n}"), fun Ω fl lg => by
    simp only [lookupInd, step_bind, step_get, cont]
    cases Ω.inds.find? (·.name == n) <;> rfl⟩

theorem readsSig_lookupGlobal (n : String) : ReadsSig (lookupGlobal n) :=
  ⟨fun _ gs => match gs.find? (·.name == n) with
    | some g => .ok g
    | none => .error (.error s!"unknown constant {n}"), fun Ω fl lg => by
    simp only [lookupGlobal, step_bind, step_get, cont]
    cases Ω.globals.find? (·.name == n) <;> rfl⟩

theorem ReadsSig.allM {α} (p : α → M Bool) (hp : ∀ a, ReadsSig (p a)) :
    ∀ l : List α, ReadsSig (l.allM p)
  | [] => by simpa [List.allM] using ReadsSig.pure true
  | a :: l => by
    simp only [List.allM]
    exact (hp a).bind fun b => by
      cases b
      · exact ReadsSig.pure false
      · exact ReadsSig.allM p hp l

/-- Reading the state, then continuing with something that depends on the state only through
its signature and reads only the signature, reads only the signature. -/
theorem ReadsSig.get {α} {k : MState → M α} (hk : ∀ s, ReadsSig (k s))
    (hdep : ∀ s, k s = k { (default : MState) with inds := s.inds, globals := s.globals }) :
    ReadsSig (get >>= k) := by
  let sig := fun (is : List IndDecl) (gs : List GDef) => ({ (default : MState) with inds := is, globals := gs } : MState)
  let h := fun s => Classical.choose (hk s)
  have hh : ∀ s Ω fl lg, step (k s) Ω fl lg = sigRes (h s Ω.inds Ω.globals) Ω fl lg :=
    fun s => Classical.choose_spec (hk s)
  refine ⟨fun is gs => h (sig is gs) is gs, fun Ω fl lg => ?_⟩
  simp only [step_bind, step_get, cont]
  rw [hdep Ω, hh]

/-! ## The decisions that read only syntax and the signature

These are the census's by-construction sites whose inputs are syntax and declarations:
whether a constructor builds a proof (D42), whether a field is a proof (D42, D71's equation
fields), whether a match on a proof may produce data (D45, subsingleton elimination), whether a
match is on a proof (site 11). Each reads only the signature, so it gives the same answer at
any two states with the same signature (`ReadsSig.agree`). -/

theorem readsSig_ctorIsProof (ty : String) : ReadsSig (ctorIsProof ty) := by
  unfold ctorIsProof
  exact (readsSig_lookupInd ty).bind fun _ => .pure _

theorem readsSig_byTypeMatch (ty : String) (arms : List (Hint × Term)) : ReadsSig (byTypeMatch ty arms) := by
  unfold byTypeMatch
  split
  · exact .pure _
  · exact (readsSig_lookupInd ty).bind fun _ => .pure _

theorem readsSig_fieldTermIsProp (d : IndDecl) (FT : Term) : ReadsSig (fieldTermIsProp d FT) := by
  unfold fieldTermIsProp
  split
  · exact .pure _
  · exact (readsSig_lookupInd _).bind fun _ => .pure _
  · exact .pure _
  · exact ReadsSig.get (fun s => by split <;> exact .pure _) (fun _ => rfl)
  · exact .pure _

theorem readsSig_fieldIsProof (g : FieldRef) : ReadsSig (fieldIsProof g) := by
  unfold fieldIsProof
  refine (readsSig_lookupInd _).bind fun d => ?_
  split
  · split
    · exact readsSig_fieldTermIsProp _ _
    · exact .pure _
  · exact .pure _

theorem readsSig_largeElim (d : IndDecl) : ReadsSig (largeElim d) := by
  unfold largeElim
  split
  · exact .pure _
  · exact ReadsSig.allM _ (fun _ => readsSig_fieldTermIsProp _ _) _
  · exact .pure _

/-- The erasure pre-pass's flags for a term, given its declared reading, read only the term's
syntax and the reading (it fails on a reading with no declared type, D63). -/
theorem readsSig_preFlags (t : Term) (d : DeclInfo) : ReadsSig (preFlags t d) := by
  unfold preFlags
  simp only []
  split
  · exact (ReadsSig.err _).bind fun _ => by split <;> exact .pure _
  · split
    · exact .pure _
    · exact .pure _

/-- D77, site 7: a binding's class is its declared type's reading, a `DeclInfo`, which holds no
value; refinement cannot reach it, and the check reads nothing else. -/
theorem readsSig_refineDecl (d : DeclInfo) : ReadsSig (refineDecl d) := by
  unfold refineDecl
  simp only []
  split
  · exact (ReadsSig.err _).bind fun _ => .pure _
  · exact .pure _

/-! ## What a successful run returns

`Post x P`: whenever `x` succeeds, its value satisfies `P`. The shape lemmas below are stated
this way: substitution keeps a term's or a value's outer shape, whatever happens inside. -/

/-- Whenever `x` succeeds, from any state, fuel and log, its value satisfies `P`. -/
def Post {α : Type} (x : M α) (P : α → Prop) : Prop :=
  ∀ Ω fl lg a Ω' fl' lg', step x Ω fl lg = ((.ok (.ok (a, Ω')), fl'), lg') → P a

theorem Post.pure {α} {P : α → Prop} {a : α} (h : P a) : Post (pure a : M α) P := by
  intro Ω fl lg b Ω' fl' lg' hs
  simp only [step_pure, Prod.mk.injEq, Except.ok.injEq] at hs
  exact hs.1.1.1 ▸ h

theorem Post.bind {α β} {x : M α} {f : α → M β} {Q : α → Prop} {P : β → Prop}
    (hx : Post x Q) (hf : ∀ a, Q a → Post (f a) P) : Post (x >>= f) P := by
  intro Ω fl lg b Ω' fl' lg' hs
  rw [step_bind] at hs
  revert hs
  rcases hr : step x Ω fl lg with ⟨⟨r, fl₁⟩, lg₁⟩
  rcases r with e | (e | ⟨a, Ω₁⟩) <;> simp only [cont] <;> intro hs
  · cases hs
  · cases hs
  · exact hf a (hx Ω fl lg a Ω₁ fl₁ lg₁ hr) Ω₁ fl₁ lg₁ b Ω' fl' lg' hs

theorem Post.bind_any {α β} {x : M α} {f : α → M β} {P : β → Prop} (hf : ∀ a, Post (f a) P) :
    Post (x >>= f) P :=
  Post.bind (Q := fun _ => True) (fun _ _ _ _ _ _ _ _ => trivial) fun a _ => hf a

theorem Post.exhausted {α} {P : α → Prop} (m : String) : Post (exhausted m : M α) P := by
  intro Ω fl lg a Ω' fl' lg' hs; cases hs

theorem Post.err {α} {P : α → Prop} (m : String) : Post (err m : M α) P := by
  intro Ω fl lg a Ω' fl' lg' hs; cases hs

theorem Post.ite {α} {P : α → Prop} (c : Prop) [Decidable c] {x y : M α} (hx : Post x P) (hy : Post y P) :
    Post (if c then x else y) P := by
  by_cases h : c <;> simp [h, hx, hy]

theorem Post.mono {α} {x : M α} {P Q : α → Prop} (hx : Post x P) (h : ∀ a, P a → Q a) : Post x Q :=
  fun Ω fl lg a Ω' fl' lg' hs => h a (hx Ω fl lg a Ω' fl' lg' hs)

/-- A successful `run?` of `x` returns a value satisfying `x`'s postcondition. -/
theorem Post.run? {α} {x : M α} {P : α → Prop} (hx : Post x P) {Ω : MState} {fuel : Nat} {a : α} {Ω' : MState}
    (h : run? x Ω fuel = some (a, Ω')) : P a := by
  rw [run?_eq] at h
  revert h
  rcases hs : step x Ω ⟨fuel⟩ #[] with ⟨⟨r, fl⟩, lg⟩
  rcases r with e | (e | ⟨b, Ω₁⟩)
  · simp
  · simp
  · simp only [Option.some.injEq, Prod.mk.injEq]
    rintro ⟨rfl, rfl⟩
    exact hx Ω ⟨fuel⟩ #[] b Ω₁ fl lg hs

/-- Folding a step that keeps an invariant keeps it. -/
theorem Post.foldlM {α β} (f : β → α → M β) (Inv : β → Prop) (hf : ∀ b a, Inv b → Post (f b a) Inv) :
    ∀ (l : List α) (b : β), Inv b → Post (l.foldlM f b) Inv
  | [], b, hb => by simpa [List.foldlM] using Post.pure hb
  | a :: l, b, hb => by
    simp only [List.foldlM]
    exact Post.bind (hf b a hb) fun b' hb' => Post.foldlM f Inv hf l b' hb'

/-! ## Substitution keeps outer shapes (L-head, for terms and Π-types)

A refinement substitutes into the values embedded in a term (`substT`), never into its syntax:
the term's outer constructor stays. That is all [Close]'s row and a syntactic erasure class
read off a codomain term. -/

/-- The part of a codomain term [Close]'s row and a function type's class read: `Unit`, `&T`,
an embedded value (a stuck block's match type), a sort, or something else. -/
def rowOf : Term → Nat
  | .unit => 1
  | .ref _ => 2
  | .val _ => 3
  | .sort _ => 4
  | _ => 0

/-- Substituting into a term keeps its outer constructor (as `rowOf` sees it). -/
theorem substT_rowOf (fuel : Nat) (x r : Value) (t : Term) :
    Post (substT fuel x r t) (fun t' => rowOf t' = rowOf t) := by
  cases fuel with
  | zero => unfold substT; exact Post.exhausted _
  | succ n =>
    unfold substT
    simp only []
    refine Post.ite _ (Post.pure rfl) ?_
    split <;> (repeat (with_reducible apply Post.bind_any; intro)) <;> exact Post.pure rfl

/-- Substituting into a Π-type's code keeps it a Π-type, with a codomain of the same shape. -/
theorem substT_pi (fuel : Nat) (x r : Value) (hs : List Hint) (ds : List Term) (c : Term) :
    Post (substT fuel x r (.pi hs ds c)) (fun t' => ∃ ds' c', t' = .pi hs ds' c' ∧ rowOf c' = rowOf c) := by
  cases fuel with
  | zero => unfold substT; exact Post.exhausted _
  | succ n =>
    unfold substT
    simp only []
    refine Post.ite _ (Post.pure ⟨ds, c, rfl, rfl⟩) ?_
    exact Post.bind_any fun ds' => Post.bind (substT_rowOf n x r c) fun c' hc => Post.pure ⟨ds', c', rfl, hc⟩

/-- Substituting a value for an abstract value inside a Π-type keeps it a Π-type, with a codomain
of the same shape: its captures and embedded values change, its syntax does not. -/
theorem substV_tPi (fuel : Nat) (σ : Nat) (r : Value) (cs : List Value) (hs : List Hint) (ds : List Term) (c : Term) :
    Post (substV fuel (.abs σ) r (.tPi cs (.pi hs ds c)))
      (fun v' => ∃ cs' ds' c', v' = .tPi cs' (.pi hs ds' c') ∧ rowOf c' = rowOf c) := by
  cases fuel with
  | zero => unfold substV; exact Post.exhausted _
  | succ n =>
    unfold substV
    simp only []
    refine Post.ite _ (Post.pure ⟨cs, ds, c, rfl, rfl⟩) ?_
    have hne : (Value.tPi cs (.pi hs ds c) == Value.abs σ) = false := rfl
    simp only [hne, Bool.false_eq_true, ↓reduceIte]
    exact Post.bind_any fun cs' => Post.bind (substT_pi n _ r hs ds c) fun t' ⟨ds', c', ht, hc⟩ =>
      Post.pure ⟨cs', ds', c', by rw [ht], hc⟩

/-- A refinement keeps a Π-type a Π-type, with a codomain of the same shape. -/
theorem onValue_tPi (α : Refinement) (fuel : Nat) (cs : List Value) (hs : List Hint) (ds : List Term) (c : Term) :
    Post (α.onValue fuel (.tPi cs (.pi hs ds c)))
      (fun v' => ∃ cs' ds' c', v' = .tPi cs' (.pi hs ds' c') ∧ rowOf c' = rowOf c) := by
  unfold Refinement.onValue
  refine Post.foldlM _ (fun (v : Value) => ∃ cs' ds' c', v = .tPi cs' (.pi hs ds' c') ∧ rowOf c' = rowOf c)
    (fun v p ⟨cs', ds', c', hv, hc⟩ => ?_) α _ ⟨cs, ds, c, rfl, rfl⟩
  subst hv
  exact (substV_tPi fuel p.1 p.2 cs' hs ds' c').mono fun v' ⟨cs'', ds'', c'', h1, h2⟩ =>
    ⟨cs'', ds'', c'', h1, h2.trans hc⟩

/-! ## [Close]'s row (site 8) and a function type's class (site 3), read off the codomain term -/

/-- [Close]'s row for a codomain term that is not an embedded value: `Unit`, `&T`, or data. -/
def rowKind (n : Nat) : Kind := if n == 1 then .unit else if n == 2 then .ref else .data

/-- [Close]'s row of a function type whose codomain term is not an embedded value is read off
the term alone: it reads no state and changes none. -/
theorem step_declKind (n : Nat) (cs : List Value) (hs : List Hint) (ds : List Term) (c : Term)
    (hc : rowOf c ≠ 3) (Ω : MState) (fl : Fuel) (lg : Array LogEntry) :
    step (declKind (n+1) (.tPi cs (.pi hs ds c))) Ω fl lg = ((.ok (.ok (rowKind (rowOf c), Ω)), fl), lg) := by
  unfold declKind
  cases c <;> simp_all [rowOf, rowKind] <;> rfl

theorem run?_declKind (fuel : Nat) (cs : List Value) (hs : List Hint) (ds : List Term) (c : Term)
    (hc : rowOf c ≠ 3) (Ω : MState) :
    (run? (declKind fuel (.tPi cs (.pi hs ds c))) Ω fuel).map (·.1) =
      if fuel = 0 then none else some (rowKind (rowOf c)) := by
  cases fuel with
  | zero => rw [run?_eq]; unfold declKind; rfl
  | succ n => rw [run?_eq, step_declKind n cs hs ds c hc]; rfl

/-- **Site 8, for functions (not stuck blocks): [Close]'s row commutes with refinement.** A
refinement substitutes into a Π-type's captures and embedded values, never its syntax, so the
codomain term keeps its shape (`onValue_tPi`), and the row is read off that shape alone, at any
state. (A stuck block's codomain is an embedded value, the match's type, whose row reads that
type's declared sort: not proved here, `notes/stability.md` §9.) -/
theorem closeRow_fn (Ω : MState) (α : Refinement) (cs : List Value) (hs : List Hint) (ds : List Term)
    (c : Term) (hc : rowOf c ≠ 3) (Pα : Value) (fuel : Nat)
    (hP : (run? (α.onValue fuel (.tPi cs (.pi hs ds c))) Ω fuel).map (·.1) = some Pα) (Ωα : MState) :
    (run? (declKind fuel Pα) Ωα fuel).map (·.1) = (run? (declKind fuel (.tPi cs (.pi hs ds c))) Ω fuel).map (·.1) := by
  obtain ⟨⟨a, Ω'⟩, hrun, ha⟩ := Option.map_eq_some_iff.mp hP
  simp only at ha; subst ha
  obtain ⟨cs', ds', c', rfl, hc'⟩ := (onValue_tPi α fuel cs hs ds c).run? hrun
  rw [run?_declKind fuel cs' hs ds' c' (hc' ▸ hc), run?_declKind fuel cs hs ds c hc, hc']

/-- The erasure class a function type's codomain term fixes by its shape alone: a sort returns
types (1); an embedded value (a stuck block's function) is given its class at its call (0). -/
def shapeClass (n : Nat) : Option Nat := if n == 4 then some 1 else if n == 3 then some 0 else none

/-- The class cache is sound for `P` at `Ω`: every entry whose key `fnClass` would match is the
class `P`'s codomain shape fixes. `fnClass` is the only writer of the cache, so this holds of
every state the machine reaches (an invariant of the machine, not proved here). -/
def ClassCacheSound (Ω : MState) (P : Value) : Prop :=
  ∀ cs hs ds c k K, P = .tPi cs (.pi hs ds c) → shapeClass (rowOf c) = some K →
    ∀ Q, (Q, k) ∈ Ω.classCache → (P == Q) = true → k = K

theorem lookup_mem {α β} [BEq α] {a : α} {b : β} : ∀ {l : List (α × β)}, l.lookup a = some b →
    ∃ q, (q, b) ∈ l ∧ (a == q) = true
  | [], h => by simp [List.lookup] at h
  | (q, c) :: l, h => by
    simp only [List.lookup] at h
    split at h
    · rename_i hq; cases h; exact ⟨q, by simp, hq⟩
    · obtain ⟨q', hm, hq'⟩ := lookup_mem h; exact ⟨q', by simp [hm], hq'⟩

/-- A function type's class, when its codomain's shape fixes it, is that class, at any state
whose class cache is sound for it. -/
theorem step_fnClass_shape (n : Nat) (cs : List Value) (hs : List Hint) (ds : List Term) (c : Term) (K : Nat)
    (hK : shapeClass (rowOf c) = some K) (Ω : MState) (hΩ : ClassCacheSound Ω (.tPi cs (.pi hs ds c)))
    (fl : Fuel) (lg : Array LogEntry) :
    ∃ Ω', step (fnClass (n+1) (.tPi cs (.pi hs ds c))) Ω fl lg = ((.ok (.ok (K, Ω')), fl), lg) := by
  unfold fnClass
  simp only [step_bind, step_get, cont]
  cases hl : Ω.classCache.lookup (Value.tPi cs (.pi hs ds c)) with
  | some k =>
    obtain ⟨q, hq, hpq⟩ := lookup_mem hl
    have := hΩ cs hs ds c k K rfl hK q hq hpq
    subst this
    exact ⟨Ω, rfl⟩
  | none =>
    cases c <;> simp_all [shapeClass, rowOf] <;> (subst_vars; exact ⟨_, rfl⟩)

theorem run?_fnClass_shape (fuel : Nat) (cs : List Value) (hs : List Hint) (ds : List Term) (c : Term) (K : Nat)
    (hK : shapeClass (rowOf c) = some K) (Ω : MState) (hΩ : ClassCacheSound Ω (.tPi cs (.pi hs ds c))) :
    (run? (fnClass fuel (.tPi cs (.pi hs ds c))) Ω fuel).map (·.1) = if fuel = 0 then none else some K := by
  cases fuel with
  | zero => rw [run?_eq]; unfold fnClass; rfl
  | succ n =>
    obtain ⟨Ω', h⟩ := step_fnClass_shape n cs hs ds c K hK Ω hΩ ⟨n+1⟩ #[]
    rw [run?_eq, h]; rfl

/-- **Site 3, by shape: a function type's class commutes with refinement** when its codomain
term's shape fixes it (a sort: returns types; a stuck block's function: class given at its
call), at states whose class caches are sound. The general case reads the captured values'
declared readings (`valueDecl`), which needs evaluation to preserve declared types (D55, not
proved here, `notes/stability.md` §9). -/
theorem fnClass_shape (Ω : MState) (α : Refinement) (cs : List Value) (hs : List Hint) (ds : List Term)
    (c : Term) (K : Nat) (hK : shapeClass (rowOf c) = some K) (Pα : Value) (fuel : Nat)
    (hP : (run? (α.onValue fuel (.tPi cs (.pi hs ds c))) Ω fuel).map (·.1) = some Pα) (Ωα : MState)
    (hΩ : ClassCacheSound Ω (.tPi cs (.pi hs ds c))) (hΩα : ClassCacheSound Ωα Pα) :
    (run? (fnClass fuel Pα) Ωα fuel).map (·.1) = (run? (fnClass fuel (.tPi cs (.pi hs ds c))) Ω fuel).map (·.1) := by
  obtain ⟨⟨a, Ω'⟩, hrun, ha⟩ := Option.map_eq_some_iff.mp hP
  simp only at ha; subst ha
  obtain ⟨cs', ds', c', rfl, hc'⟩ := (onValue_tPi α fuel cs hs ds c).run? hrun
  rw [run?_fnClass_shape fuel cs' hs ds' c' K (hc' ▸ hK) Ωα hΩα, run?_fnClass_shape fuel cs hs ds c K hK Ω hΩ]

end Ochr.Stability
