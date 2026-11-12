import Ochr.Meaning.State

/-!
# Well-formedness (WF1)–(WF7) and membership (docs/18 §2 "Well-formedness", §3.3 (b), (c))

The meaning of a state is defined for every `MState`; it *means the right thing* only under the
borrow discipline, which is what (WF1)–(WF7) say. They are stated here as `Prop`s on `MState`,
syntactically where the plan's clause is syntactic and semantically where it speaks of types.
Membership (b) is the typed part: every stored value's meaning lies in its stored type's meaning,
under every typed future, for an assignment that is itself typed and satisfies the path
condition.

(WF5), loan-free arguments at a call point, is a property of a run, not of a state: it is stated
as `ArgsLoanFree` on the argument array, for the call step lemmas.

(WF6)'s typing half ("a binding holds a value of its type") is membership (b); its naming half
(every `σ` has a type in Δ, every label is below its counter) is `WF6` here.
-/

namespace Ochr.Meaning

/-! ## Syntactic helpers -/

mutual
/-- The loans of a value outside its sealed programs: the ones (WF2) counts, since a loan inside a
sealed program whose borrow is outside the run is inert and may occur any number of times. A
closure's or Π-closure's code embeds no live loan (WF4), so only their captures are read. -/
def _root_.Ochr.Value.outerLoans : Value → List Nat
  | .loan l => [l]
  | .succ w | .tRef w | .borrow _ w => w.outerLoans
  | .tEq A a b => A.outerLoans ++ a.outerLoans ++ b.outerLoans
  | .clo cs _ _ | .tPi cs _ _ => Value.outerLoansList cs
  | .ind _ _ _ ps fs => Value.outerLoansList ps ++ Value.outerLoansList fs
  | .tInd _ fs => Value.outerLoansList fs
  | _ => []
termination_by structural v => v

def _root_.Ochr.Value.outerLoansList : List Value → List Nat
  | [] => []
  | v :: vs => v.outerLoans ++ Value.outerLoansList vs
termination_by structural vs => vs
end

/-- The values held at the positions of Ω (not the values inside them). -/
def _root_.Ochr.Env.values (env : Env) : List Value := (allPos env).map (valAt env)

/-- A closure or Π-closure whose captures hold a borrow or `⊥`, or a sealed program that is not
closed (has a free variable): what (WF4) forbids anywhere in a value. -/
def _root_.Ochr.Value.badCapture : Value → Bool
  | .clo cs _ _ | .tPi cs _ _ => cs.any fun c => c.hasBorrow || c.hasHole
  | .sealed t => !t.freeVars.isEmpty
  | _ => false

/-- "A loan of `l` occurs in the content of the borrow `m`" (docs/18 WF3). -/
def loanUnder (env : Env) (l m : Nat) : Prop :=
  ∃ p ∈ allPos env, ∃ w, valAt env p = .borrow m w ∧ l ∈ w.loans

/-! ## The clauses -/

/-- (WF1) Each label has at most one borrow, and a borrow is the whole value of a position: never
inside data, a sealed program, a closure or a type, and never inside another borrow's content. -/
def WF1 (env : Env) : Prop :=
  (∀ p ∈ allPos env, match valAt env p with
    | .borrow _ w => ¬ w.hasBorrow
    | v => ¬ v.hasBorrow) ∧
  ∀ p ∈ allPos env, ∀ q ∈ allPos env, ∀ l, Env.shape env p = some l → Env.shape env q = some l → p = q

/-- (WF2) Every loan outside a sealed program has its borrow in Ω, and occurs once. -/
def WF2 (env : Env) : Prop :=
  (∀ v ∈ Env.values env, ∀ l ∈ v.outerLoans, liveLoan env l = true) ∧
  ∀ l, ((Env.values env).flatMap Value.outerLoans).count l ≤ 1

/-- (WF3) The relation "a loan of `l` occurs in the content of borrow `m`" is acyclic: ending
borrows in that order fixes each final content once (docs/27 §3.3). -/
def WF3 (env : Env) : Prop := WellFounded (loanUnder env)

/-- (WF4) Closures and Π-closures capture no borrow and no `⊥`; sealed programs are closed. -/
def WF4 (env : Env) : Prop := ∀ v ∈ Env.values env, ¬ v.anyAtom Value.badCapture

/-- (WF5) At a call point, each argument is loan-free or a borrow whose content is loan-free
(the precondition [Close] asserts; docs/27 §9: with a live loan in an argument, a read now would
depend on a write made later). -/
def ArgsLoanFree (env : Env) (ws : Array Value) : Prop :=
  ∀ w ∈ ws.toList, match w with
    | .borrow _ u => liveLoansIn env u = []
    | u => liveLoansIn env u = []

/-- (WF6), the naming half: every abstract value occurring in Ω, in a stored type, in Δ or in the
goal has a type in Δ, and every label and abstract value is below its counter (freshness). -/
def WF6 (st : MState) : Prop :=
  (∀ v ∈ Env.values st.env, ∀ σ, v.hasAbs σ → σ < st.absTy.size) ∧
  (∀ T ∈ st.absTy.toList, ∀ σ, T.hasAbs σ → σ < st.absTy.size) ∧
  (∀ G, st.goal = some G → ∀ σ, G.hasAbs σ → σ < st.absTy.size) ∧
  st.absTy.size ≤ st.nextAbs ∧
  ∀ v ∈ Env.values st.env, ∀ l ∈ v.loans, l < st.nextLoan

section
variable (dm : DataModel) (C : CodeMeaning) (Γ : List IndDecl)

/-- (WF7) `&` is applied only to types in `Type₀`: every borrow type in Ω's stored types has a
content type of level 1, so that a borrow means forward and backward functions on data. -/
def WF7 (ρ : Assignment) (st : MState) : Prop :=
  ∀ p T, MState.posTyM dm C Γ ρ st p = some T →
    ∀ f i b, p = .bind f i → st.env[f]?.bind (·.binds[i]?) = some b →
      ∀ A, b.ty = some (.tRef A) → (Value.tyM dm C Γ ρ (fun _ => .err) A).level = some 1

/-- (WF8) `&` occurs only at the top of a declared type (RULES §1, D48 (2)): a borrow type `&A`
is the whole stored type of a binding, the whole type of an abstract value or the whole goal,
with `A` borrow-free, and no `tRef` occurs inside any value of Ω, inside a type, or inside the
parameters a constructor value records. In particular no state holds the type value
`Eq(Type₀, &A, A)`, so the model's `⟦&A⟧ = ⟦A⟧` (Value.lean) can refute nothing the checker
proves (docs/31 D1). -/
def WF8 (st : MState) : Prop :=
  (∀ v ∈ Env.values st.env, ¬ v.typeHasRef) ∧
  (∀ (f i : Nat) (b : Binding), st.env[f]?.bind (fun fr => fr.binds[i]?) = some b →
    ∀ T : Value, b.ty = some T →
    match T with | .tRef A => ¬ A.typeHasRef | T => ¬ T.typeHasRef) ∧
  (∀ T ∈ st.absTy.toList, match T with | .tRef A => ¬ A.typeHasRef | T => ¬ T.typeHasRef) ∧
  (∀ G, st.goal = some G → match G with | .tRef A => ¬ A.typeHasRef | G => ¬ G.typeHasRef)

/-- Well-formedness, part (c) of the main theorem. -/
def WF (ρ : Assignment) (st : MState) : Prop :=
  WF1 st.env ∧ WF2 st.env ∧ WF3 st.env ∧ WF4 st.env ∧ WF6 st ∧ WF7 dm C Γ ρ st ∧ WF8 st

/-! ## Typed assignments, typed futures, membership -/

/-- A future is typed for Ω: each live borrow's final content lies in the content type of its
holder's declared borrow type (`⟦&T⟧ = ⟦T⟧`). -/
def TypedFuture (ρ : Assignment) (st : MState) (φ : Future) : Prop :=
  ∀ p l, Env.shape st.env p = some l → ∀ T, MState.posTyM dm C Γ ρ st p = some T → φ l ∈ₛ T

/-- An assignment of Ω (docs/18 Def. "assignment"): each `σ` means an element of `⟦Δ(σ)⟧_ρ`, and
the path condition holds: each generalisation record `n := σ` in force says `ρ σ = ⟦n⟧_ρ` (a
generalised program is hole-free, docs/27 Lemma 5, so its meaning does not read the future),
and each η-refinement `σ := C(σ̄)` says the same of its constructor value. -/
structure TypedAssignment (ρ : Assignment) (st : MState) : Prop where
  mem : ∀ σ, σ < st.absTy.size → ρ σ ∈ₛ MState.absTyM dm C Γ ρ st σ
  neutral : ∀ n σ, (n, σ) ∈ st.neutrals →
    ρ σ = Value.mean dm C Γ ρ (fun _ => .err) (.plain (MState.absTyM dm C Γ ρ st σ)) n
  eta : ∀ σ v, (σ, v) ∈ st.etaRefs →
    ρ σ = Value.mean dm C Γ ρ (fun _ => .err) (.plain (MState.absTyM dm C Γ ρ st σ)) v

/-- Membership, part (b) of the main theorem: under every typed future, every position with a
stored type holds a (possibly partly moved) member of it; Δ's types and the goal are types. -/
structure Membership (ρ : Assignment) (st : MState) : Prop where
  pos : ∀ φ, TypedFuture dm C Γ ρ st φ →
    ∀ p T, MState.posTyM dm C Γ ρ st p = some T → (Env.mean dm C Γ ρ φ st.env p).pmem T
  absTy : ∀ σ, σ < st.absTy.size → (MState.absTyM dm C Γ ρ st σ).level.isSome
  goal : ∀ G, MState.goalM dm C Γ ρ st = some G → G.level.isSome

/-- The hypothesis of the main theorem at a state: (b) and (c) under an assignment of it. -/
def Good (ρ : Assignment) (st : MState) : Prop :=
  TypedAssignment dm C Γ ρ st ∧ Membership dm C Γ ρ st ∧ WF dm C Γ ρ st

/-! ## Values in flight: the future typed at their labels too

`TypedFuture` types a label only at a *typed* holder. A borrow the checker holds in its monad
(the result of [Borrow], or of a [Read] that moves a borrow out) is counted as an untyped
temporary (`MState.withTemp`), so its label is left untyped and the typed lender, which reads
that label, has no member (the pilot's refutations of `borrowPlace_step_stmt` and
`readPlace_step_stmt`, `Steps/BorrowCE.lean`). The in-flight value is typed by the step's
statement instead: a `Flight` lists the labels in flight with their content types (the
reference run's result type gives both), and `GoodF` is `Good` with the future typed at them. -/

/-- Labels in flight with their content types. -/
abbrev Flight : Type 3 := List (Nat × TyM)

/-- `TypedFuture`, and typed at the labels in flight. -/
def TypedFutureF (ρ : Assignment) (st : MState) (fl : Flight) (φ : Future) : Prop :=
  TypedFuture dm C Γ ρ st φ ∧ ∀ l T, (l, T) ∈ fl → φ l ∈ₛ T

/-- `Membership` under futures typed at the flight too. -/
structure MembershipF (ρ : Assignment) (st : MState) (fl : Flight) : Prop where
  pos : ∀ φ, TypedFutureF dm C Γ ρ st fl φ →
    ∀ p T, MState.posTyM dm C Γ ρ st p = some T → (Env.mean dm C Γ ρ φ st.env p).pmem T
  absTy : ∀ σ, σ < st.absTy.size → (MState.absTyM dm C Γ ρ st σ).level.isSome
  goal : ∀ G, MState.goalM dm C Γ ρ st = some G → G.level.isSome

/-- `Good`, with the values in flight typed. `GoodF ρ st [] ↔ Good ρ st` (`goodF_nil`). -/
def GoodF (ρ : Assignment) (st : MState) (fl : Flight) : Prop :=
  TypedAssignment dm C Γ ρ st ∧ MembershipF dm C Γ ρ st fl ∧ WF dm C Γ ρ st

theorem typedFutureF_nil (ρ : Assignment) (st : MState) (φ : Future) :
    TypedFutureF dm C Γ ρ st [] φ ↔ TypedFuture dm C Γ ρ st φ :=
  ⟨fun h => h.1, fun h => ⟨h, fun _ _ h => by cases h⟩⟩

theorem goodF_nil (ρ : Assignment) (st : MState) : GoodF dm C Γ ρ st [] ↔ Good dm C Γ ρ st := by
  constructor
  · rintro ⟨ha, hm, hw⟩
    exact ⟨ha, ⟨fun φ hφ => hm.pos φ ((typedFutureF_nil ..).mpr hφ), hm.absTy, hm.goal⟩, hw⟩
  · rintro ⟨ha, hm, hw⟩
    exact ⟨ha, ⟨fun φ hφ => hm.pos φ ((typedFutureF_nil ..).mp hφ), hm.absTy, hm.goal⟩, hw⟩

end

end Ochr.Meaning
