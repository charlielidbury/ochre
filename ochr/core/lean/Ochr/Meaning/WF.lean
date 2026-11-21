import Ochr.Meaning.State
import Ochr.Meaning.Places

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

/- `Value.outerLoans` and `Value.outerLoansList`, the loans of a value outside its sealed programs
(the ones (WF2) counts, since a loan inside a sealed program whose borrow is outside the run is
inert and may occur any number of times; a closure's or Π-closure's code embeds no live loan
(WF4), so only their captures are read), were defined here. Main's D111 copied them into the
checker (`Ochr/Obs.lean`, clause for clause the same) to assert (WF2) at a read, so they are the
checker's now, and this file uses those. -/

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

/-- `σ` is *referenced* by the state: it occurs in a value of Ω, in a stored or deferred type, in
the goal, in a generalisation or η record in force, or in the type of a referenced unknown.

An assignment owes an element only to a referenced unknown (docs/18 Def. "assignment": "each
abstract value σ **of Ω**"). The types of the unknowns an arm of a split created are kept when the
arm is left (`exitWorld`, D37), but nothing kept names them, and such a type can be empty in the
world an assignment selects (a field of an arm the assignment does not take). Asked of every
`σ < absTy.size`, as `TypedAssignment.mem` first was, no assignment of the state after a split
would be typed, and `exitWorld_step_stmt` was false outright
(`Regress/ExitWorld_f32a7048.lean`, kernel-checked). -/
inductive _root_.Ochr.MState.Refd (st : MState) : Nat → Prop
  | val {σ : Nat} (v : Value) (hv : v ∈ Env.values st.env) (h : v.hasAbs σ = true) : Refd st σ
  | ty {σ : Nat} (f i : Nat) (b : Binding) (T : Value) (hb : st.env[f]?.bind (fun fr => fr.binds[i]?) = some b)
      (hT : b.ty = some T) (h : T.hasAbs σ = true) : Refd st σ
  | lazyTy {σ : Nat} (f i : Nat) (b : Binding) (P : Value) (ws : List Value) (j : Nat)
      (hb : st.env[f]?.bind (fun fr => fr.binds[i]?) = some b) (hT : b.lazyTy = some (P, ws, j))
      (h : P.hasAbs σ = true ∨ ∃ w ∈ ws, w.hasAbs σ = true) : Refd st σ
  | goal {σ : Nat} (G : Value) (hG : st.goal = some G) (h : G.hasAbs σ = true) : Refd st σ
  | neutral {σ : Nat} (n : Value) (σ' : Nat) (hn : (n, σ') ∈ st.neutrals) (h : σ = σ' ∨ n.hasAbs σ = true) : Refd st σ
  | eta {σ : Nat} (σ' : Nat) (v : Value) (he : (σ', v) ∈ st.etaRefs) (h : σ = σ' ∨ v.hasAbs σ = true) : Refd st σ
  | dep {σ : Nat} (σ' : Nat) (T : Value) (hσ' : Refd st σ') (hT : st.absTy[σ']? = some T) (h : T.hasAbs σ = true) :
      Refd st σ

/-- (WF6), the naming half: every unknown the state names (in Ω, a stored or deferred type, the goal,
a generalisation or η record, or the type of one of those: `MState.Refd`) and every unknown a
[Split] refinement names (the refined one and those of its value) has a type in Δ, every unknown
in Δ's types does, and every label is below its counter (freshness).

The counter of unknowns IS the number of typed unknowns. As first written the clause had
`absTy.size ≤ nextAbs`, which a state with an untyped name below the counter satisfies; `freshAbs`
names the new unknown `nextAbs` but types it at index `absTy.size`, so from such a state a
generalisation leaves an unknown with no type in Ω and the clause's own first part fails
(`Regress/GenNeutralContent.lean`, `wf6_le_not_kept`). The checker keeps the equality: `freshAbs`
grows both, `restoreKeep` and `exitWorld` keep the copy's counter and its whole list of types,
`seedHoles` sets both.

The first and third parts were, until 2026-11-21, "every unknown in a value of Ω" and "every
unknown in the goal": stored and deferred types and the records were unbounded, though the
docstring said stored types were bounded. A record naming the counter itself then met every
clause, and a fresh unknown (`freshAbs`) took that name: the record's path condition, which
asked nothing new before, then pins the fresh unknown, and `freshAbs_sim`'s conclusion (any value
for it) was false (`Regress/FreshBound.lean`). The checker never names an unknown at or above its
counter (fresh names are never reused; swept, docs/31 D36). -/
def WF6 (st : MState) : Prop :=
  (∀ σ, st.Refd σ → σ < st.absTy.size) ∧
  (∀ T ∈ st.absTy.toList, ∀ σ, T.hasAbs σ → σ < st.absTy.size) ∧
  (∀ σ r, (σ, r) ∈ st.refs → σ < st.absTy.size ∧ ∀ τ, r.hasAbs τ → τ < st.absTy.size) ∧
  st.absTy.size = st.nextAbs ∧
  ∀ v ∈ Env.values st.env, ∀ l ∈ v.loans, l < st.nextLoan

/-- The referenced unknowns are below `n` when every place `Refd` reads holds only unknowns below
`n` (for concrete states). -/
theorem _root_.Ochr.MState.refd_lt (st : MState) (n : Nat)
    (hv : ∀ v ∈ Env.values st.env, ∀ σ, v.hasAbs σ = true → σ < n)
    (hty : ∀ (f i : Nat) (b : Binding) (T : Value), st.env[f]?.bind (fun fr => fr.binds[i]?) = some b → b.ty = some T →
      ∀ σ, T.hasAbs σ = true → σ < n)
    (hlazy : ∀ (f i : Nat) (b : Binding) (P : Value) (ws : List Value) (j : Nat), st.env[f]?.bind (fun fr => fr.binds[i]?) = some b → b.lazyTy = some (P, ws, j) →
      ∀ σ, (P.hasAbs σ = true ∨ ∃ w ∈ ws, w.hasAbs σ = true) → σ < n)
    (hgoal : ∀ G, st.goal = some G → ∀ σ, G.hasAbs σ = true → σ < n)
    (hneut : ∀ (m : Value) (σ' : Nat), (m, σ') ∈ st.neutrals → ∀ σ, (σ = σ' ∨ m.hasAbs σ = true) → σ < n)
    (heta : ∀ (σ' : Nat) (v : Value), (σ', v) ∈ st.etaRefs → ∀ σ, (σ = σ' ∨ v.hasAbs σ = true) → σ < n)
    (habs : ∀ (σ' : Nat) (T : Value), st.absTy[σ']? = some T → ∀ σ, T.hasAbs σ = true → σ < n) :
    ∀ σ, st.Refd σ → σ < n := by
  intro σ h
  induction h with
  | val v hv' h => exact hv v hv' _ h
  | ty f i b T hb hT h => exact hty f i b T hb hT _ h
  | lazyTy f i b P ws j hb hT h => exact hlazy f i b P ws j hb hT _ h
  | goal G hG h => exact hgoal G hG _ h
  | neutral m σ' hm h => exact hneut m σ' hm _ h
  | eta σ' v he h => exact heta σ' v he _ h
  | dep σ' T _ hT h _ => exact habs σ' T hT _ h

/-- The label `l` occurs in Ω: some value at a position holds a loan of `l` or a borrow labelled
`l`, anywhere inside it. (What `Rel` asks the renaming of labels to cover: a label the checker
issued inside a private copy occurs nowhere after it, docs/31 D23.) -/
def _root_.Ochr.MState.Occurs (st : MState) (l : Nat) : Prop :=
  ∃ v ∈ Env.values st.env,
    v.anyAtom (fun a => a == .loan l || (match a with | .borrow l' _ => l' == l | _ => false)) = true

section
variable (dm : DataModel) (C : CodeMeaning) (Γ : List IndDecl)

/-- (WF7) `&` is applied only to types in `Type₀`: every borrow type in Ω's stored types has a
content type of level 1, so that a borrow means forward and backward functions on data. -/
def WF7 (ρ : Assignment) (st : MState) : Prop :=
  ∀ p T, MState.posTyM dm C Γ ρ st p = some T →
    ∀ f i b, p = .bind f i → st.env[f]?.bind (·.binds[i]?) = some b →
      ∀ A, b.ty = some (.tRef A) → (Value.tyM dm C Γ ρ (fun _ => .err) A).level = some 1

/-- A borrow type value. -/
def _root_.Ochr.Value.isRefV : Value → Bool
  | .tRef _ => true
  | _ => false

/-- An `&` out of place, anywhere inside a value (code's embedded values and recorded readings
included): `&` applied to a borrow type, or a borrow type as a parameter of an inductive type, as a
parameter a constructor value records, or as the type or a side of `Eq`. A borrow type at the top
of anything else (a value, a stored type, a parameter's declared reading) is in place. -/
def _root_.Ochr.Value.refMisplaced (v : Value) : Bool := v.anyAtom fun
  | .tRef A => A.isRefV
  | .tInd _ ps => ps.any Value.isRefV
  | .ind _ _ _ ps _ => ps.any Value.isRefV
  | .tEq A a b => A.isRefV || a.isRefV || b.isRefV
  | _ => false

/-- (WF8) `&` is applied only to a type with no `&` and never sits inside a data type or an
equation, wherever the type sits (RULES §1, D48 (2)): no borrow type is under another, a
parameter of an inductive type or of a constructor value, or the type or a side of `Eq`, in any
value of Ω, stored type, type of an unknown or goal. In particular no state holds the type value
`Eq(Type₀, &A, A)`, so the model's `⟦&A⟧ = ⟦A⟧` (Value.lean) can refute nothing the checker
proves (docs/31 D1). That `&` is applied only to data types is (WF7), for stored types.

As first written the clause said `&` occurs only at the top of a stored type, an unknown's type
or the goal, and nowhere inside a value of Ω. The sweep of the checker's own states (main
d26ee93c, `lake exe sweep`) found it false two ways, neither a fault: a borrow type in flight (the
temporary holding `&Nat` on exit of the type term of `def F (x : &Nat) : Nat := 0`), and a
closed-off stuck block, whose function keeps `&A` as a captured place's declared reading
(`def W (n : Nat) : Nat := (let a = 0; match n { Z => (a := 1), S _ => () }; a)`). Both have
`&` at the top of a type, which RULES allows. -/
def WF8 (st : MState) : Prop :=
  (∀ v ∈ Env.values st.env, v.refMisplaced = false) ∧
  (∀ (f i : Nat) (b : Binding), st.env[f]?.bind (fun fr => fr.binds[i]?) = some b →
    ∀ T : Value, b.ty = some T → T.refMisplaced = false) ∧
  (∀ T ∈ st.absTy.toList, T.refMisplaced = false) ∧
  (∀ G, st.goal = some G → G.refMisplaced = false)

/-- (WF9) A loan outside a sealed program sits at a typed position. A lender's value is read
at its position's hint; a hint-dependent content written back by [End] (a constructor with
unrecorded parameters, `Nil`) means `err` at an untyped position but its value at the holder's
`&D(ā)`, so `endBorrow_step` would fail there (the spine's finding, item 3 of docs/31's plan).
Temporaries hold values in flight, which a read's [Access] has made loan-free, and every lender
is a binding with a stored type; provers show the clause is kept, and a step that cannot keep
it is a checker finding. -/
def WF9 (ρ : Assignment) (st : MState) : Prop :=
  ∀ p ∈ allPos st.env, (valAt st.env p).outerLoans ≠ [] → ∃ T, MState.posTyM dm C Γ ρ st p = some T

/-- (WF10) D88/D89: every constructor value in Ω records its parameters. A value's meaning then
reads the hint only through a sealed program (`Lemmas.hintFree_of_recorded`), which is what the
substitution lemmas' `HintFree` needs of a borrow's content at [End]. -/
def WF10 (st : MState) : Prop := ∀ v ∈ Env.values st.env, v.anyAtom (Value.bareCtor Γ) = false

/-- (WF11) Types and records hold no loan (docs/27 Lemma 5, "types are hole-free", made a clause;
docs/31 D23, third lead): no stored or deferred type of a binding, no type of an unknown, not the
goal, and no generalisation or η record holds a loan anywhere, a sealed program's holes included.

Three things rest on it and none could be derived before it was a clause. A type and a record are
read at the constant future (`Value.tyS`, `TypedAssignment.neutral`), which is the reading at the
run's future only for a value with no loan. [End] substitutes a loan in Ω's values alone
(`substEnv … false`), so a loan in a type or a record would outlive its borrow. And what survives
a private copy beside the restored Ω is exactly the records and the types of the unknowns created
inside (`restoreKeep`), so with this clause no label issued inside a copy is anywhere in the state
after it (`Steps/Sim.lean`, `private_copy_no_label`): prerequisite (b) of the migration.

`types_holeFree_stmt` used to state the types' half as a consequence of `Good` (and for LIVE
loans only), which `Good` did not imply. -/
def WF11 (st : MState) : Prop :=
  (∀ (f i : Nat) (b : Binding), st.env[f]?.bind (fun fr => fr.binds[i]?) = some b →
    (∀ T, b.ty = some T → ∀ l, T.hasLoan l = false) ∧
    (∀ P ws j, b.lazyTy = some (P, ws, j) → ∀ l, P.hasLoan l = false ∧ ∀ w ∈ ws, w.hasLoan l = false)) ∧
  (∀ T ∈ st.absTy.toList, ∀ l, T.hasLoan l = false) ∧
  (∀ G, st.goal = some G → ∀ l, G.hasLoan l = false) ∧
  (∀ n σ, (n, σ) ∈ st.neutrals → ∀ l, n.hasLoan l = false) ∧
  (∀ σ v, (σ, v) ∈ st.etaRefs → ∀ l, v.hasLoan l = false)

/-- (WF12) Under a live fill, only borrows filled there: at a position holding a live borrow's
fill at a path, every live borrow with a site at that path or below it has a fill at that same
path. So an access that passes the fill on its way to one field (the checker's `accessPath` at an
instance, where a mark is transparent) and an access of the filled place whole (the reference's
access of the shortest lent prefix, and the checker's at the generic call, where the field does
not exist) end the same borrows (`AccessAbsorb.AbsorbInv`'s second half). Read off the checker (a
returned borrow's mark wraps the whole lent place, with the reborrow's loan inside it; when a
borrow ends, its mark passes to EVERY live borrow its content was lent onward to, at the same
place; reaching below a mark ends its borrow first, D90; lending a place whole ends the borrows of
its parts), NOT proved preserved: every step's `Good` conclusion owes it. Tested by the sweep
(`lake exe sweep`, with `--probes`; docs/31 D39).

Its history (each form kept as the record). As first written (docs/31 D29): a site of a live
borrow strictly under a fill of another belongs to a borrow also lent at that fill's place or
above it. Restated after the sweep (D33) to what that sweep measured: at a live fill, no other live
borrow has a site at the fill's path or below it. FALSE since main's D93 (`SweepProbes.TwoParts`,
accepted since: two disjoint parts of a returned borrow's place lent onward; when the returned
borrow is re-pointed, its mark passes to both, so both are filled at the whole place,
`Regress/TwoFills.lean`). This form is what the absorption needs and both states meet. -/
def WF12 (env : Env) : Prop :=
  ∀ k l, liveLoan env k = true → liveLoan env l = true →
    ∀ x ∈ Env.sitesOf env k, x.fill = true → ∀ y ∈ Env.sitesOf env l, y.pos = x.pos →
      (walkKey x.path).isPrefixOf (walkKey y.path) = true →
      ∃ z ∈ Env.sitesOf env l, z.pos = x.pos ∧ walkKey z.path = walkKey x.path ∧ z.fill = true

/-- (WF14) **No live borrow is lent strictly above a moved part** (docs/31 D43): where a position's
value has `⊥` at a path, no live borrow has a site at that position at a strict prefix of the path
(compared step by step, `walkKey`, as the checker's own clauses compare; the reference's `lentPrefix`
compares by `pathKey`, `*` erased, and the two meet in `KeyBridge`, docs/31 D67). [Borrow] rejects a partly moved
place, and a move under a fill reaches the fill first and ends it. Read off the checker and swept
(`Sweep.lean`'s clause (iii), at every `⊥` part of every position), NOT proved preserved. What the
drop at the join needs where the checker's place is `⊥` (`DropOne.lentPrefix_none_of_noop`): the
checker does nothing there, so the reference's access of the lent prefix must do nothing too. -/
def WF14 (env : Env) : Prop :=
  ∀ pos path, (valAt env pos).follow path = some .bot →
    ∀ l, liveLoan env l = true → ∀ x ∈ Env.sitesOf env l, x.pos = pos →
      ∀ k < path.length, walkKey x.path ≠ walkKey (path.take k)

/-- A closure or Π-type recording (D82) a declared type that holds a loan or a mark of `l`. -/
def _root_.Ochr.Value.rdLoan (l : Nat) : Value → Bool
  | .clo _ _ rd | .tPi _ _ rd => Value.anyAtomRd (fun | .loan m | .gloan m _ => m == l | _ => false) rd
  | _ => false

/-- (WF15) **No recorded reading holds a loan or a mark** (docs/31 D46): no closure or Π-type
anywhere in Ω, inside sealed programs and code included, records a declared type holding a loan or
a mark. The checker's `Value.loans` does not walk recorded readings and `Value.hasLoan` does, so
without it a sealed program can be lent (`sitesOf`, by `hasLoan`) where no live-loan scan
(`liveLoansIn`, by `loans`) sees it. (WF11)'s kind of fact, for the readings closures record. Read
off the checker and swept (`Sweep.lean`'s (RD)), NOT proved preserved. -/
def WF15 (env : Env) : Prop := ∀ v ∈ Env.values env, ∀ l, v.anyAtom (Value.rdLoan l) = false

/-- (WF16) **No sealed program reads the hint at a tail** (docs/31 D45, D47): every sealed program
anywhere in Ω ends, on every path, in something whose meaning does not depend on the type it is
read at (`Value.topHintFree`: [Close]'s programs end in a read). What the write of `⊥` beside a
sealed program needs (`mean_updAt_botS`). Read off the checker and swept (`Sweep.lean`'s (H)),
NOT proved preserved. -/
def WF16 (st : MState) : Prop := ∀ v ∈ Env.values st.env, v.anyAtom (fun a => a.isSealed && !a.topHintFree Γ) = false

/-- Well-formedness, part (c) of the main theorem. -/
def WF (ρ : Assignment) (st : MState) : Prop :=
  WF1 st.env ∧ WF2 st.env ∧ WF3 st.env ∧ WF4 st.env ∧ WF6 st ∧ WF7 dm C Γ ρ st ∧ WF8 st ∧ WF9 dm C Γ ρ st ∧
  WF10 Γ st ∧ WF11 st ∧ WF12 st.env ∧ WF14 st.env ∧ WF15 st.env ∧ WF16 Γ st

/-! ## Typed assignments, typed futures, membership -/

/-- A future is typed for Ω: each live borrow's final content lies in the content type of its
holder's declared borrow type (`⟦&T⟧ = ⟦T⟧`). -/
def TypedFuture (ρ : Assignment) (st : MState) (φ : Future) : Prop :=
  ∀ p l, Env.shape st.env p = some l → ∀ T, MState.posTyM dm C Γ ρ st p = some T → φ l ∈ₛ[dm.read] T


/-- An assignment of Ω (docs/18 Def. "assignment"): each referenced `σ` means an element of `⟦Δ(σ)⟧_ρ`, and
the path condition holds: each generalisation record `n := σ` in force says `ρ σ = ⟦n⟧_ρ` (a
generalised program is hole-free, docs/27 Lemma 5, so its meaning does not read the future),
each η-refinement `σ := C(σ̄)` says the same of its constructor value, and so does each [Split]
refinement `σ := r` made in this world (`refs`).

The last was missing: `refs` was taken for an input of decisions only, but the checker reads it
back into the state (`canonNeutral`, `recordedNeutral`: a program generalised in this world is
its unknown with the refinements since substituted), so without it a `Good` state could replace
a program by a value meaning something else (`Regress/RefsPathCond.lean`). -/
structure TypedAssignment (ρ : Assignment) (st : MState) : Prop where
  mem : ∀ σ, st.Refd σ → σ < st.absTy.size → ρ σ ∈ₛ[dm.read] MState.absTyM dm C Γ ρ st σ
  neutral : ∀ n σ, (n, σ) ∈ st.neutrals →
    ρ σ = Value.mean dm C Γ ρ (fun _ => .err) (.plain (MState.absTyM dm C Γ ρ st σ)) n
  eta : ∀ σ v, (σ, v) ∈ st.etaRefs →
    ρ σ = Value.mean dm C Γ ρ (fun _ => .err) (.plain (MState.absTyM dm C Γ ρ st σ)) v
  refs : ∀ σ r, (σ, r) ∈ st.refs →
    ρ σ = Value.mean dm C Γ ρ (fun _ => .err) (.plain (MState.absTyM dm C Γ ρ st σ)) r

/-- Membership, part (b) of the main theorem: under every typed future, every position with a
stored type holds a (possibly partly moved) member of it; Δ's types and the goal are types. -/
structure Membership (ρ : Assignment) (st : MState) : Prop where
  pos : ∀ φ, TypedFuture dm C Γ ρ st φ →
    ∀ p T, MState.posTyM dm C Γ ρ st p = some T → DataModel.pmem dm Γ (Env.mean dm C Γ ρ φ st.env p) T
  absTy : ∀ σ, st.Refd σ → σ < st.absTy.size → (MState.absTyM dm C Γ ρ st σ).level.isSome
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
  TypedFuture dm C Γ ρ st φ ∧ ∀ l T, (l, T) ∈ fl → φ l ∈ₛ[dm.read] T

/-- `Membership` under futures typed at the flight too. -/
structure MembershipF (ρ : Assignment) (st : MState) (fl : Flight) : Prop where
  pos : ∀ φ, TypedFutureF dm C Γ ρ st fl φ →
    ∀ p T, MState.posTyM dm C Γ ρ st p = some T → DataModel.pmem dm Γ (Env.mean dm C Γ ρ φ st.env p) T
  absTy : ∀ σ, st.Refd σ → σ < st.absTy.size → (MState.absTyM dm C Γ ρ st σ).level.isSome
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
