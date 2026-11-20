import Ochr.Meaning.Steps.Knot

/-!
# The knot of [Def]: the induction on the bound (docs/31 D73, D79)

`checkDef` pushes a function's global before it checks the body, so that recursive calls find it;
`CtxOk` then asks of that global only membership below a bound (`RunCtx.cur`, `MemBelow`), and the
function's membership comes from an induction on the bound: from the function being good below `b`,
the body's generic run (the checker accepted it) makes the stage `b + 1` good at arguments of rank
`b`; so the guarded fixpoint (at arguments of rank `r`, the stage `r + 1`) is good at every member
argument, and a closure whose function is total and good is a member of its type.

Here: the induction itself, abstractly (`stages_total`, proved), and the data layer's facts it
takes as named statements: the closure lemma's two halves (`closure_mem_of_total`, `closure_apply`)
and the rank's strict decrease (`semRank_part`, R2). The spine's leaves and the assembly of
`step_member_fix` are in `Consistency.lean`.
-/

namespace Ochr.Meaning.Steps

open Ochr Ochr.Meaning

/-- **The induction on the bound** (proved; docs/31 D73 item 2). If at every bound `b`, from the
guarded fixpoint (`stage (rank a + 1) a`) being good at member arguments of rank below `b`, the stage
`b + 1` is good at member arguments of rank `b`, then the fixpoint is good at every member argument
(each has a finite rank). -/
theorem stages_total {A O : Type _} (stage : Nat → A → Option O) (rank : A → Nat) (mem : A → Prop)
    (good : A → O → Prop)
    (hstep : ∀ b, (∀ a, mem a → rank a < b → ∃ o, stage (rank a + 1) a = some o ∧ good a o) →
      ∀ a, mem a → rank a = b → ∃ o, stage (b + 1) a = some o ∧ good a o) :
    ∀ a, mem a → ∃ o, stage (rank a + 1) a = some o ∧ good a o := by
  have key : ∀ b a, mem a → rank a < b → ∃ o, stage (rank a + 1) a = some o ∧ good a o := by
    intro b
    induction b with
    | zero => intro a _ h; exact absurd h (Nat.not_lt_zero _)
    | succ b ih =>
      intro a ha h
      rcases Nat.lt_succ_iff_lt_or_eq.mp h with h | h
      · exact ih a ha h
      · rw [h]; exact hstep b ih a ha h
  intro a ha
  exact key (rank a + 1) a ha (Nat.lt_succ_self _)

/-! ### Owed by the data layer (named statements; docs/31 D73, the lane's answer, D79) -/

/-- **The closure lemma, membership half** (owed by the data layer, at any closure meaning, captures
included): a closure whose function is defined and good at every member argument is a member of its
code. For the levels the run builds (`piSort` gives `0` to `3`). -/
theorem closure_mem_of_total (R : DataRead) (l : Nat) (φ : Future) (ds : List PiDom) (out : PiCod)
    (g : List Sem → Option BodyOut) (hl : l ≤ 3)
    (htot : ∀ args, DomMembers R ds args → ∃ o, g args = some o ∧ OutGood R ds out args o) :
    closureAt R l φ ds out g ∈ₛ[R] piTyAt R l ds out := by
  sorry

/-- **The closure lemma, application half** (owed by the data layer): a closure applied at member
arguments where its function is defined is that function's result (what a call reads, `callOf`; the
borrow arguments' labels fixed to the function's final contents, `callOfL`). What the call step reads
`MemBelow` through. -/
theorem closure_apply (R : DataRead) (l : Nat) (φ : Future) (ds : List PiDom) (out : PiCod)
    (g : List Sem → Option BodyOut) (hl : 1 ≤ l ∧ l ≤ 3) (args : List Res) (s : SState) (o : BodyOut)
    (hmem : DomMembers R ds (args.map (·.1))) (hg : g (args.map (·.1)) = some o) (hdata : out.isRef = false) :
    ∃ s', callOf R (closureAt R l φ ds out g, .plain (piTyAt R l ds out)) args s =
      some ((o.result, .plain (out.cod (args.map (·.1)))), s') := by
  sorry

/-- A part of a meaning: a field of a constructor value, a number's predecessor, and so on down. -/
inductive SemPart (dm : DataModel) (Γ : List IndDecl) : Sem → Sem → Prop
  | field {c i : Nat} {s f : Sem} {T : TyS} (h : Sem.stepField dm Γ c i s = some (f, T)) : SemPart dm Γ f s
  | pred (n : Nat) : SemPart dm Γ (.el0 Nat n) (.el0 Nat (n + 1))
  | trans {a b c : Sem} : SemPart dm Γ a b → SemPart dm Γ b c → SemPart dm Γ a c

/-- **(R2) A part has a strictly smaller rank** (owed by the data layer: `semHeight_field_lt`, through
every declaration and nesting, as a function of the meaning alone; `semRank` is the height after the
port). What `recDecreases_stmt` turns [Rec]'s syntactic check into. -/
theorem semRank_part (dm : DataModel) (Γ : List IndDecl) {a b : Sem} (h : SemPart dm Γ a b) :
    semRank dm Γ a < semRank dm Γ b := by
  sorry

/-! ### The [Rec] link (the spine's; docs/31 D73 item 3) -/

/-- **[Rec], semantically** (leaf): [Rec] (`Machine.recCheck`) accepts a recursive call when the
decreasing argument `u` is a strict subterm of the parameter's entry unknown `σ` as the path
conditions expand it (`expandRefs`). At a good state, under an assignment that meets the path
conditions (`TypedAssignment.refs`) and is typed (so the entry unknown's value is a constructor value
of its type, whose fields its expansion's fields mean), `u`'s meaning is a part of `ρ σ`; with
`semRank_part` its rank is smaller, which is what the induction on the bound needs at a recursive
call. (The lane's answer: this holds only under typed assignments satisfying the records, which
`Good` gives.) -/
theorem recDecreases (K : RunCtx) (ρ : Assignment) (ψ : Future) (st st' : MState) (σ : Nat) (e u : Value) (b : Nat)
    (hT : TyS) (hg : Good K.dm K.M K.Γ ρ st) (hctx : CtxOk K ρ st)
    (he : Runs (Ochr.expandRefs st.refs (.abs σ)) st b e st')
    (hu : u ∈ Ochr.strictSubterms e) :
    SemPart K.dm K.Γ (meanV K ρ ψ hT u) (ρ σ) := by
  sorry

end Ochr.Meaning.Steps
