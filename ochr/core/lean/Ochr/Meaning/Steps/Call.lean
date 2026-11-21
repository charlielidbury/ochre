import Ochr.Meaning.Steps.CallAsm

/-!
# Step lemmas, calls: `callFn`, `runBody`, `closeCall`, `callType`, `recCheck` (milestone 3)

A call in the checker runs the callee's body (`runBody`) or, when the body is stuck, closes off
(`closeCall`, three rows). The reference run applies the callee's meaning (`callOf`). So:
* a direct call is *below* the reference (the body's run is below the function's meaning, by the
  induction hypothesis on the body: docs/18 "a call of a closure, run directly");
* closing off is *exact*: a sealed program means its run, which is the reference's call
  (docs/18 (C1)–(C9)); the row for `&T` is `callOf`'s `.ref` case; η at `Unit` is membership
  (`⟦f⟧(ā) ∈ ⟦Unit⟧`, the one-element set);
* `callType`/`declCallType` compute the codomain at the arguments, the reference's `TyS` of the
  result;
* `recCheck`'s accepting direction is the stabilisation of the stages (the semantic [Rec]).
-/

namespace Ochr.Meaning.Steps

open Ochr.Meaning

section
variable (K : RunCtx) (ρ : Assignment) (φ : Future)

/-- A direct call (`callFn`, untyped or typed): below the reference's `callOf` on the callee's
meaning, and `Good` kept. The arguments are loan-free (WF5, `ArgsLoanFree`). -/
theorem callFn_step (fuel : Nat) (ih : StepsIHBelow fuel) : callFn_step_stmt K ρ φ (fuel + 1) :=
  callFn_step_asm K ρ φ fuel ih

/-- Running a body (`runBody`): the frame pushed with the captures and parameters, the body run,
the frame popped: below the function's meaning applied (the induction hypothesis on the body). -/
theorem runBody_step (fuel : Nat) (ih : StepsIHBelow fuel) : runBody_step_stmt K ρ φ (fuel + 1) :=
  runBody_step_asm K ρ φ fuel ih

/-- [Close] (`closeCall`), every row: exact against `callOf`. The result is a sealed program (or
`()` at a declared `Unit`, or a borrow of one), and each lent place a fill: both mean what the
reference's call gives them, since a sealed program means its run. -/
theorem closeCall_step (fuel : Nat) (ih : StepsIHBelow fuel) : closeCall_step_stmt K ρ φ (fuel + 1) :=
  closeCall_step_asm K ρ φ fuel ih

/-- [Call-type] (`callType`, `declCallType`): the codomain at the arguments is the reference's
result type. -/
theorem callType_step (fuel : Nat) (ih : StepsIHBelow fuel) : callType_step_stmt K ρ φ (fuel + 1) := by
  sorry

/-! ### The obligations of the call steps (docs/31 D62)

The assemblies (`callFn_step`, `runBody_step`, `closeCall_step`, `Subst.nfSealed_step`) are not yet
written; the obligations below are the risk-bearing leaves they rest on, stated first. The
bookkeeping leaves (the frame pushed and popped against `CallRef.callFrame`/`popCallFrame`, the
lending marks and their end, the call's type and the body's and arguments' hints, η at `Unit`,
`catchStuck` restoring the state, the class of a call that is neither a statement nor erased) are
named in docs/31 D62 and get their statements with the assemblies. -/

/-- **The in-place run of a known callee's body is the application of its meaning** (the reference
alone; docs/31 D62, D70; open). `runCallRef` runs the call as the checker's `callFn` does (main's D99):
it reserves the result's label and lends it where the borrow arguments lent, pushes the callee's frame
on the caller's state, runs the body, pops the frame (every borrow it holds or the body made ends but
the returned one), and renames the returned borrow into the reserved label. `callOf` applies the
closure's meaning, built from the body's run in the closure's own frame (labels from `0`, a cell per
borrow parameter), and fixes each lent place's final content. They give the same result, its label
included (both the reserved fresh label), and every checker state related to the one is related to
the other under the same renaming. For a body that holds no `Id`, or a call with no borrow argument:
there the frame property needs no hypothesis (`FrameProp.run_frame`); the other case is
`callOf_inPlace_rel`, at a call related to the checker's.

What it rests on, none proved: the frame property with the renaming of labels
(`FrameProp.run_frame`, whose special case is `run_counter_indep`); the `self` binding (in place the
callee's reading, in the closure's meaning `err` (non-recursive: a body that never reads `self`) or
the stage's closure (recursive: the fixpoint equation under [Rec], which needs every recursive call
to decrease, `hacc`, and the `.fix` clause's stages, `RunCongr.fixStage`)); the pop against the
closure's ends and its cells (`popCallFrame` ends what `bodyAt` ends, and the cells, read after, are
what `callOf` writes into the lent places, `FrameRel.lowerVal` at the end); the reservation and the
renaming against `callOf`'s fresh label (`SState.endInto`). Checked on `Inc` and `Id1`
(`Regress/CallInPlace.inc_agree`, `Regress/CallInPlaceD99.id1_inPlace_typed`). -/
theorem callOf_inPlace (cs : List Value) (t : Term) (rd : List (DeclInfo × Value)) (fres : Res)
    (as : List Res) (s s₁ : SState) (r₁ : Res)
    (hf : run K ρ φ (.plain .err) (.val (.clo cs t rd)) s = some (fres, s))
    (hacc : ∃ st fuel st', Runs (Ochr.checkFix fuel (.clo cs t rd) [] t) st fuel () st')
    (hid : t.idFree = true ∨ ∀ a ∈ as, a.2.label = none)
    (hin : runCallRef K ρ φ fres cs t rd as s = some (r₁, s₁)) :
    ∃ s', callOf K.dm.read fres as s = some (r₁, s') ∧
      ∀ (st : MState) (π : Nat → Nat), Good K.dm K.M K.Γ ρ st → Rel K ρ φ π st s₁ → Rel K ρ φ π st s' := by
  sorry

/-- **The in-place call is `callOf`, at a call related to the checker's** (docs/31 D70; open), for every
body: `callOf_inPlace` where the body holds no `Id` or no argument is a borrow; otherwise the same
proof with the frame property at each `Id` (`FrameProp.run_frame_obs`), whose hypotheses the checker's
run gives: at each observation the parameters' final contents are whole members (no borrow ends over
a moved-out content, main's D98; the body is typed), and the caller's places determine them (each
borrow argument is lent where its final content is read directly, or through an earlier call's
backward function, injective on members). -/
theorem callOf_inPlace_rel (fuel : Nat) (st st' : MState) (fv : Value) (cs : List Value) (t : Term)
    (rd : List (DeclInfo × Value)) (ws : Array Value) (B : Option Value) (v : Value)
    (hg : Good K.dm K.M K.Γ ρ (st.withTemps (fv :: ws.toList))) (hctx : CtxOk K ρ st)
    (s : SState) (π : Nat → Nat) (hs : Rel K ρ φ π (st.withTemps (fv :: ws.toList)) s)
    (hfix : fv = .clo cs t rd ∨ ∃ n, fv = .gfn n ∧ Runs (Ochr.fixOf fv) st 0 (cs, t, rd) st)
    (fres : Res) (hf : run K ρ (fun l => φ (π l)) (.plain .err) (.val fv) s = some (fres, s))
    (as : List Res) (has : ArgsAgree K ρ φ π ws as)
    (bh : Nat) (h : Runs (Ochr.runBody fuel fv cs t rd ws B) st bh v st')
    (r₁ : Res) (s₁ : SState) (hin : runCallRef K ρ φ fres cs t rd as s = some (r₁, s₁)) :
    ∃ s', callOf K.dm.read fres as s = some (r₁, s') ∧
      ∀ (st'' : MState) (π' : Nat → Nat) (K' : RunCtx) (ρ' : Assignment), K'.dm = K.dm → K'.D = K.D →
        Good K'.dm K'.M K'.Γ ρ' st'' → Rel K' ρ' φ π' st'' s₁ → Rel K' ρ' φ π' st'' s' := by
  sorry

/-- **The nested run of a re-normalised sealed program, for a program with no hole** (`nfSealed`'s
`eval fuel' false t` on the state with an empty environment; docs/31 D62, D63). Its result means the
sealed program, under an assignment extending `ρ` at the unknowns it creates, and the state
`restoreKeep` makes of it is `Good`.

Stated for a program holding no loan (`hfree`), under plain `Good`: what both outcomes of the lead's
question need (docs/31 D63). With a hole (a live borrow's loan inside the program) the nested run
binds or writes it, and its state holds a loan outside any sealed program whose borrow it does not
hold, which (WF2) forbids and no typed future covers; either the checker never runs such a program
(main's D97, being assessed) or the invariant types the holes (D62's relative invariant). A
program with no hole runs from a state with an empty environment and the outer tables, which is
`Good` with the outer assignment, and every state of its run holds only the loans of borrows it made.
What it rests on: the induction hypothesis (`eval_step_stmt`) at the nested start, related to the
reference's `emptyState` at the checker's counter (`Rel.start`'s analogue), then the counter lemma
(`run_counter_indep`: the meaning runs from `0`), the untyped run (`hok`, docs/31 D62 item 4), and
`restoreKeep` keeping only names, the new unknowns' types and records. Not attempted. -/
theorem nestedRun_sim (fuel : Nat) (ih : StepsIHBelow fuel) (st st₁ : MState) (t : Term)
    (v : Value) (T? : Option Value) (hint : TyS)
    (hg : Good K.dm K.M K.Γ ρ st) (hctx : CtxOk K ρ st)
    (hfree : t.loans = []) (htf : Term.tailHintFree K.Γ t = true)
    (hok : ∀ ψ, (runT K ρ ψ false hint t (emptyState 0)).isSome) (hD : DecTab K.D st₁)
    (bh : Nat) (h : Runs (Ochr.eval fuel false t none)
      { st with env := #[{}], obsFrame := none, depth := st.depth + 1 } bh (v, T?) st₁) :
    NestedOut K ρ st st₁ t v hint := by
  refine nestedRun_sim_asm K ρ fuel ih st st₁ t v T? hint hg hctx hfree htf (fun ψ => ?_) hD bh h
  -- the induction hypothesis's run is at the empty hint and the outer counter: the same success
  -- (a tail-hint-free text runs alike at every hint; the counter lemma)
  have e1 := run_hintIndep K ρ ψ t htf hint (hintM K ρ none) (emptyState 0)
  have e2 := run_counter_indep K ρ ψ (hintM K ρ none) t [] 0 st.nextLoan (by simp) (by simp)
  have h0 := hok ψ
  have h1 : (run K ρ ψ (hintM K ρ none) t (emptyState 0)).isSome := by
    have := congrArg Option.isSome e1; simp only [Option.isSome_map] at this; rw [← this]; exact h0
  have h2 : (run K ρ ψ (hintM K ρ none) t (stateOf st.nextLoan [])).isSome := by
    have := congrArg Option.isSome e2; simp only [Option.isSome_map] at this
    rw [← this]; exact h1
  exact h2

/-! The text `closeCall` seals, as its local definitions build it (`wrapL`, `C`, `cellTerm`,
`cell`): the borrow arguments `(i, ℓᵢ, uᵢ)`, each content in a cell `cⱼ`, the call with `&cⱼ` for
each borrow argument and the value for the others, its head marked. -/

/-- The borrow arguments, with their positions, labels and contents. -/
def closeBs (ws : Array Value) : List (Nat × Nat × Value) :=
  (ws.toList.zipIdx).filterMap fun (w, i) => match w with
    | .borrow l u => some (i, l, u)
    | _ => none

/-- Argument `i` of the sealed call under `d` more binders: `&cⱼ` or the value. -/
def closeArgT (ws : Array Value) (d i : Nat) : Term :=
  match (closeBs ws).findIdx? (·.1 == i) with
  | some j => .borrow (.var (d + (closeBs ws).length - 1 - j))
  | none => .val ws[i]!

/-- The sealed call, its head marked (C5). -/
def closeC (fv : Value) (ws : Array Value) (d : Nat) : Term :=
  .call (.val fv) ((List.range ws.size).map (closeArgT ws d)) true

/-- Cell `cⱼ`'s initialiser: the content, at its declared type where the call has it (D82). -/
def closeCell (tys : Array (Option Value)) (i : Nat) (u : Value) : Term :=
  match tys[i]? with
  | some (some (.tRef T)) => .ascribe (.val u) (.val T)
  | _ => .val u

/-- The cells bound around `body`. -/
def closeWrap (ws : Array Value) (tys : Array (Option Value)) (body : Term) : Term :=
  ((closeBs ws).zipIdx).foldr (fun ((i, _, u), j) acc => .letIn ⟨s!"c{j + 1}"⟩ (closeCell tys i u) acc) body

/-- Cell `cⱼ` read under `d` more binders. -/
def closeCellAt (ws : Array Value) (d j : Nat) : Term := .place (.var (d + (closeBs ws).length - 1 - j))

/-- **[Close]'s sealed programs mean the reference's call** (borrow-free codomain; docs/31 D62,
risk-bearing): the result program `⌈L; C⌉` means `callOf`'s result, and each fill `⌈L; C; peek cⱼ⌉`
means what `callOf` fixes its borrow argument's label to. Both run from the empty state: the cells
bound to the contents, `&cⱼ` at fresh labels, the call by the same `callOf` on the same meanings
(the head and the other arguments are loan-free values, which mean the same in every state), and
`peek cⱼ` reads the cell after the call fixed its label. Attacked on one instance before
(`Attack/CloseCall*.lean`, the `&T` row with one borrow argument: both halves proved); the general
form, and the `&T` row (the result `borrow_k ⌈L; let r = C; peek *r⌉`, the fills
`⌈L; let r = C; *r := loan_k; peek cⱼ⌉`, against `callOf`'s forward value and backward function at
the final content of `k`), are not attempted. -/
theorem closeCall_means_data (fv : Value) (ws : Array Value) (tys : Array (Option Value)) (fres : Res)
    (as : List Res) (s s' : SState) (r : Res)
    (hf : ∀ s₀, run K ρ φ (.plain .err) (.val fv) s₀ = some (fres, s₀))
    (has : ArgsAgree K ρ φ id ws as)
    (hlf : ∀ w ∈ ws.toList, ∀ l : Nat, (match w with | .borrow _ u => u | u => u : Value).hasLoan l = false)
    (hdata : ∃ B, fres.2.m.codAt? K.dm.read (as.map (·.1)) = some (false, B))
    (hcall : callOf K.dm.read fres as s = some (r, s')) :
    meanV K ρ φ r.2 (.sealed (closeWrap ws tys (closeC fv ws 0))) = r.1 ∧
    ∃ fx : List (Nat × Sem), (∀ y ψ, s'.valAt y ψ = s.valAt y (ψ.updList fx)) ∧
      ∀ (j i l : Nat) (u : Value), (closeBs ws)[j]? = some (i, l, u) → ∀ hint,
        (l, meanV K ρ φ hint (.sealed (closeWrap ws tys (.seq (closeC fv ws 0)
          (.prim "peek" [closeCellAt ws 0 j]))))) ∈ fx := by
  sorry

end

end Ochr.Meaning.Steps
