import Ochr.Meaning.DataModel.Exists.Knot.Grammar
import Ochr.Meaning.DataModel.Exists.Knot.HintFree
import Ochr.Meaning.DataModel.Exists.RunLemmas
import Ochr.Meaning.RunCongr
import Ochr.Test
import Ochr.Examples.Nat
import Ochr.Examples.List
import Ochr.Examples.Logic

/-!
# Value arguments of a nested occurrence, and their hints (exists7, exists8; docs/34 §18.10)

The grammar had a condition (B2) on a value argument of a nested occurrence: the reference ran it at
its parameter's declared type, which can mention an earlier argument that varies with the knot's
records (`NF (A : Type) (n : Nat) (f : NegF(A, n))` with `DF := LeafF | NodeF(p : NF(DF, 0, ()))`),
and (B2) asked that the hint not vary or that the argument not read it (exists7's weakening). It
excluded `DK` and `DT3` below: a constructor whose parameter is not written, at a hint computed from
the type being declared. Lean accepts both, and so does the checker.

Since docs/31 D172 the reference runs every parameter of `D(ā)` with no hint, as the typed checker
does (`runParams`), so (B2) is gone and all four declarations are in the grammar (the `#guard` below).
What the reference does at `DK`'s bare `Cons(0, Nil[Nat])` with no hint: it solves `Cons`'s parameter
from the fields, as the checker does (`runFields`'s `unifyTyS`, the audit's A9), and computes exactly
what it computed before at the hint `List(Nat)` (`run_cons_noHint`, for every model and context that
declares `List` as the prelude does).

The two neighbours stay rejected: a value argument may not name the type being declared (`DL`,
D36/D71), and a constructor whose parameter no field determines must write it (`DT`, resolution).
-/

open Ochr Ochr.Test

namespace Ochr.Meaning.DataModel.Exists.HintShapes

ochr HintShapes uses Logic, Nats, Lists {
  inductive Void0 : Type
  def NegF (X : Type) (b : Nat) : Type := (match b { Z => Unit, S(k) => Π(x : X). Void0 })
  inductive NF (A : Type) (n : Nat) (f : NegF(A, n)) := MkNF(y : A)
  -- the checker's own example (D121's report): `()` does not read its hint
  inductive DF := LeafF | NodeF(p : NF(DF, 0, ()))
  def TK (X : Type) : Type := List(Nat)
  inductive PK (A : Type) (t : TK(A)) := MkPK(y : A)
  -- a constructor with its parameters written does not read its hint
  inductive DK2 := LK2 | NK2(p : PK(DK2, Nil[Nat]))
  -- a constructor with its parameter left to the hint, the hint `TK(DK)`: outside the grammar
  inductive DK := LK | NK(p : PK(DK, Cons(0, Nil[Nat])))
  def TF (X : Type) (b : Nat) : Type := (match b { Z => List(Nat), S(k) => List(X) })
  inductive PF (A : Type) (n : Nat) (t : TF(A, n)) := MkPF(y : A)
  inductive DT3 := LT3 | NT3(p : PF(DT3, 0, Cons(0, Nil[Nat])))
  -- the neighbours: a value argument naming the type, a parameter no field determines
  inductive Pl (A : Type) (l : List(A)) := MkPl(y : A)
  reject inductive DL := LeafL | NodeL(p : Pl(DL, Nil[DL]))
  inductive Tg (A : Type) := MkTg(n : Nat)
  inductive PT (A : Type) (t : Tg(A)) := MkPT(y : A)
  reject inductive DT := LT | NT(p : PT(DT, MkTg(3)))
}

#guard (Ochr.Test.run "HintShapes" HintShapes).rejectedWith [
  ("DL", "field p of NodeL : Pl(DL, Nil[DL]): fields are first-order data"),
  ("DT", "cannot infer the parameter A of MkTg")]

def prog : Surface.Program := libOf {} 2000000 HintShapes ++ HintShapes.decls

def items : List Item :=
  prog.filterMap fun d => match Surface.resolveProgram prog d with
    | .ok it => some it
    | .error _ => none

open Ochr.Meaning.DataModel.Exists.Knot in
-- the grammar holds at each declaration the checker stores (`DF`, `DK2`, `DK`, `DT3`); `NF`'s, `PK`'s and
-- `PF`'s first parameter is stored nestable
#guard let inds := (globalsAfter {} items).2
  let ok (n : String) : Option Bool := (inds.find? (·.name == n)).map fun d => decide (GrammarOk inds d)
  let nest (n : String) : Option (List Bool) := (inds.find? (·.name == n)).map (·.nestable)
  [ok "DF", ok "DK2", ok "DK", ok "DT3"] == [some true, some true, some true, some true] &&
    [nest "NF", nest "PK", nest "PF"] == [some [true, false, false], some [true, false], some [true, false, false]]

/-! ## What the reference does at `DK`'s bare `Cons(0, Nil[Nat])`, with no hint -/

/-- `Cons(0, Nil[Nat])` with `Cons`'s parameter not written, as the checker stores it in `DK`'s field
type `PK(DK, Cons(0, Nil[Nat]))` (pinned by the `#guard` below). -/
def consT (x x' : Hint) : Term := .ctor "List" 1 x [] [.zero, .ctor "List" 0 x' [.nat] []]

-- `DK`'s stored field type is `PK(DK, consT _ _)`, and `List` is declared as the theorem below assumes
#guard let inds := (globalsAfter {} items).2
  (match (inds.find? (·.name == "DK")).bind (·.ctors[1]?) with
    | some (_, [(_, Term.tind "PK" [Term.tind "DK" [], Term.ctor "List" 1 _ [] [Term.zero, Term.ctor "List" 0 _ [Term.nat] []]])]) =>
      true
    | _ => false) &&
  (match inds.find? (·.name == "List") with
    | some L => L.params.length == 1 && L.sort == 1 &&
        fieldTerm L 1 0 == some (.place (.var 0)) && fieldTerm L 1 1 == some (.tind "List" [.place (.var 0)])
    | none => false)

section
open Ochr.Meaning Ochr.Meaning.DataModel.Exists.Knot

/-- A constructor's fields that do not read their hints run the same whatever record the hint gave. -/
theorem runFields_rh_free (K : RunCtx) (ρ : Assignment) (φ : Future) (stmt : Bool) (d : IndDecl) (c : Nat) :
    ∀ (args : List Term) (i : Nat) (rh rh' : Option Rec) (sol : List (Option Sem)) (earlier : List Sem)
      (s : SState), (∀ a ∈ args, hintFreeB K.Γ a = true) →
    runFields K ρ φ stmt d c i rh sol earlier args s = runFields K ρ φ stmt d c i rh' sol earlier args s
  | [], _, _, _, _, _, _, _ => rfl
  | a :: as, i, rh, rh', sol, earlier, s, ha => by
    simp only [runFields]
    have e : ∀ H, runT K ρ φ false H a = runT K ρ φ false (.plain TyM.err) a :=
      fun H => runT_hintFree K ρ φ H _ a (ha a (List.mem_cons_self ..))
    apply SM.bind_congr (SM.stmtIf_congr ((congrFun (e _) _).trans (congrFun (e _) _).symm))
    intro r s₁ _
    apply SM.bind_congr (runFields_rh_free K ρ φ stmt d c as _ _ _ _ _ s₁ (fun b h => ha b (List.mem_cons_of_mem _ h)))
    intro _ _ _; rfl

theorem fillParam_solved {np j : Nat} {v : Sem} {sol : List (Option Sem)} (h : ∀ o ∈ sol, o.isSome = true) :
    fillParam np j v sol = sol := by
  unfold fillParam
  split
  · rename_i hc
    by_cases hl : np - 1 - j < sol.length
    · have := h _ (List.getElem_mem hl)
      simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hl] at hc
      rw [hc.2] at this; cases this
    · exact List.set_eq_of_length_le (by omega)
  · rfl

theorem unify_list_solved (dm : DataModel) (R : TyS) (v : Sem) :
    unifyTyS dm 1 (.tind "List" [.place (.var 0)]) R [some v] = [some v] := by
  have h : ∀ o ∈ [some v], o.isSome = true := by simp
  simp only [unifyTyS, unifyArgsTyS]
  repeat' split
  all_goals first | rfl | exact fillParam_solved h

/-- The fields `0, Nil[Nat]` of `Cons` solve its parameter to `Nat`, whatever the record the hint gave. -/
theorem runFields_cons_sol (K : RunCtx) (ρ : Assignment) (φ : Future) (L : IndDecl) (hLp : L.params.length = 1)
    (hf0 : fieldTerm L 1 0 = some (.place (.var 0))) (hf1 : fieldTerm L 1 1 = some (.tind "List" [.place (.var 0)]))
    (rh : Option Rec) (x' : Hint) (s s₂ : SState) (fs : List Sem) (sol : List (Option Sem))
    (h : runFields K ρ φ false L 1 0 rh [none] [] [.zero, .ctor "List" 0 x' [.nat] []] s = some ((fs, sol), s₂)) :
    sol = [some (.ty TyM.nat)] := by
  simp only [runFields, SM.stmtIf, Bool.false_and, Bool.false_eq_true, if_false, Bind.bind,
    RunLemmas.runT_zero, hf0, hf1, hLp] at h
  have hu0 : unifyTyS K.dm 1 (.place (.var 0)) (TyS.plain TyM.nat) [none] = [some (.ty TyM.nat)] := by
    simp [unifyTyS, fillParam, TyS.plain, TyM.isErr, TyM.nat]
  simp only [hu0, unify_list_solved] at h
  revert h
  generalize runT K ρ φ false _ _ s = r
  intro h
  cases r with
  | none => cases h
  | some r => simp only [pure, Option.some.injEq, Prod.mk.injEq] at h; exact h.1.2.symm

/-- **At no hint, the reference runs `DK`'s bare `Cons(0, Nil[Nat])` exactly as it ran it at the hint
`List(Nat)`**, in every model and context that declares `List` as the prelude does: the record the
hint used to give is the one the fields give (`0` runs at `Nat`, which solves `Cons`'s parameter,
`runFields`'s `unifyTyS`), and the fields do not read their hints. So the run succeeds where it
succeeded before, and the value no longer depends on the knot's records. -/
theorem run_cons_noHint (K : RunCtx) (ρ : Assignment) (φ : Future) (L : IndDecl) (x x' : Hint)
    (hL : K.Γ.find? (·.name == "List") = some L) (hLp : L.params.length = 1) (hLs : L.sort = 1)
    (hf0 : fieldTerm L 1 0 = some (.place (.var 0))) (hf1 : fieldTerm L 1 1 = some (.tind "List" [.place (.var 0)]))
    (s : SState) :
    runT K ρ φ false (.plain TyM.err) (consT x x') s =
      runT K ρ φ false (.plain (K.dm.tyM L [.ty TyM.nat])) (consT x x') s := by
  unfold consT
  rw [runT, runT]
  refine SM.erasedIf_congr ?_
  simp only [hL]
  apply SM.bind_congr rfl
  intro psM s₁ h1
  have hps : psM = [] ∧ s₁ = s := by
    simp only [runParams, pure, Option.some.injEq, Prod.mk.injEq] at h1; exact ⟨h1.1.symm, h1.2.symm⟩
  obtain ⟨rfl, rfl⟩ := hps
  have hname : L.name = "List" := by simpa using List.find?_some hL
  have hpe : L.params.isEmpty = false := by
    rw [Bool.eq_false_iff]; intro h; rw [List.isEmpty_iff] at h; rw [h] at hLp; cases hLp
  have hdR : (TyS.plain (K.dm.tyM L [Sem.ty TyM.nat])).data = some ("List", K.dm.recOf L [.ty TyM.nat]) := by
    simp [TyS.data, TyS.plain, DataModel.tyM, DataModel.tyR, hLs, TyM.dataRec?, hname]
  have hdE : (TyS.plain TyM.err).data = none := rfl
  simp only [hpe, hdR, hdE, List.isEmpty_nil, Bool.not_true, Bool.false_or, Bool.false_eq_true, if_false, if_true, hLp,
    hLs, List.replicate_one]
  apply SM.bind_congr (runFields_rh_free K ρ φ _ L 1 _ 0 _ _ _ [] s₁ (by simp [hintFreeB]))
  rintro ⟨fs, sol⟩ s₂ h2
  have hsol := runFields_cons_sol K ρ φ L hLp hf0 hf1 none x' s₁ s₂ fs sol h2
  subst hsol
  rfl

end

end Ochr.Meaning.DataModel.Exists.HintShapes
