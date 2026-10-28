import Ochr.Test

/-!
# Consistency, stated (the proof is open)

The paper's Conjecture 1, stated against this checker's entry point: an accepted program
without holes, after the library, contains no parameterless declaration of type `False`.
The proof is `sorry`; everything else here is a real definition, and the `#guard`s at the
end show that each part of the statement is needed and that the literal-`False` conclusion
loses nothing.

## The statement, in words

Take any list of surface declarations `q` (inductive types and definitions). Put the
library block `Prelude` (`Pair`, `False`, `True`, `And`) in front of it, as every `ochr`
block has (`Ochr.Test.libOf`). Suppose
* `q` contains no hole: no `?` and no `sorry` (`NoHoles`);
* `checkProgram` (`Ochr/Run.lean`, the entry point the `ochr` command and `Ochr.Test.run` go
  through) gives every declaration the verdict `accepted`, at some fuel (`Accepted`). Its
  verdicts are positional, one per declaration, so the library's and `q`'s are all among
  them. A declaration that is `rejected`, or `undecided` (the checker ran out of fuel or hit
  a depth limit, or the declaration mentions one that did), is not accepted.
Then no declaration of `q` is a definition with no parameters whose declared type is the
library's `False` (`IsFalseConst`).

## Why each part is as it is

* **Holes are the only axioms.** A surface `def` always has a body (`Notation.lean`'s
  `ochr_decl`), so there are no opaque or bodiless definitions to exclude. A hole (`?`, and
  `sorry`, which the notation reads as the same identifier `?`; `Surface.resolve` makes it
  `.prim "hole" []`) is accepted at any type, with a warning: it is an axiom, and
  `holeFalse` below is an accepted closed proof of `False` built from one.
* **Natives are not excluded.** A definition `implemented by "sym"` (K3) has an Ochr body,
  which the checker checks like any other (it only marks it as model code, `GDef.model`).
  Its value in conversion and in proofs is that body's. That the native code computes what
  the body computes is an assumption about compiled programs, not about the logic.
  `abstract`, `unsized` and `copy` declarations restrict where constructors may be used at
  runtime, or how values are read; none adds an inhabitant to any type. So none is excluded.
* **Function parameters are hypotheses, not axioms.** A definition with parameters, such as
  `g : Π(n : Nat). &Nat` in `ReturnedBorrows`, may prove `False` from a hypothesis that is
  impossible. Only parameterless declarations count (`IsFalseConst`), and a closed use of a
  definition with parameters is itself a parameterless declaration one line later.
* **`reject def` needs no hypothesis.** `checkProgram` never reads `SDecl.expectAccept`: it is
  the test runner's expectation, not part of the program. A program whose declarations are
  all accepted is accepted whatever they were expected to do.
* **No hypothesis on names.** The checker rejects a name already declared, whether as a
  definition, a type or a constructor (`Check.declared`, the freshness premises of [Def],
  [Const] and [Ind-decl]). So in an accepted program all names are distinct, the library's
  included, and `q` cannot declare a second `False`. (`Examples/Units.lean` checks the
  rejection, and that `checkProgram` reports each declaration's own verdict, not the verdict
  of an earlier declaration with the same name.)
* **The library in front.** The conclusion names `False`. Without `Prelude`, `q` can declare
  an inhabited type of that name (`noPrelude` below). With it, `False` is the library's
  zero-constructor proposition, and freshness forbids a second.
* **No hypothesis on the `Config`.** `Accepted` checks with the default `Config`. Its only
  fields, `trace` and `derivation`, record what the checker did and decide nothing; there
  are no rule switches, so the default is the rules as they are.
* **A literal `False` loses nothing.** The conclusion is about declarations whose declared
  type is the identifier `False`, not about every type that computes to an empty one. The
  theorem quantifies over all programs, so the stronger form follows. If an accepted program
  had a parameterless `c` whose type computes to an empty type, one more declaration with a
  fresh name would turn it into a literal one, which the theorem forbids. The reductions are
  `def B : False := c` for a type that computes to `False`, such as `Eq(Nat, 0, 1)` (`eqFalse`);
  `match` with the one arm `Intro(l, r) => l` for `False ∧ ⊤` (`andFalse`); and an annotated
  zero-arm match for a user's zero-constructor type, in `Prop` (`voidFalse`) or in `Type`
  (`emptyFalse`). Each `#guard` below checks the reduction step, with a hole standing in for
  the bad constant (for a type in `Type`, the step is checked as a function from it to
  `False`; `emptyFalse` says why). The library's `False` is fixed as the target because `Eq` on distinct
  constructors computes to it (`Machine.mkEqM`).
* **Whole-program acceptance.** "Accepted" means every declaration is accepted, not just
  some. A rejected declaration is not added to the globals, so a later declaration that uses
  it is rejected for a missing name; an undecided one makes every later declaration that
  mentions it undecided too (`checkDefs`). A form about the accepted declarations of a
  partly rejected program is plausible but not stated.
* **Every fuel.** The statement covers every fuel, so a program that needs more than the
  `ochr` command's `2000000` is covered too. There is no separate theorem at a fixed fuel:
  it would be an instance of this one.

## What a proof must confront

1. **The checker is total.** Every definition the checker runs, everything reachable from
   `checkProgram` with the parser included, is a total `def` (`ochr/core/CLAUDE.md`,
   `notes/totality-census.md`). The machine's evaluator recurses on an explicit fuel
   argument, and other recursion is structural or has a measure. So the kernel can unfold
   every step, and the statement is provable in principle; when it had `partial def`s, which
   Lean compiles to opaque constants, it could only be stated. The one exception is
   `Loc.termAddr`, an `opaque` that keys the editor's location table by a term's address.
   `Accepted` never sets `checkProgram`'s `located` flag, so the table stays empty, and every
   use of an address is a lookup in it, which is `none` whatever the key. A proof needs that
   one fact about the table and nothing about `termAddr`. What remains is the proof itself:
   either directly about the machine, or through a relational specification of the paper's
   rules (an inductive typing judgement), a consistency proof for it (the model of the
   paper's §A.6), and a proof that the checker's acceptance implies derivability in it.
2. **Fuel.** Running out of fuel, or past one of the fixed depth limits (`2000`,
   "normalisation depth exceeded" and "call depth exceeded"), is exhaustion: an outcome of
   its own (`Outcome.exhausted`, `Env.exhausted`), which no handler below the verdict
   boundary catches (`Ochr/Catch.lean` catches only *stuck*), and which `checkDefs` reports
   as `undecided`. A catch cannot refund fuel either, since the fuel counter is a state
   layer that a caught failure does not restore. Exhaustion is therefore never a decision,
   and a run that is decided (accepted or rejected) at one fuel takes the same steps, and
   gets the same verdict, at any larger fuel. That monotonicity holds by construction; it is
   not stated or proved here, and the theorem does not need it, since it quantifies over
   every fuel. A prover may want it as a lemma, to fix a fuel large enough for a given run.
3. **Universe strength (Gödel).** A Lean theorem is relative to Lean's own consistency, whose
   strength is ZFC with `n` inaccessible cardinals for every `n < ω`. Lean cannot prove the
   consistency of a theory that interprets Lean, unless Lean is inconsistent. Ochr has an
   impredicative `Prop` and `Type_i` for every `i`, like Lean, but no constructor field may
   be a function or a borrow (`firstOrderTerm`), so it has no W-types. Whether it is as
   strong as Lean is not known. The paper's model sketch (§7.1, §A.6) uses one inaccessible
   per universe level, as Lean's model does. If a proof needs that for every level at once,
   this uniform statement is unprovable in Lean. The realistic forms are then
   (a) bounded levels: add the hypothesis that every `sort l` in `q` has `l ≤ N`, and prove the
       resulting family, one instance for each numeral `N`, each at a fixed Lean universe;
   (b) relative: take a model of the set theory the proof needs as a hypothesis;
   (c) per program.
   The statement here is the uniform target. Its universe bound, if one is needed, is the
   first thing a prover should settle.
4. **Checker versus rules.** This is consistency of the checker. The paper's Conjecture 1 is
   about its rules. The checker is meant to implement exactly the paper's rules, each tagged
   by name (`Rules.lean`, `fire`), and that correspondence is tested, not proved. A proof of
   this statement also rules out implementation bugs, and so is stronger than Conjecture 1
   for the rules the checker implements.
-/

namespace Ochr.Consistency
open Ochr Ochr.Surface Ochr.Test

/-- A surface term contains a hole: the identifier `?`, which is how the `ochr` notation reads
both `?` and `sorry` (`Notation.lean`), and which `Surface.resolve` makes `.prim "hole" []`.
No other identifier is spelled `?`. Total, unlike `STerm.idents`, so that the hypothesis
built from it can be reasoned about. -/
def holeIn : STerm → Bool
  | .ident x => x == "?"
  | .num _ | .unitLit | .top | .sort _ => false
  | .app _ as => as.attach.any fun ⟨a, _⟩ => holeIn a
  | .call f as => holeIn f || as.attach.any fun ⟨a, _⟩ => holeIn a
  | .ctorP _ ps as => ps.attach.any (fun ⟨a, _⟩ => holeIn a) || as.attach.any fun ⟨a, _⟩ => holeIn a
  | .deref t | .proj _ t | .amp t | .split _ t | .loc _ _ t => holeIn t
  | .assign a b | .seq a b | .pair a b | .andI a b | .and a b | .prod a b | .ascribe a b
  | .rewrite _ a b | .arrow a b => holeIn a || holeIn b
  | .letIn _ T t u => (match T with | some A => holeIn A | none => false) || holeIn t || holeIn u
  | .matchGen p arms => holeIn p || arms.attach.any fun ⟨(_, _, t), _⟩ => holeIn t
  | .splitArms _ arms => arms.attach.any fun ⟨(_, _, t), _⟩ => holeIn t
  | .letPat _ _ sc b => holeIn sc || holeIn b
  | .pi bs c => bs.attach.any (fun ⟨(_, A), _⟩ => holeIn A) || holeIn c
  | .fix _ bs r _ b => bs.attach.any (fun ⟨(_, A), _⟩ => holeIn A) || holeIn r || holeIn b
decreasing_by
  all_goals
    first
    | decreasing_tactic
    | (rename_i h; have := List.sizeOf_lt_of_mem h; simp at this ⊢; omega)

/-- A declaration contains a hole: in a parameter type, its type, its body, or (an inductive
type) a parameter type, its sort or a field type. -/
def _root_.Ochr.Surface.SDecl.hasHole (d : SDecl) : Bool :=
  d.params.any (holeIn ·.2) || holeIn d.ret || holeIn d.body ||
    d.indParams.any (holeIn ·.2) || (d.indSort.map holeIn).getD false ||
    (d.ind?.getD []).any fun (_, fs) => fs.any (holeIn ·.2)

/-- No declaration of `p` contains a hole: `p` has no axioms (surface `def`s always have a
body, so a hole is the only one). -/
def NoHoles (p : Program) : Prop := ∀ d ∈ p, d.hasHole = false

/-- `checkProgram` gives every declaration of `p` the verdict `accepted` under `cfg` at `fuel`
(`Verdict.ok` is false on `rejected` and on `undecided`). Executable, for the `#guard`s; the
theorem uses `Accepted`, the default `Config`. -/
def accepts (cfg : Config) (fuel : Nat) (p : Program) : Bool :=
  (checkProgram p cfg fuel).all (·.2.1.ok)

/-- `checkProgram` gives every declaration of `p` the verdict `accepted`, at `fuel`: none is
rejected or undecided. -/
def Accepted (p : Program) (fuel : Nat) : Prop := accepts {} fuel p = true

/-- `d` is a definition with no parameters whose declared type is written `False` (its
locations, `STerm.loc`, ignored): a closed proof of `False`, once `False` is the library's. -/
def _root_.Ochr.Surface.SDecl.IsFalseConst (d : SDecl) : Prop :=
  d.ind? = none ∧ d.params = [] ∧ d.ret.unloc = .ident "False"

/-- **Consistency (Conjecture 1), against the checker.** No hole-free program, after the
library, whose every declaration the checker accepts, at any fuel, contains a parameterless
definition of type `False`. The module docstring gives the reason for each part of the
statement, says why a literal `False` suffices, and lists what a proof must confront (the one
`opaque`, fuel, the universe bound, the checker against the rules). -/
theorem consistency (q : Program) (fuel : Nat)
    (holes : NoHoles q)
    (acc : Accepted (Prelude.decls ++ q) fuel) :
    ∀ d ∈ q, ¬ d.IsFalseConst := by
  sorry

/-! ## The hypotheses are needed, and a literal `False` loses nothing

Each program below is checked by the build. The first two are accepted programs that contain
a closed proof of `False` once one part of the statement is dropped (no holes, the library in
front). The third shows that an `undecided` verdict is not acceptance. The last four check
the reduction behind "a literal `False` loses nothing": a constant of a type that computes to
an empty one becomes a literal `False` in one more declaration (with a hole standing in for
the bad constant, since no hole-free one is known). -/

private def F : STerm := .ident "False"
private def decl (name : String) (ret body : STerm) (params : List (String × STerm) := []) : SDecl :=
  { name, params, ret, body, expectAccept := true }
private def lib (q : Program) : Program := Prelude.decls ++ q
private def hasFalseConst (q : Program) : Bool :=
  q.any fun d => d.ind?.isNone && d.params.isEmpty && (match d.ret.unloc with | .ident "False" => true | _ => false)

-- the library satisfies the hypotheses
#guard !Prelude.decls.any (·.hasHole) && accepts {} 2000000 (lib [])

/-- `NoHoles` is needed: a hole proves `False`. -/
private def holeFalse : Program := [decl "H" F (.ident "?")]
#guard holeFalse.any (·.hasHole) && hasFalseConst holeFalse && accepts {} 2000000 (lib holeFalse)

/-- The library in front is needed: without it, `False` can be a user's inhabited type. -/
private def noPrelude : Program :=
  [{ name := "False", ind? := some [("Mk", [])], expectAccept := true }, decl "Y" F (.ident "Mk")]
#guard hasFalseConst noPrelude && accepts {} 2000000 noPrelude

-- Exhaustion is not acceptance: at fuel 1 the checker runs out, the verdicts are
-- `undecided`, and the program is not `Accepted`, although it is at the default fuel.
#guard (checkProgram (lib holeFalse) {} 1).any (·.2.1 matches .undecided _) &&
  !accepts {} 1 (lib holeFalse)

/-- A type that computes to `False` (`Eq` on distinct constructors) gives a literal `False`. -/
private def eqFalse : Program :=
  [decl "C" (.app "Eq" [.ident "Nat", .num 0, .num 1]) (.ident "?"), decl "B" F (.ident "C")]
#guard accepts {} 2000000 (lib eqFalse)

/-- `False ∧ ⊤` gives a literal `False`, by its one arm. -/
private def andFalse : Program :=
  [decl "A" (.and F .top) (.ident "?"),
   decl "B" F (.matchGen (.ident "A") [("Intro", ["l", "r"], .ident "l")])]
#guard accepts {} 2000000 (lib andFalse)

/-- A user's zero-constructor proposition gives a literal `False`, by an annotated zero-arm
match (a constant's body is evaluated, never in tail position, so the match is annotated). -/
private def voidFalse : Program :=
  [{ name := "Void", ind? := some [], indSort := some (.sort 0), expectAccept := true },
   decl "V" (.ident "Void") (.ident "?"),
   decl "B" F (.letIn "v" none (.ident "V") (.letIn "x" (some F) (.matchGen (.ident "v") []) (.ident "x")))]
#guard accepts {} 2000000 (lib voidFalse)

/-- A user's zero-constructor data type gives a literal `False` by a zero-arm match too, here
as a function, `Absurd`, which `def B : False := Absurd(c)` would call. That last step is not
checked: a constant defined by a hole at a data type is a fresh abstract value, whose type
does not survive into the next declaration's state, so a later use of it is rejected
("unknown abstract value"), whatever the use. -/
private def emptyFalse : Program :=
  [{ name := "Empty", ind? := some [], expectAccept := true },
   decl "Absurd" F (.matchGen (.ident "e") []) [("e", .ident "Empty")]]
#guard accepts {} 2000000 (lib emptyFalse)

end Ochr.Consistency
