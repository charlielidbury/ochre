import Dllbc.Program
import Dllbc.FnMacro
import Dllbc.AlphaEq
import Dllbc.Macro
import Dllbc.Std
import Dllbc.StdLemmas
import Dllbc.DeclMacro
import Dllbc.ProgMacro

/-!
# S27 — the annotated runtime λ (M27 α.1a)

`Term.lamR`'s binders carry their domains. The document's grammar has said
`λ (x : τ). t` from the start; M26-C's Curry form was the mechanization drifting
from it while building the runtime layer, and this is the drift undone.

**Nothing here checks an annotation yet.** α.1a carries the types; α.1b makes
`sealFn` convert the λ's synthesized Π against the ascription. The two are
separate commits on purpose — 95 mechanical binder edits and two rule changes in
one commit would make every red build a two-suspect investigation — so what this
file pins is exactly the mechanical half:

  * the surface really carries a domain, and the VALUE really drops it (§A/§B);
  * the traversals that gained a case really traverse it (§C free variables, §D
    equality and α-normalization);
  * and `fnElab`'s arm annotations are the ones the kernel's own `checkArm`
    derives — §E, the one place in α.1a where a wrong answer would compile,
    pass, and be silently the wrong type.
-/

namespace Dllbc.Tests.S27Lam
open Dllbc

/-- The declaration checks. -/
def ok (d : Decl) (table : List Decl := [d]) : Bool := checkFnOk d table
/-- The declaration is rejected with an error containing `needle`. -/
def rejects (d : Decl) (needle : String) (table : List Decl := [d]) : Bool :=
  checkFnErr d needle table

/-! ## §A. The surface carries the domain -/

def annotated : Term := prog{ let g = λ(a : Nat) { a }; () }

example : (match annotated with
           | .letIn _ (.lamR [(_, τ)] _) _ => Term.beq τ (.const "Nat")
           | _ => false) = true := by native_decide

-- A capitalized binder's domain carries §6's comptime marker, which is what makes
-- the annotation agree with the ascription `piPeel` checks a mode against.
def annotatedCmp : Term := prog{ let g = λ(A : Nat) { A }; () }
example : (match annotatedCmp with
           | .letIn _ (.lamR [(_, τ)] _) _ => Term.beq τ (.cmpT (.const "Nat"))
           | _ => false) = true := by native_decide

/-! ## §B. …and the VALUE drops it (the erasure, ratified)

    `readR` forms a `Val.rfn` with names only. The executing machine binds and
    runs and never converts, so there is nothing downstream of formation for a
    domain to be used by — the seal is the one consumer and it holds the
    annotated TERM. -/

-- The type-level half, and it is the stronger of the two: this expression
-- typechecks exactly because `Val.rfn`'s binders are `Var` and not `Var × Term`.
-- A ledger that fails to compile is the one that cannot drift.
example : Val := .rfn [⟨0, "a"⟩] .unit

-- The live half: an ANNOTATED λ evaluates to a value printed with names alone.
example : (match runProgram annotated with
           | .ok env => (env.lookup "g").map Val.pretty
           | .error _ => none) = some "λr(a){…}" := by native_decide

/-! ## §C. Free variables reach into the domains

    `Term.freeRVars` traverses the binder types, as a TELESCOPE — each domain
    under the binders to its left and none of its own. That is a real rule and not
    a tidiness: a domain names runtime slots (`Le (len *v) fuel` names two), so
    leaving them untraversed would let a genuinely free variable into a type and
    straight past the closedness check the traversal exists to feed.

    Three programs, one per demand site, and the λ is FORMED in every one — an
    unformed λ is never asked. -/

-- C1. The domain captures a data binding: refused, by the same rule and the same
-- message a captured body reference gets.
def capInType : Decl := decl{ fn caller () -> Unit
  { let n = 3; let g = λ(a : Le n n) { () }; () } }
example : rejects capInType "not a function" = true := by native_decide

-- C2. THE ISOLATING CONTROL. The same λ with a closed domain is accepted, so C1 is
-- about the reference and not about annotating a binder at all.
def closedType : Decl := decl{ fn caller () -> Unit
  { let n = 3; let g = λ(a : Le 3 3) { () }; () } }
example : ok closedType = true := by native_decide

-- C3. And the scoping is a TELESCOPE: a domain naming the λ's OWN earlier binder
-- is bound, not free. This is the shape every recursor arm has (`ih`'s domain
-- mentions the predecessor to its left), so getting it wrong would reject the
-- whole recursor story rather than a corner of it.
def telType : Decl := decl{ fn caller () -> Unit
  { let g = λ(m : Nat, a : Le m m) { () }; () } }
example : ok telType = true := by native_decide

/-! ## §D. Equality and α-normalization see the domains -/

-- `Term.beq` compares them structurally (via `Term.beq`, not `==`: the `BEq Term`
-- instance is declared below the mutual block this case lives in).
example : Term.beq (.lamR [(⟨0, "a"⟩, .const "Nat")] .unit)
                   (.lamR [(⟨0, "a"⟩, .const "Bool")] .unit) = false := by native_decide
example : Term.beq (.lamR [(⟨0, "a"⟩, .const "Nat")] .unit)
                   (.lamR [(⟨0, "a"⟩, .const "Nat")] .unit) = true := by native_decide

def anOf (t : Term) : Term := (anTerm [] 0 t).1
/-- `Le x x`, written raw so the variable is exactly the one under test. -/
def leSelf (x : Var) : Term := Std.LeT (.var x) (.var x)

-- α-normalization renumbers a domain's variable references with the binder they
-- name: two arms differing only in ids are α-equal, THROUGH their annotations.
def telA : Term := .lamR [(⟨7, "m"⟩, .const "Nat"), (⟨8, "a"⟩, leSelf ⟨7, "m"⟩)] .unit
def telB : Term := .lamR [(⟨3, "m"⟩, .const "Nat"), (⟨5, "a"⟩, leSelf ⟨3, "m"⟩)] .unit
example : Term.beq (anOf telA) (anOf telB) = true := by native_decide

-- Not vacuous: point the second domain at a FREE variable instead and they part.
-- Without the annotation traversal both of these would have compared EQUAL, since
-- the bodies are `()` — which is what "silently degrades to structural equality on
-- the terms it exists to compare" would have looked like here.
def telC : Term := .lamR [(⟨3, "m"⟩, .const "Nat"), (⟨5, "a"⟩, leSelf ⟨9, "other"⟩)] .unit
example : Term.beq (anOf telA) (anOf telC) = false := by native_decide

/-! ## §E. `fnElab`'s arm annotations — the boxed danger

    An arm is checked at the **motive instantiated at its constructor**, so its
    binders' domains are the residual telescope's with the scrutinee SUBSTITUTED.
    Two things follow, and the second is the one a naive transcription gets wrong:

      * `ih`'s domain is the motive at the PREDECESSOR — a term no source wrote;
      * and the trailing binders do NOT come through unchanged, because
        `absVar kv 0` abstracts the scrutinee over the whole nested Π, domains
        included. A parameter whose type mentions the decreasing one — the fuel
        bound `Le (len *v) n`, which is exactly what §12 decision 8 blessed — is
        annotated `Le (len *v) Z` in the base arm and `Le (len *v) (S n')` in the
        step arm.

    The declaration below is that shape, minimal. The assertions compare against
    hand-written terms rather than against a second call of the derivation, so
    they would fail if the macro transcribed instead of substituting. -/

def bndD : Decl := decl{ fn bnd [n] (n : Nat, v : &mut List Nat, Hn : Le (len *v) n) -> Unit {
  match n { Z => (), S(n2) => { bnd(n2, &mut *v, Hn); () } } } }

/-- The two arms of the emitted `natRec`, as annotated binder lists. -/
def bndArms : Option (List (Var × Term) × List (Var × Term)) :=
  match FnMacro.fnElab bndD with
  | .ok (.seal (.app (.app (.app (.const "natRec") _) (.lamR z _)) (.lamR s _)) _) => some (z, s)
  | _ => none

-- The shape first — assert the instrument before the conclusion.
example : (match bndArms with
           | some (z, s) => z.length == 2 && s.length == 4
           | none => false) = true := by native_decide

/-- `Le (len *v) b`, at the positional `v` the residual telescope keeps. -/
def leLen (b : Term) : Term := Std.LeT (Std.lenT (.deref (.var ⟨1, "v"⟩))) b

-- E1. The bound binder, at each constructor. `Hn` is capitalized, so its domain
-- carries §6's marker — the annotation is the domain as written, marker and all.
example : (match bndArms with
           | some (z, s) =>
             let dec := (s.get! 0).1
             Term.beq (z.get! 1).2 (.cmpT (leLen (.ctorApp "Z" [])))
               && Term.beq (s.get! 3).2 (.cmpT (leLen (.ctorApp "S" [.var dec])))
           | none => false) = true := by native_decide

-- E2. …and neither is the DECLARATION's own domain, which is what a transcription
-- would have produced. This is the assertion the handoff's "`rest` is already a
-- telescope, so those come for free" would have failed.
example : (match bndArms with
           | some (z, s) =>
             let declHn := (bndD.telescope.get! 2).2
             !(Term.beq (z.get! 1).2 declHn) && !(Term.beq (s.get! 3).2 declHn)
           | none => false) = true := by native_decide

-- E3. `ih` is the motive at the predecessor: peel it at the residual telescope's
-- own binders and its bound reads `Le (len *v) n2`, one successor BELOW the arm's
-- own. M26-C established that wrong-level `ih` is a type error rather than a
-- check (`S26Rec` §I); this is the macro's half of the same fact, and it is the
-- one that would compile and pass while being silently wrong.
example : (match bndArms with
           | some (_, s) =>
             let dec := (s.get! 0).1
             match piPeel [⟨1, "v"⟩, ⟨2, "Hn"⟩] (s.get! 1).2 with
             | .ok (tel, _) => tel.length == 2 && Term.beq (tel.get! 1).2 (leLen (.var dec))
             | .error _ => false
           | none => false) = true := by native_decide

-- E4. The predecessor binder itself is the scrutinee's own domain.
example : (match bndArms with
           | some (_, s) => Term.beq (s.get! 0).2 (.const "Nat")
           | none => false) = true := by native_decide

end Dllbc.Tests.S27Lam
