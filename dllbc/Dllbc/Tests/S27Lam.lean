import Dllbc.Program
import Dllbc.FnMacro
import Dllbc.AlphaEq
import Dllbc.Macro
import Dllbc.Std
import Dllbc.StdLemmas
import Dllbc.DeclMacro
import Dllbc.ProgMacro
import Dllbc.Tests.S26Prog
import Dllbc.Migrate

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

/-- The declaration checks, ON THE PROGRAM PATH — `decl{ … }` is a harness here,
    not the subject, so these route through `Migrate.progOkOf` and survive δ. -/
def ok (d : FnDef) (table : List FnDef := [d]) : Bool := Migrate.progOkOf d table
/-- The declaration is rejected with an error containing `needle`. -/
def rejects (d : FnDef) (needle : String) (table : List FnDef := [d]) : Bool :=
  Migrate.progRejectsOf d needle table

/-! ## §A. The surface carries the domain -/

def annotated : Term := dllbc{ let g = λ(a : Nat) { a }; () }

example : (match annotated with
           | .letIn _ (.lamR [(_, τ)] _) _ => Term.beq τ (.const "Nat")
           | _ => false) = true := by native_decide

-- A capitalized binder's domain carries §6's comptime marker, which is what makes
-- the annotation agree with the ascription `piPeel` checks a mode against.
def annotatedCmp : Term := dllbc{ let g = λ(A : Nat) { A }; () }
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
def capInType : FnDef := decl{ fn caller () -> Unit
  { let n = 3; let g = λ(a : Le n n) { () }; () } }
example : rejects capInType "not a function" = true := by native_decide

-- C2. THE ISOLATING CONTROL. The same λ with a closed domain is accepted, so C1 is
-- about the reference and not about annotating a binder at all.
def closedType : FnDef := decl{ fn caller () -> Unit
  { let n = 3; let g = λ(a : Le 3 3) { () }; () } }
example : ok closedType = true := by native_decide

-- C3. And the scoping is a TELESCOPE: a domain naming the λ's OWN earlier binder
-- is bound, not free. This is the shape every recursor arm has (`ih`'s domain
-- mentions the predecessor to its left), so getting it wrong would reject the
-- whole recursor story rather than a corner of it.
def telType : FnDef := decl{ fn caller () -> Unit
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

def bndD : FnDef := decl{ fn bnd [n] (n : Nat, v : &mut List Nat, Hn : Le (len *v) n) -> Unit {
  match n {
    Z => (),
    S(n2) => match v {
      Nil => (),
      Cons(hd, tl) => { bnd(n2, &mut *tl, Hn); () } } } } }

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

/-! ## §F. THE ONE CONVERSION (M27 α.1b)

    `sealFn` no longer descends the ascription to supply each binder a type. It
    compares the Π the λ STATES against the Π that was written (`piAgree`), and a
    recursor arm's leading binders — the predecessor and `ih` — are compared
    against what the recursor's premise gives them (`checkArm`).

    The second half is the one that matters. Once an arm ANNOTATES `ih`, an
    annotation taken on trust would let a body state the recursion at its own
    level and be handed it — `bad()` arriving through the door §8's guard used to
    hold, and the reason §7 could delete that guard at all is that `ih`'s type is
    derived rather than chosen.

    Every assertion below perturbs exactly ONE annotation of a program that
    checks, so each is a per-demand-site control rather than a rejection that
    might have had some other cause. -/

/-- The elaborated declaration, as a program: a `let` of the sealed recursor. -/
def bndProg (t : Term) : Term := .letIn ⟨900, "f"⟩ t .unit

/-- `fnElab bndD` with the step arm's `i`-th annotation replaced, and nothing else
    touched. `none` when the elaboration is not the shape this section reads. -/
def stepArmWith (i : Nat) (τ : Term) : Option Term :=
  match FnMacro.fnElab bndD with
  | .ok (.seal (.app (.app (.app (.const "natRec") mot) zArm) (.lamR s sb)) piT) =>
    some (.seal (.app (.app (.app (.const "natRec") mot) zArm)
                  (.lamR (s.set i ((s.get! i).1, τ)) sb)) piT)
  | _ => none

/-- The motive's body, read off the ascription the macro emitted: the seal's type
    is `Π (n : Nat) → R`, and every arm's type is an instance of that `R`. -/
def bndR : Option Term :=
  match FnMacro.fnElab bndD with
  | .ok (.seal _ (.pi _ R)) => some R
  | _ => none

/-- The step arm's predecessor binder. -/
def bndDec : Option Var := bndArms.map (fun p => (p.2.get! 0).1)

-- F0. THE BASELINE. Unperturbed, the elaborated declaration checks — so every
-- rejection below is the perturbation and not the program.
example : (match FnMacro.fnElab bndD with
           | .ok t => progOk (bndProg t)
           | .error _ => false) = true := by native_decide

-- …and the instrument, before the conclusion: `R` really is the motive body,
-- because `ih`'s derived annotation is exactly `R` at the predecessor. That
-- re-derives §E3 from the ASCRIPTION instead of from the arm, which is the
-- independent route to the same fact.
example : (match bndR, bndArms, bndDec with
           | some R, some (_, s), some dec =>
             Term.beq (s.get! 1).2 (Term.substPure 0 (.var dec) R)
           | _, _, _ => false) = true := by native_decide

-- F1. **`ih` AT THE ARM'S OWN LEVEL** — `R` at `S dec` where the premise gives
-- `R` at `dec`. This is precisely what §8's guard used to forbid by comparing
-- snapshots, arriving as an annotation instead of as a call, and it is refused by
-- the arm-binder rule rather than by anything downstream.
example : (match bndR, bndDec with
           | some R, some dec =>
             match stepArmWith 1 (Term.substPure 0 (.ctorApp "S" [.var dec]) R) with
             | some t => progRejects (bndProg t) "the recursor's premise does not give it"
             | none => false
           | _, _ => false) = true := by native_decide

-- F2. …and the predecessor binder is checked by the same rule.
example : (match stepArmWith 0 (.const "Bool") with
           | some t => progRejects (bndProg t) "the recursor's premise does not give it"
           | none => false) = true := by native_decide

-- F3. **THE TRANSCRIPTION BUG, now caught by the build.** Annotate the fuel bound
-- at the PREDECESSOR's level rather than the arm's own — the plausible off-by-one,
-- and the shape a "`rest` comes for free" transcription would have produced a
-- whole family of. It is refused through `piAgree`, which is the other branch of
-- the new check.
example : (match bndDec with
           | some dec =>
             match stepArmWith 3 (.cmpT (leLen (.var dec))) with
             | some t => progRejects (bndProg t) "a domain the ascription does not bind it at"
             | none => false
           | none => false) = true := by native_decide

-- F3b. **THE UNINSTANTIATED ANNOTATION** — the transcription itself, rather than
-- an off-by-one near it: the arm annotated with the DECLARATION's own domain,
-- `Le (len *v) n`, where the motive at this constructor gives `Le (len *v) (S n')`.
-- This is the control that would have caught the handoff's "`rest` is already a
-- telescope, so those come for free", and it is in the battery for that reason.
--
-- **It is refused at the CONVERSION**, and where it fires is part of the claim.
-- The declaration's domain mentions the scrutinee `n`, which does not exist
-- inside an arm — so a closedness rejection was the other plausible outcome, and
-- would have been the conversion passing for the wrong reason. `piAgree` runs
-- before `checkRFnBody`, so the domains are compared before any body is entered,
-- and the message below is the comparison's own.
example : (match stepArmWith 3 (bndD.telescope.get! 2).2 with
           | some t => progRejects (bndProg t) "a domain the ascription does not bind it at"
           | none => false) = true := by native_decide

-- F4. …and an ordinary trailing binder, mistyped outright.
example : (match stepArmWith 2
             (.borrowT (.app (.const "List") (.const "Bool"))
                       (.app (.const "List") (.const "Bool"))) with
           | some t => progRejects (bndProg t) "a domain the ascription does not bind it at"
           | none => false) = true := by native_decide

-- F5. THE ISOLATING CONTROL for the whole section: re-annotating a binder with the
-- type it already had leaves the program ACCEPTED. So F1–F4 are about the
-- disagreement, and not about the perturbation machinery having touched the term.
example : (match bndArms with
           | some (_, s) =>
             match stepArmWith 3 (s.get! 3).2 with
             | some t => progOk (bndProg t)
             | none => false
           | none => false) = true := by native_decide

/-! ### F6. A plain sealed λ, not a recursor — the `sealFn` half on its own -/

def fnTy : Term := pure{ Π (v : &mut List Nat) → Unit }

def annOk : Term := dllbc{
  let f = seal(λ(v : &mut List Nat) { *v := Nil; () }, %fnTy);
  () }
example : progOk annOk = true := by native_decide

-- The same λ, the same ascription, one annotation changed: refused. Before α.1b
-- this was ACCEPTED, because the binder's type came from the ascription and the
-- annotation was carried and never read.
def annBad : Term := dllbc defer_check {
  let f = seal(λ(v : &mut List Bool) { *v := Nil; () }, %fnTy);
  () }
example : progRejects annBad "a domain the ascription does not bind it at" = true := by
  native_decide

/-! ## §G. JUXTAPOSITION APPLICATION (M27 β)

    The document's grammar has one application form, `t t′`; the n-ary `f(a, …)`
    is the declaration era's telescope leaking into the term language, and it dies
    at δ. So `f a b` has to mean a call when `f` names a runtime function.

    **The surface does not decide this, and cannot.** `let finish = (λ (e : …). …)`
    and `let f = seal(…)` are both lowercase slots holding functions, and the first
    must be applied by ⇝ — its arguments are snapshots and proofs that a ⇒ read
    would MOVE — while the second binds Ω slots under ⇒. Nothing about the two
    spines differs syntactically. So β is a KERNEL rule, at `readR`'s `.app` case,
    beside the `runtimeRecSpine?` choice that was already being made there.

    **And the router is §7 cost 5's own distinction rather than a new test**: the
    two λs are "the same former in the document, two representations in the
    machine, because one substitutes and the other binds". A `Val.lam` substitutes;
    a `Val.rfn`, a σ with a signature, or a recursor spine binds. §G5 is the pair
    that makes that observable — the same source line, two λ representations, two
    arrows, two verdicts. -/

def juxSealTy : Term := pure{ Π (v : &mut List Nat) → Unit }

-- G1. A sealed function called by juxtaposition, in statement position.
def juxSeal : Term := dllbc{
  let f = seal(λ(v : &mut List Nat) { *v := Cons(9, Nil); () }, %juxSealTy);
  let x = Cons(1, Nil);
  let b = &mut x;
  f b;
  let y = x;
  () }
example : progOk juxSeal = true := by native_decide
-- **ACCEPTANCE IS NOT THE CLAIM**, and the flip-validation of this section is
-- what said so. With the router disabled, `f b;` in statement position is a
-- discarded ⇝ neutral: nothing is called, and the program still CHECKS. The
-- differential does not catch it either — the router is one rule in `readR`, so
-- BOTH machines stop calling and go on agreeing. It is recorded rather than
-- quietly fixed, because it is phase A's per-demand-site finding arriving in a
-- new disguise: a statement-position call is a demand site that discards its
-- value, so nothing downstream is asked.
--
-- What discriminates is what the call LEAVES: the seal forgets the payload, so
-- after a real call the caller's `y` is an EXISTENTIAL, where an uncalled program
-- still holds the concrete list.
example : ((programEnvs juxSeal).filterMap (fun r => match r with
             | .ok e => (e.lookup "y").map (fun v => v.pretty.take 1)
             | .error _ => none)) = ["σ"] := by native_decide
-- …and both machines still correspond on it, which is the ordinary obligation.
example : Tests.S26Prog.progDiff juxSeal = true := by native_decide

-- …and the comma twin is the same program: same verdict, and both machines agree
-- on it, which is what says β changed how a call is WRITTEN and not what it does.
def juxSealComma : Term := dllbc{
  let f = seal(λ(v : &mut List Nat) { *v := Cons(9, Nil); () }, %juxSealTy);
  let x = Cons(1, Nil);
  let b = &mut x;
  f(b);
  let y = x;
  () }
example : progOk juxSealComma = true := by native_decide
example : (match runProgram juxSeal, runProgram juxSealComma with
           | .ok a, .ok b => a == b
           | _, _ => false) = true := by native_decide

-- G2. A recursor's `ih`, and the sealed recursor itself, both by juxtaposition —
-- `ih tl` inside the arm and `f 3 b` at the call. `ih` is the case with no comma
-- form to fall back on after δ, so it is the one that had to work.
def juxRecMot : Term := pure{ λ (n : Nat). Π (v : &mut List Nat) → Unit }
def juxRecTy : Term := pure{ Π (n : Nat) → Π (v : &mut List Nat) → Unit }
def juxRec : Term := dllbc{
  let f = seal(natRec %juxRecMot
                 (λ(v : &mut List Nat) { () })
                 (λ(n2 : Nat, ih : Π (v : &mut List Nat) → Unit, v : &mut List Nat)
                    { match v { Nil => (), Cons(hd, tl) => { *hd := 0; ih tl; () } } }),
               %juxRecTy);
  let x = Cons(1, Cons(2, Nil));
  let b = &mut x;
  f 3 b;
  let y = x;
  () }
example : progOk juxRec = true := by native_decide
-- The same discriminator: `ih tl` and `f 3 b` really call, so the checking-mode
-- `y` is the seal's existential rather than the list the program wrote.
example : ((programEnvs juxRec).filterMap (fun r => match r with
             | .ok e => (e.lookup "y").map (fun v => v.pretty.take 1)
             | .error _ => none)) = ["σ"] := by native_decide
example : Tests.S26Prog.progDiff juxRec = true := by native_decide
-- It really recursed: the executing machine zeroes both elements.
example : (match runProgram juxRec with
           | .ok env => (env.lookup "y").map Val.pretty
           | .error _ => none) = some "Cons Z (Cons Z Nil)" := by native_decide

-- G3. A transparent runtime λ, called by juxtaposition.
def juxLam : Term := dllbc{ let g = λ(a : Nat) { S(a) }; let r = g 1; r }
example : progOk juxLam (.const "Nat") = true := by native_decide

/-! ### G5. THE ROUTER, made observable

    The same source line — `let y = mk (*v);` — under the two λ representations.
    A PURE λ is applied by ⇝, which reads the payload as a snapshot and leaves the
    borrow intact. A RUNTIME λ is applied by ⇒, which MOVES the payload out and
    leaves a hole, so the obligation audit refuses at return.

    This is the pair the whole rule rests on. Without it "juxtaposition is a call"
    would be a claim about the cases someone happened to write; with it, the two
    arrows are visible at one syntax. -/

def juxPure : FnDef := decl{ fn caller (v : &mut List Nat) -> Unit
  { let mk = (λ (l : List Nat). l);
    let y = mk (*v);
    () } }
example : ok juxPure = true := by native_decide

def juxRuntime : FnDef := decl{ fn caller (v : &mut List Nat) -> Unit
  { let mk = λ(l : List Nat) { l };
    let y = mk (*v);
    () } }
example : rejects juxRuntime "holds a hole (⊥) at return" = true := by native_decide

-- G6. Saturation, at the juxtaposition form (§12 decision 4 — the call event is
-- atomic, so a spine that stops short is an error and not a partial application).
def juxPartial : Term := dllbc defer_check {
  let f = seal(λ(a : Nat, b : Nat) { a }, Π (a : Nat) → Π (b : Nat) → Nat);
  let r = f 1;
  () }
-- The message is the call rule's own, not a parse failure: the spine reached the
-- callee and the callee's telescope is what refused it.
example : progRejects juxPartial "arity mismatch" = true := by native_decide

-- …and the saturated twin is accepted, so G6 is about the missing argument.
def juxSaturated : Term := dllbc{
  let f = seal(λ(a : Nat, b : Nat) { a }, Π (a : Nat) → Π (b : Nat) → Nat);
  let r = f 1 2;
  r }
example : progOk juxSaturated (.const "Nat") = true := by native_decide

-- G7. A RESERVED head stays a constructor, which is what keeps `S n` and a call
-- distinguishable without a token: the basis is closed, so the test is exact.
example : (match (dllbc{ let x = S 3; () } : Term) with
           | .letIn _ (.ctorApp "S" [_]) _ => true
           | _ => false) = true := by native_decide

-- G8. A CAPITAL head is never routed, in either position. §6.3 makes a capital
-- function-typed binder a SPEC parameter — cited, never called — so the spine
-- stays ⇝'s structured neutral. (`S26Modes` §B7 pins the type position; this is
-- the kernel-side guard that a body cannot reach the call rule through it.)
def juxCapital : FnDef := decl{ fn juxCapital (G : Π (x : Nat) → Nat, n : Nat)
  -> Id Nat (G n) (G n) { Refl } }
example : ok juxCapital = true := by native_decide

/-! ## §H. `alphaEq` compares `[k]` (M27-δ)

    The widening became CORRECT at exactly the moment the guard died. While `[k]`
    was a guard input, two definitions differing only in it could still be the same
    function — the hint said which parameter to police, not what to build. Now it
    is purely the scrutinee-selection hint, so it decides which recursor `fnElab`
    emits, and two definitions differing in it are two different terms.

    Asserted rather than assumed, because a widening that no pair exercises is
    indistinguishable from no widening at all. -/

def hintA : FnDef := decl{ fn h [n] (n : Nat, m : Nat) -> Id Nat Z Z
  { match m { Z => Refl, S(m2) => h(n, m2) } } }
/-- The same name, telescope, return type and body — differing in `[k]` alone. -/
def hintB : FnDef := { hintA with dec := some 1 }

example : (hintA.name == hintB.name && hintA.body == hintB.body
        && hintA.telescope == hintB.telescope && hintA.retType == hintB.retType)
  = true := by native_decide
example : FnDef.alphaEq hintA hintB = false := by native_decide
-- …and the criterion still says YES to a genuine α-variant, so §H is about `[k]`
-- and not about the comparison having become trivially false.
example : FnDef.alphaEq hintA hintA = true := by native_decide

-- The hint really does decide which recursor is emitted, which is why the
-- criterion has to see it: one of these elaborates and the other does not,
-- because only `m` is matched on.
example : ((match FnMacro.fnElab hintA with | .ok _ => true | .error _ => false)
        != (match FnMacro.fnElab hintB with | .ok _ => true | .error _ => false))
  = true := by native_decide

end Dllbc.Tests.S27Lam
