import Lean

/-!
# The `@[grows]` attribute: a `GrowsIn` lemma indexed by the machine function it is about

`grows_step` (`Steps/Machine/Tactic.lean`) looks a computation's head constant up here, so it
dispatches on the head in one lookup instead of trying every lemma in turn (the bodies are large).
A lemma's conclusion is `GrowsIn G (f …)`; its key is `f`.
-/

namespace Ochr.Meaning.Steps.Machine

open Lean Meta

initialize growsExt : SimpleScopedEnvExtension (Name × Name) (NameMap (List Name)) ←
  registerSimpleScopedEnvExtension {
    addEntry := fun m (k, v) => m.insert k (v :: (m.getD k []))
    initial := {} }

/-- The head constant of the computation in a `GrowsIn G x` conclusion. -/
def growsHead (type : Expr) : MetaM Name := forallTelescope type fun _ concl => do
  let concl ← instantiateMVars concl
  let x := concl.appArg!.headBeta
  match x.getAppFn with
  | .const n _ => pure n
  | _ => throwError "@[grows]: the computation in {concl} has no constant head"

initialize registerBuiltinAttribute {
  name := `grows
  descr := "a GrowsIn lemma for a machine function, indexed by the function"
  add := fun decl _ kind => do
    let info ← getConstInfo decl
    let h ← (growsHead info.type).run'
    growsExt.add (h, decl) kind }

/-- The `@[grows]` lemmas about `f`. -/
def growsLemmas (env : Environment) (f : Name) : List Name :=
  (growsExt.getState env).getD f []

end Ochr.Meaning.Steps.Machine
