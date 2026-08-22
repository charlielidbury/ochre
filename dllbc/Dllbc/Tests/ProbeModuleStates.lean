import Dllbc.Program
import Dllbc.FnMacro
import Dllbc.ElabCheck
import Dllbc.ProgMacro
import Dllbc.Std
open Dllbc

-- the "std module": one lemma, match+recursion form
def stdBlock : Term := prog_parse {
  fn LeRefl [n] (n : Nat) -> Le n n {
    match n { Z => unit, S(k) => LeRefl(k) } };
  () }

-- final state of the std block, WITHOUT the closing endScope (bindings persist)
def finalSt (t : Term) : Option St :=
  match explore defaultFuel (atBoundary t) initSt with
  | [.ok p] => some p.2
  | _ => none

#eval (finalSt stdBlock).isSome
#eval (finalSt stdBlock).map (fun s => (s.nextSym, s.env.length, (Term.numberSeals stdBlock).1))

-- hand-built consumer: let y = LeRefl(2); ()  (call = app spine at a name-keyed var)
def consumer : Term :=
  .letIn ⟨950, "y"⟩ (.app (.var ⟨0, "LeRefl"⟩) (Term.nat 2)) .unit

-- seeded run of the consumer
def seededRun : String :=
  match finalSt stdBlock with
  | none => "NO SEED"
  | some s =>
    match explore defaultFuel (atBoundary consumer) s with
    | [.ok p] => s!"ok nextSym={p.2.nextSym} y={((p.2.env.find? (fun (kv : Var × Val) => kv.1.name == "y")).map (fun (kv : Var × Val) => kv.2.pretty))}"
    | [.error e] => s!"ERR {e}"
    | rs => s!"paths={rs.length}"
#eval seededRun

-- the splice: same two pieces in ONE block
def spliced : Term := prog_parse {
  fn LeRefl [n] (n : Nat) -> Le n n {
    match n { Z => unit, S(k) => LeRefl(k) } };
  let y = LeRefl(2);
  () }
#eval match explore defaultFuel (atBoundary spliced) initSt with
  | [.ok p] => s!"splice ok nextSym={p.2.nextSym} y={((p.2.env.find? (fun (kv : Var × Val) => kv.1.name == "y")).map (fun (kv : Var × Val) => kv.2.pretty))}"
  | [.error e] => s!"splice ERR {e}"
  | rs => s!"splice paths={rs.length}"

-- executing mode, seeded: does it run to the concrete proof?
#eval match finalSt stdBlock with
  | none => "no seed"
  | some s =>
    match explore defaultFuel (atBoundary consumer) { s with executing := true } with
    | [.ok p] => s!"exec y={((p.2.env.find? (fun (kv : Var × Val) => kv.1.name == "y")).map (fun (kv : Var × Val) => kv.2.pretty))}"
    | [.error e] => s!"exec ERR {e}"
    | rs => s!"exec paths={rs.length}"
