import Ochr.Surface

/-!
# Fuzzer: printing surface programs in the `ochr { … }` syntax

The output parses back with `Ochr/Notation.lean`, so a shrunk counterexample can be
pasted into an example file as a regression test. Precedence levels follow the
notation: match arms are separated by commas; atoms (max), juxtaposition 60, `×`/`∧` 35, `→` 25, `:=` 20, `;`/`let`/`Π`/`λ` 10.
-/

namespace Ochr.Fuzz
open Ochr.Surface

def paren (b : Bool) (s : String) : String := if b then s!"({s})" else s

mutual
/-- Print at a context that needs level `p` (1024 = an atom). -/
partial def pp (p : Nat) : STerm → String
  | .ident x => x
  | .num n => toString n
  | .app f as => paren (p > 60) (" ".intercalate (f :: as.map fun a => match a with
      | .matchGen .. | .call .. => s!"({pp 0 a})"
      | _ => pp 1024 a))
  | .call f as => s!"{ppHead f}({", ".intercalate (as.map (pp 0))})"
  | .ctorP c ps [] => s!"{c}[{", ".intercalate (ps.map (pp 0))}]"
  | .ctorP c ps as => s!"{c}[{", ".intercalate (ps.map (pp 0))}]({", ".intercalate (as.map (pp 0))})"
  | .deref t => s!"*{pp 1024 t}"
  | .proj i t => match t with
    | .ident x => s!"{x}.{i}"
    | _ => s!"({pp 0 t}).{i}"
  | .amp t => s!"&{pp 1024 t}"
  | .assign a b => paren (p > 20) s!"{pp 21 a} := {pp 20 b}"
  | .letIn x none t u => paren (p > 10) s!"let {x} = {pp 11 t}; {pp 10 u}"
  | .letIn x (some A) t u => paren (p > 10) s!"let {x} : {pp 0 A} = {pp 11 t}; {pp 10 u}"
  | .seq a b => paren (p > 10) s!"{pp 11 a}; {pp 10 b}"
  | .matchGen sc [] => s!"match {pp 0 sc} \{}"
  | .matchGen sc arms => s!"match {pp 0 sc} \{ {", ".intercalate (arms.map ppArm)} }"
  | .pi bs c => paren (p > 10) s!"Π{ppBinders bs}. {pp 10 c}"
  | .arrow a b => paren (p > 25) s!"{pp 26 a} → {pp 25 b}"
  | .fix "_" bs r _ b => paren (p > 10) s!"λ{ppBinders bs} : {pp 21 r} => {pp 10 b}"
  | .fix f bs r d b =>
    let byS := match d with | some x => s!" by {x}" | none => ""
    paren (p > 10) s!"fix {f}{ppBinders bs} : {pp 21 r}{byS} := {pp 10 b}"
  | .unitLit => "()"
  | .pair a b => s!"({pp 0 a}, {pp 0 b})"
  | .andI a b => s!"⟨{pp 0 a}, {pp 0 b}⟩"
  | .top => "⊤"
  | .and a b => paren (p > 35) s!"{pp 36 a} ∧ {pp 35 b}"
  | .prod a b => paren (p > 35) s!"{pp 36 a} × {pp 35 b}"
  | .ascribe a b => s!"({pp 0 a} : {pp 0 b})"
  | .rewrite rev h t => paren (p > 10) s!"rewrite {if rev then "← " else ""}{pp 0 h} in {pp 10 t}"
  | .split f t => paren (p > 10) s!"split {f} in {pp 10 t}"                  -- D61
  | .splitArms f arms => s!"split {f} \{ {", ".intercalate (arms.map ppArm)} }"
  | .sort 0 => "Prop"
  | .sort _ => "Type"

partial def ppHead : STerm → String
  | .ident x => x
  | t => s!"({pp 0 t})"

partial def ppArm : String × List String × STerm → String
  | (c, [], b) => s!"{c} => {pp 10 b}"
  | ("S", [y], b) => s!"S {y} => {pp 10 b}"
  | (c, vs, b) => s!"{c}({", ".intercalate vs}) => {pp 10 b}"

partial def ppBinders (bs : List (String × STerm)) : String :=
  String.join (bs.map fun (x, A) => s!" ({x} : {pp 0 A})")
end

def ppTerm (t : STerm) : String := pp 0 t

def ppDecl (d : SDecl) : String :=
  match d.ind? with
  | some cs =>
    let ctor : String × List (String × STerm) → String
      | (c, []) => c
      | (c, fs) => s!"{c}({", ".intercalate (fs.map fun (f, T) => s!"{f} : {pp 0 T}")})"
    let sort := match d.indSort with
      | some s => s!" : {pp 21 s}"
      | none => ""
    let body := if cs.isEmpty then "" else s!" := {" | ".intercalate (cs.map ctor)}"
    s!"inductive {d.name}{ppBinders d.indParams}{sort}{body}"
  | none =>
    let pre := if d.expectAccept then "def" else "reject def"
    let byS := match d.dec with | some x => s!" by {x}" | none => ""
    s!"{pre} {d.name}{ppBinders d.params} : {pp 21 d.ret}{byS} :=\n    {pp 0 d.body}"

def ppProgram (name : String) (ds : List SDecl) : String :=
  s!"ochr {name} \{\n" ++ String.join (ds.map fun d => s!"  {ppDecl d}\n") ++ "}"

end Ochr.Fuzz
