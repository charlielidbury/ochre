import Ochr.Basic

/-! # Printing terms and values in the paper's notation. -/

namespace Ochr

private def nameAt (ns : List String) (i : Nat) : String :=
  ns.getD i s!"#{i}"

private def natLit? : Value → Option Nat
  | .zero => some 0
  | .succ v => (natLit? v).map (· + 1)
  | _ => none

private def natLitT? : Term → Option Nat
  | .zero => some 0
  | .succ t => (natLitT? t).map (· + 1)
  | _ => none

def Place.pp (ns : List String) : Place → String
  | .var i => nameAt ns i
  | .deref p => s!"*{p.pp ns}"
  | .fst (.deref p) => s!"(*{p.pp ns}).0"
  | .fst p => s!"{p.pp ns}.0"
  | .snd (.deref p) => s!"(*{p.pp ns}).1"
  | .snd p => s!"{p.pp ns}.1"
  | .field g (.deref p) => s!"(*{p.pp ns}).{g.name}"
  | .field g p => s!"{p.pp ns}.{g.name}"

/-- A universe level in subscript digits, as the surface writes it (`Type₁`). -/
def subscriptNat (l : Nat) : String :=
  String.mk ((toString l).toList.map fun c => Char.ofNat (c.toNat - '0'.toNat + 0x2080))

mutual
partial def Term.pp (ns : List String) : Term → String
  | .place p => p.pp ns
  | .borrow p => s!"&{p.pp ns}"
  | .assign p t => s!"{p.pp ns} := {t.pp ns}"
  | .letIn h t u => s!"let {h.name} = {t.pp ns}; {u.pp (h.name :: ns)}"
  | .seq t u => s!"{t.pp ns}; {u.pp ns}"
  | .matchNat p z s => s!"match {p.pp ns} \{ Z => {z.pp ns}, S _ => {s.pp ns} }"
  | .const n => n
  | .val v => v.pp
  | .sort 0 => "Prop"
  | .sort (l + 1) => if l == 0 then "Type" else "Type" ++ subscriptNat l
  | .pi hs ds c => ppPi ns hs ds c
  | .fix h hs ds c d b =>
      let (ns', bs) := domsPP ns hs ds
      let byS := match d with
        | some j => s!" by {(hs.getD j ⟨"?"⟩).name}"
        | none => ""
      s!"fix {h.name} {bs} : {c.pp ns'}{byS} := {b.pp (ns'.insertIdx hs.length h.name)}"
  | .call f as _ => s!"{f.ppHead ns}({", ".intercalate (as.map (·.pp ns))})"
  | .nat => "Nat" | .unit => "Unit" | .tt => "()"
  | .zero => "0"
  | .succ t => match natLitT? (.succ t) with
      | some n => toString n
      | none => s!"S({t.pp ns})"
  | .fst t => s!"{t.ppArg ns}.0"
  | .snd t => s!"{t.ppArg ns}.1"
  | .eq a b c => s!"Eq({a.pp ns}, {b.pp ns}, {c.pp ns})"
  | .id a b c => s!"Id({a.pp ns}, {b.pp ns}, {c.pp ns})"
  | .cong f h => s!"cong({f.pp ns}, {h.pp ns})"
  | .ref a => s!"&{a.ppArg ns}"
  | .ascribe t a => s!"({t.pp ns} : {a.pp ns})"
  | .prim "peek" [t] | .prim "inplace" [t] => t.pp ns   -- D53: a read that copies / is not consumed
  | .prim "clone" [t] => s!"clone({t.pp ns})"
  | .prim n as => " ".intercalate (n :: as.map (·.ppArg ns))
  | .tind "True" [] => "⊤"
  | .tind "And" [a, b] => s!"{a.ppArg ns} ∧ {b.ppArg ns}"
  | .tind "Pair" [a, b] => s!"{a.ppArg ns} × {b.ppArg ns}"      -- the library's notation (D52)
  | .tind n as => if as.isEmpty then n else s!"{n}({", ".intercalate (as.map (·.pp ns))})"
  | .ctor "True" _ _ _ [] => "refl"
  | .ctor "And" _ _ [] [a, b] => s!"⟨{a.pp ns}, {b.pp ns}⟩"
  | .ctor "Pair" _ _ [] [a, b] => s!"({a.pp ns}, {b.pp ns})"
  | .ctor _ _ h ps as =>
    let pre := if ps.isEmpty then "" else s!"[{", ".intercalate (ps.map (·.pp ns))}]"
    if as.isEmpty then h.name ++ pre else s!"{h.name}{pre}({", ".intercalate (as.map (·.pp ns))})"
  | .matchInd p _ as =>
    s!"match {p.pp ns} \{ {", ".intercalate (as.map fun (h, a) => s!"{h.name} => {a.pp ns}")} }"

partial def Term.ppArg (ns : List String) (t : Term) : String :=
  match t with
  | .place _ | .const _ | .nat | .unit | .tt | .zero | .sort _
  | .ascribe _ _ | .call _ _ _ | .ctor _ _ _ _ _
  | .eq _ _ _ | .id _ _ _ | .cong _ _ => t.pp ns
  | .tind "And" [_, _] | .tind "Pair" [_, _] => s!"({t.pp ns})"
  | .tind _ _ => t.pp ns
  | .val v => v.ppArg
  | .succ _ => t.pp ns
  | _ => s!"({t.pp ns})"

partial def Term.ppHead (ns : List String) (t : Term) : String :=
  match t with
  | .place _ | .const _ => t.pp ns
  | .val (.gfn n) => n
  | .val v => v.ppArg
  | _ => s!"({t.pp ns})"

partial def domsPP (ns : List String) (hs : List Hint) (ds : List Term) : List String × String :=
  let (ns', bs) := (hs.zip ds).foldl
    (fun (ns, acc) (h, d) => (h.name :: ns, acc ++ [s!"({h.name} : {d.pp ns})"])) (ns, ([] : List String))
  (ns', " ".intercalate bs)

partial def ppPi (ns : List String) (hs : List Hint) (ds : List Term) (c : Term) : String :=
  let (ns', bs) := domsPP ns hs ds
  s!"Π{bs}. {c.pp ns'}"

partial def Value.pp : Value → String
  | .zero => "0"
  | .succ v => match natLit? (.succ v) with
      | some n => toString n
      | none => s!"S({v.pp})"
  | .unit => "()"
  | .gfn n => n
  | .clo cs t => ppClosure "" cs t
  | .borrow l v => s!"borrow_{l} {v.ppArg}"
  | .loan l => s!"loan_{l}"
  | .bot => "⊥"
  | .abs s => s!"σ{s}"
  | .sealed t => s!"⌈{t.pp []}⌉"
  | .proof => "⋆"
  | .tNat => "Nat" | .tUnit => "Unit"
  | .tEq A a b => s!"Eq({A.pp}, {a.pp}, {b.pp})"
  | .tRef A => s!"&{A.ppArg}"
  | .tPi cs t => ppClosure "" cs t
  | .sort 0 => "Prop"
  | .sort (l + 1) => if l == 0 then "Type" else "Type" ++ subscriptNat l
  | .ind "Pair" 0 _ _ [a, b] => s!"({a.pp}, {b.pp})"
  | .ind _ _ h _ fs => if fs.isEmpty then h.name else s!"{h.name}({", ".intercalate (fs.map Value.pp)})"
  | .tInd "True" [] => "⊤"
  | .tInd "And" [p, q] => s!"{p.ppArg} ∧ {q.ppArg}"
  | .tInd "Pair" [a, b] => s!"{a.ppArg} × {b.ppArg}"
  | .tInd n as => if as.isEmpty then n else s!"{n}({", ".intercalate (as.map Value.pp)})"

partial def Value.ppArg (v : Value) : String :=
  match v with
  | .zero | .unit | .gfn _ | .loan _ | .bot | .abs _ | .sealed _ | .proof | .tNat | .tUnit
  | .sort _ | .ind _ _ _ _ _ | .tEq _ _ _ => v.pp
  | .tInd "And" [_, _] | .tInd "Pair" [_, _] => s!"({v.pp})"
  | .tInd _ _ => v.pp
  | .succ _ => v.pp
  | _ => s!"({v.pp})"

/-- A closure prints with its captured values named `κ₁ … κₘ` and listed after `where`. -/
partial def ppClosure (_pre : String) (cs : List Value) (t : Term) : String :=
  let capNames := (List.range cs.length).map (fun i => s!"κ{i+1}")
  let ns := capNames.reverse
  let body := t.pp ns
  if cs.isEmpty then body
  else body ++ " where " ++ ", ".intercalate ((capNames.zip cs).map fun (n, v) => s!"{n} = {v.pp}")
end

instance : ToString Value := ⟨Value.pp⟩
instance : ToString Term := ⟨Term.pp []⟩

end Ochr
