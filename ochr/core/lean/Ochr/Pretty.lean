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
  | .fst (.deref p) => s!"(*{p.pp ns}).1"
  | .fst p => s!"{p.pp ns}.1"
  | .snd (.deref p) => s!"(*{p.pp ns}).2"
  | .snd p => s!"{p.pp ns}.2"

mutual
partial def Term.pp (ns : List String) : Term → String
  | .place p => p.pp ns
  | .borrow p => s!"&{p.pp ns}"
  | .assign p t => s!"{p.pp ns} := {t.pp ns}"
  | .letIn h t u => s!"let {h.name} = {t.pp ns}; {u.pp (h.name :: ns)}"
  | .seq t u => s!"{t.pp ns}; {u.pp ns}"
  | .matchNat p z s => s!"match {p.pp ns} \{ Z => {z.pp ns} | S _ => {s.pp ns} }"
  | .const n => n
  | .val v => v.pp
  | .sort 0 => "Prop"
  | .sort (l + 1) => if l == 0 then "Type" else s!"Type_{l}"
  | .pi hs ds c => ppPi ns hs ds c
  | .fix h hs ds c b =>
      let (ns', bs) := domsPP ns hs ds
      s!"fix {h.name} {bs} : {c.pp ns'} := {b.pp (ns'.insertIdx hs.length h.name)}"
  | .call f as _ => s!"{f.ppHead ns}({", ".intercalate (as.map (·.pp ns))})"
  | .nat => "Nat" | .unit => "Unit" | .tt => "()" | .refl => "refl" | .top => "⊤"
  | .zero => "0"
  | .succ t => match natLitT? (.succ t) with
      | some n => toString n
      | none => s!"S {t.ppArg ns}"
  | .prod a b => s!"{a.ppArg ns} × {b.ppArg ns}"
  | .pair a b => s!"({a.pp ns}, {b.pp ns})"
  | .fst t => s!"{t.ppArg ns}.1"
  | .snd t => s!"{t.ppArg ns}.2"
  | .eq a b c => s!"Eq {a.ppArg ns} {b.ppArg ns} {c.ppArg ns}"
  | .id a b c => s!"Id {a.ppArg ns} {b.ppArg ns} {c.ppArg ns}"
  | .and a b => s!"{a.ppArg ns} ∧ {b.ppArg ns}"
  | .andI a b => s!"⟨{a.pp ns}, {b.pp ns}⟩"
  | .cong f h => s!"cong {f.ppArg ns} {h.ppArg ns}"
  | .ref a => s!"&{a.ppArg ns}"
  | .ascribe t a => s!"({t.pp ns} : {a.pp ns})"
  | .prim n as => " ".intercalate (n :: as.map (·.ppArg ns))

partial def Term.ppArg (ns : List String) (t : Term) : String :=
  match t with
  | .place _ | .const _ | .nat | .unit | .tt | .refl | .top | .zero | .sort _ | .pair _ _
  | .andI _ _ | .ascribe _ _ | .call _ _ _ => t.pp ns
  | .val v => v.ppArg
  | .succ _ => if (natLitT? t).isSome then t.pp ns else s!"({t.pp ns})"
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
      | none => s!"S {v.ppArg}"
  | .unit => "()"
  | .pair a b => s!"({a.pp}, {b.pp})"
  | .gfn n => n
  | .clo cs t => ppClosure "" cs t
  | .borrow l v => s!"borrow_{l} {v.ppArg}"
  | .loan l => s!"loan_{l}"
  | .bot => "⊥"
  | .abs s => s!"σ{s}"
  | .sealed t => s!"⌈{t.pp []}⌉"
  | .proof => "⋆"
  | .tNat => "Nat" | .tUnit => "Unit" | .tTop => "⊤"
  | .tProd a b => s!"{a.ppArg} × {b.ppArg}"
  | .tEq A a b => s!"Eq {A.ppArg} {a.ppArg} {b.ppArg}"
  | .tAnd p q => s!"{p.ppArg} ∧ {q.ppArg}"
  | .tRef A => s!"&{A.ppArg}"
  | .tPi cs t => ppClosure "" cs t
  | .sort 0 => "Prop"
  | .sort (l + 1) => if l == 0 then "Type" else s!"Type_{l}"

partial def Value.ppArg (v : Value) : String :=
  match v with
  | .zero | .unit | .gfn _ | .loan _ | .bot | .abs _ | .sealed _ | .proof | .tNat | .tUnit
  | .tTop | .sort _ | .pair _ _ => v.pp
  | .succ _ => if (natLit? v).isSome then v.pp else s!"({v.pp})"
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
