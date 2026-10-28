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

/-- How a value prints as an argument, given how it prints (`s = v.pp`): parenthesised
unless atomic. -/
def Value.argWrap (v : Value) (s : String) : String :=
  match v with
  | .zero | .unit | .gfn _ | .loan _ | .bot | .abs _ | .sealed _ | .proof | .tNat | .tUnit
  | .sort _ | .ind _ _ _ _ _ | .tEq _ _ _ => s
  | .tInd "And" [_, _] | .tInd "Pair" [_, _] => s!"({s})"
  | .tInd _ _ => s
  | .succ _ => s
  | _ => s!"({s})"

/-- How a term prints as an argument, given how it prints (`s = t.pp ns`). -/
def Term.argWrap (t : Term) (s : String) : String :=
  match t with
  | .place _ | .const _ | .nat | .unit | .tt | .zero | .sort _
  | .ascribe _ _ | .call _ _ _ | .ctor _ _ _ _ _
  | .eq _ _ _ | .id _ _ _ | .cong _ _ => s
  | .tind "And" [_, _] | .tind "Pair" [_, _] => s!"({s})"
  | .tind _ _ => s
  | .val v => v.argWrap s
  | .succ _ => s
  | _ => s!"({s})"

/-- How a term prints as the head of a call, given how it prints (`s = t.pp ns`). -/
def Term.headWrap (t : Term) (s : String) : String :=
  match t with
  | .place _ | .const _ => s
  | .val (.gfn n) => n
  | .val v => v.argWrap s
  | _ => s!"({s})"

mutual
def Term.pp (ns : List String) : Term → String
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
  | .pi hs ds c =>
      let (ns', bs) := Term.domsPPList ns hs ds
      s!"Π{" ".intercalate bs}. {c.pp ns'}"
  | .fix h hs ds c d b =>
      let (ns', bs) := Term.domsPPList ns hs ds
      let byS := match d with
        | some j => s!" by {(hs.getD j ⟨"?"⟩).name}"
        | none => ""
      s!"fix {h.name} {" ".intercalate bs} : {c.pp ns'}{byS} := {b.pp (ns'.insertIdx hs.length h.name)}"
  | .call f as _ => s!"{f.headWrap (f.pp ns)}({", ".intercalate (Term.ppList ns as)})"
  | .nat => "Nat" | .unit => "Unit" | .tt => "()"
  | .zero => "0"
  | .succ t => match natLitT? (.succ t) with
      | some n => toString n
      | none => s!"S({t.pp ns})"
  | .fst t => s!"{t.argWrap (t.pp ns)}.0"
  | .snd t => s!"{t.argWrap (t.pp ns)}.1"
  | .eq a b c => s!"Eq({a.pp ns}, {b.pp ns}, {c.pp ns})"
  | .id a b c => s!"Id({a.pp ns}, {b.pp ns}, {c.pp ns})"
  | .cong f h => s!"cong({f.pp ns}, {h.pp ns})"
  | .ref a => s!"&{a.argWrap (a.pp ns)}"
  | .ascribe t a => s!"({t.pp ns} : {a.pp ns})"
  | .prim "peek" [t] | .prim "inplace" [t] => t.pp ns   -- D53: a read that copies / is not consumed
  | .prim "clone" [t] => s!"clone({t.pp ns})"
  | .prim n as => " ".intercalate (n :: Term.ppArgList ns as)
  | .tind "True" [] => "⊤"
  | .tind "And" [a, b] => s!"{a.argWrap (a.pp ns)} ∧ {b.argWrap (b.pp ns)}"
  | .tind "Pair" [a, b] => s!"{a.argWrap (a.pp ns)} × {b.argWrap (b.pp ns)}"      -- the library's notation (D52)
  | .tind n as => if as.isEmpty then n else s!"{n}({", ".intercalate (Term.ppList ns as)})"
  | .ctor "True" _ _ _ [] => "refl"
  | .ctor "And" _ _ [] [a, b] => s!"⟨{a.pp ns}, {b.pp ns}⟩"
  | .ctor "Pair" _ _ [] [a, b] => s!"({a.pp ns}, {b.pp ns})"
  | .ctor _ _ h ps as =>
    let pre := if ps.isEmpty then "" else s!"[{", ".intercalate (Term.ppList ns ps)}]"
    if as.isEmpty then h.name ++ pre else s!"{h.name}{pre}({", ".intercalate (Term.ppList ns as)})"
  | .matchInd p _ as =>
    s!"match {p.pp ns} \{ {", ".intercalate (Term.ppArms ns as)} }"
termination_by structural t => t

/-- `ts.map (·.pp ns)`. -/
def Term.ppList (ns : List String) : List Term → List String
  | [] => []
  | t :: ts => t.pp ns :: Term.ppList ns ts
termination_by structural ts => ts

/-- `ts.map (·.ppArg ns)`. -/
def Term.ppArgList (ns : List String) : List Term → List String
  | [] => []
  | t :: ts => t.argWrap (t.pp ns) :: Term.ppArgList ns ts
termination_by structural ts => ts

/-- A match's arms, `C => t`. -/
def Term.ppArms (ns : List String) : List (Hint × Term) → List String
  | [] => []
  | (h, a) :: as => s!"{h.name} => {a.pp ns}" :: Term.ppArms ns as
termination_by structural as => as

/-- A telescope `(x₁ : A₁) …`, each domain printed with the names before it, and the names
with all of them bound. -/
def Term.domsPPList (ns : List String) : List Hint → List Term → List String × List String
  | h :: hs, d :: ds =>
    let (ns', bs) := Term.domsPPList (h.name :: ns) hs ds
    (ns', s!"({h.name} : {d.pp ns})" :: bs)
  | _, _ => (ns, [])
termination_by structural _ ds => ds

def Value.pp : Value → String
  | .zero => "0"
  | .succ v => match natLit? (.succ v) with
      | some n => toString n
      | none => s!"S({v.pp})"
  | .unit => "()"
  | .gfn n => n
  | .clo cs t | .tPi cs t =>
    -- a closure prints with its captured values named `κ₁ … κₘ` and listed after `where`
    let body := t.pp ((List.range cs.length).map (fun i => s!"κ{i+1}")).reverse
    if cs.isEmpty then body else body ++ " where " ++ ", ".intercalate (Value.ppCaps 0 cs)
  | .borrow l v => s!"borrow_{l} {v.argWrap v.pp}"
  | .loan l => s!"loan_{l}"
  | .bot => "⊥"
  | .abs s => s!"σ{s}"
  | .sealed t => s!"⌈{t.pp []}⌉"
  | .proof => "⋆"
  | .tNat => "Nat" | .tUnit => "Unit"
  | .tEq A a b => s!"Eq({A.pp}, {a.pp}, {b.pp})"
  | .tRef A => s!"&{A.argWrap A.pp}"
  | .sort 0 => "Prop"
  | .sort (l + 1) => if l == 0 then "Type" else "Type" ++ subscriptNat l
  | .ind "Pair" 0 _ _ [a, b] => s!"({a.pp}, {b.pp})"
  | .ind _ _ h _ fs => if fs.isEmpty then h.name else s!"{h.name}({", ".intercalate (Value.ppList fs)})"
  | .tInd "True" [] => "⊤"
  | .tInd "And" [p, q] => s!"{p.argWrap p.pp} ∧ {q.argWrap q.pp}"
  | .tInd "Pair" [a, b] => s!"{a.argWrap a.pp} × {b.argWrap b.pp}"
  | .tInd n as => if as.isEmpty then n else s!"{n}({", ".intercalate (Value.ppList as)})"
termination_by structural v => v

/-- `vs.map Value.pp`. -/
def Value.ppList : List Value → List String
  | [] => []
  | v :: vs => v.pp :: Value.ppList vs
termination_by structural vs => vs

/-- The captured values, `κᵢ = v`, numbered from `i + 1`. -/
def Value.ppCaps (i : Nat) : List Value → List String
  | [] => []
  | v :: vs => s!"κ{i+1} = {v.pp}" :: Value.ppCaps (i + 1) vs
termination_by structural vs => vs

end

def Term.ppArg (ns : List String) (t : Term) : String := t.argWrap (t.pp ns)
def Term.ppHead (ns : List String) (t : Term) : String := t.headWrap (t.pp ns)
def Value.ppArg (v : Value) : String := v.argWrap v.pp

def domsPP (ns : List String) (hs : List Hint) (ds : List Term) : List String × String :=
  let (ns', bs) := Term.domsPPList ns hs ds
  (ns', " ".intercalate bs)

def ppPi (ns : List String) (hs : List Hint) (ds : List Term) (c : Term) : String :=
  let (ns', bs) := domsPP ns hs ds
  s!"Π{bs}. {c.pp ns'}"

/-- A closure prints with its captured values named `κ₁ … κₘ` and listed after `where`. -/
def ppClosure (_pre : String) (cs : List Value) (t : Term) : String := (Value.clo cs t).pp

instance : ToString Value := ⟨Value.pp⟩
instance : ToString Term := ⟨Term.pp []⟩

end Ochr
