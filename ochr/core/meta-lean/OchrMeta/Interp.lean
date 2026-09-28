import OchrMeta.Machine

/-! # The fuelled interpreter, [Seal] normalisation, observations -/

namespace OchrMeta

/-- The interpreter: the machine with a given amount of fuel. -/
def run (P : Prog) (fuel : Nat) (s : St) (t : Term) : Res := exec P fuel s t

theorem run_sound {P : Prog} {fuel : Nat} {s : St} {t : Term} {r : Res}
    (h : run P fuel s t = r) (hr : r ≠ .oof) : Eval P s t r :=
  ⟨hr, fuel, h⟩

/-- The head call `C` of a sealed program: `f(ā)` with `aᵢ = &cᵢ` at borrow positions and `cᵢ`
elsewhere, not eligible for [Close] (D9). -/
def sealHead (f : String) (d : FunDef) : Term :=
  .call f ((List.range d.params.length).zip (d.params.map Prod.snd) |>.map fun (i, ty) =>
    match ty with
    | .ref _ => .borrow (.var (.arg i))
    | _ => .read (.var (.arg i))) false

/-- The sealed program `L; C; K`, with `L`'s bindings supplied by the frame of `sealRun`. -/
def sealTerm (f : String) (d : FunDef) : SealK → Term
  | .res => sealHead f d
  | .fin i => .seq (sealHead f d) (.read (.var (.arg i)))
  | .cur => .letIn .rb (sealHead f d) (.read (.deref (.var .rb)))
  | .back i => .letIn .rb (sealHead f d)
      (.seq (.assign (.deref (.var .rb)) (.read (.var .hole))) (.read (.var (.arg i))))

/-- The frame binding `L`: `cᵢ ↦ argᵢ` and the hole `h ↦ w`. -/
def sealFrame (args w : Val) : Frame :=
  ((List.range args.toList.length).zip args.toList |>.map fun (i, v) => (Var.arg i, v)) ++ [(.hole, w)]

/-- A fresh loan name above every loan occurring in `v`. -/
def Val.freshAbove (v : Val) : Nat := v.loans.foldr max 0 + 1

/-- [Seal]: run the sealed program from the empty environment (loans from outside are inert:
their borrows are not in this environment). -/
def sealRun (P : Prog) (fuel : Nat) (f : String) (args : Val) (k : SealK) (w : Val) : Res :=
  match P.find f with
  | none => .err
  | some d => exec P fuel ⟨[sealFrame args w], (Val.pair args w).freshAbove⟩ (sealTerm f d k)

/-- Normal form of a value: embedded values first, then each sealed program is re-run; if the
run completes its value replaces the sealed program. -/
def norm (P : Prog) (fuel : Nat) : Val → Val
  | .succ v => .succ (norm P fuel v)
  | .pair a b => .pair (norm P fuel a) (norm P fuel b)
  | .borrow l v => .borrow l (norm P fuel v)
  | .sealed f a k w =>
    let a' := norm P fuel a
    let w' := norm P fuel w
    match sealRun P fuel f a' k w' with
    | .ok _ v => v
    | _ => .sealed f a' k w'
  | v => v

/-- Owners of a loan (RULES §4): follow each occurrence outward through borrow contents to the
owned bindings.  `n` bounds the chain length. -/
def ownersN : Nat → Env → Nat → List Var
  | 0, _, _ => []
  | n + 1, Ω, l => Ω.flatten.flatMap fun (x, c) =>
      match c with
      | .borrow m w => if l ∈ w.loans then ownersN n Ω m else []
      | c => if l ∈ c.loans then [x] else []

def owners (Ω : Env) (l : Nat) : List Var := (ownersN (Ω.flatten.length + 1) Ω l).eraseDups

/-- End every borrow held in the environment (the observation's final resolution), in
environment order.  `n` bounds the number of rounds. -/
def endAllN : Nat → St → Option St
  | 0, s => some s
  | n + 1, s => match s.env.flatten.find? (fun b => match b.2 with | .borrow .. => true | _ => false) with
    | some (_, .borrow l _) => (endBorrow l s).bind (endAllN n)
    | _ => some s

def endAll (s : St) : Option St := endAllN (s.env.nb + 1) s

end OchrMeta

namespace OchrMeta

def Env.substAbs (a : Nat) (w : Val) (Ω : Env) : Env := Ω.mapVals (Val.substAbs a w)
def Env.names (Ω : Env) : List Nat := Ω.flatten.flatMap fun b => b.2.names

/-- Canonical renaming of loans, in order of first occurrence: `≈` is equality after `canon`. -/
def Env.canonMap (Ω : Env) (extra : List Nat := []) : Nat → Nat :=
  let ns := (Ω.names ++ extra).eraseDups
  fun l => (ns.idxOf? l).getD (ns.length + l)

def Env.canon (Ω : Env) : Env := Ω.mapVals (Val.rename Ω.canonMap)

/-- Canonical form of a final state and value (value names included). -/
def canonRes (Ω : Env) (v : Val) : Env × Val :=
  let ρ := Env.canonMap (Ω ++ [[(.hole, v)]])
  (Ω.mapVals (Val.rename ρ), v.rename ρ)

def Env.norm (P : Prog) (fuel : Nat) (Ω : Env) : Env := Ω.mapVals (OchrMeta.norm P fuel)

end OchrMeta
