import Ochr.Obs

/-!
# A heap-based value layer for the data slice (viability lane, `notes/stability.md` §8)

Not part of the checker: nothing in `Ochr.lean` imports this module, so the checker's path is
untouched. It is a second evaluator for the data slice of the untyped machine (variables,
field and predecessor places, constructors, `let`, `;`, matches on constructor values, `clone`,
and calls of data functions that do not get stuck), over the real `Term` syntax, in which a
value is a handle into a heap and the evaluator sees a node only by asking (`view`).
`HeapSlice.lean` runs suite programs through it and through the real machine and compares.

The evaluator is a reified computation (`Prog`), so `exec_agree` (one induction on `Prog`)
gives (P) for it with no per-construct proof (`P_evalH`).
-/

namespace Ochr.Heap
open Ochr

/-- A node of the heap: what a handle holds. An unknown (an abstract value) has no node. -/
inductive Node where
  | zero | succ (a : Nat) | unit
  | ind (ty : String) (c : Nat) (fs : List Nat)
  | opaque (v : Value)          -- a value outside the slice (a proof `⋆`, a function, a type)
deriving Inhabited

/-- A computation over the heap, reified: it returns, asks what a handle holds (`view`; `none`
for an unknown), or stores a new node (`alloc`). -/
inductive Prog (β : Type) where
  | ret (b : β)
  | view (h : Nat) (k : Option Node → Prog β)
  | alloc (n : Node) (k : Nat → Prog β)

def Prog.bind {β γ : Type} : Prog β → (β → Prog γ) → Prog γ
  | .ret b, f => f b
  | .view h k, f => .view h fun o => (k o).bind f
  | .alloc n k, f => .alloc n fun a => (k a).bind f

instance : Monad Prog where
  pure := .ret
  bind := Prog.bind

/-- The heap: each handle's node (`none`: an unknown), and the next fresh handle. -/
structure Heap where
  node : Nat → Option Node
  next : Nat

def Heap.alloc (H : Heap) (n : Node) : Heap :=
  { node := fun m => if m = H.next then some n else H.node m, next := H.next + 1 }

/-- Refine the unknown `σ` to the node `n`: a case split or an instantiation fills a node in
place, instead of substituting through the state. -/
def Heap.set (H : Heap) (σ : Nat) (n : Node) : Heap :=
  { node := fun m => if m = σ then some n else H.node m, next := H.next }

def exec {β : Type} : Prog β → Heap → β × Heap
  | .ret b, H => (b, H)
  | .view h k, H => exec (k (H.node h)) H
  | .alloc n k, H => exec (k H.next) (H.alloc n)

/-- The handles a run asks about. -/
def queries {β : Type} : Prog β → Heap → List Nat
  | .ret _, _ => []
  | .view h k, H => h :: queries (k (H.node h)) H
  | .alloc n k, H => queries (k H.next) (H.alloc n)

/-- Runs agree when the heaps agree on what is asked (one induction on `Prog`). -/
theorem exec_agree {β : Type} (D : Nat → Prop) :
    ∀ (p : Prog β) (H₁ H₂ : Heap), H₁.next = H₂.next → (∀ n, D n → n < H₁.next) →
    (∀ n, ¬ D n → H₁.node n = H₂.node n) → (∀ h ∈ queries p H₁, ¬ D h) →
    (exec p H₁).1 = (exec p H₂).1 ∧ (exec p H₁).2.next = (exec p H₂).2.next ∧
      ∀ n, ¬ D n → (exec p H₁).2.node n = (exec p H₂).2.node n
  | .ret _, _, _, hn, _, hD, _ => ⟨rfl, hn, hD⟩
  | .view h k, H₁, H₂, hn, hlt, hD, hq => by
    have hh : H₁.node h = H₂.node h := hD h (hq h (List.mem_cons_self ..))
    simp only [exec, ← hh]
    exact exec_agree D (k (H₁.node h)) H₁ H₂ hn hlt hD fun x hx => hq x (List.mem_cons_of_mem _ hx)
  | .alloc s k, H₁, H₂, hn, hlt, hD, hq => by
    simp only [exec, ← hn]
    refine exec_agree D (k H₁.next) (H₁.alloc s) (H₂.alloc s) (by simp [Heap.alloc, hn]) ?_ ?_ hq
    · intro n hd; have := hlt n hd; simp [Heap.alloc]; omega
    · intro n hd; simp only [Heap.alloc, hn]; split <;> simp_all

/-! ## The slice evaluator -/

/-- The outcome of a run: a handle, stuck on an unknown (where the machine closes off or
splits), a type error, or a term outside the slice. -/
inductive Res where
  | ok (h : Nat) | stuck | err (m : String) | outside (m : String)
deriving Inhabited

/-- An entry of the environment: a value's handle, or the function being run (its `self`). -/
inductive Entry where
  | val (h : Nat) | fn (n : String)

/-- What the slice needs to know of the program: each data function's arity and body, each
constant's value, and which inductive types are propositions. -/
structure Sig where
  fn : String → Option (Nat × Term)
  const : String → Option Value
  isProp : String → Bool
  /-- Model the real machine's whole-value walks on a read (`readPlace` checks `v.hasHole`,
  [Access] searches the value for live loans): every node reachable from the value read is
  viewed. A measurement of what such walks cost (P) (§8); off for the slice proper. -/
  walkOnRead : Bool := false

/-- Store a value in the heap: an abstract value `σ` is the handle `σ` (the unknowns are the
first handles); a value outside the slice is an opaque node. -/
def encode : Value → Prog Res
  | .abs σ => pure (.ok σ)
  | .zero => .alloc .zero fun h => pure (.ok h)
  | .unit => .alloc .unit fun h => pure (.ok h)
  | .succ w => (encode w).bind fun
    | .ok a => .alloc (.succ a) fun h => pure (.ok h)
    | r => pure r
  | .ind ty c _ _ fs => (encodeList fs).bind fun
    | .ok hs => .alloc (.ind ty c hs) fun h => pure (.ok h)
    | .error r => pure r
  | v => .alloc (.opaque v) fun h => pure (.ok h)
where
  encodeList : List Value → Prog (Except Res (List Nat))
    | [] => pure (.ok [])
    | v :: vs => (encode v).bind fun
      | .ok h => (encodeList vs).bind fun
        | .ok hs => pure (.ok (h :: hs))
        | e => pure e
      | r => pure (.error r)

/-- Follow one step of a place from a handle, by asking the heap. -/
def stepH (s : Step) (h : Nat) : Prog Res :=
  .view h fun
    | none => pure (.err "no such place: its path goes into an unknown")
    | some n => match s, n with
      | .fst, .succ a => pure (.ok a)
      | .fst, .ind "Pair" 0 [a, _] => pure (.ok a)
      | .snd, .ind "Pair" 0 [_, b] => pure (.ok b)
      | .field g, .ind t c fs =>
        if t == g.ty && c == g.ctor then
          match fs[g.idx]? with
          | some a => pure (.ok a)
          | none => pure (.err "no such field")
        else pure (.err "no such place: another constructor")
      | .field _, .opaque .proof => .alloc (.opaque .proof) fun a => pure (.ok a)
      | .deref, _ => pure (.outside "a borrow")
      | _, _ => pure (.err "no such place")

def followH : List Step → Nat → Prog Res
  | [], h => pure (.ok h)
  | s :: ss, h => (stepH s h).bind fun
    | .ok a => followH ss a
    | r => pure r

/-- View every node reachable from a handle (a whole-value walk). -/
def walkH : Nat → Nat → Prog Unit
  | 0, _ => pure ()
  | f + 1, h => .view h fun
    | some (.succ a) => walkH f a
    | some (.ind _ _ fs) => walkList f fs
    | _ => pure ()
where
  walkList (f : Nat) : List Nat → Prog Unit
    | [] => pure ()
    | a :: as => (walkH f a).bind fun _ => walkList f as

/-- Resolve a place to a handle. Reads copy: moves are not modelled (an accepted program never
reads what it moved; see §8). With `walk`, the value read is walked, as the real machine does. -/
def placeH (walk : Bool) (ρ : List Entry) (p : Place) : Prog Res :=
  let (i, ss) := p.steps
  match ρ[i]? with
  | some (.val h) => (followH ss h).bind fun
    | .ok a => if walk then (walkH 10000 a).bind fun _ => pure (.ok a) else pure (.ok a)
    | r => pure r
  | some (.fn _) => pure (.outside "a function used as a value")
  | none => pure (.err "unbound variable")

mutual
/-- The slice evaluator: the untyped machine on the data slice, with values as handles. -/
def evalH (S : Sig) : Nat → Term → List Entry → Prog Res
  | 0, _, _ => pure (.outside "out of fuel")
  | _ + 1, .zero, _ => .alloc .zero fun h => pure (.ok h)
  | _ + 1, .tt, _ => .alloc .unit fun h => pure (.ok h)
  | f + 1, .succ u, ρ => (evalH S f u ρ).bind fun
    | .ok a => .alloc (.succ a) fun h => pure (.ok h)
    | r => pure r
  | f + 1, .ctor ty c _ _ as, ρ => (evalArgs S f as ρ).bind fun
    | .ok hs => .alloc (if S.isProp ty then .opaque .proof else .ind ty c hs) fun h => pure (.ok h)
    | .error r => pure r
  | _ + 1, .place p, ρ => placeH S.walkOnRead ρ p
  | _ + 1, .val v, _ => encode v
  | _ + 1, .const n, _ => match S.const n with
    | some v => encode v
    | none => pure (.outside s!"the constant {n}")
  | f + 1, .letIn _ u w, ρ => (evalH S f u ρ).bind fun
    | .ok a => evalH S f w (.val a :: ρ)
    | r => pure r
  | f + 1, .seq u w, ρ => (evalH S f u ρ).bind fun
    | .ok _ => evalH S f w ρ
    | r => pure r
  | f + 1, .prim "clone" [u], ρ => evalH S f u ρ
  | f + 1, .matchNat p z s, ρ => (placeH false ρ p).bind fun
    | .ok a => .view a fun
      | some .zero => evalH S f z ρ
      | some (.succ _) => evalH S f s ρ
      | none => pure .stuck
      | some _ => pure (.err "[Match] on a value that is not a number")
    | r => pure r
  | f + 1, .matchInd p ty arms, ρ =>
    if S.isProp ty then pure (.outside "a match on a proof") else
    (placeH false ρ p).bind fun
    | .ok a => .view a fun
      | some (.ind t c _) =>
        if t != ty then pure (.err "[Match] on a value of another type") else
        match arms[c]? with
        | some (_, arm) => evalH S f arm ρ
        | none => pure (.err "[Match] no arm")
      | none => pure .stuck
      | some _ => pure (.err "[Match] on a value that is not of the type")
    | r => pure r
  | f + 1, .call hd as _, ρ =>
    let name : Option String := match hd with
      | .const n => some n
      | .place (.var i) => match ρ[i]? with
        | some (.fn n) => some n
        | _ => none
      | _ => none
    match name.bind S.fn with
    | none => pure (.outside "a call of something other than a data function")
    | some (k, body) =>
      if as.length != k then pure (.err "[Call] arity") else
      (evalArgs S f as ρ).bind fun
      | .ok hs =>
        -- the body sees its parameters (the last is variable 0), then itself
        evalH S f body (hs.reverse.map .val ++ [.fn (name.getD "")])
      | .error r => pure r
  | _ + 1, _, _ => pure (.outside "a term outside the slice")
termination_by structural f => f

def evalArgs (S : Sig) : Nat → List Term → List Entry → Prog (Except Res (List Nat))
  | _, [], _ => pure (.ok [])
  | 0, _ :: _, _ => pure (.error (.outside "out of fuel"))
  | f + 1, a :: as, ρ => (evalH S f a ρ).bind fun
    | .ok h => (evalArgs S f as ρ).bind fun
      | .ok hs => pure (.ok (h :: hs))
      | e => pure e
    | r => pure (.error r)
termination_by structural f => f
end

/-- **(P) for the heap slice, for free.** A run of the slice evaluator that never asks about the
unknown `σ` gives the same outcome whatever `σ` is refined to, and leaves the same heap apart
from `σ`. No case of `evalH` is looked at: this is `exec_agree` with `D = {σ}`. -/
theorem P_evalH (S : Sig) (f : Nat) (t : Term) (ρ : List Entry) (H : Heap) (σ : Nat) (n : Node)
    (hσ : σ < H.next) (hq : σ ∉ queries (evalH S f t ρ) H) :
    (exec (evalH S f t ρ) (H.set σ n)).1 = (exec (evalH S f t ρ) H).1 ∧
      ∀ m, m ≠ σ → (exec (evalH S f t ρ) (H.set σ n)).2.node m = (exec (evalH S f t ρ) H).2.node m := by
  have := exec_agree (· = σ) (evalH S f t ρ) H (H.set σ n) rfl (by intro m h; omega)
    (by intro m hm; simp [Heap.set, hm]) (by intro h hh e; exact hq (e ▸ hh))
  exact ⟨this.1.symm, fun m hm => (this.2.2 m hm).symm⟩

/-- Read a handle back as a value (an unknown handle `σ` is the abstract value `σ`). -/
def decode (H : Heap) : Nat → Nat → Value
  | 0, _ => .bot
  | f + 1, h => match H.node h with
    | none => .abs h
    | some .zero => .zero
    | some .unit => .unit
    | some (.succ a) => .succ (decode H f a)
    | some (.ind ty c fs) => .ind ty c ⟨""⟩ [] (fs.map (decode H f))
    | some (.opaque v) => v

end Ochr.Heap
