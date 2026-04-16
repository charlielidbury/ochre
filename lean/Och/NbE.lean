import Och.Syntax

/-!
# Normalization by Evaluation for Och

The eager-substitution `absEval` in `Eval.lean` copies the substituend
into every occurrence position, which makes `done_ ⊑ dNat` fan out
exponentially (iotaIntro substitutes `done_NF` for every `:self`
ascription in `dNat`'s body). NbE avoids this by evaluating into a
semantic domain with *closures*: substitution becomes environment
extension, so the substituend is shared, not copied.

This module is intended to eventually replace `absEval` once it
handles the full calculus. For now it lives alongside so the existing
test suite stays green while it's developed.

References: Abel "NbE: Dependent Types and Impredicativity" (2013);
Christiansen "Checking Dependent Types with NbE: A Tutorial".
-/

namespace NbE

mutual
  /-- Semantic values. Closures capture the evaluation environment so
      substitution is delayed until the binder is opened. Neutrals use
      de Bruijn *levels* so they can be quoted back to indices without
      shifting. -/
  inductive Val where
    | type    : Val
    | lam     : Val → Closure → Val
    | iota    : Val → Closure → Val
    | «fix»   : Val → Closure → Val
    | neutral : Neutral → Val
    deriving Inhabited

  /-- Stuck computations. `var` is a de Bruijn *level*. `app` extends
      a neutral spine with a value argument. `stuckRec` represents a
      recursive head (fix/ι value) applied to a neutral argument —
      the eliminator can't fire on an abstract scrutinee. -/
  inductive Neutral where
    | var      : Nat → Neutral
    | app      : Neutral → Val → Neutral
    | stuckRec : Val → Val → Neutral
    deriving Inhabited

  structure Closure where
    body : Expr
    env  : List Val
    deriving Inhabited
end

abbrev Env := List Val

def Val.isNeutral : Val → Bool
  | .neutral _ => true
  | _ => false

/-- Default recursive-head unfold bound. Enough to compute through
    any small concrete dNat numeral (each `dsucc` layer costs one
    unfold for the fix and one for the resulting ι) while stopping
    the `(dsucc m)→Type` self-reference after one round. -/
def unfBound : Nat := 32

mutual
  /-- `unf` bounds the number of recursive-head (fix/ι) unfolds in
      the current application chain. Unlike absEval's `muSeen` it
      doesn't try syntactic cycle detection — closures share
      structure so the chain is linear, and a small bound suffices
      to compute through any concrete dNat numeral while stopping
      the `(dsucc m)→Type` self-reference in done_'s annotation. -/
  partial def eval (fuel unf : Nat) (env : Env) (e : Expr) : Option Val :=
    match fuel with
    | 0 => none
    | fuel + 1 =>
      match e with
      | .type => some .type
      | .bvar k => env[k]?
      | .lam dom body => do
          let dom' ← eval fuel unf env dom
          some (.lam dom' ⟨body, env⟩)
      | .iota ann body => do
          let ann' ← eval fuel unf env ann
          some (.iota ann' ⟨body, env⟩)
      | .fix ann body => do
          let ann' ← eval fuel unf env ann
          some (.fix ann' ⟨body, env⟩)
      | .app f a => do
          let f' ← eval fuel unf env f
          let a' ← eval fuel unf env a
          vapp fuel unf f' a'
      | .letE v body => do
          let v' ← eval fuel unf env v
          eval fuel unf (v' :: env) body
      | .asc _t ty =>
          eval fuel unf env ty

  partial def vapp (fuel unf : Nat) (f a : Val) : Option Val :=
    match fuel with
    | 0 => none
    | fuel + 1 =>
      match f with
      | .lam _dom ⟨body, env⟩ =>
          eval fuel unf (a :: env) body
      | .iota _ann ⟨body, env⟩ =>
          if a.isNeutral || unf == 0 then
            some (.neutral (.stuckRec f a))
          else do
            let f' ← eval fuel (unf - 1) (f :: env) body
            vapp fuel (unf - 1) f' a
      | .fix _ann ⟨body, env⟩ =>
          if a.isNeutral || unf == 0 then
            some (.neutral (.stuckRec f a))
          else do
            let f' ← eval fuel (unf - 1) (f :: env) body
            vapp fuel (unf - 1) f' a
      | .neutral n => some (.neutral (.app n a))
      | .type => some (.neutral (.stuckRec f a))
end

mutual
  /-- Read a value back to an expression. `depth` is the number of
      binders opened so far (= the next fresh de Bruijn level). -/
  partial def quote (fuel depth : Nat) (v : Val) : Option Expr :=
    match fuel with
    | 0 => none
    | fuel + 1 =>
      match v with
      | .type => some .type
      | .neutral n => quoteNeutral fuel depth n
      | .lam dom cl => do
          let dom' ← quote fuel depth dom
          let body' ← quoteClosure fuel depth cl
          some (.lam dom' body')
      | .iota ann cl => do
          let ann' ← quote fuel depth ann
          let body' ← quoteClosure fuel depth cl
          some (.iota ann' body')
      | .fix ann cl => do
          let ann' ← quote fuel depth ann
          let body' ← quoteClosure fuel depth cl
          some (.fix ann' body')

  partial def quoteClosure (fuel depth : Nat) (cl : Closure) : Option Expr := do
    let bv := Val.neutral (.var depth)
    -- Opening a closure under a *neutral* fresh variable: any
    -- recursive-head application to that variable is stuck by
    -- the `a.isNeutral` gate, so the unfold bound here only
    -- matters for *closed* recursive applications captured in
    -- the environment. Use a small bound so the self-referential
    -- type annotations (e.g. `(dsucc m)→Type` in done_) terminate
    -- after one round.
    let v ← eval fuel 1 (bv :: cl.env) cl.body
    quote fuel (depth + 1) v

  partial def quoteNeutral (fuel depth : Nat) (n : Neutral) : Option Expr :=
    match fuel with
    | 0 => none
    | fuel + 1 =>
      match n with
      | .var level =>
          if level < depth then some (.bvar (depth - 1 - level)) else none
      | .app n' v => do
          let f ← quoteNeutral fuel depth n'
          let a ← quote fuel depth v
          some (.app f a)
      | .stuckRec f a => do
          let f' ← quote fuel depth f
          let a' ← quote fuel depth a
          some (.app f' a')
end

/-- Normalize a closed expression. -/
def nf (fuel : Nat) (e : Expr) : Option Expr := do
  let v ← eval fuel unfBound [] e
  quote fuel 0 v

/-- Normalize an expression with `ctxLen` free variables. Each becomes
    a fresh neutral at the corresponding level. -/
def nfIn (fuel : Nat) (ctxLen : Nat) (e : Expr) : Option Expr := do
  let env := (List.range ctxLen).reverse.map (fun lvl => Val.neutral (.var lvl))
  let v ← eval fuel unfBound env e
  quote fuel ctxLen v

/-- `Except`-flavoured `nfIn` so call sites that currently use
    `absEval` can swap without changing their error plumbing. -/
def nfInE (fuel : Nat) (ctxLen : Nat) (e : Expr) : Except String Expr :=
  match nfIn fuel ctxLen e with
  | some e' => .ok e'
  | none => .error "NbE: out of fuel"

end NbE
