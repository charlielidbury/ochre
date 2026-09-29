import Ochr.Fuzz.Run

/-!
# Fuzzer: shrinking a counterexample

Greedy, deterministic delta debugging on the surface program: repeatedly try the
candidates below in order (largest reductions first) and keep the first one on which
the checker still reports a finding of the same kind, until none applies or the budget
of checks is spent. Candidates that do not resolve or are rejected simply fail the
predicate.
-/

namespace Ochr.Fuzz
open Ochr.Surface

/-- Replacements for a term at its root, biggest reductions first. -/
def rootCands : STerm → List STerm
  | .letIn _ _ e b => [b, e]
  | .seq a b => [b, a]
  | .matchGen _ arms => arms.map (·.2.2)
  | .app "S" [a] => [a, .num 0]
  | .app "Id" [_, _, _] => [.top]
  | .app "Eq" [_, _, _] => [.top]
  | .and a b => [a, b]
  | .call _ as => as ++ [.num 0, .unitLit, .top]
  | .assign _ _ => [.unitLit]
  | .num n => if n == 0 then [] else [.num 0, .num (n - 1)]
  | .fix _ _ _ _ b => [b]
  | .ascribe a _ => [a]
  | .rewrite _ _ t | .split _ t => [t]
  | .splitArms _ arms => arms.map (·.2.2)
  | .andI _ _ => [.ident "refl", .num 0]
  | .ident _ | .unitLit | .top | .sort _ => []
  | _ => [.num 0, .unitLit]

/-- Every one-step shrink of a term: a root replacement, or a shrink of one child. -/
partial def shrinkT (t : STerm) : List STerm :=
  rootCands t ++ match t with
  | .letIn x a e b => (shrinkT e).map (.letIn x a · b) ++ (shrinkT b).map (.letIn x a e ·)
      ++ (if a.isSome then [.letIn x none e b] else [])
  | .seq a b => (shrinkT a).map (.seq · b) ++ (shrinkT b).map (.seq a ·)
  | .matchGen sc arms =>
      (List.range arms.length).flatMap fun i =>
        let (c, vs, b) := arms[i]!
        (shrinkT b).map fun b' => .matchGen sc (arms.set i (c, vs, b'))
  | .app f as => (List.range as.length).flatMap fun i => (shrinkT as[i]!).map fun a' => .app f (as.set i a')
  | .call f as => (List.range as.length).flatMap fun i => (shrinkT as[i]!).map fun a' => .call f (as.set i a')
  | .assign p e => (shrinkT e).map (.assign p ·)
  | .and a b => (shrinkT a).map (.and · b) ++ (shrinkT b).map (.and a ·)
  | .andI a b => (shrinkT a).map (.andI · b) ++ (shrinkT b).map (.andI a ·)
  | .ctorP c ps as => (List.range as.length).flatMap fun i => (shrinkT as[i]!).map fun a' => .ctorP c ps (as.set i a')
  | .fix f bs r d b => (shrinkT b).map (.fix f bs r d ·)
  | .ascribe a A => (shrinkT a).map (.ascribe · A)
  | .rewrite rev h t => (shrinkT t).map (.rewrite rev h ·)
  | .split f t => (shrinkT t).map (.split f ·)
  | .splitArms f arms =>
      (List.range arms.length).flatMap fun i =>
        let (c, vs, b) := arms[i]!
        (shrinkT b).map fun b' => .splitArms f (arms.set i (c, vs, b'))
  | _ => []

/-- Are all identifiers bound (by a binder, a pattern, a declaration, a constructor or a
builtin)? The shrinker keeps only well-scoped candidates, so counterexamples print as
valid programs. -/
partial def scopedT (names : List String) (bound : List String) : STerm → Bool
  | .ident x => bound.contains x || names.contains x ||
      ["Nat", "Unit", "Z", "refl", "S", "F", "T", "Nil", "Cons", "MkB", "Mk", "Pair", "B2", "L", "Box",
       "False", "True", "I", "And", "Intro", "Or", "Inl", "Inr", "ExN", "Wit"].contains x
  | .num _ | .unitLit | .top | .sort _ => true
  | .app _ as => as.all (scopedT names bound)
  | .call f as => scopedT names bound f && as.all (scopedT names bound)
  | .ctorP _ ps as => (ps ++ as).all (scopedT names bound)
  | .deref t | .proj _ t | .amp t => scopedT names bound t
  | .assign p t => scopedT names bound p && scopedT names bound t
  | .letIn x A t u => (A.map (scopedT names bound)).getD true && scopedT names bound t && scopedT names (x :: bound) u
  | .split _ t => scopedT names bound t
  | .splitArms _ arms => arms.all fun (_, vs, b) => scopedT names (vs ++ bound) b
  | .rewrite _ a b
  | .seq a b | .pair a b | .andI a b | .and a b | .prod a b | .ascribe a b | .arrow a b =>
      scopedT names bound a && scopedT names bound b
  | .matchGen sc arms => scopedT names bound sc && arms.all fun (_, vs, b) => scopedT names (vs ++ bound) b
  | .pi bs c => scopedBs names bound bs c
  | .fix f bs r _ b => scopedBs names bound bs r && scopedT names ((bs.map (·.1)).reverse ++ f :: bound) b
where
  scopedBs (names bound : List String) : List (String × STerm) → STerm → Bool
    | [], c => scopedT names bound c
    | (x, A) :: bs, c => scopedT names bound A && scopedBs names (x :: bound) bs c

def Case.wellScoped (c : Case) : Bool :=
  let names := c.decls.map (·.name)
  let ps := c.params.map (·.1)
  scopedT names ps c.lhs && scopedT names ps c.rhs &&
    c.extra.all (fun d => scopedT names (d.name :: d.params.map (·.1)) d.body) &&
    (match c.conv with
      | some (_, f, g) => scopedT names [] f && scopedT names [] g
      | none => true)

/-- Every one-step shrink of a case. -/
def shrinkCase (c : Case) : List Case := (shrinkCase' c).filter Case.wellScoped
where shrinkCase' (c : Case) : List Case :=
  (c.lib.map fun n => { c with lib := c.lib.erase n }) ++
  ((List.range c.extra.length).map fun i => { c with extra := c.extra.eraseIdx i }) ++
  ((List.range c.params.length).map fun i => { c with params := c.params.eraseIdx i }) ++
  ((shrinkT c.rhs).map fun r => { c with rhs := r }) ++
  ((shrinkT c.lhs).map fun l => { c with lhs := l }) ++
  ((List.range c.extra.length).flatMap fun i =>
    let d := c.extra[i]!
    (shrinkT d.body).map fun b => { c with extra := c.extra.set i { d with body := b } }) ++
  (match c.conv with
    | some (T, f, g) => [{ c with conv := none }] ++ (shrinkT f).map (fun f' => { c with conv := some (T, f', g) })
        ++ (shrinkT g).map (fun g' => { c with conv := some (T, f, g') })
    | none => [])

/-- Does the case still show a finding of this kind (and, with a baseline, is it absent
under the baseline rules)? -/
def stillFails (o : Opts) (r : Rng) (key : String) (c : Case) : Option Finding :=
  match (checkCase o c r).findings.find? (·.key == key) with
  | none => none
  | some f => match o.base with
    | some b => if ((checkCase { o with cfg := b, base := none } c r).findings.any (·.key == key)) then none else some f
    | none => some f

/-- Shrink greedily; returns the smallest failing case found and its finding. -/
partial def shrink (o : Opts) (r : Rng) (k : String) (c : Case) (f : Finding) (budget : Nat := 4000) :
    Case × Finding × Nat := Id.run do
  let mut cur := c
  let mut fcur := f
  let mut spent := 0
  let mut progress := true
  while progress && spent < budget do
    progress := false
    for c' in shrinkCase cur do
      if spent ≥ budget then break
      spent := spent + 1
      if let some f' := stillFails o r k c' then
        cur := c'
        fcur := f'
        progress := true
        break
  pure (cur, fcur, spent)

end Ochr.Fuzz
