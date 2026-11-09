import Ochr.Meaning.Sem

/-!
# Pure substitution of a loan (for the sealed-substitution lemma)

The checker's substitution (`Machine.substV`) re-normalises the sealed programs it changes, so
it is monadic. The substitution lemma of docs/27 Lemma 3, "filling a loan is fixing the future",
is about the *pure* substitution: `⟦v[loan ℓ := w]⟧_{ρ,φ} = ⟦v⟧_{ρ, φ[ℓ ↦ ⟦w⟧]}` for `w` not
mentioning `ℓ`. Re-normalisation keeping the meaning is a separate step lemma (a sealed program
means its run, and its run after substitution is its run under the fixed future). This file
defines the pure substitution on values and terms.
-/

namespace Ochr

mutual
/-- Replace every `loan l` by `w` in a value, inside sealed programs, closures and types too. -/
def Value.substLoan (l : Nat) (w : Value) : Value → Value
  | .loan l' => if l' = l then w else .loan l'
  | .succ v => .succ (Value.substLoan l w v)
  | .tRef v => .tRef (Value.substLoan l w v)
  | .borrow m v => .borrow m (Value.substLoan l w v)
  | .tEq A a b => .tEq (Value.substLoan l w A) (Value.substLoan l w a) (Value.substLoan l w b)
  | .clo cs t rd => .clo (Value.substLoanList l w cs) (Term.substLoan l w t) (Value.substLoanRd l w rd)
  | .tPi cs t rd => .tPi (Value.substLoanList l w cs) (Term.substLoan l w t) (Value.substLoanRd l w rd)
  | .sealed t => .sealed (Term.substLoan l w t)
  | .ind ty c h ps fs => .ind ty c h (Value.substLoanList l w ps) (Value.substLoanList l w fs)
  | .tInd n as => .tInd n (Value.substLoanList l w as)
  | v => v
termination_by structural v => v

def Value.substLoanList (l : Nat) (w : Value) : List Value → List Value
  | [] => []
  | v :: vs => Value.substLoan l w v :: Value.substLoanList l w vs
termination_by structural vs => vs

def Value.substLoanRd (l : Nat) (w : Value) : List (DeclInfo × Value) → List (DeclInfo × Value)
  | [] => []
  | (d, v) :: vs => (d, Value.substLoan l w v) :: Value.substLoanRd l w vs
termination_by structural vs => vs

def Term.substLoan (l : Nat) (w : Value) : Term → Term
  | .val v => .val (Value.substLoan l w v)
  | .assign p t => .assign p (Term.substLoan l w t)
  | .letIn h t u => .letIn h (Term.substLoan l w t) (Term.substLoan l w u)
  | .seq t u => .seq (Term.substLoan l w t) (Term.substLoan l w u)
  | .matchNat p z s => .matchNat p (Term.substLoan l w z) (Term.substLoan l w s)
  | .pi hs ds c => .pi hs (Term.substLoanList l w ds) (Term.substLoan l w c)
  | .fix f hs ds c d b => .fix f hs (Term.substLoanList l w ds) (Term.substLoan l w c) d (Term.substLoan l w b)
  | .call f as h => .call (Term.substLoan l w f) (Term.substLoanList l w as) h
  | .succ t => .succ (Term.substLoan l w t)
  | .eq A a b => .eq (Term.substLoan l w A) (Term.substLoan l w a) (Term.substLoan l w b)
  | .cong f h => .cong (Term.substLoan l w f) (Term.substLoan l w h)
  | .ref A => .ref (Term.substLoan l w A)
  | .id A a b => .id (Term.substLoan l w A) (Term.substLoan l w a) (Term.substLoan l w b)
  | .ascribe t A => .ascribe (Term.substLoan l w t) (Term.substLoan l w A)
  | .prim n as => .prim n (Term.substLoanList l w as)
  | .tind n as => .tind n (Term.substLoanList l w as)
  | .ctor ty c h ps as => .ctor ty c h (Term.substLoanList l w ps) (Term.substLoanList l w as)
  | .matchInd p ty arms => .matchInd p ty (Term.substLoanArms l w arms)
  | t => t
termination_by structural t => t

def Term.substLoanList (l : Nat) (w : Value) : List Term → List Term
  | [] => []
  | t :: ts => Term.substLoan l w t :: Term.substLoanList l w ts
termination_by structural ts => ts

def Term.substLoanArms (l : Nat) (w : Value) : List (Hint × Term) → List (Hint × Term)
  | [] => []
  | (h, t) :: ts => (h, Term.substLoan l w t) :: Term.substLoanArms l w ts
termination_by structural ts => ts
end

end Ochr
