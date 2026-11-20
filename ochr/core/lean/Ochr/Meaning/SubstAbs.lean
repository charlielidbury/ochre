import Ochr.Meaning.Lemmas

/-!
# Replacing an unknown by what it means: the substitution lemma for unknowns (docs/31 D77)

The counterpart, for unknowns, of `meanV_substLoan` / `run_substLoan` (`Lemmas.lean`, beside the
congruence lemmas `meanV_congr` / `run_congr`): under an assignment at which `ρ σ = ⟦r⟧`
(`Steps.RefineOk`), substituting `r` for `σ` in a value, a type or a program's text keeps the meaning
and the run. It is what `Steps.substEnv_abs_step_stmt` (a refinement's substitution over the whole
state) owes underneath: every position, stored type and record means the same, and a sealed program
whose text changed means the same before its re-run (whose meaning is [Seal]'s, `nfSealed_step`).

**Which proofs it reuses.** For a loan, `meanV_substLoan` is the congruence lemma (move to the
future fixed at `ℓ`) followed by `meanV_substSame` / `runT_substSame` (`RunSubst.lean`: at a future
where `loan ℓ` already means the filler, substituting it changes nothing, clause by clause). For an
unknown no congruence step is needed: the assignment already gives `σ` the refinement's meaning, so
the lemma IS the same-meaning substitution, with the atom `.abs σ` in place of `.loan ℓ`. That
induction does not look at which atom it replaces except in its base case, so the proof is
`RunSubst.lean`'s induction generalised from a loan to an atom (`FillOK` per atom), not a fifth
induction: provided its base case holds, the hypothesis `AbsFillOK` below.

**The base case fails today, at the type the run gives an embedded value** (`absFill_shape_false`,
kernel-checked). `run`'s `.val` clause types `.abs σ` at `Δ σ` and every other data value at the
HINT: `.val (.abs σ)` and `.val Z` mean the same where `ρ σ = 0` and are typed `Nat` and `err`. So the
run-level lemma with whole results is false (`run_substAbs_false`, the text `.val σ` itself), and the
substituted text's `let` binds its value at `err` where the original bound it at `Δ σ`. Where the
type is not read again, nothing changes: on the `SplitSubst` runs the meanings and even the whole
runs agree (`pred2_instance`), since a call reads its arguments' meanings only. Two ways out:
1. (recommended) the run's `.val` clause types a number at `Nat` and a constructor value that
   records its parameters at its own type `D(ps̄)`, as the checker types them. Then `AbsFillOK.shape`
   holds wherever `DeltaOk` does (a refinement of `σ` is a value of `σ`'s stored type, which is what
   `Δ σ` is the code of), and the lemma is the generalised `runT_substSame`. A change to a data
   clause of `Run.lean`, so after the data-layer port.
2. state it up to types (result types and the types bindings store): then it is a new induction (a
   simulation between states whose binding types differ but whose meanings agree).
-/

namespace Ochr

mutual
/-- Replace every unknown `σ` by `r` in a value, inside sealed programs, closures and types too
(the pure half of the checker's `substV (.abs σ) r`; re-normalisation is a separate step). -/
def Value.substAbs (σ : Nat) (r : Value) : Value → Value
  | .abs σ' => if σ' = σ then r else .abs σ'
  | .succ v => .succ (Value.substAbs σ r v)
  | .tRef v => .tRef (Value.substAbs σ r v)
  | .borrow m v => .borrow m (Value.substAbs σ r v)
  | .gloan m v => .gloan m (Value.substAbs σ r v)
  | .tEq A a b => .tEq (Value.substAbs σ r A) (Value.substAbs σ r a) (Value.substAbs σ r b)
  | .clo cs t rd => .clo (Value.substAbsList σ r cs) (Term.substAbs σ r t) (Value.substAbsRd σ r rd)
  | .tPi cs t rd => .tPi (Value.substAbsList σ r cs) (Term.substAbs σ r t) (Value.substAbsRd σ r rd)
  | .sealed t => .sealed (Term.substAbs σ r t)
  | .ind ty c h ps fs => .ind ty c h (Value.substAbsList σ r ps) (Value.substAbsList σ r fs)
  | .tInd n as => .tInd n (Value.substAbsList σ r as)
  | v => v
termination_by structural v => v

def Value.substAbsList (σ : Nat) (r : Value) : List Value → List Value
  | [] => []
  | v :: vs => Value.substAbs σ r v :: Value.substAbsList σ r vs
termination_by structural vs => vs

def Value.substAbsRd (σ : Nat) (r : Value) : List (DeclInfo × Value) → List (DeclInfo × Value)
  | [] => []
  | (d, v) :: vs => (d, Value.substAbs σ r v) :: Value.substAbsRd σ r vs
termination_by structural vs => vs

def Term.substAbs (σ : Nat) (r : Value) : Term → Term
  | .val v => .val (Value.substAbs σ r v)
  | .assign p t => .assign p (Term.substAbs σ r t)
  | .letIn h t u => .letIn h (Term.substAbs σ r t) (Term.substAbs σ r u)
  | .seq t u => .seq (Term.substAbs σ r t) (Term.substAbs σ r u)
  | .matchNat p z s => .matchNat p (Term.substAbs σ r z) (Term.substAbs σ r s)
  | .pi hs ds c => .pi hs (Term.substAbsList σ r ds) (Term.substAbs σ r c)
  | .fix f hs ds c d b => .fix f hs (Term.substAbsList σ r ds) (Term.substAbs σ r c) d (Term.substAbs σ r b)
  | .call f as h => .call (Term.substAbs σ r f) (Term.substAbsList σ r as) h
  | .succ t => .succ (Term.substAbs σ r t)
  | .eq A a b => .eq (Term.substAbs σ r A) (Term.substAbs σ r a) (Term.substAbs σ r b)
  | .cong f h => .cong (Term.substAbs σ r f) (Term.substAbs σ r h)
  | .ref A => .ref (Term.substAbs σ r A)
  | .id A a b => .id (Term.substAbs σ r A) (Term.substAbs σ r a) (Term.substAbs σ r b)
  | .ascribe t A => .ascribe (Term.substAbs σ r t) (Term.substAbs σ r A)
  | .prim n as => .prim n (Term.substAbsList σ r as)
  | .tind n as => .tind n (Term.substAbsList σ r as)
  | .ctor ty c h ps as => .ctor ty c h (Term.substAbsList σ r ps) (Term.substAbsList σ r as)
  | .matchInd p ty arms => .matchInd p ty (Term.substAbsArms σ r arms)
  | t => t
termination_by structural t => t

def Term.substAbsList (σ : Nat) (r : Value) : List Term → List Term
  | [] => []
  | t :: ts => Term.substAbs σ r t :: Term.substAbsList σ r ts
termination_by structural ts => ts

def Term.substAbsArms (σ : Nat) (r : Value) : List (Hint × Term) → List (Hint × Term)
  | [] => []
  | (h, t) :: ts => (h, Term.substAbs σ r t) :: Term.substAbsArms σ r ts
termination_by structural ts => ts
end

end Ochr

namespace Ochr.Meaning

section
variable (K : RunCtx) (ρ : Assignment)

/-- The decisions do not see the substitution of `r` for `σ` (`DecInvariant`'s counterpart; for a
data unknown and a constructor refinement the real `Decide` reads both `.other`: `valueDecl`'s
frozen reading of a data unknown is `valTypeDecl` of its type, `.other`, and a constructor value's
is `.other`). -/
def DecInvariantAbs (D : Decisions) (σ : Nat) (r : Value) : Prop :=
  (∀ sc t, D.flags sc (Term.substAbs σ r t) = D.flags sc t) ∧
  (∀ sc t, D.declOf sc (Term.substAbs σ r t) = D.declOf sc t) ∧
  (∀ sc t, D.piSort sc (Term.substAbs σ r t) = D.piSort sc t) ∧
  (∀ sc e t, D.joinMoves sc e (Term.substAbs σ r t) = D.joinMoves sc e t) ∧
  (∀ sc t, D.rePointed sc (Term.substAbs σ r t) = D.rePointed sc t) ∧
  (∀ sc t, D.typeDecl sc (Term.substAbs σ r t) = D.typeDecl sc t) ∧
  (∀ sc e t, D.blockCaps sc e (Term.substAbs σ r t) = D.blockCaps sc e t)

/-- What the substitution of `r` for `σ` needs (`FillOK`'s counterpart; no future is fixed, the
assignment already gives `σ` its value): `r` means `ρ σ` at every hint, the run types the embedded
`r` as it types the embedded `σ` (the base case of the induction), and the decisions do not see the
substitution. -/
structure AbsFillOK (ψ : Future) (σ : Nat) (r : Value) : Prop where
  mean : ∀ hint, meanV K ρ ψ hint r = ρ σ
  shape : ∀ hint s, (run K ρ ψ hint (.val r) s).map (·.1.2) = (run K ρ ψ hint (.val (.abs σ)) s).map (·.1.2)
  dec : DecInvariantAbs K.D σ r

/-- **Replacing an unknown by what it means keeps a value's meaning** (open; the proof is
`meanV_substSame`'s, `RunSubst.lean`, with the atom generalised from `loan ℓ` to `.abs σ`: the
mutual induction with the run below). -/
theorem meanV_substAbs (ψ : Future) (σ : Nat) (r : Value) (hF : AbsFillOK K ρ ψ σ r) (v : Value) (hint : TyS) :
    meanV K ρ ψ hint (Value.substAbs σ r v) = meanV K ρ ψ hint v := by
  sorry

/-- **Replacing an unknown by what it means keeps a program's run** (open; `runT_substSame`'s
induction with the atom generalised; at a `.fix` the stages' bodies agree by the same lemma,
`fixBodyAt_bodyEq`, `fixStage_bodyEq`, `fixG_bodyEq`, which are already stated for any body pair). -/
theorem run_substAbs (ψ : Future) (σ : Nat) (r : Value) (hF : AbsFillOK K ρ ψ σ r) (tl : Bool) (t : Term)
    (hint : TyS) : runT K ρ ψ tl hint (Term.substAbs σ r t) = runT K ρ ψ tl hint t := by
  sorry

theorem TyM.err_ne_nat : TyM.err ≠ TyM.nat := fun h => by
  have := congrArg TyM.isErr h
  simp [TyM.isErr, TyM.err, TyM.nat] at this

/-- **The base case fails as the run stands** (kernel-checked): where `Δ σ` is `Nat` and `ρ σ = 0`,
`.val Z` means `σ`'s value but is typed at the hint, `.val σ` at `Δ σ`. -/
theorem absFill_shape_false (ψ : Future) (hΔ : K.Δ 0 = .plain TyM.nat) (s : SState) :
    (run K ρ ψ (.plain .err) (.val .zero) s).map (·.1.2) ≠ (run K ρ ψ (.plain .err) (.val (.abs 0)) s).map (·.1.2) := by
  rw [run_val_def, run_val_def]
  simp only [Option.map_some]
  intro h
  have h' := congrArg (fun x => x.map TyS.m) h
  simp only [Option.map_some] at h'
  have e1 : (valT K ρ ψ (.plain .err) Value.zero).m = TyM.err := rfl
  have e2 : (valT K ρ ψ (.plain .err) (.abs 0)).m = TyM.nat := by
    show (K.Δ 0).m = TyM.nat
    rw [hΔ]; rfl
  simp only [Option.some.injEq] at h'
  exact TyM.err_ne_nat (e1.symm.trans (h'.trans e2))

/-- **So the run-level lemma with whole results is false today**, at the simplest text, `.val σ`,
although both sides mean `0` (the type differs; a `let` would store it). -/
theorem run_substAbs_false (ψ : Future) (hΔ : K.Δ 0 = .plain TyM.nat) (s : SState) :
    run K ρ ψ (.plain .err) (Term.substAbs 0 .zero (.val (.abs 0))) s ≠ run K ρ ψ (.plain .err) (.val (.abs 0)) s := by
  intro h
  exact absFill_shape_false K ρ ψ hΔ s (by
    show (run K ρ ψ (.plain .err) (Term.substAbs 0 .zero (.val (.abs 0))) s).map (·.1.2) = _
    rw [h])

end

end Ochr.Meaning
