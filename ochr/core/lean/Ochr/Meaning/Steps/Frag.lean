import Ochr.Meaning.Steps.FragRead

/-!
# The fragment theorem: the simulation for EVERY term of a small fragment, by induction (lead10)

The fragment: `Z`, `S(u)`, a read of a number variable, `let x = u; w`, `u; w`, `&x` of a number
variable, `x := u` at a number variable, `*y := u` through a borrow, nested arbitrarily, at `Nat`,
`Unit` and `&Nat` (`FTy`, a typing of the top frame's variables, innermost first). Its checker states
(`FSt`): every position holds a fragment value (`FVal`), no temporary a loan, a loan and a borrow of
each label at one position each, every loan's borrow held at a binding pushed after its lender, the
top frame's bindings typed and read as `Γ` says.

The statement (`frag_sim`) is `eval_sim`'s at every fragment term, fuel, `Δ` and assignment: the
step at `eval` (`EvalSim`) from a state meeting `FSt Γ`. It is proved by induction on the typing,
each sub-term's simulation an INDUCTION HYPOTHESIS at every extension of `Δ` and the assignment
(a `let`'s tail runs after its right-hand side made unknowns). The facts about the checker it uses
are named `Prop`s (`FragMachine.lean`, and `FragRun` below: what a fragment term's checker run
leaves, itself an induction over the inversion facts, for the machine lane); the decisions it reads
are `FragDec`, a fact about the aligned table at fragment scopes.
-/

namespace Ochr.Meaning.Steps.Form

open Ochr Ochr.Meaning Ochr.Meaning.Steps
open Classical

/-- The fragment's types. -/
inductive FT where
  | nat | unit | ref
  deriving DecidableEq

/-- A fragment type as the checker's type. -/
def FT.ty : FT → Value
  | .nat => .tNat
  | .unit => .tUnit
  | .ref => .tRef .tNat

/-- A fragment type's declared reading (the reading a `let` binding of that type gets). -/
def FT.rd : FT → DeclInfo
  | .nat => .other
  | .unit => .unit
  | .ref => .ref .other

/-- The values a binding of a fragment type holds: a number, `⊥` or a loan; `()` or `⊥`; `⊥` or a
borrow of a number. -/
def FT.holds : FT → Value → Prop
  | .nat, v => v.Num ∨ v = .bot ∨ ∃ l, v = .loan l
  | .unit, v => v = .unit ∨ v = .bot
  | .ref, v => v = .bot ∨ ∃ l w, v = .borrow l w ∧ w.Num

/-- **The fragment's typing**, `Γ` the top frame's variables' types, innermost first. -/
inductive FTy : List FT → Term → FT → Prop
  | zero (Γ : List FT) : FTy Γ .zero .nat
  | succ (Γ : List FT) (u : Term) : FTy Γ u .nat → FTy Γ (.succ u) .nat
  | var (Γ : List FT) (i : Nat) : Γ[i]? = some .nat → FTy Γ (.place (.var i)) .nat
  | bor (Γ : List FT) (i : Nat) : Γ[i]? = some .nat → FTy Γ (.borrow (.var i)) .ref
  | asg (Γ : List FT) (i : Nat) (u : Term) : Γ[i]? = some .nat → FTy Γ u .nat → FTy Γ (.assign (.var i) u) .unit
  | asgD (Γ : List FT) (i : Nat) (u : Term) : Γ[i]? = some .ref → FTy Γ u .nat →
      FTy Γ (.assign (.deref (.var i)) u) .unit
  | letIn (Γ : List FT) (x : Hint) (u w : Term) (A B : FT) : FTy Γ u A → FTy (A :: Γ) w B → FTy Γ (.letIn x u w) B
  | seq (Γ : List FT) (u w : Term) (A B : FT) : FTy Γ u A → FTy Γ w B → FTy Γ (.seq u w) B

/-- **The fragment's checker states** at the typing `Γ` of the top frame's variables. -/
structure FSt (Γ : List FT) (st : MState) : Prop where
  vals : ∀ q ∈ allPos st.env, FVal (valAt st.env q)
  /-- no temporary holds a loan or a borrow (the fragment parks no borrow across a sub-term) -/
  temps : ∀ f i, (Pos.temp f i) ∈ allPos st.env → (valAt st.env (.temp f i)).Num ∨ valAt st.env (.temp f i) = .unit
  loan1 : ∀ q q' l, q ∈ allPos st.env → q' ∈ allPos st.env → valAt st.env q = .loan l → valAt st.env q' = .loan l → q = q'
  bor1 : ∀ q q' l w w', q ∈ allPos st.env → q' ∈ allPos st.env → valAt st.env q = .borrow l w →
    valAt st.env q' = .borrow l w' → q = q'
  /-- every loan's borrow is held (the checker's D111), at a binding -/
  held : ∀ q l, q ∈ allPos st.env → valAt st.env q = .loan l → ∃ f j c, Pos.bind f j ∈ allPos st.env ∧
    valAt st.env (.bind f j) = .borrow l c
  /-- every borrow's lender is in the environment -/
  lender : ∀ q l c, q ∈ allPos st.env → valAt st.env q = .borrow l c → ∃ q', q' ∈ allPos st.env ∧
    valAt st.env q' = .loan l
  /-- the top frame's variables, as `Γ` types them -/
  top : ∀ i A, Γ[i]? = some A → ∃ f j b, ckVarPos st.env i = some (.bind f j) ∧
    st.env[f]?.bind (fun fr : Frame => fr.binds[j]?) = some b ∧ b.ty = some A.ty ∧ b.decl = A.rd ∧ A.holds b.val
  /-- a lender's binding precedes its holder's (`&x` needs `x` in scope, and no write stores a borrow
  into an older binding): so the binding a `let` drops lends to none but the value in flight -/
  order : ∀ f j f' j' l c, Pos.bind f j ∈ allPos st.env → Pos.bind f' j' ∈ allPos st.env →
    valAt st.env (.bind f j) = .loan l → valAt st.env (.bind f' j') = .borrow l c → f < f' ∨ (f = f' ∧ j < j')
  /-- a lent binding is a number variable (only `&x` of one lends) -/
  lent : ∀ (f j : Nat) (b : Binding) (l : Nat), st.env[f]?.bind (fun fr : Frame => fr.binds[j]?) = some b → b.val = .loan l →
    b.ty = some .tNat ∧ b.decl = .other

/-- A binding found by lookup is a position, holding its value. -/
theorem lookup_pos {env : Env} {f j : Nat} {b : Binding} (hb : env[f]?.bind (fun fr : Frame => fr.binds[j]?) = some b) :
    Pos.bind f j ∈ allPos env ∧ valAt env (.bind f j) = b.val := by
  rcases hfr : env[f]? with _ | fr
  · rw [hfr] at hb; cases hb
  · rw [hfr] at hb; simp only [Option.bind_some] at hb
    refine ⟨bind_mem_allPos env f j fr b hfr hb, ?_⟩
    rw [valAt_bind_eq, hfr]; simp [hb]

namespace FSt
variable {Γ : List FT} {st : MState} (h : FSt Γ st)
include h

theorem tempNoLoan : ∀ f i m, Pos.temp f i ∈ allPos st.env → valAt st.env (.temp f i) ≠ .loan m := by
  intro f i m hq e
  rcases h.temps f i hq with hn | hu
  · rw [e] at hn; cases hn
  · rw [e] at hu; cases hu

/-- The end of the borrow lent by a number binding holding `loan_l`. -/
theorem fend {f j l : Nat} (hp : Pos.bind f j ∈ allPos st.env) (hx : valAt st.env (.bind f j) = .loan l) :
    ∃ f' j' c, FEnd st.env (.bind f j) (.bind f' j') l c := by
  obtain ⟨f', j', c, hph, hy⟩ := h.held _ l hp hx
  have hc : c.Num := by
    have := h.vals _ hph; rw [hy] at this
    cases this with
    | num hn => cases hn
    | bor m hw => exact hw
  exact ⟨f', j', c, ⟨h.vals, h.tempNoLoan, hp, hph, hx, hy, hc,
    fun q hq e => h.loan1 q _ l hq hp e hx, fun q hq w e => h.bor1 q _ l w c hq hph e hy⟩⟩

theorem loansLive : ∀ q ∈ allPos st.env, ∀ m, valAt st.env q = .loan m → liveLoan st.env m = true := by
  intro q hq m e
  obtain ⟨f', j', c, hph, hy⟩ := h.held q m hq e
  unfold liveLoan findBorrow
  exact List.find?_isSome.mpr ⟨_, hph, by rw [hy]; simp [Value.holdsBorrow]⟩

/-- **A number variable is read in one of three ways**: it holds a number, it is lent, or it was moved. -/
theorem var_cases {i : Nat} (hi : Γ[i]? = some .nat) :
    NumVar i st ∨ LentVar i st ∨ ∃ f j b, ckVarPos st.env i = some (.bind f j) ∧
      st.env[f]?.bind (fun fr : Frame => fr.binds[j]?) = some b ∧ b.val = .bot ∧ b.ty = some .tNat := by
  obtain ⟨f, j, b, hck, hb, hty, hrd, hv⟩ := h.top i .nat hi
  rcases hv with hn | hbot | ⟨l, hl⟩
  · exact .inl ⟨f, j, b, hck, hb, hn, hty⟩
  · exact .inr (.inr ⟨f, j, b, hck, hb, hbot, hty⟩)
  · obtain ⟨hp, hval⟩ := lookup_pos hb
    obtain ⟨f', j', c, he⟩ := h.fend hp (by rw [hval, hl])
    exact .inr (.inl ⟨f, j, b, f', j', l, c, hck, hb, hty, hrd, he, h.loansLive⟩)

end FSt

/-- `FSt` reads only the kernel's environment, which a temporary's stored type does not change. -/
theorem FSt.of_erase {Γ : List FT} {a b : MState} (he : a.env.erase = b.env.erase) (h : FSt Γ a) : FSt Γ b := by
  have hv : ∀ q, valAt b.env q = valAt a.env q := fun q => by rw [← valAt_erase, ← he, valAt_erase]
  have ha : allPos b.env = allPos a.env := by rw [← allPos_erase, ← he, allPos_erase]
  have hl : ∀ f j, b.env[f]?.bind (fun fr : Frame => fr.binds[j]?) = a.env[f]?.bind (fun fr : Frame => fr.binds[j]?) :=
    fun f j => by rw [← lookup_erase, ← he, lookup_erase]
  have hc : ∀ i, ckVarPos b.env i = ckVarPos a.env i := fun i => by rw [← ckVarPos_erase, ← he, ckVarPos_erase]
  refine ⟨fun q hq => ?_, fun f i hq => ?_, fun q q' l hq hq' e e' => ?_, fun q q' l w w' hq hq' e e' => ?_,
    fun q l hq e => ?_, fun q l c hq e => ?_, fun i A hi => ?_,
    fun f j f' j' l c hq hq' e e' => h.order f j f' j' l c (ha ▸ hq) (ha ▸ hq') (by rw [← hv]; exact e)
      (by rw [← hv]; exact e'),
    fun f j b' l hb e => h.lent f j b' l (by rw [← hl]; exact hb) e⟩
  · rw [hv]; exact h.vals q (ha ▸ hq)
  · rw [hv]; exact h.temps f i (ha ▸ hq)
  · exact h.loan1 q q' l (ha ▸ hq) (ha ▸ hq') (by rw [← hv]; exact e) (by rw [← hv]; exact e')
  · exact h.bor1 q q' l w w' (ha ▸ hq) (ha ▸ hq') (by rw [← hv]; exact e) (by rw [← hv]; exact e')
  · obtain ⟨f, j, c, hp, hy⟩ := h.held q l (ha ▸ hq) (by rw [← hv]; exact e)
    exact ⟨f, j, c, ha ▸ hp, by rw [hv]; exact hy⟩
  · obtain ⟨q', hq', hx⟩ := h.lender q l c (ha ▸ hq) (by rw [← hv]; exact e)
    exact ⟨q', ha ▸ hq', by rw [hv]; exact hx⟩
  · obtain ⟨f, j, b', hck, hb, h1, h2, h3⟩ := h.top i A hi
    exact ⟨f, j, b', by rw [hc]; exact hck, by rw [hl]; exact hb, h1, h2, h3⟩

theorem FSt.kern {Γ : List FT} {a b : MState} (hk : Kern a b) (h : FSt Γ a) : FSt Γ b :=
  h.of_erase (congrArg (·.env) hk.norm)

/-- **The aligned table at the fragment's scopes** (a fact about the decisions, for the decisions'
lane): a fragment term of type `A` at a fragment state is classified neither a statement nor a
proof, and read `A.rd` (a `let`'s and a sequence's reading is its tail's). -/
def FragDec (D : Decisions) : Prop :=
  ∀ Γ t A st, FTy Γ t A → FSt Γ st →
    D.flags (DecideScope.topReadings st) t = (false, false) ∧ D.declOf (DecideScope.topReadings st) t = A.rd

/-- The values a fragment term of type `A` returns: a number; `()`; a borrow of a number. -/
def FT.val : FT → Value → Prop
  | .nat, v => v.Num
  | .unit, v => v = .unit
  | .ref, v => ∃ l c, v = .borrow l c ∧ c.Num

/-- **The fragment's checker states with a value in flight** (a run's end state with its value parked
as a temporary, `st'.withTempT v T?`): `FSt`, but a temporary may hold a borrow (the value in flight)
and a loan's borrow may be held there. -/
structure FStT (Γ : List FT) (st : MState) : Prop where
  vals : ∀ q ∈ allPos st.env, FVal (valAt st.env q)
  temps : ∀ f i, (Pos.temp f i) ∈ allPos st.env → (valAt st.env (.temp f i)).Num ∨
    valAt st.env (.temp f i) = .unit ∨ ∃ l c, valAt st.env (.temp f i) = .borrow l c
  loan1 : ∀ q q' l, q ∈ allPos st.env → q' ∈ allPos st.env → valAt st.env q = .loan l → valAt st.env q' = .loan l → q = q'
  bor1 : ∀ q q' l w w', q ∈ allPos st.env → q' ∈ allPos st.env → valAt st.env q = .borrow l w →
    valAt st.env q' = .borrow l w' → q = q'
  held : ∀ q l, q ∈ allPos st.env → valAt st.env q = .loan l → ∃ q' c, q' ∈ allPos st.env ∧
    valAt st.env q' = .borrow l c
  lender : ∀ q l c, q ∈ allPos st.env → valAt st.env q = .borrow l c → ∃ q', q' ∈ allPos st.env ∧
    valAt st.env q' = .loan l
  top : ∀ i A, Γ[i]? = some A → ∃ f j b, ckVarPos st.env i = some (.bind f j) ∧
    st.env[f]?.bind (fun fr : Frame => fr.binds[j]?) = some b ∧ b.ty = some A.ty ∧ b.decl = A.rd ∧ A.holds b.val
  order : ∀ f j f' j' l c, Pos.bind f j ∈ allPos st.env → Pos.bind f' j' ∈ allPos st.env →
    valAt st.env (.bind f j) = .loan l → valAt st.env (.bind f' j') = .borrow l c → f < f' ∨ (f = f' ∧ j < j')
  lent : ∀ (f j : Nat) (b : Binding) (l : Nat), st.env[f]?.bind (fun fr : Frame => fr.binds[j]?) = some b → b.val = .loan l →
    b.ty = some .tNat ∧ b.decl = .other

/-- **What a fragment term's typed run leaves** (a fact about the checker alone, by induction over
the fragment from the inversion facts; for the machine lane; it replaces `FragNatRun`): from a
fragment state, at any hint (the hint the checker hands a write's right-hand side is left free by
`AssignNumInv`/`AssignDerefInv`), entered as `eval` is entered in a typed run, the run returns a
value of the term's type at its type, in the same mode, with the top frame's readings and the
number of frames kept, and leaves a fragment state with that value in flight. -/
def FragRun (D : Decisions) : Prop :=
  ∀ Γ u A n hint st st' bh v T?, FTy Γ u A → FSt Γ st → Mode st →
    (st.tailDecl = none ∨ st.tailDecl = some (D.declOf (DecideScope.topReadings st) u)) → DecTab D st' →
    Runs (Ochr.eval n true u hint) st bh (v, T?) st' →
    T? = some A.ty ∧ A.val v ∧ ModeEq st st' ∧ DecideScope.topReadings st' = DecideScope.topReadings st ∧
    st'.env.size = st.env.size ∧ FStT Γ (st'.withTempT v T?)

/-- **A typed run of a fragment term at `Nat` returns a number at `Nat`** (a fact about the checker
alone, by induction over the fragment from the inversion facts; for the machine lane: the part of
the fragment's run facts the `S` case reads). -/
def FragNatRun (D : Decisions) : Prop :=
  ∀ Γ u n st st' bh v T?, FTy Γ u .nat → FSt Γ st → Mode st → st.tailDecl = none → DecTab D st' →
    Runs (Ochr.eval n true u none) st bh (v, T?) st' → v.Num ∧ T? = some .tNat

/-- `FragNatRun` is the `Nat` part of `FragRun`. -/
theorem FragRun.nat {D : Decisions} (h : FragRun D) : FragNatRun D :=
  fun Γ u n st st' bh v T? hu hP hm htd hD hr => by
    obtain ⟨hT, hv, -⟩ := h Γ u .nat n none st st' bh v T? hu hP hm (.inl htd) hD hr
    exact ⟨hv, hT⟩

/-- **The reference's run of a fragment term reads no hint** (each clause the fragment uses hands its
sub-terms fixed hints and ignores its own). -/
theorem frag_hint {K : RunCtx} {ρ : Assignment} {φ : Future} {Γ : List FT} {t : Term} {A : FT} (hty : FTy Γ t A)
    (tl : Bool) (h h' : TyS) (s : SState) : runT K ρ φ tl h t s = runT K ρ φ tl h' t s := by
  cases hty <;> rw [runT, runT]

/-! ## The cases of the induction -/

section
variable {K : RunCtx} {ρ : Assignment} {φ : Future}

/-- **A read of a number variable of the fragment, at `evalCore`**: a number (`var_core`), lent
(`readLent_core`), or moved (the run fails, `VarBotInv`). -/
theorem fvar_core (hVN : VarNumInv) (hV : VarLentInv) (hVB : VarBotInv) (hIE : InvEnd) (hI : InvSteps)
    (hPL : PlaceLocal K.D) {n i : Nat} {Γ : List FT} (hi : Γ[i]? = some .nat) :
    CoreSim K ρ φ (n + 1) (.place (.var i)) (FSt Γ) := by
  intro st st' typed hint v T? s π hP hty hm htn htd hcd hp hr hS hv hab hnh hfl hok hD bh h
  rcases hP.var_cases hi with hN | hL | ⟨f, j, b, hck, hb, hbot, htyb⟩
  · exact var_core hVN hI st st' typed hint v T? s π hN hty hm htn htd hcd hp hr hS hv hab hnh hfl hok hD bh h
  · exact readLent_core hV hIE hI hPL st st' typed hint v T? s π hL hty hm htn htd hcd hp hr hS hv hab hnh hfl
      hok hD bh h
  · exact absurd h (hVB n typed i hint st st' bh v T? f j b hck hb hbot htyb)

/-- **From the step at `evalCore` at every fuel to the step at `eval` at every fuel** (`eval_of_core`;
below fuel `3` the run fails, `EvalLow`). -/
theorem frag_lift (hE : EvalInv) (hlow : EvalLow) (hdec : FragDec K.D) {Γ : List FT} {t : Term} {A : FT}
    (hty : FTy Γ t A) (hval : ∀ w, t ≠ .val w) (hcall : ∀ f as h, t ≠ .call f as h)
    (hc : ∀ m, CoreSim K ρ φ (m + 1) t (FSt Γ) (· = true)) : ∀ n, EvalSim K ρ φ n t (FSt Γ) (· = true) := by
  intro n
  by_cases hn : n < 3
  · intro st st' typed hint v T? s π _ _ _ _ _ _ _ _ _ _ _ _ _ bh h
    exact absurd h (hlow n typed t hint st st' bh _ hn hval)
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 + 2 := ⟨n - 3, by omega⟩
    refine eval_of_core hE (fun a b hk ha => ha.kern hk) hval hcall (fun st hst => ?_) (hc m)
    rw [(hdec Γ t A st hty hst).2]
    cases A <;> exact ⟨fun e => (by cases e), rfl⟩

end

/-- A step for every run gives the step for the typed ones. -/
theorem CoreSim.restrict {K : RunCtx} {ρ : Assignment} {φ : Future} {n : Nat} {t : Term} {P : MState → Prop}
    {TY : Bool → Prop} (h : CoreSim K ρ φ n t P) : CoreSim K ρ φ n t P TY :=
  fun st st' typed hint v T? s π hP _ => h st st' typed hint v T? s π hP trivial

/-- **The steps of the fragment not yet proved**, each in the form the induction uses: from its
sub-terms' steps at every extension of `Δ` and the assignment, the step at `evalCore`. The cases
`Z`, `S` and the read are proved (`frag_sim`); these are the lead's open work (`OPEN.md`), stated
here so that the induction is checked now. -/
structure FragCases (K : RunCtx) (φ : Future) : Prop where
  bor : ∀ Γ i, Γ[i]? = some .nat → ∀ m (Δ : Nat → TyS) (ρ : Assignment),
    CoreSim { K with Δ := Δ } ρ φ (m + 1) (.borrow (.var i)) (FSt Γ) (· = true)
  asg : ∀ Γ i u, Γ[i]? = some .nat → FTy Γ u .nat → ∀ m,
    (∀ (Δ : Nat → TyS) (ρ : Assignment), EvalSim { K with Δ := Δ } ρ φ m u (FSt Γ) (· = true)) →
    ∀ (Δ : Nat → TyS) (ρ : Assignment), CoreSim { K with Δ := Δ } ρ φ (m + 1) (.assign (.var i) u) (FSt Γ) (· = true)
  asgD : ∀ Γ i u, Γ[i]? = some .ref → FTy Γ u .nat → ∀ m,
    (∀ (Δ : Nat → TyS) (ρ : Assignment), EvalSim { K with Δ := Δ } ρ φ m u (FSt Γ) (· = true)) →
    ∀ (Δ : Nat → TyS) (ρ : Assignment),
      CoreSim { K with Δ := Δ } ρ φ (m + 1) (.assign (.deref (.var i)) u) (FSt Γ) (· = true)
  letIn : ∀ Γ x u w A B, FTy Γ u A → FTy (A :: Γ) w B → ∀ m,
    (∀ (Δ : Nat → TyS) (ρ : Assignment), EvalSim { K with Δ := Δ } ρ φ m u (FSt Γ) (· = true)) →
    (∀ (Δ : Nat → TyS) (ρ : Assignment), EvalSim { K with Δ := Δ } ρ φ m w (FSt (A :: Γ)) (· = true)) →
    ∀ (Δ : Nat → TyS) (ρ : Assignment), CoreSim { K with Δ := Δ } ρ φ (m + 1) (.letIn x u w) (FSt Γ) (· = true)
  seq : ∀ Γ u w A B, FTy Γ u A → FTy Γ w B → ∀ m,
    (∀ (Δ : Nat → TyS) (ρ : Assignment), EvalSim { K with Δ := Δ } ρ φ m u (FSt Γ) (· = true)) →
    (∀ (Δ : Nat → TyS) (ρ : Assignment), EvalSim { K with Δ := Δ } ρ φ m w (FSt Γ) (· = true)) →
    ∀ (Δ : Nat → TyS) (ρ : Assignment), CoreSim { K with Δ := Δ } ρ φ (m + 1) (.seq u w) (FSt Γ) (· = true)

/-- **The fragment theorem** (`eval_sim` at every fragment term): for every term the fragment types,
every fuel, `Δ` and assignment, the step at `eval` from a state meeting `FSt`, by induction on the
typing, each sub-term's step an induction hypothesis at every extension. `Z`, `S` and the read
(a number, a lent variable, a moved one) are proved here; the other five cases are `FragCases`.
Assumes facts about the checker alone (`EvalInv`, `ZeroInv`, `SuccInv`, `VarNumInv`, `VarLentInv`,
`VarBotInv`, `EvalLow`, `FragNatRun`, `InvEnd`, `InvSteps`, `PlaceLocal`) and about the table
(`FragDec`). -/
theorem frag_sim {K : RunCtx} {φ : Future} (hE : EvalInv) (hZ : ZeroInv) (hS : SuccInv) (hVN : VarNumInv)
    (hV : VarLentInv) (hVB : VarBotInv) (hIE : InvEnd) (hI : InvSteps) (hlow : EvalLow) (hdec : FragDec K.D)
    (hnat : FragNatRun K.D) (hPL : PlaceLocal K.D) (hcs : FragCases K φ) :
    ∀ Γ t A, FTy Γ t A → ∀ n (Δ : Nat → TyS) (ρ : Assignment),
      EvalSim { K with Δ := Δ } ρ φ n t (FSt Γ) (· = true) := by
  intro Γ t A hty
  induction hty with
  | zero Γ =>
    intro n Δ ρ
    exact frag_lift (K := { K with Δ := Δ }) hE hlow hdec (.zero Γ) (fun _ e => by cases e)
      (fun _ _ _ e => by cases e) (fun m => ColumnC.zero_coreSim hZ hI) n
  | succ Γ u hu ih =>
    intro n Δ ρ
    refine frag_lift (K := { K with Δ := Δ }) hE hlow hdec (.succ Γ u hu) (fun _ e => by cases e)
      (fun _ _ _ e => by cases e) (fun m => ?_) n
    exact succ_core hS hI (ih m Δ ρ) (fun a b hk ha => ha.kern hk) (fun st hst => (hdec Γ u .nat st hu hst).1)
      (fun s => frag_hint hu _ _ _ s)
      (fun st₀ st₁ bh v₀ T₀ hP hm htd hD h => by
        obtain ⟨hv, rfl⟩ := hnat Γ u m st₀ st₁ bh v₀ T₀ hu hP hm htd hD h
        exact ⟨hv, fun T e => by cases e; rfl⟩)
  | var Γ i hi =>
    intro n Δ ρ
    exact frag_lift (K := { K with Δ := Δ }) hE hlow hdec (.var Γ i hi) (fun _ e => by cases e)
      (fun _ _ _ e => by cases e) (fun m => (fvar_core (K := { K with Δ := Δ }) hVN hV hVB hIE hI hPL hi).restrict) n
  | bor Γ i hi =>
    intro n Δ ρ
    exact frag_lift (K := { K with Δ := Δ }) hE hlow hdec (.bor Γ i hi) (fun _ e => by cases e)
      (fun _ _ _ e => by cases e) (fun m => hcs.bor Γ i hi m Δ ρ) n
  | asg Γ i u hi hu ih =>
    intro n Δ ρ
    exact frag_lift (K := { K with Δ := Δ }) hE hlow hdec (.asg Γ i u hi hu) (fun _ e => by cases e)
      (fun _ _ _ e => by cases e) (fun m => hcs.asg Γ i u hi hu m (ih m) Δ ρ) n
  | asgD Γ i u hi hu ih =>
    intro n Δ ρ
    exact frag_lift (K := { K with Δ := Δ }) hE hlow hdec (.asgD Γ i u hi hu) (fun _ e => by cases e)
      (fun _ _ _ e => by cases e) (fun m => hcs.asgD Γ i u hi hu m (ih m) Δ ρ) n
  | letIn Γ x u w A B hu hw ihu ihw =>
    intro n Δ ρ
    exact frag_lift (K := { K with Δ := Δ }) hE hlow hdec (.letIn Γ x u w A B hu hw) (fun _ e => by cases e)
      (fun _ _ _ e => by cases e) (fun m => hcs.letIn Γ x u w A B hu hw m (ihu m) (ihw m) Δ ρ) n
  | seq Γ u w A B hu hw ihu ihw =>
    intro n Δ ρ
    exact frag_lift (K := { K with Δ := Δ }) hE hlow hdec (.seq Γ u w A B hu hw) (fun _ e => by cases e)
      (fun _ _ _ e => by cases e) (fun m => hcs.seq Γ u w A B hu hw m (ihu m) (ihw m) Δ ρ) n

end Ochr.Meaning.Steps.Form
