import OchrMeta.Guard
import OchrMeta.Mono
import OchrMeta.WF

/-! # Lemma 1 (termination): the structural half

meta-model-v1 §2.1 Lemma 1: for a program accepted by [Rec], every run terminates.  The only
source of divergence in the machine is a call: every other rule is structural in the term (a
`match` arm is a sub-place substitution of a subterm, which does not grow it), and the fuel-free
parts of the machine (`access`, `popFrame`, `closeCall`, …) never run out of fuel.  This file
proves that half:

* `exec_total`: if every call a term makes terminates from every call point, the term terminates
  from every state;
* `termination_of_calls`: in an ordered program (`Ordered`), if every call to a *recursive*
  definition terminates, every run terminates (induction on the call order);
* `termination_nonrec`: Lemma 1 for programs with no recursive definition, from any state.

The recursive half (a call to a well-guarded recursive definition terminates) is what remains of
`termination` below (Lemma 1 proper, stated with `sorry`). -/

namespace OchrMeta

/-! ## A size of terms that sub-place substitution preserves -/

mutual
def Term.sz : Term → Nat
  | .read _ | .borrow _ | .zero | .unit => 1
  | .assign _ t | .succ t | .erase t => t.sz + 1
  | .letIn _ t u | .seq t u | .pair t u => t.sz + u.sz + 1
  | .mtch _ tz _ ts => tz.sz + ts.sz + 1
  | .call _ args _ => Term.szList args + 1
def Term.szList : List Term → Nat
  | [] => 0
  | t :: ts => t.sz + Term.szList ts + 1
end

mutual
theorem Term.sz_substVar (y : Var) (q : Place) : ∀ t : Term, (t.substVar y q).sz = t.sz
  | .read _ | .borrow _ | .zero | .unit => rfl
  | .assign _ t | .succ t | .erase t => by
    simp only [Term.substVar, Term.sz, Term.sz_substVar y q t]
  | .letIn x t u => by
    simp only [Term.substVar, Term.sz, Term.sz_substVar y q t]
    split <;> simp [Term.sz_substVar y q u]
  | .seq t u | .pair t u => by
    simp only [Term.substVar, Term.sz, Term.sz_substVar y q t, Term.sz_substVar y q u]
  | .mtch _ tz z ts => by
    simp only [Term.substVar, Term.sz, Term.sz_substVar y q tz]
    split <;> simp [Term.sz_substVar y q ts]
  | .call _ args _ => by
    simp only [Term.substVar, Term.sz, Term.szList_substVar y q args]
theorem Term.szList_substVar (y : Var) (q : Place) : ∀ ts : List Term,
    Term.szList (Term.substVarList y q ts) = Term.szList ts
  | [] => rfl
  | t :: ts => by
    simp only [Term.substVarList, Term.szList, Term.sz_substVar y q t, Term.szList_substVar y q ts]
end

mutual
theorem Term.calls_substVar (y : Var) (q : Place) : ∀ t : Term, (t.substVar y q).calls = t.calls
  | .read _ | .borrow _ | .zero | .unit => rfl
  | .assign _ t | .succ t | .erase t => by
    simp only [Term.substVar, Term.calls, Term.calls_substVar y q t]
  | .letIn x t u => by
    simp only [Term.substVar, Term.calls, Term.calls_substVar y q t]
    split <;> simp [Term.calls_substVar y q u]
  | .seq t u | .pair t u => by
    simp only [Term.substVar, Term.calls, Term.calls_substVar y q t, Term.calls_substVar y q u]
  | .mtch _ tz z ts => by
    simp only [Term.substVar, Term.calls, Term.calls_substVar y q tz]
    split <;> simp [Term.calls_substVar y q ts]
  | .call _ args _ => by
    simp only [Term.substVar, Term.calls, Term.callsList_substVar y q args]
theorem Term.callsList_substVar (y : Var) (q : Place) : ∀ ts : List Term,
    Term.callsList (Term.substVarList y q ts) = Term.callsList ts
  | [] => rfl
  | t :: ts => by
    simp only [Term.substVarList, Term.callsList, Term.calls_substVar y q t,
      Term.callsList_substVar y q ts]
end

theorem Term.mem_callsList {g : String} : ∀ {ts : List Term}, g ∈ Term.callsList ts ↔ ∃ t ∈ ts, g ∈ t.calls
  | [] => by simp [Term.callsList]
  | t :: ts => by simp [Term.callsList, Term.mem_callsList (ts := ts)]

theorem Term.sz_lt_szList {t : Term} : ∀ {ts : List Term}, t ∈ ts → t.sz < Term.szList ts + 1
  | [], h => by simp at h
  | u :: us, h => by
    simp only [List.mem_cons] at h
    simp only [Term.szList]
    rcases h with rfl | h
    · omega
    · have := Term.sz_lt_szList h; omega

/-! ## Stabilisation: a fuel-indexed result that is eventually a constant other than `oof` -/

def Stab (F : Nat → Res) : Prop := ∃ n r, r ≠ .oof ∧ ∀ m, n ≤ m → F m = r

theorem Stab.const {r : Res} (h : r ≠ .oof) : Stab (fun _ => r) := ⟨0, r, h, fun _ _ => rfl⟩

theorem Stab.bind {F : Nat → Res} {G : Nat → St → Val → Res} (hF : Stab F)
    (hG : ∀ s v, Stab (fun n => G n s v)) : Stab (fun n => (F n).bind (G n)) := by
  obtain ⟨n, r, hr, hn⟩ := hF
  cases r with
  | ok s v =>
    obtain ⟨n', r', hr', hn'⟩ := hG s v
    refine ⟨max n n', r', hr', fun m hm => ?_⟩
    show (F m).bind (G m) = r'
    rw [hn m (by omega), Res.bind_ok]; exact hn' m (by omega)
  | oof => exact absurd rfl hr
  | stuck => exact ⟨n, .stuck, by simp, fun m hm => by show (F m).bind (G m) = _; rw [hn m hm]; rfl⟩
  | err => exact ⟨n, .err, by simp, fun m hm => by show (F m).bind (G m) = _; rw [hn m hm]; rfl⟩

theorem Stab.ofExec {P : Prog} {s : St} {t : Term} (h : ∃ n, exec P n s t ≠ .oof) :
    Stab (fun n => exec P n s t) := by
  obtain ⟨n, hn⟩ := h
  exact ⟨n, _, hn, fun m hm => exec_mono_le P hm hn⟩

theorem Stab.execSucc {P : Prog} {s : St} {t : Term} (h : Stab (fun n => exec P (n + 1) s t)) :
    ∃ n, exec P n s t ≠ .oof := by
  obtain ⟨n, r, hr, hn⟩ := h
  exact ⟨n + 1, by have := hn n (Nat.le_refl n); simp only at this; rw [this]; exact hr⟩

theorem Stab.ofCallWith {P : Prog} {cc : Bool} {f : String} {d : FunDef} {ws : List Val} {s : St}
    (h : ∃ n, callWith (exec P n) cc f d ws s ≠ .oof) :
    Stab (fun n => callWith (exec P n) cc f d ws s) := by
  obtain ⟨n, hn⟩ := h
  refine ⟨n, _, hn, fun m hm => callWith_agree (fun s t ht => exec_mono_le P hm ht) cc f d ws s hn⟩

/-! ## The fuel-free parts of the machine never run out of fuel -/

theorem access_ne_oof (deep : Bool) (x : Var) (π : List Proj) :
    ∀ N (s : St), s.env.nb < N → access deep x π s ≠ .oof := by
  intro N
  induction N with
  | zero => intro s h; omega
  | succ N ih =>
    intro s hN
    rw [access]
    split
    · simp
    · split
      · split
        · simp
        · rename_i s' h
          exact ih s' (by have := endBorrow_nb_lt h; omega)
      · simp
      · simp
      · simp

theorem access_ne_oof' (deep : Bool) (x : Var) (π : List Proj) (s : St) : access deep x π s ≠ .oof :=
  access_ne_oof deep x π (s.env.nb + 1) s (by omega)

theorem Res.bind_ne_oof {r : Res} {k : St → Val → Res} (hr : r ≠ .oof) (hk : ∀ s v, k s v ≠ .oof) :
    r.bind k ≠ .oof := by
  cases r <;> simp_all [Res.bind]

theorem closeCall_ne_oof (f : String) (d : FunDef) (ws : List Val) (s : St) : closeCall f d ws s ≠ .oof := by
  unfold closeCall
  split
  · simp
  · simp only
    split
    · simp
    · split
      · split
        · simp
        · split <;> simp
      · split <;> simp
      · split <;> simp

/-- A call's result is `oof` only if its body run is. -/
theorem callWith_ne_oof {ev : St → Term → Res} {cc : Bool} {f : String} {d : FunDef} {ws : List Val}
    {s : St} (h : ∀ b, d.body = some b → ev (s.push (paramFrame d ws)) b ≠ .oof) :
    callWith ev cc f d ws s ≠ .oof := by
  unfold callWith
  split
  · split
    · exact closeCall_ne_oof f d ws s
    · simp
  · rename_i b hb
    split
    · have := h b hb
      split
      · split <;> simp
      · split
        · exact closeCall_ne_oof f d ws s
        · simp
      · simp
      · simp_all
    · simp

theorem Stab.of_eq {F : Nat → Res} {r : Res} (h : ∀ n, F n = r) (hr : r ≠ .oof) : Stab F :=
  ⟨0, r, hr, fun m _ => h m⟩

/-! ## Structural termination -/

/-- A call to `h` at argument values `ws` terminates, from every call point. -/
def CallTerm (P : Prog) (h : String) (ws : List Val) : Prop :=
  ∀ d, P.find h = some d → ∀ (cc : Bool) (s : St), ∃ n, callWith (exec P n) cc h d ws s ≠ .oof

theorem execArgs_stab {P : Prog} : ∀ (args : List Term),
    (∀ a ∈ args, ∀ s, ∃ n, exec P n s a ≠ .oof) →
    ∀ i s, Stab (fun n => execArgs (exec P n) i s args)
  | [], _, i, s => Stab.of_eq (fun _ => rfl) (by simp)
  | a :: as, h, i, s => by
    simp only [execArgs]
    exact Stab.bind (Stab.ofExec (h a (by simp) s))
      (fun s v => execArgs_stab as (fun b hb => h b (by simp [hb])) (i + 1) _)

theorem exec_total (P : Prog) : ∀ N (t : Term), t.sz < N →
    (∀ h ∈ t.calls, ∀ ws, CallTerm P h ws) → ∀ s, ∃ n, exec P n s t ≠ .oof := by
  intro N
  induction N with
  | zero => intro t h; omega
  | succ N ih =>
    intro t hsz hc s
    apply Stab.execSucc
    -- the sub-runs: a smaller term calling a subset of the functions
    have sub : ∀ t' : Term, t'.sz < t.sz → (∀ h ∈ t'.calls, h ∈ t.calls) → ∀ s, Stab (fun n => exec P n s t') :=
      fun t' h1 h2 s => Stab.ofExec (ih t' (by omega) (fun h hh => hc h (h2 h hh)) s)
    cases t with
    | read p =>
      simp only [exec]
      refine Stab.of_eq (fun _ => rfl) ?_
      refine Res.bind_ne_oof (access_ne_oof' _ _ _ _) fun s c => ?_
      split
      · simp
      · split <;> simp
      · simp
    | borrow p =>
      simp only [exec]
      refine Stab.of_eq (fun _ => rfl) ?_
      refine Res.bind_ne_oof (access_ne_oof' _ _ _ _) fun s c => ?_
      split
      · simp
      · split <;> simp
    | assign p t =>
      simp only [exec]
      refine Stab.bind (sub t (by simp [Term.sz]) (fun h hh => by simp [Term.calls, hh]) s) fun s v => Stab.of_eq (fun _ => rfl) ?_
      refine Res.bind_ne_oof (access_ne_oof' _ _ _ _) fun s c => ?_
      split
      · simp
      · split
        · simp
        · split <;> simp
    | letIn x t u =>
      simp only [exec]
      refine Stab.bind (sub t (by simp [Term.sz]; omega) (fun h hh => by simp [Term.calls, hh]) s) fun s v => ?_
      refine Stab.bind (sub u (by simp [Term.sz]; omega) (fun h hh => by simp [Term.calls, hh]) _) fun s w => ?_
      refine Stab.of_eq (fun _ => rfl) ?_
      split
      · simp
      · split <;> simp
    | seq t u =>
      simp only [exec]
      refine Stab.bind (sub t (by simp [Term.sz]; omega) (fun h hh => by simp [Term.calls, hh]) s) fun s v => ?_
      split
      · exact Stab.of_eq (fun _ => rfl) (by simp)
      · exact sub u (by simp [Term.sz]; omega) (fun h hh => by simp [Term.calls, hh]) _
    | zero => exact Stab.of_eq (fun _ => rfl) (by simp)
    | unit => exact Stab.of_eq (fun _ => rfl) (by simp)
    | succ t =>
      simp only [exec]
      refine Stab.bind (sub t (by simp [Term.sz]) (fun h hh => by simp [Term.calls, hh]) s) fun s v => ?_
      exact Stab.of_eq (fun _ => rfl) (by split <;> simp)
    | pair t u =>
      simp only [exec]
      refine Stab.bind (sub t (by simp [Term.sz]; omega) (fun h hh => by simp [Term.calls, hh]) s) fun s v => ?_
      refine Stab.bind (sub u (by simp [Term.sz]; omega) (fun h hh => by simp [Term.calls, hh]) _) fun s w => ?_
      exact Stab.of_eq (fun _ => rfl) (by split <;> simp)
    | mtch p tz y ts =>
      simp only [exec]
      refine Stab.bind (Stab.of_eq (fun _ => rfl) (access_ne_oof' _ _ _ _)) fun s c => ?_
      cases c with
      | zero => exact sub tz (by simp [Term.sz]; omega) (fun h hh => by simp [Term.calls, hh]) s
      | succ _ =>
        exact sub _ (by simp [Term.sz, Term.sz_substVar]; omega)
          (fun h hh => by simp [Term.calls, Term.calls_substVar] at hh ⊢; simp [hh]) s
      | _ => exact Stab.of_eq (fun _ => rfl) (by first | simp | (split <;> simp))
    | call f args cc =>
      simp only [exec]
      cases hf : P.find f with
      | none => exact Stab.of_eq (fun _ => rfl) (by simp)
      | some d =>
        simp only
        by_cases hp : d.ret = .prop
        · simp only [hp, if_true]; exact Stab.of_eq (fun _ => rfl) (by simp)
        · simp only [hp, if_false]
          have hargs : ∀ a ∈ args, ∀ s, ∃ n, exec P n s a ≠ .oof := fun a ha s =>
            ih a (by have := Term.sz_lt_szList ha; simp [Term.sz] at hsz; omega)
              (fun h hh => hc h (by simp only [Term.calls, List.mem_cons, Term.mem_callsList];
                                    exact Or.inr ⟨a, ha, hh⟩)) s
          refine Stab.bind (execArgs_stab args hargs 0 s) fun s _ => ?_
          split
          · exact Stab.of_eq (fun _ => rfl) (by simp)
          · rename_i ws s' _
            exact Stab.ofCallWith (hc f (by simp [Term.calls]) ws d hf cc s')
    | erase t => exact Stab.of_eq (fun _ => rfl) (by simp)

/-- A call terminates when its body terminates from every state (and an opaque call always does). -/
theorem callTerm_of_body {P : Prog} {h : String} {d : FunDef} (hd : P.find h = some d)
    (hb : ∀ b, d.body = some b → ∀ s, ∃ n, exec P n s b ≠ .oof) (ws : List Val) : CallTerm P h ws := by
  intro d' hd' cc s
  rw [hd] at hd'; cases hd'
  cases hbd : d.body with
  | none => exact ⟨0, callWith_ne_oof (fun b hb' => by simp [hbd] at hb')⟩
  | some b =>
    obtain ⟨n, hn⟩ := hb b hbd (s.push (paramFrame d ws))
    exact ⟨n, callWith_ne_oof (fun b' hb' => by rw [hbd] at hb'; cases hb'; exact hn)⟩

/-! ## The call order -/

open Guard in
theorem orderedAux_split : ∀ (A : Prog) (seen : List String) (f : String) (d : FunDef) (B : Prog),
    orderedAux seen (A ++ (f, d) :: B) = true →
    f ∉ seen ∧ f ∉ A.map Prod.fst ∧
    ∀ b, d.body = some b → ∀ g ∈ b.calls, g ∈ seen ∨ g ∈ A.map Prod.fst ∨ (g = f ∧ d.recPos.isSome)
  | [], seen, f, d, B, h => by
    simp only [List.nil_append, orderedAux, Bool.and_eq_true, Bool.not_eq_true'] at h
    obtain ⟨⟨hf, hb⟩, _⟩ := h
    refine ⟨by simpa using hf, by simp, fun b hbd g hg => ?_⟩
    rw [hbd] at hb
    simp only [List.all_eq_true, Bool.or_eq_true, List.contains_iff_mem, Bool.and_eq_true,
      beq_iff_eq] at hb
    rcases hb g hg with h1 | h1
    · exact Or.inl h1
    · exact Or.inr (Or.inr h1)
  | (f', d') :: A, seen, f, d, B, h => by
    simp only [List.cons_append, orderedAux, Bool.and_eq_true] at h
    obtain ⟨hf, hb, hc⟩ := orderedAux_split A (f' :: seen) f d B h.2
    simp only [List.mem_cons, not_or] at hf
    refine ⟨hf.2, by simp only [List.map_cons, List.mem_cons, not_or]; exact ⟨hf.1, hb⟩, fun b hbd g hg => ?_⟩
    rcases hc b hbd g hg with h1 | h1 | h1
    · simp only [List.mem_cons] at h1
      rcases h1 with h1 | h1
      · exact Or.inr (Or.inl (by simp [h1]))
      · exact Or.inl h1
    · exact Or.inr (Or.inl (by simp [h1]))
    · exact Or.inr (Or.inr h1)

theorem lookup_append_of_not_mem {f : String} {v : FunDef} : ∀ {A B : Prog}, f ∉ A.map Prod.fst →
    (A ++ (f, v) :: B).lookup f = some v
  | [], B, _ => by simp
  | (g, w) :: A, B, h => by
    simp only [List.map_cons, List.mem_cons, not_or] at h
    have hne : (f == g) = false := by simp [beq_eq_false_iff_ne]; exact h.1
    simp only [List.cons_append, List.lookup, hne]
    exact lookup_append_of_not_mem h.2

/-- In an ordered program, if every call to a recursive definition terminates, every call does:
induction on the call order. -/
theorem termination_of_calls {P : Prog} (hord : Guard.Ordered P)
    (hrec : ∀ h d, P.find h = some d → d.recPos.isSome → ∀ ws, CallTerm P h ws) :
    ∀ h ws, CallTerm P h ws := by
  have key : ∀ n (A : Prog) f d B, A.length < n → P = A ++ (f, d) :: B → ∀ ws, CallTerm P f ws := by
    intro n
    induction n with
    | zero => intro A f d B h; omega
    | succ n ih =>
      intro A f d B hlen hP ws
      obtain ⟨_, hfA, hcalls⟩ := orderedAux_split A [] f d B (by rw [← hP]; exact hord)
      have hd : P.find f = some d := by rw [hP]; exact lookup_append_of_not_mem hfA
      cases hr : d.recPos with
      | some j => exact hrec f d hd (by simp [hr]) ws
      | none =>
        refine callTerm_of_body hd (fun b hb s => exec_total P (b.sz + 1) b (by omega) (fun g hg ws' => ?_) s) ws
        rcases hcalls b hb g hg with h1 | h1 | h1
        · simp at h1
        · obtain ⟨⟨g', dg⟩, hmem, rfl⟩ := List.mem_map.mp h1
          obtain ⟨A₁, A₂, rfl⟩ := List.append_of_mem hmem
          exact ih A₁ g' dg (A₂ ++ (f, d) :: B) (by simp at hlen; omega) (by rw [hP]; simp) ws'
        · simp [hr] at h1
  intro h ws d hd
  obtain ⟨A, B, hP, _⟩ := List.lookup_eq_some_iff.mp hd
  exact key (A.length + 1) A h d B (by omega) hP ws d hd

/-- Termination reduces to the recursive definitions: in an ordered program whose calls to
recursive definitions terminate, every run terminates. -/
theorem termination_of_recCalls {P : Prog} (hord : Guard.Ordered P)
    (hrec : ∀ h d, P.find h = some d → d.recPos.isSome → ∀ ws, CallTerm P h ws) (t : Term) (s : St) :
    ∃ n, exec P n s t ≠ .oof :=
  exec_total P (t.sz + 1) t (by omega) (fun h _ ws => termination_of_calls hord hrec h ws) s

/-- **Lemma 1 without recursion**: in an ordered program with no recursive definition, every run
terminates, from any state (concrete or symbolic, well-formed or not). -/
theorem termination_nonrec {P : Prog} (hord : Guard.Ordered P)
    (hnr : ∀ h d, P.find h = some d → d.recPos = none) (t : Term) (s : St) :
    ∃ n, exec P n s t ≠ .oof :=
  termination_of_recCalls hord (fun h d hd hs => by rw [hnr h d hd] at hs; simp at hs) t s

/-- **Lemma 1 (termination)**, meta-model-v1 §2.1, for the FO fragment: in a well-guarded program,
every run from a well-formed state, concrete or symbolic, terminates (in a value, an error, or a
stuck state).

OPEN in general; proved without `sorry` for two sub-fragments:
* `termination_nonrec` (this file): no recursive definition, any state;
* `termination_bf` (GuardLemma1.lean): no borrows (no `&p` term, no `&T` parameter or result),
  from a state with no borrow: the whole guard argument (simulation of the checker's branches by
  the actual run, `sim_gexec`; strong induction on the actual entry value; call order).

What the borrow case still needs, on top of that proof (whose structure carries over):
1. the invariant: `exec_bf` (only the top frame changes) becomes Lemma 0 (W1–W4, `exec_wf`, itself
   `sorry` in WF.lean), strengthened to hold at every call site, where `call_effect` (T2b,
   Frame.lean) reduces a call to `callRun` from exactly the state the checker starts from;
2. the approximation `VR` gains a loan-name correspondence `ρ` (symbolic `borrow ℓ`/`loan ℓ` stand
   for actual `borrow ρℓ`/`loan ρℓ`), extended at each borrow creation: once an actual recursive
   call has run, the two machines' fresh-name counters diverge;
3. wildcards that carry loans: a call closed off at a borrow result leaves `loan_k` inside sealed
   fills whose actual counterparts may not contain it (Tests/Basic.lean `t5_nose_counterexample`),
   so [Access] can end a borrow symbolically that stays live in the actual run; the relation must
   allow a symbolic `⊥` against a live actual borrow whose later [End] only writes into wildcard
   positions.
The measure (the entry content, through the borrow) and the rest of the argument are unchanged. -/
theorem termination {P : Prog} (hP : Guard.WellGuarded P) {s : St} (hs : WF s) (t : Term) :
    ∃ n, exec P n s t ≠ .oof := by
  sorry

end OchrMeta
