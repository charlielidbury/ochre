import Dllbc.Program
import Dllbc.FnMacro

/-!
# Migrating the corpus: the declaration path and the program path, compared

M26-E's bar is **coverage preservation**: every declaration the old path accepted
must be accepted as a program, and every lie twin it refused must be refused as a
program. The corpus holds a few hundred of both, and the failure mode a bulk
migration has is not a wall — it is a quietly-wrong rewrite that still builds.

So nothing here rewrites a test. Each cohort is run down BOTH paths and the two
verdicts are compared, which turns "the migration is faithful" from a claim about
my care into a computation. Three things make that mechanical rather than
laborious:

  * **The cohort is derived, not declared.** A test's declaration table was always
    the callee closure of its subject; `calleeNames` computes it, and `topo`
    orders it so that every callee is bound above its caller — which is what §8
    requires of a let-chain and what the table never had to care about.
  * **`progOf` does the assembly**, exactly as it does for the flagships.
  * **Refusals are third verdict, not a failure.** `fnElab` legitimately declines
    a declaration that has no seal counterpart — a `[v]` payload decrease (§12
    decision 8) or a declared `back` (§6.2) — and those are *recorded*, per file,
    rather than silently counted as agreement. A migration report that could not
    say "this one did not move" would be the quietly-wrong thing.
-/

namespace Dllbc.Migrate

/-- Order a pool so that every callee comes before its caller. A declaration
    whose callees are all emitted (or are not in the pool at all, i.e. are
    someone else's) is ready; self-calls do not count, since `fnElab` turns them
    into `ih`. If nothing is ready the remainder is emitted as-is and the program
    path reports the forward reference itself. -/
partial def topo (pool : List FnDef) (emitted : List String) (todo : List FnDef) : List FnDef :=
  match todo.find? (fun d => (calleeNames d.body).all (fun n =>
      n == d.name || emitted.contains n || !(pool.any (·.name == n)))) with
  | none => todo
  | some d => d :: topo pool (d.name :: emitted) (todo.filter (·.name != d.name))

/-- The callee closure of `d` within `pool`, in dependency order, `d` last. -/
partial def cohort (pool : List FnDef) (d : FnDef) : List FnDef :=
  let rec expand (fuel : Nat) (acc : List FnDef) : List FnDef :=
    match fuel with
    | 0 => acc
    | fuel + 1 =>
      let wanted := (acc.flatMap (fun c => calleeNames c.body)).eraseDups
      let add := wanted.filterMap (fun n =>
        if acc.any (·.name == n) then none else pool.find? (·.name == n))
      if add.isEmpty then acc else expand fuel (acc ++ add)
  topo pool [] (expand pool.length [d])

/-! ## The comparison harness is gone (M27-δ)

    `declVerdict`, `Report` and `report` compared the two paths declaration by
    declaration. There is one path now, so there is nothing to compare: the
    harness dies with `checkFn`, which is what it existed to measure against.

    Its lesson outlives it and is recorded where it will be read — **agreement is
    not coverage**. `report` never compared a DECLINING declaration's
    declaration-path verdict (`progVerdict` returns `none` and the comparison
    skips), so `disagree.isEmpty` was true throughout while 27 of the 42
    declarations that stopped declining under a strip became REJECTS. A comparison
    harness must also measure verdict SURVIVAL.

    What survives here is what the corpus asserts THROUGH: `cohort`/`topo`, the
    two verdict helpers, and `refusal`, which is how a decline is inspected on
    purpose rather than tolerated. -/

/-- The PROGRAM path's verdict: the cohort assembled into a let-chain and checked
    by one ⇒-walk against no table. `none` = the macro declined to migrate it. -/
def progVerdict (pool : List FnDef) (d : FnDef) : Option Bool :=
  match FnMacro.progOf (cohort pool d) .unit with
  | .error _ => none
  | .ok t => some (match checkProgram t with | .ok _ => true | .error _ => false)

/-- Why a declaration did not migrate — `fnElab`'s own message, so the reason is
    the kernel-adjacent one and not a guess. -/
def refusal (pool : List FnDef) (d : FnDef) : Option String :=
  match FnMacro.progOf (cohort pool d) .unit with
  | .error e => some e
  | .ok _ => none

/-- The names a pool declined to migrate, with `fnElab`'s reason — for the record
    a partial migration owes (see each file's own section). -/
def declinedWith (pool : List FnDef) : List (String × String) :=
  pool.filterMap (fun d => (refusal pool d).map (fun e => (d.name, e)))

/-- **What survives of `report`** (M27-δ): the three counts, without the
    comparison. `Report`'s fourth field was `disagree`, and there is no second path
    to disagree with — but the counts were never the comparison. They were what
    kept it from holding vacuously, and they are exactly as useful now: a file
    quietly dropping out of the survey, or a declaration silently starting to
    decline, still moves a number. -/
structure Tally where
  accepts : Nat
  rejects : Nat
  declined : Nat
deriving BEq, Repr

def tally (pool : List FnDef) : Tally :=
  pool.foldl (fun t d =>
    match progVerdict pool d with
    | none => { t with declined := t.declined + 1 }
    | some true => { t with accepts := t.accepts + 1 }
    | some false => { t with rejects := t.rejects + 1 })
    { accepts := 0, rejects := 0, declined := 0 }

/-! ## The program path's `checkFnOk`/`checkFnErr` (M27-γ)

    The endgame moves the corpus off the declaration path, and the corpus states
    itself in two helpers: `checkFnOk d table` and `checkFnErr d needle table`.
    These are their counterparts, with the SAME shape — subject first, table
    defaulting to the subject alone — so a call site converts by renaming rather
    than by re-derivation.

    What they do is what every flagship already does: assemble the subject's
    callee closure within `table` into a let-chain (`cohort`, `progOf`) and check
    it as ONE program against no table at all. §8's direction, applied to the
    tests instead of to the flagships.

    **A declaration that does not MIGRATE fails these**, and that is deliberate
    rather than a gap: `progOf` returning an error is `false` here, not a third
    verdict, because a twin that DECLINES teaches nothing — it has to migrate and
    then be refused. `Migrate.refusal` is where a decline is inspected on purpose;
    a test asserting `progRejectsOf` must not be able to pass by not moving. -/

/-- The program-path counterpart of `checkFnOk`. -/
def progOkOf (d : FnDef) (table : List FnDef := [d]) : Bool :=
  match FnMacro.progOf (cohort table d) .unit with
  | .error _ => false
  | .ok t => progOk t

/-- The program-path counterpart of `checkFnErr`: the assembled program is
    rejected with `needle` in the message. A declaration that fails to assemble is
    `false`, so this cannot be satisfied by declining to migrate. -/
def progRejectsOf (d : FnDef) (needle : String) (table : List FnDef := [d]) : Bool :=
  match FnMacro.progOf (cohort table d) .unit with
  | .error _ => false
  | .ok t => progRejects t needle

/-- The program-path counterpart of `runFn`: the assembled program's symbolic
    final Ωs, **with the cohort's own function bindings dropped**.

    A program binds each function to a slot (§8: a declaration is a `let`), so its
    Ω carries entries a declaration's never did, and dropping them is what makes
    an inspection of "what the body left" mean the same thing on both paths.

    **They must be dropped BEFORE canonicalization, and that is not a detail.** A
    sealed function IS a σ, so a global participates in `canonicalize`'s
    first-appearance σ ordering and shifts the index of every σ after it — filter
    afterwards and an unchanged body's `y ↦ σ0` reads `σ3`, which would look like
    the migration having changed what the body leaves. So this walks `explore`
    itself rather than reusing `programEnvs`, and filters on the VAR ID against
    `progBase`, which is what a global is. -/
def progEnvsOfT (table : List FnDef) (d : FnDef) : List (Except String Env) :=
  -- **The subject's BODY is the program's TAIL**, not another `let`. `progOf ds
  -- .unit` binds every declaration and runs nothing, so a subject bound that way
  -- has its body checked inside the seal's isolated frame and its Ω never
  -- surfaces. What these assertions inspect is what a body LEAVES, so the body
  -- has to be the thing that runs — which is `dllbc [f] from 900 { … }`'s own shape, a hand-written
  -- tail over an assembled prefix.
  let deps := (cohort table d).filter (·.name != d.name)
  match FnMacro.progOf deps d.body with
  | .error e => [.error e]
  | .ok t =>
    (explore defaultFuel (pushContinuations t) initSt).map (fun r => r.bind (fun p =>
      match (endScope defaultFuel).run p.2 with
      | .ok _ st => .ok (canonicalize (st.env.filter (fun kv => kv.1.id < FnMacro.progBase)))
      | .error e _ => .error e))

/-- The program-path counterpart of `expectFnEnv`: one path, and it leaves exactly
    this Ω. Table-first, like the two it replaces, so a call site converts by
    renaming. -/
def progEnvOfT (table : List FnDef) (d : FnDef) (expected : Env) : Bool :=
  match progEnvsOfT table d with
  | [.ok env] => env == expected
  | _ => false

end Dllbc.Migrate
