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

/-! ## `Tally` and `tally` are gone (M28 μ)

    They counted a pool's accepts, rejects and declines, and every corpus-wide
    census over `pools` was computed through them. **The thing they counted is
    dissolving**: `fn` is a statement of the program grammar (M28 θ), so a
    declaration that becomes a program stops being a `FnDef` and leaves the pool.
    The counts therefore moved on every migrated file without any verdict having
    changed, which is the opposite of what a regression signal should do.

    What they were kept for after `report` died — "a file quietly dropping out of
    the survey, or a declaration silently starting to decline, still moves a
    number" — is served better by what remains, because both replacements carry
    IDENTITY where a count carries only arithmetic: `S27Dispose` §B pins the
    declining residue name for name, and `progVerdict` states a pool's verdicts
    positionally. Neither can be quieted by editing a constant.

    `progVerdict` below is what `tally` folded, and it outlives it. -/

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

/-! ## `progEnvsOfT`/`progEnvOfT` are gone (M28 ο)

    They inspected what a declaration's BODY left in Ω, by assembling the callee
    closure and running the body as the program's tail. The sweep (M28 ν) rewrote
    every call site — a body that is a program's tail needs no declaration wrapped
    around it to be one — and they finished with zero users.

    **The reasoning in their docstring did not go with them.** Their one subtle
    point was that a program's own function bindings must be dropped BEFORE
    canonicalization, because a sealed function is itself a σ and would shift the
    index of every σ after it. That now lives on `Program.tailEnvs`, which is the
    only implementation of it left. -/

end Dllbc.Migrate
