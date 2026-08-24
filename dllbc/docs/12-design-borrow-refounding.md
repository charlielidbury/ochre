# Borrow types re-founded: the shape/contract split and loan-attached debts

**Status: DESIGN ONLY. Nothing here is implemented.** This document is the design lane's deliverable for the SUGGESTIONS.md entry "dllbc/ — borrow types re-founded" (2026-08-10, from the M31 design review). Implementation is gated on the user reviewing it. Written 2026-08-17, against `b8721644` (M33 macro-top commit 9). The stamped precondition — "after M32 (it wants the suspension representation's uniform value story)" — is **met**: M32 landed 2026-08-11 (one syntax, one semantic domain, closures the only suspensions), M33 and M33a/b/Σ0 landed after it, and knowledge at rest is a canonical `Term` throughout.

Companion artifact: `dllbc/Dllbc/Tests/BorrowRefoundGoals.lean` — the three acceptance-test families as programs that build today, with the target assertions written out and commented off. That file is the milestone's finish line; this file is the argument for how to get there.

---

## 0. The one-paragraph version

A borrow is two claims that the calculus currently fuses into one syntactic marker. The **shape** claim — "this value is `borrowₘ ℓ v` with `v : τ`" — is a predicate on a value and should be a case of `hasType` like any other. The **contract** claim — "when ℓ ends, the payload is S" — is a store event registered on the loan, and it should be registerable wherever a loan is minted and asserted wherever a loan ends, of which a function signature is one instance among several. Fusing them made `&mut τ` a *telescope position* rather than a type, and that positional restriction is what makes a pair of borrows inexpressible, `split_at_mut` unwritable, and the M24 runtime-length slice a hand-cut special case rather than an instance of a rule.

Splitting them buys four things beyond tidiness, and the last two are the ones that matter. It makes borrow-carrying data ordinary. It gives Stage 0's escaping-borrow heuristic a principled statement (a scope pop is an assertion site, and an outstanding loan whose owner is leaving is an error, not a retention). Because a debt registered on a loan may mention the *exit snapshots of the loans issued alongside it*, it makes the get_mut round-trip law statable and checkable for the first time since M27 deleted declared backward specs — the missing precision the planned hashmap flagship needs, and the reason this is its own milestone. And the same mechanism closes a **live soundness gap** the `hm-probe-getmut` lane found while this was being written: today's exit audit exempts a whole parameter when any borrow derived from it is returned, so a callee may leave a hole in a sibling leaf and be accepted (§3.3.1).

---

## 1. What the calculus does today

A compressed survey, so the rest of the document can point at things. Line numbers are against `b8721644`.

### 1.1 The shape half is a position, enforced by name at five sites

`Term.borrowT : String → Term → Term → Term` (`Syntax.lean:324`) is `&mut (s : τ ↝ τ')`. `&mut τ` is `borrowT ⟨reserved⟩ τ τ` — the snapshot binder is unused and the owed type is the payload type (`Uni.lean:543-546`). Its docstring says the restriction outright: "Only valid at a telescope position — interpreted by the seeding that `checkRFnBody` runs (`seedTelescopeV`), never reflected as a value."

The restriction is enforced by five refusals and two interpreters:

| site | file:line | what it does |
| --- | --- | --- |
| `readC` (⇝) | `Machine.lean:1250` | refuses: "borrow type `&mut (τ ↝ τ')` is only valid at a telescope position" |
| `readR` (⇒) | `Machine.lean:4387` | refuses: "a telescope-position form, not a movable value" |
| `hasType` on a closure | `Machine.lean:~1512` | refuses a borrow-moded Π by `hasBorrowT ty` — "not a type a value inhabits" |
| `processArgs` | `Machine.lean:4766`, `4776`, `4794` | interprets `borrowT` and `sigmaT _ _ (borrowT …)`; anything else goes through `readCWith`, which refuses |
| `seedTelescopeV` | `Machine.lean:3146`, `3150`, `3166` | the same two shapes, at a declaration |
| `retMixesBorrow` | `Syntax.lean:~1000` | refuses a return type mixing borrow and non-borrow components (an M27 soundness containment) |
| `collectResultBorrows` | `Machine.lean:3320` | walks `borrowT` / `sigmaT` against the result value, structurally |

Two things follow that the design has to preserve or replace. A borrow-moded Π has **no `Val`**, so `sctx` cannot hold it and `fsig` exists as a second context precisely for that (`St.fsig`, `Machine.lean:~103`). And E4's enumeration — "where could a *type* be demanded of a borrow-moded λ?" — collapses to "nowhere, the question is unaskable", with the one live consequence recorded in `functions-are-comptime.md:374-389`: **passing a function whose signature has a `&mut` binder is refused** by `processArgs`' `readCWith` of the parameter type. §7's "pass it as an argument" promise is closed for borrow-free functions and open for borrow-moded ones, and `suspensions.md:421` still lists that as a residual.

### 1.2 The contract half is registered at one site and asserted at one site

`&mut (s : τ ↝ τ')` means "across this boundary, a value of type τ' is owed"; `s` names the payload at entry, for use in τ', which is checked at exit (`dllbc-arrows.md` §5.1). The mechanism:

- **Mint.** `seedTelescopeV` (`Machine.lean:3134`) walks a declaration's telescope. For a `borrowT` parameter it mints σ (the entry snapshot) and ℓ (the loan), binds the slot to `borrowₘ ℓ σ`, records `(x.id, σ)` in `St.entrySyms` — this is `old *v` — and computes `owed := τ'[s := σ]`, pushing an `Obligation ⟨arg, loan, owed, trivialOwed⟩` into `St.obligations`. The snapshot is *pinned at mint*: `Obligation.owed` holds the opened term, and it lives in `St` rather than being returned so that a §10 `Refl` refinement reaches it.
- **Assert.** `auditAction` / `auditObligation` (`Machine.lean:3278`, `3345`) at return. Each obligation is either exempt (consumed into the result, or onward into another call) or locatable-and-typed: `collapseArg` ends the field loans parked in its payload, then `hasType payload owed`.
- **Caller side.** `processArgs` (`Machine.lean:4744`) re-derives the owed type at the actuals and returns `captured : List (Nat × Term)`. `buildResult` (`Machine.lean:1383`) walks the return type, minting one issued loan per `borrowT` position with its own owed type. `callDeclC` (`Machine.lean:5292`) packs both into a `Group`.

### 1.3 Groups mix two things: an ordering and a set of contracts

```lean
structure Group where
  id : Nat
  captured : List (Nat × Term)     -- (ℓ, owed type)
  issued   : List (Nat × Term)     -- (ℓ, owed type)
  exitRelease : List (Nat × Nat) := []   -- (ℓ, σ′) — §5.4 exit-snapshot pinning
```

`endGroup` (`Machine.lean:1749`) is the ending cascade: end every issued borrow first (`endIssued` — locate, type against the owed type, kill, surrender the payload), remove the group, then release each captured loan atomically — `.know (sym σ′)` if §5.4 pinned one, else a **fresh existential at the owed type**. `endLoan` (`Machine.lean:1771`) routes: a captured loan's end is the whole group's end; anything else is plain End-Mut (`sendPayloadToLoan ℓ (killBorrowInΩ ℓ)`), which hands the owner *the exact payload*, with no type check at all.

So the shape of today's system, stated plainly: **the captured half of a `Group` already IS a loan-attached debt.** `(ℓ, owed)` is a claim registered on a loan and asserted when the loan ends. What is boundary-attached is not the debt but the *authorship*: only a signature can write one, and only for the duration of a call.

### 1.4 Opacity, and what it costs and buys

Every group release is the opaque one. The identity wire — where a captured owner recovers the issued borrow's surrendered payload — was `Group.constrained`, and M28 τ deleted it with its test (`Boundaries.lean:463-475`). The reason is the one this design has to answer:

> Inferring that wire from a signature is unsound — `through` and `advance` share one and differ in exactly what it would claim.

`through (b : &mut List Nat) → &mut List Nat = b` and an `advance` returning a field reborrow of the tail are indistinguishable to a signature-only checker, so constraining the captured release to the surrendered payload is value-wrong for one of them. M27 had already deleted the *declared* backward specs (`dllbc-arrows.md` §6.2's final fold) for a different reason — the ensures IS the contract — leaving the fresh existential as the only release rule.

The cost is stated at `Boundaries.lean:355-390`: after `*r := Cons(9, Nil)` through a `through`-issued borrow, `let y = x` gives `y` a **fresh σ**; the write is forgotten in checking mode while the executing machine still hands `Cons(9, Nil)` back. "Opacity was never a fact about what happens; it is a fact about what was promised."

The buy is easy to miss and the design must not break it. `ArraySort.lean:195` and `:737`: a call re-mints the caller's payload as a fresh σ at the declared type, "so the array comes back UNCARVED and with a FLEX length — exactly the state the three-way carve needs". One body cannot both match on a length (rigidifying it) and carve at a returned index (needing it flex); the call boundary's re-mint is the only reset. `dllbc-arrows.md` §6.2 calls this "load-bearing for expressiveness rather than for hygiene, which is this calculus's novel claim in the space". **Opacity must remain the default.**

### 1.5 The M27 containment is this milestone's hole, and it says so

`auditObligation`'s first branch (`Machine.lean:3287-3296`) refuses a **non-trivial owed type on a parameter consumed into the result**:

> §6.1 exempts a borrow consumed into the result from the payload audit, so a NON-trivial owed type there is a claim neither end checks … the caller's group end mints the release AT it. A parameter passed onward into the result owes back the type it was lent; **state a richer claim on a parameter the body keeps, where the audit runs.**

Every cursor is a parameter consumed into the result. So today, no cursor can say anything about what happens to its container — and that is precisely the get_mut round-trip law. The containment's own error message names the shape of the fix: make the audit run on a parameter the body hands onward. That is what §3 below does.
---

## 2. The contract half, re-founded

### 2.1 A debt, and where it lives

A **debt** is a claim registered on a loan at the moment the loan is minted, and asserted at the moment the loan ends. It has four parts:

```lean
/-- A claim registered on loan ℓ at its mint, asserted at its end. -/
structure Debt where
  loan    : Nat                -- ℓ
  entry   : Nat                -- σ: the payload snapshot PINNED at mint (today: seedTelescopeV's σ / entrySyms)
  owed    : Term               -- τ'[s := σ]: the TYPE the payload must have at ℓ's end
  pin     : Option Term        -- e[s := σ]: the VALUE the release IS. `none` = opaque (today's rule).
  site    : DebtSite           -- .param Var | .call Nat | .local Var  — for error messages and for the audit's routing
```

and `St` gains `debts : List Debt`, replacing two existing tables:

- `St.obligations : List Obligation` — an `Obligation ⟨arg, loan, owed, trivialOwed⟩` is a `Debt` with `site = .param arg`, `pin = none`, and `trivialOwed` recomputable as `owed ≡ the payload type as written`.
- `Group.captured : List (Nat × Term)` and `Group.exitRelease : List (Nat × Nat)` — the type moves into `Debt.owed`, the pinned release σ′ becomes a `Debt.pin` of `some (sym σ′)`.

`Group` keeps only structure:

```lean
structure Group where
  id : Nat
  captured : List Nat
  issued   : List Nat
```

**The architectural statement is: a group is an ordering, a debt is a contract.** Today they are one record and that is why a debt cannot exist outside a call. Separating them is most of the milestone's mechanical work and none of its risk.

Both the entry snapshot and the pinned release survive a refinement sweep the same way `Obligation.owed` does today: `refineSym`'s `groups` map (`Machine.lean:1007`, `1050`) becomes a `debts` map over `owed` and `pin`. That is the same code, on one table instead of two.

### 2.2 The pin may mention the exit snapshots of the loans issued alongside

This is the whole content of the milestone, and everything else is plumbing.

Consider `Nth : (v : &mut List Nat, i : Nat, p : Le (S i) (Len *v)) -> &mut Nat`. A caller wants: after `let r = Nth(&m x, i, p); *r := w;` and the group's end, `x` holds `SetNth i w x_entry`. Nothing in the signature can say that today, because the fact the caller needs is a *relation between the captured loan's release and the issued borrow's exit payload* — and the issued borrow's exit payload is written by the caller, after the call has returned.

So the claim has to be parametric in it. Write the exit payload of the returned borrow as `*res`:

```
fn Nth [i] (v : &mut (s : List Nat ~> SetNth i (*res) s),
            i : Nat, p : Le (S i) (Len *v)) -> &mut Nat
```

Read: "when ℓ_v ends, its value is `SetNth i (*res) s` — the entry list with position `i` replaced by whatever came back through the borrow I returned." The owed type is not written: it is the pin's own inferred type (`List Nat`), per D1's one-slot rule.

Three facts about this shape, in the order they matter.

**It defeats the M28 τ unsoundness by declaration rather than inference.** `through` and `advance` no longer share a signature. `through` is `&mut (s : List Nat ~> List Nat = *res)`; an `advance` returning a tail reborrow is `&mut (s : List Nat ~> List Nat = Cons (Hd s) (*res))`. The wire is not read off the *shape* of the signature — it is *written in* the signature, and the callee's audit checks it. Nothing is inferred, which is the exact distinction M28 τ's retirement note asked for.

**It is the Aeneas backward function, typed rather than termed.** `dllbc-arrows.md` §5.1 already says "↝ is the backward function's type, moved into the signature". The pin finishes the sentence: the backward function is a map from the issued borrows' final payloads to the captured loans' released values, and `SetNth i (*res) s` *is* that map, written where the type already was.

**It is M27's declared backward spec, in the one place M27 did not remove content from.** M27 deleted `back` because the ensures is the contract and because a value-returning mutator can say everything it needs to in its return type over `*v` and `old *v` (§5.4). What M27's replacement does not reach is a *borrow-returning* function, which has no value component in its return type to hang a postcondition on (`retMixesBorrow` refuses one) and whose exit is not known when it returns. The pin reaches exactly that gap and nothing else. Three differences from `back`, all of them narrowings:

1. it is in the *signature*, not a second declaration kept in step by hand;
2. it is *per loan* and *optional*, not per function and all-or-nothing — a body may pin the loans whose flow it controls and leave the rest opaque;
3. its default is today's behaviour, so the array corpus's load-bearing opacity (§1.4) is untouched by writing nothing.

What it inherits from `back` and cannot escape: **composition still climbs**. To pin a loan, every group that transitively holds that loan must itself pin it. A body that hands its container to an opaque callee and then claims to know the container's exit is refused, and rightly — the sub-call released a fresh σ. This is `dllbc-arrows.md` §6.2's "an opaque sub-group is an unresolvable hole in the tree", now scoped to one loan instead of one call tree.

### 2.3 How the callee proves a pin: hole-filling, which is M27's suspension-tree reading

At the callee's audit, the returned borrow has not been written through yet — the caller will do that. So the audit checks the pin *symbolically*: mint one fresh **exit-snapshot σ per issued loan**, substitute those for the issued markers sitting in the parameter's payload, and convert.

Concretely, for `Nth`'s `Cons`/`Z` branch — body returns `&m *hd`:

```
Ω:  v ↦ borrowₘ ℓ_v (Cons (loanₘ ℓ_hd) tl)        -- the head was reborrowed out
    result = borrowₘ ℓ_hd σ_hd
issued exit σ:  ℓ_hd ↦ σ_res
hole-filled payload of ℓ_v:  Cons σ_res tl
the pin, opened:             SetNth Z σ_res (Cons hd_entry tl)   ⇝   Cons σ_res tl
convert: ✓
```

and for the `S(k)` branch, where the body's own recursive call holds the tail loan:

```
Ω:  v ↦ borrowₘ ℓ_v (Cons hd (loanₘ ℓ_tl))
    group g: captured = [ℓ_tl], issued = [ℓ_r];  result = borrowₘ ℓ_r σ
```

Here the hole under `ℓ_tl` is not a plain marker — it is a captured loan of a live group. The audit **projects** the group's debt instead of ending it: ℓ_tl's release, under the recursive call's own pin, is `SetNth k (*res) tl_entry` with `*res := σ_res`. So

```
hole-filled payload of ℓ_v:  Cons hd (SetNth k σ_res tl_entry)
the pin, opened:             SetNth (S k) σ_res (Cons hd tl_entry)   ⇝   Cons hd (SetNth k σ_res tl_entry)
convert: ✓  (definitionally, by SetNth's own recursion)
```

Two things to note about that. The recursion resolves through the group's own declared pin, which is the same self-referential move M27's declared backs made and the same one `reachesLoan` (`Machine.lean:3254`) already models for the exemption walk — it is not a new kind of reasoning. And the operation needed is **not** `endGroup`: ending the group would end the issued borrow ℓ_r, which is this function's own result and must not be ended. It is a new, pure, non-mutating function:

```lean
/-- The value a captured loan would be released with, computed from the group's
    pins with each issued loan standing for its exit-snapshot σ. No store events. -/
def projectDebt (fuel : Nat) (exits : List (Nat × Nat)) (ℓ : Nat) : M (Option Term)
```

At a real caller's group end, the *same* function runs with `exits` instantiated to the actually-surrendered payloads instead of fresh σ's. One rule, two instantiations — which is the uniformity test this design should be held to.

### 2.4 The pin is a value, and it has to be — there is no binder at a group end

The obvious alternative is the propositional one the calculus otherwise prefers: let the debt be a *type* (a Σ carrying evidence) and let the caller project the proof, the way `quicksortA`'s return type carries `Σ (hs : SortedA n (*a)) → Π x. Id Nat (CountA x n (*a)) (CountA x n (old *a))` today. It does not work here, for two independent reasons, and both are worth writing down because they are what forces the design.

**A type-level release changes the owner's type.** Today the release is `.know (sym σ)` with `sctx[σ] = owed`. If `owed` were `Σ (l : List Nat) → Id (List Nat) l (SetNth i σ_r s)`, the owner's slot would hold a *pair*, not a list, and `let y = x` would give the caller a pair. Type-level precision reaches indices (`Vec T (S n)`) and stops there; it cannot pin a value without changing what the value is.

**Evidence needs a binder, and a group end has none.** §5.4's device — mint σ′, pin the captured release to σ′, and let the return type's `*v` read σ′, so the caller holds the owner and the evidence about the same σ′ (`Group.exitRelease`, `callDeclC`'s `exitRel`) — works because the evidence is delivered *in the return value*, at the call, where there is a `let` to bind it. The get_mut fact is not available at the call; it becomes available at the group end, and a group end is a store event triggered by a demand three statements later. There is nowhere to put a proof term.

One could *give* it a binder — make ends explicit, `let (x, h) = end b;`. That is a coherent language, and it is a different one: the ending discipline stops being lazy and demand-driven, which is the mechanism §5.2's "every demand collapses first" is built out of and which seven separate sites were found to need. It is recorded as option D2-c below and recommended against for this milestone.

So the pin is definitional, and delivered by refining the released σ. Which, spelled through the machinery that already exists, is: mint σ′ at `owed` as today, then `refineSym σ′ (the pin)`. The `pin = none` case skips the refinement and *is* today's rule, line for line. That is the compatibility argument in one sentence.

### 2.5 Naming the issued exits

`*res` above needs a definition. The corpus already reads two snapshot conventions fluently: inside a return type, `*v` is a borrow parameter's **exit** snapshot and `old *v` is its **entry** snapshot (§5.4, `St.exitSyms` / `St.entrySyms`). A debt is likewise checked at exit, so the same convention should hold inside one: the binder `s` is the entry, and any deref reads an exit.

The proposal is a **reserved name `res`** denoting the function's whole result, with ordinary field navigation for multi-borrow returns:

- `*res` — the exit payload of a single returned `&mut`;
- `*(fst res)`, `*(snd res)` — the components of a `Σ`-returned pair of borrows (`Nth2`, `split_at_mut`).

It needs no change to how return types are written, it composes with `Σ` without inventing named return binders, and `Pos`/`navStep` already does field navigation over `Val` trees so the caller-side instantiation is the walk `collectResultBorrows` makes anyway. The runner-up — naming return components in the signature, `-> (r : &mut Nat)` — reads better and costs a syntax change at every borrow-returning signature; it is D3-b below.

### 2.6 Where a debt may be registered: signatures become one mint site among many

Three mint sites, of which the first is today's:

1. **A telescope position.** `seedTelescopeV` registers a debt per `borrowT` parameter. Unchanged, except that it writes into `debts` rather than `obligations`, and it now carries a `pin`.
2. **A call.** `processArgs` registers a debt per borrow argument, from the callee's parameter type instantiated at the actuals. Unchanged, except that `Group.captured` no longer carries the type.
3. **A local `&mut`.** `let b = (&m x : &mut (s : List Nat ~> e));` registers a debt on the loan the `&m` mints. This is new, and it is the sentence "signatures become one mint site among many" made operational.

Site 3's surface form is a real decision (D7). The ascription node `.seal site t u` already exists and already means "check, then forget" — `sealValue` mints a fresh σ at the ascribed type. The natural extension is that **for a borrow-typed ascription, "forget" means reborrow**: `(&m x : &mut (s : τ ~> e))` mints a fresh loan ℓ′ carrying the debt, whose payload is the ascribed borrow and whose end sends its payload home to ℓ. A contracted reborrow, uniform with what a seal does to every other value. The wrinkle to flag: `sealNode` interns by `(site, captured inputs)` so that reading one seal twice yields one σ, and a reborrow must be a *fresh loan every time* — so the borrow case must not intern. That is one branch, but it is a branch in a rule whose whole point is that it has none.

### 2.7 Stacking, and the one thing a caller may not do

A loan may carry more than one debt: a local mint's, plus the one a call registers when the borrow is passed. The rule:

- **every** debt's `owed` is asserted at ℓ's end;
- **at most one** pin may be effective; two pins must convert (checked at the second registration, where both are in hand);
- the release is the pin if one exists, else a fresh σ at the *conjunction* of the owed types — in practice, the most recently registered one, with the others asserted against it.

And the prohibition: **a caller may not strengthen a debt at a call.** Registering `~> e` (a pin) on a loan being handed to a parameter typed `~> τ''` with no pin would be asserting what nobody checks — the callee promised τ'' and the group will release at τ''. This is the M28 τ unsoundness wearing the caller's clothes, and the check that stops it is: at a call, the parameter's debt must **entail** every debt already on the loan. A caller may register a *weaker* debt at its own mint (a deliberate assertion checkpoint); it may not register a stronger one and have it believed.
---

## 3. The three assertion sites

A debt is asserted when its loan ends. There are three ways a loan ends, and today the system installs a real check at one of them.

### 3.1 Demand

`endLoan` (`Machine.lean:1771`), reached from every rule that reads or writes a place — the `.var` move, `&mut`, the take through `*b`, the match scrutinee, the comptime deref, the bare comptime `.var`, and (since M29 δ) the assignment `⇐` (`Boundaries.lean:404-460`). §5.2's "every demand collapses first".

Today, two disjoint behaviours: a captured loan routes to `endGroup`, which asserts the issued borrows' owed types and releases the captured ones at their owed types; a plain loan takes `sendPayloadToLoan ℓ (killBorrowInΩ ℓ)`, which hands the owner the exact payload **with no check at all**.

Under the re-founding both become one rule:

```
end ℓ:
  1. collapse: End-Mut every loan marker parked in ℓ's payload (unchanged)
  2. compute the release r:
       - ℓ is a group's captured loan  → the group cascade (§3.4 below) supplies it
       - otherwise                     → the payload itself (today's plain End-Mut)
  3. for every debt d on ℓ:  assert  Ω ⊢ r : d.owed;  if d.pin is present, assert  r ≡ d.pin
  4. send r home to ℓ's marker; drop ℓ's debts
```

Step 3 on a plain loan is new and is exactly what makes a local debt meaningful: `let b = (&m x : &mut (s : List Nat ~> List Nat = Cons 9 s));` is an assertion checkpoint that the next demand on `x` checks. It never *weakens* what the owner recovers — the release is still the payload — so a local debt buys checking, not forgetting. (D14.)

### 3.2 Scope pop

`popScope` / `dropScopeEntries` (`Machine.lean:1814-1840`). Today the sweep ends every borrow a popped entry *holds*, and then truncates — **retaining** entries that still carry an ownership node, because "a scope-local whose borrow escaped the scope keeps its storage, because that storage is where the escaping borrow's payload returns to". The comment is explicit that this is a heuristic on the executing side only: "The checker rejects an escaping borrow of a local at the audit's boundary check, so this retention is only ever reached by the executing machine on a program the checker never saw."

Under the re-founding, a scope pop is an assertion site, and the retention gets its principled statement:

```
pop scope:
  1. the drop sweep, in reverse binding order (unchanged) — ending a borrow asserts its debts by §3.1
  2. for every loan MARKER in an entry about to be discarded:
       - the loan is held by an enclosing frame or a live group → fine, its story continues elsewhere
       - the loan is still outstanding and its owner is leaving  → REJECT:
           "borrow of a local escapes its scope: ℓ's owner leaves scope while the loan is live"
  3. truncate
```

Step 2's rejection is what makes the executing machine's retention unreachable *by construction* rather than by an audit that happens to be positioned downstream. It is Rust's lifetime rule with no lifetimes: the loan-attached debt has nowhere to be paid, so the program is refused where the payment was due. The executing machine keeps its retention — the two machines legitimately differ on programs the checker never admits, which is the standing arrangement (`Machine.lean:1798-1801`).

### 3.3 Function exit

`auditAction` (`Machine.lean:3345`). This is today's exit audit, and it is where the most changes land.

```
audit:
  0. mint one exit-snapshot σ per ISSUED loan (the loans of the borrows this body is returning),
     the mirror of St.exitSyms for parameters
  1. ex-falso admission (unchanged)
  2. for each debt whose loan is a parameter's:
       - locatable and not continued  → collapse in place, then assert as §3.1 step 3
       - consumed into the result, or onward into a call  → HOLE-FILL and assert:
           fill each issued marker with its exit σ, project any live group's pin (§2.3),
           then check owed and pin against the filled payload
  3. for each issued loan: its own debt's owed type against the returned payload (today's
     collectResultBorrows check), plus its pin if it has one (§5, the read-only law)
  4. the value-return path (retTyVal, exitSyms substitution) — unchanged
```

Step 2's second branch is the repeal of the M27 containment (§1.5). Today "consumed into the result" is an *exemption*; under the re-founding it is a *different check*, because there is now something to check against. The containment's rejection message goes away and the honest failure moves to where it belongs: a pin the body does not implement fails to convert, with the two sides printed.

Note what does **not** change: a parameter with no pin and a trivial owed type is exempt exactly as today, because hole-filling a trivial claim proves nothing. So the corpus's existing cursors (`Nth`, `Nth2`, `Swap`, `splitA`, `partitionA`) audit by the identical path they take now.

#### 3.3.1 The exemption is currently too coarse, and hole-filling is the fix

This was found independently and concurrently by the `hm-probe-getmut` lane (its FINDING 2), and it turns §3.3 from a precision feature into a soundness repair. The exemption in `auditObligation` is granted to the **whole parameter** when *any* borrow derived from it is returned, rather than to the returned sub-place only. So a callee may leave a hole in a sibling leaf and be accepted:

```
fn SiblingHole (a : &mut (Array 3 Nat)) -> &mut Nat {
  let l = &m (*a)[Z ; 1];
  let c = &m (*a)[1 ; 1];
  let r = &m (*a)[2 ; ..];
  let t = (*l)[0 ; 1];        -- RANGE read: takes the run out and never refills it
  let e = &m (*c)[0];
  e }
```

`a`'s payload is not whole at the exit audit — leaf `l` holds `⊥` — and the program is **accepted today**. The control that shows the check exists when it is reachable is the same body with the hole in the *returned* cell, which is rejected with "cannot type value ⊥"; and the index-read variant `(*l)[0]` is correctly accepted, because §2.1's copy-on-read leaves an index-kind value intact and there is no hole.

Hole-filling closes it without a special case. The exemption disappears: the parameter's payload is checked *whole*, with the issued markers filled by their exit σ's, so a `⊥` in a sibling leaf fails `hasType` exactly as it does in the returned leaf. The reason the exemption existed — "a borrow that left in the result has no payload here to audit" — is true of the returned *sub-place* and was over-applied to the parameter containing it.

This means stage 5 of the staging plan should be expected to **reject a program the corpus currently accepts**, and `g2SiblingHole` (in the probe lane's file) is the witness. That is the differential to pin before the stage starts.

### 3.4 The group cascade, with debts

`endGroup` becomes:

```
end group g:
  1. end each issued ℓᵢ: locate its payload, assert its own debts (owed, and pin if any),
     kill it, and record its surrendered payload as ℓᵢ's EXIT VALUE
  2. remove g
  3. for each captured ℓⱼ, atomically:
       r := projectDebt(exits := the surrendered payloads, ℓⱼ)
              -- some e  → .know (nf e)          the pinned release
              -- none    → .know (sym σ), σ fresh at ℓⱼ's owed type    TODAY'S RULE
       assert every debt on ℓⱼ against r; send r home
```

The ordering — issued first, then captured atomically — is unchanged and is still the soundness argument. What changes is that step 3 now has a non-opaque case, and that case is *declared and checked* rather than inferred.

Two consequences worth stating explicitly because the brief asks for them:

**Today's fresh-σ release IS the trivial debt.** `pin = none` reproduces `endGroup`'s current `none` branch character for character. There is no behavioural delta for any program in the corpus that does not write a pin.

**A caller does not state a debt at a call boundary; it reads one.** The debt at a call comes from the callee's parameter type. The caller's only authorship is at its *own* mints (§2.6 site 3), and those may not strengthen (§2.7). This is the answer to "how does a caller state a NON-trivial debt at a call boundary" — it doesn't, and the reason it doesn't is the M28 τ finding.

---

## 4. The shape half

### 4.1 `&mut τ` as a value predicate

The judgment the SUGGESTIONS entry asks for, spelled against the code:

```
Ω ⊢ v : &mut (s : τ ~> τ')   ⟺   v = borrowₘ ℓ p,  and
                                 (a)  ⊢ p : τ          -- the PURE conjunct: Ω-independent given p
                                 (b)  ℓ carries a debt entailing τ'[s := its entry σ]   -- the STORE conjunct
```

which is one new case of `hasType`:

```lean
| .borrowM ℓ p, .borrowT sn τ S =>
    if !(← hasType fuel p τ) then pure false
    else match (← get).debts.filter (·.loan == ℓ) with
      | [] => pure false     -- a loan with no debt cannot meet a contract
      | ds => pure (ds.any (fun d => Pure.convert fuel d.owed (open τ' at d.entry)))
```

The knowledge/state split relocates rather than dies, exactly as the entry predicts: **pure types are Ω-independent and converted; borrow types are Ω-relative and met.** Conjunct (a) is conversion, conjunct (b) is a store lookup.

### 4.2 What the telescope-position doctrine was for, and what replaces it

The doctrine's real job was keeping every boundary-crossing borrow visible to the obligation walk. That job is already done value-directed, by machinery that searches value trees rather than positions: `findBorrowPayload`, `Val.loanIds`, `firstLoanMarker`, `firstHeldBorrow`, `reachesLoan`, and Stage 0's drop sweep. `auditObligation` already says so in its own docstring — a borrow must be locatable "as a live `borrowₘ ℓ` anywhere in Ω's values, not just at its own slot (it may have been moved into a local value)". The doctrine is belt over braces.

But it also did a second job by accident, and *that* one needs a replacement: it kept `readC` from ever having to decide what a borrow type means in a pure context. Under the split, `readC` reflects `borrowT` (it is already a `Term`; reflecting it is `readC` on the two components and rebuild), and the question "does `&mut Nat` convert with `&mut Nat`?" becomes askable. The answer must be: structurally yes, and **borrow types are excluded from the proof fragment**. A `borrowT` may not occur inside an `Id`, inside a `Σ` a proof inhabits, or anywhere `Pure.nf` output is consumed as a proof term. The reason is sharp: `hasType` on a borrow reads mutable store, so if a proof's validity could depend on it, a proof would be store-dependent and the comptime fragment would stop being a fragment.

**That exclusion is the precise, weaker successor to M26-C's doctrine**: borrow types leave the *position* language and enter the *value* language, but do not enter the *proof* language. It is checkable syntactically (`hasBorrowT` already exists and is already used for exactly this kind of gating) and it should be checked, not assumed.

### 4.3 E4's enumeration shrinks to the contract form

E4 (`functions-are-comptime.md:737`, answered at `:374-389`) asked where a *type* could be demanded of a borrow-moded λ. Its answer collapsed because a borrow-moded Π has no `Val`, so `hasType` cannot be asked; the one live consequence is that **passing a function whose signature has a `&mut` binder is refused** by `processArgs`' `readCWith` of the parameter type, with §7's "pass it as an argument" promise left open for that case and `suspensions.md:421` still carrying it as a residual.

Once `readC` reflects `borrowT`, a borrow-moded Π has a reading, `fsig`'s reason for existing weakens (it can merge into `sctx`, though it need not in this milestone — D8), and the refusal can be lifted. What is left of E4 is exactly what the SUGGESTIONS entry predicts: **the contract form.** Two borrow-moded Π's agree iff their telescopes agree, and agreement at a borrow domain is agreement of the contract — τ converts, S converts, and the pins convert. `piAgree` (`Machine.lean:2753`) already does telescope agreement on `Term`s and is where that lands. E4 stops being "which sites can be asked" and becomes "how do two contracts compare", which is one function.

---

## 5. Read-only borrows: a contract, not a type former

Flag this one; it is a language-design observation, not an implementation detail.

Give the **issued** borrow the identity pin:

```
fn Get (c : &mut (s : Container ~> Container = SetAt i (*res) s), i : Nat) -> &mut (t : Nat ~> Nat = t)
```

The returned borrow's own debt says: *what comes back through this borrow is what went out through it*. `endIssued` asserts it, so a caller that writes through `r` is rejected — "this borrow is read-only" — and a caller that only reads passes. And then the container's pin computes: `SetAt i (*res) s` with `*res = Nth i s` gives `SetAt i (Nth i s) s`, which reduces to `s` under the container's own lemma. **The caller derives that the container is unchanged**; it is not separately asserted.

So a shared reference is a contract on `&mut`, not a new type former — and `&τ`, which SUGGESTIONS.md:119-126 cut from the roadmap on 2026-08-13, may be obviated for its principal motivation without being reinstated.

**The honest limit, which must not be skipped.** Identity-pinned `&mut` gives *non-mutation*. It does not give *aliasing*: the borrow is still exclusive, so two of them cannot coexist over one place, and the cut entry's other motivations — "non-destructive reads; functions chosen/created at runtime; λ capture of runtime things via aliasing (nbe.md §3's door)" — are untouched. If the user's motivating examples for `&τ` turn out to be about read-sharing, this observation does not serve them; if they are about not-writing, it removes the need for the type former entirely. Worth weighing before `&τ` returns to the roadmap, which is why it is flagged here rather than filed.

A second, smaller payoff: the identity pin also gives the calculus a **checked no-op boundary**. `fn Id (v : &mut (s : τ ~> τ = s)) -> Unit` is a function that provably does not touch its argument, which is not currently sayable at all.

---

## 6. §19 move semantics for borrow-carrying data

Once `&mut` is a value predicate, `Pair(&mut A, &mut B)` and `List (&mut T)` are ordinary values, and three rules that are currently correct-by-vacuity stop being so.

**Moves must collapse the whole tree, not the top.** `readR`'s `.var` case (`Machine.lean:4080-4090`) ends a parked reborrow only when the moved value *is* a `borrowₘ` at top level; a `Pair` of borrows falls to the plain `setSlot x .bot; pure v`. The generalization is the one the sweep functions already have: find the first loan marker **anywhere in the tree** (`firstLoanMarker` already recurses), end it, retry. Same rule, one predicate widened. The take (`.deref`) and the `&mut` reborrow (`Machine.lean:4118-4141`) already use the recursive form, so this is bringing the move into line with its two siblings rather than inventing a rule.

**`indexKindV` must refuse borrow-carrying values.** §2.1's copy-on-read leaves the owner intact for index-kind values (Nat/Bool/Unit trees, proofs, types, λs, σ's typed as one of those). None of those can carry a borrow today, so the check is vacuous; once borrows live in data it must be explicit, because copying a borrow duplicates exclusive access. One conjunct in `indexKindV` (`Machine.lean:546`), and it is a soundness conjunct — worth a negative test of its own.

**A debt survives relocation, and that is the payoff.** `Obligation` is keyed by `arg : Var` — a *slot* — which is why `auditObligation` has to search Ω for a borrow that "may have been moved into a local value" and why `collapseArg` and `collapseLoanIn` are two functions for one job. A `Debt` is keyed by ℓ. Moving a borrow into a pair, out of a pair, into a returned structure, or across a call changes nothing about its debt. That is the concrete reason loan-attachment is not merely a nicer spelling.

**What stays vacuous, deliberately.** Borrows inside *comptime* data stay unwritable — a ⇝-read of `&mut` is meaningless (`seedTelescopeV`, `processArgs` both check it), and §4.2's proof-fragment exclusion is the same rule at type level. So `List (&mut T)` is a runtime value only, and no proof ever mentions one.

---

## 7. Escape rules for borrows in returned data

Today a returned borrow is "issued" and its loan joins the group; a body returning `&m localX` is caught late or not at all — `collectResultBorrows` accepts it, the caller's group gets `issued = [ℓ_local]` with no captured loan, and `endIssued` surrenders the payload into nothing while the local's storage is gone.

The rule follows from §3.2 and needs no new machinery:

> **A loan may be issued only if its owner outlives the group.** At function exit, every issued loan must be rooted — transitively via `reachesLoan` — in a *parameter's* loan. A loan rooted in a local is refused at the scope pop, because its debt has nowhere to be paid.

This is exactly what `reachesLoan` computes for the exemption walk, run in the opposite direction, so the implementation is a reuse rather than an addition. For borrow-carrying returned *data* — a `Pair` of borrows, a `List` of them — the same walk applies per position, which is why it is stated on loans rather than on return-type positions.

The one case that needs a decision rather than a derivation is a borrow issued from a loan the body *created* over a value it also returns (a self-referential structure). The recommendation is to refuse it outright in this milestone: it is unreachable from the acceptance tests, and admitting it would need a notion of a loan whose owner is inside the returned value, which is a lifetime in all but name.
---

## 8. Kernel touch-point survey

Every site the milestone touches, what it does today, and what happens to it. Line numbers against `b8721644`. This is a survey, not a plan — the staging is §10.

### 8.1 State and structures

| site | today | change |
| --- | --- | --- |
| `Obligation` (`Machine.lean:55`) | `⟨arg, loan, owed, trivialOwed⟩`, held in `St.obligations` | **replaced** by `Debt`; `arg` becomes `DebtSite.param`, `trivialOwed` recomputed |
| `Group` (`Machine.lean:80`) | `⟨id, captured : [(ℓ,Term)], issued : [(ℓ,Term)], exitRelease : [(ℓ,σ)]⟩` | **narrowed** to `⟨id, captured : [ℓ], issued : [ℓ]⟩`; the types move to `Debt.owed`, `exitRelease` becomes `Debt.pin` |
| `St.obligations` (`Machine.lean:~140`) | per-path obligation list | **merged** into `St.debts` |
| `St.entrySyms` / `St.exitSyms` (`Machine.lean:~160`) | `old *v` / `*v`, per borrow *parameter* | `entrySyms` becomes `Debt.entry` (every loan gets one, not just parameters); `exitSyms` gains an **issued-loan** twin (§3.3 step 0) |
| `St.fsig` (`Machine.lean:~103`) | signatures of σ's whose Π has no `Val` | **may merge into `sctx`** once `readC` reflects `borrowT` (D8; not required by this milestone) |

### 8.2 The shape half

| site | today | change |
| --- | --- | --- |
| `readC` `.borrowT` (`Machine.lean:1250`) | refuses by name | **reflects**: `readC` the two components, rebuild |
| `readR` `.borrowT` (`Machine.lean:4387`) | refuses "not a movable value" | **keeps refusing**, with the ordinary type-former message (⇒ does not move types) |
| `hasType` (`Machine.lean:1457`) | no `borrowM` case; refuses a borrow-moded Π via `hasBorrowT` | **new case** `borrowM / borrowT` (§4.1); the Π refusal narrows to the proof-fragment exclusion |
| `hasBorrowT` (`Syntax.lean:959`) | "does this type contain a borrow" — a gate | **stays**, repurposed as the proof-fragment exclusion (§4.2) |
| `retMixesBorrow` (`Syntax.lean:~1000`) | refuses a return type mixing borrow and value components | **liftable** once the borrow component has a value judgment (D9) |
| `piAgree` (`Machine.lean:2753`) | telescope agreement on `Term`s | **gains contract comparison** at borrow domains (E4's residue, §4.3) |
| `processArgs` `readCWith` refusal | "borrow type is only valid at a telescope position" when a *function-typed* parameter has a `&mut` binder | **lifted**; closes §7's pass-as-argument promise / `suspensions.md:421` |
| `indexKindV` (`Machine.lean:546`) | copy-on-read predicate; vacuously borrow-free | **must refuse** borrow-carrying values (§6) |

### 8.3 The contract half

| site | today | change |
| --- | --- | --- |
| `seedTelescopeV` (`Machine.lean:3134`) | mints σ+ℓ per `borrowT` param, pushes `Obligation` | writes a `Debt` with `pin`; the `sigmaT _ _ (borrowT …)` slice special case becomes an instance of the general walk (D10) |
| `processArgs` (`Machine.lean:4744`) | returns `captured : [(ℓ, owed)]` | registers a `Debt` per borrow argument; the entailment check for stacked debts (§2.7) lands here |
| `buildResult` (`Machine.lean:1383`) | mints one issued loan per `borrowT` position with an owed type | registers each issued loan's `Debt`, including the identity pin (§5) |
| `callDeclC` (`Machine.lean:5292`) | packs `Group` with types and `exitRel` | packs the narrowed `Group`; the `exitRel` σ-minting becomes `Debt.pin := some (sym σ′)` |
| `endIssued` (`Machine.lean:1732`) | locate, `hasType` against owed, kill, surrender | additionally asserts the issued loan's **pin** (this is where read-only is enforced) |
| `endGroup` (`Machine.lean:1749`) | cascade; fresh σ per captured loan | calls `projectDebt` (new); `none` reproduces today exactly |
| `endLoan` (`Machine.lean:1771`) | group-aware routing; plain End-Mut is uncheck | **asserts debts** on the plain path too (§3.1) |
| `auditObligation` (`Machine.lean:3278`) | M27 containment; exempt-or-locate-and-type | containment **repealed**; the exempt branch becomes the hole-filling check (§3.3) |
| `auditAction` (`Machine.lean:3345`) | ex-falso, `collectResultBorrows`, obligation walk, value-return path | gains the issued-exit σ mint and routes to the new obligation walk |
| `collectResultBorrows` (`Machine.lean:3320`) | walks the return type against the result | unchanged in shape; feeds the issued-exit map |
| `popScope` / `dropScopeEntries` (`Machine.lean:1814`) | sweep + retain-ownership-nodes | gains the escape rejection (§3.2 step 2) in checking mode |
| `refineSym` `groups` map (`Machine.lean:1007`, `1050`) | refines owed types in `groups` and `obligations` | one map over `debts` instead of two |
| `reachesLoan` (`Machine.lean:3254`) | reborrow-chain + group-link reachability | **reused** for the escape rule (§7), run the other way |
| *(new)* `projectDebt` | — | pure computation of a captured loan's release from pins and an exit map (§2.3) |

### 8.4 Surface / elaboration

| site | today | change |
| --- | --- | --- |
| `Uni.lean:535-552` | `&mut (s : τ ~> τ')` → `.borrowT`; `&mut` in ⇒ position refused | adds the pin slot to the surface (D1's spelling) |
| `FnMacro.lean:116`, `406` | `absVar` over `borrowT`; the borrow-param branch | must abstract over the pin too |
| `.seal` / `sealValue` (`Machine.lean:5060`) | ascription = check then mint a fresh σ | **new borrow branch**: a contracted reborrow, not interned (D7) |

---

## 9. DECISIONS

Every point where the SUGGESTIONS sketch underdetermines the design. Options, trade-offs, recommendation. Nothing here is silently chosen.

### D1. Is a debt a type claim, a value claim, or both?

- **(a) Type only** (today's `~> τ'`, extended in scope). Smallest change; `hasType` is the only judgment needed. **Cannot express the get_mut law** — §2.4's two arguments.
- **(b) Value only** — the debt *is* a term, its type inferred. Fewest slots; but this calculus checks rather than synthesizes, and `push`'s `&mut (s : Vec T n ~> Vec T (S n))` states a type it has no term for.
- **(c) One slot, kind-classified** (2026-08-19, user ruling — supersedes the earlier two-slot `~> τ' = e` spelling). The RHS of `~>` is a single term, elaborated under the binders in scope (`s`, and `res` where the signature issues borrows), and classified by its type: **if it has type `Type`, it is the owed-type claim — today's meaning, unchanged; otherwise it is a pin, and the owed type is the term's own inferred type.** `&mut (s : τ ~> τ')` and `&mut τ` keep their exact current meaning; `&mut (s : List Nat ~> SetNth i (*res) s)` is the pin. No `= e` connective exists.

**RESOLVED: (c), in the one-slot form.** A type claim and a value claim are different claims, both already occur in the corpus, and (c) is the only option that is a strict superset of today — and the one-slot spelling retires the bikeshed rather than picking a color. Why the overload is safe in THIS calculus: types are already terms, so there is no grammar fork, only one elaborator classification — and the collision case cannot arise, because a runtime borrow's payload is runtime data and nothing of type `Type` is one, so "is the RHS a type or a value" has exactly one answer for every well-formed borrow. The reading it buys is a **precision ladder on one slot** — `~> List Nat` (some list) ⊑ `~> Σ (l : List Nat). Id (Len l) (Len s)` (a list this long) ⊑ `~> SetNth i (*res) s` (exactly this) — with the landed opaque fill sitting between the rungs as the ∀-shadow of a pin nobody wrote. Three corners, each with an obvious rule: a value whose type does not synthesize (`~> Nil`, a λ-headed pin) takes an ascription — `~> (Nil : List Nat)` — the existing seal form doing its existing job, rhyming with the λ-needs-a-destination law; a `res`-citing TYPE remains grammatically possible and inherits §2.4's objection (allowed, useless, no special case); and the old `e : τ'` registration check collapses into the synthesis itself.

### D2. How does the pinned release reach the caller?

- **(a) Definitional refinement.** Mint σ′ at `owed` as today, then `refineSym σ′ e`. Uses existing machinery; `pin = none` is byte-for-byte today's rule. **Simplification under D1's one-slot form (2026-08-19):** when the RHS is a pin, the owed type IS the pin's own type, so the mint-then-refine two-step collapses — the release is `.know (nf e)` directly, and the σ′ intermediary exists only on the type-claim rung of the ladder.
- **(b) Propositional evidence in the return type.** Refuted in §2.4: no binder exists at a group end, and a Σ-typed release changes the owner's type.
- **(c) An explicit binder-carrying end**, `let (x, h) = end b;`. Coherent, and a different language: the ending discipline stops being lazy and demand-driven, which seven separately-discovered sites depend on (`dllbc-arrows.md` §5.2).

**Recommend (a).** (c) is worth recording as a future direction if explicit ends ever become desirable for other reasons; it should not be smuggled in here.

### D3. How are the issued borrows' exit snapshots named inside a debt?

- **(a) Reserved `res` with field navigation** — `*res`, `*(fst res)`, `*(snd res)`. No signature-syntax change; composes with `Σ`; `Pos`/`navStep` already navigates.
- **(b) Named return binders** — `-> (r : &mut Nat)` and the debt says `*r`. Reads better, especially for `split_at_mut` where `*(fst res)` is opaque. Costs a syntax change at every borrow-returning signature and a binder-scoping question (a parameter's type mentioning a *later*-bound name, which telescopes do not otherwise do).
- **(c) A second binder on `borrowT`** — `&mut (s ~> x : τ)`. Rejected: it names the wrong thing (the loan's own exit, not the issued ones').

**Recommend (a) now, (b) as a follow-on** if the acceptance tests read badly. (b) is a surface change over the same kernel, so choosing (a) does not foreclose it.

### D4. Where do debts live?

- **(a) Extend `Obligation`** and leave `Group.captured` carrying types. Two tables, still.
- **(b) Extend `Group.captured`** to carry pins and leave `Obligation` alone. Debts outside a call still impossible.
- **(c) One `St.debts`, keyed by ℓ; `Group` becomes ordering-only.**

**Recommend (c).** It is the structural content of "loan-attached", and it is what makes §6's "a debt survives relocation" true rather than aspirational.

### D5. May one loan carry several debts?

- **(a) Forbid** — a loan already carrying a debt cannot be re-registered. Simple; makes `let b = (&m x : …); f(b)` illegal, which is a plausible program.
- **(b) Stack**: all owed types asserted, at most one effective pin, two pins must convert.

**Recommend (b).** The cost is one entailment check at registration (§2.7), and (a) would make the local mint site nearly useless.

### D6. May a caller strengthen a debt at a call?

**No**, and this is not really a choice — it is the M28 τ unsoundness. Recorded as a decision because it is the question a reader will ask, and because the *check* that enforces it (parameter debt entails existing debts, at `processArgs`) has to be written on purpose.

### D7. What is the surface form of a non-telescope mint?

- **(a) A borrow branch on `.seal`** — `(&m x : &mut (s : τ ~> e))` is a *contracted reborrow*: fresh loan carrying the debt, payload the ascribed borrow, end sends home. Uniform with what a seal does to every other value ("forget" = mint a fresh thing at the ascribed type). Wrinkle: `sealNode` interns by `(site, inputs)` and a reborrow must be fresh each time, so this branch must not intern — a carve-out in a rule whose selling point is that it has none.
- **(b) A typed `let`** — `.letIn` gains an optional type. Clean semantics, but `.letIn` is threaded through three drivers (`readR`, `explore`, `letStep`) and the surface, and a type on a `let` invites the question of what it means for non-borrow types (an ascription — i.e. a seal — which is (a) again).
- **(c) A dedicated node** `.borrowAt place ty`. Honest and small; adds a syntactic form for something that is morally an ascription.

**Recommend (a)**, with the interning carve-out written down at the site and a test that two textually identical local mints in a loop get distinct loans. (c) is the fallback if the carve-out proves contagious.

### D8. Does `readC` reflect `borrowT`, and does `fsig` merge into `sctx`?

Reflecting: **yes** — it is the shape half, and it is what lifts the pass-a-borrow-moded-function refusal. Merging `fsig` into `sctx`: **not in this milestone.** The merge is a separate simplification whose only driver is tidiness, it touches `callDeclC`'s dispatch, and doing it here would make the differential for the borrow change unreadable. File it.

### D9. Lift `retMixesBorrow`?

- **(a) Keep the refusal.** The acceptance tests do not need it: get_mut's precision rides in the *parameter's* pin, not in a value component of the return type.
- **(b) Lift it.** Makes `Σ (r : &mut Nat) → Id Nat (*r) (Nth i (old *v))` writable — "the borrow you got points at the i-th element" — which is genuinely useful and is the natural way to state *where* a cursor points, as opposed to what it does.

**Recommend (b), staged last.** It is a real capability, it is not needed by any acceptance test, and it is the easiest thing to cut if the milestone runs long. Note the M27 reason the containment exists (a non-borrow component of a borrow-carrying return type is judged by nothing) is answered by the same `hasType` case the shape half adds — the audit can judge the whole return type structurally once every component has a judgment.

### D10. Does the M24 slice `Σ (c : Nat) → &mut (Array c T)` special case go away?

The `sigmaT cn aTy (borrowT sn τ S)` branches in `seedTelescopeV` and `processArgs` are one hand-cut shape. Once a borrow is a value predicate, the general rule — walk the type, register a debt per borrow position — subsumes it.

- **(a) Leave it.** No risk, but the "special-cased crack in a general wall" the SUGGESTIONS entry names stays cracked.
- **(b) Delete it and let the general walk cover it.** The array corpus (`ArraySort`, `Arrays`) is the regression surface and it is the most expensive part of the build.

**Recommend (b), with the array corpus as the gate.** If it does not fall out of the general walk, that is evidence the general walk is wrong, and it is better to learn that inside this milestone than to leave a second mechanism behind.

### D11. §19 move: widen the collapse, and refuse borrow-carrying index-kind values?

Both **yes**, and both are one-conjunct changes (§6). The `indexKindV` conjunct is a soundness conjunct and needs its own negative test.

### D12. What happens to the M27 containment?

- **(a) Narrow** — refuse a non-trivial owed type on a consumed parameter *only when it has no pin*.
- **(b) Repeal** — the hole-filling audit checks both the owed type and the pin on a consumed parameter, so there is no unjudged position left.

**Recommend (b).** Hole-filling makes the type claim checkable too (fill the issued markers with unconstrained σ's, then `hasType`), and a claim that holds only for *some* writes fails to convert — which is the correct answer, not a gap.

### D13. Is the escape rejection (§3.2 step 2) checking-mode only?

**Yes.** The executing machine keeps `popScope`'s retention. The two machines differ only on programs the checker refuses, which is the standing arrangement and is already documented at the retention site. The differential harness should carry one program that the checker refuses and the machine runs, as the pinned statement of that difference.

### D14. Does a local debt weaken what the owner recovers?

**No.** A plain loan's release stays the exact payload; the debt is asserted against it. Forgetting is never forced, and a local mint whose only effect was to lose information would be a footgun with no use case.

### D15. Does the pin need `old`?

**No.** The debt's own binder `s` is the entry snapshot, pinned at mint exactly as `seedTelescopeV`'s σ and `entrySyms` do today. `old *v` remains the *return type's* way of naming the same thing, and the two agree by construction because they are the same σ. This is the precise relation the brief asks for: `Debt.entry` **is** `entrySyms`, generalized from "per borrow parameter" to "per loan", and `ArraySort`'s staged builders (`let Tl0 = *tl; let X0 = x;` — "the snapshots this builder was taking implicitly, named") are the *body-level* instance of the same pinning discipline, done by hand because a body cannot write `old` on a consumed binder. The milestone does not fix that (it is the "sixth filing for `old`-on-consumed-things"), but it uses the same idea one level down.

### D16. Is the trivial pin `= s` (identity) worth a surface abbreviation?

Read-only borrows will be common if §5 lands. `&ro τ` or `&mut ro τ` as sugar for `&mut (s : τ ~> τ = s)` costs one elaboration rule. **Recommend deferring** until the acceptance tests show how often it is written — the whole point of §5 is that it is not a new type former, and sugar that looks like one may re-teach the wrong thing.

---

## 10. Staging plan

Seven stages. The rule throughout: each stage builds green, and each stage's differential is enumerable on its own. Estimates are in agent-sessions (a session being roughly what one dispatched agent completes before a natural checkpoint), and they assume the incremental-write discipline (≤120-line writes, build per chunk).

| # | stage | content | est. |
| --- | --- | --- | --- |
| **0** | *probe* | Pin the twin probe on this base. Write the failing-today assertions in `BorrowRefoundGoals.lean` as `progRejects` with today's messages, so the milestone's differential is measured rather than remembered. | 0.5 |
| **1** | `Debt` table | Introduce `St.debts`; make `Obligation`, `Group.captured`, `Group.exitRelease` views over it; delete the originals. **No semantic change** — the corpus must be green with zero golden movement. This is the largest mechanical diff and the smallest risk. | 2 |
| **2** | shape half | `hasType`'s `borrowM`/`borrowT` case; `readC` reflects `borrowT`; the proof-fragment exclusion (§4.2) checked, not assumed; `piAgree`'s contract comparison; lift the pass-a-borrow-moded-function refusal (§7's promise, `suspensions.md:421`). | 2 |
| **3** | §19 + escape | Widen the move collapse; the `indexKindV` conjunct; the scope-pop escape rejection. Small, and it is what makes stage 5 safe. | 1 |
| **4** | mint sites | The `.seal` borrow branch (D7); debts stack with entailment (D5, D6); the local-mint assertion at demand (§3.1 step 3). Acceptance test (c) — the read-only law — should go green here if the issued pin lands with it. | 2 |
| **5** | the pin | `Debt.pin`; `projectDebt`; `endGroup`'s pinned release; `endIssued`'s pin assertion; the hole-filling audit and the M27 repeal; the issued-exit σ mint. **This is the milestone.** Acceptance tests (b) and (c) go green. | 3–4 |
| **6** | generality | Delete the M24 slice special case (D10); lift `retMixesBorrow` (D9); acceptance test (a), `split_at_mut` as an ordinary library function. | 2–3 |

**Total: 12.5–14.5 sessions**, with stages 1–3 low-risk and stage 5 carrying essentially all of it. Stage 6 is the cuttable tail.

Sequencing constraints that are not negotiable: 1 before everything (the table is the substrate); 3 before 6 (borrow-carrying data in signatures needs the move rules); 2 before 6 (a borrow in data needs a value judgment). Stage 5 needs only 1.

**The one thing to verify before committing to stage 5**, per the standing "verify viability before speculative refactors" discipline: that the `Nth` `S(k)` branch's conversion in §2.3 actually goes through definitionally on `SetNth`'s real corpus definition. That is a 30–60 minute probe — write the pin by hand into a scratch `Obligation.owed` and run the conversion — and it is worth doing before stage 1, not after stage 4. If it does not converge definitionally, the pin needs a cited bridging equation, which is a different and larger design (`dllbc-arrows.md` §6.2's "audit doing rewrite-by-Id along a proved bridge", filed and never built).

### Risks, ranked

1. **The pin's conversion is not definitional in general.** Mitigation: the probe above, before stage 1. Fallback: cited bridges, which is a separate milestone.
2. **`hasType` becomes store-relative and leaks into proofs.** Mitigation: §4.2's exclusion checked syntactically, with a negative test that a `borrowT` inside an `Id` is refused.
3. **Stage 1's mechanical diff breaks a golden silently.** Mitigation: stage 1 is defined by *zero* golden movement; any movement is a bug in the refactor, not a decision.
4. **Deleting the M24 slice special case breaks the array corpus.** Mitigation: it is stage 6, the cuttable tail, and the corpus is the gate.
5. **The `.seal` interning carve-out spreads.** Mitigation: D7's fallback (c).

---

## 11. Tests that move

These pin today's opacity and become "the needle moved" updates. None of them is wrong today; each states a fact the milestone changes deliberately.

| test | file:line | today | after |
| --- | --- | --- | --- |
| `throughCaller` | `Boundaries.lean:368-378` | `y` is a **fresh σ**; the write through the returned borrow is forgotten | with `through` written at the identity pin, `y` is the written `Cons 9 Nil`; the **unpinned** `through` must stay in the file as the control, since opacity remains the default |
| the `advance`/`through` note | `Boundaries.lean:355-366` | "signature-only checking cannot tell them apart, so constraining would be UNSOUND" | still true of *unpinned* signatures; the comment must gain the sentence that a pin makes the signatures differ, or it will read as refuted |
| the M28 τ retirement note | `Boundaries.lean:463-475` | "the kernel does not carry a case for a rule it does not have" | the kernel carries the rule now, *declared*; the note becomes the history of why it is declared and not inferred |
| `chooseCaller` | `Boundaries.lean:341-352` | `a`, `b` hold **distinct fresh σ's**; `z = 7` unprovable | unchanged — `choose` has no pin and should not get one; this is the permanent statement that opacity is the default |
| §5.3 wire | `Boundaries.lean:196-202` | fresh σ after `push` | unchanged |
| the executing counterpart | `Boundaries.lean:379-395` | the machine writes `Cons(9,Nil)` while the checker forgets | the gap **closes** for the pinned version and stays open for the unpinned one; this test becomes the pair that shows both |
| `Diff.lean:553-585` | the opaque-σ differential; "what is true: the owner recovers an opaque existential" | needs a pinned twin, or it will read as the only possibility |
| `Ledger.lean:354`, `:480`, `:486` | ledger rows recording `throughOpaque`, `qsSpc`'s deleted carrier, and "M23 body rejected, its exit being a fresh σ minted by `nth2`'s group" | the third row is the one this milestone *closes*; it should be updated with the pinned `nth2` rather than deleted |
| `ArraySort.lean:195`, `:737` | opacity as the enabler of the carve reset | **must stay green untouched.** This is the regression that matters: writing no pin must change nothing |
| `g2SiblingHole` (the `hm-probe-getmut` lane's file, wherever it lands) | **accepted** — a hole in a sibling leaf of an exempted parameter | **rejected**, by the hole-filling audit (§3.3.1). The only intended acceptance-to-rejection move in the milestone, and it should be pinned as `progOk` before stage 5 and flipped to `progRejects` by it |

The last two rows are the milestone's acceptance criteria as much as the new tests are: nothing that does not write a pin may change, and the one program that must change is a program that is wrong today.
---

## 12. The acceptance tests

Written as programs in `dllbc/Dllbc/Tests/BorrowRefoundGoals.lean`. The file **builds today**: every program is a `def`, every target assertion is commented out and marked, and what is asserted live is only what is true today (the refusals the milestone removes). Reading that file next to this one is the fastest way to see what the milestone is for.

### (a) `split_at_mut` as an ordinary library function

The SUGGESTIONS entry's own acceptance test.

```
fn SplitAtMut (v : &mut (s : List Nat ~> List Nat = Append (*(fst res)) (*(snd res))),
               i : Nat, p : Le i (Len *v))
  -> Σ (a : &mut (List Nat)) → &mut (List Nat)
```

**Measured, not assumed: the SHAPE already checks today.** Posed on an array — where the calculus has a real split, the M24 carve, and where a cons-list's prefix and suffix are not two places — a function returning a pair of borrows carved out of one array is accepted as written:

```
fn SplitAtMut (a : &mut (Array 3 Nat)) -> Σ (x : &mut (Array 1 Nat)) → &mut (Array 2 Nat) {
  let l = &m (*a)[Z ; 1];
  let r = &m (*a)[1 ; 2];
  Pair(l, r) }
```

and so is a caller that takes both halves, writes `Arr(9)` and `Arr(8,7)` through them, and reads the array back. The multi-issued group (`Nth2`, §6.1) and the carve compose with no adjustment. So "unwritable" was too strong, and the honest statement is narrower and worse: **what is missing is not the ability to write `split_at_mut`; it is the ability for its caller to learn anything from it, and the ability to pass its result on.** The caller above recovers one fresh σ at `Array 3 Nat`, related to neither write, while the executing machine produces `Arr(9,8,7)`.

Two witnesses, both measured, both honest named rejections rather than silent gaps:

1. the M27 containment, on `v` reaching *both* results — `"boundary: 'v' is consumed into the result, and §6.1 exempts such a borrow from the payload audit — so its non-trivial owed type … would be checked by nobody"`;
2. `Σ (x : &mut _) → &mut _` at a **parameter** position — `"readC (⇝): borrow type &mut (τ ↝ τ') is only valid at a telescope position"`. A `split_at_mut` whose result cannot be handed to the next function is not an ordinary library function, and this is the shape half in one line.

What it needs, in the order the staging delivers it: the shape half so the pair is passable (stage 2); the pin over **two** issued exits (stage 5); and the general walk replacing the M24 slice special case (stage 6).

### (b) The get_mut round-trip law

Stated over a list first, as the brief directs, because the container's own theory is then one `SetNth`/`Nth` pair rather than a hashmap's.

```
fn NthPin [i] (v : &mut (s : List Nat ~> SetNth i (*res) s),
               i : Nat, p : Le (S i) (Len *v)) -> &mut Nat
```

and the caller:

```
let x = Cons(1, Cons(2, Cons(3, Nil)));
let b = &m x;
let r = NthPin(b, 1, ());
*r := 9;
let y = x;          -- the group ends here
-- TARGET: y ≡ Cons(1, Cons(9, Cons(3, Nil)))  — in CHECKING mode
```

This is "whatever the user writes through a get_mut borrow is still there next time they get", and it is the precision the planned hashmap flagship is missing. Today the checker gives `y` a fresh σ and the executing machine gives it the right list — the pair `Boundaries.lean:373-395` already pins, from the other side.

The callee-side obligation is §2.3's hole-filling, and the `S(k)` branch is the one that exercises the recursive resolution through the group's own pin. That branch is the viability probe named in §10, and it has been **hand-checked against the corpus's real `StdChainRaw.Set`**, which recurses on the index first:

```
Set Z     v (Cons h t) ⇝ Cons v t              -- the Z branch's pin, definitionally
Set (S k) v (Cons h t) ⇝ Cons h (Set k v t)    -- the S(k) branch's, definitionally
```

Both legs converge without a lemma, which is the answer §10's probe is looking for. It should still be run against the machine rather than on paper before stage 1 commits.

### (c) The read-only borrow law

```
fn GetRO [i] (v : &mut (s : List Nat ~> List Nat = s), i : Nat, p : Le (S i) (Len *v))
  -> &mut (t : Nat ~> Nat = t)
```

The returned borrow's identity pin makes it read-only; the container's identity pin then holds *because* of it (§5). Two callers:

- reads through `r` via a match-mode reborrow, writes nothing, ends the group — **accepted**, and the checker knows `x` is unchanged;
- writes through `r` — **rejected**, at `endIssued`, with "the borrow's pin is violated".

The rejection is the more important of the two: it is what makes the identity pin a *contract* rather than a comment, and it is the negative test for the whole read-only story.

Note for the reviewer: `GetRO` above is *derivable* from `NthPin` — `SetNth i (Nth i s) s ⇝ s` — so if the container's own lemma is definitional, the read-only law is a consequence of the get_mut law rather than a second mechanism. Whether it reduces definitionally on the corpus's `SetNth` is a fact about the standard library, not the kernel, and the test file states it both ways.

---

## 13. What this design does not do

Recorded so the review is not surprised by absences.

- **It does not reinstate `&τ`.** §5 argues the read-only motivation is served without it; the *aliasing* motivation is untouched, and the 2026-08-13 cut stands.
- **It does not add lifetimes.** The escape rule (§7) is a reachability check on loans, not a region system, and it refuses the self-referential case rather than describing it.
- **It does not make a caller able to see through an opaque call.** Precision comes only from what the callee ascribed. §5 point 4 is untouched, and `choose` stays exactly as forgetful as it is.
- **It does not fix `old`-on-consumed-things.** `ArraySort`'s staged builders survive; D15 explains why the milestone brushes against that problem without solving it.
- **It does not touch the executing machine's semantics**, except that the escape rejection makes one of its behaviours (retention) unreachable from admitted programs.
- **It does not merge `fsig` into `sctx`** (D8), and it does not do anything about the recursor-spine milestone queued alongside it.

---

## Addendum (2026-08-17, after the design landed): the sibling-hole gap closed standalone, and stage 5 has a measured prototype

The `audit-exemption-fix` lane (branch of the same name) closed §3.3.1's sibling-hole gap WITHOUT the debt machinery: the `reachesLoan` branch of `auditObligation` (Machine.lean:3485-3487) now runs a residue audit — hole-fill the issued markers, then `hasType` the payload whole. The divergence pair flips (needle "left ⊥ in a leaf it does NOT return"), the whole hm-probe-getmut corpus replays with exactly those two flips and nothing else, full suite green from scratch. Verdict from that lane: mergeable standalone — the gap was a bug in the rule's statement (the exemption keyed per-parameter while `reachesLoan` was already answering per-loan), not a missing capability. The design's "one intended acceptance-to-rejection move" therefore lands ahead of the milestone, and stage 5 inherits a measured prototype of hole-filling rather than a paper mechanism.

Four measured findings for stage 5, recorded in full in that branch's `Tests/AuditExemption.lean` module docstring: (1) fill with the issued borrow's ACTUAL payload where available, not a minted σ — minting renumbers the corpus's σ names and steals diagnoses from the issued-borrow checks; (2) any minting inside an audit must be sandboxed against a saved state restored on exit, with the residue collapse kept outside; (3) the fill must recursively descend THROUGH in-flight markers, because a live unreturned sibling borrow inside a returned place is legitimate — the orInsert family breaks under a guard against it; (4) "one σ per issued loan" misses captured-loan markers from inner open groups — the group table's recorded owed type is the only source there, and a fresh σ at it is what the opaque release would produce anyway. Two further observations: the write rule does not type-check (`*e := True` into a Nat cell is caught only at the exit audit, so the audit's type half is load-bearing rather than belt-and-braces — §2.3's table should say so), and the fill is honest only at trivial owed types (`ob.trivialOwed` is guaranteed at that point today); at a relational owed type it would be checking a minted σ against the type it was minted at, which is exactly where the pin machinery becomes necessary rather than convenient.
