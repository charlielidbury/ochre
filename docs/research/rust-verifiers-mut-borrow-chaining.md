# How Rust verifiers relate a returned &mut's write to the next read

Research survey, 2026-08-18, by a web-research lane of the hashmap-flagship session. The question: how does each major Rust verification tool let a CALLER prove `*get_mut(k) = 42; …; assert(*get_mut(k) == 42)` — relating a returned mutable borrow's final value to the referent's subsequent state. Directly informs DLLBC's pin design (`12-design-borrow-refounding.md`); the mechanism-independent principle (VerusBelt) — "the best time to relate a mutable reference to its borrowed-from location is at the one point where they are together: at borrow time" — is `14-packed-borrows.md`'s who-knows-what argument, independently derived.

## Short answer

Six of seven tools have a mechanism, and five are the same mechanism under different names: represent `&mut T` as a pair (current value, eventual value), fix the second component when the borrow dies, let the caller's write constrain it. Creusot calls it a **prophecy** (`^x`), Verus **`final(x)`**, RefinedRust a **borrow name** (`γ`), Thrust `◦x`, Aeneas turns the same information inside-out into a **backward function**, Prusti defers it to a **pledge** (a magic wand). Flux is the odd one out and genuinely cannot do this. Kani doesn't need a mechanism and pays in non-modularity.

**Headline update: Verus now does this.** "Verus cannot return `&mut`" was true through 2025 and false as of `new-mut-ref: release` (#2393), 2026-05-01. Even the VerusBelt paper (PLDI 2026) still describes the restriction as current — written before the feature shipped.

| Tool | Verified fn returns `&mut`? | Mechanism | "Value at expiry" | Caller writes |
|---|---|---|---|---|
| Creusot | Yes | Prophecy | `^r` | nothing |
| Verus (≥ 2026-05) | Yes | Prophecy | `*final(r)` | nothing |
| Aeneas | Yes | Backward function | apply `back v'` | the generated backward application |
| RefinedRust | Yes | Borrow name + Iris resolution | `*γ` / `Res γ v` | nothing |
| Prusti | Yes, with a pledge | Pledge (magic wand) | `before_expiry(*result)` | nothing |
| Flux | Returns `&mut`, no value link | — (`ensures` is argument-only) | none | cannot prove it |
| Kani | N/A | Symbolic execution of real memory | none | nothing; no modular contract exists |

## Creusot — prophecies

A mutable borrow contains the current value and the prophecy (last value written); dropping the borrow adds the assumption `current == prophecy` ("resolving"). NOTE: Creusot's extern spec for the real `std::collections::HashMap` has NO `get`/`insert`/`get_mut` — the story lives on the ghost `FMap`, whose checked doctest is the scenario verbatim, with the load-bearing ensures clause `(^self)[*key] == ^r` (the map's final value at the key IS the reference's final value). The real-container spelling is on slices (`get_mut` with `ix.has_value((^self)@, ^r)` and `resolve_elswhere`). Caller writes nothing. Cost: the naive pair model is UNSOUND — Creusot needs a borrow *id* plus "final reborrows"; their guide derives `**evil == !**evil` without it.

## Verus — prophecies, as of May 2026

Guide (`mutable-references.md`, "Returning mutable borrows"):

```rust
fn get_mut_fst<A, B>(pair: &mut (A, B)) -> (ret: &mut A)
    ensures *ret == old(pair).0,
            *final(pair) == (*final(ret), old(pair).1),
{ &mut pair.0 }
```

Resolution axiom exposed directly: `has_resolved(x) ==> *x == *final(x)`; `after_borrow(x)` reads a local while borrowed (needed in loop invariants). vstd has no `HashMap::get_mut` but the whole **Entry API** is specced prophetically (`std_specs/hash.rs`): `OccupiedEntry::get_mut` ensures `final(entry).value() == *final(value)`, tied to the map by `entry`'s ensures (`final(m)@ == old(m)@.insert(key, value)` when the entry resolves to `Some value`). The caller (examples/entry_api.rs, real std HashMap) writes only the assert: `*value_ref = 40; assert(m@ =~= map![0 => 20, 1 => 40])`. Theory: VerusBelt (PLDI 2026) adopts RustHornBelt's `⌊&mut T⌋ = ⌊T⌋ × ⌊T⌋`, and reports a "time travel paradox" (a prophecy resolved to a value depending on itself, `ρ = ρ + 1`) with Verus's ghost types, fixed by stratifying prophecy-dependent from prophecy-independent values; Creusot's developers independently hit the same paradox.

## Aeneas — backward functions

Ochre's mirror. Rust's ordinary `get_mut(&mut self, key) -> Option<&mut T>` translates to a value-and-function pair:

```lean
def HashMap.get_mut {T} (self : HashMap T) (key : Usize) :
  Result ((Option T) × (Option T → HashMap T))
```

The caller's `*r = 42` becomes an application of the second component. The proved spec (`Hashmap/Properties.lean`, `get_mut_spec`): `hm.lookup key = opt_v`; `back none = hm` on the none path; and ∀ v v', `(back (some v')).lookup key = some v'` with the frame for other keys. Instantiate `v' := 42` and chain. The borrow's expiry is a SYNTACTIC event in the translation — no prophecy variable exists. Caveats: the ICFP'22 `test1` containing the literal chained scenario is commented out in current `tests/src/hashmap.rs` (the theorem is live; the executable test is not); the paper's analogy is lenses ("except we propagate the output back to possibly-many inputs").

## Prusti — pledges

`#[after_expiry(self.lookup(index) == before_expiry(*result) && …frame…)]` on `index_mut`, translated as a conjunct on the RHS of the Viper magic wand representing post-expiry state (OOPSLA'19). Caller writes nothing. Two limits that bite this exact scenario: no mutable references inside `Option` (so literal `get_mut -> Option<&mut V>` is unstatable — RefinedRust PLDI'24 says so explicitly; Prusti's own examples use bare `&mut` behind `!is_empty()`), and pledges "cannot accommodate the splitting of borrows" (Thrust PLDI'25).

## Flux — genuinely cannot

`&strg`/`ensures` (updated refinement of a strong reference) is ARGUMENT-position only; no return-position analogue. `index_mut` returns `&mut T` with only `T`'s invariant; PLDI'23 is explicit users "must respect the invariants in T when mutating" — the written value is not in the model. Thrust confirms the limitation is structural. Flux proves `*r2 == 42` only if 42 is baked into the element type.

## RefinedRust — borrow names

`(42, γ) @ &mut int32` — current value plus borrow name, in Iris. Figure 3 of PLDI'24 is literally the scenario on Vec: `get_mut` returns `Some (xs !!! i, γi)` and ensures `Res γ (<[i := *γi]> xs)` — the vector's model holds the PLACEHOLDER `*γi` over a borrowed-ness-enriched value domain (`bor τ ∋ g ::= #x | *γ`). When the lifetime ends, `Res γi 42` arrives and the model updates to `[#100; #42; #300]`. The only tool in the table that also verifies get_mut's IMPLEMENTATION down through raw pointers.

## Kani — the contrast

No annotations: the real HashMap body compiles to CBMC GOTO; `r1`/`r2` are pointers to the same address; the solver sees it. The price is modularity: contracts are ⟨Pre, Post, Mod⟩ with Post ranging over the state at RETURN — no construct for post-expiry state, so `stub_verified` on a get_mut contract loses the fact entirely. (UNVERIFIED as a quoted doc claim — inferred from RFC 0009's contract shape.) Practical: std's HashMap hits hashbrown SIMD intrinsics Kani doesn't support by default.

## Synthesis

Prophecies, pledges, backward functions, and borrow names are interconvertible presentations of one idea: a mutable borrow's meaning is a relation between its initial and final values, discharged at expiry. Best single connective citation: Denis et al., "Using a Prophecy-Based Encoding of Rust Borrows in a Realistic Verification Tool" (2025, hal-05244847) — makes the Aeneas, Prusti, RefinedRust, and (presciently) Verus connections in one place, plus SPARK/Ada as a fourth independent rediscovery. The one genuine dissent is Aeneas' own framing (backward functions "obviate the need for prophecy variables"): a prophecy is a VALUE constrained later; a backward function is a FUNCTION applied later — the prophecy is the eta-expanded backward argument, the backward function the defunctionalized prophecy constraint; same information, opposite dependency direction, choose by whether your logic is happy with not-yet-determined values (SMT: yes with a soundness proof; proof assistants: prefer not).

**Design inputs for DLLBC's pin (12-):** (1) the naive current×final pair is unsound without borrow identity — Creusot's `**evil == !**evil` derivation and VerusBelt's stratification are the two published repairs; any pin implementation must confront the same self-reference; (2) DLLBC's spelling is closest to Aeneas' (a function-of-the-final-payload, syntactic expiry — no prophecy variables in the logic), which is the proof-assistant-friendly end of the design space; (3) Thrust (PLDI'25) is the "prophecies in a refinement type system" design point — the closest published system to what a refinement-typed Ochre would need.

## Sources

Creusot repo (`creusot-std` hash_map/fmap/slice specs; guide `mutable_borrows.md`); Creusot HAL papers (hal-03737878, hal-05244847); Prusti user guide (pledges) + Astrauskas et al. OOPSLA'19; Aeneas ICFP'22 + repo (`tests/lean/Hashmap/{Funs,Properties}.lean`, `tests/src/hashmap.rs`); Verus repo (guide `mutable-references.md`, `vstd/std_specs/hash.rs`, `examples/entry_api.rs`, `rust_verify_test/tests/mut_refs_libs.rs`, discussion #35, PR #2393); VerusBelt PLDI'26; RustHornBelt PLDI'22; Flux PLDI'23 + book + repo; RefinedRust PLDI'24; Thrust PLDI'25; Kani ASE'26 + RFC 0009. Local: `competitors/aeneas-hashmap/current/hashmap.rs` (test1 commented at lines 314–359).
