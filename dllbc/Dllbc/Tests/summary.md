# Test suite summary

One sentence per file stating what its assertions cover (language feature / interpreter machinery wise).

| File | Assertions cover |
|---|---|
| **KernelFloor** | The pure kernel: β/ι reduction, stuck neutrals, conversion, large elimination, value typing, canonical readback, the Id/`J`/`K` fording library (no-confusion, injectivity, UIP), and the surface→kernel elaboration round-trip. |
| **Traces** | The executing borrow machine's basic walks: moves, borrow/write-through/end, drop, take-and-refill, reborrow, match in owned/borrow mode, symbolic-scrutinee refinement, and frame/scope cleanup at arm and function exit. |
| **Boundaries** | The function-call boundary: bounds-proof arguments, the call rule, loan groups (borrows entangled by a call), dependent return-type instantiation, recursive cursors, and reborrow at a call site. |
| **Diff** | The checker⇒/executor⇝ differential itself: enumerated function bodies run through both machines with the `instanceOf` simulation relation, asserting agreement counts per telescope. |
| **Programs** | Comptime vs runtime binder modes: capital `let`, the comptime-argument rule, fuel threading, erased data, borrow-lie containment (`hasBorrowT`), and the quicksort signature reading correctly under modes. |
| **Functions** | The `fn` statement: the ⇝-seal, recursors as function bodies, runtime λ values, application of value callees, transparent-vs-sealed typing, and `Qed`. |
| **Direct** | Direct proving on lists: Σ projections as specs, dependent Σ call results, recursion-as-self-ensures, `split_off`/`append_back`, relational swap, `insert_at`, branch equations, and the partition layer under list quicksort. |
| **Arrays** | Array machinery: the formers (`arrCat`, `aget`, `acons`/`arrRec`, segments), concrete and symbolic carving of `&mut Array`, disjointness demands, `refineSym`, and carve rejection cases. |
| **ArraySort** | The array flagship: in-place quicksort over `Array n Nat` proved `Sorted ∧ Perm`, with lying-twin controls and the executing differential (it really sorts, in place). |
| **ArrCatIota** | The `atake`/`adrop` projections and their ι-rules, which let a symbolic-index carve be named and discharged without a walk. |
| **SetHmProbe** | Whether a pin discharges at a symbolic carve index (no, in both spellings) and that the index-recursing walk architecture works instead. |
| **OpaqueFill** | The exit-audit's opaque fill for escaping borrows: lent places re-typed as fresh σ at the owed type, with the four unsound-acceptance programs now rejected. |
| **AuditExemption** | The exit-audit's exemption granularity: a callee leaving a hole (⊥) in a lent parameter, caught per-sub-place rather than per-parameter (M34's one-rule `auditObligation`). |
| **AuditFold** | The exit audit re-typing a dependent Σ pack whose array component is segmented (carved but unchanged), via `subsKnowledge` taking the ⇝ fold bridge. |
| **SigmaCopy** | The Σ-pack Copy rule: a pack copies iff every component is copyable or erased, positive and negative cases plus the checker/executor agreement on it. |
| **Universe** | The universe rule: formation of all type formers at `Type`, `Type : Type`, refusal of binder-mode markers as types, generic functions (`Poly(Nat, 5)`), neutral types, and types having no ⇒/runtime reading. |
| **EagerRec** | Normalizer performance: `whnfN` forcing a recursor's recursive result eagerly (only when the arm uses it), with measured linear-not-exponential scaling on `Mod`. |
| **HashMap** | The hashmap flagship: packed invariant, bucket/slot spec functions, crossing lemmas, insert/get/remove/resize checked against specs, the single-allocation rotation resize, plus lying-twin controls. |
| **HashMapDiff** | The hashmap's executing layer: runtime differential against a trusted Lean-side model (split out so it doesn't re-run the expensive concrete executions). |
| **HashMapPin** | The hashmap's borrow-returning ops (`GetMut`/`GetMutOrInsert`) with pinned one-slot contracts, and the two-call round-trip law at hashmap scale. |
| **Fence** | That `prog defer_check` suppresses only elaboration-time checking — same `Term`, still rejects/accepts under the checker — guarding all 275 fenced sites. |
| **AmbiguousMiddle** | That terms legal under both arrows genuinely diverge between `readC` (accepts) and `checkProgram` (rejects), backing docs/05's "the consumer decides" claim. |
| **Sugar** | Surface sugar goldens: match-on-expression, singleton-constructor `let`, nested constructor patterns — asserted as `Term`-equal to their desugarings, with the plain-variable match path untouched. |
| **Ledger** | Historical bookkeeping: what each claim of the retired `back` mechanism became — mostly narrative with assertions pinning the dispositions. |
| **BorrowRefoundGoals** | A target file, not a suite: the borrow re-founding's three goal families (`split_at_mut`, get_mut round-trip, read-only law) with live TODAY assertions and commented-off TARGETs. |
| **ElabSpans** | That checker rejections surface as Lean diagnostics at the offending syntax span, pinned with `#guard_msgs`. |
| **HoverSpans** | Hover answers at binder granularity (docs/16) — pinned as comments, checkable only via the language server, not by `lake build`. |
| **PointSpans** | Point-granularity hovers (docs/17, now the default) — same non-build-assertable comment discipline. |
| **ShowSpans** | The `show x` statement printing the hover answer as a diagnostic, making it `#guard_msgs`-assertable by the build. |
| **PointCost** | (Not in build) A timing harness comparing checker cost with point-delta recording on vs off. |
| **PinProbe** | (Not in build) Stage-0 viability probe: whether the pin's key conversions are definitional on the real corpus definitions. |
| **ProbeRotate** | (Not in build) Viability probes for the rotation-based resize: the mem::replace chain, carve-inside-arm, branch equations across calls. |
| **ProbeComptimeHover** | (Untracked scratch) Hover/`show` probes on comptime binders. |
| **Playground** | (Untracked scratch) Ad-hoc dev programs: snapshots, data-motive recursors, `fn` sugar vs hand-written recursor. |
| **Simple** | (Untracked scratch) One trivial two-argument function program, no assertions. |
