# CPS, Continuations, and Control Flow Effects in Ochre

This document proposes how Ochre could support control flow effects
(exceptions, async/await, generators, nondeterminism) via delimited
continuations, and how the ownership system determines compilation
strategy. This is a design exploration, not a commitment.

---

## 1. Motivation: the missing half of effects

Programming has two fundamental side effects: **mutation** and **control
flow**. Ochre's ownership model (inherited from Rust) addresses mutation.
This document addresses control flow.

Rust handles control flow effects through special-cased mechanisms: `?`
for errors, `async/await` for concurrency, iterators for generation. Each
has its own syntax, its own compilation strategy, and its own interaction
with the type system. They are zero-cost, but they are ad hoc.

Ochre could instead derive all of these from a single mechanism:
**delimited continuations** classified by the ownership system. The
ownership class (FnOnce/Fn/FnMut) of the captured continuation
determines both the expressiveness and the compilation strategy, with
zero-cost output in all cases.

---

## 2. Background: Och already has half of CPS

Church-encoded data in Och is already continuation-passing. A value of
type `Sigma Nat (lam n. Array n T)` — an existential pair — is a
function that takes a continuation and feeds it the witness:

```
v ResultType (lam n : Nat. lam arr : Array n T. <body>)
```

The `?` sugar proposed in `add-cps.md` makes this ergonomic:

```
n   = v?;
arr = id?;
<body>
```

This covers **structured elimination** of Church-encoded data. What it
does NOT cover is **non-local control flow**: jumping out of a
computation (exceptions), suspending it (async), or forking it
(nondeterminism). For that, continuations must be first-class.

---

## 3. Proposed primitives: shift and reset

Add two term formers to the calculus:

```
e ::= ...
    | reset e               -- delimit continuation scope
    | shift (k : A). e      -- capture continuation up to nearest reset
```

`reset e` marks a boundary. `shift (k : A). e` captures the continuation
from here up to the nearest enclosing `reset`, binds it to `k`, and
evaluates `e` (the handler body) with `k` in scope.

### Semantics

Concrete evaluation:
```
reset E[shift (k : A). e]  -->  e[k := lam x. reset E[x]]
```
where `E` is the evaluation context up to the nearest enclosing `reset`.

Abstract evaluation: the abstract evaluator uses the annotation `A` on
the shift to determine the continuation's type, analogous to how `mu`
uses its annotation to avoid divergence. The handler body `e` is checked
with `k : A` in scope.

### Why not call/cc?

Undelimited continuations (call/cc) are unsound in most dependent type
systems. They correspond to classical logic (Curry-Howard), which is
inconsistent with the inductive reasoning Ochre needs. Delimited
continuations (shift/reset) are well-behaved — the captured continuation
is a regular function, not an escape hatch from the type system.

---

## 4. Ownership classifies continuations

The key insight: **the ownership system determines what kind of
continuation you have**, which determines how it can be used and how it
compiles. The programmer doesn't choose — the compiler infers it from
what the continuation captures.

| Captures                | Closure trait | Handler can call k... | Use case              |
|-------------------------|---------------|----------------------|-----------------------|
| By move                 | FnOnce        | At most once         | Exceptions, async     |
| By shared ref (`&`)     | Fn            | Any number of times  | Nondeterminism        |
| By mutable ref (`&mut`) | FnMut         | Sequentially, many   | Generators, iteration |

The continuation "captures" everything that is live at the shift point
and needed by the code after it. The ownership of those captures
determines the trait.

### Examples

**FnOnce** — continuation captures a moved value:
```
fn process(data: OwnedBuffer) -> Result {
    reset {
        parsed = parse(data)?;    // data moved into continuation
        transform(parsed)
    }
}
// k captures `data` by move -> FnOnce
// handler can call k once (consuming data) or not at all (dropping it)
```

**Fn** — continuation captures only shared refs or copyable values:
```
fn solve(config: &Config) -> List<Solution> {
    reset {
        x = choose(config.options)?;   // config borrowed, x is Copy
        y = choose(config.options)?;
        validate(x, y)
    }
}
// k captures `config` by & and `x` by Copy -> Fn
// handler can call k multiple times (each call independent)
```

**FnMut** — continuation captures a mutable ref:
```
fn accumulate(total: &mut Nat) -> Nat {
    reset {
        v = yield(())?;     // total captured by &mut
        *total += v;
        *total
    }
}
// k captures `total` by &mut -> FnMut
// handler can call k sequentially (each call sees prior mutations)
```

---

## 5. Compilation strategies

Each ownership class compiles to a different zero-cost pattern. No
runtime support, no heap allocation (unless the handler explicitly stores
the continuation), no stack copying.

### 5.1. FnOnce: direct returns / state machines

**When k is never called (exceptions / early return):**

Source:
```
fn process(input: Data) -> Result {
    reset {
        a = step1(input)?;
        b = step2(a)?;
        step3(b)
    } handle throw(e, k) => Error(e)
}
```

Compiled:
```
fn process(input: Data) -> Result {
    let a = match step1(input) {
        Ok(v)  => v,
        Err(e) => return Error(e),   // jump, no closure
    };
    let b = match step2(a) {
        Ok(v)  => v,
        Err(e) => return Error(e),
    };
    step3(b)
}
```

Stack at throw point:
```
| step2       |  <-- returns Err(e)
| process     |  <-- checks return, hits Err, returns Error(e)
| main        |
```

No unwinding, no longjmp. The continuation is a jump target — the
program counter after the match. The "throw" is a return value that
propagates via normal returns. Identical to Rust's `?` on `Result`.

**When k is called once later (async/await):**

Source:
```
async fn fetch_both(a: Url, b: Url) -> (Data, Data) {
    reset {
        x = http_get(a)?;
        y = http_get(b)?;
        (x, y)
    } handle suspend(req, k) => enqueue(req, k)
}
```

Compiled to a state machine:
```
enum FetchBoth {
    Start { a: Url, b: Url },
    GotFirst { b: Url, x: Data },
}

impl Future for FetchBoth {
    fn resume(self, input: Data) -> Poll<(Data, Data)> {
        match self {
            Start { a, b } => {
                enqueue(http_get(a));
                Poll::Pending(GotFirst { b })
            }
            GotFirst { b, x } => {
                enqueue(http_get(b));
                Poll::Ready((x, input))
            }
        }
    }
}
```

The continuation's live variables are saved in the enum variant. The
stack unwinds to the executor via normal returns. On resume, the executor
calls `resume()` as a regular function. Identical to Rust's async
transform.

### 5.2. Fn: defunctionalized closures

Source:
```
fn solve() -> List<(Nat, Nat)> {
    reset {
        x = choose([1, 2, 3])?;
        y = choose([10, 20])?;
        (x, y)
    } handle choose(opts, k) => flatmap(opts, k)
}
```

Compiled via CPS defunctionalization:
```
enum Cont {
    AfterFirstChoose,
    AfterSecondChoose { x: Nat },
}

fn apply(k: &Cont, arg: Nat) -> List<(Nat, Nat)> {
    match k {
        AfterFirstChoose => {
            let x = arg;
            let k2 = Cont::AfterSecondChoose { x };
            flatmap(&[10, 20], |y| apply(&k2, y))
        }
        AfterSecondChoose { x } => {
            vec![(*x, arg)]
        }
    }
}

fn solve() -> List<(Nat, Nat)> {
    flatmap(&[1, 2, 3], |x| apply(&Cont::AfterFirstChoose, x))
}
```

The continuation is an enum on the stack, passed by `&` (shared ref).
Each "call to k" is a regular function call that pushes a frame, does
work, and returns. The stack grows and shrinks normally — no copying, no
saving, no switching.

When the handler is opaque (ascribed), the continuation degrades to
`&dyn Fn(Nat) -> List<(Nat, Nat)>` — a vtable pointer, one indirect
call per invocation. Transparent handler = static dispatch; ascribed
handler = dynamic dispatch. Same as everything else in Ochre.

### 5.3. FnMut: loops

Source:
```
fn sum_yielded() -> Nat {
    let mut total = 0;
    reset {
        yield(1)?;
        yield(2)?;
        yield(3)?;
        total
    } handle yield(v, k) => { total += v; k(()) }
}
```

Compiled to a flat loop:
```
fn sum_yielded() -> Nat {
    let mut total: Nat = 0;
    let mut phase = 0;
    loop {
        match phase {
            0 => { total += 1; phase = 1; }
            1 => { total += 2; phase = 2; }
            2 => { total += 3; phase = 3; }
            3 => return total,
        }
    }
}
```

One stack frame, never grows. The "continuation call" is `phase += 1;
continue`. Mutable captures are local variables in the single frame.
Identical to how Rust compiles `for` loops over iterators.

---

## 6. Interaction with abstract evaluation

### 6.1. Soundness

Soundness requires: if the abstract evaluator accepts the handler, the
concrete evaluator doesn't violate the contract.

**FnOnce:** k is called at most once concretely. Abstract eval models one
call with an abstract argument. The single concrete call's result refines
the abstract result. Sound by standard Och reasoning.

**Fn:** k is called multiple times concretely, each with a specific
value. Abstract eval models k as a function `A -> B`. Each concrete call
`k(v)` where `v : A` produces a result in `B`, by monotonicity. The
calls are independent (no shared mutable state), so there is no
interaction between them. Sound.

**FnMut:** k is called multiple times with mutable state evolving between
calls. Abstract eval must track the state evolution via strong mutation
(Ochre's standard mechanism). After `r1 = k(x)`, the types of mutable
captures are refined; the second call `k(y)` is type-checked against the
refined types. Sound, but requires Ochre's mutation tracking to work
across continuation calls.

### 6.2. Monotonicity

Widening the environment must widen the handler's result. The handler
body is abstractly evaluated like any other expression. The continuation
`k` is a function in the environment; widening the captured variables
widens `k`'s behavior. This should be monotone as long as function
application is monotone — which is a core Och property.

### 6.3. Abstract eval of shift

The abstract evaluator must handle `shift (k : A). e`:

1. Determine the continuation's type from `A` and the context
2. Check the handler body `e` with `k : A` in scope
3. Return the handler body's abstract result

This is analogous to `mu (f : A). body` — the annotation guides abstract
evaluation to avoid divergence. The pattern "annotation on a binder
guides the abstract evaluator" is already established.

---

## 7. Interaction with type erasure

Shift/reset interact cleanly with Ochre's erasure model:

- `reset e`: at runtime, the reset marker is a no-op (or a setjmp-like
  save point, depending on compilation strategy). At compile time, it
  delimits the continuation scope.

- `shift (k : A). e`: at runtime, captures the continuation. The
  annotation `A` is erased — it was only needed for abstract evaluation.

- `(handler : HandlerType)`: ascription on the handler erases the
  handler body at compile time, producing an opaque handler type. At
  runtime, the handler body executes normally.

No new erasure mechanism needed. The annotation on shift is erased like
lambda domains. The handler is erased or preserved based on ascription,
like everything else.

---

## 8. Decision points

### D1: Primitives vs sugar

**Option A: shift/reset as primitives.** Add new term formers. Requires
new typing rules, new cases in the soundness/monotonicity proofs.

**Option B: Algebraic effect declarations.** Higher-level surface syntax
(effect/handler declarations) that desugar to shift/reset. More
ergonomic, but shift/reset must still exist in the core.

**Option C: Monadic encoding.** No new primitives. Encode effects as
`A -> (B -> R) -> R`. Already possible in Och. The `?` sugar from
`add-cps.md` makes it tolerable.

Trade-off: A is minimal and forces the theory to be worked out. B is
more user-friendly but adds surface complexity. C requires no theory
work but produces genuinely CPS code at runtime (closure allocation per
effect operation) unless the compiler is very clever about optimization.

**Recommendation:** Start with C (monadic encoding + `?` sugar) to
validate the design, then move to A if runtime performance matters. B
is a surface-level concern that can be added later without changing the
core.

### D2: Multishot continuations

**Option A: FnOnce only.** Continuations are always linear. Simpler
theory, simpler compilation (no need for Fn/FnMut cases). Covers
exceptions and async. Does NOT cover nondeterminism or backtracking.

**Option B: FnOnce + Fn.** Allow multishot for pure continuations.
Covers nondeterminism. Requires the compiler to handle the Fn
compilation case (defunctionalization). FnMut excluded — mutable
captures force FnOnce.

**Option C: FnOnce + Fn + FnMut.** Full generality. FnMut continuations
allow stateful iteration patterns. Requires abstract evaluation to track
state evolution across continuation calls.

Trade-off: each step adds expressiveness but also proof obligations.
FnOnce is nearly trivial to prove sound. Fn requires showing that
independent calls don't interfere. FnMut requires integration with
Ochre's strong mutation. The ownership system infers the classification
automatically, so there is no user-facing complexity cost — the question
is purely about what the compiler and the theory must support.

**Recommendation:** Design for C (full generality) from the start, but
implement incrementally: FnOnce first, then Fn, then FnMut. The
ownership system is load-bearing regardless — get it right once.

### D3: Function coloring

When an effect operation is several frames deep from the handler, every
intermediate function must declare the effect in its signature and
propagate it.

**Option A: Explicit coloring (Rust-style).** Functions that can perform
an effect must declare it. Callers must propagate. Zero runtime cost.
This is what Rust does with `Result + ?` and `async`.

**Option B: Implicit propagation (exception-style).** Any function can
throw; no signature change needed. Requires either stack unwinding
(runtime cost on throw) or whole-program CPS transform (compile-time
cost, code bloat).

**Option C: Effect polymorphism.** Functions are implicitly polymorphic
over effects they don't handle. Like A but the boilerplate is inferred.
Requires effect inference.

Trade-off: A is simple and zero-cost but verbose. B breaks Ochre's
"types tell you everything" philosophy and complicates compilation. C
is the ideal but requires sophisticated inference.

**Recommendation:** A (explicit) for the core calculus. C (inferred) as
sugar layered on top, similar to how implicit arguments would be sugar
over explicit ones. This mirrors the general Ochre philosophy:
everything is explicit in the core, ergonomics are added via
elaboration.

### D4: Where to introduce this

**Option A: Add to Och.** Test the theory in the minimal calculus before
scaling up. Requires adding shift/reset (or monadic encoding) to Och and
proving soundness.

**Option B: Skip to Ochr/Ochre.** Control flow effects only become
interesting with ownership (which determines the continuation's closure
trait). Adding them to pure Och gives you only the Fn case — multishot
pure continuations — which is the least practically useful case.

**Option C: Add to Och without ownership, but design for it.** Use Och
to validate the soundness of shift/reset in a pure setting. Defer the
FnOnce/FnMut compilation strategies to Ochr.

Trade-off: The core soundness question (does shift/reset preserve
concrete-refines-abstract?) can be tested in Och. The compilation
question (does ownership classification give zero-cost?) can only be
tested in Ochr/Ochre. Doing both at once risks conflating issues.

**Recommendation:** C. Add monadic encoding + `?` sugar to Och (already
planned in `add-cps.md`), which validates the theory. Defer shift/reset
as primitives to Ochr, where ownership makes the compilation story
testable. The monadic encoding in Och will naturally evolve into
primitive shift/reset in Ochr if the theory holds up.

---

## 9. Relationship to existing Och work

This proposal does not require changes to the current Och formalization.
The monadic encoding path (D1 option C) uses only existing Och features:
lambdas, application, and the `?` sugar. The `add-cps.md` document
already describes this sugar.

What this document adds is:

1. The observation that ownership classifies continuations (section 4)
2. Concrete compilation strategies for each class (section 5)
3. Analysis of how each class interacts with abstract evaluation (section 6)
4. A staged plan for introduction (section 8)

The current Och work on soundness and monotonicity is a prerequisite.
If those properties fail for the pure core, adding continuations will
not help.

---

## 10. Open questions

### Q1: Answer type polymorphism

Shift/reset with a fixed answer type (the return type of the reset
block) is well-understood. Answer-type polymorphism (the handler can
change the return type) is more expressive but harder to type. Which
does Ochre need?

For exceptions (FnOnce, k not called), the answer type doesn't matter.
For nondeterminism (Fn), the handler maps `A -> List A`, changing the
answer type. For generators (FnMut), the handler maps `A -> Iterator A`.
Full generality likely requires answer-type polymorphism.

### Q2: Effect subtyping

If function `f` has effect `{Throw}` and function `g` has effect
`{Throw, Async}`, is `f` a subtype of `g`? (A function with fewer
effects is usable where more effects are expected.) This interacts with
Och's subtyping machinery and needs careful analysis.

### Q3: Named effects vs structural effects

Should effects be identified by name (like Koka's named handlers) or
by structure (like the monadic encoding, where the "effect" is just the
continuation's type signature)? Named effects allow multiple handlers
for the same type signature; structural effects are simpler but can
cause ambiguity.

### Q4: Deep vs shallow handlers

A deep handler re-wraps the continuation so that recursive effect
operations within the continuation are handled by the same handler. A
shallow handler only handles the first operation; the continuation must
be re-handled explicitly. Deep handlers are more convenient; shallow
handlers are simpler and more compositional.

### Q5: Interaction with mu

Mu (unified self-reference) provides recursion. A recursive function
under a handler could perform effects at each recursive step. The
abstract evaluator already avoids diverging on mu by using the
annotation. Does the same strategy work when mu interacts with
shift/reset? Specifically: if a mu body contains a shift, what is the
annotation's role?
