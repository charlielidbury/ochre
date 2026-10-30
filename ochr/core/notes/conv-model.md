# Conversion, modelled

Branch `conv-model`, off main `124216d0`. The ninth model note, after `depfields-model.md`, `split-model.md`, `id-model.md`, `rec-model.md`, `erasure-model.md`, `closeoff-model.md`, `frame-model.md` and `inductive-model.md`. Scope: definitional equality as the checker decides it (`conv`, `convList`, `convT`, `convPi`, `convFn`/`convFnRun`, `mkEqM`, `unitTop`, the `convStack`), and the rules that consume it ([J], [T-J-stuck], [T-Rewrite], argument and annotation checks).

**Result: no hole.** Every conversion rule is an equality of meanings in the set model (A.6), every derived condition is enforced, and the probes behave as the model predicts. They are registered as block `ConvModel` in `Examples/Functions.lean` (35 declarations, total 1,787 → 1,822), with every rejection's reason asserted.

## 1. The model

A value's meaning is its denotation in A.6: data as tagged trees, a proposition as `{•}` or `∅`, a type as a set, a function value as a set-theoretic function from the contents of its borrowed places (and its other arguments) to its result and their final contents, plus, for a returned borrow `&T`, a backward function from the value finally written through it to those contents (Aeneas). **Conversion is sound exactly when convertible values have the same meaning**: then `J` along a convertible pair returns `t : P(a)` at `P(b)` with `P(a)† = P(b)†`, and every `≡` premise in typing compares meanings, not texts.

The checker keeps values in normal form and decides conversion on normal forms, so each rule must be a fact about meanings of normal forms.

## 2. The principles

- **(V1) Normal forms, compared structurally.** `v == w` (identical normal forms) and congruence through constructors, `S`, `&`, `Eq`, inductive types and borrows: the meaning of a normal form is a function of its parts. Borrows compare their labels, which name one borrow in a state.
- **(V2) Constructors are free.** A constructor value's meaning is its tag and fields; the parameters it records are determined by its type and never read by code, so conversion ignores them (`inductive-model.md` E2).
- **(V3) One text, one value.** A sealed program is a closed program; two with the same text (embedded values compared by (V1)) have the same meaning, and refinement re-normalises both the same way (`closeoff-model.md` C6). Different heads are compared by their function values, so `⌈F(σ)⌉ ≡ ⌈G(σ)⌉` exactly when `F ≡ G`.
- **(V4) A Π-type's meaning is fixed at its generic arguments.** Its domains and codomain, evaluated with the binders bound to fresh generic values, determine the type at every instance by (P) (`stability.md`). Its erasure class and whether it returns a borrow are part of its meaning (D54): they decide which functions inhabit it (a returns-proofs Π is a proposition) and how a call of an inhabitant is closed off, so types that differ in either are different sets.
- **(V5) A function value's meaning is its generic observation.** Its behaviour on every input is fixed by the observation of its generic call: the result; for a returned borrow, what the borrow holds at the return **and** the final contents after one fresh `σw` is written through it ([Obs-borrow]); and the final contents of the generic owned places behind its borrow parameters. This is complete because
  - a call's only effects are its result and its borrow arguments' final contents (frame property, `frame-model.md` F3; no borrows in data or closures);
  - a backward function only ever puts the written value where the returned borrow points, so one generic `σw` determines it (hole parametricity, `closeoff-model.md` C3);
  - a call that inspects a generic argument is closed off there, so its observation is the sealed text of the call itself, and by (V3) it is convertible only with something closing off the same call: a function that inspects its argument is convertible only with itself;
  - a call that does not inspect its generic arguments behaves uniformly at every instance by (P).
- **(V6) Least, not greatest.** A comparison that needs itself again (the `convStack`) answers "not convertible". Read coinductively, any two functions stuck at their generic calls would be identified (`Functions.CoInd`), which is false. "Not convertible" is always the safe answer (V9).
- **(V7) The unit laws and η at `Unit` are equalities of sets.** `True† = {•}` and `P† ⊆ {•}`, so `(True ∧ P)† = P†`; `Unit` has one element, so a value at `Unit` is `()` (D59).
- **(V8) `Eq` computes by meanings.** Reflexivity by conversion (V1–V7); injectivity and disjointness by (V2), with dependent constructors taken apart only while their index fields are convertible (D64); an equation over a moved-out `⊥` stays stuck (D68), since a stuck block may move a place at the generic call and not at an instance. [J] returns `t` only at convertible endpoints (D56); [T-J-stuck] closes the `J` off otherwise.
- **(V9) Conversion is monotone under refinement, in the safe direction.** Refinement maps a normal form to a normal form functionally (substitution, then re-normalisation), so convertible values stay convertible ((V5)'s function case by (P)). The other direction, not convertible at the generic call and convertible at an instance, is safe because every consumer's "not convertible" branch either errors (argument, annotation, arm and `trans` checks), stays stuck ([J-stuck], `Eq` stuck, D64's blocked injectivity), or is re-checked later ([Open]'s typing by content is checked again at [Repack]). No consumer is more permissive on "not convertible" than on "convertible".

## 3. Derived conditions against the checker

| Condition | Checker |
|---|---|
| structural congruence, borrows by label (V1) | `conv`'s cases for `S`, `&`, `tInd`, `tEq`, `borrow`, `ind` |
| recorded parameters ignored (V2) | `conv`'s `.ind` case compares tag, constructor and fields only |
| sealed programs by text, heads by conversion (V3) | `.sealed` → `convT`; `convT`'s `.val` and `.call` cases |
| Π-types at generic arguments; class and borrow flag compared (V4) | `convPi` (D48 (3), D54); the fast path only when captures and code are already the same |
| functions by result, content at return, final owned contents, plus captures (V5) | `convFn`/`convFnRun`, `obsResult` with `σw`, `env[0]`'s owned places |
| least relation (V6) | `convStack` in `convPi` and `convFn` |
| unit laws only in conversion; η at `Unit` on values (V7) | `unitTop` at each `conv`; D59's readback |
| `Eq` (V8) | `mkEqM`: `⊥` first, then `conv`, then injectivity (D64-restricted), then `distinctCtors` |
| every "not convertible" branch fails safe (V9) | the call sites: `expectTy`, annotation and arm checks, `trans`, [J]/[T-J-stuck], D64, [Open]/[Repack] |

Nothing derived is missing.

## 4. The probes (`ConvModel`, all as predicted)

Accepted, true:
- `RWEq`: reading a borrowed number and writing it back is `Noop`; `PRW` transports `PW(Noop)` to `PW(RW)` along it.
- `MvCp`: moving a borrowed number out and writing its successor equals writing the successor of a copy.
- `UUEq`: `λu. u` and `λu. ()` at `Unit` (η).
- `WrapEq`: two wrappers of one stuck call; `PZB` transports a fact across them.
- `MkEq`: two functions returning closures that capture their argument.
- `PassW0`: `Π(x : &Nat). Id(Unit, *x := 0, *x := 0)` stands where `Π(x : &Nat). Id(Unit, (), ())` is expected; `PassAnd` likewise with the unit laws.

Rejected, with their reasons asserted:
- `MvNoop` (false: `MvS` changes the place).
- `W5Eq` (false: `W5` writes before returning its borrow, so the borrow holds `S(Z)` at the return; `[Obs-borrow]` observes that content, not only where the borrow points).
- `PassW1` (false at every instance where the place is not `0`).
- `IsZEq` (true but rejected: two copies of a function that inspects its argument are closed off at their generic calls as calls of different functions, (V5)/(V6); an incompleteness, pinned).

Probed during the lane, with explicit verdicts and a rejected control, before registering.

## 5. Proposals (not implemented)

- **Drop the capture comparison in [Conv-fun].** A closure's captured values affect its meaning only through its body, which the generic observation already runs; requiring them convertible as well is stricter than (V5) needs, and rejects two closures that capture different values they never use. Sound either way; dropping it is a completeness gain and one fewer clause. The paper's [Conv-fun] text would change with it.
- **A congruence fast path for closures** (the paper's [Conv-cong] for closures: convertible captures and the same code) before running observations. A completeness and speed improvement, not a soundness one; `conv` currently has it only for Π-types.
- **State (V9) in the paper.** A.3 says conversion is the least relation; that every use of "not convertible" fails safe is what makes leastness and incompleteness harmless, and it is currently implicit.

## 6. Open

As every model lane: (V4), (V5) and (V9)'s function case rest on (P), the heart of the stability lemma N. Nothing here is new beyond it.
