> **Provenance.** Research survey produced 2026-08-04 by a read-only research agent (dllbc-fx), commissioned during the fn/λ unification design discussion to inform the borrow-mode eliminator design (`combining-fns.md` §8). Reproduced verbatim below; the downloaded primary-source texts it cites were saved to the session scratchpad.

# Effectful folds with specifications: survey for the DLLBC borrow-eliminator design

**Sources read directly (primary):** Swierstra *The Hoare State Monad* (TPHOLs'09, all 10 pages); Nanevski–Morrisett–Birkedal *Hoare Type Theory, Polymorphism and Separation* (JFP); Maillard et al. *Dijkstra Monads for All* (ICFP'19); *RustHornBelt* (PLDI'22); Denis–Jourdan *Specifying and Verifying Higher-order Rust Iterators* (TACAS'23); actual source of `krmllib/C.Loops.fst` (F*/KaRaMeL); Lean 4.30 toolchain source `Std/Do/Triple/SpecLemmas.lean` and `Std/Do/PostCond.lean` on this machine; Batteries `SatisfiesM.lean`; Coq HTT library `examples/llist.v` and `examples/quicksort.v`.
**Summarized from secondary sources only (flagged inline):** Idris `Effects`/`Control.ST`, Idris 2 linear arrays, Verus, Atkey's parameterised monads, Swierstra–Altenkirch *Beauty in the Beast*.

## The headline

The working insight — "a borrow-mode eliminator is the induction principle of the ensures discipline" — is **correct and independently rediscovered at least four times**, but nobody ships it as a *primitive*. Every system either (a) types the recursion with a spec-carrying fixpoint where the IH is just the function's own type, or (b) *derives* the eliminator as an ordinary combinator/theorem in the host language. Two systems ship (b) in production, which is the strongest de-risking evidence available.

There is a sharper structural finding that four unrelated systems converge on: **a motive relating only the entry and exit snapshots of the whole structure is not inductive.** The motive must be indexed by a *cursor* — a split into an already-processed prefix and an untouched suffix, with the suffix still pinned to the entry snapshot. This is load-bearing and is the thing the design as stated is missing.

## 1. Hoare state monad (Swierstra) — the motive IS a ternary relation

```coq
Definition Pre : Type := s → Prop.
Definition Post (a : Set) : Type := s → a → s → Prop.
Program Definition HoareState (pre : Pre) (a : Set) (post : Post a) : Set
  := forall i : {t : s | pre t}, {(x,f) : a * s | post i x f}.
```

`Post` is literally the proposed motive: initial state, result, final state. Composition is relational composition with an existential intermediate state:

```coq
Program Definition bind : forall a b P1 P2 Q1 Q2,
  (HoareState P1 a Q1) → (forall (x : a), HoareState (P2 x) b (Q2 x)) →
  HoareState (fun s1 ⇒ P1 s1 ∧ forall x s2, Q1 s1 x s2 → P2 x s2)
             b
             (fun s1 y s3 ⇒ exists x, exists s2, Q1 s1 x s2 ∧ Q2 x s2 y s3)
```

Relabelling is a `Program Fixpoint`, **not** a fold or recursor:

```coq
Program Fixpoint relabel (a : Set) (t : Tree a) :
  HoareState nat top (Tree nat)
    (fun i t f ⇒ f = i + size t ∧ flatten t = seq i (size t))
  := match t with
     | Leaf x ⇒ get ≫= fun n ⇒ put (n+1) ≫ return (Leaf n)
     | Node l r ⇒ relabel l ≫= fun l' ⇒ relabel r ≫= fun r' ⇒ return (Node l' r')
     end.
```

**How the IH manifests:** there is no induction hypothesis as such. Figure 1's residual obligation context shows the IH arriving as *ordinary hypotheses that are the recursive calls' postconditions*, delivered by `bind`'s existentials:

```
sizeL   : lState = i + size l
flattenL: flatten l = seq i (size l)
sizeR   : rState = lState + size r
flattenR: flatten r = seq lState (size r)
==========================================
n = i + size t ∧ flatten t = seq i (size t)
```

That is exactly the claim in `combining-fns.md:155` — the IH *is* the ensures at the predecessor — confirmed on a worked example.

**Two warnings that transfer.** The paper says of the obvious spec: *"If we had chosen the obvious postcondition `flatten t = seq i (size t)` we would not have been able to complete this proof."* The state-arithmetic conjunct exists purely to make the motive inductive. And for the *actually desired* postcondition: *"We cannot define a relabelling function that has this postcondition — the induction hypotheses are insufficient to complete the required proofs in the Node case."* The fix is a separate, computationally inert consequence rule:

```coq
Program Definition do (s a : Set) (P1 P2 : Pre s) (Q1 Q2 : Post s a) :
  (forall i, P2 i → P1 i) → (forall i x f, Q1 i x f → Q2 i x f) →
  HoareState P1 a Q1 → HoareState P2 a Q2 := fun str wkn c ⇒ c.
```

## 2. Hoare Type Theory — binary postconditions, and the `init`/`mem` correspondence

Verbatim from the JFP paper:

> "unlike in the Hoare type, where pre- and postconditions are unary relations over the heap `mem`, here the assertions `P` and `Q` are **binary relations on heaps**, and the typing rule for introduction of Hoare types will mediate the switch from unary to binary relations. Since `P` and `Q` are binary relations, we make them depend on two free heap variables: `init`, which denotes a specific heap in the past of the computation, and `mem`, which denotes the current heap."

with `P ◦ Q = ∃h:heap. [h/mem]P ∧ [h/init]Q`.

This maps onto DLLBC term-for-term: `init` is `old *v`, `mem` is `*v`, and DLLBC's audit at the function boundary is precisely "mediating the switch from unary to binary relations."

The recursion rule puts the spec in the context and does no structural analysis:

```
∆, f:Πx:A′.Ψ.X.{R1}y:B{R2}, x:A′; this(init) ∧ ∃Ψ.X.(R1 ∗ ⊤) ⊢ E ⇐ y:B. (∀Ψ.X.R1 ⊸ R2)
──────────────────────────────────────────────────────────────────────────────────────
∆; P ⊢ y = fix f (x:A):T = do E in eval f M ; F ⇒ z:C. (∃y. Q)
```

Loops are recursion; the invariant is the precondition of the fixpoint variable's type. No eliminator — and HTT concedes it cannot state a generic one: *"Because currently HTT lacks the ability to polymorphically abstract over predicates, like the loop invariant I above, we cannot create a generic `until` constructor... A similar requirement would also appear in the specification of the usual polymorphic functionals like `map` and `fold` over inductively defined types."* DLLBC has full dependent types so this isn't a limitation, but it confirms the motive must be first-class abstractable, not an annotation.

**The Coq HTT library is the closest existing artifact to DLLBC's target.** `examples/llist.v`:

```coq
Definition lmapT (f : A -> B) :=
  forall (p : ptr), STsep {xs : seq A} (lseq p xs, [vfun _ : unit => lseq p (map f xs)]).

Program Definition lmap f : lmapT f :=
  ffix (fun (lmap : lmapT f) p =>
    Do (if p == null then ret tt
        else t <-- !p; p ::= f t; nxt <-- !p.+1; lmap nxt)).
```

Entry payload `xs` is a ghost binder, exit payload is `map f xs` — DLLBC's telescope with the entry snapshot bound as a variable. Note the effect order: `p ::= f t` runs **before** `lmap nxt`. Top-down, no contortion, because `ffix` has no order commitment. **The "catamorphisms force bottom-up effect order" wall is a property of catamorphisms, not of spec-typed recursion** — every system here avoids it identically, by recursing with the spec as the type rather than folding over already-computed results.

`reverse` shows the cursor pattern before anyone named it:

```coq
Definition revT : Type := forall (p : ptr * ptr),
  STsep {i done : seq A} (lseq p.1 i # lseq p.2 done,
                         [vfun y => lseq y (catrev i done)]).
```

**Side-finding, directly actionable for your quicksort.** `examples/quicksort.v` encodes permutation not by counting but as an explicit permutation with bounded support:

```coq
Definition quicksort_lm_loop (a : {array 'I_n.+1 -> A}) :=
  forall (lohi : 'I_n.+1 * 'I_n.+1), let lo := lohi.1 in let hi := lohi.2 in
  STsep {f : {ffun 'I_n.+1 -> A}}
        (Array.shape a f,
        [vfun (_ : unit) h =>
           exists p, let f' := pffun p f in
             [/\ perm_on [set ix : 'I_n.+1 | lo <= ix <= hi] p,
                 h \In Array.shape a f' &
                 sorted oleq (&:(fgraph f') `[lo : nat, hi : nat])]]).
```

`exit = pffun p entry` with `perm_on [range] p` gets Perm *and* out-of-range locality in one conjunct — the thing your notes record as split into separate `_lt`/`_gt` directional halves. Given "encoding is the cost," worth a look independently of the eliminator question.

## 3. Dijkstra monads / F* — the spec of a fold is a fold of specs

```
let rec mapW (l : list α) (f : α→ W β) : W (list β) =
  match l with [] → ret [] | x :: xs → bind (f x) (λ y → bind (mapW xs f) (λ ys → ret (y :: ys)))

let rec mapD (l : list α) (w : α→ W β) (f : (a:α) → D β (w a)) : D (list β) (mapW l w) =
  match l with [] → ret [] | x :: xs → let y = f x in let ys = mapD xs w f in y :: ys
```

**The specification of an effectful fold is the pure fold of the element specifications, in the specification monad.** The motive is not written by hand — it is *computed* by running the same recursion over specs. Because `mapW` is built with the same bind order as `mapD`, the order commitment is made once, in the spec-fold, and the two agree by construction.

The generic iterator needs the invariant to be an idempotent for sequencing:

```
(* requires w : W unit with  bind w (λ() → w) ≤ w *)
let rec for_in (range : list nat) (body : nat → D unit w) : D unit w =
  match range with [] → () | i :: range → body i ; for_in range body
```

and the paper notes it uses *"the possibility to weaken the specification `bind w (λ() → w)` computed from the second branch of the match to the specification `w` by assumption"* — the consequence rule again, same place Swierstra needed it.

No eliminator for recursion: general recursion is a free monad `GenRec` over a single `call` op with a well-founded order and handler `fix : ((a : A) → GenREC (B a) (inv a)) → (a : A) → PURE (B a) (inv a)`. IH = the spec `inv` assumed for `call` at smaller arguments. Everything else is VC generation per call site.

**Low\* is the strongest single piece of evidence for the eliminator design.** `C.Loops.for` is a combinator whose *type is Nat-recursion with a heap-indexed motive*:

```fstar
val for:
  start:UInt32.t ->
  finish:UInt32.t{UInt32.v finish >= UInt32.v start} ->
  inv:(HS.mem -> nat -> Type0) ->
  f:(i:UInt32.t{UInt32.(v start <= v i /\ v i < v finish)} -> Stack unit
                        (requires (fun h -> inv h (UInt32.v i)))
                        (ensures (fun h_1 _ h_2 -> UInt32.(inv h_1 (v i) /\ inv h_2 (v i + 1)))) ) ->
  Stack unit
    (requires (fun h -> inv h (UInt32.v start)))
    (ensures (fun _ _ h_2 -> inv h_2 (UInt32.v finish)))
let rec for start finish inv f = if start = finish then () else begin f start; for (start +^ 1ul) finish inv f end
```

`inv` is the motive, `f` is the step arm, the conclusion is "motive at start implies motive at finish." It is an **ordinary recursive definition in the language**, not a primitive — and KaRaMeL recognizes it and extracts a literal C `for` loop. Exactly the shape DLLBC wants: definable, not axiomatic, with the compiler recognizing the pattern.

`in_place_map` shows what its invariant has to look like:

```fstar
let inv (h1: HS.mem) (i: nat): Type0 =
    live h1 b /\ modifies (loc_buffer b) h0 h1 /\ i <= UInt32.v l
    /\ (forall (j:nat). (j >= i /\ j < UInt32.v l) ==> get h1 b j == get h0 b j)
    /\ (forall (j:nat). j < i ==> get h1 b j == f (get h0 b j))
```

The cursor split, explicitly: below `i` the new value, at or above `i` still the *entry* value read out of the captured entry heap `h0`. Unary in form only — `h0` is closed over, making it binary in content. `repeat_range` generalizes it, and its postcondition is fold-of-specs again: `interp h_2 == Spec.Loops.repeat_range min max f (interp h_1)`.

## 4. Lean 4 — a reified induction principle for effectful iteration (shipping, 4.30)

Old idiom is thin, and its authors say so. `Batteries/Classes/SatisfiesM.lean`:

```lean
def SatisfiesM {m : Type u → Type v} [Functor m] (p : α → Prop) (x : m α) : Prop :=
  ∃ x' : m {a // p a}, Subtype.val <$> x' = x
```

Unary — postcondition on the return value only, no state relation — and the module docstring: *"`SatisfiesM` is not yet a satisfactory solution for verifying the behaviour of large scale monadic programs. Such a solution would allow ergonomic reasoning about large `do` blocks, with convenient mechanisms for introducing invariants and loop conditions as needed... This is an open research program, and for now one should not be overly ambitious using `SatisfiesM`."*

The new idiom is the answer, and it is **the closest thing in the literature to the borrow-mode eliminator**. From `Std/Do/Triple/SpecLemmas.lean`:

```lean
structure Cursor {α : Type u} (l : List α) : Type u where
  «prefix» : List α
  suffix : List α
  property : «prefix» ++ suffix = l

abbrev Invariant {α : Type u₁} (xs : List α) (β : Type u₂) (ps : PostShape.{max u₁ u₂}) :=
  PostCond (List.Cursor xs × β) ps

@[spec]
theorem Spec.forIn'_list
    {xs : List α} {init : β} {f : (a : α) → a ∈ xs → β → m (ForInStep β)}
    (inv : Invariant xs β ps)
    (step : ∀ pref cur suff (h : xs = pref ++ cur :: suff) b,
      Triple (m:=m)
        (f cur (by simp [h]) b)
        (inv.1 (⟨pref, cur::suff, h.symm⟩, b))
        (fun r => match r with
                 | .yield b' => inv.1 (⟨pref ++ [cur], suff, by simp [h]⟩, b')
                 | .done b'  => inv.1 (⟨xs, [], by simp⟩, b'), inv.2)) :
    Triple (forIn' xs init f)
           (inv.1 (⟨[], xs, rfl⟩, init))
           (fun b => inv.1 (⟨xs, [], by simp⟩, b), inv.2)
```

Read as an eliminator the correspondence is exact: `inv` is the **motive**, `step` is the **cons arm**, the conclusion's precondition is the motive at the empty cursor and its postcondition the motive at the full cursor. `Spec.foldlM_list` is derived by rewriting `foldlM` into `forIn`; `Spec.forIn_list_const_inv` is the degenerate cursor-ignoring case. The theorem's own proof is by induction on the cursor. Lean's docstring states the reading: *"Before entering the loop, the cursor's prefix is empty and the suffix is `xs`. After leaving the loop, the cursor's prefix is `xs` and the suffix is empty. During the induction step, the invariant holds for a suffix with head element `x`. After running the loop body, the invariant then holds after shifting `x` to the prefix."*

## 5. Rust verifiers — prophecies make the binary motive into *data*

RustHornBelt represents a mutable borrow as a (current, prophesied-final) pair, hence `IterMut` as a **list of such pairs**:

> `⌊IterMut<𝛼,T>⌋ ≜ List (⌊T⌋ × ⌊T⌋)`

with `iter_mut`'s spec `|𝑣.2| = |𝑣.1| → 𝛹 [zip 𝑣.1 𝑣.2]` — an elementwise split of one borrow into a list of borrows. A genuinely different move: instead of a motive relating entry and exit, the entry/exit pair is **reified as a value**, and ordinary pure list reasoning applies. `inc_vec` gets `𝑣.2 = map (+ 7) 𝑣.1 → 𝛹 []`.

Creusot builds the loop invariant on a transition relation with monoid laws:

```rust
trait Iterator {
  type Item;
  #[predicate] fn completed(&mut self) -> bool;
  #[predicate] fn produces(self, visited: Seq<Self::Item>, _: Self) -> bool;
  #[law] #[ensures(a.produces(Seq::EMPTY, a))] fn produces_refl(a: Self);
  #[law] #[requires(a.produces(ab, b) && b.produces(bc, c))]
         #[ensures(a.produces(ab.concat(bc), c))]
         fn produces_trans(a: Self, ab: Seq<Self::Item>, b: Self, bc: Seq<Self::Item>, c: Self);
  #[ensures(match result { None => self.completed(),
                           Some(v) => (*self).produces(Seq::singleton(v), ^self)})]
  fn next(&mut self) -> Option<Self::Item>;
}
```

Every `for` loop is desugared to carry `#[invariant(structural, init_iter.produces(produced, iter))]` with a ghost `produced` — the cursor prefix under a third name. `IterMut`'s spec is two lines and the whole zeroing loop verifies from one user invariant over `produced`.

**Note the cost Creusot pays that an eliminator would not:** `produces_refl` and `produces_trans` are proof obligations on every implementer, needed because the invariant goes via a reflexive-transitive relation rather than structural induction. A structurally-indexed motive gets both free. Real argument in the eliminator's favour.

Verus (secondary) is plain WP/VC generation over user-written loop invariants — no reified principle.

## 6. Where the literature is genuinely thin

- **Idris 2 linear resources: not found.** `idris2-array` gives linear `MArray n a` with `alloc`/`get`/`set`/`freeze` and a length index; per its own tutorial there is no mechanism for content invariants — no sortedness, no dependent property of contents, no fold-with-invariant. (Read via a page summary, so secondary, but consistent with search results.) The older `Effects`/`Control.ST` index by **resource types**, not propositions — `Eff a xs xs'`, `putM : y -> Eff () [STATE x] [STATE y]`. That is Atkey's parameterised monad (secondary): a different design point expressing protocols, not correctness of contents.
- **A *primitive* eliminator over a mutable reference: not found.** Four searches turned up nothing combining a dependent eliminator with a mutable/borrowed scrutinee and a binary entry/exit motive as a language primitive. Every instance here is a derived combinator (`C.Loops.for`), a derived theorem (`Spec.forIn'_list`), a desugaring (Creusot's `for`), or a spec-typed fixpoint (`ffix`, `Program Fixpoint`, HTT's `fix`). **Establishing that DLLBC's version would be near-novel as a primitive is itself a result — and it also suggests it shouldn't be one.**
- *Beauty in the Beast* (secondary; not read) is about pure functional *models* of IO/state for testing, not folds with invariants. Relevant only as the alternative strategy — denote the effect as a pure state-passing function, then use ordinary induction — which DLLBC's comptime fragment already does for the pure part.

## Comparison

| System | How the fold's spec is typed | Motive / IH form | Order commitment | Closest DLLBC analogue |
|---|---|---|---|---|
| Hoare state monad (Swierstra) | `HoareState pre a post`, `Post a = s → a → s → Prop` | Ternary relation; IH = recursive call's postcondition as context hypotheses via `bind`'s ∃ | None — `Program Fixpoint`, effects in written bind order | `old *v` / `*v` return type; `[k]`-guarded `fn` |
| HTT (Nanevski et al.) | `{P}x:A{Q}`; checking assertions binary over `init`/`mem` | Binary heap relation; IH = `f`'s own Hoare type in context | None — `fix`; loops are recursion | The audit's unary-to-binary switch at the boundary |
| HTT Coq lib (`llist`, `quicksort`) | `STsep {ghosts} (pre, [vfun r h => post])` | Entry payload as ghost binder; IH = `ffix`'s self-type | Top-down; write-then-recurse | Nearly identical to the intended `fn` signature |
| Dijkstra monads / F* | `D A w`; `mapD ... : D (list β) (mapW l w)` | Motive **computed** by folding element specs; IH = index of the recursive call | Fixed once in the spec-fold, matches impl | Comptime recursor computing the postcondition |
| Low* `C.Loops.for` | Combinator type = Nat-recursion, heap-indexed motive | `inv : HS.mem -> nat -> Type0`; IH = `f` argument's `requires` | Ascending index, fixed by combinator | **The eliminator, as a definable function** |
| Lean `Std.Do` | `Triple prog pre post`, `PostCond α ps` | `Invariant xs β ps = PostCond (List.Cursor xs × β) ps`; IH = `step` premise | Left-to-right over the list | **The eliminator, as a proven theorem** |
| Lean `SatisfiesM` | `∃ x' : m {a // p a}, val <$> x' = x` | Unary, value-only; no state relation | n/a | (none — authors call it insufficient) |
| RustHornBelt | `⌊IterMut⌋ ≜ List (⌊T⌋ × ⌊T⌋)` | Entry/exit pair reified as **data**, not a motive | n/a (spec-level) | Payload snapshot pairs |
| Creusot | `produces(self, visited, _)` + refl/trans laws | Binary transition relation labelled by `produced`; structural loop invariant | Iterator order | The `for`-desugaring's ghost prefix |
| Idris `Effects`/`ST` | `Eff a xs xs'` | Pre/post as **resource types**, not predicates | n/a | (different design point) |
| Idris 2 linear arrays | `MArray n a` linear, length-indexed | none | n/a | not found |
| Verus | `#[ensures]` + `invariant` clauses, WP/VC | User-written; VC per loop | n/a | (no reified principle) |

## Judgment

**Most de-risking prior art: Lean 4.30's `Std.Do.Spec.forIn'_list`**, with Low*'s `C.Loops.for` as corroboration. Together they establish the two things the design most needs: that an eliminator over an effectful traversal whose motive is a state relation is *provable* (Lean proves it once, by induction on the cursor, and ships it as a `@[spec]` lemma), and that it is *usable at scale as an ordinary definable combinator* rather than a kernel primitive (Low*'s `for` is a `let rec` that KaRaMeL pattern-matches into a C loop, and it is what HACL* is built on). The strategy `combining-fns.md:155` already files — guarded `fn` ⟹ definable as an eliminator term ⟹ sound, with the eliminator as a proof device rather than an implementation — is precisely what both systems landed on independently. Nothing in the literature argues the design is unsound or exotic; the risk is entirely in the motive's shape.

**Its one sharpest transferable idea: the motive must be cursor-indexed, not whole-structure-indexed.** Lean's is `PostCond (List.Cursor xs × β)` where `Cursor` carries `prefix ++ suffix = l` as a field, so the invariant can name both halves and tie them back to the original. A motive of the form "relate the entry snapshot of `&mut List T` to its exit snapshot" **cannot state the state of a partially-completed traversal**, and so cannot be what the arms prove. Each arm needs to prove: *the prefix already satisfies the exit spec, the suffix still equals the entry snapshot, and one more step moves the boundary.* Four unrelated systems converge on exactly this — Lean's `Cursor{prefix, suffix}`, Low*'s `j < i ⇒ f (get h0 b j)` alongside `j ≥ i ⇒ get h0 b j`, Creusot's ghost `produced`, HTT's `revT (i, done)` split by `#`. For a `Cons(hd, tl)` arm over `&mut List T` this means the motive's arguments are the already-rebuilt prefix and the still-entry-valued tail — and DLLBC has the machinery: the borrow-match's suspended field loans are already the syntactic marker for "the untouched suffix."

**Best argument against, and it is real: Swierstra's `NoDup` failure.** You cannot assume the declared `ensures` is a usable motive. `relabel` cannot be defined with `NoDup (flatten t)` as its postcondition at all — the arms are unprovable — and the fix is to prove a stronger postcondition and weaken afterwards through a separate, computationally inert consequence rule (`do`). The same weakening appears independently in DM4All's `for_in` (`bind w (λ() → w) ≤ w`) and as HTT's admissible rule of consequence. If the borrow-mode eliminator forces motive = signature, this failure mode will dominate the user experience, and it will present as "the checker rejects my correct postcondition." Whatever the surface syntax, there must be a way to give the eliminator a motive strictly stronger than the declared `ensures`, plus an admission step that weakens it at the audit.

**Runner-up idea, if the cursor proves too costly to write by hand:** DM4All's `mapD : D (list β) (mapW l w)` and Low*'s `interp h_2 == Spec.Loops.repeat_range min max f (interp h_1)` both *compute* the motive by folding the element spec over the same structure rather than asking the user to state a relation. This dissolves the accumulator-as-motive/closure problem outright (the spec-fold's bind order is chosen once and matches the implementation's), and it plays to DLLBC's strengths — a comptime recursor computing on the cons view is exactly what `design-arrays-slices.md`'s three ι-rules already provide.

## Sources

- [The Hoare State Monad (Swierstra, TPHOLs'09)](https://webspace.science.uu.nl/~swier004/publications/2009-tphols.pdf) · [Springer](https://link.springer.com/chapter/10.1007/978-3-642-03359-9_30)
- [Hoare Type Theory, Polymorphism and Separation (JFP)](https://software.imdea.org/~aleks/htt/jfpsep07.pdf) · [Coq HTT library](https://github.com/imdea-software/htt)
- [Dijkstra Monads for All (ICFP'19)](https://arxiv.org/pdf/1903.01237) · [Dijkstra Monads for Free](https://fstar-lang.org/papers/dm4free/)
- [F*/KaRaMeL `krmllib/C.Loops.fst`](https://raw.githubusercontent.com/FStarLang/karamel/master/krmllib/C.Loops.fst)
- Lean 4.30 toolchain source: `Std/Do/Triple/SpecLemmas.lean`, `Std/Do/PostCond.lean` (local `~/.elan/toolchains/leanprover--lean4---v4.30.0/src/lean/`) · [Batteries `SatisfiesM.lean`](https://github.com/leanprover-community/batteries/blob/main/Batteries/Classes/SatisfiesM.lean)
- [RustHornBelt (PLDI'22)](https://people.mpi-sws.org/~dreyer/papers/rusthornbelt/paper.pdf)
- [Specifying and Verifying Higher-order Rust Iterators (TACAS'23)](https://hal.science/hal-03827702/document) · [Creusot](https://creusot.rs/)
- [Verus](https://arxiv.org/pdf/2303.05491) · [Atkey, Parameterised notions of computation](https://bentnib.org/paramnotions-jfp.html) · [Idris Dependent Effects](https://docs.idris-lang.org/en/latest/effects/depeff.html) · [idris2-array linear tutorial](https://github.com/stefan-hoeck/idris2-array/blob/main/docs/src/Linear/Tutorial.md) · [Beauty in the Beast](https://people.cs.nott.ac.uk/psztxa/publ/beast.pdf)
