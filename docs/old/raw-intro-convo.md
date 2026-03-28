
What do you know about the Ochre project? (Programming language) from memories

From memory, only a little:

Ochre is the wider project context I’m currently operating in, but I do not have a stored technical description of an “Ochre programming language” itself.

What I do have related to it is:

you previously said you wanted to continue work on an end section describing future languages called Och and Ochr

that you wanted to brainstorm that work against cutting-edge LLMs

that this seemed connected to a broader research/design direction rather than a mainstream existing language I already know independently

So my memory is basically:

Ochre = the project umbrella/context

Och and Ochr = future language ideas you’ve mentioned before

but I do not have a concrete remembered spec, syntax, semantics, compiler architecture, or design notes for the language itself

If you want, I can also tell you what I infer about Ochre from the surrounding context versus what is actually explicitly stored.


Repeat verbatim what is explicitly stored

Here is the exact stored memory relevant to Ochre (verbatim):

Charlie wants to continue work on this, specifically the end section where it describes future languages Och and Ochr

To do this, I want to brainstorm against cutting edge LLMs

Characterise the kind of work required to continue this line of work, then research the internet to produce a well-cited report on what the best LLMs for the task would be

That’s the only explicit stored reference.


Read and understand charlielidbury.com/ochre, let me know if you have any problems reading the page

I can’t directly access or read live webpages unless I explicitly fetch them.

So right now, I haven’t read that page yet.

Two options:

If you want: I can fetch and analyse it (just say “go ahead”).

Or paste the content / key sections and I’ll go deep on it immediately.

No issues yet—just haven’t loaded it.


Go ahead and


Thought for 19s
I hit a real problem reading it.

charlielidbury.com/ochre did not resolve successfully from my side, so I couldn’t fetch the page. I also couldn’t get the web fetcher to open it directly.

So at the moment I have not read and understood the page yet.

Best next step is for you to either paste the text here, upload it, or send an alternative working URL.


What was the problem with resolution? 

Short answer: I don’t get low-level diagnostics.

When I try to fetch a page, I’m going through a sandboxed retrieval layer—not doing raw DNS/HTTP myself—so I don’t see errors like:

DNS failure (NXDOMAIN)

TLS/SSL handshake issues

HTTP status codes (403, 404, etc.)

All I get is effectively: “failed to retrieve”.

So I can’t tell whether it was:

the domain not resolving,

the server blocking the request (very common),

HTTPS / cert issues,

or just a transient failure.

If you want a quick sanity check on your side:

dig charlielidbury.com
curl -I https://charlielidbury.com/ochre
If that works for you, the most likely cause is bot blocking / non-browser request rejection.

Fastest path forward: paste the page or give me a mirror—I’ll go deep on it.


Here is the page:

Ochre is a (work in progress) language which aims to use a new architecture:
💡

Instead of runtime code being expressed in a different language than types, Ochre expresses both in the same language, where types are just a special case of programs where the program has “ambiguity”.
In this paradigm, mutability and dependent types are compatible, allowing for a high performance system prover.
What?
Ochre will be a systems theorem prover, which is the intersection between:
	1	low-level, systems programming languages like Rust or C and
	2	theorem provers like Lean or Agda.
The former will be achieved by using Rust’s ownership semantics and borrow checker. The latter will be achieved via the inclusion of dependent types and hopefully some rigor.
￼
More or less, Ochre = Rust + Dependent Types.
Why?
These features would allow programmers to verify properties about their programs without leaving the language they’re writing those programs in. Hopefully this will make verification easier, and therefore increase how much software is formally verified globally.
I see this verification dividing into two categories:
	1	Proving properties we currently tell the compiler to assume, like removing the need for unsafe code in RefCell and Vec.
	2	Proving properties we currently don’t get the compiler involved in, like proving a financial exchange never creates nor destroys money, or that a compiler respects its formal specification.
There are already languages which support verification, but they are typically dependently typed pure functional languages which makes writing code harder both in terms of ergonomics, and runtime performance.
There are multi-language stacks which allow verification of high performance software, like the Low* translation of F* to C, but they require the programmer to significantly change how they write their programs (in Low*’s case, this means existing within the Stack monad), instead of writing more “natural” code like safe Rust.
The goal of Ochre is to allow programmers to write in a language very similar to Rust, while having access to the power of a dependent type system.
How?
The exact semantics of Ochre, and therefore the proper answer to how Ochre works are given in my masters thesis (PDF at top of this page), but here is the rough “technique” it uses to type check programs which have both dependent types and mutability:
‣

How I plan on doing it
	1	Like Rust, mutation is only allowed when the code performing the mutation has exclusive access to the data.
	2	This is done via a borrow checker and ownership, like it is in Rust.
	3	A combination of strong mutation and TypeScript-like structural typing is used to keep track of as much information statically as possible about every given variable.
	4	For example, the code x = 5 mutates x, which causes its type to be updated to the singleton type of just 5, instead of to the more generic Nat type of which 5 is a subtype.
	5	‣Strong Mutation‣TypeScript-like Structural Typing
	6	The model of computation for type level computations and runtime computations are almost exactly the same, which allows the type level to capture almost any desired runtime property.
	7	For example, the type of a function is itself a function (the function being used as a type must be an approximation of the function being typed). If this function is non-constant, it represents a dependent function type.
‣

How I know it’s possible
Begin proof:
	1	Aeneas demonstrated that Rust programs have the right “shape” to be reasoned about with dependent types
	a	They did this by showing Rust could be translated to F*, a pure functional dependently typed language
	2	If you could set up the following pipeline:
	a	annotate the source (Rust) program with dependent types and proof terms 
	b	carry those over during the translation step
	c	Let F* do the verification of the proof
	3	Then you would end up with a single user-facing language (Rust + the annotations from 2.a.) which has both high performance, and the ability to do verification.
Since this single language which does both exists, Ochre is just a matter of building that or something better.
💡

This pipeline is what I initially set out to build for my masters thesis, but in the process of doing that I realised that
	1	the simplicity of the surface level language is compromised due to having to translate to two very different languages
	2	the Rust ⇒ F* translation is as hard to define as a full type checker, so instead of making an intermediate artefact (F*) and putting that into F*’s type checker, you might as well just make a type system specifically for the surface language
and so decided to just build a new language from scratch (although it is actually embedded within Rust as a macro)
 
To illustrate how the above three aspects work together, here is an example of mutation interacting with dependent pairs.
A Taste of Ochre
First, we define a few basic types:

Copy
Bool = 'true | 'false;
Letter = 'a | 'b | 'c;
Ochre knows to interpret Bool and Letter as types because they begin with a capital letter.
‣
Equivalent Haskell

Copy
data Bool = True | False
data Letter = A | B | C

‣
Equivalent TypeScript

Copy
type Bool = "true" | "false"
type Letter = "a" | "b" | "c"

' denotes an atom, which is an arbitrary value, uniquely identified by the tag after the '. When being interpreted as a type like they are in this code snippet, atoms are interpreted as the singleton type consisting of just that atom, then | union’s those singleton types together into the non-singleton types Bool and Letter.
Then we define a dependent pair type, where the right can be either a Bool or a Letter, depending on whether the left is 'true or 'false.

Copy
DPair = (tag: Bool, match tag {
	'true => Bool,
	'false => Letter,
});

‣
Shorter version using syntactic sugar

Copy
DPair = ('true, Bool) | ('false, Letter);

('true, Bool) represents a pair where the left is always 'true (the singleton type of just 'true), and the right is always a Bool.
When it is union’ed with another similar pair, the result is a dependent pair, because type union is precise.
In the above snippet the left of the pair is a Bool, then the right of the pair is an expression which depends on the value of the left. Namely, its a match statement which returns a different type for the true and false case.
Now we can define a function which mutates one of these dependent pairs:

Copy
overwrite = (p: &mut DPair) {
	*p = ('true, 'false);
}
The function’s return type isn’t specified, so it defaults to *, which represents uninitialised data/top/no information.
This defines a function overwrite which takes in a mutable reference (a pointer + a proof this pointer is unique) to a DPair as defined earlier.
The body of overwrite may change the type being pointed at, but must leave it as a DPair by the end of the function body.
At the end of the function the type of p is the singleton type &mut ('true, 'false), which can then be widened to &mut DPair, since ('true, 'false) is a subtype of DPair.
Progress
My progress so far has been formally specifying Ochre’s syntax and typing rules as my masters project and implementing the type checker for part of the language. Both of these will need substantial work before they can be used to implement and verify useful software, most glaringly: Ochre, as formally specified, is unsound, will need major rework and the implementation doesn’t generate any code.
Show Me More!
For code examples, formal specification, and some evaluation, see my masters thesis.

No problem reading this version.

My understanding of the page is:

Ochre is a proposed systems theorem prover: roughly Rust + dependent types. The core claim is that runtime programs and types should live in the same language, with types treated as a special case of programs that retain ambiguity/approximation. That is the architectural move that is supposed to make mutability compatible with dependent typing, instead of forcing the usual pure-functional theorem prover model.

The mechanism, as described here, seems to be:

Rust-style ownership + borrow checking controls mutation

Strong mutation updates static knowledge after assignment

Structural typing / precise unions preserve fine-grained information

type-level and runtime computation have nearly the same computational model

function types are themselves functions, with dependent function types arising when the “type function” is non-constant

The key example is that after x = 5, x can have the singleton type 5, not just Nat, and similarly mutable updates to a dependent pair can refine then widen back into the enclosing dependent type.

I also understand the “why it’s possible” argument:

Aeneas suggests Rust has the right shape for dependent reasoning via translation to F*

a Rust-plus-annotations surface language could in principle support both performance and verification

therefore Ochre aims to collapse that multi-language pipeline into one native language / type system

The main caveat stated on the page is also clear:

the current formalisation is unsound

it needs major redesign

the implementation is only partial and does not generate code yet

A couple of places where I’d say I understand the intent but not yet the full precise semantics from this page alone:

what exactly “ambiguity” means technically

the exact subtyping/normalisation rules around strong mutation

how function-as-type approximation is constrained to keep checking decidable

where the current unsoundness comes from

how close the language is meant to stay to Rust operationally, especially around aliasing, references, and layout

So: I can read it fine, and I think I’ve got the main idea. The only “problems” are not reading problems, but that the page is necessarily high-level in a few semantically crucial places.



Ochre_Thesis_Main.pdf
PDF
https://assets.super.so/f890b173-9aa0-4184-8dbd-d0ee94de3ebb/files/00463014-8f18-41dc-81f5-2dccbb91ceae/Ochre_Thesis_Main.pdf

Can you see the contents of this pdf? I have lots of latex typing rules in there, can you see them or does your pdf viewer damage them? 

Short answer: yes — I can see your LaTeX-style typing rules, and they’re mostly intact, but not perfectly rendered.

Here’s the precise breakdown based on what I’m seeing.

✅ What works well
1. The formal structure is preserved
I can clearly see:

inference-style structure (even if not always in fraction form)

environments ({ b ↦ ... })

typing/state evolution across statements

syntax definitions and grammars

For example, this kind of thing comes through cleanly:

{b ↦ {'true, 'false}} → {b ↦ 'true} → merged environments


And your explanation of abstract vs concrete semantics is readable:

“abstract semantics defines how the type of a term is derived (as a set of typing rules would)”


2. Core notation survives
These are all readable:

'atoms

unions { 'true, 'false }

mappings x ↦ T

function types T -> T

dependent-like constructs in prose

Even your “type = set of values” model is very clear:

“a type is a set of possible values”


⚠️ What is degraded / lossy
1. Inference rules (biggest issue)
If you have proper LaTeX rules like:

Γ ⊢ M : T
────────────
Γ ⊢ ...
Those do NOT render cleanly. Instead:

fraction bars are often lost

premises/conclusions become linearised text

alignment is gone

So I can read the rules, but not in their original structured form.

2. Some symbols get mangled
You can see this here:

7→ instead of ↦

weird hyphenation / broken arrows

occasional spacing glitches

Example:

{Bool 7→ {'true, 'false}}


This is recoverable (I can infer it’s ↦), but it’s not pristine.

3. Grammar formatting is partially flattened
Your formal grammar:

S ::= ...
T, U, M, N ::= ...
comes through, but:

layout is compressed

multi-line productions lose visual grouping

Example:

S ::= M | M = N; S | match M { ... }


Still readable, just less “paper-quality”.

4. Mathematical layout ≠ LaTeX fidelity
Anything relying on:

alignment

spacing

multi-line derivations

visual hierarchy

…gets flattened into linear text.

🧠 Net assessment (important)
I can absolutely read and reason about your typing rules

I can reconstruct most intended meaning

But I do not see them with LaTeX-grade fidelity

Think:

“semantic fidelity high, visual fidelity medium”

🚨 When this becomes a real problem
If your argument depends on:

subtle rule distinctions via layout

side conditions placed above/below bars

multiple premises visually grouped

then I may:

misinterpret grouping

miss precedence/structure

👍 Best way to work with me on this
If you want precise feedback on typing rules, do one of:

Option A (best)
Paste rules directly in LaTeX like:

\frac{Γ ⊢ M : T}{Γ ⊢ ...}
Option B
Screenshot the rule

Option C
Ask me to reconstruct the rule from the PDF (I can normalise it)

Bottom line
Yes, I can see your typing rules

No, they are not perfectly preserved visually

But I can still reason about them at a research-level accuracy, with occasional reconstruction

If you want, I can:

pick one rule from your thesis

rewrite it cleanly in LaTeX

and sanity-check it for soundness

That would actually be a very high-leverage next step.


What do you think of Och, do you get what I’m trying to achieve with it? 

Yes — I think I do get what you’re aiming for with Och, and it’s actually quite a distinctive (and ambitious) direction.

Let me reflect it back in my own words so you can sanity-check whether I’ve really got it.

🧠 My understanding of Och (core idea)
At a high level, Ochre (and Och) is trying to do:

Make types = exact sets of runtime values, and make programs analyzable via abstract interpretation that is the type system.

Not:

“types approximate programs” (like most PLs)

But:

types are precise semantic descriptions of program behaviour

🔥 The key moves you’re making
1. Types are sets of values (fully semantic)
You explicitly collapse:

type vs value distinction

type constructors vs term constructors

“the type of every term is itself” 


This is very strong — stronger than:

Haskell

Rust

even most dependent type systems

It’s closer to:

set-theoretic type theory

semantic subtyping (Frisch/Castagna style)

but pushed into a systems language setting

2. Type checking = abstract interpretation
This is the real core.

Instead of:

typing rules over syntax

You do:

execute the program abstractly over sets of values

Example (your match):

branch refines b to 'true or 'false

environments are unioned after control flow


So:

Control flow = type refinement = dataflow analysis = type checking

This is very reminiscent of:

abstract interpretation (Cousot)

symbolic execution

flow typing (TypeScript / refinement types)

…but unified into a single semantic model

3. Precision-first typing (not approximation-first)
You explicitly say:

“type annotations serve only to lose type information” 


That’s a huge philosophical inversion.

Most languages:

types are coarse abstractions

Och:

types are maximally precise, unless you deliberately widen them

This is much closer to:

proof assistants

symbolic execution engines

SMT-backed refinement typing

4. Dependent behaviour without full dependent pain
You’re sneaking in dependent typing via:

“return type can depend on the input type because we store syntax” 


But:

not full Coq/Agda

not proof-heavy

not normalization-heavy

Instead:

dependency emerges from abstract execution

This is very clever.

🧭 What Och (the future language) seems to be aiming for
Reading between the lines (and your research direction), Och feels like:

A systems language where program execution, type checking, and symbolic reasoning are the same process.

With goals like:

✅ Precise reasoning about programs
no “unknown” types unless you introduce them

exact tracking of values across control flow

✅ Eliminate whole classes of bugs
impossible states are literally unrepresentable

not via annotations, but via execution semantics

✅ Systems-level usability
unlike Coq/Idris:

mutation exists

control flow exists

performance matters

✅ Compositional reasoning
environments merge via unions

subtyping = set inclusion (implicitly)

🧨 What’s particularly novel / interesting
These stood out as genuinely non-trivial contributions:

1. “Types are terms” pushed all the way
A lot of languages flirt with this.

You go all in:

no nominal distinction

no separate type language

That’s bold and clean.

2. Abstract interpretation as the only typing mechanism
Most systems:

typing rules + optional analysis

You:

analysis is typing

This is very aligned with your broader work (Agentica / execution-driven semantics).

3. Precision-by-default philosophy
This is rare.

Most languages:

approximate by default → refine if needed

You:

precise by default → widen if needed

That flips ergonomics and performance tradeoffs.

🤔 Where I think the hard problems are (honest critique)
If I push on it a bit:

1. Termination / complexity of type checking
Abstract interpretation can:

explode combinatorially

struggle with loops / recursion

So you’ll need:

widening strategies

fixpoint computation

maybe fuel / bounds

Otherwise:

type checking = symbolic execution = potentially intractable

2. Ergonomics of “too precise”
If everything is maximally precise:

types become huge unions

environments become large

readability suffers

You will need:

good ways to collapse / summarise types

intentional abstraction boundaries

3. Mutation + precision tension
You allow mutation:

b = 'true;
This creates:

path-sensitive state

non-monotonic reasoning

Your solution (environment unioning) is nice, but:

scaling this to larger programs is hard

4. Effects / IO / real systems concerns
Not fully clear yet:

how side effects are modelled

whether effects are tracked in the same semantic space

This is usually where these systems get messy.

🧠 My high-level take
I’d summarise Och as:

“Abstract interpretation as a programming language”

or even:

“Symbolic execution, but made into a systems language.”

And that’s very aligned with where things are going:

LLM agents → symbolic execution hybrids

program synthesis → execution-driven

verification → more automated, less proof-heavy

🔥 Most interesting meta-point (given your broader work)
This connects extremely well to your Agentica direction:

agents generate programs

those programs are executed + analysed

correctness emerges from execution traces

Och is basically:

the ideal substrate for agents writing verifiable code

👍 Final verdict
Yes — I think I understand what you’re trying to do, and:

it’s coherent

it’s non-trivial

it’s research-worthy

and importantly: it’s different from the usual PL directions

One question back to you (important)
If I had to probe the core design:

Do you see Och as ultimately:

(A) a programming language for humans
or
(B) a semantic substrate for agents / compilers / verification systems

Because right now, it feels much closer to (B) — and that has big implications for how you design the next steps.


The ochre and agentica projects are totally separate things. I have no intentions of using ochre for agentica

The only LLM component of Ochre is that which all programming languages share - they’re likely going to be written by coding agents 

——


Och is a research artefact, it is not supposed to be a standalone language which will be useful. It doesn’t have mutation nor ownership, so it can’t be a systems language

When attempting to prove the soundness of ochres type system I encountered a lot of novel difficulty for example with proving monotonicity (more approximate typing context => more approximate conclusion). During these proofs the mutation and ownership really only got in the way, and I couldn’t tell whether my core idea was broken, or whether I just could see how to fix it due to lots of noise 

That makes sense, and yes — with that clarification, I think I get Och much more precisely.

I had over-associated it with your other work. That was wrong here.

What you’re describing is:

Och is a de-noised research vehicle for the core semantic idea.
Not a practical language, not a systems language, and not something meant to stand alone for users.

So the point of Och is not:

“can I build useful software in this?”

or even “is this already Rust + dependent types?”

The point is more like:

strip away mutation / ownership / borrowing

isolate the “terms are their own types / typing as abstract interpretation / precision-vs-approximation” core

determine whether that core is actually sound and mathematically well-behaved

That is a very sensible move.

The way you describe the motivation is especially clear:

when proving things like monotonicity, mutation and ownership add huge amounts of proof noise, so you can’t tell whether the underlying idea is wrong or whether the proof is just obscured by incidental complexity

That feels exactly right. In fact, from what I’ve seen of the thesis, Ochre has at least three conceptually different sources of difficulty entangled together:

the core idea
types as semantic approximations of terms, terms-as-types, abstract interpretation as typing

dependent structure / precision machinery
unions, subtyping, pair dependence, environment narrowing, stored syntax

systems machinery
moves, loans, borrows, drop, write/read duality, mutation

If you try to prove soundness or monotonicity with all three present at once, a failed proof is hard to interpret. It does not tell you where the defect is.

So Och seems like the right scientific move:
factor the hypothesis.

My current understanding of Och is:

it is a minimal core calculus

intended to test whether your semantic picture has good metatheory

especially properties like:

monotonicity

subtyping preservation

soundness of abstract vs concrete interpretation

maybe precision properties around joins/unions

and only once that is understood would you layer back in ownership, then borrowing, then mutation

That seems like a strong research methodology, not a retreat.

I also think your proposed sequence in the thesis makes a lot of sense:

Och: no mutation, no ownership noise, isolate the terms/types idea

Ochr: add ownership / maybe immutable borrowing

only later reintroduce mutable references and the full Ochre story

That staging seems valuable because each step answers a different question:

Och: is the semantic core sane?

Ochr: can the core coexist with linear/ownership-style resource tracking?

Ochre: can that whole thing survive mutation?

And those are genuinely different research questions.

My read is that you are trying to answer:

“Is my fundamental way of unifying terms and types via approximation actually sound, before I contaminate the question with borrow-checking complexity?”

Yes, I get that now.

And I think that is the right instinct, because monotonicity is exactly the kind of property that tells you whether the abstract interpretation story is even pointed in the right direction. If monotonicity is hard to even state cleanly in the full system, or keeps failing for reasons tangled up with mutation, then building a smaller calculus is the honest way to find out whether the semantic heart of the idea works.

My strongest positive reaction to Och is:

it gives you falsifiability.

Without Och, Ochre risks being too complicated to diagnose:

maybe unsound because the core idea is wrong

maybe unsound because stored syntax in environments is wrong

maybe unsound because write judgments are awkward

maybe unsound because borrowing/mutation interacts badly with dependence

With Och, you can ask a cleaner question:

if the metatheory still fails, the core idea is in trouble

if the metatheory works, you’ve bought evidence that the later failures are in the resource/mutation layer

That is exactly what a good core calculus is for.

My one substantive thought is that Och probably should be judged less as “a small language” and more as a proof instrument. So the design criterion should be ruthless: anything that does not help isolate the semantic hypothesis should probably be removed, even if it is elegant or expressive.

In other words, for Och I would prioritise:

easiest possible statement of monotonicity

easiest possible soundness theorem

clearest subtype lattice / approximation order

clearest relation between abstract and concrete evaluation

over almost everything else.

So yes: I do get what you’re trying to achieve with Och now, and it seems like the right move.

The interesting next question, to me, is not “is Och useful?” but:

what is the smallest Och that still faithfully tests the core idea you care about?


I’ve got some ideas, but can I get your answer that question? 

Yes.

My answer is: the smallest Och should keep only the pieces needed to test this claim:

Abstract interpretation over terms-as-types gives a sound, monotone notion of typing, where widening the context widens the conclusion.

So I would keep surprisingly little.

What I would keep
I’d keep just:

variables

lambda / application

top

type annotation / ascription

whatever minimal notion of subtyping you need

one notion of abstract evaluation and one notion of concrete evaluation

That is very close to the syntax sketch you already have for Och in the thesis. 


What I would remove first
I would remove, at least initially:

pairs

atoms

unions

statements vs expressions

write judgments

compile-time vs runtime split

environment mutation of any kind

any stored syntax in values except perhaps closures/functions themselves

Because each of those adds a second source of complexity:

pairs introduce dependent elimination and “right depends on left”

atoms + unions introduce semantic subtyping / joins / precision questions

write judgments massively complicate monotonicity statements

statements exist mainly because of environment-changing constructs

comptime/runtime doubles the semantics

stored syntax in the environment risks contextual instability headaches

If the goal is to isolate the core idea, I would not ask Och to test all of that at once.

The calculus I would actually start from
I’d start with something like:

M,N ::= x | λx:T. M | M N | ⊤ | M : T
and types are just terms, modulo whatever well-formedness discipline you need.

Then define:

concrete evaluation: ordinary evaluation to values

abstract evaluation: evaluates to an approximating term/type

a preorder ⊑

soundness: if concrete gives v and abstract gives t, then v ⊑ t

monotonicity: narrowing the input environment narrows the abstract result

That seems like the true core.

Why I would initially drop unions
Even though unions feel central to Ochre, I suspect they are not central to the first test of the idea.

Because the first question is not:

can you express rich precise types?

It is:

does this semantic architecture behave well at all?

Unions are where precision really starts to matter, but they also bring join laws, normalization choices, and awkward cases around function types. I would add them only after the base monotonicity proof works in the union-free fragment.

Why I would initially drop write judgments
This is the big one.

My instinct is that read-only abstract interpretation is the real semantic core, and write is a later elaboration that becomes necessary once you want destructuring, mutation, narrowing-by-pattern, etc.

If monotonicity is already hard in the read-only system, that tells you something deep.
If it is easy there but hard once write is added, then you’ve localized the trouble.

So for smallest Och, I would want:

no write relation

no assignment

no narrowing-via-write

no pattern-directed reconstruction

Just read/evaluate.

What I would add back first
My order would be:

Stage 0: Pure read-only lambda core
variables

abstraction

application

top

ascription

subtyping preorder

Prove:

monotonicity

abstract/concrete soundness

substitution-style lemmas

Stage 1: Add unions
Now test:

joins

precision

whether your approximation story actually becomes interesting

Stage 2: Add a base datatype
Probably atoms, not pairs.

Atoms are nice because they let you test:

singleton precision

case distinctions

narrowing
without bringing dependency between components.

Stage 3: Add match / flow sensitivity
Now you can test:

branch refinement

join of branch results

whether environment refinement is stable

Stage 4: Add dependent pairs or equivalent dependency mechanism
Only now would I test the “left determines right” idea.

Because this is probably the first place where “terms are their own types” becomes genuinely distinctive rather than just elegant.

My guess about the true minimal research question
I think the smallest Och should answer:

Can a language where terms are their own most precise types support a monotone abstract semantics over environments, before adding resource sensitivity or dependent data structure machinery?

That suggests the absolute minimal Och is even smaller than your sketched one.

One sharper recommendation
I would strongly consider making the first Och call-by-value STLC + top + subtyping + ascription, with terms-as-types, but without dependency.

That sounds almost too weak, but it buys you something important:

if even that fails, the core idea is probably broken

if that works, then dependency is the next ingredient to blame/test

So in my head:

Och₀: no dependency, no unions, no data

Och₁: add unions

Och₂: add dependency

That would give you very clean fault isolation.

Bottom line
My answer is:

The smallest Och should be a pure, read-only lambda calculus with terms-as-types, subtyping, top, and ascription — and probably nothing else.

Then add back, in order:

unions

atoms + match

dependency

ownership

borrowing

mutation

If you want, tell me your ideas and I’ll compare them against this decomposition.


Thanks! That is a brilliant continuation of my ideas!

It is very common for junior researchers like myself to jump into things only to realise it’s already been done

I want to do a review of existing concepts from two angles:
1. Academia can be very precise about language and phrasing - it’s important to phrase what you’re doing in the same way as has always been done, so you fit in like legos. What’s the best way to phrase this Och project in such a way?
2. Without searching the web, are you of any type systems which follow these patterns and work like Och? What are they?
3. With web search, can you find any prior art in this space? Any existing results which I would care about?


Thought for 56s
Yes. My read is that the cleanest way to position Och is not as “a baby systems language,” but as a core calculus for the metatheory of your main idea: a pure higher-order language where typing is presented semantically, via approximation, rather than as a conventional syntax-directed proof system. In existing PL language, the closest phrases are semantic subtyping / set-theoretic types, singleton-like precision, flow-sensitive refinement, and abstract-interpretation-based analysis. I would describe Och as something like: “a proof-oriented core calculus for semantic typing by abstract interpretation” or “a pure λ-calculus with semantic subtyping and precision-by-approximation.” That phrasing fits the literature better than “a small version of Ochre.” 

The most “lego-compatible” framing is probably this: Och studies a semantic presentation of typing where types denote sets of program behaviors/values, subtyping is semantic inclusion, and abstract evaluation computes sound approximations of concrete evaluation. That immediately puts you in conversation with the semantic-subtyping literature, where subtyping is defined set-theoretically, and with the abstract-interpretation literature, where analyses are derived as sound over-approximations of execution. It also signals that Och is a core calculus meant to isolate metatheoretic questions such as soundness and monotonicity, not a usability-oriented end-user language. 

Off the top of my head, before searching, the buckets I would have named as “closest relatives” are these. First, semantic subtyping / set-theoretic type systems: Castagna/Frisch-style work is the most obvious match for your “types as sets” and “subtyping as inclusion” instinct. Second, occurrence typing / flow typing: Typed Scheme and later work are close to your environment refinement after case splits. Third, refinement and liquid types: not the same architecture, but they share the goal of getting more precise static facts than ordinary HM typing. Fourth, Dependent ML / singleton-type lines of work: these are relevant whenever you want terms to drive type precision without going full theorem prover. Fifth, abstracting abstract machines / abstracting definitional interpreters: these are the closest precedents for “derive the static semantics from an evaluator-like semantics.” 

The single closest prior-art family is, in my view, semantic subtyping. Castagna’s tutorial explicitly frames subtyping semantically and shows how to add set-theoretic union, intersection, and negation types; Frisch/Castagna/Benzaken’s work likewise defines subtyping by interpreting types set-theoretically. That is very close to your “type = set of possible values” slogan. Where Och seems different is that you are not just using set-theoretic types as a rich type algebra; you are pushing toward evaluation-style typing, where abstract execution itself is the typing engine. 

The second closest family is occurrence typing. Typed Scheme’s core move is to refine a variable’s type after dynamic tests and propagate that information through control flow. Castagna’s later work on occurrence typing makes the same connection to union elimination and type-case refinement. That feels close to your branch-sensitive narrowing story, even though Och’s philosophical basis is more semantic and less “retrofit a typed discipline onto a dynamic language.” 

A third useful comparison is refinement / liquid types. Liquid Types explicitly combine ordinary type inference with predicate abstraction, and later work describes refinement-type inference via abstract interpretation. That is relevant not because Och is “just a refinement type system” — it is not — but because this line already occupies the space where typing and abstract interpretation blur together. If you write about Och, this is worth citing as nearby-but-different work: liquid types enrich types with logical predicates; Och instead seems to make semantic approximation itself the primary typing presentation. 

A fourth comparison is Dependent ML. Xi and Pfenning’s DML was explicitly about enriching ML with a restricted form of dependent types to obtain more precise type information while keeping the system practical. That seems relevant to your goals even if the mechanics differ: DML uses constrained indices and proof obligations, whereas Och is trying to study a different route to precision. Still, if someone in PL asks “what tradition is this in?”, DML is an important answer. 

The line that feels most methodologically relevant is Abstracting Abstract Machines and Abstracting Definitional Interpreters. Van Horn and Might present abstract interpretation as a systematic abstraction of machine semantics; Darais et al. explicitly study definitional interpreters as a basis for abstract interpretation, symbolic execution, and their intermixings. That is not the same thing as Och, but it is very close in spirit to the idea that a semantic evaluator can be transformed into a sound static analysis, and that properties like soundness and precision can be studied at that level. 

One more niche but relevant piece is semantic types in the literal sense. Vouillon’s “Semantic types: a fresh look at the ideal model for types” says, in the abstract, that types are defined as sets of terms instead of sets of elements of a semantic domain. That is not your whole project, but it is unusually close to your instinct that the right semantic object is very term-near, not a separate denotational universe. I would definitely read that. 

So my verdict on prior art is: pieces of Och already exist, but not obviously the exact combination you care about. Semantic subtyping covers the “types as sets / inclusion as subtyping” piece. Occurrence typing covers the “flow-sensitive narrowing” piece. Liquid/refinement typing covers the “typing as precise static reasoning” piece. AAM/ADI cover the “derive analysis from evaluators” piece. DML and singleton-style work cover the “term-driven type precision” piece. What I do not immediately see in prior art is a famous, standard system whose center of gravity is exactly: “a pure core calculus where the most precise type of a term is the term itself, and typing is deliberately presented as abstract evaluation to study monotonicity/soundness before adding systems features.” That may exist, but it is not jumping out as a standard named result. 

If you want the safest phrasing for a paper or proposal, I would use something like:

Och is a proof-oriented core calculus for studying semantic typing by abstract interpretation. It combines a pure higher-order language with semantic subtyping and precision-sensitive typing, in order to isolate metatheoretic properties such as soundness and monotonicity before reintroducing ownership and mutation.

That sounds legible to PL people, and it honestly reflects what you told me. 

The papers I would put at the top of your reading list are: Castagna’s semantic-subtyping tutorial, Frisch/Castagna/Benzaken on semantic subtyping, Tobin-Hochstadt/Felleisen on Typed Scheme and occurrence typing, Xi/Pfenning on Dependent ML, Van Horn/Might on AAM, Darais et al. on abstracting definitional interpreters, and Vouillon on semantic types. Those look like the highest-yield anchors for naming the space around Och. 

I can turn this into a sharper literature map next: “closest match,” “adjacent but different,” and “probably worth citing anyway.”


Can you try and red team the idea a little bit? What aspects of this project and this kind of structure of language could cause really fundamental problems for properties like soundness? Is it perhaps the decidability of the type system will always be undecidable? Which, you know, that might be acceptable because typical theorem provers, the type system is always Turing complete, so it's always going to be undecidable. But yeah, in what ways could you kind of red team this idea and think of where the main problems are? Because I need to address those first.

Yes. I think there are several ways to red-team it, and a few of them are quite fundamental.

The highest-level red-team question is:

are you building a type system, or are you building a semantic meta-interpreter whose good behavior you hope will induce a type system?

That sounds almost rhetorical, but it matters. A lot of the danger comes from the fact that Och’s “typing” is not just a lightweight syntax-directed judgment. It wants to inherit its meaning from evaluation-like behavior. That gives elegance and precision, but it also imports a lot of semantic hazards.

1. The biggest risk: self-reference between typing and evaluation
Your core idea has a very strong circular flavor:

types are terms

terms are interpreted semantically

typing is abstract interpretation

the abstract interpreter may need to evaluate terms to compute types

That immediately raises the risk of meta-circularity bugs:

the type of a term depends on evaluating a term

that evaluation may itself require typing intermediate terms

those typings may depend on evaluating more terms

If the boundaries are not extremely crisp, it becomes hard to prove even basic properties because the system is no longer stratified.

In ordinary STLC, there is a clean split:

syntax

typing judgment

operational semantics

In your setup, the split is intentionally blurred. That is the point, but it is also the main danger.

So one red-team question is:

what is the well-founded measure that stops “compute the type of this term” from recursively requiring “compute the type of this term” in a semantically stronger form?

If the answer is “none,” then proofs of soundness may become slippery very fast.

2. Terms-as-types may collapse distinction you secretly need
“The most precise type of a term is the term itself” is beautiful, but dangerous.

The problem is that type systems often rely on a distinction between:

a term as executable syntax

a type as a classification object

If you erase that distinction too aggressively, you may lose:

a clean notion of well-formed type

a stable notion of canonical forms

syntactic induction principles that proofs usually lean on

This can cause soundness pain in a very direct way:

if arbitrary executable terms are admissible as types,

then type equality / subtyping / type interpretation can inherit arbitrary computational behavior.

That does not automatically make the idea broken, but it does mean you need a very disciplined account of:

which terms may appear in type position

what counts as a well-formed type

whether those terms are normalized, abstracted, or only partially interpreted

Otherwise “types are terms” becomes too unconstrained to prove much about.

3. Undecidability is likely, but that may not be the deepest problem
Yes, decidability is a real concern, but I do not think it is the scariest one.

If abstract typing executes enough of the language, and the language is expressive enough, then:

type checking will likely be undecidable

subtyping may also become undecidable

equivalence of types may become undecidable

That alone is not fatal, as you said. Coq/Lean-style systems already live with a complicated story here, though they usually recover decidability of type checking via normalization restrictions, definitional equality design, universe discipline, etc.

The deeper problem is not “undecidable.”
The deeper problem is:

even if undecidability is acceptable, is the semantic relation well-behaved enough that the undecidable thing is at least mathematically clean?

For theorem provers, undecidable proof search is fine, but type checking itself is usually still very carefully controlled. If Och lets too much arbitrary computation leak into “what type is this?”, you may get a system that is not just undecidable, but hard to state coherently.

So yes: undecidability is plausible. But the more urgent issue is whether the system remains well-founded, compositional, and stratified enough to prove soundness.

4. Monotonicity may fail for deep reasons, not just proof noise
This is an especially important red-team angle since it already bit you.

Your intended monotonicity is roughly:

more approximate context in

more approximate conclusion out

That sounds natural for abstract interpretation.
But there are reasons it can fail fundamentally.

A. Stored syntax can become more informative under narrower environments
If types contain syntax that is later re-executed in a narrower context, then narrowing the environment can do more than just refine outputs — it can qualitatively change which computations succeed, how much they reveal, or which branches they take.

That means your abstract semantics is not just monotone in the ordinary lattice sense unless you are very careful.

This is especially dangerous if:

terms stored in the environment are reinterpreted later

their meaning depends on ambient environment, not a closed substitution

narrowing exposes new computation paths

That can break monotonicity in a very structural way.

B. Precision-sensitive constructs can be anti-monotone
Some operations become more defined when the input is more precise.
For example, branching, dependent elimination, or “read the right side of a pair by consulting the left” may reveal information only once the left is narrow enough.

That can be okay, but you need to ensure the result is still monotone in the approximation order. Sometimes these operations are only monotone if the abstract domain is designed exactly right.

So one red-team hypothesis is:

the core difficulty may not have been mutation at all; it may have been that your dependence mechanism is only conditionally monotone.

That is worth testing in Och.

5. Subtyping may become semantically elegant but proof-theoretically nasty
Set-theoretic / semantic-subtyping intuitions are appealing:

types are sets

subtyping is inclusion

But once the members of those sets include functions or higher-order objects, things get hard quickly.

Questions that become dangerous:

What exactly is the set denoted by a function term?

Is subtyping extensional or intensional?

Do two extensionally equivalent functions denote the same type?

How do you decide or reason about inclusion for higher-order semantic objects?

If your answer is too extensional, you can end up quantifying over behavior in ways that wreck tractability and proof structure.
If your answer is too intensional, you may lose the elegance of the semantic story.

This is one of the places where a project can feel conceptually right but become technically vicious.

6. Ascription / widening may hide unsoundness if they are too permissive
Your idea that type annotations “lose information” is elegant.
But red-teaming it:

when can you widen safely?

If widening is allowed too freely, you may lose the invariants needed for later eliminations.
If widening is too weak, the language becomes brittle.

The main risk is that widening and later re-specialization interact badly.
Especially dangerous pattern:

assign a wide type

later recover precision by context-sensitive elimination

accidentally regain information you should not have had

That would be a direct soundness hole.

So you want to ask:

is information loss irreversible except through logically valid narrowing?

can the system “hallucinate” precision after widening because of stored syntax or environment dependence?

That is a very plausible bug source.

7. Environment dependence may destroy compositionality
A conventional type system is compositional:

the type of a term depends on the types of subterms

Your setup risks becoming only partially compositional:

the abstract meaning of a term may depend on ambient environment in rich ways

later reinterpretation of embedded terms may inspect that environment again

That can make proofs extremely hard because local reasoning breaks down.

Red-team question:

can the type of a subterm be understood from the abstract meanings of its immediate parts, or does it depend on ambient global context in an essential way?

If it is the latter, you may still have a valid system, but the metatheory gets much nastier.

8. Dependency without normalization discipline is dangerous
Once types depend on terms, you usually need some story about normalization or at least stable computation.

If Och allows rich term computation in type position, then you need to know:

when does type-level computation stop?

when are two type-level computations considered equal?

when is the result stable under substitution / narrowing?

Without a disciplined answer, you can get:

undecidable convertibility

unstable subtyping

substitution lemmas that fail or become extremely hard

So yes, “type system undecidable” is a likely outcome.
But more urgently:

convertibility

normalization

stability under substitution

are probably the first semantic fault lines to inspect.

9. Function types may be the hardest place the idea breaks
I would heavily red-team functions.

Why? Because for functions, “the most precise type is the term itself” becomes much more explosive than for atoms or pairs.

A function type is not just data; it carries behavior.
If the type of a function is the function, then typing application may amount to semantic reasoning about that function’s behavior.

That raises several hard questions:

is function subtyping behavioral?

is application abstractly interpreted by applying abstract arguments to abstract functions?

how do closures interact with environment approximation?

does narrowing a closure environment narrow the function result monotonically?

My guess is: if the core idea breaks anywhere in pure Och, it is very likely to break first around higher-order functions.

10. Abstract interpretation may need widening/join machinery that changes the “type system” story
If you really lean into abstract interpretation, eventually you may need:

widening operators

joins that are not perfectly precise

finite approximants

fuel or bounded unfolding

At that point, the elegant story “typing = semantic approximation” may become messier:

the type system becomes analysis-parameterized

soundness depends on approximation design choices

principal types may disappear

different analyzers may give different typings

This may be acceptable, but it changes the philosophical character of the project.

Red-team question:

are you trying to define a canonical type system, or a family of sound analyses?

Those are different projects.

11. You may need stratification after all
A very plausible conclusion of red-teaming is:

the idea may only work if you reintroduce a small amount of stratification.

For example:

terms and types can be represented with the same syntax, but not all terms are admissible as types

abstract interpretation can evaluate type-level terms, but only closed or well-founded ones

higher-order dependence may be restricted

environments used for reinterpreting stored syntax may be filtered or frozen

That kind of stratification may feel like compromising the purity of the idea.
But often it is what turns a beautiful principle into a provable system.

12. There may be a tension between precision and subject reduction
A classic soundness route is:

progress

preservation

In your setting, preservation may be awkward because the system seems designed around changing precision as computation proceeds.

If abstract semantics and concrete semantics move at different granularity, you may need a preservation statement that is not ordinary “same type after step,” but something like:

concrete result remains within abstract approximation

abstract approximation evolves monotonically in sync with concrete execution

That is fine, but it means ordinary syntactic proof schemas may not fit well.

Red-team question:

is the right theorem really preservation, or is it simulation between concrete and abstract semantics?

If the latter, the whole proof architecture should probably be built around simulation, not conventional typing lemmas.

So what are the biggest likely fault lines?
If I had to prioritise the most dangerous ones:

1. Re-executing stored syntax under changed environments
This feels like a genuine candidate for fundamental trouble.

2. Higher-order functions under semantic subtyping / terms-as-types
This is where extensionality, undecidability, and monotonicity all collide.

3. Lack of stratification between executable terms and admissible types
This can make the system too unconstrained to prove much.

4. Conditional monotonicity of dependent elimination
Especially if precision unlocks computation.

5. Compositionality failure
If local reasoning does not hold, metatheory gets ugly fast.

What would I address first?
If I were ruthlessly red-teaming Och, I would first try to force answers to these questions:

What exactly is the approximation order?
On terms? On semantic denotations? On environments? On closures?

What is the admissible fragment of terms that may act as types?
Truly arbitrary terms, or a disciplined subset?

When a type contains syntax, is that syntax closed, closure-converted, or interpreted relative to ambient context?
This feels critical.

What is the core simulation theorem?
Not “preservation” in the usual sense, but the exact abstract-vs-concrete relation you want.

For higher-order functions, what notion of subtyping/equality are you using?
Intensional, extensional, approximate?

Can monotonicity already fail in the pure higher-order fragment?
This is probably the first thing to attack in Och.

My overall red-team verdict
I do not think the immediate threat is merely “type checking is undecidable.”
That is almost expected.

I think the real threats are:

the idea may be insufficiently stratified

monotonicity may fail because precision-sensitive reinterpretation is not actually monotone

higher-order semantic typing may be too extensional / context-sensitive to support clean proofs

the system may be more naturally a simulation-based abstract semantics than a conventional type system, and trouble comes from trying to treat it as the latter

That is where I would push hardest first.

The good news is that Och is exactly the right setting to stress-test those issues. If you can make the pure fragment work with a very crisp abstract/concrete simulation theorem and a monotonicity proof, that would be strong evidence the core idea is real. If it fails there, that is extremely informative too.


I wrote this email to my supervisors:

On 29 Jun 2024, at 10:33, Lidbury, Charlie A <charles.lidbury20@imperial.ac.uk> wrote:

Hello all,

In the interest of accuracy I thought I’d let you know that I’ve found a soundness bug:

Expression Subtyping Preservation (Prop. 5.2.9 on p67) doesn’t hold. It states that if M is a subtype of N under one environment, it’s also a subtype of N under all narrower environments. Counter example:

Not = (X: ’true | ‘false) -> match X { ‘true => ‘false, ‘false => ‘true };
F = (B: ‘true | ‘false) -> Not B: B; // this holds
B = ‘true; Not B: B; // does not hold, despite being under a narrower environment

Soundness relies on this and therefore the system presented isn’t sound, will fix it in Och, then bring the solution over.

Many thanks,
Charlie

Is that one of the suggestions for red teaming you had?

Thought for a few seconds
Yes — very much so.

That counterexample is basically an instance of the red-team concern I raised around monotonicity / subtyping preservation failing because narrowing the environment can change the meaning of type-level computation in a non-monotone way.

In your example:

under the wider environment, B : 'true | 'false

Not B : B holds

under the narrower environment, B : 'true

Not B : B fails

So narrowing the environment made the judgment go from true to false. That is exactly a failure of the kind of “always up and right” property you wanted.

More specifically, it matches two of the failure modes I mentioned:

Precision-sensitive computation can be anti-monotone
Not B becomes more precise when B is narrowed, but that precision change does not preserve the earlier subtyping judgment.

Stored / re-executed type-level computation under a narrower environment can change behavior qualitatively
the meaning of the type expression depends on the environment, and narrowing can invalidate a previously valid relation instead of refining it compatibly.

So yes, this is very much in-family with the red-team concerns.

What is especially useful about your counterexample is that it suggests the problem is probably not just proof noise from mutation/ownership. It looks like a more basic issue in the pure dependent/abstract-evaluation core. That strongly supports your decision to move to Och.

I’d phrase the lesson as:

Subtyping preservation under environment narrowing is not automatic in a system where type expressions compute from runtime information.

or even more sharply:

Type dependency can make judgments context-monotone in the wrong direction.

That is a very central thing to isolate in Och.

The deeper issue is that your proposition was implicitly assuming something like:

if a judgment holds at a coarse approximation,

it should continue to hold at finer approximations.

But your Not example shows that some judgments are only “accidentally true” because the coarse environment is imprecise enough to blur distinctions. Once the environment becomes more precise, the latent mismatch is exposed.

So the property that failed was not a random lemma — it was pointing at a real design tension:

precision reveals information

but revealed information can destroy earlier subtype relations

That means one of these probably has to change:

the notion of subtyping preservation

the interpretation of dependent function results

the environments under which type-level terms are re-evaluated

or the exact theorem statement you need for soundness

My guess is that the theorem you wanted was too strong. The right replacement may be something more simulation-like or one-sided, rather than “all narrower environments preserve the judgment.”

So: yes, your email example is absolutely one of the kinds of fundamental problems I had in mind. In fact it is a particularly clean instance of it.

The good news is that it is exactly the sort of bug Och is for: it tells you the core metatheory needs adjustment before ownership/mutation are even relevant.


I am going to be working on these things alot, can you update your memories accordingly so I can refer to things like Och and the properties I want and its broader context in Ochre

Updated saved memory
Thought for a couple of seconds
Done — I’ve stored that context.


would twelf https://twelf.org/ be useful for programatically stating these typing rules? I want a good way to express and iterate on them in an LLM-friendly way (verifyable)

other options involve using a full theorem prover like Lean or Agda

I’m checking the tradeoffs against the current official tooling/docs so I can give you a grounded recommendation, especially for the “LLM-friendly but verifiable” part.

Thought for 18s
Yes — Twelf could be useful, but I would treat it as a very specific tool, not the default winner.

My recommendation for your use case is:

Use Twelf if your near-term goal is to state and iterate on inference rules / judgments very directly.
Use Lean if your near-term goal is to prove metatheorems about those rules and have room to grow.
Use Agda if you want something closer to executable type theory / total programming, but I think it is less naturally aligned than Lean for this particular project.

Why I say that:

Twelf is explicitly aimed at specifying, implementing, and proving properties of deductive systems such as programming languages and logics, which is unusually close to what you want. Its surface syntax is also very judgment-oriented and compact, so encodings of typing relations often look much closer to “the paper version” than they do in a full theorem prover. The main downside is that the official Twelf site now says Twelf is no longer undergoing active development, even though it still has a user community and remains valuable for research. 

So for your criteria:

For expressing rules cleanly:
Twelf is very attractive. It is built for LF-style encodings of deductive systems, and that usually makes typing rules feel natural rather than engineered. 

For LLM-friendliness:
Twelf is mixed. On the plus side, the syntax is small, declarative, and rule-shaped, which is good for model iteration. On the minus side, because it is older and less actively developed, there is much less modern ecosystem energy, fewer examples in the current LLM training zeitgeist, and less tooling momentum than Lean. The official site’s “no longer undergoing active development” line matters here. 

For “verifiable”:
Twelf is verifiable in the sense that it is designed to encode and check deductive systems and metatheoretic properties. But if you expect a long research programme with lots of proof engineering, automation, refactoring, and extension, Lean is much stronger as a modern maintained proof assistant with a minimal trusted kernel, metaprogramming, and a big active ecosystem. 

For your specific Och/Ochre workflow:
I think the crux is this:

If you want to prototype judgments, relations, and small-step / typing presentations and quickly see whether the formulation is elegant, Twelf is a very good fit.

If you want to iterate with LLMs for months and then mechanize soundness / monotonicity / preservation-style or simulation-style theorems, Lean is probably the safer long-term home.

Agda is also a serious option, and its docs show the kind of features you would expect from a modern dependently typed environment: termination checking, positivity checking, reflection, rewriting, and even HTML/LaTeX generation tools. But for “formalizing a PL metatheory with lots of judgments and proofs,” I would still lean Lean over Agda unless you specifically want the Agda style. 

My practical advice would be:

Twelf for the metalanguage sketchpad.
Encode the core Och judgments there first if what you most need is a crisp, judgmental presentation.

Lean for the serious archive.
Once the judgments stop moving daily, port the stabilized fragment into Lean and do the durable metatheory there.

That gives you:

a pleasant rule-language early on

a modern, actively maintained prover later on

If you force me to pick just one tool today, with your emphasis on LLM-friendly iteration plus verification, I would pick Lean, not because it is the most elegant way to state the rules, but because it is the strongest all-around research substrate. Lean describes itself as an open-source programming language and proof assistant for correct, maintainable, formally verified code, emphasizes a minimal trusted kernel, and has strong extensibility and active use in verification projects. 

So the shortest honest answer is:

Twelf: excellent fit for rule-shaped encodings; weaker long-term bet.
Lean: less native-feeling for inference rules, but probably the best overall choice.
Agda: viable, but not my first pick for this project.

My strongest suggestion is to do one tiny Och fragment in both Twelf and Lean before committing. That comparison will be very revealing.


is there anything you would be better than twelf and/or lean?

I’m looking for anything that beats both specifically for “state typing rules cleanly, iterate quickly, and still get machine checking,” rather than just naming other provers.

Thought for 21s
Yes — depending on what you mean by “better.”

For your exact niche — “state typing rules cleanly, iterate fast, keep it LLM-friendly, and still have machine checking” — the most plausible things that could beat either Twelf or Lean are:

Best candidates
Beluga
This is the strongest “maybe better than both” candidate for your use case.

Why:

it is built on LF-style representations of syntax and inference rules, like Twelf-adjacent tooling

but it also has first-class support for Contextual LF, i.e. terms/types together with the contexts they live in, which feels highly relevant for mechanizing metatheory about judgments with binders and environments 

it is specifically positioned around specifying formal systems and proving properties about them in a way that is often more natural than encoding everything by hand in a general-purpose prover 

My take:

more natural than Lean for rule-heavy PL metatheory

more modern / better aligned to reasoning tasks than Twelf

but still less mainstream than Lean, so the ecosystem/LLM advantage is weaker

If you want a tool that feels like “Twelf, but more metatheory-oriented,” Beluga is the first one I’d try.

Abella
Abella is another serious contender.

Why:

it is explicitly for reasoning about relational specifications 

it supports higher-order syntax / binders via the λ-tree approach and gives you inductive and coinductive reasoning tools tailored to this style of formalization 

My take:

likely better than Lean if your object language is best expressed as a set of relations/judgments

likely better than Twelf if you want more direct theorem proving over those relations

not as broad or future-proof as Lean

This is especially attractive if Och ends up being most naturally presented as a collection of semantic/typing relations rather than as executable functions.

Ott + Lean / Rocq
Not a prover by itself, but very worth considering.

Why:

Ott is designed specifically for writing definitions of programming languages and calculi in readable ASCII close to informal mathematics 

it can generate output for theorem provers and LaTeX, so it’s good for keeping paper rules and mechanized rules aligned 

My take:

for expressing the rules, Ott may actually be better than both Twelf and Lean

for proving things, pair it with Lean or Rocq

This is probably the best answer if your real problem is:

“I need a pleasant source of truth for the rules, and I don’t want my paper notation and prover notation to drift.”

PLT Redex
This is not better for proofs, but it may be better for semantic experimentation.

Why:

Redex is a DSL for specifying reduction semantics with testing/tooling support 

it is excellent for quickly building and stress-testing semantics models

My take:

better than Twelf/Lean for rapid semantics prototyping

worse than both for theorems you want to trust as final metatheory

So if you want to discover counterexamples, test reduction rules, and iterate quickly, Redex is very compelling.

Less likely to beat Lean overall
Rocq (Coq)
Rocq is obviously very strong and mature for PL metatheory, and it is still a top-tier option for serious mechanization 

But for your stated goal, I don’t think it clearly beats Lean. It is more “another strong full prover” than “the thing that solves the Twelf-vs-Lean tension.”

My actual ranking for you
If the question is:

“What is best for stating rules elegantly?”
Ott

Beluga / Twelf

Lean

“What is best for proving metatheory durably?”
Lean

Rocq

Beluga / Abella

“What is best for this exact compromise?”
Beluga

Ott + Lean

Lean alone

Abella

Twelf

Bottom-line answer
The one thing I’d say may genuinely be better than both Twelf and Lean for your niche is:

Beluga, if your priority is clean representation of object-language judgments plus metatheory.

The one thing that may be better than both for authoring the rules themselves is:

Ott, but only when paired with a prover.

So my strongest practical recommendation is:

Beluga if you want one tool to try first beyond Twelf/Lean

Ott + Lean if you want the best “paper-friendly + prover-friendly” workflow

If you want, I can do a sharper side-by-side for Twelf vs Beluga vs Abella vs Lean vs Ott, specifically for an Och fragment with:

syntax with binders

subtyping judgments

abstract/concrete interpretation

monotonicity theorem shape.
