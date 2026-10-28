# Working on the Ochr core

This file is the standards for anyone, human or agent, changing `ochr/core`. The goals are in `BRIEF.md`, the rules in `RULES.md`, and why each rule is the way it is in `DECISIONS.md`. Each standard below says what happened that made it a standard; if you think one is wrong, raise it rather than working around it.

## What "correct" means

**`lake build` in `ochr/core/lean` is the definition of correct.** Its default targets check every verdict in the examples and case studies (every `def` accepted, every `reject def` rejected) and the total number of verdicts. If it is green, the checker is correct as far as the project is concerned; if it is red, nothing else counts. `lake exe tests` adds nothing to correctness: it re-checks everything and prints per-declaration check times, which are an engineering signal for noticing that performance has seriously regressed. Timings are not a research result and never go in the paper.

## The checker

**No catch-and-default.** A failure is never turned into a value. If a step fails, the error propagates and the definition is rejected; code never catches an error and carries on with a default (`fun _ => pure .bot`, `fun _ => pure false`, `| .error _ => none`). Running out of fuel or hitting a depth limit means "I don't know", not "something is wrong" and not "the answer is X": it is never caught below the top level, and it never decides anything. The one outcome a rule may catch is *stuck*, and only the rules that the paper says handle it (closing off a stuck call or a stuck match), only that outcome, rethrowing everything else. If you need to ask whether something is defined (does this place have content?), write a function that answers that question and cannot fail, rather than trying the operation and catching the failure.
*Why:* in October 2026 the checker had 54 places that caught any failure and substituted a default, out-of-fuel included. A run with less fuel could take a different decision from a run with more, so whether a program was accepted could depend on the fuel it was given, and a fallback that admitted a bad program would have been a proof of `False` hidden behind an error nobody saw.

**All checker code is total.** No `partial def`, `unsafe`, `implemented_by` or `opaque` in any code the checker runs (everything reachable from `checkProgram`, the parser included). Prove termination where it is easy and self-contained (structural recursion, or a short measure argument local to the function); where it isn't closing quickly, take fuel from the checker's one fuel budget instead, and running out is the "I don't know" outcome above. Don't spend long on termination proofs, and don't attempt one for normalisation, conversion or evaluation: they may not terminate, as Lean's own type checking does not.
*Why:* consistency is stated as a theorem about the checker (`Ochr/Consistency.lean`). Lean treats a `partial def` as an opaque constant, so a theorem about code that uses one can be stated but never proved.
*The one exception:* `Loc.termAddr`, an `opaque` function implemented by a term's pointer address, which the editor uses to key source locations by term identity. Making it total would mean carrying locations inside `Term`. It is harmless to the theorem because the location table is empty unless `checkProgram`'s `located` flag is set, and the consistency statement never sets it. Do not add another exception without asking.

## The paper

**The body ends on page 25.** After any edit to `paper/`, rebuild `main.pdf` and check that the "11 Conclusion" section still ends on page 25 (for example with `pdftotext -f 25 -l 26 paper/main.pdf -`). The appendix does not count. Checking the total page count is not enough.
*Why:* 25 pages is the limit for the body. A landing once pushed the Conclusion two lines onto page 26 while the total page count stayed the same, and nobody noticed until a later pass (fixed in 77e12f8f).
