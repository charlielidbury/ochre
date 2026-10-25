# Anthropic Fellows (AI Security): Mentor Fit

Researched 2026-10-17 for the January 2027 cohort ([posting](https://job-boards.greenhouse.io/anthropic/jobs/5183044008)). **Applications close 18 October.** This is the companion to [mentors.md](mentors.md), which covers the AI Safety track.

A separate Sonnet subagent researched each mentor using web search; I combined the results and added my own judgement. See [Caveats](#caveats).

## TL;DR

- **All five mentors appear to be active at Anthropic.**
  - Four of them (Carlini, Cheng, Lucas, Ben Asher) work on one theme: Claude finding and exploiting real vulnerabilities in systems code (Firefox, V8, Windows kernel, Ghostscript, OpenSC).
  - The fifth, Keri Warr, works on defensive infrastructure: verifying inference and catching model-weight exfiltration.
- **On skills, this track probably suits you better than the safety track.**
  - Ochre's thesis is "make memory-safe, verified systems code practical". That's the natural defence against everything these mentors keep demonstrating.
  - Your Symbolica sandboxes are exactly the kind of isolation layer these mentors run Claude inside, and the kind they'd want to see broken.
  - Two mentors explicitly lean toward formal methods or verification: Ben Asher's listed interests are "Program Analysis, Formal Methods", and Warr is "searching for differentially defense-favored security tools".
- **The gap is just as sharp.** The posting's signals for this track are CVEs, bug bounties, pentesting, security-adjacent open source and empirical ML, and you have none of them. Your case rests on systems and verification depth plus infrastructure you actually built, not on offensive tradecraft.
- **Best fits:** Keri Warr and Nicholas Carlini, then Evyatar Ben Asher.

## Ranking

| # | Mentor | Area | Fellows record | Subagent | Mine | Strongest bridge |
|---|---|---|---|---|---|---|
| 1 | Keri Warr | Infrastructure security lead: inference verification, weight exfiltration | MATS (confirmed); Fellows not confirmed | 3/5 | ★★★★ | Verification-first, defence-favoured taste; SWE → security path; you built an inference gateway and sandboxes |
| 2 | Nicholas Carlini | LLM-found 0-days, model extraction, adversarial ML | **Confirmed** (smart-contract exploits) | 4/5 | ★★★★ | LLMs find C memory-safety bugs → verified patches / Ochre thesis; "good taste in problems" |
| 3 | Evyatar Ben Asher | Frontier Red Team: exploit development, browser bugs | None found | 3/5 | ★★★½ | Interests include formal methods; Claude's Firefox Wasm/JIT type-confusion exploit vs your WASM sandbox |
| 4 | Keane Lucas | Frontier Red Team: exploit benchmarks, autonomous red-teaming | None found | 3/5 | ★★★ | ExploitBench "sandbox primitive" rungs; binaries and compilers; agent harnesses |
| 5 | Newton Cheng | Frontier Red Team cyber lead; Project Glasswing | Posting lists track projects, but none tied to Cheng | 3/5 | ★★★ | Your microVM/WASM sandboxes are what their team stress-tests; verification as defence |

**Why I rank Warr first:**
- Warr's projects depend least on exploit tradecraft, which is where you're weakest.
- Their method is to model an attack as a security game with provable bounds, build a practical detector, then ship it open source. That's the closest in taste to how you work.

**Why Carlini is a close second:** they have the strongest Fellows track record and the most direct link to Ochre. The trade-off is that their recent work is offence-first.

## Where your taste lines up

- **Keri Warr:** formalises attacks as games, proves bounds, ships defensive tools. Of all 18 mentors across both tracks, this is the closest to "Ochre, but for AI infrastructure".
- **Nicholas Carlini:**
  - Look for places where the field is "obviously" doing something wrong.
  - Kill weak projects fast.
  - Prefer minimal scaffolding (roughly a 10-line script and Docker) over elaborate harnesses.

  Their [research-ideas logfile](https://nicholas.carlini.com/writing/2024/my-research-logfile.html) and [How to Win a Best Paper Award](https://nicholas.carlini.com/writing/2026/how-to-win-a-best-paper-award.html) are worth reading before an interview.
- **Ben Asher:** thinks about bugs structurally (program analysis, formal methods) while doing hands-on exploit work.
- **Lucas and Cheng:** build benchmarks against real software and validate results rigorously. They're closer to empirical capability measurement than to building defences.

## The gap, and how to frame around it

1. **Lead with the sandboxes.** You built secure Python execution on WebAssembly and a multi-tenant microVM platform for *untrusted LLM-generated code*. That is security engineering. If you found or fixed any isolation bugs while hardening them, say so concretely: that's the nearest thing you have to vulnerability research.
2. **Ochre as the defensive thesis.** Every one of these mentors has published on AI making memory-corruption exploits cheap. "I'm building the language that makes those bug classes provably impossible in performance-critical code" is a coherent reason to join this track.
3. **Systems depth:** an OS kernel (Pintos: virtual memory, races), an optimising compiler, an ARM emulator, and Citadel's C++ market-data library with property-based testing.

## Project ideas

1. **Verified patches for LLM-found bugs.**
   - **Question:** when Claude finds a memory-safety bug and proposes a fix, how often is the fix incomplete? Can the model produce a machine-checked proof that the whole bug class is gone (in Verus, Lean, or an Ochre-like subset)?
   - **Mentors:** Carlini, Lucas, Cheng.
2. **Can Claude escape the sandbox it runs in?**
   - **Question:** use exploit-dev agents to red-team WASM and microVM sandboxes for agent code execution, including code-mode harnesses.
   - **Mentors:** Ben Asher, Cheng, Lucas (ExploitBench's sandbox rungs), Warr.
   - **Safety track link:** this also fits AI control, so Fabien Roger and Logan Graham.
3. **Agent sandboxes as an exfiltration channel.**
   - **Question:** extend Warr's work on inference verification and exfiltration detection to code-execution environments, which are a second way for weights or secrets to leave.
   - **Mentor:** Warr.
4. **Soundness bugs in the verifiers.**
   - **Question:** if AI-written proofs become a defence, the proof checker, type checker or borrow checker becomes the trusted base. Can LLMs find soundness bugs in Lean, Verus, Dafny or rustc's borrow checker?
   - **Mentors:** Carlini, Lucas, Ben Asher (who lists formal methods as an interest).
   - **Safety track link:** this pairs with idea 2 in mentors.md (spec gaming in verified-code environments).
5. **Do memory-safe rewrites actually close the exploit paths?**
   - **Question:** take components with exploits Claude has already written, rewrite them in Rust or verify them, then rerun the exploit agents.
   - **Mentors:** Lucas, Carlini.

## Safety vs security: which to aim for?

The posting covers both workstreams, with project selection and mentor matching happening afterwards. If the application lets you state a preference, my read is:

- **Security** fits your **skills and Ochre** best. Warr and Carlini are as strong a match as anyone on the safety list.
- **Safety** fits your **philosophy and agent-infrastructure** work best (Roger, Jascha, Marks).
- **Ideas that bridge both tracks:**
  - Sandbox escape and control: Roger, Graham, Ben Asher, Cheng.
  - Spec gaming, or soundness bugs in verifiers: Perez, Price, Carlini, Lucas.
  - Naming one of these keeps you matchable to mentors on either track.

---

## Mentor profiles

### Keri Warr · ★★★★

- **Status:** Technical Lead of Anthropic's Infrastructure Security Engineering team since 2024.
  - **Remit:** building toward SL4/SL5 security, including confidential computing, supply-chain security, ML cluster security and defence against weight exfiltration.
  - Active: listed on the posting and as a MATS Autumn 2026 mentor.
  - **Background:** about 11 years as a generalist software engineer (Stripe, Faire); University of Waterloo. [Site](https://keri.warr.ca/), [GitHub](https://github.com/keriwarr).
- **Focus 2024–26:**
  - [Verifying LLM Inference to Prevent Model Weight Exfiltration](https://arxiv.org/abs/2511.02620) (Nov 2025). Models steganographic exfiltration from inference servers as a security game. Their estimators push economically feasible exfiltration of a 1TB model from about 1 day to 200+ days.
  - [DiFR: Inference Verification Despite Nondeterminism](https://arxiv.org/abs/2511.20621). Checks inference outputs against a trusted reference despite GPU nondeterminism, and detects 4-bit quantisation with AUC > 0.999. Has a [vLLM integration](https://github.com/adamkarvonen/difr).
  - "Anytime-valid detection of LLM weight exfiltration" (Oct 2026, NeurIPS E-Values workshop oral). Uses sequential testing for continuous monitoring.
  - "Haiku to Opus in Just 10 bits" (Feb 2026, with Carlini). Compression gains from LLMs.
- **Fellows projects:** MATS mentee papers confirmed (DiFR, exfiltration verification). No Fellows-tagged paper confirmed.
- **Taste:** formalise the attack, prove bounds, build a practical estimator, validate on real models (up to 30B parameters), measure false positives and the attacker's cost multiplier, then ship it. Their bio says "searching for differentially defense-favored security tools". Not much public opinion writing.
- **Fit:**
  - Their whole agenda is verification as defence for AI infrastructure.
  - Your infrastructure work (sandboxes, an inference gateway wired to billing) is the same kind of system.
  - Their non-research engineering background resembles yours.
  - **Gaps:** steganographic channels and e-processes are new to you, and code mode doesn't feature in their work.
- **Hooks:** treat sandboxes as an exfiltration vector (idea 3); use ownership or type-level reasoning to rule out covert channels in inference-serving code; red-team code-mode agents against their detectors.

### Nicholas Carlini · ★★★★

- **Status:** Research Scientist at Anthropic since March 2025, after Google DeepMind/Brain. Active: lead author on a Feb 2026 paper, MATS Summer 2026 mentor, policy work for Anthropic in June 2026. [Site](https://nicholas.carlini.com/), [papers](https://nicholas.carlini.com/papers).
- **Focus 2024–26:**
  - [Evaluating and mitigating the growing risk of LLM-discovered 0-days](https://www.anthropic.com/research/zero-days) (Feb 2026, co-first author with Keane Lucas). Claude Opus 4.6 found 500+ validated vulnerabilities in Ghostscript, OpenSC, CGIF and Firefox by reasoning about code rather than fuzzing.
  - Model extraction:
    - *Stealing Part of a Production Language Model* (ICML'24 best paper)
    - Polynomial-time cryptanalytic extraction of neural networks (EuroCrypt'25 best paper)
  - Extracting training data and prompts, adversarial prompt generation, persistent pre-training poisoning, and how durable safeguards are on open-weight models.
  - Terminal-Bench (ICLR'26).
  - A talk, "Black-hat LLMs" (2026): 0-day-finding capability is doubling roughly every four months. Also a podcast, [AI Finds Vulns You Can't](https://securitycryptographywhatever.com/2026/03/25/ai-bug-finding/).
- **Fellows projects (confirmed):** [AI agents find $4.6M in blockchain smart contract exploits](https://www.anthropic.com/research/smart-contracts) (Dec 2025, Fellows Winnie Xiao and Cole Killian, co-mentored with Alwin Peng). It introduced SCONE-bench.
- **Taste:** good taste in problems above everything else; keeps a running ideas file; maximum rigour; minimal scaffolding; committed to open publication. See [How I Use "AI"](https://nicholas.carlini.com/writing/2024/how-i-use-ai.html) and [career update](https://nicholas.carlini.com/writing/2025/career-update.html).
- **Fit:**
  - Their signature work right now (agents finding memory-safety and logic bugs in C) sits directly on your systems background and Ochre's thesis.
  - Your orientation is defensive and proof-based, while theirs is offence-first.
  - The sandbox infrastructure is the isolation layer this kind of research needs.
  - **Gap:** no CVEs or published security research.
- **Hooks:** verified patches (idea 1); soundness bugs in verifiers (idea 4); a SCONE-bench-style benchmark for compilers or systems code.

### Evyatar Ben Asher · ★★★½

- **Status:** Frontier Red Team, working on offensive security and capability evaluation. Active; most recent public work dated March 2026.
- **Focus 2024–26:**
  - Co-author of [Reverse engineering Claude's CVE-2026-2796 exploit](https://www.anthropic.com/research/exploit) (Mar 2026). Claude Opus 4.6 built a working Firefox exploit for a type confusion at the JIT/WebAssembly boundary, after about 350 attempts. It's described as the first full browser exploit written by a model "with minimal hand-holding".
  - Credited on around 28 Firefox CVEs found with Claude in Feb–Mar 2026 ([VulnCheck](https://www.vulncheck.com/blog/anthropic-glasswing-cves)).
  - Probably involved in Project Glasswing and the [open-source vulnerability-scanning service](https://www.anthropic.com/research/launching-opt-in-vuln-finding-service-for-open-source) (Oct 2026); byline not confirmed.
  - Their [HuggingFace](https://huggingface.co/basher) and [GitHub](https://github.com/kingloko) profiles list "Program Analysis, Formal Methods, Code Generation". Forked repos (angr, Ghidra, how2heap, pwntools) suggest a classic binary-exploitation and CTF background.
- **Fellows projects:** none found.
- **Taste:** little public signal because posts are bylined to the team. What's visible: exploit-first work on real targets with real CVEs, then a detailed technical write-up. The program-analysis and formal-methods interests suggest they think about bugs structurally.
- **Fit:**
  - The only mentor on either list who names formal methods as an interest.
  - The exploit they wrote up crosses the WebAssembly boundary, which is the same technology your sandbox was built on.
  - **Gap:** exploit development is their day job and it isn't yours. They also have no Fellows track record.
- **Hooks:**
  - Red-team your own kind of sandbox (idea 2).
  - Could ownership or dependent-type checking rule out the JIT/Wasm type-confusion bug classes Claude exploits?
  - Soundness bugs in verifiers (idea 4).

### Keane Lucas · ★★★

- **Status:** Member of Technical Staff on the Frontier Red Team since July 2024. Active.
  - **Education:** PhD from CMU (2024, advised by Lujo Bauer).
  - **Earlier roles:** USAF captain; stints at Google with Carlini, MIT Lincoln Lab, and the Air Force Red Team. [Site](https://keanelucas.com).
- **Focus 2024–26:**
  - [Measuring LLMs' ability to develop exploits](https://www.anthropic.com/research/exploit-evals) (May 2026). Introduces ExploitBench (a 16-rung capability ladder over 41 V8 CVEs, including sandbox rungs) and ExploitGym (898 targets). Claude Mythos Preview reached arbitrary code execution on 21 of the 41.
  - [Measuring LLMs' impact on N-day exploits](https://www.anthropic.com/research/n-days) (Jun 2026). Turning Firefox and Windows-kernel patches into working exploits within hours.
  - The 0-days paper (co-first author with Carlini).
  - The CVE-2026-2796 write-up.
  - The [Mozilla partnership](https://www.anthropic.com/news/mozilla-firefox-security).
  - [Incalmo](https://arxiv.org/abs/2501.16466) (IEEE S&P 2026): an LLM plans and agents execute red-team attacks across multi-host networks.
  - A DEF CON 33 talk, [Claude — Climbing a CTF Scoreboard Near You](https://keanelucas.com/talks/2025-08-09-claude-climbing-a-ctf-scoreboard-near-you).
  - **Before Anthropic:** binary rewriting to evade ML malware detectors (Malware Makeover), and critiques of how randomised defences are evaluated.
- **Fellows projects:** none found. The subagent's search budget ran out, so this isn't exhaustive.
- **Taste:** builds new benchmarks against real artefacts (shipped V8, live CTFs, real contract funds) and tests end to end. Cares about rigorous evaluation because sloppy setups hide the true picture.
- **Fit:**
  - Binaries, compilers and JIT miscompilation are all close to your compiler work.
  - The ExploitBench sandbox rungs connect to your sandboxes, and Incalmo is an agent-harness problem.
  - **Gap:** heavily offensive, with no Fellows record.
- **Hooks:** do memory-safe rewrites close the exploit paths (idea 5); soundness bugs in compilers or checkers (idea 4); formally grounded sandbox infrastructure for the exploit evals.

### Newton Cheng · ★★★

- **Status:** leads cyber on the Frontier Red Team. Physics PhD (UC Berkeley, quantum information); BS from Stanford. Active, and the public face of [Project Glasswing](https://www.anthropic.com/glasswing) (Apr 2026). Glasswing is a defensive partnership with AWS, Apple, Google, Microsoft, Mozilla and 50+ other organisations, built around Claude Mythos Preview, which wasn't released generally because of its offensive capability.
- **Focus 2024–26:**
  - **Earlier safety work:** Sleeper Agents and CoT faithfulness papers (2023–24).
  - **Cyber:**
    - [0-days](https://www.anthropic.com/research/zero-days) (Feb 2026)
    - [N-days](https://www.anthropic.com/research/n-days) (Jun 2026)
    - [Glasswing initial update](https://www.anthropic.com/research/glasswing-initial-update)
    - A near-weekly stream of Frontier Red Team posts, such as the [GLM-5.3 cyber analysis](https://www.anthropic.com/research/glm-5-3-and-the-spread-of-advanced-cyber-capabilities) and [ECDSA curve origins](https://www.anthropic.com/research/ecdsa-curve-origins).
- **Fellows projects:** the posting lists past security-track projects (smart-contract exploits; "Strengthening Red Teams: A Modular Scaffold for Control Evaluations"), but none is tied to Cheng specifically.
- **Taste:** minimal scaffolding with maximal validation: give Claude a sandbox and ordinary tools, then spend human effort confirming results. Prefers realistic, high-stakes targets over toy CTFs. Openly worried that capabilities are outpacing defences.
- **Fit:**
  - Your sandboxes are the defensive mirror of what their team tests.
  - Verification as defence is a story this team would recognise.
  - As team lead they may have less hands-on mentoring time. That's my guess, not a finding.
- **Hooks:** lightweight ownership or type analysis to triage which Claude-found bugs are real memory-safety issues; red-team sandbox boundaries (idea 2); does code mode change time-to-exploit?

---

## Caveats

- Facts come from Sonnet subagents using web search. Four reports independently agree on the main shared papers (0-days, N-days, the CVE-2026-2796 write-up, Glasswing).
- **Not verified:**
  - Ben Asher's earlier career and their exact count of CVE credits.
  - Warr's Oct 2026 workshop paper.
  - Whether Warr mentored any Anthropic Fellows (as opposed to MATS) projects.
- The Keane Lucas subagent ran out of search budget partway through, so its "no Fellows projects" finding is weaker than the others.
- Star ratings are judgement calls.
