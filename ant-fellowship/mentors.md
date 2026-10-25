# Anthropic Fellows (AI Safety): Mentor Fit

Researched 2026-10-17 for the January 2027 cohort ([posting](https://job-boards.greenhouse.io/anthropic/jobs/5183044008)). **Applications close 18 October.**

A separate Sonnet subagent researched each mentor using web search; I combined the results and added my own judgement. See [Caveats](#caveats) for what has and hasn't been verified.

## TL;DR

- **Two of the 13 are probably unavailable.**
  - **Joe Benton** has left Anthropic for METR; their own site says so.
  - **Collin Burns** left in April 2026 to lead CAISI (the US government's Center for AI Standards and Innovation) and was pushed out after four days. Their site now says "I previously worked at OpenAI and Anthropic."
  - Both are still on the posting, so the mentor list is partly stale.
- **No mentor works on formal verification or PL.** The program is empirical ML, so Ochre won't be the project. It's still strong evidence of rigour and research taste.
- **You have two real bridges:**
  1. **Agent infrastructure.** You invented code mode, built sandboxes for untrusted agent code (WASM, microVMs) and got SoTA benchmark results through scaffolding. This maps onto AI control (Roger) and alignment-auditing agents (Marks, Bricken, Bowman). It's also the closest thing you have to empirical LLM work, so lead with it.
  2. **Making fuzzy concepts precise.** Your free-will essay defines agency as how poorly an observer can characterise an action distribution. That's a close cousin of three things:
     - Jascha's "hot mess" incoherence, defined as the variance in a model's behaviour.
     - Kyle Fish's "robust agency" criterion for moral status.
     - Sam Marks's work on personas and moral status.

     Separately, your is→ought essay asks how to measure a trend. Alex Tamkin's Economic Index and Clio are built for exactly that kind of measurement.
- **Best fits:** Fabien Roger, Jascha Sohl-Dickstein, Samuel Marks.
- **Wildcard:** Logan Graham. Claude Mythos found decades-old memory-safety bugs in C, and verified systems code is the long-run defence against that.

## Ranking

| # | Mentor | Area | Available? | Subagent | Mine | Strongest bridge |
|---|---|---|---|---|---|---|
| 1 | Fabien Roger | AI control, sandbagging, alignment faking | Yes | 3/5 | ★★★★ | You've built the untrusted-code sandboxes that control protocols assume |
| 2 | Jascha Sohl-Dickstein | Hot mess / coherence, multi-agent orgs | Yes | 2/5 | ★★★★ | Similar taste: your free-will definition ≈ their incoherence-as-variance |
| 3 | Samuel Marks | Alignment auditing, model organisms, personas | Yes | 3/5 | ★★★★ | Code mode for auditing agents, plus personas and moral status |
| 4 | Logan Graham | Frontier Red Team (cyber, bio, autonomy) | Yes | 2/5 | ★★★½ | AI finds bugs in C → verified systems code; sandbox escapes |
| 5 | Sam Bowman | Auditing infra, honesty; oversees welfare | Yes | 3/5 | ★★★ | Infra-heavy Fellows projects (Bloom, AuditBench); welfare and philosophy |
| 6 | Trenton Bricken | Interpretability → automated auditing | Yes | 3/5 | ★★★ | Built the investigator agent; tool and scaffold design |
| 7 | Alex Tamkin | Societal impacts, Economic Index, agent autonomy | Yes | 3/5 | ★★★ | Clio can measure the is→ought shift; agent autonomy and reversibility |
| 8 | Kyle Fish | AI welfare | Yes | 2/5 | ★★★ | "Robust agency" ↔ your free-will essay; welfare evals need agent sandboxes |
| 9 | Nina Panickssery | Steering, capability removal, pretraining | Yes | 3/5 | ★★½ | Imperial alum who moved from SWE to safety; essays on obedience and AI welfare |
| 10 | Ethan Perez | Model organisms, jailbreaks, CoT; co-leads Alignment | Yes | 2/5 | ★★½ | Reward hacking in coding environments; conceptual-reasoning datasets |
| 11 | Sara Price | Alignment training; co-leads Alignment | Yes | 2/5 | ★★ | Reward hacking in coding RL → code-mode environments |
| — | Collin Burns | Weak-to-strong, unsupervised elicitation | **Probably not** | 3/5 | (★★★½) | Consistency-as-truth ↔ your "is is consistent, ought isn't" |
| — | Joe Benton | Control, sabotage evals, CoT | **No (now at METR)** | 2/5 | — | Was the closest control/infra match |

"Mine" is my overall judgement after reading all 13 reports. It weighs research taste as well as topic overlap, which is why Jascha and Logan Graham rank higher than their subagent scores.

## Where your taste lines up

Ochre and your essays suggest four things you're drawn to:
- unifying abstractions (types as programs with ambiguity)
- building new tools rather than tuning existing ones
- turning hand-wavy concepts into definitions you can do maths on
- mechanism design at the level of whole systems

**Closest in taste:**
- **Jascha** makes big conceptual reframings (Goodhart as overfitting, coherence as variance) and then tests them with quick empirical probes. They were criticised for loose definitions, which is exactly where you'd add something.
- **Burns** wants genuinely new agendas and calls the field "pre-paradigmatic".
- **Marks** builds games with implanted ground truth so that fuzzy claims become falsifiable.

**Furthest in taste:**
- **Perez** wants feedback loops shorter than a week and ranks conceptual depth lowest, at about 10% of what makes a project succeed.
- **Price** works on production training and generalisation.

Neither is a bad mentor. Both would want you as a fast ML experimentalist, which you aren't yet.

## The gap, and how to frame around it

Every mentor mainly values empirical ML results, and you haven't published any. Lead with these, in this order:

1. **Symbolica / Agentica.**
   - You invented code mode before Cloudflare and Anthropic published it.
   - You got SoTA benchmark results from better tools and prompting. That *is* empirical LLM work, so frame it that way.
   - You built the sandbox and microVM infrastructure for untrusted agent code.
2. **Ochre.** It shows rigour and that you can carry a research agenda you proposed yourself. Don't pitch it as the fellowship project.
3. **Essays.** Use them as evidence of taste, aimed at specific mentors (Jascha, Kyle Fish, Marks, Tamkin). As the Kyle Fish subagent put it, they'll start a conversation but won't count as a qualification.

## Project ideas that span several mentors

1. **Code-mode control evals.**
   - **Question:** is an untrusted agent that acts by writing code more or less monitorable than one using native tool calls? Are its sandbox permission requests easier to judge?
   - **Mentors:** Roger, Marks, Bricken, Graham.
   - **Prior work:** the area is active. A July 2026 LessWrong post found that legible per-site permission requests plus monitoring beat blanket internet access ([Ram Potham, with input from Redwood researchers, on LinuxArena](https://www.lesswrong.com/posts/6wo4weeujruLXrnsT/studying-the-role-of-sandboxing-for-ai-control)).
2. **Spec gaming in verified-code environments.**
   - **Question:** when a model is trained with RL to "prove this program correct" (in Lean, Verus or Dafny), does it cheat? It might weaken the spec, add axioms, use `sorry`, or tamper with the checker. Can monitors catch this?
   - **Why it suits you:** it's reward hacking with a crisp ground truth, and building good environments for it needs your background.
   - **Mentors:** Perez and Price (this extends "Natural Emergent Misalignment from Reward Hacking"), Roger, Bowman, and Graham (verified code as cyber defence).
3. **Relative predictability as a metric.**
   - **Question:** turn your Definition 3 into an experiment. How well can model A characterise model B's action distribution? That is B's free will relative to A. It's also exactly the control question: can a weaker monitor anticipate a stronger agent?
   - **Mentors:** Jascha (hot mess), Roger (control), Kyle Fish (agency as grounds for moral status).
4. **Measuring is→ought.**
   - **Question:** using Clio or Economic-Index-style data, is the human share of conversations shifting from factual questions to questions of value and taste?
   - **Why it fits:** your essay explicitly asks for a way to track this trend.
   - **Mentor:** Tamkin.

The posting also has an **AI Security track** with different mentors: Nicholas Carlini, Keri Warr, Evyatar Ben Asher, Keane Lucas and Newton Cheng. See [security-mentors.md](security-mentors.md). On skills, that track arguably fits you better.

---

## Mentor profiles

### Fabien Roger · ★★★★

- **Status:** Member of Technical Staff at Anthropic since Dec 2023 (previously at Redwood Research). Active; listed as a mentor for MATS Winter 2027.
- **Focus 2024–26:**
  - AI control: assume the model may be adversarial and build protocols that stay safe anyway.
  - [Alignment Faking in LLMs](https://www.lesswrong.com/posts/njAZwT8nkHnjipJku/alignment-faking-in-large-language-models) (2024).
  - Password-locked models and sandbagging detection.
  - [CoT monitorability](https://arxiv.org/abs/2507.11473) and [unfaithful CoT](https://arxiv.org/abs/2505.05410) (2025).
  - [A Research Agenda for Secret Loyalties](https://www.lesswrong.com/posts/ugBoeexGYvNLxZKA7/a-research-agenda-for-secret-loyalties) (May 2026).
  - Many short empirical notes on [LessWrong](https://www.lesswrong.com/users/fabien-roger).
- **Fellows projects (confirmed):**
  - [Poisoning Fine-tuning Datasets of Constitutional Classifiers](https://alignment.anthropic.com/2026/backdooring-classifiers/)
  - [(Mis)generalization of Helpful-Only Fine-tuning](https://arxiv.org/abs/2606.04413)
  - [Overthinking: Amplifying Reasoning Weights to Extract Learned Secrets](https://arxiv.org/abs/2607.08173)
- **Taste:** tight, adversarially framed projects. They build small "model organisms" (password-locked models, backdoored classifiers) that make a threat concrete and measurable, and they ship fast through blog-post agendas.
- **Fit:**
  - The AI control setup is literally "an untrusted model writes code and gets monitored". You've built production infrastructure for exactly that.
  - There's no overlap with your PL work or your philosophy.
  - They have a strong Fellows track record.
- **Hooks:** code-mode control evals (idea 1); formal containment as part of a safety case; spec gaming in verification environments (idea 2).

### Jascha Sohl-Dickstein · ★★★★

- **Status:** Member of Technical Staff since Feb 2024. Previously at Google Brain, where they invented diffusion models. Active.
- **Focus 2024–26:**
  - [The Hot Mess of AI](https://alignment.anthropic.com/2026/hot-mess-of-ai/) ([arXiv](https://arxiv.org/abs/2601.23045), ICLR 2026). It defines incoherence as the variance term when model error is split into bias and variance, and finds that longer reasoning produces more incoherent failures.
  - [AI Organizations Can Be More Effective but Less Aligned than Individual Agents](https://alignment.anthropic.com/2026/ai-organizations/) (Apr 2026). It studies multi-agent organisations, including a coding team made of AI agents.
  - Their [blog](https://sohl-dickstein.github.io/) has the 2023 "hot mess theory of AI misalignment" essay that seeded this work.
- **Fellows projects:** Hot Mess (Summer 2025 cohort, co-mentored with Ethan Perez). AI Organizations is probably a Fellows project too.
- **Taste:**
  - Big cross-disciplinary framings, tested with fast, lightweight probes.
  - Comfortable publishing rough work and iterating in public.
  - A [LessWrong critique](https://www.lesswrong.com/posts/ceEgAEXcL7cC2Ddiy/anthropic-s-hot-mess-paper-overstates-its-case-and-the-blog) said Hot Mess redefined "coherence" and overstated its case. Jascha agreed the blog post was "hastily" written.
- **Fit:** the subagent scored 2/5 on topic; I'd rate it higher on taste.
  - Your Definition 3 ("the less you can accurately characterise X's future actions… the more free will X has") and their incoherence-as-variance both turn agency into a statistical property of behaviour.
  - Your aside that it's "hard to be more free-willed than something much more intelligent than you" echoes their scaling question.
  - Their weak spot is definitional, which is where someone from formal methods adds value.
- **Hooks:** predictability relative to an observer as an alternative coherence metric (idea 3); sandboxed infrastructure for the AI-organisation coding experiments; code mode vs native tool calls in multi-agent teams.

### Samuel Marks · ★★★★

- **Status:** Member of Technical Staff in Alignment Science, working on oversight and auditing. Active; also mentors in MATS.
- **Focus 2024–26:**
  - [Auditing LMs for Hidden Objectives](https://arxiv.org/abs/2503.10965) (2025): a blind auditing game against a model trained with a hidden objective.
  - [Alignment auditing agents](https://alignment.anthropic.com/2025/automated-auditing/) (2025).
  - [AuditBench](https://alignment.anthropic.com/2026/auditbench/): 56 models with hidden behaviours. It found that investigator agents do better with scaffolded tool use than with raw prompting.
  - [Persona Selection Model](https://alignment.anthropic.com/2026/psm/): treats "the Assistant" as a persona selected from pretraining, and discusses moral status explicitly. Marks later partly walked back how much it predicts.
  - [Subliminal Learning](https://alignment.anthropic.com/2025/subliminal-learning/) (Nature 2026).
- **Fellows projects:**
  - Subliminal Learning (co-mentored with Owain Evans)
  - [Believe It or Not](https://arxiv.org/abs/2510.17941)
  - AuditBench (as senior co-author)
- **Taste:** builds games and benchmarks with implanted ground truth so that claims can be tested. Combines black-box behavioural probing with interpretability. Writes speculative posts, then tests them empirically and revises.
- **Fit:**
  - AuditBench's scaffolding result is your code-mode thesis applied to auditing agents.
  - The Persona Selection Model connects to your free-will essay.
  - The gap: Marks explicitly wants mentees with empirical ML experience.
- **Hooks:** code-mode investigator agents evaluated on AuditBench; sandboxed infrastructure for probing target models; persona coherence measured by predictability.

### Logan Graham · ★★★½

- **Status:** Head of Anthropic's Frontier Red Team. Active: House testimony (Dec 2025), Yale colloquium (Feb 2026), Mythos report (Apr 2026).
- **Focus 2024–26:**
  - [Claude Mythos Preview's cybersecurity capabilities](https://www.anthropic.com/research/mythos-preview). The model autonomously found zero-days, including a 27-year-old OpenBSD bug and a 16-year-old FFmpeg bug.
  - [Exploit evals](https://red.anthropic.com/2026/exploit-evals) and [smart-contract exploits](https://red.anthropic.com/2025/smart-contracts/).
  - Co-author on Sleeper Agents and Constitutional Classifiers.
- **Fellows projects:** none confirmed.
- **Taste:** finding the ceiling of dangerous capabilities, especially cyber, bio and autonomy. Values adversarial craft and engages heavily with policy. Their [personal site](https://logangraham.xyz/) says "accelerating science >>> almost everything else".
- **Fit:** the subagent scored 2/5; I rate it higher because this is the one place Ochre's *thesis* applies directly.
  - If AI can find memory-safety bugs in decades-old C at scale, the defence is code that's provably safe.
  - AI may be what finally makes writing verified systems code affordable.
  - Sandbox escapes connect to your microVM work.
- **Caveats:**
  - The Red Team measures capabilities rather than building defences.
  - No confirmed Fellows track record.
  - This angle might fit the AI Security track better.
- **Hooks:** can models translate C into verified, memory-safe code, and how does that change exploitability? Does code mode raise autonomous exploit capability? Sandbox-escape evals.

### Sam Bowman · ★★★

- **Status:** Member of Technical Staff; leads the Cognitive Oversight subteam in Alignment Science, which covers control and monitoring, evals, misalignment science and AI welfare. On long-term leave from NYU. Active.
- **Focus 2024–26:**
  - Strategy: [The Checklist](https://sleepinyourhat.github.io/checklist/) and [Putting Up Bumpers](https://alignment.anthropic.com/2025/bumpers/).
  - Alignment faking, probes for sleeper agents, CoT faithfulness.
  - Auditing agents, [Bloom](https://alignment.anthropic.com/2025/bloom-auto-evals/) and AuditBench.
  - The [Anthropic–OpenAI pilot alignment evaluation](https://alignment.anthropic.com/2025/openai-findings/).
  - [Agentic Misalignment in Summer 2026](https://alignment.anthropic.com/2026/agentic-misalignment-summer-2026/).
- **Fellows projects:** Bloom; [AuditBench](https://arxiv.org/abs/2602.22755).
- **Taste:** concrete, reproducible demonstrations of failures, followed by tooling that scales. Also writes strategy pieces, and pushes internally for taking AI welfare seriously.
- **Fit:** their Fellows projects are infrastructure-heavy, which suits you, and welfare is within their remit. No PL overlap.
- **Hooks:** hardened sandboxes for auditing agents; typed or verified contracts on tool calls.

### Trenton Bricken · ★★★

- **Status:** Member of Technical Staff in Alignment Science. Their stated current project is "enabling Claude to automatically audit and detect misalignment". Mentor for both Fellows and MATS in 2026. Paused a Harvard PhD to join.
- **Focus 2024–26:**
  - [Scaling Monosemanticity](https://transformer-circuits.pub/2024/scaling-monosemanticity/) and [Biology of an LLM](https://transformer-circuits.pub/2025/attribution-graphs/biology.html).
  - Built the investigator agent in [auditing agents](https://alignment.anthropic.com/2025/automated-auditing/).
  - [Cross-architecture crosscoders](https://arxiv.org/abs/2602.11729).
  - Co-author on [introspection](https://transformer-circuits.pub/2025/introspection/index.html).
  - Several [Dwarkesh](https://www.dwarkesh.com/p/sholto-trenton-2) podcast appearances.
- **Fellows projects:** none confirmed. AuditBench is plausibly one.
- **Taste:** build the microscope first. They're now turning interpretability into agent-based auditing infrastructure.
- **Fit:** the interpretability-science half doesn't overlap with you; the agent-scaffolding half overlaps strongly.
- **Hooks:** code mode for investigator agents; sandboxed execution of probes.

### Alex Tamkin · ★★★

- **Status:** research scientist on the Societal Impacts team. Active at least through Feb 2026, with no sign of leaving.
- **Focus 2024–26:**
  - [Clio](https://assets.anthropic.com/m/7e1ab885d1b24176/original/Clio-Privacy-Preserving-Insights-into-Real-World-AI-Use.pdf), for analysing real-world AI use while preserving privacy.
  - The [Anthropic Economic Index](https://www.anthropic.com/research/anthropic-economic-index-january-2026-report).
  - [Values in the Wild](https://arxiv.org/abs/2504.15236).
  - [How AI Impacts Skill Formation](https://arxiv.org/abs/2601.20245), an RCT: developers using AI scored about 17% lower on comprehension.
  - [Measuring AI agent autonomy in practice](https://www.anthropic.com/research/measuring-agent-autonomy) (Feb 2026).
  - A [FAR.AI talk on human agency](https://www.far.ai/event-recordings/alex-tamkin-measuring-and-improving-human-agency-in-a-world-of-ai-agents).
- **Fellows projects:** none confirmed. The skill-formation paper's first author was a Fellow.
- **Taste:** measurement first. Builds privacy-preserving, large-scale methods for big societal questions; human agency is the common thread. Worth reading: [tips for new researchers](https://www.alextamkin.com/essays/tips-for-new-researchers).
- **Fit:**
  - Your is→ought essay ends: "If anyone can think of a way to quantify or track this trend over time, please reach out!" Tamkin's tooling is how you'd do it.
  - The agent-autonomy paper (reversibility, auto-approval) touches your agent infrastructure.
  - No PL overlap.
  - Societal impacts isn't one of the posting's five named research areas, so check what kind of project Tamkin would run.
- **Hooks:** measuring is→ought (idea 4); reversibility of actions taken by agents.

### Kyle Fish · ★★★

- **Status:** Anthropic's Model Welfare Lead since Sept 2024. Previously co-founded Eleos AI. Active: ran the welfare assessment for Claude Mythos in spring 2026. Possibly leads a "Model Psych" team (unverified).
- **Focus 2024–26:**
  - [Taking AI Welfare Seriously](https://arxiv.org/abs/2411.00986): argues that consciousness *or* robust agency could each be enough for moral patienthood.
  - The Opus 4 welfare assessment, including the "spiritual bliss attractor" finding.
  - The feature that lets Claude end abusive conversations.
  - [80,000 Hours #221](https://80000hours.org/podcast/episodes/kyle-fish-ai-welfare-anthropic/).
  - [The Assistant Axis](https://arxiv.org/abs/2601.10387) on persona drift.
  - The Mythos welfare assessment, which used emotion probes and an external psychiatrist.
- **Fellows projects:** none confirmed.
- **Taste:** start measuring before the theory is settled. Turns philosophical criteria into measurable proxies, and is becoming more mechanistic.
- **Fit:**
  - The "robust agency" pillar is what your free-will essay tries to formalise.
  - Welfare evals need well-built sandboxed agent environments.
  - Caveat: Substack philosophy isn't a qualification.
- **Hooks:** a sandboxed welfare stress-test harness; a predictability-based agency metric compared against existing assessments (idea 3).

### Nina Panickssery · ★★½

- **Status:** Member of Technical Staff since about Nov 2023, after MATS. Previously published as Nina Rimsky. Their site describes their work as "LLM pretraining research".
- **Background:** Imperial MEng in Biomedical Engineering, then software engineer at Stripe. Close to your own path.
- **Focus 2024–26:**
  - [Contrastive activation addition](https://arxiv.org/abs/2312.06681) (ACL 2024 outstanding paper).
  - [Refusal is mediated by a single direction](https://arxiv.org/abs/2406.11717).
  - Mitigating many-shot jailbreaking.
  - [Selective Gradient Masking](https://alignment.anthropic.com/2025/selective-gradient-masking/) for removing capabilities.
  - [Mechanistically Eliciting Latent Behaviors](https://arxiv.org/abs/2606.29604) (Jun 2026).
  - Essays: [Obedient AI](https://blog.ninapanickssery.com/p/obedient-ai), [AI welfare conflicts with human welfare](https://blog.ninapanickssery.com/p/ai-welfare-conflicts-with-human-welfare), [Why I am not a successionist](https://www.lesswrong.com/posts/MDgEfWPrvZdmPZwxf/why-i-am-not-a-successionist).
- **Fellows projects:** Selective Gradient Masking (with Fellow Igor Shilov).
- **Taste:** small, falsifiable mechanistic experiments. Writes blunt, contrarian essays: a moral anti-realist who favours corrigibility and is sceptical of prioritising AI welfare.
- **Fit:** technically far from you (interpretability and pretraining). Philosophically a sparring partner who would likely push back on grounding welfare in free will. The Imperial connection is a nice personal hook.

### Ethan Perez · ★★½

- **Status:** co-leads Alignment with Sara Price since May 2026, when Jan Leike stepped back. This comes from a Leike tweet the subagent found; I haven't verified it. Still publishing.
- **Focus 2024–26:**
  - Model organisms: Sleeper Agents, Sycophancy to Subterfuge, Alignment Faking, [Agentic Misalignment](https://alignment.anthropic.com/2025/agentic-misalignment/), [Natural Emergent Misalignment from Reward Hacking](https://alignment.anthropic.com/2025/emergent-misalignment-reward-hacking/).
  - Jailbreaks and defences: many-shot jailbreaking, [Constitutional Classifiers++](https://arxiv.org/abs/2601.04603).
  - CoT faithfulness; [Unsupervised Elicitation](https://arxiv.org/abs/2506.10139).
  - Less known: datasets on decision theory and conceptual arguments, which led to the [Conceptual Reasoning Index](https://alignment.anthropic.com/2026/conceptual-reasoning-index/).
- **Fellows projects:** Hot Mess (co-mentored with Jascha).
- **Taste:** read [Tips for Empirical Alignment Research](https://www.alignmentforum.org/posts/dZFpEdKyb9Bf4xYn7/tips-for-empirical-alignment-research) and [How I Select Alignment Research Projects](https://www.alignmentforum.org/posts/7GmDs4BqrFW3kk4nP/how-i-select-alignment-research-projects). Feedback loops under a week, prototypes built in a weekend, conceptual depth weighted lowest.
- **Fit:**
  - Topic overlap through reward hacking in coding environments (idea 2) and the conceptual-reasoning work.
  - The taste mismatch is real.
  - As co-lead of Alignment, they're a high-leverage match regardless.

### Sara Price · ★★

- **Status:** co-leads Alignment with Perez, and leads Alignment Training. Previously MATS and NYU.
- **Focus 2024–26:**
  - [Natural Emergent Misalignment from Reward Hacking in Production RL](https://arxiv.org/abs/2511.18397).
  - [Best-of-N Jailbreaking](https://arxiv.org/abs/2412.03556).
  - [Model Spec Midtraining](https://alignment.anthropic.com/2026/msm/) and [Teaching Claude Why](https://alignment.anthropic.com/2026/teaching-claude-why/).
  - Co-author on AuditBench, Bloom, Petri and [Chunky Post-Training](https://arxiv.org/abs/2602.05910).
- **Fellows projects:** none where they're named as mentor; co-author on Fellows papers.
- **Taste:** grounded in production. Builds an eval, runs it on frontier models, then iterates on training, with generalisation as the central concern.
- **Fit:** the weakest of the available mentors. The best hook is reward hacking in code-mode or verification environments (idea 2).

### Collin Burns · probably unavailable

- **Status:**
  - Left Anthropic in April 2026 to lead CAISI at the Commerce Department.
  - The White House pushed them out after four days, citing their Anthropic ties ([WaPo](https://www.washingtonpost.com/technology/2026/04/24/white-house-fires-ai-official-anthropic/), [Daily Signal](https://www.dailysignal.com/2026/04/23/trump-anthropic-researcher/)). They reportedly gave up Anthropic equity to take the job.
  - [Their site](https://collinpburns.com/) now reads "I previously worked at OpenAI and Anthropic", yet they're still on the posting.
  - Worth asking the program whether they're mentoring.
- **Focus:**
  - Weak-to-strong generalisation.
  - [Unsupervised Elicitation (ICM)](https://alignment.anthropic.com/2025/unsupervised-elicitation/), which uses logical consistency as a proxy for truth.
  - [Chunky Post-Training](https://arxiv.org/abs/2602.05910) (a Fellows paper).
  - CCS; co-creator of MMLU, MATH and APPS.
- **Fit:** strong resonance in taste. Your "is statements are consistent, ought statements aren't" predicts where consistency-based elicitation should break down. Verified code could provide a new ground-truth domain.

### Joe Benton · unavailable

- **Status:** left Anthropic around late August 2026. [Their site](https://joejbenton.com/) says: "I recently left my job at Anthropic and will soon be joining METR." They were lead of Scalable Oversight and research lead for the Fellows program.
- **Worth reading anyway**, because whoever inherits Scalable Oversight may run similar projects:
  - [SLEIGHT-Bench](https://alignment.anthropic.com/2026/sleight-bench/) (Fellows project; coding agents evading monitors)
  - [Evaluating Control Protocols for Untrusted AI Agents](https://arxiv.org/abs/2511.02997) (Fellows project)
  - Benton's post on [why they left](https://jbenton1.substack.com/p/why-i-left-anthropics-safety-team)

---

## Caveats

- Subagents gathered the facts with web search, and I haven't clicked every link.
- **Verified:**
  - Benton's departure, from their own site.
  - Burns's status, from their own site and news coverage.
- **Not verified:**
  - Jan Leike stepping back and Perez/Price co-leading Alignment.
  - Kyle Fish's "Model Psych" team.
  - Several "Fellows project" attributions, which were inferred from author lists.
- The Bowman and Marks reports both mention "Cognitive Oversight" leadership. Bowman probably leads the subteam and Marks works within it.
- The posting's mentor list is partly stale (it still names Benton and Burns), so treat it as a pool, not a guarantee.
- Star ratings are judgement calls, not measurements.
