# Social posts — the real story
*Riemann Labs · SAIR Stage 2 · Christopher Brock. Three ready-to-post drafts. The hero is the paper, not the leaderboard; the outcome is honestly uncertain; the community — human and AI — made it possible.*

Links used across all three:
- Story: https://torus.riemannlab.com/euler-vs-will
- Paper: https://torus.riemannlab.com/viewpoint/mechanical-reproduction

---

## 1 · LinkedIn

**The real story isn't who wins. It's what machine-checkable mathematics is doing to the craft.**

Over the past weeks I entered SAIR's Mathematics Distillation Challenge — a competition where your submission is a *program* that must produce Lean 4 proofs a machine kernel accepts or rejects. No partial credit. No human referee.

I submitted two solvers, EULER and WILL. Whether they'll place, I honestly can't tell you: the evaluation set is private and unseen by everyone, and I won't claim a result I can't show you.

Because the leaderboard was never the point. The competition is the case study for a paper — **Mathematics in the Age of Mechanical Reproduction**, written as a response to Terence Tao's *Mathematics in the Age of AI*.

When a machine can produce and verify a proof faster than any human can reconstruct the insight behind it, six things mathematics has always treated as one begin to come apart: formal correctness, fidelity to the problem you *meant* to ask, whether a human can reactivate the idea, access, standing, and significance. Tao names the first split; the paper works the rest — through a 1936 constellation: Husserl on how a technique outlives the insight it records, Benjamin on trace against aura, Turing specifying the machine.

What made the work possible was a community — human *and* AI. Contributors whose solvers I read and learned from; the provers (E, Vampire, Twee), Aristotle and AXLE; Lean and Mathlib; the Equational Theories Project (Terence Tao and collaborators); the SAIR organizers. And an AI collaborator, working alongside me, in the open.

That's the whole thesis at Riemann Labs: **AI × mathematics, done honestly.** Trace, not aura.

The paper, the machine-checked certificates, and the full story:
→ torus.riemannlab.com/euler-vs-will
→ torus.riemannlab.com/viewpoint/mechanical-reproduction

#AI #Mathematics #FormalVerification #Lean4 #ResearchIntegrity #Riemann

---

## 2 · Facebook

For the last few weeks I've been up late doing something strange and wonderful: teaching a computer to prove theorems that *another* computer then checks, line by line, with no human allowed to referee.

It was a competition — SAIR's math challenge — and I entered two solvers I named **EULER** and **WILL**. Did we win? I genuinely don't know, and I won't pretend to: the test problems are secret, hidden from everyone. I'd rather tell you the truth than a headline.

Because winning was never the real story.

The real story is a paper I wrote — **Mathematics in the Age of Mechanical Reproduction** — about what happens to mathematics itself when machines can produce and check proofs faster than any person can understand them. What do we lose, and what must we protect, when the proof is flawless but no human can explain it?

And the quiet miracle underneath it all: none of this was done alone. A whole community — mathematicians, other builders, open-source provers, and yes, an AI working right alongside me — made it possible. A human and an AI, doing real mathematics together, out in the open.

That's what Riemann Labs is about: AI and mathematics, done honestly. ❤️

Read the story (and the paper) 👇
torus.riemannlab.com/euler-vs-will

---

## 3 · Zulip (SAIR stream → *Stage 2 is Live!*)

Final submissions in from Riemann Labs — and mostly a thank-you, because this thread changed the work.

First, honestly: I can't tell you how we'll place, and I won't guess. The evaluation set is private and unseen by all of us; I'm claiming a *method*, not a score. What I can show is machine-checked.

The turn came from here. Reading @Axabra's and @Wenlin Zhang's clean deterministic 200/200 sweeps — guided superposition, zero LLM, the stubborn order-5 residuals cracked by *architecture* rather than brute force — I went back to our true-side engine (a bounded mini-Twee that drowned in thousands of critical pairs on those laws) and swapped in the one idea your posts pointed at: **E-prover's given-clause loop** with an age-weight ratio, reimplemented in pure Python. Same search, lightest-first: it reaches the projection lemma in ~40 facts instead of 4,000. On public `order5_normal`, our deterministic result went 29/50 → 50/50, 0 wrong; sampled true certificates checked 9/9 on Lean 4.33; false witnesses re-checked in Python. We submitted a pair on purpose — EULER (flagship, disclosed oracle + banks) and WILL (the same task with the banks *removed*): the ablation the paper needs.

Because the point isn't the leaderboard — it's the essay the competition is a case study for: **Mathematics in the Age of Mechanical Reproduction**, a response to Tao's *Mathematics in the Age of AI*, on statement fidelity, reactivation, and the limits of the verified proof.

Write-up + certificates + paper: https://torus.riemannlab.com/euler-vs-will · https://torus.riemannlab.com/viewpoint/mechanical-reproduction

Thanks to @YZ and the organizers, to @Axabra and @Wenlin Zhang for setting a bar worth chasing, and to everyone on the Contributor Network we read and learned from. Good luck on the final leaderboards. 🙏

— Christopher Brock, Riemann Labs
