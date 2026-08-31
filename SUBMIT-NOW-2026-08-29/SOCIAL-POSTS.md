# Social posts — the addition to Tao
*Riemann Labs · Christopher Brock. Three drafts. The lead is the intellectual contribution — the unguarded problem→statement arrow (statement fidelity), an addition to Tao's* Mathematics in the Age of AI. *The SAIR competition is the case study, secondary. Honest on the uncertain outcome; the community — human and AI — made it possible.*

Links used across all three:
- Paper: https://torus.riemannlab.com/viewpoint/mechanical-reproduction
- Case study / write-up: https://torus.riemannlab.com/euler-vs-will

---

## 1 · LinkedIn

**Machine verification can certify the wrong theorem — flawlessly. Closing that gap is what my new paper adds to Terence Tao's *Mathematics in the Age of AI*.**

An AI allowed to quietly let *a, b, c* be zero can produce a *formally certified* proof that Fermat's Last Theorem is **false**. The kernel accepts it. Every downstream review passes. Nothing is wrong with the proof — the machine simply proved a subtly different statement than the one we meant to ask.

Tao maps a pipeline in which every arrow is guarded: verification for correctness, exposition for legibility, refereeing for acceptance. **My paper — *Mathematics in the Age of Mechanical Reproduction* — is an addition to his: the *first* arrow is guarded by nothing.** Formal verification adjudicates *statement → proof*; it is silent on *problem → statement*. It's the most Goodhart-exposed point in mathematics — a subtly weakened statement is cheaper to prove and passes every check. I name that the **statement-fidelity** layer and give it a stage and a protocol.

It's one of six things machine-proof abundance pulls apart that our field has always treated as one: correctness, statement fidelity, human reactivability, access, standing, significance. I read the split through a 1936 constellation — Husserl on how a technique outlives the insight it records, Benjamin on trace against aura, Turing specifying the machine.

I tested the argument against a real case: SAIR's Mathematics Distillation Challenge, judged by a deterministic Lean kernel with no human referee. Whether my two solvers place, I honestly can't say — the evaluation set is private and unseen by everyone, and I claim no result I can't show. The competition is the case study; the paper is the point. And none of it was done alone — a whole community, human and AI, made it possible.

→ torus.riemannlab.com/viewpoint/mechanical-reproduction
→ torus.riemannlab.com/euler-vs-will

#AI #Mathematics #FormalVerification #Lean4 #ResearchIntegrity

---

## 2 · Facebook

Here's something that should give anyone excited about AI and math a pause:

An AI, allowed to quietly assume the numbers can be zero, can produce a *formally certified* proof that Fermat's Last Theorem is false. The computer checks it. It passes every review. Nothing is "wrong" with the proof — the machine just proved a subtly different statement than the one we meant to ask.

That gap is what my new paper is about — **Mathematics in the Age of Mechanical Reproduction**, written as an addition to Terence Tao's *Mathematics in the Age of AI*. Tao describes a pipeline where every step is checked. I point at the one step nobody checks: the translation from the real problem into the formal statement the machine actually proves. When proofs become cheap to produce, that unguarded step is exactly where things quietly go wrong — and it's only one of several things we're about to lose track of.

I put the idea to the test in a real competition — SAIR's math challenge, judged entirely by machine. Did we win? I honestly don't know: the test set is secret, hidden from everyone, and I won't pretend to a result I can't show. The competition was the case study. The paper is the point. And none of it happened alone: a whole community — people, and an AI working right alongside me — made it possible.

Read it 👇
torus.riemannlab.com/viewpoint/mechanical-reproduction

---

## 3 · Zulip (SAIR stream → *Stage 2 is Live!*)

Final submissions are in from Riemann Labs — but the thing I most want in front of this community isn't a solver. It's an **addition to Terence Tao's *Mathematics in the Age of AI***.

Tao's pipeline guards every arrow — verification, exposition, refereeing, canonicalization. **The first arrow is unguarded.** Verification adjudicates *formal statement → proof*; nothing adjudicates *the problem you meant → the formal statement*. It's the most Goodhart-exposed point in the structure: a subtly weakened statement is cheaper to prove and passes every downstream check. (Tao and Klowden's own example: an AI permitted to let *a, b, c* be zero can formally certify that Fermat's Last Theorem is false.) My paper — ***Mathematics in the Age of Mechanical Reproduction*** — names that the statement-fidelity layer, sets it beside five other relations machine-proof abundance pulls apart (correctness, fidelity, reactivability, access, standing, significance), reads them through a 1936 constellation (Husserl, Benjamin, Turing), and proposes a statement-fidelity protocol and a reactivation packet. That's the contribution I'd value your eyes on.

The competition is the case study, not the headline. Honestly: I can't tell you how we'll place and won't guess — the private set is unseen by everyone; I claim a method, not a score. We entered a **pair on purpose** — EULER (flagship, disclosed oracle + banks) and **WILL**, the same task with the banks removed — the ablation the essay needs. (Footnote, because it happened here: @Axabra's and @Wenlin Zhang's deterministic sweeps sent me back to our engine; E-prover's given-clause loop reimplemented in pure Python took our deterministic `order5_normal` result 29/50 → 50/50, 0 wrong, certificates checked on Lean 4.33. The paper, not that number, is the point.)

- Paper — https://torus.riemannlab.com/viewpoint/mechanical-reproduction
- EULER vs WILL vs the World — https://torus.riemannlab.com/euler-vs-will

Genuine thanks to @YZ and the organizers, to @Axabra and @Wenlin Zhang for setting a bar worth chasing, and to everyone on the Contributor Network we read and learned from. This community — human and machine — is the thing the paper is really about. Good luck on the final leaderboards. 🙏

— Christopher Brock, Riemann Labs
