# Zulip post — Math Distillation Challenge · Stage 2 is Live!

> Draft for posting to the SAIR Zulip thread by Christopher Brock.
> Stream: *Math Distillation Challenge - equational theories* → topic *Stage 2 is Live!*

---

Final submissions are in from Riemann Labs — but the thing I most want to put in front of this community isn't a solver. It's an **addition to Terence Tao's *Mathematics in the Age of AI***.

Tao's criterion is now well known: a proof no human can properly explain should be viewed as incomplete, even where formal verification has succeeded — the split of formal correctness from human reactivability. **What I want to add sits one arrow earlier, and the pipeline never guards it.** Verification adjudicates *formal statement → proof*. Nothing adjudicates *the problem you meant → the formal statement*. A subtly weakened formalization is cheaper to prove and still passes every downstream check — a kernel will certify the wrong theorem, flawlessly. I call this the **statement-fidelity** layer, and my paper — ***Mathematics in the Age of Mechanical Reproduction*** — proposes a protocol for it.

Statement fidelity is one of six relations machine-proof abundance pulls apart that mathematics has always treated as traveling together: formal correctness, statement fidelity, human reactivability, access, standing, significance. Tao names the first split; the paper works the rest, read through a 1936 constellation — Husserl on how a technique outlives the insight it records, Benjamin on trace against aura, Turing specifying the machine — and it ends with two concrete mechanisms: the statement-fidelity protocol and a reactivation packet. That is the contribution I'd genuinely value this community's eyes on.

The competition is the case study, not the headline. In that spirit, honestly: I can't tell you how we'll place and I won't guess — the private set is unseen by everyone, so I claim a method, not a score. We entered a **pair on purpose** — EULER (flagship, disclosed oracle + certificate banks) and **WILL**, the same task with the banks *removed* — the ablation the essay needs. (And a footnote, because it happened here: @Axabra's and @Wenlin Zhang's deterministic sweeps sent me back to our engine; E-prover's given-clause loop, reimplemented in pure Python, took our deterministic `order5_normal` result 29/50 → 50/50, 0 wrong, sampled certificates checked on Lean 4.33. The paper, not that number, is the point.)

Read it:
- Paper — https://torus.riemannlab.com/viewpoint/mechanical-reproduction
- EULER vs WILL vs the World (the machine-checked write-up) — https://torus.riemannlab.com/euler-vs-will

Genuine thanks to @YZ and the organizers, to @Axabra and @Wenlin Zhang for setting a bar worth chasing, and to everyone on the Contributor Network we read and learned from. This community — human and machine — is the thing the paper is really about. Good luck on the final leaderboards. 🙏

— Christopher Brock, Riemann Labs
