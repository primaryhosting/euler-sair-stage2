# Zulip post — Math Distillation Challenge · Stage 2 is Live!

> Draft for posting to the SAIR Zulip thread by Christopher Brock.
> Stream: *Math Distillation Challenge - equational theories* → topic *Stage 2 is Live!*

---

Final submissions in from Riemann Labs — and a thank-you, because the last few days on this thread changed how our solver works.

**The turn.** Reading @Axabra's and @Wenlin Zhang's clean deterministic sweeps — 200/200 with *zero LLM*, guided superposition, and the two stubborn order-5 residuals cracked "by improving the proof-search architecture rather than adding brute force" — sent us back to our own true-side engine. Ours was a bounded mini-Twee doing blind critical-pair saturation: on the order-5 projection/collapse laws it would spin out to 4,000+ facts and find nothing. The fix wasn't a bigger data bank; it was the one architectural idea your posts pointed at — **E-prover's given-clause loop**, reimplemented in pure Python: process the lightest derived equation first, with an age-weight ratio so no useful lemma starves.

Reordered that way, the same search reaches the projection lemma in **~40 facts** instead of drowning in thousands. On the public `stage2_stress_test` `order5_normal` category, our **deterministic** result (no LLM, no cert bank) went from **29/50 → 50/50, 0 wrong**, closing the two residuals (E19040→E17478 total collapse; E6543→E29450 left-projection) and every other undecided true case at runtime. Sampled true certificates checked 9/9 on Lean 4.33; false witnesses re-checked exhaustively in Python.

Two things I want to be honest about, in the spirit of the tie-break discussion here:

1. This is the **public** stress set. The private evaluation is what matters, and none of us can see it — so I'm claiming a *method that generalizes*, not a score.
2. We submitted a **pair on purpose**: EULER (the flagship, which still carries a disclosed ETP-direction oracle + dev-time certificate banks for released rows) and **WILL** — the same task with the oracle, the banks, and every borrowed proof *removed*. WILL is the ablation the paper needs: strip away the sediment and whatever still proves is technique. The given-clause loop is pure technique, so it went into WILL too — it now proves the projection laws with no table at all.

Full write-up, verified certificates, and the essay this all sits inside — *Mathematics in the Age of Mechanical Reproduction* — are here:

- **EULER vs WILL vs the World** — https://torus.riemannlab.com/euler-vs-will
- **Paper (PDF)** — https://torus.riemannlab.com/viewpoint/mechanical-reproduction

Genuine thanks to @YZ and the organizers for the stress sets and the fast judge; to @Axabra and @Wenlin Zhang for setting a bar worth chasing; and to everyone on the Contributor Network we read and learned from. Good luck on the final leaderboards. 🙏

— Christopher Brock, Riemann Labs
