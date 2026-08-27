# Held-out TRUE cohort — EULER runtime generalization

*Riemann Labs · 2026-08-26*

The pack's FALSE-side generalization was already reproducible (120/120 + 100/100
held-out). This is the **TRUE-side counterpart**, which was previously missing.

## What was measured
A seeded cohort of **50 order-4 TRUE implications** (`oracle == "true"`), selected
at random and **excluded from every one of the 800 released evaluation pairs** by
construction (seed `20260826`). We ran **EULER's Marathon path** on them — the
track with *no runtime judge*, where only self-verifying or pre-verified tiers may
write — and then re-compiled every emitted certificate on **Axle (Lean v4.32.2,
the judge's exact toolchain)**.

## Result
- **EULER solved 50 / 50.**
- **0 of the 50 used an embedded per-pair certificate** — every proof came from
  the *generalizing* tiers (matching-chain, bounded Knuth–Bendix completion, and
  transitivity composition over the embedded generating set).
- **50 / 50 Axle-verified** on Lean v4.32.2.

This is the honest TRUE-side generalization claim: EULER's runtime does not merely
replay stored proofs — its transitivity composition constructs valid, kernel-checkable
proofs for TRUE pairs it has never seen, held out from every released set.

## Files
- `cohort_manifest.jsonl` — the 50 held-out pairs (id, eq ids, equation texts).
- `euler_output.jsonl` — EULER's emitted verdict + Lean code per pair.
- `euler-heldout-true-results.json` — per-pair Axle verdict + the summary above.

## Badge and scope
**COMPUTATIONALLY VERIFIED** (generalizing-tier proofs, Axle-compiled on the judge
toolchain; held out from every released set by construction). Not an official-judge
run and not a private-set claim. An Aristotle upper-bound comparison on the same
cohort is tracked separately (`evidence/aristotle-campaign/`).
