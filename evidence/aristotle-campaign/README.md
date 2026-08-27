# Aristotle campaign — three questions a frontier prover answered

*Riemann Labs · Harmonic's Aristotle · submitted & harvested 2026-08-26*

Three jobs run on Harmonic's Aristotle (Lean prover), each Axle-re-verified on the
judge's exact Lean 4.32.2. Files below are the returned proofs.

## A — Held-out TRUE upper bound  (`heldout-true-aristotle.lean`)
On the same 50 held-out TRUE pairs (excluded from every released set) that EULER's
runtime solved 50/50 with its generalizing tiers: **Aristotle also proved 50/50.**
→ EULER's runtime *matches a frontier prover* on held-out TRUE generalization.

## B — The two open FALSE holes  (`false-hole-countermodels.lean`)  ✅ both closed
- **1167 ⊭ 1763** — infinite countermodel on ℤ, `x ◇ w = (-w if 0≤x else 1-w)`.
  Aristotle also *proved it must be infinite*: any finite magma satisfying eq1167
  forces eq1763, so no finite witness exists.
- **2531 ⊭ 4307** — finite countermodel on ZMod 13, `x ◇ y = 7x + 7y` (order 13).
  A finite model does exist; our search had merely capped below order 13.
Both verified on Lean 4.32.2. No unresolved public FALSE hole remains.

## C — Sediment upper bound  (`will-unsolved-aristotle.lean`)
Of the 16 released TRUE pairs WILL's technique-only tiers could **not** solve,
**Aristotle proved 16/16** (all verified on 4.32.2). So the 34/50 → 50/50 gap is
entirely "provable but beyond distilled technique" — the sediment, made a number.

## Honest scope
Aristotle is a dev-time contributor; these results are computationally / judge-
toolchain verified, not an official-organizer run, and not a private-set claim.
