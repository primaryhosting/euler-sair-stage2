# How we built it

*Riemann Labs · SAIR Stage 2 (Equational Theories) · 2026-08-26*

Two solvers, one task: decide `E1 ⊨ E2` over magmas and emit a certificate the
open Lean judge accepts. **EULER** carries the field's accumulated knowledge;
**WILL** carries none of it. The point of building both is to measure how much of
a "solve" is knowledge and how much is technique.

## The task and the trusted base
- FALSE: exhibit a finite magma satisfying `E1`, violating `E2`; the judge
  re-decides with `decideFin!`. TRUE: a Lean 4 term of the goal type, kernel-checked
  under Lean **v4.32.2** (commit `f3b06c705…`), axioms ⊆ `{propext, Quot.sound,
  Classical.choice}`, no `sorry`/metaprogramming/unsafe.
- Sandbox: `python:3.11-slim`, 2 vCPU / 2 GB, no network, one `solver.py` ≤ 500 KB,
  3600 s/problem. Same file serves Solo (stdin/stdout) and Marathon (JSONL manifest).

## EULER — the refusal stack (precomputed knowledge)
1. **Direction oracle** — the ETP order-4 implication closure as a 4,694² bitmatrix
   (byte-identical to public `outcomes.json`), read in O(1). Selects a branch only;
   never a submitted answer's validity.
2. **FALSE** — a 305-table hypothesis-keyed finite-model bank + a stdlib CSP model
   finder + a proof-supported infinite parity tier.
3. **TRUE** — a certificate table (26 hand-derived + 390 Aristotle-proved + 18
   ATP/loop), a matching-chain prover, bounded Knuth–Bendix completion with total
   emission, transitivity composition, ATP replay.
4. **The rule** — no answer counts unless the judge accepts it; deterministic tiers
   additionally self-check before emitting.

## WILL — technique without the table
Same six ideas, every deposit removed: no oracle, no banks, no borrowed
certificates. A parser + finite evaluator, a bounded countermodel search, chain
and collapse provers, and a single embedded prompt (schemas of *moves*, no worked
answers). It is expected to score below EULER; the gap is the measurement.

## Dev-time instruments (named, not shipped — none runs at runtime)
- **ETP (Tao et al.)** — public implication closure and equation catalog.
- **Aristotle (Harmonic)** — Lean prover; produced 390 of EULER's hard TRUE proofs.
  Embedded as literal Lean bodies, re-verified by the judge at answer time.
- **Axle (Axiom — Carina Hong's team)** — judge-exact Lean v4.32.2 compile-check in
  ~2 s; every embedded certificate passed through it; both disclosed statement-fidelity
  failures surfaced as Axle divergences.
- **Mace4 / E / Vampire** — classical countermodel and proof search whose *outputs*
  (not the tools) were embedded and re-verified.

The honest reproducibility claim: every certificate is independently **re-verifiable**
from public materials with no model in the loop. The original *discovery* of some
certificates used Aristotle/Axle and is named, not push-button reproducible.

## What the numbers mean
- Released-set solve figures are a **ceiling** on our frozen 800-row dev corpus,
  leaning on exact-row certificates the organizers say won't recur privately.
- The figures that **generalize** are the held-out cohorts (120/120, 100/100),
  reproducible from a seeded program (`evidence/held-out-cohorts/`).
- No figure carries an **official** badge until an organizer judge run returns.

See `HOW-TO-CHECK.md` to verify all of this yourself.
