# Riemann Labs — SAIR Stage 2: Equational Theories

**Certificate-emitting solvers for equational implication over magmas.**
Christopher Brock · [Riemann Labs](https://torus.riemannlab.com) · SAIR Foundation Mathematics Distillation Challenge, Stage 2

> *No answer counts unless the judge accepts it.* Every claim in this repository
> is a machine-checkable Lean 4 certificate re-verified by the competition's
> open, deterministic judge — or it isn't a claim.

---

## The two solvers

| Entry | File | Philosophy |
|-------|------|------------|
| **EULER** | [`SHIP-2026-08-26/solvers/EULER.py`](SHIP-2026-08-26/solvers/) | Precomputed mathematics: an exact direction oracle from public ETP data, a hypothesis-keyed finite-model bank, bounded Knuth–Bendix completion, transitivity composition, and ATP-proof replay. |
| **WILL** | [`SHIP-2026-08-26/solvers/WILL.py`](SHIP-2026-08-26/solvers/) | The deliberate counterpart — no oracle, no banks, no borrowed certificates. Technique only. |

**The gap between them is the finding.** EULER measures what accumulated public
mathematics (*sediment*) buys; WILL measures what live reasoning (*technique*)
achieves alone. The study of that gap is the competition paper,
[*Sediment and Technique*](CONTRIBUTION-PACK/12-COMPETITION-PAPER/sediment-and-technique.md).

Both are single-file, Python 3.11 stdlib-only, under 500 KB, valid for the Solo
and Marathon tracks, with embedded-data disclosures inline.

## Start here

- **[The submission packet](SHIP-2026-08-26/)** — frozen 2026-08-26:
  solvers, papers, evidence, [`CHECKSUMS.sha256`](SHIP-2026-08-26/CHECKSUMS.sha256).
- **[How we built it](SHIP-2026-08-26/HOW-WE-BUILT-IT.md)** · **[How to check it](SHIP-2026-08-26/HOW-TO-CHECK.md)**
- **[Submission notes](SHIP-2026-08-26/SUBMISSION-NOTES.md)** — per-entry disclosures, honest scope, acknowledgments.

## The papers

1. **[Mathematics in the Age of Mechanical Reproduction](CONTRIBUTION-PACK/1-PAPER/)** —
   the epistemic framework: what it means to *know* a theorem when machines
   produce the proofs.
2. **[EULER: a certificate-emitting solver](CONTRIBUTION-PACK/11-SOLVER-PAPER/euler-a-certificate-emitting-solver.md)** —
   the architecture paper.
3. **[Sediment and Technique](CONTRIBUTION-PACK/12-COMPETITION-PAPER/sediment-and-technique.md)** —
   the EULER-vs-WILL controlled study.

Supporting: [EULER methodology](EULER-METHODOLOGY.md) ·
[trust framework](EULER-TRUST-FRAMEWORK.md) ·
[WILL manifesto](WILL/WILL-MANIFESTO.md) ·
[the full contribution pack](CONTRIBUTION-PACK/) (manifest, four tellings,
statement fidelity, epistemic badges, trace, workflow diagrams).

## Five exemplar proofs

Standalone Lean 4 files that compile against the competition judge, ordered from
the simplest technique to the most compositional:

| # | File | Pair | Technique |
|---|------|------|-----------|
| 1 | [`RiemannLabs_Proof_1_Constancy.lean`](RiemannLabs_Proof_1_Constancy.lean) | 3268 → 3253 | Direct constancy substitution |
| 2 | [`RiemannLabs_Proof_2_ConstantCollapse.lean`](RiemannLabs_Proof_2_ConstantCollapse.lean) | 3829 → 41 | Constant magma via transitivity |
| 3 | [`RiemannLabs_Proof_3_Bootstrap.lean`](RiemannLabs_Proof_3_Bootstrap.lean) | 359 → 4065 | Self-referential bootstrap (`congr_arg`) |
| 4 | [`RiemannLabs_Proof_4_Pivot.lean`](RiemannLabs_Proof_4_Pivot.lean) | 404 → 4236 | Shared pivot (`.trans` / `.symm`) |
| 5 | [`RiemannLabs_Proof_5_CompoundSubstitution.lean`](RiemannLabs_Proof_5_CompoundSubstitution.lean) | 282 → 2133 | Compound term substitution |

## Evidence, not assertion

- **[Held-out cohorts](HELD-OUT-COHORTS/)** — problems the solvers had never
  seen, with [provenance](HELD-OUT-COHORTS/PROVENANCE.md) and a
  [reproduction script](HELD-OUT-COHORTS/reproduce_heldout.py).
- **[Aristotle provenance](SHIP-2026-08-26/evidence/aristotle-provenance/)** —
  job records for every proof queued to the Aristotle/Harmonic prover.
- **[WILL bench](SHIP-2026-08-26/evidence/will-bench/)** — self-tests,
  manifests, and the Lean certificates behind WILL's numbers.
- **[Solver test environment](harness/)** — the AXLE judge replica (cloud Lean
  4.32.2, the judge's exact toolchain), TRUE/FALSE benches, and vendored
  problem sets. The ground-truth outcome table is deliberately absent — see the
  [anti-cheating note](harness/README.md).
- **[Judge bug report](SAIR-JUDGE-BUG-REPORT-2026-08-20.md)** — the
  olean-header mismatch we found and reported during Stage 2.

## Context

- **Domain:** 4,694 equational laws over magmas; ~22 million pairwise
  implications. Built on the
  [equational_theories project](https://github.com/teorth/equational_theories)
  (Tao et al.) and the
  [SAIR Stage 2 judge](https://github.com/SAIRcompetition/equational-theories-lean-stage2).
- **Verification:** Lean 4 kernel — machine-checked, zero trust.
- **Riemann Labs** is the mathematical research division of the Brock Command
  Center — formal verification, automated reasoning, and the intersection of
  algebraic structure with computational proof. See the
  [Riemann Labs observatory](https://torus.riemannlab.com) and our
  [machine-verified mathematics corpus](https://github.com/primaryhosting/brockian-mathematics)
  (11,000+ AXLE-kernel-verified Lean 4 theorems).
- [Brockian ↔ equational-theory connections](BROCKIAN-EQUATIONAL-THEORY-CONNECTIONS.md) ·
  [AI-orchestrated mathematics whitepaper](ai-orchestrated-mathematics-whitepaper.md)

---

*Frozen ship: [`SHIP-2026-08-26.zip`](SHIP-2026-08-26.zip) ·
[`SHIP-2026-08-26.FREEZE.sha256`](SHIP-2026-08-26.FREEZE.sha256)*
