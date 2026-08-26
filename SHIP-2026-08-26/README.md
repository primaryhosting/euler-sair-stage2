# Riemann Labs — SAIR Stage 2 Submission Packet

**Christopher Brock · Riemann Labs · 2026-08-26**
SAIR Foundation, Mathematics Distillation Challenge — Equational Theories,
Stage 2 (Solo + Marathon).

---

## What this is

Two solvers for equational implication over magmas, each a single `solver.py`
valid for both tracks (the same file — `__main__` branches on
`JUDGE_MARATHON_MANIFEST`). Every answer is a machine-checkable Lean certificate
re-verified by the competition's open, deterministic judge.

| Entry | File | SHA-256 | Size |
|-------|------|---------|------|
| **EULER** | `solvers/EULER.py` | `e0f7ac84…48329` | 442,061 B |
| **WILL** | `solvers/WILL.py` | `90aa400c…bc66a` | 91,230 B |

Full SHA-256 in `CHECKSUMS.sha256`. Both compile under Python 3.11 stdlib only,
under the 500 KB limit, with the embedded-data disclosure inline at the top of
each file.

**EULER** precomputes the mathematics: an exact direction oracle from public ETP
data, a hypothesis-keyed finite-model bank, bounded Knuth–Bendix completion,
transitivity composition, and ATP-proof replay — behind a strict rule: *no
answer counts unless the judge accepts it*. **WILL** is the deliberate
counterpart — no oracle, no banks, no borrowed certificates, technique only —
to measure how much of the performance is sediment and how much is technique.
The gap between them is the finding.

## Contents

- `SUBMISSION-NOTES.md` — paste-ready per-entry: title, description,
  **embedded-data disclosure**, honest scope, **acknowledgments**, links,
  and a pre-upload checklist.
- `solvers/` — the two entries.
- `papers/` — **two designated white papers** plus one supplementary study:
  1. *Mathematics in the Age of Mechanical Reproduction* — the epistemic framework
     this submission is built to satisfy (with a dated `ERRATA-` note correcting the
     Stage-2 chronology and stamping facts current as of 2026-08-26).
  2. *EULER: A Certificate-Emitting Solver for Equational Implication* — the
     technical paper.
  3. *Sediment and Technique* (`sediment-and-technique-competition-paper.md`) —
     a **supplementary** paired exploratory case study (EULER vs WILL). Held as
     supplementary, not a designated white paper, until its comparison is
     strengthened to a true single-flag ablation.
- `HOW-WE-BUILT-IT.md` / `HOW-TO-CHECK.md` — the build story and a command-by-command
  verification guide (nothing needs network or credits except the final official run).
- `evidence/` — the reproducible held-out cohorts (seeded generator, immutable
  cohort manifests, result log) and the epistemic-badge table.
- `CHECKSUMS.sha256` — verify with `shasum -a 256 -c CHECKSUMS.sha256`.

## Acknowledgments

- **Axle — Axiom (Carina Hong and the Axiom Math team).** Our dev-time
  verification backbone: judge-exact Lean v4.32.2 compile-checks in ~2 seconds.
  Every embedded certificate passed through it, and both disclosed
  statement-fidelity failures were discovered as Axle divergences.
- **Aristotle — Harmonic.** Proved 390 of EULER's hard TRUE implications during
  development; embedded and disclosed, re-verified by the judge at answer time.
  A dev-time contributor only.

With the Equational Theories Project (Tao et al.) and the classical stack —
Knuth–Bendix, Twee, Mace4, E, Vampire. None a runtime dependency; all shaped
what the runtime carries; everything re-verified before the judge saw it.

## Links

- **White paper** — *Mathematics in the Age of Mechanical Reproduction*
  (`papers/…pdf`).
- **Interactive presentation** — `https://prime-rigor-explorer.lovable.app/euler`
  (public at release).
- Equational Theories Project — github.com/teorth/equational_theories
- SAIR Stage 2 judge (open) — github.com/SAIRcompetition/equational-theories-lean-stage2

## Honest status

All measured figures are computationally verified or judge-toolchain verified,
not yet confirmed by an official-judge run — the promotion gate. The released-set
800/800 is a *ceiling* that leans on exact-row certificates for released rows;
the generalizing evidence is the held-out 120/120 and 100/100 in `evidence/`,
which is reproducible from the seeded program there. No result carries an
official-judge badge until a fresh judge run returns. Every load-bearing claim
is auditable from public materials and the artifacts in this packet.
