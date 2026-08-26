# Solver Test Environment — AXLE Judge Harness

The scoring loop for optimizing EULER/WILL. Every claimed result must pass this
harness; nothing else counts.

## The judge chain

- **AXLE** (`axle_judge.py`) — fast replica of the SAIR judge: builds the exact
  judge `Goal` (bare `Magma` class, `◇` notation, no Mathlib) and compiles the
  candidate proof on cloud Lean **4.32.2** (the judge's toolchain) via the AXLE
  verify engine. Seconds per check instead of the 40-minute playground.
- **Aristotle / Harmonic** — the theorem-proving pipeline used to queue harder
  lemmas (see `evidence/aristotle-provenance/`). Use for TRUE-direction proof
  search when the deterministic tiers stall; every returned proof still goes
  through AXLE before it counts.

## Node requirements (execution environment)

- `BROCKIAN_MATH` — path to a `brockian-mathematics` checkout providing
  `engine.verify` (default: `~/Projects/brockian-mathematics`).
- `AXLE_API_KEY` — in the environment for cloud Lean compilation.
- Python 3.11+ stdlib only otherwise.

## Running a scored experiment

```bash
python3 harness/bench_full.py normal   # full TRUE+FALSE bench (default set)
python3 harness/bench_true.py normal   # TRUE-direction only, per-tier breakdown
python3 harness/bench_full.py hard1    # harder sets: hard1 / hard2 / hard3
```

- Solver under test: `EQT02-S00021-infra-failfast.py` at the repo root, or set
  `EULER_SOLVER=/path/to/candidate.py`. `bench_full.py` args:
  `[problem_set] [sample_size] [budget_seconds]` (default `normal 50 60`).
- **Metrics:** each bench ends with machine-readable lines —
  `METRIC solve_rate=…`, `METRIC true_rate=…`, `METRIC false_rate=…`.
  These are the numbers experiments are compared on; keep the format stable.
- **Certificates survive only if committed.** Every judge-accepted result is
  written to `certs/` at the repo root — self-contained `.lean` proofs for TRUE,
  `.countermodel.json` for FALSE. Experiments should `git add certs/` so found
  proofs persist in the experiment branch (the runner uploads logs only, not
  files).
- Problem sets are vendored in `harness/problems/` (from the SAIR Stage 2
  examples). TRUE claims verify via AXLE; FALSE claims verify by finite-model
  evaluation matching the judge's `decideFin!` semantics.
- `chain_engine.py` — matching-chain prover usable as a solver tier.

## Anti-cheating (deliberate)

The equational-theories ground-truth outcome table (`outcomes.json`, 476 MB) is
**intentionally absent** from this repo and must never be added: looking up
known outcomes instead of proving/refuting them is cheating and voids the run.
The bench problem files carry an `answer` field for scoring only — solvers must
never read it.
