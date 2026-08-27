# EQT02-AUTOLAB.py — Provenance

**Entry 3 · packaged by the AutoLab optimization campaign · 2026-08-27**

## What it is

A single-file, deterministic, zero-LLM-token, stdlib-only certificate-emitting
solver for SAIR Stage 2 (Solo + Marathon; the file `__main__`-branches on
`JUDGE_MARATHON_MANIFEST`). Every TRUE is an anonymous Lean proof term of the
judge `Goal`; every FALSE is a whitelist-clean finite-countermodel existential
(arithmetic-free nested-match op, countermodel order up to 13). No network, no
subprocess, no oracle, no embedded per-pair answers; the solver never reads any
answer/ground-truth field.

## Where it came from

- AutoLab project: `primaryhosting/euler-sair-stage-2` (app.autolab.ai),
  objective: maximize judge-ACCEPTED verdicts on a uniform 1,500-pair "bigu"
  benchmark drawn from the real 4,694-law pool.
- Packaging experiment: `6f80ea8e` ("package-submission"), merged as commit
  `fe5cb16180211b0fedc0d1dbe7250c470963e8a3` — `scripts/build_solver.py`
  inlines laws + Lean emitters + all proving tiers into one `solver.py`;
  `scripts/test_solver_package.py` is the hard acceptance test.
- Canonical scorecard experiment: `388d313e` ("Escalation tier + bigu-1500
  rescore"), merged as `61516b99`.

## Measured numbers (node-verified, MLflow-logged; NOT official-judge)

- **bigu_lean_decided_pairs 1499 / 1500** — decided with a compiling Lean
  certificate on `leanprover/lean4:v4.32.2` (TRUE 553 / FALSE 946,
  `bigu_lean_false_emit_failures = 0`), wall 6,966 s (experiment `388d313e`).
- Packaging acceptance (experiment `6f80ea8e`): `runner_accepted 12/12`,
  `runner_bad_certs 0`, `solver_py_harness_imports 0`,
  `solver_py_bytes 69,055` (< 500 KB limit), normal-set regression slice
  29/29 decided, 0 undecided, wall 86.7 s.
- Sibling runs pinned `bad_certificates = 0` and runner-parity on the official
  toolchain.

- **Independent re-verification (2026-08-27, packet assembly):** the hard
  acceptance test (`scripts/test_solver_package.py`) was re-run from scratch on
  this exact file against the official `pipeline/runner.py` and judge checkout —
  **ALL CHECKS PASSED: 10/10 answers accepted, 0 harness imports, py_compile
  clean, 69,055 bytes**. Environment note: the official judge checkout pins
  Lean `v4.33.1` (not the previously published 4.32.2); the toolchain must be
  installed or every judge call times out at 30 s.

Per the packet's reactivation standard: no number above carries an
OFFICIAL-judge badge until a green run on playground.sair.foundation returns.

## File identity

```
size    69,055 bytes
sha256  b58a004ba4112c0588e5b55eabc5de7a9dac50668fcb898eee91849ca7e33683
source  origin/main @ fe5cb161 of the AutoLab project repo (solver.py, verbatim)
```

Recompute immediately before upload; rename to `solver.py` for the judge.
