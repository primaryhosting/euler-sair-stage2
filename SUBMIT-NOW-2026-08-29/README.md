# SAIR Stage 2 — upload-ready solvers

Prepared 2026-08-29 from the frozen `SHIP-2026-08-27-FINAL` packet.
Each entry contains the exact canonical bytes under the required filename
`solver.py`, plus a submission note kept below the live 5,000-character limit.

## Verified artifacts (given-clause revision, 2026-08-30)

| Entry | Size | SHA-256 |
|---|---:|---|
| EULER | 443,119 B | `8dd5633ad0854cde04acbcadf8fe82c2e60d32f9fc39a802984f4f61a7b88231` |
| WILL | 104,685 B | `cf90ee74d3e0122b8aae04fc367947f1393f5c4c0ef88adfcd650403c49d9376` |
| EQT02-ULTIMATE | 69,055 B | `b58a004ba4112c0588e5b55eabc5de7a9dac50668fcb898eee91849ca7e33683` |

**What changed in this revision.** EULER and WILL both gained a **given-clause
superposition prover** (E-prover's core loop, reimplemented in pure Python:
lightest-first processing with an age-weight selection ratio). It closes the
order-5 projection/collapse forcing laws that blind saturation missed. On the
public `order5_normal` stress category, EULER's deterministic result rose from
29/50 to **50/50, 0 wrong**; a sample of emitted true certificates verified 9/9
on Lean 4.33.0 via AXLE. WILL gained the same tier (as `_GC_SRC_B64`, disclosed
in its note — algorithm source, not data) and now proves projection laws with no
table. Pre-revision baselines are preserved beside each as `solver-baseline-preGC.py`.
EQT02-ULTIMATE is unchanged. All three are Python-stdlib-only (no third-party
packages — the sandbox is `python:3.11-slim`), ≤ 500 KB, one top-level `PROMPT`,
and support both Solo and Marathon through `JUDGE_MARATHON_MANIFEST` branching.

Links: Riemann Labs — https://torus.riemannlab.com · Paper —
https://torus.riemannlab.com/viewpoint/mechanical-reproduction · EULER vs WILL vs the World —
https://torus.riemannlab.com/euler-vs-will

## Placement decision

The live SAIR form accepts at most two submissions per track. Four slots cannot
place all three solvers in both tracks, so “correct placement” depends on the
submission objective.

Recommended if all three artifacts must be represented:

| Track | Submission 1 | Submission 2 | Why |
|---|---|---|---|
| Solo | EQT02-ULTIMATE | WILL | EQT02 is the deterministic anchor; WILL's unique six-round LLM + live-judge repair loop exists only in Solo. |
| Marathon | EQT02-ULTIMATE | EULER | EQT02 has global two-pass triage; EULER retains the broader deterministic batch router, whereas WILL disables its LLM in Marathon. |

Recommended if expected score is the only objective:

| Track | Submission 1 | Submission 2 |
|---|---|---|
| Solo | EQT02-ULTIMATE | EULER |
| Marathon | EQT02-ULTIMATE | EULER |

The private evaluation is unknown, so no ranking is certain. The first plan is
the strongest evidence-based way to include all three; the second favors the
two artifacts with the broadest measured coverage.

For Solo, assign GPT-OSS-120B to the LLM-capable companion and Gemma to EQT02.
The official Solo proxy uses the model selected in the form; a `model` field in
a solver request does not switch it. EQT02 makes no LLM calls, so its selection
does not change execution. All three frozen Marathon paths are deterministic,
so model choice does not change their behavior; use one model per upload if the
form or evaluation policy expects diversification.
