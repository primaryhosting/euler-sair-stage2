# Infinite FALSE validation record

Recorded 2026-08-25 for
`EULER-v8.1-CANDIDATE.py`, 437,402 bytes, SHA-256
`52bcd90f668873687756fa68becf9d2b9d86b55a6a9b206ac764078b0fcd303e`.

## AXLE / Axiom

Both adjacent Lean files were submitted independently to AXLE with environment
`lean-4.32.2`.

| Artifact | Compile result | Axiom audit of `submission` |
|---|---|---|
| `parity-walk-axle.lean` | `verified: true`; errors `[]`; failed declarations `[]` | `trusted: true`; axioms `[]`; extra axioms `[]` |
| `structured-plan-axle.lean` | `verified: true`; errors `[]`; failed declarations `[]` | `trusted: true`; axioms `[]`; extra axioms `[]` |

These are faithful self-contained goal wrappers for the generated certificate
and the structured-plan assembler. They are validation fixtures, not embedded
pair-keyed solver certificates.

## Official Python sandbox reproduction

The exact candidate imported and generated/validated the 1,511-byte parity
artifact inside the official pinned image
`python@sha256:db3ff2e1800a8581e2c48a27c3995339d47bdf046da21c7627accd3d51053a93`
with amd64, no network, read-only filesystem, 2 CPUs, 2,048 MB RAM, 64 PIDs,
and a 64 MB `/tmp`. The same smoke checked that raw LLM JSON preserves
arithmetic `*`. Result: `official-python-smoke-ok 1511`.

## Regression boundary

The integrated candidate rerun reached 800/800 on the four released 200-row
sets (400 TRUE / 400 FALSE). The final source changes after that run were
provenance comments and a stricter blacklist in the LLM-only FALSE artifact
envelope; no released route enters that envelope. The parity-walk recognizer
matches zero released rows, so this validation is evidence for a new
out-of-distribution capability, not an explanation of the released-set score.

No official playground credits were used. Promotion to the live mirror still
requires one fresh accepted official-judge run.
