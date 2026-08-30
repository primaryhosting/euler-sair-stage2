# EQT02 — ultimate AutoLab-distilled certificate emitter

## What it does and why

EQT02 is the deterministic result of AutoLab optimization over the EULER line.
It constructs a Lean 4 proof for TRUE or an existential countermodel proof for
FALSE. It preserves productive general algorithms while removing memorized
answers and runtime model dependence: 69,055 bytes, Python stdlib only, zero LLM
calls, no network, and no subprocess. It is the lowest-variance anchor for both
tracks.

## How it works

EQT02 parses each equation into a term tree and runs a certificate-first
cascade. It never reads an answer or ground-truth field.

- Finite FALSE search first exhausts every small table, samples order 4 with a
  fixed seed, enumerates parametric families through order 13 (affine modular
  operations, min/max, and projection families), then uses a
  constraint-pruned exhaustive order-4 search. Order 5 is attempted only after
  order 4 is genuinely exhausted, with a longer escalation when budget permits.
  Random probes may reject bad family candidates cheaply, but every survivor is
  exhaustively evaluated on all assignments before it becomes a certificate.
- TRUE search performs bidirectional term rewriting with explicit
  substitutions and positions. If that fails, proof-recording ordered
  Knuth–Bendix completion generates critical pairs and tries to join the goal.
  Separate standard and deep budgets keep easy cases cheap. A successful chain
  is independently re-walked before term- or tactic-style Lean is emitted.
- A last FALSE tier searches piecewise-affine operations on the infinite
  carrier `Int` and constructs a direct Lean/`omega` proof. The finite window is
  only candidate discovery; the emitted Lean proof, not the sample, is what the
  scoring judge ultimately trusts.
- If no certificate is found, EQT02 returns UNKNOWN/omits the row. It never
  converts failure-to-find into an implication verdict.

TRUE answers are anonymous proofs of the official `Goal`. Finite FALSE answers
define an arithmetic-free nested-match operation on `Fin n` and use exhaustive
decision. A whitelist lint blocks forbidden declarations and escape hatches.

In Solo, EQT02 sends the first certificate to the live judge and accepts only a
judge `accepted`; if time remains after rejection, it retries with deeper BFS,
completion, and order-5 budgets. In Marathon it uses the batch budget globally:
pass one runs cheap standard tiers across every problem, and pass two allocates
remaining time among only the residue. There is no LLM cost. Marathon answers
are compiled by the scoring judge after the process exits.

## Embedded-data disclosure and reproduction

EQT02 embeds no implication oracle, outcome/answer bank, pair lookup, stored
finite-model bank, compressed data, binary blob, per-law fact database, or
pair-specific Lean certificate. The inlined material is readable source code:
term/law utilities, finite evaluators, Lean emitters, search algorithms, and
configuration. The top-level `PROMPT` is an unused compatibility string; no
code path calls an LLM. A comparable artifact is reproduced by running these
deterministic tiers and retaining generated certificates; no private data or
runtime service is needed.

## AutoLab provenance and evidence

AutoLab project `primaryhosting/euler-sair-stage-2` autonomously evaluated and
refined the deterministic tiers. Canonical experiment `388d313e` measured
1,499/1,500 decided pairs on a uniform development benchmark drawn from the
full 4,694-law pool: 553 TRUE, 946 FALSE, one UNKNOWN, and zero FALSE emission
failures, on the pinned Lean 4.32.2-compatible toolchain (6,966 seconds).
Packaging experiment `6f80ea8e` passed 12/12 answers through the official
`pipeline/runner.py`, with zero bad certificates, zero harness imports, and the
69,055-byte file. Packaged commit: `fe5cb161`.

These are node-verified development measurements, not an official private-set
score and not a guarantee of 1,499/1,500 on the competition distribution. A
fresh AutoLab retry does not replace this frozen artifact unless separately
reviewed, packaged, and revalidated.

## Intended placement and credits

Submit EQT02 in both Solo and Marathon. Its oracle-free deterministic behavior,
strong broad-pool evidence, and Marathon-wide two-pass triage make it the anchor
for either an all-artifacts or score-first allocation.

Sources: the open SAIR Stage 2 judge and Equational Theories Project. AutoLab
performed the optimization campaign; Axle/Axiom supported judge-toolchain
verification during development.
