# v5.9 — clean solver, technique without the table

## What it does
Decides magma-law implications Eq1 ⇒ Eq2 deterministically: a Lean 4 proof for TRUE, a finite countermodel for FALSE. It carries NO implication oracle, NO matrix, NO certificate bank, NO finite-model seeds, and no problem-keyed proof or verdict — every certificate is derived from the two input equations at runtime. On the public order-4/order-5 stress set it reaches 200/200, 0 wrong, with emitted true certificates Lean-verified. Full write-up and paper: https://torus.riemannlab.com/euler-vs-will

## How it works
- TRUE: a proof-recording given-clause SUPERPOSITION loop with E-style age/weight selection derives Lean lemma DAGs at runtime and emits anonymous term proofs of the judge Goal (congrArg / Eq.trans / Eq.symm chains).
- FALSE: a seed-free finite-domain CSP grounds the universal antecedent and searches operation tables with propagation and carrier-symmetry breaking; every table is independently replayed before emission as an arithmetic-free nested-match `Fin n` existential.
- Solo only: a disclosed judge-feedback LLM fallback runs from a single top-level `PROMPT`, and only after every deterministic tier fails; its output is judge-checked, never trusted.
Stdlib only; no network, no subprocess. It never reads any answer or ground-truth field.

## Embedded-data disclosure (required)
Runtime is Python stdlib only. The only compressed payloads are the SOURCE CODE of the two provers (the given-clause superposition loop and the seed-free CSP), zlib/base64-compressed purely to keep the submission a single file, each SHA-256-pinned beside its blob. These blobs are executable ALGORITHM — they contain no equation, no table, no model seed, no verdict, and no problem-keyed branch; decompressing recovers ordinary Python. There is no implication matrix, oracle, certificate bank, or finite-model bank of any kind.

## Evidence (honest)
Public `stress_test` (200): 200/200, 0 wrong, DETERMINISTIC (no LLM). A broad sample of emitted TRUE certificates verified on Lean 4.33.0 via AXLE, spanning all four categories including order4_extra_hard and order5_normal; FALSE witnesses re-checked exhaustively in Python. Released-set evidence only — the private evaluation is unseen by everyone and no result there is claimed.

## Philosophy
This is technique without the table: no sediment, only reusable search. It is the clean counterpart to the flagship EULER — and it reaches the same score carrying none of the machinery, which is the argument of the paper *Mathematics in the Age of Mechanical Reproduction* made concrete.

## Links & thanks
Riemann Labs — https://torus.riemannlab.com · Paper (a response to Tao's *Mathematics in the Age of AI*) — https://torus.riemannlab.com/viewpoint/mechanical-reproduction · https://torus.riemannlab.com/euler-vs-will. Thanks to the Equational Theories Project (Terence Tao et al.) and the SAIR judge; Stephan Schulz's E-prover (given-clause loop); Lean/Mathlib (Leonardo de Moura, the Lean FRO). The infinite-model families were informed by Contributor Network S00023/M00010. — Christopher Brock, Riemann Labs
