# EULER — breadth-first, certificate-emitting solver

## What it does
EULER decides magma-law implications Eq1 ⇒ Eq2: a Lean 4 proof for TRUE, a finite or infinite countermodel for FALSE. Public knowledge narrows the direction; independent search methods then compete to produce a certificate the Lean judge accepts. Full write-up, verified certificates, and the essay this sits inside: https://riemannlab.com/euler-vs-will

## How it works
Equations are normalized; supplied IDs are bound to the supplied text before any ID-keyed fact is trusted. The public ETP implication closure supplies DIRECTION ONLY, never a proof.
- FALSE: a hypothesis-keyed finite-model bank; exhausted small tables; structured/polynomial families; a deadline-bounded CSP over orders 4–8; and, in Solo, an infinite parity-walk family. Every finite table is re-evaluated against both equations before emission.
- TRUE: an exact public-row proof when available; proof-carrying lemma chains; and the primary engine, GIVEN-CLAUSE SUPERPOSITION — E-prover's core loop reimplemented in pure Python (derived equations processed lightest-first with an age-weight selection ratio), which reaches the projection/collapse forcing lemmas that blind saturation misses; then substitutions, transitivity, rewrite/BFS, and tactic sweeps. In Marathon, unknown-direction rows get a bounded given-clause TRUE attempt before the costly countermodel search. Every emitted body is an independently replayed congrArg/Eq.trans/Eq.symm chain.
- Hard Solo residue: a budget-aware LLM receives the problem, the tried tiers, and Lean errors; its tables are Python-checked and its Lean stays untrusted until the judge accepts it.
Solo sends every candidate to the live judge; only "accepted" ends the run. Marathon has no judge or LLM: it writes only self-verified finite witnesses and deterministic or precompiled proof bodies, recompiled by the scoring judge.

## Embedded-data disclosure (required)
Runtime is Python stdlib only. Compressed payloads and how they were generated:
- Implication bitmatrix (~110 KB) + sparse lookup (~70 KB, 12,587 keys): parsed from the public ETP `outcomes.json` closure, normalized, Boolean-encoded, zlib/base64. Direction bits, not certificates.
- ETP equation texts (~15 KB), for ID/text validation.
- `_MT_SRC_B64` (~12 KB): the given-clause superposition prover's SOURCE code — algorithm, containing no equation, table, or verdict — zlib/base64.
- 305 finite magma tables (orders 2–9): harvested at development time with Mace4, each re-checked exhaustively by the solver's own evaluator before use.
- 26 hand-derived + 390 Aristotle + 18 pair-keyed ATP Lean certificates, for specific RELEASED public pairs, compiled with AXLE on the pinned toolchain. The Stage-2 spec states released rows do not recur in the private evaluation, so these are regression scaffolding, not private-set capability. Rebuild them by generating Lean conjectures from public pairs, proving via a Lean prover or ATP-to-Lean reconstruction, and keeping only compiling bodies.
Mace4, Aristotle/Harmonic, AXLE/Axiom, Twee, E-prover, and Vampire contributed at development time only; none is a runtime dependency.

## Evidence (honest)
On the public `order5_normal` stress category — entirely out of the matrix — the given-clause engine lifts the DETERMINISTIC result (no LLM, no bank) from 29/50 to 50/50, 0 wrong; sampled true certificates verified 9/9 on Lean 4.33.0 via AXLE, false witnesses re-checked exhaustively in Python. Held-out development cohorts: 120/120 and 100/100 FALSE on unseen hypotheses. None of this guarantees the private evaluation, which no one can see.

## Links & thanks
Riemann Labs — https://riemannlab.com · Paper, *Mathematics in the Age of Mechanical Reproduction* (a response to Tao's *Mathematics in the Age of AI*) — https://riemannlab.com/mechanical-reproduction · full acknowledgments — https://riemannlab.com/euler-vs-will. Thanks to the Equational Theories Project (Terence Tao et al.), the SAIR judge, Stephan Schulz's E-prover (given-clause loop), Harmonic, Axiom, Mace4, Twee, Vampire, and Lean/Mathlib (Leonardo de Moura, the Lean FRO). Contributor Network: S00019, S00023, M00010, Emily, suii0x; the given-clause turn was prompted by Axabra and Wenlin Zhang's deterministic sweeps. — Christopher Brock, Riemann Labs
