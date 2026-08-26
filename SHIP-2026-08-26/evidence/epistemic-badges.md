# EULER — Epistemic Badge Table
*(the paper's §10 requirement: mark epistemic state explicitly, and
separately from provenance; a badge that asserts nothing beyond "the kernel
checked something" leaves its trust assumptions unspecified)*

## Badge definitions used in this pack

| Badge | Meaning | Trust base disclosed |
|---|---|---|
| **VERIFIED (judge-toolchain)** | The exact artifact compiles and proves its stated goal under Lean **v4.32.2, commit `f3b06c705e6c85f5314019d5d3baab0fec5b580c`** — the official judge's pinned toolchain — against the judge-faithful goal wrapper | Lean kernel; the goal construction (rebuilt from the judge's published source after the §3-A fidelity failure); allowed axioms `propext`, `Quot.sound`, `Classical.choice`; no `sorry`-family, metaprogramming, or unsafe tokens (grep-audited) |
| **COMPUTATIONALLY VERIFIED** | A finite claim checked by exhaustive evaluation (no sampling), in `decideFin!` semantics | The 30-line Python evaluator, itself cross-checked against Lean acceptance on hundreds of certificates |
| **CEILING** | A score obtained from verified components, but not from an end-to-end official judge run | Everything above, **minus** the organizer's harness, network policy, and production sandbox |
| **OFFICIAL** | Verdict returned by the organizer's judge in production | *(no artifact in this pack currently carries this badge — stated plainly)* |

The ladder deliberately mirrors Lean's own validation guidance (escalating
audit of derivability, dependencies, implementation trust). The step we have
not taken — `lean4checker` recheck and external-checker comparison — is what
the paper calls HIGH-ASSURANCE VERIFIED; no artifact here claims it.

## Per-artifact badges

| Artifact | Badge | Notes |
|---|---|---|
| 8 `_LB` certificates (order-4 TRUE residuals) | **VERIFIED (judge-toolchain)** | Each body compiled and accepted against the judge-faithful goal on Lean 4.32.2; token-audited clean. Pair-keyed: released-set coverage only. |
| 10 `_O5B` certificates (order-5 TRUE residuals) | **VERIFIED (judge-toolchain)** | Same regime (E/Vampire replay, exact-Lean check). Pair-keyed: released-set coverage only. |
| 100 order-5 TRUE bodies (84 quick + 6 deep completion + 10 static) | **VERIFIED (judge-toolchain)** | Full released-set replay compiled offline. |
| 305-table FALSE bank | **COMPUTATIONALLY VERIFIED** | Every table: E1 holds ∀σ, E2 fails ∃τ, full evaluation. The judge's `decideFin!` re-proves each at answer time. |
| Held-out FALSE results (120/120; 100/100 novel-hypothesis) | **COMPUTATIONALLY VERIFIED** | The generalization claim of record for the FALSE side. |
| Oracle direction 600/600 | **COMPUTATIONALLY VERIFIED** | Deterministic lookup vs SAIR's published answers. |
| Released-set 800/800 | **CEILING** | Composed of verified parts; leans on pair-keyed certificates; **not** a private-set claim; **not** OFFICIAL. |
| Solver runtime behavior (sandbox compliance, protocol, Marathon fixture) | **CEILING** | Reproduced in the pinned official container image offline; not an organizer run. |
| Any private-set performance figure | **NONE — intentionally unbadged** | No number is offered. The generalizing mechanisms and their held-out evidence are the only claims made. |

## The one badge transition that remains

Every row above converts to **OFFICIAL** through exactly one action: a fresh
run under the organizer's judge (playground or final evaluation). Until that
run, this table is the pack's ceiling-vs-confirmed boundary, stated once and
referenced everywhere a number appears. The last attempted official run
(2026-08-20) failed on organizer-side infrastructure (`Magma.olean`
incompatible header) — documented, reported, and not counted as evidence in
either direction.
