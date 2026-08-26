# WILL released-set bench (mechanical tiers, fixed solver)

Deterministic 50-FALSE + 50-TRUE sample from `evaluation_normal` (seed 20260826), 25s/problem, **no LLM and no oracle** in this sandbox. WILL writes only answers its own
tiers self-verify; we additionally check verdict==ground-truth, cert shape, and (FALSE)
independent finite-model recheck. Mechanical-tier floor on released problems — NOT an
official-judge or private-set run.

- **FALSE solved (mechanical): 50/50** — cert shape OK 50/50, countermodel independently re-checked 50/50
- **TRUE solved (chain+collapse, mechanical): 34/50** — cert shape OK 34/34
- answers disagreeing with ground truth: 0 (WILL self-verifies before writing)

The FALSE certificates' *judge acceptance* (not just shape) is established separately by `gate1-judge-false-results.json` — compiled under the real local Lean v4.32.2 judge.
