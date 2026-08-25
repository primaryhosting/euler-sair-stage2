**Stage 2 judge is failing 100% of submissions with `JUDGE_INFRASTRUCTURE_ERROR` — stale `JudgeMagma/Magma.olean` (Lean toolchain mismatch)**

Competition: Mathematics Distillation Challenge — Equational Theories, Stage 2
Solver: Euler · First observed 2026-08-20 ~11:05 AM, still reproducing on re-run at 11:06 AM.

**What's happening:** every problem in every run — both `normal_true_*` and `normal_false_*` — returns verdict `--`, judge status `ERROR`, code `JUDGE_INFRASTRUCTURE_ERROR`. No submission is ever evaluated. The failure is inside the judge, *before* the submitted proof is checked.

Reproducing runs (all identical, 0 Accepted / 0 Rejected / all Errors):
`s2run_64f82eb9-012d-4238-8f9f-41afca957cfc` · `s2run_7669cb85-c3f4-42de-8750-fb139be7bebf` · `s2run_2a6c4fa4-0793-4b8c-b71b-e1bf615dc0f4` · `s2run_88e71b23-ff86-42ae-ab55-91c948070646`

**Exact error (Lean stderr):**
```
File "/opt/lean-judger/judge/verify.py", line 375, in _write_problem_module
    raise JudgeInfrastructureError(f"failed to compile JudgeProblem: {details}")
judge.verify.JudgeInfrastructureError: failed to compile JudgeProblem:
/tmp/lean-judger-artifacts/judge-.../JudgeProblem.lean:1:0:
error: failed to read file '/opt/lean-judger/JudgeMagma/Magma.olean', incompatible header
```
(The secondary `FileNotFoundError: '/opt/eq-py/-c'` is just the Python apport hook — not the cause.)

**Diagnosis:** `"incompatible header"` on a `.olean` is Lean 4's signature for a toolchain version mismatch — `/opt/lean-judger/JudgeMagma/Magma.olean` was compiled with a different Lean version than the `lean` binary now running in the judge sandbox. Since `JudgeProblem.lean` imports `JudgeMagma.Magma` on line 1, the judge can't build the problem module at all, so it raises before any submission is type-checked. Most likely trigger: a Lean/Mathlib bump in the judge image without a matching rebuild of the `JudgeMagma` oleans.

**Suggested fix:** rebuild `JudgeMagma` (and its Mathlib deps) against the judge image's current `lean-toolchain`, **or** pin the judge's `lean` binary to the toolchain that produced the shipped `Magma.olean`. A startup smoke-test that compiles a trivial `import JudgeProblem` module would catch this class of regression before it reaches competitors.

**Impact:** no competitor can get an Accepted/Rejected on Stage 2 right now, and solvers that retry on judge failure burn their full time + LLM budget against an unfixable error (one problem consumed 1,557s on our side).

Happy to provide full per-problem logs / artifact IDs if useful.
