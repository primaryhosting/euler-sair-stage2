# Bug report: Stage 2 judge fails 100% of submissions with `JUDGE_INFRASTRUCTURE_ERROR` (stale `Magma.olean`)

**Competition:** Mathematics Distillation Challenge — Equational Theories, Stage 2
**Date observed:** 2026-08-20, ~11:05–11:06 AM
**Solver:** Euler
**Affected runs (all identical):**
- `s2run_64f82eb9-012d-4238-8f9f-41afca957cfc` — 10/10 → 0A / 0R / 10E
- `s2run_7669cb85-c3f4-42de-8750-fb139be7bebf` — 10/10 → 0A / 0R / 10E
- `s2run_2a6c4fa4-0793-4b8c-b71b-e1bf615dc0f4` — 10/10 → 0A / 0R / 10E
- `s2run_88e71b23-ff86-42ae-ab55-91c948070646` — 2/2 → 0A / 0R / 2E

## Summary

Every problem in every run — **both `normal_true_*` and `normal_false_*`** — returns verdict `--` with judge status `ERROR` and code `JUDGE_INFRASTRUCTURE_ERROR`. No submission is ever evaluated. The failure occurs **inside the judge itself, before the submitted proof is checked.**

## Exact error (from Lean stderr)

```
Traceback (most recent call last):
  File "<string>", line 17, in <module>
  File "/opt/lean-judger/judge/verify.py", line 793, in verify_answer
    _write_problem_module(
  File "/opt/lean-judger/judge/verify.py", line 375, in _write_problem_module
    raise JudgeInfrastructureError(f"failed to compile JudgeProblem: {details}")
judge.verify.JudgeInfrastructureError: failed to compile JudgeProblem:
/tmp/lean-judger-artifacts/judge-.../JudgeProblem.lean:1:0:
error: failed to read file '/opt/lean-judger/JudgeMagma/Magma.olean', incompatible header
```

(There is a secondary, harmless `FileNotFoundError: '/opt/eq-py/-c'` from the Python `apport` crash-reporter hook — not the cause.)

## Diagnosis

`"incompatible header"` when loading a `.olean` is Lean 4's signature error for a **toolchain version mismatch**: the precompiled `/opt/lean-judger/JudgeMagma/Magma.olean` was built with a **different Lean version** than the `lean` binary currently running in the judge sandbox. Because `JudgeProblem.lean` imports `JudgeMagma.Magma` on line 1, the judge can't compile the problem module at all — so `_write_problem_module` raises before any submitted proof is type-checked. This is why the failure is identical on 100% of problems regardless of solver output.

Most likely trigger: a Lean/Mathlib toolchain bump in the judge image without a matching rebuild of the `JudgeMagma` oleans.

## Suggested fix

Rebuild `JudgeMagma` (and its Mathlib dependencies) against the judge image's current `lean-toolchain`, **or** pin the judge's `lean` binary to the exact toolchain that produced the shipped `Magma.olean`. Adding a startup smoke-test that compiles a trivial `import JudgeProblem` module would catch this class of regression before it reaches competitors.

## Contradicts the published Evaluation Spec

The Stage 2 Official Evaluation Spec states the judge is **pinned**: *"The deterministic Lean judge is pinned to exact toolchain and dependency versions — no floating tags, no auto-updating dependencies. Lean v4.32.2 (commit f3b06c705e6c85f5314019d5d3baab0fec5b580c), Toolchain leanprover/lean4:v4.32.2, Mathlib 905b95818eb32af7874a58b427f50c1711a5e96c."*

An `incompatible header` when loading `JudgeMagma/Magma.olean` means the running box has an olean built with a **different Lean than the `lean` now executing there** — i.e., the deployed judge has drifted from its own pinned spec. The spec also guarantees *"the same judge code runs locally and at the official evaluation."* The solver sandbox itself cannot be the cause: per spec it is a `--network=none`, read-only, `--cap-drop=ALL` `python:3.11-slim` container with no access to the judge environment; it reaches the judge only through the organizer proxy. Nothing a contestant `solver.py` can do produces this error.

## Impact

- No competitor can obtain an Accepted or Rejected verdict on Stage 2 right now.
- Solvers that retry on judge failure burn their full time + LLM budget against an unfixable error (one problem consumed 1,557s here).
