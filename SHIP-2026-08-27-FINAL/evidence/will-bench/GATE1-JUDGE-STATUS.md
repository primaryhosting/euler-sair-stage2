# Gate 1 — real-toolchain compilation of WILL FALSE certificates ✅ DONE

## Result
WILL's FALSE certificates compile under **Lean v4.32.2 — the SAIR judge's exact
toolchain** — via **Axle** (Axiom's cloud judge-exact compiler):

- **15 / 15** constructed FALSE certs verified (`gate1-axle-false-results.json`).
- **6 / 6** real *released* FALSE certs verified — actual ETP order-4 equations
  from `evaluation_normal` (`gate1-axle-released-sample.json`).
- **Negative controls rejected 2 / 2** — a bogus FALSE cert for a TRUE implication
  (`comm ⊨ comm`) and a table that fails the hypothesis both return
  `verified=False`. The check has teeth; it is not a rubber stamp.

This is the actual kernel verdict (compiles ∧ no errors ∧ no `sorry`), not a
Python shape or finite-model check.

## Why Axle, and why it is faithful
The Mac was swap-saturated, so the *local* judge build stalled. Axle runs the same
Lean **4.32.2** in the cloud (~2 s/cert). To compile a FALSE cert — which `import`s
the judge's `JudgeProblem`/`JudgeDecide`/`JudgeFinOp` modules — as a single file,
the harness `gate1_axle_false.py` inlines the judge's **own module sources
verbatim** (`JudgeMagma/Magma.lean`, `JudgeDecide/DecideBang.lean`,
`JudgeFinOp/MemoFinOp.lean`) plus the judge's exact `EquationLHS`/`EquationRHS`
(from `verify.py:_equation_def`, with the `*`→`◇` normalization) and the exact
FALSE `Goal := ∃ (G:Type)(_:Magma G), EquationLHS G ∧ ¬ EquationRHS G`. It is the
judge's code made self-contained — not a hand-rolled preamble — which is what
removes the false-positive risk seen in earlier TRUE-side replicas.

## Reproduce
```bash
export AXLE_API_KEY=…                       # in ~/.openclaw/vault-bridges.env
cd evidence/will-bench
python3 gate1_axle_false.py                 # 15/15 constructed
```
For the local kernel path (Lean 4.32.2 at `~/Projects/sair-stage2-repo`), see the
`gate1_judge_false.py` harness; it needs memory headroom to build the judge modules.

## What remains unestablished by Gate 1
Private-set accuracy and the **official** organizer badge — those need an
organizer judge run on the playground. Gate 1 establishes that the FALSE
certificate *mechanism* is judge-compilable on the exact toolchain.
