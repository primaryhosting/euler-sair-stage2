# Riemann Labs — Equational Theory Proofs

Five exemplar proofs for the SAIR Mathematics Distillation Challenge (Stage 2),
demonstrating Riemann Labs' approach to automated equational reasoning over magmas.

Each proof is a standalone Lean 4 file that compiles against the competition judge.
The proofs are ordered by technique, from the simplest to the most compositional.

## The Five Techniques

| # | File | Equation Pair | Technique |
|---|------|--------------|-----------|
| 1 | `RiemannLabs_Proof_1_Constancy.lean` | 3268 -> 3253 | Direct constancy substitution |
| 2 | `RiemannLabs_Proof_2_ConstantCollapse.lean` | 3829 -> 41 | Constant magma via transitivity |
| 3 | `RiemannLabs_Proof_3_Bootstrap.lean` | 359 -> 4065 | Self-referential bootstrap (congr_arg) |
| 4 | `RiemannLabs_Proof_4_Pivot.lean` | 404 -> 4236 | Shared pivot (.trans .symm) |
| 5 | `RiemannLabs_Proof_5_CompoundSubstitution.lean` | 282 -> 2133 | Compound term substitution |

## Proof Philosophy

These proofs follow three principles:

1. **Constancy first.** When a hypothesis has universally quantified variables
   appearing on only one side, those variables are free parameters. The proof
   begins by choosing their values strategically.

2. **Transitivity as the fundamental connective.** Every chain of equational
   reasoning reduces to `.trans` and `.symm` — forward steps and backward steps
   through a shared intermediate value.

3. **Structure absorption.** The deepest proofs substitute compound terms
   (products, iterated applications) for free variables. The magma operation
   appears inside its own proof, weaving new algebraic structure into the
   equation's fabric.

## Competition Context

- **Competition:** SAIR Mathematics Distillation Challenge, Stage 2
- **Domain:** 4,694 equational laws over magmas (sets with one binary operation)
- **Task:** Prove or disprove ~22 million pairwise implications
- **Verification:** Lean 4 kernel (machine-checked, zero trust)

## About Riemann Labs

Riemann Labs is the mathematical research division of the Brock Command Center,
focused on formal verification, automated reasoning, and the intersection of
algebraic structure with computational proof.

@Aristotle-Harmonic
