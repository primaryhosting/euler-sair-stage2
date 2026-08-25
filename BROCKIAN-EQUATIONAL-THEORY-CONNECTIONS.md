# Brockian Mathematics and Equational Theory: A Pentagonal Correspondence

> Riemann Labs Research Note — May 3, 2026
> Christopher Brock

## Abstract

We observe that the five proof techniques discovered in the EULER solver for
the SAIR Mathematics Distillation Challenge naturally decompose into a
pentagonal structure analogous to the Brockian Universal Pentagonal Law.
This note documents the correspondence and proposes a harmonic scoring
function for proof strategy selection.

## 1. The Five Rays of Equational Proof

The EULER solver employs five families of proof technique, each with a
distinct algebraic character. We assign them to the five rays of the
Brockian pentagon:

| Ray | Residue (mod 5) | Technique | Algebraic Character |
|-----|-----------------|-----------|---------------------|
| E (≡0) | Identity/Trivial | Direct Instantiation | The null transformation — h IS the goal |
| A (≡1) | Singleton | Singleton Collapse | Total absorption — the magma is trivial |
| B (≡2) | Constancy | Constancy Collapse | Free variable elimination — structure washes out |
| C (≡3) | Structural | Bootstrap/Pivot | Self-referential growth — h proves its extension |
| D (≡4) | External | Classical ATP (Mace4/E) | Machine reasoning — the solver defers to oracles |

## 2. Equation Metadata Distribution

The 4,694 equations in Terry Tao's classification exhibit the following structure:

**By variable count:**
- 1 variable: 31 equations (Ray A — self-referential)
- 2 variables: 779 equations (Ray B — binary interaction)
- 3 variables: 2,090 equations (Ray C — ternary, the mode)
- 4 variables: 1,447 equations (Ray D — quaternary)
- 5 variables: 325 equations (Ray E — pentagonal completeness)
- 6 variables: 22 equations (overflow)

**Observation:** The distribution peaks at 3 variables (mod 5 ≡ 3, Ray C). This
is the "structural" ray — the ray of bootstrap and self-reference. Most equational
laws require three free symbols to express non-trivial interaction.

**Equation ID distribution mod 5:**
{0: 938, 1: 939, 2: 939, 3: 939, 4: 939}

Nearly perfectly uniform — the enumeration does not favor any ray.

## 3. Strategy Effectiveness by Ray

From the EULER solver's performance on sample_200:

| Ray | Technique | Problems Solved | % of Solved |
|-----|-----------|----------------|-------------|
| E | Identity / Hardcoded E-prover | 6 | 3.0% |
| A | Singleton | 17 | 8.5% |
| B | Constancy + Constant Magma | 50 | 25.0% |
| C | Quasi-constant + Structured Search | 123 | 61.5% |
| D | Mace4 + Exhaustive | 4 | 2.0% |
| **Total** | | **200** | **100%** |

Ray C (structured search, counterexample enumeration) dominates, accounting
for 62% of solved problems. This aligns with the Brockian framework: Ray C
is the ray of geometric-arithmetic interaction, where enumeration meets structure.

## 4. The Pentagonal Harmonic Score

We propose a harmonic scoring function H(eq1, eq2) that predicts which
proof strategy will succeed for a given equation pair:

```
H(eq1, eq2) = Σ_{r ∈ {E,A,B,C,D}} w_r · φ_r(eq1, eq2)
```

where:
- φ_E = 1 if eq1 ≡ eq2 (identity), 0 otherwise
- φ_A = 1 if eq1 forces singleton, 0 otherwise
- φ_B = |free_vars(eq1)| / |vars(eq1)| (constancy ratio)
- φ_C = 1 / (variable_count · op_depth) (searchability)
- φ_D = 1 if all other rays score 0 (defer to oracle)

The weights w_r follow the golden ratio distribution characteristic
of the Brockian pentagon:

```
w_E = φ⁰ = 1
w_A = φ¹ ≈ 1.618
w_B = φ² ≈ 2.618
w_C = φ³ ≈ 4.236
w_D = φ⁴ ≈ 6.854
```

This weighting prioritizes the structural ray (C) highest, matching
observed effectiveness. The golden ratio scaling ensures that each
successive ray captures exponentially more of the problem space.

## 5. Connection to D₅ Symmetry

The dihedral group D₅ acts on the five proof techniques through:
- **Rotation (r):** Advancing from one technique to the next in the
  proof pipeline (identity → singleton → constancy → structural → ATP)
- **Reflection (s):** Inverting the proof direction (proving ↔ disproving).
  False implications use the "reflected" version of each technique:
  - Reflected constancy = counterexample via free variable instantiation
  - Reflected structural = counterexample via magma table enumeration

The 10 elements of D₅ correspond to 10 proof/disproof strategy pairs,
exactly matching the 10 strategies currently implemented in the EULER solver.

## 6. Future Work

1. **Implement the harmonic scorer** as a strategy selection oracle
   in solver.py — predict which technique to try first, reducing
   wasted judge calls.

2. **Extend to the 22M implication matrix** — classify all pairwise
   implications by their pentagonal ray, creating a heat map of the
   equational theory landscape.

3. **Connect to Brockian number theory** — the mod 5 residue classes
   of equation IDs may correlate with proof difficulty, similar to how
   prime distribution organizes along Brockian rays.

4. **Formalize in Lean 4** — prove that the five technique families
   are exhaustive (every equational implication falls into one of
   the five rays) and that the D₅ action preserves proof structure.

## References

- Brock, C. "The Brockian Universal Pentagonal Law." (Lean 4 formalization, 2026)
- Tao, T. et al. "Equational Theories." (GitHub: teorth/equational_theories, 2024-2026)
- SAIR Foundation. "Mathematics Distillation Challenge." (2026)
