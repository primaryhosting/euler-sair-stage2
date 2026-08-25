# EULER v6 — Brockian Pentagonal Engine Design Spec

**Author:** Christopher Brock, Riemann Labs
**Date:** 2026-05-18
**Status:** Draft
**Solver:** EULER v6 (Exploring Unsolved Lean Equations Relentlessly)
**Competition:** SAIR Mathematics Distillation Challenge, Stage 2

---

## 1. Goals

1. **Win the competition** — maximize score on the hidden evaluation set
2. **Publishable artifact** — demonstrate the Brockian pentagonal framework as a legitimate mathematical contribution to equational reasoning
3. **Exhaust the oracle** — pre-compute verified certificates for as much of the 22M matrix as possible, embedding them in the solver

### Success Criteria

- 200/200 on sample_200 (maintained from v5)
- \>95% on hidden evaluation set (estimated 500-2000 problems)
- All certificates kernel-verified by Lean 4 judge
- Solver file ≤ 512KB self-contained
- Paper-ready architecture that tells a coherent mathematical story

---

## 2. Competition Constraints

| Constraint | Value |
|-----------|-------|
| Solver format | Single Python file, ≤ 512KB |
| Communication | JSON stdin/stdout with judge harness |
| Available calls | `call_judge(verdict, code)`, `call_llm(context)` |
| Network access | None at runtime |
| Time budget | 3600 seconds per problem |
| True certificate | Lean 4 proof: `submission : Goal := by <tactic_body>` |
| False certificate | Finite magma on Fin n (2≤n≤8), verified by `decideFin!` |
| Allowed tactics | intro, exact, calc, have, congr_arg, .symm, .trans, simp only, rw, conv, grind |
| Banned tactics | sorry, admit, aesop, omega, decide, tauto, linarith, bare simp |

---

## 3. Problem Domain

- **4,694 named equations** over magmas (sets with one binary operation ◇)
- **22,033,636 pairwise implications** (4694 × 4694)
- **Ground truth:** 8,178,279 true (37.1%), 13,855,357 false (62.9%)
- **Source:** Tao et al., "The Equational Theories Project" (arXiv:2512.07087)
- **All 22M resolved** by Vampire (superposition, 37%) + Mace4 (finite models, 63%) + ManuallyProved (29 files)

---

## 4. The Brockian Pentagonal Classification

Every equational implication falls into one of five proof families (rays), classified by the structural relationship between hypothesis h and goal g. The classification is deterministic, runs in <1ms, and determines the entire execution path.

### 4.1 Ray Definitions

| Ray | Name | Structural Signature | Proof Character | Frequency |
|-----|------|---------------------|-----------------|-----------|
| **E** | Identity | `free_vars = 0` AND `vars(h) ⊇ vars(g)` | Goal is a direct substitution instance of h | ~19.5% of true |
| **A** | Singleton | LHS is single var NOT in RHS | h forces magma to be trivial (1 element) | ~8.5% of true |
| **B** | Constancy | `\|free_vars\| / \|vars\| > 0.3` | Free variables make RHS constant; `.symm.trans` chains | ~25% of true |
| **C** | Composition | Everything else | Multi-step calc chains, BFS, compound substitutions | ~47% of true |
| **D** | Enumeration | Oracle says "false" | Finite counterexample table on Fin n | 100% of false |

### 4.2 Classifier Implementation

```python
def classify(eq1, eq2, oracle_answer, info1):
    """Returns ordered list of (ray, confidence) tuples."""
    scores = [0.0] * 5  # E, A, B, C, D

    if oracle_answer == "false":
        scores[4] = 1.0  # Ray D dominant
    elif oracle_answer == "true":
        free = info1["rhs_only"] | info1["lhs_only"]
        lhs = info1["lhs"]
        lhs_vars = info1["lhs_vars"]
        rhs_vars = info1["rhs_vars"]

        # Ray E: direct substitution
        if not free and set(variables_of(eq1)) >= set(variables_of(eq2)):
            scores[0] = 0.9

        # Ray A: singleton collapse
        if len(lhs) == 1 and lhs in lhs_vars and lhs not in rhs_vars:
            scores[1] = 0.95

        # Ray B: constancy
        if free:
            ratio = len(free) / max(len(info1["variables"]), 1)
            scores[2] = min(0.9, ratio * 2)

        # Ray C: composition (default for remaining true)
        scores[3] = max(0.1, 1.0 - max(scores[:3]))

    else:  # unknown
        scores = [0.1, 0.1, 0.2, 0.3, 0.3]

    # Sort by score descending → traversal order
    rays = ["E", "A", "B", "C", "D"]
    ordered = sorted(range(5), key=lambda i: -scores[i])
    return [(rays[i], scores[i]) for i in ordered]
```

### 4.3 Neighbor Traversal

When the primary ray's strategies fail, the solver traverses to the next-highest-scoring ray. The classification produces a **priority-ordered list**, not a single dispatch. Each ray gets budget proportional to its score, but deterministic layers (L1-L6) are so fast that budget allocation only matters for the LLM layer (L7).

---

## 5. Pre-Computation Pipeline (Super Harvester)

The highest-ROI component. Runs offline for days before submission. Every implication solved offline is a guaranteed point at runtime.

### 5.1 Architecture

```
Phase 1: Oracle Verification     Phase 2: CE Mining
(spot-check bitmatrix)            (exhaustive + structured + random + backtrack)
         │                                  │
         ▼                                  ▼
Phase 3: Proof Mining              Phase 4: Compress & Embed
(deterministic + Axle verify)      (strategy index + tables → blob)
```

### 5.2 Phase 2: Counterexample Mining (13.8M false implications)

**Tiers (in order):**
1. Exhaustive Fin 2-3 (all 256 + 19,683 tables)
2. Structured families Fin 2-8 (~40 families: constant, projection, cyclic, XOR, max/min, polynomial, band, nilpotent)
3. Affine magmas `(a*i + b*j + c) mod p` for p ∈ {2,3,5,7}
4. Brockian bilinear `(a*i + b*j + c*i*j + d) mod p` for p ∈ {3,5}
5. Brockian quadratic (6-coefficient) for p ∈ {3,5}
6. Product tables Z_p × Z_q for composite n ∈ [4,9]
7. Near-miss mutation (random 1-2 cell flips on h-models)
8. Random search Fin 3-8 (seeded, 19K-30K attempts per size)
9. Backtracking with constraint propagation Fin 3-5 (15s per size)

**Current progress:** 685K mined, 99.98% solve rate on Tier 1-2.

**Target:** Certificates for >95% of all 13.8M false implications.

### 5.3 Phase 3: Proof Mining (8.2M true implications)

**Tiers:**
1. Deterministic engine (singleton, direct subst, constancy, constant magma, BFS)
2. Axle `check` verification (74ms per proof, ~48K/hour)
3. Tactic sweep candidates verified via Axle
4. E-prover offline (superposition → Lean term-mode translation)

**Target:** Verified certificates for >50% of all 8.2M true implications.

### 5.4 Phase 4: Compression & Embedding

**Budget:** Current solver is 284KB. 512KB limit leaves ~228KB for new data.

**Strategy:**
- **Counterexample tables** compressed: most are Fin 2-3 (tiny). At ~15 bytes average per CE, 228KB holds ~15,000 tables.
- **Proof strategy index**: store `(eq1_id, eq2_id, strategy_id, args_compressed)` at ~8 bytes per entry. 228KB holds ~29,000 entries.
- **Priority:** Embed CEs for equation pairs most likely to appear in the hidden set (high-frequency equation IDs first). Embed proofs only for cases no deterministic strategy can reconstruct at runtime.
- **Overflow:** If data exceeds 228KB, use the 512KB cheatsheet allowance as a sidecar.

---

## 6. Runtime Architecture (Layer Stack)

```
┌──────────────────────────────────────────────────────┐
│  L0  Brockian Harmonic Classifier                     │
│      → ray_order + confidence scores                  │
├──────────────────────────────────────────────────────┤
│  L1  Oracle (22M bitmatrix, 83KB compressed)          │
│      → known true/false → route direction             │
├──────────────────────────────────────────────────────┤
│  L2  Harvested Certificates (NEW in v6)               │
│      → embedded CE tables + proof strategy index      │
│      → instant lookup, zero judge calls               │
├──────────────────────────────────────────────────────┤
│  L3  Hardcoded Proofs (26 → expanded by harvester)    │
│      → exact match on (eq1_id, eq2_id)                │
├──────────────────────────────────────────────────────┤
│  L4  Ray-Dispatched Deterministic Engine               │
│      Ray E: direct subst → rfl/exact                  │
│      Ray A: singleton collapse                         │
│      Ray B: constancy engine + simp+const              │
│      Ray C: structural proofs + BFS(deep)              │
│      Ray D: CE portfolio (exhaustive + structured +    │
│             affine + Brockian + product + backtrack)    │
├──────────────────────────────────────────────────────┤
│  L5  BFS Tree-Rewrite Engine                          │
│      → bidirectional, 100K states, constancy seeding   │
│      → near-miss collection for L7 seeding             │
├──────────────────────────────────────────────────────┤
│  L5.5 Specialized Strategies                           │
│      → h_spec simp, simp+constancy, rw chains,        │
│        hybrid h+constancy calc                         │
├──────────────────────────────────────────────────────┤
│  L6  Tactic Sweep (50 candidates, grind/simp)         │
│      → invertibility patterns (Tao ManuallyProved)     │
├──────────────────────────────────────────────────────┤
│  L7  Technique-Specific LLM (ray-aware prompts)       │
│      → preflight + structured errors + .symm repair    │
│      → near-miss BFS seeding from L5                   │
│      → neighbor ray traversal on failure               │
│      → temperature ramp 0.0 → 1.0                     │
└──────────────────────────────────────────────────────┘
```

### 6.1 Layer Execution Order

For a given problem with ray_order = [C, B, D, A, E]:

1. L0: Classify → ray_order
2. L1: Oracle lookup → direction (true/false/unknown)
3. L2: Harvested certificate lookup → if hit, submit and return
4. L3: Hardcoded proof lookup → if hit, submit and return
5. L4: Run Ray C deterministic strategies (structural + BFS-light)
6. L4: If unsolved, run Ray B strategies (constancy)
7. L4: If unsolved, run Ray D strategies (CE portfolio)
8. L5: BFS tree-rewrite (deep, collect near-misses)
9. L5.5: Specialized strategies
10. L6: Tactic sweep
11. L7: LLM with Ray C prompt template (seeded with near-misses)
12. L7: If unsolved, LLM with Ray B prompt template
13. L7: If unsolved, LLM with Ray D prompt template (ask for counterexample)

---

## 7. LLM Layer Design (L7)

### 7.1 Five Technique-Specific Prompt Templates

Each ray gets a dedicated prompt template with the right worked examples, vocabulary, and strategy guidance. NOT personas — technique-specific engineering.

**Ray E template:** "This is a direct substitution problem. Find the variable mapping from h to the goal. Try `exact h <args>` first."

**Ray A template:** "The hypothesis forces a singleton magma. Derive `∀ (a b : G), a = b` from h, then apply to the goal."

**Ray B template:** "The hypothesis has free variables {free_vars}. The constancy lemma is: `have hconst : ∀ (...), {lhs} = {rhs} := (h ...).symm.trans (h ...)`. Use this to rewrite the goal." Includes pre-derived hconst with exact Lean syntax.

**Ray C template:** "This requires a multi-step calc chain. BFS found these near-miss intermediate expressions: {near_misses}. The gap between the closest approach and the goal is: {gap_analysis}. Use congr_arg to rewrite at subexpression positions." Includes the MATCH-COLLAPSE worked example.

**Ray D template:** "Produce a counterexample Cayley table on Fin N. The hypothesis is {eq1}. The table must satisfy h everywhere and violate the goal somewhere. Previous attempts failed because: {error_feedback}."

### 7.2 Near-Miss BFS → LLM Communication

This is the key innovation. When L5 (BFS) doesn't find a complete proof but gets close:

```python
near_misses = bfs_engine.collect_near_misses(eq1, eq2)
# Returns: [
#   {"expr": "(x ◇ y) ◇ ((x ◇ y) ◇ z)", "distance": 1, "path": "h x (x◇y) z"},
#   {"expr": "(x ◇ y) ◇ (z ◇ z)",        "distance": 2, "path": "..."},
# ]
```

The LLM prompt includes:
```
BFS explored 47,000 states in 12 seconds.
Closest approach: (x ◇ y) ◇ ((x ◇ y) ◇ z) — 1 rewrite from goal.
Reached via: h x (x ◇ y) z
The gap is: inner term ((x ◇ y) ◇ z) needs to become (z ◇ z).
Constancy lemma available: hconst proves ∀ a b, f(a) = f(b).
Close the gap.
```

This gives the LLM a **specific, bounded sub-problem** instead of the full open-ended proof task.

### 7.3 Error Feedback Loop

1. LLM generates proof
2. Preflight validation (catches sorry, banned tactics, placeholder types)
3. If preflight fails → structured error → retry with fix hint
4. If preflight passes → submit to judge
5. If judge rejects → parse Lean stderr → classify error type
6. If type_mismatch → deterministic .symm auto-repair (up to 4 variants)
7. If auto-repair fails → extract calc intermediates → seed BFS with them
8. If BFS finds proof from seeds → submit
9. Otherwise → feed structured error + fix hint back to LLM for next round
10. Temperature escalates: [0.0, 0.2, 0.35, 0.5, 0.65, 0.8, 0.9, 0.95, 1.0]

---

## 8. Axle API Integration (Pre-Computation Only)

### 8.1 API Details

| Field | Value |
|-------|-------|
| Endpoint | `https://axle.axiommath.ai/api/v1` |
| Auth | `Bearer <AXLE_API_KEY>` |
| Environment | `lean-4.29.0` |
| Key flag | `ignore_imports: true` (no Mathlib dependency) |
| Tools | `check` (74ms), `verify_proof` (102ms), `simplify_theorems`, `repair_proofs` |
| Rate | ~48,000 verifications/hour (single-threaded) |

### 8.2 Harvester Integration

- Phase 3 generates proof candidates via deterministic engine
- Each candidate submitted to Axle `check` for kernel verification
- Only Axle-verified proofs are embedded in the solver
- Failed proofs submitted to Axle `repair_proofs` for auto-fix attempt
- Accepted proofs optionally minimized via `simplify_theorems`

### 8.3 NOT Used at Runtime

The competition solver has no network access. Axle is purely a pre-computation tool for building verified proof artifacts.

---

## 9. Data Assets

### 9.1 Embedded in Solver (≤512KB total)

| Asset | Current Size | v6 Target |
|-------|-------------|-----------|
| Oracle bitmatrix (22M implications) | 83KB | 83KB (unchanged, verified correct) |
| Lookup table (JSON overlay) | 53KB | 53KB (may expand with errata) |
| Hardcoded proofs | ~30KB (26 proofs) | ~60KB (hundreds of proofs) |
| Harvested CE tables | 0 | ~50KB (thousands of tables) |
| Harvested proof index | 0 | ~30KB (strategy + args) |
| Solver code | ~118KB | ~140KB |
| **Total** | **~284KB** | **~416KB** |

### 9.2 External (Pre-Computation)

| Asset | Location | Size |
|-------|----------|------|
| Ground truth CSV | `/Volumes/BCC-Storage/projects/equational_theories/scripts/predictor/raw_implications.csv` | 22M cells |
| Equation definitions | `~/Downloads/equations_4694.json` | 4694 entries |
| equational_theories repo | `/Volumes/BCC-Storage/projects/equational_theories/` | 1301 Lean files |
| Harvester results | `~/openclaw-bridge/harvester/results/` | Growing |
| arXiv papers | `~/Downloads/arxiv_equational_magma_papers.json` | 89 papers |
| Knowledge vaults | `/Volumes/BCC-Storage/knowledge/riemann-labs/` | 239K docs |

---

## 10. Testing Strategy

### 10.1 Benchmarks

| Benchmark | Size | Purpose |
|-----------|------|---------|
| sample_200 | 200 problems | Regression (must maintain 200/200) |
| oracle_spot_check | 10,000 random pairs | Verify oracle + harvester accuracy |
| hard_tail | ~1000 pairs | Problems where deterministic engine fails (LLM required) |
| novel_equations | TBD | Synthetic problems outside training distribution |

### 10.2 Verification Chain

1. Deterministic engine generates candidate
2. Axle `check` verifies (offline)
3. Judge `call_judge` verifies (runtime)
4. Any disagreement between Axle and judge → flag and investigate

---

## 11. Implementation Plan (High-Level)

### Phase A: Complete Harvester Run (Days 1-5)

1. Phase 2 (CE mining) running — target 95%+ of 13.8M false
2. Launch Phase 3 (proof mining) — target 50%+ of 8.2M true
3. Phase 4 compress results into embeddable blobs

### Phase B: Build v6 Solver (Days 3-5, overlapping)

1. Add L0 Brockian classifier (10 lines)
2. Add L2 harvested certificate lookup
3. Add 6 quick-win strategies (#1 exhaustive Fin 3, #5 rw+simp, #7 XOR tables, #12 last-ditch CE, #16 direct subst .symm, #18 seeded RNG)
4. Add 5 medium strategies (#2 calc chain BFS, #3 compound calc, #4 BFS near-miss hints, #6 deep constancy, #13 MATCH-COLLAPSE prompt)
5. Implement 5 ray-specific LLM prompt templates
6. Wire near-miss BFS → LLM feedback
7. Integrate harvested blobs from Phase A

### Phase C: Validate & Submit (Days 5-7)

1. Regression test on sample_200 (must be 200/200)
2. Test on hard_tail benchmark
3. File size check (≤512KB)
4. Submit to SAIR Contributor Network
5. Write up results for whitepaper

---

## 12. Contributor Attributions

| ID | Author | Contribution |
|----|--------|-------------|
| EQT02-S00002 | SAIR "opnorm" | BFS design, constancy engine, preflight |
| EQT02-S00007 | Dufius "BringOn .7" | Counterexample-first strategy, gpt-oss-120b reference |
| — | Tao et al. | ManuallyProved corpus, equational_theories project |
| — | Axiom/Axle (Carina Hong) | Proof verification engine |
| — | Berlioz & Melliès | Latent space embedding concept (arXiv:2601.20759) |
| — | Christopher Brock | Brockian pentagonal framework, EULER solver design |

---

## 13. Risk Register

| Risk | Impact | Mitigation |
|------|--------|------------|
| Hidden set has novel equation patterns | High | Council LLM layer + diverse strategies |
| 512KB limit exceeded | High | Prioritize by equation frequency; use cheatsheet sidecar |
| Axle API unavailable during harvest | Medium | Harvest without verification; verify in batches later |
| Harvester solve rate drops on hard pairs | Medium | Add Mace4/Z3 as Tier 4-5 for stubborn cases |
| Oracle has undiscovered errata | Low | Verified 0 disagreements on full 22M matrix |
| LLM generates incorrect proofs | Low | Preflight + judge + .symm repair catch errors |
