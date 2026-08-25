# EULER v7 — Competition Solver Design

**Author:** Christopher Brock, Riemann Labs
**Date:** 2026-05-19
**Status:** Active
**Competition:** SAIR Mathematics Distillation Challenge, Stage 2
**Deadline:** August 31, 2026, 23:59 AoE

---

## 1. Competition Constraints

| Constraint | Value |
|-----------|-------|
| Solver format | Single `solver.py`, ≤500KB |
| Tracks | Solo (1 prob/process, 3600s) + Marathon (N=100, 0.5x budget) |
| Judge | Deterministic Lean 4 kernel, binary accept/reject |
| True cert | `submission : Goal := by <tactic_body>` |
| False cert | Finite magma on Fin n, verified by `decideFin!` |
| LLM | OpenRouter proxy, 65536 tokens/call |
| Scoring | Count of `accepted` verdicts, no partial credit |
| Hidden set | Unknown size, drawn from same corpus + order-5 laws |

## 2. Architecture (9-Layer Pipeline)

```
MARATHON SCHEDULER (marathon mode only)
  ├─ Difficulty estimator (structural analysis → easy/medium/hard)
  ├─ Budget tracker (time + tokens remaining)
  ├─ Lemma cache (proofs that worked on earlier problems)
  └─ Priority queue (easy first, hard last, skip if budget low)

L0   Pentagonal Classifier
     → ray_order[(ray, confidence)] for E/A/B/C/D
     → routes all subsequent layers

L0.5 Direction Predictor (for unknown oracle entries)
     → structural heuristics when oracle returns None
     → try both directions, cheapest first

L1   Oracle (22M bitmatrix, 83KB compressed)
     → true/false for known 4694×4694 pairs

L2   Harvested Certificate Cache
     → embedded CE tables (~50KB) + proof strategy index (~30KB)
     → instant lookup, zero judge calls

L3   Hardcoded Proofs (26+ verified)
     → exact (eq1_id, eq2_id) match

L4   Ray-Dispatched Deterministic Engine
     Ray E: direct substitution (exact h args / .symm)
     Ray A: singleton collapse (∀ a b, a = b)
     Ray B: constancy engine (compound subst + .symm.trans)
     Ray C: composition (multi-step calc, BFS-light)
     Ray D: CE portfolio (exhaustive Fin 2-3, structured, affine,
             Brockian bilinear/quadratic, product, random, backtrack)

L5   BFS Tree-Rewrite Engine
     → bidirectional, 100K states, constancy seeding
     → collect near-misses (1-2 rewrites from goal)
     → output: gap_analysis for L7

L6   Tactic Sweep (50 candidates)
     → grind, simp only [h], self-application, Jezek, Tao lemmas
     → each candidate submitted to judge independently

L7   Ray-Specific LLM (5 prompt templates)
     → seeded with near-misses from L5
     → structured error feedback + .symm auto-repair
     → temperature ramp: 0.0 → 0.2 → 0.5 → 0.8 → 1.0
     → preflight validation before judge submission

L8   Marathon Lemma Transfer (marathon only)
     → query lemma cache for structurally similar problems
     → prepend successful tactics to LLM context
```

## 3. Pentagonal Classifier (L0)

Classifies every implication into one of 5 rays based on structural analysis of eq1 and eq2. Runs in <1ms. Returns ordered list for neighbor traversal on failure.

| Ray | Condition | Confidence |
|-----|-----------|-----------|
| E (Identity) | `free_vars=0` AND `vars(h) ⊇ vars(g)` | 0.9 |
| A (Singleton) | LHS is single var NOT in RHS | 0.95 |
| B (Constancy) | `len(free)/len(vars) > 0.3` | ratio×2 |
| C (Composition) | Default for remaining true | 1-max(E,A,B) |
| D (Enumeration) | Oracle says false | 1.0 |

## 4. Direction Predictor (L0.5)

For equation pairs NOT in the 4694×4694 oracle (order-5 laws or novel equations):

1. **Structural heuristics**: If eq1 has fewer variables and simpler structure, guess "true" (eq1 is weaker). If eq1 has more constraints, guess "false."
2. **Quick CE probe**: Try Fin 2 exhaustive (256 tables, <50ms). If CE found → direction is "false."
3. **Quick proof probe**: Try singleton + direct_subst (<10ms). If proof found → "true."
4. **Both directions**: If neither resolves, try false first (cheaper — CE search), then true.

## 5. Harvested Certificate Cache (L2)

Embedded as compressed blobs in the solver. Two data structures:

**CE Cache**: `{(eq1_id, eq2_id) → (n, table)}` — prioritized by equation frequency in practice sets. Compressed via zlib+base64. Budget: ~50KB → ~3,000-5,000 tables.

**Proof Index**: `{(eq1_id, eq2_id) → (strategy_id, args)}` — stores reconstruction recipe, not full proof text. The deterministic engine regenerates the proof at runtime. Budget: ~30KB → ~15,000-20,000 entries.

**Priority**: Embed certificates for problems most likely in the hidden set. Use frequency analysis from practice sets (normal.jsonl, hard1-3.jsonl) to prioritize.

## 6. Ray-Specific LLM Prompts (L7)

Five distinct prompt templates, each optimized for one proof technique:

**Ray E**: "Direct substitution. Find variable mapping from h to goal. Try `exact h <args>`."
**Ray A**: "Singleton magma. Derive `∀ (a b : G), a = b` from h, then close goal."
**Ray B**: "Constancy. Free vars: {free}. Derive `have hconst : ... := (h ...).symm.trans (h ...)`. Use to rewrite."
**Ray C**: "Multi-step calc. BFS found near-misses: {near_misses}. Gap: {gap}. Use congr_arg at positions."
**Ray D**: "Find counterexample Cayley table on Fin N. h={eq1}. Table must satisfy h, violate goal."

Each template includes: allowed tactics, banned tactics, 1-2 worked examples, the specific equation pair, and BFS near-miss context (if available).

## 7. Marathon Scheduler

### Difficulty Estimation
Score each problem 0-1 before solving:
- `0.0-0.3` (easy): Oracle known + harvested cert exists, OR singleton/direct_subst likely
- `0.3-0.6` (medium): Oracle known, deterministic engine likely to solve
- `0.6-1.0` (hard): Unknown oracle, or requires LLM

### Budget Allocation
- Total: `0.5 × 100 × 600s = 30,000s` and `0.5 × 100 × 65536 = 3,276,800 tokens`
- Easy problems: 10s each (deterministic only, no LLM)
- Medium problems: 120s each, 32K tokens
- Hard problems: remaining budget split equally
- **Cutoff**: If <10% budget remains and >20% problems unsolved, skip remaining hard problems

### Lemma Cache
```python
lemma_cache = {}  # {structural_signature → [(proof_text, eq1_pattern, eq2_pattern)]}
```
After each solved problem, extract the winning proof's structural pattern and cache it. Before LLM calls on a new problem, query cache for similar patterns and prepend to prompt.

## 8. Test Harness & Build Pipeline

### Test Harness
- Clone `SAIRcompetition/equational-theories-lean-stage2`
- Run solver against: normal.jsonl (1000), hard1.jsonl (69), hard2.jsonl (200), hard3.jsonl (400)
- Track: accepted/total, time per problem, LLM tokens used, strategy distribution

### Build Pipeline
```bash
# Assemble solver from components
python3 build_solver.py  # merges components → solver.py

# Checks
wc -c solver.py  # must be ≤500KB
python3 -c "import solver"  # must parse
python3 benchmark.py --set normal --timeout 60  # quick benchmark
python3 benchmark.py --set all --timeout 3600  # full benchmark
```

### Regression Tests
- sample_200: must maintain 200/200
- normal.jsonl: track score over time
- File size: alert if >480KB

## 9. File Size Budget

| Component | Current (v5) | v7 Target |
|-----------|-------------|-----------|
| Oracle bitmatrix | 83KB | 83KB |
| Lookup table | 53KB | 53KB |
| Table bank (238 CEs) | 8KB | 8KB |
| Hardcoded proofs | 30KB | 30KB |
| Harvested CE blob | 0 | 50KB |
| Harvested proof index | 0 | 30KB |
| Solver code | 118KB | 140KB |
| **Total** | **292KB** | **394KB** |
| **Remaining** | 208KB | **106KB** |

## 10. Implementation Phases

### Phase 1: Foundation (Day 1)
1. Clone competition repo, set up test harness
2. Benchmark v5 (euler_phi.py) against ALL practice sets
3. Establish baseline scores

### Phase 2: Engine Upgrades (Days 2-3)
1. Implement L0 pentagonal classifier
2. Implement L0.5 direction predictor
3. Add 5 ray-specific LLM prompt templates
4. Wire BFS near-miss → L7 gap analysis
5. Benchmark after each upgrade

### Phase 3: Marathon Support (Day 3)
1. Marathon scheduler with difficulty estimation
2. Budget tracker
3. Lemma cache
4. Test against marathon practice set

### Phase 4: Harvester Integration (Day 4)
1. Wait for harvester Phase 2 + 3 to accumulate data
2. Run Phase 4 compression
3. Frequency-prioritize based on practice set analysis
4. Embed into solver, check ≤500KB
5. Full benchmark

### Phase 5: Polish & Submit (Day 5)
1. Regression test all practice sets
2. File size optimization if needed
3. LLM model benchmarking (test 2-3 models)
4. Submit to SAIR
5. Analyze results, iterate

## 11. Success Criteria

- **Minimum**: >90% on normal.jsonl (>900/1000)
- **Target**: >95% on normal.jsonl, >80% on hard sets
- **Stretch**: >98% on all sets
- **Regression**: 200/200 on sample_200 maintained
- **File size**: ≤500KB
- **Both tracks**: Solo and Marathon passing
