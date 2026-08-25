# EULER v4 — Competitor Technique Integration Plan

> **For agentic workers:** REQUIRED: Use superpowers:subagent-driven-development (if subagents available) or superpowers:executing-plans to implement this plan. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Upgrade EULER v3 to v4 by incorporating 6 proven techniques from SAIR Official solvers (opnorm, twophase, fewshot) and community solvers (marathon_v3), targeting novel problems that v3's deterministic layers cannot reach.

**Architecture:** Insert 3 new deterministic proof layers between Layer 2 (structural engine) and Layer 3 (tactic sweep): expression-tree BFS proof search, constancy/congr_arg proofs, and spine analysis. Upgrade Layer 4 (LLM fallback) to two-phase analysis-then-implementation with temperature escalation and error feedback. Add proof preflight to avoid wasting judge calls.

**Tech Stack:** Python 3.x (single file `solver.py`), Lean 4 tactic generation, stdin/stdout JSON judge protocol.

**Source files:**
- Current: `/Users/acutis/Desktop/solver.py` (EULER v3, 1296 lines)
- Competitor references:
  - `/tmp/solver_opnorm.py` (SAIR Official "opnorm", 186K chars)
  - `/tmp/solver_twophase.py` (SAIR Official "twophase", 179K chars)
  - `/tmp/solver_fewshot.py` (SAIR Official "fewshot", 24K chars)
  - `/tmp/solver_marathon_solver_v3.py` (back1sair "marathon_v3", 26K chars)

**Output:** `/Users/acutis/Desktop/solver_v4.py`

**Attribution convention:** Each incorporated technique gets a comment block:
```python
# ── Adapted from SAIR Official "opnorm" solver (contributor network) ──
```

---

## Chunk 1: Expression Tree Infrastructure + Proof Preflight

### Task 1: Expression Tree Parser (from opnorm)

**Files:**
- Create: `/Users/acutis/Desktop/solver_v4.py` (copy from solver.py, then modify)

EULER v3 uses string-based equation analysis. opnorm uses a proper AST (expression tree) representation that enables BFS, unification, and congr_arg generation. This is the foundation for Tasks 2-4.

- [ ] **Step 1: Copy solver.py to solver_v4.py**

```bash
cp /Users/acutis/Desktop/solver.py /Users/acutis/Desktop/solver_v4.py
```

- [ ] **Step 2: Update header to v4**

Change the docstring from "EULER v3" to "EULER v4" and update the architecture description to include the new layers:
```
Layer 2.5 BFS proof search — Bidirectional expression-tree BFS (from opnorm)
Layer 2.6 Constancy engine — congr_arg chain proofs (from opnorm)
Layer 2.7 Spine analysis   — Deep constancy via spine decomposition (from opnorm)
```

- [ ] **Step 3: Add expression tree parser after SECTION 3 (Equation Utilities)**

Port from opnorm's `parse_op_tree()`, `tree_to_str()`, `unify_tree()`, `get_subtree()`. These parse equation strings like `x ◇ (y ◇ z)` into tree tuples `('op', ('var', 'x'), ('op', ('var', 'y'), ('var', 'z')))`.

Key functions to extract from `/tmp/solver_opnorm.py`:
- `parse_op_tree(text)` → tree tuple
- `tree_to_str(tree)` → string
- `unify_tree(pattern, target, bindings)` → dict or None
- `get_subtree(tree, path)` → subtree at path like "LRL"
- `apply_rewrite_at(tree, path, new_subtree)` → new tree
- `wrap_congr_arg(tree, path, h_expr)` → Lean `congr_arg` expression

Adapt: Replace opnorm's `normalize_op_to_diamond()` calls with EULER's existing `normalise()`.

- [ ] **Step 4: Test tree parser locally**

```bash
cd /Users/acutis/Desktop && python3 -c "
from solver_v4 import parse_op_tree, tree_to_str
t = parse_op_tree('x ◇ (y ◇ z)')
print(t)
print(tree_to_str(t))
assert tree_to_str(t).replace(' ','') == 'x◇(y◇z)'
print('PASS')
"
```

- [ ] **Step 5: Commit**

---

### Task 2: Proof Preflight (from opnorm)

**Files:**
- Modify: `/Users/acutis/Desktop/solver_v4.py`

Add a preflight check before every judge submission to reject obviously broken proofs (banned tokens, unbalanced delimiters, empty proofs). Saves judge calls.

- [ ] **Step 1: Add preflight function after lean code generation section**

Port from opnorm:
- `preflight_proof(proof_text)` → bool (True = looks valid)
- `clean_proof(text)` → cleaned proof string

Key checks:
- Reject if contains `sorry`, `admit`, `native_decide`
- Reject if unbalanced parens/brackets
- Reject if empty after cleaning
- Strip markdown fences, `by` prefix, import lines

- [ ] **Step 2: Wire preflight into `_submit_true()` in `solve()`**

```python
def _submit_true(proof: str, high_hb: bool = False) -> bool:
    if not preflight_proof(proof):
        return False  # Don't waste a judge call
    r = call_judge("true", lean_true(proof, high_hb))
    return r.get("status") == "accepted"
```

- [ ] **Step 3: Add error parsing for judge rejections**

Port `parse_lean_error(message)` from opnorm — extracts the specific Lean error from judge response for feedback to LLM.

- [ ] **Step 4: Commit**

---

## Chunk 2: BFS Near-Miss Proof Search (from opnorm)

### Task 3: Bidirectional BFS Proof Engine

**Files:**
- Modify: `/Users/acutis/Desktop/solver_v4.py`

This is opnorm's most powerful deterministic technique. It searches from both sides of the goal equation simultaneously, applying h-rewrites at every subexpression, meeting in the middle to produce calc-chain proofs. Zero LLM calls.

- [ ] **Step 1: Add BFS helper functions**

Port from opnorm (insert as new SECTION 6.5):
- `_tree_size(tree)` → int
- `_subst_tree(tree, subst_dict)` → new tree
- `_all_completions(pattern_vars, goal_vars, max_depth=1)` → list of substitution dicts
- `_gen_rewrites(tree, h_lhs_tree, h_rhs_tree, h_vars, goal_vars)` → list of (new_tree, path, args, is_symm)
- `tree_norm(tree)` → canonical string for dedup

- [ ] **Step 2: Add BFS near-miss hint generator**

Port `compute_bfs_near_miss(eq1_text, eq2_text, eq1_vars, eq2_vars, max_states=5000, max_depth=3)`.

This runs a quick BFS and returns a string describing partial chains found — used as hints for LLM fallback even when BFS doesn't find a complete proof.

- [ ] **Step 3: Add bidirectional BFS proof search**

Port `try_subexpr_bfs_proof()` — the main engine:
1. Parse both equations into trees
2. Initialize forward frontier from goal_lhs, backward frontier from goal_rhs
3. At each depth, expand all frontier nodes by applying h-rewrites at every subexpression position
4. Check for meeting point (same normalized tree in both frontiers)
5. If found, reconstruct the chain and build a Lean calc proof

Key adaptation: Replace `call_judge("true", make_true_code(...))` with EULER's `call_judge("true", lean_true(...))`.

- [ ] **Step 4: Add calc-chain proof builder**

Port `_build_tree_bfs_proof()` which converts a chain of tree-level rewrites into a Lean calc proof:
```lean
intro x y
calc x ◇ y = (x ◇ x) ◇ y := congr_arg (fun a => a ◇ y) (h x x)
  _ = (x ◇ x) ◇ (y ◇ y) := congr_arg (fun a => (x ◇ x) ◇ a) (h y y).symm
```

Includes handling for:
- Simple h-step: `h args` or `(h args).symm`
- Constancy step: `(h orig_args).symm.trans (h new_args)`
- Nested congr_arg for rewrites at non-root positions

- [ ] **Step 5: Wire BFS into `solve()` as Layer 2.5**

Insert between Layer 2 (structural engine) and Layer 3 (tactic sweep):
```python
# ── Layer 2.5: BFS proof search (from opnorm) ──
if known in ("true", None):
    if try_subexpr_bfs_proof(problem, eq1, eq2):
        return "accepted"
```

- [ ] **Step 6: Test with a known hard case**

Try one of the hardcoded proof cases to verify the BFS can find it independently.

- [ ] **Step 7: Commit**

---

## Chunk 3: Constancy Engine + Spine Analysis (from opnorm)

### Task 4: Constancy Lemma Engine

**Files:**
- Modify: `/Users/acutis/Desktop/solver_v4.py`

When h has free variables (appear only on RHS), certain subexpressions become "constant" (independent of those variables). The constancy engine detects these and builds congr_arg chain proofs.

- [ ] **Step 1: Add constancy analysis functions**

Port from opnorm:
- `build_constancy_info(eq1_text, eq1_vars, eq2_vars)` → (constancy_dict, lhs_only, rhs_only)
  - constancy_dict maps variable names to their constancy proof args
- `find_constancy_step(gl_tree, gr_tree, constancy_info, default_fill)` → single step
- `find_constancy_steps(gl_tree, gr_tree, constancy_info, default_fill)` → list of steps

- [ ] **Step 2: Add constancy proof builder**

Port:
- `build_constancy_proof(intro, eq2_lhs, eq2_rhs, gl_tree, gr_tree, steps, constancy_info)` → Lean proof string
- `generate_lean_constancy_lemma(eq1_text, eq1_vars, free_var, bound_var)` → `have` statement

- [ ] **Step 3: Add constancy calc proof orchestrator**

Port `try_constancy_calc_proof()`:
1. Build constancy info from h's free variables
2. Find congr_arg steps from goal_lhs to goal_rhs
3. Build Lean proof
4. Submit to judge

- [ ] **Step 4: Wire into solve() as Layer 2.6**

```python
# ── Layer 2.6: Constancy engine (from opnorm) ──
if known in ("true", None):
    if try_constancy_calc_proof(problem, eq1, eq2):
        return "accepted"
```

- [ ] **Step 5: Commit**

---

### Task 5: Spine Analysis + Deep Constancy

**Files:**
- Modify: `/Users/acutis/Desktop/solver_v4.py`

For deeply nested equations like `x = F(G(H(x,y),z),w)`, trace the path ("spine") from root to the variable and generate reduction lemmas at each spine node.

- [ ] **Step 1: Add spine finder**

Port `find_spine(tree, var, prefix='')`:
- Recursively traces path to target variable through expression tree
- Returns list of (path, subtree) pairs from root to leaf

- [ ] **Step 2: Add deep constancy proof**

Port `try_deep_constancy_proof()`:
1. Find spine from root to LHS variable
2. For each intermediate spine node, instantiate h to get a reduction lemma
3. Chain reductions with constancy to build a multi-step proof

- [ ] **Step 3: Wire into solve() as Layer 2.7**

```python
# ── Layer 2.7: Spine analysis (from opnorm) ──
if known in ("true", None):
    if try_deep_constancy_proof(problem, eq1, eq2):
        return "accepted"
```

- [ ] **Step 4: Commit**

---

## Chunk 4: Two-Phase LLM + Temperature Escalation

### Task 6: Upgrade LLM Fallback to Two-Phase Strategy (from twophase)

**Files:**
- Modify: `/Users/acutis/Desktop/solver_v4.py`

Replace the current single-phase `llm_fallback()` with a two-phase approach:
- Phase 1: Ask LLM to ANALYZE the problem (verdict + strategy) without generating code
- Phase 2: Use that analysis to guide targeted proof/counterexample generation

- [ ] **Step 1: Add BFS near-miss hints to LLM context**

Before calling the LLM, run `compute_bfs_near_miss()` and include partial chain hints in the prompt. This gives the LLM structural insight that raw equation text doesn't provide.

- [ ] **Step 2: Rewrite llm_fallback() as two-phase**

Replace the current `llm_fallback()` with:

```python
def llm_fallback(problem, eq1, eq2, known, budget_seconds):
    # Collect search notes from prior layers
    search_notes = _collect_search_notes(eq1, eq2, known)

    # Phase 1: Analysis only (1 LLM call)
    phase1_context = {
        "phase": "1_analysis",
        "analysis": "\n".join(search_notes),
        "key_specialization": _compute_key_specializations(eq1),
    }
    phase1_result = call_llm(phase1_context)
    llm_verdict, llm_strategy = _parse_phase1(phase1_result)

    # If LLM says false, try harder counterexample search
    if llm_verdict == "false" and known != "true":
        # Extended search with more random attempts
        ...

    # Phase 2: Implementation loop with temperature escalation
    seen_answers = set()
    false_attempts = 0
    rnd = 0
    while budget_remaining(budget_seconds):
        temp = min(0.3 + rnd * 0.15, 0.9) if rnd > 0 else 0.0
        context = {
            "phase": "2_implementation",
            "analysis": "\n".join(search_notes),
            "strategy": llm_strategy,
            "target_verdict": llm_verdict,
            "temperature": temp,
        }
        # After 2+ failed false attempts, hint that it's TRUE
        if false_attempts >= 2:
            context["verdict_hint"] = "Previous counterexample attempts ALL failed. This is likely TRUE."
        ...
```

- [ ] **Step 3: Add temperature escalation**

From both twophase and marathon_v3:
```python
overrides = None
if rnd > 0:
    overrides = {"temperature": min(0.3 + rnd * 0.15, 0.9), "seed": rnd}
llm_result = call_llm(context, overrides=overrides)
```

Note: Check if the judge protocol supports `overrides` parameter. If not, include temperature in the context dict for the LLM to interpret.

- [ ] **Step 4: Add error-guided retry**

From opnorm: When judge rejects a proof, parse the error message and include it in the next LLM call:
```python
if r.get("status") != "accepted":
    err_msg = parse_lean_error(r.get("message", ""))
    search_notes.append(f"Round {rnd}: proof rejected: {err_msg[:200]}")
```

- [ ] **Step 5: Add deduplication of LLM attempts**

From twophase: Track seen proofs/tables to avoid wasting judge calls on duplicates:
```python
proof_key = proof.strip()
if proof_key in seen_answers:
    search_notes.append(f"Round {rnd}: duplicate proof, skipping")
    continue
seen_answers.add(proof_key)
```

- [ ] **Step 6: Add local counterexample verification before judge submission**

From twophase/opnorm: Before submitting a counterexample to the judge, verify it locally:
```python
# Verify counterexample locally before wasting a judge call
sat1 = check_equation(vs1, lhs1, rhs1, n, op)  # Must satisfy h
sat2 = check_equation(vs2, lhs2, rhs2, n, op)  # Must violate goal
if not sat1 or sat2:
    false_attempts += 1
    search_notes.append(f"Round {rnd}: table fails local verification")
    continue
```

- [ ] **Step 7: Commit**

---

## Chunk 5: Marathon Few-Shot Cache + Final Integration

### Task 7: Few-Shot Lemma Cache for Marathon Mode (from fewshot)

**Files:**
- Modify: `/Users/acutis/Desktop/solver_v4.py`

- [ ] **Step 1: Add difficulty scoring for marathon triage**

Port `difficulty_score()` from fewshot and merge with EULER's existing `_difficulty()`.

- [ ] **Step 2: Add few-shot pool to marathon runner**

Add an in-memory cache that accumulates successful proofs:
```python
fewshot_pool = []  # [{"prob": {...}, "proof_body": "..."}]

# After each success:
if accepted:
    fewshot_pool.append({"prob": p, "proof_body": proof})
```

- [ ] **Step 3: Add example relevance scoring**

Port from fewshot:
```python
def example_relevance(target, example):
    tgt_vars = set(variables_of(target.get("equation1","")))
    ex_vars = set(variables_of(example["prob"].get("equation1","")))
    var_overlap = len(tgt_vars & ex_vars)
    var_diff = abs(len(tgt_vars) - len(ex_vars))
    len_diff = abs(len(target.get("equation1","")) - len(example["prob"].get("equation1","")))
    return 10 * var_overlap - 3 * var_diff - len_diff / 50.0
```

- [ ] **Step 4: Add few-shot prompt injection**

When building LLM prompts in marathon mode, prepend the top-k most relevant prior wins:
```python
def build_fewshot_prompt(prob, fewshot_pool, k=3):
    if not fewshot_pool:
        return base_prompt
    ranked = sorted(fewshot_pool, key=lambda ex: example_relevance(prob, ex), reverse=True)[:k]
    # Inject as worked examples
    ...
```

- [ ] **Step 5: Commit**

---

### Task 8: Integration Testing + Attribution

**Files:**
- Modify: `/Users/acutis/Desktop/solver_v4.py`

- [ ] **Step 1: Add attribution comments to all incorporated code**

Each section from a competitor gets:
```python
# ── BFS near-miss proof search ────────────────────────────────────────────
# Adapted from SAIR Official "opnorm" solver (contributor network, May 2026)
# Original: try_subexpr_bfs_proof() — bidirectional tree BFS with unification
```

- [ ] **Step 2: Verify no `sorry`/`admit` in generated proofs**

Ensure `preflight_proof()` catches these in all code paths. The string "sorry" should only appear in:
- The preflight rejection list
- LLM prompt instructions telling the model NOT to use it

- [ ] **Step 3: Update docstring with new architecture**

```python
"""
EULER v4 — Riemann Labs SAIR Stage 2 Solver
============================================
Architecture:
  Layer 0    Oracle           — 22M implication matrix + mined lookup table
  Layer 1    Hardcoded        — Verified closed-form proofs for 26 hard true cases
  Layer 2    Structural       — Constant-magma pivot + direct substitution + singleton collapse
  Layer 2.5  BFS proof search — Bidirectional expression-tree BFS (adapted from opnorm)
  Layer 2.6  Constancy engine — congr_arg chain proofs (adapted from opnorm)
  Layer 2.7  Spine analysis   — Deep constancy via spine decomposition (adapted from opnorm)
  Layer 3    Tactic sweep     — grind/simp specialisation battery (50 candidates)
  Layer 4    Two-phase LLM    — Analyze-then-implement with temp escalation (adapted from twophase)

Contributor attributions:
  • BFS, constancy, spine, preflight: SAIR Official "opnorm" solver
  • Two-phase LLM, temp escalation: SAIR Official "twophase" solver
  • Few-shot marathon cache: SAIR Official "fewshot" solver
  • Temperature escalation: back1sair "marathon_solver_v3"
"""
```

- [ ] **Step 4: Run local validation**

```bash
python3 -c "
from solver_v4 import *
# Test tree parser
t = parse_op_tree('x ◇ (y ◇ z)')
assert tree_to_str(t).replace(' ','') == 'x◇(y◇z)'

# Test oracle still works
assert oracle(359, 4065) == 'true'

# Test hardcoded proofs still work
assert hardcoded_proof(359, 4065) is not None

# Test preflight
assert preflight_proof('intro x\n  grind') == True
assert preflight_proof('sorry') == False

# Test counterexample engine
vs, l, r = compile_equation('x ◇ y = y ◇ x')
vs2, l2, r2 = compile_equation('x ◇ y = x')
n, tbl = find_counterexample('x ◇ y = y ◇ x', 'x ◇ y = x')
assert n is not None

print('ALL TESTS PASS')
"
```

- [ ] **Step 5: Final commit**

```bash
git add solver_v4.py
git commit -m "feat: EULER v4 — integrate opnorm BFS/constancy, twophase LLM, fewshot marathon

Adapted from SAIR contributor network:
- BFS near-miss proof search (opnorm)
- Constancy engine + spine analysis (opnorm)
- Two-phase LLM strategy (twophase)
- Temperature escalation (twophase + marathon_v3)
- Few-shot lemma cache for marathon (fewshot)
- Proof preflight validation (opnorm)"
```

---

## Execution Notes

**Priority order:** Tasks 1-2-3 are the highest value (new deterministic proof strategies). Task 6 (two-phase LLM) is the highest value for novel problems. Tasks 4-5-7 are incremental improvements.

**Size estimate:** ~500-800 new lines, bringing solver_v4.py to ~1800-2100 lines.

**Key risk:** The expression tree parser must handle EULER's `◇` operator (U+25C7) correctly. opnorm uses `normalize_op_to_diamond()` which maps both `*` and `◇` to `◇`. Ensure tree_to_str outputs `◇` not `*`.

**Testing strategy:** Each new layer can be tested independently by running the solver against known hard cases from the training benchmark. The oracle tells us which problems are true/false, and the hardcoded proofs provide ground truth for the proof generation.
