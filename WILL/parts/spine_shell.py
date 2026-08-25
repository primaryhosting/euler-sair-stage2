"""WILL v6 — spine_shell: protocol + orchestration. No precomputed
per-problem/per-law data; algorithms only. Solo judge loop (EULER protocol
shell), Lean emitters, LLM tier (defensive parse, mechanical verify, judge
gate), Marathon branch (self-verified tiers ONLY), solve() orchestration.
Core provers plug in via PROVERS. Soundness invariant: no unverified exit —
FALSE tables exhaustively re-evaluated, deterministic TRUE bodies
self-rechecked (hook contract), LLM output judge-gated, Marathon writes
only self-verified answers."""

import json
import os
import random
import re
import sys
import time
from itertools import product as iproduct

# LLM contract (top-level PROMPT constant; proxy renders {problem.*} and {solver.*} attribute interpolations).

PROMPT = """You are assisting a mechanical solver for a magma equational implication problem.
The magma operator is ◇ (never *). Everything you suggest is untrusted and will be mechanically verified; bad hints are discarded, so guess boldly but precisely.

Problem {problem.id}:
  Hypothesis H : {problem.equation1}
  Goal         : {problem.equation2}

Decide whether H implies Goal in EVERY magma, and certify it.

Mechanical analysis (trusted, computed by the solver at runtime):
{solver.analysis}

Feedback from previous attempts (most recent first, truncated):
{solver.feedback}

Reply with EXACTLY ONE JSON object and nothing else. No prose, no markdown, no chain-of-thought.
Allowed replies:
{"kind":"false_table","n":3,"table":[[0,1,2],[1,2,0],[2,0,1]]}
  -- a finite magma on {0..n-1} with table[i][j] = i ◇ j that satisfies H and violates Goal. n <= 8.
{"kind":"goal_proof","proof":"intro x y z\\nhave h1 := h x x x\\n..."}
  -- a Lean 4 tactic body proving Goal from h : H (the context is: intro G _ h has already run; h names the hypothesis law). Use intro/have/calc/rw/simp/exact/grind and plain equational reasoning. Strictly banned: sorry, admit, #eval, macro, elab, syntax, unsafe, dbg_trace.
If unsure, prefer a false_table at small n; tables are verified instantly. If the analysis shows H forces collapse (a = b for all a b), prove ALLEQ via instantiations of h and finish the goal with one exact.
Escape newlines inside JSON strings as \\n."""

LLM_MODELS = ("openai/gpt-oss-120b", "google/gemma-4-31b-it")

# Protocol shell (verbatim from the proven EULER reference).

_LEAN_PREAMBLE = "import JudgeProblem\n\n"
_JUDGE_INFRA_DOWN = False


def read_msg():
    line = sys.stdin.readline()
    if not line:
        sys.exit(0)
    return json.loads(line.strip())


def send_msg(msg):
    print(json.dumps(msg), flush=True)


def _judge_result_is_infra(result):
    """Infra failfast: olean mismatch / infra errors mean no submission can pass."""
    try:
        blob = json.dumps(result)
    except Exception:
        blob = str(result)
    low = blob.lower()
    return ("incompatible header" in low) or ("JUDGE_INFRASTRUCTURE" in blob)


def call_judge(verdict, code):
    global _JUDGE_INFRA_DOWN
    if _JUDGE_INFRA_DOWN:
        return {"status": "error", "judge_code": "JUDGE_INFRASTRUCTURE_ERROR", "infra": True}
    send_msg({"call": "judge", "verdict": verdict, "code": code})
    result = read_msg()
    if _judge_result_is_infra(result):
        _JUDGE_INFRA_DOWN = True
        if isinstance(result, dict):
            result["infra"] = True
    return result


def lean_true(proof_body: str, high_heartbeats: bool = False) -> str:
    """Wrap a tactic proof body in the standard submission template."""
    hb = "set_option maxHeartbeats 12800000 in\n" if high_heartbeats else ""
    indented = "\n".join(
        "  " + line if line.strip() else ""
        for line in proof_body.strip().split("\n")
    )
    return f"import JudgeProblem\n\n{hb}def submission : Goal := by\n  intro G _ h\n{indented}\n"


def lean_false(n: int, table: list) -> str:
    """Wrap a counterexample table in the standard submission template."""
    return (
        _LEAN_PREAMBLE
        + "set_option maxRecDepth 8000 in\n"
        + f"def submission : Goal := by\n"
        + f"  let m : Magma (Fin {n}) := {{\n"
        + f"    op := finOpTable \"{json.dumps(table)}\"\n"
        + f"  }}\n  refine ⟨Fin {n}, m, ?_⟩\n  decideFin!\n"
    )


# Equation parsing and finite evaluation. CRITICAL LESSON: equations arrive with '*'; Lean defines only '◇'. Normalize at the boundary, always.

def normalise(text: str) -> str:
    """Replace ASCII * with the canonical ◇ operator."""
    return text.replace("*", "◇") if isinstance(text, str) else text


_TOKEN_RE = re.compile(r"\s*([A-Za-z_][A-Za-z0-9_']*|◇|\(|\))")


def _tokenize(s):
    out, i = [], 0
    while i < len(s):
        m = _TOKEN_RE.match(s, i)
        if not m:
            if s[i].isspace():
                i += 1
                continue
            raise ValueError(f"bad token at {i!r} in {s!r}")
        out.append(m.group(1))
        i = m.end()
    return out


def _parse_tree(tokens):
    """expr := term ('◇' term)*  (left-assoc);  term := var | '(' expr ')'"""
    pos = [0]

    def term():
        t = tokens[pos[0]]
        if t == "(":
            pos[0] += 1
            e = expr()
            if pos[0] >= len(tokens) or tokens[pos[0]] != ")":
                raise ValueError("unbalanced parens")
            pos[0] += 1
            return e
        if t in ("◇", ")"):
            raise ValueError(f"unexpected {t}")
        pos[0] += 1
        return ("v", t)

    def expr():
        left = term()
        while pos[0] < len(tokens) and tokens[pos[0]] == "◇":
            pos[0] += 1
            left = ("op", left, term())
        return left

    tree = expr()
    if pos[0] != len(tokens):
        raise ValueError("trailing tokens")
    return tree


def parse_term(text: str):
    return _parse_tree(_tokenize(normalise(text)))


def _tree_vars(tree, acc):
    if tree[0] == "v":
        if tree[1] not in acc:
            acc.append(tree[1])
    else:
        _tree_vars(tree[1], acc)
        _tree_vars(tree[2], acc)
    return acc


def variables_of(text: str):
    """Distinct variables of an equation, in order of first appearance."""
    lhs, rhs = normalise(text).split("=", 1)
    acc = _tree_vars(parse_term(lhs), [])
    return _tree_vars(parse_term(rhs), acc)


def _compile_tree(tree):
    if tree[0] == "v":
        name = tree[1]
        return lambda env, _n=name: env[_n]
    lf, rf = _compile_tree(tree[1]), _compile_tree(tree[2])
    return lambda env, _l=lf, _r=rf: env["op"](_l(env), _r(env))


def _parse_expr(text, _var_set=None):
    return _compile_tree(parse_term(text))


def compile_equation(text: str):
    """Return (variables, lhs_fn, rhs_fn) for use with check_equation."""
    vs = variables_of(text)
    lhs_text, rhs_text = normalise(text).split("=", 1)
    var_set = set(vs)
    return vs, _parse_expr(lhs_text, var_set), _parse_expr(rhs_text, var_set)


def check_equation(vs, lhs_fn, rhs_fn, n: int, op) -> bool:
    """Return True iff the equation holds for all assignments on Fin n."""
    for vals in iproduct(range(n), repeat=len(vs)):
        env = {"op": op}
        for v, val in zip(vs, vals):
            env[v] = val
        if lhs_fn(env) != rhs_fn(env):
            return False
    return True


def render(tree) -> str:
    if tree[0] == "v":
        return tree[1]
    return f"({render(tree[1])} ◇ {render(tree[2])})"


def _subst(tree, mapping):
    if tree[0] == "v":
        return ("v", mapping.get(tree[1], tree[1]))
    return ("op", _subst(tree[1], mapping), _subst(tree[2], mapping))


def _alpha_canon(ltree, rtree):
    """Rename variables by first appearance to v0, v1, ... (alpha canonical)."""
    order = _tree_vars(rtree, _tree_vars(ltree, []))
    mapping = {v: f"v{i}" for i, v in enumerate(order)}
    return _subst(ltree, mapping), _subst(rtree, mapping)


# Problem prep + mechanical self-checks.

def prep_problem(problem: dict) -> dict:
    """Normalize at the boundary and precompile everything."""
    e1 = normalise(problem.get("equation1", ""))
    e2 = normalise(problem.get("equation2", ""))
    vs1, l1, r1 = compile_equation(e1)
    vs2, l2, r2 = compile_equation(e2)
    lt1, rt1 = (parse_term(p) for p in e1.split("=", 1))
    lt2, rt2 = (parse_term(p) for p in e2.split("=", 1))
    return {
        "id": problem.get("id", "?"), "eq1": e1, "eq2": e2,
        "vs1": vs1, "l1": l1, "r1": r1, "lt1": lt1, "rt1": rt1,
        "vs2": vs2, "l2": l2, "r2": r2, "lt2": lt2, "rt2": rt2,
    }


def table_is_counterexample(prob: dict, n: int, table) -> bool:
    """FALSE-side soundness gate: H holds exhaustively AND Goal fails."""
    try:
        if not (isinstance(table, list) and len(table) == n):
            return False
        for row in table:
            if not (isinstance(row, list) and len(row) == n
                    and all(isinstance(c, int) and 0 <= c < n for c in row)):
                return False
        op = lambda a, b: table[a][b]
        return (check_equation(prob["vs1"], prob["l1"], prob["r1"], n, op)
                and not check_equation(prob["vs2"], prob["l2"], prob["r2"], n, op))
    except Exception:
        return False


def build_analysis(prob: dict) -> str:
    """Compact mechanical analysis for the LLM (computed, never stored)."""
    lines = [
        f"H uses {len(prob['vs1'])} variable(s) {prob['vs1']}; "
        f"Goal uses {len(prob['vs2'])} variable(s) {prob['vs2']}.",
    ]
    # Diagonal instance of H (all variables identified).
    diag = {v: "a" for v in prob["vs1"]}
    dl, dr = _subst(prob["lt1"], diag), _subst(prob["rt1"], diag)
    a, aa = ("v", "a"), ("op", ("v", "a"), ("v", "a"))
    if {dl, dr} == {a, aa}:
        lines.append("H at x=y=z forces idempotence: a = a ◇ a.")
    else:
        lines.append(f"H diagonal instance: {render(dl)} = {render(dr)}.")
    # Small consequences: 2-symbol substitution instances of H.
    k = len(prob["vs1"])
    if 0 < k <= 4:
        seen, out = set(), []
        for pat in iproduct("ab", repeat=k):
            m = dict(zip(prob["vs1"], pat))
            il, ir = _subst(prob["lt1"], m), _subst(prob["rt1"], m)
            if il == ir:
                continue
            s = f"{render(il)} = {render(ir)}"
            if s not in seen:
                seen.add(s)
                out.append(s)
            if len(out) >= 6:
                break
        if out:
            lines.append("Small instances of H: " + " | ".join(out))
    return "\n".join(lines)


# Deterministic tiers. PROVERS is the plug-point for the core parts (chain, completion/collapse, richer CE search). Hook contracts: ce_search(prob, deadline) -> (n, table) | None      (spine re-checks) chain(prob, deadline)      -> {"body": str, "self_verified": bool} | None completion(prob, deadline) -> {"body": str, "self_verified": bool} | None

PROVERS = {"ce_search": None, "chain": None, "completion": None}


def register_prover(name, fn):
    PROVERS[name] = fn


def trivial_true(prob: dict):
    """Self-verified TRUE: goal alpha-identical to H -> exact h; reflexive -> rfl."""
    if _alpha_canon(prob["lt2"], prob["rt2"]) == _alpha_canon(prob["lt1"], prob["rt1"]):
        return {"body": "exact h", "self_verified": True}
    if prob["lt2"] == prob["rt2"]:
        intro = ("intro " + " ".join(prob["vs2"]) + "\n") if prob["vs2"] else ""
        return {"body": intro + "rfl", "self_verified": True}
    return None


def _builtin_ce_search(prob: dict, deadline: float, max_n: int = 5):
    """Runtime CE search: exhaustive n=2,3; algebraic families + seeded random."""
    # Exhaustive n=2, n=3.
    for n in (2, 3):
        count = 0
        for cells in iproduct(range(n), repeat=n * n):
            count += 1
            if count % 64 == 0 and time.time() > deadline:
                return None
            table = [list(cells[i * n:(i + 1) * n]) for i in range(n)]
            if table_is_counterexample(prob, n, table):
                return n, table
    # Structured families: affine (a*i + b*j + c mod n), multiplicative, max/min.
    for n in range(2, max_n + 1):
        if time.time() > deadline:
            return None
        cands = []
        for a, b, c in iproduct(range(n), repeat=3):
            cands.append([[(a * i + b * j + c) % n for j in range(n)] for i in range(n)])
        for c in range(n):
            cands.append([[(i * j + c) % n for j in range(n)] for i in range(n)])
        cands.append([[max(i, j) for j in range(n)] for i in range(n)])
        cands.append([[min(i, j) for j in range(n)] for i in range(n)])
        for table in cands:
            if table_is_counterexample(prob, n, table):
                return n, table
    # Seeded random tables until the deadline.
    rng = random.Random(0)
    while time.time() < deadline:
        n = rng.randint(3, max_n)
        table = [[rng.randrange(n) for _ in range(n)] for _ in range(n)]
        if table_is_counterexample(prob, n, table):
            return n, table
    return None


def run_ce_search(prob: dict, deadline: float, max_n: int = 5):
    """Registered/built-in CE search; result ALWAYS re-checked exhaustively."""
    fn = PROVERS.get("ce_search") or _builtin_ce_search
    try:
        found = fn(prob, deadline) if fn is not _builtin_ce_search else fn(prob, deadline, max_n)
    except Exception:
        return None
    if found:
        n, table = found
        if table_is_counterexample(prob, n, table):
            return n, table
    return None


def run_hook(name: str, prob: dict, deadline: float):
    fn = PROVERS.get(name)
    if not fn:
        return None
    try:
        out = fn(prob, deadline)
    except Exception:
        return None
    if out and isinstance(out, dict) and isinstance(out.get("body"), str):
        return out
    return None


# LLM tier: defensive parsing + mechanical verification. The judge is the gate for proof bodies; tables are re-checked locally first.

_BANNED_TOKENS = ("sorry", "admit", "sorryAx", "mkSorry", "#eval", "run_tac",
                  "macro", "elab", "syntax", "unsafe", "implemented_by", "dbg_trace")


def call_llm(model=None):
    msg = {"call": "llm"}
    if model:
        msg["model"] = model
    send_msg(msg)
    res = read_msg()
    if isinstance(res, dict):
        for k in ("response", "output", "content", "text", "completion", "message"):
            v = res.get(k)
            if isinstance(v, str) and v.strip():
                return v
        return json.dumps(res)
    return str(res)


def _balanced_slice(text, start, open_ch, close_ch):
    depth = 0
    for i in range(start, len(text)):
        if text[i] == open_ch:
            depth += 1
        elif text[i] == close_ch:
            depth -= 1
            if depth == 0:
                return text[start:i + 1]
    return None


def parse_llm_reply(text):
    """Salvage one suggestion dict from a contract-violating reply; never raises."""
    if not isinstance(text, str) or not text.strip():
        return None
    body = re.sub(r"```[a-zA-Z]*", "", text).replace("```", "").strip()
    # Pass 1: any balanced JSON object containing a recognized kind.
    dec = json.JSONDecoder()
    for m in re.finditer(r"\{", body):
        try:
            obj, _ = dec.raw_decode(body, m.start())
        except Exception:
            continue
        if isinstance(obj, dict) and obj.get("kind") in ("false_table", "goal_proof"):
            return obj
    # Pass 2: regex salvage — a nested [[...]] literal is a table attempt.
    m = re.search(r"\[\s*\[", body)
    if m:
        blob = _balanced_slice(body, m.start(), "[", "]")
        if blob:
            try:
                table = json.loads(blob)
                if (isinstance(table, list) and table
                        and all(isinstance(r, list) for r in table)):
                    return {"kind": "false_table", "n": len(table), "table": table}
            except Exception:
                pass
    # Pass 3: a tactic-looking fragment is a proof attempt.
    m = re.search(r"^\s*(intro\b.*)$", body, re.S | re.M)
    if m:
        return {"kind": "goal_proof", "proof": m.group(1).strip()}
    return None


def proof_body_is_clean(bodytext: str) -> bool:
    return isinstance(bodytext, str) and bool(bodytext.strip()) and \
        not any(tok in bodytext for tok in _BANNED_TOKENS)


# Solver state (the LLM proxy interpolates {solver.analysis}/{solver.feedback}).

class SolverState:
    def __init__(self):
        self.analysis = "(not yet computed)"
        self.feedback = "(no attempts yet)"

    def push_feedback(self, note: str, cap: int = 2000):
        note = (note or "")[:800]
        self.feedback = (note + "\n---\n" + self.feedback)[:cap]


SOLVER = SolverState()


def _attempt_judge(verdict: str, code: str, S: SolverState) -> str:
    """One judge call. Returns 'accepted' | 'rejected' | 'infra'."""
    res = call_judge(verdict, code)
    if isinstance(res, dict):
        if res.get("infra"):
            S.push_feedback("judge infrastructure error — judging halted")
            return "infra"
        if res.get("status") == "accepted":
            return "accepted"
        try:
            S.push_feedback("judge rejected %s: %s" % (verdict, json.dumps(res)))
        except Exception:
            S.push_feedback("judge rejected %s (unserializable result)" % verdict)
    else:
        S.push_feedback("judge returned non-dict: %s" % str(res)[:200])
    return "rejected"


# solve(): FALSE probe -> chain -> completion/collapse -> LLM rounds -> opposite-direction fallback. Solo only (the judge gates everything).

def solve(problem: dict, budget: float) -> bool:
    t0 = time.time()
    deadline = t0 + max(60.0, min(budget, 3600.0)) - 30.0
    S = SOLVER
    try:
        prob = prep_problem(problem)
    except Exception as exc:
        S.push_feedback(f"problem parse failure: {exc}")
        return False
    S.analysis = build_analysis(prob)

    def remaining():
        return deadline - time.time()

    # Tier 0: trivial self-verified TRUE.
    triv = trivial_true(prob)
    if triv:
        if _attempt_judge("true", lean_true(triv["body"]), S) == "accepted":
            return True
        if _JUDGE_INFRA_DOWN:
            return False

    # Tier 1: cheap FALSE probe (~10s cap).
    found = run_ce_search(prob, min(deadline, time.time() + min(10.0, remaining() * 0.1)), max_n=4)
    if found:
        n, table = found
        if _attempt_judge("false", lean_false(n, table), S) == "accepted":
            return True
        if _JUDGE_INFRA_DOWN:
            return False

    # Tier 2: chain rewriting (self-rechecking hook).
    out = run_hook("chain", prob, time.time() + remaining() * 0.25)
    if out:
        if _attempt_judge("true", lean_true(out["body"]), S) == "accepted":
            return True
        if _JUDGE_INFRA_DOWN:
            return False

    # Tier 3: completion / collapse (self-rechecking hook).
    out = run_hook("completion", prob, time.time() + remaining() * 0.25)
    if out:
        if _attempt_judge("true", lean_true(out["body"], high_heartbeats=True), S) == "accepted":
            return True
        if _JUDGE_INFRA_DOWN:
            return False

    # Tier 4: one generic tactic attempt (judge-gated, costs one call).
    if remaining() > 60:
        intro = ("intro " + " ".join(prob["vs2"]) + "\n") if prob["vs2"] else ""
        if _attempt_judge("true", lean_true(intro + "grind", high_heartbeats=True), S) == "accepted":
            return True
        if _JUDGE_INFRA_DOWN:
            return False

    # Tier 5: LLM rounds (max 6), feeding judge errors back each round.
    if _llm_rounds(prob, S, t0 + (deadline - t0) * 0.85, max_rounds=6):
        return True
    if _JUDGE_INFRA_DOWN:
        return False

    # Tier 6: opposite-direction fallback — deep CE search, then hook retries.
    found = run_ce_search(prob, deadline - max(0.0, remaining() * 0.25), max_n=6)
    if found:
        n, table = found
        if _attempt_judge("false", lean_false(n, table), S) == "accepted":
            return True
        if _JUDGE_INFRA_DOWN:
            return False
    for name, hh in (("chain", False), ("completion", True)):
        out = run_hook(name, prob, deadline)
        if out:
            if _attempt_judge("true", lean_true(out["body"], high_heartbeats=hh), S) == "accepted":
                return True
            if _JUDGE_INFRA_DOWN:
                return False
    return False


def _llm_rounds(prob, S, deadline, max_rounds=6):
    for rnd in range(max_rounds):
        if time.time() > deadline or _JUDGE_INFRA_DOWN:
            return False
        try:
            reply = call_llm(LLM_MODELS[rnd % len(LLM_MODELS)])
        except SystemExit:
            raise
        except Exception as exc:
            S.push_feedback(f"llm call failed: {exc}")
            continue
        sug = parse_llm_reply(reply)
        if not sug:
            S.push_feedback("your last reply was unparseable; reply with ONE JSON object only")
            continue
        if sug.get("kind") == "false_table":
            table = sug.get("table")
            n = sug.get("n") or (len(table) if isinstance(table, list) else 0)
            if table_is_counterexample(prob, n, table):
                if _attempt_judge("false", lean_false(n, table), S) == "accepted":
                    return True
            else:
                S.push_feedback(
                    "your table failed the mechanical check (must satisfy H exhaustively and violate Goal); fix or switch strategy")
        elif sug.get("kind") == "goal_proof":
            bodytext = sug.get("proof", "")
            if not proof_body_is_clean(bodytext):
                S.push_feedback("your proof body was empty or used a banned token; rewrite it")
                continue
            if _attempt_judge("true", lean_true(bodytext, high_heartbeats=True), S) == "accepted":
                return True
        else:
            S.push_feedback(f"unknown kind {sug.get('kind')!r}; use false_table or goal_proof")
    return False


# Marathon branch: no judge at runtime -> ONLY self-verified answers are written. Deterministic tiers only; the LLM tier is disabled entirely.

def marathon():
    manifest_path = os.environ.get("JUDGE_MARATHON_MANIFEST")
    output_path = os.environ.get("JUDGE_MARATHON_OUTPUT")
    if not manifest_path or not output_path:
        return
    per_problem = float(os.environ.get("JUDGE_MARATHON_PER_PROBLEM", "60"))
    with open(manifest_path, "r", encoding="utf-8") as fh:
        lines = [ln for ln in fh.read().splitlines() if ln.strip()]
    with open(output_path, "w", encoding="utf-8") as out:
        for ln in lines:
            try:
                rec = json.loads(ln)
                problem = rec.get("problem", rec)
                ans = _marathon_solve_one(problem, time.time() + per_problem)
            except Exception:
                ans = None
            if ans:
                out.write(json.dumps(ans) + "\n")
                out.flush()


def _marathon_solve_one(problem, deadline):
    """Self-verified tiers only. Returns an answer record or None."""
    prob = prep_problem(problem)
    pid = prob["id"]
    triv = trivial_true(prob)
    if triv and triv.get("self_verified"):
        return {"id": pid, "problem_id": pid, "verdict": "true", "code": lean_true(triv["body"])}
    found = run_ce_search(prob, min(deadline, time.time() + (deadline - time.time()) * 0.6), max_n=5)
    if found:
        n, table = found  # already re-checked exhaustively by run_ce_search
        return {"id": pid, "problem_id": pid, "verdict": "false", "code": lean_false(n, table)}
    for name, hh in (("chain", False), ("completion", True)):
        out = run_hook(name, prob, deadline)
        if out and out.get("self_verified"):
            return {"id": pid, "problem_id": pid, "verdict": "true",
                    "code": lean_true(out["body"], high_heartbeats=hh)}
    return None  # no unverified exit, ever


# Entry points (verbatim protocol shape).

def main():
    startup = read_msg()
    problem = startup["problem"]
    budget = startup.get("budget", {}).get("timeout_seconds", 3600)
    solve(problem, float(budget))


def _selftest():
    """Dev-only smoke test (strippable at assembly). Exercises every public
    surface on tiny cases; prints PASS/FAIL lines."""
    ok = True

    def rep(name, cond):
        nonlocal ok
        print(("PASS " if cond else "FAIL ") + name)
        ok = ok and bool(cond)

    comm, proj = "x * y = y * x", "x * y = x"
    xor = [[0, 1], [1, 0]]
    op = lambda a, b: xor[a][b]
    vs, lf, rf = compile_equation(comm)
    v2, l2, r2 = compile_equation(proj)
    rep("normalise", normalise("x * y") == "x ◇ y")
    rep("check_eq comm on XOR", check_equation(vs, lf, rf, 2, op))
    rep("check_eq proj fails on XOR", not check_equation(v2, l2, r2, 2, op))

    prob = prep_problem({"id": "t1", "equation1": comm, "equation2": proj})
    found = run_ce_search(prob, time.time() + 5.0, max_n=3)
    rep("builtin CE search finds table", found is not None)
    if found:
        n, table = found
        cert = lean_false(n, table)
        rep("lean_false shape", "finOpTable" in cert and "decideFin!" in cert
            and cert.startswith("import JudgeProblem"))
        rep("CE independently re-checked", table_is_counterexample(prob, n, table))

    tt = trivial_true(prep_problem({"id": "t2", "equation1": comm, "equation2": "a * b = b * a"}))
    rep("trivial true: alpha-identical -> exact h", tt is not None and tt["body"] == "exact h")
    tr = trivial_true(prep_problem({"id": "t3", "equation1": comm, "equation2": "x * y = x * y"}))
    rep("trivial true: reflexive -> rfl", tr is not None and tr["body"].endswith("rfl"))
    body = lean_true("intro x y\nexact h y x")
    rep("lean_true shape", body.startswith("import JudgeProblem")
        and "intro G _ h" in body and "  intro x y" in body)

    s1 = parse_llm_reply('junk\n```json\n{"kind":"false_table","n":2,"table":[[0,0],[1,1]]}\n```\nok')
    rep("llm parse: fenced json", s1 is not None and s1["kind"] == "false_table" and s1["n"] == 2)
    s2 = parse_llm_reply("the table [[0, 1], [1, 0]] should work")
    rep("llm parse: bare table salvage", s2 is not None and s2["table"] == [[0, 1], [1, 0]])
    s3 = parse_llm_reply("intro x y z\nhave h1 := h x x x\nexact h1")
    rep("llm parse: bare tactic salvage", s3 is not None and s3["kind"] == "goal_proof")
    rep("llm parse: garbage -> None", parse_llm_reply(":-) nothing here") is None)
    rep("banned token screen", not proof_body_is_clean("intro x\nsorry")
        and proof_body_is_clean("intro x\ngrind"))

    rep("infra: olean mismatch", _judge_result_is_infra(
        {"status": "error", "detail": "Magma.olean incompatible header"}))
    rep("infra: judge code", _judge_result_is_infra({"judge_code": "JUDGE_INFRASTRUCTURE_ERROR"}))
    rep("infra: plain reject not infra", not _judge_result_is_infra(
        {"status": "rejected", "detail": "type mismatch"}))

    import tempfile
    with tempfile.TemporaryDirectory() as td:
        man, outp = os.path.join(td, "m.jsonl"), os.path.join(td, "o.jsonl")
        with open(man, "w", encoding="utf-8") as fh:
            fh.write(json.dumps({"id": "m1", "equation1": comm, "equation2": proj}) + "\n")
            fh.write(json.dumps({"problem": {"id": "m2", "equation1": "x = y",
                                             "equation2": comm}}) + "\n")
        keys = ("JUDGE_MARATHON_MANIFEST", "JUDGE_MARATHON_OUTPUT", "JUDGE_MARATHON_PER_PROBLEM")
        old = {k: os.environ.get(k) for k in keys}
        os.environ.update({keys[0]: man, keys[1]: outp, keys[2]: "5"})
        try:
            marathon()
        finally:
            for k, v in old.items():
                os.environ.pop(k, None) if v is None else os.environ.__setitem__(k, v)
        with open(outp, "r", encoding="utf-8") as fh:
            ans = [json.loads(ln) for ln in fh if ln.strip()]
        rep("marathon writes only self-verified", len(ans) == 1 and ans[0]["id"] == "m1"
            and ans[0]["verdict"] == "false" and "decideFin!" in ans[0]["code"])

    an = build_analysis(prep_problem({"id": "t4", "equation1": "x = x * x", "equation2": comm}))
    rep("analysis: idempotence detected", "idempotence" in an)
    rep("analysis: variable counts", "variable(s)" in an)

    print("SELFTEST " + ("PASS" if ok else "FAIL"))
    return ok


if __name__ == "__main__":
    if "--selftest" in sys.argv or os.environ.get("SPINE_SELFTEST"):
        sys.exit(0 if _selftest() else 1)
    if os.environ.get("JUDGE_MARATHON_MANIFEST"):
        marathon()
    else:
        main()
