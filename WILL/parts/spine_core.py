"""spine_core — WILL v6 parser, finite evaluator, and FALSE engine.

Algorithms only. No precomputed per-problem or per-law data of any kind:
no implication matrix, no table banks, no pair-keyed certificates. Every
witness table is *computed at runtime* (exhaustive scan, structured
generators derived from closed-form formulas, or backtracking finite-model
search) and exhaustively re-verified by `self_check_false` before anything
downstream may emit it.

Operator boundary rule (the lesson that cost a measurement cycle): problem
equations arrive with '*' as the operator; Lean defines only '◇'. Every
public entry point normalises at the boundary via `normalise`. The internal
term representation is operator-free: a term is either a variable name
(str) or a pair (left_term, right_term) meaning left ◇ right.

Table convention: a witness is (n, table) with table a row-major list of n
lists of n ints — table[i][j] == i ◇ j. This is the shape the protocol
reference's `lean_false(n, table)` json.dumps's into `finOpTable`.

Pure Python 3.11 stdlib. Import-safe (no side effects at import).
"""

from itertools import product as _iproduct
import time as _time

__all__ = [
    "normalise", "parse_equation", "variables_of",
    "compile_equation", "check_equation",
    "term_to_str", "eval_term",
    "table_satisfies", "table_violates",
    "self_check_false", "find_counterexample",
]

OP = "◇"  # ◇


# ---------------------------------------------------------------------------
# Boundary normalisation + parser
# ---------------------------------------------------------------------------

def normalise(text: str) -> str:
    """Replace ASCII * with the canonical ◇ operator. Boundary rule: every
    public entry point calls this before touching the text."""
    return text.replace("*", OP) if isinstance(text, str) else text


def _tokenize(text: str):
    toks, i, n = [], 0, len(text)
    while i < n:
        c = text[i]
        if c.isspace():
            i += 1
        elif c in "()" or c == OP or c == "=":
            toks.append(c)
            i += 1
        elif c.isalnum() or c == "_" or c == "'":
            j = i
            while j < n and (text[j].isalnum() or text[j] in "_'"):
                j += 1
            toks.append(text[i:j])
            i = j
        else:
            raise ValueError(f"unexpected character {c!r} in equation")
    return toks


def _parse_term(toks, pos):
    """term := atom (OP atom)*   (left-associative). Returns (term, pos)."""
    node, pos = _parse_atom(toks, pos)
    while pos < len(toks) and toks[pos] == OP:
        rhs, pos = _parse_atom(toks, pos + 1)
        node = (node, rhs)
    return node, pos


def _parse_atom(toks, pos):
    if pos >= len(toks):
        raise ValueError("unexpected end of equation")
    t = toks[pos]
    if t == "(":
        node, pos = _parse_term(toks, pos + 1)
        if pos >= len(toks) or toks[pos] != ")":
            raise ValueError("missing ')'")
        return node, pos + 1
    if t in (")", OP, "="):
        raise ValueError(f"unexpected token {t!r}")
    return t, pos + 1  # variable


def parse_equation(text: str):
    """Parse 'lhs = rhs' (with * or ◇) into a pair of term trees."""
    toks = _tokenize(normalise(text))
    if "=" not in toks:
        raise ValueError("equation has no '='")
    cut = toks.index("=")
    lhs, p = _parse_term(toks[:cut], 0)
    if p != cut:
        raise ValueError("trailing tokens on LHS")
    rtoks = toks[cut + 1:]
    rhs, p = _parse_term(rtoks, 0)
    if p != len(rtoks):
        raise ValueError("trailing tokens on RHS")
    return lhs, rhs


def _collect_vars(term, seen, order):
    if isinstance(term, str):
        if term not in seen:
            seen.add(term)
            order.append(term)
    else:
        _collect_vars(term[0], seen, order)
        _collect_vars(term[1], seen, order)


def variables_of(text: str):
    """Variables of an equation, in order of first appearance."""
    lhs, rhs = parse_equation(text)
    seen, order = set(), []
    _collect_vars(lhs, seen, order)
    _collect_vars(rhs, seen, order)
    return order


def term_to_str(term) -> str:
    if isinstance(term, str):
        return term
    return f"({term_to_str(term[0])} {OP} {term_to_str(term[1])})"


# ---------------------------------------------------------------------------
# Evaluators (semantics copied from the protocol reference)
# ---------------------------------------------------------------------------

def _compile_term(term):
    """Term tree -> closure(env) with env = {'op': fn, var: val, ...}."""
    if isinstance(term, str):
        name = term
        return lambda env: env[name]
    lf, rf = _compile_term(term[0]), _compile_term(term[1])
    return lambda env: env["op"](lf(env), rf(env))


def compile_equation(text: str):
    """Return (variables, lhs_fn, rhs_fn) for use with check_equation.
    Signature and semantics match the protocol reference."""
    lhs, rhs = parse_equation(text)
    seen, vs = set(), []
    _collect_vars(lhs, seen, vs)
    _collect_vars(rhs, seen, vs)
    return vs, _compile_term(lhs), _compile_term(rhs)


def check_equation(vs, lhs_fn, rhs_fn, n: int, op) -> bool:
    """True iff the equation holds for ALL assignments on Fin n (exhaustive,
    no sampling — the same finite semantics the judge re-decides)."""
    for vals in _iproduct(range(n), repeat=len(vs)):
        env = {"op": op}
        for v, val in zip(vs, vals):
            env[v] = val
        if lhs_fn(env) != rhs_fn(env):
            return False
    return True


def eval_term(term, env, table):
    """Evaluate a term tree under env (var -> value) and a possibly PARTIAL
    table (unassigned cells are None). Returns a value or None."""
    if isinstance(term, str):
        return env[term]
    a = eval_term(term[0], env, table)
    if a is None:
        return None
    b = eval_term(term[1], env, table)
    if b is None:
        return None
    return table[a][b]


def _compiled(eq_text):
    """(vs, lhs_tree, rhs_tree, lhs_fn, rhs_fn) for one equation."""
    lhs, rhs = parse_equation(eq_text)
    seen, vs = set(), []
    _collect_vars(lhs, seen, vs)
    _collect_vars(rhs, seen, vs)
    return vs, lhs, rhs, _compile_term(lhs), _compile_term(rhs)


def table_satisfies(eq_text: str, n: int, table) -> bool:
    """Exhaustive: does (Fin n, table) satisfy the law?"""
    vs, lf, rf = compile_equation(eq_text)
    return check_equation(vs, lf, rf, n, lambda a, b: table[a][b])


def table_violates(eq_text: str, n: int, table) -> bool:
    """Exhaustive: does some assignment falsify the law on (Fin n, table)?"""
    return not table_satisfies(eq_text, n, table)


# ---------------------------------------------------------------------------
# Soundness gate — nothing is emitted without passing this
# ---------------------------------------------------------------------------

def self_check_false(eq1: str, eq2: str, n: int, table) -> bool:
    """Independent pre-emission check for a FALSE witness: (Fin n, table)
    must satisfy eq1 exhaustively AND violate eq2. Also validates shape.
    Every candidate from every search path must pass here before emission."""
    if not isinstance(n, int) or n < 1:
        return False
    if len(table) != n or any(len(row) != n for row in table):
        return False
    for row in table:
        for v in row:
            if not isinstance(v, int) or not (0 <= v < n):
                return False
    return table_satisfies(eq1, n, table) and table_violates(eq2, n, table)


# ---------------------------------------------------------------------------
# FALSE engine — counterexample search (algorithms only)
# ---------------------------------------------------------------------------

def _try_table(c1, c2, n, table):
    """Fast accept test using precompiled equations. c = (vs,lt,rt,lf,rf)."""
    op = lambda a, b: table[a][b]
    if not check_equation(c1[0], c1[3], c1[4], n, op):
        return False
    return not check_equation(c2[0], c2[3], c2[4], n, op)


def _exhaustive_order(c1, c2, n, deadline):
    """Enumerate ALL n^(n*n) tables of order n (use only for n <= 3)."""
    rng = range(n)
    count = 0
    for flat in _iproduct(rng, repeat=n * n):
        count += 1
        if count % 1024 == 0 and _time.monotonic() > deadline:
            return None
        table = [list(flat[i * n:(i + 1) * n]) for i in rng]
        if _try_table(c1, c2, n, table):
            return table
    return None


def _structured_generators():
    """Yield (n, table) candidates computed from closed-form formulas at
    runtime. No stored tables: each is generated from a formula family.

    Families: projections, constants, affine (a*i + b*j + c) mod p, and
    bilinear (a*i*j + b*i + c*j + d) mod p, for p in {2, 3, 5}."""
    for n in (2, 3, 4, 5, 6):
        r = range(n)
        yield n, [[i for _ in r] for i in r]           # left projection
        yield n, [[j for j in r] for _ in r]           # right projection
        for c in r:                                    # constants
            yield n, [[c for _ in r] for _ in r]
    for p in (2, 3, 5):
        r = range(p)
        for a in r:
            for b in r:
                for c in r:
                    yield p, [[(a * i + b * j + c) % p for j in r] for i in r]
        for a in r:
            for b in r:
                for c in r:
                    for d in r:
                        yield p, [[(a * i * j + b * i + c * j + d) % p
                                   for j in r] for i in r]


def _assignments(vs, n):
    """All variable assignments (as dicts) for a law over Fin n."""
    return [dict(zip(vs, vals)) for vals in _iproduct(range(n), repeat=len(vs))]


def _cell_order(n):
    """Concentric ('square-by-square') cell order — pairs with the least
    number heuristic for sound isomorphism symmetry breaking."""
    cells = []
    for k in range(n):
        for j in range(k):
            cells.append((k, j))
        for i in range(k):
            cells.append((i, k))
        cells.append((k, k))
    return cells


def _search_order(c1, c2, n, deadline, node_budget=2_000_000):
    """Bounded backtracking finite-model search at order n with forward
    checking and least-number symmetry breaking. Enumerates models of eq1;
    each completed model is tested against eq2. Returns a table or None.

    Sound and complete up to isomorphism within the node/time budget; makes
    no completeness claim when the budget exhausts."""
    vs1, l1, r1 = c1[0], c1[1], c1[2]
    envs1 = _assignments(vs1, n)
    cells = _cell_order(n)
    ncells = len(cells)
    table = [[None] * n for _ in range(n)]
    nodes = 0

    def propagate(pending):
        """Re-evaluate unresolved eq1 instances against the partial table.
        Returns surviving pending list, or None on a definite conflict."""
        keep = []
        for env in pending:
            a = eval_term(l1, env, table)
            b = eval_term(r1, env, table)
            if a is None or b is None:
                keep.append(env)      # still undetermined
            elif a != b:
                return None           # definite eq1 violation -> prune
            # determined and equal: resolved, drop
        return keep

    def rec(depth, mx, pending):
        nonlocal nodes
        if depth == ncells:
            # complete eq1-model; accept iff eq2 fails somewhere
            op = lambda a, b: table[a][b]
            if not check_equation(c2[0], c2[3], c2[4], n, op):
                return [row[:] for row in table]
            return None
        i, j = cells[depth]
        m = max(mx, i, j)
        vmax = min(n - 1, m + 1)      # least number heuristic
        for v in range(vmax + 1):
            nodes += 1
            if nodes > node_budget:
                return None
            if nodes % 256 == 0 and _time.monotonic() > deadline:
                return None
            table[i][j] = v
            surv = propagate(pending)
            if surv is not None:
                got = rec(depth + 1, max(m, v), surv)
                if got is not None:
                    return got
            table[i][j] = None
            if nodes > node_budget or _time.monotonic() > deadline:
                return None
        return None

    return rec(0, -1, envs1)


def find_counterexample(eq1: str, eq2: str, max_order: int = 6,
                        deadline_s: float = 60.0):
    """Search for a finite magma satisfying eq1 and violating eq2.

    Pipeline (all computed at runtime, no stored data):
      1. exhaustive scan of every table at orders 2 and 3;
      2. structured generators (projections, constants, affine and bilinear
         formulas mod 2/3/5);
      3. bounded backtracking finite-model search at orders 4..max_order
         with forward checking and least-number symmetry breaking.

    Returns (n, table) — guaranteed to pass self_check_false — or None.
    None means 'not found within budget', never 'the implication is TRUE'."""
    eq1, eq2 = normalise(eq1), normalise(eq2)
    t0 = _time.monotonic()
    deadline = t0 + deadline_s
    c1, c2 = _compiled(eq1), _compiled(eq2)

    def gate(n, table):
        if table is not None and self_check_false(eq1, eq2, n, table):
            return n, table
        return None

    # Tier 1: exhaustive small orders.
    for n in (2, 3):
        if n > max_order or _time.monotonic() > deadline:
            break
        got = gate(n, _exhaustive_order(c1, c2, n, deadline))
        if got:
            return got

    # Tier 2: structured generators.
    for n, table in _structured_generators():
        if n > max_order:
            continue
        if _time.monotonic() > deadline:
            break
        if _try_table(c1, c2, n, table):
            got = gate(n, table)
            if got:
                return got

    # Tier 3: backtracking finite-model search, orders 4..max_order.
    orders = [n for n in range(4, max_order + 1)]
    for idx, n in enumerate(orders):
        now = _time.monotonic()
        if now > deadline:
            break
        # split remaining time evenly across remaining orders, keep a tail
        slice_end = now + (deadline - now) / (len(orders) - idx)
        got = gate(n, _search_order(c1, c2, n, min(slice_end, deadline)))
        if got:
            return got
    return None


# ---------------------------------------------------------------------------
# Self-test
# ---------------------------------------------------------------------------

def _selftest():
    ok = True

    def report(name, cond):
        nonlocal ok
        print(("PASS" if cond else "FAIL") + f"  {name}")
        ok = ok and cond

    # 1. Parser + boundary normalisation + evaluator on projections.
    left_proj = "x * y = x"
    t = [[0, 0], [1, 1]]                       # i ◇ j = i
    report("parse/normalise variables", variables_of("x = (y * x) * ((x * z) * z)") == ["x", "y", "z"])
    report("evaluator: left projection satisfies x◇y=x", table_satisfies(left_proj, 2, t))
    report("evaluator: left projection violates x◇y=y", table_violates("x * y = y", 2, t))

    # 2. Exhaustive tier: commutative but not associative (order 2 exists).
    got = find_counterexample("x * y = y * x", "(x * y) * z = x * (y * z)",
                              max_order=3, deadline_s=20.0)
    report("exhaustive tier finds comm-not-assoc witness",
           got is not None and self_check_false("x * y = y * x",
                                                "(x * y) * z = x * (y * z)",
                                                got[0], got[1]))

    # 3. TRUE implication: no witness may ever be found.
    got = find_counterexample("x * y = y * x", "y * x = x * y",
                              max_order=3, deadline_s=5.0)
    report("no witness for a TRUE implication", got is None)

    # 4. Backtracking tier directly at order 4 (skipping small orders).
    c1 = _compiled(normalise("x * y = y * x"))
    c2 = _compiled(normalise("(x * y) * z = x * (y * z)"))
    tbl = _search_order(c1, c2, 4, _time.monotonic() + 30.0)
    report("backtracking search finds order-4 witness",
           tbl is not None and self_check_false("x * y = y * x",
                                                "(x * y) * z = x * (y * z)", 4, tbl))

    # 5. self_check_false rejects a bad witness (table violating eq1).
    bad = [[1, 0], [0, 0]]  # not left projection
    report("self_check_false rejects invalid witness",
           not self_check_false(left_proj, "x * y = y", 2, bad))

    # 6. check_equation matches reference semantics with op-in-env.
    vs, lf, rf = compile_equation("x * (y * z) = (x * y) * z")
    report("check_equation on Z2 addition (associative)",
           check_equation(vs, lf, rf, 2, lambda a, b: (a + b) % 2))

    print("SELFTEST " + ("PASS" if ok else "FAIL"))
    return ok


if __name__ == "__main__":
    import sys
    sys.exit(0 if _selftest() else 1)
