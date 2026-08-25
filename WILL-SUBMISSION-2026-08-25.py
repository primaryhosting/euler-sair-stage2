# ─── EMBEDDED-DATA DISCLOSURE (SAIR Stage 2, required) ──────────────────────
# WILL embeds NO lookup tables, NO implication matrix, NO answer banks, and NO
# per-problem certificates. The only embedded payload is its own PROMPT constant
# — a prompt teaching technique, whose three worked demonstrations are explicitly
# framed as re-derivable illustrations of moves, not memorized verdicts. There is
# no compressed data blob to disclose. (Sibling entry EULER embeds the public
# ETP implication data; WILL deliberately carries none of it.)
# ────────────────────────────────────────────────────────────────────────────
# ============================================================================
# WILL v6 — walk in without it. Be elegance in action.
# ----------------------------------------------------------------------------
# Second SAIR Stage-2 entry from Riemann Labs; sibling to EULER, not a fork.
# No oracle: no implication matrix, no direction lookup, no answer banks.
# No banks: no table banks, no lookup blobs, no pair-keyed certificates.
# No borrowed proofs: every Lean body is constructed here, at runtime.
# The one embedded payload is the PROMPT constant, which carries three worked
# teaching examples of the moves — concrete (H, Goal, verdict) triples, but
# re-derived by technique, not retrieved from a table. Disclosed, not hidden.
# Technique only: chain rewriting, bounded Knuth-Bendix completion, ALLEQ
# collapse construction, and counterexample search whose structured
# generators are computed from the formulas in hand — never stored.
# Every exit verified: FALSE tables exhaustively re-evaluated, TRUE chains
# independently re-walked, LLM output judge-gated, Marathon self-verified only.
# The line is principled: sediment = data, technique = code.
# Expected to score below the flagship — and that is the point.
# ============================================================================

import heapq
import itertools
import json
import os
import random
import re
import sys
import time
from collections import namedtuple
from itertools import product as iproduct

# ============================================================================
# PROMPT — the top-level LLM contract. The proxy renders {problem.*} and
# {solver.*} attribute interpolations; the literal JSON braces below are not
# interpolation slots. Models: openai/gpt-oss-120b, google/gemma-4-31b-it.
# ============================================================================

PROMPT = r"""You are WILL, a proof strategist for magma equational logic. You carry no lookup tables and no answer banks — only technique, and the three worked examples below, which are illustrations of the moves you re-derive, not answers to retrieve. Walk in without it. Be elegance in action.

A magma is a set G with one binary operation ◇ (problems may print it as *; treat * and ◇ as the same symbol, and always write ◇ in your output). Decide whether every magma satisfying H also satisfies the Goal.

Problem {problem.id}
  H    : {problem.equation1}
  Goal : {problem.equation2}

Machine analysis (trusted, computed at runtime):
{solver.analysis}

What already failed (do not repeat these verbatim):
{solver.feedback}

Reply with EXACTLY one JSON object. No prose, no markdown, no reasoning text before or after. Two shapes only:

  {"verdict":"true","proof":"<Lean tactic body>","check":"<load-bearing instantiations of h>","lemma":"<optional bridge equation>"}
  {"verdict":"false","table":[[...],[...]],"check":"<breaking assignment with both sides computed>"}

Rules for "proof": it is inserted after `intro G _ h`, where `h : H`. Begin with `intro x y z ...` — one variable per Goal variable, in order. Use only: intro, have, calc, rw, exact, .trans, .symm, congrArg. Never sorry, never #eval, no imports, no `def`. Escape newlines as \n inside the JSON string. Rules for "table": table[i][j] = i ◇ j, entries in 0..n-1, n ≤ 4. It must satisfy H at EVERY assignment and break the Goal at SOME assignment — check every cell before you answer. Rules for "check" (mandatory): for "false", name the breaking assignment with both sides computed (e.g. "x=0,y=1: LHS=0, RHS=1"); for "true", name the instantiations of h your proof stands on. Compute it against THIS problem's H — if you cannot fill it honestly, your answer is wrong. Rules for "lemma": one equation over x y z and ◇; the solver will itself try to prove H ⇒ lemma and H + lemma ⇒ Goal. Offer it only when you cannot finish directly.

Three demonstrations of the moves. These are illustrations of technique, not
answers to look up — each is re-derived from the method in front of you, and you
must do the same for the real problem, which will differ. Learn the MOVE, not the pair.

1. Collapse — the crown move. Illustrated on H: x = y ◇ y, Goal: x = (y ◇ x) ◇ z.
   See it: h a a : a = a ◇ a and h b a : b = a ◇ a, so a = b — the magma has one element, and ANY goal is an instance.
   {"verdict":"true","proof":"intro x y z\nhave ALLEQ : ∀ a b : G, a = b := fun a b => (h a a).trans (h b a).symm\nexact ALLEQ x ((y ◇ x) ◇ z)","check":"h a a : a = a ◇ a; h b a : b = a ◇ a; chained give a = b"}
   Whenever H forces all elements equal (projection laws like a = a ◇ b, constant laws, squashing laws), prove ALLEQ first; the goal then falls to one `exact ALLEQ _ _`. Never try to rewrite your way to a collapse goal — rewriting proves reachability; collapse must be constructed from instantiations of h chained with .trans and .symm.

2. Chain. Illustrated on H: x ◇ y = y, Goal: (x ◇ y) ◇ z = z.
   See it: rewrite with h twice, walking the left side down to the right.
   {"verdict":"true","proof":"intro x y z\ncalc (x ◇ y) ◇ z = y ◇ z := by rw [h x y]\n  _ = z := h y z","check":"h x y : x ◇ y = y; h y z : y ◇ z = z"}
   Most true implications are short chains: instantiate h at chosen arguments and walk one side of the Goal to the other in a calc. Choose instantiations by matching subterms of the Goal against one side of H.

3. Countermodel. Illustrated on H: x ◇ y = y ◇ x, Goal: x ◇ x = x.
   See it: any symmetric table is commutative; make one diagonal cell disobey idempotence.
   {"verdict":"false","table":[[1,0],[0,0]],"check":"x=0: LHS=0◇0=1, RHS=0 — Goal breaks; table symmetric so H holds at all 4 assignments"}
   Check: the table is symmetric, so H holds at all 4 assignments; 0 ◇ 0 = 1 ≠ 0 breaks the Goal. Prefer n = 2 or 3. Try constant tables, projections (table[i][j] = i or j), cyclic tables ((i + j) mod n), then perturb one cell and re-check H everywhere.

Method, in that order: (1) if a tiny table satisfies H and breaks the Goal, answer false with it; (2) ask whether H forces ALLEQ — if yes, construct it and finish in one exact; (3) hunt a calc chain; (4) if you see a plausible stepping stone but cannot finish, send your best direct attempt plus the stepping stone in "lemma".

Before you answer, run this mechanical scan: scan your finished proof for any * and rewrite it to ◇; fully parenthesize every ◇ application.

Your answer is mechanically verified before use; a wrong table or a broken proof is simply discarded. A precise small answer beats an ambitious broken one.

One JSON object. Nothing else."""

# ============================================================================
# SHARED BOUNDARY — the operator lesson that cost a measurement cycle:
# problem equations arrive with '*'; Lean defines only '◇'. Normalise at the
# boundary, always. One definition, used by every section below.
# ============================================================================

OP = "◇"


def normalise(text):
    """Replace ASCII '*' with the canonical ◇ operator (boundary rule)."""
    return text.replace("*", OP) if isinstance(text, str) else text


# ============================================================================
# SECTION 1 — spine_core: parser, finite evaluator, FALSE engine
# ============================================================================

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

# ---------------------------------------------------------------------------
# Boundary normalisation + parser
# ---------------------------------------------------------------------------

def _c_tokenize(text: str):
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


def core_parse_equation(text: str):
    """Parse 'lhs = rhs' (with * or ◇) into a pair of term trees."""
    toks = _c_tokenize(normalise(text))
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


def core_variables_of(text: str):
    """Variables of an equation, in order of first appearance."""
    lhs, rhs = core_parse_equation(text)
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


def core_compile_equation(text: str):
    """Return (variables, lhs_fn, rhs_fn) for use with core_check_equation.
    Signature and semantics match the protocol reference."""
    lhs, rhs = core_parse_equation(text)
    seen, vs = set(), []
    _collect_vars(lhs, seen, vs)
    _collect_vars(rhs, seen, vs)
    return vs, _compile_term(lhs), _compile_term(rhs)


def core_check_equation(vs, lhs_fn, rhs_fn, n: int, op) -> bool:
    """True iff the equation holds for ALL assignments on Fin n (exhaustive,
    no sampling — the same finite semantics the judge re-decides)."""
    for vals in iproduct(range(n), repeat=len(vs)):
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
    lhs, rhs = core_parse_equation(eq_text)
    seen, vs = set(), []
    _collect_vars(lhs, seen, vs)
    _collect_vars(rhs, seen, vs)
    return vs, lhs, rhs, _compile_term(lhs), _compile_term(rhs)


def table_satisfies(eq_text: str, n: int, table) -> bool:
    """Exhaustive: does (Fin n, table) satisfy the law?"""
    vs, lf, rf = core_compile_equation(eq_text)
    return core_check_equation(vs, lf, rf, n, lambda a, b: table[a][b])


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
    if not core_check_equation(c1[0], c1[3], c1[4], n, op):
        return False
    return not core_check_equation(c2[0], c2[3], c2[4], n, op)


def _exhaustive_order(c1, c2, n, deadline):
    """Enumerate ALL n^(n*n) tables of order n (use only for n <= 3)."""
    rng = range(n)
    count = 0
    for flat in iproduct(rng, repeat=n * n):
        count += 1
        if count % 1024 == 0 and time.monotonic() > deadline:
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
    return [dict(zip(vs, vals)) for vals in iproduct(range(n), repeat=len(vs))]


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
            if not core_check_equation(c2[0], c2[3], c2[4], n, op):
                return [row[:] for row in table]
            return None
        i, j = cells[depth]
        m = max(mx, i, j)
        vmax = min(n - 1, m + 1)      # least number heuristic
        for v in range(vmax + 1):
            nodes += 1
            if nodes > node_budget:
                return None
            if nodes % 256 == 0 and time.monotonic() > deadline:
                return None
            table[i][j] = v
            surv = propagate(pending)
            if surv is not None:
                got = rec(depth + 1, max(m, v), surv)
                if got is not None:
                    return got
            table[i][j] = None
            if nodes > node_budget or time.monotonic() > deadline:
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
    t0 = time.monotonic()
    deadline = t0 + deadline_s
    c1, c2 = _compiled(eq1), _compiled(eq2)

    def gate(n, table):
        if table is not None and self_check_false(eq1, eq2, n, table):
            return n, table
        return None

    # Tier 1: exhaustive small orders.
    for n in (2, 3):
        if n > max_order or time.monotonic() > deadline:
            break
        got = gate(n, _exhaustive_order(c1, c2, n, deadline))
        if got:
            return got

    # Tier 2: structured generators.
    for n, table in _structured_generators():
        if n > max_order:
            continue
        if time.monotonic() > deadline:
            break
        if _try_table(c1, c2, n, table):
            got = gate(n, table)
            if got:
                return got

    # Tier 3: backtracking finite-model search, orders 4..max_order.
    orders = [n for n in range(4, max_order + 1)]
    for idx, n in enumerate(orders):
        now = time.monotonic()
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

def _selftest_core():
    ok = True

    def report(name, cond):
        nonlocal ok
        print(("PASS" if cond else "FAIL") + f"  {name}")
        ok = ok and cond

    # 1. Parser + boundary normalisation + evaluator on projections.
    left_proj = "x * y = x"
    t = [[0, 0], [1, 1]]                       # i ◇ j = i
    report("parse/normalise variables", core_variables_of("x = (y * x) * ((x * z) * z)") == ["x", "y", "z"])
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
    tbl = _search_order(c1, c2, 4, time.monotonic() + 30.0)
    report("backtracking search finds order-4 witness",
           tbl is not None and self_check_false("x * y = y * x",
                                                "(x * y) * z = x * (y * z)", 4, tbl))

    # 5. self_check_false rejects a bad witness (table violating eq1).
    bad = [[1, 0], [0, 0]]  # not left projection
    report("self_check_false rejects invalid witness",
           not self_check_false(left_proj, "x * y = y", 2, bad))

    # 6. core_check_equation matches reference semantics with op-in-env.
    vs, lf, rf = core_compile_equation("x * (y * z) = (x * y) * z")
    report("core_check_equation on Z2 addition (associative)",
           core_check_equation(vs, lf, rf, 2, lambda a, b: (a + b) % 2))

    print("SELFTEST " + ("PASS" if ok else "FAIL"))
    return ok


# ============================================================================
# SECTION 2 — spine_provers: deterministic TRUE engines (chain, completion,
# ALLEQ collapse) + the mechanically-earned LLM lemma bridge
# ============================================================================

"""spine_provers.py — WILL v6 deterministic TRUE-side technique engines.

WILL carries no precomputed per-problem or per-law data; everything here
is TECHNIQUE operating on the two equations handed to us at runtime.

1. chain_prove(hyp, goal) — matching-chain prover.  H as a two-way
   rewrite rule; bidirectional BFS between the goal's sides.  The chain
   is independently RE-WALKED (verify_chain) before a Lean `calc` body
   is emitted; each step is one congrArg with an explicit context
   lambda, built structurally from the verified step — never from
   string luck.

2. collapse_prove(hyp, goal) — bounded Knuth–Bendix completion.  Derives
   critical-pair consequences of H; every lemma carries an explicit
   proof chain from H and earlier lemmas, registered only after its
   chain re-walks cleanly.  On a projection law (x◇y = x / x◇y = y), a
   fresh-variable law (s = z, z not in s), or bare x = y, attempts the
   ALLEQ total-collapse construction: `exact ALLEQ lhs rhs`.

   HONEST SCOPE of ALLEQ (documented limit): fresh-variable / var=var
   lemmas always collapse; a projection lemma collapses ONLY when the
   extreme leaf (leftmost for left projection, rightmost for right) of
   H's two sides are DIFFERENT variables — then instantiating H so the
   projection contracts both sides gives a = b directly (generalizes
   the worked 1689⇒2391 proof).  If both sides share the extreme leaf,
   projection does not by itself force collapse (the free projection
   magma satisfies x = x◇y without collapsing) and we return None
   rather than guess.

3. prove_true(hyp, goal) — orchestrator: chain first, then collapse.

Soundness invariant: every returned body is built from a chain/lemma
ladder that passed verify_chain against the hypothesis alone; no emit
path skips the re-walk.  Validation is structural (chain re-walk); Lean
compilation is the judge's job.  Bodies fit the `intro G _ h` wrapper.

Terms: a variable is a str; a node is a 2-tuple (left, right).
Pure Python 3.11 stdlib.  Import-safe (no side effects at import).
"""

Eq = namedtuple("Eq", "vars lhs rhs")


# --- Parsing and term basics ---

def _p_tokenize(s):
    toks, i, n = [], 0, len(s)
    while i < n:
        c = s[i]
        if c.isspace():
            i += 1
        elif c in "()" or c == OP:
            toks.append(c)
            i += 1
        elif c.isalnum() or c in "_'":
            j = i
            while j < n and (s[j].isalnum() or s[j] in "_'"):
                j += 1
            toks.append(s[i:j])
            i = j
        else:
            raise ValueError("bad char %r in %r" % (c, s))
    return toks


def _p_parse(toks, pos):
    def atom(p):
        if toks[p] == "(":
            t, p = expr(p + 1)
            if p >= len(toks) or toks[p] != ")":
                raise ValueError("unbalanced parens")
            return t, p + 1
        t = toks[p]
        if t in (OP, ")", "("):
            raise ValueError("unexpected token %r" % t)
        return t, p + 1

    def expr(p):
        left, p = atom(p)
        while p < len(toks) and toks[p] == OP:
            right, p = atom(p + 1)
            left = (left, right)
        return left, p

    t, p = expr(pos)
    return t, p


def p_parse_term(text):
    """Parse one term.  '*' is normalised to ◇ first."""
    toks = _p_tokenize(normalise(text))
    t, p = _p_parse(toks, 0)
    if p != len(toks):
        raise ValueError("trailing tokens in %r" % text)
    return t


def term_vars(t, acc=None):
    """Variables of t in order of first appearance."""
    if acc is None:
        acc = []
    if isinstance(t, str):
        if t not in acc:
            acc.append(t)
    else:
        term_vars(t[0], acc)
        term_vars(t[1], acc)
    return acc


def p_parse_equation(text):
    """Parse 'lhs = rhs' (either operator glyph) into an Eq."""
    text = normalise(text)
    parts = text.split("=")
    if len(parts) != 2:
        raise ValueError("expected exactly one '=' in %r" % text)
    lhs, rhs = p_parse_term(parts[0]), p_parse_term(parts[1])
    vs = term_vars(lhs, [])
    term_vars(rhs, vs)
    return Eq(tuple(vs), lhs, rhs)


def term_size(t):
    return 1 if isinstance(t, str) else 1 + term_size(t[0]) + term_size(t[1])


def positions(t, base=()):
    """All positions, root first."""
    yield base
    if not isinstance(t, str):
        yield from positions(t[0], base + (0,))
        yield from positions(t[1], base + (1,))


def positions_nonvar(t, base=()):
    if isinstance(t, str):
        return
    yield base
    yield from positions_nonvar(t[0], base + (0,))
    yield from positions_nonvar(t[1], base + (1,))


def subterm_at(t, pos):
    for i in pos:
        t = t[i]
    return t


def replace_at(t, pos, new):
    if not pos:
        return new
    if pos[0] == 0:
        return (replace_at(t[0], pos[1:], new), t[1])
    return (t[0], replace_at(t[1], pos[1:], new))


def subst(t, sigma):
    if isinstance(t, str):
        return sigma.get(t, t)
    return (subst(t[0], sigma), subst(t[1], sigma))


def match_pat(pat, t, sigma):
    """One-way matching: instantiate pat's vars to equal t.  Returns dict or None."""
    if isinstance(pat, str):
        b = sigma.get(pat)
        if b is None:
            s2 = dict(sigma)
            s2[pat] = t
            return s2
        return sigma if b == t else None
    if isinstance(t, str):
        return None
    s2 = match_pat(pat[0], t[0], sigma)
    if s2 is None:
        return None
    return match_pat(pat[1], t[1], s2)


def _walk(sigma, t):
    while isinstance(t, str) and t in sigma:
        t = sigma[t]
    return t


def _occurs(sigma, v, t):
    t = _walk(sigma, t)
    if isinstance(t, str):
        return t == v
    return _occurs(sigma, v, t[0]) or _occurs(sigma, v, t[1])


def unify(a, b, sigma):
    """Full unification with occurs check; triangular sigma dict or None."""
    a, b = _walk(sigma, a), _walk(sigma, b)
    if a == b:
        return sigma
    if isinstance(a, str):
        if _occurs(sigma, a, b):
            return None
        s2 = dict(sigma)
        s2[a] = b
        return s2
    if isinstance(b, str):
        return unify(b, a, sigma)
    s2 = unify(a[0], b[0], sigma)
    if s2 is None:
        return None
    return unify(a[1], b[1], s2)


def resolve(sigma, t):
    """Deep-apply a triangular substitution."""
    t = _walk(sigma, t)
    if isinstance(t, str):
        return t
    return (resolve(sigma, t[0]), resolve(sigma, t[1]))


# Chains: shared proof-step semantics, checker, Lean emission.
# A step is (ref, args, pos, symm): lemma name, binder instantiation terms,
# rewrite position, and whether the instantiated statement is used
# right-to-left.  env maps name -> (vars_tuple, s, t).

def apply_step(env, term, step):
    """Apply one step; return the next term, or None if the step is invalid."""
    ref, args, pos, symm = step
    ent = env.get(ref)
    if ent is None:
        return None
    vs, s, t = ent
    if len(args) != len(vs):
        return None
    sigma = dict(zip(vs, args))
    rl, rr = subst(s, sigma), subst(t, sigma)
    if symm:
        rl, rr = rr, rl
    try:
        sub = subterm_at(term, pos)
    except (IndexError, TypeError):
        return None
    if sub != rl:
        return None
    return replace_at(term, pos, rr)


def verify_chain(env, start, steps, end):
    """Independent re-walk: True iff the steps carry start to end exactly."""
    cur = start
    for st in steps:
        cur = apply_step(env, cur, st)
        if cur is None:
            return False
    return cur == end


def _drop_noop_steps(env, start, steps):
    """Drop steps that rewrite a term to itself (cosmetic only)."""
    out, cur = [], start
    for st in steps:
        nxt = apply_step(env, cur, st)
        if nxt is None:
            return None
        if nxt != cur:
            out.append(st)
        cur = nxt
    return out


def p_render(t):
    if isinstance(t, str):
        return t
    return "(%s %s %s)" % (p_render(t[0]), OP, p_render(t[1]))


def _render_hole(t, pos, hole):
    if not pos:
        return hole
    if pos[0] == 0:
        return "(%s %s %s)" % (_render_hole(t[0], pos[1:], hole), OP, p_render(t[1]))
    return "(%s %s %s)" % (p_render(t[0]), OP, _render_hole(t[1], pos[1:], hole))


def _pick_hole(used):
    h = "t"
    while h in used:
        h += "'"
    return h


def _step_proof_expr(env, cur, step, hole):
    ref, args, pos, symm = step
    inst = ref if not args else "(%s %s)" % (ref, " ".join(p_render(a) for a in args))
    if symm:
        inst = "(%s.symm)" % inst
    if not pos:
        return inst
    ctx = _render_hole(cur, pos, hole)
    return "congrArg (fun %s => %s) %s" % (hole, ctx, inst)


def _all_names(env, terms):
    used = set()
    for t in terms:
        used.update(term_vars(t, []))
    for vs, s, t in env.values():
        used.update(vs)
        used.update(term_vars(s, []))
        used.update(term_vars(t, []))
    return used


def calc_lines(env, start, steps, end, indent=""):
    """Emit a calc block from a VERIFIED chain; re-applies each step and
    raises on any disagreement (defense in depth)."""
    if not steps:
        if start != end:
            raise ValueError("empty chain with distinct endpoints")
        return [indent + "rfl"]
    hole = _pick_hole(_all_names(env, [start, end]))
    lines = [indent + "calc " + p_render(start)]
    cur = start
    for st in steps:
        nxt = apply_step(env, cur, st)
        if nxt is None:
            raise ValueError("invalid step during emission")
        lines.append(indent + "  _ = %s := %s"
                     % (p_render(nxt), _step_proof_expr(env, cur, st, hole)))
        cur = nxt
    if cur != end:
        raise ValueError("chain does not reach endpoint")
    return lines


def _have_lines(env, name, vs, s, t, steps):
    binder = "" if not vs else "∀ (%s : G), " % " ".join(vs)
    lines = ["have %s : %s%s = %s := by" % (name, binder, p_render(s), p_render(t))]
    if vs:
        lines.append("  intro %s" % " ".join(vs))
    lines.extend(calc_lines(env, s, steps, t, indent="  "))
    return lines


# --- Engine 1: matching-chain prover ---

def _rules_of(name, eq):
    """One hypothesis as two-way rules (frm, to, ref, symm, binders);
    symm=True means the named hypothesis is used right-to-left."""
    return [(eq.lhs, eq.rhs, name, False, eq.vars),
            (eq.rhs, eq.lhs, name, True, eq.vars)]


def _instantiation_pool(goal, cap=8):
    pool = [v for v in goal.vars]
    for side in (goal.lhs, goal.rhs):
        for p in positions(side):
            sub = subterm_at(side, p)
            if term_size(sub) <= 3 and sub not in pool:
                pool.append(sub)
            if len(pool) >= cap:
                return pool[:cap]
    return pool[:cap] if pool else ["x"]


def _successors(term, rules, pool, size_cap):
    """Yield (next_term, step) for every one-rule rewrite of term, over any
    number of named hypotheses (rules carry their name and binders)."""
    for pos in positions(term):
        sub = subterm_at(term, pos)
        for frm, to, name, symm, hv in rules:
            sigma = match_pat(frm, sub, {})
            if sigma is None:
                continue
            extra = [v for v in term_vars(to, []) if v not in sigma]
            if len(extra) > 2:
                continue
            combos = [()] if not extra else itertools.product(pool, repeat=len(extra))
            for combo in combos:
                s2 = dict(sigma)
                for v, val in zip(extra, combo):
                    s2[v] = val
                nxt = replace_at(term, pos, subst(to, s2))
                if term_size(nxt) > size_cap:
                    continue
                args = tuple(s2.get(v, pool[0]) for v in hv)
                yield nxt, (name, args, pos, symm)


def _rebuild(visited, node):
    """Walk parent pointers to the origin; steps come out reversed."""
    steps = []
    while True:
        parent, step = visited[node]
        if step is None:
            return steps
        steps.append(step)
        node = parent


def _reverse_steps(steps):
    return [(ref, args, pos, not symm) for (ref, args, pos, symm) in reversed(steps)]


def chain_prove_multi(named_hyps, goal_text, max_nodes=20000, deadline=25.0):
    """Matching-chain prover over one or more named hypotheses:
    bidirectional BFS with each hypothesis as a two-way rule (extra rule
    variables instantiated from a pool computed from the goal at runtime).
    The found chain is re-walked with verify_chain before an
    `intro ...; calc ...` body is emitted.  Returns the body or None; None
    means "no chain within budget", NOT evidence the implication is false.
    """
    t0 = time.monotonic()
    parsed = [(name, p_parse_equation(txt)) for name, txt in named_hyps]
    goal = p_parse_equation(goal_text)
    env = {name: (eq.vars, eq.lhs, eq.rhs) for name, eq in parsed}
    if goal.lhs == goal.rhs:
        return _finalize_chain_body(env, goal, [])
    rules = []
    for name, eq in parsed:
        rules.extend(_rules_of(name, eq))
    pool = _instantiation_pool(goal)
    sizes = [term_size(goal.lhs), term_size(goal.rhs)]
    for _, eq in parsed:
        sizes.extend((term_size(eq.lhs), term_size(eq.rhs)))
    size_cap = max(sizes) + 8

    fwd = {goal.lhs: (None, None)}   # node -> (parent, step parent->node)
    bwd = {goal.rhs: (None, None)}
    frontier_f, frontier_b = [goal.lhs], [goal.rhs]
    expanded = 0

    def join(mid):
        f_steps = list(reversed(_rebuild(fwd, mid)))          # lhs -> mid
        b_steps = _reverse_steps(list(reversed(_rebuild(bwd, mid))))  # mid -> rhs
        steps = f_steps + b_steps
        if not verify_chain(env, goal.lhs, steps, goal.rhs):
            return None  # soundness gate: never emit an unverified chain
        return _finalize_chain_body(env, goal, steps)

    if goal.lhs in bwd:
        return join(goal.lhs)

    while frontier_f or frontier_b:
        if expanded >= max_nodes or time.monotonic() - t0 > deadline:
            return None
        # expand the smaller frontier
        if frontier_b and (not frontier_f or len(frontier_b) <= len(frontier_f)):
            frontier, visited, other = frontier_b, bwd, fwd
            which = "b"
        else:
            frontier, visited, other = frontier_f, fwd, bwd
            which = "f"
        nxt_frontier = []
        for node in frontier:
            if expanded >= max_nodes or time.monotonic() - t0 > deadline:
                return None
            expanded += 1
            for child, step in _successors(node, rules, pool, size_cap):
                if child in visited:
                    continue
                visited[child] = (node, step)
                if child in other:
                    return join(child)
                nxt_frontier.append(child)
        if which == "b":
            frontier_b = nxt_frontier
        else:
            frontier_f = nxt_frontier
    return None


def chain_prove(hyp_text, goal_text, max_nodes=20000, deadline=25.0):
    """Single-hypothesis matching-chain prover (H is named 'h')."""
    return chain_prove_multi([("h", hyp_text)], goal_text,
                             max_nodes=max_nodes, deadline=deadline)


def bridge_prove(hyp_text, lemma_text, goal_text, deadline=20.0):
    """LLM-suggested bridge lemma, mechanically earned: prove H => lemma
    with the chain engine, then prove Goal from H plus the lemma, and
    splice the verified `have hL` ladder into the final body.  The lemma
    statement itself is never trusted: if either chain fails to verify,
    the whole route returns None.  If the second chain never actually
    uses the lemma, the direct (h-only) body is returned instead.
    """
    try:
        lem = p_parse_equation(lemma_text)
    except Exception:
        return None
    half = max(1.0, deadline / 2.0)
    body1 = chain_prove(hyp_text, lemma_text, deadline=half)
    if body1 is None:
        return None
    body2 = chain_prove_multi([("h", hyp_text), ("hL", lemma_text)],
                              goal_text, deadline=half)
    if body2 is None:
        return None
    if "hL" not in body2:
        return body2
    lines2 = body2.split("\n")
    idx = 1 if lines2 and lines2[0].startswith("intro ") else 0
    binder = ("∀ (%s : G), " % " ".join(lem.vars)) if lem.vars else ""
    have = ["have hL : %s%s = %s := by" % (binder, p_render(lem.lhs), p_render(lem.rhs))]
    have.extend("  " + ln for ln in body1.split("\n"))
    return "\n".join(lines2[:idx] + have + lines2[idx:])


def _finalize_chain_body(env, goal, steps):
    steps = _drop_noop_steps(env, goal.lhs, steps)
    if steps is None or not verify_chain(env, goal.lhs, steps, goal.rhs):
        return None
    lines = []
    if goal.vars:
        lines.append("intro %s" % " ".join(goal.vars))
    lines.extend(calc_lines(env, goal.lhs, steps, goal.rhs))
    return "\n".join(lines)


# --- Engine 2: bounded Knuth–Bendix completion + ALLEQ collapse ---

class _KB:
    """Bounded completion over the single hypothesis.  Every registered
    lemma carries an explicit chain from 'h' and earlier lemmas and is
    re-walked at registration; unverifiable candidates are dropped, so
    the lemma store can never contain an underived statement.
    """

    def __init__(self, hyp, max_lemmas=300, size_cap=44, norm_fuel=60,
                 deadline=60.0):
        self.hyp = hyp
        self.env = {"h": (hyp.vars, hyp.lhs, hyp.rhs)}
        self.chains = {}          # name -> steps
        self.deps = {"h": set()}  # name -> set of referenced lemma names
        self.order = []           # creation order of derived lemmas
        self.rules = []           # (frm, to, ref, symm)  [statement flipped iff symm]
        self.seen = set()
        self.max_lemmas = max_lemmas
        self.size_cap = size_cap
        self.norm_fuel = norm_fuel
        self.t_end = time.monotonic() + deadline
        self.heap = []
        self.counter = 0
        self.projections = []     # (name, kind) kind in {'L','R'}
        self.alleq_sources = []   # (name, mode) mode 'fresh'
        self._register_rules("h", hyp.vars, hyp.lhs, hyp.rhs)
        self._detect("h", hyp.vars, hyp.lhs, hyp.rhs)
        self._push_cps_for_new_rules(0)

    # -- rule management ---------------------------------------------------

    def _orientable(self, s, t):
        ss, ts = term_size(s), term_size(t)
        if ss > ts:
            return True
        if ss < ts:
            return False
        return p_render(s) > p_render(t)

    def _register_rules(self, name, vs, s, t):
        added = []
        for frm, to, symm in ((s, t, False), (t, s, True)):
            if isinstance(frm, str):
                continue  # bare-variable LHS matches everything
            if not self._orientable(frm, to):
                continue
            fv = set(term_vars(frm, []))
            if any(v not in fv for v in term_vars(to, [])):
                continue  # 'to' vars matching cannot bind
            self.rules.append((frm, to, name, symm))
            added.append(len(self.rules) - 1)
        return added

    # -- normalization (records proof steps) -------------------------------

    def _normal_form(self, term):
        steps = []
        fuel = self.norm_fuel
        changed = True
        while changed and fuel > 0:
            changed = False
            for pos in positions(term):
                sub = subterm_at(term, pos)
                if isinstance(sub, str):
                    continue
                for frm, to, ref, symm in self.rules:
                    sigma = match_pat(frm, sub, {})
                    if sigma is None:
                        continue
                    vs = self.env[ref][0]
                    args = tuple(sigma.get(v, sub) for v in vs)
                    new = replace_at(term, pos, subst(to, sigma))
                    if new == term:
                        continue
                    steps.append((ref, args, pos, symm))
                    term = new
                    fuel -= 1
                    changed = True
                    break
                if changed:
                    break
        return term, steps

    # -- critical pairs ----------------------------------------------------

    def _push(self, s, t, chain, depth):
        w = term_size(s) + term_size(t) + 2 * depth
        self.counter += 1
        if len(self.heap) < 20000:
            heapq.heappush(self.heap, (w, self.counter, s, t, chain, depth))

    def _cp(self, ai, bi, depth):
        fa, ta, ra, sa = self.rules[ai]
        fb, tb, rb, sb = self.rules[bi]
        ren = {v: v + "′" for v in term_vars(fb, term_vars(tb, []))}
        fb2, tb2 = subst(fb, ren), subst(tb, ren)
        vs_a = self.env[ra][0]
        vs_b = self.env[rb][0]
        for p in positions_nonvar(fa):
            if p == () and ai == bi:
                continue
            mu = unify(subterm_at(fa, p), fb2, {})
            if mu is None:
                continue
            u = resolve(mu, ta)
            v = replace_at(resolve(mu, fa), p, resolve(mu, tb2))
            if u == v:
                continue
            if term_size(u) + term_size(v) > self.size_cap:
                continue
            args_a = tuple(resolve(mu, x) for x in vs_a)
            args_b = tuple(resolve(mu, ren.get(x, x)) for x in vs_b)
            chain = [
                (ra, args_a, (), not sa),   # u = mu(ta)  ->  mu(fa)
                (rb, args_b, p, sb),        # rewrite at p: mu(fb2) -> mu(tb2)
            ]
            self._push(u, v, chain, depth)

    def _push_cps_for_new_rules(self, depth):
        n = len(self.rules)
        for i in range(n):
            for j in range(n):
                self._cp(i, j, depth)

    def _push_cps_between(self, new_idx, depth):
        for i in new_idx:
            for j in range(len(self.rules)):
                self._cp(i, j, depth)
                if j not in new_idx:
                    self._cp(j, i, depth)

    # -- lemma registration + detection ------------------------------------

    def _canon(self, s, t, chain):
        vs = term_vars(s, [])
        term_vars(t, vs)
        extra = []
        for (_, args, _, _) in chain:
            for a in args:
                for v in term_vars(a, []):
                    if v not in vs and v not in extra:
                        extra.append(v)
        ren = {v: "a%d" % i for i, v in enumerate(vs + extra)}
        s2, t2 = subst(s, ren), subst(t, ren)
        chain2 = [(ref, tuple(subst(a, ren) for a in args), pos, sy)
                  for (ref, args, pos, sy) in chain]
        binders = tuple(ren[v] for v in vs + extra)
        return binders, s2, t2, chain2

    def _register(self, s, t, chain, depth):
        binders, s2, t2, chain2 = self._canon(s, t, chain)
        key = (s2, t2)
        key2 = (t2, s2)
        if key in self.seen or key2 in self.seen:
            return None
        name = "L%d" % (len(self.order) + 1)
        if not verify_chain(self.env, s2, chain2, t2):
            return None  # soundness gate: drop, never register
        self.seen.add(key)
        self.env[name] = (binders, s2, t2)
        self.chains[name] = chain2
        self.deps[name] = {ref for (ref, _, _, _) in chain2 if ref != "h"}
        self.order.append(name)
        new_idx = self._register_rules(name, binders, s2, t2)
        self._push_cps_between(new_idx, depth + 1)
        self._detect(name, binders, s2, t2)
        return name

    def _detect(self, name, vs, s, t):
        for a, b in ((s, t), (t, s)):
            if isinstance(b, str):
                if b not in term_vars(a, []):
                    self.alleq_sources.append((name, a, b, s, t))
            if (not isinstance(a, str) and isinstance(a[0], str)
                    and isinstance(a[1], str) and a[0] != a[1]
                    and isinstance(b, str)):
                if b == a[0]:
                    self.projections.append((name, "L"))
                elif b == a[1]:
                    self.projections.append((name, "R"))

    # -- main loop ---------------------------------------------------------

    def run(self):
        """Process critical pairs until an ALLEQ route succeeds or budget
        ends; returns (alleq_vars, alleq_chain, needed_names) or None."""
        res = self._try_alleq()
        if res is not None:
            return res
        while self.heap:
            if time.monotonic() > self.t_end:
                return None
            if len(self.order) >= self.max_lemmas:
                return None
            _, _, s, t, chain, depth = heapq.heappop(self.heap)
            ns, st_s = self._normal_form(s)
            nt, st_t = self._normal_form(t)
            if ns == nt:
                continue
            full = _reverse_steps(st_s) + chain + st_t
            if self._register(ns, nt, full, depth) is None:
                continue
            res = self._try_alleq()
            if res is not None:
                return res
        return None

    # -- ALLEQ constructions -----------------------------------------------

    def _fresh_pair(self):
        used = set(self.hyp.vars)
        for vs, s, t in self.env.values():
            used.update(vs)
        a = "a"
        while a in used:
            a += "'"
        b = "b"
        while b in used or b == a:
            b += "'"
        return a, b

    def _try_alleq(self):
        for (name, termside, varside, s, t) in self.alleq_sources:
            res = self._alleq_from_fresh(name, termside, varside, s, t)
            if res is not None:
                return res
        for (name, kind) in self.projections:
            res = self._alleq_from_projection(name, kind)
            if res is not None:
                return res
        return None

    def _alleq_from_fresh(self, name, termside, varside, s, t):
        """s = t with one side a variable absent from the other: then
        termside[all->a] equals both a and b, so a = b in two steps."""
        a, b = self._fresh_pair()
        vs = self.env[name][0]
        var_on_right = (t == varside)  # statement reads: termside = varside
        sig1 = {v: a for v in vs}      # everything -> a  (varside too)
        sig2 = {v: a for v in vs}
        sig2[varside] = b              # varside -> b; termside unchanged
        args1 = tuple(sig1[v] for v in vs)
        args2 = tuple(sig2[v] for v in vs)
        # termside=varside: inst1 termside[a]=a needs symm; inst2 goes ->b.
        step1 = (name, args1, (), var_on_right)
        step2 = (name, args2, (), not var_on_right)
        chain = [step1, step2]
        chain = _drop_noop_steps(self.env, a, chain)
        if chain is None or not verify_chain(self.env, a, chain, b):
            return None
        needed = self._closure(name)
        return ((a, b), chain, needed)

    def _proj_step(self, pname, node):
        """One projection application at the root of node=(l,r)."""
        vs, s, t = self.env[pname]
        for src, dst, symm in ((s, t, False), (t, s, True)):
            if isinstance(src, str):
                continue
            sigma = match_pat(src, node, {})
            if sigma is None:
                continue
            kept = subst(dst, sigma)
            if not isinstance(dst, str):
                continue
            args = tuple(sigma.get(v, node) for v in vs)
            return (pname, args, (), symm), kept
        return None

    def _collapse_steps(self, pname, term):
        """Apply the projection at the root until a variable remains."""
        steps = []
        while not isinstance(term, str):
            got = self._proj_step(pname, term)
            if got is None:
                return None
            step, term = got
            steps.append(step)
        return steps, term

    def _alleq_from_projection(self, pname, kind):
        """ALLEQ from projection + one h instantiation.  Covers ONLY the
        subclass where the extreme leaves of h's sides are distinct
        variables; otherwise returns None (see module docstring)."""
        hyp = self.hyp

        def extreme(t):
            while not isinstance(t, str):
                t = t[0] if kind == "L" else t[1]
            return t

        lv1, lv2 = extreme(hyp.lhs), extreme(hyp.rhs)
        if lv1 == lv2:
            return None
        a, b = self._fresh_pair()
        sigma = {v: a for v in hyp.vars}
        sigma[lv1] = a
        sigma[lv2] = b
        sl, sr = subst(hyp.lhs, sigma), subst(hyp.rhs, sigma)
        left = self._collapse_steps(pname, sl)
        right = self._collapse_steps(pname, sr)
        if left is None or right is None:
            return None
        lsteps, lvar = left
        rsteps, rvar = right
        if lvar != a or rvar != b:
            return None
        hargs = tuple(sigma[v] for v in hyp.vars)
        chain = (_reverse_steps(lsteps)
                 + [("h", hargs, (), False)]
                 + rsteps)
        chain = _drop_noop_steps(self.env, a, chain)
        if chain is None or not verify_chain(self.env, a, chain, b):
            return None
        needed = self._closure(pname)
        return ((a, b), chain, needed)

    def _closure(self, name):
        """Dependency closure of a lemma, in creation order (h excluded)."""
        need, stack = set(), [name]
        while stack:
            n = stack.pop()
            if n == "h" or n in need:
                continue
            need.add(n)
            stack.extend(self.deps.get(n, ()))
        return [n for n in self.order if n in need]


def collapse_prove(hyp_text, goal_text, max_lemmas=300, deadline=60.0,
                   size_cap=44):
    """Bounded Knuth–Bendix completion + ALLEQ total-collapse.

    Derives critical-pair consequences of H with explicit, re-walked
    proof chains.  On a collapse route (fresh-variable law, x = y, or a
    projection law whose H-instantiation contracts — honest scope in the
    module docstring) emits: intro; the needed `have L_k` ladder; `have
    ALLEQ : ∀ (a b : G), a = b`; `exact ALLEQ lhs rhs`.  Every emitted
    chain is verified with verify_chain first.  Returns the body or
    None; None is NOT evidence the implication is false.
    """
    hyp = p_parse_equation(hyp_text)
    goal = p_parse_equation(goal_text)
    kb = _KB(hyp, max_lemmas=max_lemmas, size_cap=size_cap, deadline=deadline)
    res = kb.run()
    if res is None:
        return None
    (a, b), chain, needed = res
    env = kb.env
    # final independent verification of everything we are about to emit
    for name in needed:
        vs, s, t = env[name]
        if not verify_chain(env, s, kb.chains[name], t):
            return None
    if not verify_chain(env, a, chain, b):
        return None
    try:
        lines = []
        if goal.vars:
            lines.append("intro %s" % " ".join(goal.vars))
        for name in needed:
            vs, s, t = env[name]
            lines.extend(_have_lines(env, name, vs, s, t, kb.chains[name]))
        lines.append("have ALLEQ : ∀ (%s %s : G), %s = %s := by" % (a, b, a, b))
        lines.append("  intro %s %s" % (a, b))
        lines.extend(calc_lines(env, a, chain, b, indent="  "))
        lines.append("exact ALLEQ %s %s" % (p_render(goal.lhs), p_render(goal.rhs)))
        return "\n".join(lines)
    except ValueError:
        return None  # emission disagreed with the verified chain: refuse


# --- Orchestrator ---

def prove_true(hyp_text, goal_text, deadline=60.0):
    """Deterministic TRUE engines in cost order: chain_prove (most TRUE
    implications are rewrite chains), then collapse_prove.  Returns a
    body for the `intro G _ h` wrapper, or None.  Every returned body
    has passed an independent chain re-walk; no unverified exit.
    """
    t0 = time.monotonic()
    body = chain_prove(hyp_text, goal_text, deadline=min(25.0, deadline * 0.4))
    if body is not None:
        return body
    remaining = deadline - (time.monotonic() - t0)
    if remaining <= 1.0:
        return None
    return collapse_prove(hyp_text, goal_text, deadline=remaining)


# --- Self-test ---

def _selftest_provers():
    ok = True

    def report(label, passed, extra=""):
        nonlocal ok
        ok = ok and passed
        print("%s %s%s" % ("PASS" if passed else "FAIL", label,
                           (" — " + extra) if extra else ""))

    b1 = chain_prove("x * y = y * x", "x * (y * z) = x * (z * y)",
                     deadline=10.0)
    report("T1 chain + congrArg",
           b1 is not None and "calc" in b1 and "congrArg" in b1)

    b2 = collapse_prove("x * y = z", "x = (y * x) * z", deadline=10.0)
    report("T2 fresh-var ALLEQ",
           b2 is not None and "ALLEQ" in b2 and "exact ALLEQ" in b2)

    b3 = collapse_prove("x = (y * x) * ((x * z) * z)",
                        "x = (y * (z * (y * z))) * z",
                        deadline=120.0)
    report("T3 1689=>2391 collapse",
           b3 is not None and "ALLEQ" in b3,
           "" if b3 else "no collapse found within budget")

    # honest boundary: h = left projection must NOT collapse
    b4 = collapse_prove("x = x * y", "x = (x * y) * z", deadline=10.0)
    report("T4 honest None", b4 is None)

    print("SELFTEST", "PASS" if ok else "FAIL")
    return ok


# ============================================================================
# SECTION 3 — spine_shell: protocol, orchestration, LLM tier, Marathon
# ============================================================================

"""WILL v6 — spine_shell: protocol + orchestration. No precomputed
per-problem/per-law data; algorithms only. Solo judge loop (EULER protocol
shell), Lean emitters, LLM tier (defensive parse, mechanical verify, judge
gate), Marathon branch (self-verified tiers ONLY), solve() orchestration.
Core provers plug in via PROVERS. Soundness invariant: no unverified exit —
FALSE tables exhaustively re-evaluated, deterministic TRUE bodies
self-rechecked (hook contract), LLM output judge-gated, Marathon writes
only self-verified answers."""

# The top-level PROMPT constant lives at the top of this file; the proxy
# renders {problem.*} and {solver.*} attribute interpolations.

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
                  "macro", "elab", "syntax", "unsafe", "implemented_by", "dbg_trace",
                  "native_decide", "ofReduceBool", "reduceBool")


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


def _normalize_sug(obj):
    """Map either reply dialect to the internal suggestion shape.  The
    mandatory 'check' field is prompt-side discipline only: no code path
    reads it (the spine never trusts it), so it is dropped here."""
    if not isinstance(obj, dict):
        return None
    if obj.get("kind") in ("false_table", "goal_proof"):
        return obj
    v = str(obj.get("verdict", "")).strip().lower()
    if v == "false" and isinstance(obj.get("table"), list):
        return {"kind": "false_table", "n": len(obj["table"]), "table": obj["table"]}
    if v == "true" and isinstance(obj.get("proof"), str):
        out = {"kind": "goal_proof", "proof": obj["proof"]}
        lem = obj.get("lemma")
        if isinstance(lem, str) and lem.strip():
            out["lemma"] = lem
        return out
    return None


def parse_llm_reply(text):
    """Salvage one suggestion dict from a contract-violating reply; never raises."""
    if not isinstance(text, str) or not text.strip():
        return None
    body = re.sub(r"```[a-zA-Z]*", "", text).replace("```", "").strip()
    # Pass 1: any balanced JSON object in either reply dialect.
    dec = json.JSONDecoder()
    for m in re.finditer(r"\{", body):
        try:
            obj, _ = dec.raw_decode(body, m.start())
        except Exception:
            continue
        sug = _normalize_sug(obj)
        if sug is not None:
            return sug
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
    # Honor the hook's self_verified contract even here (not only in Marathon):
    # a third-party prover registered via register_prover must not ship an
    # unverified body to the judge. In-file hooks always set the flag True.
    out = run_hook("chain", prob, time.time() + remaining() * 0.25)
    if out and out.get("self_verified"):
        if _attempt_judge("true", lean_true(out["body"]), S) == "accepted":
            return True
        if _JUDGE_INFRA_DOWN:
            return False

    # Tier 3: completion / collapse (self-rechecking hook).
    out = run_hook("completion", prob, time.time() + remaining() * 0.25)
    if out and out.get("self_verified"):
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
        if out and out.get("self_verified"):
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
                    "your table failed the mechanical check (must satisfy H at every assignment and violate Goal at some); fix or switch strategy")
        elif sug.get("kind") == "goal_proof":
            # Boundary rule holds even for model output: '*' -> '◇'.
            bodytext = normalise(sug.get("proof", ""))
            if proof_body_is_clean(bodytext):
                if _attempt_judge("true", lean_true(bodytext, high_heartbeats=True), S) == "accepted":
                    return True
            else:
                S.push_feedback("your proof body was empty or used a banned token; rewrite it")
            lemma = sug.get("lemma")
            if (isinstance(lemma, str) and "=" in lemma
                    and not _JUDGE_INFRA_DOWN and time.time() < deadline):
                try:
                    bridged = bridge_prove(prob["eq1"], normalise(lemma), prob["eq2"],
                                           deadline=min(20.0, max(2.0, deadline - time.time())))
                except Exception:
                    bridged = None
                if bridged is not None and proof_body_is_clean(bridged):
                    if _attempt_judge("true", lean_true(bridged, high_heartbeats=True), S) == "accepted":
                        return True
                else:
                    S.push_feedback(
                        "your bridge lemma did not verify mechanically; offer a different stepping stone")
        else:
            S.push_feedback("unknown reply shape; use verdict true+proof or verdict false+table")
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


def _selftest_shell():
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
        by_id = {a["id"]: a for a in ans}
        rep("marathon writes only self-verified answers",
            set(by_id) == {"m1", "m2"}
            and by_id["m1"]["verdict"] == "false" and "decideFin!" in by_id["m1"]["code"]
            and by_id["m2"]["verdict"] == "true" and "decideFin!" not in by_id["m2"]["code"]
            and "sorry" not in by_id["m2"]["code"])

    an = build_analysis(prep_problem({"id": "t4", "equation1": "x = x * x", "equation2": comm}))
    rep("analysis: idempotence detected", "idempotence" in an)
    rep("analysis: variable counts", "variable(s)" in an)

    print("SELFTEST " + ("PASS" if ok else "FAIL"))
    return ok


# ============================================================================
# SECTION 4 — WILL wiring: plug the deterministic engines into the shell.
# Hook contract honesty: chain/collapse bodies are marked self_verified
# because every one has passed an independent chain re-walk (verify_chain)
# before emission; ce_search results are exhaustively re-checked twice
# (self_check_false inside the engine, table_is_counterexample in the shell).
# ============================================================================


def _hook_ce_search(prob, deadline):
    remain = deadline - time.time()
    if remain < 0.5:
        return None
    return find_counterexample(prob["eq1"], prob["eq2"], max_order=6,
                               deadline_s=remain)


def _hook_chain(prob, deadline):
    remain = deadline - time.time()
    if remain < 0.5:
        return None
    body = chain_prove(prob["eq1"], prob["eq2"], deadline=remain)
    if body is None:
        return None
    return {"body": body, "self_verified": True}


def _hook_completion(prob, deadline):
    remain = deadline - time.time()
    if remain < 0.5:
        return None
    body = collapse_prove(prob["eq1"], prob["eq2"], deadline=remain)
    if body is None:
        return None
    return {"body": body, "self_verified": True}


register_prover("ce_search", _hook_ce_search)
register_prover("chain", _hook_chain)
register_prover("completion", _hook_completion)


# ============================================================================
# SECTION 5 — self-tests + entry points
# ============================================================================


def _selftest_will():
    ok = True

    def rep(name, cond):
        nonlocal ok
        print(("PASS " if cond else "FAIL ") + name)
        ok = ok and bool(cond)

    # New-dialect LLM replies parse and normalise ('check' is dropped).
    s1 = parse_llm_reply(
        '{"verdict":"false","table":[[1,0],[0,0]],"check":"x=0: LHS=1, RHS=0"}')
    rep("will parse: verdict-false dialect",
        s1 is not None and s1["kind"] == "false_table" and s1["n"] == 2)
    s2 = parse_llm_reply(
        '{"verdict":"true","proof":"intro x y\\nexact h y x",'
        '"check":"h y x","lemma":"x * y = y * x"}')
    rep("will parse: verdict-true dialect + lemma",
        s2 is not None and s2["kind"] == "goal_proof" and "lemma" in s2)

    # PROMPT carries the grafts and the interpolation slots.
    for frag in ('"check"', "scan your finished proof for any *",
                 "fully parenthesize", "ALLEQ",
                 "{problem.equation1}", "{problem.equation2}",
                 "{solver.analysis}", "{solver.feedback}"):
        rep("prompt fragment: " + frag[:36], frag in PROMPT)
    rep("prompt: check field in both shapes and all three miniatures",
        PROMPT.count('"check":"') == 5)

    # Hooks registered.
    rep("hooks registered",
        all(PROVERS[k] for k in ("ce_search", "chain", "completion")))

    # Bridge prover returns a verified body (direct or spliced).
    b = bridge_prove("x * y = y * x", "y * x = x * y",
                     "x * (y * z) = x * (z * y)", deadline=15.0)
    rep("bridge_prove returns verified body",
        b is not None and b.startswith("intro"))
    rep("bridge_prove rejects an unprovable lemma",
        bridge_prove("x * y = y * x", "x * y = x", "x * x = x",
                     deadline=6.0) is None)

    # Boundary rule end-to-end: '*' in model proofs is normalised.
    rep("normalise applies inside proof bodies",
        normalise("exact h (x * y) z") == "exact h (x ◇ y) z")

    print("WILL-EXTRA SELFTEST " + ("PASS" if ok else "FAIL"))
    return ok


def _selftest():
    print("== core ==")
    ok = _selftest_core()
    print("== provers ==")
    ok = _selftest_provers() and ok
    print("== shell ==")
    ok = _selftest_shell() and ok
    print("== will ==")
    ok = _selftest_will() and ok
    print("WILL v6 SELFTEST " + ("PASS" if ok else "FAIL"))
    return ok


if __name__ == "__main__":
    if "--selftest" in sys.argv or os.environ.get("WILL_SELFTEST"):
        sys.exit(0 if _selftest() else 1)
    if os.environ.get("JUDGE_MARATHON_MANIFEST"):
        marathon()
    else:
        main()
