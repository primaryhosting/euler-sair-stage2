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

import heapq
import itertools
import time
from collections import namedtuple

OP = "◇"

Eq = namedtuple("Eq", "vars lhs rhs")


# --- Parsing and term basics ---

def normalise(text):
    """Replace ASCII '*' with the canonical ◇ operator (boundary rule)."""
    return text.replace("*", OP) if isinstance(text, str) else text


def _tokenize(s):
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


def _parse(toks, pos):
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


def parse_term(text):
    """Parse one term.  '*' is normalised to ◇ first."""
    toks = _tokenize(normalise(text))
    t, p = _parse(toks, 0)
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


def parse_equation(text):
    """Parse 'lhs = rhs' (either operator glyph) into an Eq."""
    text = normalise(text)
    parts = text.split("=")
    if len(parts) != 2:
        raise ValueError("expected exactly one '=' in %r" % text)
    lhs, rhs = parse_term(parts[0]), parse_term(parts[1])
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


def render(t):
    if isinstance(t, str):
        return t
    return "(%s %s %s)" % (render(t[0]), OP, render(t[1]))


def _render_hole(t, pos, hole):
    if not pos:
        return hole
    if pos[0] == 0:
        return "(%s %s %s)" % (_render_hole(t[0], pos[1:], hole), OP, render(t[1]))
    return "(%s %s %s)" % (render(t[0]), OP, _render_hole(t[1], pos[1:], hole))


def _pick_hole(used):
    h = "t"
    while h in used:
        h += "'"
    return h


def _step_proof_expr(env, cur, step, hole):
    ref, args, pos, symm = step
    inst = ref if not args else "(%s %s)" % (ref, " ".join(render(a) for a in args))
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
    lines = [indent + "calc " + render(start)]
    cur = start
    for st in steps:
        nxt = apply_step(env, cur, st)
        if nxt is None:
            raise ValueError("invalid step during emission")
        lines.append(indent + "  _ = %s := %s"
                     % (render(nxt), _step_proof_expr(env, cur, st, hole)))
        cur = nxt
    if cur != end:
        raise ValueError("chain does not reach endpoint")
    return lines


def _have_lines(env, name, vs, s, t, steps):
    binder = "" if not vs else "∀ (%s : G), " % " ".join(vs)
    lines = ["have %s : %s%s = %s := by" % (name, binder, render(s), render(t))]
    if vs:
        lines.append("  intro %s" % " ".join(vs))
    lines.extend(calc_lines(env, s, steps, t, indent="  "))
    return lines


# --- Engine 1: matching-chain prover ---

def _hyp_rules(hyp):
    """H as rules (frm, to, symm): symm=True means h used right-to-left."""
    return [(hyp.lhs, hyp.rhs, False), (hyp.rhs, hyp.lhs, True)]


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


def _successors(term, hyp, rules, pool, size_cap):
    """Yield (next_term, step) for every one-rule rewrite of term."""
    hv = hyp.vars
    for pos in positions(term):
        sub = subterm_at(term, pos)
        for frm, to, symm in rules:
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
                yield nxt, ("h", args, pos, symm)


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


def chain_prove(hyp_text, goal_text, max_nodes=20000, deadline=25.0):
    """Matching-chain prover: bidirectional BFS with H as a two-way rule
    (extra rule variables instantiated from a pool computed from the goal
    at runtime).  The found chain is re-walked with verify_chain before a
    `intro ...; calc ...` body is emitted.  Returns the body or None; None
    means "no chain within budget", NOT evidence the implication is false.
    """
    t0 = time.monotonic()
    hyp = parse_equation(hyp_text)
    goal = parse_equation(goal_text)
    env = {"h": (hyp.vars, hyp.lhs, hyp.rhs)}
    if goal.lhs == goal.rhs:
        return _finalize_chain_body(env, goal, [])
    rules = _hyp_rules(hyp)
    pool = _instantiation_pool(goal)
    size_cap = max(term_size(goal.lhs), term_size(goal.rhs),
                   term_size(hyp.lhs), term_size(hyp.rhs)) + 8

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
            for child, step in _successors(node, hyp, rules, pool, size_cap):
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
        return render(s) > render(t)

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
    hyp = parse_equation(hyp_text)
    goal = parse_equation(goal_text)
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
        lines.append("exact ALLEQ %s %s" % (render(goal.lhs), render(goal.rhs)))
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

def _selftest():
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


if __name__ == "__main__":
    import sys
    sys.exit(0 if _selftest() else 1)
