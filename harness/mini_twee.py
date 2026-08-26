#!/usr/bin/env python3
"""mini-Twee: a bounded Knuth-Bendix-style critical-pair completion that emits
allowlist-safe Lean 4 proofs for magma equational implications.

WHY THIS EXISTS
---------------
Twee (unfailing completion) produces FORWARD equational proofs with explicit
lemmas -- almost a Lean `calc` already.  It needs GHC/cabal, which are absent on
this box and too heavy to build (disk/mem-constrained, crash-prone).  So we
reimplement the *idea* deterministically in Python:

  1. Orient the hypothesis  x = big  as a rewrite rule  big -> x.
  2. Saturate: repeatedly superpose rules onto each other, deriving new
     equations (critical pairs).  Each derived equation carries a Lean proof
     term built ONLY from: function application of earlier lemmas, congrArg,
     .symm, .trans, fun.  (This is exactly what E-prover's `spm` steps do -- we
     verified on all 6 targets that the needed lemmas are 1-3 superpositions
     deep and tiny.)
  3. Prove the goal by rewriting goalLHS -> goalRHS with the derived rules
     (or, if the theory collapsed to a trivial magma, close directly).
  4. Emit `def submission : Goal := by intro G _ h; intro <gvars>; <have ...>; calc ...`.

Everything is verified end-to-end by Axle (the SAIR judge's Lean 4.32.2).

Term := ("var", name) | ("op", left, right)
"""
import itertools, time

# ---------------------------------------------------------------- term utils
def parse_side(s):
    s = s.strip()
    while len(s) >= 2 and s[0] == "(" and s[-1] == ")":
        depth = 0; matched = True
        for i, c in enumerate(s):
            if c == "(": depth += 1
            elif c == ")": depth -= 1
            if depth == 0 and i < len(s) - 1: matched = False; break
        if matched: s = s[1:-1].strip()
        else: break
    depth = 0; last = -1
    for i, c in enumerate(s):
        if c == "(": depth += 1
        elif c == ")": depth -= 1
        elif (c == "◇" or c == "*") and depth == 0: last = i
    if last >= 0:
        return ("op", parse_side(s[:last]), parse_side(s[last + 1:]))
    return ("var", s.strip())

def parse_law(text):
    l, r = text.split("=", 1)
    return parse_side(l), parse_side(r)

def render(t):
    if t[0] == "var": return t[1]
    return "(" + render(t[1]) + " ◇ " + render(t[2]) + ")"

def tsize(t):
    if t[0] == "var": return 1
    return 1 + tsize(t[1]) + tsize(t[2])

# ------------------------------------------------------------------- duality
# Mirror map  Φ : swap the two arguments of every ◇.  Φ is an involution and a
# term homomorphism; every allowlist tactic (congrArg / .symm / .trans / calc /
# have) is Φ-equivariant, so Φ(proof of Φe1⊢Φe2) is a proof of e1⊢e2 (h : Φe1
# mirrors back to h : e1 since ΦΦ = id).  This doubles reachability for free:
# a theory that won't KB-complete in one handedness often completes in the other.
def dual_term(t):
    if t[0] == "var": return t
    return ("op", dual_term(t[2]), dual_term(t[1]))

def dual_law(text):
    l, r = parse_law(text)
    return render(dual_term(l)) + " = " + render(dual_term(r))

def _swap_ops(s):
    """Apply Φ to every balanced (...) group in an emitted Lean body string.
    render() fully parenthesises ops, so every ◇ lives inside a paren group;
    non-term Lean (fun/have/calc/:=/.symm) carries no depth-0 ◇, so recursion
    reaches the term groups without disturbing syntax."""
    out = []; i = 0; n = len(s)
    while i < n:
        if s[i] == "(":
            d = 0; j = i
            while j < n:
                if s[j] == "(": d += 1
                elif s[j] == ")":
                    d -= 1
                    if d == 0: break
                j += 1
            out.append("(" + _swap_group(s[i + 1:j]) + ")")
            i = j + 1
        else:
            out.append(s[i]); i += 1
    return "".join(out)

def _swap_group(inner):
    d = 0; pos = -1
    for k, c in enumerate(inner):
        if c == "(": d += 1
        elif c == ")": d -= 1
        elif c == "◇" and d == 0: pos = k        # render gives exactly one depth-0 ◇
    if pos < 0:
        return _swap_ops(inner)                    # no top-level ◇: recurse for nesting
    return _swap_ops(inner[pos + 1:].strip()) + " ◇ " + _swap_ops(inner[:pos].strip())


def _rebind_dual_body(body, eq1_text, eq2_text):
    """Restore positional Lean binder order after mirroring a proof body.

    Dualizing terms can reverse the order in which variables first occur.
    ``intro`` and applications of the external hypothesis are positional, so
    operation swapping alone is insufficient.  Introduce goal variables in
    the original order and bridge mirrored-order ``h`` calls through a local
    theorem with an explicit argument permutation.
    """
    def vars_of(law):
        left, right = law
        variables = list(tvars(left))
        variables.extend(v for v in tvars(right) if v not in variables)
        return variables

    original_h = parse_law(eq1_text)
    mirrored_h = parse_law(dual_law(eq1_text))
    h_vars = vars_of(original_h)
    mirrored_h_vars = vars_of(mirrored_h)
    goal_vars = vars_of(parse_law(eq2_text))
    if set(h_vars) != set(mirrored_h_vars) or not h_vars:
        return None

    lines = body.split("\n")
    if not lines or not lines[0].strip().startswith("intro G _ h"):
        return None
    import re
    rest = re.sub(r"\bh\b", "hdual", "\n".join(lines[1:]))
    left, right = original_h
    first = "intro G _ h" + ((" " + " ".join(goal_vars)) if goal_vars else "")
    bridge = (
        "have hdual : ∀ (" + " ".join(mirrored_h_vars) + " : G), "
        + render(left) + " = " + render(right) + " := fun "
        + " ".join(mirrored_h_vars) + " => h " + " ".join(h_vars)
    )
    return first + "\n" + bridge + "\n" + rest

def tvars(t, acc=None):
    if acc is None: acc = []
    if t[0] == "var":
        if t[1] not in acc: acc.append(t[1])
    else:
        tvars(t[1], acc); tvars(t[2], acc)
    return acc

def positions(t, p=()):
    yield p, t
    if t[0] != "var":
        yield from positions(t[1], p + (1,))
        yield from positions(t[2], p + (2,))

def replace_at(t, p, new):
    if not p: return new
    if p[0] == 1: return ("op", replace_at(t[1], p[1:], new), t[2])
    return ("op", t[1], replace_at(t[2], p[1:], new))

def subterm_at(t, p):
    for pos, s in positions(t):
        if pos == p: return s
    raise KeyError(p)

# --------------------------------------------------------------- unification
def walk(t, sub):
    while t[0] == "var" and t[1] in sub:
        t = sub[t[1]]
    return t

def occurs(v, t, sub):
    t = walk(t, sub)
    if t[0] == "var": return t[1] == v
    return occurs(v, t[1], sub) or occurs(v, t[2], sub)

def unify(a, b, sub):
    a = walk(a, sub); b = walk(b, sub)
    if a[0] == "var":
        if b[0] == "var" and a[1] == b[1]: return sub
        if occurs(a[1], b, sub): return None
        s = dict(sub); s[a[1]] = b; return s
    if b[0] == "var":
        if occurs(b[1], a, sub): return None
        s = dict(sub); s[b[1]] = a; return s
    if a[0] == "op" and b[0] == "op":
        s = unify(a[1], b[1], sub)
        if s is None: return None
        return unify(a[2], b[2], s)
    return None

def apply_sub(t, sub):
    t = walk(t, sub)
    if t[0] == "var": return t
    return ("op", apply_sub(t[1], sub), apply_sub(t[2], sub))

def subst_flat(t, sub):
    """One-pass simultaneous substitution — replaces each var by sub[var] EXACTLY
    once, never chasing chains.  Correct for MATCH substitutions (flat, from a
    ground-ish target) and, unlike walk-based apply_sub, always terminates: a
    non-renamed rule can match a subterm with swapped vars, yielding a cyclic
    match sub like {a:b, b:a} that would make walk loop forever."""
    if t[0] == "var": return sub.get(t[1], t)
    return ("op", subst_flat(t[1], sub), subst_flat(t[2], sub))

# ------------------------------------------------------------ one-way match
def match(pat, term, sub):
    """Match rule pattern `pat` (its vars bindable) against ground-ish `term`."""
    if pat[0] == "var":
        v = pat[1]
        if v in sub: return sub[v] == term
        sub[v] = term; return True
    if term[0] != "op": return False
    return match(pat[1], term[1], sub) and match(pat[2], term[2], sub)

# ---------------------------------------------------------------- fresh vars
_FRESH = [0]
def fresh_name():
    n = _FRESH[0]; _FRESH[0] += 1
    return "v%d" % n

def rename_fresh(l, r, params):
    m = {p: fresh_name() for p in params}
    def go(t):
        if t[0] == "var": return ("var", m[t[1]])
        return ("op", go(t[1]), go(t[2]))
    return go(l), go(r), [m[p] for p in params]

def hole_name(avoid):
    for c in ["t", "s", "r", "q", "p", "u", "o", "n", "m", "k", "j", "i"]:
        if c not in avoid: return c
    return "hle"

# ================================================================ Fact
class Fact:
    __slots__ = ("name", "l", "r", "params", "proof", "deps")
    def __init__(self, name, l, r, params, proof, deps):
        self.name = name         # lean identifier
        self.l = l               # `from` term (oriented larger)
        self.r = r               # `to` term
        self.params = params     # ordered ∀-bound var names
        self.proof = proof       # lean expr proving  render(l) = render(r)
        self.deps = deps         # set of fact names referenced by proof

    def statement(self):
        binders = " ".join("(%s : G)" % p for p in self.params) or "(_z : G)"
        return "∀ %s, %s = %s" % (binders, render(self.l), render(self.r))

    def have_line(self):
        binders = " ".join(self.params) if self.params else "_z"
        return "have %s : %s := fun %s => %s" % (
            self.name, self.statement(), binders, self.proof)

# ================================================================ completion
def orient(P, Q):
    """Return (frm,to) with frm the larger term (KBO-ish: size then string)."""
    if (tsize(P), render(P)) >= (tsize(Q), render(Q)):
        return P, Q, True   # frm=P,to=Q, forward
    return Q, P, False       # frm=Q,to=P

def superpose(A, B, counter):
    """All critical pairs from superposing rule B into rule A. Yields Facts."""
    out = []
    al, ar, aparams = rename_fresh(A.l, A.r, A.params)
    bl, br, bparams = rename_fresh(B.l, B.r, B.params)
    for p, sub_t in positions(al):
        if sub_t[0] == "var":       # superpose only at non-variable subterms
            continue
        sigma = unify(sub_t, bl, {})
        if sigma is None: continue
        Als = apply_sub(al, sigma)
        P = replace_at(Als, p, apply_sub(br, sigma))   # A.l with subterm rewritten by B
        Q = apply_sub(ar, sigma)                        # A.r
        if P == Q: continue
        # Fail-fast on runaway growth: compound=compound hypotheses (LHS not a
        # single var) can explode into deep terms that never enter a usable fact
        # (normalize_fact caps `from` at MAX_FROM anyway) but still cost O(size)
        # in tvars/render here and can blow the time budget.  Drop them early.
        if tsize(P) > CP_SIZE_CAP or tsize(Q) > CP_SIZE_CAP: continue
        # `keep` = vars that survive into the critical pair (the lemma's binders).
        # Any other var occurring in the instance args is a "filler": the lemma
        # holds for ALL its values, so pin it to a surviving param (needs one).
        keep = set(tvars(P) + tvars(Q))
        if not keep: continue
        anchor = ("var", (tvars(P) + tvars(Q))[0])
        def _pin(t):
            if t[0] == "var": return t if t[1] in keep else anchor
            return ("op", _pin(t[1]), _pin(t[2]))
        # proofs of the two instances
        a_args = " ".join(render(_pin(apply_sub(("var", v), sigma))) for v in aparams)
        b_args = " ".join(render(_pin(apply_sub(("var", v), sigma))) for v in bparams)
        aInst = "(%s %s)" % (A.name, a_args) if a_args else A.name   # Als = Q
        bInst = "(%s %s)" % (B.name, b_args) if b_args else B.name   # subterm = its B.r
        avoid = set(tvars(P) + tvars(Q))
        hn = hole_name(avoid)
        ctx = render(replace_at(Als, p, ("var", hn)))
        # congrArg (fun hn => ctx) bInst : Als = P
        congr = "congrArg (fun %s => %s) %s" % (hn, ctx, bInst)
        # proof of  P = Q :  (congr).symm.trans aInst
        proofPQ = "((%s).symm.trans %s)" % (congr, aInst)
        frm, to, fwd = orient(P, Q)
        proof = proofPQ if fwd else "(%s).symm" % proofPQ
        params = tvars(frm) + [v for v in tvars(to) if v not in tvars(frm)]
        nm = "L%d" % counter[0]; counter[0] += 1
        out.append(Fact(nm, frm, to, params, proof, {A.name, B.name}))
    return out

def base_fact(eq1_text):
    """Fact h0:  big = x   from hypothesis  x = big  (proof (h ..).symm)."""
    l1, r1 = parse_law(eq1_text)              # l1 = x (var), r1 = big
    hvars = tvars(l1) + [v for v in tvars(r1) if v not in tvars(l1)]
    args = " ".join(hvars)
    proof = "(h %s).symm" % args if args else "h.symm"
    return Fact("h0", r1, l1, hvars, proof, set())   # from=big, to=x

MAX_FROM = 13
TIME_CAP = 8.0        # hard wall-clock budget per completion (fail-fast fallback)
CP_SIZE_CAP = 22      # drop critical pairs bigger than this before any tvars/render
FACT_CAP = 1500       # provable cases saturate in <100 facts; big sets only slow reduce_path

# One wall-clock deadline honored by EVERY long loop (step, reduce_path, the
# round loop) so prove() ALWAYS returns within TIME_CAP — even on compound=
# compound hypotheses that explode the fact set.  Set at each _prove_direct entry.
_DEADLINE = [0.0]
def _expired():
    return time.time() > _DEADLINE[0]

class Completion:
    """Incremental critical-pair saturation with early-exit hooks."""
    def __init__(self, eq1_text):
        _FRESH[0] = 0
        self.counter = [0]
        self.facts = [base_fact(eq1_text)]
        self.seen = {(render(self.facts[0].l), render(self.facts[0].r))}
        self.frontier = list(self.facts)
        self.t0 = time.time()

    def _add(self, cp):
        """Interreduce a raw critical pair by existing rules, then register it."""
        nf = normalize_fact(cp, self.facts)
        if nf is None: return None
        key = (render(nf.l), render(nf.r))
        if key in self.seen: return None
        self.seen.add(key); return nf

    def step(self, verbose=False):
        """Run one saturation round. Return number of new facts."""
        newf = []
        for A in self.frontier:
            if _expired():                            # bail before a fresh A's inner sweep
                self.facts += newf; self.frontier = newf; return len(newf)
            for B in self.facts:
                for cp in superpose(A, B, self.counter):
                    c = self._add(cp)
                    if c: newf.append(c)
                for cp in superpose(B, A, self.counter):
                    c = self._add(cp)
                    if c: newf.append(c)
                if _expired():
                    self.facts += newf; self.frontier = newf; return len(newf)
            if len(self.facts) + len(newf) > FACT_CAP: break
        self.facts += newf; self.frontier = newf
        if verbose:
            print("  round: +%d facts (total %d)" % (len(newf), len(self.facts)))
        return len(newf)

# ============================================================ goal proving
def find_trivial(facts):
    """Detect a collapsed magma.  Return ('eq2', fact) if a var=var fact exists,
    or ('const', fact) if a op(a,b)=c fact with c free exists."""
    for f in facts:
        if f.l[0] == "var" and f.r[0] == "var" and f.l[1] != f.r[1]:
            return ("eq2", f)
    for f in facts:
        if f.l[0] == "op" and f.r[0] == "var" and f.r[1] not in tvars(f.l):
            return ("const", f)
    return None

def reduce_path(term, facts, max_iters=60):
    """Rewrite `term` to a normal form using strictly size-reducing forward
    rules (f.l -> f.r, all rule vars fixed by matching f.l). Return (path, steps)
    where path = [term, ..., nf] and steps[i] = (f,pos,sub,True) took path[i]->path[i+1]."""
    path = [term]; steps = []
    for _ in range(max_iters):
        if _expired(): break
        cur = path[-1]; applied = False
        for pos, sub_t in positions(cur):
            if _expired(): return path, steps      # bail mid-sweep; a large fact set
            for f in facts:                         # makes one position-scan multi-second
                # A reducing rule shrinks: f.r can't be larger than what it rewrites.
                # Skip oversized rules BEFORE apply_sub, which would otherwise build a
                # huge term (millions of nodes) and only then fail the size check.
                if tsize(f.r) > tsize(sub_t): continue
                if not set(tvars(f.r)) <= set(tvars(f.l)): continue
                sub = {}
                if match(f.l, sub_t, sub) and all(v in sub for v in tvars(f.l)):
                    newsub = subst_flat(f.r, sub)                # flat: never loops
                    if tsize(newsub) >= tsize(sub_t): continue   # strict decrease
                    newt = replace_at(cur, pos, newsub)
                    if newt == cur: continue
                    path.append(newt); steps.append((f, pos, sub, True)); applied = True
                    break
            if applied: break
        if not applied: break
    return path, steps

def step_just(term_before, just):
    f, pos, sub, fwd = just
    params = f.params
    args = " ".join(render(sub.get(v, ("var", v))) for v in params)
    base = ("%s %s" % (f.name, args)) if args else f.name
    if not fwd:
        base = "(%s).symm" % base
    if pos:
        avoid = set(tvars(term_before))
        hn = hole_name(avoid)
        ctx = render(replace_at(term_before, pos, ("var", hn)))
        if fwd:
            base = "congrArg (fun %s => %s) (%s)" % (hn, ctx, base)
        else:
            base = "congrArg (fun %s => %s) (%s)" % (hn, ctx, base)
    else:
        if fwd:
            base = "%s" % base
    return base, f.name

def chain_expr(terms, steps):
    """Build a Lean term proving render(terms[0]) = render(terms[-1]).
    steps[i] connects terms[i]->terms[i+1]; each is
    ('rule', f, pos, sub, fwd)  or  ('raw', expr_string)."""
    if not steps:
        return "rfl", set()
    parts = []; used = set()
    for i, st in enumerate(steps):
        if st[0] == "raw":
            parts.append(st[1])
        else:
            _, f, pos, sub, fwd = st
            expr, nm = step_just(terms[i], (f, pos, sub, fwd))
            used.add(nm); parts.append(expr)
    acc = parts[-1]
    for e in reversed(parts[:-1]):
        acc = "(%s).trans (%s)" % (e, acc)   # fully-grouped, right-associative
    return acc, used

def normalize_fact(cp, facts):
    """Reduce a raw critical pair cp (from=cp.l, to=cp.r, proof cp.proof) to
    normal form under the current rules, composing the proof. Return Fact/None."""
    pathF, stepsF = reduce_path(cp.l, facts)   # cp.l -> frm'
    pathT, stepsT = reduce_path(cp.r, facts)   # cp.r -> to'
    frmN, toN = pathF[-1], pathT[-1]
    if frmN == toN: return None
    # chain:  frmN <-..(rev F).. cp.l  --raw-->  cp.r  ..(fwd T).. -> toN
    terms = list(reversed(pathF)) + list(pathT)
    steps = []
    for j in range(len(stepsF) - 1, -1, -1):
        f, pos, sub, _ = stepsF[j]
        steps.append(("rule", f, pos, sub, False))
    steps.append(("raw", cp.proof))
    for f, pos, sub, _ in stepsT:
        steps.append(("rule", f, pos, sub, True))
    expr, used = chain_expr(terms, steps)
    if (tsize(frmN), render(frmN)) >= (tsize(toN), render(toN)):
        L, R, pf = frmN, toN, expr
    else:
        L, R, pf = toN, frmN, "(%s).symm" % expr
    if tsize(L) > MAX_FROM: return None
    params = tvars(L) + [v for v in tvars(R) if v not in tvars(L)]
    if not params: return None
    # Intermediate chain terms may mention vars that vanish from the normal
    # form; the lemma holds for ALL their values, so pin any stray var (a v\d+
    # identifier not among the binders) to the first param.
    import re as _re
    stray = [v for v in set(_re.findall(r"\bv\d+\b", pf)) if v not in params]
    for v in stray:
        pf = _re.sub(r"\b%s\b" % v, params[0], pf)
    return Fact(cp.name, L, R, params, pf, set(cp.deps) | used)

def collect_used(names, facts):
    by = {f.name: f for f in facts}
    used = set(); stack = list(names)
    while stack:
        n = stack.pop()
        if n in used or n not in by: continue
        used.add(n)
        stack.extend(by[n].deps)
    return used

# ============================================================ top-level
def _emit(head, terms, steps, facts):
    used_names = set()
    calc_lines = ["calc " + render(terms[0])]
    for i, just in enumerate(steps):
        expr, nm = step_just(terms[i], just)
        used_names.add(nm)
        calc_lines.append("  _ = %s := %s" % (render(terms[i + 1]), expr))
    used = collect_used(used_names, facts)
    haves = [x.have_line() for x in facts if x.name in used]
    return "\n".join([head] + haves + calc_lines)

def try_goal(facts, gl, gr, head):
    """Attempt to close the goal from the current fact set."""
    rL, rR = render(gl), render(gr)
    # (1) trivial-magma collapse
    triv = find_trivial(facts)
    if triv:
        kind, f = triv
        used = collect_used({f.name}, facts)
        haves = [x.have_line() for x in facts if x.name in used]
        if kind == "eq2":                     # f : ∀ a b, a = b  (exactly 2 binders)
            proof = "%s %s %s" % (f.name, rL, rR)
        else:                                  # f : ∀ .., BIG(..) = c  (c free ⇒ total collapse)
            # f says BIG(..) equals ANY value of c.  Apply it twice with every
            # binder pinned to rL EXCEPT the c-slot, which we set to rL then rR:
            #   (f ..rL..)  : BIG(rL..) = rL     (c := rL)
            #   (f ..rR..)  : BIG(rL..) = rR     (c := rR)
            # both share the same BIG(rL..), so .symm.trans gives  rL = rR.
            # c can sit at ANY index in params (for h0 it is first, not last) —
            # locating it by name is what makes this arity/position correct.
            ci = f.params.index(f.r[1])        # index of the free RHS var c
            def _app(cval):
                a = [rL] * len(f.params); a[ci] = cval
                return "%s %s" % (f.name, " ".join(a))
            proof = "((%s).symm.trans (%s))" % (_app(rL), _app(rR))
        return "\n".join([head] + haves + ["exact %s" % proof]), "trivial-%s" % kind
    # (2) normalize both sides to a common normal form, stitch the two chains
    pathL, stepsL = reduce_path(gl, facts)
    pathR, stepsR = reduce_path(gr, facts)
    if render(pathL[-1]) == render(pathR[-1]):
        terms = list(pathL) + list(reversed(pathR[:-1]))
        steps = list(stepsL)
        # walk pathR backwards: pathR[j] -> pathR[j+1] was forward; present reversed
        for j in range(len(stepsR) - 1, -1, -1):
            f, pos, sub, _ = stepsR[j]
            steps.append((f, pos, sub, False))
        if render(terms[0]) == render(gl) and render(terms[-1]) == render(gr):
            return _emit(head, terms, steps, facts), \
                   "normalize(%d+%d steps)" % (len(stepsL), len(stepsR))
    return None, None

def _prove_direct(eq1_text, eq2_text, rounds, verbose):
    _DEADLINE[0] = time.time() + TIME_CAP          # arm the shared wall-clock guard
    gl, gr = parse_law(eq2_text)
    gvars = tvars(gl) + [v for v in tvars(gr) if v not in tvars(gl)]
    head = "intro G _ h" + ((" " + " ".join(gvars)) if gvars else "")
    comp = Completion(eq1_text)
    # try the goal after each saturation round (early exit as soon as provable)
    for rnd in range(rounds):
        if _expired(): break
        body, info = try_goal(comp.facts, gl, gr, head)
        if body is not None:
            return body, "%s @round%d (%d facts)" % (info, rnd, len(comp.facts))
        added = comp.step(verbose=verbose)
        if added == 0: break
    if not _expired():
        body, info = try_goal(comp.facts, gl, gr, head)
        if body is not None:
            return body, "%s @final (%d facts)" % (info, len(comp.facts))
    return None, "no-proof (%d facts)" % len(comp.facts)

def prove(eq1_text, eq2_text, rounds=6, verbose=False, try_dual=False):
    """Return (body, info) with body an allowlist Lean tactic block, or (None,reason).
    Duality (Φ-map, sound helpers kept below) is OFF by default: measured 0 lift on
    order-4 TRUE and it doubles latency on the hard tail (dual is compound too).
    Pass try_dual=True to enable the mirror-theory retry for other distributions."""
    body, info = _prove_direct(eq1_text, eq2_text, rounds, verbose)
    if body is not None:
        return body, info
    if try_dual:
        db, di = _prove_direct(dual_law(eq1_text), dual_law(eq2_text), rounds, verbose)
        if db is not None:
            repaired = _rebind_dual_body(_swap_ops(db), eq1_text, eq2_text)
            if repaired is not None:
                return repaired, "dual[%s]" % di
    return None, info
