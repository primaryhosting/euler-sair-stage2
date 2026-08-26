#!/usr/bin/env python3
"""Matching chain-search TRUE prover (technique from the ETP/public-200 lane),
reimplemented self-contained in EULER's term format so it can be inlined.

Term := ("var", name) | ("op", left, right).
A proof of E1 => E2 is a chain of terms goalLHS = t0, t1, ..., tk = goalRHS
where each step ti -> ti+1 rewrites one subterm using E1 (fwd hl->hr or rev hr->hl),
with the free variables of E1 filled from the goal's subterm pool. chain_recheck
re-derives every step from the terms alone (a search bug cannot self-certify).
"""
import itertools, time

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

def law_vars(t, acc=None):
    if acc is None: acc = []
    if t[0] == "var":
        if t[1] not in acc: acc.append(t[1])
    else:
        law_vars(t[1], acc); law_vars(t[2], acc)
    return acc

def render(t):
    if t[0] == "var": return t[1]
    return "(" + render(t[1]) + " ◇ " + render(t[2]) + ")"

def tsize(t):
    if t[0] == "var": return 1
    return 1 + tsize(t[1]) + tsize(t[2])

def positions(t, p=()):
    yield p, t
    if t[0] != "var":
        yield from positions(t[1], p + (1,))
        yield from positions(t[2], p + (2,))

def replace_at(t, p, new):
    if not p: return new
    if p[0] == 1: return ("op", replace_at(t[1], p[1:], new), t[2])
    return ("op", t[1], replace_at(t[2], p[1:], new))

def subst(t, sub):
    if t[0] == "var": return sub[t[1]]
    return ("op", subst(t[1], sub), subst(t[2], sub))

def match(pat, term, sub):
    if pat[0] == "var":
        v = pat[1]
        if v in sub: return sub[v] == term
        sub[v] = term; return True
    if term[0] != "op": return False
    return match(pat[1], term[1], sub) and match(pat[2], term[2], sub)

def subterms(t, acc=None):
    if acc is None: acc = []
    acc.append(t)
    if t[0] != "var":
        subterms(t[1], acc); subterms(t[2], acc)
    return acc

def chain_prove(law1, law2, max_depth=6, time_cap=45.0, max_size=16,
                node_cap=600000, frontier_cap=200000):
    hl, hr = law1
    hvars = law_vars(hl) + [v for v in law_vars(hr) if v not in law_vars(hl)]
    gl, gr = law2
    pool, seen_pool = [], set()
    for s in subterms(gl) + subterms(gr):
        k = render(s)
        if k not in seen_pool:
            seen_pool.add(k); pool.append(s)
    target = render(gr)
    if render(gl) == target:
        return [gl], [], {"reason": "identical"}
    frontier = [(gl, [gl], [])]; seen = {render(gl)}; nodes = 0; trunc = False; t0 = time.time()
    for depth in range(max_depth):
        nxt = []
        for term, path, steps in frontier:
            for direction, pat, out in (("fwd", hl, hr), ("rev", hr, hl)):
                for pos, sub_t in positions(term):
                    sub = {}
                    if not match(pat, sub_t, sub): continue
                    free = [v for v in hvars if v not in sub]
                    for combo in itertools.product(pool, repeat=len(free)):
                        full = dict(sub); full.update(dict(zip(free, combo)))
                        try: new_term = replace_at(term, pos, subst(out, full))
                        except KeyError: continue
                        if tsize(new_term) > max_size: continue
                        nodes += 1
                        if nodes > node_cap or time.time() - t0 > time_cap:
                            return None, None, {"reason": "capped", "nodes": nodes, "depth": depth}
                        k = render(new_term)
                        if k == target:
                            return path + [new_term], steps + [(direction, pos, full)], {"reason": "found", "depth": depth + 1, "nodes": nodes}
                        if k in seen: continue
                        seen.add(k); nxt.append((new_term, path + [new_term], steps + [(direction, pos, full)]))
        if len(nxt) > frontier_cap: trunc = True; nxt = nxt[:frontier_cap]
        frontier = nxt
        if not frontier:
            return None, None, {"reason": "frontier_cap" if trunc else "exhausted", "depth": depth + 1}
    return None, None, {"reason": "depth_cap", "nodes": nodes}

def text_vars(text):
    seen = []
    for v in __import__("re").findall(r"\b([a-z])\b", text):
        if v not in seen: seen.append(v)
    return seen

def emit_chain_proof(terms, steps, eq1_text, eq2_text):
    """Emit the judge tactic body: calc chain, h-args at root, congrArg deeper."""
    hvars = text_vars(eq1_text); gvars = text_vars(eq2_text)
    hole = next((c for c in "tsrqpnmk" if c not in gvars), "t")
    lines = ["intro G _ h" + ((" " + " ".join(gvars)) if gvars else ""),
             "calc " + render(terms[0])]
    for i, (direction, pos, sub) in enumerate(steps):
        args = " ".join(render(sub[v]) for v in hvars)
        just = ("h " + args) if args else "h"
        if direction == "rev": just = "(%s).symm" % just
        elif pos: just = "(%s)" % just
        if pos:
            ctx = replace_at(terms[i], pos, ("var", hole))
            just = "congrArg (fun %s => %s) %s" % (hole, render(ctx), just)
        lines.append("  _ = %s := %s" % (render(terms[i + 1]), just))
    return "\n".join(lines)

def chain_recheck(terms, law1, law2):
    hl, hr = law1; hvars = law_vars(hl) + [v for v in law_vars(hr) if v not in law_vars(hl)]
    if render(terms[0]) != render(law2[0]): return False, "start"
    if render(terms[-1]) != render(law2[1]): return False, "end"
    for i in range(len(terms) - 1):
        a, b = terms[i], terms[i + 1]; ok = False
        for pos, sub_a in positions(a):
            sub_b = None
            for q, s in positions(b):
                if q == pos: sub_b = s; break
            if sub_b is None: continue
            if replace_at(a, pos, sub_b) != b: continue
            for pat, out in ((hl, hr), (hr, hl)):
                sub = {}
                if not match(pat, sub_a, sub): continue
                sub2 = dict(sub)
                if not match(out, sub_b, sub2): continue
                if all(v in sub2 for v in hvars): ok = True; break
            if ok: break
        if not ok: return False, "step %d" % i
    return True, "ok"
