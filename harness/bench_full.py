#!/usr/bin/env python3
"""Full end-to-end benchmark of EULER v8 on normal.jsonl (TRUE via Axle, FALSE via
Python finite-model verification == judge decideFin! semantics). Measures real
solve rate AND catches any wrong-direction / bad-counterexample bug."""
import importlib.util, json, os, pathlib, sys, time, random, itertools
HARNESS = pathlib.Path(__file__).resolve().parent
REPO = HARNESS.parent
sys.setrecursionlimit(20000); sys.path.insert(0, str(HARNESS))
from axle_judge import axle_true, make_true_lean
from mini_twee import parse_law

CERTS = REPO / "certs"

DST = os.environ.get("EULER_SOLVER", str(REPO / "EQT02-S00021-infra-failfast.py"))
spec = importlib.util.spec_from_file_location("euler", DST)
m = importlib.util.module_from_spec(spec); spec.loader.exec_module(m)

def ev(t, asg, table):
    if t[0] == "var": return asg[t[1]]
    return table[ev(t[1], asg, table)][ev(t[2], asg, table)]

def holds_forall(law, n, table):
    l, r = parse_law(law); vs = sorted(set(_vars(l) | _vars(r)))
    for combo in itertools.product(range(n), repeat=len(vs)):
        asg = dict(zip(vs, combo))
        if ev(l, asg, table) != ev(r, asg, table): return False
    return True

def fails_exists(law, n, table):
    l, r = parse_law(law); vs = sorted(set(_vars(l) | _vars(r)))
    for combo in itertools.product(range(n), repeat=len(vs)):
        asg = dict(zip(vs, combo))
        if ev(l, asg, table) != ev(r, asg, table): return True
    return False

def _vars(t, acc=None):
    if acc is None: acc = set()
    if t[0] == "var": acc.add(t[1])
    else: _vars(t[1], acc); _vars(t[2], acc)
    return acc

_cur = {"e1": None, "e2": None, "false_stash": None}
_orig_lean_false = m.lean_false
def stash_lean_false(n, table):
    _cur["false_stash"] = (n, table)
    return _orig_lean_false(n, table)
m.lean_false = stash_lean_false

def fake_judge(verdict, code):
    if verdict == "true":
        tac = code.split("def submission : Goal := by\n", 1)[1]
        body = "\n".join(ln[2:] if ln.startswith("  ") else ln for ln in tac.split("\n")).strip("\n")
        v, _ = axle_true(_cur["e1"], _cur["e2"], body)
        if v and _cur.get("ids"):
            CERTS.mkdir(exist_ok=True)
            (CERTS / "{}__{}.lean".format(*_cur["ids"])).write_text(
                make_true_lean(_cur["e1"], _cur["e2"], body))
        return {"status": "accepted" if v else "rejected"}
    else:
        st = _cur["false_stash"]
        if not st: return {"status": "rejected"}
        n, table = st
        ok = holds_forall(_cur["e1"], n, table) and fails_exists(_cur["e2"], n, table)
        if ok and _cur.get("ids"):
            CERTS.mkdir(exist_ok=True)
            (CERTS / "{}__{}.countermodel.json".format(*_cur["ids"])).write_text(
                json.dumps({"n": n, "table": table}))
        return {"status": "accepted" if ok else "rejected"}
m.call_judge = fake_judge
m.call_llm = lambda *a, **k: {}

FSET = sys.argv[1] if len(sys.argv) > 1 else "normal"
NS = int(sys.argv[2]) if len(sys.argv) > 2 else 50
BUDGET = float(sys.argv[3]) if len(sys.argv) > 3 else 60.0
probs = [json.loads(l) for l in open(HARNESS / "problems" / f"{FSET}.jsonl")]
random.seed(9); sample = random.sample(probs, min(NS, len(probs)))
print(f"{FSET}: sampling {len(sample)} (true+false)", flush=True)

solved = wrong = 0; tcount = fcount = tsolved = fsolved = 0; t0 = time.time()
for k, p in enumerate(sample):
    _cur["e1"] = m.normalise(p["equation1"]); _cur["e2"] = m.normalise(p["equation2"]); _cur["false_stash"] = None
    _cur["ids"] = (p["eq1_id"], p["eq2_id"])
    ans = p.get("answer")
    if ans: tcount += 1
    else: fcount += 1
    prob = {"equation1": p["equation1"], "equation2": p["equation2"], "eq1_id": p["eq1_id"], "eq2_id": p["eq2_id"]}
    try: res = m.solve(prob, budget_seconds=BUDGET)
    except Exception as ex: res = "exc:" + type(ex).__name__
    if res == "accepted":
        solved += 1
        if ans: tsolved += 1
        else: fsolved += 1
    else:
        print(f"  FAIL {'T' if ans else 'F'} {p['eq1_id']}=>{p['eq2_id']}: {res}", flush=True)
print(f"\n==== EULER v8 FULL {FSET}: {solved}/{len(sample)} solved, {time.time()-t0:.0f}s ====", flush=True)
print(f"TRUE: {tsolved}/{tcount}   FALSE: {fsolved}/{fcount}", flush=True)
print(f"METRIC solve_rate={solved/max(len(sample),1):.4f}", flush=True)
print(f"METRIC true_rate={tsolved/max(tcount,1):.4f}", flush=True)
print(f"METRIC false_rate={fsolved/max(fcount,1):.4f}", flush=True)
