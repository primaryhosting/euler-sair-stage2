#!/usr/bin/env python3
"""End-to-end TRUE-side benchmark of EULER v8 solve(): patch call_judge to verify
true-proofs via Axle (reject false-certs), run on TRUE problems from normal.jsonl,
report solve rate + which tier won. Measures transitivity's real lift."""
import importlib.util, json, os, pathlib, sys, time, random
HARNESS = pathlib.Path(__file__).resolve().parent
REPO = HARNESS.parent
sys.setrecursionlimit(20000); sys.path.insert(0, str(HARNESS))
from axle_judge import axle_true, make_true_lean

CERTS = REPO / "certs"

DST = os.environ.get("EULER_SOLVER", str(REPO / "EQT02-S00021-infra-failfast.py"))
spec = importlib.util.spec_from_file_location("euler", DST)
m = importlib.util.module_from_spec(spec); spec.loader.exec_module(m)

_cur = {"e1": None, "e2": None, "ncalls": 0}
def fake_judge(verdict, code):
    _cur["ncalls"] += 1
    if verdict != "true":
        return {"status": "rejected"}          # benchmarking TRUE problems only
    tac = code.split("def submission : Goal := by\n", 1)[1]
    body = "\n".join(ln[2:] if ln.startswith("  ") else ln for ln in tac.split("\n")).strip("\n")
    v, _ = axle_true(_cur["e1"], _cur["e2"], body)
    if v and _cur.get("ids"):
        CERTS.mkdir(exist_ok=True)
        (CERTS / "{}__{}.lean".format(*_cur["ids"])).write_text(
            make_true_lean(_cur["e1"], _cur["e2"], body))
    return {"status": "accepted" if v else "rejected"}
m.call_judge = fake_judge
m.call_llm = lambda *a, **k: {}                 # no LLM in benchmark

FSET = sys.argv[1] if len(sys.argv) > 1 else "normal"
probs = [json.loads(l) for l in open(HARNESS / "problems" / f"{FSET}.jsonl")]
true_probs = [p for p in probs if p.get("answer") is True]
random.seed(3); sample = random.sample(true_probs, min(40, len(true_probs)))
print(f"benchmarking {FSET}: {len(true_probs)} TRUE problems, sampling {len(sample)}", flush=True)

solved = 0; by_tier = {}; t0 = time.time()
for k, p in enumerate(sample):
    _cur["e1"] = m.normalise(p["equation1"]); _cur["e2"] = m.normalise(p["equation2"])
    _cur["ncalls"] = 0; _cur["ids"] = (p["eq1_id"], p["eq2_id"])
    prob = {"equation1": p["equation1"], "equation2": p["equation2"],
            "eq1_id": p["eq1_id"], "eq2_id": p["eq2_id"]}
    t1 = time.time()
    try:
        res = m.solve(prob, budget_seconds=60.0)
    except Exception as ex:
        res = "exc:" + type(ex).__name__
    dt = time.time() - t1
    tiers = getattr(m, "_tiers_attempted", set())
    won = "?"
    if res == "accepted":
        solved += 1
        # infer winning tier: the LAST attempted-but-not-added is the winner; simpler: mark transitivity if it was needed
        won = "transitivity" if "find_proof" in tiers else ("chain/mt" if ("chain" in tiers or "mini_twee" in tiers) else "early")
        by_tier[won] = by_tier.get(won, 0) + 1
    print(f"  {k+1}/40 {p['eq1_id']}=>{p['eq2_id']}: {res} [{dt:.0f}s, {_cur['ncalls']} judge calls] {won}", flush=True)
print(f"\n==== EULER v8 TRUE-side: {solved}/{len(sample)} solved, {time.time()-t0:.0f}s ====", flush=True)
print(f"winning-tier buckets: {by_tier}", flush=True)
print(f"METRIC true_rate={solved/max(len(sample),1):.4f}", flush=True)
