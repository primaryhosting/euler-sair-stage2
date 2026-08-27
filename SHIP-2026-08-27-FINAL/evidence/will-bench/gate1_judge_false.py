"""GATE 1 — compile WILL's emitted FALSE certificates under the REAL SAIR judge
(local Lean v4.32.2, ~/Projects/sair-stage2-repo/judge/verify.py). This is the
actual kernel check, not a Python shape check."""
import json, os, sys, pathlib
sys.path.insert(0, str(pathlib.Path.home()/"Projects/sair-stage2-repo"))
from judge import verify as J

HERE=os.path.dirname(os.path.abspath(__file__))
man=[json.loads(l) for l in open(os.path.join(HERE,"false-bench-manifest.jsonl")) if l.strip()]
byid={m["id"]:m for m in man}
out=[json.loads(l) for l in open(os.path.join(HERE,"false-bench-output.jsonl")) if l.strip()]

results=[]; accepted=0
for a in out:
    pid=a["id"]; p=byid[pid]
    problem={"id":pid,"eq1_id":1,"eq2_id":2,
             "equation1":p["equation1"],"equation2":p["equation2"]}
    raw=json.dumps({"verdict":a["verdict"],"code":a["code"]})
    r=J.verify_answer(problem, raw)
    st=r.get("status"); code=r.get("code")
    ok = (st=="accepted")
    if ok: accepted+=1
    results.append({"id":pid,"pair":p["name"],"status":st,"judge_code":code})
    print(f'{pid:6} {p["name"]:26} -> {st}{"" if ok else "  "+str(r.get("detail",""))[:70]}')

print(f"\nACCEPTED by real Lean 4.32.2 judge: {accepted}/{len(out)}")
open(os.path.join(HERE,"gate1-judge-false-results.json"),"w").write(json.dumps(results,indent=1))
