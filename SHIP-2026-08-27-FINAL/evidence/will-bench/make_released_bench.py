"""
WILL released-set bench — mechanical tiers only (no LLM, no oracle available in
this sandbox), fixed solver (post FALSE-preamble fix). Deterministic 50-FALSE +
50-TRUE sample drawn from the released `evaluation_normal` set (seeded). We run
WILL's Marathon path and, for every answer it writes, (a) confirm the verdict
matches ground truth, (b) confirm the emitted Lean cert now carries the correct
preamble shape, and (c) for FALSE, independently re-check the table is a genuine
counterexample. This is a mechanical-tier floor on released problems, NOT an
official-judge run and NOT a private-set claim.
"""
import importlib.util, json, os, re, random
HERE=os.path.dirname(os.path.abspath(__file__))
WILL=os.path.join(HERE,"..","..","WILL-SUBMISSION-2026-08-25.py")
spec=importlib.util.spec_from_file_location("will",WILL)
m=importlib.util.module_from_spec(spec)
try: spec.loader.exec_module(m)
except SystemExit: pass

rows=[json.loads(l) for l in open("/tmp/evaluation_normal.jsonl") if l.strip()]
false=[r for r in rows if r["answer"] is False]
true=[r for r in rows if r["answer"] is True]
rng=random.Random(20260826)
rng.shuffle(false); rng.shuffle(true)
sample=false[:50]+true[:50]
man=os.path.join(HERE,"released-bench-manifest.jsonl")
outp=os.path.join(HERE,"released-bench-output.jsonl")
certdir=os.path.join(HERE,"released-certs"); os.makedirs(certdir,exist_ok=True)
with open(man,"w") as fh:
    for r in sample:
        fh.write(json.dumps({"id":r["id"],"equation1":r["equation1"],
                             "equation2":r["equation2"]})+"\n")
gt={r["id"]:("false" if r["answer"] is False else "true") for r in sample}
keys=("JUDGE_MARATHON_MANIFEST","JUDGE_MARATHON_OUTPUT","JUDGE_MARATHON_PER_PROBLEM")
old={k:os.environ.get(k) for k in keys}
os.environ.update({keys[0]:man,keys[1]:outp,keys[2]:"25"})
try: m.marathon()
finally:
    for k,v in old.items():
        os.environ.pop(k,None) if v is None else os.environ.__setitem__(k,v)

ans=[json.loads(l) for l in open(outp) if l.strip()]
by={a["id"]:a for a in ans}
PRE=("import JudgeProblem\nimport JudgeDecide.DecideBang\n"
     "import JudgeFinOp.MemoFinOp\nopen MemoFinOp")
f_solved=f_shape=f_model=0; t_solved=t_shape=0; wrong=0
byid_sample={r["id"]:r for r in sample}
for r in sample:
    pid=r["id"]; a=by.get(pid)
    if not a: continue
    v=a.get("verdict"); code=a.get("code","")
    if v!=gt[pid]: wrong+=1; continue  # WILL only writes self-verified; must match GT
    if v=="false":
        f_solved+=1
        if "finOpTable" in code and "decideFin!" in code and code.startswith(PRE): f_shape+=1
        mm=re.search(r'finOpTable\s+"(\[\[.*?\]\])"',code)
        if mm:
            tbl=json.loads(mm.group(1))
            if m.table_is_counterexample(m.prep_problem(r),len(tbl),tbl): f_model+=1
        open(os.path.join(certdir,pid+".lean"),"w").write(code)
    else:
        t_solved+=1
        if code.startswith("import JudgeProblem") and "decideFin!" not in code and "sorry" not in code: t_shape+=1
        open(os.path.join(certdir,pid+".lean"),"w").write(code)

log=os.path.join(HERE,"released-bench-result.md")
with open(log,"w") as fh:
    fh.write("# WILL released-set bench (mechanical tiers, fixed solver)\n\n")
    fh.write("Deterministic 50-FALSE + 50-TRUE sample from `evaluation_normal` "
             "(seed 20260826), 25s/problem, no LLM and no oracle in this sandbox.\n")
    fh.write("WILL writes only answers its own tiers self-verify; we additionally\n")
    fh.write("check verdict==ground-truth, cert shape, and (FALSE) independent model recheck.\n")
    fh.write("Mechanical-tier floor on released problems — NOT an official-judge or private-set run.\n\n")
    fh.write(f"- FALSE solved (mechanical): **{f_solved}/50**  "
             f"(cert shape OK {f_shape}/{f_solved}, model re-checked {f_model}/{f_solved})\n")
    fh.write(f"- TRUE solved (chain+collapse, mechanical): **{t_solved}/50**  "
             f"(cert shape OK {t_shape}/{t_solved})\n")
    fh.write(f"- answers disagreeing with ground truth: {wrong} (WILL self-verifies before writing)\n")
print(open(log).read())
