"""
WILL FALSE-side bench — technique-only, self-contained, self-verified.

Runs WILL's own Marathon path over a manifest of E1 |= E2 pairs that are each
FALSE (a finite magma satisfies E1 but violates E2). WILL is oracle-free: it must
find each countermodel by its OWN bounded CE search — no banks, no embedded certs.
For every answer WILL emits we (a) confirm the Lean cert carries the full FALSE
preamble + finOpTable + decideFin!, and (b) INDEPENDENTLY re-check the table is a
real counterexample with WILL's table_is_counterexample. This is a shape+model
check, NOT an official-judge run.
"""
import importlib.util, json, os, sys, tempfile

HERE = os.path.dirname(os.path.abspath(__file__))
WILL = os.path.join(HERE, "..", "..", "WILL-SUBMISSION-2026-08-25.py")
spec = importlib.util.spec_from_file_location("will", WILL)
m = importlib.util.module_from_spec(spec)
try:
    spec.loader.exec_module(m)
except SystemExit:
    pass

# 15 pairs, each FALSE with a small (n<=3) countermodel WILL can find by search.
PAIRS = [
    ("comm |= left-proj",      "x * y = y * x",           "x * y = x"),
    ("comm |= right-proj",     "x * y = y * x",           "x * y = y"),
    ("comm |= idempotent",     "x * y = y * x",           "x * x = x"),
    ("idempotent |= comm",     "x * x = x",               "x * y = y * x"),
    ("assoc |= comm",          "(x * y) * z = x * (y * z)","x * y = y * x"),
    ("left-proj |= comm",      "x * y = x",               "x * y = y * x"),
    ("left-proj |= right-proj","x * y = x",               "x * y = y"),
    ("comm |= assoc-collapse", "x * y = y * x",           "x * y = x * (x * y)"),
    ("idempotent |= left-proj","x * x = x",               "x * y = x"),
    ("comm |= x=xx",           "x * y = y * x",           "x = x * x"),
    ("assoc |= idempotent",    "(x * y) * z = x * (y * z)","x * x = x"),
    ("right-proj |= left-proj","x * y = y",               "x * y = x"),
    ("comm |= right-collapse", "x * y = y * x",           "x * y = y * (y * x)"),
    ("left-proj |= idempotent","x * y = x",               "x * x = y"),
    ("comm |= const",          "x * y = y * x",           "x * y = z * w"),
]

man = os.path.join(HERE, "false-bench-manifest.jsonl")
outp = os.path.join(HERE, "false-bench-output.jsonl")
certdir = os.path.join(HERE, "certs")
os.makedirs(certdir, exist_ok=True)
with open(man, "w", encoding="utf-8") as fh:
    for i, (name, e1, e2) in enumerate(PAIRS):
        fh.write(json.dumps({"id": f"wf{i:02d}", "name": name,
                             "equation1": e1, "equation2": e2}) + "\n")

keys = ("JUDGE_MARATHON_MANIFEST", "JUDGE_MARATHON_OUTPUT", "JUDGE_MARATHON_PER_PROBLEM")
old = {k: os.environ.get(k) for k in keys}
os.environ.update({keys[0]: man, keys[1]: outp, keys[2]: "20"})
try:
    m.marathon()
finally:
    for k, v in old.items():
        os.environ.pop(k, None) if v is None else os.environ.__setitem__(k, v)

ans = [json.loads(l) for l in open(outp, encoding="utf-8") if l.strip()]
by = {a["id"]: a for a in ans}
names = {f"wf{i:02d}": PAIRS[i] for i in range(len(PAIRS))}
solved = false_shape_ok = model_ok = 0
rows = []
for i,(nm,e1,e2) in enumerate(PAIRS):
    pid=f"wf{i:02d}"; a=by.get(pid)
    if not a:
        rows.append((pid,nm,"NO-ANSWER","","")); continue
    solved+=1
    code=a.get("code","")
    shape = (a.get("verdict")=="false" and "finOpTable" in code and "decideFin!" in code
             and code.startswith("import JudgeProblem\nimport JudgeDecide.DecideBang\n"
                                 "import JudgeFinOp.MemoFinOp\nopen MemoFinOp"))
    if shape: false_shape_ok+=1
    # independent model re-check
    prob=m.prep_problem({"id":pid,"equation1":e1,"equation2":e2})
    tbl=a.get("table"); n=a.get("n")
    mok=False
    if tbl is not None and n is not None:
        try: mok=m.table_is_counterexample(prob,n,tbl)
        except Exception: mok=False
    if mok: model_ok+=1
    open(os.path.join(certdir,pid+".lean"),"w",encoding="utf-8").write(code)
    rows.append((pid,nm,"FALSE" if a.get("verdict")=="false" else a.get("verdict"),
                 "shape-OK" if shape else "SHAPE-BAD",
                 "model-OK" if mok else "MODEL-BAD"))

log=os.path.join(HERE,"false-bench-result.md")
with open(log,"w",encoding="utf-8") as fh:
    fh.write("# WILL FALSE-side bench result\n\n")
    fh.write("Technique-only (oracle-free) Marathon over 15 FALSE pairs, 20s/problem.\n")
    fh.write("Each solved answer: cert carries full FALSE preamble + finOpTable + decideFin!,\n")
    fh.write("and the table is independently re-checked as a genuine counterexample.\n")
    fh.write("This is a shape + finite-model check, NOT an official-judge run.\n\n")
    fh.write(f"- solved: {solved}/{len(PAIRS)}\n")
    fh.write(f"- cert shape OK (full preamble): {false_shape_ok}/{solved}\n")
    fh.write(f"- countermodel independently re-verified: {model_ok}/{solved}\n\n")
    fh.write("| id | pair | verdict | cert shape | model recheck |\n|---|---|---|---|---|\n")
    for r in rows: fh.write("| "+" | ".join(r)+" |\n")
print(open(log).read())
