#!/usr/bin/env python3
"""Rebuild released_index.json from the four SAIR released eval files.
Deterministic: same inputs -> same index -> same sha256. See PROVENANCE.md."""
import json, hashlib, os
EVALS=["/tmp/evaluation_normal.jsonl","/tmp/evaluation_hard.jsonl",
       "/tmp/evaluation_extra_hard.jsonl","/tmp/evaluation_order5.jsonl"]
pairs=set(); hyps=set()
for f in EVALS:
    for line in open(f):
        if not line.strip(): continue
        r=json.loads(line); pairs.add((r["eq1_id"],r["eq2_id"])); hyps.add(r["eq1_id"])
idx={"source":"SAIR Stage 2 released eval sets (normal/hard/extra_hard/order5, 800 pairs)",
     "note":"Exclusion index for held-out cohort construction. released_pairs = every (eq1_id,eq2_id) in the released sets; released_hyps = every eq1_id used as hypothesis.",
     "released_pairs":sorted([list(p) for p in pairs]),
     "released_hyps":sorted(hyps)}
open("released_index.json","w").write(json.dumps(idx,indent=1))
print("released_pairs",len(idx["released_pairs"]),"released_hyps",len(idx["released_hyps"]))
print("sha256",hashlib.sha256(open("released_index.json","rb").read()).hexdigest())
