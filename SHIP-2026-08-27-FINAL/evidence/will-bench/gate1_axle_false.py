"""GATE 1 via Axle — compile WILL FALSE certs on Axiom's cloud Lean 4.32.2
(the judge's exact toolchain). Faithful by construction: we inline the judge's
OWN module sources (JudgeMagma/JudgeDecide/JudgeFinOp verbatim) + the judge's
exact EquationLHS/RHS + FALSE Goal from verify.py, then splice the cert body.
No hand-rolled preamble — this is the judge's code, made self-contained for a
single-file compiler."""
import importlib.util, json, os, re, sys, pathlib
sys.path.insert(0, str(pathlib.Path.home()/"Projects/brockian-mathematics"))
sys.path.insert(0, str(pathlib.Path.home()/"Projects/brockian-mathematics/engine"))
from engine import verify as V

JUDGE = pathlib.Path.home()/"Projects/sair-stage2-repo/judge"
MAGMA = (JUDGE/"JudgeMagma/Magma.lean").read_text()
# MemoFinOp minus its own import (JudgeMagma inlined above)
MEMO = "\n".join(l for l in (JUDGE/"JudgeFinOp/MemoFinOp.lean").read_text().splitlines()
                 if not l.strip().startswith("import "))
DECIDE_MACRO = 'macro "decideFin!" : tactic => `(tactic| decide)'

def eqdef(name, text):                      # replica of verify.py _equation_def
    text = text.replace("*", "◇")           # judge normalization
    seen, vs = set(), []
    for v in re.findall(r'\b([a-z])\b', text):
        if v not in seen: seen.add(v); vs.append(v)
    binders = " ".join(f"({v} : G)" for v in vs)
    return f"@[reducible] def {name} (G : Type _) [Magma G] : Prop := ∀ {binders}, {text}"

def strip_body(code):                       # drop the cert's imports + open (inlined here)
    out=[]
    for l in code.splitlines():
        s=l.strip()
        if s.startswith("import ") or s=="open MemoFinOp": continue
        out.append(l)
    return "\n".join(out).strip()

def build(eq1, eq2, code):
    return (
        "import Lean\n" + MAGMA + "\n" + DECIDE_MACRO + "\n" + MEMO + "\nopen MemoFinOp\n"
        + eqdef("EquationLHS", eq1) + "\n" + eqdef("EquationRHS", eq2) + "\n"
        + "abbrev Goal : Prop := ∃ (G : Type) (_ : Magma G), EquationLHS G ∧ ¬ EquationRHS G\n"
        + strip_body(code) + "\n")

if __name__ == "__main__":
    HERE=os.path.dirname(os.path.abspath(__file__))
    man={m["id"]:m for m in (json.loads(l) for l in open(os.path.join(HERE,"false-bench-manifest.jsonl")) if l.strip())}
    out=[json.loads(l) for l in open(os.path.join(HERE,"false-bench-output.jsonl")) if l.strip()]
    only = sys.argv[1] if len(sys.argv)>1 else None
    results=[]; ok=0; n=0
    for a in out:
        pid=a["id"]
        if only and pid!=only: continue
        p=man[pid]; src=build(p["equation1"], p["equation2"], a["code"])
        r=V.compile_check(src)
        v=bool(getattr(r,"verified",False)); n+=1; ok+=v
        errs=getattr(r,"errors",None) or []
        results.append({"id":pid,"pair":p["name"],"verified":v,"err":(errs[0][:100] if errs else "")})
        print(f'{pid} {p["name"]:24} verified={v} {"" if v else (errs[0][:90] if errs else "")}',flush=True)
    print(f"\nAXLE (Lean 4.32.2) verified: {ok}/{n}")
    if not only:
        open(os.path.join(HERE,"gate1-axle-false-results.json"),"w").write(json.dumps(results,indent=1))
