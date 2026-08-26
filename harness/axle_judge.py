#!/usr/bin/env python3
"""Fast SAIR-judge replica via Axle (cloud Lean 4.32.2 = the judge's version).

Builds a self-contained Lean file equivalent to the judge's Goal for a TRUE
implication (Magma class + ◇ notation + the two equations as hypothesis→goal),
splices in a candidate proof body, and asks Axle to compile it. verified=True
iff the proof actually closes — a seconds-fast stand-in for the 40-min playground.
"""
import os, re, sys, pathlib
sys.path.insert(0, os.environ.get("BROCKIAN_MATH",
                                  str(pathlib.Path.home() / "Projects/brockian-mathematics")))
from engine import verify as ev  # noqa: E402

def parse_vars(text):
    seen = []
    for v in re.findall(r"\b([a-z])\b", text):
        if v not in seen:
            seen.append(v)
    return seen

# Faithful replica of the judge: bare JudgeMagma.Magma (NO Mathlib), named
# @[reducible] EquationLHS/RHS with per-variable binders, abbrev Goal.
_PREAMBLE = ("class Magma (α : Type _) where op : α → α → α\n"
             '@[inherit_doc] infix:65 " ◇ " => Magma.op\n')

def make_true_lean(eq1, eq2, body):
    v1 = " ".join(f"({v} : G)" for v in parse_vars(eq1))
    v2 = " ".join(f"({v} : G)" for v in parse_vars(eq2))
    body = body.rstrip("\n")
    ind = "\n".join(("  " + ln if ln.strip() else ln) for ln in body.splitlines())
    return (_PREAMBLE +
            f"@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ {v1}, {eq1}\n"
            f"@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ {v2}, {eq2}\n"
            "abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G\n"
            f"def submission : Goal := by\n{ind}\n")

def axle_true(eq1, eq2, body):
    code = make_true_lean(eq1, eq2, body)
    r = ev.compile_check(code)
    return r.verified, (r.errors or [])

if __name__ == "__main__":
    export = os.environ.get("AXLE_API_KEY")
    tests = [
        ("identical (valid)", "x = x ◇ y", "x = x ◇ y", "intro G _ h\nexact h"),
        ("not-implied (invalid)", "x = x ◇ y", "x = y ◇ x", "intro G _ h\nexact h"),
    ]
    for name, e1, e2, body in tests:
        v, errs = axle_true(e1, e2, body)
        print(f"{name}: verified={v}  {(errs or [''])[0][:90]}")
