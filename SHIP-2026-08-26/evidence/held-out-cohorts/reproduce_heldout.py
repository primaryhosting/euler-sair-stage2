#!/usr/bin/env python3
"""Reproducible held-out FALSE cohorts for EULER.

Addresses the audit finding that the 120/120 and 100/100 held-out numbers were
prose-only. This program regenerates both cohorts DETERMINISTICALLY (fixed
seeds), excludes every released-set pair by construction, runs the frozen
solver's FALSE engine, exhaustively self-checks every emitted witness, and
writes immutable manifests + logs. Re-running it reproduces the same cohorts and
the same result.

What this DOES establish: the cohorts are held-out from every released set by
construction (selection excludes all released pairs / all released hypotheses),
the selection is seeded and inspectable, and every counted witness is a sound
finite countermodel (E1 holds for all assignments, E2 fails for some).
What it does NOT establish: private-set accuracy (unmeasurable before the run),
or that these particular pairs mirror the private distribution.

Usage:  python3 reproduce_heldout.py
Inputs: the frozen solver (auto-located: ../../solvers/EULER.py in the ship packet,
        else ../EULER-SUBMISSION-2026-08-25.py in the dev tree) and the bundled
        released_index.json (the exclusion set — 800 released pairs / 497 released
        hypotheses). The four released eval jsonl files are only a fallback used to
        rebuild the index if it is absent; the packet ships the index so this run
        is self-contained.
Output: cohort_heldout_false.json, cohort_novel_hypothesis.json, RESULTS.md
        written next to this file.
"""
import json, os, random, importlib.util, hashlib

HERE = os.path.dirname(os.path.abspath(__file__))

# Locate the frozen solver: ship packet first, then the dev tree.
_SOLVER_CANDIDATES = [
    os.path.join(HERE, "..", "..", "solvers", "EULER.py"),
    os.path.join(HERE, "..", "EULER-SUBMISSION-2026-08-25.py"),
]
SOLVER = next((p for p in _SOLVER_CANDIDATES if os.path.exists(p)), None)
if SOLVER is None:
    raise SystemExit("EULER solver not found; looked for:\n  " +
                     "\n  ".join(_SOLVER_CANDIDATES))

spec = importlib.util.spec_from_file_location("euler", SOLVER)
E = importlib.util.module_from_spec(spec); spec.loader.exec_module(E)
EQS = E._eq_list()

# Exclusion set = everything released. Load the bundled, hashed index so the
# reproduction is self-contained; only if it is missing do we rebuild from the
# raw eval files. If NEITHER is available we abort — we never silently run with
# an empty exclusion set (which would forfeit the held-out-by-construction claim).
INDEX = os.path.join(HERE, "released_index.json")
EVALS = ["/tmp/evaluation_normal.jsonl", "/tmp/evaluation_hard.jsonl",
         "/tmp/evaluation_extra_hard.jsonl", "/tmp/evaluation_order5.jsonl"]
released_pairs, released_hyps = set(), set()
if os.path.exists(INDEX):
    idx = json.load(open(INDEX))
    released_pairs = {tuple(p) for p in idx["released_pairs"]}
    released_hyps = set(idx["released_hyps"])
    _h = hashlib.sha256(open(INDEX, "rb").read()).hexdigest()
    print(f"exclusion index: {len(released_pairs)} pairs / {len(released_hyps)} "
          f"hyps  (released_index.json sha256 {_h[:16]}…)")
else:
    present = [f for f in EVALS if os.path.exists(f)]
    if not present:
        raise SystemExit(
            "No exclusion source: bundled released_index.json is missing and none "
            "of the raw eval files are present. Refusing to run — an empty "
            "exclusion set would silently void the held-out-by-construction claim.")
    for f in present:
        for line in open(f):
            if not line.strip():
                continue
            r = json.loads(line)
            released_pairs.add((r["eq1_id"], r["eq2_id"]))
            released_hyps.add(r["eq1_id"])
    print(f"exclusion index rebuilt from {len(present)}/4 raw eval files: "
          f"{len(released_pairs)} pairs / {len(released_hyps)} hyps")

def selfcheck(eq1, eq2, n, table):
    vs1, l1, r1 = E.compile_equation(eq1); vs2, l2, r2 = E.compile_equation(eq2)
    op = lambda a, b, t=table: t[a][b]
    return E.check_equation(vs1, l1, r1, n, op) and not E.check_equation(vs2, l2, r2, n, op)

def run_cohort(seed, target, novel_hyp):
    """Deterministic sample of oracle-FALSE order-4 pairs held out from released
    sets. novel_hyp=True additionally requires the hypothesis id to be unseen."""
    rng = random.Random(seed)
    cohort, tries = [], 0
    while len(cohort) < target and tries < 500000:
        tries += 1
        a, b = rng.randint(1, 4694), rng.randint(1, 4694)
        if a == b or (a, b) in released_pairs:
            continue
        if novel_hyp and a in released_hyps:
            continue
        if E.oracle(a, b) == "false":
            cohort.append((a, b))
    results, solved, invalid = [], 0, 0
    for a, b in cohort:
        eq1, eq2 = E.normalise(EQS[a-1]), E.normalise(EQS[b-1])
        n, table = E.find_counterexample(eq1, eq2, a, deadline=None)
        ok = bool(n is not None and selfcheck(eq1, eq2, n, table))
        if ok: solved += 1
        elif n is not None: invalid += 1
        results.append({"eq1_id": a, "eq2_id": b, "solved": ok,
                        "order": (n if n else None)})
    return {"seed": seed, "target": target, "novel_hypothesis": novel_hyp,
            "excluded_released_pairs": len(released_pairs),
            "excluded_released_hyps": len(released_hyps) if novel_hyp else None,
            "size": len(cohort), "solved": solved, "invalid_witnesses": invalid,
            "results": results}

heldout = run_cohort(12345, 120, novel_hyp=False)
novel = run_cohort(999, 100, novel_hyp=True)
json.dump(heldout, open(os.path.join(HERE, "cohort_heldout_false.json"), "w"), indent=1)
json.dump(novel, open(os.path.join(HERE, "cohort_novel_hypothesis.json"), "w"), indent=1)

md = f"""# Held-out FALSE cohorts — reproducible result log

Regenerate: `python3 reproduce_heldout.py` (deterministic; same seeds → same
cohorts → same result). Solver: `{os.path.relpath(SOLVER, HERE)}`. Exclusion set:
bundled `released_index.json` (800 released pairs / 497 released hypotheses).

## Cohort A — held-out order-4 FALSE (seed 12345)
Selection: random order-4 pairs the embedded oracle calls FALSE, **excluding
every released-set pair** ({heldout['excluded_released_pairs']} excluded).
Size {heldout['size']}. **Solved {heldout['solved']}/{heldout['size']}**,
invalid witnesses {heldout['invalid_witnesses']}. IDs in
`cohort_heldout_false.json`.

## Cohort B — novel-hypothesis order-4 FALSE (seed 999)
Selection: as above, additionally requiring the hypothesis id to appear in NO
released set ({novel['excluded_released_hyps']} released hypotheses excluded).
Size {novel['size']}. **Solved {novel['solved']}/{novel['size']}**,
invalid witnesses {novel['invalid_witnesses']}. IDs in
`cohort_novel_hypothesis.json`.

## What this establishes, and what it does not
Establishes: both cohorts are held out from every released set by construction;
selection is seeded and inspectable; every counted witness is a sound finite
countermodel (E1 holds for all assignments, E2 fails for some — re-checked here
and again by the judge's `decideFin!` if submitted). Does NOT establish
private-set accuracy, nor that these pairs mirror the private distribution.
Badge: COMPUTATIONALLY VERIFIED (witness soundness + held-out-by-construction),
not an official-judge or private-set result.
"""
open(os.path.join(HERE, "RESULTS.md"), "w").write(md)
print(f"Cohort A held-out: {heldout['solved']}/{heldout['size']} "
      f"(invalid {heldout['invalid_witnesses']})")
print(f"Cohort B novel-hyp: {novel['solved']}/{novel['size']} "
      f"(invalid {novel['invalid_witnesses']})")
print("Wrote cohort manifests + RESULTS.md")
