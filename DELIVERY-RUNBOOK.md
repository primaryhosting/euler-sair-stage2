# SAIR Stage 2 — Delivery Runbook
*Christopher Brock · Riemann Labs · finalized 2026-08-27 · deadline 2026-08-31 23:59 AoE*

This is the single source of truth for **uploading**. Everything below is
verified against the frozen packet as of 2026-08-27. The covers to paste live in
`SUBMISSION-COVERS.md` (identical text in `SHIP-2026-08-26/SUBMISSION-NOTES.md`).

---

## What ships (and what doesn't yet)

| # | Entry | File to upload (rename to `solver.py`) | Size | SHA-256 | State |
|---|-------|-----------------------------------------|------|---------|-------|
| 1 | **EULER** | `solvers/EULER.py` (in ship zip) = `EULER-SUBMISSION-2026-08-25.py` | 442,061 B | `e0f7ac84…c9b48329` | **READY** |
| 2 | **WILL** | `solvers/WILL.py` (in ship zip) = `WILL-SUBMISSION-2026-08-25.py` | 91,230 B | `90aa400c…a639468` | **READY** |
| 3 | AutoLab solver (EQT02-S00021) | — not a single file yet — | ~48.8 KB + harness | — | **BLOCKED on packaging** (`6f80ea8e`) |

Up to **5 solvers per phase** (Solo and Marathon), submissions **private until
results** — so there is no penalty for submitting entries 1–2 now and adding a
3rd later if it packages clean before the deadline.

---

## Step-by-step upload (per entry, for BOTH Solo and Marathon)

1. **Recompute the SHA immediately before upload** and match the table above:
   ```bash
   cd ~/Desktop/SAIR-RIEMANN-LABS-PACKAGE
   shasum -a 256 EULER-SUBMISSION-2026-08-25.py   # expect e0f7ac84…
   shasum -a 256 WILL-SUBMISSION-2026-08-25.py    # expect 90aa400c…
   ```
2. **Rename to `solver.py`** for upload (judge requires that exact name). Keep a
   copy; don't rename the canonical file in place.
3. **Place the disclosure.** If the submission form has a notes/description
   field, paste that entry's cover text from `SUBMISSION-COVERS.md`
   (Description + Embedded-data disclosure + Honest scope + Acknowledgments).
   **If there is no notes field, prepend the disclosure block as a `#` comment
   at the top of `solver.py` before upload** — the single-file rule means the
   disclosure must travel inside the file.
4. **Upload the same file for both tracks** — Solo and Marathon (the file
   `__main__`-branches on `JUDGE_MARATHON_MANIFEST`; one file serves both).
5. **If the judge returns `incompatible header` / an infrastructure error:** that
   is SAIR-side (documented 2026-08-20). The solver fail-fasts in seconds — report
   it to SAIR, do **not** treat it as a solver defect.

---

## Numbers you can stand behind (for the notes field / any questions)

- **EULER held-out generalization** (reproducible, judge-toolchain Axle-verified):
  FALSE 120/120 pairs + 100/100 unseen hypotheses; **held-out TRUE 50/50**
  (all from generalizing tiers, 0 embedded per-pair certs). Order-5 scored
  category: **190/200** by computation (FALSE 100/100, TRUE 90/100).
- **WILL mechanical bench** (no LLM, no oracle, 100 released): FALSE 50/50,
  TRUE 34/50; every FALSE cert emitted as **compiling Lean** in the judge's exact
  format — confirmed on Lean v4.32.2 (15/15 constructed + 6/6 released verified,
  2/2 broken rejected).
- **AutoLab solver canonical scorecard** (`388d313e`, if/when it becomes entry 3):
  **bigu_lean 1499/1500** decided with a compiling Lean certificate on
  `leanprover/lean4:v4.32.2` — TRUE 553, FALSE 946, **0 emit failures** (up to
  countermodel order 13); sibling runs pinned `bad_certificates = 0` and
  runner-parity on the official toolchain.
- **No result carries an OFFICIAL-judge badge until a green run on
  playground.sair.foundation returns.** State every number as held-out /
  computational until then. This is the reactivation standard.

---

## The one external gate

**SAIR credits for `playground.sair.foundation`.** The upload is a web action
that only Chris can perform, and it needs credits on the account. Nothing in the
packet is blocked on our side — the moment credits are live, entries 1–2 can go
up in minutes using the steps above.

---

## Recommended order of operations

1. **Now / when credits land:** upload **EULER** and **WILL**, each to **Solo +
   Marathon** (4 uploads total). This is the delivery — done.
2. **In parallel:** let `6f80ea8e` package the AutoLab solver into a real
   single-file `solver.py` (0 harness imports, ≤500 KB, every answer accepted by
   the official `pipeline/runner.py`). If it passes **before 08-31**, add it as
   **entry 3** with its own disclosure note (oracle-free, deterministic,
   1499/1500 canonical). If it doesn't package clean in time, ship the two
   flagships and enter the AutoLab solver in a later phase — it is a bonus, never
   a blocker.
3. **After a green official run:** upgrade the badges from held-out/computational
   to OFFICIAL on the deck (`prime-rigor-explorer.lovable.app/euler`) and in the
   memory note.

---

## Pre-flight checklist (final)

- [x] EULER 442,061 B · `e0f7ac84…` · py_compile clean (2026-08-27)
- [x] WILL 91,230 B · `90aa400c…` · py_compile clean (2026-08-27)
- [x] ship zip `solvers/EULER.py` + `solvers/WILL.py` byte-identical to canonical
- [x] covers + notes consistent with these SHAs
- [ ] recompute both SHAs at the console immediately before upload
- [ ] disclosure placed (notes field, or prepended as a `#` comment)
- [ ] each file uploaded to **both** Solo and Marathon
- [ ] SAIR credits confirmed live on the account
