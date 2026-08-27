# Upload — one command per solver (needs your SAIR_API_KEY + credits)

Three staged `solver.py` files, disclosure prepended, py_compile-verified,
all under 500 KB (`STAGED.sha256` has the exact hashes).

## Option A — API (playground run, from this Claude session)

Type these in the session prompt (the `!` runs it here; key never stored):

```
! export SAIR_API_KEY=<your key>
! cd ~/Projects/sair-eq2-harvest && SOLVER_PATH=~/Desktop/SAIR-RIEMANN-LABS-PACKAGE/UPLOAD-2026-08-27/EULER/solver.py RUN_LABEL=EULER-2026-08-27 python3 sair_submit_run.py
! cd ~/Projects/sair-eq2-harvest && SOLVER_PATH=~/Desktop/SAIR-RIEMANN-LABS-PACKAGE/UPLOAD-2026-08-27/WILL/solver.py RUN_LABEL=WILL-2026-08-27 python3 sair_submit_run.py
! cd ~/Projects/sair-eq2-harvest && SOLVER_PATH=~/Desktop/SAIR-RIEMANN-LABS-PACKAGE/UPLOAD-2026-08-27/EQT02-AUTOLAB/solver.py RUN_LABEL=EQT02-2026-08-27 python3 sair_submit_run.py
```

(Or paste just the key with `! export SAIR_API_KEY=...` and tell me "submit" —
I'll run the three submissions and watch the results.)

## Option B — Web (competition submission form)

playground.sair.foundation → competition → upload each staged `solver.py`
(they already carry the disclosure inside). Both tracks per entry — Solo +
Marathon are the same file.

Up to 5 solvers per phase; we ship 3. Deadline 2026-08-31 AoE.
