# WILL v6 — Mechanical-Tier Bench (NO LLM, NO oracle)

Date: 2026-08-25
Solver: `WILL-v6-CANDIDATE.py` (89,936 bytes), imported as a module — deterministic
tiers only: runtime counterexample search, chain rewriting prover, Knuth–Bendix
completion/collapse prover. No judge, no LLM, no precomputed data (per WILL's rule:
sediment = data, technique = code).

## Sample (deterministic selection)

From the released evaluation sets (`/tmp/evaluation_normal.jsonl`,
`/tmp/evaluation_order5.jsonl`), first N of each answer class in file order:

| Set | TRUE rows | FALSE rows | Total |
|---|---|---|---|
| normal | 30 | 30 | 60 |
| order5 | 20 | 20 | 40 |

Deadlines: FALSE search 30 s/problem; TRUE 30 s chain then 30 s collapse.
Raw per-row records: `/tmp/will_bench_results.jsonl`.

## FALSE tier — `find_counterexample`

| Set | Found | Valid (independent re-check) |
|---|---|---|
| normal | **30/30** | 30/30 |
| order5 | **20/20** | 20/20 |
| **Total** | **50/50 (100%)** | **50/50 (100%)** |

- Every found table was re-checked by an *independent* evaluator written in the
  bench harness (own parser + exhaustive finite evaluation of both laws over all
  assignments), not the solver's own gate. Zero invalid tables.
- Witness order distribution: n=2 ×33, n=3 ×8, n=4 ×7, n=5 ×2.
- Speed: total 0.7 s for all 50 rows (median per-row 0.0 s, max 0.1 s). The 30 s
  deadline was never approached.

## TRUE tier — chain prover, then completion/collapse

| Set | Emitted | via chain | via collapse | Unsolved |
|---|---|---|---|---|
| normal | **16/30 (53%)** | 10 | 6 | 14 |
| order5 | **17/20 (85%)** | 2 | 15 | 3 |
| **Total** | **33/50 (66%)** | 12 | 21 | 17 |

- Speed: chain median 0.0 s / max 0.45 s; collapse median 0.0 s / max 0.01 s.
  Every emission was near-instant; the 17 misses each burned the full 60 s
  (30 s chain + 30 s collapse) without finding a proof — the deterministic tiers
  fail fast-or-never on this sample.
- Unsolved TRUE ids: normal 0008, 0012, 0014, 0018, 0022, 0024, 0030, 0036,
  0038, 0040, 0044, 0046, 0048, 0058; order5 0010, 0028, 0040.
- Note the inversion: order5 TRUEs are *easier* for collapse (15/20) — deeper
  laws more often force constancy/collapse — while mid-difficulty normal TRUEs
  are where technique-alone runs out.

## Spot verification of emitted Lean bodies (Axle judge-replica, Lean 4.32.2)

Bodies wrapped as `intro G _ h` + emitted body, compiled against a faithful
replica of the judge's Goal via `~/Projects/sair-eq2-harvest/axle_judge.py`:

| Sample | Verified |
|---|---|
| 10 planned spot checks (5 chain + 5 collapse, normal set) | **10/10** |
| +4 extra order5 checks (2 chain + 2 collapse) | **4/4** |
| **Total attempted** | **14/14 (100%)** |

Records: `/tmp/will_axle_spot.jsonl`, `/tmp/will_axle_spot_o5.jsonl`.
The remaining 19 emitted bodies were self-verified by the solver's internal
chain re-walk / rewrite replay but NOT independently compiled — reported
honestly as spot-checked, not exhaustively certified.

## Combined mechanical-tier score (this sample)

- **83/100 answered** (50 FALSE + 33 TRUE), 0 wrong emissions detected,
  100% of independent checks passed (50/50 tables, 14/14 Lean bodies).
- Projected balanced accuracy if only self-verified answers are written
  (Marathon discipline): 100% precision on the 83, abstain on 17.

## Caveat — the LLM tier is untestable offline

WILL v6's LLM rounds (gpt-oss-120b / gemma-4-31b-it via the competition proxy,
rendered from the top-level `PROMPT` constant) exist only inside the SAIR
sandbox. Nothing here measures them. The 17 unsolved TRUE rows are precisely
the population the LLM tier (and Solo judge feedback loop) is designed to
attack; this bench establishes the *floor* — technique alone, walking in
without the library — not the ceiling.
