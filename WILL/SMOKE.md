# WILL v6 — Protocol Smoke Test

- **Candidate:** `WILL/WILL-v6-CANDIDATE.py` (89,936 bytes)
- **Harness:** `/private/tmp/claude-501/-Users-acutis/d1c9179b-b093-42ef-ad47-bd787f4d07ac/scratchpad/will_smoke.py` (fake Solo judge over subprocess pipes + Marathon env run)
- **Date:** 2026-08-25 · Python 3 (host) · **Result: 28/28 PASS**
- Built-in selftest (`--selftest`): `WILL v6 SELFTEST PASS` (all four sections, 0.11s)

## Scenario A — Solo, trivially-TRUE, judge accepts
Startup: `{"equation1":"x = x ◇ y","equation2":"x = x ◇ y"}`, budget 60s.

| Check | Result |
|---|---|
| A1 First message is a `{"call":"judge",...}` | PASS |
| A2 Verdict `true` | PASS |
| A3 TRUE cert shape (`import JudgeProblem` / `def submission : Goal := by` / `intro G _ h` / indented `exact h`) | PASS |
| A4 No banned tokens, no bare `*` in Lean | PASS |
| A5 Clean exit (rc 0) after `accepted` | PASS |
| A6 stdout contained valid JSON lines only | PASS |
| A7 No messages emitted after acceptance | PASS |

## Scenario B — Solo, easy FALSE with `'*'` operator, scripted reject→accept
Startup: H = `x * y = y * x`, Goal = `x * y = x` (sent with `*`, the boundary-normalization trap). Policy: reject judge call #1, answer LLM calls with a valid `verdict:false` table, accept the next verified submission.

| Check | Result |
|---|---|
| B1 First judge call verdict `false` | PASS |
| B2 FALSE cert independently re-verified by harness (table satisfies H exhaustively, violates Goal) | PASS |
| B3 `'*'` normalized — no `*` op leaked into emitted Lean (`◇`/finOpTable only) | PASS |
| B4 Resubmission after rejection also carried a verified cert | PASS |
| B6 Solver retried after rejection (2 judge calls) | PASS |
| B7 Acceptance reached (judge=2, llm=1, sub-second wall) | PASS |
| B8/B9 Clean exit; stdout valid JSON only | PASS |

Observed flow matches design: FALSE probe → rejection feedback into `SOLVER.feedback` → deterministic tiers → LLM round whose table was mechanically re-checked before resubmission.

## Scenario C — Solo, infra-error failfast
Same FALSE problem, budget **3600s**. Judge reply to call #1: `{"status":"error","judge_code":"JUDGE_INFRASTRUCTURE_ERROR","detail":"Magma.olean incompatible header"}`.

| Check | Result |
|---|---|
| C1 Judge call received | PASS |
| C2 Zero further judge/LLM calls after infra error | PASS |
| C3 Process exited ~0.00s after infra reply (vs 3600s budget) — failfast works | PASS |
| C4 Exit code 0 | PASS |
| C5 stdout valid JSON only | PASS |

This is the fix for the EULER-era defect (retrying infra errors into LLM fallback for ≤1557s/problem): `_judge_result_is_infra` trips `_JUDGE_INFRA_DOWN` and every tier bails immediately.

## Scenario D — Marathon branch (no judge at runtime)
3-line manifest: `m1` trivially-TRUE (`x = x ◇ y` ⊢ `a = a ◇ b`), `m2` easy FALSE (comm ⊢ left-proj, `*` operator), `m3` **malformed** equation (`x ◇ (y ◇`). Env: `JUDGE_MARATHON_MANIFEST/OUTPUT`, 20s per problem. stdin closed.

| Check | Result |
|---|---|
| D1 Exit 0, no crash (malformed line handled) | PASS |
| D2 Nothing printed to stdout | PASS |
| D3 Output contains exactly `m1`+`m2` — malformed `m3` skipped, **no unverified write** | PASS |
| D4 `m1`: verdict true, self-verified `exact h` cert, banned-token free | PASS |
| D5 `m2`: verdict false, table independently re-verified by harness | PASS |
| D6 Every output line valid JSON with `id`/`verdict`/`code` | PASS |

## Static checks
| Check | Result |
|---|---|
| S1 File size 89,936 ≤ 500,000 bytes | PASS |
| S2 Imports are stdlib-only (`sys os re json time random itertools tempfile`-class; no sympy/numpy) | PASS |

## Verdict
All checks pass: no crashes, stdout is protocol-JSON only, Solo judge loop (accept / reject-retry / infra-failfast) behaves, Marathon writes only self-verified answers and survives malformed manifest rows, `'*'`→`'◇'` normalization holds at every boundary including LLM-suggested content. Candidate is protocol-clean for Stage-2 Solo and Marathon.

Not covered here (by design of a protocol smoke): real Lean judging, prover strength on hard problems, 2-vCPU/2GB sandbox timing.
