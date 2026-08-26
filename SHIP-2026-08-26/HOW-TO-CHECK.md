# How to check it

*Every load-bearing claim in this packet is auditable. Here is how, command by
command. Nothing below needs network or the organizers' credits, except the final
official run.*

## 0. Verify the archive and file hashes
```bash
shasum -a 256 -c CHECKSUMS.sha256          # every file in the packet
```
The two solver hashes are also printed in `SUBMISSION-NOTES.md`:
- `solvers/EULER.py` → `e0f7ac84…48329` (442,061 B)
- `solvers/WILL.py`  → `90aa400c…39468` (91,230 B)

## 1. Both solvers self-test (Solo + Marathon core)
```bash
python3 solvers/WILL.py --selftest        # → WILL v6 SELFTEST PASS
# EULER Marathon smoke:
printf '%s\n' \
 '{"id":"a","equation1":"x * y = y * x","equation2":"x * y = x"}' \
 '{"id":"b","equation1":"x = x * (x * y)","equation2":"x * y = x * (y * y)"}' > /tmp/m.jsonl
JUDGE_MARATHON_MANIFEST=/tmp/m.jsonl JUDGE_MARATHON_OUTPUT=/tmp/o.jsonl \
 JUDGE_MARATHON_PER_PROBLEM=15 python3 solvers/EULER.py
cat /tmp/o.jsonl   # a→false, b→true
```

## 2. Held-out cohorts reproduce (and are genuinely self-contained)
```bash
cd evidence/held-out-cohorts
python3 reproduce_heldout.py               # → 120/120 and 100/100, 0 invalid
```
It loads the **bundled** `released_index.json` (800 released pairs / 497
hypotheses) and prints its sha256. To prove it does not secretly need the raw
released files, run it with them absent — it still reproduces (that is the
clean-environment test). The exclusion set's provenance and raw-file hashes are in
`PROVENANCE.md`; rebuild the index with `python3 build_released_index.py`.

## 3. WILL's technique-only bench (fixed solver)
```bash
cd evidence/will-bench
cat released-bench-result.md   # FALSE 50/50, TRUE 34/50, 0 disagreements
cat false-bench-result.md      # 15/15 constructed FALSE, full preamble + model re-checked
```
`make_false_bench.py` / `make_released_bench.py` regenerate these; every emitted
certificate is in `certs/` (constructed) and inline in `released-bench-output.jsonl`.

## 4. Compile the FALSE certificates under the real judge (Gate 1)
The FALSE certs are shape-verified and finite-model-verified in this packet. To
compile them under the actual kernel, use the local judge (Lean v4.32.2, the
judge's exact commit):
```bash
python3 evidence/will-bench/gate1_judge_false.py    # asserts status=="accepted"
```
Status and prerequisites (a memory-headroom note) are in
`evidence/will-bench/GATE1-JUDGE-STATUS.md`.

## 5. What no local check can establish
Private-set accuracy, and the **official** badge. Those require an organizer judge
run. Until one returns, read every figure as computationally- or
toolchain-verified, never official.
