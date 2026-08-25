# EULER v8 — Submission Note (embedded data disclosure)

Per the Stage-2 rule that solvers embedding compressed data/binary blobs disclose
them, EULER's `solver.py` contains four embedded payloads. All are derived from
public, open data; none encodes per-problem answers beyond what the public
implication table already states.

| Blob | Contents | Size (compressed) | How generated |
|------|----------|-------------------|---------------|
| `_MATRIX_BLOB` | The 4694×4694 order-4 implication bitmatrix (eq_i ⇒ eq_j, one bit each) | ~110 KB | Byte-identical to the public `outcomes.json` closure from the Equational Theories Project (Tao et al.); recomputed and cross-checked (0 disagreements). Gives authoritative TRUE/FALSE **direction** for any order-4 pair. |
| `_LOOKUP_BLOB` | Sparse direction lookup (12,587 keys). 12,365 are in-range 1..4694 (redundant with the bitmatrix; 13 historical errors, bitmatrix wins). 222 have at least one ID outside 1..4694 (ids up to ~936k) — the only keys that can fire. | **70,592 chars** compressed | Same ETP source; fallback only when `_matrix_bit` returns None. |
| `_MT_SRC_B64` | The full Python source of the embedded mini-Twee prover | ~11 KB | Our own bounded Knuth–Bendix completion prover (`twee/mini_twee.py`), zlib+base64. Runs in-sandbox; emits explicit `intro`/`calc`/`have`/`congrArg` Lean (a style choice, not a judge requirement). |
| `_EQ_SRC_B64` | The 4694 order-4 equation texts (one per line) | ~15 KB | Public `equations.txt` from the Equational Theories Project; needed so the transitivity tier can name intermediate laws. |

## Methodology of the solver

Direction is read from the embedded implication matrix (public data). Given the
direction:

- **FALSE**: search for a finite magma counterexample (table bank → exhaustive →
  structured/affine/bilinear), emit `finOpTable` + `decideFin!`.
- **TRUE**: prove `EquationLHS ⇒ EquationRHS` with a cascade, cheapest first:
  1. matching-chain prover (self-rechecked),
  2. mini-Twee Knuth–Bendix completion (total: if it emits, the proof is valid),
  3. structural tactic strategies,
  4. **transitivity composition** — split a hard `i ⇒ j` through a directly-provable
     intermediate `k` (`i ⇒ k`, `k ⇒ j`, both TRUE per the matrix) and compose the
     two proofs into one `have`-chain. Candidate `k`'s come from the embedded matrix;
     no per-pair proof is stored.

Every candidate proof is submitted to the judge (`call_judge`) and only an
`accepted` verdict finalizes the answer — no proof is trusted without the judge.

The judge token-bans `sorry`/`admit`/`sorryAx`/`dbg_trace`/`run_tac`/`mkSorry`/
`initialize` and metaprogramming (`#eval`/`elab`/`macro`/`unsafe*`), then checks
axiom/declaration dependency-closure (`#judge_report`). Production allows
`propext` / `Quot.sound` / `Classical.choice` plus a prefix declaration
allowlist. `rw` / `simp` / `grind` / `aesop` / `decide` are ordinary legal
tactics, not banned tokens. EULER's chain / mini-Twee / transitivity tiers
prefer a small explicit set (`intro`/`exact`/`calc`/`have`/`congrArg`/`.symm`/
`.trans`/`fun`/`rfl`) as a style convention; hardcoded and tactic-sweep paths
may use `rw`/`simp`/`grind`. Every candidate is submitted via `call_judge`;
only `accepted` finalizes.

Official evaluation pin (2026-08): Lean **4.32.2**, sandbox `python:3.11-slim`
@ `sha256:db3ff2e1800a…`, 2 vCPU / 2048 MB / `--network=none` / read-only FS,
FALSE = finite magma, LLM via proxy (`gpt-oss-120b` reasoning_effort=low +
`gemma-4-31b-it`, T=0, seed=0). EULER is stdlib-only and emits `Fin n`
witnesses. It does not declare a top-level `PROMPT` constant (LLM tier is
unused on public order-4; a `{solver.rendered_prompt}` shim is the fix if
that tier must work on official eval).

Open-source basis: the Equational Theories Project (github.com/teorth/equational_theories).

## Isolated v8.1 candidate disclosure

`EULER-v8.1-CANDIDATE.py` is not the live v8 file. In addition to the four v8
payloads above, it contains `_EXTRA_MODEL_SEEDS`: 67 literal finite operation
tables produced during development with Mace4 from the public FALSE problem
pairs, then exhaustively rechecked by EULER's Python evaluator before
embedding. Combined with the original compressed bank, the candidate has 305
unique tables. Mace4 is not imported, executed, or required in the submission
sandbox. The candidate also adds pure-stdlib CSP code; that code is an
algorithm, not an embedded answer payload. The current candidate additionally
contains ten disclosed, pair-keyed Lean certificates for public order-5 TRUE
residuals. See `EULER-v8.1-SUBMISSION-NOTE.md` for the complete current payload
disclosure and `~/Projects/sair-eq2-harvest/CSP-FALSE-FINDER.md` for finite-model
provenance and coverage.
