# EULER Φ — Methodology

SAIR Stage 2 (Equational Theories), Solo track. This document describes the
solver's architecture, its correctness guarantee, the validation evidence, and
its honest limits. It is written to match the research candidate
`EULER-v8.1-CANDIDATE.py`; the promoted live mirror remains the prior
baseline until a fresh official judge run succeeds.

Official scoring pin (playground page *Official Evaluation Spec*, recorded
2026-08): see **§0**. Where this document and the cloned repo's
`pipeline/config.json` disagree, the official spec wins.

---

## 0. Official evaluation spec (pin) vs EULER v8

Host is a GCE `c2d-highmem-16` (16 vCPU / 128 GB). Contestant code never
sees it. Scoring uses the **sandbox**, not the host.

| Pin | Official spec | EULER v8 |
|-----|---------------|----------|
| Image | `python:3.11-slim` digest `sha256:db3ff2e1800a…` (amd64, recorded 2026-08-06) | stdlib-only; no third-party imports. Spec: do **not** assume sympy/numpy. |
| Sandbox | 2 vCPU, **2048 MB**, 64 PIDs, `/tmp` 64 MB tmpfs, **read-only FS**, `--network=none`, all caps dropped | Solo: stdin/stdout only. mini-Twee `exec`s the decoded blob **in memory** (no disk). No subprocesses. Fits. |
| Env | `PATH`, `HOME`, `LANG`, `PYTHONDONTWRITEBYTECODE` | no extra env needed |
| Lean | **v4.32.2** (`f3b06c705e6c85f5314019d5d3baab0fec5b580c`), Mathlib `905b95818eb32af7874a58b427f50c1711a5e96c` | Axle validation is Lean **4.32.2**. The cloned repo's `lean-toolchain` still says `v4.30.0-rc2` — ignore it for scoring. |
| Size | `solver.py` ≤ 500,000 bytes | promoted v8.1 mirror: 402,238 B; isolated candidate: 437,402 B |
| Solo budget | 3600 s wall-clock / problem (excludes organizer LLM latency) | `solve(..., 3600)` |
| Judge | 300 s / call; code 100,000 B; false cert **20,000 B** | `lean_false` tables are tens of bytes |
| LLM | proxy-only; models `openai/gpt-oss-120b` (`reasoning_effort = **low**`) and `google/gemma-4-31b-it` (reasoning off); T=0, seed=0; 65,536 out tokens; DeepInfra via OpenRouter; no fallback | solver **cannot** pick the model or `reasoning_effort`. Cloned `config.json` still says `medium` — official pin is **low**. |
| Prompt | "in-file top-level constant"; proxy AST-extracts `PROMPT = "..."` | candidate has `PROMPT = "{solver.rendered_prompt}"`; the proxy fills the dynamic prompt from solver context. |
| FALSE | `∃ (G : Type) (_ : Magma G), H G ∧ ¬ GoalLaw G`; no `Finite`/`Fintype` constraint in the released judge | finite tables use `decideFin!`; the candidate also has a proof-producing `Bool × Nat` compiler and a judge-gated structured/complete Lean artifact path. |
| Protocol | `{"call":"judge","verdict":"true"|"false","code":...}` | matches. Accepted-judge finalizes in `pipeline/proxy.py`. |

Proof policy in the official spec matches the cloned judge: trusted axioms
`propext` / `Quot.sound` / `Classical.choice`; `incomplete_proof` for holes,
metaprogramming, unsafe, debug/IO. Not a tactic ban.

"If the (local) harness turns green for your `solver.py`, the judge returns
the same verdict in production." That is the official identity. It does
**not** make Axle = production, and it does **not** make a broken playground
olean the official host. Playground of v8-as-is remains step 0.

---

## 1. Problem

A **magma** is a set with a single binary operation `◇` (no axioms). An
*equational law* is a universally-quantified identity in `◇` (e.g.
`x ◇ y = y ◇ x`). For an ordered pair of laws `(E1, E2)` the task is to decide
the implication

> `E1 ⇒ E2` : does every magma satisfying `E1` also satisfy `E2`?

and produce a Lean artifact the judge accepts:

- **FALSE** — a magma witness satisfying `E1` and violating `E2`. The released
  judge defines this as `∃ (G : Type) (_ : Magma G), E1 G ∧ ¬ E2 G` and
  explicitly accepts finite or infinite carriers. Finite tables are discharged
  by `decideFin!`; infinite artifacts prove the universal hypothesis and a
  concrete goal failure directly in Lean.
- **TRUE** — a Lean proof of `EquationLHS G → EquationRHS G`.

**What the judge actually bans** (repo `README.md` Constraints +
`judge/verify.py` `BANNED_PROOF_TOKENS`): `sorry`, `admit`, `sorryAx`,
`dbg_trace`/`dbgTrace`, `run_tac`, `mkSorry`, `initialize`/`builtin_initialize`,
plus `#eval`/`elab`/`macro`/`unsafe*` and banned axioms/declarations via
`#judge_report` dependency-closure. Production policy (`pipeline/proxy.py`
`DEFAULT_PROOF_POLICY`) allows axioms `{propext, Quot.sound, Classical.choice}`
and a prefix allowlist (`Eq.`, `Fin.`, `Mathlib.`, `congrArg`, `Lean.`, …).

`rw`, `simp`, `grind`, `aesop`, `decide` are **not** token-banned. A proof that
compiles, uses no sorry/admit, and pulls no disallowed axiom/declaration is
accepted. (A fixture, `r5_grind_unsound`, shows `grind` can pull the three
standard axioms — those are *allowed* under the production policy, and rejected
only under an empty-axiom test policy.)

**EULER's preferred emit set** (a self-imposed convention for the
correct-by-construction tiers — chain, mini-Twee, transitivity — not a judge
rule): `intro`, `exact`, `calc`, `have`, `congrArg`, `.symm`, `.trans`, `fun`,
`rfl`. Hardcoded proofs, tactic-sweep, and the LLM tier may still emit `rw` /
`simp only [h]` / `grind`; those paths are judge-gated, not liabilities.

---

## 2. Architecture — certificate-first, oracle-directed, cheapest-first

`solve()` runs a tiered router. Each tier is attempted only when cheaper tiers
fail, and each tier is direction-aware.

```
Tier 0  Hardcoded certificates                                  (instant)
Tier 1  Oracle-directed deterministic engine                    (<500 ms intent)
          FALSE: table bank → exhaustive → structured → polynomial
          TRUE:  chain → mini-Twee → structural strategies → transitivity
Tier 2  BFS tree-rewrite engine                                 (~10 s)
Tier 3  Expensive direction-aware search                        (~60 s)
          FALSE: proof-supported infinite family → finite CSP
          TRUE:  invertibility sweep → tactic sweep
Tier 4  LLM with accumulated near-miss context                  (remaining)
Tier 5  Opposite-direction fallback
```

For inputs whose IDs correspond to the ETP order-4 catalog (1–4694), Tier 1 alone resolves essentially every
problem; Tiers 2–5 are safety nets for out-of-distribution / unknown-band inputs.

---

## 3. Direction — the embedded implication oracle

`oracle(eq1_id, eq2_id)` reads TRUE/FALSE **direction** from an embedded
4694×4694 bitmatrix (`_MATRIX_BLOB`, one bit per ordered pair). The matrix is
**byte-identical to the public Equational Theories Project closure**
(`outcomes.json`, Tao et al.); it was recomputed and cross-checked with **0
disagreements**.

- The **public Stage-2 repo sets** (`normal.jsonl` + `hard1/2/3` + `sample_200`)
  are **100% order-4**. On those, the oracle gives exact direction.
- HuggingFace `SAIRfoundation/equational-theories-selected-problems` also
  ships `evaluation_order5.jsonl` (**200 problems, 100 T / 100 F**, all IDs
  4863–41402, **oracle None on 200/200**). Measured 2026-08-24 on v8 with
  *known direction* (dataset `answer`), 12 s CE / 8+10 s chain+twee, no
  transitivity, no judge: **FALSE 100/100, TRUE 90/100, combined 190/200**.
  That is the historical v8 ceiling. The isolated candidate now reaches the
  released set's **200/200**: all 100 FALSE models self-check, and all 100 TRUE
  bodies compile on exact Lean 4.32.2 (84 quick completion, six deeper
  completion, ten disclosed ATP-replayed public residuals). The ten static
  proofs are public-pair regression coverage, not private-set evidence.
- For an out-of-range / unknown pair (`direction is None`), EULER probes: a
  ~12 s counterexample probe (found ⇒ FALSE), else a quick `find_proof` probe
  (found ⇒ TRUE), else `unknown` (try FALSE first, it's cheaper).

Direction only *selects the branch*; it is never emitted as a claim. The proof
or counterexample is what the judge checks.

---

## 4. FALSE side — finite counterexample search

`find_counterexample(E1, E2, id, deadline)` looks for the smallest magma table
that satisfies `E1` and refutes `E2`, cheapest source first:

1. **Table bank** — precomputed small witnessing tables.
2. **Exhaustive** small-order enumeration.
3. **Structured families** — affine, bilinear, product constructions,
   backtracking, randomized (Tier 3).

The winning table is emitted as a `finOpTable` and discharged by the judge's
`decideFin!`. Exhaustive search is **n = 2 only**; n = 3..8 is structured
families + random + a short backtrack.

**FALSE-side measurements (do not collapse them):**
- Early evaluation/normal slice: **11/12** FALSE (~92%).
- v8 `bench_full.py` 50-problem normal slice (Axle / finite-model): **26/26**.
- hard2: **18/21** FALSE; the three misses (964⇒4192, 646⇒2858, 1167⇒1763) have
  **no counterexample at n ≤ 3**.

The real remaining FALSE gap is finite models outside the parametric families.
An isolated **v8.1 candidate** now contains a pure-stdlib finite-domain CSP
(runtime orders 4–8) and a harvested bank with models through order 9. The bank
alone covers 848/850 original public FALSE pairs and 400/400 FALSE rows in the
four released Stage 1 evaluation subsets. It is intentionally not copied over
the promoted live mirror until official judge credits are available. Details and the two
remaining public pairs: `~/Projects/sair-eq2-harvest/CSP-FALSE-FINDER.md`.

### 4.4 Infinite-model FALSE tier

The public S00023 solver exposed a missing capability: some non-implications
may have no small finite witness, while the judge permits an infinite carrier.
The candidate now adds two certificate-only paths:

1. `parity_walk_infinite_countermodel` recognizes a specific hypothesis family
   whose operation is a parity-controlled involution. It selects a concrete
   goal-breaking assignment by bounded evaluation and emits a complete
   universal proof over `Bool × Nat`. The bounded evaluation is never treated
   as evidence that the hypothesis holds; the fixed Lean proof establishes it.
2. The LLM fallback may return either a complete under-20KB Lean artifact or a
   structured model plan (`carrier`, local definitions, operation, setup,
   universal hypothesis proof, concrete refutation). EULER assembles and
   envelope-checks it, preserves arithmetic `*` in raw Lean, and submits it
   only as a FALSE judge call. Rejections feed the exact Lean diagnostic into
   the next repair round.

Both a deterministic parity-walk certificate and a structured-plan `Nat`
certificate compile in AXLE's exact Lean 4.32.2 environment and have empty
`#print axioms` reports. The four released evaluation sets contain no match for
the parity-walk compiler, so the 800/800 released ceiling is not evidence for
this new private-set capability.

---

## 5. TRUE side — the proof cascade (cheapest first)

Given TRUE direction, EULER tries four provers in order; the first whose output
the judge accepts wins.

### 5.1 Matching-chain prover (`_ce_chain_proof`)
A forward matching-search prover reimplemented in EULER's term format. It builds
a rewrite chain from `E1` to `E2` and **self-rechecks** it (`chain_recheck`)
before ever calling the judge — correct-by-construction. Handles the "chainable"
population of TRUE problems.

### 5.2 mini-Twee — bounded Knuth–Bendix completion (`_mt_prove`)
An embedded, pure-stdlib Knuth–Bendix completion prover (`_MT_SRC_B64`, ~11 KB
zlib+base64, run exec-isolated in-sandbox). It cracks the **structural /
constancy / collapse** proofs that defeated matching-search and the old
`simp only` closes (the original cause of EULER's TRUE-side rejections). Two
properties matter and are both established by testing:

- **Direct completion is total** — *if it emits a direct proof, that proof is
  valid Lean* (the const-collapse emission template was made
  correct-by-construction: pin every binder to the LHS reduct except the
  constant slot, `(f …).symm.trans (f …)`). Measured: random-30 seed11 27/27
  valid, 0 invalid; unseen seed777 0 invalid; structural 6/6.
- **Terminating** — a hard `_DEADLINE` (8 s cap) checked inside `step`,
  `reduce_path` per position, and the round loop, plus `CP_SIZE_CAP=22` /
  `FACT_CAP=1500`. The earlier infinite-loop (a rewrite rule matching a subterm
  with swapped vars → cyclic match substitution) was fixed with `subst_flat`
  (one-pass simultaneous substitution). Measured: 0 hangs on the 90-pair suite.

The optional mirrored-law retry originally swapped operation terms without
repairing positional Lean binder order. A full 100-row kernel audit caught two
invalid generated bodies (`0146`, `0188`). The candidate now reintroduces goal
variables in original order and routes mirrored-order hypothesis calls through
an explicit permutation theorem; both repaired bodies compile. The public fast
path also carries independent ATP-replayed certificates for those rows.

Current released order-5 TRUE routing is 84 two-round completion, six deeper
direct completion, and ten static residual certificates. All 100 were generated
from the candidate and compiled with exact Lean 4.32.2, zero failures; the
largest body is 6,559 bytes.

#### Static ATP-replayed residual certificates

Installed E and Vampire proved the ten public order-5 residuals offline. A
deterministic reconstructor converted their superposition traces to shared Lean
proof DAGs using kernel equality operations. The compressed bodies are keyed by
the exact public equation-ID pair and disclosed in
`EULER-v8.1-SUBMISSION-NOTE.md`. They close a public regression set; they do not
generalize by lookup to unseen pairs and are not presented as private-evaluation
evidence.

### 5.3 Structural tactic strategies (`find_proof`)
Direct substitution, singleton, constancy, constant-pivot, and related
hand-written strategies for the remaining structural shapes.

### 5.4 Transitivity composition — Lever 1 (`_transitivity_prove`) — *v8*
For a hard `i ⇒ j` that no single prover closes, split it through a **directly
provable intermediate law `k`**: if `i ⇒ k` and `k ⇒ j` are both TRUE (per the
embedded matrix) and each hop is directly provable, compose the two proofs into
one `have`-chain (hypothesis renamed per hop; the last hop proves the goal
directly). Candidate `k`'s come **only** from the embedded oracle
(`_matrix_bit`) plus the embedded 4694-line equations text (`_EQ_SRC_B64`, needed
to *name* the intermediate law) — **no per-pair proof is stored**.

Coverage was verified structurally: the closure of the 10,657 public
`explicit_proof_true` generating edges equals all 8,178,279 order-4 TRUE pairs
(missing = 0, extra = 0). A 2-hop split through a directly-provable `k` recovers
the TRUE pairs that chain + mini-Twee individually miss (measured: hard3
TRUE-side 39/40, the 2 extra recoveries were transitivity's).

**Known TRUE limit (honest):** one hard-set pair, 853⇒160, needs a **3-hop**
split (and 4208⇒3879 needs deeper completion). These are hard-training pairs, not
scored normal pairs. 3-hop transitivity is a bounded, known future lever.

---

## 6. Soundness — why no invalid proof can ever be returned

Two independent guarantees:

1. **Judge-gating everywhere.** Every emit path finalizes only through `_T`
   (TRUE) or `_F` (FALSE), which call `call_judge` and return accepted **only on
   an `accepted` verdict**. The Tier 2/3/4 strategy functions
   (`proof_engine_v5`, `specialized_simp_v5`, `simp_constancy_v5`, `rw_chain_v5`,
   `hybrid_calc_v5`, `invertibility_sweep`, `tactic_sweep`, `llm_fallback_v5`)
   each call `call_judge("true", …)` internally and return True only on accept.
   A gating audit of `solve()` confirms **no path returns "accepted" without a
   passing judge call.**
2. **Correct-by-construction lower tiers.** The chain prover self-rechecks
   (`chain_recheck`); direct mini-Twee emission is total, and mirrored emission
   now includes an explicit positional-binder permutation bridge; the
   transitivity composer only assembles proved hops. The full released order-5
   TRUE output was compiled end-to-end on exact Lean 4.32.2.

⟹ The judge is a hard gate on top of already-sound provers. An `accepted`
verdict is the finalization in Solo mode (confirmed against the harness
`pipeline/proxy.py` — no separate `submit` message exists).

---

## 7. Robustness — infra-failfast

The live judge was observed (2026-08-20) returning a **judge-side infrastructure
error** (`Magma.olean` incompatible header — a SAIR Lean-toolchain version
mismatch, not a solver defect). EULER carries four surgical guards so it does not
burn the 3600 s budget retrying a broken judge:

- module flag `_JUDGE_INFRA_DOWN` + helper `_judge_result_is_infra()` (markers:
  `incompatible header`, `failed to compile JudgeProblem`, `judge_infrastructure`);
- `call_judge` short-circuits **all** subsequent judge calls once infra is
  detected;
- loop guards in the Solo loop, in the `llm_fallback_v5` loop, and in Marathon
  Pass C.

Verified on a simulated broken judge: **original 9 LLM / 103 judge calls →
patched 0 LLM / 1 judge call.** On a healthy judge these guards are inert.

---

## 8. Validation evidence

All dev-time validation uses **Axle** (cloud Lean **4.32.2 = the judge's Lean
version**, judge-faithful `JudgeProblem`/`Goal` binding: bare `Magma`, named
`EquationLHS`/`EquationRHS`, `infix:65`, no Mathlib). Every reported proof is
Axle-`verified=True`.

| Set | Measured (Axle / finite-model check) |
|-----|--------------------------------------|
| evaluation/normal — TRUE side | **40/40** |
| evaluation/normal — FALSE side | **11/12** |
| hard3 — TRUE side | 39/40 (2 recovered by transitivity) |
| hard2 — full | 36/40 (TRUE 18/19, FALSE 18/21) |
| Structural population (true_0008/0010/0014/0016/0018/0020) | 6/6 via `_mt_prove` |

FALSE-side benchmarks use a Python finite-model check with the same semantics as
the judge's `decideFin!`.

**Distribution fact:** Stage-2 *repo* public sets are 100% order-4 (§3). HF
`evaluation_order5` is a defined 200-problem order-5 slice where the oracle
is dead and transitivity cannot run. Historical v8 reached **190/200** (FALSE
100, TRUE 90); the isolated candidate reaches **200/200** on that released
reference set after ten targeted static proof replays. This does not imply that
an unseen order-5 slice is complete.

**Caveat (honest):** these are Axle numbers. Independent confirmation on the live
playground judge is pending a fresh run (the judge was infra-broken at last
check; see README status). The infra-failfast guards ensure that a still-broken
judge costs seconds, not budget.

---

## 9. Embedded data & provenance

Disclosed in full in `EULER-v8.1-SUBMISSION-NOTE.md`. Summary:

| Blob | Contents | Source |
|------|----------|--------|
| `_MATRIX_BLOB` | 4694² order-4 implication bitmatrix (~110 KB) | Public ETP `outcomes.json` closure (Tao et al.); recomputed, 0 disagreements. |
| `_LOOKUP_BLOB` | Sparse direction lookup, **70,592** compressed chars (12,587 keys; 222 have an ID outside 1..4694, including values up to ~936k). Used only when the bitmatrix misses. Not "small". Same ETP source; historically 13 in-range errors, overridden by the bitmatrix. |
| `_MT_SRC_B64` | mini-Twee prover source (~11 KB) | Our own bounded KB completion prover (`twee/mini_twee.py`). |
| `_EQ_SRC_B64` | 4694 order-4 equation texts (~15 KB) | Public ETP `equations.txt`; used only to *name* intermediate laws in the transitivity tier. |
| `_O5B` + `_O5B2` | Ten pair-keyed public order-5 Lean proof DAGs (6,476 base64 chars) | E/Vampire traces, deterministically replayed and compiled on exact Lean 4.32.2. |

The order-5 proof blobs intentionally encode certificates for ten exact public
reference pairs; they are disclosed and excluded from generalization claims.
Open-source basis: the Equational Theories Project
(github.com/teorth/equational_theories). The matching-chain and completion
techniques draw on the public Stage-2 leader's method and Krympa-style
forward-chain reconstruction (github.com/kondylidou/Krympa).

---

## 10. Honest limits (single list)

- Validation is Axle-based; **not yet re-confirmed on the live judge** (judge was
  infra-broken at last check).
- **finite FALSE tail:** the v8.1 candidate's harvested bank now covers 848/850
  original public FALSE pairs plus 400/400 released Stage 1 evaluation FALSE
  rows, and its bounded stdlib CSP searches orders 4–8. The two public bank
  misses are 1167⇒1763 and 2531⇒4307; neither is proved to lack a finite model.
  See `CSP-FALSE-FINDER.md` and `HF-BENCHMARK-AUDIT.md`.
- **hard TRUE misses** (853⇒160 needs 3-hop transitivity; 4208⇒3879 needs deeper
  completion). Hard training set only; 3-hop is a bounded future lever.
- **public order-5 targeting:** ten exact-pair static certificates close the
  released regression but add no lookup coverage for unseen order-5 pairs.
- A **Tier-4 LLM fallback** remains in the router. The solver issues an `llm`
  request; the organizer proxy renders the embedded prompt and picks the model
  (`openai/gpt-oss-120b` in the reference config). EULER does not choose the
  model. On public order-4 the deterministic tiers resolve the set, so this
  tier is a tail net, judge-gated and infra-failfast-guarded.
- **Marathon (v8.1):** the old Pass A/B/C path was not a second copy of Solo.
  The official runner sets `stdin=DEVNULL` (no `call_judge`), Pass A wrote
  ungated certs and marked them solved, and chain/mini-Twee/transitivity never
  ran. Rewritten: same v8 deterministic emitters, file JSONL only, python-checked
  FALSE + correct-by-construction TRUE, hard per-problem time slice. Smoke:
  `normal_0003` false + `normal_0001` true in 8.1 s, process exit 0.
