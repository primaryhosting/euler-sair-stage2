# EULER Φ — SAIR Stage 2 Final Submission Package

**Challenge:** SAIR Foundation — Mathematics Distillation Challenge,
Equational Theories, **Stage 2** (Solo track).
**Task:** for a pair of magma laws `(equation1, equation2)`, decide whether
`equation1 ⇒ equation2` holds in every magma and emit a machine-checkable Lean
proof — a finite or infinite counterexample model for FALSE, an implication proof for TRUE —
that the SAIR judge accepts.

---

## Entry point

| | |
|---|---|
| **Frozen final pre-submit candidate** | `EULER-v8.1-CANDIDATE.py` — **not promoted without a fresh official judge run** |
| **Candidate size / SHA-256** | 437,402 bytes · `52bcd90f668873687756fa68becf9d2b9d86b55a6a9b206ac764078b0fcd303e` |
| **Promoted live mirror** | `EQT02-S00021-infra-failfast.py` — prior v8.1 baseline, intentionally unchanged |
| **Live size / SHA-256** | 402,238 bytes · `33456faa124da32a72019ef045bbfd347a943686b84d833fc0e1d30bf6d81178` |
| **Compiles** | `python3 -m py_compile` — clean |
| **Interface** | `solve(problem, budget)` (Solo, stdin/stdout) · `marathon()` when `JUDGE_MARATHON_MANIFEST` is set (both tracks, one file) |
| **Per-problem budget** | 3600 s (Solo); typical resolve is sub-second |
| **Prior version** | `EULER-v8-SOLO-SUBMISSION.py` (SHA `67b47769…`, 381,891 B) retained for history; `EQT02-S00021-infra-failfast.py.v8-bak` is the rollback of the pre-promotion live file. |

**What the promoted v8.1 baseline adds over v8:** a hypothesis-keyed 305-table
counterexample bank (orders 2–9, Mace4-harvested + self-checked) and a
pure-stdlib runtime CSP finite-model finder. **What the current isolated
candidate adds over that baseline:** staged proof-carrying completion, a fixed
dual-law binder transformer, ten exact-Lean ATP-replayed certificates for the
public order-5 TRUE residuals (`_O5B`/`_O5B2`), **eight more pair-keyed
Axle-verified certificates for the order-4 TRUE residuals (`_LB`/`_loop25`:
3-hop, 5× Vampire+Krympa, collapse-finisher, E-prover DAG)**, three new
generalizing runtime tiers (**bounded 3-hop transitivity; 12-round completion;
12-round completion + duality on UNKNOWN**), and a **12 s UNKNOWN-direction CE
probe** (was 2 s — the released order-5 FALSE rows, the exact population that
reaches that branch, measured 100/100 at 12 s). Together these take the
released-set regression to 800/800 (ceiling; see below). Disclosure and the
honest public-targeting caveat are in `EULER-v8.1-SUBMISSION-NOTE.md`.
The final hardening pass also repairs the generic total-collapse certificate
(`Equation 2: x = y`) and gives Marathon the same 12-round completion and
`k=40`/bounded-3-hop TRUE tail as Solo.
The latest hardening adds an **infinite-model FALSE tier**: a deterministic,
proof-producing `Bool × Nat` parity-walk compiler plus a structured/complete
Lean artifact protocol for the LLM, with a 20KB envelope, banned-token checks,
arithmetic-safe JSON parsing, and judge-diagnostic repair. This corrects the
older prompt's false claim that the judge required finite carriers.

The solver speaks the standard Solo harness protocol: it issues `judge` requests
to self-verify candidate proofs, and an **accepted `judge` verdict is the
finalization** (confirmed against the current harness `pipeline/proxy.py`; there
is no separate `submit` message in Solo mode).

---

## Package contents

| Document | Purpose |
|----------|---------|
| **`EULER-FINAL-README.md`** | This file — cover, entry point, how to run, status. |
| **`EULER-METHODOLOGY.md`** | Full algorithm writeup: architecture, direction oracle, FALSE engine, TRUE cascade, soundness argument, validation evidence, honest limits. |
| **`EULER-v8.1-SUBMISSION-NOTE.md`** | Embedded-data disclosure for the current candidate — the 305-table bank, Mace4 provenance, and ten pair-keyed public order-5 proof DAGs. |
| **`EULER-v8.1-CANDIDATE.py`** | The isolated research candidate; not yet copied over the promoted live mirror. |
| **`EULER-FINALIZATION-2026-08-25.md`** | Frozen handoff record, exact upload instructions, evidence, caveats, and promotion gate. |
| **`EULER-v8.1-FINAL.sha256`** | Checksums for the frozen candidate, rollback, and infinite-FALSE validation fixtures. |
| **`infinite-false-artifacts/`** | AXLE-checked parity-walk and structured-plan Lean fixtures plus the exact validation record. |
| `EULER-v8-SUBMISSION-NOTE.md` | Disclosure for the prior v8 (four-payload). Superseded by the v8.1 note. |
| `EULER-v8-SOLO-SUBMISSION.py` | Prior v8 solver, retained for history. |
| `EULER-v6.1-CHANGELOG.md` | Version history v6.1 → v7 → v8. |

---

## What EULER does, in one paragraph

Direction (TRUE vs FALSE) is read from an **embedded 4694×4694 order-4
implication bitmatrix** that is byte-identical to the public Equational Theories
Project closure — so on the scored (order-4) distribution, direction is exact
with zero search. Given the direction, **FALSE** problems first get a
finite-magma counterexample (table bank → exhaustive →
structured/affine/bilinear/CSP) emitted as `finOpTable` + `decideFin!`; after a
finite miss, EULER can emit a proof-producing infinite `Bool × Nat` model or a
judge-gated structured/complete Lean model artifact. **TRUE** problems get an implication proof from a
cheapest-first cascade — matching-chain prover, then a bounded Knuth–Bendix
completion prover (mini-Twee), then structural tactic strategies, then
**transitivity composition** (split a hard `i ⇒ j` through a directly-provable
intermediate `k`). Every candidate proof is submitted to the judge; **only an
`accepted` verdict finalizes an answer**, so no invalid proof can ever be
returned. The judge bans only placeholder tokens (`sorry`/`admit`/…) and banned
axioms — not ordinary tactics; EULER's core provers nonetheless prefer a small
explicit tactic set (`intro`/`exact`/`calc`/`have`/`congrArg`/`.symm`/`.trans`)
for compile speed and reliability. See `EULER-METHODOLOGY.md` §1.

---

## Validation status (honest)

Validation is a mix of exhaustive Python finite-model checking and local exact
Lean **4.32.2** kernel checking. It is not a green live-judge run — see the last
two bullets.

- **Measured against all four official SAIR evaluation subsets** (from
  `SAIRfoundation/equational-theories-selected-problems`, 200 problems each,
  balanced 100 TRUE / 100 FALSE). FALSE via a Python finite-model check
  (`decideFin!` semantics, every witness self-checked); TRUE via
  chain→mini-Twee→transitivity plus the disclosed static ATP-replayed public
  residuals. Current candidate regression:

  | Set | Order | FALSE | TRUE | Combined |
  |-----|-------|-------|------|----------|
  | evaluation_normal | 4 | 100/100 | 100/100 | 200/200 |
  | evaluation_hard | 4 | 100/100 | 100/100 | 200/200 |
  | evaluation_extra_hard | 4 | 100/100 | 100/100 | 200/200 |
  | evaluation_order5 | 5 | 100/100 | 100/100 | 200/200 |
  | **Total** | | | | **800/800 — released-set CEILING** |

  The last nine order-4 TRUE rows are covered by the eight `_LB` pair-keyed
  certificates plus one organic transitivity recovery. **This 800/800 is a
  released-set ceiling that leans on pair-keyed certs — it is NOT a
  private-set claim and NOT a live-judge result.** The Stage-2 spec states
  released Stage-1 evaluation rows will not appear in the private set; what
  carries to the private set are the generalizing tiers (hypothesis-keyed
  bank, CSP finder, 3-hop transitivity, 12-round completion ± duality, 12 s
  UNKNOWN CE probe) and the held-out FALSE evidence below.

- **Oracle direction is exact: 600/600** vs the official answers on all three
  order-4 sets (0 wrong, 0 missed) — an independent check of the bitmatrix
  against SAIR ground truth.
- **Released order-5 regression is complete offline.** The
  `evaluation_order5` set is 100% outside the order-4 oracle (IDs 4863–41402):
  no oracle direction and transitivity is inert. The current candidate reaches
  **200/200**: 100 independently rechecked finite models and 100 exact-Lean
  TRUE bodies (84 quick completion, six deeper completion, ten static ATP
  replays). The ten static proofs are exact-public-pair coverage, not evidence
  about unseen order-5 pairs.
- **FALSE-side honesty (important).** The released-set FALSE = 100% is **inflated
  by construction**: the Mace4 harvest that grew the bank targeted these exact
  released problems. The real generalization evidence is **held-out**: 120/120
  order-4 FALSE pairs excluded from every released set, and 100/100 FALSE pairs
  whose *hypothesis never appears in any released set* — all sound. Full
  disclosure in `EULER-v8.1-SUBMISSION-NOTE.md`.
- **Exact candidate replay is green offline.** A credit-free run of the exact
  single file, with no gold label supplied to the solver, routed all 800 rows:
  400/400 TRUE certificates and 400/400 independently self-checked FALSE
  witnesses. All 400 captured first-choice TRUE certificates compile under the
  exact Lean 4.32.2 kernel. That audit exposed three legacy `x = y` bodies with
  a reversed final equality; the candidate now replaces the whole class with a
  direct generated certificate, and the three replacements compile. Maximum
  emitted sizes were 7,785 B TRUE and 512 B FALSE.
- **Infinite FALSE validation is separate and explicit.** No released row
  matches the new parity-walk recognizer, so it does not inflate the 800/800
  ceiling. A representative 1,511-byte deterministic `Bool × Nat` artifact
  and a separate structured-plan `Nat` artifact both compile under AXLE's
  exact Lean 4.32.2 environment. Axiom audits of `submission` report
  `trusted: true`, `axioms: []`, and `extra_axioms: []` for both.
  Arbitrary LLM-produced plans remain untrusted until the official judge
  accepts the concrete emitted artifact.
- **Offline sandbox reproduction is green.** The current candidate imports and
  decodes all eighteen added proof bodies in the exact official amd64
  `python:3.11-slim` image digest under the published read-only, no-network,
  CPU/memory/PID/`/tmp` limits. The prior v8.1 baseline also passed interactive
  Solo and five-problem Marathon protocol fixtures. This validates packaging
  and protocol, not an official judge verdict.
- **Not confirmed on the live judge.** The playground is out of credits. A
  clean temporary installation of the exact Lean 4.32.2 commit compiled all
  400 released TRUE certificates through the faithful core-only judge goal
  wrapper, but that is not an organizer judge call. The last live run
  (2026-08-20) hit a SAIR-side
  infrastructure error (`Magma.olean` incompatible header — not a solver defect;
  `SAIR-JUDGE-BUG-REPORT-2026-08-20.md`). EULER carries **infra-failfast guards**
  so a still-broken judge costs seconds, not budget. A fresh playground run of
  the candidate remains the promotion gate.

---

## How to run (local sanity)

```bash
# Compile check (isolated candidate)
python3 -m py_compile EULER-v8.1-CANDIDATE.py

# Solo harness drives solve(problem, budget_seconds) per problem and
# relays the solver's `judge` requests to the SAIR judge; an accepted
# verdict finalizes that problem.
```

Dev-time re-validation of any proof (independent of the live judge) uses Axle:
see `~/Projects/sair-eq2-harvest/axle_judge.py` (`axle_true(eq1, eq2, body)`,
Lean 4.32.2) and the end-to-end harnesses `bench_full.py` / `bench_true.py`.
