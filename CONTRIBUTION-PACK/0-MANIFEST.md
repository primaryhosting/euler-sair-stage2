# EULER × "Mathematics in the Age of Mechanical Reproduction"
## A contribution pack: the paper's protocol, instantiated on a real solver

**Author / owner:** Christopher Brock (chrisbrock54@gmail.com)
**Date assembled:** 2026-08-25
**Competition:** SAIR Foundation, Mathematics Distillation Challenge —
Equational Theories, Stage 2 (Solo + Marathon; deadline 2026-08-31 AoE)

---

## What this pack is

Two artifacts, each of which makes the other stronger:

1. **The paper** (`1-PAPER/`) — *Mathematics in the Age of Mechanical
   Reproduction: statement fidelity, reactivation, and the limits of the
   verified proof*. It argues that Tao's criterion ("a proof no human can
   properly explain should be viewed as incomplete") names a real epistemic
   layer that formal verification does not supply, separates six relations
   that institutions run together, and proposes two operational mechanisms:
   a **statement-fidelity protocol** (§8) and a **reactivation packet** with
   public tests and epistemic badges (§10).

2. **The solver** (`2-SOLVER/solver.py`) — EULER, a deterministic,
   certificate-emitting entry for SAIR Stage 2, whose every answer is a
   machine-checkable Lean artifact re-verified by the competition's open
   deterministic judge.

**The claim of the pack:** the solver submission is packaged to the paper's
own standards — to our knowledge the first competition entry accompanied by a
§8 statement-fidelity record, a §10 reactivation packet with the
process-evidence trace kept separate from retrospective rationale, and
per-artifact epistemic badges. The paper does not merely describe a norm;
this pack instantiates it, on the record, where anyone can audit it.

The pack therefore answers Tao's criterion in the strong form: not only *can*
the authors explain the result at an expert level (`6-DEMONSTRATION.md` is
that exposition, written to be delivered and recorded), but the explanation,
the failure history that produced it, the fidelity decisions beneath it, and
the verification status of every claim are all shipped as first-class
artifacts.

---

## Contents and audit map

| Path | Artifact | How to audit it |
|------|----------|-----------------|
| `1-PAPER/mathematics-in-the-age-of-mechanical-reproduction.pdf` | The white paper (24 pp., 2026-08-20) | Every load-bearing claim carries a locator; the tool-and-resource disclosure is on the final page. |
| `2-SOLVER/solver.py` | **EULER, snapshot of record for this pack.** 422,250 bytes, SHA-256 `8ecb362d8aa470336b57e6784b91c4575d0cf971df6743f046da4b1e0edcd55f`, `py_compile` clean. One file, both tracks (`__main__` branches on `JUDGE_MARATHON_MANIFEST`). | Run the SAIR open harness on it; recompute the SHA; the embedded-data disclosure enumerates every blob. |
| `2-SOLVER/EULER-v8.1-SUBMISSION-NOTE.md` | Embedded-data disclosure (bitmatrix, lookup, mini-Twee source, equation texts, table bank, pair-keyed certificate blobs) with provenance and the honest-targeting caveats | Diff each blob against its stated public source; re-verify any table with a 20-line finite check. |
| `2-SOLVER/EULER-METHODOLOGY.md` | Algorithms: direction oracle, FALSE engine, TRUE cascade, soundness argument | Cross-read against the code; every tier is named in both. |
| `3-REACTIVATION-PACKET.md` | **§10 reactivation packet**: governing idea, pivotal lemmas, failed approaches that materially explain the successful ones, dependency map, recorded explanation pointer, machine-verifiable artifacts — with the process-evidence trace / retrospective rationale / difficulty map kept explicitly apart | The trace files in `8-TRACE/` are the contemporaneous record the packet cites. |
| `4-STATEMENT-FIDELITY.md` | **§8 protocol applied**: formalization contract, semantic change log, adversarial statement review (two real caught failures), dual formalization, boundary testing | Both failure episodes are reproducible from the described inputs. |
| `5-EPISTEMIC-BADGES.md` | Per-artifact badge table: verification state, toolchain pin, axiom disclosure, and the ceiling-vs-confirmed separation | Recheck any certificate against Lean v4.32.2 commit `f3b06c705e6c85f5314019d5d3baab0fec5b580c`. |
| `6-DEMONSTRATION.md` | The expert-level exposition (Tao's rule of thumb, made an artifact): the governing ideas, one fully worked pivotal proof, the honest limits | Readable end-to-end without access to the authors; every step checkable. |
| `7-TRUST/EULER-TRUST-FRAMEWORK.md` | Provenance ledger, per-emit-path soundness, re-derivation recipe, honest-measurement protocol, dated iteration log | The re-derivation recipe uses only public materials. |
| `11-SOLVER-PAPER/` | **The consolidated EULER solver white paper** (~7pp, arXiv-style): abstract, problem, refusal-stack architecture, the completion tier's termination + total-emission properties, Theorem 4.1 (no unverified exit), Theorem 5.1 (the collapse, worked with verbatim kernel-checked Lean), badged measurement, the two philosophies, statement-fidelity failures, limitations, reproducibility, references. Companion to the philosophy paper. | Lean blocks verified against `8-TRACE/final2_solved.json` (2/2); every figure carries its badge; no OFFICIAL claim. |
| `9-WORKFLOW-DIAGRAMS.md` | Runtime-pipeline and dev-time-ecosystem diagrams (Mermaid), with the named acknowledgment of Axle (Axiom) and Aristotle (Harmonic) | Cross-read against the code and the disclosure note. |
| `10-FOUR-TELLINGS/` | **The paper's translation test, executed**: one result told four times — popular, literate, practitioner, formal — with the same pivotal proof at four depths; Telling IV quotes the kernel-checked derivation verbatim | Climb I→IV; the proof should come into focus, not change. Verify IV's Lean blocks against `8-TRACE/final2_solved.json`. |
| `8-TRACE/` | **Contemporaneous process-evidence trace**: the dated miss-characterization output and the four solved-body files exactly as produced during the improvement loop | These are the raw outputs the retrospective documents cite; they were written before the narrative, not after. |

---

## The three headline numbers, with their badges (do not collapse them)

| Claim | Value | Badge (see `5-EPISTEMIC-BADGES.md`) |
|---|---|---|
| Direction accuracy vs SAIR's published answers, order-4 evaluation sets | **600/600** | COMPUTATIONALLY VERIFIED (deterministic table lookup vs published ground truth) |
| Released-set solve ceiling (4×200 problems) | **800/800** | CEILING — leans on pair-keyed certificates for released rows; **not** a private-set claim, **not** an official-judge result |
| Held-out FALSE generalization (pairs/hypotheses absent from every released set) | **120/120 and 100/100** | COMPUTATIONALLY VERIFIED (full finite check, `decideFin!` semantics) |

The last official playground run (2026-08-20) failed on a SAIR-side
infrastructure error (`Magma.olean` incompatible header), documented and
reported. A fresh official judge run is the promotion gate and is stated as
such everywhere a score appears.

---

## Interested-party disclosure (mirroring the paper's §9)

The paper's author competed in the challenge this pack is submitted to, and
the paper's §9 discusses the challenge's access arrangements. That interest
is disclosed in the paper and repeated here. Everything else the pack relies
on is on the record: the open judge repository, the public problem sets, the
cited texts, and the artifacts in this pack. If any claim is wrong, it should
be possible to establish that from those sources alone.
